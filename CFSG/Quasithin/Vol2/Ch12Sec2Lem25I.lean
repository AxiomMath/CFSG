module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Gaschutz
public import CFSG.Quasithin.Background.BlueprintB2Frattini
public import CFSG.Quasithin.H13.A7KLocal
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem24
public import CFSG.Quasithin.Vol2.Ch12Sec5L11
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

namespace Lem25

variable {G : Type} [Group G]

theorem exists_mem_centralizer_of_conj_mul [Finite G] {U : Subgroup G} {h x u₁ : G}
    (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hhU : h ∈ Subgroup.normalizer (U : Set G))
    (hUh : ∀ u ∈ U, h * u * h⁻¹ = u → u = 1) (hu₁ : u₁ ∈ U) (hx : x * h * x⁻¹ = u₁ * h) :
    ∃ u ∈ U, u⁻¹ * x * h = h * (u⁻¹ * x) := by
  classical
  have hconj : ∀ u ∈ U, h * u * h⁻¹ ∈ U := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp hhU u).mp hu
  let f : ↥U → ↥U := fun u =>
    ⟨(u : G) * (h * u * h⁻¹)⁻¹, U.mul_mem u.2 (U.inv_mem (hconj u u.2))⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : (a : G) * (h * a * h⁻¹)⁻¹ = b * (h * b * h⁻¹)⁻¹ := congrArg Subtype.val hab
    have ha' := hconj a a.2
    have hb' := hconj b b.2
    have h2 : (b : G)⁻¹ * a = (h * b * h⁻¹)⁻¹ * (h * a * h⁻¹) := by
      calc (b : G)⁻¹ * a = (b : G)⁻¹ * (a * (h * a * h⁻¹)⁻¹) * (h * a * h⁻¹) := by group
        _ = (b : G)⁻¹ * (b * (h * b * h⁻¹)⁻¹) * (h * a * h⁻¹) := by rw [h1]
        _ = (h * b * h⁻¹)⁻¹ * (h * a * h⁻¹) := by group
    have hc : h * ((a : G) * (b : G)⁻¹) * h⁻¹ = (a : G) * (b : G)⁻¹ := by
      calc h * ((a : G) * (b : G)⁻¹) * h⁻¹ = (h * a * h⁻¹) * (h * b * h⁻¹)⁻¹ := by group
        _ = (h * b * h⁻¹)⁻¹ * (h * a * h⁻¹) := hUab _ ha' _ (U.inv_mem hb')
        _ = (b : G)⁻¹ * a := h2.symm
        _ = (a : G) * (b : G)⁻¹ := hUab _ (U.inv_mem b.2) _ a.2
    have h3 := hUh _ (U.mul_mem a.2 (U.inv_mem b.2)) hc
    exact Subtype.ext (mul_inv_eq_one.mp h3)
  obtain ⟨u, hu⟩ := (Finite.injective_iff_surjective.mp hf) ⟨u₁, hu₁⟩
  refine ⟨u, u.2, ?_⟩
  have hu' : (u : G) * (h * u * h⁻¹)⁻¹ = u₁ := congrArg Subtype.val hu
  have hxh : x * h = u₁ * h * x := by
    calc x * h = x * h * x⁻¹ * x := by group
      _ = u₁ * h * x := by rw [hx]
  calc (u : G)⁻¹ * x * h = (u : G)⁻¹ * (u₁ * h * x) := by rw [mul_assoc, hxh]
    _ = (u : G)⁻¹ * ((u : G) * (h * u * h⁻¹)⁻¹ * h * x) := by rw [hu']
    _ = h * ((u : G)⁻¹ * x) := by group

theorem exists_complement_of_three [Finite G] (h1222 : Stmt12_2_2)
    {T L V H P U I : Subgroup G} {h : G} {n p : ℕ} (hH : Hyp1223 G T L V)
    (hC : Config12_2_24 T L V H P U I h n p) (hp3 : p = 3) :
    ∃ X : Subgroup G, X ≤ L ∧ X ⊓ V = ⊥ ∧ X ⊔ V = L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hHs, -, -, -, -, -, hp, hp2, hP, hord, -, -, hI, -, hUd, hUi, hUe, hD, hUP,
    hidx, -, hUO, -, hK, hHU, -, -, -, -, -⟩ := hC
  subst hp3
  have hTH : T ≤ H := hHs.1.1
  have hLV := le_normalizer_of_hyp1223 hH
  have hVe : IsElemAbelian 2 V := S125.isElemAbelian_of_hyp1223 hH
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hVe
  have hU2 : IsPGroup 2 U := B2F.isPGroup_of_isElemAbelian hUe
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hUe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨S, rfl⟩ := exists_sylow_coe_eq hH.sylow
  have hUT : U ≤ (S : Subgroup G) :=
    hUO.trans (A7.pCoreOf_le_of_le_normalizer S (hTH.trans Subgroup.le_normalizer))
  obtain ⟨-, -, hall⟩ := ((h1222 G S hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨hVT, hTV, -, -⟩, -, -, -, -⟩ := hall V hH.irrPlus
  have hVL : V ≤ L := by
    rw [← commutator_eq_of_hyp1223 hH, Subgroup.commutator_le]
    intro v hv l hl
    rw [commutatorElement_def]
    exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hH.normalizes (hVT hv)) l).mp hl)
      (L.inv_mem hl)
  have hPh : P = Subgroup.zpowers h := hP
  have hhH : h ∈ H := by
    have h1 : h ∈ oTwoUpper H := by
      rw [hK, hPh]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers h)
    exact oTwoUpper_le H h1
  have hhU : h ∈ Subgroup.normalizer (U : Set G) := hHU hhH
  have hPU : Subgroup.zpowers h ≤ Subgroup.normalizer (U : Set G) :=
    Subgroup.zpowers_le.mpr hhU
  have hh3 : h ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one h
  have hh1 : h ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hord
    omega
  have hhnU : h ∉ U := by
    intro hhu
    obtain ⟨k, hk⟩ := hU2 ⟨h, hhu⟩
    have hk' : h ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hcop : Nat.gcd (2 ^ k) 3 = 1 := Nat.Coprime.pow_left k (by norm_num)
    have := pow_gcd_eq_one.mpr ⟨hk', hh3⟩
    rw [hcop, pow_one] at this
    exact hh1 this
  have hUh : ∀ u ∈ U, h * u * h⁻¹ = u → u = 1 := by
    intro u hu hfix
    have huP : u ∈ U ⊓ Subgroup.centralizer (P : Set G) := by
      refine ⟨hu, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
      rw [hPh] at hk
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
      have hc : Commute h u := by
        calc h * u = h * u * h⁻¹ * h := by group
          _ = u * h := by rw [hfix]
      exact (hc.zpow_left j).eq
    rw [hUP, Subgroup.mem_bot] at huP
    exact huP
  have hTh : ∀ t ∈ (S : Subgroup G), ∃ u ∈ U,
      t * h * t⁻¹ = u ∨ t * h * t⁻¹ = u * h ∨ t * h * t⁻¹ = u * h ^ 2 := by
    intro t ht
    have h1 : t * h * t⁻¹ ∈ oTwoUpper H := by
      have h2 : h ∈ oTwoUpper H := by
        rw [hK, hPh]
        exact Subgroup.mem_sup_left (Subgroup.mem_zpowers h)
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper H (hTH ht)) h).mp h2
    rw [hK, hPh, sup_comm] at h1
    obtain ⟨u, hu, q, hq, huq⟩ := Lem24.exists_mul_of_mem_sup_normal hPU h1
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
    have h3 : h ^ j = h ^ (j % 3) := by
      conv_lhs => rw [← zpow_mod_orderOf, hord]
      norm_num
    have h4 : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
    refine ⟨u, hu, ?_⟩
    rw [← huq, h3]
    rcases h4 with h4 | h4 | h4 <;> rw [h4]
    · left; rw [zpow_zero, mul_one]
    · right; left; rw [zpow_one]
    · right; right; rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
  have hnot0 : ∀ t ∈ (S : Subgroup G), ∀ u ∈ U, t * h * t⁻¹ ≠ u := by
    intro t ht u hu h1
    apply hhnU
    have := (Subgroup.mem_normalizer_iff.mp (hHU (hTH (S.inv_mem ht))) u).mp hu
    rwa [← h1, show t⁻¹ * (t * h * t⁻¹) * t⁻¹⁻¹ = h by group] at this
  have hinv : ∀ v ∈ V, v ∉ U → ∃ u ∈ U, v * h * v⁻¹ = u * h ^ 2 := by
    by_contra hno
    push Not at hno
    obtain ⟨v₀, hv₀V, hv₀U, hv₀⟩ := hno
    obtain ⟨u₀, hu₀, hv₀h⟩ := hTh v₀ (hVT hv₀V)
    have hv₀h' : v₀ * h * v₀⁻¹ = u₀ * h := by
      rcases hv₀h with h1 | h1 | h1
      · exact absurd h1 (hnot0 v₀ (hVT hv₀V) u₀ hu₀)
      · exact h1
      · exact absurd h1 (hv₀ u₀ hu₀)
    have hcomm : ∀ v ∈ V, v * h * v⁻¹ * h⁻¹ ∈ U := by
      intro v hv
      by_cases hvU : v ∈ U
      · rw [show v * h * v⁻¹ * h⁻¹ = v * (h * v⁻¹ * h⁻¹) by group]
        exact U.mul_mem hvU ((Subgroup.mem_normalizer_iff.mp hhU _).mp (U.inv_mem hvU))
      ·
        have ha : v₀⁻¹ * v ∈ U ⊓ V := by
          have h1 := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨v₀, hv₀V⟩ : ↥V)⁻¹)
            (b := (⟨v, hv⟩ : ↥V))).mpr (by
              rw [inv_mem_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
              exact iff_of_false (fun h2 => hv₀U h2.1) (fun h2 => hvU h2.1))
          rw [Subgroup.mem_subgroupOf] at h1
          exact h1
        obtain ⟨a, haUV, rfl⟩ : ∃ a ∈ U ⊓ V, v = v₀ * a := ⟨v₀⁻¹ * v, ha, by group⟩
        have hah : a * h * a⁻¹ * h⁻¹ ∈ U := by
          rw [show a * h * a⁻¹ * h⁻¹ = a * (h * a⁻¹ * h⁻¹) by group]
          exact U.mul_mem haUV.1 ((Subgroup.mem_normalizer_iff.mp hhU _).mp
            (U.inv_mem haUV.1))
        have hv₀N := hHU (hTH (hVT hv₀V))
        have h2 : v₀ * (a * h * a⁻¹ * h⁻¹) * v₀⁻¹ ∈ U :=
          (Subgroup.mem_normalizer_iff.mp hv₀N _).mp hah
        rw [show v₀ * a * h * (v₀ * a)⁻¹ * h⁻¹ =
          (v₀ * (a * h * a⁻¹ * h⁻¹) * v₀⁻¹) * (v₀ * h * v₀⁻¹ * h⁻¹) by group, hv₀h',
          show u₀ * h * h⁻¹ = u₀ by group]
        exact U.mul_mem h2 hu₀
    have hVh : CFSG.conjugate V h ≤ U ⊔ V := by
      intro x hx
      have hxv : h * x * h⁻¹ ∈ V := BlueprintB2.mem_conjugate_iff.mp hx
      have h1 := hcomm _ hxv
      have h2 : h⁻¹ * ((h * x * h⁻¹) * h * (h * x * h⁻¹)⁻¹ * h⁻¹) * h ∈ U := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hhU) _).mp h1
        rwa [inv_inv] at this
      have h3 : x = (h⁻¹ * ((h * x * h⁻¹) * h * (h * x * h⁻¹)⁻¹ * h⁻¹) * h) *
          (h * x * h⁻¹) := by group
      rw [h3]
      exact Subgroup.mul_mem_sup h2 hxv
    have hIUV : I ≤ U ⊔ V := by
      rw [hI]
      exact sup_le le_sup_right hVh
    have hUV2 : IsPGroup 2 ↥(U ⊔ V) :=
      IsPGroup.to_sup_of_normal_right' hU2 hV2 (hUT.trans hTV)
    have hI2 : IsPGroup 2 I := hUV2.to_le hIUV
    obtain ⟨_, ⟨eD⟩⟩ := hD
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (U.subgroupOf I)
    rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card] at hcard
    obtain ⟨k, hk⟩ := hI2.exists_card_eq
    have hpd : 3 ∣ 2 ^ k := by
      rw [← hk, hcard]
      exact Dvd.dvd.mul_right (dvd_mul_left 3 2) _
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hpd) (by norm_num)
  set CP : Subgroup G := (S : Subgroup G) ⊓ Subgroup.centralizer (P : Set G) with hCPdef
  have hmemCP : ∀ x ∈ (S : Subgroup G), x * h = h * x → x ∈ CP := by
    intro x hx hxh
    refine ⟨hx, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
    rw [hPh] at hk
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    exact ((Commute.zpow_left (show Commute h x from hxh.symm) j)).eq
  have hcomm1 : ∀ t ∈ (S : Subgroup G), ∀ u₁ ∈ U, t * h * t⁻¹ = u₁ * h → t ∈ U ⊔ CP := by
    intro t ht u₁ hu₁ h1
    obtain ⟨u, hu, hut⟩ := exists_mem_centralizer_of_conj_mul hUab hhU hUh hu₁ h1
    have hc : u⁻¹ * t ∈ CP := hmemCP _ (S.mul_mem (S.inv_mem (hUT hu)) ht) hut
    rw [show t = u * (u⁻¹ * t) by group]
    exact Subgroup.mul_mem_sup hu hc
  obtain ⟨v₀, hv₀V, hv₀U⟩ : ∃ v₀ ∈ V, v₀ ∉ U := by
    by_contra hno
    push Not at hno
    have hVU : (U ⊓ V).subgroupOf V = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_subgroupOf]
      exact ⟨hno x x.2, x.2⟩
    have : ((U ⊓ V).subgroupOf V).index = 2 := hidx
    rw [hVU, Subgroup.index_top] at this
    omega
  obtain ⟨u₂, hu₂, hv₀h⟩ := hinv v₀ hv₀V hv₀U
  have hT : (S : Subgroup G) ≤ (U ⊔ CP) ⊔ V := by
    intro t ht
    obtain ⟨u₁, hu₁, h1 | h1 | h1⟩ := hTh t ht
    · exact absurd h1 (hnot0 t ht u₁ hu₁)
    · exact Subgroup.mem_sup_left (hcomm1 t ht u₁ hu₁ h1)
    ·
      have htv : t * v₀ ∈ (S : Subgroup G) := S.mul_mem ht (hVT hv₀V)
      have hu₂' : t * u₂ * t⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp (hHU (hTH ht)) u₂).mp hu₂
      have hu₁' : h ^ 2 * u₁ * h⁻¹ ^ 2 ∈ U := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hhU 2) u₁).mp hu₁
        rwa [← inv_pow] at this
      have h2 : t * v₀ * h * (t * v₀)⁻¹ =
          ((t * u₂ * t⁻¹) * u₁ * (h ^ 2 * u₁ * h⁻¹ ^ 2)) * h := by
        calc t * v₀ * h * (t * v₀)⁻¹ = t * (v₀ * h * v₀⁻¹) * t⁻¹ := by group
          _ = t * (u₂ * h ^ 2) * t⁻¹ := by rw [hv₀h]
          _ = (t * u₂ * t⁻¹) * ((t * h * t⁻¹) * (t * h * t⁻¹)) := by rw [pow_two]; group
          _ = (t * u₂ * t⁻¹) * ((u₁ * h ^ 2) * (u₁ * h ^ 2)) := by rw [h1]
          _ = ((t * u₂ * t⁻¹) * u₁ * (h ^ 2 * u₁ * h⁻¹ ^ 2)) * (h ^ 3 * h) := by group
          _ = ((t * u₂ * t⁻¹) * u₁ * (h ^ 2 * u₁ * h⁻¹ ^ 2)) * h := by rw [hh3, one_mul]
      have h3 := hcomm1 _ htv _ (U.mul_mem (U.mul_mem hu₂' hu₁) hu₁') h2
      rw [show t = (t * v₀) * v₀⁻¹ by group]
      exact Subgroup.mul_mem_sup h3 (V.inv_mem hv₀V)
  set B := U ⊓ CFSG.conjugate V h with hBdef
  have hCPB : CP ≤ Subgroup.normalizer (B : Set G) := by
    intro c hc
    have hch : c * h = h * c := (Subgroup.mem_centralizer_iff.mp hc.2 h (by
      rw [hPh]; exact Subgroup.mem_zpowers h)).symm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hcU := hHU (hTH hc.1)
    have hcV := hTV hc.1
    constructor
    · rintro ⟨hxU, hxV⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp hcU x).mp hxU, BlueprintB2.mem_conjugate_iff.mpr ?_⟩
      have hxv := BlueprintB2.mem_conjugate_iff.mp hxV
      rw [show h * (c * x * c⁻¹) * h⁻¹ = c * (h * x * h⁻¹) * c⁻¹ by
        rw [show h * (c * x * c⁻¹) * h⁻¹ = (h * c) * x * (h * c)⁻¹ by group, ← hch]; group]
      exact (Subgroup.mem_normalizer_iff.mp hcV _).mp hxv
    · rintro ⟨hxU, hxV⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp hcU x).mpr hxU, BlueprintB2.mem_conjugate_iff.mpr ?_⟩
      have hxv := BlueprintB2.mem_conjugate_iff.mp hxV
      have : c * (h * x * h⁻¹) * c⁻¹ ∈ V := by
        rw [show c * (h * x * h⁻¹) * c⁻¹ = h * (c * x * c⁻¹) * h⁻¹ by
          rw [show h * (c * x * c⁻¹) * h⁻¹ = (h * c) * x * (h * c)⁻¹ by group, ← hch]; group]
        exact hxv
      exact (Subgroup.mem_normalizer_iff.mp hcV _).mpr this
  set C := B ⊔ CP with hCdef
  have hCT : C ≤ (S : Subgroup G) := sup_le (inf_le_left.trans hUT) inf_le_left
  have hTC : (S : Subgroup G) ≤ C ⊔ V := by
    refine hT.trans (sup_le (sup_le ?_ (le_sup_right.trans le_sup_left)) le_sup_right)
    rw [hUd]
    exact sup_le (inf_le_right.trans le_sup_right) (le_sup_left.trans le_sup_left)
  have hCV : C ⊓ V = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxC, hxV⟩
    obtain ⟨b, hb, c, hc, rfl⟩ := Lem24.exists_mul_of_mem_sup_normal hCPB hxC
    rw [Subgroup.mem_bot]
    have hch : c * h = h * c := (Subgroup.mem_centralizer_iff.mp hc.2 h (by
      rw [hPh]; exact Subgroup.mem_zpowers h)).symm
    by_cases hbc : b * c ∈ U
    ·
      have hcU : c ∈ U := by
        have := U.mul_mem (U.inv_mem hb.1) hbc
        rwa [show b⁻¹ * (b * c) = c by group] at this
      have hc1 : c = 1 := hUh c hcU (by rw [← hch]; group)
      subst hc1
      rw [mul_one] at hxV hbc ⊢
      have h1 : b ∈ (U ⊓ V) ⊓ (U ⊓ CFSG.conjugate V h) := ⟨⟨hb.1, hxV⟩, hb⟩
      rw [hUi, Subgroup.mem_bot] at h1
      exact h1
    ·
      exfalso
      obtain ⟨u₃, hu₃, h1⟩ := hinv (b * c) hxV hbc
      have h2 : b * c * h * (b * c)⁻¹ = b * h * b⁻¹ := by
        rw [show b * c * h * (b * c)⁻¹ = b * (c * h) * c⁻¹ * b⁻¹ by group, hch]; group
      rw [h2] at h1
      have h3 : b * h * b⁻¹ * h⁻¹ ∈ U := by
        rw [show b * h * b⁻¹ * h⁻¹ = b * (h * b⁻¹ * h⁻¹) by group]
        exact U.mul_mem hb.1 ((Subgroup.mem_normalizer_iff.mp hhU _).mp (U.inv_mem hb.1))
      rw [h1, show u₃ * h ^ 2 * h⁻¹ = u₃ * h by group] at h3
      have h4 := U.mul_mem (U.inv_mem hu₃) h3
      rw [show u₃⁻¹ * (u₃ * h) = h by group] at h4
      exact hhnU h4
  have hCVT : C ⊔ V = (S : Subgroup G) := le_antisymm (sup_le hCT hVT) hTC
  have hLS : IsSylowTwoOf ((S : Subgroup G) ⊓ L) L := by
    have hS : IsSylowTwoOf (S : Subgroup G) (L ⊔ (S : Subgroup G)) := by
      refine ⟨le_sup_right, S.isPGroup', fun h2 => hH.sylow.2 ?_⟩
      exact h2.trans (Subgroup.relIndex_dvd_index_of_le le_sup_right)
    exact A4.isSylowTwoOf_inf_normal hS le_sup_left
      (sup_le Subgroup.le_normalizer hH.normalizes)
  have hCL : (C ⊓ L) ⊔ V = (S : Subgroup G) ⊓ L := by
    apply le_antisymm
    · exact sup_le (inf_le_inf_right L hCT) (le_inf hVT hVL)
    · rintro x ⟨hxS, hxL⟩
      have hx : x ∈ V ⊔ C := by rw [sup_comm, hCVT]; exact hxS
      obtain ⟨v, hv, c, hc, rfl⟩ :=
        Lem24.exists_mul_of_mem_sup_normal (fun y hy => hTV (hCT hy)) hx
      have hcL : c ∈ L := by
        have := L.mul_mem (L.inv_mem (hVL hv)) hxL
        rwa [show v⁻¹ * (v * c) = c by group] at this
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hv) (Subgroup.mem_sup_left ⟨hc, hcL⟩)
  obtain ⟨X₀, hX₀L, hX₀V, hX₀sup⟩ := C5.exists_complement_of_sylow_split hVL hLV hVab hV2 hLS
    (inf_le_inf_right L hCT) (eq_bot_iff.mpr fun x hx => by
      rw [← hCV]; exact ⟨hx.1.1, hx.2⟩) hCL
  exact ⟨X₀, hX₀L, by rw [inf_comm]; exact hX₀V, by rw [sup_comm]; exact hX₀sup⟩

end Lem25

end CFSG.Quasithin.H13
