module

public import CFSG.Quasithin.Background.B5Statement
import CFSG.Foundations.KCoreClosure
public import CFSG.Quasithin.Background.B1MoreElevenD
public import CFSG.Quasithin.Background.B1MoreTwelveA

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B5

theorem comm_mul_right_of_commute {Ω : Type*} [Group Ω] {k z y : Ω} (h : z * y = y * z) :
    ⁅k * z, y⁆ = ⁅k, y⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have : k * z * y * (k * z)⁻¹ * y⁻¹ = k * (z * y) * z⁻¹ * k⁻¹ * y⁻¹ := by group
  rw [this, h]
  group

theorem comm_mul_left_of_commute {Ω : Type*} [Group Ω] {x k' z' : Ω} (h : z' * x = x * z') :
    ⁅x, k' * z'⁆ = ⁅x, k'⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have h' : z' * x⁻¹ = x⁻¹ * z' := (show Commute z' x from h).inv_right.eq
  have : x * (k' * z') * x⁻¹ * (k' * z')⁻¹ = x * k' * (z' * x⁻¹) * z'⁻¹ * k'⁻¹ := by group
  rw [this, h']
  group

theorem comm_mul_central {Ω : Type*} [Group Ω] {k k' z z' : Ω} (h1 : z * k' = k' * z)
    (h2 : z * z' = z' * z) (h3 : z' * k = k * z') :
    ⁅k * z, k' * z'⁆ = ⁅k, k'⁆ := by
  have hz : z * (k' * z') = (k' * z') * z := by
    calc z * (k' * z') = (z * k') * z' := by rw [mul_assoc]
      _ = (k' * z) * z' := by rw [h1]
      _ = k' * (z * z') := by rw [mul_assoc]
      _ = k' * (z' * z) := by rw [h2]
      _ = (k' * z') * z := by rw [mul_assoc]
  rw [comm_mul_right_of_commute hz, comm_mul_left_of_commute h3]



theorem elemAbelian_le_of_two_quotient {G : Type} [Group G] (L : Subgroup G) [L.Normal]
    (h2 : IsPGroup 2 (G ⧸ L)) {p : ℕ} (hp2 : p ≠ 2) (hp : p.Prime) {E : Subgroup G}
    (hE : IsElemAbelian p E) : E ≤ L := by
  intro x hx
  obtain ⟨n, hn⟩ := h2 (QuotientGroup.mk x)
  have h1 : (QuotientGroup.mk x : G ⧸ L) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, hE.2 x hx, QuotientGroup.mk_one]
  have hcop : Nat.Coprime (2 ^ n) p :=
    Nat.Coprime.pow_left n ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have h3 : orderOf (QuotientGroup.mk x : G ⧸ L) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  have h4 : orderOf (QuotientGroup.mk x : G ⧸ L) ∣ p := orderOf_dvd_of_pow_eq_one h1
  have h5 : orderOf (QuotientGroup.mk x : G ⧸ L) = 1 := Nat.eq_one_of_dvd_coprimes hcop h3 h4
  have h6 : (QuotientGroup.mk x : G ⧸ L) = 1 := orderOf_eq_one_iff.1 h5
  exact (QuotientGroup.eq_one_iff x).1 h6

theorem sqt_of_two_quotient {X : Type} [Group X] [Finite X] (L : Subgroup X) [L.Normal]
    (h2 : IsPGroup 2 (X ⧸ L)) (hL : CFSG.Open.SQTKTauCeti.StronglyQuasithin ↥L) :
    CFSG.Open.SQTKTauCeti.StronglyQuasithin X := by
  intro p hp hp2
  obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup X)
  have hEL : E ≤ L :=
    elemAbelian_le_of_two_quotient L h2 hp2 hp hE
  have hE' : IsElemAbelian p (E.subgroupOf L) := by
    have e1 : ↥(E.subgroupOf L) ≃* ↥E := Subgroup.subgroupOfEquivOfLe hEL
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply e1.injective
      rw [map_mul, map_mul]
      exact hE.1.is_comm.comm _ _
    · have := hE.2 (x : X) hx
      exact Subtype.ext this
  have hle : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥L) := by
    refine CFSG.SectionRank.le_pRank hp.one_lt le_top hE' ?_
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv
  exact hle.trans (hL p hp hp2)

theorem kGroup_of_two_quotient {X : Type} [Group X] [Finite X] (L : Subgroup X) [L.Normal]
    (h2 : IsPGroup 2 (X ⧸ L)) (hL : CFSG.SectionRank.IsKGroupCat ↥L) : CFSG.SectionRank.IsKGroupCat X :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent (X ⧸ L) := h2.isNilpotent
  CFSG.KCore.KGroupAllSimple.of_ker CFSG.SectionRank.catalog_isoInvariant (QuotientGroup.mk' L)
    (hL.of_mulEquiv (MulEquiv.subgroupCongr (QuotientGroup.ker_mk' L)))
    (CFSG.KCore.KGroupAllSimple.of_isSolvable CFSG.SectionRank.catalog_containsAbelianSimple
      inferInstance)

section Setting

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

variable (h : B51Hyp G L)
include h

theorem fstar_eq : quasithinGenFitting G = L ⊔ centerOf G := h.1

theorem quasi_L : CFSG.IsQuasisimple ↥L := h.2.1

theorem le_G : L ≤ G := h.2.2.2.1

theorem o2_G : pCoreOf 2 G = ⊥ := h.2.2.2.2.1

omit [Finite V] h in
theorem central_comm (G : Subgroup (MulAut V)) : ∀ z ∈ centerOf G, ∀ g ∈ G, z * g = g * z := by
  intro z hz g hg
  exact (Subgroup.mem_centralizer_iff.1 hz.2 g hg).symm

theorem normal_L : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
  have hq := quasi_L h
  have hLG := le_G h
  have hF := fstar_eq h
  have hperf : ⁅L, L⁆ = L := by
    have : Group.IsPerfect ↥L := hq.1
    exact Subgroup.commutator_eq_self
  set Z := centerOf G with hZ
  have hZG : Z ≤ G := fun z hz => hz.1
  have hZn : Z ≤ Subgroup.normalizer (L : Set (MulAut V)) := by
    intro z hz
    have hzc : z ∈ Subgroup.centralizer (L : Set (MulAut V)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact (central_comm G z hz l (hLG hl)).symm
    exact Subgroup.centralizer_le_normalizer _ hzc
  have hdec : ∀ x ∈ quasithinGenFitting G, ∃ l ∈ L, ∃ z ∈ Z, x = l * z := by
    intro x hx
    rw [hF] at hx
    exact (B19Aux.mem_sup_iff_of_le_normalizer hZn).1 hx
  intro g hg l hl
  have hFn : ∀ x ∈ L, g * x * g⁻¹ ∈ quasithinGenFitting G := by
    intro x hx
    have := (Subgroup.mem_normalizer_iff.1 (le_normalizer_quasithinGenFitting G hg) x).1
    refine this ?_
    rw [hF]
    exact Subgroup.mem_sup_left hx
  have hconj : ∀ x ∈ L, g * x * g⁻¹ ∈ L ⊔ Z := fun x hx => hF ▸ hFn x hx
  have hcomm : ∀ x ∈ ⁅L, L⁆, g * x * g⁻¹ ∈ L := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hy
      obtain ⟨l₁, hl₁, z₁, hz₁, he₁⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hZn).1 (hconj a ha)
      obtain ⟨l₂, hl₂, z₂, hz₂, he₂⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hZn).1 (hconj b hb)
      have hcc : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [hcc, he₁, he₂, comm_mul_central (central_comm G z₁ hz₁ l₂ (hLG hl₂))
        (central_comm G z₁ hz₁ z₂ (hZG hz₂)) (central_comm G z₂ hz₂ l₁ (hLG hl₁))]
      exact Subgroup.commutator_mem_commutator hl₁ hl₂ |> fun h => by
        simpa [hperf] using h
    | one => simp [L.one_mem]
    | mul x y _ _ hx hy =>
      have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [this]; exact L.mul_mem hx hy
    | inv x _ hx =>
      have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [this]; exact L.inv_mem hx
  exact hcomm l (by rw [hperf]; exact hl)


theorem central_le_normalizer : centerOf G ≤ Subgroup.normalizer (L : Set (MulAut V)) := by
  have hLG := le_G h
  intro z hz
  have hzc : z ∈ Subgroup.centralizer (L : Set (MulAut V)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (central_comm G z hz l (hLG hl)).symm
  exact Subgroup.centralizer_le_normalizer _ hzc

theorem mem_fstar_iff {x : MulAut V} :
    x ∈ quasithinGenFitting G ↔ ∃ l ∈ L, ∃ z ∈ centerOf G, x = l * z := by
  rw [fstar_eq h]
  exact B19Aux.mem_sup_iff_of_le_normalizer (central_le_normalizer h)

theorem two_inf_centralizer_eq_bot {Y : Subgroup (MulAut V)} (hYG : Y ≤ G) (hY2 : IsPGroup 2 Y) :
    Y ⊓ Subgroup.centralizer (L : Set (MulAut V)) = ⊥ := by
  have hLG := le_G h
  set Y' := Y ⊓ Subgroup.centralizer (L : Set (MulAut V)) with hY'
  have hY'2 : IsPGroup 2 ↥Y' := hY2.to_le inf_le_left
  have hY'G : Y' ≤ G := inf_le_left.trans hYG
  have hcentF : Y' ≤ Subgroup.centralizer (quasithinGenFitting G : Set (MulAut V)) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    obtain ⟨l, hl, z, hz, rfl⟩ := (mem_fstar_iff h).1 hf
    have h1 : l * y = y * l := (Subgroup.mem_centralizer_iff.1 hy.2 l hl)
    have h2 : z * y = y * z := central_comm G z hz y (hY'G hy)
    calc l * z * y = l * (z * y) := by rw [mul_assoc]
      _ = l * (y * z) := by rw [h2]
      _ = (l * y) * z := by rw [mul_assoc]
      _ = (y * l) * z := by rw [h1]
      _ = y * (l * z) := by rw [mul_assoc]
  have hYF : Y' ≤ quasithinGenFitting G := fun y hy =>
    centralizer_quasithinGenFitting_le G ⟨hY'G hy, hcentF hy⟩
  exact B1More.eq_bot_of_le_center_genFitting (o2_G h) hY'2 hYF hcentF

theorem odd_orderOf_of_mem_centralizer {x : MulAut V} (hxG : x ∈ G)
    (hxc : x ∈ Subgroup.centralizer (L : Set (MulAut V))) : Odd (orderOf x) := by
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  obtain ⟨m, hm⟩ := hev
  have hord : 0 < orderOf x := orderOf_pos x
  set y := x ^ (orderOf x / 2) with hy
  have hy2 : orderOf y = 2 := by
    rw [hy, orderOf_pow_orderOf_div (orderOf_pos x).ne' (by omega)]
  have hYG : Subgroup.zpowers y ≤ G := by
    rw [Subgroup.zpowers_le]
    exact G.pow_mem hxG _
  have hY2 : IsPGroup 2 ↥(Subgroup.zpowers y) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hy2]
    simp
  have hyc : y ∈ Subgroup.centralizer (L : Set (MulAut V)) :=
    Subgroup.pow_mem _ hxc _
  have hbot := two_inf_centralizer_eq_bot h hYG hY2
  have hymem : y ∈ Subgroup.zpowers y ⊓ Subgroup.centralizer (L : Set (MulAut V)) :=
    ⟨Subgroup.mem_zpowers y, hyc⟩
  rw [hbot, Subgroup.mem_bot] at hymem
  rw [hymem, orderOf_one] at hy2
  omega

theorem sup_inf_centralizer_le {T : Subgroup (MulAut V)} (hTG : T ≤ G) (hT2 : IsPGroup 2 T) :
    (L ⊔ T) ⊓ Subgroup.centralizer (L : Set (MulAut V)) ≤ L := by
  intro x hx
  have hLTG : L ⊔ T ≤ G := sup_le (le_G h) hTG
  have hTn : T ≤ Subgroup.normalizer (L : Set (MulAut V)) := fun t ht =>
    Subgroup.mem_normalizer_iff.2 fun l =>
      ⟨fun hl => normal_L h t (hTG ht) l hl, fun hl => by
        have := normal_L h t⁻¹ (G.inv_mem (hTG ht)) _ hl
        simpa [mul_assoc] using this⟩
  exact B1Red.mem_of_odd_orderOf_of_mem_sup hT2 hTn hx.1
    (odd_orderOf_of_mem_centralizer h (hLTG hx.1) hx.2)


theorem hTn_of {T : Subgroup (MulAut V)} (hTG : T ≤ G) :
    T ≤ Subgroup.normalizer (L : Set (MulAut V)) := fun t ht =>
  Subgroup.mem_normalizer_iff.2 fun l =>
    ⟨fun hl => normal_L h t (hTG ht) l hl, fun hl => by
      have := normal_L h t⁻¹ (G.inv_mem (hTG ht)) _ hl
      simpa [mul_assoc] using this⟩

theorem normal_le_of_not_ge {M N : Subgroup (MulAut V)} (hLM : L ≤ M)
    (hLn : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L)
    (hCL : M ⊓ Subgroup.centralizer (L : Set (MulAut V)) ≤ L) (hNM : N ≤ M)
    (hN : ∀ m ∈ M, ∀ n ∈ N, m * n * m⁻¹ ∈ N) (hNL : ¬ L ≤ N) :
    N ≤ L ∧ N ≤ Subgroup.centralizer (L : Set (MulAut V)) := by
  have hL := quasi_L h
  have hLo : CFSG.Open.IsQuasisimple ↥L := ⟨Group.isPerfect_def.mp hL.1, hL.2.1⟩
  have hcentral : N ⊓ L ≤ Subgroup.centralizer (L : Set (MulAut V)) := by
    have hnorm : ((N ⊓ L).subgroupOf L).Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      refine ⟨?_, ?_⟩
      · have := hN (g : MulAut V) (hLM g.2) x hx.1
        simpa using this
      · exact L.mul_mem (L.mul_mem g.2 hx.2) (L.inv_mem g.2)
    have hne : (N ⊓ L).subgroupOf L ≠ ⊤ := by
      intro h'
      apply hNL
      intro l hl
      have : (⟨l, hl⟩ : L) ∈ (N ⊓ L).subgroupOf L := by rw [h']; trivial
      rw [Subgroup.mem_subgroupOf] at this
      exact this.1
    have hc := CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hLo _ hne
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hx' : (⟨x, hx.2⟩ : L) ∈ (N ⊓ L).subgroupOf L := hx
    have := Subgroup.mem_center_iff.mp (hc hx') ⟨l, hl⟩
    exact congrArg Subtype.val this
  have hcomm : ⁅N, L⁆ ≤ N ⊓ L := by
    rw [Subgroup.commutator_le]
    intro n hn l hl
    refine ⟨?_, ?_⟩
    · have h1 := hN l (hLM hl) n⁻¹ (N.inv_mem hn)
      have : n * l * n⁻¹ * l⁻¹ = n * (l * n⁻¹ * l⁻¹) := by simp [mul_assoc]
      show n * l * n⁻¹ * l⁻¹ ∈ N
      rw [this]
      exact N.mul_mem hn h1
    · have h1 := hLn n (hNM hn) l hl
      show n * l * n⁻¹ * l⁻¹ ∈ L
      exact L.mul_mem h1 (L.inv_mem hl)
  have h1 : ⁅⁅N, L⁆, L⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hcomm.trans hcentral)
  have h2 : ⁅⁅L, N⁆, L⁆ = ⊥ := by rw [Subgroup.commutator_comm L N]; exact h1
  have h3 : ⁅⁅L, L⁆, N⁆ = ⊥ := three_subgroup_lemma h2 h1
  have hperf : Group.IsPerfect ↥L := hL.1
  rw [Subgroup.commutator_eq_self] at h3
  have h4 : N ≤ Subgroup.centralizer (L : Set (MulAut V)) := by
    rw [Subgroup.commutator_comm] at h3
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3
  exact ⟨fun x hx => hCL ⟨hNM hx, h4 hx⟩, h4⟩


section SupT

variable {T : Subgroup (MulAut V)} (hTG : T ≤ G) (hT2 : IsPGroup 2 T)
include h hTG hT2

omit hT2 in
theorem sup_normal_L : ∀ m ∈ L ⊔ T, ∀ l ∈ L, m * l * m⁻¹ ∈ L := by
  intro m hm l hl
  obtain ⟨l', hl', t, ht, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer (hTn_of h hTG)).1 hm
  have e : l' * t * l * (l' * t)⁻¹ = l' * (t * l * t⁻¹) * l'⁻¹ := by group
  rw [e]
  exact L.mul_mem (L.mul_mem hl' (normal_L h t (hTG ht) l hl)) (L.inv_mem hl')

theorem sup_two_pow_mem : ∀ m ∈ L ⊔ T, ∃ k : ℕ, m ^ 2 ^ k ∈ L := by
  intro m hm
  obtain ⟨l, hl, t, ht, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer (hTn_of h hTG)).1 hm
  obtain ⟨j, hj⟩ := hT2 ⟨t, ht⟩
  have htj : t ^ 2 ^ j = 1 := congrArg Subtype.val hj
  obtain ⟨x', hx', hx⟩ := A4.exists_pow_mul_eq hl (hTn_of h hTG ht) (2 ^ j)
  rw [htj, mul_one] at hx
  exact ⟨j, hx ▸ hx'⟩

omit hT2 in
theorem sub_normal_inst : (L.subgroupOf (L ⊔ T)).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  have := sup_normal_L h hTG (g : MulAut V) g.2 x hx
  simpa using this

theorem quot_isPGroup [(L.subgroupOf (L ⊔ T)).Normal] :
    IsPGroup 2 (↥(L ⊔ T) ⧸ L.subgroupOf (L ⊔ T)) := by
  intro q
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨k, hk⟩ := sup_two_pow_mem h hTG hT2 (m : MulAut V) m.2
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact hk

theorem genFitting_sup_le : quasithinGenFitting (L ⊔ T) ≤ L := by
  have hLG := le_G h
  have hq := quasi_L h
  have hLM : L ≤ L ⊔ T := le_sup_left
  have hCL := sup_inf_centralizer_le h hTG hT2
  have hLn := sup_normal_L h hTG
  refine sup_le (sSup_le ?_) (sSup_le ?_)
  · rintro N ⟨hNM, hNn, hNnil⟩
    by_cases hLN : L ≤ N
    · exfalso
      have hnil : Group.IsNilpotent (L.subgroupOf N) := inferInstance
      have hnilL : Group.IsNilpotent ↥L :=
        (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hLN)).mp hnil
      have hperf : Group.IsPerfect ↥L := hq.1
      have hnt : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial
        (B1Red.isQuasisimple_to_open hq)
      exact Group.IsPerfect.not_isNilpotent ↥L hnilL
    · refine (normal_le_of_not_ge h hLM hLn hCL hNM ?_ hLN).1
      intro m hm n hn
      have := hNn.conj_mem ⟨n, hNM hn⟩ (by simpa [Subgroup.mem_subgroupOf] using hn) ⟨m, hm⟩
      simpa [Subgroup.mem_subgroupOf] using this
  · rintro K ⟨hKM, hKsub, hKq⟩
    have := sub_normal_inst h hTG
    have : IsPGroup 2 (↥(L ⊔ T) ⧸ L.subgroupOf (L ⊔ T)) := quot_isPGroup h hTG hT2
    have : Group.IsNilpotent (↥(L ⊔ T) ⧸ L.subgroupOf (L ⊔ T)) := IsPGroup.isNilpotent this
    have hKperf : Group.IsPerfect ↥K := by
      have := hKq.1
      exact ⟨this⟩
    set f : ↥K →* (↥(L ⊔ T) ⧸ L.subgroupOf (L ⊔ T)) :=
      (QuotientGroup.mk' (L.subgroupOf (L ⊔ T))).comp (Subgroup.inclusion hKM) with hf
    have : Group.IsPerfect ↥f.range := Group.IsPerfect.range f
    have hrange : f.range = ⊥ := by
      by_contra hne
      have : Nontrivial ↥f.range := (Subgroup.nontrivial_iff_ne_bot _).2 hne
      exact Group.IsPerfect.not_isSolvable ↥f.range inferInstance
    intro k hk
    have : f ⟨k, hk⟩ = 1 := by
      have hmem : f ⟨k, hk⟩ ∈ f.range := ⟨_, rfl⟩
      rw [hrange, Subgroup.mem_bot] at hmem
      exact hmem
    simpa [hf, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] using this


omit hT2 in
theorem le_genFitting_sup : L ≤ quasithinGenFitting (L ⊔ T) := by
  have hq := quasi_L h
  have hcomp : CFSG.Open.IsComponentOf L (L ⊔ T) := by
    refine ⟨le_sup_left, ?_, B1Red.isQuasisimple_to_open hq⟩
    have hnorm : (L.subgroupOf (L ⊔ T)).Normal := sub_normal_inst h hTG
    exact CFSG.Open.IsSubnormal.step le_sup_left hnorm (CFSG.Open.IsSubnormal.refl _)
  exact le_sup_of_le_right (le_sSup hcomp)

theorem genFitting_sup_eq : quasithinGenFitting (L ⊔ T) = L :=
  le_antisymm (genFitting_sup_le h hTG hT2) (le_genFitting_sup h hTG)

theorem pCoreOf_sup_eq_bot : pCoreOf 2 (L ⊔ T) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLG := le_G h
  have hq := quasi_L h
  have hO2 := o2_G h
  have hCL := sup_inf_centralizer_le h hTG hT2
  have hLn := sup_normal_L h hTG
  set M := L ⊔ T with hM
  set R := pCoreOf 2 M with hR
  have hR2 : IsPGroup 2 ↥R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hRM : R ≤ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M
  have hRn : ∀ m ∈ M, ∀ r ∈ R, m * r * m⁻¹ ∈ R := fun m hm r hr =>
    B1Red.conj_mem_pCoreOf_prime 2 hm hr
  have hRL : R ⊓ L = ⊥ := by
    set N := R ⊓ L with hN
    have hN2 : IsPGroup 2 ↥N := hR2.to_le inf_le_left
    have hnorm : L ≤ Subgroup.normalizer (N : Set (MulAut V)) :=
      le_normalizer_of_conj fun l hl n hn => ⟨hRn l (Subgroup.mem_sup_left hl) n hn.1,
        L.mul_mem (L.mul_mem hl hn.2) (L.inv_mem hl)⟩
    have h1 : N ≤ pCoreOf 2 L :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hnorm hN2
    have hsub : CFSG.Open.IsSubnormal L G := by
      have hnormG : (L.subgroupOf G).Normal := by
        refine ⟨fun x hx g => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        have := normal_L h (g : MulAut V) g.2 x hx
        simpa using this
      exact CFSG.Open.IsSubnormal.step hLG hnormG (CFSG.Open.IsSubnormal.refl _)
    have h2 : pCoreOf 2 L ≤ pCoreOf 2 G := A4.pCoreOf_le_of_subnormal 2 hsub
    rw [hO2] at h2
    exact le_bot_iff.1 (h1.trans h2)
  have hRc : R ≤ Subgroup.centralizer (L : Set (MulAut V)) := by
    have hcomm : ⁅R, L⁆ ≤ R ⊓ L := by
      rw [Subgroup.commutator_le]
      intro r hr l hl
      refine ⟨?_, ?_⟩
      · have h1 := hRn l (Subgroup.mem_sup_left hl) r⁻¹ (R.inv_mem hr)
        have : r * l * r⁻¹ * l⁻¹ = r * (l * r⁻¹ * l⁻¹) := by simp [mul_assoc]
        show r * l * r⁻¹ * l⁻¹ ∈ R
        rw [this]
        exact R.mul_mem hr h1
      · have h1 := hLn r (hRM hr) l hl
        show r * l * r⁻¹ * l⁻¹ ∈ L
        exact L.mul_mem h1 (L.inv_mem hl)
    rw [hRL] at hcomm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 (le_bot_iff.1 hcomm)
  rw [eq_bot_iff]
  intro r hr
  have hrL : r ∈ L := hCL ⟨hRM hr, hRc hr⟩
  have : r ∈ R ⊓ L := ⟨hr, hrL⟩
  rw [hRL] at this
  exact this

theorem sqtk_sup : SQTKGroup ↥(L ⊔ T) := by
  have hSQ : SQTKGroup ↥L := h.2.2.1
  have hnorm := sub_normal_inst h hTG
  have hq : IsPGroup 2 (↥(L ⊔ T) ⧸ L.subgroupOf (L ⊔ T)) := quot_isPGroup h hTG hT2
  let e : ↥(L.subgroupOf (L ⊔ T)) ≃* ↥L := Subgroup.subgroupOfEquivOfLe le_sup_left
  have hLm : SQTKGroup ↥(L.subgroupOf (L ⊔ T)) := by
    refine ⟨fun p hp hp2 => ?_, hSQ.2.of_mulEquiv e⟩
    show CFSG.Open.pRank p (⊤ : Subgroup ↥(L.subgroupOf (L ⊔ T))) ≤ 2
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
    exact hSQ.1 p hp hp2
  exact ⟨sqt_of_two_quotient _ hq hLm.1, kGroup_of_two_quotient _ hq hLm.2⟩

end SupT

end Setting

end B5

end CFSG.Quasithin
