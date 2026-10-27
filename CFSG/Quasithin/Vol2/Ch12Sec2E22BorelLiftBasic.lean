module

public import CFSG.Quasithin.Background.E6TorusFacts
public import CFSG.GroupTheory.SolvableHallNodes
public import CFSG.Quasithin.Background.A3StructureBasic
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

namespace E2.BorelLift

variable {Γ : Type} [Group Γ]

theorem card_sup_mul_card_inf {A B : Subgroup Γ} (hAB : A ≤ Subgroup.normalizer (B : Set Γ)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B := by
  have h1 : B.relIndex (A ⊔ B) = B.relIndex A := A4.relIndex_sup_eq_of_le_normalizer' hAB
  have h2 : B.relIndex (A ⊔ B) * Nat.card ↥(B ⊓ (A ⊔ B)) = Nat.card ↥(A ⊔ B) :=
    Subgroup.relIndex_mul_card _ _
  have h3 : B.relIndex A * Nat.card ↥(B ⊓ A) = Nat.card A := Subgroup.relIndex_mul_card _ _
  rw [inf_eq_left.mpr (le_sup_right : B ≤ A ⊔ B)] at h2
  rw [← h2, h1, inf_comm A B, ← h3]
  ring

theorem le_of_odd {N X C : Subgroup Γ} (hNX : N ≤ X) (hXN : X ≤ Subgroup.normalizer (N : Set Γ))
    {k : ℕ} (hk : N.relIndex X = 2 ^ k) (hCX : C ≤ X) (hC : Odd (Nat.card C)) : C ≤ N := by
  have hCN : C ≤ Subgroup.normalizer (N : Set Γ) := hCX.trans hXN
  have h1 : N.relIndex (C ⊔ N) = N.relIndex C := A4.relIndex_sup_eq_of_le_normalizer' hCN
  have h2 : N.relIndex (C ⊔ N) ∣ 2 ^ k := by
    rw [← hk]
    exact dvd_of_mul_right_eq _ (Subgroup.relIndex_mul_relIndex _ _ _ le_sup_right (sup_le hCX hNX))
  have h3 : N.relIndex C ∣ Nat.card C := Subgroup.relIndex_dvd_card _ _
  rw [h1] at h2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
  have hodd : Odd (N.relIndex C) := hC.of_dvd_nat h3
  have hj0 : j = 0 := by
    rcases j with _ | j
    · rfl
    · exfalso
      rw [hj, pow_succ] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_two.mul_left _)
  rw [hj0, pow_zero] at hj
  exact Subgroup.relIndex_eq_one.mp hj

variable [Finite Γ]

theorem inf_eq_bot_of_odd {A N : Subgroup Γ} (hA : Odd (Nat.card A)) (hN : IsPGroup 2 N) :
    A ⊓ N = ⊥ := by
  have hcop : Nat.Coprime (Nat.card A) (Nat.card N) := by
    obtain ⟨k, hk⟩ := hN.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hA)
  exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)

theorem exists_conj_of_card_eq {N A A' : Subgroup Γ} (hN : IsPGroup 2 N) (hA : Odd (Nat.card A))
    (hAN : A ≤ Subgroup.normalizer (N : Set Γ)) (hA'le : A' ≤ A ⊔ N)
    (hcard : Nat.card A' = Nat.card A) :
    ∃ n ∈ N, A' = A.map (MulAut.conj n⁻¹).toMonoidHom := by
  classical
  set F : Subgroup Γ := A ⊔ N with hF
  have hFN : F ≤ Subgroup.normalizer (N : Set Γ) := sup_le hAN Subgroup.le_normalizer
  set N' : Subgroup F := N.subgroupOf F with hN'
  have hN'n : N'.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hFN
  have hA'odd : Odd (Nat.card A') := hcard ▸ hA
  have hAN0 : A ⊓ N = ⊥ := inf_eq_bot_of_odd hA hN
  have hA'N0 : A' ⊓ N = ⊥ := inf_eq_bot_of_odd hA'odd hN
  have hcN' : Nat.card N' = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  have hcF : Nat.card F = Nat.card A * Nat.card N := by
    have h := card_sup_mul_card_inf hAN
    rw [hAN0, Subgroup.card_bot, mul_one] at h
    exact h
  have hNpos : 0 < Nat.card N := Nat.card_pos
  have hindex : N'.index = Nat.card A := by
    have h := N'.card_mul_index
    rw [hcN', hcF, mul_comm (Nat.card A)] at h
    exact Nat.eq_of_mul_eq_mul_left hNpos h
  have hNsolv : Group.IsSolvable N' := by
    have h2 : IsPGroup 2 N' := hN.of_equiv (Subgroup.subgroupOfEquivOfLe le_sup_right).symm
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := h2.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card N') N'.index := by
    rw [hcN', hindex]
    obtain ⟨k, hk⟩ := hN.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hA)
  set H' : Subgroup F := A.subgroupOf F with hH'
  set K' : Subgroup F := A'.subgroupOf F with hK'
  have hcH' : Nat.card H' = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
  have hcK' : Nat.card K' = Nat.card A :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA'le).toEquiv).trans hcard
  have hbot : ∀ B : Subgroup Γ, B ⊓ N = ⊥ → N' ⊓ B.subgroupOf F = ⊥ := by
    intro B hB
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have hx : (x : Γ) ∈ B ⊓ N := ⟨hx2, hx1⟩
    rw [hB, Subgroup.mem_bot] at hx
    exact Subgroup.mem_bot.mpr (Subtype.ext hx)
  have hNH : N' ⊓ H' = ⊥ := hbot A hAN0
  have hNK : N' ⊓ K' = ⊥ := hbot A' hA'N0
  have hcardF : Nat.card F = Nat.card A * Nat.card N := hcF
  have huniv : ∀ L : Subgroup F, Nat.card L = Nat.card A → N' ⊓ L = ⊥ →
      (N' : Set F) * (L : Set F) = Set.univ := by
    intro L hL hNL
    have hc := Subgroup.isComplement'_of_card_mul_and_disjoint (H := N') (K := L)
      (by rw [hcN', hL, mul_comm, ← hcardF])
      (disjoint_iff.mpr hNL)
    rw [← Subgroup.normal_mul, hc.sup_eq_top, Subgroup.coe_top]
  obtain ⟨n, hn, hKeq⟩ := CFSG.SolvableHall.solvable_normal_hall_complement_conjugacy N'
    hNsolv hcop (huniv H' hcH' hNH) (huniv K' hcK' hNK) hNH hNK
  refine ⟨(n : Γ), hn, ?_⟩
  ext x
  constructor
  · intro hx
    have hxK : (⟨x, hA'le hx⟩ : F) ∈ K' := hx
    rw [hKeq] at hxK
    obtain ⟨y, hy, hyx⟩ := hxK
    refine ⟨(y : Γ), hy, ?_⟩
    have := congrArg Subtype.val hyx
    simpa using this
  · rintro ⟨y, hy, rfl⟩
    have hyF : y ∈ F := (le_sup_left : A ≤ A ⊔ N) hy
    have hmem : (MulAut.conj (n⁻¹ : F)).toMonoidHom ⟨y, hyF⟩ ∈ K' := by
      rw [hKeq]
      exact ⟨⟨y, hyF⟩, hy, rfl⟩
    have h1 : ((MulAut.conj (n⁻¹ : F)).toMonoidHom ⟨y, hyF⟩ : Γ) =
        (MulAut.conj (n : Γ)⁻¹).toMonoidHom y := by
      simp
    rw [← h1]
    exact hmem

theorem exists_complement {R X : Subgroup Γ} (hRX : R ≤ X)
    (hXR : X ≤ Subgroup.normalizer (R : Set Γ)) (hR : IsPGroup 2 R) (hodd : Odd (R.relIndex X)) :
    ∃ C : Subgroup Γ, C ≤ X ∧ Nat.card C = R.relIndex X ∧ C ⊓ R = ⊥ := by
  classical
  set N : Subgroup X := R.subgroupOf X with hN
  have hNn : N.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hXR
  have hcN : Nat.card N = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRX).toEquiv
  have hcop : Nat.Coprime (Nat.card N) N.index := by
    rw [hcN]
    obtain ⟨k, hk⟩ := hR.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  obtain ⟨H', hH'⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  refine ⟨H'.map X.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective X.subtype_injective]
    have h1 := hH'.card_mul_card
    have h2 := N.card_mul_index
    have hpos : 0 < Nat.card N := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
  · rw [eq_bot_iff]
    rintro _ ⟨⟨x, hx, rfl⟩, hxR⟩
    have hxN : x ∈ N := hxR
    have := Subgroup.disjoint_def.mp hH'.disjoint hxN hx
    rw [this]
    exact Subgroup.one_mem _

theorem odd_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨2 ^ m - 1, ?_⟩
  have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  rw [pow_succ]
  omega

omit [Finite Γ] in
theorem mem_normalizer_subgroupOf_iff {S K : Subgroup Γ} (hSK : S ≤ K) (k : ↥K) :
    k ∈ Subgroup.normalizer ((S.subgroupOf K : Subgroup ↥K) : Set ↥K) ↔
      (k : Γ) ∈ Subgroup.normalizer (S : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    constructor
    · intro hy
      have h1 := (h ⟨y, hSK hy⟩).mp hy
      exact h1
    · intro hy
      have hyK : y ∈ K := by
        have h2 : (k : Γ) * y * (k : Γ)⁻¹ ∈ K := hSK hy
        have h3 : y = (k : Γ)⁻¹ * ((k : Γ) * y * (k : Γ)⁻¹) * (k : Γ) := by group
        rw [h3]
        exact K.mul_mem (K.mul_mem (K.inv_mem k.2) h2) k.2
      exact (h ⟨y, hyK⟩).mpr hy
  · intro h x
    exact h x

theorem torus_of_cover (hTor : E2.E22TorusCover) {K : Subgroup Γ} {X' : Type} [Group X']
    (ρ : ↥K →* X') (hρ : Function.Surjective ρ) (hO : CFSG.pCore 2 ↥K ≤ ρ.ker)
    (hZ : ∀ k ∈ ρ.ker, ∀ x : ↥K, k * x * k⁻¹ * x⁻¹ ∈ CFSG.pCore 2 ↥K)
    {n : ℕ} (hn : 2 ≤ n) (hty : IsBenderOf n X' ∨ IsPSL 3 2 n X' ∨ IsPSp4 2 n X')
    {S : Subgroup Γ} (hS : IsSylowTwoOf S K) :
    (∀ a ∈ K ⊓ Subgroup.normalizer (S : Set Γ), ∀ b ∈ K ⊓ Subgroup.normalizer (S : Set Γ),
        a * b * a⁻¹ * b⁻¹ ∈ S) ∧
    ∃ (Y : Subgroup Γ) (w : Γ), Y ≤ K ⊓ Subgroup.normalizer (S : Set Γ) ∧ IsCyclic ↥Y ∧
      Nat.card Y = 2 ^ n - 1 ∧ w ∈ K ∧ w ∉ Subgroup.normalizer (S : Set Γ) ∧
      ∀ y ∈ Y, w * y * w⁻¹ * y ∈ pCoreOf 2 K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O : Subgroup K := CFSG.pCore 2 ↥K with hOdef
  have hOn : O.Normal := CFSG.pCore_normal
  have hO2 : IsPGroup 2 O := CFSG.pCore_isPGroup
  set π : ↥K →* ↥K ⧸ O := QuotientGroup.mk' O with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective O
  have hπk : π.ker = O := QuotientGroup.ker_mk' O
  set φ : ↥K ⧸ O →* X' := QuotientGroup.lift O ρ hO with hφ
  have hφs : Function.Surjective φ := by
    intro x
    obtain ⟨k, rfl⟩ := hρ x
    exact ⟨π k, rfl⟩
  have hφker : φ.ker ≤ Subgroup.center (↥K ⧸ O) := by
    intro q hq
    obtain ⟨k, rfl⟩ := hπs q
    have hk : k ∈ ρ.ker := hq
    rw [Subgroup.mem_center_iff]
    intro q'
    obtain ⟨x, rfl⟩ := hπs q'
    have h1 := hZ k hk x
    have h2 : π (k * x * k⁻¹ * x⁻¹) = 1 := by
      rw [← MonoidHom.mem_ker, hπk]
      exact h1
    have h3 : π k * π x = π x * π k := by
      simp only [map_mul, map_inv] at h2
      calc π k * π x = (π k * π x * (π k)⁻¹ * (π x)⁻¹) * (π x * π k) := by group
        _ = π x * π k := by rw [h2, one_mul]
    exact h3.symm
  have hφodd : Odd (Nat.card φ.ker) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hev)
    have hz1 : (z : ↥K ⧸ O) ≠ 1 := by
      intro h
      rw [← Subgroup.orderOf_coe, h, orderOf_one] at hz
      exact absurd hz (by norm_num)
    have hzc : (z : ↥K ⧸ O) ∈ Subgroup.center (↥K ⧸ O) := hφker z.2
    have hzp : IsPGroup 2 (Subgroup.zpowers (z : ↥K ⧸ O)) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz, pow_one]
    have hzn : (Subgroup.zpowers (z : ↥K ⧸ O)).Normal := by
      refine ⟨fun x hx g => ?_⟩
      have hxc : x ∈ Subgroup.center (↥K ⧸ O) :=
        (Subgroup.zpowers_le.mpr hzc) hx
      rw [Subgroup.mem_center_iff] at hxc
      rw [hxc g, mul_inv_cancel_right]
      exact hx
    have hle : Subgroup.zpowers (z : ↥K ⧸ O) ≤ CFSG.pCore 2 (↥K ⧸ O) := by
      exact CFSG.LieType.BorelTits.le_pCore 2 hzn hzp
    rw [pCore_two_quotient_pCore_two] at hle
    exact hz1 (Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers _)))
  set S' : Subgroup K := S.subgroupOf K with hS'
  have hOS : O ≤ S' := by
    have := hO2.le_sylow_of_normal (A4.toSylow hS)
    rwa [A4.toSylow_coe] at this
  set Sh : Subgroup (↥K ⧸ O) := S'.map π with hSh
  have hcomap : Sh.comap π = S' := by
    rw [hSh, Subgroup.comap_map_eq, hπk, sup_eq_left.mpr hOS]
  have hShSyl : IsSylowTwoOf Sh ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · have h2 : IsPGroup 2 S' := hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
      exact h2.map π
    · intro hdvd
      change 2 ∣ Sh.relIndex ⊤ at hdvd
      rw [Subgroup.relIndex_top_right] at hdvd
      exact hS.2.2 (hdvd.trans (Subgroup.index_map_dvd S' hπs))
  have hnorm : ∀ k : ↥K, π k ∈ Subgroup.normalizer (Sh : Set (↥K ⧸ O)) ↔
      (k : Γ) ∈ Subgroup.normalizer (S : Set Γ) := by
    intro k
    rw [← mem_normalizer_subgroupOf_iff hS.1, ← hS', ← hcomap,
      ← Subgroup.comap_normalizer_eq_of_surjective Sh hπs]
    rfl
  obtain ⟨hcomm, Yh, wh, hYN, hYc, hYcard, hwN, hwY⟩ :=
    hTor (↥K ⧸ O) X' φ n hφs hφker hφodd hn hty Sh hShSyl
  refine ⟨?_, ?_⟩
  ·
    rintro a ⟨haK, haN⟩ b ⟨hbK, hbN⟩
    have ha := (hnorm ⟨a, haK⟩).mpr haN
    have hb := (hnorm ⟨b, hbK⟩).mpr hbN
    have h1 := hcomm _ ha _ hb
    have h2 : (⟨a, haK⟩ * ⟨b, hbK⟩ * ⟨a, haK⟩⁻¹ * ⟨b, hbK⟩⁻¹ : ↥K) ∈ Sh.comap π := by
      rw [Subgroup.mem_comap]
      simpa only [map_mul, map_inv] using h1
    rw [hcomap] at h2
    exact h2
  ·
    set Yt : Subgroup K := Yh.comap π with hYt
    have hOYt : O ≤ Yt := by
      rw [← hπk]
      exact Subgroup.ker_le_comap π Yh
    have hYtO : Yt ≤ Subgroup.normalizer (O : Set ↥K) := fun x _ => by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      refine ⟨fun hy => hOn.conj_mem y hy x, fun hy => ?_⟩
      have := hOn.conj_mem _ hy x⁻¹
      simpa [mul_assoc] using this
    have hidx : O.relIndex Yt = Nat.card Yh := by
      have h2 : (π.ker).relIndex Yt = Nat.card Yh := by
        rw [← MonoidHom.comap_bot, Subgroup.relIndex_comap, Subgroup.relIndex_bot_left, hYt,
          Subgroup.map_comap_eq_self_of_surjective hπs]
      rwa [hπk] at h2
    have hodd : Odd (O.relIndex Yt) := by
      rw [hidx, hYcard]
      exact odd_two_pow_sub_one (by omega)
    obtain ⟨Y0, hY0Yt, hY0card, hY0O⟩ := exists_complement hOYt hYtO hO2 hodd
    have hinj : Function.Injective (π.comp Y0.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro y hy
      have hy' : (y : ↥K) ∈ O := by
        rw [← hπk]
        exact hy
      have : (y : ↥K) ∈ Y0 ⊓ O := ⟨y.2, hy'⟩
      rw [hY0O, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (Subtype.ext this)
    have hmapY : Y0.map π ≤ Yh := by
      rintro _ ⟨y, hy, rfl⟩
      exact hY0Yt hy
    have hcY0 : Nat.card Y0 = Nat.card Yh := by rw [hY0card, hidx]
    have hY0cyc : IsCyclic Y0 := by
      have : IsCyclic Yh := hYc
      have hf : ∀ y : Y0, π y ∈ Yh := fun y => hmapY ⟨y, y.2, rfl⟩
      exact isCyclic_of_injective ((π.comp Y0.subtype).codRestrict Yh hf)
        (fun a b hab => hinj (congrArg Subtype.val hab))
    obtain ⟨w0, rfl⟩ := hπs wh
    refine ⟨Y0.map K.subtype, (w0 : Γ), ?_, ?_, ?_, w0.2, ?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨y.2, (hnorm y).mp (hYN (hY0Yt hy))⟩
    · exact isCyclic_of_injective
        (Subgroup.equivMapOfInjective Y0 K.subtype K.subtype_injective).symm.toMonoidHom
        (Subgroup.equivMapOfInjective Y0 K.subtype K.subtype_injective).symm.injective
    · rw [Subgroup.card_map_of_injective K.subtype_injective, hcY0, hYcard]
    · intro h
      exact hwN ((hnorm w0).mpr h)
    · rintro _ ⟨y, hy, rfl⟩
      have h1 := hwY (π y) (hY0Yt hy)
      have h2 : w0 * y * w0⁻¹ * y ∈ O := by
        rw [← hπk, MonoidHom.mem_ker]
        simp only [map_mul, map_inv, h1, inv_mul_cancel]
      have hpc : pCoreOf 2 K = O.map K.subtype := by
        rw [hOdef]
        rfl
      rw [hpc]
      exact ⟨_, h2, rfl⟩

end E2.BorelLift

end CFSG.Quasithin
