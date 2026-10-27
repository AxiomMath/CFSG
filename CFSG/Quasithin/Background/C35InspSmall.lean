module

public import CFSG.Quasithin.Background.C35InspLift
public import CFSG.Quasithin.Background.C48PfFourModPfGrp
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFactsPSL2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6TitsLattice
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6A312Over

public section

namespace CFSG.Quasithin.C35Pf

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def SolvOver (X : Type) [Group X] : Prop :=
  ∀ T M : Subgroup X, IsSylowTwoOf T ⊤ → T ≤ M → M ≠ ⊤ → Group.IsSolvable ↥M

theorem SolvOver.of_mulEquiv {X X' : Type} [Group X] [Group X'] [Finite X] (e : X ≃* X')
    (h : SolvOver X) : SolvOver X' := by
  have : Finite X' := Finite.of_equiv X e.toEquiv
  intro T M hT hTM hM
  have hT' : IsSylowTwoOf (T.map e.symm.toMonoidHom) ⊤ := by
    have := CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.1 hT
    refine CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.2 ?_
    have h2 := CFSG.QuasithinUnique.Setup.X6.isSylowOf_map_injective e.symm.toMonoidHom
      e.symm.injective this
    rwa [Subgroup.map_top_of_surjective _ e.symm.surjective] at h2
  have hM' : M.map e.symm.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hM
    have := congrArg (Subgroup.map e.toMonoidHom) htop
    rwa [Subgroup.map_map, Subgroup.map_top_of_surjective _ e.surjective,
      show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id X' by ext; simp,
      Subgroup.map_id] at this
  have hs := h _ _ hT' (Subgroup.map_mono hTM) hM'
  exact Group.isSolvable_of_isSolvable_injective
    (f := (M.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).toMonoidHom)
    (M.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).injective

theorem solvOver_of_sylow {X : Type} [Group X] [Finite X] {T₀ : Subgroup X}
    (hT₀ : IsSylowTwoOf T₀ ⊤) (h : ∀ M : Subgroup X, T₀ ≤ M → M ≠ ⊤ → Group.IsSolvable ↥M) :
    SolvOver X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro T M hT hTM hM
  obtain ⟨P, rfl⟩ := CFSG.QuasithinUnique.Unc25K1.exists_sylow_of_isSylowTwoOf_top hT
  obtain ⟨P₀, rfl⟩ := CFSG.QuasithinUnique.Unc25K1.exists_sylow_of_isSylowTwoOf_top hT₀
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P P₀
  let c : X ≃* X := MulAut.conj g
  have hle : (P₀ : Subgroup X) ≤ M.map c.toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact Subgroup.map_mono hTM
  have hne : M.map c.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hM
    have := congrArg (Subgroup.map c.symm.toMonoidHom) htop
    rwa [Subgroup.map_map, Subgroup.map_top_of_surjective _ c.symm.surjective,
      show c.symm.toMonoidHom.comp c.toMonoidHom = MonoidHom.id X by ext; simp,
      Subgroup.map_id] at this
  have hs := h _ hle hne
  exact Group.isSolvable_of_isSolvable_injective
    (f := (M.equivMapOfInjective c.toMonoidHom c.injective).toMonoidHom)
    (M.equivMapOfInjective c.toMonoidHom c.injective).injective

theorem false_of_solvOver {A : Type} [Group A] [Finite A] {K Y M₀ V : Subgroup A}
    (hD : C35Data K Y M₀ V) (h : SolvOver (↥K ⧸ Subgroup.center ↥K)) : False := by
  obtain ⟨T, hT, hTY, -, hne, hns⟩ := exists_overgroup hD
    (φ := QuotientGroup.mk' (Subgroup.center ↥K)) (by rw [QuotientGroup.ker_mk'])
    (QuotientGroup.mk'_surjective _)
  exact hns (h T _ hT hTY hne)

theorem isSolvable_of_card_pow_mul_pow {G : Type*} [Group G] [Finite G] {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (h : Nat.card G = p ^ a * q ^ b) :
    Group.IsSolvable G := by
  let _ : Fintype G := Fintype.ofFinite G
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq hpq
    (by rw [← Nat.card_eq_fintype_card]; exact h)

theorem card_of_isSylowTwoOf {X : Type} [Group X] [Finite X] {T : Subgroup X}
    (hT : IsSylowTwoOf T ⊤) {a m : ℕ} (hX : Nat.card X = 2 ^ a * m) (hm : ¬ 2 ∣ m) :
    Nat.card T = 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hp, hidx⟩ := hT
  rw [index_subgroupOf_top] at hidx
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hmul := T.card_mul_index
  rw [hk, hX] at hmul
  have hka : k = a := by
    rcases lt_trichotomy k a with h | h | h
    · exfalso
      obtain ⟨d, rfl⟩ : ∃ d, a = k + d + 1 := ⟨a - k - 1, by omega⟩
      have : T.index = 2 ^ (d + 1) * m := by
        apply Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num : 0 < 2) k)
        rw [hmul]
        ring
      exact hidx (this ▸ dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) m)
    · exact h
    · exfalso
      obtain ⟨d, rfl⟩ : ∃ d, k = a + d + 1 := ⟨k - a - 1, by omega⟩
      have : 2 ^ (d + 1) * T.index = m := by
        apply Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num : 0 < 2) a)
        rw [← hmul]
        ring
      exact hm (this ▸ dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _)
  rw [hk, hka]

theorem card_le_factorial_index {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {M : Subgroup X} (hM : M ≠ ⊤) : Nat.card X ≤ M.index.factorial := by
  have hfi : M.FiniteIndex := inferInstance
  have h1 := M.index_normalCore_le_factorial_index
  rcases (M.normalCore_normal).eq_bot_or_eq_top with h | h
  · rwa [h, Subgroup.index_bot] at h1
  · exact absurd (eq_top_iff.2 (h ▸ M.normalCore_le)) hM

theorem card_overgroup {X : Type} [Group X] [Finite X] {T M : Subgroup X} (hT : IsSylowTwoOf T ⊤)
    (hTM : T ≤ M) (hM : M ≠ ⊤) {a m : ℕ} (hX : Nat.card X = 2 ^ a * m) (hm : ¬ 2 ∣ m) :
    ∃ k, Nat.card M = 2 ^ a * k ∧ k ∣ m ∧ k ≠ m := by
  have hTc := card_of_isSylowTwoOf hT hX hm
  have h1 : 2 ^ a ∣ Nat.card M := by
    have h := Subgroup.card_dvd_of_le hTM
    rwa [hTc] at h
  obtain ⟨k, hk⟩ := h1
  have hd : 2 ^ a * k ∣ 2 ^ a * m := hk ▸ hX ▸ Subgroup.card_subgroup_dvd_card M
  refine ⟨k, hk, Nat.dvd_of_mul_dvd_mul_left (pow_pos (by norm_num) a) hd, fun h => hM ?_⟩
  exact Subgroup.eq_top_of_card_eq M (by rw [hk, hX, h])

theorem solvOver_of_card60 {X : Type} [Group X] [Finite X] (hX : Nat.card X = 60) :
    SolvOver X := by
  intro T M hT hTM hM
  obtain ⟨k, hk, hkd, hkne⟩ := card_overgroup hT hTM hM (a := 2) (m := 15)
    (by rw [hX]; norm_num) (by decide)
  have key : ∀ k ≤ 15, k ∣ 15 → k ≠ 15 → k = 1 ∨ k = 3 ∨ k = 5 := by decide
  rcases key k (Nat.le_of_dvd (by norm_num) hkd) hkd hkne with rfl | rfl | rfl
  · exact isSolvable_of_card_pow_mul_pow (a := 2) (b := 0) Nat.prime_two Nat.prime_three
      (by norm_num) (by rw [hk]; norm_num)
  · exact isSolvable_of_card_pow_mul_pow (a := 2) (b := 1) Nat.prime_two Nat.prime_three
      (by norm_num) (by rw [hk]; norm_num)
  · exact isSolvable_of_card_pow_mul_pow (a := 2) (b := 1) Nat.prime_two Nat.prime_five
      (by norm_num) (by rw [hk]; norm_num)

theorem solvOver_of_card168 {X : Type} [Group X] [Finite X] (hX : Nat.card X = 168) :
    SolvOver X := by
  intro T M hT hTM hM
  obtain ⟨k, hk, hkd, hkne⟩ := card_overgroup hT hTM hM (a := 3) (m := 21)
    (by rw [hX]; norm_num) (by decide)
  have key : ∀ k ≤ 21, k ∣ 21 → k ≠ 21 → k = 1 ∨ k = 3 ∨ k = 7 := by decide
  rcases key k (Nat.le_of_dvd (by norm_num) hkd) hkd hkne with rfl | rfl | rfl
  · exact isSolvable_of_card_pow_mul_pow (a := 3) (b := 0) Nat.prime_two Nat.prime_three
      (by norm_num) (by rw [hk]; norm_num)
  · exact isSolvable_of_card_pow_mul_pow (a := 3) (b := 1) Nat.prime_two Nat.prime_three
      (by norm_num) (by rw [hk]; norm_num)
  · exact isSolvable_of_card_pow_mul_pow (a := 3) (b := 1) Nat.prime_two (by norm_num : (7).Prime)
      (by norm_num) (by rw [hk]; norm_num)

theorem solvOver_of_card360 {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hX : Nat.card X = 360) : SolvOver X := by
  intro T M hT hTM hM
  obtain ⟨k, hk, hkd, hkne⟩ := card_overgroup hT hTM hM (a := 3) (m := 45)
    (by rw [hX]; norm_num) (by decide)
  have key : ∀ k ≤ 45, k ∣ 45 → k ≠ 45 → k = 1 ∨ k = 3 ∨ k = 5 ∨ k = 9 ∨ k = 15 := by decide
  rcases key k (Nat.le_of_dvd (by norm_num) hkd) hkd hkne with rfl | rfl | rfl | rfl | rfl
  · exact isSolvable_of_card_pow_mul_pow (a := 3) (b := 0) Nat.prime_two Nat.prime_three
      (by norm_num) (by rw [hk]; norm_num)
  · exact isSolvable_of_card_pow_mul_pow (a := 3) (b := 1) Nat.prime_two Nat.prime_three
      (by norm_num) (by rw [hk]; norm_num)
  · exact isSolvable_of_card_pow_mul_pow (a := 3) (b := 1) Nat.prime_two Nat.prime_five
      (by norm_num) (by rw [hk]; norm_num)
  · exact isSolvable_of_card_pow_mul_pow (a := 3) (b := 2) Nat.prime_two Nat.prime_three
      (by norm_num) (by rw [hk]; norm_num)
  · exfalso
    have hidx : M.index = 3 := by
      have := M.card_mul_index
      rw [hk, hX] at this
      omega
    have := card_le_factorial_index hM
    rw [hidx, hX] at this
    norm_num [Nat.factorial] at this

theorem solvOver_of_bender {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hB : fusionIsBenderGroup X) : SolvOver X := by
  intro T M hT hTM hM
  obtain ⟨P, rfl⟩ := CFSG.QuasithinUnique.Unc25K1.exists_sylow_of_isSylowTwoOf_top hT
  exact CFSG.QuasithinUnique.Unc25G2.A312Sub.bender_overgroups hB P hTM hM

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Vol2Native.A312L in
theorem solvOver_of_isPSL2 {X : Type} [Group X] [Finite X] {f : ℕ} (hf : 1 ≤ f)
    (hX : IsPSL 2 2 f X) : SolvOver X := by
  obtain ⟨-, F, hF, hFin, hcard, ⟨e⟩⟩ := hX
  have : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
  let e' : X ≃* projectiveSL 2 F := e.trans (statedSLEquivProjectiveSL 2 F)
  obtain ⟨P, hP⟩ := exists_sylow_projUnitriangular (K := F) 2 (n := 2) (by norm_num)
  have hT₀ : IsSylowTwoOf (projUnitriangular 2 F) ⊤ :=
    hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  exact SolvOver.of_mulEquiv e'.symm (solvOver_of_sylow hT₀ fun M hM hne =>
    isSolvable_of_overgroup_two ⟨f, hcard⟩ M hM hne)

theorem solvOver_of_isPSU3 {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {f : ℕ}
    (hf : 2 ≤ f) (hX : IsPSU 3 2 f X) : SolvOver X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  have hcard : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  let e' : X ≃* CFSG.Open.GLAProj (CFSG.Open.GLASUGroup (Fin 3) K (2 ^ f)) := e
  exact solvOver_of_bender
    (Or.inr (Or.inl ⟨f, hf, ⟨e'.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative f hf hcard)⟩⟩))

theorem solvOver_of_isSz {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {f : ℕ}
    (hX : IsSz f X) : SolvOver X := by
  obtain ⟨a, ha, ⟨e⟩⟩ := CFSG.LieType.Simplicity.exists_mulEquiv_suzukiMatrixGroup_of_suzukiModel hX
  exact solvOver_of_bender
    (Or.inr (Or.inr ⟨a, ha, ⟨e.trans (CFSG.ShultStronglyClosedTI.suzukiCoverNativeEquiv a).symm⟩⟩))

theorem solvOver_of_isTits
    {X : Type} [Group X] [Finite X] (hX : IsTits X) : SolvOver X := by
  intro T M hT hTM hM
  obtain ⟨H, N, -, -, -, -, -, hlat, hHs, hNs⟩ :=
    CFSG.QuasithinUnique.Setup.X6.titsSylowOvergroupLattice X hX T hT
  rcases hlat M hTM with rfl | rfl | rfl | rfl
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := hT.2.1.isNilpotent
    infer_instance
  · exact hHs
  · exact hNs
  · exact absurd rfl hM

theorem small_holds :
    ∀ (A : Type) [Group A] [Finite A] (K Y M₀ V : Subgroup A), C35Data K Y M₀ V →
      ((∃ f : ℕ, (2 ≤ f ∧ IsPSL 2 2 f (↥K ⧸ Subgroup.center ↥K)) ∨
          (2 ≤ f ∧ IsPSU 3 2 f (↥K ⧸ Subgroup.center ↥K)) ∨
          (Odd f ∧ 3 ≤ f ∧ IsSz f (↥K ⧸ Subgroup.center ↥K))) ∨
        IsAlt 5 (↥K ⧸ Subgroup.center ↥K) ∨ IsAlt 6 (↥K ⧸ Subgroup.center ↥K) ∨
        IsPSL 3 2 1 (↥K ⧸ Subgroup.center ↥K) ∨ IsTits (↥K ⧸ Subgroup.center ↥K)) → False := by
  intro A _ _ K Y M₀ V hD hfam
  refine false_of_solvOver hD ?_
  have : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hD.quasisimple.2
  rcases hfam with ⟨f, ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨-, -, h⟩⟩ | h5 | h6 | h | h
  · exact solvOver_of_isPSL2 (by omega) h
  · exact solvOver_of_isPSU3 hf h
  · exact solvOver_of_isSz h
  · obtain ⟨e⟩ := h5
    refine solvOver_of_card60 ?_
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    decide
  · obtain ⟨e⟩ := h6
    refine solvOver_of_card360 ?_
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    decide
  · exact solvOver_of_card168 ((C48Pf.FMod.card_of_isPSL_two_one (Or.inl rfl) h).1 rfl)
  · exact solvOver_of_isTits h

end CFSG.Quasithin.C35Pf
