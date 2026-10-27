module

public import Mathlib
public import CFSG.Foundations.Basic
public import CFSG.Open.Defs
public import CFSG.Open.LocalVocabulary
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Milestones.ASVolI.J1
public import CFSG.Milestones.ASVolI.J2
public import CFSG.Quasithin.Background.ASVolIRu.Bridge
public import CFSG.Quasithin.Background.ASVolIRu.StUnique
public import CFSG.Quasithin.Recognition.RuTypeJ31c
public import CFSG.Quasithin.Recognition.RuTypeJ36f
public import CFSG.Quasithin.Recognition.RuTypeJ31b

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.ChIJK

open CFSG.Open

@[expose] def IsPOnePlusTwoGroup (p : ℕ) (X : Type) [Group X] : Prop :=
  Nat.card X = p ^ 3 ∧ Monoid.exponent X = p ∧ ∃ a b : X, a * b ≠ b * a

end CFSG.ASVolI.ChIJK

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChIJK

@[expose] def J_3_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    Nat.card G = 2 ^ 14 * 3 ^ 3 * 5 ^ 3 * 7 * 13 * 29

section BurnsideJ5

private theorem burnsideJ5_mem_conjClass_iff {G : Type} [Group G] (z x : G) :
    x ∈ CFSG.ASVolI.ChIJK.conjClass z ↔ IsConj z x := by
  rw [isConj_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g⁻¹, by group⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c⁻¹, by group⟩

private theorem burnsideJ5_eq_z {G : Type} [Group G] [Finite G]
    (M : CFSG.Quasithin.RuType.RuDataM G) {z : G}
    (hz : Subgroup.zpowers z = CFSG.Quasithin.RuType.ruZ M.T) : z = M.z := by
  have hzmem : z ∈ CFSG.Quasithin.RuType.ruZ M.T := by
    rw [← hz]
    exact Subgroup.mem_zpowers z
  rcases M.mem_Z_iff.mp hzmem with h1 | h1
  · exfalso
    have h2 := M.toRuData.card_Z
    rw [← hz, h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at h2
    omega
  · exact h1

private theorem burnsideJ5_comm_conj_iff {G : Type} [Group G] (l a b : G) :
    (l⁻¹ * a * l) * (l⁻¹ * b * l) = (l⁻¹ * b * l) * (l⁻¹ * a * l) ↔ a * b = b * a := by
  constructor
  · intro h
    have h' : l⁻¹ * (a * b) * l = l⁻¹ * (b * a) * l := by
      calc l⁻¹ * (a * b) * l = (l⁻¹ * a * l) * (l⁻¹ * b * l) := by group
        _ = (l⁻¹ * b * l) * (l⁻¹ * a * l) := h
        _ = l⁻¹ * (b * a) * l := by group
    exact mul_left_cancel (mul_right_cancel h')
  · intro h
    calc (l⁻¹ * a * l) * (l⁻¹ * b * l) = l⁻¹ * (a * b) * l := by group
      _ = l⁻¹ * (b * a) * l := by rw [h]
      _ = (l⁻¹ * b * l) * (l⁻¹ * a * l) := by group

private theorem burnsideJ5_isConj_conj_iff {G : Type} [Group G] (z u l : G) :
    IsConj z (l⁻¹ * u * l) ↔ IsConj z u :=
  ⟨fun h => h.trans (isConj_iff.mpr ⟨l, by group⟩),
    fun h => h.trans (isConj_iff.mpr ⟨l⁻¹, by group⟩)⟩

private theorem burnsideJ5_conj_sq_eq_one_iff {G : Type} [Group G] (l u : G) :
    (l⁻¹ * u * l) ^ 2 = 1 ↔ u ^ 2 = 1 := by
  have h : (l⁻¹ * u * l) ^ 2 = l⁻¹ * u ^ 2 * l := by
    rw [pow_two, pow_two]
    group
  rw [h]
  constructor
  · intro h1
    calc u ^ 2 = l * (l⁻¹ * u ^ 2 * l) * l⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · intro h1
    rw [h1]
    group

private theorem burnsideJ5_conj_eq_one_iff {G : Type} [Group G] (l u : G) :
    l⁻¹ * u * l = 1 ↔ u = 1 := by
  constructor
  · intro h1
    calc u = l * (l⁻¹ * u * l) * l⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · intro h1
    rw [h1]
    group

private theorem burnsideJ5_pResidualOf_two_eq {G : Type} [Group G] [Finite G] (X : Subgroup G) :
    CFSG.GorensteinWalter.pResidualOf X 2 = CFSG.Quasithin.oTwoUpper X := by
  apply le_antisymm
  · have hN : ((CFSG.Quasithin.oTwoUpper X).subgroupOf X).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (CFSG.Quasithin.le_normalizer_oTwoUpper X)
    have hQ : IsPGroup 2 (X ⧸ (CFSG.Quasithin.oTwoUpper X).subgroupOf X) := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨k, hk⟩ := CFSG.Quasithin.exists_pow_mem_oTwoUpper X x.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hk
    exact CFSG.GorensteinWalter.pResidualOf_le_of_quotient_isPGroup X _ 2 Nat.prime_two
      (CFSG.Quasithin.oTwoUpper_le X) hN hQ
  · refine (Subgroup.closure_le _).mpr fun x hx => ?_
    exact CFSG.GorensteinWalter.mem_pResidualOf_of_order_coprime X 2 Nat.prime_two hx.1
      (Nat.coprime_two_left.mpr hx.2)

private theorem burnsideJ5_centralizer_map_conj {G : Type} [Group G] (l s : G) :
    (Subgroup.centralizer ({s} : Set G)).map (MulAut.conj l⁻¹).toMonoidHom =
      Subgroup.centralizer ({l⁻¹ * s * l} : Set G) := by
  ext x
  rw [Subgroup.mem_map_equiv]
  simp only [MulAut.conj_symm_apply, Subgroup.mem_centralizer_singleton_iff, inv_inv]
  have h := burnsideJ5_comm_conj_iff l (l * x * l⁻¹) s
  have e : l⁻¹ * (l * x * l⁻¹) * l = x := by group
  rw [e] at h
  exact h.symm

private theorem burnsideJ5_mem_Ls_iff {G : Type} [Group G] [Finite G] (l s u : G) :
    u ∈ CFSG.Quasithin.RuType.Ls s ↔ l⁻¹ * u * l ∈ CFSG.Quasithin.RuType.Ls (l⁻¹ * s * l) := by
  show u ∈ CFSG.GorensteinWalter.pResidualOf (Subgroup.centralizer ({s} : Set G)) 2 ↔
    l⁻¹ * u * l ∈ CFSG.GorensteinWalter.pResidualOf (Subgroup.centralizer ({l⁻¹ * s * l} : Set G)) 2
  rw [← burnsideJ5_centralizer_map_conj l s, burnsideJ5_pResidualOf_two_eq,
    burnsideJ5_pResidualOf_two_eq, CFSG.Quasithin.oTwoUpper_map]
  have h := (Subgroup.mem_map_iff_mem (f := (MulAut.conj l⁻¹).toMonoidHom)
    (MulAut.conj l⁻¹).injective (K := CFSG.Quasithin.oTwoUpper (Subgroup.centralizer ({s} : Set G)))
    (x := u)).symm
  simpa [MulAut.conj_apply] using h

private theorem burnsideJ5_exists_conj_of_card_seven {G : Type} [Group G] [Finite G] {L A B :
    Subgroup G}
    (hL : Nat.card L = 2 ^ 11 * 168) (hA : A ≤ L) (hB : B ≤ L)
    (hAc : Nat.card A = 7) (hBc : Nat.card B = 7) :
    ∃ l ∈ L, ∀ x : G, x ∈ A ↔ l⁻¹ * x * l ∈ B := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hsyl : ∀ C : Subgroup G, C ≤ L → Nat.card C = 7 →
      ∃ P : Sylow 7 L, (P : Subgroup L) = C.subgroupOf L := by
    intro C hC hCc
    have hcard : Nat.card (C.subgroupOf L) = 7 := by
      rw [CFSG.Quasithin.RuType.card_subgroupOf_of_le hC, hCc]
    have hp : IsPGroup 7 (C.subgroupOf L) := IsPGroup.of_card (n := 1) (by rw [hcard]; norm_num)
    refine ⟨IsPGroup.toSylow hp ?_, rfl⟩
    have h := Subgroup.index_mul_card (C.subgroupOf L)
    rw [hcard, hL] at h
    omega
  obtain ⟨PA, hPA⟩ := hsyl A hA hAc
  obtain ⟨PB, hPB⟩ := hsyl B hB hBc
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L PB PA
  have key : ∀ x' : L, (x' : G) ∈ A ↔ (g : G)⁻¹ * (x' : G) * (g : G) ∈ B := by
    intro x'
    have h1 : (x' : G) ∈ A ↔ x' ∈ (PA : Subgroup L) := by
      rw [hPA]
      exact Iff.rfl
    have h2 : x' ∈ (PA : Subgroup L) ↔ g⁻¹ * x' * g ∈ (PB : Subgroup L) := by
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simp [MulAut.smul_def, MulAut.inv_def, MulAut.conj_symm_apply]
    have h3 : g⁻¹ * x' * g ∈ (PB : Subgroup L) ↔ (g : G)⁻¹ * (x' : G) * (g : G) ∈ B := by
      rw [hPB]
      exact Iff.rfl
    exact h1.trans (h2.trans h3)
  refine ⟨(g : G), g.2, fun x => ?_⟩
  by_cases hxL : x ∈ L
  · exact key ⟨x, hxL⟩
  · refine ⟨fun hx => absurd (hA hx) hxL, fun hx => absurd ?_ hxL⟩
    have h1 : (g : G)⁻¹ * x * g ∈ L := hB hx
    have h2 : (g : G) * ((g : G)⁻¹ * x * g) * (g : G)⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem g.2 h1) (L.inv_mem g.2)
    have e : (g : G) * ((g : G)⁻¹ * x * g) * (g : G)⁻¹ = x := by group
    rwa [e] at h2

end BurnsideJ5

section

private theorem burnsideJ5_J_3_1_of_st (hSt : CFSG.Quasithin.RuType.StUniqueStatement) : J_3_1 := by
  intro G _ _ L V T h
  obtain ⟨M, -, -⟩ := CFSG.ASVolI.ChIJK.RuType.exists_ruDataM hSt h
  exact M.card_eq

theorem as_J_3_1 : J_3_1 :=
  burnsideJ5_J_3_1_of_st CFSG.Quasithin.RuType.stUnique

end

@[expose] def J_3_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    ∀ z : G, Subgroup.zpowers z = ZRu T →
      ∀ u ∈ conjClass z, ∀ v ∈ conjClass z, u * v = v * u → u * v ≠ 1 → u * v ∈ conjClass z

section

private theorem burnsideJ5_J_3_2_of_st (hSt : CFSG.Quasithin.RuType.StUniqueStatement) : J_3_2 := by
  intro G _ _ L V T h z hz u hu v hv huv h1
  obtain ⟨M, -, hMT⟩ := CFSG.ASVolI.ChIJK.RuType.exists_ruDataM hSt h
  have hzM : z = M.z := by
    refine burnsideJ5_eq_z M ?_
    rw [hMT, ← CFSG.ASVolI.ChIJK.RuType.ZRu_eq_ruZ h]
    exact hz
  subst hzM
  obtain ⟨s, hs, hs1⟩ := M.exists_S0_ne_one
  rw [burnsideJ5_mem_conjClass_iff] at hu hv ⊢
  exact M.lemma_J32 hs hs1 hu hv huv h1

theorem as_J_3_2 : J_3_2 :=
  burnsideJ5_J_3_2_of_st CFSG.Quasithin.RuType.stUnique

end

@[expose] def J_3_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    ∀ B7 : Subgroup G, B7 ≤ L → Nat.card ↥B7 = 7 →
    ∀ z s : G, Subgroup.zpowers z = ZRu T → s ∈ S0Ru L B7 → s ≠ 1 →
      (conjClass z ∩ (Subgroup.centralizer ({s} : Set G) : Set G)).ncard =
          (involutionsOf (LsRu s)).ncard ∧
        (involutionsOf (LsRu s)).ncard = 5 * 7 * 13 ∧ 5 * 7 * 13 = 455

section

private theorem burnsideJ5_J_3_3_of_st (hSt : CFSG.Quasithin.RuType.StUniqueStatement) : J_3_3 := by
  intro G _ _ L V T h B7 hB7L hB7c z s hz hs hs1
  obtain ⟨M, hML, hMT⟩ := CFSG.ASVolI.ChIJK.RuType.exists_ruDataM hSt h
  subst hML
  have hzM : z = M.z := by
    refine burnsideJ5_eq_z M ?_
    rw [hMT, ← CFSG.ASVolI.ChIJK.RuType.ZRu_eq_ruZ h]
    exact hz
  subst hzM
  obtain ⟨l, hlL, hl⟩ := burnsideJ5_exists_conj_of_card_seven M.toRuData.card_L hB7L
    (Subgroup.zpowers_le.mpr M.cel.2) hB7c M.card_B7
  have hsS : s ∈ CFSG.Quasithin.RuType.ruS M.L := (Subgroup.mem_inf.mp hs).1
  have hsC : s ∈ Subgroup.centralizer (B7 : Set G) := (Subgroup.mem_inf.mp hs).2
  have hs₀S : l⁻¹ * s * l ∈ CFSG.Quasithin.RuType.ruS M.L := by
    have := (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M.L (M.L.inv_mem hlL)) s).mp hsS
    simpa using this
  have hs₀C : (M.cel : G) * (l⁻¹ * s * l) = (l⁻¹ * s * l) * M.cel := by
    have hmem : l * (M.cel : G) * l⁻¹ ∈ B7 := by
      rw [hl]
      have e : l⁻¹ * (l * (M.cel : G) * l⁻¹) * l = M.cel := by group
      rw [e]
      exact Subgroup.mem_zpowers _
    have hc := Subgroup.mem_centralizer_iff.mp hsC _ hmem
    calc (M.cel : G) * (l⁻¹ * s * l) = l⁻¹ * ((l * M.cel * l⁻¹) * s) * l := by group
      _ = l⁻¹ * (s * (l * M.cel * l⁻¹)) * l := by rw [hc]
      _ = (l⁻¹ * s * l) * M.cel := by group
  have hs₀ : l⁻¹ * s * l ∈ M.S0 := M.mem_S0.mpr ⟨hs₀S, hs₀C⟩
  have hs₀1 : l⁻¹ * s * l ≠ 1 := fun h1 => hs1 ((burnsideJ5_conj_eq_one_iff l s).mp h1)
  obtain ⟨c1, c2⟩ := M.lemma_J33 hs₀ hs₀1
  let e : G ≃ G := ⟨fun u => l⁻¹ * u * l, fun u => l * u * l⁻¹, fun u => by group,
    fun u => by group⟩
  have e1 : (CFSG.ASVolI.ChIJK.conjClass M.z ∩
      (Subgroup.centralizer ({s} : Set G) : Set G)).ncard = 455 := by
    rw [← Nat.card_coe_set_eq]
    refine (Nat.card_congr (Equiv.subtypeEquiv e fun u => ?_)).trans c1
    show (u ∈ CFSG.ASVolI.ChIJK.conjClass M.z ∧ u ∈ (Subgroup.centralizer ({s} : Set G) : Set G)) ↔
      IsConj M.z (l⁻¹ * u * l) ∧
        (l⁻¹ * u * l) * (l⁻¹ * s * l) = (l⁻¹ * s * l) * (l⁻¹ * u * l)
    rw [burnsideJ5_mem_conjClass_iff, burnsideJ5_isConj_conj_iff, burnsideJ5_comm_conj_iff,
      SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  have e2 : (CFSG.ASVolI.ChIJK.involutionsOf (CFSG.ASVolI.ChIJK.LsRu s)).ncard = 455 := by
    rw [← Nat.card_coe_set_eq]
    refine (Nat.card_congr (Equiv.subtypeEquiv e fun u => ?_)).trans c2
    show (u ∈ CFSG.ASVolI.ChIJK.LsRu s ∧ u ^ 2 = 1 ∧ u ≠ 1) ↔
      (l⁻¹ * u * l ∈ CFSG.Quasithin.RuType.Ls (l⁻¹ * s * l) ∧ (l⁻¹ * u * l) ^ 2 = 1 ∧
        l⁻¹ * u * l ≠ 1)
    rw [burnsideJ5_conj_sq_eq_one_iff, ne_eq, ne_eq, burnsideJ5_conj_eq_one_iff]
    exact and_congr_left' (burnsideJ5_mem_Ls_iff l s u)
  exact ⟨e1.trans e2.symm, by rw [e2], by norm_num⟩

theorem as_J_3_3 : J_3_3 :=
  burnsideJ5_J_3_3_of_st CFSG.Quasithin.RuType.stUnique

end

@[expose] def J_3_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    ∀ z : G, Subgroup.zpowers z = ZRu T →
      (conjClass z ∩ (HRu T : Set G)).ncard = 1391

section BurnsideJ34

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_nilp_conj : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A.trace = 0 → A * A = 0 →
    A ≠ 0 → ∃ g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), SL3.IsRow0 (stAct g A) := by
  decide +kernel

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_cubic_conj : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A * A * A + A + 1 = 0 →
    ∃ g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), stAct g A ∈ SL3.fixC0List := by
  decide +kernel

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_card_E :
    Fintype.card {A : Matrix (Fin 3) (Fin 3) (ZMod 2) //
      A.trace = 0 ∧ (A * A = 0 ∨ A * A * A + A + 1 = 0)} = 46 := by
  decide +kernel

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_stAct_eq_iff (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    stAct g A = A ↔
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * A = A * (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  have h1 : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
      ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]
    rfl
  have h2 : ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)) * (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]
    rfl
  unfold stAct
  constructor
  · intro h
    calc (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * A
        = ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * A *
            ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
              Matrix (Fin 3) (Fin 3) (ZMod 2))) * (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
          rw [Matrix.mul_assoc _ _ (g : Matrix (Fin 3) (Fin 3) (ZMod 2)), h2, Matrix.mul_one]
      _ = A * (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by rw [h]
  · intro h
    calc (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * A *
          ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))
        = A * (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
          ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
            Matrix (Fin 3) (Fin 3) (ZMod 2)) := by rw [h]
      _ = A := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_stab_le_comm :
    ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A.trace = 0 → ¬ (A * A = 0 ∨ A * A * A + A + 1 = 0) →
      Fintype.card {g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) //
        (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * A = A * (g : Matrix (Fin 3) (Fin 3) (ZMod 2))} ≤
          6 := by
  decide +kernel

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_stab_le :
    ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A.trace = 0 → ¬ (A * A = 0 ∨ A * A * A + A + 1 = 0) →
      Fintype.card {g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) // stAct g A = A} ≤ 6 := by
  intro A h1 h2
  rw [Fintype.card_congr (Equiv.subtypeEquivRight fun g => burnsideJ28_stAct_eq_iff g A)]
  exact burnsideJ28_stab_le_comm A h1 h2

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_dec_R0 : ∀ r : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), r ∈ SL3.R0 → r ≠ 1 →
    Fintype.card {A : Matrix (Fin 3) (Fin 3) (ZMod 2) // A.trace = 0 ∧ stAct r A = A} = 16 ∧
    (∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A.trace = 0 → stAct r A = A →
      ∃ B : Matrix (Fin 3) (Fin 3) (ZMod 2), B.trace = 0 ∧ stAct r B + B = A) ∧
    Fintype.card {u : Fin 3 → ZMod 2 // natAct3 r u = u} = 4 := by
  decide +kernel



open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_U0_sq : ∀ u : SigmaL2F4, u ∈ Sigma.U0 → u ^ 2 = 1 := by
  decide +kernel

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_sl_inv_conj : ∀ A A' : SigmaL2F4, A ^ 2 = 1 → A.right = 1 → A ≠ 1 →
    A' ^ 2 = 1 → A'.right = 1 → A' ≠ 1 → ∃ g : SigmaL2F4, g * A * g⁻¹ = A' := by
  decide +kernel


section BurnsideJ28Cnt

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_sq_mul_V {G : Type} [Group G] [Finite G] (M : RuDataM G) {s v : G}
    (hs : s ∈ ruS M.L) (hv : v ∈ ruV M.L) : (s * v) ^ 2 = s ^ 2 := by
  have hc : s * v = v * s := M.V_comm_S hv hs
  have hv2 : v * v = 1 := by rw [← pow_two]; exact M.sq_eq_one_of_V hv
  calc (s * v) ^ 2 = s * (v * s) * v := by rw [pow_two]; group
    _ = s * (s * v) * v := by rw [← hc]
    _ = s * s * (v * v) := by group
    _ = s ^ 2 := by rw [hv2, mul_one, pow_two]

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_zq_conj {G : Type} [Group G] [Finite G] (M : RuDataM G)
    {A : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (hA : ∃ s : ruS M.L, M.χ s = Multiplicative.ofAdd A ∧ (s : G) ^ 2 = 1)
    (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    ∃ s : ruS M.L, M.χ s = Multiplicative.ofAdd (stAct g A) ∧ (s : G) ^ 2 = 1 := by
  obtain ⟨s, hs, hs2⟩ := hA
  obtain ⟨l, rfl⟩ := M.θ_surj g
  have hmem : (l : G) * s * (l : G)⁻¹ ∈ ruS M.L :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L l.2) s).mp s.2
  refine ⟨⟨_, hmem⟩, ?_, ?_⟩
  · rw [M.χ_equiv l s ⟨_, hmem⟩ rfl, hs, toAdd_ofAdd]
  · show ((l : G) * s * (l : G)⁻¹) ^ 2 = 1
    rw [conj_pow, hs2]
    group

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_card_inv_S {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    Nat.card {s : ruS M.L // (s : G) ^ 2 = 1} =
      8 * Nat.card {A : Matrix (Fin 3) (Fin 3) (ZMod 2) //
        A.trace = 0 ∧ ∃ s : ruS M.L, M.χ s = Multiplicative.ofAdd A ∧ (s : G) ^ 2 = 1} := by
  classical
  let P := {s : ruS M.L // (s : G) ^ 2 = 1}
  let f : P → Matrix (Fin 3) (Fin 3) (ZMod 2) := fun s => Multiplicative.toAdd (M.χ s.1)
  have hsum : Nat.card P = ∑ B : Matrix (Fin 3) (Fin 3) (ZMod 2), Nat.card {s : P // f s = B} := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
  have hχB : ∀ (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) (s : {s : P // f s = B}),
      M.χ s.1.1 = Multiplicative.ofAdd B := fun B s =>
    calc M.χ s.1.1 = Multiplicative.ofAdd (Multiplicative.toAdd (M.χ s.1.1)) :=
          (ofAdd_toAdd _).symm
      _ = Multiplicative.ofAdd B := congrArg _ s.2
  have hfib : ∀ B : Matrix (Fin 3) (Fin 3) (ZMod 2), Nat.card {s : P // f s = B} =
      if (B.trace = 0 ∧ ∃ s : ruS M.L, M.χ s = Multiplicative.ofAdd B ∧ (s : G) ^ 2 = 1)
        then 8 else 0 := by
    intro B
    by_cases hB : B.trace = 0 ∧ ∃ s : ruS M.L, M.χ s = Multiplicative.ofAdd B ∧ (s : G) ^ 2 = 1
    · rw [if_pos hB]
      obtain ⟨-, s0, hs0, hs02⟩ := hB
      rw [← M.toRuData.card_V]
      have hmemV : ∀ s : {s : P // f s = B}, (s0 : G)⁻¹ * (s.1.1 : G) ∈ ruV M.L := by
        intro s
        have hk : s0⁻¹ * s.1.1 ∈ M.χ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hχB B s, hs0]
          exact inv_mul_cancel _
        rw [M.χ_ker, Subgroup.mem_subgroupOf] at hk
        exact hk
      have hχV : ∀ v : ruV M.L, M.χ ⟨(v : G), M.toRuData.V_le_S v.2⟩ = 1 := by
        intro v
        have : (⟨(v : G), M.toRuData.V_le_S v.2⟩ : ruS M.L) ∈ M.χ.ker := by
          rw [M.χ_ker, Subgroup.mem_subgroupOf]
          exact v.2
        exact this
      refine Nat.card_congr
        { toFun := fun s => ⟨(s0 : G)⁻¹ * (s.1.1 : G), hmemV s⟩
          invFun := fun v => ⟨⟨s0 * ⟨v.1, M.toRuData.V_le_S v.2⟩, by
              show ((s0 : G) * (v : G)) ^ 2 = 1
              rw [burnsideJ28_sq_mul_V M s0.2 v.2, hs02]⟩, by
              show Multiplicative.toAdd (M.χ (s0 * ⟨v.1, M.toRuData.V_le_S v.2⟩)) = B
              rw [map_mul, hχV v, mul_one, hs0, toAdd_ofAdd]⟩
          left_inv := fun s => ?_
          right_inv := fun v => ?_ }
      · apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        show (s0 : G) * ((s0 : G)⁻¹ * (s.1.1 : G)) = (s.1.1 : G)
        group
      · apply Subtype.ext
        show (s0 : G)⁻¹ * ((s0 : G) * (v : G)) = (v : G)
        group
    · rw [if_neg hB]
      have : IsEmpty {s : P // f s = B} := ⟨fun s => hB ⟨by
        have h := M.χ_trace s.1.1
        rwa [show Multiplicative.toAdd (M.χ s.1.1) = B from s.2] at h, s.1.1, hχB B s, s.1.2⟩⟩
      exact Nat.card_of_isEmpty
  rw [hsum]
  simp_rw [hfib]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_comm]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_stAct_mul (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (A B : Matrix (Fin 3) (Fin 3) (ZMod 2)) : stAct g (A * B) = stAct g A * stAct g B := by
  have h : ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  unfold stAct
  calc (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (A * B) *
        ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))
      = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * A * (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) * B *
        ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
        rw [Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * A *
          (((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            (g : Matrix (Fin 3) (Fin 3) (ZMod 2))) * B *
        ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
        rw [h]
    _ = _ := by simp only [Matrix.mul_assoc]

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_stAct_one (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    stAct g (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by
  unfold stAct
  rw [Matrix.mul_one, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one]

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_stAct_zero (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    stAct g (0 : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 0 := by
  unfold stAct
  simp

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_E_conj (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hA : A * A = 0 ∨ A * A * A + A + 1 = 0) :
    stAct g A * stAct g A = 0 ∨ stAct g A * stAct g A * stAct g A + stAct g A + 1 = 0 := by
  rcases hA with h | h
  · left
    rw [← burnsideJ28_stAct_mul, h, burnsideJ28_stAct_zero]
  · right
    have := congrArg (stAct g) h
    rw [SL3.stAct_add, SL3.stAct_add, burnsideJ28_stAct_mul, burnsideJ28_stAct_mul,
      burnsideJ28_stAct_one, burnsideJ28_stAct_zero] at this
    exact this

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_row0_inv {G : Type} [Group G] [Finite G] (M : RuDataM G)
    {B : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hB : IsTraceZero B) (hr : SL3.IsRow0 B) :
    ∃ s : ruS M.L, M.χ s = Multiplicative.ofAdd B ∧ (s : G) ^ 2 = 1 := by
  have hmem : ((M.sOf B : ruS M.L) : G) ∈ ruU M.L M.T := by
    refine (M.mem_U_iff (M.sOf B).2).mpr ?_
    have : M.χ ⟨((M.sOf B : ruS M.L) : G), (M.sOf B).2⟩ = Multiplicative.ofAdd B :=
      M.χ_sOf hB
    rw [this, toAdd_ofAdd]
    exact hr
  exact ⟨M.sOf B, M.χ_sOf hB, M.U_sq hmem⟩

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_fixC0_inv {G : Type} [Group G] [Finite G] (M : RuDataM G)
    {B : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hB : B ∈ SL3.fixC0List) :
    ∃ s : ruS M.L, M.χ s = Multiplicative.ofAdd B ∧ (s : G) ^ 2 = 1 := by
  obtain ⟨x, hx, hxχ⟩ := M.exists_S0_χ hB
  exact ⟨⟨x, (M.mem_S0.mp hx).1⟩, by rw [← hxχ, ofAdd_toAdd], M.S0_elem.2 x hx⟩

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_E_sub_Z {G : Type} [Group G] [Finite G] (M : RuDataM G)
    {A : Matrix (Fin 3) (Fin 3) (ZMod 2)} (htr : A.trace = 0)
    (hA : A * A = 0 ∨ A * A * A + A + 1 = 0) :
    ∃ s : ruS M.L, M.χ s = Multiplicative.ofAdd A ∧ (s : G) ^ 2 = 1 := by
  rcases hA with h0 | h3
  · by_cases hA0 : A = 0
    · subst hA0
      exact ⟨1, by simp, by simp⟩
    · obtain ⟨g, hg⟩ := burnsideJ28_nilp_conj A htr h0 hA0
      have hB : IsTraceZero (stAct g A) := by
        unfold IsTraceZero
        rw [SL3.trace_stAct]
        exact htr
      have := burnsideJ28_zq_conj M (burnsideJ28_row0_inv M hB hg) g⁻¹
      rwa [← SL3.stAct_mul, inv_mul_cancel, SL3.stAct_one] at this
  · obtain ⟨g, hg⟩ := burnsideJ28_cubic_conj A h3
    have := burnsideJ28_zq_conj M (burnsideJ28_fixC0_inv M hg) g⁻¹
    rwa [← SL3.stAct_mul, inv_mul_cancel, SL3.stAct_one] at this

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_Z_eq (Z : Set (Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (hE : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A.trace = 0 →
      (A * A = 0 ∨ A * A * A + A + 1 = 0) → A ∈ Z)
    (hZtr : ∀ A ∈ Z, A.trace = 0)
    (hconj : ∀ (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (A : Matrix (Fin 3) (Fin 3) (ZMod 2)),
      A ∈ Z → stAct g A ∈ Z)
    (hcard : Nat.card Z ≤ 58) :
    ∀ A ∈ Z, A * A = 0 ∨ A * A * A + A + 1 = 0 := by
  classical
  intro A hA
  by_contra hnot
  let Es : Set (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
    {B | B.trace = 0 ∧ (B * B = 0 ∨ B * B * B + B + 1 = 0)}
  let D : Set (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
    {B | B ∈ Z ∧ ¬ (B * B = 0 ∨ B * B * B + B + 1 = 0)}
  have hEs : Nat.card Es = 46 := by
    have := burnsideJ28_card_E
    rw [← Nat.card_eq_fintype_card] at this
    exact this
  have hEsZ : Es ⊆ Z := fun B hB => hE B hB.1 hB.2
  have hDZ : D ⊆ Z := fun B hB => hB.1
  have hdisj : Disjoint Es D := Set.disjoint_left.mpr fun B hB hD => hD.2 hB.2
  have hsum : Nat.card Es + Nat.card D ≤ Nat.card Z := by
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
      ← Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
    exact Set.ncard_le_ncard (Set.union_subset hEsZ hDZ) (Set.toFinite _)
  have hAD : A ∈ D := ⟨hA, hnot⟩
  have hf : ∀ g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), stAct g A ∈ D := by
    intro g
    refine ⟨hconj g A hA, fun h => hnot ?_⟩
    have := burnsideJ28_E_conj g⁻¹ _ h
    rwa [← SL3.stAct_mul, inv_mul_cancel, SL3.stAct_one] at this
  let f : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) → D := fun g => ⟨stAct g A, hf g⟩
  have hfib : ∀ B : D, Nat.card {g // f g = B} ≤ 6 := by
    intro B
    by_cases hne : Nonempty {g // f g = B}
    · obtain ⟨⟨g0, hg0⟩⟩ := hne
      have hB : stAct g0 A = (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) := congrArg Subtype.val hg0
      have hstab : Fintype.card {h : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) // stAct h A = A}
          ≤ 6 := burnsideJ28_stab_le A (hZtr A hA) hnot
      calc Nat.card {g // f g = B}
          ≤ Nat.card {h : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) // stAct h A = A} := by
            refine Nat.card_le_card_of_injective (fun g => ⟨g0⁻¹ * g.1, ?_⟩) ?_
            · have h1 : stAct g.1 A = (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
                congrArg Subtype.val g.2
              rw [SL3.stAct_mul, h1, ← hB, ← SL3.stAct_mul, inv_mul_cancel, SL3.stAct_one]
            · intro a b hab
              have h1 : g0⁻¹ * a.1 = g0⁻¹ * b.1 := congrArg Subtype.val hab
              exact Subtype.ext (mul_left_cancel h1)
        _ = Fintype.card {h : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) // stAct h A = A} :=
            Nat.card_eq_fintype_card
        _ ≤ 6 := hstab
    · rw [not_nonempty_iff] at hne
      rw [Nat.card_of_isEmpty]
      omega
  have hD := card_le_mul_of_fiber f 6 hfib
  rw [SL3.card_SL3] at hD
  omega

private theorem burnsideJ28_inv_iff {G : Type} [Group G] {x0 s : G} (hx : x0 ^ 2 = 1) :
    (x0 * s) ^ 2 = 1 ↔ x0 * s * x0⁻¹ = s⁻¹ := by
  have hxx : x0 * x0 = 1 := by rw [← pow_two]; exact hx
  have hinv : x0⁻¹ = x0 := inv_eq_of_mul_eq_one_right hxx
  rw [hinv, pow_two]
  constructor
  · intro h
    have : x0 * s * x0 * s = 1 := by simpa [mul_assoc] using h
    exact eq_inv_of_mul_eq_one_left this
  · intro h
    calc x0 * s * (x0 * s) = (x0 * s * x0) * s := by group
      _ = s⁻¹ * s := by rw [h]
      _ = 1 := inv_mul_cancel s

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_inv_mul_V {G : Type} [Group G] [Finite G] (M : RuDataM G) {x0 s v : G}
    (hx : x0 ^ 2 = 1) (hs : s ∈ ruS M.L) (hv : v ∈ ruV M.L) (hxs : (x0 * s) ^ 2 = 1) :
    (x0 * (s * v)) ^ 2 = 1 ↔ x0 * v * x0⁻¹ = v := by
  have h1 : x0 * s * x0⁻¹ = s⁻¹ := (burnsideJ28_inv_iff hx).mp hxs
  have hc : s * v = v * s := M.V_comm_S hv hs
  have hv2 : v * v = 1 := by rw [← pow_two]; exact M.sq_eq_one_of_V hv
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  rw [burnsideJ28_inv_iff hx]
  constructor
  · intro h
    have h2 : x0 * (s * v) * x0⁻¹ = (x0 * s * x0⁻¹) * (x0 * v * x0⁻¹) := by group
    rw [h2, h1, mul_inv_rev, hvinv] at h
    have hcs : s⁻¹ * v = v * s⁻¹ := by
      have := congrArg (fun y => s⁻¹ * y * s⁻¹) hc
      simpa [mul_assoc] using this.symm
    calc x0 * v * x0⁻¹ = s * (s⁻¹ * (x0 * v * x0⁻¹)) := by group
      _ = s * (v * s⁻¹) := by rw [h]
      _ = s * (s⁻¹ * v) := by rw [hcs]
      _ = v := by group
  · intro h
    have h2 : x0 * (s * v) * x0⁻¹ = (x0 * s * x0⁻¹) * (x0 * v * x0⁻¹) := by group
    rw [h2, h1, h, mul_inv_rev, hvinv]
    have hcs : s⁻¹ * v = v * s⁻¹ := by
      have := congrArg (fun y => s⁻¹ * y * s⁻¹) hc
      simpa [mul_assoc] using this.symm
    exact hcs

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_card_CV {G : Type} [Group G] [Finite G] (M : RuDataM G) (x0L : M.L)
    (h4 : Fintype.card {u : Fin 3 → ZMod 2 // natAct3 (M.θ x0L) u = u} = 4) :
    Nat.card {v : ruV M.L // (x0L : G) * v * (x0L : G)⁻¹ = v} = 4 := by
  rw [← h4, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := fun v => ⟨Multiplicative.toAdd (M.ψV v.1), (M.toRuData.conj_eq_iff x0L v.1).mp v.2⟩
      invFun := fun u => ⟨M.ψV.symm (Multiplicative.ofAdd u.1), (M.toRuData.conj_eq_iff x0L _).mpr (by
          simpa using u.2)⟩
      left_inv := fun v => by simp
      right_inv := fun u => by simp }

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_card_coset_inv {G : Type} [Group G] [Finite G] (M : RuDataM G) {x0 : G}
    (hx0L : x0 ∈ M.L) (hx02 : x0 ^ 2 = 1) (hr0 : M.θ ⟨x0, hx0L⟩ ∈ SL3.R0)
    (hr1 : M.θ ⟨x0, hx0L⟩ ≠ 1) :
    Nat.card {x : G // ∃ hx : x ∈ M.L, M.θ ⟨x, hx⟩ = M.θ ⟨x0, hx0L⟩ ∧ x ^ 2 = 1} = 64 := by
  classical
  obtain ⟨D1, D2, D3⟩ := burnsideJ28_dec_R0 _ hr0 hr1
  have hxx : x0 * x0 = 1 := by rw [← pow_two]; exact hx02
  have hinv : x0⁻¹ = x0 := inv_eq_of_mul_eq_one_right hxx
  let x0L : M.L := ⟨x0, hx0L⟩
  let P := {s : ruS M.L // (x0 * (s : G)) ^ 2 = 1}
  have hθS : ∀ s : ruS M.L, M.θ ⟨(s : G), M.toRuData.S_le_L s.2⟩ = 1 := by
    intro s
    have : (⟨(s : G), M.toRuData.S_le_L s.2⟩ : M.L) ∈ M.θ.ker := by
      rw [M.θ_ker, Subgroup.mem_subgroupOf]
      exact s.2
    exact this
  have e1 : Nat.card {x : G // ∃ hx : x ∈ M.L, M.θ ⟨x, hx⟩ = M.θ x0L ∧ x ^ 2 = 1} =
      Nat.card P := by
    have hfwd : ∀ x : {x : G // ∃ hx : x ∈ M.L, M.θ ⟨x, hx⟩ = M.θ x0L ∧ x ^ 2 = 1},
        x0⁻¹ * x.1 ∈ ruS M.L := by
      intro x
      obtain ⟨hx, hθ, -⟩ := x.2
      have hkL : x0⁻¹ * x.1 ∈ M.L := mul_mem (inv_mem hx0L) hx
      have hk : (⟨x0⁻¹ * x.1, hkL⟩ : M.L) ∈ M.θ.ker := by
        rw [MonoidHom.mem_ker]
        have e : (⟨x0⁻¹ * x.1, hkL⟩ : M.L) = x0L⁻¹ * ⟨x.1, hx⟩ := rfl
        rw [e, map_mul, map_inv, hθ]
        exact inv_mul_cancel _
      rw [M.θ_ker, Subgroup.mem_subgroupOf] at hk
      exact hk
    refine Nat.card_congr
      { toFun := fun x => ⟨⟨x0⁻¹ * x.1, hfwd x⟩, by
          obtain ⟨-, -, hx2⟩ := x.2
          show (x0 * (x0⁻¹ * x.1)) ^ 2 = 1
          rw [mul_inv_cancel_left]
          exact hx2⟩
        invFun := fun s => ⟨x0 * (s.1 : G), ⟨mul_mem hx0L (M.toRuData.S_le_L s.1.2), by
          have e : (⟨x0 * (s.1 : G), mul_mem hx0L (M.toRuData.S_le_L s.1.2)⟩ : M.L) =
              x0L * ⟨(s.1 : G), M.toRuData.S_le_L s.1.2⟩ := rfl
          rw [e, map_mul, hθS s.1, mul_one], s.2⟩⟩
        left_inv := fun x => Subtype.ext (by
          show x0 * (x0⁻¹ * x.1) = x.1
          group)
        right_inv := fun s => Subtype.ext (Subtype.ext (by
          show x0⁻¹ * (x0 * (s.1 : G)) = (s.1 : G)
          group)) }
  rw [e1]
  let f : P → Matrix (Fin 3) (Fin 3) (ZMod 2) := fun s => Multiplicative.toAdd (M.χ s.1)
  have hsum : Nat.card P = ∑ A : Matrix (Fin 3) (Fin 3) (ZMod 2), Nat.card {s : P // f s = A} := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
  have hχA : ∀ (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (s : {s : P // f s = A}),
      M.χ s.1.1 = Multiplicative.ofAdd A := fun A s =>
    calc M.χ s.1.1 = Multiplicative.ofAdd (Multiplicative.toAdd (M.χ s.1.1)) :=
          (ofAdd_toAdd _).symm
      _ = Multiplicative.ofAdd A := congrArg _ s.2
  have hχV : ∀ v : ruV M.L, M.χ ⟨(v : G), M.toRuData.V_le_S v.2⟩ = 1 := by
    intro v
    have : (⟨(v : G), M.toRuData.V_le_S v.2⟩ : ruS M.L) ∈ M.χ.ker := by
      rw [M.χ_ker, Subgroup.mem_subgroupOf]
      exact v.2
    exact this
  have hfix : ∀ s : ruS M.L, M.χ ⟨x0 * (s : G) * x0⁻¹,
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L hx0L) s).mp s.2⟩ =
      Multiplicative.ofAdd (stAct (M.θ x0L) (Multiplicative.toAdd (M.χ s))) := fun s =>
    M.χ_equiv x0L s _ rfl
  have hfib : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), Nat.card {s : P // f s = A} =
      if (A.trace = 0 ∧ stAct (M.θ x0L) A = A) then 4 else 0 := by
    intro A
    by_cases hA : A.trace = 0 ∧ stAct (M.θ x0L) A = A
    · rw [if_pos hA]
      obtain ⟨htr, hfixA⟩ := hA
      obtain ⟨B, hBtr, hB⟩ := D2 A htr hfixA
      have hBtr' : IsTraceZero B := hBtr
      set t : ruS M.L := M.sOf B with ht
      have hχt : M.χ t = Multiplicative.ofAdd B := M.χ_sOf hBtr'
      have hconjt : x0 * (t : G) * x0⁻¹ ∈ ruS M.L :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L hx0L) t).mp t.2
      set sA : ruS M.L := ⟨x0 * (t : G) * x0⁻¹, hconjt⟩ * t⁻¹ with hsA
      have hsAχ : M.χ sA = Multiplicative.ofAdd A := by
        apply Multiplicative.toAdd.injective
        rw [hsA, M.toAdd_χ_mul, M.toAdd_χ_inv, hχt, hfix t, hχt, toAdd_ofAdd, toAdd_ofAdd,
          toAdd_ofAdd]
        exact hB
      have hsAsq : (x0 * (sA : G)) ^ 2 = 1 := by
        have hcoe : (sA : G) = x0 * (t : G) * x0⁻¹ * (t : G)⁻¹ := rfl
        have h1 : x0 * (sA : G) = (t : G) * x0 * (t : G)⁻¹ := by
          rw [hcoe]
          calc x0 * (x0 * (t : G) * x0⁻¹ * (t : G)⁻¹)
              = (x0 * x0) * (t : G) * x0⁻¹ * (t : G)⁻¹ := by group
            _ = (t : G) * x0 * (t : G)⁻¹ := by rw [hxx, one_mul, hinv]
        rw [h1, conj_pow, hx02]
        group
      have hsAP : (x0 * (sA : G)) ^ 2 = 1 := hsAsq
      rw [← burnsideJ28_card_CV M x0L D3]
      have hvmem : ∀ s : {s : P // f s = A}, (sA : G)⁻¹ * (s.1.1 : G) ∈ ruV M.L := by
        intro s
        have hk : sA⁻¹ * s.1.1 ∈ M.χ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hχA A s, hsAχ]
          exact inv_mul_cancel _
        rw [M.χ_ker, Subgroup.mem_subgroupOf] at hk
        exact hk
      refine Nat.card_congr
        { toFun := fun s => ⟨⟨(sA : G)⁻¹ * (s.1.1 : G), hvmem s⟩, ?_⟩
          invFun := fun v => ⟨⟨sA * ⟨(v.1 : G), M.toRuData.V_le_S v.1.2⟩, ?_⟩, ?_⟩
          left_inv := fun s => ?_
          right_inv := fun v => ?_ }
      ·
        have h2 : (x0 * ((sA : G) * ((sA : G)⁻¹ * (s.1.1 : G)))) ^ 2 = 1 := by
          rw [mul_inv_cancel_left]
          exact s.1.2
        exact (burnsideJ28_inv_mul_V M hx02 sA.2 (hvmem s) hsAP).mp h2
      · show (x0 * ((sA : G) * (v.1 : G))) ^ 2 = 1
        exact (burnsideJ28_inv_mul_V M hx02 sA.2 v.1.2 hsAP).mpr v.2
      · show Multiplicative.toAdd (M.χ (sA * ⟨(v.1 : G), M.toRuData.V_le_S v.1.2⟩)) = A
        rw [map_mul, hχV v.1, mul_one, hsAχ, toAdd_ofAdd]
      · apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        show (sA : G) * ((sA : G)⁻¹ * (s.1.1 : G)) = (s.1.1 : G)
        group
      · apply Subtype.ext
        apply Subtype.ext
        show (sA : G)⁻¹ * ((sA : G) * (v.1 : G)) = (v.1 : G)
        group
    · rw [if_neg hA]
      have : IsEmpty {s : P // f s = A} := ⟨fun s => hA ⟨by
        have h := M.χ_trace s.1.1
        rwa [show Multiplicative.toAdd (M.χ s.1.1) = A from s.2] at h, by
        have h1 : x0 * (s.1.1 : G) * x0⁻¹ = (s.1.1 : G)⁻¹ := (burnsideJ28_inv_iff hx02).mp s.1.2
        have h2 := hfix s.1.1
        have h3 : (⟨x0 * (s.1.1 : G) * x0⁻¹,
            (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L hx0L) s.1.1).mp
              s.1.1.2⟩ : ruS M.L) = s.1.1⁻¹ := Subtype.ext h1
        rw [h3] at h2
        have h4 := congrArg Multiplicative.toAdd h2
        rw [M.toAdd_χ_inv, toAdd_ofAdd] at h4
        have h5 : Multiplicative.toAdd (M.χ s.1.1) = A := s.2
        rw [h5] at h4
        exact h4.symm⟩⟩
      exact Nat.card_of_isEmpty
  rw [hsum]
  simp_rw [hfib]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_comm]
  have hcard : (Finset.univ.filter fun A : Matrix (Fin 3) (Fin 3) (ZMod 2) =>
      A.trace = 0 ∧ stAct (M.θ x0L) A = A).card = 16 := by
    rw [← Fintype.card_subtype]
    exact D1
  rw [hcard]
  norm_num

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_card_Cset {G : Type} [Group G] [Finite G] (M : RuDataM G) {x1 : G}
    (hx1L : x1 ∈ M.L) (hx12 : x1 ^ 2 = 1) (hr0 : M.θ ⟨x1, hx1L⟩ ∈ SL3.R0)
    (hr1 : M.θ ⟨x1, hx1L⟩ ≠ 1) {r : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (hr : r ∈ SL3.R0) (hr' : r ≠ 1) :
    Nat.card {x : G // ∃ hx : x ∈ M.L, M.θ ⟨x, hx⟩ = r ∧ x ^ 2 = 1} = 64 := by
  obtain ⟨g, -, hg⟩ := SL3.conj_R0_transitive _ hr0 hr1 r hr hr'
  obtain ⟨l, hl⟩ := M.θ_surj g
  rw [← burnsideJ28_card_coset_inv M hx1L hx12 hr0 hr1]
  symm
  have hto : ∀ x : {x : G // ∃ hx : x ∈ M.L, M.θ ⟨x, hx⟩ = M.θ ⟨x1, hx1L⟩ ∧ x ^ 2 = 1},
      ∃ hx : (l : G) * x.1 * (l : G)⁻¹ ∈ M.L,
        M.θ ⟨(l : G) * x.1 * (l : G)⁻¹, hx⟩ = r ∧ ((l : G) * x.1 * (l : G)⁻¹) ^ 2 = 1 := by
    intro x
    obtain ⟨hx, hθ, hx2⟩ := x.2
    have hmem : (l : G) * x.1 * (l : G)⁻¹ ∈ M.L := mul_mem (mul_mem l.2 hx) (inv_mem l.2)
    refine ⟨hmem, ?_, ?_⟩
    · have e : (⟨(l : G) * x.1 * (l : G)⁻¹, hmem⟩ : M.L) = l * ⟨x.1, hx⟩ * l⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv, hθ, hl, hg]
    · rw [conj_pow, hx2]
      group
  have hfrom : ∀ x : {x : G // ∃ hx : x ∈ M.L, M.θ ⟨x, hx⟩ = r ∧ x ^ 2 = 1},
      ∃ hx : (l : G)⁻¹ * x.1 * (l : G) ∈ M.L,
        M.θ ⟨(l : G)⁻¹ * x.1 * (l : G), hx⟩ = M.θ ⟨x1, hx1L⟩ ∧
          ((l : G)⁻¹ * x.1 * (l : G)) ^ 2 = 1 := by
    intro x
    obtain ⟨hx, hθ, hx2⟩ := x.2
    have hmem : (l : G)⁻¹ * x.1 * (l : G) ∈ M.L := mul_mem (mul_mem (inv_mem l.2) hx) l.2
    refine ⟨hmem, ?_, ?_⟩
    · have e : (⟨(l : G)⁻¹ * x.1 * (l : G), hmem⟩ : M.L) = l⁻¹ * ⟨x.1, hx⟩ * l := rfl
      rw [e, map_mul, map_mul, map_inv, hθ, hl, ← hg]
      group
    · have : ((l : G)⁻¹ * x.1 * (l : G)) ^ 2 = (l : G)⁻¹ * x.1 ^ 2 * (l : G) := by
        have := conj_pow (a := (l : G)⁻¹) (b := x.1) (i := 2)
        simpa using this
      rw [this, hx2]
      group
  exact Nat.card_congr
    { toFun := fun x => ⟨(l : G) * x.1 * (l : G)⁻¹, hto x⟩
      invFun := fun x => ⟨(l : G)⁻¹ * x.1 * (l : G), hfrom x⟩
      left_inv := fun x => Subtype.ext (by
        show (l : G)⁻¹ * ((l : G) * x.1 * (l : G)⁻¹) * (l : G) = x.1
        group)
      right_inv := fun x => Subtype.ext (by
        show (l : G) * ((l : G)⁻¹ * x.1 * (l : G)) * (l : G)⁻¹ = x.1
        group) }

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_card_inv_R1_L {G : Type} [Group G] [Finite G] (M : RuDataM G) {x1 : G}
    (hx1L : x1 ∈ M.L) (hx12 : x1 ^ 2 = 1) (hr0 : M.θ ⟨x1, hx1L⟩ ∈ SL3.R0)
    (hr1 : M.θ ⟨x1, hx1L⟩ ≠ 1) :
    Nat.card {x : G // x ∈ M.R1 ∧ x ^ 2 = 1} =
      Nat.card {s : ruS M.L // (s : G) ^ 2 = 1} + 3 * 64 := by
  classical
  have hR1L : M.R1 ≤ M.L := Subgroup.map_subtype_le _
  let P := {x : G // x ∈ M.R1 ∧ x ^ 2 = 1}
  let f : P → Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) := fun x => M.θ ⟨x.1, hR1L x.2.1⟩
  have hsum : Nat.card P = ∑ r : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      Nat.card {x : P // f x = r} := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
  have hfR0 : ∀ x : P, f x ∈ SL3.R0 := by
    intro x
    obtain ⟨h, hh⟩ := mem_pullL.mp x.2.1
    exact hh
  have hmemR1 : ∀ (z : G) (hz : z ∈ M.L), M.θ ⟨z, hz⟩ ∈ SL3.R0 → z ∈ M.R1 := fun z hz h =>
    mem_pullL.mpr ⟨hz, h⟩
  have hfib : ∀ r : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), Nat.card {x : P // f x = r} =
      if r ∈ SL3.R0 then (if r = 1 then Nat.card {s : ruS M.L // (s : G) ^ 2 = 1} else 64)
        else 0 := by
    intro r
    by_cases hr : r ∈ SL3.R0
    · rw [if_pos hr]
      have hcset : Nat.card {x : P // f x = r} =
          Nat.card {x : G // ∃ hx : x ∈ M.L, M.θ ⟨x, hx⟩ = r ∧ x ^ 2 = 1} := by
        refine Nat.card_congr
          { toFun := fun x => ⟨x.1.1, hR1L x.1.2.1, x.2, x.1.2.2⟩
            invFun := fun z => ⟨⟨z.1, hmemR1 z.1 z.2.choose (by rw [z.2.choose_spec.1]; exact hr),
              z.2.choose_spec.2⟩, z.2.choose_spec.1⟩
            left_inv := fun x => rfl
            right_inv := fun z => rfl }
      rw [hcset]
      by_cases hr1' : r = 1
      · rw [if_pos hr1']
        subst hr1'
        have hθS : ∀ s : ruS M.L, M.θ ⟨(s : G), M.toRuData.S_le_L s.2⟩ = 1 := by
          intro s
          have : (⟨(s : G), M.toRuData.S_le_L s.2⟩ : M.L) ∈ M.θ.ker := by
            rw [M.θ_ker, Subgroup.mem_subgroupOf]
            exact s.2
          exact this
        refine Nat.card_congr
          { toFun := fun z => ⟨⟨z.1, ?_⟩, z.2.choose_spec.2⟩
            invFun := fun s => ⟨(s.1 : G), M.toRuData.S_le_L s.1.2, hθS s.1, s.2⟩
            left_inv := fun z => rfl
            right_inv := fun s => rfl }
        have hk : (⟨z.1, z.2.choose⟩ : M.L) ∈ M.θ.ker := by
          rw [MonoidHom.mem_ker]
          exact z.2.choose_spec.1
        rw [M.θ_ker, Subgroup.mem_subgroupOf] at hk
        exact hk
      · rw [if_neg hr1']
        exact burnsideJ28_card_Cset M hx1L hx12 hr0 hr1 hr hr1'
    · rw [if_neg hr]
      have : IsEmpty {x : P // f x = r} := ⟨fun x => hr (x.2 ▸ hfR0 x.1)⟩
      exact Nat.card_of_isEmpty
  rw [hsum]
  simp_rw [hfib]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  set F := Finset.univ.filter
    (fun r : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) => r ∈ SL3.R0) with hF
  have h1F : (1 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∈ F := by
    simp [hF]
  have hcardF : F.card = 4 := by
    have := SL3.card_R0
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at this
    exact this
  rw [← Finset.add_sum_erase F _ h1F, if_pos rfl]
  have h64 : ∑ x ∈ F.erase 1, (if x = 1 then Nat.card {s : ruS M.L // (s : G) ^ 2 = 1} else 64) =
      ∑ x ∈ F.erase 1, 64 :=
    Finset.sum_congr rfl fun x hx => if_neg (Finset.ne_of_mem_erase hx)
  rw [h64, Finset.sum_const, Finset.card_erase_of_mem h1F, hcardF, smul_eq_mul]

end BurnsideJ28Cnt

section BurnsideJ28Hside

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_card_fib_conj {G : Type} [Group G] [Finite G] (M : RuDataM G)
    (A : SigmaL2F4) (h : ruH M.T) :
    Nat.card {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = M.φ h * A * (M.φ h)⁻¹ ∧ x ^ 2 = 1} =
      Nat.card {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = A ∧ x ^ 2 = 1} := by
  symm
  have hto : ∀ x : {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = A ∧ x ^ 2 = 1},
      ∃ hx : (h : G) * x.1 * (h : G)⁻¹ ∈ ruH M.T,
        M.φ ⟨(h : G) * x.1 * (h : G)⁻¹, hx⟩ = M.φ h * A * (M.φ h)⁻¹ ∧
          ((h : G) * x.1 * (h : G)⁻¹) ^ 2 = 1 := by
    intro x
    obtain ⟨hx, hφ, hx2⟩ := x.2
    have hmem : (h : G) * x.1 * (h : G)⁻¹ ∈ ruH M.T := mul_mem (mul_mem h.2 hx) (inv_mem h.2)
    refine ⟨hmem, ?_, ?_⟩
    · have e : (⟨(h : G) * x.1 * (h : G)⁻¹, hmem⟩ : ruH M.T) = h * ⟨x.1, hx⟩ * h⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv, hφ]
    · rw [conj_pow, hx2]
      group
  have hfrom : ∀ y : {x : G // ∃ hx : x ∈ ruH M.T,
        M.φ ⟨x, hx⟩ = M.φ h * A * (M.φ h)⁻¹ ∧ x ^ 2 = 1},
      ∃ hx : (h : G)⁻¹ * y.1 * (h : G) ∈ ruH M.T,
        M.φ ⟨(h : G)⁻¹ * y.1 * (h : G), hx⟩ = A ∧ ((h : G)⁻¹ * y.1 * (h : G)) ^ 2 = 1 := by
    intro y
    obtain ⟨hy, hφ, hy2⟩ := y.2
    have hmem : (h : G)⁻¹ * y.1 * (h : G) ∈ ruH M.T := mul_mem (mul_mem (inv_mem h.2) hy) h.2
    refine ⟨hmem, ?_, ?_⟩
    · have e : (⟨(h : G)⁻¹ * y.1 * (h : G), hmem⟩ : ruH M.T) = h⁻¹ * ⟨y.1, hy⟩ * h := rfl
      rw [e, map_mul, map_mul, map_inv, hφ]
      group
    · have : ((h : G)⁻¹ * y.1 * (h : G)) ^ 2 = (h : G)⁻¹ * y.1 ^ 2 * (h : G) := by
        have := conj_pow (a := (h : G)⁻¹) (b := y.1) (i := 2)
        simpa using this
      rw [this, hy2]
      group
  exact Nat.card_congr
    { toFun := fun x => ⟨(h : G) * x.1 * (h : G)⁻¹, hto x⟩
      invFun := fun y => ⟨(h : G)⁻¹ * y.1 * (h : G), hfrom y⟩
      left_inv := fun x => Subtype.ext (by
        show (h : G)⁻¹ * ((h : G) * x.1 * (h : G)⁻¹) * (h : G) = x.1
        group)
      right_inv := fun y => Subtype.ext (by
        show (h : G) * ((h : G)⁻¹ * y.1 * (h : G)) * (h : G)⁻¹ = y.1
        group) }

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_card_fib_conj' {G : Type} [Group G] [Finite G] (M : RuDataM G)
    (A g : SigmaL2F4) :
    Nat.card {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = g * A * g⁻¹ ∧ x ^ 2 = 1} =
      Nat.card {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = A ∧ x ^ 2 = 1} := by
  obtain ⟨h, rfl⟩ := M.φ_surj g
  exact burnsideJ28_card_fib_conj M A h

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_card_fib_inv {G : Type} [Group G] [Finite G] (M : RuDataM G)
    {A A' : SigmaL2F4} (hA2 : A ^ 2 = 1) (hAr : A.right = 1) (hA1 : A ≠ 1)
    (hA2' : A' ^ 2 = 1) (hAr' : A'.right = 1) (hA1' : A' ≠ 1) :
    Nat.card {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = A' ∧ x ^ 2 = 1} =
      Nat.card {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = A ∧ x ^ 2 = 1} := by
  obtain ⟨g, hg⟩ := burnsideJ28_sl_inv_conj A A' hA2 hAr hA1 hA2' hAr' hA1'
  rw [← hg]
  exact burnsideJ28_card_fib_conj' M A g

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_card_fib_le {G : Type} [Group G] [Finite G] (M : RuDataM G)
    {A : SigmaL2F4} (hA1 : A ≠ 1) :
    Nat.card {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = A ∧ x ^ 2 = 1} ≤ 128 := by
  by_cases hne : Nonempty {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = A ∧ x ^ 2 = 1}
  · obtain ⟨⟨k, hkH, hkA, hk2⟩⟩ := hne
    have hkQ : k ∉ ruQ M.T := by
      intro hq
      apply hA1
      rw [← hkA]
      have hk : (⟨k, hkH⟩ : ruH M.T) ∈ M.φ.ker := by
        rw [M.φ_ker, Subgroup.mem_subgroupOf]
        exact hq
      exact MonoidHom.mem_ker.mp hk
    have hQ : ∀ x : {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = A ∧ x ^ 2 = 1},
        k⁻¹ * x.1 ∈ ruQ M.T := by
      intro x
      obtain ⟨hx, hφ, -⟩ := x.2
      have hker : (⟨k, hkH⟩ : ruH M.T)⁻¹ * ⟨x.1, hx⟩ ∈ M.φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hφ, hkA, inv_mul_cancel]
      rw [M.φ_ker, Subgroup.mem_subgroupOf] at hker
      simpa using hker
    refine (Nat.card_le_card_of_injective (fun x =>
      (⟨⟨k⁻¹ * x.1, hQ x⟩, by
        show (k * (k⁻¹ * x.1)) ^ 2 = 1
        rw [mul_inv_cancel_left]
        obtain ⟨hx, -, hx2⟩ := x.2
        exact hx2⟩ : {q : ruQ M.T // (k * (q : G)) ^ 2 = 1})) ?_).trans
      (M.card_inv_coset_le hkH hkQ hk2)
    intro x y h
    have h' : k⁻¹ * x.1 = k⁻¹ * y.1 := congrArg (fun w => ((w.1 : ruQ M.T) : G)) h
    exact Subtype.ext (mul_left_cancel h')
  · have := not_nonempty_iff.mp hne
    rw [Nat.card_of_isEmpty]
    omega

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_R1_le_H {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    M.R1 ≤ ruH M.T := by
  have hSH : ruS M.L ≤ ruH M.T := M.toRuData.S_le_T.trans M.toRuData.T_le_H
  have hQH : ruQ M.T ≤ ruH M.T := pCoreOf_le 2 _
  rw [← M.Q_sup_S]
  exact sup_le hQH hSH

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_φ_R1 {G : Type} [Group G] [Finite G] (M : RuDataM G) {x : G}
    (hx : x ∈ M.R1) : M.φ ⟨x, burnsideJ28_R1_le_H M hx⟩ ∈ Sigma.U0 := by
  have hSH : ruS M.L ≤ ruH M.T := M.toRuData.S_le_T.trans M.toRuData.T_le_H
  have hQH : ruQ M.T ≤ ruH M.T := pCoreOf_le 2 _
  have hR : (M.R1.subgroupOf (ruH M.T)).map M.φ = ((ruS M.L).subgroupOf (ruH M.T)).map M.φ := by
    rw [← M.Q_sup_S, Subgroup.subgroupOf_sup hQH hSH, Subgroup.map_sup]
    have : ((ruQ M.T).subgroupOf (ruH M.T)).map M.φ = ⊥ := by
      rw [← M.φ_ker]
      exact (Subgroup.map_eq_bot_iff _).mpr le_rfl
    rw [this, bot_sup_eq]
  have hmem : M.φ ⟨x, burnsideJ28_R1_le_H M hx⟩ ∈ (M.R1.subgroupOf (ruH M.T)).map M.φ :=
    ⟨⟨x, burnsideJ28_R1_le_H M hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  rw [hR] at hmem
  obtain ⟨⟨s, hsH⟩, hs, he⟩ := hmem
  rw [← he]
  exact M.φ_S_mem (Subgroup.mem_subgroupOf.mp hs)

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_mem_R1_of_φ {G : Type} [Group G] [Finite G] (M : RuDataM G) {x : G}
    (hxH : x ∈ ruH M.T) (hx : M.φ ⟨x, hxH⟩ ∈ Sigma.U0) : x ∈ M.R1 := by
  obtain ⟨s, hs, hφs⟩ := M.exists_S_of_U0 hx
  have hsH : s ∈ ruH M.T := M.toRuData.T_le_H (M.toRuData.S_le_T hs)
  have hk : (⟨x, hxH⟩ : ruH M.T) * ⟨s, hsH⟩⁻¹ ∈ M.φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hφs, mul_inv_cancel]
  rw [M.φ_ker, Subgroup.mem_subgroupOf] at hk
  have hk' : x * s⁻¹ ∈ ruQ M.T := hk
  rw [← M.Q_sup_S]
  have e : x = (x * s⁻¹) * s := by group
  rw [e]
  exact Subgroup.mul_mem_sup hk' hs

set_option linter.constructorNameAsVariable false in
open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_card_inv_R1_H {G : Type} [Group G] [Finite G] (M : RuDataM G)
    {u : SigmaL2F4} (hu2 : u ^ 2 = 1) (hur : u.right = 1) (hu1 : u ≠ 1) :
    Nat.card {x : G // x ∈ M.R1 ∧ x ^ 2 = 1} =
      Nat.card {x : G // x ∈ ruQ M.T ∧ x ^ 2 = 1} +
        3 * Nat.card {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = u ∧ x ^ 2 = 1} := by
  classical
  have hR1H := burnsideJ28_R1_le_H M
  let P := {x : G // x ∈ M.R1 ∧ x ^ 2 = 1}
  let f : P → SigmaL2F4 := fun x => M.φ ⟨x.1, hR1H x.2.1⟩
  have hsum : Nat.card P = ∑ A : SigmaL2F4, Nat.card {x : P // f x = A} := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
  have hfib : ∀ A : SigmaL2F4, Nat.card {x : P // f x = A} =
      if A ∈ Sigma.U0 then
        Nat.card {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = A ∧ x ^ 2 = 1} else 0 := by
    intro A
    by_cases hA : A ∈ Sigma.U0
    · rw [if_pos hA]
      refine Nat.card_congr
        { toFun := fun x => ⟨x.1.1, hR1H x.1.2.1, x.2, x.1.2.2⟩
          invFun := fun z => ⟨⟨z.1, burnsideJ28_mem_R1_of_φ M z.2.choose
              (by rw [z.2.choose_spec.1]; exact hA), z.2.choose_spec.2⟩, z.2.choose_spec.1⟩
          left_inv := fun x => rfl
          right_inv := fun z => rfl }
    · rw [if_neg hA]
      have : IsEmpty {x : P // f x = A} :=
        ⟨fun x => hA (x.2 ▸ burnsideJ28_φ_R1 M x.1.2.1)⟩
      exact Nat.card_of_isEmpty
  rw [hsum]
  simp_rw [hfib]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  rw [← Finset.add_sum_erase (Finset.univ.filter (fun A : SigmaL2F4 => A ∈ Sigma.U0)) _
    (a := 1) (by simp)]
  have hcardF : ((Finset.univ.filter (fun A : SigmaL2F4 => A ∈ Sigma.U0)).erase 1).card = 3 := by
    rw [Finset.card_erase_of_mem (by simp)]
    have := Sigma.card_U0
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at this
    rw [this]
  have h1 : Nat.card {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = 1 ∧ x ^ 2 = 1} =
      Nat.card {x : G // x ∈ ruQ M.T ∧ x ^ 2 = 1} := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1, ?_, x.2.choose_spec.2⟩
        invFun := fun y => ⟨y.1, pCoreOf_le 2 _ y.2.1, ?_, y.2.2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    · have hk : (⟨x.1, x.2.choose⟩ : ruH M.T) ∈ M.φ.ker := by
        rw [MonoidHom.mem_ker]
        exact x.2.choose_spec.1
      rw [M.φ_ker, Subgroup.mem_subgroupOf] at hk
      exact hk
    · have hk : (⟨y.1, pCoreOf_le 2 _ y.2.1⟩ : ruH M.T) ∈ M.φ.ker := by
        rw [M.φ_ker, Subgroup.mem_subgroupOf]
        exact y.2.1
      exact MonoidHom.mem_ker.mp hk
  have h3 : ∑ A ∈ (Finset.univ.filter (fun A : SigmaL2F4 => A ∈ Sigma.U0)).erase 1,
      Nat.card {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = A ∧ x ^ 2 = 1} =
      ∑ A ∈ (Finset.univ.filter (fun A : SigmaL2F4 => A ∈ Sigma.U0)).erase 1,
        Nat.card {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = u ∧ x ^ 2 = 1} := by
    refine Finset.sum_congr rfl fun A hA => ?_
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hA
    obtain ⟨hA1, hAU⟩ := hA
    exact burnsideJ28_card_fib_inv M hu2 hur hu1 (burnsideJ28_U0_sq A hAU) hAU.2 hA1
  rw [h3, Finset.sum_const, hcardF, smul_eq_mul, h1]

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_card_inv_Q {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    Nat.card {x : G // x ∈ ruQ M.T ∧ x ^ 2 = 1} = 272 := by
  classical
  have := Fintype.ofFinite G
  obtain ⟨l, hl, hne, w, hwl, hwQ, hwC, hw2⟩ := burnsideJ28_exists_w M
  have hI := burnsideJ28_card_I M hwQ hwC hw2
  have hUc := M.toRuData.card_U
  rw [natCard_subtype_eq] at hI ⊢
  have hUc' : (Finset.univ.filter fun x : G => x ∈ ruU M.L M.T).card = 32 := by
    rw [← natCard_subtype_eq]
    exact hUc
  have hsplit : (Finset.univ.filter fun x : G => x ∈ ruQ M.T ∧ x ^ 2 = 1) =
      (Finset.univ.filter fun x : G => x ∈ ruQ M.T ∧ x ∉ ruU M.L M.T ∧ x ^ 2 = 1) ∪
        (Finset.univ.filter fun x : G => x ∈ ruU M.L M.T) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨hQ, hx2⟩
      by_cases hU : x ∈ ruU M.L M.T
      · exact Or.inr hU
      · exact Or.inl ⟨hQ, hU, hx2⟩
    · rintro (⟨hQ, -, hx2⟩ | hU)
      · exact ⟨hQ, hx2⟩
      · exact ⟨M.U_le_Q hU, M.U_sq hU⟩
  have hdisj : Disjoint
      (Finset.univ.filter fun x : G => x ∈ ruQ M.T ∧ x ∉ ruU M.L M.T ∧ x ^ 2 = 1)
      (Finset.univ.filter fun x : G => x ∈ ruU M.L M.T) :=
    Finset.disjoint_filter.mpr fun x _ h1 h2 => h1.2.1 h2
  rw [hsplit, Finset.card_union_of_disjoint hdisj, hI, hUc']

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_exists_x1 {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    ∃ x1 : G, ∃ hx1L : x1 ∈ M.L, x1 ^ 2 = 1 ∧ M.θ ⟨x1, hx1L⟩ ∈ SL3.R0 ∧
      M.θ ⟨x1, hx1L⟩ ≠ 1 := by
  obtain ⟨l, hl, hne, w, hwl, hwQ, hwC, hw2⟩ := burnsideJ28_exists_w M
  obtain ⟨k, hkK, hkS⟩ := M.exists_conj_not_mem_S hwQ hwC
  have hkH : k ∈ ruH M.T := M.K_le_H hkK
  have hx1Q : k * w * k⁻¹ ∈ ruQ M.T := M.conj_mem_Q hkH hwQ
  have hx1L : k * w * k⁻¹ ∈ M.L := M.Q_le_L hx1Q
  refine ⟨k * w * k⁻¹, hx1L, ?_, ?_, ?_⟩
  · rw [conj_pow, hw2]
    group
  · rw [← M.θQ_eq]
    exact ⟨⟨k * w * k⁻¹, hx1L⟩, Subgroup.mem_subgroupOf.mpr hx1Q, rfl⟩
  · intro h1
    apply hkS
    have hk : (⟨k * w * k⁻¹, hx1L⟩ : M.L) ∈ M.θ.ker := h1
    rw [M.θ_ker, Subgroup.mem_subgroupOf] at hk
    exact hk

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_card_inv_K {G : Type} [Group G] [Finite G] (M : RuDataM G)
    {u : SigmaL2F4} (hu2 : u ^ 2 = 1) (hur : u.right = 1) (hu1 : u ≠ 1) :
    Nat.card {x : G // x ∈ M.K ∧ x ∉ ruQ M.T ∧ x ^ 2 = 1} =
      15 * Nat.card {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = u ∧ x ^ 2 = 1} := by
  classical
  have hKH := M.K_le_H
  let g : {x : G // x ∈ M.K ∧ x ∉ ruQ M.T ∧ x ^ 2 = 1} →
      {A : SigmaL2F4 // A ^ 2 = 1 ∧ A.right = 1 ∧ A ≠ 1} := fun x =>
    ⟨M.φ ⟨x.1, hKH x.2.1⟩, by
      rw [← map_pow]
      have : (⟨x.1, hKH x.2.1⟩ : ruH M.T) ^ 2 = 1 := Subtype.ext (by simpa using x.2.2.2)
      rw [this, map_one], by
      obtain ⟨hk, h1⟩ := M.mem_K_iff.mp x.2.1
      exact h1, M.φ_ne_one (hKH x.2.1) x.2.2.1⟩
  have hsum : Nat.card {x : G // x ∈ M.K ∧ x ∉ ruQ M.T ∧ x ^ 2 = 1} =
      ∑ A : {A : SigmaL2F4 // A ^ 2 = 1 ∧ A.right = 1 ∧ A ≠ 1}, Nat.card {x // g x = A} := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv g), Nat.card_sigma]
  have hfib : ∀ A : {A : SigmaL2F4 // A ^ 2 = 1 ∧ A.right = 1 ∧ A ≠ 1},
      Nat.card {x // g x = A} =
        Nat.card {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = u ∧ x ^ 2 = 1} := by
    intro A
    rw [← burnsideJ28_card_fib_inv M hu2 hur hu1 A.2.1 A.2.2.1 A.2.2.2]
    have hfrom : ∀ y : {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = A.1 ∧ x ^ 2 = 1},
        y.1 ∈ M.K ∧ y.1 ∉ ruQ M.T ∧ y.1 ^ 2 = 1 := by
      intro y
      obtain ⟨hy, hφ, hy2⟩ := y.2
      refine ⟨M.mem_K_iff.mpr ⟨hy, by rw [hφ]; exact A.2.2.1⟩, fun hq => A.2.2.2 ?_, hy2⟩
      rw [← hφ]
      have hk : (⟨y.1, hy⟩ : ruH M.T) ∈ M.φ.ker := by
        rw [M.φ_ker, Subgroup.mem_subgroupOf]
        exact hq
      exact MonoidHom.mem_ker.mp hk
    exact Nat.card_congr
      { toFun := fun x => ⟨x.1.1, hKH x.1.2.1, congrArg Subtype.val x.2, x.1.2.2.2⟩
        invFun := fun y => ⟨⟨y.1, hfrom y⟩, Subtype.ext y.2.choose_spec.1⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  rw [hsum, Finset.sum_congr rfl (fun A _ => hfib A), Finset.sum_const, Finset.card_univ,
    Sigma.card_inv_sl, smul_eq_mul]

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_card_N {G : Type} [Group G] [Finite G] (M : RuDataM G)
    {u : SigmaL2F4} (hu2 : u ^ 2 = 1) (hur : u.right = 1) (hu1 : u ≠ 1) :
    Nat.card {x : G // ∃ hx : x ∈ ruH M.T, M.φ ⟨x, hx⟩ = u ∧ x ^ 2 = 1} = 96 := by
  classical
  obtain ⟨x1, hx1L, hx12, hr0, hr1⟩ := burnsideJ28_exists_x1 M
  have hS := burnsideJ28_card_inv_S M
  have hL := burnsideJ28_card_inv_R1_L M hx1L hx12 hr0 hr1
  have hH := burnsideJ28_card_inv_R1_H M hu2 hur hu1
  have hQ := burnsideJ28_card_inv_Q M
  have hNle := burnsideJ28_card_fib_le M hu1
  have hz58 : Nat.card {A : Matrix (Fin 3) (Fin 3) (ZMod 2) //
      A.trace = 0 ∧ ∃ s : ruS M.L, M.χ s = Multiplicative.ofAdd A ∧ (s : G) ^ 2 = 1} ≤ 58 := by
    omega
  let Z : Set (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
    {A | A.trace = 0 ∧ ∃ s : ruS M.L, M.χ s = Multiplicative.ofAdd A ∧ (s : G) ^ 2 = 1}
  have hZe : ∀ A ∈ Z, A * A = 0 ∨ A * A * A + A + 1 = 0 :=
    burnsideJ28_Z_eq Z (fun A htr hA => ⟨htr, burnsideJ28_E_sub_Z M htr hA⟩) (fun A hA => hA.1)
      (fun g A hA => ⟨by rw [SL3.trace_stAct]; exact hA.1, burnsideJ28_zq_conj M hA.2 g⟩) hz58
  have hZeq : Z = {B : Matrix (Fin 3) (Fin 3) (ZMod 2) |
      B.trace = 0 ∧ (B * B = 0 ∨ B * B * B + B + 1 = 0)} := by
    ext A
    exact ⟨fun hA => ⟨hA.1, hZe A hA⟩, fun hA => ⟨hA.1, burnsideJ28_E_sub_Z M hA.1 hA.2⟩⟩
  have hZ46 : Nat.card {A : Matrix (Fin 3) (Fin 3) (ZMod 2) //
      A.trace = 0 ∧ ∃ s : ruS M.L, M.χ s = Multiplicative.ofAdd A ∧ (s : G) ^ 2 = 1} = 46 := by
    have h1 : Nat.card Z = 46 := by
      rw [hZeq]
      have := burnsideJ28_card_E
      rw [← Nat.card_eq_fintype_card] at this
      exact this
    exact h1
  omega

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_card_inv_K_eq {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    Nat.card {x : G // x ∈ M.K ∧ x ∉ ruQ M.T ∧ x ^ 2 = 1} = 1440 := by
  obtain ⟨⟨u, hu2, hur, hu1⟩⟩ : Nonempty {g : SigmaL2F4 // g ^ 2 = 1 ∧ g.right = 1 ∧ g ≠ 1} := by
    rw [← Fintype.card_pos_iff, Sigma.card_inv_sl]
    norm_num
  rw [burnsideJ28_card_inv_K M hu2 hur hu1, burnsideJ28_card_N M hu2 hur hu1]

end BurnsideJ28Hside

section BurnsideJ28Three4

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_card_zG_H {G : Type} [Group G] [Finite G] (M : RuDataM G) {w : G}
    (hwQ : w ∈ ruQ M.T) (hwC : w ∉ M.HC) (hw2 : w ^ 2 = 1)
    (h480 : Nat.card {x : G // IsConj M.z x ∧ x ∈ M.K ∧ x ∉ ruQ M.T} = 480) :
    Nat.card {x : G // IsConj M.z x ∧ x ∈ ruH M.T} = 1391 := by
  classical
  have := Fintype.ofFinite G
  have hI := burnsideJ28_card_I M hwQ hwC hw2
  have hHK := M.card_inv_H_K
  have hUc := M.toRuData.card_U
  rw [natCard_subtype_eq] at hI hHK h480
  have hUc' : (Finset.univ.filter fun x : G => x ∈ ruU M.L M.T).card = 32 := by
    rw [← natCard_subtype_eq]
    exact hUc
  have hDF : (Finset.univ.filter fun x : G => x ∈ ruU M.L M.T ∧ x ≠ 1).card = 31 := by
    have e : (Finset.univ.filter fun x : G => x ∈ ruU M.L M.T ∧ x ≠ 1) =
        (Finset.univ.filter fun x : G => x ∈ ruU M.L M.T).erase 1 := by
      ext x
      simp [and_comm]
    rw [e, Finset.card_erase_of_mem (by simp), hUc']
  rw [natCard_subtype_eq]
  have hsplit : (Finset.univ.filter fun x : G => IsConj M.z x ∧ x ∈ ruH M.T) =
      (((Finset.univ.filter fun x : G => x ∈ ruH M.T ∧ x ∉ M.K ∧ x ^ 2 = 1) ∪
        (Finset.univ.filter fun x : G => IsConj M.z x ∧ x ∈ M.K ∧ x ∉ ruQ M.T)) ∪
        (Finset.univ.filter fun x : G => x ∈ ruQ M.T ∧ x ∉ ruU M.L M.T ∧ x ^ 2 = 1)) ∪
        (Finset.univ.filter fun x : G => x ∈ ruU M.L M.T ∧ x ≠ 1) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨hz, hxH⟩
      have hx2 : x ^ 2 = 1 := by
        obtain ⟨g, rfl⟩ := isConj_iff.mp hz
        calc (g * M.z * g⁻¹) ^ 2 = g * M.z ^ 2 * g⁻¹ := by rw [conj_pow]
          _ = 1 := by rw [M.z_sq]; group
      have hx1 : x ≠ 1 := by
        rintro rfl
        exact M.z_ne_one (isConj_one_left.mp hz)
      by_cases hK : x ∈ M.K
      · by_cases hQ : x ∈ ruQ M.T
        · by_cases hU : x ∈ ruU M.L M.T
          · exact Or.inr ⟨hU, hx1⟩
          · exact Or.inl (Or.inr ⟨hQ, hU, hx2⟩)
        · exact Or.inl (Or.inl (Or.inr ⟨hz, hK, hQ⟩))
      · exact Or.inl (Or.inl (Or.inl ⟨hxH, hK, hx2⟩))
    · rintro (((⟨hxH, hK, hx2⟩ | ⟨hz, hK, hQ⟩) | ⟨hQ, hU, hx2⟩) | ⟨hU, hx1⟩)
      · exact ⟨M.lemma_J26.2.2.1 x hxH hK hx2, hxH⟩
      · exact ⟨hz, M.K_le_H hK⟩
      · have hx1 : x ≠ 1 := by
          rintro rfl
          exact hU (one_mem _)
        exact ⟨M.lemma_J26.2.2.2.2.1 x hQ hx2 hx1, pCoreOf_le 2 _ hQ⟩
      · exact ⟨M.isConj_z_of_U hU hx1, M.U_le_H hU⟩
  rw [hsplit]
  have hUQ : ∀ x : G, x ∈ ruU M.L M.T → x ∈ ruQ M.T := fun x hx => M.U_le_Q hx
  have hQK : ∀ x : G, x ∈ ruQ M.T → x ∈ M.K := fun x hx => M.Q_le_K hx
  have dAB : Disjoint (Finset.univ.filter fun x : G => x ∈ ruH M.T ∧ x ∉ M.K ∧ x ^ 2 = 1)
      (Finset.univ.filter fun x : G => IsConj M.z x ∧ x ∈ M.K ∧ x ∉ ruQ M.T) :=
    Finset.disjoint_filter.mpr fun x _ h1 h2 => h1.2.1 h2.2.1
  have dABC : Disjoint ((Finset.univ.filter fun x : G => x ∈ ruH M.T ∧ x ∉ M.K ∧ x ^ 2 = 1) ∪
      (Finset.univ.filter fun x : G => IsConj M.z x ∧ x ∈ M.K ∧ x ∉ ruQ M.T))
      (Finset.univ.filter fun x : G => x ∈ ruQ M.T ∧ x ∉ ruU M.L M.T ∧ x ^ 2 = 1) := by
    refine Finset.disjoint_union_left.mpr ⟨?_, ?_⟩
    · exact Finset.disjoint_filter.mpr fun x _ h1 h2 => h1.2.1 (hQK x h2.1)
    · exact Finset.disjoint_filter.mpr fun x _ h1 h2 => h1.2.2 h2.1
  have dABCD : Disjoint (((Finset.univ.filter fun x : G => x ∈ ruH M.T ∧ x ∉ M.K ∧ x ^ 2 = 1) ∪
      (Finset.univ.filter fun x : G => IsConj M.z x ∧ x ∈ M.K ∧ x ∉ ruQ M.T)) ∪
      (Finset.univ.filter fun x : G => x ∈ ruQ M.T ∧ x ∉ ruU M.L M.T ∧ x ^ 2 = 1))
      (Finset.univ.filter fun x : G => x ∈ ruU M.L M.T ∧ x ≠ 1) := by
    refine Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Finset.disjoint_filter.mpr fun x _ h1 h2 => h1.2.1 (hQK x (hUQ x h2.1))
    · exact Finset.disjoint_filter.mpr fun x _ h1 h2 => h1.2.2 (hUQ x h2.1)
    · exact Finset.disjoint_filter.mpr fun x _ h1 h2 => h1.2.1 h2.1
  rw [Finset.card_union_of_disjoint dABCD, Finset.card_union_of_disjoint dABC,
    Finset.card_union_of_disjoint dAB, hHK, h480, hI, hDF]

end BurnsideJ28Three4

private theorem burnsideJ28_J_3_4_of_KQ
    (h480 : ∀ (G : Type) [Group G] [Finite G] (M : CFSG.Quasithin.RuType.RuDataM G),
      Nat.card {x : G // IsConj M.z x ∧ x ∈ M.K ∧ x ∉ CFSG.Quasithin.RuType.ruQ M.T} = 480) :
    J_3_4 := by
  intro G _ _ L V T h z hz
  obtain ⟨M, hML, hMT, hV, hZ, hH, hQ, hU⟩ :=
    burnsideJ28_exists_M CFSG.Quasithin.RuType.stUnique h
  subst hML
  subst hMT
  subst hV
  have hzz : z = M.z := burnsideJ28_eq_z M (hz.trans hZ)
  subst hzz
  obtain ⟨l, hl, hne, w, hwl, hwQ, hwC, hw2⟩ := burnsideJ28_exists_w M
  rw [hH]
  have hcard := burnsideJ28_card_zG_H M hwQ hwC hw2 (h480 G M)
  have hset : CFSG.ASVolI.ChIJK.conjClass M.z ∩ (CFSG.Quasithin.RuType.ruH M.T : Set G) =
      {x | IsConj M.z x ∧ x ∈ CFSG.Quasithin.RuType.ruH M.T} := by
    ext x
    constructor
    · rintro ⟨hx, hxH⟩
      exact ⟨(burnsideJ28_mem_conjClass_iff _ _).mp hx, hxH⟩
    · rintro ⟨hx, hxH⟩
      exact ⟨(burnsideJ28_mem_conjClass_iff _ _).mpr hx, hxH⟩
  rw [hset, ← Nat.card_coe_set_eq]
  exact hcard

end BurnsideJ34

section

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_card_sH {G : Type} [Group G] [Finite G] (M : RuDataM G) {s : G}
    (hs : s ∈ M.S0) (hs1 : s ≠ 1) :
    Nat.card {x : G // IsConj s x ∧ x ∈ ruH M.T} = 960 := by
  let _ : MulAction (ruH M.T) G := MulAction.compHom G ((MulAut.conj).comp (ruH M.T).subtype)
  have hsmul : ∀ (l : ruH M.T) (x : G), l • x = (l : G) * x * (l : G)⁻¹ := fun _ _ => rfl
  have hsH : s ∈ ruH M.T := M.S0_le_H hs
  have horb : MulAction.orbit (ruH M.T) s = {u : G | IsConj s u ∧ u ∈ ruH M.T} := by
    ext u
    simp only [MulAction.mem_orbit_iff, hsmul]
    show _ ↔ IsConj s u ∧ u ∈ ruH M.T
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨isConj_iff.mpr ⟨l, rfl⟩, mul_mem (mul_mem l.2 hsH) (inv_mem l.2)⟩
    · rintro ⟨hsu, huH⟩
      obtain ⟨⟨h, hh, rfl⟩, -, -⟩ := M.lemma_J27_8 hs hs1 huH hsu
      exact ⟨⟨h, hh⟩, rfl⟩
  have hstab : MulAction.stabilizer (ruH M.T) s =
      (ruH M.T ⊓ Subgroup.centralizer ({s} : Set G)).subgroupOf (ruH M.T) := by
    ext l
    rw [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      refine ⟨l.2, ?_⟩
      calc (l : G) * s = ((l : G) * s * (l : G)⁻¹) * l := by group
        _ = s * (l : G) := by rw [h]
    · rintro ⟨-, h⟩
      calc (l : G) * s * (l : G)⁻¹ = s * (l : G) * (l : G)⁻¹ := by rw [h]
        _ = s := by group
  have hstabcard : Nat.card (MulAction.stabilizer (ruH M.T) s) = 2 ^ 8 := by
    rw [hstab, card_subgroupOf_of_le inf_le_left, M.centralizer_H_eq hs hs1,
      M.card_centralizer_S (M.mem_S0.mp hs).1 (M.not_mem_V_of_S0 hs hs1)]
  have hcard : Nat.card (MulAction.orbit (ruH M.T) s) = 960 := by
    rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (ruH M.T) s)]
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (MulAction.stabilizer (ruH M.T) s)
    rw [hstabcard, M.toRuData.card_H] at h
    omega
  rw [← hcard, horb]
  rfl

open CFSG.Quasithin.RuType CFSG.LieType.BorelTits in
private theorem burnsideJ28_card_zG_KQ {G : Type} [Group G] [Finite G] (M : RuDataM G) :
    Nat.card {x : G // IsConj M.z x ∧ x ∈ M.K ∧ x ∉ ruQ M.T} = 480 := by
  classical
  have := Fintype.ofFinite G
  obtain ⟨s, hs, hs1⟩ := M.exists_S0_ne_one
  have hs2 : s ^ 2 = 1 := M.S0_elem.2 s hs
  obtain ⟨hzs, hall⟩ := M.lemma_J27_4 hs hs1
  have hI := burnsideJ28_card_inv_K_eq M
  have hB := burnsideJ28_card_sH M hs hs1
  rw [natCard_subtype_eq] at hI hB ⊢
  have hsplit : (Finset.univ.filter fun x : G => x ∈ M.K ∧ x ∉ ruQ M.T ∧ x ^ 2 = 1) =
      (Finset.univ.filter fun x : G => IsConj M.z x ∧ x ∈ M.K ∧ x ∉ ruQ M.T) ∪
        (Finset.univ.filter fun x : G => IsConj s x ∧ x ∈ ruH M.T) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨hK, hQ, hx2⟩
      have hx1 : x ≠ 1 := by
        rintro rfl
        exact hQ (one_mem _)
      rcases hall x hx2 hx1 with hz | hsx
      · exact Or.inl ⟨hz, hK, hQ⟩
      · exact Or.inr ⟨hsx, M.K_le_H hK⟩
    · rintro (⟨hz, hK, hQ⟩ | ⟨hsx, hH⟩)
      · refine ⟨hK, hQ, ?_⟩
        obtain ⟨g, rfl⟩ := isConj_iff.mp hz
        rw [conj_pow, M.z_sq]
        group
      · obtain ⟨-, hK, hQ⟩ := M.lemma_J27_8 hs hs1 hH hsx
        refine ⟨hK, hQ, ?_⟩
        obtain ⟨g, rfl⟩ := isConj_iff.mp hsx
        rw [conj_pow, hs2]
        group
  have hdisj : Disjoint (Finset.univ.filter fun x : G => IsConj M.z x ∧ x ∈ M.K ∧ x ∉ ruQ M.T)
      (Finset.univ.filter fun x : G => IsConj s x ∧ x ∈ ruH M.T) :=
    Finset.disjoint_filter.mpr fun x _ h1 h2 => hzs (h1.1.trans h2.1.symm)
  rw [hsplit, Finset.card_union_of_disjoint hdisj, hB] at hI
  omega


theorem as_J_3_4 : J_3_4 := by
  exact burnsideJ28_J_3_4_of_KQ fun G _ _ M => burnsideJ28_card_zG_KQ M

end

@[expose] def J_3_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    (HRu T).index ≤ 5 * 7 * 13 * 1846 ∧ 5 * 7 * 13 * 1846 < (3 ^ 2 * 5 ^ 2 * 7 * 13) * 42

section

private theorem burnsideJ5_J_3_5_of_st (hSt : CFSG.Quasithin.RuType.StUniqueStatement) : J_3_5 := by
  intro G _ _ L V T h
  obtain ⟨M, -, hMT⟩ := CFSG.ASVolI.ChIJK.RuType.exists_ruDataM hSt h
  have hG := M.card_eq
  have hH : Nat.card (CFSG.ASVolI.ChIJK.HRu T) = 2 ^ 11 * 120 := by
    rw [h.HRu_eq_ruH, ← hMT]
    exact M.toRuData.card_H
  have hidx := Subgroup.card_mul_index (CFSG.ASVolI.ChIJK.HRu T)
  rw [hH, hG] at hidx
  refine ⟨?_, by norm_num⟩
  norm_num at hidx ⊢
  omega

theorem as_J_3_5 : J_3_5 :=
  burnsideJ5_J_3_5_of_st CFSG.Quasithin.RuType.stUnique

end

@[expose] def J_3_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V T : Subgroup G), RuType G L V T →
    ∀ z : G, Subgroup.zpowers z = ZRu T →
    ∀ B5 : Subgroup G, IsSylowIn 5 B5 (HRu T) →
      ∃ R : Subgroup G,
        Subgroup.normalizer (B5 : Set G) =
          (CFSG.generalizedFitting ↥(Subgroup.normalizer (B5 : Set G))).map
            (Subgroup.normalizer (B5 : Set G)).subtype ⊔ R ∧
        IsPOnePlusTwoGroup 5
          ↥((CFSG.generalizedFitting ↥(Subgroup.normalizer (B5 : Set G))).map
            (Subgroup.normalizer (B5 : Set G)).subtype) ∧
        IsSylowIn 5 ((CFSG.generalizedFitting ↥(Subgroup.normalizer (B5 : Set G))).map
            (Subgroup.normalizer (B5 : Set G)).subtype) ⊤ ∧
        Nonempty (↥R ≃* WreathedTwoGroup 2) ∧
        z ∈ R ∧ ∀ r ∈ R, r * z = z * r

section BurnsideJ6b

private theorem burnsideJ6b_eq_z {G : Type} [Group G] [Finite G]
    (M : CFSG.Quasithin.RuType.RuDataM G) {z : G}
    (hz : Subgroup.zpowers z = CFSG.Quasithin.RuType.ruZ M.T) : z = M.z := by
  have hzmem : z ∈ CFSG.Quasithin.RuType.ruZ M.T := by
    rw [← hz]
    exact Subgroup.mem_zpowers z
  rcases M.mem_Z_iff.mp hzmem with h1 | h1
  · exfalso
    have h2 := M.toRuData.card_Z
    rw [← hz, h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at h2
    omega
  · exact h1

private theorem burnsideJ6b_exists_gen {G : Type} [Group G] [Finite G] {H B : Subgroup G}
    (hH : Nat.card H = 2 ^ 11 * 120) (hB : CFSG.ASVolI.ChIJK.IsSylowIn 5 B H) :
    ∃ b : G, orderOf b = 5 ∧ Subgroup.zpowers b = B := by
  obtain ⟨hBH, hBp, hidx⟩ := hB
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨n, hn⟩ := hBp.exists_card_eq
  have h := Subgroup.index_mul_card (B.subgroupOf H)
  rw [CFSG.Quasithin.RuType.card_subgroupOf_of_le hBH, hn, hH] at h
  have hn1 : n = 1 := by
    rcases n with _ | _ | n
    · exfalso
      rw [pow_zero, mul_one] at h
      apply hidx
      rw [h]
      norm_num
    · rfl
    · exfalso
      have h25 : 25 ∣ (B.subgroupOf H).index * 5 ^ (n + 2) :=
        Dvd.dvd.mul_left (by
          rw [show (25 : ℕ) = 5 ^ 2 by norm_num]
          exact pow_dvd_pow 5 (by omega)) _
      rw [h] at h25
      norm_num at h25
  rw [hn1, pow_one] at hn
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := B) 5 (by rw [hn])
  refine ⟨(x : G), by rw [Subgroup.orderOf_coe, hx], ?_⟩
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr x.2) ?_
  rw [hn, Nat.card_zpowers, Subgroup.orderOf_coe, hx]

end BurnsideJ6b

section

theorem as_J_3_6 : J_3_6 := by
  intro G _ _ L V T h z hz B5 hB5
  obtain ⟨M, -, hMT⟩ := h.exists_ruDataM CFSG.Quasithin.RuType.stUnique
  have hH : Nat.card (CFSG.ASVolI.ChIJK.HRu T) = 2 ^ 11 * 120 := by
    rw [h.HRu_eq_ruH, ← hMT]
    exact M.toRuData.card_H
  have hzM : z = M.z := by
    refine burnsideJ6b_eq_z M ?_
    rw [hMT, ← CFSG.ASVolI.ChIJK.RuType.ZRu_eq_ruZ h]
    exact hz
  obtain ⟨b, hb5, rfl⟩ := burnsideJ6b_exists_gen hH hB5
  have hbH : b ∈ CFSG.Quasithin.RuType.ruH M.T := by
    rw [hMT, ← CFSG.ASVolI.ChIJK.RuType.HRu_eq_ruH h]
    exact hB5.1 (Subgroup.mem_zpowers b)
  obtain ⟨hF, ⟨hcard, hexp, hnc⟩, ⟨S, hS⟩, R, -, hPR, -, ⟨eR⟩, hzR, hzc⟩ :=
    CFSG.Quasithin.RuType.RuDataM.lemma_J36 (M := M) hbH hb5
  subst hzM
  refine ⟨R, ?_, ?_, ?_, ⟨eR⟩, hzR, hzc⟩
  · rw [hF]
    exact hPR.symm
  · rw [hF]
    refine ⟨hcard, ?_, ?_⟩
    · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      have hne : Nontrivial ↥(CFSG.Quasithin.RuType.P5 b) :=
        Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
      refine (Monoid.exponent_eq_prime_iff (by norm_num)).mpr fun g hg => orderOf_eq_prime ?_ hg
      exact Subtype.ext (by simpa using hexp g g.2)
    · by_contra hcon
      refine hnc fun x hx y hy => ?_
      by_contra hxy
      exact hcon ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy (congrArg Subtype.val h)⟩
  · rw [hF, ← hS]
    refine ⟨le_top, S.isPGroup', ?_⟩
    rw [show ((S : Subgroup G).subgroupOf ⊤).index = (S : Subgroup G).index from
      Subgroup.relIndex_top_right (S : Subgroup G)]
    exact S.not_dvd_index

end

end CFSG.ASVolI
