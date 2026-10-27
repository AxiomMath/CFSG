module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4GCover
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4Facts
public import CFSG.Quasithin.EmptyFaithful.S14610Hat6
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4GRank

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S15223P4.G

variable {G : Type} [Group G] [Finite G]

variable {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

omit [Finite G] in
theorem oTwoZIn_le_inf
    (hC : X ⊓ Subgroup.centralizer (P4V M I X : Set G) = pCoreOf 2 X)
    (hO2 : pCoreOf 2 X ≤ M ⊓ I ⊓ X)
    (hpar : IsMaxParabolic2 (autOn X (P4V M I X)) (autOn (M ⊓ I ⊓ X) (P4V M I X))) :
    oTwoZIn X ≤ M ⊓ I ⊓ X := by
  intro z hz
  obtain ⟨hzX, hcomm⟩ := mem_oTwoZIn_iff_commutator.mp hz
  have hXN := le_normalizer_V X M I
  have hker : pCoreOf 2 X ≤ Subgroup.centralizer (P4V M I X : Set G) := hC ▸ inf_le_right
  have hzN := hXN hzX
  obtain ⟨-, S₀, hS₀, hnorm⟩ := hpar.1
  have hζL : conjAct (P4V M I X) ⟨z, hzN⟩ ∈ autOn X (P4V M I X) :=
    mem_autOn_iff_exists.mpr ⟨z, hzN, hzX, rfl⟩
  have hcent : ∀ a ∈ autOn X (P4V M I X),
      conjAct (P4V M I X) ⟨z, hzN⟩ * a * (conjAct (P4V M I X) ⟨z, hzN⟩)⁻¹ = a := by
    intro a ha
    obtain ⟨y, hyN, hyX, rfl⟩ := mem_autOn_iff_exists.mp ha
    have hcC : z * y * z⁻¹ * y⁻¹ ∈ Subgroup.centralizer (P4V M I X : Set G) := hker (hcomm y hyX)
    have hcN : z * y * z⁻¹ * y⁻¹ ∈ Subgroup.normalizer (P4V M I X : Set G) :=
      Subgroup.centralizer_le_normalizer (P4V M I X : Set G) hcC
    have h1 : conjAct (P4V M I X) ⟨z * y * z⁻¹ * y⁻¹, hcN⟩ = 1 := A4.conjAct_eq_one_iff.mpr hcC
    have h2 : (⟨z * y * z⁻¹ * y⁻¹, hcN⟩ : ↥(Subgroup.normalizer (P4V M I X : Set G))) =
        ⟨z, hzN⟩ * ⟨y, hyN⟩ * ⟨z, hzN⟩⁻¹ * ⟨y, hyN⟩⁻¹ := rfl
    rw [h2, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    exact mul_inv_eq_one.mp h1
  have hζnorm : conjAct (P4V M I X) ⟨z, hzN⟩ ∈
      Subgroup.normalizer (S₀ : Set (MulAut ↥(P4V M I X))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hcent h (hS₀.le hh)]
      exact hh
    · intro hh
      have hhL : h ∈ autOn X (P4V M I X) := by
        have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hζL) (hS₀.le hh)) hζL
        convert this using 1
        group
      rwa [hcent h hhL] at hh
  obtain ⟨m, hmN, hmMX, hmζ⟩ := mem_autOn_iff_exists.mp
    (hnorm (Subgroup.mem_inf.mpr ⟨hζL, hζnorm⟩))
  have h3 : conjAct (P4V M I X) (⟨z, hzN⟩⁻¹ * ⟨m, hmN⟩) = 1 := by
    rw [map_mul, map_inv, hmζ]
    group
  have h4 : z⁻¹ * m ∈ Subgroup.centralizer (P4V M I X : Set G) := A4.conjAct_eq_one_iff.mp h3
  have h5 : z⁻¹ * m ∈ pCoreOf 2 X := by
    rw [← hC]
    exact ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hzX) hmMX.2, h4⟩
  have h6 : z = m * (z⁻¹ * m)⁻¹ := by group
  rw [h6]
  exact Subgroup.mul_mem _ hmMX (Subgroup.inv_mem _ (hO2 h5))

theorem exists_central_order_three {F : Type} [Field F] [Fintype F] {n : ℕ}
    (hF : Fintype.card F = 2 ^ n) (hn : Even n) :
    ∃ σ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F),
      σ ∈ Subgroup.center ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) ∧ orderOf σ = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Nat.card Fˣ := by
    rw [Nat.card_units, Nat.card_eq_fintype_card, hF]
    obtain ⟨k, rfl⟩ := hn
    have := Nat.pow_sub_one_dvd_pow_sub_one (x := 2) (m := 2) (k := k + k) (by omega)
    simpa using this
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 h3
  have hω3 : ω ^ 3 = 1 := hω ▸ pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := fun h => by simp [h] at hω
  let s : GL (Fin 3) F := (Matrix.GeneralLinearGroup.scalar (Fin 3) : Fˣ →* GL (Fin 3) F) ω
  have hdet : (s : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    have h1 : (s : Matrix (Fin 3) (Fin 3) F).det = (ω : F) ^ 3 := by
      simp [s, Matrix.GeneralLinearGroup.scalar]
    rw [h1, ← Units.val_pow_eq_pow_val, hω3, Units.val_one]
  have hs : s ∈ CFSG.Assembly.LowTwoRank.StatedSL 3 F := Subgroup.subset_closure hdet
  have hcen : s ∈ Subgroup.center (GL (Fin 3) F) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨ω, rfl⟩
  refine ⟨⟨s, hs⟩, ?_, ?_⟩
  · rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp hcen g.1)
  · have h3' : (⟨s, hs⟩ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) ^ 3 = 1 := by
      apply Subtype.ext
      change s ^ 3 = 1
      simp only [s, ← map_pow, hω3, map_one]
    have h1' : (⟨s, hs⟩ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) ≠ 1 := by
      intro h
      have h2 : s = 1 := congrArg Subtype.val h
      have h4 := congrArg (fun g : GL (Fin 3) F => ((g : Matrix (Fin 3) (Fin 3) F) 0 0)) h2
      simp [s, Matrix.GeneralLinearGroup.scalar] at h4
      exact hω1 h4
    exact orderOf_eq_prime h3' h1'

theorem exists_orderOf_three_mem_oTwoZIn
    (hC : X ⊓ Subgroup.centralizer (P4V M I X : Set G) = pCoreOf 2 X)
    {n : ℕ} {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ n) (hn : Even n)
    (e : Nonempty (↥(autOn X (P4V M I X)) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))) :
    ∃ z : G, z ∈ oTwoZIn X ∧ orderOf z = 3 := by
  obtain ⟨φ⟩ := e
  obtain ⟨σ, hσc, hσ3⟩ := exists_central_order_three hF hn
  have hXN := le_normalizer_V X M I
  have hker : pCoreOf 2 X ≤ Subgroup.centralizer (P4V M I X : Set G) := hC ▸ inf_le_right
  set ζ0 : ↥(autOn X (P4V M I X)) := φ.symm σ with hζ0
  have hζ0c : ∀ a : ↥(autOn X (P4V M I X)), ζ0 * a = a * ζ0 := by
    intro a
    have h := Subgroup.mem_center_iff.mp hσc (φ a)
    apply φ.injective
    rw [map_mul, map_mul, hζ0, MulEquiv.apply_symm_apply]
    exact h.symm
  have hζ03 : orderOf ζ0 = 3 := by rw [hζ0, MulEquiv.orderOf_eq]; exact hσ3
  obtain ⟨x, hxN, hxX, hxa⟩ := mem_autOn_iff_exists.mp ζ0.2
  have hxZ : x ∈ oTwoZIn X := by
    refine mem_oTwoZIn_iff_commutator.mpr ⟨hxX, fun w hw => ?_⟩
    have hwN := hXN hw
    have hwa : conjAct (P4V M I X) ⟨w, hwN⟩ ∈ autOn X (P4V M I X) :=
      mem_autOn_iff_exists.mpr ⟨w, hwN, hw, rfl⟩
    have hcomm := congrArg Subtype.val (hζ0c ⟨_, hwa⟩)
    have hcN : x * w * x⁻¹ * w⁻¹ ∈ Subgroup.normalizer (P4V M I X : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hxN hwN) (Subgroup.inv_mem _ hxN))
        (Subgroup.inv_mem _ hwN)
    have h1 : conjAct (P4V M I X) ⟨x * w * x⁻¹ * w⁻¹, hcN⟩ = 1 := by
      have h2 : (⟨x * w * x⁻¹ * w⁻¹, hcN⟩ : ↥(Subgroup.normalizer (P4V M I X : Set G))) =
          ⟨x, hxN⟩ * ⟨w, hwN⟩ * ⟨x, hxN⟩⁻¹ * ⟨w, hwN⟩⁻¹ := rfl
      rw [h2, map_mul, map_mul, map_mul, map_inv, map_inv, hxa]
      have h3 : (ζ0 : MulAut ↥(P4V M I X)) * conjAct (P4V M I X) ⟨w, hwN⟩ =
          conjAct (P4V M I X) ⟨w, hwN⟩ * (ζ0 : MulAut ↥(P4V M I X)) := hcomm
      rw [h3]
      group
    rw [← hC]
    exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hxX hw)
      (Subgroup.inv_mem _ hxX)) (Subgroup.inv_mem _ hw), A4.conjAct_eq_one_iff.mp h1⟩
  have hdvd : 3 ∣ orderOf x := by
    have h1 : orderOf (conjAct (P4V M I X) ⟨x, hxN⟩) ∣ orderOf (⟨x, hxN⟩ :
        ↥(Subgroup.normalizer (P4V M I X : Set G))) := orderOf_map_dvd _ _
    rw [hxa, Subgroup.orderOf_coe, hζ03, ← Subgroup.orderOf_coe] at h1
    exact h1
  exact ⟨x ^ (orderOf x / 3), Subgroup.pow_mem _ hxZ _,
    orderOf_pow_orderOf_div (orderOf_pos x).ne' hdvd⟩

theorem false_of_even (hcover : AsA36NoOddCover) (c : P4Ctx T Mc M H B₀ I X)
    {n : ℕ} {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ n) (hn : Even n)
    (e : Nonempty (↥(autOn X (P4V M I X)) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)))
    (hpar : IsMaxParabolic2 (autOn X (P4V M I X)) (autOn (M ⊓ I ⊓ X) (P4V M I X)))
    (hMS : IsMSPair (X ⊔ P4R M I) (P4R M I)) : False := by
  have hC := inf_centralizer_eq_pCoreOf hcover c hF e
  have hZM := oTwoZIn_le_inf hC (pCoreOf_le_inf c hMS) hpar
  obtain ⟨z, hzZ, hz3⟩ := exists_orderOf_three_mem_oTwoZIn hC hF hn e
  obtain ⟨E, hEK, hE, hE9⟩ := c.exists_E9
  have h3 : 3 ∣ Nat.card (oTwoZIn X) := by
    have h1 : orderOf (⟨z, hzZ⟩ : ↥(oTwoZIn X)) ∣ Nat.card ↥(oTwoZIn X) := orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk, hz3] at h1
  have hne := exists_mem_inf_of_rank (pRank_three_le_two_of_hyp c)
    ((oTwoZIn_le_self X).trans c.X_le_I) (hEK.trans c.K_le_I)
    (hEK.trans (c.K_norm.trans (normalizer_le_normalizer_oTwoZIn X))) hE hE9 h3
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have huT : u ∈ T := by
    rw [c.inputs.hN.eq_inf]
    exact ⟨(hZM hu.2).1.1, oTwoUpper_le H (hEK hu.1)⟩
  have hu3 : u ^ 3 = 1 := hE.2 u hu.1
  exact hu1 (Subtype.ext (eq_one_of_isPGroup_two_of_pow_three c.setting.qtfe.sylow.1 huT hu3))

end S15223P4.G

end CFSG.Quasithin
