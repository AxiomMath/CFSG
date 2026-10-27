module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aCartD
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL3
public import CFSG.Quasithin.Vol2.Ch11SecQ9aShA

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

open CFSG.Open CFSG.QuasithinUnique.Setup.X6
open scoped Pointwise

variable {Q : Type} [Group Q]

theorem card_sup_eq_mul [Finite Q] {N H : Subgroup Q}
    (hHN : H ≤ Subgroup.normalizer (N : Set Q)) (hd : N ⊓ H = ⊥) :
    Nat.card ↥(H ⊔ N) = Nat.card ↥N * Nat.card ↥H := by
  have hc : ((H ⊔ N : Subgroup Q) : Set Q) = (H : Set Q) * (N : Set Q) :=
    Subgroup.coe_mul_of_left_le_normalizer_right H N hHN
  have h1 : Nat.card ↥(H ⊔ N) = Nat.card ↥((H : Set Q) * (N : Set Q)) := by
    rw [← hc]
    rfl
  rw [h1, Subgroup.card_mul_eq_card_subgroup_mul_card_quotient, Nat.card_image_of_injOn]
  · rfl
  · intro a ha b hb hab
    have hab' : a⁻¹ * b ∈ N ⊓ H := ⟨QuotientGroup.eq.mp hab, H.mul_mem (H.inv_mem ha) hb⟩
    rw [hd, Subgroup.mem_bot] at hab'
    exact inv_mul_eq_one.mp hab'

structure BorelPair (S : Subgroup Q) (B : Fin 2 → Subgroup Q) : Prop where
  parab : ParabPair S B
  inf_le : Subgroup.normalizer (B 0 : Set Q) ⊓ Subgroup.normalizer (B 1 : Set Q) ≤
    Subgroup.normalizer (S : Set Q)
  card : Nat.card ↥(Subgroup.normalizer (S : Set Q)) = Nat.card ↥S * 9

theorem BorelPair.borelShape {S : Subgroup Q} {B : Fin 2 → Subgroup Q} (h : BorelPair S B)
    {B₁ B₂ : Subgroup Q} (hne : B₁ ≠ B₂) (h₁ : IsL24Sub S B₁) (h₂ : IsL24Sub S B₂) :
    Subgroup.normalizer (B₁ : Set Q) ⊓ Subgroup.normalizer (B₂ : Set Q) ≤
        Subgroup.normalizer (S : Set Q) ∧
      Nat.card ↥(Subgroup.normalizer (S : Set Q)) = Nat.card ↥S * 9 := by
  refine ⟨?_, h.card⟩
  have ht : ∀ X Y : Subgroup Q, X ≠ Y → IsL24Sub S X → IsL24Sub S Y → X ≠ ⊤ := by
    intro X Y hXY hX hY hXt
    subst hXt
    exact h.parab.top_not Y hY (Ne.symm hXY) hX
  have hnt : ∀ X : Subgroup Q, IsL24Sub S X → X ≠ ⊤ → X = B 0 ∨ X = B 1 := by
    intro X hX hXt
    rcases h.parab.eq_or_eq_of_isL24Sub hX with e | e | e
    · exact Or.inl e
    · exact Or.inr e
    · exact absurd e hXt
  have e₁ := hnt B₁ h₁ (ht B₁ B₂ hne h₁ h₂)
  have e₂ := hnt B₂ h₂ (ht B₂ B₁ (Ne.symm hne) h₂ h₁)
  rcases e₁ with rfl | rfl <;> rcases e₂ with rfl | rfl
  · exact absurd rfl hne
  · exact h.inf_le
  · rw [inf_comm]
    exact h.inf_le
  · exact absurd rfl hne

theorem borelPair_of_residual [Finite Q] {S : Subgroup Q}
    (hS : QuasithinUnique.IsSylowTwoOf S ⊤) {P : Fin 2 → Subgroup Q}
    (hres : ResidualOvergroupsAt Q S P) (hB : ∀ j, dInf (P j) ≠ ⊥)
    (hN : ∀ X : Subgroup Q, X.Normal → ⁅X, X⁆ = X → X ≠ ⊥ → X = ⊤)
    (htop : ∀ X : Subgroup Q, IsL24Sub S X → X ≠ ⊤ → ¬ IsL24Sub S ⊤)
    (hinf : P 0 ⊓ P 1 ≤ Subgroup.normalizer (S : Set Q))
    (hcard : Nat.card ↥(Subgroup.normalizer (S : Set Q)) = Nat.card ↥S * 9) :
    BorelPair S (fun j => dInf (P j)) := by
  have hpp := parabPair_of_residual_of hS hres hB hN htop
  have hNP : ∀ j, Subgroup.normalizer (dInf (P j) : Set Q) = P j := by
    intro j
    have hcov : P j ⋖ ⊤ := (hres.2.2.1 (P j) (hres.2.1 j)).mpr ⟨j, rfl⟩
    have hle : P j ≤ Subgroup.normalizer (dInf (P j) : Set Q) := by
      rw [CFSG.QuasithinUnique.Vol2Native.A312L.dInf_eq_perfectCore]
      exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore _)
    rcases hcov.eq_or_eq hle le_top with e | e
    · exact e
    · exact absurd (hN _ (Subgroup.normalizer_eq_top_iff.mp e) (hpp.perfect j) (hB j))
        (hpp.ne_top j)
  refine ⟨hpp, ?_, hcard⟩
  show Subgroup.normalizer (dInf (P 0) : Set Q) ⊓ Subgroup.normalizer (dInf (P 1) : Set Q) ≤ _
  rw [hNP 0, hNP 1]
  exact hinf

theorem top_not_of_card [Finite Q] (hQ : Nat.card Q = 60480) {S : Subgroup Q} :
    ∀ X : Subgroup Q, IsL24Sub S X → X ≠ ⊤ → ¬ IsL24Sub S ⊤ := by
  intro X _ _ htop
  obtain ⟨-, -, -, F, _, _, hF, ⟨e⟩⟩ := htop
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := (CFSG.pCore 2 ↥(⊤ : Subgroup Q)).card_eq_card_quotient_mul_card_subgroup
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp
    (CFSG.pCore_isPGroup : IsPGroup 2 ↥(CFSG.pCore 2 ↥(⊤ : Subgroup Q)))
  rw [Nat.card_congr e.toEquiv, card_SL2_four hF, Subgroup.card_top, hQ, ha] at h1
  have h2 : 2 ^ a = 1008 := by omega
  have ha' : a < 10 := by
    by_contra hc
    have h3 : 2 ^ 10 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hc)
    norm_num at h3
    omega
  interval_cases a <;> norm_num at h2

theorem eq_top_of_normal_of_equiv {G : Type*} [Group G] (e : Q ≃* G)
    (hG : ∀ Y : Subgroup G, Y.Normal → ⁅Y, Y⁆ = Y → Y ≠ ⊥ → Y = ⊤)
    {X : Subgroup Q} (hXn : X.Normal) (hXp : ⁅X, X⁆ = X) (hX1 : X ≠ ⊥) : X = ⊤ := by
  have h := hG (X.map e.toMonoidHom) (hXn.map e.toMonoidHom e.surjective)
    (by rw [← Subgroup.map_commutator, hXp])
    (fun h => hX1 ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h))
  rw [← Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at h
  exact Subgroup.map_injective e.injective h

section SL3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.ClassicalInvolution.ModelFacts.OddCover

variable {K : Type} [Field K]

theorem eq_top_of_normal_SL3 {X : Subgroup (SpecialLinearGroup (Fin 3) K)} (hXn : X.Normal)
    (hXp : ⁅X, X⁆ = X) (hX1 : X ≠ ⊥) : X = ⊤ := by
  have hq : CFSG.IsQuasisimple (SpecialLinearGroup (Fin 3) K) :=
    CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 K le_rfl
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hXn with h | h
  · exact h
  · refine absurd ?_ hX1
    rw [← hXp]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (h.trans (Subgroup.center_le_centralizer _))

theorem embSL_range_ne_bot [CharP K 2] (hK4 : ∃ s : Finset K, s.card = 4) (j : Fin 2) :
    (embSL (K := K) j).range ≠ ⊥ := by
  intro h
  obtain ⟨a, b, hab⟩ := sl2_nonabelian (K := K) hK4
  have hinj : Function.Injective (embSL (K := K) j) := fun A B e => by
    have := congrArg (fun M : SpecialLinearGroup (Fin 3) K =>
      blkAt (1 - (j : ℕ)) 2 (q3_blk_le j) (M : Matrix (Fin 3) (Fin 3) K)) e
    simp only [coe_embSL, blkAt_embMat] at this
    exact Subtype.ext this
  have h1 : embSL j a = embSL j 1 := by
    have : embSL j a ∈ (embSL (K := K) j).range := ⟨a, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    rw [this, map_one]
  rw [hinj h1, one_mul, mul_one] at hab
  exact hab rfl

variable [Finite K]

theorem card_SL3_four (hK : Nat.card K = 4) :
    Nat.card (SpecialLinearGroup (Fin 3) K) = 60480 := by
  rw [card_SL_eq (by norm_num), hK]
  decide

theorem card_upperTriangular_three (hK : Nat.card K = 4) :
    Nat.card ↥(upperTriangular 3 K) = Nat.card ↥(unitriangular 3 K) * 9 := by
  have hT : diagSL 3 K ≤
      Subgroup.normalizer (unitriangular 3 K : Set (SpecialLinearGroup (Fin 3) K)) := by
    rw [normalizer_unitriangular]
    exact diagSL_le_upperTriangular
  have hB : diagSL 3 K ⊔ unitriangular 3 K = upperTriangular 3 K :=
    le_antisymm (sup_le diagSL_le_upperTriangular (unitriangular_le_upperTriangular 3 K))
      (upperTriangular_le_sup_diagSL.trans (sup_comm _ _).le)
  have hu : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  rw [← hB, card_sup_eq_mul hT unitriangular_inf_diagSL, diagSL_eq_torus3,
    ← Nat.card_congr (MonoidHom.ofInjective (tSL_injective (K := K))).toEquiv, Nat.card_prod, hu]

theorem exists_borelPair_sl3 [Finite Q] (hK : Nat.card K = 2 ^ 2)
    (e : Q ≃* SpecialLinearGroup (Fin 3) K) {S : Subgroup Q}
    (hS : QuasithinUnique.IsSylowTwoOf S ⊤) : ∃ B : Fin 2 → Subgroup Q, BorelPair S B := by
  have hK' : Nat.card K = 4 := by rw [hK]; norm_num
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by norm_num) hK
  have hK4 : ∃ s : Finset K, s.card = 4 := exists_finset_card_four (by omega)
  obtain ⟨P0, hP0⟩ := exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
  have hU₀ : QuasithinUnique.IsSylowTwoOf (unitriangular 3 K) ⊤ :=
    hP0 ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P0
  have h₀ := linear_three_residual_of_cover ⟨2, hK⟩ (MonoidHom.id _) Function.surjective_id
    (by rw [MonoidHom.ker_id]; exact bot_le)
  simp only [Subgroup.map_id] at h₀
  obtain ⟨φ, hφ, hres⟩ := h₀.exists_iso_of_isSylow e hU₀ hS
  have hS' : S = (unitriangular 3 K).map φ.symm.toMonoidHom := by
    rw [← hφ]
    ext x
    simp
  have hB : ∀ j, dInf ((Q3 K j).map φ.symm.toMonoidHom) ≠ ⊥ := fun j h => by
    apply embSL_range_ne_bot hK4 j
    have hX : ((embSL (K := K) j).range).map φ.symm.toMonoidHom ≤
        dInf ((Q3 K j).map φ.symm.toMonoidHom) :=
      le_dInf_of_perfect (map_isPerfect (Subgroup.isPerfect_iff.mpr (embSL_range_perfect hK4 j)) _)
        (Subgroup.map_mono (by rintro _ ⟨A, rfl⟩; exact embSL_mem_Q3 j A))
    rw [h] at hX
    exact (Subgroup.map_eq_bot_iff_of_injective _ φ.symm.injective).mp (le_bot_iff.mp hX)
  have hN : ∀ X : Subgroup Q, X.Normal → ⁅X, X⁆ = X → X ≠ ⊥ → X = ⊤ := fun X hXn hXp hX1 =>
    eq_top_of_normal_of_equiv e (fun Y hYn hYp hY1 => eq_top_of_normal_SL3 hYn hYp hY1) hXn hXp
      hX1
  have hcardQ : Nat.card Q = 60480 := by rw [Nat.card_congr e.toEquiv, card_SL3_four hK']
  have hinf : (Q3 K 0).map φ.symm.toMonoidHom ⊓ (Q3 K 1).map φ.symm.toMonoidHom ≤
      Subgroup.normalizer (S : Set Q) := by
    rw [← Subgroup.map_inf_eq _ _ _ φ.symm.injective, inf_eq_of_covBy (covBy_Q3 0) (covBy_Q3 1)
      Q3_ne, hS', ← Subgroup.map_equiv_normalizer_eq, normalizer_unitriangular]
  have hcard : Nat.card ↥(Subgroup.normalizer (S : Set Q)) = Nat.card ↥S * 9 := by
    rw [hS', ← Subgroup.map_equiv_normalizer_eq, normalizer_unitriangular,
      Subgroup.card_map_of_injective φ.symm.injective,
      Subgroup.card_map_of_injective φ.symm.injective, card_upperTriangular_three hK']
  exact ⟨_, borelPair_of_residual hS hres hB hN (top_not_of_card hcardQ) hinf hcard⟩

end SL3

end CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
