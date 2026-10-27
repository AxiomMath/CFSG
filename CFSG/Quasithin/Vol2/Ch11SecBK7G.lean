module

public import CFSG.Quasithin.Vol2.Ch11SecAKA18
public import CFSG.Quasithin.Vol2.Ch11SecBFacts24

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin Matrix
open CFSG.Open (pCoreOf)
open CFSG.Quasithin.Vol2.KGNat
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.ClassicalInvolution.ModelFacts.OddCover (qSp)
open scoped IsMulCommutative

namespace K7

section Tf

variable {K : Type} [Field K] {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}
  {Z : Subgroup W} {π : ↥(StatedSp 2 K) →* ↥H} {f : W → (Fin 2 ⊕ Fin 2 → K)}

theorem tf_conj (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) (g : StatedSp 2 K)
    {k : MulAut W} (hkZ : ∀ z ∈ Z, k z ∈ Z) (hkH : ∀ h ∈ H, k * h * k⁻¹ ∈ H)
    (γ : ↥(StatedSp 2 K)) : ∃ γ' : ↥(StatedSp 2 K), ∀ x,
      KA.tf hf g k (mat 2 K γ *ᵥ x) = mat 2 K γ' *ᵥ KA.tf hf g k x := by
  obtain ⟨δ, hδ⟩ : ∃ δ : ↥(StatedSp 2 K), π δ = ⟨_, hkH _ (π (g * γ * g⁻¹)).2⟩ := hf.onto _
  refine ⟨g⁻¹ * δ * g, fun x => ?_⟩
  obtain ⟨w, hw⟩ := hf.surj (mat 2 K g *ᵥ x)
  have hx : x = mat 2 K g⁻¹ *ᵥ f w := by rw [hw, mat_inv_mulVec]
  have e1 : mat 2 K γ *ᵥ x = mat 2 K g⁻¹ *ᵥ f (((π (g * γ * g⁻¹) : ↥H) : MulAut W) w) := by
    rw [hf.act4, conj_mulVec_sp, hx]
  have e2 : k (((π (g * γ * g⁻¹) : ↥H) : MulAut W) w) = ((π δ : ↥H) : MulAut W) (k w) := by
    rw [hδ]
    simp [MulAut.mul_apply]
  rw [e1, KA.tf_mk hf g hkZ, e2, hf.act4, hx, KA.tf_mk hf g hkZ, map_mul, map_mul,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mat_mulVec_inv]

theorem tf_pow (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) (g : StatedSp 2 K)
    {k : MulAut W} (hkZ : ∀ z ∈ Z, k z ∈ Z) (m : ℕ) (x : Fin 2 ⊕ Fin 2 → K) :
    KA.tf hf g (k ^ m) x = (KA.tf hf g k)^[m] x := by
  induction m with
  | zero =>
    rw [pow_zero, Function.iterate_zero, id_eq, KA.tf, MulAut.one_apply,
      Function.surjInv_eq hf.surj, mat_inv_mulVec]
  | succ m ih => rw [pow_succ', KA.tf_mul hf g hkZ, ih, Function.iterate_succ_apply']

end Tf

variable {G : Type} [Group G] {L V X T V₁ V₂ : Subgroup G} {n : ℕ}

theorem lOf_sup_le (hfl : Flag24 L V X T V₁ V₂ n) :
    LOf L V₂ ⊔ T ≤ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (L : Set G) ⊓
      Subgroup.normalizer (V₂ : Set G) ⊓ Subgroup.normalizer (LOf L V₂ : Set G) := by
  have h : LOf L V₂ ≤ L ⊓ Subgroup.normalizer (V₂ : Set G) := perfectCore_le _
  have hT : T ≤ Subgroup.normalizer ((L ⊓ Subgroup.normalizer (V₂ : Set G) : Subgroup G) :
      Set G) :=
    (le_inf hfl.T_le_L (hfl.T_le_V₂.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  refine sup_le (le_inf (le_inf (le_inf ?_ ?_) ?_) Subgroup.le_normalizer)
    (le_inf (le_inf (le_inf hfl.T_le_V hfl.T_le_L) hfl.T_le_V₂)
      (hT.trans (normalizer_le_normalizer_perfectCore _)))
  · exact h.trans (inf_le_left.trans hfl.le_normalizer)
  · exact h.trans (inf_le_left.trans Subgroup.le_normalizer)
  · exact h.trans inf_le_right

theorem r2_le (hfl : Flag24 L V X T V₁ V₂ n) :
    pCoreOf 2 (LOf L V₂ ⊔ T) ≤ Subgroup.normalizer (V : Set G) ⊓
      Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V₂ : Set G) ⊓
      Subgroup.normalizer (LOf L V₂ : Set G) :=
  (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (lOf_sup_le hfl)

theorem r2_le_normalizer (hfl : Flag24 L V X T V₁ V₂ n) {r : G}
    (hr : r ∈ pCoreOf 2 (LOf L V₂ ⊔ T)) : r ∈ Subgroup.normalizer (V : Set G) :=
  (r2_le hfl hr).1.1.1

theorem comm_mem_pCoreOf [Finite G] (hfl : Flag24 L V X T V₁ V₂ n) {r l : G}
    (hr : r ∈ pCoreOf 2 (LOf L V₂ ⊔ T)) (hl : l ∈ LOf L V₂) :
    r * l * r⁻¹ * l⁻¹ ∈ pCoreOf 2 (LOf L V₂) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 (LOf L V₂ ⊔ T) with hR
  have hNR : LOf L V₂ ⊔ T ≤ Subgroup.normalizer (R : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hle : R ⊓ LOf L V₂ ≤ pCoreOf 2 (LOf L V₂) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left)
    exact (le_inf (le_sup_left.trans hNR) Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  refine hle ⟨?_, ?_⟩
  · have h1 : l * r⁻¹ * l⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp (hNR (le_sup_left (α := Subgroup G) hl)) _).mp
        (R.inv_mem hr)
    have := R.mul_mem hr h1
    rwa [← mul_assoc, ← mul_assoc] at this
  · have h1 : r * l * r⁻¹ ∈ LOf L V₂ :=
      (Subgroup.mem_normalizer_iff.mp (r2_le hfl hr).2 _).mp hl
    exact (LOf L V₂).mul_mem h1 ((LOf L V₂).inv_mem hl)

end K7

end CFSG.Quasithin.Vol2.Ch11.SecB
