module

public import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusUnitaryVec
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates

public section

namespace CFSG.StandardType.SympMinus

open Matrix CFSG.StandardType.TorC CFSG.StandardType.SpJoin
open CFSG.ClassicalInvolution.Models.SymplecticPairs (gram mulVec_single_one_apply)
open CFSG.Open (StatedSp)

variable {K : Type} [Field K] {m : ℕ}

theorem smu_eq_of_suppIn_singleton {x : Fin m} {w : Fin m ⊕ Fin m → K} (hw : SmuSuppIn {x} w) :
    w = w (Sum.inl x) • (Pi.single (Sum.inl x) (1 : K) : Fin m ⊕ Fin m → K) +
      w (Sum.inr x) • (Pi.single (Sum.inr x) (1 : K) : Fin m ⊕ Fin m → K) := by
  funext r
  rcases r with y | y
  · by_cases hy : y = x
    · subst hy
      simp
    · have h0 : w (Sum.inl y) = 0 := hw _ (by simpa [WitSpNs.plane] using hy)
      simp [h0, Pi.single_apply, hy]
  · by_cases hy : y = x
    · subst hy
      simp
    · have h0 : w (Sum.inr y) = 0 := hw _ (by simpa [WitSpNs.plane] using hy)
      simp [h0, Pi.single_apply, hy]

theorem SmuOffFix.mulVec_single_card_le_one {S : Finset (Fin m)} (hS : S.card ≤ 1)
    {j : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K}
    (hjs : jᵀ * gram K m * j = gram K m) (hj : SmuOffFix S j) (r : Fin m ⊕ Fin m) :
    j *ᵥ Pi.single r 1 =
      blk j (WitSpNs.plane r) (WitSpNs.plane r) 0 (WitSpNs.side r) •
          (Pi.single (Sum.inl (WitSpNs.plane r)) (1 : K) : Fin m ⊕ Fin m → K) +
        blk j (WitSpNs.plane r) (WitSpNs.plane r) 1 (WitSpNs.side r) •
          (Pi.single (Sum.inr (WitSpNs.plane r)) (1 : K) : Fin m ⊕ Fin m → K) := by
  by_cases hx : WitSpNs.plane r ∈ S
  · have hSx : S = {WitSpNs.plane r} := by
      have h1 : S.card = 1 := le_antisymm hS (Finset.card_pos.mpr ⟨_, hx⟩)
      obtain ⟨y, hy⟩ := Finset.card_eq_one.mp h1
      rw [hy] at hx ⊢
      rw [Finset.mem_singleton] at hx
      rw [hx]
    have hw : SmuSuppIn {WitSpNs.plane r} (j *ᵥ Pi.single r (1 : K)) := by
      rw [← hSx]
      exact hj.suppIn_mulVec hjs (smu_suppIn_single hx)
    refine (smu_eq_of_suppIn_singleton hw).trans ?_
    rw [mulVec_single_one_apply, mulVec_single_one_apply]
    simp only [blk, Matrix.of_apply, smu_coord_side_plane]
    simp [WitSpNs.coord]
  · rw [hj.mulVec_single r hx]
    have hb : blk j (WitSpNs.plane r) (WitSpNs.plane r) = 1 := by
      rw [hj _ hx (WitSpNs.plane r)]
      simp
    rw [hb]
    rcases r with p' | p'
    · simp [Matrix.one_apply, WitSpNs.plane, WitSpNs.side]
    · simp [Matrix.one_apply, WitSpNs.plane, WitSpNs.side]

theorem SmuOffFix.eq_planeMat_of_card_le_one {S : Finset (Fin m)} (hS : S.card ≤ 1)
    {j : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K}
    (hjs : jᵀ * gram K m * j = gram K m) (hj : SmuOffFix S j) :
    j = WitSpNs.planeMat (fun x => blk j x x) :=
  WitSpNs.eq_planeMat_of_mulVec
    (fun x => SmuOffFix.mulVec_single_card_le_one hS hjs hj (Sum.inl x))
    (fun x => SmuOffFix.mulVec_single_card_le_one hS hjs hj (Sum.inr x))

theorem commute_of_commute_of_trace_ne_zero_gl [Finite K] [CharP K 2]
    {Z : SpecialLinearGroup (Fin 2) K} (htr : (Z : Matrix (Fin 2) (Fin 2) K).trace ≠ 0)
    {B B' : Matrix (Fin 2) (Fin 2) K} (hB : B.det ≠ 0) (hB' : B'.det ≠ 0)
    (h : B * (Z : Matrix (Fin 2) (Fin 2) K) = (Z : Matrix (Fin 2) (Fin 2) K) * B)
    (h' : B' * (Z : Matrix (Fin 2) (Fin 2) K) = (Z : Matrix (Fin 2) (Fin 2) K) * B') :
    B * B' = B' * B := by
  obtain ⟨δ, hδ⟩ := isSquare_of_charTwo' B.det
  obtain ⟨δ', hδ'⟩ := isSquare_of_charTwo' B'.det
  have hδ0 : δ ≠ 0 := fun h0 => hB (by rw [hδ, h0, mul_zero])
  have hδ0' : δ' ≠ 0 := fun h0 => hB' (by rw [hδ', h0, mul_zero])
  let N : SpecialLinearGroup (Fin 2) K :=
    ⟨δ⁻¹ • B, by rw [Matrix.det_smul, Fintype.card_fin, hδ]; field_simp⟩
  let N' : SpecialLinearGroup (Fin 2) K :=
    ⟨δ'⁻¹ • B', by rw [Matrix.det_smul, Fintype.card_fin, hδ']; field_simp⟩
  have hN : N * Z = Z * N := by
    apply Subtype.ext
    show (δ⁻¹ • B) * (Z : Matrix (Fin 2) (Fin 2) K) = (Z : Matrix (Fin 2) (Fin 2) K) * (δ⁻¹ • B)
    rw [Matrix.smul_mul, Matrix.mul_smul, h]
  have hN' : N' * Z = Z * N' := by
    apply Subtype.ext
    show (δ'⁻¹ • B') * (Z : Matrix (Fin 2) (Fin 2) K) = (Z : Matrix (Fin 2) (Fin 2) K) * (δ'⁻¹ • B')
    rw [Matrix.smul_mul, Matrix.mul_smul, h']
  have h1 := commute_of_commute_of_trace_ne_zero htr hN hN'
  have h2 : (δ⁻¹ • B) * (δ'⁻¹ • B') = (δ'⁻¹ • B') * (δ⁻¹ • B) :=
    congrArg (fun X : SpecialLinearGroup (Fin 2) K => (X : Matrix (Fin 2) (Fin 2) K)) h1
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul] at h2
  rw [mul_comm δ'⁻¹ δ⁻¹] at h2
  exact smul_right_injective _ (mul_ne_zero (inv_ne_zero hδ0) (inv_ne_zero hδ0')) h2

theorem card_ge_two_of_component [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    (f₀ : Fin m → Multiplicative (ZMod p)) {c : Multiplicative (ZMod p)} (hc : c ≠ 1)
    {J₀ : Subgroup (StatedSp m K)}
    (hJ : CFSG.Assembly.IsComponentOf J₀
      (Subgroup.centralizer ({spPlaneTorus m ζ f₀} : Set (StatedSp m K))))
    {S : Finset (Fin m)} (hS : ∀ i, i ∈ S ↔ f₀ i = c ∨ f₀ i = c⁻¹)
    (hsupp : ∀ j ∈ J₀, SmuOffFix S
      (((j : StatedSp m K) : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)) :
    2 ≤ S.card := by
  classical
  by_contra hlt
  have hS1 : S.card ≤ 1 := by omega
  let M : ↥(StatedSp m K) → Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K :=
    fun j => ((j : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
  have hblk : ∀ j ∈ J₀, M j = WitSpNs.planeMat (fun x => blk (M j) x x) := fun j hj =>
    SmuOffFix.eq_planeMat_of_card_le_one hS1 (CFSG.Open.StatedAPI.mem_statedSp_iff.mp j.2)
      (hsupp j hj)
  have hMg : M (spPlaneTorus m ζ f₀) = WitSpNs.planeMat
      (fun x => ((ζ (f₀ x) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) :=
    coe_spPlaneTorus m ζ f₀
  have hmul : ∀ j j' : ↥(StatedSp m K), M (j * j') = M j * M j' := fun j j' => rfl
  have hdet : ∀ j ∈ J₀, ∀ x, (blk (M j) x x).det ≠ 0 := by
    intro j hj x
    have hj' : j⁻¹ ∈ J₀ := J₀.inv_mem hj
    have h1 : M j * M j⁻¹ = 1 := by
      rw [← hmul, mul_inv_cancel]; rfl
    rw [hblk j hj, hblk j⁻¹ hj', WitSpNs.planeMat_mul, ← WitSpNs.planeMat_one] at h1
    have h2 := congrFun (WitSpNs.planeMat_injective h1) x
    have h3 := congrArg Matrix.det h2
    rw [Matrix.det_mul, Matrix.det_one] at h3
    exact left_ne_zero_of_mul_eq_one h3
  have hcent : ∀ j ∈ J₀, ∀ x, (blk (M j) x x) *
      ((ζ (f₀ x) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ((ζ (f₀ x) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * blk (M j) x x := by
    intro j hj x
    have hjg : j * spPlaneTorus m ζ f₀ = spPlaneTorus m ζ f₀ * j :=
      Subgroup.mem_centralizer_singleton_iff.mp (hJ.1 hj)
    have h1 : M j * M (spPlaneTorus m ζ f₀) = M (spPlaneTorus m ζ f₀) * M j := by
      rw [← hmul, ← hmul, hjg]
    rw [hMg] at h1
    have e := hblk j hj
    rw [e] at h1
    rw [WitSpNs.planeMat_mul, WitSpNs.planeMat_mul] at h1
    exact congrFun (WitSpNs.planeMat_injective h1) x
  have hcomm : ∀ j ∈ J₀, ∀ j' ∈ J₀, j * j' = j' * j := by
    intro j hj j' hj'
    apply Subtype.ext
    apply Units.ext
    change M (j * j') = M (j' * j)
    rw [hmul, hmul]
    have e := hblk j hj
    have e' := hblk j' hj'
    rw [e, e', WitSpNs.planeMat_mul, WitSpNs.planeMat_mul]
    congr 1
    funext x
    by_cases hx : x ∈ S
    · have hfx : f₀ x ≠ 1 := by
        rcases (hS x).mp hx with h | h
        · rw [h]; exact hc
        · rw [h]; exact inv_ne_one.mpr hc
      have hZ1 : ζ (f₀ x) ≠ 1 := fun h => hfx (hζ (h.trans (map_one ζ).symm))
      have hZp : (ζ (f₀ x)) ^ p = 1 := by
        rw [← map_pow]
        have : (f₀ x) ^ p = 1 := by
          obtain ⟨z, hz⟩ : ∃ z : ZMod p, Multiplicative.ofAdd z = f₀ x :=
            ⟨Multiplicative.toAdd (f₀ x), rfl⟩
          rw [← hz, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]
        rw [this, map_one]
      have htr := trace_ne_zero_of_pow_eq_one hZ1 (hp.odd_of_ne_two hp2) hZp
      exact commute_of_commute_of_trace_ne_zero_gl htr (hdet j hj x) (hdet j' hj' x)
        (hcent j hj x) (hcent j' hj' x)
    · have e1 := hsupp j hj x hx x
      have e2 := hsupp j' hj' x hx x
      simp only [if_true] at e1 e2
      change blk (M j) x x * blk (M j') x x = blk (M j') x x * blk (M j) x x
      rw [e1, e2]
  have hq := (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp
    hJ.2.2
  obtain ⟨-, -, a, b, hab⟩ := hq
  induction a using QuotientGroup.induction_on with | H x => ?_
  induction b using QuotientGroup.induction_on with | H y => ?_
  apply hab
  have hxy : x * y = y * x := Subtype.ext (hcomm x x.2 y y.2)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxy]

end CFSG.StandardType.SympMinus

end
