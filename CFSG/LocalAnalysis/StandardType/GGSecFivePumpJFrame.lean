module

public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSLCent
import CFSG.LocalAnalysis.StandardType.GGSixLinearModelOmega

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal

private theorem jframe_pair {m : ℕ} {F : Type} [Field F] (hm : 2 ≤ m) {G : Type} [Group G]
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) {b : G}
    (hb : ∀ γ ∈ (SpecialLinear.rootDatum m F).roots, ∃ h ∈ ggTorus (SpecialLinear.rootDatum m F),
      ∀ z ∈ (SpecialLinear.rootDatum m F).rootGroup γ, b * ψ z * b⁻¹ = ψ (h * z * h⁻¹)) :
    ∃ d : Fin (m + 1) → Fˣ, (b, InnerDiagA.diagGL d) ∈ LinFusion.ggInducedPairs ψ := by
  have key : ∀ (i j : Fin (m + 1)) (hij : i ≠ j), ∃ χ : F, ∀ t : F,
      b * ψ (Matrix.SpecialLinearGroup.transvection hij t) * b⁻¹ =
        ψ (Matrix.SpecialLinearGroup.transvection hij (χ * t)) := by
    intro i j hij
    obtain ⟨h, hh, hz⟩ := hb _ (InnerDiagA.typeARoot_mem_roots F hij)
    have hN : h ∈ Subgroup.normalizer (SpecialLinear.rootSubgroup m F hij :
        Set (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) := by
      simp only [ggTorus, Subgroup.mem_iInf] at hh
      have h1 : h ∈ Subgroup.normalizer (SpecialLinear.rootGroup m F (InnerDiagA.typeARoot i j) :
          Set (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) :=
        hh _ (InnerDiagA.typeARoot_mem_roots F hij)
      rwa [InnerDiagA.rootGroup_typeARoot] at h1
    obtain ⟨χ, hχ⟩ := InnerDiagA.exists_conj_transvection_eq hij hN
    have hmem : ∀ t : F, Matrix.SpecialLinearGroup.transvection hij t ∈
        SpecialLinear.rootGroup m F (InnerDiagA.typeARoot i j) := fun t => by
      rw [InnerDiagA.rootGroup_typeARoot]
      exact SpecialLinear.transvection_mem_rootSubgroup hij t
    exact ⟨χ, fun t => by rw [hz _ (hmem t), hχ]⟩
  choose! χ hχ using key
  have hne : ∀ i j : Fin (m + 1), i ≠ j → χ i j ≠ 0 := by
    intro i j hij h0
    have h1 := hχ i j hij 1
    rw [h0, zero_mul, Matrix.SpecialLinearGroup.transvection_coeff_zero, map_one] at h1
    have h2 : ψ (Matrix.SpecialLinearGroup.transvection hij 1) = 1 := by
      calc ψ (Matrix.SpecialLinearGroup.transvection hij 1)
          = b⁻¹ * (b * ψ (Matrix.SpecialLinearGroup.transvection hij 1) * b⁻¹) * b := by group
        _ = 1 := by rw [h1]; group
    exact one_ne_zero (InnerDiagA.eq_zero_of_transvection_mem_center hij (hker h2))
  let β : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G := (MulAut.conj b).toMonoidHom.comp ψ
  have hβ : ∀ u, β u = b * ψ u * b⁻¹ := fun u => by simp [β]
  have hχ' : ∀ (i j : Fin (m + 1)) (hij : i ≠ j) (t : F),
      β (Matrix.SpecialLinearGroup.transvection hij t) =
        ψ (Matrix.SpecialLinearGroup.transvection hij (χ i j * t)) :=
    fun i j hij t => (hβ _).trans (hχ i j hij t)
  obtain ⟨d, hd⟩ := InnerDiagA.exists_diag_of_cocycle (χ := χ) hm
    (fun _ _ _ hij hjk hik => InnerDiagA.chi_cocycle ψ β hker hχ' hij hjk hik) hne
  have hβψ : β = ψ.comp (InnerDiagA.conjSL (InnerDiagA.diagGL d)) := by
    refine MonoidHom.eq_of_eqOn_dense
      Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field ?_
    rintro _ ⟨⟨i, j, hij, t⟩, rfl⟩
    rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk, hχ', MonoidHom.comp_apply,
      InnerDiagA.conjSL_diagGL_transvection, hd i j hij, Units.val_inv_eq_inv_val,
      mul_right_comm (χ i j), mul_assoc _ _ ((d j : F))⁻¹, mul_inv_cancel₀ (d j).ne_zero,
      mul_one]
  exact ⟨d, LinFusion.mem_ggInducedPairs.mpr fun u => by rw [← hβ, hβψ, MonoidHom.comp_apply]⟩

private theorem jframe_unique {m : ℕ} {F : Type} [Field F] [CharP F 2] {G : Type} [Group G]
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) {b : G}
    {d d' : Fin (m + 1) → Fˣ} (hd : (b, InnerDiagA.diagGL d) ∈ LinFusion.ggInducedPairs ψ)
    (hd' : (b, InnerDiagA.diagGL d') ∈ LinFusion.ggInducedPairs ψ) (h0 : d 0 = d' 0) :
    d = d' := by
  obtain ⟨c, hc⟩ := LinTorus.exists_scalar_mul_of_mem_ggInducedPairs hker hd hd'
  exact LinModel.eq_of_diagGL_eq_scalar_mul hc h0

private theorem jframe_full {m : ℕ} {F : Type} [Field F] {p : ℕ} (hp : p.Prime) {H : Type}
    [Group H] (δ : H →* (Fin (m + 1) → Fˣ)) (h0 : ∀ b, δ b 0 = 1)
    (hδp : ∀ b j, δ b j ^ p = 1) (hcard : p ^ m ≤ Nat.card δ.range)
    (v : Fin (m + 1) → Fˣ) (hv : ∀ j, v j ^ p = 1) : ∃ (b : H) (c : Fˣ), ∀ j, δ b j = c * v j := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hmem : ∀ (y : δ.range) (j : Fin (m + 1)), (y : Fin (m + 1) → Fˣ) j ∈ rootsOfUnity p F := by
    intro y j
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp y.2
    rw [mem_rootsOfUnity, ← hb]
    exact hδp b j
  have hy0 : ∀ y : δ.range, (y : Fin (m + 1) → Fˣ) 0 = 1 := by
    intro y
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp y.2
    rw [← hb]
    exact h0 b
  let π : δ.range → (Fin m → rootsOfUnity p F) := fun y j => ⟨_, hmem y j.succ⟩
  have hinj : Function.Injective π := by
    intro y y' hyy
    refine Subtype.ext (funext fun j => ?_)
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
    · rw [hy0, hy0]
    · exact congrArg Subtype.val (congrFun hyy k)
  have hle : Nat.card (Fin m → rootsOfUnity p F) ≤ Nat.card δ.range := by
    rw [Nat.card_fun, Nat.card_fin]
    exact (Nat.pow_le_pow_left (card_rootsOfUnity F p) m).trans hcard
  have hw : ∀ j : Fin m, (v 0)⁻¹ * v j.succ ∈ rootsOfUnity p F := fun j => by
    rw [mem_rootsOfUnity, mul_pow, inv_pow, hv, hv, inv_one, one_mul]
  obtain ⟨y, hy⟩ := (hinj.bijective_of_nat_card_le hle).2 fun j => ⟨_, hw j⟩
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp y.2
  refine ⟨b, (v 0)⁻¹, fun j => ?_⟩
  rw [hb]
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
  · rw [hy0, inv_mul_cancel]
  · exact congrArg Subtype.val (congrFun hy k)

theorem ggDk_exists_diagFrame {m : ℕ} {F : Type} [Field F] [CharP F 2] (hm : 2 ≤ m)
    {G : Type} [Group G] {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {p : ℕ} (hp : p.Prime) {Bs : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hstd : GGKGPosStdPos (SpecialLinear.rootDatum m F) ψ Bs)
    (hcard : Nat.card Bs = p ^ (m + 1))
    (hC : Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) ≤ p) :
    ∃ δ : ↥Bs →* (Fin (m + 1) → Fˣ),
      (∀ b : ↥Bs, ((b : G), InnerDiagA.diagGL (δ b)) ∈ LinFusion.ggInducedPairs ψ) ∧
      (∀ (b : ↥Bs) j, δ b j ^ p = 1) ∧
      (∀ b : ↥Bs, (b : G) ∈ Subgroup.centralizer (ψ.range : Set G) → δ b = 1) ∧
      ∀ v : Fin (m + 1) → Fˣ, (∀ j, v j ^ p = 1) →
        ∃ (b : ↥Bs) (c : Fˣ), ∀ j, δ b j = c * v j := by
  have hrep : ∀ b : ↥Bs, ∃ d : Fin (m + 1) → Fˣ, d 0 = 1 ∧
      ((b : G), InnerDiagA.diagGL d) ∈ LinFusion.ggInducedPairs ψ := by
    intro b
    obtain ⟨d, hd⟩ := jframe_pair hm hker (hstd b b.2)
    refine ⟨fun i => (d 0)⁻¹ * d i, inv_mul_cancel _, ?_⟩
    rw [← LinModel.scalar_mul_diagGL]
    exact LinModel.scalar_mul_mem_ggInducedPairs hd _
  choose d hd0 hd using hrep
  have hmul : ∀ a b : ↥Bs, d (a * b) = d a * d b := fun a b =>
    jframe_unique hker (hd (a * b))
      (by rw [LinFusion.diagGL_mul]; exact (LinFusion.ggInducedPairs ψ).mul_mem (hd a) (hd b))
      (by simp only [Pi.mul_apply, hd0, one_mul])
  let δ : ↥Bs →* (Fin (m + 1) → Fˣ) := MonoidHom.mk' d hmul
  have hpow : ∀ (b : ↥Bs) j, δ b j ^ p = 1 := by
    intro b j
    have h1 : δ b ^ p = 1 := by
      rw [← map_pow, show b ^ p = 1 from Subtype.ext (hBs.2 b b.2), map_one]
    exact congrFun h1 j
  have hcent : ∀ b : ↥Bs, (b : G) ∈ Subgroup.centralizer (ψ.range : Set G) → δ b = 1 := by
    intro b hb
    refine jframe_unique hker (hd b) ?_ (hd0 b)
    rw [LinFusion.diagGL_one]
    refine LinFusion.mem_ggInducedPairs.mpr fun u => ?_
    rw [LinFusion.conjSL_one,
      ← Subgroup.mem_centralizer_iff.mp hb _ (MonoidHom.mem_range.mpr ⟨u, rfl⟩),
      mul_inv_cancel_right]
  have hkerC : ∀ b : ↥Bs, δ b = 1 → (b : G) ∈ Bs ⊓ Subgroup.centralizer (ψ.range : Set G) := by
    intro b hb
    refine Subgroup.mem_inf.mpr ⟨b.2, LinFusion.mem_centralizer_of_mem_ggInducedPairs_one ?_⟩
    have h1 := hd b
    rwa [show d b = 1 from hb, LinFusion.diagGL_one] at h1
  haveI : Finite ↥Bs :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.ne_zero)
  haveI : Finite ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) :=
    Finite.of_injective _ (Subgroup.inclusion_injective inf_le_left)
  have hk : Nat.card δ.ker ≤ p :=
    (Nat.card_le_card_of_injective (fun b : δ.ker => (⟨b.1, hkerC b.1 (MonoidHom.mem_ker.mp b.2)⟩ :
      ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G))))
      fun x y hxy => Subtype.ext (Subtype.ext (congrArg
        (Subtype.val : ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) → G) hxy))).trans hC
  have hr : p ^ m ≤ Nat.card δ.range := by
    have h1 := Subgroup.card_ker_mul_card_range δ
    rw [hcard, pow_succ] at h1
    have h2 : p ^ m * p ≤ Nat.card δ.range * p := by
      rw [← h1, mul_comm (Nat.card δ.range)]
      exact Nat.mul_le_mul_right _ hk
    exact Nat.le_of_mul_le_mul_right h2 hp.pos
  exact ⟨δ, hd, hpow, hcent, fun v hv => jframe_full hp δ hd0 hpow hr v hv⟩

end CFSG.StandardType

end
