module

public import CFSG.Quasithin.Vol2.Ch11G2Q8AutV
public import CFSG.Quasithin.Vol2.Ch11SecBK4P

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin CFSG.Quasithin.JonesParshall
open scoped IsMulCommutative

namespace BK4

variable {G : Type} [Group G] {L V : Subgroup G}

theorem exists_pow_of_flag [IsMulCommutative ↥V] {Dm : FFModel} {K M : Type} [Field K]
    [Finite K] [CharP K 2] [AddCommGroup M] [Module K M] [Finite M]
    {LM : KGNat.LinModel Dm K M} {π : Dm.Gam →* ↥(autOn L V)} {f : ↥V → M}
    (hf : KGNat.IsCoord LM (autOn L V) ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) {D : Subgroup G} [IsMulCommutative ↥D]
    (hDL : D ≤ L) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hDp : ∀ d ∈ D, d ^ p = 1) {t : G}
    (htV : t ∈ Subgroup.normalizer (V : Set G)) (htL : t ∈ Subgroup.normalizer (L : Set G))
    (htD : t ∈ Subgroup.normalizer (D : Set G))
    {m : ℕ} (F : ℕ → Submodule K M) (hF0 : F 0 = ⊥) (hFm : F m = ⊤)
    (hstep : ∀ i < m, ∃ e ∈ F (i + 1), e ∉ F i ∧ ∀ y ∈ F (i + 1), ∃ c : K, y - c • e ∈ F i)
    (hDF : ∀ d (hd : d ∈ D), ∀ i, ∀ w : ↥V, f w ∈ F i →
      f (SecA.conjV V d (hLV (hDL hd)) w) ∈ F i)
    {T' : M →+ M} {σ : K →+* K} (hσ : ∀ (c : K) y, T' (c • y) = σ c • T' y)
    (hT' : ∀ w, f (SecA.conjV V t htV w) = T' (f w)) (hTF : ∀ i, ∀ y ∈ F i, T' y ∈ F i)
    (hrig : ∀ x (hxV : x ∈ Subgroup.normalizer (V : Set G)),
      x ∈ Subgroup.normalizer (L : Set G) → (∀ w, f (SecA.conjV V x hxV w) = f w) →
        x ∈ Subgroup.centralizer (V : Set G)) :
    ∃ r : ℕ, ∀ d ∈ D, t * d * t⁻¹ * (d ^ r)⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  have hdV : ∀ d : ↥D, (d : G) ∈ Subgroup.normalizer (V : Set G) := fun d => hLV (hDL d.2)
  have hZ : ∀ d : ↥D, ∀ z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V,
      SecA.conjV V d (hdV d) z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V :=
    fun d z hz => G2Q8.conjV_mem_centralizer (Subgroup.le_normalizer (hDL d.2)) (hdV d) hz
  let ρ : ↥D → M →+ M := fun d => hf.inducedMap (SecA.conjV V d (hdV d)).toMonoidHom (hZ d)
  have hρ : ∀ d w, ρ d (f w) = f (SecA.conjV V d (hdV d) w) := fun d w =>
    hf.inducedMap_apply _ (hZ d) w
  have hρ1 : ∀ y, ρ 1 y = y := by
    intro y
    obtain ⟨w, rfl⟩ := hf.surj y
    rw [hρ]
    congr 1
    exact Subtype.ext (by rw [SecA.conjV_apply_coe]; simp)
  have hρmul : ∀ d₁ d₂ y, ρ (d₁ * d₂) y = ρ d₁ (ρ d₂ y) := by
    intro d₁ d₂ y
    obtain ⟨w, rfl⟩ := hf.surj y
    rw [hρ, hρ, hρ]
    congr 1
    exact Subtype.ext (by simp only [SecA.conjV_apply_coe, Subgroup.coe_mul]; group)
  have hρlin : ∀ d (c : K) y, ρ d (c • y) = c • ρ d y := by
    intro d c y
    obtain ⟨γ, hγ⟩ := hf.exists_lin ⟨SecA.conjV V d (hdV d), SecA.conjV_mem_autOn (hDL d.2) _⟩
    have hl : ∀ y, ρ d y = LM.lin γ y := fun y => by
      obtain ⟨w, rfl⟩ := hf.surj y
      rw [hρ]
      exact hγ w
    rw [hl, hl, LinearMap.map_smul]
  have hρF : ∀ d i, ∀ y ∈ F i, ρ d y ∈ F i := by
    intro d i y hy
    obtain ⟨w, rfl⟩ := hf.surj y
    rw [hρ]
    exact hDF d d.2 i w hy
  let τ : ↥D → ↥D := fun d => ⟨t * d * t⁻¹, (Subgroup.mem_normalizer_iff.mp htD d).mp d.2⟩
  have hτ : ∀ d y, T' (ρ d y) = ρ (τ d) (T' y) := by
    intro d y
    obtain ⟨w, rfl⟩ := hf.surj y
    rw [hρ, ← hT', ← hT', hρ]
    congr 1
    exact Subtype.ext (by simp only [SecA.conjV_apply_coe, τ]; group)
  have hTinj : Function.Injective T' := by
    refine Finite.injective_iff_surjective.mpr fun y => ?_
    obtain ⟨w, rfl⟩ := hf.surj y
    refine ⟨f ((SecA.conjV V t htV)⁻¹ w), ?_⟩
    rw [← hT', MulAut.apply_inv_self]
  have hDp' : ∀ d : ↥D, d ^ p = 1 := fun d => Subtype.ext (by simp [hDp d d.2])
  obtain ⟨r, hr⟩ := conj_eq_pow_of_flag ρ F hF0 hFm hstep hp hp2 hDp' hρ1 hρmul hρlin hρF T'
    σ hσ hTinj hTF τ hτ
  refine ⟨r, fun d hd => ?_⟩
  set d' : ↥D := ⟨d, hd⟩ with hd'
  have hxV : t * d * t⁻¹ * (d ^ r)⁻¹ ∈ Subgroup.normalizer (V : Set G) := by
    have := hdV d'
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ htV this)
      (Subgroup.inv_mem _ htV)) (Subgroup.inv_mem _ (Subgroup.pow_mem _ this r))
  refine hrig _ hxV ?_ fun w => ?_
  · have hdL := Subgroup.le_normalizer (hDL hd)
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ htL hdL)
      (Subgroup.inv_mem _ htL)) (Subgroup.inv_mem _ (Subgroup.pow_mem _ hdL r))
  set u := SecA.conjV V ((d' ^ r)⁻¹ : ↥D) (hdV _) w with hu
  have e1 : SecA.conjV V _ hxV w = SecA.conjV V (τ d') (hdV _) u :=
    Subtype.ext (by simp only [hu, SecA.conjV_apply_coe, τ, hd', InvMemClass.coe_inv,
      SubmonoidClass.coe_pow]; group)
  have e2 : SecA.conjV V (d' ^ r : ↥D) (hdV _) u = w :=
    Subtype.ext (by simp only [hu, SecA.conjV_apply_coe, InvMemClass.coe_inv,
      SubmonoidClass.coe_pow]; group)
  rw [e1, ← hρ, hr, hρ, e2]

end BK4

end CFSG.Quasithin.Vol2.Ch11.SecB
