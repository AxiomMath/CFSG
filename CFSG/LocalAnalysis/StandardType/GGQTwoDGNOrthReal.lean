module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthPaths
public import CFSG.LocalAnalysis.StandardType.GGQTwoDGNOrthGen

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.StandardType.OrthTorus
open CFSG.RankThree.Classical2 (orthDerived)
open Multiplicative

section Even

variable {p r : ℕ}

@[expose] def omEven (p r : ℕ) : Subgroup (MulAut (Fin r → Multiplicative (ZMod p))) :=
  Subgroup.closure (Set.range (SpCoord.permAut (p := p) (k := r)) ∪
    {w | ∃ i j : Fin r, i ≠ j ∧
      w = (SpCoord.sgnAut i : MulAut (Fin r → Multiplicative (ZMod p))) * SpCoord.sgnAut j})

theorem permAut_mem_omEven (σ : Equiv.Perm (Fin r)) :
    (SpCoord.permAut σ : MulAut (Fin r → Multiplicative (ZMod p))) ∈ omEven p r :=
  Subgroup.subset_closure (Or.inl ⟨σ, rfl⟩)

theorem sgnAut_mul_mem_omEven {i j : Fin r} (hij : i ≠ j) :
    (SpCoord.sgnAut i : MulAut (Fin r → Multiplicative (ZMod p))) * SpCoord.sgnAut j ∈
      omEven p r :=
  Subgroup.subset_closure (Or.inr ⟨i, j, hij, rfl⟩)

theorem sgnAut_mul_self' (i : Fin r) :
    (SpCoord.sgnAut i : MulAut (Fin r → Multiplicative (ZMod p))) * SpCoord.sgnAut i = 1 := by
  have h := SpCoord.sgnAut_sq (p := p) i
  rwa [pow_two] at h

theorem sgnAut_inv' (i : Fin r) :
    (SpCoord.sgnAut i : MulAut (Fin r → Multiplicative (ZMod p)))⁻¹ = SpCoord.sgnAut i :=
  inv_eq_of_mul_eq_one_right (sgnAut_mul_self' i)

theorem permAut_inv_conj_sgnAut (σ : Equiv.Perm (Fin r)) (u : Fin r) :
    (SpCoord.permAut σ : MulAut (Fin r → Multiplicative (ZMod p)))⁻¹ * SpCoord.sgnAut u *
        SpCoord.permAut σ = SpCoord.sgnAut (σ⁻¹ u) := by
  refine MulEquiv.ext fun f => funext fun j => ?_
  simp only [MulAut.mul_apply, SpCoord.permAut_inv_apply, SpCoord.permAut_apply,
    SpCoord.sgnAut_apply, Function.comp_apply, Function.update_apply]
  by_cases hj : j = σ⁻¹ u
  · subst hj
    simp
  · have h1 : σ j ≠ u := fun h => hj (by rw [← h]; simp)
    have hj' : j ≠ σ.symm u := hj
    simp [hj', h1]

theorem sgnAut_conj_mem_omEven (u : Fin r) {w : MulAut (Fin r → Multiplicative (ZMod p))}
    (hw : w ∈ omEven p r) :
    (SpCoord.sgnAut u : MulAut (Fin r → Multiplicative (ZMod p))) * w *
      (SpCoord.sgnAut u)⁻¹ ∈ omEven p r := by
  have hle : (omEven p r).map (MulAut.conj (SpCoord.sgnAut u :
      MulAut (Fin r → Multiplicative (ZMod p)))).toMonoidHom ≤ omEven p r := by
    rw [omEven, MonoidHom.map_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨g, hg, rfl⟩
    rcases hg with ⟨σ, rfl⟩ | ⟨i, j, hij, rfl⟩
    · have h1 : (SpCoord.sgnAut u : MulAut (Fin r → Multiplicative (ZMod p))) *
          SpCoord.permAut σ = SpCoord.permAut σ * SpCoord.sgnAut (σ⁻¹ u) := by
        rw [← permAut_inv_conj_sgnAut σ u]
        group
      have h2 : (MulAut.conj (SpCoord.sgnAut u :
          MulAut (Fin r → Multiplicative (ZMod p)))).toMonoidHom (SpCoord.permAut σ) =
            SpCoord.permAut σ * (SpCoord.sgnAut (σ⁻¹ u) * SpCoord.sgnAut u) := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, sgnAut_inv']
        rw [h1, mul_assoc]
      rw [h2]
      refine Subgroup.mul_mem _ (permAut_mem_omEven σ) ?_
      by_cases hσu : σ⁻¹ u = u
      · rw [hσu, sgnAut_mul_self']
        exact Subgroup.one_mem _
      · exact sgnAut_mul_mem_omEven hσu
    · have hci : (SpCoord.sgnAut u : MulAut (Fin r → Multiplicative (ZMod p))) *
          SpCoord.sgnAut i = SpCoord.sgnAut i * SpCoord.sgnAut u := SpCoord.sgnAut_mul_comm u i
      have hcj : (SpCoord.sgnAut u : MulAut (Fin r → Multiplicative (ZMod p))) *
          SpCoord.sgnAut j = SpCoord.sgnAut j * SpCoord.sgnAut u := SpCoord.sgnAut_mul_comm u j
      have hcomm : (SpCoord.sgnAut u : MulAut (Fin r → Multiplicative (ZMod p))) *
          (SpCoord.sgnAut i * SpCoord.sgnAut j) =
            (SpCoord.sgnAut i * SpCoord.sgnAut j) * SpCoord.sgnAut u := by
        rw [← mul_assoc, hci, mul_assoc, hcj, ← mul_assoc]
      have h2 : (MulAut.conj (SpCoord.sgnAut u :
          MulAut (Fin r → Multiplicative (ZMod p)))).toMonoidHom
            (SpCoord.sgnAut i * SpCoord.sgnAut j) = SpCoord.sgnAut i * SpCoord.sgnAut j := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [hcomm, mul_inv_cancel_right]
      rw [h2]
      exact sgnAut_mul_mem_omEven hij
  have h1 := hle ⟨w, hw, rfl⟩
  simpa [MulAut.conj_apply] using h1

theorem mem_omEven_or_sgn_mul (u : Fin r) {w : MulAut (Fin r → Multiplicative (ZMod p))}
    (hw : w ∈ omSigned p r) :
    w ∈ omEven p r ∨ (SpCoord.sgnAut u : MulAut (Fin r → Multiplicative (ZMod p))) * w ∈
      omEven p r := by
  have hs2 := sgnAut_mul_self' (p := p) u
  have hs := sgnAut_inv' (p := p) u
  unfold omSigned at hw
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨σ, rfl⟩ | ⟨i, rfl⟩
    · exact Or.inl (permAut_mem_omEven σ)
    · by_cases hiu : i = u
      · subst hiu
        exact Or.inr (by rw [hs2]; exact Subgroup.one_mem _)
      · exact Or.inr (sgnAut_mul_mem_omEven (Ne.symm hiu))
  | one => exact Or.inl (Subgroup.one_mem _)
  | mul a b _ _ ha hb =>
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact Or.inl (Subgroup.mul_mem _ ha hb)
    · right
      have e : (SpCoord.sgnAut u : MulAut (Fin r → Multiplicative (ZMod p))) * (a * b) =
          ((SpCoord.sgnAut u : MulAut (Fin r → Multiplicative (ZMod p))) * a *
            (SpCoord.sgnAut u)⁻¹) * (SpCoord.sgnAut u * b) := by group
      rw [e]
      exact Subgroup.mul_mem _ (sgnAut_conj_mem_omEven u ha) hb
    · right
      have e : (SpCoord.sgnAut u : MulAut (Fin r → Multiplicative (ZMod p))) * (a * b) =
          (SpCoord.sgnAut u * a) * b := by group
      rw [e]
      exact Subgroup.mul_mem _ ha hb
    · left
      have e : a * b = ((SpCoord.sgnAut u : MulAut (Fin r → Multiplicative (ZMod p))) *
          (SpCoord.sgnAut u * a) * (SpCoord.sgnAut u)⁻¹) * (SpCoord.sgnAut u * b) := by
        rw [← mul_assoc (SpCoord.sgnAut u) (SpCoord.sgnAut u) a, hs2, one_mul]
        group
      rw [e]
      exact Subgroup.mul_mem _ (sgnAut_conj_mem_omEven u ha) hb
  | inv a _ ha =>
    rcases ha with ha | ha
    · exact Or.inl (Subgroup.inv_mem _ ha)
    · right
      have e : (SpCoord.sgnAut u : MulAut (Fin r → Multiplicative (ZMod p))) * a⁻¹ =
          SpCoord.sgnAut u * (SpCoord.sgnAut u * a)⁻¹ * (SpCoord.sgnAut u)⁻¹ := by
        rw [mul_inv_rev, hs]
        simp only [mul_assoc, hs2, mul_one]
      rw [e]
      exact sgnAut_conj_mem_omEven u (Subgroup.inv_mem _ ha)

theorem omTog_of_not_mem {i : Fin r} {x : OmPlusIdx r} (h : i ∉ omSupp x) : omTog i x = x := by
  simp [omTog, h]

theorem not_mem_omSupp_std (hr : 4 ≤ r) (k : Fin r) (hk : k.val ≤ 1) :
    (⟨3, by omega⟩ : Fin r) ∉ omSupp (omStd r (by omega) k) := by
  rw [omSupp_omStd_chain (by omega) (by omega)]
  simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, not_or]
  omega

theorem exists_omEven_conj_std (hr : 4 ≤ r) {x y : OmPlusIdx r}
    (hxy : omSupp x ≠ omSupp y) (hnd : ¬ Disjoint (omSupp x) (omSupp y)) :
    ∃ w ∈ omEven p r,
      omPlusRefl p (omStd r (by omega) ⟨0, by omega⟩) = w * omPlusRefl p x * w⁻¹ ∧
      omPlusRefl p (omStd r (by omega) ⟨1, by omega⟩) = w * omPlusRefl p y * w⁻¹ := by
  obtain ⟨m, hx, hy⟩ := omMove_pair (p := p) (by omega : 3 ≤ r) hxy hnd
  have hmx : omPlusRefl p (omStd r (by omega) ⟨0, by omega⟩) =
      m.w * omPlusRefl p x * m.w⁻¹ := by rw [← hx, m.hf x]
  have hmy : omPlusRefl p (omStd r (by omega) ⟨1, by omega⟩) =
      m.w * omPlusRefl p y * m.w⁻¹ := by rw [← hy, m.hf y]
  rcases mem_omEven_or_sgn_mul (p := p) (⟨3, by omega⟩ : Fin r) m.hw with hm | hm
  · exact ⟨m.w, hm, hmx, hmy⟩
  · refine ⟨SpCoord.sgnAut ⟨3, by omega⟩ * m.w, hm, ?_, ?_⟩
    · have h0 := not_mem_omSupp_std hr ⟨0, by omega⟩ (by simp)
      have e0 : omPlusRefl p (omStd r (by omega) ⟨0, by omega⟩) =
          SpCoord.sgnAut ⟨3, by omega⟩ * omPlusRefl p (omStd r (by omega) ⟨0, by omega⟩) *
            (SpCoord.sgnAut ⟨3, by omega⟩)⁻¹ := by
        rw [← omTog_refl, omTog_of_not_mem h0]
      calc omPlusRefl p (omStd r (by omega) ⟨0, by omega⟩)
          = SpCoord.sgnAut ⟨3, by omega⟩ * omPlusRefl p (omStd r (by omega) ⟨0, by omega⟩) *
            (SpCoord.sgnAut ⟨3, by omega⟩)⁻¹ := e0
        _ = SpCoord.sgnAut ⟨3, by omega⟩ * (m.w * omPlusRefl p x * m.w⁻¹) *
            (SpCoord.sgnAut ⟨3, by omega⟩)⁻¹ := by rw [← hmx]
        _ = (SpCoord.sgnAut ⟨3, by omega⟩ * m.w) * omPlusRefl p x *
            (SpCoord.sgnAut ⟨3, by omega⟩ * m.w)⁻¹ := by group
    · have h0 := not_mem_omSupp_std hr ⟨1, by omega⟩ (by simp)
      have e0 : omPlusRefl p (omStd r (by omega) ⟨1, by omega⟩) =
          SpCoord.sgnAut ⟨3, by omega⟩ * omPlusRefl p (omStd r (by omega) ⟨1, by omega⟩) *
            (SpCoord.sgnAut ⟨3, by omega⟩)⁻¹ := by
        rw [← omTog_refl, omTog_of_not_mem h0]
      calc omPlusRefl p (omStd r (by omega) ⟨1, by omega⟩)
          = SpCoord.sgnAut ⟨3, by omega⟩ * omPlusRefl p (omStd r (by omega) ⟨1, by omega⟩) *
            (SpCoord.sgnAut ⟨3, by omega⟩)⁻¹ := e0
        _ = SpCoord.sgnAut ⟨3, by omega⟩ * (m.w * omPlusRefl p y * m.w⁻¹) *
            (SpCoord.sgnAut ⟨3, by omega⟩)⁻¹ := by rw [← hmy]
        _ = (SpCoord.sgnAut ⟨3, by omega⟩ * m.w) * omPlusRefl p y *
            (SpCoord.sgnAut ⟨3, by omega⟩ * m.w)⁻¹ := by group

theorem exists_omEven_conj_pair (hp : p.Prime) (hr : 4 ≤ r) {x y x' y' : OmPlusIdx r}
    (hnc : omPlusRefl p x * omPlusRefl p y ≠ omPlusRefl p y * omPlusRefl p x)
    (hnc' : omPlusRefl p x' * omPlusRefl p y' ≠ omPlusRefl p y' * omPlusRefl p x') :
    ∃ w ∈ omEven p r, omPlusRefl p x' = w * omPlusRefl p x * w⁻¹ ∧
      omPlusRefl p y' = w * omPlusRefl p y * w⁻¹ := by
  obtain ⟨hxy, hnd⟩ := (omPlusRefl_not_comm_iff_supp hp x y).mp hnc
  obtain ⟨hxy', hnd'⟩ := (omPlusRefl_not_comm_iff_supp hp x' y').mp hnc'
  obtain ⟨w₁, hw₁, h1x, h1y⟩ := exists_omEven_conj_std (p := p) hr hxy hnd
  obtain ⟨w₂, hw₂, h2x, h2y⟩ := exists_omEven_conj_std (p := p) hr hxy' hnd'
  refine ⟨w₂⁻¹ * w₁, Subgroup.mul_mem _ (Subgroup.inv_mem _ hw₂) hw₁, ?_, ?_⟩
  · have e : omPlusRefl p x' = w₂⁻¹ * omPlusRefl p (omStd r (by omega) ⟨0, by omega⟩) * w₂ := by
      rw [h2x]
      group
    rw [e, h1x]
    group
  · have e : omPlusRefl p y' = w₂⁻¹ * omPlusRefl p (omStd r (by omega) ⟨1, by omega⟩) * w₂ := by
      rw [h2y]
      group
    rw [e, h1y]
    group

end Even

end CFSG.StandardType.QTwo

namespace CFSG.StandardType.OrthTorus

open CFSG.StandardType.QTwo
open CFSG.RankThree.Classical2 (orthDerived)

section Real

variable {G : Type} [Group G] {p : ℕ} {Bs X : Subgroup G}

@[expose] def OrthFrameCore.realGroup (Φ : OrthFrameCore p Bs X) :
    Subgroup (MulAut (Fin Φ.r → Multiplicative (ZMod p))) where
  carrier := {w | ∃ μ : ↥(orthDerived Φ.Q),
    (∀ f, (μ : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (μ : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ = Φ.Δ.τ (w f)) ∧
      Φ.ψ μ ∈ Subgroup.normalizer (Bs : Set G)}
  mul_mem' := by
    rintro w₁ w₂ ⟨μ₁, h₁, n₁⟩ ⟨μ₂, h₂, n₂⟩
    refine ⟨μ₁ * μ₂, fun f => ?_, by rw [map_mul]; exact Subgroup.mul_mem _ n₁ n₂⟩
    have e : ((μ₁ * μ₂ : ↥(orthDerived Φ.Q)) : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f *
        ((μ₁ * μ₂ : ↥(orthDerived Φ.Q)) : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ =
        (μ₁ : Φ.V ≃ₗ[Φ.F] Φ.V) * ((μ₂ : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f *
          (μ₂ : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹) * (μ₁ : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ := by
      simp only [Subgroup.coe_mul, mul_inv_rev]
      group
    rw [e, h₂ f]
    exact h₁ (w₂ f)
  one_mem' := ⟨1, fun f => by simp, by rw [map_one]; exact Subgroup.one_mem _⟩
  inv_mem' := by
    rintro w ⟨μ, h, n⟩
    refine ⟨μ⁻¹, fun f => ?_, by rw [map_inv]; exact Subgroup.inv_mem _ n⟩
    have h1 := h (w⁻¹ f)
    rw [MulAut.apply_inv_self] at h1
    have e : ((μ⁻¹ : ↥(orthDerived Φ.Q)) : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f *
        ((μ⁻¹ : ↥(orthDerived Φ.Q)) : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ = Φ.Δ.τ (w⁻¹ f) := by
      rw [← h1]
      simp only [Subgroup.coe_inv, inv_inv]
      group
    exact e

theorem OrthFrameCore.permAut_mem_realGroup (Φ : OrthFrameCore p Bs X)
    (σ : Equiv.Perm (Fin Φ.r)) : SpCoord.permAut σ ∈ Φ.realGroup := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one =>
    have h1 : (SpCoord.permAut (1 : Equiv.Perm (Fin Φ.r)) :
        MulAut (Fin Φ.r → Multiplicative (ZMod p))) = 1 :=
      MulEquiv.ext fun f => funext fun j => by simp [SpCoord.permAut_apply]
    rw [h1]
    exact Φ.realGroup.one_mem
  | swap_mul σ a b hab ih =>
    have h1 : (SpCoord.permAut (Equiv.swap a b * σ) :
        MulAut (Fin Φ.r → Multiplicative (ZMod p))) =
        SpCoord.permAut (Equiv.swap a b) * SpCoord.permAut σ :=
      MulEquiv.ext fun f => funext fun j => by simp [SpCoord.permAut_apply, mul_inv_rev]
    rw [h1]
    refine Φ.realGroup.mul_mem ?_ ih
    obtain ⟨w, hw, hn⟩ := Φ.swapReal a b hab
    exact ⟨w, hw, hn⟩

theorem OrthFrameCore.sgnAut_mul_mem_realGroup (Φ : OrthFrameCore p Bs X) {i j : Fin Φ.r}
    (hij : i ≠ j) :
    (SpCoord.sgnAut i : MulAut (Fin Φ.r → Multiplicative (ZMod p))) * SpCoord.sgnAut j ∈
      Φ.realGroup := by
  obtain ⟨w, hw, hn⟩ := Φ.dinvReal i j hij
  exact ⟨w, hw, hn⟩

theorem OrthFrameCore.omEven_le_realGroup (Φ : OrthFrameCore p Bs X) :
    omEven p Φ.r ≤ Φ.realGroup := by
  rw [omEven, Subgroup.closure_le]
  rintro w (⟨σ, rfl⟩ | ⟨i, j, hij, rfl⟩)
  · exact Φ.permAut_mem_realGroup σ
  · exact Φ.sgnAut_mul_mem_realGroup hij

theorem OrthFrameCore.img_map_conj (Φ : OrthFrameCore p Bs X) (μ : ↥(orthDerived Φ.Q))
    (S : Subgroup (Φ.V ≃ₗ[Φ.F] Φ.V)) :
    Φ.img (S.map (MulAut.conj (μ : Φ.V ≃ₗ[Φ.F] Φ.V)).toMonoidHom) =
      (Φ.img S).map (MulAut.conj (Φ.ψ μ)).toMonoidHom := by
  ext g
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz1 : (z : Φ.V ≃ₗ[Φ.F] Φ.V) ∈
        S.map (MulAut.conj (μ : Φ.V ≃ₗ[Φ.F] Φ.V)).toMonoidHom := Subgroup.mem_subgroupOf.mp hz
    obtain ⟨s, hs, hsz⟩ := Subgroup.mem_map.mp hz1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hsz
    have hsμ : s = ((μ⁻¹ * z * μ : ↥(orthDerived Φ.Q)) : Φ.V ≃ₗ[Φ.F] Φ.V) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hsz]
      group
    refine ⟨Φ.ψ (μ⁻¹ * z * μ), ⟨μ⁻¹ * z * μ, ?_, rfl⟩, ?_⟩
    · refine Subgroup.mem_subgroupOf.mpr ?_
      rw [← hsμ]
      exact hs
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
      group
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨μ * t * μ⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · refine Subgroup.mem_map.mpr ⟨t, Subgroup.mem_subgroupOf.mp ht, ?_⟩
      simp [MulAut.conj_apply]
    · simp [map_mul, map_inv, MulAut.conj_apply]

variable [Finite G] [Fact p.Prime]

theorem OrthFrameCore.exists_img_rank2_conj (Φ : OrthFrameCore p Bs X)
    {x y x' y' : OmPlusIdx Φ.r}
    (hnc : omPlusRefl p x * omPlusRefl p y ≠ omPlusRefl p y * omPlusRefl p x)
    (hnc' : omPlusRefl p x' * omPlusRefl p y' ≠ omPlusRefl p y' * omPlusRefl p x') :
    ∃ g ∈ X ⊓ Subgroup.normalizer (Bs : Set G),
      Φ.img (Φ.rank2 x' y') = (Φ.img (Φ.rank2 x y)).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨w, hwE, hx, hy⟩ := exists_omEven_conj_pair (Fact.out) Φ.hr hnc hnc'
  obtain ⟨μ, hμ, hμN⟩ := Φ.omEven_le_realGroup hwE
  have hμO : (μ : Φ.V ≃ₗ[Φ.F] Φ.V) ∈ TauCeti.QuadraticMap.orthogonalGroup Φ.Q :=
    CFSG.RankThree.Classical.orthDerived_le_orthogonalGroup Φ.Q μ.2
  have hrank := qtwoOrth_rank2_conj Φ hμO hμ hx hy
  refine ⟨Φ.ψ μ, Subgroup.mem_inf.mpr ⟨?_, hμN⟩, ?_⟩
  · have hmem : Φ.ψ μ ∈ Φ.ψ.range := ⟨μ, rfl⟩
    rwa [Φ.hrange] at hmem
  · rw [hrank]
    exact Φ.img_map_conj μ _

end Real

end CFSG.StandardType.OrthTorus

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.StandardType.OrthTorus
open CFSG.RankThree.Classical2 (orthDerived)

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs X : Subgroup G}

theorem qTwoD_orth_anchor_gen (Φ : OrthFrameCore p Bs X) (hF : Nat.card Φ.F = 2)
    {x y : OmPlusIdx Φ.r}
    (hxy : omPlusRefl p x * omPlusRefl p y ≠ omPlusRefl p y * omPlusRefl p x) :
    X ≤ ⨆ (g : G) (_ : g ∈ X ⊓ Subgroup.normalizer (Bs : Set G)),
      (Φ.img (Φ.rank2 x y)).map (MulAut.conj g).toMonoidHom := by
  refine (Φ.le_iSup_img_rank2 hF).trans (iSup₂_le fun x' y' => iSup_le fun hxy' => ?_)
  obtain ⟨g, hg, heq⟩ := Φ.exists_img_rank2_conj hxy hxy'
  rw [heq]
  exact le_iSup₂_of_le g hg le_rfl

theorem qTwoD_gn_of_orthChart {J : Subgroup G} (Φ : OrthFrameCore p Bs X)
    (hF : Nat.card Φ.F = 2) {x y : OmPlusIdx Φ.r}
    (hxy : omPlusRefl p x * omPlusRefl p y ≠ omPlusRefl p y * omPlusRefl p x)
    (hJ : Φ.img (Φ.rank2 x y) ≤ J) :
    X ≤ ⨆ (g : G) (_ : g ∈ X) (_ : ∃ φ : MulAut ↥Bs,
        g ∈ Subgroup.normalizer (Bs : Set G) ∧
          ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = g * b * g⁻¹),
      J.map (MulAut.conj g).toMonoidHom := by
  refine (qTwoD_orth_anchor_gen Φ hF hxy).trans (iSup₂_le fun g hg => ?_)
  obtain ⟨hgX, hgN⟩ := Subgroup.mem_inf.mp hg
  exact le_iSup₂_of_le g hgX (le_iSup_of_le ⟨ggConjAut Bs hgN, hgN,
    fun b => ggConjAut_apply Bs hgN b⟩ (Subgroup.map_mono hJ))

end CFSG.StandardType.QTwo

end
