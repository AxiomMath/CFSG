module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthTorDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthRealize
import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthPathsMoves
import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown

public section

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.RankThree.Classical2 (orthDerived)
open TauCeti.QuadraticMap
open CFSG.StandardType.QTwo
open scoped commutatorElement

@[expose] def torStd (p r a₀ : ℕ) : Fin r → Multiplicative (ZMod p) := fun i =>
  if i.val < a₀ then 1 else Multiplicative.ofAdd 1

theorem plh_toAdd_eq_zero_iff {p : ℕ} (x : Multiplicative (ZMod p)) :
    Multiplicative.toAdd x = 0 ↔ x = 1 := by
  constructor
  · intro h
    exact Multiplicative.toAdd.injective (by rw [h, toAdd_one])
  · intro h
    rw [h, toAdd_one]

theorem plh_permAut_mul_inv {p k : ℕ} (σ : Equiv.Perm (Fin k)) :
    SpCoord.permAut (p := p) σ * SpCoord.permAut σ⁻¹ = 1 := by
  refine MulEquiv.ext fun f => funext fun j => ?_
  simp [SpCoord.permAut_apply, MulAut.mul_apply]

theorem plh_permAut_inv {p k : ℕ} (σ : Equiv.Perm (Fin k)) :
    (SpCoord.permAut (p := p) σ)⁻¹ = SpCoord.permAut σ⁻¹ :=
  inv_eq_of_mul_eq_one_right (plh_permAut_mul_inv σ)

theorem plh_sgnAut_inv {p k : ℕ} (i : Fin k) :
    (SpCoord.sgnAut (p := p) i)⁻¹ = SpCoord.sgnAut i := by
  have h := SpCoord.sgnAut_sq (p := p) i
  rw [pow_two] at h
  exact inv_eq_of_mul_eq_one_right h

theorem plh_toAdd_torStd {p r a₀ : ℕ} (j : Fin r) :
    Multiplicative.toAdd (torStd p r a₀ j) = if j.val < a₀ then 0 else 1 := by
  unfold torStd
  split_ifs
  · rw [toAdd_one]
  · rw [toAdd_ofAdd]

theorem plh_zmod_three (x : ZMod 3) : x = 0 ∨ x = 1 ∨ x = 2 := by
  revert x
  decide

theorem plh_zmod_sign_three {p : ℕ} (hp : p = 3) (x : ZMod p) :
    (if x = -1 then (-1 : ZMod p) else 1) * x = if x = 0 then 0 else 1 := by
  subst p
  rcases plh_zmod_three x with rfl | rfl | rfl <;> decide

theorem plh_card_filter_fin_le (n a : ℕ) :
    (Finset.univ.filter (fun i : Fin n => a ≤ i.val)).card = n - a := by
  symm
  rw [← Finset.card_fin (n - a)]
  refine Finset.card_bij (fun j (_ : j ∈ (Finset.univ : Finset (Fin (n - a)))) =>
    (⟨a + j.val, by have := j.isLt; omega⟩ : Fin n)) ?_ ?_ ?_
  · intro j _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · intro j₁ _ j₂ _ h
    exact Fin.ext (by simpa using congrArg Fin.val h)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    refine ⟨⟨i.val - a, by omega⟩, Finset.mem_univ _, ?_⟩
    exact Fin.ext (by simp; omega)

theorem omSigned_exists_refl_conj {p r : ℕ} {w : MulAut (Fin r → Multiplicative (ZMod p))}
    (hw : w ∈ omSigned p r) (x : OmPlusIdx r) :
    ∃ x' : OmPlusIdx r, omPlusRefl p x' = w * omPlusRefl p x * w⁻¹ := by
  have key : ∀ w : MulAut (Fin r → Multiplicative (ZMod p)), w ∈ omSigned p r →
      ∃ f : OmPlusIdx r → OmPlusIdx r,
        ∀ x, omPlusRefl p (f x) = w * omPlusRefl p x * w⁻¹ := by
    intro w hw
    refine Subgroup.closure_induction''
      (p := fun w _ => ∃ f : OmPlusIdx r → OmPlusIdx r,
        ∀ x, omPlusRefl p (f x) = w * omPlusRefl p x * w⁻¹) ?_ ?_ ?_ ?_ hw
    · rintro u (⟨σ, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨omPerm σ, omPerm_refl σ⟩
      · exact ⟨omTog i, omTog_refl i⟩
    · rintro u (⟨σ, rfl⟩ | ⟨i, rfl⟩)
      · refine ⟨omPerm σ⁻¹, fun x => ?_⟩
        rw [plh_permAut_inv]
        exact omPerm_refl σ⁻¹ x
      · refine ⟨omTog i, fun x => ?_⟩
        rw [plh_sgnAut_inv]
        exact omTog_refl i x
    · exact ⟨_root_.id, fun x => by simp⟩
    · rintro u v _ _ ⟨f, hf⟩ ⟨g, hg⟩
      refine ⟨f ∘ g, fun x => ?_⟩
      change omPlusRefl p (f (g x)) = (u * v) * omPlusRefl p x * (u * v)⁻¹
      rw [hf (g x), hg x, mul_inv_rev]
      group
  obtain ⟨f, hf⟩ := key w hw
  exact ⟨f x, hf x⟩

section Conj

variable {G : Type} [Group G] {p : ℕ} {Bs X : Subgroup G} (Φ : OrthFrameCore p Bs X)

theorem plh_orthDerived_conj {μ : Φ.V ≃ₗ[Φ.F] Φ.V}
    (hμ : μ ∈ TauCeti.QuadraticMap.orthogonalGroup Φ.Q) :
    (orthDerived Φ.Q).map (MulAut.conj μ).toMonoidHom = orthDerived Φ.Q := by
  have hH : (TauCeti.QuadraticMap.orthogonalGroup Φ.Q).map (MulAut.conj μ).toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup Φ.Q := by
    apply le_antisymm
    · rintro _ ⟨h, hh, rfl⟩
      exact mul_mem (mul_mem hμ hh) (inv_mem hμ)
    · intro h hh
      refine Subgroup.mem_map.mpr ⟨μ⁻¹ * h * μ, mul_mem (mul_mem (inv_mem hμ) hh) hμ, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  rw [show orthDerived Φ.Q = ⁅TauCeti.QuadraticMap.orthogonalGroup Φ.Q,
      TauCeti.QuadraticMap.orthogonalGroup Φ.Q⁆ from rfl]
  rw [Subgroup.map_commutator, hH]

theorem plh_centralizer_conj {t μ : Φ.V ≃ₗ[Φ.F] Φ.V} :
    (Subgroup.centralizer ({t} : Set (Φ.V ≃ₗ[Φ.F] Φ.V))).map
        (MulAut.conj μ).toMonoidHom =
      Subgroup.centralizer ({μ * t * μ⁻¹} : Set (Φ.V ≃ₗ[Φ.F] Φ.V)) := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    have hth : t * h = h * t := (Subgroup.mem_centralizer_iff.mp hh) t (by simp)
    calc (μ * t * μ⁻¹) * (μ * h * μ⁻¹) = μ * (t * h) * μ⁻¹ := by group
      _ = μ * (h * t) * μ⁻¹ := by rw [hth]
      _ = (μ * h * μ⁻¹) * (μ * t * μ⁻¹) := by group
  · intro hg
    rw [Subgroup.mem_centralizer_iff] at hg
    refine ⟨μ⁻¹ * g * μ, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      rw [ha]
      have h' : t * (μ⁻¹ * g * μ) = (μ⁻¹ * g * μ) * t := by
        have hg' : (μ * t * μ⁻¹) * g = g * (μ * t * μ⁻¹) := hg (μ * t * μ⁻¹) (by simp)
        calc t * (μ⁻¹ * g * μ) = μ⁻¹ * ((μ * t * μ⁻¹) * g) * μ := by group
          _ = μ⁻¹ * (g * (μ * t * μ⁻¹)) * μ := by rw [hg']
          _ = (μ⁻¹ * g * μ) * t := by group
      simpa using h'
    · ext v
      simp [LinearEquiv.mul_apply]

theorem plh_fixTorus_conj {μ : Φ.V ≃ₗ[Φ.F] Φ.V}
    {w : MulAut (Fin Φ.r → Multiplicative (ZMod p))}
    (hw : ∀ f, μ * Φ.Δ.τ f * μ⁻¹ = Φ.Δ.τ (w f)) {x x' : OmPlusIdx Φ.r}
    (hx : omPlusRefl p x' = w * omPlusRefl p x * w⁻¹) :
    Φ.fixTorus x' = (Φ.fixTorus x).map (MulAut.conj μ).toMonoidHom := by
  ext t
  constructor
  · intro ht
    rw [OrthFrameCore.fixTorus, Subgroup.mem_map] at ht
    obtain ⟨g, hg, rfl⟩ := ht
    change omPlusRefl p x' g = g at hg
    refine Subgroup.mem_map.mpr ⟨Φ.Δ.τ (w⁻¹ g), ?_, ?_⟩
    · rw [OrthFrameCore.fixTorus, Subgroup.mem_map]
      refine ⟨w⁻¹ g, ?_, rfl⟩
      change omPlusRefl p x (w⁻¹ g) = w⁻¹ g
      have h2 : omPlusRefl p x' g = w (omPlusRefl p x (w⁻¹ g)) := by
        rw [hx]
        simp only [MulAut.mul_apply, MulAut.inv_apply_self]
      have h3 : w (omPlusRefl p x (w⁻¹ g)) = g := h2 ▸ hg
      apply w.injective
      rw [h3, MulAut.apply_inv_self]
    · show (MulAut.conj μ) (Φ.Δ.τ (w⁻¹ g)) = Φ.Δ.τ g
      rw [MulAut.conj_apply, hw (w⁻¹ g), MulAut.apply_inv_self]
  · intro ht
    rw [Subgroup.mem_map] at ht
    obtain ⟨a, ha, rfl⟩ := ht
    rw [OrthFrameCore.fixTorus, Subgroup.mem_map] at ha
    obtain ⟨f, hf, rfl⟩ := ha
    change omPlusRefl p x f = f at hf
    rw [OrthFrameCore.fixTorus, Subgroup.mem_map]
    refine ⟨w f, ?_, ?_⟩
    · change omPlusRefl p x' (w f) = w f
      have h2 : omPlusRefl p x' (w f) = w (omPlusRefl p x f) := by
        rw [hx]
        simp only [MulAut.mul_apply, MulAut.inv_apply_self]
      rw [h2, hf]
    · show Φ.Δ.τ (w f) = (MulAut.conj μ) (Φ.Δ.τ f)
      rw [MulAut.conj_apply, hw f]

theorem plh_rank2_conj {μ : Φ.V ≃ₗ[Φ.F] Φ.V}
    (hμ : μ ∈ TauCeti.QuadraticMap.orthogonalGroup Φ.Q)
    {w : MulAut (Fin Φ.r → Multiplicative (ZMod p))}
    (hw : ∀ f, μ * Φ.Δ.τ f * μ⁻¹ = Φ.Δ.τ (w f)) {x y x' y' : OmPlusIdx Φ.r}
    (hx : omPlusRefl p x' = w * omPlusRefl p x * w⁻¹)
    (hy : omPlusRefl p y' = w * omPlusRefl p y * w⁻¹) :
    Φ.rank2 x' y' = (Φ.rank2 x y).map (MulAut.conj μ).toMonoidHom := by
  haveI : Finite (Φ.V ≃ₗ[Φ.F] Φ.V) := Φ.finite_linearEquiv
  have hfixx := plh_fixTorus_conj (Φ := Φ) hw hx
  have hfixy := plh_fixTorus_conj (Φ := Φ) hw hy
  have hder := plh_orthDerived_conj (Φ := Φ) hμ
  have hfixxy : Φ.fixTorus x' ⊓ Φ.fixTorus y' =
      (Φ.fixTorus x ⊓ Φ.fixTorus y).map (MulAut.conj μ).toMonoidHom := by
    rw [hfixx, hfixy, Subgroup.map_inf _ _ _ (MulAut.conj μ).injective]
  unfold OrthFrameCore.rank2
  rw [ggOTwoPrime_map_conj μ (orthDerived Φ.Q ⊓ Subgroup.centralizer
      ((Φ.fixTorus x ⊓ Φ.fixTorus y : Subgroup (Φ.V ≃ₗ[Φ.F] Φ.V)) :
        Set (Φ.V ≃ₗ[Φ.F] Φ.V))),
    Subgroup.map_inf _ _ _ (MulAut.conj μ).injective,
    ggMap_conj_centralizer μ (Φ.fixTorus x ⊓ Φ.fixTorus y), hder, ← hfixxy]

theorem plh_torC_conj {t μ : Φ.V ≃ₗ[Φ.F] Φ.V}
    (hμ : μ ∈ TauCeti.QuadraticMap.orthogonalGroup Φ.Q) :
    (Φ.torC t).map (MulAut.conj μ).toMonoidHom = Φ.torC (μ * t * μ⁻¹) := by
  rw [OrthFrameCore.torC, OrthFrameCore.torC,
    Subgroup.map_inf _ _ _ (MulAut.conj μ).injective]
  congr 1
  · exact plh_orthDerived_conj (Φ := Φ) hμ
  · exact plh_centralizer_conj (Φ := Φ) (t := t) (μ := μ)

theorem plh_torFactor_map_conj {μ : Φ.V ≃ₗ[Φ.F] Φ.V}
    {w : MulAut (Fin Φ.r → Multiplicative (ZMod p))}
    (hμ : μ ∈ TauCeti.QuadraticMap.orthogonalGroup Φ.Q)
    (hw : ∀ f, μ * Φ.Δ.τ f * μ⁻¹ = Φ.Δ.τ (w f)) (hws : w ∈ omSigned p Φ.r)
    {P' : Subgroup (Φ.V ≃ₗ[Φ.F] Φ.V)} (h : Φ.TorFactor P') :
    Φ.TorFactor (P'.map (MulAut.conj μ⁻¹).toMonoidHom) := by
  classical
  let e' : ↥P' ≃* ↥(P'.map (MulAut.conj μ⁻¹).toMonoidHom) :=
    P'.equivMapOfInjective (MulAut.conj μ⁻¹).toMonoidHom (MulAut.conj μ⁻¹).injective
  rcases h with hsol | ⟨hqs, ⟨lab, hΛ, hhas, hn, htag, htwD⟩, hxy⟩
  · left
    exact Group.isSolvable_of_isSolvable_injective (f := e'.symm.toMonoidHom)
      e'.symm.injective
  · right
    obtain ⟨x', y', hnc', hrank2'⟩ := hxy
    refine ⟨IsQuasisimple.of_mulEquiv e'.symm hqs,
      ⟨lab, hΛ, ?_, hn, htag, htwD⟩, ?_⟩
    · exact ggHasLabel_of_mulEquiv
        (QuotientGroup.congr _ _ e' (Subgroup.map_center_eq e')) hhas
    · obtain ⟨x, hx⟩ := omSigned_exists_refl_conj ((omSigned p Φ.r).inv_mem hws) x'
      obtain ⟨y, hy⟩ := omSigned_exists_refl_conj ((omSigned p Φ.r).inv_mem hws) y'
      have hx' : omPlusRefl p x' = w * omPlusRefl p x * w⁻¹ := by rw [hx]; group
      have hy' : omPlusRefl p y' = w * omPlusRefl p y * w⁻¹ := by rw [hy]; group
      have hnc : omPlusRefl p x * omPlusRefl p y ≠ omPlusRefl p y * omPlusRefl p x := by
        intro hc
        apply hnc'
        calc omPlusRefl p x' * omPlusRefl p y'
            = w * (omPlusRefl p x * omPlusRefl p y) * w⁻¹ := by rw [hx', hy']; group
          _ = w * (omPlusRefl p y * omPlusRefl p x) * w⁻¹ := by rw [hc]
          _ = omPlusRefl p y' * omPlusRefl p x' := by rw [hx', hy']; group
      have hrank2 : Φ.rank2 x y ≤ P'.map (MulAut.conj μ⁻¹).toMonoidHom := by
        intro g hg
        have h1 : (MulAut.conj μ) g ∈ Φ.rank2 x' y' := by
          rw [plh_rank2_conj (Φ := Φ) hμ hw hx' hy']
          exact ⟨g, hg, rfl⟩
        exact Subgroup.mem_map.mpr ⟨(MulAut.conj μ) g, hrank2' h1, by
          show (MulAut.conj μ⁻¹) ((MulAut.conj μ) g) = g
          rw [MulAut.conj_apply, MulAut.conj_apply]
          group⟩
      exact ⟨x, y, hnc, hrank2⟩

end Conj

end OrthTorus

end CFSG.StandardType

end
