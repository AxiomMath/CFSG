module

public import CFSG.LocalAnalysis.StandardType.GGRealKGSignedRefl
public import CFSG.LocalAnalysis.StandardType.GGKGForkTransfer
public import CFSG.LocalAnalysis.StandardType.GGRealKGTorusComponentsDefs

public section

namespace CFSG.StandardType

namespace RealKGModelRoot

open CFSG.Assembly Multiplicative SpCoord

variable {p k : ℕ} {R : Type} [Group R]

private def indAut (τ : (Fin k → Multiplicative (ZMod p)) →* R) :
    Subgroup (MulAut (Fin k → Multiplicative (ZMod p))) where
  carrier := {u | ∃ g : R, ∀ f, g * τ f * g⁻¹ = τ (u f)}
  one_mem' := ⟨1, fun f => by simp⟩
  mul_mem' := by
    rintro u v ⟨g, hg⟩ ⟨h, hh⟩
    refine ⟨g * h, fun f => ?_⟩
    rw [MulAut.mul_apply, ← hg, ← hh]
    group
  inv_mem' := by
    rintro u ⟨g, hg⟩
    refine ⟨g⁻¹, fun f => ?_⟩
    have h := hg (u⁻¹ f)
    rw [MulAut.apply_inv_self] at h
    rw [← h]
    group

private theorem finite_mulAut (hp : p.Prime) :
    Finite (MulAut (Fin k → Multiplicative (ZMod p))) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  exact Finite.of_injective (fun u : MulAut (Fin k → Multiplicative (ZMod p)) =>
    (⇑u : (Fin k → Multiplicative (ZMod p)) → (Fin k → Multiplicative (ZMod p))))
    DFunLike.coe_injective

theorem exists_inducedAut (hp : p.Prime) {E : Subgroup R}
    {τ : (Fin k → Multiplicative (ZMod p)) →* R} (hτ : Function.Injective τ)
    (hτE : τ.range = E) {g : R} (hg : g ∈ Subgroup.normalizer (E : Set R)) :
    ∃ u : MulAut (Fin k → Multiplicative (ZMod p)), ∀ f, g * τ f * g⁻¹ = τ (u f) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hmem : ∀ f, (MulAut.conj g).toMonoidHom (τ f) ∈ τ.range := fun f => by
    rw [hτE]
    exact (Subgroup.mem_normalizer_iff.mp hg (τ f)).mp (by rw [← hτE]; exact ⟨f, rfl⟩)
  let φ : (Fin k → Multiplicative (ZMod p)) →* (Fin k → Multiplicative (ZMod p)) :=
    (MonoidHom.ofInjective hτ).symm.toMonoidHom.comp
      (((MulAut.conj g).toMonoidHom.comp τ).codRestrict τ.range hmem)
  have hφ : ∀ f, τ (φ f) = g * τ f * g⁻¹ := fun f => by
    have h := congrArg Subtype.val ((MonoidHom.ofInjective hτ).apply_symm_apply ⟨_, hmem f⟩)
    rw [MonoidHom.ofInjective_apply] at h
    exact h
  have hinj : Function.Injective φ := fun a b hab => hτ (by
    have h := congrArg τ hab
    rw [hφ, hφ] at h
    exact mul_left_cancel (mul_right_cancel h))
  exact ⟨MulEquiv.ofBijective φ (Finite.injective_iff_bijective.mp hinj), fun f => (hφ f).symm⟩

theorem isSignedPerm_of_coords (hp : p.Prime) {τ τ' : (Fin k → Multiplicative (ZMod p)) →* R}
    (hτ : Function.Injective τ) (hτ' : Function.Injective τ') (hr : τ'.range = τ.range)
    (h' : ∀ (g : R) (u : MulAut (Fin k → Multiplicative (ZMod p))),
      (∀ f, g * τ' f * g⁻¹ = τ' (u f)) → IsSignedPerm ⇑u)
    (hs : ∀ i : Fin k, ∃ g : R, ∀ f, g * τ f * g⁻¹ = τ (sgnAut i f))
    (ht : ∀ a b : Fin k, a ≠ b → ∃ g : R, ∀ f, g * τ f * g⁻¹ = τ (permAut (Equiv.swap a b) f))
    {g : R} {u : MulAut (Fin k → Multiplicative (ZMod p))} (hgu : ∀ f, g * τ f * g⁻¹ = τ (u f)) :
    IsSignedPerm ⇑u := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI := finite_mulAut (k := k) hp
  let ψ : MulAut (Fin k → Multiplicative (ZMod p)) :=
    ((MonoidHom.ofInjective hτ).trans (MulEquiv.subgroupCongr hr.symm)).trans
      (MonoidHom.ofInjective hτ').symm
  have hψ : ∀ f, τ' (ψ f) = τ f := by
    intro f
    have h := congrArg Subtype.val ((MonoidHom.ofInjective hτ').apply_symm_apply
      ((MulEquiv.subgroupCongr hr.symm) (MonoidHom.ofInjective hτ f)))
    rw [MonoidHom.ofInjective_apply] at h
    exact h
  have hconj : ∀ v ∈ (indAut τ : Set (MulAut (Fin k → Multiplicative (ZMod p)))),
      IsSignedPerm ⇑(ψ * v * ψ⁻¹) := by
    rintro v ⟨h, hh⟩
    refine h' h _ fun x => ?_
    have hx : τ' x = τ (ψ⁻¹ x) := by rw [← hψ, MulAut.apply_inv_self]
    rw [hx, hh, ← hψ, MulAut.mul_apply, MulAut.mul_apply]
  have hSP : {v : MulAut (Fin k → Multiplicative (ZMod p)) | IsSignedPerm ⇑v} ⊆
      (indAut τ : Set (MulAut (Fin k → Multiplicative (ZMod p)))) := fun v hv =>
    mem_of_isSignedPerm (H := indAut τ) hs ht hv
  have hle : (indAut τ : Set (MulAut (Fin k → Multiplicative (ZMod p)))).ncard ≤
      {v : MulAut (Fin k → Multiplicative (ZMod p)) | IsSignedPerm ⇑v}.ncard :=
    Set.ncard_le_ncard_of_injOn (fun v => ψ * v * ψ⁻¹) hconj
      (fun a _ b _ hab => by simpa using hab)
  have heq := Set.eq_of_subset_of_ncard_le hSP hle
  have hu : u ∈ (indAut τ : Set (MulAut (Fin k → Multiplicative (ZMod p)))) := ⟨g, hgu⟩
  rw [← heq] at hu
  exact hu

private theorem commutator_eq_self_of_isComponentOf {J K : Subgroup R} (h : IsComponentOf J K) :
    ⁅J, J⁆ = J := by
  have h1 := Subgroup.map_subtype_commutator J
  rw [h.2.2.1, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
  exact h1.symm

private theorem ggKGComponentDatumAt_of_model_core (hp : p.Prime) {E : Subgroup R}
    {τ : (Fin k → Multiplicative (ZMod p)) →* R} (hτ : Function.Injective τ) (hτE : τ.range = E)
    {ι : Type} (w : ι → R) (s : ι → MulAut (Fin k → Multiplicative (ZMod p)))
    (S : ι → Subgroup R) (hws : ∀ i f, w i * τ f * (w i)⁻¹ = τ (s i f)) (hwS : ∀ i, w i ∈ S i)
    (hcomp : ∀ i, IsComponentOf (S i) (Subgroup.centralizer (τ '' {f | s i f = f})))
    (hdvd : ∀ i, p ∣ Nat.card (S i))
    (hcover : ∀ (g : R) (u : MulAut (Fin k → Multiplicative (ZMod p))),
      (∀ f, g * τ f * g⁻¹ = τ (u f)) → u * u = 1 →
      Nat.card {f // u f = f} * p = Nat.card (Fin k → Multiplicative (ZMod p)) → ∃ i, s i = u) :
    ∀ w₀ : R, GGKGIsReflAt p E w₀ →
      ∃ (w : R) (J : Subgroup R), (∀ e ∈ E, w * e * w⁻¹ = w₀ * e * w₀⁻¹) ∧
        w ∈ J ∧ IsComponentOf J
          (Subgroup.centralizer ((E ⊓ Subgroup.centralizer ({w} : Set R) : Subgroup R) : Set R)) ∧
        p ∣ Nat.card J ∧
        (∀ (hlayer : ∀ a ∈ E, ∀ J : Subgroup R, ⁅J, J⁆ = J →
            J ≤ Subgroup.centralizer ({a} : Set R) →
              J ≤ LargeEvenLayer (Subgroup.centralizer ({a} : Set R))),
          ∀ a ∈ E, w * a = a * w →
            J ≤ LargeEvenLayer (Subgroup.centralizer ({a} : Set R))) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hτmem : ∀ f, τ f ∈ E := fun f => by rw [← hτE]; exact ⟨f, rfl⟩
  rintro w₀ ⟨hnorm, hinv, hfix⟩
  obtain ⟨u, hu⟩ := exists_inducedAut hp hτ hτE hnorm
  have hu2 : u * u = 1 := by
    refine MulEquiv.ext fun f => hτ ?_
    rw [MulAut.mul_apply, MulAut.one_apply, ← hu, ← hu]
    exact hinv _ (hτmem f)
  let eE : (Fin k → Multiplicative (ZMod p)) ≃* E :=
    (MonoidHom.ofInjective hτ).trans (MulEquiv.subgroupCongr hτE)
  have hfix' : Nat.card {f // u f = f} * p = Nat.card (Fin k → Multiplicative (ZMod p)) := by
    have h1 : Nat.card {f // u f = f} = Nat.card {e : E // w₀ * (e : R) * w₀⁻¹ = e} := by
      refine Nat.card_congr (Equiv.subtypeEquiv eE.toEquiv fun f => ?_)
      change u f = f ↔ w₀ * τ f * w₀⁻¹ = τ f
      rw [hu]
      exact hτ.eq_iff.symm
    rw [h1, hfix]
    exact Nat.card_congr eE.toEquiv.symm
  obtain ⟨i, hi⟩ := hcover w₀ u hu hu2 hfix'
  have hinf : ((E ⊓ Subgroup.centralizer ({w i} : Set R) : Subgroup R) : Set R) =
      τ '' {f | s i f = f} := by
    ext x
    constructor
    · rintro ⟨hxE, hxc⟩
      rw [← hτE] at hxE
      obtain ⟨f, rfl⟩ := hxE
      refine ⟨f, hτ ?_, rfl⟩
      rw [← hws i f, mul_inv_eq_iff_eq_mul]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hxc).symm
    · rintro ⟨f, hf, rfl⟩
      refine ⟨hτmem f, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have h := hws i f
      rw [show s i f = f from hf, mul_inv_eq_iff_eq_mul] at h
      exact h.symm
  refine ⟨w i, S i, ?_, hwS i, ?_, hdvd i, ?_⟩
  · intro e he
    rw [← hτE] at he
    obtain ⟨f, rfl⟩ := he
    rw [hws, hu, hi]
  · rw [hinf]
    exact hcomp i
  · intro hlayer a ha haw
    have haS : a ∈ τ '' {f | s i f = f} := by
      rw [← hinf]
      exact ⟨ha, Subgroup.mem_centralizer_singleton_iff.mpr haw.symm⟩
    refine hlayer a ha (S i) (commutator_eq_self_of_isComponentOf (hcomp i)) fun x hx => ?_
    have hxc := Subgroup.mem_centralizer_iff.mp ((hcomp i).1 hx) a haS
    exact Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Set.mem_singleton_iff.mp hy]
      exact hxc

theorem ggKGComponentDatumAt_of_model (hp : p.Prime) {E : Subgroup R}
    {τ : (Fin k → Multiplicative (ZMod p)) →* R} (hτ : Function.Injective τ) (hτE : τ.range = E)
    {ι : Type} (w : ι → R) (s : ι → MulAut (Fin k → Multiplicative (ZMod p)))
    (S : ι → Subgroup R) (hws : ∀ i f, w i * τ f * (w i)⁻¹ = τ (s i f)) (hwS : ∀ i, w i ∈ S i)
    (hcomp : ∀ i, IsComponentOf (S i) (Subgroup.centralizer (τ '' {f | s i f = f})))
    (hdvd : ∀ i, p ∣ Nat.card (S i))
    (hcover : ∀ (g : R) (u : MulAut (Fin k → Multiplicative (ZMod p))),
      (∀ f, g * τ f * g⁻¹ = τ (u f)) → u * u = 1 →
      Nat.card {f // u f = f} * p = Nat.card (Fin k → Multiplicative (ZMod p)) → ∃ i, s i = u) :
    GGKGComponentDatumAt p E := by
  intro w₀ hw₀
  obtain ⟨w, J, hw, hwJ, hcompJ, hdvdJ, -⟩ :=
    ggKGComponentDatumAt_of_model_core hp hτ hτE w s S hws hwS hcomp hdvd hcover w₀ hw₀
  exact ⟨w, hw, J, hwJ, hcompJ, hdvdJ⟩

theorem ggKGRootDatumAt_of_model (hp : p.Prime) {E : Subgroup R}
    {τ : (Fin k → Multiplicative (ZMod p)) →* R} (hτ : Function.Injective τ) (hτE : τ.range = E)
    {ι : Type} (w : ι → R) (s : ι → MulAut (Fin k → Multiplicative (ZMod p)))
    (S : ι → Subgroup R) (hws : ∀ i f, w i * τ f * (w i)⁻¹ = τ (s i f)) (hwS : ∀ i, w i ∈ S i)
    (hcomp : ∀ i, IsComponentOf (S i) (Subgroup.centralizer (τ '' {f | s i f = f})))
    (hdvd : ∀ i, p ∣ Nat.card (S i))
    (hcover : ∀ (g : R) (u : MulAut (Fin k → Multiplicative (ZMod p))),
      (∀ f, g * τ f * g⁻¹ = τ (u f)) → u * u = 1 →
      Nat.card {f // u f = f} * p = Nat.card (Fin k → Multiplicative (ZMod p)) → ∃ i, s i = u)
    (hlayer : ∀ a ∈ E, ∀ J : Subgroup R, ⁅J, J⁆ = J →
      J ≤ Subgroup.centralizer ({a} : Set R) →
        J ≤ LargeEvenLayer (Subgroup.centralizer ({a} : Set R))) :
    GGKGRootDatumAt p E := by
  intro w₀ hw₀
  obtain ⟨w, J, hw, hwJ, hcompJ, hdvdJ, hlay⟩ :=
    ggKGComponentDatumAt_of_model_core hp hτ hτE w s S hws hwS hcomp hdvd hcover w₀ hw₀
  exact ⟨w, hw, J, hwJ, hcompJ, hdvdJ, hlay hlayer⟩

theorem ggKGRootDatumAt_of_signedModel (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup R}
    {τ τ' : (Fin k → Multiplicative (ZMod p)) →* R} (hτ : Function.Injective τ)
    (hτE : τ.range = E) (hτ' : Function.Injective τ') (hτ'E : τ'.range = E)
    (h' : ∀ g : R, (∀ e ∈ E, g * e * g⁻¹ ∈ E) →
      ∃ (π : Equiv.Perm (Fin k)) (ε : Fin k → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
        ∀ f f', g * τ' f * g⁻¹ = τ' f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i))
    (w : OmPlusIdx k ⊕ Fin k → R) (S : OmPlusIdx k ⊕ Fin k → Subgroup R)
    (hws : ∀ i f, w i * τ f * (w i)⁻¹ = τ (Sum.elim (omPlusRefl p) sgnAut i f))
    (hwS : ∀ i, w i ∈ S i)
    (hcomp : ∀ i, IsComponentOf (S i)
      (Subgroup.centralizer (τ '' {f | Sum.elim (omPlusRefl p) sgnAut i f = f})))
    (hdvd : ∀ i, p ∣ Nat.card (S i))
    (hlayer : ∀ a ∈ E, ∀ J : Subgroup R, ⁅J, J⁆ = J →
      J ≤ Subgroup.centralizer ({a} : Set R) →
        J ≤ LargeEvenLayer (Subgroup.centralizer ({a} : Set R))) :
    GGKGRootDatumAt p E := by
  refine ggKGRootDatumAt_of_model hp hτ hτE w _ S hws hwS hcomp hdvd ?_ hlayer
  intro g u hgu hu2 hfix
  have h'' : ∀ (g : R) (u : MulAut (Fin k → Multiplicative (ZMod p))),
      (∀ f, g * τ' f * g⁻¹ = τ' (u f)) → IsSignedPerm ⇑u := by
    intro g u hgu'
    obtain ⟨π, ε, hε, hπ⟩ := h' g fun e he => by
      rw [← hτ'E] at he ⊢
      obtain ⟨f, rfl⟩ := he
      exact ⟨u f, (hgu' f).symm⟩
    exact ⟨π, ε, hε, fun f i => hπ f (u f) (hgu' f) i⟩
  have hs : ∀ i : Fin k, ∃ g : R, ∀ f, g * τ f * g⁻¹ = τ (sgnAut i f) :=
    fun i => ⟨w (Sum.inr i), hws (Sum.inr i)⟩
  have ht : ∀ a b : Fin k, a ≠ b →
      ∃ g : R, ∀ f, g * τ f * g⁻¹ = τ (permAut (Equiv.swap a b) f) := by
    intro a b hab
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨w (Sum.inl (⟨(a, b), h⟩, false)), hws (Sum.inl (⟨(a, b), h⟩, false))⟩
    · rw [Equiv.swap_comm]
      exact ⟨w (Sum.inl (⟨(b, a), h⟩, false)), hws (Sum.inl (⟨(b, a), h⟩, false))⟩
  have hsp := isSignedPerm_of_coords hp hτ hτ' (hτ'E.trans hτE.symm) h'' hs ht hgu
  rcases RealKGSignedRefl.signedRefl_cases hp hp2 hsp hu2 hfix with ⟨a, ha⟩ | ⟨x, hx⟩
  · exact ⟨Sum.inr a, ha.symm⟩
  · exact ⟨Sum.inl x, hx.symm⟩

theorem ggKGComponentDatumAt_of_signedModel (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup R}
    {τ τ' : (Fin k → Multiplicative (ZMod p)) →* R} (hτ : Function.Injective τ)
    (hτE : τ.range = E) (hτ' : Function.Injective τ') (hτ'E : τ'.range = E)
    (h' : ∀ g : R, (∀ e ∈ E, g * e * g⁻¹ ∈ E) →
      ∃ (π : Equiv.Perm (Fin k)) (ε : Fin k → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
        ∀ f f', g * τ' f * g⁻¹ = τ' f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i))
    (w : OmPlusIdx k ⊕ Fin k → R) (S : OmPlusIdx k ⊕ Fin k → Subgroup R)
    (hws : ∀ i f, w i * τ f * (w i)⁻¹ = τ (Sum.elim (omPlusRefl p) sgnAut i f))
    (hwS : ∀ i, w i ∈ S i)
    (hcomp : ∀ i, IsComponentOf (S i)
      (Subgroup.centralizer (τ '' {f | Sum.elim (omPlusRefl p) sgnAut i f = f})))
    (hdvd : ∀ i, p ∣ Nat.card (S i)) :
    GGKGComponentDatumAt p E := by
  refine ggKGComponentDatumAt_of_model hp hτ hτE w _ S hws hwS hcomp hdvd ?_
  intro g u hgu hu2 hfix
  have h'' : ∀ (g : R) (u : MulAut (Fin k → Multiplicative (ZMod p))),
      (∀ f, g * τ' f * g⁻¹ = τ' (u f)) → IsSignedPerm ⇑u := by
    intro g u hgu'
    obtain ⟨π, ε, hε, hπ⟩ := h' g fun e he => by
      rw [← hτ'E] at he ⊢
      obtain ⟨f, rfl⟩ := he
      exact ⟨u f, (hgu' f).symm⟩
    exact ⟨π, ε, hε, fun f i => hπ f (u f) (hgu' f) i⟩
  have hs : ∀ i : Fin k, ∃ g : R, ∀ f, g * τ f * g⁻¹ = τ (sgnAut i f) :=
    fun i => ⟨w (Sum.inr i), hws (Sum.inr i)⟩
  have ht : ∀ a b : Fin k, a ≠ b →
      ∃ g : R, ∀ f, g * τ f * g⁻¹ = τ (permAut (Equiv.swap a b) f) := by
    intro a b hab
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨w (Sum.inl (⟨(a, b), h⟩, false)), hws (Sum.inl (⟨(a, b), h⟩, false))⟩
    · rw [Equiv.swap_comm]
      exact ⟨w (Sum.inl (⟨(b, a), h⟩, false)), hws (Sum.inl (⟨(b, a), h⟩, false))⟩
  have hsp := isSignedPerm_of_coords hp hτ hτ' (hτ'E.trans hτE.symm) h'' hs ht hgu
  rcases RealKGSignedRefl.signedRefl_cases hp hp2 hsp hu2 hfix with ⟨a, ha⟩ | ⟨x, hx⟩
  · exact ⟨Sum.inr a, ha.symm⟩
  · exact ⟨Sum.inl x, hx.symm⟩

end RealKGModelRoot

end CFSG.StandardType

end
