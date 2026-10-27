module

public import CFSG.Timmesfeld.Bridge.RootSetsConn7

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity

@[expose] def Step6ThreeProductHyp : Prop :=
  ∀ (G : Type) [Group G] (D : Set G) (a b c x z : G) (P : Subgroup G), ConnCex D →
    Step6 D a b c x z P → Step6ThreeProduct D x P

variable {G : Type} [Group G] {D : Set G}

namespace Step6

variable {a b c x z : G} {P : Subgroup G}

theorem conj (hC : ConnCex D) (h : Step6 D a b c x z P) {g : G}
    (hg : g ∈ Subgroup.normalizer (P : Set G)) :
    Step6 D (g * a * g⁻¹) (g * b * g⁻¹) (g * c * g⁻¹) (g * x * g⁻¹) (g * z * g⁻¹) P := by
  have hN := hC.setting.normal
  have hP : ∀ p, p ∈ P ↔ g * p * g⁻¹ ∈ P := fun p => Subgroup.mem_normalizer_iff.1 hg p
  have hP' : ∀ p, p ∈ P → g⁻¹ * p * g ∈ P := fun p hp => by
    rw [hP]
    simpa [mul_assoc] using hp
  have hinj : ∀ u v : G, g * u * g⁻¹ = g * v * g⁻¹ → u = v := fun u v huv =>
    mul_left_cancel (mul_right_cancel huv)
  refine ⟨⟨hN g a h.ha, hN g b h.hb, hN g c h.hc, hN g x h.hx, fun huv => h.hab (hinj a b huv),
    (Commute.conj_iff g).2 h.hcab, (Commute.conj_iff g).2 h.hca, (Commute.conj_iff g).2 h.hcb,
    fun hD => h.hnD ?_, reach_conj hN g h.hac, fun hr => h.hax ?_, ?_,
    fun h1 => h.hz1 ?_, (Commute.conj_iff g).2 h.hxz⟩, h.hP2, (hP a).1 h.haP, (hP b).1 h.hbP,
    (hP c).1 h.hcP, ?_, ?_, ?_, h.hPL⟩
  · have := hN g⁻¹ _ hD
    simpa [mul_assoc] using this
  · have := reach_conj hN g⁻¹ hr
    simpa [mul_assoc] using this
  · rw [h.hz]
    group
  · have := congrArg (fun w => g⁻¹ * w * g) h1
    simpa [mul_assoc] using this
  · intro p hp
    have hp' := hP' p hp
    have hc := Subgroup.mem_centralizer_singleton_iff.1 (h.hPz hp')
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := (Commute.conj_iff g).2 (show Commute (g⁻¹ * p * g) z from hc)
    simpa [mul_assoc] using this.eq
  · intro y hy hyL
    have hy' : g⁻¹ * y * g ∈ D := by simpa using hN g⁻¹ y hy
    have hmem := h.hcent _ hy' fun l hl hlP => by
      have hc := hyL (g * l * g⁻¹) (hN g l hl) ((hP l).1 hlP)
      have := (Commute.conj_iff g⁻¹).2 hc
      simpa [mul_assoc] using this
    have := (hP _).1 hmem
    simpa [mul_assoc] using this
  · obtain ⟨e, he, f, hf, heP, hfP, hef, hefD⟩ := h.hLL
    refine ⟨g * e * g⁻¹, hN g e he, g * f * g⁻¹, hN g f hf, (hP e).1 heP, (hP f).1 hfP,
      fun h' => hef (hinj e f h'), ?_⟩
    have := hN g _ hefD
    simpa [mul_assoc] using this

end Step6

theorem lsub_conj (hN : IsNormalSet D) {x : G} {P : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (P : Set G)) :
    lsub D (g * x * g⁻¹) P = (lsub D x P).map (MulAut.conj g).toMonoidHom := by
  have hP : ∀ p, p ∈ P ↔ g * p * g⁻¹ ∈ P := fun p => Subgroup.mem_normalizer_iff.1 hg p
  have hSS : (MulAut.conj g).toMonoidHom '' {y | y ∈ D ∧ y ∈ P} = {y | y ∈ D ∧ y ∈ P} := by
    ext y
    constructor
    · rintro ⟨w, ⟨hw, hwP⟩, rfl⟩
      exact ⟨hN g w hw, (hP w).1 hwP⟩
    · rintro ⟨hy, hyP⟩
      refine ⟨g⁻¹ * y * g, ⟨by simpa using hN g⁻¹ y hy, ?_⟩, by simp [mul_assoc]⟩
      rw [hP]
      simpa [mul_assoc] using hyP
  rw [lsub, lsub, MonoidHom.map_closure, Set.image_insert_eq, hSS]
  rfl

theorem qcore_conj (hN : IsNormalSet D) {x : G} {P : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (P : Set G)) :
    qcore D (g * x * g⁻¹) P = (qcore D x P).map (MulAut.conj g).toMonoidHom := by
  set X := lsub D x P
  have hXX := lsub_conj hN (x := x) hg
  let e : X ≃* lsub D (g * x * g⁻¹) P :=
    ((MulAut.conj g).subgroupMap X).trans (MulEquiv.subgroupCongr hXX.symm)
  have hcore := CFSG.pCore_map_iso 2 e
  rw [qcore, qcore, ← hcore, Subgroup.map_map, Subgroup.map_map]
  congr 1

namespace Step6

variable {a b c x z : G} {P : Subgroup G}

theorem conj_mul_mem_qcore (hB : OddTranspBender) (h3 : Step6ThreeProductHyp) (hC : ConnCex D)
    (h : Step6 D a b c x z P) {g : G} (hg : g ∈ Subgroup.normalizer (P : Set G)) {e f : G}
    (he : e ∈ D) (hf : f ∈ D) (heP : e ∈ P) (hfP : f ∈ P) (hq : e * f ∈ qcore D x P) :
    g * e * g⁻¹ * (g * f * g⁻¹) ∈ qcore D x P := by
  have hN := hC.setting.normal
  have hP : ∀ p, p ∈ P ↔ g * p * g⁻¹ ∈ P := fun p => Subgroup.mem_normalizer_iff.1 hg p
  have h' := h.conj hC hg
  have hq' : g * e * g⁻¹ * (g * f * g⁻¹) ∈ qcore D (g * x * g⁻¹) P := by
    rw [qcore_conj hN hg]
    exact ⟨e * f, hq, by simp [mul_assoc]⟩
  exact h'.mul_mem_qcore_of_mul_mem_qcore hB hC h (h3 G D _ _ _ _ _ P hC h') (hN g e he)
    (hN g f hf) ((hP e).1 heP) ((hP f).1 hfP) hq'

end Step6

end CFSG.Timmesfeld.Bridge
