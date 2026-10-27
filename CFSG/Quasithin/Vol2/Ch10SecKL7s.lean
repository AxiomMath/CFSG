module

public import CFSG.Quasithin.Vol2.Ch10SecKL7q

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KL7

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

variable {W : Type} [CommGroup W]

namespace Hyp

variable {Mb L₁ L₂ R : Subgroup (MulAut W)} {W₁ W₂ : Subgroup W} {τ : MulAut W}
variable (h : Hyp Mb L₁ L₂ W₁ W₂ τ) (hR : RHyp Mb L₁ L₂ R) (c₁ : Coord L₁ W₁)
variable {S : Subgroup (MulAut W)} {t : MulAut W}
variable (hSM : S ≤ Mb) (htS : t ∈ S) (htK : t ∉ Subgroup.normalizer (L₁ : Set (MulAut W)))
variable (hSK : ∀ s ∈ S, s ∈ Subgroup.normalizer (L₁ : Set (MulAut W)) →
  ∃ p ∈ U3.map c₁.phi, p⁻¹ * s ∈ Subgroup.centralizer (L₁ : Set (MulAut W)))

theorem A₁_le : EE.map c₁.phi ⊔ Subgroup.zpowers (c₁.phi gq) ≤ L₁ :=
  sup_le (c₁.E_le_P.trans c₁.P_le) (Subgroup.zpowers_le.2 (c₁.phi_mem gq))

include h

omit h in
include hSK in
theorem conj_mem_A₁ {s : MulAut W} (hs : s ∈ S)
    (hsN : s ∈ Subgroup.normalizer (L₁ : Set (MulAut W))) {x : MulAut W}
    (hx : x ∈ EE.map c₁.phi ⊔ Subgroup.zpowers (c₁.phi gq)) :
    s * x * s⁻¹ ∈ EE.map c₁.phi ⊔ Subgroup.zpowers (c₁.phi gq) := by
  obtain ⟨p, hp, hpy⟩ := hSK s hs hsN
  have hy := Subgroup.mem_centralizer_iff.1 hpy x (A₁_le c₁ hx)
  have h1 : s * x * s⁻¹ = p * x * p⁻¹ := by
    have e1 : s = p * (p⁻¹ * s) := by group
    rw [e1, show p * (p⁻¹ * s) * x * (p * (p⁻¹ * s))⁻¹ = p * ((p⁻¹ * s) * x) * (p⁻¹ * s)⁻¹ * p⁻¹
      by group, ← hy]
    group
  rw [h1]
  exact c₁.P_conj_A hp hx

include hR hSM htS htK hSK in
theorem conj_mem_D {s : MulAut W} (hs : s ∈ S) {x : MulAut W}
    (hx : x ∈ (EE.map c₁.phi ⊔ Subgroup.zpowers (c₁.phi gq)) ⊔
      (EE.map c₁.phi ⊔ Subgroup.zpowers (c₁.phi gq)).map (MulAut.conj t).toMonoidHom ⊔ R) :
    s * x * s⁻¹ ∈ (EE.map c₁.phi ⊔ Subgroup.zpowers (c₁.phi gq)) ⊔
      (EE.map c₁.phi ⊔ Subgroup.zpowers (c₁.phi gq)).map (MulAut.conj t).toMonoidHom ⊔ R := by
  set A₁ := EE.map c₁.phi ⊔ Subgroup.zpowers (c₁.phi gq) with hA₁
  set A₂ := A₁.map (MulAut.conj t).toMonoidHom with hA₂
  have htM : t ∈ Mb := hSM htS
  have hKA₂ : ∀ s ∈ S, s ∈ Subgroup.normalizer (L₁ : Set (MulAut W)) → ∀ x ∈ A₂,
      s * x * s⁻¹ ∈ A₂ := by
    intro s hs hsN x hx
    obtain ⟨a, ha, rfl⟩ := hx
    have hs' : t⁻¹ * s * t ∈ S := mul_mem (mul_mem (S.inv_mem htS) hs) htS
    have hsN' : t⁻¹ * s * t ∈ Subgroup.normalizer (L₁ : Set (MulAut W)) := by
      have := h.conj_mem_K (Mb.inv_mem htM) (hSM hs) hsN
      simpa using this
    have h1 := conj_mem_A₁ c₁ hSK hs' hsN' ha
    refine ⟨_, h1, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hKD : ∀ s ∈ S, s ∈ Subgroup.normalizer (L₁ : Set (MulAut W)) → ∀ x ∈ A₁ ⊔ A₂ ⊔ R,
      s * x * s⁻¹ ∈ A₁ ⊔ A₂ ⊔ R := by
    intro s hs hsN x hx
    refine conj_mem_sup_of (fun y hy => Subgroup.mem_sup_left ?_) (fun r hr =>
      Subgroup.mem_sup_right (hR.normal s (hSM hs) r hr)) hx
    exact conj_mem_sup_of (fun a ha => Subgroup.mem_sup_left (conj_mem_A₁ c₁ hSK hs hsN ha))
      (fun a ha => Subgroup.mem_sup_right (hKA₂ s hs hsN a ha)) hy
  by_cases hsN : s ∈ Subgroup.normalizer (L₁ : Set (MulAut W))
  · exact hKD s hs hsN x hx
  have hts : t⁻¹ * s ∈ Subgroup.normalizer (L₁ : Set (MulAut W)) := by
    rw [h.mul_mem_K (Mb.inv_mem htM) (hSM hs)]
    have htinv : t⁻¹ ∉ Subgroup.normalizer (L₁ : Set (MulAut W)) := fun h1 => htK (by
      have := (Subgroup.normalizer (L₁ : Set (MulAut W))).inv_mem h1
      rwa [inv_inv] at this)
    tauto
  have htt : t * t ∈ Subgroup.normalizer (L₁ : Set (MulAut W)) := by
    rw [h.mul_mem_K htM htM]
  have htD : ∀ y ∈ A₁ ⊔ A₂ ⊔ R, t * y * t⁻¹ ∈ A₁ ⊔ A₂ ⊔ R := by
    intro y hy
    refine conj_mem_sup_of (fun z hz => Subgroup.mem_sup_left ?_) (fun r hr =>
      Subgroup.mem_sup_right (hR.normal t htM r hr)) hy
    refine conj_mem_sup_of (fun a ha => Subgroup.mem_sup_right
      (Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom ha)) (fun a ha => ?_) hz
    obtain ⟨a', ha', rfl⟩ := ha
    have h1 := conj_mem_A₁ c₁ hSK (mul_mem htS htS) htt ha'
    refine Subgroup.mem_sup_left ?_
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    convert h1 using 1
    group
  have h2 := hKD (t⁻¹ * s) (mul_mem (S.inv_mem htS) hs) hts x hx
  have h3 := htD _ h2
  convert h3 using 1
  group

end Hyp

end CFSG.Quasithin.Vol2.Ch10.SecB.KL7
