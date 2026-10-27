module

public import CFSG.Quasithin.H13.A6Setting4
public import CFSG.Quasithin.Vol2.Ch3Sec3A6Cocycle

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Quasithin.H13.A6Coc
open scoped commutatorElement

def vecOf (x : ↥W4) : Vec4 := crd (Multiplicative.toAdd (x : P6))

theorem vecOf_mul (x y : ↥W4) : vecOf (x * y) = vecOf x + vecOf y := by
  unfold vecOf
  rw [Subgroup.coe_mul, toAdd_mul, crd_add]

theorem crd_toAdd_nrm (y : P6) :
    crd (Multiplicative.toAdd (nrm y)) = crd (Multiplicative.toAdd y) := by
  rcases nrm_eq_or y with h | h
  · rw [h]
  · rw [h, toAdd_mul, crd_add]
    have : Multiplicative.toAdd (G6.allOnes 6) = fun _ => (1 : ZMod 2) := rfl
    rw [this, crd_const, add_zero]

theorem vecOf_act4 (σ : Perm (Fin 6)) (x : ↥W4) : vecOf (act4 σ x) = act σ (vecOf x) := by
  unfold vecOf
  rw [act4_coe, crd_toAdd_nrm]
  have hx : ∑ i, Multiplicative.toAdd (x : P6) i = 0 := x.2.1
  rw [act_crd σ _ hx]
  rfl

theorem vecOf_injective : Function.Injective vecOf := by
  have key : ∀ x y : P6, InW4 x ∧ InW4 y ∧
      crd (Multiplicative.toAdd x) = crd (Multiplicative.toAdd y) → x = y := by
    decide +kernel
  intro x y h
  exact Subtype.ext (key x y ⟨x.2, y.2, h⟩)

theorem vecOf_surjective : Function.Surjective vecOf := by
  intro v
  have hs : ∑ i, Multiplicative.toAdd (Multiplicative.ofAdd (sec v) : P6) i = 0 := sum_sec v
  refine ⟨⟨nrm (Multiplicative.ofAdd (sec v)), inW4_nrm _ hs⟩, ?_⟩
  show crd (Multiplicative.toAdd (nrm (Multiplicative.ofAdd (sec v)))) = v
  rw [crd_toAdd_nrm]
  exact crd_sec v

section Cocycle

variable {G : Type} [Group G] {T L V : Subgroup G} (F : Frame4 T L V)

theorem Frame4.psi_conj (g : ↥(Subgroup.normalizer (V : Set G))) (v : ↥V) :
    F.ψ ⟨(g : G) * v * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp g.2 v).mp v.2⟩ =
      act4 (F.ρ g) (F.ψ v) := by
  rw [← F.equiv]
  congr 1

noncomputable def coordV (v : ↥V) : Vec4 := vecOf (F.ψ v)

theorem coordV_mul (a b : ↥V) : coordV F (a * b) = coordV F a + coordV F b := by
  unfold coordV
  rw [map_mul, vecOf_mul]

theorem coordV_injective : Function.Injective (coordV F) :=
  vecOf_injective.comp F.ψ.injective

theorem coordV_surjective : Function.Surjective (coordV F) :=
  vecOf_surjective.comp F.ψ.surjective

theorem coordV_conj (g : ↥(Subgroup.normalizer (V : Set G))) (v : ↥V) :
    coordV F ⟨(g : G) * v * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp g.2 v).mp v.2⟩ =
      act (F.ρ g) (coordV F v) := by
  unfold coordV
  rw [F.psi_conj g v, vecOf_act4]

open Classical in
noncomputable def phi (g : G) : Vec4 := if h : g ∈ V then coordV F ⟨g, h⟩ else 0

theorem phi_of_mem {g : G} (h : g ∈ V) : phi F g = coordV F ⟨g, h⟩ := by
  unfold phi
  simp [h]

theorem phi_one : phi F 1 = 0 := by
  rw [phi_of_mem F (one_mem V)]
  have : (⟨1, one_mem V⟩ : ↥V) = 1 := rfl
  rw [this]
  have h := coordV_mul F 1 1
  rw [mul_one] at h
  exact left_eq_add.mp h

theorem phi_mul {a b : G} (ha : a ∈ V) (hb : b ∈ V) : phi F (a * b) = phi F a + phi F b := by
  rw [phi_of_mem F (V.mul_mem ha hb), phi_of_mem F ha, phi_of_mem F hb]
  exact coordV_mul F ⟨a, ha⟩ ⟨b, hb⟩

theorem phi_conj {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G)) {v : G} (hv : v ∈ V) :
    phi F (g * v * g⁻¹) = act (F.ρ ⟨g, hg⟩) (phi F v) := by
  rw [phi_of_mem F ((Subgroup.mem_normalizer_iff.mp hg v).mp hv), phi_of_mem F hv]
  exact coordV_conj F ⟨g, hg⟩ ⟨v, hv⟩

theorem phi_injOn {a b : G} (ha : a ∈ V) (hb : b ∈ V) (h : phi F a = phi F b) : a = b := by
  rw [phi_of_mem F ha, phi_of_mem F hb] at h
  exact congrArg Subtype.val (coordV_injective F h)

theorem phi_inv {a : G} (ha : a ∈ V) : phi F a⁻¹ = - phi F a := by
  have h := phi_mul F ha (V.inv_mem ha)
  rw [mul_inv_cancel, phi_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm


noncomputable def cocy (d ℓ : G) : Vec4 := phi F ⁅d, ℓ⁆

theorem comm_mul_right (d ℓ ℓ' : G) : ⁅d, ℓ * ℓ'⁆ = ⁅d, ℓ⁆ * (ℓ * ⁅d, ℓ'⁆ * ℓ⁻¹) := by
  simp only [commutatorElement_def]
  group

theorem comm_mul_left (a b ℓ : G) : ⁅a * b, ℓ⁆ = a * ⁅b, ℓ⁆ * a⁻¹ * ⁅a, ℓ⁆ := by
  simp only [commutatorElement_def]
  group

theorem eq_of_cocycle {D : Subgroup G}
    (hDV : ∀ d ∈ D, ∀ v ∈ V, d * v = v * d)
    (hDL : ∀ d ∈ D, ∀ ℓ ∈ L, ⁅d, ℓ⁆ ∈ V)
    (hDR : ∀ d ∈ D, ∀ ℓ ∈ L, ∀ hℓ : ℓ ∈ Subgroup.normalizer (V : Set G),
      F.ρ ⟨ℓ, hℓ⟩ = 1 → d * ℓ = ℓ * d)
    (hkey : ∀ u ∈ V, ∀ d ∈ D, (∀ ℓ ∈ L, ⁅d, ℓ⁆ = ⁅u, ℓ⁆) → d = 1)
    {d₁ d₂ : G} (h₁ : d₁ ∈ D) (h₂ : d₂ ∈ D) (hn₁ : d₁ ≠ 1) (hn₂ : d₂ ≠ 1) : d₁ = d₂ := by
  classical
  have hLN : L ≤ Subgroup.normalizer (V : Set G) := F.L_le
  have hcomm_in : ∀ u ∈ V, ∀ ℓ ∈ L, ⁅u, ℓ⁆ ∈ V := by
    intro u hu ℓ hℓ
    have h1 : ℓ * u⁻¹ * ℓ⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hLN hℓ) u⁻¹).mp (V.inv_mem hu)
    have := V.mul_mem hu h1
    simpa [commutatorElement_def, mul_assoc] using this
  have hconj_in : ∀ d ∈ D, ∀ ℓ (hℓ : ℓ ∈ L), ∀ ℓ' ∈ L, ℓ * ⁅d, ℓ'⁆ * ℓ⁻¹ ∈ V :=
    fun d hd ℓ hℓ ℓ' hℓ' =>
      (Subgroup.mem_normalizer_iff.mp (hLN hℓ) _).mp (hDL d hd ℓ' hℓ')
  have hcoc : ∀ d ∈ D, ∀ ℓ (hℓ : ℓ ∈ L), ∀ ℓ' (hℓ' : ℓ' ∈ L),
      cocy F d (ℓ * ℓ') = cocy F d ℓ + act (F.ρ ⟨ℓ, hLN hℓ⟩) (cocy F d ℓ') := by
    intro d hd ℓ hℓ ℓ' hℓ'
    unfold cocy
    rw [comm_mul_right, phi_mul F (hDL d hd ℓ hℓ) (hconj_in d hd ℓ hℓ ℓ' hℓ'),
      phi_conj F (hLN hℓ) (hDL d hd ℓ' hℓ')]
  have hinv : ∀ d ∈ D, ∀ ℓ (hℓ : ℓ ∈ L), ∀ ℓ' (hℓ' : ℓ' ∈ L),
      F.ρ ⟨ℓ, hLN hℓ⟩ = F.ρ ⟨ℓ', hLN hℓ'⟩ → cocy F d ℓ = cocy F d ℓ' := by
    intro d hd ℓ hℓ ℓ' hℓ' hρ
    have hr : ℓ⁻¹ * ℓ' ∈ L := L.mul_mem (L.inv_mem hℓ) hℓ'
    have hρr : F.ρ ⟨ℓ⁻¹ * ℓ', hLN hr⟩ = 1 := by
      have : (⟨ℓ⁻¹ * ℓ', hLN hr⟩ : ↥(Subgroup.normalizer (V : Set G))) =
          ⟨ℓ, hLN hℓ⟩⁻¹ * ⟨ℓ', hLN hℓ'⟩ := rfl
      rw [this, map_mul, map_inv, hρ, inv_mul_cancel]
    have hdr := hDR d hd (ℓ⁻¹ * ℓ') hr (hLN hr) hρr
    have hc1 : ⁅d, ℓ⁻¹ * ℓ'⁆ = 1 := by
      simp only [commutatorElement_def]
      rw [hdr]
      group
    have h0 : cocy F d (ℓ⁻¹ * ℓ') = 0 := by
      unfold cocy
      rw [hc1, phi_one]
    have := hcoc d hd ℓ hℓ (ℓ⁻¹ * ℓ') hr
    rw [mul_inv_cancel_left, h0, act_zero, add_zero] at this
    exact this.symm
  have hlift : ∀ γ : Γ, ∃ g : ↥(Subgroup.normalizer (V : Set G)),
      (g : G) ∈ L ∧ F.ρ g = (γ : Perm (Fin 6)) := fun γ => (F.image_L γ).2 γ.2
  choose lift hliftL hliftρ using hlift
  let δ : G → Γ → Vec4 := fun d γ => cocy F d (lift γ : G)
  have hcross : ∀ d ∈ D, IsCrossed (δ d) := by
    intro d hd γ γ'
    show cocy F d (lift (γ * γ') : G) =
      cocy F d (lift γ : G) + act (γ : Perm (Fin 6)) (cocy F d (lift γ' : G))
    have h1 : cocy F d (lift (γ * γ') : G) = cocy F d ((lift γ : G) * (lift γ' : G)) := by
      refine hinv d hd _ (hliftL _) _ (L.mul_mem (hliftL γ) (hliftL γ')) ?_
      have e : (⟨(lift γ : G) * (lift γ' : G), hLN (L.mul_mem (hliftL γ) (hliftL γ'))⟩ :
          ↥(Subgroup.normalizer (V : Set G))) = lift γ * lift γ' := rfl
      rw [e, map_mul]
      show F.ρ (lift (γ * γ')) = _
      rw [hliftρ, hliftρ, hliftρ]
      rfl
    rw [h1, hcoc d hd _ (hliftL γ) _ (hliftL γ')]
    have e : (⟨(lift γ : G), hLN (hliftL γ)⟩ : ↥(Subgroup.normalizer (V : Set G))) = lift γ := rfl
    rw [e, hliftρ]
  have hinner : ∀ d ∈ D, IsInner (δ d) → d = 1 := by
    rintro d hd ⟨w, hw⟩
    obtain ⟨u, rfl⟩ := coordV_surjective F w
    refine hkey (u : G) u.2 d hd (fun ℓ hℓ => ?_)
    have hγ : F.ρ ⟨ℓ, hLN hℓ⟩ ∈ alternatingGroup (Fin 6) :=
      (F.image_L _).1 ⟨⟨ℓ, hLN hℓ⟩, hℓ, rfl⟩
    have h1 := hw ⟨F.ρ ⟨ℓ, hLN hℓ⟩, hγ⟩
    have h2 : δ d ⟨F.ρ ⟨ℓ, hLN hℓ⟩, hγ⟩ = cocy F d ℓ := by
      refine hinv d hd _ (hliftL _) ℓ hℓ ?_
      have e : (⟨(lift ⟨F.ρ ⟨ℓ, hLN hℓ⟩, hγ⟩ : G), hLN (hliftL _)⟩ :
          ↥(Subgroup.normalizer (V : Set G))) = lift ⟨F.ρ ⟨ℓ, hLN hℓ⟩, hγ⟩ := rfl
      rw [e, hliftρ]
    rw [h2] at h1
    have e1 : ⁅(u : G), ℓ⁆ = (u : G) * (ℓ * (u : G) * ℓ⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    have hconj : ℓ * (u : G) * ℓ⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hLN hℓ) _).mp u.2
    have hphiu : phi F ⁅(u : G), ℓ⁆ = coordV F u - act (F.ρ ⟨ℓ, hLN hℓ⟩) (coordV F u) := by
      rw [e1, phi_mul F u.2 (V.inv_mem hconj), phi_inv F hconj, phi_conj F (hLN hℓ) u.2,
        phi_of_mem F u.2, sub_eq_add_neg]
      rfl
    exact phi_injOn F (hDL d hd ℓ hℓ) (hcomm_in u u.2 ℓ hℓ) (by
      rw [hphiu]
      exact h1)
  have hhom : ∀ a ∈ D, ∀ b ∈ D, ∀ ℓ ∈ L, cocy F (a * b) ℓ = cocy F a ℓ + cocy F b ℓ := by
    intro a ha b hb ℓ hℓ
    unfold cocy
    rw [comm_mul_left]
    have hbV := hDL b hb ℓ hℓ
    have e : a * ⁅b, ℓ⁆ * a⁻¹ = ⁅b, ℓ⁆ := by
      rw [hDV a ha _ hbV]
      group
    rw [e, phi_mul F hbV (hDL a ha ℓ hℓ), add_comm]
  have hone : ∀ ℓ, cocy F 1 ℓ = 0 := fun ℓ => by
    unfold cocy
    rw [show ⁅(1 : G), ℓ⁆ = 1 by simp [commutatorElement_def], phi_one]
  have hinvd : ∀ d ∈ D, ∀ ℓ ∈ L, cocy F d⁻¹ ℓ = - cocy F d ℓ := by
    intro d hd ℓ hℓ
    have := hhom d hd d⁻¹ (D.inv_mem hd) ℓ hℓ
    rw [mul_inv_cancel, hone] at this
    exact eq_neg_of_add_eq_zero_right this.symm
  have hsub : ∀ γ : Γ, δ (d₁ * d₂⁻¹) γ = δ d₁ γ - δ d₂ γ := by
    intro γ
    show cocy F (d₁ * d₂⁻¹) (lift γ : G) = cocy F d₁ (lift γ : G) - cocy F d₂ (lift γ : G)
    rw [hhom d₁ h₁ d₂⁻¹ (D.inv_mem h₂) _ (hliftL γ), hinvd d₂ h₂ _ (hliftL γ), sub_eq_add_neg]
    rfl
  have hdiff := diff_inner (hcross d₁ h₁) (hcross d₂ h₂) (fun h => hn₁ (hinner d₁ h₁ h))
    (fun h => hn₂ (hinner d₂ h₂ h))
  have he : d₁ * d₂⁻¹ = 1 := by
    refine hinner _ (D.mul_mem h₁ (D.inv_mem h₂)) ?_
    obtain ⟨w, hw⟩ := hdiff
    exact ⟨w, fun γ => by rw [hsub γ]; exact hw γ⟩
  exact mul_inv_eq_one.mp he

end Cocycle

end CFSG.Quasithin.H13.A6
