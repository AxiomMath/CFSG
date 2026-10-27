module

public import CFSG.Sporadic.Co2Smith.RigidNF
public import CFSG.Sporadic.Co2Smith.RigidSplit

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Certificates.ExtraspecialNF

universe u v

namespace SmithConfig

theorem closure_top
    (c : SmithConfig.{u}) :
    Subgroup.closure (insert c.zE (Set.range c.vh)) = ⊤ :=
  closure_eq_top_of_surj c.nf_bijective.2

theorem nf_inv_mul_nf_mem
    (c : SmithConfig.{u}) (σ τ : ZMod 2) (u' : Fin 8 → ZMod 2) :
    (nf c.zE c.vh σ u')⁻¹ * nf c.zE c.vh τ u' ∈ Subgroup.center c.E := by
  have hz : ∀ σ : ZMod 2, c.zE ^ σ.val ∈ Subgroup.center c.E :=
    fun σ => Subgroup.pow_mem _ c.zE_mem_center _
  have e : (nf c.zE c.vh σ u')⁻¹ * nf c.zE c.vh τ u' =
      (mon c.vh u')⁻¹ * ((c.zE ^ σ.val)⁻¹ * c.zE ^ τ.val) * (mon c.vh u')⁻¹⁻¹ := by
    simp only [nf]
    group
  rw [e]
  exact (inferInstance : (Subgroup.center c.E).Normal).conj_mem _
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hz σ)) (hz τ)) _

variable (c₁ : SmithConfig.{u}) (c₂ : SmithConfig.{v})

@[expose] noncomputable def θE : c₁.E ≃* c₂.E :=
  nfEquiv c₁.rel_vh c₂.rel_vh c₁.nf_bijective c₂.nf_bijective

theorem θE_nf (s : ZMod 2) (u' : Fin 8 → ZMod 2) :
    c₁.θE c₂ (nf c₁.zE c₁.vh s u') = nf c₂.zE c₂.vh s u' :=
  nfEquiv_nf _ _ _ _ s u'

theorem θE_zE : c₁.θE c₂ c₁.zE = c₂.zE := by
  have h := c₁.θE_nf c₂ 1 0
  rwa [nf_one_zero, nf_one_zero] at h

theorem θE_vh (a : Fin 8) : c₁.θE c₂ (c₁.vh a) = c₂.vh a := by
  have h := c₁.θE_nf c₂ 0 (Pi.single a 1)
  rwa [nf_single, nf_single] at h

@[expose] noncomputable def phiL (g : S0) : c₁.E →* c₂.E :=
  (c₁.θE c₂).toMonoidHom.comp (c₁.cE (c₁.ι g)).toMonoidHom

@[expose] noncomputable def phiR (g : S0) : c₁.E →* c₂.E :=
  (c₂.cE (c₂.ι g)).toMonoidHom.comp (c₁.θE c₂).toMonoidHom

theorem phiL_apply (g : S0) (e : c₁.E) : c₁.phiL c₂ g e = c₁.θE c₂ (c₁.cE (c₁.ι g) e) := rfl

theorem phiR_apply (g : S0) (e : c₁.E) : c₁.phiR c₂ g e = c₂.cE (c₂.ι g) (c₁.θE c₂ e) := rfl

@[expose] noncomputable def eqvSub : Subgroup S0 where
  carrier := {g | ∀ e : c₁.E, c₁.θE c₂ (c₁.cE (c₁.ι g) e) = c₂.cE (c₂.ι g) (c₁.θE c₂ e)}
  mul_mem' {g h} hg hh e := by
    simp only [Set.mem_ofPred_eq] at hg hh
    rw [map_mul, c₁.cE_mul, hg, hh, map_mul, c₂.cE_mul]
  one_mem' e := by
    simp only [map_one, c₁.cE_one, c₂.cE_one]
  inv_mem' {g} hg e := by
    simp only [Set.mem_ofPred_eq] at hg ⊢
    have h1 := hg (c₁.cE (c₁.ι g⁻¹) e)
    rw [← c₁.cE_mul, ← map_mul, mul_inv_cancel, map_one, c₁.cE_one] at h1
    rw [h1, ← c₂.cE_mul, ← map_mul, inv_mul_cancel, map_one, c₂.cE_one]

theorem mem_eqvSub_iff (g : S0) : g ∈ c₁.eqvSub c₂ ↔ c₁.phiL c₂ g = c₁.phiR c₂ g := by
  constructor
  · intro h
    ext e
    exact congrArg Subtype.val (h e)
  · intro h e
    exact DFunLike.congr_fun h e

theorem mem_eqvSub_of_vh (g : S0)
    (h : ∀ a, c₁.θE c₂ (c₁.cE (c₁.ι g) (c₁.vh a)) = c₂.cE (c₂.ι g) (c₁.θE c₂ (c₁.vh a))) :
    g ∈ c₁.eqvSub c₂ := by
  rw [mem_eqvSub_iff]
  refine MonoidHom.eq_of_eqOn_dense c₁.closure_top ?_
  rintro x (rfl | ⟨a, rfl⟩)
  · rw [phiL_apply, phiR_apply, c₁.cE_zE, c₁.θE_zE, c₂.cE_zE]
  · exact h a

theorem y1_mem_eqvSub : frS 0 ∈ c₁.eqvSub c₂ := by
  refine c₁.mem_eqvSub_of_vh c₂ _ fun a => ?_
  rw [← vcode_bits a, c₁.θE_vh, c₁.vh_vcode, c₂.vh_vcode]
  generalize a.val.testBit 1 = e1
  generalize a.val.testBit 2 = e2
  cases a.val.testBit 0
  · have h1 := c₁.y1_vhv_false e1 e2
    have h2 := c₂.y1_vhv_false e1 e2
    rw [h1, h2, ← c₁.vh_vcode, ← c₂.vh_vcode, c₁.θE_vh]
  · have h1 := c₁.y1_vhv_true e1 e2
    have h2 := c₂.y1_vhv_true e1 e2
    rw [h1, h2, map_mul, ← c₁.vh_vcode, ← c₁.vh_vcode, ← c₂.vh_vcode, ← c₂.vh_vcode, c₁.θE_vh,
      c₁.θE_vh]

theorem mem_eqvSub_of_frame
    {k : ℕ} (hk : k < 9) {h' : S0} (hh' : h' ∈ c₁.eqvSub c₂)
    (hrel : frS k * frS 0 = h' * frS k) : frS k ∈ c₁.eqvSub c₂ := by
  set g := frS k with hgdef
  have hy := c₁.y1_mem_eqvSub c₂
  set D := defect (c₁.phiL c₂ g) (c₁.phiR c₂ g) with hD
  have hgen : ∀ s ∈ insert c₁.zE (Set.range c₁.vh), D s ∈ Subgroup.center c₂.E := by
    rintro x (rfl | ⟨a, rfl⟩)
    · rw [hD, defect, phiL_apply, phiR_apply, c₁.cE_zE, c₁.θE_zE, c₂.cE_zE, inv_mul_cancel]
      exact Subgroup.one_mem _
    · obtain ⟨σ₁, h₁⟩ := c₁.frame_vh_ι k hk a
      obtain ⟨σ₂, h₂⟩ := c₂.frame_vh_ι k hk a
      rw [hD, defect, phiL_apply, phiR_apply, h₁, c₁.θE_vh, h₂, c₁.θE_nf]
      exact c₂.nf_inv_mul_nf_mem _ _ _
  have hcen := defect_central _ _ c₁.closure_top hgen
  have hmul := defect_mul _ _ c₁.closure_top hgen
  simp only [← hD] at hcen hmul
  have hz : D c₁.zE = 1 := by
    rw [hD, defect, phiL_apply, phiR_apply, c₁.cE_zE, c₁.θE_zE, c₂.cE_zE, inv_mul_cancel]
  have hinv : ∀ x, D x⁻¹ = (D x)⁻¹ := by
    intro x
    have h1 := hmul x x⁻¹
    rw [mul_inv_cancel] at h1
    have h0 : D 1 = 1 := by rw [hD, defect, map_one, map_one, inv_one, one_mul]
    rw [h0] at h1
    exact eq_inv_of_mul_eq_one_right h1.symm
  have hyD : ∀ x, D (c₁.cE (c₁.ι (frS 0)) x) = D x := by
    intro x
    have hL : c₁.phiL c₂ g (c₁.cE (c₁.ι (frS 0)) x) =
        c₂.cE (c₂.ι h') (c₁.phiL c₂ g x) := by
      rw [phiL_apply, ← c₁.cE_mul, ← map_mul, hrel, map_mul, c₁.cE_mul, hh']
      rfl
    have hR : c₁.phiR c₂ g (c₁.cE (c₁.ι (frS 0)) x) =
        c₂.cE (c₂.ι h') (c₁.phiR c₂ g x) := by
      rw [phiR_apply, hy, ← c₂.cE_mul, ← map_mul, hrel, map_mul, c₂.cE_mul]
      rfl
    rw [hD, defect, hL, hR, ← map_inv, ← map_mul]
    exact c₂.cE_center _ (hcen x)
  have hall : ∀ x, D x = 1 := by
    intro e
    let T : c₁.M → c₁.M := fun n => c₁.mA (frS 0) n * n⁻¹
    have hTinj : Function.Injective T := by
      intro n n' h
      have e1 : c₁.mA (frS 0) n / n = c₁.mA (frS 0) n' / n' := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact h
      have e2 : c₁.mA (frS 0) n / c₁.mA (frS 0) n' = n / n' :=
        div_eq_div_iff_div_eq_div.mp e1
      have h1 : c₁.mA (frS 0) (n / n') = n / n' := by rw [map_div, e2]
      exact div_eq_one.mp (c₁.y1_fpf _ h1)
    obtain ⟨n, hn⟩ := (Finite.injective_iff_surjective.mp hTinj) (c₁.piM e)
    set x := c₁.lift n
    have hx : c₁.piM (c₁.cE (c₁.ι (frS 0)) x * x⁻¹) = c₁.piM e := by
      rw [map_mul, map_inv, ← c₁.mA_piM_ι, c₁.piM_lift]
      exact hn
    obtain ⟨k₀, hk₀, hke⟩ := c₁.eq_mul_center hx
    rw [hke, hmul, hmul, hyD, hinv, mul_inv_cancel, one_mul]
    rcases (c₁.mem_center_iff k₀).mp hk₀ with rfl | rfl
    · rw [hD, defect, map_one, map_one, inv_one, one_mul]
    · exact hz
  rw [mem_eqvSub_iff]
  exact eq_of_defect _ _ hall

end SmithConfig

end CFSG.Sporadic.Co2Smith
