module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBBlocks
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBSetting
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGM

open Subgroup CFSG.Quasithin

variable {X : Type} [Group X]

@[expose] def conjAut (L : Subgroup X) {x : X} (hx : x ∈ normalizer (L : Set X)) : MulAut L where
  toFun l := ⟨x * l * x⁻¹, (mem_normalizer_iff.mp hx l).mp l.2⟩
  invFun l := ⟨x⁻¹ * l * x, by simpa using (mem_normalizer_iff.mp (inv_mem hx) l).mp l.2⟩
  left_inv l := by ext; simp [mul_assoc]
  right_inv l := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]

theorem conjAut_apply (L : Subgroup X) {x : X} (hx : x ∈ normalizer (L : Set X)) (l : L) :
    (conjAut L hx l : X) = x * l * x⁻¹ :=
  rfl

theorem mul_conj_mul_inv {G : Type} [Group G] (φ : MulAut G) (l : G) :
    φ * MulAut.conj l * φ⁻¹ = MulAut.conj (φ l) := by
  ext m
  simp [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply]

open scoped Classical in
@[expose] noncomputable def rhoB (L : Subgroup X) (β : MulAut L →* Equiv.Perm (Fin 8)) (x : X) :
    Equiv.Perm (Fin 8) :=
  if hx : x ∈ normalizer (L : Set X) then β (conjAut L hx) else 1

section Rho

variable {L : Subgroup X} {β : MulAut L →* Equiv.Perm (Fin 8)}

theorem rhoB_of_mem {x : X} (hx : x ∈ normalizer (L : Set X)) :
    rhoB L β x = β (conjAut L hx) := by
  rw [rhoB, dif_pos hx]

theorem rhoB_mul {x y : X} (hx : x ∈ normalizer (L : Set X)) (hy : y ∈ normalizer (L : Set X)) :
    rhoB L β (x * y) = rhoB L β x * rhoB L β y := by
  rw [rhoB_of_mem hx, rhoB_of_mem hy, rhoB_of_mem (mul_mem hx hy), ← map_mul]
  congr 1
  ext l
  simp [conjAut_apply, MulAut.mul_apply, mul_assoc]

theorem rhoB_eq_mul {a b c : X} (ha : a ∈ normalizer (L : Set X))
    (hb : b ∈ normalizer (L : Set X)) (h : c = a * b) :
    rhoB L β c = rhoB L β a * rhoB L β b := by
  rw [h, rhoB_mul ha hb]

theorem rhoB_eq_one {x : X} (hx : ∀ l ∈ L, x * l * x⁻¹ = l) : rhoB L β x = 1 := by
  have hxN : x ∈ normalizer (L : Set X) := by
    rw [mem_normalizer_iff]
    intro l
    constructor
    · intro hl
      rw [hx l hl]
      exact hl
    · intro hl
      have h2 := congrArg (fun z => x⁻¹ * z * x) (hx _ hl)
      have h3 : x * l * x⁻¹ = l := by simpa [mul_assoc] using h2
      rwa [h3] at hl
  rw [rhoB_of_mem hxN]
  have h1 : conjAut L hxN = 1 := by
    ext l
    exact hx l l.2
  rw [h1, map_one]

theorem rhoB_one : rhoB L β 1 = 1 := rhoB_eq_one (fun l _ => by group)

theorem rhoB_of_mem_L {l : X} (hl : l ∈ L) : rhoB L β l = β (MulAut.conj ⟨l, hl⟩) := by
  rw [rhoB_of_mem (le_normalizer hl)]
  rfl

theorem comm_of_rhoB_eq_one (hβ : Function.Injective β) {x : X}
    (hx : x ∈ normalizer (L : Set X)) (h : rhoB L β x = 1) : ∀ l ∈ L, x * l * x⁻¹ = l := by
  intro l hl
  rw [rhoB_of_mem hx, ← map_one β] at h
  have h1 := congrArg (fun φ : MulAut L => ((φ ⟨l, hl⟩ : L) : X)) (hβ h)
  simpa [conjAut_apply] using h1

theorem rhoB_conj {x : X} (hx : x ∈ normalizer (L : Set X)) (l : L) :
    rhoB L β x * β (MulAut.conj l) * (rhoB L β x)⁻¹ = β (MulAut.conj (conjAut L hx l)) := by
  rw [rhoB_of_mem hx, ← map_inv, ← map_mul, ← map_mul, mul_conj_mul_inv]

end Rho

open scoped Classical in
@[expose] noncomputable def phiFun (L : Subgroup X) (β : MulAut L →* Equiv.Perm (Fin 8)) (t₀ x : X) : P16 :=
  if x ∈ normalizer (L : Set X) then blk (rhoB L β x, rhoB L β (t₀⁻¹ * x * t₀))
  else blk (rhoB L β (x * t₀), rhoB L β (t₀⁻¹ * x)) * sig

theorem phiFun_of_mem {L : Subgroup X} {β : MulAut L →* Equiv.Perm (Fin 8)} {t₀ x : X}
    (hx : x ∈ normalizer (L : Set X)) :
    phiFun L β t₀ x = blk (rhoB L β x, rhoB L β (t₀⁻¹ * x * t₀)) := by
  rw [phiFun, if_pos hx]

theorem phiFun_of_not_mem {L : Subgroup X} {β : MulAut L →* Equiv.Perm (Fin 8)} {t₀ x : X}
    (hx : x ∉ normalizer (L : Set X)) :
    phiFun L β t₀ x = blk (rhoB L β (x * t₀), rhoB L β (t₀⁻¹ * x)) * sig := by
  rw [phiFun, if_neg hx]

theorem blk_mul_blk (a b c d : Equiv.Perm (Fin 8)) : blk (a, b) * blk (c, d) = blk (a * c, b * d) := by
  rw [← map_mul, Prod.mk_mul_mk]

theorem blk_mul_blk_sig (a b c d : Equiv.Perm (Fin 8)) :
    blk (a, b) * (blk (c, d) * sig) = blk (a * c, b * d) * sig := by
  rw [← mul_assoc, blk_mul_blk]

theorem blk_sig_mul_blk (a b c d : Equiv.Perm (Fin 8)) :
    blk (a, b) * sig * blk (c, d) = blk (a * d, b * c) * sig := by
  rw [mul_assoc, sig_mul_blk, ← mul_assoc, blk_mul_blk]

theorem blk_sig_mul_blk_sig (a b c d : Equiv.Perm (Fin 8)) :
    blk (a, b) * sig * (blk (c, d) * sig) = blk (a * d, b * c) := by
  rw [← mul_assoc, blk_sig_mul_blk, mul_assoc, sig_mul_sig, mul_one]

namespace Setting

variable {L L' Tb : Subgroup X} {t₀ : X} (hS : Setting L L' Tb t₀)
  {β : MulAut L →* Equiv.Perm (Fin 8)}
include hS

theorem t₀_inv_not_mem : t₀⁻¹ ∉ normalizer (L : Set X) := fun h =>
  hS.t₀_not_mem (by simpa using inv_mem h)

theorem conj_mem {x : X} (hx : x ∈ normalizer (L : Set X)) :
    t₀⁻¹ * x * t₀ ∈ normalizer (L : Set X) := by
  rw [hS.mul_mem_iff, hS.mul_mem_iff]
  simp [hx, hS.t₀_inv_not_mem, hS.t₀_not_mem]

theorem mul_t₀_mem {x : X} (hx : x ∉ normalizer (L : Set X)) :
    x * t₀ ∈ normalizer (L : Set X) := by
  rw [hS.mul_mem_iff]
  simp [hx, hS.t₀_not_mem]

theorem inv_mul_mem {x : X} (hx : x ∉ normalizer (L : Set X)) :
    t₀⁻¹ * x ∈ normalizer (L : Set X) := by
  rw [hS.mul_mem_iff]
  simp [hx, hS.t₀_inv_not_mem]

theorem phiFun_mul_mem_mem {x y : X} (hx : x ∈ normalizer (L : Set X))
    (hy : y ∈ normalizer (L : Set X)) :
    phiFun L β t₀ (x * y) = phiFun L β t₀ x * phiFun L β t₀ y := by
  have e2 : rhoB L β (t₀⁻¹ * (x * y) * t₀) =
      rhoB L β (t₀⁻¹ * x * t₀) * rhoB L β (t₀⁻¹ * y * t₀) :=
    rhoB_eq_mul (hS.conj_mem hx) (hS.conj_mem hy) (by group)
  rw [phiFun_of_mem (mul_mem hx hy), phiFun_of_mem hx, phiFun_of_mem hy, blk_mul_blk,
    rhoB_mul hx hy, e2]

theorem phiFun_mul_mem_not {x y : X} (hx : x ∈ normalizer (L : Set X))
    (hy : y ∉ normalizer (L : Set X)) :
    phiFun L β t₀ (x * y) = phiFun L β t₀ x * phiFun L β t₀ y := by
  have hxy : x * y ∉ normalizer (L : Set X) := by rw [hS.mul_mem_iff]; simp [hx, hy]
  have e1 : rhoB L β (x * y * t₀) = rhoB L β x * rhoB L β (y * t₀) :=
    rhoB_eq_mul hx (hS.mul_t₀_mem hy) (by group)
  have e2 : rhoB L β (t₀⁻¹ * (x * y)) = rhoB L β (t₀⁻¹ * x * t₀) * rhoB L β (t₀⁻¹ * y) :=
    rhoB_eq_mul (hS.conj_mem hx) (hS.inv_mul_mem hy) (by group)
  rw [phiFun_of_not_mem hxy, phiFun_of_mem hx, phiFun_of_not_mem hy, blk_mul_blk_sig,
    e1, e2]

theorem phiFun_mul_not_mem {x y : X} (hx : x ∉ normalizer (L : Set X))
    (hy : y ∈ normalizer (L : Set X)) :
    phiFun L β t₀ (x * y) = phiFun L β t₀ x * phiFun L β t₀ y := by
  have hxy : x * y ∉ normalizer (L : Set X) := by rw [hS.mul_mem_iff]; simp [hx, hy]
  have e1 : rhoB L β (x * y * t₀) = rhoB L β (x * t₀) * rhoB L β (t₀⁻¹ * y * t₀) :=
    rhoB_eq_mul (hS.mul_t₀_mem hx) (hS.conj_mem hy) (by group)
  have e2 : rhoB L β (t₀⁻¹ * (x * y)) = rhoB L β (t₀⁻¹ * x) * rhoB L β y :=
    rhoB_eq_mul (hS.inv_mul_mem hx) hy (by group)
  rw [phiFun_of_not_mem hxy, phiFun_of_not_mem hx, phiFun_of_mem hy, blk_sig_mul_blk,
    e1, e2]

theorem phiFun_mul_not_not {x y : X} (hx : x ∉ normalizer (L : Set X))
    (hy : y ∉ normalizer (L : Set X)) :
    phiFun L β t₀ (x * y) = phiFun L β t₀ x * phiFun L β t₀ y := by
  have hxy : x * y ∈ normalizer (L : Set X) := by rw [hS.mul_mem_iff]; simp [hx, hy]
  have e1 : rhoB L β (x * y) = rhoB L β (x * t₀) * rhoB L β (t₀⁻¹ * y) :=
    rhoB_eq_mul (hS.mul_t₀_mem hx) (hS.inv_mul_mem hy) (by group)
  have e2 : rhoB L β (t₀⁻¹ * (x * y) * t₀) = rhoB L β (t₀⁻¹ * x) * rhoB L β (y * t₀) :=
    rhoB_eq_mul (hS.inv_mul_mem hx) (hS.mul_t₀_mem hy) (by group)
  rw [phiFun_of_mem hxy, phiFun_of_not_mem hx, phiFun_of_not_mem hy,
    blk_sig_mul_blk_sig, e1, e2]

theorem phiFun_mul (x y : X) : phiFun L β t₀ (x * y) = phiFun L β t₀ x * phiFun L β t₀ y := by
  by_cases hx : x ∈ normalizer (L : Set X) <;> by_cases hy : y ∈ normalizer (L : Set X)
  · exact hS.phiFun_mul_mem_mem hx hy
  · exact hS.phiFun_mul_mem_not hx hy
  · exact hS.phiFun_mul_not_mem hx hy
  · exact hS.phiFun_mul_not_not hx hy

variable (β) in
@[expose] noncomputable def phi : X →* P16 where
  toFun := phiFun L β t₀
  map_one' := by
    rw [phiFun_of_mem (one_mem _), mul_one, inv_mul_cancel, rhoB_one, Prod.mk_one_one,
      map_one]
  map_mul' := hS.phiFun_mul

theorem phi_apply (x : X) : hS.phi β x = phiFun L β t₀ x := rfl

theorem phi_of_mem_L {l : X} (hl : l ∈ L) : hS.phi β l = blk (β (MulAut.conj ⟨l, hl⟩), 1) := by
  rw [phi_apply, phiFun_of_mem (le_normalizer hl), rhoB_of_mem_L hl]
  congr 2
  refine rhoB_eq_one fun m hm => ?_
  have h1 := hS.commute hm (hS.mem_L'_of_mem hl)
  rw [h1, mul_inv_cancel_right]

theorem phi_of_mem_L' {l : X} (hl : l ∈ L') :
    hS.phi β l = blk (1, β (MulAut.conj ⟨t₀⁻¹ * l * t₀, hS.mem_L_of_mem' hl⟩)) := by
  have hlN : l ∈ normalizer (L : Set X) := hS.sup_le_normalizer (mem_sup_right hl)
  rw [phi_apply, phiFun_of_mem hlN, rhoB_of_mem_L (hS.mem_L_of_mem' hl)]
  congr 2
  refine rhoB_eq_one fun m hm => ?_
  rw [hS.commute hm hl, mul_inv_cancel_right]

theorem phi_injective (hβ : Function.Injective β) : Function.Injective (hS.phi β) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  rw [phi_apply] at hx
  by_cases hxN : x ∈ normalizer (L : Set X)
  · rw [phiFun_of_mem hxN, ← map_one blk, ← Prod.mk_one_one] at hx
    obtain ⟨h1, h2⟩ := Prod.mk.inj (blk_injective hx)
    have hc1 := comm_of_rhoB_eq_one hβ hxN h1
    have hc2 := comm_of_rhoB_eq_one hβ (hS.conj_mem hxN) h2
    have hcen : x ∈ centralizer ((L ⊔ L' : Subgroup X) : Set X) := by
      have hLx : L ⊔ L' ≤ centralizer ({x} : Set X) := by
        refine sup_le (fun l hl => ?_) (fun l hl => ?_)
        · rw [mem_centralizer_singleton_iff]
          have := hc1 l hl
          calc l * x = x * l * x⁻¹ * x := by rw [this]
            _ = x * l := by group
        · rw [mem_centralizer_singleton_iff]
          have := hc2 _ (hS.mem_L_of_mem' hl)
          have e : x * l * x⁻¹ = l := by
            have e1 : x * l * x⁻¹ = t₀ * ((t₀⁻¹ * x * t₀) * (t₀⁻¹ * l * t₀) *
                (t₀⁻¹ * x * t₀)⁻¹) * t₀⁻¹ := by group
            rw [e1, this]
            group
          calc l * x = x * l * x⁻¹ * x := by rw [e]
            _ = x * l := by group
      rw [mem_centralizer_iff]
      intro h hh
      exact mem_centralizer_singleton_iff.mp (hLx hh)
    rw [hS.cent, mem_bot] at hcen
    exact hcen
  · rw [phiFun_of_not_mem hxN] at hx
    exact absurd hx (blk_mul_sig_ne_one _)

end Setting

end CFSG.LocalAnalysis.WeakClosure81.NGM
