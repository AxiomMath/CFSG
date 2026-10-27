module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.ComponentNormal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NLift
public import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly

theorem isGLLift_one {U X ι F : Type} [Group U] [Group X] [Fintype ι] [DecidableEq ι] [Field F]
    {j : U →* GL ι F} {ψ : U →* X} : IsGLLift j ψ 1 1 := by
  intro u
  exact ⟨u, by simp, by simp⟩

theorem IsGLLift.mul {U X ι F : Type} [Group U] [Group X] [Fintype ι] [DecidableEq ι] [Field F]
    {j : U →* GL ι F} {ψ : U →* X} {s s' : GL ι F} {b b' : X} (hs : IsGLLift j ψ s b)
    (hs' : IsGLLift j ψ s' b') : IsGLLift j ψ (s' * s) (b * b') := by
  intro u
  obtain ⟨u₁, h₁j, h₁b⟩ := hs u
  obtain ⟨u₂, h₂j, h₂b⟩ := hs' u₁
  refine ⟨u₂, ?_, ?_⟩
  · rw [h₂j, h₁j]; group
  · calc (b * b')⁻¹ * ψ u * (b * b')
        = b'⁻¹ * (b⁻¹ * ψ u * b) * b' := by group
      _ = b'⁻¹ * ψ u₁ * b' := by rw [h₁b]
      _ = ψ u₂ := h₂b

theorem IsGLLift.pow {U X ι F : Type} [Group U] [Group X] [Fintype ι] [DecidableEq ι] [Field F]
    {j : U →* GL ι F} {ψ : U →* X} {s : GL ι F} {b : X} (hs : IsGLLift j ψ s b) (k : ℕ) :
    IsGLLift j ψ (s ^ k) (b ^ k) := by
  induction k with
  | zero => simpa using isGLLift_one (j := j) (ψ := ψ)
  | succ k ih =>
      have h := ih.mul hs
      rwa [← pow_succ', ← pow_succ] at h

private lemma sAc_commutator_central {G : Type*} [Group G] {c d x y : G}
    (hcx : Commute c x) (hcy : Commute c y) (hdx : Commute d x) (hdy : Commute d y)
    (hcd : Commute c d) :
    (c * x) * (d * y) * (c * x)⁻¹ * (d * y)⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  have hcxy : Commute c (x * y * x⁻¹) := (hcx.mul_right hcy).mul_right hcx.inv_right
  have hc_conj : (x * y * x⁻¹) * c⁻¹ = c⁻¹ * (x * y * x⁻¹) := hcxy.symm.inv_right.eq
  have hcd_c : c * d * c⁻¹ = d := by rw [hcd.eq]; group
  have hdxy : Commute d (x * y * x⁻¹ * y⁻¹) :=
    ((hdx.mul_right hdy).mul_right hdx.inv_right).mul_right hdy.inv_right
  calc
    (c * x) * (d * y) * (c * x)⁻¹ * (d * y)⁻¹
        = c * x * d * y * x⁻¹ * c⁻¹ * y⁻¹ * d⁻¹ := by group
    _ = c * (x * d) * y * x⁻¹ * c⁻¹ * y⁻¹ * d⁻¹ := by group
    _ = c * (d * x) * y * x⁻¹ * c⁻¹ * y⁻¹ * d⁻¹ := by rw [hdx.eq.symm]
    _ = c * d * x * y * x⁻¹ * c⁻¹ * y⁻¹ * d⁻¹ := by group
    _ = c * d * (x * y * x⁻¹ * c⁻¹) * y⁻¹ * d⁻¹ := by group
    _ = c * d * (c⁻¹ * (x * y * x⁻¹)) * y⁻¹ * d⁻¹ := by rw [hc_conj]
    _ = c * d * c⁻¹ * (x * y * x⁻¹) * y⁻¹ * d⁻¹ := by group
    _ = d * (x * y * x⁻¹) * y⁻¹ * d⁻¹ := by rw [hcd_c]
    _ = d * (x * y * x⁻¹ * y⁻¹) * d⁻¹ := by group
    _ = (x * y * x⁻¹ * y⁻¹) * d * d⁻¹ := by rw [hdxy.eq]
    _ = x * y * x⁻¹ * y⁻¹ := by group

namespace StepA

theorem exists_isComponentOf_comap_lift_of_isGLLift
    {U X ι F : Type} [Group U] [Group X] [Fintype ι] [DecidableEq ι] [Field F]
    (j : U →* GL ι F) (hj : Function.Injective j) (ψ : U →* X) (hψ : ψ.ker ≤ Subgroup.center U)
    (P : GL ι F → Prop) {D J : Subgroup X}
    (hJ : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (D : Set X)))
    (hlift : ∀ d ∈ D, ∃ s : GL ι F, P s ∧ IsGLLift j ψ s d) :
    ∃ J' : Subgroup U,
      IsComponentOf J'
        ((Subgroup.centralizer {s : GL ι F | P s ∧ ∃ d ∈ D, IsGLLift j ψ s d}).comap j) ∧
      J'.map ψ = J := by
  set S : Set (GL ι F) := {s : GL ι F | P s ∧ ∃ d ∈ D, IsGLLift j ψ s d} with hS
  set C : Subgroup U := (Subgroup.centralizer (D : Set X)).comap ψ with hC
  set N : Subgroup U := (Subgroup.centralizer S).comap j with hN
  have hmap : C.map ψ = ψ.range ⊓ Subgroup.centralizer (D : Set X) := by
    rw [hC, Subgroup.map_comap_eq]
  have hJopen : CFSG.Open.IsComponentOf J (C.map ψ) := by
    rw [hmap]
    exact (CFSG.Assembly.isComponentOf_iff_open).mp hJ
  obtain ⟨K, hKC, hKmap⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.I142N.exists_component_lift ψ
      (fun g hg => hψ (MonoidHom.mem_ker.mpr hg)) hJopen
  have hNC : N ≤ C := by
    intro u hu
    rw [hN, Subgroup.mem_comap] at hu
    rw [hC, Subgroup.mem_comap]
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    obtain ⟨s, hPs, hsLift⟩ := hlift d hd
    have hsS : s ∈ S := by rw [hS]; exact ⟨hPs, d, hd, hsLift⟩
    have hcomm : s * j u = j u * s := (Subgroup.mem_centralizer_iff.mp hu) s hsS
    obtain ⟨u', hu'j, hu'b⟩ := hsLift u
    have hu'j' : j u' = j u := by rw [hu'j, hcomm]; simp
    have hu' : u' = u := hj hu'j'
    have hdψ : d⁻¹ * ψ u * d = ψ u := by rw [hu'] at hu'b; exact hu'b
    have hdψ' : d * ψ u = ψ u * d := by
      have h1 : d * (d⁻¹ * ψ u * d) = d * ψ u := by rw [hdψ]
      have h2 : d * (d⁻¹ * ψ u * d) = ψ u * d := by group
      exact h1.symm.trans h2
    exact hdψ'
  have hab : ∀ a ∈ C, ∀ b ∈ C, a * b * a⁻¹ * b⁻¹ ∈ N := by
    intro a ha b hb
    rw [hN, Subgroup.mem_comap]
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    rw [hS] at hs
    obtain ⟨-, d, hd, hsLift⟩ := hs
    have haC : ψ a ∈ Subgroup.centralizer (D : Set X) := by
      rw [hC, Subgroup.mem_comap] at ha; exact ha
    have hbC : ψ b ∈ Subgroup.centralizer (D : Set X) := by
      rw [hC, Subgroup.mem_comap] at hb; exact hb
    have hda : d * ψ a = ψ a * d := (Subgroup.mem_centralizer_iff.mp haC) d hd
    have hdb : d * ψ b = ψ b * d := (Subgroup.mem_centralizer_iff.mp hbC) d hd
    obtain ⟨a', ha'j, ha'b⟩ := hsLift a
    obtain ⟨b', hb'j, hb'b⟩ := hsLift b
    have hda' : d⁻¹ * ψ a * d = ψ a := by
      have h := congrArg (fun z => d⁻¹ * z) hda
      simpa [mul_assoc] using h.symm
    have hdb' : d⁻¹ * ψ b * d = ψ b := by
      have h := congrArg (fun z => d⁻¹ * z) hdb
      simpa [mul_assoc] using h.symm
    have ha'ψ : ψ a' = ψ a := by rw [← ha'b, hda']
    have hb'ψ : ψ b' = ψ b := by rw [← hb'b, hdb']
    have hza_ker : a' * a⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ha'ψ]
      group
    have hzb_ker : b' * b⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hb'ψ]
      group
    have hza : a' * a⁻¹ ∈ Subgroup.center U := hψ hza_ker
    have hzb : b' * b⁻¹ ∈ Subgroup.center U := hψ hzb_ker
    have ha_eq : a' = (a' * a⁻¹) * a := by group
    have hb_eq : b' = (b' * b⁻¹) * b := by group
    have hja : s * j a * s⁻¹ = j (a' * a⁻¹) * j a := by
      calc s * j a * s⁻¹ = j a' := ha'j.symm
        _ = j ((a' * a⁻¹) * a) := by conv_lhs => rw [ha_eq]
        _ = j (a' * a⁻¹) * j a := by rw [map_mul]
    have hjb : s * j b * s⁻¹ = j (b' * b⁻¹) * j b := by
      calc s * j b * s⁻¹ = j b' := hb'j.symm
        _ = j ((b' * b⁻¹) * b) := by conv_lhs => rw [hb_eq]
        _ = j (b' * b⁻¹) * j b := by rw [map_mul]
    have hc_a : Commute (j (a' * a⁻¹)) (j a) := by
      rw [commute_iff_eq]
      have h := congrArg j (Subgroup.mem_center_iff.mp hza a)
      simpa only [map_mul] using h.symm
    have hc_b : Commute (j (a' * a⁻¹)) (j b) := by
      rw [commute_iff_eq]
      have h := congrArg j (Subgroup.mem_center_iff.mp hza b)
      simpa only [map_mul] using h.symm
    have hd_a : Commute (j (b' * b⁻¹)) (j a) := by
      rw [commute_iff_eq]
      have h := congrArg j (Subgroup.mem_center_iff.mp hzb a)
      simpa only [map_mul] using h.symm
    have hd_b : Commute (j (b' * b⁻¹)) (j b) := by
      rw [commute_iff_eq]
      have h := congrArg j (Subgroup.mem_center_iff.mp hzb b)
      simpa only [map_mul] using h.symm
    have hcd : Commute (j (a' * a⁻¹)) (j (b' * b⁻¹)) := by
      rw [commute_iff_eq]
      have h := congrArg j (Subgroup.mem_center_iff.mp hza (b' * b⁻¹))
      simpa only [map_mul] using h.symm
    have hcomm_w : s * j (a * b * a⁻¹ * b⁻¹) * s⁻¹ = j (a * b * a⁻¹ * b⁻¹) := by
      simp only [map_mul, map_inv]
      calc s * (j a * j b * (j a)⁻¹ * (j b)⁻¹) * s⁻¹
          = (s * j a * s⁻¹) * (s * j b * s⁻¹) * (s * j a * s⁻¹)⁻¹ *
              (s * j b * s⁻¹)⁻¹ := by group
        _ = (j (a' * a⁻¹) * j a) * (j (b' * b⁻¹) * j b) *
              (j (a' * a⁻¹) * j a)⁻¹ * (j (b' * b⁻¹) * j b)⁻¹ := by rw [hja, hjb]
        _ = j a * j b * (j a)⁻¹ * (j b)⁻¹ :=
              sAc_commutator_central hc_a hc_b hd_a hd_b hcd
    have hfin : s * j (a * b * a⁻¹ * b⁻¹) = j (a * b * a⁻¹ * b⁻¹) * s := by
      have h := congrArg (fun z => z * s) hcomm_w
      simpa [mul_assoc] using h
    exact hfin
  have hcomp : IsComponentOf K C := (CFSG.Assembly.isComponentOf_iff_open).mpr hKC
  refine ⟨K, ?_, hKmap⟩
  exact (isComponentOf_iff_of_normal_of_commutator_le hNC hab).mp hcomp

end StepA

end CFSG.StandardType.ClassicalPosition
