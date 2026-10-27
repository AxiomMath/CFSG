module

public import CFSG.LocalAnalysis.WeakClosure81.W16LSixCDefs
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveFam

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.SignalizerFunctorTheorem.Quadratic
open CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

theorem IsMinFam16.normalClosure_subgroupOf (h1 : W16One G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H) :
    Subgroup.normalClosure
      ((V.subgroupOf (CFSG.Quasithin.conjClosure V H) :
        Subgroup ↥(CFSG.Quasithin.conjClosure V H)) :
        Set ↥(CFSG.Quasithin.conjClosure V H)) = ⊤ := by
  let K := CFSG.Quasithin.conjClosure V H
  let N : Subgroup ↥K :=
    Subgroup.normalClosure ((V.subgroupOf K : Subgroup ↥K) : Set ↥K)
  change N = ⊤
  have hKH : K ≤ H := IsMinFam16.conjClosure_le_H h hH
  have hVK : V ≤ K := CFSG.Quasithin.le_conjClosure V H
  have hsup : S ⊔ K = H := IsMinFam16.sup_conjClosure_eq h1 hS h hH hV
  have hKn : H ≤ Subgroup.normalizer (K : Set G) :=
    CFSG.Quasithin.le_normalizer_conjClosure V H
  have hgen : ∀ (y : G) (hy : y ∈ Subgroup.closure
      {x : G | ∃ h ∈ H, ∃ z ∈ V, h * z * h⁻¹ = x}), (⟨y, hy⟩ : ↥K) ∈ N := by
    intro y hy
    refine Subgroup.closure_induction (p := fun y hy => (⟨y, hy⟩ : ↥K) ∈ N)
      ?_ ?_ ?_ ?_ hy
    · intro x hx
      obtain ⟨h', hh', z, hz, rfl⟩ := hx
      have hSK : (↑(S ⊔ K) : Set G) = (S : Set G) * (K : Set G) :=
        Subgroup.coe_mul_of_left_le_normalizer_right S K (hH.1.1.trans hKn)
      have hh'K : h' ∈ S ⊔ K := hsup ▸ hh'
      change h' ∈ (↑(S ⊔ K) : Set G) at hh'K
      rw [hSK] at hh'K
      obtain ⟨s, hsS, k, hkK, rfl⟩ := hh'K
      have hsH : s ∈ H := hH.1.1 hsS
      have hszV : s * z * s⁻¹ ∈ V := by
        have hsn : s ∈ Subgroup.normalizer (V : Set G) := by
          rw [h.hyp.h6.normalizer_eq]
          exact h.S_le_M hsS
        exact (Subgroup.mem_normalizer_iff.1 hsn z).1 hz
      have hszK : s * z * s⁻¹ ∈ K := hVK hszV
      have hskK : s * k * s⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.1 (hKn hsH) k).1 hkK
      have hconjK : (s * k) * z * (s * k)⁻¹ ∈ K := by
        have heq2 : (s * k) * z * (s * k)⁻¹
            = (s * k * s⁻¹) * (s * z * s⁻¹) * (s * k * s⁻¹)⁻¹ := by group
        rw [heq2]
        exact K.mul_mem (K.mul_mem hskK hszK) (K.inv_mem hskK)
      have hzV : (⟨s * z * s⁻¹, hszK⟩ : ↥K) ∈ V.subgroupOf K := by
        rw [Subgroup.mem_subgroupOf]
        exact hszV
      have hzN : (⟨s * z * s⁻¹, hszK⟩ : ↥K) ∈ N := Subgroup.subset_normalClosure hzV
      have hconj := (inferInstance : N.Normal).conj_mem
        (⟨s * z * s⁻¹, hszK⟩ : ↥K) hzN (⟨s * k * s⁻¹, hskK⟩ : ↥K)
      have heq : (⟨(s * k) * z * (s * k)⁻¹, hconjK⟩ : ↥K)
          = (⟨s * k * s⁻¹, hskK⟩ : ↥K) * (⟨s * z * s⁻¹, hszK⟩ : ↥K)
            * (⟨s * k * s⁻¹, hskK⟩ : ↥K)⁻¹ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [heq]
      exact hconj
    · exact N.one_mem
    · intro x y hx hy ihx ihy
      have hxy : (⟨x * y, mul_mem hx hy⟩ : ↥K)
          = (⟨x, hx⟩ : ↥K) * (⟨y, hy⟩ : ↥K) := Subtype.ext rfl
      rw [hxy]
      exact N.mul_mem ihx ihy
    · intro x hx ihx
      have hxinv : (⟨x⁻¹, inv_mem hx⟩ : ↥K) = (⟨x, hx⟩ : ↥K)⁻¹ := Subtype.ext rfl
      rw [hxinv]
      exact N.inv_mem ihx
  rw [eq_top_iff]
  intro x _
  have hx' : (⟨(x : G), x.2⟩ : ↥K) ∈ N := hgen (x : G) x.2
  simpa using hx'

theorem IsMinFam16.normalClosure_barSub (h1 : W16One G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    {X : Type} [Group X] {φ : ↥(CFSG.Quasithin.conjClosure V H) →* X}
    (hφ : SevenK.IsBarMap (CFSG.Quasithin.conjClosure V H) (iSub16 V H) φ) :
    Subgroup.normalClosure
      ((SevenK.barSub (CFSG.Quasithin.conjClosure V H) φ V : Subgroup X) : Set X) = ⊤ ∧
    Subgroup.closure {x : X | x * x = 1} = ⊤ := by
  have hnc := IsMinFam16.normalClosure_subgroupOf h1 hS h hH hV
  have hmap := Subgroup.map_normalClosure
    ((V.subgroupOf (CFSG.Quasithin.conjClosure V H) :
      Subgroup ↥(CFSG.Quasithin.conjClosure V H)) :
      Set ↥(CFSG.Quasithin.conjClosure V H)) φ hφ.surjective
  rw [hnc, Subgroup.map_top_of_surjective φ hφ.surjective] at hmap
  have h1st : Subgroup.normalClosure
      ((SevenK.barSub (CFSG.Quasithin.conjClosure V H) φ V : Subgroup X) : Set X) = ⊤ := by
    have hcoe : ((SevenK.barSub (CFSG.Quasithin.conjClosure V H) φ V : Subgroup X) : Set X)
        = φ '' ((V.subgroupOf (CFSG.Quasithin.conjClosure V H) :
            Subgroup ↥(CFSG.Quasithin.conjClosure V H)) :
            Set ↥(CFSG.Quasithin.conjClosure V H)) := by
      rw [SevenK.barSub, Subgroup.coe_map]
    rw [hcoe, ← hmap]
  refine ⟨h1st, ?_⟩
  have hnorm : (Subgroup.closure {x : X | x * x = 1}).Normal := by
    refine ⟨fun n hn g => ?_⟩
    refine Subgroup.closure_induction
      (p := fun n _ => g * n * g⁻¹ ∈ Subgroup.closure {x : X | x * x = 1})
      ?_ ?_ ?_ ?_ hn
    · intro x hx
      refine Subgroup.subset_closure ?_
      show (g * x * g⁻¹) * (g * x * g⁻¹) = 1
      rw [show (g * x * g⁻¹) * (g * x * g⁻¹) = g * (x * x) * g⁻¹ by group, hx,
        mul_one, mul_inv_cancel]
    · rw [show g * 1 * g⁻¹ = 1 by group]
      exact Subgroup.one_mem _
    · intro x y hx hy ihx ihy
      have hxy : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [hxy]
      exact Subgroup.mul_mem _ ihx ihy
    · intro x hx ihx
      have hxinv : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [hxinv]
      exact Subgroup.inv_mem _ ihx
  haveI : (Subgroup.closure {x : X | x * x = 1}).Normal := hnorm
  have hbar_le : SevenK.barSub (CFSG.Quasithin.conjClosure V H) φ V
      ≤ Subgroup.closure {x : X | x * x = 1} := by
    intro x hx
    obtain ⟨k, hkV, rfl⟩ := SevenK.mem_barSub.1 hx
    refine Subgroup.subset_closure ?_
    show φ k * φ k = 1
    have hk2 : k * k = 1 :=
      Subtype.ext (by simpa [pow_two] using h.hyp.h6.elemAbelian.2 (k : G) hkV)
    rw [← map_mul, hk2, map_one]
  have hle := Subgroup.normalClosure_le_normal
    (N := Subgroup.closure {x : X | x * x = 1}) hbar_le
  rw [h1st] at hle
  exact top_le_iff.mp hle

private theorem w16l_he_stab_space (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) {t : G} (ht : t ∈ H) {j : ↥H} (hj : (j : G) ∈ V)
    (hnc' : ¬ ∀ x ∈ V, ∀ y ∈ CFSG.Quasithin.conjSubgroup V t, x * y = y * x)
    (hstab : (D.sp (CFSG.Quasithin.conjSubgroup V₀ t)).map
      ((D.ρ j : D.W ≃ₗ[ZMod 2] D.W) : D.W →ₗ[ZMod 2] D.W)
      = D.sp (CFSG.Quasithin.conjSubgroup V₀ t)) :
    (j : G) ∈ U ⊔ V₀ := by
  have hKn : H ≤ Subgroup.normalizer (iSub16 V H : Set G) :=
    CFSG.Quasithin.le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H
  have hV0_le_I : V₀ ≤ iSub16 V H :=
    (le_inf h.hyp.h6.le (h.V₀_le_pCoreOf h5 hS hH.1 hV)).trans
      (CFSG.Quasithin.le_conjClosure _ _)
  have hV0t_le_I : CFSG.Quasithin.conjSubgroup V₀ t ≤ iSub16 V H := by
    intro x hx
    rw [CFSG.Quasithin.mem_conjSubgroup_iff] at hx
    have hmem : t * x * t⁻¹ ∈ iSub16 V H := hV0_le_I hx
    have h := (Subgroup.mem_normalizer_iff.1 (hKn (H.inv_mem ht)) (t * x * t⁻¹)).1 hmem
    simpa [mul_assoc] using h
  have hj2 : (j : G) * (j : G) = 1 := by
    simpa [pow_two] using h.hyp.h6.elemAbelian.2 (j : G) hj
  have hmem_sp : ∀ x ∈ CFSG.Quasithin.conjSubgroup V₀ t,
      (j : G) * x * (j : G)⁻¹ ∈ CFSG.Quasithin.conjSubgroup V₀ t := by
    intro x hx
    have hxI : x ∈ iSub16 V H := hV0t_le_I hx
    have hxsp : D.ι x ∈ D.sp (CFSG.Quasithin.conjSubgroup V₀ t) := ⟨x, ⟨hx, hxI⟩, rfl⟩
    have hmap : D.ρ j (D.ι x) ∈ D.sp (CFSG.Quasithin.conjSubgroup V₀ t) := by
      rw [← hstab]
      exact Submodule.mem_map.2 ⟨D.ι x, hxsp, rfl⟩
    rw [D.ρ_ι j x hxI] at hmap
    have hjeI : (j : G) * x * (j : G)⁻¹ ∈ iSub16 V H :=
      (Subgroup.mem_normalizer_iff.1 (hKn j.2) x).1 hxI
    obtain ⟨e, he, hι⟩ := D.mem_sp.1 hmap
    rw [← D.ι_injOn he.2 hjeI hι]
    exact he.1
  have hnorm : (j : G) ∈ Subgroup.normalizer (CFSG.Quasithin.conjSubgroup V₀ t : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hmem_sp x hx, fun hx => ?_⟩
    have hjj : (j : G) * ((j : G) * x * (j : G)⁻¹) * (j : G)⁻¹ = x := by
      have h1 : (j : G) * ((j : G) * x * (j : G)⁻¹) * (j : G)⁻¹ =
          ((j : G) * (j : G)) * x * ((j : G)⁻¹ * (j : G)⁻¹) := by group
      rw [h1, show (j : G)⁻¹ * (j : G)⁻¹ = ((j : G) * (j : G))⁻¹ by rw [mul_inv_rev],
        hj2, inv_one, one_mul, mul_one]
    rw [← hjj]
    exact hmem_sp ((j : G) * x * (j : G)⁻¹) hx
  have hjM : (j : G) ∈ CFSG.Quasithin.conjSubgroup M t := by
    rw [← E3.conjSubgroup_normalizer V₀ t, h.hyp.normalizer₀] at hnorm
    exact hnorm
  have hfive : V ⊓ CFSG.Quasithin.conjSubgroup M t = U ⊔ V₀ :=
    h5 hS h hH.1 hV t ht hnc'
  rw [← hfive]
  exact ⟨hj, hjM⟩

section Certified


theorem IsMinFam16.he_of_noncomm (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) {X : Type} [Group X]
    {φ : ↥(CFSG.Quasithin.conjClosure V H) →* X}
    (hφ : SevenK.IsBarMap (CFSG.Quasithin.conjClosure V H) (iSub16 V H) φ)
    {ρ : X →* LGL 2 D.W}
    (hρ : ∀ k : ↥(CFSG.Quasithin.conjClosure V H),
      ρ (φ k) = D.ρ (IsMinFam16.inclK h hH k))
    (g : ↥(CFSG.Quasithin.conjClosure V H))
    (hnc : ¬ ∀ x ∈ V, ∀ y ∈ CFSG.Quasithin.conjSubgroup V (g : G), x * y = y * x) :
    (∀ a ∈ SevenK.barSub (CFSG.Quasithin.conjClosure V H) φ V,
      ((D.sp V₀).map ((ρ (φ g) : D.W ≃ₗ[ZMod 2] D.W) : D.W →ₗ[ZMod 2] D.W)).map
        ((ρ a : D.W ≃ₗ[ZMod 2] D.W) : D.W →ₗ[ZMod 2] D.W) =
          (D.sp V₀).map ((ρ (φ g) : D.W ≃ₗ[ZMod 2] D.W) : D.W →ₗ[ZMod 2] D.W) → a = 1) ∧
    (∀ a ∈ SevenK.barSub (CFSG.Quasithin.conjClosure V H) φ V,
      ((D.sp V₀).map ((ρ (φ g)⁻¹ : D.W ≃ₗ[ZMod 2] D.W) : D.W →ₗ[ZMod 2] D.W)).map
        ((ρ a : D.W ≃ₗ[ZMod 2] D.W) : D.W →ₗ[ZMod 2] D.W) =
          (D.sp V₀).map ((ρ (φ g)⁻¹ : D.W ≃ₗ[ZMod 2] D.W) : D.W →ₗ[ZMod 2] D.W) → a = 1) := by
  classical
  have hKH : CFSG.Quasithin.conjClosure V H ≤ H := IsMinFam16.conjClosure_le_H h hH
  have hUVI : U ⊔ V₀ ≤ iSub16 V H := by
    rw [← Cex16.inf_iSub16_eq h1 h5 hS h hH.1 hV]
    exact inf_le_right
  have hnc_inv : ¬ ∀ x ∈ V, ∀ y ∈ CFSG.Quasithin.conjSubgroup V (g : G)⁻¹,
      x * y = y * x := by
    intro hall
    apply hnc
    intro x hx y hy
    rw [CFSG.Quasithin.mem_conjSubgroup_iff] at hy
    have hw : (g : G) * x * (g : G)⁻¹ ∈ CFSG.Quasithin.conjSubgroup V (g : G)⁻¹ := by
      rw [CFSG.Quasithin.mem_conjSubgroup_iff]
      have e : (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) * (g : G)⁻¹⁻¹ = x := by group
      rw [e]
      exact hx
    have hzy := hall ((g : G) * y * (g : G)⁻¹) hy ((g : G) * x * (g : G)⁻¹) hw
    have h2 : y * x = x * y := by
      have h3 := congrArg (fun z => (g : G)⁻¹ * z * (g : G)) hzy
      simpa [mul_assoc] using h3
    exact h2.symm
  constructor
  · intro a ha hstab
    obtain ⟨k, hkV, rfl⟩ := SevenK.mem_barSub.1 ha
    let j : ↥H := IsMinFam16.inclK h hH k
    have hspace : (D.sp V₀).map
        ((ρ (φ g) : D.W ≃ₗ[ZMod 2] D.W) : D.W →ₗ[ZMod 2] D.W)
        = D.sp (CFSG.Quasithin.conjSubgroup V₀ (g : G)⁻¹) := by
      change conjSub (ρ (φ g)) (D.sp V₀)
        = D.sp (CFSG.Quasithin.conjSubgroup V₀ (g : G)⁻¹)
      rw [hρ g]
      exact D.conjSub_sp V₀ (IsMinFam16.inclK h hH g)
    have hstab' : (D.sp (CFSG.Quasithin.conjSubgroup V₀ (g : G)⁻¹)).map
        ((D.ρ j : D.W ≃ₗ[ZMod 2] D.W) : D.W →ₗ[ZMod 2] D.W)
        = D.sp (CFSG.Quasithin.conjSubgroup V₀ (g : G)⁻¹) := by
      have hρk : (ρ (φ k) : D.W ≃ₗ[ZMod 2] D.W) = D.ρ j := by
        rw [hρ k]
      rw [hspace, hρk] at hstab
      exact hstab
    have hmem := w16l_he_stab_space h5 hS h hH hV D
      (H.inv_mem (hKH g.2)) hkV hnc_inv hstab'
    exact (hφ.ker_iff k).2 (hUVI hmem)
  · intro a ha hstab
    obtain ⟨k, hkV, rfl⟩ := SevenK.mem_barSub.1 ha
    let j : ↥H := IsMinFam16.inclK h hH k
    have hspace : (D.sp V₀).map
        ((ρ (φ g⁻¹) : D.W ≃ₗ[ZMod 2] D.W) : D.W →ₗ[ZMod 2] D.W)
        = D.sp (CFSG.Quasithin.conjSubgroup V₀ (g : G)) := by
      change conjSub (ρ (φ g⁻¹)) (D.sp V₀)
        = D.sp (CFSG.Quasithin.conjSubgroup V₀ (g : G))
      rw [hρ (g⁻¹)]
      simpa [IsMinFam16.inclK] using D.conjSub_sp V₀ (IsMinFam16.inclK h hH (g⁻¹))
    have hstab' : (D.sp (CFSG.Quasithin.conjSubgroup V₀ (g : G))).map
        ((D.ρ j : D.W ≃ₗ[ZMod 2] D.W) : D.W →ₗ[ZMod 2] D.W)
        = D.sp (CFSG.Quasithin.conjSubgroup V₀ (g : G)) := by
      have hρk : (ρ (φ k) : D.W ≃ₗ[ZMod 2] D.W) = D.ρ j := by
        rw [hρ k]
      simp only [← map_inv] at hstab
      rw [hspace, hρk] at hstab
      exact hstab
    have hmem := w16l_he_stab_space h5 hS h hH hV D (hKH g.2) hkV hnc hstab'
    exact (hφ.ker_iff k).2 (hUVI hmem)

end Certified

theorem w16l_exists_noncomm_conj {X Y : Type} [Group X] [Group Y] (θ : X →* Y)
    (hθ : Function.Surjective θ) {A : Subgroup X} {B : Subgroup Y}
    (hAB : A.map θ = B) (hB : B ≠ ⊥) (hBel : IsElemAbelian 2 B)
    (hgen : Subgroup.normalClosure (B : Set Y) = ⊤)
    (hcore : ∀ N : Subgroup Y, N.Normal → IsPGroup 2 N → N = ⊥) :
    ∃ l : X, ∃ a ∈ A, ∃ b ∈ A.map (MulAut.conj l).toMonoidHom, a * b ≠ b * a := by
  classical
  by_contra hcon
  have hall : ∀ l : X, ∀ a ∈ A, ∀ b ∈ A.map (MulAut.conj l).toMonoidHom,
      a * b = b * a := by
    intro l a ha b hb
    by_contra hne
    exact hcon ⟨l, a, ha, b, hb, hne⟩
  have hpair : ∀ t : Y, ∀ b ∈ B, ∀ b' ∈ B,
      b * (t * b' * t⁻¹) = (t * b' * t⁻¹) * b := by
    intro t b hb b' hb'
    obtain ⟨l, hl⟩ := hθ t
    have hbA : b ∈ A.map θ := by rwa [hAB]
    have hbA' : b' ∈ A.map θ := by rwa [hAB]
    obtain ⟨a, haA, ha⟩ := Subgroup.mem_map.1 hbA
    obtain ⟨c, hcA, hc⟩ := Subgroup.mem_map.1 hbA'
    have hc' : (MulAut.conj l) c ∈ A.map (MulAut.conj l).toMonoidHom :=
      Subgroup.mem_map.2 ⟨c, hcA, rfl⟩
    have hcomm := hall l a haA ((MulAut.conj l) c) hc'
    have hthis := congrArg θ hcomm
    simp only [map_mul, map_inv, MulAut.conj_apply] at hthis
    rwa [ha, hc, hl] at hthis
  have hpairC : ∀ t u : Y, ∀ b ∈ B, ∀ b' ∈ B,
      (t * b * t⁻¹) * (u * b' * u⁻¹) = (u * b' * u⁻¹) * (t * b * t⁻¹) := by
    intro t u b hb b' hb'
    have h := hpair (t⁻¹ * u) b hb b' hb'
    have h2 : (t * b * t⁻¹) * (u * b' * u⁻¹)
        = t * (b * ((t⁻¹ * u) * b' * (t⁻¹ * u)⁻¹)) * t⁻¹ := by group
    have h3 : t * (((t⁻¹ * u) * b' * (t⁻¹ * u)⁻¹) * b) * t⁻¹
        = (u * b' * u⁻¹) * (t * b * t⁻¹) := by group
    rw [h2, h, h3]
  have hkcomm : (Group.conjugatesOfSet (B : Set Y)).Pairwise Commute := by
    intro x hx y hy _
    obtain ⟨b, hb, hcx⟩ := Group.mem_conjugatesOfSet_iff.1 hx
    obtain ⟨b', hb', hcy⟩ := Group.mem_conjugatesOfSet_iff.1 hy
    obtain ⟨t, ht⟩ := isConj_iff.1 hcx
    obtain ⟨u, hu⟩ := isConj_iff.1 hcy
    rw [← ht, ← hu]
    exact hpairC t u b hb b' hb'
  haveI : IsMulCommutative ↥(Subgroup.closure (Group.conjugatesOfSet (B : Set Y))) :=
    Subgroup.isMulCommutative_closure hkcomm
  have hexp : ∀ y ∈ Subgroup.closure (Group.conjugatesOfSet (B : Set Y)), y ^ 2 = 1 := by
    intro y hy
    refine Subgroup.closure_induction (p := fun y _ => y ^ 2 = 1) ?_ ?_ ?_ ?_ hy
    · intro x hx
      obtain ⟨b, hb, hcx⟩ := Group.mem_conjugatesOfSet_iff.1 hx
      obtain ⟨t, ht⟩ := isConj_iff.1 hcx
      rw [← ht, pow_two]
      have hb2 : b * b = 1 := by simpa [pow_two] using hBel.2 b hb
      rw [show (t * b * t⁻¹) * (t * b * t⁻¹) = t * (b * b) * t⁻¹ by group,
        hb2, mul_one, mul_inv_cancel]
    · simp
    · intro x y hx hy ihx ihy
      have hxy : x * y = y * x :=
        congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥(Subgroup.closure
          (Group.conjugatesOfSet (B : Set Y)))) ⟨y, hy⟩)
      rw [pow_two]
      calc (x * y) * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [hxy]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by
            rw [show x * x = 1 from by simpa [pow_two] using ihx,
              show y * y = 1 from by simpa [pow_two] using ihy, mul_one]
    · intro x hx ihx
      rw [pow_two, show x⁻¹ * x⁻¹ = (x * x)⁻¹ by rw [mul_inv_rev],
        show x * x = 1 from by simpa [pow_two] using ihx, inv_one]
  have hP : IsPGroup 2 ↥(Subgroup.closure (Group.conjugatesOfSet (B : Set Y))) := by
    intro x
    refine ⟨1, ?_⟩
    have hx2 : x ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hexp (x : Y) x.2)
    simpa using hx2
  have htopP : IsPGroup 2 (⊤ : Subgroup Y) := by
    rw [← hgen]
    exact hP
  have hbot : (⊤ : Subgroup Y) = ⊥ := hcore ⊤ inferInstance htopP
  exact hB (le_bot_iff.mp (le_top.trans (le_of_eq hbot)))

end CFSG.LocalAnalysis.WeakClosure81

end
