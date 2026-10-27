module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinSingleSupport
public import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit
public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneTorusLift

public section

namespace CFSG.StandardType.SpJoin

open CFSG.Open CFSG.LieType.Universal.Symplectic
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl Matrix

variable {G : Type} [Group G] [Finite G]

theorem spEnd_exists_lift_lam_zero_mul_inv {F : Type} [Field F] [Finite F] {p m : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : 3 ≤ m) (h2 : (2 : F) = 0) {B Bs X Y : Subgroup G}
    (hBs : GGBstar p B Bs) (φ' : StatedSp (m + 1) F →* G) (hinj : Function.Injective φ')
    (hrange : φ'.range = X) (hNX : Bs ≤ Subgroup.normalizer (X : Set G))
    (hinner : ∀ b ∈ Bs, ∃ g ∈ X, ∀ k ∈ X, b * k * b⁻¹ = g * k * g⁻¹)
    (hcent : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ p)
    (hrank : p ^ (m + 1 + 1) ≤ Nat.card Bs) {A : Subgroup (MulAut ↥Bs)}
    (hA : GGWeylOfType p (CoxeterMatrix.B (m + 1 + 1)) A) (hXA : ggAutomizer X Bs ≤ A)
    (hYA : ggAutomizer Y Bs ≤ A)
    (hY : 2 ^ (m + 1) * (m + 1).factorial ≤ Nat.card (ggAutomizer Y Bs)) {z : G} (hz : z ∈ Bs)
    (hzY : z ∈ Subgroup.centralizer (Y : Set G)) (hzX : z ∉ Subgroup.centralizer (X : Set G)) :
    ∃ (ψ : StatedSp (m + 1) F →* G) (g : SpecialLinearGroup (Fin 2) F) (c : G),
      Function.Injective ψ ∧ ψ.range = X ∧ c ∈ Subgroup.centralizer (X : Set G) ∧ c ∈ Bs ∧
        z = ψ (lam (0 : Fin (m + 1)) g) * c ∧
        ∃ s ∈ X, s ∈ Subgroup.normalizer (Bs : Set G) ∧
          s * ψ (lam (0 : Fin (m + 1)) g) * s⁻¹ = (ψ (lam (0 : Fin (m + 1)) g))⁻¹ := by
  classical
  haveI : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 h2
  have hZ : Subgroup.center X = ⊥ := by
    have hZsp : Subgroup.center (StatedSp (m + 1) F) = ⊥ := by
      rw [CFSG.LieType.Universal.Symplectic.center_eq,
        CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]
    have he := Subgroup.map_center_eq (MonoidHom.ofInjective hinj)
    rw [hZsp, Subgroup.map_bot] at he
    rw [← hrange]
    exact he.symm
  obtain ⟨ζ, φ, hl⟩ :=
    exists_plane_torus_lift_of_range hp hp2 h2 φ' hinj hBs hrange hNX hinner hcent hrank
  obtain ⟨u, hu, c, hc, hzuc⟩ := ggBstar_split_of_inner hBs hZ hNX hinner z hz
  have hu' : u ∈ (φ.comp (spPlaneTorus (m + 1) ζ)).range := by
    rw [hl.torus_range]
    exact hu
  obtain ⟨v, hv⟩ := hu'
  have hv1 : v ≠ 1 := by
    rintro rfl
    apply hzX
    have hu1 : u = 1 := by rw [← hv, map_one]
    rw [hzuc, hu1, one_mul]
    exact hc.2
  have hzv : z = (φ.comp (spPlaneTorus (m + 1) ζ)) v * c := by
    rw [hv]
    exact hzuc
  obtain ⟨i, hi0⟩ := Function.ne_iff.mp hv1
  have hi : v i ≠ 1 := hi0
  have hsingle : ∀ j, j ≠ i → v j = 1 := fun j hji =>
    (coord_eq_one_of_orbit hp hp2 (by omega) h2 hl hA hXA hYA hY hz hzY hc.2 hzv
      hji.symm).resolve_left hi
  have hv_eq : v = Pi.mulSingle i (v i) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · rw [Pi.mulSingle_eq_of_ne hj, hsingle j hj]
  obtain ⟨ψ, hψinj, hψrange, hψval⟩ := exists_lift_lam_zero_eq_tor_mulSingle h2 hl i (v i)
  have hzψ : z = ψ (lam (0 : Fin (m + 1)) (ζ (v i))) * c := by
    have h1 : (φ.comp (spPlaneTorus (m + 1) ζ)) v =
        ψ (lam (0 : Fin (m + 1)) (ζ (v i))) := by
      conv_lhs => rw [hv_eq, ← hψval]
    rw [hzv, h1]
  have hle := spSignedGroup_le_torusPerms (p := p) (n := m + 1) h2 hl
  have hmem := hle (coordInv_mem_spSignedGroup (n := m + 1) (p := p) i)
  rw [mem_torusPerms_iff] at hmem
  obtain ⟨s, hs, hconj⟩ := hmem
  have hcoordInv_v : coordInv (m + 1) p i v = v⁻¹ := by
    funext j
    by_cases hj : j = i
    · subst hj
      rw [coordInv_apply, Function.update_self, Pi.inv_apply]
    · rw [coordInv_apply, Function.update_of_ne hj, hv_eq, Pi.mulSingle_eq_of_ne hj,
        Pi.inv_apply, Pi.mulSingle_eq_of_ne hj, inv_one]
  have htor_inv : s * (φ.comp (spPlaneTorus (m + 1) ζ)) v * s⁻¹ =
      ((φ.comp (spPlaneTorus (m + 1) ζ)) v)⁻¹ := by
    rw [hconj v, hcoordInv_v, map_inv]
  have hs_inv : s * ψ (lam (0 : Fin (m + 1)) (ζ (v i))) * s⁻¹ =
      (ψ (lam (0 : Fin (m + 1)) (ζ (v i))))⁻¹ := by
    rw [hψval, ← hv_eq]
    exact htor_inv
  exact ⟨ψ, ζ (v i), c, hψinj, hψrange, hc.2, hc.1, hzψ, s, hs.1, hs.2, hs_inv⟩

end CFSG.StandardType.SpJoin
