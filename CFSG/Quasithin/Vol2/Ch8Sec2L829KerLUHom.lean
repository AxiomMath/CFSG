module

public import CFSG.Quasithin.Background.D2Basic
public import CFSG.Quasithin.Background.AutOnBasics

public section

namespace CFSG.Quasithin.H13

open scoped IsMulCommutative

theorem autSub_hom_klu {G : Type} [Group G] (V : Subgroup G) [IsMulCommutative V] (L U : Subgroup G)
    (F : Subgroup V) (hUV : U ≤ V) (hF : ∀ v : V, v ∈ F ↔ (v : G) ∈ U)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hLU : L ≤ Subgroup.normalizer (U : Set G)) :
    ∃ Φ : L →* MulAut F, (∀ x : L, Φ x ∈ autSub (autOn L V) F) ∧
      (∀ φ ∈ autSub (autOn L V) F, ∃ x : L, Φ x = φ) ∧
      (∀ x : L, Φ x = 1 ↔ (x : G) ∈ Subgroup.centralizer (U : Set G)) := by
  let ψ : L →* MulAut V := (conjAct V).comp (Subgroup.inclusion hLV)
  have hψapp : ∀ (x : L) (v : V), ((ψ x v : V) : G) = (x : G) * (v : G) * (x : G)⁻¹ :=
    fun x v => AutOn.coe_conjAct_apply V (Subgroup.inclusion hLV x) v
  have hstab : ∀ x : L, ψ x ∈ stabSub F := by
    intro x
    refine mem_stabSub.mpr (fun v => ?_)
    rw [hF, hF, hψapp]
    exact (Subgroup.mem_normalizer_iff.mp (hLU x.2) (v : G)).symm
  let ψ' : L →* stabSub F := ψ.codRestrict (stabSub F) hstab
  let Φ : L →* MulAut F := (resHom F).comp ψ'
  have hΦapp : ∀ (x : L) (f : F), ((Φ x f : F) : V) = ψ x (f : V) :=
    fun x f => resHom_apply F (ψ' x) f
  refine ⟨Φ, fun x => ?_, fun φ hφ => ?_, fun x => ?_⟩
  · refine mem_autSub.mpr ⟨ψ' x, ?_, rfl⟩
    exact AutOn.conjAct_mem_autOn_of_mem (hLV x.2) x.2
  · obtain ⟨g, hgX, hgφ⟩ := mem_autSub.mp hφ
    obtain ⟨y, hy, hyL, hyg⟩ := AutOn.mem_autOn_iff_exists.mp hgX
    refine ⟨⟨y, hyL⟩, ?_⟩
    have hg : ψ' ⟨y, hyL⟩ = g := Subtype.ext hyg
    show resHom F (ψ' ⟨y, hyL⟩) = φ
    rw [hg, hgφ]
  · constructor
    · intro h
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have h1 : Φ x ⟨⟨u, hUV hu⟩, (hF ⟨u, hUV hu⟩).mpr hu⟩ = ⟨⟨u, hUV hu⟩, (hF ⟨u, hUV hu⟩).mpr hu⟩ := by
        rw [h]
        rfl
      have h2 := congrArg (fun f : F => ((f : V) : G)) h1
      simp only at h2
      rw [hΦapp, hψapp] at h2
      exact (mul_inv_eq_iff_eq_mul.mp h2).symm
    · intro hx
      apply MulEquiv.ext
      intro f
      have key : Φ x f = f := by
        apply Subtype.ext
        apply Subtype.ext
        rw [hΦapp, hψapp]
        exact mul_inv_eq_iff_eq_mul.mpr
          (Subgroup.mem_centralizer_iff.mp hx _ ((hF f.1).mp f.2)).symm
      exact key

end CFSG.Quasithin.H13
