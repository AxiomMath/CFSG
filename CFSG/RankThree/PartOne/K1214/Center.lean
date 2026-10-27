module

public import CFSG.RankThree.PartOne.K1214.XFrame
import CFSG.RankThree.PartOne.S12.Sec12Three
public import CFSG.RankThree.PartOne.S12.Sec12FusSplit

public section

namespace CFSG.RankThree.PartOne.K1214

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.GroupTheory

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
  {b : G} {K I X P Q : Subgroup G}

omit [Finite G] in
theorem P_le_normalizer_of_omega (hom : omegaOne p P = E) :
    P ≤ Subgroup.normalizer (E : Set G) := fun y hy => by
  have := Sec12Fus.mem_normalizer_omegaOne (p := p) (Subgroup.le_normalizer hy)
  rwa [hom] at this

omit [Finite G] in
theorem E_le_P (hC : Choice1212 p E b I X P Q) : E ≤ P := hC.X_sylow.2.trans hC.P_sylow.2

omit [Finite G] in
theorem c_not_mem_Q (hF : Field1213 p A c L b K I) (hC : Choice1212 p E b I X P Q) : c ∉ Q := by
  intro hcQ
  have hQle : Q ≤ I ⊔ Subgroup.centralizer (I : Set G) := by
    rw [hC.Q_eq]
    exact sup_le (le_sup_of_le_right inf_le_left) (le_sup_of_le_left inf_le_right)
  exact hF.field.2.1 (hQle hcQ)

theorem kf1214Center_of_u5 (hU5 : KF1214U5) : KF1214Center := by
  intro G _ _ p A c L E ctx b K I X P Q hL hC hF ha hom
  have hp : p.Prime := ctx.hyp.prime
  have hn12 : ¬ RowModel p L 12 := hU5 G p A c L E ctx
  have hnH := not_dvd_torusImage ctx hn12
  have hPE := P_le_normalizer_of_omega hom
  have hEP := E_le_P hC
  have hcE := c_mem_E ctx
  have hcP : c ∈ P := hEP hcE
  have hcQ := c_not_mem_Q hF hC
  obtain ⟨f, hfP, hPf⟩ := ha.P_gen
  have hab := quotient_abelian_of_sup_zpowers ha.Q_norm.1 ha.Q_norm.2 hfP hPf
  have hD := data_of_ctx ctx
  have hcB := c_not_mem_B ctx
  have hBQ : ∀ z ∈ E ⊓ L, z ∈ Q := by
    intro z hz
    have hzE : z ∈ E := hz.1
    have hzB : (⟨z, hzE⟩ : ↥E) ∈ (E ⊓ L).subgroupOf E := Subgroup.mem_subgroupOf.2 hz
    obtain ⟨w, hw⟩ := hD.xiHom_surjective hcB ⟨⟨z, hzE⟩, hzB⟩
    have hw' := congrArg (fun t : ↥((E ⊓ L).subgroupOf E) => ((t : ↥E) : G)) hw
    obtain ⟨y, hyX, hy, hyw⟩ := exists_mem_X_conjAut hp hC w.2
    have h1 := Equivariance.coe_conjAut hy ⟨c, hcE⟩
    rw [hyw] at h1
    have h2 : y * c * y⁻¹ * c⁻¹ = z := by
      have h3 : (((torusWeyl E).subtype (w : ↥(torusWeyl E)) ⟨c, hcE⟩ * (⟨c, hcE⟩ : ↥E)⁻¹ : ↥E) : G)
          = z := hw'
      rw [Subgroup.coe_mul, Subgroup.coe_inv] at h3
      rw [← h3]
      show y * c * y⁻¹ * c⁻¹ = (((w : ↥(torusWeyl E)) : MulAut E) ⟨c, hcE⟩ : G) * c⁻¹
      rw [h1]
    have h4 := hab ⟨y, hC.P_sylow.2 hyX⟩ ⟨c, hcP⟩
    rw [← h2]
    exact Subgroup.mem_subgroupOf.1 h4
  have h4a : Q ⊓ E = E ⊓ L := by
    apply le_antisymm
    · rintro e ⟨heQ, heE⟩
      obtain ⟨b', hb', a, hba⟩ := hD.exists_decomp hcB ⟨e, heE⟩
      have hb'G : (b' : G) ∈ E ⊓ L := Subgroup.mem_subgroupOf.1 hb'
      have he_eq : e = (b' : G) * c ^ a := by
        have := congrArg Subtype.val hba
        simpa using this
      have hca : c ^ a ∈ Q := by
        have h1 : c ^ a = (b' : G)⁻¹ * e := by
          rw [he_eq]
          group
        rw [h1]
        exact Q.mul_mem (Q.inv_mem (hBQ _ hb'G)) heQ
      have hbot := Sec12Three.zpowers_inf_eq_bot hp (Sec12Three.orderOf_c ctx.hyp) hcQ
      have hca1 : c ^ a = 1 := by
        have hmem : c ^ a ∈ Subgroup.zpowers c ⊓ Q :=
          ⟨Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) a, hca⟩
        rw [hbot, Subgroup.mem_bot] at hmem
        exact hmem
      rw [he_eq, hca1, mul_one]
      exact hb'G
    · intro z hz
      exact ⟨hBQ z hz, hz.1⟩
  have h4b : E ⊓ L = omegaOne p ((Subgroup.center ↥P).map P.subtype) := by
    apply le_antisymm
    · intro z hz
      have hzP : z ∈ P := hEP hz.1
      have hzp : z ^ p = 1 := Sec12Three.pow_eq_one_of_mem_E ctx.hyp hz.1
      have hcent : (⟨z, hzP⟩ : ↥P) ∈ Subgroup.center ↥P := by
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        have h1 := fix_B ctx hnH hC hPE g.2 hz
        show (g : G) * z = z * g
        calc (g : G) * z = ((g : G) * z * (g : G)⁻¹) * g := by group
          _ = z * g := by rw [h1]
      exact Subgroup.subset_closure ⟨⟨⟨z, hzP⟩, hcent, rfl⟩, hzp⟩
    · refine (Subgroup.closure_le _).2 ?_
      rintro x ⟨⟨x', hx', rfl⟩, hxp⟩
      have hxP : (x' : G) ∈ P := x'.2
      have hxE : (x' : G) ∈ E := by
        rw [← hom]
        exact Subgroup.subset_closure ⟨hxP, hxp⟩
      have hfix : (x' : G) ∈ pCoreFixed p E := by
        refine mem_pCoreFixed_of_fixed ⟨(x' : G), hxE⟩ ?_
        intro φ hφ
        obtain ⟨y, hyX, hy, hyφ⟩ := exists_mem_X_conjAut hp hC hφ
        apply Subtype.ext
        have h1 := Equivariance.coe_conjAut hy ⟨(x' : G), hxE⟩
        rw [hyφ] at h1
        rw [h1]
        have hc := Subgroup.mem_center_iff.1 hx' ⟨y, hC.P_sylow.2 hyX⟩
        have h2 : y * (x' : G) = (x' : G) * y := congrArg Subtype.val hc
        calc y * (x' : G) * y⁻¹ = (x' : G) * y * y⁻¹ := by rw [h2]
          _ = x' := by group
      exact ctx.ten.1 ▸ hfix
  exact ⟨h4a, h4b⟩

end CFSG.RankThree.PartOne.K1214
