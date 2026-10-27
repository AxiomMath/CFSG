module

public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619Contracts
import CFSG.LocalAnalysis.StandardType.GGUSixTwoLayer
import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndModel
import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace S2MathAs3_1619Final

open CFSG CFSG.Assembly CFSG.StandardType

private theorem ltrcd_ggFixSub_eq_ggFix {X : Type*} [Group X] (a : MulAut X) :
    ggFixSub a = ggFix a :=
  Subgroup.ext fun _ => Iff.rfl

theorem coverDescent_holds (R : Type) [Group R] (I : Set (MulAut R)) (h : RawActionAt R I) :
    NoSetupAt R I := by
  intro L' _ _ ψ hψ hker hperf e J a hsetup
  unfold GGRankOneSetup at hsetup
  obtain ⟨hp, hp2, he1, he3, ⟨φ, hφI, hφ⟩, hJ, h2n, hlabel, hae, ⟨φ', hφ'I, hφ'⟩, hpres, hnon⟩ :=
    hsetup
  have hφne : φ ≠ 1 := by
    intro h1
    have heq1 : e = 1 :=
      TypeA.mulAut_eq_of_forall ψ hker hperf (a := e) (b := 1) fun l => by
        rw [MulAut.one_apply, ← hφ l, h1, MulAut.one_apply]
    exact he1 heq1
  have hφ3 : φ ^ 3 = 1 :=
    TypeA.induced_unique ψ hψ (TypeA.induced_pow ψ hφ 3) fun l => by
      simp only [MulAut.one_apply, he3]
  have hcomm : φ' * φ = φ * φ' :=
    TypeA.induced_unique (a := a * e) ψ hψ
      (fun l => by simp only [MulAut.mul_apply, hφ, hφ' (e l)])
      (fun l => by
        have hh : a (e l) = e (a l) := by
          have h2 := congrArg (fun f : MulAut L' => f l) hae
          simpa only [MulAut.mul_apply] using h2
        simp only [MulAut.mul_apply, hφ', hφ (a l), hh])
  let C : Subgroup R := J.map ψ
  have hJfix : CFSG.Assembly.IsComponentOf J (ggFix e) := by
    rw [ltrcd_ggFixSub_eq_ggFix e] at hJ
    exact hJ
  have hCcomp : CFSG.Assembly.IsComponentOf C (ggFixSub φ) := by
    change CFSG.Assembly.IsComponentOf (J.map ψ) (ggFixSub φ)
    rw [ltrcd_ggFixSub_eq_ggFix φ]
    exact CFSG.StandardType.USixTwo.isComponentOf_map_fix (π := ψ) (a := e) (ab := φ)
      hψ hker hφ hJfix
  let f : ↥J →* ↥C :=
    { toFun := fun j => ⟨ψ (j : L'), ⟨j, j.2, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp }
  have hf : Function.Surjective f := by
    intro c
    obtain ⟨j, hj, hjc⟩ := Subgroup.mem_map.mp (show (c : R) ∈ J.map ψ from c.2)
    exact ⟨⟨j, hj⟩, Subtype.ext hjc⟩
  have hkerf : f.ker ≤ Subgroup.center ↥J := by
    intro j hj
    rw [MonoidHom.mem_ker] at hj
    have hj1 : ψ (j : L') = 1 := by
      have hval := congrArg Subtype.val hj
      simpa [f] using hval
    have hc : (j : L') ∈ Subgroup.center L' := hker (by simpa [MonoidHom.mem_ker] using hj1)
    rw [Subgroup.mem_center_iff]
    intro x
    ext
    exact Subgroup.mem_center_iff.mp hc (x : L')
  let g : ↥J →* ↥C ⧸ Subgroup.center ↥C :=
    (QuotientGroup.mk' (Subgroup.center ↥C)).comp f
  have hJperf : Group.IsPerfect ↥J := Group.IsPerfect.mk hJ.2.2.1
  have hcenter_eq : Subgroup.center ↥J = g.ker := by
    change Subgroup.center ↥J = ((QuotientGroup.mk' (Subgroup.center ↥C)).comp f).ker
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact (CFSG.LocalCores.comap_center_eq_of_perfect hJperf f hf hkerf).symm
  have hg : Function.Surjective g :=
    (QuotientGroup.mk'_surjective (Subgroup.center ↥C)).comp hf
  let e : ↥J ⧸ Subgroup.center ↥J ≃* ↥C ⧸ Subgroup.center ↥C :=
    (QuotientGroup.quotientMulEquivOfEq hcenter_eq).trans
      (QuotientGroup.quotientKerEquivOfSurjective g hg)
  have he_mk : ∀ j : ↥J, e (QuotientGroup.mk j) = (f j : ↥C ⧸ Subgroup.center ↥C) := by
    intro j
    rfl
  have hClabel : GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel) (↥C ⧸ Subgroup.center ↥C) :=
    ggHasLabel_of_mulEquiv e hlabel
  have hpresC : ∀ c ∈ C, φ' c ∈ C := by
    intro c hc
    change c ∈ J.map ψ at hc
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hc
    rw [hφ' j]
    exact Subgroup.mem_map_of_mem ψ (hpres j hj)
  have hQI : QuotientInner C φ' :=
    h φ hφI hφne hφ3 C hCcomp hClabel φ' hφ'I hcomm hpresC
  obtain ⟨z, hz⟩ := hQI
  refine hnon ⟨e.symm z, fun j j' haj => ?_⟩
  have hcf : φ' ((f j : ↥C) : R) = ((f j' : ↥C) : R) := by
    change φ' (ψ (j : L')) = ψ (j' : L')
    rw [hφ' (j : L'), haj]
  have hz' := hz (f j) (f j') hcf
  have h1 : e (QuotientGroup.mk j') = z * e (QuotientGroup.mk j) * z⁻¹ := by
    rw [he_mk j', he_mk j]
    simpa using hz'
  have h2 : (QuotientGroup.mk j' : ↥J ⧸ Subgroup.center ↥J) =
      e.symm z * (QuotientGroup.mk j) * (e.symm z)⁻¹ := by
    have hh := congrArg e.symm h1
    simpa using hh
  exact h2

end S2MathAs3_1619Final

end
