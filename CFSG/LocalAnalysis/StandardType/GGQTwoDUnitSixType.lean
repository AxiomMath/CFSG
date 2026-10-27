module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixBase
public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMBridge
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBaseThm
public import CFSG.LocalAnalysis.StandardType.GGNsq2QuotNorm
import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthBase
import CFSG.LocalAnalysis.StandardType.GGNsq2QuotAut
import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

namespace NsQuot

variable {G : Type} [Group G] [Finite G] {Q : Type} [Group Q]
variable {p : ℕ} {N : Subgroup G} {f : ↥N →* Q} {L Bs Z : Subgroup G}

theorem Datum.map_automizer_le (hD : Datum p N f L Bs Z) {X : Subgroup G} (hXN : X ≤ N) :
    (ggAutomizer X Bs).map (MulAut.congr hD.tau).toMonoidHom ≤
      ggAutomizer (img N f X) (img N f Bs) := by
  unfold ggAutomizer
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨φ, ⟨g, hgX, hgN, hφ⟩, rfl⟩
  have hgN' : g ∈ N := hXN hgX
  refine Subgroup.subset_closure ⟨f ⟨g, hgN'⟩, mem_img.2 ⟨⟨g, hgN'⟩, hgX, rfl⟩, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      obtain ⟨b, hb, rfl⟩ := mem_img.1 hq
      have hbBs : (b : G) ∈ Bs := hb
      have h := hφ ⟨b, hbBs⟩
      have hmem : g * (b : G) * g⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hgN _).mp hbBs
      exact mem_img.2 ⟨⟨g * b * g⁻¹, N.mul_mem (N.mul_mem hgN' b.2) (N.inv_mem hgN')⟩, hmem,
        by rw [show (⟨g * b * g⁻¹, _⟩ : ↥N) = ⟨g, hgN'⟩ * b * ⟨g, hgN'⟩⁻¹ from rfl, map_mul,
          map_mul, map_inv]⟩
    · intro hq
      obtain ⟨b, hb, hfb⟩ := mem_img.1 hq
      have hbBs : (b : G) ∈ Bs := hb
      have hmem : g⁻¹ * (b : G) * g⁻¹⁻¹ ∈ Bs :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) _).mp hbBs
      have hq' : q = f ⟨g⁻¹ * b * g, N.mul_mem (N.mul_mem (N.inv_mem hgN') b.2) hgN'⟩ := by
        rw [show (⟨g⁻¹ * b * g, _⟩ : ↥N) = ⟨g, hgN'⟩⁻¹ * b * ⟨g, hgN'⟩ from rfl, map_mul,
          map_mul, map_inv, hfb]
        group
      rw [hq']
      exact mem_img.2 ⟨_, by simpa using hmem, rfl⟩
  · intro q
    obtain ⟨b, rfl⟩ := hD.tau.surjective q
    change ((MulAut.congr hD.tau φ (hD.tau b) : ↥(img N f Bs)) : Q) = _
    rw [congr_apply_tau, Datum.tau_apply, Datum.tau_apply]
    have hφb : ((φ b : ↥Bs) : G) = g * b * g⁻¹ := hφ b
    have hmemN : (⟨((φ b : ↥Bs) : G), hD.BsN (φ b).2⟩ : ↥N) = ⟨g, hgN'⟩ *
        ⟨(b : G), hD.BsN b.2⟩ * ⟨g, hgN'⟩⁻¹ := Subtype.ext hφb
    rw [hmemN, map_mul, map_mul, map_inv]

theorem Datum.map_automizer_eq (hD : Datum p N f L Bs Z) {X : Subgroup G} (hZX : Z ≤ X)
    (hXN : X ≤ N) :
    (ggAutomizer X Bs).map (MulAut.congr hD.tau).toMonoidHom =
      ggAutomizer (img N f X) (img N f Bs) :=
  le_antisymm (hD.map_automizer_le hXN) (hD.automizer_le_map hZX hXN)

end NsQuot

theorem GGWeylOfType.of_congr {G G' : Type} [Group G] [Group G'] {p : ℕ} {Bs : Subgroup G}
    {Bs' : Subgroup G'} (σ : ↥Bs ≃* ↥Bs') {ι : Type} {M : CoxeterMatrix ι}
    {A : Subgroup (MulAut ↥Bs)} {A' : Subgroup (MulAut ↥Bs')}
    (hA : A.map (MulAut.congr σ).toMonoidHom = A') (h : GGWeylOfType p M A') :
    GGWeylOfType p M A := by
  obtain ⟨e', he'⟩ := h
  let ι' : ↥A ≃* ↥A' :=
    (MulEquiv.subgroupMap (MulAut.congr σ) A).trans (MulEquiv.subgroupCongr hA)
  refine ⟨e'.trans ι'.symm, fun i => ?_⟩
  rw [← ggIsReflection_congr_iff σ]
  have hval : MulAut.congr σ (((e'.trans ι'.symm) (M.simple i) : ↥A) : MulAut ↥Bs) =
      ((e' (M.simple i) : ↥A') : MulAut ↥Bs') := by
    have h1 : ι' ((e'.trans ι'.symm) (M.simple i)) = e' (M.simple i) := by
      simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    exact congrArg Subtype.val h1
  rw [hval]
  exact he' i

end CFSG.StandardType

namespace CFSG.StandardType.QTwo

open CFSG.Assembly

theorem ggQTwoDRMBaseTypeInputOn_six
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) :
    GGQTwoDRMBaseTypeInputOn (fun m => m = 6) := by
  classical
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM
  subst hm
  have hp : p = 3 := by
    obtain ⟨r, hr, hrc, h6⟩ := hcfg.2.2.2.2
    exact ggQTwo_p_eq_three hcfg.1 M e hcfg.2.2.2.1 hr hrc h6
  subst hp
  by_cases hL : qtwoOrthL G L 𝒦
  · exact Or.inr (ggQTwoDOrthBase_weylD ggLabelRigidInput_holds hTBF hWI hcfg e' (by norm_num)
      hM hL)
  rcases ggQTwoDUnit_memberUnitary_L_or_u62 ggLabelRigidInput_holds hTBF hcfg e' (by norm_num) hM
      hL with hU | ⟨-, hmark⟩
  · obtain ⟨F0, hF0, hF0fin, hF0char, ψ, ε, hbase⟩ :=
      ggQTwoDUnit_base_of_member hTBF hWI hcfg e' (by norm_num) hM hU
    exact Or.inl (qtwoD_weylA_of_unitBase hbase (by norm_num))
  · obtain ⟨-, K, hKf, hKfin, hKchar, Q, hQ, hQfin, f, ψ, ε, hx, hD, hbase⟩ :=
      ggQTwoDUnitSix_quotBase hTBF hWI hcfg e' hM hmark
    exact Or.inl (GGWeylOfType.of_congr hD.tau (hD.map_automizer_eq hD.ZL hD.LN)
      (qtwoD_weylA_of_unitBase hbase (by norm_num)))

end CFSG.StandardType.QTwo

end
