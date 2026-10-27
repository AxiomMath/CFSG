module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinOrthExclAux
public import CFSG.LocalAnalysis.StandardType.GGNSJoinOrthPerp
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxBasic
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAux


public section

namespace CFSG.StandardType

namespace NSJoin


open CFSG CFSG.Assembly
open CFSG.StandardType.OrthF3
open TauCeti

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

def nsOrth_reflSet {G : Type} [Group G] [Finite G] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (𝒦 : Finset (Subgroup G)) : Set (MulAut ↥Bs) :=
  {a | a ∈ ggAInf 3 B Bs x L D J ∧ GGIsReflection 3 a ∧ GGRealized 3 Bs a}

def nsOrth_reflClosure {G : Type} [Group G] [Finite G] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (𝒦 : Finset (Subgroup G)) : Subgroup (MulAut ↥Bs) :=
  Subgroup.closure (nsOrth_reflSet B Bs x L D J 𝒦)

theorem nsOrth_le_ainf_left {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} : ggAutomizer L Bs ≤ ggAInf p B Bs x L D J :=
  le_sup_left

theorem nsOrth_le_ainf_nbr {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hnbr : GGNbr p B x D J y K) :
    ggAutomizer K Bs ≤ ggAInf p B Bs x L D J :=
  le_trans (le_iSup₂_of_le y K (le_iSup (fun _ : GGNbr p B x D J y K => ggAutomizer K Bs) hnbr))
    le_sup_right

theorem nsOrth_ainf_le {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {H : Subgroup (MulAut ↥Bs)} (hL : ggAutomizer L Bs ≤ H)
    (hK : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → ggAutomizer K Bs ≤ H) :
    ggAInf p B Bs x L D J ≤ H :=
  sup_le hL (iSup_le fun y => iSup_le fun K => iSup_le fun hnbr => hK y K hnbr)

theorem nsOrth_closure_le_ainf {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} :
    nsOrth_reflClosure B Bs x L D J 𝒦 ≤ ggAInf 3 B Bs x L D J := by
  refine (Subgroup.closure_le _).mpr ?_
  intro a ha
  exact ha.1

theorem nsOrth_autL_le_closure {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hBase : NSBaseFrameInputOf T) (hRootGenL : NSRootGenLInputOf T)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : NSRegularCfgOf T 3 B Bs x L D J 𝒦) :
    ggAutomizer L Bs ≤ nsOrth_reflClosure B Bs x L D J 𝒦 := by
  obtain ⟨ιL, instL, ML, hML, hWeylL, -, -⟩ := hBase G 3 B Bs x L D J 𝒦 hcfg
  have hWM : GGIsWeylMatrix ML := hML.elim (fun h => h.isWeylMatrix) (fun h => h.isWeylMatrix)
  have hWeylL' : GGWeylReflectionGroup 3 (ggAutomizer L Bs) :=
    CFSG.StandardType.GGWeylOfType.weylReflectionGroup hWM hWeylL
  refine le_trans (le_of_eq (nsOrth_weyl_generated hWeylL')) ?_
  refine (Subgroup.closure_le _).mpr ?_
  rintro a ⟨haL, haRe⟩
  exact Subgroup.subset_closure ⟨nsOrth_le_ainf_left haL, haRe,
    hRootGenL G 3 B Bs x L D J 𝒦 hcfg a haL haRe⟩

theorem nsOrth_autK_le_closure {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hRQ : NSRealNbrInputOf T) (hNbrQ4 : NSNbrQFourInputOf T) (hPumpNbr : NSPumpNbrInputOf T)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : NSRegularCfgOf T 3 B Bs x L D J 𝒦) {y : G}
    {K : Subgroup G} (hnbr : GGNbr 3 B x D J y K) :
    ggAutomizer K Bs ≤ nsOrth_reflClosure B Bs x L D J 𝒦 := by
  have hconf : GGConfig 3 B Bs x L D J := hcfg.1.1.1
  have hp3 : Nat.Prime 3 := by norm_num
  have hWeylK : GGWeylReflectionGroup 3 (ggAutomizer K Bs) :=
    (hPumpNbr G 3 B Bs x L D J 𝒦 hcfg y K hnbr).1
  refine le_trans (le_of_eq (nsOrth_weyl_generated hWeylK)) ?_
  refine (Subgroup.closure_le _).mpr ?_
  rintro a ⟨haK, haRe⟩
  have hR : GGReflRealizedIn 3 Bs K :=
    hRQ G B Bs x L D J 𝒦 hcfg y K hnbr (hNbrQ4 G B Bs x L D J 𝒦 hcfg y K hnbr)
  have hyBs : y ∈ Bs := hconf.2.1.1 hnbr.1.2.1
  have hKpc : LargeEvenPComponent 3 (Subgroup.centralizer ({y} : Set G)) K :=
    hnbr.1.2.2.2.2.1
  have haReal : GGRealized 3 Bs a :=
    ggRealized_of_reflRealizedIn hp3 hyBs
      ((CFSG.Assembly.LargeEven.largeEvenPComponent_iff_glaPComponent 3 _ K).mp hKpc) hR haK haRe
  exact Subgroup.subset_closure ⟨nsOrth_le_ainf_nbr hnbr haK, haRe, haReal⟩

theorem nsOrth_ainf_generated
    {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop} (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hBase : NSBaseFrameInputOf T) (hRootGenL : NSRootGenLInputOf T) (hRQ : NSRealNbrInputOf T)
    (hNbrQ4 : NSNbrQFourInputOf T) (hPumpNbr : NSPumpNbrInputOf T)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : NSRegularCfgOf T 3 B Bs x L D J 𝒦) :
    ggAInf 3 B Bs x L D J = nsOrth_reflClosure B Bs x L D J 𝒦 :=
  le_antisymm
    (nsOrth_ainf_le (nsOrth_autL_le_closure hBase hRootGenL hcfg)
      (fun _ _ hnbr => nsOrth_autK_le_closure hRQ hNbrQ4 hPumpNbr hcfg hnbr))
    nsOrth_closure_le_ainf

theorem nsOrth_both_classes
    {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop} (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hBase : NSBaseFrameInputOf T) (hRootGenL : NSRootGenLInputOf T) (hRQ : NSRealNbrInputOf T)
    (hNbrQ4 : NSNbrQFourInputOf T) (hPumpNbr : NSPumpNbrInputOf T)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : NSRegularCfgOf T 3 B Bs x L D J 𝒦)
    (hC : ∀ b : ↥Bs, (∀ φ ∈ ggAInf 3 B Bs x L D J, φ b = b) → b = 1)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V] (Q : QuadraticForm (ZMod 3) V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (ι : Additive ↥Bs ≃+ V)
    (hdim : Module.finrank (ZMod 3) V = 4 ∨ Module.finrank (ZMod 3) V = 5)
    (himage : ∀ g : V ≃ₗ[ZMod 3] V,
      (∃ a ∈ ggAInf 3 B Bs x L D J, ggLin (p := 3) ι a = g) ↔ ∀ v, Q (g v) = Q v) :
    ∃ c : ZMod 3, c ≠ 0 ∧
      ∃ a b : MulAut ↥Bs, a ∈ ggAInf 3 B Bs x L D J ∧ b ∈ ggAInf 3 B Bs x L D J ∧
        GGIsReflection 3 a ∧ GGIsReflection 3 b ∧ GGRealized 3 Bs a ∧ GGRealized 3 Bs b ∧
        OrthReflOfNorm Q c (ggLin (p := 3) ι a) ∧
        OrthReflOfNorm Q (-c) (ggLin (p := 3) ι b) := by
  haveI : FiniteDimensional (ZMod 3) V := Module.Finite.of_finite
  have hd2 : 2 ≤ Module.finrank (ZMod 3) V := by rcases hdim with h | h <;> omega
  obtain ⟨ιL, instL, ML, hML, hWeylL, -, hrank⟩ := hBase G 3 B Bs x L D J 𝒦 hcfg
  letI := instL
  haveI : Nonempty ιL := Fintype.card_pos_iff.mp (by omega)
  let i₀ : ιL := Classical.arbitrary ιL
  obtain ⟨eL, heL⟩ := hWeylL
  let a₀ : MulAut ↥Bs := ((eL (ML.simple i₀) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)
  have ha₀L : a₀ ∈ ggAutomizer L Bs := (eL (ML.simple i₀)).2
  have ha₀re : GGIsReflection 3 a₀ := heL i₀
  have ha₀A : a₀ ∈ ggAInf 3 B Bs x L D J := nsOrth_le_ainf_left ha₀L
  have ha₀Real : GGRealized 3 Bs a₀ :=
    hRootGenL G 3 B Bs x L D J 𝒦 hcfg a₀ ha₀L ha₀re
  obtain ⟨c₀, hc₀, hc₀ON⟩ := nsOrth_refl_class ι hQ himage ha₀A ha₀re
  have hnotall : ¬ (∀ r ∈ ggAInf 3 B Bs x L D J, ∀ _ : GGIsReflection 3 r,
      GGRealized 3 Bs r → OrthReflOfNorm Q c₀ (ggLin (p := 3) ι r)) := by
    intro hall
    have hc₂ : (-c₀) ≠ 0 := neg_ne_zero.mpr hc₀
    have hc₂c₀ : c₀ ≠ -c₀ := by
      intro h
      have h2 : (2 : ZMod 3) * c₀ = 0 := by
        have hsum : c₀ + c₀ = 0 := by
          calc c₀ + c₀ = c₀ + -c₀ := congrArg (fun t => c₀ + t) h
            _ = 0 := add_neg_cancel c₀
        simpa [two_mul] using hsum
      exact hc₀ ((mul_eq_zero.mp h2).resolve_left (by decide))
    obtain ⟨g₂, hg₂ON⟩ := exists_orthReflOfNorm hQ hd2 hc₂
    have hg₂O : g₂ ∈ QuadraticMap.orthogonalGroup Q :=
      (OrthReflOfNorm.mem_orthogonalGroup_and_ne_zero hg₂ON).1
    obtain ⟨r, hrA, hrg⟩ := (himage g₂).mpr ((QuadraticMap.mem_orthogonalGroup_iff).mp hg₂O)
    have hgen : ggAInf 3 B Bs x L D J = nsOrth_reflClosure B Bs x L D J 𝒦 :=
      nsOrth_ainf_generated hL hP hBase hRootGenL hRQ hNbrQ4 hPumpNbr hcfg
    have hrcl : r ∈ nsOrth_reflClosure B Bs x L D J 𝒦 := by
      rw [← hgen]; exact hrA
    have hmem : ggLin (p := 3) ι r ∈
        Subgroup.closure ((ggLin (p := 3) ι) '' nsOrth_reflSet B Bs x L D J 𝒦) := by
      have h1 : (ggLin (p := 3) ι) r ∈
          (Subgroup.closure (nsOrth_reflSet B Bs x L D J 𝒦)).map (ggLin (p := 3) ι) :=
        Subgroup.mem_map.mpr ⟨r, hrcl, rfl⟩
      rwa [MonoidHom.map_closure] at h1
    have hsub : ((ggLin (p := 3) ι) '' nsOrth_reflSet B Bs x L D J 𝒦) ⊆
        {h | OrthReflOfNorm Q c₀ h} := by
      rintro _ ⟨r', hr', rfl⟩
      exact hall r' hr'.1 hr'.2.1 hr'.2.2
    have hcl : g₂ ∈ Subgroup.closure {h | OrthReflOfNorm Q c₀ h} := by
      rw [← hrg]
      exact Subgroup.closure_mono hsub hmem
    exact orthRefl_not_mem_closure hQ hc₀ hc₂ hc₂c₀ hg₂ON hcl
  push Not at hnotall
  obtain ⟨b, hbA, hbRe, hbReal, hbne⟩ := hnotall
  obtain ⟨cb, hcb, hcbON⟩ := nsOrth_refl_class ι hQ himage hbA hbRe
  have hcbne : cb ≠ c₀ := fun h => hbne (h ▸ hcbON)
  have hcbeq : cb = -c₀ :=
    (by decide : ∀ c₀ cb : ZMod 3, c₀ ≠ 0 → cb ≠ 0 → cb ≠ c₀ → cb = -c₀) c₀ cb hc₀ hcb hcbne
  exact ⟨c₀, hc₀, a₀, b, ha₀A, hbA, ha₀re, hbRe, ha₀Real, hbReal, hc₀ON, hcbeq ▸ hcbON⟩

theorem nsOrth_conj_to_fix
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V] [FiniteDimensional (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hxBs : x ∈ Bs)
    (ι : Additive ↥Bs ≃+ V)
    (himage : ∀ g : V ≃ₗ[ZMod 3] V,
      (∃ a ∈ ggAInf 3 B Bs x L D J, ggLin (p := 3) ι a = g) ↔ ∀ v, Q (g v) = Q v)
    (hd2 : 2 ≤ Module.finrank (ZMod 3) V)
    {a : MulAut ↥Bs} (haA : a ∈ ggAInf 3 B Bs x L D J) (haRe : GGIsReflection 3 a)
    (haReal : GGRealized 3 Bs a)
    {c : ZMod 3} (haON : OrthReflOfNorm Q c (ggLin (p := 3) ι a))
    {w : V} (hwperp : QuadraticMap.polar Q w (ι (Additive.ofMul ⟨x, hxBs⟩)) = 0)
    (hwQ : Q w = c) (hc : c ≠ 0) :
    ∃ a' : MulAut ↥Bs, a' ∈ ggAInf 3 B Bs x L D J ∧ GGIsReflection 3 a' ∧
      GGRealized 3 Bs a' ∧ x ∈ ggFixG Bs a' ∧ OrthReflOfNorm Q c (ggLin (p := 3) ι a') := by
  letI : Invertible (Q w) := invertibleOfNonzero (by rw [hwQ]; exact hc)
  let s : V ≃ₗ[ZMod 3] V :=
    (QuadraticMap.reflectionOrthogonal Q w : QuadraticMap.orthogonalGroup Q)
  have hsON : OrthReflOfNorm Q c s := ⟨w, inferInstance, hwQ, rfl⟩
  obtain ⟨e, he, heq⟩ := orthReflOfNorm_conjugate hQ hd2 haON hsON
  obtain ⟨g', hg'A, hg'eq⟩ := (himage e).mpr ((QuadraticMap.mem_orthogonalGroup_iff).mp he)
  have hconj_lin : ggLin (p := 3) ι (g' * a * g'⁻¹) = s := by
    rw [map_mul, map_mul, map_inv, hg'eq]
    exact heq.symm
  have hs_vec : s (ι (Additive.ofMul ⟨x, hxBs⟩)) = ι (Additive.ofMul ⟨x, hxBs⟩) := by
    have hs_eq : s = QuadraticMap.reflection Q w := by
      dsimp only [s]
      exact QuadraticMap.coe_reflectionOrthogonal (Q := Q) (v := w)
    rw [hs_eq, QuadraticMap.reflection_apply_eq_sub_div, hwperp, zero_div, zero_smul, sub_zero]
  have hfix : (g' * a * g'⁻¹) ⟨x, hxBs⟩ = ⟨x, hxBs⟩ :=
    (ggLin_fix_iff (p := 3) ι (g' * a * g'⁻¹) ⟨x, hxBs⟩).mpr
      (by rw [hconj_lin]; exact hs_vec)
  have hg'Ind : g' ∈ ggAutomizer ⊤ Bs := by
    rw [ggAutomizer_eq]
    exact ggRM_ainf_le_induced hg'A
  obtain ⟨g₀, -, hg₀N, hg₀eq⟩ := eq_ggConjAut_of_mem_ggAutomizer hg'Ind
  have hReal : GGRealized 3 Bs (g' * a * g'⁻¹) := by
    rw [hg₀eq]
    exact haReal.conj (by norm_num : Nat.Prime 3) hg₀N
  refine ⟨g' * a * g'⁻¹, ?_, haRe.conj' g', hReal, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg'A haA) (Subgroup.inv_mem _ hg'A)
  · exact Subgroup.mem_map.mpr ⟨⟨x, hxBs⟩, hfix, rfl⟩
  · rw [hconj_lin]; exact hsON

theorem nsOrth_fixed_refl_classes
    {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop} (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hBase : NSBaseFrameInputOf T) (hRootGenL : NSRootGenLInputOf T) (hRQ : NSRealNbrInputOf T)
    (hNbrQ4 : NSNbrQFourInputOf T) (hPumpNbr : NSPumpNbrInputOf T)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : NSRegularCfgOf T 3 B Bs x L D J 𝒦)
    (hC : ∀ b : ↥Bs, (∀ φ ∈ ggAInf 3 B Bs x L D J, φ b = b) → b = 1)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V] (Q : QuadraticForm (ZMod 3) V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (ι : Additive ↥Bs ≃+ V)
    (hdim : Module.finrank (ZMod 3) V = 4 ∨ Module.finrank (ZMod 3) V = 5)
    (himage : ∀ g : V ≃ₗ[ZMod 3] V,
      (∃ a ∈ ggAInf 3 B Bs x L D J, ggLin (p := 3) ι a = g) ↔ ∀ v, Q (g v) = Q v) :
    ∃ c : ZMod 3, c ≠ 0 ∧
      ∃ a b : MulAut ↥Bs, a ∈ ggAInf 3 B Bs x L D J ∧ b ∈ ggAInf 3 B Bs x L D J ∧
        GGIsReflection 3 a ∧ GGIsReflection 3 b ∧ GGRealized 3 Bs a ∧ GGRealized 3 Bs b ∧
        x ∈ ggFixG Bs a ∧ x ∈ ggFixG Bs b ∧
        OrthReflOfNorm Q c (ggLin (p := 3) ι a) ∧
        OrthReflOfNorm Q (-c) (ggLin (p := 3) ι b) := by
  haveI : FiniteDimensional (ZMod 3) V := Module.Finite.of_finite
  have hxBs : x ∈ Bs := hcfg.1.1.1.tableB_facts.2.2.1
  have hd2 : 2 ≤ Module.finrank (ZMod 3) V := by rcases hdim with h | h <;> omega
  obtain ⟨c, hc, a, b, haA, hbA, haRe, hbRe, haReal, hbReal, haON, hbON⟩ :=
    nsOrth_both_classes hL hP hBase hRootGenL hRQ hNbrQ4 hPumpNbr hcfg hC Q hQ ι hdim himage
  obtain ⟨w₁, hw₁p, hw₁Q⟩ :=
    nsOrth_perp_aniso hQ hdim (ι (Additive.ofMul ⟨x, hxBs⟩)) hc
  obtain ⟨w₂, hw₂p, hw₂Q⟩ :=
    nsOrth_perp_aniso hQ hdim (ι (Additive.ofMul ⟨x, hxBs⟩)) (neg_ne_zero.mpr hc)
  obtain ⟨a', ha'A, ha'Re, ha'Real, ha'Fx, ha'ON⟩ :=
    nsOrth_conj_to_fix hQ hxBs ι himage hd2 haA haRe haReal haON hw₁p hw₁Q hc
  obtain ⟨b', hb'A, hb'Re, hb'Real, hb'Fx, hb'ON⟩ :=
    nsOrth_conj_to_fix hQ hxBs ι himage hd2 hbA hbRe hbReal hbON hw₂p hw₂Q
      (neg_ne_zero.mpr hc)
  exact ⟨c, hc, a', b', ha'A, hb'A, ha'Re, hb'Re, ha'Real, hb'Real, ha'Fx, hb'Fx,
    ha'ON, hb'ON⟩

end NSJoin

end CFSG.StandardType

end
