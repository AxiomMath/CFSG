module

public import CFSG.Quasithin.EmptyFaithful.S153GCount
public import CFSG.Quasithin.EmptyFaithful.S153GIneq
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

section CountIneqTools

variable {G : Type} [Group G]

private theorem gci_comm_of_mem {E : Subgroup G} (hE : IsElemAbelian 2 E) {x y : G}
    (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x := CFSG.Open.IsElemAbelian.comm hE hx hy

private theorem gci_isElemAbelian_of_le {E X : Subgroup G} (hE : IsElemAbelian 2 E)
    (hXE : X ≤ E) : IsElemAbelian 2 X := CFSG.Open.IsElemAbelian.mono hE hXE

private theorem gci_mem_conjBy153 {t x : G} {X : Subgroup G} :
    x ∈ conjBy153 t X ↔ t⁻¹ * x * t ∈ X := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    exact ⟨t⁻¹ * x * t, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

private theorem gci_isElemAbelian_conjBy153 {E : Subgroup G} (hE : IsElemAbelian 2 E) (t : G) :
    IsElemAbelian 2 (conjBy153 t E) := by
  have hcomm : ∀ x ∈ conjBy153 t E, ∀ y ∈ conjBy153 t E, x * y = y * x := by
    intro x hx y hy
    rw [gci_mem_conjBy153] at hx hy
    have h := gci_comm_of_mem hE hx hy
    calc x * y = t * ((t⁻¹ * x * t) * (t⁻¹ * y * t)) * t⁻¹ := by group
      _ = t * ((t⁻¹ * y * t) * (t⁻¹ * x * t)) * t⁻¹ := by rw [h]
      _ = y * x := by group
  refine ⟨⟨⟨fun x y => Subtype.ext (hcomm x x.2 y y.2)⟩⟩, fun x hx => ?_⟩
  rw [gci_mem_conjBy153] at hx
  have h2 := hE.2 _ hx
  have e : x = t * (t⁻¹ * x * t) * t⁻¹ := by group
  calc x ^ 2 = (t * (t⁻¹ * x * t) * t⁻¹) ^ 2 := by rw [← e]
    _ = t * (t⁻¹ * x * t) ^ 2 * t⁻¹ := conj_pow
    _ = 1 := by rw [h2]; group

private theorem gci_conjBy153_le {S X : Subgroup G} {t : G}
    (ht : t ∈ Subgroup.normalizer (S : Set G)) (hX : X ≤ S) : conjBy153 t X ≤ S := by
  intro x hx
  rw [gci_mem_conjBy153] at hx
  exact (Subgroup.mem_normalizer_iff''.mp ht x).mpr (hX hx)

private theorem gci_le_normalizer_conjBy153 {S X : Subgroup G} {t : G}
    (ht : t ∈ Subgroup.normalizer (S : Set G)) (hX : S ≤ Subgroup.normalizer (X : Set G)) :
    S ≤ Subgroup.normalizer (conjBy153 t X : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hg' : t⁻¹ * g * t ∈ S := (Subgroup.mem_normalizer_iff''.mp ht g).mp hg
  have key := Subgroup.mem_normalizer_iff.mp (hX hg') (t⁻¹ * h * t)
  rw [gci_mem_conjBy153, gci_mem_conjBy153]
  have e : t⁻¹ * (g * h * g⁻¹) * t = (t⁻¹ * g * t) * (t⁻¹ * h * t) * (t⁻¹ * g * t)⁻¹ := by group
  rw [e]
  exact key

private theorem gci_mem_normalizer_commutator {A B : Subgroup G} {s : G}
    (hA : s ∈ Subgroup.normalizer (A : Set G)) (hB : s ∈ Subgroup.normalizer (B : Set G)) :
    s ∈ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_commutator, hA, hB]

end CountIneqTools

section Derivation

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

private theorem gci_omegaOneCenter_le (h : Hyp15310 G T Mc M V₁ V₂ Yp t) :
    quasithinOmegaOneCenter T ≤ quasithinOmegaOneCenter (Sgp153 T V₁) := by
  unfold quasithinOmegaOneCenter
  refine Subgroup.closure_mono fun z hz => ?_
  have hzV : z ∈ VZ T M := le_conjClosure _ _ (Subgroup.subset_closure hz)
  exact ⟨⟨S153D.VZ_le_Sgp153 h hzV, Subgroup.centralizer_le (fun x hx => hx.1) hz.1.2⟩, hz.2⟩

private theorem gci_abstract_inputs (c : Ctx15332 T Mc M V₁ V₂ Yp I L t)
    (cc : Concl15332 T M V₁ I L) {t' : G} (ht'T : t' ∈ T) (ht'S : t' ∉ Sgp153 T V₁) :
    IsElemAbelian 2 (UL153 T I L) ∧ IsElemAbelian 2 (conjBy153 t' (UL153 T I L)) ∧
      UL153 T I L ≤ Sgp153 T V₁ ∧ conjBy153 t' (UL153 T I L) ≤ Sgp153 T V₁ ∧
      (∀ u ∈ UL153 T I L, ∀ v ∈ conjBy153 t' (UL153 T I L), u * v = v * u) ∧
      UL153 T I L ⊓ conjBy153 t' (UL153 T I L) = ⊥ ∧
      Sgp153 T V₁ ≤ Subgroup.normalizer (UL153 T I L : Set G) ∧
      Sgp153 T V₁ ≤ Subgroup.normalizer (conjBy153 t' (UL153 T I L) : Set G) ∧
      Sgp153 T V₁ ⊓ Subgroup.centralizer
        ((UL153 T I L ⊔ conjBy153 t' (UL153 T I L) : Subgroup G) : Set G) ≤ P153 T M V₁ := by
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t :=
    c.toCtx15331.toCtx15330.toCtx15328.toCtx15327.toCtx15325L
  have hyp : Hyp15310 G T Mc M V₁ V₂ Yp t := c25.ctx.hyp
  have hF : Facts153 T M V₁ Yp I := c25.facts.toFacts153
  have hsyl : IsSylowTwoOf (Sgp153 T V₁) I := hF.sylow
  have hSI : Sgp153 T V₁ ≤ I := hsyl.1
  have hLI : L ≤ I := (le_of_mem_cComp c25.conc.1).trans (thompsonJ_le_self I)
  have hIL : I ≤ Subgroup.normalizer (L : Set G) := c.c27.normal
  have hIU : I ≤ Subgroup.normalizer (UI153 T I : Set G) := le_normalizer_conjClosure _ I
  have hUI : IsElemAbelian 2 (UI153 T I) ∧ UI153 T I ≤ pCoreOf 2 I := by
    obtain ⟨hle, hel⟩ := conjClosure_le_centerOf_pCoreOf_of_sylowIn hsyl.1 hsyl.2.1 hsyl.2.2
      c25.ctx.charTwo (gci_omegaOneCenter_le hyp)
    exact ⟨hel, hle.trans inf_le_left⟩
  have hUUI : UL153 T I L ≤ UI153 T I :=
    (Subgroup.le_normalizer_iff_commutator_le_left (H := L) (K := UI153 T I)).mp (hLI.trans hIU)
  have hUel : IsElemAbelian 2 (UL153 T I L) := gci_isElemAbelian_of_le hUI.1 hUUI
  have hVel : IsElemAbelian 2 (conjBy153 t' (UL153 T I L)) :=
    gci_isElemAbelian_conjBy153 hUel t'
  have hUS : UL153 T I L ≤ Sgp153 T V₁ :=
    hUUI.trans (hUI.2.trans (S153D.pCoreOf_le_Sgp153' hF))
  have ht'N : t' ∈ Subgroup.normalizer (Sgp153 T V₁ : Set G) :=
    Hyp153.T_le_normalizer_Sgp153 hyp.hyp hyp.decomp ht'T
  have hVS : conjBy153 t' (UL153 T I L) ≤ Sgp153 T V₁ := gci_conjBy153_le ht'N hUS
  have hSU : Sgp153 T V₁ ≤ Subgroup.normalizer (UL153 T I L : Set G) := fun s hs =>
    gci_mem_normalizer_commutator (hIU (hSI hs)) (hIL (hSI hs))
  have hSV : Sgp153 T V₁ ≤ Subgroup.normalizer (conjBy153 t' (UL153 T I L) : Set G) :=
    gci_le_normalizer_conjBy153 ht'N hSU
  obtain ⟨hcomm, hUVb, -⟩ := cc.W_direct t' ht'T ht'S
  have hUV : ∀ u ∈ UL153 T I L, ∀ v ∈ conjBy153 t' (UL153 T I L), u * v = v * u := by
    intro u hu v hv
    have h := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hu
    exact (Subgroup.mem_centralizer_iff.mp h v hv).symm
  have hP : Sgp153 T V₁ ⊓ Subgroup.centralizer
      ((UL153 T I L ⊔ conjBy153 t' (UL153 T I L) : Subgroup G) : Set G) ≤ P153 T M V₁ := by
    have hPeq : P153 T M V₁ = (Sgp153 T V₁ ⊓ Subgroup.centralizer (UL153 T I L : Set G)) ⊔
        (Sgp153 T V₁ ⊓ Subgroup.centralizer (conjBy153 t' (UL153 T I L) : Set G)) :=
      (cc.P_split t' ht'T ht'S).1
    rw [hPeq]
    have hUW : UL153 T I L ≤ UL153 T I L ⊔ conjBy153 t' (UL153 T I L) := le_sup_left
    exact le_trans (inf_le_inf_left _ (Subgroup.centralizer_le hUW)) le_sup_left
  exact ⟨hUel, hVel, hUS, hVS, hUV, hUVb, hSU, hSV, hP⟩

private theorem gci_rk_mono (P U V A : Subgroup G) :
    rk ↥(A ⊓ P) ≤ rk ↥A ∧
      rk ↥(A ⊓ P ⊓ Subgroup.centralizer (U : Set G)) ≤ rk ↥(A ⊓ P) ∧
      rk ↥(A ⊓ P ⊓ Subgroup.centralizer (V : Set G)) ≤ rk ↥(A ⊓ P) ∧
      rk ↥(U ⊓ Subgroup.centralizer (A : Set G)) ≤ rk ↥U ∧
      rk ↥(V ⊓ Subgroup.centralizer (A : Set G)) ≤ rk ↥V :=
  ⟨rk_mono inf_le_left, rk_mono inf_le_left, rk_mono inf_le_left, rk_mono inf_le_left,
    rk_mono inf_le_left⟩

private theorem gci_cm_le_of_rk (P U V A : Subgroup G)
    (h : rk ↥U + rk ↥V + rk ↥(A ⊓ P ⊓ Subgroup.centralizer (U : Set G)) +
        rk ↥(A ⊓ P ⊓ Subgroup.centralizer (V : Set G)) ≤
      rk ↥A + rk ↥(A ⊓ P) + rk ↥(U ⊓ Subgroup.centralizer (A : Set G)) +
        rk ↥(V ⊓ Subgroup.centralizer (A : Set G))) :
    cm3 U A + cm3 V A ≤ cm0 P A + cm1 P U A + cm1 P V A := by
  obtain ⟨m1, m2, m3, m4, m5⟩ := gci_rk_mono P U V A
  simp only [cm0, cm1, cm3]
  omega

private theorem gci_rk_eq_of_cm (P U V A : Subgroup G)
    (h : cm3 U A + cm3 V A = cm0 P A + cm1 P U A + cm1 P V A) :
    rk ↥U + rk ↥V + rk ↥(A ⊓ P ⊓ Subgroup.centralizer (U : Set G)) +
        rk ↥(A ⊓ P ⊓ Subgroup.centralizer (V : Set G)) =
      rk ↥A + rk ↥(A ⊓ P) + rk ↥(U ⊓ Subgroup.centralizer (A : Set G)) +
        rk ↥(V ⊓ Subgroup.centralizer (A : Set G)) := by
  obtain ⟨m1, m2, m3, m4, m5⟩ := gci_rk_mono P U V A
  simp only [cm0, cm1, cm3] at h
  omega

theorem count_bw_of_equality {t' : G} {A : Subgroup G}
    (c : Ctx15332 T Mc M V₁ V₂ Yp I L t) (cc : Concl15332 T M V₁ I L) (ht'T : t' ∈ T)
    (ht'S : t' ∉ Sgp153 T V₁) (hA : IsMaxElemAbelian (Sgp153 T V₁) A)
    (hEq : cm3 (UL153 T I L) A + cm3 (conjBy153 t' (UL153 T I L)) A =
      cm0 (P153 T M V₁) A + cm1 (P153 T M V₁) (UL153 T I L) A +
        cm1 (P153 T M V₁) (conjBy153 t' (UL153 T I L)) A) :
    IsMaxElemAbelian (Sgp153 T V₁)
      ((A ⊓ Subgroup.centralizer
          ((UL153 T I L ⊔ conjBy153 t' (UL153 T I L) : Subgroup G) : Set G)) ⊔
        (UL153 T I L ⊔ conjBy153 t' (UL153 T I L))) := by
  obtain ⟨hUel, hVel, hUS, hVS, hUV, hUVb, hSU, hSV, hP⟩ := gci_abstract_inputs c cc ht'T ht'S
  exact count_eq_abstract hA hUel hVel hUS hVS hUV hUVb hSU hSV hP (gci_rk_eq_of_cm _ _ _ _ hEq)

end Derivation

theorem countIneq_of_abstract : CountIneq := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c cc t' ht'T ht'S A hA
  obtain ⟨hUel, hVel, hUS, hVS, hUV, hUVb, hSU, hSV, hP⟩ := gci_abstract_inputs c cc ht'T ht'S
  exact gci_cm_le_of_rk _ _ _ _
    (count_ineq_abstract hA hUel hVel hUS hVS hUV hUVb hSU hSV hP)

end CFSG.Quasithin
