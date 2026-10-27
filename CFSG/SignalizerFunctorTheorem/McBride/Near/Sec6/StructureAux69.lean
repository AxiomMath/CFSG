module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.StructureAux68
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.StructureAux

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

open Thm210

namespace Sec6S31

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

omit [Finite G] in
theorem fitting_le_gamma (S H : Subgroup G) :
    CFSG.fittingSubgroupOf (S ⊓ kOf H) ≤ (H ⊓ S) ⊔ A :=
  (Subgroup.map_subtype_le _).trans
    ((le_inf (inf_le_right.trans (kOf_le _)) inf_le_left).trans le_sup_left)

omit [Finite G] in
theorem commutator_split {j l v : G} (h : Commute v l) :
    v * (j * l) * v⁻¹ * (j * l)⁻¹ = v * j * v⁻¹ * j⁻¹ := by
  have h' : l * v⁻¹ = v⁻¹ * l := h.inv_left.symm.eq
  calc v * (j * l) * v⁻¹ * (j * l)⁻¹ = v * j * (l * v⁻¹) * l⁻¹ * j⁻¹ := by group
    _ = v * j * (v⁻¹ * l) * l⁻¹ * j⁻¹ := by rw [h']
    _ = v * j * v⁻¹ * j⁻¹ := by group

section Setting

variable (h : Counterexample p A θ) {B : Subgroup G} (hB : B ∈ rSet p A θ)

include h hB

theorem fProd_eq :
    fProd A (kOf (thetaOf θ B)) =
      CFSG.fittingSubgroupOf (ssol p A θ ⊓ kOf (thetaOf θ B)) := by
  have hK := (hyp h hB).semisimpleAction
  rw [← hK.fittingSubgroupOf_kProd, ← hK.mOf_eq_kProd, mOf_eq h hB]

theorem dsub_sup_le_gamma :
    dsub A θ ⊔ A ≤ (thetaOf θ B ⊓ ssol p A θ) ⊔ A :=
  sup_le ((le_inf (mem_mtil h hB).2 h.dsub_le_ssol).trans le_sup_left) le_sup_right

theorem admits_fitting :
    Admits ((thetaOf θ B ⊓ ssol p A θ) ⊔ A)
      (CFSG.fittingSubgroupOf (ssol p A θ ⊓ kOf (thetaOf θ B))) := by
  have H := hyp h hB
  have hS : A ≤ Subgroup.normalizer (ssol p A θ : Set G) := h.ssol_mem_assoc.1
  refine sup_le (fun g hg => ?_) (fun a ha => ?_)
  · exact Lemma216.mem_normalizer_fittingSubgroupOf (Lemma216.mem_normalizer_inf
      (Subgroup.le_normalizer hg.2) (Nonsolv.le_normalizer_kOf _ hg.1))
  · exact Lemma216.mem_normalizer_fittingSubgroupOf
      (Lemma216.mem_normalizer_inf (hS ha) (H.A_le_normalizer ha))

end Setting

section Main

variable (h : Counterexample p A θ) {B : Subgroup G} (hB : B ∈ rSet p A θ)
  {J : Subgroup G} (hJ : J ∈ lcal (thetaOf θ B))
  (hJ3 : Nonempty (↥J ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 p)))

include h hB hJ hJ3

omit hJ3 in
theorem fitting_ne_bot :
    CFSG.fittingSubgroupOf (ssol p A θ ⊓ kOf (thetaOf θ B)) ≠ ⊥ := by
  have H := hyp h hB
  have hK := H.semisimpleAction
  have hJ' : J ∈ lcal (kOf (thetaOf θ B)) := H.lcal_kOf ▸ hJ
  intro hbot
  refine hK.fittingSubgroupOf_kJ_ne_bot hJ' (le_bot_iff.mp ?_)
  rw [← hbot, ← fProd_eq h hB]
  exact le_sSup ⟨J, hJ', rfl⟩

theorem fitting_minimal
    {N : Subgroup G}
    (hNF : N ≤ CFSG.fittingSubgroupOf (ssol p A θ ⊓ kOf (thetaOf θ B)))
    (hNΓ : (thetaOf θ B ⊓ ssol p A θ) ⊔ A ≤ Subgroup.normalizer (N : Set G))
    (hN1 : N ≠ ⊥) :
    N = CFSG.fittingSubgroupOf (ssol p A θ ⊓ kOf (thetaOf θ B)) := by
  have H := hyp h hB
  have hK := H.semisimpleAction
  have hG := hK.semisimple
  have hfp := fProd_eq h hB
  have hJ' : J ∈ lcal (kOf (thetaOf θ B)) := H.lcal_kOf ▸ hJ
  have hkP : kProd A (kOf (thetaOf θ B)) = ssol p A θ ⊓ kOf (thetaOf θ B) :=
    hK.mOf_eq_kProd.symm.trans (mOf_eq h hB)
  refine le_antisymm hNF ?_
  obtain ⟨⟨n, hn⟩, hn1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hN1
  have hn1' : n ≠ 1 := fun e => hn1 (Subtype.ext e)
  have hnF : n ∈ fProd A (kOf (thetaOf θ B)) := hfp ▸ hNF hn
  have hnK : n ∈ kOf (thetaOf θ B) := fProd_le A _ hnF
  obtain ⟨J₀, hJ₀, hnJ₀⟩ := exists_crd_ne_one hG hnK hn1'
  have hJ₀3 : Nonempty (↥J₀ ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 p)) := by
    obtain ⟨e⟩ := nonempty_mulEquiv h hB hJ₀ hJ'
    obtain ⟨e'⟩ := hJ3
    exact ⟨e.trans e'⟩
  have hKJ : kJ A J₀ = cenIn J₀ (norIn A J₀) := kJ_eq_cenIn_of_psl3 hK hJ₀ hJ₀3
  obtain ⟨v, hvC, hvy⟩ := exists_fpf_kJ hK hJ₀
  have hvJ : v ∈ J₀ := (mem_cenIn_iff.mp hvC).1
  have hkJM : kJ A J₀ ≤ ssol p A θ ⊓ kOf (thetaOf θ B) :=
    hkP ▸ le_sSup ⟨J₀, hJ₀, rfl⟩
  have hMΓ : ssol p A θ ⊓ kOf (thetaOf θ B) ≤ (thetaOf θ B ⊓ ssol p A θ) ⊔ A :=
    (le_inf (inf_le_right.trans (kOf_le _)) inf_le_left).trans le_sup_left
  have hCΓ : ∀ c ∈ cenIn J₀ (norIn A J₀), c ∈ (thetaOf θ B ⊓ ssol p A θ) ⊔ A := fun c hc =>
    hMΓ (hkJM (hKJ ▸ hc))
  set j := crd (kOf (thetaOf θ B)) J₀ n with hj
  have hjJ : j ∈ J₀ := crd_mem hG hJ₀ hnK
  have hjy : j ∈ CFSG.fittingSubgroupOf (kJ A J₀) := by
    obtain ⟨hnG', hc⟩ := hK.mem_fProd_iff.mp hnF
    rw [hj, crd_eq hG hJ₀ hnK]
    exact hc J₀ hJ₀
  have hj1 : j ≠ 1 := hnJ₀
  have hjK : j ∈ kOf (thetaOf θ B) := hK.isDirectProduct_lcal.le hJ₀ hjJ
  have hl : j⁻¹ * n ∈ sSup (lcal (kOf (thetaOf θ B)) \ {J₀}) := by
    rw [← crd_eq_one_iff hG hJ₀ (mul_mem (inv_mem hjK) hnK), crd_mul hG hJ₀ (inv_mem hjK) hnK,
      crd_inv hG hJ₀ hjK, crd_of_mem hG hJ₀ hjJ, ← hj, inv_mul_cancel]
  have hn_eq : n = j * (j⁻¹ * n) := by group
  have hcomm : Commute v (j⁻¹ * n) :=
    (hK.isDirectProduct_lcal.commute_sSup_diff hJ₀ v hvJ _ hl)
  have hcN : v * j * v⁻¹ * j⁻¹ ∈ N := by
    have hvΓ : v ∈ (thetaOf θ B ⊓ ssol p A θ) ⊔ A := hCΓ v hvC
    have h1 : v * n * v⁻¹ * n⁻¹ ∈ N :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp (hNΓ hvΓ) n).mp hn) (inv_mem hn)
    rw [hn_eq, commutator_split hcomm] at h1
    exact h1
  have hcJ : v * j * v⁻¹ * j⁻¹ ∈ J₀ :=
    mul_mem (mul_mem (mul_mem hvJ hjJ) (inv_mem hvJ)) (inv_mem hjJ)
  have hc1 : v * j * v⁻¹ * j⁻¹ ≠ 1 := fun e => hvy j hjy hj1 (mul_inv_eq_one.mp e)
  have hN₀ne : N ⊓ J₀ ≠ ⊥ := fun e =>
    hc1 (Subgroup.mem_bot.mp (e ▸ Subgroup.mem_inf.mpr ⟨hcN, hcJ⟩))
  have hN₀C : N ⊓ J₀ ≤ cenIn J₀ (norIn A J₀) := by
    intro x hx
    rw [← hKJ]
    have : x ∈ fProd A (kOf (thetaOf θ B)) ⊓ J₀ := Subgroup.mem_inf.mpr ⟨hfp ▸ hNF hx.1, hx.2⟩
    rw [hK.fProd_inf hJ₀] at this
    exact Subgroup.map_subtype_le _ this
  have hN₀n : ((N ⊓ J₀).subgroupOf (cenIn J₀ (norIn A J₀))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hN₀C]
    intro x c hx hc
    refine Subgroup.mem_inf.mpr ⟨?_, mul_mem (mul_mem (mem_cenIn_iff.mp hc).1 hx.2)
      (inv_mem (mem_cenIn_iff.mp hc).1)⟩
    exact (Subgroup.mem_normalizer_iff.mp (hNΓ (hCΓ c hc)) x).mp hx.1
  have hF₀ := hK.fittingSubgroupOf_cenIn_le_of_normal hJ₀ hN₀C hN₀n hN₀ne
  have hF₀N : CFSG.fittingSubgroupOf (kJ A J₀) ≤ N := by
    rw [hKJ]
    exact hF₀.trans inf_le_left
  rw [← hfp]
  refine sSup_le ?_
  rintro _ ⟨J₁, hJ₁, rfl⟩
  obtain ⟨g, hg, rfl⟩ := exists_conj h hB hJ₀ hJ₁
  have hgΓ : g ∈ (thetaOf θ B ⊓ ssol p A θ) ⊔ A := dsub_sup_le_gamma h hB hg
  intro x hx
  have hx' : x ∈ fProd A (kOf (thetaOf θ B)) ⊓ J₀.map (MulAut.conj g).toMonoidHom := by
    rw [hK.fProd_inf hJ₁]
    exact hx
  obtain ⟨hxf, y, hyJ, hyx⟩ := hx'
  have hy : g⁻¹ * x * g ∈ J₀ := by
    have : g⁻¹ * x * g = y := by
      rw [← hyx]
      simp [mul_assoc]
    rw [this]
    exact hyJ
  have hyf : g⁻¹ * x * g ∈ fProd A (kOf (thetaOf θ B)) := by
    rw [hfp]
    have hxF : x ∈ CFSG.fittingSubgroupOf (ssol p A θ ⊓ kOf (thetaOf θ B)) := hfp ▸ hxf
    have := (Subgroup.mem_normalizer_iff.mp (admits_fitting h hB (inv_mem hgΓ)) x).mp hxF
    simpa using this
  have hyF : g⁻¹ * x * g ∈ CFSG.fittingSubgroupOf (kJ A J₀) := by
    have : g⁻¹ * x * g ∈ fProd A (kOf (thetaOf θ B)) ⊓ J₀ := ⟨hyf, hy⟩
    rwa [hK.fProd_inf hJ₀] at this
  have := (Subgroup.mem_normalizer_iff.mp (hNΓ hgΓ) (g⁻¹ * x * g)).mp (hF₀N hyF)
  simpa [mul_assoc] using this

theorem eq_fitting_of_minimal
    {N : Subgroup G} (hNK : N ≤ kOf (thetaOf θ B))
    (hN : IsNormalIn N ((thetaOf θ B ⊓ ssol p A θ) ⊔ A)) (hN1 : N ≠ ⊥)
    (hmin : ∀ N' : Subgroup G, IsNormalIn N' ((thetaOf θ B ⊓ ssol p A θ) ⊔ A) → N' ≤ N →
      N' = ⊥ ∨ N' = N) :
    N = CFSG.fittingSubgroupOf (ssol p A θ ⊓ kOf (thetaOf θ B)) := by
  have H := hyp h hB
  have hK := H.semisimpleAction
  have hFN : IsNormalIn (CFSG.fittingSubgroupOf (ssol p A θ ⊓ kOf (thetaOf θ B)))
      ((thetaOf θ B ⊓ ssol p A θ) ⊔ A) := ⟨fitting_le_gamma _ _, admits_fitting h hB⟩
  have hinf : IsNormalIn (N ⊓ CFSG.fittingSubgroupOf (ssol p A θ ⊓ kOf (thetaOf θ B)))
      ((thetaOf θ B ⊓ ssol p A θ) ⊔ A) :=
    ⟨inf_le_left.trans hN.1, fun g hg => Lemma216.mem_normalizer_inf (hN.2 hg) (hFN.2 hg)⟩
  have hdK : dOne p A θ ≤ kOf (thetaOf θ B) :=
    (Subgroup.map_subtype_le _).trans ((dZero_eq h hB).le.trans inf_le_right)
  have hadm : Admits (cenIn (kOf (thetaOf θ B)) A ⊔ A) (dOne p A θ) := by
    intro g hg
    have h1 := Lemma216.admits_cenIn_kOf (thetaOf θ B) A
      (sup_le_sup_right (inf_le_inf_right _ (kOf_le _)) A hg)
    rw [cenIn_kOf_eq h hB] at h1
    exact Lemma216.mem_normalizer_fittingSubgroupOf h1
  have hdFM : dOne p A θ ≤ CFSG.fittingSubgroupOf (ssol p A θ ⊓ kOf (thetaOf θ B)) := by
    have := thm210f hK (X := dOne p A θ) hdK hadm (isNilpotent_fittingSubgroupOf _)
    rwa [mOf_eq h hB] at this
  rcases hmin _ hinf inf_le_left with h0 | h0
  · exfalso
    have hcen : ∀ n ∈ N, ∀ m ∈ CFSG.fittingSubgroupOf (ssol p A θ ⊓ kOf (thetaOf θ B)),
        n * m = m * n := by
      intro n hn m hm
      have h1 : n * m * n⁻¹ * m⁻¹ ∈
          N ⊓ CFSG.fittingSubgroupOf (ssol p A θ ⊓ kOf (thetaOf θ B)) := by
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · have h2 := (Subgroup.mem_normalizer_iff.mp (hN.2 (hFN.1 hm)) n⁻¹).mp (inv_mem hn)
          have h3 := mul_mem hn h2
          simpa [mul_assoc] using h3
        · have h2 := (Subgroup.mem_normalizer_iff.mp (hFN.2 (hN.1 hn)) m).mp hm
          exact mul_mem (by simpa using h2) (inv_mem hm)
      rw [h0, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
      exact h1
    have hNFM : N ≤ CFSG.fittingSubgroupOf (ssol p A θ ⊓ kOf (thetaOf θ B)) := by
      intro n hn
      rw [(fitting_eq_cenIn_kOf h hB).1]
      exact ⟨hNK hn, Subgroup.mem_centralizer_iff.mpr fun d hd =>
        (hcen n hn d (hdFM hd)).symm⟩
    exact hN1 (by rw [← inf_eq_left.mpr hNFM, h0])
  · exact fitting_minimal h hB hJ hJ3 (inf_eq_left.mp h0) hN.2 hN1

end Main

end Sec6S31

end CFSG.SignalizerFunctorTheorem.McBride.Near
