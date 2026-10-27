module

public import CFSG.Quasithin.EmptyFaithful.S143Struct
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabNine
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem iTwo_eq (h : Hyp1281Two G T M (yOfL22 T M)) (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) :
    iTwo T M = yOfL22 T M ⊔ uOfL22 T M := by
  apply le_antisymm
  · refine conjClosure_le fun l hl u hu => ?_
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hl)
      (Subgroup.mem_sup_right hu)) (Subgroup.inv_mem _ (Subgroup.mem_sup_left hl))
  · obtain ⟨g, hg⟩ := h.exists_goodElt_L
    rw [← h.sup_rconj_uOfL22_eq hU hg]
    refine sup_le (le_conjClosure _ _) ?_
    intro y hy
    rw [mem_rconj] at hy
    have h1 := mem_conjClosure (Subgroup.inv_mem _ hg.mem) hy
    have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    rwa [e] at h1

omit [Finite G] in
theorem mem_pCore_iff {X : Subgroup G} (x : ↥X) :
    x ∈ CFSG.Open.pCore 2 ↥X ↔ (x : G) ∈ pCoreOf 2 X := (CFSG.mem_openPCoreOf_iff_open x).symm

theorem i2_cent_of (h : Hyp1281Two G T M (yOfL22 T M)) (hU : ¬ IsMulCommutative ↥(uOfL22 T M))
    {g : G} (hg : GoodElt128 T (yOfL22 T M) g) :
    iTwo T M ⊓ Subgroup.centralizer (VZ T M : Set G) = rOf T M := by
  unfold rOf
  rw [iTwo_eq h hU]
  exact (h.pCoreOf_sup_uOfL22_eq hU hg).symm

theorem perm3_words : ∀ a b : Equiv.Perm (Fin 3), a ^ 2 = 1 → a ≠ 1 → b ^ 3 = 1 → b ≠ 1 →
    ∀ x : Equiv.Perm (Fin 3),
      x = 1 ∨ x = a ∨ x = b ∨ x = b * b ∨ x = a * b ∨ x = a * (b * b) := by decide

theorem perm3_order_three : ∀ a b : Equiv.Perm (Fin 3), a ^ 3 = 1 → a ≠ 1 → b ^ 3 = 1 → b ≠ 1 →
    a = b ∨ a = b⁻¹ := by decide

noncomputable def phiI (h : Hyp1281Two G T M (yOfL22 T M)) :
    ↥(yOfL22 T M ⊔ uOfL22 T M) →* Equiv.Perm (Fin 3) :=
  h.phiS3.comp (Subgroup.inclusion h.sup_uOfL22_le_LT)

theorem phiI_eq_one_iff (h : Hyp1281Two G T M (yOfL22 T M))
    (x : ↥(yOfL22 T M ⊔ uOfL22 T M)) :
    phiI h x = 1 ↔ (x : G) ∈ pCoreOf 2 (yOfL22 T M ⊔ T) :=
  h.phiS3_eq_one_iff (Subgroup.inclusion h.sup_uOfL22_le_LT x)

theorem ker_phiI (h : Hyp1281Two G T M (yOfL22 T M)) (hU : ¬ IsMulCommutative ↥(uOfL22 T M))
    {g : G} (hg : GoodElt128 T (yOfL22 T M) g) :
    MonoidHom.ker (phiI h) = CFSG.Open.pCore 2 ↥(yOfL22 T M ⊔ uOfL22 T M) := by
  ext x
  rw [MonoidHom.mem_ker, phiI_eq_one_iff, mem_pCore_iff, h.pCoreOf_sup_uOfL22_eq hU hg]
  constructor
  · intro hx
    refine ⟨x.2, ?_⟩
    have : (x : G) ∈ (yOfL22 T M ⊔ T) ⊓ Subgroup.centralizer (VZ T M : Set G) := by
      rw [h.centralizer]; exact hx
    exact this.2
  · intro hx
    rw [← h.centralizer]
    exact ⟨h.sup_uOfL22_le_LT hx.1, hx.2⟩

theorem phiI_surjective (h : Hyp1281Two G T M (yOfL22 T M))
    (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G} (hg : GoodElt128 T (yOfL22 T M) g) :
    Function.Surjective (phiI h) := by
  obtain ⟨u, huU, huC⟩ : ∃ u ∈ uOfL22 T M, u ∉ Subgroup.centralizer (VZ T M : Set G) := by
    by_contra hall
    push Not at hall
    exact h.not_le_centralizer_VZ_of_nonabelian hU fun u hu => hall u hu
  have huW : u ∉ Hyp1281Two.wOfU T M := fun hw => huC hw.2
  have hgI : g ∈ yOfL22 T M ⊔ uOfL22 T M := Subgroup.mem_sup_left hg.mem
  have huI : u ∈ yOfL22 T M ⊔ uOfL22 T M := Subgroup.mem_sup_right huU
  set a := phiI h ⟨u, huI⟩ with ha
  set b := phiI h ⟨g, hgI⟩ with hb
  have ha2 : a ^ 2 = 1 := by
    rw [ha, ← map_pow, phiI_eq_one_iff]
    exact h.sq_mem_pCoreOf_LT huU
  have ha1 : a ≠ 1 := fun he => h.not_mem_pCoreOf_LT_of_not_mem_W huU huW
    ((phiI_eq_one_iff h ⟨u, huI⟩).mp he)
  have hb3 : b ^ 3 = 1 := by
    rw [hb, ← map_pow, phiI_eq_one_iff]
    exact h.pow_three_mem_pCoreOf_LT hg.mem
  have hb1 : b ≠ 1 := fun he => h.not_mem_pCoreOf_LT_of_goodElt hg
    ((phiI_eq_one_iff h ⟨g, hgI⟩).mp he)
  intro x
  rcases perm3_words a b ha2 ha1 hb3 hb1 x with hx | hx | hx | hx | hx | hx
  · exact ⟨1, by rw [hx, map_one]⟩
  · exact ⟨⟨u, huI⟩, hx.symm⟩
  · exact ⟨⟨g, hgI⟩, hx.symm⟩
  · exact ⟨⟨g, hgI⟩ * ⟨g, hgI⟩, by rw [map_mul, hx]⟩
  · exact ⟨⟨u, huI⟩ * ⟨g, hgI⟩, by rw [map_mul, hx]⟩
  · exact ⟨⟨u, huI⟩ * (⟨g, hgI⟩ * ⟨g, hgI⟩), by rw [map_mul, map_mul, hx]⟩

theorem i2_sThree_of (h : Hyp1281Two G T M (yOfL22 T M)) (hU : ¬ IsMulCommutative ↥(uOfL22 T M))
    {g : G} (hg : GoodElt128 T (yOfL22 T M) g) :
    Nonempty (OTwoQuot (iTwo T M) ≃* Equiv.Perm (Fin 3)) := by
  rw [iTwo_eq h hU]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (ker_phiI h hU hg)).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (phiI_surjective h hU hg))⟩


section Invariance

variable (h : Hyp1281Two G T M (yOfL22 T M)) (hU : ¬ IsMulCommutative ↥(uOfL22 T M))

include h hU

theorem mem_normalizer_E {g : G} (hg : GoodElt128 T (yOfL22 T M) g) {x : G}
    (hx : x ∈ yOfL22 T M ⊔ uOfL22 T M) :
    x ∈ Subgroup.normalizer
      ((Hyp1281Two.wOfU T M ⊓ rconj (Hyp1281Two.wOfU T M) g : Subgroup G) : Set G) := by
  rw [h.wOfU_inf_rconj_eq hU hg]
  exact h.sup_le_normalizer_inf_rconj hU hg hx

theorem wOfU_inf_rconj_inv {g : G} (hg : GoodElt128 T (yOfL22 T M) g) :
    Hyp1281Two.wOfU T M ⊓ rconj (Hyp1281Two.wOfU T M) g⁻¹ =
      Hyp1281Two.wOfU T M ⊓ rconj (Hyp1281Two.wOfU T M) g := by
  have hgI : g ∈ yOfL22 T M ⊔ uOfL22 T M := hg.mem_sup _
  have hgI' : g⁻¹ ∈ yOfL22 T M ⊔ uOfL22 T M := Subgroup.inv_mem _ hgI
  have hN := mem_normalizer_E h hU hg hgI
  have hN' := mem_normalizer_E h hU hg hgI'
  ext x
  constructor
  · rintro ⟨hxW, hx'⟩
    have hx'' : g⁻¹ * x * g⁻¹⁻¹ ∈ Hyp1281Two.wOfU T M := mem_rconj.mp hx'
    rw [inv_inv] at hx''
    have hy : g⁻¹ * x * g ∈
        Hyp1281Two.wOfU T M ⊓ rconj (Hyp1281Two.wOfU T M) g := by
      refine ⟨hx'', ?_⟩
      refine mem_rconj.mpr ?_
      have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
      rw [e]; exact hxW
    have h1 := (Subgroup.mem_normalizer_iff.mp hN _).mp hy
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [e] at h1
    exact h1
  · intro hx
    refine ⟨hx.1, ?_⟩
    refine mem_rconj.mpr ?_
    have h1 := (Subgroup.mem_normalizer_iff.mp hN' _).mp hx
    exact h1.1

theorem wOfU_inf_rconj_indep {g g' : G} (hg : GoodElt128 T (yOfL22 T M) g)
    (hg' : GoodElt128 T (yOfL22 T M) g') :
    Hyp1281Two.wOfU T M ⊓ rconj (Hyp1281Two.wOfU T M) g' =
      Hyp1281Two.wOfU T M ⊓ rconj (Hyp1281Two.wOfU T M) g := by
  have hgP : g ∈ yOfL22 T M ⊔ T := Subgroup.mem_sup_left hg.mem
  have hgP' : g' ∈ yOfL22 T M ⊔ T := Subgroup.mem_sup_left hg'.mem
  have ha3 : h.phiS3 ⟨g, hgP⟩ ^ 3 = 1 := by
    rw [← map_pow, h.phiS3_eq_one_iff]
    exact h.pow_three_mem_pCoreOf_LT hg.mem
  have ha1 : h.phiS3 ⟨g, hgP⟩ ≠ 1 := fun he =>
    h.not_mem_pCoreOf_LT_of_goodElt hg ((h.phiS3_eq_one_iff _).mp he)
  have hb3 : h.phiS3 ⟨g', hgP'⟩ ^ 3 = 1 := by
    rw [← map_pow, h.phiS3_eq_one_iff]
    exact h.pow_three_mem_pCoreOf_LT hg'.mem
  have hb1 : h.phiS3 ⟨g', hgP'⟩ ≠ 1 := fun he =>
    h.not_mem_pCoreOf_LT_of_goodElt hg' ((h.phiS3_eq_one_iff _).mp he)
  have hTW : T ≤ Subgroup.normalizer (Hyp1281Two.wOfU T M : Set G) := h.T_le_normalizer_wOfU
  have hO : pCoreOf 2 (yOfL22 T M ⊔ T) ≤ T := pCoreOf_two_le_of_isSylowTwoOf (sylow_LT_of_hyp h)
  rcases perm3_order_three _ _ hb3 hb1 ha3 ha1 with hba | hba
  · have hc : g' * g⁻¹ ∈ pCoreOf 2 (yOfL22 T M ⊔ T) := by
      have h1 : h.phiS3 (⟨g', hgP'⟩ * ⟨g, hgP⟩⁻¹) = 1 := by
        rw [map_mul, map_inv, hba]; simp
      exact (h.phiS3_eq_one_iff _).mp h1
    have e : g' = (g' * g⁻¹) * g := by group
    rw [e, rconj_mul_eq_of_mem_normalizer (hTW (hO hc))]
  · have hc : g' * g ∈ pCoreOf 2 (yOfL22 T M ⊔ T) := by
      have h1 : h.phiS3 (⟨g', hgP'⟩ * ⟨g, hgP⟩) = 1 := by
        rw [map_mul, hba]; simp
      exact (h.phiS3_eq_one_iff _).mp h1
    have e : g' = (g' * g) * g⁻¹ := by group
    rw [e, rconj_mul_eq_of_mem_normalizer (hTW (hO hc))]
    exact wOfU_inf_rconj_inv h hU hg

theorem T_le_normalizer_E {g : G} (hg : GoodElt128 T (yOfL22 T M) g) :
    T ≤ Subgroup.normalizer
      ((Hyp1281Two.wOfU T M ⊓ rconj (Hyp1281Two.wOfU T M) g : Subgroup G) : Set G) := by
  refine le_normalizer_of_conj_mem fun t ht e he => ?_
  have hTW : T ≤ Subgroup.normalizer (Hyp1281Two.wOfU T M : Set G) := h.T_le_normalizer_wOfU
  have hTN : t ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := by
    rw [h.normalizer_Z_eq_centralizer]
    exact h.almostSpecialHyp_g1.T_le_H ht
  have hg' : GoodElt128 T (yOfL22 T M) (t⁻¹ * g * t) := by
    refine ⟨?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (h.normal (h.inM.2 (T.inv_mem ht))) g).mp hg.mem
      simpa using this
    · intro hmem
      apply hg.not_mem
      have := Subgroup.mul_mem _ (Subgroup.mul_mem _ hTN hmem) (Subgroup.inv_mem _ hTN)
      simpa [mul_assoc] using this
  have he' : e ∈ Hyp1281Two.wOfU T M ⊓ rconj (Hyp1281Two.wOfU T M) (t⁻¹ * g * t) := by
    rw [wOfU_inf_rconj_indep h hU hg hg']; exact he
  refine ⟨(Subgroup.mem_normalizer_iff.mp (hTW ht) e).mp he.1, ?_⟩
  refine mem_rconj.mpr ?_
  have h2 := (Subgroup.mem_normalizer_iff.mp (hTW ht) _).mp (mem_rconj.mp he'.2)
  have e2 : t * ((t⁻¹ * g * t) * e * (t⁻¹ * g * t)⁻¹) * t⁻¹ = g * (t * e * t⁻¹) * g⁻¹ := by group
  rw [← e2]
  exact h2

end Invariance

end S143

end CFSG.Quasithin
