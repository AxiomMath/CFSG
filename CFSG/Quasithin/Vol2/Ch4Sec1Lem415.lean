module

public import CFSG.Quasithin.Vol2.Ch4Sec1Lem414
public import CFSG.Quasithin.Background.G2

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4

variable {G : Type} [Group G] [Finite G] {T M Mp Mm : Subgroup G}

omit [Finite G] in
theorem commute_of_le_omegaOneCenterOf {Rp V : Subgroup G} (hVle : V ≤ omegaOneCenterOf Rp)
    {v y : G} (hv : v ∈ V) (hy : y ∈ Rp) : y * v = v * y :=
  mem_centralizer_of_mem_omegaOneCenterOf (hVle hv) hy

omit [Finite G] in
theorem le_centralizer_of_le_omegaOneCenterOf {Rp V X : Subgroup G}
    (hVle : V ≤ omegaOneCenterOf Rp) (hX : X ≤ Rp) :
    V ≤ Subgroup.centralizer (X : Set G) := fun _ hv =>
  Subgroup.mem_centralizer_iff.mpr fun _ hy => commute_of_le_omegaOneCenterOf hVle hv (hX hy)

theorem lemma_4_1_5_one (h : Hyp4_1_1 G T M Mp) (hS : IsSigma M Mp Mm) {Rp V I : Subgroup G}
    (hRp : IsSylowTwoOf Rp (centralizerSection M Mp (pCoreOf 2 Mp)))
    (hVle : V ≤ omegaOneCenterOf Rp) (hI : IsGammaStar M Mp Mm I)
    (hRRp : pCoreOf 2 I ≤ Rp) : V ≤ centerOf (pCoreOf 2 I) := by
  have hVM : V ≤ M :=
    hVle.trans ((omegaOneCenterOf_le Rp).trans (hRp.1.trans (centralizerSection_le_left _ _ _)))
  obtain ⟨H, hH, hHM⟩ := hI.1.2
  obtain ⟨H₁, hH₁, hHH₁⟩ := exists_inM_of_pCoreOf_ne_bot hH.2
  have hH₁M : ¬ H₁ ≤ M := fun hle => hHM (hHH₁.trans hle)
  have hIH₁ : InH I H₁ := ⟨hH.1.trans hHH₁, pCoreOf_ne_bot_of_isTwoLocal hH₁.1⟩
  obtain ⟨-, -, h5a, h5b⟩ := lemma_4_1_4_five h hS hI hIH₁ hH₁M
  have hc := lemma_4_1_4_six h hS hI hIH₁ hH₁M
  have hVH₁ : V ≤ H₁ := by
    intro v hv
    rw [← normalizer_pCoreOf_eq_of_isMaxTwoLocal hH₁]
    exact Subgroup.centralizer_le_normalizer _
      (le_centralizer_of_le_omegaOneCenterOf hVle ((h5a.trans h5b).trans hRRp) hv)
  have hVO : V ≤ pCoreOf 2 (H₁ ⊓ M) := fun v hv =>
    hc ⟨⟨hVH₁ hv, hVM hv⟩, le_centralizer_of_le_omegaOneCenterOf hVle (h5b.trans hRRp) hv⟩
  exact le_inf (hVO.trans h5b) (le_centralizer_of_le_omegaOneCenterOf hVle hRRp)

theorem lemma_4_1_5_two (h : Hyp4_1_1 G T M Mp) {Rp V : Subgroup G}
    (hRp : IsSylowTwoOf Rp (centralizerSection M Mp (pCoreOf 2 Mp))) (hV1 : V ≠ ⊥)
    (hVle : V ≤ omegaOneCenterOf Rp) (hVeq : V = ⁅omegaOneCenterOf Rp, Mp⁆) :
    Subgroup.normalizer (V : Set G) ≤ M := by
  refine isUniqueM_normalizer_le (lemma_4_1_2 h hRp) hV1
    (hRp.2.1.to_le (hVle.trans (omegaOneCenterOf_le Rp))) fun g hg => ?_
  rw [hVeq]
  exact mem_normalizer_commutator (normalizer_le_normalizer_omegaOneCenterOf Rp hg.2)
    (h.normal hg.1)

theorem lemma_4_1_5_three (h : Hyp4_1_1 G T M Mp) (hS : IsSigma M Mp Mm) {Rp V I H : Subgroup G}
    (hRp : IsSylowTwoOf Rp (centralizerSection M Mp (pCoreOf 2 Mp)))
    (hVeq : V = ⁅V, Mp⁆) (hVle : V ≤ omegaOneCenterOf Rp) (hI : IsIota M Mp Mm I)
    (hIH : I ≤ H) : V = ⁅V, oTwoUpper (Mp ⊓ H)⁆ := by
  obtain ⟨hMp, -⟩ := lemma_4_1_4_three h hS hI hIH
  have hHpMp : oTwoUpper (Mp ⊓ H) ≤ Mp := (oTwoUpper_le _).trans inf_le_left
  refine le_antisymm ?_ ?_
  · calc V = ⁅V, Mp⁆ := hVeq
      _ ≤ ⁅V, oTwoUpper (Mp ⊓ H)⁆ := by
        rw [Subgroup.commutator_le]
        intro v hv m hm
        have hm' : m ∈ oTwoUpper (Mp ⊓ H) ⊔ pCoreOf 2 Mp := hMp ▸ hm
        obtain ⟨a, ha, o, ho, rfl⟩ := (mem_sup_of_le_normalizer
          (hHpMp.trans (h.Mp_le.trans h.le_normalizer_pCoreOf_Mp))).mp hm'
        have hvo : Commute v o :=
          (commute_of_le_omegaOneCenterOf hVle hv (h.pCoreOf_Mp_le hRp ho)).symm
        have hov : o * v⁻¹ = v⁻¹ * o := (hvo.inv_left).eq.symm
        have e : v * (a * o) * v⁻¹ * (a * o)⁻¹ = v * a * v⁻¹ * a⁻¹ := by
          calc v * (a * o) * v⁻¹ * (a * o)⁻¹ = v * a * (o * v⁻¹) * o⁻¹ * a⁻¹ := by group
            _ = v * a * (v⁻¹ * o) * o⁻¹ * a⁻¹ := by rw [hov]
            _ = v * a * v⁻¹ * a⁻¹ := by group
        rw [commutatorElement_def, e]
        exact Subgroup.commutator_mem_commutator hv ha
  · calc ⁅V, oTwoUpper (Mp ⊓ H)⁆ ≤ ⁅V, Mp⁆ := Subgroup.commutator_mono le_rfl hHpMp
      _ = V := hVeq.symm

end CFSG.Quasithin.H13.Ch4
