module

public import CFSG.Quasithin.EmptyFaithful.S153D43

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def Input15343Inner : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp1 T Mc M V₁ V₂ Yp I L t → Concl15343Open T M V₁ V₂ Yp I L →
      Yp ≤ L ⊔ Subgroup.centralizer (L : Set G)

@[expose] def Input15343Project : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp1 T Mc M V₁ V₂ Yp I L t → Concl15343Open T M V₁ V₂ Yp I L →
      Yp ≤ L ⊔ Subgroup.centralizer (L : Set G) → Yp ≤ L

namespace S153I

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem Yp_ne_bot_of_open (c : CtxComp1 T Mc M V₁ V₂ Yp I L t)
    (hopen : Concl15343Open T M V₁ V₂ Yp I L) : Yp ≠ ⊥ := by
  intro hbot
  have h1 : ⁅V₂, Yp⁆ = V₂ := hopen.b_V2.1
  rw [hbot, Subgroup.commutator_bot_right] at h1
  have h4 := c.hyp.decomp.card₂
  rw [← h1, Subgroup.card_bot] at h4
  omega

theorem sgp153_le_normalizer_of_Yp_le (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (c : CtxComp1 T Mc M V₁ V₂ Yp I L t) (hne : Yp ≠ ⊥) (hYL : Yp ≤ L) :
    Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) := by
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.hyp
  have hq := hh.hyp.qtfe
  have hLI : L ∈ cComp I := c.c33.mem
  have hLle : L ≤ I := le_of_mem_cComp hLI
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
  have hSYp : Sgp153 T V₁ ≤ Subgroup.normalizer (Yp : Set G) := by
    intro s hs
    have hsM : s ∈ M ⊓ I := ⟨hh.hyp.T_le hs.1, hSI hs⟩
    rw [← c.facts.norm_eq] at hsM
    exact hsM.2
  intro s hs
  by_contra hsn
  rcases lemma_1_2_1_three hq.qtke hq.simple hq.nonabelian h37 h38 c.inH.1.2 hLI with hn | ⟨-, htypes⟩
  · exact hsn ((Subgroup.normal_subgroupOf_iff_le_normalizer hLle).mp hn (hSI hs))
  have hsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types htypes
  set L' := L.map (MulAut.conj s).toMonoidHom with hL'
  have hL'c : L' ∈ cComp I := map_conj_mem_cComp hLI (hSI hs)
  have hne' : L ≠ L' := fun h' => hsn (A38.map_conj_eq_iff.mp h'.symm)
  obtain ⟨hc1, -⟩ := lemma_1_2_1_two hq.qtke hq.simple hq.nonabelian h37 c.inH.1.2 hLI hL'c hne'
  have key : ∀ y ∈ Yp, Odd (orderOf y) → y = 1 := by
    intro y hy hodd
    have hyL : y ∈ L := hYL hy
    have hsinv : s⁻¹ ∈ Subgroup.normalizer (Yp : Set G) :=
      (Subgroup.normalizer (Yp : Set G)).inv_mem (hSYp hs)
    have hy' : s⁻¹ * y * s ∈ Yp := by
      have := (Subgroup.mem_normalizer_iff.mp hsinv y).mp hy
      simpa using this
    have hyL' : y ∈ L' := by
      rw [hL', A38.mem_map_conj]
      exact hYL hy'
    have hcomm : ∀ l ∈ L, l * y * l⁻¹ * y⁻¹ ∈ pCoreOf 2 L := fun l hl =>
      (hc1 (Subgroup.commutator_mem_commutator hl hyL')).1
    have hyO : y ∈ pCoreOf 2 L := S153D.mem_pCoreOf_of_commutators hLI hsimple hyL hcomm
    obtain ⟨j, hj⟩ := (pCoreOf_isPGroup 2 L) ⟨y, hyO⟩
    have hy2 : y ^ 2 ^ j = 1 := congrArg Subtype.val hj
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      ((Nat.coprime_two_right.mpr hodd).pow_right j) dvd_rfl (orderOf_dvd_of_pow_eq_one hy2))
  apply hne
  have hbot : oTwoUpper Yp = ⊥ := by
    rw [eq_bot_iff, oTwoUpper, Subgroup.closure_le]
    rintro x ⟨hx, hxodd⟩
    exact Subgroup.mem_bot.mpr (key x hx hxodd)
  rw [← hh.oTwoUpper_eq]
  exact hbot

theorem input15343Reduce_of_named_inputs (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (hI : Input15343Inner) (hP : Input15343Project) : Input15343Reduce := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hopen
  have hin := hI G T Mc M V₁ V₂ Yp I L t c hopen
  have hYL := hP G T Mc M V₁ V₂ Yp I L t c hopen hin
  exact ⟨hYL, sgp153_le_normalizer_of_Yp_le h37 h38 c (Yp_ne_bot_of_open c hopen) hYL⟩

end S153I

end CFSG.Quasithin
