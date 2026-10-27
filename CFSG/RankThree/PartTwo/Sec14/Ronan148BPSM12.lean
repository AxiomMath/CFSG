module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSConj
public import CFSG.RankThree.PartTwo.Sec14.Ronan148BSolv3520
public import CFSG.Quasithin.H13.NQCatT3Perm
public import Certificates.Certificate148011
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanM12E9
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KF148Sig.Cores
public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofSporM12

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B.M12

open Subgroup CFSG.Blueprint CFSG.RankThree.PartTwo CFSG.GH74.M12.Hyp
  CFSG.RankThree.PartTwo.Toolkit.M12 CFSG.RankThree.PartTwo.Sec4.Sporadic.M12Sig
  CFSG.RankThree.PartTwo.Sec14.Ronan148B.M12Gen
open CFSG.RankThree.Asc83Table (E9Basis)
open scoped commutatorElement

section Gen


theorem gen_spec :
    (∀ k ∈ List.range 9, (VT (k / 3)).contains (vGensT.getD k tid) = true) ∧
      wprod wordA = tA ∧ wprod wordB = tB ∧
      (∀ i ∈ List.range 3, ∀ u ∈ VT i, ∃ v ∈ VT i, ∃ f ∈ AT, u = tcm v f) := by
  have h := Certificates.certificate148011
  simp only [genCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem V_eq_commutator (i : Fin 3) : V i = ⁅V i, basisA.sub⁆ := by
  apply le_antisymm
  · intro g hg
    obtain ⟨v, hv, f, hf, he⟩ := gen_spec.2.2.2 i.val (List.mem_range.mpr i.isLt) _ (mem_V.mp hg)
    obtain ⟨gv, hgv⟩ := exists_of_mem_VT hv
    obtain ⟨gf, hgfA, hgf⟩ := exists_mem_A hf
    have hgvV : gv ∈ V i := by rw [mem_V, hgv]; exact hv
    have : g = ⁅gv, gf⁆ := by
      rw [eq_iff_tbl, tblG_comm, hgv, hgf, he]
    rw [this]
    exact Subgroup.commutator_mem_commutator hgvV hgfA
  · rw [Subgroup.commutator_le]
    intro v hv f hf
    have hfv : f * v⁻¹ * f⁻¹ ∈ V i :=
      (mem_normalizer_iff.mp (A_le_normalizer_V i hf) v⁻¹).mp (inv_mem hv)
    have e : ⁅v, f⁆ = v * (f * v⁻¹ * f⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact mul_mem hv hfv

theorem exists_mem_sup_of_word (w : List ℕ) (hw : ∀ k ∈ w, k < 9) :
    ∃ g ∈ V 0 ⊔ V 1 ⊔ V 2, tbl g.1 = wprod w := by
  induction w with
  | nil => exact ⟨1, one_mem _, by rw [tblG_one]; rfl⟩
  | cons k w ih =>
    obtain ⟨g, hg, hgt⟩ := ih fun k' hk' => hw k' (List.mem_cons_of_mem _ hk')
    have hk : k < 9 := hw k List.mem_cons_self
    have hmem := gen_spec.1 k (List.mem_range.mpr hk)
    rw [List.contains_iff_mem] at hmem
    have hk3 : k / 3 < 3 := by omega
    have hmem' : vGensT.getD k tid ∈ VT ((⟨k / 3, hk3⟩ : Fin 3) : ℕ) := hmem
    obtain ⟨h, hh⟩ := exists_of_mem_VT hmem'
    have hhV : h ∈ V 0 ⊔ V 1 ⊔ V 2 := by
      have hV : h ∈ V ⟨k / 3, hk3⟩ := by rw [mem_V, hh]; exact hmem'
      have h3 : k / 3 = 0 ∨ k / 3 = 1 ∨ k / 3 = 2 := by omega
      rcases h3 with h3 | h3 | h3
      · have : (⟨k / 3, hk3⟩ : Fin 3) = 0 := Fin.ext h3
        rw [this] at hV
        exact mem_sup_left (mem_sup_left hV)
      · have : (⟨k / 3, hk3⟩ : Fin 3) = 1 := Fin.ext h3
        rw [this] at hV
        exact mem_sup_left (mem_sup_right hV)
      · have : (⟨k / 3, hk3⟩ : Fin 3) = 2 := Fin.ext h3
        rw [this] at hV
        exact mem_sup_right hV
    refine ⟨h * g, mul_mem hhV hg, ?_⟩
    rw [tblG_mul, hh, hgt]
    rfl

theorem sup_V_eq_top : V 0 ⊔ V 1 ⊔ V 2 = ⊤ := by
  obtain ⟨ga, hga, hta⟩ := exists_mem_sup_of_word wordA (by decide)
  obtain ⟨gb, hgb, htb⟩ := exists_mem_sup_of_word wordB (by decide)
  have ha : ga = CFSG.Sporadic.Mathieu.m12a := by
    rw [eq_iff_tbl, hta, gen_spec.2.1]
    exact tbl_m12gA.symm
  have hb : gb = CFSG.Sporadic.Mathieu.m12b := by
    rw [eq_iff_tbl, htb, gen_spec.2.2.1]
    exact tbl_m12gB.symm
  rw [eq_top_iff, ← CFSG.Sporadic.Mathieu.closure_pair_eq_top CFSG.Sporadic.Mathieu.m12_eq _ _,
    closure_le]
  rintro _ (rfl | rfl)
  · exact ha ▸ hga
  · exact hb ▸ hgb

end Gen

theorem isElemAbelian_of_le_P0 {B : Subgroup G12} (hB : B ≤ P0) (hB9 : Nat.card B = 9) :
    CFSG.Assembly.IsElemAbelian 3 B :=
  ⟨⟨⟨fun a b => Subtype.ext
    (CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KF148Sig.comm_of_card_nine B hB9 _ a.2 _ b.2)⟩⟩,
    fun g hg => cube_of_mem_P0 (hB hg)⟩

theorem false_of_EF
    {B : E9Basis G12} (hB : B = basisE ∨ B = basisF)
    {K Q D : Subgroup G12} (hh : SigGenHyp B.sub K Q D) : False := by
  have hQ3 : ¬ 3 ∣ Nat.card Q := fun h3 => (hh.inv.2.1 ⟨3, Nat.prime_three⟩ h3) rfl
  have hBle : B.sub ≤ P0 := by rcases hB with rfl | rfl; exacts [E_le, F_le]
  have hQ : Q = ⊥ := by
    refine CFSG.RankThree.PartTwo.Sec4.Item434SporGen.eq_bot_of_le_normalizer_of_cent
      (isElemAbelian_of_le_P0 hBle B.card) B.card hQ3 hh.inv.2.2 ?_ ?_
    · intro v hv hv1
      rcases hB with rfl | rfl
      · exact CFSG.RankThree.PartTwo.Sec4.Item434SporGen.card_centralizer_E hv hv1
      · exact CFSG.RankThree.PartTwo.Sec4.Item434SporGen.card_centralizer_F hv hv1
    · intro t ht
      have hC : Nat.card (centralizer (B.sub : Set G12)) = 9 := by
        rcases hB with rfl | rfl
        · rw [centralizer_E]; exact basisE.card
        · rw [centralizer_F]; exact basisF.card
      exact CFSG.RankThree.PartTwo.Sec4.Item434SporGen.mem_of_commute_of_card B.card hC
        (fun a ha b hb =>
          CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KF148Sig.comm_of_card_nine _ B.card a ha b
            hb) t ht
  apply hh.nontriv
  rw [hQ, Subgroup.commutator_bot_right]
  exact bot_le

theorem sigGenConcl_A
    {K Q D : Subgroup G12} (hh : SigGenHyp basisA.sub K Q D) : SigGenConcl basisA.sub K := by
  have hK1 : K ≠ ⊥ := by
    rintro rfl
    have := hh.three
    rw [Subgroup.card_bot] at this
    norm_num at this
  have hAut : Nonempty (CFSG.RankThree.PartTwo.Sec4.autIn ⊤ basisA.sub ≃* Equiv.Perm (Fin 3)) := by
    obtain ⟨e⟩ := automizer_A
    exact ⟨(CFSG.RankThree.PartTwo.Sec4.Sporadic.automizerEquivAutIn _).symm.trans e⟩
  have hK : K = ⊤ := KFacts.ks1515M12Cover G12 ⟨MulEquiv.refl _⟩ basisA.sub K
    (isElemAbelian_of_le_P0 A_le basisA.card) basisA.card hAut hh.perf hK1 hh.normK
  have hsig : ∀ i : Fin 3, V i ≤ sSup {W : Subgroup G12 | W ≤ K ∧
      W ∈ invariantPiSubgroups ⊤ basisA.sub (piCompl 3) ∧ W = ⁅W, basisA.sub⁆} := fun i =>
    le_sSup ⟨hK ▸ le_top, ⟨le_top, fun r hr => by
      rw [card_V] at hr
      change (r : ℕ) ≠ 3
      intro h3
      rw [h3] at hr
      norm_num at hr, A_le_normalizer_V i⟩, V_eq_commutator i⟩
  unfold SigGenConcl
  calc K = ⊤ := hK
    _ = V 0 ⊔ V 1 ⊔ V 2 := sup_V_eq_top.symm
    _ ≤ _ := sup_le (sup_le (hsig 0) (hsig 1)) (hsig 2)


theorem sigGenIn_m12 : SigGenIn148 G12 := by
  intro P K Q D _ hP9 hh
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 2) (by rw [hP9]; norm_num)
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.exists_le_map_conj_of_card
    CFSG.RankThree.PartTwo.Sec4.Res423Two.card_P0_eq hPp
  refine sigGenConcl_of_map (MulAut.conj g⁻¹) (fun hh' => ?_) hh
  have hle : P.map (MulAut.conj g⁻¹).toMonoidHom ≤ P0 :=
    CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.map_conj_inv_le hg
  have hmem : P.map (MulAut.conj g⁻¹).toMonoidHom ∈ {B : Subgroup G12 | B ≤ P0 ∧ Nat.card B = 9} :=
    ⟨hle, by rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hP9]⟩
  rw [nine_eq] at hmem
  rcases hmem with h | h | h | h
  · rw [h] at hh' ⊢
    exact (false_of_EF (Or.inl rfl) hh').elim
  · rw [h] at hh' ⊢
    exact (false_of_EF (Or.inr rfl) hh').elim
  · rw [h] at hh' ⊢
    exact sigGenConcl_A hh'
  · rw [h] at hh' ⊢
    refine sigGenConcl_of_map (MulAut.conj g0) (fun hh'' => ?_) hh'
    rw [map_g0_A'] at hh'' ⊢
    exact sigGenConcl_A hh''

theorem threeSolv_m12 : ThreeSolv148 G12 := by
  intro V hV3
  apply isSolvable_of_card_dvd_3520
  have hdvd : Nat.card V ∣ (2 ^ 6 * 5 * 11) * 3 ^ 3 := by
    rw [show (2 ^ 6 * 5 * 11) * 3 ^ 3 = 95040 by norm_num, ← CFSG.Sporadic.Mathieu.card_M12]
    exact Subgroup.card_subgroup_dvd_card V
  exact (Nat.Coprime.pow_right 3 hV3.symm).dvd_of_dvd_mul_right hdvd

theorem rankTwo_m12 : RankTwo148 G12 := by
  intro E hE hE27
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 3) (by rw [hE27]; norm_num)
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.exists_le_map_conj_of_card
    CFSG.RankThree.PartTwo.Sec4.Res423Two.card_P0_eq hEp
  have heq : E = P0.map (MulAut.conj g).toMonoidHom :=
    Subgroup.eq_of_le_of_card_ge hg (by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_P0, hE27])
  apply not_comm_P0
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have ha : MulAut.conj g (a : G12) ∈ E := heq ▸ Subgroup.mem_map_of_mem _ a.2
  have hb : MulAut.conj g (b : G12) ∈ E := heq ▸ Subgroup.mem_map_of_mem _ b.2
  have := congrArg Subtype.val (hE.1.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)
  simp only [Subgroup.coe_mul] at this
  rw [← map_mul, ← map_mul] at this
  exact (MulAut.conj g).injective this

theorem inspIn148_m12 :
    InspIn148 NativeSporadic.M12 := by
  refine ⟨CFSG.Sporadic.Schreier.m12_center_eq_bot', fun α hα => ?_,
    fun _ V _ _ hV3 _ => threeSolv_m12 V hV3, rankTwo_m12, sigGenIn_m12⟩
  have hodd : Odd (orderOf α) :=
    Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hα)
  obtain ⟨g, rfl⟩ := CFSG.Quasithin.H13.NQCat.T3.oddInner_of_card_le
    CFSG.Sporadic.Schreier.m12_center_eq_bot' CFSG.Sporadic.Schreier.m12_mulAut_card α hodd
  exact ⟨g, rfl⟩

end CFSG.RankThree.PartTwo.Sec14.Ronan148B.M12
