module

public import CFSG.Quasithin.EmptyFaithful.S1421Q9A
public import CFSG.Quasithin.EmptyFaithful.S1421Q9C
public import CFSG.Quasithin.EmptyFaithful.S1421Q9D
public import CFSG.Quasithin.EmptyFaithful.S1421QEx
public import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.Quasithin.EmptyFaithful.S1421L11

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Q9

variable {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}

theorem isMaximalLocal_oTwoUpper
    (h128Four : Lemma128Four) (hL34 : L34Maximal) (st : Setting1427 T M H K1)
    (hK : oTwoUpper H ∈ cComp H) (hs3 : ShapeL3Sp4 T K1 (oTwoUpper H)) :
    quasithinIsMaximalLocal T (oTwoUpper H) := by
  have hTN : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    st.hStar.1.1.trans (le_normalizer_oTwoUpper H)
  have hKloc : quasithinIsLocal T (oTwoUpper H) := isLocal_of_cComp_H st hK
  by_cases hP : IsPSL 3 2 2 (ModO2 (oTwoUpper H))
  · exact hL34 G st.hyp.qtke st.hyp.simple st.hyp.nonabelian T (oTwoUpper H) st.hyp.sylow hKloc
      hTN hP hs3.diag
  · obtain ⟨n, hn2, -, hcen⟩ := hs3.exists_n
    have hex := exactType_oTwoQuot (perfect_of_mem_cComp hK) hn2 hcen
    let e : OTwoQuot (oTwoUpper H) ≃* ModO2 (oTwoUpper H) :=
      QuotientGroup.quotientMulEquivOfEq (BlueprintB2.pCore_eq_open_pCore 2 _).symm
    have hex' : IsPSL 3 2 n (ModO2 (oTwoUpper H)) ∨ IsSL3 (2 ^ n) (ModO2 (oTwoUpper H)) ∨
        IsPSp4 2 n (ModO2 (oTwoUpper H)) := by
      rcases hex with h | h | h
      · exact Or.inl (IsPSL.of_mulEquiv e h)
      · exact Or.inr (Or.inl (IsSL3.of_mulEquiv e h))
      · exact Or.inr (Or.inr (IsPSp4.of_mulEquiv e h))
    exact h128Four G st.hyp.qtke st.hyp.simple st.hyp.nonabelian T (oTwoUpper H) hKloc
      (a128FourList_of_exactType hn2 hex' hP)

theorem K_le_sup_of_sylow (st : Setting1427 T M H K1) (hK : oTwoUpper H ∈ cComp H)
    (hs3 : ShapeL3Sp4 T K1 (oTwoUpper H))
    (hMcN : mcOf T ≤ Subgroup.normalizer (oTwoUpper H : Set G)) {T1 : Subgroup G}
    (hT1 : IsSylowTwoOf T1 (mcOf T)) (hST1 : S1421.sOf T K1 ≤ T1) :
    oTwoUpper H ≤ K1 ⊔ T1 := by
  obtain ⟨P, P', -, hP, hP', hBor, hK1P, hcov⟩ := hs3.parabolic
  have hTMc := isSylowTwoOf_mcOf st
  have hKMc : oTwoUpper H ≤ mcOf T := (oTwoUpper_le H).trans (H_le_mcOf st)
  have hTNK : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    st.hStar.1.1.trans (le_normalizer_oTwoUpper H)
  have hUle : T ⊓ oTwoUpper H ≤ T1 :=
    (le_inf inf_le_left st.notation_.inf_le : T ⊓ oTwoUpper H ≤ S1421.sOf T K1).trans hST1
  have hSylTK : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
    A4.isSylowTwoOf_inf_normal hTMc hKMc hMcN
  have hSylT1K : IsSylowTwoOf (T1 ⊓ oTwoUpper H) (oTwoUpper H) :=
    A4.isSylowTwoOf_inf_normal hT1 hKMc hMcN
  have hUeq : T ⊓ oTwoUpper H = T1 ⊓ oTwoUpper H :=
    eq_of_isSylowTwoOf_of_le hSylTK hSylT1K (le_inf hUle inf_le_right)
  set N : Subgroup G := mcOf T ⊓ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G)
    with hN
  have hTN' : T ≤ N := le_inf hTMc.1 fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hTNK ht⟩
  have hT1N' : T1 ≤ N := by
    refine le_inf hT1.1 fun t ht => ?_
    rw [hUeq]
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer ht, hMcN (hT1.1 ht)⟩
  have hSylT : IsSylowTwoOf T N := A4.isSylowTwoOf_mono hTMc hTN' inf_le_left
  have hSylT1 : IsSylowTwoOf T1 N := A4.isSylowTwoOf_mono hT1 hT1N' inf_le_left
  have hNK : N ≤ Subgroup.normalizer (oTwoUpper H : Set G) := inf_le_left.trans hMcN
  have hNU : N ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := inf_le_right
  have hUP : T ⊓ oTwoUpper H ≤ P := fun x hx => (hBor ⟨hx.2, Subgroup.le_normalizer hx⟩).1
  have hPK : P ≤ oTwoUpper H := hP.1.1
  have hTP : ¬ T ≤ Subgroup.normalizer (P : Set G) :=
    hs3.diag P hP fun x hx => (hBor hx).1
  have hTP' : ¬ T ≤ Subgroup.normalizer (P' : Set G) :=
    hs3.diag P' hP' fun x hx => (hBor hx).2
  obtain ⟨r, hrT1, hr⟩ := exists_swap_of_sylow hSylT hSylT1 hNK hNU hcov hUP hPK hTP hTP'
  have hK1ne : K1 ≠ ⊥ := ne_bot_of_mem_cComp st.notation_.cComp_mem
  have hK1perf : ⁅K1, K1⁆ = K1 := perfect_of_mem_cComp st.notation_.cComp_mem
  have hgen : conjClosure K1 T = oTwoUpper H :=
    conjClosure_eq_of_cComp hK (sup_eq_hStar st).symm st.notation_.le_K hK1ne hK1perf hTNK
  have hK1r : K1.map (MulAut.conj r).toMonoidHom = perfectCore P' := by
    rw [hK1P, map_perfectCore, hr]
  have hconj : ∀ h ∈ T, K1.map (MulAut.conj h).toMonoidHom = K1 ∨
      K1.map (MulAut.conj h).toMonoidHom = K1.map (MulAut.conj r).toMonoidHom := by
    intro h hh
    have e1 : K1.map (MulAut.conj h).toMonoidHom =
        perfectCore (P.map (MulAut.conj h).toMonoidHom) := by
      rw [hK1P, map_perfectCore]
    rcases conj_eq_or_eq_of_covBy hcov hUP hPK (hNK (hTN' hh)) (hNU (hTN' hh)) with h1 | h1
    · left
      rw [e1, h1, ← hK1P]
    · right
      rw [e1, h1, hK1r]
  have hle : oTwoUpper H ≤ K1 ⊔ K1.map (MulAut.conj r).toMonoidHom := by
    rw [← hgen]
    refine conjClosure_le fun h hh z hz => ?_
    have hz' : h * z * h⁻¹ ∈ K1.map (MulAut.conj h).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨z, hz, by simp [MulAut.conj_apply]⟩
    rcases hconj h hh with h1 | h1
    · rw [h1] at hz'
      exact Subgroup.mem_sup_left hz'
    · rw [h1] at hz'
      exact Subgroup.mem_sup_right hz'
  refine hle.trans (sup_le le_sup_left ?_)
  rintro x ⟨z, hz, rfl⟩
  have hmem : r * z * r⁻¹ ∈ K1 ⊔ T1 :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ ((le_sup_right : T1 ≤ K1 ⊔ T1) hrT1)
      ((le_sup_left : K1 ≤ K1 ⊔ T1) hz)) (Subgroup.inv_mem _ ((le_sup_right : T1 ≤ K1 ⊔ T1) hrT1))
  simpa [MulAut.conj_apply] using hmem

theorem case3_of_maximal (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (st : Setting1427 T M H K1) (hK : oTwoUpper H ∈ cComp H)
    (hs3 : ShapeL3Sp4 T K1 (oTwoUpper H)) (hmax : quasithinIsMaximalLocal T (oTwoUpper H)) :
    ∃ Kc ∈ cComp (mcOf T), K1 ≤ Kc ∧ oTwoUpper H ≤ Kc ⊔ T ∧
      ∀ T1 : Subgroup G, IsSylowTwoOf T1 (mcOf T) → S1421.sOf T K1 ≤ T1 →
        Kc ≤ K1 ⊔ T1 ∨ 2 ≤ CFSG.Open.pRank 3 (conjClosure K1 T1) := by
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hKT : oTwoUpper H ⊔ T = H := S1421.sup_oTwoUpper_eq st
  have hTN : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    st.hStar.1.1.trans (le_normalizer_oTwoUpper H)
  have hBl : oTwoUpper H ∈ lFamily T := by
    show oTwoUpper H ∈ cComp (oTwoUpper H ⊔ T)
    rw [hKT]
    exact hK
  obtain ⟨Kc, hKc, hKKc⟩ := exists_cComp_mcOf h37 h39 st hBl (hKH.trans (H_le_mcOf st))
  have hKcK : Kc = oTwoUpper H := hmax.2 Kc (isLocal_of_cComp_mcOf st hKc) hKKc
  have hKMc : mcOf T ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
    have hnorm := lemma_1_2_4_normal st.hyp.qtke st.hyp.simple st.hyp.nonabelian h37 h38
      (pCoreOf_mcOf_ne_bot st) (isSylowTwoOf_mcOf st) hBl hKKc hKc hTN
    rw [hKcK] at hnorm
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (hKH.trans (H_le_mcOf st))).mp hnorm
  refine ⟨Kc, hKc, st.notation_.le_K.trans hKKc, hKKc.trans le_sup_left, ?_⟩
  intro T1 hT1 hST1
  left
  rw [hKcK]
  exact K_le_sup_of_sylow st hK hs3 hKMc hT1 hST1

theorem case3
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h128Four : Lemma128Four) (hL34 : L34Maximal) (st : Setting1427 T M H K1)
    (hK : oTwoUpper H ∈ cComp H) (hs3 : ShapeL3Sp4 T K1 (oTwoUpper H)) :
    ∃ Kc ∈ cComp (mcOf T), K1 ≤ Kc ∧ oTwoUpper H ≤ Kc ⊔ T ∧
      ∀ T1 : Subgroup G, IsSylowTwoOf T1 (mcOf T) → S1421.sOf T K1 ≤ T1 →
        Kc ≤ K1 ⊔ T1 ∨ 2 ≤ CFSG.Open.pRank 3 (conjClosure K1 T1) :=
  case3_of_maximal h37 h38 h39 st hK hs3 (isMaximalLocal_oTwoUpper h128Four hL34 st hK hs3)

end Q9

end CFSG.Quasithin
