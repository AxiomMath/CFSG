module

public import CFSG.Quasithin.H13.L32NThm14326
public import CFSG.Quasithin.H13.L32NLem1442
public import CFSG.Quasithin.EmptyFaithful.S1421F112
public import CFSG.Quasithin.H13.L32NThm144Big

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative
open scoped MatrixGroups

@[expose] def Q8SqE9Decomp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G),
    IsQ8Sq ↥(pCoreOf 2 H) →
    IsElemAbelian 3 (imageOTwoQuot H (oTwoUpper H)) →
    Nat.card ↥(imageOTwoQuot H (oTwoUpper H)) = 9 →
    centralizerMod (centerOf (pCoreOf 2 H)) H (pCoreOf 2 H) = pCoreOf 2 H →
      pCoreOf 2 H ≤ oTwoUpper H ∧
      ∃ K₁ K₂ : Subgroup G, K₁ ⊔ K₂ = oTwoUpper H ∧
        K₁ ⊓ K₂ = centerOf (pCoreOf 2 H) ∧ K₁ ≤ Subgroup.centralizer (K₂ : Set G) ∧
        Nonempty (↥K₁ ≃* SL(2, ZMod 3)) ∧ Nonempty (↥K₂ ≃* SL(2, ZMod 3)) ∧
        ∀ w ∈ H, (∀ x ∈ oTwoUpper H, w * x * w⁻¹ * x ∈ pCoreOf 2 H) →
          w ∈ Subgroup.normalizer (K₁ : Set G) ∧ w ∈ Subgroup.normalizer (K₂ : Set G)

variable {G : Type} [Group G]

theorem isQ8Sq_of_isQ8CentralPow_two {P : Type*} [Group P] (h : IsQ8CentralPow 2 P) :
    IsQ8Sq P := by
  obtain ⟨hcard, Q, hcomm, hsup, hiso⟩ := h
  refine ⟨by simpa using hcard, Q 0, Q 1, ⟨hcomm 0 1 (by decide), ?_⟩, hiso 0, hiso 1⟩
  rw [← hsup]
  refine le_antisymm (sup_le (le_iSup Q 0) (le_iSup Q 1)) (iSup_le fun i => ?_)
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

theorem normalizer_eq_centralizer_self_of_card_two {A : Subgroup G} (hA : Nat.card A = 2) :
    Subgroup.normalizer (A : Set G) = Subgroup.centralizer (A : Set G) := by
  obtain ⟨z, hz1, -⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hA
  have hz : (z : G) ≠ 1 := fun h0 => hz1 (Subtype.ext h0)
  refine le_antisymm ?_ (Subgroup.centralizer_le_normalizer _)
  rw [normalizer_eq_centralizer_of_card_two hA z.2 hz]
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hcomm : g * z = z * g := (Subgroup.mem_centralizer_iff.mp hg z rfl).symm
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hA
  by_cases ha1 : a = 1
  · rw [ha1, one_mul, mul_one]
  · have h1 := huniq ⟨a, ha⟩ (fun h => ha1 (congrArg Subtype.val h))
    have h2 := huniq z hz1
    have haz : a = z := congrArg Subtype.val (h1.trans h2.symm)
    rw [haz, hcomm]

namespace Hyp14310One

variable [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem conjugate_le_l32nH {V₂ : Subgroup G} {g : G} (hV₂ : IsL32NPlane T V V₂)
    (hgN : g ∈ Subgroup.normalizer (V₂ : Set G)) :
    CFSG.conjugate (fsuU T V ⊓ Subgroup.centralizer (V₂ : Set G)) g ≤ l32nH T V := by
  rintro _ ⟨w, hw, rfl⟩
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hvV₂ : v ∈ V₂ := hV₂.2 hv
  have hgv : g * v * g⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.mp hgN v).mp hvV₂
  have hc := (Subgroup.mem_centralizer_iff.mp hw.2) _ hgv
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  calc v * (g⁻¹ * w * g) = g⁻¹ * ((g * v * g⁻¹) * w) * g := by group
    _ = g⁻¹ * (w * (g * v * g⁻¹)) * g := by rw [hc]
    _ = g⁻¹ * w * g * v := by group

theorem isG23Type (h : Hyp14310One G T L V) (h13322 : Stmt13_3_2_two) (hV : StmtL32NModule)
    (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h1284 : Lemma12_8_4) (h14441 : Lemma1444One)
    (h14442 : Lemma1444Two) (h14444 : Lemma1444Four) (h14447 : Lemma1444Seven)
    (h14452 : Lemma1445Two) (h14453 : Lemma1445Three)
    (hdec : Q8SqE9Decomp) (hext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V))
    (h32 : Nat.card ↥(fsuU T V) = 2 ^ 5) (hG2 : ¬ LieModel G .G2 0 3 1) :
    G23Type.IsG23Type G := by
  have h1281 := h.hyp1281One h13322 hV
  obtain ⟨hVe, hV8, -, hV1, -⟩ := hV G T L V h.hyp h.fsu
  obtain ⟨hUQ, N, hNn, -, hN9, hN2⟩ := h14452 G T L V h hext h32 hG2
  obtain ⟨V₂, g, ⟨hV₂, hV₁₂⟩, hgP, hgH⟩ := h.exists_plane_and_g h13322 hV (exist1282g h1222)
  obtain ⟨⟨U₀, -, hU₀ext, hΦ, hU₀Z⟩, -⟩ :=
    lemma12_8_8_n3 h1222 h12213 (h.setting1282One h13322 hV ⟨hV₂, hV₁₂⟩)
  have hV1Z := fsuV1_le_centerOf_of_decomp hU₀Z hU₀ext hΦ
  have hZ2 : Nat.card ↥(centerOf (fsuU T V)) = 2 := by
    rw [l32n_card_centerOf]
    exact hext.2.2.2
  have hZV1 : centerOf (fsuU T V) = fsuV1 T V :=
    (Subgroup.eq_of_le_of_card_ge hV1Z (by rw [hZ2, hV1])).symm
  have hk : IsQ8CentralPow 2 ↥(fsuU T V) := lemma1442Q8Four_of_inputs hV h hext h32
  have hQ8 : IsQ8Sq ↥(pCoreOf 2 (l32nH T V)) := hUQ ▸ isQ8Sq_of_isQ8CentralPow_two hk
  have hfaith : centralizerMod (centerOf (pCoreOf 2 (l32nH T V))) (l32nH T V)
      (pCoreOf 2 (l32nH T V)) = pCoreOf 2 (l32nH T V) := by
    rw [← hUQ, hZV1]
    exact (h1284 G T L V 3 h1281 (fsuV1 T V) (l32nH T V) (h.isTSub_fsuV1 hV)
      (h.isHzOne_l32nH h13322 hV (lemma12_8_3 h12213))).2.2.2.trans hUQ.symm
  obtain ⟨hK1, hK9⟩ := h14441 G T L V h hext h32 hG2
  obtain ⟨hQK, K₁, K₂, hsup, hinf, hcomm, he₁, he₂, hw⟩ :=
    hdec G (l32nH T V) hQ8 hK1 hK9 hfaith
  obtain ⟨-, -, hinv, -⟩ := h14442 G T L V h hext h32 hG2 V₂ g ⟨hV₂, hV₁₂⟩ hgP hgH
  have hT := h14453 G T L V h hext h32 hG2 V₂ g ⟨hV₂, hV₁₂⟩ hgP hgH
  have hHKT := (h14447 G T L V h hext h32 hG2).1
  have hgN : g ∈ Subgroup.normalizer (V₂ : Set G) :=
    (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hgP.2 V₂) ⟨2, le_rfl, hV₂⟩)
  have hWgH := conjugate_le_l32nH (T := T) (V := V) ⟨hV₂, hV₁₂⟩ hgN
  have hwinv : ∀ w ∈ CFSG.conjugate (fsuU T V ⊓ Subgroup.centralizer (V₂ : Set G)) g,
      w ∉ pCoreOf 2 (l32nH T V) →
      ∀ x ∈ oTwoUpper (l32nH T V), w * x * w⁻¹ * x ∈ pCoreOf 2 (l32nH T V) := by
    intro w hwW hwQ x hx
    have hxH : x ∈ l32nH T V := oTwoUpper_le _ hx
    have hwH : w ∈ l32nH T V := hWgH hwW
    have hne : (QuotientGroup.mk ⟨w, hwH⟩ : OTwoQuot (l32nH T V)) ≠ 1 := by
      intro h1
      rw [QuotientGroup.eq_one_iff] at h1
      exact hwQ ⟨_, h1, rfl⟩
    have h1 := hinv (QuotientGroup.mk ⟨w, hwH⟩) ⟨⟨w, hwH⟩, hwW, rfl⟩ hne
      (QuotientGroup.mk ⟨x, hxH⟩) ⟨⟨x, hxH⟩, hx, rfl⟩
    have h2 : (QuotientGroup.mk (⟨w, hwH⟩ * ⟨x, hxH⟩ * ⟨w, hwH⟩⁻¹ * ⟨x, hxH⟩ :
        ↥(l32nH T V)) : OTwoQuot (l32nH T V)) = 1 := by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [h1, inv_mul_cancel]
    rw [QuotientGroup.eq_one_iff] at h2
    exact ⟨_, h2, rfl⟩
  have hKN₁ : oTwoUpper (l32nH T V) ≤ Subgroup.normalizer (K₁ : Set G) := by
    rw [← hsup]
    exact sup_le Subgroup.le_normalizer
      ((Subgroup.le_centralizer_iff.mp hcomm).trans (Subgroup.centralizer_le_normalizer _))
  have hKN₂ : oTwoUpper (l32nH T V) ≤ Subgroup.normalizer (K₂ : Set G) := by
    rw [← hsup]
    exact sup_le (hcomm.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  have hHN : ∀ i : Fin 2, l32nH T V ≤
      Subgroup.normalizer ((if i = 0 then K₁ else K₂ : Subgroup G) : Set G) := by
    intro i
    have hK : oTwoUpper (l32nH T V) ≤
        Subgroup.normalizer ((if i = 0 then K₁ else K₂ : Subgroup G) : Set G) := by
      fin_cases i
      · exact hKN₁
      · exact hKN₂
    have hW : CFSG.conjugate (fsuU T V ⊓ Subgroup.centralizer (V₂ : Set G)) g ≤
        Subgroup.normalizer ((if i = 0 then K₁ else K₂ : Subgroup G) : Set G) := by
      intro w hwW
      by_cases hwQ : w ∈ pCoreOf 2 (l32nH T V)
      · exact hK (hQK hwQ)
      have := hw w (hWgH hwW) (hwinv w hwW hwQ)
      fin_cases i
      · exact this.1
      · exact this.2
    calc l32nH T V = oTwoUpper (l32nH T V) ⊔ T := hHKT
      _ ≤ _ := sup_le hK (by
        rw [hT]
        exact sup_le ((hUQ.le.trans hQK).trans hK) hW)
  have hindex : (K₁ ⊔ K₂).relIndex (l32nH T V) = 2 := by
    rw [hsup, Subgroup.relIndex]
    have hker : (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(l32nH T V))).ker ≤
        (oTwoUpper (l32nH T V)).subgroupOf (l32nH T V) := by
      intro x hx
      rw [QuotientGroup.ker_mk'] at hx
      exact hQK ⟨x, hx, rfl⟩
    rw [← Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _) hker]
    have h18 : Nat.card (OTwoQuot (l32nH T V)) = 18 := by
      rw [← N.card_mul_index, hN9, hN2]
    have := (imageOTwoQuot (l32nH T V) (oTwoUpper (l32nH T V))).card_mul_index
    change Nat.card ↥(imageOTwoQuot (l32nH T V) (oTwoUpper (l32nH T V))) *
      (imageOTwoQuot (l32nH T V) (oTwoUpper (l32nH T V))).index = _ at this
    rw [hK9, h18] at this
    change (imageOTwoQuot (l32nH T V) (oTwoUpper (l32nH T V))).index = 2
    omega
  refine ⟨l32nH T V, K₁, K₂, L, ?_, ?_⟩
  · have hK₁ : K₁ ≤ l32nH T V := (le_sup_left.trans hsup.le).trans (oTwoUpper_le _)
    have hK₂ : K₂ ≤ l32nH T V := (le_sup_right.trans hsup.le).trans (oTwoUpper_le _)
    refine ⟨hK₁, hK₂, hHN 0, hHN 1, he₁, he₂, hindex, ?_, ?_⟩
    · rw [hinf, ← hUQ, hZV1, hV1]
    · rw [hinf, ← hUQ, hZV1]
      exact normalizer_eq_centralizer_self_of_card_two hV1
  · have hFL : quasithinGenFitting L = pCoreOf 2 L := h.fsu.faithful.2.2.1
    have hVL := h14444 G T L V h hext h32 hG2
    refine ⟨?_, ?_, ?_⟩
    · rw [hFL, ← hVL]
      exact hVe
    · rw [hFL, ← hVL, hV8]
    · rw [hFL]
      exact exists_surj_SL32_of_lieModel h.hyp.linear

end Hyp14310One

theorem thm1443One_of_inputs (hI45 : G23Type.StatementI45) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h14441 : Lemma1444One)
    (h14442 : Lemma1444Two) (h14444 : Lemma1444Four) (h14447 : Lemma1444Seven)
    (h14452 : Lemma1445Two) (h14453 : Lemma1445Three) (hdec : Q8SqE9Decomp) : Thm1443One := by
  intro G _ _ T L V h hext h32
  by_contra hG2
  exact hG2 (hI45 G (h.isG23Type (stmt13_3_2_two_of_stmt13_3_2 h1332)
    (stmtL32NModule_of_inputs h1332 h1334) h1222 h12213 (lemma12_8_4 h1222 h37 h38 h39)
    h14441 h14442 h14444 h14447 h14452 h14453 hdec hext h32 hG2))

end CFSG.Quasithin.H13
