module

public import CFSG.Quasithin.Vol2.Ch1Eight
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux
public import CFSG.Quasithin.EmptyFaithful.Setting

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem charTwo_of_isLocal (hQ : quasithinIsQTKECat G) {T K : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hK : quasithinIsLocal T K) : CharTwo K := by
  obtain ⟨S, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  have hH' : InH (S : Subgroup G) (K ⊔ (S : Subgroup G)) := ⟨le_sup_right, hK.2.2.2⟩
  exact A4.charTwo_of_subnormal (subnormal_of_mem_cComp (cComp_of_isLocal hK))
    (charTwo_of_inH hQ.2.1 S hH')

theorem isXClass_of_isLocal (hQ : quasithinIsQTKECat G) {T K : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hK : quasithinIsLocal T K) : IsXClass K :=
  ⟨ne_bot_of_mem_cComp (cComp_of_isLocal hK),
    eq_oTwoUpper_of_perfect (perfect_of_mem_cComp (cComp_of_isLocal hK)),
    charTwo_of_isLocal hQ hT hK⟩

theorem isSylowTwoOf_sup_of_inf {R K : Subgroup G} (hR : IsPGroup 2 R)
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) (h : IsSylowTwoOf (R ⊓ K) K) :
    IsSylowTwoOf R (K ⊔ R) := by
  rw [A4.isSylowTwoOf_iff_maximal]
  refine ⟨le_sup_right, hR, fun P hPH hP hRP => ?_⟩
  intro t ht
  have htH : t ∈ R ⊔ K := by rw [sup_comm]; exact hPH ht
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right R K hRK] at htH
  obtain ⟨r, hr, k, hk, rfl⟩ := htH
  have hkP : k ∈ P := by
    have := P.mul_mem (P.inv_mem (hRP hr)) ht
    simpa using this
  have hmax := ((A4.isSylowTwoOf_iff_maximal).mp h).2.2 (P ⊓ K) inf_le_right (hP.to_inf_left)
    (le_inf (inf_le_left.trans hRP) inf_le_right)
  have hkR : k ∈ R := (hmax ⟨hkP, hk⟩).1
  exact R.mul_mem hr hkR

theorem isSylowTwoOf_sup_of_isLocal {T K R : Subgroup G} (hK : quasithinIsLocal T K) (hRT : R ≤ T)
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) (hKR : T ⊓ K ≤ R) : IsSylowTwoOf R (K ⊔ R) := by
  have hTS : IsSylowTwoOf T (K ⊔ T) := ⟨le_sup_right, hK.1, hK.2.2.1⟩
  have h1 : IsSylowTwoOf (T ⊓ K) K :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp (cComp_of_isLocal hK)) hTS
  have hRKeq : R ⊓ K = T ⊓ K :=
    le_antisymm (inf_le_inf_right K hRT) (le_inf hKR inf_le_right)
  rw [← hRKeq] at h1
  exact isSylowTwoOf_sup_of_inf (hK.1.to_le hRT) hRK h1

theorem pCoreOf_sup_eq_centralizerSection {X T : Subgroup G} (h : A410Hyp X X T) :
    pCoreOf 2 (X ⊔ T) = centralizerSection T X (pCoreOf 2 X) := by
  have hmax := a4_10_1 h
  refine le_antisymm (A4.pCoreOf_sup_le_centralizerSection h) ?_
  have hTN : T ≤ Subgroup.normalizer (centralizerSection T X (pCoreOf 2 X) : Set G) :=
    (le_inf le_rfl h.normalizes).trans (le_normalizer_centralizerSection T X)
  exact le_pCoreOf_of_le_normalizer 2 ((centralizerSection_le_left T X _).trans le_sup_right)
    (sup_le hmax.1.2.2 hTN) hmax.1.2.1

theorem lemma_1_2_9_one (hQ : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK) (h128 : Lemma128One)
    {T L K : Subgroup G} (hT : quasithinIsSylowTwo T) (hL : quasithinIsFaithfulLocal T L)
    (hK : quasithinIsLocal T K) (hLK : L ≤ K) :
    VYR L (pCoreOf 2 ((T ⊓ Subgroup.normalizer (L : Set G)) ⊔ L)) ≤
        VYR K (pCoreOf 2 ((T ⊓ Subgroup.normalizer (K : Set G)) ⊔ K)) ∧
      quasithinIsFaithfulLocal T K := by
  obtain ⟨hLloc, hLX⟩ := isFaithfulLocal_iff_isXf.mp hL
  have heq := lemma_1_2_8_one hQ hs hnab h37 h128 hLloc hK hLK
  set R := T ⊓ Subgroup.normalizer (K : Set G) with hR
  have hRL : R ≤ Subgroup.normalizer (L : Set G) := h128 G hQ hs hnab T L K hLloc hK hLK
  have hKR : T ⊓ K ≤ R := le_inf inf_le_left (inf_le_right.trans Subgroup.le_normalizer)
  have hLR : T ⊓ L ≤ R := fun x hx => ⟨hx.1, Subgroup.le_normalizer (hLK hx.2)⟩
  have hRsylK : IsSylowTwoOf R (K ⊔ R) :=
    isSylowTwoOf_sup_of_isLocal hK inf_le_left inf_le_right hKR
  have hRsylL : IsSylowTwoOf R (L ⊔ R) :=
    isSylowTwoOf_sup_of_isLocal hLloc inf_le_left hRL hLR
  have hXK : IsXClass K := isXClass_of_isLocal hQ hT hK
  have hO2K : pCoreOf 2 (K ⊔ R) ≤ R := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hRsylK
  have hO2L : pCoreOf 2 (L ⊔ R) ≤ R := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hRsylL
  have hA : A410Hyp L K R :=
    { xclass := hLX.1
      yclass := hXK
      xy := hLK
      normalizes := inf_le_right
      sylowT := hRsylK
      o2le := le_inf hO2K (hO2K.trans hRL)
      sylowNT := by
        rw [inf_eq_left.mpr hRL]
        exact A4.isSylowTwoOf_mono hRsylK (le_inf le_sup_right hRL) inf_le_left }
  have hA' : A410Hyp L L R :=
    { xclass := hLX.1
      yclass := hLX.1
      xy := le_rfl
      normalizes := hRL
      sylowT := hRsylL
      o2le := le_inf hO2L (hO2L.trans hRL)
      sylowNT := by
        rw [inf_eq_left.mpr hRL]
        exact A4.isSylowTwoOf_mono hRsylL (le_inf le_sup_right hRL) inf_le_left }
  refine ⟨?_, isFaithfulLocal_iff_isXf.mpr ⟨hK, a4_10_3 hA hLX⟩⟩
  have h2 := a4_10_2 hA
  rw [← pCoreOf_sup_eq_centralizerSection hA'] at h2
  rw [heq, sup_comm, sup_comm (T ⊓ Subgroup.normalizer (K : Set G))]
  exact h2

theorem lemma_1_2_9_two (hQ : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK) (h128 : Lemma128One)
    {T L : Subgroup G} (hT : quasithinIsSylowTwo T) (hL : quasithinIsFaithfulLocal T L)
    (hmax : ∀ K : Subgroup G, quasithinIsFaithfulLocal T K → L ≤ K → K = L) :
    quasithinIsMaximalLocal T L ∧ quasithinIsFaithfulLocal T L :=
  ⟨⟨hL.1, fun K hK hLK =>
    hmax K (lemma_1_2_9_one hQ hs hnab h37 h128 hT hL hK hLK).2 hLK⟩, hL⟩

end CFSG.Quasithin
