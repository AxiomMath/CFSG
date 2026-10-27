module

public import CFSG.Quasithin.Vol2.Ch1Prop121
public import CFSG.Quasithin.Background.A1aFStar
public import CFSG.Quasithin.Background.A4Reduced
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pCoreOf_ne_bot_of_charTwo {K : Subgroup G} (hK : CharTwo K) (hne : K ≠ ⊥) :
    pCoreOf 2 K ≠ ⊥ := by
  intro h
  apply hne
  rw [eq_bot_iff]
  intro x hx
  have h1 : x ∈ K ⊓ Subgroup.centralizer (pCoreOf 2 K : Set G) := by
    refine ⟨hx, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hy' : y ∈ pCoreOf 2 K := hy
    rw [h, Subgroup.mem_bot] at hy'
    rw [hy']
    simp
  have h2 := hK h1
  rwa [h] at h2

theorem lemma_1_2_7_one (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK) (h39 : A39ForSQTK)
    {T L H : Subgroup G} (hT : quasithinIsSylowTwo T) (hL : quasithinIsMaximalLocal T L)
    (hH : InH (L ⊔ T) H) : L ∈ cComp H := by
  have hTH : T ≤ H := le_sup_right.trans hH.1
  have hLH : L ≤ H := le_sup_left.trans hH.1
  have hS : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo hT hTH
  obtain ⟨K, hK', hLK⟩ := lemma_1_2_4_exists hK hs hnab h37 h39 hH.2 hS hLH
    (mem_lFamily_of_isLocal hL.1)
  have hKloc : quasithinIsLocal T K := isLocal_of_mem_cComp_of_sylow hS hH.2 hK'
  have : K = L := hL.2 K hKloc hLK
  rw [← this]
  exact hK'

theorem lemma_1_2_7_two (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK) (h39 : A39ForSQTK)
    {T L : Subgroup G} (hT : quasithinIsSylowTwo T) (hL : quasithinIsMaximalLocal T L) :
    quasithinGenFitting L = pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  have hH : InH (L ⊔ (S : Subgroup G)) (L ⊔ (S : Subgroup G)) := ⟨le_rfl, hL.1.2.2.2⟩
  have hLc := lemma_1_2_7_one hK hs hnab h37 h39 hT hL hH
  have hH' : InH (S : Subgroup G) (L ⊔ (S : Subgroup G)) := ⟨le_sup_right, hL.1.2.2.2⟩
  have hFH := charTwo_of_inH hK.2.1 S hH'
  exact (quasithinGenFitting_eq_pCoreOf_iff L 2).mpr
    (A4.charTwo_of_subnormal (subnormal_of_mem_cComp hLc) hFH)

theorem lemma_1_2_7_three (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    {T L : Subgroup G} (hT : quasithinIsSylowTwo T) (hL : quasithinIsMaximalLocal T L) :
    IsUniqueM (L ⊔ T) (Subgroup.normalizer (conjClosure L T : Set G)) := by
  obtain ⟨S, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  have hH₀ : pCoreOf 2 (L ⊔ (S : Subgroup G)) ≠ ⊥ := hL.1.2.2.2
  obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hH₀
  have hnorm : ∀ M : Subgroup G, InM (L ⊔ (S : Subgroup G)) M →
      M ≤ Subgroup.normalizer (conjClosure L (S : Subgroup G) : Set G) := by
    intro M hM
    have hMH : InH (L ⊔ (S : Subgroup G)) M := inH_of_inM hM
    have hTM : (S : Subgroup G) ≤ M := le_sup_right.trans hM.2
    have hLM := lemma_1_2_7_one hK hs hnab h37 h39 hT hL hMH
    exact normal_conjClosure_of_pCoreOf_ne_bot hK hs hnab h37 h38 hMH.2
      (isSylowTwoOf_of_quasithinIsSylowTwo hT hTM) hLM
  have hL₀M : conjClosure L (S : Subgroup G) ≤ M' :=
    conjClosure_le fun h hh z hz =>
      M'.mul_mem (M'.mul_mem (le_sup_right.trans hM'.2 hh) (le_sup_left.trans hM'.2 hz))
        (M'.inv_mem (le_sup_right.trans hM'.2 hh))
  have hL₀ne : conjClosure L (S : Subgroup G) ≠ ⊥ := by
    intro h
    apply ne_bot_of_mem_cComp (cComp_of_isLocal hL.1 : L ∈ cComp (L ⊔ (S : Subgroup G)))
    exact le_bot_iff.mp ((le_conjClosure L (S : Subgroup G)).trans h.le)
  have hSM' : InM (S : Subgroup G) M' := ⟨hM'.1, le_sup_right.trans hM'.2⟩
  have hFM' : CharTwo M' := charTwo_of_inH hK.2.1 S (inH_of_inM hSM')
  have hFL₀ : CharTwo (conjClosure L (S : Subgroup G)) :=
    A4.charTwo_of_subnormal (A3.subnormal_of_normal hL₀M
      (Subgroup.normal_subgroupOf_iff_le_normalizer hL₀M |>.mpr (hnorm M' hM'))) hFM'
  have hO₂ := pCoreOf_ne_bot_of_charTwo hFL₀ hL₀ne
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 (conjClosure L (S : Subgroup G)) : Set G)) :=
    ⟨_, hO₂, pCoreOf_isPGroup 2 _, rfl⟩
  have hM'le : M' ≤ Subgroup.normalizer (conjClosure L (S : Subgroup G) : Set G) := hnorm M' hM'
  have hle2 : Subgroup.normalizer (conjClosure L (S : Subgroup G) : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 (conjClosure L (S : Subgroup G)) : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 _
  have hM'eq : M' = Subgroup.normalizer (conjClosure L (S : Subgroup G) : Set G) := by
    have h1 := hM'.1.2 _ hloc (hM'le.trans hle2)
    exact le_antisymm hM'le (hle2.trans h1.le)
  refine ⟨⟨hM'eq ▸ hM'.1, hM'.2.trans hM'le⟩, fun M hM => ?_⟩
  have h1 : M ≤ M' := (hnorm M hM).trans hM'eq.ge
  exact hM.1.2 M' hM'.1.1 h1 |>.symm.trans hM'eq

end CFSG.Quasithin
