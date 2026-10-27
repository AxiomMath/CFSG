module

public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofThreeFive
public import CFSG.RankThree.PartTwo.KFacts.K426J3
public import CFSG.RankThree.PartTwo.KFacts.K426RestMcL
public import CFSG.Sporadic.ON
public import CFSG.Sporadic.McL.Simple
import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofA9
public import CFSG.RankThree.PartTwo.Sec21.Item22Res4ProofNarrow

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Blueprint

@[expose] def sporadicsData228 : List TauCeti.SporadicName := [.M11, .M12, .J2, .J3, .McL, .ONan]

@[expose] def Census228SporData : Prop :=
  ∀ s ∈ sporadicsData228, ThreeFiveData228 (NativeSporadic.Carrier s)

namespace Item228CensusProof

theorem census228Fact_of_simple {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hnp : ¬ (Nat.card S).Prime) (hL : L2Order228 S) (h : ThreeFiveData228 S) :
    Census228Fact S := by
  have hZ := Item223CensusProof.center_eq_bot_of_isSimpleGroup hnp
  refine Or.inr (noL2Normal228_of_threeFive (MonoidHom.id S) Function.surjective_id ?_ ?_ hL h)
  · rw [MonoidHom.ker_id, hZ]
  · rw [hZ, Subgroup.card_bot]
    exact one_dvd 3

theorem exists_surjective_hom_of_isExtOf {Y T : Type} [Group Y] [Group T] [Group.IsPerfect T]
    (hZT : Subgroup.center T = ⊥) (h : Sec4.IsExtOf Y T (Multiplicative (ZMod 3))) :
    ∃ f : Y →* T, Function.Surjective f ∧ f.ker = Subgroup.center Y ∧
      Nat.card (Subgroup.center Y) = 3 := by
  obtain ⟨K, hK, ⟨eK⟩, ⟨eQ⟩⟩ := h
  have h3 : Nat.card K = 3 := by
    rw [Nat.card_congr eK.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card]
  have : Group.IsPerfect (Y ⧸ K) := Group.IsPerfect.ofSurjective (f := eQ.symm.toMonoidHom)
    eQ.symm.surjective
  have hKZ : K ≤ Subgroup.center Y := Item223CensusProof.le_center_of_card_eq_three h3
  set f : Y →* T := eQ.toMonoidHom.comp (QuotientGroup.mk' K) with hf
  have hfs : Function.Surjective f :=
    eQ.surjective.comp (QuotientGroup.mk'_surjective K)
  have hker : f.ker = K := by
    ext z
    rw [MonoidHom.mem_ker, hf, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hZK : Subgroup.center Y ≤ K := by
    intro z hz
    rw [← hker, MonoidHom.mem_ker]
    have : f z ∈ Subgroup.center T := by
      rw [Subgroup.mem_center_iff]
      intro t
      obtain ⟨w, rfl⟩ := hfs t
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz w)]
    rwa [hZT, Subgroup.mem_bot] at this
  have hKeq : K = Subgroup.center Y := le_antisymm hKZ hZK
  exact ⟨f, hfs, hker.trans hKeq, hKeq ▸ h3⟩

theorem census228Fact_of_cover {Y S : Type} [Group Y] [Finite Y] [Group S] [Finite S]
    [IsSimpleGroup S] (hnp : ¬ (Nat.card S).Prime) (hL : L2Order228 S) (h : ThreeFiveData228 S)
    (hY : Sec4.IsExtOf Y S (Multiplicative (ZMod 3))) : Census228Fact Y := by
  have hZ := Item223CensusProof.center_eq_bot_of_isSimpleGroup hnp
  have : Nontrivial S := IsSimpleGroup.toNontrivial
  obtain ⟨a, b, hab⟩ := Item22Res4Proof.exists_ne_comm_of_center_eq_bot hZ
  have : Group.IsPerfect S := Item22Res4Proof.isPerfect_of_simple hab
  obtain ⟨f, hfs, hker, h3⟩ := exists_surjective_hom_of_isExtOf hZ hY
  exact Or.inr (noL2Normal228_of_threeFive f hfs hker (by rw [h3]) hL h)

set_option maxRecDepth 20000 in
theorem card_centralizer_j3P {x : Equiv.Perm (Fin 6156)}
    (hx : x ∈ CFSG.Sporadic.Schreier.j3P) (hxo : orderOf x = 3) :
    Nat.card (Subgroup.centralizer {x} ⊓ CFSG.Sporadic.Schreier.j3P :
        Subgroup (Equiv.Perm (Fin 6156))) = 1080 ∨
      Nat.card (Subgroup.centralizer {x} ⊓ CFSG.Sporadic.Schreier.j3P :
        Subgroup (Equiv.Perm (Fin 6156))) = 243 := by
  obtain ⟨k, hk, c, hc, e, he, rfl⟩ := KFacts.K426.j3t_fusion hx hxo
  have hA3 : KFacts.K426.j3tXA ^ 3 = 1 := (KFacts.K426.j3tReps_spec (c := 0) (by norm_num)).2
  have hB3 : KFacts.K426.j3tXB ^ 3 = 1 := (KFacts.K426.j3tReps_spec (c := 1) (by norm_num)).2
  rcases hc with rfl | rfl
  · left
    rw [KFacts.K426Rest.card_centralizer_conj hk hA3 he, ← KFacts.K426.j3t_caseA.1]
    exact KFacts.K426.j3t_caseA.2
  · right
    rw [KFacts.K426Rest.card_centralizer_conj hk hB3 he, ← KFacts.K426.j3t_caseB.1]
    exact KFacts.K426.j3t_caseB.2

noncomputable def j3CarrierEquiv :
    NativeSporadic.Carrier .J3 ≃* CFSG.Sporadic.Schreier.j3P :=
  CFSG.Sporadic.Schreier.j3PermEquiv

theorem j3ThreeCentralizerCard (x : NativeSporadic.Carrier .J3) (hx : orderOf x = 3) :
    Nat.card (Subgroup.centralizer ({x} : Set (NativeSporadic.Carrier .J3))) = 1080 ∨
      Nat.card (Subgroup.centralizer ({x} : Set (NativeSporadic.Carrier .J3))) = 243 := by
  have h := KFacts.K426Rest.card_centralizer_of_mulEquiv j3CarrierEquiv x
  have hXo : orderOf ((j3CarrierEquiv x : CFSG.Sporadic.Schreier.j3P) :
      Equiv.Perm (Fin 6156)) = 3 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hx
  rcases card_centralizer_j3P (j3CarrierEquiv x).2 hXo with h1 | h1
  · exact Or.inl (h.trans h1)
  · exact Or.inr (h.trans h1)

theorem l2Order228_J3 : L2Order228 (NativeSporadic.Carrier .J3) := by
  refine l2Order228_of_centralizer fun x hx => ?_
  rcases j3ThreeCentralizerCard x hx with h | h <;> rw [h] <;> norm_num

end Item228CensusProof

open Item228CensusProof

theorem census228SporRest_of
    (h : Census228SporData) : Census228SporRest := by
  have hM11 := h .M11 (by simp [sporadicsData228])
  have hM12 := h .M12 (by simp [sporadicsData228])
  have hJ2 := h .J2 (by simp [sporadicsData228])
  have hJ3 := h .J3 (by simp [sporadicsData228])
  have hMcL := h .McL (by simp [sporadicsData228])
  have hON := h .ONan (by simp [sporadicsData228])
  have sM11 := CFSG.Sporadic.Mathieu.fam_m11_simplicity
  have sM12 := CFSG.Sporadic.Mathieu.fam_m12_simplicity
  have sJ2 := CFSG.Sporadic.J2.fam_j2_simplicity
  have sJ3 := CFSG.Sporadic.J3.fam_j3_simplicity
  have sMcL := CFSG.Sporadic.McL.fam_mcl_simplicity
  have sON := CFSG.Sporadic.ON.fam_on_simplicity
  have : Finite (NativeSporadic.Carrier .M11) := sM11.1
  have : IsSimpleGroup (NativeSporadic.Carrier .M11) := sM11.2.2
  have : Finite (NativeSporadic.Carrier .M12) := sM12.1
  have : IsSimpleGroup (NativeSporadic.Carrier .M12) := sM12.2.2
  have : Finite (NativeSporadic.Carrier .J2) := sJ2.1
  have : IsSimpleGroup (NativeSporadic.Carrier .J2) := sJ2.2.2
  have : Finite (NativeSporadic.Carrier .J3) := sJ3.1
  have : IsSimpleGroup (NativeSporadic.Carrier .J3) := sJ3.2.2
  have : Finite (NativeSporadic.Carrier .McL) := sMcL.1
  have : IsSimpleGroup (NativeSporadic.Carrier .McL) := sMcL.2.2
  have : Finite (NativeSporadic.Carrier .ONan) := sON.1
  have : IsSimpleGroup (NativeSporadic.Carrier .ONan) := sON.2.2
  have cM11 : Nat.card (NativeSporadic.Carrier .M11) = 7920 := CFSG.Sporadic.Mathieu.card_M11
  have cM12 : Nat.card (NativeSporadic.Carrier .M12) = 95040 := CFSG.Sporadic.Mathieu.card_M12
  have cJ2 : Nat.card (NativeSporadic.Carrier .J2) = 604800 := CFSG.Sporadic.J2.card_J2
  have cJ3 : Nat.card (NativeSporadic.Carrier .J3) = 50232960 := CFSG.Sporadic.J3.card_J3
  have cMcL : Nat.card (NativeSporadic.Carrier .McL) = 898128000 := CFSG.Sporadic.McL.card_McL
  have cON : Nat.card (NativeSporadic.Carrier .ONan) = 460815505920 := CFSG.Sporadic.ON.card_ON
  have lM11 : L2Order228 (NativeSporadic.Carrier .M11) :=
    l2Order228_of_card (by rw [cM11]; norm_num) (by rw [cM11]; norm_num) (by rw [cM11]; norm_num)
  have lM12 : L2Order228 (NativeSporadic.Carrier .M12) :=
    l2Order228_of_card (by rw [cM12]; norm_num) (by rw [cM12]; norm_num) (by rw [cM12]; norm_num)
  have lJ2 : L2Order228 (NativeSporadic.Carrier .J2) :=
    l2Order228_of_card (by rw [cJ2]; norm_num) (by rw [cJ2]; norm_num) (by rw [cJ2]; norm_num)
  have lMcL : L2Order228 (NativeSporadic.Carrier .McL) :=
    l2Order228_of_card (by rw [cMcL]; norm_num) (by rw [cMcL]; norm_num) (by rw [cMcL]; norm_num)
  have lON : L2Order228 (NativeSporadic.Carrier .ONan) :=
    l2Order228_of_card (by rw [cON]; norm_num) (by rw [cON]; norm_num) (by rw [cON]; norm_num)
  refine ⟨fun s hs => ?_, fun s hs Y _ _ hY => ?_⟩
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact census228Fact_of_simple (S := NativeSporadic.Carrier .M11) (by rw [cM11]; norm_num)
        lM11 hM11
    · exact census228Fact_of_simple (S := NativeSporadic.Carrier .M12) (by rw [cM12]; norm_num)
        lM12 hM12
    · exact census228Fact_of_simple (S := NativeSporadic.Carrier .J2) (by rw [cJ2]; norm_num)
        lJ2 hJ2
    · exact census228Fact_of_simple (S := NativeSporadic.Carrier .J3) (by rw [cJ3]; norm_num)
        l2Order228_J3 hJ3
    · exact census228Fact_of_simple (S := NativeSporadic.Carrier .McL) (by rw [cMcL]; norm_num)
        lMcL hMcL
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact census228Fact_of_cover (S := NativeSporadic.Carrier .J3) (by rw [cJ3]; norm_num)
        l2Order228_J3 hJ3 hY
    · exact census228Fact_of_cover (S := NativeSporadic.Carrier .McL) (by rw [cMcL]; norm_num)
        lMcL hMcL hY
    · exact census228Fact_of_cover (S := NativeSporadic.Carrier .ONan) (by rw [cON]; norm_num)
        lON hON hY

end CFSG.RankThree.PartTwo.Sec21
