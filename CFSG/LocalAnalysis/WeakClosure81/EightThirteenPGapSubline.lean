module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapF4Data
public import Certificates.Certificate43
import CFSG.GroupTheory.AlternatingFive.SylowTwo
public import CFSG.CGT.Timmesfeld75.Cfg214Gen
public import CFSG.LargeExtraspecial.S9TIXC
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPShape
public import CFSG.LocalAnalysis.WeakClosure81.SevenFour
public import CFSG.LocalAnalysis.WeakClosure81.SevenKGen
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2)

private theorem wcgapsl_card_of_isL2 {X : Type} [Group X]
    (h : IsL2 X 2) : Nat.card X = 60 := by
  obtain ⟨e⟩ := CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model X h
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  norm_num

private theorem wcgapsl_isSimpleGroup_of_isL2 {X : Type} [Group X]
    (h : IsL2 X 2) : IsSimpleGroup X := by
  obtain ⟨e⟩ := CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model X h
  exact e.isSimpleGroup

private theorem wcgapsl_factorization_60_two : Nat.factorization 60 2 = 2 := by
  rw [show (60 : ℕ) = 2 ^ 2 * 15 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization Nat.prime_two,
    Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  rfl

private theorem wcgapsl_oTwoMod_bot_eq_bot {Y : Type} [Group Y] [Finite Y] (L : Subgroup Y)
    (hsimple : IsSimpleGroup ↥L) (hcard : Nat.card ↥L = 60) :
    oTwoMod (⊥ : Subgroup Y) L = ⊥ := by
  rw [oTwoMod]
  refine le_antisymm (iSup₂_le fun W hW => ?_) bot_le
  have hWL : W ≤ L := hW.2.1
  have hWnorm : (W.subgroupOf L).Normal := hW.2.2.1
  have hW2 : IsPGroup 2 W := by
    intro w
    obtain ⟨k, hk⟩ := hW.2.2.2 (w : Y) w.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  haveI := hWnorm
  rcases hsimple.eq_bot_or_eq_top_of_normal (W.subgroupOf L) with h | h
  · rw [← Subgroup.map_subgroupOf_eq_of_le hWL, h, Subgroup.map_bot]
  · exfalso
    have hWL' : W = L := by
      have h1 : W = (⊤ : Subgroup ↥L).map L.subtype := by
        rw [← Subgroup.map_subgroupOf_eq_of_le hWL, h]
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
      exact h1
    have hPL : IsPGroup 2 ↥L := hWL' ▸ hW2
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥L)).mp hPL
    rw [hcard] at hn
    have h3 : 3 ∣ 2 ^ n := by rw [← hn]; norm_num
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

private theorem wcgapsl_hasQuotShape_of_oTwoMod_eq_bot {Y : Type} [Group Y] {L : Subgroup Y}
    (hL2 : IsL2 ↥L 2) (h : oTwoMod (⊥ : Subgroup Y) L = ⊥) :
    HasQuotShape L (oTwoMod (⊥ : Subgroup Y) L : Set Y) (fun X _ => IsL2 X 2) := by
  rw [h]
  refine ⟨↥L, inferInstance, MonoidHom.id ↥L, fun x => ⟨x, rfl⟩, ?_, hL2⟩
  intro k
  show MonoidHom.id ↥L k = 1 ↔ (k : Y) ∈ (⊥ : Subgroup Y)
  rw [Subgroup.mem_bot]
  exact Subtype.ext_iff

private theorem wcgapsl_relIndex_normalizer_eq_five
    {Y : Type} [Group Y] [Finite Y] {L S : Subgroup Y} (hL2 : IsL2 ↥L 2)
    (hSL : S ≤ L) (hP : IsPGroup 2 (S.subgroupOf L))
    (hnd : ¬ 2 ∣ (S.subgroupOf L).index) :
    (L ⊓ normalizer (S : Set Y)).relIndex L = 5 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model ↥L hL2
  have hB : (L ⊓ normalizer (S : Set Y)).subgroupOf L =
      Subgroup.normalizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    rw [Subgroup.inf_subgroupOf_left, Subgroup.subgroupOf_normalizer_eq hSL]
  rw [Subgroup.relIndex, hB]
  have hmap : (Subgroup.normalizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L)).map
        e.toMonoidHom =
      Subgroup.normalizer (((S.subgroupOf L).map e.toMonoidHom :
        Subgroup (alternatingGroup (Fin 5))) : Set (alternatingGroup (Fin 5))) :=
    Subgroup.map_equiv_normalizer_eq (S.subgroupOf L) e
  have hstep : (Subgroup.normalizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L)).index =
      (Subgroup.normalizer (((S.subgroupOf L).map e.toMonoidHom :
        Subgroup (alternatingGroup (Fin 5))) : Set (alternatingGroup (Fin 5)))).index := by
    calc (Subgroup.normalizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L)).index
        = ((Subgroup.normalizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L)).map
            e.toMonoidHom).index :=
          (Subgroup.index_map_equiv
            (Subgroup.normalizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L)) e).symm
      _ = _ := by rw [hmap]
  rw [hstep]
  let P'' : Sylow 2 (alternatingGroup (Fin 5)) :=
    (hP.map e.toMonoidHom).toSylow (Subgroup.index_map_equiv (S.subgroupOf L) e ▸ hnd)
  have hcoe : (P'' : Subgroup (alternatingGroup (Fin 5))) =
      (S.subgroupOf L).map e.toMonoidHom := IsPGroup.toSylow_coe _ _
  have hstep2 : (Subgroup.normalizer (((S.subgroupOf L).map e.toMonoidHom :
        Subgroup (alternatingGroup (Fin 5))) : Set (alternatingGroup (Fin 5)))).index =
      (Subgroup.normalizer (P'' : Set (alternatingGroup (Fin 5)))).index :=
    congrArg (fun H : Subgroup (alternatingGroup (Fin 5)) =>
      (Subgroup.normalizer (H : Set (alternatingGroup (Fin 5)))).index) hcoe.symm
  rw [hstep2]
  have hcardN : Nat.card ↥(Subgroup.normalizer (P'' : Set (alternatingGroup (Fin 5)))) = 12 :=
    CFSG.GroupTheory.AlternatingFive.card_normalizer_sylow_two P''
  have hcardA : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hmul := Subgroup.card_mul_index
    (Subgroup.normalizer (P'' : Set (alternatingGroup (Fin 5))))
  rw [hcardN, hcardA] at hmul
  omega

theorem centralKData_of_subline {G : Type} [Group G] [Finite G]
    {S K : Subgroup G} (hS : IsSylowIn 2 S (⊤ : Subgroup G)) (hK : IsL2 ↥K 2)
    (hZ : Nat.card ↥(S ⊓ centralizer (S : Set G)) = 4)
    (hZK : S ⊓ centralizer (S : Set G) ≤ K)
    (hN : normalizer ((S ⊓ centralizer (S : Set G) : Subgroup G) : Set G) ≤
      normalizer (S : Set G)) :
    CentralKData S (S ⊓ centralizer (S : Set G)) := by
  classical
  set A : Subgroup G := S ⊓ centralizer (S : Set G) with hA
  have hcardK : Nat.card ↥K = 60 := wcgapsl_card_of_isL2 hK
  have hsimpleK : IsSimpleGroup ↥K := wcgapsl_isSimpleGroup_of_isL2 hK
  have hO2 : oTwoMod (⊥ : Subgroup G) K = ⊥ :=
    wcgapsl_oTwoMod_bot_eq_bot K hsimpleK hcardK
  have hshape : HasQuotShape K (oTwoMod (⊥ : Subgroup G) K : Set G)
      (fun X _ => IsL2 X 2) :=
    wcgapsl_hasQuotShape_of_oTwoMod_eq_bot hK hO2
  have hnotA : ¬ A ≤ oTwoMod (⊥ : Subgroup G) K := by
    intro hle
    rw [hO2] at hle
    have hAbot : A = ⊥ := le_antisymm hle bot_le
    have h1 : Nat.card ↥A = 1 := by rw [hAbot]; exact Subgroup.card_bot
    omega
  have hSK2 : IsPGroup 2 ↥(S ⊓ K) :=
    hS.isPGroup.of_injective (Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion_injective inf_le_left)
  have hSK2K : IsPGroup 2 ↥((S ⊓ K).subgroupOf K) :=
    hSK2.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  obtain ⟨Q, hQle⟩ := hSK2K.exists_le_sylow
  have hQcard : Nat.card ↥Q = 4 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hmult : Nat.card ↥Q = 2 ^ (Nat.card ↥K).factorization 2 :=
      Sylow.card_eq_multiplicity Q
    rw [hmult, hcardK, wcgapsl_factorization_60_two]
    norm_num
  have hbound : Nat.card ↥(S ⊓ K) ≤ 4 := by
    calc Nat.card ↥(S ⊓ K)
        = Nat.card ↥((S ⊓ K).subgroupOf K) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm
      _ ≤ Nat.card ↥Q :=
          Finite.card_le_of_embedding
            ⟨fun x => Subgroup.inclusion hQle x, Subgroup.inclusion_injective hQle⟩
      _ = 4 := hQcard
  have hAeq : A = S ⊓ K :=
    Subgroup.eq_of_le_of_card_ge (le_inf inf_le_left hZK) (by rw [hZ]; exact hbound)
  have hSKeq : S ⊓ K = A := hAeq.symm
  have hcard_AK : Nat.card ↥(A.subgroupOf K) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZK).toEquiv, hZ]
  have hnd : ¬ 2 ∣ (A.subgroupOf K).index := by
    have hmul := Subgroup.card_mul_index (A.subgroupOf K)
    rw [hcard_AK, hcardK] at hmul
    have hidx : (A.subgroupOf K).index = 15 := by omega
    rw [hidx]
    norm_num
  have hPA : IsPGroup 2 ↥(A.subgroupOf K) := by rw [hAeq]; exact hSK2K
  have hsyl : IsSylowIn 2 (S ⊓ K) K := by
    refine ⟨inf_le_right, hSK2, ?_⟩
    show ¬ 2 ∣ ((S ⊓ K).subgroupOf K).index
    have hsub : (S ⊓ K).subgroupOf K = A.subgroupOf K := by rw [← hSKeq]
    rw [hsub]
    exact hnd
  have hNA : K ⊓ normalizer (S : Set G) = K ⊓ normalizer (A : Set G) := by
    refine le_antisymm ?_ ?_
    · intro g hg
      obtain ⟨hgK, hgS⟩ := Subgroup.mem_inf.mp hg
      have hgNK : g ∈ normalizer (K : Set G) := Subgroup.le_normalizer hgK
      have hgN : g ∈ normalizer ((K ⊓ S : Subgroup G) : Set G) :=
        Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.mpr ⟨hgNK, hgS⟩)
      have hKSA : K ⊓ S = A := by rw [inf_comm]; exact hSKeq
      rw [hKSA] at hgN
      exact Subgroup.mem_inf.mpr ⟨hgK, hgN⟩
    · intro g hg
      obtain ⟨hgK, hgA⟩ := Subgroup.mem_inf.mp hg
      exact Subgroup.mem_inf.mpr ⟨hgK, hN hgA⟩
  have hidx : (K ⊓ ((⊤ : Subgroup G) ⊓ normalizer (S : Set G))).relIndex K = 5 := by
    rw [top_inf_eq, hNA]
    exact wcgapsl_relIndex_normalizer_eq_five hK hZK hPA hnd
  exact ⟨K, hZK, hnotA, hshape, hsyl, hidx⟩

end CFSG.LocalAnalysis.WeakClosure81

end
