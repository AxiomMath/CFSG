module

public import CFSG.LocalAnalysis.StandardType.GGA2EightDefs
public import CFSG.LocalAnalysis.StandardType.GGL45FixA2RankSeven
public import CFSG.LocalAnalysis.StandardType.GGB36LemmaRT
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATorus
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeACover
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem a2c_aut_A2 {J : Type} [Group J] [Finite J] (hperf : commutator J = ⊤)
    (hlab : GGHasLabel ⟨.A, 2, 3⟩ (J ⧸ Subgroup.center J)) :
    ∀ E : Subgroup (MulAut J), IsElemAbelian 7 E → Nat.card E ≤ 7 ^ 2 := by
  intro E hE
  unfold GGHasLabel at hlab
  dsimp only [LargeEvenRawDatum] at hlab
  unfold LargeEvenRecipeLinear at hlab
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hlab
  have hK8 : Nat.card K = 8 := by rw [hKcard]; norm_num
  have hb := gffa2_rank_linear_seven (K := K) hK8
    (E.map (ggInducedAut e)) (TableB.isElemAbelian_map hE (ggInducedAut e))
  have hinj : Function.Injective (ggInducedAut e) :=
    ggInducedAut_injective_of_perfect hperf e
  have hcard : Nat.card (E.map (ggInducedAut e)) = Nat.card E :=
    Subgroup.card_map_of_injective hinj
  rwa [hcard] at hb

private theorem a2c_le_twoLocalRank_of_torusLift {p r s : ℕ} (hp : p.Prime)
    {G : Type} [Group G] [Finite G] {L E : Subgroup G}
    (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ s)
    (hEL : ∀ a ∈ E, ∀ l ∈ L, a * l = l * a) (hL : commutator L = ⊤)
    {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R) (hlift : GGTorusLift p r R) :
    s + r ≤ LargeEvenTwoLocalRank p G := by
  have := Fact.mk hp
  obtain ⟨U, EJ, hU, hU2, hEJU, hEJ, hEJcard, hEJker⟩ := hlift L (ggQuotHom θ)
    (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hL
  rw [ker_ggQuotHom] at hEJker
  have hEG : IsElemAbelian p (EJ.map L.subtype) := TableB.isElemAbelian_map hEJ L.subtype
  have hEX : ∀ a ∈ EJ.map L.subtype, ∀ c ∈ E, a * c = c * a := by
    rintro _ ⟨e, he, rfl⟩ c hc
    exact (hEL c hc e e.2).symm
  have hE' : IsElemAbelian p (EJ.map L.subtype ⊔ E) := TableB.isElemAbelian_sup hEG hE hEX
  have hdisj : Disjoint (EJ.map L.subtype) E := by
    rw [Subgroup.disjoint_def]
    rintro _ ⟨e, he, rfl⟩ ha
    have hec : e ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext (hEL e.1 ha l.1 l.2).symm
    have hmem : e ∈ EJ ⊓ Subgroup.center ↥L := ⟨he, hec⟩
    rw [hEJker, Subgroup.mem_bot] at hmem
    rw [hmem]
    rfl
  have hEN : E ≤ Subgroup.normalizer ((EJ.map L.subtype : Subgroup G) : Set G) := by
    intro y hy
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun g hg => by
        obtain ⟨u, -, rfl⟩ := hg
        exact (hEL y hy u u.2).symm)
  have hcard : Nat.card (EJ.map L.subtype ⊔ E : Subgroup G) = p ^ (r + s) := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hEN hdisj,
      ← Nat.card_congr (EJ.equivMapOfInjective _ L.subtype_injective).toEquiv, hEJcard, hEcard,
      ← pow_add]
  have hUne : U.map L.subtype ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective]
    exact hU
  have hTL : IsTwoLocal (Subgroup.normalizer ((U.map L.subtype : Subgroup G) : Set G)) :=
    ⟨_, hUne, hU2.map _, rfl⟩
  have hle : EJ.map L.subtype ⊔ E ≤
      Subgroup.normalizer ((U.map L.subtype : Subgroup G) : Set G) := by
    refine sup_le ((Subgroup.map_mono hEJU).trans (Subgroup.le_normalizer_map _)) ?_
    intro y hy
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun g hg => by
        obtain ⟨u, -, rfl⟩ := hg
        exact (hEL y hy u u.2).symm)
  have hbound := TableB.le_twoLocalRank hp.one_lt hTL
    (TableB.le_pRank_of_le hp.one_lt hle hE' hcard)
  omega

theorem ggA2EightAb_card_le {X : Type} [Group X] [Finite X] {A Ab : Subgroup (MulAut X)}
    {σ : MulAut X} {J : Subgroup X} {n : ℕ} {S : ℕ → LargeEvenLabel → Prop}
    (hd : GGTPNBasicB 7 n S A Ab σ J)
    (hhJ : GGHasLabel ⟨.A, 2, 3⟩ (↥J ⧸ Subgroup.center ↥J)) : Nat.card Ab ≤ 7 ^ 3 := by
  obtain ⟨hlocCore, hflat, -, hrank, -, -, -, hmarked⟩ := hd
  obtain ⟨hAbA, hσAb, -, hkerAb⟩ := hflat
  have hnormA : ∀ a ∈ A, ∀ j ∈ J, a j ∈ J := hlocCore.2.2.2.2
  have hperfJ : commutator ↥J = ⊤ := hlocCore.2.2.2.1.2.2.1
  have hAbab : IsElemAbelian 7 Ab := by
    obtain ⟨hc, hp⟩ := hlocCore.1
    haveI : IsMulCommutative A := hc
    refine ⟨⟨⟨fun u v => ?_⟩⟩, fun z hz => ?_⟩
    · apply Subtype.ext
      exact Subgroup.mul_comm_of_mem_isMulCommutative A (hAbA u.2) (hAbA v.2)
    · exact hp z (hAbA hz)
  have hnorm : ∀ a ∈ Ab, ∀ j ∈ J, a j ∈ J := fun a ha j hj => hnormA a (hAbA ha) j hj
  have hAut : ∀ E : Subgroup (MulAut ↥J), IsElemAbelian 7 E → Nat.card E ≤ 7 ^ 2 :=
    a2c_aut_A2 hperfJ hhJ
  have h := B36.card_le_of_kernel_le_zpowers (p := 7) (by norm_num) hAbab hσAb hnorm hkerAb
    (k := 2) hAut
  simpa using h

theorem ggCentJRank_a2Eight {X : Type} [Group X] [Finite X] {A Ab : Subgroup (MulAut X)}
    {σ : MulAut X} {J : Subgroup X} {n : ℕ} {S : ℕ → LargeEvenLabel → Prop}
    (hd : GGTPNBasicB 7 n S A Ab σ J)
    (hhJ : GGHasLabel ⟨.A, 2, 3⟩ (↥J ⧸ Subgroup.center ↥J)) : GGCentJRank 7 X J := by
  have hAb_le := ggA2EightAb_card_le hd hhJ
  obtain ⟨hlocCore, hflat, -, hrank, -, -, -, hmarked⟩ := hd
  have hperfJ : commutator ↥J = ⊤ := hlocCore.2.2.2.1.2.2.1
  have hlift : GGTorusLift 7 2 (↥J ⧸ Subgroup.center ↥J) := by
    unfold GGHasLabel at hhJ
    dsimp only [LargeEvenRawDatum] at hhJ
    unfold LargeEvenRecipeLinear at hhJ
    obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hhJ
    haveI : CharP K 2 := CFSG.TauCetiBridge.charP_two_of_card_eq_two_pow hKcard
    have hsec : TypeA.SLHasSections 3 K :=
      TypeA.slHasSections_of_card (d := 3) (K := K) (by norm_num) (by omega) (by omega) (by omega)
    have hproj := TypeA.ggTorusLift_coprime (p := 7) (d := 3) (K := K) (by norm_num)
      (by rw [hKcard]; norm_num) (by norm_num) (by norm_num) hsec
    exact TypeA.ggTorusLift_of_mulEquiv (e.trans (TypeA.recipeEquiv 3 K)) hproj
  intro hcop E hE hcent
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨s, hs⟩ := IsPGroup.iff_card.mp (TableB.isPGroup_of_isElemAbelian hE)
  have hmain : s + 2 ≤ LargeEvenTwoLocalRank 7 X :=
    a2c_le_twoLocalRank_of_torusLift (p := 7) (r := 2) (s := s) (by norm_num)
      hE hs hcent hperfJ (MulEquiv.refl _) hlift
  obtain ⟨m, hmcard, hmrank⟩ := hrank
  have h7 : ¬ 7 ∣ Nat.card (Subgroup.center X) :=
    (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 7)).mp hcop.symm
  have hm3 : m ≤ 3 := by
    have h : 7 ^ m ≤ 7 ^ 3 := by rw [← hmcard]; exact hAb_le
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 7)).mp h
  rw [if_neg h7] at hmrank
  have hmrank3 : LargeEvenTwoLocalRank 7 X ≤ 3 := by omega
  have hs1 : s ≤ 1 := by omega
  rw [hs]
  calc 7 ^ s ≤ 7 ^ 1 := Nat.pow_le_pow_right (by norm_num : 0 < 7) hs1
    _ = 7 := by norm_num

end CFSG.StandardType

end
