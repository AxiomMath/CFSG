module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.QuotInfBar2
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214e2
public import CFSG.LocalAnalysis.UniquenessCase.UC22S217L2Three
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rh
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Borel
import CFSG.LocalAnalysis.UniquenessCase.UC22P21a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedThree)

variable {G : Type} [Group G] [Finite G]

theorem uc22s2122np_centralizesBar_of_not_dvd {M L S : Subgroup G}
    (hL : L ∈ calC M) {a : ℕ} (hSp : IsSp4 (Bar2 L) a)
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S L) {b : G}
    (hbN : b ∈ normalizer (L : Set G)) (hbS : b ∈ normalizer (S : Set G))
    {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2) (hbs : orderOf b = s)
    (hsn : ¬ s ∣ 2 ^ a - 1)
    (hinner : inducedQuotInfAut L b hbN ∈
      (MulAut.conj : (BarInf L ⧸ center (BarInf L)) →*
        MulAut (BarInf L ⧸ center (BarInf L))).range) :
    CentralizesBar b L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact s.Prime := ⟨hs⟩
  have hZ : center (Bar2 L) = ⊥ := center_eq_bot_of_isSp4 hL.2.2 hSp
  let e := quotCenterEquivBar2 hL.2.2 hZ
  let θ := inducedQuotInfAut L b hbN
  let U := (S.subgroupOf L).map (piBarInf L)
  have hS' : CFSG.ABGLocalTools.IsSylowOf 2 (S.subgroupOf L) ⊤ := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff L,
      Subgroup.map_subgroupOf_eq_of_le hS.le]
    simpa only [Subgroup.map_top, L.range_subtype] using hS
  have hU : CFSG.ABGLocalTools.IsSylowOf 2 U ⊤ :=
    uc22p22r_isSylowOf_map_top (piBarInf_surjective L) hS'
  have hθU : U.map θ.toMonoidHom = U := by
    apply Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨y, ⟨l, hl, rfl⟩, rfl⟩
      let l' : L := ⟨b * (l : G) * b⁻¹, (mem_normalizer_iff.mp hbN l).mp l.2⟩
      have hl' : l' ∈ S.subgroupOf L :=
        mem_subgroupOf.mpr ((mem_normalizer_iff.mp hbS (l : G)).mp
          (mem_subgroupOf.mp hl))
      exact mem_map.mpr ⟨l', hl', (inducedQuotInfAut_piBarInf L b hbN l).symm⟩
    · rw [Subgroup.card_map_of_injective (f := θ.toMonoidHom) θ.injective]
  have hZX : center (BarInf L ⧸ center (BarInf L)) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    have hez : e z ∈ center (Bar2 L) :=
      Subgroup.map_center_le_center e.surjective (Subgroup.mem_map_of_mem e.toMonoidHom hz)
    rw [hZ, mem_bot] at hez
    exact e.injective (by simpa using hez)
  have hθs : θ ^ s = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one]
    simpa [θ, hbs] using orderOf_inducedQuotInfAut_dvd L hbN
  have hθ : θ = 1 := by
    by_contra hθne
    obtain ⟨x, hxN, hx1, hxs⟩ := uc22s2114_exists_of_inner hZX hθU hinner hθne hθs
    have hxo : orderOf x = s := orderOf_eq_prime hxs hx1
    have hsN : s ∣ Nat.card (normalizer (U : Set (BarInf L ⧸ center (BarInf L)))) := by
      have h := Subgroup.orderOf_dvd_natCard (normalizer (U : Set (BarInf L ⧸ center (BarInf L)))) hxN
      rwa [hxo] at h
    exact hsn (uc22p2214_borel_prime_Sp4
      (lieModel_xbar_of_lieModel_bar2 hL.2.2 hZ hSp) hU hs hs2 hsN)
  refine ⟨hbN, fun l hl => ?_⟩
  have hq := congrArg e (DFunLike.congr_fun hθ (piBarInf L ⟨l, hl⟩))
  rw [show θ = inducedQuotInfAut L b hbN from rfl,
    quotCenterEquivBar2_inducedQuotInfAut_piBarInf, MulAut.one_apply,
    quotCenterEquivBar2_piBarInf] at hq
  have hmem : (⟨b * l * b⁻¹, (mem_normalizer_iff.mp hbN l).mp hl⟩ : L) / ⟨l, hl⟩ ∈
      CFSG.pCore 2 ↥L := (QuotientGroup.eq_iff_div_mem).mp hq
  unfold CFSG.Open.pCoreOf
  apply Subgroup.mem_map.mpr
  refine ⟨(⟨b * l * b⁻¹, (mem_normalizer_iff.mp hbN l).mp hl⟩ : L) / ⟨l, hl⟩, hmem, ?_⟩
  rw [map_div, div_eq_mul_inv]
  rfl

theorem uc22s2122np_false_of_centralizesBar (hK3 : StronglyEmbeddedThree)
    {D : Data G} {Ch : Choice2011 G} (hH : H1930 D) (c : Ctx21 D Ch)
    {L : Subgroup G} (hL : L ∈ calC D.M) {a : ℕ} (hSp : IsSp4 (Bar2 L) a)
    (hM : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M)
    {b : G} (hb : b ∈ c.B0) {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2)
    (hbs : orderOf b = s) (hbL : CentralizesBar b L) : False := by
  let c₀ : Ctx21 D Ch := { c with B := c.B0, hB := c.hB0, hle := le_rfl }
  have hA : Nat.card (zpowers b) = s := by rw [Nat.card_zpowers, hbs]
  have hAM : zpowers b ≤ D.M := zpowers_le.mpr (c.hBM hb)
  have hY : (L ⊓ centralizer ((zpowers b : Subgroup G) : Set G)) ⊔ pCoreOf 2 L = L :=
    uc22p21d_sup_pCore_eq hs hs2 hA
      (fun g hg => uc22p21d_centralizesBar_of_mem_zpowers hbL hg)
  have hL3 : 2 ≤ CFSG.Open.pRank 3 L :=
    uc22p2214_two_le_pRank_of_surj (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
      (QuotientGroup.mk'_surjective _) Nat.prime_three (by norm_num)
      (uc22p2214_two_le_pRank_sp4 hSp)
  exact s21_2 D Ch hH c₀ (zpowers b) (zpowers_le.mpr hb)
    (uc22s217l2t_normalizer_le_of_strongThree D.standing.simple D.standing.kProper
      hK3 hM hL.1.le hL.2.1 hL3 hs hAM hA hY)

end CFSG.LocalAnalysis.UniquenessCase.UC22
