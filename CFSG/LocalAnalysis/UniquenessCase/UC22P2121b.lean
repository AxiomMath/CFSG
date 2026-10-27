module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2121a
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst
import CFSG.LocalAnalysis.UniquenessCase.UC22P21c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)

variable {G : Type} [Group G] [Finite G]

theorem uc22p2121b_pRank_le_iInf_ker_add_sum {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {ι : Type*} {H : ι → Type*} [∀ i, Group (H i)] [∀ i, Finite (H i)] (f : ∀ i, X →* H i)
    (R : Subgroup X) (s : Finset ι) :
    CFSG.Open.pRank p R ≤
      CFSG.Open.pRank p (R ⊓ ⨅ i ∈ s, (f i).ker) + ∑ i ∈ s, CFSG.Open.pRank p (R.map (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.iInf_insert]
    have h1 := CFSG.AGLEmbedding.pRank_le_pRank_inf_ker_add_pRank_map hp (f a) (R ⊓ ⨅ i ∈ s, (f i).ker)
    have h2 := CFSG.SectionRank.pRank_mono hp.one_lt
      (show (R ⊓ ⨅ i ∈ s, (f i).ker) ⊓ (f a).ker ≤ R ⊓ ((f a).ker ⊓ ⨅ i ∈ s, (f i).ker) from
        le_inf (inf_le_left.trans inf_le_left) (le_inf inf_le_right (inf_le_left.trans inf_le_right)))
    have h3 := CFSG.SectionRank.pRank_mono hp.one_lt
      (Subgroup.map_mono (f := f a) (inf_le_left : R ⊓ ⨅ i ∈ s, (f i).ker ≤ R))
    omega

theorem uc22p2121b_pRank_le_centE_add_sum (M : Subgroup G) {p : ℕ} (hp : p.Prime)
    (s : Finset (Subgroup (Bar2 M))) (hsN : ∀ C ∈ s, C.Normal) (hs : ∀ C, CFSG.IsComponent C → C ∈ s) :
    CFSG.Open.pRank p M ≤ CFSG.Open.pRank p (barPreimage M (centE M)) +
      ∑ C ∈ s, CFSG.Open.pRank p (Subgroup.normalizerMonoidHom C).range := by
  have hnorm : ∀ i : {C // C ∈ s}, ∀ y : ↥M, uc22p21cPi M y ∈ normalizer ((i.1 : Subgroup (Bar2 M)) : Set (Bar2 M)) :=
    fun i y => by
      haveI := hsN i.1 i.2
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top _
  let f : ∀ i : {C // C ∈ s}, ↥M →* MulAut ↥i.1 := fun i =>
    (Subgroup.normalizerMonoidHom i.1).comp ((uc22p21cPi M).codRestrict _ (hnorm i))
  have hgen := uc22p2121b_pRank_le_iInf_ker_add_sum hp f ⊤ s.attach
  have hcent : ∀ x : ↥M, x ∈ (⊤ ⊓ ⨅ i ∈ s.attach, (f i).ker : Subgroup ↥M) → uc22p21cPi M x ∈ centE M := by
    intro x hx
    have hxC : ∀ C ∈ s, uc22p21cPi M x ∈ centralizer (C : Set (Bar2 M)) := fun C hC => by
      have hx' : x ∈ (f ⟨C, hC⟩).ker :=
        Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx.2 ⟨C, hC⟩) (Finset.mem_attach _ _)
      rw [MonoidHom.mem_ker] at hx'
      have hx'' : (uc22p21cPi M).codRestrict _ (hnorm ⟨C, hC⟩) x ∈ (Subgroup.normalizerMonoidHom C).ker :=
        MonoidHom.mem_ker.2 hx'
      rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf, MonoidHom.codRestrict_apply] at hx''
      exact hx''
    have hz : Subgroup.zpowers (uc22p21cPi M x) ≤ centralizer (CFSG.layer (Bar2 M) : Set (Bar2 M)) := by
      rw [Subgroup.le_centralizer_iff, CFSG.layer.eq_sSup]
      refine sSup_le fun K hK => ?_
      rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
      exact hxC K (hs K hK)
    exact hz (Subgroup.mem_zpowers _)
  have hker : CFSG.Open.pRank p (⊤ ⊓ ⨅ i ∈ s.attach, (f i).ker : Subgroup ↥M) ≤
      CFSG.Open.pRank p (barPreimage M (centE M)) := by
    refine (CFSG.SectionRank.pRank_le_map hp.one_lt M.subtype M.subtype_injective _).trans
      (CFSG.SectionRank.pRank_mono hp.one_lt ?_)
    unfold barPreimage
    exact Subgroup.map_mono fun x hx => hcent x hx
  have hmap : ∀ i : {C // C ∈ s}, CFSG.Open.pRank p ((⊤ : Subgroup ↥M).map (f i)) ≤
      CFSG.Open.pRank p (Subgroup.normalizerMonoidHom i.1).range := fun i =>
    CFSG.SectionRank.pRank_mono hp.one_lt (by
      rintro _ ⟨x, -, rfl⟩
      exact MonoidHom.mem_range.2 ⟨_, rfl⟩)
  have hsum : ∑ i ∈ s.attach, CFSG.Open.pRank p ((⊤ : Subgroup ↥M).map (f i)) ≤
      ∑ C ∈ s, CFSG.Open.pRank p (Subgroup.normalizerMonoidHom C).range :=
    (Finset.sum_le_sum fun i _ => hmap i).trans_eq
      (Finset.sum_attach s fun C => CFSG.Open.pRank p (Subgroup.normalizerMonoidHom C).range)
  have htop : CFSG.Open.pRank p M = CFSG.Open.pRank p (⊤ : Subgroup ↥M) :=
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup M
  omega

theorem uc22p2121b_normal_of_hyp2120 {D : Data G} {Ch : Choice2011 G} {c : Ctx21 D Ch} (hH : Hyp2120 D c)
    {C : Subgroup (Bar2 D.M)} (hC : CFSG.IsComponent C) : C.Normal := by
  obtain ⟨-, h2, -, -⟩ := hH
  obtain ⟨L, hL, rfl⟩ := uc22p21c_exists_calC_of_component D.M hC
  exact (h2 L hL).1.map _ (QuotientGroup.mk'_surjective _)

theorem uc22p2121b_pRank_le_one_add_sum {D : Data G} {Ch : Choice2011 G} (h61 : UC6.R6_1 D) (c : Ctx21 D Ch)
    (hH : Hyp2120 D c) {p : ℕ} (hp : p ∈ D.sig) (s : Finset (Subgroup (Bar2 D.M)))
    (hs : ∀ C, C ∈ s ↔ CFSG.IsComponent C) :
    CFSG.Open.pRank p D.M ≤ 1 + ∑ C ∈ s, CFSG.Open.pRank p (Subgroup.normalizerMonoidHom C).range := by
  have h1 := uc22p2121_pRank_centE_le_one h61 c hH hp
  have h2 := uc22p2121b_pRank_le_centE_add_sum D.M (D.sig_prime p hp).1 s
    (fun C hC => uc22p2121b_normal_of_hyp2120 hH ((hs C).1 hC)) fun C hC => (hs C).2 hC
  omega

theorem uc22p2121b_three_le_sum_setup4 (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    {Ch : Choice2011 G} (c : Ctx21 (UC6.dataOfSetup4 hS hU S) Ch) (hH : Hyp2120 (UC6.dataOfSetup4 hS hU S) c)
    {p : ℕ} (hp : p ∈ (UC6.dataOfSetup4 hS hU S).sig)
    (s : Finset (Subgroup (Bar2 (UC6.dataOfSetup4 hS hU S).M))) (hs : ∀ C, C ∈ s ↔ CFSG.IsComponent C) :
    3 ≤ ∑ C ∈ s, CFSG.Open.pRank p (Subgroup.normalizerMonoidHom C).range := by
  have h4 : 4 ≤ CFSG.Open.pRank p (UC6.dataOfSetup4 hS hU S).M := UC6.four_le_pRank_of_sigma hp
  have h := uc22p2121b_pRank_le_one_add_sum (UC6.r6_1_dataOfSetup4 hS hU S) c hH hp s hs
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
