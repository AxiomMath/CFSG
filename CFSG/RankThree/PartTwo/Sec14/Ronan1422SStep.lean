module

public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SMain
public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SJ3
public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SSp48
public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SFus
public import CFSG.RankThree.PartTwo.Sec14.Item1418Res2ProofDefs

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSp)

variable {G : Type} [Group G] [Finite G]

section KP4Syl


namespace Cfg

variable {A L R S J : Subgroup G} {c : G}
  [(ker148 A (Subgroup.normalizer (S : Set G))).Normal]

theorem false_of_Sp48 (hKF : KF1422Sp48) (hA6 : KF1422AutA6) (h : Cfg A c L R S J)
    (hJ : Nonempty (↥(img148 A (Subgroup.normalizer (S : Set G)) J) ≃*
      projSp 2 (GaloisField 2 3))) : False := by
  obtain ⟨ψ⟩ := hJ
  have hA : IsE27 A := h.pt.std.isE27
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨P, N, hAP, hP3, hNP, hNn, hidx, hcN, hBN, hNc, hP27, hΩ, htr⟩ :=
    h.exists_fusion_data_Sp48 hKF ψ
  obtain ⟨g, hg⟩ := exists_inverting_of_fusion h.pt.four.isSimpleGroup h.pt.four.nonabelian
    hAc hA.1.2 h.pt.mem_A h.c_ne_one inf_le_left (fun hc => h.pt.not_mem hc.2) hAP hP3 hNP hNn
    hidx hcN hBN hNc hP27 hΩ htr (fun Q hQ hAQ hQN => h.pt.eq_of_isPGroup_three hQ hAQ hQN)
  exact h.false_of_inverting_Sp48 hKF hA6 ψ hg

end Cfg

end KP4Syl

section KP4


variable {A L R : Subgroup G} {c : G}

theorem Pt.normalizer_ne_top_of_fam (h : Pt A c L) (hR : R ∈ scriptQPiStar A (lB A) L (piOf 2))
    {K S : Subgroup G} (hS : S ∈ fam A c R K) : Subgroup.normalizer (S : Set G) ≠ ⊤ := by
  obtain ⟨hS2, -, hRS, -⟩ := fam_facts hS
  have hRne : R ≠ ⊥ := by
    intro hR0
    have h16 := (h.R_kp4 hR).2.1
    rw [hR0, Subgroup.card_bot] at h16
    norm_num at h16
  have hSne : S ≠ ⊥ := fun hS0 => hRne (le_bot_iff.mp (hS0 ▸ hRS))
  intro htop
  have hSn : S.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  have hsimple : IsSimpleGroup G := h.std.isSimpleGroup
  rcases hSn.eq_bot_or_eq_top with h1 | h1
  · exact hSne h1
  · obtain ⟨a, b, hab⟩ := h.std.nonabelian
    have hG2 : IsPGroup 2 G := by
      have h2 := hS2
      rw [h1] at h2
      exact h2.of_equiv Subgroup.topEquiv
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Nontrivial G := hsimple.toNontrivial
    have hZ := hG2.center_nontrivial
    have hZtop : Subgroup.center G = ⊤ := by
      rcases (Subgroup.center G).normal_of_characteristic.eq_bot_or_eq_top with h0 | h0
      · exfalso
        obtain ⟨⟨z, hz⟩, ⟨w, hw⟩, hzw⟩ := hZ
        have hz1 : z = 1 := by rw [h0] at hz; exact hz
        have hw1 : w = 1 := by rw [h0] at hw; exact hw
        exact hzw (Subtype.ext (hz1.trans hw1.symm))
      · exact h0
    have ha : a ∈ Subgroup.center G := hZtop ▸ Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.mp ha b).symm)

end KP4

theorem step1422SIQR_of
    (h431 : Sec4.Ronan431.Item4_31List42) (hCL : F135Last.ComponentList42)
    (hA6 : KF1422AutA6) (hA9 : KF1422A9Sp6) (hJ3 : KF1422J3) (hGL : KF1422GL42)
    (hSp : KF1422Sp48) (h1413 : Item1413CR) (h135 : Item135) (h142 : Concl142S14)
    (hbot : Item145BotS14) (h131 : Item131) (h48 : Sec4.Item4_8) (h45 : Sec4.Item4_5) :
    Step1422SIQR := by
  intro G _ _ A c₀ L₀ hR hfail c hcΓ L hL hM hWB hTr hΩ hIQ R hRmem
  have hpt : Pt A c L := pt_of h1413 h135 h142 hbot h131 hR hfail hcΓ hL hM hWB hTr hΩ hIQ
  obtain ⟨S, hRS, hSmax⟩ := Finite.exists_le_maximal
    (p := (· ∈ fam A c R (L ⊓ Subgroup.normalizer (R : Set G)))) (hpt.mem_fam_R hRmem)
  have hSmem : S ∈ fam A c R (L ⊓ Subgroup.normalizer (R : Set G)) := hSmax.1
  obtain ⟨-, hAS, -, hKS⟩ := fam_facts hSmem
  have hM4 : SectionFourHyp ↥(Subgroup.normalizer (S : Set G)) :=
    hpt.four.sectionFourHyp (hpt.normalizer_ne_top_of_fam hRmem hSmem)
  have hA : IsE27 A := hpt.std.isE27
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨-, f, hf, hker⟩ := hpt.K_kp4 hRmem
  obtain ⟨hRe, -, ⟨d, e, hdB, heB, hde⟩, -⟩ := hpt.R_kp4 hRmem
  obtain ⟨hRL, hR2, hAR, -⟩ := hpt.R_facts hRmem
  have hRc : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hRe.1.is_comm.comm (⟨x, hx⟩ : ↥R) ⟨y, hy⟩)
  have hBK : A ⊓ L ≤ L ⊓ Subgroup.normalizer (R : Set G) := B_le_K hAR
  have hKp : Group.IsPerfect ↥(L ⊓ Subgroup.normalizer (R : Set G)) :=
    isPerfect_of_quot (R_le_K hRL) f hf hker hRc hR2 (hBK hdB) (hBK heB) (hA3 d hdB.1)
      (hA3 e heB.1) (hAc d hdB.1 e heB.1) (hAR hdB.1) (hAR heB.1) hde
  have hKθ := mem_thetaComponentsAt_of_quot hKS (hAS hpt.mem_A)
    (inf_le_left.trans hpt.le_centralizer) (hpt.centralizer_inf_le_normalizer_K hRmem hSmem) hKp
    f hf hker hR2 (R_le_K hRL)
  have hc1 : c ≠ 1 := fun hc => hpt.not_mem (hc ▸ L.one_mem)
  obtain ⟨J₀, hJ₀, hKJ₀, hAJ₀⟩ :=
    exists_thetaComponent_of_quot h48 h45 hM4 hA.1 hA.2 hAS hpt.mem_A hc1 hKθ
  have hKJ : L ⊓ Subgroup.normalizer (R : Set G) ≤
      J₀.map (Subgroup.normalizer (S : Set G)).subtype :=
    fun k hk => ⟨⟨k, hKS hk⟩, hKJ₀ (Subgroup.mem_subgroupOf.mpr hk), rfl⟩
  have hAJ : A ≤ Subgroup.normalizer
      ((J₀.map (Subgroup.normalizer (S : Set G)).subtype : Subgroup G) : Set G) := by
    intro a ha
    have h1 : (⟨a, hAS ha⟩ : ↥(Subgroup.normalizer (S : Set G))) ∈
        Subgroup.normalizer (J₀ : Set ↥(Subgroup.normalizer (S : Set G))) :=
      hAJ₀ (Subgroup.mem_subgroupOf.mpr ha)
    exact Subgroup.le_normalizer_map (Subgroup.normalizer (S : Set G)).subtype ⟨_, h1, rfl⟩
  have hcfg : Cfg A c L R S (J₀.map (Subgroup.normalizer (S : Set G)).subtype) :=
    ⟨hpt, hRmem, hSmem, ⟨J₀, hJ₀, rfl⟩, hKJ, hAJ⟩
  haveI := hcfg.ker_normal
  rcases hcfg.type431 h431 hCL with hJA6 | hJ3' | hJ6 | hJ9 | hJ48
  · obtain ⟨ψ⟩ := hJA6
    exact ⟨S, hcfg.mem_star hA6 ψ (fun S' hS' hSS' => hSmax.2 hS' hSS'), hRS,
      hcfg.normalizer_inf_le ψ⟩
  · exact (hcfg.false_of_J3 hJ3 hGL hJ3').elim
  · exact (hcfg.false_of_A9Sp6 hA9 (Or.inr hJ6)).elim
  · exact (hcfg.false_of_A9Sp6 hA9 (Or.inl hJ9)).elim
  · exact (hcfg.false_of_Sp48 hSp hA6 hJ48).elim

end CFSG.RankThree.PartTwo.Sec14.Ronan1422S
