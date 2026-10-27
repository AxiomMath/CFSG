module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBFinal
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKKR
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKFlipD
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKF53
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBFlip
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBL323

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.CosetGraph
open scoped commutatorElement Pointwise

theorem flipCore_of_nsb (hN31 : NotC31) (h22 : ∀ (G : Type) [Group G] [Finite G], ASC22Three G)
    (h27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G) (h31 : Lemma31)
    (h32 : Lemma32) (hN3 : NSBModuleStructure) (hF53 : NSBLocalFlipFiveThree) : FlipCore := by
  intro G _ _ T M L Mm I H K m k hch hIV g hg h1 h2 h3
  have hd : NoSumBigData G T M L Mm I H K m k := hch.1
  obtain ⟨hHK, -, n, hnm, hpsl⟩ := h32 G T M L Mm I H K m k hd
  by_cases h53 : n = 5 ∧ m = 3
  · exfalso
    obtain ⟨rfl, hm3⟩ := h53
    obtain ⟨j, α, β, hjn, hsurj, hker, hbij, hequi⟩ := hN3 G T M L Mm I H K m k hd 5 hnm hpsl
    obtain ⟨α', β', hs', hk', hb', he', hVc, hcov, hkj, hVeq⟩ :=
      exists_std_coordinates hN31 h22 h27 hd hnm α β hsurj hker hbij hequi
    exact hF53 G T M L Mm I H K m k j hch hIV hm3 hjn hkj
      ⟨α', β', hs', hk', hb', he', hVc, hcov, hVeq⟩ g hg h1 h2 h3
  · have hnm1 : n = m + 1 := by
      rcases hnm with ⟨h4, h5⟩ | ⟨h4, h5⟩ | ⟨h4, h5⟩
      · omega
      · exact absurd ⟨h4, h5⟩ h53
      · omega
    obtain ⟨j, α, β, hjn, hsurj, hker, hbij, hequi⟩ := hN3 G T M L Mm I H K m k hd n hnm hpsl
    obtain ⟨α', β', hs', hk', hb', he', hVc, hcov, hkj, hVeq⟩ :=
      exists_std_coordinates hN31 h22 h27 hd hnm α β hsurj hker hbij hequi
    subst hnm1
    have hmk : m ≤ k := hd.2.2.2.2.1
    have hm34 : m = 3 ∨ m = 4 := hd.2.2.2.1
    have hjm : j = m := by omega
    have hkm : k = m := by omega
    have hj : 0 < j := by omega
    let D : StdData G T L I K m k (m + 1) j := ⟨α', β', hs', hk', hb', he', hVc, hcov, hVeq⟩
    have hVU := vV_le_uZero hN31 h22 h27 hd
    obtain ⟨hRlt, hRC⟩ := h31 G T M L Mm I H K m k hd
    exact flip_conclusion_succ hd.2.2.1 (h22 G) hd.2.1.2 hHK hVU hj hjm hkm D hRlt hRC h1 h2 h3

theorem localFlip_of_nsb (hN31 : NotC31) (h22 : ∀ (G : Type) [Group G] [Finite G], ASC22Three G)
    (h27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G) (h31 : Lemma31)
    (h32 : Lemma32) (h323 : Lemma323') (hN3 : NSBModuleStructure)
    (hF53 : NSBLocalFlipFiveThree) : LocalFlip :=
  localFlip_of h323 (flipCore_of_nsb hN31 h22 h27 h31 h32 hN3 hF53)

theorem conf4212NoSumBig_of_nsb_inputs
    (h22 : ∀ (G : Type) [Group G] [Finite G], ASC22Three G)
    (h27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h425 : Thm4_2_5) (h48 : ∀ (G : Type) [Group G] [Finite G], ASC48Statement G)
    (hN3 : NSBModuleStructure) (hF53 : NSBLocalFlipFiveThree) : Conf4212NoSumBig := by
  have h31 : Lemma31 := lemma31_holds h37 h38 h39
  have h32 : Lemma32 := lemma32_of notC31_holds (c41Case4Of_holds h37 h38 h39)
  exact conf4212NoSumBig_of_module_data h22 h27 h36 h37 h38 h39 h425 h48
    (lemma35KR_of_module notC31_holds h22 h27 hN3 h31 h32)
    (localFlip_of_nsb notC31_holds h22 h27 h31 h32 (lemma323'_holds h37 h38 h39) hN3 hF53)

end CFSG.Quasithin.H13.Ch4.NSB
