module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBFFin
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBMFinal
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBFTen

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.CosetGraph
open scoped commutatorElement Pointwise

theorem nsbLocalFlipFiveThree_of (hN31 : NotC31)
    (h22 : ∀ (G : Type) [Group G] [Finite G], ASC22Three G)
    (h27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G) (h31 : Lemma31)
    (h32 : Lemma32) (h323 : Lemma323') : NSBLocalFlipFiveThree := by
  intro G _ _ T M L Mm I H K m k j hch hIV hm3 hjn hkj D g hg h1 h2 h3
  have hd : NoSumBigData G T M L Mm I H K m k := hch.1
  have hc : Conf4212 G T M L I H K := hd.2.2.1
  have hVU := vV_le_uZero hN31 h22 h27 hd
  have hIH : I ≤ H := hd.2.1.2
  obtain ⟨hHK, -⟩ := h32 G T M L Mm I H K m k hd
  obtain ⟨hRlt, hRC⟩ := h31 G T M L Mm I H K m k hd
  have hRΓ : pCoreOf 2 I ≤ gammaZero T M L I := fun r hr =>
    ⟨⟨(hRlt.le hr).2, Subgroup.le_normalizer hr⟩, hRC (hRlt.le hr)⟩
  have hmk : m ≤ k := hd.2.2.2.2.1
  have hj3 : 3 ≤ j := by omega
  have hk2 : 2 ≤ k := by omega
  obtain ⟨U, ι, θ, hU, hι, hCF⟩ :=
    exists_flip_group (h22 G) hc hIH hHK (by norm_num) le_rfl hj3 D hRΓ h1 h2 h3
  obtain ⟨w₀, w₁, hw₀, hw₁, hw₁₀, hV₀, hV₁⟩ :=
    exists_V_tensor hN31 h22 h27 hd (by omega) hk2 D
  have hnormU : K ⊔ pCoreOf 2 I ≤ Subgroup.normalizer (uZero I K : Set G) :=
    le_normalizer_uZero hIH hHK
  have hKU : ∀ x : ↥K, ∀ z ∈ uZero I K, (x : G) * z * (x : G)⁻¹ ∈ uZero I K := fun x z hz =>
    (Subgroup.mem_normalizer_iff.mp (hnormU (Subgroup.mem_sup_left x.2)) z).mp hz
  exact false_of_flip_data h323 hd hVU hKU (by norm_num) D hm3 hj3 hU hι hCF hw₀ hw₁ hw₁₀ hV₀ hV₁

theorem conf4212NoSumBig_holds
    (h22 : ∀ (G : Type) [Group G] [Finite G], ASC22Three G)
    (h27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h425 : Thm4_2_5) (h48 : ∀ (G : Type) [Group G] [Finite G], ASC48Statement G)
    (h51 : AsB51) (hI16 : AsI16Cover) (hA8 : AsI16CoverA8) : Conf4212NoSumBig :=
  conf4212NoSumBig_of_flip53 h22 h27 h36 h37 h38 h39 h425 h48 h51 hI16 hA8
    (nsbLocalFlipFiveThree_of notC31_holds h22 h27 (lemma31_holds h37 h38 h39)
      (lemma32_of notC31_holds (c41Case4Of_holds h37 h38 h39)) (lemma323'_holds h37 h38 h39))

end CFSG.Quasithin.H13.Ch4.NSB
