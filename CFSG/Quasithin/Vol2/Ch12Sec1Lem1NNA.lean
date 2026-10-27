module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1NNJ
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1NmD

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Lem1211NNKv5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V V₁ V₂ : Subgroup G) (β : G → G → ZMod 2),
    Hyp121 G T L V V₁ V₂ 5 → T ≤ Subgroup.normalizer (L : Set G) →
    IsDualPairing121 L V₁ V₂ β → ∀ v ∈ V, IsNonsingular121 V₁ V₂ β v →
      CharTwo (Subgroup.centralizer ({v} : Set G)) →
      ∃ K ∈ cComp (Subgroup.centralizer ({v} : Set G)),
        oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G)) ≤ K ∧
          Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (K : Set G)

open Sec1211Ns in
theorem lem1211NotNormal_of (h331 : Stmt3_3_1)
    (h129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (h36 : Vol2Native.A36CoreForSQTKCat) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat)
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G) (hB51 : AsB51)
    (hA21 : AsA21SQTKSection) (hParab : Lem1211NNParab) (hG2 : Lem1211NNG2)
    (hSL3 : Lem1211NNSL3) (hMod : Lem1211NNMod) (hKv5 : Lem1211NNKv5) : Lem1211NotNormal := by
  intro G _ _ T L V V₁ V₂ n β hyp hTL hβ v hv hns hchar hnorm
  exfalso
  obtain ⟨S₀⟩ := KGH91.Setting.nonempty hyp
  have hns' := hns
  obtain ⟨a₀, ha₀, c₀, hc₀, rfl, hac⟩ := hns
  have hP := KGH91.eq_pairing S₀.hn S₀.C₁ S₀.C₂ S₀.dual hβ.1 hβ.2.1 hβ.2.2.2.2
    ⟨a₀, ha₀, c₀, hc₀, by rw [hac]; exact one_ne_zero⟩ a₀ ha₀ c₀ hc₀
  have S : Sec1211Ns.Setting T L V V₁ V₂ n a₀ c₀ :=
    { toSetting := S₀, hTL := hTL, ha₀ := ha₀, hc₀ := hc₀, hns := hP ▸ hac }
  obtain ⟨F⟩ := S.nonempty_frame
  have hm : 3 ≤ n - 1 := S.three_le
  have hlv := S.lv_eq_oTwoUpper
  obtain ⟨K, hK, hlvK, hKn⟩ : ∃ K ∈ cComp (Subgroup.centralizer ({a₀ * c₀} : Set G)),
      Sec1216Lv.lv L (a₀ * c₀) ≤ K ∧
        Subgroup.centralizer ({a₀ * c₀} : Set G) ≤ Subgroup.normalizer (K : Set G) := by
    rcases hyp.rank with rfl | rfl
    · exact S.exists_kv_four h331 h37 h38 h39 F
    · rw [hlv]
      exact hKv5 G T L V V₁ V₂ β hyp hTL hβ _ hv hns' hchar
  have hlt : Sec1216Lv.lv L (a₀ * c₀) < K := by
    refine lt_of_le_of_ne hlvK fun he => hnorm ?_
    rw [← hlv, he]
    exact hKn
  have hq := S.isQuasisimple_of_lt h331 (h129 G) h36 F hm hchar hK hlt hKn
  exact S.false_of_lt h331 (hC27 G) hParab hG2 hSL3 hB51 hA21 hMod F hm hchar hK hlt hKn hq

end CFSG.Quasithin.H13
