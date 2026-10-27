module

public import CFSG.Assembly.LargeEvenDefs
public import CFSG.ClassicalInvolution.Phan.Defs
public import CFSG.Open.LocalVocabulary
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCompA2
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCompC1
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCompC2

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan

variable {G : Type} [Group G] [Finite G]

theorem ggQTwoDUnit_one_component
    {H J₁ J₂ P : Subgroup G} {F0 : Type} [Field F0] [Finite F0]
    [CharP F0 2] (hF0 : Nat.card F0 = 4) {d : ℕ} (hd : 5 ≤ d) {y₁ y₂ : G}
    (hJ₁ : ∃ θ : Su F0 2 1 d →* G, Function.Injective θ ∧ θ.range = J₁)
    (hJ₂ : ∃ θ : Su F0 2 1 d →* G, Function.Injective θ ∧ θ.range = J₂)
    (hy₁ : y₁ ∈ H) (hy₂ : y₂ ∈ H) (hy₁3 : y₁ ^ 3 = 1) (hy₂3 : y₂ ^ 3 = 1)
    (hc₁ : IsComponentOf J₁ (H ⊓ Subgroup.centralizer ({y₁} : Set G)))
    (hc₂ : IsComponentOf J₂ (H ⊓ Subgroup.centralizer ({y₂} : Set G)))
    (hl₁ : J₁ ≤ LargeEvenPLayer 3 H) (hl₂ : J₂ ≤ LargeEvenPLayer 3 H)
    (hP₁ : P ≤ J₁) (hP₂ : P ≤ J₂) (hPperf : ⁅P, P⁆ = P) (hP3 : 3 ∣ Nat.card ↥P)
    (hrank : ∀ E : Subgroup G, CFSG.Open.IsElemAbelian 3 E →
      (∃ U : Subgroup G, U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.normalizer (U : Set G)) →
        Nat.card ↥E ≤ 3 ^ (d + 1)) :
    ∃ N : Subgroup G, LargeEvenPComponent 3 H N ∧ J₁ ≤ N ∧ J₂ ≤ N := by
  have hJH₁ : J₁ ≤ H := hc₁.1.trans inf_le_left
  have hJH₂ : J₂ ≤ H := hc₂.1.trans inf_le_left
  let y₁' : ↥H := ⟨y₁, hy₁⟩
  let y₂' : ↥H := ⟨y₂, hy₂⟩
  have hy₁3' : y₁' ^ 3 = 1 := by
    apply Subtype.ext
    simpa [y₁'] using hy₁3
  have hy₂3' : y₂' ^ 3 = 1 := by
    apply Subtype.ext
    simpa [y₂'] using hy₂3
  obtain ⟨Q₁, hQ₁, hJQ₁⟩ :=
    qtwoDB7_exists_component (y := y₁') hF0 hd hJ₁ hy₁3' hc₁ hl₁ hrank
  obtain ⟨Q₂, hQ₂, hJQ₂⟩ :=
    qtwoDB7_exists_component (y := y₂') hF0 hd hJ₂ hy₂3' hc₂ hl₂ hrank
  have hPH : P ≤ H := hP₁.trans hJH₁
  obtain ⟨hPperf', hPne⟩ := qtwoDB7_perfect_image hPH hPperf hP3
  have hPQ₁ : (P.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)) ≤ Q₁ :=
    (Subgroup.map_mono (Subgroup.subgroupOf_mono H hP₁)).trans hJQ₁
  have hPQ₂ : (P.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)) ≤ Q₂ :=
    (Subgroup.map_mono (Subgroup.subgroupOf_mono H hP₂)).trans hJQ₂
  have hQeq : Q₁ = Q₂ := qtwoDB7_components_eq hQ₁ hQ₂ hPperf' hPne hPQ₁ hPQ₂
  obtain ⟨hJ₁q, h3₁⟩ := qtwoDB7_su_data hF0 hd hJ₁ hJH₁
  obtain ⟨hJ₂q, h3₂⟩ := qtwoDB7_su_data hF0 hd hJ₂ hJH₂
  obtain ⟨N₁, hN₁, hJN₁, himg₁⟩ := qtwoDB7_exists_pcomp hQ₁ hJH₁ hJ₁q h3₁ hJQ₁
  obtain ⟨N₂, hN₂, hJN₂, himg₂⟩ := qtwoDB7_exists_pcomp hQ₂ hJH₂ hJ₂q h3₂ hJQ₂
  have hN₁₂ : N₁ = N₂ :=
    qtwoDB7_pcomp_unique hN₁ hN₂ (himg₁.trans (hQeq.trans himg₂.symm))
  exact ⟨N₁, hN₁, hJN₁, hN₁₂.symm ▸ hJN₂⟩

end CFSG.StandardType.QTwo

end
