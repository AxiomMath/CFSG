module

public import CFSG.Quasithin.Background.Harris.KFact2d.StarFacts
public import CFSG.Quasithin.Background.Harris.KFact2d.F4Apply
public import CFSG.Quasithin.Background.Harris.KFact2d.OddStep
public import CFSG.Quasithin.Background.G2
public import CFSG.Quasithin.Background.Harris.KFact2d.Setup

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin E2P B6 CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem stepOne (hF4 : F4Stmt) {T N K K0 V : Subgroup G} (hmp : MinParabolic K T N)
    (hK0 : K0 ∈ cComp K) (hKK0 : K = K0 ⊔ T) (hc : CFSG.Quasithin.Gap6R2.E22Case2d K T N K0)
    (hJT : ¬ kerIn N K ≤ T) (hV : IsElemAbelian 2 V) (hVT : V ≤ T)
    (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hat : ∀ A : Subgroup G, T ≤ A → A ≤ N → ¬ A ≤ Subgroup.normalizer (V : Set G) →
      (∀ B : Subgroup G, T ≤ B → B < A → B ≤ Subgroup.normalizer (V : Set G)) →
      IsElemAbelian 2 (conjClosure V A)) :
    E2.star N K V ≤ E2.star N K K0 := by
  obtain ⟨hTn, hker⟩ := case2d_facts hc
  obtain ⟨p, hX⟩ := exists_case2dStar hmp hK0 hKK0 hc
  have hTK : T ≤ K := hmp.isSylow.1
  have hNK : N ≤ K := hmp.maximal.1.le
  have hK0K : K0 ≤ K := le_of_mem_cComp hK0
  have hJN : kerIn N K ≤ N := kerIn_le
  have hJK : kerIn N K ≤ K := hJN.trans hNK
  have hQK : K ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) := le_normalizer_pCoreOf 2 K
  have hQleK : pCoreOf 2 K ≤ K := pCoreOf_le 2 K
  have hDK : K0 ⊔ pCoreOf 2 K ≤ K := D_le_K hK0
  have hDn : K ≤ Subgroup.normalizer ((K0 ⊔ pCoreOf 2 K : Subgroup G) : Set G) :=
    le_normalizer_sup₂ (K0_le_normalizer hKK0 hTn) hQK
  have hQJ : pCoreOf 2 K ≤ kerIn N K := Q_le_J hK0 hker
  have hodd := odd_of_J hker hJK
  have hQT : pCoreOf 2 K ≤ T := pCoreOf_two_le_of_isSylowTwoOf hmp.isSylow
  have hQlt : pCoreOf 2 K < kerIn N K :=
    lt_of_le_of_ne hQJ (fun h => hJT (h ▸ hQT))
  have hTJ : T ≤ Subgroup.normalizer (kerIn N K : Set G) :=
    hTK.trans (le_normalizer_kerIn N K)
  obtain ⟨J1, hQJ1, hJ1J, hTJ1, hminJ1⟩ := exists_minimal_inv hQlt hTJ
  have hcomm : ∀ v ∈ V, ∀ y ∈ J1, v * y * v⁻¹ * y⁻¹ ∈ pCoreOf 2 K :=
    comm_mem_of_atom hmp.isSylow.2.1 hmp.le (hJ1J.trans hJN) hTJ1 hTV hVT
      (fun y hy => hodd y (hJ1J hy))
      (fun B hTB hBA => eq_or_eq_sup_of_minimal hQT hQJ1.le hTJ1 hminJ1 hTB hBA) hat
  rintro _ ⟨y, hy, rfl⟩
  by_contra hnot
  have hv : (y : G) ∈ V := Subgroup.mem_subgroupOf.mp hy
  have hv2 : (y : G) * y = 1 := by
    have := hV.2 y hv
    rwa [pow_two] at this
  have hKs : ((K0 ⊔ pCoreOf 2 K).subgroupOf K).map (starMap N K) = E2.star N K K0 :=
    star_sup_pCore hQJ hK0K hQK
  have hJiff : ∀ x, x ∈ kerIn N K ↔ x ∈ K0 ⊔ pCoreOf 2 K ∧
      ∀ z ∈ K0 ⊔ pCoreOf 2 K, x * z * x⁻¹ * z⁻¹ ∈ pCoreOf 2 K := hker
  have hinv := inverts_of_F4 hF4 (starMap N K) (E2.star N K K0) (K0 := K0) (J := kerIn N K)
    (D := K0 ⊔ pCoreOf 2 K) hQK hQleK hDK hDn rfl hK0K hK0.2.1 hJiff hQJ (ker_starMap N K) hKs
    hX.1.cent hodd hX.2.1 hX.2.2.1
    (hX.2.2.2.1.imp id fun h => ⟨h.1, h.2.1⟩) y.2 hv2
    (by
      intro hmem
      apply hnot
      have : y = ⟨(y : G), y.2⟩ := rfl
      rwa [← this] at hmem)
  obtain ⟨j, hjJ1, hjQ⟩ := IsConcreteLE.exists_of_lt hQJ1
  have h1 := hinv j (hJ1J hjJ1)
  have h2 := hcomm (y : G) hv j hjJ1
  have hj2 : j ^ 2 ∈ pCoreOf 2 K := by
    have h3 : j ^ 2 = ((y : G) * j * (y : G)⁻¹ * j⁻¹)⁻¹ * ((y : G) * j * (y : G)⁻¹ * j) := by
      rw [pow_two]
      group
    rw [h3]
    exact (pCoreOf 2 K).mul_mem ((pCoreOf 2 K).inv_mem h2) h1
  exact hjQ (hodd j (hJ1J hjJ1) ⟨1, by simpa using hj2⟩)

end CFSG.Quasithin.Background.Harris.KFact2d
