module

public import CFSG.Quasithin.Background.A4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.A4

variable {G : Type*} [Group G]

@[expose] def CKQ (K Q : Subgroup G) : Subgroup G :=
  ⨆ (C : Subgroup G) (_ : C ≤ Q) (_ : C ≠ ⊥) (_ : (C.subgroupOf Q).Characteristic),
    K ⊓ Subgroup.normalizer (C : Set G)

namespace A4

theorem oTwoUpper_oTwoUpper (X : Subgroup G) : oTwoUpper (oTwoUpper X) = oTwoUpper X := by
  refine le_antisymm (oTwoUpper_le _) ((Subgroup.closure_le _).mpr fun x hx => ?_)
  exact mem_oTwoUpper_of_odd (Subgroup.subset_closure hx) hx.2

end A4

section Finite

variable [Finite G]

theorem a4_4_1_of_faithful {H K X : Subgroup G} (hOX : pCoreOf 2 H ≤ X) (hXHK : X ≤ H ⊓ K)
    (hX : X = oTwoUpper X ⊔ pCoreOf 2 H) (hXH : IsSubnormal X H)
    (hfaith : IsSylowTwoOf (pCoreOf 2 H) (centralizerSection H X (pCoreOf 2 H))) :
    pCoreOf 2 (H ⊓ K) = pCoreOf 2 H := by
  set P := pCoreOf 2 H with hP
  set L := H ⊓ K with hL
  set Q := pCoreOf 2 L with hQ
  have hPn : H ≤ Subgroup.normalizer (P : Set G) := le_normalizer_pCoreOf 2 H
  refine le_antisymm ?_ (le_pCoreOf_of_le_normalizer 2 (hOX.trans hXHK)
    (inf_le_left.trans hPn) (pCoreOf_isPGroup 2 H))
  set X₀ := oTwoUpper X with hX₀
  have hX₀X : IsSubnormal X₀ X :=
    subnormal_of_normal (oTwoUpper_le X)
      (Subgroup.normal_subgroupOf_of_le_normalizer (le_normalizer_oTwoUpper X))
  have hX₀H : IsSubnormal X₀ H := subnormal_trans hX₀X hXH
  have hX₀₀ : X₀ = oTwoUpper X₀ := (oTwoUpper_oTwoUpper X).symm
  have hQsig : IsSignalizer H X₀ Q :=
    ⟨(pCoreOf_le 2 L).trans inf_le_left, pCoreOf_isPGroup 2 L,
      ((oTwoUpper_le X).trans (hXHK.trans (le_normalizer_pCoreOf 2 L)))⟩
  have hcomm : ⁅X₀, Q⁆ ≤ P := (a4_2_3 hX₀₀ hX₀H hQsig).trans (pCoreOf_le_of_subnormal 2 hX₀H)
  have hXQ : ⁅X, Q⁆ ≤ P := by
    refine Subgroup.commutator_le.mpr fun x hx q hq => ?_
    have hx' : x ∈ (↑(X₀ ⊔ P) : Set G) := hX ▸ hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right X₀ P
      ((oTwoUpper_le X).trans (hXHK.trans inf_le_left) |>.trans hPn)] at hx'
    obtain ⟨x₀, hx₀, p, hp, rfl⟩ := hx'
    have hqH : q ∈ H := (pCoreOf_le 2 L hq).1
    have h1 : p * q * p⁻¹ * q⁻¹ ∈ P := by
      have := (Subgroup.mem_normalizer_iff.mp (hPn hqH) p⁻¹).mp (P.inv_mem hp)
      have h2 := P.mul_mem hp this
      simpa [mul_assoc] using h2
    have h2 : x₀ * (p * q * p⁻¹ * q⁻¹) * x₀⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (hPn ((oTwoUpper_le X).trans (hXHK.trans inf_le_left) hx₀))
        _).mp h1
    have h3 : x₀ * q * x₀⁻¹ * q⁻¹ ∈ P := hcomm (Subgroup.commutator_mem_commutator hx₀ hq)
    have e : x₀ * p * q * (x₀ * p)⁻¹ * q⁻¹ =
        (x₀ * (p * q * p⁻¹ * q⁻¹) * x₀⁻¹) * (x₀ * q * x₀⁻¹ * q⁻¹) := by group
    show x₀ * p * q * (x₀ * p)⁻¹ * q⁻¹ ∈ P
    rw [e]
    exact P.mul_mem h2 h3
  have hQC : Q ≤ centralizerSection H X P :=
    (le_centralizerSection_iff hOX).mpr ⟨(pCoreOf_le 2 L).trans inf_le_left, hXQ⟩
  obtain ⟨hPC, hP2, hmax⟩ := isSylowTwoOf_iff_maximal.mp hfaith
  have hQn : Q ≤ Subgroup.normalizer (P : Set G) :=
    hQC.trans (centralizerSection_le_normalizer_right H X P)
  have hPQ2 : IsPGroup 2 (P ⊔ Q : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hP2 (pCoreOf_isPGroup 2 L) hQn
  exact le_sup_right.trans (hmax _ (sup_le hPC hQC) hPQ2 le_sup_left)

theorem a4_4_2_of_pCoreOf_eq {H K : Subgroup G} (hH : quasithinIsMaxTwoLocal H)
    (hQ : pCoreOf 2 (H ⊓ K) = pCoreOf 2 H) : CKQ K (pCoreOf 2 (H ⊓ K)) ≤ H ⊓ K := by
  rw [hQ]
  refine iSup₂_le fun C hC => iSup₂_le fun hne hchar => ?_
  have hHC : H ≤ Subgroup.normalizer (C : Set G) := by
    have := normalizer_le_normalizer_map_of_characteristic (C.subgroupOf (pCoreOf 2 H))
    rw [Subgroup.map_subgroupOf_eq_of_le hC] at this
    exact (le_normalizer_pCoreOf 2 H).trans this
  have hloc : IsTwoLocal (Subgroup.normalizer (C : Set G)) :=
    ⟨C, hne, (pCoreOf_isPGroup 2 H).to_le hC, rfl⟩
  have heq : Subgroup.normalizer (C : Set G) = H := hH.2 _ hloc hHC
  rw [heq, inf_comm]

theorem a4_4_3_of_pCoreOf_eq {H K : Subgroup G} (hH : quasithinIsMaxTwoLocal H)
    (hK : quasithinIsMaxTwoLocal K) (hQ : pCoreOf 2 K = pCoreOf 2 H) : H = K := by
  obtain ⟨P, hPne, hP2, hHP⟩ := hH.1
  have hPle : P ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 (hHP ▸ Subgroup.le_normalizer) (hHP ▸ le_rfl) hP2
  have hne : pCoreOf 2 H ≠ ⊥ := fun h => hPne (le_bot_iff.mp (h ▸ hPle))
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 H : Set G)) :=
    ⟨pCoreOf 2 H, hne, pCoreOf_isPGroup 2 H, rfl⟩
  have h1 : Subgroup.normalizer (pCoreOf 2 H : Set G) = H :=
    hH.2 _ hloc (le_normalizer_pCoreOf 2 H)
  have h2 : Subgroup.normalizer (pCoreOf 2 H : Set G) = K := by
    rw [← hQ]
    exact hK.2 _ (hQ ▸ hloc) (le_normalizer_pCoreOf 2 K)
  rw [← h1, h2]

end Finite

end CFSG.Quasithin
