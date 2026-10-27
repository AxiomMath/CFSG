module

public import CFSG.Quasithin.Background.F6Cat
public import CFSG.Quasithin.H13.L32A513b
public import CFSG.Quasithin.H13.L32A53c
public import CFSG.Quasithin.Vol2.Ch6Vocab

public section

namespace CFSG.Quasithin.H13.L32A.T53

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {T L V V₂ Y : Subgroup G} (C : Ctx G T L V V₂ Y)
include C

theorem relIndex_pCoreOf_hY_le
    (hXS3 : quasithinO2QuotientIso (xL L V₂ ⊔ T) (Equiv.Perm (Fin 3)))
    (hinf : (xL L V₂ ⊔ T) ⊓ (Y ⊔ T) = T) (hQ : pCoreOf 2 (hY T L V₂ Y) ≠ ⊥)
    (hsolv : Group.IsSolvable ↥(hY T L V₂ Y)) : (pCoreOf 2 (hY T L V₂ Y)).relIndex T ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXH : xL L V₂ ⊔ T ≤ hY T L V₂ Y := sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hYH : Y ⊔ T ≤ hY T L V₂ Y := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hTH : T ≤ hY T L V₂ Y := le_sup_right
  have hGI : F6.IsGoldschmidtTripleIn (hY T L V₂ Y) (xL L V₂ ⊔ T) (Y ⊔ T) := by
    refine ⟨?_, nonempty_open_of_quasithinO2QuotientIso hXS3,
      nonempty_open_of_quasithinO2QuotientIso C.hS3, ?_⟩
    · apply le_antisymm
      · exact sup_le hXH hYH
      · exact sup_le (sup_le (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_right))
          (le_sup_right.trans le_sup_right)
    · rw [hinf]
      exact C.isSylowTwoOf_T le_sup_right
  set H := hY T L V₂ Y with hH
  set K := CFSG.pPrimeCore 3 ↥H with hK
  set T' := T.subgroupOf H with hT'
  have hTT : (xL L V₂ ⊔ T).subgroupOf H ⊓ (Y ⊔ T).subgroupOf H = T' := by
    rw [hT']
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    rw [← Subgroup.mem_inf, hinf]
  have hTK : K ⊓ T' = Open.pCore 2 ↥H := by
    rw [inf_comm, ← hTT]
    exact F6.inf_inf_pPrimeCore_eq_pCore hGI.subgroupOf
  have hcard : Nat.card ↥(T'.map (QuotientGroup.mk' K)) = (pCoreOf 2 H).relIndex T := by
    rw [← Subgroup.relIndex_ker (K := T') (f := QuotientGroup.mk' K), QuotientGroup.ker_mk',
      ← Subgroup.inf_relIndex_right (H := K) (K := T'), hTK,
      ← Subgroup.relIndex_map_map_of_injective (Open.pCore 2 ↥H) T' H.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTH]
    rfl
  have hT2 : IsPGroup 2 ↥(T'.map (QuotientGroup.mk' K)) :=
    ((C.isSylowTwoOf_T (K := H) le_sup_right).2.1.of_equiv
      (Subgroup.subgroupOfEquivOfLe hTH).symm).map _
  obtain ⟨k, hk⟩ := hT2.exists_card_eq
  have hdvd := Subgroup.card_subgroup_dvd_card (T'.map (QuotientGroup.mk' K))
  rw [← hcard, hk]
  have key : ∀ a m : ℕ, Odd m → Nat.card (↥H ⧸ K) = 2 ^ a * m → 2 ^ k ≤ 2 ^ a := by
    intro a m hm he
    rw [hk, he] at hdvd
    exact Nat.le_of_dvd (by positivity) (Nat.Coprime.dvd_of_dvd_mul_right
      (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm)) hdvd)
  rcases hGI.goldschmidt_mod_pPrimeCore with ⟨hinf', hA, -⟩ | ⟨-, -, ⟨e⟩, -, -⟩
  · have hX3 : Open.pRank 3 (⊤ : Subgroup ↥H) ≤ 2 :=
      stronglyQuasithin_of_pCoreOf_ne_bot C.hyp.fsu.qtke hQ 3 Nat.prime_three (by norm_num)
    obtain ⟨hO3', hm3⟩ := F6.pPrimeCore_eq_bot_and_pRank_le hX3 (MulEquiv.refl _)
    have : Group.IsSolvable ↥H := hsolv
    rcases F6.f618_trichotomy hA.toIsGoldschmidtTriple hO3' hm3 with
      (hc1 | hc2) | ⟨-, K', hK', -, -⟩ | ⟨-, hqs⟩
    ·
      obtain ⟨e⟩ := hc1.1
      have h2 : Nat.card ↥(T'.map (QuotientGroup.mk' K)) = 2 := by
        rw [← hTT, ← hinf', Nat.card_congr e.toEquiv,
          Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2), Nat.card_zmod]
      rw [hk] at h2
      omega
    ·
      rcases hc2 with ⟨⟨e⟩⟩ | ⟨φ, hφ, hker⟩
      · exact key 2 9 (by decide) (by
          rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_perm, Nat.card_fin]; rfl)
      · refine key 2 27 (by decide) ?_
        have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
        rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv, hker.2.1,
          Nat.card_prod] at h1
        rw [h1]
        simp [Nat.card_eq_fintype_card]
    · exact (CFSG.LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple hK'.1
        inferInstance).elim
    · exact (CFSG.LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple hqs
        inferInstance).elim
  ·
    have h6 : Nat.card (↥H ⧸ K) = 2 ^ 1 * 3 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]; rfl
    exact (key 1 3 (by decide) h6).trans (by norm_num)

theorem relIndex_centralizer_vH_le
    (hXS3 : quasithinO2QuotientIso (xL L V₂ ⊔ T) (Equiv.Perm (Fin 3)))
    (hinf : (xL L V₂ ⊔ T) ⊓ (Y ⊔ T) = T) (hQ : pCoreOf 2 (hY T L V₂ Y) ≠ ⊥)
    (hsolv : Group.IsSolvable ↥(hY T L V₂ Y)) :
    (Subgroup.centralizer (vH T L V V₂ Y : Set G)).relIndex T ≤ 4 := by
  have hQC : pCoreOf 2 (hY T L V₂ Y) ≤ Subgroup.centralizer (vH T L V V₂ Y : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (((C.vH_le_center hQ).1 hw).2 q hq).symm
  exact (Subgroup.relIndex_le_of_le_left hQC
    (Subgroup.index_ne_zero_of_finite : ((pCoreOf 2 (hY T L V₂ Y)).subgroupOf T).index ≠ 0)).trans
    (C.relIndex_pCoreOf_hY_le hXS3 hinf hQ hsolv)

theorem not_thompsonJk_le_pCoreOf (hX1 : xL L V₂ = ⁅xL L V₂, thompsonJk 1 T⁆) :
    ¬ thompsonJk 1 T ≤ pCoreOf 2 (xL L V₂ ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hJO
  have hXO' : ⁅xL L V₂, thompsonJk 1 T⁆ ≤ pCoreOf 2 (xL L V₂ ⊔ T) := by
    rw [Subgroup.commutator_le]
    intro x hx q hq
    have hqO := hJO hq
    have hxN : x ∈ Subgroup.normalizer (pCoreOf 2 (xL L V₂ ⊔ T) : Set G) :=
      normalizer_le_normalizer_pCoreOf 2 _ (Subgroup.le_normalizer (Subgroup.mem_sup_left hx))
    rw [commutatorElement_def]
    exact (pCoreOf 2 _).mul_mem ((Subgroup.mem_normalizer_iff.mp hxN q).mp hqO)
      ((pCoreOf 2 _).inv_mem hqO)
  have hXO : xL L V₂ ≤ pCoreOf 2 (xL L V₂ ⊔ T) := hX1.trans_le hXO'
  obtain ⟨z, a, x, hz, hz1, ha, haV, hx, hx3, hxz, hxa⟩ := C.exists_rot_X
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (xL L V₂ ⊔ T) ⟨x, hXO hx⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf x = 1 := Nat.Coprime.eq_one_of_dvd
    ((Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)).coprime_dvd_left
      (orderOf_dvd_of_pow_eq_one hx3)) (orderOf_dvd_of_pow_eq_one hk')
  rw [orderOf_eq_one_iff] at h1
  apply haV
  rw [← hxz, h1, one_mul, inv_one, mul_one]
  exact hz

theorem exists_offender (hX1 : xL L V₂ = ⁅xL L V₂, thompsonJk 1 T⁆) :
    ∃ A : Subgroup G, A ≤ T ∧ IsElemAbelian 2 A ∧
      (∀ B : Subgroup G, B ≤ T → IsElemAbelian 2 B → Nat.card B ≤ 2 ^ 1 * Nat.card A) ∧
      ¬ A ≤ pCoreOf 2 (xL L V₂ ⊔ T) := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  exact C.not_thompsonJk_le_pCoreOf hX1 (iSup₂_le fun A hA => hcon A hA.1 hA.2.1 hA.2.2)

theorem card_le_mul (hQ : pCoreOf 2 (hY T L V₂ Y) ≠ ⊥) {A : Subgroup G} (hAT : A ≤ T)
    (hA : IsElemAbelian 2 A)
    (hmax : ∀ B : Subgroup G, B ≤ T → IsElemAbelian 2 B → Nat.card B ≤ 2 ^ 1 * Nat.card A) :
    Nat.card (vH T L V V₂ Y) ≤
      2 * (A ⊓ Subgroup.centralizer (vH T L V V₂ Y : Set G)).relIndex A *
        Nat.card ↥(vH T L V V₂ Y ⊓ Subgroup.centralizer (A : Set G)) := by
  set W := vH T L V V₂ Y with hW
  set A₀ := A ⊓ Subgroup.centralizer (W : Set G) with hA₀
  have hWe := (C.vH_le_center hQ).2
  have hWZ := (C.vH_le_center hQ).1
  have hWT : W ≤ T := fun w hw =>
    (pCoreOf_two_le_of_isSylowTwoOf (C.isSylowTwoOf_T (K := hY T L V₂ Y) le_sup_right))
      (hWZ hw).1
  have hcomm : ∀ a ∈ A₀, ∀ w ∈ W, a * w = w * a := fun a ha w hw =>
    (Subgroup.mem_centralizer_iff.mp ha.2 w hw).symm
  have hA₀e : IsElemAbelian 2 A₀ := B2F.isElemAbelian_mono inf_le_left hA
  have hBe : IsElemAbelian 2 (A₀ ⊔ W) := B2F.isElemAbelian_sup_of_commute hA₀e hWe hcomm
  have hBT : A₀ ⊔ W ≤ T := sup_le (inf_le_left.trans hAT) hWT
  have hcard := hmax _ hBT hBe
  have e1 := B2F.card_sup_mul_card_inf_of_commute hcomm
  have e2 := Subgroup.relIndex_mul_card (H := A₀) (K := A)
  rw [inf_eq_left.mpr (inf_le_left : A₀ ≤ A)] at e2
  have hle : A₀ ⊓ W ≤ W ⊓ Subgroup.centralizer (A : Set G) := by
    intro w hw
    refine ⟨hw.2, ?_⟩
    show w ∈ Subgroup.centralizer (A : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have := hA.1.is_comm.comm ⟨a, ha⟩ ⟨w, hw.1.1⟩
    exact congrArg Subtype.val this
  have hc3 := Subgroup.card_le_of_le hle
  have hpos : 0 < Nat.card A₀ := Nat.card_pos
  have key : Nat.card A₀ * Nat.card W ≤ Nat.card A₀ * (2 * A₀.relIndex A *
      Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G))) := by
    calc Nat.card A₀ * Nat.card W = Nat.card ↥(A₀ ⊔ W) * Nat.card ↥(A₀ ⊓ W) := e1.symm
      _ ≤ (2 ^ 1 * Nat.card A) * Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G)) :=
          Nat.mul_le_mul hcard hc3
      _ = Nat.card A₀ * (2 * A₀.relIndex A *
          Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G))) := by
          rw [← e2]; ring
  exact Nat.le_of_mul_le_mul_left key hpos

end Ctx

end CFSG.Quasithin.H13.L32A.T53

end
