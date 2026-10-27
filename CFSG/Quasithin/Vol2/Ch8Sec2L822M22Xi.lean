module

public import CFSG.Quasithin.Vol2.Ch1Xi
public import CFSG.Quasithin.Vol2.Ch3Sec1L319S3Wr
public import CFSG.Quasithin.Vol2.Ch3zCmp

public section

namespace CFSG.Quasithin.H13.L319

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_oTwoUpper_eq (H : Subgroup G) :
    pCoreOf 2 (oTwoUpper H) = oTwoUpper H ⊓ pCoreOf 2 H := by
  have hXH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hXn : H ≤ Subgroup.normalizer (oTwoUpper H : Set G) := le_normalizer_oTwoUpper H
  apply le_antisymm
  · refine le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 _) ?_
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hXH)
      (hXn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_right)
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hx, CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hXH hx)⟩

section Quot

variable {H : Subgroup G}

theorem range_comp_oTwoUpper (φ : ↥H →* S3Wr) (hs : Function.Surjective φ) :
    (φ.comp (Subgroup.inclusion (oTwoUpper_le H))).range = oddSub := by
  apply le_antisymm
  · rintro _ ⟨⟨x, hx⟩, rfl⟩
    have hQ : oTwoUpper H ≤ (oddSub.comap φ).map H.subtype := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro y ⟨hyH, hyo⟩
      refine ⟨⟨y, hyH⟩, ?_, rfl⟩
      refine (mem_oddSub_iff _).mpr ?_
      have h1 : orderOf (φ ⟨y, hyH⟩) ∣ orderOf (⟨y, hyH⟩ : ↥H) := orderOf_map_dvd φ _
      have h2 : Odd (orderOf (⟨y, hyH⟩ : ↥H)) := by
        rw [← Subgroup.orderOf_coe]; exact hyo
      exact h2.of_dvd_nat h1
    obtain ⟨z, hz, hzx⟩ := hQ hx
    have : z = ⟨x, oTwoUpper_le H hx⟩ := Subtype.ext hzx
    subst this
    exact hz
  · intro w hw
    have hwo : Odd (orderOf w) := (mem_oddSub_iff w).mp hw
    obtain ⟨h, rfl⟩ := hs w
    obtain ⟨n, hno, hφ⟩ := CFSG.Quasithin.Ch3z.exists_odd_pow_eq φ (isOfFinOrder_of_finite h) hwo
    have hmem : ((h ^ n : ↥H) : G) ∈ oTwoUpper H :=
      mem_oTwoUpper_of_odd (h ^ n).2 (by rw [Subgroup.orderOf_coe]; exact hno)
    exact ⟨⟨(h ^ n : ↥H), hmem⟩, hφ⟩

end Quot

theorem isXi_of_quot_S3Wr {T H : Subgroup G} (hT : IsSylowTwoOf T H) (hO : pCoreOf 2 H ≠ ⊥)
    (φ : ↥H →* S3Wr) (hs : Function.Surjective φ) (hk : φ.ker = (pCoreOf 2 H).subgroupOf H) :
    IsXi T (twoResidual H) := by
  have e : twoResidual H = oTwoUpper H := F6.twoResidual_eq_oTwoUpper H
  rw [e]
  have hXH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hXn : H ≤ Subgroup.normalizer (oTwoUpper H : Set G) := le_normalizer_oTwoUpper H
  have hTH : T ≤ H := hT.1
  have hpX : pCoreOf 2 (oTwoUpper H) = oTwoUpper H ⊓ pCoreOf 2 H := pCoreOf_oTwoUpper_eq H
  have hrange := range_comp_oTwoUpper φ hs
  have hφX : ∀ x : G, ∀ hx : x ∈ oTwoUpper H, φ ⟨x, hXH hx⟩ ∈ oddSub := by
    intro x hx
    rw [← hrange]
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : ∀ x : G, ∀ hx : x ∈ oTwoUpper H, φ ⟨x, hXH hx⟩ = 1 → x ∈ pCoreOf 2 (oTwoUpper H) := by
    intro x hx h1
    rw [hpX]
    refine ⟨hx, ?_⟩
    have : (⟨x, hXH hx⟩ : ↥H) ∈ φ.ker := h1
    rw [hk] at this
    exact this
  have hcardE : Nat.card (oddSub) = 3 ^ 2 := by rw [oddSub_card]; norm_num
  have hcommE : ∀ a b : S3Wr, a ∈ oddSub → b ∈ oddSub → a * b = b * a := by
    intro a b ha hb
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have := IsPGroup.commutative_of_card_eq_prime_sq (G := ↥oddSub) (p := 3) hcardE ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  have hrel : (pCoreOf 2 (oTwoUpper H)).relIndex (oTwoUpper H) = 9 := by
    set ψ : ↥(oTwoUpper H) →* S3Wr := φ.comp (Subgroup.inclusion hXH) with hψ
    have hker' : ψ.ker = (pCoreOf 2 (oTwoUpper H)).subgroupOf (oTwoUpper H) := by
      ext x
      constructor
      · intro hx
        exact hker x x.2 hx
      · intro hx
        have hx' : (x : G) ∈ pCoreOf 2 (oTwoUpper H) := hx
        rw [hpX] at hx'
        have : (⟨x, hXH x.2⟩ : ↥H) ∈ φ.ker := by rw [hk]; exact hx'.2
        exact this
    unfold Subgroup.relIndex
    rw [← hker', Subgroup.index_ker, hrange, oddSub_card]
  refine ⟨?_, hTH.trans hXn, ?_, 3, Nat.prime_three, by norm_num, ?_, Or.inl (by rw [hrel]; norm_num),
    ?_⟩
  · calc oTwoUpper H = twoResidual H := e.symm
      _ = twoResidual (twoResidual H) := (twoResidual_twoResidual H).symm
      _ = twoResidual (oTwoUpper H) := by rw [e]
      _ = oTwoUpper (oTwoUpper H) := F6.twoResidual_eq_oTwoUpper _
  · have hsup : oTwoUpper H ⊔ T = H := by
      rw [sup_comm, ← e]
      exact sup_twoResidual_eq hT
    rw [hsup]
    exact hO
  · intro x hx
    have h1 := hφX x hx
    have h3 : φ ⟨x, hXH hx⟩ ^ 3 = 1 := S3Wr_odd_pow_three _ ((mem_oddSub_iff _).mp h1)
    have h4 : (⟨x ^ 3, (oTwoUpper H).pow_mem hx 3 |> hXH⟩ : ↥H) = ⟨x, hXH hx⟩ ^ 3 := rfl
    exact hker (x ^ 3) ((oTwoUpper H).pow_mem hx 3) (by rw [h4, map_pow]; exact h3)
  · intro Y hY1 hYX hTY
    have hcomm : ⁅oTwoUpper H, oTwoUpper H⁆ ≤ pCoreOf 2 (oTwoUpper H) := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      have hab : ⁅a, b⁆ ∈ oTwoUpper H := by
        rw [commutatorElement_def]
        exact (oTwoUpper H).mul_mem ((oTwoUpper H).mul_mem ((oTwoUpper H).mul_mem ha hb)
          ((oTwoUpper H).inv_mem ha)) ((oTwoUpper H).inv_mem hb)
      refine hker _ hab ?_
      have e1 : (⟨⁅a, b⁆, hXH hab⟩ : ↥H) = ⁅(⟨a, hXH ha⟩ : ↥H), (⟨b, hXH hb⟩ : ↥H)⁆ := rfl
      rw [e1, map_commutatorElement, commutatorElement_eq_one_iff_commute]
      exact hcommE _ _ (hφX a ha) (hφX b hb)
    have hsup : ⁅oTwoUpper H, oTwoUpper H⁆ ⊔ pCoreOf 2 (oTwoUpper H) = pCoreOf 2 (oTwoUpper H) :=
      sup_eq_right.mpr hcomm
    rw [hsup] at hY1 ⊢
    set K : Subgroup S3Wr := (Y.subgroupOf H).map φ with hK
    have hKE : K ≤ oddSub := by
      rintro _ ⟨y, hy, rfl⟩
      exact hφX y (hYX hy)
    set S : Subgroup S3Wr := (T.subgroupOf H).map φ with hS
    have hS2 : IsPGroup 2 S := by
      intro s
      obtain ⟨t, ht, hts⟩ := s.2
      obtain ⟨k, hk⟩ := hT.2.1 ⟨(t : G), ht⟩
      refine ⟨k, Subtype.ext ?_⟩
      have h1 : t ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
      show (s : S3Wr) ^ 2 ^ k = 1
      rw [← hts, ← map_pow, h1, map_one]
    have hSidx : ¬ 2 ∣ S.index := by
      intro hd
      have h1 : S.index ∣ (T.subgroupOf H).index := Subgroup.index_map_dvd (T.subgroupOf H) hs
      exact hT.2.2 (hd.trans h1)
    have hS8 : Nat.card S = 8 := by
      obtain ⟨n, hn⟩ := hS2.exists_card_eq
      have h1 := Subgroup.card_mul_index S
      rw [S3Wr_card, hn] at h1
      have hn3 : n ≤ 3 := by
        by_contra hlt
        have : 2 ^ 4 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
        have : 16 ∣ 72 := by
          have h72 : 72 = 2 ^ n * S.index := h1.symm
          rw [h72]
          exact (by simpa using this : 16 ∣ 2 ^ n).mul_right _
        omega
      rw [hn]
      interval_cases n <;> omega
    have hconj : ∀ t ∈ T.subgroupOf H, ∀ k ∈ K, φ t * k * (φ t)⁻¹ ∈ K := by
      intro t ht k hk
      obtain ⟨y, hy, rfl⟩ := hk
      refine ⟨t * y * t⁻¹, ?_, by simp [map_mul, map_inv]⟩
      have h1 : (y : G) ∈ Y := hy
      have h2 := (Subgroup.mem_normalizer_iff.mp (hTY ht)) (y : G) |>.mp h1
      exact Subgroup.mem_subgroupOf.mpr (by simpa using h2)
    have hSK : S ≤ Subgroup.normalizer (K : Set S3Wr) := by
      rintro _ ⟨t, ht, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro k
      refine ⟨fun hk => hconj t ht k hk, fun hk => ?_⟩
      have := hconj t⁻¹ ((T.subgroupOf H).inv_mem ht) _ hk
      simpa [map_inv, mul_assoc] using this
    rcases oddSub_irreducible S hS2 hS8 K hKE hSK with hK0 | hK1
    · left
      refine le_antisymm (fun y hy => ?_) hY1
      have : φ ⟨y, hXH (hYX hy)⟩ ∈ K := ⟨⟨y, hXH (hYX hy)⟩, hy, rfl⟩
      rw [hK0, Subgroup.mem_bot] at this
      exact hker y (hYX hy) this
    · right
      refine le_antisymm hYX (fun x hx => ?_)
      have h1 : φ ⟨x, hXH hx⟩ ∈ K := by rw [hK1]; exact hφX x hx
      obtain ⟨y, hy, hyx⟩ := h1
      have hy' : (y : G) ∈ Y := hy
      have hxy : x * (y : G)⁻¹ ∈ pCoreOf 2 (oTwoUpper H) := by
        refine hker _ ((oTwoUpper H).mul_mem hx ((oTwoUpper H).inv_mem (hYX hy'))) ?_
        have : (⟨x * (y : G)⁻¹, hXH ((oTwoUpper H).mul_mem hx ((oTwoUpper H).inv_mem (hYX hy')))⟩ :
            ↥H) = ⟨x, hXH hx⟩ * y⁻¹ := rfl
        rw [this, map_mul, map_inv, hyx, mul_inv_cancel]
      have : x = (x * (y : G)⁻¹) * y := by group
      rw [this]
      exact Y.mul_mem (hY1 hxy) hy'

end CFSG.Quasithin.H13.L319
