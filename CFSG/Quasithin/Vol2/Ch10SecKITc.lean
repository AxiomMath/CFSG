module

public import CFSG.Quasithin.Vol2.Ch10SecKITb
public import CFSG.Quasithin.Background.F9Comp
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem perfectCore_eq_of_le_sup {K₀ Q H : Subgroup G}
    (hKQ : K₀ ≤ Subgroup.normalizer (Q : Set G)) (hQ : IsPGroup 2 Q) (hK : ⁅K₀, K₀⁆ = K₀)
    (hKH : K₀ ≤ H) (hHK : H ≤ K₀ ⊔ Q) (hHN : H ≤ Subgroup.normalizer (K₀ : Set G)) :
    perfectCore H = K₀ := by
  refine le_antisymm ?_ (le_perfectCore_of_perfect hKH hK)
  have hsup : H = K₀ ⊔ (H ⊓ Q) := by
    refine le_antisymm (fun a ha => ?_) (sup_le hKH inf_le_left)
    have ha' : a ∈ ((K₀ ⊔ Q : Subgroup G) : Set G) := hHK ha
    rw [Subgroup.coe_mul_of_left_le_normalizer_right K₀ Q hKQ] at ha'
    obtain ⟨k, hk, q, hq, rfl⟩ := ha'
    have hqH : q ∈ H := by
      have : q = k⁻¹ * (k * q) := by group
      rw [this]
      exact H.mul_mem (H.inv_mem (hKH hk)) ha
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right ⟨hqH, hq⟩)
  have hs : Group.IsSolvable ↥(H ⊓ Q) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := (hQ.to_le (inf_le_right : H ⊓ Q ≤ Q)).isNilpotent
    infer_instance
  exact perfectCore_le_of_sup_solvable hKH
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hHN) hsup hs

theorem le_normalizer_aux {K Q : Subgroup G} (hKQ : K ≤ Subgroup.normalizer (Q : Set G))
    (hQ : IsPGroup 2 Q) (hK : ⁅K, K⁆ = K) :
    ∀ {A H : Subgroup G}, IsSubnormal A H → H ≤ K ⊔ Q → K ≤ A →
      A ≤ Subgroup.normalizer (K : Set G) → H ≤ Subgroup.normalizer (K : Set G) := by
  intro A H hA
  induction hA with
  | refl => exact fun _ _ h => h
  | @step A B C hAB hAn hBC ih =>
    intro hCK hKA hAN
    refine ih hCK (hKA.trans hAB) ?_
    have hcore := perfectCore_eq_of_le_sup hKQ hQ hK hKA
      (hAB.trans ((A3.subnormal_le hBC).trans hCK)) hAN
    have hBA : B ≤ Subgroup.normalizer (A : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hAB).mp hAn
    exact hBA.trans (hcore ▸ normalizer_le_normalizer_perfectCore A)

theorem le_normalizer_of_subnormal_sup {K Q H : Subgroup G}
    (hKQ : K ≤ Subgroup.normalizer (Q : Set G)) (hQ : IsPGroup 2 Q) (hK : ⁅K, K⁆ = K)
    (hHK : H ≤ K ⊔ Q) (hsub : IsSubnormal K H) : H ≤ Subgroup.normalizer (K : Set G) :=
  le_normalizer_aux hKQ hQ hK hsub hHK le_rfl Subgroup.le_normalizer

variable {M T L X : Subgroup G} {n : ℕ}

theorem pCoreOf_le_of_cComp (hT : IsSylowTwoOf T M) (hL : L ∈ cComp M) : pCoreOf 2 L ≤ T :=
  (pCoreOf_le_pCoreOf_of_isSubnormal (subnormal_of_mem_cComp hL)).trans
    (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hT)

theorem pCoreOf_le_normalizer (hT : IsSylowTwoOf T M) (hL : L ∈ cComp M) (hX : X ∈ lFamily T)
    (hXL : X ≤ L) : pCoreOf 2 L ≤ Subgroup.normalizer (X : Set G) := by
  have hX' : X ∈ cComp (X ⊔ T) := hX
  have hQT := pCoreOf_le_of_cComp hT hL
  have hXQ : X ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    hXL.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
  have hQ : IsPGroup 2 (pCoreOf 2 L) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hsub : IsSubnormal X (X ⊔ pCoreOf 2 L) :=
    A3.subnormal_of_le_of_le (subnormal_of_mem_cComp hX') le_sup_left (sup_le_sup_left hQT X)
  exact le_sup_right.trans
    (le_normalizer_of_subnormal_sup hXQ hQ (perfect_of_mem_cComp hX') le_rfl hsub)

theorem commutator_le_inf (hT : IsSylowTwoOf T M) (hL : L ∈ cComp M) (hX : X ∈ lFamily T)
    (hXL : X ≤ L) : ⁅pCoreOf 2 L, X⁆ ≤ X ⊓ pCoreOf 2 L := by
  rw [inf_comm]
  exact commutator_le_inf_of_normalizes (pCoreOf_le_normalizer hT hL hX hXL)
    (hXL.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L))

theorem IsNatBlock.inf_cases (h : IsNatBlock X n) (hn : 2 ≤ n) (hXL : X ≤ L) :
    X ⊓ pCoreOf 2 L = ⊥ ∨ X ⊓ pCoreOf 2 L = blockU X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 ↥(X ⊓ pCoreOf 2 L) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le inf_le_right
  have hN : X ≤ Subgroup.normalizer ((X ⊓ pCoreOf 2 L : Subgroup G) : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hg, hXL.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L) hg⟩
  rcases h.normal_cases hn inf_le_left hN with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · exfalso
    have h2 : IsPGroup 2 ↥X := by rw [← h1]; exact hP
    have hq := h.card_quot
    obtain ⟨k, hk⟩ := (IsPGroup.to_quotient h2 (CFSG.pCore 2 ↥X)).exists_card_eq
    rw [hq] at hk
    have hodd : Odd (Ch11.SecA.oSL2 n) := by
      unfold Ch11.SecA.oSL2
      exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
    have h3 : Ch11.SecA.oSL2 n ∣ 2 ^ k := hk ▸ dvd_mul_left _ _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
    have h5 : 3 ≤ Ch11.SecA.oSL2 n := by
      unfold Ch11.SecA.oSL2
      have : 2 ^ 2 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rcases j with _ | j
    · rw [hj] at h5
      norm_num at h5
    · rw [hj, pow_succ] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_two.mul_left _)

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KH
