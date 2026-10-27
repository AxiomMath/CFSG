module

public import CFSG.Quasithin.Vol2.GoldschmidtF431AGMain

public section

namespace CFSG.Quasithin.H13.F431.AG

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

variable {K : Type*} [Group K]

theorem exists_parabolic_of_isAGMember [Finite K] {X T D : Subgroup K} [X.Normal]
    (hBT : BorelTitsIn X) (hT : IsSylowTwoOf T X) (hD : IsAGMember T D) :
    ∃ P : Subgroup K, P ≤ X ∧ P ≠ X ∧ X ⊓ Subgroup.normalizer (T : Set K) ≤ P ∧
      ∀ φ ∈ Subgroup.normalizer (D : Set K),
        ∃ p ∈ P, p⁻¹ * φ ∈ Subgroup.normalizer (T : Set K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTX : T ≤ X := hT.1
  have hTp : IsPGroup 2 T := hT.2.1
  have hDT : D ≤ T := hD.1
  have hD1 : D ≠ ⊥ := hD.2.1
  have hsyl : IsSylowTwoOf (T ⊓ Subgroup.normalizer (D : Set K))
      (Subgroup.normalizer (D : Set K)) := hD.2.2.1
  set N := Subgroup.normalizer (D : Set K) with hN
  have hDX : D ≤ X := hDT.trans hTX
  have hDp : IsPGroup 2 D := hTp.to_le hDT
  have hNX : N ≤ Subgroup.normalizer (X : Set K) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  have hNN0 : N ≤ Subgroup.normalizer ((X ⊓ N : Subgroup K) : Set K) :=
    F7.le_normalizer_inf hNX Subgroup.le_normalizer
  have hcore : pCoreOf 2 (X ⊓ N) ≤ D := by
    have h1 : N ≤ Subgroup.normalizer (pCoreOf 2 (X ⊓ N) : Set K) :=
      hNN0.trans (normalizer_le_normalizer_pCoreOf 2 _)
    have h2 : pCoreOf 2 (X ⊓ N) ≤ pCoreOf 2 N :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans inf_le_right) h1
        (pCoreOf_isPGroup 2 _)
    exact h2.trans (pCoreOf_normalizer_le_of_isAGMember hTp hD)
  obtain ⟨S, P, hSX, hPX, hPne, hN0P, -, hDP, hSP⟩ := hBT D hDX hD1 hDp
  have hQp : IsPGroup 2 (pCoreOf 2 P) := pCoreOf_isPGroup 2 P
  have hPQ : P ≤ Subgroup.normalizer (pCoreOf 2 P : Set K) := le_normalizer_pCoreOf 2 P
  have hQN : pCoreOf 2 P ⊓ N ≤ D := by
    have hle : pCoreOf 2 P ⊓ N ≤ X ⊓ N :=
      inf_le_inf_right N ((pCoreOf_le 2 P).trans hPX)
    have hnorm : X ⊓ N ≤ Subgroup.normalizer ((pCoreOf 2 P ⊓ N : Subgroup K) : Set K) :=
      F7.le_normalizer_inf (hN0P.trans hPQ) (inf_le_right.trans Subgroup.le_normalizer)
    exact (le_pCoreOf_of_le_normalizer 2 hle hnorm (hQp.to_le inf_le_left)).trans hcore
  have hDQ : D = pCoreOf 2 P := eq_of_inf_normalizer_le hQp hDP hQN
  have hPN : P ≤ N := by rw [hN, hDQ]; exact hPQ
  have hPeq : P = X ⊓ N := le_antisymm (le_inf hPX hPN) hN0P
  have hT'N0 : T ⊓ N ≤ X ⊓ N := inf_le_inf_right N hTX
  have hT'syl : IsSylowTwoOf (T ⊓ N) P := by
    rw [hPeq]
    exact F7.isSylowTwoOf_mono_right hsyl hT'N0 inf_le_right
  have hSle : S ≤ P := fun s hs => hSP (Subgroup.mem_inf.mpr ⟨hSX.1 hs, Subgroup.le_normalizer hs⟩)
  have hPodd : ¬ 2 ∣ P.relIndex X := by
    intro hd
    have h := Subgroup.relIndex_mul_relIndex S P X hSle hPX
    exact F7.isSylowTwoOf_odd_relIndex hSX (h ▸ hd.mul_left _)
  have hT'X : IsSylowTwoOf (T ⊓ N) X := by
    refine F7.isSylowTwoOf_of_relIndex (hT'syl.1.trans hPX) (hTp.to_le inf_le_left) ?_
    intro hd
    rw [← Subgroup.relIndex_mul_relIndex (T ⊓ N) P X hT'syl.1 hPX] at hd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd with h | h
    · exact F7.isSylowTwoOf_odd_relIndex hT'syl h
    · exact hPodd h
  have hTeq : T ⊓ N = T := eq_of_le_of_isSylowTwoOf hT'X inf_le_left hTX hTp
  have hTP : T ≤ P := hTeq ▸ hT'syl.1
  have hTsyl : IsSylowTwoOf T P := F7.isSylowTwoOf_mono_right hT hTP hPX
  refine ⟨P, hPX, hPne, inf_normalizer_le_of_isSylowTwoOf hPX hSX hT hTP hSP, ?_⟩
  intro φ hφ
  have hφP : φ ∈ Subgroup.normalizer (P : Set K) := by rw [hPeq]; exact hNN0 hφ
  have hle : conjSub φ T ≤ P := (conjSub_mono φ hTP).trans fun x hx => by
    rw [mem_conjSub] at hx
    have e : φ * (φ⁻¹ * x * φ) * φ⁻¹ = x := by group
    exact e ▸ ((Subgroup.mem_normalizer_iff.mp hφP _).mp hx)
  obtain ⟨p, hpP, hpT⟩ := F7.isSylowTwoOf_exists_conj_le hTsyl hle (F7.isPGroup_conjSub hTp)
  have heq : conjSub φ T = conjSub p T := conjSub_eq_of_le hpT
  refine ⟨p, hpP, mem_normalizer_of_conjSub_eq ?_⟩
  rw [conjSub_mul, heq, conjSub_conjSub_inv]

theorem normalizer_le_of_isAGMember [Finite K] {X T D P₀ P₁ : Subgroup K} [X.Normal]
    (hBT : BorelTitsIn X) (hT : IsSylowTwoOf T X)
    (habove : ∀ A : Subgroup K, A ≤ X → X ⊓ Subgroup.normalizer (T : Set K) ≤ A → A ≠ X →
      A ≤ P₀ ∨ A ≤ P₁)
    (hfix₀ : Subgroup.normalizer (T : Set K) ≤ Subgroup.normalizer (P₀ : Set K))
    (hfix₁ : Subgroup.normalizer (T : Set K) ≤ Subgroup.normalizer (P₁ : Set K))
    (hD : IsAGMember T D) :
    Subgroup.normalizer (D : Set K) ≤ Subgroup.normalizer (P₀ : Set K) ∨
      Subgroup.normalizer (D : Set K) ≤ Subgroup.normalizer (P₁ : Set K) := by
  obtain ⟨P, hPX, hPne, hPT, hfr⟩ := exists_parabolic_of_isAGMember hBT hT hD
  rcases habove P hPX hPT hPne with h | h
  · refine Or.inl fun φ hφ => ?_
    obtain ⟨p, hp, hpn⟩ := hfr φ hφ
    have := (Subgroup.normalizer (P₀ : Set K)).mul_mem (Subgroup.le_normalizer (h hp)) (hfix₀ hpn)
    simpa using this
  · refine Or.inr fun φ hφ => ?_
    obtain ⟨p, hp, hpn⟩ := hfr φ hφ
    have := (Subgroup.normalizer (P₁ : Set K)).mul_mem (Subgroup.le_normalizer (h hp)) (hfix₁ hpn)
    simpa using this

end CFSG.Quasithin.H13.F431.AG
