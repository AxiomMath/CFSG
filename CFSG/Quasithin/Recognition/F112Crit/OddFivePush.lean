module

public import CFSG.Quasithin.Recognition.F112Crit.APrime.ConcreteA
public import CFSG.Quasithin.Recognition.F112Crit.APrime.Lemma758Block
public import CFSG.Quasithin.Recognition.F112Crit.APrime.Lemma758W
public import CFSG.Quasithin.Recognition.F112Crit.APrime.Lemma758MFacts
public import CFSG.Quasithin.Recognition.F112Crit.APrime.Lemma758M

public section

namespace CFSG.Quasithin.F112Crit.APrime

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.F7

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T L : Subgroup G}

theorem AmalgamS3.false_of_le_normalizer_pCoreOf_inf (hA : AmalgamS3 G₀ G₁ G₂ T L)
    (hD : G₂ ≤ Subgroup.normalizer ((pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ : Subgroup G) : Set G))
    (h2 : (pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂).relIndex (pCoreOf 2 G₁) = 2) {V : Subgroup G}
    (hV : V ≤ coreIn (pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂) G₁)
    (hVn : G₂ ≤ Subgroup.normalizer (V : Set G))
    (hVr : ∀ r ∈ G₂, r ∉ G₁ → ∃ v ∈ V, r * v * r⁻¹ ≠ v) : False := by
  classical
  have hM : ParabolicA G₁ G₂ (conjClosure (pCoreOf 2 G₁) G₂) :=
    hA.parabolicA_conjClosure hD (hA.relIndex_conjClosure_pCoreOf h2 hD)
  obtain ⟨W, r, hWD, -, hWn, -, hQ₁W, hrG₂, hrG₁, hrD, hWcard, hWcent⟩ :=
    hM.exists_block hA
  have hV_le_D : V ≤ pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ := hV.trans (coreIn_le_right _ _)
  obtain ⟨v, hvV, hvr⟩ := hVr r hrG₂ hrG₁
  let c : G := r * v * r⁻¹ * v⁻¹
  have hcV : c ∈ V := by
    have hrN : r ∈ Subgroup.normalizer (V : Set G) := hVn hrG₂
    have hconj : r * v * r⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hrN v).mp hvV
    exact V.mul_mem hconj (V.inv_mem hvV)
  have hcW : c ∈ W := hrD v (hV_le_D hvV)
  have hc_ne : c ≠ 1 := by
    intro hc
    have hcv : r * v * r⁻¹ * v⁻¹ = 1 := hc
    have h1 : r * v * r⁻¹ = v := by
      calc r * v * r⁻¹ = (r * v * r⁻¹ * v⁻¹) * v := by group
        _ = 1 * v := by rw [hcv]
        _ = v := by simp
    exact hvr h1
  let c' : G := r * c * r⁻¹
  have hc'V : c' ∈ V := by
    have hrN : r ∈ Subgroup.normalizer (V : Set G) := hVn hrG₂
    exact (Subgroup.mem_normalizer_iff.mp hrN c).mp hcV
  have hc'W : c' ∈ W := by
    have hrN : r ∈ Subgroup.normalizer (W : Set G) := hWn hrG₂
    exact (Subgroup.mem_normalizer_iff.mp hrN c).mp hcW
  have hc'_ne : c' ≠ 1 := by
    intro hc'
    have hc'_eq : r * c * r⁻¹ = 1 := hc'
    apply hc_ne
    calc c = r⁻¹ * (r * c * r⁻¹) * r := by group
      _ = r⁻¹ * 1 * r := by rw [hc'_eq]
      _ = 1 := by simp
  have hc'_ne_c : c' ≠ c := by
    intro h
    have hc'_eq : r * c * r⁻¹ = c := h
    have hcomm : c ∈ Subgroup.centralizer ({r} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : r * c = c * r := by
        calc r * c = (r * c * r⁻¹) * r := by group
          _ = c * r := by rw [hc'_eq]
      exact h1.symm
    have hmem : c ∈ W ⊓ Subgroup.centralizer ({r} : Set G) := ⟨hcW, hcomm⟩
    rw [hWcent] at hmem
    exact hc_ne (Subgroup.mem_bot.mp hmem)
  have hcK : c ∈ V ⊓ W := ⟨hcV, hcW⟩
  have hc'K : c' ∈ V ⊓ W := ⟨hc'V, hc'W⟩
  have hKcard : Nat.card ↥(V ⊓ W) = 4 := by
    have hdvd : Nat.card ↥(V ⊓ W) ∣ 4 := by
      have h := Subgroup.card_dvd_of_le (H := V ⊓ W) (K := W) inf_le_right
      rwa [hWcard] at h
    have hdvd' : Nat.card ↥(V ⊓ W) ∣ 2 ^ 2 := by simpa using hdvd
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd'
    have hk012 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk012 with rfl | rfl | rfl
    · have hbot : V ⊓ W = ⊥ := Subgroup.card_eq_one.mp (by simpa using hk')
      exact absurd (Subgroup.mem_bot.mp (hbot ▸ hcK)) hc_ne
    · obtain ⟨y, _hy, huniq⟩ :=
        (Nat.card_eq_two_iff' (1 : ↥(V ⊓ W))).mp (by simpa using hk')
      have hcy : (⟨c, hcK⟩ : ↥(V ⊓ W)) = y :=
        huniq _ (fun h1 => hc_ne (Subtype.ext_iff.mp h1))
      have hc'y : (⟨c', hc'K⟩ : ↥(V ⊓ W)) = y :=
        huniq _ (fun h1 => hc'_ne (Subtype.ext_iff.mp h1))
      exfalso
      exact hc'_ne_c (Subtype.ext_iff.mp (hc'y.trans hcy.symm))
    · simpa using hk'
  have hKW : V ⊓ W = W := Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
  have hWV : W ≤ V := hKW ▸ inf_le_left
  have hW_le_core : W ≤ coreIn (pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂) G₁ := hWV.trans hV
  have hcore_bot : coreIn (pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂) G₁ = ⊥ :=
    hA.coreIn_eq_bot hW_le_core hrG₂ hrG₁ hrD
  have hWbot : W = ⊥ := le_bot_iff.mp (hcore_bot ▸ hW_le_core)
  apply hQ₁W
  rw [hWbot]
  have htop : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
    rw [Subgroup.centralizer_eq_top_iff_subset]
    intro x hx
    simp at hx
    subst hx
    exact Subgroup.one_mem _
  rw [htop]
  exact le_top

theorem false_of_le_normalizer_pCoreOf_inf_of_setting {L1 L2 S : Subgroup G}
    (hR : Hyp111R L1 L2 S) (hS3 : VS3 L1) (hS : S ≤ L1)
    (hD : P₁ L1 L2 S ≤ Subgroup.normalizer
      ((pCoreOf 2 (P₂ L1 L2 S) ⊓ pCoreOf 2 (P₁ L1 L2 S) : Subgroup G) : Set G))
    (h2 : (pCoreOf 2 (P₂ L1 L2 S) ⊓ pCoreOf 2 (P₁ L1 L2 S)).relIndex (pCoreOf 2 (P₂ L1 L2 S)) = 2)
    {V : Subgroup G}
    (hV : V ≤ coreIn (pCoreOf 2 (P₂ L1 L2 S) ⊓ pCoreOf 2 (P₁ L1 L2 S)) (P₂ L1 L2 S))
    (hVn : P₁ L1 L2 S ≤ Subgroup.normalizer (V : Set G))
    (hVr : ∀ r ∈ P₁ L1 L2 S, r ∉ P₂ L1 L2 S → ∃ v ∈ V, r * v * r⁻¹ ≠ v) : False :=
  (amalgamS3_of_setting hR hS3 hS).false_of_le_normalizer_pCoreOf_inf hD h2 hV hVn hVr

end CFSG.Quasithin.F112Crit.APrime

end
