module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompS
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompE
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompR

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

namespace S143

namespace InspW2

section Three

variable {X : Type*} [Group X] [Finite X]

theorem false_of_three_components (hO : CFSG.pPrimeCore 2 X = ⊥) {w : X}
    (hwc : ∀ g : X, g * w = w * g) (hw1 : w ≠ 1) (hwP : w ∈ CFSG.pCore 2 X)
    (hP : Nat.card (CFSG.pCore 2 X) ≤ 4) {T : Subgroup X} (hT2 : IsPGroup 2 T)
    (hTi : ¬ 2 ∣ T.index) (hTcard : Nat.card T ≤ 128) {u : X} (huT : u ∈ T)
    (hu : u * u ∉ CFSG.pCore 2 X) {L₁ L₂ L₃ : Subgroup X} (h₁ : CFSG.IsComponent L₁)
    (h₂ : CFSG.IsComponent L₂) (h₃ : CFSG.IsComponent L₃) (h12 : L₁ ≠ L₂) (h13 : L₁ ≠ L₃)
    (h23 : L₂ ≠ L₃) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := CFSG.pCore 2 X with hPdef
  set φ := QuotientGroup.mk' P with hφ
  have hφs : Function.Surjective φ := QuotientGroup.mk'_surjective P
  have hP2 : 2 ≤ Nat.card P := by
    have hne : P ≠ ⊥ := fun hb => hw1 (by rw [hb, Subgroup.mem_bot] at hwP; exact hwP)
    have := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
    omega
  have hPT : P ≤ T := fun p hp =>
    (IsPGroup.mem_toSylow hT2 hTi).mp
      ((CFSG.pCore_isPGroup (p := 2) (G := X)).le_sylow_of_normal (hT2.toSylow hTi) hp)
  have hcardT : Nat.card ↥(T.map φ) * Nat.card P = Nat.card T := by
    have h1 := Subgroup.relIndex_ker (K := T) φ
    rw [hφ, QuotientGroup.ker_mk'] at h1
    have h2 := Subgroup.relIndex_mul_card (H := P) (K := T)
    rw [inf_eq_left.mpr hPT, h1] at h2
    exact h2
  have hT64 : Nat.card ↥(T.map φ) ≤ 64 := by nlinarith
  have hT2' : IsPGroup 2 ↥(T.map φ) := hT2.map φ
  have hTi' : ¬ 2 ∣ (T.map φ).index := fun h2 => hTi (h2.trans (Subgroup.index_map_dvd T hφs))
  have hbound : ∀ B : Subgroup (X ⧸ P), IsPGroup 2 B → Nat.card B ≤ 64 := by
    intro B hB
    obtain ⟨Q, hQ⟩ := hB.exists_le_sylow
    let ST : Sylow 2 (X ⧸ P) := hT2'.toSylow hTi'
    have hQST : Nat.card Q = Nat.card ST :=
      (Sylow.card_eq_multiplicity Q).trans (Sylow.card_eq_multiplicity ST).symm
    calc Nat.card B ≤ Nat.card Q := Subgroup.card_le_of_le hQ
      _ = Nat.card ST := hQST
      _ = Nat.card ↥(T.map φ) := rfl
      _ ≤ 64 := hT64
  obtain ⟨hp₁, hn₁, hc₁⟩ := map_component_facts hO hwc hw1 hwP hP h₁
  obtain ⟨hp₂, hn₂, -⟩ := map_component_facts hO hwc hw1 hwP hP h₂
  obtain ⟨hp₃, hn₃, hc₃⟩ := map_component_facts hO hwc hw1 hwP hP h₃
  have hcommute : ∀ {A B : Subgroup X}, CFSG.IsComponent A → CFSG.IsComponent B → A ≠ B →
      ∀ a ∈ A.map φ, ∀ b ∈ B.map φ, a * b = b * a := by
    intro A B hA hB hAB a ha b hb
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    obtain ⟨b₀, hb₀, rfl⟩ := hb
    rcases CFSG.LocalCores.distinct_components_commute hA hB with h | h
    · exact absurd h hAB
    · rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
      have := Subgroup.mem_centralizer_iff.mp (h ha₀) b₀ hb₀
      rw [← map_mul, ← map_mul, this]
  obtain ⟨A, hA2, hAcard, hAexp⟩ := exists_exp_two_of_three hp₁ hp₂ hp₃ hn₁ hn₂ hn₃ hc₁ hc₃
    (hcommute h₁ h₂ h12) (hcommute h₁ h₃ h13) (hcommute h₂ h₃ h23) hbound
  have hSyl : IsSylowTwoOf (T.map φ) ⊤ := by
    refine ⟨le_top, hT2', fun h2 => hTi' ?_⟩
    have : ((T.map φ).subgroupOf ⊤).index = (T.map φ).index := Subgroup.relIndex_top_right _
    rwa [this] at h2
  obtain ⟨c, -, hc⟩ := exists_conj_le_sylow hSyl hA2 le_top
  have hle : A.map (MulAut.conj c).toMonoidHom ≤ T.map φ := by
    rintro _ ⟨s, hs, rfl⟩
    exact hc s hs
  have hcA : Nat.card ↥(A.map (MulAut.conj c).toMonoidHom) = 64 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, hAcard]
  have heq : A.map (MulAut.conj c).toMonoidHom = T.map φ :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcA]; exact hT64)
  have huT' : φ u ∈ A.map (MulAut.conj c).toMonoidHom := by
    rw [heq]; exact ⟨u, huT, rfl⟩
  obtain ⟨a, ha, hau⟩ := huT'
  have h1 : φ (u * u) = 1 := by
    rw [map_mul, ← hau]
    have : (MulAut.conj c) a * (MulAut.conj c) a = 1 := by
      rw [← map_mul, hAexp a ha, map_one]
    exact this
  exact hu ((QuotientGroup.eq_one_iff _).mp h1)

end Three

end InspW2

end S143

end CFSG.Quasithin
