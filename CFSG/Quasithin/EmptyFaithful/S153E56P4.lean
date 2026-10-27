module

public import CFSG.Quasithin.EmptyFaithful.S153E56P3

public section

namespace CFSG.Quasithin

namespace S153E56p

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S153E CFSG.Quasithin.S153E57
open scoped commutatorElement Pointwise

section Tilde

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {s : ℕ} {y t₁ : G}

abbrev Gz (T : Subgroup G) : Type := SecQuot (NZ T) (quasithinOmegaOneCenter T)

abbrev smk (T : Subgroup G) : ↥(NZ T) →* Gz T := secMk (NZ T) (quasithinOmegaOneCenter T)

omit [Finite G] in
theorem tildeOf_Z_eq_bot' (T : Subgroup G) :
    tildeOf (quasithinOmegaOneCenter T) (quasithinOmegaOneCenter T) = ⊥ := by
  ext y
  rw [Subgroup.mem_bot]
  constructor
  · intro hy
    obtain ⟨x, hxZ, rfl⟩ := mem_secImg.1 hy
    exact secMk_eq_one_iff.2 hxZ
  · rintro rfl
    exact one_mem _

omit [Finite G] in
theorem smk_mem_tilde_iff {A : Subgroup G} (hZA : quasithinOmegaOneCenter T ≤ A) {n : ↥(NZ T)} :
    smk T n ∈ tildeOf (quasithinOmegaOneCenter T) A ↔ (n : G) ∈ A :=
  secMk_mem_secImg_iff hZA

omit [Finite G] in
theorem mem_tilde_iff {A : Subgroup G} {w : Gz T} :
    w ∈ tildeOf (quasithinOmegaOneCenter T) A ↔ ∃ n : ↥(NZ T), (n : G) ∈ A ∧ smk T n = w :=
  mem_secImg

omit [Finite G] in
theorem card_tilde_eq' {A : Subgroup G} (hZA : quasithinOmegaOneCenter T ≤ A) (hAN : A ≤ NZ T) :
    Nat.card ↥(tildeOf (quasithinOmegaOneCenter T) A) = (quasithinOmegaOneCenter T).relIndex A := by
  have h := relIndex_secImg (A := NZ T) (B := quasithinOmegaOneCenter T) (T := quasithinOmegaOneCenter T)
    (H := A) le_rfl hZA hAN
  have hbot : secImg (NZ T) (quasithinOmegaOneCenter T) (quasithinOmegaOneCenter T) = ⊥ :=
    tildeOf_Z_eq_bot' T
  rw [hbot, Subgroup.relIndex_bot_left] at h
  exact h

theorem relIndex_eq_two_pow {A B : Subgroup G} (hA : IsPGroup 2 A) :
    B.relIndex A = 2 ^ mIdx A B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  have hmul := Subgroup.relIndex_mul_card B A
  have hdvd : B.relIndex A ∣ 2 ^ n := by
    rw [← hn, ← hmul]
    exact Dvd.intro _ rfl
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [mIdx, hk, padicValNat.prime_pow]

omit [Finite G] in
theorem two_mul_relIndex_Z {A : Subgroup G} (hZ : Nat.card (quasithinOmegaOneCenter T) = 2)
    (hZA : quasithinOmegaOneCenter T ≤ A) :
    (quasithinOmegaOneCenter T).relIndex A * 2 = Nat.card A := by
  have e := Subgroup.relIndex_mul_card (quasithinOmegaOneCenter T) A
  rw [inf_eq_left.2 hZA, hZ] at e
  exact e

variable (S : Ctx56 T Mc M V₁ V₂ t N₁ N₂ s y t₁)

include S

theorem E_isPGroup : IsPGroup 2 (Egp153 T M V₁ Mc y) :=
  isPGroup_of_isElemAbelian (E_elemAbelian S)

theorem E_le_NZ : Egp153 T M V₁ Mc y ≤ NZ T :=
  fun _ he => Mc_le_NZ S.cx (U_le_Mc S (E_le_U S he))

theorem E'_le_NZ : conjSubgroup (Egp153 T M V₁ Mc y) t₁ ≤ NZ T :=
  fun _ he => Mc_le_NZ S.cx (U_le_Mc S (E'_le_U S he))

theorem U_le_NZ' : UH153 T M V₁ Mc ≤ NZ T := fun _ hu => Mc_le_NZ S.cx (U_le_Mc S hu)

theorem card_tilde_E : Nat.card ↥(tildeOf (quasithinOmegaOneCenter T) (Egp153 T M V₁ Mc y)) =
    2 ^ (s + 2) := by
  rw [card_tilde_eq' (Z_le_E S) (E_le_NZ S), relIndex_eq_two_pow (E_isPGroup S), S.hG.E_sing.2.2]

theorem card_tilde_E' : Nat.card ↥(tildeOf (quasithinOmegaOneCenter T)
    (conjSubgroup (Egp153 T M V₁ Mc y) t₁)) = 2 ^ (s + 2) := by
  have h1 := two_mul_relIndex_Z (Z_card S.cx) (Z_le_E' S)
  have h2 := two_mul_relIndex_Z (Z_card S.cx) (Z_le_E S)
  have h3 : Nat.card (conjSubgroup (Egp153 T M V₁ Mc y) t₁) = Nat.card (Egp153 T M V₁ Mc y) :=
    card_conjSubgroup' _ _
  have h4 : (quasithinOmegaOneCenter T).relIndex (conjSubgroup (Egp153 T M V₁ Mc y) t₁) =
      (quasithinOmegaOneCenter T).relIndex (Egp153 T M V₁ Mc y) := by omega
  rw [card_tilde_eq' (Z_le_E' S) (E'_le_NZ S), h4, relIndex_eq_two_pow (E_isPGroup S),
    S.hG.E_sing.2.2]

theorem card_tilde_U : Nat.card ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) =
    2 ^ (2 * (s + 2)) := by
  have : IsPGroup 2 (UH153 T M V₁ Mc) := S.cx.hF.isPGroup_conjClosure
  rw [card_tilde_eq' (Z_le_U S) (U_le_NZ' S), relIndex_eq_two_pow this, S.hG.rank]

theorem tilde_E_le_U : tildeOf (quasithinOmegaOneCenter T) (Egp153 T M V₁ Mc y) ≤
    tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc) := secImg_mono (E_le_U S)

theorem tilde_E'_le_U : tildeOf (quasithinOmegaOneCenter T) (conjSubgroup (Egp153 T M V₁ Mc y) t₁) ≤
    tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc) := secImg_mono (E'_le_U S)

theorem tilde_inf_E : tildeOf (quasithinOmegaOneCenter T) (Egp153 T M V₁ Mc y) ⊓
    tildeOf (quasithinOmegaOneCenter T) (conjSubgroup (Egp153 T M V₁ Mc y) t₁) = ⊥ := by
  rw [eq_bot_iff]
  rintro w ⟨hw₁, hw₂⟩
  obtain ⟨n, hnE, rfl⟩ := mem_tilde_iff.1 hw₁
  have hn' : (n : G) ∈ conjSubgroup (Egp153 T M V₁ Mc y) t₁ := (smk_mem_tilde_iff (Z_le_E' S)).1 hw₂
  rw [Subgroup.mem_bot]
  exact secMk_eq_one_iff.2 (EEt S ⟨hnE, hn'⟩)

end Tilde

end S153E56p

end CFSG.Quasithin
