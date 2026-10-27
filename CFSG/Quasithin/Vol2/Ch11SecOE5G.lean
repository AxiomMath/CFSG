module

public import CFSG.Quasithin.Vol2.Ch11SecOE5F
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall
public import CFSG.RankThree.PartOne.S12.TerminalWeylPerm

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.OE5

open CFSG.Open CFSG.Blueprint

variable {Q : Type} [Group Q] [Finite Q]

theorem card_sup_eq {S B : Subgroup Q} (hS : QuasithinUnique.IsSylowTwoOf S ⊤)
    (hS16 : Nat.card S = 16) (hQ : Nat.card Q = 126000) (hB : IsL24Sub S B) :
    Nat.card ↥(B ⊔ S) = 240 := by
  obtain ⟨m, hm⟩ := O11.card_sup hS.2.1 hB
  have h16 : 16 ∣ Nat.card ↥(B ⊔ S) := hS16 ▸ Subgroup.card_dvd_of_le le_sup_right
  have hdvd : Nat.card ↥(B ⊔ S) ∣ 126000 := hQ ▸ Subgroup.card_subgroup_dvd_card _
  rw [hm] at h16 hdvd ⊢
  have hm4 : m ≤ 4 := by
    by_contra h
    have := (Nat.mul_dvd_mul_left 15 (Nat.pow_dvd_pow 2 (show 5 ≤ m by omega))).trans hdvd
    norm_num at this
  interval_cases m <;> omega

theorem le_centralizer_of_eq_bot {S B : Subgroup Q} {z : Q}
    (hS : QuasithinUnique.IsSylowTwoOf S ⊤) (hS16 : Nat.card S = 16) (hQ : Nat.card Q = 126000)
    (hZN : ∀ N : Subgroup Q, N ≤ S → S ≤ Subgroup.normalizer (N : Set Q) → N ≠ ⊥ → z ∈ N)
    (hB : IsL24Sub S B) (hP1 : CFSG.pCore 2 ↥B = ⊥) : B ≤ Subgroup.centralizer {z} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hSB, F, _, _, hF, ⟨e⟩⟩ := id hB
  obtain ⟨eA⟩ := QuasithinUnique.Setup.Family.specialLinear_two_equiv_alternating_five F hF
  let eB : ↥B ≃* alternatingGroup (Fin 5) :=
    ((QuotientGroup.quotientMulEquivOfEq hP1).trans QuotientGroup.quotientBot).symm.trans
      (e.trans eA)
  have hcB : Nat.card B = 60 := by
    rw [card_eq_sixty_mul hB, hP1, Subgroup.card_bot]
  have hΓN : B ⊔ S ≤ Subgroup.normalizer (B : Set Q) := sup_le Subgroup.le_normalizer hSB
  have hYn : ∀ g ∈ B ⊔ S, ∀ y ∈ B, g * y * g⁻¹ ∈ B := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (hΓN hg) y).mp hy
  obtain ⟨π, hπB, hπk⟩ :=
    CFSG.RankThree.PartOne.TerminalPerm.exists_pi_of_equiv eB le_sup_left hYn
  have hΓ := card_sup_eq hS hS16 hQ hB
  have hr120 : Nat.card π.range ∣ 120 := by
    have h := Subgroup.card_subgroup_dvd_card π.range
    rwa [Nat.card_perm, Nat.card_fin] at h
  have hinjB : Function.Injective (π.comp (Subgroup.inclusion (le_sup_left : B ≤ B ⊔ S))) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    have h1 : π ⟨y, le_sup_left (a := B) y.2⟩ = 1 := hy
    rw [hπB y y.2] at h1
    have h2 : eB y = 1 := Subtype.ext h1
    exact Subgroup.mem_bot.mpr (eB.injective (h2.trans (map_one eB).symm))
  have hr60 : 60 ∣ Nat.card π.range := by
    have h1 : (π.comp (Subgroup.inclusion (le_sup_left : B ≤ B ⊔ S))).range ≤ π.range :=
      fun x ⟨y, hy⟩ => ⟨_, hy⟩
    have h2 := Subgroup.card_dvd_of_le h1
    rwa [← Nat.card_congr (MonoidHom.ofInjective hinjB).toEquiv, hcB] at h2
  have hk := Subgroup.card_mul_index π.ker
  rw [Subgroup.index_ker, hΓ] at hk
  have hrpos : 0 < Nat.card π.range := Nat.card_pos
  have hrle : Nat.card π.range ≤ 120 := Nat.le_of_dvd (by norm_num) hr120
  obtain ⟨a, ha⟩ := hr60
  have hcases : Nat.card π.range = 60 ∨ Nat.card π.range = 120 := by
    rcases a with _ | _ | _ | a <;> omega
  have hk2 : IsPGroup 2 π.ker := by
    rcases hcases with h | h
    · rw [h] at hk
      exact IsPGroup.of_card (n := 2) (by omega)
    · rw [h] at hk
      exact IsPGroup.of_card (n := 1) (by omega)
  set K' : Subgroup Q := π.ker.map (B ⊔ S).subtype with hK'
  have hK'2 : IsPGroup 2 K' := hk2.map _
  have hK'ne : K' ≠ ⊥ := by
    rw [hK', Ne, Subgroup.map_eq_bot_iff_of_injective _ (B ⊔ S).subtype_injective]
    intro h
    rw [h, Subgroup.card_bot] at hk
    omega
  have hSK' : S ≤ Subgroup.normalizer (K' : Set Q) := by
    have hKΓ : K' ≤ B ⊔ S := Subgroup.map_subtype_le _
    have hn : (K'.subgroupOf (B ⊔ S)).Normal := by
      have h : K'.subgroupOf (B ⊔ S) = π.ker :=
        Subgroup.comap_map_eq_self_of_injective (B ⊔ S).subtype_injective _
      rw [h]
      exact π.normal_ker
    exact le_sup_right.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKΓ).mp hn)
  obtain ⟨k, hk1, rfl⟩ := hZN K' (le_of_isPGroup hS hK'2 hSK') hSK' hK'ne
  intro b hb
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (hπk k hk1 b hb).symm

theorem le_centralizer {S B : Subgroup Q} {z : Q}
    (hS : QuasithinUnique.IsSylowTwoOf S ⊤) (hS16 : Nat.card S = 16) (hQ : Nat.card Q = 126000)
    (hZN : ∀ N : Subgroup Q, N ≤ S → S ≤ Subgroup.normalizer (N : Set Q) → N ≠ ⊥ → z ∈ N)
    (hB : IsL24Sub S B) : B ≤ Subgroup.centralizer {z} := by
  by_cases hP1 : CFSG.pCore 2 ↥B = ⊥
  · exact le_centralizer_of_eq_bot hS hS16 hQ hZN hB hP1
  · exact le_centralizer_of_ne_bot hS hQ hZN hB hP1

theorem l24Unique_of_data {S : Subgroup Q} {z : Q}
    (hS : QuasithinUnique.IsSylowTwoOf S ⊤) (hS16 : Nat.card S = 16) (hQ : Nat.card Q = 126000)
    (hzc : ∀ x ∈ S, x * z = z * x)
    (hZ : ∀ y ∈ S, (∀ x ∈ S, x * y = y * x) → y = 1 ∨ y = z)
    (hC : Nat.card (Subgroup.centralizer {z}) ≤ 240) : O11.L24Unique S := by
  have hZN : ∀ N : Subgroup Q, N ≤ S → S ≤ Subgroup.normalizer (N : Set Q) → N ≠ ⊥ → z ∈ N :=
    fun N hNS hSN hN => mem_of_normal hS.2.1 hZ hNS hSN hN
  have key : ∀ B, IsL24Sub S B → B ⊔ S = Subgroup.centralizer {z} := by
    intro B hB
    have hle : B ⊔ S ≤ Subgroup.centralizer {z} := sup_le (le_centralizer hS hS16 hQ hZN hB)
      (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hzc x hx))
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_sup_eq hS hS16 hQ hB]; exact hC)
  intro B₁ B₂ h₁ h₂
  exact O11.eq_of_sup_eq hS.2.1 h₁ h₂ ((key B₁ h₁).trans (key B₂ h₂).symm)

end CFSG.Quasithin.Vol2.Ch11.SecS.OE5
