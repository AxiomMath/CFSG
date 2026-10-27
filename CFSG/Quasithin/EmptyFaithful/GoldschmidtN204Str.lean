module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtN204Elem
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ExclNB
public import CFSG.Quasithin.EmptyFaithful.S151ZB
public import CFSG.Quasithin.Recognition.GoldschmidtF112FA5Alt
public import CFSG.RankThree.PartOne.K1214.Basic
public import CFSG.Quasithin.EmptyFaithful.S152He9V

public section

namespace CFSG.Quasithin.He9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.N204
open scoped commutatorElement Pointwise

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def g1Of (T Mc M K₁ : Subgroup G) : Subgroup G :=
  l1Of T Mc M ⊔ sOf T K₁ ⊔ borelOf K₁ (sOf T K₁)

@[expose] def g2Of (T K₁ : Subgroup G) : Subgroup G := K₁ ⊔ sOf T K₁

theorem relIndex_sup_dvd_card {A B : Subgroup G} (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    B.relIndex (A ⊔ B) ∣ Nat.card A := by
  have h1 := Subgroup.relIndex_mul_card (H := B) (K := A ⊔ B)
  rw [inf_of_le_left le_sup_right] at h1
  have h2 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hB
  have hB0 : 0 < Nat.card B := Nat.card_pos
  have h3 : B.relIndex (A ⊔ B) * Nat.card (A ⊓ B : Subgroup G) * Nat.card B =
      Nat.card A * Nat.card B := by
    rw [← h2, ← h1]
    ring
  have h4 : B.relIndex (A ⊔ B) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A :=
    Nat.eq_of_mul_eq_mul_right hB0 h3
  exact ⟨_, h4.symm⟩

namespace Ctx15204

variable {T Mc M H K₁ K₂ : Subgroup G} {π : ↥H →* W5} (c : Ctx15204 T Mc M H K₁ K₂ π)

include c

theorem B₂_le_G₀ : borelOf K₁ (sOf T K₁) ≤ g0Of T Mc M K₁ := (F1.borelOf_le _ _).trans K₁_le_G₀

theorem G₁_le_G₀ : g1Of T Mc M K₁ ≤ g0Of T Mc M K₁ :=
  sup_le (sup_le (le_sup_left.trans le_sup_left) S_le_G₀) c.B₂_le_G₀

theorem G₂_le_G₀ : g2Of T K₁ ≤ g0Of T Mc M K₁ := sup_le K₁_le_G₀ S_le_G₀

theorem G₁_le_M : g1Of T Mc M K₁ ≤ M :=
  sup_le (sup_le c.L₁_le_M c.S_le_M) (fun _ hx => (c.borel₂_le_HM hx).2)

theorem B₂_le_normalizer_Y : borelOf K₁ (sOf T K₁) ≤ Subgroup.normalizer (yOf152 T Mc M : Set G) :=
  fun _ hx => c.inf_normalizer_Y (c.borel₂_le_HM hx)

theorem S_le_normalizer_B₂ :
    sOf T K₁ ≤ Subgroup.normalizer (borelOf K₁ (sOf T K₁) : Set G) := by
  have hR : sOf T K₁ ≤ Subgroup.normalizer ((sOf T K₁ ⊓ K₁ : Subgroup G) : Set G) :=
    Rk2.le_normalizer_inf Subgroup.le_normalizer S_le_normalizer_K₁
  exact Rk2.le_normalizer_inf (A := sOf T K₁) (X := K₁)
    (Y := Subgroup.normalizer ((sOf T K₁ ⊓ K₁ : Subgroup G) : Set G)) S_le_normalizer_K₁
    (hR.trans Subgroup.le_normalizer)

theorem S_le_normalizer_YB₂ :
    sOf T K₁ ≤ Subgroup.normalizer ((yOf152 T Mc M ⊔ borelOf K₁ (sOf T K₁) : Subgroup G) : Set G) :=
  fun s hs => by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (c.S_le_normalizer_Y hs),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (c.S_le_normalizer_B₂ hs)]

theorem G₁_eq : g1Of T Mc M K₁ = (yOf152 T Mc M ⊔ borelOf K₁ (sOf T K₁)) ⊔ sOf T K₁ := by
  unfold g1Of l1Of
  apply le_antisymm
  · exact sup_le (sup_le (sup_le (le_sup_left.trans le_sup_left)
      (c.rc_le_S.trans le_sup_right)) le_sup_right)
      (le_sup_right.trans le_sup_left)
  · exact sup_le (sup_le (le_sup_left.trans (le_sup_left.trans le_sup_left))
      le_sup_right) (le_sup_right.trans le_sup_left)

theorem card_Y_eq : ∃ a : ℕ, Nat.card ↥(yOf152 T Mc M) = 5 * 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h5 := c.y.relIndex_five
  have h := Subgroup.relIndex_mul_card (H := pCoreOf 2 (yOf152 T Mc M)) (K := yOf152 T Mc M)
  rw [inf_of_le_left (pCoreOf_le 2 _), h5] at h
  obtain ⟨a, ha⟩ := (pCoreOf_isPGroup 2 (yOf152 T Mc M)).exists_card_eq
  exact ⟨a, by rw [← h, ha]⟩

theorem not_dvd_card_Y {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h5 : p ≠ 5) :
    ¬ p ∣ Nat.card ↥(yOf152 T Mc M) := by
  obtain ⟨a, ha⟩ := c.card_Y_eq
  rw [ha]
  intro hd
  rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
  · exact h5 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)
  · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))

theorem not_five_dvd_card_B₂ : ¬ 5 ∣ Nat.card ↥(borelOf K₁ (sOf T K₁)) := by
  obtain ⟨e⟩ := c.quot_K₁
  obtain ⟨D, hDB, hD3, hDR, hsup⟩ := FA5.exists_cartan_three c.sylow_K₁ e
  have hnorm : D ≤ Subgroup.normalizer ((sOf T K₁ ⊓ K₁ : Subgroup G) : Set G) :=
    hDB.trans (F1.borelOf_le_normalizer K₁ (sOf T K₁))
  have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (A := sOf T K₁ ⊓ K₁) (B := D) hnorm
  rw [hsup, inf_comm, hDR, Subgroup.card_bot, hD3, mul_one] at hprod
  obtain ⟨a, ha⟩ := ((c.S_pgroup.to_le inf_le_left : IsPGroup 2 ↥(sOf T K₁ ⊓ K₁))).exists_card_eq
  rw [hprod, ha]
  intro hd
  have : Nat.Prime 5 := by norm_num
  rcases (Nat.Prime.dvd_mul this).mp hd with h | h
  · have := (Nat.prime_dvd_prime_iff_eq this Nat.prime_two).mp (this.dvd_of_dvd_pow h)
    omega
  · omega

theorem exists_conj_mem_B₂ {p k : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h5 : p ≠ 5) {x : G}
    (hx : x ∈ yOf152 T Mc M ⊔ borelOf K₁ (sOf T K₁)) (hxk : x ^ p ^ k = 1) :
    ∃ g ∈ yOf152 T Mc M ⊔ borelOf K₁ (sOf T K₁), g⁻¹ * x * g ∈ borelOf K₁ (sOf T K₁) := by
  have : Fact p.Prime := ⟨hp⟩
  refine N204.exists_conj_mem_of_not_dvd ?_ hx hxk
  intro hd
  exact c.not_dvd_card_Y hp h2 h5 (hd.trans (relIndex_sup_dvd_card c.B₂_le_normalizer_Y))

theorem exists_conj_mem_Y {k : ℕ} {x : G} (hx : x ∈ yOf152 T Mc M ⊔ borelOf K₁ (sOf T K₁))
    (hxk : x ^ 5 ^ k = 1) :
    ∃ g ∈ yOf152 T Mc M ⊔ borelOf K₁ (sOf T K₁), g⁻¹ * x * g ∈ yOf152 T Mc M := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine N204.exists_conj_mem_of_not_dvd ?_ hx hxk
  intro hd
  have h1 : (yOf152 T Mc M).relIndex (yOf152 T Mc M ⊔ borelOf K₁ (sOf T K₁)) =
      (yOf152 T Mc M).relIndex (borelOf K₁ (sOf T K₁)) := zb_relIndex_sup c.B₂_le_normalizer_Y
  rw [h1] at hd
  exact c.not_five_dvd_card_B₂ (hd.trans (Subgroup.relIndex_dvd_card _ _))

end Ctx15204

end CFSG.Quasithin.He9
