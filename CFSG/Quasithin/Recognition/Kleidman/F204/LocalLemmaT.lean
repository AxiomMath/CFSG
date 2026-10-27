module

public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalTvQ
public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalDich

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

theorem four_le_relIndex_of_no_five (F : Frame L1 L2 S D X) {δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hδ : vtype δ = false) {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hN : stab δ ≤ Subgroup.normalizer (V : Set G))
    (hno5 : ∀ e ∈ stab δ, e ∈ Subgroup.centralizer (V : Set G) → e ^ 5 ∈ Qv δ → e ∈ Qv δ)
    {x : G} (hx : x ∈ stab δ) (hxQ : x ∉ Qv δ) {k : ℕ} (hxk : x ^ 2 ^ k ∈ Qv δ) :
    4 ≤ (V ⊓ Subgroup.centralizer {x}).relIndex V := by
  obtain ⟨j, haQ, ha2⟩ := exists_pow_sq_mem (Qv δ) hxQ hxk
  have hastab : x ^ j ∈ stab δ := (stab δ).pow_mem hx j
  have hle : V ⊓ Subgroup.centralizer {x} ≤ V ⊓ Subgroup.centralizer {x ^ j} := by
    intro v hv
    have hc : Commute x v := Subgroup.mem_centralizer_iff.mp hv.2 x rfl
    exact ⟨hv.1, Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff.mp hh]; exact (hc.pow_left j).eq⟩
  have hrel : (V ⊓ Subgroup.centralizer {x ^ j}).relIndex V ≤
      (V ⊓ Subgroup.centralizer {x}).relIndex V :=
    Subgroup.relIndex_le_of_le_left (L := V) hle Subgroup.index_ne_zero_of_finite
  suffices h : 3 ≤ (V ⊓ Subgroup.centralizer {x ^ j}).relIndex V by
    have hp2 : IsPGroup 2 V := F7.isPGroup_of_isElemAbelian hV
    have hdvd : (V ⊓ Subgroup.centralizer {x ^ j}).relIndex V ∣ Nat.card V := by
      have := Subgroup.relIndex_mul_card (H := V ⊓ Subgroup.centralizer {x ^ j}) (K := V)
      rw [inf_eq_left.mpr inf_le_left] at this
      exact Dvd.intro _ this
    obtain ⟨n, hn⟩ := hp2.exists_card_eq
    rw [hn] at hdvd
    obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have : 4 ≤ 2 ^ i := by
      by_contra hlt
      have hi2 : i ≤ 1 := by
        by_contra h2; exact hlt (by calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega))
      interval_cases i
      · rw [pow_zero] at hi'; omega
      · rw [pow_one] at hi'; omega
    calc 4 ≤ 2 ^ i := this
      _ = (V ⊓ Subgroup.centralizer {x ^ j}).relIndex V := hi'.symm
      _ ≤ _ := hrel
  by_contra hlt
  have h2 : (V ⊓ Subgroup.centralizer {x ^ j}).relIndex V ≤ 2 := by omega
  have hAQ : x ^ j * x ^ j ∈ Qv δ := ha2
  obtain ⟨e, he, heC, heQ, he5⟩ := exists_centralizing_five F hδ hV hN hastab haQ hAQ h2
  exact heQ (hno5 e he heC he5)

end CFSG.Quasithin.Kleidman.F204
