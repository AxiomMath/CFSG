module

public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalDich

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom
  CFSG.QuasithinUnique.A5.Delta5

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

theorem four_le_relIndex_A (F : Frame L1 L2 S D X) {δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hδ : vtype δ = true) {M : Subgroup G} (hM : IsElemAbelian 2 M)
    (hN : stab δ ≤ Subgroup.normalizer (M : Set G))
    (hQ : Qv δ ≤ Subgroup.centralizer (M : Set G))
    (hfaith : ¬ stab δ ≤ Subgroup.centralizer (M : Set G))
    {x : G} (hx : x ∈ stab δ) (hxQ : x ∉ Qv δ) {k : ℕ} (hxk : x ^ 2 ^ k ∈ Qv δ) :
    4 ≤ (M ⊓ Subgroup.centralizer {x}).relIndex M := by
  obtain ⟨j, haQ, ha2⟩ := exists_pow_sq_mem (Qv δ) hxQ hxk
  have hastab : x ^ j ∈ stab δ := (stab δ).pow_mem hx j
  have hle : M ⊓ Subgroup.centralizer {x} ≤ M ⊓ Subgroup.centralizer {x ^ j} := by
    intro v hv
    have hc : Commute x v := Subgroup.mem_centralizer_iff.mp hv.2 x rfl
    exact ⟨hv.1, Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff.mp hh]; exact (hc.pow_left j).eq⟩
  have hrel : (M ⊓ Subgroup.centralizer {x ^ j}).relIndex M ≤
      (M ⊓ Subgroup.centralizer {x}).relIndex M :=
    Subgroup.relIndex_le_of_le_left (L := M) hle Subgroup.index_ne_zero_of_finite
  suffices h : 3 ≤ (M ⊓ Subgroup.centralizer {x ^ j}).relIndex M by
    have hp2 : IsPGroup 2 M := F7.isPGroup_of_isElemAbelian hM
    have hdvd : (M ⊓ Subgroup.centralizer {x ^ j}).relIndex M ∣ Nat.card M := by
      have := Subgroup.relIndex_mul_card (H := M ⊓ Subgroup.centralizer {x ^ j}) (K := M)
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
      _ = (M ⊓ Subgroup.centralizer {x ^ j}).relIndex M := hi'.symm
      _ ≤ _ := hrel
  by_contra hlt
  have h2 : (M ⊓ Subgroup.centralizer {x ^ j}).relIndex M ≤ 2 := by omega
  obtain ⟨φ, hφs, hφk⟩ := exists_phi_stab F hδ
  have hM2 : ∀ v ∈ M, v * v = 1 := fun v hv => by rw [← pow_two]; exact hM.2 v hv
  have hker : ∀ l : ↥(stab δ), φ l = 1 → (l : G) ∈ Subgroup.centralizer (M : Set G) := by
    intro l hl
    have : l ∈ φ.ker := hl
    rw [hφk, Subgroup.mem_subgroupOf] at this
    exact hQ this
  let l : ↥(stab δ) := ⟨x ^ j, hastab⟩
  have hl1 : φ l ≠ 1 := fun h => haQ (by
    have : l ∈ φ.ker := h
    rwa [hφk, Subgroup.mem_subgroupOf] at this)
  have hl2 : φ l ^ 2 = 1 := by
    rw [← map_pow]
    have : l ^ 2 ∈ φ.ker := by
      rw [hφk, Subgroup.mem_subgroupOf]
      show (x ^ j) ^ 2 ∈ Qv δ
      rw [pow_two]; exact ha2
    exact this
  exact hfaith (FA5.centralizes_of_alt5_transvection hM2 hN φ hφs hker hl1 hl2 h2)

end CFSG.Quasithin.Kleidman.F204
