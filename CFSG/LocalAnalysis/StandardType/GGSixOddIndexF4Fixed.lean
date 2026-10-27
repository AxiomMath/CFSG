module

public import CFSG.LocalAnalysis.StandardType.GGSixOddIndexF4

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section General

variable {G : Type*} [Group G]

theorem ggF4_mem_normalizer_closure {S : Set G} {g : G} (h1 : ∀ x ∈ S, g * x * g⁻¹ ∈ S)
    (h2 : ∀ x ∈ S, g⁻¹ * x * g ∈ S) : g ∈ Subgroup.normalizer (Subgroup.closure S : Set G) := by
  have key : ∀ k : G, (∀ x ∈ S, k * x * k⁻¹ ∈ S) →
      ∀ h ∈ Subgroup.closure S, k * h * k⁻¹ ∈ Subgroup.closure S := by
    intro k hk h hh
    have hle : Subgroup.closure S ≤
        (Subgroup.closure S).comap (MulAut.conj k).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro x hx
      exact Subgroup.subset_closure (hk x hx)
    exact hle hh
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact key g h1 h
  · intro hh
    have h2' : ∀ x ∈ S, g⁻¹ * x * g⁻¹⁻¹ ∈ S := by
      intro x hx
      rw [inv_inv]
      exact h2 x hx
    have := key g⁻¹ h2' _ hh
    simpa [mul_assoc] using this

theorem ggF4_commutator_mem_of_sq_mem {P W : Subgroup G} (hPW : P ≤ Subgroup.normalizer (W : Set G))
    (hsq : ∀ x ∈ P, x ^ 2 ∈ W) {x y : G} (hx : x ∈ P) (hy : y ∈ P) :
    x * y * x⁻¹ * y⁻¹ ∈ W := by
  have hxy : (x * y) ^ 2 ∈ W := hsq _ (P.mul_mem hx hy)
  have hx2 : (x ^ 2)⁻¹ ∈ W := W.inv_mem (hsq x hx)
  have hy2 : (y ^ 2)⁻¹ ∈ W := W.inv_mem (hsq y hy)
  have hconj : y⁻¹ * (x ^ 2)⁻¹ * y⁻¹⁻¹ ∈ W :=
    (Subgroup.mem_normalizer_iff.mp (hPW (P.inv_mem hy)) _).mp hx2
  have h := W.mul_mem (W.mul_mem hxy hconj) hy2
  have heq : (x * y) ^ 2 * (y⁻¹ * (x ^ 2)⁻¹ * y⁻¹⁻¹) * (y ^ 2)⁻¹ = x * y * x⁻¹ * y⁻¹ := by
    simp only [pow_two]
    group
  rwa [heq] at h

theorem ggF4_le_normalizer_of_sq_mem {P W W' : Subgroup G}
    (hPW : P ≤ Subgroup.normalizer (W : Set G)) (hsq : ∀ x ∈ P, x ^ 2 ∈ W) (hWW' : W ≤ W')
    (hW'P : W' ≤ P) : P ≤ Subgroup.normalizer (W' : Set G) := by
  have fwd : ∀ p ∈ P, ∀ w ∈ W', p * w * p⁻¹ ∈ W' := by
    intro p hp w hw
    have hc := hWW' (ggF4_commutator_mem_of_sq_mem hPW hsq hp (hW'P hw))
    have := W'.mul_mem hc hw
    simpa [mul_assoc] using this
  intro p hp
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · exact fwd p hp w
  · intro hw
    have := fwd p⁻¹ (P.inv_mem hp) _ hw
    simpa [mul_assoc] using this

theorem ggF4_closure_sq_ne [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P) (hP1 : P ≠ ⊥) :
    Subgroup.closure {x | ∃ y ∈ P, y ^ 2 = x} ≠ P := by
  intro heq
  have hnt : Nontrivial P := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    exact hP1
  have hnil : Group.IsNilpotent P := hP.isNilpotent
  obtain ⟨M₀, hM₀⟩ := IsCoatomic.exists_coatom (Subgroup P)
  have hidx : M₀.index = 2 := (hP.isCoatom_iff_index_eq_prime (p := 2)).mp hM₀
  have hle : Subgroup.closure {x | ∃ y ∈ P, y ^ 2 = x} ≤ M₀.map P.subtype := by
    rw [Subgroup.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩ ^ 2, Subgroup.sq_mem_of_index_two hidx _, rfl⟩
  apply hM₀.1
  rw [eq_top_iff]
  intro z _
  have hz : (z : G) ∈ M₀.map P.subtype := hle (by rw [heq]; exact z.2)
  obtain ⟨m, hm, hmz⟩ := hz
  have : m = z := Subtype.ext hmz
  exact this ▸ hm

theorem ggF4_conj_pow_eq {e v c : G} (hec : e * c = c * e) (hv : e * v * e⁻¹ = c * v) (k : ℕ) :
    e ^ k * v * (e ^ k)⁻¹ = c ^ k * v := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hck : e * c ^ k * e⁻¹ = c ^ k := by
      rw [(Commute.pow_right (show Commute e c from hec) k).eq, mul_inv_cancel_right]
    calc e ^ (k + 1) * v * (e ^ (k + 1))⁻¹ = e * (e ^ k * v * (e ^ k)⁻¹) * e⁻¹ := by
          rw [pow_succ']
          group
      _ = e * (c ^ k * v) * e⁻¹ := by rw [ih]
      _ = (e * c ^ k * e⁻¹) * (e * v * e⁻¹) := by group
      _ = c ^ (k + 1) * v := by rw [hck, hv, pow_succ, mul_assoc]

theorem ggF4_le_normalizer_closure_sq (P : Subgroup G) :
    Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer (Subgroup.closure {x | ∃ y ∈ P, y ^ 2 = x} : Set G) := by
  intro g hg
  have hsq : ∀ a y : G, a * y ^ 2 * a⁻¹ = (a * y * a⁻¹) ^ 2 := fun a y => by
    rw [conj_pow]
  apply ggF4_mem_normalizer_closure
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨g * y * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg y).mp hy, (hsq g y).symm⟩
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : g⁻¹ * y * g⁻¹⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) y).mp hy
    rw [inv_inv] at hy'
    refine ⟨g⁻¹ * y * g, hy', ?_⟩
    have := (hsq g⁻¹ y).symm
    rwa [inv_inv] at this

theorem ggF4_centralizes_of_chiefFactor [Finite G] {Y : Subgroup G} {e : G}
    (he : Odd (orderOf e))
    (hfac : ∀ N V : Subgroup G, N < V → IsPGroup 2 V → V ≤ Subgroup.normalizer (N : Set G) →
      Y ≤ Subgroup.normalizer (N : Set G) → Y ≤ Subgroup.normalizer (V : Set G) →
      (∀ x ∈ V, x ^ 2 ∈ N) →
      (∀ W : Subgroup G, N ≤ W → W ≤ V → Y ≤ Subgroup.normalizer (W : Set G) →
        W = N ∨ W = V) →
        ∃ v ∈ V, v ∉ N ∧ e * v * e⁻¹ * v⁻¹ ∈ N) :
    ∀ P : Subgroup G, IsPGroup 2 P → Y ≤ Subgroup.normalizer (P : Set G) →
      (∀ x ∈ P, x * e = e * x → ∀ y ∈ Y, x * y = y * x) → ∀ x ∈ P, x * e = e * x := by
  classical
  intro P
  obtain ⟨n, hn⟩ : ∃ n, Nat.card P = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing P with
  | _ n ih =>
  intro hP hYP hfix
  by_cases hP1 : P = ⊥
  · intro x hx
    rw [hP1, Subgroup.mem_bot] at hx
    rw [hx, one_mul, mul_one]
  set 𝒲 : Set (Subgroup G) := {W | W ≤ P ∧ W ≠ P ∧ P ≤ Subgroup.normalizer (W : Set G) ∧
    Y ≤ Subgroup.normalizer (W : Set G) ∧ ∀ x ∈ P, x ^ 2 ∈ W} with h𝒲
  have hne : 𝒲.Nonempty := by
    refine ⟨Subgroup.closure {x | ∃ y ∈ P, y ^ 2 = x}, ?_, ggF4_closure_sq_ne hP hP1,
      Subgroup.le_normalizer.trans (ggF4_le_normalizer_closure_sq P),
      hYP.trans (ggF4_le_normalizer_closure_sq P),
      fun x hx => Subgroup.subset_closure ⟨x, hx, rfl⟩⟩
    rw [Subgroup.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    exact P.pow_mem hy 2
  obtain ⟨P', hP'max⟩ := (Set.toFinite 𝒲).exists_maximal hne
  obtain ⟨hP'P, hP'ne, hPP', hYP', hsq⟩ := hP'max.1
  have hlt : P' < P := lt_of_le_of_ne hP'P hP'ne
  have hP'c : ∀ x ∈ P', x * e = e * x :=
    ih (Nat.card P') (hn ▸ Subgroup.card_lt_of_lt hlt) P' rfl (hP.to_le hP'P) hYP'
      (fun x hx hxe y hy => hfix x (hP'P hx) hxe y hy)
  have hirr : ∀ W : Subgroup G, P' ≤ W → W ≤ P → Y ≤ Subgroup.normalizer (W : Set G) →
      W = P' ∨ W = P := by
    intro W hP'W hWP hYW
    by_cases hWP' : W = P
    · exact Or.inr hWP'
    · left
      have hW𝒲 : W ∈ 𝒲 := ⟨hWP, hWP', ggF4_le_normalizer_of_sq_mem hPP' hsq hP'W hWP, hYW,
        fun x hx => hP'W (hsq x hx)⟩
      exact le_antisymm (hP'max.2 hW𝒲 hP'W) hP'W
  obtain ⟨v, hvP, hvP', hc⟩ := hfac P' P hlt hP hPP' hYP' hYP hsq hirr
  have hec : e * (e * v * e⁻¹ * v⁻¹) = (e * v * e⁻¹ * v⁻¹) * e := (hP'c _ hc).symm
  have hv : e * v * e⁻¹ = (e * v * e⁻¹ * v⁻¹) * v := by group
  have hcm : (e * v * e⁻¹ * v⁻¹) ^ orderOf e = 1 := by
    have h := ggF4_conj_pow_eq hec hv (orderOf e)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h
    calc (e * v * e⁻¹ * v⁻¹) ^ orderOf e
        = (e * v * e⁻¹ * v⁻¹) ^ orderOf e * v * v⁻¹ := by group
      _ = v * v⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel v
  have hc1 : e * v * e⁻¹ * v⁻¹ = 1 := ggSix_eq_one_of_mem_of_odd (hP.to_le hP'P) hc
    (Odd.of_dvd_nat he (orderOf_dvd_of_pow_eq_one hcm))
  have hve : v * e = e * v := by
    calc v * e = (e * v * e⁻¹ * v⁻¹)⁻¹ * (e * v) := by group
      _ = e * v := by rw [hc1, inv_one, one_mul]
  set W := Subgroup.closure ((P' : Set G) ∪ {v}) with hW
  have hP'W : P' ≤ W := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hvW : v ∈ W := Subgroup.subset_closure (Or.inr rfl)
  have hWP : W ≤ P := by
    rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · exact hP'P hx
    · rw [Set.mem_singleton_iff.mp hx]
      exact hvP
  have hYW : Y ≤ Subgroup.normalizer (W : Set G) := by
    intro y hy
    have hvy := hfix v hvP hve y hy
    apply ggF4_mem_normalizer_closure
    · rintro x (hx | hx)
      · exact Or.inl ((Subgroup.mem_normalizer_iff.mp (hYP' hy) x).mp hx)
      · right
        rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff, ← hvy, mul_inv_cancel_right]
    · rintro x (hx | hx)
      · left
        have := (Subgroup.mem_normalizer_iff.mp (hYP' (Y.inv_mem hy)) x).mp hx
        simpa using this
      · right
        rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff, mul_assoc, hvy,
          inv_mul_cancel_left]
  have hWeq : W = P := by
    rcases hirr W hP'W hWP hYW with h | h
    · exact absurd (h ▸ hvW) hvP'
    · exact h
  have hPC : P ≤ Subgroup.centralizer {e} := by
    rw [← hWeq, Subgroup.closure_le]
    rintro x (hx | hx)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hP'c x hx)
    · rw [Set.mem_singleton_iff.mp hx]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hve
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mp (hPC hx)

end General

end CFSG.StandardType
