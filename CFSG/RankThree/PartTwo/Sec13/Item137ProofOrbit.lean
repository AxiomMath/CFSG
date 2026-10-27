module

public import CFSG.RankThree.PartTwo.Sec13.Item137
public import CFSG.RankThree.PartTwo.Sec13.Item13Inputs
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic
import CFSG.RankThree.PartTwo.Sec13.Item137Delta
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
import CFSG.RankThree.PartTwo.Sec13.Item134Arg128FailHJ
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped Pointwise commutatorElement

section Orbit

variable {α : Type*}

theorem ncard_four_eq {a b c d : α} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) : ({a, b, c, d} : Set α).ncard = 4 := by
  rw [Set.ncard_insert_of_notMem (by simp [hab, hac, had]),
    Set.ncard_insert_of_notMem (by simp [hbc, hbd]), Set.ncard_pair hcd]

theorem ncard_three_eq {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Set α).ncard = 3 := by
  rw [Set.ncard_insert_of_notMem (by simp [hab, hac]), Set.ncard_pair hbc]

theorem ncard_four_le (a b c d : α) : ({a, b, c, d} : Set α).ncard ≤ 4 :=
  (Set.ncard_insert_le _ _).trans (Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans
    (Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])))))

variable {Γ β : Type*} [Group Γ] [MulAction Γ α] [MulAction Γ β]

theorem smul_mem_orbit_of_mem {x y : α} (hy : y ∈ MulAction.orbit Γ x) (g : Γ) :
    g • y ∈ MulAction.orbit Γ x := by
  obtain ⟨h, rfl⟩ := hy
  exact ⟨g * h, mul_smul g h x⟩

theorem smul_eq_of_ncard_orbit_eq_three {Δ : Set α} (hΔ : ∀ g : Γ, ∀ y ∈ Δ, g • y ∈ Δ)
    {A A' E F : α} (hΔeq : Δ = {A, A', E, F}) (hAA' : A ≠ A') (hEA : E ≠ A) (hEA' : E ≠ A')
    (hEF : E ≠ F) (hFA : F ≠ A) (hFA' : F ≠ A') (hmove : ∃ g : Γ, g • A = A')
    {ℓ : β} (hEℓ : ∀ g : Γ, g • E = E → g • ℓ = ℓ) (hℓ : (MulAction.orbit Γ ℓ).ncard = 3)
    (g : Γ) : g • F = F := by
  set O := MulAction.orbit Γ E with hO
  have hdvd : 3 ∣ O.ncard := by
    rw [← hℓ, hO, ← MulAction.index_stabilizer, ← MulAction.index_stabilizer]
    exact Subgroup.index_dvd_of_le fun g hg => hEℓ g hg
  have hsub : O ⊆ Δ := by
    rintro _ ⟨g, rfl⟩
    exact hΔ g E (by rw [hΔeq]; simp)
  have hΔfin : Δ.Finite := hΔeq ▸ Set.toFinite _
  have hOfin : O.Finite := hΔfin.subset hsub
  have hle4 : O.ncard ≤ 4 :=
    (Set.ncard_le_ncard hsub hΔfin).trans (hΔeq ▸ ncard_four_le A A' E F)
  have hEO : E ∈ O := MulAction.mem_orbit_self E
  have hpos : 0 < O.ncard := (Set.ncard_pos hOfin).mpr ⟨E, hEO⟩
  have h3 : O.ncard = 3 := by
    obtain ⟨k, hk⟩ := hdvd
    omega
  obtain ⟨g₀, hg₀⟩ := hmove
  have hAA'O : A ∈ O → A' ∈ O := fun h => hg₀ ▸ smul_mem_orbit_of_mem h g₀
  have hA'AO : A' ∈ O → A ∈ O := fun h => by
    have := smul_mem_orbit_of_mem h g₀⁻¹
    rwa [← hg₀, inv_smul_smul] at this
  have hFO : F ∉ O := by
    intro hF
    by_cases hA : A ∈ O
    · have h4 : ({A, A', E, F} : Set α) ⊆ O := by
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl | rfl
        · exact hA
        · exact hAA'O hA
        · exact hEO
        · exact hF
      have := Set.ncard_le_ncard h4 hOfin
      rw [ncard_four_eq hAA' hEA.symm hFA.symm hEA'.symm hFA'.symm hEF] at this
      omega
    · have hA' : A' ∉ O := fun h => hA (hA'AO h)
      have h2 : O ⊆ {E, F} := by
        intro y hy
        have := hsub hy
        rw [hΔeq] at this
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this ⊢
        rcases this with rfl | rfl | h | h
        · exact absurd hy hA
        · exact absurd hy hA'
        · exact Or.inl h
        · exact Or.inr h
      have := Set.ncard_le_ncard h2 (Set.toFinite _)
      rw [Set.ncard_pair hEF] at this
      omega
  have hOeq : O = {A, A', E} := by
    have hsub3 : O ⊆ {A, A', E} := by
      intro y hy
      have := hsub hy
      rw [hΔeq] at this
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this ⊢
      rcases this with h | h | h | rfl
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact absurd hy hFO
    exact Set.eq_of_subset_of_ncard_le hsub3
      (by rw [ncard_three_eq hAA' hEA.symm hEA'.symm, h3]) (Set.toFinite _)
  have hgF : g • F ∈ Δ := hΔ g F (by rw [hΔeq]; simp)
  have hgFO : g • F ∉ O := fun h => by
    have := smul_mem_orbit_of_mem h g⁻¹
    rw [inv_smul_smul] at this
    exact hFO this
  rw [hΔeq] at hgF
  rw [hOeq] at hgFO
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgF hgFO
  tauto

end Orbit

section Conj

variable {G : Type*} [Group G]

@[expose, instance_reducible] noncomputable def conjActionOn (X : Subgroup G) :
    MulAction X (Subgroup G) :=
  MulAction.compHom (Subgroup G)
    ((ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom.comp X.subtype)

theorem orbit_conjActionOn_eq (X Y : Subgroup G) :
    (letI := conjActionOn X; MulAction.orbit X Y) = orbitIn X Y := by
  let := conjActionOn X
  ext Z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

end Conj

section Lines

variable {G : Type*} [Group G]

theorem zpow_eq_zpow_emod_of_pow_three {x : G} (hx : x ^ 3 = 1) (i : ℤ) : x ^ i = x ^ (i % 3) := by
  conv_lhs => rw [← Int.mul_ediv_add_emod i 3]
  rw [zpow_add, zpow_mul, show x ^ (3 : ℤ) = 1 by exact_mod_cast hx, one_zpow, one_mul]

theorem zpow_mul_zpow_pow_three {c d : G} (hc3 : c ^ 3 = 1) (hd3 : d ^ 3 = 1)
    (hcd : Commute c d) (a b : ℤ) : (c ^ a * d ^ b) ^ 3 = 1 := by
  rw [(hcd.zpow_zpow a b).mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
    mul_comm a, mul_comm b, zpow_mul, zpow_mul, show c ^ ((3 : ℕ) : ℤ) = 1 by exact_mod_cast hc3,
    show d ^ ((3 : ℕ) : ℤ) = 1 by exact_mod_cast hd3, one_zpow, one_zpow, one_mul]

theorem zpowers_eq_zpowers_sq {x : G} (hx3 : x ^ 3 = 1) :
    Subgroup.zpowers x = Subgroup.zpowers (x ^ (2 : ℤ)) := by
  have h2 : x ^ (2 : ℤ) = x⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← zpow_add_one, show (2 : ℤ) + 1 = (3 : ℕ) by norm_num,
      zpow_natCast, hx3]
  rw [h2, Subgroup.zpowers_inv]

theorem zpowers_eq_of_not_mem {c d x : G} (hc3 : c ^ 3 = 1) (hd3 : d ^ 3 = 1)
    (hcd : c * d = d * c) {i j : ℤ} (hx : x = c ^ i * d ^ j)
    (hxd : x ∉ Subgroup.zpowers d) :
    Subgroup.zpowers x = Subgroup.zpowers c ∨ Subgroup.zpowers x = Subgroup.zpowers (c * d) ∨
      Subgroup.zpowers x = Subgroup.zpowers (c * d ^ 2) := by
  have hcd' : Commute c d := hcd
  rw [zpow_eq_zpow_emod_of_pow_three hc3 i, zpow_eq_zpow_emod_of_pow_three hd3 j] at hx
  have hi := Int.emod_nonneg i (by norm_num : (3 : ℤ) ≠ 0)
  have hi' := Int.emod_lt_of_pos i (by norm_num : (0 : ℤ) < 3)
  have hj := Int.emod_nonneg j (by norm_num : (3 : ℤ) ≠ 0)
  have hj' := Int.emod_lt_of_pos j (by norm_num : (0 : ℤ) < 3)
  have hc4 : c ^ ((2 : ℤ) * 2) = c := by
    rw [show (2 : ℤ) * 2 = 3 + 1 by norm_num, zpow_add, zpow_one,
      show c ^ (3 : ℤ) = 1 by exact_mod_cast hc3, one_mul]
  have hd4 : d ^ ((2 : ℤ) * 2) = d := by
    rw [show (2 : ℤ) * 2 = 3 + 1 by norm_num, zpow_add, zpow_one,
      show d ^ (3 : ℤ) = 1 by exact_mod_cast hd3, one_mul]
  have hx3 : x ^ 3 = 1 := hx ▸ zpow_mul_zpow_pow_three hc3 hd3 hcd' _ _
  rcases (show i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 by omega) with h0 | h1 | h2
  · rw [h0, zpow_zero, one_mul] at hx
    exact absurd (hx ▸ Subgroup.zpow_mem_zpowers d (j % 3)) hxd
  · rw [h1, zpow_one] at hx
    rw [hx]
    rcases (show j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 by omega) with k0 | k1 | k2
    · left
      rw [k0, zpow_zero, mul_one]
    · right; left
      rw [k1, zpow_one]
    · right; right
      rw [k2]
      norm_cast
  · rw [zpowers_eq_zpowers_sq hx3, hx, h2, (hcd'.zpow_zpow 2 (j % 3)).mul_zpow, ← zpow_mul,
      ← zpow_mul, hc4]
    rcases (show j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 by omega) with k0 | k1 | k2
    · left
      rw [k0, zero_mul, zpow_zero, mul_one]
    · right; right
      rw [k1]
      norm_num
    · right; left
      rw [k2, hd4]

end Lines

section Structure

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

theorem exists_commutator_eq_zpowers_of_isSylowOf (h131 : Item131) (hspor : SporadicModels131)
    (h414 : Sec4.Item4_14_local) (h : Sec13Data G A c L)
    (hM : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M12))
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (A ⊔ L)) (hAP : A ≤ P) :
    ∃ d : G, d ∈ L ∧ d ≠ 1 ∧ d ^ 3 = 1 ∧ ⁅P, P⁆ = Subgroup.zpowers d ∧
      (∀ z ∈ P, (∀ x ∈ P, z * x = x * z) → ∃ i j : ℤ, z = c ^ i * d ^ j) ∧
      (∀ x ∈ P, d * x = x * d) ∧ Nat.card P = 81 ∧ ∀ x ∈ P, x ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hcL, h9, -⟩ := facts_of_m12 h131 hspor h hM
  have hc3 : c ^ 3 = 1 := h.isElemAbelian.2 c h.mem_A
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hl)
  have hBL : A ⊓ L ≤ L := inf_le_right
  have hAB : A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
    have hle : Subgroup.zpowers c ⊔ (A ⊓ L) ≤ A :=
      sup_le (Subgroup.zpowers_le.mpr h.mem_A) inf_le_left
    have hcard := (isElemAbelian_zpowers_sup_of_card_nine hc3 (fun hcB => hcL (hBL hcB)) le_rfl h9
      (fun b hb => h.isElemAbelian.2 b hb.1) (fun b hb => h.commute h.mem_A hb.1)).2
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h.card_eq, hcard])).symm
  have hAL : A ⊔ L = Subgroup.zpowers c ⊔ L :=
    le_antisymm (sup_le (hAB ▸ sup_le le_sup_left (hBL.trans le_sup_right)) le_sup_right)
      (sup_le_sup_right (Subgroup.zpowers_le.mpr h.mem_A) L)
  have hLN : A ⊔ L ≤ Subgroup.normalizer (L : Set G) :=
    sup_le h.le_normalizer Subgroup.le_normalizer
  obtain ⟨Q, hQ⟩ := hP.inf_of_le_normalizer le_sup_right hLN
  have hS3 : IsPGroup 3 (Q : Subgroup L) := Q.isPGroup'
  set Ps : Sylow 3 (L ⧸ aschbacherSolvableCore 3 L) :=
    Q.mapSurjective (QuotientGroup.mk'_surjective _) with hPsdef
  have hPs : (Ps : Subgroup _) =
      (Q : Subgroup L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) :=
    Sylow.coe_mapSurjective _ _
  obtain ⟨hHeis, -⟩ := h414 _ hM Ps
  rw [hPs] at hHeis
  obtain ⟨hS27, -, hSexp⟩ := facts_of_isHeisThree_map hS3 hHeis
  set S' : Subgroup G := (Q : Subgroup L).map L.subtype with hS'def
  have hS'L : S' ≤ L := Subgroup.map_subtype_le _
  have hS'P : S' ≤ P := hQ ▸ inf_le_left
  have hH : Sec4.IsHeisThree S' := by
    let ψ : S' ≃* (Q : Subgroup L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) :=
      ((Q : Subgroup L).equivMapOfInjective L.subtype L.subtype_injective).symm.trans
        (mkEquivOfIsPGroup hS3)
    exact isHeisThree_of_mulEquiv ψ.symm hHeis
  have hZ3 := Item134Arg128Fail.card_inf_centralizer_of_heis hH
  have hP0 := isSylowOf_zpowers_sup hc3 hcL hLc Q hS27
  rw [← hAL] at hP0
  have hPeq : P = Subgroup.zpowers c ⊔ S' :=
    hP0.eq_of_le (sup_le (Subgroup.zpowers_le.mpr (hAP h.mem_A)) hS'P) hP.le hP.isPGroup
  have hcS : ∀ y ∈ S', c * y = y * c := fun y hy => (hLc y (hS'L hy)).symm
  have hPPle : ⁅P, P⁆ ≤ S' ⊓ Subgroup.centralizer (S' : Set G) := by
    rw [hPeq]
    refine (commutator_zpowers_sup_le hcS).trans ?_
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact Item134Arg128Fail.commutator_mem_inf_centralizer_of_heis hH hx hy
  have hPPne : ⁅P, P⁆ ≠ ⊥ := by
    intro hbot
    have hle : S' ≤ S' ⊓ Subgroup.centralizer (S' : Set G) := by
      refine le_inf le_rfl fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      have hxy : ⁅y, x⁆ ∈ ⁅P, P⁆ :=
        Subgroup.commutator_mem_commutator (hS'P hy) (hS'P hx)
      rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hxy
      exact hxy
    have := Subgroup.card_le_of_le hle
    rw [hZ3, show Nat.card S' = 27 from hS27] at this
    omega
  have hPPeq : ⁅P, P⁆ = S' ⊓ Subgroup.centralizer (S' : Set G) := by
    refine Subgroup.eq_of_le_of_card_ge hPPle ?_
    rw [hZ3]
    have hdvd : Nat.card (⁅P, P⁆ : Subgroup G) ∣ 3 := hZ3 ▸ Subgroup.card_dvd_of_le hPPle
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd ((Subgroup.card_eq_one).mp h1) hPPne
    · exact h3.ge
  obtain ⟨⟨d, hdPP'⟩, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hPPne
  have hd1' : d ≠ 1 := fun h1 => hd1 (Subtype.ext h1)
  have hord : orderOf d = 3 := by
    have hdvd : orderOf d ∣ 3 := by
      have := Subgroup.orderOf_dvd_natCard ⁅P, P⁆ hdPP'
      rwa [show Nat.card (⁅P, P⁆ : Subgroup G) = 3 by rw [hPPeq, hZ3]] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hd1'
    · exact h3
  have hzd : Subgroup.zpowers d = ⁅P, P⁆ := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdPP') ?_
    rw [Nat.card_zpowers, hord, hPPeq, hZ3]
  have hdZ : d ∈ S' ⊓ Subgroup.centralizer (S' : Set G) := by
    rw [hPPeq] at hdPP'
    exact hdPP'
  have hcomm : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ S', x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_left (hcS y hy) k).eq
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  have hdecomp : ∀ x ∈ P, ∃ (i : ℤ) (y : G), y ∈ S' ∧ x = c ^ i * y := by
    intro x hx
    have hx' : x ∈ ((Subgroup.zpowers c ⊔ S' : Subgroup G) : Set G) := hPeq ▸ hx
    rw [hset] at hx'
    obtain ⟨a, ha, y, hy, rfl⟩ := hx'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact ⟨i, y, hy, rfl⟩
  refine ⟨d, hS'L hdZ.1, hd1', by rw [← hord]; exact pow_orderOf_eq_one _, hzd.symm, ?_, ?_,
    ?_, ?_⟩
  rotate_left
  ·
    intro x hx
    obtain ⟨i, y, hy, rfl⟩ := hdecomp x hx
    have h1 : d * c ^ i = c ^ i * d := (Commute.zpow_right (hLc d (hS'L hdZ.1)) i).eq
    have h2 : d * y = y * d := (Subgroup.mem_centralizer_iff.mp hdZ.2 y hy).symm
    calc d * (c ^ i * y) = c ^ i * (d * y) := by rw [← mul_assoc, h1, mul_assoc]
      _ = c ^ i * y * d := by rw [h2, mul_assoc]
  ·
    rw [hPeq]
    exact card_zpowers_sup_map hc3 hcL hLc hS27
  ·
    intro x hx
    obtain ⟨i, y, hy, rfl⟩ := hdecomp x hx
    rw [(Commute.zpow_left (hcS y hy) i).mul_pow, hSexp y hy, mul_one, ← zpow_natCast,
      ← zpow_mul, mul_comm, zpow_mul, show c ^ ((3 : ℕ) : ℤ) = 1 by exact_mod_cast hc3, one_zpow]
  intro z hz hzc
  obtain ⟨i, y, hy, rfl⟩ := hdecomp z hz
  have hyZ : y ∈ S' ⊓ Subgroup.centralizer (S' : Set G) := by
    refine ⟨hy, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    have h1 := hzc x (hS'P hx)
    have h2 : c ^ i * x = x * c ^ i := (Commute.zpow_left (hcS x hx) i).eq
    have h3 : c ^ i * (x * y) = c ^ i * (y * x) :=
      calc c ^ i * (x * y) = x * c ^ i * y := by rw [← mul_assoc, h2]
        _ = x * (c ^ i * y) := mul_assoc _ _ _
        _ = c ^ i * y * x := h1.symm
        _ = c ^ i * (y * x) := mul_assoc _ _ _
    exact mul_left_cancel h3
  rw [← hPPeq, ← hzd] at hyZ
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyZ
  exact ⟨i, j, rfl⟩

end Structure

section OrbitC

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_conj_eq_iff_mem_normalizer {H : Subgroup G} {g : G} :
    H.map (MulAut.conj g).toMonoidHom = H ↔ g ∈ Subgroup.normalizer (H : Set G) :=
  Subgroup.mem_normalizer_iff_map_conj_eq.symm

omit [Finite G] in
theorem map_commutator_eq_of_mem_normalizer {P : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (P : Set G)) :
    (⁅P, P⁆ : Subgroup G).map (MulAut.conj g).toMonoidHom = ⁅P, P⁆ := by
  have h1 : P.map (MulAut.conj g).toMonoidHom = P := map_conj_eq_iff_mem_normalizer.mpr hg
  rw [Subgroup.map_commutator, h1]

theorem ncard_orbitIn_zpowers_eq_three {P L : Subgroup G} {c d s t : G} (hc3 : c ^ 3 = 1)
    (hcL : c ∉ L) (hdL : d ∈ L) (hd1 : d ≠ 1) (hd3 : d ^ 3 = 1) (hcd : c * d = d * c)
    (hcP : c ∈ P) (hcZ : ∀ x ∈ P, c * x = x * c) (hPP : ⁅P, P⁆ = Subgroup.zpowers d)
    (hZ : ∀ z ∈ P, (∀ x ∈ P, z * x = x * z) → ∃ i j : ℤ, z = c ^ i * d ^ j)
    (hsP : s ∈ Subgroup.normalizer (P : Set G))
    (hsH : s ∉ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (htP : t ∈ Subgroup.normalizer (P : Set G)) (htc : t * c * t⁻¹ = c)
    (htd : t * d * t⁻¹ = d⁻¹) :
    (orbitIn (Subgroup.normalizer (P : Set G)) (Subgroup.zpowers c)).ncard = 3 := by
  have hcd' : Commute c d := hcd
  have hcdL : Subgroup.zpowers c ⊓ L = ⊥ := zpowers_inf_eq_bot hc3 hcL
  have hmap : ∀ (g y : G), (Subgroup.zpowers y).map (MulAut.conj g).toMonoidHom =
      Subgroup.zpowers (g * y * g⁻¹) := fun g y => by
    rw [MonoidHom.map_zpowers]
    rfl
  have hne1 : ∀ {x : G}, x ∈ L → x ≠ 1 → Subgroup.zpowers c ≠ Subgroup.zpowers (c * x) := by
    intro x hxL hx1 heq
    have hcx : c * x ∈ Subgroup.zpowers c := heq ▸ Subgroup.mem_zpowers (c * x)
    have hx : x ∈ Subgroup.zpowers c := by
      have := (Subgroup.zpowers c).mul_mem (Subgroup.inv_mem _ (Subgroup.mem_zpowers c)) hcx
      rwa [inv_mul_cancel_left] at this
    have : x ∈ Subgroup.zpowers c ⊓ L := ⟨hx, hxL⟩
    rw [hcdL, Subgroup.mem_bot] at this
    exact hx1 this
  have hd2L : d ^ 2 ∈ L := L.pow_mem hdL 2
  have hd21 : d ^ 2 ≠ 1 := by
    intro h21
    apply hd1
    calc d = d ^ 3 * (d ^ 2)⁻¹ := by group
      _ = 1 := by rw [hd3, h21, inv_one, one_mul]
  have h12 : Subgroup.zpowers c ≠ Subgroup.zpowers (c * d) := hne1 hdL hd1
  have h13 : Subgroup.zpowers c ≠ Subgroup.zpowers (c * d ^ 2) := hne1 hd2L hd21
  have h23 : Subgroup.zpowers (c * d) ≠ Subgroup.zpowers (c * d ^ 2) := by
    intro heq
    apply h12
    have hcd2 : c * d ^ 2 ∈ Subgroup.zpowers (c * d) := heq ▸ Subgroup.mem_zpowers _
    have hdm : d ∈ Subgroup.zpowers (c * d) := by
      have := (Subgroup.zpowers (c * d)).mul_mem
        (Subgroup.inv_mem _ (Subgroup.mem_zpowers (c * d))) hcd2
      rwa [show (c * d)⁻¹ * (c * d ^ 2) = d by group] at this
    have hcm : c ∈ Subgroup.zpowers (c * d) := by
      have := (Subgroup.zpowers (c * d)).mul_mem (Subgroup.mem_zpowers (c * d))
        (Subgroup.inv_mem _ hdm)
      rwa [mul_inv_cancel_right] at this
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcm) ?_
    have hcd3 : (c * d) ^ 3 = 1 := by
      rw [hcd'.mul_pow, hc3, hd3, one_mul]
    rw [Nat.card_zpowers, Nat.card_zpowers]
    have hc1 : c ≠ 1 := fun h1 => hcL (h1 ▸ L.one_mem)
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [orderOf_eq_prime hc3 hc1]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hcd3)
  have hsub : orbitIn (Subgroup.normalizer (P : Set G)) (Subgroup.zpowers c) ⊆
      {Subgroup.zpowers c, Subgroup.zpowers (c * d), Subgroup.zpowers (c * d ^ 2)} := by
    rintro _ ⟨g, hg, rfl⟩
    rw [hmap]
    have hgcP : g * c * g⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hg c).mp hcP
    have hgcZ : ∀ x ∈ P, g * c * g⁻¹ * x = x * (g * c * g⁻¹) := by
      intro x hx
      have hx' : g⁻¹ * x * g ∈ P := by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) x).mp hx
        simpa using this
      have h1 := hcZ _ hx'
      calc g * c * g⁻¹ * x = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by rw [h1]
        _ = x * (g * c * g⁻¹) := by group
    obtain ⟨i, j, hij⟩ := hZ _ hgcP hgcZ
    have hnot : g * c * g⁻¹ ∉ Subgroup.zpowers d := by
      intro hmem
      rw [← hPP] at hmem
      have hc : c ∈ ⁅P, P⁆ := by
        have h1 := map_commutator_eq_of_mem_normalizer (inv_mem hg)
        rw [← h1]
        refine ⟨g * c * g⁻¹, hmem, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [hPP] at hc
      exact hcL (Subgroup.zpowers_le.mpr hdL hc)
    rcases zpowers_eq_of_not_mem hc3 hd3 hcd hij hnot with h | h | h <;> rw [h] <;> simp
  have hsP' : (Subgroup.zpowers c).map (MulAut.conj s).toMonoidHom ≠ Subgroup.zpowers c :=
    fun h => hsH (map_conj_eq_iff_mem_normalizer.mp h)
  have hs_mem := hsub ⟨s, hsP, rfl⟩
  have htcd : ∀ k : ℕ, t * (c * d ^ k) * t⁻¹ = c * (d ^ k)⁻¹ := by
    intro k
    calc t * (c * d ^ k) * t⁻¹ = (t * c * t⁻¹) * (t * d * t⁻¹) ^ k := by
          rw [conj_pow]; group
      _ = c * (d ^ k)⁻¹ := by rw [htc, htd, inv_pow]
  have hdinv : d⁻¹ = d ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', hd3]
  have hdinv2 : (d ^ 2)⁻¹ = d := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ, hd3]
  have hts : (Subgroup.zpowers c).map (MulAut.conj (t * s)).toMonoidHom =
      ((Subgroup.zpowers c).map (MulAut.conj s).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have htsP : t * s ∈ Subgroup.normalizer (P : Set G) := mul_mem htP hsP
  have hsup : {Subgroup.zpowers c, Subgroup.zpowers (c * d), Subgroup.zpowers (c * d ^ 2)} ⊆
      orbitIn (Subgroup.normalizer (P : Set G)) (Subgroup.zpowers c) := by
    intro Y hY
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hY hs_mem
    rcases hs_mem with h0 | h1 | h2
    · exact absurd h0 hsP'
    · rcases hY with rfl | rfl | rfl
      · exact ⟨1, one_mem _, by simp⟩
      · exact ⟨s, hsP, h1.symm⟩
      · refine ⟨t * s, htsP, ?_⟩
        rw [hts, h1, hmap, show c * d = c * d ^ 1 by rw [pow_one], htcd, pow_one, hdinv]
    · rcases hY with rfl | rfl | rfl
      · exact ⟨1, one_mem _, by simp⟩
      · refine ⟨t * s, htsP, ?_⟩
        rw [hts, h2, hmap, htcd, hdinv2]
      · exact ⟨s, hsP, h2.symm⟩
  rw [Set.Subset.antisymm hsub hsup, ncard_three_eq h12 h13 h23]

end OrbitC

section Reduction

@[expose] def Item137Core : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L →
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M12) →
        ∀ (P E F : Subgroup G) (t : G), Config137 A c L P E F t → HypS E ∨ HypT E →
          Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
            ∃ s ∈ Subgroup.normalizer (P : Set G),
              s ∉ Subgroup.normalizer (Subgroup.zpowers c : Set G)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_mem_setOf_elemAbelian {P Y : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (P : Set G))
    (hY : Y ∈ {B : Subgroup G | B ≤ P ∧ CFSG.Assembly.IsElemAbelian 3 B ∧ Nat.card B = 27}) :
    Y.map (MulAut.conj g).toMonoidHom ∈
      {B : Subgroup G | B ≤ P ∧ CFSG.Assembly.IsElemAbelian 3 B ∧ Nat.card B = 27} := by
  obtain ⟨hYP, hY3, hY27⟩ := hY
  refine ⟨?_, isElemAbelian_map hY3 _, ?_⟩
  · rw [← map_conj_eq_iff_mem_normalizer.mpr hg]
    exact Subgroup.map_mono hYP
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hY27]

theorem mem_normalizer_of_config (h131 : Item131) (hspor : SporadicModels131)
    (h414 : Sec4.Item4_14_local) {A L P E F : Subgroup G} {c t s : G}
    (h : Sec13Data G A c L)
    (hM : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M12))
    (hcfg : Config137 A c L P E F t)
    (hU : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hsP : s ∈ Subgroup.normalizer (P : Set G))
    (hsH : s ∉ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    s ∈ Subgroup.normalizer (F : Set G) := by
  obtain ⟨hP, hAP, htLP, htinv, hΔ, hAAt, hEF, hEA, hEAt, hFA, hFAt, -, -, -, -, -, -⟩ := hcfg
  obtain ⟨htL, htP⟩ := Subgroup.mem_inf.mp htLP
  obtain ⟨hcL, -, -⟩ := facts_of_m12 h131 hspor h hM
  obtain ⟨d, hdL, hd1, hd3, hPP, hZ, -, -, -⟩ :=
    exists_commutator_eq_zpowers_of_isSylowOf h131 hspor h414 h hM hP hAP
  have hc3 : c ^ 3 = 1 := h.isElemAbelian.2 c h.mem_A
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hl)
  have hcP : c ∈ P := hAP h.mem_A
  have hcZ : ∀ x ∈ P, c * x = x * c := by
    intro x hx
    have hxAL : x ∈ A ⊔ L := hP.le hx
    have hle : A ⊔ L ≤ Subgroup.centralizer ({c} : Set G) :=
      sup_le h.A_le_centralizer h.le_centralizer
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hxAL)).symm
  have htc : t * c * t⁻¹ = c := by rw [hLc t htL, mul_inv_cancel_right]
  have htd : t * d * t⁻¹ = d⁻¹ := htinv d (hPP ▸ Subgroup.mem_zpowers d)
  have hℓ := ncard_orbitIn_zpowers_eq_three hc3 hcL hdL hd1 hd3 (hLc d hdL).symm hcP hcZ hPP hZ
    hsP hsH htP htc htd
  let := conjActionOn (Subgroup.normalizer (P : Set G))
  have key := smul_eq_of_ncard_orbit_eq_three (Γ := Subgroup.normalizer (P : Set G))
    (Δ := {B : Subgroup G | B ≤ P ∧ CFSG.Assembly.IsElemAbelian 3 B ∧ Nat.card B = 27})
    (fun g Y hY => map_mem_setOf_elemAbelian g.2 hY) hΔ hAAt hEA hEAt hEF hFA hFAt
    ⟨⟨t⁻¹, inv_mem htP⟩, rfl⟩ (ℓ := Subgroup.zpowers c)
    (fun g hg => map_conj_eq_iff_mem_normalizer.mpr
      (hU (map_conj_eq_iff_mem_normalizer.mp hg)))
    (by rw [orbit_conjActionOn_eq]; exact hℓ) ⟨s, hsP⟩
  exact map_conj_eq_iff_mem_normalizer.mp key

theorem item137Move_of_core_inputs (h131 : Item131) (hspor : SporadicModels131)
    (h414 : Sec4.Item4_14_local) (hcore : Item137Core) : Item137Move := by
  intro G _ _ A c L h hM P E F t hcfg hST hU
  obtain ⟨s, hsP, hsH⟩ := hcore G A c L h hM P E F t hcfg hST hU
  exact ⟨s, mem_normalizer_of_config h131 hspor h414 h hM hcfg hU hsP hsH, hsH⟩

end Reduction

end CFSG.RankThree.PartTwo.Sec13
