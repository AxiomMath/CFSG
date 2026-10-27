module

public import CFSG.RankThree.PartTwo.Sec11.TwoStarProofComponent

public section

namespace CFSG.RankThree.PartTwo.Sec11

namespace LSSolvableProof

open scoped commutatorElement

theorem exists_list_sup_closure_eq_top {G : Type*} [Group G] [Finite G] {s : ℕ} (hs : s.Prime) :
    ∀ (n : ℕ) (H : Subgroup G), H.index = s ^ n →
      ∃ l : List G, l.length ≤ n ∧ H ⊔ Subgroup.closure {g | g ∈ l} = ⊤ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro H hH
    by_cases htop : H = ⊤
    · exact ⟨[], by simp, by rw [htop, top_sup_eq]⟩
    obtain ⟨g, hg⟩ : ∃ g, g ∉ H := by
      by_contra hall
      push Not at hall
      exact htop (eq_top_iff.mpr fun x _ => hall x)
    set H' := H ⊔ Subgroup.zpowers g with hH'
    have hlt : H < H' := lt_of_le_of_ne le_sup_left fun h => hg (by
      rw [h]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers g))
    have hidx : H'.index < H.index := Subgroup.index_strictAnti hlt
    have hdvd : H'.index ∣ s ^ n := hH ▸ Subgroup.index_dvd_of_le le_sup_left
    obtain ⟨n', hn'le, hn'⟩ := (Nat.dvd_prime_pow hs).mp hdvd
    have hn'lt : n' < n := by
      by_contra hge
      push Not at hge
      have : n' = n := le_antisymm hn'le hge
      rw [hn', this, ← hH] at hidx
      exact lt_irrefl _ hidx
    obtain ⟨l, hl, hlH⟩ := ih n' hn'lt H' hn'
    have hlen : (g :: l).length ≤ n := by
      rw [List.length_cons]
      omega
    refine ⟨g :: l, hlen, ?_⟩
    rw [eq_top_iff, ← hlH, hH']
    refine sup_le (sup_le le_sup_left ?_) ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    · refine le_trans (Subgroup.closure_mono fun x hx => ?_) le_sup_right
      simp only [Set.mem_ofPred_eq, List.mem_cons] at hx ⊢
      exact Or.inr hx

section Commutators

variable {Y : Type*} [Group Y]

theorem conj_pow_eq_of_central {x y : Y} (hc : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center Y)
    (n : ℕ) : x ^ n * y * (x ^ n)⁻¹ = (x * y * x⁻¹ * y⁻¹) ^ n * y := by
  set c := x * y * x⁻¹ * y⁻¹ with hcdef
  have hxy : x * y * x⁻¹ = c * y := by rw [hcdef]; group
  induction n with
  | zero => simp
  | succ n ih =>
    have hcn : c ^ n ∈ Subgroup.center Y := Subgroup.pow_mem _ hc n
    calc x ^ (n + 1) * y * (x ^ (n + 1))⁻¹ = x * (x ^ n * y * (x ^ n)⁻¹) * x⁻¹ := by group
      _ = x * (c ^ n * y) * x⁻¹ := by rw [ih]
      _ = c ^ n * (x * y * x⁻¹) := by
          rw [← mul_assoc x, Subgroup.mem_center_iff.mp hcn x]
          group
      _ = c ^ (n + 1) * y := by rw [hxy]; group

theorem commutator_pow_eq_one {x y : Y} (hc : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center Y) {n : ℕ}
    (hxn : x ^ n ∈ Subgroup.center Y) : (x * y * x⁻¹ * y⁻¹) ^ n = 1 := by
  have h := conj_pow_eq_of_central hc n
  have h1 : x ^ n * y * (x ^ n)⁻¹ = y := by
    rw [← Subgroup.mem_center_iff.mp hxn y, mul_assoc, mul_inv_cancel, mul_one]
  rw [h1] at h
  have h2 : (x * y * x⁻¹ * y⁻¹) ^ n * y = 1 * y := by rw [← h, one_mul]
  exact mul_right_cancel h2

theorem pow_eq_one_of_mem_commutator {R : Subgroup Y} (hRR : ⁅R, R⁆ ≤ Subgroup.center Y)
    {s : ℕ} (hpow : ∀ x ∈ R, x ^ s ∈ Subgroup.center Y) :
    ∀ c ∈ ⁅R, R⁆, c ^ s = 1 := by
  intro c hc
  rw [Subgroup.commutator_def] at hc
  induction hc using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hg
    have hcen : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center Y := by
      have := hRR (Subgroup.commutator_mem_commutator hx hy)
      rwa [commutatorElement_def] at this
    rw [commutatorElement_def]
    exact commutator_pow_eq_one hcen (hpow x hx)
  | one => exact one_pow s
  | mul a b ha hb iha ihb =>
    have haZ : a ∈ Subgroup.center Y := hRR (by rw [Subgroup.commutator_def]; exact ha)
    have hab : Commute a b := (Subgroup.mem_center_iff.mp haZ b).symm
    rw [hab.mul_pow, iha, ihb, one_mul]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

end Commutators

theorem exists_noncentral_normal {Y : Type*} [Group Y] [Finite Y] [Group.IsPerfect Y]
    (M : Subgroup Y) [M.Normal] (hM : Group.IsSolvable M) (hMZ : ¬ M ≤ Subgroup.center Y) :
    ∃ R : Subgroup Y, R.Normal ∧ Subgroup.center Y ≤ R ∧ ¬ R ≤ Subgroup.center Y ∧
      ⁅R, R⁆ ≤ Subgroup.center Y ∧ ∃ s : ℕ, s.Prime ∧ (∀ x ∈ R, x ^ s ∈ Subgroup.center Y) ∧
        ∃ y : Y, ∃ x ∈ R, y * x * y⁻¹ * x⁻¹ ∉ Subgroup.center Y := by
  classical
  set Z := Subgroup.center Y with hZ
  let D : ℕ → Subgroup Y := fun k => Nat.rec M (fun _ D => ⁅D, D⁆) k
  have hD0 : D 0 = M := rfl
  have hDs : ∀ k, D (k + 1) = ⁅D k, D k⁆ := fun _ => rfl
  have hDn : ∀ k, (D k).Normal := by
    intro k
    induction k with
    | zero => rw [hD0]; infer_instance
    | succ k ih => rw [hDs]; exact @Subgroup.commutator_normal _ _ (D k) (D k) ih ih
  have hDle : ∀ k, D k ≤ (derivedSeries M k).map M.subtype := by
    intro k
    induction k with
    | zero =>
      rw [hD0, derivedSeries_zero, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    | succ k ih =>
      rw [hDs, derivedSeries_succ, Subgroup.map_commutator]
      exact Subgroup.commutator_mono ih ih
  obtain ⟨n, hn⟩ := hM.solvable
  have hex : ∃ k, D k ≤ Z := ⟨n, by
    have := hDle n
    rw [hn, Subgroup.map_bot] at this
    exact this.trans bot_le⟩
  have hdec : DecidablePred fun n => D n ≤ Z := Classical.decPred _
  set k := @Nat.find (fun n => D n ≤ Z) hdec hex with hk
  have hkZ : D k ≤ Z := @Nat.find_spec (fun n => D n ≤ Z) hdec hex
  have hk0 : k ≠ 0 := by
    intro h0
    apply hMZ
    have h1 := hkZ
    rw [h0, hD0] at h1
    exact h1
  set j := k - 1 with hj
  have hjk : j + 1 = k := by omega
  have hDj : ¬ D j ≤ Z := @Nat.find_min (fun n => D n ≤ Z) hdec hex j (by omega)
  have hDjj : ⁅D j, D j⁆ ≤ Z := by rw [← hDs j, hjk]; exact hkZ
  have : (D j).Normal := hDn j
  set π := QuotientGroup.mk' Z with hπ
  set B : Subgroup (Y ⧸ Z) := (D j).map π with hB
  have hBn : B.Normal := Subgroup.Normal.map (hDn j) π (QuotientGroup.mk'_surjective Z)
  have hBcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have h1 : ⁅x, y⁆ ∈ Z := hDjj (Subgroup.commutator_mem_commutator hx hy)
    have h2 : π ⁅x, y⁆ = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact h1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2
  obtain ⟨d, hdD, hdZ⟩ : ∃ d ∈ D j, d ∉ Z := by
    by_contra hall
    push Not at hall
    exact hDj fun x hx => hall x hx
  have hπd : π d ≠ 1 := by
    rw [hπ, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]; exact hdZ
  have hB1 : Nat.card B ≠ 1 := by
    intro h1
    have : Subsingleton B := (Nat.card_eq_one_iff_unique.mp h1).1
    have := Subsingleton.elim (⟨π d, d, hdD, rfl⟩ : B) 1
    exact hπd (congrArg Subtype.val this)
  set s := (Nat.card B).minFac with hs
  have hsp : s.Prime := Nat.minFac_prime hB1
  have : Fact s.Prime := ⟨hsp⟩
  obtain ⟨b₀, hb₀⟩ := exists_prime_orderOf_dvd_card' (G := B) s (Nat.minFac_dvd _)
  let Rbar : Subgroup (Y ⧸ Z) :=
    { carrier := {x | x ∈ B ∧ x ^ s = 1}
      one_mem' := ⟨B.one_mem, one_pow s⟩
      mul_mem' := fun {a b} ha hb => ⟨B.mul_mem ha.1 hb.1, by
        rw [(show Commute a b from hBcomm a ha.1 b hb.1).mul_pow, ha.2, hb.2, one_mul]⟩
      inv_mem' := fun {a} ha => ⟨B.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hRbarn : Rbar.Normal := ⟨fun a ha g => ⟨hBn.conj_mem a ha.1 g, by
    rw [conj_pow, ha.2, mul_one, mul_inv_cancel]⟩⟩
  set R := Rbar.comap π with hR
  have hRn : R.Normal := Subgroup.Normal.comap hRbarn π
  have hmemR : ∀ x, x ∈ R ↔ π x ∈ B ∧ π x ^ s = 1 := fun x => Iff.rfl
  have hZR : Z ≤ R := by
    intro z hz
    have hπz : π z = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hz
    rw [hmemR, hπz]
    exact ⟨B.one_mem, one_pow s⟩
  obtain ⟨y₀, hy₀⟩ := QuotientGroup.mk'_surjective Z (b₀ : Y ⧸ Z)
  have hy₀R : y₀ ∈ R := by
    rw [hmemR, ← hπ] at *
    rw [hy₀]
    refine ⟨b₀.2, ?_⟩
    rw [← Subgroup.coe_pow, ← hb₀, pow_orderOf_eq_one, Subgroup.coe_one]
  have hy₀Z : y₀ ∉ Z := by
    intro hz
    have h1 : π y₀ = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hz
    rw [← hπ] at hy₀
    rw [hy₀] at h1
    have : b₀ = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hb₀
    exact hsp.one_lt.ne hb₀
  have hRR : ⁅R, R⁆ ≤ Z := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have h2 : π ⁅x, y⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hBcomm _ ((hmemR x).mp hx).1 _ ((hmemR y).mp hy).1
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact h2
  have hpow : ∀ x ∈ R, x ^ s ∈ Z := by
    intro x hx
    have h1 : π (x ^ s) = 1 := by rw [map_pow]; exact ((hmemR x).mp hx).2
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  refine ⟨R, hRn, hZR, fun h => hy₀Z (h hy₀R), hRR, s, hsp, hpow, ?_⟩
  by_contra hall
  push Not at hall
  have h1 : ⁅(⊤ : Subgroup Y), R⁆ ≤ Z := by
    rw [Subgroup.commutator_le]
    intro y _ x hx
    rw [commutatorElement_def]
    exact hall y x hx
  have hcen : ∀ H : Subgroup Y, H ≤ Z → ⁅H, (⊤ : Subgroup Y)⁆ = ⊥ := by
    intro H hH
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.coe_top,
      Subgroup.centralizer_univ]
    exact hH
  have hc1 : ⁅⁅(⊤ : Subgroup Y), R⁆, (⊤ : Subgroup Y)⁆ = ⊥ := hcen _ h1
  have hc2 : ⁅⁅R, (⊤ : Subgroup Y)⁆, (⊤ : Subgroup Y)⁆ = ⊥ := by
    rw [Subgroup.commutator_comm R]; exact hc1
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate hc1 hc2
  have htop : ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ = ⊤ := by
    rw [← commutator_def]
    exact Group.IsPerfect.commutator_eq_top
  rw [htop, Subgroup.commutator_eq_bot_iff_le_centralizer, ← Subgroup.le_centralizer_iff,
    Subgroup.coe_top, Subgroup.centralizer_univ] at h3
  exact hy₀Z (h3 hy₀R)

end LSSolvableProof

end CFSG.RankThree.PartTwo.Sec11
