module

public import CFSG.RankThree.PartOne.Q1327T.R8Homo
import CFSG.GroupTheory.WeirSylow.Orthogonal
import CFSG.RankThree.PartOne.N143X.EvenSmall
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.RankThree.PartOne.Q1327T.R8

open CFSG CFSG.Assembly.LowTwoRank CFSG.GroupTheory.WeirSylow

theorem not_dvd_two_pow {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ 2 ^ f := fun h =>
  hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))

theorem sp3_rank_cases {e : ℕ} (he : 0 < e) :
    (if Even e then 2 * 3 else 3) / e ≤ 3 ∧
      ((if Even e then 2 * 3 else 3) / e < 2 ∨ 0 + 2 < (if Even e then 2 * 3 else 3) / e) := by
  by_cases hev : Even e
  · rw [ite_eq_left hev]
    obtain ⟨k, hk⟩ := hev
    by_cases h2 : e = 2
    · subst h2
      norm_num
    · have h4 : 4 ≤ e := by omega
      exact ⟨Nat.div_le_of_le_mul (by omega), Or.inl ((Nat.div_lt_iff_lt_mul he).2 (by omega))⟩
  · rw [ite_eq_right hev]
    by_cases h1 : e = 1
    · subst h1
      norm_num
    · have h3 : 3 ≤ e := by
        have : e ≠ 2 := fun h => hev (h ▸ ⟨1, rfl⟩)
        omega
      exact ⟨Nat.div_le_of_le_mul (by omega), Or.inl ((Nat.div_lt_iff_lt_mul he).2 (by omega))⟩

theorem false_of_plane_sp6 {K : Type} [Field K] [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f)
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (F : Subgroup (GL (Fin 3 ⊕ Fin 3) K))
    (hFM : F ≤ StatedSp 3 K) [IsElementaryAbelian p F] (hFc : Nat.card F = p ^ 2)
    (hmax : ∀ D : Subgroup (GL (Fin 3 ⊕ Fin 3) K), D ≤ StatedSp 3 K → IsElementaryAbelian p D →
      F ≤ D → D ≤ Subgroup.centralizer (F : Set (GL (Fin 3 ⊕ Fin 3) K)) →
      Nat.card D ≤ Nat.card F) : False := by
  classical
  have hp := (Fact.out : p.Prime)
  have hp1 : Odd p := hp.odd_of_ne_two (by omega)
  have : Fintype K := Fintype.ofFinite K
  have hKc : Fintype.card K = 2 ^ f := by rw [Fintype.card_eq_nat_card, hK]
  have hpK : ¬ p ∣ Fintype.card K := by rw [hKc]; exact not_dvd_two_pow hp (by omega)
  let M : Subgroup (GL (Fin 3 ⊕ Fin 3) K) := StatedSp 3 K
  let F₁ : Subgroup ↥M := F.subgroupOf M
  have hF₁el : IsElementaryAbelian p F₁ := IsElementaryAbelian.subgroupOf hFM
  have hF₁c : Nat.card F₁ = p ^ 2 := by
    rw [← hFc]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFM).toEquiv)
  refine false_of_homocyclic_sylow (F := F₁) (r := 0) hF₁c (fun D hD hFD hDc => ?_)
    (fun S => ?_)
  ·
    have hDM : D.map M.subtype ≤ M := fun x ⟨y, _, hy⟩ => hy ▸ y.2
    have hFle : F ≤ D.map M.subtype := fun x hx => ⟨⟨x, hFM hx⟩, hFD hx, rfl⟩
    have hcent : D.map M.subtype ≤ Subgroup.centralizer (F : Set (GL (Fin 3 ⊕ Fin 3) K)) := by
      rintro _ ⟨d, hd, rfl⟩ x hx
      have := Subgroup.mem_centralizer_iff.1 (hDc hd) ⟨x, hFM hx⟩ hx
      exact congrArg Subtype.val this
    have hel : IsElementaryAbelian p (D.map M.subtype) := by
      have := hD
      exact IsElementaryAbelian.map_subtype
    have h1 := hmax _ hDM hel hFle hcent
    rw [Subgroup.card_map_of_injective M.subtype_injective] at h1
    rw [hFc] at h1
    simpa using h1
  ·
    obtain ⟨φ⟩ := sylow_Sp hp1 K hpK 3 S
    have he : 0 < weirE p K := weirE_pos hpK
    have ha : 1 ≤ weirA p K := one_le_weirA hpK
    obtain ⟨hle3, hcases⟩ := sp3_rank_cases he
    refine ⟨(if Even (weirE p K) then 2 * 3 else 3) / weirE p K, weirA p K, ha, ?_, hcases⟩
    obtain ⟨ψ⟩ := nonempty_sigmaModel_mulEquiv_homo (p := p) (e := weirE p K) (a := weirA p K)
      (N := if Even (weirE p K) then 2 * 3 else 3) (by omega)
    exact ⟨φ.trans ψ⟩

theorem gl4_rank_cases {e : ℕ} (he : 0 < e) (he2 : e ≠ 2) :
    4 / e ≤ 4 ∧ (4 / e < 2 ∨ 1 + 2 < 4 / e) := by
  by_cases h1 : e = 1
  · subst h1
    norm_num
  · have h3 : 3 ≤ e := by omega
    exact ⟨Nat.div_le_self _ _, Or.inl ((Nat.div_lt_iff_lt_mul he).2 (by omega))⟩

theorem false_of_plane_sl4 {K : Type} [Field K] [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f)
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (F : Subgroup (GL (Fin 4) K))
    (hFM : F ≤ StatedSL 4 K) [IsElementaryAbelian p F] (hFc : Nat.card F = p ^ 2)
    (hmax : ∀ D : Subgroup (GL (Fin 4) K), D ≤ StatedSL 4 K → IsElementaryAbelian p D →
      F ≤ D → D ≤ Subgroup.centralizer (F : Set (GL (Fin 4) K)) → Nat.card D ≤ Nat.card F)
    (he2 : orderOf ((Nat.card K : ℕ) : ZMod p) ≠ 2) : False := by
  classical
  have hp := (Fact.out : p.Prime)
  have hp1 : Odd p := hp.odd_of_ne_two (by omega)
  have : Fintype K := Fintype.ofFinite K
  have hKc : Fintype.card K = 2 ^ f := by rw [Fintype.card_eq_nat_card, hK]
  have hpK : ¬ p ∣ Fintype.card K := by rw [hKc]; exact not_dvd_two_pow hp (by omega)
  refine false_of_homocyclic_sylow (F := F) (r := 1) hFc (fun D hD hFD hDc => ?_) (fun S => ?_)
  ·
    let φ : D →* Kˣ := (Matrix.GeneralLinearGroup.det).comp D.subtype
    have hdet1 : ∀ x : GL (Fin 4) K, x ∈ StatedSL 4 K →
        Matrix.GeneralLinearGroup.det x = 1 := fun x hx =>
      Units.ext (N143X.det_eq_one_of_mem_statedSL' hx)
    let D' : Subgroup (GL (Fin 4) K) := φ.ker.map D.subtype
    have hD'D : D' ≤ D := by
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    have hD'SL : D' ≤ StatedSL 4 K := by
      rintro _ ⟨y, hy, rfl⟩
      refine Subgroup.subset_closure ?_
      have h1 : Matrix.GeneralLinearGroup.det (y : GL (Fin 4) K) = 1 := hy
      have h2 := congrArg (fun u : Kˣ => (u : K)) h1
      simpa using h2
    have hFD' : F ≤ D' := fun x hx =>
      ⟨⟨x, hFD hx⟩, hdet1 x (hFM hx), rfl⟩
    have hD'el : IsElementaryAbelian p D' := isElementaryAbelian_of_le hD hD'D
    have hD'c : D' ≤ Subgroup.centralizer (F : Set (GL (Fin 4) K)) := hD'D.trans hDc
    have h1 : Nat.card D' ≤ p ^ 2 := by
      have := hmax D' hD'SL hD'el hFD' hD'c
      rwa [hFc] at this
    have hD'card : Nat.card D' = Nat.card φ.ker :=
      Subgroup.card_map_of_injective D.subtype_injective
    have hrange : Nat.card φ.range ≤ p := by
      have hel : IsElementaryAbelian p φ.range := by
        refine { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (mul_comm _ _)⟩⟩
                 exponent_dvd_p := ?_ }
        refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun y => ?_
        obtain ⟨d, hd⟩ := y.2
        apply Subtype.ext
        change (y : Kˣ) ^ p = 1
        rw [← hd, ← map_pow]
        have : d ^ p = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (A := D) _ d.2)
        rw [this, map_one]
      have hexp : Monoid.exponent ↥φ.range ∣ p := IsElementaryAbelian.exponent_dvd_p p _
      rw [IsCyclic.exponent_eq_card] at hexp
      exact Nat.le_of_dvd hp.pos hexp
    have h2 : Nat.card D = Nat.card φ.ker * Nat.card φ.range := by
      rw [← Subgroup.index_ker φ]
      exact (Subgroup.card_mul_index φ.ker).symm
    calc Nat.card D = Nat.card φ.ker * Nat.card φ.range := h2
      _ ≤ p ^ 2 * p := by
          rw [← hD'card]
          exact Nat.mul_le_mul h1 hrange
      _ = p ^ (1 + 2) := by ring
  · obtain ⟨φ⟩ := sylow_GL hp1 K hpK 4 S
    have he : 0 < weirE p K := weirE_pos hpK
    have ha : 1 ≤ weirA p K := one_le_weirA hpK
    have he2' : weirE p K ≠ 2 := by
      have : weirE p K = orderOf ((Nat.card K : ℕ) : ZMod p) := by
        rw [weirE, Nat.card_eq_fintype_card]
      rw [this]
      exact he2
    obtain ⟨hle4, hcases⟩ := gl4_rank_cases he he2'
    refine ⟨4 / weirE p K, weirA p K, ha, ?_, hcases⟩
    obtain ⟨ψ⟩ := nonempty_sigmaModel_mulEquiv_homo (p := p) (e := weirE p K) (a := weirA p K)
      (N := 4) (by omega)
    exact ⟨φ.trans ψ⟩

end CFSG.RankThree.PartOne.Q1327T.R8
