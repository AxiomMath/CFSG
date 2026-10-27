module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
public import CFSG.Assembly.Defs
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

namespace Res423Two

open Equiv Equiv.Perm Item434AltPerm

theorem check_comm_A0 : ∀ u v : Fin 3 → ZMod 3, ∀ j : Fin 3, j ≠ 0 →
    vecPerm 9 u * (vecPerm 9 v * tt 9 ^ (j : ℕ)) = (vecPerm 9 v * tt 9 ^ (j : ℕ)) * vecPerm 9 u →
      u 0 = u 1 ∧ u 1 = u 2 := by
  decide +kernel

theorem check_fpf_W : ∀ v : Fin 3 → ZMod 3, ∀ j : Fin 3, j ≠ 0 → ∀ p : Fin 9,
    (vecPerm 9 v * tt 9 ^ (j : ℕ)) p ≠ p := by
  decide +kernel

theorem check_fpf_const : ∀ u : Fin 3 → ZMod 3, u 0 = u 1 → u 1 = u 2 → vecPerm 9 u ≠ 1 →
    ∀ p : Fin 9, vecPerm 9 u p ≠ p := by
  decide +kernel

theorem fpf_of_le_W_of_not_le_A0 {D : Subgroup (Perm (Fin 9))} (hDW : D ≤ W 9)
    (hDA : ¬ D ≤ A0 9) (hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) {d : Perm (Fin 9)} (hd : d ∈ D)
    (hd1 : d ≠ 1) (p : Fin 9) : d p ≠ p := by
  have hf := wFacts_nine
  obtain ⟨x, hxD, hxA⟩ := Set.not_subset.mp hDA
  obtain ⟨v, j, rfl⟩ := mem_W hf (hDW hxD)
  have hj : j ≠ 0 := by
    rintro rfl
    apply hxA
    simpa using vecPerm_mem_A0 hf.toA0Facts v
  obtain ⟨w, k, rfl⟩ := mem_W hf (hDW hd)
  by_cases hk : k = 0
  · subst hk
    simp only [Fin.val_zero, pow_zero, mul_one] at hd hd1 ⊢
    obtain ⟨h01, h12⟩ := check_comm_A0 w v j hj (hDc _ hd _ hxD)
    exact check_fpf_const w h01 h12 hd1 p
  · exact check_fpf_W w k hk p

theorem card_centralizer_fpf_nine {d : Perm (Fin 9)} (h3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    (hfpf : ∀ p, d p ≠ p) : Nat.card (Subgroup.centralizer ({d} : Set (Perm (Fin 9)))) = 162 := by
  have hord : orderOf d = 3 := orderOf_eq_prime h3 hd1
  obtain ⟨m, hm⟩ := cycleType_prime_order (σ := d) (by rw [hord]; exact Nat.prime_three)
  rw [hord] at hm
  have hsupp : d.support.card = 9 := by
    have : d.support = Finset.univ := Finset.eq_univ_iff_forall.mpr fun p => mem_support.mpr
      (hfpf p)
    rw [this, Finset.card_univ, Fintype.card_fin]
  have hsum := sum_cycleType d
  rw [hm, Multiset.sum_replicate, hsupp, smul_eq_mul] at hsum
  have hm2 : m = 2 := by omega
  subst hm2
  rw [nat_card_centralizer, hm]
  decide

theorem exists_apply_eq_of_fpf {D : Subgroup (Perm (Fin 9))} (hD9 : Nat.card D = 9)
    (hfpf : ∀ d ∈ D, d ≠ 1 → ∀ p, d p ≠ p) (p q : Fin 9) : ∃ d ∈ D, d p = q := by
  let f : D → Fin 9 := fun d => (d : Perm (Fin 9)) p
  have hinj : Function.Injective f := by
    intro a b hab
    by_contra hne
    have h1 : (b⁻¹ * a : D) ≠ 1 := fun h => hne (inv_mul_eq_one.mp h).symm
    apply hfpf _ (b⁻¹ * a).2 (fun h => h1 (Subtype.ext h)) p
    change (b : Perm (Fin 9))⁻¹ ((a : Perm (Fin 9)) p) = p
    rw [show (a : Perm (Fin 9)) p = (b : Perm (Fin 9)) p from hab]
    exact (b : Perm (Fin 9)).symm_apply_apply p
  have hbij := (Nat.bijective_iff_injective_and_card f).mpr
    ⟨hinj, by rw [hD9, Nat.card_eq_fintype_card, Fintype.card_fin]⟩
  obtain ⟨d, hd⟩ := hbij.2 q
  exact ⟨d, d.2, hd⟩

theorem eq_one_of_commute_of_transitive {D : Subgroup (Perm (Fin 9))}
    (htr : ∀ p q : Fin 9, ∃ d ∈ D, d p = q) {y : Perm (Fin 9)} (hy2 : y ^ 2 = 1)
    (hy : ∀ d ∈ D, y * d = d * y) : y = 1 := by
  obtain ⟨p, hp⟩ : ∃ p, y p = p := by
    by_contra hcon
    push Not at hcon
    have hsupp : y.support.card = 9 := by
      have : y.support = Finset.univ := Finset.eq_univ_iff_forall.mpr fun p => mem_support.mpr
        (hcon p)
      rw [this, Finset.card_univ, Fintype.card_fin]
    have h2 := two_dvd_card_support hy2
    rw [hsupp] at h2
    omega
  refine Equiv.ext fun q => ?_
  obtain ⟨d, hd, rfl⟩ := htr p q
  rw [Perm.one_apply, ← Perm.mul_apply, hy d hd, Perm.mul_apply, hp]

theorem eq_bot_of_le_W_of_not_le_A0 {D X : Subgroup (Perm (Fin 9))} (hDW : D ≤ W 9)
    (hDA : ¬ D ≤ A0 9) (hDe : CFSG.Assembly.IsElemAbelian 3 D) (hD9 : Nat.card D = 9)
    (hX : ¬ 3 ∣ Nat.card X) (hN : D ≤ Subgroup.normalizer (X : Set (Perm (Fin 9)))) : X = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hDe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hfpf : ∀ d ∈ D, d ≠ 1 → ∀ p, d p ≠ p := fun d hd hd1 p =>
    fpf_of_le_W_of_not_le_A0 hDW hDA hDc hd hd1 p
  have htr := exists_apply_eq_of_fpf hD9 hfpf
  have hX3 : Nat.Coprime 3 (Nat.card X) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hX
  rw [eq_bot_iff]
  refine Sec5.le_of_forall_inf_centralizer_sub_le (k := 1) Nat.prime_three hDe
    (by rw [hD9]; norm_num) hN hX3 fun H hHD hH3 => ?_
  set Y := X ⊓ Subgroup.centralizer (H : Set (Perm (Fin 9))) with hY
  have hH1 : H ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hH3
    norm_num at hH3
  obtain ⟨⟨d, hdH⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hH1
  have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
  have hd3 : d ^ 3 = 1 := hDe.2 d (hHD hdH)
  have hYd : Y ≤ Subgroup.centralizer ({d} : Set (Perm (Fin 9))) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2 d hdH).symm
  have hY3 : Nat.Coprime (Nat.card Y) 3 :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le inf_le_left) hX3.symm
  have hdvd : Nat.card Y ∣ 162 := by
    rw [← card_centralizer_fpf_nine hd3 hd1' (hfpf d (hHD hdH) hd1')]
    exact Subgroup.card_dvd_of_le hYd
  have h2 : Nat.card Y ∣ 2 := by
    have hc : Nat.Coprime (Nat.card Y) 81 := Nat.Coprime.pow_right 4 hY3
    exact hc.dvd_of_dvd_mul_right (by simpa using hdvd)
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h2'
  · rw [Subgroup.card_eq_one.mp h1]
  · exfalso
    have hYn : ∀ a ∈ D, ∀ y ∈ Y, a * y * a⁻¹ ∈ Y := by
      intro a ha y hy
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hN ha) y).mp (Subgroup.mem_inf.mp hy).1
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        have hyh := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2 h hh
        have hah : Commute h a := hDc h (hHD hh) a ha
        have hhy : Commute h y := hyh
        exact ((hah.mul_right hhy).mul_right hah.inv_right).eq
    obtain ⟨⟨y, hyY⟩, hy1, -⟩ := (Nat.card_eq_two_iff' (1 : Y)).mp h2'
    have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
    have hy2 : y ^ 2 = 1 := by
      have h := orderOf_dvd_natCard (⟨y, hyY⟩ : Y)
      rw [Subgroup.orderOf_mk, h2'] at h
      exact orderOf_dvd_iff_pow_eq_one.mp h
    have hcomm : ∀ a ∈ D, y * a = a * y := by
      intro a ha
      have hmem := hYn a ha y hyY
      have hne : (⟨a * y * a⁻¹, hmem⟩ : Y) ≠ 1 := by
        intro h
        apply hy1'
        have h' : a * y * a⁻¹ = 1 := congrArg Subtype.val h
        rw [mul_inv_eq_one, mul_eq_left] at h'
        exact h'
      obtain ⟨z, -, hz⟩ := (Nat.card_eq_two_iff' (1 : Y)).mp h2'
      have e1 := hz _ hne
      have e2 := hz _ hy1
      have e : a * y * a⁻¹ = y := congrArg Subtype.val (e1.trans e2.symm)
      calc y * a = a * y * a⁻¹ * a := by rw [e]
        _ = a * y := by group
    exact hy1' (eq_one_of_commute_of_transitive htr hy2 hcomm)

end Res423Two

end CFSG.RankThree.PartTwo.Sec4
