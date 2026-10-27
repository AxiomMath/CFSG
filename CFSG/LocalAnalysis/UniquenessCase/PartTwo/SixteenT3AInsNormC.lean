module

public import CFSG.Assembly.Defs
public import CFSG.Quasithin.Background.Ordering

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped Pointwise

theorem s16t_a_exists_fixed_vector {T : Type} [CommGroup T] [Finite T] (hT : ∀ v : T, v ^ 2 = 1)
    {ι : Type} [Fintype ι] (hι : Fintype.card ι = 3) {Y : ι → Subgroup T}
    (hind : iSupIndep Y) (hY : ∀ i, Y i ≠ ⊥) {a : MulAut T} (ha3 : a ^ 3 = 1)
    (hperm : ∀ i, ∃ j, (Y i).map a.toMonoidHom = Y j)
    (hmove : ∀ i, (Y i).map a.toMonoidHom ≠ Y i) {B : Subgroup (MulAut T)} (hB : IsPGroup 2 ↥B)
    (hBa : ∀ b ∈ B, b * a * b⁻¹ ∈ Subgroup.zpowers a) :
    ∃ n : T, n ≠ 1 ∧ a n = n ∧ ∀ b ∈ B, b n = n := by
  classical
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  let i₀ : ι := Classical.arbitrary ι
  obtain ⟨v, hv, hv1⟩ := (Subgroup.bot_or_exists_ne_one (Y i₀)).resolve_left (hY i₀)
  obtain ⟨j₁, hj₁⟩ := hperm i₀
  obtain ⟨j₂, hj₂⟩ := hperm j₁
  have hj₁_ne : j₁ ≠ i₀ := by
    intro h
    rw [h] at hj₁
    exact hmove i₀ hj₁
  have hj₂_ne : j₂ ≠ j₁ := by
    intro h
    rw [h] at hj₂
    exact hmove j₁ hj₂
  have haa : (Y i₀).map (a ^ 2).toMonoidHom = Y j₂ := by
    have hcomp : (a ^ 2).toMonoidHom = a.toMonoidHom.comp a.toMonoidHom := by
      ext x
      rfl
    rw [hcomp, ← Subgroup.map_map, hj₁, hj₂]
  have hj₂_ne_i₀ : j₂ ≠ i₀ := by
    intro h
    rw [h] at haa
    have hconj : (Y i₀).map a.toMonoidHom = Y i₀ := by
      have h3 : (Y i₀).map (a * a ^ 2).toMonoidHom = Y i₀ := by
        rw [show a * a ^ 2 = a ^ 3 by rw [← pow_succ'], ha3]
        exact Subgroup.map_id (Y i₀)
      have hcomp : (a * a ^ 2).toMonoidHom = a.toMonoidHom.comp (a ^ 2).toMonoidHom := by
        ext x
        rfl
      rw [hcomp, ← Subgroup.map_map, haa] at h3
      exact h3
    exact hmove i₀ hconj
  have hS : ({i₀, j₁, j₂} : Finset ι).SupIndep Y := hind.supIndep' _
  have hts : ({j₁, j₂} : Finset ι) ⊆ {i₀, j₁, j₂} := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    tauto
  have hi_not : i₀ ∉ ({j₁, j₂} : Finset ι) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hj₁_ne.symm, hj₂_ne_i₀.symm⟩
  have hdisj : Disjoint (Y i₀) (Y j₁ ⊔ Y j₂) := by
    have h := hS hts (by simp) hi_not
    simpa using h
  let n : T := v * (a v * a (a v))
  have ha3v : a (a (a v)) = v := by
    have h : (a ^ 3) v = (1 : MulAut T) v := by rw [ha3]
    simpa [pow_succ, MulAut.mul_apply] using h
  have han : a n = n := by
    have hn : n = v * (a v * a (a v)) := rfl
    rw [hn, map_mul, map_mul, ha3v]
    ac_rfl
  have hav : a v ∈ Y j₁ := by
    rw [← hj₁]
    exact ⟨v, hv, rfl⟩
  have haav : a (a v) ∈ Y j₂ := by
    rw [← hj₂]
    exact ⟨a v, hav, rfl⟩
  have hprod : a v * a (a v) ∈ Y j₁ ⊔ Y j₂ := Subgroup.mul_mem_sup hav haav
  have hn1 : n ≠ 1 := by
    intro h
    have hn_eq : v * (a v * a (a v)) = 1 := by
      have hn : n = v * (a v * a (a v)) := rfl
      rw [← hn]
      exact h
    have hv_eq : v = (a v * a (a v))⁻¹ := eq_inv_of_mul_eq_one_left hn_eq
    have hmem : v ∈ Y j₁ ⊔ Y j₂ := by
      rw [hv_eq]
      exact Subgroup.inv_mem _ hprod
    exact hv1 (Subgroup.disjoint_def.mp hdisj hv hmem)
  let C : Subgroup T :=
    { carrier := {x : T | a x = x}
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [map_mul, hx, hy]
      one_mem' := by
        simp only [Set.mem_setOf_eq]
        exact map_one a
      inv_mem' := by
        intro x hx
        simp only [Set.mem_setOf_eq] at hx ⊢
        rw [map_inv, hx] }
  have hnC : n ∈ C := han
  let S : SubMulAction ↥B T :=
    { carrier := {x : T | a x = x ∧ x ≠ 1}
      smul_mem' := by
        rintro ⟨b, hb⟩ x ⟨hax, hx1⟩
        change a (b x) = b x ∧ b x ≠ 1
        refine ⟨?_, ?_⟩
        · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hBa b⁻¹ (B.inv_mem hb))
          rw [inv_inv] at hk
          have hstab : a ∈ MulAction.stabilizer (MulAut T) x :=
            MulAction.mem_stabilizer_iff.mpr hax
          have hkx : (b⁻¹ * a * b) x = x := by
            rw [← hk]
            exact MulAction.mem_stabilizer_iff.mp (Subgroup.zpow_mem _ hstab k)
          have hconj : a * b = b * (b⁻¹ * a * b) := by
            rw [← mul_assoc b (b⁻¹ * a) b, ← mul_assoc b b⁻¹ a, mul_inv_cancel, one_mul]
          calc a (b x) = (a * b) x := rfl
            _ = (b * (b⁻¹ * a * b)) x := congrArg (fun f : MulAut T => f x) hconj
            _ = b ((b⁻¹ * a * b) x) := rfl
            _ = b x := by rw [hkx]
        · intro h
          exact hx1 (b.injective (by rw [h, map_one])) }
  have hC2 : IsPGroup 2 ↥C := fun x => ⟨1, by
    show x ^ (2 ^ 1) = 1
    rw [pow_one]
    exact Subtype.ext (hT x)⟩
  obtain ⟨m, hm⟩ := hC2.exists_card_eq
  have hCne : C ≠ ⊥ := by
    intro hbot
    have h1 : n ∈ (⊥ : Subgroup T) := hbot ▸ hnC
    exact hn1 (by simpa using h1)
  have hm1 : 0 < m := by
    have hlt : 1 < Nat.card ↥C := by
      have hne : (⟨n, hnC⟩ : ↥C) ≠ 1 := by
        intro h
        exact hn1 (congrArg Subtype.val h)
      haveI : Nontrivial ↥C := ⟨⟨n, hnC⟩, 1, hne⟩
      exact Finite.one_lt_card
    rw [hm] at hlt
    by_contra h
    have hm0 : m = 0 := by omega
    rw [hm0, pow_zero] at hlt
    omega
  have hSeq : (S : Set T) = (C : Set T) \ {1} := rfl
  have hcardS : Nat.card ↥S = Nat.card ↥C - 1 := by
    change Nat.card (S : Set T) = Nat.card (C : Set T) - 1
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    rw [hSeq, Set.ncard_sdiff_singleton_of_mem C.one_mem]
  have hndvd : ¬ 2 ∣ Nat.card ↥S := by
    rw [hcardS, hm]
    have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hpow]
    exact Nat.two_not_dvd_two_mul_sub_one (pow_pos (by norm_num) (m - 1))
  obtain ⟨s, hs⟩ := hB.nonempty_fixed_point_of_prime_not_dvd_card ↥S hndvd
  refine ⟨s.1, s.2.2, s.2.1, ?_⟩
  intro b hb
  have h := congrArg Subtype.val (MulAction.mem_fixedPoints.mp hs (⟨b, hb⟩ : ↥B))
  simpa using h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
