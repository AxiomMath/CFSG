module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3A7PowA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3A7PowB
public import TauCeti.GroupTheory.OrderOfElement.PPart
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

private theorem s16t3_sign_viaEmbedding {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : Equiv.Perm α) (ι : α ↪ β) :
    Equiv.Perm.sign (e.viaEmbedding ι) = Equiv.Perm.sign e := by
  simpa [Equiv.Perm.viaEmbedding] using
    Equiv.Perm.sign_extendDomain e (Equiv.ofInjective ι.1 ι.2)

private noncomputable def s16t3_altHom {n : ℕ} (h5 : 5 ≤ n) :
    alternatingGroup (Fin 5) →* alternatingGroup (Fin n) where
  toFun x := ⟨(x : Equiv.Perm (Fin 5)).viaEmbedding (Fin.castLEEmb h5), by
    rw [Equiv.Perm.mem_alternatingGroup, s16t3_sign_viaEmbedding]
    exact (Equiv.Perm.mem_alternatingGroup).mp x.2⟩
  map_one' := by
    apply Subtype.ext
    change Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h5) (1 : Equiv.Perm (Fin 5)) = 1
    rw [map_one]
  map_mul' x y := by
    apply Subtype.ext
    change Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h5)
        ((x : Equiv.Perm (Fin 5)) * (y : Equiv.Perm (Fin 5))) =
      Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h5) (x : Equiv.Perm (Fin 5)) *
        Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h5) (y : Equiv.Perm (Fin 5))
    rw [map_mul]

private theorem s16t3_altHom_injective {n : ℕ} (h5 : 5 ≤ n) :
    Function.Injective (s16t3_altHom h5) := by
  intro x y hxy
  apply Subtype.ext
  exact Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb h5)
    (show Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h5) (x : Equiv.Perm (Fin 5)) =
        Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h5) (y : Equiv.Perm (Fin 5)) from
      congrArg Subtype.val hxy)

private theorem s16t3_map_pPart {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (x : G) :
    f (TauCeti.pPart 3 x) = TauCeti.pPart 3 (f x) := by
  have hx0 : orderOf x ≠ 0 := by
    intro h
    have hd := orderOf_dvd_natCard x
    rw [h, zero_dvd_iff] at hd
    exact Nat.card_pos.ne' hd
  have hd : orderOf (f (TauCeti.pPart 3 x)) ∣ 3 ^ (orderOf x).factorization 3 := by
    rw [← TauCeti.orderOf_pPart (p := 3) Nat.prime_three hx0]
    exact orderOf_map_dvd f _
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd
  exact TauCeti.eq_pPart (p := 3) Nat.prime_three
    ((TauCeti.commute_pFreePart_pPart 3 x).map f)
    (by rw [← map_mul, TauCeti.pFreePart_mul_pPart])
    (fun h3 => TauCeti.not_dvd_orderOf_pFreePart (p := 3) Nat.prime_three hx0
      (dvd_trans h3 (orderOf_map_dvd f _)))
    hk

private theorem s16t3_eq_one_of_pElement_of_two {Y : Type*} [Group Y] {O : Subgroup Y}
    (hO : IsPGroup 2 ↥O) {y : Y} (hyO : y ∈ O) {m : ℕ} (hy : y ^ 3 ^ m = 1) : y = 1 := by
  obtain ⟨k, hk⟩ := hO ⟨y, hyO⟩
  have hk' : y ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hcop : Nat.Coprime (3 ^ m) (2 ^ k) :=
    Nat.Coprime.pow m k ((Nat.coprime_primes Nat.prime_three Nat.prime_two).2 (by norm_num))
  rw [← orderOf_eq_one_iff]
  exact Nat.dvd_one.1 (hcop.gcd_eq_one ▸ Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hy)
    (orderOf_dvd_of_pow_eq_one hk'))

private theorem s16t3_pow_three_of_threeCycle {E : Type*} [Group E] [Finite E] {n : ℕ}
    (hn : n = 6 ∨ n = 7) (π : E →* alternatingGroup (Fin n))
    (hπ : Function.Surjective π) (hZc : π.ker ≤ center E)
    (hZ3 : ∀ z ∈ π.ker, ∀ m : ℕ, z ^ 3 ^ m = 1 → z ^ 3 = 1)
    {x : E} {k : ℕ} (hx : x ^ 3 ^ k = 1)
    (hc : Equiv.Perm.IsThreeCycle ((π x : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))) :
    x ^ 3 = 1 := by
  classical
  have h5 : 5 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  let e0 : alternatingGroup (Fin 5) :=
    ⟨Equiv.swap (0 : Fin 5) 1 * Equiv.swap (0 : Fin 5) 2, by
      exact (Equiv.Perm.isThreeCycle_swap_mul_swap_same (show (0 : Fin 5) ≠ 1 by decide)
        (show (0 : Fin 5) ≠ 2 by decide)
        (show (1 : Fin 5) ≠ 2 by decide)).mem_alternatingGroup⟩
  have he0 : Equiv.Perm.IsThreeCycle ((e0 : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same (show (0 : Fin 5) ≠ 1 by decide)
      (show (0 : Fin 5) ≠ 2 by decide) (show (1 : Fin 5) ≠ 2 by decide)
  let ψ : alternatingGroup (Fin 5) →* alternatingGroup (Fin n) := s16t3_altHom h5
  let B0 : Subgroup (alternatingGroup (Fin n)) := ψ.range
  let c0 : alternatingGroup (Fin n) := ψ e0
  have hψ_inj : Function.Injective ψ := s16t3_altHom_injective h5
  have hB0card : Nat.card B0 = 60 := by
    have h1 : Nat.card B0 = Nat.card (alternatingGroup (Fin 5)) := by
      have hcard := Subgroup.card_map_of_injective (f := ψ)
        (K := (⊤ : Subgroup (alternatingGroup (Fin 5)))) hψ_inj
      rw [Subgroup.map_top] at hcard
      simpa [B0, Subgroup.card_top] using hcard
    rw [h1, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hB0perf : commutator B0 = ⊤ := by
    have hψ'_inj : Function.Injective ψ.rangeRestrict := by
      intro a b hab
      apply hψ_inj
      exact congrArg Subtype.val hab
    let ψ' : alternatingGroup (Fin 5) ≃* B0 :=
      MulEquiv.ofBijective ψ.rangeRestrict ⟨hψ'_inj, ψ.rangeRestrict_surjective⟩
    have h : (commutator (alternatingGroup (Fin 5))).map ψ'.toMonoidHom = commutator B0 := by
      rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator]
      congr 1
      · rw [Subgroup.map_top]
        exact MonoidHom.range_eq_top.2 ψ'.surjective
      · rw [Subgroup.map_top]
        exact MonoidHom.range_eq_top.2 ψ'.surjective
    rw [commutator_alternatingGroup_eq_top (α := Fin 5) (by simp)] at h
    have htop : (⊤ : Subgroup (alternatingGroup (Fin 5))).map ψ'.toMonoidHom = ⊤ := by
      rw [Subgroup.map_top]
      exact MonoidHom.range_eq_top.2 ψ'.surjective
    rw [htop] at h
    exact h.symm
  have hc0 : Equiv.Perm.IsThreeCycle ((c0 : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) := by
    change Equiv.Perm.IsThreeCycle
      ((e0 : Equiv.Perm (Fin 5)).viaEmbedding (Fin.castLEEmb h5))
    rw [← card_support_eq_three_iff, Equiv.Perm.viaEmbedding]
    exact (@Equiv.Perm.card_support_extend_domain
      (Fin 5) _ _ (Fin n) _ _
      (fun x => x ∈ Set.range (Fin.castLEEmb h5).toFun)
      (fun a => Classical.propDecidable _)
      (Equiv.ofInjective (Fin.castLEEmb h5).toFun (Fin.castLEEmb h5).2)
      (e0 : Equiv.Perm (Fin 5))).trans (card_support_eq_three_iff.mpr he0)
  obtain ⟨g, hg⟩ := alternatingGroup.isThreeCycle_isConj (α := Fin n) (by simpa using h5) hc hc0
  obtain ⟨gE, hgE⟩ := hπ g
  let x' : E := gE * x * gE⁻¹
  have hx'img : π x' = c0 := by
    dsimp only [x']
    rw [map_mul, map_mul, map_inv, hgE, hg]
    group
  have hx'fin : x' ^ 3 ^ k = 1 := by
    dsimp only [x']
    rw [conj_pow, hx, mul_one, mul_inv_cancel]
  have hx'B0 : π x' ∈ B0 := by
    rw [hx'img]
    exact MonoidHom.mem_range.mpr ⟨e0, rfl⟩
  let Q : Subgroup E := B0.comap π
  have hx'Q : x' ∈ Q := hx'B0
  let pB : Q →* B0 := (π.comp Q.subtype).codRestrict B0 fun q => q.2
  have hpB_surj : Function.Surjective pB := by
    intro b
    obtain ⟨t, ht⟩ := hπ b.1
    exact ⟨⟨t, by show π t ∈ B0; rw [ht]; exact b.2⟩, by apply Subtype.ext; exact ht⟩
  let Z : Subgroup Q := pB.ker
  let e : Q ⧸ Z ≃* B0 := QuotientGroup.quotientKerEquivOfSurjective pB hpB_surj
  have hZcQ : Z ≤ center Q := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    have hzker : z.1 ∈ π.ker := by
      have h := MonoidHom.mem_ker.mp hz
      exact Subtype.ext_iff.mp h
    exact Subgroup.mem_center_iff.mp (hZc hzker) w.1
  have hZ3Q : ∀ z ∈ Z, ∀ m : ℕ, z ^ 3 ^ m = 1 → z ^ 3 = 1 := by
    intro z hz m hzm
    have hzker : z.1 ∈ π.ker := by
      have h := MonoidHom.mem_ker.mp hz
      exact Subtype.ext_iff.mp h
    have hzm1 : z.1 ^ 3 ^ m = 1 := by
      have h := congrArg Subtype.val hzm
      simpa using h
    exact Subtype.ext (by simpa using hZ3 z.1 hzker m hzm1)
  have hperfQ : commutator (Q ⧸ Z) = ⊤ := by
    have h : (commutator (Q ⧸ Z)).map e.toMonoidHom = commutator B0 := by
      rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator]
      congr 1
      · rw [Subgroup.map_top]; exact MonoidHom.range_eq_top.2 e.surjective
      · rw [Subgroup.map_top]; exact MonoidHom.range_eq_top.2 e.surjective
    rw [hB0perf] at h
    exact Subgroup.map_injective e.injective
      (h.trans (Subgroup.map_top_of_surjective _ e.surjective).symm)
  have h9Q : ¬ 9 ∣ Nat.card (Q ⧸ Z) := by
    rw [Nat.card_congr e.toEquiv, hB0card]
    norm_num
  have hu : (⟨x', hx'Q⟩ : Q) ^ 3 ^ k = 1 := by
    apply Subtype.ext
    exact hx'fin
  have hx'3 : (⟨x', hx'Q⟩ : Q) ^ 3 = 1 :=
    s16t3_pow_three_of_central Z hZcQ hZ3Q hperfQ h9Q hu
  have hx'3' : x' ^ 3 = 1 := by
    have h := congrArg Subtype.val hx'3
    simpa using h
  have hx3 : x ^ 3 = 1 := by
    have hconj : x = gE⁻¹ * x' * gE := by
      dsimp only [x']
      group
    rw [hconj, show gE⁻¹ * x' * gE = gE⁻¹ * x' * (gE⁻¹)⁻¹ by group,
      conj_pow, hx'3', mul_one, mul_inv_cancel]
  exact hx3

private theorem s16t3_pow_three_of_twoThreeCycles {E : Type*} [Group E] [Finite E] {n : ℕ}
    (hn : n = 6 ∨ n = 7) (π : E →* alternatingGroup (Fin n))
    (hπ : Function.Surjective π) (hZc : π.ker ≤ center E)
    (hZ3 : ∀ z ∈ π.ker, ∀ m : ℕ, z ^ 3 ^ m = 1 → z ^ 3 = 1)
    {x : E} {k : ℕ} (hx : x ^ 3 ^ k = 1)
    (hc : ((π x : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)).cycleType = {3, 3}) :
    x ^ 3 = 1 := by
  classical
  have hmem : 3 ∈ ((π x : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)).cycleType := by
    rw [hc]
    simp
  obtain ⟨c₁, c₂, hc_eq, hdc, hc1cyc, hc1card⟩ := Equiv.Perm.mem_cycleType_iff.1 hmem
  have hc1 : c₁.IsThreeCycle := by
    rw [Equiv.Perm.IsThreeCycle, hc1cyc.cycleType, hc1card]
  have hc2 : c₂.IsThreeCycle := by
    rw [Equiv.Perm.IsThreeCycle]
    have h := hdc.cycleType_mul
    rw [← hc_eq, hc, hc1.cycleType] at h
    have h' : {3} + c₂.cycleType = {3} + ({3} : Multiset ℕ) := by
      rw [← h]
      rfl
    exact add_left_cancel h'
  let C1 : alternatingGroup (Fin n) := ⟨c₁, hc1.mem_alternatingGroup⟩
  let C2 : alternatingGroup (Fin n) := ⟨c₂, hc2.mem_alternatingGroup⟩
  let D : Subgroup (alternatingGroup (Fin n)) := Subgroup.closure {C1, C2}
  let Dstar : Subgroup E := D.comap π
  have hxC : π x = C1 * C2 := by
    apply Subtype.ext
    simpa using hc_eq
  have hxD : x ∈ Dstar := by
    rw [Subgroup.mem_comap, hxC]
    exact Subgroup.mul_mem _
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  let p : Dstar →* alternatingGroup (Fin n) := π.comp Dstar.subtype
  let Z : Subgroup Dstar := p.ker
  have hp_range : p.range = D := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact Subgroup.map_comap_eq_self_of_surjective hπ D
  obtain ⟨a₀, ha₀⟩ := hπ C1
  obtain ⟨b₀, hb₀⟩ := hπ C2
  have ha₀D : a₀ ∈ Dstar := by
    rw [Subgroup.mem_comap, ha₀]
    exact Subgroup.subset_closure (by simp)
  have hb₀D : b₀ ∈ Dstar := by
    rw [Subgroup.mem_comap, hb₀]
    exact Subgroup.subset_closure (by simp)
  have haD : TauCeti.pPart 3 a₀ ∈ Dstar :=
    (Subgroup.zpowers_le.mpr ha₀D) (TauCeti.pPart_mem_zpowers 3 a₀)
  have hbD : TauCeti.pPart 3 b₀ ∈ Dstar :=
    (Subgroup.zpowers_le.mpr hb₀D) (TauCeti.pPart_mem_zpowers 3 b₀)
  let a : Dstar := ⟨TauCeti.pPart 3 a₀, haD⟩
  let b : Dstar := ⟨TauCeti.pPart 3 b₀, hbD⟩
  have hpa : p a = C1 := by
    change π (TauCeti.pPart 3 a₀) = C1
    rw [s16t3_map_pPart π a₀, ha₀]
    exact (TauCeti.eq_pPart (p := 3) Nat.prime_three (Commute.one_left C1) (one_mul C1)
      (by norm_num)
      (show orderOf C1 = 3 ^ 1 by
        rw [pow_one]
        exact (Subgroup.orderOf_mk c₁ hc1.mem_alternatingGroup).trans hc1.orderOf)).symm
  have hpb : p b = C2 := by
    change π (TauCeti.pPart 3 b₀) = C2
    rw [s16t3_map_pPart π b₀, hb₀]
    exact (TauCeti.eq_pPart (p := 3) Nat.prime_three (Commute.one_left C2) (one_mul C2)
      (by norm_num)
      (show orderOf C2 = 3 ^ 1 by
        rw [pow_one]
        exact (Subgroup.orderOf_mk c₂ hc2.mem_alternatingGroup).trans hc2.orderOf)).symm
  have ha3 : a ^ 3 = 1 := by
    have ha0 : orderOf a₀ ≠ 0 := by
      intro h
      have hd := orderOf_dvd_natCard a₀
      rw [h, zero_dvd_iff] at hd
      exact Nat.card_pos.ne' hd
    have hfin : (TauCeti.pPart 3 a₀) ^ 3 ^ (orderOf a₀).factorization 3 = 1 := by
      rw [show (3 : ℕ) ^ (orderOf a₀).factorization 3 = orderOf (TauCeti.pPart 3 a₀) by
        rw [TauCeti.orderOf_pPart (p := 3) Nat.prime_three ha0]]
      exact pow_orderOf_eq_one _
    have hpx : ((π (TauCeti.pPart 3 a₀) : alternatingGroup (Fin n)) :
        Equiv.Perm (Fin n)) = c₁ := by
      rw [show π (TauCeti.pPart 3 a₀) = C1 from hpa]
    have hc1' : Equiv.Perm.IsThreeCycle
        ((π (TauCeti.pPart 3 a₀) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) := by
      rw [hpx]
      exact hc1
    apply Subtype.ext
    exact s16t3_pow_three_of_threeCycle hn π hπ hZc hZ3 hfin hc1'
  have hb3 : b ^ 3 = 1 := by
    have hb0 : orderOf b₀ ≠ 0 := by
      intro h
      have hd := orderOf_dvd_natCard b₀
      rw [h, zero_dvd_iff] at hd
      exact Nat.card_pos.ne' hd
    have hfin : (TauCeti.pPart 3 b₀) ^ 3 ^ (orderOf b₀).factorization 3 = 1 := by
      rw [show (3 : ℕ) ^ (orderOf b₀).factorization 3 = orderOf (TauCeti.pPart 3 b₀) by
        rw [TauCeti.orderOf_pPart (p := 3) Nat.prime_three hb0]]
      exact pow_orderOf_eq_one _
    have hpx : ((π (TauCeti.pPart 3 b₀) : alternatingGroup (Fin n)) :
        Equiv.Perm (Fin n)) = c₂ := by
      rw [show π (TauCeti.pPart 3 b₀) = C2 from hpb]
    have hc2' : Equiv.Perm.IsThreeCycle
        ((π (TauCeti.pPart 3 b₀) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) := by
      rw [hpx]
      exact hc2
    apply Subtype.ext
    exact s16t3_pow_three_of_threeCycle hn π hπ hZc hZ3 hfin hc2'
  have hZcD : Z ≤ center Dstar := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    have hzker : z.1 ∈ π.ker := by
      change π z.1 = 1
      exact MonoidHom.mem_ker.mp hz
    exact Subgroup.mem_center_iff.mp (hZc hzker) w.1
  have hZ3D : ∀ z ∈ Z, ∀ m : ℕ, z ^ 3 ^ m = 1 → z ^ 3 = 1 := by
    intro z hz m hzm
    have hzker : z.1 ∈ π.ker := by
      change π z.1 = 1
      exact MonoidHom.mem_ker.mp hz
    have hzm1 : z.1 ^ 3 ^ m = 1 := by
      have h := congrArg Subtype.val hzm
      simpa using h
    exact Subtype.ext (by simpa using hZ3 z.1 hzker m hzm1)
  have hcommC : C1 * C2 = C2 * C1 := Subtype.ext hdc.commute.eq
  have hab : a * b * a⁻¹ * b⁻¹ ∈ Z := by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    simp only [map_mul, map_inv, hpa, hpb]
    rw [hcommC]
    group
  have hmapZ : Z.map p = ⊥ := (Subgroup.map_eq_bot_iff Z).mpr le_rfl
  have hgen : Subgroup.closure {a, b} ⊔ Z = ⊤ := by
    refine Subgroup.map_injective_of_ker_le p le_sup_right le_top ?_
    have himg : p '' ({a, b} : Set Dstar) = ({C1, C2} : Set (alternatingGroup (Fin n))) := by
      rw [Set.image_pair, hpa, hpb]
    rw [Subgroup.map_sup, MonoidHom.map_closure, himg, hmapZ, sup_bot_eq,
      Subgroup.map_top, hp_range]
  have hxq : (⟨x, hxD⟩ : Dstar) ^ 3 ^ k = 1 := by
    apply Subtype.ext
    exact hx
  have hx3' : (⟨x, hxD⟩ : Dstar) ^ 3 = 1 :=
    s16t3_pow_three_of_two_gen Z hZcD hZ3D ha3 hb3 hab hgen hxq
  have hx3 : x ^ 3 = 1 := by
    have h := congrArg Subtype.val hx3'
    simpa using h
  exact hx3

theorem s16t3_pow_three_of_alt_cover {Y : Type*} [Group Y] [Finite Y] {n : ℕ}
    (hn : n = 6 ∨ n = 7) (π : Y →* alternatingGroup (Fin n))
    (hπ : Function.Surjective π) (O : Subgroup Y) [O.Normal] (hO : IsPGroup 2 ↥O)
    (hOker : O ≤ π.ker) (hcent : π.ker.map (QuotientGroup.mk' O) ≤ center (Y ⧸ O))
    (hZ3 : ∀ x ∈ π.ker, ∀ m : ℕ, x ^ 3 ^ m = 1 → x ^ 3 = 1) {u : Y} {k : ℕ}
    (hu : u ^ 3 ^ k = 1)
    (hcyc : ((π u : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)).cycleType = 0 ∨
      ((π u : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)).cycleType = {3} ∨
      ((π u : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)).cycleType = {3, 3}) :
    u ^ 3 = 1 := by
  classical
  let π' : Y ⧸ O →* alternatingGroup (Fin n) := QuotientGroup.lift O π hOker
  have hπ' : Function.Surjective π' := by
    intro a
    obtain ⟨y, hy⟩ := hπ a
    exact ⟨QuotientGroup.mk' O y,
      by rw [show π' (QuotientGroup.mk' O y) = π y from
        QuotientGroup.lift_mk' O hOker y, hy]⟩
  have hZ_eq : π'.ker = π.ker.map (QuotientGroup.mk' O) :=
    QuotientGroup.ker_lift O π hOker
  have hZc : π'.ker ≤ center (Y ⧸ O) := by
    rw [hZ_eq]
    exact hcent
  have hZ3' : ∀ z ∈ π'.ker, ∀ m : ℕ, z ^ 3 ^ m = 1 → z ^ 3 = 1 := by
    intro z hz m hzm
    rw [hZ_eq] at hz
    obtain ⟨x, hxker, rfl⟩ := Subgroup.mem_map.mp hz
    have hx0 : orderOf x ≠ 0 := by
      intro h
      have hd := orderOf_dvd_natCard x
      rw [h, zero_dvd_iff] at hd
      exact Nat.card_pos.ne' hd
    have hpz : TauCeti.pPart 3 (QuotientGroup.mk' O x) = QuotientGroup.mk' O x := by
      obtain ⟨j, _, hj⟩ :=
        (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hzm)
      exact (TauCeti.eq_pPart (p := 3) Nat.prime_three
        (Commute.one_left (QuotientGroup.mk' O x)) (one_mul _) (by norm_num) hj).symm
    have hpk : TauCeti.pPart 3 x ∈ π.ker :=
      (Subgroup.zpowers_le.mpr hxker) (TauCeti.pPart_mem_zpowers 3 x)
    have hcube : (TauCeti.pPart 3 x) ^ 3 = 1 := by
      refine hZ3 _ hpk ((orderOf x).factorization 3) ?_
      rw [show (3 : ℕ) ^ (orderOf x).factorization 3 =
        orderOf (TauCeti.pPart 3 x) by rw [TauCeti.orderOf_pPart (p := 3) Nat.prime_three hx0]]
      exact pow_orderOf_eq_one _
    calc (QuotientGroup.mk' O x) ^ 3
        = (QuotientGroup.mk' O (TauCeti.pPart 3 x)) ^ 3 := by
          rw [s16t3_map_pPart (QuotientGroup.mk' O) x, hpz]
      _ = QuotientGroup.mk' O ((TauCeti.pPart 3 x) ^ 3) := by
          exact (map_pow (QuotientGroup.mk' O) (TauCeti.pPart 3 x) 3).symm
      _ = 1 := by rw [hcube, map_one]
  have huq : (QuotientGroup.mk' O u) ^ 3 ^ k = 1 := by
    rw [← map_pow, hu, map_one]
  have hcyc' : ((π' (QuotientGroup.mk' O u) : alternatingGroup (Fin n)) :
        Equiv.Perm (Fin n)).cycleType = 0 ∨
      ((π' (QuotientGroup.mk' O u) : alternatingGroup (Fin n)) :
        Equiv.Perm (Fin n)).cycleType = {3} ∨
      ((π' (QuotientGroup.mk' O u) : alternatingGroup (Fin n)) :
        Equiv.Perm (Fin n)).cycleType = {3, 3} := by
    rw [show π' (QuotientGroup.mk' O u) = π u from QuotientGroup.lift_mk' O hOker u]
    exact hcyc
  have hmain : (QuotientGroup.mk' O u) ^ 3 = 1 := by
    rcases hcyc' with h0 | h3 | h33
    · rw [Equiv.Perm.cycleType_eq_zero] at h0
      exact hZ3' _ (by rw [MonoidHom.mem_ker]; exact Subtype.ext h0) k huq
    · exact s16t3_pow_three_of_threeCycle hn π' hπ' hZc hZ3' huq h3
    · exact s16t3_pow_three_of_twoThreeCycles hn π' hπ' hZc hZ3' huq h33
  have huO : u ^ 3 ∈ O := (QuotientGroup.eq_one_iff (u ^ 3)).1 (by
    show (QuotientGroup.mk' O (u ^ 3)) = 1
    rw [map_pow, hmain])
  have hu3 : (u ^ 3) ^ 3 ^ k = 1 := by
    rw [← pow_mul, mul_comm (3 : ℕ) (3 ^ k), pow_mul, hu, one_pow]
  exact s16t3_eq_one_of_pElement_of_two hO huO hu3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
