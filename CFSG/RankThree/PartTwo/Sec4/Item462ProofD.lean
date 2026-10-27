module

public import CFSG.RankThree.PartTwo.Sec4.Item462ProofTools
public import CFSG.RankThree.PartTwo.Sec4.Statements423
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_conj_eq_of_card_three [Finite G] {D : Subgroup G} (hD : Nat.card D = 3) {h : G}
    (hhD : h ∈ Subgroup.normalizer (D : Set G)) {d : G} (hd : d ∈ D) :
    h * (h * d * h⁻¹) * h⁻¹ = d := by
  by_cases hd1 : d = 1
  · rw [hd1]
    group
  have hD3 : ∀ x ∈ D, x ^ 3 = 1 := fun x hx => by
    have h1 := orderOf_dvd_natCard (⟨x, hx⟩ : D)
    rw [hD, Subgroup.orderOf_mk] at h1
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  have hdo : orderOf d = 3 := orderOf_eq_prime (hD3 d hd) hd1
  have hDz : D = Subgroup.zpowers d :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hd)
      (by rw [hD, Nat.card_zpowers, hdo])).symm
  have hhd : h * d * h⁻¹ ∈ Subgroup.zpowers d :=
    hDz ▸ (Subgroup.mem_normalizer_iff.mp hhD d).mp hd
  have hhd1 : h * d * h⁻¹ ≠ 1 := by
    intro h1
    apply hd1
    calc d = h⁻¹ * (h * d * h⁻¹) * h := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hhd
  have hd3' : d ^ (3 : ℤ) = 1 := by exact_mod_cast hD3 d hd
  rw [zpow_eq_zpow_emod k hd3'] at hk
  have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk3 with h0 | h0 | h0 <;> rw [h0] at hk
  · exact absurd (by rw [← hk, zpow_zero]) hhd1
  · rw [zpow_one] at hk
    rw [← hk, ← hk]
  · have hinv : h * d * h⁻¹ = d⁻¹ := by
      rw [← hk, show (2 : ℤ) = 3 + (-1) by norm_num, zpow_add, hd3', one_mul, zpow_neg_one]
    rw [hinv]
    calc h * d⁻¹ * h⁻¹ = (h * d * h⁻¹)⁻¹ := by group
      _ = d := by rw [hinv, inv_inv]

omit [Finite G] in
theorem normalizerMonoidHom_pow_apply_coe {A : Subgroup G} {h : G}
    (hN : h ∈ Subgroup.normalizer (A : Set G)) (n : ℕ) (x : A) :
    (((A.normalizerMonoidHom ⟨h, hN⟩ ^ n) x : A) : G) = h ^ n * x * (h ^ n)⁻¹ := by
  rw [← map_pow, normalizerMonoidHom_apply_coe]
  rfl

theorem sq_eq_one_of_mem_autIn {A D L : Subgroup G} {a : G}
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) (h27 : Nat.card A = 27) (haA : a ∈ A)
    (haZ : a ∈ Subgroup.center G) (ha1 : a ≠ 1) (hDA : D ≤ A) (hD3 : Nat.card D = 3)
    (haD : a ∉ D) (hND : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (D : Set G))
    {σ : MulAut A} (hσ : σ ∈ autIn L A) (hσ4 : σ ^ 4 = 1) : σ ^ 2 = 1 := by
  obtain ⟨h, hN, -, rfl⟩ := mem_autIn_iff.mp hσ
  have hhD : h ∈ Subgroup.normalizer (D : Set G) := hND hN
  have ha3 : orderOf a = 3 := orderOf_eq_prime (hAe.2 a haA) ha1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.1.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hZn : (Subgroup.zpowers a).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr haZ)
  set M := D ⊔ Subgroup.zpowers a with hM
  have hMA : M ≤ A := sup_le hDA (Subgroup.zpowers_le.mpr haA)
  have hMc : Nat.card M = 9 := by
    rw [hM, card_sup_zpowers_of_not_mem haZ ha3 haD, hD3]
  have hfixM : ∀ m ∈ M, h * (h * m * h⁻¹) * h⁻¹ = m := by
    intro m hm
    obtain ⟨d, hd, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hm
    have hzc := Subgroup.mem_center_iff.mp ((Subgroup.zpowers_le.mpr haZ) hz)
    have hz' : ∀ g : G, g * z * g⁻¹ = z := fun g => by rw [hzc g, mul_inv_cancel_right]
    have h1 : h * (d * z) * h⁻¹ = (h * d * h⁻¹) * z := by
      rw [show h * (d * z) * h⁻¹ = (h * d * h⁻¹) * (h * z * h⁻¹) by group, hz']
    rw [h1, show h * (h * d * h⁻¹ * z) * h⁻¹ = h * (h * d * h⁻¹) * h⁻¹ * (h * z * h⁻¹) by group,
      hz', conj_conj_eq_of_card_three hD3 hhD hd]
  have hhM : ∀ m ∈ M, h * m * h⁻¹ ∈ M := by
    intro m hm
    obtain ⟨d, hd, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hm
    have hzc := Subgroup.mem_center_iff.mp ((Subgroup.zpowers_le.mpr haZ) hz)
    rw [show h * (d * z) * h⁻¹ = (h * d * h⁻¹) * (h * z * h⁻¹) by group, hzc h,
      mul_inv_cancel_right]
    exact M.mul_mem (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hhD d).mp hd))
      (Subgroup.mem_sup_right hz)
  have hhA : ∀ x ∈ A, h * x * h⁻¹ ∈ A := fun x hx => (Subgroup.mem_normalizer_iff.mp hN x).mp hx
  have hMx : ∀ x ∈ A, ∃ m ∈ M, h * (h * x * h⁻¹) * h⁻¹ = m * x := by
    intro x hx
    by_cases hxM : x ∈ M
    · exact ⟨1, M.one_mem, by rw [hfixM x hxM, one_mul]⟩
    have hx3 : x ^ 3 = 1 := hAe.2 x hx
    have hxC : x ∈ Subgroup.centralizer (M : Set G) := Subgroup.mem_centralizer_iff.mpr
      fun m hm => hcomm m (hMA hm) x hx
    have hAx : M ⊔ Subgroup.zpowers x = A := by
      refine Subgroup.eq_of_le_of_card_ge (sup_le hMA (Subgroup.zpowers_le.mpr hx)) ?_
      have hN' : Subgroup.zpowers x ≤ Subgroup.normalizer (M : Set G) :=
        (Subgroup.zpowers_le.mpr hxC).trans (Subgroup.centralizer_le_normalizer _)
      rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer M _ hN'
        (disjoint_zpowers_of_pow_three hx3 hxM), hMc, Nat.card_zpowers,
        orderOf_eq_prime hx3 (fun h1 => hxM (h1 ▸ M.one_mem)), h27]
    have hxA : h * x * h⁻¹ ∈ M ⊔ Subgroup.zpowers x := hAx ▸ hhA x hx
    have hMN : M ≤ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) :=
      (Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr hxC)).trans
        (Subgroup.centralizer_le_normalizer _)
    have hset := Subgroup.coe_mul_of_left_le_normalizer_right M (Subgroup.zpowers x) hMN
    have hxA' : h * x * h⁻¹ ∈ (M : Set G) * (Subgroup.zpowers x : Set G) := by
      rw [← hset]
      exact hxA
    obtain ⟨m, hm, y, hy, hmy⟩ := hxA'
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    change m * x ^ j = h * x * h⁻¹ at hmy
    have hx3' : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx3
    rw [zpow_eq_zpow_emod j hx3'] at hmy
    have hj3 : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
    have hhm := hhM m hm
    rcases hj3 with h0 | h0 | h0 <;> rw [h0] at hmy
    · exfalso
      apply hxM
      rw [zpow_zero, mul_one] at hmy
      have h1 : x = h⁻¹ * (h * x * h⁻¹) * h := by group
      rw [h1, ← hmy]
      have := hfixM m hm
      have h2 : h⁻¹ * m * h = h * m * h⁻¹ := by
        calc h⁻¹ * m * h = h⁻¹ * (h * (h * m * h⁻¹) * h⁻¹) * h := by rw [this]
          _ = h * m * h⁻¹ := by group
      rw [h2]
      exact hhm
    · rw [zpow_one] at hmy
      refine ⟨(h * m * h⁻¹) * m, M.mul_mem hhm hm, ?_⟩
      calc h * (h * x * h⁻¹) * h⁻¹ = h * (m * x) * h⁻¹ := by rw [hmy]
        _ = (h * m * h⁻¹) * (h * x * h⁻¹) := by group
        _ = (h * m * h⁻¹) * (m * x) := by rw [hmy]
        _ = (h * m * h⁻¹) * m * x := by group
    · have hx2 : x ^ (2 : ℤ) = x⁻¹ := by
        rw [show (2 : ℤ) = 3 + (-1) by norm_num, zpow_add, hx3', one_mul, zpow_neg_one]
      rw [hx2] at hmy
      refine ⟨(h * m * h⁻¹) * m⁻¹, M.mul_mem hhm (M.inv_mem hm), ?_⟩
      calc h * (h * x * h⁻¹) * h⁻¹ = h * (m * x⁻¹) * h⁻¹ := by rw [hmy]
        _ = (h * m * h⁻¹) * (h * x * h⁻¹)⁻¹ := by group
        _ = (h * m * h⁻¹) * (m * x⁻¹)⁻¹ := by rw [hmy]
        _ = (h * m * h⁻¹) * (x * m⁻¹) := by group
        _ = (h * m * h⁻¹) * (m⁻¹ * x) := by rw [hcomm x hx m⁻¹ (A.inv_mem (hMA hm))]
        _ = (h * m * h⁻¹) * m⁻¹ * x := by group
  have hpow : ∀ (n : ℕ) (y : G), h ^ (n + 1) * y * (h ^ (n + 1))⁻¹ =
      h * (h ^ n * y * (h ^ n)⁻¹) * h⁻¹ := fun n y => by
    rw [pow_succ', mul_inv_rev]
    group
  have h4 : ∀ x ∈ A, h * (h * (h * (h * x * h⁻¹) * h⁻¹) * h⁻¹) * h⁻¹ = x := by
    intro x hx
    have := congrArg (fun τ : MulAut A => ((τ ⟨x, hx⟩ : A) : G)) hσ4
    simp only [MulAut.one_apply] at this
    rw [normalizerMonoidHom_pow_apply_coe, hpow 3, hpow 2, hpow 1, hpow 0, pow_zero, one_mul,
      inv_one, mul_one] at this
    exact this
  ext x
  rw [normalizerMonoidHom_pow_apply_coe, MulAut.one_apply, hpow 1, hpow 0, pow_zero, one_mul,
    inv_one, mul_one]
  obtain ⟨m, hm, hmx⟩ := hMx x x.2
  have hfix := hfixM m hm
  have h4' : h * (h * (h * (h * (x : G) * h⁻¹) * h⁻¹) * h⁻¹) * h⁻¹ = m * m * x := by
    calc h * (h * (h * (h * (x : G) * h⁻¹) * h⁻¹) * h⁻¹) * h⁻¹ =
          h * (h * (m * x) * h⁻¹) * h⁻¹ := by rw [hmx]
      _ = (h * (h * m * h⁻¹) * h⁻¹) * (h * (h * x * h⁻¹) * h⁻¹) := by group
      _ = m * (m * x) := by rw [hfix, hmx]
      _ = m * m * x := by group
  rw [h4 x x.2] at h4'
  have hm2 : m * m = 1 := by
    have h5 : m * m * x * (x : G)⁻¹ = x * (x : G)⁻¹ := by rw [← h4']
    rwa [mul_inv_cancel_right, mul_inv_cancel] at h5
  have hm3 : m ^ 3 = 1 := hAe.2 m (hMA hm)
  have hm1 : m = 1 := by
    calc m = m ^ 3 * (m * m)⁻¹ := by group
      _ = 1 := by rw [hm3, hm2]; group
  rw [hmx, hm1, one_mul]

theorem nonempty_mulEquiv_of_le_prod {X : Type*} [Group X] {H K : Subgroup X} {C S : Type*}
    [CommGroup C] [Group S] (hS : IsSimpleGroup S) (hKH : K ≤ H)
    (hKn : H ≤ Subgroup.normalizer (K : Set X)) (hKp : Group.IsPerfect K) (hK1 : K ≠ ⊥)
    (f : H ≃* C × S) : Nonempty (K ≃* S) := by
  classical
  set ι := Subgroup.inclusion hKH with hι
  set ψ : K →* S := (MonoidHom.snd C S).comp (f.toMonoidHom.comp ι) with hψ
  have hfst : ∀ k : K, (f (ι k)).1 = 1 := by
    intro k
    have hker : commutator K ≤ ((MonoidHom.fst C S).comp (f.toMonoidHom.comp ι)).ker :=
      Abelianization.commutator_subset_ker _
    rw [@Group.IsPerfect.commutator_eq_top _ _ hKp] at hker
    exact hker (Subgroup.mem_top k)
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro k hk
    rw [MonoidHom.mem_ker] at hk
    have h1 : f (ι k) = 1 := Prod.ext (hfst k) hk
    have h2 : ι k = 1 := f.injective (h1.trans (map_one f).symm)
    exact Subgroup.mem_bot.mpr (Subgroup.inclusion_injective hKH (h2.trans (map_one ι).symm))
  have hsurj : Function.Surjective ψ := by
    have hnorm : ψ.range.Normal := by
      refine ⟨fun s hs t => ?_⟩
      obtain ⟨k, rfl⟩ := hs
      set h := f.symm (1, t) with hh
      have hk' : (h : X) * k * (h : X)⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hKn h.2) k).mp k.2
      refine ⟨⟨_, hk'⟩, ?_⟩
      have hιk : ι ⟨_, hk'⟩ = h * ι k * h⁻¹ := Subtype.ext rfl
      have hfh : f h = (1, t) := by rw [hh, MulEquiv.apply_symm_apply]
      change (f (ι ⟨_, hk'⟩)).2 = t * (f (ι k)).2 * t⁻¹
      rw [hιk, map_mul, map_mul, map_inv, hfh]
      rfl
    rcases hS.eq_bot_or_eq_top_of_normal ψ.range with h | h
    · exfalso
      apply hK1
      rw [eq_bot_iff]
      intro x hx
      have h1 : ψ ⟨x, hx⟩ = 1 := by
        have : ψ ⟨x, hx⟩ ∈ ψ.range := ⟨_, rfl⟩
        rwa [h, Subgroup.mem_bot] at this
      have h2 : (⟨x, hx⟩ : K) = 1 := hinj (h1.trans (map_one ψ).symm)
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val h2)
    · exact MonoidHom.range_eq_top.mp h
  exact ⟨MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩⟩

theorem nonempty_mulEquiv_of_thetaImage {A L : Subgroup G} (hL : L ∈ thetaComponents 3 G)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) {S : Type*} [Group S] (hS : IsSimpleGroup S)
    (e : thetaImage (L ⊔ A) ≃* Multiplicative (ZMod 3) × S) :
    Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* S) := by
  obtain ⟨-, hK, ⟨η, -⟩, -⟩ := theta_component_quotient_structure Nat.prime_three hL
  obtain ⟨hKp, -, x, y, hxy⟩ := hK.1
  have hKH : L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) ≤ thetaImage (L ⊔ A) :=
    Subgroup.map_mono le_sup_left
  have hKn : thetaImage (L ⊔ A) ≤ Subgroup.normalizer
      ((L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) : Subgroup _) : Set _) :=
    (Subgroup.map_mono (sup_le Subgroup.le_normalizer hAL)).trans (Subgroup.le_normalizer_map _)
  have hK1 : L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) ≠ ⊥ := by
    intro h
    apply hxy
    have hsub : ∀ k : L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)), k = 1 := fun k =>
      Subtype.ext (Subgroup.mem_bot.mp (h.le k.2))
    obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
    rw [hsub x', hsub y']
  obtain ⟨e'⟩ := nonempty_mulEquiv_of_le_prod hS hKH hKn hKp hK1 e
  exact ⟨η.trans e'⟩

end CFSG.RankThree.PartTwo.Sec4.Item462Proof
