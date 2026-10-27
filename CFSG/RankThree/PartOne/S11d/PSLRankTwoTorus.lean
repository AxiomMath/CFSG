module

public import CFSG.RankThree.PartOne.S11d.PSLRankTwoLow
public import CFSG.RankThree.PartOne.S11c.Sec66TorusPSL
public import CFSG.RankThree.PartOne.S11d.PSLRank

public section

namespace CFSG.RankThree.PartOne

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag Subgroup CFSG Matrix

theorem isElementaryAbelian_map_of_comm {G H : Type*} [CommGroup G] [Group H] (f : G →* H)
    {p : ℕ} (S : Subgroup G) (hS : ∀ x ∈ S, x ^ p = 1) :
    CFSG.IsElementaryAbelian p (S.map f) := by
  refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
  · intro a b
    obtain ⟨x, -, hxa⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨y, -, hyb⟩ := Subgroup.mem_map.mp b.2
    apply Subtype.ext
    show (a : H) * b = b * a
    rw [← hxa, ← hyb, ← map_mul, ← map_mul, mul_comm]
  · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => ?_
    obtain ⟨x, hx, hg⟩ := Subgroup.mem_map.mp g.2
    apply Subtype.ext
    show (g : H) ^ p = 1
    rw [← hg, ← map_pow, hS x hx, map_one]

section Root

variable {n : ℕ} {k : Type} [Field k]

@[expose] def rootElt (hn : 3 ≤ n) (t : k) : SpecialLinearGroup (Fin n) k :=
  ⟨transvection (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ t,
    det_transvection_of_ne _ _ (by simp [Fin.ext_iff]) t⟩

theorem coe_rootElt (hn : 3 ≤ n) (t : k) :
    ((rootElt hn t : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      transvection (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ t := rfl

theorem rootElt_zero (hn : 3 ≤ n) : rootElt hn (0 : k) = 1 :=
  Subtype.ext (transvection_zero _ _)

theorem rootElt_add (hn : 3 ≤ n) (s t : k) :
    rootElt hn (s + t) = rootElt hn s * rootElt hn t :=
  Subtype.ext (by
    rw [coe_rootElt, Matrix.SpecialLinearGroup.coe_mul, coe_rootElt, coe_rootElt,
      transvection_mul_transvection_same _ _ (by simp [Fin.ext_iff])])

@[expose] def rootEltHom (hn : 3 ≤ n) (k : Type) [Field k] :
    Multiplicative k →* SpecialLinearGroup (Fin n) k where
  toFun t := rootElt hn (Multiplicative.toAdd t)
  map_one' := rootElt_zero hn
  map_mul' _ _ := rootElt_add hn _ _

theorem rootElt_ne_one (hn : 3 ≤ n) {t : k} (ht : t ≠ 0) : rootElt hn t ≠ 1 := by
  intro h
  have h1 := congrArg (fun A : SpecialLinearGroup (Fin n) k =>
    (A : Matrix (Fin n) (Fin n) k) ⟨0, by omega⟩ ⟨1, by omega⟩) h
  simp [coe_rootElt, transvection, Fin.ext_iff] at h1
  exact ht h1

theorem rootElt_mul_self [CharP k 2] (hn : 3 ≤ n) (t : k) :
    rootElt hn t * rootElt hn t = 1 := by
  rw [← rootElt_add, CharTwo.add_self_eq_zero, rootElt_zero]

theorem rootEltHom_range_ne_bot (hn : 3 ≤ n) : (rootEltHom hn k).range ≠ ⊥ := by
  intro hbot
  have hmem : rootElt hn (1 : k) ∈ (rootEltHom hn k).range := ⟨Multiplicative.ofAdd 1, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact rootElt_ne_one hn one_ne_zero hmem

theorem isPGroup_rootEltHom_range [CharP k 2] (hn : 3 ≤ n) : IsPGroup 2 (rootEltHom hn k).range :=
  fun x => by
    obtain ⟨t, ht⟩ := x.2
    refine ⟨1, Subtype.ext ?_⟩
    show (x : SpecialLinearGroup (Fin n) k) ^ (2 ^ 1) = 1
    rw [← ht, pow_one, pow_two]
    exact rootElt_mul_self hn _

theorem torusTwoMat_apply_zero (hn : 3 ≤ n) (ab : kˣ × kˣ) :
    torusTwoMat hn ab ⟨0, by omega⟩ ⟨0, by omega⟩ = ab.1 := by
  simp [torusTwoMat]

theorem torusTwoMat_apply_one (hn : 3 ≤ n) (ab : kˣ × kˣ) :
    torusTwoMat hn ab ⟨1, by omega⟩ ⟨1, by omega⟩ = ab.2 * ab.1⁻¹ := by
  simp [torusTwoMat]

theorem torusTwoMat_apply_two (hn : 3 ≤ n) (ab : kˣ × kˣ) :
    torusTwoMat hn ab ⟨2, by omega⟩ ⟨2, by omega⟩ = ab.2⁻¹ := by
  simp [torusTwoMat]

theorem torusTwoHom_injective (hn : 3 ≤ n) : Function.Injective (torusTwoHom hn k) := by
  intro ab ab' h
  have hm : torusTwoMat hn ab = torusTwoMat hn ab' := congrArg Subtype.val h
  have h0 := congrFun (congrFun hm ⟨0, by omega⟩) ⟨0, by omega⟩
  have h2 := congrFun (congrFun hm ⟨2, by omega⟩) ⟨2, by omega⟩
  rw [torusTwoMat_apply_zero, torusTwoMat_apply_zero] at h0
  rw [torusTwoMat_apply_two, torusTwoMat_apply_two] at h2
  exact Prod.ext (Units.ext h0) (Units.ext (by simpa using h2))

theorem torusTwoMat_inv (hn : 3 ≤ n) (ab : kˣ × kˣ) :
    torusTwoMat hn ab⁻¹ = diagonal (fun i : Fin n => (torusTwoMat hn ab i i)⁻¹) := by
  rw [torusTwoMat, torusTwoMat]
  congr 1
  funext i
  simp only [Prod.fst_inv, Prod.snd_inv, Matrix.diagonal_apply_eq]
  rw [← Units.val_inv_eq_inv_val]
  congr 1
  by_cases h0 : i = ⟨0, by omega⟩ <;> by_cases h1 : i = ⟨1, by omega⟩ <;>
    by_cases h2 : i = ⟨2, by omega⟩ <;> simp [h0, h1, h2, mul_comm]

theorem torusTwo_conj_rootElt (hn : 3 ≤ n) (ab : kˣ × kˣ) (t : k) :
    torusTwoHom hn k ab * rootElt hn t * (torusTwoHom hn k ab)⁻¹ =
      rootElt hn ((ab.1 : k) * t * ((ab.2 * ab.1⁻¹ : kˣ) : k)⁻¹) := by
  rw [← map_inv]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_rootElt,
    coe_rootElt]
  change torusTwoMat hn ab * transvection (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ t *
    torusTwoMat hn ab⁻¹ = _
  rw [torusTwoMat_inv]
  have key := CFSG.RankThree.PartOne.Sec66T.diagonal_mul_transvection_mul_inv
    (fun i : Fin n => torusTwoMat hn ab i i) (fun i => by
      simp [torusTwoMat]) (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ (by simp [Fin.ext_iff]) t
  have hd : torusTwoMat hn ab = diagonal (fun i : Fin n => torusTwoMat hn ab i i) := by
    rw [torusTwoMat]
    simp
  rw [← hd, torusTwoMat_apply_zero, torusTwoMat_apply_one] at key
  exact key

end Root

section Main

variable {n : ℕ} {k : Type} [Field k] [Finite k] [CharP k 2]

theorem zpow_pow_eq_one {G : Type*} [Group G] {g : G} {p : ℕ} (hg : g ^ p = 1) (i : ℤ) :
    (g ^ i) ^ p = 1 := by
  rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hg,
    _root_.one_zpow]

theorem exists_rank_two_unip_psl_torus [NeZero n] (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime)
    (hp3 : p ≠ 3) (hpK : p ∣ Nat.card kˣ) :
    ∃ R U : Subgroup (projectiveSL n k), CFSG.IsElementaryAbelian p R ∧ Nat.card R = p ^ 2 ∧
      U ≠ ⊥ ∧ IsPGroup 2 U ∧ R ≤ Subgroup.normalizer (U : Set (projectiveSL n k)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := kˣ) p hpK
  have hωp : ω ^ p = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  let S : Subgroup (kˣ × kˣ) := (zpowers ω).prod (zpowers ω)
  have hS : ∀ x ∈ S, x ^ p = 1 := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact Prod.ext (zpow_pow_eq_one hωp i) (zpow_pow_eq_one hωp j)
  let R₁ : Subgroup (SpecialLinearGroup (Fin n) k) := S.map (torusTwoHom hn k)
  let U₁ : Subgroup (SpecialLinearGroup (Fin n) k) := (rootEltHom hn k).range
  have hR₁e : CFSG.IsElementaryAbelian p R₁ := isElementaryAbelian_map_of_comm _ S hS
  have hR₁c : Nat.card R₁ = p ^ 2 := by
    have hc : Nat.card S = p ^ 2 := by
      rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, Nat.card_zpowers, hω]
      ring
    rw [Subgroup.card_map_of_injective (torusTwoHom_injective hn), hc]
  have hN : R₁ ≤ Subgroup.normalizer (U₁ : Set (SpecialLinearGroup (Fin n) k)) := by
    have key : ∀ (s : kˣ × kˣ) (u : SpecialLinearGroup (Fin n) k), u ∈ U₁ →
        torusTwoHom hn k s * u * (torusTwoHom hn k s)⁻¹ ∈ U₁ := by
      rintro ⟨a, b⟩ _ ⟨t, rfl⟩
      show torusTwoHom hn k (a, b) * rootElt hn (Multiplicative.toAdd t) *
        (torusTwoHom hn k (a, b))⁻¹ ∈ _
      rw [torusTwo_conj_rootElt]
      exact ⟨Multiplicative.ofAdd _, rfl⟩
    rintro _ ⟨s, -, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro u
    refine ⟨key s u, fun hu => ?_⟩
    have := key s⁻¹ _ hu
    rw [map_inv, inv_inv] at this
    have h2 : (torusTwoHom hn k s)⁻¹ * (torusTwoHom hn k s * u * (torusTwoHom hn k s)⁻¹) *
        torusTwoHom hn k s = u := by group
    rwa [h2] at this
  have hRinj : ∀ x ∈ R₁, ∀ y ∈ R₁, proj n k x = proj n k y → x = y := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩ h
    have hsc := proj_eq_proj_iff.mp h
    have hmul : (torusTwoHom hn k s)⁻¹ * torusTwoHom hn k s' =
        torusTwo hn (s⁻¹ * s') := by
      rw [← map_inv, ← map_mul]
      rfl
    rw [hmul] at hsc
    have hss' : s⁻¹ * s' ∈ S := S.mul_mem (S.inv_mem hs) hs'
    obtain ⟨h3, hb⟩ := torusTwo_scalar hn (a := (s⁻¹ * s').1) (b := (s⁻¹ * s').2) hsc
    have hap : (s⁻¹ * s').1 ^ p = 1 := (Prod.ext_iff.mp (hS _ hss')).1
    have hord : orderOf (s⁻¹ * s').1 ∣ Nat.gcd 3 p :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one hap)
    have hcop : Nat.gcd 3 p = 1 := by
      rw [Nat.gcd_comm]
      exact (Nat.coprime_primes hp Nat.prime_three).mpr hp3
    rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at hord
    have h1 : s⁻¹ * s' = 1 := Prod.ext hord (by rw [hb, hord]; simp)
    rw [inv_mul_eq_one.mp h1]
  have hUinj : ∀ x ∈ U₁, proj n k x = 1 → x = 1 := by
    rintro _ ⟨t, rfl⟩ h
    obtain ⟨c, -, hmat⟩ := mem_scalars.mp (proj_eq_one_iff.mp h)
    have hmat' : ((rootElt hn (Multiplicative.toAdd t) : SpecialLinearGroup (Fin n) k) :
        Matrix (Fin n) (Fin n) k) = scalar (Fin n) (c : k) := hmat
    have h1 := congrFun (congrFun hmat' ⟨0, by omega⟩) ⟨1, by omega⟩
    have ht : Multiplicative.toAdd t = 0 := by
      simpa [coe_rootElt, transvection, Matrix.scalar_apply, Fin.ext_iff] using h1
    show rootElt hn (Multiplicative.toAdd t) = 1
    rw [ht, rootElt_zero]
  obtain ⟨h1, h2, h3, h4, h5⟩ := rankTwoCfg_map (proj n k) R₁ U₁ hRinj hUinj hR₁e hR₁c
    (rootEltHom_range_ne_bot hn) (isPGroup_rootEltHom_range hn) hN
  exact ⟨_, _, h1, h2, h3, h4, h5⟩

end Main

end CFSG.RankThree.PartOne
