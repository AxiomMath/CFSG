module

import CFSG.LocalAnalysis.StandardType.KGLangTorusNorm
import CFSG.LocalAnalysis.StandardType.KGLangH90
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.CharP
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.StandardType

theorem kgLangC_mem_of_pow_mem {p e : ℕ} (hp : p.Prime) (hpe : ¬ p ∣ e) {G : Type*} [Group G]
    (H : Subgroup G) {u : G} (hu : u ^ e ∈ H) {k : ℕ} (hk : u ^ p ^ k = 1) : u ∈ H := by
  rcases k with _ | k
  · rw [pow_zero, pow_one] at hk
    rw [hk]
    exact H.one_mem
  · have hcop : Nat.Coprime e (p ^ (k + 1)) :=
      (Nat.Coprime.pow_right (k + 1) (hp.coprime_iff_not_dvd.mpr hpe).symm)
    have h1 : 1 < p ^ (k + 1) :=
      one_lt_pow₀ (Nat.Prime.one_lt hp) (Nat.succ_ne_zero k)
    obtain ⟨b, -, hb⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
    have hmod : e * b ≡ 1 [MOD p ^ (k + 1)] := by
      rw [Nat.ModEq, hb]
      exact (Nat.mod_eq_of_lt h1).symm
    have hpow : u ^ (e * b) = u := by
      simpa using pow_eq_pow_of_modEq hmod hk
    have hmem : (u ^ e) ^ b ∈ H := H.pow_mem hu b
    rw [← pow_mul] at hmem
    rwa [← hpow]

private theorem kgLangCSpanAux_adjoin_comm_reduced {ι : Type} [Fintype ι] [DecidableEq ι]
    {𝕂 : Type} [Field 𝕂] [Finite 𝕂] [CharP 𝕂 2]
    (P : Subgroup (GL ι 𝕂)) (hab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hodd : Odd (Nat.card P)) :
    (∀ x ∈ Algebra.adjoin 𝕂 ((fun g : GL ι 𝕂 => (g : Matrix ι ι 𝕂)) '' (P : Set _)),
      ∀ y ∈ Algebra.adjoin 𝕂 ((fun g : GL ι 𝕂 => (g : Matrix ι ι 𝕂)) '' (P : Set _)),
        x * y = y * x) ∧
    ∀ x ∈ Algebra.adjoin 𝕂 ((fun g : GL ι 𝕂 => (g : Matrix ι ι 𝕂)) '' (P : Set _)),
      IsNilpotent x → x = 0 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · haveI := hι
    exact ⟨fun x _ y _ => Subsingleton.elim _ _, fun x _ _ => Subsingleton.elim _ _⟩
  · set s : Set (Matrix ι ι 𝕂) :=
      (fun g : GL ι 𝕂 => (g : Matrix ι ι 𝕂)) '' (P : Set _) with hs
    let S : Subalgebra 𝕂 (Matrix ι ι 𝕂) := Algebra.adjoin 𝕂 s
    have hs_pair : s.Pairwise Commute := by
      intro a ha b hb _
      obtain ⟨g, hg, rfl⟩ := ha
      obtain ⟨h, hh, rfl⟩ := hb
      show Commute (↑g : Matrix ι ι 𝕂) (↑h : Matrix ι ι 𝕂)
      rw [commute_iff_eq, ← Matrix.GeneralLinearGroup.coe_mul, ← Matrix.GeneralLinearGroup.coe_mul,
        hab g hg h hh]
    have hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
      haveI : IsMulCommutative S := Algebra.isMulCommutative_adjoin 𝕂 hs_pair
      intro x hx y hy
      have hcommS : ∀ a b : S, a * b = b * a :=
        isMulCommutative_iff.mp (inferInstance : IsMulCommutative S)
      simpa using congrArg Subtype.val (hcommS ⟨x, hx⟩ ⟨y, hy⟩)
    refine ⟨hcomm, ?_⟩
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Algebra (ZMod 2) 𝕂 := ZMod.algebra 𝕂 2
    letI : Fintype 𝕂 := Fintype.ofFinite 𝕂
    let f := Module.finrank (ZMod 2) 𝕂
    let m := Nat.card P
    let k := f * Nat.totient m
    have hcard : 2 ^ f = Nat.card 𝕂 := FiniteField.pow_finrank_eq_natCard 2 𝕂
    have hm_pos : 0 < m := by
      haveI : Nonempty P := ⟨⟨1, one_mem P⟩⟩
      change 0 < Nat.card P
      exact Nat.card_pos
    have hf_pos : 0 < f := by
      change 0 < Module.finrank (ZMod 2) 𝕂
      exact Module.finrank_pos
    have hk_pos : 0 < k := by
      change 0 < f * Nat.totient m
      exact Nat.mul_pos hf_pos (Nat.totient_pos.mpr hm_pos)
    have hcop : Nat.Coprime 2 m := hodd.coprime_two_left
    have hk_mod : 2 ^ k ≡ 1 [MOD m] := by
      have h1 : (2 ^ Nat.totient m) ^ f ≡ 1 ^ f [MOD m] :=
        (Nat.ModEq.pow_totient hcop).pow f
      rw [one_pow] at h1
      have h2 : (2 ^ Nat.totient m) ^ f = 2 ^ k := by
        change (2 ^ Nat.totient m) ^ f = 2 ^ (f * Nat.totient m)
        rw [Nat.mul_comm, pow_mul]
      rwa [← h2]
    have hfixK : ∀ c : 𝕂, c ^ (2 ^ k) = c := by
      intro c
      have hq : 2 ^ k = (Nat.card 𝕂) ^ Nat.totient m := by
        change 2 ^ (f * Nat.totient m) = (Nat.card 𝕂) ^ Nat.totient m
        rw [← hcard, pow_mul]
      rw [hq, ← Fintype.card_eq_nat_card]
      exact FiniteField.pow_card_pow (Nat.totient m) c
    have hfixS : ∀ x ∈ S, x ^ (2 ^ k) = x := by
      intro x hxS
      refine Algebra.adjoin_induction (p := fun x _ => x ^ (2 ^ k) = x) ?_ ?_ ?_ ?_ hxS
      · intro y hy
        obtain ⟨g, hg, rfl⟩ := hy
        have hgm : (↑g : Matrix ι ι 𝕂) ^ m = 1 := by
          have h : g ^ m = 1 := by
            have h' := congrArg Subtype.val (pow_card_eq_one' (G := P) (x := ⟨g, hg⟩))
            simp only [Subgroup.coe_pow] at h'
            simpa [m] using h'
          have h2 := congrArg (fun u : GL ι 𝕂 => (u : Matrix ι ι 𝕂)) h
          simpa using h2
        have h := pow_eq_pow_of_modEq (x := (↑g : Matrix ι ι 𝕂)) hk_mod hgm
        rwa [pow_one] at h
      · intro r
        have hr : algebraMap 𝕂 (Matrix ι ι 𝕂) r = Matrix.scalar ι r := by
          simp [Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
        rw [hr, ← map_pow, hfixK r]
      · intro a b ha hb ha' hb'
        rw [add_pow_char_pow_of_commute (p := 2) (n := k) (hcomm a ha b hb), ha', hb']
      · intro a b ha hb ha' hb'
        rw [Commute.mul_pow (hcomm a ha b hb) (2 ^ k), ha', hb']
    intro x hxS hnil
    obtain ⟨n, hn⟩ := hnil
    have hiter : ∀ t : ℕ, x ^ ((2 ^ k) ^ t) = x := by
      intro t
      induction t with
      | zero => simp
      | succ t ih => rw [pow_succ, pow_mul, ih]; exact hfixS x hxS
    have h2k_ge_two : 2 ≤ 2 ^ k := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk_pos
    have hle : n ≤ (2 ^ k) ^ n :=
      (le_of_lt Nat.lt_two_pow_self).trans (Nat.pow_le_pow_left h2k_ge_two n)
    have hzero : x ^ ((2 ^ k) ^ n) = 0 := by
      rw [show (2 ^ k) ^ n = n + ((2 ^ k) ^ n - n) from (Nat.add_sub_cancel' hle).symm]
      rw [pow_add, hn, zero_mul]
    rw [hiter n] at hzero
    exact hzero

private theorem kgLangCSpanAux_toMulEquiv_pow_apply {R : Type*} [Ring R] (e : R ≃+* R) (n : ℕ)
    (x : R) : (e.toMulEquiv ^ n) x = (e ^ n) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, ih, pow_succ']
    rfl

private theorem kgLangCSpanAux_mapEquiv_pow_val {R : Type*} [Monoid R] (e : R ≃* R) (n : ℕ)
    (u : Rˣ) : (((Units.mapEquiv e) ^ n) u : R) = (e ^ n) (u : R) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, Units.coe_mapEquiv, ih, pow_succ', MulAut.mul_apply]

private theorem kgLangCSpanAux_coe_list_prod {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (S : Subalgebra R A) (l : List Sˣ) :
    ((↑(l.prod) : S) : A) = (List.map (fun u => ((u : S) : A)) l).prod := by
  induction l with
  | nil => rfl
  | cons u l ih => simp [List.prod_cons, List.map_cons, ih]

theorem kgLangC_span_h90 {p : ℕ} (hp : p.Prime) {ι 𝕂 : Type} [Fintype ι] [DecidableEq ι] [Field 𝕂]
    [Finite 𝕂] [CharP 𝕂 2] {σ : 𝕂 ≃+* 𝕂} (hσ : orderOf σ = p)
    (P : Subgroup (GL ι 𝕂)) (hab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hodd : Odd (Nat.card P))
    (B : Subalgebra 𝕂 (Matrix ι ι 𝕂))
    (hB : B = Algebra.adjoin 𝕂 ((fun g : GL ι 𝕂 => (g : Matrix ι ι 𝕂)) '' (P : Set (GL ι 𝕂))))
    (β : Matrix ι ι 𝕂 →+* Matrix ι ι 𝕂)
    (hβP : ∀ g ∈ P, β (g : Matrix ι ι 𝕂) ∈ (fun g : GL ι 𝕂 => (g : Matrix ι ι 𝕂)) '' (P : Set (GL ι 𝕂)))
    (hβsc : ∀ c : 𝕂, β (Matrix.scalar ι c) = Matrix.scalar ι (σ c))
    (hβp : ∀ a ∈ B, (⇑β)^[p] a = a) :
    ∀ x : GL ι 𝕂, (x : Matrix ι ι 𝕂) ∈ B →
      ((List.range p).map fun i => (⇑β)^[i] (x : Matrix ι ι 𝕂)).prod = 1 →
      ∃ s : GL ι 𝕂, (s : Matrix ι ι 𝕂) ∈ B ∧
        (x : Matrix ι ι 𝕂) = ((s⁻¹ : GL ι 𝕂) : Matrix ι ι 𝕂) * β (s : Matrix ι ι 𝕂) := by
  subst hB
  set s : Set (Matrix ι ι 𝕂) :=
    (fun g : GL ι 𝕂 => (g : Matrix ι ι 𝕂)) '' (P : Set _) with hs
  have hs_pair : s.Pairwise Commute := by
    intro a ha b hb _
    obtain ⟨g, hg, rfl⟩ := ha
    obtain ⟨h, hh, rfl⟩ := hb
    show Commute (↑g : Matrix ι ι 𝕂) (↑h : Matrix ι ι 𝕂)
    rw [commute_iff_eq, ← Matrix.GeneralLinearGroup.coe_mul, ← Matrix.GeneralLinearGroup.coe_mul,
      hab g hg h hh]
  have hcomm := (kgLangCSpanAux_adjoin_comm_reduced P hab hodd).1
  letI : CommRing ↥(Algebra.adjoin 𝕂 s) :=
    { (inferInstance : Ring ↥(Algebra.adjoin 𝕂 s)) with
      mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  haveI : Finite ↥(Algebra.adjoin 𝕂 s) := inferInstance
  have hred := (kgLangCSpanAux_adjoin_comm_reduced P hab hodd).2
  haveI : IsReduced ↥(Algebra.adjoin 𝕂 s) :=
    ⟨fun x hx => Subtype.ext (hred (x : Matrix ι ι 𝕂) x.2 (hx.map (Algebra.adjoin 𝕂 s).val))⟩
  have hβB : ∀ a ∈ Algebra.adjoin 𝕂 s, β a ∈ Algebra.adjoin 𝕂 s := by
    intro a ha
    refine Algebra.adjoin_induction (p := fun a _ => β a ∈ Algebra.adjoin 𝕂 s) ?_ ?_ ?_ ?_ ha
    · intro y hy
      obtain ⟨g, hg, rfl⟩ := hy
      exact Algebra.subset_adjoin (hβP g hg)
    · intro r
      have hr : algebraMap 𝕂 (Matrix ι ι 𝕂) r = Matrix.scalar ι r := by
        simp [Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
      rw [hr, hβsc]
      have hr2 : Matrix.scalar ι (σ r) = algebraMap 𝕂 (Matrix ι ι 𝕂) (σ r) := by
        simp [Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
      rw [hr2]
      exact Subalgebra.algebraMap_mem _ (σ r)
    · intro a b ha hb ha' hb'
      rw [map_add]
      exact add_mem ha' hb'
    · intro a b ha hb ha' hb'
      rw [map_mul]
      exact mul_mem ha' hb'
  let βB : ↥(Algebra.adjoin 𝕂 s) →+* ↥(Algebra.adjoin 𝕂 s) :=
    { toFun := fun a => ⟨β a, hβB a a.2⟩
      map_one' := by ext; simp
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp
      map_mul' := by intro a b; ext; simp }
  have hβB_val : ∀ a : ↥(Algebra.adjoin 𝕂 s),
      ((βB a : ↥(Algebra.adjoin 𝕂 s)) : Matrix ι ι 𝕂) = β (a : Matrix ι ι 𝕂) := fun _ => rfl
  have hβB_inj : Function.Injective βB := by
    intro a b hab
    have hβab : β (a : Matrix ι ι 𝕂) = β (b : Matrix ι ι 𝕂) := by
      have h := congrArg (fun z : ↥(Algebra.adjoin 𝕂 s) => (z : Matrix ι ι 𝕂)) hab
      simpa [hβB_val] using h
    have hp1 : p - 1 + 1 = p := Nat.succ_pred_eq_of_pos hp.pos
    have key : ∀ c : ↥(Algebra.adjoin 𝕂 s),
        (c : Matrix ι ι 𝕂) = (⇑β)^[p - 1] (β (c : Matrix ι ι 𝕂)) := by
      intro c
      have h := hβp (c : Matrix ι ι 𝕂) c.2
      rw [← hp1] at h
      rw [Function.iterate_succ_apply] at h
      exact h.symm
    apply Subtype.ext
    rw [key a, key b, hβab]
  have hβB_bij : Function.Bijective βB := Function.Injective.bijective_of_finite hβB_inj
  let βBe : ↥(Algebra.adjoin 𝕂 s) ≃+* ↥(Algebra.adjoin 𝕂 s) :=
    RingEquiv.ofBijective βB hβB_bij
  have hβBe_val : ∀ a : ↥(Algebra.adjoin 𝕂 s),
      ((βBe a : ↥(Algebra.adjoin 𝕂 s)) : Matrix ι ι 𝕂) = β (a : Matrix ι ι 𝕂) := by
    intro a
    rw [RingEquiv.ofBijective_apply]
    rfl
  have hβBe_pow_val : ∀ (i : ℕ) (a : ↥(Algebra.adjoin 𝕂 s)),
      (((βBe ^ i) a : ↥(Algebra.adjoin 𝕂 s)) : Matrix ι ι 𝕂) = (⇑β)^[i] (a : Matrix ι ι 𝕂) := by
    intro i
    induction i with
    | zero => intro a; simp
    | succ i ih =>
      intro a
      rw [pow_succ', show (βBe * βBe ^ i) a = βBe ((βBe ^ i) a) from rfl, hβBe_val, ih,
        Function.iterate_succ_apply']
  have hβe : βBe ^ p = 1 := by
    apply RingEquiv.ext
    intro a
    apply Subtype.ext
    rw [hβBe_pow_val p a, hβp (a : Matrix ι ι 𝕂) a.2]
    rfl
  have hσne : σ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hσ
    exact hp.ne_one hσ.symm
  have hstar : ∀ ε : ↥(Algebra.adjoin 𝕂 s), IsIdempotentElem ε → ε ≠ 0 → βBe ε = ε →
      ∃ x : ↥(Algebra.adjoin 𝕂 s), βBe (ε * x) ≠ ε * x := by
    intro ε _hεid hεne hεfix
    obtain ⟨c, hc⟩ := DFunLike.exists_ne hσne
    have hc' : σ c ≠ c := by simpa using hc
    have hc_mem : Matrix.scalar ι c ∈ Algebra.adjoin 𝕂 s := by
      have h : Matrix.scalar ι c = algebraMap 𝕂 (Matrix ι ι 𝕂) c := by
        simp [Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
      rw [h]
      exact Subalgebra.algebraMap_mem _ c
    refine ⟨⟨Matrix.scalar ι c, hc_mem⟩, ?_⟩
    intro heq
    have hβε : β (ε : Matrix ι ι 𝕂) = (ε : Matrix ι ι 𝕂) := by
      have h := congrArg (fun z : ↥(Algebra.adjoin 𝕂 s) => (z : Matrix ι ι 𝕂)) hεfix
      simpa [hβBe_val] using h
    have hval : (ε : Matrix ι ι 𝕂) * Matrix.scalar ι (σ c) =
        (ε : Matrix ι ι 𝕂) * Matrix.scalar ι c := by
      have h := congrArg (fun z : ↥(Algebra.adjoin 𝕂 s) => (z : Matrix ι ι 𝕂)) heq
      rw [hβBe_val] at h
      simp only [Subalgebra.coe_mul] at h
      rw [map_mul, hβε, hβsc] at h
      simpa using h
    have hzero : (ε : Matrix ι ι 𝕂) * Matrix.scalar ι (σ c - c) = 0 := by
      rw [map_sub, mul_sub, hval, sub_self]
    have hunit : IsUnit (Matrix.scalar ι (σ c - c)) := by
      have hd : σ c - c ≠ 0 := sub_ne_zero.mpr hc'
      exact IsUnit.map (Matrix.scalar ι) (isUnit_iff_ne_zero.mpr hd)
    obtain ⟨u, hu⟩ := hunit
    have hε0 : (ε : Matrix ι ι 𝕂) = 0 := by
      have h1 : (ε : Matrix ι ι 𝕂) * Matrix.scalar ι (σ c - c) * (↑u⁻¹ : Matrix ι ι 𝕂) = 0 := by
        rw [hzero, zero_mul]
      rw [mul_assoc, ← hu, Units.mul_inv, mul_one] at h1
      exact h1
    exact hεne (Subtype.ext hε0)
  have hnormSurj := kgLangC_normSurj hp βBe hβe hstar
  let β' : MulAut (↥(Algebra.adjoin 𝕂 s))ˣ := Units.mapEquiv βBe.toMulEquiv
  have hβ' : β' ^ p = 1 := by
    apply MulEquiv.ext
    intro u
    apply Units.ext
    rw [kgLangCSpanAux_mapEquiv_pow_val βBe.toMulEquiv p u, MulAut.one_apply]
    apply Subtype.ext
    rw [kgLangCSpanAux_toMulEquiv_pow_apply βBe p (u : ↥(Algebra.adjoin 𝕂 s)),
      hβBe_pow_val p (u : ↥(Algebra.adjoin 𝕂 s)),
      hβp (u : ↥(Algebra.adjoin 𝕂 s)) (u : ↥(Algebra.adjoin 𝕂 s)).2]
  let coeHom : (↥(Algebra.adjoin 𝕂 s))ˣ →* ↥(Algebra.adjoin 𝕂 s) :=
    Units.coeHom (↥(Algebra.adjoin 𝕂 s))
  have hnormSurj' : ∀ c : (↥(Algebra.adjoin 𝕂 s))ˣ, β' c = c →
      ∃ t : (↥(Algebra.adjoin 𝕂 s))ˣ,
        c = ((List.range p).map fun i => (β' ^ i) t).prod := by
    intro c hc
    have hc' : βBe (c : ↥(Algebra.adjoin 𝕂 s)) = (c : ↥(Algebra.adjoin 𝕂 s)) := by
      have h := congrArg (fun z : (↥(Algebra.adjoin 𝕂 s))ˣ => (z : ↥(Algebra.adjoin 𝕂 s))) hc
      simpa [β', Units.coe_mapEquiv] using h
    obtain ⟨t, ht⟩ := hnormSurj c hc'
    refine ⟨t, ?_⟩
    apply Units.ext
    rw [ht]
    rw [← List.toFinset_range p,
      List.prod_toFinset (fun i => (βBe ^ i) (t : ↥(Algebra.adjoin 𝕂 s))) List.nodup_range]
    rw [show (↑(((List.range p).map fun i => (β' ^ i) t).prod : (↥(Algebra.adjoin 𝕂 s))ˣ) :
          ↥(Algebra.adjoin 𝕂 s)) =
        (List.map (fun u : (↥(Algebra.adjoin 𝕂 s))ˣ => (↑u : ↥(Algebra.adjoin 𝕂 s)))
          ((List.range p).map fun i => (β' ^ i) t)).prod from
      map_list_prod (Units.coeHom (↥(Algebra.adjoin 𝕂 s))) _]
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [← kgLangCSpanAux_toMulEquiv_pow_apply βBe i (t : ↥(Algebra.adjoin 𝕂 s))]
    exact (kgLangCSpanAux_mapEquiv_pow_val βBe.toMulEquiv i t).symm
  have hH90 : ∀ c : (↥(Algebra.adjoin 𝕂 s))ˣ,
      ((List.range p).map fun i => (β' ^ i) c).prod = 1 → ∃ t, c = t⁻¹ * β' t :=
    (kgLangH90_iff_normSurj (p := p) β' hβ').mpr hnormSurj'
  intro x hx hnorm
  let valHom : ↥(Algebra.adjoin 𝕂 s) →* Matrix ι ι 𝕂 := Subalgebra.val (Algebra.adjoin 𝕂 s)
  have hxunit : IsUnit (⟨(x : Matrix ι ι 𝕂), hx⟩ : ↥(Algebra.adjoin 𝕂 s)) := by
    rw [isUnit_iff_mem_nonZeroDivisors_of_finite, mem_nonZeroDivisors_iff_right]
    intro y hy
    apply Subtype.ext
    have h := congrArg (fun z : ↥(Algebra.adjoin 𝕂 s) => (z : Matrix ι ι 𝕂)) hy
    simp only [Subalgebra.coe_mul, Subalgebra.coe_zero] at h
    have hxunit_mat : IsUnit (x : Matrix ι ι 𝕂) := ⟨x, rfl⟩
    have h' : (y : Matrix ι ι 𝕂) * (x : Matrix ι ι 𝕂) = (0 : Matrix ι ι 𝕂) * (x : Matrix ι ι 𝕂) := by
      rw [h, zero_mul]
    exact hxunit_mat.mul_right_cancel h'
  let x' : (↥(Algebra.adjoin 𝕂 s))ˣ := hxunit.unit
  have hx'_val : (x' : ↥(Algebra.adjoin 𝕂 s)) = ⟨(x : Matrix ι ι 𝕂), hx⟩ := IsUnit.unit_spec hxunit
  have hx'_map : Units.map valHom x' = x := by
    apply Units.ext
    rw [Units.coe_map, hx'_val]
    rfl
  let l : List (↥(Algebra.adjoin 𝕂 s))ˣ := (List.range p).map fun i => (β' ^ i) x'
  have hnorm' : l.prod = 1 := by
    apply Units.ext
    rw [Units.val_one]
    apply Subtype.ext
    rw [Subalgebra.coe_one, kgLangCSpanAux_coe_list_prod (Algebra.adjoin 𝕂 s) l, ← hnorm]
    apply congrArg List.prod
    dsimp only [l]
    rw [List.bind_eq_flatMap]
    rw [show List.flatMap (fun a : (↥(Algebra.adjoin 𝕂 s))ˣ =>
            pure (↑a : ↥(Algebra.adjoin 𝕂 s)))
          ((List.range p).map fun i => (β' ^ i) x') =
        List.map (fun a : (↥(Algebra.adjoin 𝕂 s))ˣ => (↑a : ↥(Algebra.adjoin 𝕂 s)))
          ((List.range p).map fun i => (β' ^ i) x') from
      List.flatMap_pure_eq_map
        (fun a : (↥(Algebra.adjoin 𝕂 s))ˣ => (↑a : ↥(Algebra.adjoin 𝕂 s))) _]
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply]
    rw [kgLangCSpanAux_mapEquiv_pow_val βBe.toMulEquiv i x',
      kgLangCSpanAux_toMulEquiv_pow_apply βBe i (x' : ↥(Algebra.adjoin 𝕂 s)),
      hβBe_pow_val i x', hx'_val]
  obtain ⟨t, ht⟩ := hH90 x' hnorm'
  refine ⟨Units.map valHom t, ?_, ?_⟩
  · rw [Units.coe_map]
    exact (t : ↥(Algebra.adjoin 𝕂 s)).2
  · have h := congrArg (Units.map valHom) ht
    rw [map_mul, map_inv, hx'_map] at h
    have hβt : ((Units.map valHom (β' t) : GL ι 𝕂) : Matrix ι ι 𝕂) =
        β ((Units.map valHom t : GL ι 𝕂) : Matrix ι ι 𝕂) := by
      rw [Units.coe_map, Units.coe_map, Units.coe_mapEquiv]
      change (βBe (t : ↥(Algebra.adjoin 𝕂 s)) : Matrix ι ι 𝕂) =
        β ((t : ↥(Algebra.adjoin 𝕂 s)) : Matrix ι ι 𝕂)
      rw [hβBe_val]
    have h' := congrArg (fun z : GL ι 𝕂 => (z : Matrix ι ι 𝕂)) h
    rw [h']
    simp only [Units.val_mul]
    rw [hβt]

theorem kgLangC_span_h90_unitary {p : ℕ} (hp : p.Prime) {ι 𝕂 : Type} [Fintype ι] [DecidableEq ι]
    [Field 𝕂] [Finite 𝕂] [CharP 𝕂 2] {σ : 𝕂 ≃+* 𝕂} (hσ : orderOf σ = p)
    (P : Subgroup (GL ι 𝕂)) (hab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hodd : Odd (Nat.card P))
    (B : Subalgebra 𝕂 (Matrix ι ι 𝕂))
    (hB : B = Algebra.adjoin 𝕂 ((fun g : GL ι 𝕂 => (g : Matrix ι ι 𝕂)) '' (P : Set (GL ι 𝕂))))
    (β : Matrix ι ι 𝕂 →+* Matrix ι ι 𝕂)
    (hβP : ∀ g ∈ P, β (g : Matrix ι ι 𝕂) ∈ (fun g : GL ι 𝕂 => (g : Matrix ι ι 𝕂)) '' (P : Set (GL ι 𝕂)))
    (hβsc : ∀ c : 𝕂, β (Matrix.scalar ι c) = Matrix.scalar ι (σ c))
    (hβp : ∀ a ∈ B, (⇑β)^[p] a = a)
    (τ : Matrix ι ι 𝕂 → Matrix ι ι 𝕂) (hτB : ∀ a ∈ B, τ a ∈ B)
    (hτadd : ∀ a ∈ B, ∀ b ∈ B, τ (a + b) = τ a + τ b)
    (hτmul : ∀ a ∈ B, ∀ b ∈ B, τ (a * b) = τ a * τ b) (hτone : τ 1 = 1)
    (hττ : ∀ a ∈ B, τ (τ a) = a) (hτβ : ∀ a ∈ B, τ (β a) = β (τ a)) :
    ∀ x : GL ι 𝕂, (x : Matrix ι ι 𝕂) ∈ B → (x : Matrix ι ι 𝕂) * τ x = 1 →
      ((List.range p).map fun i => (⇑β)^[i] (x : Matrix ι ι 𝕂)).prod = 1 →
      ∃ s : GL ι 𝕂, (s : Matrix ι ι 𝕂) ∈ B ∧ (s : Matrix ι ι 𝕂) * τ s = 1 ∧
        (x : Matrix ι ι 𝕂) = ((s⁻¹ : GL ι 𝕂) : Matrix ι ι 𝕂) * β (s : Matrix ι ι 𝕂) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · haveI := hι
    intro x _hx _hxτ _hnorm
    exact ⟨1, Subalgebra.one_mem _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  · haveI : Nonempty ι := hι
    subst hB
    set s : Set (Matrix ι ι 𝕂) :=
      (fun g : GL ι 𝕂 => (g : Matrix ι ι 𝕂)) '' (P : Set _) with hs
    have hs_pair : s.Pairwise Commute := by
      intro a ha b hb _
      obtain ⟨g, hg, rfl⟩ := ha
      obtain ⟨h, hh, rfl⟩ := hb
      show Commute (↑g : Matrix ι ι 𝕂) (↑h : Matrix ι ι 𝕂)
      rw [commute_iff_eq, ← Matrix.GeneralLinearGroup.coe_mul, ← Matrix.GeneralLinearGroup.coe_mul,
        hab g hg h hh]
    have hcomm := (kgLangCSpanAux_adjoin_comm_reduced P hab hodd).1
    letI : CommRing ↥(Algebra.adjoin 𝕂 s) :=
      { (inferInstance : Ring ↥(Algebra.adjoin 𝕂 s)) with
        mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
    haveI : Finite ↥(Algebra.adjoin 𝕂 s) := inferInstance
    have hred := (kgLangCSpanAux_adjoin_comm_reduced P hab hodd).2
    haveI : IsReduced ↥(Algebra.adjoin 𝕂 s) :=
      ⟨fun x hx => Subtype.ext (hred (x : Matrix ι ι 𝕂) x.2 (hx.map (Algebra.adjoin 𝕂 s).val))⟩
    have hβB : ∀ a ∈ Algebra.adjoin 𝕂 s, β a ∈ Algebra.adjoin 𝕂 s := by
      intro a ha
      refine Algebra.adjoin_induction (p := fun a _ => β a ∈ Algebra.adjoin 𝕂 s) ?_ ?_ ?_ ?_ ha
      · intro y hy
        obtain ⟨g, hg, rfl⟩ := hy
        exact Algebra.subset_adjoin (hβP g hg)
      · intro r
        have hr : algebraMap 𝕂 (Matrix ι ι 𝕂) r = Matrix.scalar ι r := by
          simp [Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
        rw [hr, hβsc]
        have hr2 : Matrix.scalar ι (σ r) = algebraMap 𝕂 (Matrix ι ι 𝕂) (σ r) := by
          simp [Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
        rw [hr2]
        exact Subalgebra.algebraMap_mem _ (σ r)
      · intro a b ha hb ha' hb'
        rw [map_add]
        exact add_mem ha' hb'
      · intro a b ha hb ha' hb'
        rw [map_mul]
        exact mul_mem ha' hb'
    let βB : ↥(Algebra.adjoin 𝕂 s) →+* ↥(Algebra.adjoin 𝕂 s) :=
      { toFun := fun a => ⟨β a, hβB a a.2⟩
        map_one' := by ext; simp
        map_zero' := by ext; simp
        map_add' := by intro a b; ext; simp
        map_mul' := by intro a b; ext; simp }
    have hβB_val : ∀ a : ↥(Algebra.adjoin 𝕂 s),
        ((βB a : ↥(Algebra.adjoin 𝕂 s)) : Matrix ι ι 𝕂) = β (a : Matrix ι ι 𝕂) := fun _ => rfl
    have hβB_inj : Function.Injective βB := by
      intro a b hab
      have hβab : β (a : Matrix ι ι 𝕂) = β (b : Matrix ι ι 𝕂) := by
        have h := congrArg (fun z : ↥(Algebra.adjoin 𝕂 s) => (z : Matrix ι ι 𝕂)) hab
        simpa [hβB_val] using h
      have hp1 : p - 1 + 1 = p := Nat.succ_pred_eq_of_pos hp.pos
      have key : ∀ c : ↥(Algebra.adjoin 𝕂 s),
          (c : Matrix ι ι 𝕂) = (⇑β)^[p - 1] (β (c : Matrix ι ι 𝕂)) := by
        intro c
        have h := hβp (c : Matrix ι ι 𝕂) c.2
        rw [← hp1] at h
        rw [Function.iterate_succ_apply] at h
        exact h.symm
      apply Subtype.ext
      rw [key a, key b, hβab]
    have hβB_bij : Function.Bijective βB := Function.Injective.bijective_of_finite hβB_inj
    let βBe : ↥(Algebra.adjoin 𝕂 s) ≃+* ↥(Algebra.adjoin 𝕂 s) :=
      RingEquiv.ofBijective βB hβB_bij
    have hβBe_val : ∀ a : ↥(Algebra.adjoin 𝕂 s),
        ((βBe a : ↥(Algebra.adjoin 𝕂 s)) : Matrix ι ι 𝕂) = β (a : Matrix ι ι 𝕂) := by
      intro a
      rw [RingEquiv.ofBijective_apply]
      rfl
    have hβBe_pow_val : ∀ (i : ℕ) (a : ↥(Algebra.adjoin 𝕂 s)),
        (((βBe ^ i) a : ↥(Algebra.adjoin 𝕂 s)) : Matrix ι ι 𝕂) = (⇑β)^[i] (a : Matrix ι ι 𝕂) := by
      intro i
      induction i with
      | zero => intro a; simp
      | succ i ih =>
        intro a
        rw [pow_succ', show (βBe * βBe ^ i) a = βBe ((βBe ^ i) a) from rfl, hβBe_val, ih,
          Function.iterate_succ_apply']
    have hβe : βBe ^ p = 1 := by
      apply RingEquiv.ext
      intro a
      apply Subtype.ext
      rw [hβBe_pow_val p a, hβp (a : Matrix ι ι 𝕂) a.2]
      rfl
    have hσne : σ ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hσ
      exact hp.ne_one hσ.symm
    have hstar : ∀ ε : ↥(Algebra.adjoin 𝕂 s), IsIdempotentElem ε → ε ≠ 0 → βBe ε = ε →
        ∃ x : ↥(Algebra.adjoin 𝕂 s), βBe (ε * x) ≠ ε * x := by
      intro ε _hεid hεne hεfix
      obtain ⟨c, hc⟩ := DFunLike.exists_ne hσne
      have hc' : σ c ≠ c := by simpa using hc
      have hc_mem : Matrix.scalar ι c ∈ Algebra.adjoin 𝕂 s := by
        have h : Matrix.scalar ι c = algebraMap 𝕂 (Matrix ι ι 𝕂) c := by
          simp [Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
        rw [h]
        exact Subalgebra.algebraMap_mem _ c
      refine ⟨⟨Matrix.scalar ι c, hc_mem⟩, ?_⟩
      intro heq
      have hβε : β (ε : Matrix ι ι 𝕂) = (ε : Matrix ι ι 𝕂) := by
        have h := congrArg (fun z : ↥(Algebra.adjoin 𝕂 s) => (z : Matrix ι ι 𝕂)) hεfix
        simpa [hβBe_val] using h
      have hval : (ε : Matrix ι ι 𝕂) * Matrix.scalar ι (σ c) =
          (ε : Matrix ι ι 𝕂) * Matrix.scalar ι c := by
        have h := congrArg (fun z : ↥(Algebra.adjoin 𝕂 s) => (z : Matrix ι ι 𝕂)) heq
        rw [hβBe_val] at h
        simp only [Subalgebra.coe_mul] at h
        rw [map_mul, hβε, hβsc] at h
        simpa using h
      have hzero : (ε : Matrix ι ι 𝕂) * Matrix.scalar ι (σ c - c) = 0 := by
        rw [map_sub, mul_sub, hval, sub_self]
      have hunit : IsUnit (Matrix.scalar ι (σ c - c)) := by
        have hd : σ c - c ≠ 0 := sub_ne_zero.mpr hc'
        exact IsUnit.map (Matrix.scalar ι) (isUnit_iff_ne_zero.mpr hd)
      obtain ⟨u, hu⟩ := hunit
      have hε0 : (ε : Matrix ι ι 𝕂) = 0 := by
        have h1 : (ε : Matrix ι ι 𝕂) * Matrix.scalar ι (σ c - c) * (↑u⁻¹ : Matrix ι ι 𝕂) = 0 := by
          rw [hzero, zero_mul]
        rw [mul_assoc, ← hu, Units.mul_inv, mul_one] at h1
        exact h1
      exact hεne (Subtype.ext hε0)
    let τB : ↥(Algebra.adjoin 𝕂 s) →+* ↥(Algebra.adjoin 𝕂 s) :=
      { toFun := fun a => ⟨τ a, hτB a a.2⟩
        map_one' := by
          apply Subtype.ext
          show τ (1 : Matrix ι ι 𝕂) = 1
          exact hτone
        map_zero' := by
          apply Subtype.ext
          have h : τ (0 : Matrix ι ι 𝕂) = τ 0 + τ 0 := by
            simpa using hτadd 0 (zero_mem _) 0 (zero_mem _)
          exact add_left_cancel (show τ 0 + τ 0 = τ 0 + 0 by rw [add_zero]; exact h.symm)
        map_add' := by intro a b; apply Subtype.ext; exact hτadd a a.2 b b.2
        map_mul' := by intro a b; apply Subtype.ext; exact hτmul a a.2 b b.2 }
    have hτB_invol : Function.Involutive τB := by
      intro a
      apply Subtype.ext
      exact hττ a a.2
    let τBe : ↥(Algebra.adjoin 𝕂 s) ≃+* ↥(Algebra.adjoin 𝕂 s) :=
      RingEquiv.ofBijective τB hτB_invol.bijective
    have hτBe_val : ∀ a : ↥(Algebra.adjoin 𝕂 s),
        ((τBe a : ↥(Algebra.adjoin 𝕂 s)) : Matrix ι ι 𝕂) = τ (a : Matrix ι ι 𝕂) := by
      intro a
      rw [RingEquiv.ofBijective_apply]
      rfl
    have hτBe_inv : τBe * τBe = 1 := by
      apply RingEquiv.ext
      intro a
      apply Subtype.ext
      change τ (τ (a : Matrix ι ι 𝕂)) = (a : Matrix ι ι 𝕂)
      exact hττ a a.2
    have hβτBe : βBe * τBe = τBe * βBe := by
      apply RingEquiv.ext
      intro a
      apply Subtype.ext
      change β (τ (a : Matrix ι ι 𝕂)) = τ (β (a : Matrix ι ι 𝕂))
      exact (hτβ a a.2).symm
    haveI : CharP ↥(Algebra.adjoin 𝕂 s) 2 := by
      have halg_inj : Function.Injective (algebraMap 𝕂 ↥(Algebra.adjoin 𝕂 s)) := by
        intro a b hab
        have ha := congrArg (fun z : ↥(Algebra.adjoin 𝕂 s) => (z : Matrix ι ι 𝕂)) hab
        simp only [Subalgebra.coe_algebraMap] at ha
        have hr : ∀ r : 𝕂, algebraMap 𝕂 (Matrix ι ι 𝕂) r = Matrix.scalar ι r := by
          intro r
          simp [Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
        rw [hr a, hr b] at ha
        exact Matrix.scalar_inj.mp ha
      exact charP_of_injective_algebraMap halg_inj 2
    have hlist_eq : ∀ (f : ℕ → ↥(Algebra.adjoin 𝕂 s)),
        ((List.range p).map f).prod = ∏ i ∈ Finset.range p, f i := by
      intro f
      rw [← List.prod_toFinset f List.nodup_range, List.toFinset_range]
    intro x hx hxτ hnorm
    let valHom : ↥(Algebra.adjoin 𝕂 s) →* Matrix ι ι 𝕂 := Subalgebra.val (Algebra.adjoin 𝕂 s)
    have hxunit : IsUnit (⟨(x : Matrix ι ι 𝕂), hx⟩ : ↥(Algebra.adjoin 𝕂 s)) := by
      rw [isUnit_iff_mem_nonZeroDivisors_of_finite, mem_nonZeroDivisors_iff_right]
      intro y hy
      apply Subtype.ext
      have h := congrArg (fun z : ↥(Algebra.adjoin 𝕂 s) => (z : Matrix ι ι 𝕂)) hy
      simp only [Subalgebra.coe_mul, Subalgebra.coe_zero] at h
      have hxunit_mat : IsUnit (x : Matrix ι ι 𝕂) := ⟨x, rfl⟩
      have h' : (y : Matrix ι ι 𝕂) * (x : Matrix ι ι 𝕂) =
          (0 : Matrix ι ι 𝕂) * (x : Matrix ι ι 𝕂) := by
        rw [h, zero_mul]
      exact hxunit_mat.mul_right_cancel h'
    let x' : (↥(Algebra.adjoin 𝕂 s))ˣ := hxunit.unit
    have hx'_val : (x' : ↥(Algebra.adjoin 𝕂 s)) = ⟨(x : Matrix ι ι 𝕂), hx⟩ :=
      IsUnit.unit_spec hxunit
    have hx'_map : Units.map valHom x' = x := by
      apply Units.ext
      rw [Units.coe_map, hx'_val]
      rfl
    have hx'τ : (x' : ↥(Algebra.adjoin 𝕂 s)) * τBe x' = 1 := by
      apply Subtype.ext
      rw [Subalgebra.coe_mul, Subalgebra.coe_one,
        hτBe_val (x' : ↥(Algebra.adjoin 𝕂 s)), hx'_val]
      simpa using hxτ
    have hnormB : ∏ i ∈ Finset.range p, (βBe ^ i) (x' : ↥(Algebra.adjoin 𝕂 s)) = 1 := by
      rw [← hlist_eq (fun i => (βBe ^ i) (x' : ↥(Algebra.adjoin 𝕂 s)))]
      apply Subtype.ext
      rw [Subalgebra.coe_one]
      change (Algebra.adjoin 𝕂 s).val
        ((List.map (fun i => (βBe ^ i) (x' : ↥(Algebra.adjoin 𝕂 s)))
          (List.range p)).prod) = 1
      rw [map_list_prod (Algebra.adjoin 𝕂 s).val, List.map_map]
      rw [show (List.map (⇑(Algebra.adjoin 𝕂 s).val ∘
              (fun i => (βBe ^ i) (x' : ↥(Algebra.adjoin 𝕂 s)))) (List.range p)) =
            List.map (fun i => (⇑β)^[i] (x : Matrix ι ι 𝕂)) (List.range p) from by
        apply List.map_congr_left
        intro i _
        show ((βBe ^ i) (x' : ↥(Algebra.adjoin 𝕂 s)) : Matrix ι ι 𝕂) =
          (⇑β)^[i] (x : Matrix ι ι 𝕂)
        rw [hβBe_pow_val i (x' : ↥(Algebra.adjoin 𝕂 s)), hx'_val]]
      exact hnorm
    obtain ⟨t, htτ, ht⟩ :=
      kgLangC_unitary_h90 hp βBe hβe hstar τBe hτBe_inv hβτBe x' hx'τ hnormB
    let β' : MulAut (↥(Algebra.adjoin 𝕂 s))ˣ := Units.mapEquiv βBe.toMulEquiv
    have ht_units : x' = t⁻¹ * β' t := by
      apply Units.ext
      rw [Units.val_mul, Units.coe_mapEquiv]
      exact ht
    have hβt : ((Units.map valHom (β' t) : GL ι 𝕂) : Matrix ι ι 𝕂) =
        β ((Units.map valHom t : GL ι 𝕂) : Matrix ι ι 𝕂) := by
      rw [Units.coe_map, Units.coe_mapEquiv, Units.coe_map]
      exact hβBe_val (t : ↥(Algebra.adjoin 𝕂 s))
    refine ⟨Units.map valHom t, ?_, ?_, ?_⟩
    · rw [Units.coe_map]
      exact (t : ↥(Algebra.adjoin 𝕂 s)).2
    · have h := congrArg (fun z : ↥(Algebra.adjoin 𝕂 s) => (z : Matrix ι ι 𝕂)) htτ
      rw [Subalgebra.coe_mul, Subalgebra.coe_one, hτBe_val (t : ↥(Algebra.adjoin 𝕂 s))] at h
      rw [Units.coe_map]
      exact h
    · have h := congrArg (Units.map valHom) ht_units
      rw [map_mul, map_inv, hx'_map] at h
      have h' := congrArg (fun z : GL ι 𝕂 => (z : Matrix ι ι 𝕂)) h
      rw [h']
      simp only [Units.val_mul]
      rw [hβt]

end CFSG.StandardType
