module

public import CFSG.Quasithin.EmptyFaithful.S1421QNSDefs
public import CFSG.LinearAlgebra.OddSolvableUnitary.CommutatorForm

public section

namespace CFSG.Quasithin.AutExt9

open Module Subgroup
open scoped commutatorElement

section Fixed

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem add_self_eq_zero (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v]
  have : (2 : ZMod 2) = 0 := rfl
  rw [this, zero_smul]

theorem sub_one_apply_eq_zero_of_fixed {f : Module.End (ZMod 2) V} {m : ℕ} (hm : Odd m)
    (hfm : f ^ m = 1) {v : V} (h : f ((f - 1) v) = (f - 1) v) : (f - 1) v = 0 := by
  rw [LinearMap.sub_apply, Module.End.one_apply, map_sub] at h
  have h2 : f (f v) = v := by
    calc f (f v) = f v - v + f v := sub_eq_iff_eq_add.1 h
      _ = (f v + f v) - v := by abel
      _ = 0 - v := by rw [add_self_eq_zero]
      _ = v := by rw [zero_sub]; exact neg_eq_of_add_eq_zero_left (add_self_eq_zero v)
  have h5 : ∀ k : ℕ, (f ^ (2 * k)) v = v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add, Module.End.mul_apply,
        pow_two, Module.End.mul_apply, h2, ih]
  obtain ⟨k, rfl⟩ := hm
  have h6 : f v = v := by
    have h7 : (f ^ (2 * k + 1)) v = v := by rw [hfm]; rfl
    rw [pow_succ', Module.End.mul_apply, h5] at h7
    exact h7
  rw [LinearMap.sub_apply, Module.End.one_apply, h6, sub_self]

variable [FiniteDimensional (ZMod 2) V]

theorem even_finrank_ker_sub_one {B : LinearMap.BilinForm (ZMod 2) V} (hB : B.IsAlt)
    (hnd : B.Nondegenerate) {f : Module.End (ZMod 2) V} (hf : ∀ v w, B (f v) (f w) = B v w)
    {m : ℕ} (hm : Odd m) (hfm : f ^ m = 1) :
    Even (finrank (ZMod 2) (LinearMap.ker (f - 1))) := by
  classical
  set C := LinearMap.ker (f - 1) with hC
  set W := LinearMap.range (f - 1) with hW
  have hCmem : ∀ v, v ∈ C ↔ f v = v := fun v => by
    rw [hC, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  have hCW : Disjoint C W := by
    rw [Submodule.disjoint_def]
    rintro w hwC ⟨v, rfl⟩
    exact sub_one_apply_eq_zero_of_fixed hm hfm ((hCmem _).1 hwC)
  have hWC : W ≤ B.orthogonal C := by
    rintro w ⟨v, rfl⟩
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro c hc
    have hc' : f c = c := (hCmem c).1 hc
    rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, ← hf c v, hc']
    exact sub_self _
  have hrk : finrank (ZMod 2) W + finrank (ZMod 2) C = finrank (ZMod 2) V :=
    LinearMap.finrank_range_add_finrank_ker (f - 1)
  have horth := LinearMap.BilinForm.finrank_orthogonal hnd C
  have hWeq : W = B.orthogonal C :=
    Submodule.eq_of_le_of_finrank_eq hWC (by rw [horth]; omega)
  have hdisj : Disjoint C (B.orthogonal C) := hWeq ▸ hCW
  have hnd' : (B.restrict C).Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal B hB.isRefl hdisj
  have halt' : (B.restrict C).IsAlt := fun x => hB x
  exact LinearMap.BilinForm.IsAlt.even_finrank halt' hnd'

end Fixed

section Counting

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem card_modEq_card_fixed [Finite V] (f : Module.End (ZMod 2) V) {p n : ℕ} [Fact p.Prime]
    (hfp : f ^ p ^ n = 1) : Nat.card V ≡ Nat.card {v : V // f v = v} [MOD p] := by
  classical
  have : Fintype V := Fintype.ofFinite V
  have h := Equiv.Perm.card_fixedPoints_modEq
    (f := MulAction.toEndHom (M := Module.End (ZMod 2) V) (α := V) f)
    (p := p) (n := n) (by rw [← map_pow, hfp, map_one])
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card] at h
  exact h

theorem exists_card_fixed_of_isometry [Finite V] {B : LinearMap.BilinForm (ZMod 2) V}
    (hBa : B.IsAlt) (hBn : B.Nondegenerate) {N : ℕ} (hV : Nat.card V = 2 ^ N)
    {f : Module.End (ZMod 2) V} (hf : ∀ v w, B (f v) (f w) = B v w) {p n : ℕ} [Fact p.Prime]
    (hodd : Odd p) (hfp : f ^ p ^ n = 1) (hne : f ≠ 1) :
    ∃ c : ℕ, c < N ∧ Even c ∧ 2 ^ N ≡ 2 ^ c [MOD p] ∧ Nat.card {v : V // f v = v} = 2 ^ c := by
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hcard : ∀ S : Submodule (ZMod 2) V, Nat.card S = 2 ^ finrank (ZMod 2) S := fun S => by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hfr : finrank (ZMod 2) V = N := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
    rw [hV, Nat.card_zmod] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  set C := LinearMap.ker (f - 1) with hC
  have hCmem : ∀ v, v ∈ C ↔ f v = v := fun v => by
    rw [hC, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  have hev : Even (finrank (ZMod 2) C) :=
    even_finrank_ker_sub_one hBa hBn hf (hodd.pow : Odd (p ^ n)) hfp
  have hCtop : C ≠ ⊤ := by
    intro h
    apply hne
    refine LinearMap.ext fun v => ?_
    have : v ∈ C := h ▸ Submodule.mem_top
    exact (hCmem v).1 this
  have hlt : finrank (ZMod 2) C < N := hfr ▸ Submodule.finrank_lt hCtop
  have hfix : Nat.card {v : V // f v = v} = 2 ^ finrank (ZMod 2) C := by
    rw [← hcard C]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun v => (hCmem v).symm)
  refine ⟨finrank (ZMod 2) C, hlt, hev, ?_, hfix⟩
  have := card_modEq_card_fixed f hfp (p := p) (n := n)
  rwa [hV, hfix] at this

end Counting

section Group

variable {Q : Type} [Group Q]

theorem facts_of_isSpecialPow [Finite Q] (hQ : IsSpecialPow 2 2 4 Q) :
    center Q = commutator Q ∧ (∀ x : Q, x ^ 2 ∈ center Q) ∧ Nat.card (center Q) = 2 ∧
      Nat.card Q = 512 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hQ2, hsp⟩, hcard, hZ⟩ := hQ
  have : Fact (IsPGroup 2 Q) := ⟨hQ2⟩
  have h512 : Nat.card Q = 512 := by rw [hcard]; norm_num
  rcases hsp with ⟨hab, -⟩ | ⟨hcomm, hfr, -⟩
  · exfalso
    have htop : center Q = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      exact hab.is_comm.comm y x
    rw [htop, Subgroup.card_top, h512] at hZ
    omega
  · exact ⟨hcomm.symm, fun x => hfr ▸ CFSG.pth_power_mem_frattini_of_isPGroup (p := 2) x, hZ,
      h512⟩

theorem mulAut_apply_eq_of_mem_center (hc : Nat.card (center Q) = 2) (φ : MulAut Q) {z : Q}
    (hz : z ∈ center Q) : φ z = z := by
  have hφz : φ z ∈ center Q := by
    rw [Subgroup.mem_center_iff]
    intro r
    obtain ⟨s, rfl⟩ := φ.surjective r
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz s]
  by_cases h1 : z = 1
  · rw [h1, map_one]
  · obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : center Q)).1 hc
    have hne : (⟨φ z, hφz⟩ : center Q) ≠ 1 := fun h => h1 (φ.injective
      ((congrArg Subtype.val h).trans (map_one φ).symm))
    have hne' : (⟨z, hz⟩ : center Q) ≠ 1 := fun h => h1 (congrArg Subtype.val h)
    exact congrArg Subtype.val ((hy _ hne).trans (hy _ hne').symm)

theorem mul_self_eq_one_of_mem_center (hc : Nat.card (center Q) = 2) {z : Q}
    (hz : z ∈ center Q) : z * z = 1 := by
  have h : (⟨z, hz⟩ : center Q) ^ Nat.card (center Q) = 1 := pow_card_eq_one'
  rw [hc, sq] at h
  exact congrArg Subtype.val h

theorem exists_ofMul_of (v : Additive (Abelianization Q)) :
    ∃ q : Q, Additive.ofMul (Abelianization.of q) = v := by
  obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective v.toMul
  refine ⟨q, ?_⟩
  change Additive.ofMul (QuotientGroup.mk q : Abelianization Q) = v
  rw [hq]
  rfl

theorem two_nsmul_eq_zero (hZ : center Q = commutator Q) (hsq : ∀ x : Q, x ^ 2 ∈ center Q)
    (v : Additive (Abelianization Q)) : 2 • v = 0 := by
  obtain ⟨x, rfl⟩ := exists_ofMul_of v
  rw [← ofMul_pow, ← map_pow]
  have hx : x ^ 2 ∈ (Abelianization.of : Q →* Abelianization Q).ker := by
    rw [Abelianization.ker_of, ← hZ]
    exact hsq x
  rw [MonoidHom.mem_ker.1 hx]
  rfl

variable [Module (ZMod 2) (Additive (Abelianization Q))]

@[expose] def autEnd : MulAut Q →* Module.End (ZMod 2) (Additive (Abelianization Q)) where
  toFun g := (MonoidHom.toAdditive (Abelianization.map g.toMonoidHom)).toZModLinearMap 2
  map_one' := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨q, rfl⟩ := exists_ofMul_of v
    rfl
  map_mul' g g' := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨q, rfl⟩ := exists_ofMul_of v
    rfl

theorem autEnd_apply (g : MulAut Q) (x : Q) :
    autEnd g (Additive.ofMul (Abelianization.of x)) =
      Additive.ofMul (Abelianization.of (g x)) := rfl

end Group

section Rep

variable {Q : Type} [Group Q] [Finite Q]

theorem exists_symplectic_rep (hQ : IsSpecialPow 2 2 4 Q) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 2) V) (_ : Finite V)
      (B : LinearMap.BilinForm (ZMod 2) V) (ρ : MulAut Q →* Module.End (ZMod 2) V),
      B.IsAlt ∧ B.Nondegenerate ∧ Nat.card V = 2 ^ 8 ∧ (∀ g v w, B (ρ g v) (ρ g w) = B v w) ∧
        ∀ g : MulAut Q, ∀ m : ℕ, Odd m → g ^ m = 1 → ρ g = 1 → g = 1 := by
  obtain ⟨hZ, hsq, hc, h512⟩ := facts_of_isSpecialPow hQ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Module (ZMod 2) (Additive (Abelianization Q)) :=
    AddCommGroup.zmodModule (two_nsmul_eq_zero hZ hsq)
  obtain ⟨ε⟩ := CFSG.OddSolvableUnitary.nonempty_center_mulEquiv hc
  obtain ⟨B, hBa, hBn, hB⟩ := CFSG.OddSolvableUnitary.exists_commForm hZ ε
  have hfin : Finite (Additive (Abelianization Q)) :=
    Finite.of_surjective (fun x : Q => Additive.ofMul (Abelianization.of x))
      fun v => (exists_ofMul_of v).imp fun _ h => h
  have hcardV : Nat.card (Additive (Abelianization Q)) = 2 ^ 8 := by
    have h := CFSG.OddSolvableUnitary.card_eq_card_abelianization_mul hZ hc
    rw [h512] at h
    have h2 : Nat.card (Abelianization Q) = 2 ^ 8 := by omega
    rw [← h2]
    exact Nat.card_congr Additive.toMul
  refine ⟨Additive (Abelianization Q), inferInstance, inferInstance, hfin, B, autEnd, hBa, hBn,
    hcardV, ?_, ?_⟩
  · intro g v w
    obtain ⟨x, rfl⟩ := exists_ofMul_of v
    obtain ⟨y, rfl⟩ := exists_ofMul_of w
    rw [autEnd_apply, autEnd_apply, hB, hB]
    have : (⟨⁅g x, g y⁆, CFSG.OddSolvableUnitary.commutatorElement_mem_center hZ _ _⟩ :
        center Q) = ⟨⁅x, y⁆, CFSG.OddSolvableUnitary.commutatorElement_mem_center hZ _ _⟩ := by
      refine Subtype.ext ?_
      show ⁅g x, g y⁆ = ⁅x, y⁆
      rw [← map_commutatorElement]
      exact mulAut_apply_eq_of_mem_center hc g
        (CFSG.OddSolvableUnitary.commutatorElement_mem_center hZ x y)
    rw [this]
  · intro g m hm hgm hρ
    have hg2 : g * g = 1 := by
      ext x
      have h1 : Additive.ofMul (Abelianization.of (g x)) =
          Additive.ofMul (Abelianization.of x) := by
        have := LinearMap.congr_fun hρ (Additive.ofMul (Abelianization.of x))
        rwa [autEnd_apply, Module.End.one_apply] at this
      have h2 : Abelianization.of (g x) = Abelianization.of x := Additive.ofMul.injective h1
      have h3 : (g x)⁻¹ * x ∈ center Q := by
        rw [hZ, ← Abelianization.ker_of, MonoidHom.mem_ker, map_mul, map_inv, h2, inv_mul_cancel]
      have hw : x⁻¹ * g x ∈ center Q := by
        have := inv_mem h3
        rwa [mul_inv_rev, inv_inv] at this
      have hww := mul_self_eq_one_of_mem_center hc hw
      have hgx : g x = x * (x⁻¹ * g x) := (mul_inv_cancel_left x (g x)).symm
      generalize x⁻¹ * g x = w at hgx hw hww
      calc (g * g) x = g (g x) := rfl
        _ = g (x * w) := by rw [← hgx]
        _ = g x * w := by rw [map_mul, mulAut_apply_eq_of_mem_center hc g hw]
        _ = x * (w * w) := by rw [hgx, mul_assoc]
        _ = x := by rw [hww, mul_one]
    obtain ⟨k, rfl⟩ := hm
    have : g ^ (2 * k + 1) = g := by
      rw [pow_succ, pow_mul, pow_two, hg2, one_pow, one_mul]
    rw [← this, hgm]

end Rep

end CFSG.Quasithin.AutExt9

namespace CFSG.Quasithin

open CFSG.Quasithin.AutExt9

theorem autExt9Facts_holds : AutExt9Facts := by
  intro Q _ _ hQ
  obtain ⟨V, _, _, _, B, ρ, hBa, hBn, hV, hinv, hfaith⟩ := exists_symplectic_rep hQ
  have key : ∀ (p n : ℕ) [Fact p.Prime], Odd p → ∀ g : MulAut Q, g ≠ 1 → g ^ (p ^ n) = 1 →
      ∃ c : ℕ, c < 8 ∧ Even c ∧ 2 ^ 8 ≡ 2 ^ c [MOD p] ∧
        Nat.card {v : V // ρ g v = v} = 2 ^ c := by
    intro p n _ hp g hg1 hgp
    exact exists_card_fixed_of_isometry hBa hBn hV (hinv g) hp
      (by rw [← map_pow, hgp, map_one]) (fun h => hg1 (hfaith g (p ^ n) hp.pow hgp h))
  have hprime : ∀ r : ℕ, Nat.Prime r → Odd r → r ∣ Nat.card (MulAut Q) →
      ∃ c : ℕ, c < 8 ∧ 2 ^ 8 ≡ 2 ^ c [MOD r] := by
    intro r hr hodd hdvd
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' r hdvd
    have hg1 : g ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hg
      exact hr.one_lt.ne hg
    have hgp : g ^ (r ^ 1) = 1 := by rw [pow_one, ← hg]; exact pow_orderOf_eq_one g
    obtain ⟨c, hc8, -, hmod, -⟩ := key r 1 hodd g hg1 hgp
    exact ⟨c, hc8, hmod⟩
  refine ⟨fun h => ?_, fun h => ?_, ?_⟩
  · obtain ⟨c, hc8, hmod⟩ := hprime 13 (by norm_num) (by decide) h
    interval_cases c <;> revert hmod <;> decide
  · obtain ⟨c, hc8, hmod⟩ := hprime 73 (by norm_num) (by decide) h
    interval_cases c <;> revert hmod <;> decide
  · rintro ⟨E, hE⟩
    have h4 : ∀ g : E, g ≠ 1 → Nat.card {v : V // ρ (g : MulAut Q) v = v} = 4 := by
      intro g hg
      have hg1 : (g : MulAut Q) ≠ 1 := fun h => hg (Subtype.ext h)
      have hgp : (g : MulAut Q) ^ (7 ^ 2) = 1 := by
        have h1 : g ^ Nat.card E = 1 := pow_card_eq_one'
        rw [hE] at h1
        have h2 := congrArg Subtype.val h1
        simpa using h2
      have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      obtain ⟨c, hc8, hce, hmod, hcard⟩ := key 7 2 (by decide) _ hg1 hgp
      have hc2 : c = 2 := by
        interval_cases c <;> first | rfl | (exfalso; revert hce hmod; decide)
      rw [hcard, hc2]
      norm_num
    classical
    have : Fintype E := Fintype.ofFinite E
    let act : E →* Module.End (ZMod 2) V := ρ.comp E.subtype
    let _ : MulAction E V := MulAction.compHom V act
    have hsmul : ∀ (g : E) (v : V), g • v = ρ (g : MulAut Q) v := fun g v => rfl
    have hfc : ∀ g : E, Nat.card (MulAction.fixedBy V g) =
        Nat.card {v : V // ρ (g : MulAut Q) v = v} :=
      fun g => Nat.card_congr (Equiv.subtypeEquivRight fun v => by
        rw [MulAction.mem_fixedBy, hsmul])
    have : ∀ g : E, Fintype (MulAction.fixedBy V g) := fun g => Fintype.ofFinite _
    have : Fintype (Quotient (MulAction.orbitRel E V)) := Fintype.ofFinite _
    have burn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group E V
    have hE' : Fintype.card E = 49 := by rw [Fintype.card_eq_nat_card, hE]
    have hsum : ∑ g : E, Fintype.card (MulAction.fixedBy V g) = 256 + 48 * 4 := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (1 : E))]
      congr 1
      · rw [Fintype.card_eq_nat_card, hfc]
        have : Nat.card {v : V // ρ ((1 : E) : MulAut Q) v = v} = Nat.card V := by
          refine Nat.card_congr (Equiv.subtypeUnivEquiv fun v => ?_)
          simp
        rw [this, hV]
        norm_num
      · calc ∑ g ∈ Finset.univ.erase (1 : E), Fintype.card (MulAction.fixedBy V g)
            = ∑ g ∈ Finset.univ.erase (1 : E), 4 := by
              refine Finset.sum_congr rfl fun g hg => ?_
              rw [Fintype.card_eq_nat_card, hfc]
              exact h4 g (Finset.ne_of_mem_erase hg)
          _ = 48 * 4 := by
              rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
                Finset.card_univ, hE']
              rfl
    rw [hsum, hE'] at burn
    omega

end CFSG.Quasithin
