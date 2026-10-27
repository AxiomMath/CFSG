module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.Assembly.Defs
import CFSG.CharacterTheory.Semidihedral.ElementaryActionTransport
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
import CFSG.GH74.Filter.Small.Eigenbasis
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBK

open Subgroup CFSG
open scoped IsMulCommutative

theorem exists_common_eigenbasis {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) {Q J : Type*} [Group Q]
    [Finite Q] [IsElementaryAbelian r Q] [Group J] [Finite J] (ρ : J →* MulAut Q)
    (hcomm : ∀ a b : J, a * b = b * a) (hsq : ∀ a : J, a ^ 2 = 1) :
    ∃ (e : ℕ) (w : Fin e → Q) (μ : J → Fin e → ZMod r), Nat.card Q = r ^ e ∧
      (∀ a i, ρ a (w i) = w i ^ (μ a i).val) ∧ (∀ a i, μ a i = 1 ∨ μ a i = -1) ∧
      (∀ i, w i ≠ 1) ∧ ∀ σ τ : MulAut Q, (∀ i, σ (w i) = τ (w i)) → σ = τ := by
  classical
  have hr : r.Prime := Fact.out
  have h2 : (2 : ZMod r) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod r) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h')
  have : Module.Finite (ZMod r) (Additive Q) := Module.Finite.of_finite
  set F := CFSG.Semidihedral.ElementaryActionTransport.primeFieldAction (p := r) ρ with hF
  let f : J → Module.End (ZMod r) (Additive Q) := fun a => (F a : Module.End _ _)
  have hfc : ∀ a b, Commute (f a) (f b) := fun a b => by
    change (F a : Module.End (ZMod r) (Additive Q)) * (F b : Module.End (ZMod r) (Additive Q)) =
      (F b : Module.End (ZMod r) (Additive Q)) * (F a : Module.End (ZMod r) (Additive Q))
    rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, hcomm]
  have hfs : ∀ a, f a ^ 2 = 1 := fun a => by
    change (F a : Module.End (ZMod r) (Additive Q)) ^ 2 = 1
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hsq, map_one, Units.val_one]
  obtain ⟨b, μ, hb⟩ := CFSG.GH74.Filter.exists_basis_common_eigenvectors_of_sq_eq_one h2 f hfc hfs
  refine ⟨Module.finrank (ZMod r) (Additive Q), fun i => Additive.toMul (b i), μ, ?_, ?_, ?_, ?_,
    ?_⟩
  · have := Module.natCard_eq_pow_finrank (K := ZMod r) (V := Additive Q)
    rwa [Nat.card_zmod] at this
  · intro a i
    have h := hb a i
    apply Additive.ofMul.injective
    have h1 : f a (b i) = Additive.ofMul (ρ a (Additive.toMul (b i))) := rfl
    rw [← h1, h, ofMul_pow, ofMul_toMul, ← Nat.cast_smul_eq_nsmul (ZMod r), ZMod.natCast_zmod_val]
  · intro a i
    have h1 : (f a ^ 2) (b i) = b i := by rw [hfs, Module.End.one_apply]
    rw [sq, Module.End.mul_apply, hb, map_smul, hb, smul_smul] at h1
    have h3 : (μ a i * μ a i - 1) • b i = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    exact mul_self_eq_one_iff.mp (sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right (b.ne_zero i)))
  · intro i h
    apply b.ne_zero i
    have h' : Additive.toMul (b i) = 1 := h
    rw [← ofMul_toMul (b i), h', ofMul_one]
  · intro σ τ h
    have h1 : CFSG.Semidihedral.ElementaryActionTransport.autToGL (p := r) σ =
        CFSG.Semidihedral.ElementaryActionTransport.autToGL (p := r) τ := by
      apply Units.ext
      apply b.ext
      intro i
      have hσ := CFSG.Semidihedral.ElementaryActionTransport.autToGL_apply (p := r) σ
        (Additive.toMul (b i))
      have hτ := CFSG.Semidihedral.ElementaryActionTransport.autToGL_apply (p := r) τ
        (Additive.toMul (b i))
      rw [ofMul_toMul] at hσ hτ
      rw [hσ, hτ, h i]
    exact CFSG.Semidihedral.ElementaryActionTransport.autToGL_injective h1

open CFSG.Semidihedral.Principal.CoprimeFixedPoint (quotientAction quotientAction_mk) in
theorem elementary_two_action_class_two_global_odd_rank_bound {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) {D A : Type*} [Group D] [Finite D] [Group A] [Finite A]
    [MulDistribMulAction A D] (hDexp : ∀ x : D, x ^ r = 1) (hDcl : commutator D ≤ center D)
    (hAcomm : ∀ a b : A, a * b = b * a) (hAsq : ∀ a : A, a ^ 2 = 1)
    (hfaith : ∀ a : A, (∀ x : D, a • x = x) → a = 1) :
    CFSG.Assembly.pRank 2 (⊤ : Subgroup A) ≤ CFSG.Assembly.pRank r (⊤ : Subgroup D) := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have hcz : ∀ x y : D, x * y * x⁻¹ * y⁻¹ ∈ center D := fun x y => by
    apply hDcl
    rw [commutator_def, ← commutatorElement_def]
    exact commutator_mem_commutator (mem_top x) (mem_top y)
  have hZinv : ∀ a : A, ∀ z ∈ center D, a • z ∈ center D := by
    intro a z hz
    rw [mem_center_iff] at hz ⊢
    intro y
    have h := hz (a⁻¹ • y)
    have h' := congrArg (a • ·) h
    simpa [smul_mul', smul_inv_smul] using h'
  set S : Set (Subgroup D) := {U | center D ≤ U ∧ (∀ a : A, ∀ u ∈ U, a • u ∈ U) ∧
    ∀ u ∈ U, ∀ v ∈ U, u * v = v * u} with hS
  have hZS : center D ∈ S := ⟨le_rfl, hZinv, fun u hu v _ => (mem_center_iff.mp hu v).symm⟩
  obtain ⟨U, hUmax⟩ := (Set.toFinite S).exists_maximal ⟨center D, hZS⟩
  obtain ⟨hZU, hUinv, hUcomm⟩ := hUmax.prop
  set C := centralizer (U : Set D) with hC
  have hUC : U ≤ C := fun u hu => mem_centralizer_iff.mpr fun v hv => hUcomm v hv u hu
  have hCinv : ∀ a : A, ∀ c ∈ C, a • c ∈ C := by
    intro a c hc
    rw [mem_centralizer_iff] at hc ⊢
    intro u hu
    have h := hc (a⁻¹ • u) (hUinv a⁻¹ u hu)
    have h' := congrArg (a • ·) h
    simpa [smul_mul', smul_inv_smul] using h'
  have hCU : C ≤ U := by
    by_contra hCU
    obtain ⟨c, hcC, hcU⟩ := Set.not_subset.mp hCU
    have : IsInvariant A D C :=
      ⟨fun a g => ⟨hCinv a g, fun h => by simpa using hCinv a⁻¹ _ h⟩⟩
    have hUn : (U.subgroupOf C).Normal := by
      rw [normal_subgroupOf_iff hUC]
      intro h k hh hk
      rw [mem_centralizer_iff] at hk
      rw [← hk h hh, mul_inv_cancel_right]
      exact hh
    have hQcomm : ∀ s t : C ⧸ U.subgroupOf C, s * t = t * s := by
      intro s t
      obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective s
      obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective t
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
      have h := hZU (hcz (t : D)⁻¹ (s : D)⁻¹)
      simpa [mul_assoc] using h
    have hQexp : ∀ s : C ⧸ U.subgroupOf C, s ^ r = 1 := by
      intro s
      obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective s
      rw [← QuotientGroup.mk_pow, show s ^ r = 1 from Subtype.ext (hDexp s), QuotientGroup.mk_one]
    have : IsElementaryAbelian r (C ⧸ U.subgroupOf C) :=
      { toIsMulCommutative := ⟨⟨hQcomm⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hQexp }
    let αC : A →* MulAut C := MulDistribMulAction.toMulAut A C
    have hUαC : ∀ a : A, ∀ n ∈ U.subgroupOf C, αC a n ∈ U.subgroupOf C :=
      fun a n hn => hUinv a n hn
    obtain ⟨e, w, μ, hQcard, hρw, -, hw1, -⟩ :=
      exists_common_eigenbasis hr2 (quotientAction αC (U.subgroupOf C) hUαC) hAcomm hAsq
    have he : 0 < e := by
      rcases Nat.eq_zero_or_pos e with h0 | h0
      · exfalso
        rw [h0, pow_zero] at hQcard
        have h1 : (QuotientGroup.mk ⟨c, hcC⟩ : C ⧸ U.subgroupOf C) = 1 :=
          (Nat.card_eq_one_iff_unique.mp hQcard).1.elim _ _
        rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
        exact hcU h1
      · exact h0
    obtain ⟨c0, hc0⟩ := QuotientGroup.mk_surjective (w ⟨0, he⟩)
    have hxU : (c0 : D) ∉ U := by
      intro h
      apply hw1 ⟨0, he⟩
      rw [← hc0, QuotientGroup.eq_one_iff, mem_subgroupOf]
      exact h
    set X := U ⊔ zpowers (c0 : D) with hX
    have hxinv : ∀ a : A, a • (c0 : D) ∈ X := by
      intro a
      have h := hρw a ⟨0, he⟩
      rw [← hc0, quotientAction_mk, ← QuotientGroup.mk_pow, QuotientGroup.eq,
        mem_subgroupOf] at h
      have h' : a • (c0 : D) = (c0 : D) ^ (μ a ⟨0, he⟩).val *
          (((c0 : D) ^ (μ a ⟨0, he⟩).val)⁻¹ * (a • (c0 : D))) := by group
      rw [h']
      refine mul_mem (mem_sup_right (pow_mem (mem_zpowers _) _)) (mem_sup_left ?_)
      have h2 := inv_mem h
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, mul_inv_rev, inv_inv] at h2
      exact h2
    have hXc : X ≤ centralizer (X : Set D) := by
      have hxU' : zpowers (c0 : D) ≤ centralizer (U : Set D) := zpowers_le.mpr c0.2
      have h1 : U ≤ centralizer (X : Set D) := by
        rw [le_centralizer_iff]
        exact sup_le hUC hxU'
      have h2 : zpowers (c0 : D) ≤ centralizer (X : Set D) := by
        rw [le_centralizer_iff]
        refine sup_le ?_ ?_
        · rw [← le_centralizer_iff]
          exact hxU'
        · exact le_centralizer_iff_isMulCommutative.mpr inferInstance
      exact sup_le h1 h2
    have hXS : X ∈ S := by
      refine ⟨hZU.trans le_sup_left, fun a y hy => ?_, fun u hu v hv =>
        mem_centralizer_iff.mp (hXc hv) u hu⟩
      have hle : X ≤ X.comap (MulDistribMulAction.toMulAut A D a).toMonoidHom :=
        sup_le (fun u hu => mem_sup_left (hUinv a u hu)) (zpowers_le.mpr (hxinv a))
      exact hle hy
    exact hxU (hUmax.2 hXS le_sup_left (mem_sup_right (mem_zpowers _)))
  have hfaithU : ∀ a : A, (∀ u ∈ U, a • u = u) → a = 1 := by
    intro a ha
    refine hfaith a fun x => ?_
    set n := x⁻¹ * (a • x) with hn
    have hnC : n ∈ C := by
      rw [mem_centralizer_iff]
      intro u hu
      have hc := hZU (hcz x u)
      have h1 := ha _ hc
      simp only [smul_mul', smul_inv'] at h1
      rw [ha u hu] at h1
      have h2 : (a • x) * u * (a • x)⁻¹ = x * u * x⁻¹ := by
        have := congrArg (· * u) h1
        simpa [mul_assoc] using this
      calc u * n = x⁻¹ * (x * u * x⁻¹) * (a • x) := by rw [hn]; group
        _ = x⁻¹ * ((a • x) * u * (a • x)⁻¹) * (a • x) := by rw [h2]
        _ = n * u := by rw [hn]; group
    have hnU := hCU hnC
    have hax : a • x = x * n := by rw [hn, mul_inv_cancel_left]
    have h2 : a • (a • x) = x := by
      rw [← mul_smul, ← sq, hAsq, one_smul]
    rw [hax, smul_mul', ha n hnU, hax, mul_assoc] at h2
    have hn2 : n ^ 2 = 1 := by
      rw [sq]
      exact mul_left_cancel (h2.trans (mul_one x).symm)
    have hn1 : n = 1 := by
      have h : n ^ Nat.gcd 2 r = 1 := pow_gcd_eq_one.mpr ⟨hn2, hDexp n⟩
      rwa [(Nat.coprime_primes Nat.prime_two hr).mpr hr2.symm, pow_one] at h
    rw [hax, hn1, mul_one]
  have : IsInvariant A D U :=
    ⟨fun a g => ⟨hUinv a g, fun h => by simpa using hUinv a⁻¹ _ h⟩⟩
  let αU : A →* MulAut U := MulDistribMulAction.toMulAut A U
  have hαU : Function.Injective αU := by
    rw [injective_iff_map_eq_one]
    intro a ha
    refine hfaithU a fun u hu => ?_
    have h := congrArg Subtype.val (DFunLike.congr_fun ha (⟨u, hu⟩ : U))
    exact h
  have : IsElementaryAbelian r U :=
    { toIsMulCommutative := ⟨⟨fun u v => Subtype.ext (hUcomm u u.2 v v.2)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun u =>
        Subtype.ext (hDexp u) }
  obtain ⟨e, w, μ, hUcard, hρw, hμ, -, hgen⟩ := exists_common_eigenbasis hr2 αU hAcomm hAsq
  have hAcard : Nat.card A ≤ 2 ^ e := by
    let T : Finset (ZMod r) := {1, -1}
    have hT : Fintype.card T ≤ 2 := by
      rw [Fintype.card_coe]
      exact Finset.card_le_two
    let φ : A → (Fin e → T) := fun a i =>
      ⟨μ a i, by rcases hμ a i with h | h <;> simp [T, h]⟩
    have hφ : Function.Injective φ := by
      intro a b hab
      refine hαU (hgen _ _ fun i => ?_)
      have h := congrArg Subtype.val (congrFun hab i)
      change μ a i = μ b i at h
      rw [hρw, hρw, h]
    calc Nat.card A ≤ Nat.card (Fin e → T) := Nat.card_le_card_of_injective φ hφ
      _ = Fintype.card T ^ e := by
        rw [Nat.card_fun, Nat.card_eq_fintype_card (α := T), Nat.card_eq_fintype_card (α := Fin e),
          Fintype.card_fin]
      _ ≤ 2 ^ e := Nat.pow_le_pow_left hT e
  have hUel : CFSG.Assembly.IsElemAbelian r U :=
    ⟨⟨⟨fun u v => Subtype.ext (hUcomm u u.2 v v.2)⟩⟩, fun u _ => hDexp u⟩
  have h1 : e ≤ CFSG.Assembly.pRank r (⊤ : Subgroup D) :=
    CFSG.SectionRank.le_pRank hr.one_lt le_top hUel hUcard
  have h2 : CFSG.Assembly.pRank 2 (⊤ : Subgroup A) ≤ e :=
    CFSG.SectionRank.pRank_le (by norm_num) fun E _ _ =>
      (Subgroup.card_le_card_group E).trans hAcard
  exact h2.trans h1

end CFSG.RankThree.GroupTheory.SteinbergBK
