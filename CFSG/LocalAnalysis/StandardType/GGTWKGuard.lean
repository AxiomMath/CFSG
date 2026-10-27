module

public import CFSG.LocalAnalysis.StandardType.GGTWHLCover
public import CFSG.LocalAnalysis.StandardType.GGTWLowOf
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepFrame
public import CFSG.LocalAnalysis.StandardType.GGTWPat2Base
public import CFSG.LocalAnalysis.StandardType.GGRowKFrameDim

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nG1_A_adj (N : ℕ) (hN : 5 ≤ N) (a b : Fin (N - 3)) :
    (CartanMatrix.A (N - 1)) (ggTWPat2_xiA N a).1 (ggTWPat2_xiA N b).1 =
      (CartanMatrix.A (N - 3)) a b := by
  have ha : (ggTWPat2_xiA N a).1 = ⟨a.val, by omega⟩ := Fin.ext rfl
  have hb : (ggTWPat2_xiA N b).1 = ⟨b.val, by omega⟩ := Fin.ext rfl
  rw [ha, hb]
  simp only [CartanMatrix.A, Matrix.of_apply, Fin.mk.injEq]
  split_ifs <;> omega

private theorem l05nG1_A_ends (N : ℕ) (hN : 5 ≤ N) (a b : Fin (N - 3)) :
    (CartanMatrix.A (N - 1)) (ggTWPat2_xiE N a).1 (ggTWPat2_xiE N b).1 =
      (CartanMatrix.A (N - 3)) a b := by
  have ha : (ggTWPat2_xiE N a).1 = ⟨a.val + 1, by omega⟩ := Fin.ext rfl
  have hb : (ggTWPat2_xiE N b).1 = ⟨b.val + 1, by omega⟩ := Fin.ext rfl
  rw [ha, hb]
  simp only [CartanMatrix.A, Matrix.of_apply, Fin.mk.injEq]
  split_ifs <;> omega

theorem ggTWHKGuard_holds (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) : GGTWHKGuard := by
  intro G _ _ p N k _ B Bs x L D J y K hH hxL hk hp hpN hN hcard hA
  classical
  obtain ⟨pos, Λ, hΛf, hΛd, b₁, b₂, Λa, hΛaf, hΛad, ML, CL, MK, CK, V, hVadd, hVmod,
    ι, φ, h, α, e, hb12, hcardΛa, hpos, hMLeq, hMLweyl, hCLcartan, hMKweyl, hCKcartan,
    hk2, hform, hrefl, hpairL, hpairK, hAL, hAK, hAJ⟩ := hA
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod p) V := hVmod
  letI : Fintype Λ := hΛf
  letI : DecidableEq Λ := hΛd
  letI : Fintype Λa := hΛaf
  letI : DecidableEq Λa := hΛad
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hp2 : p ≠ 2 := by omega
  have hN5 : 5 ≤ N := by rcases hN with h' | h' | h' <;> omega
  have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hy : y ∈ Bs := hH.1.2.1.1 hH.2.2.2.2.1.1.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hH.1.tableB_facts.2.2.2.1
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hH.2.2.2.2.1.1.2.2.2.1
  let xV : V := ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs))
  let yV : V := ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))
  let ΦK : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} ⊕ Λa → MulAut ↥Bs := fun o => φ (o.map Subtype.val id)
  have hAKrange : Set.range ΦK =
      Set.range (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j.1)) ∪
        Set.range (fun a : Λa => φ (Sum.inr a)) := by
    ext z
    constructor
    · rintro ⟨o, rfl⟩
      cases o with
      | inl j => exact Or.inl ⟨j, rfl⟩
      | inr a => exact Or.inr ⟨a, rfl⟩
    · rintro (⟨j, rfl⟩ | ⟨a, rfl⟩)
      · exact ⟨Sum.inl j, rfl⟩
      · exact ⟨Sum.inr a, rfl⟩
  have hAK' : ggAutomizer K Bs = Subgroup.closure (Set.range ΦK) := by
    rw [hAK, ← hAKrange]
  have hfixx : ∀ ψ ∈ ggAutomizer L Bs, ψ ⟨x, hx⟩ = ⟨x, hx⟩ :=
    ggRC_automizer_fixes_y hx hLx
  have hαLx : ∀ i : Λ, α (Sum.inl i) xV = 0 := by
    intro i
    have hmem : φ (Sum.inl i) ∈ ggAutomizer L Bs := by
      rw [hAL]
      exact Subgroup.subset_closure ⟨i, rfl⟩
    have hfixi := hfixx (φ (Sum.inl i)) hmem
    have hlin := (ggLin_fix_iff (p := p) ι (φ (Sum.inl i)) (⟨x, hx⟩ : ↥Bs)).mp hfixi
    have h1 := hform (Sum.inl i) xV
    rw [hlin] at h1
    have h2 : α (Sum.inl i) xV • h (Sum.inl i) = 0 := sub_eq_self.mp h1.symm
    have h3 : α (Sum.inl i) (α (Sum.inl i) xV • h (Sum.inl i)) = 0 := by rw [h2, map_zero]
    rw [map_smul, smul_eq_mul, hpairL i i, hCLcartan.1 i] at h3
    have h2ne : ((2 : ℤ) : ZMod p) ≠ 0 := by
      simpa using (zmod_two_ne_zero (p := p) hp2)
    exact (mul_eq_zero.mp h3).resolve_right h2ne
  have hfixy : ∀ ψ ∈ ggAutomizer K Bs, ψ ⟨y, hy⟩ = ⟨y, hy⟩ :=
    ggRC_automizer_fixes_y hy hKy
  have hαKy : ∀ o : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} ⊕ Λa, α (o.map Subtype.val id) yV = 0 := by
    intro o
    have hmem : φ (o.map Subtype.val id) ∈ ggAutomizer K Bs := by
      rw [hAK']
      exact Subgroup.subset_closure ⟨o, rfl⟩
    have hfixo := hfixy (φ (o.map Subtype.val id)) hmem
    have hlin := (ggLin_fix_iff (p := p) ι (φ (o.map Subtype.val id)) (⟨y, hy⟩ : ↥Bs)).mp hfixo
    have h1 := hform (o.map Subtype.val id) yV
    rw [hlin] at h1
    have h2 : α (o.map Subtype.val id) yV • h (o.map Subtype.val id) = 0 :=
      sub_eq_self.mp h1.symm
    have h3 : α (o.map Subtype.val id)
        (α (o.map Subtype.val id) yV • h (o.map Subtype.val id)) = 0 := by rw [h2, map_zero]
    rw [map_smul, smul_eq_mul, hpairK o o, hCKcartan.1 o] at h3
    have h2ne : ((2 : ℤ) : ZMod p) ≠ 0 := by
      simpa using (zmod_two_ne_zero (p := p) hp2)
    exact (mul_eq_zero.mp h3).resolve_right h2ne
  have hyV0 : yV ≠ 0 := by
    intro hy0
    apply ggRC_y_ne_one hH
    have h1 : Additive.ofMul (⟨y, hy⟩ : ↥Bs) = 0 := by
      apply ι.injective
      simpa only [yV, map_zero] using hy0
    have h2 : (⟨y, hy⟩ : ↥Bs) = 1 := by
      simpa using congrArg Additive.toMul h1
    exact congrArg Subtype.val h2
  have hexa : ∃ a : Λa, α (Sum.inr a) xV ≠ 0 := by
    by_contra hno
    push Not at hno
    have hfixgen : ∀ o : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} ⊕ Λa,
        φ (o.map Subtype.val id) ⟨x, hx⟩ = ⟨x, hx⟩ := by
      intro o
      apply (ggLin_fix_iff (p := p) ι (φ (o.map Subtype.val id)) (⟨x, hx⟩ : ↥Bs)).mpr
      cases o with
      | inl j =>
          show ggLin (p := p) ι (φ (Sum.inl j.1)) xV = xV
          rw [hform (Sum.inl j.1) xV, hαLx j.1, zero_smul, sub_zero]
      | inr a =>
          show ggLin (p := p) ι (φ (Sum.inr a)) xV = xV
          rw [hform (Sum.inr a) xV, hno a, zero_smul, sub_zero]
    have hfix : ∀ ψ ∈ ggAutomizer K Bs, ψ ⟨x, hx⟩ = ⟨x, hx⟩ := by
      intro ψ hψ
      rw [hAK'] at hψ
      exact ggFixed_of_mem_closure ΦK (⟨x, hx⟩ : ↥Bs) hfixgen ψ hψ
    exact ggTT_not_fixed hFixK hH hx hfix
  have hcartan : ∀ i j : Fin (N - 1), CL (e i) (e j) = CartanMatrix.A (N - 1) i j :=
    ggIndep_cartan_of_reindex (m := N - 1) e hCLcartan hMLeq
  have hpairJ : ∃ eS : Fin (N - 3) ≃ {j : Λ // j ≠ b₁ ∧ j ≠ b₂},
      ∀ a b : Fin (N - 3),
        α (Sum.inl (eS a).1) (h (Sum.inl (eS b).1)) = (CartanMatrix.A (N - 3) a b : ZMod p) := by
    cases pos with
    | adj =>
        refine ⟨(ggTWPat2_xiA N).trans
          (Equiv.subtypeEquiv (q := fun j : Λ => j ≠ b₁ ∧ j ≠ b₂) e hpos), ?_⟩
        intro a b
        have ha : (((ggTWPat2_xiA N).trans
            (Equiv.subtypeEquiv (q := fun j : Λ => j ≠ b₁ ∧ j ≠ b₂) e hpos)) a).1 =
            e ((ggTWPat2_xiA N a).1) := by
          simp only [Equiv.trans_apply, Equiv.subtypeEquiv_apply]
        have hb : (((ggTWPat2_xiA N).trans
            (Equiv.subtypeEquiv (q := fun j : Λ => j ≠ b₁ ∧ j ≠ b₂) e hpos)) b).1 =
            e ((ggTWPat2_xiA N b).1) := by
          simp only [Equiv.trans_apply, Equiv.subtypeEquiv_apply]
        rw [ha, hb, hpairL, hcartan, l05nG1_A_adj N hN5 a b]
    | ends =>
        refine ⟨(ggTWPat2_xiE N).trans
          (Equiv.subtypeEquiv (q := fun j : Λ => j ≠ b₁ ∧ j ≠ b₂) e hpos), ?_⟩
        intro a b
        have ha : (((ggTWPat2_xiE N).trans
            (Equiv.subtypeEquiv (q := fun j : Λ => j ≠ b₁ ∧ j ≠ b₂) e hpos)) a).1 =
            e ((ggTWPat2_xiE N a).1) := by
          simp only [Equiv.trans_apply, Equiv.subtypeEquiv_apply]
        have hb : (((ggTWPat2_xiE N).trans
            (Equiv.subtypeEquiv (q := fun j : Λ => j ≠ b₁ ∧ j ≠ b₂) e hpos)) b).1 =
            e ((ggTWPat2_xiE N b).1) := by
          simp only [Equiv.trans_apply, Equiv.subtypeEquiv_apply]
        rw [ha, hb, hpairL, hcartan, l05nG1_A_ends N hN5 a b]
  obtain ⟨eS, hpairJ⟩ := hpairJ
  have hfinrank : Module.finrank (ZMod p) V = N - 1 := by
    haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
    have hVcard : Nat.card V = p ^ Module.finrank (ZMod p) V := by
      have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
      rwa [Nat.card_zmod] at h
    have hcardV : Nat.card V = Nat.card ↥Bs := by
      rw [Nat.card_congr (Additive.ofMul (α := ↥Bs))]
      exact (Nat.card_congr ι.toEquiv).symm
    have heq : p ^ Module.finrank (ZMod p) V = p ^ (N - 1) := by
      rw [← hVcard, hcardV, hcard]
    exact Nat.pow_right_injective (Fact.out : p.Prime).two_le heq
  have hdet : ((CartanMatrix.A (N - 3)).map (fun x : ℤ => (x : ZMod p))).det ≠ 0 := by
    rw [← Int.cast_det, CartanMatrix.A_det]
    intro hz
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
    have hpZ : (p : ℤ) ∣ (N : ℤ) := by exact_mod_cast hpN
    have h2 : (p : ℤ) ∣ (2 : ℤ) := by
      have hsub := dvd_sub hpZ hz
      have heq : (N : ℤ) - (((N - 3 : ℕ) : ℤ) + 1) = 2 := by omega
      rwa [heq] at hsub
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp
      (Int.natCast_dvd_natCast.1 h2))
  let T : V →ₗ[ZMod p] ({j : Λ // j ≠ b₁ ∧ j ≠ b₂} ⊕ Λa → ZMod p) :=
    { toFun := fun v o => α (o.map Subtype.val id) v
      map_add' := by intro u v; ext o; simp
      map_smul' := by intro c v; ext o; simp }
  have hkerfin : Module.finrank (ZMod p) (LinearMap.ker T) ≤ 1 := by
    haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
    have hrn := LinearMap.finrank_range_add_finrank_ker (f := T)
    rw [hfinrank] at hrn
    have hrange : N - 2 ≤ Module.finrank (ZMod p) (LinearMap.range T) := by
      let Mm : Matrix ({j : Λ // j ≠ b₁ ∧ j ≠ b₂} ⊕ Λa) (Option (Fin (N - 3))) (ZMod p) :=
        fun o i => match i with
          | some a => α (o.map Subtype.val id) (h (Sum.inl (eS a).1))
          | none => α (o.map Subtype.val id) xV
      let Ψ : (Option (Fin (N - 3)) → ZMod p) →ₗ[ZMod p]
          ({j : Λ // j ≠ b₁ ∧ j ≠ b₂} ⊕ Λa → ZMod p) := Mm.mulVecLin
      have hΨzero : ∀ d : Option (Fin (N - 3)) → ZMod p, Ψ d = 0 → d = 0 := by
        intro d hd
        have hJmul : ((CartanMatrix.A (N - 3)).map (fun x : ℤ => (x : ZMod p))).mulVec
            (fun a : Fin (N - 3) => d (some a)) = 0 := by
          ext b
          rw [Matrix.mulVec_apply_eq_sum, Pi.zero_apply]
          have hb := congrFun hd (Sum.inl (eS b))
          rw [Matrix.mulVecLin_apply, Matrix.mulVec_apply_eq_sum, Fintype.sum_option] at hb
          simpa [Mm, Matrix.map_apply, hαLx (eS b).1, hpairJ b] using hb
        have hd' : (fun a : Fin (N - 3) => d (some a)) = 0 :=
          Matrix.eq_zero_of_mulVec_eq_zero hdet hJmul
        have hd'a : ∀ a : Fin (N - 3), d (some a) = 0 := fun a => by
          have := congrFun hd' a
          simpa using this
        obtain ⟨a₀, ha₀⟩ := hexa
        have hdnone : d none = 0 := by
          have h0 := congrFun hd (Sum.inr a₀)
          rw [Matrix.mulVecLin_apply, Matrix.mulVec_apply_eq_sum, Fintype.sum_option] at h0
          have hsum0 : (∑ a : Fin (N - 3), Mm (Sum.inr a₀) (some a) * d (some a)) = 0 := by
            apply Finset.sum_eq_zero
            intro a _
            rw [hd'a a, mul_zero]
          rw [hsum0, add_zero] at h0
          have hMm : Mm (Sum.inr a₀) none = α (Sum.inr a₀) xV := rfl
          rw [hMm, Pi.zero_apply, mul_eq_zero] at h0
          rcases h0 with h | h
          · exact absurd h ha₀
          · exact h
        funext i
        cases i with
        | none => exact hdnone
        | some a => exact hd'a a
      have hΨker : LinearMap.ker Ψ = ⊥ := by
        rw [LinearMap.ker_eq_bot]
        intro d e hde
        have h0 : Ψ (d - e) = 0 := by rw [map_sub, hde, sub_self]
        exact sub_eq_zero.mp (hΨzero (d - e) h0)
      have hΨrank : Module.finrank (ZMod p) (LinearMap.range Ψ) = N - 2 := by
        have hrnΨ := LinearMap.finrank_range_add_finrank_ker (f := Ψ)
        rw [hΨker, finrank_bot] at hrnΨ
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_option, Fintype.card_fin] at hrnΨ
        omega
      have hΨrange : LinearMap.range Ψ ≤ LinearMap.range T := by
        rintro x ⟨d, rfl⟩
        rw [Matrix.mulVecLin_apply]
        rw [show Mm.mulVec d = ∑ i : Option (Fin (N - 3)), d i • (fun o => Mm o i) by
          ext o
          rw [Matrix.mulVec_apply_eq_sum, Finset.sum_apply]
          exact Finset.sum_congr rfl fun i _ => by
            rw [Pi.smul_apply, smul_eq_mul, mul_comm]]
        refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
        cases i with
        | none => exact ⟨xV, by ext o; rfl⟩
        | some a => exact ⟨h (Sum.inl (eS a).1), by ext o; rfl⟩
      calc N - 2 = Module.finrank (ZMod p) (LinearMap.range Ψ) := hΨrank.symm
        _ ≤ Module.finrank (ZMod p) (LinearMap.range T) := Submodule.finrank_mono hΨrange
    omega
  have hfix : ∀ v : V, (∀ o : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} ⊕ Λa,
      α (o.map Subtype.val id) v = 0) → v ∈ Submodule.span (ZMod p) ({yV} : Set V) := by
    intro v hv
    have hvker : v ∈ LinearMap.ker T := by
      rw [LinearMap.mem_ker]
      ext o
      exact hv o
    have hyker : yV ∈ LinearMap.ker T := by
      rw [LinearMap.mem_ker]
      ext o
      exact hαKy o
    have hspanle : Submodule.span (ZMod p) ({yV} : Set V) ≤ LinearMap.ker T := by
      rw [Submodule.span_le]
      rintro w (rfl : w = yV)
      exact hyker
    have hfin_ge : 1 ≤ Module.finrank (ZMod p) (LinearMap.ker T) := by
      calc 1 = Module.finrank (ZMod p) (Submodule.span (ZMod p) ({yV} : Set V)) :=
            (finrank_span_singleton hyV0).symm
        _ ≤ Module.finrank (ZMod p) (LinearMap.ker T) := Submodule.finrank_mono hspanle
    have hfin : Module.finrank (ZMod p) (LinearMap.ker T) = 1 := le_antisymm hkerfin hfin_ge
    have heq : LinearMap.ker T = Submodule.span (ZMod p) ({yV} : Set V) :=
      eq_span_singleton_of_mem_of_finrank_eq_one hfin hyker hyV0
    rw [heq] at hvker
    exact hvker
  refine ggNbr_cent_le_of_fix (p := p) hp2 (Bs := Bs) (K := K) (y := y) hy (ι := ι)
    (φ := ΦK) (h := fun o : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} ⊕ Λa => h (o.map Subtype.val id))
    (α := fun o => α (o.map Subtype.val id)) ?_ ?_ hAK' ?_
  · intro o w
    exact hform (o.map Subtype.val id) w
  · intro o
    rw [hpairK o o, hCKcartan.1 o]
    norm_num
  · intro v hv
    exact hfix v hv

end CFSG.StandardType

end
