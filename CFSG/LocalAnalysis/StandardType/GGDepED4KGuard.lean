module

public import CFSG.LocalAnalysis.StandardType.GGDepED4PackDefs
public import CFSG.LocalAnalysis.StandardType.GGTWKGuard

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nGD_cartan_of_reindex {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} (e : Fin 6 ≃ Λ)
    (hCL : GGIntCartan ML CL) (hML : ML = CoxeterMatrix.E₆.reindex e) :
    ∀ i j : Fin 6, CL (e i) (e j) = CartanMatrix.E 6 i j := by
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [hCL.1]
    fin_cases i <;> decide
  · have heij : e i ≠ e j := fun h => hij (e.injective h)
    have h₂ : GGIntCartan ML (Matrix.reindex e e (CartanMatrix.E 6)) := by
      rw [hML]
      exact GGIntCartan.reindex e ggIntCartan_E₆
    have hMle : ML.M (e i) (e j) ≤ 3 := by
      rw [hML, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      fin_cases i <;> fin_cases j <;> decide
    have h1 := (hCL.pair h₂ heij).2 hMle
    rw [h1.1]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]

private def l05nGD_Eidx : Fin 4 → Fin 6 := fun a => ⟨a.val + 1, by omega⟩

private def l05nGD_DE : Matrix (Fin 4) (Fin 4) ℤ :=
  fun a b => CartanMatrix.E 6 (l05nGD_Eidx a) (l05nGD_Eidx b)

@[expose] def GGDepED4KGuard : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p k : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → p = 3 →
    Nat.card ↥Bs = 3 ^ 6 → x ∉ L → y ∉ K → (k = 1 ∨ k = 2) → GGDepED4Aligned p k Bs L J K →
    Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y

theorem ggDepED4KGuard_holds (hFixK : GGTBFixNbrInput) : GGDepED4KGuard := by
  intro G _ _ p k _ B Bs x L D J y K hH hp3 hcard hxL hyK hk hA
  classical
  obtain ⟨Λ, hΛf, hΛd, b₁, b₂, Λa, hΛaf, hΛad, ML, CL, MK, CK, V, hVadd, hVmod,
    ι, φ, h, α, e, hb1, hb2, hcardΛa, hML, hMLweyl, hCLcartan, hMKweyl, hCKcartan,
    hk2, hform, hrefl, hpairL, hpairK, hAL, hAK, hAJ⟩ := hA
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod p) V := hVmod
  letI : Fintype Λ := hΛf
  letI : DecidableEq Λ := hΛd
  letI : Fintype Λa := hΛaf
  letI : DecidableEq Λa := hΛad
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hp2 : p ≠ 2 := by omega
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
  have hcart : ∀ i j : Fin 6, CL (e i) (e j) = CartanMatrix.E 6 i j :=
    l05nGD_cartan_of_reindex e hCLcartan hML
  have hfinrank : Module.finrank (ZMod p) V = 6 := by
    haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
    have hVcard : Nat.card V = p ^ Module.finrank (ZMod p) V := by
      have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
      rwa [Nat.card_zmod] at h
    have hcardV : Nat.card V = Nat.card ↥Bs := by
      rw [Nat.card_congr (Additive.ofMul (α := ↥Bs))]
      exact (Nat.card_congr ι.toEquiv).symm
    have heq : p ^ Module.finrank (ZMod p) V = 3 ^ 6 := by
      rw [← hVcard, hcardV, hcard]
    have heq3 : 3 ^ Module.finrank (ZMod p) V = 3 ^ 6 := by
      simpa [hp3] using heq
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) heq3
  let Eidx : Fin 4 → Fin 6 := l05nGD_Eidx
  have hEidx0 : ∀ a, Eidx a ≠ 0 := by
    intro a h
    have := congrArg Fin.val h
    simp [Eidx, l05nGD_Eidx] at this
  have hEidx5 : ∀ a, Eidx a ≠ 5 := by
    intro a h
    have := congrArg Fin.val h
    simp [Eidx, l05nGD_Eidx] at this
    omega
  have hEidx_inj : Function.Injective Eidx := by
    intro a b hab
    apply Fin.ext
    have := congrArg Fin.val hab
    simp [Eidx, l05nGD_Eidx] at this
    omega
  have hbij : Function.Bijective
      (fun a : Fin 4 => (⟨e (Eidx a), by
        rw [hb1, hb2]
        exact ⟨fun h => hEidx0 a (e.injective h),
          fun h => hEidx5 a (e.injective h)⟩⟩ : {j : Λ // j ≠ b₁ ∧ j ≠ b₂})) := by
    constructor
    · intro a b hab
      exact hEidx_inj (e.injective (Subtype.ext_iff.mp hab))
    · intro j
      have hc0 : e.symm j.1 ≠ 0 := by
        intro hc
        apply j.2.1
        calc j.1 = e (e.symm j.1) := (Equiv.apply_symm_apply e j.1).symm
          _ = e 0 := by rw [hc]
          _ = b₁ := hb1.symm
      have hc5 : e.symm j.1 ≠ 5 := by
        intro hc
        apply j.2.2
        calc j.1 = e (e.symm j.1) := (Equiv.apply_symm_apply e j.1).symm
          _ = e 5 := by rw [hc]
          _ = b₂ := hb2.symm
      refine ⟨⟨(e.symm j.1).val - 1, by omega⟩, ?_⟩
      apply Subtype.ext
      have hEc : Eidx ⟨(e.symm j.1).val - 1, by omega⟩ = e.symm j.1 := by
        apply Fin.ext
        simp [Eidx, l05nGD_Eidx]
        omega
      simp only
      rw [hEc, Equiv.apply_symm_apply]
  let eS : Fin 4 ≃ {j : Λ // j ≠ b₁ ∧ j ≠ b₂} := Equiv.ofBijective _ hbij
  have hS : ∀ a, (eS a).1 = e (Eidx a) := fun a => rfl
  have hpairJ : ∀ a b : Fin 4,
      α (Sum.inl (eS a).1) (h (Sum.inl (eS b).1)) = (l05nGD_DE a b : ZMod p) := by
    intro a b
    rw [hS a, hS b, hpairL, hcart]
    rfl
  have hdet : (l05nGD_DE.map (fun x : ℤ => (x : ZMod p))).det ≠ 0 := by
    have hde : l05nGD_DE.det = 4 := by decide
    rw [← Int.cast_det, hde]
    intro hz
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
    have h4 : p ∣ 4 := by exact_mod_cast hz
    have h2 : p ∣ 2 := by
      have h4' : p ∣ 2 ^ 2 := by simpa using h4
      exact (Fact.out : p.Prime).dvd_of_dvd_pow h4'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 h2)
  let T : V →ₗ[ZMod p] ({j : Λ // j ≠ b₁ ∧ j ≠ b₂} ⊕ Λa → ZMod p) :=
    { toFun := fun v o => α (o.map Subtype.val id) v
      map_add' := by intro u v; ext o; simp
      map_smul' := by intro c v; ext o; simp }
  have hkerfin : Module.finrank (ZMod p) (LinearMap.ker T) ≤ 1 := by
    haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
    have hrn := LinearMap.finrank_range_add_finrank_ker (f := T)
    rw [hfinrank] at hrn
    have hrange : 5 ≤ Module.finrank (ZMod p) (LinearMap.range T) := by
      let Mm : Matrix ({j : Λ // j ≠ b₁ ∧ j ≠ b₂} ⊕ Λa) (Option (Fin 4)) (ZMod p) :=
        fun o i => match i with
          | some a => α (o.map Subtype.val id) (h (Sum.inl (eS a).1))
          | none => α (o.map Subtype.val id) xV
      let Ψ : (Option (Fin 4) → ZMod p) →ₗ[ZMod p]
          ({j : Λ // j ≠ b₁ ∧ j ≠ b₂} ⊕ Λa → ZMod p) := Mm.mulVecLin
      have hΨzero : ∀ d : Option (Fin 4) → ZMod p, Ψ d = 0 → d = 0 := by
        intro d hd
        have hJmul : (l05nGD_DE.map (fun x : ℤ => (x : ZMod p))).mulVec
            (fun a : Fin 4 => d (some a)) = 0 := by
          ext b
          rw [Matrix.mulVec_apply_eq_sum, Pi.zero_apply]
          have hb := congrFun hd (Sum.inl (eS b))
          rw [Matrix.mulVecLin_apply, Matrix.mulVec_apply_eq_sum, Fintype.sum_option] at hb
          simpa [Mm, Matrix.map_apply, hαLx (eS b).1, hpairJ b] using hb
        have hd' : (fun a : Fin 4 => d (some a)) = 0 :=
          Matrix.eq_zero_of_mulVec_eq_zero hdet hJmul
        have hd'a : ∀ a : Fin 4, d (some a) = 0 := fun a => by
          have := congrFun hd' a
          simpa using this
        obtain ⟨a₀, ha₀⟩ := hexa
        have hdnone : d none = 0 := by
          have h0 := congrFun hd (Sum.inr a₀)
          rw [Matrix.mulVecLin_apply, Matrix.mulVec_apply_eq_sum, Fintype.sum_option] at h0
          have hsum0 : (∑ a : Fin 4, Mm (Sum.inr a₀) (some a) * d (some a)) = 0 := by
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
      have hΨrank : Module.finrank (ZMod p) (LinearMap.range Ψ) = 5 := by
        have hrnΨ := LinearMap.finrank_range_add_finrank_ker (f := Ψ)
        rw [hΨker, finrank_bot] at hrnΨ
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_option, Fintype.card_fin] at hrnΨ
        omega
      have hΨrange : LinearMap.range Ψ ≤ LinearMap.range T := by
        rintro x ⟨d, rfl⟩
        rw [Matrix.mulVecLin_apply]
        rw [show Mm.mulVec d = ∑ i : Option (Fin 4), d i • (fun o => Mm o i) by
          ext o
          rw [Matrix.mulVec_apply_eq_sum, Finset.sum_apply]
          exact Finset.sum_congr rfl fun i _ => by
            rw [Pi.smul_apply, smul_eq_mul, mul_comm]]
        refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
        cases i with
        | none => exact ⟨xV, by ext o; rfl⟩
        | some a => exact ⟨h (Sum.inl (eS a).1), by ext o; rfl⟩
      calc 5 = Module.finrank (ZMod p) (LinearMap.range Ψ) := hΨrank.symm
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
