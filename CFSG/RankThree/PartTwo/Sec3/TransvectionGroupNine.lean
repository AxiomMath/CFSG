module

public import CFSG.RankThree.PartTwo.Sec3.QuaternionIrreducible
public import CFSG.RankThree.PartTwo.Sec3.TransvectionSylowCentralizer

public section

namespace CFSG.RankThree.PartTwo.Sec3

open Module CFSG.RankThree.Classical
open scoped MatrixGroups

variable {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]

theorem exists_eq_add_smul_of_center {r : V ≃ₗ[ZMod 3] V} {v u : V} {f : Dual (ZMod 3) V}
    (hr : IsTransvectionWith r v f)
    (hU : LinearMap.range ((r : V →ₗ[ZMod 3] V) - 1) = Submodule.span (ZMod 3) {u}) :
    ∃ f' : Dual (ZMod 3) V, f' u = 0 ∧ ∀ y, r y = y + f' y • u := by
  rw [range_sub_one_eq_span hr] at hU
  have hv : v ∈ Submodule.span (ZMod 3) {u} := by
    rw [← hU]; exact Submodule.mem_span_singleton_self v
  have hu : u ∈ Submodule.span (ZMod 3) {v} := by
    rw [hU]; exact Submodule.mem_span_singleton_self u
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hu
  refine ⟨c • f, ?_, fun y => ?_⟩
  · rw [LinearMap.smul_apply, ← hd, map_smul, hr.2.2.1, smul_zero, smul_zero]
  · rw [hr.2.2.2, ← hc, smul_smul, LinearMap.smul_apply, smul_eq_mul, mul_comm]

theorem conj_apply_eq {t g : V ≃ₗ[ZMod 3] V} {u : V} {f : Dual (ZMod 3) V}
    (ht : ∀ y, t y = y + f y • u) (y : V) : (g * t * g⁻¹) y = y + f (g⁻¹ y) • g u := by
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ht, map_add, map_smul]
  congr 1
  change g (g.symm y) = y
  exact g.apply_symm_apply y

theorem exists_dual_ne_zero_ne_zero {u a b : V} (ha : a ∉ Submodule.span (ZMod 3) {u})
    (hb : b ∉ Submodule.span (ZMod 3) {u}) :
    ∃ f : Dual (ZMod 3) V, f u = 0 ∧ f a ≠ 0 ∧ f b ≠ 0 := by
  obtain ⟨f₁, hf₁a, hf₁u⟩ := Submodule.exists_le_ker_of_notMem ha
  obtain ⟨f₂, hf₂b, hf₂u⟩ := Submodule.exists_le_ker_of_notMem hb
  have h₁u : f₁ u = 0 := hf₁u (Submodule.mem_span_singleton_self u)
  have h₂u : f₂ u = 0 := hf₂u (Submodule.mem_span_singleton_self u)
  by_cases h₁b : f₁ b = 0
  · by_cases h₂a : f₂ a = 0
    · refine ⟨f₁ + f₂, ?_, ?_, ?_⟩
      · rw [LinearMap.add_apply, h₁u, h₂u, add_zero]
      · rw [LinearMap.add_apply, h₂a, add_zero]; exact hf₁a
      · rw [LinearMap.add_apply, h₁b, zero_add]; exact hf₂b
    · exact ⟨f₂, h₂u, h₂a, hf₂b⟩
  · exact ⟨f₁, h₁u, hf₁a, h₁b⟩

theorem three_dvd_card_SL : 3 ∣ Nat.card SL(2, ZMod 3) := by
  let A : SL(2, ZMod 3) := ⟨!![1, 1; 0, 1], by decide⟩
  have hA : orderOf A = 3 :=
    orderOf_eq_prime (by decide) (fun h => absurd (congrArg Subtype.val h) (by decide))
  have := orderOf_dvd_natCard A
  rwa [hA] at this

variable [FiniteDimensional (ZMod 3) V]

omit [FiniteDimensional (ZMod 3) V] in
theorem exists_linearIndependent_triple (hV : finrank (ZMod 3) V = 3) {u : V} (hu : u ≠ 0) :
    ∃ w₂ w₃ : V, LinearIndependent (ZMod 3) ![u, w₂, w₃] := by
  have h1 : Submodule.span (ZMod 3) {u} ≠ ⊤ := fun h => by
    have := finrank_span_singleton (K := ZMod 3) hu
    rw [h, finrank_top, hV] at this
    omega
  obtain ⟨w₂, hw₂⟩ : ∃ w, w ∉ Submodule.span (ZMod 3) {u} := by
    by_contra h
    push Not at h
    exact h1 (eq_top_iff.mpr fun w _ => h w)
  have hli2 : LinearIndependent (ZMod 3) ![u, w₂] :=
    LinearIndependent.pair_iff.mpr fun s t hst => by
      by_cases ht : t = 0
      · rw [ht, zero_smul, add_zero] at hst
        exact ⟨(smul_eq_zero.mp hst).resolve_right hu, ht⟩
      · exfalso
        apply hw₂
        have h3 : w₂ = t⁻¹ • (t • w₂) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        have h4 : t • w₂ = -(s • u) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hst
        rw [h3, h4, smul_neg, smul_smul, ← neg_smul]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
  have h2 : Submodule.span (ZMod 3) {u, w₂} ≠ ⊤ := fun h => by
    have := finrank_span_pair hli2
    rw [h, finrank_top, hV] at this
    omega
  obtain ⟨w₃, hw₃⟩ : ∃ w, w ∉ Submodule.span (ZMod 3) {u, w₂} := by
    by_contra h
    push Not at h
    exact h2 (eq_top_iff.mpr fun w _ => h w)
  refine ⟨w₂, w₃, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc
  rw [Fin.sum_univ_three] at hc
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hc
  have hc2 : c 2 = 0 := by
    by_contra h
    apply hw₃
    have h3 : w₃ = (c 2)⁻¹ • (c 2 • w₃) := by rw [smul_smul, inv_mul_cancel₀ h, one_smul]
    have h4 : c 2 • w₃ = -(c 0 • u + c 1 • w₂) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact hc
    rw [h3, h4]
    refine Submodule.smul_mem _ _ (Submodule.neg_mem _ (Submodule.add_mem _ ?_ ?_))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  rw [hc2, zero_smul, add_zero] at hc
  obtain ⟨hc0, hc1⟩ := LinearIndependent.pair_iff.mp hli2 _ _ hc
  intro i
  fin_cases i
  exacts [hc0, hc1, hc2]

omit [FiniteDimensional (ZMod 3) V] in
theorem exists_mem_of_card_eq_nine (hV : finrank (ZMod 3) V = 3) {u : V} (hu : u ≠ 0)
    {R : Subgroup (V ≃ₗ[ZMod 3] V)} (hR9 : Nat.card R = 9)
    (hR : ∀ r ∈ R, ∃ f : Dual (ZMod 3) V, f u = 0 ∧ ∀ y, r y = y + f y • u)
    {f : Dual (ZMod 3) V} (hf : f u = 0) : ∃ r ∈ R, ∀ y, r y = y + f y • u := by
  classical
  obtain ⟨w₂, w₃, hli⟩ := exists_linearIndependent_triple hV hu
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hV])
  have hb0 : b 0 = u := by simp [b]
  have hb1 : b 1 = w₂ := by simp [b]
  have hb2 : b 2 = w₃ := by simp [b]
  have hdet : ∀ f₁ f₂ : Dual (ZMod 3) V, f₁ u = 0 → f₂ u = 0 → f₁ w₂ = f₂ w₂ →
      f₁ w₃ = f₂ w₃ → f₁ = f₂ := by
    intro f₁ f₂ h1 h2 h3 h4
    refine b.ext fun i => ?_
    fin_cases i
    · show f₁ (b 0) = f₂ (b 0)
      rw [hb0, h1, h2]
    · show f₁ (b 1) = f₂ (b 1)
      rw [hb1, h3]
    · show f₁ (b 2) = f₂ (b 2)
      rw [hb2, h4]
  have hex : ∀ r : R, ∃ f' : Dual (ZMod 3) V, f' u = 0 ∧
      ∀ y, (r : V ≃ₗ[ZMod 3] V) y = y + f' y • u := fun r => hR r r.2
  choose F hFu hF using hex
  let Φ : R → ZMod 3 × ZMod 3 := fun r => (F r w₂, F r w₃)
  have hinj : Function.Injective Φ := by
    intro r r' h
    have hFF : F r = F r' :=
      hdet _ _ (hFu r) (hFu r') (congrArg Prod.fst h) (congrArg Prod.snd h)
    apply Subtype.ext
    apply LinearEquiv.ext
    intro y
    rw [hF r y, hF r' y, hFF]
  have hcard : Nat.card (ZMod 3 × ZMod 3) ≤ Nat.card R := by
    rw [Nat.card_prod, Nat.card_zmod, hR9]
  obtain ⟨r, hr⟩ := (hinj.bijective_of_nat_card_le hcard).2 (f w₂, f w₃)
  have hFr : F r = f := hdet _ _ (hFu r) hf (congrArg Prod.fst hr) (congrArg Prod.snd hr)
  exact ⟨r, r.2, fun y => by rw [hF r y, hFr]⟩

theorem exists_subgroup_of_pair (hV : finrank (ZMod 3) V = 3)
    {G R : Subgroup (V ≃ₗ[ZMod 3] V)} (hRG : R ≤ G) {u : V} (hu : u ≠ 0)
    (hRform : ∀ r ∈ R, ∃ f : Dual (ZMod 3) V, f u = 0 ∧ ∀ y, r y = y + f y • u)
    (hfull : ∀ f : Dual (ZMod 3) V, f u = 0 → ∃ r ∈ R, ∀ y, r y = y + f y • u)
    {g : V ≃ₗ[ZMod 3] V} (hgG : g ∈ G) {f : Dual (ZMod 3) V} (hfu : f u = 0)
    (hα : f (g u) ≠ 0) (hβ : f (g⁻¹ u) ≠ 0) :
    ∃ H : Subgroup (V ≃ₗ[ZMod 3] V), R ≤ H ∧ H ≤ G ∧
      H = Subgroup.closure {y | ∃ h ∈ H, ∃ r ∈ R, y = h * r * h⁻¹} ∧
      (∃ Q : Subgroup H, ∃ _ : Q.Normal, CFSG.Assembly.IsElemAbelian 3 Q ∧ Nat.card Q = 9 ∧
        Nonempty (H ⧸ Q ≃* SL(2, ZMod 3))) ∧
      ∃ W : Submodule (ZMod 3) V, finrank (ZMod 3) W = 2 ∧ u ∈ W ∧
        ∀ h ∈ H, W.map (h : V →ₗ[ZMod 3] V) = W := by
  classical
  obtain ⟨t₁, ht₁R, ht₁⟩ := hfull f hfu
  set t₂ := g * t₁ * g⁻¹ with ht₂def
  set ψ : Dual (ZMod 3) V := f.comp ((g⁻¹ : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) with hψdef
  have hψ : ∀ y, ψ y = f (g⁻¹ y) := fun y => rfl
  have ht₂ : ∀ y, t₂ y = y + ψ y • g u := fun y => conj_apply_eq ht₁ y
  have hf0 : f ≠ 0 := fun h => hα (by rw [h, LinearMap.zero_apply])
  have hgu0 : g u ≠ 0 := fun h => hu (by
    have : g⁻¹ (g u) = u := by change g.symm (g u) = u; exact g.symm_apply_apply u
    rw [← this, h, map_zero])
  have hψgu : ψ (g u) = 0 := by
    rw [hψ]; change f (g.symm (g u)) = 0; rw [g.symm_apply_apply, hfu]
  have hψ0 : ψ ≠ 0 := fun h => hβ (by rw [← hψ, h, LinearMap.zero_apply])
  have h₁ : IsTransvectionWith t₁ u f := ⟨hu, hf0, hfu, ht₁⟩
  have h₂ : IsTransvectionWith t₂ (g u) ψ := ⟨hgu0, hψ0, hψgu, ht₂⟩
  have hgv : ψ u ≠ 0 := hβ
  set X := Subgroup.closure ({t₁, t₂} : Set (V ≃ₗ[ZMod 3] V)) with hXdef
  set P := Submodule.span (ZMod 3) {u, g u} with hPdef
  set L := LinearMap.ker f ⊓ LinearMap.ker ψ with hLdef
  have hPL : IsCompl P L := isCompl_span_pair_ker_inf_ker hfu hψgu hα hgv
  have huP : u ∈ P := Submodule.subset_span (by simp)
  have hguP : g u ∈ P := Submodule.subset_span (by simp)
  have hvw : LinearIndependent (ZMod 3) ![u, g u] :=
    linearIndependent_pair_of_transvections h₁ hα hu
  have hP2 : finrank (ZMod 3) P = 2 := finrank_span_pair hvw
  set H := R ⊔ X with hHdef
  have hXH : X ≤ H := le_sup_right
  have hRH : R ≤ H := le_sup_left
  have ht₁H : t₁ ∈ H := hRH ht₁R
  have ht₂X : t₂ ∈ X := Subgroup.subset_closure (by simp)
  have ht₂H : t₂ ∈ H := hXH ht₂X
  have ht₂G : t₂ ∈ G := G.mul_mem (G.mul_mem hgG (hRG ht₁R)) (G.inv_mem hgG)
  have hHG : H ≤ G := by
    refine sup_le hRG ?_
    rw [hXdef, Subgroup.closure_le]
    intro y hy
    rcases hy with hy | hy
    · rw [hy]; exact hRG ht₁R
    · rw [Set.mem_singleton_iff] at hy; rw [hy]; exact ht₂G
  have hgood : ∀ h ∈ H, (∀ p ∈ P, h p ∈ P) ∧ (∀ y, h y - y ∈ P) ∧
      ∀ hP : (∀ p ∈ P, h p ∈ P), LinearMap.det ((h : V →ₗ[ZMod 3] V).restrict hP) = 1 := by
    intro h hh
    rw [hHdef, Subgroup.sup_eq_closure] at hh
    induction hh using Subgroup.closure_induction with
    | mem h hh =>
      rcases hh with hR | hX
      · obtain ⟨f', hf'u, hf'⟩ := hRform h hR
        refine ⟨fun p hp => ?_, fun y => ?_, fun hP => ?_⟩
        · rw [hf']; exact P.add_mem hp (P.smul_mem _ huP)
        · rw [hf', add_sub_cancel_left]; exact P.smul_mem _ huP
        · have : (h : V →ₗ[ZMod 3] V).restrict hP =
              LinearMap.transvection (f'.comp P.subtype) ⟨u, huP⟩ := by
            ext y
            simp [LinearMap.restrict_apply, hf', LinearMap.transvection.apply]
          rw [this, LinearMap.transvection.det]
          simp [hf'u]
      · obtain ⟨hmap, hfix⟩ := pair_mapsTo_and_fix h₁ h₂ hX
        refine ⟨hmap, fun y => ?_, fun hP => det_restrict_pair h₁ h₂ hX⟩
        have hy : y ∈ P ⊔ L := by rw [hPL.sup_eq_top]; exact Submodule.mem_top
        obtain ⟨p, hp, l, hl, rfl⟩ := Submodule.mem_sup.mp hy
        rw [map_add, hfix l hl, add_sub_add_right_eq_sub]
        exact P.sub_mem (hmap p hp) hp
    | one =>
      refine ⟨fun p hp => hp, fun y => ?_, fun hP => ?_⟩
      · rw [LinearEquiv.coe_one, id, sub_self]; exact P.zero_mem
      · convert LinearMap.det_id (A := ZMod 3) (M := P) using 2
        ext y
        rfl
    | mul a b _ _ iha ihb =>
      refine ⟨fun p hp => iha.1 _ (ihb.1 p hp), fun y => ?_, fun hP => ?_⟩
      · have : (a * b) y - y = (a (b y) - b y) + (b y - y) := by
          rw [LinearEquiv.mul_apply]; abel
        rw [this]
        exact P.add_mem (iha.2.1 _) (ihb.2.1 _)
      · have hmul : ((a * b : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V).restrict hP =
            (a : V →ₗ[ZMod 3] V).restrict iha.1 * (b : V →ₗ[ZMod 3] V).restrict ihb.1 := by
          ext y; rfl
        rw [hmul, map_mul, iha.2.2 iha.1, ihb.2.2 ihb.1, one_mul]
    | inv a _ iha =>
      refine ⟨inv_mapsTo iha.1, fun y => ?_, fun hP => ?_⟩
      · have h1 : a (a⁻¹ y) = y := by change a (a.symm y) = y; exact a.apply_symm_apply y
        have : a⁻¹ y - y = -(a (a⁻¹ y) - a⁻¹ y) := by rw [h1]; abel
        rw [this]
        exact P.neg_mem (iha.2.1 _)
      · have hmul : (a : V →ₗ[ZMod 3] V).restrict iha.1 *
            ((a⁻¹ : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V).restrict hP = 1 := by
          ext y
          change a (a.symm (y : V)) = y
          rw [LinearEquiv.apply_symm_apply]
        have := congrArg LinearMap.det hmul
        rw [map_mul, iha.2.2 iha.1, one_mul, map_one] at this
        exact this
  have hmapH : ∀ h : H, ∀ p ∈ P, (h : V ≃ₗ[ZMod 3] V) p ∈ P := fun h => (hgood h h.2).1
  set B := pairBasis hvw with hBdef
  let ρ : H →* SL(2, ZMod 3) :=
    { toFun := fun h => ⟨LinearMap.toMatrix B B
          (((h : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V).restrict (hmapH h)), by
        rw [LinearMap.det_toMatrix]
        exact (hgood h h.2).2.2 _⟩
      map_one' := by
        apply Subtype.ext
        change LinearMap.toMatrix B B _ = 1
        convert LinearMap.toMatrix_id B using 2
        ext y
        rfl
      map_mul' := fun x y => by
        apply Subtype.ext
        change LinearMap.toMatrix B B _ = LinearMap.toMatrix B B _ * LinearMap.toMatrix B B _
        rw [← LinearMap.toMatrix_comp]
        rfl }
  have hρ : ∀ h : H, ((ρ h : SL(2, ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
      LinearMap.toMatrix B B (((h : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V).restrict (hmapH h)) :=
    fun h => rfl
  have hker : ∀ h : H, h ∈ ρ.ker ↔ ∀ p ∈ P, (h : V ≃ₗ[ZMod 3] V) p = p := by
    intro h
    rw [MonoidHom.mem_ker]
    constructor
    · intro h1 p hp
      have hm := congrArg (fun A : SL(2, ZMod 3) => (A : Matrix (Fin 2) (Fin 2) (ZMod 3))) h1
      simp only [hρ, Matrix.SpecialLinearGroup.coe_one] at hm
      rw [← LinearMap.toMatrix_id B] at hm
      have hres := (LinearMap.toMatrix B B).injective hm
      exact congrArg (fun φ : P →ₗ[ZMod 3] P => (φ ⟨p, hp⟩ : V)) hres
    · intro h1
      apply Subtype.ext
      rw [hρ, Matrix.SpecialLinearGroup.coe_one, ← LinearMap.toMatrix_id B]
      congr 1
      ext y
      exact h1 y y.2
  have hsurj : Function.Surjective ρ := by
    intro A
    set φ : P →ₗ[ZMod 3] P := Matrix.toLin B B (A : Matrix (Fin 2) (Fin 2) (ZMod 3))
    have hφ : LinearMap.det φ = 1 := by rw [LinearMap.det_toLin]; exact A.2
    obtain ⟨y, hy, hyP, -⟩ := exists_mem_of_det_eq_one (H := X) h₁ h₂
      (Subgroup.subset_closure (by simp)) ht₂X hα hgv φ hφ
    refine ⟨⟨y, hXH hy⟩, Subtype.ext ?_⟩
    rw [hρ]
    have hres : ((y : V →ₗ[ZMod 3] V)).restrict (hmapH ⟨y, hXH hy⟩) = φ := by
      ext p
      exact hyP p
    change LinearMap.toMatrix B B ((y : V →ₗ[ZMod 3] V).restrict (hmapH ⟨y, hXH hy⟩)) = _
    rw [hres, LinearMap.toMatrix_toLin]
  have hL1 : finrank (ZMod 3) L = 1 := by
    have := Submodule.finrank_add_eq_of_isCompl hPL
    rw [hP2, hV] at this
    omega
  obtain ⟨l₀, hl₀L, hl₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := L)
    (fun h => by rw [h, finrank_bot] at hL1; exact zero_ne_one hL1)
  have hl₀P : l₀ ∉ P := fun h => hl₀0 ((Submodule.disjoint_def.mp hPL.disjoint) l₀ h hl₀L)
  obtain ⟨f₁, hf₁l, hf₁P⟩ := Submodule.exists_le_ker_of_notMem hl₀P
  set f₀ : Dual (ZMod 3) V := (f₁ l₀)⁻¹ • f₁ with hf₀def
  have hf₀l : f₀ l₀ = 1 := by
    rw [hf₀def, LinearMap.smul_apply, smul_eq_mul]; exact inv_mul_cancel₀ hf₁l
  have hf₀P : ∀ p ∈ P, f₀ p = 0 := fun p hp => by
    rw [hf₀def, LinearMap.smul_apply, LinearMap.mem_ker.mp (hf₁P hp), smul_zero]
  have hkerf₀ : ∀ y, f₀ y = 0 → y ∈ P := by
    have hf₀ne : f₀ ≠ 0 := fun h => by
      rw [h, LinearMap.zero_apply] at hf₀l; exact zero_ne_one hf₀l
    have h1 := Module.Dual.finrank_ker_add_one_of_ne_zero hf₀ne
    rw [hV] at h1
    have heq : P = LinearMap.ker f₀ :=
      Submodule.eq_of_le_of_finrank_eq (fun p hp => hf₀P p hp) (by rw [hP2]; omega)
    intro y hy
    rw [heq]
    exact hy
  have hdecomp : ∀ y, y - f₀ y • l₀ ∈ P := fun y => by
    apply hkerf₀
    rw [map_sub, map_smul, hf₀l, smul_eq_mul, mul_one]
    exact sub_self _
  let S : AddSubgroup V :=
    { carrier := {p | p ∈ P ∧ ∃ h ∈ H, ∀ y, h y = y + f₀ y • p}
      add_mem' := by
        rintro p p' ⟨hp, h, hh, hhy⟩ ⟨hp', h', hh', hh'y⟩
        refine ⟨P.add_mem hp hp', h * h', H.mul_mem hh hh', fun y => ?_⟩
        rw [LinearEquiv.mul_apply, hh'y, map_add, map_smul, hhy y, hhy p', hf₀P p' hp',
          zero_smul, add_zero, smul_add]
        abel
      zero_mem' := ⟨P.zero_mem, 1, H.one_mem, fun y => by
        rw [smul_zero, add_zero]; rfl⟩
      neg_mem' := by
        rintro p ⟨hp, h, hh, hhy⟩
        refine ⟨P.neg_mem hp, h⁻¹, H.inv_mem hh, fun y => ?_⟩
        change h.symm y = _
        rw [LinearEquiv.symm_apply_eq, hhy, map_add, map_smul, hf₀P _ (P.neg_mem hp),
          smul_zero, add_zero, smul_neg]
        abel }
  have hsmulS : ∀ (c : ZMod 3) {x : V}, x ∈ S → c • x ∈ S := fun c x hx => by
    rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]
    exact S.nsmul_mem hx _
  obtain ⟨r₀, hr₀R, hr₀⟩ := hfull f₀ (hf₀P u huP)
  have huS : u ∈ S := ⟨huP, r₀, hRH hr₀R, hr₀⟩
  have ht₂uS : t₂ u ∈ S := by
    refine ⟨(hgood t₂ ht₂H).1 u huP, t₂ * r₀ * t₂⁻¹,
      H.mul_mem (H.mul_mem ht₂H (hRH hr₀R)) (H.inv_mem ht₂H), fun y => ?_⟩
    rw [conj_apply_eq hr₀ y]
    congr 2
    have := hf₀P _ ((hgood t₂⁻¹ (H.inv_mem ht₂H)).2.1 y)
    rw [map_sub] at this
    exact sub_eq_zero.mp this
  have hPS : ∀ p ∈ P, p ∈ S := by
    intro p hp
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hp
    have hgu : g u = (ψ u)⁻¹ • (t₂ u - u) := by
      rw [ht₂ u, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hgv, one_smul]
    rw [hgu]
    exact S.add_mem (hsmulS a huS) (hsmulS b (hsmulS _ (S.sub_mem ht₂uS huS)))
  have hkerform : ∀ h : H, h ∈ ρ.ker →
      ∀ y, (h : V ≃ₗ[ZMod 3] V) y = y + f₀ y • ((h : V ≃ₗ[ZMod 3] V) l₀ - l₀) := by
    intro h hh y
    have hfix := (hker h).mp hh
    have h1 : (h : V ≃ₗ[ZMod 3] V) (y - f₀ y • l₀) = y - f₀ y • l₀ := hfix _ (hdecomp y)
    rw [map_sub, map_smul] at h1
    rw [smul_sub]
    calc (h : V ≃ₗ[ZMod 3] V) y
        = ((h : V ≃ₗ[ZMod 3] V) y - f₀ y • (h : V ≃ₗ[ZMod 3] V) l₀) +
          f₀ y • (h : V ≃ₗ[ZMod 3] V) l₀ := by abel
      _ = y + (f₀ y • (h : V ≃ₗ[ZMod 3] V) l₀ - f₀ y • l₀) := by rw [h1]; abel
  let κ : ρ.ker → P := fun h => ⟨((h : H) : V ≃ₗ[ZMod 3] V) l₀ - l₀, (hgood _ (h : H).2).2.1 l₀⟩
  have hκ : Function.Bijective κ := by
    constructor
    · intro h h' hhh'
      have heq : ((h : H) : V ≃ₗ[ZMod 3] V) l₀ - l₀ = ((h' : H) : V ≃ₗ[ZMod 3] V) l₀ - l₀ :=
        congrArg Subtype.val hhh'
      apply Subtype.ext; apply Subtype.ext; apply LinearEquiv.ext
      intro y
      rw [hkerform _ h.2, hkerform _ h'.2, heq]
    · rintro ⟨p, hp⟩
      obtain ⟨-, h, hh, hhy⟩ := hPS p hp
      have hhker : (⟨h, hh⟩ : H) ∈ ρ.ker := by
        rw [hker]
        intro p' hp'
        change h p' = p'
        rw [hhy, hf₀P p' hp', zero_smul, add_zero]
      refine ⟨⟨⟨h, hh⟩, hhker⟩, Subtype.ext ?_⟩
      change h l₀ - l₀ = p
      rw [hhy, hf₀l, one_smul, add_sub_cancel_left]
  have hQ9 : Nat.card ρ.ker = 9 := by
    rw [Nat.card_congr (Equiv.ofBijective κ hκ)]
    rw [Module.natCard_eq_pow_finrank (K := ZMod 3), Nat.card_zmod, hP2]
    norm_num
  have hf₀add : ∀ y p : V, f₀ p = 0 → ∀ c : ZMod 3, f₀ (y + c • p) = f₀ y := by
    intro y p hp c
    rw [map_add, map_smul, hp, smul_zero]
    exact add_zero _
  have hQab : CFSG.Assembly.IsElemAbelian 3 ρ.ker := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
    · apply Subtype.ext; apply Subtype.ext; apply LinearEquiv.ext
      intro y
      change ((a : H) : V ≃ₗ[ZMod 3] V) (((b : H) : V ≃ₗ[ZMod 3] V) y) =
        ((b : H) : V ≃ₗ[ZMod 3] V) (((a : H) : V ≃ₗ[ZMod 3] V) y)
      set pa := ((a : H) : V ≃ₗ[ZMod 3] V) l₀ - l₀ with hpadef
      set pb := ((b : H) : V ≃ₗ[ZMod 3] V) l₀ - l₀ with hpbdef
      have ha : ∀ y, ((a : H) : V ≃ₗ[ZMod 3] V) y = y + f₀ y • pa := hkerform _ a.2
      have hb : ∀ y, ((b : H) : V ≃ₗ[ZMod 3] V) y = y + f₀ y • pb := hkerform _ b.2
      have hpa : f₀ pa = 0 := hf₀P _ ((hgood _ (a : H).2).2.1 l₀)
      have hpb : f₀ pb = 0 := hf₀P _ ((hgood _ (b : H).2).2.1 l₀)
      rw [ha (((b : H) : V ≃ₗ[ZMod 3] V) y), hb y, ha y, hb (y + f₀ y • pa), hf₀add y pb hpb,
        hf₀add y pa hpa]
      abel
    · apply Subtype.ext; apply LinearEquiv.ext
      intro y
      set pa := (a : V ≃ₗ[ZMod 3] V) l₀ - l₀ with hpadef
      have hform : ∀ y, (a : V ≃ₗ[ZMod 3] V) y = y + f₀ y • pa := hkerform a ha
      have hpa : f₀ pa = 0 := hf₀P _ ((hgood _ a.2).2.1 l₀)
      change ((a ^ 3 : H) : V ≃ₗ[ZMod 3] V) y = y
      rw [Subgroup.coe_pow, pow_three, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hform y,
        hform (y + f₀ y • pa), hf₀add y pa hpa, hform, hf₀add _ pa hpa, hf₀add y pa hpa]
      have h3 := zmod3_three_smul (f₀ y • pa)
      calc y + f₀ y • pa + f₀ y • pa + f₀ y • pa = y + (3 : ℕ) • (f₀ y • pa) := by abel
        _ = y := by rw [h3, add_zero]
  have hnc : H = Subgroup.closure {y | ∃ h ∈ H, ∃ r ∈ R, y = h * r * h⁻¹} := by
    apply le_antisymm
    · rw [hHdef, sup_le_iff]
      constructor
      · intro r hr
        exact Subgroup.subset_closure ⟨1, H.one_mem, r, hr, by rw [one_mul, inv_one, mul_one]⟩
      · rw [hXdef, Subgroup.closure_le]
        intro y hy
        rcases hy with hy | hy
        · rw [hy]
          exact Subgroup.subset_closure ⟨1, H.one_mem, t₁, ht₁R, by rw [one_mul, inv_one, mul_one]⟩
        · rw [Set.mem_singleton_iff] at hy
          rw [hy]
          have ht₂u : t₂ u = u + ψ u • g u := ht₂ u
          have hft₂u : f (t₂ u) = ψ u * f (g u) := by
            rw [ht₂u, map_add, map_smul, hfu, smul_eq_mul, zero_add]
          have ht₁inv : ∀ y, t₁⁻¹ y = y - f y • u := fun y => by
            have hfy : f (y - f y • u) = f y := by
              rw [map_sub, map_smul, hfu, smul_zero]
              exact sub_zero _
            change t₁.symm y = _
            rw [LinearEquiv.symm_apply_eq, ht₁, hfy, sub_add_cancel]
          obtain ⟨x, hxH, hxu⟩ : ∃ x ∈ H, x u = ψ u • g u := by
            rcases (by decide : ∀ c : ZMod 3, c ≠ 0 → c = 1 ∨ c = 2) _
              (mul_ne_zero hgv hα) with hc | hc
            · refine ⟨t₁⁻¹ * t₂, H.mul_mem (H.inv_mem ht₁H) ht₂H, ?_⟩
              rw [LinearEquiv.mul_apply, ht₁inv, hft₂u, hc, one_smul, ht₂u, add_sub_cancel_left]
            · refine ⟨t₁ * t₂, H.mul_mem ht₁H ht₂H, ?_⟩
              rw [LinearEquiv.mul_apply, ht₁, hft₂u, hc, ht₂u, add_assoc, ← add_assoc u,
                ← add_comm (ψ u • g u), add_assoc]
              have : u + (2 : ZMod 3) • u = 0 := by
                rw [show (2 : ZMod 3) • u = u + u by
                  rw [show (2 : ZMod 3) = 1 + 1 from rfl, add_smul, one_smul]]
                rw [← add_assoc]
                have := zmod3_three_smul u
                rwa [show (3 : ℕ) • u = u + u + u by abel] at this
              rw [this, add_zero]
          have hxinv : x⁻¹ (g u) = (ψ u)⁻¹ • u := by
            change x.symm (g u) = _
            rw [LinearEquiv.symm_apply_eq, map_smul, hxu, smul_smul, inv_mul_cancel₀ hgv,
              one_smul]
          set f'' : Dual (ZMod 3) V :=
            (ψ u)⁻¹ • ψ.comp ((x : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) with hf''def
          have hf''app : ∀ y, f'' y = (ψ u)⁻¹ * ψ (x y) := fun y => rfl
          have hf''u : f'' u = 0 := by
            rw [hf''app, hxu, map_smul, hψgu, smul_zero]
            exact mul_zero _
          obtain ⟨r'', hr''R, hr''⟩ := hfull f'' hf''u
          have hr''eq : r'' = x⁻¹ * t₂ * x⁻¹⁻¹ := by
            apply LinearEquiv.ext
            intro y
            rw [hr'' y, conj_apply_eq ht₂ y, inv_inv, hxinv, smul_smul, hf''app, mul_comm]
          refine Subgroup.subset_closure ⟨x, hxH, r'', hr''R, ?_⟩
          rw [hr''eq, inv_inv]
          group
    · rw [Subgroup.closure_le]
      rintro _ ⟨h, hh, r, hr, rfl⟩
      exact H.mul_mem (H.mul_mem hh (hRH hr)) (H.inv_mem hh)
  refine ⟨H, hRH, hHG, hnc, ⟨ρ.ker, inferInstance, hQab, hQ9,
    ⟨QuotientGroup.quotientKerEquivOfSurjective ρ hsurj⟩⟩, P, hP2, huP, fun h hh => ?_⟩
  exact map_eq_of_mapsTo (hgood h hh).1

theorem rank3II_3_12 (hV : finrank (ZMod 3) V = 3) {G R : Subgroup (V ≃ₗ[ZMod 3] V)}
    {U : Submodule (ZMod 3) V} (hU : finrank (ZMod 3) U = 1) (hRG : R ≤ G)
    (hR9 : Nat.card R = 9)
    (hRU : ∀ r ∈ R, r ≠ 1 → (∃ v f, IsTransvectionWith r v f) ∧
      LinearMap.range ((r : V →ₗ[ZMod 3] V) - 1) = U) :
    ((¬ ∀ g ∈ G, U.map (g : V →ₗ[ZMod 3] V) = U) →
      ∃ H : Subgroup (V ≃ₗ[ZMod 3] V), R ≤ H ∧ H ≤ G ∧
        H = Subgroup.closure {y | ∃ h ∈ H, ∃ r ∈ R, y = h * r * h⁻¹} ∧
        (∃ Q : Subgroup H, ∃ _ : Q.Normal, CFSG.Assembly.IsElemAbelian 3 Q ∧
          Nat.card Q = 9 ∧ Nonempty (H ⧸ Q ≃* SL(2, ZMod 3))) ∧
        ∃ W : Submodule (ZMod 3) V, finrank (ZMod 3) W = 2 ∧ U ≤ W ∧
          ∀ h ∈ H, W.map (h : V →ₗ[ZMod 3] V) = W) ∧
      (CFSG.ABGLocalTools.IsSylowOf 3 R G → ∀ g ∈ G, U.map (g : V →ₗ[ZMod 3] V) = U) := by
  obtain ⟨u, hu, hUu⟩ := exists_eq_span_of_finrank_eq_one hU
  have hRform : ∀ r ∈ R, ∃ f : Dual (ZMod 3) V, f u = 0 ∧ ∀ y, r y = y + f y • u := by
    intro r hr
    by_cases h1 : r = 1
    · refine ⟨0, rfl, fun y => ?_⟩
      rw [h1, LinearMap.zero_apply, zero_smul, add_zero]
      rfl
    · obtain ⟨⟨v, f, hvf⟩, hrange⟩ := hRU r hr h1
      exact exists_eq_add_smul_of_center hvf (hrange.trans hUu)
  have hfull : ∀ f : Dual (ZMod 3) V, f u = 0 → ∃ r ∈ R, ∀ y, r y = y + f y • u :=
    fun f hf => exists_mem_of_card_eq_nine hV hu hR9 hRform hf
  have part1 : (¬ ∀ g ∈ G, U.map (g : V →ₗ[ZMod 3] V) = U) →
      ∃ H : Subgroup (V ≃ₗ[ZMod 3] V), R ≤ H ∧ H ≤ G ∧
        H = Subgroup.closure {y | ∃ h ∈ H, ∃ r ∈ R, y = h * r * h⁻¹} ∧
        (∃ Q : Subgroup H, ∃ _ : Q.Normal, CFSG.Assembly.IsElemAbelian 3 Q ∧
          Nat.card Q = 9 ∧ Nonempty (H ⧸ Q ≃* SL(2, ZMod 3))) ∧
        ∃ W : Submodule (ZMod 3) V, finrank (ZMod 3) W = 2 ∧ U ≤ W ∧
          ∀ h ∈ H, W.map (h : V →ₗ[ZMod 3] V) = W := by
    intro hne
    push Not at hne
    obtain ⟨g, hgG, hgU⟩ := hne
    have hgu : g u ∉ Submodule.span (ZMod 3) {u} := by
      intro h
      apply hgU
      apply Submodule.eq_of_le_of_finrank_eq
      · rw [hUu, Submodule.map_span_le]
        intro m hm
        rw [Set.mem_singleton_iff] at hm
        rw [hm]
        exact h
      · exact LinearEquiv.finrank_map_eq g U
    have hgu' : g⁻¹ u ∉ Submodule.span (ZMod 3) {u} := by
      intro h
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
      have hgc : u = c • g u := by
        have : g (g⁻¹ u) = u := by change g (g.symm u) = u; exact g.apply_symm_apply u
        rw [← hc, map_smul] at this
        exact this.symm
      have hc0 : c ≠ 0 := fun h0 => hu (by rw [hgc, h0, zero_smul])
      apply hgu
      rw [Submodule.mem_span_singleton]
      refine ⟨c⁻¹, ?_⟩
      have := congrArg (c⁻¹ • ·) hgc
      rw [this, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    obtain ⟨f, hfu, hα, hβ⟩ := exists_dual_ne_zero_ne_zero hgu hgu'
    obtain ⟨H, hRH, hHG, hnc, hQ, W, hW2, huW, hHW⟩ :=
      exists_subgroup_of_pair hV hRG hu hRform hfull hgG hfu hα hβ
    refine ⟨H, hRH, hHG, hnc, hQ, W, hW2, ?_, hHW⟩
    rw [hUu, Submodule.span_le, Set.singleton_subset_iff]
    exact huW
  refine ⟨part1, fun hsyl => ?_⟩
  by_contra hne
  obtain ⟨H, -, hHG, -, ⟨Q, hQn, -, hQ9, ⟨e⟩⟩, -⟩ := part1 hne
  have : Finite (V ≃ₗ[ZMod 3] V) := finite_linearEquiv
  have h3 : 3 ∣ Nat.card (H ⧸ Q) := by
    rw [Nat.card_congr e.toEquiv]
    exact three_dvd_card_SL
  have h27 : 3 ^ 3 ∣ Nat.card G := by
    have hH : Nat.card H = Nat.card (H ⧸ Q) * 9 := by
      rw [← hQ9]; exact Subgroup.card_eq_card_quotient_mul_card_subgroup Q
    have : 3 ^ 3 ∣ Nat.card H := by
      rw [hH]
      obtain ⟨k, hk⟩ := h3
      rw [hk]
      exact ⟨k, by ring⟩
    exact this.trans (Subgroup.card_dvd_of_le hHG)
  obtain ⟨Q₀, hQ₀⟩ := hsyl
  have hdvd := Q₀.pow_dvd_card_of_pow_dvd_card h27
  have hcard : Nat.card (Q₀ : Subgroup G) = Nat.card R := by
    rw [← hQ₀]
    exact (Subgroup.card_map_of_injective G.subtype_injective).symm
  rw [hcard, hR9] at hdvd
  norm_num at hdvd

end CFSG.RankThree.PartTwo.Sec3
