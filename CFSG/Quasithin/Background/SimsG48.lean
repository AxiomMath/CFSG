module

public import CFSG.Quasithin.Background.SimsG4Defs
public import CFSG.Quasithin.Background.SimsG45Transv

public section

namespace CFSG.Quasithin.SimsG4

open LinearMap (BilinForm)

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

namespace G48

theorem exists_stabField [Finite F] (I : AddSubgroup V) :
    ∃ F₀ : Subfield F, ∀ c, c ∈ F₀ ↔ ∀ x ∈ I, c • x ∈ I := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hpow : ∀ c : F, (∀ x ∈ I, c • x ∈ I) → ∀ n : ℕ, ∀ x ∈ I, c ^ n • x ∈ I := by
    intro c hc n
    induction n with
    | zero =>
      intro x hx
      rwa [pow_zero, one_smul]
    | succ n ih =>
      intro x hx
      rw [pow_succ, mul_smul]
      exact ih _ (hc x hx)
  have hinv : ∀ c : F, (∀ x ∈ I, c • x ∈ I) → ∀ x ∈ I, c⁻¹ • x ∈ I := by
    intro c hc
    rcases eq_or_ne c 0 with rfl | hc0
    · intro x _
      rw [inv_zero, zero_smul]
      exact I.zero_mem
    have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
    have h1 : c ^ (Fintype.card F - 2) * c = 1 := by
      rw [← pow_succ, show Fintype.card F - 2 + 1 = Fintype.card F - 1 by omega]
      exact FiniteField.pow_card_sub_one_eq_one c hc0
    rw [← eq_inv_of_mul_eq_one_left h1]
    exact hpow c hc _
  let F₀ : Subfield F :=
    { carrier := {c | ∀ x ∈ I, c • x ∈ I}
      mul_mem' := fun {c d} hc hd x hx => by
        rw [mul_smul]
        exact hc _ (hd x hx)
      one_mem' := fun x hx => by
        rw [one_smul]
        exact hx
      add_mem' := fun {c d} hc hd x hx => by
        rw [add_smul]
        exact I.add_mem (hc x hx) (hd x hx)
      zero_mem' := fun x _ => by
        rw [zero_smul]
        exact I.zero_mem
      neg_mem' := fun {c} hc x hx => by
        rw [neg_smul]
        exact I.neg_mem (hc x hx)
      inv_mem' := fun c hc => hinv c hc }
  exact ⟨F₀, fun c => Iff.rfl⟩

theorem forall_mem_sup_zpowers {G : Type*} [Group G] {H : Subgroup G} {a : G} {P : G → Prop}
    (one : P 1) (mul : ∀ x y, P x → P y → P (x * y)) (inv : ∀ x, P x → P x⁻¹)
    (hH : ∀ h ∈ H, P h) (ha : P a) : ∀ g ∈ H ⊔ Subgroup.zpowers a, P g := by
  let K : Subgroup G :=
    { carrier := {g | P g}
      mul_mem' := fun {x y} hx hy => mul x y hx hy
      one_mem' := one
      inv_mem' := fun {x} hx => inv x hx }
  have hle : H ⊔ Subgroup.zpowers a ≤ K :=
    sup_le (fun h hh => hH h hh) (Subgroup.zpowers_le.mpr ha)
  exact fun g hg => hle hg

theorem invariant_sup_zpowers {H : Subgroup (V ≃ₗ[F] V)} {a : V ≃ₗ[F] V} (haa : a * a = 1)
    {S : AddSubgroup V} (hH : ∀ h ∈ H, ∀ y ∈ S, h y ∈ S) (ha : ∀ y ∈ S, a y ∈ S) :
    ∀ g ∈ H ⊔ Subgroup.zpowers a, ∀ y ∈ S, g y ∈ S := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have key := forall_mem_sup_zpowers (H := H) (a := a)
    (P := fun g => (∀ y ∈ S, g y ∈ S) ∧ ∀ y ∈ S, g⁻¹ y ∈ S)
    ⟨fun y hy => hy, fun y hy => by rw [inv_one]; exact hy⟩
    (fun x y hx hy => ⟨fun z hz => hx.1 _ (hy.1 z hz), fun z hz => by
      rw [mul_inv_rev]
      exact hy.2 _ (hx.2 z hz)⟩)
    (fun x hx => ⟨hx.2, fun z hz => by rw [inv_inv]; exact hx.1 z hz⟩)
    (fun h hh => ⟨hH h hh, hH h⁻¹ (H.inv_mem hh)⟩)
    ⟨ha, fun y hy => by rw [hainv]; exact ha y hy⟩
  exact fun g hg => (key g hg).1

theorem eq_of_minimal {G : Subgroup (V ≃ₗ[F] V)} {I : AddSubgroup V}
    (hImin : ∀ Y : AddSubgroup V, Y ≤ I → (∀ g ∈ G, ∀ y ∈ Y, g y ∈ Y) → Y = ⊥ ∨ Y = I)
    {Y : AddSubgroup V} (hYI : Y ≤ I) (hY : ∀ g ∈ G, ∀ y ∈ Y, g y ∈ Y) {x : V} (hx : x ∈ Y)
    (hx0 : x ≠ 0) : Y = I := by
  refine (hImin Y hYI hY).resolve_left fun h => hx0 ?_
  rw [h] at hx
  exact AddSubgroup.mem_bot.mp hx

theorem smul_mem_of_smul_mem {G : Subgroup (V ≃ₗ[F] V)} {I : AddSubgroup V}
    (hIinv : ∀ g ∈ G, ∀ x ∈ I, g x ∈ I)
    (hImin : ∀ Y : AddSubgroup V, Y ≤ I → (∀ g ∈ G, ∀ y ∈ Y, g y ∈ Y) → Y = ⊥ ∨ Y = I)
    {c : F} {x : V} (hx : x ∈ I) (hx0 : x ≠ 0) (hcx : c • x ∈ I) : ∀ y ∈ I, c • y ∈ I := by
  let Y : AddSubgroup V :=
    { carrier := {z | z ∈ I ∧ c • z ∈ I}
      zero_mem' := ⟨I.zero_mem, by rw [smul_zero]; exact I.zero_mem⟩
      add_mem' := fun {z w} hz hw => ⟨I.add_mem hz.1 hw.1, by
        rw [smul_add]
        exact I.add_mem hz.2 hw.2⟩
      neg_mem' := fun {z} hz => ⟨I.neg_mem hz.1, by
        rw [smul_neg]
        exact I.neg_mem hz.2⟩ }
  have hY : ∀ g ∈ G, ∀ y ∈ Y, g y ∈ Y := fun g hg y hy =>
    ⟨hIinv g hg y hy.1, by
      rw [← map_smul]
      exact hIinv g hg _ hy.2⟩
  have hYI : Y ≤ I := fun z hz => hz.1
  have hYeq := eq_of_minimal hImin hYI hY (x := x) ⟨hx, hcx⟩ hx0
  intro y hy
  have hy' : y ∈ Y := by rw [hYeq]; exact hy
  exact hy'.2

theorem span_eq_top_of_irred {G H : Subgroup (V ≃ₗ[F] V)} {I : AddSubgroup V} (hHG : H ≤ G)
    (hIinv : ∀ g ∈ G, ∀ x ∈ I, g x ∈ I) (hHirr : IsIrredOnV H) (hI0 : I ≠ ⊥) :
    Submodule.span F (I : Set V) = ⊤ := by
  refine (hHirr _ fun g hg w hw => ?_).resolve_left fun h => hI0 ?_
  · have hle : Submodule.span F (I : Set V) ≤
        (Submodule.span F (I : Set V)).comap (g : V →ₗ[F] V) :=
      Submodule.span_le.mpr fun x hx => Submodule.subset_span (hIinv g (hHG hg) x hx)
    exact hle hw
  · rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ Submodule.span F (I : Set V) := Submodule.subset_span hx
    rw [h, Submodule.mem_bot] at hx'
    exact AddSubgroup.mem_bot.mpr hx'

theorem exists_ne_zero_of_span (B : BilinForm F V) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    {I : AddSubgroup V} (hspan : Submodule.span F (I : Set V) = ⊤) {x : V} (hx0 : x ≠ 0) :
    ∃ y ∈ I, B x y ≠ 0 := by
  by_contra hcon
  push Not at hcon
  refine hx0 (hnd x fun y => ?_)
  have hle : Submodule.span F (I : Set V) ≤ LinearMap.ker (B x) :=
    Submodule.span_le.mpr fun z hz => LinearMap.mem_ker.mpr (hcon z hz)
  have hy : y ∈ LinearMap.ker (B x) := hle (by rw [hspan]; exact Submodule.mem_top)
  exact LinearMap.mem_ker.mp hy

theorem eq_zero_of_forall_left (B : BilinForm F V) (halt : ∀ x, B x x = 0)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) {I : AddSubgroup V}
    (hspan : Submodule.span F (I : Set V) = ⊤) {x : V} (h : ∀ y ∈ I, B y x = 0) : x = 0 := by
  by_contra hx0
  obtain ⟨y, hy, hxy⟩ := exists_ne_zero_of_span B hnd hspan hx0
  apply hxy
  rw [SimsG45.bilin_skew B halt x y, h y hy, neg_zero]

theorem exists_not_mem_span_pair (hdim : Module.finrank F V = 4) {I : AddSubgroup V}
    (hspan : Submodule.span F (I : Set V) = ⊤) (p q : V) :
    ∃ z ∈ I, z ∉ Submodule.span F {p, q} := by
  classical
  by_contra hcon
  push Not at hcon
  have hle : Submodule.span F (I : Set V) ≤ Submodule.span F {p, q} :=
    Submodule.span_le.mpr fun z hz => hcon z hz
  rw [hspan] at hle
  have h1 : Module.finrank F (Submodule.span F ({p, q} : Set V)) ≤ 2 := by
    have h := finrank_span_finset_le_card (R := F) ({p, q} : Finset V)
    rw [Finset.coe_insert, Finset.coe_singleton] at h
    exact h.trans Finset.card_le_two
  have h2 : Module.finrank F (Submodule.span F ({p, q} : Set V)) = 4 := by
    rw [eq_top_iff.mpr hle, finrank_top, hdim]
  omega

theorem linearIndependent_antidiag (B₀ : BilinForm F V) {e : Fin 4 → V}
    (hb : ∀ i j, B₀ (e i) (e j) = if i.val + j.val = 3 then 1 else 0) :
    LinearIndependent F e := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have key : ∀ j, ∑ i, g i * B₀ (e i) (e j) = 0 := fun j => by
    simpa [map_sum, map_smul] using congrArg (fun x => B₀ x (e j)) hg
  fin_cases i
  · simpa [Fin.sum_univ_four, hb] using key 3
  · simpa [Fin.sum_univ_four, hb] using key 2
  · simpa [Fin.sum_univ_four, hb] using key 1
  · simpa [Fin.sum_univ_four, hb] using key 0

theorem repr_antidiag (B₀ : BilinForm F V) (b : Module.Basis (Fin 4) F V)
    (hb : ∀ i j, B₀ (b i) (b j) = if i.val + j.val = 3 then 1 else 0) (w : V) (i : Fin 4) :
    b.repr w i = B₀ (b i.rev) w := by
  conv_rhs => rw [← b.sum_repr w]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, hb]
  fin_cases i <;> simp [Fin.sum_univ_four, Fin.rev]

theorem exists_antidiag_family [CharP F 2] (B₀ : BilinForm F V) (halt : ∀ x, B₀ x x = 0)
    {F₀ : Subfield F} {I : AddSubgroup V} (hsm : ∀ c ∈ F₀, ∀ x ∈ I, c • x ∈ I)
    (hval : ∀ x ∈ I, ∀ y ∈ I, B₀ x y ∈ F₀) (hnd : ∀ x ∈ I, x ≠ 0 → ∃ y ∈ I, B₀ x y ≠ 0)
    (hI0 : I ≠ ⊥) (hbig : ∀ p q : V, ∃ z ∈ I, z ∉ Submodule.span F {p, q}) :
    ∃ e : Fin 4 → V, (∀ i, e i ∈ I) ∧
      ∀ i j, B₀ (e i) (e j) = if i.val + j.val = 3 then 1 else 0 := by
  have hskew : ∀ x y, B₀ x y = - B₀ y x := SimsG45.bilin_skew B₀ halt
  have hsymm : ∀ x y, B₀ x y = B₀ y x := fun x y => by rw [hskew x y, CharTwo.neg_eq]
  obtain ⟨e₀, he₀I, he₀0⟩ : ∃ e₀ ∈ I, e₀ ≠ 0 := by
    obtain ⟨⟨x, hx⟩, hx0⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp hI0
    exact ⟨x, hx, fun h => hx0 (Subtype.ext h)⟩
  obtain ⟨y, hyI, hy0⟩ := hnd e₀ he₀I he₀0
  obtain ⟨e₃, he₃⟩ : ∃ e₃ : V, e₃ = (B₀ e₀ y)⁻¹ • y := ⟨_, rfl⟩
  have he₃I : e₃ ∈ I := he₃ ▸ hsm _ (F₀.inv_mem (hval e₀ he₀I y hyI)) y hyI
  have p03 : B₀ e₀ e₃ = 1 := by rw [he₃, map_smul, smul_eq_mul, inv_mul_cancel₀ hy0]
  obtain ⟨P, hP⟩ : ∃ P : V → V, ∀ w, P w = w - B₀ w e₃ • e₀ + B₀ w e₀ • e₃ :=
    ⟨_, fun _ => rfl⟩
  have hPI : ∀ w ∈ I, P w ∈ I := fun w hw => by
    rw [hP]
    exact I.add_mem (I.sub_mem hw (hsm _ (hval w hw e₃ he₃I) e₀ he₀I))
      (hsm _ (hval w hw e₀ he₀I) e₃ he₃I)
  have hP0 : ∀ w, B₀ (P w) e₀ = 0 := fun w => by
    rw [hP]
    simp only [LinearMap.map_add₂, LinearMap.map_sub₂, LinearMap.map_smul₂, smul_eq_mul, halt,
      hskew e₃ e₀, p03]
    ring
  have hP3 : ∀ w, B₀ (P w) e₃ = 0 := fun w => by
    rw [hP]
    simp only [LinearMap.map_add₂, LinearMap.map_sub₂, LinearMap.map_smul₂, smul_eq_mul, halt,
      p03]
    ring
  have hPx : ∀ x w, B₀ x e₀ = 0 → B₀ x e₃ = 0 → B₀ x (P w) = B₀ x w := fun x w h0 h3 => by
    rw [hP]
    simp only [map_add, map_sub, map_smul, smul_eq_mul, h0, h3]
    ring
  obtain ⟨z, hzI, hz⟩ := hbig e₀ e₃
  have he₁0 : P z ≠ 0 := by
    intro h
    apply hz
    have e1 : z = B₀ z e₃ • e₀ - B₀ z e₀ • e₃ + P z := by
      rw [hP]
      abel
    rw [e1, h, add_zero]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  obtain ⟨y', hy'I, hy'0⟩ := hnd (P z) (hPI z hzI) he₁0
  have hs : B₀ (P z) (P y') = B₀ (P z) y' := hPx _ _ (hP0 z) (hP3 z)
  obtain ⟨e₂, he₂⟩ : ∃ e₂ : V, e₂ = (B₀ (P z) y')⁻¹ • P y' := ⟨_, rfl⟩
  have he₂I : e₂ ∈ I := he₂ ▸ hsm _ (F₀.inv_mem (hval _ (hPI z hzI) y' hy'I)) _ (hPI y' hy'I)
  have p12 : B₀ (P z) e₂ = 1 := by rw [he₂, map_smul, smul_eq_mul, hs, inv_mul_cancel₀ hy'0]
  have p20 : B₀ e₂ e₀ = 0 := by
    rw [he₂, LinearMap.map_smul₂, smul_eq_mul, hP0, mul_zero]
  have p23 : B₀ e₂ e₃ = 0 := by
    rw [he₂, LinearMap.map_smul₂, smul_eq_mul, hP3, mul_zero]
  have p10 := hP0 z
  have p13 := hP3 z
  obtain ⟨e, he⟩ : ∃ e : Fin 4 → V, e = ![e₀, P z, e₂, e₃] := ⟨_, rfl⟩
  refine ⟨e, fun i => ?_, fun i j => ?_⟩
  · fin_cases i <;> simp [he, he₀I, hPI z hzI, he₂I, he₃I]
  · have p01 : B₀ e₀ (P z) = 0 := by rw [hsymm, p10]
    have p02 : B₀ e₀ e₂ = 0 := by rw [hsymm, p20]
    have p21 : B₀ e₂ (P z) = 1 := by rw [hsymm, p12]
    have p30 : B₀ e₃ e₀ = 1 := by rw [hsymm, p03]
    have p31 : B₀ e₃ (P z) = 0 := by rw [hsymm, p13]
    have p32 : B₀ e₃ e₂ = 0 := by rw [hsymm, p23]
    fin_cases i <;> fin_cases j <;>
      simp [he, halt, p01, p02, p03, p10, p12, p13, p20, p21, p23, p30, p31, p32]

theorem linearIndependent_of_subfield (F₀ : Subfield F) {I : AddSubgroup V} (B₀ : BilinForm F V)
    (hsm : ∀ c ∈ F₀, ∀ x ∈ I, c • x ∈ I) (hval : ∀ x ∈ I, ∀ y ∈ I, B₀ x y ∈ F₀)
    (hnd : ∀ x ∈ I, (∀ y ∈ I, B₀ y x = 0) → x = 0)
    {ι : Type} [Fintype ι] (v : ι → V) (hv : ∀ i, v i ∈ I) (hli : LinearIndependent F₀ v) :
    LinearIndependent F v := by
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro l hl i
  refine (Module.forall_dual_apply_eq_zero_iff F₀ (l i)).mp fun π => ?_
  have hw : ∑ j, π (l j) • v j = 0 := by
    refine hnd _ (AddSubgroup.sum_mem _ fun j _ => ?_) fun y hy => ?_
    · rw [Subfield.smul_def]
      exact hsm _ (π (l j)).2 _ (hv j)
    let t : ι → F₀ := fun j => ⟨B₀ y (v j), hval y hy (v j) (hv j)⟩
    have hL : B₀ y (∑ j, π (l j) • v j) = ∑ j, (π (l j) : F) * (t j : F) := by
      simp only [map_sum, Subfield.smul_def, map_smul, smul_eq_mul]
      rfl
    have hR : ((π (∑ j, t j • l j) : F₀) : F) = ∑ j, (π (l j) : F) * (t j : F) := by
      rw [map_sum]
      simp only [map_smul, smul_eq_mul]
      push_cast
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have h0 : ∑ j, t j • l j = 0 := by
      have e1 : ∑ j, t j • l j = B₀ y (∑ j, l j • v j) := by
        simp only [map_sum, map_smul, smul_eq_mul, Subfield.smul_def]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      rw [e1, hl, map_zero]
    rw [hL, ← hR, h0, map_zero, ZeroMemClass.coe_zero]
  exact hli _ hw i

theorem card_eq_pow_of_basis (F₀ : Subfield F) {I : AddSubgroup V}
    (hsm : ∀ c ∈ F₀, ∀ x ∈ I, c • x ∈ I) (e : Module.Basis (Fin 4) F V) (he : ∀ i, e i ∈ I)
    (hrepr : ∀ x ∈ I, ∀ i, e.repr x i ∈ F₀) : Nat.card I = Nat.card F₀ ^ 4 := by
  let Φ : I → (Fin 4 → F₀) := fun x i => ⟨e.repr x i, hrepr x x.2 i⟩
  have hbij : Function.Bijective Φ := by
    refine ⟨fun x y hxy => ?_, fun c => ?_⟩
    · apply Subtype.ext
      apply e.repr.injective
      ext i
      exact congrArg Subtype.val (congrFun hxy i)
    · refine ⟨⟨∑ i, (c i : F) • e i, AddSubgroup.sum_mem _ fun i _ => hsm _ (c i).2 _ (he i)⟩,
        funext fun i => Subtype.ext ?_⟩
      show e.repr (∑ i, (c i : F) • e i) i = c i
      rw [e.repr_sum_self]
  rw [Nat.card_eq_of_bijective Φ hbij, Nat.card_fun]
  simp

theorem card_fix_mul {F₀ : Subfield F} {I : AddSubgroup V} (hsm : ∀ c ∈ F₀, ∀ x ∈ I, c • x ∈ I)
    (B : BilinForm F V) {a : V ≃ₗ[F] V} {x₀ y₀ : V} {ν : F} (hx₀0 : x₀ ≠ 0) (hν : ν ≠ 0)
    (ha : ∀ v, a v = v + (ν * B v x₀) • x₀) (hcoef : ∀ y ∈ I, ν * B y x₀ ∈ F₀) (hy₀ : y₀ ∈ I)
    (hy₀1 : ν * B y₀ x₀ = 1) :
    Nat.card {y : I // a y = y} * Nat.card F₀ = Nat.card I := by
  let ψ : I →+ F₀ := AddMonoidHom.mk' (fun y => ⟨ν * B y x₀, hcoef y y.2⟩) fun y z => by
    apply Subtype.ext
    simp [mul_add]
  have hsurj : Function.Surjective ψ := fun t => ⟨⟨(t : F) • y₀, hsm _ t.2 _ hy₀⟩, by
    apply Subtype.ext
    show ν * B ((t : F) • y₀) x₀ = t
    rw [LinearMap.map_smul₂, smul_eq_mul, mul_left_comm, hy₀1, mul_one]⟩
  have hker : ∀ y : I, y ∈ ψ.ker ↔ a y = y := by
    intro y
    rw [AddMonoidHom.mem_ker, ha y]
    constructor
    · intro h
      have h' : ν * B y x₀ = 0 := congrArg Subtype.val h
      rw [h', zero_smul, add_zero]
    · intro h
      apply Subtype.ext
      have h1 : (ν * B y x₀) • x₀ = 0 := add_eq_left.mp h
      exact (smul_eq_zero.mp h1).resolve_right hx₀0
  rw [← AddSubgroup.card_ker_mul_card_of_surjective hsurj]
  congr 1
  exact Nat.card_congr (Equiv.subtypeEquivRight hker).symm

theorem exists_normal_form (B : BilinForm F V) (halt : ∀ x, B x x = 0)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) {a : V ≃ₗ[F] V} (haSp : a ∈ spGroup B)
    (haT : IsTransv a) {I : AddSubgroup V} (hspan : Submodule.span F (I : Set V) = ⊤)
    (haI : ∀ x ∈ I, a x ∈ I) :
    ∃ x₀ ∈ I, x₀ ≠ 0 ∧ ∃ ν : F, ν ≠ 0 ∧ ∀ v, a v = v + (ν * B v x₀) • x₀ := by
  obtain ⟨u, hu0, c, hc0, hau, -⟩ := SimsG45.exists_transv_form B halt hnd a haSp haT.1
  obtain ⟨y₀, hy₀, hmov⟩ : ∃ y₀ ∈ I, a y₀ ≠ y₀ := by
    by_contra hcon
    push Not at hcon
    have hle : Submodule.span F (I : Set V) ≤
        LinearMap.ker ((a : V →ₗ[F] V) - LinearMap.id) :=
      Submodule.span_le.mpr fun z hz => by
        rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
          LinearEquiv.coe_coe, hcon z hz, sub_self]
    have hfix : ∀ v, a v = v := fun v => by
      have hv : v ∈ LinearMap.ker ((a : V →ₗ[F] V) - LinearMap.id) :=
        hle (by rw [hspan]; exact Submodule.mem_top)
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe,
        sub_eq_zero] at hv
      exact hv
    apply hu0
    apply hnd u
    intro y
    have h1 : y + (c * B y u) • u = y + 0 := by rw [add_zero, ← hau y, hfix y]
    rcases smul_eq_zero.mp (add_left_cancel h1) with h2 | h2
    · rw [SimsG45.bilin_skew B halt u y, (mul_eq_zero.mp h2).resolve_left hc0, neg_zero]
    · exact absurd h2 hu0
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = c * B y₀ u := ⟨_, rfl⟩
  have hμ0 : μ ≠ 0 := by
    intro h0
    apply hmov
    rw [hau y₀, ← hμ, h0, zero_smul, add_zero]
  have hx₀ : μ • u = a y₀ - y₀ := by
    rw [hau y₀, ← hμ]
    abel
  refine ⟨μ • u, by rw [hx₀]; exact I.sub_mem (haI y₀ hy₀) hy₀, smul_ne_zero hμ0 hu0,
    c * μ⁻¹ * μ⁻¹, mul_ne_zero (mul_ne_zero hc0 (inv_ne_zero hμ0)) (inv_ne_zero hμ0),
    fun v => ?_⟩
  rw [hau v, map_smul, smul_eq_mul, smul_smul,
    show c * μ⁻¹ * μ⁻¹ * (μ * B v u) * μ = c * B v u by field_simp]

section Descent

variable {G : Subgroup (V ≃ₗ[F] V)} {I : AddSubgroup V} {F₀ : Subfield F}

theorem coeff_mem (hF₀ : ∀ c, c ∈ F₀ ↔ ∀ x ∈ I, c • x ∈ I)
    (hIinv : ∀ g ∈ G, ∀ x ∈ I, g x ∈ I)
    (hImin : ∀ Y : AddSubgroup V, Y ≤ I → (∀ g ∈ G, ∀ y ∈ Y, g y ∈ Y) → Y = ⊥ ∨ Y = I)
    {B : BilinForm F V} {a : V ≃ₗ[F] V} (haG : a ∈ G) {x₀ : V} (hx₀ : x₀ ∈ I) (hx₀0 : x₀ ≠ 0)
    {ν : F} (ha : ∀ v, a v = v + (ν * B v x₀) • x₀) {y : V} (hy : y ∈ I) :
    ν * B y x₀ ∈ F₀ := by
  rw [hF₀]
  refine smul_mem_of_smul_mem hIinv hImin hx₀ hx₀0 ?_
  have e : (ν * B y x₀) • x₀ = a y - y := by
    rw [ha y]
    abel
  rw [e]
  exact I.sub_mem (hIinv a haG y hy) hy

theorem form_mem (hF₀ : ∀ c, c ∈ F₀ ↔ ∀ x ∈ I, c • x ∈ I)
    (hIinv : ∀ g ∈ G, ∀ x ∈ I, g x ∈ I)
    (hImin : ∀ Y : AddSubgroup V, Y ≤ I → (∀ g ∈ G, ∀ y ∈ Y, g y ∈ Y) → Y = ⊥ ∨ Y = I)
    {B : BilinForm F V} (hGSp : G ≤ spGroup B) {a : V ≃ₗ[F] V} (haG : a ∈ G) {x₀ : V}
    (hx₀ : x₀ ∈ I) (hx₀0 : x₀ ≠ 0) {ν : F} (ha : ∀ v, a v = v + (ν * B v x₀) • x₀) :
    ∀ x ∈ I, ∀ y ∈ I, ν * B x y ∈ F₀ := by
  let T : AddSubgroup V :=
    { carrier := {x | x ∈ I ∧ ∀ y ∈ I, ν * B y x ∈ F₀}
      zero_mem' := ⟨I.zero_mem, fun y _ => by rw [map_zero, mul_zero]; exact F₀.zero_mem⟩
      add_mem' := fun {x x'} hx hx' => ⟨I.add_mem hx.1 hx'.1, fun y hy => by
        rw [map_add, mul_add]
        exact F₀.add_mem (hx.2 y hy) (hx'.2 y hy)⟩
      neg_mem' := fun {x} hx => ⟨I.neg_mem hx.1, fun y hy => by
        rw [map_neg, mul_neg]
        exact F₀.neg_mem (hx.2 y hy)⟩ }
  have hTI : T ≤ I := fun x hx => hx.1
  have hT : ∀ g ∈ G, ∀ x ∈ T, g x ∈ T := by
    intro g hg x hx
    refine ⟨hIinv g hg x hx.1, fun y hy => ?_⟩
    have e : B y (g x) = B (g⁻¹ y) x := by
      have h1 : B (g (g⁻¹ y)) (g x) = B (g⁻¹ y) x := hGSp hg (g⁻¹ y) x
      rwa [show g (g⁻¹ y) = y from g.apply_symm_apply y] at h1
    rw [e]
    exact hx.2 _ (hIinv _ (G.inv_mem hg) y hy)
  have hx₀T : x₀ ∈ T := ⟨hx₀, fun y hy => coeff_mem hF₀ hIinv hImin haG hx₀ hx₀0 ha hy⟩
  have hTeq := eq_of_minimal hImin hTI hT hx₀T hx₀0
  intro x hx y hy
  have hy' : y ∈ T := by rw [hTeq]; exact hy
  exact hy'.2 x hx

theorem exists_coeff_eq_one (hF₀ : ∀ c, c ∈ F₀ ↔ ∀ x ∈ I, c • x ∈ I) (B : BilinForm F V)
    (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hspan : Submodule.span F (I : Set V) = ⊤) {x₀ : V} (hx₀0 : x₀ ≠ 0) {ν : F} (hν : ν ≠ 0)
    (hcoef : ∀ y ∈ I, ν * B y x₀ ∈ F₀) : ∃ y₀ ∈ I, ν * B y₀ x₀ = 1 := by
  obtain ⟨y, hy, hyx⟩ : ∃ y ∈ I, B y x₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx₀0 (eq_zero_of_forall_left B halt hnd hspan hcon)
  have ht : ν * B y x₀ ≠ 0 := mul_ne_zero hν hyx
  refine ⟨(ν * B y x₀)⁻¹ • y, (hF₀ _).mp (F₀.inv_mem (hcoef y hy)) y hy, ?_⟩
  rw [LinearMap.map_smul₂, smul_eq_mul, mul_left_comm, inv_mul_cancel₀ ht]

theorem eq_smul_of_commute (hIinv : ∀ g ∈ G, ∀ x ∈ I, g x ∈ I)
    (hImin : ∀ Y : AddSubgroup V, Y ≤ I → (∀ g ∈ G, ∀ y ∈ Y, g y ∈ Y) → Y = ⊥ ∨ Y = I)
    {B : BilinForm F V} {a : V ≃ₗ[F] V} (haG : a ∈ G) {x₀ y₀ : V} (hx₀ : x₀ ∈ I)
    (hx₀0 : x₀ ≠ 0) {ν : F} (ha : ∀ v, a v = v + (ν * B v x₀) • x₀)
    (hcoef : ∀ y ∈ I, ν * B y x₀ ∈ F₀) (hy₀ : y₀ ∈ I) (hy₀1 : ν * B y₀ x₀ = 1) (f : V →+ V)
    (hfI : ∀ x ∈ I, f x ∈ I) (hfG : ∀ g ∈ G, ∀ x ∈ I, f (g x) = g (f x)) :
    ∃ c ∈ F₀, ∀ x ∈ I, f x = c • x := by
  have hay₀ : a y₀ = y₀ + x₀ := by rw [ha y₀, hy₀1, one_smul]
  have hfx₀ : f x₀ = (ν * B (f y₀) x₀) • x₀ := by
    have h1 := hfG a haG y₀ hy₀
    rw [hay₀, map_add, ha (f y₀)] at h1
    exact add_left_cancel h1
  refine ⟨ν * B (f y₀) x₀, hcoef _ (hfI y₀ hy₀), ?_⟩
  obtain ⟨c, hc⟩ : ∃ c, c = ν * B (f y₀) x₀ := ⟨_, rfl⟩
  rw [← hc] at hfx₀ ⊢
  let S : AddSubgroup V :=
    { carrier := {y | y ∈ I ∧ f y = c • y}
      zero_mem' := ⟨I.zero_mem, by rw [map_zero, smul_zero]⟩
      add_mem' := fun {y z} hy hz => ⟨I.add_mem hy.1 hz.1, by rw [map_add, hy.2, hz.2, smul_add]⟩
      neg_mem' := fun {y} hy => ⟨I.neg_mem hy.1, by rw [map_neg, hy.2, smul_neg]⟩ }
  have hSI : S ≤ I := fun y hy => hy.1
  have hS : ∀ g ∈ G, ∀ y ∈ S, g y ∈ S := fun g hg y hy =>
    ⟨hIinv g hg y hy.1, by rw [hfG g hg y hy.1, hy.2, map_smul]⟩
  have hx₀S : x₀ ∈ S := ⟨hx₀, hfx₀⟩
  have hSeq := eq_of_minimal hImin hSI hS hx₀S hx₀0
  intro x hx
  have hx' : x ∈ S := by rw [hSeq]; exact hx
  exact hx'.2

end Descent

section Irred

variable {I : AddSubgroup V} {H : Subgroup (V ≃ₗ[F] V)} {a : V ≃ₗ[F] V}

theorem conj_facts (haa : a * a = 1) (haN : a ∈ Subgroup.normalizer (H : Set (V ≃ₗ[F] V))) :
    (∀ v, a (a v) = v) ∧ (∀ h ∈ H, a * h * a ∈ H) ∧
      ∀ h : V ≃ₗ[F] V, ∀ z, a (h z) = (a * h * a) (a z) := by
  have haa' : ∀ v, a (a v) = v := fun v => by
    change (a * a) v = v
    rw [haa]
    rfl
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  refine ⟨haa', fun h hh => ?_, fun h z => ?_⟩
  · have h1 := (Subgroup.mem_normalizer_iff.mp haN h).mp hh
    rwa [hainv] at h1
  · change a (h z) = a (h (a (a z)))
    rw [haa']

theorem irred_of_card [Finite V] (haa : a * a = 1)
    (haN : a ∈ Subgroup.normalizer (H : Set (V ≃ₗ[F] V)))
    (hIinv : ∀ g ∈ H ⊔ Subgroup.zpowers a, ∀ x ∈ I, g x ∈ I)
    (hImin : ∀ Y : AddSubgroup V, Y ≤ I →
      (∀ g ∈ H ⊔ Subgroup.zpowers a, ∀ y ∈ Y, g y ∈ Y) → Y = ⊥ ∨ Y = I)
    {q : ℕ} (hq : 2 ≤ q) (hcardI : Nat.card I = q ^ 4)
    (hcardC : Nat.card {y : I // a y = y} = q ^ 3) :
    ∀ Y : AddSubgroup V, Y ≤ I → (∀ h ∈ H, ∀ y ∈ Y, h y ∈ Y) → Y = ⊥ ∨ Y = I := by
  intro Y hYI hYH
  obtain ⟨haa', hconj, hcomm⟩ := conj_facts haa haN
  have haG : a ∈ H ⊔ Subgroup.zpowers a := Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  have haI : ∀ x ∈ I, a x ∈ I := hIinv a haG
  let aY : AddSubgroup V :=
    { carrier := {z | a z ∈ Y}
      zero_mem' := by
        show a 0 ∈ Y
        rw [map_zero]
        exact Y.zero_mem
      add_mem' := fun {z w} hz hw => by
        show a (z + w) ∈ Y
        rw [map_add]
        exact Y.add_mem hz hw
      neg_mem' := fun {z} hz => by
        show a (-z) ∈ Y
        rw [map_neg]
        exact Y.neg_mem hz }
  have hmem : ∀ z, z ∈ aY ↔ a z ∈ Y := fun z => Iff.rfl
  have haYI : aY ≤ I := fun z hz => by
    rw [← haa' z]
    exact haI _ (hYI hz)
  have hsup : ∀ g ∈ H ⊔ Subgroup.zpowers a, ∀ y ∈ Y ⊔ aY, g y ∈ Y ⊔ aY := by
    refine invariant_sup_zpowers haa (fun h hh x hx => ?_) (fun x hx => ?_)
    · obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.mp hx
      rw [map_add]
      refine AddSubgroup.add_mem_sup (hYH h hh y hy) ?_
      rw [hmem, hcomm]
      exact hYH _ (hconj h hh) _ hz
    · obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.mp hx
      rw [map_add, add_comm]
      refine AddSubgroup.add_mem_sup hz ?_
      rw [hmem, haa']
      exact hy
  have hinf : ∀ g ∈ H ⊔ Subgroup.zpowers a, ∀ y ∈ Y ⊓ aY, g y ∈ Y ⊓ aY := by
    refine invariant_sup_zpowers haa (fun h hh x hx => ?_) (fun x hx => ?_)
    · refine AddSubgroup.mem_inf.mpr ⟨hYH h hh x hx.1, ?_⟩
      rw [hmem, hcomm]
      exact hYH _ (hconj h hh) _ hx.2
    · refine AddSubgroup.mem_inf.mpr ⟨hx.2, ?_⟩
      rw [hmem, haa']
      exact hx.1
  by_cases hY0 : Y = ⊥
  · exact Or.inl hY0
  have hsupeq : Y ⊔ aY = I := by
    rcases hImin _ (sup_le hYI haYI) hsup with h | h
    · exact absurd (eq_bot_iff.mpr (h ▸ le_sup_left)) hY0
    · exact h
  rcases hImin _ (inf_le_left.trans hYI) hinf with hinf0 | hinfeq
  swap
  · exact Or.inr (le_antisymm hYI (hinfeq ▸ inf_le_left))
  exfalso
  have hinj : Function.Injective (fun p : {y : I // a y = y} × Y =>
      (⟨p.1.1.1 + p.2.1, I.add_mem p.1.1.2 (hYI p.2.2)⟩ : I)) := by
    rintro ⟨⟨⟨c, hcI⟩, hca⟩, ⟨y, hy⟩⟩ ⟨⟨⟨c', hc'I⟩, hc'a⟩, ⟨y', hy'⟩⟩ h
    have hca' : a c = c := hca
    have hc'a' : a c' = c' := hc'a
    have h1 : c + y = c' + y' := congrArg Subtype.val h
    have e1 : c - c' = y' - y := by
      rw [sub_eq_sub_iff_add_eq_add, add_comm y' c']
      exact h1
    have hdY : c - c' ∈ Y := by
      rw [e1]
      exact Y.sub_mem hy' hy
    have hdaY : c - c' ∈ aY := by
      rw [hmem, map_sub, hca', hc'a']
      exact hdY
    have hd : c - c' ∈ Y ⊓ aY := AddSubgroup.mem_inf.mpr ⟨hdY, hdaY⟩
    rw [hinf0, AddSubgroup.mem_bot, sub_eq_zero] at hd
    subst hd
    have hyy : y = y' := add_left_cancel h1
    subst hyy
    rfl
  have hsurj : Function.Surjective (fun p : Y × Y =>
      (⟨p.1.1 + a p.2.1, I.add_mem (hYI p.1.2) (haI _ (hYI p.2.2))⟩ : I)) := by
    rintro ⟨x, hx⟩
    rw [← hsupeq] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.mp hx
    refine ⟨(⟨y, hy⟩, ⟨a z, hz⟩), Subtype.ext ?_⟩
    show y + a (a z) = y + z
    rw [haa']
  have h1 := Nat.card_le_card_of_injective _ hinj
  have h2 := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_prod, hcardC, hcardI] at h1
  rw [Nat.card_prod, hcardI] at h2
  have hm : Nat.card Y ≤ q := by
    have h3 : q ^ 3 * Nat.card Y ≤ q ^ 3 * q := by rw [← pow_succ]; exact h1
    exact Nat.le_of_mul_le_mul_left h3 (by positivity)
  have h3 : q ^ 4 ≤ q ^ 2 := calc
    q ^ 4 ≤ Nat.card Y * Nat.card Y := h2
    _ ≤ q * q := Nat.mul_le_mul hm hm
    _ = q ^ 2 := (sq q).symm
  have h4 : q ^ 2 < q ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

theorem commute_of_commute_H [Finite V] (haa : a * a = 1)
    (haN : a ∈ Subgroup.normalizer (H : Set (V ≃ₗ[F] V)))
    (hHI : ∀ h ∈ H, ∀ x ∈ I, h x ∈ I) (haI : ∀ x ∈ I, a x ∈ I)
    (hirr : ∀ Y : AddSubgroup V, Y ≤ I → (∀ h ∈ H, ∀ y ∈ Y, h y ∈ Y) → Y = ⊥ ∨ Y = I)
    {q : ℕ} (hq : 2 ≤ q) (hcardI : Nat.card I = q ^ 4)
    (hcardC : Nat.card {y : I // a y = y} = q ^ 3)
    (f : V →+ V) (hfI : ∀ x ∈ I, f x ∈ I) (hfH : ∀ h ∈ H, ∀ x ∈ I, f (h x) = h (f x)) :
    ∀ x ∈ I, f (a x) = a (f x) := by
  obtain ⟨haa', hconj, hcomm⟩ := conj_facts haa haN
  by_contra hcon
  push Not at hcon
  obtain ⟨x₁, hx₁, hne⟩ := hcon
  let K : AddSubgroup V :=
    { carrier := {x | x ∈ I ∧ f x = a (f (a x))}
      zero_mem' := ⟨I.zero_mem, by simp⟩
      add_mem' := fun {x y} hx hy => ⟨I.add_mem hx.1 hy.1, by simp only [map_add, hx.2, hy.2]⟩
      neg_mem' := fun {x} hx => ⟨I.neg_mem hx.1, by simp only [map_neg, hx.2]⟩ }
  have hKI : K ≤ I := fun x hx => hx.1
  have hKH : ∀ h ∈ H, ∀ x ∈ K, h x ∈ K := by
    intro h hh x hx
    refine ⟨hHI h hh x hx.1, ?_⟩
    have e2 : ∀ w, a ((a * h * a) w) = h (a w) := fun w => by
      change a (a (h (a w))) = h (a w)
      rw [haa']
    rw [hfH h hh x hx.1, hx.2, hcomm h x, hfH _ (hconj h hh) _ (haI x hx.1), e2]
  rcases hirr K hKI hKH with hK | hK
  · have hinj : Function.Injective (fun p : {y : I // a y = y} × {y : I // a y = y} =>
        (⟨p.1.1.1 + f p.2.1.1, I.add_mem p.1.1.2 (hfI _ p.2.1.2)⟩ : I)) := by
      rintro ⟨⟨⟨c₁, hc₁⟩, ha₁⟩, ⟨⟨c₂, hc₂⟩, ha₂⟩⟩ ⟨⟨⟨d₁, hd₁⟩, hb₁⟩, ⟨⟨d₂, hd₂⟩, hb₂⟩⟩ h
      have ha₁' : a c₁ = c₁ := ha₁
      have ha₂' : a c₂ = c₂ := ha₂
      have hb₁' : a d₁ = d₁ := hb₁
      have hb₂' : a d₂ = d₂ := hb₂
      have h1 : c₁ + f c₂ = d₁ + f d₂ := congrArg Subtype.val h
      have hfw : f (c₂ - d₂) = d₁ - c₁ := by
        rw [map_sub, sub_eq_sub_iff_add_eq_add, add_comm (f c₂) c₁]
        exact h1
      have hamw : a (c₂ - d₂) = c₂ - d₂ := by rw [map_sub, ha₂', hb₂']
      have hw : c₂ - d₂ ∈ K := by
        refine ⟨I.sub_mem hc₂ hd₂, ?_⟩
        show f (c₂ - d₂) = a (f (a (c₂ - d₂)))
        rw [hamw, hfw, map_sub, ha₁', hb₁']
      rw [hK, AddSubgroup.mem_bot, sub_eq_zero] at hw
      subst hw
      have hcd : c₁ = d₁ := add_right_cancel h1
      subst hcd
      rfl
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod, hcardC, hcardI, ← pow_add] at h1
    have h2 : q ^ 4 < q ^ (3 + 3) := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega
  · apply hne
    have hax : a x₁ ∈ K := by
      rw [hK]
      exact haI x₁ hx₁
    rw [hax.2, haa']

end Irred

theorem exists_inv_form (F₀ : Subfield F) {I : AddSubgroup V} (B : BilinForm F V)
    {H : Subgroup (V ≃ₗ[F] V)} (hHSp : H ≤ spGroup B) {ν : F} (hν : ν ≠ 0)
    (hval : ∀ x ∈ I, ∀ y ∈ I, ν * B x y ∈ F₀) (hnd : ∀ x ∈ I, x ≠ 0 → ∃ y ∈ I, B x y ≠ 0) :
    ∃ β : LinearMap.BilinForm F₀ V,
      (∀ h ∈ H, ∀ x ∈ I, ∀ y ∈ I, β (h x) (h y) = β x y) ∧
        ∀ x ∈ I, x ≠ 0 → ∃ y ∈ I, β x y ≠ 0 := by
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap F₀ F)
    (LinearMap.ker_eq_bot.mpr (algebraMap F₀ F).injective)
  have hπ' : ∀ t : F₀, π (t : F) = t := fun t => LinearMap.congr_fun hπ t
  let β : LinearMap.BilinForm F₀ V := LinearMap.mk₂ F₀ (fun x y => π (ν * B x y))
    (fun x x' y => by rw [LinearMap.map_add₂, mul_add, map_add])
    (fun c x y => by
      have e : ν * B (c • x) y = c • (ν * B x y) := by
        simp only [Subfield.smul_def, LinearMap.map_smul₂, smul_eq_mul]
        ring
      rw [e, map_smul])
    (fun x y y' => by rw [map_add, mul_add, map_add])
    (fun c x y => by
      have e : ν * B x (c • y) = c • (ν * B x y) := by
        simp only [Subfield.smul_def, map_smul, smul_eq_mul]
        ring
      rw [e, map_smul])
  refine ⟨β, fun h hh x _ y _ => ?_, fun x hx hx0 => ?_⟩
  · show π (ν * B (h x) (h y)) = π (ν * B x y)
    rw [show B (h x) (h y) = B x y from hHSp hh x y]
  · obtain ⟨y, hy, hxy⟩ := hnd x hx hx0
    refine ⟨y, hy, ?_⟩
    show π (ν * B x y) ≠ 0
    have e : π (ν * B x y) = ⟨ν * B x y, hval x hx y hy⟩ := hπ' ⟨ν * B x y, hval x hx y hy⟩
    rw [e]
    intro h0
    have h1 : ν * B x y = 0 := congrArg Subtype.val h0
    exact hxy ((mul_eq_zero.mp h1).resolve_left hν)

theorem exists_symp_basis_subfield [Finite F] [CharP F 2] (B : BilinForm F V)
    (hdim : Module.finrank F V = 4) {F₀ : Subfield F} {I : AddSubgroup V} {ν : F}
    (e : Fin 4 → V) (he : ∀ i, e i ∈ I)
    (hgram : ∀ i j, ν * B (e i) (e j) = if i.val + j.val = 3 then 1 else 0)
    (hval : ∀ x ∈ I, ∀ y ∈ I, ν * B x y ∈ F₀) {G : Subgroup (V ≃ₗ[F] V)}
    (hGI : ∀ g ∈ G, ∀ x ∈ I, g x ∈ I) :
    ∃ b : Module.Basis (Fin 4) F V, IsSympBasis B b ∧ ∀ g ∈ G, g ∈ subfieldSpOf b F₀ := by
  obtain ⟨s, hs⟩ := isSquare_of_charTwo' ν
  obtain ⟨f, hf_def⟩ : ∃ f : Fin 4 → V, ∀ i, f i = s • e i := ⟨_, fun _ => rfl⟩
  have hf : ∀ i j, B (f i) (f j) = if i.val + j.val = 3 then 1 else 0 := by
    intro i j
    rw [← hgram i j, hs, hf_def, hf_def]
    simp only [LinearMap.map_smul₂, map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hli := linearIndependent_antidiag B hf
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdim])
  have hb : ⇑b = f := coe_basisOfLinearIndependentOfCardEqFinrank hli _
  have hbg : ∀ i j, B (b i) (b j) = if i.val + j.val = 3 then 1 else 0 := by
    rw [hb]
    exact hf
  refine ⟨b, hbg, fun g hg i j => ?_⟩
  rw [LinearMap.toMatrix_apply, repr_antidiag B b hbg _ i, hb]
  simp only [hf_def, LinearEquiv.coe_coe, map_smul, LinearMap.map_smul₂, LinearMap.smul_apply,
    smul_eq_mul]
  rw [← mul_assoc, ← hs]
  exact hval _ (he _) _ (hGI g hg _ (he j))

theorem form_unique [FiniteDimensional F V] (B : BilinForm F V) (halt : ∀ x, B x x = 0)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) {G H : Subgroup (V ≃ₗ[F] V)} (hHirr : IsIrredOnV H)
    (hHG : H ≤ G) (hGSp : G ≤ spGroup B) {a : V ≃ₗ[F] V} (haG : a ∈ G) {x₀ y₀ : V} {ν : F}
    (hx₀0 : x₀ ≠ 0) (ha : ∀ v, a v = v + (ν * B v x₀) • x₀) (hy₀1 : ν * B y₀ x₀ = 1)
    (B' : BilinForm F V) (hB'nd : ∀ x, (∀ y, B' x y = 0) → x = 0)
    (hB'inv : ∀ g ∈ G, ∀ x y, B' (g x) (g y) = B' x y) :
    ∃ c : F, c ≠ 0 ∧ B' = c • B := by
  have halt' : LinearMap.IsAlt B := halt
  have hBnd : B.Nondegenerate := ⟨hnd, fun y hy => hnd y fun x => halt'.eq_iff.mp (hy x)⟩
  let φ : V →ₗ[F] V := (B.toDual hBnd).symm.toLinearMap ∘ₗ B'
  have hφ : ∀ x y, B (φ x) y = B' x y := fun x y =>
    LinearMap.BilinForm.apply_toDual_symm_apply (hB := hBnd) (B' x) y
  have hφg : ∀ g ∈ G, ∀ x, φ (g x) = g (φ x) := by
    intro g hg x
    have h0 : φ (g x) - g (φ x) = 0 := by
      refine hnd _ fun y => ?_
      rw [LinearMap.map_sub₂, hφ, sub_eq_zero]
      have e1 : B' (g x) y = B' x (g⁻¹ y) := by
        have h1 := hB'inv g hg x (g⁻¹ y)
        rwa [show g (g⁻¹ y) = y from g.apply_symm_apply y] at h1
      have e2 : B (g (φ x)) y = B (φ x) (g⁻¹ y) := by
        have h1 : B (g (φ x)) (g (g⁻¹ y)) = B (φ x) (g⁻¹ y) := hGSp hg (φ x) (g⁻¹ y)
        rwa [show g (g⁻¹ y) = y from g.apply_symm_apply y] at h1
      rw [e1, e2, hφ]
    exact sub_eq_zero.mp h0
  have hφx₀ : φ x₀ = (ν * B (φ y₀) x₀) • x₀ := by
    have h1 := hφg a haG y₀
    rw [ha y₀, hy₀1, one_smul, map_add, ha (φ y₀)] at h1
    exact add_left_cancel h1
  obtain ⟨c, hc⟩ : ∃ c, c = ν * B (φ y₀) x₀ := ⟨_, rfl⟩
  rw [← hc] at hφx₀
  have hφc : ∀ v, φ v = c • v := by
    let E : Submodule F V := LinearMap.ker (φ - c • LinearMap.id)
    have hmemE : ∀ v, v ∈ E ↔ φ v = c • v := fun v => by
      simp [E, sub_eq_zero]
    have hEinv : ∀ h ∈ H, ∀ w ∈ E, h w ∈ E := by
      intro h hh w hw
      rw [hmemE] at hw ⊢
      rw [hφg h (hHG hh) w, hw, map_smul]
    rcases hHirr E hEinv with hE | hE
    · exfalso
      apply hx₀0
      have hx₀E : x₀ ∈ E := (hmemE x₀).mpr hφx₀
      rw [hE] at hx₀E
      exact (Submodule.mem_bot F).mp hx₀E
    · intro v
      exact (hmemE v).mp (by rw [hE]; exact Submodule.mem_top)
  refine ⟨c, fun hc0 => hx₀0 (hB'nd x₀ fun y => ?_), ?_⟩
  · rw [← hφ, hφc, hc0, zero_smul, map_zero, LinearMap.zero_apply]
  · ext x y
    rw [← hφ, hφc, LinearMap.map_smul₂, LinearMap.smul_apply, LinearMap.smul_apply]

end G48

open G48 in
theorem g48_descent {F : Type} [Field F] [Finite F] [CharP F 2]
    {V : Type} [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V)
    (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hdim : Module.finrank F V = 4)
    (a : V ≃ₗ[F] V) (haSp : a ∈ spGroup B) (haT : IsTransv a)
    (H : Subgroup (V ≃ₗ[F] V)) (hHSp : H ≤ spGroup B)
    (haN : a ∈ Subgroup.normalizer (H : Set (V ≃ₗ[F] V))) (hHirr : IsIrredOnV H)
    (I : AddSubgroup V) (hI0 : I ≠ ⊥)
    (hIinv : ∀ g ∈ H ⊔ Subgroup.zpowers a, ∀ x ∈ I, g x ∈ I)
    (hImin : ∀ Y : AddSubgroup V, Y ≤ I → (∀ g ∈ H ⊔ Subgroup.zpowers a, ∀ y ∈ Y, g y ∈ Y) →
      Y = ⊥ ∨ Y = I) :
    ∃ F₀ : Subfield F,
      (∀ c ∈ F₀, ∀ x ∈ I, c • x ∈ I) ∧
      (∀ f : V →+ V, (∀ x ∈ I, f x ∈ I) →
        (∀ g ∈ H ⊔ Subgroup.zpowers a, ∀ x ∈ I, f (g x) = g (f x)) →
        ∃ c ∈ F₀, ∀ x ∈ I, f x = c • x) ∧
      (∀ f : V →+ V, (∀ x ∈ I, f x ∈ I) → (∀ h ∈ H, ∀ x ∈ I, f (h x) = h (f x)) →
        ∃ c ∈ F₀, ∀ x ∈ I, f x = c • x) ∧
      (∀ Y : AddSubgroup V, Y ≤ I → (∀ h ∈ H, ∀ y ∈ Y, h y ∈ Y) →
        (∀ c ∈ F₀, ∀ y ∈ Y, c • y ∈ Y) → Y = ⊥ ∨ Y = I) ∧
      (∃ β : LinearMap.BilinForm F₀ V,
        (∀ h ∈ H, ∀ x ∈ I, ∀ y ∈ I, β (h x) (h y) = β x y) ∧
        ∀ x ∈ I, x ≠ 0 → ∃ y ∈ I, β x y ≠ 0) ∧
      (Submodule.span F (I : Set V) = ⊤ ∧
        ∀ (ι : Type) [Fintype ι] (v : ι → V), (∀ i, v i ∈ I) →
          LinearIndependent F₀ v → LinearIndependent F v) ∧
      (∃ b : Module.Basis (Fin 4) F V, IsSympBasis B b ∧
        ∀ g ∈ H ⊔ Subgroup.zpowers a, g ∈ spGroup B ∧ g ∈ subfieldSpOf b F₀) ∧
      (∀ B' : LinearMap.BilinForm F V, (∀ x, B' x x = 0) →
        (∀ x, (∀ y, B' x y = 0) → x = 0) →
        (∀ g ∈ H ⊔ Subgroup.zpowers a, ∀ x y, B' (g x) (g y) = B' x y) →
        ∃ c : F, c ≠ 0 ∧ B' = c • B) := by
  haveI : Module.Finite F V := Module.finite_of_finrank_pos (by rw [hdim]; norm_num)
  haveI : Finite V := Module.finite_of_finite F
  have hHG : H ≤ H ⊔ Subgroup.zpowers a := le_sup_left
  have haG : a ∈ H ⊔ Subgroup.zpowers a := Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  have hGSp : H ⊔ Subgroup.zpowers a ≤ spGroup B :=
    sup_le hHSp (Subgroup.zpowers_le.mpr haSp)
  have hspan := span_eq_top_of_irred hHG hIinv hHirr hI0
  obtain ⟨x₀, hx₀, hx₀0, ν, hν, ha⟩ :=
    exists_normal_form B halt hnd haSp haT hspan (hIinv a haG)
  have haa : a * a = 1 := SimsG45.transv_mul_self B halt ha
  obtain ⟨F₀, hF₀⟩ := exists_stabField (F := F) I
  have hsm : ∀ c ∈ F₀, ∀ x ∈ I, c • x ∈ I := fun c hc => (hF₀ c).mp hc
  have hcoef : ∀ y ∈ I, ν * B y x₀ ∈ F₀ := fun y hy =>
    coeff_mem hF₀ hIinv hImin haG hx₀ hx₀0 ha hy
  have hval : ∀ x ∈ I, ∀ y ∈ I, ν * B x y ∈ F₀ :=
    form_mem hF₀ hIinv hImin hGSp haG hx₀ hx₀0 ha
  have hndI : ∀ x ∈ I, x ≠ 0 → ∃ y ∈ I, B x y ≠ 0 := fun x _ hx0 =>
    exists_ne_zero_of_span B hnd hspan hx0
  obtain ⟨y₀, hy₀, hy₀1⟩ := exists_coeff_eq_one hF₀ B halt hnd hspan hx₀0 hν hcoef
  obtain ⟨e, heI, hgram⟩ := exists_antidiag_family (ν • B) (fun x => by simp [halt]) hsm
    (fun x hx y hy => by simpa using hval x hx y hy)
    (fun x hx hx0 => by
      obtain ⟨y, hy, hxy⟩ := hndI x hx hx0
      exact ⟨y, hy, by simpa [hν] using hxy⟩)
    hI0 (exists_not_mem_span_pair hdim hspan)
  have hgram' : ∀ i j, ν * B (e i) (e j) = if i.val + j.val = 3 then 1 else 0 := fun i j => by
    simpa using hgram i j
  have hli := linearIndependent_antidiag (ν • B) hgram
  let eB := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdim])
  have heB : ⇑eB = e := coe_basisOfLinearIndependentOfCardEqFinrank hli _
  have hrepr : ∀ x ∈ I, ∀ i, eB.repr x i ∈ F₀ := by
    intro x hx i
    rw [repr_antidiag (ν • B) eB (by rw [heB]; exact hgram) x i, heB]
    simpa using hval _ (heI _) x hx
  have hq : 2 ≤ Nat.card F₀ := Finite.one_lt_card
  have hcardI : Nat.card I = Nat.card F₀ ^ 4 :=
    card_eq_pow_of_basis F₀ hsm eB (fun i => by rw [heB]; exact heI i) hrepr
  have hcardC : Nat.card {y : I // a y = y} = Nat.card F₀ ^ 3 := by
    have h1 := card_fix_mul hsm B hx₀0 hν ha hcoef hy₀ hy₀1
    rw [hcardI, show Nat.card F₀ ^ 4 = Nat.card F₀ ^ 3 * Nat.card F₀ by ring] at h1
    exact Nat.eq_of_mul_eq_mul_right (by omega) h1
  have hirr := irred_of_card haa haN hIinv hImin hq hcardI hcardC
  refine ⟨F₀, hsm, fun f hfI hfG => ?_, fun f hfI hfH => ?_, fun Y hYI hYH _ => hirr Y hYI hYH,
    exists_inv_form F₀ B hHSp hν hval hndI, ⟨hspan, fun ι _ v hv hli => ?_⟩, ?_,
    fun B' _ hB'nd hB'inv => ?_⟩
  · exact eq_smul_of_commute hIinv hImin haG hx₀ hx₀0 ha hcoef hy₀ hy₀1 f hfI hfG
  · have hfa := commute_of_commute_H haa haN (fun h hh => hIinv h (hHG hh)) (hIinv a haG) hirr
      hq hcardI hcardC f hfI hfH
    have key := forall_mem_sup_zpowers (H := H) (a := a)
      (P := fun g => g ∈ H ⊔ Subgroup.zpowers a ∧ ∀ x ∈ I, f (g x) = g (f x))
      ⟨one_mem _, fun x _ => rfl⟩
      (fun g₁ g₂ h₁ h₂ => ⟨mul_mem h₁.1 h₂.1, fun x hx => by
        change f (g₁ (g₂ x)) = g₁ (g₂ (f x))
        rw [h₁.2 _ (hIinv _ h₂.1 x hx), h₂.2 x hx]⟩)
      (fun g hg => ⟨inv_mem hg.1, fun x hx => by
        have h1 := hg.2 _ (hIinv _ (inv_mem hg.1) x hx)
        rw [show g (g⁻¹ x) = x from g.apply_symm_apply x] at h1
        rw [h1]
        exact (g.symm_apply_apply _).symm⟩)
      (fun h hh => ⟨hHG hh, hfH h hh⟩) ⟨haG, hfa⟩
    exact eq_smul_of_commute hIinv hImin haG hx₀ hx₀0 ha hcoef hy₀ hy₀1 f hfI
      fun g hg => (key g hg).2
  · exact linearIndependent_of_subfield F₀ (ν • B) hsm
      (fun x hx y hy => by simpa using hval x hx y hy)
      (fun x _ h => eq_zero_of_forall_left B halt hnd hspan fun y hy => by
        simpa [hν] using h y hy)
      v hv hli
  · obtain ⟨b, hb, hbG⟩ := exists_symp_basis_subfield B hdim e heI hgram' hval hIinv
    exact ⟨b, hb, fun g hg => ⟨hGSp hg, hbG g hg⟩⟩
  · exact form_unique B halt hnd hHirr hHG hGSp haG hx₀0 ha hy₀1 B' hB'nd hB'inv

end CFSG.Quasithin.SimsG4
