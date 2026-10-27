module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelClassify

public section

namespace CFSG.StandardType.E6ThreeModel

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three

variable {R : Type} [Group R] {L' : Type} [Group L'] (D : FrameData R)

theorem fix_of_conj_eq (hcen : Subgroup.center R = ⊥) {β : MulAut R} {r : R}
    (h : MulAut.conj r * β * (MulAut.conj r)⁻¹ = β) : β r = r := by
  have h2 : MulAut.conj r * β = β * MulAut.conj r := mul_inv_eq_iff_eq_mul.1 h
  have hc : (β r)⁻¹ * r ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨s, rfl⟩ := β.surjective g
    have h3 := DFunLike.congr_fun h2 s
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv] at h3
    calc β s * ((β r)⁻¹ * r) = (β r)⁻¹ * (β r * β s * (β r)⁻¹) * r := by group
      _ = (β r)⁻¹ * (r * β s * r⁻¹) * r := by rw [h3]
      _ = (β r)⁻¹ * r * β s := by group
  rw [hcen, Subgroup.mem_bot, inv_mul_eq_one] at hc
  exact hc

theorem exists_S {A : Subgroup (MulAut L')} {Φ : A →* Multiplicative (Fin Tag.E6.rank → ZMod 3)}
    (hrange : Φ.range = ⊤ ∨ ∀ x, Multiplicative.ofAdd x ∈ Φ.range ↔ x ∈ NoOffRest.hypE6) :
    ∃ S : Set (Fin Tag.E6.rank → ZMod 3),
      (S = Set.univ ∨ S = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3))) ∧
        ∀ x, Multiplicative.ofAdd x ∈ Φ.range ↔ x ∈ S := by
  rcases hrange with h | h
  · exact ⟨Set.univ, Or.inl rfl, fun x => by simp [h]⟩
  · exact ⟨_, Or.inr rfl, h⟩

theorem act_clause {ρ : MulAut L' →* MulAut R} {A : Subgroup (MulAut L')}
    {Φ : A →* Multiplicative (Fin Tag.E6.rank → ZMod 3)}
    (hΦ : ∀ a : A, D.diag (Φ a) = ρ a) {S : Set (Fin Tag.E6.rank → ZMod 3)}
    (hS : ∀ x, Multiplicative.ofAdd x ∈ Φ.range ↔ x ∈ S) {α : MulAut L'}
    (hα : α ∈ Subgroup.normalizer (A : Set (MulAut L'))) :
    (∀ x ∈ S, ∃ y ∈ S, ρ α * D.ad x * (ρ α)⁻¹ = D.ad y) ∧
      ∀ a b : A, (b : MulAut L') = α * a * α⁻¹ →
        ρ α * D.ad (Multiplicative.toAdd (Φ a)) * (ρ α)⁻¹ = D.ad (Multiplicative.toAdd (Φ b)) := by
  have key : ∀ a b : A, (b : MulAut L') = α * a * α⁻¹ →
      ρ α * D.ad (Multiplicative.toAdd (Φ a)) * (ρ α)⁻¹ = D.ad (Multiplicative.toAdd (Φ b)) := by
    intro a b hb
    have h1 : ρ b = ρ α * ρ a * (ρ α)⁻¹ := by rw [hb, map_mul, map_mul, map_inv]
    change ρ α * D.diag (Φ a) * (ρ α)⁻¹ = D.diag (Φ b)
    rw [hΦ a, hΦ b, h1]
  refine ⟨fun x hx => ?_, key⟩
  obtain ⟨a, ha⟩ := (hS x).2 hx
  have hmem : α * (a : MulAut L') * α⁻¹ ∈ A := ((Subgroup.mem_normalizer_iff.1 hα) a).1 a.2
  refine ⟨Multiplicative.toAdd (Φ ⟨_, hmem⟩), (hS _).1 ⟨_, rfl⟩, ?_⟩
  have := key a ⟨_, hmem⟩ rfl
  rwa [show Multiplicative.toAdd (Φ a) = x by rw [ha]; rfl] at this

theorem nb_word_act (hD : D.WeylOK) (ω : List (Fin 6)) (x : Fin Tag.E6.rank → ZMod 3) :
    MulAut.conj (ω.map D.nb).prod * D.ad x * (MulAut.conj (ω.map D.nb).prod)⁻¹ =
      D.ad (adWord .E6 3 ω x) := by
  induction ω generalizing x with
  | nil =>
    simp only [List.map_nil, List.prod_nil, map_one, inv_one, one_mul, mul_one]
    rfl
  | cons i ω ih =>
    have h1 := hD.2.2.1 i (adWord .E6 3 ω x)
    rw [List.map_cons, List.prod_cons, map_mul]
    calc MulAut.conj (D.nb i) * MulAut.conj (ω.map D.nb).prod * D.ad x *
          (MulAut.conj (D.nb i) * MulAut.conj (ω.map D.nb).prod)⁻¹
        = MulAut.conj (D.nb i) * (MulAut.conj (ω.map D.nb).prod * D.ad x *
            (MulAut.conj (ω.map D.nb).prod)⁻¹) * (MulAut.conj (D.nb i))⁻¹ := by group
      _ = MulAut.conj (D.nb i) * D.ad (adWord .E6 3 ω x) * (MulAut.conj (D.nb i))⁻¹ := by rw [ih]
      _ = D.ad (adWord .E6 3 (i :: ω) x) := h1

theorem inner_automizer_clause (hD : D.Good) {ψ : L' →* R} (hψ : Function.Surjective ψ)
    {ρ : MulAut L' →* MulAut R} (hρ : ∀ a l, ρ a (ψ l) = ψ (a l))
    {A : Subgroup (MulAut L')} {Φ : A →* Multiplicative (Fin Tag.E6.rank → ZMod 3)}
    (hΦ : ∀ a : A, D.diag (Φ a) = ρ a)
    (hrange : Φ.range = ⊤ ∨ ∀ x, Multiplicative.ofAdd x ∈ Φ.range ↔ x ∈ NoOffRest.hypE6) :
    ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      ∃ u : WeylGroup .E6, ∀ a b : A,
        (b : MulAut L') = MulAut.conj n * a * (MulAut.conj n)⁻¹ →
          Multiplicative.toAdd (Φ b) = adAct .E6 3 u (Multiplicative.toAdd (Φ a)) := by
  intro n hn
  obtain ⟨S, hSc, hS⟩ := exists_S hrange
  obtain ⟨hnorm, hact⟩ := act_clause D hΦ hS hn
  rw [rho_conj hψ hρ n] at hnorm hact
  obtain ⟨u, hu⟩ := hD.norm (ψ n) S hSc hnorm
  refine ⟨u, fun a b hb => ?_⟩
  have hxS : Multiplicative.toAdd (Φ a) ∈ S := (hS _).1 ⟨a, rfl⟩
  have h1 := hact a b hb
  rw [hu _ hxS] at h1
  exact (congrArg Multiplicative.toAdd (hD.faithful h1)).symm

theorem full_automizer_clause (hD : D.Good) {ψ : L' →* R} (hψ : Function.Surjective ψ)
    {ρ : MulAut L' →* MulAut R} (hρ : ∀ a l, ρ a (ψ l) = ψ (a l))
    {A : Subgroup (MulAut L')} {Φ : A →* Multiplicative (Fin Tag.E6.rank → ZMod 3)}
    (hΦ : ∀ a : A, D.diag (Φ a) = ρ a)
    (hrange : Φ.range = ⊤ ∨ ∀ x, Multiplicative.ofAdd x ∈ Φ.range ↔ x ∈ NoOffRest.hypE6) :
    ∀ α : MulAut L', α ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      ∃ (c : ZMod 3) (u : WeylGroup .E6), c ≠ 0 ∧ ∀ a b : A, (b : MulAut L') = α * a * α⁻¹ →
        Multiplicative.toAdd (Φ b) = c • adAct .E6 3 u (Multiplicative.toAdd (Φ a)) := by
  intro α hα
  obtain ⟨S, hSc, hS⟩ := exists_S hrange
  obtain ⟨hnorm, hact⟩ := act_clause D hΦ hS hα
  obtain ⟨c, u, hc, hu⟩ := hD.aut (ρ α) S hSc hnorm
  refine ⟨c, u, hc, fun a b hb => ?_⟩
  have hxS : Multiplicative.toAdd (Φ a) ∈ S := (hS _).1 ⟨a, rfl⟩
  have h1 := hact a b hb
  rw [hu _ hxS] at h1
  exact (congrArg Multiplicative.toAdd (hD.faithful h1)).symm

theorem normalizer_clause (hD : D.Good) {ψ : L' →* R} (hψ : Function.Surjective ψ)
    {ρ : MulAut L' →* MulAut R} (hρ : ∀ a l, ρ a (ψ l) = ψ (a l))
    {A : Subgroup (MulAut L')} {Φ : A →* Multiplicative (Fin Tag.E6.rank → ZMod 3)}
    (hΦ : ∀ a : A, D.diag (Φ a) = ρ a)
    (hrange : Φ.range = ⊤ ∨ ∀ x, Multiplicative.ofAdd x ∈ Φ.range ↔ x ∈ NoOffRest.hypE6)
    {w : Fin 6 → L'} (hw : ∀ i, ψ (w i) = D.nb i) :
    ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      ∃ v ∈ Subgroup.closure (Set.range w), n * v⁻¹ ∈ D.Tor.comap ψ := by
  intro n hn
  obtain ⟨S, hSc, hS⟩ := exists_S hrange
  obtain ⟨hnorm, -⟩ := act_clause D hΦ hS hn
  rw [rho_conj hψ hρ n] at hnorm
  obtain ⟨u, hu⟩ := hD.norm (ψ n) S hSc hnorm
  have hS_hyp : ∀ x ∈ NoOffRest.hypE6, x ∈ S := by
    rcases hSc with h | h
    · intro x _
      rw [h]
      exact Set.mem_univ _
    · intro x hx
      rw [h]
      exact hx
  obtain ⟨ω, rfl⟩ : ∃ ω : List (Fin 6), (coxeterSystem .E6).wordProd ω = u :=
    (coxeterSystem .E6).wordProd_surjective u
  have hψw : ∀ ω : List (Fin 6), ψ (ω.map w).prod = (ω.map D.nb).prod := by
    intro ω
    induction ω with
    | nil => simp
    | cons i ω ih => simp only [List.map_cons, List.prod_cons, map_mul, ih, hw]
  set v : L' := (ω.map w).prod with hv
  have hvmem : v ∈ Subgroup.closure (Set.range w) := by
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hψv : ψ v = (ω.map D.nb).prod := hψw ω
  have hP : ∀ y, MulAut.conj (ω.map D.nb).prod * D.ad y * (MulAut.conj (ω.map D.nb).prod)⁻¹ =
      D.ad (adAct .E6 3 ((coxeterSystem .E6).wordProd ω) y) := fun y =>
    (nb_word_act D hD.weyl ω y).trans (congrArg D.ad (adWord_eq_adAct (τ := .E6) (p := 3) ω y))
  refine ⟨v, hvmem, ?_⟩
  rw [Subgroup.mem_comap, map_mul, map_inv, hψv]
  refine (hD.cent _).1 fun x hx => ?_
  have hy : adAct .E6 3 ((coxeterSystem .E6).wordProd ω)⁻¹ x ∈ NoOffRest.hypE6 :=
    NoOffRest.adAct_mem_hypE6 _ hx
  have hyx : adAct .E6 3 ((coxeterSystem .E6).wordProd ω)
      (adAct .E6 3 ((coxeterSystem .E6).wordProd ω)⁻¹ x) = x := by
    rw [← adAct_mul, mul_inv_cancel, adAct_one]
  have hPy := hP (adAct .E6 3 ((coxeterSystem .E6).wordProd ω)⁻¹ x)
  have hQy := hu _ (hS_hyp _ hy)
  rw [hyx] at hPy hQy
  apply fix_of_conj_eq hD.center
  rw [map_mul, map_inv]
  have h1 : (MulAut.conj (ω.map D.nb).prod)⁻¹ * D.ad x * MulAut.conj (ω.map D.nb).prod =
      D.ad (adAct .E6 3 ((coxeterSystem .E6).wordProd ω)⁻¹ x) := by
    rw [← hPy]
    group
  calc MulAut.conj (ψ n) * (MulAut.conj (ω.map D.nb).prod)⁻¹ * D.ad x *
        (MulAut.conj (ψ n) * (MulAut.conj (ω.map D.nb).prod)⁻¹)⁻¹
      = MulAut.conj (ψ n) * ((MulAut.conj (ω.map D.nb).prod)⁻¹ * D.ad x *
          MulAut.conj (ω.map D.nb).prod) * (MulAut.conj (ψ n))⁻¹ := by group
    _ = MulAut.conj (ψ n) * D.ad (adAct .E6 3 ((coxeterSystem .E6).wordProd ω)⁻¹ x) *
          (MulAut.conj (ψ n))⁻¹ := by rw [h1]
    _ = D.ad x := hQy

end CFSG.StandardType.E6ThreeModel
