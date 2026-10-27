module

public import CFSG.Quasithin.Vol2.Ch10SecQ9G22
public import CFSG.Quasithin.Vol2.Ch10SecQ9G21

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I W : Subgroup G} {s : G}

namespace C5Coord

variable (C : C5Coord L W s)

omit [Finite G] in
theorem b_one : C.D.b 1 = 0 := by
  have h := C.D.b_mul 1 W.one_mem 1 W.one_mem
  rw [mul_one] at h
  simpa using h

omit [Finite G] in
theorem c_one : C.c 1 = 0 := by
  have h := C.c_mul 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
  rw [mul_one] at h
  simpa using h

theorem exists_three_of_fix (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h1011 : Stmt10_1_1) (hyp : Hyp10 G T L I)
    (hker : ∀ l : ↥L, (l : G) ∈ Subgroup.centralizer (W : Set G) →
      (l : G) ∈ Subgroup.centralizer (fsuUL T L I : Set G))
    (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hLWs : L ≤ Subgroup.normalizer ((CFSG.conjugate W s : Subgroup G) : Set G))
    {a b : G} (ha : a ∈ W) (hb : b ∈ CFSG.conjugate W s) {γ : L3.Γ} (hγ3 : γ ^ 3 = 1)
    (hγ1 : γ ≠ 1) (hγa : L3.act γ (C.D.b a) = C.D.b a)
    (hγb : L3.act (τ3 γ) (C.c b) = C.c b) : ∃ l ∈ L, orderOf l = 3 ∧ l * (a * b) = a * b * l := by
  obtain ⟨l, hl3, m, -, hlm⟩ := exists_three_lift h37 h38 h1011 hyp C.D.ρ C.D.ρ_surj
    (fun l hl => hker l ((C.D.ker_ρ l).mp hl)) hγ3 hγ1
  have hla : (l : G) * a * (l : G)⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hLW l.2) a).mp ha
  have hlb : (l : G) * b * (l : G)⁻¹ ∈ CFSG.conjugate W s :=
    (Subgroup.mem_normalizer_iff.mp (hLWs l.2) b).mp hb
  have e1 : (l : G) * a * (l : G)⁻¹ = a := by
    refine C.D.b_inj _ hla _ ha ?_
    rw [C.D.equi l a ha, hlm, act_pow_fix hγa]
  have e2 : (l : G) * b * (l : G)⁻¹ = b := by
    refine C.c_inj _ hlb _ hb ?_
    rw [C.c_equi l b hb, hlm, map_pow, act_pow_fix hγb]
  refine ⟨l, l.2, hl3, ?_⟩
  calc (l : G) * (a * b) = ((l : G) * a * (l : G)⁻¹) * ((l : G) * b * (l : G)⁻¹) * l := by group
    _ = a * b * l := by rw [e1, e2]

theorem eq_or_eq_of_card_two {X : Type*} [Finite X] (hX : Nat.card X = 2) {p q : X} (hpq : p ≠ q)
    (r : X) : r = p ∨ r = q := by
  classical
  have := Fintype.ofFinite X
  by_contra hr
  rw [not_or] at hr
  have h3 : ({p, q, r} : Finset X).card = 3 :=
    Finset.card_eq_three.mpr ⟨_, _, _, hpq, fun h => hr.1 h.symm, fun h => hr.2 h.symm, rfl⟩
  have h4 := Finset.card_le_univ ({p, q, r} : Finset X)
  rw [h3, ← Nat.card_eq_fintype_card, hX] at h4
  omega

omit [Finite G] in
theorem fix_W {k : L3.Γ}
    (hS : ((T ⊓ L).subgroupOf L).map C.D.ρ = SecD.L3.P0.map (MulAut.conj k).toMonoidHom)
    {a' : G} (ha' : a' ∈ W) (hC : ∀ u ∈ T ⊓ L, u * a' * u⁻¹ = a') :
    C.D.b a' = 0 ∨ C.D.b a' = L3.act k e0' := by
  set P := SecD.L3.P0.map (MulAut.conj k).toMonoidHom with hP
  have hP8 : Nat.card P = 8 := by
    rw [hP, Subgroup.card_map_of_injective (MulAut.conj k).injective, SecD.L3.card_P0]
  have hfix : ∀ σ ∈ P, L3.act σ (C.D.b a') = C.D.b a' := by
    intro σ hσ
    rw [← hS] at hσ
    obtain ⟨u, hu, rfl⟩ := hσ
    rw [← C.D.equi u a' ha', hC _ (Subgroup.mem_subgroupOf.mp hu)]
  have hk0 : ∀ σ ∈ P, L3.act σ (L3.act k e0') = L3.act k e0' := by
    rintro σ ⟨p, hp, rfl⟩
    show L3.act (k * p * k⁻¹) (L3.act k e0') = L3.act k e0'
    rw [← L3.act_mul, show k * p * k⁻¹ * k = k * p by group, L3.act_mul, P0_fix_e0 p hp]
  have hne : (⟨0, fun σ _ => L3.act_zero σ⟩ : {v : L3.Vec // ∀ σ ∈ P, L3.act σ v = v}) ≠
      ⟨L3.act k e0', hk0⟩ := by
    intro h
    have h1 := congrArg Subtype.val h
    have h2 : L3.act k e0' = L3.act k 0 := by rw [L3.act_zero]; exact h1.symm
    exact absurd (act_injective k h2) (by decide)
  rcases eq_or_eq_of_card_two (SecD.L3.card_fix_of_card_eq_eight hP8) hne ⟨_, hfix⟩ with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val h)

omit [Finite G] in
theorem fix_Ws {k : L3.Γ}
    (hS : ((T ⊓ L).subgroupOf L).map C.D.ρ = SecD.L3.P0.map (MulAut.conj k).toMonoidHom)
    {b' : G} (hb' : b' ∈ CFSG.conjugate W s) (hC : ∀ u ∈ T ⊓ L, u * b' * u⁻¹ = b') :
    C.c b' = 0 ∨ C.c b' = L3.act (τ3 k) e2' := by
  set P := (SecD.L3.P0.map (MulAut.conj k).toMonoidHom).map τ3.toMonoidHom with hP
  have hP8 : Nat.card P = 8 := by
    rw [hP, Subgroup.card_map_of_injective τ3.injective,
      Subgroup.card_map_of_injective (MulAut.conj k).injective, SecD.L3.card_P0]
  have hfix : ∀ σ ∈ P, L3.act σ (C.c b') = C.c b' := by
    intro σ hσ
    rw [hP, ← hS] at hσ
    obtain ⟨_, ⟨u, hu, rfl⟩, rfl⟩ := hσ
    show L3.act (τ3 (C.D.ρ u)) (C.c b') = C.c b'
    rw [← C.c_equi u b' hb', hC _ (Subgroup.mem_subgroupOf.mp hu)]
  have hk0 : ∀ σ ∈ P, L3.act σ (L3.act (τ3 k) e2') = L3.act (τ3 k) e2' := by
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    show L3.act (τ3 (k * p * k⁻¹)) (L3.act (τ3 k) e2') = L3.act (τ3 k) e2'
    rw [← L3.act_mul, map_mul, map_mul, map_inv, show τ3 k * τ3 p * (τ3 k)⁻¹ * τ3 k =
      τ3 k * τ3 p by group, L3.act_mul, tau_P0_fix_e2 p hp]
  have hne : (⟨0, fun σ _ => L3.act_zero σ⟩ : {v : L3.Vec // ∀ σ ∈ P, L3.act σ v = v}) ≠
      ⟨L3.act (τ3 k) e2', hk0⟩ := by
    intro h
    have h1 := congrArg Subtype.val h
    have h2 : L3.act (τ3 k) e2' = L3.act (τ3 k) 0 := by rw [L3.act_zero]; exact h1.symm
    exact absurd (act_injective _ h2) (by decide)
  rcases eq_or_eq_of_card_two (SecD.L3.card_fix_of_card_eq_eight hP8) hne ⟨_, hfix⟩ with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val h)

end C5Coord

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
