module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem513LowS5
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem517A5Coord
public import CFSG.Quasithin.Background.InternalSecISec

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Equiv
open scoped IsMulCommutative

section Frame

variable {G : Type} [Group G]

structure S5Frame (Y W : Subgroup G) : Type where
  le : Y ≤ Subgroup.normalizer (W : Set G)
  c : ↥W → Fin 5 → ZMod 2
  c_mul : ∀ u v, c (u * v) = c u + c v
  c_inj : Function.Injective c
  c_sum : ∀ u, ∑ i, c u i = 0
  c_surj : ∀ x : Fin 5 → ZMod 2, ∑ i, x i = 0 → ∃ u, c u = x
  ρ : ↥Y →* Perm (Fin 5)
  ρ_surj : Function.Surjective ρ
  equiv : ∀ (y : ↥Y) (u : ↥W) (hu : (y : G) * u * (y : G)⁻¹ ∈ W),
    c ⟨_, hu⟩ = pmv (ρ y) (c u)

theorem nonempty_s5Frame {Y W : Subgroup G} [IsMulCommutative ↥W]
    (hYW : Y ≤ Subgroup.normalizer (W : Set G))
    (hs : SymmetricNatural (V := ↥W) (autOn Y W) ⊤ ⊥ 5) : Nonempty (S5Frame Y W) := by
  classical
  obtain ⟨π, hπ⟩ : ∃ π : Perm (Fin 5) →* ↥(autOn Y W),
      (FFModel.symDn 5).RealizesVia (autOn Y W) ⊤ ⊥ π := hs
  have hπi : Function.Injective π :=
    G64.RealizesVia.injective_of_faithful' (G64.symDn_faithful le_rfl) hπ
  have hπs : Function.Surjective π := hπ.1
  obtain ⟨vec, hvec_mul, hvec_ker, hvec_sum, hvec_surj, hvec_act⟩ := exists_s5_coords hπ
  let πe : Perm (Fin 5) ≃* ↥(autOn Y W) := MulEquiv.ofBijective π ⟨hπi, hπs⟩
  let φ : ↥Y →* ↥(autOn Y W) := InternalSec.autOnHom hYW
  have hφ : ∀ (y : ↥Y) (u : ↥W),
      (((φ y : ↥(autOn Y W)) : MulAut ↥W) u : G) = y * u * (y : G)⁻¹ :=
    fun y u => CFSG.QuasithinUnique.Setup.rho_apply_coe hYW y u
  have hinj : Function.Injective fun u : ↥W => vec ⟨u, Subgroup.mem_top u⟩ := by
    intro u w huw
    have h1 : vec (⟨u, Subgroup.mem_top u⟩ * (⟨w, Subgroup.mem_top w⟩)⁻¹) = 0 := by
      have h3 := hvec_mul (⟨u, Subgroup.mem_top u⟩ * (⟨w, Subgroup.mem_top w⟩)⁻¹)
        ⟨w, Subgroup.mem_top w⟩
      rw [inv_mul_cancel_right] at h3
      simp only at huw
      rw [huw] at h3
      exact right_eq_add.mp h3
    have h2 := (hvec_ker _).1 h1
    rw [Subgroup.mem_bot] at h2
    exact mul_inv_eq_one.mp h2
  refine ⟨{ le := hYW
            c := fun u => vec ⟨u, Subgroup.mem_top u⟩
            c_mul := fun u v => hvec_mul ⟨u, Subgroup.mem_top u⟩ ⟨v, Subgroup.mem_top v⟩
            c_inj := hinj
            c_sum := fun u => hvec_sum _
            c_surj := fun x hx => ?_
            ρ := πe.symm.toMonoidHom.comp φ
            ρ_surj := πe.symm.surjective.comp (InternalSec.autOnHom_surjective hYW)
            equiv := fun y u hu => ?_ }⟩
  · obtain ⟨u, hu⟩ := hvec_surj x hx
    exact ⟨u.1, hu⟩
  · set σ := πe.symm (φ y) with hσ
    have hπσ : π σ = φ y := πe.apply_symm_apply (φ y)
    have h1 := hvec_act σ ⟨u, Subgroup.mem_top u⟩ (Subgroup.mem_top _)
    have e1 : (⟨((π σ : ↥(autOn Y W)) : MulAut ↥W) (u : ↥W), Subgroup.mem_top _⟩ :
        ↥(⊤ : Subgroup ↥W)) = ⟨⟨_, hu⟩, Subgroup.mem_top _⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      show ((((π σ) : ↥(autOn Y W)) : MulAut ↥W) u : G) = y * u * (y : G)⁻¹
      rw [hπσ, hφ]
    rw [e1] at h1
    exact h1

namespace S5Frame

variable {Y W : Subgroup G}

theorem c_one (F : S5Frame Y W) : F.c 1 = 0 := by
  have h := F.c_mul 1 1
  rw [mul_one] at h
  exact right_eq_add.mp h

theorem c_inv (F : S5Frame Y W) (u : ↥W) : F.c u⁻¹ = F.c u := by
  have h := F.c_mul u u⁻¹
  rw [mul_inv_cancel, c_one] at h
  funext i
  have h1 := congrFun h i
  simp only [Pi.add_apply, Pi.zero_apply] at h1
  exact zmod2_eq_of_zero_eq_add _ _ h1

theorem c_eq_zero_iff (F : S5Frame Y W) (u : ↥W) : F.c u = 0 ↔ u = 1 := by
  constructor
  · intro h
    exact F.c_inj (h.trans F.c_one.symm)
  · rintro rfl
    exact F.c_one

@[expose] def conj (F : S5Frame Y W) (h : Perm (Fin 5)) : S5Frame Y W where
  le := F.le
  c := fun u => pmv h⁻¹ (F.c u)
  c_mul := fun u v => by rw [F.c_mul]; rfl
  c_inj := fun u v huv => by
    apply F.c_inj
    have h1 := congrArg (pmv h) huv
    simp only [← pmv_mul, mul_inv_cancel, pmv_one] at h1
    exact h1
  c_sum := fun u => by
    show ∑ i, F.c u (h⁻¹⁻¹ i) = 0
    rw [inv_inv, Equiv.sum_comp h (F.c u)]
    exact F.c_sum u
  c_surj := fun x hx => by
    have hs : ∑ i, pmv h x i = 0 := by
      show ∑ i, x (h⁻¹ i) = 0
      rw [Equiv.sum_comp h⁻¹ x]
      exact hx
    obtain ⟨u, hu⟩ := F.c_surj (pmv h x) hs
    refine ⟨u, ?_⟩
    show pmv h⁻¹ (F.c u) = x
    rw [hu, ← pmv_mul, inv_mul_cancel, pmv_one]
  ρ := (MulAut.conj h⁻¹).toMonoidHom.comp F.ρ
  ρ_surj := (MulAut.conj h⁻¹).surjective.comp F.ρ_surj
  equiv := fun y u hu => by
    show pmv h⁻¹ (F.c ⟨_, hu⟩) = pmv (h⁻¹ * F.ρ y * h⁻¹⁻¹) (pmv h⁻¹ (F.c u))
    rw [F.equiv, ← pmv_mul, ← pmv_mul, inv_inv, mul_assoc (h⁻¹ * F.ρ y), mul_inv_cancel,
      mul_one]

theorem conj_ρ (F : S5Frame Y W) (h : Perm (Fin 5)) (y : ↥Y) :
    (F.conj h).ρ y = h⁻¹ * F.ρ y * h := by
  show h⁻¹ * F.ρ y * h⁻¹⁻¹ = _
  rw [inv_inv]

theorem ρ_eq_one_iff (F : S5Frame Y W) (y : ↥Y) :
    F.ρ y = 1 ↔ (y : G) ∈ Subgroup.centralizer (W : Set G) := by
  constructor
  · intro h1
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hyu : (y : G) * u * (y : G)⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (F.le y.2) u).mp hu
    have h2 := F.equiv y ⟨u, hu⟩ hyu
    rw [h1, pmv_one] at h2
    have h3 := congrArg Subtype.val (F.c_inj h2)
    simp only at h3
    calc u * (y : G) = (y : G) * u * (y : G)⁻¹ * y := by rw [h3]
      _ = y * u := by group
  · intro hyC
    have hfix : ∀ x : Fin 5 → ZMod 2, ∑ i, x i = 0 → pmv (F.ρ y) x = x := by
      intro x hx
      obtain ⟨u, rfl⟩ := F.c_surj x hx
      have hyu : (y : G) * u * (y : G)⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (F.le y.2) u).mp u.2
      rw [← F.equiv y u hyu]
      congr 1
      apply Subtype.ext
      show (y : G) * u * (y : G)⁻¹ = u
      rw [← Subgroup.mem_centralizer_iff.mp hyC u u.2, mul_inv_cancel_right]
    exact pmv_faithful _ hfix

theorem exists_adapted [Finite G] (F : S5Frame Y W) {T : Subgroup G} (hT : IsSylowTwoOf T Y) :
    ∃ F' : S5Frame Y W, (∀ t : ↥Y, (t : G) ∈ T → InD8 (F'.ρ t)) ∧
      ∀ σ : Perm (Fin 5), InD8 σ → ∃ t : ↥Y, (t : G) ∈ T ∧ F'.ρ t = σ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h, hh⟩ := exists_conj_d8 ((A4.toSylow hT).mapSurjective F.ρ_surj)
  have hmem : ∀ σ, σ ∈ (T.subgroupOf Y).map F.ρ ↔ h⁻¹ * σ * h ∈ d8Sub := hh
  refine ⟨F.conj h, fun t ht => ?_, fun σ hσ => ?_⟩
  · rw [conj_ρ]
    exact (hmem _).1 ⟨t, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  · obtain ⟨t, ht, hteq⟩ := (hmem (h * σ * h⁻¹)).2 (by
      show InD8 (h⁻¹ * (h * σ * h⁻¹) * h)
      rw [show h⁻¹ * (h * σ * h⁻¹) * h = σ by group]
      exact hσ)
    refine ⟨t, Subgroup.mem_subgroupOf.mp ht, ?_⟩
    rw [conj_ρ, hteq]
    group

@[expose] def ρOn (F : S5Frame Y W) {A : Subgroup G} (hAY : A ≤ Y) : ↥A →* Perm (Fin 5) :=
  F.ρ.comp (Subgroup.inclusion hAY)

theorem relIndex_eq_card_range (F : S5Frame Y W) {A : Subgroup G} (hAY : A ≤ Y) :
    (A ⊓ Subgroup.centralizer (W : Set G)).relIndex A = Nat.card (F.ρOn hAY).range := by
  have hker : (F.ρOn hAY).ker = (A ⊓ Subgroup.centralizer (W : Set G)).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    show F.ρ (Subgroup.inclusion hAY a) = 1 ↔ _
    rw [F.ρ_eq_one_iff]
    exact ⟨fun h => ⟨a.2, h⟩, fun h => h.2⟩
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]

theorem card_W [Finite G] (F : S5Frame Y W) : Nat.card W = 16 := by
  classical
  have h1 : Nat.card W = Nat.card {x : Fin 5 → ZMod 2 // ∑ i, x i = 0} :=
    Nat.card_congr (Equiv.ofBijective (fun u => (⟨F.c u, F.c_sum u⟩ :
      {x : Fin 5 → ZMod 2 // ∑ i, x i = 0}))
      ⟨fun u v h => F.c_inj (congrArg Subtype.val h), fun x => by
        obtain ⟨u, hu⟩ := F.c_surj x.1 x.2
        exact ⟨u, Subtype.ext hu⟩⟩)
  rw [h1, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

theorem card_fix_le [Finite G] (F : S5Frame Y W) {A : Subgroup G} {a : ↥Y} (ha : (a : G) ∈ A) :
    Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G)) ≤ fixCard1 (F.ρ a) := by
  classical
  have hfix : ∀ u : ↥(W ⊓ Subgroup.centralizer (A : Set G)),
      F.c ⟨u, u.2.1⟩ ∈ Finset.univ.filter fun x : Fin 5 → ZMod 2 =>
        ∑ i, x i = 0 ∧ pmv (F.ρ a) x = x := by
    intro u
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, F.c_sum _, ?_⟩
    have hau : (a : G) * u * (a : G)⁻¹ ∈ W := by
      rw [Subgroup.mem_centralizer_iff.mp u.2.2 a ha, mul_inv_cancel_right]
      exact u.2.1
    rw [← F.equiv a ⟨u, u.2.1⟩ hau]
    congr 1
    apply Subtype.ext
    show (a : G) * u * (a : G)⁻¹ = u
    rw [Subgroup.mem_centralizer_iff.mp u.2.2 a ha, mul_inv_cancel_right]
  have hinj : Function.Injective fun u : ↥(W ⊓ Subgroup.centralizer (A : Set G)) =>
      (⟨F.c ⟨u, u.2.1⟩, hfix u⟩ : {x // x ∈ Finset.univ.filter fun x : Fin 5 → ZMod 2 =>
        ∑ i, x i = 0 ∧ pmv (F.ρ a) x = x}) := by
    intro u v huv
    have h1 := F.c_inj (congrArg Subtype.val huv)
    exact Subtype.ext (congrArg (fun x : ↥W => (x : G)) h1)
  calc Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G)) ≤ Nat.card {x // x ∈
        Finset.univ.filter fun x : Fin 5 → ZMod 2 => ∑ i, x i = 0 ∧ pmv (F.ρ a) x = x} :=
        Nat.card_le_card_of_injective _ hinj
    _ = fixCard1 (F.ρ a) := Nat.card_eq_finsetCard _

theorem card_fix_le_two [Finite G] (F : S5Frame Y W) {A : Subgroup G} {a b : ↥Y}
    (ha : (a : G) ∈ A) (hb : (b : G) ∈ A) :
    Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G)) ≤ fixCard2 (F.ρ a) (F.ρ b) := by
  classical
  have hfix1 : ∀ (u : ↥(W ⊓ Subgroup.centralizer (A : Set G))) (y : ↥Y), (y : G) ∈ A →
      pmv (F.ρ y) (F.c ⟨u, u.2.1⟩) = F.c ⟨u, u.2.1⟩ := by
    intro u y hy
    have hyu : (y : G) * u * (y : G)⁻¹ ∈ W := by
      rw [Subgroup.mem_centralizer_iff.mp u.2.2 y hy, mul_inv_cancel_right]
      exact u.2.1
    rw [← F.equiv y ⟨u, u.2.1⟩ hyu]
    congr 1
    apply Subtype.ext
    show (y : G) * u * (y : G)⁻¹ = u
    rw [Subgroup.mem_centralizer_iff.mp u.2.2 y hy, mul_inv_cancel_right]
  have hfix : ∀ u : ↥(W ⊓ Subgroup.centralizer (A : Set G)),
      F.c ⟨u, u.2.1⟩ ∈ Finset.univ.filter fun x : Fin 5 → ZMod 2 =>
        ∑ i, x i = 0 ∧ pmv (F.ρ a) x = x ∧ pmv (F.ρ b) x = x := by
    intro u
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, F.c_sum _, hfix1 u a ha, hfix1 u b hb⟩
  have hinj : Function.Injective fun u : ↥(W ⊓ Subgroup.centralizer (A : Set G)) =>
      (⟨F.c ⟨u, u.2.1⟩, hfix u⟩ : {x // x ∈ Finset.univ.filter fun x : Fin 5 → ZMod 2 =>
        ∑ i, x i = 0 ∧ pmv (F.ρ a) x = x ∧ pmv (F.ρ b) x = x}) := by
    intro u v huv
    have h1 := F.c_inj (congrArg Subtype.val huv)
    exact Subtype.ext (congrArg (fun x : ↥W => (x : G)) h1)
  calc Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set G)) ≤ Nat.card {x // x ∈
        Finset.univ.filter fun x : Fin 5 → ZMod 2 =>
          ∑ i, x i = 0 ∧ pmv (F.ρ a) x = x ∧ pmv (F.ρ b) x = x} :=
        Nat.card_le_card_of_injective _ hinj
    _ = fixCard2 (F.ρ a) (F.ρ b) := Nat.card_eq_finsetCard _

end S5Frame

end Frame

end CFSG.Quasithin.H13
