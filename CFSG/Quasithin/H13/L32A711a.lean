module

public import CFSG.Quasithin.H13.ModelsSymplectic

public section

namespace CFSG.Quasithin.H13.L32A.Sp5

open Matrix

abbrev Ix : Type := Fin 3 ⊕ Fin 3

abbrev Mat : Type := Matrix Ix Ix (ZMod 2)

abbrev Vec : Type := Ix → ZMod 2

abbrev Sp : Type := Matrix.symplecticGroup (Fin 3) (ZMod 2)

@[expose] def ofT (t : Matrix (Fin 6) (Fin 6) (ZMod 2)) : Mat :=
  Matrix.of fun i j => t (finSumFinEquiv i) (finSumFinEquiv j)

@[expose] def vecT (t : Fin 6 → ZMod 2) : Vec := fun i => t (finSumFinEquiv i)

@[expose] def x0T : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 1, 0, 0, 1, 0; 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0; 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def y0T : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0;
    0, 0, 1, 0, 0, 1]

@[expose] def biT : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0; 0, 1, 0, 1, 0, 0; 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def x0M : Mat := ofT x0T

@[expose] def y0M : Mat := ofT y0T

@[expose] def biM : Mat := ofT biT

@[expose] def pM : Mat := 1 + x0M + x0M * x0M + x0M * x0M * x0M + x0M * x0M * x0M * x0M

@[expose] def eV : Vec := vecT ![1, 0, 0, 0, 0, 0]

@[expose] def w0V : Vec := vecT ![0, 0, 1, 0, 0, 0]

@[expose] def w1V : Vec := vecT ![0, 0, 0, 0, 0, 1]

@[expose] def cols (a b c : Vec) : Fin 6 → Vec :=
  ![a, x0M *ᵥ a, x0M *ᵥ (x0M *ᵥ a), x0M *ᵥ (x0M *ᵥ (x0M *ᵥ a)), b, c]

@[expose] def colMat (v : Fin 6 → Vec) : Mat := Matrix.of fun i j => v (finSumFinEquiv j) i

@[expose] def cand (a b c : Vec) : Mat := colMat (cols a b c) * biM

@[expose, irreducible] def Wp : Finset Vec := Finset.univ.filter fun v => pM *ᵥ v = 0

@[expose, irreducible] def W : Finset Vec := Finset.univ.filter fun v => x0M *ᵥ v = v

@[expose, irreducible] def S : Finset ((Vec × Vec) × Vec) :=
  ((Wp ×ˢ W) ×ˢ W).filter fun t =>
    cand t.1.1 t.1.2 t.2 * Matrix.J (Fin 3) (ZMod 2) * (cand t.1.1 t.1.2 t.2).transpose =
      Matrix.J (Fin 3) (ZMod 2)

theorem card_S : S.card = 30 := by decide +kernel

theorem x0M_mem : x0M ∈ Matrix.symplecticGroup (Fin 3) (ZMod 2) :=
  SymplecticGroup.mem_iff.mpr (by decide +kernel)

theorem y0M_mem : y0M ∈ Matrix.symplecticGroup (Fin 3) (ZMod 2) :=
  SymplecticGroup.mem_iff.mpr (by decide +kernel)

@[expose] def x0 : Sp := ⟨x0M, x0M_mem⟩

@[expose] def y0 : Sp := ⟨y0M, y0M_mem⟩

theorem colMat_cols : colMat (cols eV w0V w1V) * biM = 1 := by decide +kernel

theorem pM_eV : pM *ᵥ eV = 0 := by decide +kernel

theorem x0M_w0V : x0M *ᵥ w0V = w0V := by decide +kernel

theorem x0M_w1V : x0M *ᵥ w1V = w1V := by decide +kernel

theorem x0M_pow : x0M ^ 5 = 1 := by decide +kernel

theorem x0M_ne : x0M ≠ 1 := by decide +kernel

theorem y0M_pow : y0M ^ 3 = 1 := by decide +kernel

theorem y0M_ne : y0M ≠ 1 := by decide +kernel

theorem y0M_comm : y0M * x0M = x0M * y0M := by decide +kernel

theorem mul_colMat (A : Mat) (v : Fin 6 → Vec) :
    A * colMat v = colMat fun k => A *ᵥ v k := by
  ext i j
  simp [colMat, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem mulVec_cols {g : Mat} (hg : g * x0M = x0M * g) (a b c : Vec) :
    (fun k => g *ᵥ cols a b c k) = cols (g *ᵥ a) (g *ᵥ b) (g *ᵥ c) := by
  have h1 : ∀ v : Vec, g *ᵥ (x0M *ᵥ v) = x0M *ᵥ (g *ᵥ v) := fun v => by
    rw [Matrix.mulVec_mulVec, hg, ← Matrix.mulVec_mulVec]
  funext k
  fin_cases k
  · rfl
  · exact h1 a
  · show g *ᵥ (x0M *ᵥ (x0M *ᵥ a)) = x0M *ᵥ (x0M *ᵥ (g *ᵥ a))
    rw [h1, h1]
  · show g *ᵥ (x0M *ᵥ (x0M *ᵥ (x0M *ᵥ a))) = x0M *ᵥ (x0M *ᵥ (x0M *ᵥ (g *ᵥ a)))
    rw [h1, h1, h1]
  · rfl
  · rfl

theorem eq_cand {g : Mat} (hg : g * x0M = x0M * g) :
    g = cand (g *ᵥ eV) (g *ᵥ w0V) (g *ᵥ w1V) := by
  calc g = g * (colMat (cols eV w0V w1V) * biM) := by rw [colMat_cols, Matrix.mul_one]
    _ = (g * colMat (cols eV w0V w1V)) * biM := by rw [Matrix.mul_assoc]
    _ = cand (g *ᵥ eV) (g *ᵥ w0V) (g *ᵥ w1V) := by
      rw [mul_colMat, mulVec_cols hg]
      rfl

theorem comm_pM {g : Mat} (hg : g * x0M = x0M * g) : g * pM = pM * g := by
  have hc : Commute g x0M := hg
  have := ((((Commute.one_right g).add_right hc).add_right (hc.mul_right hc)).add_right
    ((hc.mul_right hc).mul_right hc)).add_right (((hc.mul_right hc).mul_right hc).mul_right hc)
  exact this

@[expose] def trip (g : Mat) : (Vec × Vec) × Vec := ((g *ᵥ eV, g *ᵥ w0V), g *ᵥ w1V)

theorem comm_x0M {g : Sp} (hg : g * x0 = x0 * g) : (g : Mat) * x0M = x0M * (g : Mat) :=
  congrArg Subtype.val hg

theorem trip_injective {g h : Sp} (hg : g * x0 = x0 * g) (hh : h * x0 = x0 * h)
    (e : trip (g : Mat) = trip (h : Mat)) : g = h := by
  simp only [trip, Prod.mk.injEq] at e
  obtain ⟨⟨e1, e2⟩, e3⟩ := e
  apply Subtype.ext
  rw [eq_cand (comm_x0M hg), eq_cand (comm_x0M hh), e1, e2, e3]

theorem mem_S {g : Sp} (hg : g * x0 = x0 * g) : trip (g : Mat) ∈ S := by
  have hc := comm_x0M hg
  have hW : ∀ v : Vec, x0M *ᵥ v = v → x0M *ᵥ ((g : Mat) *ᵥ v) = (g : Mat) *ᵥ v := fun v hv => by
    rw [Matrix.mulVec_mulVec, ← hc, ← Matrix.mulVec_mulVec, hv]
  have hWp : pM *ᵥ ((g : Mat) *ᵥ eV) = 0 := by
    rw [Matrix.mulVec_mulVec, ← comm_pM hc, ← Matrix.mulVec_mulVec, pM_eV, Matrix.mulVec_zero]
  have hsp := SymplecticGroup.mem_iff.mp g.2
  simp only [trip, S, Wp, W, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
  refine ⟨⟨⟨hWp, hW _ x0M_w0V⟩, hW _ x0M_w1V⟩, ?_⟩
  rw [← eq_cand hc]
  exact hsp

theorem card_centralizer_x0_le : Nat.card (Subgroup.centralizer ({x0} : Set Sp)) ≤ 30 := by
  have hcomm : ∀ g : Subgroup.centralizer ({x0} : Set Sp), (g : Sp) * x0 = x0 * (g : Sp) :=
    fun g => Subgroup.mem_centralizer_singleton_iff.mp g.2
  let f : Subgroup.centralizer ({x0} : Set Sp) → {t // t ∈ S} := fun g =>
    Subtype.mk (trip ((g : Sp) : Mat)) (mem_S (hcomm g))
  have hf : Function.Injective f := by
    intro g h hgh
    have h1 : trip ((g : Sp) : Mat) = trip ((h : Sp) : Mat) := congrArg Subtype.val hgh
    exact Subtype.ext (trip_injective (hcomm g) (hcomm h) h1)
  have hS : Nat.card {t // t ∈ S} = 30 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, card_S]
  calc Nat.card (Subgroup.centralizer ({x0} : Set Sp)) ≤ Nat.card {t // t ∈ S} :=
        Nat.card_le_card_of_injective f hf
    _ = 30 := hS

theorem orderOf_x0 : orderOf x0 = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine orderOf_eq_prime (Subtype.ext ?_) fun h => x0M_ne (congrArg Subtype.val h)
  rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
  exact x0M_pow

theorem orderOf_y0 : orderOf y0 = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime (Subtype.ext ?_) fun h => y0M_ne (congrArg Subtype.val h)
  rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
  exact y0M_pow

theorem card_centralizer_x0 :
    Nat.card (Subgroup.centralizer ({x0} : Set Sp)) = 15 ∨
      Nat.card (Subgroup.centralizer ({x0} : Set Sp)) = 30 := by
  have hx : x0 ∈ Subgroup.centralizer ({x0} : Set Sp) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hy : y0 ∈ Subgroup.centralizer ({x0} : Set Sp) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext y0M_comm)
  have h5 : 5 ∣ Nat.card (Subgroup.centralizer ({x0} : Set Sp)) := by
    have := Subgroup.orderOf_dvd_natCard _ hx
    rwa [orderOf_x0] at this
  have h3 : 3 ∣ Nat.card (Subgroup.centralizer ({x0} : Set Sp)) := by
    have := Subgroup.orderOf_dvd_natCard _ hy
    rwa [orderOf_y0] at this
  have hle := card_centralizer_x0_le
  have hpos : 0 < Nat.card (Subgroup.centralizer ({x0} : Set Sp)) := Nat.card_pos
  have h15 : 15 ∣ Nat.card (Subgroup.centralizer ({x0} : Set Sp)) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 h5
  obtain ⟨k, hk⟩ := h15
  rw [hk] at hle hpos ⊢
  have : k = 1 ∨ k = 2 := by omega
  rcases this with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem card_centralizer_eq {x : Sp} (hx : orderOf x = 5) :
    Nat.card (Subgroup.centralizer ({x} : Set Sp)) =
      Nat.card (Subgroup.centralizer ({x0} : Set Sp)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hfin : Finite Sp :=
    Nat.finite_of_card_ne_zero (by rw [card_symplecticGroup_three_two]; norm_num)
  have hcard := card_symplecticGroup_three_two
  have hsyl : ∀ y : Sp, orderOf y = 5 → IsPGroup 5 (Subgroup.zpowers y) ∧
      ¬ 5 ∣ (Subgroup.zpowers y).index := fun y hy => by
    refine ⟨IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one]), fun hd => ?_⟩
    have hm := Subgroup.card_mul_index (Subgroup.zpowers y)
    rw [Nat.card_zpowers, hy, hcard] at hm
    have hi : (Subgroup.zpowers y).index = 290304 := by omega
    rw [hi] at hd
    norm_num at hd
  let P : Sylow 5 Sp := (hsyl x hx).1.toSylow (hsyl x hx).2
  let Q : Sylow 5 Sp := (hsyl x0 orderOf_x0).1.toSylow (hsyl x0 orderOf_x0).2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Sp Q P
  have hgQ : ((g • Q : Sylow 5 Sp) : Subgroup Sp) = Subgroup.zpowers x := by
    rw [hg]
    rfl
  rw [Sylow.coe_subgroup_smul] at hgQ
  have hmem : g * x0 * g⁻¹ ∈ Subgroup.zpowers x := by
    rw [← hgQ]
    exact ⟨x0, Subgroup.mem_zpowers x0, rfl⟩
  have hord : orderOf (g * x0 * g⁻¹) = 5 := by
    have h := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x0
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    rw [h, orderOf_x0]
  have hxmem : x ∈ Subgroup.zpowers (g * x0 * g⁻¹) := by
    have hle : Subgroup.zpowers (g * x0 * g⁻¹) ≤ Subgroup.zpowers x :=
      Subgroup.zpowers_le.mpr hmem
    have heq : Subgroup.zpowers (g * x0 * g⁻¹) = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hx, hord])
    rw [heq]
    exact Subgroup.mem_zpowers x
  have hC : Subgroup.centralizer ({x} : Set Sp) =
      Subgroup.centralizer ({g * x0 * g⁻¹} : Set Sp) := by
    ext c
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      rw [← hk]
      exact (Commute.zpow_right h k : Commute c (x ^ k))
    · intro h
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxmem
      rw [← hk]
      exact (Commute.zpow_right h k : Commute c ((g * x0 * g⁻¹) ^ k))
  rw [hC]
  have hconj : Subgroup.centralizer ({g * x0 * g⁻¹} : Set Sp) =
      (Subgroup.centralizer ({x0} : Set Sp)).map (MulAut.conj g).toMonoidHom := by
    ext c
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      refine ⟨g⁻¹ * c * g, Subgroup.mem_centralizer_singleton_iff.mpr ?_, by simp [mul_assoc]⟩
      calc g⁻¹ * c * g * x0 = g⁻¹ * (c * (g * x0 * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x0 * g⁻¹) * c) * g := by rw [h]
        _ = x0 * (g⁻¹ * c * g) := by group
    · rintro ⟨d, hd, rfl⟩
      have hd' := Subgroup.mem_centralizer_singleton_iff.mp hd
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g * d * g⁻¹ * (g * x0 * g⁻¹) = g * (d * x0) * g⁻¹ := by group
        _ = g * (x0 * d) * g⁻¹ := by rw [hd']
        _ = g * x0 * g⁻¹ * (g * d * g⁻¹) := by group
  rw [hconj]
  exact Nat.card_congr ((Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective).symm.toEquiv)

theorem card_le_two_of_le_centralizer {x : Sp} (hx : orderOf x = 5) {P : Subgroup Sp}
    (hP : IsPGroup 2 P) (hPC : P ≤ Subgroup.centralizer ({x} : Set Sp)) : Nat.card P ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : Finite Sp :=
    Nat.finite_of_card_ne_zero (by rw [card_symplecticGroup_three_two]; norm_num)
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hd := Subgroup.card_dvd_of_le hPC
  rw [card_centralizer_eq hx, hk] at hd
  have hk1 : k ≤ 1 := by
    by_contra h
    push Not at h
    have h4 : 4 ∣ 2 ^ k := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact Nat.pow_dvd_pow 2 h
    rcases card_centralizer_x0 with h15 | h30
    · rw [h15] at hd
      have := h4.trans hd
      norm_num at this
    · rw [h30] at hd
      have := h4.trans hd
      norm_num at this
  rw [hk]
  calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
    _ = 2 := by norm_num

end CFSG.Quasithin.H13.L32A.Sp5
