module

public import CFSG.Quasithin.Background.SmithB42LnL5W4
public import CFSG.Quasithin.Background.JonesParshallWords
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.Module
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.Quasithin.B42Ln

open Matrix

local notation "𝕄₄" => Matrix (Fin 4) (Fin 4) (ZMod 2)

instance (M : 𝕄₄) : Decidable (IsUp4 M) := by
  unfold IsUp4
  haveI : ∀ a : Fin 4, Decidable (∀ b : Fin 4, (b < a → M a b = 0) ∧ (a = b → M a b = 1)) :=
    fun _ => Fintype.decidableForallFintype
  exact Fintype.decidableForallFintype

@[expose] def xM4 (s : Fin 3) : 𝕄₄ :=
  Matrix.of fun a b => if a = b then 1 else if a = s.castSucc ∧ b = s.succ then 1 else 0

@[expose] def yM4 (s : Fin 3) : 𝕄₄ :=
  Matrix.of fun a b => if a = b then 1 else if a = s.succ ∧ b = s.castSucc then 1 else 0

@[expose] def pm (σ : Equiv.Perm (Fin 4)) : 𝕄₄ := Matrix.of fun i j => if i = σ j then 1 else 0

abbrev sw (s : Fin 3) : Equiv.Perm (Fin 4) := Equiv.swap s.castSucc s.succ

abbrev lo4 (c : Fin 64) : 𝕄₄ := (up4 c)ᵀ

theorem pm_mul (σ τ : Equiv.Perm (Fin 4)) : pm (σ * τ) = pm σ * pm τ := by
  ext i j
  simp only [pm, Matrix.of_apply, Matrix.mul_apply, Equiv.Perm.mul_apply, ite_mul, one_mul,
    zero_mul]
  rw [Finset.sum_eq_single (τ j)]
  · by_cases h : i = σ (τ j) <;> simp [h]
  · intro b _ hb
    simp [hb]
  · simp

theorem pm_one : pm 1 = 1 := by decide

theorem xM4_mul_self : ∀ s : Fin 3, xM4 s * xM4 s = 1 := by decide

theorem yM4_mul_self : ∀ s : Fin 3, yM4 s * yM4 s = 1 := by decide

theorem det_eq_one_of_mul4 {M M' : 𝕄₄} (h : M * M' = 1) : M.det = 1 := by
  have h1 : M.det * M'.det = 1 := by rw [← det_mul, h, det_one]
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) M.det with h0 | h0
  · rw [h0, zero_mul] at h1
    exact absurd h1 (by decide)
  · exact h0

theorem pm_mul_inv (σ : Equiv.Perm (Fin 4)) : pm σ * pm σ⁻¹ = 1 := by
  rw [← pm_mul, mul_inv_cancel, pm_one]

@[expose] def x4 (s : Fin 3) : G4 := ⟨xM4 s, det_eq_one_of_mul4 (xM4_mul_self s)⟩

@[expose] def y4 (s : Fin 3) : G4 := ⟨yM4 s, det_eq_one_of_mul4 (yM4_mul_self s)⟩

@[expose] def permHom : Equiv.Perm (Fin 4) →* G4 where
  toFun σ := ⟨pm σ, det_eq_one_of_mul4 (pm_mul_inv σ)⟩
  map_one' := Subtype.ext pm_one
  map_mul' σ τ := Subtype.ext (pm_mul σ τ)

abbrev n4 (s : Fin 3) : G4 := permHom (sw s)

theorem coe_x4 (s : Fin 3) : ((x4 s : G4) : 𝕄₄) = xM4 s := rfl

theorem coe_y4 (s : Fin 3) : ((y4 s : G4) : 𝕄₄) = yM4 s := rfl

theorem coe_permHom (σ : Equiv.Perm (Fin 4)) : ((permHom σ : G4) : 𝕄₄) = pm σ := rfl

theorem x4_mul_self (s : Fin 3) : x4 s * x4 s = 1 := Subtype.ext (xM4_mul_self s)

theorem y4_mul_self (s : Fin 3) : y4 s * y4 s = 1 := Subtype.ext (yM4_mul_self s)

theorem sw_mul_self (s : Fin 3) : sw s * sw s = 1 := Equiv.swap_mul_self _ _

theorem n4_mul_self (s : Fin 3) : n4 s * n4 s = 1 := by
  rw [← map_mul, sw_mul_self, map_one]

theorem isUp4_up4 : ∀ c : Fin 64, IsUp4 (up4 c) := by decide

set_option maxRecDepth 100000 in
theorem up4_pow_four : ∀ c : Fin 64, up4 c * up4 c * up4 c * up4 c = 1 := by decide +kernel

theorem isUp4_one : IsUp4 (1 : 𝕄₄) := by decide

theorem isUp4_mul {A B : 𝕄₄} (hA : IsUp4 A) (hB : IsUp4 B) : IsUp4 (A * B) := by
  rw [eq_mat_of_isUp4 hA, eq_mat_of_isUp4 hB]
  intro a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem pow_four_of_isUp4 {A : 𝕄₄} (hA : IsUp4 A) : A * A * A * A = 1 := by
  rw [← up4_code4 hA]
  exact up4_pow_four _

theorem inv_eq_cube {g : G4} (h : (g : 𝕄₄) * g * g * g = 1) : g⁻¹ = g * g * g := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, ← h]
  simp only [Matrix.mul_assoc]

@[expose] def U4 : Subgroup G4 where
  carrier := {g | IsUp4 (g : 𝕄₄)}
  one_mem' := isUp4_one
  mul_mem' ha hb := isUp4_mul ha hb
  inv_mem' {g} hg := by
    show IsUp4 ((g⁻¹ : G4) : 𝕄₄)
    rw [inv_eq_cube (pow_four_of_isUp4 hg)]
    exact isUp4_mul (isUp4_mul hg hg) hg

@[expose] def L4 : Subgroup G4 where
  carrier := {g | IsUp4 (g : 𝕄₄)ᵀ}
  one_mem' := by
    show IsUp4 (1 : 𝕄₄)ᵀ
    rw [transpose_one]
    exact isUp4_one
  mul_mem' {a b} ha hb := by
    show IsUp4 ((a : 𝕄₄) * b)ᵀ
    rw [transpose_mul]
    exact isUp4_mul hb ha
  inv_mem' {g} hg := by
    have h4 : (g : 𝕄₄) * g * g * g = 1 := by
      have := pow_four_of_isUp4 hg
      rw [← transpose_mul, ← transpose_mul, ← transpose_mul, ← transpose_one] at this
      have h2 := congrArg transpose this
      simp only [transpose_transpose, Matrix.mul_assoc] at h2 ⊢
      exact h2
    show IsUp4 ((g⁻¹ : G4) : 𝕄₄)ᵀ
    rw [inv_eq_cube h4]
    simp only [Matrix.SpecialLinearGroup.coe_mul, transpose_mul]
    exact isUp4_mul hg (isUp4_mul hg hg)

theorem up4_eq_one_of_isUp4_transpose : ∀ c : Fin 64, IsUp4 (up4 c)ᵀ → up4 c = 1 := by decide

theorem U4_inf_L4 : U4 ⊓ L4 = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hU, hL⟩ := Subgroup.mem_inf.1 hg
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  have hU' : IsUp4 (g : 𝕄₄) := hU
  have hL' : IsUp4 (g : 𝕄₄)ᵀ := hL
  rw [← up4_code4 hU'] at hL' ⊢
  exact up4_eq_one_of_isUp4_transpose _ hL'

theorem code4_up4 : ∀ c : Fin 64, code4 (up4 c) = c := by decide

theorem det_up4 (c : Fin 64) : (up4 c).det = 1 := by
  have h := up4_pow_four c
  exact det_eq_one_of_mul4 (M' := up4 c * up4 c * up4 c) (by simpa only [Matrix.mul_assoc] using h)

theorem det_lo4 (c : Fin 64) : (lo4 c).det = 1 := by
  rw [det_transpose]
  exact det_up4 c

@[expose] def uOf (c : Fin 64) : G4 := ⟨up4 c, det_up4 c⟩

@[expose] def lOf (c : Fin 64) : G4 := ⟨lo4 c, det_lo4 c⟩

theorem uOf_mem (c : Fin 64) : uOf c ∈ U4 := isUp4_up4 c

theorem lOf_mem (c : Fin 64) : lOf c ∈ L4 := by
  show IsUp4 (lo4 c)ᵀ
  rw [transpose_transpose]
  exact isUp4_up4 c

theorem eq_uOf {g : G4} (hg : g ∈ U4) : g = uOf (code4 (g : 𝕄₄)) :=
  Subtype.ext (up4_code4 hg).symm

theorem eq_lOf {g : G4} (hg : g ∈ L4) : g = lOf (code4 (g : 𝕄₄)ᵀ) := by
  apply Subtype.ext
  show (g : 𝕄₄) = (up4 (code4 (g : 𝕄₄)ᵀ))ᵀ
  rw [up4_code4 hg, transpose_transpose]

theorem card_U4 : Nat.card U4 = 64 := by
  have e : ↥U4 ≃ Fin 64 :=
    { toFun := fun g => code4 ((g : G4) : 𝕄₄)
      invFun := fun c => ⟨uOf c, uOf_mem c⟩
      left_inv := fun g => Subtype.ext (eq_uOf g.2).symm
      right_inv := fun c => code4_up4 c }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_L4 : Nat.card L4 = 64 := by
  have e : ↥L4 ≃ Fin 64 :=
    { toFun := fun g => code4 ((g : G4) : 𝕄₄)ᵀ
      invFun := fun c => ⟨lOf c, lOf_mem c⟩
      left_inv := fun g => Subtype.ext (eq_lOf g.2).symm
      right_inv := fun c => by
        show code4 (lo4 c)ᵀ = c
        rw [transpose_transpose]
        exact code4_up4 c }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem isPGroup_U4 : IsPGroup 2 U4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.of_card (n := 6) (by rw [card_U4]; norm_num)

theorem isPGroup_L4 : IsPGroup 2 L4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.of_card (n := 6) (by rw [card_L4]; norm_num)

theorem permHom_inv (σ : Equiv.Perm (Fin 4)) : (permHom σ)⁻¹ = permHom σ⁻¹ :=
  (map_inv _ _).symm

theorem sw_inv (s : Fin 3) : (sw s)⁻¹ = sw s := Equiv.swap_inv _ _

theorem n4_inv (s : Fin 3) : (n4 s)⁻¹ = n4 s := by rw [permHom_inv, sw_inv]

theorem pm_conj_apply (π : Equiv.Perm (Fin 4)) (M : 𝕄₄) (i j : Fin 4) :
    (pm π⁻¹ * M * pm π) i j = M (π i) (π j) := by
  simp only [Matrix.mul_apply, pm, Matrix.of_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, ite_mul, one_mul, zero_mul,
    Equiv.Perm.eq_inv_iff_eq, Finset.sum_ite_eq]

theorem pm_sw_conj_apply (s : Fin 3) (M : 𝕄₄) (i j : Fin 4) :
    (pm (sw s) * M * pm (sw s)) i j = M (sw s i) (sw s j) := by
  have h := pm_conj_apply (sw s) M i j
  rwa [sw_inv] at h

theorem isUp4_conj_iff {π : Equiv.Perm (Fin 4)} {M : 𝕄₄} (hM : IsUp4 M) :
    IsUp4 (pm π⁻¹ * M * pm π) ↔ ∀ i j : Fin 4, j < i → M (π i) (π j) = 0 := by
  constructor
  · intro h i j hij
    rw [← pm_conj_apply π M i j]
    exact (h i j).1 hij
  · intro h i j
    refine ⟨fun hij => by rw [pm_conj_apply]; exact h i j hij, fun hij => ?_⟩
    subst hij
    rw [pm_conj_apply]
    exact (hM _ _).2 rfl

theorem isUp4_xM4 : ∀ s : Fin 3, IsUp4 (xM4 s) := by decide

theorem isUp4_yM4 : ∀ s : Fin 3, IsUp4 (yM4 s)ᵀ := by decide

theorem xM4_entry : ∀ s : Fin 3, xM4 s s.castSucc s.succ = 1 := by decide

theorem yM4_entry : ∀ s : Fin 3, yM4 s s.succ s.castSucc = 1 := by decide

theorem x4_mem (s : Fin 3) : x4 s ∈ U4 := isUp4_xM4 s

theorem y4_mem (s : Fin 3) : y4 s ∈ L4 := isUp4_yM4 s

theorem x4_ne_one (s : Fin 3) : x4 s ≠ 1 := by
  intro h
  have := congrArg (fun g : G4 => (g : 𝕄₄) s.castSucc s.succ) h
  simp only [coe_x4, xM4_entry, Matrix.SpecialLinearGroup.coe_one,
    Matrix.one_apply_ne (Fin.castSucc_lt_succ (i := s)).ne] at this
  exact one_ne_zero this

theorem x4_inv (s : Fin 3) : (x4 s)⁻¹ = x4 s := inv_eq_of_mul_eq_one_right (x4_mul_self s)

theorem y4_inv (s : Fin 3) : (y4 s)⁻¹ = y4 s := inv_eq_of_mul_eq_one_right (y4_mul_self s)

theorem rank_one_checks : ∀ s : Fin 3,
    pm (sw s) * xM4 s * pm (sw s) = yM4 s ∧ pm (sw s) * yM4 s * pm (sw s) = xM4 s ∧
    xM4 s * pm (sw s) = yM4 s * xM4 s ∧
    pm (sw s) * xM4 s * pm (sw s) = xM4 s * pm (sw s) * xM4 s ∧
    yM4 s = xM4 s * pm (sw s) * xM4 s ∧ xM4 s = yM4 s * pm (sw s) * yM4 s ∧
    xM4 s * yM4 s = yM4 s * pm (sw s) := by
  decide

theorem n4_conj_x4 (s : Fin 3) : n4 s * x4 s * (n4 s)⁻¹ = y4 s := by
  rw [n4_inv]
  exact Subtype.ext (rank_one_checks s).1

theorem n4_conj_y4 (s : Fin 3) : n4 s * y4 s * (n4 s)⁻¹ = x4 s := by
  rw [n4_inv]
  exact Subtype.ext (rank_one_checks s).2.1

theorem x4_mul_n4 (s : Fin 3) : x4 s * n4 s = y4 s * x4 s :=
  Subtype.ext (rank_one_checks s).2.2.1

theorem n4_x4_n4 (s : Fin 3) : n4 s * x4 s * n4 s = x4 s * n4 s * x4 s :=
  Subtype.ext (rank_one_checks s).2.2.2.1

theorem y4_eq (s : Fin 3) : y4 s = x4 s * n4 s * x4 s :=
  Subtype.ext (rank_one_checks s).2.2.2.2.1

theorem x4_eq (s : Fin 3) : x4 s = y4 s * n4 s * y4 s :=
  Subtype.ext (rank_one_checks s).2.2.2.2.2.1

theorem x4_mul_y4 (s : Fin 3) : x4 s * y4 s = y4 s * n4 s :=
  Subtype.ext (rank_one_checks s).2.2.2.2.2.2

@[expose] def pairSub (x : G4) (hx : x * x = 1) : Subgroup G4 where
  carrier := {g | g = 1 ∨ g = x}
  one_mem' := Or.inl rfl
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [hx]
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rcases ha with rfl | rfl
    · simp
    · exact Or.inr (inv_eq_of_mul_eq_one_right hx)

abbrev X4 (s : Fin 3) : Subgroup G4 := pairSub (x4 s) (x4_mul_self s)

abbrev Y4 (s : Fin 3) : Subgroup G4 := pairSub (y4 s) (y4_mul_self s)

theorem entry_mul_up {A B : 𝕄₄} (hA : IsUp4 A) (hB : IsUp4 B) (s : Fin 3) :
    (A * B) s.castSucc s.succ = A s.castSucc s.succ + B s.castSucc s.succ := by
  rw [eq_mat_of_isUp4 hA, eq_mat_of_isUp4 hB]
  fin_cases s <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem entry_mul_lo {A B : 𝕄₄} (hA : IsUp4 Aᵀ) (hB : IsUp4 Bᵀ) (s : Fin 3) :
    (A * B) s.succ s.castSucc = A s.succ s.castSucc + B s.succ s.castSucc := by
  have h := entry_mul_up hB hA s
  rw [← transpose_mul] at h
  simp only [transpose_apply] at h
  rw [h, add_comm]

theorem entry_inv_up {g : G4} (hg : g ∈ U4) (s : Fin 3) :
    ((g⁻¹ : G4) : 𝕄₄) s.castSucc s.succ = (g : 𝕄₄) s.castSucc s.succ := by
  have h := entry_mul_up (U4.inv_mem hg) hg s
  rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
    Matrix.one_apply_ne (Fin.castSucc_lt_succ (i := s)).ne] at h
  have h2 : ∀ a b : ZMod 2, 0 = a + b → a = b := by decide
  exact h2 _ _ h

theorem entry_inv_lo {g : G4} (hg : g ∈ L4) (s : Fin 3) :
    ((g⁻¹ : G4) : 𝕄₄) s.succ s.castSucc = (g : 𝕄₄) s.succ s.castSucc := by
  have h := entry_mul_lo (L4.inv_mem hg) hg s
  rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
    Matrix.one_apply_ne (Fin.castSucc_lt_succ (i := s)).ne'] at h
  have h2 : ∀ a b : ZMod 2, 0 = a + b → a = b := by decide
  exact h2 _ _ h

@[expose] def Us4 (s : Fin 3) : Subgroup G4 where
  carrier := {g | g ∈ U4 ∧ (g : 𝕄₄) s.castSucc s.succ = 0}
  one_mem' := ⟨U4.one_mem, Matrix.one_apply_ne (Fin.castSucc_lt_succ (i := s)).ne⟩
  mul_mem' {a b} ha hb := ⟨U4.mul_mem ha.1 hb.1, by
    rw [Matrix.SpecialLinearGroup.coe_mul, entry_mul_up ha.1 hb.1, ha.2, hb.2, add_zero]⟩
  inv_mem' {g} hg := ⟨U4.inv_mem hg.1, by rw [entry_inv_up hg.1, hg.2]⟩

@[expose] def Qs4 (s : Fin 3) : Subgroup G4 where
  carrier := {g | g ∈ L4 ∧ (g : 𝕄₄) s.succ s.castSucc = 0}
  one_mem' := ⟨L4.one_mem, Matrix.one_apply_ne (Fin.castSucc_lt_succ (i := s)).ne'⟩
  mul_mem' {a b} ha hb := ⟨L4.mul_mem ha.1 hb.1, by
    rw [Matrix.SpecialLinearGroup.coe_mul, entry_mul_lo ha.1 hb.1, ha.2, hb.2, add_zero]⟩
  inv_mem' {g} hg := ⟨L4.inv_mem hg.1, by rw [entry_inv_lo hg.1, hg.2]⟩

theorem zmod2_eq (c : ZMod 2) : c = 0 ∨ c = 1 := by
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with h | h <;> simp [h]

theorem conj_mem_Us4 {s : Fin 3} {u v : G4} (hu : u ∈ U4) (hv : v ∈ Us4 s) :
    u * v * u⁻¹ ∈ Us4 s := by
  refine ⟨U4.mul_mem (U4.mul_mem hu hv.1) (U4.inv_mem hu), ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, entry_mul_up (U4.mul_mem hu hv.1) (U4.inv_mem hu),
    Matrix.SpecialLinearGroup.coe_mul, entry_mul_up hu hv.1, hv.2, entry_inv_up hu, add_zero]
  rcases zmod2_eq ((u : 𝕄₄) s.castSucc s.succ) with h | h <;> rw [h] <;> decide

theorem conj_mem_Qs4 {s : Fin 3} {l q : G4} (hl : l ∈ L4) (hq : q ∈ Qs4 s) :
    l * q * l⁻¹ ∈ Qs4 s := by
  refine ⟨L4.mul_mem (L4.mul_mem hl hq.1) (L4.inv_mem hl), ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, entry_mul_lo (L4.mul_mem hl hq.1) (L4.inv_mem hl),
    Matrix.SpecialLinearGroup.coe_mul, entry_mul_lo hl hq.1, hq.2, entry_inv_lo hl, add_zero]
  rcases zmod2_eq ((l : 𝕄₄) s.succ s.castSucc) with h | h <;> rw [h] <;> decide

theorem U4_eq (s : Fin 3) {u : G4} (hu : u ∈ U4) : ∃ x ∈ X4 s, ∃ v ∈ Us4 s, u = x * v := by
  rcases zmod2_eq ((u : 𝕄₄) s.castSucc s.succ) with h | h
  · exact ⟨1, Or.inl rfl, u, ⟨hu, h⟩, (one_mul u).symm⟩
  · refine ⟨x4 s, Or.inr rfl, x4 s * u, ⟨U4.mul_mem (x4_mem s) hu, ?_⟩, ?_⟩
    · rw [Matrix.SpecialLinearGroup.coe_mul, entry_mul_up (x4_mem s) hu, h, coe_x4,
        xM4_entry]
      decide
    · rw [← mul_assoc, x4_mul_self, one_mul]

theorem L4_eq (s : Fin 3) {l : G4} (hl : l ∈ L4) : l ∈ Qs4 s ∨ y4 s * l ∈ Qs4 s := by
  rcases zmod2_eq ((l : 𝕄₄) s.succ s.castSucc) with h | h
  · exact Or.inl ⟨hl, h⟩
  · refine Or.inr ⟨L4.mul_mem (y4_mem s) hl, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, entry_mul_lo (y4_mem s) hl, h, coe_y4, yM4_entry]
    decide

set_option maxRecDepth 100000 in
theorem norm_checks : ∀ (s : Fin 3) (c : Fin 64),
    (up4 c s.castSucc s.succ = 0 → (∀ i j : Fin 4, j < i → up4 c (sw s i) (sw s j) = 0) ∧
      up4 c (sw s s.castSucc) (sw s s.succ) = 0) ∧
    (lo4 c s.succ s.castSucc = 0 → (∀ i j : Fin 4, i < j → lo4 c (sw s i) (sw s j) = 0) ∧
      lo4 c (sw s s.succ) (sw s s.castSucc) = 0) ∧
    (lo4 c s.succ s.castSucc = 0 → IsUp4 (xM4 s * lo4 c * xM4 s)ᵀ ∧
      (xM4 s * lo4 c * xM4 s) s.succ s.castSucc = 0) := by
  decide +kernel

theorem n4_conj_Us4 {s : Fin 3} {v : G4} (hv : v ∈ Us4 s) : n4 s * v * (n4 s)⁻¹ ∈ Us4 s := by
  have hc := (norm_checks s (code4 (v : 𝕄₄))).1
  rw [up4_code4 hv.1] at hc
  obtain ⟨h1, h2⟩ := hc hv.2
  have e : ((n4 s * v * (n4 s)⁻¹ : G4) : 𝕄₄) = pm (sw s) * v * pm (sw s) := by
    rw [n4_inv]
    rfl
  refine ⟨?_, ?_⟩
  · show IsUp4 _
    rw [e]
    intro i j
    refine ⟨fun hij => by rw [pm_sw_conj_apply]; exact h1 i j hij, fun hij => ?_⟩
    subst hij
    rw [pm_sw_conj_apply]
    exact (hv.1 _ _).2 rfl
  · rw [e, pm_sw_conj_apply]
    exact h2

theorem n4_conj_Qs4 {s : Fin 3} {q : G4} (hq : q ∈ Qs4 s) : n4 s * q * (n4 s)⁻¹ ∈ Qs4 s := by
  have hc := (norm_checks s (code4 (q : 𝕄₄)ᵀ)).2.1
  have hq' : lo4 (code4 (q : 𝕄₄)ᵀ) = q := by
    show (up4 (code4 (q : 𝕄₄)ᵀ))ᵀ = q
    rw [up4_code4 hq.1, transpose_transpose]
  rw [hq'] at hc
  obtain ⟨h1, h2⟩ := hc hq.2
  have e : ((n4 s * q * (n4 s)⁻¹ : G4) : 𝕄₄) = pm (sw s) * q * pm (sw s) := by
    rw [n4_inv]
    rfl
  refine ⟨?_, ?_⟩
  · show IsUp4 _
    rw [e]
    intro i j
    refine ⟨fun hij => by rw [transpose_apply, pm_sw_conj_apply]; exact h1 j i hij,
      fun hij => ?_⟩
    subst hij
    rw [transpose_apply, pm_sw_conj_apply]
    have := (hq.1 (sw s i) (sw s i)).2 rfl
    rwa [transpose_apply] at this
  · rw [e, pm_sw_conj_apply]
    exact h2

theorem x4_conj_Qs4 {s : Fin 3} {q : G4} (hq : q ∈ Qs4 s) : x4 s * q * (x4 s)⁻¹ ∈ Qs4 s := by
  have hc := (norm_checks s (code4 (q : 𝕄₄)ᵀ)).2.2
  have hq' : lo4 (code4 (q : 𝕄₄)ᵀ) = q := by
    show (up4 (code4 (q : 𝕄₄)ᵀ))ᵀ = q
    rw [up4_code4 hq.1, transpose_transpose]
  rw [hq'] at hc
  rw [x4_inv]
  exact hc hq.2

@[expose] def upWord4 : Fin 4 → Fin 4 → List (Fin 3) :=
  ![![[], [0], [0, 1, 0, 1], [0, 1, 2, 1, 0, 1, 2, 1]],
    ![[], [], [1], [1, 2, 1, 2]],
    ![[], [], [], [2]],
    ![[], [], [], []]]

theorem upWord4_spec : ∀ i j : Fin 4, i < j →
    Matrix.transvection i j (1 : ZMod 2) = ((upWord4 i j).map xM4).prod := by
  decide

theorem lower_transvection4 : ∀ i j : Fin 4, j < i →
    IsUp4 (Matrix.transvection i j (1 : ZMod 2))ᵀ := by
  decide

theorem prod_x4_coe (l : List (Fin 3)) : (((l.map x4).prod : G4) : 𝕄₄) = (l.map xM4).prod := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    rw [List.map_cons, List.prod_cons, Matrix.SpecialLinearGroup.coe_mul, ih, List.map_cons,
      List.prod_cons, coe_x4]

theorem prod_x4_mem (l : List (Fin 3)) :
    (l.map x4).prod ∈ Subgroup.closure ((L4 : Set G4) ∪ Set.range x4) := by
  induction l with
  | nil => exact Subgroup.one_mem _
  | cons s l ih =>
    rw [List.map_cons, List.prod_cons]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr ⟨s, rfl⟩)) ih

theorem closure_L4_x4 : Subgroup.closure ((L4 : Set G4) ∪ Set.range x4) = ⊤ := by
  refine JonesParshall.closure_eq_top_of_transvection fun t => ?_
  obtain ⟨i, j, hij, c⟩ := t
  rcases zmod2_eq c with rfl | rfl
  · rw [TransvectionStruct.toSpecialLinearGroup_mk, SpecialLinearGroup.transvection_coeff_zero]
    exact Subgroup.one_mem _
  · rw [TransvectionStruct.toSpecialLinearGroup_mk]
    rcases lt_or_gt_of_ne hij with h | h
    · have e : SpecialLinearGroup.transvection hij (1 : ZMod 2) = ((upWord4 i j).map x4).prod :=
        Subtype.ext (by rw [prod_x4_coe]; exact upWord4_spec i j h)
      rw [e]
      exact prod_x4_mem _
    · exact Subgroup.subset_closure (Or.inl (lower_transvection4 i j h))

end CFSG.Quasithin.B42Ln
