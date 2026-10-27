module

public import CFSG.Quasithin.EmptyFaithful.S14612EA
public import CFSG.Quasithin.EmptyFaithful.S151cOrbI
public import CFSG.Quasithin.EmptyFaithful.S151cShapeE27
public import CFSG.Quasithin.EmptyFaithful.S151cShapeNine
public import CFSG.Quasithin.EmptyFaithful.S151cShapeOmega

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open CFSG.QuasithinUnique (IsSylowTwoOf)

section ClassAut

variable {V : Type} [CommGroup V] [Finite V] {X Tb P : Subgroup (MulAut V)} {p : ℕ}

private theorem card_le_three_14612 {G : Type*} [Group G] [Finite G] [IsCyclic G]
    (hexp : ∀ g : G, g ^ 3 = 1) : Nat.card G ≤ 3 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := G)
  have h3 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one (hexp g)
  rw [hg] at h3
  exact Nat.le_of_dvd (by norm_num) h3

omit [Finite V] in
private theorem nonempty_equiv_conjBy_14612 {L L' : Subgroup (MulAut V)} {x : MulAut V}
    (e : conjBy x L = L') : Nonempty (↥L ≃* ↥L') := by
  subst e
  exact ⟨Subgroup.equivMapOfInjective L (MulAut.conj x).toMonoidHom (MulAut.conj x).injective⟩

omit [Finite V] in
private theorem conjAut_eq_conjBy_14612 (g : MulAut V) (A : Subgroup (MulAut V)) :
    B1.conjAut g A = conjBy g A := by
  ext x
  rw [B1.mem_conjAut, mem_conjBy_iff]

open Classical in
private theorem commV_pair_14612 {Xc : Subgroup (MulAut V)} (h : Setting151c X Tb Xc)
    {I : Finset (Subgroup (MulAut V))} (hI : IsBlocks216 (Jhat X) I)
    {L₁ L₂ : Subgroup (MulAut V)} (h1 : L₁ ∈ I) (h2 : L₂ ∈ I) (hne : L₂ ≠ L₁)
    (hJ : Jhat X = L₁ ⊔ L₂) (hfix : fixV (Jhat X) = ⊥) :
    commV L₁ ⊓ commV L₂ = ⊥ ∧ commV L₁ ⊔ commV L₂ = ⊤ := by
  refine ⟨?_, ?_⟩
  · refine le_bot_iff.mp ?_
    rw [← hI.indepV L₁ h1]
    exact inf_le_inf_left _ (le_iSup₂ (f := fun L' (_ : L' ∈ I.erase L₁) => commV L') L₂
      (Finset.mem_erase.mpr ⟨hne, h2⟩))
  · have hcop := commV_fitting_sup_fixV h.sq h.o2
    have hFJ : fittingOf (Jhat X) ≤ Jhat X := fittingOf_le _
    have hfix_eq : fixV (Jhat X) = fixV (fittingOf (Jhat X)) :=
      le_antisymm (fun c hc f hf => hc f (hFJ hf)) (fun c hc j hj => h.central c hc j hj)
    have hC0 : fixV (fittingOf (Jhat X)) = ⊥ := by rw [← hfix_eq]; exact hfix
    have hcomm : commV (fittingOf (Jhat X)) = ⊤ := by
      have := hcop.1
      rwa [hC0, sup_bot_eq] at this
    have hle : commV (Jhat X) ≤ commV L₁ ⊔ commV L₂ := by
      rw [hJ]
      exact commV_sup_le151c L₁ L₂
    rw [eq_top_iff, ← hcomm]
    exact (commV_mono216 hFJ).trans hle

private def cSL14612 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) := ⟨!![0, 1; 1, 1], by decide⟩

private def sSL14612 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) := ⟨!![0, 1; 1, 0], by decide⟩

private def d3toSL14612 : DihedralGroup 3 → Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)
  | .r i => cSL14612 ^ i.val
  | .sr i => sSL14612 * cSL14612 ^ i.val

private theorem d3toSL14612_mul :
    ∀ a b : DihedralGroup 3, d3toSL14612 (a * b) = d3toSL14612 a * d3toSL14612 b := by
  decide +kernel

private noncomputable def d3hom14612 :
    DihedralGroup 3 →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) where
  toFun := d3toSL14612
  map_one' := by decide +kernel
  map_mul' := d3toSL14612_mul

private theorem d3hom14612_injective : Function.Injective d3hom14612 := by
  have : ∀ a b : DihedralGroup 3, d3toSL14612 a = d3toSL14612 b → a = b := by decide +kernel
  exact fun a b h => this a b h

private theorem d3hom14612_card :
    Nat.card (DihedralGroup 3) = Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) := by
  rw [DihedralGroup.nat_card, Nat.card_eq_fintype_card]
  decide +kernel

private noncomputable def sl2EquivDihedral3_14612 :
    Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) ≃* DihedralGroup 3 :=
  (MulEquiv.ofBijective d3hom14612 ((Nat.bijective_iff_injective_and_card d3hom14612).2
    ⟨d3hom14612_injective, d3hom14612_card⟩)).symm

theorem class_aut_O4 (h : PStr14612 X Tb P p) (hO : IsOFourPlusAct X) :
    p = 3 ∧ ∃ L₁ L₂, Blocks14612 X Tb P p L₁ L₂ ∧ rk (commV L₁) = 2 := by
  obtain ⟨hcard, q, hq1, hq2, hq3, hXq⟩ := hO
  have hexp : ∀ w : V, w * w = 1 := fun w => by rw [← pow_two]; exact h.sq w
  obtain ⟨L₁, L₂, t, hS, -⟩ := exists_ofourStruct_of_plusType hexp hcard hq1 hq2 hq3
  rw [← hXq] at hS
  have hp3 : p = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hdvd : 3 ∣ Nat.card X := by rw [hS.card_X]; norm_num
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 3 hdvd
    have hxo : orderOf (x : MulAut V) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
    exact (h.prime_eq_of_orderOf x.2 Nat.prime_three (by norm_num) hxo).symm
  subst hp3
  have hconj : ∀ g : MulAut V, conjBy g L₁ = B1.conjAut g L₁ := fun g =>
    (conjAut_eq_conjBy_14612 g L₁).symm
  have hswap : ∀ x ∈ X, x ∉ L₁ ⊔ L₂ → conjBy x L₁ = L₂ := by
    intro x hx hxN
    have hxt : x * t ∈ L₁ ⊔ L₂ := (hS.mem_or_mul_t_mem hx).resolve_left hxN
    have hx_eq : x = (x * t) * t := by rw [mul_assoc, hS.tsq, mul_one]
    have h1 : conjBy t L₁ = L₂ := by rw [← conjAut_eq_conjBy_14612]; exact hS.conj₁
    have h2 : conjBy (x * t) L₂ = L₂ :=
      conjBy_eq_of_mem_normalizer (hS.sup_le_normalizer_L₂ hxt)
    rw [hx_eq, ← conjBy_conjBy, h1, h2]
  have hsylX : IsSylowTwoOf Tb X := h.syl
  have hTb8 : Nat.card Tb = 8 := hS.card_T hsylX
  have hTbN : ¬ Tb ≤ L₁ ⊔ L₂ := by
    intro hle
    have hd : Nat.card Tb ∣ Nat.card ↥(L₁ ⊔ L₂) := Subgroup.card_dvd_of_le hle
    rw [hTb8, hS.card_sup] at hd
    omega
  obtain ⟨t', ht', ht'N⟩ := Set.not_subset.mp hTbN
  have hsw : conjBy t' L₁ = L₂ := hswap t' (h.tb_le ht') ht'N
  have he₁ : Nonempty (↥L₁ ≃* DihedralGroup 3) := by
    obtain ⟨e₁, -, -⟩ := hS.nat₁
    exact ⟨e₁.trans sl2EquivDihedral3_14612⟩
  have he₂ : Nonempty (↥L₂ ≃* DihedralGroup 3) := by
    obtain ⟨e₂, -, -⟩ := hS.nat₂
    exact ⟨e₂.trans sl2EquivDihedral3_14612⟩
  have hrk₁ : rk (commV L₁) = 2 := by
    have h4 := hS.card_U₁
    rw [card_eq_two_pow h.sq] at h4
    have : (2 : ℕ) ^ rk (commV L₁) = 2 ^ 2 := by rw [h4]; norm_num
    exact Nat.pow_right_injective (le_refl 2) this
  have hrk₂ : rk (commV L₂) = rk (commV L₁) := by rw [← hsw, rk_commV_conjBy]
  refine ⟨rfl, L₁, L₂, ⟨hS.L₁_le, hS.L₂_le, he₁, he₂, hS.Linf, hS.comm, hS.L₁_ne_L₂.symm, ?_, ⟨t', ht', hsw⟩,
    ?_, hS.inf, hS.sup, ?_, ?_, hrk₂, ⟨fun h5 => absurd h5 (by norm_num), fun _ => Or.inl hrk₁⟩⟩, hrk₁⟩
  · intro x hx
    have hodd : Odd (orderOf x) := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨b, hb⟩ := h.pgrp ⟨x, hx⟩
      have hb' : x ^ 3 ^ b = 1 := congrArg Subtype.val hb
      exact Odd.of_dvd_nat (Odd.pow (by decide : Odd 3)) (orderOf_dvd_of_pow_eq_one hb')
    exact hS.odd_mem_sup (h.P_le hx) hodd
  · intro x hx
    rcases hS.perm x hx with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl (by rw [← conjAut_eq_conjBy_14612]; exact h1)
    · exact Or.inr (by rw [← conjAut_eq_conjBy_14612]; exact h1)
  · intro v hv l hl
    exact hS.L₂_fix₁ hl hv
  · intro v hv l hl
    exact hS.symm.L₂_fix₁ hl hv

private def rotFst14612 : Subgroup (DihedralGroup 3 × DihedralGroup 3) where
  carrier := {x | ∃ i : ZMod 3, x = (DihedralGroup.r i, 1)}
  one_mem' := ⟨0, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨i + j, rfl⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact ⟨-i, rfl⟩

private def rotSnd14612 : Subgroup (DihedralGroup 3 × DihedralGroup 3) where
  carrier := {x | ∃ i : ZMod 3, x = (1, DihedralGroup.r i)}
  one_mem' := ⟨0, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨i + j, rfl⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact ⟨-i, rfl⟩

private theorem rotFst14612_normal :
    ∀ (g : DihedralGroup 3 × DihedralGroup 3) (i : ZMod 3),
      ∃ j : ZMod 3, g * (DihedralGroup.r i, 1) * g⁻¹ = (DihedralGroup.r j, 1) := by
  decide +kernel

private theorem rotSnd14612_normal :
    ∀ (g : DihedralGroup 3 × DihedralGroup 3) (i : ZMod 3),
      ∃ j : ZMod 3, g * (1, DihedralGroup.r i) * g⁻¹ = (1, DihedralGroup.r j) := by
  decide +kernel

private theorem rot_cube14612 : ∀ i : ZMod 3, (DihedralGroup.r i : DihedralGroup 3) ^ 3 = 1 := by
  decide +kernel

private theorem false_of_d33 (h : PStr14612 X Tb P p) (hXJ : X = Jhat X)
    (e : ↥(Jhat X) ≃* DihedralGroup 3 × DihedralGroup 3) : False := by
  have hJX : Jhat X ≤ X := Jhat_le X
  have key : ∀ (S : Subgroup (DihedralGroup 3 × DihedralGroup 3))
      (_ : ∀ g : DihedralGroup 3 × DihedralGroup 3, ∀ x ∈ S, g * x * g⁻¹ ∈ S)
      (_ : ∀ x ∈ S, x ^ 3 = 1),
      ((S.comap e.toMonoidHom).map (Jhat X).subtype ≤ P) ∧
        NormalIn X ((S.comap e.toMonoidHom).map (Jhat X).subtype) := by
    intro S hS hS3
    refine ⟨?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      have hy' : e y ∈ S := hy
      have hy3 : y ^ 3 = 1 := by
        have h1 : e (y ^ 3) = 1 := by rw [map_pow]; exact hS3 _ hy'
        exact e.injective (by rw [h1, map_one])
      have hy3' : (y : MulAut V) ^ 3 = 1 := by simpa using congrArg Subtype.val hy3
      have hodd : Odd (orderOf (y : MulAut V)) :=
        Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hy3')
      exact h.odd_mem (hJX y.2) hodd
    · intro g hg k hk
      obtain ⟨y, hy, rfl⟩ := hk
      have hgJ : g ∈ Jhat X := hXJ ▸ hg
      refine ⟨⟨g, hgJ⟩ * y * ⟨g, hgJ⟩⁻¹, ?_, rfl⟩
      show e (⟨g, hgJ⟩ * y * ⟨g, hgJ⟩⁻¹) ∈ S
      rw [map_mul, map_mul, map_inv]
      exact hS _ _ hy
  have hne : ∀ (S : Subgroup (DihedralGroup 3 × DihedralGroup 3))
      (x : DihedralGroup 3 × DihedralGroup 3), x ∈ S → x ≠ 1 →
      (S.comap e.toMonoidHom).map (Jhat X).subtype ≠ ⊥ := by
    intro S x hx hx1 hbot
    have hmem : ((e.symm x : ↥(Jhat X)) : MulAut V) ∈
        (S.comap e.toMonoidHom).map (Jhat X).subtype :=
      ⟨e.symm x, by show e (e.symm x) ∈ S; rw [MulEquiv.apply_symm_apply]; exact hx, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have : e.symm x = 1 := Subtype.ext hmem
    exact hx1 (by simpa using congrArg e this)
  obtain ⟨hN₁P, hN₁n⟩ := key rotFst14612
    (by
      rintro g _ ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := rotFst14612_normal g i
      exact ⟨j, hj⟩)
    (by
      rintro _ ⟨i, rfl⟩
      exact Prod.ext (rot_cube14612 i) (by simp))
  obtain ⟨hN₂P, hN₂n⟩ := key rotSnd14612
    (by
      rintro g _ ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := rotSnd14612_normal g i
      exact ⟨j, hj⟩)
    (by
      rintro _ ⟨i, rfl⟩
      exact Prod.ext (by simp) (rot_cube14612 i))
  have hN₁ne := hne rotFst14612 (DihedralGroup.r 1, 1) ⟨1, rfl⟩ (by decide)
  have hN₂ne := hne rotSnd14612 (1, DihedralGroup.r 1) ⟨1, rfl⟩ (by decide)
  have hN₁eq := (h.minimal _ hN₁P hN₁n).resolve_left hN₁ne
  have hN₂eq := (h.minimal _ hN₂P hN₂n).resolve_left hN₂ne
  have hinf : ((rotFst14612.comap e.toMonoidHom).map (Jhat X).subtype) ⊓
      ((rotSnd14612.comap e.toMonoidHom).map (Jhat X).subtype) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => ?_
    obtain ⟨⟨y₁, hy₁, rfl⟩, ⟨y₂, hy₂, hy₂e⟩⟩ := hz
    have hy : y₂ = y₁ := Subtype.ext hy₂e
    rw [hy] at hy₂
    obtain ⟨i, hi⟩ : ∃ i : ZMod 3, e y₁ = (DihedralGroup.r i, 1) := hy₁
    obtain ⟨j, hj⟩ : ∃ j : ZMod 3, e y₁ = (1, DihedralGroup.r j) := hy₂
    have hfst : (DihedralGroup.r i : DihedralGroup 3) = 1 := congrArg Prod.fst (hi.symm.trans hj)
    have hy1 : y₁ = 1 := by
      apply e.injective
      rw [hi, hfst, map_one]
      rfl
    rw [hy1]
    rfl
  rw [hN₁eq, hN₂eq, inf_idem] at hinf
  rw [hN₁eq] at hN₁ne
  exact hN₁ne hinf

theorem class_aut_not_O4 (h : PStr14612 X Tb P p) (hfix : fixV P = ⊥)
    (hgen : ∀ W : Subgroup V, (∀ g ∈ X, ∀ z ∈ fixV Tb, g z ∈ W) → W = ⊤)
    (hO : ¬ IsOFourPlusAct X) :
    (p = 3 ∧ Nat.card Tb = 4) ∨ ∃ L₁ L₂, Blocks14612 X Tb P p L₁ L₂ := by
  classical
  have hS : Setting151c X Tb Tb := h.setting hfix hgen
  obtain ⟨r, hr, hr2⟩ := h.exists_rat
  have hJ := Jhat_compat hr hr2
  obtain ⟨I, hI⟩ := exists_isBlocks216 hr2 (Jhat X) hJ.1 hJ.2
  have hIne : I.Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    apply h.Jhat_ne_bot
    rw [hI.sup_eq, hcon]
    simp
  obtain ⟨L, hL⟩ := hIne
  obtain ⟨K, hK, hLK⟩ := exists_comp hS hr hr2 hI hL
  have hKne : K ≠ ⊥ := fun e => hI.ne_bot L hL (le_bot_iff.mp (e ▸ hLK))
  have hcase : Jhat X = K ∧ fixV (Jhat X) = ⊥ := by
    rcases dich hS hI hK hKne with H | ⟨-, hKT, -⟩
    · exact H
    · exfalso
      have hKn := hK.normalIn
      have hKX : K ≤ X := (hK.le_Jhat hI).trans (Jhat_le X)
      have h2 : IsPGroup 2 K := h.tb_two.to_le hKT
      have := le_pCoreOf_of_le_normalizer 2 hKX hKn.le_normalizer h2
      rw [h.o2, le_bot_iff] at this
      exact hKne this
  rcases hK with ⟨L', hL', hnorm, hKL⟩ | ⟨L₁, h1, L₂, h2, hne, ⟨x₂, hx₂, e₂⟩, horb, hKL⟩
  ·
    left
    have hJL : Jhat X = L' := hcase.1.trans hKL
    have hLu : ∀ L'' ∈ I, L'' = L' := fun L'' hL'' =>
      block_eq_of_le hI hL'' hL' (hJL ▸ block_le_J hI hL'')
    have B := oneBlock_of_single hS hr hr2 hI hL' hLu hcase.2
    obtain ⟨-, hD⟩ := B.d217
    have hPJ := h.P_le_Jhat
    have hcP : Nat.card P ≤ Nat.card (Jhat X) := Subgroup.card_le_of_le hPJ
    have hdvd : Nat.card P ∣ Nat.card (Jhat X) := Subgroup.card_dvd_of_le hPJ
    have h9 := h.nine_le_card
    have hodd := h.odd_card
    rcases hD with ⟨⟨e⟩, hrk, hr'⟩ | ⟨⟨e⟩, hrk, hr'⟩ | ⟨hE, hF9, ht, hrk, hr'⟩ |
        ⟨hF27, hexp, hnc, ht, hrk, hr'⟩ | ⟨hrk, hΩ, ⟨eΩ⟩, hr'⟩ | h6
    · exfalso
      have := card_of_dihedral ⟨e⟩
      omega
    · exfalso
      have h10 := card_of_dihedral (⟨e⟩ : Nonempty (↥(Jhat X) ≃* DihedralGroup 5))
      rw [h10] at hcP hdvd
      have hle : Nat.card P ≤ 10 := by omega
      have h910 : Nat.card P = 9 ∨ Nat.card P = 10 := by omega
      rcases h910 with h9' | h10'
      · rw [h9'] at hdvd
        omega
      · rw [h10'] at hodd
        exact absurd hodd (by decide)
    · have hA4 := shape_Nine B hE hF9 ht hr' hrk
      obtain ⟨-, ⟨-, hc9, -⟩, ⟨eT⟩⟩ := hA4
      have hP9 : Nat.card P = 9 := by rw [← h.oTwoUpper_eq]; exact hc9
      have hTb4 : Nat.card Tb = 4 := by
        rw [Nat.card_congr eT.toEquiv, Nat.card_eq_fintype_card]
        simp
      refine ⟨?_, hTb4⟩
      obtain ⟨n, hn⟩ := h.card_eq_pow
      have hn1 : n ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hn
        omega
      have hpd : p ∣ 3 ^ 2 := by
        have : p ∣ p ^ n := dvd_pow_self p hn1
        rw [← hn, hP9] at this
        simpa using this
      exact (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_three).mp (h.prime.dvd_of_dvd_pow hpd)
    · exfalso
      have hA7 := shape_E27 B hF27 hexp hnc ht hr' hrk
      obtain ⟨-, ⟨hExt, -, -⟩⟩ := hA7
      obtain ⟨hExt1, hExt2, -⟩ := hExt
      have hoT := h.oTwoUpper_eq
      have hcomm : ∀ a b : ↥(oTwoUpper X), a * b = b * a := fun a b => by
        have ha : (a : MulAut V) ∈ P := hoT ▸ a.2
        have hb : (b : MulAut V) ∈ P := hoT ▸ b.2
        exact Subtype.ext (h.abelian _ ha _ hb)
      have hcenter : Subgroup.center ↥(oTwoUpper X) = ⊤ :=
        (Subgroup.eq_top_iff' _).2 fun a => Subgroup.mem_center_iff.2 fun g => hcomm g a
      have : CFSG.IsExtraspecial 3 ↥(oTwoUpper X) := hExt1
      have h3 := CFSG.IsExtraspecial.center_order_p 3 ↥(oTwoUpper X)
      rw [hcenter, Subgroup.card_top, hExt2] at h3
      omega
    · exfalso
      have hA3 := shape_Omega B hΩ hr' hrk
      exact false_of_d33 h hA3.2.1 eΩ
    · exact absurd (oneBlock_not_shape6 B h6) id
  ·
    right
    have hJ' : Jhat X = L₁ ⊔ L₂ := hcase.1.trans hKL
    obtain ⟨-, ⟨p', -, hA6⟩, -⟩ := twoOrbit_cases hS hr hr2 hI h1 h2 hne hx₂ e₂ horb hJ' hcase.2 hO
    obtain ⟨hV256, -⟩ := hA6
    have hLinf := block_inf_eq_bot hI h1 h2 hne.symm
    have hcomm := hI.comm L₁ h1 L₂ h2 hne.symm
    obtain ⟨hUinf, hUsup⟩ := commV_pair_14612 hS hI h1 h2 hne hJ' hcase.2
    have hrk₂ : rk (commV L₂) = rk (commV L₁) := by rw [← e₂, rk_commV_conjBy]
    have hrkV : rk V = 8 := by
      have h1' := card_eq_two_pow_rk (V := V) h.sq
      rw [hV256] at h1'
      have : (2 : ℕ) ^ 8 = 2 ^ rk V := by rw [← h1']; norm_num
      exact (Nat.pow_right_injective (le_refl 2) this).symm
    have hrk4 : rk (commV L₁) = 4 := by
      have h3 := rk_sup_add_rk_inf (commV L₁) (commV L₂)
      rw [hUsup, hUinf] at h3
      simp only [rk_top, rk_bot] at h3
      omega
    have hs₁ := suppData_block hS hI h1
    obtain ⟨-, hD⟩ := block_d217 hS hr hr2 hI h1
    have hcycF : IsCyclic ↥(fittingOf L₁) :=
      orbit_two_fitting_cyclic hS hr hr2 hI h1 h2 hne.symm e₂.symm
    have hcycY : IsCyclic ↥(fittingOf (autSub L₁ (commV L₁))) := by
      by_contra hnc
      exact not_isCyclic_fittingOf_block hS hI h1 hnc hcycF
    obtain ⟨hr_eq, -, -⟩ := twoOrbit_cases hS hr hr2 hI h1 h2 hne hx₂ e₂ horb hJ' hcase.2 hO
    have hshape : ∃ q : ℕ, (q = 3 ∨ q = 5) ∧ Nonempty (↥(autSub L₁ (commV L₁)) ≃* DihedralGroup q) := by
      rcases hD with ⟨⟨eY⟩, -, -⟩ | ⟨⟨eY⟩, -, -⟩ | ⟨hE, hF, -⟩ | ⟨-, -, -, -, hrk6, -⟩ |
          ⟨-, -, -, hr32⟩ | ⟨-, -, -, hrk6, -⟩
      · exact ⟨3, Or.inl rfl, ⟨eY⟩⟩
      · exact ⟨5, Or.inr rfl, ⟨eY⟩⟩
      · exfalso
        have := card_le_three_14612 (G := ↥(fittingOf (autSub L₁ (commV L₁))))
          (fun g => Subtype.ext (hE.2 (g : MulAut (↥(commV L₁))) g.2))
        omega
      · omega
      · rw [hr_eq] at hr32
        norm_num at hr32
      · omega
    obtain ⟨q, hq, ⟨eY⟩⟩ := hshape
    have eL₁ : ↥L₁ ≃* DihedralGroup q := hs₁.restrictEquiv.trans eY
    have hq2 : q ≠ 2 := by rcases hq with rfl | rfl <;> norm_num
    have hqpr : q.Prime := by rcases hq with rfl | rfl <;> norm_num
    have hL₁X : L₁ ≤ X := (block_le_J hI h1).trans (Jhat_le X)
    have hL₂X : L₂ ≤ X := (block_le_J hI h2).trans (Jhat_le X)
    have hx1 : orderOf ((eL₁.symm (DihedralGroup.r 1) : ↥L₁) : MulAut V) = q := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      have : NeZero q := ⟨hqpr.ne_zero⟩
      exact DihedralGroup.orderOf_r_one
    have hqp : q = p := h.prime_eq_of_orderOf (hL₁X (eL₁.symm (DihedralGroup.r 1)).2) hqpr hq2 hx1
    have eL₁p : Nonempty (↥L₁ ≃* DihedralGroup p) := by
      rw [← hqp]
      exact ⟨eL₁⟩
    obtain ⟨iso⟩ := nonempty_equiv_conjBy_14612 e₂
    have eL₂p : Nonempty (↥L₂ ≃* DihedralGroup p) := by
      obtain ⟨e₁'⟩ := eL₁p
      exact ⟨iso.symm.trans e₁'⟩
    refine ⟨L₁, L₂, ⟨hL₁X, hL₂X, eL₁p, eL₂p, hLinf, hcomm, hne, ?_,
      exists_swap_of_orbit_two hS hne hx₂ e₂ horb, horb, hUinf, hUsup,
      hI.triv L₁ h1 L₂ h2 hne.symm, hI.triv L₂ h2 L₁ h1 hne, hrk₂,
      ⟨fun _ => hrk4, fun _ => Or.inr hrk4⟩⟩⟩
    rw [← hJ']
    exact h.P_le_Jhat

theorem class_aut (h : PStr14612 X Tb P p) (hfix : fixV P = ⊥)
    (hgen : ∀ W : Subgroup V, (∀ g ∈ X, ∀ z ∈ fixV Tb, g z ∈ W) → W = ⊤) :
    (p = 3 ∧ Nat.card Tb = 4) ∨ ∃ L₁ L₂, Blocks14612 X Tb P p L₁ L₂ := by
  by_cases hO : IsOFourPlusAct X
  · obtain ⟨-, L₁, L₂, hB, -⟩ := class_aut_O4 h hO
    exact Or.inr ⟨L₁, L₂, hB⟩
  · exact class_aut_not_O4 h hfix hgen hO

end ClassAut

end CFSG.Quasithin
