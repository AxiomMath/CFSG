module

public import CFSG.Quasithin.EmptyFaithful.S14612GA0
public import CFSG.Quasithin.EmptyFaithful.S14612EA
public import CFSG.Quasithin.EmptyFaithful.S151cOrbI
public import CFSG.Quasithin.EmptyFaithful.S151cShapeE27
public import CFSG.Quasithin.EmptyFaithful.S151cShapeNine
public import CFSG.Quasithin.EmptyFaithful.S151cShapeOmega

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

section ClassAutShape

variable {V : Type} [CommGroup V] [Finite V] {X Tb P : Subgroup (MulAut V)} {p : ℕ}

private theorem card_Tb_of_ofour_GA1 (h : PStr14612 X Tb P p) (hO : IsOFourPlusAct X) :
    Nat.card Tb = 8 := by
  obtain ⟨hcard, q, hq1, hq2, hq3, hXq⟩ := hO
  have hexp : ∀ w : V, w * w = 1 := fun w => by rw [← pow_two]; exact h.sq w
  obtain ⟨L₁, L₂, t, hS, -⟩ := exists_ofourStruct_of_plusType hexp hcard hq1 hq2 hq3
  rw [← hXq] at hS
  exact hS.card_T h.syl

omit [CommGroup V] [Finite V] in
private theorem inf_eq_bot_GA1 {G : Type*} [Group G] {A B : Subgroup G} (hA : Nat.card A = 9)
    (hB : Nat.card B = 4) : A ⊓ B = ⊥ := by
  have h1 : Nat.card ↥(A ⊓ B) ∣ 9 := hA ▸ Subgroup.card_dvd_of_le inf_le_left
  have h2 : Nat.card ↥(A ⊓ B) ∣ 4 := hB ▸ Subgroup.card_dvd_of_le inf_le_right
  have h3 := Nat.dvd_gcd h1 h2
  exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp (by simpa using h3))

private theorem card_X_GA1 (h : PStr14612 X Tb P p) (hP : Nat.card P = 9)
    (hTb : Nat.card Tb = 4) : Nat.card X = 36 := by
  have := card_sup_of_normalizes h.tb_le_normalizer (inf_eq_bot_GA1 hP hTb)
  rw [← h.eq, hP, hTb] at this
  exact this

private theorem card_P_eq_nine_GA1 (h : PStr14612 X Tb P 3) (hdvd : Nat.card P ∣ 36) :
    Nat.card P = 9 := by
  obtain ⟨n, hn⟩ := h.card_eq_pow
  have h9 := h.nine_le_card
  have hle : Nat.card P ≤ 36 := Nat.le_of_dvd (by norm_num) hdvd
  have hn4 : n < 4 := by
    by_contra hcon
    have h81 : 3 ^ 4 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hcon)
    rw [← hn] at h81
    norm_num at h81
    omega
  interval_cases n
  · rw [pow_zero] at hn
    omega
  · rw [pow_one] at hn
    omega
  · rw [hn]
    norm_num
  · rw [hn] at hdvd
    norm_num at hdvd

private theorem Jhat_eq_of_card_GA1 (h : PStr14612 X Tb P 3) (hTb : Nat.card Tb = 4)
    (hJ : Nat.card (Jhat X) = 36) : Jhat X = X := by
  have hdvd : Nat.card P ∣ 36 := hJ ▸ Subgroup.card_dvd_of_le h.P_le_Jhat
  have hX := card_X_GA1 h (card_P_eq_nine_GA1 h hdvd) hTb
  exact Subgroup.eq_of_le_of_card_ge (Jhat_le X) (by rw [hX, hJ])

omit [Finite V] in
private theorem le_normalizer_of_comm_GA1 {A B : Subgroup (MulAut V)}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : B ≤ Subgroup.normalizer (A : Set (MulAut V)) :=
  fun b hb => Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.mpr fun a ha => hcomm a ha b hb)

omit [Finite V] in
private theorem sup_le_normalizer_GA1 {A B : Subgroup (MulAut V)}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : A ⊔ B ≤ Subgroup.normalizer (A : Set (MulAut V)) :=
  sup_le Subgroup.le_normalizer (le_normalizer_of_comm_GA1 hcomm)

omit [Finite V] in
private theorem exists_orderOf_dihedral_GA1 {A : Subgroup (MulAut V)} {n : ℕ} [NeZero n]
    (e : ↥A ≃* DihedralGroup n) : ∃ x ∈ A, orderOf x = n := by
  refine ⟨((e.symm (DihedralGroup.r 1) : ↥A) : MulAut V), (e.symm (DihedralGroup.r 1)).2, ?_⟩
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  exact DihedralGroup.orderOf_r_one

private theorem exists_inv_Tb_GA1 (h : PStr14612 X Tb P 3) (hTb : Nat.card Tb = 4)
    (hP9 : Nat.card P = 9) (hexp : ∀ a ∈ P, a ^ 3 = 1) {t : MulAut V} (htX : t ∈ X)
    (ht2 : orderOf t = 2) (htinv : ∀ a ∈ P, t * a * t⁻¹ = a⁻¹) :
    ∃ s ∈ Tb, orderOf s = 2 ∧ ∀ a ∈ P, s * a * s⁻¹ = a⁻¹ := by
  obtain ⟨a, ha, s, hs, rfl⟩ := h.exists_mul htX
  have hPn : ∀ y ∈ P, s * y * s⁻¹ ∈ P := fun y hy => h.normal s (h.tb_le hs) y hy
  have hsq : s * s = 1 := by
    have h1 : (a * s) * (a * s) = 1 := by
      rw [← pow_two]
      have := pow_orderOf_eq_one (a * s)
      rwa [ht2] at this
    have e : (a * s) * (a * s) = (a * (s * a * s⁻¹)) * (s * s) := by group
    rw [e] at h1
    have h2 : s * s = (a * (s * a * s⁻¹))⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hmemP : s * s ∈ P := by
      rw [h2]
      exact P.inv_mem (P.mul_mem ha (hPn a ha))
    have hmemT : s * s ∈ Tb := Tb.mul_mem hs hs
    have : s * s ∈ P ⊓ Tb := ⟨hmemP, hmemT⟩
    rw [inf_eq_bot_GA1 hP9 hTb, Subgroup.mem_bot] at this
    exact this
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [mul_one] at ht2
    have h3 : a ^ 3 = 1 := hexp a ha
    have h2 : a ^ 2 = 1 := by
      have := pow_orderOf_eq_one a
      rwa [ht2] at this
    have : a = 1 := by
      calc a = a ^ 3 * (a ^ 2)⁻¹ := by group
        _ = 1 := by rw [h3, h2]; group
    rw [this, orderOf_one] at ht2
    omega
  refine ⟨s, hs, ?_, fun x hx => ?_⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hsq) hs1
  · have hy := hPn x hx
    have hc := h.abelian a ha _ hy
    have e : a * s * x * (a * s)⁻¹ = a * (s * x * s⁻¹) * a⁻¹ := by group
    have h4 := htinv x hx
    rw [e, hc] at h4
    simpa using h4

private def rotFst_GA1 : Subgroup (DihedralGroup 3 × DihedralGroup 3) where
  carrier := {x | ∃ i : ZMod 3, x = (DihedralGroup.r i, 1)}
  one_mem' := ⟨0, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨i + j, rfl⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact ⟨-i, rfl⟩

private def rotSnd_GA1 : Subgroup (DihedralGroup 3 × DihedralGroup 3) where
  carrier := {x | ∃ i : ZMod 3, x = (1, DihedralGroup.r i)}
  one_mem' := ⟨0, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨i + j, rfl⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact ⟨-i, rfl⟩

private theorem rotFst_GA1_normal :
    ∀ (g : DihedralGroup 3 × DihedralGroup 3) (i : ZMod 3),
      ∃ j : ZMod 3, g * (DihedralGroup.r i, 1) * g⁻¹ = (DihedralGroup.r j, 1) := by
  decide +kernel

private theorem rotSnd_GA1_normal :
    ∀ (g : DihedralGroup 3 × DihedralGroup 3) (i : ZMod 3),
      ∃ j : ZMod 3, g * (1, DihedralGroup.r i) * g⁻¹ = (1, DihedralGroup.r j) := by
  decide +kernel

private theorem rot_cube_GA1 : ∀ i : ZMod 3, (DihedralGroup.r i : DihedralGroup 3) ^ 3 = 1 := by
  decide +kernel

private theorem false_of_d33_GA1 (h : PStr14612 X Tb P p) (hXJ : X = Jhat X)
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
  obtain ⟨hN₁P, hN₁n⟩ := key rotFst_GA1
    (by
      rintro g _ ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := rotFst_GA1_normal g i
      exact ⟨j, hj⟩)
    (by
      rintro _ ⟨i, rfl⟩
      exact Prod.ext (rot_cube_GA1 i) (by simp))
  obtain ⟨hN₂P, hN₂n⟩ := key rotSnd_GA1
    (by
      rintro g _ ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := rotSnd_GA1_normal g i
      exact ⟨j, hj⟩)
    (by
      rintro _ ⟨i, rfl⟩
      exact Prod.ext (by simp) (rot_cube_GA1 i))
  have hN₁ne := hne rotFst_GA1 (DihedralGroup.r 1, 1) ⟨1, rfl⟩ (by decide)
  have hN₂ne := hne rotSnd_GA1 (1, DihedralGroup.r 1) ⟨1, rfl⟩ (by decide)
  have hN₁eq := (h.minimal _ hN₁P hN₁n).resolve_left hN₁ne
  have hN₂eq := (h.minimal _ hN₂P hN₂n).resolve_left hN₂ne
  have hinf : ((rotFst_GA1.comap e.toMonoidHom).map (Jhat X).subtype) ⊓
      ((rotSnd_GA1.comap e.toMonoidHom).map (Jhat X).subtype) = ⊥ := by
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

private theorem class_aut_shape_not_O4 (h : PStr14612 X Tb P 3) (hfix : fixV P = ⊥)
    (hgen : ∀ W : Subgroup V, (∀ g ∈ X, ∀ z ∈ fixV Tb, g z ∈ W) → W = ⊤)
    (hO : ¬ IsOFourPlusAct X) (hTb : Nat.card Tb = 4) : E9Z4Str X Tb P := by
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
    ·
      obtain ⟨-, -, ⟨eT⟩⟩ := shape_Nine B hE hF9 ht hr' hrk
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hPF : P ≤ fittingOf (Jhat X) :=
        le_fittingOf_of_normal_nilpotent hPJ
          (fun x hx n hn => h.normal x (Jhat_le X hx) n hn) h.pgrp.isNilpotent
      have hP9 : Nat.card P = 9 := le_antisymm (hF9 ▸ Subgroup.card_le_of_le hPF) h9
      have hPeq : P = fittingOf (Jhat X) :=
        Subgroup.eq_of_le_of_card_ge hPF (by rw [hF9, hP9])
      have hexpP : ∀ a ∈ P, a ^ 3 = 1 := fun a ha => hE.2 a (hPeq ▸ ha)
      obtain ⟨P₁, P₂, h1, h2, hdisj, hsup, hle12, hle21, hFsup, hchar⟩ :=
        exists_planes_E9 B.sq hE hF9 B.hyp.comm_fitting hrk
      have hpl : E9Planes151c (Jhat X) P₁ P₂ := ⟨h1, h2, hdisj, hsup, hle12, hle21, hFsup, hchar⟩
      have hXT : Tb ⊔ fittingOf (Jhat X) = X := by rw [← hPeq, sup_comm, ← h.eq]
      obtain ⟨σ, hσT, hσ⟩ := hpl.exists_swap B.normal B.le B.setting hXT
      obtain ⟨t₀, ht₀J, ht₀2, ht₀inv, -⟩ := ht
      have hinv := exists_inv_Tb_GA1 h hTb hP9 hexpP (Jhat_le X ht₀J) ht₀2
        (fun a ha => ht₀inv a (hPeq ▸ ha))
      refine ⟨h.sq, hfix, h.eq, h.normal, hrk, hP9, h.abelian, hexpP, hTb,
        (MulEquiv.isCyclic eT).mpr inferInstance, hinv, ?_⟩
      exact ⟨P₁, P₂, hPeq ▸ hpl.le_fittingOf₁, hPeq ▸ hpl.le_fittingOf₂, hpl.card₁, hpl.card₂,
        hPeq ▸ hFsup, hdisj, hsup, hle12, hle21, σ, hσT, hσ⟩
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
      exact false_of_d33_GA1 h hA3.2.1 eΩ
    · exact absurd (oneBlock_not_shape6 B h6) id
  ·
    exfalso
    have hJ' : Jhat X = L₁ ⊔ L₂ := hcase.1.trans hKL
    obtain ⟨-, ⟨p', hp', hA6⟩, -⟩ :=
      twoOrbit_cases hS hr hr2 hI h1 h2 hne hx₂ e₂ horb hJ' hcase.2 hO
    obtain ⟨-, A₁, A₂, ⟨hJA, hA12, hAc⟩, ⟨eA₁⟩, ⟨eA₂⟩, -⟩ := hA6
    have hp3 : p' = 3 := by
      rcases hp' with rfl | rfl
      · rfl
      · exfalso
        obtain ⟨x, hxA, hxo⟩ := exists_orderOf_dihedral_GA1 eA₁
        have hxX : x ∈ X := Jhat_le X (by rw [hJA]; exact Subgroup.mem_sup_left hxA)
        have := h.prime_eq_of_orderOf hxX (by norm_num) (by norm_num) hxo
        omega
    subst hp3
    have hJ36 : Nat.card (Jhat X) = 36 := by
      rw [hJA, card_sup_of_normalizes (le_normalizer_of_comm_GA1 hAc) hA12,
        card_of_dihedral ⟨eA₁⟩, card_of_dihedral ⟨eA₂⟩]
    have hJX : Jhat X = X := Jhat_eq_of_card_GA1 h hTb hJ36
    have hx₂' : x₂ ∈ L₁ ⊔ L₂ := by rw [← hJ', hJX]; exact hx₂
    have hcomm := hI.comm L₁ h1 L₂ h2 hne.symm
    exact hne (e₂.symm.trans (conjBy_eq_of_mem_normalizer (sup_le_normalizer_GA1 hcomm hx₂')))

theorem class_aut_shape (h : PStr14612 X Tb P p) (hfix : fixV P = ⊥)
    (hgen : ∀ W : Subgroup V, (∀ g ∈ X, ∀ z ∈ fixV Tb, g z ∈ W) → W = ⊤)
    (hp : p = 3) (hTb : Nat.card Tb = 4) : E9Z4Str X Tb P := by
  subst hp
  refine class_aut_shape_not_O4 h hfix hgen (fun hO => ?_) hTb
  have := card_Tb_of_ofour_GA1 h hO
  omega

end ClassAutShape

end CFSG.Quasithin
