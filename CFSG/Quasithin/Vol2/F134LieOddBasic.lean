module

public import CFSG.Quasithin.Vol2.F134Basic

public section

namespace CFSG.Quasithin.F134.LieOdd

open CFSG.Quasithin.P134 CFSG.QuasithinUnique

@[expose] def E9Inv (X : Type*) [Group X] : Prop :=
  ∀ P U : Subgroup X, Nat.card P = 9 → (∀ x ∈ P, x ^ 3 = 1) → IsPGroup 2 U → ¬ 2 ∣ U.index →
    Nat.card (P ⊔ U : Subgroup X) = 9 * Nat.card U →
    ∃ Q : Subgroup X, Q ≤ P ∧ Nat.card Q = 3 ∧ ∀ α : X ≃* X,
      P.map α.toMonoidHom = P → U.map α.toMonoidHom = U → Q.map α.toMonoidHom = Q

theorem map_symm_map {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (K : Subgroup X) :
    (K.map e.toMonoidHom).map e.symm.toMonoidHom = K := by
  ext x
  simp

theorem map_map_symm {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (K : Subgroup Y) :
    (K.map e.symm.toMonoidHom).map e.toMonoidHom = K := by
  ext x
  simp

theorem map_conj_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (α : X ≃* X)
    (K : Subgroup X) :
    (K.map e.toMonoidHom).map (e.symm.trans (α.trans e)).toMonoidHom =
      (K.map α.toMonoidHom).map e.toMonoidHom := by
  ext y
  simp only [Subgroup.mem_map_equiv, MulEquiv.symm_trans_apply, MulEquiv.symm_symm,
    MulEquiv.symm_apply_apply]

theorem E9Inv.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (h : E9Inv Y) :
    E9Inv X := by
  intro P U hP hexp hU hidx hcard
  have hinj := e.injective
  obtain ⟨Q, hQP, hQ3, hQ⟩ := h (P.map e.toMonoidHom) (U.map e.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective hinj, hP])
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hexp x hx, map_one])
    (hU.map e.toMonoidHom)
    (by rwa [show (U.map e.toMonoidHom).index = U.index from Subgroup.index_map_equiv U e])
    (by
      rw [← Subgroup.map_sup, Subgroup.card_map_of_injective hinj,
        Subgroup.card_map_of_injective hinj, hcard])
  refine ⟨Q.map e.symm.toMonoidHom, ?_, ?_, fun α hαP hαU => ?_⟩
  · calc Q.map e.symm.toMonoidHom ≤ (P.map e.toMonoidHom).map e.symm.toMonoidHom :=
          Subgroup.map_mono hQP
      _ = P := map_symm_map e P
  · rw [Subgroup.card_map_of_injective e.symm.injective, hQ3]
  · have hβ := hQ (e.symm.trans (α.trans e))
      (by rw [map_conj_mulEquiv, hαP]) (by rw [map_conj_mulEquiv, hαU])
    have hβ' : ((Q.map e.symm.toMonoidHom).map α.toMonoidHom).map e.toMonoidHom =
        (Q.map e.symm.toMonoidHom).map e.toMonoidHom := by
      rw [← map_conj_mulEquiv, map_map_symm]
      exact hβ
    exact Subgroup.map_injective e.injective hβ'

theorem exists_invariant_of_map {X : Type*} [Group X] (φ : X ≃* X) {P U : Subgroup X}
    (h : ∃ Q : Subgroup X, Q ≤ P.map φ.toMonoidHom ∧ Nat.card Q = 3 ∧ ∀ α : X ≃* X,
      (P.map φ.toMonoidHom).map α.toMonoidHom = P.map φ.toMonoidHom →
      (U.map φ.toMonoidHom).map α.toMonoidHom = U.map φ.toMonoidHom →
      Q.map α.toMonoidHom = Q) :
    ∃ Q : Subgroup X, Q ≤ P ∧ Nat.card Q = 3 ∧ ∀ α : X ≃* X,
      P.map α.toMonoidHom = P → U.map α.toMonoidHom = U → Q.map α.toMonoidHom = Q := by
  obtain ⟨Q, hQP, hQ3, hQ⟩ := h
  refine ⟨Q.map φ.symm.toMonoidHom, ?_, ?_, fun α hαP hαU => ?_⟩
  · calc Q.map φ.symm.toMonoidHom ≤ (P.map φ.toMonoidHom).map φ.symm.toMonoidHom :=
          Subgroup.map_mono hQP
      _ = P := map_symm_map φ P
  · rw [Subgroup.card_map_of_injective φ.symm.injective, hQ3]
  · have hβ := hQ (φ.symm.trans (α.trans φ))
      (by rw [map_conj_mulEquiv, hαP]) (by rw [map_conj_mulEquiv, hαU])
    have hβ' : ((Q.map φ.symm.toMonoidHom).map α.toMonoidHom).map φ.toMonoidHom =
        (Q.map φ.symm.toMonoidHom).map φ.toMonoidHom := by
      rw [← map_conj_mulEquiv, map_map_symm]
      exact hβ
    exact Subgroup.map_injective φ.injective hβ'

section Config

variable {A : Type} [Group A]

theorem map_conjNormal_subgroupOf {L B : Subgroup A} [L.Normal] {t : A}
    (ht : t ∈ Subgroup.normalizer (B : Set A)) :
    (B.subgroupOf L).map (MulAut.conjNormal t).toMonoidHom = B.subgroupOf L := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  have h : (((MulAut.conjNormal t).symm x : L) : A) = t⁻¹ * x * t := by
    have : (MulAut.conjNormal t).symm x = MulAut.conjNormal t⁻¹ x := by
      rw [map_inv]
      rfl
    rw [this, MulAut.conjNormal_apply, inv_inv]
  rw [h]
  exact ((Subgroup.mem_normalizer_iff''.1 ht) x).symm

theorem noE9Config_of_e9Inv {F : ∀ (X : Type) [Group X], Prop}
    (hF : ∀ (X : Type) [Group X], F X → E9Inv X) : NoE9Config F := by
  intro A _ _ L P T hL hcfg
  have hLn := hcfg.normal
  have hPL := hcfg.le
  have hS := E9Config.isSylowTwoOf_inf hcfg
  have hTL : T ⊓ L ≤ L := inf_le_right
  obtain ⟨Q', hQ'P, hQ'3, hQ'⟩ := hF L hL (P.subgroupOf L) ((T ⊓ L).subgroupOf L)
    (by rw [← hcfg.card]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv)
    (fun x hx => Subtype.ext (by simpa using hcfg.exp x (Subgroup.mem_subgroupOf.mp hx)))
    (hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTL).symm)
    hS.2.2
    (by
      rw [← Subgroup.subgroupOf_sup hPL hTL,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sup_le hPL hTL)).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv]
      exact E9Config.card_sup_inf hcfg)
  set Q := Q'.map L.subtype with hQdef
  have hQP : Q ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hQ'P hx)
  have hQ3 : Nat.card Q = 3 := by
    rw [Subgroup.card_map_of_injective L.subtype_injective, hQ'3]
  have hnorm : T ⊓ Subgroup.normalizer (P : Set A) ≤ Subgroup.normalizer (Q : Set A) := by
    rintro t ⟨htT, htP⟩
    have htTL : t ∈ Subgroup.normalizer ((T ⊓ L : Subgroup A) : Set A) := by
      rw [Subgroup.mem_normalizer_iff]
      intro g
      constructor
      · rintro ⟨hgT, hgL⟩
        exact ⟨T.mul_mem (T.mul_mem htT hgT) (T.inv_mem htT), hLn.conj_mem g hgL t⟩
      · rintro ⟨hgT, hgL⟩
        refine ⟨?_, ?_⟩
        · have := T.mul_mem (T.mul_mem (T.inv_mem htT) hgT) htT
          rwa [show t⁻¹ * (t * g * t⁻¹) * t = g by group] at this
        · have := hLn.conj_mem _ hgL t⁻¹
          rwa [show t⁻¹ * (t * g * t⁻¹) * t⁻¹⁻¹ = g by group] at this
    have hα := hQ' (MulAut.conjNormal t) (map_conjNormal_subgroupOf htP)
      (map_conjNormal_subgroupOf htTL)
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : MulAut.conjNormal t x ∈ Q' := by
        rw [← hα]
        exact ⟨x, hx, rfl⟩
      exact ⟨_, hx', by simp [MulAut.conjNormal_apply]⟩
    · rintro ⟨y, hy, hyg⟩
      have hyg' : (y : A) = t * g * t⁻¹ := hyg
      have hgL : g ∈ L := by
        have := hLn.conj_mem _ y.2 t⁻¹
        rwa [hyg', show t⁻¹ * (t * g * t⁻¹) * t⁻¹⁻¹ = g by group] at this
      refine ⟨⟨g, hgL⟩, ?_, rfl⟩
      rw [← hα] at hy
      obtain ⟨x, hx, hxy⟩ := hy
      have hxg : x = ⟨g, hgL⟩ := by
        apply Subtype.ext
        have h1 : t * (x : A) * t⁻¹ = (y : A) := by
          rw [← MulAut.conjNormal_apply]
          exact congrArg Subtype.val hxy
        rw [hyg'] at h1
        simpa using h1
      rw [← hxg]
      exact hx
  rcases hcfg.irred Q hQP hnorm with h | h
  · rw [h, Subgroup.card_bot] at hQ3
    omega
  · rw [h, hcfg.card] at hQ3
    omega

end Config

theorem exists_involution_pow {G : Type*} [Group G] {u : G} (hu : u ≠ 1) {k : ℕ}
    (hk : u ^ 2 ^ k = 1) : ∃ j : ℕ, (u ^ 2 ^ j) ^ 2 = 1 ∧ u ^ 2 ^ j ≠ 1 := by
  classical
  have hex : ∃ i, u ^ 2 ^ i = 1 := ⟨k, hk⟩
  have hi1 : u ^ 2 ^ Nat.find hex = 1 := Nat.find_spec hex
  have hi0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, pow_zero, pow_one] at hi1
    exact hu hi1
  refine ⟨Nat.find hex - 1, ?_, Nat.find_min hex (by omega)⟩
  rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (by omega)]
  exact hi1

@[expose] def powSubgroup {G : Type*} [Group G] (B : Subgroup G)
    (hB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (n : ℕ) : Subgroup G where
  carrier := {x | x ∈ B ∧ x ^ n = 1}
  mul_mem' := fun {a b} ha hb => ⟨B.mul_mem ha.1 hb.1, by
    rw [Commute.mul_pow (hB a ha.1 b hb.1), ha.2, hb.2, one_mul]⟩
  one_mem' := ⟨B.one_mem, one_pow n⟩
  inv_mem' := fun {a} ha => ⟨B.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

theorem card_eq_three_of_lt {X : Type*} [Group X] {P R : Subgroup X} (hP : Nat.card P = 9)
    (hRP : R ≤ P) (hR1 : R ≠ ⊥) (hR9 : R ≠ P) : Nat.card R = 3 := by
  have : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; norm_num)
  have hdvd : Nat.card R ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hP]
    exact Subgroup.card_dvd_of_le hRP
  obtain ⟨i, hi, hRi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  interval_cases i
  · exact absurd (Subgroup.eq_bot_of_card_eq R (by rw [hRi]; norm_num)) hR1
  · rw [hRi]; norm_num
  · exact absurd (Subgroup.eq_of_le_of_card_ge hRP (by rw [hP, hRi]; norm_num)) hR9

theorem sup_eq_of_card_three {X : Type*} [Group X] {P R R' : Subgroup X} (hP : Nat.card P = 9)
    (hR : R ≤ P) (hR' : R' ≤ P) (h3 : Nat.card R = 3) (h3' : Nat.card R' = 3) (hne : R ≠ R') :
    R ⊔ R' = P := by
  have : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; norm_num)
  have hle : R ⊔ R' ≤ P := sup_le hR hR'
  by_contra hne'
  have h3'' : Nat.card (R ⊔ R' : Subgroup X) = 3 := card_eq_three_of_lt hP hle (by
    intro hbot
    have : R = ⊥ := le_bot_iff.1 (hbot ▸ le_sup_left)
    rw [this, Subgroup.card_bot] at h3
    omega) hne'
  have : Finite (R ⊔ R' : Subgroup X) := Nat.finite_of_card_ne_zero (by rw [h3'']; norm_num)
  have e1 : R = R ⊔ R' := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h3'', h3])
  have e2 : R' = R ⊔ R' := Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [h3'', h3'])
  exact hne (e1.trans e2.symm)

end CFSG.Quasithin.F134.LieOdd
