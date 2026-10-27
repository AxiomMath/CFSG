module

public import CFSG.Quasithin.H13.NQCoreP134X27Cfg
public import CFSG.Quasithin.Vol2.F134LieOddBasic

public section

namespace CFSG.Quasithin.H13.KGX27

open CFSG.Quasithin.H13.NQCore CFSG.Quasithin.F134.LieOdd
open scoped commutatorElement

@[expose] def X27Inv (X : Type*) [Group X] : Prop :=
  ∀ P U : Subgroup X, Nat.card P = 27 → (∀ x ∈ P, x ^ 3 = 1) → IsPGroup 2 U → ¬ 2 ∣ U.index →
    Nat.card (P ⊔ U : Subgroup X) = 27 * Nat.card U →
    ∃ Q : Subgroup X, Q ≤ P ∧ Nat.card Q = 9 ∧ ∀ α : X ≃* X,
      P.map α.toMonoidHom = P → U.map α.toMonoidHom = U → Q.map α.toMonoidHom = Q

theorem X27Inv.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (h : X27Inv Y) :
    X27Inv X := by
  intro P U hP hexp hU hidx hcard
  have hinj := e.injective
  obtain ⟨Q, hQP, hQ9, hQ⟩ := h (P.map e.toMonoidHom) (U.map e.toMonoidHom)
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
  · rw [Subgroup.card_map_of_injective e.symm.injective, hQ9]
  · have hβ := hQ (e.symm.trans (α.trans e))
      (by rw [map_conj_mulEquiv, hαP]) (by rw [map_conj_mulEquiv, hαU])
    have hβ' : ((Q.map e.symm.toMonoidHom).map α.toMonoidHom).map e.toMonoidHom =
        (Q.map e.symm.toMonoidHom).map e.toMonoidHom := by
      rw [← map_conj_mulEquiv, map_map_symm]
      exact hβ
    exact Subgroup.map_injective e.injective hβ'

theorem exists_invariant_of_map' {X : Type*} [Group X] (φ : X ≃* X) {P U : Subgroup X} {n : ℕ}
    (h : ∃ Q : Subgroup X, Q ≤ P.map φ.toMonoidHom ∧ Nat.card Q = n ∧ ∀ α : X ≃* X,
      (P.map φ.toMonoidHom).map α.toMonoidHom = P.map φ.toMonoidHom →
      (U.map φ.toMonoidHom).map α.toMonoidHom = U.map φ.toMonoidHom →
      Q.map α.toMonoidHom = Q) :
    ∃ Q : Subgroup X, Q ≤ P ∧ Nat.card Q = n ∧ ∀ α : X ≃* X,
      P.map α.toMonoidHom = P → U.map α.toMonoidHom = U → Q.map α.toMonoidHom = Q := by
  obtain ⟨Q, hQP, hQn, hQ⟩ := h
  refine ⟨Q.map φ.symm.toMonoidHom, ?_, ?_, fun α hαP hαU => ?_⟩
  · calc Q.map φ.symm.toMonoidHom ≤ (P.map φ.toMonoidHom).map φ.symm.toMonoidHom :=
          Subgroup.map_mono hQP
      _ = P := map_symm_map φ P
  · rw [Subgroup.card_map_of_injective φ.symm.injective, hQn]
  · have hβ := hQ (φ.symm.trans (α.trans φ))
      (by rw [map_conj_mulEquiv, hαP]) (by rw [map_conj_mulEquiv, hαU])
    have hβ' : ((Q.map φ.symm.toMonoidHom).map α.toMonoidHom).map φ.toMonoidHom =
        (Q.map φ.symm.toMonoidHom).map φ.toMonoidHom := by
      rw [← map_conj_mulEquiv, map_map_symm]
      exact hβ
    exact Subgroup.map_injective φ.injective hβ'

theorem commutator_le_of_card_27 {X : Type*} [Group X] {P Q : Subgroup X} (hQP : Q ≤ P)
    (hP : Nat.card P = 27) (hQ : Nat.card Q = 9) : ⁅P, P⁆ ≤ Q := by
  have : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; norm_num)
  have hidx : (Q.subgroupOf P).index = 3 := by
    have h := Subgroup.card_mul_index (Q.subgroupOf P)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv, hQ, hP] at h
    omega
  have : (Q.subgroupOf P).Normal :=
    Subgroup.normal_of_index_eq_minFac_card (by rw [hidx, hP]; norm_num)
  have hQ3 : Nat.card (↥P ⧸ Q.subgroupOf P) = 3 := hidx
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsCyclic (↥P ⧸ Q.subgroupOf P) := isCyclic_of_prime_card hQ3
  have hcomm : ∀ x y : ↥P ⧸ Q.subgroupOf P, x * y = y * x := fun x y => by
    let := IsCyclic.commGroup (α := ↥P ⧸ Q.subgroupOf P)
    exact mul_comm x y
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have h1 : (⁅(⟨x, hx⟩ : ↥P), ⟨y, hy⟩⁆ : ↥P) ∈ Q.subgroupOf P := by
    rw [← QuotientGroup.eq_one_iff]
    rw [commutatorElement_def]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hcomm (QuotientGroup.mk ⟨x, hx⟩) (QuotientGroup.mk ⟨y, hy⟩)]
    group
  exact Subgroup.mem_subgroupOf.mp h1

section Config

variable {A : Type} [Group A]

theorem mem_normalizer_inf {L T : Subgroup A} (hLn : L.Normal) {t : A} (htT : t ∈ T) :
    t ∈ Subgroup.normalizer ((T ⊓ L : Subgroup A) : Set A) := by
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

theorem le_normalizer_map {L P T : Subgroup A} (hLn : L.Normal) (Q' : Subgroup L)
    (hQ' : ∀ α : ↥L ≃* ↥L, (P.subgroupOf L).map α.toMonoidHom = P.subgroupOf L →
      ((T ⊓ L).subgroupOf L).map α.toMonoidHom = (T ⊓ L).subgroupOf L →
      Q'.map α.toMonoidHom = Q') :
    T ⊓ Subgroup.normalizer (P : Set A) ≤ Subgroup.normalizer ((Q'.map L.subtype : Subgroup A) :
      Set A) := by
  have := hLn
  rintro t ⟨htT, htP⟩
  have hα := hQ' (MulAut.conjNormal t) (map_conjNormal_subgroupOf htP)
    (map_conjNormal_subgroupOf (mem_normalizer_inf hLn htT))
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

theorem noX27Simple_of_x27Inv {F : ∀ (X : Type) [Group X], Prop}
    (hF : ∀ (X : Type) [Group X], F X → X27Inv X) : NoX27Simple F := by
  intro A _ _ L P T hcfg h27 hL
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPL := hcfg.le
  have hS := OddConfig.isSylowTwoOf_inf hcfg
  have hTL : T ⊓ L ≤ L := inf_le_right
  obtain ⟨Q', hQ'P, hQ'9, hQ'⟩ := hF L hL (P.subgroupOf L) ((T ⊓ L).subgroupOf L)
    (by rw [← h27]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv)
    (fun x hx => Subtype.ext (by simpa using hcfg.exp x (Subgroup.mem_subgroupOf.mp hx)))
    (hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTL).symm)
    hS.2.2
    (by
      rw [← Subgroup.subgroupOf_sup hPL hTL,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sup_le hPL hTL)).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv]
      exact OddConfig.card_sup_inf_x27 hcfg h27)
  set Q := Q'.map L.subtype with hQdef
  have hQP : Q ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hQ'P hx)
  have hQ9 : Nat.card Q = 9 := by
    rw [Subgroup.card_map_of_injective L.subtype_injective, hQ'9]
  have hnorm := le_normalizer_map hcfg.normal Q' hQ'
  rcases hcfg.irred Q (commutator_le_of_card_27 hQP h27 hQ9) hQP hnorm with h | h
  · have hle := card_commutator_le (G := A) (p := 3) hcfg.exp (by rw [h27]; norm_num)
      (by rw [h27]; norm_num)
    rw [← h, hQ9] at hle
    omega
  · rw [h, h27] at hQ9
    omega

theorem noE9Cfg_of_e9Inv {F : ∀ (X : Type) [Group X], Prop}
    (hF : ∀ (X : Type) [Group X], F X → E9Inv X) : NoE9Cfg F := by
  intro A _ _ L P T hL hcfg
  have hPL := hcfg.le
  have hS := E9Cfg.isSylowTwoOf_inf hcfg
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
      exact E9Cfg.card_sup_inf hcfg)
  set Q := Q'.map L.subtype with hQdef
  have hQP : Q ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hQ'P hx)
  have hQ3 : Nat.card Q = 3 := by
    rw [Subgroup.card_map_of_injective L.subtype_injective, hQ'3]
  rcases hcfg.irred Q hQP (le_normalizer_map hcfg.normal Q' hQ') with h | h
  · rw [h, Subgroup.card_bot] at hQ3
    omega
  · rw [h, hcfg.card] at hQ3
    omega

end Config

end CFSG.Quasithin.H13.KGX27
