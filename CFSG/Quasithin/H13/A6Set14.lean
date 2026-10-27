module

public import CFSG.Quasithin.H13.U3L14Producers
public import CFSG.Quasithin.H13.A6S1356Two
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem6
public import CFSG.Quasithin.H13.A5S1515a
public import CFSG.Quasithin.H13.A6HatPlusB

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

namespace S14

@[expose] def C3 : List (Perm (Fin 6)) :=
  [1, swap 0 1 * swap 1 2, swap 0 2 * swap 2 1, swap 0 1 * swap 1 3, swap 0 3 * swap 3 1,
    swap 0 2 * swap 2 3, swap 0 3 * swap 3 2, swap 1 2 * swap 2 3, swap 1 3 * swap 3 2]

theorem c3_facts : ∀ τ ∈ C3, τ 4 = 4 ∧ τ 5 = 5 ∧ Perm.sign τ = 1 ∧ τ ^ 3 = 1 := by
  decide +kernel

theorem alt4_prod : ∀ σ : Perm (Fin 6), σ 4 = 4 → σ 5 = 5 → Perm.sign σ = 1 →
    ∃ τ₁ ∈ C3, ∃ τ₂ ∈ C3, σ = τ₁ * τ₂ := by
  decide +kernel

theorem fix45_W3 : ∀ σ : Perm (Fin 6), σ 4 = 4 ∧ σ 5 = 5 → ∀ y : P6, InW4 y → InW3 y →
    InW3 (act4f σ y) := by
  decide +kernel

theorem gen_W3 : ∀ x : P6, InW4 x → InW3 x → ∃ τ ∈ C3, ∃ y : P6, InW2 y ∧ act4f τ y = x := by
  decide +kernel

@[expose] def span3 (y : P6) : List P6 :=
  [1, e0123, y, y * e0123, act4f (swap 0 1 * swap 1 2) y,
    act4f (swap 0 1 * swap 1 2) y * e0123, y * act4f (swap 0 1 * swap 1 2) y,
    y * act4f (swap 0 1 * swap 1 2) y * e0123]

theorem span3_W3 : ∀ y : P6, InW4 y → InW3 y → y ≠ 1 → y ≠ e0123 →
    ∀ x : P6, InW4 x → InW3 x → x ∈ span3 y := by
  decide +kernel

theorem comm_W3_K4 : ∀ κ ∈ K4L, ∀ y : P6, InW4 y → InW3 y →
    y * (act4f κ y)⁻¹ = 1 ∨ y * (act4f κ y)⁻¹ = e0123 := by
  decide +kernel

theorem comm_e01 : swap (0 : Fin 6) 2 * swap 1 3 ∈ K4L ∧
    dv 0 1 * (act4f (swap 0 2 * swap 1 3) (dv 0 1))⁻¹ = e0123 ∧ InW3 (dv 0 1) ∧
    swap (0 : Fin 6) 2 * swap 1 3 = (swap 0 1 * swap 1 2) * (swap 0 1 * swap 1 3) := by
  decide +kernel

@[expose] def E8 : List (Perm (Fin 6)) :=
  [1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2, swap 4 5,
    swap 0 1 * swap 2 3 * swap 4 5, swap 0 2 * swap 1 3 * swap 4 5, swap 0 3 * swap 1 2 * swap 4 5]

theorem e8_mul : ∀ a ∈ E8, ∀ b ∈ E8, a * b ∈ E8 := by decide +kernel

theorem e8_sq : ∀ a ∈ E8, a * a = 1 := by decide +kernel

@[expose] def E8sub : Subgroup (Perm (Fin 6)) where
  carrier := {σ | σ ∈ E8}
  mul_mem' := fun {a b} ha hb => e8_mul a ha b hb
  one_mem' := List.mem_cons_self
  inv_mem' := fun {a} ha => by
    show a⁻¹ ∈ E8
    rw [inv_eq_of_mul_eq_one_right (e8_sq a ha)]
    exact ha

theorem e8_norm : ∀ σ : Perm (Fin 6), (InD6 σ ∨ (σ 4 = 4 ∧ σ 5 = 5)) →
    ∀ e ∈ E8, σ * e * σ⁻¹ ∈ E8 := by
  decide +kernel

theorem e8_index : ∀ σ τ : Perm (Fin 6), InD6 σ → InD6 τ → σ ∉ E8 → τ ∉ E8 → σ⁻¹ * τ ∈ E8 := by
  have hD : ∀ σ : Perm (Fin 6), InD6 σ → σ ∈ [1, swap 0 1, swap 2 3, swap 0 1 * swap 2 3,
      swap 0 2 * swap 1 3, swap 0 3 * swap 1 2, swap 0 2 * swap 1 3 * swap 0 1,
      swap 0 2 * swap 1 3 * swap 2 3, swap 4 5, swap 0 1 * swap 4 5, swap 2 3 * swap 4 5,
      swap 0 1 * swap 2 3 * swap 4 5, swap 0 2 * swap 1 3 * swap 4 5,
      swap 0 3 * swap 1 2 * swap 4 5, swap 0 2 * swap 1 3 * swap 0 1 * swap 4 5,
      swap 0 2 * swap 1 3 * swap 2 3 * swap 4 5] := by
    decide +kernel
  have hL : ∀ σ ∈ [1, swap 0 1, swap 2 3, swap 0 1 * swap 2 3,
      swap 0 2 * swap 1 3, swap 0 3 * swap 1 2, swap 0 2 * swap 1 3 * swap 0 1,
      swap 0 2 * swap 1 3 * swap 2 3, swap 4 5, swap 0 1 * swap 4 5, swap 2 3 * swap 4 5,
      swap 0 1 * swap 2 3 * swap 4 5, swap 0 2 * swap 1 3 * swap 4 5,
      swap 0 3 * swap 1 2 * swap 4 5, swap 0 2 * swap 1 3 * swap 0 1 * swap 4 5,
      swap 0 2 * swap 1 3 * swap 2 3 * swap 4 5],
      ∀ τ ∈ [1, swap 0 1, swap 2 3, swap 0 1 * swap 2 3,
      swap 0 2 * swap 1 3, swap 0 3 * swap 1 2, swap 0 2 * swap 1 3 * swap 0 1,
      swap 0 2 * swap 1 3 * swap 2 3, swap 4 5, swap 0 1 * swap 4 5, swap 2 3 * swap 4 5,
      swap 0 1 * swap 2 3 * swap 4 5, swap 0 2 * swap 1 3 * swap 4 5,
      swap 0 3 * swap 1 2 * swap 4 5, swap 0 2 * swap 1 3 * swap 0 1 * swap 4 5,
      swap 0 2 * swap 1 3 * swap 2 3 * swap 4 5],
      σ ∉ E8 → τ ∉ E8 → (σ⁻¹ * τ : Perm (Fin 6)) ∈ E8 := by
    decide +kernel
  exact fun σ τ hσ hτ => hL σ (hD σ hσ) τ (hD τ hτ)

theorem D_A4 : ∀ σ : Perm (Fin 6), InD6 σ → σ 4 = 4 → σ 5 = 5 → Perm.sign σ = 1 → σ ∈ K4L := by
  decide +kernel

theorem K4_norm : ∀ σ : Perm (Fin 6), σ 4 = 4 ∧ σ 5 = 5 → ∀ κ ∈ K4L, σ * κ * σ⁻¹ ∈ K4L := by
  decide +kernel

theorem fix_e0123_of_pair : ∀ σ : Perm (Fin 6), ((σ 4 = 4 ∧ σ 5 = 5) ∨ (σ 4 = 5 ∧ σ 5 = 4)) →
    act4f σ e0123 = e0123 := by
  decide +kernel

@[expose] def RepWords : List (List ℕ) :=
  [[3], [3, 1], [3, 2], [3, 1, 0], [0, 2, 0], [0, 2], [0, 1], [3, 2, 0], [0, 1, 0], [0],
    [3, 1, 3], [3, 2, 3], [0, 2, 3], [0, 1, 3], []]

@[expose] def letter (i : ℕ) : Perm (Fin 6) :=
  if i = 0 then U3.a6s3 else if i = 1 then swap 0 1 * swap 1 2 else if i = 2 then
    swap 1 2 * swap 2 3 else U3.a6s3 * U3.a6s3

@[expose] def evalWord (w : List ℕ) : Perm (Fin 6) := (w.map letter).prod

theorem cosets_A6 : ∀ σ : Perm (Fin 6), Perm.sign σ = 1 → ∃ w ∈ RepWords,
    ((σ * (evalWord w)⁻¹) 4 = 4 ∧ (σ * (evalWord w)⁻¹) 5 = 5) ∨
      ((σ * (evalWord w)⁻¹) 4 = 5 ∧ (σ * (evalWord w)⁻¹) 5 = 4) := by
  decide +kernel

theorem repWords_lt : ∀ w ∈ RepWords, ∀ i ∈ w, i < 4 := by decide

theorem letter12_facts : (letter 1 4 = 4 ∧ letter 1 5 = 5 ∧ Perm.sign (letter 1) = 1) ∧
    (letter 2 4 = 4 ∧ letter 2 5 = 5 ∧ Perm.sign (letter 2) = 1) := by
  decide +kernel

theorem s3_move : act4f U3.a6s3 e0123 ≠ e0123 := by decide +kernel

theorem s3_move2 : act4f (U3.a6s3 * U3.a6s3) e0123 ≠ e0123 := by decide +kernel

theorem s3_sum : ∀ y : P6, InW4 y → ∃ y₁ : P6, ∃ y₂ : P6, InW4 y₁ ∧ InW3 y₁ ∧ InW4 y₂ ∧
    InW3 y₂ ∧ y = y₁ * act4f U3.a6s3 y₂ := by
  decide +kernel

theorem s3_sum2 : ∀ y : P6, InW4 y → ∃ y₁ : P6, ∃ y₂ : P6, InW4 y₁ ∧ InW3 y₁ ∧ InW4 y₂ ∧
    InW3 y₂ ∧ y = y₁ * act4f (U3.a6s3 * U3.a6s3) y₂ := by
  decide +kernel

theorem t0_facts : InD6 (swap 0 1 * swap 4 5) ∧ Perm.sign (swap 0 1 * swap 4 5 : Perm (Fin 6)) = 1 ∧
    ¬ InD6 ((swap 0 1 * swap 1 2) * (swap 0 1 * swap 4 5) * (swap 0 1 * swap 1 2)⁻¹) := by
  decide +kernel

theorem ab_facts : (swap 0 1 * swap 1 2) * (swap 0 1 * swap 4 5) * (swap 0 1 * swap 1 2)⁻¹ *
      (swap 0 1 * swap 4 5)⁻¹ = (swap 0 2 * swap 2 1 : Perm (Fin 6)) ∧
    (swap 0 1 * swap 1 3) * (swap 0 1 * swap 4 5) * (swap 0 1 * swap 1 3)⁻¹ *
      (swap 0 1 * swap 4 5)⁻¹ = (swap 0 3 * swap 3 1 : Perm (Fin 6)) ∧
    ∀ τ ∈ C3, ∃ x ∈ [(1 : Perm (Fin 6)), swap 0 2 * swap 2 1, swap 0 3 * swap 3 1],
      ∃ y ∈ [(1 : Perm (Fin 6)), swap 0 2 * swap 2 1, swap 0 3 * swap 3 1],
        ∃ m n : Fin 3, τ = x ^ (m : ℕ) * y ^ (n : ℕ) := by
  decide +kernel

@[expose] def A4sub : Subgroup (Perm (Fin 6)) where
  carrier := {σ | σ 4 = 4 ∧ σ 5 = 5 ∧ Perm.sign σ = 1}
  mul_mem' := fun {a b} ha hb => by
    obtain ⟨ha4, ha5, has⟩ := ha
    obtain ⟨hb4, hb5, hbs⟩ := hb
    refine ⟨?_, ?_, ?_⟩
    · rw [Perm.mul_apply, hb4, ha4]
    · rw [Perm.mul_apply, hb5, ha5]
    · rw [Perm.sign_mul, has, hbs, one_mul]
  one_mem' := ⟨rfl, rfl, Perm.sign_one⟩
  inv_mem' := fun {a} ha => by
    obtain ⟨ha4, ha5, has⟩ := ha
    exact ⟨Perm.inv_eq_iff_eq.2 ha4.symm, Perm.inv_eq_iff_eq.2 ha5.symm,
      by rw [Perm.sign_inv, has]⟩

theorem card_A4sub : Nat.card A4sub = 12 := by
  have : Fintype.card {σ : Perm (Fin 6) // σ 4 = 4 ∧ σ 5 = 5 ∧ Perm.sign σ = 1} = 12 := by
    decide +kernel
  rw [← this, ← Nat.card_eq_fintype_card]
  rfl

theorem card_K4sub' : Nat.card K4sub = 4 := by
  have : Fintype.card {σ : Perm (Fin 6) // σ ∈ K4L} = 4 := by decide +kernel
  rw [← this, ← Nat.card_eq_fintype_card]
  rfl

theorem K4L_A4 : ∀ σ ∈ K4L, σ 4 = 4 ∧ σ 5 = 5 ∧ Perm.sign σ = 1 := by decide +kernel

theorem K4sub_le_A4sub : K4sub ≤ A4sub := fun σ hσ => K4L_A4 σ hσ

theorem relIndex_K4_A4 : K4sub.relIndex A4sub = 3 := by
  have h := Subgroup.relIndex_mul_card (H := K4sub) (K := A4sub)
  rw [inf_eq_left.2 K4sub_le_A4sub, card_K4sub', card_A4sub] at h
  omega

theorem oTwoRes_idem {G : Type} [Group G] (X : Subgroup G) : oTwoRes (oTwoRes X) = oTwoRes X := by
  refine le_antisymm (oTwoRes_le _) ?_
  rw [oTwoRes, Subgroup.closure_le]
  rintro y ⟨hy, m, hm, hym⟩
  exact Subgroup.subset_closure ⟨Subgroup.subset_closure ⟨hy, m, hm, hym⟩, m, hm, hym⟩

theorem relIndex_le_two_of {G : Type} [Group G] [Finite G] {H K : Subgroup G}
    (h : ∀ a ∈ K, ∀ b ∈ K, a ∉ H → b ∉ H → a⁻¹ * b ∈ H) : H.relIndex K ≤ 2 := by
  classical
  have hwd : ∀ a b : ↥K, (QuotientGroup.leftRel (H.subgroupOf K)) a b →
      decide ((a : G) ∈ H) = decide ((b : G) ∈ H) := by
    intro a b hab
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at hab
    have hab' : (a : G)⁻¹ * b ∈ H := by simpa using hab
    by_cases ha : (a : G) ∈ H
    · have hb : (b : G) ∈ H := by
        have := H.mul_mem ha hab'
        simpa using this
      simp [ha, hb]
    · have hb : (b : G) ∉ H := fun hb => ha (by
        have := H.mul_mem hb (H.inv_mem hab')
        simpa using this)
      simp [ha, hb]
  let f : ↥K ⧸ H.subgroupOf K → Bool := Quotient.lift (fun a : ↥K => decide ((a : G) ∈ H)) hwd
  have hf : Function.Injective f := by
    intro q₁ q₂ hq
    induction q₁ using QuotientGroup.induction_on with | H a => ?_
    induction q₂ using QuotientGroup.induction_on with | H b => ?_
    have hq' : decide ((a : G) ∈ H) = decide ((b : G) ∈ H) := hq
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    by_cases ha : (a : G) ∈ H
    · have hb : (b : G) ∈ H := by simpa [ha] using hq'
      simpa using H.mul_mem (H.inv_mem ha) hb
    · have hb : (b : G) ∉ H := by simpa [ha] using hq'
      simpa using h a a.2 b b.2 ha hb
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
  exact this

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

structure PlusData (S : Setting4 G T L V) (Lp : Subgroup G) : Prop where
  eq : Lp = oTwoUpper Lp
  le_L1 : Lp ≤ S.L1
  T_le : T ≤ Subgroup.normalizer (Lp : Set G)
  three : ∀ τ ∈ C3, ∃ x : ↥(Subgroup.normalizer (V : Set G)), (x : G) ∈ Lp ∧ S.frame.ρ x = τ
  cent : Lp ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 L

@[expose] noncomputable def K4pre (S : Setting4 G T L V) (Lp : Subgroup G) : Subgroup G :=
  Lp ⊓ (K4sub.comap S.frame.ρ).map (Subgroup.normalizer (V : Set G)).subtype

theorem mem_K4pre {S : Setting4 G T L V} {Lp : Subgroup G} {x : G} :
    x ∈ K4pre S Lp ↔ x ∈ Lp ∧
      ∃ hx : x ∈ Subgroup.normalizer (V : Set G), S.frame.ρ ⟨x, hx⟩ ∈ K4L := by
  constructor
  · rintro ⟨hxL, y, hy, rfl⟩
    exact ⟨hxL, y.2, hy⟩
  · rintro ⟨hxL, hx, hK⟩
    exact ⟨hxL, ⟨x, hx⟩, hK, rfl⟩

@[expose] noncomputable def Ypre (S : Setting4 G T L V) (Lp : Subgroup G) : Subgroup G :=
  (Lp ⊔ T) ⊓ (E8sub.comap S.frame.ρ).map (Subgroup.normalizer (V : Set G)).subtype

theorem mem_Ypre {S : Setting4 G T L V} {Lp : Subgroup G} {x : G} :
    x ∈ Ypre S Lp ↔ x ∈ Lp ⊔ T ∧
      ∃ hx : x ∈ Subgroup.normalizer (V : Set G), S.frame.ρ ⟨x, hx⟩ ∈ E8 := by
  constructor
  · rintro ⟨hxL, y, hy, rfl⟩
    exact ⟨hxL, y.2, hy⟩
  · rintro ⟨hxL, hx, hK⟩
    exact ⟨hxL, ⟨x, hx⟩, hK, rfl⟩

@[expose] noncomputable def rhoLp (S : Setting4 G T L V) (Lp : Subgroup G)
    (h : Lp ≤ Subgroup.normalizer (V : Set G)) : ↥Lp →* Perm (Fin 6) :=
  S.frame.ρ.comp (Subgroup.inclusion h)

namespace PlusData

variable {S : Setting4 G T L V} {Lp : Subgroup G} (P : PlusData S Lp)
include P

theorem le_L : Lp ≤ L := P.le_L1.trans S.L1_le_L

theorem le_NV : Lp ≤ Subgroup.normalizer (V : Set G) := P.le_L.trans S.frame.L_le

theorem le_NV1 : Lp ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
  P.le_L1.trans (S.L1_le.trans inf_le_right)

theorem rho {x : ↥(Subgroup.normalizer (V : Set G))} (hx : (x : G) ∈ Lp) :
    S.frame.ρ x 4 = 4 ∧ S.frame.ρ x 5 = 5 ∧ Perm.sign (S.frame.ρ x) = 1 :=
  S.rho_L1 (P.le_L1 hx)

theorem le_NV3 : Lp ≤ Subgroup.normalizer (S.V3 : Set G) := fun x hx => by
  obtain ⟨h4, h5, -⟩ := P.rho (x := ⟨x, P.le_NV hx⟩) hx
  refine U3.L15A.mem_normalizer_pre S ⟨x, P.le_NV hx⟩ fun y hy => ?_
  show InW3 ((act4 (S.frame.ρ ⟨x, P.le_NV hx⟩) y : ↥W4) : P6)
  rw [act4_coe]
  exact fix45_W3 _ ⟨h4, h5⟩ _ y.2 hy

theorem isPGroup_K4pre : IsPGroup 2 (K4pre S Lp) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine isPGroup_two_of_forall fun y hy => ?_
  obtain ⟨hyL, hyN, hK⟩ := (mem_K4pre (S := S)).1 hy
  have hy2 : y ^ 2 ∈ Lp ⊓ Subgroup.centralizer (V : Set G) := by
    refine ⟨Lp.pow_mem hyL 2, (S.rho_eq_one_iff ⟨y ^ 2, Subgroup.pow_mem _ hyN 2⟩).1 ?_⟩
    have e : (⟨y ^ 2, Subgroup.pow_mem _ hyN 2⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        ⟨y, hyN⟩ ^ 2 := rfl
    rw [e, map_pow, pow_two]
    exact K4L_sq _ hK
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 L ⟨_, P.cent hy2⟩
  refine ⟨k + 1, ?_⟩
  have hk' : (y ^ 2) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  rw [pow_succ', pow_mul, hk']

theorem mem_pCoreOf_of_K4 {x : ↥(Subgroup.normalizer (V : Set G))} (hx : (x : G) ∈ Lp)
    (hK : S.frame.ρ x ∈ K4L) : (x : G) ∈ pCoreOf 2 Lp := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ P.isPGroup_K4pre
    ((mem_K4pre (S := S)).2 ⟨hx, x.2, hK⟩)
  refine A5.le_normalizer_of_forall_conj_mem fun l hl y hy => ?_
  obtain ⟨hyL, hyN, hyK⟩ := (mem_K4pre (S := S)).1 hy
  have hlN := P.le_NV hl
  have hN : l * y * l⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hlN hyN) (Subgroup.inv_mem _ hlN)
  refine (mem_K4pre (S := S)).2 ⟨Lp.mul_mem (Lp.mul_mem hl hyL) (Lp.inv_mem hl), hN, ?_⟩
  have e : (⟨l * y * l⁻¹, hN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
      ⟨l, hlN⟩ * ⟨y, hyN⟩ * ⟨l, hlN⟩⁻¹ := rfl
  obtain ⟨h4, h5, -⟩ := P.rho (x := ⟨l, hlN⟩) hl
  rw [e, map_mul, map_mul, map_inv]
  exact K4_norm _ ⟨h4, h5⟩ _ hyK

theorem pCoreOf_le_T : pCoreOf 2 Lp ≤ T :=
  (pCoreOf_le_pCoreOf_sup P.T_le).trans (pCoreOf_le_of_sylow S.h13.sylow le_sup_right)

theorem sup_inf_centralizer_le_T :
    (Lp ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ T := by
  rintro x ⟨hx, hxC⟩
  have hmul : ((Lp ⊔ T : Subgroup G) : Set G) = (Lp : Set G) * (T : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left Lp T P.T_le
  have hx' : x ∈ (Lp : Set G) * (T : Set G) := by
    rw [← hmul]
    exact hx
  obtain ⟨l, hl, t, ht, rfl⟩ := Set.mem_mul.mp hx'
  have hlN := P.le_NV hl
  have htN := S.frame.T_le ht
  have hρ : S.frame.ρ (⟨l, hlN⟩ * ⟨t, htN⟩) = 1 :=
    (S.rho_eq_one_iff (⟨l, hlN⟩ * ⟨t, htN⟩)).2 hxC
  rw [map_mul] at hρ
  have hρl : S.frame.ρ ⟨l, hlN⟩ = (S.frame.ρ ⟨t, htN⟩)⁻¹ := eq_inv_of_mul_eq_one_left hρ
  have hD : InD6 (S.frame.ρ ⟨l, hlN⟩) := by
    rw [hρl]
    exact (D6sub.inv_mem (mem_D6sub.2 (S.frame.T_D ⟨t, htN⟩ ht)) : _)
  obtain ⟨h4, h5, hs⟩ := P.rho (x := ⟨l, hlN⟩) hl
  have hlT := P.pCoreOf_le_T (P.mem_pCoreOf_of_K4 hl (D_A4 _ hD h4 h5 hs))
  exact T.mul_mem hlT ht

theorem gen : conjClosure S.V2 Lp = S.V3 := by
  apply le_antisymm
  · refine conjClosure_le fun l hl w hw => ?_
    exact (Subgroup.mem_normalizer_iff.mp (P.le_NV3 hl) w).mp (S.V2_le_V3 hw)
  · intro v hv
    obtain ⟨hvV, hv3⟩ := S.mem_pre.1 hv
    obtain ⟨τ, hτ, y, hy, hτy⟩ := gen_W3 _ (S.frame.ψ ⟨v, hvV⟩).2 hv3
    obtain ⟨x, hxL, hρx⟩ := P.three τ hτ
    obtain ⟨w, hw⟩ := S.frame.ψ.surjective ⟨y, U3.inW4_of_inW2 y hy⟩
    have hwV2 : (w : G) ∈ S.V2 := S.mem_pre.2 ⟨w.2, by
      have e : S.frame.ψ ⟨(w : G), w.2⟩ = ⟨y, U3.inW4_of_inW2 y hy⟩ := hw
      rw [e]
      exact hy⟩
    have hmem := mem_conjClosure hxL hwV2
    have heq : (x : G) * w * (x : G)⁻¹ = v := by
      have h1 := S.psi_conj x w
      have h2 : S.frame.ψ ⟨(x : G) * w * (x : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp x.2 w).mp w.2⟩ = S.frame.ψ ⟨v, hvV⟩ := by
        rw [h1, hρx, hw]
        exact Subtype.ext hτy
      exact congrArg Subtype.val (S.frame.ψ.injective h2)
    rw [← heq]
    exact hmem

theorem irred : IsIrredOnSection (Lp ⊔ T) S.V3 (fsuV1 T V) := by
  refine ⟨?_, sup_le P.le_NV3 S.T_le_normalizer_V3, sup_le P.le_NV1 S.T_le_NV1, ?_⟩
  · refine lt_of_le_of_ne (S.V1_le_V2.trans S.V2_le_V3) fun h => ?_
    have h1 := S.card_V1
    have h3 := S.card_V3
    rw [h] at h1
    omega
  · intro W h1W hW3 hWN
    by_cases hW : W ≤ fsuV1 T V
    · exact Or.inl (le_antisymm hW h1W)
    · right
      obtain ⟨w, hwW, hwV1⟩ := IsConcreteLE.not_le_iff_exists.1 hW
      refine le_antisymm hW3 fun x hx => ?_
      have hwV : w ∈ V := S.V3_le_V (hW3 hwW)
      obtain ⟨_, hw3⟩ := S.mem_pre.1 (hW3 hwW)
      have hinj : ∀ (u u' : ↥V), (S.frame.ψ u : P6) = (S.frame.ψ u' : P6) → (u : G) = u' :=
        fun u u' h => congrArg Subtype.val (S.frame.ψ.injective (Subtype.ext h))
      have hψz : (S.frame.ψ ⟨S.z, S.z_mem_V⟩ : P6) = e0123 := by rw [S.psi_z]
      have hne1 : (S.frame.ψ ⟨w, hwV⟩ : P6) ≠ 1 := fun h => hwV1 (by
        have : w = ((1 : ↥V) : G) := hinj ⟨w, hwV⟩ 1 (by rw [h, map_one]; rfl)
        rw [this]
        exact Subgroup.one_mem _)
      have hne2 : (S.frame.ψ ⟨w, hwV⟩ : P6) ≠ e0123 := fun h => hwV1 (by
        have : w = S.z := hinj ⟨w, hwV⟩ ⟨S.z, S.z_mem_V⟩ (by rw [h, hψz])
        rw [this]
        exact S.mem_V1_iff.2 (Or.inr rfl))
      obtain ⟨c, hcL, hρc⟩ := P.three (swap 0 1 * swap 1 2) (by decide)
      have hcw : (c : G) * w * (c : G)⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hWN ((le_sup_left : Lp ≤ Lp ⊔ T) hcL)) w).mp hwW
      have hcwV : (c : G) * w * (c : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp c.2 w).mp hwV
      have hzW : S.z ∈ W := h1W (S.mem_V1_iff.2 (Or.inr rfl))
      have hψd : (S.frame.ψ ⟨(c : G) * w * (c : G)⁻¹, hcwV⟩ : P6) =
          act4f (swap 0 1 * swap 1 2) (S.frame.ψ ⟨w, hwV⟩ : P6) := by
        rw [S.psi_conj c ⟨w, hwV⟩, hρc]
        rfl
      obtain ⟨hxV, hx3⟩ := S.mem_pre.1 hx
      have hspan := span3_W3 _ (S.frame.ψ ⟨w, hwV⟩).2 hw3 hne1 hne2 _ (S.frame.ψ ⟨x, hxV⟩).2 hx3
      simp only [span3, List.mem_cons, List.mem_nil_iff, or_false] at hspan
      let zV : ↥V := ⟨S.z, S.z_mem_V⟩
      let wV : ↥V := ⟨w, hwV⟩
      let dV : ↥V := ⟨(c : G) * w * (c : G)⁻¹, hcwV⟩
      have key : ∀ u : ↥V, (u : G) ∈ W → (S.frame.ψ ⟨x, hxV⟩ : P6) = (S.frame.ψ u : P6) →
          x ∈ W := fun u hu h => by
        have : x = (u : G) := hinj ⟨x, hxV⟩ u h
        rw [this]
        exact hu
      rcases hspan with h | h | h | h | h | h | h | h
      · exact key 1 W.one_mem (by rw [h, map_one]; rfl)
      · exact key zV hzW (by rw [h]; exact hψz.symm)
      · exact key wV hwW h
      · exact key (wV * zV) (W.mul_mem hwW hzW)
          (by rw [h, map_mul, Subgroup.coe_mul]; rw [show (S.frame.ψ zV : P6) = e0123 from hψz])
      · exact key dV hcw (by rw [h]; exact hψd.symm)
      · exact key (dV * zV) (W.mul_mem hcw hzW) (by
          rw [h, map_mul, Subgroup.coe_mul, show (S.frame.ψ dV : P6) = _ from hψd,
            show (S.frame.ψ zV : P6) = e0123 from hψz])
      · exact key (wV * dV) (W.mul_mem hwW hcw) (by
          rw [h, map_mul, Subgroup.coe_mul, show (S.frame.ψ dV : P6) = _ from hψd])
      · exact key (wV * dV * zV) (W.mul_mem (W.mul_mem hwW hcw) hzW) (by
          rw [h, map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul,
            show (S.frame.ψ dV : P6) = _ from hψd, show (S.frame.ψ zV : P6) = e0123 from hψz])

theorem comm3 : ⁅S.V3, pCoreOf 2 Lp⁆ = fsuV1 T V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj : ∀ (u u' : ↥V), (S.frame.ψ u : P6) = (S.frame.ψ u' : P6) → (u : G) = u' :=
    fun u u' h => congrArg Subtype.val (S.frame.ψ.injective (Subtype.ext h))
  have hψz : (S.frame.ψ ⟨S.z, S.z_mem_V⟩ : P6) = e0123 := by rw [S.psi_z]
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro v hv u hu
    have huL : u ∈ Lp := pCoreOf_le 2 Lp hu
    have huN := P.le_NV huL
    obtain ⟨h4, h5, hs⟩ := P.rho (x := ⟨u, huN⟩) huL
    have h2 : S.frame.ρ ⟨u, huN⟩ ^ 4 = 1 := by
      obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 Lp ⟨u, hu⟩
      refine pow_four_of_pow_two_pow (k := k) ?_
      rw [← map_pow]
      have : (⟨u, huN⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ 2 ^ k = 1 :=
        Subtype.ext (by simpa using congrArg Subtype.val hk)
      rw [this, map_one]
    have hK := mem_K4L _ h4 h5 hs h2
    obtain ⟨hvV, hv3⟩ := S.mem_pre.1 hv
    obtain ⟨hc, hψc⟩ := S.psi_commutator ⟨v, hvV⟩ ⟨u, huN⟩
    rw [commutatorElement_def]
    rcases comm_W3_K4 _ hK _ (S.frame.ψ ⟨v, hvV⟩).2 hv3 with h | h
    · have := hinj ⟨_, hc⟩ 1 (by rw [hψc, Subgroup.coe_mul, Subgroup.coe_inv, map_one]; exact h)
      rw [show v * u * v⁻¹ * u⁻¹ = ((1 : ↥V) : G) from this]
      exact Subgroup.one_mem _
    · have := hinj ⟨_, hc⟩ ⟨S.z, S.z_mem_V⟩
        (by rw [hψc, Subgroup.coe_mul, Subgroup.coe_inv, hψz]; exact h)
      rw [show v * u * v⁻¹ * u⁻¹ = S.z from this]
      exact S.mem_V1_iff.2 (Or.inr rfl)
  · intro x hx
    rcases S.mem_V1_iff.1 hx with rfl | rfl
    · exact Subgroup.one_mem _
    obtain ⟨hK, hcomm, h01, hprod⟩ := comm_e01
    obtain ⟨c₁, hc₁, hρ₁⟩ := P.three (swap 0 1 * swap 1 2) (by decide)
    obtain ⟨c₂, hc₂, hρ₂⟩ := P.three (swap 0 1 * swap 1 3) (by decide)
    have hu : ((c₁ * c₂ : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ pCoreOf 2 Lp :=
      P.mem_pCoreOf_of_K4 (Lp.mul_mem hc₁ hc₂) (by rw [map_mul, hρ₁, hρ₂, ← hprod]; exact hK)
    obtain ⟨v, hv⟩ := S.frame.ψ.surjective ⟨dv 0 1, dv_mem 0 1⟩
    have hv3 : (v : G) ∈ S.V3 := S.mem_pre.2 ⟨v.2, by
      have e : S.frame.ψ ⟨(v : G), v.2⟩ = ⟨dv 0 1, dv_mem 0 1⟩ := hv
      rw [e]
      exact h01⟩
    obtain ⟨hc, hψc⟩ := S.psi_commutator v (c₁ * c₂)
    have := hinj ⟨_, hc⟩ ⟨S.z, S.z_mem_V⟩ (by
      rw [hψc, Subgroup.coe_mul, Subgroup.coe_inv, hψz, map_mul, hρ₁, hρ₂, ← hprod, hv]
      exact hcomm)
    rw [← show (v : G) * ((c₁ * c₂ : ↥(Subgroup.normalizer (V : Set G))) : G) * (v : G)⁻¹ *
      ((c₁ * c₂ : ↥(Subgroup.normalizer (V : Set G))) : G)⁻¹ = S.z from this]
    exact Subgroup.commutator_mem_commutator hv3 hu

theorem Ypre_le_pCoreOf : Ypre S Lp ≤ pCoreOf 2 (Lp ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hconj : ∀ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ Lp ⊔ T →
      (∀ e ∈ E8, S.frame.ρ g * e * (S.frame.ρ g)⁻¹ ∈ E8) →
      ∀ y ∈ Ypre S Lp, (g : G) * y * (g : G)⁻¹ ∈ Ypre S Lp := by
    intro g hg hgE y hy
    obtain ⟨hyX, hyN, hyE⟩ := mem_Ypre.1 hy
    have hN : (g : G) * y * (g : G)⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ g.2 hyN) (Subgroup.inv_mem _ g.2)
    refine mem_Ypre.2 ⟨(Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hg) y).mp hyX,
      hN, ?_⟩
    have e : (⟨(g : G) * y * (g : G)⁻¹, hN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        g * ⟨y, hyN⟩ * g⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact hgE _ hyE
  refine le_pCoreOf_of_le_normalizer 2 inf_le_left (sup_le ?_ ?_) ?_
  · refine A5.le_normalizer_of_forall_conj_mem fun l hl y hy => ?_
    obtain ⟨h4, h5, -⟩ := P.rho (x := ⟨l, P.le_NV hl⟩) hl
    exact hconj ⟨l, P.le_NV hl⟩ ((le_sup_left : Lp ≤ Lp ⊔ T) hl)
      (e8_norm _ (Or.inr ⟨h4, h5⟩)) y hy
  · refine A5.le_normalizer_of_forall_conj_mem fun t ht y hy => ?_
    exact hconj ⟨t, S.frame.T_le ht⟩ ((le_sup_right : T ≤ Lp ⊔ T) ht)
      (e8_norm _ (Or.inl (S.frame.T_D ⟨t, S.frame.T_le ht⟩ ht))) y hy
  · refine isPGroup_two_of_forall fun y hy => ?_
    obtain ⟨hyX, hyN, hyE⟩ := mem_Ypre.1 hy
    have hy2 : y ^ 2 ∈ (Lp ⊔ T) ⊓ Subgroup.centralizer (V : Set G) := by
      refine ⟨(Lp ⊔ T).pow_mem hyX 2,
        (S.rho_eq_one_iff ⟨y ^ 2, Subgroup.pow_mem _ hyN 2⟩).1 ?_⟩
      have e : (⟨y ^ 2, Subgroup.pow_mem _ hyN 2⟩ : ↥(Subgroup.normalizer (V : Set G))) =
          ⟨y, hyN⟩ ^ 2 := rfl
      rw [e, map_pow, pow_two]
      exact e8_sq _ hyE
    obtain ⟨k, hk⟩ := S.h13.sylow.1 ⟨_, P.sup_inf_centralizer_le_T hy2⟩
    refine ⟨k + 1, ?_⟩
    have hk' : (y ^ 2) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [pow_succ', pow_mul, hk']

theorem index2 : (pCoreOf 2 (Lp ⊔ T)).relIndex T ≤ 2 := by
  have hle : T ⊓ Ypre S Lp ≤ pCoreOf 2 (Lp ⊔ T) := inf_le_right.trans P.Ypre_le_pCoreOf
  have h1 : (pCoreOf 2 (Lp ⊔ T)).relIndex T ≤ (T ⊓ Ypre S Lp).relIndex T :=
    Subgroup.relIndex_le_of_le_left hle Subgroup.index_ne_zero_of_finite
  refine h1.trans (relIndex_le_two_of fun a ha b hb haY hbY => ?_)
  have haN := S.frame.T_le ha
  have hbN := S.frame.T_le hb
  have haE : S.frame.ρ ⟨a, haN⟩ ∉ E8 := fun h =>
    haY ⟨ha, mem_Ypre.2 ⟨(le_sup_right : T ≤ Lp ⊔ T) ha, haN, h⟩⟩
  have hbE : S.frame.ρ ⟨b, hbN⟩ ∉ E8 := fun h =>
    hbY ⟨hb, mem_Ypre.2 ⟨(le_sup_right : T ≤ Lp ⊔ T) hb, hbN, h⟩⟩
  have hab := e8_index _ _ (S.frame.T_D ⟨a, haN⟩ ha) (S.frame.T_D ⟨b, hbN⟩ hb) haE hbE
  have hN : a⁻¹ * b ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ haN) hbN
  refine ⟨T.mul_mem (T.inv_mem ha) hb,
    mem_Ypre.2 ⟨(le_sup_right : T ≤ Lp ⊔ T) (T.mul_mem (T.inv_mem ha) hb), hN, ?_⟩⟩
  have e : (⟨a⁻¹ * b, hN⟩ : ↥(Subgroup.normalizer (V : Set G))) = ⟨a, haN⟩⁻¹ * ⟨b, hbN⟩ := rfl
  rw [e, map_mul, map_inv]
  exact hab

theorem index2_eq : (pCoreOf 2 (Lp ⊔ T)).relIndex T = 2 := by
  have h2 := P.index2
  have h0 : (pCoreOf 2 (Lp ⊔ T)).relIndex T ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : (pCoreOf 2 (Lp ⊔ T)).relIndex T ≠ 1 := by
    intro h
    rw [Subgroup.relIndex_eq_one] at h
    obtain ⟨hD, hs, hnD⟩ := t0_facts
    obtain ⟨t, htT, hρt⟩ := S.frame.DA_T _ hD (Perm.mem_alternatingGroup.2 hs)
    obtain ⟨l, hlL, hρl⟩ := P.three (swap 0 1 * swap 1 2) (by decide)
    have htO := h htT
    have hlt : (l : G) * t * (l : G)⁻¹ ∈ T :=
      pCoreOf_le_of_sylow S.h13.sylow le_sup_right
        ((Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _
          ((le_sup_left : Lp ≤ Lp ⊔ T) hlL)) t).mp htO)
    apply hnD
    have := S.frame.T_D (l * t * l⁻¹) hlt
    rw [map_mul, map_mul, map_inv, hρl, hρt] at this
    exact this
  omega

theorem range_rhoLp : (rhoLp S Lp P.le_NV).range = A4sub := by
  ext σ
  constructor
  · rintro ⟨x, rfl⟩
    exact P.rho (x := ⟨x, P.le_NV x.2⟩) x.2
  · rintro ⟨h4, h5, hs⟩
    obtain ⟨τ₁, hτ₁, τ₂, hτ₂, rfl⟩ := alt4_prod σ h4 h5 hs
    obtain ⟨x₁, hx₁, hρ₁⟩ := P.three τ₁ hτ₁
    obtain ⟨x₂, hx₂, hρ₂⟩ := P.three τ₂ hτ₂
    refine ⟨⟨_, Lp.mul_mem hx₁ hx₂⟩, ?_⟩
    have e : (Subgroup.inclusion P.le_NV ⟨_, Lp.mul_mem hx₁ hx₂⟩ :
        ↥(Subgroup.normalizer (V : Set G))) = x₁ * x₂ := rfl
    show S.frame.ρ (Subgroup.inclusion P.le_NV ⟨_, Lp.mul_mem hx₁ hx₂⟩) = τ₁ * τ₂
    rw [e, map_mul, hρ₁, hρ₂]

theorem pCoreOf_eq_K4pre : pCoreOf 2 Lp = K4pre S Lp := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · intro u hu
    have huL : u ∈ Lp := pCoreOf_le 2 Lp hu
    have huN := P.le_NV huL
    obtain ⟨h4, h5, hs⟩ := P.rho (x := ⟨u, huN⟩) huL
    have h2 : S.frame.ρ ⟨u, huN⟩ ^ 4 = 1 := by
      obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 Lp ⟨u, hu⟩
      refine pow_four_of_pow_two_pow (k := k) ?_
      rw [← map_pow]
      have : (⟨u, huN⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ 2 ^ k = 1 :=
        Subtype.ext (by simpa using congrArg Subtype.val hk)
      rw [this, map_one]
    exact mem_K4pre.2 ⟨huL, huN, mem_K4L _ h4 h5 hs h2⟩
  · intro u hu
    obtain ⟨huL, huN, hK⟩ := mem_K4pre.1 hu
    exact P.mem_pCoreOf_of_K4 (x := ⟨u, huN⟩) huL hK

theorem Lp3 : (pCoreOf 2 Lp).relIndex Lp = 3 := by
  have e : (pCoreOf 2 Lp).subgroupOf Lp = K4sub.comap (rhoLp S Lp P.le_NV) := by
    rw [P.pCoreOf_eq_K4pre]
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    constructor
    · intro h
      obtain ⟨-, _, hK⟩ := mem_K4pre.1 h
      exact hK
    · intro h
      exact mem_K4pre.2 ⟨x.2, P.le_NV x.2, h⟩
  show ((pCoreOf 2 Lp).subgroupOf Lp).index = 3
  rw [e, Subgroup.index_comap, P.range_rhoLp, relIndex_K4_A4]

end PlusData

theorem cv3 (S : Setting4 G T L V) : ∀ y ∈ Subgroup.normalizer (V : Set G) ⊓
    Subgroup.centralizer (S.V3 : Set G), Odd (orderOf y) →
      y ∈ Subgroup.centralizer (V : Set G) := by
  rintro y ⟨hyN, hyC⟩ hodd
  rcases fixW3_iff _ (S.fixW3_of_centralizer (x := ⟨y, hyN⟩) hyC) with h | h
  · exact (S.rho_eq_one_iff _).1 h
  · exfalso
    have h1 : S.frame.ρ (⟨y, hyN⟩ ^ orderOf y) = 1 := by
      have : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ orderOf y = 1 :=
        Subtype.ext (by simp [pow_orderOf_eq_one])
      rw [this, map_one]
    rw [map_pow, h] at h1
    obtain ⟨k, hk⟩ := hodd
    rw [hk, pow_succ, pow_mul, sq, swap_mul_self, one_pow, one_mul] at h1
    exact absurd h1 (by decide)

theorem mem_g1_of_fix (S : Setting4 G T L V) {y : ↥(Subgroup.normalizer (V : Set G))}
    (hy : act4f (S.frame.ρ y) e0123 = e0123) : (y : G) ∈ A6.g1 T V := by
  have hz : (y : G) * S.z * (y : G)⁻¹ = S.z := by
    rw [S.conj_eq_iff y ⟨S.z, S.z_mem_V⟩, S.psi_z]
    exact Subtype.ext hy
  show (y : G) ∈ Subgroup.normalizer (fsuV1 T V : Set G)
  rw [S.normalizer_V1, Subgroup.mem_centralizer_singleton_iff]
  calc (y : G) * S.z = (y : G) * S.z * (y : G)⁻¹ * y := by group
    _ = S.z * y := by rw [hz]

theorem genL (S : Setting4 G T L V) : L ≤ A6.g1 T V ⊔ L₁Of L S.V2 := by
  obtain ⟨g, hgL, hgV2, hg, -, -⟩ := U3.L15A.exists_lift_s3 S
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have hx2 : ((g ^ 4 ^ a : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ L₁Of L S.V2 := by
    refine Subgroup.subset_closure ⟨⟨?_, ?_⟩, m, hm, ?_⟩
    · simpa using L.pow_mem hgL (4 ^ a)
    · simpa using Subgroup.pow_mem _ hgV2 (4 ^ a)
    · have h1 : (g ^ (4 ^ a)) ^ m = (g ^ (2 ^ a * m)) ^ (2 ^ a) := by
        rw [← pow_mul, ← pow_mul]
        congr 1
        rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
        ring
      have h2 : g ^ (2 ^ a * m) = 1 := by rw [← hnm, pow_orderOf_eq_one]
      have h3 : (g ^ (4 ^ a)) ^ m = 1 := by rw [h1, h2, one_pow]
      simpa using congrArg Subtype.val h3
  have hρx : S.frame.ρ (g ^ 4 ^ a) = U3.a6s3 := by
    rw [map_pow, hg, pow_four_pow_of_cube U3.cert_a6_s3.2.1]
  have hletter : ∀ i < 4, ∃ y : ↥(Subgroup.normalizer (V : Set G)),
      (y : G) ∈ A6.g1 T V ⊔ L₁Of L S.V2 ∧ S.frame.ρ y = letter i := by
    intro i hi
    interval_cases i
    · exact ⟨g ^ 4 ^ a, Subgroup.mem_sup_right hx2, by rw [hρx]; rfl⟩
    · obtain ⟨h4, h5, hs⟩ := letter12_facts.1
      obtain ⟨l, -, hl⟩ := (S.frame.image_L (letter 1)).2 (Perm.mem_alternatingGroup.2 hs)
      exact ⟨l, Subgroup.mem_sup_left (mem_g1_of_fix S (by
        rw [hl]
        exact fix_e0123_of_pair _ (Or.inl ⟨h4, h5⟩))), hl⟩
    · obtain ⟨h4, h5, hs⟩ := letter12_facts.2
      obtain ⟨l, -, hl⟩ := (S.frame.image_L (letter 2)).2 (Perm.mem_alternatingGroup.2 hs)
      exact ⟨l, Subgroup.mem_sup_left (mem_g1_of_fix S (by
        rw [hl]
        exact fix_e0123_of_pair _ (Or.inl ⟨h4, h5⟩))), hl⟩
    · exact ⟨g ^ 4 ^ a * g ^ 4 ^ a, Subgroup.mem_sup_right (Subgroup.mul_mem _ hx2 hx2),
        by rw [map_mul, hρx]; rfl⟩
  have hword : ∀ w : List ℕ, (∀ i ∈ w, i < 4) → ∃ y : ↥(Subgroup.normalizer (V : Set G)),
      (y : G) ∈ A6.g1 T V ⊔ L₁Of L S.V2 ∧ S.frame.ρ y = evalWord w := by
    intro w hw
    induction w with
    | nil => exact ⟨1, Subgroup.one_mem _, by rw [map_one]; rfl⟩
    | cons i w ih =>
      obtain ⟨y₁, hy₁, hρ₁⟩ := hletter i (hw i List.mem_cons_self)
      obtain ⟨y₂, hy₂, hρ₂⟩ := ih fun j hj => hw j (List.mem_cons_of_mem _ hj)
      refine ⟨y₁ * y₂, Subgroup.mul_mem _ hy₁ hy₂, ?_⟩
      rw [map_mul, hρ₁, hρ₂]
      simp [evalWord]
  intro l hl
  have hlN := S.frame.L_le hl
  have hs : Perm.sign (S.frame.ρ ⟨l, hlN⟩) = 1 :=
    Perm.mem_alternatingGroup.1 ((S.frame.image_L _).1 ⟨⟨l, hlN⟩, hl, rfl⟩)
  obtain ⟨w, hw, hcase⟩ := cosets_A6 _ hs
  obtain ⟨y, hy, hρy⟩ := hword w (repWords_lt w hw)
  have hly : ((⟨l, hlN⟩ * y⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ A6.g1 T V := by
    refine mem_g1_of_fix S ?_
    rw [map_mul, map_inv, hρy]
    exact fix_e0123_of_pair _ hcase
  have e : l = ((⟨l, hlN⟩ * y⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G) * y := by simp
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hly) hy

theorem bcase_of (S : Setting4 G T L V) {x : G} (hxL : x ∈ L ⊓ Subgroup.normalizer (S.V2 : Set G))
    (hx3 : x ^ 3 = 1) (hxN : x ∈ Subgroup.normalizer (V : Set G))
    (hρx : S.frame.ρ ⟨x, hxN⟩ = U3.a6s3 ∨ S.frame.ρ ⟨x, hxN⟩ = U3.a6s3 * U3.a6s3) :
    ∃ g ∈ L ⊓ Subgroup.normalizer (S.V2 : Set G), g ^ 3 = 1 ∧
      g ∉ Subgroup.normalizer (fsuV1 T V : Set G) ∧
      Subgroup.centralizer ((S.V3 ⊔ S.V3.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ≤
        Subgroup.normalizer (L : Set G) := by
  refine ⟨x, hxL, hx3, fun h => ?_, ?_⟩
  · have hfix := S.fix_e0123 ⟨x, hxN⟩ (S.conj_z_of_normalizes h)
    rcases hρx with h1 | h1 <;> rw [h1] at hfix
    · exact s3_move hfix
    · exact s3_move2 hfix
  · have hVeq : S.V3 ⊔ S.V3.map (MulAut.conj x).toMonoidHom = V := by
      apply le_antisymm
      · refine sup_le S.V3_le_V ?_
        rintro _ ⟨v, hv, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hxN v).mp (S.V3_le_V hv)
      · intro v hv
        have hinj : ∀ (u u' : ↥V), (S.frame.ψ u : P6) = (S.frame.ψ u' : P6) → (u : G) = u' :=
          fun u u' h => congrArg Subtype.val (S.frame.ψ.injective (Subtype.ext h))
        have hsum : ∃ y₁ : P6, ∃ y₂ : P6, InW4 y₁ ∧ InW3 y₁ ∧ InW4 y₂ ∧ InW3 y₂ ∧
            (S.frame.ψ ⟨v, hv⟩ : P6) = y₁ * act4f (S.frame.ρ ⟨x, hxN⟩) y₂ := by
          rcases hρx with h1 | h1 <;> rw [h1]
          · exact s3_sum _ (S.frame.ψ ⟨v, hv⟩).2
          · exact s3_sum2 _ (S.frame.ψ ⟨v, hv⟩).2
        obtain ⟨y₁, y₂, h1W, h13, h2W, h23, hy⟩ := hsum
        obtain ⟨v₁, hv₁⟩ := S.frame.ψ.surjective ⟨y₁, h1W⟩
        obtain ⟨v₂, hv₂⟩ := S.frame.ψ.surjective ⟨y₂, h2W⟩
        have hv₁3 : (v₁ : G) ∈ S.V3 := S.mem_pre.2 ⟨v₁.2, by
          have e : S.frame.ψ ⟨(v₁ : G), v₁.2⟩ = ⟨y₁, h1W⟩ := hv₁
          rw [e]
          exact h13⟩
        have hv₂3 : (v₂ : G) ∈ S.V3 := S.mem_pre.2 ⟨v₂.2, by
          have e : S.frame.ψ ⟨(v₂ : G), v₂.2⟩ = ⟨y₂, h2W⟩ := hv₂
          rw [e]
          exact h23⟩
        have hxv₂ : x * v₂ * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hxN v₂).mp v₂.2
        have : v = (v₁ : G) * (x * v₂ * x⁻¹) := by
          have := hinj ⟨v, hv⟩ (v₁ * ⟨x * v₂ * x⁻¹, hxv₂⟩) (by
            rw [map_mul, Subgroup.coe_mul, S.psi_conj ⟨x, hxN⟩ v₂, hv₁, hv₂, hy]
            rfl)
          exact this
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hv₁3)
          (Subgroup.mem_sup_right ⟨v₂, hv₂3, rfl⟩)
    rw [hVeq]
    exact (Subgroup.centralizer_le_normalizer (V : Set G)).trans S.NV_le_M

theorem hyp1223 (S : Setting4 G T L V) : Hyp1223 G T L V where
  simple := S.h13.simple
  nonabelian := S.h13.nonabelian
  qtke := S.h13.qtke
  sylow := S.h13.sylow
  notAlt := S.not_alt12_2_2
  maximal := S.maximal
  faithful := S.h13.faithful
  quasisimple := S.fsu.quasisimple
  normalizes := S.T_le_NL
  irrPlus := S.irr

theorem plusData_L1 (S : Setting4 G T L V) (hhat : ¬ IsHatA6 L) :
    PlusData S S.L1 where
  eq := by
    rw [← oTwoRes_eq_oTwoUpper]
    exact (oTwoRes_idem _).symm
  le_L1 := le_rfl
  T_le := S.T_le_normalizer_L1
  three := fun τ hτ => by
    obtain ⟨h4, h5, hs, h3⟩ := c3_facts τ hτ
    exact S.exists_L1_of_three hs h4 h5 h3
  cent := fun x hx => S.inf_centralizer_le_pCoreOf hhat ⟨S.L1_le_L hx.1, hx.2⟩

theorem exists_TL_rho (S : Setting4 G T L V) {σ : Perm (Fin 6)} (hσD : InD6 σ)
    (hσA : Perm.sign σ = 1) :
    ∃ t : ↥(Subgroup.normalizer (V : Set G)), (t : G) ∈ T ⊓ L ∧ S.frame.ρ t = σ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let θ : ↥L →* ↥(alternatingGroup (Fin 6)) :=
    (S.frame.ρ.comp (Subgroup.inclusion S.frame.L_le)).codRestrict _ fun l =>
      U3.L15A.rho_mem_alt S (g := ⟨l, S.frame.L_le l.2⟩) l.2
  have hθ : Function.Surjective θ := by
    rintro ⟨τ, hτ⟩
    obtain ⟨g, hgL, hg⟩ := (S.frame.image_L τ).2 hτ
    exact ⟨⟨g, hgL⟩, Subtype.ext hg⟩
  have hTLs : IsSylowTwoOf (T ⊓ L) L := A4.isSylowTwoOf_inf_normal
    (A5.isSylowTwoOf_of_le S.h13.sylow le_sup_right) le_sup_left
    (sup_le Subgroup.le_normalizer S.T_le_NL)
  have hP1 : IsPGroup 2 ((T ⊓ L).subgroupOf L) :=
    hTLs.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTLs.1).symm
  let P : Sylow 2 ↥L := hP1.toSylow hTLs.2.2
  let Q : Sylow 2 ↥(alternatingGroup (Fin 6)) := P.mapSurjective hθ
  have hQcard : Nat.card (Q : Subgroup ↥(alternatingGroup (Fin 6))) = 8 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 Q.isPGroup'
    have h1 := Subgroup.card_mul_index (Q : Subgroup ↥(alternatingGroup (Fin 6)))
    rw [hk, nat_card_alt_six] at h1
    have h2 := Q.not_dvd_index
    have hk9 : k < 9 := by
      by_contra h
      have h3 : 2 ^ 9 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (not_lt.1 h)
      have h4 : 2 ^ k ≤ 360 := Nat.le_of_dvd (by norm_num) ⟨_, h1.symm⟩
      norm_num at h3
      omega
    rw [hk]
    interval_cases k <;> omega
  set Q' := (Q : Subgroup ↥(alternatingGroup (Fin 6))).map (alternatingGroup (Fin 6)).subtype
  have hQ'card : Nat.card Q' = 8 := by
    rw [Subgroup.card_map_of_injective (alternatingGroup (Fin 6)).subtype_injective, hQcard]
  have hQ'le : Q' ≤ D6sub ⊓ alternatingGroup (Fin 6) := by
    rintro _ ⟨q, hq, rfl⟩
    rw [Sylow.coe_mapSurjective] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    have hpT : (p : G) ∈ T :=
      (Subgroup.mem_subgroupOf.1 (show p ∈ (T ⊓ L).subgroupOf L from hp)).1
    exact ⟨mem_D6sub.2 (S.frame.T_D _ hpT), (θ p).2⟩
  have hDA : Nat.card ↥(D6sub ⊓ alternatingGroup (Fin 6)) = 8 := by
    rw [Nat.card_eq_fintype_card, ← card_DA, Fintype.card_subtype]
    congr 1
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Subgroup.mem_inf, mem_D6sub,
      Perm.mem_alternatingGroup]
  have hQeq : Q' = D6sub ⊓ alternatingGroup (Fin 6) :=
    Subgroup.eq_of_le_of_card_ge hQ'le (by rw [hDA, hQ'card])
  have hσ : σ ∈ Q' := by
    rw [hQeq]
    exact ⟨mem_D6sub.2 hσD, Perm.mem_alternatingGroup.2 hσA⟩
  obtain ⟨q, hq, hqe⟩ := hσ
  rw [Sylow.coe_mapSurjective] at hq
  obtain ⟨p, hp, rfl⟩ := hq
  have hp' := Subgroup.mem_subgroupOf.1 (show p ∈ (T ⊓ L).subgroupOf L from hp)
  exact ⟨⟨p, S.frame.L_le p.2⟩, hp', hqe⟩

theorem exists_oTwoRes_rho (S : Setting4 G T L V) {X : Subgroup G}
    {c : ↥(Subgroup.normalizer (V : Set G))} (hc : (c : G) ∈ X) {σ : Perm (Fin 6)}
    (hρ : S.frame.ρ c = σ) (h3 : σ ^ 3 = 1) :
    ∃ y : ↥(Subgroup.normalizer (V : Set G)), (y : G) ∈ oTwoRes X ∧ S.frame.ρ y = σ := by
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  refine ⟨c ^ 4 ^ a, Subgroup.subset_closure ⟨by simpa using X.pow_mem hc (4 ^ a), m, hm, ?_⟩,
    by rw [map_pow, hρ, pow_four_pow_of_cube h3]⟩
  have h1 : (c ^ (4 ^ a)) ^ m = (c ^ (2 ^ a * m)) ^ (2 ^ a) := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
    ring
  have h2 : c ^ (2 ^ a * m) = 1 := by rw [← hnm, pow_orderOf_eq_one]
  have h3' : (c ^ (4 ^ a)) ^ m = 1 := by rw [h1, h2, one_pow]
  simpa using congrArg Subtype.val h3'

theorem commutator_L1_TL_le (S : Setting4 G T L V) : ⁅S.L1, T ⊓ L⁆ ≤ S.L1 := by
  rw [Subgroup.commutator_le]
  intro h hh k hk
  have e : ⁅h, k⁆ = h * (k * h⁻¹ * k⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact S.L1.mul_mem hh ((Subgroup.mem_normalizer_iff.mp (S.T_le_normalizer_L1 hk.1) h⁻¹).mp
    (S.L1.inv_mem hh))

theorem plusData_l1plus (S : Setting4 G T L V)
    (hP1 : l1plus T L V ⊓ o2Z L ≤ pCoreOf 2 L) : PlusData S (l1plus T L V) := by
  have hle : l1plus T L V ≤ S.L1 := (oTwoRes_le _).trans (commutator_L1_TL_le S)
  refine ⟨?_, hle, ?_, ?_, ?_⟩
  · rw [← oTwoRes_eq_oTwoUpper]
    unfold l1plus
    rw [oTwoRes_idem]
  · exact A5.le_normalizer_oTwoRes_of_le_normalizer (A5.le_normalizer_commutator
      S.T_le_normalizer_L1 (F7.le_normalizer_inf Subgroup.le_normalizer S.T_le_NL))
  · obtain ⟨hD, hs, -⟩ := t0_facts
    obtain ⟨t, htTL, hρt⟩ := exists_TL_rho S hD hs
    obtain ⟨ha, hb, hab⟩ := ab_facts
    have hlift : ∀ τ₀ : Perm (Fin 6), τ₀ ∈ C3 → ∀ σ : Perm (Fin 6), σ ^ 3 = 1 →
        τ₀ * (swap 0 1 * swap 4 5) * τ₀⁻¹ * (swap 0 1 * swap 4 5)⁻¹ = σ →
        ∃ y : ↥(Subgroup.normalizer (V : Set G)), (y : G) ∈ l1plus T L V ∧ S.frame.ρ y = σ := by
      intro τ₀ hτ₀ σ hσ3 hσ
      obtain ⟨h4, h5, hs0, h3⟩ := c3_facts τ₀ hτ₀
      obtain ⟨x, hxL, hρx⟩ := S.exists_L1_of_three hs0 h4 h5 h3
      have hc : ((x * t * x⁻¹ * t⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G) ∈
          ⁅S.L1, T ⊓ L⁆ := by
        have := Subgroup.commutator_mem_commutator hxL htTL
        rw [commutatorElement_def] at this
        exact this
      exact exists_oTwoRes_rho S hc
        (by rw [map_mul, map_mul, map_mul, map_inv, map_inv, hρx, hρt]; exact hσ) hσ3
    obtain ⟨ya, hya, hρa⟩ :=
      hlift (swap 0 1 * swap 1 2) (by decide) _ (c3_facts _ (by decide)).2.2.2 ha
    obtain ⟨yb, hyb, hρb⟩ :=
      hlift (swap 0 1 * swap 1 3) (by decide) _ (c3_facts _ (by decide)).2.2.2 hb
    intro τ hτ
    obtain ⟨x₁, hx₁, x₂, hx₂, m, n, hτe⟩ := hab τ hτ
    have hpick : ∀ x ∈ [(1 : Perm (Fin 6)), swap 0 2 * swap 2 1, swap 0 3 * swap 3 1],
        ∃ y : ↥(Subgroup.normalizer (V : Set G)), (y : G) ∈ l1plus T L V ∧ S.frame.ρ y = x := by
      intro x hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨1, Subgroup.one_mem _, map_one _⟩
      · exact ⟨ya, hya, hρa⟩
      · exact ⟨yb, hyb, hρb⟩
    obtain ⟨y₁, hy₁, hρ₁⟩ := hpick x₁ hx₁
    obtain ⟨y₂, hy₂, hρ₂⟩ := hpick x₂ hx₂
    refine ⟨y₁ ^ (m : ℕ) * y₂ ^ (n : ℕ), ?_, by rw [map_mul, map_pow, map_pow, hρ₁, hρ₂, hτe]⟩
    simpa using (l1plus T L V).mul_mem ((l1plus T L V).pow_mem hy₁ (m : ℕ))
      ((l1plus T L V).pow_mem hy₂ (n : ℕ))
  · intro x hx
    exact hP1 ⟨hx.1, S.centralizer_le_o2Z ⟨S.L1_le_L (hle hx.1), hx.2⟩⟩

theorem set14_of (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (S : Setting4 G T L V) (hV2 : IsV2 T V S.V2) {Lp : Subgroup G} (P : PlusData S Lp)
    (hb : ∃ g ∈ L ⊓ Subgroup.normalizer (S.V2 : Set G), g ^ 3 = 1 ∧
      g ∉ Subgroup.normalizer (fsuV1 T V : Set G) ∧
      Subgroup.centralizer ((S.V3 ⊔ S.V3.map (MulAut.conj g).toMonoidHom : Subgroup G) :
        Set G) ≤ Subgroup.normalizer (L : Set G))
    (hdef : (IsHatA6 L → Lp = l1plus T L V) ∧ (¬ IsHatA6 L → Lp = L₁Of L (fsuV1 T V))) :
    U3.Set14 G T L V S.V2 S.V3 Lp where
  h13 := S.h13
  irr := S.irr
  zv := S.zv
  v2 := hV2
  card1 := S.card_V1
  le23 := S.V2_le_V3
  le3V := S.V3_le_V
  T_V3 := S.T_le_normalizer_V3
  card3 := S.card_V3
  Lp_eq := P.eq
  Lp_L := P.le_L
  Lp_V1 := P.le_NV1
  T_Lp := P.T_le
  gen := P.gen
  irred := P.irred
  comm3 := P.comm3
  index2 := P.index2_eq
  Lp_def := hdef
  Lp3 := P.Lp3
  cv3 := cv3 S
  clv := S.centralizer_le_o2Z
  bcase := Or.inr hb
  genL := genL S
  fsu := S.fsu
  T_L := S.T_le_NL
  V_T := S.V_le_T
  T_V := S.frame.T_le
  Mmax := S.uniqueM.1.1
  uniq := fun M hM hLT => S.uniqueM.2 M ⟨hM, hLT⟩
  ti := (stmt12_2_6_of h1222 h323 G T L V (hyp1223 S)).2

end S14

theorem set14ProducerA6_of (h1332 : Stmt13_3_2)
    (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3) : U3.Set14ProducerA6 := by
  intro G _ _ T L V V₂ _ hH hV hZV hV2 hnat
  obtain ⟨S⟩ := U3.setting4_of_case_b h1332 hH hV hZV hnat
  have hV2e : V₂ = S.V2 := S.V2_unique hV2
  subst hV2e
  by_cases hhat : IsHatA6 L
  · have hP1 := S.hatL1Plus hhat
    have hP2 := S.hatL2Plus hhat
    obtain ⟨x, hx, hx3, -, hxN, hρx⟩ := U3.L15A.exists_X_hat S hP2
    have hxL2 : x ∈ L ⊓ Subgroup.normalizer (S.V2 : Set G) := by
      have hT2 : T ⊓ L ≤ Subgroup.normalizer (L₁Of L S.V2 : Set G) :=
        inf_le_left.trans (A5.le_normalizer_oTwoRes_of_le_normalizer
          (F7.le_normalizer_inf S.T_le_NL (S.T_le_normalizer_V2.trans Subgroup.le_normalizer)))
      have hc : ⁅L₁Of L S.V2, T ⊓ L⁆ ≤ L₁Of L S.V2 := by
        rw [Subgroup.commutator_le]
        intro h hh k hk
        have e : ⁅h, k⁆ = h * (k * h⁻¹ * k⁻¹) := by
          rw [commutatorElement_def]
          group
        rw [e]
        exact (L₁Of L S.V2).mul_mem hh
          ((Subgroup.mem_normalizer_iff.mp (hT2 hk) h⁻¹).mp ((L₁Of L S.V2).inv_mem hh))
      exact oTwoRes_le _ (hc (oTwoRes_le _ hx))
    exact ⟨S.V3, l1plus T L V, S14.set14_of h1222 h323 S hV2 (S14.plusData_l1plus S hP1)
      (S14.bcase_of S hxL2 hx3 hxN hρx) ⟨fun _ => rfl, fun h => absurd hhat h⟩⟩
  · obtain ⟨x, hx, hx3, -, hxN, hρx⟩ := U3.L15A.exists_X_nonhat S hhat
    exact ⟨S.V3, S.L1, S14.set14_of h1222 h323 S hV2 (S14.plusData_L1 S hhat)
      (S14.bcase_of S (oTwoRes_le _ hx) hx3 hxN hρx) ⟨fun h => absurd h hhat, fun _ => rfl⟩⟩

end CFSG.Quasithin.H13.A6
