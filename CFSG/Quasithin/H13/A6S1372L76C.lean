module

public import CFSG.Quasithin.H13.A6S1372L76D
public import CFSG.Quasithin.H13.A6S1372KeyData
public import CFSG.Quasithin.H13.A6S1372L76

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace A6L76C

theorem mem_zpowers_allOnes_iff {n : ℕ} (x : G6.PermMod n) :
    x ∈ Subgroup.zpowers (G6.allOnes n) ↔ x = 1 ∨ x = G6.allOnes n := by
  have h2 : G6.allOnes n * G6.allOnes n = 1 := G6.permMod_mul_self _
  have hinv : (G6.allOnes n)⁻¹ = G6.allOnes n := inv_eq_of_mul_eq_one_right h2
  have key : ∀ k : ℤ, G6.allOnes n ^ k = 1 ∨ G6.allOnes n ^ k = G6.allOnes n := by
    intro k
    induction k using Int.induction_on with
    | zero => exact Or.inl (zpow_zero _)
    | succ i ih =>
      rw [zpow_add_one]
      rcases ih with h | h <;> rw [h]
      · exact Or.inr (one_mul _)
      · exact Or.inl h2
    | pred i ih =>
      rw [zpow_sub_one]
      rcases ih with h | h <;> rw [h]
      · right
        rw [one_mul]
        exact hinv
      · exact Or.inl (mul_inv_cancel _)
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    exact key k
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

@[expose] def permOf {n : ℕ} (σ : (FFModel.altDn n).Gam) : Perm (Fin n) :=
  @Subtype.val (Perm (Fin n)) (fun x => x ∈ alternatingGroup (Fin n)) σ

theorem permOf_mul {n : ℕ} (σ τ : (FFModel.altDn n).Gam) : permOf (σ * τ) = permOf σ * permOf τ :=
  rfl

theorem permOf_sign {n : ℕ} (σ : (FFModel.altDn n).Gam) : Perm.sign (permOf σ) = 1 :=
  Perm.mem_alternatingGroup.1 σ.2

theorem permOf_injective {n : ℕ} : Function.Injective (permOf (n := n)) :=
  fun _ _ h => Subtype.ext h

theorem act_eq {n : ℕ} (σ : (FFModel.altDn n).Gam) (x : (FFModel.altDn n).Amb) :
    (FFModel.altDn n).act σ x = G6.permAct n (permOf σ) x := rfl

@[expose] def FixCls (n : ℕ) (σ : Perm (Fin n)) (m : G6.PermMod n) : Prop :=
  G6.permAct n σ m * m⁻¹ = 1 ∨ G6.permAct n σ m * m⁻¹ = G6.allOnes n

instance (n : ℕ) (σ : Perm (Fin n)) (m : G6.PermMod n) : Decidable (FixCls n σ m) := by
  unfold FixCls; infer_instance

theorem act_mul_inv_mem_ker_iff {n : ℕ} {m : (FFModel.altDn n).Amb}
    (hm : m ∈ (FFModel.altDn n).sec) (σ : (FFModel.altDn n).Gam) :
    (FFModel.altDn n).act σ m * m⁻¹ ∈ (FFModel.altDn n).ker ↔ FixCls n (permOf σ) m := by
  have hm' : (show G6.PermMod n from m) ∈ G6.coreMod n := hm
  show G6.permAct n (permOf σ) m * (show G6.PermMod n from m)⁻¹ ∈
    Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n ↔ _
  rw [Subgroup.mem_inf, mem_zpowers_allOnes_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, (G6.coreMod n).mul_mem (G6.permAct_mem_coreMod _ hm')
    ((G6.coreMod n).inv_mem hm')⟩⟩

@[expose] noncomputable def conjAlt {n : ℕ} (τ : Perm (Fin n)) :
    (FFModel.altDn n).Gam →* (FFModel.altDn n).Gam :=
  (MulAut.conjNormal (H := alternatingGroup (Fin n)) τ).toMonoidHom

theorem conjAlt_coe {n : ℕ} (τ : Perm (Fin n)) (σ : (FFModel.altDn n).Gam) :
    permOf (conjAlt τ σ) = τ * permOf σ * τ⁻¹ :=
  MulAut.conjNormal_apply τ σ

theorem conjAlt_conjAlt_inv {n : ℕ} (τ : Perm (Fin n)) (σ : (FFModel.altDn n).Gam) :
    conjAlt τ⁻¹ (conjAlt τ σ) = σ := by
  apply permOf_injective
  rw [conjAlt_coe, conjAlt_coe]
  group

@[expose] noncomputable def coreHom {n : ℕ} (τ : Perm (Fin n)) :
    ↥(FFModel.altDn n).sec →* ↥(FFModel.altDn n).sec :=
  (G6.coreAct n τ).toMonoidHom

theorem coreHom_coe {n : ℕ} (τ : Perm (Fin n)) (m : ↥(FFModel.altDn n).sec) :
    ((coreHom τ m : ↥(FFModel.altDn n).sec) : (FFModel.altDn n).Amb) =
      (G6.permAct n τ (show G6.PermMod n from m.1) : G6.PermMod n) := rfl

theorem coreHom_ker_le {n : ℕ} (τ : Perm (Fin n)) :
    (FFModel.altDn n).ker.subgroupOf (FFModel.altDn n).sec ≤
      ((FFModel.altDn n).ker.subgroupOf (FFModel.altDn n).sec).comap (coreHom τ) := by
  intro m hm
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  rw [Subgroup.mem_subgroupOf] at hm
  have hm' : (show G6.PermMod n from m.1) ∈ Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n := hm
  show G6.permAct n τ (show G6.PermMod n from m.1) ∈
    Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n
  refine ⟨?_, G6.permAct_mem_coreMod τ hm'.2⟩
  rcases (mem_zpowers_allOnes_iff _).1 hm'.1 with h | h <;> rw [h]
  · rw [map_one]
    exact Subgroup.one_mem _
  · rw [CFSG.Quasithin.permAct_allOnes n τ]
    exact Subgroup.mem_zpowers _

@[expose] noncomputable def twistQ {n : ℕ} (τ : Perm (Fin n)) :
    (FFModel.altDn n).Mod →* (FFModel.altDn n).Mod :=
  QuotientGroup.map _ _ (coreHom τ) (coreHom_ker_le τ)

theorem twistQ_mk {n : ℕ} (τ : Perm (Fin n)) (m : ↥(FFModel.altDn n).sec) :
    twistQ τ (QuotientGroup.mk m) = QuotientGroup.mk (coreHom τ m) := rfl

theorem twistQ_mul {n : ℕ} (τ τ' : Perm (Fin n)) (x : (FFModel.altDn n).Mod) :
    twistQ τ (twistQ τ' x) = twistQ (τ * τ') x := by
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
  rfl

theorem twistQ_one {n : ℕ} (x : (FFModel.altDn n).Mod) : twistQ 1 x = x := by
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
  rfl

theorem realizesBy_twist {V : Type*} [CommGroup V] {n : ℕ} {Y : Subgroup (MulAut V)}
    {U Z : Subgroup V} {π : (FFModel.altDn n).Gam →* ↥Y}
    {β : ↥U →* ↥(FFModel.altDn n).sec ⧸ (FFModel.altDn n).ker.subgroupOf (FFModel.altDn n).sec}
    (hR : CFSG.Quasithin.H.Mathieu.RealizesBy (FFModel.altDn n) Y U Z π β) (τ : Perm (Fin n)) :
    CFSG.Quasithin.H.Mathieu.RealizesBy (FFModel.altDn n) Y U Z (π.comp (conjAlt τ⁻¹))
      ((twistQ τ).comp β) := by
  obtain ⟨hπs, hZU, hks, hYU, hYZ, hsec, hker, hβs, hβk, hβe⟩ := hR
  have hinv : ∀ x, twistQ τ⁻¹ (twistQ τ x) = x := fun x => by
    rw [twistQ_mul, inv_mul_cancel, twistQ_one]
  have hinv' : ∀ x, twistQ τ (twistQ τ⁻¹ x) = x := fun x => by
    rw [twistQ_mul, mul_inv_cancel, twistQ_one]
  refine ⟨?_, hZU, hks, hYU, hYZ, hsec, hker, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨σ, rfl⟩ := hπs y
    exact ⟨conjAlt τ σ, by rw [MonoidHom.comp_apply, conjAlt_conjAlt_inv]⟩
  · intro x
    obtain ⟨u, hu⟩ := hβs (twistQ τ⁻¹ x)
    exact ⟨u, by rw [MonoidHom.comp_apply, hu, hinv']⟩
  · intro u
    rw [MonoidHom.comp_apply, ← hβk u]
    constructor
    · intro h
      rw [← hinv (β u), h, map_one]
    · intro h
      rw [h, map_one]
  · intro γ u m hu hm hum
    have hm0 : G6.permAct n τ⁻¹ (show G6.PermMod n from m.1) ∈ (FFModel.altDn n).sec :=
      G6.permAct_mem_coreMod _ m.2
    have hβu : β u = QuotientGroup.mk ⟨_, hm0⟩ := by
      rw [← hinv (β u)]
      rw [MonoidHom.comp_apply] at hum
      rw [hum, twistQ_mk]
      rfl
    have hact : (FFModel.altDn n).act (conjAlt τ⁻¹ γ)
        (G6.permAct n τ⁻¹ (show G6.PermMod n from m.1)) ∈ (FFModel.altDn n).sec :=
      hsec _ _ hm0
    have h1 := hβe (conjAlt τ⁻¹ γ) u ⟨_, hm0⟩ hu hact hβu
    show twistQ τ (β ⟨((π (conjAlt τ⁻¹ γ) : ↥Y) : MulAut V) (u : V), hu⟩) = _
    rw [h1, twistQ_mk]
    congr 1
    apply Subtype.ext
    rw [coreHom_coe]
    show G6.permAct n τ (G6.permAct n (permOf (conjAlt τ⁻¹ γ)) (G6.permAct n τ⁻¹ m.1)) =
      G6.permAct n (permOf γ) m.1
    have key : ∀ x : G6.PermMod n, G6.permAct n τ (G6.permAct n (τ⁻¹ * permOf γ * τ⁻¹⁻¹)
        (G6.permAct n τ⁻¹ x)) = G6.permAct n (permOf γ) x := by
      intro x
      rw [← CFSG.Quasithin.permAct_mul_act, ← CFSG.Quasithin.permAct_mul_act]
      congr 2
      group
    rw [conjAlt_coe]
    exact key _

@[expose] noncomputable def act6 : ↥(alternatingGroup (Fin 6)) →* MulAut ↥W4 :=
  act4.comp (alternatingGroup (Fin 6)).subtype

theorem endTriv_W4 : A6L76D.EndTriv act6 := fun f hf =>
  A6Fin.end_W4 f fun σ hσ w => hf ⟨σ, hσ⟩ w

instance : Nontrivial ↥W4 :=
  ⟨⟨A6Fin.dvW 1, 1, fun h => (dv_zero_facts.1 1 (by decide)) (congrArg Subtype.val h)⟩⟩

theorem card_mulAut_alt6 :
    Nat.card (MulAut ↥(alternatingGroup (Fin 6))) =
      Nat.card ↥(alternatingGroup (Fin 6)) * 2 ^ 2 := by
  rw [A6Key.card_mulAut_alt6, CFSG.QuasithinUnique.DoubleA3.card_alt6']
  norm_num

@[expose] noncomputable def act7 : ↥(alternatingGroup (Fin 7)) →* MulAut ↥(G6.coreMod 7) :=
  (G6.coreAct 7).comp (alternatingGroup (Fin 7)).subtype

@[expose] def e7 (j : Fin 6) : ↥(G6.coreMod 7) :=
  ⟨A6L76.vecS 7 {0, j.succ}, G6.mem_coreMod.2 (by revert j; decide)⟩

@[expose] def g7a : Perm (Fin 7) := swap 2 3 * swap 3 4 * swap 4 5 * swap 5 6

@[expose] def g7b : Perm (Fin 7) := swap 0 1 * swap 2 3

theorem stab_fix7 : ∀ y : G6.PermMod 7, ∑ i, Multiplicative.toAdd y i = 0 →
    G6.permAct 7 g7a y = y → G6.permAct 7 g7b y = y → y = 1 ∨ y = A6L76.vecS 7 {0, 1} := by
  decide +kernel

theorem g7_facts : Perm.sign g7a = 1 ∧ Perm.sign g7b = 1 ∧
    G6.permAct 7 g7a (A6L76.vecS 7 {0, 1}) = A6L76.vecS 7 {0, 1} ∧
    G6.permAct 7 g7b (A6L76.vecS 7 {0, 1}) = A6L76.vecS 7 {0, 1} := by
  decide +kernel

@[expose] def piK7 (k : Fin 7) : Perm (Fin 7) :=
  if k = 1 then 1 else if k = 5 ∨ k = 6 then swap 1 k * swap 2 3 else swap 1 k * swap 5 6

theorem piK7_facts : ∀ k : Fin 7, k ≠ 0 → Perm.sign (piK7 k) = 1 ∧
    G6.permAct 7 (piK7 k) (A6L76.vecS 7 {0, 1}) = A6L76.vecS 7 {0, k} := by
  decide +kernel

theorem eq_prod_e7 : ∀ y : G6.PermMod 7, ∑ i, Multiplicative.toAdd y i = 0 →
    y = A6L76.vecS 7 {0, 1} ^ (Multiplicative.toAdd y 1).val *
      A6L76.vecS 7 {0, 2} ^ (Multiplicative.toAdd y 2).val *
      A6L76.vecS 7 {0, 3} ^ (Multiplicative.toAdd y 3).val *
      A6L76.vecS 7 {0, 4} ^ (Multiplicative.toAdd y 4).val *
      A6L76.vecS 7 {0, 5} ^ (Multiplicative.toAdd y 5).val *
      A6L76.vecS 7 {0, 6} ^ (Multiplicative.toAdd y 6).val := by
  decide +kernel

theorem vecS_ne_one : A6L76.vecS 7 {0, 1} ≠ 1 := by decide

theorem endTriv_core7 : A6L76D.EndTriv act7 := by
  intro f hf
  have hfix : ∀ g : Perm (Fin 7), Perm.sign g = 1 →
      G6.permAct 7 g (A6L76.vecS 7 {0, 1}) = A6L76.vecS 7 {0, 1} →
      G6.permAct 7 g (f (e7 0) : G6.PermMod 7) = f (e7 0) := by
    intro g hg hgx
    have h1 := hf ⟨g, Perm.mem_alternatingGroup.2 hg⟩ (e7 0)
    have h2 : act7 ⟨g, Perm.mem_alternatingGroup.2 hg⟩ (e7 0) = e7 0 := by
      apply Subtype.ext
      exact hgx
    rw [h2] at h1
    exact (congrArg Subtype.val h1).symm
  obtain ⟨ha, hb, hax, hbx⟩ := g7_facts
  have h1 := stab_fix7 _ (G6.mem_coreMod.1 (f (e7 0)).2) (hfix _ ha hax) (hfix _ hb hbx)
  have hk : ∀ j : Fin 6, f (e7 j) = act7 ⟨piK7 j.succ, Perm.mem_alternatingGroup.2
      (piK7_facts j.succ (Fin.succ_ne_zero j)).1⟩ (f (e7 0)) := by
    intro j
    rw [← hf]
    congr 1
    apply Subtype.ext
    exact ((piK7_facts j.succ (Fin.succ_ne_zero j)).2).symm
  have hgen : ∀ w : ↥(G6.coreMod 7),
      w = e7 0 ^ (Multiplicative.toAdd (w : G6.PermMod 7) 1).val *
        e7 1 ^ (Multiplicative.toAdd (w : G6.PermMod 7) 2).val *
        e7 2 ^ (Multiplicative.toAdd (w : G6.PermMod 7) 3).val *
        e7 3 ^ (Multiplicative.toAdd (w : G6.PermMod 7) 4).val *
        e7 4 ^ (Multiplicative.toAdd (w : G6.PermMod 7) 5).val *
        e7 5 ^ (Multiplicative.toAdd (w : G6.PermMod 7) 6).val := fun w =>
    Subtype.ext (eq_prod_e7 _ (G6.mem_coreMod.1 w.2))
  rcases h1 with h1 | h1
  · left
    have h0 : ∀ j : Fin 6, f (e7 j) = 1 := by
      intro j
      have hf1 : f (e7 0) = 1 := Subtype.ext h1
      rw [hk j, hf1, map_one]
    intro w
    rw [hgen w, map_mul, map_mul, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow,
      map_pow, map_pow, h0, h0, h0, h0, h0, h0]
    simp
  · right
    have h0 : ∀ j : Fin 6, f (e7 j) = e7 j := by
      intro j
      have hf1 : f (e7 0) = e7 0 := Subtype.ext h1
      rw [hk j, hf1]
      apply Subtype.ext
      exact (piK7_facts j.succ (Fin.succ_ne_zero j)).2
    intro w
    conv_lhs => rw [hgen w]
    rw [map_mul, map_mul, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow,
      map_pow, map_pow, h0, h0, h0, h0, h0, h0, ← hgen w]

instance : Nontrivial ↥(G6.coreMod 7) :=
  ⟨⟨e7 0, 1, fun h => vecS_ne_one (congrArg Subtype.val h)⟩⟩

theorem card_mulAut_alt7 :
    Nat.card (MulAut ↥(alternatingGroup (Fin 7))) =
      Nat.card ↥(alternatingGroup (Fin 7)) * 2 ^ 1 := by
  rw [← Nat.card_congr (Equiv.ofBijective _
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
        (by norm_num))),
    nat_card_alternatingGroup, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem ker_altDn7 : (FFModel.altDn 7).ker.subgroupOf (FFModel.altDn 7).sec = ⊥ := by
  rw [eq_bot_iff]
  intro m hm
  rw [Subgroup.mem_subgroupOf] at hm
  have hm' : (show G6.PermMod 7 from m.1) ∈ Subgroup.zpowers (G6.allOnes 7) ⊓ G6.coreMod 7 := hm
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rcases (mem_zpowers_allOnes_iff _).1 hm'.1 with h | h
  · exact h
  · exfalso
    have h2 := G6.mem_coreMod.1 hm'.2
    rw [h] at h2
    revert h2
    decide

@[expose] noncomputable def mod7Equiv : (FFModel.altDn 7).Mod ≃* ↥(G6.coreMod 7) :=
  (QuotientGroup.quotientMulEquivOfEq ker_altDn7).trans QuotientGroup.quotientBot

theorem mod7Equiv_mk (m : ↥(FFModel.altDn 7).sec) :
    mod7Equiv (QuotientGroup.mk m) = m := rfl

end A6L76C

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

section KTilde

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
  {H : Subgroup G} (hH : H ∈ S.Hz) [IsMulCommutative ↥(conjClosure S.V3 H)]
include hNS h13315 h1356two hH

theorem keyDataG_of_realizesBy {K : Subgroup G} (hKH : K ≤ H)
    (hUK : ⁅conjClosure S.V3 H, K⁆ = conjClosure S.V3 H) {D : FFModel}
    {π : D.Gam →* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))}
    {β : ↥(commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) →* ↥D.sec ⧸ D.ker.subgroupOf D.sec}
    (hR : CFSG.Quasithin.H.Mathieu.RealizesBy D
      (autSec (autOn K (conjClosure S.V3 H)) ⊤ ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) π β)
    (hπ : Function.Injective π) {W : Type} [CommGroup W] {act : D.Gam →* MulAut W}
    (e : ↥D.sec ⧸ D.ker.subgroupOf D.sec ≃* W)
    (he : ∀ (γ : D.Gam) (m : ↥D.sec) (hm : D.act γ m ∈ D.sec),
      e (QuotientGroup.mk ⟨D.act γ m, hm⟩) = act γ (e (QuotientGroup.mk m))) :
    Nonempty (S.KeyDataG H K D.Gam W act) := by
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHV := S.le_normalizer_UV1 hH
  let Kt := autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
  have htop : commV Kt = ⊤ := Conf.commV_tilde_eq_top hH hKH hUK
  let eπ : D.Gam ≃* ↥Kt := MulEquiv.ofBijective π ⟨hπ, hR.1⟩
  obtain ⟨-, -, -, -, -, hsec, -, hβs, hβk, hβe⟩ := id hR
  let κ : ↥K →* ↥Kt := ((A6Mod.secAct hHU hHV).comp (Subgroup.inclusion hKH)).codRestrict Kt
    fun k => (A6Mod.mem_autSec_iff hHU hHV hKH).2 ⟨_, k.2, rfl⟩
  have hκ : ∀ k : ↥K, ((κ k : ↥Kt) : MulAut _) = A6Mod.secAct hHU hHV ⟨k, hKH k.2⟩ :=
    fun _ => rfl
  have hκs : Function.Surjective κ := by
    intro x
    obtain ⟨h, hhK, hx⟩ := (A6Mod.mem_autSec_iff hHU hHV hKH).1 x.2
    exact ⟨⟨h, hhK⟩, Subtype.ext hx⟩
  let α : ↥K →* D.Gam := eπ.symm.toMonoidHom.comp κ
  have hπα : ∀ k : ↥K, π (α k) = κ k := fun k => eπ.apply_symm_apply (κ k)
  let ι : ↥(conjClosure S.V3 H) →* ↥(commV Kt) :=
    (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))).codRestrict (commV Kt)
      fun u => (Subgroup.eq_top_iff' _).1 htop _
  let β₀ : ↥(conjClosure S.V3 H) →* W := e.toMonoidHom.comp (β.comp ι)
  have hβ₀ : ∀ u, β₀ u = e (β (ι u)) := fun _ => rfl
  have hker : ∀ u : ↥(conjClosure S.V3 H),
      β₀ u = 1 ↔ ∀ k ∈ K, k * (u : G) * k⁻¹ * (u : G)⁻¹ ∈ fsuV1 T V := by
    intro u
    rw [hβ₀, MulEquiv.map_eq_one_iff, hβk]
    constructor
    · rintro ⟨hfix, -⟩ k hk
      have h1 : A6Mod.secAct hHU hHV ⟨k, hKH hk⟩
          (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u) =
          InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u :=
        hfix _ ((A6Mod.mem_autSec_iff hHU hHV hKH).2 ⟨⟨k, hKH hk⟩, hk, rfl⟩)
      have h2 : A6Mod.secAct hHU hHV ⟨k, hKH hk⟩
          (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u) *
          (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u)⁻¹ = 1 := by
        rw [h1, mul_inv_cancel]
      rw [A6Mod.secAct_secMk, ← map_inv, ← map_mul, A6Mod.secMk_eq_one_iff] at h2
      simpa [Setup.rho_apply_coe] using h2
    · intro h
      refine ⟨fun x hx => ?_, (ι u).2⟩
      obtain ⟨⟨k, hkH⟩, hk, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHV hKH).1 hx
      show A6Mod.secAct hHU hHV ⟨k, hkH⟩
          (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u) =
        InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u
      rw [← mul_inv_eq_one, A6Mod.secAct_secMk, ← map_inv, ← map_mul, A6Mod.secMk_eq_one_iff]
      simpa [Setup.rho_apply_coe] using h k hk
  have hequiv : ∀ (k : ↥K) (u : ↥(conjClosure S.V3 H))
      (hku : (k : G) * u * (k : G)⁻¹ ∈ conjClosure S.V3 H),
      β₀ ⟨_, hku⟩ = act (α k) (β₀ u) := by
    intro k u hku
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β (ι u))
    have hact : D.act (α k) m.1 ∈ D.sec := hsec _ _ m.2
    have hu' : ((π (α k) : ↥Kt) : MulAut _) ((ι u : ↥(commV Kt)) : Sec _ _) ∈ commV Kt :=
      (Subgroup.eq_top_iff' _).1 htop _
    have h1 := hβe (α k) (ι u) m hu' hact hm.symm
    have h2 : (⟨((π (α k) : ↥Kt) : MulAut _) ((ι u : ↥(commV Kt)) : Sec _ _), hu'⟩ :
        ↥(commV Kt)) = ι ⟨_, hku⟩ := by
      apply Subtype.ext
      show ((π (α k) : ↥Kt) : MulAut _) ((ι u : ↥(commV Kt)) : Sec _ _) =
        Subtype.val (ι ⟨_, hku⟩)
      rw [hπα, hκ]
      rfl
    rw [h2] at h1
    rw [hβ₀, hβ₀, h1, ← hm, he]
  refine ⟨⟨hKH, α, β₀, eπ.symm.surjective.comp hκs, fun k => ?_, ?_, hker, hequiv, ?_⟩⟩
  · rw [show α k = eπ.symm (κ k) from rfl, MulEquiv.map_eq_one_iff,
      S.mem_QH_iff_tilde hNS h13315 h1356two hH (hKH k.2)]
    exact Subtype.ext_iff.trans (A6Mod.secAct_eq_one_iff hHU hHV ⟨k, hKH k.2⟩)
  · intro w
    obtain ⟨t, rfl⟩ := e.surjective w
    obtain ⟨x, rfl⟩ := hβs t
    obtain ⟨u, hu⟩ := InternalSec.secMk_surjective _ (Subtype.val x)
    exact ⟨u, by rw [hβ₀]; congr 2; exact Subtype.ext hu⟩
  · rw [hUK]
    exact sup_eq_left.2 S.V1_le_UH

theorem sup_eq_of_realizes6 {K : Subgroup G} (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hUK : ⁅conjClosure S.V3 H, K⁆ = conjClosure S.V3 H)
    {π : (FFModel.altDn 6).Gam →* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))}
    {β : ↥(commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) →*
        ↥(FFModel.altDn 6).sec ⧸ (FFModel.altDn 6).ker.subgroupOf (FFModel.altDn 6).sec}
    (hR : CFSG.Quasithin.H.Mathieu.RealizesBy (FFModel.altDn 6)
      (autSec (autOn K (conjClosure S.V3 H)) ⊤ ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) π β)
    (hπ : Function.Injective π) : K ⊔ T = H := by
  have he : ∀ (γ : (FFModel.altDn 6).Gam) (m : ↥(FFModel.altDn 6).sec)
      (hm : (FFModel.altDn 6).act γ m ∈ (FFModel.altDn 6).sec),
      modW4Equiv (QuotientGroup.mk ⟨(FFModel.altDn 6).act γ m, hm⟩) =
        A6L76C.act6 γ (modW4Equiv (QuotientGroup.mk m)) := by
    intro γ m hm
    rw [modW4Equiv_mk, modW4Equiv_mk]
    apply Subtype.ext
    show nrm (G6.permAct 6 _ (show P6 from m.1)) = nrm (G6.permAct 6 _ (nrm (show P6 from m.1)))
    rw [nrm_permAct_nrm]
    rfl
  have : Finite (FFModel.altDn 6).Gam := inferInstanceAs (Finite ↥(alternatingGroup (Fin 6)))
  obtain ⟨D⟩ := keyDataG_of_realizesBy hNS h13315 h1356two hH hKH hUK hR hπ modW4Equiv he
  exact D.sup_eq A6L76C.endTriv_W4 A6L76C.card_mulAut_alt6 hH
    (S.hypF91 hNS h13315 h1356two hH) hHK

theorem sup_eq_of_realizes7 {K : Subgroup G} (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hUK : ⁅conjClosure S.V3 H, K⁆ = conjClosure S.V3 H)
    {π : (FFModel.altDn 7).Gam →* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))}
    {β : ↥(commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) →*
        ↥(FFModel.altDn 7).sec ⧸ (FFModel.altDn 7).ker.subgroupOf (FFModel.altDn 7).sec}
    (hR : CFSG.Quasithin.H.Mathieu.RealizesBy (FFModel.altDn 7)
      (autSec (autOn K (conjClosure S.V3 H)) ⊤ ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) π β)
    (hπ : Function.Injective π) : K ⊔ T = H := by
  have he : ∀ (γ : (FFModel.altDn 7).Gam) (m : ↥(FFModel.altDn 7).sec)
      (hm : (FFModel.altDn 7).act γ m ∈ (FFModel.altDn 7).sec),
      A6L76C.mod7Equiv (QuotientGroup.mk ⟨(FFModel.altDn 7).act γ m, hm⟩) =
        A6L76C.act7 γ (A6L76C.mod7Equiv (QuotientGroup.mk m)) := by
    intro γ m hm
    rw [A6L76C.mod7Equiv_mk, A6L76C.mod7Equiv_mk]
    rfl
  have : Finite (FFModel.altDn 7).Gam := inferInstanceAs (Finite ↥(alternatingGroup (Fin 7)))
  obtain ⟨D⟩ := keyDataG_of_realizesBy hNS h13315 h1356two hH hKH hUK hR hπ A6L76C.mod7Equiv he
  exact D.sup_eq A6L76C.endTriv_core7 A6L76C.card_mulAut_alt7 hH
    (S.hypF91 hNS h13315 h1356two hH) hHK

end KTilde

end Setting4

end CFSG.Quasithin.H13.A6
