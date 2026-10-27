module

public import CFSG.RankThree.PartTwo.KFacts.KS21FusionCore
public import CFSG.RankThree.PartTwo.KFacts.KS21FusionDFT

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS21

open CFSG.Assembly (IsElemAbelian)
open CFSG.RankThree.PartTwo.KFacts.KS21.DFT

@[expose] def MaxEA (X : Type) [Group X] (n : ℕ) : Prop :=
  (∀ B : Subgroup X, IsElemAbelian 3 B → Nat.card B ≤ 3 ^ n) ∧
    ∀ P : Sylow 3 X, ∀ B B' : Subgroup X, B ≤ P → B' ≤ P → IsElemAbelian 3 B →
      IsElemAbelian 3 B' → Nat.card B = 3 ^ n → Nat.card B' = 3 ^ n → B = B'

theorem MaxEA.of_mulEquiv {X Y : Type} [Group X] [Group Y] {n : ℕ} (e : X ≃* Y)
    (h : MaxEA X n) : MaxEA Y n := by
  have hcard : ∀ B : Subgroup Y, Nat.card (B.map e.symm.toMonoidHom) = Nat.card B :=
    fun B => Subgroup.card_map_of_injective e.symm.injective
  refine ⟨fun B hB => ?_, fun P B B' hBP hB'P hB hB' hc hc' => ?_⟩
  · rw [← hcard]
    exact h.1 _ (isElemAbelian_map _ hB)
  · obtain ⟨P', hP'⟩ : ∃ P' : Sylow 3 X,
        (P' : Subgroup X) = (P : Subgroup Y).comap e.toMonoidHom :=
      ⟨P.comapOfInjective e.toMonoidHom e.injective (fun y _ => ⟨e.symm y, by simp⟩),
        Sylow.coe_comapOfInjective _ _ _ _⟩
    have hle : ∀ C : Subgroup Y, C ≤ P → C.map e.symm.toMonoidHom ≤ P' := by
      rintro C hC _ ⟨y, hy, rfl⟩
      rw [hP', Subgroup.mem_comap]
      simpa using hC hy
    have := h.2 P' _ _ (hle B hBP) (hle B' hB'P) (isElemAbelian_map _ hB)
      (isElemAbelian_map _ hB') (by rw [hcard, hc]) (by rw [hcard, hc'])
    exact Subgroup.map_injective e.symm.injective this

theorem elemThompson_eq_of_maxEA {G : Type} [Group G] [Finite G] {I : Subgroup G} {n : ℕ}
    (h : MaxEA I n) (P : Sylow 3 I) {A : Subgroup G} (hA : IsElemAbelian 3 A)
    (hAP : A ≤ (P : Subgroup I).map I.subtype) (hcard : Nat.card A = 3 ^ n) :
    (CFSG.elemThompson ((P : Subgroup I).map I.subtype) 3).map
      ((P : Subgroup I).map I.subtype).subtype = A := by
  set P' := (P : Subgroup I).map I.subtype with hP'def
  have hP'I : P' ≤ I := Subgroup.map_subtype_le _
  have hAI : A ≤ I := hAP.trans hP'I
  have hinP : ∀ C : Subgroup G, C ≤ P' → C.subgroupOf I ≤ P := by
    intro C hC x hx
    obtain ⟨y, hy, hyx⟩ := hC hx
    rw [← Subtype.ext hyx]
    exact hy
  have hcardI : ∀ C : Subgroup G, C ≤ I → Nat.card (C.subgroupOf I) = Nat.card C :=
    fun C hC => Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC).toEquiv
  have hEAI : ∀ C : Subgroup G, IsElemAbelian 3 C → IsElemAbelian 3 (C.subgroupOf I) := by
    intro C hC
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => Subtype.ext ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      show ((a : I) : G) * ((b : I) : G) = ((b : I) : G) * ((a : I) : G)
      exact congrArg Subtype.val (hC.1.is_comm.comm ⟨((a : I) : G), a.2⟩ ⟨((b : I) : G), b.2⟩)
    · exact hC.2 _ hx
  have hAEA : IsElemAbelian 3 (A.subgroupOf I) := hEAI A hA
  have hmapI : ∀ C : Subgroup G, C ≤ I → (C.subgroupOf I).map I.subtype = C := fun C hC => by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hC]
  have key : ∀ F : Subgroup P', CFSG.IsElementaryAbelian 3 F →
      Nat.card F ≤ 3 ^ n ∧ (Nat.card F = 3 ^ n → F.map P'.subtype = A) := by
    intro F hF
    have hF' : IsElemAbelian 3 (F.map P'.subtype) := by
      refine isElemAbelian_map _ ⟨hF.toIsMulCommutative, fun x hx => ?_⟩
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian x hx
    have hFP : F.map P'.subtype ≤ P' := Subgroup.map_subtype_le _
    have hcF : Nat.card (F.map P'.subtype) = Nat.card F :=
      Subgroup.card_map_of_injective P'.subtype_injective
    have hcF' := hcardI _ (hFP.trans hP'I)
    refine ⟨?_, fun hc => ?_⟩
    · rw [← hcF, ← hcF']
      exact h.1 _ (hEAI _ hF')
    · have := h.2 P _ _ (hinP _ hFP) (hinP _ hAP) (hEAI _ hF') hAEA (by rw [hcF', hcF, hc])
        (by rw [hcardI _ hAI, hcard])
      rw [← hmapI _ (hFP.trans hP'I), this, hmapI _ hAI]
  set E := A.subgroupOf P' with hEdef
  have hEmap : E.map P'.subtype = A := by rw [hEdef, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr hAP]
  have hcardE : Nat.card E = 3 ^ n := by
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv
  have hEab : CFSG.IsElementaryAbelian 3 E := by
    refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
    · apply Subtype.ext
      apply Subtype.ext
      show ((a : P') : G) * ((b : P') : G) = ((b : P') : G) * ((a : P') : G)
      exact congrArg Subtype.val (hA.1.is_comm.comm ⟨((a : P') : G), a.2⟩ ⟨((b : P') : G), b.2⟩)
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
      apply Subtype.ext
      apply Subtype.ext
      exact hA.2 _ a.2
  have hrank : CFSG.pRank 3 P' = n := by
    apply IsGreatest.csSup_eq
    refine ⟨⟨E, hEab, hcardE⟩, ?_⟩
    rintro r ⟨F, hF, hFcard⟩
    have := (key F hF).1
    rw [hFcard] at this
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  have hfam : CFSG.elemThompsonFamily P' 3 = {E} := by
    ext F
    constructor
    · rintro ⟨hF, hFcard⟩
      rw [hrank] at hFcard
      have := (key F hF).2 hFcard
      rw [← hEmap] at this
      exact Subgroup.map_injective P'.subtype_injective this
    · rintro rfl
      exact ⟨hEab, by rw [hrank, hcardE]⟩
  rw [CFSG.elemThompson, hfam, sSup_singleton, hEmap]

theorem nonempty_sylow_mulEquiv {X W : Type} [Group X] [Finite X] [Group W] (Φ : W →* X)
    (hΦ : Function.Injective Φ) (hW : Nat.card W = 3 ^ (Nat.card X).factorization 3)
    (P : Sylow 3 X) : Nonempty ((P : Subgroup X) ≃* W) := by
  have hR : Nat.card Φ.range = 3 ^ (Nat.card X).factorization 3 := by
    rw [← hW]
    exact Nat.card_congr (MonoidHom.ofInjective hΦ).toEquiv.symm
  let R : Sylow 3 X := Sylow.ofCard Φ.range hR
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq X R P
  have hP : (P : Subgroup X) = Φ.range.map (MulAut.conj h).toMonoidHom := by
    ext x
    rw [← hh, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      Subgroup.mem_map]
    constructor
    · intro hx
      refine ⟨(MulAut.conj h)⁻¹ • x, hx, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, ← MulAut.smul_def, smul_inv_smul]
    · rintro ⟨y, hy, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, ← MulAut.smul_def, inv_smul_smul]
      exact hy
  exact ⟨(MulEquiv.subgroupCongr hP).trans
    ((Subgroup.equivMapOfInjective Φ.range _ (MulAut.conj h).injective).symm.trans
      (MonoidHom.ofInjective hΦ).symm)⟩

@[expose] def SylowModel (X W : Type) [Group X] [Group W] : Prop :=
  ∃ Φ : W →* X, Function.Injective Φ ∧ Nat.card W = 3 ^ (Nat.card X).factorization 3

theorem SylowModel.of_mulEquiv {X Y W : Type} [Group X] [Group Y] [Group W] (e : X ≃* Y)
    (h : SylowModel X W) : SylowModel Y W := by
  obtain ⟨Φ, hΦ, hW⟩ := h
  exact ⟨e.toMonoidHom.comp Φ, e.injective.comp hΦ, by rw [hW, Nat.card_congr e.toEquiv]⟩

theorem SylowModel.nonempty_mulEquiv {X W : Type} [Group X] [Finite X] [Group W]
    (h : SylowModel X W) (P : Sylow 3 X) : Nonempty ((P : Subgroup X) ≃* W) := by
  obtain ⟨Φ, hΦ, hW⟩ := h
  exact nonempty_sylow_mulEquiv Φ hΦ hW P

theorem factorization_three_eq {N m k : ℕ} (hN : N = 3 ^ m * k) (hk : ¬ 3 ∣ k) :
    N.factorization 3 = m := by
  have hk0 : k ≠ 0 := by rintro rfl; exact hk (dvd_zero 3)
  rw [hN, Nat.factorization_mul (by positivity) hk0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Nat.factorization_eq_zero_of_not_dvd hk,
    add_zero, Finsupp.single_eq_same]

theorem card_V3_three : Nat.card {a : Fin 3 → ZMod 3 // 3 • a = 0} = 3 ^ 3 := by
  have h : ∀ a : Fin 3 → ZMod 3, 3 • a = 0 := fun a => by
    funext i
    simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
    rw [show ((3 : ℕ) : ZMod 3) = 0 from rfl, zero_mul]
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv h), Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem card_fix3_lt :
    3 * Nat.card {u : Fin 3 → ZMod 3 // rot3 u = u ∧ 3 • u = 0} <
      Nat.card {a : Fin 3 → ZMod 3 // 3 • a = 0} := by
  rw [card_V3_three]
  have h : Nat.card {u : Fin 3 → ZMod 3 // rot3 u = u ∧ 3 • u = 0} ≤ Nat.card (ZMod 3) :=
    Nat.card_le_card_of_injective (fun u => u.1 0) fun u v huv => by
      apply Subtype.ext
      rw [rot3_fixed u.2.1, rot3_fixed v.2.1]
      exact congrArg (fun c => fun _ : Fin 3 => c) huv
  rw [Nat.card_zmod] at h
  omega

abbrev Z9three := {a : ZMod 9 // 3 • a = 0}

theorem card_Z9three : Nat.card Z9three = 3 := by
  rw [Nat.card_eq_fintype_card]
  decide

@[expose] def v9ThreeEquiv :
    {a : (Fin 3 → ZMod 9) × ZMod 9 // 3 • a = 0} ≃ (Fin 3 → Z9three) × Z9three where
  toFun a := (fun i => ⟨a.1.1 i, by
      have := congrFun (congrArg Prod.fst a.2) i
      simpa using this⟩, ⟨a.1.2, by
      have := congrArg Prod.snd a.2
      simpa using this⟩)
  invFun b := ⟨(fun i => (b.1 i).1, b.2.1), by
    rw [Prod.smul_mk, Prod.mk_eq_zero]
    exact ⟨funext fun i => (b.1 i).2, b.2.2⟩⟩
  left_inv a := rfl
  right_inv b := rfl

theorem card_V9_three : Nat.card {a : (Fin 3 → ZMod 9) × ZMod 9 // 3 • a = 0} = 3 ^ 4 := by
  rw [Nat.card_congr v9ThreeEquiv, Nat.card_prod, Nat.card_fun, card_Z9three, Nat.card_fin]
  norm_num

theorem card_fix9_lt :
    3 * Nat.card {u : (Fin 3 → ZMod 9) × ZMod 9 // rot9 u = u ∧ 3 • u = 0} <
      Nat.card {a : (Fin 3 → ZMod 9) × ZMod 9 // 3 • a = 0} := by
  rw [card_V9_three]
  have h : Nat.card {u : (Fin 3 → ZMod 9) × ZMod 9 // rot9 u = u ∧ 3 • u = 0} ≤
      Nat.card (Z9three × Z9three) := by
    refine Nat.card_le_card_of_injective (fun u => (⟨u.1.1 0, ?_⟩, ⟨u.1.2, ?_⟩)) ?_
    · have := congrFun (congrArg Prod.fst u.2.2) 0
      simpa using this
    · have := congrArg Prod.snd u.2.2
      simpa using this
    · intro u v huv
      have h1 : u.1.1 0 = v.1.1 0 := congrArg (fun p => (p.1 : ZMod 9)) huv
      have h2 : u.1.2 = v.1.2 := congrArg (fun p => (p.2 : ZMod 9)) huv
      have hu1 : rot3 u.1.1 = u.1.1 := congrArg Prod.fst u.2.1
      have hv1 : rot3 v.1.1 = v.1.1 := congrArg Prod.fst v.2.1
      have hu := rot3_fixed hu1
      have hv := rot3_fixed hv1
      apply Subtype.ext
      refine Prod.ext ?_ h2
      rw [hu, hv, h1]
  rw [Nat.card_prod, card_Z9three] at h
  omega

section Torus

variable {X : Type} [Group X] {V : Type} [AddCommGroup V] {σ : V →+ V}
  {τ : Multiplicative V →* X} {w : X}

@[expose] def fixPart (σ : V →+ V) (τ : Multiplicative V →* X) (w : X) : Set X :=
  {x | ∃ u : V, σ u = u ∧ 3 • u = 0 ∧ ∃ i : Fin 3, x = τ (.ofAdd u) * w ^ (i : ℕ)}

theorem card_fixPart_le [Finite V] :
    Nat.card (fixPart σ τ w) ≤ 3 * Nat.card {u : V // σ u = u ∧ 3 • u = 0} := by
  let f : {u : V // σ u = u ∧ 3 • u = 0} × Fin 3 → fixPart σ τ w := fun p =>
    ⟨τ (.ofAdd p.1.1) * w ^ (p.2 : ℕ), p.1.1, p.1.2.1, p.1.2.2, p.2, rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨_, u, hu, hu3, i, rfl⟩
    exact ⟨(⟨u, hu, hu3⟩, i), rfl⟩
  have := Nat.card_le_card_of_surjective f hf
  rwa [Nat.card_prod, Nat.card_fin, mul_comm] at this

theorem card_torusOmega (hτ : Function.Injective τ) :
    Nat.card (torusOmega τ) = Nat.card {a : V // 3 • a = 0} := by
  refine (Nat.card_eq_of_bijective (fun a : {a : V // 3 • a = 0} =>
    (⟨τ (.ofAdd a.1), a.1, a.2, rfl⟩ : torusOmega τ)) ⟨fun a b h => ?_, ?_⟩).symm
  · exact Subtype.ext (Multiplicative.ofAdd.injective (hτ (congrArg Subtype.val h)))
  · rintro ⟨_, a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

theorem le_torusOmega_or_conj_subset_fixPart (hτ : Function.Injective τ) (hw3 : w ^ 3 = 1)
    (hwτ : ∀ v, w * τ (.ofAdd v) = τ (.ofAdd (σ v)) * w)
    (hN : ∀ v, v + σ v + σ (σ v) = 0 → ∃ s c, v = σ s - s + c ∧ σ c = c ∧ 3 • c = 0)
    {B : Subgroup X} (hB : IsElemAbelian 3 B) (hBP : B ≤ torusExt σ τ w hw3 hwτ) :
    B ≤ torusOmega τ ∨ ∃ y : X, ∀ z ∈ B, y * z * y⁻¹ ∈ fixPart σ τ w := by
  by_cases hT : ∃ b ∈ B, ∀ v, b ≠ τ (.ofAdd v)
  · right
    obtain ⟨b, hbB, hbT⟩ := hT
    obtain ⟨v, j, rfl⟩ := hBP hbB
    have hwj : w ^ j = w ^ (j % 3) := pow_eq_pow_mod j hw3
    obtain ⟨v', hv'B⟩ : ∃ v', τ (.ofAdd v') * w ∈ B := by
      have hj : j % 3 = 1 ∨ j % 3 = 2 := by
        have hj0 : j % 3 ≠ 0 := by
          intro h0
          apply hbT v
          rw [hwj, h0, pow_zero, mul_one]
        omega
      rcases hj with h1 | h2
      · exact ⟨v, by rw [hwj, h1, pow_one] at hbB; exact hbB⟩
      · refine ⟨v + σ (σ v), ?_⟩
        have hsq := B.pow_mem hbB 2
        rwa [hwj, h2, tau_mul_sq_sq hw3 hwτ] at hsq
    have hx3 := hB.2 _ hv'B
    rw [tau_mul_pow_three hwτ, hw3, mul_one, ← map_one τ, ← ofAdd_zero] at hx3
    obtain ⟨s, c, hv', hc, -⟩ := hN v' (Multiplicative.ofAdd.injective (hτ hx3))
    have hy₀P : τ (.ofAdd s) ∈ torusExt σ τ w hw3 hwτ := ⟨s, 0, by rw [pow_zero, mul_one]⟩
    have hx' : τ (.ofAdd s) * (τ (.ofAdd v') * w) * (τ (.ofAdd s))⁻¹ = τ (.ofAdd c) * w := by
      rw [tau_conj_tau_mul hwτ]
      congr 3
      rw [hv']
      abel
    refine ⟨τ (.ofAdd s), fun z₀ hz₀B => ?_⟩
    have hz₁P : τ (.ofAdd s) * z₀ * (τ (.ofAdd s))⁻¹ ∈ torusExt σ τ w hw3 hwτ :=
      (torusExt σ τ w hw3 hwτ).mul_mem ((torusExt σ τ w hw3 hwτ).mul_mem hy₀P (hBP hz₀B))
        ((torusExt σ τ w hw3 hwτ).inv_mem hy₀P)
    obtain ⟨u, i, hui⟩ := hz₁P
    have hcomm0 : z₀ * (τ (.ofAdd v') * w) = τ (.ofAdd v') * w * z₀ := by
      have := hB.1.is_comm.comm ⟨z₀, hz₀B⟩ ⟨_, hv'B⟩
      exact congrArg Subtype.val this
    have hcomm : ∀ r, z₀ * (τ (.ofAdd v') * (w * r)) = τ (.ofAdd v') * (w * (z₀ * r)) := by
      intro r
      calc z₀ * (τ (.ofAdd v') * (w * r)) = z₀ * (τ (.ofAdd v') * w) * r := by
            simp only [mul_assoc]
        _ = τ (.ofAdd v') * w * z₀ * r := by rw [hcomm0]
        _ = τ (.ofAdd v') * (w * (z₀ * r)) := by simp only [mul_assoc]
    have hcomm' : τ (.ofAdd u) * w ^ i * (τ (.ofAdd c) * w) =
        τ (.ofAdd c) * w * (τ (.ofAdd u) * w ^ i) := by
      rw [← hui, ← hx']
      simp only [mul_assoc, inv_mul_cancel_left, hcomm]
    have hu := fixed_of_commute hτ hwτ hc u i hcomm'
    have hz3 : (τ (.ofAdd u) * w ^ i) ^ 3 = 1 := by
      rw [← hui, conj_pow, hB.2 z₀ hz₀B, mul_one, mul_inv_cancel]
    rw [tau_mul_pow_pow_three hw3 hwτ hu, ← map_one τ, ← ofAdd_zero] at hz3
    refine ⟨u, hu, Multiplicative.ofAdd.injective (hτ hz3), ⟨i % 3, Nat.mod_lt _ (by norm_num)⟩,
      ?_⟩
    rw [hui]
    exact congrArg _ (pow_eq_pow_mod i hw3)
  · left
    push Not at hT
    intro z hz
    obtain ⟨v, hv⟩ := hT z hz
    have h3 := hB.2 z hz
    rw [hv, ← map_pow, ← ofAdd_nsmul, ← map_one τ, ← ofAdd_zero] at h3
    exact ⟨v, Multiplicative.ofAdd.injective (hτ h3), hv.symm⟩

theorem card_le_of_le_torusExt [Finite X] [Finite V] (hτ : Function.Injective τ)
    (hw3 : w ^ 3 = 1) (hwτ : ∀ v, w * τ (.ofAdd v) = τ (.ofAdd (σ v)) * w)
    (hN : ∀ v, v + σ v + σ (σ v) = 0 → ∃ s c, v = σ s - s + c ∧ σ c = c ∧ 3 • c = 0)
    (hfix : 3 * Nat.card {u : V // σ u = u ∧ 3 • u = 0} < Nat.card (torusOmega τ))
    {B : Subgroup X} (hB : IsElemAbelian 3 B) (hBP : B ≤ torusExt σ τ w hw3 hwτ) :
    Nat.card B ≤ Nat.card (torusOmega τ) ∧
      (Nat.card B = Nat.card (torusOmega τ) → B = torusOmega τ) := by
  rcases le_torusOmega_or_conj_subset_fixPart hτ hw3 hwτ hN hB hBP with hle | ⟨y, hy⟩
  · exact ⟨Subgroup.card_le_of_le hle, fun h => Subgroup.eq_of_le_of_card_ge hle h.ge⟩
  · have h1 : Nat.card B ≤ Nat.card (fixPart σ τ w) :=
      Nat.card_le_card_of_injective (fun b => ⟨y * b * y⁻¹, hy b b.2⟩) (fun a b h => by
        have h' : y * (a : X) * y⁻¹ = y * b * y⁻¹ := congrArg Subtype.val h
        rw [mul_left_inj, mul_right_inj] at h'
        exact Subtype.ext h')
    have hlt := lt_of_le_of_lt (h1.trans card_fixPart_le) hfix
    exact ⟨hlt.le, fun h => absurd h hlt.ne⟩

theorem exists_sylow_torusExt [Finite X] [Finite V] (hτ : Function.Injective τ)
    (hw3 : w ^ 3 = 1) (hwτ : ∀ v, w * τ (.ofAdd v) = τ (.ofAdd (σ v)) * w)
    (hσ : ∃ v, σ v ≠ v) {e k : ℕ} (hV : Nat.card V = 3 ^ e)
    (hX : Nat.card X = 3 ^ (e + 1) * k) (hk : ¬ 3 ∣ k) :
    ∃ P₀ : Sylow 3 X, (P₀ : Subgroup X) = torusExt σ τ w hw3 hwτ := by
  have hk0 : k ≠ 0 := by rintro rfl; exact hk (dvd_zero 3)
  have hcard : Nat.card (torusExt σ τ w hw3 hwτ) = 3 ^ (Nat.card X).factorization 3 := by
    rw [card_torusExt hτ hw3 hwτ hσ, hV, hX, Nat.factorization_mul (by positivity) hk0,
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd hk, add_zero, Finsupp.single_eq_same, pow_succ,
      mul_comm]
  exact ⟨Sylow.ofCard _ hcard, rfl⟩

theorem map_conj_inv_le {P₀ Q : Sylow 3 X} {h : X} (hh : h • P₀ = Q) {B : Subgroup X}
    (hBQ : B ≤ Q) : B.map (MulAut.conj h⁻¹).toMonoidHom ≤ P₀ := by
  rintro _ ⟨b, hb, rfl⟩
  have hbQ := hBQ hb
  rw [← hh, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hbQ
  convert hbQ using 1
  simp

theorem maxEA_of_torus [Finite X] [Finite V] (hτ : Function.Injective τ) (hw3 : w ^ 3 = 1)
    (hwτ : ∀ v, w * τ (.ofAdd v) = τ (.ofAdd (σ v)) * w) (hσ : ∃ v, σ v ≠ v) {e k : ℕ}
    (hV : Nat.card V = 3 ^ e) (hX : Nat.card X = 3 ^ (e + 1) * k) (hk : ¬ 3 ∣ k)
    (hN : ∀ v, v + σ v + σ (σ v) = 0 → ∃ s c, v = σ s - s + c ∧ σ c = c ∧ 3 • c = 0)
    (hfix : 3 * Nat.card {u : V // σ u = u ∧ 3 • u = 0} < Nat.card {a : V // 3 • a = 0})
    {n : ℕ} (hn : Nat.card {a : V // 3 • a = 0} = 3 ^ n) : MaxEA X n := by
  obtain ⟨P₀, hP₀⟩ := exists_sylow_torusExt hτ hw3 hwτ hσ hV hX hk
  have hA₀ := card_torusOmega hτ
  have hfix' : 3 * Nat.card {u : V // σ u = u ∧ 3 • u = 0} < Nat.card (torusOmega τ) := by
    rw [hA₀]; exact hfix
  have hconj : ∀ B : Subgroup X, ∀ y : X,
      Nat.card (B.map (MulAut.conj y).toMonoidHom) = Nat.card B :=
    fun B y => Subgroup.card_map_of_injective (MulAut.conj y).injective
  have hbound : ∀ Q : Sylow 3 X, ∀ B : Subgroup X, B ≤ Q → IsElemAbelian 3 B →
      ∃ h : X, Nat.card B ≤ 3 ^ n ∧ (Nat.card B = 3 ^ n →
        B.map (MulAut.conj h⁻¹).toMonoidHom = torusOmega τ) := by
    intro Q B hBQ hB
    obtain ⟨h, hh⟩ := MulAction.exists_smul_eq X P₀ Q
    have hle := map_conj_inv_le hh hBQ
    rw [hP₀] at hle
    obtain ⟨h1, h2⟩ := card_le_of_le_torusExt hτ hw3 hwτ hN hfix' (isElemAbelian_map _ hB) hle
    rw [hconj, hA₀, hn] at h1 h2
    exact ⟨h, h1, h2⟩
  refine ⟨fun B hB => ?_, fun Q B B' hBQ hB'Q hB hB' hc hc' => ?_⟩
  · obtain ⟨Q, hQ⟩ := (isPGroup_of_isElemAbelian hB).exists_le_sylow
    obtain ⟨h, h1, -⟩ := hbound Q B hQ hB
    exact h1
  · obtain ⟨h, hh⟩ := MulAction.exists_smul_eq X P₀ Q
    have hmap : ∀ C : Subgroup X, C ≤ Q → IsElemAbelian 3 C → Nat.card C = 3 ^ n →
        C.map (MulAut.conj h⁻¹).toMonoidHom = torusOmega τ := by
      intro C hCQ hC hcC
      have hle := map_conj_inv_le hh hCQ
      rw [hP₀] at hle
      obtain ⟨-, h2⟩ := card_le_of_le_torusExt hτ hw3 hwτ hN hfix' (isElemAbelian_map _ hC) hle
      exact h2 (by rw [hconj, hA₀, hn, hcC])
    exact Subgroup.map_injective (MulAut.conj h⁻¹).injective
      ((hmap B hBQ hB hc).trans (hmap B' hB'Q hB' hc').symm)

theorem maxEA_of_torus_hom {G₀ : Type} [Group G₀] [Finite X] [Finite V]
    (ι : G₀ →* X) (hι : Function.Injective ι) {τ₁ : Multiplicative V →* G₀}
    (hτ₁ : Function.Injective τ₁) {w₀ : G₀} (hw3 : w₀ ^ 3 = 1)
    (hwτ : ∀ v, w₀ * τ₁ (.ofAdd v) = τ₁ (.ofAdd (σ v)) * w₀) (hσ : ∃ v, σ v ≠ v) {e k : ℕ}
    (hV : Nat.card V = 3 ^ e) (hX : Nat.card X = 3 ^ (e + 1) * k) (hk : ¬ 3 ∣ k)
    (hN : ∀ v, v + σ v + σ (σ v) = 0 → ∃ s c, v = σ s - s + c ∧ σ c = c ∧ 3 • c = 0)
    (hfix : 3 * Nat.card {u : V // σ u = u ∧ 3 • u = 0} < Nat.card {a : V // 3 • a = 0})
    {n : ℕ} (hn : Nat.card {a : V // 3 • a = 0} = 3 ^ n) : MaxEA X n :=
  maxEA_of_torus (σ := σ) (τ := ι.comp τ₁) (w := ι w₀) (hι.comp hτ₁)
    (by rw [← map_pow, hw3, map_one])
    (fun v => by rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_mul, ← map_mul, hwτ])
    hσ hV hX hk hN hfix hn

theorem maxEA_of_torus_sub {G₀ Y : Type} [Group G₀] [Group Y] {S : Subgroup Y}
    [Finite S] [Finite V] (ι : G₀ →* Y) (hι : Function.Injective ι)
    {τ₁ : Multiplicative V →* G₀} (hτ₁ : Function.Injective τ₁) (hτS : ∀ v, ι (τ₁ v) ∈ S)
    {w₀ : G₀} (hwS : ι w₀ ∈ S) (hw3 : w₀ ^ 3 = 1)
    (hwτ : ∀ v, w₀ * τ₁ (.ofAdd v) = τ₁ (.ofAdd (σ v)) * w₀) (hσ : ∃ v, σ v ≠ v) {e k : ℕ}
    (hV : Nat.card V = 3 ^ e) (hX : Nat.card S = 3 ^ (e + 1) * k) (hk : ¬ 3 ∣ k)
    (hN : ∀ v, v + σ v + σ (σ v) = 0 → ∃ s c, v = σ s - s + c ∧ σ c = c ∧ 3 • c = 0)
    (hfix : 3 * Nat.card {u : V // σ u = u ∧ 3 • u = 0} < Nat.card {a : V // 3 • a = 0})
    {n : ℕ} (hn : Nat.card {a : V // 3 • a = 0} = 3 ^ n) : MaxEA S n := by
  let G₁ : Subgroup G₀ := S.comap ι
  let ι₁ : G₁ →* S := (ι.comp G₁.subtype).codRestrict S (fun x => x.2)
  have hι₁ : Function.Injective ι₁ := fun x y h => Subtype.ext (hι (congrArg Subtype.val h))
  let τ₂ : Multiplicative V →* G₁ := τ₁.codRestrict G₁ hτS
  have hτ₂ : Function.Injective τ₂ := fun x y h => hτ₁ (congrArg Subtype.val h)
  exact maxEA_of_torus_hom ι₁ hι₁ (τ₁ := τ₂) hτ₂ (w₀ := ⟨w₀, hwS⟩) (Subtype.ext hw3)
    (fun v => Subtype.ext (hwτ v)) hσ hV hX hk hN hfix hn

end Torus

section Wreath

variable {X : Type} [Group X]

@[expose] def wvec {R : Type} [AddCommGroup R] (f : Multiplicative (ZMod 3) → Multiplicative R) :
    Fin 3 → R :=
  fun k : Fin 3 => Multiplicative.toAdd (f (Multiplicative.ofAdd (α := ZMod 3) k))

theorem wvec_shift {R : Type} [AddCommGroup R] (f : Multiplicative (ZMod 3) → Multiplicative R)
    (q : Multiplicative (ZMod 3)) :
    wvec (fun x => f (q⁻¹ * x)) = (⇑rot3)^[(Multiplicative.toAdd q).val] (wvec f) := by
  obtain ⟨r, rfl⟩ := Multiplicative.ofAdd.surjective q
  funext k
  fin_cases r <;> fin_cases k <;> rfl

theorem wvec_mul_left {R : Type} [AddCommGroup R]
    (x y : Multiplicative R ≀ᵣ Multiplicative (ZMod 3)) :
    wvec (x * y).left =
      wvec x.left + (⇑rot3)^[(Multiplicative.toAdd x.right).val] (wvec y.left) := by
  rw [← wvec_shift]
  rfl

theorem wvec_eq_zero {R : Type} [AddCommGroup R] {f : Multiplicative (ZMod 3) → Multiplicative R}
    (h : wvec f = 0) : f = 1 := by
  funext z
  obtain ⟨k, rfl⟩ := Multiplicative.ofAdd.surjective z
  have := congrFun h k
  exact Multiplicative.toAdd.injective this

theorem pow_val_mul {w : X} (hw3 : w ^ 3 = 1) (a b : Multiplicative (ZMod 3)) :
    w ^ (Multiplicative.toAdd (a * b)).val =
      w ^ (Multiplicative.toAdd a).val * w ^ (Multiplicative.toAdd b).val := by
  rw [toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ hw3, pow_add]

@[expose] def wreathHom {R : Type} [AddCommGroup R] (τ : Multiplicative (Fin 3 → R) →* X) (w : X)
    (hw3 : w ^ 3 = 1) (hwτ : ∀ v, w * τ (.ofAdd v) = τ (.ofAdd (rot3 v)) * w) :
    Multiplicative R ≀ᵣ Multiplicative (ZMod 3) →* X where
  toFun x := τ (.ofAdd (wvec x.left)) * w ^ (Multiplicative.toAdd x.right).val
  map_one' := by
    have h0 : wvec (1 : Multiplicative (ZMod 3) → Multiplicative R) = 0 := rfl
    simp only [RegularWreathProduct.one_left, RegularWreathProduct.one_right, h0, toAdd_one,
      ZMod.val_zero, pow_zero, mul_one, ofAdd_zero, map_one]
  map_mul' x y := by
    show τ (.ofAdd (wvec (x * y).left)) * w ^ (Multiplicative.toAdd (x * y).right).val =
      τ (.ofAdd (wvec x.left)) * w ^ (Multiplicative.toAdd x.right).val *
        (τ (.ofAdd (wvec y.left)) * w ^ (Multiplicative.toAdd y.right).val)
    rw [wvec_mul_left, RegularWreathProduct.mul_right, pow_val_mul hw3, ofAdd_add, map_mul]
    calc τ (.ofAdd (wvec x.left)) * τ (.ofAdd ((⇑rot3)^[(Multiplicative.toAdd x.right).val]
          (wvec y.left))) * (w ^ (Multiplicative.toAdd x.right).val *
            w ^ (Multiplicative.toAdd y.right).val)
        = τ (.ofAdd (wvec x.left)) * (τ (.ofAdd ((⇑rot3)^[(Multiplicative.toAdd x.right).val]
          (wvec y.left))) * w ^ (Multiplicative.toAdd x.right).val) *
            w ^ (Multiplicative.toAdd y.right).val := by simp only [mul_assoc]
      _ = _ := by rw [← pow_mul_tau hwτ]; simp only [mul_assoc]

theorem eq_zero_of_tau_mul_pow_eq_one {V : Type} [AddCommGroup V] {σ : V →+ V}
    {τ : Multiplicative V →* X} (hτ : Function.Injective τ) {w : X} (hw3 : w ^ 3 = 1)
    (hwτ : ∀ v, w * τ (.ofAdd v) = τ (.ofAdd (σ v)) * w) (hσ : ∃ v, σ v ≠ v) {v : V} {j : ℕ}
    (hj : j < 3) (h : τ (.ofAdd v) * w ^ j = 1) : j = 0 ∧ v = 0 := by
  have hj0 : j = 0 := by
    by_contra hne
    apply pow_ne_tau hτ hw3 hwτ hσ (d := j) (by omega) (-v)
    rw [ofAdd_neg, map_inv, eq_inv_iff_mul_eq_one, mul_eq_one_comm]
    exact h
  subst hj0
  rw [pow_zero, mul_one, ← map_one τ, ← ofAdd_zero] at h
  exact ⟨rfl, Multiplicative.ofAdd.injective (hτ h)⟩

theorem wreathHom_injective {R : Type} [AddCommGroup R] {τ : Multiplicative (Fin 3 → R) →* X}
    (hτ : Function.Injective τ) {w : X} (hw3 : w ^ 3 = 1)
    (hwτ : ∀ v, w * τ (.ofAdd v) = τ (.ofAdd (rot3 v)) * w)
    (hσ : ∃ v : Fin 3 → R, rot3 v ≠ v) : Function.Injective (wreathHom τ w hw3 hwτ) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨hj, hv⟩ := eq_zero_of_tau_mul_pow_eq_one hτ hw3 hwτ hσ
    (ZMod.val_lt (Multiplicative.toAdd x.right)) hx
  refine RegularWreathProduct.ext (wvec_eq_zero hv) ?_
  rw [ZMod.val_eq_zero] at hj
  exact Multiplicative.toAdd.injective hj

theorem rot9_iterate (n : ℕ) (u : Fin 3 → ZMod 9) (d : ZMod 9) :
    (⇑rot9)^[n] (u, d) = ((⇑rot3)^[n] u, d) := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, rot9_apply, ih]

@[expose] def wreathHom9 (τ : Multiplicative ((Fin 3 → ZMod 9) × ZMod 9) →* X) (w : X)
    (hw3 : w ^ 3 = 1) (hwτ : ∀ v, w * τ (.ofAdd v) = τ (.ofAdd (rot9 v)) * w) :
    Multiplicative (ZMod 9) × (Multiplicative (ZMod 9) ≀ᵣ Multiplicative (ZMod 3)) →* X where
  toFun x := τ (.ofAdd (wvec x.2.left, Multiplicative.toAdd x.1)) *
    w ^ (Multiplicative.toAdd x.2.right).val
  map_one' := by
    have h0 : wvec (1 : Multiplicative (ZMod 3) → Multiplicative (ZMod 9)) = 0 := rfl
    simp only [Prod.snd_one, Prod.fst_one, RegularWreathProduct.one_left,
      RegularWreathProduct.one_right, h0, toAdd_one, ZMod.val_zero, pow_zero, mul_one]
    rw [show ((0 : Fin 3 → ZMod 9), (0 : ZMod 9)) = 0 from rfl, ofAdd_zero, map_one]
  map_mul' x y := by
    show τ (.ofAdd (wvec (x.2 * y.2).left, Multiplicative.toAdd (x.1 * y.1))) *
        w ^ (Multiplicative.toAdd (x.2 * y.2).right).val =
      τ (.ofAdd (wvec x.2.left, Multiplicative.toAdd x.1)) *
          w ^ (Multiplicative.toAdd x.2.right).val *
        (τ (.ofAdd (wvec y.2.left, Multiplicative.toAdd y.1)) *
          w ^ (Multiplicative.toAdd y.2.right).val)
    have hv : (wvec (x.2 * y.2).left, Multiplicative.toAdd (x.1 * y.1)) =
        (wvec x.2.left, Multiplicative.toAdd x.1) +
          (⇑rot9)^[(Multiplicative.toAdd x.2.right).val]
            (wvec y.2.left, Multiplicative.toAdd y.1) := by
      rw [rot9_iterate, wvec_mul_left, toAdd_mul, Prod.mk_add_mk]
    rw [hv, RegularWreathProduct.mul_right, pow_val_mul hw3, ofAdd_add, map_mul]
    calc τ (.ofAdd (wvec x.2.left, Multiplicative.toAdd x.1)) *
          τ (.ofAdd ((⇑rot9)^[(Multiplicative.toAdd x.2.right).val]
            (wvec y.2.left, Multiplicative.toAdd y.1))) *
          (w ^ (Multiplicative.toAdd x.2.right).val * w ^ (Multiplicative.toAdd y.2.right).val)
        = τ (.ofAdd (wvec x.2.left, Multiplicative.toAdd x.1)) *
          (τ (.ofAdd ((⇑rot9)^[(Multiplicative.toAdd x.2.right).val]
            (wvec y.2.left, Multiplicative.toAdd y.1))) *
              w ^ (Multiplicative.toAdd x.2.right).val) *
            w ^ (Multiplicative.toAdd y.2.right).val := by simp only [mul_assoc]
      _ = _ := by rw [← pow_mul_tau hwτ]; simp only [mul_assoc]

theorem wreathHom9_apply (τ : Multiplicative ((Fin 3 → ZMod 9) × ZMod 9) →* X) (w : X)
    (hw3 : w ^ 3 = 1) (hwτ : ∀ v, w * τ (.ofAdd v) = τ (.ofAdd (rot9 v)) * w)
    (x : Multiplicative (ZMod 9) × (Multiplicative (ZMod 9) ≀ᵣ Multiplicative (ZMod 3))) :
    wreathHom9 τ w hw3 hwτ x = τ (.ofAdd (wvec x.2.left, Multiplicative.toAdd x.1)) *
      w ^ (Multiplicative.toAdd x.2.right).val := rfl

theorem wreathHom9_injective {τ : Multiplicative ((Fin 3 → ZMod 9) × ZMod 9) →* X}
    (hτ : Function.Injective τ) {w : X} (hw3 : w ^ 3 = 1)
    (hwτ : ∀ v, w * τ (.ofAdd v) = τ (.ofAdd (rot9 v)) * w)
    (hσ : ∃ v, rot9 v ≠ v) : Function.Injective (wreathHom9 τ w hw3 hwτ) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨hj, hv⟩ := eq_zero_of_tau_mul_pow_eq_one hτ hw3 hwτ hσ
    (ZMod.val_lt (Multiplicative.toAdd x.2.right)) hx
  rw [Prod.mk_eq_zero] at hv
  rw [ZMod.val_eq_zero] at hj
  refine Prod.ext (Multiplicative.toAdd.injective hv.2) (RegularWreathProduct.ext
    (wvec_eq_zero hv.1) (Multiplicative.toAdd.injective hj))

end Wreath

end CFSG.RankThree.PartTwo.KFacts.KS21
