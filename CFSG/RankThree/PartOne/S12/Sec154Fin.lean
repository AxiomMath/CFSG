module

public import CFSG.RankThree.PartOne.S12.Sec1322Fin
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import Mathlib.GroupTheory.Perm.Fin

public section

namespace CFSG.RankThree.PartOne.Sec154Fin

open Equiv Sec1322Fin

set_option maxRecDepth 100000

@[expose] def s4s : Perm (Fin 4) := swap 0 1

@[expose] def s4c : Perm (Fin 4) := finRotate 4

theorem closure_s4 : Subgroup.closure ({s4c, s4s} : Set (Perm (Fin 4))) = ⊤ := by
  have := Equiv.Perm.closure_cycle_adjacent_swap (σ := finRotate 4) isCycle_finRotate
    support_finRotate 0
  have h : swap (0 : Fin 4) (finRotate 4 0) = swap 0 1 := by decide
  rw [h] at this
  exact this

@[expose] def GoodPair4 (t d : Perm (Fin 4)) : Prop :=
  t * t = 1 ∧ d ^ 4 = 1 ∧ d ^ 2 ≠ 1 ∧ (t * d) ^ 3 = 1 ∧ t * d ≠ 1 ∧ t ≠ 1

instance (t d : Perm (Fin 4)) : Decidable (GoodPair4 t d) := by
  unfold GoodPair4
  infer_instance

theorem pairs_conj4 : ∀ t d : Perm (Fin 4), GoodPair4 t d →
    ∃ g : Perm (Fin 4), g * s4s * g⁻¹ = t ∧ g * s4c * g⁻¹ = d := by
  decide +kernel

theorem center4 : ∀ g : Perm (Fin 4), g * s4s = s4s * g → g * s4c = s4c * g → g = 1 := by
  decide +kernel

theorem good4 : GoodPair4 s4s s4c := by decide +kernel

theorem sym4_conj_surjective :
    Function.Surjective (MulAut.conj : Perm (Fin 4) →* MulAut (Perm (Fin 4))) := by
  intro φ
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := good4
  have hgood : GoodPair4 (φ s4s) (φ s4c) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← map_mul, h1, map_one]
    · rw [← map_pow, h2, map_one]
    · intro h
      exact h3 (φ.injective (by rw [map_pow, h, map_one]))
    · rw [← map_mul, ← map_pow, h4, map_one]
    · intro h
      exact h5 (φ.injective (by rw [map_mul, h, map_one]))
    · intro h
      exact h6 (φ.injective (h.trans (map_one φ).symm))
  obtain ⟨g, hgs, hgc⟩ := pairs_conj4 _ _ hgood
  refine ⟨g, ?_⟩
  have e : (MulAut.conj g).toMonoidHom = φ.toMonoidHom := by
    refine MonoidHom.eq_of_eqOn_dense closure_s4 ?_
    rintro x (rfl | rfl)
    · exact hgc
    · exact hgs
  exact MulEquiv.ext fun x => DFunLike.congr_fun e x

theorem sym4_center : ∀ σ : Perm (Fin 4), (∀ τ, σ * τ = τ * σ) → σ = 1 :=
  fun σ h => center4 σ (h _) (h _)

@[expose] def isKlein (σ : Perm (Fin 4)) : Prop := σ * σ = 1 ∧ (nfix σ = 0 ∨ σ = 1)

instance : DecidablePred isKlein := fun x => by unfold isKlein; infer_instance

theorem isKlein_one : isKlein 1 := by decide +kernel
theorem isKlein_mul : ∀ a b : Perm (Fin 4), isKlein a → isKlein b → isKlein (a * b) := by
  decide +kernel
theorem isKlein_inv : ∀ a : Perm (Fin 4), isKlein a → isKlein a⁻¹ := by decide +kernel
theorem isKlein_conj : ∀ n g : Perm (Fin 4), isKlein n → isKlein (g * n * g⁻¹) := by
  decide +kernel

@[expose] def klein4 : Subgroup (Perm (Fin 4)) where
  carrier := {x | isKlein x}
  one_mem' := isKlein_one
  mul_mem' := fun {a b} ha hb => isKlein_mul a b ha hb
  inv_mem' := fun {a} ha => isKlein_inv a ha

instance klein4_normal : klein4.Normal :=
  ⟨fun n hn g => isKlein_conj n g hn⟩

theorem klein_normal : klein.Normal :=
  ⟨fun n hn g => by
    have : ∀ n g : Gp, kleinP n → kleinP (g * n * g⁻¹) := by decide +kernel
    exact this n g hn⟩

theorem exists_order_three : ∀ σ : Perm (Fin 4), ¬ isKlein σ →
    ∃ ρ : Perm (Fin 4), (σ ^ 3 = 1 ∧ σ ≠ 1) ∨
      ((σ * (ρ * σ * ρ⁻¹)) ^ 3 = 1 ∧ σ * (ρ * σ * ρ⁻¹) ≠ 1) := by decide +kernel

theorem pCore_le_klein4 : CFSG.pCore 2 (Perm (Fin 4)) ≤ klein4 := by
  intro σ hσ
  by_contra hnot
  obtain ⟨ρ, h⟩ := exists_order_three σ hnot
  have hN : (CFSG.pCore 2 (Perm (Fin 4))).Normal := CFSG.pCore_normal
  have hpg := CFSG.pCore_isPGroup (p := 2) (G := Perm (Fin 4))
  have key : ∀ y ∈ CFSG.pCore 2 (Perm (Fin 4)), y ^ 3 = 1 → y = 1 := by
    intro y hy hy3
    obtain ⟨k, hk⟩ := hpg ⟨y, hy⟩
    have hk' : y ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have h1 : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one hy3
    have h2 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hcop : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num)
    have h3 := Nat.dvd_gcd h1 h2
    rw [hcop] at h3
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  rcases h with ⟨h3, h1⟩ | ⟨h3, h1⟩
  · exact h1 (key σ hσ h3)
  · refine h1 (key _ ?_ h3)
    exact (CFSG.pCore 2 _).mul_mem hσ (hN.conj_mem σ hσ ρ)

theorem pCore_eq_of_hom {H : Type*} [Group H] (π : H →* Perm (Fin 4))
    (hπ : Function.Surjective π) (K : Subgroup H) (hKn : K.Normal)
    (hK2 : ∀ x ∈ K, x * x = 1) (hK : ∀ x, x ∈ K ↔ π x ∈ klein4) :
    CFSG.pCore 2 H = K := by
  apply le_antisymm
  · intro x hx
    rw [hK]
    have hle : (CFSG.pCore 2 H).map π ≤ klein4 := by
      refine le_trans ?_ pCore_le_klein4
      refine le_sSup ⟨?_, ?_⟩
      · exact Subgroup.Normal.map CFSG.pCore_normal π hπ
      · exact IsPGroup.map CFSG.pCore_isPGroup π
    exact hle ⟨x, hx, rfl⟩
  · refine le_sSup ⟨hKn, ?_⟩
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    have := hK2 g g.2
    simpa [pow_two] using this

theorem pCore_gp : CFSG.pCore 2 Gp = klein := by
  refine pCore_eq_of_hom (MonoidHom.snd _ _) (fun σ => ⟨((1 : Multiplicative (ZMod 2)), σ), rfl⟩) klein klein_normal ?_ ?_
  · have : ∀ x : Gp, kleinP x → x * x = 1 := by decide +kernel
    exact fun x hx => this x hx
  · intro x
    exact Iff.rfl

theorem pCore_s4 : CFSG.pCore 2 (Perm (Fin 4)) = klein4 := by
  refine pCore_eq_of_hom (MonoidHom.id _) (fun σ => ⟨σ, rfl⟩) klein4 klein4_normal ?_ ?_
  · exact fun x hx => hx.1
  · intro x
    exact Iff.rfl

theorem isSwap_iff4 : ∀ σ : Perm (Fin 4), σ.IsSwap ↔ (σ * σ = 1 ∧ nfix σ = 2) := by
  unfold Perm.IsSwap
  decide +kernel

theorem swap_not_klein : ∀ σ : Perm (Fin 4), σ * σ = 1 → nfix σ = 2 → ¬ isKlein σ := by
  decide +kernel

@[expose] def signBit (σ : Perm (Fin 4)) : Multiplicative (ZMod 2) :=
  if Perm.sign σ = 1 then 1 else Multiplicative.ofAdd 1

theorem signBit_mul : ∀ a b : Perm (Fin 4), signBit (a * b) = signBit a * signBit b := by
  decide +kernel

theorem signBit_swap : ∀ τ : Perm (Fin 4), τ * τ = 1 → nfix τ = 2 →
    signBit τ = Multiplicative.ofAdd 1 := by decide +kernel

@[expose] def grHom : Perm (Fin 4) →* Gp where
  toFun σ := (signBit σ, σ)
  map_one' := by
    have : signBit 1 = 1 := by decide +kernel
    exact Prod.ext this rfl
  map_mul' a b := Prod.ext (signBit_mul a b) rfl

theorem grHom_injective : Function.Injective grHom :=
  fun _ _ h => congrArg Prod.snd h

theorem inr_injective : Function.Injective
    (MonoidHom.inr (Multiplicative (ZMod 2)) (Perm (Fin 4))) :=
  fun _ _ h => congrArg Prod.snd h

theorem swapClass_T {D : Set Gp} (h : ∀ x, x ∈ D ↔ isT x ∨ isV' x) :
    ∀ x : Gp, (x ∈ D ∧ x ∉ klein) ↔
      ∃ τ : Perm (Fin 4), τ.IsSwap ∧ (MonoidHom.inr _ _ : Perm (Fin 4) →* Gp) τ = x := by
  intro x
  rw [h x]
  constructor
  · rintro ⟨hx | hx, hnk⟩
    · refine ⟨x.2, (isSwap_iff4 x.2).2 ⟨hx.2.1, hx.2.2⟩, ?_⟩
      exact Prod.ext hx.1.symm rfl
    · exact absurd (kleinP_V' x hx) hnk
  · rintro ⟨τ, hτ, rfl⟩
    obtain ⟨h1, h2⟩ := (isSwap_iff4 τ).1 hτ
    refine ⟨Or.inl ⟨rfl, h1, h2⟩, ?_⟩
    intro hk
    exact swap_not_klein τ h1 h2 hk

theorem swapClass_T' {D : Set Gp} (h : ∀ x, x ∈ D ↔ isT' x ∨ isV' x) :
    ∀ x : Gp, (x ∈ D ∧ x ∉ klein) ↔ ∃ τ : Perm (Fin 4), τ.IsSwap ∧ grHom τ = x := by
  intro x
  rw [h x]
  constructor
  · rintro ⟨hx | hx, hnk⟩
    · refine ⟨x.2, (isSwap_iff4 x.2).2 ⟨hx.2.1, hx.2.2⟩, ?_⟩
      refine Prod.ext ?_ rfl
      show signBit x.2 = x.1
      rw [hx.1]
      exact signBit_swap x.2 hx.2.1 hx.2.2
    · exact absurd (kleinP_V' x hx) hnk
  · rintro ⟨τ, hτ, rfl⟩
    obtain ⟨h1, h2⟩ := (isSwap_iff4 τ).1 hτ
    refine ⟨Or.inl ⟨signBit_swap τ h1 h2, h1, h2⟩, ?_⟩
    intro hk
    exact swap_not_klein τ h1 h2 hk

theorem swapClass_gp {D : Set Gp}
    (h : (∀ x, x ∈ D ↔ isT x ∨ isV' x) ∨ (∀ x, x ∈ D ↔ isT' x ∨ isV' x)) :
    ∃ ψ : Perm (Fin 4) →* Gp, Function.Injective ψ ∧
      ∀ x : Gp, (x ∈ D ∧ x ∉ klein) ↔ ∃ τ : Perm (Fin 4), τ.IsSwap ∧ ψ τ = x := by
  rcases h with h | h
  · exact ⟨MonoidHom.inr _ _, inr_injective, swapClass_T h⟩
  · exact ⟨grHom, grHom_injective, swapClass_T' h⟩

theorem swapClass_s4 {D : Set (Perm (Fin 4))} (hconj : ∀ g x, x ∈ D → g * x * g⁻¹ ∈ D)
    (hinv : ∀ x ∈ D, x * x = 1 ∧ x ≠ 1) (hgen : Subgroup.closure D = ⊤) :
    ∃ ψ : Perm (Fin 4) →* Perm (Fin 4), Function.Injective ψ ∧
      ∀ x : Perm (Fin 4), (x ∈ D ∧ x ∉ klein4) ↔ ∃ τ : Perm (Fin 4), τ.IsSwap ∧ ψ τ = x := by
  have hinvol : ∀ x : Perm (Fin 4), x * x = 1 → x ≠ 1 → ¬ isKlein x → x.IsSwap := by
    intro x h1 h2 h3
    rw [isSwap_iff4]
    refine ⟨h1, ?_⟩
    revert x
    decide +kernel
  have hex : ∃ d ∈ D, d ∉ klein4 := by
    by_contra hcon
    push Not at hcon
    have hle : Subgroup.closure D ≤ klein4 := (Subgroup.closure_le _).2 hcon
    rw [hgen] at hle
    have : (Equiv.swap (0 : Fin 4) 1) ∈ klein4 := hle trivial
    exact swap_not_klein _ (by decide) (by decide) this
  refine ⟨MonoidHom.id _, fun a b h => h, fun x => ?_⟩
  have hiff : (∃ τ : Perm (Fin 4), τ.IsSwap ∧
      (MonoidHom.id (Perm (Fin 4)) : Perm (Fin 4) →* Perm (Fin 4)) τ = x) ↔ x.IsSwap :=
    ⟨fun ⟨τ, hτ, h⟩ => h ▸ hτ, fun h => ⟨x, h, rfl⟩⟩
  rw [hiff]
  constructor
  · rintro ⟨hx, hnk⟩
    exact hinvol x (hinv x hx).1 (hinv x hx).2 hnk
  · intro hx
    obtain ⟨d, hd, hdk⟩ := hex
    have hdswap : d.IsSwap := hinvol d (hinv d hd).1 (hinv d hd).2 hdk
    obtain ⟨a, b, hab, rfl⟩ := hdswap
    obtain ⟨c, e, hce, rfl⟩ := hx
    obtain ⟨γ, hγ⟩ := isConj_iff.1 (Equiv.Perm.isConj_swap hab hce)
    refine ⟨?_, ?_⟩
    · rw [← hγ]
      exact hconj γ _ hd
    · intro hk
      obtain ⟨h1, h2⟩ := (isSwap_iff4 _).1 ⟨c, e, hce, rfl⟩
      exact swap_not_klein _ h1 h2 hk

end CFSG.RankThree.PartOne.Sec154Fin
