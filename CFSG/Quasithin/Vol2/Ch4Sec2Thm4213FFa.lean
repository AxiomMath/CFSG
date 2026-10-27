module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213FFh
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213FFn

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.Ch4.FFa

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13.Ch4.FFh
open scoped Matrix

theorem isFFModule_alt_of_offender {m r s : ℕ} (hm : 2 ≤ m) (he : Even m) (i₀ : Fin m)
    (hr : 1 ≤ r) (φ : Multiplicative (Fin r → ZMod 2) →* Equiv.Perm (Fin m))
    (hφA : ∀ v, φ v ∈ alternatingGroup (Fin m))
    (hfaith : ∀ v : Multiplicative (Fin r → ZMod 2), v ≠ 1 → ∃ x : Fin m → ZMod 2,
      ∑ i, x i = 0 ∧ ¬ ∀ i, x ((φ v)⁻¹ i) + x i = x ((φ v)⁻¹ i₀) + x i₀)
    (C : Matrix (Fin m) (Fin s) (ZMod 2)) (hCw : ∀ w : Fin s → ZMod 2, ∑ i, (C *ᵥ w) i = 0)
    (hCinj : ∀ w : Fin s → ZMod 2, (∀ i, (C *ᵥ w) i = (C *ᵥ w) i₀) → w = 0)
    (hfix : ∀ (v : Multiplicative (Fin r → ZMod 2)) (w : Fin s → ZMod 2) (i : Fin m),
      (C *ᵥ w) ((φ v)⁻¹ i) + (C *ᵥ w) i = (C *ᵥ w) ((φ v)⁻¹ i₀) + (C *ᵥ w) i₀)
    (hcount : 2 ^ m ≤ 4 * (2 ^ r * 2 ^ s)) :
    IsFFModule (V := Multiplicative (AltHeart m))
      ((heartAut m).comp (alternatingGroup (Fin m)).subtype).range := by
  set χ := (heartAut m).comp φ with hχ
  have hinj : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro v hv
    by_contra hne
    obtain ⟨x, hx, hnot⟩ := hfaith v hne
    apply hnot
    have h1 := congrArg (fun g : MulAut (Multiplicative (AltHeart m)) =>
      g (Multiplicative.ofAdd (QuotientAddGroup.mk (⟨x, AddMonoidHom.mem_ker.mpr hx⟩ :
        ↥(evenWeight m))))) hv
    simp only [hχ, MonoidHom.comp_apply, MulAut.one_apply] at h1
    exact (FFh.heartAut_mk_eq_iff i₀ _ _).mp h1
  set X := χ.range with hX
  let ι : (Fin s → ZMod 2) → ↥(evenWeight m) := fun w =>
    ⟨C *ᵥ w, AddMonoidHom.mem_ker.mpr (hCw w)⟩
  let ψ : Multiplicative (Fin s → ZMod 2) →* Multiplicative (AltHeart m) :=
    { toFun := fun w => Multiplicative.ofAdd (QuotientAddGroup.mk (ι (Multiplicative.toAdd w)))
      map_one' := by
        show Multiplicative.ofAdd (QuotientAddGroup.mk (ι 0)) = 1
        have : ι 0 = 0 := Subtype.ext (Matrix.mulVec_zero C)
        rw [this, QuotientAddGroup.mk_zero]
        rfl
      map_mul' := fun w w' => by
        show Multiplicative.ofAdd (QuotientAddGroup.mk
          (ι (Multiplicative.toAdd w + Multiplicative.toAdd w'))) = _
        have : ι (Multiplicative.toAdd w + Multiplicative.toAdd w') =
            ι (Multiplicative.toAdd w) + ι (Multiplicative.toAdd w') :=
          Subtype.ext (Matrix.mulVec_add C _ _)
        rw [this, QuotientAddGroup.mk_add]
        rfl }
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have h1 : (QuotientAddGroup.mk (ι (Multiplicative.toAdd w)) : AltHeart m) =
        QuotientAddGroup.mk (0 : ↥(evenWeight m)) := by
      rw [QuotientAddGroup.mk_zero]
      exact congrArg Multiplicative.toAdd hw
    rw [FFh.mk_eq_mk_iff i₀] at h1
    have h2 := hCinj (Multiplicative.toAdd w) fun i => by simpa [ι] using h1 i
    exact Multiplicative.toAdd.injective h2
  have hfixX : ψ.range ≤ fixV X := by
    rintro _ ⟨w, rfl⟩
    rw [mem_fixV]
    rintro _ ⟨v, rfl⟩
    exact (FFh.heartAut_mk_eq_iff i₀ _ _).mpr fun i => hfix v (Multiplicative.toAdd w) i
  refine ⟨X, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨v, rfl⟩
    exact ⟨⟨φ v, hφA v⟩, rfl⟩
  · intro hbot
    have hv : (Multiplicative.ofAdd (Pi.single ⟨0, hr⟩ 1) :
        Multiplicative (Fin r → ZMod 2)) ≠ 1 := by
      intro h
      have := congrFun (congrArg Multiplicative.toAdd h) ⟨0, hr⟩
      simp at this
    apply hv
    apply hinj
    have hmem : χ (Multiplicative.ofAdd (Pi.single ⟨0, hr⟩ 1)) ∈ X := ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    rw [hmem, map_one]
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ 2 = 1 := by
      apply Multiplicative.toAdd.injective
      funext j
      simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul,
        Nat.cast_ofNat]
      exact (show ∀ c : ZMod 2, 2 * c = 0 by decide) _
    rw [this, map_one]
  · have hcX : Nat.card X = 2 ^ r := by
      rw [hX, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top]
      show Nat.card (Fin r → ZMod 2) = _
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin r), Fintype.card_fin]
    have hcψ : Nat.card ψ.range = 2 ^ s := by
      rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hψinj, Subgroup.card_top]
      show Nat.card (Fin s → ZMod 2) = _
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin s), Fintype.card_fin]
    have hle : Nat.card ψ.range ≤ Nat.card (fixV X) := Subgroup.card_le_of_le hfixX
    have hH := card_altHeart hm he
    have hH' : Nat.card (Multiplicative (AltHeart m)) = Nat.card (AltHeart m) := rfl
    rw [hH', hcX]
    have h4 : Nat.card (AltHeart m) ≤ 2 ^ r * 2 ^ s := by omega
    calc Nat.card (AltHeart m) ≤ 2 ^ r * 2 ^ s := h4
      _ = 2 ^ r * Nat.card ψ.range := by rw [hcψ]
      _ ≤ 2 ^ r * Nat.card (fixV X) := Nat.mul_le_mul_left _ hle

@[expose] def a6 : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 2 3

@[expose] def b6 : Equiv.Perm (Fin 6) := Equiv.swap 2 3 * Equiv.swap 4 5

@[expose] def k6 : Multiplicative (Fin 2 → ZMod 2) →* Equiv.Perm (Fin 6) where
  toFun v := a6 ^ (Multiplicative.toAdd v 0).val * b6 ^ (Multiplicative.toAdd v 1).val
  map_one' := by decide
  map_mul' := by decide +kernel

theorem k6_mem (v : Multiplicative (Fin 2 → ZMod 2)) : k6 v ∈ alternatingGroup (Fin 6) := by
  have ha : a6 ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup, a6, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
    decide
  have hb : b6 ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup, b6, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
    decide
  exact (alternatingGroup (Fin 6)).mul_mem ((alternatingGroup (Fin 6)).pow_mem ha _)
    ((alternatingGroup (Fin 6)).pow_mem hb _)

@[expose] def c6 : Matrix (Fin 6) (Fin 2) (ZMod 2) := !![1, 0; 1, 0; 0, 1; 0, 1; 0, 0; 0, 0]

theorem isFFModule_heart6 :
    IsFFModule (V := Multiplicative (AltHeart 6))
      ((heartAut 6).comp (alternatingGroup (Fin 6)).subtype).range :=
  isFFModule_alt_of_offender (r := 2) (s := 2) (by norm_num) (by decide) 0 (by norm_num) k6 k6_mem
    (by decide +kernel) c6 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num)

@[expose] def t81 : Equiv.Perm (Fin 8) :=
  Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5 * Equiv.swap 6 7

@[expose] def t82 : Equiv.Perm (Fin 8) :=
  Equiv.swap 0 2 * Equiv.swap 1 3 * Equiv.swap 4 6 * Equiv.swap 5 7

@[expose] def t84 : Equiv.Perm (Fin 8) :=
  Equiv.swap 0 4 * Equiv.swap 1 5 * Equiv.swap 2 6 * Equiv.swap 3 7

@[expose] def k8 : Multiplicative (Fin 3 → ZMod 2) →* Equiv.Perm (Fin 8) where
  toFun v := t81 ^ (Multiplicative.toAdd v 0).val * t82 ^ (Multiplicative.toAdd v 1).val *
    t84 ^ (Multiplicative.toAdd v 2).val
  map_one' := by decide
  map_mul' := by decide +kernel

theorem t8_mem {a b c d e f g h : Fin 8} (hab : a ≠ b) (hcd : c ≠ d) (hef : e ≠ f)
    (hgh : g ≠ h) :
    Equiv.swap a b * Equiv.swap c d * Equiv.swap e f * Equiv.swap g h ∈
      alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab, Equiv.Perm.sign_swap hcd,
    Equiv.Perm.sign_swap hef, Equiv.Perm.sign_swap hgh]
  decide

theorem k8_mem (v : Multiplicative (Fin 3 → ZMod 2)) : k8 v ∈ alternatingGroup (Fin 8) := by
  have h1 : t81 ∈ alternatingGroup (Fin 8) := t8_mem (by decide) (by decide) (by decide) (by decide)
  have h2 : t82 ∈ alternatingGroup (Fin 8) := t8_mem (by decide) (by decide) (by decide) (by decide)
  have h4 : t84 ∈ alternatingGroup (Fin 8) := t8_mem (by decide) (by decide) (by decide) (by decide)
  exact (alternatingGroup (Fin 8)).mul_mem
    ((alternatingGroup (Fin 8)).mul_mem ((alternatingGroup (Fin 8)).pow_mem h1 _)
      ((alternatingGroup (Fin 8)).pow_mem h2 _)) ((alternatingGroup (Fin 8)).pow_mem h4 _)

@[expose] def c8 : Matrix (Fin 8) (Fin 3) (ZMod 2) :=
  !![0, 0, 0; 1, 0, 0; 0, 1, 0; 1, 1, 0; 0, 0, 1; 1, 0, 1; 0, 1, 1; 1, 1, 1]

theorem isFFModule_heart8 :
    IsFFModule (V := Multiplicative (AltHeart 8))
      ((heartAut 8).comp (alternatingGroup (Fin 8)).subtype).range :=
  isFFModule_alt_of_offender (r := 3) (s := 3) (by norm_num) (by decide) 0 (by norm_num) k8 k8_mem
    (by decide +kernel) c8 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num)

section Transport

variable {G : Type} [Group G]

open scoped IsMulCommutative in
theorem isFFModule_autOn_of_altNatural {A V : Subgroup G} [IsMulCommutative ↥V]
    {N : Subgroup ↥A} {m : ℕ} (h : IsAltNaturalSection A V ⊥ N m)
    (hFF : IsFFModule (V := Multiplicative (AltHeart m))
      ((heartAut m).comp (alternatingGroup (Fin m)).subtype).range) :
    IsFFModule (autOn A V) := by
  obtain ⟨hAV, α, hα, -, β, hβ, hβker, hβeq⟩ := h
  have hinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβker, Subgroup.bot_subgroupOf]
  refine FFn.isFFModule_autOn_of_equiv hAV ((heartAut m).comp (alternatingGroup (Fin m)).subtype)
    α hα (MulEquiv.ofBijective β ⟨hinj, hβ⟩) (fun a w w' hw' => ?_) hFF
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (β w))
  have h1 := hβeq a w w' hw' x hx
  show β w' = heartAut m (α a : Equiv.Perm (Fin m)) (β w)
  rw [heartAut_apply, ← hx, hAct_mk, h1]
  rfl

open scoped IsMulCommutative in
theorem isFFModule_autOn_of_altBlock {L V : Subgroup G} [IsMulCommutative ↥V]
    (hL : IsAltBlockType L 6) (hVU : V ≤ blockU L) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hV1 : V ≠ ⊥) (hVZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    IsFFModule (autOn L V) := by
  obtain ⟨-, α, hα, -, β, hβ, hβker, hβeq⟩ := hL
  set βV : ↥V →* Multiplicative (AltHeart 6) := β.comp (Subgroup.inclusion hVU) with hβV
  have hinj : Function.Injective βV := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have hk : Subgroup.inclusion hVU v ∈ β.ker := hv
    rw [hβker, Subgroup.mem_subgroupOf] at hk
    have hvC : (v : G) ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨v.2, hk.2⟩
    rw [hVZ, Subgroup.mem_bot] at hvC
    exact Subtype.ext hvC
  let X : AddSubgroup (AltHeart 6) :=
    { carrier := {y | ∃ v : ↥V, βV v = Multiplicative.ofAdd y}
      add_mem' := fun {a b} ⟨v, hv⟩ ⟨w, hw⟩ => ⟨v * w, by rw [map_mul, hv, hw]; rfl⟩
      zero_mem' := ⟨1, by rw [map_one]; rfl⟩
      neg_mem' := fun {a} ⟨v, hv⟩ => ⟨v⁻¹, by rw [map_inv, hv]; rfl⟩ }
  have hmemX : ∀ y : AltHeart 6, y ∈ X ↔ ∃ v : ↥V, βV v = Multiplicative.ofAdd y :=
    fun _ => Iff.rfl
  have hXinv : ∀ σ : alternatingGroup (Fin 6), ∀ x : ↥(evenWeight 6),
      (QuotientAddGroup.mk x : AltHeart 6) ∈ X →
        (QuotientAddGroup.mk (permWeight 6 (σ : Equiv.Perm (Fin 6)) x) : AltHeart 6) ∈ X := by
    intro σ x hx
    obtain ⟨v, hv⟩ := (hmemX _).mp hx
    obtain ⟨ℓ, rfl⟩ := hα σ
    have hw : (ℓ : G) * v * (ℓ : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hLV ℓ.2) v).mp v.2
    refine (hmemX _).mpr ⟨⟨_, hw⟩, ?_⟩
    have h1 := hβeq ℓ (Subgroup.inclusion hVU v) (Subgroup.inclusion hVU ⟨_, hw⟩) rfl x
      (by rw [show β (Subgroup.inclusion hVU v) = βV v from rfl, hv]; rfl)
    show β (Subgroup.inclusion hVU ⟨_, hw⟩) = _
    rw [h1]
    rfl
  have hsurj : Function.Surjective βV := by
    rcases FFh.heart6_eq_bot_or_top X hXinv with hbot | htop
    · exfalso
      obtain ⟨v, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hV1
      apply hv1
      apply hinj
      have hmem : Multiplicative.toAdd (βV v) ∈ X := (hmemX _).mpr ⟨v, rfl⟩
      rw [hbot, AddSubgroup.mem_bot] at hmem
      rw [map_one]
      exact hmem
    · intro y
      have hmem : Multiplicative.toAdd y ∈ X := by
        rw [htop]
        exact AddSubgroup.mem_top _
      obtain ⟨v, hv⟩ := (hmemX _).mp hmem
      exact ⟨v, hv⟩
  refine FFn.isFFModule_autOn_of_equiv hLV ((heartAut 6).comp (alternatingGroup (Fin 6)).subtype)
    α hα (MulEquiv.ofBijective βV ⟨hinj, hsurj⟩) (fun a w w' hw' => ?_) isFFModule_heart6
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (βV w))
  have h1 := hβeq a (Subgroup.inclusion hVU w) (Subgroup.inclusion hVU w') hw' x hx
  show βV w' = heartAut 6 (α a : Equiv.Perm (Fin 6)) (βV w)
  rw [heartAut_apply, ← hx, hAct_mk, h1]
  rfl

end Transport

end CFSG.Quasithin.H13.Ch4.FFa
