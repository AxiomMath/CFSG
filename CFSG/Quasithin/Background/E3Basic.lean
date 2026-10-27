module

public import CFSG.Quasithin.Background.FixVTransport
public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.Quasithin

namespace E3

open CFSG.Open
open scoped commutatorElement

universe u

section Conj

variable {G : Type*} [Group G]

theorem mem_conjSubgroup_inv_iff {A : Subgroup G} {g x : G} :
    x ∈ conjSubgroup A g⁻¹ ↔ g⁻¹ * x * g ∈ A := by
  rw [mem_conjSubgroup_iff]
  simp

theorem conjSubgroup_conj_inv (A : Subgroup G) (g : G) :
    conjSubgroup (conjSubgroup A g) g⁻¹ = A := by
  rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]

theorem conjSubgroup_inv_conj (A : Subgroup G) (g : G) :
    conjSubgroup (conjSubgroup A g⁻¹) g = A := by
  have := conjSubgroup_conj_inv A g⁻¹
  rwa [inv_inv] at this

theorem conjSubgroup_mono_left {A B : Subgroup G} (g : G) (h : A ≤ B) :
    conjSubgroup A g ≤ conjSubgroup B g := fun x hx => by
  rw [mem_conjSubgroup_iff] at hx ⊢
  exact h hx

theorem conjSubgroup_le_conjSubgroup_iff {A B : Subgroup G} (g : G) :
    conjSubgroup A g ≤ conjSubgroup B g ↔ A ≤ B := by
  refine ⟨fun h => ?_, conjSubgroup_mono_left g⟩
  have := conjSubgroup_mono_left g⁻¹ h
  rwa [conjSubgroup_conj_inv, conjSubgroup_conj_inv] at this

theorem conjSubgroup_inf (A B : Subgroup G) (g : G) :
    conjSubgroup (A ⊓ B) g = conjSubgroup A g ⊓ conjSubgroup B g := by
  ext x
  simp [mem_conjSubgroup_iff, Subgroup.mem_inf]

theorem conjSubgroup_bot (g : G) : conjSubgroup (⊥ : Subgroup G) g = ⊥ := by
  ext x
  simp [mem_conjSubgroup_iff]

theorem conjSubgroup_top (g : G) : conjSubgroup (⊤ : Subgroup G) g = ⊤ := by
  ext x
  simp [mem_conjSubgroup_iff]

theorem conjSubgroup_centralizer (A : Subgroup G) (g : G) :
    conjSubgroup (Subgroup.centralizer (A : Set G)) g =
      Subgroup.centralizer (conjSubgroup A g : Set G) := by
  ext x
  simp only [mem_conjSubgroup_iff, Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · intro h y hy
    have h1 := h _ hy
    have h2 : g * (y * x) * g⁻¹ = g * (x * y) * g⁻¹ := by
      calc g * (y * x) * g⁻¹ = (g * y * g⁻¹) * (g * x * g⁻¹) := by group
        _ = (g * x * g⁻¹) * (g * y * g⁻¹) := h1
        _ = g * (x * y) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  · intro h a ha
    have e1 : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
    have h1 := h (g⁻¹ * a * g) (by rw [e1]; exact ha)
    have h2 : g * (g⁻¹ * a * g * x) * g⁻¹ = g * (x * (g⁻¹ * a * g)) * g⁻¹ := by rw [h1]
    calc a * (g * x * g⁻¹) = g * (g⁻¹ * a * g * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * a * g)) * g⁻¹ := h2
      _ = (g * x * g⁻¹) * a := by group

theorem conjSubgroup_normalizer (A : Subgroup G) (g : G) :
    conjSubgroup (Subgroup.normalizer (A : Set G)) g =
      Subgroup.normalizer (conjSubgroup A g : Set G) := by
  ext x
  simp only [mem_conjSubgroup_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    have h1 := h (g * y * g⁻¹)
    have e1 : g * (x * y * x⁻¹) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ := by
      group
    rw [e1]
    exact h1
  · intro h a
    have h1 := h (g⁻¹ * a * g)
    have e1 : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
    have e2 : g * (x * (g⁻¹ * a * g) * x⁻¹) * g⁻¹ = (g * x * g⁻¹) * a * (g * x * g⁻¹)⁻¹ := by
      group
    rw [e1, e2] at h1
    exact h1

theorem conjSubgroup_commutator (A B : Subgroup G) (g : G) :
    conjSubgroup ⁅A, B⁆ g = ⁅conjSubgroup A g, conjSubgroup B g⁆ := by
  unfold conjSubgroup
  exact Subgroup.map_commutator A B _

theorem card_conjSubgroup (A : Subgroup G) (g : G) :
    Nat.card (conjSubgroup A g) = Nat.card A :=
  Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj g⁻¹))

theorem relIndex_conjSubgroup (A B : Subgroup G) (g : G) :
    (conjSubgroup A g).relIndex (conjSubgroup B g) = A.relIndex B :=
  Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom) A B
    (MulEquiv.injective (MulAut.conj g⁻¹))

theorem mQuot_conjSubgroup (V U : Subgroup G) (g : G) :
    mQuot (conjSubgroup V g) (conjSubgroup U g) = mQuot V U := by
  unfold mQuot
  rw [relIndex_conjSubgroup]

theorem isPGroup_conjSubgroup {p : ℕ} {A : Subgroup G} (hA : IsPGroup p A) (g : G) :
    IsPGroup p (conjSubgroup A g) := by
  have := hA.map (MulAut.conj g⁻¹).toMonoidHom
  exact this

theorem isElemAbelian_conjSubgroup {A : Subgroup G} (hA : IsElemAbelian 2 A) (g : G) :
    IsElemAbelian 2 (conjSubgroup A g) := by
  have hc := hA.1
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · have hx := mem_conjSubgroup_iff.1 x.2
    have hy := mem_conjSubgroup_iff.1 y.2
    apply Subtype.ext
    have h := B2F.isElemAbelian_comm hA hx hy
    have h2 : g⁻¹ * (g * x * g⁻¹ * (g * y * g⁻¹)) * g = g⁻¹ * (g * y * g⁻¹ * (g * x * g⁻¹)) * g := by
      rw [h]
    simpa [mul_assoc] using h2
  · have h := hA.2 _ (mem_conjSubgroup_iff.1 hx)
    have h2 : (g * x * g⁻¹) ^ 2 = g * x ^ 2 * g⁻¹ := by simp [pow_two, mul_assoc]
    rw [h2] at h
    have h3 : x ^ 2 = g⁻¹ * (g * x ^ 2 * g⁻¹) * g := by simp [mul_assoc]
    rw [h3, h]
    simp

end Conj

section RParam

variable {G : Type*} [Group G]

theorem rParam_conj_le (V : Subgroup G) (g : G) [Finite G] :
    rParam (conjSubgroup V g) ≤ rParam V := by
  refine le_iInf₂ fun U hU => ?_
  obtain ⟨hUV, hnc⟩ := hU
  refine (iInf₂_le (conjSubgroup U g) ⟨(conjSubgroup_le_conjSubgroup_iff g).2 hUV, ?_⟩).trans
    (le_of_eq ?_)
  · rw [mQuot_conjSubgroup]
  · intro h
    apply hnc
    rw [← conjSubgroup_le_conjSubgroup_iff g, conjSubgroup_centralizer, conjSubgroup_normalizer]
    exact h

theorem rParam_conj (V : Subgroup G) (g : G) [Finite G] :
    rParam (conjSubgroup V g) = rParam V := by
  refine le_antisymm (rParam_conj_le V g) ?_
  have := rParam_conj_le (conjSubgroup V g) g⁻¹
  rwa [conjSubgroup_conj_inv] at this

theorem rParam_le_mQuot {V U : Subgroup G} (hUV : U ≤ V)
    (hC : ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G)) :
    rParam V ≤ mQuot V U :=
  iInf₂_le U ⟨hUV, hC⟩

variable [Finite G]

theorem e3_4_one {V B : Subgroup G} {g : G}
    (hB : B ≤ conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))
    (hC : ¬ V ⊓ Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer (conjSubgroup V g : Set G)) :
    rParam V ≤ mQuot (conjSubgroup V g) B := by
  rw [← rParam_conj V g]
  refine rParam_le_mQuot (hB.trans inf_le_left) fun h => hC ?_
  exact inf_le_right.trans h

theorem e3_4_two {V : Subgroup G} {g : G}
    (h : ¬ V ≤ Subgroup.normalizer (conjSubgroup V g : Set G)) :
    rParam V ≤ mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ Subgroup.centralizer (V : Set G)) := by
  refine e3_4_one (g := g) ?_ ?_
  · exact inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _)
  · intro hle
    apply h
    refine le_trans (fun v hv => ?_) hle
    refine Subgroup.mem_inf.2 ⟨hv, Subgroup.mem_centralizer_iff.2 fun b hb => ?_⟩
    exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hb).2 v hv).symm

end RParam

section ModuleLemmas

variable {W : Type*} [CommGroup W]

theorem exists_orderOf_two_of_isPGroup {M : Type*} [Group M] [Finite M] {A : Subgroup M}
    (hA : IsPGroup 2 A) (h1 : A ≠ ⊥) : ∃ t ∈ A, orderOf t = 2 := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hA
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply h1
    rw [Subgroup.eq_bot_iff_card]
    simpa using hn
  have h2 : 2 ∣ Nat.card A := by rw [hn]; exact dvd_pow_self 2 hn0
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 h2
  exact ⟨x.1, x.2, (Subgroup.orderOf_coe x).trans hx⟩

theorem isPGroup_of_isElemAbelian2 {A : Subgroup (MulAut W)} (hA : IsElemAbelian2 A) :
    IsPGroup 2 A := fun x => ⟨1, by
  apply Subtype.ext
  simpa using hA.2 x x.2⟩

theorem even_card_of_isPGroup [Finite W] {X A : Subgroup (MulAut W)} (hAX : A ≤ X)
    (hA : IsPGroup 2 A) (hA1 : A ≠ ⊥) : Even (Nat.card X) := by
  obtain ⟨t, htA, hto⟩ := exists_orderOf_two_of_isPGroup hA hA1
  have h : orderOf (⟨t, hAX htA⟩ : X) ∣ Nat.card X := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hto] at h
  exact even_iff_two_dvd.2 h

theorem mParam_le_rkIdx_fixV [Finite W] {X A : Subgroup (MulAut W)} (hAX : A ≤ X)
    (hA : IsPGroup 2 A) (hA1 : A ≠ ⊥) : mParam X ≤ rkIdx (fixV A) := by
  obtain ⟨t, htA, hto⟩ := exists_orderOf_two_of_isPGroup hA hA1
  have hev := even_card_of_isPGroup hAX hA hA1
  have hmem : rkIdx (fixV (Subgroup.zpowers t)) ∈ {n : ℕ | ∃ t ∈ X, orderOf t = 2 ∧
      n = rkIdx (fixV (Subgroup.zpowers t))} := ⟨t, hAX htA, hto, rfl⟩
  simp only [mParam, hev, ↓reduceIte]
  refine (Nat.sInf_le hmem).trans ?_
  refine rkIdx_anti fun v hv x hx => hv x ?_
  exact (Subgroup.zpowers_le.2 htA) hx

theorem e3_2 [Finite W] {X A : Subgroup (MulAut W)} (hAX : A ≤ X) (hA : IsElemAbelian2 A)
    (hA1 : A ≠ ⊥) : mParam X ≤ rkIdx (fixV A) :=
  mParam_le_rkIdx_fixV hAX (isPGroup_of_isElemAbelian2 hA) hA1

end ModuleLemmas

theorem rkIdx_map_equiv {W₁ W₂ : Type*} [Group W₁] [Group W₂] (φ : W₁ ≃* W₂) (S : Subgroup W₁) :
    rkIdx (S.map φ.toMonoidHom) = rkIdx S :=
  congrArg (padicValNat 2) (Subgroup.index_map_equiv S φ)

section ModuleLemmas

variable {W : Type*} [CommGroup W]

theorem fixV_map_congr {W' : Type*} [CommGroup W'] (φ : W ≃* W') (X : Subgroup (MulAut W)) :
    fixV (X.map (MulAut.congr φ).toMonoidHom) = (fixV X).map φ.toMonoidHom :=
  fixV_map_congr_equiv φ X

theorem mParam_map_congr {W' : Type*} [CommGroup W'] (φ : W ≃* W') (X : Subgroup (MulAut W)) :
    mParam (X.map (MulAut.congr φ).toMonoidHom) = mParam X := by
  have hcard : Nat.card ↥(X.map (MulAut.congr φ).toMonoidHom) = Nat.card X :=
    Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.congr φ))
  have hrk : rk W' = rk W := by
    unfold rk
    rw [Nat.card_congr φ.toEquiv.symm]
  have hset : {n : ℕ | ∃ t ∈ X.map (MulAut.congr φ).toMonoidHom, orderOf t = 2 ∧
        n = rkIdx (fixV (Subgroup.zpowers t))} =
      {n : ℕ | ∃ t ∈ X, orderOf t = 2 ∧ n = rkIdx (fixV (Subgroup.zpowers t))} := by
    ext n
    constructor
    · rintro ⟨t', ⟨t, ht, rfl⟩, ho, rfl⟩
      refine ⟨t, ht, ?_, ?_⟩
      · rwa [orderOf_injective (MulAut.congr φ).toMonoidHom
          (MulEquiv.injective (MulAut.congr φ)) t] at ho
      · rw [← MonoidHom.map_zpowers, fixV_map_congr, rkIdx_map_equiv]
    · rintro ⟨t, ht, ho, rfl⟩
      refine ⟨(MulAut.congr φ).toMonoidHom t, ⟨t, ht, rfl⟩, ?_, ?_⟩
      · rwa [orderOf_injective (MulAut.congr φ).toMonoidHom
          (MulEquiv.injective (MulAut.congr φ)) t]
      · rw [← MonoidHom.map_zpowers, fixV_map_congr, rkIdx_map_equiv]
  unfold mParam
  rw [hcard, hrk, hset]

theorem aSet_mono {k : ℕ} {X X' : Subgroup (MulAut W)} (h : X ≤ X') : aSet k X ⊆ aSet k X' :=
  fun _ hA => ⟨hA.1.trans h, hA.2⟩

theorem aSet_anti {k l : ℕ} (h : l ≤ k) (X : Subgroup (MulAut W)) : aSet k X ⊆ aSet l X :=
  fun _ hA => ⟨hA.1, hA.2.1, hA.2.2.1, fun B hB hm => hA.2.2.2 B hB (lt_of_lt_of_le hm h)⟩

theorem aSet_one [Finite W] (X : Subgroup (MulAut W)) :
    aSet 1 X = {A | A ≤ X ∧ A ≠ ⊥ ∧ IsElemAbelian2 A} := by
  ext A
  constructor
  · rintro ⟨h1, h2, h3, -⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, h3, fun B hB hm => ?_⟩
    have hm0 : mQuot A B = 0 := by omega
    rw [(mQuot_eq_zero_iff (isPGroup_of_isElemAbelian2 h3) hB).1 hm0]

theorem le_mQuot_bot_of_mem_aSet [Finite W] {k : ℕ} {X A : Subgroup (MulAut W)}
    (hA : A ∈ aSet k X) : k ≤ mQuot A ⊥ := by
  by_contra hlt
  push Not at hlt
  have h := hA.2.2.2 ⊥ bot_le hlt
  apply hA.2.1
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  ext v
  have hv : v ∈ fixV (⊥ : Subgroup (MulAut W)) := fun x hx => by
    rw [Subgroup.mem_bot.1 hx]
    rfl
  rw [h] at hv
  simpa using hv a ha

theorem aSet_bddAbove [Finite W] (X : Subgroup (MulAut W)) :
    BddAbove {k : ℕ | 0 < k ∧ (aSet k X).Nonempty} := by
  refine ⟨Nat.card X, ?_⟩
  rintro k ⟨-, A, hA⟩
  have h1 := le_mQuot_bot_of_mem_aSet hA
  have h2 : mQuot A ⊥ ≤ Nat.card A := by
    unfold mQuot
    rw [Subgroup.relIndex_bot_left]
    exact Nat.padicValNat_le_self _
  have h3 : Nat.card A ≤ Nat.card X := Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hA.1)
  omega

theorem le_aParam_of_mem_aSet [Finite W] {k : ℕ} {X A : Subgroup (MulAut W)}
    (hk : 0 < k) (hA : A ∈ aSet k X) : k ≤ aParam X := by
  have hev := even_card_of_isPGroup hA.1 (isPGroup_of_isElemAbelian2 hA.2.2.1) hA.2.1
  simp only [aParam, hev, ↓reduceIte]
  exact le_csSup (aSet_bddAbove X) ⟨hk, A, hA⟩

theorem aParam_of_odd {X : Subgroup (MulAut W)} (h : ¬ Even (Nat.card X)) : aParam X = 0 := by
  simp [aParam, h]

theorem aParam_mono [Finite W] {X X' : Subgroup (MulAut W)} (h : X ≤ X') :
    aParam X ≤ aParam X' := by
  by_cases hev : Even (Nat.card X)
  · have hev' : Even (Nat.card X') :=
      even_iff_two_dvd.2 ((even_iff_two_dvd.1 hev).trans (Subgroup.card_dvd_of_le h))
    simp only [aParam, hev, hev', ↓reduceIte]
    by_cases hne : {k : ℕ | 0 < k ∧ (aSet k X).Nonempty}.Nonempty
    · refine csSup_le_csSup (aSet_bddAbove X') hne fun k hk => ?_
      obtain ⟨A, hA⟩ := hk.2
      exact ⟨hk.1, A, aSet_mono h hA⟩
    · rw [Set.not_nonempty_iff_eq_empty.1 hne, csSup_empty]
      exact Nat.zero_le _
  · rw [aParam_of_odd hev]
    exact Nat.zero_le _

end ModuleLemmas

section ConjMod

variable {G : Type u} [Group G] {V : Subgroup G}

@[expose] def conjMod (hV : IsElemAbelian 2 V) (g : G)
    (hVg : IsElemAbelian 2 (conjSubgroup V g)) :
    IntMod V hV ≃* IntMod (conjSubgroup V g) hVg where
  toFun v := IntMod.mk hVg ⟨g⁻¹ * v.val * g, by
    have e : g * (g⁻¹ * v.val * g) * g⁻¹ = v.val := by group
    rw [mem_conjSubgroup_iff, e]
    exact v.val_mem⟩
  invFun w := IntMod.mk hV ⟨g * w.val * g⁻¹, mem_conjSubgroup_iff.1 w.val_mem⟩
  left_inv v := by
    apply IntMod.val_injective
    show g * (g⁻¹ * v.val * g) * g⁻¹ = v.val
    group
  right_inv w := by
    apply IntMod.val_injective
    show g⁻¹ * (g * w.val * g⁻¹) * g = w.val
    group
  map_mul' a b := by
    apply IntMod.val_injective
    show g⁻¹ * (a.val * b.val) * g = (g⁻¹ * a.val * g) * (g⁻¹ * b.val * g)
    group

theorem congr_conjMod_convI (hV : IsElemAbelian 2 V) (g : G)
    (hVg : IsElemAbelian 2 (conjSubgroup V g)) {m n : G} (hm : m ∈ Subgroup.normalizer (V : Set G))
    (hn : n ∈ Subgroup.normalizer (conjSubgroup V g : Set G)) (h : n = g⁻¹ * m * g) :
    MulAut.congr (conjMod hV g hVg) (convI hV ⟨m, hm⟩) = convI hVg ⟨n, hn⟩ := by
  subst h
  ext w
  apply IntMod.val_injective
  have h1 := convI_apply_val hV ⟨m, hm⟩ ((conjMod hV g hVg).symm w)
  have h2 := convI_apply_val hVg ⟨g⁻¹ * m * g, hn⟩ w
  rw [MulAut.congr_apply]
  show g⁻¹ * (convI hV ⟨m, hm⟩ ((conjMod hV g hVg).symm w)).val * g = _
  rw [h1, h2]
  show g⁻¹ * (m * (g * w.val * g⁻¹) * m⁻¹) * g = g⁻¹ * m * g * w.val * (g⁻¹ * m * g)⁻¹
  group

theorem autI_top_conj [Finite G] (hV : IsElemAbelian 2 V) (g : G)
    (hVg : IsElemAbelian 2 (conjSubgroup V g)) :
    autI hVg ⊤ = (autI hV ⊤).map (MulAut.congr (conjMod hV g hVg)).toMonoidHom := by
  ext ψ
  rw [Subgroup.mem_map]
  constructor
  · intro hψ
    obtain ⟨n, -, rfl⟩ := (mem_autI hVg).1 hψ
    have hn : g * (n : G) * g⁻¹ ∈ Subgroup.normalizer (V : Set G) := by
      have h : (n : G) ∈ conjSubgroup (Subgroup.normalizer (V : Set G)) g := by
        rw [conjSubgroup_normalizer]
        exact n.2
      exact mem_conjSubgroup_iff.1 h
    refine ⟨convI hV ⟨g * (n : G) * g⁻¹, hn⟩, convI_mem_autI hV (Subgroup.mem_top _) hn, ?_⟩
    exact congr_conjMod_convI hV g hVg hn n.2 (by group)
  · rintro ⟨χ, hχ, rfl⟩
    obtain ⟨m, -, rfl⟩ := (mem_autI hV).1 hχ
    have hn : g⁻¹ * (m : G) * g ∈ Subgroup.normalizer (conjSubgroup V g : Set G) := by
      rw [← conjSubgroup_normalizer, mem_conjSubgroup_iff]
      have e : g * (g⁻¹ * (m : G) * g) * g⁻¹ = m := by group
      rw [e]
      exact m.2
    refine (mem_autI hVg).2 ⟨⟨g⁻¹ * (m : G) * g, hn⟩, Subgroup.mem_top _, ?_⟩
    exact (congr_conjMod_convI hV g hVg m.2 hn rfl).symm

theorem mParam_conj [Finite G] (hV : IsElemAbelian 2 V) (g : G)
    (hVg : IsElemAbelian 2 (conjSubgroup V g)) :
    mParam (autI hVg ⊤) = mParam (autI hV ⊤) := by
  rw [autI_top_conj hV g hVg, mParam_map_congr]

theorem sParam_conj [Finite G] (hV : IsElemAbelian 2 V) (g : G)
    (hVg : IsElemAbelian 2 (conjSubgroup V g)) : sParam hVg = sParam hV := by
  unfold sParam
  rw [rParam_conj, mParam_conj hV g hVg]

end ConjMod

section Lemmas

variable {G : Type u} [Group G] [Finite G] {V : Subgroup G}

theorem rkIdx_fixV_autI (hV : IsElemAbelian 2 V) {K : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (V : Set G)) :
    rkIdx (fixV (autI hV K)) = mQuot V (V ⊓ Subgroup.centralizer (K : Set G)) := by
  unfold rkIdx mQuot
  congr 1
  have h1 := Subgroup.card_mul_index (fixV (autI hV K))
  have h2 := Subgroup.relIndex_mul_card (H := V ⊓ Subgroup.centralizer (K : Set G)) (K := V)
  rw [inf_eq_left.2 (inf_le_left : V ⊓ Subgroup.centralizer (K : Set G) ≤ V)] at h2
  rw [card_fixV_autI hV hK] at h1
  have hpos : 0 < Nat.card ↥(V ⊓ Subgroup.centralizer (K : Set G)) := Nat.card_pos
  have h3 : Nat.card (IntMod V hV) = Nat.card V := rfl
  rw [h3] at h1
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [h1, mul_comm]
  exact h2.symm

omit [Finite G] in
theorem isPGroup_autI (hV : IsElemAbelian 2 V) {K : Subgroup G}
    (hKN : K ≤ Subgroup.normalizer (V : Set G)) (hK : IsPGroup 2 K) :
    IsPGroup 2 (autI hV K) := by
  unfold autI
  exact (hK.of_equiv (Subgroup.subgroupOfEquivOfLe hKN).symm).map (convI hV)

omit [Finite G] in
theorem sParam_le_mParam (hV : IsElemAbelian 2 V) : sParam hV ≤ mParam (autI hV ⊤) :=
  ENat.toNat_le_of_le_natCast (min_le_right _ _)

omit [Finite G] in
theorem coe_sParam_le_rParam (hV : IsElemAbelian 2 V) : (sParam hV : ℕ∞) ≤ rParam V := by
  unfold sParam
  have hne : min (rParam V) ((mParam (autI hV ⊤) : ℕ) : ℕ∞) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top _) (min_le_right _ _)
  rw [ENat.natCast_toNat hne]
  exact min_le_left _ _

theorem e3_6 (hV : IsElemAbelian 2 V) {A B E : Subgroup G} (hBA : B ≤ A) (hAV : A ≤ V)
    (hs : mQuot V B < sParam hV) (hE : IsPGroup 2 E) :
    E ⊓ Subgroup.centralizer (A : Set G) = E ⊓ Subgroup.centralizer (B : Set G) ∧
      E ⊓ Subgroup.centralizer (B : Set G) = E ⊓ Subgroup.centralizer (V : Set G) := by
  have hBV : B ≤ V := hBA.trans hAV
  have hr : (mQuot V B : ℕ∞) < rParam V :=
    lt_of_lt_of_le (by exact_mod_cast hs) (coe_sParam_le_rParam hV)
  have hKN : E ⊓ Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer (V : Set G) := by
    intro x hx
    by_contra hxN
    have hC : ¬ Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer (V : Set G) :=
      fun h => hxN (h (Subgroup.mem_inf.1 hx).2)
    exact absurd (rParam_le_mQuot hBV hC) (not_le_of_gt hr)
  have hKC : E ⊓ Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer (V : Set G) := by
    by_contra hKC
    have hX1 : autI hV (E ⊓ Subgroup.centralizer (B : Set G)) ≠ ⊥ :=
      fun h => hKC ((autI_eq_bot_iff hV hKN).1 h)
    have hXp : IsPGroup 2 (autI hV (E ⊓ Subgroup.centralizer (B : Set G))) :=
      isPGroup_autI hV hKN (hE.to_le inf_le_left)
    have h1 := mParam_le_rkIdx_fixV (autI_mono hV (le_top : E ⊓ Subgroup.centralizer (B : Set G) ≤ ⊤))
      hXp hX1
    rw [rkIdx_fixV_autI hV hKN] at h1
    have hBle : B ≤ V ⊓ Subgroup.centralizer ((E ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) :
        Set G) := by
      refine le_inf hBV fun b hb => Subgroup.mem_centralizer_iff.2 fun k hk => ?_
      exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hk).2 b hb).symm
    have h2 := mQuot_mono (V := V) hBle
    have h3 := sParam_le_mParam hV
    omega
  have hAB : E ⊓ Subgroup.centralizer (A : Set G) ≤ E ⊓ Subgroup.centralizer (B : Set G) :=
    inf_le_inf_left E (Subgroup.centralizer_le hBA)
  have hVA : E ⊓ Subgroup.centralizer (V : Set G) ≤ E ⊓ Subgroup.centralizer (A : Set G) :=
    inf_le_inf_left E (Subgroup.centralizer_le hAV)
  have hBV' : E ⊓ Subgroup.centralizer (B : Set G) ≤ E ⊓ Subgroup.centralizer (V : Set G) :=
    le_inf inf_le_left hKC
  exact ⟨le_antisymm hAB (hBV'.trans hVA), le_antisymm hBV' (hVA.trans hAB)⟩

theorem e3_7 (hV : IsElemAbelian 2 V) {g : G} {B : Subgroup G}
    (hB : B ≤ conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))
    (hs : mQuot (conjSubgroup V g) B < sParam hV) :
    V ⊓ Subgroup.centralizer (B : Set G) = V ⊓ Subgroup.centralizer (conjSubgroup V g : Set G) := by
  have hVg := isElemAbelian_conjSubgroup hV g
  have h := e3_6 hVg (A := conjSubgroup V g) (B := B) (E := V) (hB.trans inf_le_left) le_rfl
    (by rwa [sParam_conj hV g hVg]) (B2F.isPGroup_of_isElemAbelian hV)
  exact h.1.symm

omit [Finite G] in
theorem isFFModule_autI_of_card_le (hV : IsElemAbelian 2 V) {X W : Subgroup G} (hWX : W ≤ X)
    (hWN : W ≤ Subgroup.normalizer (V : Set G)) (hW : IsElemAbelian 2 W) (hnt : ⁅V, W⁆ ≠ ⊥)
    (hcard : Nat.card V = Nat.card W)
    (hle : Nat.card ↥(W ⊓ Subgroup.centralizer (V : Set G)) ≤
      Nat.card ↥(V ⊓ Subgroup.centralizer (W : Set G))) : IsFFModule (autI hV X) := by
  have hnc : ¬ W ≤ Subgroup.centralizer (V : Set G) := by
    intro h
    apply hnt
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h
  refine ⟨autI hV W, autI_mono hV hWX, (autI_eq_bot_iff hV hWN).not.2 hnc,
    isElemAbelian2_autI hV hW hWN, ?_⟩
  have h1 := card_autI_mul_card_inf hV hWN
  have h2 := card_fixV_autI hV hWN
  have h3 : Nat.card (IntMod V hV) = Nat.card V := rfl
  rw [h3, hcard, h2, ← h1]
  exact Nat.mul_le_mul_left _ hle

omit [Finite G] in
theorem card_inf_centralizer_conj (A B : Subgroup G) (g : G) :
    Nat.card ↥(conjSubgroup A g ⊓ Subgroup.centralizer (conjSubgroup B g : Set G)) =
      Nat.card ↥(A ⊓ Subgroup.centralizer (B : Set G)) := by
  rw [← conjSubgroup_centralizer, ← conjSubgroup_inf, card_conjSubgroup]

omit [Finite G] in
theorem e3_11 (hV : IsElemAbelian 2 V) (hFF : ¬ IsFFModule (autI hV ⊤)) {g : G}
    (hg : conjSubgroup V g ≤ Subgroup.normalizer (V : Set G))
    (hnc : ⁅V, conjSubgroup V g⁆ ≠ ⊥) :
    ¬ V ≤ Subgroup.normalizer (conjSubgroup V g : Set G) := by
  intro hVN
  apply hFF
  have hg' : conjSubgroup V g⁻¹ ≤ Subgroup.normalizer (V : Set G) := by
    have := conjSubgroup_mono_left g⁻¹ hVN
    rwa [conjSubgroup_normalizer, conjSubgroup_conj_inv] at this
  have hnc' : ⁅V, conjSubgroup V g⁻¹⁆ ≠ ⊥ := by
    intro h
    apply hnc
    have h' := congrArg (fun C => conjSubgroup C g) h
    simp only [conjSubgroup_commutator, conjSubgroup_inv_conj, conjSubgroup_bot] at h'
    rw [Subgroup.commutator_comm]
    exact h'
  have hc1 : Nat.card ↥(conjSubgroup V g⁻¹ ⊓ Subgroup.centralizer (V : Set G)) =
      Nat.card ↥(V ⊓ Subgroup.centralizer (conjSubgroup V g : Set G)) := by
    have := card_inf_centralizer_conj (conjSubgroup V g⁻¹) V g
    rw [conjSubgroup_inv_conj] at this
    exact this.symm
  have hc2 : Nat.card ↥(V ⊓ Subgroup.centralizer (conjSubgroup V g⁻¹ : Set G)) =
      Nat.card ↥(conjSubgroup V g ⊓ Subgroup.centralizer (V : Set G)) := by
    have := card_inf_centralizer_conj V (conjSubgroup V g⁻¹) g
    rw [conjSubgroup_inv_conj] at this
    exact this.symm
  by_cases hle : Nat.card ↥(conjSubgroup V g ⊓ Subgroup.centralizer (V : Set G)) ≤
      Nat.card ↥(V ⊓ Subgroup.centralizer (conjSubgroup V g : Set G))
  · exact isFFModule_autI_of_card_le hV (X := ⊤) le_top hg (isElemAbelian_conjSubgroup hV g) hnc
      (card_conjSubgroup V g).symm hle
  · push Not at hle
    exact isFFModule_autI_of_card_le hV (X := ⊤) le_top hg' (isElemAbelian_conjSubgroup hV g⁻¹)
      hnc' (card_conjSubgroup V g⁻¹).symm (by rw [hc1, hc2]; exact hle.le)

theorem mQuot_autI_preI (hV : IsElemAbelian 2 V) {A : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (V : Set G)) {B' : Subgroup (MulAut (IntMod V hV))}
    (hB' : B' ≤ autI hV A) :
    mQuot (autI hV A) B' = mQuot A (preI hV A hAN B') := by
  unfold mQuot
  congr 1
  have h1 := Subgroup.relIndex_mul_card (H := B') (K := autI hV A)
  rw [inf_eq_left.2 hB'] at h1
  have h2 := Subgroup.relIndex_mul_card (H := preI hV A hAN B') (K := A)
  rw [inf_eq_left.2 (preI_le hV)] at h2
  have hcB := card_preI hV hB' (hA := hAN)
  have hcA := card_autI_mul_card_inf hV hAN
  have hb : 0 < Nat.card B' := Nat.card_pos
  have hc : 0 < Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hb hc)
  rw [hcB] at h2
  calc B'.relIndex (autI hV A) * (Nat.card B' * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)))
      = (B'.relIndex (autI hV A) * Nat.card B') * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) :=
        by ring
    _ = Nat.card (autI hV A) * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := by rw [h1]
    _ = Nat.card A := hcA
    _ = (preI hV A hAN B').relIndex A *
        (Nat.card B' * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G))) := h2.symm

theorem e3_10_one (hV : IsElemAbelian 2 V) {g : G}
    (hb : mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) <
      sParam hV) :
    V ⊓ Subgroup.centralizer ((conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) : Subgroup G) :
        Set G) = V ⊓ Subgroup.centralizer (conjSubgroup V g : Set G) :=
  e3_7 hV le_rfl hb

theorem e3_10_two (hV : IsElemAbelian 2 V) {g : G}
    (hb : mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) <
      sParam hV) (hnc : ⁅V, conjSubgroup V g⁆ ≠ ⊥) :
    autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) ∈
      aSet (sParam hV - mQuot (conjSubgroup V g)
        (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))) (autI hV ⊤) := by
  have hVg : IsElemAbelian 2 (conjSubgroup V g) := isElemAbelian_conjSubgroup hV g
  have hAN : conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    inf_le_right
  have hAVg : conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) ≤ conjSubgroup V g := inf_le_left
  have hAel : IsElemAbelian 2 (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) :=
    B2F.isElemAbelian_mono hAVg hVg
  have hC := e3_10_one hV hb
  refine ⟨autI_mono hV le_top, ?_, isElemAbelian2_autI hV hAel hAN, ?_⟩
  · intro h
    apply hnc
    have hAc := (autI_eq_bot_iff hV hAN).1 h
    have hVA : V ≤ Subgroup.centralizer ((conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) :
        Subgroup G) : Set G) := fun v hv =>
      Subgroup.mem_centralizer_iff.2 fun a ha =>
        (Subgroup.mem_centralizer_iff.1 (hAc ha) v hv).symm
    have : V ≤ Subgroup.centralizer (conjSubgroup V g : Set G) := by
      have h1 : V ≤ V ⊓ Subgroup.centralizer ((conjSubgroup V g ⊓
          Subgroup.normalizer (V : Set G) : Subgroup G) : Set G) := le_inf le_rfl hVA
      rw [hC] at h1
      exact h1.trans inf_le_right
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 this
  · intro B' hB' hm
    set A := conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) with hAdef
    have hBA : preI hV A hAN B' ≤ A := preI_le hV
    have hpre : autI hV (preI hV A hAN B') = B' := autI_preI hV hB'
    have hm' : mQuot A (preI hV A hAN B') < sParam hV - mQuot (conjSubgroup V g) A := by
      rw [← mQuot_autI_preI hV hAN hB']
      exact hm
    generalize preI hV A hAN B' = B at hBA hpre hm'
    have hBN : B ≤ Subgroup.normalizer (V : Set G) := hBA.trans hAN
    have hadd := mQuot_add (V := conjSubgroup V g) hBA hAVg
    have hlt : mQuot (conjSubgroup V g) B < sParam hV := by omega
    have hCB := e3_7 hV hBA hlt
    ext v
    have e1 : v ∈ fixV B' ↔ v.val ∈ Subgroup.centralizer (B : Set G) := by
      rw [← hpre]
      exact mem_fixV_autI hV hBN v
    have e2 : v ∈ fixV (autI hV A) ↔ v.val ∈ Subgroup.centralizer (A : Set G) :=
      mem_fixV_autI hV hAN v
    rw [e1, e2]
    have hv : v.val ∈ V := v.val_mem
    constructor
    · intro hc
      have : v.val ∈ V ⊓ Subgroup.centralizer (B : Set G) := Subgroup.mem_inf.2 ⟨hv, hc⟩
      rw [hCB, ← hC] at this
      exact (Subgroup.mem_inf.1 this).2
    · intro hc
      have : v.val ∈ V ⊓ Subgroup.centralizer (A : Set G) := Subgroup.mem_inf.2 ⟨hv, hc⟩
      rw [hC, ← hCB] at this
      exact (Subgroup.mem_inf.1 this).2

theorem e3_10_three (hV : IsElemAbelian 2 V) {g : G}
    (hb : mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) <
      sParam hV) (hnc : ⁅V, conjSubgroup V g⁆ ≠ ⊥) :
    sParam hV - aParam (autI hV ⊤) ≤
      mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) := by
  have h := le_aParam_of_mem_aSet (by omega) (e3_10_two hV hb hnc)
  omega

end Lemmas

end E3

end CFSG.Quasithin
