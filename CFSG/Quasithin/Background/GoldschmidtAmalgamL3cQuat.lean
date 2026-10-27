module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.QuaternionCoordinateHom
public import CFSG.Quasithin.Background.F6GoldschmidtList
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2SHyp

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL2S

namespace F6

namespace GoldAmL3c

variable {D : Type*} [Group D]

theorem exists_quaternion_hom {I J w : D} (hw1 : w ≠ 1) (hww : w * w = 1)
    (hII : I * I = w) (hJJ : J * J = w) (hJIJ : J * I * J⁻¹ = I⁻¹) :
    ∃ f : QuaternionGroup 2 →* D, Function.Injective f ∧ f (QuaternionGroup.a 1) = I ∧
      f (QuaternionGroup.xa 0) = J ∧ ∀ q, f q ∈ Subgroup.closure ({I, J} : Set D) := by
  have hi2 : ¬ I ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two, hII]; exact hw1
  have hi4 : I ^ 2 ^ (1 + 1) = 1 := by
    have e : (2 : ℕ) ^ (1 + 1) = 4 := by norm_num
    rw [e, show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, hII, hww]
  have hiord : orderOf I = 2 ^ (1 + 1) := orderOf_eq_prime_pow hi2 hi4
  have hZi : Nat.card (Subgroup.zpowers I) = 2 * 2 := by
    rw [Nat.card_zpowers, hiord]; norm_num
  have hgen : ∀ y : ↥(Subgroup.zpowers I),
      y ∈ Subgroup.zpowers (⟨I, Subgroup.mem_zpowers _⟩ : ↥(Subgroup.zpowers I)) := by
    rintro ⟨y, hy⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ⟨n, Subtype.ext (by simp)⟩
  let eZ := zmodMulEquivOfGenerator hgen hZi
  let coords : Multiplicative (ZMod (2 * 2)) →* D :=
    (Subgroup.zpowers I).subtype.comp eZ.toMonoidHom
  have hcoords_zpow : ∀ n : ℤ, coords (Multiplicative.ofAdd (n : ZMod (2 * 2))) = I ^ n := by
    intro n
    have := zmodMulEquivOfGenerator_apply_ofAdd_intCast hgen hZi n
    simp only [coords, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
    change ((zmodMulEquivOfGenerator hgen hZi (Multiplicative.ofAdd (n : ZMod (2 * 2))) :
      ↥(Subgroup.zpowers I)) : D) = _
    rw [this]
    simp
  have hcoords_mem : ∀ c, coords c ∈ Subgroup.zpowers I := fun c => (eZ c).2
  have hcinj : Function.Injective coords := Subtype.val_injective.comp eZ.injective
  have hJnot : J ∉ coords.range := by
    rintro ⟨c, hc⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hcoords_mem c)
    have hcomm : I * J = J * I := by
      rw [← hc, ← hn]
      exact ((Commute.refl I).zpow_right n).eq
    have h1 : J * I * J⁻¹ = I := by
      rw [← hcomm]; group
    rw [h1] at hJIJ
    have h2 : I * I = 1 := by
      calc I * I = I * I⁻¹⁻¹ := by rw [inv_inv]
        _ = I⁻¹ * I⁻¹⁻¹ := by rw [← hJIJ]
        _ = 1 := by rw [inv_inv]; group
    rw [hII] at h2
    exact hw1 h2
  have hsquare : J ^ 2 = coords (Multiplicative.ofAdd (((2 : ℕ) : ZMod (2 * 2)))) := by
    have e1 := hcoords_zpow 2
    have e2 : (((2 : ℤ) : ZMod (2 * 2))) = ((2 : ℕ) : ZMod (2 * 2)) := by simp
    rw [e2] at e1
    rw [e1, pow_two, hJJ, zpow_two, hII]
  have hinversion : ∀ c, J * coords c * J⁻¹ = (coords c)⁻¹ := by
    intro c
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hcoords_mem c)
    rw [← hn, ← conj_zpow, hJIJ, inv_zpow]
  let f : QuaternionGroup 2 →* D :=
    CFSG.DisconnectedInvolutionGraph.Helpers.quaternionCoordinateHom 2 coords J hsquare
      hinversion
  have hty : ∀ p q : ZMod (2 * 2),
      coords (Multiplicative.ofAdd p) ≠ J * coords (Multiplicative.ofAdd q) := by
    intro p q hpq
    apply hJnot
    have e : J = coords (Multiplicative.ofAdd p) * (coords (Multiplicative.ofAdd q))⁻¹ := by
      rw [hpq]; group
    rw [e]
    exact coords.range.mul_mem ⟨_, rfl⟩ (coords.range.inv_mem ⟨_, rfl⟩)
  have hfinj : Function.Injective f := by
    intro p q hpq
    cases p with
    | a p =>
      cases q with
      | a q =>
        change coords (Multiplicative.ofAdd p) = coords (Multiplicative.ofAdd q) at hpq
        exact congrArg QuaternionGroup.a (congrArg Multiplicative.toAdd (hcinj hpq))
      | xa q => exact (hty p q hpq).elim
    | xa p =>
      cases q with
      | a q => exact (hty q p hpq.symm).elim
      | xa q =>
        change J * coords (Multiplicative.ofAdd p) = J * coords (Multiplicative.ofAdd q) at hpq
        exact congrArg QuaternionGroup.xa
          (congrArg Multiplicative.toAdd (hcinj (mul_left_cancel hpq)))
  have hIc : I ∈ Subgroup.closure ({I, J} : Set D) := Subgroup.subset_closure (Or.inl rfl)
  have hJc : J ∈ Subgroup.closure ({I, J} : Set D) := Subgroup.subset_closure (Or.inr rfl)
  refine ⟨f, hfinj, ?_, ?_, ?_⟩
  · change coords (Multiplicative.ofAdd (1 : ZMod (2 * 2))) = I
    have := hcoords_zpow 1
    simpa using this
  · change J * coords (Multiplicative.ofAdd (0 : ZMod (2 * 2))) = J
    simp
  · intro q
    cases q with
    | a k =>
      change coords (Multiplicative.ofAdd k) ∈ _
      exact Subgroup.zpowers_le.mpr hIc (hcoords_mem _)
    | xa k =>
      change J * coords (Multiplicative.ofAdd k) ∈ _
      exact Subgroup.mul_mem _ hJc (Subgroup.zpowers_le.mpr hIc (hcoords_mem _))

theorem commute_of_closure {S T : Set D} (h : ∀ x ∈ S, ∀ y ∈ T, x * y = y * x) {a b : D}
    (ha : a ∈ Subgroup.closure S) (hb : b ∈ Subgroup.closure T) : a * b = b * a := by
  have h1 : ∀ y ∈ T, Subgroup.closure S ≤ Subgroup.centralizer ({y} : Set D) := by
    intro y hy
    rw [Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact (h x hx w hy).symm
  have h2 : Subgroup.closure T ≤ Subgroup.centralizer (Subgroup.closure S : Set D) := by
    rw [Subgroup.closure_le]
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro a' ha'
    exact (Subgroup.mem_centralizer_iff.mp (h1 y hy ha') y rfl).symm
  exact Subgroup.mem_centralizer_iff.mp (h2 hb) a ha

theorem isCentralProduct₂_of_dihedral_pair [Finite D] (P : Subgroup D) {s t s' t' z₀ : D}
    (hs : s ∈ P) (ht : t ∈ P) (hs' : s' ∈ P) (ht' : t' ∈ P)
    (hz1 : z₀ ≠ 1) (hz2 : z₀ * z₀ = 1)
    (hzs : z₀ * s = s * z₀) (hzs' : z₀ * s' = s' * z₀)
    (hss : s * s = 1) (htt : t * t = 1) (hss' : s' * s' = 1) (htt' : t' * t' = 1)
    (hts : t * s * t⁻¹ = z₀ * s) (hts' : t' * s' * t'⁻¹ = z₀ * s')
    (c1 : s * s' = s' * s) (c2 : s * t' = t' * s) (c3 : t * s' = s' * t) (c4 : t * t' = t' * t)
    (hgen : Subgroup.closure ({s, t, s', t'} : Set D) = P) (hcard : Nat.card ↥P = 32) :
    IsCentralProduct₂ ↥P (QuaternionGroup 2) (QuaternionGroup 2) := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hs'i : s'⁻¹ = s' := inv_eq_of_mul_eq_one_right hss'
  have ht'i : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right htt'
  have tsx : t * s = z₀ * s * t := by
    calc t * s = (t * s * t⁻¹) * t := by group
      _ = z₀ * s * t := by rw [hts]
  have t's' : t' * s' = z₀ * s' * t' := by
    calc t' * s' = (t' * s' * t'⁻¹) * t' := by group
      _ = z₀ * s' * t' := by rw [hts']
  have hrs : (s * t) * s = z₀ * t := by
    calc (s * t) * s = s * (t * s) := by group
      _ = s * (z₀ * s * t) := by rw [tsx]
      _ = (s * z₀) * s * t := by group
      _ = (z₀ * s) * s * t := by rw [← hzs]
      _ = z₀ * (s * s) * t := by group
      _ = z₀ * t := by rw [hss]; group
  have hr's' : (s' * t') * s' = z₀ * t' := by
    calc (s' * t') * s' = s' * (t' * s') := by group
      _ = s' * (z₀ * s' * t') := by rw [t's']
      _ = (s' * z₀) * s' * t' := by group
      _ = (z₀ * s') * s' * t' := by rw [← hzs']
      _ = z₀ * (s' * s') * t' := by group
      _ = z₀ * t' := by rw [hss']; group
  have hII : (s * t) * (s * t) = z₀ := by
    calc (s * t) * (s * t) = ((s * t) * s) * t := by group
      _ = z₀ * t * t := by rw [hrs]
      _ = z₀ * (t * t) := by group
      _ = z₀ := by rw [htt]; group
  have hI'I' : (s' * t') * (s' * t') = z₀ := by
    calc (s' * t') * (s' * t') = ((s' * t') * s') * t' := by group
      _ = z₀ * t' * t' := by rw [hr's']
      _ = z₀ * (t' * t') := by group
      _ = z₀ := by rw [htt']; group
  have hr's : s * (s' * t') = (s' * t') * s := by
    calc s * (s' * t') = (s * s') * t' := by group
      _ = (s' * s) * t' := by rw [c1]
      _ = s' * (s * t') := by group
      _ = s' * (t' * s) := by rw [c2]
      _ = (s' * t') * s := by group
  have hr't : t * (s' * t') = (s' * t') * t := by
    calc t * (s' * t') = (t * s') * t' := by group
      _ = (s' * t) * t' := by rw [c3]
      _ = s' * (t * t') := by group
      _ = s' * (t' * t) := by rw [c4]
      _ = (s' * t') * t := by group
  have hrr' : (s * t) * (s' * t') = (s' * t') * (s * t) := by
    calc (s * t) * (s' * t') = s * (t * (s' * t')) := by group
      _ = s * ((s' * t') * t) := by rw [hr't]
      _ = (s * (s' * t')) * t := by group
      _ = ((s' * t') * s) * t := by rw [hr's]
      _ = (s' * t') * (s * t) := by group
  have hs'r : s' * (s * t) = (s * t) * s' := by
    calc s' * (s * t) = (s' * s) * t := by group
      _ = (s * s') * t := by rw [c1]
      _ = s * (s' * t) := by group
      _ = s * (t * s') := by rw [c3]
      _ = (s * t) * s' := by group
  have hJJ : (s * (s' * t')) * (s * (s' * t')) = z₀ := by
    calc (s * (s' * t')) * (s * (s' * t')) = s * ((s' * t') * s) * (s' * t') := by group
      _ = s * (s * (s' * t')) * (s' * t') := by rw [← hr's]
      _ = (s * s) * ((s' * t') * (s' * t')) := by group
      _ = z₀ := by rw [hss, hI'I']; group
  have hJ'J' : (s' * (s * t)) * (s' * (s * t)) = z₀ := by
    calc (s' * (s * t)) * (s' * (s * t)) = s' * ((s * t) * s') * (s * t) := by group
      _ = s' * (s' * (s * t)) * (s * t) := by rw [← hs'r]
      _ = (s' * s') * ((s * t) * (s * t)) := by group
      _ = z₀ := by rw [hss', hII]; group
  have hJIJ : (s * (s' * t')) * (s * t) * (s * (s' * t'))⁻¹ = (s * t)⁻¹ := by
    have hc : (s' * t') * (s * t) * (s' * t')⁻¹ = s * t := by
      calc (s' * t') * (s * t) * (s' * t')⁻¹ = ((s * t) * (s' * t')) * (s' * t')⁻¹ := by
            rw [hrr']
        _ = s * t := by group
    calc (s * (s' * t')) * (s * t) * (s * (s' * t'))⁻¹
        = s * ((s' * t') * (s * t) * (s' * t')⁻¹) * s⁻¹ := by group
      _ = s * (s * t) * s⁻¹ := by rw [hc]
      _ = (s * s) * t * s⁻¹ := by group
      _ = t * s := by rw [hss, one_mul, hsi]
      _ = (s * t)⁻¹ := by rw [mul_inv_rev, hti, hsi]
  have hJ'I'J' : (s' * (s * t)) * (s' * t') * (s' * (s * t))⁻¹ = (s' * t')⁻¹ := by
    have hc : (s * t) * (s' * t') * (s * t)⁻¹ = s' * t' := by
      calc (s * t) * (s' * t') * (s * t)⁻¹ = ((s' * t') * (s * t)) * (s * t)⁻¹ := by rw [hrr']
        _ = s' * t' := by group
    calc (s' * (s * t)) * (s' * t') * (s' * (s * t))⁻¹
        = s' * ((s * t) * (s' * t') * (s * t)⁻¹) * s'⁻¹ := by group
      _ = s' * (s' * t') * s'⁻¹ := by rw [hc]
      _ = (s' * s') * t' * s'⁻¹ := by group
      _ = t' * s' := by rw [hss', one_mul, hs'i]
      _ = (s' * t')⁻¹ := by rw [mul_inv_rev, ht'i, hs'i]
  have hIJ' : (s * t) * (s' * (s * t)) = (s' * (s * t)) * (s * t) := by
    calc (s * t) * (s' * (s * t)) = ((s * t) * s') * (s * t) := by group
      _ = (s' * (s * t)) * (s * t) := by rw [← hs'r]
  have hJI' : (s * (s' * t')) * (s' * t') = (s' * t') * (s * (s' * t')) := by
    calc (s * (s' * t')) * (s' * t') = s * ((s' * t') * (s' * t')) := by group
      _ = (s * (s' * t')) * (s' * t') := by group
      _ = ((s' * t') * s) * (s' * t') := by rw [hr's]
      _ = (s' * t') * (s * (s' * t')) := by group
  have hJJ' : (s * (s' * t')) * (s' * (s * t)) = (s' * (s * t)) * (s * (s' * t')) := by
    have e1 : (s * (s' * t')) * (s' * (s * t)) = z₀ * t' * t := by
      calc (s * (s' * t')) * (s' * (s * t)) = s * ((s' * t') * s') * (s * t) := by group
        _ = s * (z₀ * t') * (s * t) := by rw [hr's']
        _ = (s * z₀) * (t' * s) * t := by group
        _ = (z₀ * s) * (t' * s) * t := by rw [← hzs]
        _ = z₀ * (s * t') * s * t := by group
        _ = z₀ * (t' * s) * s * t := by rw [c2]
        _ = z₀ * t' * (s * s) * t := by group
        _ = z₀ * t' * t := by rw [hss]; group
    have e2 : (s' * (s * t)) * (s * (s' * t')) = z₀ * t * t' := by
      calc (s' * (s * t)) * (s * (s' * t')) = s' * ((s * t) * s) * (s' * t') := by group
        _ = s' * (z₀ * t) * (s' * t') := by rw [hrs]
        _ = (s' * z₀) * (t * s') * t' := by group
        _ = (z₀ * s') * (t * s') * t' := by rw [← hzs']
        _ = z₀ * (s' * t) * s' * t' := by group
        _ = z₀ * (t * s') * s' * t' := by rw [← c3]
        _ = z₀ * t * (s' * s') * t' := by group
        _ = z₀ * t * t' := by rw [hss']; group
    rw [e1, e2]
    calc z₀ * t' * t = z₀ * (t' * t) := by group
      _ = z₀ * (t * t') := by rw [c4]
      _ = z₀ * t * t' := by group
  obtain ⟨f₁, hf₁inj, hf₁I, hf₁J, hf₁mem⟩ := exists_quaternion_hom hz1 hz2 hII hJJ hJIJ
  obtain ⟨f₂, hf₂inj, hf₂I, hf₂J, hf₂mem⟩ := exists_quaternion_hom hz1 hz2 hI'I' hJ'J' hJ'I'J'
  have hIP : s * t ∈ P := P.mul_mem hs ht
  have hI'P : s' * t' ∈ P := P.mul_mem hs' ht'
  have hJP : s * (s' * t') ∈ P := P.mul_mem hs hI'P
  have hJ'P : s' * (s * t) ∈ P := P.mul_mem hs' hIP
  have hcl₁ : Subgroup.closure ({s * t, s * (s' * t')} : Set D) ≤ P := by
    rw [Subgroup.closure_le]
    rintro w (rfl | rfl)
    · exact hIP
    · exact hJP
  have hcl₂ : Subgroup.closure ({s' * t', s' * (s * t)} : Set D) ≤ P := by
    rw [Subgroup.closure_le]
    rintro w (rfl | rfl)
    · exact hI'P
    · exact hJ'P
  have hS₁P : f₁.range ≤ P := by
    rintro _ ⟨q, rfl⟩; exact hcl₁ (hf₁mem q)
  have hS₂P : f₂.range ≤ P := by
    rintro _ ⟨q, rfl⟩; exact hcl₂ (hf₂mem q)
  have hcomm : ∀ u ∈ f₁.range, ∀ w ∈ f₂.range, u * w = w * u := by
    rintro _ ⟨q, rfl⟩ _ ⟨q', rfl⟩
    refine commute_of_closure (S := ({s * t, s * (s' * t')} : Set D))
      (T := ({s' * t', s' * (s * t)} : Set D)) ?_ (hf₁mem q) (hf₂mem q')
    rintro u (rfl | rfl) w (rfl | rfl)
    · exact hrr'
    · exact hIJ'
    · exact hJI'
    · exact hJJ'
  have hIr : s * t ∈ f₁.range := ⟨QuaternionGroup.a 1, hf₁I⟩
  have hJr : s * (s' * t') ∈ f₁.range := ⟨QuaternionGroup.xa 0, hf₁J⟩
  have hI'r : s' * t' ∈ f₂.range := ⟨QuaternionGroup.a 1, hf₂I⟩
  have hJ'r : s' * (s * t) ∈ f₂.range := ⟨QuaternionGroup.xa 0, hf₂J⟩
  have hsupP : f₁.range ⊔ f₂.range = P := by
    refine le_antisymm (sup_le hS₁P hS₂P) ?_
    rw [← hgen, Subgroup.closure_le]
    have hI : s * t ∈ f₁.range ⊔ f₂.range := Subgroup.mem_sup_left hIr
    have hJ : s * (s' * t') ∈ f₁.range ⊔ f₂.range := Subgroup.mem_sup_left hJr
    have hI' : s' * t' ∈ f₁.range ⊔ f₂.range := Subgroup.mem_sup_right hI'r
    have hJ' : s' * (s * t) ∈ f₁.range ⊔ f₂.range := Subgroup.mem_sup_right hJ'r
    have hs_mem : s ∈ f₁.range ⊔ f₂.range := by
      have e : s = (s * (s' * t')) * (s' * t')⁻¹ := by group
      rw [e]; exact Subgroup.mul_mem _ hJ (Subgroup.inv_mem _ hI')
    have hs'_mem : s' ∈ f₁.range ⊔ f₂.range := by
      have e : s' = (s' * (s * t)) * (s * t)⁻¹ := by group
      rw [e]; exact Subgroup.mul_mem _ hJ' (Subgroup.inv_mem _ hI)
    have ht_mem : t ∈ f₁.range ⊔ f₂.range := by
      have e : t = s⁻¹ * (s * t) := by group
      rw [e]; exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hs_mem) hI
    have ht'_mem : t' ∈ f₁.range ⊔ f₂.range := by
      have e : t' = s'⁻¹ * (s' * t') := by group
      rw [e]; exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hs'_mem) hI'
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> assumption
  have hc₁ : Nat.card f₁.range = 8 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hf₁inj).toEquiv, Nat.card_eq_fintype_card,
      QuaternionGroup.card]
  have hc₂ : Nat.card f₂.range = 8 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hf₂inj).toEquiv, Nat.card_eq_fintype_card,
      QuaternionGroup.card]
  have hprod := card_sup_mul_card_inf_of_commute' hcomm
  rw [hsupP, hcard, hc₁, hc₂] at hprod
  have hinf : Nat.card ↥(f₁.range ⊓ f₂.range) = 2 := by omega
  refine ⟨f₁.range.subgroupOf P, f₂.range.subgroupOf P, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.subgroupOf_sup hS₁P hS₂P, hsupP, Subgroup.subgroupOf_self]
  · intro u hu w hw
    apply Subtype.ext
    exact hcomm u hu w hw
  · exact ⟨(Subgroup.subgroupOfEquivOfLe hS₁P).trans (MonoidHom.ofInjective hf₁inj).symm⟩
  · exact ⟨(Subgroup.subgroupOfEquivOfLe hS₂P).trans (MonoidHom.ofInjective hf₂inj).symm⟩
  · have e : f₁.range.subgroupOf P ⊓ f₂.range.subgroupOf P =
        (f₁.range ⊓ f₂.range).subgroupOf P := (Subgroup.comap_inf _ _ _).symm
    rw [e, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hS₁P)).toEquiv]
    exact hinf

end GoldAmL3c

end F6

end CFSG.Quasithin
