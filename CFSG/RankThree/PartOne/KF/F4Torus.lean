module

public import CFSG.LocalAnalysis.SectionRank.LargeRee.Torus
public import CFSG.LieType.Ree.LargeReeTorusRootForms
public import CFSG.LieType.Ree.LargeReeFixedGroupOddCore

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.SectionRank.LargeRee
  CFSG.LieType.Ree.LargeReeCover CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.LieType.Simplicity

variable {p a : ℕ} {K : Type} [Field K]

structure F4Param (p a : ℕ) (K : Type) [Field K] : Prop where
  prime : p.Prime
  five_le : 5 ≤ p
  card : Nat.card K = 2 ^ (2 * a + 1)
  dvd : p ∣ 2 ^ (2 * a + 1) - 1

namespace F4Param

variable (h : F4Param p a K)

include h in
theorem finite : Finite K := Nat.finite_of_card_ne_zero (by rw [h.card]; positivity)

include h in
theorem one_le : 1 ≤ a := by
  by_contra h0
  have ha : a = 0 := by omega
  have h1 := h.dvd
  rw [ha] at h1
  have h2 := Nat.le_of_dvd (by norm_num) h1
  have := h.five_le
  omega

include h in
theorem theta_dvd : (p : ℤ) ∣ 2 * ((2 ^ a : ℕ) : ℤ) ^ 2 - 1 := by
  have h1 : ((2 ^ (2 * a + 1) - 1 : ℕ) : ℤ) = 2 * ((2 ^ a : ℕ) : ℤ) ^ 2 - 1 := by
    have : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
    rw [Nat.cast_sub this]
    push_cast
    ring
  rw [← h1]
  exact Int.natCast_dvd_natCast.2 h.dvd

include h in
theorem charP_two : CharP K ReeTag.F4.prime := by
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (p := 2) (f := 2 * a + 1) (by
    rw [Fintype.card_eq_nat_card]
    exact h.card)

end F4Param

section Torus

variable (p a K) in
@[expose] noncomputable def tp4Hom
    : (Fin 2 → rootsOfUnity p K) →* ModGL F4.tag K :=
  (torusPair (K := K) a).comp (MonoidHom.prod
    ((rootsOfUnity p K).subtype.comp (Pi.evalMonoidHom (fun _ => rootsOfUnity p K) 0))
    ((rootsOfUnity p K).subtype.comp (Pi.evalMonoidHom (fun _ => rootsOfUnity p K) 1)))

theorem tp4Hom_apply
    (b : Fin 2 → rootsOfUnity p K) :
    tp4Hom p a K b =
      torusPair a (((b 0 : rootsOfUnity p K) : Kˣ), ((b 1 : rootsOfUnity p K) : Kˣ)) :=
  rfl

theorem simpleChar_T_mul_zero [Finite K]
    (u v : Kˣ) :
    simpleChar (F4.reeTorus a (fi 0) u * F4.reeTorus a (fi 1) v) (fi 0) =
      ((u ^ (2 : ℤ) * v ^ (-1 : ℤ) : Kˣ) : K) := by
  rw [simpleChar_mul (F4.reeTorus_mem_H a _ u) (F4.reeTorus_mem_H a _ v), simpleChar_reeTorus,
    simpleChar_reeTorus, reeExp_zero_zero, reeExp_one_zero, ← Units.val_mul]

theorem simpleChar_T_mul_one [Finite K]
    (u v : Kˣ) :
    simpleChar (F4.reeTorus a (fi 0) u * F4.reeTorus a (fi 1) v) (fi 1) =
      ((u ^ (-1 : ℤ) * v ^ (2 - 2 * ((ReeTag.F4.prime ^ a : ℕ) : ℤ)) : Kˣ) : K) := by
  rw [simpleChar_mul (F4.reeTorus_mem_H a _ u) (F4.reeTorus_mem_H a _ v), simpleChar_reeTorus,
    simpleChar_reeTorus, reeExp_zero_one, reeExp_one_one, ← Units.val_mul]

theorem eq_one_of_two_chars [Finite K] (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1)) {U V : Kˣ}
    (h0 : U ^ (2 : ℤ) * V ^ (-1 : ℤ) = 1)
    (h1 : U ^ (-1 : ℤ) * V ^ (2 - 2 * ((ReeTag.F4.prime ^ a : ℕ) : ℤ)) = 1) : U = 1 ∧ V = 1 := by
  set e : ℤ := ((ReeTag.F4.prime ^ a : ℕ) : ℤ) with he
  have hq : (Nat.card K : ℤ) = 2 * e ^ 2 := by
    rw [hK]
    exact two_pow_eq_two_mul_sq a
  have hV : V = U ^ (2 : ℤ) := by
    rw [zpow_neg_one] at h0
    exact (mul_inv_eq_one.1 h0).symm
  rw [hV, ← zpow_mul] at h1
  have h3 : U ^ (3 - 4 * e) = 1 := by
    calc U ^ (3 - 4 * e) = U ^ (-1 : ℤ) * U ^ (2 * (2 - 2 * e)) := by
          rw [← zpow_add]
          ring_nf
      _ = 1 := h1
  have hu : U = 1 := by
    have hexp : (3 - 4 * e) * (3 + 4 * e) = 1 + (-8) * ((Nat.card K : ℤ) - 1) := by
      rw [hq]
      ring
    rw [← units_zpow_one_add_mul U (-8), ← hexp, zpow_mul, h3, one_zpow]
  refine ⟨hu, ?_⟩
  rw [hV, hu, one_zpow]

theorem torusPair_eq_one
    [Finite K]
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1)) {u v : Kˣ}
    (huv : torusPair a (u, v) = 1) : u = 1 ∧ v = 1 := by
  rw [torusPair_eq_reeTorus] at huv
  have h1 : F4.reeTorus a (fi 0) u * F4.reeTorus a (fi 1) v = 1 := Subtype.ext huv
  have h0 : simpleChar (1 : adjointGroup F4.tag K) (fi 0) = 1 := by simp [simpleChar]
  have h0' : simpleChar (1 : adjointGroup F4.tag K) (fi 1) = 1 := by simp [simpleChar]
  have c0 := congrArg (fun g => simpleChar g (fi 0)) h1
  have c1 := congrArg (fun g => simpleChar g (fi 1)) h1
  rw [simpleChar_T_mul_zero, h0] at c0
  rw [simpleChar_T_mul_one, h0'] at c1
  exact eq_one_of_two_chars hK (Units.ext c0) (Units.ext c1)

theorem reeTorus_inv
    [Finite K] (j : Fin F4.tag.rank) (u : Kˣ) :
    F4.reeTorus a j u⁻¹ = (F4.reeTorus a j u)⁻¹ := by
  have h := reeTorus_mul (K := K) a j u⁻¹ u
  rw [inv_mul_cancel, reeTorus_one] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem reeTorus_zero_one_comm
    [Finite K] (u v : Kˣ) :
    F4.reeTorus a (fi 0) u * F4.reeTorus a (fi 1) v =
      F4.reeTorus a (fi 1) v * F4.reeTorus a (fi 0) u :=
  (commute_of_mem_H (F4.reeTorus_mem_H a _ u) (F4.reeTorus_mem_H a _ v)).eq

theorem conj_nrep_zero
    [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1)) (u v : Kˣ) :
    nrep F4.tag K (F4.blockElt (fi 0)) * (F4.reeTorus a (fi 0) u * F4.reeTorus a (fi 1) v) *
        (nrep F4.tag K (F4.blockElt (fi 0)))⁻¹ =
      F4.reeTorus a (fi 0) (u⁻¹ * v) * F4.reeTorus a (fi 1) v := by
  have h1 := (torus_reflections (a := a) hK u).1
  have h2 := (torus_reflections (a := a) hK v).2.1
  calc nrep F4.tag K (F4.blockElt (fi 0)) * (F4.reeTorus a (fi 0) u * F4.reeTorus a (fi 1) v) *
        (nrep F4.tag K (F4.blockElt (fi 0)))⁻¹ =
      (nrep F4.tag K (F4.blockElt (fi 0)) * F4.reeTorus a (fi 0) u *
        (nrep F4.tag K (F4.blockElt (fi 0)))⁻¹) *
      (nrep F4.tag K (F4.blockElt (fi 0)) * F4.reeTorus a (fi 1) v *
        (nrep F4.tag K (F4.blockElt (fi 0)))⁻¹) := by group
    _ = (F4.reeTorus a (fi 0) u)⁻¹ * (F4.reeTorus a (fi 1) v * F4.reeTorus a (fi 0) v) := by
      rw [h1, h2]
    _ = (F4.reeTorus a (fi 0) u)⁻¹ * (F4.reeTorus a (fi 0) v * F4.reeTorus a (fi 1) v) := by
      rw [← reeTorus_zero_one_comm]
    _ = F4.reeTorus a (fi 0) (u⁻¹ * v) * F4.reeTorus a (fi 1) v := by
      rw [reeTorus_mul, reeTorus_inv, mul_assoc]

theorem conj_nrep_one
    [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1)) (u v : Kˣ) :
    nrep F4.tag K (F4.blockElt (fi 1)) * (F4.reeTorus a (fi 0) u * F4.reeTorus a (fi 1) v) *
        (nrep F4.tag K (F4.blockElt (fi 1)))⁻¹ =
      F4.reeTorus a (fi 0) u *
        F4.reeTorus a (fi 1) (u ^ (2 + 2 * ((ReeTag.F4.prime ^ a : ℕ) : ℤ)) * v⁻¹) := by
  have h3 := (torus_reflections (a := a) hK v).2.2.1
  have h4 := (torus_reflections (a := a) hK u).2.2.2
  calc nrep F4.tag K (F4.blockElt (fi 1)) * (F4.reeTorus a (fi 0) u * F4.reeTorus a (fi 1) v) *
        (nrep F4.tag K (F4.blockElt (fi 1)))⁻¹ =
      (nrep F4.tag K (F4.blockElt (fi 1)) * F4.reeTorus a (fi 0) u *
        (nrep F4.tag K (F4.blockElt (fi 1)))⁻¹) *
      (nrep F4.tag K (F4.blockElt (fi 1)) * F4.reeTorus a (fi 1) v *
        (nrep F4.tag K (F4.blockElt (fi 1)))⁻¹) := by group
    _ = (F4.reeTorus a (fi 0) u *
          F4.reeTorus a (fi 1) (u ^ (2 + 2 * ((ReeTag.F4.prime ^ a : ℕ) : ℤ)))) *
        (F4.reeTorus a (fi 1) v)⁻¹ := by rw [h3, h4]
    _ = F4.reeTorus a (fi 0) u *
        F4.reeTorus a (fi 1) (u ^ (2 + 2 * ((ReeTag.F4.prime ^ a : ℕ) : ℤ)) * v⁻¹) := by
      rw [reeTorus_mul, reeTorus_inv, mul_assoc]

theorem tp4Hom_conj_zero
    [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1)) (b : Fin 2 → rootsOfUnity p K) :
    ((nrep F4.tag K (F4.blockElt (fi 0)) : adjointGroup F4.tag K) : ModGL F4.tag K) *
        tp4Hom p a K b *
      ((nrep F4.tag K (F4.blockElt (fi 0)) : adjointGroup F4.tag K) : ModGL F4.tag K)⁻¹ =
      torusPair a ((((b 0 : rootsOfUnity p K) : Kˣ))⁻¹ * ((b 1 : rootsOfUnity p K) : Kˣ),
        ((b 1 : rootsOfUnity p K) : Kˣ)) := by
  have h := congrArg (Subtype.val : adjointGroup F4.tag K → ModGL F4.tag K)
    (conj_nrep_zero (a := a) hK ((b 0 : rootsOfUnity p K) : Kˣ) ((b 1 : rootsOfUnity p K) : Kˣ))
  rw [tp4Hom_apply, torusPair_eq_reeTorus, torusPair_eq_reeTorus]
  exact h

theorem tp4Hom_conj_one
    [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1)) (b : Fin 2 → rootsOfUnity p K) :
    ((nrep F4.tag K (F4.blockElt (fi 1)) : adjointGroup F4.tag K) : ModGL F4.tag K) *
        tp4Hom p a K b *
      ((nrep F4.tag K (F4.blockElt (fi 1)) : adjointGroup F4.tag K) : ModGL F4.tag K)⁻¹ =
      torusPair a (((b 0 : rootsOfUnity p K) : Kˣ),
        ((b 0 : rootsOfUnity p K) : Kˣ) ^ (2 + 2 * ((ReeTag.F4.prime ^ a : ℕ) : ℤ)) *
          ((b 1 : rootsOfUnity p K) : Kˣ)⁻¹) := by
  have h := congrArg (Subtype.val : adjointGroup F4.tag K → ModGL F4.tag K)
    (conj_nrep_one (a := a) hK ((b 0 : rootsOfUnity p K) : Kˣ) ((b 1 : rootsOfUnity p K) : Kˣ))
  rw [tp4Hom_apply, torusPair_eq_reeTorus, torusPair_eq_reeTorus]
  exact h

theorem tp4Hom_mem_torusGroup
    (b : Fin 2 → rootsOfUnity p K) :
    tp4Hom p a K b ∈ torusGroup F4.tag K := by
  rw [tp4Hom_apply, torusPair_apply]
  exact mul_mem (mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _))
    (mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _))

@[expose] noncomputable def tp4M
    [Finite K] [CharP K ReeTag.F4.prime] (h : F4Param p a K) :
    (Fin 2 → rootsOfUnity p K) →* ↥(F4.reeGamma K a) :=
  (tp4Hom p a K).codRestrict _ (fun _ => torusPair_mem_reeGamma a h.card _)

@[expose] noncomputable def Tp4
    [Finite K] [CharP K ReeTag.F4.prime] (h : F4Param p a K) :
    Subgroup ↥(F4.reeGamma K a) :=
  (tp4M h).range

@[expose] noncomputable def nGamma
    [Finite K] [CharP K ReeTag.F4.prime] :
    F4.relWeylRee →* ↥(F4.reeGamma K a) :=
  (reeFixedEquivReeGamma K a).toMonoidHom.comp (relNrepHom K a)

section Gamma

variable [Finite K] [CharP K ReeTag.F4.prime] (h : F4Param p a K)

theorem coe_tp4M
    (b : Fin 2 → rootsOfUnity p K) :
    ((tp4M h b : ↥(F4.reeGamma K a)) : ModGL F4.tag K) = tp4Hom p a K b := rfl

theorem coe_nGamma
    (w : F4.relWeylRee) :
    ((nGamma w : ↥(F4.reeGamma K a)) : ModGL F4.tag K) =
      ((nrep F4.tag K w.1 : adjointGroup F4.tag K) : ModGL F4.tag K) := rfl

include h in
theorem tp4M_injective :
    Function.Injective (tp4M h) := by
  refine (injective_iff_map_eq_one (tp4M h)).2 fun b hb => ?_
  have h1 : tp4Hom p a K b = 1 := congrArg (Subtype.val : ↥(F4.reeGamma K a) → ModGL F4.tag K) hb
  rw [tp4Hom_apply] at h1
  obtain ⟨h0, h1'⟩ := torusPair_eq_one h.card h1
  funext i
  fin_cases i
  · exact Subtype.ext h0
  · exact Subtype.ext h1'

theorem tp4M_mem_Tp4
    (b : Fin 2 → rootsOfUnity p K) : tp4M h b ∈ Tp4 h := ⟨b, rfl⟩

theorem Tp4_comm
    (s t : ↥(F4.reeGamma K a)) (hs : s ∈ Tp4 h) (ht : t ∈ Tp4 h) :
    s * t = t * s := by
  obtain ⟨b, rfl⟩ := hs
  obtain ⟨b', rfl⟩ := ht
  rw [← map_mul, ← map_mul, mul_comm]

theorem Tp4_exp
    (t : ↥(F4.reeGamma K a)) (ht : t ∈ Tp4 h) : t ^ p = 1 := by
  obtain ⟨b, rfl⟩ := ht
  rw [← map_pow]
  have : b ^ p = 1 := funext fun i => Subtype.ext (by
    simpa using (mem_rootsOfUnity p _).mp (b i).2)
  rw [this, map_one]

include h in
theorem exists_conj_into_Tp4_of
    (hSyl : ∀ R : Subgroup (ModGL F4.tag K), R ≤ F4.reeGamma K a → IsPGroup p R →
      ∃ g ∈ F4.reeGamma K a, R.map (MulAut.conj g).toMonoidHom ≤ F4.reeFixedTorus K a)
    (hCoord : ∀ x ∈ F4.reeFixedTorus K a, ∃ u v : Kˣ, torusPair a (u, v) = x)
    (X : Subgroup ↥(F4.reeGamma K a)) (hX : ∀ x ∈ X, x ^ p = 1) :
    ∃ g : ↥(F4.reeGamma K a), ∀ x ∈ X, g * x * g⁻¹ ∈ Tp4 h := by
  have hP : IsPGroup p X := fun x => ⟨1, Subtype.ext (by simpa using hX x.1 x.2)⟩
  have hRp : IsPGroup p (X.map (F4.reeGamma K a).subtype) :=
    hP.of_equiv (X.equivMapOfInjective (F4.reeGamma K a).subtype Subtype.val_injective)
  obtain ⟨g, hgΓ, hg⟩ := hSyl (X.map (F4.reeGamma K a).subtype) (Subgroup.map_subtype_le X) hRp
  refine ⟨⟨g, hgΓ⟩, fun x hx => ?_⟩
  have hmem : g * ((x : ↥(F4.reeGamma K a)) : ModGL F4.tag K) * g⁻¹ ∈ F4.reeFixedTorus K a :=
    hg ⟨(x : ModGL F4.tag K), ⟨x, hx, rfl⟩, rfl⟩
  obtain ⟨u, v, huv⟩ := hCoord _ hmem
  have hxp : ((x : ↥(F4.reeGamma K a)) : ModGL F4.tag K) ^ p = 1 := by
    simpa using congrArg (Subtype.val : ↥(F4.reeGamma K a) → ModGL F4.tag K) (hX x hx)
  have hpow : torusPair a (u ^ p, v ^ p) = 1 := by
    have h1 : (g * ((x : ↥(F4.reeGamma K a)) : ModGL F4.tag K) * g⁻¹) ^ p = 1 := by
      rw [conj_pow, hxp, mul_one, mul_inv_cancel]
    calc torusPair a (u ^ p, v ^ p) = torusPair a ((u, v) ^ p) := rfl
      _ = (torusPair a (u, v)) ^ p := map_pow _ _ _
      _ = (g * ((x : ↥(F4.reeGamma K a)) : ModGL F4.tag K) * g⁻¹) ^ p := by rw [huv]
      _ = 1 := h1
  obtain ⟨hu, hv⟩ := torusPair_eq_one h.card hpow
  refine ⟨![⟨u, (mem_rootsOfUnity p u).2 hu⟩, ⟨v, (mem_rootsOfUnity p v).2 hv⟩], Subtype.ext ?_⟩
  show tp4Hom p a K _ = g * ((x : ↥(F4.reeGamma K a)) : ModGL F4.tag K) * g⁻¹
  rw [tp4Hom_apply]
  exact huv

end Gamma

end Torus

end CFSG.RankThree.PartOne.KFU
