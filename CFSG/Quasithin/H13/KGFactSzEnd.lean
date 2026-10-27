module

public import CFSG.Quasithin.H13.A6S13816Sz
public import CFSG.Quasithin.EmptyFaithful.SzN15Nat
public import CFSG.LieType.Ree.SuzukiOvoidWeyl

public section

namespace CFSG.Quasithin.H13.KGSz

open Matrix CFSG.Blueprint CFSG.LieType.Ree CFSG.Quasithin

variable {a : ℕ} {K : Type} [Field K]

theorem suzukiS_one_zero_fix [CharP K 2] {v : Fin 4 → K} (h : (suzukiS a 1 0) *ᵥ v = v) :
    v = Pi.single 3 (v 3) := by
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp [suzukiS, suzukiN, mulVec, dotProduct, Fin.sum_univ_four] at h1 h2 h3
  rw [h1, h2, zero_add, zero_add] at h3
  ext i
  fin_cases i <;> simp [h1, h2, h3]

theorem suzukiS_e4 (u v c : K) : (suzukiS a u v) *ᵥ (Pi.single 3 c) = Pi.single 3 c := by
  ext i
  fin_cases i <;> simp [suzukiS, mulVec, dotProduct, Fin.sum_univ_four]

theorem suzukiD_e4 (l : Kˣ) (c : K) : (suzukiD a l) *ᵥ (Pi.single 3 c) =
    Pi.single 3 (((l ^ (-1 - (2 ^ a : ℤ)) : Kˣ) : K) * c) := by
  ext i
  fin_cases i <;> simp [suzukiD, mulVec, dotProduct, Fin.sum_univ_four]

theorem suzukiW_e4 (c : K) : (suzukiW K) *ᵥ (Pi.single 3 c) = Pi.single 0 c := by
  rw [suzukiW_mulVec]
  ext i
  fin_cases i <;> simp

theorem suzukiS_e1 (u v c : K) : (suzukiS a u v) *ᵥ (Pi.single 0 c) =
    ![c, u * c, v * c, suzukiN a u v * c] := by
  ext i
  fin_cases i <;> simp [suzukiS, mulVec, dotProduct, Fin.sum_univ_four]

@[expose] def sterm (g : suzukiGroup a K) (c : K) : Fin 4 → K :=
  ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ (Pi.single 3 c)

theorem sz_induction [CharP K 2] {P : (Fin 4 → K) → Prop}
    (hadd : ∀ x y, P x → P y → P (x + y)) (hT : ∀ (g : suzukiGroup a K) (c : K), P (sterm g c))
    (x : Fin 4 → K) : P x := by
  have hW : ∀ c : K, sterm (suzukiWElt a K) c = ![c, 0, 0, 0] := by
    intro c
    rw [sterm, coe_suzukiWElt, suzukiW_e4]
    ext i
    fin_cases i <;> simp
  have hSW : ∀ u v c : K, sterm (suzukiSElt a K u v * suzukiWElt a K) c =
      ![c, u * c, v * c, suzukiN a u v * c] := by
    intro u v c
    rw [sterm, Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec, coe_suzukiSElt, coe_suzukiWElt,
      suzukiW_e4, suzukiS_e1]
  have h1 : ∀ c : K, sterm (1 : suzukiGroup a K) c = ![0, 0, 0, c] := by
    intro c
    rw [sterm, Subgroup.coe_one, Units.val_one, one_mulVec]
    ext i
    fin_cases i <;> simp
  have hN10 : suzukiN a (1 : K) 0 = 1 := by simp [suzukiN]
  have hN01 : suzukiN a (0 : K) 1 = 1 := by simp [suzukiN]
  have hx : x = sterm (suzukiWElt a K) (x 0) +
      (sterm (suzukiSElt a K 1 0 * suzukiWElt a K) (x 1) + sterm (suzukiWElt a K) (x 1) +
        sterm (1 : suzukiGroup a K) (x 1)) +
      (sterm (suzukiSElt a K 0 1 * suzukiWElt a K) (x 2) + sterm (suzukiWElt a K) (x 2) +
        sterm (1 : suzukiGroup a K) (x 2)) + sterm (1 : suzukiGroup a K) (x 3) := by
    rw [hW, hW, hW, hSW, hSW, h1, h1, h1, hN10, hN01]
    ext i
    fin_cases i <;> simp [CharTwo.add_self_eq_zero]
  rw [hx]
  exact hadd _ _ (hadd _ _ (hadd _ _ (hT _ _) (hadd _ _ (hadd _ _ (hT _ _) (hT _ _)) (hT _ _)))
    (hadd _ _ (hadd _ _ (hT _ _) (hT _ _)) (hT _ _))) (hT _ _)

theorem coprime_two_pow (a : ℕ) : (2 ^ (2 * a + 1) - 1).Coprime (2 ^ a + 1) := by
  obtain ⟨y, hy⟩ : ∃ y, 2 ^ a = y + 1 := ⟨2 ^ a - 1, by have := Nat.one_le_two_pow (n := a); omega⟩
  have h1 : 2 ^ (2 * a + 1) - 1 = 1 + (2 * y) * (2 ^ a + 1) := by
    rw [pow_succ, pow_mul', hy]
    apply Nat.sub_eq_of_eq_add
    ring
  rw [h1, Nat.coprime_add_mul_right_left]
  exact Nat.coprime_one_left _

theorem exists_zpow_eq [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (c : Kˣ) :
    ∃ l : Kˣ, l ^ (-1 - (2 ^ a : ℤ)) = c := by
  classical
  have := Fintype.ofFinite K
  have hcop : (Nat.card Kˣ).Coprime (2 ^ a + 1) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
    exact coprime_two_pow a
  obtain ⟨l, hl⟩ := (Nat.Coprime.pow_left_bijective hcop).2 c⁻¹
  refine ⟨l, ?_⟩
  rw [show (-1 - (2 ^ a : ℤ)) = -((2 ^ a + 1 : ℕ) : ℤ) by push_cast; ring, _root_.zpow_neg,
    zpow_natCast]
  have hl' : l ^ (2 ^ a + 1) = c⁻¹ := hl
  rw [hl', inv_inv]

theorem coprime_three_pow (a e : ℕ) : (3 ^ e).Coprime (2 ^ (2 * a + 1) - 1) := by
  refine Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr ?_)
  have h2 : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have h1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  omega

theorem eq_smul_of_commute [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (g : (Fin 4 → K) →+ (Fin 4 → K))
    (hg : ∀ (h : suzukiGroup a K) (x : Fin 4 → K),
      g (((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ x) =
        ((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ g x) :
    ∃ μ : K, ∀ x, g x = μ • x := by
  have : CharP K 2 := (suzuki_frobenius_exponents a K hK).1
  have hfix : (suzukiS a 1 0) *ᵥ g (Pi.single 3 1) = g (Pi.single 3 1) := by
    have := hg (suzukiSElt a K 1 0) (Pi.single 3 1)
    rw [coe_suzukiSElt, suzukiS_e4] at this
    exact this.symm
  set μ := g (Pi.single 3 1) 3 with hμ
  have h4 : g (Pi.single 3 1) = Pi.single 3 μ := suzukiS_one_zero_fix hfix
  have hc : ∀ c : K, g (Pi.single 3 c) = Pi.single 3 (μ * c) := by
    intro c
    by_cases hc0 : c = 0
    · rw [hc0, Pi.single_zero, map_zero, mul_zero, Pi.single_zero]
    · obtain ⟨l, hl⟩ := exists_zpow_eq hK (Units.mk0 c hc0)
      have he : Pi.single 3 c = suzukiD a l *ᵥ Pi.single 3 (1 : K) := by
        rw [suzukiD_e4, hl, Units.val_mk0, mul_one]
      rw [he, ← coe_suzukiDElt a K l, hg, h4, coe_suzukiDElt, suzukiD_e4, hl, Units.val_mk0,
        mul_comm]
  refine ⟨μ, fun x => sz_induction (a := a) (P := fun x => g x = μ • x)
    (fun x y hx hy => by rw [map_add, hx, hy, smul_add]) (fun h c => ?_) x⟩
  show g (sterm h c) = μ • sterm h c
  rw [sterm, hg, hc, ← smul_eq_mul, Pi.single_smul, mulVec_smul]

theorem trivial_of_natReal {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} {U C : Subgroup W} [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {π : ↥(suzukiGroup a K) →* ↥L} (R : SzN15.NatReal L U C (suzukiGroup a K) π)
    {c : MulAut W} {e : ℕ} (he : c ^ 3 ^ e = 1) (hcU : ∀ u ∈ U, c u ∈ U)
    (hcC : ∀ u ∈ C, c u ∈ C) (hcL : ∀ h ∈ L, c * h = h * c) : ∀ u ∈ U, c u * u⁻¹ ∈ C := by
  obtain ⟨-, hUinv, -, β, hβs, hβk, hβe⟩ := R
  let cU : ↥U →* ↥U :=
    { toFun := fun u => ⟨c u, hcU u u.2⟩
      map_one' := Subtype.ext (map_one c)
      map_mul' := fun u v => Subtype.ext (map_mul c (u : W) v) }
  have hcU' : ∀ u : ↥U, ((cU u : ↥U) : W) = c u := fun u => rfl
  have hker : β.ker ≤ (β.comp cU).ker := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    rw [MonoidHom.comp_apply]
    exact (hβk _).mpr (hcC _ ((hβk u).mp hu))
  set γ := MonoidHom.liftOfSurjective β hβs ⟨β.comp cU, hker⟩ with hγdef
  have hγ : ∀ u, γ (β u) = β (cU u) := fun u =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ u
  have hγcomm : ∀ (h : suzukiGroup a K) (m : Multiplicative (Fin 4 → K)),
      γ (natAct (suzukiGroup a K) h m) = natAct (suzukiGroup a K) h (γ m) := by
    intro h m
    obtain ⟨u, rfl⟩ := hβs m
    have hu : ((π h : ↥L) : MulAut W) u ∈ U := hUinv (π h) u u.2
    have hcu : ((π h : ↥L) : MulAut W) (cU u) ∈ U := hUinv (π h) _ (cU u).2
    have e3 : (⟨((π h : ↥L) : MulAut W) (cU u), hcu⟩ : ↥U) = cU ⟨_, hu⟩ := by
      apply Subtype.ext
      show ((π h : ↥L) : MulAut W) (c u) = c (((π h : ↥L) : MulAut W) u)
      rw [show c (((π h : ↥L) : MulAut W) u) = (c * (π h : MulAut W)) u from rfl,
        hcL _ (π h).2]
      rfl
    rw [← hβe h u hu, hγ, hγ, ← hβe h (cU u) hcu, e3]
  let g : (Fin 4 → K) →+ (Fin 4 → K) :=
    { toFun := fun x => Multiplicative.toAdd (γ (Multiplicative.ofAdd x))
      map_zero' := by simp
      map_add' := fun x y => by simp [ofAdd_add] }
  obtain ⟨μ, hμ⟩ := eq_smul_of_commute hK g fun h x =>
    congrArg Multiplicative.toAdd (hγcomm h (Multiplicative.ofAdd x))
  have hγμ : ∀ m, γ m = Multiplicative.ofAdd (μ • Multiplicative.toAdd m) := fun m =>
    congrArg Multiplicative.ofAdd (hμ (Multiplicative.toAdd m))
  have hpow : ∀ k : ℕ, ∀ u : ↥U, ∃ hk : (c ^ k) u ∈ U,
      β ⟨(c ^ k) u, hk⟩ = Multiplicative.ofAdd (μ ^ k • Multiplicative.toAdd (β u)) := by
    intro k
    induction k with
    | zero => intro u; exact ⟨u.2, by simp⟩
    | succ k ih =>
      intro u
      obtain ⟨hk, hβk'⟩ := ih u
      have hck : (c ^ (k + 1)) u = c ((c ^ k) u) := by rw [pow_succ', MulAut.mul_apply]
      have hmem : (c ^ (k + 1)) u ∈ U := hck ▸ hcU _ hk
      refine ⟨hmem, ?_⟩
      have h1 : (⟨(c ^ (k + 1)) u, hmem⟩ : ↥U) = cU ⟨(c ^ k) u, hk⟩ := Subtype.ext hck
      rw [h1, ← hγ, hγμ, hβk', toAdd_ofAdd, smul_smul, pow_succ']
  have hμ1 : μ = 1 := by
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd (Pi.single 3 1))
    obtain ⟨hk, h3⟩ := hpow (3 ^ e) u
    have h4 : (⟨(c ^ 3 ^ e) u, hk⟩ : ↥U) = u :=
      Subtype.ext (show (c ^ 3 ^ e) (u : W) = u by rw [he]; rfl)
    rw [h4, hu, toAdd_ofAdd] at h3
    have h5 := congrArg (fun m : Multiplicative (Fin 4 → K) => Multiplicative.toAdd m 3) h3
    simp only [toAdd_ofAdd, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h5
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      rw [zero_pow (pow_ne_zero _ (by norm_num))] at h5
      exact one_ne_zero h5
    have hν : (Units.mk0 μ hμ0) ^ 3 ^ e = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val,
      Units.val_mk0, ← h5, Units.val_one])
    have hcard : Nat.card Kˣ = 2 ^ (2 * a + 1) - 1 := by rw [Nat.card_units, hK]
    have h1 := orderOf_dvd_of_pow_eq_one hν
    have h2 : orderOf (Units.mk0 μ hμ0) ∣ 2 ^ (2 * a + 1) - 1 := hcard ▸ orderOf_dvd_natCard _
    have h3 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 (coprime_three_pow a e))
      h2
    have h6 : Units.mk0 μ hμ0 = 1 := orderOf_eq_one_iff.mp h3
    exact congrArg Units.val h6
  intro u hu
  have h1 : β (cU ⟨u, hu⟩) = β ⟨u, hu⟩ := by
    rw [← hγ, hγμ, hμ1, one_smul, ofAdd_toAdd]
  have h2 : β (cU ⟨u, hu⟩ * (⟨u, hu⟩ : ↥U)⁻¹) = 1 := by rw [map_mul, map_inv, h1, mul_inv_cancel]
  exact (hβk _).mp h2

theorem szEnd_holds : A6.SzEnd := by
  intro W _ _ L U C f hnat c hc3 hcU hcC hcL
  obtain ⟨a, -, rfl, K, _, _, hK, π, hπ⟩ := hnat
  obtain ⟨e, he⟩ := hc3
  exact trivial_of_natReal hK (SzN15.NatReal.of_realizesVia hπ) he hcU hcC hcL

end CFSG.Quasithin.H13.KGSz
