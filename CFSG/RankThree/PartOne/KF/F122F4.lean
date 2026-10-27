module

public import CFSG.RankThree.PartOne.KF.F122ExcEngine
public import CFSG.RankThree.PartOne.S11c.Sec66F4ReeK1
public import CFSG.RankThree.PartOne.RF4.FinalSec66
public import CFSG.RankThree.PartOne.KF.F122Sp

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Simplicity CFSG.LieType.Ree.LargeReeCover
open CFSG.Assembly.RankThreeEven (localRank)

section Lower

variable {K : Type} [Field K] (t : ReeTag) (a : ℕ)

theorem reeTorus_pow_conj
    (j : Fin t.tag.rank) (u : Kˣ) (β : Root t.tag) (c : K) (n : ℕ) :
    (t.reeTorus a j u) ^ n * (rootOperatorFamily t.tag).eltElement β c * ((t.reeTorus a j u) ^ n)⁻¹ =
      (rootOperatorFamily t.tag).eltElement β
        (((((u ^ (t.cartanPair j β.1 + ((t.prime ^ a : ℕ) : ℤ) * t.cartanPair (t.perm j) β.1) :
          Kˣ) : K)) ^ n) * c) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : ∀ T S x : adjointGroup t.tag K, (T * S) * x * (T * S)⁻¹ = T * (S * x * S⁻¹) * T⁻¹ :=
      fun T S x => by group
    rw [pow_succ', e, ih, t.reeTorus_conj a j u β]
    congr 1
    rw [pow_succ', mul_assoc]

theorem reeTorus_commute
    (j j' : Fin t.tag.rank) (u v : Kˣ) :
    Commute (t.reeTorus a j u) (t.reeTorus a j' v) := by
  unfold ReeTag.reeTorus
  exact (Commute.mul_left (torusElement_commute _ _ _ _) (torusElement_commute _ _ _ _)).mul_right
    (Commute.mul_left (torusElement_commute _ _ _ _) (torusElement_commute _ _ _ _))

theorem reeTorus_mul
    (j : Fin t.tag.rank) (u v : Kˣ) :
    t.reeTorus a j (u * v) = t.reeTorus a j u * t.reeTorus a j v := by
  have h1 : ∀ (i : Fin t.tag.rank) (x y : Kˣ),
      torusElement t.tag K i (x * y) = torusElement t.tag K i x * torusElement t.tag K i y :=
    fun i x y => Subtype.ext (torusElt_mul i x y)
  simp only [ReeTag.reeTorus, h1, mul_pow]
  exact (Commute.mul_mul_mul_comm (torusElement_commute _ _ _ _) _ _)

theorem reeTorus_one
    (j : Fin t.tag.rank) : t.reeTorus a j (1 : Kˣ) = 1 := by
  have h1 : ∀ i : Fin t.tag.rank, torusElement t.tag K i (1 : Kˣ) = 1 :=
    fun i => Subtype.ext (torusElt_one i)
  simp only [ReeTag.reeTorus, h1, one_pow, mul_one]

theorem reeTorus_pow
    (j : Fin t.tag.rank) (u : Kˣ) (n : ℕ) :
    (t.reeTorus a j u) ^ n = t.reeTorus a j (u ^ n) := by
  induction n with
  | zero => simp [reeTorus_one]
  | succ n ih => rw [pow_succ, ih, pow_succ, reeTorus_mul]

theorem F4_reeTorus_indep
    {p : ℕ} (hp : p.Prime) (hpk : p ∣ 2 ^ (2 * a + 1) - 1)
    {u₀ : Kˣ} (hu₀ : orderOf u₀ = p) (m n : ℕ)
    (h : (ReeTag.F4.reeTorus a (f4i 0) u₀) ^ m * (ReeTag.F4.reeTorus a (f4i 1) u₀) ^ n = 1) :
    p ∣ m ∧ p ∣ n := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have key : ∀ β : Root ReeTag.F4.tag, (p : ℤ) ∣
      (ReeTag.F4.cartanPair (f4i 0) β.1 + ((2 ^ a : ℕ) : ℤ) *
        ReeTag.F4.cartanPair (ReeTag.F4.perm (f4i 0)) β.1) * m +
      (ReeTag.F4.cartanPair (f4i 1) β.1 + ((2 ^ a : ℕ) : ℤ) *
        ReeTag.F4.cartanPair (ReeTag.F4.perm (f4i 1)) β.1) * n := by
    intro β
    have hx : ((ReeTag.F4.reeTorus a (f4i 0) u₀) ^ m * (ReeTag.F4.reeTorus a (f4i 1) u₀) ^ n) *
        (rootOperatorFamily ReeTag.F4.tag).eltElement β (1 : K) *
        ((ReeTag.F4.reeTorus a (f4i 0) u₀) ^ m * (ReeTag.F4.reeTorus a (f4i 1) u₀) ^ n)⁻¹ =
        (rootOperatorFamily ReeTag.F4.tag).eltElement β (1 : K) := by
      rw [h]
      group
    have e2 : ∀ x T S : adjointGroup ReeTag.F4.tag K, (T * S) * x * (T * S)⁻¹ =
        T * (S * x * S⁻¹) * T⁻¹ := fun x T S => by group
    rw [e2, reeTorus_pow_conj ReeTag.F4 a (f4i 1) u₀ β 1 n,
      reeTorus_pow_conj ReeTag.F4 a (f4i 0) u₀ β _ m] at hx
    have hinj := eltElement_injective β hx
    have h3 : (u₀ ^ (ReeTag.F4.cartanPair (f4i 0) β.1 + ((ReeTag.F4.prime ^ a : ℕ) : ℤ) *
          ReeTag.F4.cartanPair (ReeTag.F4.perm (f4i 0)) β.1)) ^ m *
        (u₀ ^ (ReeTag.F4.cartanPair (f4i 1) β.1 + ((ReeTag.F4.prime ^ a : ℕ) : ℤ) *
          ReeTag.F4.cartanPair (ReeTag.F4.perm (f4i 1)) β.1)) ^ n = 1 := by
      apply Units.ext
      simpa [Units.val_mul, Units.val_pow_eq_pow_val] using hinj
    have h4 : u₀ ^ ((ReeTag.F4.cartanPair (f4i 0) β.1 + ((ReeTag.F4.prime ^ a : ℕ) : ℤ) *
          ReeTag.F4.cartanPair (ReeTag.F4.perm (f4i 0)) β.1) * m +
        (ReeTag.F4.cartanPair (f4i 1) β.1 + ((ReeTag.F4.prime ^ a : ℕ) : ℤ) *
          ReeTag.F4.cartanPair (ReeTag.F4.perm (f4i 1)) β.1) * n) = 1 := by
      rw [_root_.zpow_add, _root_.zpow_mul, _root_.zpow_mul, zpow_natCast, zpow_natCast]
      exact h3
    have h5 := orderOf_dvd_iff_zpow_eq_one.mpr h4
    rwa [hu₀] at h5
  have hE0 : ReeTag.F4.cartanPair (f4i 0) (Pi.single (f4i 0) 1) = 2 ∧
      ReeTag.F4.cartanPair (ReeTag.F4.perm (f4i 0)) (Pi.single (f4i 0) 1) = 0 ∧
      ReeTag.F4.cartanPair (f4i 1) (Pi.single (f4i 0) 1) = -1 ∧
      ReeTag.F4.cartanPair (ReeTag.F4.perm (f4i 1)) (Pi.single (f4i 0) 1) = 0 := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel
  have hE1 : ReeTag.F4.cartanPair (f4i 0) (Pi.single (f4i 1) 1) = -1 ∧
      ReeTag.F4.cartanPair (ReeTag.F4.perm (f4i 0)) (Pi.single (f4i 1) 1) = 0 ∧
      ReeTag.F4.cartanPair (f4i 1) (Pi.single (f4i 1) 1) = 2 ∧
      ReeTag.F4.cartanPair (ReeTag.F4.perm (f4i 1)) (Pi.single (f4i 1) 1) = -2 := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel
  have h0 := key ⟨Pi.single (f4i 0) 1, isRoot_single ReeTag.F4.tag (f4i 0)⟩
  have h1 := key ⟨Pi.single (f4i 1) 1, isRoot_single ReeTag.F4.tag (f4i 1)⟩
  simp only [hE0.1, hE0.2.1, hE0.2.2.1, hE0.2.2.2, hE1.1, hE1.2.1, hE1.2.2.1, hE1.2.2.2] at h0 h1
  have hθ : (2 * ((2 : ZMod p) ^ a) ^ 2 - 1 : ZMod p) = 0 := by
    have h1 := (ZMod.natCast_eq_zero_iff _ _).mpr hpk
    have h2 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
    rw [Nat.cast_sub h2] at h1
    push_cast at h1
    linear_combination h1
  have z0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h0
  have z1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h1
  push_cast at z0 z1
  have hm : (m : ZMod p) = 0 := by
    linear_combination (3 + 4 * (2 : ZMod p) ^ a) * (z1 + (2 - 2 * (2 : ZMod p) ^ a) * z0) +
      8 * (m : ZMod p) * hθ
  have hn : (n : ZMod p) = 0 := by linear_combination 2 * hm - z0
  exact ⟨(ZMod.natCast_eq_zero_iff _ _).mp hm, (ZMod.natCast_eq_zero_iff _ _).mp hn⟩

theorem two_le_localRank_reeFixed_F4
    [Finite K] [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {p : ℕ} (hp : p.Prime) (hpk : p ∣ 2 ^ (2 * a + 1) - 1) :
    2 ≤ localRank p ↥(reeFixed ReeTag.F4 K a) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hpcard : p ∣ Nat.card Kˣ := by rw [Nat.card_units, hK]; exact hpk
  obtain ⟨u₀, hu₀⟩ := exists_prime_orderOf_dvd_card' p hpcard
  have hu₀p : u₀ ^ p = 1 := by rw [← hu₀]; exact pow_orderOf_eq_one u₀
  let x₁ : reeFixed ReeTag.F4 K a :=
    ⟨ReeTag.F4.reeTorus a (f4i 0) u₀,
      ReeTag.F4.reeTorus_mem_reeFixed a hK f4i_zero_mem_longSet u₀⟩
  let x₂ : reeFixed ReeTag.F4 K a :=
    ⟨ReeTag.F4.reeTorus a (f4i 1) u₀,
      ReeTag.F4.reeTorus_mem_reeFixed a hK f4i_one_mem_longSet u₀⟩
  have hx₁p : x₁ ^ p = 1 := Subtype.ext (by
    change (ReeTag.F4.reeTorus a (f4i 0) u₀) ^ p = 1
    rw [reeTorus_pow, hu₀p, reeTorus_one])
  have hx₂p : x₂ ^ p = 1 := Subtype.ext (by
    change (ReeTag.F4.reeTorus a (f4i 1) u₀) ^ p = 1
    rw [reeTorus_pow, hu₀p, reeTorus_one])
  have hcomm : x₁ * x₂ = x₂ * x₁ := Subtype.ext (reeTorus_commute ReeTag.F4 a _ _ u₀ u₀).eq
  have indep : ∀ m n : ℕ, x₁ ^ m * x₂ ^ n = 1 → p ∣ m ∧ p ∣ n := fun m n h =>
    F4_reeTorus_indep a hp hpk hu₀ m n (by simpa using congrArg Subtype.val h)
  have hx₁1 : x₁ ≠ 1 := by
    intro h
    have := (indep 1 0 (by rw [h]; simp)).1
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have hord : orderOf x₁ = p := orderOf_eq_prime hx₁p hx₁1
  have hx₂A : x₂ ∉ Subgroup.zpowers x₁ := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h1 := zpow_mod_orderOf x₁ k
    rw [hord] at h1
    have h2 : (0 : ℤ) ≤ k % p := Int.emod_nonneg _ (by exact_mod_cast hp.ne_zero)
    have hk' : x₁ ^ ((k % (p : ℤ)).toNat) = x₂ := by
      rw [← hk, ← h1, ← zpow_natCast, Int.toNat_of_nonneg h2]
    have h3 := indep ((k % (p : ℤ)).toNat) (p - 1) (by
      rw [hk', ← pow_succ', Nat.sub_add_cancel hp.one_le, hx₂p])
    have h4 := Nat.le_of_dvd (by have := hp.two_le; omega) h3.2
    have := hp.two_le
    omega
  have hAc : ∀ x ∈ Subgroup.zpowers x₁, ∀ y ∈ Subgroup.zpowers x₁, x * y = y * x := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact (Commute.zpow_zpow_self x₁ i j).eq
  have hAp : ∀ x ∈ Subgroup.zpowers x₁, x ^ p = 1 := by
    rintro _ ⟨i, rfl⟩
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hx₁p,
      _root_.one_zpow]
  have hAcard : Nat.card (Subgroup.zpowers x₁) = p ^ 1 := by
    rw [Nat.card_zpowers, hord, pow_one]
  obtain ⟨R, -, hRle, hRcard, hRc, hRp⟩ := Sec66T.exists_elementary_ext hp hAc hAp hAcard hx₂A hx₂p
    (fun x hx => by
      obtain ⟨i, rfl⟩ := hx
      exact (Commute.zpow_left (show Commute x₁ x₂ from hcomm) i).eq)
  have hE : CFSG.Assembly.IsElemAbelian p R :=
    ⟨⟨⟨fun x y => Subtype.ext (hRc _ x.2 _ y.2)⟩⟩, fun y hy => hRp y hy⟩
  have hnorm : ∀ x : reeFixed ReeTag.F4 K a,
      ((x : adjointGroup ReeTag.F4.tag K) ∈ (nativeData ReeTag.F4.tag K).H) →
        x ∈ Subgroup.normalizer (reeUnipPart ReeTag.F4 K a : Set (reeFixed ReeTag.F4 K a)) := by
    intro x hxH
    rw [Subgroup.mem_normalizer_iff]
    intro s
    exact Subgroup.mem_normalizer_iff.mp
      (RootGroupData.H_le_normalizer_U (D := nativeData ReeTag.F4.tag K) hxH)
      (s : adjointGroup ReeTag.F4.tag K)
  have hREP : R ≤ Subgroup.normalizer (reeUnipPart ReeTag.F4 K a : Set (reeFixed ReeTag.F4 K a)) :=
    hRle.trans (sup_le
      ((Subgroup.zpowers_le).mpr (hnorm x₁ (ReeTag.F4.reeTorus_mem_H a (f4i 0) u₀)))
      ((Subgroup.zpowers_le).mpr (hnorm x₂ (ReeTag.F4.reeTorus_mem_H a (f4i 1) u₀))))
  have hU2 : IsPGroup 2 (reeUnipPart ReeTag.F4 K a) :=
    ((nativeRootSubgroups ReeTag.F4.tag K).isPGroup_U ReeTag.F4.prime).comap_of_injective _
      Subtype.val_injective
  exact CFSG.RankThree.PartTwo.Census.le_localRank_of_le_normalizer hp
    (reeUnipPart_ne_bot a) hU2 hE hRcard hREP

end Lower

open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_model_field_outer_group_and_inner_involutions
    large_Ree_full_inner_field_automorphism_normal_form)
open CFSG.RankThree.PartOne.Sec66T
open CFSG.RankThree.PartTwo.Census (localRank_eq_of_mulEquiv)

theorem kf122Row4_holds
    : KF122Row 4 := by
  intro G _ _ p L hp hp5 hmodel _ α hαp hαinn hLRA
  obtain ⟨f, hf1, hpq, hM⟩ := hmodel
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hR⟩ := lieModel_twistedF4_iff.mp hM
  obtain ⟨a, K, _, _, _, ha, hfa, hKcard, ⟨e⟩⟩ := reeF4_model_data hR
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hKcard
  have : Finite (F4.reeGamma K a) := Finite.of_equiv _ e.toEquiv
  have hα1 : α ≠ 1 := fun h => hαinn (h ▸ Subgroup.one_mem _)
  have hord : orderOf α = p := orderOf_eq_prime hαp hα1
  set α' : MulAut (F4.reeGamma K a) := MulAut.congr e α with hα'
  have hα'ord : orderOf α' = p := (orderOf_congr e α).trans hord
  have hα'p : α' ^ p = 1 := by rw [← hα'ord]; exact pow_orderOf_eq_one α'
  have hα'inn : α' ∉ (MulAut.conj : ↥(F4.reeGamma K a) →* MulAut ↥(F4.reeGamma K a)).range :=
    fun h => hαinn ((mem_innerAut_congr e α).mp h)
  obtain ⟨-, hNF, ⟨Ψ, hΨ⟩, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha K hK
  obtain ⟨⟨x, β⟩, hxβ, -⟩ := hNF α'
  have hΨα : Ψ ⟨x, β⟩ = α' := by rw [hΨ x β]; exact hxβ.symm
  let Θ : MulAut (F4.reeGamma K a) →* (K ≃+* K) :=
    SemidirectProduct.rightHom.comp Ψ.symm.toMonoidHom
  have hΘα : Θ α' = β := by
    show SemidirectProduct.rightHom (Ψ.symm α') = β
    rw [← hΨα, MulEquiv.symm_apply_apply]
    rfl
  have hβp : β ^ p = 1 := by
    rw [← hΘα, ← map_pow, hα'p, map_one]
  have hone : F4.reeGammaFieldAut K a 1 = 1 := by rw [← reeGammaFieldAutHom_apply, map_one]
  have hβ1 : β ≠ 1 := by
    intro h
    apply hα'inn
    rw [h, hone, mul_one] at hxβ
    exact ⟨x, hxβ.symm⟩
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  obtain ⟨g, hg⟩ := RF4.largeReeFieldAutCoset a ha K hK p hp hp5 β hβord α' hα'p ⟨x, hxβ⟩
  have hψ : (MulAut.conj g)⁻¹ * MulAut.congr e α * ((MulAut.conj g)⁻¹)⁻¹ =
      F4.reeGammaFieldAut K a β := by
    have : MulAut.congr e α = MulAut.conj g * F4.reeGammaFieldAut K a β * (MulAut.conj g)⁻¹ :=
      hg
    rw [this]
    group
  obtain ⟨b, hbp, hbcard, hchar, ⟨eC⟩⟩ := reeF4_fixed_data ha hK hp (by omega) hβord
  have hff' : f = p * (2 * b + 1) := by rw [mul_comm, hbp, hfa]
  have hpk : p ∣ 2 ^ (2 * b + 1) - 1 := dvd_two_pow_sub_one_of_mul hp (hff' ▸ hpq)
  have : Finite (fixSubfield β) := Subtype.finite
  have hlow : 2 ≤ localRank p ↥(F4.reeGamma (fixSubfield β) b) := by
    rw [← localRank_eq_of_mulEquiv (ReeTag.reeFixedEquivReeGamma (fixSubfield β) b) hp]
    exact two_le_localRank_reeFixed_F4 b hbcard hp hpk
  exact false_of_conj_fixed hp e hαp hαinn (MulAut.conj g)⁻¹ (F4.reeGammaFieldAut K a β)
    (by rw [hψ]) eC hlow hLRA

end CFSG.RankThree.PartOne
