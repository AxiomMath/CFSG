module

public import CFSG.RankThree.PartTwo.Sec14.Item148Res8ProofLin
import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofCent
import CFSG.RankThree.PartTwo.Sec14.Item148RankProofField
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri

public section

namespace CFSG.RankThree.PartTwo.Sec14.Item148Res8

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.IVK (fixedField)
open CFSG.RankThree.PartTwo.Sec19.Item19Res2Proof (subfieldProj subfieldProj_proj
  subfieldProj_injective card_projectiveSL_three_congr commutatorElement_mul_center)
open scoped commutatorElement

section Lift

variable {K : Type} [Field K]

theorem le_range_subfieldProj_of_fixed {σ : K ≃+* K} {Lb : Subgroup (projectiveSL 3 K)}
    (hLp : Group.IsPerfect Lb) (hfix : ∀ y ∈ Lb, fieldAut 3 K σ y = y) :
    Lb ≤ (subfieldProj σ).range := by
  have hcomm : ⁅Lb, Lb⁆ = Lb := by
    rw [← Subgroup.map_subtype_commutator, Group.IsPerfect.commutator_eq_top,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hz : ∀ r : SpecialLinearGroup (Fin 3) K, proj 3 K r ∈ Lb →
      r⁻¹ * SpecialLinearGroup.map σ.toRingHom r ∈
        Subgroup.center (SpecialLinearGroup (Fin 3) K) := by
    intro r hr
    have h1 := hfix _ hr
    rw [fieldAut_proj, proj_eq_proj_iff] at h1
    rw [← scalars_eq_center]
    have h2 := (scalars 3 K).inv_mem h1
    simpa using h2
  rw [← hcomm, Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨s, rfl⟩ := proj_surjective 3 K a
  obtain ⟨t, rfl⟩ := proj_surjective 3 K b
  have hfixc : SpecialLinearGroup.map σ.toRingHom ⁅s, t⁆ = ⁅s, t⁆ := by
    rw [map_commutatorElement]
    have e1 : SpecialLinearGroup.map σ.toRingHom s =
        s * (s⁻¹ * SpecialLinearGroup.map σ.toRingHom s) := by group
    have e2 : SpecialLinearGroup.map σ.toRingHom t =
        t * (t⁻¹ * SpecialLinearGroup.map σ.toRingHom t) := by group
    rw [e1, e2, commutatorElement_mul_center _ _ (hz s ha) (hz t hb)]
  obtain ⟨A₀, hA₀⟩ := CFSG.RankThree.PartTwo.KFacts.exists_sl_map_subtype_eq hfixc
  exact ⟨proj 3 _ A₀, by rw [subfieldProj_proj, hA₀, map_commutatorElement]⟩

end Lift

theorem not_isMulCommutative_of_six_dvd {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (h2 : 2 ∣ Nat.card Y) (h3 : 3 ∣ Nat.card Y) : ¬ IsMulCommutative Y := by
  intro hc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hn : (Subgroup.zpowers g).Normal :=
    ⟨fun x hx y => by rw [hc.is_comm.comm y x, mul_inv_cancel_right]; exact hx⟩
  rcases hn.eq_bot_or_eq_top with hb | ht
  · rw [Subgroup.zpowers_eq_bot] at hb
    rw [hb, orderOf_one] at hg
    norm_num at hg
  · have hcard : Nat.card Y = 2 := by
      rw [← Subgroup.card_top (G := Y), ← ht, Nat.card_zpowers, hg]
    rw [hcard] at h3
    norm_num at h3

section Transfer


theorem subfieldOver_of_linear {Γ : Type} [Group Γ] [Finite Γ]
    {X K H : Subgroup Γ} {σ : Γ} {n : ℕ} (hn : 1 ≤ n) (hX : Sec4.IsoLThreePi ↥X 2 (3 * n))
    (hq : 2 ^ (3 * n) % 3 = 1) (hind : KFacts.InducesStdKind X σ .field) (hσ3 : σ ^ 3 = 1)
    (hσN : σ ∈ Subgroup.normalizer (X : Set Γ)) (hKX : K ≤ X)
    (hKC : K ≤ Subgroup.centralizer ({σ} : Set Γ)) (hKs : IsSimpleGroup ↥K)
    (hK : Sec4.IsoLThreePi ↥K 2 n) (hKH : K ≤ H) (hHX : H ≤ X) :
    H = X ∨ (H ≤ Subgroup.normalizer (K : Set Γ) ∧ Nat.card H ∣ 3 * Nat.card K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcube : 2 ^ (3 * n) = (2 ^ n) ^ 3 := by rw [← pow_mul, mul_comm]
  have hmod : 2 ^ (3 * n) % 3 = 2 ^ n % 3 := by
    rw [hcube]
    exact Item148Rank.pow_three_mod_three148 _
  rcases hX with ⟨-, ⟨e⟩⟩ | ⟨hq', -⟩
  swap
  · omega
  rcases hK with ⟨hqK, ⟨eK⟩⟩ | ⟨hqK, -⟩
  swap
  · omega
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have h1 : n = 1 := by omega
    subst h1
    norm_num at hqK
  set F := GaloisField 2 (3 * n) with hFdef
  have hcardF : Nat.card F = 2 ^ (3 * n) := GaloisField.card 2 (3 * n) (by omega)
  obtain ⟨φ⟩ := CFSG.RankThree.PartTwo.KFacts.nonempty_projSL_mulEquiv 3 F
  set τ : ↥X ≃* projectiveSL 3 F := e.trans φ with hτ
  set α := X.normalizerMonoidHom ⟨σ, hσN⟩ with hα
  have hα3 : α ^ 3 = 1 := by
    rw [hα, ← map_pow]
    have : (⟨σ, hσN⟩ : Subgroup.normalizer (X : Set Γ)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hσ3)
    rw [this, map_one]
  have hout := not_isInnerAut_of_inducesStdKind_field148 hind hσN
  have hαk : ∀ k : ↥X, (k : Γ) ∈ K → α k = k := by
    intro k hk
    apply Subtype.ext
    show σ * (k : Γ) * σ⁻¹ = k
    rw [(Subgroup.mem_centralizer_singleton_iff.mp (hKC hk)).symm, mul_inv_cancel_right]
  have h2K : 2 ∣ Nat.card K := Item148Res5.two_dvd_card_of_isoLThreePi hn (Or.inl ⟨hqK, ⟨eK⟩⟩)
  obtain ⟨k₀, hk₀⟩ := exists_prime_orderOf_dvd_card' 2 h2K
  set t : ↥X := ⟨k₀, hKX k₀.2⟩ with ht
  have ht2 : t ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    have : (k₀ : Γ) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, ← hk₀, pow_orderOf_eq_one, Subgroup.coe_one]
    exact this
  have ht1 : t ≠ 1 := by
    intro h1
    have h2 : ((t : ↥X) : Γ) = 1 := congrArg Subtype.val h1
    have hk1 : k₀ = 1 := Subtype.ext h2
    rw [hk1, orderOf_one] at hk₀
    norm_num at hk₀
  have hαt : α t = t := hαk t k₀.2
  set β := MulAut.congr τ α with hβ
  have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, hα3, map_one]
  have hβout : ¬ KFacts.IsInnerAut β := fun hb =>
    hout ((KFacts.isInnerAut_congr τ α).mp hb)
  have hβt : β (τ t) = τ t := by
    change τ (α (τ.symm (τ t))) = τ t
    rw [MulEquiv.symm_apply_apply, hαt]
  have hτt2 : (τ t) ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  have hτt1 : τ t ≠ 1 := fun h1 => ht1 (τ.injective (h1.trans (map_one τ).symm))
  have hlin : β ∉ linearAutGroup 3 F := by
    intro hl
    obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.mp hl
    apply hβout
    rw [← hA]
    have h9 : 9 ∣ Nat.card F - 1 := by
      rw [hcardF]
      exact (Item148Res5.nine_dvd_of_two_pow_three_mul n).1 hq
    exact Sec19.Item19Res2Proof.isInnerAut_of_conjAut_fix_involution h9 (by rw [hA]; exact hβ3)
      hτt2 hτt1 (by rw [hA]; exact hβt)
  obtain ⟨σ', hσ', H₀, hβH⟩ :=
    CFSG.RankThree.PartTwo.KFacts.linear_order_three_field_descent le_rfl β hβ3 hlin
  set γ := conjAut 3 F H₀ with hγ
  set ψ : ↥X ≃* projectiveSL 3 F := τ.trans (γ⁻¹ : MulAut (projectiveSL 3 F)) with hψ
  have hψα : ∀ x : ↥X, ψ (α x) = fieldAut 3 F σ' (ψ x) := by
    intro x
    have h1 : β (τ x) = τ (α x) := by
      change τ (α (τ.symm (τ x))) = τ (α x)
      rw [MulEquiv.symm_apply_apply]
    have h2 : fieldAut 3 F σ' = γ⁻¹ * β * γ := by rw [hβH]; group
    change γ⁻¹ (τ (α x)) = fieldAut 3 F σ' (γ⁻¹ (τ x))
    rw [h2, ← h1]
    change γ⁻¹ (β (τ x)) = γ⁻¹ (β (γ (γ⁻¹ (τ x))))
    rw [MulAut.apply_inv_self]
  have hFσ : Nat.card (fixedField σ') = 2 ^ n := by
    have h1 := CFSG.GH74.GLS.IVK.fixedField_card_pow σ'
    rw [hσ', hcardF, hcube] at h1
    exact Nat.pow_left_injective (by norm_num) h1
  set K' := (K.subgroupOf X).map ψ.toMonoidHom with hK'
  set H' := (H.subgroupOf X).map ψ.toMonoidHom with hH'
  have hcardK' : Nat.card K' = Nat.card K := by
    rw [hK', Subgroup.card_map_of_injective ψ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKX).toEquiv]
  have hcardH' : Nat.card H' = Nat.card H := by
    rw [hH', Subgroup.card_map_of_injective ψ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHX).toEquiv]
  have hK'fix : ∀ y ∈ K', fieldAut 3 F σ' y = y := by
    rintro _ ⟨k, hk, rfl⟩
    change fieldAut 3 F σ' (ψ k) = ψ k
    rw [← hψα, hαk k (Subgroup.mem_subgroupOf.mp hk)]
  have h3K : 3 ∣ Nat.card K :=
    Sec19.Step1914TriProof.three_dvd_card_of_isoLThreePi hn (Or.inl ⟨hqK, ⟨eK⟩⟩)
  have hKnc : ¬ IsMulCommutative ↥K := not_isMulCommutative_of_six_dvd h2K h3K
  have hKp : Group.IsPerfect ↥K := TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hKnc
  have hK'p : Group.IsPerfect K' := by
    have e1 : ↥K ≃* K' := (Subgroup.subgroupOfEquivOfLe hKX).symm.trans
      ((K.subgroupOf X).equivMapOfInjective ψ.toMonoidHom ψ.injective)
    exact Group.IsPerfect.ofSurjective (f := e1.toMonoidHom) e1.surjective
  have hcardP : Nat.card (subfieldProj σ').range = Nat.card K := by
    rw [← (Nat.card_congr (MonoidHom.ofInjective (subfieldProj_injective σ')).toEquiv),
      Nat.card_congr eK.toEquiv]
    have e2 := CFSG.RankThree.PartTwo.KFacts.nonempty_projSL_mulEquiv 3 (GaloisField 2 n)
    obtain ⟨e2⟩ := e2
    rw [Nat.card_congr e2.toEquiv]
    exact card_projectiveSL_three_congr (hFσ.trans (GaloisField.card 2 n (by omega)).symm)
  have hK'eq : K' = (subfieldProj σ').range := by
    refine Subgroup.eq_of_le_of_card_ge (le_range_subfieldProj_of_fixed hK'p hK'fix) ?_
    rw [hcardP, hcardK']
  have hKH' : (subfieldProj σ').range ≤ H' := by
    rw [← hK'eq, hK', hH']
    exact Subgroup.map_mono (fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hKH (Subgroup.mem_subgroupOf.mp hx)))
  have hmemK' : ∀ x : ↥X, ψ x ∈ K' ↔ (x : Γ) ∈ K := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := ψ.injective hyx
      rw [← this]
      exact Subgroup.mem_subgroupOf.mp hy
    · intro hx
      exact ⟨x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  rcases overgroup_subfieldProj hσ' hn2 hFσ hqK H' hKH' with htop | ⟨hnorm, hdvd⟩
  · left
    apply le_antisymm hHX
    intro x hx
    have : ψ ⟨x, hx⟩ ∈ H' := htop ▸ Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := this
    have hyx' : y = ⟨x, hx⟩ := ψ.injective hyx
    rw [hyx'] at hy
    exact Subgroup.mem_subgroupOf.mp hy
  · right
    refine ⟨?_, ?_⟩
    · intro h hh
      have hhX := hHX hh
      have hψh : ψ ⟨h, hhX⟩ ∈
          Subgroup.normalizer ((subfieldProj σ').range : Set (projectiveSL 3 F)) :=
        hnorm ⟨⟨h, hhX⟩, Subgroup.mem_subgroupOf.mpr hh, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro k
      constructor
      · intro hk
        have hkX := hKX hk
        have hconj : h * k * h⁻¹ ∈ X := X.mul_mem (X.mul_mem hhX hkX) (X.inv_mem hhX)
        have h1 : ψ ⟨k, hkX⟩ ∈ (subfieldProj σ').range := by
          rw [← hK'eq]; exact (hmemK' _).mpr hk
        have h2 := (Subgroup.mem_normalizer_iff.mp hψh (ψ ⟨k, hkX⟩)).mp h1
        have e : ψ ⟨h, hhX⟩ * ψ ⟨k, hkX⟩ * (ψ ⟨h, hhX⟩)⁻¹ = ψ ⟨h * k * h⁻¹, hconj⟩ := by
          rw [← map_mul, ← map_inv, ← map_mul]
          rfl
        rw [e, ← hK'eq] at h2
        exact (hmemK' _).mp h2
      · intro hk
        have hconjX : h * k * h⁻¹ ∈ X := hKX hk
        have hkX : k ∈ X := by
          have : k = h⁻¹ * (h * k * h⁻¹) * h := by group
          rw [this]
          exact X.mul_mem (X.mul_mem (X.inv_mem hhX) hconjX) hhX
        have h1 : ψ ⟨h * k * h⁻¹, hconjX⟩ ∈ (subfieldProj σ').range := by
          rw [← hK'eq]; exact (hmemK' _).mpr hk
        have e : ψ ⟨h, hhX⟩ * ψ ⟨k, hkX⟩ * (ψ ⟨h, hhX⟩)⁻¹ = ψ ⟨h * k * h⁻¹, hconjX⟩ := by
          rw [← map_mul, ← map_inv, ← map_mul]
          rfl
        rw [← e] at h1
        have h2 := (Subgroup.mem_normalizer_iff.mp hψh (ψ ⟨k, hkX⟩)).mpr h1
        rw [← hK'eq] at h2
        exact (hmemK' _).mp h2
    · rw [← hcardH', ← hcardK', hK'eq]
      exact hdvd

end Transfer

end CFSG.RankThree.PartTwo.Sec14.Item148Res8
