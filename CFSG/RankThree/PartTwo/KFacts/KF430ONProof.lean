module

public import CFSG.RankThree.PartTwo.KFacts.KF430ON
import CFSG.RankThree.PartTwo.Sec13.Item134ONProof
public import CFSG.RankThree.Native.ONTripleSylow

public section

namespace CFSG.RankThree.PartTwo.KFacts.KF430ONProof

attribute [local irreducible] dotProduct

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.Native.ONTriple
open scoped commutatorElement Pointwise

private theorem cube_aut_fixed {Γ : Type*} [Group Γ] {Z : Subgroup Γ} (hZ : Nat.card Z = 3)
    {σ : MulAut Γ} (hσ3 : σ ^ 3 = 1) (hσZ : ∀ z ∈ Z, σ z ∈ Z) {z : Γ} (hz : z ∈ Z) :
    σ z = z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite Z := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
  by_cases hz1 : z = 1
  · rw [hz1, map_one]
  have hzo : orderOf z = 3 := by
    have h := Subgroup.orderOf_dvd_natCard Z hz
    rw [hZ] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp h with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz1
    · exact h
  have hZz : Z = Subgroup.zpowers z :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz)
      (by rw [hZ, Nat.card_zpowers, hzo])).symm
  have hσz : σ z ∈ Subgroup.zpowers z := hZz ▸ hσZ z hz
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hσz
  have hz3 : z ^ 3 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one z
  have hkmod : z ^ k = z ^ (k % 3) := by
    rw [← zpow_mod_orderOf z k, hzo, Nat.cast_ofNat]
  have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  have hσ3z : σ (σ (σ z)) = z := by
    have h := congrArg (fun τ : MulAut Γ => τ z) hσ3
    simpa [pow_succ, MulAut.mul_apply] using h
  rcases hk3 with h | h | h
  · rw [hkmod, h, zpow_zero] at hk
    exact absurd ((map_eq_one_iff σ σ.injective).mp hk.symm) hz1
  · rw [hkmod, h, zpow_one] at hk
    exact hk.symm
  · rw [hkmod, h] at hk
    exfalso
    have h2 : σ z = z * z := by rw [← hk, zpow_two]
    have h4 : σ (σ z) = z := by
      rw [h2, map_mul, h2]
      calc z * z * (z * z) = z ^ 3 * z := by rw [pow_three]; simp only [mul_assoc]
        _ = z := by rw [hz3, one_mul]
    rw [h4, h2] at hσ3z
    apply hz1
    calc z = z * z * z⁻¹ := by group
      _ = z * z⁻¹ := by rw [hσ3z]
      _ = 1 := by group

private theorem card_sup_inf_of_normal {X : Type*} [Group X] (A B : Subgroup X) [A.Normal] :
    Nat.card (A ⊔ B : Subgroup X) * Nat.card (A ⊓ B : Subgroup X) = Nat.card A * Nat.card B := by
  have h1 := Subgroup.relIndex_mul_card (H := A) (K := A ⊔ B)
  rw [Subgroup.relIndex_sup_left, inf_eq_left.mpr le_sup_left] at h1
  have h2 := Subgroup.relIndex_mul_card (H := A) (K := B)
  rw [← h1, ← h2]
  ring

private theorem card_sup_inf_of_le_normalizer {X : Type*} [Group X] {A B : Subgroup X}
    (hB : B ≤ Subgroup.normalizer (A : Set X)) :
    Nat.card (A ⊔ B : Subgroup X) * Nat.card (A ⊓ B : Subgroup X) = Nat.card A * Nat.card B := by
  set N := Subgroup.normalizer (A : Set X)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have h := card_sup_inf_of_normal (A.subgroupOf N) (B.subgroupOf N)
  have hc : ∀ Y : Subgroup X, Y ≤ N → Nat.card (Y.subgroupOf N) = Nat.card Y := fun Y hY =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv
  have hsup : A.subgroupOf N ⊔ B.subgroupOf N = (A ⊔ B).subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAN, inf_eq_left.mpr hB,
      inf_eq_left.mpr (sup_le hAN hB)]
  have hinf : A.subgroupOf N ⊓ B.subgroupOf N = (A ⊓ B).subgroupOf N :=
    Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc A hAN, hc B hB] at h
  exact h

private theorem normConj_coe {M : Type} [Group M] {L : Subgroup M} {e : M}
    (he : e ∈ Subgroup.normalizer (L : Set M)) (y : ↥L) :
    ((L.normalizerMonoidHom ⟨e, he⟩ y : ↥L) : M) = e * y * e⁻¹ :=
  rfl

private def commHomCentral {X : Type*} [Group X] (x : X) (P : Subgroup X)
    (hc : ∀ p ∈ P, ⁅x, p⁆ ∈ Subgroup.center X) : ↥P →* X where
  toFun p := ⁅x, (p : X)⁆
  map_one' := by simp [commutatorElement_def]
  map_mul' p q := by
    have h := (Subgroup.mem_center_iff.mp (hc q q.2)) (p : X)
    simp only [Subgroup.coe_mul, commutatorElement_def] at h ⊢
    calc x * (↑p * ↑q) * x⁻¹ * (↑p * ↑q)⁻¹ =
        x * ↑p * x⁻¹ * (↑p)⁻¹ * (↑p * (x * ↑q * x⁻¹ * (↑q)⁻¹)) * (↑p)⁻¹ := by group
      _ = x * ↑p * x⁻¹ * (↑p)⁻¹ * ((x * ↑q * x⁻¹ * (↑q)⁻¹) * ↑p) * (↑p)⁻¹ := by rw [h]
      _ = x * ↑p * x⁻¹ * (↑p)⁻¹ * (x * ↑q * x⁻¹ * (↑q)⁻¹) := by group

private theorem gens_of_card27 {M : Type} [Group M] [Finite M] {A : Subgroup M} {a : M}
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) (hA27 : Nat.card A = 27) (haA : a ∈ A)
    (ha1 : a ≠ 1) :
    ∃ e₁ ∈ A, ∃ e₂ ∈ A, A = Subgroup.zpowers a ⊔ Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : ∀ g ∈ A, g ^ 3 = 1 := hAe.2
  have hAc : ∀ g ∈ A, ∀ h ∈ A, g * h = h * g := fun g hg h hh =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨g, hg⟩ ⟨h, hh⟩)
  have hcard : ∀ B : Subgroup M, B ≤ A → ∀ h ∈ A, h ≠ 1 → h ∉ B →
      Nat.card (B ⊔ Subgroup.zpowers h : Subgroup M) = 3 * Nat.card B := by
    intro B hB h hh hh1 hhB
    have hh3 : Nat.card (Subgroup.zpowers h) = 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (hA3 h hh) hh1
    have hN : Subgroup.zpowers h ≤ Subgroup.normalizer (B : Set M) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.mem_normalizer_fintype fun z hz => ?_
      rw [hAc h hh z (hB hz), mul_inv_cancel_right]
      exact hz
    have hinf : B ⊓ Subgroup.zpowers h = ⊥ := by
      rcases (Nat.dvd_prime Nat.prime_three).mp
          (hh3 ▸ Subgroup.card_dvd_of_le (inf_le_right : B ⊓ Subgroup.zpowers h ≤ _)) with
        h1 | h1
      · exact Subgroup.card_eq_one.mp h1
      · exfalso
        have heq : B ⊓ Subgroup.zpowers h = Subgroup.zpowers h :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h1, hh3])
        exact hhB (Subgroup.mem_inf.mp (heq.symm ▸ Subgroup.mem_zpowers h)).1
    have hc := card_sup_inf_of_le_normalizer hN
    rw [hinf, Subgroup.card_bot, mul_one, hh3] at hc
    rw [hc, mul_comm]
  have ha3 : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hA3 a haA) ha1
  have hnle1 : ¬ A ≤ Subgroup.zpowers a := fun hle => by
    have := Subgroup.card_le_of_le hle
    rw [hA27, ha3] at this
    norm_num at this
  obtain ⟨e₁, he₁A, he₁⟩ := SetLike.not_le_iff_exists.mp hnle1
  have he₁1 : e₁ ≠ 1 := fun h => he₁ (h ▸ one_mem _)
  have hB₁A : Subgroup.zpowers a ⊔ Subgroup.zpowers e₁ ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr haA) (Subgroup.zpowers_le.mpr he₁A)
  have hB₁9 : Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers e₁ : Subgroup M) = 9 := by
    rw [hcard _ (Subgroup.zpowers_le.mpr haA) e₁ he₁A he₁1 he₁, ha3]
  have hnle2 : ¬ A ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers e₁ := fun hle => by
    have := Subgroup.card_le_of_le hle
    rw [hA27, hB₁9] at this
    norm_num at this
  obtain ⟨e₂, he₂A, he₂⟩ := SetLike.not_le_iff_exists.mp hnle2
  have he₂1 : e₂ ≠ 1 := fun h => he₂ (h ▸ one_mem _)
  refine ⟨e₁, he₁A, e₂, he₂A,
    (Subgroup.eq_of_le_of_card_ge (sup_le hB₁A (Subgroup.zpowers_le.mpr he₂A)) ?_).symm⟩
  rw [hcard _ hB₁A e₂ he₂A he₂1 he₂, hB₁9, hA27]

private theorem sylow_stable {M : Type} [Group M] [Finite M] {A L : Subgroup M}
    (hAp : IsPGroup 3 A) (hAL : A ≤ Subgroup.normalizer (L : Set M)) :
    ∃ P : Sylow 3 ↥L, ∀ e (he : e ∈ A), ∀ p ∈ (P : Subgroup ↥L),
      L.normalizerMonoidHom ⟨e, hAL he⟩ p ∈ (P : Subgroup ↥L) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : MulDistribMulAction ↥A ↥L :=
    MulDistribMulAction.compHom ↥L (Subgroup.inclusion hAL)
  obtain ⟨P, hP⟩ := hAp.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 3 ↥L)
    (not_dvd_card_sylow 3 ↥L)
  refine ⟨P, fun e he p hp => ?_⟩
  have hfix : (⟨e, he⟩ : ↥A) • P = P := MulAction.mem_fixedPoints.mp hP ⟨e, he⟩
  have h1 : (⟨e, he⟩ : ↥A) • p ∈ (⟨e, he⟩ : ↥A) • (P : Subgroup ↥L) :=
    Subgroup.smul_mem_pointwise_smul p _ _ hp
  rw [← Sylow.pointwise_smul_def, hfix] at h1
  exact h1

private theorem comm_center_of_sylow
    {X : Type} [Group X] [Finite X] (ψ : X ≃* GM) (P : Sylow 3 X) {p q : X}
    (hp : p ∈ (P : Subgroup X)) (hq : q ∈ (P : Subgroup X)) : ⁅p, q⁆ ∈ Subgroup.center X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card ((P : Subgroup X).map ψ.toMonoidHom) =
      3 ^ (Nat.card GM).factorization 3 := by
    rw [Subgroup.card_map_of_injective ψ.injective, Sylow.card_eq_multiplicity,
      Nat.card_congr ψ.toEquiv]
  obtain ⟨g, hg⟩ := sylow_eq_threeQ (Sylow.ofCard _ hcard)
  have hr := relG_conj g
  have hp' : ψ p ∈ threeQ (MulAut.conj g zG) (fun i => MulAut.conj g (xG i)) := by
    rw [← hg]
    exact ⟨p, hp, rfl⟩
  have hq' : ψ q ∈ threeQ (MulAut.conj g zG) (fun i => MulAut.conj g (xG i)) := by
    rw [← hg]
    exact ⟨q, hq, rfl⟩
  have h := hr.comm_mem hp' hq'
  have hz : MulAut.conj g zG = zG := conj_zG g
  rw [hz] at h
  rw [Sec13.ON134.mem_center_iff_model ψ, map_commutatorElement]
  exact h

section Setting

variable {M : Type} [Group M] [Finite M] {A L : Subgroup M} {a : M}

private theorem center_map_eq_a (hA3 : ∀ g ∈ A, g ^ 3 = 1)
    (hmax : ∀ x : M, x ^ 3 = 1 → (∀ y ∈ A, x * y = y * x) → x ∈ A)
    (hAL : A ≤ Subgroup.normalizer (L : Set M)) (hZ3 : Nat.card (Subgroup.center ↥L) = 3)
    (hCa : A ⊓ Subgroup.centralizer (L : Set M) = Subgroup.zpowers a) (ha3 : orderOf a = 3) :
    (Subgroup.center ↥L).map L.subtype = Subgroup.zpowers a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZA : ∀ z ∈ Subgroup.center ↥L, ∀ e ∈ A, e * (z : M) = (z : M) * e := by
    intro z hz e he
    set σ := L.normalizerMonoidHom ⟨e, hAL he⟩ with hσ
    have hσ3 : σ ^ 3 = 1 := by
      have h : (⟨e, hAL he⟩ : Subgroup.normalizer (L : Set M)) ^ 3 = 1 :=
        Subtype.ext (by simpa using hA3 e he)
      rw [hσ, ← map_pow, h, map_one]
    have hσZ : ∀ y ∈ Subgroup.center ↥L, σ y ∈ Subgroup.center ↥L := by
      intro y hy
      rw [Subgroup.mem_center_iff] at hy ⊢
      intro g
      obtain ⟨g', rfl⟩ := σ.surjective g
      rw [← map_mul, ← map_mul, hy g']
    have h : ((σ z : ↥L) : M) = z := congrArg Subtype.val (cube_aut_fixed hZ3 hσ3 hσZ hz)
    rw [hσ, normConj_coe] at h
    calc e * (z : M) = e * (z : M) * e⁻¹ * e := by group
      _ = (z : M) * e := by rw [h]
  have hle : (Subgroup.center ↥L).map L.subtype ≤ Subgroup.zpowers a := by
    rintro _ ⟨z, hz, rfl⟩
    rw [← hCa]
    refine Subgroup.mem_inf.mpr ⟨hmax _ ?_ fun y hy => (hZA z hz y hy).symm, ?_⟩
    · have h := pow_card_eq_one' (G := Subgroup.center ↥L) (x := ⟨z, hz⟩)
      rw [hZ3] at h
      simpa using congrArg (fun w : Subgroup.center ↥L => ((w : ↥L) : M)) h
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨y, hy⟩)
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [Subgroup.card_map_of_injective L.subtype_injective, hZ3, Nat.card_zpowers, ha3]

private theorem inner_of_mem_A
    (ψ : ↥L ≃* GM) (hAc : ∀ g ∈ A, ∀ h ∈ A, g * h = h * g) (haA : a ∈ A)
    (hcen : (Subgroup.center ↥L).map L.subtype = Subgroup.zpowers a)
    (hAL : A ≤ Subgroup.normalizer (L : Set M)) {e : M} (he : e ∈ A) :
    ∃ x : ↥L, ∀ y : ↥L, L.normalizerMonoidHom ⟨e, hAL he⟩ y = x * y * x⁻¹ := by
  refine Sec13.ON134.aut_inner ψ _ fun z hz => ?_
  have hz' : (z : M) ∈ Subgroup.zpowers a := hcen ▸ ⟨z, hz, rfl⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz'
  apply Subtype.ext
  rw [normConj_coe, ← hk, (Commute.zpow_right (hAc e he a haA) k).eq, mul_inv_cancel_right]

private theorem le_of_inner
    (ψ : ↥L ≃* GM) (hAe : CFSG.Assembly.IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hmax : ∀ x : M, x ^ 3 = 1 → (∀ y ∈ A, x * y = y * x) → x ∈ A)
    (hAL : A ≤ Subgroup.normalizer (L : Set M)) (hZ3 : Nat.card (Subgroup.center ↥L) = 3)
    (haA : a ∈ A) (ha1 : a ≠ 1) (haL : a ∈ Subgroup.centralizer (L : Set M))
    (hinn : ∀ e (he : e ∈ A), ∃ x : ↥L, ∀ y : ↥L,
      L.normalizerMonoidHom ⟨e, hAL he⟩ y = x * y * x⁻¹) :
    A ≤ L := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : ∀ g ∈ A, g ^ 3 = 1 := hAe.2
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hA27]; norm_num)
  obtain ⟨P, hAP⟩ := sylow_stable hAp hAL
  have hexp : ∀ p ∈ (P : Subgroup ↥L), p ^ 3 = 1 := fun p hp => by
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨p, hp⟩
    exact Sec13.ON134.pow_three_eq_one ψ (k := k) (by simpa using congrArg Subtype.val hk)
  have hcomm : ∀ p ∈ (P : Subgroup ↥L), ∀ q ∈ (P : Subgroup ↥L),
      ⁅p, q⁆ ∈ Subgroup.center ↥L := fun p hp q hq => comm_center_of_sylow ψ P hp hq
  have hxe : ∀ e (he : e ∈ A), ∃ x ∈ (P : Subgroup ↥L),
      ∀ y : ↥L, L.normalizerMonoidHom ⟨e, hAL he⟩ y = x * y * x⁻¹ := by
    intro e he
    obtain ⟨x, hx⟩ := hinn e he
    refine ⟨x, ?_, hx⟩
    have hx3c : x ^ 3 ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 : (L.normalizerMonoidHom ⟨e, hAL he⟩ ^ 3) y = y := by
        have h : (⟨e, hAL he⟩ : Subgroup.normalizer (L : Set M)) ^ 3 = 1 :=
          Subtype.ext (by simpa using hA3 e he)
        rw [← map_pow, h, map_one, MulAut.one_apply]
      rw [Sec13.ON134.pow_apply_of_conj hx 3 y] at h1
      calc y * x ^ 3 = x ^ 3 * y * (x ^ 3)⁻¹ * x ^ 3 := by rw [h1]
        _ = x ^ 3 * y := by group
    have hx9 : x ^ 3 ^ 2 = 1 := by
      have h := pow_card_eq_one' (G := Subgroup.center ↥L) (x := ⟨x ^ 3, hx3c⟩)
      rw [hZ3] at h
      have h' : (x ^ 3) ^ 3 = 1 := by simpa using congrArg Subtype.val h
      rw [show 3 ^ 2 = 3 * 3 by norm_num, pow_mul]
      exact h'
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hx9)
    have hxp : IsPGroup 3 (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
    have hN : Subgroup.zpowers x ≤ Subgroup.normalizer ((P : Subgroup ↥L) : Set ↥L) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.mem_normalizer_fintype fun y hy => ?_
      rw [← hx y]
      exact hAP e he y hy
    have hsup := hxp.to_sup_of_normal_right' P.isPGroup' hN
    rw [← P.is_maximal' hsup le_sup_right]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hind : ∀ e ∈ A, ∃ C : Subgroup ↥(P : Subgroup ↥L), C.index ≤ 3 ∧
      ∀ c ∈ C, e * ((c : ↥L) : M) = ((c : ↥L) : M) * e := by
    intro e he
    obtain ⟨x, hxP, hx⟩ := hxe e he
    set χ := commHomCentral x (P : Subgroup ↥L) (fun p hp => hcomm x hxP p hp) with hχ
    refine ⟨χ.ker, ?_, fun c hc => ?_⟩
    · rw [Subgroup.index_ker]
      have hle : χ.range ≤ Subgroup.center ↥L := by
        rintro _ ⟨p, rfl⟩
        exact hcomm x hxP p p.2
      have := Subgroup.card_le_of_le hle
      rwa [hZ3] at this
    · have h1 : ⁅x, (c : ↥L)⁆ = 1 := MonoidHom.mem_ker.mp hc
      have h2 : x * (c : ↥L) * x⁻¹ = c := by
        rw [commutatorElement_def] at h1
        calc x * ↑c * x⁻¹ = x * ↑c * x⁻¹ * (↑c)⁻¹ * ↑c := by group
          _ = ↑c := by rw [h1, one_mul]
      have h3 := congrArg Subtype.val ((hx c).trans h2)
      rw [normConj_coe] at h3
      calc e * ((c : ↥L) : M) = e * ((c : ↥L) : M) * e⁻¹ * e := by group
        _ = ((c : ↥L) : M) * e := by rw [h3]
  obtain ⟨e₁, he₁, e₂, he₂, hgens⟩ := gens_of_card27 hAe hA27 haA ha1
  obtain ⟨C₁, hC₁, hC₁c⟩ := hind e₁ he₁
  obtain ⟨C₂, hC₂, hC₂c⟩ := hind e₂ he₂
  have hcardP : Nat.card ↥(P : Subgroup ↥L) = 243 := by
    rw [Sylow.card_eq_multiplicity, Nat.card_congr ψ.toEquiv, factorization_card_GM]
    norm_num
  have hC27 : 27 ≤ Nat.card ↥(C₁ ⊓ C₂) := by
    have h := (C₁ ⊓ C₂).card_mul_index
    rw [hcardP] at h
    have hi : (C₁ ⊓ C₂).index ≤ 9 := Subgroup.index_inf_le.trans (Nat.mul_le_mul hC₁ hC₂)
    have : 243 ≤ Nat.card ↥(C₁ ⊓ C₂) * 9 := h ▸ Nat.mul_le_mul_left _ hi
    omega
  set Cm : Subgroup M := ((C₁ ⊓ C₂).map (P : Subgroup ↥L).subtype).map L.subtype with hCm
  have hCmcard : Nat.card Cm = Nat.card ↥(C₁ ⊓ C₂) := by
    rw [hCm, Subgroup.card_map_of_injective L.subtype_injective,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  have hCmA : Cm ≤ A := by
    rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    show (((c : ↥(P : Subgroup ↥L)) : ↥L) : M) ∈ A
    set y : M := (((c : ↥(P : Subgroup ↥L)) : ↥L) : M) with hy
    refine hmax y ?_ fun f hf => ?_
    · have h := hexp _ (c : ↥(P : Subgroup ↥L)).2
      simpa [hy] using congrArg Subtype.val h
    · have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂ ≤
          Subgroup.centralizer ({y} : Set M) := by
        refine sup_le (sup_le ?_ ?_) ?_ <;>
          rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        · exact ((Subgroup.mem_centralizer_iff.mp haL) y (c : ↥L).2).symm
        · exact hC₁c c (Subgroup.mem_inf.mp hc).1
        · exact hC₂c c (Subgroup.mem_inf.mp hc).2
      rw [hgens] at hf
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hf)).symm
  have hCmeq := Subgroup.eq_of_le_of_card_ge hCmA (by rw [hA27, hCmcard]; exact hC27)
  rw [← hCmeq]
  exact Subgroup.map_subtype_le _

end Setting

theorem kf430ON_holds :
    KF430ON := by
  intro M _ _ A L a c hAe hA27 hmax hAL hperf hON hCa ha3 hcA hca hnorm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ψ⟩ := Sec13.ON134.nonempty_equiv_model hperf hON
  have hA3 : ∀ g ∈ A, g ^ 3 = 1 := hAe.2
  have hAc : ∀ g ∈ A, ∀ h ∈ A, g * h = h * g := fun g hg h hh =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨g, hg⟩ ⟨h, hh⟩)
  have haCa : a ∈ A ⊓ Subgroup.centralizer (L : Set M) := hCa ▸ Subgroup.mem_zpowers a
  have haA : a ∈ A := (Subgroup.mem_inf.mp haCa).1
  have haL : a ∈ Subgroup.centralizer (L : Set M) := (Subgroup.mem_inf.mp haCa).2
  have ha1 : a ≠ 1 := fun h => by
    rw [h, orderOf_one] at ha3
    norm_num at ha3
  have hcen := center_map_eq_a hA3 hmax hAL hON.1 hCa ha3
  have hAL' : A ≤ L := le_of_inner ψ hAe hA27 hmax hAL hON.1 haA ha1 haL
    (fun e he => inner_of_mem_A ψ hAc haA hcen hAL he)
  set A₀ : Subgroup ↥L := A.subgroupOf L with hA₀
  have hA₀e : Late.IsE27 A₀ := by
    refine ⟨⟨⟨⟨fun u v => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
    · have h := hAc _ (Subgroup.mem_subgroupOf.mp u.2) _ (Subgroup.mem_subgroupOf.mp v.2)
      apply Subtype.ext
      apply Subtype.ext
      simpa using h
    · apply Subtype.ext
      simpa using hA3 _ (Subgroup.mem_subgroupOf.mp hx)
    · rw [hA₀, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL').toEquiv, hA27]
  have hcL : c ∈ L := hAL' hcA
  have hcaA : c * a ∈ A := mul_mem hcA haA
  have hcaL : c * a ∈ L := hAL' hcaA
  have hc0 : (⟨c, hcL⟩ : ↥L) ∉ Subgroup.center ↥L := fun h => hca (hcen ▸ ⟨_, h, rfl⟩)
  have hca0 : (⟨c * a, hcaL⟩ : ↥L) ∉ Subgroup.center ↥L := fun h => by
    have h1 : c * a ∈ Subgroup.zpowers a := hcen ▸ ⟨_, h, rfl⟩
    apply hca
    have h2 := mul_mem h1 (inv_mem (Subgroup.mem_zpowers a))
    rwa [mul_inv_cancel_right] at h2
  obtain ⟨g, hgN, hgc⟩ := Sec13.ON134.transitive ψ hA₀e
    (Subgroup.mem_subgroupOf.mpr hcA : (⟨c, hcL⟩ : ↥L) ∈ A₀)
    (Subgroup.mem_subgroupOf.mpr hcaA : (⟨c * a, hcaL⟩ : ↥L) ∈ A₀) hc0 hca0
  have hgA : (g : M) ∈ L ⊓ Subgroup.normalizer (A : Set M) := by
    refine Subgroup.mem_inf.mpr ⟨g.2, Subgroup.mem_normalizer_fintype fun y hy => ?_⟩
    have h := (Subgroup.mem_normalizer_iff.mp hgN ⟨y, hAL' hy⟩).mp
      (Subgroup.mem_subgroupOf.mpr hy)
    exact Subgroup.mem_subgroupOf.mp h
  have hgc' := hnorm hgA
  have hmem : c * a ∈ Subgroup.zpowers c := by
    have h1 : (⟨c * a, hcaL⟩ : ↥L) ∈
        (Subgroup.zpowers (⟨c, hcL⟩ : ↥L)).map (MulAut.conj g).toMonoidHom :=
      hgc ▸ Subgroup.mem_zpowers _
    obtain ⟨y, hy, hyc⟩ := h1
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have h2 := congrArg Subtype.val hyc
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_inv, SubgroupClass.coe_zpow] at h2
    rw [← h2]
    exact (Subgroup.mem_normalizer_iff.mp hgc' (c ^ k)).mp (Subgroup.zpow_mem_zpowers c k)
  have haC : a ∈ Subgroup.zpowers c := by
    have h := mul_mem (inv_mem (Subgroup.mem_zpowers c)) hmem
    rwa [inv_mul_cancel_left] at h
  have hc1 : c ≠ 1 := fun h => hca (h ▸ one_mem _)
  have hceq : Subgroup.zpowers a = Subgroup.zpowers c :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haC) (by
      rw [Nat.card_zpowers, Nat.card_zpowers, ha3, orderOf_eq_prime (hA3 c hcA) hc1])
  exact hca (hceq ▸ Subgroup.mem_zpowers c)

end CFSG.RankThree.PartTwo.KFacts.KF430ONProof
