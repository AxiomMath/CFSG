module

public import CFSG.RankThree.PartTwo.Sec16.Item162Res7Y1
public import CFSG.RankThree.PartTwo.Sec16.Item162Res7Y2
public import CFSG.RankThree.PartTwo.Sec16.Item162Res7Lift
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CentralizerZpowers
import CFSG.Timmesfeld.LocalTwoSubgroups.CoprimeActionBounds
public import CFSG.Monster.B.TwoA.Census.PermClasses
import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open CFSG.RankThreeEvenClassification.Helpers
open scoped Pointwise commutatorElement

namespace Res162Seven

namespace Conf683

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₁ Y₂ S : Subgroup G}
  {b : G} {Lb : Subgroup G}

private theorem image_inf_le_normalizer_image {A K S : Subgroup G}
    (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hAS : A ≤ Subgroup.normalizer (S : Set G))
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7)) :
    (((A ⊓ K).subgroupOf (Subgroup.normalizer (K : Set G))).map
        (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ) : Subgroup (Equiv.Perm (Fin 7))) ≤
      Subgroup.normalizer (((S.subgroupOf (Subgroup.normalizer (K : Set G))).map
        (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ) : Subgroup (Equiv.Perm (Fin 7))) :
          Set (Equiv.Perm (Fin 7))) := by
  classical
  let N := Subgroup.normalizer (K : Set G)
  let ρ := CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ
  rintro _ ⟨d, hd, rfl⟩
  have hdD : (d : G) ∈ A ⊓ K := Subgroup.mem_subgroupOf.mp hd
  have hdA : (d : G) ∈ A := (Subgroup.mem_inf.mp hdD).1
  refine Subgroup.mem_normalizer_fintype fun v hv => ?_
  have hv' : v ∈ (S.subgroupOf N).map ρ := by simpa [N, ρ] using hv
  obtain ⟨s, hsS, rfl⟩ := Subgroup.mem_map.mp hv'
  have hs : (s : G) ∈ S := Subgroup.mem_subgroupOf.mp hsS
  have hsN : (d * s * d⁻¹ : ↥N) ∈ S.subgroupOf N := by
    refine Subgroup.mem_subgroupOf.mpr ?_
    exact (Subgroup.mem_normalizer_iff.mp (hAS hdA) (s : G)).mp hs
  have heq : ρ d * ρ s * (ρ d)⁻¹ = ρ (d * s * d⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  rw [heq]
  exact Subgroup.mem_map.mpr ⟨d * s * d⁻¹, hsN, rfl⟩

private theorem a7Rep_inverts_inf {A K : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7))
    {x : G} {τ : Equiv.Perm (Fin 7)} (hxK : x ∈ Subgroup.normalizer (K : Set G))
    (hxA : x ∈ Subgroup.normalizer (A : Set G))
    (hxρ : CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ ⟨x, hxK⟩ = τ)
    (hτ : ∀ e ∈ (((A ⊓ K).subgroupOf (Subgroup.normalizer (K : Set G))).map
        (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ) : Subgroup (Equiv.Perm (Fin 7))),
        τ * e * τ⁻¹ = e⁻¹) :
    ∀ e ∈ A ⊓ K, x * e * x⁻¹ = e⁻¹ := by
  classical
  let N := Subgroup.normalizer (K : Set G)
  let ρ := CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ
  intro e he
  have heA : e ∈ A := (Subgroup.mem_inf.mp he).1
  have heK : e ∈ K := (Subgroup.mem_inf.mp he).2
  have hxeA : x * e * x⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hxA e).mp heA
  have hxeK : x * e * x⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hxK e).mp heK
  have hxeD : x * e * x⁻¹ ∈ A ⊓ K := ⟨hxeA, hxeK⟩
  have heD : e⁻¹ ∈ A ⊓ K := ⟨A.inv_mem heA, K.inv_mem heK⟩
  have hρeP : ρ ⟨e, Subgroup.le_normalizer heK⟩ ∈ ((A ⊓ K).subgroupOf N).map ρ :=
    Subgroup.mem_map.mpr ⟨⟨e, Subgroup.le_normalizer heK⟩,
      Subgroup.mem_subgroupOf.mpr he, rfl⟩
  have hτe := hτ _ hρeP
  have hρconj : ρ ⟨x * e * x⁻¹, Subgroup.le_normalizer hxeK⟩ =
      ρ ⟨e⁻¹, Subgroup.le_normalizer heD.2⟩ := by
    calc ρ ⟨x * e * x⁻¹, Subgroup.le_normalizer hxeK⟩
        = ρ ⟨x, hxK⟩ * ρ ⟨e, Subgroup.le_normalizer heK⟩ * (ρ ⟨x, hxK⟩)⁻¹ := by
          have e1 : (⟨x * e * x⁻¹, Subgroup.le_normalizer hxeK⟩ : ↥N) =
              ⟨x, hxK⟩ * ⟨e, Subgroup.le_normalizer heK⟩ * ⟨x, hxK⟩⁻¹ :=
            Subtype.ext (by simp)
          rw [e1, map_mul, map_mul, map_inv]
      _ = τ * ρ ⟨e, Subgroup.le_normalizer heK⟩ * τ⁻¹ := by rw [hxρ]
      _ = (ρ ⟨e, Subgroup.le_normalizer heK⟩)⁻¹ := hτe
      _ = ρ ⟨e⁻¹, Subgroup.le_normalizer heD.2⟩ := by
          rw [show (⟨e⁻¹, Subgroup.le_normalizer heD.2⟩ : ↥N) =
            (⟨e, Subgroup.le_normalizer heK⟩ : ↥N)⁻¹ from Subtype.ext rfl, map_inv]
  have hinj := a7Rep_injective_inf (A := A) (K := K) hA φ
  have heq : (⟨x * e * x⁻¹, hxeD⟩ : ↥(A ⊓ K)) = ⟨e⁻¹, heD⟩ :=
    hinj (by simpa using hρconj)
  exact congrArg Subtype.val heq

private theorem pow_odd_inverts {x e : G} (h : x * e * x⁻¹ = e⁻¹) {m : ℕ} (hm : Odd m) :
    x ^ m * e * (x ^ m)⁻¹ = e⁻¹ := by
  obtain ⟨k, rfl⟩ := hm
  have hx2 : x ^ 2 * e * (x ^ 2)⁻¹ = e := by
    have hinv : x * e⁻¹ * x⁻¹ = e := by
      simpa [mul_assoc] using congrArg Inv.inv h
    calc x ^ 2 * e * (x ^ 2)⁻¹ = x * (x * e * x⁻¹) * x⁻¹ := by
          rw [pow_two]
          group
      _ = x * e⁻¹ * x⁻¹ := by rw [h]
      _ = e := hinv
  have hx2k : ∀ k : ℕ, (x ^ 2) ^ k * e * ((x ^ 2) ^ k)⁻¹ = e := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc (x ^ 2) ^ (k + 1) * e * ((x ^ 2) ^ (k + 1))⁻¹
            = x ^ 2 * ((x ^ 2) ^ k * e * ((x ^ 2) ^ k)⁻¹) * (x ^ 2)⁻¹ := by
              group
          _ = x ^ 2 * e * (x ^ 2)⁻¹ := by rw [ih]
          _ = e := hx2
  have hpow : x ^ (2 * k + 1) = x * (x ^ 2) ^ k := by
    rw [show 2 * k + 1 = 1 + 2 * k by omega, pow_add, pow_one, pow_mul]
  rw [hpow, mul_inv_rev]
  calc x * (x ^ 2) ^ k * e * (((x ^ 2) ^ k)⁻¹ * x⁻¹)
      = x * ((x ^ 2) ^ k * e * ((x ^ 2) ^ k)⁻¹) * x⁻¹ := by group
    _ = x * e * x⁻¹ := by rw [hx2k k]
    _ = e⁻¹ := h

theorem exists_t₁ (h : Conf683 A c L Y₁ Y₂ S b Lb) :
    ∃ t ∈ Y₁ ⊔ S, t ∈ Subgroup.normalizer (A : Set G) ∧
      t ∈ Subgroup.normalizer (S : Set G) ∧ IsPGroup 2 (Subgroup.zpowers t) ∧
      t * c = c * t ∧ ∀ e ∈ A ⊓ Y₁, t * e * t⁻¹ = e⁻¹ := by
  classical
  let N := Subgroup.normalizer (Y₁ : Set G)
  let ρ := CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep Y₁ (Classical.choice h.a7₁)
  let P : Subgroup (Equiv.Perm (Fin 7)) := ((A ⊓ Y₁).subgroupOf N).map ρ
  let V : Subgroup (Equiv.Perm (Fin 7)) := (S.subgroupOf N).map ρ
  have hA := isElemAbelian_A h
  have hcA := c_mem h
  have hAK := le_normalizer₁ h
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := h.maxCE.1.s₁.prop.1.1.1.2.2
  have hS := isPGroup_S₁ h
  have hSK : S ≤ Subgroup.normalizer (Y₁ : Set G) := h.maxCE.1.s₁.prop.1.2
  have hQS := pCoreOf_sup_le₁ h
  have hck : ∀ x ∈ Y₁ ⊔ S, c * x * c⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 (Y₁ ⊔ S) :=
    fun x hx => commutator_c_mem h hx
  have hAk := (card_inf₁ h).2.2
  have hP9 : Nat.card P = 9 := by
    simpa [P, N, ρ] using card_map_a7Rep_inf (A := A) (K := Y₁) hA
      (Classical.choice h.a7₁) (card_inf₁ h).1
  have hV2 : IsPGroup 2 V := by
    have h1 : IsPGroup 2 (S.subgroupOf N) :=
      hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSK).symm
    simpa [V, N, ρ] using h1.map ρ
  have hPV : P ≤ Subgroup.normalizer (V : Set (Equiv.Perm (Fin 7))) := by
    simpa [P, V, N, ρ] using image_inf_le_normalizer_image (K := Y₁) hAK hAS
      (Classical.choice h.a7₁)
  obtain ⟨τ, hτA, hτinv, hτV⟩ :=
    CFSG.RankThree.PartTwo.KFacts.KP2.exists_inv_mem_normalizer hP9 hV2 hPV
  have hτP : τ ∈ Subgroup.normalizer (P : Set (Equiv.Perm (Fin 7))) := by
    refine Subgroup.mem_normalizer_fintype fun p hp => ?_
    rw [hτinv p hp]
    exact P.inv_mem hp
  obtain ⟨x, hxKS, hxK, hxA, hxc, hxρ, hxS⟩ :=
    exists_lift_of_a7 (A := A) (K := Y₁) (S := S) (k := c) hA hcA hAK hAS hS hSK hQS hck
      hAk (Classical.choice h.a7₁) hτA (by simpa [P, N, ρ] using hτP)
  have hxInv : ∀ e ∈ A ⊓ Y₁, x * e * x⁻¹ = e⁻¹ :=
    a7Rep_inverts_inf hA (Classical.choice h.a7₁) hxK hxA hxρ hτinv
  have hn0 : orderOf x ≠ 0 := (isOfFinOrder_of_finite x).orderOf_pos.ne'
  obtain ⟨k, m, hm_odd, hm_eq⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  have hm0 : m ≠ 0 := by
    rintro rfl
    norm_num at hm_odd
  have ht_order : orderOf (x ^ m) = 2 ^ k := by
    have hdvd : m ∣ orderOf x := ⟨2 ^ k, by rw [hm_eq, mul_comm]⟩
    rw [orderOf_pow_of_dvd hm0 hdvd, hm_eq, Nat.mul_comm]
    exact Nat.mul_div_right (2 ^ k) (Nat.pos_of_ne_zero hm0)
  have ht2 : IsPGroup 2 (Subgroup.zpowers (x ^ m)) := by
    apply IsPGroup.of_card (n := k)
    rw [Nat.card_zpowers, ht_order]
  have htS : x ^ m ∈ Subgroup.normalizer (S : Set G) :=
    (Subgroup.normalizer (S : Set G)).pow_mem (hxS hτV) m
  refine ⟨x ^ m, (Y₁ ⊔ S).pow_mem hxKS m,
    (Subgroup.normalizer (A : Set G)).pow_mem hxA m, htS, ht2, ?_, ?_⟩
  · exact (Commute.pow_left (show Commute x c from hxc) m).eq
  · intro e he
    exact pow_odd_inverts (hxInv e he) hm_odd

theorem exists_t₂ (h : Conf683 A c L Y₁ Y₂ S b Lb) :
    ∃ t ∈ Y₂ ⊔ S, t ∈ Subgroup.normalizer (A : Set G) ∧
      t ∈ Subgroup.normalizer (S : Set G) ∧ IsPGroup 2 (Subgroup.zpowers t) ∧
      t * b = b * t ∧ ∀ e ∈ A ⊓ Y₂, t * e * t⁻¹ = e⁻¹ := by
  classical
  let N := Subgroup.normalizer (Y₂ : Set G)
  let ρ := CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep Y₂ (Classical.choice h.a7₂)
  let P : Subgroup (Equiv.Perm (Fin 7)) := ((A ⊓ Y₂).subgroupOf N).map ρ
  let V : Subgroup (Equiv.Perm (Fin 7)) := (S.subgroupOf N).map ρ
  have hA := isElemAbelian_A h
  have hbA := b_mem h
  have hAK := le_normalizer₂ h
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := h.maxCE.1.s₂.prop.1.1.1.2.2
  have hS := isPGroup_S₁ h
  have hSK : S ≤ Subgroup.normalizer (Y₂ : Set G) := h.maxCE.1.s₂.prop.1.2
  have hQS := R_le h
  have hck : ∀ x ∈ Y₂ ⊔ S, b * x * b⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 (Y₂ ⊔ S) :=
    fun x hx => commutator_b_mem h hx
  have hAk := (card_inf₂ h).2.2
  have hP9 : Nat.card P = 9 := by
    simpa [P, N, ρ] using card_map_a7Rep_inf (A := A) (K := Y₂) hA
      (Classical.choice h.a7₂) (card_inf₂ h).1
  have hV2 : IsPGroup 2 V := by
    have h1 : IsPGroup 2 (S.subgroupOf N) :=
      hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSK).symm
    simpa [V, N, ρ] using h1.map ρ
  have hPV : P ≤ Subgroup.normalizer (V : Set (Equiv.Perm (Fin 7))) := by
    simpa [P, V, N, ρ] using image_inf_le_normalizer_image (K := Y₂) hAK hAS
      (Classical.choice h.a7₂)
  obtain ⟨τ, hτA, hτinv, hτV⟩ :=
    CFSG.RankThree.PartTwo.KFacts.KP2.exists_inv_mem_normalizer hP9 hV2 hPV
  have hτP : τ ∈ Subgroup.normalizer (P : Set (Equiv.Perm (Fin 7))) := by
    refine Subgroup.mem_normalizer_fintype fun p hp => ?_
    rw [hτinv p hp]
    exact P.inv_mem hp
  obtain ⟨x, hxKS, hxK, hxA, hxb, hxρ, hxS⟩ :=
    exists_lift_of_a7 (A := A) (K := Y₂) (S := S) (k := b) hA hbA hAK hAS hS hSK hQS hck
      hAk (Classical.choice h.a7₂) hτA (by simpa [P, N, ρ] using hτP)
  have hxInv : ∀ e ∈ A ⊓ Y₂, x * e * x⁻¹ = e⁻¹ :=
    a7Rep_inverts_inf hA (Classical.choice h.a7₂) hxK hxA hxρ hτinv
  have hn0 : orderOf x ≠ 0 := (isOfFinOrder_of_finite x).orderOf_pos.ne'
  obtain ⟨k, m, hm_odd, hm_eq⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  have hm0 : m ≠ 0 := by
    rintro rfl
    norm_num at hm_odd
  have ht_order : orderOf (x ^ m) = 2 ^ k := by
    have hdvd : m ∣ orderOf x := ⟨2 ^ k, by rw [hm_eq, mul_comm]⟩
    rw [orderOf_pow_of_dvd hm0 hdvd, hm_eq, Nat.mul_comm]
    exact Nat.mul_div_right (2 ^ k) (Nat.pos_of_ne_zero hm0)
  have ht2 : IsPGroup 2 (Subgroup.zpowers (x ^ m)) := by
    apply IsPGroup.of_card (n := k)
    rw [Nat.card_zpowers, ht_order]
  have htS : x ^ m ∈ Subgroup.normalizer (S : Set G) :=
    (Subgroup.normalizer (S : Set G)).pow_mem (hxS hτV) m
  refine ⟨x ^ m, (Y₂ ⊔ S).pow_mem hxKS m,
    (Subgroup.normalizer (A : Set G)).pow_mem hxA m, htS, ht2, ?_, ?_⟩
  · exact (Commute.pow_left (show Commute x b from hxb) m).eq
  · intro e he
    exact pow_odd_inverts (hxInv e he) hm_odd

private theorem mem_normalizer_zpowers_of_mem_normalizer_sectionCentralizer
    {A Y : Subgroup G} {b t : G}
    (hsec : Late.sectionCentralizer A Y (CFSG.Open.pCoreOf 2 Y) = (Subgroup.zpowers b : Set G))
    (htA : t ∈ Subgroup.normalizer (A : Set G))
    (htY : t ∈ Subgroup.normalizer (Y : Set G)) :
    t ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
  classical
  have htO : t ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y htY
  have htYinv : t⁻¹ ∈ Subgroup.normalizer (Y : Set G) :=
    (Subgroup.normalizer (Y : Set G)).inv_mem htY
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  have hxsec : x ∈ Late.sectionCentralizer A Y (CFSG.Open.pCoreOf 2 Y) := by
    rw [hsec]
    exact hx
  refine ?_
  rw [← hsec]
  refine ⟨(Subgroup.mem_normalizer_iff.mp htA x).mp hxsec.1, fun y hy => ?_⟩
  have hy' : t⁻¹ * y * t ∈ Y := by
    simpa using (Subgroup.mem_normalizer_iff.mp htYinv y).mp hy
  have hinner : x * (t⁻¹ * y * t) * x⁻¹ * (t⁻¹ * y * t)⁻¹ ∈
      CFSG.Open.pCoreOf 2 Y := hxsec.2 _ hy'
  have e : (t * x * t⁻¹) * y * (t * x * t⁻¹)⁻¹ * y⁻¹ =
      t * (x * (t⁻¹ * y * t) * x⁻¹ * (t⁻¹ * y * t)⁻¹) * t⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp htO _).mp hinner

theorem b_mem_y₁ (h : Conf683 A c L Y₁ Y₂ S b Lb) : b ∈ Y₁ := by
  classical
  obtain ⟨t, -, htA, htS, -, htc, htinv⟩ := exists_t₁ h
  have htAS : t ∈ Subgroup.normalizer ((A ⊔ S : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_sup A S ⟨htA, htS⟩
  have htY₂ : t ∈ Subgroup.normalizer (Y₂ : Set G) := normalizer_sup_le₂ h htAS
  have htB : t ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G) :=
    mem_normalizer_zpowers_of_mem_normalizer_sectionCentralizer h.sc₂ htA htY₂
  let D := A ⊓ Y₁
  have hA := isElemAbelian_A h
  have hcA := c_mem h
  have hAk := (card_inf₁ h).2.2
  have hbA : b ∈ A := b_mem h
  have hDk : D ≤ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
    intro d hd
    refine CFSG.GorensteinWalter.centralizer_singleton_le_normalizer_zpowers c ?_
    exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
      (hA.1.is_comm.comm ⟨d, (Subgroup.mem_inf.mp hd).1⟩ ⟨c, hcA⟩))
  have hb_mem : b ∈ D ⊔ Subgroup.zpowers c := by
    rw [hAk]
    exact hbA
  have hb'' : b ∈ (D : Set G) * (Subgroup.zpowers c : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right D (Subgroup.zpowers c) hDk]
    exact hb_mem
  obtain ⟨a, haD, z, hz, haz⟩ := hb''
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hb_eq : b = a * c ^ j := haz.symm
  have hb_card : Nat.card (Subgroup.zpowers b) = 3 :=
    (zpowers_mem_omegaA_iff.mp h.omega_b).2.1
  have hc_card : Nat.card (Subgroup.zpowers c) = 3 :=
    (zpowers_mem_omegaA_iff.mp h.sec15R.toSec13Data.zpowers_mem_omegaA).2.1
  have hb_order : orderOf b = 3 := by
    rw [← Nat.card_zpowers]
    exact hb_card
  have hz_mem : t * b * t⁻¹ ∈ Subgroup.zpowers b :=
    (Subgroup.mem_normalizer_iff.mp htB b).mp (Subgroup.mem_zpowers b)
  have hz_ne : t * b * t⁻¹ ≠ 1 := by
    intro h1
    have h2 : b = 1 := by
      calc b = t⁻¹ * (t * b * t⁻¹) * t := by group
        _ = t⁻¹ * 1 * t := by rw [h1]
        _ = 1 := by group
    exact b_ne_one h h2
  have haz_mem : t * b * t⁻¹ ∈ (Finset.range (orderOf b)).image (b ^ ·) := by
    rwa [← mem_zpowers_iff_mem_range_orderOf]
  obtain ⟨i, hi, hi_eq⟩ := Finset.mem_image.mp haz_mem
  rw [Finset.mem_range] at hi
  have hi3 : i < 3 := by simpa [hb_order] using hi
  have hz_eq : t * b * t⁻¹ = a⁻¹ * c ^ j := by
    calc t * b * t⁻¹ = (t * a * t⁻¹) * (t * c ^ j * t⁻¹) := by rw [hb_eq]; group
      _ = a⁻¹ * c ^ j := by
        rw [htinv a haD]
        have hcomm : Commute t c := htc
        rw [show t * c ^ j * t⁻¹ = c ^ j from by
          rw [(hcomm.zpow_right j).eq]
          group]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
  · exfalso
    have h1 : t * b * t⁻¹ = 1 := by simpa using hi_eq.symm
    exact hz_ne h1
  ·
    have hb' : t * b * t⁻¹ = b := by simpa using hi_eq.symm
    have ha_eq : a⁻¹ = a := by
      have h1 : a⁻¹ * c ^ j = a * c ^ j := by
        rw [← hz_eq, hb']
        exact hb_eq
      exact mul_right_cancel h1
    have ha2 : a ^ 2 = 1 := by
      have := congrArg (fun w => w * a) ha_eq
      simpa [pow_two] using this.symm
    have ha3 : a ^ 3 = 1 := hA.2 a haD.1
    have ha1 : a = 1 := by
      calc a = a * a ^ 2 := by rw [ha2, mul_one]
        _ = a ^ 3 := by group
        _ = 1 := ha3
    have hb_c : b ∈ Subgroup.zpowers c := by
      rw [hb_eq, ha1, one_mul]
      exact (Subgroup.zpowers c).zpow_mem (Subgroup.mem_zpowers c) j
    have hle : Subgroup.zpowers b ≤ Subgroup.zpowers c := Subgroup.zpowers_le.mpr hb_c
    exfalso
    exact h.ne_c (Subgroup.eq_of_le_of_card_ge hle (by rw [hb_card, hc_card]))
  ·
    have ha3 : a ^ 3 = 1 := hA.2 a haD.1
    have ha_inv : a⁻¹ = a ^ 2 := by
      refine inv_eq_of_mul_eq_one_right ?_
      calc a * a ^ 2 = a ^ 3 := by group
        _ = 1 := ha3
    have hcomm_ac : Commute a c :=
      congrArg Subtype.val (hA.1.is_comm.comm ⟨a, haD.1⟩ ⟨c, hcA⟩)
    have hcomm : Commute a (c ^ j) := hcomm_ac.zpow_right j
    have hb2 : b ^ 2 = a ^ 2 * (c ^ j) ^ 2 := by
      rw [hb_eq]
      exact hcomm.mul_pow 2
    have h1 : a ^ 2 * (c ^ j) ^ 2 = a ^ 2 * c ^ j := by
      have := hi_eq
      rw [hb2, hz_eq, ha_inv] at this
      exact this
    have hc2 : (c ^ j) ^ 2 = c ^ j := mul_left_cancel h1
    have hc1 : c ^ j = 1 := by
      have := congrArg (fun w => w * (c ^ j)⁻¹) hc2
      simpa [pow_two, mul_assoc] using this
    have hbD : b ∈ D := by
      rw [hb_eq, hc1, mul_one]
      exact haD
    exact (Subgroup.mem_inf.mp hbD).2

theorem c_mem_y₂ (h : Conf683 A c L Y₁ Y₂ S b Lb) : c ∈ Y₂ := by
  classical
  obtain ⟨t, -, htA, htS, -, htb, htinv⟩ := exists_t₂ h
  have htAS : t ∈ Subgroup.normalizer ((A ⊔ S : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_sup A S ⟨htA, htS⟩
  have htY₁ : t ∈ Subgroup.normalizer (Y₁ : Set G) := normalizer_sup_le₁ h htAS
  have htC : t ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    mem_normalizer_zpowers_of_mem_normalizer_sectionCentralizer h.sc₁ htA htY₁
  let D := A ⊓ Y₂
  have hA := isElemAbelian_A h
  have hbA := b_mem h
  have hAk := (card_inf₂ h).2.2
  have hDk : D ≤ Subgroup.normalizer ((Subgroup.zpowers b : Subgroup G) : Set G) := by
    intro d hd
    refine CFSG.GorensteinWalter.centralizer_singleton_le_normalizer_zpowers b ?_
    exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
      (hA.1.is_comm.comm ⟨d, (Subgroup.mem_inf.mp hd).1⟩ ⟨b, hbA⟩))
  have hc_mem : c ∈ D ⊔ Subgroup.zpowers b := by
    rw [hAk]
    exact c_mem h
  have hc'' : c ∈ (D : Set G) * (Subgroup.zpowers b : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right D (Subgroup.zpowers b) hDk]
    exact hc_mem
  obtain ⟨a, haD, z, hz, haz⟩ := hc''
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hc_eq : c = a * b ^ j := haz.symm
  have hc_card : Nat.card (Subgroup.zpowers c) = 3 :=
    (zpowers_mem_omegaA_iff.mp h.sec15R.toSec13Data.zpowers_mem_omegaA).2.1
  have hb_card : Nat.card (Subgroup.zpowers b) = 3 :=
    (zpowers_mem_omegaA_iff.mp h.omega_b).2.1
  have hc_order : orderOf c = 3 := by
    rw [← Nat.card_zpowers]
    exact hc_card
  have hz_mem : t * c * t⁻¹ ∈ Subgroup.zpowers c :=
    (Subgroup.mem_normalizer_iff.mp htC c).mp (Subgroup.mem_zpowers c)
  have hz_ne : t * c * t⁻¹ ≠ 1 := by
    intro h1
    have h2 : c = 1 := by
      calc c = t⁻¹ * (t * c * t⁻¹) * t := by group
        _ = t⁻¹ * 1 * t := by rw [h1]
        _ = 1 := by group
    exact c_ne_one h h2
  have haz_mem : t * c * t⁻¹ ∈ (Finset.range (orderOf c)).image (c ^ ·) := by
    rwa [← mem_zpowers_iff_mem_range_orderOf]
  obtain ⟨i, hi, hi_eq⟩ := Finset.mem_image.mp haz_mem
  rw [Finset.mem_range] at hi
  have hi3 : i < 3 := by simpa [hc_order] using hi
  have hz_eq : t * c * t⁻¹ = a⁻¹ * b ^ j := by
    calc t * c * t⁻¹ = (t * a * t⁻¹) * (t * b ^ j * t⁻¹) := by rw [hc_eq]; group
      _ = a⁻¹ * b ^ j := by
        rw [htinv a haD]
        have hcomm_ac : Commute t b := htb
        rw [show t * b ^ j * t⁻¹ = b ^ j from by
          rw [(hcomm_ac.zpow_right j).eq]
          group]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
  · exfalso
    have h1 : t * c * t⁻¹ = 1 := by simpa using hi_eq.symm
    exact hz_ne h1
  ·
    have hc' : t * c * t⁻¹ = c := by simpa using hi_eq.symm
    have ha_eq : a⁻¹ = a := by
      have h1 : a⁻¹ * b ^ j = a * b ^ j := by
        rw [← hz_eq, hc']
        exact hc_eq
      exact mul_right_cancel h1
    have ha2 : a ^ 2 = 1 := by
      have := congrArg (fun w => w * a) ha_eq
      simpa [pow_two] using this.symm
    have ha3 : a ^ 3 = 1 := hA.2 a haD.1
    have ha1 : a = 1 := by
      calc a = a * a ^ 2 := by rw [ha2, mul_one]
        _ = a ^ 3 := by group
        _ = 1 := ha3
    have hc_b : c ∈ Subgroup.zpowers b := by
      rw [hc_eq, ha1, one_mul]
      exact (Subgroup.zpowers b).zpow_mem (Subgroup.mem_zpowers b) j
    have hle : Subgroup.zpowers c ≤ Subgroup.zpowers b := Subgroup.zpowers_le.mpr hc_b
    exfalso
    exact h.ne_c.symm (Subgroup.eq_of_le_of_card_ge hle (by rw [hc_card, hb_card]))
  ·
    have ha3 : a ^ 3 = 1 := hA.2 a haD.1
    have ha_inv : a⁻¹ = a ^ 2 := by
      refine inv_eq_of_mul_eq_one_right ?_
      calc a * a ^ 2 = a ^ 3 := by group
        _ = 1 := ha3
    have hcomm_ab : Commute a b :=
      congrArg Subtype.val (hA.1.is_comm.comm ⟨a, haD.1⟩ ⟨b, hbA⟩)
    have hcomm : Commute a (b ^ j) := hcomm_ab.zpow_right j
    have hc2 : c ^ 2 = a ^ 2 * (b ^ j) ^ 2 := by
      rw [hc_eq]
      exact hcomm.mul_pow 2
    have h1 : a ^ 2 * (b ^ j) ^ 2 = a ^ 2 * b ^ j := by
      have := hi_eq
      rw [hc2, hz_eq, ha_inv] at this
      exact this
    have hb2 : (b ^ j) ^ 2 = b ^ j := mul_left_cancel h1
    have hb1 : b ^ j = 1 := by
      have := congrArg (fun w => w * (b ^ j)⁻¹) hb2
      simpa [pow_two, mul_assoc] using this
    have hcD : c ∈ D := by
      rw [hc_eq, hb1, mul_one]
      exact haD
    exact (Subgroup.mem_inf.mp hcD).2

theorem exists_b' (h : Conf683 A c L Y₁ Y₂ S b Lb) :
    ∃ b' ∈ A, b' ≠ 1 ∧ A ⊓ Y₁ ⊓ Y₂ = Subgroup.zpowers b' ∧
      A ⊓ Y₁ = Subgroup.zpowers b ⊔ Subgroup.zpowers b' ∧
      A ⊓ Y₂ = Subgroup.zpowers c ⊔ Subgroup.zpowers b' := by
  classical
  let D₁ : Subgroup G := A ⊓ Y₁
  let D₂ : Subgroup G := A ⊓ Y₂
  let D : Subgroup G := D₁ ⊓ D₂
  have hA := isElemAbelian_A h
  have hD₁card : Nat.card D₁ = 9 := (card_inf₁ h).1
  have hD₂card : Nat.card D₂ = 9 := (card_inf₂ h).1
  have hAD₁ : D₁ ≤ A := inf_le_left
  have hAD₂ : D₂ ≤ A := inf_le_left
  have hcD₂ : c ∈ D₂ := ⟨c_mem h, c_mem_y₂ h⟩
  have hc_not_D₁ : c ∉ D₁ := fun hc => (card_inf₁ h).2.1 (Subgroup.mem_inf.mp hc).2
  have hne : D₁ ≠ D₂ := fun heq => hc_not_D₁ (heq ▸ hcD₂)
  have hcomm : ∀ x ∈ D₁, ∀ y ∈ D₂, x * y * x⁻¹ ∈ D₂ := by
    intro x hx y hy
    have hxA : x ∈ A := hAD₁ hx
    have hyA : y ∈ A := hAD₂ hy
    have hcommxy : x * y = y * x := congrArg Subtype.val
      (hA.1.is_comm.comm ⟨x, hxA⟩ ⟨y, hyA⟩)
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [show x * y * x⁻¹ = y by rw [hcommxy]; group]
      exact hyA
    · rw [show x * y * x⁻¹ = y by rw [hcommxy]; group]
      exact (Subgroup.mem_inf.mp hy).2
  have hcard :=
    CFSG.Timmesfeld.LocalTwoSubgroups.FrobeniusFixedSpaceBounds.card_sup_mul_card_inf
      D₁ D₂ hcomm
  have hsup_le : D₁ ⊔ D₂ ≤ A := sup_le hAD₁ hAD₂
  have hsup_card : Nat.card ↥(D₁ ⊔ D₂) ≤ 27 :=
    (Subgroup.card_le_of_le hsup_le).trans (le_of_eq (card_A h))
  have hprod : Nat.card ↥(D₁ ⊔ D₂) * Nat.card ↥(D₁ ⊓ D₂) = 81 := by
    rw [hcard, hD₁card, hD₂card]
  have hDcard : Nat.card D = 3 := by
    have hge3 : 3 ≤ Nat.card ↥(D₁ ⊓ D₂) := by
      have h1 : 81 ≤ 27 * Nat.card ↥(D₁ ⊓ D₂) := by
        rw [← hprod]
        exact Nat.mul_le_mul_right _ hsup_card
      omega
    have hdvd : Nat.card ↥(D₁ ⊓ D₂) ∣ 9 := by
      have h := Subgroup.card_dvd_of_le (show D₁ ⊓ D₂ ≤ D₁ from inf_le_left)
      simpa [hD₁card] using h
    have hle9 : Nat.card ↥(D₁ ⊓ D₂) ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd
    have hne9 : Nat.card ↥(D₁ ⊓ D₂) ≠ 9 := by
      intro h9
      have heq : D₁ ⊓ D₂ = D₁ :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h9, hD₁card])
      have hle : D₁ ≤ D₂ := by rw [← heq]; exact inf_le_right
      exact hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hD₁card, hD₂card]))
    have h3 : Nat.card ↥(D₁ ⊓ D₂) = 3 := by
      have hdvd' : Nat.card ↥(D₁ ⊓ D₂) ∣ 3 ^ 2 := by simpa using hdvd
      obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow (p := 3) (m := 2) Nat.prime_three).mp hdvd'
      have hj2 : j ≤ 2 := by simpa using hjle
      interval_cases j
      · rw [hj] at hge3
        norm_num at hge3
      · rw [hj]
        norm_num
      · exfalso
        exact hne9 hj
    simpa [D] using h3
  have hDne : D ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hDcard
    norm_num at hDcard
  haveI : Nontrivial ↥D := (Subgroup.nontrivial_iff_ne_bot D).mpr hDne
  obtain ⟨b', hb'ne⟩ := exists_ne (1 : ↥D)
  have hb'D : (b' : G) ∈ D := b'.2
  have hb'A : (b' : G) ∈ A := hAD₁ (Subgroup.mem_inf.mp hb'D).1
  have hb'Y₁ : (b' : G) ∈ Y₁ := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hb'D).1).2
  have hb'Y₂ : (b' : G) ∈ Y₂ := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hb'D).2).2
  have hb'ne' : (b' : G) ≠ 1 := by
    intro h1
    exact hb'ne (Subtype.ext h1)
  have hb'ord : orderOf (b' : G) = 3 := by
    have hdvd : orderOf (b' : G) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one (hA.2 (b' : G) hb'A)
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hb'ne'
    · exact h3
  have hb'card : Nat.card (Subgroup.zpowers (b' : G)) = 3 := by
    rw [Nat.card_zpowers, hb'ord]
  have hD_eq : D = Subgroup.zpowers (b' : G) := by
    have hle : Subgroup.zpowers (b' : G) ≤ D := Subgroup.zpowers_le.mpr hb'D
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hDcard, hb'card])).symm
  have hbA : b ∈ A := b_mem h
  have hbY₁ : b ∈ Y₁ := b_mem_y₁ h
  have hb_not_Y₂ : b ∉ Y₂ := (card_inf₂ h).2.1
  have hcA : c ∈ A := c_mem h
  have hc_not_Y₁ : c ∉ Y₁ := (card_inf₁ h).2.1
  have hb_card : Nat.card (Subgroup.zpowers b) = 3 :=
    (zpowers_mem_omegaA_iff.mp h.omega_b).2.1
  have hc_card : Nat.card (Subgroup.zpowers c) = 3 :=
    (zpowers_mem_omegaA_iff.mp h.sec15R.toSec13Data.zpowers_mem_omegaA).2.1
  have hb'notzpb : (b' : G) ∉ Subgroup.zpowers b := by
    intro hmem
    have hle : Subgroup.zpowers (b' : G) ≤ Subgroup.zpowers b := Subgroup.zpowers_le.mpr hmem
    have heq : Subgroup.zpowers (b' : G) = Subgroup.zpowers b :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hb'card, hb_card])
    have hbY₂ : b ∈ Y₂ := by
      have hb_mem : b ∈ Subgroup.zpowers (b' : G) := by
        rw [heq]
        exact Subgroup.mem_zpowers b
      exact (Subgroup.zpowers_le.mpr hb'Y₂) hb_mem
    exact hb_not_Y₂ hbY₂
  have hb'notzpc : (b' : G) ∉ Subgroup.zpowers c := by
    intro hmem
    have hle : Subgroup.zpowers (b' : G) ≤ Subgroup.zpowers c := Subgroup.zpowers_le.mpr hmem
    have heq : Subgroup.zpowers (b' : G) = Subgroup.zpowers c :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hb'card, hc_card])
    have hcY₁ : c ∈ Y₁ := by
      have hc_mem : c ∈ Subgroup.zpowers (b' : G) := by
        rw [heq]
        exact Subgroup.mem_zpowers c
      exact (Subgroup.zpowers_le.mpr hb'Y₁) hc_mem
    exact hc_not_Y₁ hcY₁
  have hdisj_b : Disjoint (Subgroup.zpowers b) (Subgroup.zpowers (b' : G)) := by
    have hdvd : Nat.card ↥(Subgroup.zpowers b ⊓ Subgroup.zpowers (b' : G)) ∣ 3 := by
      have h := Subgroup.card_dvd_of_le
        (show Subgroup.zpowers b ⊓ Subgroup.zpowers (b' : G) ≤ Subgroup.zpowers b from inf_le_left)
      simpa [hb_card] using h
    have hne3 : Nat.card ↥(Subgroup.zpowers b ⊓ Subgroup.zpowers (b' : G)) ≠ 3 := by
      intro h3
      have heq : Subgroup.zpowers b ⊓ Subgroup.zpowers (b' : G) = Subgroup.zpowers b :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hb_card])
      have hle : Subgroup.zpowers b ≤ Subgroup.zpowers (b' : G) := by
        rw [← heq]; exact inf_le_right
      have heq2 : Subgroup.zpowers b = Subgroup.zpowers (b' : G) :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hb_card, hb'card])
      have hb'zpb : (b' : G) ∈ Subgroup.zpowers b := by
        rw [heq2]
        exact Subgroup.mem_zpowers (b' : G)
      exact hb'notzpb hb'zpb
    have h1 : Nat.card ↥(Subgroup.zpowers b ⊓ Subgroup.zpowers (b' : G)) = 1 := by
      rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hdvd with h1 | h3
      · exact h1
      · exact absurd h3 hne3
    exact disjoint_iff.mpr (Subgroup.card_eq_one.mp h1)
  have hdisj_c : Disjoint (Subgroup.zpowers c) (Subgroup.zpowers (b' : G)) := by
    have hdvd : Nat.card ↥(Subgroup.zpowers c ⊓ Subgroup.zpowers (b' : G)) ∣ 3 := by
      have h := Subgroup.card_dvd_of_le
        (show Subgroup.zpowers c ⊓ Subgroup.zpowers (b' : G) ≤ Subgroup.zpowers c from inf_le_left)
      simpa [hc_card] using h
    have hne3 : Nat.card ↥(Subgroup.zpowers c ⊓ Subgroup.zpowers (b' : G)) ≠ 3 := by
      intro h3
      have heq : Subgroup.zpowers c ⊓ Subgroup.zpowers (b' : G) = Subgroup.zpowers c :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hc_card])
      have hle : Subgroup.zpowers c ≤ Subgroup.zpowers (b' : G) := by
        rw [← heq]; exact inf_le_right
      have heq2 : Subgroup.zpowers c = Subgroup.zpowers (b' : G) :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hc_card, hb'card])
      have hb'zpc : (b' : G) ∈ Subgroup.zpowers c := by
        rw [heq2]
        exact Subgroup.mem_zpowers (b' : G)
      exact hb'notzpc hb'zpc
    have h1 : Nat.card ↥(Subgroup.zpowers c ⊓ Subgroup.zpowers (b' : G)) = 1 := by
      rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hdvd with h1 | h3
      · exact h1
      · exact absurd h3 hne3
    exact disjoint_iff.mpr (Subgroup.card_eq_one.mp h1)
  have hsup_b : Nat.card ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers (b' : G)) = 9 := by
    have hcen : (b' : G) ∈ Subgroup.centralizer ({b} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
        (hA.1.is_comm.comm ⟨(b' : G), hb'A⟩ ⟨b, hbA⟩))
    have hnorm : Subgroup.zpowers (b' : G) ≤
        Subgroup.normalizer (Subgroup.zpowers b : Set G) :=
      (Subgroup.zpowers_le.mpr hcen).trans
        (CFSG.GorensteinWalter.centralizer_singleton_le_normalizer_zpowers b)
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (Subgroup.zpowers b) (Subgroup.zpowers (b' : G)) hnorm hdisj_b, hb_card, hb'card]
  have hsup_c : Nat.card ↥(Subgroup.zpowers c ⊔ Subgroup.zpowers (b' : G)) = 9 := by
    have hcen : (b' : G) ∈ Subgroup.centralizer ({c} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
        (hA.1.is_comm.comm ⟨(b' : G), hb'A⟩ ⟨c, hcA⟩))
    have hnorm : Subgroup.zpowers (b' : G) ≤
        Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
      (Subgroup.zpowers_le.mpr hcen).trans
        (CFSG.GorensteinWalter.centralizer_singleton_le_normalizer_zpowers c)
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (Subgroup.zpowers c) (Subgroup.zpowers (b' : G)) hnorm hdisj_c, hc_card, hb'card]
  refine ⟨(b' : G), hb'A, hb'ne', ?_, ?_, ?_⟩
  · have hD_eq' : D = A ⊓ Y₁ ⊓ Y₂ := by
      simp [D, D₁, D₂, inf_assoc, inf_left_comm, inf_comm,
        inf_of_le_left (inf_le_left : A ⊓ Y₁ ≤ A)]
    exact hD_eq'.symm.trans hD_eq
  · refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
    · exact sup_le (Subgroup.zpowers_le.mpr ⟨hbA, hbY₁⟩)
        (Subgroup.zpowers_le.mpr ⟨hb'A, hb'Y₁⟩)
    · rw [hD₁card, hsup_b]
  · refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
    · exact sup_le (Subgroup.zpowers_le.mpr ⟨hcA, c_mem_y₂ h⟩)
        (Subgroup.zpowers_le.mpr ⟨hb'A, hb'Y₂⟩)
    · rw [hD₂card, hsup_c]

private theorem not_mem_zpowers_of_mem_of_not_mem {A K : Subgroup G} {x y : G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hx : x ∈ A) (hxK : x ∉ K)
    (hy : y ∈ A) (hyK : y ∈ K) (hy1 : y ≠ 1) :
    y ∉ Subgroup.zpowers x := by
  intro hmem
  have hx1 : x ≠ 1 := by
    intro hx0
    exact hxK (hx0 ▸ K.one_mem)
  have hxord : orderOf x = 3 := by
    have hdvd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one (hA.2 x hx)
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hx1
    · exact h3
  have hyord : orderOf y = 3 := by
    have hdvd : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one (hA.2 y hy)
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hy1
    · exact h3
  have hle : Subgroup.zpowers y ≤ Subgroup.zpowers x := Subgroup.zpowers_le.mpr hmem
  have heq : Subgroup.zpowers y = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Nat.card_zpowers, Nat.card_zpowers, hyord, hxord])
  have hxmem : x ∈ Subgroup.zpowers y := by
    rw [heq]
    exact Subgroup.mem_zpowers x
  exact hxK (Subgroup.zpowers_le.mpr hyK hxmem)

theorem a7Rep_not_mem₂ (h : Conf683 A c L Y₁ Y₂ S b Lb)
    (φ₂ : ↥Y₂ ⧸ CFSG.pCore 2 ↥Y₂ ≃* alternatingGroup (Fin 7)) {t : G}
    (htA : t ∈ Subgroup.normalizer (A : Set G))
    (htS : t ∈ Subgroup.normalizer (S : Set G)) (htc : t * c = c * t)
    (ht : ∀ e ∈ A ⊓ Y₁, t * e * t⁻¹ = e⁻¹) :
    ∃ ht2 : t ∈ Subgroup.normalizer (Y₂ : Set G),
      CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep Y₂ φ₂ ⟨t, ht2⟩ ∉ alternatingGroup (Fin 7) := by
  classical
  obtain ⟨b', hb'A, hb'ne, hb'D, -, -⟩ := exists_b' h
  have hb'Dmem : b' ∈ A ⊓ Y₁ ⊓ Y₂ := by
    rw [hb'D]
    exact Subgroup.mem_zpowers b'
  have hb'D1 : b' ∈ A ⊓ Y₁ := (Subgroup.mem_inf.mp hb'Dmem).1
  have hb'D2 : b' ∈ A ⊓ Y₂ :=
    ⟨(Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hb'Dmem).1).1,
      (Subgroup.mem_inf.mp hb'Dmem).2⟩
  have hb'Y₁ : b' ∈ Y₁ := (Subgroup.mem_inf.mp hb'D1).2
  have hA := isElemAbelian_A h
  have hcD2 : c ∈ A ⊓ Y₂ := ⟨c_mem h, c_mem_y₂ h⟩
  have hc_not_Y₁ : c ∉ Y₁ := (card_inf₁ h).2.1
  have hb'notzpc : b' ∉ Subgroup.zpowers c :=
    not_mem_zpowers_of_mem_of_not_mem hA (c_mem h) hc_not_Y₁ hb'A hb'Y₁ hb'ne
  have htAS : t ∈ Subgroup.normalizer ((A ⊔ S : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_sup A S ⟨htA, htS⟩
  have ht2 : t ∈ Subgroup.normalizer (Y₂ : Set G) := normalizer_sup_le₂ h htAS
  let N := Subgroup.normalizer (Y₂ : Set G)
  let ρ := CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep Y₂ φ₂
  let P : Subgroup (Equiv.Perm (Fin 7)) := ((A ⊓ Y₂).subgroupOf N).map ρ
  have hP9 : Nat.card P = 9 := by
    simpa [P, N, ρ] using card_map_a7Rep_inf (A := A) (K := Y₂) hA φ₂ (card_inf₂ h).1
  have he₁P : ρ ⟨c, Subgroup.le_normalizer (Subgroup.mem_inf.mp hcD2).2⟩ ∈ P :=
    Subgroup.mem_map.mpr ⟨⟨c, Subgroup.le_normalizer (Subgroup.mem_inf.mp hcD2).2⟩,
      Subgroup.mem_subgroupOf.mpr hcD2, rfl⟩
  have he₂P : ρ ⟨b', Subgroup.le_normalizer (Subgroup.mem_inf.mp hb'D2).2⟩ ∈ P :=
    Subgroup.mem_map.mpr ⟨⟨b', Subgroup.le_normalizer (Subgroup.mem_inf.mp hb'D2).2⟩,
      Subgroup.mem_subgroupOf.mpr hb'D2, rfl⟩
  have he₁1 : ρ ⟨c, Subgroup.le_normalizer (Subgroup.mem_inf.mp hcD2).2⟩ ≠ 1 := by
    intro h1
    have hcO : c ∈ CFSG.Open.pCoreOf 2 Y₂ :=
      (a7Rep_eq_one_iff_mem_pCoreOf φ₂ (Subgroup.mem_inf.mp hcD2).2).mp h1
    have hc1 : c = 1 := eq_one_of_mem_two_group_of_mem_elemAbelian_three
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y₂) hA hcO (Subgroup.mem_inf.mp hcD2).1
    exact c_ne_one h hc1
  have he₂1 : ρ ⟨b', Subgroup.le_normalizer (Subgroup.mem_inf.mp hb'D2).2⟩ ∉
      Subgroup.zpowers (ρ ⟨c, Subgroup.le_normalizer (Subgroup.mem_inf.mp hcD2).2⟩) := by
    intro hmem
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hcjD2 : c ^ j ∈ A ⊓ Y₂ :=
      ⟨A.zpow_mem (Subgroup.mem_inf.mp hcD2).1 j,
        Y₂.zpow_mem (Subgroup.mem_inf.mp hcD2).2 j⟩
    have hρcj : ρ ⟨c ^ j, Subgroup.le_normalizer (Subgroup.mem_inf.mp hcjD2).2⟩ =
        (ρ ⟨c, Subgroup.le_normalizer (Subgroup.mem_inf.mp hcD2).2⟩) ^ j := by
      have e : (⟨c ^ j, Subgroup.le_normalizer (Subgroup.mem_inf.mp hcjD2).2⟩ : ↥N) =
          (⟨c, Subgroup.le_normalizer (Subgroup.mem_inf.mp hcD2).2⟩ : ↥N) ^ j :=
        Subtype.ext rfl
      rw [e]
      exact map_zpow ρ _ j
    have hinj := a7Rep_injective_inf (A := A) (K := Y₂) hA φ₂
    have heq : (⟨c ^ j, hcjD2⟩ : ↥(A ⊓ Y₂)) = ⟨b', hb'D2⟩ := by
      refine hinj ?_
      change ρ ⟨c ^ j, Subgroup.le_normalizer (Subgroup.mem_inf.mp hcjD2).2⟩ =
        ρ ⟨b', Subgroup.le_normalizer (Subgroup.mem_inf.mp hb'D2).2⟩
      rw [hρcj]
      exact hj
    have hmemc : b' ∈ Subgroup.zpowers c := by
      have : b' = c ^ j := (congrArg Subtype.val heq).symm
      rw [this]
      exact (Subgroup.zpowers c).zpow_mem (Subgroup.mem_zpowers c) j
    exact hb'notzpc hmemc
  have hfix : ρ ⟨t, ht2⟩ * ρ ⟨c, Subgroup.le_normalizer (Subgroup.mem_inf.mp hcD2).2⟩ *
      (ρ ⟨t, ht2⟩)⁻¹ = ρ ⟨c, Subgroup.le_normalizer (Subgroup.mem_inf.mp hcD2).2⟩ := by
    have e : (⟨t, ht2⟩ * ⟨c, Subgroup.le_normalizer (Subgroup.mem_inf.mp hcD2).2⟩ *
        ⟨t, ht2⟩⁻¹ : ↥N) = ⟨c, Subgroup.le_normalizer (Subgroup.mem_inf.mp hcD2).2⟩ :=
      Subtype.ext (by
        change t * c * t⁻¹ = c
        rw [htc]
        group)
    calc ρ ⟨t, ht2⟩ * ρ ⟨c, Subgroup.le_normalizer (Subgroup.mem_inf.mp hcD2).2⟩ *
          (ρ ⟨t, ht2⟩)⁻¹
        = ρ (⟨t, ht2⟩ * ⟨c, Subgroup.le_normalizer (Subgroup.mem_inf.mp hcD2).2⟩ *
            ⟨t, ht2⟩⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = ρ ⟨c, Subgroup.le_normalizer (Subgroup.mem_inf.mp hcD2).2⟩ := by rw [e]
  have hinv : ρ ⟨t, ht2⟩ * ρ ⟨b', Subgroup.le_normalizer (Subgroup.mem_inf.mp hb'D2).2⟩ *
      (ρ ⟨t, ht2⟩)⁻¹ =
        (ρ ⟨b', Subgroup.le_normalizer (Subgroup.mem_inf.mp hb'D2).2⟩)⁻¹ := by
    have e : (⟨t, ht2⟩ * ⟨b', Subgroup.le_normalizer (Subgroup.mem_inf.mp hb'D2).2⟩ *
        ⟨t, ht2⟩⁻¹ : ↥N) = (⟨b', Subgroup.le_normalizer (Subgroup.mem_inf.mp hb'D2).2⟩ : ↥N)⁻¹ :=
      Subtype.ext (by
        change t * b' * t⁻¹ = b'⁻¹
        exact ht b' hb'D1)
    calc ρ ⟨t, ht2⟩ * ρ ⟨b', Subgroup.le_normalizer (Subgroup.mem_inf.mp hb'D2).2⟩ *
          (ρ ⟨t, ht2⟩)⁻¹
        = ρ (⟨t, ht2⟩ * ⟨b', Subgroup.le_normalizer (Subgroup.mem_inf.mp hb'D2).2⟩ *
            ⟨t, ht2⟩⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = ρ ((⟨b', Subgroup.le_normalizer (Subgroup.mem_inf.mp hb'D2).2⟩ : ↥N)⁻¹) := by rw [e]
      _ = (ρ ⟨b', Subgroup.le_normalizer (Subgroup.mem_inf.mp hb'D2).2⟩)⁻¹ := by rw [map_inv]
  exact ⟨ht2, CFSG.RankThree.PartTwo.KFacts.KP2.not_mem_alternatingGroup_of_fix_inv
    hP9 he₁P he₂P he₁1 he₂1 hfix hinv⟩

theorem a7Rep_not_mem₁ (h : Conf683 A c L Y₁ Y₂ S b Lb)
    (φ₁ : ↥Y₁ ⧸ CFSG.pCore 2 ↥Y₁ ≃* alternatingGroup (Fin 7)) {t : G}
    (htA : t ∈ Subgroup.normalizer (A : Set G))
    (htS : t ∈ Subgroup.normalizer (S : Set G)) (htb : t * b = b * t)
    (ht : ∀ e ∈ A ⊓ Y₂, t * e * t⁻¹ = e⁻¹) :
    ∃ ht1 : t ∈ Subgroup.normalizer (Y₁ : Set G),
      CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep Y₁ φ₁ ⟨t, ht1⟩ ∉ alternatingGroup (Fin 7) := by
  classical
  obtain ⟨b', hb'A, hb'ne, hb'D, -, -⟩ := exists_b' h
  have hb'Dmem : b' ∈ A ⊓ Y₁ ⊓ Y₂ := by
    rw [hb'D]
    exact Subgroup.mem_zpowers b'
  have hb'D1 : b' ∈ A ⊓ Y₁ := (Subgroup.mem_inf.mp hb'Dmem).1
  have hb'D2 : b' ∈ A ⊓ Y₂ :=
    ⟨(Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hb'Dmem).1).1,
      (Subgroup.mem_inf.mp hb'Dmem).2⟩
  have hb'Y₂ : b' ∈ Y₂ := (Subgroup.mem_inf.mp hb'D2).2
  have hA := isElemAbelian_A h
  have hbD1 : b ∈ A ⊓ Y₁ := ⟨b_mem h, b_mem_y₁ h⟩
  have hb_not_Y₂ : b ∉ Y₂ := (card_inf₂ h).2.1
  have hb'notzpb : b' ∉ Subgroup.zpowers b :=
    not_mem_zpowers_of_mem_of_not_mem hA (b_mem h) hb_not_Y₂ hb'A hb'Y₂ hb'ne
  have htAS : t ∈ Subgroup.normalizer ((A ⊔ S : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_sup A S ⟨htA, htS⟩
  have ht1 : t ∈ Subgroup.normalizer (Y₁ : Set G) := normalizer_sup_le₁ h htAS
  let N := Subgroup.normalizer (Y₁ : Set G)
  let ρ := CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep Y₁ φ₁
  let P : Subgroup (Equiv.Perm (Fin 7)) := ((A ⊓ Y₁).subgroupOf N).map ρ
  have hP9 : Nat.card P = 9 := by
    simpa [P, N, ρ] using card_map_a7Rep_inf (A := A) (K := Y₁) hA φ₁ (card_inf₁ h).1
  have he₁P : ρ ⟨b, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbD1).2⟩ ∈ P :=
    Subgroup.mem_map.mpr ⟨⟨b, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbD1).2⟩,
      Subgroup.mem_subgroupOf.mpr hbD1, rfl⟩
  have he₂P : ρ ⟨b', Subgroup.le_normalizer (Subgroup.mem_inf.mp hb'D1).2⟩ ∈ P :=
    Subgroup.mem_map.mpr ⟨⟨b', Subgroup.le_normalizer (Subgroup.mem_inf.mp hb'D1).2⟩,
      Subgroup.mem_subgroupOf.mpr hb'D1, rfl⟩
  have he₁1 : ρ ⟨b, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbD1).2⟩ ≠ 1 := by
    intro h1
    have hbO : b ∈ CFSG.Open.pCoreOf 2 Y₁ :=
      (a7Rep_eq_one_iff_mem_pCoreOf φ₁ (Subgroup.mem_inf.mp hbD1).2).mp h1
    have hb1 : b = 1 := eq_one_of_mem_two_group_of_mem_elemAbelian_three
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y₁) hA hbO (Subgroup.mem_inf.mp hbD1).1
    exact b_ne_one h hb1
  have he₂1 : ρ ⟨b', Subgroup.le_normalizer (Subgroup.mem_inf.mp hb'D1).2⟩ ∉
      Subgroup.zpowers (ρ ⟨b, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbD1).2⟩) := by
    intro hmem
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hbjD1 : b ^ j ∈ A ⊓ Y₁ :=
      ⟨A.zpow_mem (Subgroup.mem_inf.mp hbD1).1 j,
        Y₁.zpow_mem (Subgroup.mem_inf.mp hbD1).2 j⟩
    have hρbj : ρ ⟨b ^ j, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbjD1).2⟩ =
        (ρ ⟨b, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbD1).2⟩) ^ j := by
      have e : (⟨b ^ j, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbjD1).2⟩ : ↥N) =
          (⟨b, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbD1).2⟩ : ↥N) ^ j :=
        Subtype.ext rfl
      rw [e]
      exact map_zpow ρ _ j
    have hinj := a7Rep_injective_inf (A := A) (K := Y₁) hA φ₁
    have heq : (⟨b ^ j, hbjD1⟩ : ↥(A ⊓ Y₁)) = ⟨b', hb'D1⟩ := by
      refine hinj ?_
      change ρ ⟨b ^ j, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbjD1).2⟩ =
        ρ ⟨b', Subgroup.le_normalizer (Subgroup.mem_inf.mp hb'D1).2⟩
      rw [hρbj]
      exact hj
    have hmemb : b' ∈ Subgroup.zpowers b := by
      have : b' = b ^ j := (congrArg Subtype.val heq).symm
      rw [this]
      exact (Subgroup.zpowers b).zpow_mem (Subgroup.mem_zpowers b) j
    exact hb'notzpb hmemb
  have hfix : ρ ⟨t, ht1⟩ * ρ ⟨b, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbD1).2⟩ *
      (ρ ⟨t, ht1⟩)⁻¹ = ρ ⟨b, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbD1).2⟩ := by
    have e : (⟨t, ht1⟩ * ⟨b, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbD1).2⟩ *
        ⟨t, ht1⟩⁻¹ : ↥N) = ⟨b, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbD1).2⟩ :=
      Subtype.ext (by
        change t * b * t⁻¹ = b
        rw [htb]
        group)
    calc ρ ⟨t, ht1⟩ * ρ ⟨b, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbD1).2⟩ *
          (ρ ⟨t, ht1⟩)⁻¹
        = ρ (⟨t, ht1⟩ * ⟨b, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbD1).2⟩ *
            ⟨t, ht1⟩⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = ρ ⟨b, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbD1).2⟩ := by rw [e]
  have hinv : ρ ⟨t, ht1⟩ * ρ ⟨b', Subgroup.le_normalizer (Subgroup.mem_inf.mp hb'D1).2⟩ *
      (ρ ⟨t, ht1⟩)⁻¹ =
        (ρ ⟨b', Subgroup.le_normalizer (Subgroup.mem_inf.mp hb'D1).2⟩)⁻¹ := by
    have e : (⟨t, ht1⟩ * ⟨b', Subgroup.le_normalizer (Subgroup.mem_inf.mp hb'D1).2⟩ *
        ⟨t, ht1⟩⁻¹ : ↥N) = (⟨b', Subgroup.le_normalizer (Subgroup.mem_inf.mp hb'D1).2⟩ : ↥N)⁻¹ :=
      Subtype.ext (by
        change t * b' * t⁻¹ = b'⁻¹
        exact ht b' hb'D2)
    calc ρ ⟨t, ht1⟩ * ρ ⟨b', Subgroup.le_normalizer (Subgroup.mem_inf.mp hb'D1).2⟩ *
          (ρ ⟨t, ht1⟩)⁻¹
        = ρ (⟨t, ht1⟩ * ⟨b', Subgroup.le_normalizer (Subgroup.mem_inf.mp hb'D1).2⟩ *
            ⟨t, ht1⟩⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = ρ ((⟨b', Subgroup.le_normalizer (Subgroup.mem_inf.mp hb'D1).2⟩ : ↥N)⁻¹) := by rw [e]
      _ = (ρ ⟨b', Subgroup.le_normalizer (Subgroup.mem_inf.mp hb'D1).2⟩)⁻¹ := by rw [map_inv]
  exact ⟨ht1, CFSG.RankThree.PartTwo.KFacts.KP2.not_mem_alternatingGroup_of_fix_inv
    hP9 he₁P he₂P he₁1 he₂1 hfix hinv⟩

private theorem disjoint_zpowers_of_card_three {x y : G}
    (hx : Nat.card (Subgroup.zpowers x) = 3)
    (hy : Nat.card (Subgroup.zpowers y) = 3)
    (hyx : y ∉ Subgroup.zpowers x) :
    Disjoint (Subgroup.zpowers x) (Subgroup.zpowers y) := by
  have hdvd : Nat.card ↥(Subgroup.zpowers x ⊓ Subgroup.zpowers y) ∣ 3 := by
    have h := Subgroup.card_dvd_of_le
      (show Subgroup.zpowers x ⊓ Subgroup.zpowers y ≤ Subgroup.zpowers x from inf_le_left)
    simpa [hx] using h
  have hne3 : Nat.card ↥(Subgroup.zpowers x ⊓ Subgroup.zpowers y) ≠ 3 := by
    intro h3
    have heq : Subgroup.zpowers x ⊓ Subgroup.zpowers y = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hx])
    have hle : Subgroup.zpowers x ≤ Subgroup.zpowers y := by
      rw [← heq]
      exact inf_le_right
    have heq2 : Subgroup.zpowers x = Subgroup.zpowers y :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hx, hy])
    have hy_mem : y ∈ Subgroup.zpowers x := by
      rw [heq2]
      exact Subgroup.mem_zpowers y
    exact hyx hy_mem
  have h1 : Nat.card ↥(Subgroup.zpowers x ⊓ Subgroup.zpowers y) = 1 := by
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hdvd with h1 | h3
    · exact h1
    · exact absurd h3 hne3
  exact disjoint_iff.mpr (Subgroup.card_eq_one.mp h1)

private theorem card_sup_zpowers_eq_nine {x y : G}
    (hx : Nat.card (Subgroup.zpowers x) = 3)
    (hy : Nat.card (Subgroup.zpowers y) = 3)
    (hdisj : Disjoint (Subgroup.zpowers x) (Subgroup.zpowers y))
    (hcomm : Commute x y) :
    Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) = 9 := by
  have hycen : y ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm.eq.symm
  have hnorm : Subgroup.zpowers y ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) :=
    (Subgroup.zpowers_le.mpr hycen).trans
      (CFSG.GorensteinWalter.centralizer_singleton_le_normalizer_zpowers x)
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (Subgroup.zpowers x) (Subgroup.zpowers y) hnorm hdisj, hx, hy]

private theorem mem_normalizer_of_maps_generators {H : Subgroup G} {r x y : G}
    (hH : H = Subgroup.zpowers x ⊔ Subgroup.zpowers y)
    (hxr : r * x * r⁻¹ ∈ H) (hyr : r * y * r⁻¹ ∈ H) :
    r ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : H.map (MulAut.conj r).toMonoidHom ≤ H := by
    rw [hH, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rw [hH] at hxr hyr
    exact sup_le (Subgroup.zpowers_le.mpr (by simpa [MulAut.conj_apply] using hxr))
      (Subgroup.zpowers_le.mpr (by simpa [MulAut.conj_apply] using hyr))
  have hcard : Nat.card ↥(H.map (MulAut.conj r).toMonoidHom) = Nat.card ↥H :=
    Subgroup.card_map_of_injective (MulAut.conj r).injective
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)


theorem exists_y₁ (h : Conf683 A c L Y₁ Y₂ S b Lb) {b' : G}
    (hb' : A ⊓ Y₁ ⊓ Y₂ = Subgroup.zpowers b') :
    ∃ y ∈ Y₁ ⊔ S, y ∈ Subgroup.normalizer (A : Set G) ∧
      y * b * y⁻¹ ∈ Subgroup.zpowers b' ∧
      y * b' * y⁻¹ ∈ Subgroup.zpowers b ∧
      ∀ e ∈ A ⊓ Y₁, y ^ 2 * e * (y ^ 2)⁻¹ = e⁻¹ := by
  classical
  obtain ⟨b₀, hb₀A, hb₀ne, hb₀D, -, -⟩ := exists_b' h
  have hb₀Dmem : b₀ ∈ A ⊓ Y₁ ⊓ Y₂ := by
    rw [hb₀D]
    exact Subgroup.mem_zpowers b₀
  have hb₀D1 : b₀ ∈ A ⊓ Y₁ := (Subgroup.mem_inf.mp hb₀Dmem).1
  have hb₀D2 : b₀ ∈ A ⊓ Y₂ :=
    ⟨(Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hb₀Dmem).1).1,
      (Subgroup.mem_inf.mp hb₀Dmem).2⟩
  have hb₀Y₂ : b₀ ∈ Y₂ := (Subgroup.mem_inf.mp hb₀D2).2
  have hbb' : Subgroup.zpowers b₀ = Subgroup.zpowers b' := by
    rw [← hb₀D, hb']
  have hA := isElemAbelian_A h
  have hbD1 : b ∈ A ⊓ Y₁ := ⟨b_mem h, b_mem_y₁ h⟩
  have hb_not_Y₂ : b ∉ Y₂ := (card_inf₂ h).2.1
  have hb₀notzpb : b₀ ∉ Subgroup.zpowers b :=
    not_mem_zpowers_of_mem_of_not_mem hA (b_mem h) hb_not_Y₂ hb₀A hb₀Y₂ hb₀ne
  obtain ⟨t, -, htA, htS, -, htb, htinv⟩ := exists_t₂ h
  have htAS : t ∈ Subgroup.normalizer ((A ⊔ S : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_sup A S ⟨htA, htS⟩
  have htY₁ : t ∈ Subgroup.normalizer (Y₁ : Set G) := normalizer_sup_le₁ h htAS
  let N := Subgroup.normalizer (Y₁ : Set G)
  let ρ := CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep Y₁ (Classical.choice h.a7₁)
  let P : Subgroup (Equiv.Perm (Fin 7)) := ((A ⊓ Y₁).subgroupOf N).map ρ
  let e₁ : Equiv.Perm (Fin 7) := ρ ⟨b, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbD1).2⟩
  let e₂ : Equiv.Perm (Fin 7) := ρ ⟨b₀, Subgroup.le_normalizer (Subgroup.mem_inf.mp hb₀D1).2⟩
  have hP9 : Nat.card P = 9 := by
    simpa [P, N, ρ] using card_map_a7Rep_inf (A := A) (K := Y₁) hA
      (Classical.choice h.a7₁) (card_inf₁ h).1
  have he₁P : e₁ ∈ P := by
    simpa [e₁, P, N, ρ] using Subgroup.mem_map.mpr
      ⟨⟨b, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbD1).2⟩,
        Subgroup.mem_subgroupOf.mpr hbD1, rfl⟩
  have he₂P : e₂ ∈ P := by
    simpa [e₂, P, N, ρ] using Subgroup.mem_map.mpr
      ⟨⟨b₀, Subgroup.le_normalizer (Subgroup.mem_inf.mp hb₀D1).2⟩,
        Subgroup.mem_subgroupOf.mpr hb₀D1, rfl⟩
  have hb_ord : orderOf b = 3 := by
    rw [← Nat.card_zpowers]
    exact (zpowers_mem_omegaA_iff.mp h.omega_b).2.1
  have hb₀_ord : orderOf b₀ = 3 := by
    have hdvd : orderOf b₀ ∣ 3 := orderOf_dvd_of_pow_eq_one (hA.2 b₀ hb₀A)
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hb₀ne
    · exact h3
  have he₁card : Nat.card (Subgroup.zpowers e₁) = 3 := by
    rw [Nat.card_zpowers]
    have hdvd : orderOf e₁ ∣ 3 := by
      rw [← hb_ord]
      simpa [e₁] using orderOf_map_dvd ρ ⟨b, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbD1).2⟩
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hdvd with h1 | h3
    · exfalso
      have he1 : e₁ = 1 := orderOf_eq_one_iff.mp h1
      have hbO : b ∈ CFSG.Open.pCoreOf 2 Y₁ := by
        refine (a7Rep_eq_one_iff_mem_pCoreOf (Classical.choice h.a7₁)
          (Subgroup.mem_inf.mp hbD1).2).mp ?_
        simpa [e₁] using he1
      have hb1 : b = 1 := eq_one_of_mem_two_group_of_mem_elemAbelian_three
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y₁) hA hbO
        (Subgroup.mem_inf.mp hbD1).1
      exact b_ne_one h hb1
    · exact h3
  have he₂card : Nat.card (Subgroup.zpowers e₂) = 3 := by
    rw [Nat.card_zpowers]
    have hdvd : orderOf e₂ ∣ 3 := by
      rw [← hb₀_ord]
      simpa [e₂] using orderOf_map_dvd ρ ⟨b₀, Subgroup.le_normalizer (Subgroup.mem_inf.mp hb₀D1).2⟩
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hdvd with h1 | h3
    · exfalso
      have he2 : e₂ = 1 := orderOf_eq_one_iff.mp h1
      have hbO : b₀ ∈ CFSG.Open.pCoreOf 2 Y₁ := by
        refine (a7Rep_eq_one_iff_mem_pCoreOf (Classical.choice h.a7₁)
          (Subgroup.mem_inf.mp hb₀D1).2).mp ?_
        simpa [e₂] using he2
      have hb1 : b₀ = 1 := eq_one_of_mem_two_group_of_mem_elemAbelian_three
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y₁) hA hbO
        (Subgroup.mem_inf.mp hb₀D1).1
      exact hb₀ne hb1
    · exact h3
  have he₂1 : e₂ ∉ Subgroup.zpowers e₁ := by
    intro hmem
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hbjD1 : b ^ j ∈ A ⊓ Y₁ :=
      ⟨A.zpow_mem (Subgroup.mem_inf.mp hbD1).1 j,
        Y₁.zpow_mem (Subgroup.mem_inf.mp hbD1).2 j⟩
    have hρbj : ρ ⟨b ^ j, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbjD1).2⟩ = e₁ ^ j := by
      have e : (⟨b ^ j, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbjD1).2⟩ : ↥N) =
          (⟨b, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbD1).2⟩ : ↥N) ^ j :=
        Subtype.ext rfl
      rw [e]
      exact map_zpow ρ _ j
    have hinj := a7Rep_injective_inf (A := A) (K := Y₁) hA (Classical.choice h.a7₁)
    have heq : (⟨b ^ j, hbjD1⟩ : ↥(A ⊓ Y₁)) = ⟨b₀, hb₀D1⟩ := by
      refine hinj ?_
      change ρ ⟨b ^ j, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbjD1).2⟩ =
        ρ ⟨b₀, Subgroup.le_normalizer (Subgroup.mem_inf.mp hb₀D1).2⟩
      rw [hρbj]
      exact hj
    have hmemb : b₀ ∈ Subgroup.zpowers b := by
      have : b₀ = b ^ j := (congrArg Subtype.val heq).symm
      rw [this]
      exact (Subgroup.zpowers b).zpow_mem (Subgroup.mem_zpowers b) j
    exact hb₀notzpb hmemb
  have hfix : ρ ⟨t, htY₁⟩ * e₁ * (ρ ⟨t, htY₁⟩)⁻¹ = e₁ := by
    have e : (⟨t, htY₁⟩ * ⟨b, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbD1).2⟩ *
        ⟨t, htY₁⟩⁻¹ : ↥N) = ⟨b, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbD1).2⟩ :=
      Subtype.ext (by
        change t * b * t⁻¹ = b
        rw [htb]
        group)
    calc ρ ⟨t, htY₁⟩ * e₁ * (ρ ⟨t, htY₁⟩)⁻¹
        = ρ (⟨t, htY₁⟩ * ⟨b, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbD1).2⟩ *
            ⟨t, htY₁⟩⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = e₁ := by rw [e]
  have hinv : ρ ⟨t, htY₁⟩ * e₂ * (ρ ⟨t, htY₁⟩)⁻¹ = e₂⁻¹ := by
    have e : (⟨t, htY₁⟩ * ⟨b₀, Subgroup.le_normalizer (Subgroup.mem_inf.mp hb₀D1).2⟩ *
        ⟨t, htY₁⟩⁻¹ : ↥N) =
        (⟨b₀, Subgroup.le_normalizer (Subgroup.mem_inf.mp hb₀D1).2⟩ : ↥N)⁻¹ :=
      Subtype.ext (by
        change t * b₀ * t⁻¹ = b₀⁻¹
        exact htinv b₀ hb₀D2)
    calc ρ ⟨t, htY₁⟩ * e₂ * (ρ ⟨t, htY₁⟩)⁻¹
        = ρ (⟨t, htY₁⟩ * ⟨b₀, Subgroup.le_normalizer (Subgroup.mem_inf.mp hb₀D1).2⟩ *
            ⟨t, htY₁⟩⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = ρ ((⟨b₀, Subgroup.le_normalizer (Subgroup.mem_inf.mp hb₀D1).2⟩ : ↥N)⁻¹) := by rw [e]
      _ = e₂⁻¹ := by rw [map_inv]
  have he₁ne : e₁ ≠ 1 := by
    intro h1
    rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at he₁card
    norm_num at he₁card
  obtain ⟨r, hrA, hline₁, hline₂, hsq⟩ :=
    CFSG.RankThree.PartTwo.KFacts.KP2.exists_swap_of_fix_inv hP9 he₁P he₂P
      he₁ne he₂1 hfix hinv
  have hbA : b ∈ A := (Subgroup.mem_inf.mp hbD1).1
  have hcomm_bb₀ : Commute (⟨b, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbD1).2⟩ : ↥N)
      ⟨b₀, Subgroup.le_normalizer (Subgroup.mem_inf.mp hb₀D1).2⟩ := by
    apply Subtype.ext
    simpa using congrArg Subtype.val (hA.1.is_comm.comm ⟨b, hbA⟩ ⟨b₀, hb₀A⟩)
  have hcomm_e : Commute e₁ e₂ := by
    simpa [e₁, e₂] using hcomm_bb₀.map ρ
  have hdisj_e : Disjoint (Subgroup.zpowers e₁) (Subgroup.zpowers e₂) :=
    disjoint_zpowers_of_card_three he₁card he₂card he₂1
  have hsup_e : Nat.card ↥(Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂) = 9 :=
    card_sup_zpowers_eq_nine he₁card he₂card hdisj_e hcomm_e
  have hP_eq : P = Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂ :=
    (Subgroup.eq_of_le_of_card_ge
      (sup_le (Subgroup.zpowers_le.mpr he₁P) (Subgroup.zpowers_le.mpr he₂P))
      (by rw [hsup_e, hP9])).symm
  have hσP : r ∈ Subgroup.normalizer (P : Set (Equiv.Perm (Fin 7))) :=
    mem_normalizer_of_maps_generators hP_eq
      (Subgroup.zpowers_le.mpr he₂P hline₁) (Subgroup.zpowers_le.mpr he₁P hline₂)
  obtain ⟨y, hyKS, hyK, hyA, hyc, hyρ, -⟩ :=
    exists_lift_of_a7 (A := A) (K := Y₁) (S := S) (k := c) hA (c_mem h)
      (le_normalizer₁ h) (h.maxCE.1.s₁.prop.1.1.1.2.2) (isPGroup_S₁ h)
      h.maxCE.1.s₁.prop.1.2 (pCoreOf_sup_le₁ h)
      (fun x hx => commutator_c_mem h hx) (card_inf₁ h).2.2
      (Classical.choice h.a7₁) hrA (by simpa [P, N, ρ] using hσP)
  have hy_b₀ : y * b₀ * y⁻¹ ∈ Subgroup.zpowers b := by
    have hmemY : y * b₀ * y⁻¹ ∈ A ⊓ Y₁ :=
      ⟨(Subgroup.mem_normalizer_iff.mp hyA b₀).mp hb₀A,
        (Subgroup.mem_normalizer_iff.mp hyK b₀).mp (Subgroup.mem_inf.mp hb₀D1).2⟩
    have hρeq : ρ ⟨y * b₀ * y⁻¹, Subgroup.le_normalizer hmemY.2⟩ = r * e₂ * r⁻¹ := by
      have e : (⟨y * b₀ * y⁻¹, Subgroup.le_normalizer hmemY.2⟩ : ↥N) =
          ⟨y, hyK⟩ * ⟨b₀, Subgroup.le_normalizer (Subgroup.mem_inf.mp hb₀D1).2⟩ *
            ⟨y, hyK⟩⁻¹ := Subtype.ext (by simp)
      rw [e, map_mul, map_mul, map_inv, hyρ]
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hline₂
    have hbjD1 : b ^ j ∈ A ⊓ Y₁ :=
      ⟨A.zpow_mem hbA j, Y₁.zpow_mem (Subgroup.mem_inf.mp hbD1).2 j⟩
    have hρbj : ρ ⟨b ^ j, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbjD1).2⟩ = e₁ ^ j := by
      have e : (⟨b ^ j, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbjD1).2⟩ : ↥N) =
          (⟨b, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbD1).2⟩ : ↥N) ^ j :=
        Subtype.ext rfl
      rw [e]
      exact map_zpow ρ _ j
    have hinj := a7Rep_injective_inf (A := A) (K := Y₁) hA (Classical.choice h.a7₁)
    have heq : (⟨y * b₀ * y⁻¹, hmemY⟩ : ↥(A ⊓ Y₁)) = ⟨b ^ j, hbjD1⟩ := by
      refine hinj ?_
      change ρ ⟨y * b₀ * y⁻¹, Subgroup.le_normalizer hmemY.2⟩ =
        ρ ⟨b ^ j, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbjD1).2⟩
      rw [hρeq, hρbj]
      exact hj.symm
    have : y * b₀ * y⁻¹ = b ^ j := congrArg Subtype.val heq
    rw [this]
    exact (Subgroup.zpowers b).zpow_mem (Subgroup.mem_zpowers b) j
  have hy_b : y * b * y⁻¹ ∈ Subgroup.zpowers b₀ := by
    have hmemY : y * b * y⁻¹ ∈ A ⊓ Y₁ :=
      ⟨(Subgroup.mem_normalizer_iff.mp hyA b).mp hbA,
        (Subgroup.mem_normalizer_iff.mp hyK b).mp (Subgroup.mem_inf.mp hbD1).2⟩
    have hρeq : ρ ⟨y * b * y⁻¹, Subgroup.le_normalizer hmemY.2⟩ = r * e₁ * r⁻¹ := by
      have e : (⟨y * b * y⁻¹, Subgroup.le_normalizer hmemY.2⟩ : ↥N) =
          ⟨y, hyK⟩ * ⟨b, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbD1).2⟩ *
            ⟨y, hyK⟩⁻¹ := Subtype.ext (by simp)
      rw [e, map_mul, map_mul, map_inv, hyρ]
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hline₁
    have hb₀jD1 : b₀ ^ j ∈ A ⊓ Y₁ :=
      ⟨A.zpow_mem hb₀A j, Y₁.zpow_mem (Subgroup.mem_inf.mp hb₀D1).2 j⟩
    have hρb₀j : ρ ⟨b₀ ^ j, Subgroup.le_normalizer (Subgroup.mem_inf.mp hb₀jD1).2⟩ = e₂ ^ j := by
      have e : (⟨b₀ ^ j, Subgroup.le_normalizer (Subgroup.mem_inf.mp hb₀jD1).2⟩ : ↥N) =
          (⟨b₀, Subgroup.le_normalizer (Subgroup.mem_inf.mp hb₀D1).2⟩ : ↥N) ^ j :=
        Subtype.ext rfl
      rw [e]
      exact map_zpow ρ _ j
    have hinj := a7Rep_injective_inf (A := A) (K := Y₁) hA (Classical.choice h.a7₁)
    have heq : (⟨y * b * y⁻¹, hmemY⟩ : ↥(A ⊓ Y₁)) = ⟨b₀ ^ j, hb₀jD1⟩ := by
      refine hinj ?_
      change ρ ⟨y * b * y⁻¹, Subgroup.le_normalizer hmemY.2⟩ =
        ρ ⟨b₀ ^ j, Subgroup.le_normalizer (Subgroup.mem_inf.mp hb₀jD1).2⟩
      rw [hρeq, hρb₀j]
      exact hj.symm
    have : y * b * y⁻¹ = b₀ ^ j := congrArg Subtype.val heq
    rw [this]
    exact (Subgroup.zpowers b₀).zpow_mem (Subgroup.mem_zpowers b₀) j
  have hy_b' : y * b' * y⁻¹ ∈ Subgroup.zpowers b := by
    have hb'zpb₀ : b' ∈ Subgroup.zpowers b₀ := by
      rw [hbb']
      exact Subgroup.mem_zpowers b'
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hb'zpb₀
    rw [← hm]
    have e : y * b₀ ^ m * y⁻¹ = (y * b₀ * y⁻¹) ^ m := by
      simpa [MulAut.conj_apply] using (map_zpow (MulAut.conj y) b₀ m)
    rw [e]
    exact (Subgroup.zpowers b).zpow_mem hy_b₀ m
  have hρy2 : ρ ⟨y ^ 2, N.pow_mem hyK 2⟩ = r ^ 2 := by
    have e : (⟨y ^ 2, N.pow_mem hyK 2⟩ : ↥N) = (⟨y, hyK⟩ : ↥N) ^ 2 := Subtype.ext rfl
    rw [e, map_pow, hyρ]
  have hy2inv : ∀ e ∈ A ⊓ Y₁, y ^ 2 * e * (y ^ 2)⁻¹ = e⁻¹ :=
    a7Rep_inverts_inf hA (Classical.choice h.a7₁) (N.pow_mem hyK 2)
      ((Subgroup.normalizer (A : Set G)).pow_mem hyA 2) hρy2 hsq
  refine ⟨y, hyKS, hyA, ?_, hy_b', hy2inv⟩
  rw [← hbb']
  exact hy_b


theorem exists_y₂ (h : Conf683 A c L Y₁ Y₂ S b Lb) {b' : G}
    (hb' : A ⊓ Y₁ ⊓ Y₂ = Subgroup.zpowers b') :
    ∃ y ∈ Y₂ ⊔ S, y ∈ Subgroup.normalizer (A : Set G) ∧
      y * c * y⁻¹ ∈ Subgroup.zpowers b' ∧
      y * b' * y⁻¹ ∈ Subgroup.zpowers c ∧
      ∀ e ∈ A ⊓ Y₂, y ^ 2 * e * (y ^ 2)⁻¹ = e⁻¹ := by
  classical
  obtain ⟨b₀, hb₀A, hb₀ne, hb₀D, -, -⟩ := exists_b' h
  have hb₀Dmem : b₀ ∈ A ⊓ Y₁ ⊓ Y₂ := by
    rw [hb₀D]
    exact Subgroup.mem_zpowers b₀
  have hb₀D1 : b₀ ∈ A ⊓ Y₂ :=
    ⟨(Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hb₀Dmem).1).1,
      (Subgroup.mem_inf.mp hb₀Dmem).2⟩
  have hb₀D2 : b₀ ∈ A ⊓ Y₁ := (Subgroup.mem_inf.mp hb₀Dmem).1
  have hb₀Y₁ : b₀ ∈ Y₁ := (Subgroup.mem_inf.mp hb₀D2).2
  have hbb' : Subgroup.zpowers b₀ = Subgroup.zpowers b' := by
    rw [← hb₀D, hb']
  have hA := isElemAbelian_A h
  have hcD2 : c ∈ A ⊓ Y₂ := ⟨c_mem h, c_mem_y₂ h⟩
  have hb_not_Y₁ : c ∉ Y₁ := (card_inf₁ h).2.1
  have hb₀notzpc : b₀ ∉ Subgroup.zpowers c :=
    not_mem_zpowers_of_mem_of_not_mem hA (c_mem h) hb_not_Y₁ hb₀A hb₀Y₁ hb₀ne
  obtain ⟨t, -, htA, htS, -, htc, htinv⟩ := exists_t₁ h
  have htAS : t ∈ Subgroup.normalizer ((A ⊔ S : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_sup A S ⟨htA, htS⟩
  have htY₂ : t ∈ Subgroup.normalizer (Y₂ : Set G) := normalizer_sup_le₂ h htAS
  let N := Subgroup.normalizer (Y₂ : Set G)
  let ρ := CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep Y₂ (Classical.choice h.a7₂)
  let P : Subgroup (Equiv.Perm (Fin 7)) := ((A ⊓ Y₂).subgroupOf N).map ρ
  let e₁ : Equiv.Perm (Fin 7) := ρ ⟨c, Subgroup.le_normalizer (Subgroup.mem_inf.mp hcD2).2⟩
  let e₂ : Equiv.Perm (Fin 7) := ρ ⟨b₀, Subgroup.le_normalizer (Subgroup.mem_inf.mp hb₀D1).2⟩
  have hP9 : Nat.card P = 9 := by
    simpa [P, N, ρ] using card_map_a7Rep_inf (A := A) (K := Y₂) hA
      (Classical.choice h.a7₂) (card_inf₂ h).1
  have he₁P : e₁ ∈ P := by
    simpa [e₁, P, N, ρ] using Subgroup.mem_map.mpr
      ⟨⟨c, Subgroup.le_normalizer (Subgroup.mem_inf.mp hcD2).2⟩,
        Subgroup.mem_subgroupOf.mpr hcD2, rfl⟩
  have he₂P : e₂ ∈ P := by
    simpa [e₂, P, N, ρ] using Subgroup.mem_map.mpr
      ⟨⟨b₀, Subgroup.le_normalizer (Subgroup.mem_inf.mp hb₀D1).2⟩,
        Subgroup.mem_subgroupOf.mpr hb₀D1, rfl⟩
  have hc_ord : orderOf c = 3 := by
    rw [← Nat.card_zpowers]
    exact (zpowers_mem_omegaA_iff.mp h.sec15R.toSec13Data.zpowers_mem_omegaA).2.1
  have hb₀_ord : orderOf b₀ = 3 := by
    have hdvd : orderOf b₀ ∣ 3 := orderOf_dvd_of_pow_eq_one (hA.2 b₀ hb₀A)
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hb₀ne
    · exact h3
  have he₁card : Nat.card (Subgroup.zpowers e₁) = 3 := by
    rw [Nat.card_zpowers]
    have hdvd : orderOf e₁ ∣ 3 := by
      rw [← hc_ord]
      simpa [e₁] using orderOf_map_dvd ρ ⟨c, Subgroup.le_normalizer (Subgroup.mem_inf.mp hcD2).2⟩
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hdvd with h1 | h3
    · exfalso
      have he1 : e₁ = 1 := orderOf_eq_one_iff.mp h1
      have hbO : c ∈ CFSG.Open.pCoreOf 2 Y₂ := by
        refine (a7Rep_eq_one_iff_mem_pCoreOf (Classical.choice h.a7₂)
          (Subgroup.mem_inf.mp hcD2).2).mp ?_
        simpa [e₁] using he1
      have hb1 : c = 1 := eq_one_of_mem_two_group_of_mem_elemAbelian_three
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y₂) hA hbO
        (Subgroup.mem_inf.mp hcD2).1
      exact c_ne_one h hb1
    · exact h3
  have he₂card : Nat.card (Subgroup.zpowers e₂) = 3 := by
    rw [Nat.card_zpowers]
    have hdvd : orderOf e₂ ∣ 3 := by
      rw [← hb₀_ord]
      simpa [e₂] using orderOf_map_dvd ρ ⟨b₀, Subgroup.le_normalizer (Subgroup.mem_inf.mp hb₀D1).2⟩
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hdvd with h1 | h3
    · exfalso
      have he2 : e₂ = 1 := orderOf_eq_one_iff.mp h1
      have hbO : b₀ ∈ CFSG.Open.pCoreOf 2 Y₂ := by
        refine (a7Rep_eq_one_iff_mem_pCoreOf (Classical.choice h.a7₂)
          (Subgroup.mem_inf.mp hb₀D1).2).mp ?_
        simpa [e₂] using he2
      have hb1 : b₀ = 1 := eq_one_of_mem_two_group_of_mem_elemAbelian_three
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y₂) hA hbO
        (Subgroup.mem_inf.mp hb₀D1).1
      exact hb₀ne hb1
    · exact h3
  have he₂1 : e₂ ∉ Subgroup.zpowers e₁ := by
    intro hmem
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hbjD1 : c ^ j ∈ A ⊓ Y₂ :=
      ⟨A.zpow_mem (Subgroup.mem_inf.mp hcD2).1 j,
        Y₂.zpow_mem (Subgroup.mem_inf.mp hcD2).2 j⟩
    have hρbj : ρ ⟨c ^ j, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbjD1).2⟩ = e₁ ^ j := by
      have e : (⟨c ^ j, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbjD1).2⟩ : ↥N) =
          (⟨c, Subgroup.le_normalizer (Subgroup.mem_inf.mp hcD2).2⟩ : ↥N) ^ j :=
        Subtype.ext rfl
      rw [e]
      exact map_zpow ρ _ j
    have hinj := a7Rep_injective_inf (A := A) (K := Y₂) hA (Classical.choice h.a7₂)
    have heq : (⟨c ^ j, hbjD1⟩ : ↥(A ⊓ Y₂)) = ⟨b₀, hb₀D1⟩ := by
      refine hinj ?_
      change ρ ⟨c ^ j, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbjD1).2⟩ =
        ρ ⟨b₀, Subgroup.le_normalizer (Subgroup.mem_inf.mp hb₀D1).2⟩
      rw [hρbj]
      exact hj
    have hmemb : b₀ ∈ Subgroup.zpowers c := by
      have : b₀ = c ^ j := (congrArg Subtype.val heq).symm
      rw [this]
      exact (Subgroup.zpowers c).zpow_mem (Subgroup.mem_zpowers c) j
    exact hb₀notzpc hmemb
  have hfix : ρ ⟨t, htY₂⟩ * e₁ * (ρ ⟨t, htY₂⟩)⁻¹ = e₁ := by
    have e : (⟨t, htY₂⟩ * ⟨c, Subgroup.le_normalizer (Subgroup.mem_inf.mp hcD2).2⟩ *
        ⟨t, htY₂⟩⁻¹ : ↥N) = ⟨c, Subgroup.le_normalizer (Subgroup.mem_inf.mp hcD2).2⟩ :=
      Subtype.ext (by
        change t * c * t⁻¹ = c
        rw [htc]
        group)
    calc ρ ⟨t, htY₂⟩ * e₁ * (ρ ⟨t, htY₂⟩)⁻¹
        = ρ (⟨t, htY₂⟩ * ⟨c, Subgroup.le_normalizer (Subgroup.mem_inf.mp hcD2).2⟩ *
            ⟨t, htY₂⟩⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = e₁ := by rw [e]
  have hinv : ρ ⟨t, htY₂⟩ * e₂ * (ρ ⟨t, htY₂⟩)⁻¹ = e₂⁻¹ := by
    have e : (⟨t, htY₂⟩ * ⟨b₀, Subgroup.le_normalizer (Subgroup.mem_inf.mp hb₀D1).2⟩ *
        ⟨t, htY₂⟩⁻¹ : ↥N) =
        (⟨b₀, Subgroup.le_normalizer (Subgroup.mem_inf.mp hb₀D1).2⟩ : ↥N)⁻¹ :=
      Subtype.ext (by
        change t * b₀ * t⁻¹ = b₀⁻¹
        exact htinv b₀ hb₀D2)
    calc ρ ⟨t, htY₂⟩ * e₂ * (ρ ⟨t, htY₂⟩)⁻¹
        = ρ (⟨t, htY₂⟩ * ⟨b₀, Subgroup.le_normalizer (Subgroup.mem_inf.mp hb₀D1).2⟩ *
            ⟨t, htY₂⟩⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = ρ ((⟨b₀, Subgroup.le_normalizer (Subgroup.mem_inf.mp hb₀D1).2⟩ : ↥N)⁻¹) := by rw [e]
      _ = e₂⁻¹ := by rw [map_inv]
  have he₁ne : e₁ ≠ 1 := by
    intro h1
    rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at he₁card
    norm_num at he₁card
  obtain ⟨r, hrA, hline₁, hline₂, hsq⟩ :=
    CFSG.RankThree.PartTwo.KFacts.KP2.exists_swap_of_fix_inv hP9 he₁P he₂P
      he₁ne he₂1 hfix hinv
  have hcA : c ∈ A := (Subgroup.mem_inf.mp hcD2).1
  have hcomm_bb₀ : Commute (⟨c, Subgroup.le_normalizer (Subgroup.mem_inf.mp hcD2).2⟩ : ↥N)
      ⟨b₀, Subgroup.le_normalizer (Subgroup.mem_inf.mp hb₀D1).2⟩ := by
    apply Subtype.ext
    simpa using congrArg Subtype.val (hA.1.is_comm.comm ⟨c, hcA⟩ ⟨b₀, hb₀A⟩)
  have hcomm_e : Commute e₁ e₂ := by
    simpa [e₁, e₂] using hcomm_bb₀.map ρ
  have hdisj_e : Disjoint (Subgroup.zpowers e₁) (Subgroup.zpowers e₂) :=
    disjoint_zpowers_of_card_three he₁card he₂card he₂1
  have hsup_e : Nat.card ↥(Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂) = 9 :=
    card_sup_zpowers_eq_nine he₁card he₂card hdisj_e hcomm_e
  have hP_eq : P = Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂ :=
    (Subgroup.eq_of_le_of_card_ge
      (sup_le (Subgroup.zpowers_le.mpr he₁P) (Subgroup.zpowers_le.mpr he₂P))
      (by rw [hsup_e, hP9])).symm
  have hσP : r ∈ Subgroup.normalizer (P : Set (Equiv.Perm (Fin 7))) :=
    mem_normalizer_of_maps_generators hP_eq
      (Subgroup.zpowers_le.mpr he₂P hline₁) (Subgroup.zpowers_le.mpr he₁P hline₂)
  obtain ⟨y, hyKS, hyK, hyA, hyc, hyρ, -⟩ :=
    exists_lift_of_a7 (A := A) (K := Y₂) (S := S) (k := b) hA (b_mem h)
      (le_normalizer₂ h) (h.maxCE.1.s₂.prop.1.1.1.2.2) (isPGroup_S₁ h)
      h.maxCE.1.s₂.prop.1.2 (R_le h)
      (fun x hx => commutator_b_mem h hx) (card_inf₂ h).2.2
      (Classical.choice h.a7₂) hrA (by simpa [P, N, ρ] using hσP)
  have hy_b₀ : y * b₀ * y⁻¹ ∈ Subgroup.zpowers c := by
    have hmemY : y * b₀ * y⁻¹ ∈ A ⊓ Y₂ :=
      ⟨(Subgroup.mem_normalizer_iff.mp hyA b₀).mp hb₀A,
        (Subgroup.mem_normalizer_iff.mp hyK b₀).mp (Subgroup.mem_inf.mp hb₀D1).2⟩
    have hρeq : ρ ⟨y * b₀ * y⁻¹, Subgroup.le_normalizer hmemY.2⟩ = r * e₂ * r⁻¹ := by
      have e : (⟨y * b₀ * y⁻¹, Subgroup.le_normalizer hmemY.2⟩ : ↥N) =
          ⟨y, hyK⟩ * ⟨b₀, Subgroup.le_normalizer (Subgroup.mem_inf.mp hb₀D1).2⟩ *
            ⟨y, hyK⟩⁻¹ := Subtype.ext (by simp)
      rw [e, map_mul, map_mul, map_inv, hyρ]
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hline₂
    have hbjD1 : c ^ j ∈ A ⊓ Y₂ :=
      ⟨A.zpow_mem hcA j, Y₂.zpow_mem (Subgroup.mem_inf.mp hcD2).2 j⟩
    have hρbj : ρ ⟨c ^ j, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbjD1).2⟩ = e₁ ^ j := by
      have e : (⟨c ^ j, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbjD1).2⟩ : ↥N) =
          (⟨c, Subgroup.le_normalizer (Subgroup.mem_inf.mp hcD2).2⟩ : ↥N) ^ j :=
        Subtype.ext rfl
      rw [e]
      exact map_zpow ρ _ j
    have hinj := a7Rep_injective_inf (A := A) (K := Y₂) hA (Classical.choice h.a7₂)
    have heq : (⟨y * b₀ * y⁻¹, hmemY⟩ : ↥(A ⊓ Y₂)) = ⟨c ^ j, hbjD1⟩ := by
      refine hinj ?_
      change ρ ⟨y * b₀ * y⁻¹, Subgroup.le_normalizer hmemY.2⟩ =
        ρ ⟨c ^ j, Subgroup.le_normalizer (Subgroup.mem_inf.mp hbjD1).2⟩
      rw [hρeq, hρbj]
      exact hj.symm
    have : y * b₀ * y⁻¹ = c ^ j := congrArg Subtype.val heq
    rw [this]
    exact (Subgroup.zpowers c).zpow_mem (Subgroup.mem_zpowers c) j
  have hy_b : y * c * y⁻¹ ∈ Subgroup.zpowers b₀ := by
    have hmemY : y * c * y⁻¹ ∈ A ⊓ Y₂ :=
      ⟨(Subgroup.mem_normalizer_iff.mp hyA c).mp hcA,
        (Subgroup.mem_normalizer_iff.mp hyK c).mp (Subgroup.mem_inf.mp hcD2).2⟩
    have hρeq : ρ ⟨y * c * y⁻¹, Subgroup.le_normalizer hmemY.2⟩ = r * e₁ * r⁻¹ := by
      have e : (⟨y * c * y⁻¹, Subgroup.le_normalizer hmemY.2⟩ : ↥N) =
          ⟨y, hyK⟩ * ⟨c, Subgroup.le_normalizer (Subgroup.mem_inf.mp hcD2).2⟩ *
            ⟨y, hyK⟩⁻¹ := Subtype.ext (by simp)
      rw [e, map_mul, map_mul, map_inv, hyρ]
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hline₁
    have hb₀jD1 : b₀ ^ j ∈ A ⊓ Y₂ :=
      ⟨A.zpow_mem hb₀A j, Y₂.zpow_mem (Subgroup.mem_inf.mp hb₀D1).2 j⟩
    have hρb₀j : ρ ⟨b₀ ^ j, Subgroup.le_normalizer (Subgroup.mem_inf.mp hb₀jD1).2⟩ = e₂ ^ j := by
      have e : (⟨b₀ ^ j, Subgroup.le_normalizer (Subgroup.mem_inf.mp hb₀jD1).2⟩ : ↥N) =
          (⟨b₀, Subgroup.le_normalizer (Subgroup.mem_inf.mp hb₀D1).2⟩ : ↥N) ^ j :=
        Subtype.ext rfl
      rw [e]
      exact map_zpow ρ _ j
    have hinj := a7Rep_injective_inf (A := A) (K := Y₂) hA (Classical.choice h.a7₂)
    have heq : (⟨y * c * y⁻¹, hmemY⟩ : ↥(A ⊓ Y₂)) = ⟨b₀ ^ j, hb₀jD1⟩ := by
      refine hinj ?_
      change ρ ⟨y * c * y⁻¹, Subgroup.le_normalizer hmemY.2⟩ =
        ρ ⟨b₀ ^ j, Subgroup.le_normalizer (Subgroup.mem_inf.mp hb₀jD1).2⟩
      rw [hρeq, hρb₀j]
      exact hj.symm
    have : y * c * y⁻¹ = b₀ ^ j := congrArg Subtype.val heq
    rw [this]
    exact (Subgroup.zpowers b₀).zpow_mem (Subgroup.mem_zpowers b₀) j
  have hy_b' : y * b' * y⁻¹ ∈ Subgroup.zpowers c := by
    have hb'zpb₀ : b' ∈ Subgroup.zpowers b₀ := by
      rw [hbb']
      exact Subgroup.mem_zpowers b'
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hb'zpb₀
    rw [← hm]
    have e : y * b₀ ^ m * y⁻¹ = (y * b₀ * y⁻¹) ^ m := by
      simpa [MulAut.conj_apply] using (map_zpow (MulAut.conj y) b₀ m)
    rw [e]
    exact (Subgroup.zpowers c).zpow_mem hy_b₀ m
  have hρy2 : ρ ⟨y ^ 2, N.pow_mem hyK 2⟩ = r ^ 2 := by
    have e : (⟨y ^ 2, N.pow_mem hyK 2⟩ : ↥N) = (⟨y, hyK⟩ : ↥N) ^ 2 := Subtype.ext rfl
    rw [e, map_pow, hyρ]
  have hy2inv : ∀ e ∈ A ⊓ Y₂, y ^ 2 * e * (y ^ 2)⁻¹ = e⁻¹ :=
    a7Rep_inverts_inf hA (Classical.choice h.a7₂) (N.pow_mem hyK 2)
      ((Subgroup.normalizer (A : Set G)).pow_mem hyA 2) hρy2 hsq
  refine ⟨y, hyKS, hyA, ?_, hy_b', hy2inv⟩
  rw [← hbb']
  exact hy_b

end Conf683

end Res162Seven

end CFSG.RankThree.PartTwo.Sec16
