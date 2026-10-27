module

public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofSwap
import CFSG.RankThree.PartTwo.Sec11.Item1117ResProofSwap
import CFSG.RankThree.PartTwo.Sec11.Item1119Proof

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

section Statements


@[expose] def Gap1117SwapSylowW : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Data G A c L a R Y d x s r g →
      Subgroup.zpowers s = Subgroup.zpowers c →
      Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s} →
      g * x * g⁻¹ * x⁻¹ ∈ A → g * x * g⁻¹ * x⁻¹ ∉ Subgroup.closure {c, d} →
      (∀ a' ∈ Subgroup.closure ({g * x * g⁻¹ * x⁻¹, d} : Set G), a' ∉ Subgroup.zpowers d →
        ∀ Y' ∈ thetaComponentsAt 3 a', sec11K L a' ≤ Y' → KFacts.InducesStdKind Y' c .field) →
      ∀ (Ye R' Y'' : Subgroup G), Ye ∈ thetaComponentsAt 3 (g * x * g⁻¹ * x⁻¹) →
        sec11K L (g * x * g⁻¹ * x⁻¹) ≤ Ye →
        Sec11Std G A (g * x * g⁻¹ * x⁻¹) Ye c R' Y'' →
        9 < orderOf x → KFacts.InducesStdKind Y c .field →
        9 < Nat.card (R' ⊓ Ye : Subgroup G) →
          ∀ w ∈ Subgroup.normalizer (Subgroup.zpowers (g * x * g⁻¹ * x⁻¹) : Set G) ⊓
              Subgroup.normalizer (A : Set G),
            (∃ k : ℕ, w ^ 3 ^ k = 1) → w * c * w⁻¹ * c⁻¹ ∈ Subgroup.zpowers d

end Statements

namespace Item1117ResProof

section Group

variable {G : Type} [Group G] [Finite G]

theorem card_le_of_isSylowOf {X S K : Subgroup G} (hXK : X ≤ K) (hX : IsPGroup 3 X)
    (hS : IsSylowOf 3 S K) : Nat.card X ≤ Nat.card S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T, hT⟩ := (hX.comap_subtype (K := K)).exists_le_sylow
  rw [hS.card_eq, ← Sylow.card_eq_multiplicity T]
  calc Nat.card X = Nat.card (X.subgroupOf K) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv).symm
    _ ≤ Nat.card T := Subgroup.card_le_of_le hT

theorem card_le_three_mul_card_inf_centralizer {X : Subgroup G} {c d : G} (hd3 : d ^ 3 = 1)
    (hXd : ∀ w ∈ X, w * d = d * w)
    (hXc : ∀ w ∈ X, w * c * w⁻¹ * c⁻¹ ∈ Subgroup.zpowers d) :
    Nat.card X ≤ 3 * Nat.card (X ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) := by
  have hcomm : ∀ w ∈ X, ∀ u ∈ Subgroup.zpowers d, w * u * w⁻¹ = u := by
    intro w hw u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    rw [← conj_zpow, (hXd w hw), mul_inv_cancel_right]
  let f : X →* Subgroup.zpowers d :=
    { toFun := fun w => ⟨(w : G) * c * (w : G)⁻¹ * c⁻¹, hXc w w.2⟩
      map_one' := by ext; simp
      map_mul' := by
        intro w₁ w₂
        apply Subtype.ext
        have h2 := hcomm w₁ w₁.2 _ (hXc w₂ w₂.2)
        have hcomm' : ∀ u v : G, u ∈ Subgroup.zpowers d → v ∈ Subgroup.zpowers d →
            u * v = v * u := by
          intro u v hu hv
          obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
          obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
          exact (Commute.zpow_zpow_self d i j).eq
        simp only [Subgroup.coe_mul]
        calc (w₁ : G) * w₂ * c * ((w₁ : G) * w₂)⁻¹ * c⁻¹
            = ((w₁ : G) * ((w₂ : G) * c * (w₂ : G)⁻¹ * c⁻¹) * (w₁ : G)⁻¹) *
                ((w₁ : G) * c * (w₁ : G)⁻¹ * c⁻¹) := by group
          _ = ((w₂ : G) * c * (w₂ : G)⁻¹ * c⁻¹) * ((w₁ : G) * c * (w₁ : G)⁻¹ * c⁻¹) := by
              rw [h2]
          _ = ((w₁ : G) * c * (w₁ : G)⁻¹ * c⁻¹) * ((w₂ : G) * c * (w₂ : G)⁻¹ * c⁻¹) :=
              hcomm' _ _ (hXc w₂ w₂.2) (hXc w₁ w₁.2) }
  have hker : Nat.card f.ker =
      Nat.card (X ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) := by
    refine Nat.card_congr ⟨fun w => ⟨w.1, w.1.2, ?_⟩, fun w => ⟨⟨w.1, w.2.1⟩, ?_⟩, ?_, ?_⟩
    · have h1 : f w.1 = 1 := w.2
      have h2 : (w.1 : G) * c * (w.1 : G)⁻¹ * c⁻¹ = 1 := congrArg Subtype.val h1
      show (w.1 : G) ∈ Subgroup.centralizer ({c} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (w.1 : G) * c = ((w.1 : G) * c * (w.1 : G)⁻¹ * c⁻¹) * c * (w.1 : G) := by group
        _ = c * (w.1 : G) := by rw [h2, one_mul]
    · rw [MonoidHom.mem_ker]
      apply Subtype.ext
      change (w : G) * c * (w : G)⁻¹ * c⁻¹ = 1
      rw [Subgroup.mem_centralizer_singleton_iff.mp w.2.2, mul_inv_cancel_right, mul_inv_cancel]
    · intro w; rfl
    · intro w; rfl
  have hrange : Nat.card f.range ≤ 3 := by
    calc Nat.card f.range ≤ Nat.card (Subgroup.zpowers d) := Subgroup.card_le_card_group _
      _ ≤ 3 := by
        rw [Nat.card_zpowers]
        exact orderOf_le_of_pow_eq_one (by norm_num) hd3
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker] at h1
  calc Nat.card X = Nat.card f.ker * Nat.card f.range := h1.symm
    _ ≤ Nat.card f.ker * 3 := Nat.mul_le_mul_left _ hrange
    _ = 3 * Nat.card (X ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) := by
        rw [hker, mul_comm]

end Group

end Item1117ResProof

section Main


open Item1117ResProof in
theorem gap1117SwapSylow_of_W (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (hW : Gap1117SwapSylowW) : Gap1117SwapSylow := by
  intro G _ _ A c L a R Y d x s r g h hsc hrs heA hecd hsym Ye R' Y'' hYe hKYe hstd hx9 hf hbig
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set e := g * x * g⁻¹ * x⁻¹ with he
  set T := sec11P R g ⊓ Subgroup.centralizer ({e} : Set G) with hT
  set CA := Subgroup.centralizer (A : Set G) with hCA
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ y ∈ A, y ^ 3 = 1 := hAe.2
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hdA := Item1117Proof.d_mem_A h
  have hd3 : d ^ 3 = 1 := hexp d hdA
  have hd3o : orderOf d = 3 := Item1117Proof.orderOf_d h
  have hR'W : R' ≤ Subgroup.normalizer (A : Set G) :=
    le_normalizer_of_eq_closure (h113 G A e Ye c R' Y'' hstd).1
  have hR'N : R' ≤ Subgroup.normalizer (Subgroup.zpowers e : Set G) := hstd.isSylowOf.le
  have hR'3 : IsPGroup 3 R' := hstd.isSylowOf.isPGroup
  have hR'el : ∀ w ∈ R', ∃ k : ℕ, w ^ 3 ^ k = 1 := fun w hw => by
    obtain ⟨k, hk⟩ := hR'3 ⟨w, hw⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hR'c : ∀ w ∈ R', w * c * w⁻¹ * c⁻¹ ∈ Subgroup.zpowers d := fun w hw =>
    hW G A c L a R Y d x s r g h hsc hrs heA hecd hsym Ye R' Y'' hYe hKYe hstd hx9 hf hbig w
      ⟨hR'N hw, hR'W hw⟩ (hR'el w hw)
  have hR'd : ∀ w ∈ R', w * d = d * w := fun w hw => by
    obtain ⟨k, hk⟩ := hR'el w hw
    exact Sec12.commute_of_conj_mem_zpowers hd3o ((Subgroup.mem_normalizer_iff.mp
      (Item1115Proof.W_le_normalizer_d h117 h (hR'W hw)) d).mp (Subgroup.mem_zpowers d)) hk
  have hR'e : ∀ w ∈ R', w * e = e * w := fun w hw => by
    obtain ⟨k, hk⟩ := hR'el w hw
    have he1 : e ≠ 1 := fun h1 => hecd (h1 ▸ Subgroup.one_mem _)
    exact Sec12.commute_of_conj_mem_zpowers (orderOf_eq_prime (hexp e heA) he1)
      ((Subgroup.mem_normalizer_iff.mp (hR'N hw) e).mp (Subgroup.mem_zpowers e)) hk
  have hcard1 := card_le_three_mul_card_inf_centralizer hd3 hR'd hR'c
  have hA' : A = Subgroup.closure {c, e, d} := by
    rw [h.toSec11Std.closure_eq_of_not_mem h.inf_eq h.closure_eq heA hecd, Set.insert_comm]
  have hR'cA : R' ⊓ Subgroup.centralizer ({c} : Set G) ≤ CA := by
    intro w hw
    rw [hCA, Subgroup.mem_centralizer_iff, hA']
    intro z hz
    refine (Subgroup.closure_induction (p := fun z _ => z * w = w * z) ?_ ?_ ?_ ?_ hz)
    · rintro y (rfl | rfl | rfl)
      · exact (Subgroup.mem_centralizer_singleton_iff.mp hw.2).symm
      · exact (hR'e w hw.1).symm
      · exact (hR'd w hw.1).symm
    · simp
    · intro y z _ _ hy hz
      rw [mul_assoc, hz, ← mul_assoc, hy, mul_assoc]
    · intro y _ hy
      calc y⁻¹ * w = y⁻¹ * (w * y) * y⁻¹ := by group
        _ = y⁻¹ * (y * w) * y⁻¹ := by rw [hy]
        _ = w * y⁻¹ := by group
  have hCAH : CA ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer (A : Set G) := by
    intro z hz
    refine ⟨?_, Subgroup.centralizer_le_normalizer _ hz⟩
    have hzc : z ∈ Subgroup.centralizer ({c} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hz c h.mem_A).symm)
    rw [GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers] at hzc
    exact Subgroup.centralizer_le_normalizer _ hzc
  have hNCA : Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (CA : Set G) := by
    intro n hn
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hz ⊢
    intro y hy
    have hy' : n⁻¹ * y * n⁻¹⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp (inv_mem hn.2) y).mp hy
    rw [inv_inv] at hy'
    have h1 := hz _ hy'
    calc y * (n * z * n⁻¹) = n * ((n⁻¹ * y * n) * z) * n⁻¹ := by group
      _ = n * (z * (n⁻¹ * y * n)) * n⁻¹ := by rw [h1]
      _ = n * z * n⁻¹ * y := by group
  have hS := h.isSylowOf_inf.inf_of_le_normalizer hCAH hNCA
  have hcard2 : Nat.card (R' ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) ≤
      Nat.card ((R ⊓ Subgroup.normalizer (A : Set G)) ⊓ CA : Subgroup G) :=
    card_le_of_isSylowOf hR'cA (hR'3.to_le inf_le_left) hS
  obtain ⟨n, hn⟩ := Item1117StepsProof.exists_mul_pow_mem_inf h45 h117 h hsc hrs heA hecd
  have hCRT : (R ⊓ Subgroup.normalizer (A : Set G)) ⊓ CA ≤ T ⊓ CA := by
    refine le_inf ?_ inf_le_right
    intro z hz
    refine ⟨Item1119Proof.R_le_P R g hz.1.1, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hz.2 e heA).symm
  have hgxc : g * x ^ n ∉ T ⊓ CA := by
    intro hm
    have hxc : x * c = c * x := Subgroup.mem_centralizer_singleton_iff.mp
      (Item1117Proof.R_le_centralizer_c h (Item1116Proof.mem_R h).2.1)
    have h1 := Subgroup.mem_centralizer_iff.mp hm.2 c h.mem_A
    apply h.g_not_mem
    apply Sec10.mem_normalizer_zpowers_of_conj_mem
    have e1 : g * c * g⁻¹ = (g * x ^ n) * c * (g * x ^ n)⁻¹ := by
      have := (Commute.pow_left hxc n).eq
      calc g * c * g⁻¹ = g * (x ^ n * c * (x ^ n)⁻¹) * g⁻¹ := by
            rw [this, mul_inv_cancel_right]
        _ = (g * x ^ n) * c * (g * x ^ n)⁻¹ := by group
    rw [e1, ← h1, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers c
  have hcard3 : 3 * Nat.card (T ⊓ CA : Subgroup G) ≤ Nat.card T :=
    three_mul_card_le_of_lt inf_le_left (h.isPGroup_sec11P.to_le inf_le_left) hn hgxc
  have hcard4 : Nat.card ((R ⊓ Subgroup.normalizer (A : Set G)) ⊓ CA : Subgroup G) ≤
      Nat.card (T ⊓ CA : Subgroup G) := Subgroup.card_le_of_le hCRT
  have hgoal : Nat.card R' ≤ Nat.card T := by omega
  have hTN : T ≤ Subgroup.normalizer (Subgroup.zpowers e : Set G) := by
    refine inf_le_right.trans ?_
    rw [GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers]
    exact Subgroup.centralizer_le_normalizer _
  exact Item1117StepsProof.isSylowOf_of_card_le hTN (h.isPGroup_sec11P.to_le inf_le_left)
    hstd.isSylowOf hgoal

end Main

end CFSG.RankThree.PartTwo.Sec11
