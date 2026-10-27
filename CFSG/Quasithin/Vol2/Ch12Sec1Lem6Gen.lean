module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem6
public import CFSG.Quasithin.Vol2.Ch12Sec1H9Lin
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma116
public import CFSG.Quasithin.Background.G2
public import CFSG.Quasithin.Background.I4Basic
public import CFSG.GroupTheory.BaerSuzuki
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoOfNoComponent

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement Matrix

namespace Sec1216Gen

variable {G : Type} [Group G]

theorem commute_of_sq {y w : G} (hy : Odd (orderOf y)) (h : Commute (y ^ 2) w) :
    Commute y w := by
  obtain ⟨k, hk⟩ := hy
  have e : y = (y ^ 2) ^ (k + 1) := by
    rw [← pow_mul, show 2 * (k + 1) = orderOf y + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [e]
  exact h.pow_left _

theorem mem_centralizer_of_index_two {V B : Subgroup G} (hV : IsElemAbelian 2 V) (hBV : B ≤ V)
    (hidx : B.relIndex V = 2) {y : G} (hy : Odd (orderOf y))
    (hyV : y ∈ Subgroup.normalizer (V : Set G)) (hyB : y ∈ Subgroup.centralizer (B : Set G)) :
    y ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hV.1.1.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hw' : y * w * y⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hyV w).mp hw
  have hyBc : ∀ b ∈ B, y * b * y⁻¹ = b := fun b hb => by
    have h1 := Subgroup.mem_centralizer_iff.mp hyB b hb
    calc y * b * y⁻¹ = b * y * y⁻¹ := by rw [h1]
      _ = b := by group
  have hyBc' : ∀ b ∈ B, y⁻¹ * b * y = b := fun b hb => by
    calc y⁻¹ * b * y = y⁻¹ * (y * b * y⁻¹) * y := by rw [hyBc b hb]
      _ = b := by group
  have hmem : y * w * y⁻¹ * w⁻¹ ∈ B := by
    have h2 : (B.subgroupOf V).index = 2 := hidx
    have h := Subgroup.mul_mem_iff_of_index_two h2 (a := (⟨y * w * y⁻¹, hw'⟩ : ↥V))
      (b := (⟨w, hw⟩ : ↥V)⁻¹)
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at h
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    refine h.mpr ⟨fun h1 => B.inv_mem ?_, fun h1 => ?_⟩
    · have e : w = y⁻¹ * (y * w * y⁻¹) * y := by group
      rw [e, hyBc' _ h1]
      exact h1
    · have hwB : w ∈ B := by simpa using B.inv_mem h1
      rw [hyBc w hwB]
      exact hwB
  set b := y * w * y⁻¹ * w⁻¹ with hb
  have hbV : b ∈ V := hBV hmem
  have hb2 : b * b = 1 := by
    have := hV.2 b hbV
    rwa [pow_two] at this
  have e1 : y * w * y⁻¹ = b * w := by rw [hb]; group
  have e2 : y ^ 2 * w * (y ^ 2)⁻¹ = w := by
    rw [pow_two]
    calc y * y * w * (y * y)⁻¹ = y * (y * w * y⁻¹) * y⁻¹ := by group
      _ = y * (b * w) * y⁻¹ := by rw [e1]
      _ = y * b * y⁻¹ * (y * w * y⁻¹) := by group
      _ = b * (b * w) := by rw [hyBc b hmem, e1]
      _ = w := by rw [← mul_assoc, hb2, one_mul]
  have h3 : Commute (y ^ 2) w := by
    show y ^ 2 * w = w * y ^ 2
    calc y ^ 2 * w = y ^ 2 * w * (y ^ 2)⁻¹ * y ^ 2 := by group
      _ = w * y ^ 2 := by rw [e2]
  exact (commute_of_sq hy h3).eq.symm

theorem le_iSup_hyperplane [Finite G] {A Y : Subgroup G} [CFSG.IsElementaryAbelian 2 A]
    [Nontrivial A] (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hY : ¬ 2 ∣ Nat.card Y) :
    Y ≤ ⨆ (B : Subgroup A) (_ : B.index = 2),
      Y ⊓ Subgroup.centralizer ((B.map A.subtype : Subgroup G) : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : MulDistribMulAction A Y := Subgroup.conjMulDistribMulActionOfLeNormalizer A Y hAY
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := 2) (A := A) (H := Y) hY
  set target : Subgroup G := ⨆ (B : Subgroup A) (_ : B.index = 2),
      Y ⊓ Subgroup.centralizer ((B.map A.subtype : Subgroup G) : Set G) with htarget
  have hle : (⨆ (B : Subgroup A) (_ : B.index = 2), CFSG.fixedPointSubgroup B Y) ≤
      target.comap Y.subtype := by
    refine iSup₂_le fun B hB x hx => ?_
    rw [Subgroup.mem_comap]
    have hcomm : ∀ b : B, ((b : A) : G) * (x : G) * ((b : A) : G)⁻¹ = x := fun b =>
      congrArg Subtype.val (hx b)
    refine Subgroup.mem_iSup_of_mem B (Subgroup.mem_iSup_of_mem hB ?_)
    refine Subgroup.mem_inf.2 ⟨x.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, hyB, rfl⟩
    have h1 := hcomm ⟨y, hyB⟩
    change ((y : A) : G) * (x : G) = (x : G) * ((y : A) : G)
    calc ((y : A) : G) * (x : G) = (((y : A) : G) * x * ((y : A) : G)⁻¹) * ((y : A) : G) := by
          group
      _ = (x : G) * ((y : A) : G) := by rw [h1]
  intro x hx
  have hx' : (⟨x, hx⟩ : Y) ∈ (⊤ : Subgroup Y) := Subgroup.mem_top _
  rw [← hgen] at hx'
  exact hle hx'

theorem isElementaryAbelian_of {A : Subgroup G} (hA : IsElemAbelian 2 A) :
    CFSG.IsElementaryAbelian 2 A := CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hA

theorem oddCoreIn_eq_bot [Finite G]
    (hev : CFSG.Assembly.Quasithin.quasithinEvenCharacteristic G) {T T₁ V : Subgroup G}
    (hT : IsSylowTwoOf T ⊤) (hV : IsElemAbelian 2 V) (hVT : V ≤ T)
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) (hV1 : V ≠ ⊥)
    (hhyp : ∀ B : Subgroup G, B ≤ V → B.relIndex V = 2 →
      Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer (V : Set G))
    {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) (hT₁ : IsSylowTwoOf T₁ (Subgroup.centralizer ({v} : Set G)))
    (hT₁T : T₁ ≤ T) : oddCoreIn (Subgroup.centralizer ({v} : Set G)) = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.centralizer ({v} : Set G) with hHdef
  have hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hV.1.1.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨z, hzV, hz1, hzc⟩ := Sec1215.exists_ne_one_mem_centralizer hT.2.1 hVT hTV hV1
  have hz2 : z ^ 2 = 1 := hV.2 z hzV
  have hzo : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  obtain ⟨M', hM', hCM'⟩ := exists_maxTwoLocal_ge (I4.isTwoLocal_centralizer hzo)
  have hvo : orderOf v = 2 := orderOf_eq_prime (hV.2 v hv) hv1
  have hB : IsPGroup 2 (Subgroup.zpowers v) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hvo, pow_one])
  have hB1 : Subgroup.zpowers v ≠ ⊥ := by
    intro h
    have : v ∈ (⊥ : Subgroup G) := h ▸ Subgroup.mem_zpowers v
    exact hv1 (Subgroup.mem_bot.mp this)
  have hNv : Subgroup.normalizer (Subgroup.zpowers v : Set G) = H :=
    I4.normalizer_zpowers_eq_centralizer hvo
  have hBH : Subgroup.zpowers v ⊔ Subgroup.centralizer (Subgroup.zpowers v : Set G) ≤ H := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · intro g hg
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hg v (Subgroup.mem_zpowers v)).symm
  have hHB : H ≤ Subgroup.normalizer (Subgroup.zpowers v : Set G) := hNv.ge
  have hzT : z ∈ T := hVT hzV
  have h115 := lemma116 hev hB hB1 hBH hHB hT₁ hT hT₁T hzT hzc hz1 hz2 hM' hCM'
  have hYz : oddCoreIn H ⊓ Subgroup.centralizer ({z} : Set G) = ⊥ :=
    h115.oddCoreIn_properties.2.1
  have hVH : V ≤ H := fun a ha => by
    rw [hHdef, Subgroup.mem_centralizer_singleton_iff]
    exact hcomm a ha v hv
  have hVY : V ≤ Subgroup.normalizer (oddCoreIn H : Set G) :=
    hVH.trans (QuasithinUnique.le_normalizer_oddCoreIn H)
  have hYodd : ¬ 2 ∣ Nat.card (oddCoreIn H) := by
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact QuasithinUnique.odd_card_oddCoreIn H
  have : CFSG.IsElementaryAbelian 2 V := isElementaryAbelian_of hV
  have : Nontrivial V := by
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV1
    exact ⟨⟨a, 1, ha⟩⟩
  have hgen := le_iSup_hyperplane hVY hYodd
  have hzero : ∀ B : Subgroup V, B.index = 2 →
      oddCoreIn H ⊓ Subgroup.centralizer ((B.map V.subtype : Subgroup G) : Set G) = ⊥ := by
    intro B hBi
    rw [eq_bot_iff]
    intro y hy
    have hyY := hy.1
    have hBV : B.map V.subtype ≤ V := Subgroup.map_subtype_le B
    have hBidx : (B.map V.subtype).relIndex V = 2 := by
      rw [Subgroup.relIndex, show (B.map V.subtype).subgroupOf V = B from
        Subgroup.comap_map_eq_self_of_injective V.subtype_injective B]
      exact hBi
    have hyN : y ∈ Subgroup.normalizer (V : Set G) := hhyp _ hBV hBidx hy.2
    have hyo : Odd (orderOf y) := by
      have h1 := orderOf_dvd_natCard (⟨y, hyY⟩ : oddCoreIn H)
      rw [Subgroup.orderOf_mk] at h1
      exact (QuasithinUnique.odd_card_oddCoreIn H).of_dvd_nat h1
    have hyV := mem_centralizer_of_index_two hV hBV hBidx hyo hyN hy.2
    have hyz : y ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hyV z hzV).symm
    rw [← hYz]
    exact ⟨hyY, hyz⟩
  rw [eq_bot_iff]
  intro y hy
  have := hgen hy
  have hbot : (⨆ (B : Subgroup V) (_ : B.index = 2),
      oddCoreIn H ⊓ Subgroup.centralizer ((B.map V.subtype : Subgroup G) : Set G)) = ⊥ := by
    refine le_bot_iff.mp (iSup₂_le fun B hB => ?_)
    rw [hzero B hB]
  rwa [hbot] at this

section Coord

open scoped Matrix

variable {n : ℕ}

theorem updateCol_one_mulVec_self (i : Fin n) (x : Fin n → ZMod 2) :
    ((1 : Matrix (Fin n) (Fin n) (ZMod 2)).updateCol i x) *ᵥ Pi.single i 1 = x := by
  funext k
  simp [Matrix.mulVec, dotProduct, Matrix.updateCol_apply, Pi.single_apply]

theorem updateCol_one_mulVec_of_ne {i k : Fin n} (hik : i ≠ k) (x : Fin n → ZMod 2) :
    ((1 : Matrix (Fin n) (Fin n) (ZMod 2)).updateCol i x) *ᵥ Pi.single k 1 = Pi.single k 1 := by
  funext j
  simp [Matrix.mulVec, dotProduct, Matrix.updateCol_apply, Pi.single_apply, Matrix.one_apply,
    hik.symm]

theorem exists_sl_fix_of_coord {x y : Fin n → ZMod 2} {i k : Fin n} (hik : i ≠ k)
    (hx : x i = 1) (hy : y i = 1) :
    ∃ A : Matrix.SpecialLinearGroup (Fin n) (ZMod 2),
      (A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Pi.single k 1 = Pi.single k 1 ∧
        (A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x = y := by
  set Bx : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) :=
    ⟨(1 : Matrix (Fin n) (Fin n) (ZMod 2)).updateCol i x, by rw [Sec121Q.det_updateCol_one, hx]⟩
    with hBx
  set By : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) :=
    ⟨(1 : Matrix (Fin n) (Fin n) (ZMod 2)).updateCol i y, by rw [Sec121Q.det_updateCol_one, hy]⟩
    with hBy
  have hinv : ∀ (B : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) (u w : Fin n → ZMod 2),
      (B : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ u = w →
        ((B⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ w = u := by
    intro B u w h
    rw [← h, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  refine ⟨By * Bx⁻¹, ?_, ?_⟩
  · rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec,
      hinv Bx _ _ (updateCol_one_mulVec_of_ne hik x)]
    exact updateCol_one_mulVec_of_ne hik y
  · rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec,
      hinv Bx _ _ (updateCol_one_mulVec_self i x)]
    exact updateCol_one_mulVec_self i y

theorem exists_sl_fix_single {x y : Fin n → ZMod 2} {k : Fin n} (hx : ∃ i, i ≠ k ∧ x i = 1)
    (hy : ∃ j, j ≠ k ∧ y j = 1) :
    ∃ A : Matrix.SpecialLinearGroup (Fin n) (ZMod 2),
      (A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Pi.single k 1 = Pi.single k 1 ∧
        (A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x = y := by
  obtain ⟨i, hik, hxi⟩ := hx
  obtain ⟨j, hjk, hyj⟩ := hy
  have h01 : ∀ c : ZMod 2, c ≠ 1 → c = 0 := by decide
  by_cases hyi : y i = 1
  · exact exists_sl_fix_of_coord hik hxi hyi
  · have hij : i ≠ j := fun h => hyi (h ▸ hyj)
    set z : Fin n → ZMod 2 := Pi.single i 1 + Pi.single j 1 with hz
    have hzi : z i = 1 := by simp [z, hij]
    have hzj : z j = 1 := by simp [z, hij.symm]
    obtain ⟨A₁, hA₁k, hA₁⟩ := exists_sl_fix_of_coord hik hxi hzi
    obtain ⟨A₂, hA₂k, hA₂⟩ := exists_sl_fix_of_coord hjk hzj hyj
    refine ⟨A₂ * A₁, ?_, ?_⟩
    · rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hA₁k, hA₂k]
    · rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hA₁, hA₂]

theorem exists_coord_ne {x : Fin n → ZMod 2} {k : Fin n} (hx0 : x ≠ 0)
    (hxk : x ≠ Pi.single k 1) : ∃ i, i ≠ k ∧ x i = 1 := by
  by_contra h
  push Not at h
  have h01 : ∀ c : ZMod 2, c ≠ 1 → c = 0 := by decide
  have hx : ∀ i, i ≠ k → x i = 0 := fun i hi => h01 _ (h i hi)
  have h2 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases h2 (x k) with hk | hk
  · apply hx0
    funext i
    by_cases hi : i = k
    · rw [hi, hk]; rfl
    · rw [hx i hi]; rfl
  · apply hxk
    funext i
    by_cases hi : i = k
    · rw [hi, hk]; simp
    · rw [hx i hi]; simp [hi]

theorem exists_sl_fix {x₀ x y : Fin n → ZMod 2} (h0 : x₀ ≠ 0) (hx0 : x ≠ 0) (hx : x ≠ x₀)
    (hy0 : y ≠ 0) (hy : y ≠ x₀) :
    ∃ A : Matrix.SpecialLinearGroup (Fin n) (ZMod 2),
      (A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x₀ = x₀ ∧
        (A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x = y := by
  obtain ⟨k, -⟩ := Function.ne_iff.mp h0
  have hk0 : (Pi.single k 1 : Fin n → ZMod 2) ≠ 0 := by
    intro h
    have := congrFun h k
    simp at this
  obtain ⟨P, hP⟩ := Sec121Q.exists_sl_mulVec_eq hk0 h0
  have hPi : ∀ u w : Fin n → ZMod 2, (P : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ u = w →
      ((P⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ w =
        u := by
    intro u w h
    rw [← h, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  have hPP : ∀ u, (P : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
      (((P⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ u) = u := by
    intro u
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  set x' := ((P⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
    Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x with hx'
  set y' := ((P⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
    Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ y with hy'
  have hx'0 : x' ≠ 0 := fun h => hx0 (by rw [← hPP x, ← hx', h, Matrix.mulVec_zero])
  have hx'k : x' ≠ Pi.single k 1 := fun h => hx (by rw [← hPP x, ← hx', h, hP])
  have hy'0 : y' ≠ 0 := fun h => hy0 (by rw [← hPP y, ← hy', h, Matrix.mulVec_zero])
  have hy'k : y' ≠ Pi.single k 1 := fun h => hy (by rw [← hPP y, ← hy', h, hP])
  obtain ⟨A₀, hA₀k, hA₀⟩ := exists_sl_fix_single (exists_coord_ne hx'0 hx'k)
    (exists_coord_ne hy'0 hy'k)
  refine ⟨P * A₀ * P⁻¹, ?_, ?_⟩
  · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPi _ _ hP, hA₀k, hP]
  · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hx', hA₀, hy', hPP]

end Coord

theorem oTwoUpper_sup_eq [Finite G] {S H : Subgroup G} (hS : IsSylowTwoOf S H) :
    oTwoUpper H ⊔ S = H := by
  classical
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hNH : oTwoUpper H ⊔ S ≤ H := sup_le hKH hS.1
  refine le_antisymm hNH ?_
  have h1 : (oTwoUpper H ⊔ S).relIndex H ∣ S.relIndex H :=
    Subgroup.relIndex_dvd_of_le_left H le_sup_right
  have h2 : (oTwoUpper H ⊔ S).relIndex H ∣ (oTwoUpper H).relIndex H :=
    Subgroup.relIndex_dvd_of_le_left H le_sup_left
  have h3 : ∃ m : ℕ, (oTwoUpper H).relIndex H = 2 ^ m := by
    have hn : ((oTwoUpper H).subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr (le_normalizer_oTwoUpper H)
    have hp : IsPGroup 2 (↥H ⧸ (oTwoUpper H).subgroupOf H) := by
      intro q
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper H h.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr hk
    obtain ⟨m, hm⟩ := hp.exists_card_eq
    exact ⟨m, by rw [Subgroup.relIndex, Subgroup.index_eq_card, hm]⟩
  obtain ⟨m, hm⟩ := h3
  rw [hm] at h2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  have hj0 : j = 0 := by
    by_contra hne
    apply hS.2.2
    have h2d : 2 ∣ (oTwoUpper H ⊔ S).relIndex H := by
      rw [hj]
      exact dvd_pow_self 2 hne
    exact h2d.trans h1
  rw [hj0, pow_zero] at hj
  exact Subgroup.relIndex_eq_one.mp hj

theorem exists_conj_V₁ [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ}
    (hyp : Hyp121 G T L V V₁ V₂ n) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hV : IsElemAbelian 2 V) {v a b : G} (hv : v ∈ V₁) (hv1 : v ≠ 1) (ha : a ∈ V₁) (ha1 : a ≠ 1)
    (hav : a ≠ v) (hb : b ∈ V₁) (hb1 : b ≠ 1) (hbv : b ≠ v) :
    ∃ l ∈ L, l * v * l⁻¹ = v ∧ l * a * l⁻¹ = b := by
  have hn : 3 ≤ n := by rcases hyp.rank with h | h <;> omega
  have hV₁V : V₁ ≤ V := hyp.sup ▸ le_sup_left
  have hH9 := h9Hyp_of_hyp121 hyp hTL hV
  obtain ⟨e, φ, hLe, -, hW₁, -⟩ := H9Coord.exists_linIso hH9 hn
  let w : ∀ x : G, x ∈ V₁ → IntMod V hV := fun x hx => IntMod.mk hV ⟨x, hV₁V hx⟩
  have hw₂ : ∀ x (hx : x ∈ V₁), (e (w x hx)).2 = 1 := fun x hx => (hW₁ _).mp hx
  have hwval : ∀ x (hx : x ∈ V₁), (w x hx).val = x := fun _ _ => rfl
  have hinj : ∀ x (hx : x ∈ V₁) y (hy : y ∈ V₁),
      ((e (w x hx)).1).toAdd = ((e (w y hy)).1).toAdd → x = y := by
    intro x hx y hy h
    have h1 : e (w x hx) = e (w y hy) :=
      Prod.ext (Multiplicative.toAdd.injective h) ((hw₂ x hx).trans (hw₂ y hy).symm)
    have h2 := congrArg IntMod.val (e.injective h1)
    exact h2
  have hzero : ∀ x (hx : x ∈ V₁), ((e (w x hx)).1).toAdd = 0 → x = 1 := by
    intro x hx h
    refine hinj x hx 1 V₁.one_mem ?_
    rw [h, show w 1 V₁.one_mem = 1 from IntMod.val_injective rfl, map_one]
    rfl
  obtain ⟨A, hAv, hAa⟩ := exists_sl_fix (fun h => hv1 (hzero v hv h))
    (fun h => ha1 (hzero a ha h)) (fun h => hav (hinj a ha v hv h))
    (fun h => hb1 (hzero b hb h)) (fun h => hbv (hinj b hb v hv h))
  set A' : GL (Fin n) (ZMod 2) := Matrix.SpecialLinearGroup.toGL A with hA'
  have hA'm : (A' : Matrix (Fin n) (Fin n) (ZMod 2)) = (A : Matrix (Fin n) (Fin n) (ZMod 2)) := rfl
  set lb := φ.symm A' with hlb
  obtain ⟨⟨g, hgN⟩, hgL, hg⟩ := (mem_autI hV).1 lb.2
  have hact : ∀ x (hx : x ∈ V₁), ((e ((lb : MulAut (IntMod V hV)) (w x hx))).1).toAdd =
      (A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ ((e (w x hx)).1).toAdd := by
    intro x hx
    rw [hLe, hlb, MulEquiv.apply_symm_apply, H9Coord.vecAut_apply, toAdd_ofAdd, hA'm]
  have hmapsto : ∀ x (hx : x ∈ V₁) y (hy : y ∈ V₁),
      (A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ ((e (w x hx)).1).toAdd = ((e (w y hy)).1).toAdd →
        g * x * g⁻¹ = y := by
    intro x hx y hy h
    have h1 : (lb : MulAut (IntMod V hV)) (w x hx) = w y hy := by
      apply e.injective
      refine Prod.ext (Multiplicative.toAdd.injective ((hact x hx).trans h)) ?_
      rw [hw₂ y hy, hLe, hw₂ x hx, map_one]
    have h2 := congrArg IntMod.val h1
    rw [← hg, convI_apply_val] at h2
    exact h2
  exact ⟨g, hgL, hmapsto v hv v hv hAv, hmapsto a ha b hb hAa⟩

theorem charTwo_of_no_component [Finite G] {X : Subgroup G}
    (hE : ∀ K : Subgroup G, ¬ IsComponentIn K X) (hodd : oddCoreIn X = ⊥) : CharTwo X :=
  CFSG.QuasithinUnique.charTwo_of_forall_not_isComponentIn hE hodd

theorem le_oTwoUpper_sup [Finite G] {X C T₁ : Subgroup G} (hXC : X ≤ C)
    (hCX : C ≤ Subgroup.normalizer (X : Set G)) (hT₁ : IsSylowTwoOf T₁ C) :
    X ≤ oTwoUpper X ⊔ T₁ := by
  have h1 := A4.isSylowTwoOf_inf_normal hT₁ hXC hCX
  have h2 := oTwoUpper_sup_eq h1
  calc X = oTwoUpper X ⊔ (T₁ ⊓ X) := h2.symm
    _ ≤ oTwoUpper X ⊔ T₁ := sup_le_sup_left inf_le_left _

theorem of_tildeOf_le {V₁ X Q : Subgroup G} (hX : X ≤ Subgroup.normalizer (V₁ : Set G))
    (hQ : Q ≤ Subgroup.normalizer (V₁ : Set G)) (hV₁Q : V₁ ≤ Q)
    (h : tildeOf V₁ X ≤ omegaOneCenterOf (tildeOf V₁ Q)) :
    X ≤ Q ∧ ∀ x ∈ X, ∀ q ∈ Q, x * q * x⁻¹ * q⁻¹ ∈ V₁ := by
  have hmem : ∀ x (hx : x ∈ X), tmk V₁ ⟨x, hX hx⟩ ∈ omegaOneCenterOf (tildeOf V₁ Q) :=
    fun x hx => (secImg_le_iff.1 h) ⟨x, hX hx⟩ hx
  refine ⟨fun x hx => ?_, fun x hx q hq => ?_⟩
  · have h1 := omegaOneCenterOf_le _ (hmem x hx)
    obtain ⟨q, hq, hqx⟩ := mem_secImg.1 h1
    have h2 := secMk_eq_secMk_iff.1 hqx
    have e : x = (q : G) * ((q : G)⁻¹ * x) := by group
    rw [e]
    exact Q.mul_mem hq (hV₁Q h2)
  · have hqQ : tmk V₁ ⟨q, hQ hq⟩ ∈ tildeOf V₁ Q := secMk_mem_secImg hq
    have h1 := mem_centralizer_of_mem_omegaOneCenterOf (hmem x hx) hqQ
    exact commutator_mem_of_secMk_commute h1.symm

theorem isElemAbelian_of_le {V X : Subgroup G} (hV : IsElemAbelian 2 V) (hXV : X ≤ V) :
    IsElemAbelian 2 X := CFSG.Open.IsElemAbelian.mono hV hXV

theorem mem_normalizer_inf {A B : Subgroup G} {x : G} (hA : x ∈ Subgroup.normalizer (A : Set G))
    (hB : x ∈ Subgroup.normalizer (B : Set G)) : x ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) :
      Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro g
  simp only [Subgroup.mem_inf]
  rw [hA g, hB g]

theorem irred_V₁ [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ}
    (hyp : Hyp121 G T L V V₁ V₂ n) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hV : IsElemAbelian 2 V) {v : G} (hv : v ∈ V₁) (hv1 : v ≠ 1) (W : Subgroup G)
    (hW1 : Subgroup.zpowers v ≤ W) (hW2 : W ≤ V₁)
    (hWN : L ⊓ Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (W : Set G)) :
    W = Subgroup.zpowers v ∨ W = V₁ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hne1, hne2⟩ := hcon
  obtain ⟨a, haW, havz⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hW1 (Ne.symm hne1))
  obtain ⟨b, hbV, hbW⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hW2 hne2)
  have hvW : v ∈ W := hW1 (Subgroup.mem_zpowers v)
  have ha1 : a ≠ 1 := fun h => havz (h ▸ Subgroup.one_mem _)
  have hav : a ≠ v := fun h => havz (h ▸ Subgroup.mem_zpowers v)
  have hb1 : b ≠ 1 := fun h => hbW (h ▸ W.one_mem)
  have hbv : b ≠ v := fun h => hbW (h ▸ hvW)
  obtain ⟨l, hlL, hlv, hlab⟩ :=
    exists_conj_V₁ hyp hTL hV hv hv1 (hW2 haW) ha1 hav hbV hb1 hbv
  have hlC : l ∈ Subgroup.centralizer ({v} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc l * v = l * v * l⁻¹ * l := by group
      _ = v * l := by rw [hlv]
  have h1 := (Subgroup.mem_normalizer_iff.mp (hWN ⟨hlL, hlC⟩) a).mp haW
  rw [hlab] at h1
  exact hbW h1

@[expose] def iSet (V : Subgroup G) (g : G) : Set G := {x | x ∈ V ∨ ∃ y ∈ V, x = g * y * g⁻¹}

structure Ctx0 [Finite G] (T L V V₁ V₂ : Subgroup G) (n : ℕ) (β : G → G → ZMod 2) (v : G) :
    Prop where
  hyp : Hyp121 G T L V V₁ V₂ n
  hTL : T ≤ Subgroup.normalizer (L : Set G)
  hβ : IsDualPairing121 L V₁ V₂ β
  hv : V₁ ⊓ Subgroup.centralizer ((T ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) : Set G) =
    Subgroup.zpowers v

structure Ctx [Finite G] (T L V V₁ V₂ : Subgroup G) (n : ℕ) (β : G → G → ZMod 2) (v : G) : Prop
    extends Ctx0 T L V V₁ V₂ n β v where
  hSyl : IsSylowTwoOf (T ⊓ Subgroup.normalizer (V₁ : Set G)) (Subgroup.centralizer ({v} : Set G))
  hHe : CharTwo (Subgroup.centralizer ({v} : Set G))
  hone : ∀ U : Subgroup G, U ≤ V →
    ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (L : Set G) →
      ∀ u ∈ U, IsSingular121 V₁ V₂ β u

namespace Ctx0

variable [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ} {β : G → G → ZMod 2} {v : G}
  (c : Ctx0 T L V V₁ V₂ n β v)
include c

theorem hVe : IsElemAbelian 2 V :=
  Sec121Thm.isElemAbelian_of_isPrimeReduced c.hyp.le c.hyp.reduced

theorem V₁_le : V₁ ≤ V := c.hyp.sup ▸ le_sup_left

theorem V₂_le : V₂ ≤ V := c.hyp.sup ▸ le_sup_right

theorem comm {x y : G} (hx : x ∈ V) (hy : y ∈ V) : x * y = y * x :=
  congrArg Subtype.val (c.hVe.1.1.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem mul_self {x : G} (hx : x ∈ V) : x * x = 1 := by
  have := c.hVe.2 x hx
  rwa [pow_two] at this

theorem inv_eq {x : G} (hx : x ∈ V) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (c.mul_self hx)

theorem v_mem : v ∈ V₁ ⊓ Subgroup.centralizer
    ((T ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) : Set G) :=
  c.hv ▸ Subgroup.mem_zpowers v

theorem v_mem_V₁ : v ∈ V₁ := c.v_mem.1

theorem v_mem_V : v ∈ V := c.V₁_le c.v_mem_V₁

theorem v_ne_one : v ≠ 1 := by
  intro h
  apply Sec1215.inf_centralizer_ne_bot c.hyp c.hTL
  rw [c.hv, h, Subgroup.zpowers_one_eq_bot]

theorem orderOf_v : orderOf v = 2 :=
  orderOf_eq_prime (c.hVe.2 v c.v_mem_V) c.v_ne_one

theorem mem_zpowers_iff {x : G} : x ∈ Subgroup.zpowers v ↔ x = 1 ∨ x = v := by
  constructor
  · exact I4.eq_one_or_eq_of_mem_zpowers c.orderOf_v
  · rintro (h | h)
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h]
      exact Subgroup.mem_zpowers v

theorem T₁_le : T ⊓ Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.centralizer ({v} : Set G) :=
  fun t ht => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp c.v_mem.2 t ht

theorem V_le_T : V ≤ T := Sec1215.le_of_hyp121 c.hyp c.hTL

theorem V_le_T₁ : V ≤ T ⊓ Subgroup.normalizer (V₁ : Set G) :=
  le_inf c.V_le_T fun x hx => Sec121Swap.mem_normalizer_of_conj_mem fun a ha => by
    rw [c.comm hx (c.V₁_le ha), mul_inv_cancel_right]
    exact ha

theorem T₁_le_NL : T ⊓ Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (L : Set G) :=
  inf_le_left.trans c.hTL

omit c in
theorem Qv_le (hSyl : IsSylowTwoOf (T ⊓ Subgroup.normalizer (V₁ : Set G))
      (Subgroup.centralizer ({v} : Set G))) :
    pCoreOf 2 (Subgroup.centralizer ({v} : Set G)) ≤ T ⊓ Subgroup.normalizer (V₁ : Set G) :=
  pCoreOf_two_le_of_isSylowTwoOf hSyl

omit [Finite G] c in
theorem Qv_normal {g q : G} (hg : g ∈ Subgroup.centralizer ({v} : Set G))
    (hq : q ∈ pCoreOf 2 (Subgroup.centralizer ({v} : Set G))) :
    g * q * g⁻¹ ∈ pCoreOf 2 (Subgroup.centralizer ({v} : Set G)) :=
  (Subgroup.mem_normalizer_iff.mp
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hg) q).mp hq

theorem zpowers_le_Qv : Subgroup.zpowers v ≤ pCoreOf 2 (Subgroup.centralizer ({v} : Set G)) := by
  refine le_pCoreOf_of_le_normalizer ?_ ?_ ?_
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  · rw [← I4.normalizer_zpowers_eq_centralizer c.orderOf_v]
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, c.orderOf_v, pow_one])

theorem ne_bot_V₁ : V₁ ≠ ⊥ := by
  obtain ⟨hc₁, hnat₁⟩ := c.hyp.nat₁
  have hn2 : 2 ≤ n := by rcases c.hyp.rank with h | h <;> omega
  exact Sec121Q.ne_bot_of_natural hn2 hnat₁

theorem conj_V₂ {m : G} (hm : m ∈ Subgroup.normalizer (L : Set G))
    (hm1 : m ∈ Subgroup.normalizer (V₁ : Set G)) {x : G} (hx : x ∈ V₂) : m * x * m⁻¹ ∈ V₂ := by
  have := c.hVe.1
  rcases Sec1212.conj_mem_of_hyp121 c.hyp hm with ⟨-, h2⟩ | h
  · exact h2 x hx
  · exfalso
    apply c.ne_bot_V₁
    rw [eq_bot_iff]
    intro a ha
    have h1 : m * a * m⁻¹ ∈ V₁ ⊓ V₂ :=
      ⟨(Subgroup.mem_normalizer_iff.mp hm1 a).mp ha, h a ha⟩
    rw [c.hyp.inf, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    calc a = m⁻¹ * (m * a * m⁻¹) * m := by group
      _ = 1 := by rw [h1]; group

theorem mem_centralizer_V {m : G} (hm : m ∈ Subgroup.normalizer (L : Set G))
    (h : (∀ a ∈ V₁, m * a = a * m) ∨ ∀ x ∈ V₂, m * x = x * m) :
    m ∈ Subgroup.centralizer (V : Set G) := by
  have := c.hVe.1
  rcases h with h | h
  · obtain ⟨hc₁, hnat₁⟩ := c.hyp.nat₁
    exact Sec1212.mem_centralizer_of_hyp121 c.hyp c.V₁_le c.hyp.norm₁ hnat₁ hm
      (Subgroup.mem_centralizer_iff.mpr fun a ha => (h a ha).symm)
  · obtain ⟨hc₂, hnat₂⟩ := c.hyp.nat₂
    exact Sec1212.mem_centralizer_of_hyp121 c.hyp c.V₂_le c.hyp.norm₂ hnat₂ hm
      (Subgroup.mem_centralizer_iff.mpr fun x hx => (h x hx).symm)

theorem β_one_right {a : G} (ha : a ∈ V₁) : β a 1 = 0 := by
  have h := c.hβ.2.1 a ha 1 V₂.one_mem 1 V₂.one_mem
  rw [one_mul] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

theorem eq_one_of_β_left {a : G} (ha : a ∈ V₁) (h : ∀ x ∈ V₂, β a x = 0) : a = 1 := by
  by_contra h1
  obtain ⟨x, hx, hax⟩ := c.hβ.2.2.1 a ha h1
  rw [h x hx] at hax
  exact zero_ne_one hax

theorem eq_one_of_β_right {x : G} (hx : x ∈ V₂) (h : ∀ a ∈ V₁, β a x = 0) : x = 1 := by
  by_contra h1
  obtain ⟨a, ha, hax⟩ := c.hβ.2.2.2.1 x hx h1
  rw [h a ha] at hax
  exact zero_ne_one hax

@[expose] def U₂ : Subgroup G where
  carrier := {x | x ∈ V₂ ∧ β v x = 0}
  mul_mem' := fun {x y} hx hy =>
    ⟨V₂.mul_mem hx.1 hy.1, by rw [c.hβ.2.1 v c.v_mem_V₁ x hx.1 y hy.1, hx.2, hy.2, add_zero]⟩
  one_mem' := ⟨V₂.one_mem, c.β_one_right c.v_mem_V₁⟩
  inv_mem' := fun {x} hx => by
    show x⁻¹ ∈ V₂ ∧ β v x⁻¹ = 0
    rw [c.inv_eq (c.V₂_le hx.1)]
    exact hx

theorem U₂_le : c.U₂ ≤ V₂ := fun _ hx => hx.1

theorem U₂_le_V : c.U₂ ≤ V := c.U₂_le.trans c.V₂_le

theorem exists_U₂_ne_one : ∃ x ∈ c.U₂, x ≠ 1 := by
  have := c.hVe.1
  obtain ⟨-, hcard₂, -⟩ := Sec1212.card_eq_of_hyp121 c.hyp
  have hn2 : 2 ≤ n := by rcases c.hyp.rank with h | h <;> omega
  have h4 : 4 ≤ Nat.card V₂ := by
    rw [hcard₂]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hex : ∀ a b : G, ∃ y ∈ V₂, y ≠ a ∧ y ≠ b := by
    intro a b
    by_contra h
    push Not at h
    have hsub : (V₂ : Set G) ⊆ {a, b} := fun y hy => by
      by_cases hya : y = a
      · exact Or.inl hya
      · exact Or.inr (h y hy hya)
    have h1 : Nat.card V₂ ≤ 2 := by
      rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
      exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
        ((Set.ncard_insert_le a {b}).trans (by rw [Set.ncard_singleton]))
    omega
  obtain ⟨x, hx, hx1, -⟩ := hex 1 1
  by_cases hxv : β v x = 0
  · exact ⟨x, ⟨hx, hxv⟩, hx1⟩
  obtain ⟨y, hy, hy1, hyx⟩ := hex 1 x
  by_cases hyv : β v y = 0
  · exact ⟨y, ⟨hy, hyv⟩, hy1⟩
  have h01 : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
  refine ⟨x * y, ⟨V₂.mul_mem hx hy, ?_⟩, ?_⟩
  · rw [c.hβ.2.1 v c.v_mem_V₁ x hx y hy, h01 _ hxv, h01 _ hyv]
    decide
  · intro h
    apply hyx
    have : x = y⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this, c.inv_eq (c.V₂_le hy)]

theorem mem_zpowers_of_perp {a : G} (ha : a ∈ V₁) (h : ∀ x ∈ c.U₂, β a x = 0) :
    a ∈ Subgroup.zpowers v := by
  have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  obtain ⟨x₀, hx₀, hvx₀⟩ := c.hβ.2.2.1 v c.v_mem_V₁ c.v_ne_one
  have key : ∀ d ∈ V₂, β a d = β a x₀ * β v d := by
    intro d hd
    rcases h01 (β v d) with h0 | h1
    · rw [h0, mul_zero]
      exact h d ⟨hd, h0⟩
    · have hdx : d * x₀ ∈ c.U₂ := ⟨V₂.mul_mem hd hx₀, by
        rw [c.hβ.2.1 v c.v_mem_V₁ d hd x₀ hx₀, h1, hvx₀]
        decide⟩
      have h2 := h _ hdx
      rw [c.hβ.2.1 a ha d hd x₀ hx₀] at h2
      rw [h1, mul_one]
      have h3 : β a d = -β a x₀ := eq_neg_of_add_eq_zero_left h2
      rw [h3]
      exact CharTwo.neg_eq _
  rw [c.mem_zpowers_iff]
  rcases h01 (β a x₀) with h0 | h1
  · left
    exact c.eq_one_of_β_left ha fun d hd => by rw [key d hd, h0, zero_mul]
  · right
    have h2 : a * v = 1 := c.eq_one_of_β_left (V₁.mul_mem ha c.v_mem_V₁) fun d hd => by
      rw [c.hβ.1 a ha v c.v_mem_V₁ d hd, key d hd, h1, one_mul]
      exact CharTwo.add_self_eq_zero _
    calc a = a * v * v⁻¹ := by group
      _ = v := by rw [h2, one_mul, c.inv_eq c.v_mem_V]

theorem β_conj {m : G} (hm : m ∈ Subgroup.normalizer (L : Set G))
    (hm1 : m ∈ Subgroup.normalizer (V₁ : Set G)) {a x : G} (ha : a ∈ V₁) (hx : x ∈ V₂) :
    β (m * a * m⁻¹) (m * x * m⁻¹) = β a x := by
  obtain ⟨hc₁, hnat₁⟩ := c.hyp.nat₁
  have hmN : Subgroup.zpowers m ≤ Subgroup.normalizer (V₁ : Set G) := by
    rw [Subgroup.zpowers_le]
    exact hm1
  have hφ : A4.actionOn V₁ (Subgroup.normalizer (V₁ : Set G)) le_rfl ⟨m, hm1⟩ ∈ autOn L V₁ := by
    rw [G64.BinaryNaturalSL.eq_top hnat₁]
    exact Subgroup.mem_top _
  obtain ⟨⟨l, hl⟩, hlφ⟩ := (A4.mem_autOn_iff c.hyp.norm₁).mp hφ
  have hla : ∀ b ∈ V₁, l * b * l⁻¹ = m * b * m⁻¹ := by
    intro b hb
    have h1 := congrArg (fun ψ : MulAut ↥V₁ => ((ψ ⟨b, hb⟩ : ↥V₁) : G)) hlφ
    simpa only [A4.actionOn_apply_coe] using h1
  have hlm : l⁻¹ * m ∈ Subgroup.centralizer (V : Set G) := by
    refine c.mem_centralizer_V ((Subgroup.normalizer (L : Set G)).mul_mem
      ((Subgroup.normalizer (L : Set G)).inv_mem (Subgroup.le_normalizer hl)) hm) (Or.inl ?_)
    intro b hb
    have h1 := hla b hb
    calc l⁻¹ * m * b = l⁻¹ * (m * b * m⁻¹) * m := by group
      _ = l⁻¹ * (l * b * l⁻¹) * m := by rw [h1]
      _ = b * (l⁻¹ * m) := by group
  have hconj : ∀ y ∈ V, m * y * m⁻¹ = l * y * l⁻¹ := by
    intro y hy
    have h1 := Subgroup.mem_centralizer_iff.mp hlm y hy
    calc m * y * m⁻¹ = l * ((l⁻¹ * m) * y) * m⁻¹ := by group
      _ = l * (y * (l⁻¹ * m)) * m⁻¹ := by rw [h1]
      _ = l * y * l⁻¹ := by group
  rw [hconj a (c.V₁_le ha), hconj x (c.V₂_le hx)]
  exact c.hβ.2.2.2.2 l hl a ha x hx

theorem centralizes_U₂ {m : G} (hm : m ∈ Subgroup.normalizer (L : Set G))
    (hm1 : m ∈ Subgroup.normalizer (V₁ : Set G))
    (h : ∀ a ∈ V₁, m * a * m⁻¹ * a⁻¹ ∈ Subgroup.zpowers v) {x : G} (hx : x ∈ c.U₂) :
    m * x * m⁻¹ = x := by
  have hy : m * x * m⁻¹ ∈ V₂ := c.conj_V₂ hm hm1 hx.1
  have hd : m * x * m⁻¹ * x⁻¹ = 1 := by
    refine c.eq_one_of_β_right (V₂.mul_mem hy (V₂.inv_mem hx.1)) fun a ha => ?_
    have ha' : m⁻¹ * a * m ∈ V₁ := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (V₁ : Set G)).inv_mem hm1)
        a).mp ha
      simpa using this
    have h1 := h _ ha'
    have e1 : m * (m⁻¹ * a * m) * m⁻¹ = a := by group
    rw [e1] at h1
    have h2 : β (m⁻¹ * a * m) x = β a x := by
      rcases c.mem_zpowers_iff.mp h1 with h3 | h3
      · have : m⁻¹ * a * m = a := by
          have := mul_inv_eq_one.mp h3
          exact this.symm
        rw [this]
      · have e2 : m⁻¹ * a * m = v * a := by
          have := mul_inv_eq_iff_eq_mul.mp h3
          calc m⁻¹ * a * m = (a * (m⁻¹ * a * m)⁻¹)⁻¹ * a := by group
            _ = v⁻¹ * a := by rw [h3]
            _ = v * a := by rw [c.inv_eq c.v_mem_V]
        rw [e2, c.hβ.1 v c.v_mem_V₁ a ha x hx.1, hx.2, zero_add]
    have h3 := c.β_conj hm hm1 ha' hx.1
    rw [e1] at h3
    rw [c.hβ.2.1 a ha _ hy _ (V₂.inv_mem hx.1), c.inv_eq (c.V₂_le hx.1), h3, h2]
    exact CharTwo.add_self_eq_zero _
  exact mul_inv_eq_one.mp hd

theorem comm_V₁_of_centralizes {m : G} (hm : m ∈ Subgroup.normalizer (L : Set G))
    (hm1 : m ∈ Subgroup.normalizer (V₁ : Set G)) (hU : ∀ x ∈ c.U₂, m * x * m⁻¹ = x) {a : G}
    (ha : a ∈ V₁) : m * a * m⁻¹ * a⁻¹ ∈ Subgroup.zpowers v := by
  have hma : m * a * m⁻¹ ∈ V₁ := (Subgroup.mem_normalizer_iff.mp hm1 a).mp ha
  refine c.mem_zpowers_of_perp (V₁.mul_mem hma (V₁.inv_mem ha)) fun x hx => ?_
  rw [c.hβ.1 _ hma _ (V₁.inv_mem ha) x hx.1, c.inv_eq (c.V₁_le ha)]
  have h1 := c.β_conj hm hm1 ha hx.1
  rw [hU x hx] at h1
  rw [h1]
  exact CharTwo.add_self_eq_zero _

theorem comm_V₂_of_centralizes {m : G} (hm : m ∈ Subgroup.normalizer (L : Set G))
    (hm1 : m ∈ Subgroup.normalizer (V₁ : Set G)) (hmv : m * v * m⁻¹ = v) {x : G}
    (hx : x ∈ V₂) : m * x * m⁻¹ * x⁻¹ ∈ c.U₂ := by
  have hmx : m * x * m⁻¹ ∈ V₂ := c.conj_V₂ hm hm1 hx
  refine ⟨V₂.mul_mem hmx (V₂.inv_mem hx), ?_⟩
  rw [c.hβ.2.1 v c.v_mem_V₁ _ hmx _ (V₂.inv_mem hx), c.inv_eq (c.V₂_le hx)]
  have h1 := c.β_conj hm hm1 c.v_mem_V₁ hx
  rw [hmv] at h1
  rw [h1]
  exact CharTwo.add_self_eq_zero _

theorem oTwo_eq_L : L = oTwoUpper L :=
  (c.hyp.faithful.2.1 _ (oTwoUpper_le L)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le L)).mpr
      (le_normalizer_oTwoUpper L))
    fun _ hx => exists_pow_mem_oTwoUpper L hx).symm

theorem centralizer_eq_normalizer :
    Subgroup.normalizer (Subgroup.zpowers v : Set G) = Subgroup.centralizer ({v} : Set G) :=
  I4.normalizer_zpowers_eq_centralizer c.orderOf_v

theorem CL_le : L ⊓ Subgroup.centralizer ({v} : Set G) ≤
    lOne L (Subgroup.zpowers v) ⊔ (T ⊓ Subgroup.normalizer (V₁ : Set G)) := by
  have hT₁C : T ⊓ Subgroup.normalizer (V₁ : Set G) ≤
      Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({v} : Set G) :=
    le_inf c.T₁_le_NL c.T₁_le
  have := c.hVe.1
  have hSyl : IsSylowTwoOf (T ⊓ Subgroup.normalizer (V₁ : Set G))
      (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({v} : Set G)) :=
    Sec1215.isSylowTwoOf_of_le_of_le (Sec1215.isSylowTwoOf_inf_normalizer c.hyp c.hTL).2 hT₁C
      fun m hm => ⟨hm.1, Sec1215.mem_normalizer_of_mem_centralizer c.hyp c.v_mem_V₁ c.v_ne_one
        hm.1 hm.2⟩
  have hle := le_oTwoUpper_sup (inf_le_inf_right _ Subgroup.le_normalizer)
    (fun x hx => mem_normalizer_inf hx.1 (Subgroup.le_normalizer hx.2)) hSyl
  refine hle.trans (sup_le_sup_right ?_ _)
  refine oTwoUpper_mono (inf_le_inf_left _ ?_)
  rw [c.centralizer_eq_normalizer]

theorem irred : IsIrredOnSection (lOne L (Subgroup.zpowers v) ⊔
    (T ⊓ Subgroup.normalizer (V₁ : Set G))) V₁ (Subgroup.zpowers v) := by
  have hzV₁ : Subgroup.zpowers v ≤ V₁ := by
    rw [Subgroup.zpowers_le]
    exact c.v_mem_V₁
  have hlOne : lOne L (Subgroup.zpowers v) ≤ L ⊓ Subgroup.centralizer ({v} : Set G) := by
    rw [← c.centralizer_eq_normalizer]
    exact oTwoUpper_le _
  have hX1 : lOne L (Subgroup.zpowers v) ⊔ (T ⊓ Subgroup.normalizer (V₁ : Set G)) ≤
      Subgroup.normalizer (V₁ : Set G) :=
    sup_le (hlOne.trans (inf_le_left.trans c.hyp.norm₁)) inf_le_right
  have hX2 : lOne L (Subgroup.zpowers v) ⊔ (T ⊓ Subgroup.normalizer (V₁ : Set G)) ≤
      Subgroup.normalizer (Subgroup.zpowers v : Set G) := by
    rw [c.centralizer_eq_normalizer]
    exact sup_le (hlOne.trans inf_le_right) c.T₁_le
  refine ⟨lt_of_le_of_ne hzV₁ fun h => ?_, hX1, hX2, fun W hW1 hW2 hWN => ?_⟩
  ·
    have := c.hVe.1
    obtain ⟨hcard₁, -, -⟩ := Sec1212.card_eq_of_hyp121 c.hyp
    have h1 : Nat.card V₁ = 2 := by
      rw [← h, Nat.card_zpowers, c.orderOf_v]
    have hn2 : 2 ≤ n := by rcases c.hyp.rank with h | h <;> omega
    rw [hcard₁] at h1
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  · exact irred_V₁ c.hyp c.hTL c.hVe c.v_mem_V₁ c.v_ne_one W hW1 hW2 (c.CL_le.trans hWN)

end Ctx0

namespace Ctx

variable [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ} {β : G → G → ZMod 2} {v : G}
  (c : Ctx T L V V₁ V₂ n β v)
include c

theorem Qv_le : pCoreOf 2 (Subgroup.centralizer ({v} : Set G)) ≤
    T ⊓ Subgroup.normalizer (V₁ : Set G) :=
  Ctx0.Qv_le c.hSyl

theorem almostSpecial : AlmostSpecialHyp V₁ (Subgroup.zpowers v) L
    (T ⊓ Subgroup.normalizer (V₁ : Set G)) (Subgroup.centralizer ({v} : Set G)) where
  elemAbelian := isElemAbelian_of_le c.hVe c.V₁_le
  ne_bot := by
    intro h
    have : v ∈ (⊥ : Subgroup G) := h ▸ Subgroup.mem_zpowers v
    exact c.v_ne_one (Subgroup.mem_bot.mp this)
  le_V := by
    rw [Subgroup.zpowers_le]
    exact c.v_mem_V₁
  oTwo_eq := c.oTwo_eq_L
  V_le_T := c.V₁_le.trans c.V_le_T₁
  T_le_normV₁ := by
    rw [c.centralizer_eq_normalizer]
    exact c.T₁_le
  T_le_normV := inf_le_right
  T_le_normL := c.T₁_le_NL
  sylow_LT := by
    have := c.hVe.1
    exact Sec1215.isSylowTwoOf_of_le_of_le
      (Sec1215.isSylowTwoOf_inf_normalizer c.hyp c.hTL).2 le_sup_right
      (sup_le (le_inf Subgroup.le_normalizer c.hyp.norm₁) (le_inf c.T₁_le_NL inf_le_right))
  H_le := c.centralizer_eq_normalizer.ge
  lOne_sup_le := by
    refine sup_le ?_ c.T₁_le
    unfold lOne
    rw [c.centralizer_eq_normalizer]
    exact (oTwoUpper_le _).trans inf_le_right
  sylow_H := c.hSyl
  charTwo := c.hHe
  irred := c.irred

theorem g22 : V₁ ≤ pCoreOf 2 (Subgroup.centralizer ({v} : Set G)) ∧
    ∀ a ∈ V₁, ∀ q ∈ pCoreOf 2 (Subgroup.centralizer ({v} : Set G)),
      a * q * a⁻¹ * q⁻¹ ∈ Subgroup.zpowers v := by
  have h := c.almostSpecial.G22_one
  have hV₁N : V₁ ≤ Subgroup.normalizer (Subgroup.zpowers v : Set G) := by
    rw [c.centralizer_eq_normalizer]
    exact c.V₁_le.trans (c.V_le_T₁.trans c.T₁_le)
  have hQN : pCoreOf 2 (Subgroup.centralizer ({v} : Set G)) ≤
      Subgroup.normalizer (Subgroup.zpowers v : Set G) := by
    rw [c.centralizer_eq_normalizer]
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 _
  exact of_tildeOf_le hV₁N hQN c.zpowers_le_Qv (h.1.trans h.2)

theorem V₁_le_Qv : V₁ ≤ pCoreOf 2 (Subgroup.centralizer ({v} : Set G)) := c.g22.1

theorem Qv_centralizes {q x : G} (hq : q ∈ pCoreOf 2 (Subgroup.centralizer ({v} : Set G)))
    (hx : x ∈ c.U₂) : q * x = x * q := by
  have hqT := c.Qv_le hq
  have h1 := c.centralizes_U₂ (c.T₁_le_NL hqT) hqT.2 (fun a ha => by
    have h2 := c.g22.2 a ha q hq
    have e : q * a * q⁻¹ * a⁻¹ = (a * q * a⁻¹ * q⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ h2) hx
  calc q * x = q * x * q⁻¹ * q := by group
    _ = x * q := by rw [h1]

theorem U₂_le_Qv : c.U₂ ≤ pCoreOf 2 (Subgroup.centralizer ({v} : Set G)) := by
  intro x hx
  have h : x ∈ Subgroup.centralizer
      ((pCoreOf 2 (Subgroup.centralizer ({v} : Set G)) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact c.Qv_centralizes hq hx
  exact c.hHe ⟨c.V_le_T₁.trans c.T₁_le (c.U₂_le_V hx), h⟩

theorem centralizer_le : Subgroup.centralizer ((V₁ ⊔ c.U₂ : Subgroup G) : Set G) ≤
    Subgroup.normalizer (L : Set G) := by
  by_contra hC
  obtain ⟨x, hx, hx1⟩ := c.exists_U₂_ne_one
  obtain ⟨a, ha, hax⟩ := c.hβ.2.2.2.1 x hx.1 hx1
  have hsing := c.hone _ (sup_le c.V₁_le c.U₂_le_V) hC (a * x)
    (Subgroup.mul_mem_sup ha hx)
  obtain ⟨a', ha', x', hx', he, h0⟩ := hsing
  obtain ⟨rfl, rfl⟩ := Sec1212.decomp_unique c.hyp.inf ha hx.1 ha' hx' he
  rw [hax] at h0
  exact one_ne_zero h0

theorem U₂_comm_conj {g : G} (hg : g ∈ Subgroup.centralizer ({v} : Set G)) {x y : G}
    (hx : x ∈ c.U₂) (hy : y ∈ V) : x * (g * y * g⁻¹) = (g * y * g⁻¹) * x := by
  have hz : g⁻¹ * x * g ∈ Subgroup.centralizer ((V₁ ⊔ c.U₂ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hwQ : w ∈ pCoreOf 2 (Subgroup.centralizer ({v} : Set G)) :=
      sup_le c.V₁_le_Qv c.U₂_le_Qv hw
    have hgw := Ctx0.Qv_normal hg hwQ
    have h1 := c.Qv_centralizes hgw hx
    calc w * (g⁻¹ * x * g) = g⁻¹ * ((g * w * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * w * g⁻¹)) * g := by rw [← h1]
      _ = g⁻¹ * x * g * w := by group
  have hzN := c.centralizer_le hz
  have hzV := c.mem_centralizer_V hzN (Or.inl fun a ha => by
    exact (Subgroup.mem_centralizer_iff.mp hz a (Subgroup.mem_sup_left ha)).symm)
  have h1 := Subgroup.mem_centralizer_iff.mp hzV y hy
  calc x * (g * y * g⁻¹) = g * ((g⁻¹ * x * g) * y) * g⁻¹ := by group
    _ = g * (y * (g⁻¹ * x * g)) * g⁻¹ := by rw [← h1]
    _ = (g * y * g⁻¹) * x := by group

theorem comm_of_le_Qv (hVQ : V ≤ pCoreOf 2 (Subgroup.centralizer ({v} : Set G))) {g : G}
    (hg : g ∈ Subgroup.centralizer ({v} : Set G)) {x y : G} (hx : x ∈ V) (hy : y ∈ V) :
    x * (g * y * g⁻¹) = (g * y * g⁻¹) * x := by
  have hginv : g⁻¹ ∈ Subgroup.centralizer ({v} : Set G) := Subgroup.inv_mem _ hg
  have hgv : g * v * g⁻¹ = v := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hg
    calc g * v * g⁻¹ = v * g * g⁻¹ := by rw [this]
      _ = v := by group
  have step1 : ∀ a ∈ V₁, ∀ d ∈ V₂, (g⁻¹ * a * g) * d = d * (g⁻¹ * a * g) := by
    intro a ha d hd
    set a' := g⁻¹ * a * g with ha'
    have ha'Q : a' ∈ pCoreOf 2 (Subgroup.centralizer ({v} : Set G)) := by
      have := Ctx0.Qv_normal hginv (hVQ (c.V₁_le ha))
      simpa [ha'] using this
    have ha'T := c.Qv_le ha'Q
    have hdQ : g * d * g⁻¹ ∈ pCoreOf 2 (Subgroup.centralizer ({v} : Set G)) :=
      Ctx0.Qv_normal hg (hVQ (c.V₂_le hd))
    have h1 := c.g22.2 a ha _ hdQ
    have hconjd : a' * d * a'⁻¹ ∈ V₂ := c.conj_V₂ (c.T₁_le_NL ha'T) ha'T.2 hd
    have e : a * (g * d * g⁻¹) * a⁻¹ * (g * d * g⁻¹)⁻¹ =
        g * (a' * d * a'⁻¹ * d⁻¹) * g⁻¹ := by
      rw [ha']; group
    rw [e] at h1
    rcases c.mem_zpowers_iff.mp h1 with h2 | h2
    · have h3 : a' * d * a'⁻¹ * d⁻¹ = 1 := by
        have := congrArg (fun t => g⁻¹ * t * g) h2
        simpa [mul_assoc] using this
      calc a' * d = a' * d * a'⁻¹ * d⁻¹ * (d * a') := by group
        _ = d * a' := by rw [h3, one_mul]
    · exfalso
      have h3 : a' * d * a'⁻¹ * d⁻¹ = v := by
        have := congrArg (fun t => g⁻¹ * t * g) h2
        have e2 : g⁻¹ * v * g = v := by
          calc g⁻¹ * v * g = g⁻¹ * (g * v * g⁻¹) * g := by rw [hgv]
            _ = v := by group
        simpa [mul_assoc, e2] using this
      have h4 : v ∈ V₂ := h3 ▸ V₂.mul_mem hconjd (V₂.inv_mem hd)
      have h5 : v ∈ V₁ ⊓ V₂ := ⟨c.v_mem_V₁, h4⟩
      rw [c.hyp.inf, Subgroup.mem_bot] at h5
      exact c.v_ne_one h5
  have step2 : ∀ a ∈ V₁, ∀ w ∈ V, a * (g * w * g⁻¹) = (g * w * g⁻¹) * a := by
    intro a ha w hw
    have ha'Q : g⁻¹ * a * g ∈ pCoreOf 2 (Subgroup.centralizer ({v} : Set G)) := by
      have := Ctx0.Qv_normal hginv (hVQ (c.V₁_le ha))
      simpa using this
    have hV := c.mem_centralizer_V (c.T₁_le_NL (c.Qv_le ha'Q))
      (Or.inr fun d hd => step1 a ha d hd)
    have h1 := Subgroup.mem_centralizer_iff.mp hV w hw
    calc a * (g * w * g⁻¹) = g * ((g⁻¹ * a * g) * w) * g⁻¹ := by group
      _ = g * (w * (g⁻¹ * a * g)) * g⁻¹ := by rw [← h1]
      _ = (g * w * g⁻¹) * a := by group
  have hyQ : g * y * g⁻¹ ∈ pCoreOf 2 (Subgroup.centralizer ({v} : Set G)) :=
    Ctx0.Qv_normal hg (hVQ hy)
  have hV := c.mem_centralizer_V (c.T₁_le_NL (c.Qv_le hyQ))
    (Or.inl fun a ha => (step2 a ha y hy).symm)
  exact Subgroup.mem_centralizer_iff.mp hV x hx

theorem comm_conj_V₁ {g : G} (hg : g ∈ Subgroup.centralizer ({v} : Set G)) {a : G}
    (ha : a ∈ V₁) {w : G} (hw : w ∈ V) :
    ∃ z ∈ Subgroup.zpowers v, ∃ u ∈ c.U₂,
      (g * a * g⁻¹) * w * (g * a * g⁻¹)⁻¹ * w⁻¹ = z * u := by
  set x := g * a * g⁻¹ with hxdef
  have hxQ : x ∈ pCoreOf 2 (Subgroup.centralizer ({v} : Set G)) := Ctx0.Qv_normal hg (c.V₁_le_Qv ha)
  have hxT := c.Qv_le hxQ
  have hxN := c.T₁_le_NL hxT
  have hxv : x * v * x⁻¹ = v := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (c.T₁_le hxT)
    calc x * v * x⁻¹ = v * x * x⁻¹ := by rw [this]
      _ = v := by group
  have hU : ∀ y ∈ c.U₂, x * y * x⁻¹ = y := fun y hy => by
    have := c.Qv_centralizes hxQ hy
    calc x * y * x⁻¹ = y * x * x⁻¹ := by rw [this]
      _ = y := by group
  have hcomm₁₂ : ∀ p ∈ V₁, ∀ q ∈ V₂, p * q = q * p := fun p hp q hq =>
    c.comm (c.V₁_le hp) (c.V₂_le hq)
  obtain ⟨a', ha', d, hd, rfl⟩ := Sec121Thm.exists_mul_of_mem_sup hcomm₁₂
    (show w ∈ V₁ ⊔ V₂ from c.hyp.sup.symm ▸ hw)
  refine ⟨x * a' * x⁻¹ * a'⁻¹, c.comm_V₁_of_centralizes hxN hxT.2 hU ha',
    x * d * x⁻¹ * d⁻¹, c.comm_V₂_of_centralizes hxN hxT.2 hxv hd, ?_⟩
  have h1 : x * a' * x⁻¹ ∈ V := c.V₁_le ((Subgroup.mem_normalizer_iff.mp hxT.2 a').mp ha')
  have h2 : x * d * x⁻¹ * d⁻¹ ∈ V :=
    c.V₂_le (V₂.mul_mem (c.conj_V₂ hxN hxT.2 hd) (V₂.inv_mem hd))
  have h3 := c.comm (V.inv_mem (c.V₁_le ha')) h2
  calc x * (a' * d) * x⁻¹ * (a' * d)⁻¹
      = x * a' * x⁻¹ * ((x * d * x⁻¹ * d⁻¹) * a'⁻¹) := by group
    _ = x * a' * x⁻¹ * (a'⁻¹ * (x * d * x⁻¹ * d⁻¹)) := by rw [h3]
    _ = x * a' * x⁻¹ * a'⁻¹ * (x * d * x⁻¹ * d⁻¹) := by group

@[expose] def zSet (g : G) : Set G :=
  {x | x ∈ c.U₂ ∨ (∃ u ∈ c.U₂, x = g * u * g⁻¹) ∨ x = v}

theorem zSet_comm {g : G} (hg : g ∈ Subgroup.centralizer ({v} : Set G)) {z : G}
    (hz : z ∈ c.zSet g) {x : G} (hx : x ∈ iSet V g) : z * x = x * z := by
  have hginv : g⁻¹ ∈ Subgroup.centralizer ({v} : Set G) := Subgroup.inv_mem _ hg
  have hgv : g * v * g⁻¹ = v := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hg
    calc g * v * g⁻¹ = v * g * g⁻¹ := by rw [this]
      _ = v := by group
  rcases hz with hz | ⟨u, hu, rfl⟩ | hzv
  · rcases hx with hx | ⟨y, hy, rfl⟩
    · exact c.comm (c.U₂_le_V hz) hx
    · exact c.U₂_comm_conj hg hz hy
  · rcases hx with hx | ⟨y, hy, rfl⟩
    ·
      have h1 := c.U₂_comm_conj hginv hu hx
      rw [inv_inv] at h1
      calc g * u * g⁻¹ * x = g * (u * (g⁻¹ * x * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * x * g) * u) * g⁻¹ := by rw [h1]
        _ = x * (g * u * g⁻¹) := by group
    · have h1 := c.comm (c.U₂_le_V hu) hy
      calc g * u * g⁻¹ * (g * y * g⁻¹) = g * (u * y) * g⁻¹ := by group
        _ = g * (y * u) * g⁻¹ := by rw [h1]
        _ = g * y * g⁻¹ * (g * u * g⁻¹) := by group
  · rw [hzv]
    rcases hx with hx | ⟨y, hy, rfl⟩
    · exact c.comm c.v_mem_V hx
    · have h1 := c.comm c.v_mem_V hy
      calc v * (g * y * g⁻¹) = g * v * g⁻¹ * (g * y * g⁻¹) := by rw [hgv]
        _ = g * (v * y) * g⁻¹ := by group
        _ = g * (y * v) * g⁻¹ := by rw [h1]
        _ = g * y * g⁻¹ * (g * v * g⁻¹) := by group
        _ = g * y * g⁻¹ * v := by rw [hgv]

theorem zSet_sub_iSet {g : G} : c.zSet g ⊆ iSet V g := by
  rintro z (hz | ⟨u, hu, rfl⟩ | hzv)
  · exact Or.inl (c.U₂_le_V hz)
  · exact Or.inr ⟨u, c.U₂_le_V hu, rfl⟩
  · rw [hzv]
    exact Or.inl c.v_mem_V

theorem closure_zSet_comm {g : G} (hg : g ∈ Subgroup.centralizer ({v} : Set G)) {z : G}
    (hz : z ∈ Subgroup.closure (c.zSet g)) {x : G} (hx : x ∈ Subgroup.closure (iSet V g)) :
    z * x = x * z := by
  have h1 : Subgroup.closure (iSet V g) ≤ Subgroup.centralizer (c.zSet g) := by
    rw [Subgroup.closure_le]
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro z hz
    exact c.zSet_comm hg hz hy
  have h2 : Subgroup.closure (c.zSet g) ≤ Subgroup.centralizer
      ((Subgroup.closure (iSet V g) : Subgroup G) : Set G) := by
    rw [Subgroup.closure_le]
    intro z hz
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    have := Subgroup.mem_centralizer_iff.mp (h1 hy) z hz
    exact this.symm
  exact (Subgroup.mem_centralizer_iff.mp (h2 hz) x hx).symm

theorem closure_zSet_sq {g : G} (hg : g ∈ Subgroup.centralizer ({v} : Set G)) {z : G}
    (hz : z ∈ Subgroup.closure (c.zSet g)) : z * z = 1 := by
  have hS : ∀ a ∈ c.zSet g, ∀ b ∈ c.zSet g, a * b = b * a := fun a ha b hb =>
    c.zSet_comm hg ha (c.zSet_sub_iSet hb)
  have h2 : ∀ a ∈ c.zSet g, a ^ 2 = 1 := by
    rintro a (ha | ⟨u, hu, rfl⟩ | hav)
    · exact c.hVe.2 a (c.U₂_le_V ha)
    · have := c.hVe.2 u (c.U₂_le_V hu)
      rw [conj_pow, this, mul_one, mul_inv_cancel]
    · rw [hav]
      exact c.hVe.2 v c.v_mem_V
  have := (B2F.isElemAbelian_closure hS h2).2 z hz
  rwa [pow_two] at this

theorem stab {g : G} (hg : g ∈ Subgroup.centralizer ({v} : Set G)) {y : G}
    (hy : y ∈ Subgroup.closure (iSet V g)) :
    ∀ u ∈ V₁ ⊔ c.U₂, y * u * y⁻¹ * u⁻¹ ∈ Subgroup.closure (c.zSet g) ∧
      y⁻¹ * u * y * u⁻¹ ∈ Subgroup.closure (c.zSet g) := by
  have hginv : g⁻¹ ∈ Subgroup.centralizer ({v} : Set G) := Subgroup.inv_mem _ hg
  have hgv : ∀ z ∈ Subgroup.zpowers v, g * z * g⁻¹ = z := fun z hz => by
    have := Subgroup.mem_centralizer_singleton_iff.mp hg
    rcases c.mem_zpowers_iff.mp hz with h | h
    · rw [h]
      group
    · rw [h]
      calc g * v * g⁻¹ = v * g * g⁻¹ := by rw [this]
        _ = v := by group
  have hcomm : ∀ p ∈ V₁, ∀ q ∈ c.U₂, p * q = q * p := fun p hp q hq =>
    c.comm (c.V₁_le hp) (c.U₂_le_V hq)
  have hgen : ∀ x ∈ iSet V g, ∀ u ∈ V₁ ⊔ c.U₂,
      x * u * x⁻¹ * u⁻¹ ∈ Subgroup.closure (c.zSet g) := by
    intro x hx u hu
    rcases hx with hx | ⟨w, hw, rfl⟩
    · have hu' : u ∈ V := sup_le c.V₁_le c.U₂_le_V hu
      rw [c.comm hx hu', mul_inv_cancel_right, mul_inv_cancel]
      exact Subgroup.one_mem _
    · obtain ⟨a, ha, d, hd, rfl⟩ := Sec121Thm.exists_mul_of_mem_sup hcomm hu
      have hdw := c.U₂_comm_conj hg hd hw
      obtain ⟨z, hz, u', hu', he⟩ := c.comm_conj_V₁ hginv ha hw
      rw [inv_inv] at he
      have e1 : g * w * g⁻¹ * (a * d) * (g * w * g⁻¹)⁻¹ * (a * d)⁻¹ =
          g * (g⁻¹ * a * g * w * (g⁻¹ * a * g)⁻¹ * w⁻¹)⁻¹ * g⁻¹ := by
        have e2 : g * w * g⁻¹ * d * (g * w * g⁻¹)⁻¹ = d := by
          calc g * w * g⁻¹ * d * (g * w * g⁻¹)⁻¹ = d * (g * w * g⁻¹) * (g * w * g⁻¹)⁻¹ := by
                rw [hdw]
            _ = d := by group
        calc g * w * g⁻¹ * (a * d) * (g * w * g⁻¹)⁻¹ * (a * d)⁻¹
            = g * w * g⁻¹ * a * (g * w * g⁻¹)⁻¹ *
                (g * w * g⁻¹ * d * (g * w * g⁻¹)⁻¹) * d⁻¹ * a⁻¹ := by group
          _ = g * w * g⁻¹ * a * (g * w * g⁻¹)⁻¹ * a⁻¹ := by rw [e2]; group
          _ = g * (g⁻¹ * a * g * w * (g⁻¹ * a * g)⁻¹ * w⁻¹)⁻¹ * g⁻¹ := by group
      rw [e1, he, mul_inv_rev]
      have e3 : g * (u'⁻¹ * z⁻¹) * g⁻¹ = (g * u'⁻¹ * g⁻¹) * (g * z⁻¹ * g⁻¹) := by group
      rw [e3, hgv _ (Subgroup.inv_mem _ hz)]
      refine Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr (Or.inl
        ⟨u'⁻¹, c.U₂.inv_mem hu', rfl⟩))) ?_
      rcases c.mem_zpowers_iff.mp (Subgroup.inv_mem _ hz) with h | h
      · rw [h]
        exact Subgroup.one_mem _
      · rw [h]
        exact Subgroup.subset_closure (Or.inr (Or.inr rfl))
  have hgen' : ∀ x ∈ iSet V g, x⁻¹ ∈ iSet V g := by
    rintro x (hx | ⟨w, hw, rfl⟩)
    · exact Or.inl (V.inv_mem hx)
    · exact Or.inr ⟨w⁻¹, V.inv_mem hw, by group⟩
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    intro u hu
    refine ⟨hgen x hx u hu, ?_⟩
    have := hgen x⁻¹ (hgen' x hx) u hu
    rwa [inv_inv] at this
  | one =>
    intro u hu
    simp only [one_mul, inv_one, mul_one, mul_inv_cancel]
    exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩
  | mul x₁ x₂ hx₁ hx₂ ih₁ ih₂ =>
    intro u hu
    obtain ⟨h₁, h₁'⟩ := ih₁ u hu
    obtain ⟨h₂, h₂'⟩ := ih₂ u hu
    constructor
    · have hc := c.closure_zSet_comm hg h₂ hx₁
      have e : x₁ * x₂ * u * (x₁ * x₂)⁻¹ * u⁻¹ =
          (x₁ * (x₂ * u * x₂⁻¹ * u⁻¹) * x₁⁻¹) * (x₁ * u * x₁⁻¹ * u⁻¹) := by group
      have e2 : x₁ * (x₂ * u * x₂⁻¹ * u⁻¹) * x₁⁻¹ = x₂ * u * x₂⁻¹ * u⁻¹ := by
        rw [← hc]
        group
      rw [e, e2]
      exact Subgroup.mul_mem _ h₂ h₁
    · have hc := c.closure_zSet_comm hg h₁' (Subgroup.inv_mem _ hx₂)
      have e : (x₁ * x₂)⁻¹ * u * (x₁ * x₂) * u⁻¹ =
          (x₂⁻¹ * (x₁⁻¹ * u * x₁ * u⁻¹) * x₂⁻¹⁻¹) * (x₂⁻¹ * u * x₂ * u⁻¹) := by group
      have e2 : x₂⁻¹ * (x₁⁻¹ * u * x₁ * u⁻¹) * x₂⁻¹⁻¹ = x₁⁻¹ * u * x₁ * u⁻¹ := by
        rw [← hc]
        group
      rw [e, e2]
      exact Subgroup.mul_mem _ h₁' h₂'
  | inv x _ ih =>
    intro u hu
    obtain ⟨h₁, h₁'⟩ := ih u hu
    rw [inv_inv]
    exact ⟨h₁', h₁⟩

theorem odd_mem_centralizer {g : G} (hg : g ∈ Subgroup.centralizer ({v} : Set G)) {y : G}
    (hy : y ∈ Subgroup.closure (iSet V g)) (hyo : Odd (orderOf y)) :
    y ∈ Subgroup.centralizer (V : Set G) := by
  have hU : y ∈ Subgroup.centralizer ((V₁ ⊔ c.U₂ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h1 := (c.stab hg hy u hu).1
    set z := y * u * y⁻¹ * u⁻¹ with hz
    have hz2 := c.closure_zSet_sq hg h1
    have hzy := c.closure_zSet_comm hg h1 hy
    have e1 : y * u * y⁻¹ = z * u := by rw [hz]; group
    have h2 : Commute (y ^ 2) u := by
      show y ^ 2 * u = u * y ^ 2
      have e2 : y ^ 2 * u * (y ^ 2)⁻¹ = u := by
        rw [pow_two]
        calc y * y * u * (y * y)⁻¹ = y * (y * u * y⁻¹) * y⁻¹ := by group
          _ = y * (z * u) * y⁻¹ := by rw [e1]
          _ = y * z * y⁻¹ * (y * u * y⁻¹) := by group
          _ = z * (z * u) := by
              rw [e1]
              congr 1
              calc y * z * y⁻¹ = z * y * y⁻¹ := by rw [← hzy]
                _ = z := by group
          _ = u := by rw [← mul_assoc, hz2, one_mul]
      calc y ^ 2 * u = y ^ 2 * u * (y ^ 2)⁻¹ * y ^ 2 := by group
        _ = u * y ^ 2 := by rw [e2]
    exact (commute_of_sq hyo h2).eq.symm
  exact c.mem_centralizer_V (c.centralizer_le hU) (Or.inl fun a ha =>
    (Subgroup.mem_centralizer_iff.mp hU a (Subgroup.mem_sup_left ha)).symm)

omit c in
theorem exists_odd_of_not_isPGroup {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hJ : ¬ IsPGroup 2 (Subgroup.closure ({x, y} : Set G))) :
    ∃ w ∈ Subgroup.closure ({x, y} : Set G), w ≠ 1 ∧ Odd (orderOf w) ∧ x * w * x⁻¹ = w⁻¹ := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  set r := x * y with hr
  have hxr : x * r * x⁻¹ = r⁻¹ := by
    rw [hr, mul_inv_rev, hxi, hyi]
    calc x * (x * y) * x = (x * x) * y * x := by group
      _ = y * x := by rw [hx, one_mul]
  have hxrj : ∀ j : ℤ, x * r ^ j = r ^ (-j) * x := by
    intro j
    have h1 : x * r ^ j * x⁻¹ = (r⁻¹) ^ j := by rw [← conj_zpow, hxr]
    calc x * r ^ j = x * r ^ j * x⁻¹ * x := by group
      _ = r ^ (-j) * x := by rw [h1, inv_zpow']
  have hfin : orderOf r ≠ 0 := (orderOf_pos r).ne'
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hfin
  set w := r ^ (2 ^ k) with hw
  have hwo : orderOf w = m := by
    rw [hw, orderOf_pow' r (by positivity), hkm, Nat.gcd_mul_right_left,
      Nat.mul_div_cancel_left _ (by positivity)]
  have hrJ : r ∈ Subgroup.closure ({x, y} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl rfl))
      (Subgroup.subset_closure (Or.inr rfl))
  refine ⟨w, Subgroup.pow_mem _ hrJ _, fun hw1 => hJ ?_, hwo ▸ hm, ?_⟩
  ·
    have hm1 : m = 1 := by rw [← hwo, hw1, orderOf_one]
    have hr2 : r ^ (2 ^ k) = 1 := by
      have := pow_orderOf_eq_one r
      rwa [hkm, hm1, mul_one] at this
    have hform : ∀ z ∈ Subgroup.closure ({x, y} : Set G),
        ∃ j : ℤ, z = r ^ j ∨ z = r ^ j * x := by
      intro z hz
      induction hz using Subgroup.closure_induction with
      | mem z hz =>
        rcases hz with hz | hz
        · exact ⟨0, Or.inr (by rw [hz, zpow_zero, one_mul])⟩
        · rw [Set.mem_singleton_iff] at hz
          refine ⟨-1, Or.inr ?_⟩
          rw [hz, zpow_neg_one, hr, mul_inv_rev, hxi, hyi, mul_assoc, hx, mul_one]
      | one => exact ⟨0, Or.inl (by rw [zpow_zero])⟩
      | mul a b _ _ iha ihb =>
        obtain ⟨i, hi⟩ := iha
        obtain ⟨j, hj⟩ := ihb
        rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
        · exact ⟨i + j, Or.inl (zpow_add r i j).symm⟩
        · exact ⟨i + j, Or.inr (by rw [zpow_add, mul_assoc])⟩
        · refine ⟨i - j, Or.inr ?_⟩
          calc r ^ i * x * r ^ j = r ^ i * (x * r ^ j) := by group
            _ = r ^ i * (r ^ (-j) * x) := by rw [hxrj]
            _ = r ^ (i - j) * x := by rw [← mul_assoc, ← zpow_add, sub_eq_add_neg]
        · refine ⟨i - j, Or.inl ?_⟩
          calc r ^ i * x * (r ^ j * x) = r ^ i * (x * r ^ j) * x := by group
            _ = r ^ i * (r ^ (-j) * x) * x := by rw [hxrj]
            _ = r ^ i * r ^ (-j) * (x * x) := by group
            _ = r ^ (i - j) := by rw [hx, mul_one, ← zpow_add, sub_eq_add_neg]
      | inv a _ ih =>
        obtain ⟨i, hi⟩ := ih
        rcases hi with rfl | rfl
        · exact ⟨-i, Or.inl (zpow_neg r i).symm⟩
        · refine ⟨i, Or.inr ?_⟩
          rw [mul_inv_rev, hxi, ← zpow_neg, hxrj, neg_neg]
    intro z
    obtain ⟨j, hj⟩ := hform z z.2
    rcases hj with hj | hj
    · refine ⟨k, Subtype.ext ?_⟩
      rw [Subgroup.coe_pow, hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        hr2, one_zpow, Subgroup.coe_one]
    · refine ⟨1, Subtype.ext ?_⟩
      rw [Subgroup.coe_pow, hj, pow_one, pow_two, Subgroup.coe_one]
      calc r ^ j * x * (r ^ j * x) = r ^ j * (x * r ^ j) * x := by group
        _ = r ^ j * (r ^ (-j) * x) * x := by rw [hxrj]
        _ = r ^ j * r ^ (-j) * (x * x) := by group
        _ = 1 := by rw [hx, mul_one, ← zpow_add, add_neg_cancel, zpow_zero]
  · rw [hw, ← conj_pow, hxr, inv_pow]

theorem le_Qv : V ≤ pCoreOf 2 (Subgroup.centralizer ({v} : Set G)) := by
  by_contra hVQ
  obtain ⟨x, hxV, hxQ⟩ := Set.not_subset.mp hVQ
  set H := Subgroup.centralizer ({v} : Set G) with hH
  have hxH : x ∈ H := c.V_le_T₁.trans c.T₁_le hxV
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx' : (⟨x, hxH⟩ : ↥H) ∉ CFSG.pCore 2 ↥H := by
    intro h
    apply hxQ
    rw [pCoreOf]
    exact ⟨⟨x, hxH⟩, h, rfl⟩
  rw [CFSG.BaerSuzuki.baer_suzuki_iff] at hx'
  push Not at hx'
  obtain ⟨⟨g, hg⟩, hg2⟩ := hx'
  set y := g * x * g⁻¹ with hy
  have hJ : ¬ IsPGroup 2 (Subgroup.closure ({x, y} : Set G)) := by
    intro hJ
    apply hg2
    refine (hJ.comap_subtype (K := H)).to_le ?_
    rw [Subgroup.closure_le]
    rintro z (rfl | hz)
    · exact Subgroup.subset_closure (Or.inl rfl)
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact Subgroup.subset_closure (Or.inr rfl)
  have hx2 : x * x = 1 := c.mul_self hxV
  have hy2 : y * y = 1 := by
    rw [hy]
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  obtain ⟨w, hwJ, hw1, hwo, hxw⟩ := exists_odd_of_not_isPGroup hx2 hy2 hJ
  have hwI : w ∈ Subgroup.closure (iSet V g) := by
    refine (Subgroup.closure_le _).mpr ?_ hwJ
    rintro z (rfl | hz)
    · exact Subgroup.subset_closure (Or.inl hxV)
    · rw [Set.mem_singleton_iff] at hz
      exact Subgroup.subset_closure (Or.inr ⟨x, hxV, hz⟩)
  have hwV := c.odd_mem_centralizer hg hwI hwo
  have h1 := Subgroup.mem_centralizer_iff.mp hwV x hxV
  rw [h1, mul_inv_cancel_right] at hxw
  have hw2 : w ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 1 [hxw]
    exact inv_mul_cancel w
  have h3 := orderOf_dvd_of_pow_eq_one hw2
  have h4 : orderOf w = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h3 with h | h
    · exact h
    · rw [h] at hwo
      exact absurd hwo (by decide)
  exact hw1 (orderOf_eq_one_iff.mp h4)

theorem conjClosure_comm {x : G} (hx : x ∈ conjClosure V (Subgroup.centralizer ({v} : Set G)))
    {y : G} (hy : y ∈ conjClosure V (Subgroup.centralizer ({v} : Set G))) : x * y = y * x := by
  set H := Subgroup.centralizer ({v} : Set G) with hH
  have hgen : ∀ a ∈ {z | ∃ h ∈ H, ∃ w ∈ V, h * w * h⁻¹ = z},
      ∀ b ∈ {z | ∃ h ∈ H, ∃ w ∈ V, h * w * h⁻¹ = z}, Commute a b := by
    rintro _ ⟨h, hh, w, hw, rfl⟩ _ ⟨k, hk, w', hw', rfl⟩
    have hhk : h⁻¹ * k ∈ H := H.mul_mem (H.inv_mem hh) hk
    have h1 := c.comm_of_le_Qv c.le_Qv hhk hw hw'
    show h * w * h⁻¹ * (k * w' * k⁻¹) = k * w' * k⁻¹ * (h * w * h⁻¹)
    calc h * w * h⁻¹ * (k * w' * k⁻¹) = h * (w * (h⁻¹ * k * w' * (h⁻¹ * k)⁻¹)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * k * w' * (h⁻¹ * k)⁻¹) * w) * h⁻¹ := by rw [h1]
      _ = k * w' * k⁻¹ * (h * w * h⁻¹) := by group
  have hab := Subgroup.isMulCommutative_closure (k := {z | ∃ h ∈ H, ∃ w ∈ V, h * w * h⁻¹ = z})
    fun a ha b hb _ => hgen a ha b hb
  exact congrArg Subtype.val (hab.1.comm ⟨x, hx⟩ ⟨y, hy⟩)

end Ctx

end Sec1216Gen

@[expose] def Lem1216Comp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V V₁ V₂ : Subgroup G) (n : ℕ),
    Hyp121 G T L V V₁ V₂ n → T ≤ Subgroup.normalizer (L : Set G) → ∀ v : G,
      V₁ ⊓ Subgroup.centralizer ((T ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) : Set G) =
        Subgroup.zpowers v →
      IsSylowTwoOf (T ⊓ Subgroup.normalizer (V₁ : Set G)) (Subgroup.centralizer ({v} : Set G)) →
      oddCoreIn (Subgroup.centralizer ({v} : Set G)) = ⊥ →
      ∀ K : Subgroup G, ¬ IsComponentIn K (Subgroup.centralizer ({v} : Set G))

theorem lem1216Gen_of (h1001 : Stmt10_0_1) (h331 : Stmt3_3_1) (h1211 : Lem1211) (hH91 : LemH91)
    (h1215 : Lem1215) (hComp : Lem1216Comp) : Lem1216Gen := by
  intro G _ _ T L V V₁ V₂ n hyp hTL v hv x hx y hy
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨β, hβ, -⟩ := (hH91 G T L V V₁ V₂ n hyp hTL).2
  have hSyl := (h1215 G T L V V₁ V₂ n hyp).1 v hv
  have h1212 := (lem1212_of h1001 h331 h1211) G T L V V₁ V₂ n β hyp hβ
  obtain ⟨-, hNV⟩ := Sec121Thm.normalizer_eq_of_hyp121 h1001 h331 hyp
  have hVe := Sec121Thm.isElemAbelian_of_isPrimeReduced hyp.le hyp.reduced
  have hn4 : 4 ≤ n := by rcases hyp.rank with h | h <;> omega
  have hhyp : ∀ B : Subgroup G, B ≤ V → B.relIndex V = 2 →
      Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer (V : Set G) := by
    intro B hBV hidx
    by_contra hC
    have h1 := rParam_le_mQuot hBV hC
    have h2 : mQuot V B = 1 := by
      unfold mQuot
      rw [hidx]
      exact padicValNat.self (by norm_num)
    rw [h2] at h1
    have h3 := (h1212.2 hVe).1.trans h1
    have h4 : n ≤ 1 := by exact_mod_cast h3
    omega
  have hvmem : v ∈ V₁ ⊓ Subgroup.centralizer
      ((T ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) : Set G) :=
    hv ▸ Subgroup.mem_zpowers v
  have hvV : v ∈ V := (hyp.sup ▸ le_sup_left : V₁ ≤ V) hvmem.1
  have hv1 : v ≠ 1 := by
    intro h
    apply Sec1215.inf_centralizer_ne_bot hyp hTL
    rw [hv, h, Subgroup.zpowers_one_eq_bot]
  have hT : IsSylowTwoOf T ⊤ := by
    refine ⟨le_top, hyp.sylow.1, ?_⟩
    show ¬ 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hyp.sylow.2
  have hV1 : V ≠ ⊥ := fun h => hv1 (Subgroup.mem_bot.mp (h ▸ hvV))
  have hodd := Sec1216Gen.oddCoreIn_eq_bot hyp.qtke.2.1 hT hVe (Sec1215.le_of_hyp121 hyp hTL)
    (hTL.trans hNV.ge) hV1 hhyp hvV hv1 hSyl inf_le_left
  have hHe := Sec1216Gen.charTwo_of_no_component (hComp G T L V V₁ V₂ n hyp hTL v hv hSyl hodd)
    hodd
  exact (Sec1216Gen.Ctx.mk ⟨hyp, hTL, hβ, hv⟩ hSyl hHe h1212.1).conjClosure_comm hx hy

end CFSG.Quasithin.H13
