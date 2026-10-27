module

public import CFSG.Quasithin.H13.A6S1372L76N3m
public import CFSG.Quasithin.H13.A6S1372L76Of4
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Quot
public import CFSG.Quasithin.H13.A6S1372L76N3h

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace A6L76N3

theorem s1_s2_facts :
    SL3.InX1 SL3.s2 ∧ ¬ SL3.InX2 SL3.s2 ∧ SL3.InX2 SL3.s1 ∧ ¬ SL3.InX1 SL3.s1 := by
  decide +kernel

theorem exists_seven : ∃ s : SL3.S, s ^ 7 = 1 ∧ s ≠ 1 := by
  decide +kernel

theorem pow_eight_of_mem_P0 {g : SL3.S} (hg : g ∈ SL3.P0) : g ^ 8 = 1 := by
  have h := Subgroup.orderOf_dvd_natCard SL3.P0 hg
  rw [SL3.card_P0] at h
  exact orderOf_dvd_iff_pow_eq_one.1 h

theorem mem_of_odd_of_le {Y A : Subgroup SL3.S} (hYe : ∀ g ∈ Y, g ^ 24 = 1)
    (hconj : ∀ a ∈ Y, ∀ b ∈ Y, a ^ 3 = 1 → a ≠ 1 → b ^ 3 = 1 →
      b = 1 ∨ ∃ h ∈ Y, b = h * a * h⁻¹ ∨ b = h * a⁻¹ * h⁻¹)
    (hYA : Y ≤ Subgroup.normalizer (A : Set SL3.S)) {a : SL3.S} (ha : a ∈ A) (haY : a ∈ Y)
    (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) {b : SL3.S} (hbY : b ∈ Y) (hb : Odd (orderOf b)) : b ∈ A := by
  have hb3 : b ^ 3 = 1 := cube_of_odd (hYe b hbY) hb
  rcases hconj a haY b hbY ha3 ha1 hb3 with h | ⟨h, hh, e | e⟩
  · rw [h]
    exact A.one_mem
  · rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hYA hh) a).mp ha
  · rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hYA hh) a⁻¹).mp (A.inv_mem ha)

theorem x1_conj : ∀ a ∈ SL3.X1, ∀ b ∈ SL3.X1, a ^ 3 = 1 → a ≠ 1 → b ^ 3 = 1 →
    b = 1 ∨ ∃ h ∈ SL3.X1, b = h * a * h⁻¹ ∨ b = h * a⁻¹ * h⁻¹ :=
  fun a ha b hb ha3 ha1 hb3 => (x1_three_conj a b ha hb ha3 ha1 hb3).imp_right
    fun ⟨h, hh, e⟩ => ⟨h, hh, e⟩

theorem x2_conj : ∀ a ∈ SL3.X2, ∀ b ∈ SL3.X2, a ^ 3 = 1 → a ≠ 1 → b ^ 3 = 1 →
    b = 1 ∨ ∃ h ∈ SL3.X2, b = h * a * h⁻¹ ∨ b = h * a⁻¹ * h⁻¹ :=
  fun a ha b hb ha3 ha1 hb3 => (x2_three_conj a b ha hb ha3 ha1 hb3).imp_right
    fun ⟨h, hh, e⟩ => ⟨h, hh, e⟩

theorem odd_mem_of_overgroups {A B : Subgroup SL3.S} (hAB : A ≤ B)
    (hPA : SL3.P0 ≤ Subgroup.normalizer (A : Set SL3.S))
    {a : SL3.S} (ha : a ∈ A) (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (hB : B ⊔ SL3.P0 ≠ ⊤)
    {b : SL3.S} (hb : b ∈ B) (hodd : Odd (orderOf b)) : b ∈ A := by
  obtain ⟨h12, h22, h21, h11⟩ := s1_s2_facts
  have hYN : A ⊔ SL3.P0 ≤ Subgroup.normalizer (A : Set SL3.S) := sup_le Subgroup.le_normalizer hPA
  have hY : A ⊔ SL3.P0 ≤ B ⊔ SL3.P0 := sup_le_sup_right hAB _
  have haY : a ∈ A ⊔ SL3.P0 := Subgroup.mem_sup_left ha
  have hbY : b ∈ B ⊔ SL3.P0 := Subgroup.mem_sup_left hb
  have hP0X1 : SL3.P0 ≤ SL3.X1 := inf_le_left
  have hP0X2 : SL3.P0 ≤ SL3.X2 := inf_le_right
  rcases SL3.overgroups_SL3 (A ⊔ SL3.P0) le_sup_right with h | h | h | h
  · exfalso
    rw [h] at haY
    exact ha1 (eq_one_of_pow_two_pow (j := 3) (by simpa using pow_eight_of_mem_P0 haY) ha3
      (by decide))
  · rcases SL3.overgroups_SL3 (B ⊔ SL3.P0) le_sup_right with h' | h' | h' | h'
    · exfalso
      have hs : SL3.s2 ∈ B ⊔ SL3.P0 := hY (h ▸ (h12 : SL3.s2 ∈ SL3.X1))
      rw [h'] at hs
      exact h22 (hP0X2 hs)
    · rw [h] at hYN haY
      rw [h'] at hbY
      exact mem_of_odd_of_le (fun g hg => x1_pow_24 g hg) x1_conj hYN ha haY ha3 ha1 hbY hodd
    · exfalso
      have hs : SL3.s2 ∈ B ⊔ SL3.P0 := hY (h ▸ (h12 : SL3.s2 ∈ SL3.X1))
      rw [h'] at hs
      exact h22 hs
    · exact absurd h' hB
  · rcases SL3.overgroups_SL3 (B ⊔ SL3.P0) le_sup_right with h' | h' | h' | h'
    · exfalso
      have hs : SL3.s1 ∈ B ⊔ SL3.P0 := hY (h ▸ (h21 : SL3.s1 ∈ SL3.X2))
      rw [h'] at hs
      exact h11 (hP0X1 hs)
    · exfalso
      have hs : SL3.s1 ∈ B ⊔ SL3.P0 := hY (h ▸ (h21 : SL3.s1 ∈ SL3.X2))
      rw [h'] at hs
      exact h11 hs
    · rw [h] at hYN haY
      rw [h'] at hbY
      exact mem_of_odd_of_le (fun g hg => x2_pow_24 g hg) x2_conj hYN ha haY ha3 ha1 hbY hodd
    · exact absurd h' hB
  · exact absurd (top_le_iff.1 (h ▸ hY)) hB

theorem sup_P0_ne_top {B : Subgroup SL3.S} (hPB : SL3.P0 ≤ Subgroup.normalizer (B : Set SL3.S))
    (hB : ∀ b ∈ B, ∃ k : ℕ, b ^ (18 * 2 ^ k) = 1) : B ⊔ SL3.P0 ≠ ⊤ := by
  intro h
  have hS : IsSimpleGroup SL3.S := A6L76A.isSimpleGroup_sl (le_refl 3) (by simp)
  have hN : B.Normal := by
    have hle : (⊤ : Subgroup SL3.S) ≤ Subgroup.normalizer (B : Set SL3.S) :=
      h ▸ sup_le Subgroup.le_normalizer hPB
    exact ⟨fun n hn g => (Subgroup.mem_normalizer_iff.mp (hle (Subgroup.mem_top g)) n).mp hn⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal B with h1 | h1
  · rw [h1, bot_sup_eq] at h
    have h2 := congrArg (fun X : Subgroup SL3.S => Nat.card X) h
    simp only [SL3.card_P0, Subgroup.card_top, SL3.card_S] at h2
    norm_num at h2
  · obtain ⟨s, hs7, hs1⟩ := exists_seven
    obtain ⟨k, hk⟩ := hB s (h1 ▸ Subgroup.mem_top s)
    have h1 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hs7) (orderOf_dvd_of_pow_eq_one hk)
    have h2 : Nat.gcd 7 (18 * 2 ^ k) = 1 :=
      Nat.Coprime.mul_right (by norm_num) (Nat.Coprime.pow_right _ (by norm_num))
    rw [h2, Nat.dvd_one, orderOf_eq_one_iff] at h1
    exact hs1 h1

theorem mem_of_odd_of_mul_QH {G : Type} [Group G] [Finite G] {H K : Subgroup G}
    (hK : K ∈ cComp H) {k q : G} (hk : k ∈ K) (hq : q ∈ pCoreOf 2 H)
    (hodd : Odd (orderOf (k * q))) : k * q ∈ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hqN : q ∈ Subgroup.normalizer (K : Set G) := P134.pCoreOf_le_normalizer_of_mem_cComp hK hq
  obtain ⟨a, ha⟩ := pCoreOf_isPGroup 2 H ⟨q, hq⟩
  have hqa : q ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  obtain ⟨k', hk', he⟩ := U3.pow_mem_mul_of_normalizes' hk hqN (2 ^ a)
  rw [hqa, mul_one] at he
  have hcop : Nat.Coprime (2 ^ a) (orderOf (k * q)) := (Odd.coprime_two_left hodd).pow_left a
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm, he]
  exact K.pow_mem hk' m

end A6L76N3

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem exists_X1375_c012_cube :
    ∃ x₀ : ↥(Subgroup.normalizer (V : Set G)), (x₀ : G) ∈ S.X1375 ∧
      S.frame.ρ x₀ = swap 0 1 * swap 1 2 ∧ (x₀ : G) ^ 3 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have P := S.plusData_X1375
  obtain ⟨g, hgX, hg⟩ := S.exists_X1375_c012
  have h3 : ((g ^ 3 : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ pCoreOf 2 S.X1375 :=
    P.mem_pCoreOf_of_K4 (by simpa using S.X1375.pow_mem hgX 3)
      (by rw [map_pow, hg, c012_facts.2.2]; decide)
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 S.X1375 ⟨_, h3⟩
  have hk' : ((g : G) ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine ⟨g ^ 4 ^ k, by simpa using S.X1375.pow_mem hgX (4 ^ k), ?_, ?_⟩
  · rw [map_pow, hg, pow_four_pow_of_cube c012_facts.2.2]
  · have e : (4 : ℕ) ^ k = 2 ^ k * 2 ^ k := by
      rw [← mul_pow]
      norm_num
    simp only [SubgroupClass.coe_pow]
    rw [← pow_mul, mul_comm, pow_mul, e, pow_mul, hk', one_pow]

theorem X1375_decomp {x₀ : ↥(Subgroup.normalizer (V : Set G))}
    (hx₀ : (x₀ : G) ∈ S.X1375) (hρ : S.frame.ρ x₀ = swap 0 1 * swap 1 2) {x : G}
    (hx : x ∈ S.X1375) :
    x ∈ pCoreOf 2 S.X1375 ∨ (x₀ : G) * x₀ * x ∈ pCoreOf 2 S.X1375 ∨
      (x₀ : G) * x ∈ pCoreOf 2 S.X1375 := by
  have P := S.plusData_X1375
  obtain ⟨xn, rfl⟩ : ∃ xn : ↥(Subgroup.normalizer (V : Set G)), (xn : G) = x :=
    ⟨⟨x, P.le_NV hx⟩, rfl⟩
  obtain ⟨h4, h5, hs⟩ := P.rho hx
  rcases (a4At_all _ h4 h5 hs).1 with h | h | h
  · exact Or.inl (P.mem_pCoreOf_of_K4 hx h)
  · refine Or.inr (Or.inl ?_)
    exact P.mem_pCoreOf_of_K4 (x := x₀ * x₀ * xn)
      (S.X1375.mul_mem (S.X1375.mul_mem hx₀ hx₀) hx) (by rw [map_mul, map_mul, hρ]; exact h)
  · refine Or.inr (Or.inr ?_)
    exact P.mem_pCoreOf_of_K4 (x := x₀ * xn) (S.X1375.mul_mem hx₀ hx)
      (by rw [map_mul, hρ]; exact h)

theorem L1_le_oTwoUpper : S.L1 ≤ oTwoUpper S.L1 := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨hx, m, hm, hxm⟩
  exact Subgroup.subset_closure ⟨Subgroup.subset_closure ⟨hx, m, hm, hxm⟩,
    Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hxm)⟩

section Act

variable {H : Subgroup G} (hH : H ∈ S.Hz) [IsMulCommutative ↥(conjClosure S.V3 H)]
  {K : Subgroup G} (hK : K ∈ cComp H)
include hH hK

theorem secAct_mem_normalizer (h : ↥(H ⊓ Subgroup.normalizer (K : Set G))) :
    A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 hH) ⟨h, h.2.1⟩ ∈
      Subgroup.normalizer ((autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) :
          Subgroup (MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))) :
        Set (MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))) := by
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHV := S.le_normalizer_UV1 hH
  have hKH : K ≤ H := le_of_mem_cComp hK
  have key : ∀ x : ↥H, (x : G) ∈ Subgroup.normalizer (K : Set G) →
      ∀ y ∈ autSec (autOn K (conjClosure S.V3 H)) ⊤ ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)),
        A6Mod.secAct hHU hHV x * y * (A6Mod.secAct hHU hHV x)⁻¹ ∈
          autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) := by
    intro x hx y hy
    obtain ⟨f, hfK, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHV hKH).1 hy
    refine (A6Mod.mem_autSec_iff hHU hHV hKH).2
      ⟨x * f * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx f).mp hfK, ?_⟩
    rw [map_mul, map_mul, map_inv]
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key _ h.2.2 y, fun hy => ?_⟩
  have h2 := key (⟨h, h.2.1⟩ : ↥H)⁻¹ (Subgroup.inv_mem _ h.2.2) _ hy
  have e : (A6Mod.secAct hHU hHV ⟨h, h.2.1⟩)⁻¹ * (A6Mod.secAct hHU hHV ⟨h, h.2.1⟩ * y *
      (A6Mod.secAct hHU hHV ⟨h, h.2.1⟩)⁻¹) * (A6Mod.secAct hHU hHV ⟨h, h.2.1⟩)⁻¹⁻¹ = y := by
    group
  rwa [map_inv, e] at h2

@[expose] noncomputable def secActN : ↥(H ⊓ Subgroup.normalizer (K : Set G)) →*
    ↥(Subgroup.normalizer ((autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) :
          Subgroup (MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))) :
        Set (MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))))) :=
  ((A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 hH)).comp
    (Subgroup.inclusion inf_le_left)).codRestrict _ (S.secAct_mem_normalizer hH hK)

end Act

end Setting4

end CFSG.Quasithin.H13.A6
