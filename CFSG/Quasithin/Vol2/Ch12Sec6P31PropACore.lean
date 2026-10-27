module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31WA
public import CFSG.Milestones.ASVolI.A3Aut.Core
public import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin.H13.P31A

open scoped Pointwise commutatorElement
open CFSG.Open

variable {X : Type} [Group X]

theorem mem_sup_centralizer_of_outer_eq_one {K : Subgroup X} [K.Normal] {x : X}
    (hx : (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥K))
      (MulAut.conjNormal (H := K) x) = 1) :
    x ∈ K ⊔ Subgroup.centralizer (K : Set X) := by
  obtain ⟨k, hk⟩ := (QuotientGroup.eq_one_iff (MulAut.conjNormal (H := K) x)).mp hx
  have hφ : MulAut.conjNormal (H := K) ((k : X)⁻¹ * x) = 1 := by
    rw [map_mul, map_inv, MulAut.conjNormal_val, ← hk, inv_mul_cancel]
  have hmem : (k : X)⁻¹ * x ∈ Subgroup.centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := congrArg (fun α : MulAut ↥K => ((α ⟨y, hy⟩ : ↥K) : X)) hφ
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    have h2 : ((k : X)⁻¹ * x) * y = y * ((k : X)⁻¹ * x) := by
      calc ((k : X)⁻¹ * x) * y
          = (((k : X)⁻¹ * x) * y * ((k : X)⁻¹ * x)⁻¹) * ((k : X)⁻¹ * x) := by group
        _ = y * ((k : X)⁻¹ * x) := by rw [h1]
    exact h2.symm
  have hx' : x = (k : X) * ((k : X)⁻¹ * x) := by group
  rw [hx']
  exact Subgroup.mul_mem_sup k.2 hmem

theorem commutator_mem_sup_centralizer_of_isCyclic_outer {K : Subgroup X} [K.Normal]
    (hcyc : IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K)) (a b : X) :
    a * b * a⁻¹ * b⁻¹ ∈ K ⊔ Subgroup.centralizer (K : Set X) := by
  let ψ : X →* CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥K)).comp
      (MulAut.conjNormal (H := K))
  have hcomm : ∀ u v : CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K,
      u * v = v * u := by
    haveI : IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K) := hcyc
    have := (IsCyclic.isMulCommutative
      (α := CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K)).is_comm.comm
    exact fun u v => this u v
  have hψ : ψ (a * b * a⁻¹ * b⁻¹) = 1 := by
    have e : a * b * a⁻¹ * b⁻¹ = ⁅a, b⁆ := by rw [commutatorElement_def]
    rw [e, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm (ψ a) (ψ b)
  exact mem_sup_centralizer_of_outer_eq_one hψ


theorem mem_zpowers_or_mem_zpowers_of_isPGroup {Γ : Type*} [Group Γ] [Finite Γ] [IsCyclic Γ]
    {p : ℕ} (hp : p.Prime) {g h : Γ}
    (hg : ∃ i : ℕ, orderOf g = p ^ i) (hh : ∃ j : ℕ, orderOf h = p ^ j) :
    g ∈ Subgroup.zpowers h ∨ h ∈ Subgroup.zpowers g := by
  obtain ⟨i, hi⟩ := hg
  obtain ⟨j, hj⟩ := hh
  have hmem : ∀ {x y : Γ}, orderOf x ∣ orderOf y → x ∈ Subgroup.zpowers y := by
    intro x y hxy
    have hle : Subgroup.zpowers x ≤ Subgroup.zpowers y :=
      (IsCyclic.subgroup_le_iff_card_dvd).mpr (by
        rw [Nat.card_zpowers, Nat.card_zpowers]
        exact hxy)
    exact hle (Subgroup.mem_zpowers x)
  rcases le_total i j with hij | hji
  · exact Or.inl (hmem (by rw [hi, hj]; exact Nat.pow_dvd_pow p hij))
  · exact Or.inr (hmem (by rw [hj, hi]; exact Nat.pow_dvd_pow p hji))

theorem exists_pow_mul_inv_mem_sup_centralizer {K : Subgroup X} [K.Normal] [Finite X]
    (hcyc : IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K)) {p : ℕ}
    (hp : p.Prime) {a b : X} (ha : ∃ m : ℕ, a ^ p ^ m = 1) (hb : ∃ m : ℕ, b ^ p ^ m = 1) :
    (∃ k : ℕ, a ^ k * b⁻¹ ∈ K ⊔ Subgroup.centralizer (K : Set X)) ∨
      ∃ k : ℕ, b ^ k * a⁻¹ ∈ K ⊔ Subgroup.centralizer (K : Set X) := by
  haveI : Finite ↥K := Subtype.finite
  classical
  haveI : Finite (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K) := inferInstance
  haveI : IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K) := hcyc
  let ψ : X →* CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥K)).comp
      (MulAut.conjNormal (H := K))
  have hψa : ∃ i : ℕ, orderOf (ψ a) = p ^ i := by
    obtain ⟨m, hm⟩ := ha
    have h : (ψ a) ^ (p ^ m) = 1 := by rw [← map_pow, hm, map_one]
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one h)
    exact ⟨i, hi⟩
  have hψb : ∃ j : ℕ, orderOf (ψ b) = p ^ j := by
    obtain ⟨m, hm⟩ := hb
    have h : (ψ b) ^ (p ^ m) = 1 := by rw [← map_pow, hm, map_one]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one h)
    exact ⟨j, hj⟩
  rcases mem_zpowers_or_mem_zpowers_of_isPGroup (Γ :=
      CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K) hp hψa hψb with hmem | hmem
  ·
    rw [(isOfFinOrder_of_finite (ψ b)).mem_zpowers_iff_mem_range_orderOf] at hmem
    obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hmem
    refine Or.inr ⟨k, ?_⟩
    refine mem_sup_centralizer_of_outer_eq_one (K := K) ?_
    change ψ (b ^ k * a⁻¹) = 1
    rw [map_mul, map_pow, hk, map_inv, mul_inv_cancel]
  ·
    rw [(isOfFinOrder_of_finite (ψ a)).mem_zpowers_iff_mem_range_orderOf] at hmem
    obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hmem
    refine Or.inl ⟨k, ?_⟩
    refine mem_sup_centralizer_of_outer_eq_one (K := K) ?_
    change ψ (a ^ k * b⁻¹) = 1
    rw [map_mul, map_pow, hk, map_inv, mul_inv_cancel]

theorem pRank_add_pRank_le_of_commute {p : ℕ} [Finite X] (hp : p.Prime) {A B : Subgroup X}
    (hdisj : A ⊓ B = ⊥) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    CFSG.Open.pRank p A + CFSG.Open.pRank p B ≤ CFSG.Open.pRank p (A ⊔ B) := by
  obtain ⟨EA, hEAA, hEA, hEAcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt A
  obtain ⟨EB, hEBB, hEB, hEBcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt B
  have hdisj' : EA ⊓ EB = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hx' : x ∈ A ⊓ B := ⟨hEAA hx.1, hEBB hx.2⟩
    rwa [hdisj, Subgroup.mem_bot] at hx'
  have hsup : IsElemAbelian p (EA ⊔ EB) :=
    hEA.sup_of_commute hEB (fun a ha b hb => hcomm a (hEAA ha) b (hEBB hb))
  have hcard : Nat.card ↥(EA ⊔ EB) =
      p ^ (CFSG.Open.pRank p A + CFSG.Open.pRank p B) := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute EA EB
      (fun a ha b hb => hcomm a (hEAA ha) b (hEBB hb))).1
    rw [hdisj'] at h
    simp only [Subgroup.card_bot, mul_one] at h
    rw [hEAcard, hEBcard, ← pow_add] at h
    exact h
  exact CFSG.SectionRank.le_pRank hp.one_lt
    (sup_le (hEAA.trans le_sup_left) (hEBB.trans le_sup_right)) hsup hcard

theorem inf_centralizer_eq_bot_of_center_eq_bot {K : Subgroup X}
    (hZ : Subgroup.center ↥K = ⊥) :
    K ⊓ Subgroup.centralizer (K : Set X) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hzc : (⟨z, hz.1⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hz.2 (k : X) k.2)
  rw [hZ, Subgroup.mem_bot] at hzc
  exact congrArg Subtype.val hzc

theorem commutator_le_pCoreOf_of_burnsideAut_SolvBorel {K L T : Subgroup X} [K.Normal]
    [Finite X] (hSB : CFSG.ASVolI.burnsideAut_SolvBorel ↥K ((T ⊓ K).subgroupOf K))
    (hTL : T ≤ Subgroup.normalizer (L : Set X)) (hLK : L ≤ K)
    (hT2 : IsPGroup 2 T) (hLsolv : Group.IsSolvable ↥L) :
    ⁅L, T ⊓ K⁆ ≤ pCoreOf 2 L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U : Subgroup X := T ⊓ K with hU
  have hU2 : IsPGroup 2 U := hT2.to_le inf_le_left
  have hUK : U ≤ K := inf_le_right
  have hUN : U ≤ Subgroup.normalizer (L : Set X) := inf_le_left.trans hTL
  have hUsolv : Group.IsSolvable ↥U := CFSG.Quasithin.F1.isSolvable_of_isPGroup_two hU2
  have hsolv : Group.IsSolvable ↥(L ⊔ U) :=
    CFSG.Quasithin.F1.isSolvable_sup_of_le_normalizer hLsolv hUsolv hUN
  have hLVK : L ⊔ U ≤ K := sup_le hLK hUK
  let Y : Subgroup ↥K := (L ⊔ U).subgroupOf K
  have hYsolv : Group.IsSolvable ↥Y :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hLVK).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hLVK).injective
  have hSY : (T ⊓ K).subgroupOf K ≤ Y := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hx))
  have hnormY : Y ≤ Subgroup.normalizer ((T ⊓ K).subgroupOf K : Set ↥K) :=
    hSB Y hSY hYsolv
  have hLN : L ≤ Subgroup.normalizer (U : Set X) := by
    intro l hl
    have hmem : (⟨l, hLK hl⟩ : ↥K) ∈
        (Subgroup.normalizer (U : Set X)).subgroupOf K := by
      rw [Subgroup.subgroupOf_normalizer_eq (H := U) (N := K) hUK]
      exact hnormY (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hl))
    exact Subgroup.mem_subgroupOf.mp hmem
  have hNleU : ⁅L, U⁆ ≤ U := by
    rw [Subgroup.commutator_le]
    intro l hl u hu
    have h1 : l * u * l⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hLN hl) u).mp hu
    have e : ⁅l, u⁆ = (l * u * l⁻¹) * u⁻¹ := by rw [commutatorElement_def]
    rw [e]
    exact U.mul_mem h1 (U.inv_mem hu)
  have hNle : ⁅L, U⁆ ≤ L := by
    rw [Subgroup.commutator_le]
    intro l hl u hu
    have h1 : u * l * u⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hUN hu) l).mp hl
    have h2 : u * l * u⁻¹ * l⁻¹ ∈ L := L.mul_mem h1 (L.inv_mem hl)
    rw [commutatorElement_def]
    have e : l * u * l⁻¹ * u⁻¹ = (u * l * u⁻¹ * l⁻¹)⁻¹ := by group
    rw [e]
    exact L.inv_mem h2
  have hNLU : L ⊔ U ≤ Subgroup.normalizer ((⁅L, U⁆ : Subgroup X) : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.commutator_le_sup L U)).mp
      (CFSG.commutator_normal_in_sup L U)
  have hLNn : L ≤ Subgroup.normalizer ((⁅L, U⁆ : Subgroup X) : Set X) := le_sup_left.trans hNLU
  have hN2 : IsPGroup 2 ↥(⁅L, U⁆ : Subgroup X) := hU2.to_le hNleU
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNle hLNn hN2

theorem sylow_inf_sup_centralizer_eq {K T : Subgroup X} [K.Normal] [Finite X]
    (hKC : K ⊓ Subgroup.centralizer (K : Set X) = ⊥)
    (hT2 : IsPGroup 2 T)
    (hTmax : ∀ S : Subgroup X, IsPGroup 2 S → T ≤ S → S = T) :
    T ⊓ (K ⊔ Subgroup.centralizer (K : Set X)) =
      (T ⊓ K) ⊔ (T ⊓ Subgroup.centralizer (K : Set X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : (Subgroup.centralizer (K : Set X)).Normal := Subgroup.normal_centralizer
  set C : Subgroup X := Subgroup.centralizer (K : Set X) with hC
  set W : Subgroup X := K ⊔ C with hW
  haveI hWn : W.Normal := Subgroup.sup_normal K C
  have hcomm : ∀ k ∈ K, ∀ c ∈ C, k * c = c * k := by
    intro k hk c hc
    exact Subgroup.mem_centralizer_iff.mp hc k hk
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ := by
    obtain ⟨S, hTS⟩ := hT2.exists_le_sylow
    have hST : (S : Subgroup X) = T := hTmax S S.isPGroup' hTS
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, hT2, ?_⟩
    rw [← hST]
    simpa [Subgroup.relIndex_top_right] using S.not_dvd_index
  have hWsyl : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ W) W := by
    refine hTsyl.inf_of_le_normalizer (N := W) le_top ?_
    rw [Subgroup.normalizer_eq_top_iff.mpr hWn]
  have hmax : ∀ S : Subgroup X, S ≤ W → IsPGroup 2 S → T ⊓ W ≤ S → S = T ⊓ W := by
    intro S hSW hS2 hle
    have hSsub : (T ⊓ W).subgroupOf W ≤ S.subgroupOf W := by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hle (Subgroup.mem_subgroupOf.mp hx))
    obtain ⟨Q, hQ⟩ := hWsyl.exists_sylow_eq_subgroupOf
    have hS2' : IsPGroup 2 (S.subgroupOf W) := hS2.comap_subtype
    have hle' : (Q : Subgroup W) ≤ S.subgroupOf W := by
      rw [hQ]
      exact hSsub
    have heq : S.subgroupOf W = (Q : Subgroup W) := Q.3 hS2' hle'
    have heq' : S.subgroupOf W = (T ⊓ W).subgroupOf W := by rw [heq, hQ]
    calc S = (S.subgroupOf W).map W.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hSW).symm
      _ = ((T ⊓ W).subgroupOf W).map W.subtype := by rw [heq']
      _ = T ⊓ W := Subgroup.map_subgroupOf_eq_of_le inf_le_right
  have hmain := sylow_inter_prod (K := K) (C := C) (T := T ⊓ W) hKC hcomm
    (hT2.to_le inf_le_left) inf_le_right hmax
  have hKW : K ≤ W := le_sup_left
  have hCW : C ≤ W := le_sup_right
  simpa [W, C, inf_assoc, inf_eq_left.mpr hKW, inf_eq_left.mpr hCW] using hmain

theorem false_of_action_mod {R O T W : Subgroup X}
    (hOR : O ≤ R) (hOn : ∀ r ∈ R, ∀ o ∈ O, r * o * r⁻¹ ∈ O)
    (hTR : T ≤ Subgroup.normalizer (R : Set X))
    (hTO : T ≤ Subgroup.normalizer (O : Set X))
    (htriv : ∀ s ∈ T ⊓ W, ∀ r ∈ R, s * r * s⁻¹ * r⁻¹ ∈ O)
    {t₁ t₂ : X} (ht₁ : t₁ ∈ T) (ht₂ : t₂ ∈ T)
    (hchain : (∃ k : ℕ, t₁ ^ k * t₂⁻¹ ∈ W) ∨ (∃ k : ℕ, t₂ ^ k * t₁⁻¹ ∈ W))
    {x y : X} (hx : x ∈ R) (hy : y ∈ R)
    (h₁ : t₁ * x * t₁⁻¹ * x ∈ O) (h₂ : t₂ * x * t₂⁻¹ * y⁻¹ ∈ O)
    (h₃ : t₂ * y * t₂⁻¹ * x⁻¹ ∈ O)
    (hx₂ : x ^ 2 ∉ O) (hyx : y * x ∉ O) (hyx' : y * x⁻¹ ∉ O) : False := by
  let Eqv : X → X → Prop := fun a b => a * b⁻¹ ∈ O
  have hrefl : ∀ a : X, Eqv a a := by
    intro a
    change a * a⁻¹ ∈ O
    rw [mul_inv_cancel]
    exact O.one_mem
  have hsymm : ∀ {a b : X}, Eqv a b → Eqv b a := by
    intro a b hab
    change b * a⁻¹ ∈ O
    have h := O.inv_mem hab
    simpa [mul_inv_rev] using h
  have htrans : ∀ {a b c : X}, Eqv a b → Eqv b c → Eqv a c := by
    intro a b c hab hbc
    change a * c⁻¹ ∈ O
    have h := O.mul_mem hab hbc
    simpa [mul_assoc] using h
  have hinv : ∀ {a b : X}, a ∈ R → Eqv a b → Eqv a⁻¹ b⁻¹ := by
    intro a b ha hab
    show a⁻¹ * (b⁻¹)⁻¹ ∈ O
    have h1 : b * a⁻¹ ∈ O := by
      have h := O.inv_mem hab
      simpa [mul_inv_rev] using h
    have h2 : a⁻¹ * (b * a⁻¹) * a ∈ O := by
      simpa using hOn a⁻¹ (R.inv_mem ha) (b * a⁻¹) h1
    simpa [mul_assoc] using h2
  have hconj : ∀ {a b : X}, Eqv a b → ∀ t ∈ T, Eqv (t * a * t⁻¹) (t * b * t⁻¹) := by
    intro a b hab t ht
    change (t * a * t⁻¹) * (t * b * t⁻¹)⁻¹ ∈ O
    have e : (t * a * t⁻¹) * (t * b * t⁻¹)⁻¹ = t * (a * b⁻¹) * t⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hTO ht) (a * b⁻¹)).mp hab
  have hconjR : ∀ t ∈ T, ∀ r ∈ R, t * r * t⁻¹ ∈ R := by
    intro t ht r hr
    exact (Subgroup.mem_normalizer_iff.mp (hTR ht) r).mp hr
  have hxinv : Eqv (t₁ * x * t₁⁻¹) x⁻¹ := by simpa [Eqv] using h₁
  have hxy : Eqv (t₂ * x * t₂⁻¹) y := by simpa [Eqv] using h₂
  have hyxEq : Eqv (t₂ * y * t₂⁻¹) x := by simpa [Eqv] using h₃
  have hx_ne : ¬ Eqv x x⁻¹ := by
    intro h
    exact hx₂ (by simpa [Eqv, pow_two] using h)
  have hy_ne_x : ¬ Eqv y x := by
    intro h
    exact hyx' (by simpa [Eqv] using h)
  have hy_ne_xinv : ¬ Eqv y x⁻¹ := by
    intro h
    exact hyx (by simpa [Eqv] using h)
  have hxinv' : Eqv (t₁ * x⁻¹ * t₁⁻¹) x := by
    have ha : t₁ * x * t₁⁻¹ ∈ R := hconjR t₁ ht₁ x hx
    have h := hinv ha hxinv
    simpa [mul_inv_rev, mul_assoc] using h
  have hparity : ∀ (t a b : X), t ∈ T → Eqv (t * a * t⁻¹) b → Eqv (t * b * t⁻¹) a →
      (∀ m : ℕ, Eqv (t ^ (2 * m) * a * (t ^ (2 * m))⁻¹) a) ∧
        (∀ m : ℕ, Eqv (t ^ (2 * m + 1) * a * (t ^ (2 * m + 1))⁻¹) b) := by
    intro t a b ht hab hba
    have hsq : Eqv (t ^ 2 * a * (t ^ 2)⁻¹) a := by
      have e : t ^ 2 * a * (t ^ 2)⁻¹ = t * (t * a * t⁻¹) * t⁻¹ := by
        simp only [pow_two, mul_inv_rev]
        group
      rw [e]
      exact htrans (hconj hab t ht) hba
    have hiter : ∀ m : ℕ, Eqv ((t ^ 2) ^ m * a * ((t ^ 2) ^ m)⁻¹) a := by
      intro m
      induction m with
      | zero => simpa using hrefl a
      | succ m ih =>
          have e : (t ^ 2) ^ (m + 1) * a * ((t ^ 2) ^ (m + 1))⁻¹ =
              (t ^ 2) * ((t ^ 2) ^ m * a * ((t ^ 2) ^ m)⁻¹) * (t ^ 2)⁻¹ := by
            rw [pow_succ]
            group
          rw [e]
          exact htrans (hconj ih (t ^ 2) (T.pow_mem ht 2)) hsq
    have hbiter : ∀ m : ℕ, Eqv ((t ^ 2) ^ m * b * ((t ^ 2) ^ m)⁻¹) b := by
      intro m
      set u : X := (t ^ 2) ^ m with hu
      have huT : u ∈ T := by
        rw [hu]
        exact T.pow_mem (T.pow_mem ht 2) m
      have hut : u * t = t * u := by
        rw [hu]
        exact (((Commute.refl t).pow_left 2).pow_left m).eq
      have htinv : t⁻¹ * u⁻¹ = u⁻¹ * t⁻¹ := by
        calc t⁻¹ * u⁻¹ = (u * t)⁻¹ := (mul_inv_rev u t).symm
          _ = (t * u)⁻¹ := by rw [hut]
          _ = u⁻¹ * t⁻¹ := mul_inv_rev t u
      have h1 : Eqv (u * (t * a * t⁻¹) * u⁻¹) (t * a * t⁻¹) := by
        have e : u * (t * a * t⁻¹) * u⁻¹ = t * (u * a * u⁻¹) * t⁻¹ := by
          calc u * (t * a * t⁻¹) * u⁻¹
              = (u * t) * a * (t⁻¹ * u⁻¹) := by group
            _ = (t * u) * a * (u⁻¹ * t⁻¹) := by rw [hut, htinv]
            _ = t * (u * a * u⁻¹) * t⁻¹ := by group
        rw [e]
        exact hconj (hiter m) t ht
      have h2 : Eqv (u * b * u⁻¹) b :=
        htrans (htrans (hsymm (hconj hab u huT)) h1) hab
      simpa [hu] using h2
    refine ⟨?_, ?_⟩
    · intro m
      simpa [pow_mul] using hiter m
    · intro m
      have e : t ^ (2 * m + 1) * a * (t ^ (2 * m + 1))⁻¹ =
          (t ^ 2) ^ m * (t * a * t⁻¹) * ((t ^ 2) ^ m)⁻¹ := by
        rw [pow_succ, pow_mul]
        group
      rw [e]
      exact htrans (hconj hab ((t ^ 2) ^ m) (T.pow_mem (T.pow_mem ht 2) m)) (hbiter m)
  have hpar₁ := hparity t₁ x x⁻¹ ht₁ hxinv hxinv'
  have hpar₂ := hparity t₂ x y ht₂ hxy hyxEq
  rcases hchain with ⟨k, hk⟩ | ⟨k, hk⟩
  ·
    set s : X := t₂ * (t₁ ^ k)⁻¹ with hsdef
    have hsT : s ∈ T := T.mul_mem ht₂ (T.inv_mem (T.pow_mem ht₁ k))
    have hsW : s ∈ W := by
      have h := W.inv_mem hk
      simpa [s, mul_inv_rev] using h
    have hs : s ∈ T ⊓ W := ⟨hsT, hsW⟩
    have hrR : t₁ ^ k * x * (t₁ ^ k)⁻¹ ∈ R :=
      hconjR _ (T.pow_mem ht₁ k) x hx
    have htr := htriv s hs (t₁ ^ k * x * (t₁ ^ k)⁻¹) hrR
    have h2' : Eqv (t₂ * x * t₂⁻¹) (t₁ ^ k * x * (t₁ ^ k)⁻¹) := by
      have e : t₂ * x * t₂⁻¹ = s * (t₁ ^ k * x * (t₁ ^ k)⁻¹) * s⁻¹ := by
        simp [s, mul_assoc]
      rw [e]
      exact htr
    have hyEq : Eqv y (t₁ ^ k * x * (t₁ ^ k)⁻¹) := htrans (hsymm hxy) h2'
    rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · exact hy_ne_x (htrans hyEq
        (by simpa [show m + m = 2 * m by omega] using hpar₁.1 m))
    · exact hy_ne_xinv (htrans hyEq
        (by simpa [show m + m + 1 = 2 * m + 1 by omega] using hpar₁.2 m))
  ·
    set s : X := t₁ * (t₂ ^ k)⁻¹ with hsdef
    have hsT : s ∈ T := T.mul_mem ht₁ (T.inv_mem (T.pow_mem ht₂ k))
    have hsW : s ∈ W := by
      have h := W.inv_mem hk
      simpa [s, mul_inv_rev] using h
    have hs : s ∈ T ⊓ W := ⟨hsT, hsW⟩
    have hrR : t₂ ^ k * x * (t₂ ^ k)⁻¹ ∈ R :=
      hconjR _ (T.pow_mem ht₂ k) x hx
    have htr := htriv s hs (t₂ ^ k * x * (t₂ ^ k)⁻¹) hrR
    have h1' : Eqv (t₁ * x * t₁⁻¹) (t₂ ^ k * x * (t₂ ^ k)⁻¹) := by
      have e : t₁ * x * t₁⁻¹ = s * (t₂ ^ k * x * (t₂ ^ k)⁻¹) * s⁻¹ := by
        simp [s, mul_assoc]
      rw [e]
      exact htr
    rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · have hxEq : Eqv (t₁ * x * t₁⁻¹) x :=
        htrans h1' (by simpa [show m + m = 2 * m by omega] using hpar₂.1 m)
      exact hx_ne (htrans (hsymm hxEq) hxinv)
    · have hxEq : Eqv (t₁ * x * t₁⁻¹) y :=
        htrans h1' (by simpa [show m + m + 1 = 2 * m + 1 by omega] using hpar₂.2 m)
      exact hy_ne_xinv (htrans (hsymm hxEq) hxinv)

theorem false_of_propA {K L₁ T : Subgroup X} [K.Normal] [Finite X]
    (hcyc : IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K))
    (hZ : Subgroup.center ↥K = ⊥)
    (hSB : CFSG.ASVolI.burnsideAut_SolvBorel ↥K ((T ⊓ K).subgroupOf K))
    (hK3 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥K))
    (hX3 : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2)
    (hT2 : IsPGroup 2 T) (hTmax : ∀ S : Subgroup X, IsPGroup 2 S → T ≤ S → S = T)
    (hTL : T ≤ Subgroup.normalizer (L₁ : Set X)) (hL₁solv : Group.IsSolvable ↥L₁)
    (hL₁T : ⁅L₁, T⁆ = L₁)
    (hL₁gen : L₁ = Subgroup.closure {x : X | x ∈ L₁ ∧ ∃ k : ℕ, x ^ (3 ^ k) = 1})
    {x y t₁ t₂ : X} (hx : x ∈ L₁) (hy : y ∈ L₁) (ht₁ : t₁ ∈ T) (ht₂ : t₂ ∈ T)
    (h₁ : t₁ * x * t₁⁻¹ * x ∈ pCoreOf 2 L₁) (h₂ : t₂ * x * t₂⁻¹ * y⁻¹ ∈ pCoreOf 2 L₁)
    (h₃ : t₂ * y * t₂⁻¹ * x⁻¹ ∈ pCoreOf 2 L₁)
    (hx₂ : x ^ 2 ∉ pCoreOf 2 L₁) (hyx : y * x ∉ pCoreOf 2 L₁)
    (hyx' : y * x⁻¹ ∉ pCoreOf 2 L₁) : False := by
  let C : Subgroup X := Subgroup.centralizer (K : Set X)
  let W : Subgroup X := K ⊔ C
  have hKC : K ⊓ C = ⊥ := inf_centralizer_eq_bot_of_center_eq_bot hZ
  have hcomm : ∀ k ∈ K, ∀ c ∈ C, k * c = c * k := by
    intro k hk c hc
    exact Subgroup.mem_centralizer_iff.mp hc k hk
  have hK3' : 2 ≤ CFSG.Open.pRank 3 K := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) (G := X) (H := K)]
    exact hK3
  have hKle : CFSG.Open.pRank 3 K ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
    CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) le_top
  have hKeq : CFSG.Open.pRank 3 K = 2 := le_antisymm (hKle.trans hX3) hK3'
  have hXeq : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 :=
    le_antisymm hX3 (hK3'.trans hKle)
  have hrank : CFSG.Open.pRank 3 K + CFSG.Open.pRank 3 C ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
    (pRank_add_pRank_le_of_commute Nat.prime_three hKC hcomm).trans
      (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) le_top)
  have hL₁sup : L₁ ≤ W := by
    have h := le_sup_centralizer_of_out_comm (X := ⊤)
      (fun a _ b _ => by
        simpa [C] using commutator_mem_sup_centralizer_of_isCyclic_outer hcyc a b)
      le_top le_top hL₁T
    simpa [W, C] using h
  obtain ⟨-, hL₁K⟩ := le_of_threeRank hKC hcomm hrank hKeq hXeq hL₁sup hL₁gen
  have hstep3 : ⁅L₁, T ⊓ K⁆ ≤ pCoreOf 2 L₁ :=
    commutator_le_pCoreOf_of_burnsideAut_SolvBorel hSB hTL hL₁K hT2 hL₁solv
  have hstep4 : T ⊓ W = (T ⊓ K) ⊔ (T ⊓ C) :=
    sylow_inf_sup_centralizer_eq hKC hT2 hTmax
  have htriv : ∀ s ∈ T ⊓ W, ∀ r ∈ L₁, s * r * s⁻¹ * r⁻¹ ∈ pCoreOf 2 L₁ := by
    intro s hs r hr
    have hDnorm : T ⊓ C ≤ Subgroup.normalizer (T ⊓ K : Set X) :=
      (inf_le_right : T ⊓ C ≤ C).trans
        (le_normalizer_of_comm (K := K) (C := C) (H := T ⊓ K) inf_le_right hcomm)
    have hset : (((T ⊓ K) ⊔ (T ⊓ C) : Subgroup X) : Set X) =
        ((T ⊓ K : Subgroup X) : Set X) * ((T ⊓ C : Subgroup X) : Set X) :=
      Subgroup.coe_mul_of_right_le_normalizer_left (T ⊓ K) (T ⊓ C) hDnorm
    have hs' : s ∈ ((T ⊓ K) ⊔ (T ⊓ C) : Subgroup X) := hstep4 ▸ hs
    have hs'' : s ∈ ((T ⊓ K : Subgroup X) : Set X) * ((T ⊓ C : Subgroup X) : Set X) := by
      rw [← hset]
      exact hs'
    obtain ⟨u, hu, c, hc, huc⟩ := Set.mem_mul.mp hs''
    have huK : u ∈ K := (inf_le_right : T ⊓ K ≤ K) hu
    have hcC : c ∈ C := (inf_le_right : T ⊓ C ≤ C) hc
    have hcr : c * r = r * c :=
      (Subgroup.mem_centralizer_iff.mp hcC r (hL₁K hr)).symm
    have hcu : c * u = u * c := (Subgroup.mem_centralizer_iff.mp hcC u huK).symm
    have key : (u * c) * r * (u * c)⁻¹ * r⁻¹ = u * r * u⁻¹ * r⁻¹ := by
      calc (u * c) * r * (u * c)⁻¹ * r⁻¹
          = u * (c * r) * c⁻¹ * u⁻¹ * r⁻¹ := by group
        _ = u * (r * c) * c⁻¹ * u⁻¹ * r⁻¹ := by rw [hcr]
        _ = u * r * u⁻¹ * r⁻¹ := by group
    rw [← huc, key]
    have hmem : ⁅r, u⁆ ∈ pCoreOf 2 L₁ :=
      hstep3 (Subgroup.commutator_mem_commutator hr hu)
    have hmem' : ⁅u, r⁆ ∈ pCoreOf 2 L₁ := by
      simpa [commutatorElement_inv] using (pCoreOf 2 L₁).inv_mem hmem
    simpa [commutatorElement_def] using hmem'
  have hOn : ∀ r ∈ L₁, ∀ o ∈ pCoreOf 2 L₁, r * o * r⁻¹ ∈ pCoreOf 2 L₁ := by
    intro r hr o ho
    have hN : r ∈ Subgroup.normalizer (pCoreOf 2 L₁ : Set X) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L₁ hr
    exact (Subgroup.mem_normalizer_iff.mp hN o).mp ho
  have hTO : T ≤ Subgroup.normalizer (pCoreOf 2 L₁ : Set X) :=
    hTL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L₁)
  have hpow (t : X) (ht : t ∈ T) : ∃ m : ℕ, t ^ 2 ^ m = 1 := by
    obtain ⟨m, hm⟩ := hT2 ⟨t, ht⟩
    exact ⟨m, by simpa using congrArg Subtype.val hm⟩
  have hchain := exists_pow_mul_inv_mem_sup_centralizer (K := K) hcyc
    (p := 2) Nat.prime_two (hpow t₁ ht₁) (hpow t₂ ht₂)
  exact false_of_action_mod (R := L₁) (O := pCoreOf 2 L₁) (T := T) (W := W)
    (CFSG.openPCoreOf_le 2 L₁) hOn hTL hTO htriv ht₁ ht₂ hchain hx hy
    h₁ h₂ h₃ hx₂ hyx hyx'

end CFSG.Quasithin.H13.P31A
