module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommRootStandardMatrix

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace RootStandard

open Subgroup GomiFusion RootAxisTwoCore FullCenterTorus
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped commutatorElement

section Pull

variable {G : Type*} [Group G] {L : Subgroup G} {X : Type*} [Group X]

theorem pull_centralizer (φ : L ≃* X) (S : Subgroup X) :
    pull φ (centralizer (S : Set X)) = L ⊓ centralizer (pull φ S : Set G) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxL, hxC⟩ := mem_pull.mp hx
    refine ⟨hxL, mem_centralizer_iff.mpr fun y hy => ?_⟩
    obtain ⟨a, ha, rfl⟩ := exists_eq_symm_of_mem_pull hy
    have h1 := congrArg (fun z => ((φ.symm z : L) : G)) (mem_centralizer_iff.mp hxC a ha)
    simpa [map_mul] using h1
  · rintro ⟨hxL, hxC⟩
    refine mem_pull.mpr ⟨hxL, mem_centralizer_iff.mpr fun a ha => ?_⟩
    apply φ.symm.injective
    apply Subtype.ext
    simpa [map_mul] using mem_centralizer_iff.mp hxC _ (symm_mem_pull.mpr ha)

theorem pull_commutator (φ : L ≃* X) (A B : Subgroup X) :
    pull φ ⁅A, B⁆ = ⁅pull φ A, pull φ B⁆ := by
  simp only [pull, comap_equiv_eq_map_symm', Subgroup.map_commutator]

end Pull

section Root

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  (φ : L ≃* antiSp K)

local notation "𝐔[" k "]" => pull φ (rootU K k)
local notation "𝐉[" k "]" => pull φ (axisTorus K k)
local notation "𝐉" => pull φ (diagTorus K)
set_option quotPrecheck false in
local notation "𝐒[" k "]" => (⁅L ⊓ centralizer (𝐉[k] : Set G),
  L ⊓ centralizer (𝐉[k] : Set G)⁆ : Subgroup G)

@[expose] noncomputable def rootHom (k : Axis) : SL₂ K →* G :=
  L.subtype.comp (φ.symm.toMonoidHom.comp (rootSLHom K k))

theorem rootHom_apply (k : Axis) (A : SL₂ K) :
    rootHom φ k A = ((φ.symm (rootSLHom K k A) : L) : G) :=
  rfl

theorem rootHom_injective (k : Axis) : Function.Injective (rootHom φ k) := fun _ _ h =>
  rootSLHom_injective k (φ.symm.injective (Subtype.ext h))

theorem range_rootHom (k : Axis) : (rootHom φ k).range = pull φ (rootSLHom K k).range := by
  ext x
  constructor
  · rintro ⟨A, rfl⟩
    exact symm_mem_pull.mpr ⟨A, rfl⟩
  · intro hx
    obtain ⟨a, ⟨A, rfl⟩, rfl⟩ := exists_eq_symm_of_mem_pull hx
    exact ⟨A, rfl⟩

theorem CL_eq [Finite K] (hK : 2 < Nat.card K) (k : Axis) :
    L ⊓ centralizer (𝐉[k] : Set G) = 𝐉[k] ⊔ (rootHom φ k).range := by
  rw [← pull_centralizer, centralizer_axisTorus_eq hK, pull_sup, range_rootHom]

theorem S_eq [Finite K] (hK : 4 ≤ Nat.card K) (k : Axis) : 𝐒[k] = (rootHom φ k).range := by
  rw [← pull_centralizer, ← pull_commutator, commutator_centralizer_axisTorus hK, range_rootHom]

omit [CharP K 2] in
theorem J_le_CL (k : Axis) : 𝐉[k] ≤ L ⊓ centralizer (𝐉[k] : Set G) := by
  rw [← pull_centralizer]
  exact pull_mono φ (axisTorus_le_centralizer k)

omit [CharP K 2] in
theorem S_le_CL (k : Axis) : 𝐒[k] ≤ L ⊓ centralizer (𝐉[k] : Set G) :=
  commutator_le.mpr fun _ hx _ hy => mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)

omit [CharP K 2] in
theorem S_le_L (k : Axis) : 𝐒[k] ≤ L := (S_le_CL φ k).trans inf_le_left

omit [CharP K 2] in
theorem J_comm_S (k : Axis) {x y : G} (hx : x ∈ 𝐉[k]) (hy : y ∈ 𝐒[k]) : x * y = y * x :=
  mem_centralizer_iff.mp (mem_inf.mp (S_le_CL φ k hy)).2 x hx

theorem J_sup_S [Finite K] (hK : 4 ≤ Nat.card K) (k : Axis) :
    𝐉[k] ⊔ 𝐒[k] = L ⊓ centralizer (𝐉[k] : Set G) := by
  rw [S_eq φ hK, CL_eq φ (by omega)]

theorem exists_equiv_S [Finite K] (hK : 4 ≤ Nat.card K) (k : Axis) :
    ∃ e : SL₂ K ≃* ↥𝐒[k], ∀ A, (e A : G) = ((φ.symm (rootSLHom K k A) : L) : G) :=
  ⟨(MonoidHom.ofInjective (rootHom_injective φ k)).trans
    (MulEquiv.subgroupCongr (S_eq φ hK k).symm), fun _ => rfl⟩

theorem eq_one_of_comm_S [Finite K] (hK : 4 ≤ Nat.card K) (k : Axis) {s : G} (hs : s ∈ 𝐒[k])
    (hc : ∀ y ∈ 𝐒[k], s * y = y * s) : s = 1 := by
  rw [S_eq φ hK] at hs
  obtain ⟨A, rfl⟩ := hs
  have hA : A ∈ center (SL₂ K) := mem_center_iff.mpr fun B => rootHom_injective φ k (by
    rw [map_mul, map_mul]
    exact (hc _ (by rw [S_eq φ hK]; exact ⟨B, rfl⟩)).symm)
  rw [sl2_center_eq_bot, mem_bot] at hA
  rw [hA, map_one]

theorem U_le_S [Finite K] (hK : 4 ≤ Nat.card K) (k : Axis) : 𝐔[k] ≤ 𝐒[k] := by
  rw [S_eq φ hK, range_rootHom]
  exact pull_mono φ (rootU_le_range k)

omit [CharP K 2] in
theorem card_sl2 [Finite K] : Nat.card (SL₂ K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  have := Fintype.ofFinite K
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Nat.card_eq_fintype_card]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  set q := Fintype.card K
  have hq : 1 ≤ q := Fintype.card_pos
  have e : q ^ 2 - q = q * (q - 1) := by
    rw [Nat.mul_sub_one, sq]
  rw [e, ← mul_assoc, Nat.mul_div_cancel _ (by
    have : 2 ≤ q := by
      have := Fintype.one_lt_card (α := K)
      omega
    omega), mul_comm]

theorem exists_sylow_U [Finite K] {n : ℕ} (hn : 2 ≤ n) (hKn : Nat.card K = 2 ^ n) (k : Axis) :
    ∃ R : Sylow 2 ↥𝐒[k], (R : Subgroup ↥𝐒[k]).map 𝐒[k].subtype = 𝐔[k] := by
  have hK : 4 ≤ Nat.card K := by
    rw [hKn]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hUS := U_le_S φ hK k
  have hUp : IsPGroup 2 (𝐔[k].subgroupOf 𝐒[k]) := by
    refine IsPGroup.of_card (n := n) ?_
    rw [Nat.card_congr (subgroupOfEquivOfLe hUS).toEquiv, card_U, hKn]
  have hcardS : Nat.card ↥𝐒[k] = Nat.card K * (Nat.card K ^ 2 - 1) := by
    obtain ⟨e, -⟩ := exists_equiv_S φ hK k
    rw [← Nat.card_congr e.toEquiv, card_sl2]
  have hidx : (𝐔[k].subgroupOf 𝐒[k]).index = Nat.card K ^ 2 - 1 := by
    have h1 := Subgroup.card_mul_index (𝐔[k].subgroupOf 𝐒[k])
    rw [Nat.card_congr (subgroupOfEquivOfLe hUS).toEquiv, card_U, hcardS] at h1
    exact Nat.eq_of_mul_eq_mul_left (by omega) h1
  have hodd : ¬ 2 ∣ (𝐔[k].subgroupOf 𝐒[k]).index := by
    rw [hidx]
    intro h2
    have h3 : 2 ∣ Nat.card K ^ 2 := by
      rw [hKn]
      exact dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
    have h4 : Nat.card K ^ 2 = (Nat.card K ^ 2 - 1) + 1 := by
      have : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega
    rw [h4] at h3
    exact absurd ((Nat.dvd_add_right h2).mp h3) (by norm_num)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hUp.toSylow hodd, ?_⟩
  change (𝐔[k].subgroupOf 𝐒[k]).map 𝐒[k].subtype = 𝐔[k]
  rw [subgroupOf_map_subtype, inf_of_le_left hUS]

omit [CharP K 2] in
theorem J₀_le_CL (k : Axis) : 𝐉 ≤ L ⊓ centralizer (𝐉[k] : Set G) := fun _ hz =>
  ⟨pull_le φ _ hz, mem_centralizer_iff.mpr fun _ hb =>
    torus_comm (axisTorus_le_J0 k hb) hz⟩

theorem exists_torus_decomp [Finite K] (hK : 4 ≤ Nat.card K) (k : Axis) {z : G} (hz : z ∈ 𝐉) :
    ∃ b ∈ 𝐉[k], ∃ s ∈ 𝐒[k], b * s = z := by
  have hz' := J₀_le_CL φ k hz
  rw [← J_sup_S φ hK] at hz'
  exact (mem_sup_of_commute fun x hx y hy => J_comm_S φ k hx hy).mp hz'

end Root

section Centralizer

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] [Finite K]
  {n : ℕ} {t : G} (φ : L ≃* antiSp K)

local notation "𝐔[" k "]" => pull φ (rootU K k)
local notation "𝐉[" k "]" => pull φ (axisTorus K k)
set_option quotPrecheck false in
local notation "𝐒[" k "]" => (⁅L ⊓ centralizer (𝐉[k] : Set G),
  L ⊓ centralizer (𝐉[k] : Set G)⁆ : Subgroup G)
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)

omit [CharP K 2] [Finite K] in
theorem zpowers_le_centralizer_S (hS : TwoCoreSetup L K n t) (k : Axis) :
    zpowers t ≤ centralizer (𝐒[k] : Set G) :=
  fun _ hy => mem_centralizer_iff.mpr fun _ hx => (hS.zpowers_comm hy (S_le_L φ k hx)).symm

theorem centralizer_S_inf_C (hS : TwoCoreSetup L K n t) (k : Axis) :
    centralizer (𝐒[k] : Set G) ⊓ 𝐂 = (L ⊓ centralizer (𝐒[k] : Set G)) ⊔ zpowers t := by
  have hK : 4 ≤ Nat.card K := by
    rw [hS.card_K]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hS.two_le
  apply le_antisymm
  · intro x hx
    obtain ⟨hxS, hxC⟩ := mem_inf.mp hx
    have hxV : x ∈ centralizer ((zpowers t ⊔ 𝐔[k] : Subgroup G) : Set G) := by
      refine mem_centralizer_sup_iff.mpr ⟨mem_centralizer_zpowers_iff'.mpr ?_, ?_⟩
      · exact (mem_centralizer_singleton_iff.mp hxC)
      · exact mem_centralizer_iff.mpr fun u hu =>
          mem_centralizer_iff.mp hxS u (U_le_S φ hK k hu)
    obtain ⟨τ, hτ, c, hc, rfl⟩ := (hS.mem_K_iff φ k).mp hxV
    have hcL : c ∈ L := pull_le φ _ hc
    have hcS : c ∈ centralizer (𝐒[k] : Set G) := by
      have h1 := mul_mem (zpowers_le_centralizer_S φ hS k (inv_mem hτ)) hxS
      rwa [inv_mul_cancel_left] at h1
    rw [show τ * c = c * τ from hS.zpowers_comm hτ hcL]
    exact mul_mem (mem_sup_left ⟨hcL, hcS⟩) (mem_sup_right hτ)
  · refine sup_le (le_inf inf_le_right (inf_le_left.trans hS.L_le)) (le_inf
      (zpowers_le_centralizer_S φ hS k) (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)))

theorem centralizer_J_inf_centralizer_S_inf_C (hS : TwoCoreSetup L K n t) (k : Axis) :
    centralizer (𝐉[k] : Set G) ⊓ centralizer (𝐒[k] : Set G) ⊓ 𝐂 = 𝐉[k] ⊔ zpowers t := by
  have hK : 4 ≤ Nat.card K := by
    rw [hS.card_K]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hS.two_le
  apply le_antisymm
  · intro x hx
    obtain ⟨⟨hxJ, hxS⟩, hxC⟩ := hx
    have hx' : x ∈ (L ⊓ centralizer (𝐒[k] : Set G)) ⊔ zpowers t := by
      rw [← centralizer_S_inf_C φ hS k]
      exact ⟨hxS, hxC⟩
    obtain ⟨c, hc, τ, hτ, rfl⟩ := (mem_sup_of_commute fun x hx y hy =>
      (hS.zpowers_comm hy (mem_inf.mp hx).1).symm).mp hx'
    have hcJ : c ∈ centralizer (𝐉[k] : Set G) := by
      have h1 : τ⁻¹ ∈ centralizer (𝐉[k] : Set G) := mem_centralizer_iff.mpr fun _ hb =>
        (hS.zpowers_comm (inv_mem hτ) (pull_le φ _ hb)).symm
      have h2 := mul_mem hxJ h1
      rwa [mul_inv_cancel_right] at h2
    have hcCL : c ∈ 𝐉[k] ⊔ 𝐒[k] := by
      rw [J_sup_S φ hK]
      exact ⟨(mem_inf.mp hc).1, hcJ⟩
    obtain ⟨b, hb, s, hs, rfl⟩ := (mem_sup_of_commute fun x hx y hy =>
      J_comm_S φ k hx hy).mp hcCL
    have hs1 : s = 1 := by
      refine eq_one_of_comm_S φ hK k hs fun y hy => ?_
      have h1 := mem_centralizer_iff.mp (mem_inf.mp hc).2 y hy
      have h2 := J_comm_S φ k hb hy
      have h3 : b * (s * y) = b * (y * s) :=
        calc b * (s * y) = y * (b * s) := by rw [← mul_assoc, h1]
          _ = b * y * s := by rw [← mul_assoc, h2]
          _ = b * (y * s) := mul_assoc _ _ _
      exact mul_left_cancel h3
    rw [hs1, mul_one]
    exact mul_mem (mem_sup_left hb) (mem_sup_right hτ)
  · refine sup_le (le_inf (le_inf ?_ ?_) ?_) (le_inf (le_inf ?_ (zpowers_le_centralizer_S φ hS k))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)))
    · exact (J_le_CL φ k).trans inf_le_right
    · exact fun x hx => mem_centralizer_iff.mpr fun y hy => (J_comm_S φ k hx hy).symm
    · exact (pull_le φ _).trans hS.L_le
    · exact fun _ hy => mem_centralizer_iff.mpr fun _ hx =>
        (hS.zpowers_comm hy (pull_le φ _ hx)).symm

omit [CharP K 2] [Finite K] in
theorem J_inf_zpowers (hS : TwoCoreSetup L K n t) (k : Axis) : 𝐉[k] ⊓ zpowers t = ⊥ := by
  rw [inf_comm]
  exact hS.zpowers_inf (pull_le φ _)

omit [CharP K 2] [Finite K] in
theorem conj_mem_S (hS : TwoCoreSetup L K n t) (k : Axis) {g : G}
    (hg : g ∈ centralizer (𝐉[k] : Set G) ⊓ 𝐂) {s : G} (hs : s ∈ 𝐒[k]) :
    g * s * g⁻¹ ∈ 𝐒[k] := by
  obtain ⟨hgJ, hgC⟩ := mem_inf.mp hg
  have hgL := hS.cent_le hgC
  have hCL : (L ⊓ centralizer (𝐉[k] : Set G)).map (MulAut.conj g).toMonoidHom =
      L ⊓ centralizer (𝐉[k] : Set G) := by
    apply le_antisymm
    · rintro _ ⟨x, ⟨hxL, hxJ⟩, rfl⟩
      refine ⟨(mem_normalizer_iff.mp hgL x).mp hxL, mem_centralizer_iff.mpr fun b hb => ?_⟩
      have h1 : Commute b g := mem_centralizer_iff.mp hgJ b hb
      have h2 : Commute b x := mem_centralizer_iff.mp hxJ b hb
      exact ((h1.mul_right h2).mul_right h1.inv_right).eq
    · intro x hx
      refine ⟨g⁻¹ * x * g, ⟨?_, mem_centralizer_iff.mpr fun b hb => ?_⟩, by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group⟩
      · have := (mem_normalizer_iff.mp (inv_mem hgL) x).mp hx.1
        rwa [inv_inv] at this
      · have h1 : Commute b g := mem_centralizer_iff.mp hgJ b hb
        have h2 : Commute b x := mem_centralizer_iff.mp hx.2 b hb
        exact ((h1.inv_right.mul_right h2).mul_right h1).eq
  have hmem : g * s * g⁻¹ ∈ 𝐒[k].map (MulAut.conj g).toMonoidHom := ⟨s, hs, rfl⟩
  rwa [Subgroup.map_commutator, hCL] at hmem

end Centralizer

end RootStandard

end CFSG.LocalAnalysis.SymplecticFourStandard
