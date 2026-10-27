module

public import CFSG.Quasithin.Vol2.Ch4Sec2Lem4212B
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.Quasithin.H13.Ch4.G443J4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem exists_mul_mem_centralizer {K : Subgroup G}
    (hout : ∀ α : MulAut ↥K, ∃ g : ↥K, α = MulAut.conj g) {y : G}
    (hy : y ∈ Subgroup.normalizer (K : Set G)) :
    ∃ k ∈ K, k⁻¹ * y ∈ Subgroup.centralizer (K : Set G) := by
  have hmap : K.map (MulAut.conj y).toMonoidHom = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hy
  let α : MulAut ↥K := ((MulAut.conj y).subgroupMap K).trans (MulEquiv.subgroupCongr hmap)
  obtain ⟨g, hg⟩ := hout α
  refine ⟨g, g.2, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
  have h1 := congrArg (fun φ : MulAut ↥K => ((φ ⟨x, hx⟩ : ↥K) : G)) hg
  have h2 : ((α ⟨x, hx⟩ : ↥K) : G) = y * x * y⁻¹ := rfl
  rw [h2] at h1
  have h3 : y * x * y⁻¹ = (g : G) * x * (g : G)⁻¹ := by simpa [MulAut.conj_apply] using h1
  calc x * ((g : G)⁻¹ * y) = (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) * y := by group
    _ = (g : G)⁻¹ * (y * x * y⁻¹) * y := by rw [h3]
    _ = (g : G)⁻¹ * y * x := by group

variable [Finite G]

theorem perfectCore_eq_of_inner {H K : Subgroup G} (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hKp : ⁅K, K⁆ = K)
    (hout : ∀ α : MulAut ↥K, ∃ g : ↥K, α = MulAut.conj g)
    (hC : Odd (Nat.card ↥(H ⊓ Subgroup.centralizer (K : Set G)))) : perfectCore H = K := by
  have hKY : K ≤ perfectCore H := le_perfectCore_of_perfect hKH hKp
  refine le_antisymm ?_ hKY
  set Y := perfectCore H with hY
  have hYH : Y ≤ H := perfectCore_le H
  set X := Y ⊓ Subgroup.centralizer (K : Set G) with hX
  have hXs : Group.IsSolvable ↥X := by
    have hodd : Odd (Nat.card ↥X) := Odd.of_dvd_nat hC
      (Subgroup.card_dvd_of_le (inf_le_inf_right _ hYH))
    exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hXW : perfectCore X ≤ K := by
    rw [(isSolvable_iff_perfectCore_eq_bot X).mp hXs]
    exact bot_le
  refine L4212.le_of_perfect_of_le_sup (perfectCore_perfect H) hKY (hYH.trans hHK) inf_le_left
    (fun y hy => ?_) hXW
  obtain ⟨k, hk, hc⟩ := exists_mul_mem_centralizer hout (hHK (hYH hy))
  have hcY : k⁻¹ * y ∈ Y := Y.mul_mem (Y.inv_mem (hKY hk)) hy
  have e : y = k * (k⁻¹ * y) := by group
  rw [e, sup_comm]
  exact Subgroup.mul_mem_sup hk ⟨hcY, hc⟩

omit [Finite G] in
theorem le_centralizer_of_le_normalizer {K B : Subgroup G} (hK : IsSimpleGroup ↥K)
    (hKp : ⁅K, K⁆ = K) (hKB : K ≤ Subgroup.normalizer (B : Set G))
    (hBK : B ≤ Subgroup.normalizer (K : Set G)) (hBc : IsMulCommutative ↥B) :
    K ≤ Subgroup.centralizer (B : Set G) := by
  have hn : ((K ⊓ B).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun k hk =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hk, hKB hk⟩
  have hKB1 : K ⊓ B = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((K ⊓ B).subgroupOf K) with h | h
    · rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hx.1⟩ : ↥K) ∈ (K ⊓ B).subgroupOf K := hx
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    · exfalso
      have hab : ⁅K, K⁆ = ⊥ := by
        rw [eq_bot_iff, Subgroup.commutator_le]
        intro a ha b hb
        have ha'' : (⟨a, ha⟩ : ↥K) ∈ (K ⊓ B).subgroupOf K := h ▸ Subgroup.mem_top _
        have hb'' : (⟨b, hb⟩ : ↥K) ∈ (K ⊓ B).subgroupOf K := h ▸ Subgroup.mem_top _
        have ha' : a ∈ B := ha''.2
        have hb' : b ∈ B := hb''.2
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
        exact congrArg Subtype.val (hBc.is_comm.comm ⟨a, ha'⟩ ⟨b, hb'⟩)
      rw [hKp] at hab
      have := hK.toNontrivial
      obtain ⟨x, hx⟩ := exists_ne (1 : ↥K)
      have h1 : (x : G) ∈ (⊥ : Subgroup G) := by
        rw [← hab]
        exact x.2
      exact hx (Subtype.ext (Subgroup.mem_bot.mp h1))
  have hc : ⁅K, B⁆ ≤ K ⊓ B :=
    le_inf (Subgroup.le_normalizer_iff_commutator_le_left.mp hBK)
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hKB)
  rw [hKB1, le_bot_iff] at hc
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have := Subgroup.commutator_mem_commutator hk hb
  rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
  exact this.symm

omit [Finite G] in
theorem conjClosure_le_oTwoUpper {B T : Subgroup G} (hB : Odd (Nat.card B)) :
    conjClosure B T ≤ oTwoUpper (conjClosure B T) := by
  refine CFSG.Quasithin.conjClosure_le fun t ht b hb => mem_oTwoUpper_of_odd
    (mem_conjClosure ht hb) ?_
  rw [← SemiconjBy.orderOf_eq t (x := b) (y := t * b * t⁻¹)
    (show t * b = t * b * t⁻¹ * t by group)]
  exact Odd.of_dvd_nat hB (Subgroup.orderOf_dvd_natCard B hb)

theorem le_normalizer_conjClosure_of_mem {B T Y P : Subgroup G} (hB : Odd (Nat.card B))
    (hP2 : IsPGroup 2 ↥P) (hPX : P ≤ Subgroup.normalizer (conjClosure B T : Set G))
    (hYP : Y ≤ Subgroup.normalizer (P : Set G))
    (hcomm : ∀ y ∈ Y, ∀ t ∈ T, ∀ b ∈ B, y * (t * b * t⁻¹) * y⁻¹ * (t * b * t⁻¹)⁻¹ ∈ P) :
    Y ≤ Subgroup.normalizer (conjClosure B T : Set G) := by
  set X := conjClosure B T with hX
  have hO : oTwoUpper (X ⊔ P) = X :=
    le_antisymm (L4212.oTwoUpper_sup_le hPX hP2)
      ((conjClosure_le_oTwoUpper hB).trans (oTwoUpper_mono le_sup_left))
  intro y hy
  have hW : y ∈ Subgroup.normalizer ((X ⊔ P : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hP' : P.map (MulAut.conj y).toMonoidHom = P :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hYP hy)
    have hle : (X ⊔ P).map (MulAut.conj y).toMonoidHom ≤ X ⊔ P := by
      rw [Subgroup.map_sup, hP']
      refine sup_le ?_ le_sup_right
      rw [Subgroup.map_le_iff_le_comap]
      refine conjClosure_le fun t ht b hb => ?_
      show (MulAut.conj y).toMonoidHom (t * b * t⁻¹) ∈ X ⊔ P
      have e : (MulAut.conj y).toMonoidHom (t * b * t⁻¹) =
          (y * (t * b * t⁻¹) * y⁻¹ * (t * b * t⁻¹)⁻¹) * (t * b * t⁻¹) := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e, sup_comm]
      exact Subgroup.mul_mem_sup (hcomm y hy t ht b hb) (mem_conjClosure ht hb)
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj y).injective]
  have := normalizer_le_normalizer_oTwoUpper _ hW
  rwa [hO] at this

end CFSG.Quasithin.H13.Ch4.G443J4
