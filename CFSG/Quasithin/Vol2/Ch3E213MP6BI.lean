module

public import CFSG.Quasithin.Vol2.Ch3E213MP6BH
public import CFSG.Quasithin.Vol2.Ch3E213MP6CK
public import CFSG.Quasithin.Vol2.Ch3E213MP6BG

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.Open CFSG.QuasithinUnique B6
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp uElt antiUnipotent
  antiUnipotentCenter minorAut)
open CFSG.Quasithin.SteinbergBS (rootLong rootShort upper_of_mem_normalizer
  mem_normalizer_of_conj_mul_pow map_eq_of_map_le)

variable {G : Type} [Group G] [Finite G] {H T M V K : Subgroup G}
  {k : Type} [Field k] [Finite k] [CharP k 2]

namespace P6B

omit [Finite G] in
theorem mem_coordIn_of_swap (D : Sp4Data H T M V K k) {s : ↥H ⧸ kerIn (M.subgroupOf H) ⊤}
    (hs : s ∈ barIn M H T) {e : MulAut (antiSp k)} (hact : ∀ x, D.θ (D.ι s x) = e (D.θ x))
    {X : Subgroup G} (hTX : T ≤ Subgroup.normalizer (X : Set G)) :
    ∀ w ∈ coordIn D.θ X, e w ∈ coordIn D.θ X := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨D.ι s x, ?_, by
    change D.θ (D.ι s x) = e (D.θ x)
    exact hact x⟩
  change ((D.ι s x : ↥(kZero H M)) : ↥H ⧸ kerIn (M.subgroupOf H) ⊤) ∈ barIn M H X
  rw [D.ι_apply]
  obtain ⟨t, ht, rfl⟩ := hs
  have hx' : (x : ↥H ⧸ kerIn (M.subgroupOf H) ⊤) ∈ barIn M H X := hx
  obtain ⟨y, hy, hyx⟩ := hx'
  rw [← hyx]
  have ht' : (t : G) ∈ T := Subgroup.mem_subgroupOf.mp ht
  have hy' : (y : G) ∈ X := Subgroup.mem_subgroupOf.mp hy
  refine ⟨t * y * t⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp⟩
  simpa using (Subgroup.mem_normalizer_iff.mp (hTX ht') _).mp hy'

theorem swap_data (hS : Setting H T M V K) (D : Sp4Data H T M V K k) :
    ∃ (h : antiSp k) (r : ℕ), IsUpper h ∧
      ∀ w ∈ coordIn D.θ V, (MulAut.conj h * minorAut k ^ (2 * r + 1)) w ∈ coordIn D.θ V := by
  obtain ⟨s, hs, h, j, hj, hact, -⟩ := D.swap
  obtain ⟨r, rfl⟩ := hj
  have hU : ∀ u ∈ antiUnipotent k,
      (MulAut.conj h * minorAut k ^ (2 * r + 1)) u ∈ antiUnipotent k := by
    rw [← D.sylow]
    exact mem_coordIn_of_swap D hs hact Subgroup.le_normalizer
  have hUeq : (antiUnipotent k).map (MulAut.conj h * minorAut k ^ (2 * r + 1)).toMonoidHom =
      antiUnipotent k :=
    map_eq_of_map_le (by rintro _ ⟨u, hu, rfl⟩; exact hU u hu) le_rfl
  exact ⟨h, r, upper_of_mem_normalizer (mem_normalizer_of_conj_mul_pow hUeq),
    mem_coordIn_of_swap D hs hact hS.hyp.normal_T⟩

omit [Finite G] in
theorem spansCenter_coordIn (D : Sp4Data H T M V K k)
    (hμ : ∀ μ : k, μ ≠ 0 → ¬ coordIn D.θ V ≤ zLine 1 μ) : SpansCenter (coordIn D.θ V) := by
  intro α β hαβ hle
  by_cases hα : α = 0
  · apply D.V_not_le_short
    intro w hw
    obtain ⟨t, ht⟩ := hle hw
    exact ⟨t * β, by rw [ht, hα, mul_zero]⟩
  · by_cases hβ : β = 0
    · apply D.V_not_le_long
      intro w hw
      obtain ⟨t, ht⟩ := hle hw
      exact ⟨t * α, by rw [ht, hβ, mul_zero]⟩
    · refine hμ (β / α) (div_ne_zero hβ hα) fun w hw => ?_
      obtain ⟨t, ht⟩ := hle hw
      refine ⟨t * α, ?_⟩
      rw [ht]
      congr 1
      · field_simp
      · ring

theorem four_le_card_coordIn (hS : Setting H T M V K) (D : Sp4Data H T M V K k) :
    4 ≤ Nat.card (coordIn D.θ V) := by
  rw [coordIn, Subgroup.card_map_of_injective D.θ.injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe D.V_le).toEquiv, D.card_V]
  exact hS.four_le

end P6B

theorem pkgSp4C2W
    (hG41 : FactSp4TransvW)
    (hCTwo : FactSp4CTwo) : PkgSp4C2 := by
  intro G _ _ H T M V K hS _ _ hB k _ _ _ n hn hk D hl hμ
  obtain ⟨h, r, hh, hσ⟩ := P6B.swap_data hS D
  have hsp := P6B.spansCenter_coordIn D hμ
  rcases P6B.exists_member_or_suzuki hG41 hCTwo hn hk D.V_le_center hl hsp hh hσ with
    ⟨F₀, c, g, hc, hgY, hY⟩ | ⟨F₀, a, ha, hcard, d, hd, hW⟩
  · obtain ⟨g', hg'⟩ := exists_sp4Member_of_subfieldSp hS hB D hc hgY hY
    exact e213Concl_of_sp4Member hg'
  · obtain ⟨Y, g, hgY, hY, hSyl, hcore, hO2, hO2B, hexact, hstar⟩ :=
      P6B.exists_sz_member D.V_le_center (P6B.four_le_card_coordIn hS D) ha hcard hd hW
    exact e213Concl_of_coord_member hS hB D hgY hY hSyl hcore hO2 hO2B hexact hstar

end CFSG.Quasithin.Ch3E213M
