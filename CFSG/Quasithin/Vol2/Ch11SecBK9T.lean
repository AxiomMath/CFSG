module

public import CFSG.Quasithin.Vol2.Ch11SecBK9S
public import CFSG.Quasithin.Vol2.Ch11SecBK7P

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Assembly.LowTwoRank (StatedSp)
open scoped IsMulCommutative

namespace K9

variable {G : Type} [Group G]

theorem conj_eq_of_card_two {L V : Subgroup G} {z : G}
    (hzu : ∀ w ∈ V ⊓ Subgroup.centralizer (L : Set G), w ≠ 1 → w = z)
    (hz : z ∈ V ⊓ Subgroup.centralizer (L : Set G)) (hz1 : z ≠ 1) {x : G}
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) (hxL : x ∈ Subgroup.normalizer (L : Set G)) :
    x⁻¹ * z * x = z := by
  apply hzu
  · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxV) z).mp hz.1
      rwa [inv_inv] at h
    · rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hl' : x * l * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hxL l).mp hl
      have hc := Subgroup.mem_centralizer_iff.mp hz.2 _ hl'
      calc l * (x⁻¹ * z * x) = x⁻¹ * ((x * l * x⁻¹) * z) * x := by group
        _ = x⁻¹ * (z * (x * l * x⁻¹)) * x := by rw [hc]
        _ = x⁻¹ * z * x * l := by group
  · intro h
    apply hz1
    calc z = x * (x⁻¹ * z * x) * x⁻¹ := by group
      _ = 1 := by rw [h]; group

end K9

theorem factSp4FourExt_holds : FactSp4FourExt := by
  intro G _ _ L V T hV hLV hVL hnat hk hZ2 hCL hTS hTV hTL
  refine ⟨K7.not_le_centralizer_sp4 (n := 2) le_rfl hLV hnat hk hTS hTV hTL, ?_⟩
  intro U hUV hU hUC
  obtain ⟨_, K, _, _, _, hK, π, f, hf, -, -⟩ :=
    K7.exists_coord_sp4 (n := 2) le_rfl hLV hnat hk hTS hTL
  have hK4 : Nat.card K = 4 := by
    rw [hK]
    norm_num
  have hsq : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hV.2 w w.2)
  have hV2 : IsPGroup 2 ↥V := fun w => ⟨1, by rw [pow_one]; exact hsq w⟩
  obtain ⟨z, hz1, hzu⟩ :=
    (Nat.card_eq_two_iff' (1 : ↥(V ⊓ Subgroup.centralizer (L : Set G)))).mp hZ2
  have hzu' : ∀ w ∈ V ⊓ Subgroup.centralizer (L : Set G), w ≠ 1 → w = (z : G) :=
    fun w hw hw1 => congrArg Subtype.val (hzu ⟨w, hw⟩ fun h => hw1 (congrArg Subtype.val h))
  have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hmemZ : ∀ w : ↥V, w ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V ↔
      w = 1 ∨ w = ⟨(z : G), z.2.1⟩ := by
    intro w
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hw
      by_cases hw1 : w = 1
      · exact Or.inl hw1
      · exact Or.inr (Subtype.ext (hzu' w ⟨w.2, hw⟩ fun h => hw1 (Subtype.ext h)))
    · rintro (rfl | rfl)
      · exact Subgroup.one_mem _
      · exact z.2.2
  have hU2 : (U.subgroupOf V).index = 2 := by
    have h := E3.relIndex_eq_two_pow hV2 U
    rw [hU, pow_one] at h
    exact h
  have hzU : (⟨(z : G), z.2.1⟩ : ↥V) ∉ U.subgroupOf V := fun h => hz1' (by
    have hm : (z : G) ∈ U ⊓ Subgroup.centralizer (L : Set G) := ⟨h, z.2.2⟩
    rw [hUC, Subgroup.mem_bot] at hm
    exact hm)
  let C : K9.CovData K ↥V :=
    { H := autOn L V
      Z := (Subgroup.centralizer (L : Set G)).subgroupOf V
      π := π
      f := f
      coord := hf
      z := ⟨(z : G), z.2.1⟩
      memZ := hmemZ
      z_ne := fun h => hz1' (congrArg Subtype.val h)
      sq := hsq
      fixZ := K7.fix_of_autOn
      U₀ := U.subgroupOf V
      index₀ := hU2
      z_not_mem₀ := hzU }
  have hcomm : commV C.H = ⊤ := K7.commV_autOn_eq_top hLV hVL
  obtain ⟨Ψ, hΨ⟩ := C.exists_psi hK4 hcomm
  have hbij : Function.Bijective π := ⟨hf.injective_nat, hf.onto⟩
  have hCpi : ∀ γ, C.pi' γ = ((π γ : ↥(autOn L V)) : MulAut ↥V) := fun _ => rfl
  have hxz : ∀ x ∈ L ⊔ T, x⁻¹ * ((C.z : ↥V) : G) * x = C.z := fun x hx =>
    K9.conj_eq_of_card_two hzu' z.2 hz1' (sup_le hLV hTV hx)
      (sup_le Subgroup.le_normalizer hTL hx)
  exact ⟨K9.isMaxSubgroupIn_of_cov hK4 hLV hbij C hCpi hΨ hUV rfl hTV hTL hxz,
    K9.relIndex_ne_two_of_cov hK4 hLV hbij C hCpi hΨ hUV rfl,
    K9.exists_three_of_cov hK4 hLV hbij C hCpi hΨ hUV rfl z.2.2 hCL⟩

end CFSG.Quasithin.Vol2.Ch11.SecB
