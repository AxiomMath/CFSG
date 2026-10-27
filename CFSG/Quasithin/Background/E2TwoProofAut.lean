module

public import CFSG.Quasithin.Background.E2TwoProofFactor
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2P

theorem exists_mul_of_mem_sup_of_commute {G : Type*} [Group G] {A B : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, a * b = x}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, mul_one 1⟩
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
        refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
        have h := hAB a₂ ha₂ b₁ hb₁
        calc a₁ * a₂ * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by group
          _ = a₁ * (b₁ * a₂) * b₂ := by rw [h]
          _ = a₁ * b₁ * (a₂ * b₂) := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        rw [mul_inv_rev]
        exact hAB a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb) }
  have hle : A ⊔ B ≤ S := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, mul_one a⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, one_mul b⟩)
  exact hle hx

theorem exists_mul_of_mem_sup_of_le_normalizer {G : Type*} [Group G] {N T : Subgroup G}
    (hT : T ≤ Subgroup.normalizer (N : Set G)) {x : G} (hx : x ∈ N ⊔ T) :
    ∃ n ∈ N, ∃ t ∈ T, n * t = x := by
  let S : Subgroup G :=
    { carrier := {x | ∃ n ∈ N, ∃ t ∈ T, n * t = x}
      one_mem' := ⟨1, N.one_mem, 1, T.one_mem, mul_one 1⟩
      mul_mem' := by
        rintro _ _ ⟨n₁, hn₁, t₁, ht₁, rfl⟩ ⟨n₂, hn₂, t₂, ht₂, rfl⟩
        have h := (Subgroup.mem_normalizer_iff.mp (hT ht₁) n₂).mp hn₂
        refine ⟨n₁ * (t₁ * n₂ * t₁⁻¹), N.mul_mem hn₁ h, t₁ * t₂, T.mul_mem ht₁ ht₂, ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨n, hn, t, ht, rfl⟩
        have h := (Subgroup.mem_normalizer_iff.mp (hT (T.inv_mem ht)) n⁻¹).mp (N.inv_mem hn)
        refine ⟨t⁻¹ * n⁻¹ * t⁻¹⁻¹, h, t⁻¹, T.inv_mem ht, ?_⟩
        group }
  have hle : N ⊔ T ≤ S := sup_le (fun n hn => ⟨n, hn, 1, T.one_mem, mul_one n⟩)
    (fun t ht => ⟨1, N.one_mem, t, ht, one_mul t⟩)
  exact hle hx

section Inner

variable {Y : Type} [Group Y]

theorem innAut_conj (L : Subgroup Y) (φ : MulAut L) (x : L) :
    φ * innAut L x * φ⁻¹ = innAut L (φ x) := by
  ext y
  simp only [MulAut.mul_apply, ← indAut_eq_innAut,
    coe_indAut_apply (Subgroup.le_normalizer (φ x).2)]
  have h1 : ((indAut L (x : Y) (φ⁻¹ y) : L) : Y) = x * (φ⁻¹ y : Y) * x⁻¹ :=
    coe_indAut_apply (Subgroup.le_normalizer x.2) _
  have h2 : indAut L (x : Y) (φ⁻¹ y) = x * φ⁻¹ y * x⁻¹ := Subtype.ext (by rw [h1]; rfl)
  rw [h2, map_mul, map_mul, map_inv, MulAut.apply_inv_self]
  rfl

theorem range_innAut_le (L : Subgroup Y) : (innAut L).range ≤ autOn ⊤ L := by
  rintro _ ⟨x, rfl⟩
  rw [← indAut_eq_innAut]
  exact indAut_mem_autOn (Subgroup.mem_top _) (Subgroup.le_normalizer x.2)

theorem innAut_range_normal (L : Subgroup Y) : (innAut L).range.Normal := by
  refine ⟨?_⟩
  rintro _ ⟨x, rfl⟩ φ
  exact ⟨φ x, (innAut_conj L φ x).symm⟩

end Inner

section Aut

variable {Y : Type} [Group Y] [Finite Y] {T M L : Subgroup Y}

namespace Factor

variable (hF : Factor T M L)
include hF

theorem even_card : Even (Nat.card L) := by
  by_contra hodd
  have hsolv : Group.IsSolvable L := CFSG.FeitThompson.isSolvable_of_odd_natCard L (Nat.not_even_iff_odd.mp hodd)
  have := hF.simple
  exact hF.nonab (IsMulCommutative.of_comm ((IsSimpleGroup.comm_iff_isSolvable).mpr hsolv))

theorem exists_autData : ∃ C, AutData T L (twoResidual (⊤ : Subgroup Y)) C := by
  have hKn := Factor.twoResidual_normal (Y := Y)
  exact B6.exists_autData hF.minPar.isSylow.2.1 hKn (sup_twoResidual_eq hF.minPar.isSylow)
    (isSylowTwoOf_inf_normal hF.minPar.isSylow le_top (le_normalizer_twoResidual ⊤)) hF.simple
    hF.nonab hF.even_card hF.le hF.gen hF.ind hF.normal

theorem autOn_top_le_sup : autOn ⊤ L ≤ (innAut L).range ⊔ autOn T L := by
  obtain ⟨C, d⟩ := hF.exists_autData
  exact d.autOn_top_le le_sup_right fun x => Subgroup.mem_sup_left ⟨x, rfl⟩

theorem isSylowTwoOf_autOn : IsSylowTwoOf (autOn T L) (autOn ⊤ L) := by
  obtain ⟨C, d⟩ := hF.exists_autData
  have hInn : (innAut L).range.Normal := innAut_range_normal L
  refine ⟨autOn_le_autOn_of_le le_top, isPGroup_autOn hF.minPar.isSylow.2.1 L, ?_⟩
  have hsup : autOn ⊤ L = autOn T L ⊔ (innAut L).range :=
    le_antisymm (by rw [sup_comm]; exact hF.autOn_top_le_sup)
      (sup_le (autOn_le_autOn_of_le le_top) (range_innAut_le L))
  have h1 : ((autOn T L).subgroupOf (autOn ⊤ L)).index =
      (autOn T L ⊓ (innAut L).range).relIndex (innAut L).range := by
    rw [hsup]
    exact (relIndex_inf_eq_relIndex_sup
      (fun x _ => Subgroup.le_normalizer_of_normal (Subgroup.mem_top x))).symm
  have h2 : (autOn T L ⊓ (innAut L).range).relIndex (innAut L).range =
      ((autOn T L).comap (innAut L)).index := by
    rw [Subgroup.index_comap]
    exact Subgroup.inf_relIndex_right _ _
  have h3 : (T ⊓ L).subgroupOf L ≤ (autOn T L).comap (innAut L) := by
    intro x hx
    rw [Subgroup.mem_comap, ← indAut_eq_innAut]
    exact indAut_mem_autOn (Subgroup.mem_subgroupOf.mp hx).1 (Subgroup.le_normalizer x.2)
  rw [h1, h2]
  intro hd
  exact d.sylow_TL.2.2 (hd.trans (Subgroup.index_dvd_of_le h3))

theorem minParabolic_autOn : MinParabolic (autOn ⊤ L) (autOn T L) (autOn M L) := by
  obtain ⟨hA1, hA2⟩ := aut_clause hF.minPar hF.simple hF.nonab hF.even_card hF.le hF.gen hF.ind
    hF.normal
  exact ⟨hF.isSylowTwoOf_autOn, hA1.2, hA2⟩

theorem asHyp_autOn :
    ASHyp ((innAut L).range.subgroupOf (autOn ⊤ L)) ((autOn T L).subgroupOf (autOn ⊤ L))
      ((autOn M L).subgroupOf (autOn ⊤ L)) := by
  have hinj := innAut_injective hF.simple hF.nonab
  have hInn : (innAut L).range.Normal := innAut_range_normal L
  have e : ↥L ≃* ↥((innAut L).range.subgroupOf (autOn ⊤ L)) :=
    (MonoidHom.ofInjective hinj).trans (Subgroup.subgroupOfEquivOfLe (range_innAut_le L)).symm
  have := hF.simple
  refine ⟨hF.minParabolic_autOn.subgroupOf, hInn.subgroupOf _,
    (MulEquiv.isSimpleGroup_congr e).mp hF.simple, ?_, ?_, ?_⟩
  · obtain ⟨a, b, hab⟩ := hF.exists_ne_comm
    exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul, h]))⟩
  · rw [← Subgroup.subgroupOf_sup (range_innAut_le L) (autOn_le_autOn_of_le le_top)]
    exact Subgroup.subgroupOf_eq_top.mpr hF.autOn_top_le_sup
  · rw [eq_bot_iff]
    intro α hα
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [Subgroup.coe_one]
    ext x
    have hx : (⟨innAut L x, (range_innAut_le L) ⟨x, rfl⟩⟩ : ↥(autOn ⊤ L)) ∈
        (innAut L).range.subgroupOf (autOn ⊤ L) := ⟨x, rfl⟩
    have hc := Subgroup.mem_centralizer_iff.mp hα _ hx
    have hc' : (α : MulAut L) * innAut L x = innAut L x * α := (congrArg Subtype.val hc).symm
    have h1 : innAut L ((α : MulAut L) x) = innAut L x := by
      rw [← innAut_conj, hc', mul_inv_cancel_right]
    rw [hinj h1, MulAut.one_apply]

end Factor

end Aut

end E2P

end CFSG.Quasithin
