module

public import CFSG.RankThree.CentralLift.LinearScalarCover

public section

namespace CFSG.RankThree.CentralLift

theorem exists_comp_eq_of_pullback_section {H L Q : Type*} [Group H] [Group L] [Group Q]
    {β : H →* Q} {η : L →* Q} (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center L)
    {p : ℕ} (hCp : IsPGroup p η.ker)
    (hsplit : ∀ (P : Subgroup (H × L)) (ρ : P →* H), Function.Surjective ρ →
      ρ.ker ≤ Subgroup.center P → IsPGroup p ρ.ker → ∃ s : H →* P, ρ.comp s = MonoidHom.id H) :
    ∃ φ : H →* L, η.comp φ = β := by
  set P := (β.comp (MonoidHom.fst H L)).eqLocus (η.comp (MonoidHom.snd H L)) with hP
  set ρ := (MonoidHom.fst H L).comp P.subtype with hρ
  have hmemP : ∀ y : H × L, y ∈ P ↔ β y.1 = η y.2 := fun _ => Iff.rfl
  have hρs : Function.Surjective ρ := by
    intro h
    obtain ⟨l, hl⟩ := hη (β h)
    exact ⟨⟨(h, l), (hmemP _).2 hl.symm⟩, rfl⟩
  have hρker : ∀ y : P, y ∈ ρ.ker ↔ (y : H × L).1 = 1 := fun _ => Iff.rfl
  have hkerη : ∀ y : P, y ∈ ρ.ker → (y : H × L).2 ∈ η.ker := by
    intro y hy
    rw [MonoidHom.mem_ker, ← (hmemP _).1 y.2, (hρker y).1 hy, map_one]
  have hA : ρ.ker ≤ Subgroup.center P := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro z
    have hc := Subgroup.mem_center_iff.1 (hC (hkerη y hy)) (z : H × L).2
    have h1 : (y : H × L).1 = 1 := (hρker y).1 hy
    refine Subtype.ext (Prod.ext ?_ hc)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Prod.fst_mul, Prod.fst_mul, h1, mul_one, one_mul]
  have hAp : IsPGroup p ρ.ker := by
    refine hCp.of_injective
      ((MonoidHom.snd _ L).comp (P.subtype.comp ρ.ker.subtype) |>.codRestrict η.ker
        fun y => hkerη y y.2) fun y z hyz => ?_
    have h2 : (y : P).1.2 = (z : P).1.2 := congrArg Subtype.val hyz
    exact Subtype.ext (Subtype.ext (Prod.ext (((hρker y).1 y.2).trans ((hρker z).1 z.2).symm)
      h2))
  obtain ⟨s, hs⟩ := hsplit P ρ hρs hA hAp
  refine ⟨(MonoidHom.snd H L).comp (P.subtype.comp s), MonoidHom.ext fun h => ?_⟩
  have hh := DFunLike.congr_fun hs h
  change ((s h : P) : H × L).1 = h at hh
  change η ((s h : P) : H × L).2 = β h
  rw [← (hmemP _).1 (s h).2, hh]

theorem cover_map_of_comp_eq {H L Q : Type*} [Group H] [Group L] [Group Q] [Group.IsPerfect L]
    {β : H →* Q} (hβ : Function.Surjective β) {η : L →* Q} (hC : η.ker ≤ Subgroup.center L)
    {φ : H →* L} (hφ : η.comp φ = β) :
    Function.Surjective φ ∧ φ.ker ≤ β.ker ∧ β.ker.map φ = η.ker ∧
      (∃ e : H ⧸ φ.ker ≃* L, ∀ h : H, e (h : H ⧸ φ.ker) = φ h ∧ η (e (h : H ⧸ φ.ker)) = β h) ∧
      Nonempty (η.ker ≃* β.ker ⧸ φ.ker.subgroupOf β.ker) := by
  have hηφ : ∀ h, η (φ h) = β h := fun h => DFunLike.congr_fun hφ h
  have hLC : ∀ l : L, ∃ c ∈ η.ker, ∃ h, l = c * φ h := by
    intro l
    obtain ⟨h, hh⟩ := hβ (η l)
    refine ⟨l * (φ h)⁻¹, ?_, h, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hηφ, hh, mul_inv_cancel]
  have hsurj : Function.Surjective φ := by
    have hcomm : commutator L ≤ φ.range := by
      rw [commutator_eq_closure, Subgroup.closure_le]
      rintro _ ⟨a, b, rfl⟩
      obtain ⟨c, hc, x, rfl⟩ := hLC a
      obtain ⟨d, hd, y, rfl⟩ := hLC b
      rw [commutatorElement_mul_center (hC hc) (hC hd), ← map_commutatorElement]
      exact ⟨_, rfl⟩
    have htop : commutator L = ⊤ := Group.isPerfect_def.1 inferInstance
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← htop]
    exact hcomm
  have hker : φ.ker ≤ β.ker := by
    intro h hh
    rw [MonoidHom.mem_ker, ← hηφ, MonoidHom.mem_ker.1 hh, map_one]
  have hmapD : β.ker.map φ = η.ker := by
    apply le_antisymm
    · rintro _ ⟨d, hd, rfl⟩
      rw [MonoidHom.mem_ker, hηφ]
      exact hd
    · intro c hc
      obtain ⟨h, rfl⟩ := hsurj c
      refine ⟨h, ?_, rfl⟩
      change β h = 1
      rw [← hηφ]
      exact hc
  have hDC : ∀ d : β.ker, φ d ∈ η.ker := fun d => hmapD ▸ Subgroup.mem_map_of_mem φ d.2
  let ψ : β.ker →* η.ker := (φ.comp β.ker.subtype).codRestrict η.ker hDC
  have hψ : Function.Surjective ψ := by
    rintro ⟨c, hc⟩
    rw [← hmapD] at hc
    obtain ⟨d, hd, rfl⟩ := hc
    exact ⟨⟨d, hd⟩, rfl⟩
  have hψker : ψ.ker = φ.ker.subgroupOf β.ker := by
    ext d
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  exact ⟨hsurj, hker, hmapD, ⟨QuotientGroup.quotientKerEquivOfSurjective φ hsurj,
    fun h => ⟨rfl, hηφ h⟩⟩, ⟨((QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)).symm⟩⟩

end CFSG.RankThree.CentralLift
