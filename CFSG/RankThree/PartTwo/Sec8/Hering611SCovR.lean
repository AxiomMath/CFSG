module

public import CFSG.RankThree.PartTwo.Sec8.Hering611SCovX
public import CFSG.RankThree.PartTwo.Sec8.Hering611SCovAB
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporMcL9Lift

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

variable {X : Type*} [Group X] [Finite X] {Z R T : Subgroup X} {s : X}

private theorem R_pow_three_eq_one (h : CoverX X Z R T s) {x : X} (hx : x ∈ R) :
    x ^ 3 = 1 := by
  have hZc : ∀ z ∈ Z, ∀ g : X, g * z = z * g := fun z hz g =>
    Subgroup.mem_center_iff.mp (h.Z_central hz) g
  have hZ3 : ∀ z ∈ Z, z ^ 3 = 1 := by
    intro z hz
    have h0 := pow_card_eq_one' (G := Z) (x := ⟨z, hz⟩)
    rw [h.card_Z] at h0
    simpa using congrArg Subtype.val h0
  obtain ⟨ζ, hζdef⟩ : ∃ ζ : X, ζ = s ^ 4 * x * (s ^ 4)⁻¹ * x := ⟨_, rfl⟩
  have hζ : ζ ∈ Z := by
    rw [hζdef]
    exact h.R_inv x hx
  have hcj : s ^ 4 * x * (s ^ 4)⁻¹ = ζ * x⁻¹ := by
    rw [hζdef, mul_inv_cancel_right]
  have hg : s ^ 4 * x * (s ^ 4)⁻¹ = x⁻¹ * ζ := hcj.trans (hZc ζ hζ x⁻¹).symm
  exact CFSG.RankThree.PartTwo.Sec4.Item434SporMcL9.cube_eq_one_of_conj_inv h.Z_central hZ3
    (h.R_cube x hx) hζ hg

theorem exists_R0 (h : CoverX X Z R T s) :
    ∃ R₀ : Subgroup X, R₀ ≤ R ∧ Disjoint R₀ Z ∧ Z ⊔ R₀ = R ∧
      (∀ x ∈ R₀, s * x * s⁻¹ ∈ R₀) := by
  have hZc : ∀ z ∈ Z, ∀ g : X, g * z = z * g := fun z hz g =>
    Subgroup.mem_center_iff.mp (h.Z_central hz) g
  have hRc : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := fun a ha b hb =>
    h.R_central a ha b (h.R_le_T hb)
  letI : CommGroup R := { (inferInstance : Group R) with
    mul_comm := fun a b => Subtype.ext (hRc a a.2 b b.2) }
  obtain ⟨sN, hsN⟩ : ∃ t : Subgroup.normalizer (R : Set X), (t : X) = s :=
    ⟨⟨s, h.s_normR⟩, rfl⟩
  have hsN8 : sN ^ 8 = 1 := Subtype.ext (by simp [hsN, h.s_pow])
  have hσ8 : (R.normalizerMonoidHom sN) ^ 8 = 1 := by
    rw [← map_pow, hsN8, map_one]
  have hσapp : ∀ b : R, (((R.normalizerMonoidHom sN) b : R) : X) = s * b * s⁻¹ := fun b => by
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hsN]
  have hm : ∀ b : R, b ^ 3 = 1 := fun b =>
    Subtype.ext (by simpa using R_pow_three_eq_one h b.2)
  have hfix : ∀ z ∈ Z.subgroupOf R, (R.normalizerMonoidHom sN) z = z := by
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz
    apply Subtype.ext
    rw [hσapp z, hZc _ hz s, mul_inv_cancel_right]
  have hfix' : ∀ b : R, (R.normalizerMonoidHom sN) b = b → b ∈ Z.subgroupOf R := by
    intro b hb
    rw [Subgroup.mem_subgroupOf]
    apply h.R_fix (b : X) b.2
    have hb' : s * (b : X) * s⁻¹ = (b : X) := by
      rw [← hσapp b, hb]
    rw [hb', mul_inv_cancel]
    exact Z.one_mem
  obtain ⟨ρ, hρZ, hρσ⟩ := exists_retraction_of_fixed_le (m' := 2) (R.normalizerMonoidHom sN)
    hσ8 hm (by decide) (Z.subgroupOf R) hfix hfix'
  refine ⟨(ρ.ker).map R.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  ·
    rw [Subgroup.disjoint_def]
    intro x hx hxZ
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
    rw [MonoidHom.mem_ker] at hb
    have hbZ : b ∈ Z.subgroupOf R := Subgroup.mem_subgroupOf.mpr hxZ
    have h1 : ρ b = ⟨b, hbZ⟩ := hρZ ⟨b, hbZ⟩
    have h2 : (⟨b, hbZ⟩ : Z.subgroupOf R) = 1 := h1.symm.trans hb
    have h3 : b = 1 := congrArg Subtype.val h2
    rw [h3, map_one]
  ·
    refine le_antisymm (sup_le h.Z_le_R (Subgroup.map_subtype_le _)) ?_
    intro x hx
    obtain ⟨w, hw⟩ : ∃ w : Z.subgroupOf R, ρ ⟨x, hx⟩ = w := ⟨_, rfl⟩
    have hwZ : ((w : R) : X) ∈ Z := Subgroup.mem_subgroupOf.mp w.2
    have hr : (w : R)⁻¹ * (⟨x, hx⟩ : R) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hρZ w, hw, inv_mul_cancel]
    have hmem := Subgroup.mul_mem_sup hwZ (Subgroup.mem_map_of_mem R.subtype hr)
    simpa using hmem
  ·
    intro y hy
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    rw [MonoidHom.mem_ker] at hb
    refine Subgroup.mem_map.mpr ⟨(R.normalizerMonoidHom sN) b, ?_, ?_⟩
    · rw [MonoidHom.mem_ker, hρσ b, hb]
    · exact hσapp b

end CFSG.RankThree.PartTwo.Sec8.Hering611
