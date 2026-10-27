module

public import CFSG.Monster.B.TwoA.Amalgam.LocalBldMain

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.Geometry
open CFSG.Blueprint.Chevalley

@[expose] def chamberLeft :
    Eam →* Equiv.Perm Chamber where
  toFun g :=
    { toFun := fun c => chamberMul c g⁻¹
      invFun := fun c => chamberMul c g
      left_inv := fun c => by
        change chamberMul (chamberMul c g⁻¹) g = c
        rw [← chamberMul_mul, inv_mul_cancel, chamberMul_one]
      right_inv := fun c => by
        change chamberMul (chamberMul c g) g⁻¹ = c
        rw [← chamberMul_mul, mul_inv_cancel, chamberMul_one] }
  map_one' := by
    ext c
    change chamberMul c 1⁻¹ = c
    rw [inv_one, chamberMul_one]
  map_mul' g h := by
    ext c
    change chamberMul c (g * h)⁻¹ = chamberMul (chamberMul c h⁻¹) g⁻¹
    rw [mul_inv_rev, chamberMul_mul]

theorem chamberLeft_apply
    (g : Eam) (c : Chamber) : chamberLeft g c = chamberMul c g⁻¹ := rfl

theorem chamberLeft_chamberOf
    (g h : Eam) : chamberLeft g (chamberOf h) = chamberOf (h * g⁻¹) :=
  rfl

theorem chamberAdj_chamberLeft
    (i : Fin 4) (g : Eam) (c d : Chamber) :
    chamberAdj i (chamberLeft g c) (chamberLeft g d) ↔ chamberAdj i c d :=
  chamberAdj_chamberMul i c d g⁻¹

theorem mem_ker_chamberLeft_iff
    (g : Eam) :
    g ∈ chamberLeft.ker ↔ ∀ c : Chamber, chamberMul c g = c := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h c
    have h1 := congrArg (fun σ : Equiv.Perm Chamber => σ (chamberMul c g)) h
    simp only [chamberLeft_apply, Equiv.Perm.coe_one, id_eq, ← chamberMul_mul,
      mul_inv_cancel, chamberMul_one] at h1
    exact h1.symm
  · intro h
    refine Equiv.ext fun c => ?_
    have h1 := h (chamberMul c g⁻¹)
    rw [← chamberMul_mul, inv_mul_cancel, chamberMul_one] at h1
    exact h1.symm

theorem ker_chamberLeft :
    chamberLeft.ker = (Bam.subgroupOf Eam).normalCore := by
  ext g
  rw [mem_ker_chamberLeft_iff]
  change _ ↔ ∀ x : Eam, x * g * x⁻¹ ∈ Bam.subgroupOf Eam
  constructor
  · intro h x
    have h1 := h (chamberOf x)
    rw [chamberMul_chamberOf, chamberOf_eq_iff] at h1
    rw [Subgroup.mem_subgroupOf]
    simpa [mul_assoc] using Bam.inv_mem h1
  · intro h c
    obtain ⟨x, rfl⟩ := chamberOf_surjective c
    rw [chamberMul_chamberOf, chamberOf_eq_iff]
    have h1 := Subgroup.mem_subgroupOf.mp (h x)
    simpa [mul_assoc] using Bam.inv_mem h1

theorem chamberLeft_chamberOf_one_eq_iff
    (g : Eam) :
    chamberLeft g (chamberOf 1) = chamberOf 1 ↔ g ∈ Bam.subgroupOf Eam := by
  rw [chamberLeft_chamberOf, chamberOf_eq_iff, Subgroup.mem_subgroupOf]
  simp

instance :
    Nonempty Chamber := ⟨chamberOf 1⟩

@[expose] def typesOff (i : Fin 4) : Set (Fin Tag.F4.rank) := {j | (j : ℕ) ≠ (i : ℕ)}

theorem parJ_mono
    {J K : Set (Fin Tag.F4.rank)} (h : J ⊆ K) : parJ J ≤ parJ K :=
  sup_le (Bam_le_parJ K) (iSup₂_le fun _ hj => Qam_le_parJ (h hj))

theorem parJ_empty : parJ ∅ = Bam :=
  sup_eq_left.mpr (iSup₂_le fun _ hj => absurd hj (Set.notMem_empty _))

theorem parJ_eq_Qam
    (l : Fin 4) : parJ {k | (k : ℕ) = (l : ℕ)} = Qam l := by
  refine le_antisymm (sup_le (Bam_le_Qam l) (iSup₂_le fun k hk => ?_)) (Qam_le_parJ rfl)
  rw [show k = l from Fin.ext hk]

theorem parJ_typesOff
    {i : Fin 4} (hP : Pc i = ⨆ (j : Fin 4) (_ : j ≠ i), Qam j) :
    parJ (typesOff i) = Pc i := by
  refine le_antisymm (sup_le (Bam_le_Pc i) (iSup₂_le fun j hj => ?_)) ?_
  · exact Qam_le_Pc (fun h => hj (congrArg Fin.val h.symm))
  · rw [hP]
    exact iSup₂_le fun j hj => Qam_le_parJ (J := typesOff i) (j := j)
      (fun h => hj (Fin.ext h))

@[expose] def resGroup
    (J : Set (Fin Tag.F4.rank)) : Subgroup Eam := (parJ J).subgroupOf Eam

theorem Bam_le_resGroup
    (J : Set (Fin Tag.F4.rank)) : Bam.subgroupOf Eam ≤ resGroup J :=
  Subgroup.subgroupOf_mono Eam (Bam_le_parJ J)

theorem resGroup_mono
    {J K : Set (Fin Tag.F4.rank)} (h : J ⊆ K) : resGroup J ≤ resGroup K :=
  Subgroup.subgroupOf_mono Eam (parJ_mono h)

theorem natCard_resGroup
    (J : Set (Fin Tag.F4.rank)) :
    Nat.card (resGroup J) = Nat.card (parJ J) :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe (parJ_le_Eam J)).toEquiv

variable {X : ChamberSystem (Fin Tag.F4.rank) Chamber}
  (hX : ∀ i c d, X.adj i c d ↔ chamberAdj i c d)

theorem residue_chamberOf_one
    (hres : ∀ (J : Set (Fin Tag.F4.rank)) (g h : Eam), chamberOf h ∈ X.residue J (chamberOf g) ↔
      ((h * g⁻¹ : Eam) : Dfull) ∈ parJ J)
    (J : Set (Fin Tag.F4.rank)) :
    X.residue J (chamberOf 1) = chamberOf '' (resGroup J : Set Eam) := by
  ext c
  obtain ⟨h, rfl⟩ := chamberOf_surjective c
  rw [hres, inv_one, mul_one]
  constructor
  · intro hh
    exact ⟨h, Subgroup.mem_subgroupOf.mpr hh, rfl⟩
  · rintro ⟨x, hx, hxh⟩
    rw [chamberOf_eq_iff] at hxh
    have h1 : ((h * x⁻¹ : Eam) : Dfull) * (x : Dfull) ∈ parJ J :=
      mul_mem (Bam_le_parJ J hxh) (Subgroup.mem_subgroupOf.mp hx)
    have h2 : (h : Dfull) ∈ parJ J := by simpa using h1
    exact h2

theorem natCard_eq_mul_ncard_image {S : Subgroup Eam} (hBS : Bam.subgroupOf Eam ≤ S) :
    Nat.card S = Nat.card Bam * (chamberOf '' (S : Set Eam)).ncard := by
  set K := (Bam.subgroupOf Eam).subgroupOf S with hK
  have hrel : ∀ a b : S, chamberOf a = chamberOf b ↔ QuotientGroup.rightRel K a b := by
    intro a b
    rw [chamberOf_eq_iff, QuotientGroup.rightRel_apply, hK, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf]
    rfl
  let f : Quotient (QuotientGroup.rightRel K) → ↥(chamberOf '' (S : Set Eam)) :=
    Quotient.lift (fun a : S => ⟨chamberOf a, a, a.2, rfl⟩) fun a b h =>
      Subtype.ext ((hrel a b).mpr h)
  have hf : Function.Bijective f := by
    refine ⟨fun x y hxy => ?_, fun ⟨c, a, ha, hac⟩ => ⟨Quotient.mk _ ⟨a, ha⟩, Subtype.ext hac⟩⟩
    induction x using Quotient.inductionOn with | h a => ?_
    induction y using Quotient.inductionOn with | h b => ?_
    exact Quotient.sound ((hrel a b).mp (congrArg Subtype.val hxy))
  rw [← Nat.card_coe_set_eq, ← Nat.card_congr (Equiv.ofBijective f hf),
    Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel K), ← Subgroup.index_eq_card,
    ← K.card_mul_index, hK, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBS).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe Bam_le_Eam).toEquiv]

theorem image_chamberLeft_eq_iff {S : Subgroup Eam} (hBS : Bam.subgroupOf Eam ≤ S) (g : Eam) :
    chamberLeft g '' (chamberOf '' (S : Set Eam)) = chamberOf '' (S : Set Eam) ↔ g ∈ S := by
  constructor
  · intro h
    have h1 : chamberLeft g (chamberOf 1) ∈ chamberOf '' (S : Set Eam) :=
      h ▸ ⟨chamberOf 1, ⟨1, one_mem S, rfl⟩, rfl⟩
    obtain ⟨x, hx, hxe⟩ := h1
    rw [chamberLeft_chamberOf, one_mul, chamberOf_eq_iff] at hxe
    have hxg : g⁻¹ * x⁻¹ ∈ S := hBS (Subgroup.mem_subgroupOf.mpr hxe)
    have h2 : g⁻¹ * x⁻¹ * x ∈ S := mul_mem hxg hx
    rw [inv_mul_cancel_right] at h2
    simpa using inv_mem h2
  · intro hg
    ext c
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x * g⁻¹, mul_mem hx (inv_mem hg), rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨chamberOf (x * g), ⟨x * g, mul_mem hx hg, rfl⟩, by
        rw [chamberLeft_chamberOf, mul_inv_cancel_right]⟩

include hX in
theorem chamberLeft_mem_typeAut (g : Eam) : chamberLeft g ∈ X.typeAut := by
  intro i c d
  rw [hX, hX]
  exact chamberAdj_chamberLeft i g c d

variable (X) in
@[expose] def chamberRho : Eam →* X.typeAut :=
  chamberLeft.codRestrict X.typeAut (chamberLeft_mem_typeAut hX)

theorem chamberRho_apply (g : Eam) (c : Chamber) :
    ((chamberRho X hX g : X.typeAut) : Equiv.Perm Chamber) c = chamberMul c g⁻¹ := rfl

theorem ker_chamberRho : (chamberRho X hX).ker = chamberLeft.ker :=
  MonoidHom.ker_codRestrict _ _ _

theorem exists_chamberRho_apply_eq (c d : Chamber) :
    ∃ g : Eam, ((chamberRho X hX g : X.typeAut) : Equiv.Perm Chamber) c = d := by
  obtain ⟨a, rfl⟩ := chamberOf_surjective c
  obtain ⟨b, rfl⟩ := chamberOf_surjective d
  exact ⟨b⁻¹ * a, by rw [chamberRho_apply, chamberMul_chamberOf]; congr 1; group⟩

end CFSG.Monster.B.TwoA.Amalgam
