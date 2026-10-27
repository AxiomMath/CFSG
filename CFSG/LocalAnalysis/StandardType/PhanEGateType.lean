module

public import CFSG.LocalAnalysis.StandardType.PhanEGatePsi

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Gate

open CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
  {C : Type*} {δ : C → C → W} {w₀ : W} {t : C → C} {J I : Set ι} {a x₁ : C}

@[expose] def flipCoreType (cs : CoxeterSystem M W) (J : Set ι) (π : W) : Set ι :=
  {i | i ∈ J ∧ ∃ j ∈ J, π * cs.simple j * π⁻¹ = cs.simple i}

theorem flipCoreType_subset (cs : CoxeterSystem M W) (J : Set ι) (π : W) :
    flipCoreType cs J π ⊆ J :=
  fun _ hi => hi.1

private theorem p9uGT_conjInter_flipType_eq_flipCoreType (cs : CoxeterSystem M W) (J : Set ι)
    (w₁ w₀ : W) (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀) :
    cs.conjInter J (flipType cs w₀ J) w₁ = flipCoreType cs J (w₁ * w₀) := by
  have hw0 : w₀ * w₀ = 1 := CoxeterSystem.w0_mul_self cs w₀ hw
  ext i
  constructor
  · rintro ⟨hiJ, k, ⟨j, hjJ, hjk⟩, hik⟩
    refine ⟨hiJ, j, hjJ, ?_⟩
    have hstep : cs.simple i * (w₁ * w₀) = (w₁ * w₀) * cs.simple j := by
      calc cs.simple i * (w₁ * w₀) = (cs.simple i * w₁) * w₀ := by rw [mul_assoc]
        _ = (w₁ * cs.simple k) * w₀ := by rw [hik]
        _ = (w₁ * (w₀ * cs.simple j * w₀)) * w₀ := by rw [← hjk]
        _ = w₁ * (w₀ * cs.simple j * (w₀ * w₀)) := by group
        _ = w₁ * (w₀ * cs.simple j) := by rw [hw0, mul_one]
        _ = (w₁ * w₀) * cs.simple j := by group
    calc (w₁ * w₀) * cs.simple j * (w₁ * w₀)⁻¹
        = cs.simple i * (w₁ * w₀) * (w₁ * w₀)⁻¹ := by rw [← hstep]
      _ = cs.simple i := by group
  · rintro ⟨hiJ, j, hjJ, hconj⟩
    obtain ⟨k, hk⟩ := CoxeterSystem.exists_simple_conj_w0 cs w₀ hw j
    refine ⟨hiJ, k, ⟨j, hjJ, hk⟩, ?_⟩
    have hstep : cs.simple i * (w₁ * w₀) = (w₁ * w₀) * cs.simple j := by
      rw [← hconj]; group
    have h1 : cs.simple i * w₁ = cs.simple i * (w₁ * w₀) * w₀ := by
      calc cs.simple i * w₁ = cs.simple i * w₁ * (w₀ * w₀) := by rw [hw0, mul_one]
        _ = cs.simple i * (w₁ * w₀) * w₀ := by group
    calc cs.simple i * w₁ = cs.simple i * (w₁ * w₀) * w₀ := h1
      _ = (w₁ * w₀) * cs.simple j * w₀ := by rw [hstep]
      _ = w₁ * (w₀ * cs.simple j * w₀) := by group
      _ = w₁ * cs.simple k := by rw [hk]

theorem flipCore_eq_residue_flipCoreType (hB : IsWeylDistanceBuilding cs δ)
    (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : IsFlipInvolution cs δ w₀ t) (hx₁ : x₁ ∈ flipCore cs δ t J a) :
    flipCore cs δ t J a =
      residue cs δ (flipCoreType cs J (flipPi cs δ w₀ t J a x₁)) x₁ := by
  let w₁ : W := δ (flipPsi cs δ t J a x₁) (t x₁)
  have hpi : flipPi cs δ w₀ t J a x₁ = w₁ * w₀ := rfl
  have hxy : IsClosestPair cs δ J (flipType cs w₀ J) a (t a)
      (flipPsi cs δ t J a x₁) (t x₁) := isClosestPair_flipPsi hB hw ht hx₁
  have hcore : flipCore cs δ t J a =
      projSet cs δ J a (residue cs δ (flipType cs w₀ J) (t a)) := by
    unfold flipCore
    rw [image_residue_flip hw ht J a]
  have hx₁mem : x₁ ∈ residue cs δ (cs.conjInter J (flipType cs w₀ J) w₁)
      (flipPsi cs δ t J a x₁) := by
    rw [← projSet_eq_residue hB hxy, ← hcore]
    exact hx₁
  have hres := residue_eq_of_mem hB hx₁mem
  calc flipCore cs δ t J a
      = projSet cs δ J a (residue cs δ (flipType cs w₀ J) (t a)) := hcore
    _ = residue cs δ (cs.conjInter J (flipType cs w₀ J) w₁)
          (flipPsi cs δ t J a x₁) := projSet_eq_residue hB hxy
    _ = residue cs δ (cs.conjInter J (flipType cs w₀ J) w₁) x₁ := hres.symm
    _ = residue cs δ (flipCoreType cs J (w₁ * w₀)) x₁ := by
          rw [p9uGT_conjInter_flipType_eq_flipCoreType cs J w₁ w₀ hw]
    _ = residue cs δ (flipCoreType cs J (flipPi cs δ w₀ t J a x₁)) x₁ := by rw [hpi]

@[expose] noncomputable def flipTypeMap (cs : CoxeterSystem M W) (δ : C → C → W) (w₀ : W)
    (t : C → C) (J : Set ι) (a x₁ : C) (i : ι) : ι :=
  open Classical in
  if h : ∃ i', flipPi cs δ w₀ t J a x₁ * cs.simple i * (flipPi cs δ w₀ t J a x₁)⁻¹ =
      cs.simple i' then h.choose else i

theorem flipTypeMap_spec (hB : IsWeylDistanceBuilding cs δ)
    (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : IsFlipInvolution cs δ w₀ t) (hI : flipCore cs δ t J a = residue cs δ I x₁) {i : ι}
    (hi : i ∈ I) :
    flipTypeMap cs δ w₀ t J a x₁ i ∈ I ∧
      flipPi cs δ w₀ t J a x₁ * cs.simple i * (flipPi cs δ w₀ t J a x₁)⁻¹ =
        cs.simple (flipTypeMap cs δ w₀ t J a x₁ i) := by
  obtain ⟨i', hi', heq⟩ := exists_simple_flipPsi hB hw ht hI hi
  have hex : ∃ i'', flipPi cs δ w₀ t J a x₁ * cs.simple i *
      (flipPi cs δ w₀ t J a x₁)⁻¹ = cs.simple i'' := ⟨i', heq⟩
  have hmap : flipTypeMap cs δ w₀ t J a x₁ i = hex.choose := by
    unfold flipTypeMap
    exact dif_pos hex
  have hchoose : hex.choose = i' :=
    CoxeterSystem.simple_injective cs ((Classical.choose_spec hex).symm.trans heq)
  exact ⟨by rw [hmap, hchoose]; exact hi', by rw [hmap]; exact Classical.choose_spec hex⟩

theorem flipTypeMap_flipTypeMap (hB : IsWeylDistanceBuilding cs δ)
    (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : IsFlipInvolution cs δ w₀ t) (hI : flipCore cs δ t J a = residue cs δ I x₁) {i : ι}
    (hi : i ∈ I) :
    flipTypeMap cs δ w₀ t J a x₁ (flipTypeMap cs δ w₀ t J a x₁ i) = i := by
  obtain ⟨hi'I, hconj⟩ := flipTypeMap_spec hB hw ht hI hi
  obtain ⟨-, hconj'⟩ := flipTypeMap_spec hB hw ht hI hi'I
  have hx₁core : x₁ ∈ flipCore cs δ t J a := by
    rw [hI]
    exact self_mem_residue I x₁
  obtain ⟨z, hz, -⟩ := hB.exists_simple x₁ x₁ i
  have hzcore : z ∈ flipCore cs δ t J a := by
    rw [hI]
    exact Relation.ReflTransGen.single ⟨i, hi, hz⟩
  have hψx₁ : flipPsi cs δ t J a x₁ ∈ flipCore cs δ t J a :=
    flipPsi_mem hB hw ht hx₁core
  have hψz : flipPsi cs δ t J a z ∈ flipCore cs δ t J a :=
    flipPsi_mem hB hw ht hzcore
  have heq1 : δ (flipPsi cs δ t J a x₁) (flipPsi cs δ t J a z) =
      cs.simple (flipTypeMap cs δ w₀ t J a x₁ i) := by
    have h := (dist_flipPsi hB hw ht hx₁core hzcore).1
    rw [h, hz, hconj]
  have hpi_eq : flipPi cs δ w₀ t J a (flipPsi cs δ t J a x₁) =
      flipPi cs δ w₀ t J a x₁ := flipPi_eq hB hw ht hψx₁ hx₁core
  have heq2 := (dist_flipPsi hB hw ht hψx₁ hψz).1
  rw [hpi_eq, heq1, hconj'] at heq2
  rw [flipPsi_flipPsi hB hw ht hx₁core, flipPsi_flipPsi hB hw ht hzcore] at heq2
  exact CoxeterSystem.simple_injective cs (heq2.symm.trans hz)

end CFSG.ClassicalInvolution.Phan.PhanE.Gate

end
