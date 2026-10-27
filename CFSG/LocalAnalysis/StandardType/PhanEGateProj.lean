module

public import CFSG.LocalAnalysis.StandardType.PhanEGatePair

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Gate

open CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
  {C : Type*} {δ : C → C → W} {J K : Set ι} {a b x y x' y' : C}

private theorem p9uGJ_isClosestPair_of_gate (hB : IsWeylDistanceBuilding cs δ)
    {z p q : C} (hzK : z ∈ residue cs δ K b)
    (hpJ : IsProjection cs δ (residue cs δ J a) z p)
    (hqK : IsProjection cs δ (residue cs δ K b) p q) :
    IsClosestPair cs δ J K a b p q := by
  obtain ⟨hmul, hlen⟩ := hqK.gate hB hzK
  have hminK : cs.IsMinimalCosetRep K (δ p q) :=
    isMinimalCosetRep_of_forall_le (J := K) (y := b) (z := p) (p := q) hB hqK.1
      fun r hr => by
        by_cases hrq : r = q
        · rw [hrq]
        · exact (hqK.2 r hr hrq).le
  have hminJ : cs.IsMinimalCosetRep J (δ z p) :=
    isMinimalCosetRep_of_forall_le (J := J) (y := a) (z := z) (p := p) hB hpJ.1
      fun r hr => by
        by_cases hrp : r = p
        · rw [hrp]
        · exact (hpJ.2 r hr hrp).le
  have hnoLeft_pz : ∀ i ∈ J, ¬ cs.IsLeftDescent (δ p z) i := by
    intro i hi hd
    have hd' : cs.IsLeftDescent (δ z p)⁻¹ i := by
      simpa only [← dist_inv hB z p] using hd
    exact (cs.isMinimalCosetRep_iff.mp hminJ) i hi (cs.isLeftDescent_inv_iff.mp hd')
  have hnoLeft_pq : ∀ i ∈ J, ¬ cs.IsLeftDescent (δ p q) i := by
    intro i hi hd
    refine hnoLeft_pz i hi ?_
    have hassoc : cs.simple i * δ p z = (cs.simple i * δ p q) * δ q z := by
      rw [hmul]; group
    have hle := cs.length_mul_le (cs.simple i * δ p q) (δ q z)
    have hd' : cs.length (cs.simple i * δ p q) < cs.length (δ p q) := hd
    show cs.length (cs.simple i * δ p z) < cs.length (δ p z)
    rw [hassoc, hlen]
    omega
  have hminDC : cs.IsMinimalDoubleCosetRep J K (δ p q) := by
    rw [cs.isMinimalDoubleCosetRep_iff]
    exact ⟨fun k hk => (cs.isMinimalCosetRep_iff.mp hminK) k hk, hnoLeft_pq⟩
  refine ⟨hpJ.1, hqK.1, fun x'' hx'' y'' hy'' => ?_⟩
  obtain ⟨u, hu, v, hv, huv⟩ :=
    DoubleCoset.mem_doubleCoset.mp (dist_mem_doubleCoset hB hx'' hy'')
  obtain ⟨u', hu', v', hv', hu'v'⟩ :=
    DoubleCoset.mem_doubleCoset.mp (dist_mem_doubleCoset hB hpJ.1 hqK.1)
  have heq : δ x'' y'' = (u * u'⁻¹) * δ p q * (v'⁻¹ * v) := by
    rw [huv, hu'v']; group
  have hfin := hminDC (u * u'⁻¹) (mul_mem hu (inv_mem hu')) (v'⁻¹ * v)
    (mul_mem (inv_mem hv') hv)
  rwa [← heq] at hfin

theorem mem_projSet_iff (hB : IsWeylDistanceBuilding cs δ) :
    x ∈ projSet cs δ J a (residue cs δ K b) ↔ ∃ y, IsClosestPair cs δ J K a b x y := by
  show x ∈ resProj cs δ J a '' residue cs δ K b ↔ ∃ y, IsClosestPair cs δ J K a b x y
  constructor
  · rintro ⟨z, hzK, rfl⟩
    exact ⟨resProj cs δ K b (resProj cs δ J a z),
      p9uGJ_isClosestPair_of_gate hB hzK (isProjection_resProj hB J a z)
        (isProjection_resProj hB K b (resProj cs δ J a z))⟩
  · rintro ⟨z, hxz⟩
    exact ⟨z, hxz.2.1, hxz.eq_resProj_left hB⟩

private theorem p9uGJ_gate_left (hB : IsWeylDistanceBuilding cs δ)
    (h : IsClosestPair cs δ J K a b x y) :
    IsProjection cs δ (residue cs δ J a) y x :=
  h.eq_resProj_left hB ▸ isProjection_resProj hB J a y

private theorem p9uGJ_gate_right (hB : IsWeylDistanceBuilding cs δ)
    (h : IsClosestPair cs δ J K a b x y) :
    IsProjection cs δ (residue cs δ K b) x y :=
  h.eq_resProj_right hB ▸ isProjection_resProj hB K b x

theorem IsClosestPair.dist_left_eq (hB : IsWeylDistanceBuilding cs δ)
    (h : IsClosestPair cs δ J K a b x y) (h' : IsClosestPair cs δ J K a b x' y') :
    δ x x' = δ x y * δ y y' * (δ x y)⁻¹ := by
  obtain ⟨hAmul, -⟩ := (p9uGJ_gate_left hB h).gate hB h'.1
  obtain ⟨hBmul, -⟩ := (p9uGJ_gate_right hB h').gate hB h.2.1
  have h1 : δ y x' = (δ x y)⁻¹ * δ x x' := by rw [hAmul, dist_inv hB x y]
  have h2 : δ y x' = δ y y' * (δ x y)⁻¹ := by
    rw [dist_inv hB x' y, hBmul, mul_inv_rev, ← dist_inv hB y' y, ← h.dist_eq hB h']
  have hkey : (δ x y)⁻¹ * δ x x' = δ y y' * (δ x y)⁻¹ := h1.symm.trans h2
  calc δ x x' = δ x y * ((δ x y)⁻¹ * δ x x') := by group
    _ = δ x y * (δ y y' * (δ x y)⁻¹) := by rw [hkey]
    _ = δ x y * δ y y' * (δ x y)⁻¹ := by group

theorem IsClosestPair.length_left_eq (hB : IsWeylDistanceBuilding cs δ)
    (h : IsClosestPair cs δ J K a b x y) (h' : IsClosestPair cs δ J K a b x' y') :
    cs.length (δ x x') = cs.length (δ y y') := by
  have hA := ((p9uGJ_gate_left hB h).gate hB h'.1).2
  have hB' := ((p9uGJ_gate_right hB h').gate hB h.2.1).2
  have e1 : cs.length (δ y x') = cs.length (δ x' y) := by
    rw [dist_inv hB x' y, cs.length_inv]
  have e2 : cs.length (δ y x) = cs.length (δ x y) := by
    rw [dist_inv hB x y, cs.length_inv]
  have e3 : cs.length (δ x' y') = cs.length (δ x y) := by rw [h.dist_eq hB h']
  have e4 : cs.length (δ y' y) = cs.length (δ y y') := by
    rw [dist_inv hB y y', cs.length_inv]
  omega

end CFSG.ClassicalInvolution.Phan.PhanE.Gate

end
