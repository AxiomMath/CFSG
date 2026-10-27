module

public import CFSG.LocalAnalysis.StandardType.GGKGAF4CoreDefs
public import CFSG.LocalAnalysis.StandardType.GGKGAF4
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixPerfect
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndModel

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace KGA

theorem ggF4_image_component {L' R : Type} [Group L'] [Group R] (ψ : L' →* R)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (u : L')
    {J : Subgroup L'} (hJ : IsComponentOf J (ggFixSub (MulAut.conj u : MulAut L'))) :
    IsComponentOf (J.map ψ) (Subgroup.centralizer ({ψ u} : Set R)) ∧
      Nonempty ((J.map ψ ⧸ Subgroup.center (J.map ψ)) ≃* (J ⧸ Subgroup.center J)) := by
  have hKH : ggFixSub (MulAut.conj u : MulAut L') ≤
      (Subgroup.centralizer ({ψ u} : Set R)).comap ψ := by
    intro k hk
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    have hfix := mem_ggFixSub.mp hk
    rw [MulAut.conj_apply] at hfix
    have hψfix := congrArg ψ hfix
    simp only [map_mul, map_inv] at hψfix
    exact (mul_inv_eq_iff_eq_mul.mp hψfix).symm
  have hKnormal : (ggFixSub (MulAut.conj u : MulAut L') |>.subgroupOf
      ((Subgroup.centralizer ({ψ u} : Set R)).comap ψ)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hKH]
    intro k x hk hx
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at hx
    have hfix := mem_ggFixSub.mp hk
    rw [MulAut.conj_apply] at hfix
    rw [mem_ggFixSub, MulAut.conj_apply]
    have hz : u * x * u⁻¹ * x⁻¹ ∈ Subgroup.center L' := by
      apply hker
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, ← hx]
      group
    have hzc : ∀ a : L', (u * x * u⁻¹ * x⁻¹) * a * (u * x * u⁻¹ * x⁻¹)⁻¹ = a := by
      intro a
      rw [← Subgroup.mem_center_iff.mp hz a, mul_assoc, mul_inv_cancel, mul_one]
    calc u * (x * k * x⁻¹) * u⁻¹
        = (u * x * u⁻¹) * (u * k * u⁻¹) * (u * x * u⁻¹)⁻¹ := by group
      _ = (u * x * u⁻¹) * k * (u * x * u⁻¹)⁻¹ := by rw [hfix]
      _ = ((u * x * u⁻¹ * x⁻¹) * x) * k * ((u * x * u⁻¹ * x⁻¹) * x)⁻¹ := by
            conv_lhs => rw [show u * x * u⁻¹ = (u * x * u⁻¹ * x⁻¹) * x by group]
      _ = x * k * x⁻¹ := by
            rw [show ((u * x * u⁻¹ * x⁻¹) * x) * k * ((u * x * u⁻¹ * x⁻¹) * x)⁻¹
                = (u * x * u⁻¹ * x⁻¹) * (x * k * x⁻¹) * (u * x * u⁻¹ * x⁻¹)⁻¹ by group]
            exact hzc (x * k * x⁻¹)
  have hsub : IsSubnormal (J.map ψ) (Subgroup.centralizer ({ψ u} : Set R)) := by
    have htrans : IsSubnormal J ((Subgroup.centralizer ({ψ u} : Set R)).comap ψ) :=
      IsSubnormal.trans hJ.2.1
        (IsSubnormal.step hKH hKnormal (IsSubnormal.refl _))
    have hmap := htrans.map ψ
    rwa [Subgroup.map_comap_eq_self_of_surjective hψ] at hmap
  have hle : J.map ψ ≤ Subgroup.centralizer ({ψ u} : Set R) := by
    rintro r ⟨j, hj, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hfix := mem_ggFixSub.mp (hJ.1 hj)
    rw [MulAut.conj_apply] at hfix
    have hψfix := congrArg ψ hfix
    simp only [map_mul, map_inv] at hψfix
    exact (mul_inv_eq_iff_eq_mul.mp hψfix).symm
  let ψJ : ↥J →* ↥(J.map ψ) :=
    (ψ.comp J.subtype).codRestrict (J.map ψ) fun j => Subgroup.mem_map_of_mem ψ j.2
  have hψJ : ∀ j : ↥J, ((ψJ j : ↥(J.map ψ)) : R) = ψ (j : L') := fun _ => rfl
  have hsurj : Function.Surjective ψJ := by
    intro b
    obtain ⟨j, hj, hjb⟩ := Subgroup.mem_map.mp b.2
    exact ⟨⟨j, hj⟩, Subtype.ext hjb⟩
  have hkerJ : ψJ.ker ≤ Subgroup.center ↥J := by
    intro j hj
    rw [MonoidHom.mem_ker] at hj
    have hψj : ψ (j : L') = 1 := by
      have h := congrArg (fun z : ↥(J.map ψ) => (z : R)) hj
      simpa [hψJ] using h
    have hjcent : (j : L') ∈ Subgroup.center L' := by
      apply hker
      rwa [MonoidHom.mem_ker]
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hjcent (y : L')
  let φ : ↥J →* (↥(J.map ψ) ⧸ Subgroup.center ↥(J.map ψ)) :=
    (QuotientGroup.mk' (Subgroup.center ↥(J.map ψ))).comp ψJ
  have hsurjφ : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective _).comp hsurj
  have hkerφ : φ.ker = Subgroup.center ↥J := by
    apply le_antisymm
    · intro j hj
      rw [MonoidHom.mem_ker] at hj
      have hcenter : ψJ j ∈ Subgroup.center ↥(J.map ψ) := by
        have hmem : ψJ j ∈ (QuotientGroup.mk' (Subgroup.center ↥(J.map ψ))).ker := hj
        rwa [QuotientGroup.ker_mk'] at hmem
      have hconj : ∀ y : ↥J, ψJ ((MulAut.conj j) y) = ψJ y := by
        intro y
        have hc := Subgroup.mem_center_iff.mp hcenter (ψJ y)
        have hc' : ψ (y : L') * ψ (j : L') = ψ (j : L') * ψ (y : L') := by
          have h := congrArg (fun z : ↥(J.map ψ) => (z : R)) hc
          simpa [hψJ] using h
        apply Subtype.ext
        show ψ (((MulAut.conj j) y : ↥J) : L') = ψ (y : L')
        rw [MulAut.conj_apply]
        push_cast
        rw [map_mul, map_mul, map_inv, ← hc', mul_assoc, mul_inv_cancel, mul_one]
      have hb := ggAut_eq_one_of_induced_one ψJ hkerJ hJ.2.2.1 (MulAut.conj j) hconj
      rw [Subgroup.mem_center_iff]
      intro y
      have h := congrArg (fun f : MulAut ↥J => f y) hb
      simp only [MulAut.one_apply, MulAut.conj_apply] at h
      exact (mul_inv_eq_iff_eq_mul.mp h).symm
    · intro j hj
      rw [MonoidHom.mem_ker]
      change (QuotientGroup.mk' (Subgroup.center ↥(J.map ψ))) (ψJ j) = 1
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact Subgroup.mem_center_iff.mpr fun y => by
        obtain ⟨x, rfl⟩ := hsurj y
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hj x]
  haveI : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hJ.2.2.2
  have e1 : ↥J ⧸ φ.ker ≃* ↥(J.map ψ) ⧸ Subgroup.center ↥(J.map ψ) :=
    QuotientGroup.quotientKerEquivOfSurjective φ hsurjφ
  have e2 : ↥J ⧸ Subgroup.center ↥J ≃* ↥J ⧸ φ.ker :=
    QuotientGroup.quotientMulEquivOfEq hkerφ.symm
  have e : ↥J ⧸ Subgroup.center ↥J ≃*
      ↥(J.map ψ) ⧸ Subgroup.center ↥(J.map ψ) := e2.trans e1
  haveI hperfJ : Group.IsPerfect ↥J := Group.isPerfect_def.mpr hJ.2.2.1
  have hperfect : commutator ↥(J.map ψ) = ⊤ :=
    (Group.IsPerfect.ofSurjective (f := ψJ) hsurj).commutator_eq_top
  have hsimple : IsSimpleGroup (↥(J.map ψ) ⧸ Subgroup.center ↥(J.map ψ)) :=
    e.symm.isSimpleGroup
  exact ⟨⟨hle, hsub, hperfect, hsimple⟩, ⟨e.symm⟩⟩

theorem ggF4_lift_inner {L' R : Type} [Group L'] [Group R] (ψ : L' →* R)
    (hker : ψ.ker ≤ Subgroup.center L') {J : Subgroup L'} (hJperf : commutator ↥J = ⊤) (v : L')
    (h1 : ∃ x ∈ J.map ψ, ∀ y ∈ J.map ψ, ψ v * y * (ψ v)⁻¹ = x * y * x⁻¹) :
    (∀ y ∈ J, v * y * v⁻¹ ∈ J) ∧ ∃ j ∈ J, ∀ y ∈ J, v * y * v⁻¹ = j * y * j⁻¹ := by
  obtain ⟨x, hxS, hx⟩ := h1
  obtain ⟨j, hjj, hψj⟩ := Subgroup.mem_map.mp hxS
  have hzmem : ∀ y : ↥J, (j * (y : L') * j⁻¹)⁻¹ * (v * (y : L') * v⁻¹) ∈
      Subgroup.center L' := by
    intro y
    apply hker
    rw [MonoidHom.mem_ker]
    have hxy := hx (ψ (y : L')) (Subgroup.mem_map_of_mem ψ y.2)
    have hzj : ψ (j * (y : L') * j⁻¹) = x * ψ (y : L') * x⁻¹ := by
      rw [map_mul, map_mul, map_inv, hψj]
    have hzv : ψ (v * (y : L') * v⁻¹) = x * ψ (y : L') * x⁻¹ := by
      rw [map_mul, map_mul, map_inv]
      exact hxy
    rw [map_mul, map_inv, hzj, hzv, inv_mul_cancel]
  let f : ↥J →* ↥(Subgroup.center L') :=
    { toFun := fun y => ⟨(j * (y : L') * j⁻¹)⁻¹ * (v * (y : L') * v⁻¹), hzmem y⟩
      map_one' := by
        apply Subtype.ext
        push_cast
        group
      map_mul' := fun y₁ y₂ => by
        apply Subtype.ext
        push_cast
        have hc := Subgroup.mem_center_iff.mp (hzmem y₁)
        calc (j * ((y₁ : L') * (y₂ : L')) * j⁻¹)⁻¹ *
                (v * ((y₁ : L') * (y₂ : L')) * v⁻¹)
            = (j * (y₂ : L') * j⁻¹)⁻¹ * ((j * (y₁ : L') * j⁻¹)⁻¹ *
                (v * (y₁ : L') * v⁻¹)) * (v * (y₂ : L') * v⁻¹) := by group
          _ = ((j * (y₁ : L') * j⁻¹)⁻¹ * (v * (y₁ : L') * v⁻¹)) *
                (j * (y₂ : L') * j⁻¹)⁻¹ * (v * (y₂ : L') * v⁻¹) := by
              rw [hc (j * (y₂ : L') * j⁻¹)⁻¹]
          _ = ((j * (y₁ : L') * j⁻¹)⁻¹ * (v * (y₁ : L') * v⁻¹)) *
                ((j * (y₂ : L') * j⁻¹)⁻¹ * (v * (y₂ : L') * v⁻¹)) := by group }
  have hfker : f.ker = ⊤ := by
    apply le_antisymm le_top
    rw [← hJperf, commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subtype.ext (Subgroup.mem_center_iff.mp (f a).2 (f b : L')).symm)
  have hf : f = 1 := MonoidHom.ker_eq_top_iff.mp hfker
  have hconj : ∀ y ∈ J, v * y * v⁻¹ = j * y * j⁻¹ := by
    intro y hy
    have h := congrArg (fun g : ↥J →* ↥(Subgroup.center L') => g ⟨y, hy⟩) hf
    have hz1 : (j * y * j⁻¹)⁻¹ * (v * y * v⁻¹) = 1 := by
      have h3 := congrArg (fun z : ↥(Subgroup.center L') => (z : L')) h
      simpa [f] using h3
    rw [inv_mul_eq_one] at hz1
    exact hz1.symm
  exact ⟨fun y hy => by
      rw [hconj y hy]
      exact J.mul_mem (J.mul_mem hjj hy) (J.inv_mem hjj),
    ⟨j, hjj, hconj⟩⟩

private theorem pg_hasLabel_of_mulEquiv {lab : LargeEvenLabel} {Q Q' : Type} [Group Q] [Group Q']
    (e : Q ≃* Q') (h : GGHasLabel lab Q) : GGHasLabel lab Q' :=
  largeEvenRawDatum_mono (fun _ _ _ _ ⟨f⟩ => ⟨e.symm.trans f⟩) h

theorem ggF4CentAt_of_core {p f : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hZ : Subgroup.center R = ⊥) (hI : ∀ φ ∈ I, ∃ r : R, φ = MulAut.conj r)
    (hcore : GGF4CoreAt p f R) : GGF4CentAt p f R I := by
  intro L' _ _ ψ hψ hker hperf e a hep he1 hea hIe hIa J hJ hC3
  obtain ⟨φe, hφeI, hφe⟩ := hIe
  obtain ⟨φa, hφaI, hφa⟩ := hIa
  obtain ⟨se, rfl⟩ := hI φe hφeI
  obtain ⟨ga, rfl⟩ := hI φa hφaI
  obtain ⟨u, rfl⟩ := hψ se
  obtain ⟨v, rfl⟩ := hψ ga
  have heu : e = MulAut.conj u := TypeA.mulAut_eq_of_forall ψ hker hperf fun l => by
    rw [← hφe l]
    simp [MulAut.conj_apply]
  have hav : a = MulAut.conj v := TypeA.mulAut_eq_of_forall ψ hker hperf fun l => by
    rw [← hφa l]
    simp [MulAut.conj_apply]
  subst heu
  subst hav
  have hcenter : ∀ z ∈ Subgroup.center L', ψ z ∈ Subgroup.center R := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro r
    obtain ⟨l, rfl⟩ := hψ r
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (Subgroup.mem_center_iff.mp hz l)
  have hs : (ψ u) ^ p = 1 := by
    have hz : u ^ p ∈ Subgroup.center L' := by
      rw [Subgroup.mem_center_iff]
      intro l
      have h := congrArg (fun m : MulAut L' => m l) hep
      simp only [← map_pow, MulAut.conj_apply, MulAut.one_apply] at h
      calc l * u ^ p = (u ^ p * l * (u ^ p)⁻¹) * u ^ p := by rw [h]
        _ = u ^ p * l := by group
    have := hcenter _ hz
    rw [hZ, Subgroup.mem_bot, map_pow] at this
    exact this
  have hs1 : ψ u ≠ 1 := by
    intro h1
    apply he1
    refine TypeA.mulAut_eq_of_forall ψ hker hperf fun l => ?_
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, h1]
    simp
  have hcomm : ψ u * ψ v = ψ v * ψ u := by
    have hab : ∀ r : R, (ψ u * ψ v) * r * (ψ u * ψ v)⁻¹ = (ψ v * ψ u) * r * (ψ v * ψ u)⁻¹ := by
      intro r
      obtain ⟨l, rfl⟩ := hψ r
      have h := congrArg (fun m : MulAut L' => ψ (m l)) hea
      simp only [Equiv.Perm.mul_apply, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv] at h
      simpa [mul_assoc] using h
    have hc : (ψ v * ψ u)⁻¹ * (ψ u * ψ v) ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro r
      have h := hab r
      have key : ((ψ v * ψ u)⁻¹ * (ψ u * ψ v)) * r * ((ψ v * ψ u)⁻¹ * (ψ u * ψ v))⁻¹ = r := by
        calc ((ψ v * ψ u)⁻¹ * (ψ u * ψ v)) * r * ((ψ v * ψ u)⁻¹ * (ψ u * ψ v))⁻¹
            = (ψ v * ψ u)⁻¹ * ((ψ u * ψ v) * r * (ψ u * ψ v)⁻¹) * (ψ v * ψ u) := by group
          _ = (ψ v * ψ u)⁻¹ * ((ψ v * ψ u) * r * (ψ v * ψ u)⁻¹) * (ψ v * ψ u) := by rw [h]
          _ = r := by group
      exact (mul_inv_eq_iff_eq_mul.mp key).symm
    rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hc
    exact hc.symm
  have hgmem : ψ v ∈ Subgroup.centralizer ({ψ u} : Set R) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
  obtain ⟨hSc, ⟨hSiso⟩⟩ := ggF4_image_component ψ hψ hker u hJ
  have hSlab : GGHasLabel ⟨.C, 3, f⟩ (J.map ψ ⧸ Subgroup.center (J.map ψ)) :=
    pg_hasLabel_of_mulEquiv hSiso.symm hC3
  have h1 := hcore (ψ u) hs hs1 (J.map ψ) hSc hSlab (ψ v) hgmem
  obtain ⟨hnorm, hinner⟩ := ggF4_lift_inner ψ hker hJ.2.2.1 v h1
  exact ⟨fun x hx => by rw [MulAut.conj_apply]; exact hnorm x hx,
    by
      obtain ⟨j, hj, hjy⟩ := hinner
      exact ⟨j, hj, fun x hx => by rw [MulAut.conj_apply]; exact hjy x hx⟩⟩

theorem ggF4C3CentInputStrong_of_core
    (hC : GGF4CoreInput) : GGF4C3CentInputStrong := by
  intro p hp hp2 f hf
  have h12 := largeEvenLabelAll_and (hC p hp hp2 f hf) (ggF4_basics_label (f := f))
  intro Q hQ
  refine largeEvenRawDatum_mono ?_ (h12 Q hQ)
  rintro R _ I F ⟨hq, hcore, hsimple, hnab, -, hI⟩
  have hZ : Subgroup.center R = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center R) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  exact ⟨hq, ggF4CentAt_of_core hZ hI hcore⟩

end KGA

end CFSG.StandardType

end
