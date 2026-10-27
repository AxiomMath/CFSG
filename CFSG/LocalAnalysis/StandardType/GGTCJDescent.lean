module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType.TCJ

open CFSG.Open CFSG.Assembly

theorem tcjDescent_fixSub_map_le {L' R : Type} [Group L'] [Group R] (ψ : L' →* R)
    (e : MulAut L') (φ : MulAut R) (hφ : ∀ l : L', φ (ψ l) = ψ (e l)) :
    (ggFixSub e).map ψ ≤ ggFixSub φ := by
  rintro _ ⟨l, hl, rfl⟩
  rw [mem_ggFixSub, hφ, mem_ggFixSub.1 hl]

theorem tcjDescent_fixSub_map_normal {L' R : Type} [Group L'] [Group R] (ψ : L' →* R)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (e : MulAut L')
    (φ : MulAut R) (hφ : ∀ l : L', φ (ψ l) = ψ (e l)) :
    (((ggFixSub e).map ψ).subgroupOf (ggFixSub φ)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (tcjDescent_fixSub_map_le ψ e φ hφ)]
  rintro _ g ⟨l0, hl0, rfl⟩ hg
  obtain ⟨lr, rfl⟩ := hψ g
  have hz : lr⁻¹ * e lr ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hφ, mem_ggFixSub.1 hg, inv_mul_cancel]
  have hzc := hker hz
  have h0 : e l0 = l0 := mem_ggFixSub.1 hl0
  have hzl : (lr⁻¹ * e lr) * l0 = l0 * (lr⁻¹ * e lr) := (Subgroup.mem_center_iff.1 hzc l0).symm
  have hconj : (lr⁻¹ * e lr) * l0 * (lr⁻¹ * e lr)⁻¹ = l0 := by
    rw [hzl]; group
  refine ⟨lr * l0 * lr⁻¹, ?_, by simp⟩
  rw [SetLike.mem_coe, mem_ggFixSub, map_mul, map_mul, map_inv, h0]
  calc e lr * l0 * (e lr)⁻¹
      = lr * ((lr⁻¹ * e lr) * l0 * (lr⁻¹ * e lr)⁻¹) * lr⁻¹ := by group
    _ = lr * l0 * lr⁻¹ := by rw [hconj]

theorem tcjDescent_commutator_map_eq_top {L' R : Type} [Group L'] [Group R] {J : Subgroup L'}
    (hJ : commutator ↥J = ⊤) (ψ : L' →* R) : commutator ↥(J.map ψ) = ⊤ := by
  have hf : Function.Surjective (ψ.subgroupMap J) := ψ.subgroupMap_surjective J
  have h1 : (commutator ↥J).map (ψ.subgroupMap J) = commutator ↥(J.map ψ) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      MonoidHom.range_eq_top_of_surjective _ hf]
  rw [← h1, hJ, Subgroup.map_top, MonoidHom.range_eq_top_of_surjective _ hf]

theorem tcjDescent_center_comap_eq {L' R : Type} [Group L'] [Group R] {J : Subgroup L'}
    (ψ : L' →* R) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator ↥(J.map ψ) = ⊤)
    (hsimple : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J)) :
    (Subgroup.center ↥(J.map ψ)).comap (ψ.subgroupMap J) = Subgroup.center ↥J := by
  have hf : Function.Surjective (ψ.subgroupMap J) := ψ.subgroupMap_surjective J
  have hle : Subgroup.center ↥J ≤ (Subgroup.center ↥(J.map ψ)).comap (ψ.subgroupMap J) := by
    intro z hz
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro g
    obtain ⟨j, rfl⟩ := hf g
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz j)]
  refine le_antisymm ?_ hle
  haveI hN : ((Subgroup.center ↥(J.map ψ)).comap (ψ.subgroupMap J)).Normal := inferInstance
  haveI hN' : (((Subgroup.center ↥(J.map ψ)).comap (ψ.subgroupMap J)).map
      (QuotientGroup.mk' (Subgroup.center ↥J))).Normal :=
    hN.map _ (QuotientGroup.mk'_surjective _)
  rcases hsimple.eq_bot_or_eq_top_of_normal (((Subgroup.center ↥(J.map ψ)).comap
      (ψ.subgroupMap J)).map (QuotientGroup.mk' (Subgroup.center ↥J))) with h | h
  · intro x hx
    have h1 : QuotientGroup.mk' (Subgroup.center ↥J) x ∈ ((Subgroup.center ↥(J.map ψ)).comap
        (ψ.subgroupMap J)).map (QuotientGroup.mk' (Subgroup.center ↥J)) :=
      Subgroup.mem_map_of_mem _ hx
    rw [h, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff x).1 h1
  · exfalso
    have htop : ∀ x : ↥J, x ∈ (Subgroup.center ↥(J.map ψ)).comap (ψ.subgroupMap J) := by
      intro x
      have hx : QuotientGroup.mk' (Subgroup.center ↥J) x ∈ ((Subgroup.center ↥(J.map ψ)).comap
          (ψ.subgroupMap J)).map (QuotientGroup.mk' (Subgroup.center ↥J)) := by
        rw [h]; trivial
      obtain ⟨y, hy, hxy⟩ := hx
      have hyx : y⁻¹ * x ∈ Subgroup.center ↥J := by
        rw [← QuotientGroup.eq]
        exact hxy
      have := mul_mem hy (hle hyx)
      simpa using this
    have hcomm : ∀ a b : ↥(J.map ψ), a * b = b * a := by
      intro a b
      obtain ⟨x, rfl⟩ := hf a
      exact ((Subgroup.mem_center_iff.1 (htop x)) b).symm
    have hbot : commutator ↥(J.map ψ) ≤ ⊥ := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      exact Subgroup.mem_bot.2 (commutatorElement_eq_one_iff_mul_comm.2 (hcomm a b))
    rw [hperf] at hbot
    have hone : ∀ a : ↥(J.map ψ), a = 1 := fun a =>
      Subgroup.mem_bot.1 (hbot (Subgroup.mem_top a))
    have hcentJ : ∀ x : ↥J, x ∈ Subgroup.center ↥J := by
      intro x
      have hx1 : ψ.subgroupMap J x = 1 := hone _
      have hx2 : ψ (x : L') = 1 := by
        have := congrArg Subtype.val hx1
        simpa using this
      rw [Subgroup.mem_center_iff]
      intro g
      have hc := Subgroup.mem_center_iff.1 (hker hx2) (g : L')
      exact Subtype.ext hc
    haveI := hsimple.toNontrivial
    obtain ⟨a, b, hab⟩ := exists_pair_ne (↥J ⧸ Subgroup.center ↥J)
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    rw [(QuotientGroup.eq_one_iff a').2 (hcentJ a'), (QuotientGroup.eq_one_iff b').2 (hcentJ b')]

theorem ggTCJ_descent {L' R : Type} [Group L'] [Group R]
    (ψ : L' →* R) (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (e : MulAut L') (φ : MulAut R) (hφ : ∀ l : L', φ (ψ l) = ψ (e l)) (J : Subgroup L')
    (hJ : CFSG.Assembly.IsComponentOf J (ggFixSub e)) :
    CFSG.Assembly.IsComponentOf (J.map ψ) (ggFixSub φ) ∧
      Nonempty ((J ⧸ Subgroup.center J) ≃* ((J.map ψ) ⧸ Subgroup.center (J.map ψ))) := by
  obtain ⟨hJle, hJsub, hJperf, hJsimple⟩ := hJ
  have hf : Function.Surjective (ψ.subgroupMap J) := ψ.subgroupMap_surjective J
  have hle : (ggFixSub e).map ψ ≤ ggFixSub φ := tcjDescent_fixSub_map_le ψ e φ hφ
  have hsub : CFSG.Assembly.IsSubnormal (J.map ψ) (ggFixSub φ) :=
    (hJsub.map ψ).trans (.step hle (tcjDescent_fixSub_map_normal ψ hψ hker e φ hφ) (.refl _))
  have hperf' : commutator ↥(J.map ψ) = ⊤ := tcjDescent_commutator_map_eq_top hJperf ψ
  have hcen := tcjDescent_center_comap_eq (J := J) ψ hker hperf' hJsimple
  let g : (↥J ⧸ Subgroup.center ↥J) →* (↥(J.map ψ) ⧸ Subgroup.center ↥(J.map ψ)) :=
    QuotientGroup.map (Subgroup.center ↥J) (Subgroup.center ↥(J.map ψ)) (ψ.subgroupMap J)
      (le_of_eq hcen.symm)
  have hginj : Function.Injective g := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_map, hcen]
    ext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    simp [Subgroup.mem_map, QuotientGroup.eq_one_iff]
  have hgsurj : Function.Surjective g := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨QuotientGroup.mk x, rfl⟩
  let eqv : (↥J ⧸ Subgroup.center ↥J) ≃* (↥(J.map ψ) ⧸ Subgroup.center ↥(J.map ψ)) :=
    MulEquiv.ofBijective g ⟨hginj, hgsurj⟩
  have hsimple' : IsSimpleGroup (↥(J.map ψ) ⧸ Subgroup.center ↥(J.map ψ)) :=
    MulEquiv.isSimpleGroup eqv.symm
  exact ⟨⟨(Subgroup.map_mono hJle).trans hle, hsub, hperf', hsimple'⟩, ⟨eqv⟩⟩

end CFSG.StandardType.TCJ

end
