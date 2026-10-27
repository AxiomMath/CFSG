module

public import CFSG.LocalAnalysis.StandardType.GGK1LiftComp
public import CFSG.LocalAnalysis.StandardType.GGKacK0V2
public import CFSG.LocalAnalysis.StandardType.GGTCJDescent
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixPerfect
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

open scoped commutatorElement IsMulCommutative

private theorem ggK1Cb_core_le_component {L' R : Type} [Group L'] [Group R] (ψ : L' →* R)
    (hker : ψ.ker ≤ Subgroup.center L') {J : Subgroup L'}
    (hJ : commutator ↥J = ⊤) :
    ⁅(J.map ψ).comap ψ, (J.map ψ).comap ψ⁆ ≤ J := by
  have hJset : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hJ)
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hxψ : ψ x ∈ J.map ψ := Subgroup.mem_comap.mp hx
  have hyψ : ψ y ∈ J.map ψ := Subgroup.mem_comap.mp hy
  obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hxψ
  obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.mp hyψ
  have hzx : a⁻¹ * x ∈ Subgroup.center L' := by
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hax, inv_mul_cancel]
  have hzy : b⁻¹ * y ∈ Subgroup.center L' := by
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hby, inv_mul_cancel]
  have hx' : x = a * (a⁻¹ * x) := by group
  have hy' : y = b * (b⁻¹ * y) := by group
  rw [hx', hy', ggComm_mul_central a b (a⁻¹ * x) (b⁻¹ * y) hzx hzy]
  exact hJset ▸ Subgroup.commutator_mem_commutator ha hb

private theorem ggK1Cb_map_injective {L' R : Type} [Group L'] [Group R] (ψ : L' →* R)
    (hker : ψ.ker ≤ Subgroup.center L') {J₁ J₂ : Subgroup L'}
    (h₁ : commutator ↥J₁ = ⊤) (h₂ : commutator ↥J₂ = ⊤)
    (hmap : J₁.map ψ = J₂.map ψ) : J₁ = J₂ := by
  have hJ₁perf : ⁅J₁, J₁⁆ = J₁ := Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr h₁)
  have hJ₂perf : ⁅J₂, J₂⁆ = J₂ := Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr h₂)
  have hle : J₁ ≤ J₂ := by
    have hle' : J₁ ≤ (J₂.map ψ).comap ψ := by
      intro x hx
      rw [Subgroup.mem_comap, ← hmap]
      exact Subgroup.mem_map_of_mem ψ hx
    calc J₁ = ⁅J₁, J₁⁆ := hJ₁perf.symm
      _ ≤ ⁅(J₂.map ψ).comap ψ, (J₂.map ψ).comap ψ⁆ :=
            Subgroup.commutator_mono hle' hle'
      _ ≤ J₂ := ggK1Cb_core_le_component ψ hker h₂
  have hle' : J₂ ≤ J₁ := by
    have hle'' : J₂ ≤ (J₁.map ψ).comap ψ := by
      intro x hx
      rw [Subgroup.mem_comap, hmap]
      exact Subgroup.mem_map_of_mem ψ hx
    calc J₂ = ⁅J₂, J₂⁆ := hJ₂perf.symm
      _ ≤ ⁅(J₁.map ψ).comap ψ, (J₁.map ψ).comap ψ⁆ :=
            Subgroup.commutator_mono hle'' hle''
      _ ≤ J₁ := ggK1Cb_core_le_component ψ hker h₁
  exact le_antisymm hle hle'

private theorem ggK1Cb_core_component {L' R : Type} [Group L'] [Group R] (ψ : L' →* R)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (e : MulAut L')
    (φ : MulAut R) (hφ : ∀ l : L', φ (ψ l) = ψ (e l)) {K : Subgroup R}
    (hK : CFSG.Assembly.IsComponentOf K (ggFixSub φ)) :
    CFSG.Assembly.IsComponentOf ⁅K.comap ψ, K.comap ψ⁆ (ggFixSub e) ∧
      (⁅K.comap ψ, K.comap ψ⁆).map ψ = K := by
  obtain ⟨hKle, hKsub, hKperf, hKsimple⟩ := hK
  let P : Subgroup L' := K.comap ψ
  let Q : Subgroup L' := ⁅P, P⁆
  have hPmap : P.map ψ = K := Subgroup.map_comap_eq_self_of_surjective hψ K
  have hQK : Q.map ψ = K := by
    dsimp only [Q]
    rw [Subgroup.map_commutator, hPmap, ← Subgroup.map_subtype_commutator K, hKperf,
      Subgroup.map_top, Subgroup.range_subtype]
  have hKperfSet : ⁅K, K⁆ = K := by
    rw [← Subgroup.map_subtype_commutator K, hKperf, Subgroup.map_top, Subgroup.range_subtype]
  have hQperfect : ⁅Q, Q⁆ = Q := (ggPerfectCore ψ hψ hker K hKperfSet).2
  have hQperf : commutator ↥Q = ⊤ :=
    Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hQperfect)
  have hQleC' : Q ≤ ggFixSub e :=
    ggFixes_core ψ hker e φ (fun l => (hφ l).symm) P
      (fun _ hl => mem_ggFixSub.mp (hKle (Subgroup.mem_comap.mp hl)))
  have hC'le : ggFixSub e ≤ (ggFixSub φ).comap ψ := by
    intro l hl
    rw [Subgroup.mem_comap, mem_ggFixSub]
    rw [hφ l, mem_ggFixSub.1 hl]
  have hPsub : CFSG.Assembly.IsSubnormal P ((ggFixSub φ).comap ψ) := hKsub.comap ψ
  have hsub1 : CFSG.Assembly.IsSubnormal (P ⊓ ggFixSub e) (ggFixSub e) := by
    have h := hPsub.inf (ggFixSub e)
    rwa [inf_eq_right.2 hC'le] at h
  have hQleP : Q ≤ P := Subgroup.commutator_le_self P
  have hQnormal : (Q.subgroupOf (P ⊓ ggFixSub e)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_inf hQleP hQleC')).2
      (inf_le_left.trans (Subgroup.normalizer_commutator_ge_left P P))
  have hsubQ : CFSG.Assembly.IsSubnormal Q (ggFixSub e) :=
    CFSG.Assembly.IsSubnormal.step (le_inf hQleP hQleC') hQnormal hsub1
  let f : ↥Q →* ↥K :=
    { toFun := fun x => ⟨ψ x, by rw [← hQK]; exact Subgroup.mem_map_of_mem ψ x.2⟩
      map_one' := Subtype.ext (map_one ψ)
      map_mul' := fun x y => Subtype.ext (map_mul ψ (x : L') (y : L')) }
  have hf_surj : Function.Surjective f := by
    intro k
    have hk : (k : R) ∈ Q.map ψ := by rw [hQK]; exact k.2
    obtain ⟨q, hqQ, hqk⟩ := Subgroup.mem_map.1 hk
    exact ⟨⟨q, hqQ⟩, Subtype.ext (by simpa [f] using hqk)⟩
  have hcenter_le : Subgroup.center ↥Q ≤ (Subgroup.center ↥K).comap f := by
    intro z hz
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro k
    obtain ⟨q, rfl⟩ := hf_surj k
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz q]
  have hcenter_ge : (Subgroup.center ↥K).comap f ≤ Subgroup.center ↥Q := by
    intro x hx
    have hmem : ∀ y : ↥Q, ⁅(x : L'), (y : L')⁆ ∈ ψ.ker := by
      intro y
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 (by
        have := congrArg (fun s : ↥K => (s : R))
          (Subgroup.mem_center_iff.1 hx (f y)).symm
        simpa [f] using this)
    let δ : ↥Q →* ↥(Subgroup.center L') :=
      { toFun := fun y => ⟨⁅(x : L'), (y : L')⁆, hker (hmem y)⟩
        map_one' := by
          apply Subtype.ext
          simp
        map_mul' := fun y z => by
          apply Subtype.ext
          have hzc : (⁅(x : L'), (z : L')⁆) ∈ Subgroup.center L' := hker (hmem z)
          have hcomm : (y : L') * (⁅(x : L'), (z : L')⁆) =
              (⁅(x : L'), (z : L')⁆) * (y : L') :=
            Subgroup.mem_center_iff.1 hzc (y : L')
          have hconj : (y : L') * ⁅(x : L'), (z : L')⁆ * (y : L')⁻¹ =
              ⁅(x : L'), (z : L')⁆ := by
            rw [hcomm]; group
          change ⁅(x : L'), (y : L') * (z : L')⁆ =
            ⁅(x : L'), (y : L')⁆ * ⁅(x : L'), (z : L')⁆
          calc ⁅(x : L'), (y : L') * (z : L')⁆
              = ⁅(x : L'), (y : L')⁆ * (y : L') * ⁅(x : L'), (z : L')⁆ * (y : L')⁻¹ :=
                commutatorElement_mul_right_eq_mul_conj (x : L') (y : L') (z : L')
            _ = ⁅(x : L'), (y : L')⁆ *
                  ((y : L') * ⁅(x : L'), (z : L')⁆ * (y : L')⁻¹) := by group
            _ = ⁅(x : L'), (y : L')⁆ * ⁅(x : L'), (z : L')⁆ := by rw [hconj] }
    have hδker : commutator ↥Q ≤ δ.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro u _ v _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm (δ u) (δ v)
    rw [Subgroup.mem_center_iff]
    intro y
    have hy : y ∈ δ.ker := by
      have : y ∈ commutator ↥Q := by rw [hQperf]; trivial
      exact hδker this
    have h1 : δ y = 1 := by simpa [MonoidHom.mem_ker] using hy
    have h2 : ⁅(x : L'), (y : L')⁆ = 1 := by
      have := congrArg (fun s : ↥(Subgroup.center L') => (s : L')) h1
      simpa [δ] using this
    exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.1 h2).symm
  have hcen : (Subgroup.center ↥K).comap f = Subgroup.center ↥Q :=
    le_antisymm hcenter_ge hcenter_le
  let g : (↥Q ⧸ Subgroup.center ↥Q) →* (↥K ⧸ Subgroup.center ↥K) :=
    QuotientGroup.map (Subgroup.center ↥Q) (Subgroup.center ↥K) f (le_of_eq hcen.symm)
  have hginj : Function.Injective g := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_map, hcen]
    ext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    simp [Subgroup.mem_map, QuotientGroup.eq_one_iff]
  have hgsurj : Function.Surjective g := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨x, rfl⟩ := hf_surj y
    exact ⟨QuotientGroup.mk x, rfl⟩
  let eqv : (↥Q ⧸ Subgroup.center ↥Q) ≃* (↥K ⧸ Subgroup.center ↥K) :=
    MulEquiv.ofBijective g ⟨hginj, hgsurj⟩
  have hQsimple : IsSimpleGroup (↥Q ⧸ Subgroup.center ↥Q) := by
    haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hKsimple
    exact eqv.isSimpleGroup
  exact ⟨⟨hQleC', hsubQ, hQperf, hQsimple⟩, hQK⟩

theorem ggK1_cover_bij {D : GGKacDatum} {R L' : Type} [Group R] [Group L'] [Finite L']
    (ψ : L' →* R) (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (e : MulAut L') (φ : MulAut R) (hφ : ∀ l : L', φ (ψ l) = ψ (e l))
    (hcore : GGKacCompBij D R φ) : GGKacCompBij D L' e := by
  obtain ⟨f, hf⟩ := hcore
  let Φ : {J : Subgroup L' // CFSG.Assembly.IsComponentOf J (ggFixSub e)} →
      {K : Subgroup R // CFSG.Assembly.IsComponentOf K (ggFixSub φ)} :=
    fun J => ⟨J.1.map ψ, (TCJ.ggTCJ_descent ψ hψ hker e φ hφ J.1 J.2).1⟩
  have hΦ_inj : Function.Injective Φ := by
    rintro ⟨J₁, h₁⟩ ⟨J₂, h₂⟩ heq
    have hmap : J₁.map ψ = J₂.map ψ := congrArg Subtype.val heq
    exact Subtype.ext (ggK1Cb_map_injective ψ hker h₁.2.2.1 h₂.2.2.1 hmap)
  have hΦ_surj : Function.Surjective Φ := by
    rintro ⟨K, hK⟩
    obtain ⟨hcomp, hmap⟩ := ggK1Cb_core_component ψ hψ hker e φ hφ hK
    exact ⟨⟨_, hcomp⟩, Subtype.ext hmap⟩
  let Φe : {J : Subgroup L' // CFSG.Assembly.IsComponentOf J (ggFixSub e)} ≃
      {K : Subgroup R // CFSG.Assembly.IsComponentOf K (ggFixSub φ)} :=
    Equiv.ofBijective Φ ⟨hΦ_inj, hΦ_surj⟩
  refine ⟨Φe.trans f, ?_⟩
  intro J
  obtain ⟨-, ⟨eqv⟩⟩ := TCJ.ggTCJ_descent ψ hψ hker e φ hφ J.1 J.2
  simpa only [Equiv.trans_apply] using ggHasLabel_of_mulEquiv eqv.symm (hf (Φe J))

end CFSG.StandardType

end
