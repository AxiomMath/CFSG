module

public import CFSG.LocalAnalysis.StandardType.GGTCJCoverGen
public import CFSG.LocalAnalysis.StandardType.GGTCJDescent

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open
open scoped commutatorElement IsMulCommutative

private lemma ggK1Lift_commutatorElement_mul_center_left {G : Type*} [Group G] {n a b : G}
    (hn : n ∈ Subgroup.center G) : ⁅a * n, b⁆ = ⁅a, b⁆ := by
  have hnb : ⁅n, b⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 hn b).symm
  rw [commutatorElement_mul_left_eq_conj_mul, hnb]
  group

private lemma ggK1Lift_commutatorElement_mul_center_right {G : Type*} [Group G] {n a b : G}
    (hn : n ∈ Subgroup.center G) : ⁅a, b * n⁆ = ⁅a, b⁆ := by
  have han : ⁅a, n⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 hn a)
  rw [commutatorElement_mul_right_eq_mul_conj, han]
  group

private theorem ggK1Lift_e_mem_comap {L' R : Type*} [Group L'] [Group R] (ψ : L' →* R)
    (e : MulAut L') (φ : MulAut R) (hφ : ∀ l : L', φ (ψ l) = ψ (e l)) {K : Subgroup R}
    (hKle : K ≤ ggFixSub φ) {x : L'} (hx : x ∈ K.comap ψ) : e x ∈ K.comap ψ := by
  rw [Subgroup.mem_comap] at hx ⊢
  rw [← hφ x, mem_ggFixSub.1 (hKle hx)]
  exact hx

private def ggK1Lift_z {L' R : Type*} [Group L'] [Group R] (ψ : L' →* R) (e : MulAut L')
    (φ : MulAut R) (hφ : ∀ l : L', φ (ψ l) = ψ (e l)) {K : Subgroup R}
    (hKle : K ≤ ggFixSub φ) (hker : ψ.ker ≤ Subgroup.center L') :
    ↥(K.comap ψ) →* ↥(Subgroup.center L') where
  toFun x := ⟨(x : L')⁻¹ * e x, by
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hφ (x : L'), mem_ggFixSub.1 (hKle x.2),
      inv_mul_cancel]⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    have hcx : (x : L')⁻¹ * e x ∈ Subgroup.center L' := by
      apply hker
      rw [MonoidHom.mem_ker, map_mul, map_inv, ← hφ (x : L'), mem_ggFixSub.1 (hKle x.2),
        inv_mul_cancel]
    have hcomm : (y : L')⁻¹ * ((x : L')⁻¹ * e x) =
        ((x : L')⁻¹ * e x) * (y : L')⁻¹ :=
      Subgroup.mem_center_iff.1 hcx (y : L')⁻¹
    change ((x : L') * (y : L'))⁻¹ * e ((x : L') * (y : L')) =
      ((x : L')⁻¹ * e (x : L')) * ((y : L')⁻¹ * e (y : L'))
    calc ((x : L') * (y : L'))⁻¹ * e ((x : L') * (y : L'))
        = (y : L')⁻¹ * (x : L')⁻¹ * (e (x : L') * e (y : L')) := by
          rw [map_mul, mul_inv_rev]
      _ = (y : L')⁻¹ * ((x : L')⁻¹ * e (x : L')) * e (y : L') := by group
      _ = ((x : L')⁻¹ * e (x : L')) * (y : L')⁻¹ * e (y : L') := by rw [hcomm]
      _ = ((x : L')⁻¹ * e (x : L')) * ((y : L')⁻¹ * e (y : L')) := by group

private theorem ggK1Lift_commutator_le_fixSub {L' R : Type*} [Group L'] [Group R]
    (ψ : L' →* R) (e : MulAut L') (φ : MulAut R) (hφ : ∀ l : L', φ (ψ l) = ψ (e l))
    {K : Subgroup R} (hKle : K ≤ ggFixSub φ) (hker : ψ.ker ≤ Subgroup.center L') :
    ⁅K.comap ψ, K.comap ψ⁆ ≤ ggFixSub e := by
  let z : ↥(K.comap ψ) →* ↥(Subgroup.center L') := ggK1Lift_z ψ e φ hφ hKle hker
  have hkerz : commutator ↥(K.comap ψ) ≤ z.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm (z a) (z b)
  rw [← Subgroup.map_subtype_commutator (K.comap ψ)]
  intro y hy
  rw [Subgroup.mem_map] at hy
  obtain ⟨q, hq, rfl⟩ := hy
  have hzq : z q = 1 := by simpa [MonoidHom.mem_ker] using hkerz hq
  rw [mem_ggFixSub]
  change e (q : L') = (q : L')
  have h := congrArg (fun s : ↥(Subgroup.center L') => (s : L')) hzq
  change (q : L')⁻¹ * e (q : L') = 1 at h
  calc e (q : L') = (q : L') * ((q : L')⁻¹ * e (q : L')) := by group
    _ = (q : L') * 1 := by rw [h]
    _ = (q : L') := by simp

theorem ggK1_lift_component {R L' : Type} [Group R] [Group L'] (ψ : L' →* R)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (e : MulAut L')
    (φ : MulAut R) (hφ : ∀ l : L', φ (ψ l) = ψ (e l)) {K : Subgroup R}
    (hK : CFSG.Assembly.IsComponentOf K (ggFixSub φ)) :
    ∃ J : Subgroup L', CFSG.Assembly.IsComponentOf J (ggFixSub e) ∧
      Nonempty ((J ⧸ Subgroup.center J) ≃* (K ⧸ Subgroup.center K)) := by
  obtain ⟨hKle, hKsub, hKperf, hKsimple⟩ := hK
  let P : Subgroup L' := K.comap ψ
  let Q : Subgroup L' := ⁅P, P⁆
  have hPmap : P.map ψ = K := Subgroup.map_comap_eq_self_of_surjective hψ K
  have hQK : Q.map ψ = K := by
    dsimp only [Q]
    rw [Subgroup.map_commutator, hPmap, ← Subgroup.map_subtype_commutator K, hKperf,
      Subgroup.map_top, Subgroup.range_subtype]
  have hQleP : Q ≤ P := Subgroup.commutator_le_self P
  have hQleC' : Q ≤ ggFixSub e := ggK1Lift_commutator_le_fixSub ψ e φ hφ hKle hker
  have hQleQQ : Q ≤ ⁅Q, Q⁆ := by
    dsimp only [Q]
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hKa : ψ a ∈ K := Subgroup.mem_comap.1 ha
    have hKb : ψ b ∈ K := Subgroup.mem_comap.1 hb
    obtain ⟨q, hqQ, hqψ⟩ := Subgroup.mem_map.1 (by rw [hQK]; exact hKa)
    obtain ⟨q', hq'Q, hq'ψ⟩ := Subgroup.mem_map.1 (by rw [hQK]; exact hKb)
    have hna : q⁻¹ * a ∈ Subgroup.center L' := by
      apply hker
      rw [MonoidHom.mem_ker, map_mul, map_inv, hqψ, inv_mul_cancel]
    have hnb : (q')⁻¹ * b ∈ Subgroup.center L' := by
      apply hker
      rw [MonoidHom.mem_ker, map_mul, map_inv, hq'ψ, inv_mul_cancel]
    have hcomm : ⁅a, b⁆ = ⁅q, q'⁆ := by
      calc ⁅a, b⁆ = ⁅q * (q⁻¹ * a), q' * ((q')⁻¹ * b)⁆ := by
            rw [mul_inv_cancel_left, mul_inv_cancel_left]
        _ = ⁅q, q' * ((q')⁻¹ * b)⁆ := ggK1Lift_commutatorElement_mul_center_left hna
        _ = ⁅q, q'⁆ := ggK1Lift_commutatorElement_mul_center_right hnb
    rw [hcomm]
    exact Subgroup.commutator_mem_commutator hqQ hq'Q
  have hQQ : ⁅Q, Q⁆ = Q := le_antisymm (Subgroup.commutator_le_self Q) hQleQQ
  have hQperf : commutator ↥Q = ⊤ := by
    have hmap := Subgroup.map_subtype_commutator Q
    rw [hQQ] at hmap
    refine (Subgroup.map_subtype_inj (H := Q)).1 ?_
    rw [hmap, Subgroup.map_top, Subgroup.range_subtype]
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
  have hC'le : ggFixSub e ≤ (ggFixSub φ).comap ψ := by
    intro l hl
    rw [Subgroup.mem_comap, mem_ggFixSub]
    rw [hφ l, mem_ggFixSub.1 hl]
  have hPsub : CFSG.Assembly.IsSubnormal P ((ggFixSub φ).comap ψ) :=
    CFSG.Assembly.IsSubnormal.comap ψ hKsub
  have hsub1 : CFSG.Assembly.IsSubnormal (P ⊓ ggFixSub e) (ggFixSub e) := by
    have h := hPsub.inf (ggFixSub e)
    rwa [inf_eq_right.2 hC'le] at h
  have hQnormal : (Q.subgroupOf (P ⊓ ggFixSub e)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_inf hQleP hQleC')).2
      (inf_le_left.trans (Subgroup.normalizer_commutator_ge_left P P))
  have hsubQ : CFSG.Assembly.IsSubnormal Q (ggFixSub e) :=
    CFSG.Assembly.IsSubnormal.step (le_inf hQleP hQleC') hQnormal hsub1
  exact ⟨Q, ⟨⟨hQleC', hsubQ, hQperf, hQsimple⟩, ⟨eqv⟩⟩⟩

end CFSG.StandardType

end
