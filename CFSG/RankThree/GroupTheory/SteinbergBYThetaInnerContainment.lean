module

public import CFSG.RankThree.GroupTheory.SteinbergCEThetaSubnormalDichotomy
public import CFSG.RankThree.GroupTheory.SteinbergBYAlphaTransport
public import CFSG.GroupTheory.ConjugatePairSubnormality
import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBY

open CFSG CFSG.RankThree CFSG.RankThree.GroupTheory CFSG.RankThree.LocalRank
open scoped commutatorElement

variable {H : Type*} [Group H]

theorem commutator_mem_of_inner {L : Subgroup H} {x y l : H}
    (hxL : x ∈ Subgroup.normalizer (L : Set H)) (hyx : y * x = x * y) (hl : l ∈ L)
    (hyl : ∀ z ∈ L, y * z * y⁻¹ = l * z * l⁻¹) :
    l * x * l⁻¹ * x⁻¹ ∈ L ∧ ∀ z ∈ L, (l * x * l⁻¹ * x⁻¹) * z = z * (l * x * l⁻¹ * x⁻¹) := by
  have hmemL : ∀ z ∈ L, x⁻¹ * z * x ∈ L := fun z hz =>
    (Subgroup.mem_normalizer_iff''.mp hxL z).mp hz
  have hmemL' : ∀ z ∈ L, x * z * x⁻¹ ∈ L := fun z hz =>
    (Subgroup.mem_normalizer_iff.mp hxL z).mp hz
  have hinv : ∀ z ∈ L, l⁻¹ * z * l = y⁻¹ * z * y := by
    intro z hz
    have h := hyl (l⁻¹ * z * l) (L.mul_mem (L.mul_mem (L.inv_mem hl) hz) hl)
    have h' : y * (l⁻¹ * z * l) * y⁻¹ = z := by rw [h]; group
    calc l⁻¹ * z * l = y⁻¹ * (y * (l⁻¹ * z * l) * y⁻¹) * y := by group
      _ = y⁻¹ * z * y := by rw [h']
  refine ⟨?_, fun z hz => ?_⟩
  · have := L.mul_mem hl (hmemL' _ (L.inv_mem hl))
    simpa only [mul_assoc] using this
  · have hw := hmemL z hz
    have h1 : l⁻¹ * (x⁻¹ * z * x) * l = y⁻¹ * (x⁻¹ * z * x) * y := hinv _ hw
    have hxy : x * y⁻¹ = y⁻¹ * x := by
      calc x * y⁻¹ = y⁻¹ * (y * x) * y⁻¹ := by group
        _ = y⁻¹ * (x * y) * y⁻¹ := by rw [hyx]
        _ = y⁻¹ * x := by group
    have h2 : x * (y⁻¹ * (x⁻¹ * z * x) * y) * x⁻¹ = y⁻¹ * z * y := by
      calc x * (y⁻¹ * (x⁻¹ * z * x) * y) * x⁻¹
          = (x * y⁻¹) * x⁻¹ * z * x * (x * y⁻¹)⁻¹ := by group
        _ = (y⁻¹ * x) * x⁻¹ * z * x * (y⁻¹ * x)⁻¹ := by rw [hxy]
        _ = y⁻¹ * z * y := by group
    have hyz : y⁻¹ * z * y ∈ L := by
      have := hinv z hz
      rw [← this]
      exact L.mul_mem (L.mul_mem (L.inv_mem hl) hz) hl
    have h3 : l * (y⁻¹ * z * y) * l⁻¹ = z := by
      rw [← hyl _ hyz]
      group
    calc (l * x * l⁻¹ * x⁻¹) * z
        = (l * (x * (l⁻¹ * (x⁻¹ * z * x) * l) * x⁻¹) * l⁻¹) * (l * x * l⁻¹ * x⁻¹) := by group
      _ = (l * (x * (y⁻¹ * (x⁻¹ * z * x) * y) * x⁻¹) * l⁻¹) * (l * x * l⁻¹ * x⁻¹) := by
          rw [h1]
      _ = (l * (y⁻¹ * z * y) * l⁻¹) * (l * x * l⁻¹ * x⁻¹) := by rw [h2]
      _ = z * (l * x * l⁻¹ * x⁻¹) := by rw [h3]

theorem local_theta_component_inner_containment_aux [Finite H] {p : ℕ} (hp : p.Prime) {x : H}
    {C : Subgroup H} (hC : C = Subgroup.centralizer ({x} : Set H)) {Y : Subgroup C}
    (hY : Y ∈ thetaComponents p C) {L : Subgroup H} (hL : IsComponent L)
    (hxL : x ∈ Subgroup.normalizer (L : Set H))
    (hYL : Y.map C.subtype ≤ Subgroup.normalizer (L : Set H))
    (hinner : ∀ y ∈ Y.map C.subtype, ∃ l ∈ L, ∀ z ∈ L, y * z * y⁻¹ = l * z * l⁻¹)
    (hnt : ⁅Y.map C.subtype, L⁆ ≠ ⊥) : Y.map C.subtype ≤ L := by
  set YH := Y.map C.subtype with hYH
  have hYHC : YH ≤ C := Subgroup.map_subtype_le _
  have hYHx : ∀ y ∈ YH, y * x = x * y := fun y hy => by
    have h := hYHC hy
    rw [hC] at h
    exact Subgroup.mem_centralizer_singleton_iff.mp h
  set Z := (Subgroup.center L).map L.subtype with hZ
  set X := Subgroup.zpowers x ⊔ Z with hX
  set M := Subgroup.normalizer (X : Set H) with hM
  set CX := Subgroup.centralizer (X : Set H) with hCX
  have hZL : Z ≤ L := Subgroup.map_subtype_le _
  have hZcomm : ∀ z ∈ Z, ∀ w ∈ L, z * w = w * z := by
    rintro _ ⟨z, hz, rfl⟩ w hw
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨w, hw⟩)).symm
  have hYCX : YH ≤ CX := by
    rw [hCX, Subgroup.le_centralizer_iff]
    refine sup_le (Subgroup.zpowers_le.mpr ?_) ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact hYHx y hy
    · intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨l, hl, hyl⟩ := hinner y hy
      have h := hyl z (hZL hz)
      rw [← hZcomm z hz l hl, mul_inv_cancel_right] at h
      calc y * z = y * z * y⁻¹ * y := by group
        _ = z * y := by rw [h]
  have hCXC : CX ≤ C := by
    rw [hC]
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers x)))
  have hCXM : CX ≤ M := Subgroup.centralizer_le_normalizer _
  have hYM : YH ≤ M := hYCX.trans hCXM
  set YM := YH.subgroupOf M with hYMdef
  have hYsubC : (YH.subgroupOf C).IsSubnormal := by
    have h : YH.subgroupOf C = Y := by
      rw [hYH, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
    rw [h]
    exact hY.2.1
  have hYsubCX : (YH.subgroupOf CX).IsSubnormal :=
    GroupTheory.isSubnormal_subgroupOf_of_le hCXC hYsubC
  have hCXsubM : (CX.subgroupOf M).IsSubnormal :=
    Subgroup.Normal.isSubnormal (Subgroup.normal_subgroupOf_centralizer_normalizer _)
  have hYMsub : YM.IsSubnormal :=
    GroupTheory.isSubnormal_subgroupOf_trans hYCX hCXM hYsubCX hCXsubM
  set e : Y ≃* YM := (Y.equivMapOfInjective C.subtype C.subtype_injective).trans
    (Subgroup.subgroupOfEquivOfLe hYM).symm with he
  have hYMtheta : YM ∈ thetaComponents p M := by
    refine ⟨?_, hYMsub, ?_⟩
    · have := hY.1
      exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    · exact LocalCores.isQuasisimple_of_mulEquiv
        (QuotientGroup.congr _ _ e (aschbacherSolvableCore_map_mulEquiv hp e)) hY.2.2
  have hUsub : (L.subgroupOf M).IsSubnormal := hL.2.subgroupOf
  rcases theta_component_subnormal_subgroup_dichotomy hp hYMtheta hUsub with hle | ⟨-, hcomm⟩
  · intro y hy
    exact hle (show (⟨y, hYM hy⟩ : M) ∈ YM from hy)
  · exfalso
    apply hnt
    set T := (inSubgroup (aschbacherSolvableCore p) YM).map M.subtype with hT
    have hTs : Group.IsSolvable T := by
      have := (solvable_prime_complement_core_characterization (H := YM) hp).1
      have : Group.IsSolvable (inSubgroup (aschbacherSolvableCore p) YM) :=
        Group.isSolvable_of_surjective (YM.subtype.subgroupMap_surjective _)
      exact Group.isSolvable_of_surjective (M.subtype.subgroupMap_surjective _)
    have hTYH : T ≤ YH := by
      rintro _ ⟨t, ht, rfl⟩
      have ht' : t ∈ YM := Subgroup.map_subtype_le _ ht
      exact ht'
    have hYUT : ⁅YH, L ⊓ M⁆ ≤ T := by
      have h := Subgroup.map_mono (f := M.subtype) hcomm
      rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
        Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hYM] at h
      exact h
    set NL := Subgroup.normalizer (L : Set H) with hNL
    set ρ := L.normalizerMonoidHom with hρ
    have hρapp : ∀ (g : NL) (z : L), ((ρ g z : L) : H) = g * z * (g : H)⁻¹ := fun g z => by
      rw [hρ, Subgroup.normalizerMonoidHom_apply_apply_coe]
    have hTNL : T ≤ NL := hTYH.trans hYL
    have hUNL : L ⊓ M ≤ NL := inf_le_left.trans Subgroup.le_normalizer
    set Y' := YH.subgroupOf NL
    set U' := (L ⊓ M).subgroupOf NL
    set T' := T.subgroupOf NL
    have hYU : Y'.map ρ ≤ U'.map ρ := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨l, hl, hyl⟩ := hinner y hy
      obtain ⟨hcL, hcZ⟩ := commutator_mem_of_inner hxL (hYHx y hy) hl hyl
      have hcZ' : l * x * l⁻¹ * x⁻¹ ∈ Z :=
        ⟨⟨_, hcL⟩, Subgroup.mem_center_iff.mpr fun w => Subtype.ext (hcZ w w.2).symm, rfl⟩
      have hlX : X.map (MulAut.conj l).toMonoidHom ≤ X := by
        rw [hX, Subgroup.map_sup, sup_le_iff]
        refine ⟨?_, ?_⟩
        · rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
          have : (MulAut.conj l).toMonoidHom x = (l * x * l⁻¹ * x⁻¹) * x := by
            simp [MulAut.conj_apply]
          rw [this]
          exact mul_mem (Subgroup.mem_sup_right hcZ') (Subgroup.mem_sup_left
            (Subgroup.mem_zpowers x))
        · rintro _ ⟨z, hz, rfl⟩
          have : (MulAut.conj l).toMonoidHom z = z := by
            simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
            rw [← hZcomm z hz l hl, mul_inv_cancel_right]
          rw [this]
          exact Subgroup.mem_sup_right hz
      have hlM : l ∈ M := by
        apply mem_normalizer_of_map_conj_eq
        exact Subgroup.eq_of_le_of_card_ge hlX (le_of_eq
          (Subgroup.card_map_of_injective (MulAut.conj l).injective).symm)
      refine ⟨⟨l, Subgroup.le_normalizer hl⟩, ⟨hl, hlM⟩, ?_⟩
      ext z
      rw [hρapp, hρapp]
      exact (hyl z z.2).symm
    have hYUT' : ⁅Y', U'⁆ ≤ T' := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      have := hYUT (Subgroup.commutator_mem_commutator ha hb)
      exact this
    have hY'perf : ⁅Y', Y'⁆ = Y' := by
      have hperf : Group.IsPerfect YH := by
        have := hY.1
        exact Group.IsPerfect.ofSurjective
          (f := (Y.equivMapOfInjective C.subtype C.subtype_injective).toMonoidHom)
          (Y.equivMapOfInjective C.subtype C.subtype_injective).surjective
      apply Subgroup.map_injective NL.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hYL]
      exact Subgroup.isPerfect_iff.mp hperf
    have hY'T' : Y'.map ρ ≤ T'.map ρ := by
      calc Y'.map ρ = ⁅Y'.map ρ, Y'.map ρ⁆ := by rw [← Subgroup.map_commutator, hY'perf]
        _ ≤ ⁅Y'.map ρ, U'.map ρ⁆ := Subgroup.commutator_mono le_rfl hYU
        _ = ⁅Y', U'⁆.map ρ := (Subgroup.map_commutator _ _ _).symm
        _ ≤ T'.map ρ := Subgroup.map_mono hYUT'
    have hT's : Group.IsSolvable (T'.map ρ) := by
      have : Group.IsSolvable T' := Group.isSolvable_of_surjective
        (f := (Subgroup.subgroupOfEquivOfLe hTNL).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hTNL).symm.surjective
      exact Group.isSolvable_of_surjective (ρ.subgroupMap_surjective _)
    have hY's : Group.IsSolvable (Y'.map ρ) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hY'T')
    have hY'p : Group.IsPerfect (Y'.map ρ) := by
      rw [Subgroup.isPerfect_iff, ← Subgroup.map_commutator, hY'perf]
    have hbot := eq_bot_of_isPerfect_of_isSolvable hY'p hY's
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro y hy z hz
    have hρy : ρ ⟨y, hYL hy⟩ = 1 := by
      have : ρ ⟨y, hYL hy⟩ ∈ Y'.map ρ := ⟨⟨y, hYL hy⟩, hy, rfl⟩
      rwa [hbot, Subgroup.mem_bot] at this
    have h := congrArg (fun φ : MulAut L => ((φ ⟨z, hz⟩ : L) : H)) hρy
    simp only [MulAut.one_apply] at h
    rw [hρapp] at h
    rw [Subgroup.mem_bot, commutatorElement_def, h, mul_inv_cancel]

theorem local_theta_component_nontrivial_inner_action_containment [Finite H] {p : ℕ}
    (hp : p.Prime) {x : H} {Y : Subgroup (Subgroup.centralizer ({x} : Set H))}
    (hY : Y ∈ thetaComponents p (Subgroup.centralizer ({x} : Set H))) {L : Subgroup H}
    (hL : IsComponent L) (hxL : x ∈ Subgroup.normalizer (L : Set H))
    (hYL : Y.map (Subgroup.centralizer ({x} : Set H)).subtype ≤
      Subgroup.normalizer (L : Set H))
    (hinner : ∀ y ∈ Y.map (Subgroup.centralizer ({x} : Set H)).subtype,
      ∃ l ∈ L, ∀ z ∈ L, y * z * y⁻¹ = l * z * l⁻¹)
    (hnt : ⁅Y.map (Subgroup.centralizer ({x} : Set H)).subtype, L⁆ ≠ ⊥) :
    Y.map (Subgroup.centralizer ({x} : Set H)).subtype ≤ L :=
  local_theta_component_inner_containment_aux hp rfl hY hL hxL hYL hinner hnt

end CFSG.RankThree.GroupTheory.SteinbergBY
