module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.BAuxAct
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.KAPIHypB

public section

open CFSG.SignalizerFunctorTheorem.Nonsolvable CFSG.SignalizerFunctorTheorem.McBride
  CFSG.SignalizerFunctorTheorem.McBride.Near.KAPI

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.BAux

theorem normal_map_perfectResidual {Y : Type*} [Group Y] [Finite Y] (W : Subgroup Y)
    [hW : W.Normal] : ((CFSG.perfectResidual W).map W.subtype).Normal := by
  have h := normalizer_le_normalizer_perfectResidual_map W
  rw [Subgroup.normalizer_eq_top_iff.mpr hW, top_le_iff] at h
  exact Subgroup.normalizer_eq_top_iff.mp h

theorem normal_perfectResidual_of_normal_normal {X : Type*} [Group X] [Finite X]
    (hX : oStar X = ⊤) (Y : Subgroup X) [hY : Y.Normal] (W : Subgroup Y) [hW : W.Normal] :
    (((CFSG.perfectResidual W).map W.subtype).map Y.subtype).Normal := by
  set R := CFSG.solvableRadical X with hR
  have hRs : Group.IsSolvable R := isSolvable_solvableRadical
  set π := QuotientGroup.mk' R with hπ
  have hSS : DirFac (X ⧸ R) := dirFac_of_oStar_eq_top hX
  set D : Subgroup Y := (CFSG.perfectResidual W).map W.subtype with hD
  have hDn : D.Normal := normal_map_perfectResidual W
  set WX : Subgroup X := W.map Y.subtype with hWX
  set DX : Subgroup X := D.map Y.subtype with hDX
  have hDW : D ≤ W := Subgroup.map_subtype_le _
  have hDXW : DX ≤ WX := Subgroup.map_mono hDW
  have hYb : (Y.map π).Normal :=
    Subgroup.Normal.map hY π (QuotientGroup.mk'_surjective _)
  have hWb : (WX.map π).Normal := by
    refine hSS.normal_of_conj_closed (N := Y.map π)
      (Subgroup.map_mono (Subgroup.map_subtype_le W)) ?_
    rintro _ ⟨y, hy, rfl⟩ _ ⟨w, hw, rfl⟩
    obtain ⟨w', hw', rfl⟩ := hw
    refine ⟨y * w' * y⁻¹, ⟨⟨y, hy⟩ * w' * ⟨y, hy⟩⁻¹, hW.conj_mem w' hw' ⟨y, hy⟩, rfl⟩, ?_⟩
    simp
  have hDb : (DX.map π).Normal := by
    refine hSS.normal_of_conj_closed (N := WX.map π) (Subgroup.map_mono hDXW) ?_
    rintro _ ⟨w, hw, rfl⟩ _ ⟨d, hd, rfl⟩
    obtain ⟨w', hw', rfl⟩ := hw
    obtain ⟨d', hd', rfl⟩ := hd
    have hw'Y : (w' : X) ∈ Y := w'.2
    refine ⟨(w' : X) * (d' : X) * (w' : X)⁻¹, ?_, by simp⟩
    exact ⟨w' * d' * w'⁻¹, hDn.conj_mem d' hd' w', rfl⟩
  have hnorm : (DX ⊔ R).Normal := by
    have hcomap : (DX.map π).comap π = DX ⊔ R := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    rw [← hcomap]
    exact hDb.comap π
  have hDp : Group.IsPerfect D := isPerfect_perfectResidual_map W
  have hDXp : Group.IsPerfect DX := Group.IsPerfect.map (f := Y.subtype)
  have hDXs : DX.IsSubnormal := by
    refine Subgroup.IsSubnormal.step DX Y (Subgroup.map_subtype_le D)
      (Subgroup.Normal.isSubnormal hY) ?_
    have : DX.subgroupOf Y = D := Subgroup.comap_map_eq_self_of_injective Y.subtype_injective D
    rw [this]
    exact hDn
  have h := normalizer_sup_le_normalizer hDXp hDXs inferInstance hRs
  rw [Subgroup.normalizer_eq_top_iff.mpr hnorm, top_le_iff] at h
  exact Subgroup.normalizer_eq_top_iff.mp h

variable {X G : Type*} [Group X] [Group G] {φ : X →* G}

theorem actKer_perfectResidual_le_cen [Finite X] (hX : oStar X = ⊤) {O : Set (Subgroup G)}
    (hO : IsInv φ O) (htr : ∀ J ∈ O, ∀ J' ∈ O, ∃ x : X, act φ x J = J') {J₀ : Subgroup G}
    (hJ₀ : J₀ ∈ O) (w : fixer φ O)
    (hw : w ∈ (CFSG.perfectResidual
        (actHom J₀ (fixer φ O) (fun _ hy => hy J₀ hJ₀)).ker).map
      (actHom J₀ (fixer φ O) (fun _ hy => hy J₀ hJ₀)).ker.subtype) :
    (w : X) ∈ cen φ O := by
  have hYn : (fixer φ O).Normal := fixer_normal hO
  have hY : ∀ y ∈ fixer φ O, act φ y J₀ = J₀ := fun y hy => hy J₀ hJ₀
  have hWn : (actHom J₀ (fixer φ O) hY).ker.Normal := MonoidHom.normal_ker _
  have hDX := normal_perfectResidual_of_normal_normal hX (fixer φ O)
    (actHom J₀ (fixer φ O) hY).ker
  have hwDX : (w : X) ∈ (((CFSG.perfectResidual (actHom J₀ (fixer φ O) hY).ker).map
      (actHom J₀ (fixer φ O) hY).ker.subtype).map (fixer φ O).subtype) := ⟨w, hw, rfl⟩
  intro J hJ j hj
  obtain ⟨x, hx⟩ := htr J₀ hJ₀ J hJ
  have hjJ : j ∈ act φ x J₀ := hx ▸ hj
  rw [mem_act_iff] at hjJ
  have hd := hDX.conj_mem _ hwDX x⁻¹
  obtain ⟨d', hd', hdd'⟩ := hd
  have hdW : d' ∈ (actHom J₀ (fixer φ O) hY).ker := Subgroup.map_subtype_le _ hd'
  have hc := (mem_ker_actHom_iff hY).mp hdW _ hjJ
  have hdd'' : (d' : X) = x⁻¹ * (w : X) * x := by
    simpa using hdd'
  rw [hdd'', map_mul, map_mul, map_inv] at hc
  have h1 : (φ x)⁻¹ * (j * φ (w : X)) * φ x = (φ x)⁻¹ * (φ (w : X) * j) * φ x := by
    calc (φ x)⁻¹ * (j * φ (w : X)) * φ x
        = ((φ x)⁻¹ * j * φ x) * ((φ x)⁻¹ * φ (w : X) * φ x) := by group
      _ = ((φ x)⁻¹ * φ (w : X) * φ x) * ((φ x)⁻¹ * j * φ x) := hc
      _ = (φ x)⁻¹ * (φ (w : X) * j) * φ x := by group
  exact mul_left_cancel (mul_right_cancel h1)

theorem deg_fixer_le [Finite X] [Finite G] (hX : oStar X = ⊤) {O : Set (Subgroup G)}
    (hO : IsInv φ O) (htr : ∀ J ∈ O, ∀ J' ∈ O, ∃ x : X, act φ x J = J') {J₀ : Subgroup G}
    (hJ₀ : J₀ ∈ O) (hB : HypB ↥J₀) :
    deg ↥(fixer φ O) ≤ deg ↥(cen φ O) + deg ↥J₀ ∧
      (Group.IsPerfect ↥(fixer φ O) → deg ↥(fixer φ O) = deg ↥(cen φ O) + deg ↥J₀ →
        ∀ y : fixer φ O, ∃ k ∈ J₀, ∀ j ∈ J₀, φ y * j * (φ y)⁻¹ = k * j * k⁻¹) := by
  have hYn : (fixer φ O).Normal := fixer_normal hO
  have hCn : (cen φ O).Normal := cen_normal hO
  have hY : ∀ y ∈ fixer φ O, act φ y J₀ = J₀ := fun y hy => hy J₀ hJ₀
  have hYo : oStar ↥(fixer φ O) = ⊤ := KAPI.oStar_eq_top_of_normal hX _
  set ρ := actHom J₀ (fixer φ O) hY with hρ
  have hHB := KAPI.deg_quotient_ker_le hB hYo ρ
  have hC'n : ((cen φ O).subgroupOf (fixer φ O)).Normal := Subgroup.normal_subgroupOf
  have hle : (cen φ O).subgroupOf (fixer φ O) ≤ ρ.ker := by
    intro c hc
    exact (mem_ker_actHom_iff hY).mpr fun j hj => hc J₀ hJ₀ j hj
  let π₂ : ↥(fixer φ O) ⧸ (cen φ O).subgroupOf (fixer φ O) →* ↥(fixer φ O) ⧸ ρ.ker :=
    QuotientGroup.map _ ρ.ker (MonoidHom.id _) (by simpa using hle)
  have hπ₂ : Function.Surjective π₂ :=
    QuotientGroup.map_surjective_of_surjective _ _ (MonoidHom.id _)
      (QuotientGroup.mk'_surjective _) _
  have hkereq : π₂.ker = ρ.ker.map (QuotientGroup.mk' ((cen φ O).subgroupOf (fixer φ O))) := by
    show (QuotientGroup.map _ ρ.ker (MonoidHom.id _) _).ker = _
    rw [QuotientGroup.ker_map, Subgroup.comap_id]
  have hsolv : Group.IsSolvable π₂.ker := by
    rw [hkereq]
    refine KAPI.isSolvable_of_perfectResidual_le
      ((QuotientGroup.mk' ((cen φ O).subgroupOf (fixer φ O))).subgroupMap ρ.ker)
      (MonoidHom.subgroupMap_surjective _ _) ?_
    intro w hw
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    show QuotientGroup.mk' ((cen φ O).subgroupOf (fixer φ O)) (w : fixer φ O) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact actKer_perfectResidual_le_cen hX hO htr hJ₀ (w : fixer φ O) ⟨w, hw, rfl⟩
  have hdeg : deg (↥(fixer φ O) ⧸ (cen φ O).subgroupOf (fixer φ O)) =
      deg (↥(fixer φ O) ⧸ ρ.ker) := KAPI.deg_eq_of_surjective hπ₂ hsolv
  have hadd := deg_add hYo ((cen φ O).subgroupOf (fixer φ O))
  have hiso : deg ↥((cen φ O).subgroupOf (fixer φ O)) = deg ↥(cen φ O) :=
    KAPI.deg_congr (Subgroup.subgroupOfEquivOfLe (cen_le_fixer O))
  refine ⟨by omega, fun hperf heq => ?_⟩
  have hrange := hHB.2 ⟨hperf, by omega⟩
  intro y
  exact (actHom_mem_range_conj_iff hY y).mp (hrange ⟨y, rfl⟩)

theorem deg_le_fixer_add [Finite X] [Finite G] (hX : oStar X = ⊤) {O : Set (Subgroup G)}
    (hO : IsInv φ O) (hfin : O.Finite) : deg X ≤ deg ↥(fixer φ O) + O.ncard := by
  have : (fixer φ O).Normal := fixer_normal hO
  have hadd := deg_add hX (fixer φ O)
  have hXq : oStar (X ⧸ fixer φ O) = ⊤ :=
    KAPI.oStar_eq_top_of_surjective hX (QuotientGroup.mk'_surjective _)
  have : Finite O := hfin.to_subtype
  have hperm : permDeg (X ⧸ fixer φ O) ≤ O.ncard := by
    let e : X ⧸ fixer φ O ≃* X ⧸ (permAct φ O hO).ker :=
      QuotientGroup.quotientMulEquivOfEq (ker_permAct hO).symm
    have hinj : Function.Injective
        ((QuotientGroup.kerLift (permAct φ O hO)).comp e.toMonoidHom) := by
      rw [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
      exact (QuotientGroup.kerLift_injective _).comp e.injective
    have := permDeg_le_of_injective _ hinj
    rwa [Nat.card_coe_set_eq] at this
  have := deg_le_permDeg hXq
  omega

@[expose] noncomputable def kappa (S : Set (Subgroup G)) : ℕ := ∑ᶠ J ∈ S, deg ↥J

theorem kappa_empty : kappa (∅ : Set (Subgroup G)) = 0 := by
  simp [kappa]

theorem kappa_union {S₁ S₂ : Set (Subgroup G)} (h₁ : S₁.Finite) (h₂ : S₂.Finite)
    (hd : Disjoint S₁ S₂) : kappa (S₁ ∪ S₂) = kappa S₁ + kappa S₂ := by
  simp only [kappa]
  exact finsum_mem_union hd h₁ h₂

theorem kappa_orbit [Finite G] {O : Set (Subgroup G)} (hfin : O.Finite)
    (htr : ∀ J ∈ O, ∀ J' ∈ O, ∃ x : X, act φ x J = J') {J₀ : Subgroup G} (hJ₀ : J₀ ∈ O) :
    kappa O = O.ncard * deg ↥J₀ := by
  have hconst : ∀ J ∈ O, deg ↥J = deg ↥J₀ := by
    intro J hJ
    obtain ⟨x, rfl⟩ := htr J₀ hJ₀ J hJ
    exact (KAPI.deg_congr (actEquiv (φ := φ) x J₀)).symm
  simp only [kappa]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_congr rfl
    (fun J hJ => hconst J (hfin.mem_toFinset.mp hJ)), Finset.sum_const, smul_eq_mul,
    ← Set.ncard_eq_toFinset_card O hfin]

@[expose] def Inner (φ : X →* G) (S : Set (Subgroup G)) : Prop :=
  ∀ x : X, ∃ k ∈ sSup S, ∀ J ∈ S, ∀ j ∈ J, φ x * j * (φ x)⁻¹ = k * j * k⁻¹

theorem single_orbit [Finite X] [Finite G] (hX : oStar X = ⊤) {O : Set (Subgroup G)}
    (hO : IsInv φ O) (hfin : O.Finite) (hne : O.Nonempty)
    (htr : ∀ J ∈ O, ∀ J' ∈ O, ∃ x : X, act φ x J = J') (hB : ∀ J ∈ O, HypB ↥J) :
    deg X ≤ deg ↥(cen φ O) + kappa O ∧
      (Group.IsPerfect X → deg X = deg ↥(cen φ O) + kappa O → O.ncard = 1 ∧ Inner φ O) := by
  obtain ⟨J₀, hJ₀⟩ := hne
  have hk := kappa_orbit hfin htr hJ₀
  have h1 := deg_fixer_le hX hO htr hJ₀ (hB J₀ hJ₀)
  have h2 := deg_le_fixer_add hX hO hfin
  have hn : 1 ≤ O.ncard := (Set.ncard_pos hfin).mpr ⟨J₀, hJ₀⟩
  obtain ⟨hs, hnc, -⟩ := hB J₀ hJ₀
  have hnc' : ¬ IsMulCommutative ↥J₀ := by
    intro hcomm
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (hcomm.is_comm.comm a b)
  have hd3 : 3 ≤ deg ↥J₀ := by
    rw [deg_eq_permDeg_of_isSimpleGroup ↥J₀ hnc']
    exact KAPI.three_le_permDeg hnc'
  by_cases hn1 : O.ncard = 1
  · obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp hn1
    have hJa : J₀ = a := by simpa [ha] using hJ₀
    subst hJa
    have hYtop : fixer φ O = ⊤ := by
      refine top_unique fun x _ J hJ => ?_
      have := hO x J hJ
      rw [ha] at hJ this
      rw [Set.mem_singleton_iff] at hJ this
      rw [hJ] at this ⊢
      exact this
    have hdegY : deg ↥(fixer φ O) = deg X := by
      rw [hYtop]
      exact KAPI.deg_congr Subgroup.topEquiv
    have hk1 : kappa O = deg ↥J₀ := by rw [hk, hn1, one_mul]
    rw [hk1]
    refine ⟨by omega, fun hperf heq => ⟨hn1, ?_⟩⟩
    have hperfY : Group.IsPerfect ↥(fixer φ O) := by
      rw [hYtop]
      have := hperf
      infer_instance
    obtain ⟨hh1, hh2⟩ := h1
    intro x
    obtain ⟨k, hkJ, hkx⟩ := hh2 hperfY (by omega) ⟨x, hYtop ▸ Subgroup.mem_top x⟩
    refine ⟨k, ?_, fun J hJ j hj => ?_⟩
    · rw [ha, sSup_singleton]
      exact hkJ
    · rw [ha, Set.mem_singleton_iff] at hJ
      subst hJ
      exact hkx j hj
  · have hn2 : 2 ≤ O.ncard := by omega
    rw [hk]
    have hlt : deg ↥J₀ + O.ncard < O.ncard * deg ↥J₀ := by nlinarith
    refine ⟨by omega, fun _ heq => ?_⟩
    exfalso
    omega

end CFSG.SignalizerFunctorTheorem.McBride.Near.BAux
