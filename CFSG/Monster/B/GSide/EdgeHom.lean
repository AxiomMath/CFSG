module

public import CFSG.Monster.B.GSide.FusionRA
public import CFSG.Monster.B.TwoA.Amalgam.DistThreeCentFinal
public import CFSG.Monster.B.TwoA.Amalgam.DistThreeOuterFinal

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam

section Beta

variable {A : Type*} [Group A]

open scoped _root_.Classical in
@[expose] def betaFun (w x : A) : A := x * (if x ∈ commutator A then 1 else w)

theorem betaFun_of_mem {w x : A} (hx : x ∈ commutator A) : betaFun w x = x := by
  unfold betaFun
  rw [ite_eq_left hx, mul_one]

theorem betaFun_of_not_mem {w x : A} (hx : x ∉ commutator A) : betaFun w x = x * w := by
  unfold betaFun
  rw [ite_eq_right hx]

theorem betaFun_one (x : A) : betaFun 1 x = x := by
  by_cases hx : x ∈ commutator A
  · exact betaFun_of_mem hx
  · rw [betaFun_of_not_mem hx, mul_one]

theorem betaFun_mem_iff {w : A} (hwA : w ∈ commutator A) (x : A) :
    betaFun w x ∈ commutator A ↔ x ∈ commutator A := by
  by_cases hx : x ∈ commutator A
  · rw [betaFun_of_mem hx]
  · rw [betaFun_of_not_mem hx, Subgroup.mul_mem_cancel_right _ hwA]

theorem betaFun_betaFun {w w' : A} (hw'A : w' ∈ commutator A) (x : A) :
    betaFun w (betaFun w' x) = betaFun (w' * w) x := by
  by_cases hx : x ∈ commutator A
  · rw [betaFun_of_mem hx, betaFun_of_mem hx, betaFun_of_mem hx]
  · have hx' : betaFun w' x ∉ commutator A := fun h => hx ((betaFun_mem_iff hw'A x).1 h)
    rw [betaFun_of_not_mem hx', betaFun_of_not_mem hx, betaFun_of_not_mem hx, mul_assoc]

theorem betaFun_conj {w : A} (hw : w ∈ Subgroup.center A) (b x : A) :
    betaFun w (b * x * b⁻¹) = b * betaFun w x * b⁻¹ := by
  have hN : (commutator A).Normal := inferInstance
  have hmem : b * x * b⁻¹ ∈ commutator A ↔ x ∈ commutator A := by
    constructor
    · intro h
      have := hN.conj_mem _ h b⁻¹
      rwa [show b⁻¹ * (b * x * b⁻¹) * b⁻¹⁻¹ = x by group] at this
    · intro h
      exact hN.conj_mem _ h b
  by_cases hx : x ∈ commutator A
  · rw [betaFun_of_mem hx, betaFun_of_mem (hmem.2 hx)]
  · rw [betaFun_of_not_mem hx, betaFun_of_not_mem (fun h => hx (hmem.1 h))]
    have hc : b⁻¹ * w = w * b⁻¹ := (Subgroup.mem_center_iff.1 hw b⁻¹)
    calc b * x * b⁻¹ * w = b * x * (b⁻¹ * w) := by group
      _ = b * (x * w) * b⁻¹ := by rw [hc]; group

theorem map_betaFun (σ : A ≃* A) (w x : A) : σ (betaFun w x) = betaFun (σ w) (σ x) := by
  have hmem : σ x ∈ commutator A ↔ x ∈ commutator A := by
    have h := Subgroup.characteristic_iff_comap_eq.1 (inferInstance :
      (commutator A).Characteristic) σ
    have h2 : x ∈ (commutator A).comap σ.toMonoidHom ↔ σ.toMonoidHom x ∈ commutator A :=
      Subgroup.mem_comap
    rw [h] at h2
    exact h2.symm
  by_cases hx : x ∈ commutator A
  · rw [betaFun_of_mem hx, betaFun_of_mem (hmem.2 hx)]
  · rw [betaFun_of_not_mem hx, betaFun_of_not_mem (fun h => hx (hmem.1 h)), map_mul]

theorem betaFun_mul (hidx : (commutator A).index = 2) {w : A} (hw : w ∈ Subgroup.center A)
    (hw2 : w * w = 1) (x y : A) : betaFun w (x * y) = betaFun w x * betaFun w y := by
  have hc : ∀ z : A, z * w = w * z := fun z => (Subgroup.mem_center_iff.1 hw z)
  have hxy := Subgroup.mul_mem_iff_of_index_two hidx (a := x) (b := y)
  by_cases hx : x ∈ commutator A <;> by_cases hy : y ∈ commutator A
  · rw [betaFun_of_mem (hxy.2 (iff_of_true hx hy)), betaFun_of_mem hx, betaFun_of_mem hy]
  · rw [betaFun_of_not_mem (fun h => hy ((hxy.1 h).1 hx)), betaFun_of_mem hx,
      betaFun_of_not_mem hy, mul_assoc]
  · rw [betaFun_of_not_mem (fun h => hx ((hxy.1 h).2 hy)), betaFun_of_not_mem hx,
      betaFun_of_mem hy, mul_assoc, mul_assoc, hc y]
  · rw [betaFun_of_mem (hxy.2 (iff_of_false hx hy)), betaFun_of_not_mem hx,
      betaFun_of_not_mem hy]
    calc x * y = x * y * (w * w) := by rw [hw2, mul_one]
      _ = x * w * (y * w) := by rw [mul_assoc x w, ← mul_assoc w y w, ← hc y]; group

@[expose] def betaEquiv
    (hidx : (commutator A).index = 2) {w : A} (hw : w ∈ Subgroup.center A)
    (hwA : w ∈ commutator A) (hw2 : w * w = 1) : A ≃* A where
  toFun := betaFun w
  invFun := betaFun w
  left_inv x := by rw [betaFun_betaFun hwA, hw2, betaFun_one]
  right_inv x := by rw [betaFun_betaFun hwA, hw2, betaFun_one]
  map_mul' := betaFun_mul hidx hw hw2

theorem betaEquiv_apply
    (hidx : (commutator A).index = 2) {w : A} (hw : w ∈ Subgroup.center A)
    (hwA : w ∈ commutator A) (hw2 : w * w = 1) (x : A) :
    betaEquiv hidx hw hwA hw2 x = betaFun w x :=
  rfl

theorem betaFun_map {B : Type*} [Group B] (f : A →* B) {p : A} {c : B} (hfp : f p = c)
    (hmem : ∀ a, f a ∈ commutator B ↔ a ∈ commutator A) (a : A) :
    betaFun c (f a) = f (betaFun p a) := by
  by_cases ha : a ∈ commutator A
  · rw [betaFun_of_mem ((hmem a).2 ha), betaFun_of_mem ha]
  · rw [betaFun_of_not_mem (fun h => ha ((hmem a).1 h)), betaFun_of_not_mem ha, map_mul, hfp]

end Beta

section Swap

variable {A : Type*} [Group A]

theorem inner_or_twist_of_swap {p q : A} (hp : p ∈ Subgroup.center A)
    (hq : q ∈ Subgroup.center A) (hpA : p ∈ commutator A) (hqA : q ∈ commutator A)
    (hpq : p * q = q * p) (hp2 : p * p = 1) (hq2 : q * q = 1)
    (hZ : ∀ z ∈ Subgroup.center A, z = 1 ∨ z = p ∨ z = q ∨ z = p * q)
    (σ : A ≃* A) (hσp : σ p = q) (hσq : σ q = p) (k₀ : A)
    (hσ2 : ∀ a, σ (σ a) = k₀ * a * k₀⁻¹)
    (hE1 : ∀ τ : A ≃* A, τ p = p → τ q = q → ∃ (b w : A), w ∈ Subgroup.center A ∧
      ∀ x : A, τ x = b * betaFun w x * b⁻¹)
    (hB8 : ¬ ∃ b : A, ∀ x : A, betaFun (p * q) x = b * x * b⁻¹)
    (τG : A ≃* A) (hτp : τG p = q) (hτq : τG q = p) (k : A)
    (hτ2 : ∀ a, τG (τG a) = k * a * k⁻¹) :
    (∃ b : A, ∀ a, τG a = σ (b * a * b⁻¹)) ∨
      ∃ b : A, ∀ a, betaFun p (τG (betaFun p a)) = σ (b * a * b⁻¹) := by
  have hσp' : σ.symm q = p := by rw [← hσp, MulEquiv.symm_apply_apply]
  have hσq' : σ.symm p = q := by rw [← hσq, MulEquiv.symm_apply_apply]
  obtain ⟨b, w, hw, hτ⟩ := hE1 (τG.trans σ.symm)
    (by rw [MulEquiv.trans_apply, hτp, hσp']) (by rw [MulEquiv.trans_apply, hτq, hσq'])
  have hτG : ∀ a, τG a = σ (b * betaFun w a * b⁻¹) := fun a => by
    rw [← hτ a, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  have hwA : w ∈ commutator A := by
    rcases hZ w hw with h | h | h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact hpA
    · rw [h]; exact hqA
    · rw [h]; exact Subgroup.mul_mem _ hpA hqA
  have hw' : σ.symm w ∈ Subgroup.center A := by
    have h := Subgroup.characteristic_iff_comap_eq.1 (inferInstance :
      (Subgroup.center A).Characteristic) σ
    have h2 : σ.symm w ∈ (Subgroup.center A).comap σ.toMonoidHom ↔
        σ.toMonoidHom (σ.symm w) ∈ Subgroup.center A := Subgroup.mem_comap
    rw [h] at h2
    refine h2.2 ?_
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    exact hw
  have hsq : ∀ a, τG (τG a) =
      (σ b * k₀ * b) * betaFun (w * σ.symm w) a * (σ b * k₀ * b)⁻¹ := by
    intro a
    rw [hτG (τG a), hτG a]
    have e1 : betaFun w (σ (b * betaFun w a * b⁻¹)) =
        σ (b * betaFun (w * σ.symm w) a * b⁻¹) := by
      have h := map_betaFun σ (σ.symm w) (b * betaFun w a * b⁻¹)
      rw [MulEquiv.apply_symm_apply] at h
      rw [← h, betaFun_conj hw' b, betaFun_betaFun hwA]
    rw [e1, map_mul, map_mul, map_inv, hσ2]
    group
  have hinner : ∀ a, betaFun (w * σ.symm w) a =
      ((σ b * k₀ * b)⁻¹ * k) * a * ((σ b * k₀ * b)⁻¹ * k)⁻¹ := by
    intro a
    have h1 := (hsq a).symm.trans (hτ2 a)
    set m := σ b * k₀ * b
    calc betaFun (w * σ.symm w) a = m⁻¹ * (m * betaFun (w * σ.symm w) a * m⁻¹) * m := by group
      _ = m⁻¹ * (k * a * k⁻¹) * m := by rw [h1]
      _ = (m⁻¹ * k) * a * (m⁻¹ * k)⁻¹ := by group
  rcases hZ w hw with rfl | rfl | rfl | rfl
  · exact Or.inl ⟨b, fun a => by rw [hτG a, betaFun_one]⟩
  · exfalso
    rw [hσq'] at hinner
    exact hB8 ⟨_, hinner⟩
  · exfalso
    rw [hσp', ← hpq] at hinner
    exact hB8 ⟨_, hinner⟩
  · refine Or.inr ⟨b, fun a => ?_⟩
    have hqp : σ.symm p = q := hσq'
    rw [hτG, betaFun_betaFun hpA]
    have e2 : p * (p * q) = q := by rw [← mul_assoc, hp2, one_mul]
    rw [e2]
    have h := map_betaFun σ q (b * betaFun q a * b⁻¹)
    rw [hσq] at h
    rw [← h, betaFun_conj hq b, betaFun_betaFun hqA, hq2, betaFun_one]

end Swap

@[expose] def cEdgeFixToH :
    cEdgeFix →* vStab cv0 := Subgroup.inclusion inf_le_left

theorem coe_cEdgeFixToH
    (a : cEdgeFix) : ((cEdgeFixToH a : vStab cv0) : Shat) = a := rfl

theorem cEdgeFixToH_injective :
    Function.Injective cEdgeFixToH := Subgroup.inclusion_injective _

theorem cEdgeFixToH_lamV0 :
    cEdgeFixToH lamV0 = cV0 := rfl

theorem cEdgeFixToH_lamW0 :
    cEdgeFixToH lamW0 = lamW0H := rfl

theorem index_commutator_H :
    (commutator (vStab cv0)).index = 2 :=
  index_commutator_vStab (cvMul_one cv0)

theorem cV0_mem_commutator_H :
    cV0 ∈ commutator (vStab cv0) ∧ lamW0H ∈ commutator (vStab cv0) := by
  obtain ⟨ρ, iv, hρ⟩ := exists_isCompatLocal cv0
  rw [← comap_Ginl_eq_commutator hρ.1]
  refine ⟨?_, ?_⟩
  · show ρ cV0 ∈ E6.Ginl
    rw [(hρ.2.1 cV0).2 (by rw [coe_cV0, coe_clabelS]; exact Subgroup.mem_zpowers _)]
    exact Subgroup.one_mem _
  · show ρ lamW0H ∈ E6.Ginl
    rw [hρ.2.2.2.2 ⟨cw0, cgraph_adj_cv0_cw0⟩ lamW0H rfl]
    exact ⟨_, rfl⟩

@[expose] def betaH :
    vStab cv0 ≃* vStab cv0 :=
  betaEquiv index_commutator_H cV0_mem_center_vStab cV0_mem_commutator_H.1 cV0_mul_self

theorem betaH_apply
    (h : vStab cv0) : betaH h = betaFun cV0 h := rfl

theorem betaH_symm_apply
    (h : vStab cv0) : betaH.symm h = betaFun cV0 h := rfl

theorem betaH_cV0 :
    betaH cV0 = cV0 := betaFun_of_mem cV0_mem_commutator_H.1

theorem betaH_symm_lamW0H :
    betaH.symm lamW0H = lamW0H := betaFun_of_mem cV0_mem_commutator_H.2

theorem commute_clabelS_iff_mem
    (v : CVert) (s : Shat) : Commute s (clabelS v) ↔ s ∈ vStab v := by
  rw [mem_vStab, ← commute_clabel_iff]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem exists_not_mem_commutator_H :
    ∃ a : cEdgeFix, cEdgeFixToH a ∉ commutator (vStab cv0) := by
  have hne := sphereDistThree_nonempty_of_ambient ambientRootOrbitsHyp cv0
  obtain ⟨u₀, hu₀⟩ := hne
  have hu₀' : cgraph.dist u₀ cv0 = 3 := by
    rw [SimpleGraph.dist_comm]
    exact mem_sphereDistThree.1 hu₀
  have hT := native_distance_three_pair_two_local_root_orbits_final hu₀'
  have hz0 := hT.2.2.1
  obtain ⟨z, hz⟩ := hz0
  have hset := hT.2.2.2.2.2.2.2.2.2.2.1
  have hz' : z ∈ {z | z ∈ cgraph.neighborSet cv0 ∧ cvMul z (clabelS u₀) = z} := by
    rw [hset]
    exact hz
  have htr := cvMul_edge_transitive hz'.1 cgraph_adj_cv0_cw0
  obtain ⟨h, hh0, hhz⟩ := htr
  have hu3 : cvMul u₀ h ∈ sphereDistThree cv0 := by
    have := sphereDistThree_cvMul hu₀ h
    rwa [hh0] at this
  have hcz : Commute (clabelS u₀) (clabelS z) :=
    (commute_clabelS_iff_mem z (clabelS u₀)).2 (mem_vStab.2 hz'.2)
  have hcw : Commute (clabelS (cvMul u₀ h)) (clabelS cw0) := by
    rw [← hhz, clabelS_cvMul, clabelS_cvMul]
    have h1 := hcz.map (MulAut.conj h⁻¹).toMonoidHom
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h1
    exact h1
  have huS := native_distance_three_label_is_outer_local_involution_final hu3
  exact ⟨⟨clabelS (cvMul u₀ h), huS.1, (commute_clabelS_iff_mem cw0 _).1 hcw⟩, huS.2.1 _ rfl⟩

theorem mem_commutator_H_iff
    (hAidx : (commutator cEdgeFix).index = 2) (a : cEdgeFix) :
    cEdgeFixToH a ∈ commutator (vStab cv0) ↔ a ∈ commutator cEdgeFix := by
  have hle : commutator cEdgeFix ≤ (commutator (vStab cv0)).comap cEdgeFixToH := by
    rw [← Subgroup.map_le_iff_le_comap, commutator, commutator, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  have hKidx : ((commutator (vStab cv0)).comap cEdgeFixToH).index = 2 := by
    have hdvd : ((commutator (vStab cv0)).comap cEdgeFixToH).index ∣ 2 := by
      rw [Subgroup.index_comap, ← index_commutator_H]
      exact Subgroup.relIndex_dvd_index_of_normal _ _
    have hne : ((commutator (vStab cv0)).comap cEdgeFixToH).index ≠ 1 := by
      intro h1
      rw [Subgroup.index_eq_one] at h1
      obtain ⟨a, ha⟩ := exists_not_mem_commutator_H
      exact ha (show a ∈ (commutator (vStab cv0)).comap cEdgeFixToH by rw [h1]; trivial)
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd h hne
    · exact h
  have : ((commutator (vStab cv0)).comap cEdgeFixToH).FiniteIndex := ⟨by rw [hKidx]; norm_num⟩
  have heq := Subgroup.eq_of_index_dvd_index hle (by rw [hAidx, hKidx])
  rw [heq]
  rfl

theorem betaH_cEdgeFixToH
    (hAidx : (commutator cEdgeFix).index = 2) (a : cEdgeFix) :
    betaH (cEdgeFixToH a) = cEdgeFixToH (betaFun lamV0 a) :=
  betaFun_map cEdgeFixToH cEdgeFixToH_lamV0 (mem_commutator_H_iff hAidx) a

section Edge

variable {G : Type*} [Group G] {d : G}

@[expose] def conjSubgroupEquiv (K : Subgroup G) (t : G) (h1 : ∀ x ∈ K, t * x * t⁻¹ ∈ K)
    (h2 : ∀ x ∈ K, t⁻¹ * x * t ∈ K) : K ≃* K where
  toFun x := ⟨t * x * t⁻¹, h1 x x.2⟩
  invFun x := ⟨t⁻¹ * x * t, h2 x x.2⟩
  left_inv x := Subtype.ext (show t⁻¹ * (t * (x : G) * t⁻¹) * t = x by group)
  right_inv x := Subtype.ext (show t * (t⁻¹ * (x : G) * t) * t⁻¹ = x by group)
  map_mul' x y := Subtype.ext (show t * ((x : G) * y) * t⁻¹ = t * x * t⁻¹ * (t * y * t⁻¹) by
    group)

@[expose] def edgeTheta
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0) : cEdgeFix →* G :=
  (Subgroup.centralizer {d}).subtype.comp (ψ.symm.toMonoidHom.comp cEdgeFixToH)

theorem edgeTheta_apply
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0) (a : cEdgeFix) :
    edgeTheta ψ a = ((ψ.symm (cEdgeFixToH a) : Subgroup.centralizer {d}) : G) := rfl

theorem edgeTheta_injective
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0) :
    Function.Injective (edgeTheta ψ) := fun _ _ h =>
  cEdgeFixToH_injective (ψ.symm.injective (Subtype.ext h))

theorem edgeTheta_lamV0
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0) : edgeTheta ψ lamV0 = d := by
  rw [edgeTheta_apply, cEdgeFixToH_lamV0, ← hψ, MulEquiv.symm_apply_apply]

theorem edgeTheta_lamW0
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0) :
    edgeTheta ψ lamW0 = ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) := rfl

theorem mem_range_edgeTheta
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0) {x : G} :
    x ∈ (edgeTheta ψ).range ↔ x ∈ Subgroup.centralizer {d} ∧
      x * ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) =
        ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) * x := by
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨(ψ.symm (cEdgeFixToH a)).2, ?_⟩
    have h1 : cEdgeFixToH a * lamW0H = lamW0H * cEdgeFixToH a :=
      Subtype.ext ((commute_clabelS_iff_mem cw0 a).2 a.2.2)
    have h2 := congrArg (fun y => ((ψ.symm y : Subgroup.centralizer {d}) : G)) h1
    simp only [map_mul, Subgroup.coe_mul] at h2
    exact h2
  · rintro ⟨hx, hxe⟩
    have hy : ψ ⟨x, hx⟩ * lamW0H = lamW0H * ψ ⟨x, hx⟩ := by
      have h1 : (⟨x, hx⟩ : Subgroup.centralizer {d}) * ψ.symm lamW0H =
          ψ.symm lamW0H * ⟨x, hx⟩ := Subtype.ext hxe
      have h2 := congrArg ψ h1
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
    have hmem : ((ψ ⟨x, hx⟩ : vStab cv0) : Shat) ∈ vStab cw0 :=
      (commute_clabelS_iff_mem cw0 _).1 (congrArg Subtype.val hy)
    refine ⟨⟨_, (ψ ⟨x, hx⟩).2, hmem⟩, ?_⟩
    rw [edgeTheta_apply]
    have e : cEdgeFixToH ⟨_, (ψ ⟨x, hx⟩).2, hmem⟩ = ψ ⟨x, hx⟩ := rfl
    rw [e, MulEquiv.symm_apply_apply]

theorem conj_mem_inter_of_swap {d e t x : G} (ht1 : t * d * t⁻¹ = e) (ht2 : t * e * t⁻¹ = d)
    (hxd : x * d = d * x) (hxe : x * e = e * x) :
    t * x * t⁻¹ * d = d * (t * x * t⁻¹) ∧ t * x * t⁻¹ * e = e * (t * x * t⁻¹) := by
  constructor
  · calc t * x * t⁻¹ * d = t * x * t⁻¹ * (t * e * t⁻¹) := by rw [ht2]
      _ = t * (x * e) * t⁻¹ := by group
      _ = t * (e * x) * t⁻¹ := by rw [hxe]
      _ = t * e * t⁻¹ * (t * x * t⁻¹) := by group
      _ = d * (t * x * t⁻¹) := by rw [ht2]
  · calc t * x * t⁻¹ * e = t * x * t⁻¹ * (t * d * t⁻¹) := by rw [ht1]
      _ = t * (x * d) * t⁻¹ := by group
      _ = t * (d * x) * t⁻¹ := by rw [hxd]
      _ = t * d * t⁻¹ * (t * x * t⁻¹) := by group
      _ = e * (t * x * t⁻¹) := by rw [ht1]

theorem swap_inv {d e t : G} (ht1 : t * d * t⁻¹ = e) (ht2 : t * e * t⁻¹ = d) :
    t⁻¹ * d * t⁻¹⁻¹ = e ∧ t⁻¹ * e * t⁻¹⁻¹ = d := by
  constructor
  · rw [← ht2]; group
  · rw [← ht1]; group

theorem exists_conj_equiv_of_range {A : Type*} [Group A] (θ : A →* G)
    (hθ : Function.Injective θ) (t : G) (h1 : ∀ x ∈ θ.range, t * x * t⁻¹ ∈ θ.range)
    (h2 : ∀ x ∈ θ.range, t⁻¹ * x * t ∈ θ.range) :
    ∃ τ : A ≃* A, (∀ a, θ (τ a) = t * θ a * t⁻¹) ∧
      ∀ k : A, θ k = t * t → ∀ a, τ (τ a) = k * a * k⁻¹ := by
  refine ⟨(MonoidHom.ofInjective hθ).trans ((conjSubgroupEquiv θ.range t h1 h2).trans
    (MonoidHom.ofInjective hθ).symm), fun a => ?_, fun k hk a => ?_⟩
  · have h := congrArg Subtype.val ((MonoidHom.ofInjective hθ).apply_symm_apply
      (conjSubgroupEquiv θ.range t h1 h2 (MonoidHom.ofInjective hθ a)))
    exact h
  · have hτ : ∀ a, θ (((MonoidHom.ofInjective hθ).trans ((conjSubgroupEquiv θ.range t h1 h2).trans
        (MonoidHom.ofInjective hθ).symm)) a) = t * θ a * t⁻¹ := fun a =>
      congrArg Subtype.val ((MonoidHom.ofInjective hθ).apply_symm_apply
        (conjSubgroupEquiv θ.range t h1 h2 (MonoidHom.ofInjective hθ a)))
    apply hθ
    rw [hτ, hτ, map_mul, map_mul, map_inv, hk]
    group

theorem exists_tauG
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0) {t : G}
    (ht1 : t * d * t⁻¹ = ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G))
    (ht2 : t * ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) * t⁻¹ = d) :
    ∃ τG : cEdgeFix ≃* cEdgeFix, (∀ a, edgeTheta ψ (τG a) = t * edgeTheta ψ a * t⁻¹) ∧
      τG lamV0 = lamW0 ∧ τG lamW0 = lamV0 ∧ ∃ k : cEdgeFix, edgeTheta ψ k = t * t ∧
        ∀ a, τG (τG a) = k * a * k⁻¹ := by
  have hR : ∀ {u : G}, u * d * u⁻¹ = ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) →
      u * ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) * u⁻¹ = d →
      ∀ x ∈ (edgeTheta ψ).range, u * x * u⁻¹ ∈ (edgeTheta ψ).range := by
    intro u hu1 hu2 x hx
    rw [mem_range_edgeTheta] at hx ⊢
    have h := conj_mem_inter_of_swap hu1 hu2
      (Subgroup.mem_centralizer_singleton_iff.1 hx.1) hx.2
    exact ⟨Subgroup.mem_centralizer_singleton_iff.2 h.1, h.2⟩
  have hinv := swap_inv ht1 ht2
  have hR' : ∀ x ∈ (edgeTheta ψ).range, t⁻¹ * x * t ∈ (edgeTheta ψ).range := fun x hx => by
    have h := hR hinv.1 hinv.2 x hx
    rwa [inv_inv] at h
  have hτex := exists_conj_equiv_of_range (edgeTheta ψ) (edgeTheta_injective ψ) t
    (hR ht1 ht2) hR'
  obtain ⟨τG, hτ, hτ2⟩ := hτex
  have htt : t * t ∈ (edgeTheta ψ).range := by
    have h0 : (1 : G) ∈ (edgeTheta ψ).range := Subgroup.one_mem _
    have h1 := hR ht1 ht2 _ h0
    rw [mem_range_edgeTheta]
    constructor
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc t * t * d = t * (t * d * t⁻¹) * t := by group
        _ = t * ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) * t⁻¹ * (t * t) := by
          rw [ht1]; group
        _ = d * (t * t) := by rw [ht2]
    · calc t * t * ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) =
          t * (t * ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) * t⁻¹) * t := by group
        _ = t * d * t⁻¹ * (t * t) := by rw [ht2]; group
        _ = ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) * (t * t) := by rw [ht1]
  obtain ⟨k, hk⟩ := htt
  refine ⟨τG, hτ, ?_, ?_, k, hk, hτ2 k hk⟩
  · apply edgeTheta_injective ψ
    rw [hτ, edgeTheta_lamV0 ψ hψ, ht1, edgeTheta_lamW0]
  · apply edgeTheta_injective ψ
    rw [hτ, edgeTheta_lamW0, ht2, edgeTheta_lamV0 ψ hψ]

theorem ext_injective_and_swap {A E : Type*} [Group A] [Group E] (i : A →* E)
    (hidx : i.range.index = 2) {s : E} (hs : s ∉ i.range) (θ : A →* G)
    (hθ : Function.Injective θ) {d e t : G} (hde : d ≠ e) (ht1 : t * d * t⁻¹ = e)
    (ht2 : t * e * t⁻¹ = d) (hθde : ∀ a, θ a * d = d * θ a ∧ θ a * e = e * θ a)
    (f : E →* G) (hf : ∀ a, f (i a) = θ a) (c₀ : A) (hfs : f s = t * θ c₀) :
    Function.Injective f ∧
      ∀ g : E, g ∉ i.range → f g * d * (f g)⁻¹ = e ∧ f g * e * (f g)⁻¹ = d := by
  have hsw : ∀ g : E, g ∉ i.range → f g * d * (f g)⁻¹ = e ∧ f g * e * (f g)⁻¹ = d := by
    intro g hg
    have hmem : s⁻¹ * g ∈ i.range :=
      (Subgroup.mul_mem_iff_of_index_two hidx).2 (iff_of_false (fun h => hs (by
        simpa using i.range.inv_mem h)) hg)
    obtain ⟨a, ha⟩ := hmem
    have hg' : f g = t * θ (c₀ * a) := by
      have e1 : g = s * i a := by rw [ha]; group
      rw [e1, map_mul, hf, hfs, map_mul, mul_assoc]
    obtain ⟨h1, h2⟩ := hθde (c₀ * a)
    rw [hg']
    constructor
    · calc t * θ (c₀ * a) * d * (t * θ (c₀ * a))⁻¹ = t * (θ (c₀ * a) * d) * (θ (c₀ * a))⁻¹ * t⁻¹ :=
            by group
        _ = e := by rw [h1, ← ht1]; group
    · calc t * θ (c₀ * a) * e * (t * θ (c₀ * a))⁻¹ = t * (θ (c₀ * a) * e) * (θ (c₀ * a))⁻¹ * t⁻¹ :=
            by group
        _ = d := by rw [h2, ← ht2]; group
  refine ⟨(injective_iff_map_eq_one f).2 fun g hg => ?_, hsw⟩
  by_cases hgr : g ∈ i.range
  · obtain ⟨a, rfl⟩ := hgr
    rw [hf] at hg
    rw [(injective_iff_map_eq_one θ).1 hθ a hg, map_one]
  · exfalso
    have h := (hsw g hgr).1
    rw [hg, one_mul, inv_one, mul_one] at h
    exact hde h

theorem twist_conj {A : Type*} [Group A] (θ θ' : A →* G) (β : A → A) (hβ : ∀ a, β (β a) = a)
    (hθ' : ∀ a, θ' a = θ (β a)) (τ : A → A) {t : G} (hτ : ∀ a, θ (τ a) = t * θ a * t⁻¹)
    (σ : A → A) (b : A) (hb : ∀ a, β (τ (β a)) = σ (b * a * b⁻¹)) (a : A) :
    t * θ' a * t⁻¹ = θ' (σ (b * a * b⁻¹)) := by
  rw [hθ', hθ', ← hτ, ← hb a, hβ]

theorem exists_edge_ext
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0) {t : G}
    (ht1 : t * d * t⁻¹ = ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G))
    (ht2 : t * ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) * t⁻¹ = d)
    {s : Shat} (hs0 : cvMul cv0 s = cw0) (hs1 : cvMul cw0 s = cv0) (b : cEdgeFix)
    (hb : ∀ a, t * edgeTheta ψ a * t⁻¹ = edgeTheta ψ (cEdgeSigma hs0 hs1 (b * a * b⁻¹))) :
    ∃ φe : cEdgeStab →* G, Function.Injective φe ∧ (∀ a, φe (cEdgeIncl a) = edgeTheta ψ a) ∧
      ∀ g : cEdgeStab, (g : Shat) ∉ cEdgeFix →
        φe g * d * (φe g)⁻¹ = ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) ∧
        φe g * ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) * (φe g)⁻¹ = d := by
  have htt : t * t ∈ (edgeTheta ψ).range := by
    rw [mem_range_edgeTheta]
    constructor
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc t * t * d = t * (t * d * t⁻¹) * t := by group
        _ = t * ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) * t⁻¹ * (t * t) := by
          rw [ht1]; group
        _ = d * (t * t) := by rw [ht2]
    · calc t * t * ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) =
          t * (t * ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) * t⁻¹) * t := by group
        _ = t * d * t⁻¹ * (t * t) := by rw [ht2]; group
        _ = ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) * (t * t) := by rw [ht1]
  have hext := exists_hom_cEdgeStab hs0 hs1 (edgeTheta ψ) (edgeTheta_injective ψ) t b hb htt
  obtain ⟨f, hf, d', -, hfs⟩ := hext
  have hde : d ≠ ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) := by
    intro h
    apply ne_cV0_of_mem_RA lamW0H_mem_RA
    apply ψ.symm.injective
    rw [← hψ, MulEquiv.symm_apply_apply]
    exact Subtype.ext h.symm
  have hθde : ∀ a, edgeTheta ψ a * d = d * edgeTheta ψ a ∧
      edgeTheta ψ a * ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) =
        ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) * edgeTheta ψ a := fun a => by
    have h := (mem_range_edgeTheta ψ).1 ⟨a, rfl⟩
    exact ⟨Subgroup.mem_centralizer_singleton_iff.1 h.1, h.2⟩
  have hres := ext_injective_and_swap cEdgeIncl index_range_cEdgeIncl
    (swapE_not_mem_range hs0 hs1) (edgeTheta ψ) (edgeTheta_injective ψ) hde ht1 ht2 hθde f hf
    (b⁻¹ * d') hfs
  refine ⟨f, hres.1, hf, fun g hg => hres.2 g ?_⟩
  rw [cEdgeIncl_range, Subgroup.mem_subgroupOf]
  exact hg

theorem edgeTheta_trans_betaH
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hAidx : (commutator cEdgeFix).index = 2) (a : cEdgeFix) :
    edgeTheta (ψ.trans betaH) a = edgeTheta ψ (betaFun lamV0 a) :=
  congrArg (fun y => ((ψ.symm y : Subgroup.centralizer {d}) : G)) (betaH_cEdgeFixToH hAidx a)

theorem exists_edge_ext_twist
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0) {t : G}
    (ht1 : t * d * t⁻¹ = ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G))
    (ht2 : t * ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) * t⁻¹ = d)
    {s : Shat} (hs0 : cvMul cv0 s = cw0) (hs1 : cvMul cw0 s = cv0)
    (hAidx : (commutator cEdgeFix).index = 2) (hcA : lamV0 ∈ commutator cEdgeFix)
    (τG : cEdgeFix ≃* cEdgeFix) (hτ : ∀ a, edgeTheta ψ (τG a) = t * edgeTheta ψ a * t⁻¹)
    (b : cEdgeFix)
    (hb : ∀ a, betaFun lamV0 (τG (betaFun lamV0 a)) = cEdgeSigma hs0 hs1 (b * a * b⁻¹)) :
    ∃ φe : cEdgeStab →* G, Function.Injective φe ∧
      (∀ a, φe (cEdgeIncl a) = edgeTheta (ψ.trans betaH) a) ∧
      ∀ g : cEdgeStab, (g : Shat) ∉ cEdgeFix →
        φe g * d * (φe g)⁻¹ = ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) ∧
        φe g * ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) * (φe g)⁻¹ = d := by
  have hψ'd : (ψ.trans betaH) ⟨d, mem_centralizer_singleton_self d⟩ = cV0 := by
    rw [MulEquiv.trans_apply, hψ, betaH_cV0]
  have hψ'e : (ψ.trans betaH).symm lamW0H = ψ.symm lamW0H := by
    rw [MulEquiv.symm_trans_apply, betaH_symm_lamW0H]
  have hβ2 : ∀ a, betaFun lamV0 (betaFun lamV0 a) = a := fun a => by
    rw [betaFun_betaFun hcA, lamV0_mul_self, betaFun_one]
  have hb' := twist_conj (edgeTheta ψ) (edgeTheta (ψ.trans betaH)) (betaFun lamV0) hβ2
    (edgeTheta_trans_betaH ψ hAidx) τG hτ (cEdgeSigma hs0 hs1) b hb
  have ht1' : t * d * t⁻¹ = (((ψ.trans betaH).symm lamW0H : Subgroup.centralizer {d}) : G) := by
    rw [hψ'e]
    exact ht1
  have ht2' : t * (((ψ.trans betaH).symm lamW0H : Subgroup.centralizer {d}) : G) * t⁻¹ = d := by
    rw [hψ'e]
    exact ht2
  have hres := exists_edge_ext (ψ.trans betaH) hψ'd ht1' ht2' hs0 hs1 b hb'
  obtain ⟨φe, hinj, hext, hswap⟩ := hres
  refine ⟨φe, hinj, hext, fun g hg => ?_⟩
  have h := hswap g hg
  rw [hψ'e] at h
  exact h

open scoped _root_.Classical in
theorem exists_edge_hom
    [Finite G] (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0) (hd : orderOf d = 2)
    (hidx : 2 ∣ (Subgroup.centralizer {d}).index)
    (hE1 : ∀ τ : cEdgeFix ≃* cEdgeFix, τ lamV0 = lamV0 → τ lamW0 = lamW0 →
      ∃ (b : cEdgeFix) (w : cEdgeFix), w ∈ Subgroup.center cEdgeFix ∧
        ∀ x : cEdgeFix, τ x = b * (x * (if x ∈ commutator cEdgeFix then 1 else w)) * b⁻¹)
    (hAidx : (commutator cEdgeFix).index = 2)
    (hZA : Subgroup.center cEdgeFix ≤ commutator cEdgeFix)
    (hB8 : ¬ ∃ b : cEdgeFix, ∀ x : cEdgeFix,
      x * (if x ∈ commutator cEdgeFix then 1 else lamV0 * lamW0) = b * x * b⁻¹) :
    ∃ ψ' : Subgroup.centralizer {d} ≃* vStab cv0,
      (ψ' = ψ ∨ ψ' = ψ.trans betaH) ∧
      ψ' ⟨d, mem_centralizer_singleton_self d⟩ = cV0 ∧ ψ'.symm lamW0H = ψ.symm lamW0H ∧
      ∃ φe : cEdgeStab →* G, Function.Injective φe ∧
        (∀ a : cEdgeFix,
          φe (cEdgeIncl a) = ((ψ'.symm (cEdgeFixToH a) : Subgroup.centralizer {d}) : G)) ∧
        ∀ g : cEdgeStab, (g : Shat) ∉ cEdgeFix →
          φe g * d * (φe g)⁻¹ = ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) ∧
          φe g * ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) * (φe g)⁻¹ = d := by
  have hsw := exists_swap_edge ψ hψ hd hidx
  obtain ⟨t, ht1, ht2⟩ := hsw
  have hsS := exists_edge_swap
  obtain ⟨s, hs0, hs1⟩ := hsS
  have hτex := exists_tauG ψ hψ ht1 ht2
  obtain ⟨τG, hτ, hτp, hτq, k, -, hτ2⟩ := hτex
  have hσ2 : ∀ a, cEdgeSigma hs0 hs1 (cEdgeSigma hs0 hs1 a) =
      ⟨s * s, swap_mul_self_mem hs0 hs1⟩ * a * (⟨s * s, swap_mul_self_mem hs0 hs1⟩ : cEdgeFix)⁻¹ :=
    fun a => Subtype.ext (show s * (s * (a : Shat) * s⁻¹) * s⁻¹ = s * s * a * (s * s)⁻¹ by group)
  have hgen := inner_or_twist_of_swap lamV0_mem_center lamW0_mem_center (hZA lamV0_mem_center)
    (hZA lamW0_mem_center) lamV0_mul_comm lamV0_mul_self lamW0_mul_self
    (fun z hz => mem_center_cEdgeFix_iff.1 hz) (cEdgeSigma hs0 hs1) (cEdgeSigma_lamV0 hs0 hs1)
    (cEdgeSigma_lamW0 hs0 hs1) _ hσ2 hE1 hB8 τG hτp hτq k hτ2
  rcases hgen with ⟨b, hb⟩ | ⟨b, hb⟩
  · have hb' : ∀ a, t * edgeTheta ψ a * t⁻¹ = edgeTheta ψ (cEdgeSigma hs0 hs1 (b * a * b⁻¹)) :=
      fun a => by rw [← hτ, hb]
    have hres := exists_edge_ext ψ hψ ht1 ht2 hs0 hs1 b hb'
    obtain ⟨φe, hinj, hext, hswap⟩ := hres
    exact ⟨ψ, Or.inl rfl, hψ, rfl, φe, hinj, hext, hswap⟩
  · have hres := exists_edge_ext_twist ψ hψ ht1 ht2 hs0 hs1 hAidx (hZA lamV0_mem_center) τG hτ b hb
    obtain ⟨φe, hinj, hext, hswap⟩ := hres
    refine ⟨ψ.trans betaH, Or.inr rfl, ?_, ?_, φe, hinj, hext, hswap⟩
    · rw [MulEquiv.trans_apply, hψ, betaH_cV0]
    · rw [MulEquiv.symm_trans_apply, betaH_symm_lamW0H]

end Edge

end CFSG.Monster.B.GSide
