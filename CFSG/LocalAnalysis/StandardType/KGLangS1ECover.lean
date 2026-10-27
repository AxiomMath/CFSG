module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangKGInputs
public import CFSG.LocalAnalysis.StandardType.GGFixSub

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem kgLangS1ECoverAux_fixedPointSubgroup_zpowers {K : Type} [Group K]
    (ξ : MulAut K) :
    fixedPointSubgroup ↥(Subgroup.zpowers ξ) K = ggFixSub ξ := by
  ext k
  rw [fixedPointSubgroup, FixedPoints.mem_subgroup, mem_ggFixSub]
  constructor
  · intro h
    exact h ⟨ξ, Subgroup.mem_zpowers ξ⟩
  · intro h a
    let S : Subgroup (MulAut K) :=
      { carrier := {φ | φ k = k}
        one_mem' := by simp
        mul_mem' := by
          intro φ ψ hφ hψ
          show φ (ψ k) = k
          rw [hψ, hφ]
        inv_mem' := by
          intro φ hφ
          apply φ.injective
          rw [hφ]
          simp }
    have hgen : ξ ∈ S := h
    have hle : Subgroup.zpowers ξ ≤ S := Subgroup.zpowers_le.mpr hgen
    exact hle a.2

private theorem kgLangS1ECoverAux_induced_mk {K R : Type} [Group K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (ξ : MulAut K) (q : K ⧸ Subgroup.center K) :
    kgInducedAut θ ξ (θ q) = θ (centerQuotAut K ξ q) := by
  simp [kgInducedAut, MulAut.congr_apply]

private theorem kgLangS1ECoverAux_surj {p : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {K : Type} [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center K)) {ξ : MulAut K} (hξp : ξ ^ p = 1) :
    ∀ r ∈ ggFixSub (kgInducedAut θ ξ), ∃ k ∈ ggFixSub ξ, θ (QuotientGroup.mk k) = r := by
  intro r hr
  let A := ↥(Subgroup.zpowers ξ)
  haveI : Finite (MulAut K) :=
    Finite.of_injective (fun e : MulAut K => (e : K → K)) DFunLike.coe_injective
  haveI : Finite A := inferInstance
  have hInv : CFSG.IsInvariant A K (Subgroup.center K) :=
    isInvariant_of_characteristic (A := A) (G := K) (Subgroup.center K)
  have hcop : Nat.Coprime (Nat.card A) (Nat.card ↥(Subgroup.center K)) := by
    have hdvd : Nat.card A ∣ p := by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_iff_pow_eq_one.mpr hξp
    exact Nat.Coprime.coprime_dvd_left hdvd (hp.coprime_iff_not_dvd.mpr hZ)
  letI : MulDistribMulAction A (K ⧸ Subgroup.center K) :=
    quotientMulDistribMulAction (A := A) (G := K) (Subgroup.center K) hInv
  have hfix := fixedPointSubgroup_quotient_eq_map_of_isMulCommutative (A := A) (G := K)
    (Subgroup.center K) hInv hcop
  let q : K ⧸ Subgroup.center K := θ.symm r
  have hcenter : centerQuotAut K ξ q = q := by
    apply θ.injective
    rw [← kgLangS1ECoverAux_induced_mk θ ξ q]
    show kgInducedAut θ ξ (θ q) = θ q
    rw [show θ q = r from θ.apply_symm_apply r]
    exact hr
  have hsmul_center : ∀ (a : A) (x : K ⧸ Subgroup.center K),
      a • x = centerQuotAut K (a : MulAut K) x := by
    intro a x
    induction x using QuotientGroup.induction_on with
    | H k =>
      rw [MulAction.Quotient.smul_coe, centerQuotAut_mk]
      rfl
  have hgen : (⟨ξ, Subgroup.mem_zpowers ξ⟩ : A) • q = q := by
    rw [hsmul_center]
    exact hcenter
  have hq : q ∈ fixedPointSubgroup A (K ⧸ Subgroup.center K) := by
    rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
    intro a
    have hgenmem : (⟨ξ, Subgroup.mem_zpowers ξ⟩ : A) ∈ MulAction.stabilizer A q :=
      MulAction.mem_stabilizer_iff.mpr hgen
    have hle : Subgroup.zpowers (⟨ξ, Subgroup.mem_zpowers ξ⟩ : A) ≤ MulAction.stabilizer A q :=
      Subgroup.zpowers_le.mpr hgenmem
    have hamem : a ∈ Subgroup.zpowers (⟨ξ, Subgroup.mem_zpowers ξ⟩ : A) := by
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp a.2
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hn)⟩
    exact MulAction.mem_stabilizer_iff.mp (hle hamem)
  rw [hfix] at hq
  obtain ⟨k, hk, hkq⟩ := Subgroup.mem_map.mp hq
  refine ⟨k, ?_, ?_⟩
  · rw [← kgLangS1ECoverAux_fixedPointSubgroup_zpowers ξ]
    exact hk
  · change θ (QuotientGroup.mk k) = r
    change QuotientGroup.mk k = q at hkq
    rw [hkq]
    exact θ.apply_symm_apply r


theorem kgLangS1E_component_cover {p : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {K : Type} [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center K))
    {ξ : MulAut K} (hξp : ξ ^ p = 1)
    (hCs : IsSimpleGroup ↥(ggFixSub (kgInducedAut θ ξ)))
    (hCna : ∃ a b : ↥(ggFixSub (kgInducedAut θ ξ)), a * b ≠ b * a)
    {J₀ : Subgroup K} (hJ₀ : IsComponentOf J₀ (ggFixSub ξ)) :
    (∀ j ∈ J₀, θ (QuotientGroup.mk j) ∈ ggFixSub (kgInducedAut θ ξ)) ∧
    (∀ r ∈ ggFixSub (kgInducedAut θ ξ), ∃ j ∈ J₀, θ (QuotientGroup.mk j) = r) ∧
    (∀ j ∈ J₀, θ (QuotientGroup.mk j) = 1 ↔ ∀ j' ∈ J₀, j * j' = j' * j) ∧
    ∀ α : MulAut K, α * ξ = ξ * α → ∀ j ∈ J₀, α j ∈ J₀ := by
  classical
  let C : Subgroup R := ggFixSub (kgInducedAut θ ξ)
  haveI : IsSimpleGroup ↥C := hCs
  have hmap_mem : ∀ j ∈ ggFixSub ξ, θ (QuotientGroup.mk j) ∈ C := by
    intro j hj
    have hj' : ξ j = j := by simpa using hj
    rw [mem_ggFixSub, kgLangS1ECoverAux_induced_mk, centerQuotAut_mk, hj']
  let πbar : ↥(ggFixSub ξ) →* ↥C :=
    (θ.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center K)).comp
      (Subgroup.subtype (ggFixSub ξ)))).codRestrict C (fun j => hmap_mem j j.2)
  have hπbar_apply : ∀ j : ↥(ggFixSub ξ),
      ((πbar j : ↥C) : R) = θ (QuotientGroup.mk (j : K)) := fun j => rfl
  have hπbar_surj : Function.Surjective πbar := by
    intro r
    obtain ⟨k, hk, hkq⟩ := kgLangS1ECoverAux_surj hp θ hZ hξp r r.2
    exact ⟨⟨k, hk⟩, Subtype.ext hkq⟩
  have honto_of_comp : ∀ {J : Subgroup K}, IsComponentOf J (ggFixSub ξ) →
      ∀ r : ↥C, ∃ j ∈ J, θ (QuotientGroup.mk j) = (r : R) := by
    intro J hJ r
    have hJsub : Assembly.IsSubnormal (J.subgroupOf (ggFixSub ξ)) ⊤ :=
      Assembly.IsSubnormal.of_mathlib ((Assembly.IsSubnormal.iff_subgroupOf hJ.1).mp hJ.2.1)
    have hmap_sub : Assembly.IsSubnormal ((J.subgroupOf (ggFixSub ξ)).map πbar) ⊤ := by
      have h := Assembly.IsSubnormal.map πbar hJsub
      rwa [Subgroup.map_top_of_surjective πbar hπbar_surj] at h
    have hnot_bot : (J.subgroupOf (ggFixSub ξ)).map πbar ≠ ⊥ := by
      intro hbot
      have hJZ : J ≤ Subgroup.center K := by
        intro j hj
        have hmemJ : (⟨j, hJ.1 hj⟩ : ↥(ggFixSub ξ)) ∈ J.subgroupOf (ggFixSub ξ) := by
          rw [Subgroup.mem_subgroupOf]; exact hj
        have h1 : πbar ⟨j, hJ.1 hj⟩ = 1 := by
          have hx : πbar ⟨j, hJ.1 hj⟩ ∈ (J.subgroupOf (ggFixSub ξ)).map πbar :=
            ⟨_, hmemJ, rfl⟩
          rwa [hbot, Subgroup.mem_bot] at hx
        have hmk : QuotientGroup.mk j = 1 := θ.injective (by
          have h := congrArg (fun x : ↥C => (x : R)) h1
          rw [hπbar_apply] at h
          simpa using h)
        exact (QuotientGroup.eq_one_iff j).mp hmk
      haveI : IsMulCommutative ↥J :=
        IsMulCommutative.of_comm fun a b => by
          apply Subtype.ext
          exact (Subgroup.mem_center_iff.mp (hJZ a.2) b).symm
      have hcommbot : commutator ↥J = ⊥ := (commutator_eq_bot_iff ↥J).mpr inferInstance
      haveI : Nontrivial ↥J :=
        CFSG.LocalCores.isQuasisimple_nontrivial
          ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥J).mp
            hJ.2.2)
      have htop := hJ.2.2.1
      rw [hcommbot] at htop
      exact bot_ne_top htop
    have htop : (J.subgroupOf (ggFixSub ξ)).map πbar = ⊤ :=
      (Assembly.IsSubnormal.eq_bot_or_top hmap_sub).resolve_left hnot_bot
    have hr' : r ∈ (J.subgroupOf (ggFixSub ξ)).map πbar := by rw [htop]; trivial
    obtain ⟨x, hx, hxr⟩ := Subgroup.mem_map.mp hr'
    have hxj : (x : K) ∈ J := by rw [Subgroup.mem_subgroupOf] at hx; exact hx
    refine ⟨x, hxj, ?_⟩
    have h := congrArg (fun y : ↥C => (y : R)) hxr
    rwa [hπbar_apply] at h
  have hcenter_bot : Subgroup.center ↥C = ⊥ := by
    rcases hCs.eq_bot_or_eq_top_of_normal (Subgroup.center ↥C) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hCna
      exact hab (Subgroup.mem_center_iff.mp (by rw [h]; trivial : a ∈ Subgroup.center ↥C) b).symm
  refine ⟨fun j hj => hmap_mem j (hJ₀.1 hj), ?_, ?_, ?_⟩
  · intro r hr
    exact honto_of_comp hJ₀ ⟨r, hr⟩
  · intro j hj
    constructor
    · intro h1 j' hj'
      have hmk : QuotientGroup.mk j = 1 := θ.injective (by rw [h1, map_one])
      exact (Subgroup.mem_center_iff.mp ((QuotientGroup.eq_one_iff j).mp hmk) j').symm
    · intro hcomm
      have hcen : (⟨θ (QuotientGroup.mk j), hmap_mem j (hJ₀.1 hj)⟩ : ↥C) ∈
          Subgroup.center ↥C := by
        rw [Subgroup.mem_center_iff]
        intro r
        obtain ⟨j', hj', hj'eq⟩ := honto_of_comp hJ₀ r
        apply Subtype.ext
        change (r : R) * θ (QuotientGroup.mk j) = θ (QuotientGroup.mk j) * (r : R)
        rw [← hj'eq, ← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        rw [hcomm j' hj']
      rw [hcenter_bot, Subgroup.mem_bot] at hcen
      exact Subtype.ext_iff.mp hcen
  · intro α hα j hj
    have hfixα : (ggFixSub ξ).map α.toMonoidHom = ggFixSub ξ := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hy' : ξ y = y := by simpa using hy
        change ξ (α y) = α y
        calc ξ (α y) = (ξ * α) y := rfl
          _ = (α * ξ) y := by rw [hα]
          _ = α (ξ y) := rfl
          _ = α y := by rw [hy']
      · intro hx
        refine ⟨α.symm x, ?_, by simp⟩
        have hx' : ξ x = x := by simpa using hx
        change ξ (α.symm x) = α.symm x
        have hαsymm : α.symm * ξ = ξ * α.symm := by
          change α⁻¹ * ξ = ξ * α⁻¹
          calc α⁻¹ * ξ = α⁻¹ * (ξ * α) * α⁻¹ := by group
            _ = α⁻¹ * (α * ξ) * α⁻¹ := by rw [hα]
            _ = ξ * α⁻¹ := by group
        calc ξ (α.symm x) = (ξ * α.symm) x := rfl
          _ = (α.symm * ξ) x := by rw [hαsymm]
          _ = α.symm (ξ x) := rfl
          _ = α.symm x := by rw [hx']
    have hcomp : IsComponentOf (J₀.map α.toMonoidHom) (ggFixSub ξ) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [← hfixα]
        exact Subgroup.map_mono hJ₀.1
      · rw [← hfixα]
        exact Assembly.IsSubnormal.map α.toMonoidHom hJ₀.2.1
      · exact Assembly.IsQuasisimple.of_mulEquiv
          (J₀.equivMapOfInjective α.toMonoidHom α.injective).symm hJ₀.2.2
    by_cases heq : J₀.map α.toMonoidHom = J₀
    · have : α j ∈ J₀.map α.toMonoidHom := ⟨j, hj, rfl⟩
      rwa [heq] at this
    · exfalso
      rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hJ₀ hcomp with h | h
      · exact heq h.symm
      · have hcomm : ∀ a ∈ J₀, ∀ b ∈ J₀.map α.toMonoidHom, a * b = b * a := by
          intro a ha b hb
          have hmem : a * b * a⁻¹ * b⁻¹ ∈ ⁅J₀, J₀.map α.toMonoidHom⁆ :=
            Subgroup.commutator_mem_commutator ha hb
          rw [h, Subgroup.mem_bot] at hmem
          calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
            _ = b * a := by rw [hmem, one_mul]
        have hCabel : ∀ r s : ↥C, r * s = s * r := by
          intro r s
          apply Subtype.ext
          obtain ⟨a, ha, haeq⟩ := honto_of_comp hJ₀ r
          obtain ⟨b, hb, hbeq⟩ := honto_of_comp hcomp s
          change (r : R) * (s : R) = (s : R) * (r : R)
          rw [← haeq, ← hbeq, ← map_mul, ← map_mul, ← QuotientGroup.mk_mul,
            ← QuotientGroup.mk_mul]
          rw [hcomm a ha b hb]
        obtain ⟨a, b, hab⟩ := hCna
        exact hab (hCabel a b)


end CFSG.StandardType
