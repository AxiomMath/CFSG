module

public import CFSG.RankThree.PartOne.K159H.O3Wpart
public import CFSG.RankThree.PartOne.K159H.O3Rot

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.RankThree.PartOne.K159H

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal.Spin
  CFSG.RankThree.OrthogonalInvolutions Module

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] {r : ℕ}

variable (K) in
@[expose] def Sk (r : ℕ) (k : Fin r) : Subgroup (Fin r → Kˣ) :=
  (Pi.evalMonoidHom (fun _ : Fin r => Kˣ) k).ker

theorem mem_Sk {k : Fin r} {d : Fin r → Kˣ} : d ∈ Sk K r k ↔ d k = 1 := MonoidHom.mem_ker

theorem trivOn_Sk_iff (hK : ∃ u : Kˣ, u ≠ 1) {k : Fin r} (j : Fin r ⊕ Fin r) :
    TrivOn (Sk K r k) j ↔ coordIdx j = k := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨u, hu⟩ := hK
    have hd : (Pi.mulSingle (coordIdx j) u : Fin r → Kˣ) ∈ Sk K r k := by
      rw [mem_Sk, Pi.mulSingle_eq_of_ne (Ne.symm hne)]
    have := h _ hd
    rcases j with m | m
    · simp only [wt_inl, coordIdx_inl] at this
      rw [Pi.mulSingle_eq_same] at this
      exact hu this
    · simp only [wt_inr, coordIdx_inr] at this
      have h2 : ((Pi.mulSingle m u : Fin r → Kˣ) m) = u := by simp
      rw [h2, inv_eq_one] at this
      exact hu this
  · intro h d hd
    rw [mem_Sk] at hd
    rcases j with m | m
    · simp only [coordIdx_inl] at h
      subst h
      exact hd
    · simp only [coordIdx_inr] at h
      subst h
      simp [wt_inr, hd]

variable (qA : QuadraticForm K A)

@[expose] def Bshort (k : Fin r) : Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) where
  carrier := {g | g ∈ Om qA r ∧ ∀ c, coordIdx c ≠ k → g (hypVec K A c) = hypVec K A c}
  mul_mem' := by
    rintro g h ⟨hg, hgf⟩ ⟨hh, hhf⟩
    refine ⟨mul_mem hg hh, fun c hc => ?_⟩
    rw [LinearEquiv.mul_apply, hhf c hc, hgf c hc]
  one_mem' := ⟨one_mem _, fun c _ => rfl⟩
  inv_mem' := by
    rintro g ⟨hg, hgf⟩
    refine ⟨inv_mem hg, fun c hc => ?_⟩
    conv_lhs => rw [← hgf c hc]
    exact LinearEquiv.inv_apply_apply' g _

variable {qA}

theorem eichler_tail_mem_Bshort [Finite K] [CharP K 2] [FiniteDimensional K A]
    (hreg : (polarBilin qA).Nondegenerate) (hr : 3 ≤ r) {c : Fin r ⊕ Fin r} (a : A) :
    eichler (quadTail r qA) (hypVec K A c) ((0 : Fin r ⊕ Fin r → K), a) ∈ Bshort qA (coordIdx c) := by
  refine ⟨eichler_mem_Om hreg hr _ _, fun c' hc' => ?_⟩
  refine eichler_apply_of_polar_eq_zero ?_ (polar_hypVec_tail c' a)
  rw [polar_hypVec_hypVec, ite_eq_right]
  intro h
  apply hc'
  rw [h, coordIdx_swap]

theorem Bshort_fix_Sk (hK : ∃ u : Kˣ, u ≠ 1) {k : Fin r} {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)}
    (hg : g ∈ Bshort qA k) : ∀ j, ¬ TrivOn (Sk K r k) j → g (hypVec K A j) = hypVec K A j := fun j hj =>
  hg.2 j fun h => hj ((trivOn_Sk_iff hK j).2 h)

theorem torH_mem_Bshort_iff [Finite K] [CharP K 2] [FiniteDimensional K A]
    (hreg : (polarBilin qA).Nondegenerate) (hr : 3 ≤ r) (k : Fin r) (d : Fin r → Kˣ) :
    torH K A r d ∈ Bshort qA k ↔ ∀ c, coordIdx c ≠ k → wt d c = 1 := by
  constructor
  · intro h c hc
    have h1 := h.2 c hc
    rw [torH_hypVec] at h1
    have := congrFun (congrArg Prod.fst h1) c
    simp only [Prod.smul_fst, Pi.smul_apply, hypVec_fst, smul_eq_mul, ite_true, mul_one] at this
    exact Units.ext this
  · intro h
    refine ⟨torH_mem_Om hreg hr d, fun c hc => ?_⟩
    rw [torH_hypVec, h c hc, Units.val_one, one_smul]

theorem Bshort_comm_torH [Finite K] [CharP K 2] [FiniteDimensional K A] (hK : ∃ u : Kˣ, u ≠ 1)
    (_hreg : (polarBilin qA).Nondegenerate) (_hr : 3 ≤ r) {k : Fin r} {d : Fin r → Kˣ} (hd : d k = 1)
    {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)} (hg : g ∈ Bshort qA k) :
    g * torH K A r d = torH K A r d * g := by
  have hgO := Om_le_orth hg.1
  have hwk : ∀ c, coordIdx c = k → wt d c = 1 := by
    intro c hc
    rcases c with m | m
    · simp only [coordIdx_inl] at hc
      subst hc
      exact hd
    · simp only [coordIdx_inr] at hc
      subst hc
      simp [wt_inr, hd]
  have hW : ∀ v : (Fin r ⊕ Fin r → K) × A, v ∈ Wsub (K := K) (A := A) (Sk K r k) →
      torH K A r d v = v := by
    intro v hv
    refine Prod.ext (funext fun c => ?_) rfl
    rw [torH_fst]
    by_cases hc : coordIdx c = k
    · rw [hwk c hc, Units.val_one, one_mul]
    · have : ¬ TrivOn (Sk K r k) c := fun h => hc ((trivOn_Sk_iff hK c).1 h)
      rw [hv c this, mul_zero]
  refine ext_frame_tail (fun c => ?_) (fun a => ?_)
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    by_cases hc : coordIdx c = k
    · have hcW : hypVec K A c ∈ Wsub (K := K) (A := A) (Sk K r k) :=
        hypVec_mem_Wsub ((trivOn_Sk_iff hK c).2 hc)
      rw [hW _ hcW]
      have hgW := ((supp_Wsub (S := Sk K r k) hgO (Bshort_fix_Sk hK hg)) (hypVec K A c)).1 hcW
      rw [hW _ hgW]
    · rw [hg.2 c hc, torH_hypVec, map_smul, hg.2 c hc]
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, torH_snd_zero]
    have hgW := ((supp_Wsub (S := Sk K r k) hgO (Bshort_fix_Sk hK hg)) ((0 : Fin r ⊕ Fin r → K), a)).1
      (tail_mem_Wsub a)
    rw [hW _ hgW]

section Simple

variable [Finite K] [CharP K 2] [FiniteDimensional K A]

omit [Finite K] [CharP K 2] [FiniteDimensional K A] in
theorem regular_Wsub {S : Subgroup (Fin r → Kˣ)} (hreg : (polarBilin qA).Nondegenerate) :
    (polarBilin ((quadTail r qA).restrict (Wsub (K := K) (A := A) S))).Nondegenerate :=
  nondegenerate_polarBilin_restrict (polarNondegOn_Wsub hreg)

theorem Wsub_omega_facts {S : Subgroup (Fin r → Kˣ)} (hreg : (polarBilin qA).Nondegenerate)
    (hani : qA.Anisotropic) (hdim : finrank K A = 2) (hr : r = 3) (hnt : ∃ j, ¬ TrivOn S j)
    (htr : ∃ j, TrivOn S j) :
    omegaGroup ((quadTail r qA).restrict (Wsub (K := K) (A := A) S)) (regular_Wsub hreg) =
        elementaryGroup ((quadTail r qA).restrict (Wsub (K := K) (A := A) S)) ∧
      IsSimpleGroup ↥(omegaGroup ((quadTail r qA).restrict (Wsub (K := K) (A := A) S)) (regular_Wsub hreg)) ∧
      Group.IsPerfect ↥(omegaGroup ((quadTail r qA).restrict (Wsub (K := K) (A := A) S)) (regular_Wsub hreg)) := by
  have hr3 : 3 ≤ r := by omega
  have hQ := nondegenerate_polarBilin_quadTail (r := r) hreg
  have hS := regular_Wsub (S := S) hreg
  have hd := finrank_Wsub_cases (S := S) hdim hr hnt htr
  have hts := fun (U : Submodule K ↥(Wsub (K := K) (A := A) S))
      (hU : finrank K U = finrank K (Wsub (K := K) (A := A) S) / 2) => hts_Wsub hani hdim U hU
  have hEΩ : elementaryGroup (quadTail r qA) ≤ omegaGroup (quadTail r qA) hQ := by
    rw [← Om_eq_omega hreg hr3, ← Om_eq_elementary hreg hr3]
  have hEΩ' := elementary_restrict_le_omega hS hEΩ
  obtain ⟨i, hi⟩ := exists_pair_trivial htr
  obtain ⟨-, hsimple, hperf⟩ := omega_eq_derived_small hS hd hts
  exact ⟨le_antisymm (omega_le_elementary_small hS hd hts hEΩ' (exists_nontrivial_eichler_Wsub hdim hi)) hEΩ',
    hsimple, hperf⟩

end Simple

section Iso

variable [Finite K] [CharP K 2] [FiniteDimensional K A]

@[expose] def resB (hK : ∃ u : Kˣ, u ≠ 1) (k : Fin r) :
    ↥(Bshort qA k) →* (↥(Wsub (K := K) (A := A) (Sk K r k)) ≃ₗ[K] ↥(Wsub (K := K) (A := A) (Sk K r k))) where
  toFun g := resAut g.1 (supp_Wsub (Om_le_orth g.2.1) (Bshort_fix_Sk hK g.2))
  map_one' := LinearEquiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => Subtype.ext rfl

theorem resB_injective (hK : ∃ u : Kˣ, u ≠ 1) (hreg : (polarBilin qA).Nondegenerate) (k : Fin r) :
    Function.Injective (resB (qA := qA) hK k) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply Subtype.ext
  refine eq_of_agree_on' (regular_Wsub hreg) (fun x hx => ?_)
    (fun z hz => fix_perp_Wsub hreg (Bshort_fix_Sk hK g.2) hz) (fun z _ => rfl)
  have h := congrArg Subtype.val (LinearEquiv.congr_fun hg ⟨x, hx⟩)
  exact h

omit [Finite K] [CharP K 2] in
theorem Sk_triv (k : Fin r) : ∃ j, TrivOn (Sk K r k) j :=
  ⟨Sum.inl k, fun d hd => by rw [mem_Sk] at hd; exact hd⟩

omit [Finite K] [CharP K 2] in
theorem Sk_nontriv (hK : ∃ u : Kˣ, u ≠ 1) (hr2 : 2 ≤ r) (k : Fin r) : ∃ j, ¬ TrivOn (Sk K r k) j := by
  have : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.2 hr2
  obtain ⟨k', hk'⟩ := exists_ne k
  exact ⟨Sum.inl k', fun h => hk' ((trivOn_Sk_iff hK _).1 h)⟩

theorem resB_range (hK : ∃ u : Kˣ, u ≠ 1) (hreg : (polarBilin qA).Nondegenerate) (hani : qA.Anisotropic)
    (hdim : finrank K A = 2) (hr : r = 3) (k : Fin r) :
    (resB (qA := qA) hK k).range = omegaGroup ((quadTail r qA).restrict (Wsub (K := K) (A := A) (Sk K r k)))
      (regular_Wsub hreg) := by
  have hr3 : 3 ≤ r := by omega
  have hQ := nondegenerate_polarBilin_quadTail (r := r) hreg
  have hS := regular_Wsub (S := Sk K r k) hreg
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    have hgΩ : g.1 ∈ omegaGroup (quadTail r qA) hQ := by
      rw [← Om_eq_omega hreg hr3]
      exact g.2.1
    exact resAut_mem_omega hS hgΩ (supp_Wsub (Om_le_orth g.2.1) (Bshort_fix_Sk hK g.2))
      (fun z hz => fix_perp_Wsub hreg (Bshort_fix_Sk hK g.2) hz)
  · intro g' hg'
    have hE : g' ∈ elementaryGroup ((quadTail r qA).restrict (Wsub (K := K) (A := A) (Sk K r k))) := by
      rw [← (Wsub_omega_facts hreg hani hdim hr (Sk_nontriv hK (by omega) k) (Sk_triv k)).1]
      exact hg'
    obtain ⟨g, hgE, hgx, hgz⟩ := exists_extend_of_mem_elementaryGroup_restrict hE
    have hgOm : g ∈ Om qA r := by
      rw [Om_eq_elementary hreg hr3]
      exact hgE
    have hfixB : ∀ c, coordIdx c ≠ k → g (hypVec K A c) = hypVec K A c := by
      intro c hc
      refine hgz _ fun x hx => ?_
      rw [polar_comm, polar_hypVec]
      have hnt : ¬ TrivOn (Sk K r k) c.swap := fun h =>
        hc ((trivOn_Sk_iff hK c).1 ((trivOn_swap_iff _ c).1 h))
      exact hx c.swap hnt
    exact ⟨⟨g, hgOm, hfixB⟩, LinearEquiv.ext fun x => Subtype.ext (hgx x)⟩

@[expose] noncomputable def BshortEquiv (hK : ∃ u : Kˣ, u ≠ 1) (hreg : (polarBilin qA).Nondegenerate)
    (hani : qA.Anisotropic) (hdim : finrank K A = 2) (hr : r = 3) (k : Fin r) :
    ↥(Bshort qA k) ≃* ↥(omegaGroup ((quadTail r qA).restrict (Wsub (K := K) (A := A) (Sk K r k)))
      (regular_Wsub hreg)) :=
  (MonoidHom.ofInjective (resB_injective hK hreg k)).trans
    (MulEquiv.subgroupCongr (resB_range hK hreg hani hdim hr k))

theorem isSimpleGroup_Bshort (hK : ∃ u : Kˣ, u ≠ 1) (hreg : (polarBilin qA).Nondegenerate)
    (hani : qA.Anisotropic) (hdim : finrank K A = 2) (hr : r = 3) (k : Fin r) :
    IsSimpleGroup ↥(Bshort qA k) := by
  have h := (Wsub_omega_facts hreg hani hdim hr (Sk_nontriv hK (by omega) k) (Sk_triv k)).2.1
  exact (BshortEquiv hK hreg hani hdim hr k).isSimpleGroup

theorem Bshort_perfect (hK : ∃ u : Kˣ, u ≠ 1) (hreg : (polarBilin qA).Nondegenerate)
    (hani : qA.Anisotropic) (hdim : finrank K A = 2) (hr : r = 3) (k : Fin r) :
    ⁅Bshort qA k, Bshort qA k⁆ = Bshort qA k := by
  have hperf := (Wsub_omega_facts hreg hani hdim hr (Sk_nontriv hK (by omega) k) (Sk_triv k)).2.2
  have : Group.IsPerfect ↥(Bshort qA k) :=
    @Group.IsPerfect.ofSurjective _ _ _ _ (BshortEquiv hK hreg hani hdim hr k).symm.toMonoidHom hperf
      (BshortEquiv hK hreg hani hdim hr k).symm.surjective
  exact Subgroup.isPerfect_iff.1 this

end Iso

end CFSG.RankThree.PartOne.K159H
