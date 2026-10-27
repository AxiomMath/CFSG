module

public import CFSG.Monster.B.GSide.EdgeQCertV

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.TwoA.Amalgam
open CFSG.Monster.B.Co2 (v0 decW)

theorem exists_OmegaW_bV_one
    {v : Wv v0} (hv : v ≠ 0) : ∃ s ∈ Unitary.OmegaW, bV s v = 1 := by
  by_contra hall
  push Not at hall
  apply hv
  have hker : Submodule.span (ZMod 2) (Set.range Co2.wvec) ≤ LinearMap.ker (bV.flip v) := by
    refine Submodule.span_le.2 fun s hs => ?_
    have hs' : s ∈ Unitary.OmegaW := by rw [Unitary.OmegaW_eq]; exact hs
    have h := hall s hs'
    show bV s v = 0
    rcases Fischer.zmod2_cases (bV s v) with h0 | h0
    · exact h0
    · exact absurd h0 h
  rw [Co2.span_wvec] at hker
  exact bV_nondegenerate.2 _ fun x => hker (Submodule.mem_top (x := x))

theorem xhat_ne_one' : xhat ≠ 1 := fun h => by
  have h2 := orderOf_xhat
  rw [h, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem qV_eq_zero_of_mul_self
    (e : Ehat) (h : (e : Dfull) * e = 1) : qV (psiW e) = 0 := by
  by_contra hq
  have hq1 : qV (psiW e) = 1 := zmod2_eq_one_of_ne_zero hq
  have hv : psiW e ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hq1
    exact zero_ne_one hq1
  obtain ⟨s, hs, hsv⟩ := exists_OmegaW_bV_one hv
  obtain ⟨f, hf⟩ := psiW_surjective s
  obtain ⟨g, hg⟩ := psiW_surjective (psiW e + s)
  have hqs : qV s = 0 := qV_of_mem_OmegaW hs
  have hqt : qV (psiW e + s) = 0 := by
    rw [qV_add, hq1, hqs, bV_comm, hsv]
    rfl
  have hf2 : (f : Dfull) * f = 1 := Ehat_mul_self f (by rw [hf]; exact hqs)
  have hg2 : (g : Dfull) * g = 1 := Ehat_mul_self g (by rw [hg]; exact hqt)
  have hb : bV (psiW g) (psiW f) = 1 := by
    rw [hg, hf, map_add, LinearMap.add_apply, bV_self, add_zero, bV_comm]
    exact hsv
  have hc := Ehat_comm g f
  rw [hb, ZMod.val_one, pow_one] at hc
  have hxg : (g : Dfull) * xhat = xhat * g := xhat_comm_of_mem_Jhat (Ehat_le_Jhat g.2)
  have hfg : ((f : Dfull) * g) * ((f : Dfull) * g) = xhat := by
    calc ((f : Dfull) * g) * ((f : Dfull) * g) = f * ((g : Dfull) * f) * g := by group
      _ = f * (f * g * xhat) * g := by rw [hc]
      _ = (f * f) * (g * (xhat * g)) := by group
      _ = (f * f) * (g * (g * xhat)) := by rw [← hxg]
      _ = (f * f) * ((g * g) * xhat) := by group
      _ = xhat := by rw [hf2, hg2, one_mul, one_mul]
  have hpsi : psiW (e⁻¹ * (f * g)) = 0 := by
    rw [psiW_mul, psiW_inv, psiW_mul, hf, hg, ZModModule.neg_eq_self, add_comm s,
      ← add_assoc, ← add_assoc, ZModModule.add_self, zero_add, ZModModule.add_self]
  have hxe : (e : Dfull) * xhat = xhat * e := xhat_comm_of_mem_Jhat (Ehat_le_Jhat e.2)
  rcases (psiW_eq_zero_iff _).1 hpsi with h1 | h1
  · have e1 : (f : Dfull) * g = e := by
      have := congrArg Subtype.val (inv_mul_eq_one.1 h1)
      exact this.symm
    apply xhat_ne_one'
    rw [← hfg, e1, h]
  · have e1 : (f : Dfull) * g = e * xhat := congrArg Subtype.val (inv_mul_eq_iff_eq_mul.1 h1)
    apply xhat_ne_one'
    calc xhat = (e * xhat) * (e * xhat) := by rw [← e1, hfg]
      _ = (e * e) * (xhat * xhat) := by
          calc (e * xhat) * (e * xhat) = (e : Dfull) * (xhat * e) * xhat := by group
            _ = e * (e * xhat) * xhat := by rw [← hxe]
            _ = (e * e) * (xhat * xhat) := by group
      _ = 1 := by rw [h, xhat_mul_self, one_mul]

theorem mul_self_iff_qV
    (e : Ehat) : (e : Dfull) * e = 1 ↔ qV (psiW e) = 0 :=
  ⟨qV_eq_zero_of_mul_self e, Ehat_mul_self e⟩

@[expose] def qToEhat
    {x : cEdgeStab} (h : ((x : Shat) : Dfull) ∈ Ehat) : Ehat := ⟨_, h⟩

theorem mul_self_eq_one_iff_of_edgeQ
    {x : cEdgeStab} (h : ((x : Shat) : Dfull) ∈ Ehat) :
    x * x = 1 ↔ qV (psiW (qToEhat h)) = 0 := by
  rw [← mul_self_iff_qV]
  constructor
  · intro hx
    exact congrArg (fun b : cEdgeStab => ((b : Shat) : Dfull)) hx
  · intro hx
    exact cEdgeStab_val_injective hx

theorem not_mem_cEdgeFix_iff_of_edgeQ
    {x : cEdgeStab} (h : ((x : Shat) : Dfull) ∈ Ehat) :
    (x : Shat) ∉ cEdgeFix ↔ bV Unitary.sigmaW (psiW (qToEhat h)) = 1 := by
  have key : (x : Shat) ∈ cEdgeFix ↔ bV Unitary.sigmaW (psiW (qToEhat h)) = 0 := by
    rw [mem_cEdgeFix_iff, ← mem_N1_iff_bV]
    constructor
    · intro hP
      exact ⟨h, hP.2⟩
    · intro hN
      exact ⟨Ehat_le_Jhat h, hN.2⟩
  rw [key]
  constructor
  · intro hn
    exact zmod2_eq_one_of_ne_zero hn
  · intro h1 h0
    rw [h0] at h1
    exact zero_ne_one h1

@[expose] def edgeO
    (i : Fin 4) : Set cEdgeStab :=
  {x | ∃ h : ((x : Shat) : Dfull) ∈ Ehat, psiW (qToEhat h) ∈ edgeT i}

theorem iUnion_edgeO :
    ⋃ i, edgeO i = {x | x ∈ edgeQ ∧ x * x = 1 ∧ (x : Shat) ∉ cEdgeFix} := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, h, hT⟩
    have hV := edgeT_subset i hT
    exact ⟨h, (mul_self_eq_one_iff_of_edgeQ h).2 hV.2, (not_mem_cEdgeFix_iff_of_edgeQ h).2 hV.1⟩
  · rintro ⟨h, hx, hA⟩
    have hV : psiW (qToEhat h) ∈ edgeV :=
      ⟨(not_mem_cEdgeFix_iff_of_edgeQ h).1 hA, (mul_self_eq_one_iff_of_edgeQ h).1 hx⟩
    rw [← iUnion_edgeT, Set.mem_iUnion] at hV
    obtain ⟨i, hi⟩ := hV
    exact ⟨i, h, hi⟩

theorem edgeO_disjoint :
    Pairwise (Function.onFun Disjoint edgeO) := by
  intro i j hij
  refine Set.disjoint_left.2 fun x hi hj => ?_
  obtain ⟨h, hTi⟩ := hi
  obtain ⟨h', hTj⟩ := hj
  exact Set.disjoint_left.1 (edgeT_disjoint hij) hTi hTj

theorem ncard_psiW_preimage
    (T : Set (Wv v0)) :
    {e : Ehat | psiW e ∈ T}.ncard = 2 * T.ncard := by
  have h := ncard_preimage_of_surjective psiE psiE_surjective (Multiplicative.toAdd ⁻¹' T)
  have e1 : (psiE ⁻¹' (Multiplicative.toAdd ⁻¹' T)) = {e : Ehat | psiW e ∈ T} := rfl
  have e2 : (Multiplicative.toAdd ⁻¹' T).ncard = T.ncard :=
    Set.ncard_preimage_of_injective_subset_range Multiplicative.toAdd.injective
      (fun x _ => ⟨Multiplicative.ofAdd x, rfl⟩)
  rw [← e1, h, natCard_ker_psiE, e2]

theorem edgeO_bij
    (i : Fin 4) :
    Set.BijOn (fun x : cEdgeStab => ((x : Shat) : Dfull)) (edgeO i)
      ((fun e : Ehat => (e : Dfull)) '' {e : Ehat | psiW e ∈ edgeT i}) := by
  refine ⟨fun x hx => ?_, fun x _ y _ hxy => cEdgeStab_val_injective hxy, fun d hd => ?_⟩
  · obtain ⟨h, hT⟩ := hx
    exact ⟨qToEhat h, hT, rfl⟩
  · obtain ⟨e, he, rfl⟩ := hd
    exact ⟨edgeQOf e.2, ⟨e.2, he⟩, rfl⟩

@[expose] def edgeOSize : Fin 4 → ℕ := ![2816, 456192, 1596672, 41472]

theorem ncard_edgeO
    (i : Fin 4) : (edgeO i).ncard = edgeOSize i := by
  rw [(edgeO_bij i).ncard_eq, Set.ncard_image_of_injective _ Subtype.val_injective,
    ncard_psiW_preimage, ncard_edgeT]
  fin_cases i <;> rfl

theorem psiW_ne_zero_of_edgeV
    {v : Wv v0} (h : v ∈ edgeV) : v ≠ 0 := fun h0 => by
  have h1 := h.1
  rw [h0, map_zero] at h1
  exact zero_ne_one h1

theorem psiW_ne_sigma_of_edgeV
    {v : Wv v0} (h : v ∈ edgeV) : v ≠ Unitary.sigmaW := fun h0 => by
  have h1 := h.1
  rw [h0, bV_self] at h1
  exact zero_ne_one h1

@[expose] def edgeORepE (i : Fin 4) : Ehat := (psiW_surjective (decW (orbRep i))).choose

theorem psiW_edgeORepE (i : Fin 4) : psiW (edgeORepE i) = decW (orbRep i) :=
  (psiW_surjective (decW (orbRep i))).choose_spec

@[expose] def edgeORep
    (i : Fin 4) : cEdgeStab := edgeQOf (edgeORepE i).2

theorem qToEhat_edgeORep
    (i : Fin 4) : qToEhat (x := edgeORep i) (edgeORepE i).2 = edgeORepE i :=
  rfl

theorem edgeORep_mem
    (i : Fin 4) : edgeORep i ∈ edgeO i := by
  refine ⟨(edgeORepE i).2, ?_⟩
  rw [qToEhat_edgeORep, psiW_edgeORepE]
  exact Unitary.mem_usigOrbit_self _

theorem conj_mem_edgeO
    {i : Fin 4} {x : cEdgeStab} (hx : x ∈ edgeO i) (a : cEdgeFix) :
    cEdgeIncl a * x * (cEdgeIncl a)⁻¹ ∈ edgeO i := by
  obtain ⟨h, hT⟩ := hx
  have haP : ((a : Shat) : Dfull) ∈ P1 := mem_cEdgeFix_iff.1 a.2
  have haJ : ((a : Shat) : Dfull)⁻¹ ∈ Jhat := Jhat.inv_mem (P1_le_Jhat haP)
  have hval : (((cEdgeIncl a * x * (cEdgeIncl a)⁻¹ : cEdgeStab) : Shat) : Dfull) =
      (((a : Shat) : Dfull)⁻¹)⁻¹ * ((x : Shat) : Dfull) * ((a : Shat) : Dfull)⁻¹ := by
    rw [inv_inv]
    rfl
  have hE : (((cEdgeIncl a * x * (cEdgeIncl a)⁻¹ : cEdgeStab) : Shat) : Dfull) ∈ Ehat := by
    rw [hval]
    exact conj_mem_Ehat haJ h
  refine ⟨hE, ?_⟩
  have hpsi : psiW (qToEhat hE) = wAct v0 (jhatToKv0 ⟨_, haJ⟩) (psiW (qToEhat h)) := by
    have e : qToEhat hE = ⟨(((a : Shat) : Dfull)⁻¹)⁻¹ * ((x : Shat) : Dfull) *
        ((a : Shat) : Dfull)⁻¹, conj_mem_Ehat haJ h⟩ := Subtype.ext hval
    rw [e]
    exact psiW_conj haJ h
  have hU : jhatToKv0 ⟨_, haJ⟩ ∈ Unitary.Usig := by
    have e : jhatToKv0 ⟨_, haJ⟩ = (p1Proj ⟨_, P1.inv_mem haP⟩ : Kstab v0) := rfl
    rw [e]
    exact (p1Proj ⟨_, P1.inv_mem haP⟩).2
  rw [hpsi]
  obtain ⟨u, hu, hux⟩ := hT
  refine ⟨u * jhatToKv0 ⟨_, haJ⟩, Unitary.Usig.mul_mem hu hU, ?_⟩
  rw [Co2.wAct_mul, Module.End.mul_apply, hux]

theorem exists_cEdgeFix_conj_of_P1
    {x y : cEdgeStab} {g : Dfull} (hg : g ∈ P1)
    (hgxy : g⁻¹ * ((x : Shat) : Dfull) * g = ((y : Shat) : Dfull)) :
    ∃ a : cEdgeFix, y = cEdgeIncl a * x * (cEdgeIncl a)⁻¹ := by
  have hgS : g⁻¹ ∈ Shat := Jhat_le_Shat (P1_le_Jhat (P1.inv_mem hg))
  refine ⟨⟨⟨g⁻¹, hgS⟩, mem_cEdgeFix_iff.2 (P1.inv_mem hg)⟩, cEdgeStab_val_injective ?_⟩
  show ((y : Shat) : Dfull) = g⁻¹ * ((x : Shat) : Dfull) * g⁻¹⁻¹
  rw [inv_inv]
  exact hgxy.symm

theorem exists_conj_of_mem_edgeO
    {i : Fin 4} {y : cEdgeStab} (hy : y ∈ edgeO i) :
    ∃ a : cEdgeFix, y = cEdgeIncl a * edgeORep i * (cEdgeIncl a)⁻¹ :=
  hy.elim fun hyE hyT =>
    (show psiW (qToEhat hyE) ∈ Unitary.usigOrbit (psiW (edgeORepE i)) by
      rw [psiW_edgeORepE]; exact hyT).elim fun u hu =>
      (p1Proj_surjective ⟨u, hu.1⟩).elim fun p hp =>
        (exists_P1_conj (a := edgeORepE i) (b := qToEhat hyE) p.2
          (by rw [show jhatToKv0 ⟨p, P1_le_Jhat p.2⟩ = u by rw [← coe_p1Proj, hp]]; exact hu.2)
          (psiW_ne_zero_of_edgeV (edgeT_subset i hyT))
          (psiW_ne_sigma_of_edgeV (edgeT_subset i hyT))).elim fun g hg =>
          exists_cEdgeFix_conj_of_P1 hg.1 hg.2

theorem edgeO_eq_class
    (i : Fin 4) :
    edgeO i = {y | ∃ a : cEdgeFix, y = cEdgeIncl a * edgeORep i * (cEdgeIncl a)⁻¹} := by
  ext y
  constructor
  · exact exists_conj_of_mem_edgeO
  · rintro ⟨a, rfl⟩
    exact conj_mem_edgeO (edgeORep_mem i) a

theorem mem_edgeO_zero_of_label
    {x : cEdgeStab} (hx : x ∈ edgeQ) (hA : (x : Shat) ∉ cEdgeFix)
    (hl : ∃ v, (x : Shat) = clabelS v) : x ∈ edgeO 0 := by
  have h : ((x : Shat) : Dfull) ∈ Ehat := hx
  refine ⟨h, ?_⟩
  obtain ⟨g, hg⟩ := (exists_clabelS_iff (x : Shat)).1 hl
  have hΩ : psiW (qToEhat h) ∈ Unitary.OmegaW := psiW_mem_OmegaW_of_label (t := qToEhat h) hg
  have hb := (not_mem_cEdgeFix_iff_of_edgeQ h).1 hA
  rw [Unitary.OmegaW_eq_union] at hΩ
  rcases hΩ with (hs | hΔ) | hτ
  · rw [Set.mem_singleton_iff] at hs
    rw [hs, bV_self] at hb
    exact absurd hb zero_ne_one
  · have h0 := ((mem_DeltaW_iff ⟨_, Unitary.DeltaW_subset hΔ⟩).1 hΔ).2
    have h1 : bV Unitary.sigmaW (psiW (qToEhat h)) = 0 := h0
    rw [h1] at hb
    exact absurd hb zero_ne_one
  · exact hτ

theorem edgeQCert_Q2 :
    (⋃ i, edgeO i = {x | x ∈ edgeQ ∧ x * x = 1 ∧ (x : Shat) ∉ cEdgeFix}) ∧
    (∀ i, ∃ x ∈ edgeO i, edgeO i = {y | ∃ a : cEdgeFix, y = cEdgeIncl a * x * (cEdgeIncl a)⁻¹}) ∧
    Pairwise (Function.onFun Disjoint edgeO) ∧
    (∀ i, (edgeO i).ncard = ![2816, 456192, 1596672, 41472] i) ∧
    (∀ x ∈ edgeQ, (x : Shat) ∉ cEdgeFix → (∃ v, (x : Shat) = clabelS v) → x ∈ edgeO 0) :=
  ⟨iUnion_edgeO, fun i => ⟨edgeORep i, edgeORep_mem i, edgeO_eq_class i⟩, edgeO_disjoint,
    ncard_edgeO, fun _ hx hA hl => mem_edgeO_zero_of_label hx hA hl⟩

end CFSG.Monster.B.GSide
