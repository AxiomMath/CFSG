module

public import CFSG.LocalAnalysis.StandardType.GGReflExtBasic
public import CFSG.LocalAnalysis.StandardType.GGFLWReflForm
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import Certificates.Data.CFSGNative.ReflExt.Check
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosFacts
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosWeyl
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallRankDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallVerifyK
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallVerifyW

public section

namespace CFSG.ReflExt

open CFSG.TwoNodeSmall CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem verifyAll_elim {P0 : Pt} {T : Tables} (h : verifyAll P0 T = true) :
    wfCheck P0 = true ∧ vRoots P0 T = true ∧ vCover P0 T (candOf P0 T) = true ∧
      T.orb1.all (entryOK P0 T) = true ∧ T.reps.all (verifyRep P0 T (candOf P0 T)) = true := by
  unfold verifyAll at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem vRoots_elim {P0 : Pt} {T : Tables} (h : vRoots P0 T = true) :
    ∀ ρ ∈ T.roots, wfR P0 ρ.r = true ∧ realizes P0 ρ.w ρ.r = true ∧ P0.dotv ρ.r.f P0.x = 0 := by
  intro ρ hρ
  unfold vRoots at h
  have := List.all_eq_true.mp h ρ hρ
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem entryOK_elim {P0 : Pt} {T : Tables} {e : OEnt} (h : entryOK P0 T e = true) :
    wfR P0 e.e = true ∧ ∃ rp, T.reps[e.j]? = some rp ∧
      realizes (withExtra P0 [e.e]) (e.w ++ [P0.gens.length] ++ e.w.reverse) rp.r = true := by
  unfold entryOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, _⟩, h3⟩ := h
  refine ⟨h1, ?_⟩
  cases hr : T.reps[e.j]? with
  | none => rw [hr] at h3; simp at h3
  | some rp => rw [hr] at h3; exact ⟨rp, rfl, h3⟩

theorem s2Orb_elim {P0 : Pt} {rp : Rep} (h : s2Orb P0 rp = true) :
    ∀ x ∈ rp.orb2, wfR P0 x.e = true ∧ ∃ q, rp.reps2[x.j]? = some q ∧
      realizes (withExtra P0 [rp.r, x.e]) (x.w ++ [P0.gens.length + 1] ++ x.w.reverse) q.r = true := by
  intro x hx
  unfold s2Orb at h
  have := List.all_eq_true.mp h x hx
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  obtain ⟨⟨h1, _⟩, h3⟩ := this
  refine ⟨h1, ?_⟩
  cases hr : rp.reps2[x.j]? with
  | none => rw [hr] at h3; simp at h3
  | some q => rw [hr] at h3; exact ⟨q, rfl, h3⟩

theorem s2Cand_elim {P0 : Pt} {T : Tables} {rp : Rep} {c : Refl} (h : s2Cand P0 T rp c = true) :
    (∃ ρ ∈ rp.roots, reqb c ρ.r = true) ∨
    (∃ ρ ∈ rp.roots, asymR (withExtra P0 [rp.r]) c ρ.r = true) ∨
    (∃ x ∈ rp.orb2, reqb x.e c = true) ∨
    (rp.maximal = false ∧ ∃ e ∈ T.orb1, reqb e.e c = true ∧ ∃ rq, T.reps[e.j]? = some rq ∧
      rq.isGoodMax = true) := by
  unfold s2Cand at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, List.mem_map, Bool.not_eq_true',
    asymAny] at h
  rcases h with ((⟨r, ⟨ρ, hρ, rfl⟩, hr⟩ | ⟨r, ⟨ρ, hρ, rfl⟩, hr⟩) | ⟨x, hx, hxc⟩) | ⟨hm, e, he, hec, hrq⟩
  · exact Or.inl ⟨ρ, hρ, hr⟩
  · exact Or.inr (Or.inl ⟨ρ, hρ, hr⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨x, hx, hxc⟩))
  · refine Or.inr (Or.inr (Or.inr ⟨hm, e, he, hec, ?_⟩))
    cases hr : T.reps[e.j]? with
    | none => rw [hr] at hrq; simp at hrq
    | some rq => rw [hr] at hrq; exact ⟨rq, rfl, hrq⟩

theorem verifyRep_bad {P0 : Pt} {T : Tables} {cand : List Refl} {rp : Rep} {o : OWit}
    (hk : rp.kind = .bad o) (h : verifyRep P0 T cand rp = true) :
    wfCheck (withExtra P0 [rp.r]) = true ∧ verifyO (withExtra P0 [rp.r]) o P0.bound = true := by
  unfold verifyRep at h
  rw [hk] at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.2, h.2⟩

theorem verifyRep_good {P0 : Pt} {T : Tables} {cand : List Refl} {rp : Rep} {c : WWit}
    (hk : rp.kind = .good c) (h : verifyRep P0 T cand rp = true) :
    wfCheck (withExtra P0 [rp.r]) = true ∧ verifyWPos (withExtra P0 [rp.r]) c = true ∧
      verifyStage2 P0 T cand rp = true := by
  unfold verifyRep at h
  rw [hk] at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.2, h.2.1, h.2.2⟩

theorem verifyStage2_elim {P0 : Pt} {T : Tables} {cand : List Refl} {rp : Rep}
    (h : verifyStage2 P0 T cand rp = true) :
    s2Roots P0 rp = true ∧ s2Reps P0 rp = true ∧ s2Orb P0 rp = true ∧
      ∀ c ∈ cand, s2Cand P0 T rp c = true := by
  unfold verifyStage2 at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem Rep.good_of_goodMax {rp : Rep} (h : rp.isGoodMax = true) :
    (∃ cw, rp.kind = .good cw) ∧ rp.maximal = true := by
  unfold Rep.isGoodMax at h
  cases hk : rp.kind with
  | bad o => rw [hk] at h; simp at h
  | good cw => rw [hk] at h; exact ⟨⟨cw, rfl⟩, h⟩

structure Ctx (P0 : Pt) [Fact P0.p.Prime] (T : Tables)
    (A : Subgroup (P0.V ≃ₗ[ZMod P0.p] P0.V)) : Prop where
  hp2 : P0.p ≠ 2
  frame : ∀ r ∈ P0.gens, HasRefl P0 A r
  rgen : A = Subgroup.closure {s | s ∈ A ∧ GGLinRefl s}
  nt : ∀ g ∈ A, ¬ IsTransv g
  card : Nat.card A ≤ P0.bound
  ok : verifyAll P0 T = true

variable {P0 : Pt} [Fact P0.p.Prime] {T : Tables} {A : Subgroup (P0.V ≃ₗ[ZMod P0.p] P0.V)}

theorem Ctx.wf0c (C : Ctx P0 T A) : wfCheck P0 = true := (verifyAll_elim C.ok).1

theorem Ctx.wf0 (C : Ctx P0 T A) : P0.WF := wfCheck_sound C.wf0c

theorem Ctx.group_le (C : Ctx P0 T A) {extra : List Refl} (h : ∀ r ∈ extra, HasRefl P0 A r) :
    (withExtra P0 extra).group ≤ A := by
  apply withExtra_group_le P0 extra A
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact C.frame r hr
  · exact h r hr

theorem Ctx.roots_hasRefl (C : Ctx P0 T A) : ∀ ρ ∈ T.roots, HasRefl P0 A ρ.r := by
  intro ρ hρ
  obtain ⟨_, hreal, _⟩ := vRoots_elim (verifyAll_elim C.ok).2.1 ρ hρ
  obtain ⟨γ, hγ, hγf⟩ := realizes_hasRefl C.wf0 hreal
  exact ⟨γ, group_le_of_gens P0 A C.frame hγ, hγf⟩

theorem refl_datum (hp2 : P0.p ≠ 2) {s : P0.V ≃ₗ[ZMod P0.p] P0.V} (hs : GGLinRefl s) :
    ∃ c : Refl, wfR P0 c = true ∧ c.f ∈ allVecsP P0.p P0.D ∧ c.h ∈ allVecsP P0.p P0.D ∧
      ∀ w, s w = w - P0.dot (P0.vec c.f) w • P0.vec c.h := by
  obtain ⟨h', β, hh', hβ, hsf⟩ := ggFLW_isRefl_form hp2 (t := s) hs
  have key : β = pww2_dotLM P0 (fun i => β (Pi.single i 1)) := by
    apply pww2_lin_ext_unit P0
    intro j
    rw [Pt.vec_unit, dotLM_apply, pww2_dot_single]
  have hdot : ∀ w, β w = P0.dot (fun i => β (Pi.single i 1)) w := fun w =>
    (congrArg (fun φ : Module.Dual (ZMod P0.p) P0.V => φ w) key).trans
      (dotLM_apply P0 (fun i => β (Pi.single i 1)) w)
  refine ⟨⟨natVec P0 (fun i => β (Pi.single i 1)), natVec P0 h'⟩, ?_,
    natVec_mem P0 (fun i => β (Pi.single i 1)), natVec_mem P0 h', ?_⟩
  · rw [wfR_iff, vec_natVec, vec_natVec, ← hdot]
    exact hβ
  · intro w
    rw [hsf w, vec_natVec, vec_natVec, ← hdot]

theorem Ctx.datum_cand (C : Ctx P0 T A) {c : Refl} (hc : wfR P0 c = true)
    (hf : c.f ∈ allVecsP P0.p P0.D) (hh : c.h ∈ allVecsP P0.p P0.D) (hcA : HasRefl P0 A c) :
    c ∈ candOf P0 T := by
  unfold candOf
  have hdot : P0.dotv c.f c.h = 2 % P0.p := by
    unfold wfR at hc
    exact beq_iff_eq.mp hc
  apply mem_candList P0 _ c hf hh hdot
  intro ρ' hρ'
  obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.mp hρ'
  cases hasym : asymR P0 c ρ.r with
  | false => rfl
  | true =>
    obtain ⟨hwρ, _, _⟩ := vRoots_elim (verifyAll_elim C.ok).2.1 ρ hρ
    obtain ⟨g, hgA, hg⟩ := asym_transv C.hp2 hc hwρ hcA (C.roots_hasRefl ρ hρ) hasym
    exact (C.nt g hgA hg).elim

theorem Ctx.entry_rep (C : Ctx P0 T A) {e : OEnt} (he : e ∈ T.orb1) (heA : HasRefl P0 A e.e)
    {rp : Rep} (hrp : T.reps[e.j]? = some rp) : HasRefl P0 A rp.r := by
  obtain ⟨hwf, rp', hrp', hreal⟩ :=
    entryOK_elim (List.all_eq_true.mp (verifyAll_elim C.ok).2.2.2.1 e he)
  rw [hrp] at hrp'
  have hrr : rp' = rp := (Option.some.inj hrp').symm
  subst hrr
  have hw : (withExtra P0 [e.e]).WF :=
    wfCheck_sound (wfCheck_withExtra C.wf0c (by
      intro r hr
      rw [List.mem_singleton] at hr
      rw [hr]
      exact hwf))
  obtain ⟨γ, hγ, hγf⟩ := realizes_hasRefl hw hreal
  have hle : (withExtra P0 [e.e]).group ≤ A := by
    apply C.group_le
    intro r hr
    rw [List.mem_singleton] at hr
    rw [hr]
    exact heA
  exact ⟨γ, hle hγ, hγf⟩

theorem Ctx.rep_of_moving (C : Ctx P0 T A) {t : P0.V ≃ₗ[ZMod P0.p] P0.V} (htA : t ∈ A)
    (htr : GGLinRefl t) (htm : t (P0.vec P0.x) ≠ P0.vec P0.x) :
    ∃ rp ∈ T.reps, HasRefl P0 A rp.r := by
  obtain ⟨c, hc, hcf, hch, hct⟩ := refl_datum C.hp2 htr
  have hcA : HasRefl P0 A c := ⟨t, htA, hct⟩
  have hcand := C.datum_cand hc hcf hch hcA
  have hmov : c ∈ movingOf P0 (candOf P0 T) := by
    unfold movingOf
    rw [List.mem_filter]
    refine ⟨hcand, ?_⟩
    have hne : P0.dot (P0.vec c.f) (P0.vec P0.x) ≠ 0 := by
      intro h0
      apply htm
      rw [hct, h0, zero_smul, sub_zero]
    have : P0.dotv c.f P0.x ≠ 0 := fun h0 => hne ((dotv_eq_zero_iff P0 _ _).mp h0)
    simpa using this
  obtain ⟨e, he, hec⟩ := List.any_eq_true.mp
    (List.all_eq_true.mp (verifyAll_elim C.ok).2.2.1 c hmov)
  have hee : e.e = c := reqb_eq hec
  obtain ⟨_, rp, hrp, _⟩ := entryOK_elim (List.all_eq_true.mp (verifyAll_elim C.ok).2.2.2.1 e he)
  exact ⟨rp, List.mem_of_getElem? hrp, C.entry_rep he (by rw [hee]; exact hcA) hrp⟩

theorem Ctx.not_bad (C : Ctx P0 T A) {rp : Rep} (hrp : rp ∈ T.reps) {o : OWit}
    (hk : rp.kind = .bad o) (hA : HasRefl P0 A rp.r) : False := by
  obtain ⟨hwf, hv⟩ := verifyRep_bad hk (List.all_eq_true.mp (verifyAll_elim C.ok).2.2.2.2 rp hrp)
  apply order_contra P0 [rp.r] (wfCheck_sound hwf) hv A _ C.card
  apply C.group_le
  intro r hr
  rw [List.mem_singleton] at hr
  rw [hr]
  exact hA

theorem Ctx.refl_class (C : Ctx P0 T A) {rp : Rep} (hrp : rp ∈ T.reps) {cw : WWit}
    (hk : rp.kind = .good cw) (hA : HasRefl P0 A rp.r) {s : P0.V ≃ₗ[ZMod P0.p] P0.V}
    (hsA : s ∈ A) (hsr : GGLinRefl s) :
    s ∈ (withExtra P0 [rp.r]).group ∨
      (rp.maximal = false ∧ ∃ rq ∈ T.reps, rq.isGoodMax = true ∧ HasRefl P0 A rq.r) := by
  obtain ⟨hwfj, hW, hS2⟩ :=
    verifyRep_good hk (List.all_eq_true.mp (verifyAll_elim C.ok).2.2.2.2 rp hrp)
  obtain ⟨hs2roots, hs2reps, hs2orb, hs2cand⟩ := verifyStage2_elim hS2
  have hwj : (withExtra P0 [rp.r]).WF := wfCheck_sound hwfj
  have hwr : wfR P0 rp.r = true := wfR_of_wfCheck hwfj (by simp [withExtra])
  have hleJ : (withExtra P0 [rp.r]).group ≤ A := by
    apply C.group_le
    intro r hr
    rw [List.mem_singleton] at hr
    rw [hr]
    exact hA
  obtain ⟨c, hc, hcf, hch, hcs⟩ := refl_datum C.hp2 hsr
  have hcA : HasRefl P0 A c := ⟨s, hsA, hcs⟩
  have hcand := C.datum_cand hc hcf hch hcA
  rcases s2Cand_elim (hs2cand c hcand) with
    ⟨ρ, hρ, hρc⟩ | ⟨ρ, hρ, hρc⟩ | ⟨x, hx, hxc⟩ | ⟨hm, e, he, hec, rq, hrq, hgm⟩
  ·
    left
    have hreal := List.all_eq_true.mp hs2roots ρ hρ
    simp only [Bool.and_eq_true] at hreal
    obtain ⟨γ, hγ, hγf⟩ := realizes_hasRefl hwj hreal.2
    have hcρ : c = ρ.r := reqb_eq hρc
    have hsγ : s = γ := by
      apply LinearEquiv.ext
      intro w
      rw [hcs w, hγf w, hcρ]
      rfl
    rw [hsγ]
    exact hγ
  ·
    exfalso
    have hreal := List.all_eq_true.mp hs2roots ρ hρ
    simp only [Bool.and_eq_true] at hreal
    obtain ⟨γ, hγ, hγf⟩ := realizes_hasRefl hwj hreal.2
    obtain ⟨g, hgA, hg⟩ := asym_transv (P := withExtra P0 [rp.r]) C.hp2 hc hreal.1 hcA
      ⟨γ, hleJ hγ, hγf⟩ hρc
    exact C.nt g hgA hg
  ·
    exfalso
    obtain ⟨hwx, q, hq, hreal⟩ := s2Orb_elim hs2orb x hx
    have hxe : x.e = c := reqb_eq hxc
    have hqmem : q ∈ rp.reps2 := List.mem_of_getElem? hq
    have hq2 := List.all_eq_true.mp hs2reps q hqmem
    simp only [Bool.and_eq_true] at hq2
    obtain ⟨⟨hwq, hwfq⟩, hvq⟩ := hq2
    have hwx' : (withExtra P0 [rp.r, x.e]).WF :=
      wfCheck_sound (wfCheck_withExtra C.wf0c (by
        intro r hr
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hwr
        · exact hwx))
    obtain ⟨γ, hγ, hγf⟩ := realizes_hasRefl hwx' hreal
    have hleX : (withExtra P0 [rp.r, x.e]).group ≤ A := by
      apply C.group_le
      intro r hr
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hA
      · rw [hxe]; exact hcA
    have hqA : HasRefl P0 A q.r := ⟨γ, hleX hγ, hγf⟩
    apply order_contra P0 [rp.r, q.r] (wfCheck_sound hwfq) hvq A _ C.card
    apply C.group_le
    intro r hr
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hA
    · exact hqA
  ·
    right
    refine ⟨hm, rq, List.mem_of_getElem? hrq, hgm, ?_⟩
    have hecA : HasRefl P0 A e.e := by rw [reqb_eq hec]; exact hcA
    exact C.entry_rep he hecA hrq

theorem Ctx.eq_of_goodMax (C : Ctx P0 T A) {rp : Rep} (hrp : rp ∈ T.reps)
    (hgm : rp.isGoodMax = true) (hA : HasRefl P0 A rp.r) : A = (withExtra P0 [rp.r]).group := by
  obtain ⟨⟨cw, hk⟩, hmax⟩ := Rep.good_of_goodMax hgm
  apply le_antisymm
  · conv_lhs => rw [C.rgen]
    rw [Subgroup.closure_le]
    rintro s ⟨hsA, hsr⟩
    rcases C.refl_class hrp hk hA hsA hsr with h | ⟨hm, _⟩
    · exact h
    · rw [hmax] at hm
      exact absurd hm (by decide)
  · apply C.group_le
    intro r hr
    rw [List.mem_singleton] at hr
    rw [hr]
    exact hA

theorem Ctx.linWeyl_of_good
    (C : Ctx P0 T A) {rp : Rep} (hrp : rp ∈ T.reps) {cw : WWit} (hk : rp.kind = .good cw) :
    ZS.LinWeyl P0.p (withExtra P0 [rp.r]).group := by
  obtain ⟨hwfj, hW, _⟩ := verifyRep_good hk (List.all_eq_true.mp (verifyAll_elim C.ok).2.2.2.2 rp hrp)
  exact verifyWPos_sound (wfCheck_sound hwfj) hW

theorem Ctx.linWeyl (C : Ctx P0 T A)
    {t : P0.V ≃ₗ[ZMod P0.p] P0.V} (htA : t ∈ A) (htr : GGLinRefl t)
    (htm : t (P0.vec P0.x) ≠ P0.vec P0.x) : ZS.LinWeyl P0.p A := by
  obtain ⟨rp0, hrp0, hA0⟩ := C.rep_of_moving htA htr htm
  cases hk : rp0.kind with
  | bad o => exact (C.not_bad hrp0 hk hA0).elim
  | good cw =>
    by_cases hex : ∃ rq ∈ T.reps, rq.isGoodMax = true ∧ HasRefl P0 A rq.r
    · obtain ⟨rq, hrq, hgm, hAq⟩ := hex
      obtain ⟨⟨cq, hkq⟩, _⟩ := Rep.good_of_goodMax hgm
      have heq := C.eq_of_goodMax hrq hgm hAq
      have hw := C.linWeyl_of_good hrq hkq
      rw [← heq] at hw
      exact hw
    · have hle : (withExtra P0 [rp0.r]).group ≤ A := by
        apply C.group_le
        intro r hr
        rw [List.mem_singleton] at hr
        rw [hr]
        exact hA0
      have heq : A = (withExtra P0 [rp0.r]).group := by
        apply le_antisymm _ hle
        conv_lhs => rw [C.rgen]
        rw [Subgroup.closure_le]
        rintro s ⟨hsA, hsr⟩
        rcases C.refl_class hrp0 hk hA0 hsA hsr with h | ⟨_, hrq⟩
        · exact h
        · exact (hex hrq).elim
      have hw := C.linWeyl_of_good hrp0 hk
      rw [← heq] at hw
      exact hw

end CFSG.ReflExt

end
