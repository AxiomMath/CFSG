module

public import CFSG.LocalAnalysis.StandardType.GGReflExtTransport
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallSound
public import Certificates.Data.CFSGNative.NineAll.Check

public section

namespace CFSG.NineAll

open CFSG.TwoNodeSmall CFSG.ReflExt CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose, reducible] def NCore (P0 : Pt) (Bstab : ℕ) (T : NTables) : Prop :=
  wfCheck P0 = true ∧ vFixN P0 = true ∧ vRootsN P0 T = true ∧
    vCover0 P0 T (candOfN P0 T) = true ∧ T.orb0.all (entry0OK P0 T) = true ∧
    T.reps0.all (rep0OK P0 Bstab) = true ∧ vCover1 P0 T (candOfN P0 T) = true ∧
    T.orb1.all (entry1OK P0 T) = true

@[expose, reducible] def MCore (P0 : Pt) (T : NTables) : Prop :=
  wfCheck P0 = true ∧ vFixN P0 = true ∧ vRootsN P0 T = true ∧
    vCover1 P0 T (candOfN P0 T) = true ∧ T.orb1.all (entry1OK P0 T) = true

theorem NCore.toM {P0 : Pt} {Bstab : ℕ} {T : NTables} (h : NCore P0 Bstab T) : MCore P0 T :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

theorem verifyAllN_elim {P0 : Pt} {Bstab : ℕ} {T : NTables} (h : verifyAllN P0 Bstab T = true) :
    NCore P0 Bstab T ∧ T.reps.all (verifyRepN P0 (candOfN P0 T)) = true := by
  unfold verifyAllN at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, ⟨⟨⟨⟨⟨h4, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, h9⟩

theorem vRootsN_elim {P0 : Pt} {T : NTables} (h : vRootsN P0 T = true) :
    ∀ ρ ∈ T.roots, wfR P0 ρ.r = true ∧ realizes P0 ρ.w ρ.r = true ∧ P0.dotv ρ.r.f P0.x = 0 := by
  intro ρ hρ
  unfold vRootsN at h
  have := List.all_eq_true.mp h ρ hρ
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem vFixN_elim {P0 : Pt} (h : vFixN P0 = true) : ∀ g ∈ P0.gens, P0.dotv g.f P0.x = 0 := by
  intro g hg
  unfold vFixN at h
  have := List.all_eq_true.mp h g hg
  simpa using this

theorem entry0OK_elim {P0 : Pt} {T : NTables} {e : OEnt} (h : entry0OK P0 T e = true) :
    wfR P0 e.e = true ∧ ∃ rp, T.reps0[e.j]? = some rp ∧
      realizes (withExtra P0 [e.e]) (e.w ++ [P0.gens.length] ++ e.w.reverse) rp.r = true := by
  unfold entry0OK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, _⟩, h3⟩ := h
  refine ⟨h1, ?_⟩
  cases hr : T.reps0[e.j]? with
  | none => rw [hr] at h3; simp at h3
  | some rp => rw [hr] at h3; exact ⟨rp, rfl, h3⟩

theorem entry1OK_elim {P0 : Pt} {T : NTables} {e : OEnt} (h : entry1OK P0 T e = true) :
    wfR P0 e.e = true ∧ ∃ rp, T.reps[e.j]? = some rp ∧
      realizes (withExtra P0 [e.e]) (e.w ++ [P0.gens.length] ++ e.w.reverse) rp.r = true := by
  unfold entry1OK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, _⟩, h3⟩ := h
  refine ⟨h1, ?_⟩
  cases hr : T.reps[e.j]? with
  | none => rw [hr] at h3; simp at h3
  | some rp => rw [hr] at h3; exact ⟨rp, rfl, h3⟩

theorem rep0OK_elim {P0 : Pt} {Bstab : ℕ} {rp : Rep0} (h : rep0OK P0 Bstab rp = true) :
    wfR P0 rp.r = true ∧ P0.dotv rp.r.f P0.x = 0 ∧
      verifyBad (withBound (withExtra P0 [rp.r]) Bstab) rp.w = true := by
  unfold rep0OK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem s2OrbN_elim {P0 : Pt} {rp : NRep} (h : s2OrbN P0 rp = true) :
    ∀ x ∈ rp.orb2, wfR P0 x.e = true ∧ ∃ q, rp.reps2[x.j]? = some q ∧
      realizes (withExtra P0 [rp.r, x.e]) (x.w ++ [P0.gens.length + 1] ++ x.w.reverse) q.r = true := by
  intro x hx
  unfold s2OrbN at h
  have := List.all_eq_true.mp h x hx
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  obtain ⟨⟨h1, _⟩, h3⟩ := this
  refine ⟨h1, ?_⟩
  cases hr : rp.reps2[x.j]? with
  | none => rw [hr] at h3; simp at h3
  | some q => rw [hr] at h3; exact ⟨q, rfl, h3⟩

theorem s2CandN_elim {P0 : Pt} {rp : NRep} {c : Refl} (h : s2CandN P0 rp c = true) :
    (∃ ρ ∈ rp.roots, reqb c ρ.r = true) ∨
    (∃ ρ ∈ rp.roots, asymR (withExtra P0 [rp.r]) c ρ.r = true) ∨
    (∃ x ∈ rp.orb2, reqb x.e c = true) := by
  unfold s2CandN at h
  simp only [Bool.or_eq_true, List.any_eq_true, List.mem_map, asymAny] at h
  rcases h with (⟨r, ⟨ρ, hρ, rfl⟩, hr⟩ | ⟨r, ⟨ρ, hρ, rfl⟩, hr⟩) | ⟨x, hx, hxc⟩
  · exact Or.inl ⟨ρ, hρ, hr⟩
  · exact Or.inr (Or.inl ⟨ρ, hρ, hr⟩)
  · exact Or.inr (Or.inr ⟨x, hx, hxc⟩)

theorem verifyStage2N_elim {P0 : Pt} {cand : List Refl} {rp : NRep}
    (h : verifyStage2N P0 cand rp = true) :
    s2RootsN P0 rp = true ∧ s2RepsN P0 rp = true ∧ s2OrbN P0 rp = true ∧
      ∀ c ∈ movingOf P0 cand, s2CandN P0 rp c = true := by
  unfold verifyStage2N at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem verifyBad_elim {P : Pt} [Fact P.p.Prime] {w : Witness} (h : verifyBad P w = true) :
    (∃ g ∈ P.group, IsTransv g) ∨ P.bound < Nat.card P.group := by
  unfold verifyBad at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hb, hv⟩ := h
  cases w with
  | kernel v => simp [isBadW] at hb
  | weyl c => simp [isBadW] at hb
  | transv t =>
    simp only [verify, Bool.and_eq_true] at hv
    exact Or.inl (verifyT_sound (wfCheck_sound hv.1) hv.2)
  | order o =>
    simp only [verify, Bool.and_eq_true] at hv
    exact Or.inr (verifyO_sound (wfCheck_sound hv.1) hv.2)

theorem group_le_stabilizer (P : Pt) [Fact P.p.Prime] {v : P.V}
    (h : ∀ r ∈ P.gens, P.dot (P.vec r.f) v = 0) :
    P.group ≤ MulAction.stabilizer (P.V ≃ₗ[ZMod P.p] P.V) v := by
  unfold Pt.group
  rw [Subgroup.closure_le]
  rintro e ⟨r, hr, he⟩
  rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
  change e v = v
  rw [he v, h r hr, zero_smul, sub_zero]

theorem group_le_withExtra (P0 : Pt) [Fact P0.p.Prime] (extra : List Refl) :
    P0.group ≤ (withExtra P0 extra).group := by
  unfold Pt.group
  apply Subgroup.closure_mono
  rintro e ⟨r, hr, he⟩
  exact ⟨r, List.mem_append_left _ hr, he⟩

theorem commute_of_gens (P : Pt) [Fact P.p.Prime] (γ : P.V ≃ₗ[ZMod P.p] P.V)
    (h : ∀ r ∈ P.gens, ∀ e : P.V ≃ₗ[ZMod P.p] P.V,
      (∀ w, e w = w - P.dot (P.vec r.f) w • P.vec r.h) → e * γ = γ * e) :
    ∀ g ∈ P.group, g * γ = γ * g := by
  intro g hg
  have hle : P.group ≤ Subgroup.centralizer ({γ} : Set (P.V ≃ₗ[ZMod P.p] P.V)) := by
    unfold Pt.group
    rw [Subgroup.closure_le]
    rintro e ⟨r, hr, he⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact (h r hr e he).symm
  have := Subgroup.mem_centralizer_iff.mp (hle hg) γ (Set.mem_singleton γ)
  exact this.symm

structure CtxN (P0 : Pt) [Fact P0.p.Prime] (Bstab : ℕ) (T : NTables)
    (A : Subgroup (P0.V ≃ₗ[ZMod P0.p] P0.V)) : Prop where
  hp2 : P0.p ≠ 2
  frame : ∀ r ∈ P0.gens, HasRefl P0 A r
  rgen : A = Subgroup.closure {s | s ∈ A ∧ GGLinRefl s}
  nt : ∀ g ∈ A, ¬ IsTransv g
  card : Nat.card A ≤ P0.bound
  stab : Nat.card ↥(A ⊓ MulAction.stabilizer (P0.V ≃ₗ[ZMod P0.p] P0.V) (P0.vec P0.x)) ≤ Bstab
  ok : NCore P0 Bstab T

structure CtxM (P0 : Pt) [Fact P0.p.Prime] (T : NTables)
    (A : Subgroup (P0.V ≃ₗ[ZMod P0.p] P0.V)) : Prop where
  hp2 : P0.p ≠ 2
  frame : ∀ r ∈ P0.gens, HasRefl P0 A r
  nt : ∀ g ∈ A, ¬ IsTransv g
  card : Nat.card A ≤ P0.bound
  ok : MCore P0 T

variable {P0 : Pt} [Fact P0.p.Prime] {Bstab : ℕ} {T : NTables}
  {A : Subgroup (P0.V ≃ₗ[ZMod P0.p] P0.V)}

theorem CtxN.toM (C : CtxN P0 Bstab T A) : CtxM P0 T A := ⟨C.hp2, C.frame, C.nt, C.card, C.ok.toM⟩

theorem CtxM.wf0c (C : CtxM P0 T A) : wfCheck P0 = true := C.ok.1

theorem CtxM.wf0 (C : CtxM P0 T A) : P0.WF := wfCheck_sound C.wf0c

theorem CtxM.group_le (C : CtxM P0 T A) {extra : List Refl}
    (h : ∀ r ∈ extra, HasRefl P0 A r) : (withExtra P0 extra).group ≤ A := by
  apply withExtra_group_le P0 extra A
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact C.frame r hr
  · exact h r hr

theorem CtxM.roots_hasRefl (C : CtxM P0 T A) : ∀ ρ ∈ T.roots, HasRefl P0 A ρ.r := by
  intro ρ hρ
  obtain ⟨-, -, hroots, -⟩ := C.ok
  obtain ⟨_, hreal, _⟩ := vRootsN_elim hroots ρ hρ
  obtain ⟨γ, hγ, hγf⟩ := realizes_hasRefl C.wf0 hreal
  exact ⟨γ, group_le_of_gens P0 A C.frame hγ, hγf⟩

theorem CtxM.datum_cand (C : CtxM P0 T A) {c : Refl} (hc : wfR P0 c = true)
    (hf : c.f ∈ allVecsP P0.p P0.D) (hh : c.h ∈ allVecsP P0.p P0.D) (hcA : HasRefl P0 A c) :
    c ∈ candOfN P0 T := by
  unfold candOfN
  have hdot : P0.dotv c.f c.h = 2 % P0.p := by
    unfold wfR at hc
    exact beq_iff_eq.mp hc
  apply mem_candList P0 _ c hf hh hdot
  intro ρ' hρ'
  obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.mp hρ'
  cases hasym : asymR P0 c ρ.r with
  | false => rfl
  | true =>
    obtain ⟨-, -, hroots, -⟩ := C.ok
    obtain ⟨hwρ, _, _⟩ := vRootsN_elim hroots ρ hρ
    obtain ⟨g, hgA, hg⟩ := asym_transv C.hp2 hc hwρ hcA (C.roots_hasRefl ρ hρ) hasym
    exact (C.nt g hgA hg).elim

theorem CtxM.entry1_rep (C : CtxM P0 T A) {e : OEnt} (he : e ∈ T.orb1)
    (heA : HasRefl P0 A e.e) {rp : NRep} (hrp : T.reps[e.j]? = some rp) : HasRefl P0 A rp.r := by
  obtain ⟨-, -, -, -, horb1⟩ := C.ok
  obtain ⟨hwf, rp', hrp', hreal⟩ := entry1OK_elim (List.all_eq_true.mp horb1 e he)
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

theorem CtxM.entry_of_moving (C : CtxM P0 T A) {t : P0.V ≃ₗ[ZMod P0.p] P0.V} (htA : t ∈ A)
    (htr : GGLinRefl t) (htm : t (P0.vec P0.x) ≠ P0.vec P0.x) :
    ∃ e ∈ T.orb1, (∀ w, t w = w - P0.dot (P0.vec e.e.f) w • P0.vec e.e.h) ∧
      ∃ rp, T.reps[e.j]? = some rp ∧ HasRefl P0 A rp.r := by
  obtain ⟨c, hc, hcf, hch, hct⟩ := refl_datum C.hp2 htr
  have hcA : HasRefl P0 A c := ⟨t, htA, hct⟩
  have hcand := C.datum_cand hc hcf hch hcA
  have hmov : c ∈ movingOf P0 (candOfN P0 T) := by
    unfold movingOf
    rw [List.mem_filter]
    refine ⟨hcand, ?_⟩
    have hne : P0.dot (P0.vec c.f) (P0.vec P0.x) ≠ 0 := by
      intro h0
      apply htm
      rw [hct, h0, zero_smul, sub_zero]
    have : P0.dotv c.f P0.x ≠ 0 := fun h0 => hne ((dotv_eq_zero_iff P0 _ _).mp h0)
    simpa using this
  obtain ⟨-, -, -, hcov1, horb1⟩ := C.ok
  obtain ⟨e, he, hec⟩ := List.any_eq_true.mp (List.all_eq_true.mp hcov1 c hmov)
  have hee : e.e = c := reqb_eq hec
  obtain ⟨_, rp, hrp, _⟩ := entry1OK_elim (List.all_eq_true.mp horb1 e he)
  exact ⟨e, he, fun w => by rw [hee]; exact hct w, rp, hrp,
    C.entry1_rep he (by rw [hee]; exact hcA) hrp⟩

theorem CtxM.rep_of_moving (C : CtxM P0 T A) {t : P0.V ≃ₗ[ZMod P0.p] P0.V} (htA : t ∈ A)
    (htr : GGLinRefl t) (htm : t (P0.vec P0.x) ≠ P0.vec P0.x) :
    ∃ rp ∈ T.reps, HasRefl P0 A rp.r := by
  obtain ⟨e, he, -, rp, hrp, hA⟩ := C.entry_of_moving htA htr htm
  exact ⟨rp, List.mem_of_getElem? hrp, hA⟩

theorem CtxM.not_bad1 (C : CtxM P0 T A) {rp : NRep} {w : Witness}
    (hv : verify (withExtra P0 [rp.r]) w = true) (hbad : isBadW w = true)
    (hA : HasRefl P0 A rp.r) : False := by
  haveI := finite_linEquiv P0
  have hvb : verifyBad (withExtra P0 [rp.r]) w = true := by
    unfold verifyBad
    rw [Bool.and_eq_true]
    exact ⟨hbad, hv⟩
  have hleA : (withExtra P0 [rp.r]).group ≤ A := by
    apply C.group_le
    intro r hr
    rw [List.mem_singleton] at hr
    rw [hr]
    exact hA
  rcases verifyBad_elim hvb with ⟨g, hgG, hg⟩ | hbig
  · exact C.nt g (hleA hgG) hg
  · have h1 : Nat.card (withExtra P0 [rp.r]).group ≤ Nat.card A := Subgroup.card_le_of_le hleA
    have h2 := C.card
    have h3 : P0.bound < Nat.card (withExtra P0 [rp.r]).group := hbig
    omega

theorem datum_fix_dot {c : Refl} (hp2 : P0.p ≠ 2) (hc : wfR P0 c = true)
    {s : P0.V ≃ₗ[ZMod P0.p] P0.V} (hcs : ∀ w, s w = w - P0.dot (P0.vec c.f) w • P0.vec c.h)
    (hsx : s (P0.vec P0.x) = P0.vec P0.x) : P0.dotv c.f P0.x = 0 := by
  have h1 := hcs (P0.vec P0.x)
  rw [hsx] at h1
  have h2 : P0.dot (P0.vec c.f) (P0.vec P0.x) • P0.vec c.h = 0 := sub_eq_self.mp h1.symm
  have hh : P0.vec c.h ≠ 0 := by
    intro h0
    have h3 := (wfR_iff P0 c).mp hc
    rw [h0] at h3
    have h4 : P0.dot (P0.vec c.f) 0 = 0 := by
      show (pww2_dotLM P0 (P0.vec c.f)) 0 = 0
      exact map_zero _
    rw [h4] at h3
    exact CFSG.ReflExt.two_ne_zero_zmod hp2 h3.symm
  have h5 : P0.dot (P0.vec c.f) (P0.vec P0.x) = 0 := (smul_eq_zero.mp h2).resolve_right hh
  exact (dotv_eq_zero_iff P0 _ _).mpr h5

theorem CtxN.entry0_rep (C : CtxN P0 Bstab T A) {e : OEnt} (he : e ∈ T.orb0)
    (heA : HasRefl P0 A e.e) {rp : Rep0} (hrp : T.reps0[e.j]? = some rp) :
    HasRefl P0 A rp.r := by
  obtain ⟨-, -, -, -, horb0, -⟩ := C.ok
  obtain ⟨hwf, rp', hrp', hreal⟩ := entry0OK_elim (List.all_eq_true.mp horb0 e he)
  rw [hrp] at hrp'
  have hrr : rp' = rp := (Option.some.inj hrp').symm
  subst hrr
  have hw : (withExtra P0 [e.e]).WF :=
    wfCheck_sound (wfCheck_withExtra C.toM.wf0c (by
      intro r hr
      rw [List.mem_singleton] at hr
      rw [hr]
      exact hwf))
  obtain ⟨γ, hγ, hγf⟩ := realizes_hasRefl hw hreal
  have hle : (withExtra P0 [e.e]).group ≤ A := by
    apply C.toM.group_le
    intro r hr
    rw [List.mem_singleton] at hr
    rw [hr]
    exact heA
  exact ⟨γ, hle hγ, hγf⟩

theorem CtxN.not_bad0 (C : CtxN P0 Bstab T A) {rp : Rep0} (hrp : rp ∈ T.reps0)
    (hA : HasRefl P0 A rp.r) : False := by
  obtain ⟨-, hfixN, -, -, -, hreps0, -⟩ := C.ok
  obtain ⟨hwr, hdot, hv⟩ := rep0OK_elim (List.all_eq_true.mp hreps0 rp hrp)
  haveI : Fact (withBound (withExtra P0 [rp.r]) Bstab).p.Prime := ‹Fact P0.p.Prime›
  haveI := finite_linEquiv P0
  have hleA : (withExtra P0 [rp.r]).group ≤ A := by
    apply C.toM.group_le
    intro r hr
    rw [List.mem_singleton] at hr
    rw [hr]
    exact hA
  have hleS : (withExtra P0 [rp.r]).group ≤
      MulAction.stabilizer (P0.V ≃ₗ[ZMod P0.p] P0.V) (P0.vec P0.x) := by
    apply group_le_stabilizer
    intro r hr
    simp only [withExtra, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | hr
    · exact (dotv_eq_zero_iff P0 _ _).mp (vFixN_elim hfixN r hr)
    · rw [hr]
      exact (dotv_eq_zero_iff P0 _ _).mp hdot
  rcases verifyBad_elim hv with ⟨g, hgG, hg⟩ | hbig
  · exact C.nt g (hleA hgG) hg
  · have h1 : Nat.card (withExtra P0 [rp.r]).group ≤
        Nat.card ↥(A ⊓ MulAction.stabilizer (P0.V ≃ₗ[ZMod P0.p] P0.V) (P0.vec P0.x)) :=
      Subgroup.card_le_of_le (le_inf hleA hleS)
    have h2 := C.stab
    have h3 : Bstab < Nat.card (withExtra P0 [rp.r]).group := hbig
    omega

theorem CtxN.fixing_class (C : CtxN P0 Bstab T A) {s : P0.V ≃ₗ[ZMod P0.p] P0.V} (hsA : s ∈ A)
    (hsr : GGLinRefl s) (hsx : s (P0.vec P0.x) = P0.vec P0.x) : s ∈ P0.group := by
  obtain ⟨c, hc, hcf, hch, hcs⟩ := refl_datum C.hp2 hsr
  have hcA : HasRefl P0 A c := ⟨s, hsA, hcs⟩
  have hcand := C.toM.datum_cand hc hcf hch hcA
  have hdotv : P0.dotv c.f P0.x = 0 := datum_fix_dot C.hp2 hc hcs hsx
  obtain ⟨-, -, hroots, hcov0, horb0, -⟩ := C.ok
  have hmem : c ∈ (candOfN P0 T).filter (fun c => P0.dotv c.f P0.x == 0) := by
    rw [List.mem_filter]
    exact ⟨hcand, by simpa using hdotv⟩
  have hc0 := List.all_eq_true.mp hcov0 c hmem
  simp only [Bool.or_eq_true, List.any_eq_true] at hc0
  rcases hc0 with ⟨ρ, hρ, hρc⟩ | ⟨e, he, hec⟩
  · obtain ⟨-, hreal, -⟩ := vRootsN_elim hroots ρ hρ
    obtain ⟨γ, hγ, hγf⟩ := realizes_hasRefl C.toM.wf0 hreal
    have hcρ : ρ.r = c := reqb_eq hρc
    have hsγ : s = γ := by
      apply LinearEquiv.ext
      intro w
      rw [hcs w, hγf w, ← hcρ]
    rw [hsγ]
    exact hγ
  · have hee : e.e = c := reqb_eq hec
    obtain ⟨-, rp, hrp, -⟩ := entry0OK_elim (List.all_eq_true.mp horb0 e he)
    exact (C.not_bad0 (List.mem_of_getElem? hrp) (C.entry0_rep he (by rw [hee]; exact hcA) hrp)).elim

theorem vec_negR (P : Pt) [Fact P.p.Prime] (r : Refl) :
    P.vec (negR P r).f = - P.vec r.f ∧ P.vec (negR P r).h = - P.vec r.h := by
  have hp : 0 < P.p := (Fact.out (p := P.p.Prime)).pos
  have key : ∀ a : ℕ, ((((P.p - a % P.p) % P.p : ℕ)) : ZMod P.p) = - (a : ZMod P.p) := by
    intro a
    rw [ZMod.natCast_mod, Nat.cast_sub (Nat.mod_lt a hp).le, ZMod.natCast_self, ZMod.natCast_mod]
    ring
  constructor
  · funext j
    show ((((negR P r).f.getD j.val 0 : ℕ)) : ZMod P.p) = - ((r.f.getD j.val 0 : ℕ) : ZMod P.p)
    unfold negR
    rw [pww2_getD_range_map P.D _ j]
    exact key _
  · funext j
    show ((((negR P r).h.getD j.val 0 : ℕ)) : ZMod P.p) = - ((r.h.getD j.val 0 : ℕ) : ZMod P.p)
    unfold negR
    rw [pww2_getD_range_map P.D _ j]
    exact key _

theorem CtxN.stage2 (C : CtxN P0 Bstab T A) {rp : NRep} (hwr : wfR P0 rp.r = true)
    (hS2 : verifyStage2N P0 (candOfN P0 T) rp = true) (hA : HasRefl P0 A rp.r)
    {s : P0.V ≃ₗ[ZMod P0.p] P0.V} (hsA : s ∈ A) (hsr : GGLinRefl s) :
    s ∈ (withExtra P0 [rp.r]).group ∧
      (s (P0.vec P0.x) ≠ P0.vec P0.x → ∃ ρ ∈ rp.roots,
        ∀ w, s w = w - P0.dot (P0.vec ρ.r.f) w • P0.vec ρ.r.h) := by
  obtain ⟨hs2roots, hs2reps, hs2orb, hs2cand⟩ := verifyStage2N_elim hS2
  have hleJ : (withExtra P0 [rp.r]).group ≤ A := by
    apply C.toM.group_le
    intro r hr
    rw [List.mem_singleton] at hr
    rw [hr]
    exact hA
  by_cases hsx : s (P0.vec P0.x) = P0.vec P0.x
  · exact ⟨group_le_withExtra P0 [rp.r] (C.fixing_class hsA hsr hsx), fun h => absurd hsx h⟩
  · have hwj : (withExtra P0 [rp.r]).WF :=
      wfCheck_sound (wfCheck_withExtra C.toM.wf0c (by
        intro r hr
        rw [List.mem_singleton] at hr
        rw [hr]
        exact hwr))
    obtain ⟨c, hc, hcf, hch, hcs⟩ := refl_datum C.hp2 hsr
    have hcA : HasRefl P0 A c := ⟨s, hsA, hcs⟩
    have hcand := C.toM.datum_cand hc hcf hch hcA
    have hmov : c ∈ movingOf P0 (candOfN P0 T) := by
      unfold movingOf
      rw [List.mem_filter]
      refine ⟨hcand, ?_⟩
      have hne : P0.dot (P0.vec c.f) (P0.vec P0.x) ≠ 0 := by
        intro h0
        apply hsx
        rw [hcs, h0, zero_smul, sub_zero]
      have : P0.dotv c.f P0.x ≠ 0 := fun h0 => hne ((dotv_eq_zero_iff P0 _ _).mp h0)
      simpa using this
    rcases s2CandN_elim (hs2cand c hmov) with ⟨ρ, hρ, hρc⟩ | ⟨ρ, hρ, hρc⟩ | ⟨x, hx, hxc⟩
    ·
      have hreal := List.all_eq_true.mp hs2roots ρ hρ
      simp only [Bool.and_eq_true] at hreal
      obtain ⟨γ, hγ, hγf⟩ := realizes_hasRefl hwj hreal.2
      have hcρ : c = ρ.r := reqb_eq hρc
      have hsγ : s = γ := by
        apply LinearEquiv.ext
        intro w
        rw [hcs w, hγf w, hcρ]
        rfl
      refine ⟨hsγ ▸ hγ, fun _ => ⟨ρ, hρ, fun w => ?_⟩⟩
      rw [hcs w, hcρ]
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
      haveI := finite_linEquiv P0
      obtain ⟨hwx, q, hq, hreal⟩ := s2OrbN_elim hs2orb x hx
      have hxe : x.e = c := reqb_eq hxc
      have hqmem : q ∈ rp.reps2 := List.mem_of_getElem? hq
      have hq2 := List.all_eq_true.mp hs2reps q hqmem
      simp only [Bool.and_eq_true] at hq2
      obtain ⟨hwq, hvq⟩ := hq2
      have hwx' : (withExtra P0 [rp.r, x.e]).WF :=
        wfCheck_sound (wfCheck_withExtra C.toM.wf0c (by
          intro r hr
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hwr
          · exact hwx))
      obtain ⟨γ, hγ, hγf⟩ := realizes_hasRefl hwx' hreal
      have hleX : (withExtra P0 [rp.r, x.e]).group ≤ A := by
        apply C.toM.group_le
        intro r hr
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hA
        · rw [hxe]; exact hcA
      have hqA : HasRefl P0 A q.r := ⟨γ, hleX hγ, hγf⟩
      have hleQ : (withExtra P0 [rp.r, q.r]).group ≤ A := by
        apply C.toM.group_le
        intro r hr
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hA
        · exact hqA
      haveI : Fact (withExtra P0 [rp.r, q.r]).p.Prime := ‹Fact P0.p.Prime›
      rcases verifyBad_elim hvq with ⟨g, hgG, hg⟩ | hbig
      · exact C.nt g (hleQ hgG) hg
      · have h1 : Nat.card (withExtra P0 [rp.r, q.r]).group ≤ Nat.card A :=
          Subgroup.card_le_of_le hleQ
        have h2 := C.card
        have h3 : P0.bound < Nat.card (withExtra P0 [rp.r, q.r]).group := hbig
        omega

theorem CtxN.classification
    (C : CtxN P0 Bstab T A) (hreps : T.reps.all (verifyRepN P0 (candOfN P0 T)) = true)
    {t : P0.V ≃ₗ[ZMod P0.p] P0.V} (htA : t ∈ A) (htr : GGLinRefl t)
    (htm : t (P0.vec P0.x) ≠ P0.vec P0.x) :
    ZS.LinWeyl P0.p A ∨
      ∃ t' ∈ A, GGLinRefl t' ∧ t' (P0.vec P0.x) ≠ P0.vec P0.x ∧ (∀ g ∈ A, g * t' = t' * g) ∧
        ∀ s ∈ A, GGLinRefl s → s (P0.vec P0.x) ≠ P0.vec P0.x → s = t' := by
  obtain ⟨rp, hrp, hA⟩ := C.toM.rep_of_moving htA htr htm
  have hv := List.all_eq_true.mp hreps rp hrp
  unfold verifyRepN at hv
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hv
  obtain ⟨⟨hwr, hmv⟩, hk⟩ := hv
  have hleG : (withExtra P0 [rp.r]).group ≤ A := by
    apply C.toM.group_le
    intro r hr
    rw [List.mem_singleton] at hr
    rw [hr]
    exact hA
  cases hkind : rp.kind with
  | w w =>
    simp only [hkind] at hk
    cases w with
    | kernel v => simp at hk
    | transv t0 =>
      dsimp only at hk
      exact (C.toM.not_bad1 hk rfl hA).elim
    | order o =>
      dsimp only at hk
      exact (C.toM.not_bad1 hk rfl hA).elim
    | weyl cw =>
      dsimp only at hk
      simp only [Bool.and_eq_true] at hk
      obtain ⟨hvw, hS2⟩ := hk
      left
      have hAeq : A = (withExtra P0 [rp.r]).group := by
        apply le_antisymm
        · conv_lhs => rw [C.rgen]
          rw [Subgroup.closure_le]
          rintro s ⟨hsA, hsr⟩
          exact (C.stage2 hwr hS2 hA hsA hsr).1
        · exact hleG
      simp only [verify, Bool.and_eq_true] at hvw
      have hW : ZS.LinWeyl P0.p (withExtra P0 [rp.r]).group :=
        verifyW_sound (wfCheck_sound hvw.1) hvw.2
      rw [hAeq]
      exact hW
  | cent =>
    simp only [hkind, Bool.and_eq_true] at hk
    obtain ⟨⟨hcent, hcr⟩, hS2⟩ := hk
    right
    have hAeq : A = (withExtra P0 [rp.r]).group := by
      apply le_antisymm
      · conv_lhs => rw [C.rgen]
        rw [Subgroup.closure_le]
        rintro s ⟨hsA, hsr⟩
        exact (C.stage2 hwr hS2 hA hsA hsr).1
      · exact hleG
    obtain ⟨γ, hγA, hγ⟩ := hA
    have hγv : ∀ u, γ (P0.vec u) = P0.vec (P0.applyRefl rp.r u) := fun u => by
      rw [Pt.vec_applyRefl, hγ]
    have huniq : ∀ s ∈ A, GGLinRefl s → s (P0.vec P0.x) ≠ P0.vec P0.x → s = γ := by
      intro s hsA hsr hsm
      obtain ⟨-, hex⟩ := C.stage2 hwr hS2 ⟨γ, hγA, hγ⟩ hsA hsr
      obtain ⟨ρ, hρ, hρs⟩ := hex hsm
      have hcr' : rp.roots.all (fun ρ => reqb ρ.r rp.r || reqb ρ.r (negR P0 rp.r) ||
          P0.dotv ρ.r.f P0.x == 0) = true := hcr
      have hρr := List.all_eq_true.mp hcr' ρ hρ
      simp only [Bool.or_eq_true, beq_iff_eq] at hρr
      rcases hρr with (h1 | h2) | h3
      · have h1' : ρ.r = rp.r := reqb_eq h1
        apply LinearEquiv.ext
        intro w
        rw [hρs w, hγ w, h1']
      · have h2' : ρ.r = negR P0 rp.r := reqb_eq h2
        apply LinearEquiv.ext
        intro w
        obtain ⟨hf, hh⟩ := vec_negR P0 rp.r
        rw [hρs w, hγ w, h2', hf, hh]
        have hd : P0.dot (-P0.vec rp.r.f) w = - P0.dot (P0.vec rp.r.f) w := by
          show (pww2_dotLM P0 (-P0.vec rp.r.f)) w = - (pww2_dotLM P0 (P0.vec rp.r.f)) w
          simp [pww2_dotLM, Pt.dot, Finset.sum_neg_distrib]
        rw [hd, neg_smul, smul_neg, neg_neg]
      · exfalso
        apply hsm
        have hz : P0.dot (P0.vec ρ.r.f) (P0.vec P0.x) = 0 := (dotv_eq_zero_iff P0 _ _).mp h3
        rw [hρs, hz, zero_smul, sub_zero]
    have htγ : t = γ := huniq t htA htr htm
    have hcentγ : ∀ g ∈ A, g * γ = γ * g := by
      rw [hAeq]
      apply commute_of_gens (withExtra P0 [rp.r]) γ
      intro r hr e he
      simp only [withExtra, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | hr
      · have hev : ∀ u, e (P0.vec u) = P0.vec (P0.applyRefl r u) := fun u => by
          rw [Pt.vec_applyRefl]
          exact he (P0.vec u)
        apply pww2_le_ext_unit P0
        intro j
        show e (γ (P0.vec (P0.unit j))) = γ (e (P0.vec (P0.unit j)))
        rw [hγv, hev, hev, hγv]
        have hcent' : P0.gens.all (fun g => (List.range P0.D).all fun j =>
            P0.vecEq (P0.applyRefl g (P0.applyRefl rp.r (P0.unit j)))
              (P0.applyRefl rp.r (P0.applyRefl g (P0.unit j)))) = true := hcent
        have hcj := List.all_eq_true.mp (List.all_eq_true.mp hcent' r hr) j
          (List.mem_range.mpr j.isLt)
        exact pww2_vec_of_vecEq P0 _ _ hcj
      · have : e = γ := by
          apply LinearEquiv.ext
          intro w
          subst hr
          exact (he w).trans (hγ w).symm
        rw [this]
    refine ⟨t, htA, htr, htm, ?_, ?_⟩
    · intro g hg
      rw [htγ]
      exact hcentγ g hg
    · intro s hsA hsr hsm
      rw [htγ]
      exact huniq s hsA hsr hsm

theorem ctxM_of_conj {P0 : Pt} [Fact P0.p.Prime] {T : NTables} (hp2 : P0.p ≠ 2)
    (hok : MCore P0 T) {V : Type} [AddCommGroup V] [Module (ZMod P0.p) V]
    (ε : V ≃ₗ[ZMod P0.p] P0.V) (A : Subgroup (V ≃ₗ[ZMod P0.p] V))
    (hfr : ∀ r ∈ P0.gens, ∃ g ∈ A,
      ∀ w : P0.V, ε (g (ε.symm w)) = w - P0.dot (P0.vec r.f) w • P0.vec r.h)
    (hnt : ∀ g ∈ A, ¬ IsTransv g) (hcard : Nat.card A ≤ P0.bound) :
    CtxM P0 T (A.map (rxConj ε).toMonoidHom) := by
  refine ⟨hp2, ?_, ?_, ?_, hok⟩
  · intro r hr
    obtain ⟨g, hgA, hg⟩ := hfr r hr
    exact ⟨rxConj ε g, Subgroup.mem_map.mpr ⟨g, hgA, rfl⟩, fun w => by
      rw [rxConj_apply]
      exact hg w⟩
  · intro g' hg'
    obtain ⟨g, hgA, rfl⟩ := Subgroup.mem_map.mp hg'
    intro hT
    exact hnt g hgA ((rxConj_isTransv ε g).mp hT)
  · calc Nat.card ↥(A.map (rxConj ε).toMonoidHom) = Nat.card ↥A :=
          (Nat.card_congr (MulEquiv.subgroupMap (rxConj ε) A).toEquiv).symm
      _ ≤ P0.bound := hcard

theorem ctxN_of_conj {P0 : Pt} [Fact P0.p.Prime] {Bstab : ℕ} {T : NTables} (hp2 : P0.p ≠ 2)
    (hok : NCore P0 Bstab T) {V : Type} [AddCommGroup V] [Module (ZMod P0.p) V]
    (ε : V ≃ₗ[ZMod P0.p] P0.V) (x : V) (hεx : ε x = P0.vec P0.x)
    (A : Subgroup (V ≃ₗ[ZMod P0.p] V))
    (hfr : ∀ r ∈ P0.gens, ∃ g ∈ A,
      ∀ w : P0.V, ε (g (ε.symm w)) = w - P0.dot (P0.vec r.f) w • P0.vec r.h)
    (hrg : A = Subgroup.closure {s | s ∈ A ∧ GGLinRefl s})
    (hnt : ∀ g ∈ A, ¬ IsTransv g) (hcard : Nat.card A ≤ P0.bound)
    (hstab : Nat.card ↥(A ⊓ MulAction.stabilizer (V ≃ₗ[ZMod P0.p] V) x) ≤ Bstab) :
    CtxN P0 Bstab T (A.map (rxConj ε).toMonoidHom) := by
  have hM := ctxM_of_conj hp2 hok.toM ε A hfr hnt hcard
  refine ⟨hM.hp2, hM.frame, ?_, hM.nt, hM.card, ?_, hok⟩
  ·
    have himg : {s | s ∈ A.map (rxConj ε).toMonoidHom ∧ GGLinRefl s} =
        (rxConj ε).toMonoidHom '' {s | s ∈ A ∧ GGLinRefl s} := by
      ext s
      constructor
      · rintro ⟨hs, hsr⟩
        obtain ⟨g, hgA, rfl⟩ := Subgroup.mem_map.mp hs
        exact ⟨g, ⟨hgA, (rxConj_isRefl ε g).mp hsr⟩, rfl⟩
      · rintro ⟨g, ⟨hgA, hgr⟩, rfl⟩
        exact ⟨Subgroup.mem_map.mpr ⟨g, hgA, rfl⟩, (rxConj_isRefl ε g).mpr hgr⟩
    rw [himg, ← MonoidHom.map_closure, ← hrg]
  ·
    have hmap : (A ⊓ MulAction.stabilizer (V ≃ₗ[ZMod P0.p] V) x).map (rxConj ε).toMonoidHom =
        A.map (rxConj ε).toMonoidHom ⊓
          MulAction.stabilizer (P0.V ≃ₗ[ZMod P0.p] P0.V) (P0.vec P0.x) := by
      ext g
      simp only [Subgroup.mem_map, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
      constructor
      · rintro ⟨a, ⟨haA, hax⟩, rfl⟩
        refine ⟨⟨a, haA, rfl⟩, ?_⟩
        change rxConj ε a (P0.vec P0.x) = P0.vec P0.x
        rw [← hεx, rxConj_apply, LinearEquiv.symm_apply_apply]
        have hax' : a x = x := hax
        rw [hax']
      · rintro ⟨⟨a, haA, rfl⟩, hs⟩
        refine ⟨a, ⟨haA, ?_⟩, rfl⟩
        have hs' : rxConj ε a (P0.vec P0.x) = P0.vec P0.x := hs
        rw [← hεx, rxConj_apply, LinearEquiv.symm_apply_apply] at hs'
        exact ε.injective hs'
    calc Nat.card ↥(A.map (rxConj ε).toMonoidHom ⊓
          MulAction.stabilizer (P0.V ≃ₗ[ZMod P0.p] P0.V) (P0.vec P0.x))
        = Nat.card ↥((A ⊓ MulAction.stabilizer (V ≃ₗ[ZMod P0.p] V) x).map
            (rxConj ε).toMonoidHom) := by rw [hmap]
      _ = Nat.card ↥(A ⊓ MulAction.stabilizer (V ≃ₗ[ZMod P0.p] V) x) :=
          (Nat.card_congr (MulEquiv.subgroupMap (rxConj ε) _).toEquiv).symm
      _ ≤ Bstab := hstab

end CFSG.NineAll

end
