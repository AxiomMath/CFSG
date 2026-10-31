
module

public import CFSG.Sporadic.J4.QT2LocX0MainBase
public import CFSG.Sporadic.J4.QT2LocScanNative
public import CFSG.Sporadic.J4.QT2LocFixMainBase
public import CFSG.Sporadic.J4.QT2LocX0KNative

@[expose] public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT Matrix
open scoped Classical

set_option maxRecDepth 100000

theorem scanBs_eq : scanBs = bs0 := bs0_def.symm

theorem enum_facts {nl m : ℕ} {R : Array (Array V2)} {O : MOrb} {w : Array V2}
    (hok : oOrbOK (fun M g => mulRows M (R[g]!)) nl w O m = true) :
    O.mats.size = m ∧ 0 < m ∧ O.mats[0]! = w ∧
      ∀ q < m, oOrbAt (fun M g => mulRows M (R[g]!)) nl O q = true := by
  unfold oOrbOK at hok
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hok
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hok
  exact ⟨h1, h4, eqRows_iff.1 h5, h6⟩

theorem enum_closure_sub {nl m : ℕ} {G : ℕ → J} {R : Array (Array V2)}
    (hR : ∀ i < nl, Mx (G i) = rowsMatrix (R[i]!)) {O : MOrb}
    (hok : oOrbOK (fun M g => mulRows M (R[g]!)) nl idRows O m = true) :
    ∀ g ∈ Subgroup.closure (G '' {i | i < nl}), ∃ q < m, Mx g = rowsMatrix (O.mats[q]!) := by
  obtain ⟨hsz, hm0, hroot, hat⟩ := enum_facts hok
  have hstep : ∀ g : J, (∃ q < m, Mx g = rowsMatrix (O.mats[q]!)) → ∀ i < nl,
      ∃ q < m, Mx (g * G i) = rowsMatrix (O.mats[q]!) := by
    rintro g ⟨q, hq, hgq⟩ i hi
    obtain ⟨-, -, hstep, -⟩ := oOrbAt_facts (hat q hq)
    obtain ⟨e, he0, hesz, hee⟩ := hstep i hi
    refine ⟨e - 1, by omega, ?_⟩
    rw [hee, map_mul, hgq, hR i hi]
    exact (rowsMatrix_mulRows _ _).symm
  have hone : ∃ q < m, Mx (1 : J) = rowsMatrix (O.mats[q]!) :=
    ⟨0, hm0, by rw [hroot, map_one, rowsMatrix_idRows]⟩
  have hmul : ∀ k ∈ Submonoid.closure (G '' {i | i < nl}), ∀ g : J,
      (∃ q < m, Mx g = rowsMatrix (O.mats[q]!)) →
        ∃ q < m, Mx (g * k) = rowsMatrix (O.mats[q]!) := by
    intro k hk
    induction hk using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      exact fun g hg => hstep g hg i hi
    | one => intro g hg; simpa using hg
    | mul x y _ _ hx hy => intro g hg; rw [← mul_assoc]; exact hy _ (hx g hg)
  intro g hg
  have hg' : g ∈ (Subgroup.closure (G '' {i | i < nl})).toSubmonoid := hg
  rw [Subgroup.closure_toSubmonoid_of_finite] at hg'
  have := hmul g hg' 1 hone
  rwa [one_mul] at this

theorem enum_of_lt {nl m : ℕ} {G : ℕ → J} {R : Array (Array V2)}
    (hR : ∀ i < nl, Mx (G i) = rowsMatrix (R[i]!)) {O : MOrb}
    (hok : oOrbOK (fun M g => mulRows M (R[g]!)) nl idRows O m = true) :
    ∀ q < m, ∃ g ∈ Subgroup.closure (G '' {i | i < nl}), Mx g = rowsMatrix (O.mats[q]!) := by
  obtain ⟨hsz, hm0, hroot, hat⟩ := enum_facts hok
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hq
    obtain ⟨-, -, -, hpar⟩ := oOrbAt_facts (hat q hq)
    rcases hpar with h0 | ⟨hp, hl, hst⟩
    · refine ⟨1, Subgroup.one_mem _, ?_⟩
      subst h0
      rw [hroot, map_one, rowsMatrix_idRows]
    · obtain ⟨g, hg, hgM⟩ := ih _ hp (lt_trans hp hq)
      refine ⟨g * G (O.lab[q]!), Subgroup.mul_mem _ hg (Subgroup.subset_closure ⟨_, hl, rfl⟩), ?_⟩
      rw [← hst, map_mul, hgM, hR _ hl]
      exact (rowsMatrix_mulRows _ _).symm

theorem enum_inj {nl m : ℕ} {R : Array (Array V2)} {O : MOrb}
    (hok : oOrbOK (fun M g => mulRows M (R[g]!)) nl idRows O m = true)
    {q q' : ℕ} (hq : q < m) (hq' : q' < m)
    (h : rowsMatrix (O.mats[q]!) = rowsMatrix (O.mats[q']!)) : q = q' := by
  obtain ⟨-, -, -, hat⟩ := enum_facts hok
  obtain ⟨hw, hf, -⟩ := oOrbAt_facts (hat q hq)
  obtain ⟨hw', hf', -⟩ := oOrbAt_facts (hat q' hq')
  have := eq_of_rowsMatrix_eq hw hw' h
  rw [this] at hf
  omega

theorem card_enum {nl m : ℕ} {G : ℕ → J} {R : Array (Array V2)}
    (hR : ∀ i < nl, Mx (G i) = rowsMatrix (R[i]!)) {O : MOrb}
    (hok : oOrbOK (fun M g => mulRows M (R[g]!)) nl idRows O m = true) :
    Nat.card (Subgroup.closure (G '' {i | i < nl})) = m := by
  let f : Fin m → Subgroup.closure (G '' {i | i < nl}) := fun q =>
    ⟨(enum_of_lt hR hok q q.2).choose, (enum_of_lt hR hok q q.2).choose_spec.1⟩
  have hspec : ∀ q : Fin m, Mx (f q : J) = rowsMatrix (O.mats[q.val]!) := fun q =>
    (enum_of_lt hR hok q q.2).choose_spec.2
  have hbij : Function.Bijective f := by
    constructor
    · intro q q' h
      have h1 : Mx (f q : J) = Mx (f q' : J) := by rw [h]
      rw [hspec, hspec] at h1
      exact Fin.ext (enum_inj hok q.2 q'.2 h1)
    · intro g
      obtain ⟨q, hq, hgq⟩ := enum_closure_sub hR hok g g.2
      refine ⟨⟨q, hq⟩, ?_⟩
      apply Subtype.ext
      apply Mx_injective
      rw [hspec]
      exact hgq.symm
  rw [← Nat.card_congr (Equiv.ofBijective f hbij)]
  simp

noncomputable def kGen (i : ℕ) : J :=
  if i < 6 then QT2A.el5 (kWords.getD i []) else (QT2A.el5 (kWords.getD (i - 6) []))⁻¹

noncomputable def KSub : Subgroup J := Subgroup.closure (kGen '' {i | i < 12})

noncomputable def q1Row : Row := toRow x0Q1.toVec

noncomputable def Estab (p : Row) : Subgroup J := Eg uJ 11 ⊓ MulAction.stabilizer J p

theorem Estab_smul (hM : MatFacts) {h : J} (hh : h ∈ Hj) (p : Row) :
    Estab (h • p) = conjSub h (Estab p) := by
  ext x
  rw [mem_conjSub]
  unfold Estab
  simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  constructor
  · rintro ⟨hxE, hxp⟩
    refine ⟨by simpa using Hj_normalizes_Eg hM h⁻¹ (Hj.inv_mem hh) x hxE, ?_⟩
    rw [mul_smul, mul_smul, hxp, inv_smul_smul]
  · rintro ⟨hxE, hxp⟩
    refine ⟨?_, ?_⟩
    · have := Hj_normalizes_Eg hM h hh _ hxE
      simpa [mul_assoc] using this
    · have e : x * h = h * (h⁻¹ * x * h) := by group
      calc x • (h • p) = (x * h) • p := (mul_smul _ _ _).symm
        _ = (h * (h⁻¹ * x * h)) • p := by rw [e]
        _ = h • ((h⁻¹ * x * h) • p) := mul_smul _ _ _
        _ = h • p := by rw [hxp]

theorem card_Estab_smul
    (hM : MatFacts) {h : J} (hh : h ∈ Hj) (p : Row) :
    Nat.card (Estab (h • p)) = Nat.card (Estab p) := by
  rw [Estab_smul hM hh]
  exact card_conjSub h _

theorem toVec_eq_of_not_differs {a b : V2} (h : differs a b = false) : a.toVec = b.toVec := by
  by_contra hne
  have := differs_toVec (a := a) (b := b)
  unfold differs at h
  simp only [List.any_eq_false, List.mem_range, bne_iff_ne, ne_eq, not_not] at h
  apply hne
  funext j
  rw [V2.toVec_apply, V2.toVec_apply, h j.val j.isLt]

theorem eta_mem_Estab_iff (hM : MatFacts) {c : ℕ} (v : V2) :
    eta uJ 11 c ∈ Estab (toRow v.toVec) ↔
      differs (frApply (frTable (etaRows (uTab (locMats ()) (locInvs ())) 11 c)) v) v = false := by
  unfold Estab
  rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, eta_smul_toRow hM c v]
  constructor
  · rintro ⟨-, h⟩
    by_contra hd
    rw [Bool.not_eq_false] at hd
    exact differs_toVec hd h
  · intro h
    exact ⟨eta_mem_Eg 11 le_rfl c, by rw [toVec_eq_of_not_differs h]⟩

theorem card_Estab_toRow (hM : MatFacts) (v : V2) :
    Nat.card ↥(Estab (toRow v.toVec)) =
      (eFixMasks (uTab (locMats ()) (locInvs ())) v).length := by
  have hset : ((Estab (toRow v.toVec) : Subgroup J) : Set J) =
      ↑(((eFixMasks (uTab (locMats ()) (locInvs ())) v).map (eta uJ 11)).toFinset) := by
    ext x
    simp only [SetLike.mem_coe, List.mem_toFinset, List.mem_map]
    constructor
    · intro hx
      obtain ⟨c, hc, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 (Subgroup.mem_inf.1 hx).1
      refine ⟨c, ?_, rfl⟩
      rw [eFixMasks, List.mem_filter, List.mem_range, Bool.not_eq_true']
      exact ⟨hc, (eta_mem_Estab_iff hM v).1 hx⟩
    · rintro ⟨c, hc, rfl⟩
      rw [eFixMasks, List.mem_filter, List.mem_range, Bool.not_eq_true'] at hc
      exact (eta_mem_Estab_iff hM v).2 hc.2
  have hnd : (eFixMasks (uTab (locMats ()) (locInvs ())) v).Nodup :=
    (List.nodup_range).filter _
  have hinj : ((eFixMasks (uTab (locMats ()) (locInvs ())) v).map (eta uJ 11)).Nodup := by
    rw [List.nodup_map_iff_inj_on hnd]
    intro c hc d hd e
    have hc' := (List.mem_filter.1 hc).1
    have hd' := (List.mem_filter.1 hd).1
    exact eta_inj hM c (by simpa using List.mem_range.1 hc') d (by simpa using List.mem_range.1 hd')
      e
  have : Nat.card ↥(Estab (toRow v.toVec)) =
      (↑(((eFixMasks (uTab (locMats ()) (locInvs ())) v).map (eta uJ 11)).toFinset) :
        Set J).ncard := by
    rw [← hset]
    exact Nat.card_coe_set_eq _
  rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hinj, List.length_map]

theorem smul_rep_form' (hM : MatFacts) {ℓ : ℕ} {h h' : J} (hh' : h' ∈ Hj) :
    (h * (pathElt (repPaths.getD ℓ []))⁻¹ * h') • w₀ = h • rep ℓ := by
  rw [mul_smul, mul_smul, smul_root_of_mem_Hj hM hh', rep_eq]
  rfl

noncomputable def CxH : Subgroup J :=
  Subgroup.centralizer ({fiveElt} : Set J) ⊓ Hj

theorem fiveElt_smul_pts
    (hM : MatFacts) {p : Row} (hp : p ∈ x0PtSet) : fiveElt • p = p := by
  obtain ⟨g, hg, rfl⟩ := exists_of_mem_pts hM hp
  have hc : fiveElt * g = g * fiveElt :=
    (Subgroup.mem_centralizer_singleton_iff.1 (X0Sub_le_centralizer hM hg)).symm
  rw [← mul_smul, hc, mul_smul, smul_root_of_mem_Hj hM fiveElt_mem_Hj]

theorem w₀_mem_pts (hM : MatFacts) : w₀ ∈ x0PtSet := by
  have := smul_mem_pts hM (X0Sub.one_mem : (1 : J) ∈ X0Sub)
  rwa [one_smul] at this

theorem card_X0Sub_inf_Hj
    (hF : J4Facts) : Nat.card ↥(X0Sub ⊓ Hj) = 480 := by
  have hM := hF.mat
  have h := card_X0Sub_stabilizer hM
  have hsub : (X0Sub ⊓ Hj).subgroupOf X0Sub = MulAction.stabilizer ↥X0Sub w₀ := by
    ext ⟨g, hg⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
    constructor
    · rintro ⟨-, hH⟩
      exact smul_root_of_mem_Hj hM hH
    · intro hfix
      exact ⟨hg, mem_Hj_of_smul_root hF hfix⟩
  rw [← hsub] at h
  rw [← h]
  exact (Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe (inf_le_left : X0Sub ⊓ Hj ≤ X0Sub)).toEquiv).symm

theorem X0Sub_inf_Hj_le_CxH (hM : MatFacts) : X0Sub ⊓ Hj ≤ CxH :=
  fun _ hg => ⟨X0Sub_le_centralizer hM hg.1, hg.2⟩

end CFSG.Sporadic.J4.QT2
