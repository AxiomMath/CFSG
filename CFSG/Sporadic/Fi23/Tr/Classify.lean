module

public import CFSG.Sporadic.Fi23.Tr.Points
public import CFSG.Sporadic.Fi23.Tr.Local
public import CFSG.Sporadic.Fi23.Tr.Det
public import CFSG.Sporadic.Fi23.Tr.Conj
public import CFSG.Sporadic.Fi23.Graph
public import CFSG.Fischer.Polar.Facts

public section

namespace CFSG.Sporadic.Fi23

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.F3.Native Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem conj_conj_image (g : J) (U : Set J) :
    (fun z => g * z * g⁻¹) '' ((fun z => g⁻¹ * z * g⁻¹⁻¹) '' U) = U := by
  rw [Set.image_image]
  have : ∀ z, g * (g⁻¹ * z * g⁻¹⁻¹) * g⁻¹ = z := fun z => by group
  simp only [this, Set.image_id']

theorem conj_image_image
    (g₁ g₂ : J) (X : Set J) :
    (fun z => g₁ * z * g₁⁻¹) '' ((fun z => g₂ * z * g₂⁻¹) '' X) =
      (fun z => (g₁ * g₂) * z * (g₁ * g₂)⁻¹) '' X := by
  ext y
  simp only [Set.mem_image, exists_exists_and_eq_and]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, by group⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, by group⟩

theorem conj_one_image
    (X : Set J) : (fun z => (1 : J) * z * (1 : J)⁻¹) '' X = X := by
  simp

theorem conj_image_inter_localClass (g : J) (U : Set J) (e : J) :
    (fun z => g * z * g⁻¹) '' (U ∩ LocalClass D23 e) =
      (fun z => g * z * g⁻¹) '' U ∩ LocalClass D23 (g * e * g⁻¹) := by
  rw [image_conj_inter, Pair.image_conj_localClass pair_J]

theorem val_image_conjPerm'
    (g : J) (T : Set D23) :
    Subtype.val '' (⇑(Pair.conjPerm pair_J g) '' T) =
      (fun x => g * x * g⁻¹) '' (Subtype.val '' T) := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, ⟨x, hx, rfl⟩, (Pair.conjPerm_apply pair_J g x).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, Pair.conjPerm_apply pair_J g x⟩

theorem star_ok :
    trStarOK orb dT biT ea phiP cB = true := tr_parts.2.2.2.2.1

theorem gens_ok :
    trGensOK cB tB lK trc.treeC trc.treeR = true := tr_parts.2.2.2.2.2.1

theorem comm_ok :
    trCommOK orb dT biT cB trc.cord trc.cpar = true := tr_parts.2.2.2.2.2.2.1

theorem dom_ok :
    trDomOK orb dT biT cB tB trc.domW trc.ncW = true := tr_parts.2.2.2.2.2.2.2.1

theorem ptE_lt
    (u : Fin 3510) : ea[phiP[u.val]!]! < 31671 := ea_get_lt (phiP_lt u.2)

theorem ptE_eq
    (u : Fin 3510) : (ptE u : J) = (ptD23 ⟨ea[phiP[u.val]!]!, ptE_lt u⟩ : J) :=
  ptE_apply u

theorem mem_lhRoot_iff (i : Fin 2) (u : Fin 3510) :
    Fi22.ptD u ∈ Fi22.lhRoot i ↔ u.val ∈ Fi22.Native.lhData[i.val]! := by
  unfold Fi22.lhRoot
  rw [Fi22.ptD.injective.mem_set_image]
  rfl

theorem mem_lhRoot_zero (u : Fin 3510) :
    Fi22.ptD u ∈ Fi22.lhRoot 0 ↔ u.val ∈ Fi22.Native.lhData[0]! :=
  mem_lhRoot_iff 0 u

theorem mem_lhRoot_one (u : Fin 3510) :
    Fi22.ptD u ∈ Fi22.lhRoot 1 ↔ u.val ∈ Fi22.Native.lhData[1]! :=
  mem_lhRoot_iff 1 u

theorem chiPre_cRoot :
    chiPre (Subtype.val '' cRoot) = Fi22.lhRoot 0 := by
  ext p
  obtain ⟨u, rfl⟩ := Fi22.ptD.surjective p
  rw [mem_chiPre, chiD_symm_ptD, mem_lhRoot_zero, ptE_eq, Subtype.val_injective.mem_set_image,
    ptD23_mem_cRoot, Fin.val_mk, ((trStarOK_spec star_ok).2.2.2 u.val u.2).1,
    Array.contains_iff_mem]

theorem act23_zero
    {m : ℕ} (hm : m < 31671) : act23 0 m = ap dT m := by
  rw [act23_spec 0 m hm, conjPt_zero, rep_dT m hm]

theorem failC_lt :
    failC < 31671 := (trStarOK_spec star_ok).1

theorem d_mul_failC :
    d * conjPt failC ≠ conjPt failC * d := by
  rw [← conjPt_zero, ne_eq, conjPt_commute_iff (by norm_num) failC_lt, act23_zero failC_lt]
  exact (trStarOK_spec star_ok).2.2.1

theorem failC_mem_D23 :
    conjPt failC ∈ D23 := conjPt_mem_D23 failC_lt

theorem chiPre_mu :
    chiPre (LocalClass D23 (conjPt failC)) = Fi22.lhRoot 1 := by
  ext p
  obtain ⟨u, rfl⟩ := Fi22.ptD.surjective p
  have hlt := ptE_lt u
  have hE : (ptE u : J) = conjPt ea[phiP[u.val]!]! := ptE_apply u
  have hspec := ((trStarOK_spec star_ok).2.2.2 u.val u.2).2
  rw [mem_chiPre, chiD_symm_ptD, mem_lhRoot_one, ← Array.contains_iff_mem, hspec,
    tauAct_eq_act23, hE, mem_localClass, ← conjPt_commute_iff failC_lt hlt]
  constructor
  · rintro ⟨-, -, h⟩
    exact h.symm
  · intro h
    refine ⟨conjPt_mem_D23 hlt, fun e => d_mul_failC ?_, h.symm⟩
    have hs := (ptE u).2.2.2
    rw [hE, e] at hs
    exact hs.symm

@[expose] noncomputable def lKG (l : ℕ) : J := conjPt cGens[l]!

theorem rep_lKG : ∀ l ∈ Array.range 9, Rep 31671 lK[l]! (lKG l) := by
  intro l hl
  rw [Array.mem_range] at hl
  exact rep_lK hl

theorem cGens_lt
    {l : ℕ} (hl : l < 9) : cGens[l]! < 31671 :=
  ((trGensOK_spec gens_ok).2.1 l hl).1

theorem lKG_mem_cRoot
    {l : ℕ} (hl : l < 9) : lKG l ∈ Subtype.val '' cRoot :=
  conjPt_mem_cRoot (cGens_lt hl) ((trGensOK_spec gens_ok).2.1 l hl).2.1

theorem conj_image_cRoot_lKG
    {l : ℕ} (hl : l < 9) :
    (fun z => lKG l * z * (lKG l)⁻¹) '' (Subtype.val '' cRoot) = Subtype.val '' cRoot := by
  show (fun z => conjPt cGens[l]! * z * (conjPt cGens[l]!)⁻¹) '' (Subtype.val '' cRoot) =
    Subtype.val '' cRoot
  rw [← val_image_conjPerm', cRoot_eq,
    conjPerm_image_dsetP (rep_lK hl) ((trGensOK_spec gens_ok).2.1 l hl).2.2]

theorem conj_image_cRoot_of_mem
    {g : J} (hg : g ∈ lettersGroup (Array.range 9) lKG) :
    (fun z => g * z * g⁻¹) '' (Subtype.val '' cRoot) = Subtype.val '' cRoot := by
  induction hg using Subgroup.closure_induction with
  | mem s hs =>
    obtain ⟨l, hl, rfl⟩ := hs
    rw [Array.mem_range] at hl
    exact conj_image_cRoot_lKG hl
  | one => simp
  | mul x y _ _ hx hy =>
    have e : (fun z => x * y * z * (x * y)⁻¹) =
        (fun z => x * z * x⁻¹) ∘ (fun z => y * z * y⁻¹) := by
      funext z
      simp only [Function.comp, mul_inv_rev]
      group
    rw [e, Set.image_comp, hy, hx]
  | inv x _ hx =>
    have e : (fun z => x⁻¹ * z * x⁻¹⁻¹) '' ((fun z => x * z * x⁻¹) '' (Subtype.val '' cRoot)) =
        Subtype.val '' cRoot := by
      rw [Set.image_image]
      simp only [inv_inv]
      have : ∀ z, x⁻¹ * (x * z * x⁻¹) * x = z := fun z => by group
      simp only [this, Set.image_id']
    rwa [hx] at e

theorem treeC_facts :
    TreeFacts 31671 trc.treeC (Array.range 9) lKG 0 :=
  treeOK_facts rep_lKG (trGensOK_spec gens_ok).2.2.1

theorem treeR_facts :
    TreeFacts 31671 trc.treeR (Array.range 9) lKG rRoot :=
  treeOK_facts rep_lKG (trGensOK_spec gens_ok).2.2.2.1

theorem exists_conj_eq
    {q : ℕ} (hq : q < 31671) (hqC : pBit cB q = true) :
    ∃ g ∈ lettersGroup (Array.range 9) lKG, g * d * g⁻¹ = conjPt q := by
  have hin := ((trGensOK_spec gens_ok).2.2.2.2 q hq).1 hqC
  simp only [inTreeB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hin
  obtain ⟨hpos, hpts⟩ := hin
  refine ⟨treeG trc.treeC lKG (ap trc.treeC.pos q), treeC_facts.treeG_mem hpos, ?_⟩
  have he := treeC_facts.elt _ hpos
  rw [hpts] at he
  rw [← conjPt_zero]
  exact (idx_eq_iff (by norm_num) hq).1 he

theorem star_eq_of_agree
    (hHF : HyperovalFacts) {S : Set J} (hS : IsLocally351 D23 S) {x : J}
    (hxS : x ∈ S) (hxC : x ∈ Subtype.val '' cRoot) (hxd : x ∈ LocalClass D23 d) (hdS : d ∈ S)
    (hx : S ∩ LocalClass D23 x = Subtype.val '' cRoot ∩ LocalClass D23 x) :
    S ∩ LocalClass D23 d = Subtype.val '' cRoot ∩ LocalClass D23 d := by
  set xs : LocalClass D23 d := ⟨x, hxd⟩
  have hV := isLocallyHyperoval_chiPre (hS.locally d hdS)
  have hpV : (chiD xs : Fi22.J) ∈ Subtype.val '' chiPre (S ∩ LocalClass D23 d) :=
    ⟨chiD xs, (chiD_mem_chiPre xs).2 ⟨hxS, hxd⟩, rfl⟩
  have hpR : (chiD xs : Fi22.J) ∈ Subtype.val '' Fi22.lhRoot 0 :=
    ⟨chiD xs, by rw [← chiPre_cRoot]; exact (chiD_mem_chiPre xs).2 hxC, rfl⟩
  have hagree : Subtype.val '' chiPre (S ∩ LocalClass D23 d) ∩ LocalClass Fi22.D (chiD xs) =
      Subtype.val '' Fi22.lhRoot 0 ∩ LocalClass Fi22.D (chiD xs) := by
    ext q
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, hpl⟩
      obtain ⟨y, rfl⟩ := chiD.surjective p
      have hyx : (y : J) ∈ LocalClass D23 x := (mem_localClass_chiD xs y).2 hpl
      have hy : (y : J) ∈ S ∩ LocalClass D23 x := ⟨((chiD_mem_chiPre y).1 hp).1, hyx⟩
      rw [hx] at hy
      exact ⟨⟨chiD y, by rw [← chiPre_cRoot]; exact (chiD_mem_chiPre y).2 hy.1, rfl⟩, hpl⟩
    · rintro ⟨⟨p, hp, rfl⟩, hpl⟩
      obtain ⟨y, rfl⟩ := chiD.surjective p
      have hyx : (y : J) ∈ LocalClass D23 x := (mem_localClass_chiD xs y).2 hpl
      rw [← chiPre_cRoot] at hp
      have hy : (y : J) ∈ Subtype.val '' cRoot ∩ LocalClass D23 x := ⟨(chiD_mem_chiPre y).1 hp, hyx⟩
      rw [← hx] at hy
      exact ⟨⟨chiD y, (chiD_mem_chiPre y).2 ⟨hy.1, y.2⟩, rfl⟩, hpl⟩
  have h := Fi22.eq_lhRoot_of_agree hHF 0 hV hpV hpR hagree
  have h' : chiPre (S ∩ LocalClass D23 d) = chiPre (Subtype.val '' cRoot ∩ LocalClass D23 d) := by
    rw [chiPre_inter_star (Subtype.val '' cRoot), chiPre_cRoot]
    exact Set.image_injective.2 Subtype.val_injective h
  exact chiPre_inj Set.inter_subset_right Set.inter_subset_right h'

theorem good_step
    (hHF : HyperovalFacts) {S : Set J} (hS : IsLocally351 D23 S) {x y : J}
    (hxS : x ∈ S) (hxC : x ∈ Subtype.val '' cRoot)
    (hx : S ∩ LocalClass D23 x = Subtype.val '' cRoot ∩ LocalClass D23 x)
    (hyC : y ∈ Subtype.val '' cRoot) (hyx : y ∈ LocalClass D23 x) :
    y ∈ S ∧ S ∩ LocalClass D23 y = Subtype.val '' cRoot ∩ LocalClass D23 y := by
  have hyS : y ∈ S := by
    have h : y ∈ Subtype.val '' cRoot ∩ LocalClass D23 x := ⟨hyC, hyx⟩
    rw [← hx] at h
    exact h.1
  refine ⟨hyS, ?_⟩
  obtain ⟨z, hzC, rfl⟩ := hyC
  obtain ⟨q, rfl⟩ := ptD23.surjective z
  have hqC' : pBit cB q.val = true := ptD23_mem_cRoot.1 hzC
  obtain ⟨g, hg, hgd⟩ := exists_conj_eq q.2 hqC'
  rw [ptD23_val'] at hyx hyS ⊢
  have hgC := conj_image_cRoot_of_mem hg
  have hgC' := conj_image_cRoot_of_mem (Subgroup.inv_mem _ hg)
  have hS'l : IsLocally351 D23 ((fun z => g⁻¹ * z * g⁻¹⁻¹) '' S) := hS.conj pair_J g⁻¹
  have hd : g⁻¹ * conjPt q.val * g⁻¹⁻¹ = d := by rw [← hgd]; group
  have hdS' : d ∈ (fun z => g⁻¹ * z * g⁻¹⁻¹) '' S := ⟨conjPt q.val, hyS, hd⟩
  have hxy : x ∈ LocalClass D23 (conjPt q.val) :=
    ⟨hS.subset hxS, fun e => hyx.2.1 e.symm, hyx.2.2.symm⟩
  have hx'S : g⁻¹ * x * g⁻¹⁻¹ ∈ (fun z => g⁻¹ * z * g⁻¹⁻¹) '' S := ⟨x, hxS, rfl⟩
  have hx'C : g⁻¹ * x * g⁻¹⁻¹ ∈ Subtype.val '' cRoot := by rw [← hgC']; exact ⟨x, hxC, rfl⟩
  have hx'd : g⁻¹ * x * g⁻¹⁻¹ ∈ LocalClass D23 d := by
    rw [← hd]
    exact (Pair.conj_mem_localClass_iff pair_J g⁻¹).2 hxy
  have hx' : (fun z => g⁻¹ * z * g⁻¹⁻¹) '' S ∩ LocalClass D23 (g⁻¹ * x * g⁻¹⁻¹) =
      Subtype.val '' cRoot ∩ LocalClass D23 (g⁻¹ * x * g⁻¹⁻¹) := by
    rw [← conj_image_inter_localClass, hx, conj_image_inter_localClass, hgC']
  have hstar := star_eq_of_agree hHF hS'l hx'S hx'C hx'd hdS' hx'
  have e := congrArg (fun U => (fun z => g * z * g⁻¹) '' U) hstar
  rw [conj_image_inter_localClass, conj_image_inter_localClass, conj_conj_image, hgC,
    hgd] at e
  exact e

theorem trData_ne
    {p : ℕ} (hp : p < 31671) (hT : pBit tB p = true) (hC : pBit cB p = false) :
    inTreeB trc.treeR p = true :=
  ((trGensOK_spec gens_ok).2.2.2.2 p hp).2.1 hT hC

@[expose] def Agree (S : Set J) (z : J) : Prop :=
  z ∈ S ∧ S ∩ LocalClass D23 z = Subtype.val '' cRoot ∩ LocalClass D23 z

theorem agree_step_idx
    (hHF : HyperovalFacts) {S : Set J} (hS : IsLocally351 D23 S) {x y : ℕ}
    (hx : x < 31671) (hy : y < 31671) (hxB : pBit cB x = true) (hyB : pBit cB y = true)
    (hc : tauAct orb dT biT x y = y) (hn : x ≠ y) (hgx : Agree S (conjPt x)) :
    Agree S (conjPt y) :=
  good_step hHF hS hgx.1 (conjPt_mem_cRoot hx hxB) hgx.2 (conjPt_mem_cRoot hy hyB)
    ⟨conjPt_mem_D23 hy, fun e => hn (conjPt_injOn hx hy e.symm),
      ((conjPt_commute_iff hx hy).2 hc).symm⟩

theorem agree_all
    (hHF : HyperovalFacts) {S : Set J} (hS : IsLocally351 D23 S) (hdS : d ∈ S)
    (hstar : S ∩ LocalClass D23 d = Subtype.val '' cRoot ∩ LocalClass D23 d) :
    ∀ z ∈ Subtype.val '' cRoot, Agree S z := by
  obtain ⟨hosz, -, ho0, hc0, hopar, hocov⟩ := trCommOK_spec comm_ok
  have hlt : ∀ k < 1080, trc.cord[k]! < 31671 := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [ho0]; norm_num
    · exact (hopar k hk0 hk).2.1
  have hB : ∀ k < 1080, pBit cB trc.cord[k]! = true := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [ho0]; exact hc0
    · exact (hopar k hk0 hk).2.2.1
  have hgood : ∀ k < 1080, Agree S (conjPt trc.cord[k]!) := by
    intro k hk
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [ho0, conjPt_zero]
        exact ⟨hdS, hstar⟩
      · obtain ⟨hp, -, -, hc, hn⟩ := hopar k hk0 hk
        have hpk : trc.cpar[k]! < 1080 := by omega
        exact agree_step_idx hHF hS (hlt _ hpk) (hlt k hk) (hB _ hpk) (hB k hk) hc hn
          (ih _ hp hpk)
  rintro _ ⟨z, hm, rfl⟩
  obtain ⟨m, rfl⟩ := ptD23.surjective z
  have hmC : m.val ∈ cData := (pBit_cB m.2).1 (ptD23_mem_cRoot.1 hm)
  obtain ⟨k, hk, hke⟩ := Array.mem_iff_getElem.1 (hocov _ hmC)
  have hk' : k < 1080 := by omega
  have := hgood k hk'
  rw [getElem!_pos trc.cord k hk, hke] at this
  exact this

theorem dom_notMem_idx
    {S : Set J} {m w : ℕ} (hm : m < 31671) (hw : w < 31671)
    (hwB : pBit cB w = true) (hwm : tauAct orb dT biT w m = m) (hmT : pBit tB m = false)
    (hgw : Agree S (conjPt w)) : conjPt m ∉ S := by
  intro hmS
  have hmw : conjPt m ∈ LocalClass D23 (conjPt w) := by
    refine ⟨conjPt_mem_D23 hm, fun e => ?_, ((conjPt_commute_iff hw hm).2 hwm).symm⟩
    have := conjPt_injOn hm hw e
    rw [this] at hmT
    have hT := ((trGensOK_spec gens_ok).2.2.2.2 w hw).2.2 hwB
    rw [hmT] at hT
    exact absurd hT (by decide)
  have h' : conjPt m ∈ S ∩ LocalClass D23 (conjPt w) := ⟨hmS, hmw⟩
  rw [hgw.2] at h'
  obtain ⟨z, hz, hzm⟩ := h'.1
  obtain ⟨j, rfl⟩ := ptD23.surjective z
  have := conjPt_injOn j.2 hm hzm
  rw [ptD23_mem_cRoot, this] at hz
  have hT := ((trGensOK_spec gens_ok).2.2.2.2 m hm).2.2 hz
  rw [hmT] at hT
  exact absurd hT (by decide)

theorem subset_trRoot
    {S : Set J} (hS : IsLocally351 D23 S)
    (hgoodC : ∀ z ∈ Subtype.val '' cRoot, Agree S z) : S ⊆ Subtype.val '' trRoot := by
  intro f hfS
  obtain ⟨m, rfl⟩ : ∃ m : Fin 31671, f = conjPt m.val := by
    obtain ⟨m, hm⟩ := (isConj_d_iff f).1 (hS.subset hfS)
    exact ⟨m, hm.symm⟩
  by_contra hfT
  have hmT : pBit tB m.val = false := by
    cases h : pBit tB m.val
    · rfl
    · exact absurd (conjPt_mem_trRoot m.2 h) hfT
  obtain ⟨h1, h2, h3, -, -, -⟩ := trDomOK_spec dom_ok m.2 hmT
  exact dom_notMem_idx m.2 h1 h2 h3 hmT (hgoodC _ (conjPt_mem_cRoot h1 h2)) hfS

theorem lK_mem_iff
    {S : Set J} (hS : IsLocally351 D23 S) {l : ℕ} (hl : l < 9)
    (hlS : lKG l ∈ S) {p : ℕ} (hp : p < 31671) :
    conjPt p ∈ S ↔ conjPt (ap lK[l]! p) ∈ S := by
  have hgl : lKG l ∈ D23 := hS.subset hlS
  have e : conjPt (ap lK[l]! p) = lKG l * conjPt p * lKG l := by
    rw [rep_lK hl p hp]
    have := (idx_eq_iff hp (idx_lt (conjPt cGens[l]!) hp)).1 rfl
    rw [conjPt_inv' (cGens_lt hl)] at this
    exact this.symm
  rw [e]
  constructor
  · intro h
    exact hS.closed _ hlS _ h
  · intro h
    have := hS.closed _ hlS _ h
    rwa [show lKG l * (lKG l * conjPt p * lKG l) * lKG l = (lKG l * lKG l) * conjPt p *
      (lKG l * lKG l) by group, Pair.mul_self pair_J hgl, one_mul, mul_one] at this

theorem treeR_mem_iff
    {S : Set J} (hS : IsLocally351 D23 S)
    (hCS : Subtype.val '' cRoot ⊆ S) :
    ∀ k < trc.treeR.pts.size, (conjPt (ap trc.treeR.pts k) ∈ S ↔ conjPt rRoot ∈ S) := by
  obtain ⟨-, hr0, hptsl, -, -, hpar, -⟩ := treeR_facts
  obtain ⟨-, -, hp⟩ := treeOK_spec' (trGensOK_spec gens_ok).2.2.2.1
  intro k hk
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [hr0]
    · obtain ⟨hpk, hlab⟩ := hpar k hk hk0
      have hpk' : ap trc.treeR.par k < trc.treeR.pts.size := by omega
      rw [Array.mem_range] at hlab
      have hedge := ((hp k hk).2 hk0).2.2
      rw [← ih _ hpk hpk', ← hedge]
      exact (lK_mem_iff hS hlab (hCS (lKG_mem_cRoot hlab)) (hptsl _ hpk')).symm

theorem rest_mem_iff
    {S : Set J} (hS : IsLocally351 D23 S) (hCS : Subtype.val '' cRoot ⊆ S)
    {p : ℕ} (hp : p < 31671) (hpT : pBit tB p = true) (hpC : pBit cB p = false) :
    conjPt p ∈ S ↔ conjPt rRoot ∈ S := by
  have hin := trData_ne hp hpT hpC
  simp only [inTreeB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hin
  obtain ⟨hpos, hpts⟩ := hin
  have := treeR_mem_iff hS hCS _ hpos
  rwa [hpts] at this

theorem eq_cRoot_or_trRoot
    (hHF : HyperovalFacts) {S : Set J} (hS : IsLocally351 D23 S)
    (hdS : d ∈ S) (hstar : S ∩ LocalClass D23 d = Subtype.val '' cRoot ∩ LocalClass D23 d) :
    S = Subtype.val '' cRoot ∨ S = Subtype.val '' trRoot := by
  have hgoodC := agree_all hHF hS hdS hstar
  have hsub := subset_trRoot hS hgoodC
  have hCS : Subtype.val '' cRoot ⊆ S := fun z hz => (hgoodC z hz).1
  by_cases hrest : ∃ v ∈ S, v ∈ Subtype.val '' trRoot ∧ v ∉ Subtype.val '' cRoot
  · right
    obtain ⟨v, hvS, ⟨z, hpT, rfl⟩, hvC⟩ := hrest
    obtain ⟨p, rfl⟩ := ptD23.surjective z
    have hpC : pBit cB p.val = false := by
      cases h : pBit cB p.val
      · rfl
      · exact absurd (conjPt_mem_cRoot p.2 h) hvC
    have hroot : conjPt rRoot ∈ S :=
      (rest_mem_iff hS hCS p.2 (ptD23_mem_trRoot.1 hpT) hpC).1 hvS
    refine Set.Subset.antisymm hsub ?_
    rintro _ ⟨z, hwT, rfl⟩
    obtain ⟨w, rfl⟩ := ptD23.surjective z
    by_cases hwC : pBit cB w.val = true
    · exact hCS (conjPt_mem_cRoot w.2 hwC)
    · exact (rest_mem_iff hS hCS w.2 (ptD23_mem_trRoot.1 hwT) (by simpa using hwC)).2 hroot
  · left
    refine Set.Subset.antisymm (fun z hz => ?_) hCS
    by_contra hzC
    exact hrest ⟨z, hz, hsub hz, hzC⟩

theorem classify
    (hFF : Fi22Facts) (T : Set D23)
    (hT : IsLocally351 D23 (Subtype.val '' T)) (hne : T.Nonempty) : T ∈ cOrbit ∨ T ∈ trOrbit := by
  have hHF := hyperovalFacts
  obtain ⟨t, htT⟩ := hne
  obtain ⟨c, hc⟩ := isConj_iff.1 t.2
  obtain ⟨S₁, hS₁⟩ : ∃ S₁, S₁ = (fun x => c⁻¹ * x * c⁻¹⁻¹) '' (Subtype.val '' T) := ⟨_, rfl⟩
  have hS₁l : IsLocally351 D23 S₁ := hS₁ ▸ hT.conj pair_J c⁻¹
  have hdS₁ : d ∈ S₁ := by
    rw [hS₁]
    exact ⟨t, ⟨t, htT, rfl⟩, by rw [← hc]; group⟩
  have hV := isLocallyHyperoval_chiPre (hS₁l.locally d hdS₁)
  rw [chiPre_inter_star] at hV
  obtain ⟨i, g, hg⟩ := hFF.exists_mem_lhOrbit _ hV (chiPre_nonempty (hS₁l.nonempty d hdS₁))
  obtain ⟨h, hh⟩ := pi22_mem_range g
  obtain ⟨S₂, hS₂⟩ : ∃ S₂, S₂ = (fun x => (h : J)⁻¹ * x * ((h : J)⁻¹)⁻¹) '' S₁ := ⟨_, rfl⟩
  have hS₂l : IsLocally351 D23 S₂ := hS₂ ▸ hS₁l.conj pair_J _
  have hhd : (h : J)⁻¹ * d * ((h : J)⁻¹)⁻¹ = d := by
    have := mem_Cd.1 h.2
    rw [inv_inv, mul_assoc, ← this, ← mul_assoc, inv_mul_cancel, one_mul]
  have hdS₂ : d ∈ S₂ := by rw [hS₂]; exact ⟨d, hdS₁, hhd⟩
  have hpre : chiPre S₂ = Fi22.lhRoot i := by
    rw [hS₂, chiPre_conj h g hh, hg, ← Set.image_comp, ← Equiv.Perm.coe_mul, ← map_mul,
      inv_mul_cancel, map_one, Equiv.Perm.coe_one, Set.image_id]
  have hback : ∀ R : Set D23, Subtype.val '' R = S₂ →
      T = ⇑(Pair.conjPerm pair_J (c * (h : J))) '' R := by
    intro R hR
    apply Set.image_injective.2 Subtype.val_injective
    rw [val_image_conjPerm', hR, hS₂, hS₁, conj_image_image, conj_image_image,
      show c * (h : J) * (h : J)⁻¹ * c⁻¹ = 1 by group, conj_one_image]
  fin_cases i
  ·
    have hst : S₂ ∩ LocalClass D23 d = Subtype.val '' cRoot ∩ LocalClass D23 d := by
      apply chiPre_inj Set.inter_subset_right Set.inter_subset_right
      rw [chiPre_inter_star, chiPre_inter_star, chiPre_cRoot]
      exact hpre
    rcases eq_cRoot_or_trRoot hHF hS₂l hdS₂ hst with e | e
    · exact Or.inl ⟨c * h, hback cRoot e.symm⟩
    · exact Or.inr ⟨c * h, hback trRoot e.symm⟩
  ·
    exfalso
    have hst : S₂ ∩ LocalClass D23 d = LocalClass D23 d ∩ LocalClass D23 (conjPt failC) := by
      apply chiPre_inj Set.inter_subset_right Set.inter_subset_left
      rw [chiPre_inter_star, Set.inter_comm, chiPre_inter_star, chiPre_mu]
      exact hpre
    exact IsLocally351.not_star_muSet hHF Fi22.f22_J pair_J (localPoints_D23 polarFacts) hS₂l
      hdS₂ failC_mem_D23 d_mul_failC hst

end CFSG.Sporadic.Fi23
