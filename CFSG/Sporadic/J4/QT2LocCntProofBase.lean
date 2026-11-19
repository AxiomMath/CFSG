
module

public import CFSG.Sporadic.J4.QT2LocProofBase
public import CFSG.Sporadic.J4.QT2LocCntCheck
public import CFSG.Sporadic.J4.QT2LocCntGen
public import CFSG.Sporadic.J4.QTOutNorm

@[expose] public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.Th Matrix
open scoped Classical

instance rowFinite : Finite Row := inferInstanceAs (Finite (Fin 112 → ZMod 2))

noncomputable def w₀ : Row := toRow rootV.toVec

theorem vecAt_zero' (hF : J4NativeFacts) : vecAt 0 = w₀ := vecAt_zero hF.orbitFacts

theorem mem_Hj_of_smul_root (hF : J4Facts) {x : J} (h : x • w₀ = w₀) : x ∈ Hj := hF.stab x h

theorem smul_root_of_mem_Hj (hM : MatFacts) {x : J} (h : x ∈ Hj) : x • w₀ = w₀ :=
  Hj_fix_root hM x h

def RIn (v : Row) (x : J) : Prop :=
  ∃ g : J, g • w₀ = v ∧ g⁻¹ * x * g ∈ Eg uJ 11

theorem RIn_conj (k : J) (v : Row) (x : J) : RIn (k • v) (k * x * k⁻¹) ↔ RIn v x := by
  constructor
  · rintro ⟨g, hg, hE⟩
    refine ⟨k⁻¹ * g, ?_, ?_⟩
    · rw [mul_smul, hg, inv_smul_smul]
    · have e : (k⁻¹ * g)⁻¹ * x * (k⁻¹ * g) = g⁻¹ * (k * x * k⁻¹) * g := by group
      rw [e]
      exact hE
  · rintro ⟨g, hg, hE⟩
    refine ⟨k * g, ?_, ?_⟩
    · rw [mul_smul, hg]
    · have e : (k * g)⁻¹ * (k * x * k⁻¹) * (k * g) = g⁻¹ * x * g := by group
      rw [e]
      exact hE

theorem RIn_rep (hM : MatFacts) (hF : J4Facts) {u : J} {r : Row} (hr : r = u⁻¹ • w₀) (x : J) :
    RIn r x ↔ u * x * u⁻¹ ∈ Eg uJ 11 := by
  constructor
  · rintro ⟨g, hg, hE⟩
    have h1 : (u * g) • w₀ = w₀ := by rw [mul_smul, hg, hr, smul_inv_smul]
    have hH : u * g ∈ Hj := mem_Hj_of_smul_root hF h1
    have e : u * x * u⁻¹ = (u * g) * (g⁻¹ * x * g) * (u * g)⁻¹ := by group
    rw [e]
    exact Hj_normalizes_Eg hM _ hH _ hE
  · intro h
    refine ⟨u⁻¹, hr.symm, ?_⟩
    rw [inv_inv]
    exact h

theorem conj_closed_of_letters (hM : MatFacts) (L : List ℕ)
    (hL : ∀ c ∈ L, ∀ ℓ ∈ letters, act ℓ c ∈ L) :
    ∀ h ∈ Hj, (∀ c ∈ L, ∃ c' ∈ L, h * eta uJ 11 c * h⁻¹ = eta uJ 11 c') ∧
      (∀ c ∈ L, ∃ c' ∈ L, h⁻¹ * eta uJ 11 c * h = eta uJ 11 c') := by
  have hmem : ∀ h ∈ Subgroup.closure (XJ '' {ℓ | ℓ ∈ letters}),
      (∀ c ∈ L, ∃ c' ∈ L, h * eta uJ 11 c * h⁻¹ = eta uJ 11 c') ∧
        (∀ c ∈ L, ∃ c' ∈ L, h⁻¹ * eta uJ 11 c * h = eta uJ 11 c') := by
    intro h hh
    induction hh using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨ℓ, hℓ, rfl⟩ := hy
      refine ⟨fun c hc => ⟨act ℓ c, hL c hc ℓ hℓ, hX_all hM hℓ c⟩, fun c hc => ?_⟩
      obtain ⟨hℓ', hinv⟩ := XJ_inv hℓ
      refine ⟨act (-ℓ) c, hL c hc _ hℓ', ?_⟩
      have := hX_all hM hℓ' c
      rwa [hinv, inv_inv] at this
    | one => exact ⟨fun c hc => ⟨c, hc, by simp⟩, fun c hc => ⟨c, hc, by simp⟩⟩
    | mul x y _ _ hx hy =>
      refine ⟨fun c hc => ?_, fun c hc => ?_⟩
      · obtain ⟨c1, hc1, e1⟩ := hy.1 c hc
        obtain ⟨c2, hc2, e2⟩ := hx.1 c1 hc1
        refine ⟨c2, hc2, ?_⟩
        rw [← e2, ← e1]
        group
      · obtain ⟨c1, hc1, e1⟩ := hx.2 c hc
        obtain ⟨c2, hc2, e2⟩ := hy.2 c1 hc1
        refine ⟨c2, hc2, ?_⟩
        rw [← e2, ← e1]
        group
    | inv x _ hx =>
      refine ⟨fun c hc => ?_, fun c hc => ?_⟩
      · obtain ⟨c1, hc1, e1⟩ := hx.2 c hc
        exact ⟨c1, hc1, by rw [inv_inv]; exact e1⟩
      · obtain ⟨c1, hc1, e1⟩ := hx.1 c hc
        exact ⟨c1, hc1, by rw [inv_inv]; exact e1⟩
  exact fun h hh => hmem h (Hj_le_closure hh)

theorem chkZMasks_parts : (∀ c ∈ zMasks, c < 2048 ∧ ∀ ℓ ∈ letters, act ℓ c ∈ zMasks) ∧
    zMasks.length = 1771 ∧ zMasks.Nodup ∧ (3 : ℕ) ∈ zMasks ∧ (1131 : ℕ) ∈ zMasks ∧
    (orbits.getD 1 (3, [], [])).1 = 3 := by
  have h := chkZMasks_true
  unfold chkZMasks at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨fun c hc => ⟨(h1 c hc).1, fun ℓ hℓ => by simpa using (h1 c hc).2 ℓ hℓ⟩, h2, h3, h4, h5, h6⟩

noncomputable def Zl : Finset J := (zMasks.map (eta uJ 11)).toFinset

theorem mem_Zl {x : J} : x ∈ Zl ↔ ∃ c ∈ zMasks, eta uJ 11 c = x := by
  simp [Zl]

theorem card_Zl (hM : MatFacts) : Zl.card = 1771 := by
  obtain ⟨h1, h2, h3, -⟩ := chkZMasks_parts
  rw [Zl, List.toFinset_card_of_nodup, List.length_map, h2]
  rw [List.nodup_map_iff_inj_on h3]
  intro c hc d hd e
  exact eta_inj hM c (h1 c hc).1 d (h1 d hd).1 e

theorem Zl_conj (hM : MatFacts) :
    ∀ h ∈ Hj, (∀ x ∈ Zl, h * x * h⁻¹ ∈ Zl) ∧ (∀ x ∈ Zl, h⁻¹ * x * h ∈ Zl) := by
  intro h hh
  obtain ⟨h1, -⟩ := chkZMasks_parts
  have := conj_closed_of_letters hM zMasks (fun c hc ℓ hℓ => (h1 c hc).2 ℓ hℓ) h hh
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨c, hc, rfl⟩ := mem_Zl.1 hx
    obtain ⟨c', hc', e⟩ := this.1 c hc
    exact mem_Zl.2 ⟨c', hc', e.symm⟩
  · obtain ⟨c, hc, rfl⟩ := mem_Zl.1 hx
    obtain ⟨c', hc', e⟩ := this.2 c hc
    exact mem_Zl.2 ⟨c', hc', e.symm⟩

theorem exists_conj_eta_three (hM : MatFacts) {c : ℕ} (hc : c ∈ zMasks) :
    ∃ g ∈ Hj, g * eta uJ 11 3 * g⁻¹ = eta uJ 11 c := by
  obtain ⟨-, h2, -, -, -, h6⟩ := chkZMasks_parts
  have hoo : orbits.getD 1 (3, [], []) ∈ orbits := by
    by_contra hnot
    have hdef : orbits.getD 1 (3, [], []) = (3, [], []) := by
      rw [List.getD_eq_getElem?_getD]
      cases h : orbits[1]? with
      | none => rfl
      | some y =>
        exact absurd (List.mem_of_getElem? h) (by simpa [List.getD_eq_getElem?_getD, h] using hnot)
    have hz : zMasks = [] := by
      simp only [zMasks, hdef]
      rfl
    rw [hz] at h2
    simp at h2
  obtain ⟨p, hp, rfl⟩ : ∃ p ∈ (orbits.getD 1 (3, [], [])).2.1, p.1 = c := by
    simpa [zMasks] using hc
  obtain ⟨hlet, hfold⟩ := orbit_words _ hoo p hp
  rw [h6] at hfold
  refine ⟨(p.2.map XJ).prod, ?_, ?_⟩
  · refine Subgroup.list_prod_mem Hj ?_
    intro x hx
    obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_map.1 hx
    exact XJ_mem (hlet ℓ hℓ)
  · rw [word_conj XJ act p.2 (fun ℓ hℓ => hX_all hM (hlet ℓ hℓ)), hfold]

theorem Zl_trans (hM : MatFacts) : ∀ x ∈ Zl, ∀ y ∈ Zl, ∃ h ∈ Hj, h * x * h⁻¹ = y := by
  intro x hx y hy
  obtain ⟨c₁, hc₁, rfl⟩ := mem_Zl.1 hx
  obtain ⟨c₂, hc₂, rfl⟩ := mem_Zl.1 hy
  obtain ⟨g₁, hg₁, e₁⟩ := exists_conj_eta_three hM hc₁
  obtain ⟨g₂, hg₂, e₂⟩ := exists_conj_eta_three hM hc₂
  refine ⟨g₂ * g₁⁻¹, Hj.mul_mem hg₂ (Hj.inv_mem hg₁), ?_⟩
  rw [← e₁, ← e₂]
  group

noncomputable def vecP (O : VOrb) (p : ℕ) : Row := toRow (O.pts[p]!).toVec

theorem locTabs_get (hM : MatFacts) {g : ℕ} (hg : g < 3) :
    locTabs[g]! = frTable ((locMats ())[g]?.getD idRows) := by
  have hs := hM.locSize
  rw [locTabs, getElem!_pos _ g (by rw [Array.size_map, hs]; exact hg), Array.getElem_map,
    Array.getElem?_eq_getElem (by rw [hs]; exact hg), Option.getD_some]

theorem locTabs_size (hM : MatFacts) : locTabs.size = 3 := by
  rw [locTabs, Array.size_map]; exact hM.locSize

theorem vorb_size {O : VOrb} {r : V2} {m : ℕ} (hok : vorbOK locTabs r O m = true) :
    O.pts.size = m := by
  unfold vorbOK at hok
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  exact hok.1.1.1.1.1

theorem vorb_root {O : VOrb} {r : V2} {m : ℕ} (hok : vorbOK locTabs r O m = true) :
    O.pts[0]! = r ∧ 0 < m := by
  unfold vorbOK at hok
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, V2.beq_iff] at hok
  exact ⟨hok.1.2, hok.1.1.2⟩

theorem vorb_at {O : VOrb} {r : V2} {m : ℕ} (hok : vorbOK locTabs r O m = true) {q : ℕ}
    (hq : q < m) : vorbAt locTabs O q = true := by
  unfold vorbOK at hok
  rw [Bool.and_eq_true, List.all_eq_true] at hok
  exact hok.2 q (List.mem_range.2 hq)

theorem vorb_img (hM : MatFacts) {O : VOrb} {r : V2} {m : ℕ}
    (hok : vorbOK locTabs r O m = true) {k p : ℕ} (hk : k < 3) (hp : p < m) :
    ∃ q < m, vecP O q = (xJ k)⁻¹ • vecP O p := by
  have h := vorb_at hok hp
  unfold vorbAt at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have := h.1.2 k (by rw [locTabs_size hM]; exact hk)
  simp only [bne_iff_ne, ne_eq, decide_eq_true_eq, V2.beq_iff] at this
  obtain ⟨⟨h0, hle⟩, heq⟩ := this
  rw [vorb_size hok] at hle
  refine ⟨vfind O.pts O.slots O.bits (frApply locTabs[k]! O.pts[p]!) - 1, by omega, ?_⟩
  rw [← ofRow_inj, xJ_inv_smul hM]
  show (O.pts[vfind O.pts O.slots O.bits (frApply locTabs[k]! O.pts[p]!) - 1]!).toVec =
    (O.pts[p]!).toVec ᵥ* _
  rw [heq, locTabs_get hM hk, frApply_toVec_eq_vecMul]

theorem vorb_invariant (hM : MatFacts) {O : VOrb} {r : V2} {m : ℕ}
    (hok : vorbOK locTabs r O m = true) :
    ∀ g ∈ Hj, ∀ v ∈ vecP O '' Set.Iio m, g • v ∈ vecP O '' Set.Iio m := by
  refine smul_mem_of_inv_gens fun g hg v hv => ?_
  obtain ⟨p, hp, rfl⟩ := hv
  have hk : ∃ k < 3, g = xJ k := by
    rcases hg with h | h | h
    · exact ⟨0, by norm_num, h⟩
    · exact ⟨1, by norm_num, h⟩
    · exact ⟨2, by norm_num, h⟩
  obtain ⟨k, hk, rfl⟩ := hk
  obtain ⟨q, hq, e⟩ := vorb_img hM hok hk hp
  exact ⟨q, hq, e⟩

theorem vorb_orbit_subset (hM : MatFacts) {O : VOrb} {r : V2} {m : ℕ}
    (hok : vorbOK locTabs r O m = true) {v : Row} (hv : ∃ h ∈ Hj, v = h • toRow r.toVec) :
    v ∈ (Finset.range m).image (vecP O) := by
  obtain ⟨h, hh, rfl⟩ := hv
  have h0 : toRow r.toVec ∈ vecP O '' Set.Iio m :=
    ⟨0, (vorb_root hok).2, by rw [vecP, (vorb_root hok).1]⟩
  obtain ⟨q, hq, e⟩ := vorb_invariant hM hok h hh _ h0
  exact Finset.mem_image.2 ⟨q, Finset.mem_range.2 hq, e⟩

noncomputable def uElt (ℓ : ℕ) : J := pathElt (repPaths.getD ℓ [])

noncomputable def rep (ℓ : ℕ) : Row := (uElt ℓ)⁻¹ • w₀

theorem rep_eq (ℓ : ℕ) : rep ℓ = (uElt ℓ)⁻¹ • w₀ := rfl

def Dlt (ℓ : ℕ) : Set Row := {v | ∃ h ∈ Hj, v = h • rep ℓ}

theorem rep_toVec (hM : MatFacts) {ℓ : ℕ} (hℓ : ℓ < 7) :
    rep ℓ = toRow (pathVec (repPaths.getD ℓ [])).toVec := by
  rw [← ofRow_inj, rep, uElt, inv_smul_row, ← Mx_apply, Mx_pathElt hM _ (repPaths_letters ℓ hℓ), w₀]
  change rootV.toVec ᵥ* rowsMatrix _ = (pathVec (repPaths.getD ℓ [])).toVec
  rw [pathVec, pathVecFrom_toVec]

theorem Dlt_zero_card (hM : MatFacts) : (Dlt 0).ncard ≤ 1 := by
  have h : Dlt 0 ⊆ {w₀} := by
    rintro v ⟨h, hh, rfl⟩
    have : rep 0 = w₀ := by
      simp [rep, uElt, repPaths, pathElt]
    rw [this, smul_root_of_mem_Hj hM hh]
    exact Set.mem_singleton _
  exact (Set.ncard_le_ncard h (Set.finite_singleton _)).trans (by simp)

theorem Dlt_card_le_of_vorb (hM : MatFacts) {ℓ : ℕ} {O : VOrb} {r : V2} {m : ℕ}
    (hok : vorbOK locTabs r O m = true) (hr : rep ℓ = toRow r.toVec) : (Dlt ℓ).ncard ≤ m := by
  have hsub : Dlt ℓ ⊆ ↑((Finset.range m).image (vecP O)) := by
    rintro v ⟨h, hh, hvh⟩
    exact Finset.mem_coe.2 (vorb_orbit_subset hM hok ⟨h, hh, by rw [hvh, hr]⟩)
  refine (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans ?_
  rw [Set.ncard_coe_finset]
  exact Finset.card_image_le.trans (by simp)

theorem Dlt_eq_orbit_rep (ℓ : ℕ) : Dlt ℓ = MulAction.orbit Hj (rep ℓ) := by
  ext v
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h, hh⟩, rfl⟩
  · rintro ⟨⟨h, hh⟩, rfl⟩
    exact ⟨h, hh, rfl⟩

theorem Dlt_six_card (hF : J4Facts) : (Dlt 6).ncard ≤ 28336 := by
  have hM := hF.mat
  refine Dlt_card_le_of_vorb hM (O := orb6) (r := rep6Vec) orb6_ok ?_
  exact rep_toVec hM (by norm_num)

noncomputable def ZE (ℓ : ℕ) : Finset J :=
  Zl.filter fun x => uElt ℓ * x * (uElt ℓ)⁻¹ ∈ Eg uJ 11

theorem dlt_filter_bound (hM : MatFacts) (hF : J4Facts) (ℓ : ℕ) {m dl : ℕ}
    (hm : (ZE ℓ).card ≤ m) (hD : (Dlt ℓ).ncard ≤ dl) {z : J} (hz : z ∈ Zl) :
    1771 * {v | v ∈ Dlt ℓ ∧ RIn v z}.ncard ≤ dl * m := by
  have hc := card_Zl hM
  have hm' : ∀ v ∈ Dlt ℓ, {x | x ∈ (↑Zl : Set J) ∧ RIn v x}.ncard ≤ m := by
    rintro v ⟨h, hh, rfl⟩
    have hmap : ∀ x ∈ {x | x ∈ (↑Zl : Set J) ∧ RIn (h • rep ℓ) x},
        (fun x => h⁻¹ * x * h) x ∈ (↑(ZE ℓ) : Set J) := by
      rintro x ⟨hxZ, hxR⟩
      rw [Finset.mem_coe] at hxZ ⊢
      refine Finset.mem_filter.2 ⟨(Zl_conj hM h hh).2 x hxZ, ?_⟩
      have h1 : RIn (rep ℓ) (h⁻¹ * x * h) := by
        have := (RIn_conj h (rep ℓ) (h⁻¹ * x * h)).1
        rw [show h * (h⁻¹ * x * h) * h⁻¹ = x by group] at this
        exact this hxR
      exact (RIn_rep hM hF (rep_eq ℓ) _).1 h1
    have hinj : Set.InjOn (fun x => h⁻¹ * x * h) {x | x ∈ (↑Zl : Set J) ∧ RIn (h • rep ℓ) x} := by
      intro x _ y _ hxy
      simpa using hxy
    refine (Set.ncard_le_ncard_of_injOn _ hmap hinj (Finset.finite_toSet _)).trans ?_
    rw [Set.ncard_coe_finset]
    exact hm
  have hY : ∀ x ∈ (↑Zl : Set J), {p | p ∈ Dlt ℓ ∧ RIn p z}.ncard ≤
      {p | p ∈ Dlt ℓ ∧ RIn p x}.ncard := by
    intro x hx
    obtain ⟨k, hk, hkx⟩ := Zl_trans hM z hz x (Finset.mem_coe.1 hx)
    refine Set.ncard_le_ncard_of_injOn (fun v => k • v) ?_ ?_ (Set.toFinite _)
    · rintro v ⟨⟨h, hh, rfl⟩, hvR⟩
      refine ⟨⟨k * h, Hj.mul_mem hk hh, by rw [mul_smul]⟩, ?_⟩
      have := (RIn_conj k (h • rep ℓ) z).2 hvR
      rwa [hkx] at this
    · intro v _ v' _ hvv
      exact MulAction.injective k hvv
  have key := incidence_le_ncard (Dlt ℓ) (↑Zl : Set J) RIn m hm' z hY
  rw [Set.ncard_coe_finset, hc] at key
  exact key.trans (Nat.mul_le_mul_right _ hD)

theorem memEVec_of_mem (hM : MatFacts) {ℓ : ℕ} (hℓ : ℓ < 7) {c : ℕ}
    (hinv : eqRows (mulRows (pathRows (repPaths.getD ℓ []))
      (invRows (pathRows (repPaths.getD ℓ [])))) idRows = true)
    (hmem : uElt ℓ * eta uJ 11 c * (uElt ℓ)⁻¹ ∈ Eg uJ 11) :
    memEVec (uTab (locMats ()) (locInvs ())) (evsOf (uTab (locMats ()) (locInvs ())))
      (pathRows (repPaths.getD ℓ [])) (invRows (pathRows (repPaths.getD ℓ []))) c = true := by
  set M := pathRows (repPaths.getD ℓ []) with hMdef
  set Mi := invRows M with hMidef
  obtain ⟨c'', hc'', he⟩ := (mem_Eg_iff (elem_uJ hM)).1 hmem
  have hMx : Mx (uElt ℓ) = rowsMatrix M := Mx_pathElt hM _ (repPaths_letters ℓ hℓ)
  have h1 : rowsMatrix M * rowsMatrix Mi = 1 := by
    have := congrArg rowsMatrix (eqRows_iff.1 hinv)
    rwa [rowsMatrix_mulRows, rowsMatrix_idRows] at this
  have hMxi : Mx (uElt ℓ)⁻¹ = rowsMatrix Mi := by
    have h2 : Mx (uElt ℓ)⁻¹ * Mx (uElt ℓ) = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    calc Mx (uElt ℓ)⁻¹ = Mx (uElt ℓ)⁻¹ * (rowsMatrix M * rowsMatrix Mi) := by rw [h1, mul_one]
      _ = (Mx (uElt ℓ)⁻¹ * Mx (uElt ℓ)) * rowsMatrix Mi := by rw [hMx, mul_assoc]
      _ = rowsMatrix Mi := by rw [h2, one_mul]
  have hc2 : Mx (eta uJ 11 c) = rowsMatrix (etaRows (uTab (locMats ()) (locInvs ())) 11 c) :=
    Mx_eta hM 11 le_rfl c
  have h3 := congrArg Mx he
  rw [map_mul, map_mul, hMx, hMxi, hc2, ← rowsMatrix_mulRows, ← rowsMatrix_mulRows] at h3
  unfold memEVec evsOf
  rw [List.any_eq_true]
  refine ⟨etaVec ((uTab (locMats ()) (locInvs ())).map frTable) 11 c'',
    List.mem_map.2 ⟨c'', List.mem_range.2 (by simpa using hc''), rfl⟩, ?_⟩
  by_contra hne
  have hd : differs (frApply (frTable (mulRows (mulRows M (etaRows (uTab (locMats ())
      (locInvs ())) 11 c)) Mi)) w0)
      (etaVec ((uTab (locMats ()) (locInvs ())).map frTable) 11 c'') = true := by
    simpa using hne
  apply differs_toVec hd
  rw [frApply_toVec_eq_vecMul, h3, etaVec_toVec hM 11 le_rfl]

theorem ZE_card_le (hM : MatFacts) {ℓ : ℕ} (hℓ : ℓ < 7) {n : ℕ}
    (hinv : eqRows (mulRows (pathRows (repPaths.getD ℓ []))
      (invRows (pathRows (repPaths.getD ℓ [])))) idRows = true)
    (hn : (candZ (locMats ()) (locInvs ()) ℓ).length ≤ n) : (ZE ℓ).card ≤ n := by
  have hsub : ZE ℓ ⊆ ((candZ (locMats ()) (locInvs ()) ℓ).map (eta uJ 11)).toFinset := by
    intro x hx
    rw [ZE, Finset.mem_filter] at hx
    obtain ⟨hxZ, hxE⟩ := hx
    obtain ⟨c, hc, rfl⟩ := mem_Zl.1 hxZ
    rw [List.mem_toFinset, List.mem_map]
    refine ⟨c, ?_, rfl⟩
    unfold candZ
    rw [List.mem_filter]
    exact ⟨hc, memEVec_of_mem hM hℓ hinv hxE⟩
  exact (Finset.card_le_card hsub).trans (List.toFinset_card_le _ |>.trans (by simpa using hn))

def Omega (z : J) : Set Row := {v | RIn v z}

theorem pathInv_get {ℓ : ℕ} (hℓ : ℓ < 7) :
    eqRows (mulRows (pathRows (repPaths.getD ℓ [])) (invRows (pathRows (repPaths.getD ℓ []))))
      idRows = true := by
  have h := pathInv_ok
  rw [List.all_eq_true] at h
  exact h ℓ (List.mem_range.2 hℓ)

theorem cands_parts :
    (candZ (locMats ()) (locInvs ()) 1).length = 0 ∧
    (candZ (locMats ()) (locInvs ()) 2).length = 0 ∧
    (candZ (locMats ()) (locInvs ()) 3).length = 0 ∧
    (candZ (locMats ()) (locInvs ()) 4).length = 0 ∧
    (candZ (locMats ()) (locInvs ()) 5).length = 7 ∧
    (candZ (locMats ()) (locInvs ()) 6).length = 1 := by
  have h := chkCntZ_true
  unfold chkCntZ at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem z0_mem_Zl : eta uJ 11 1131 ∈ Zl := mem_Zl.2 ⟨1131, chkZMasks_parts.2.2.2.2.1, rfl⟩

theorem mem_Eg_of_mem_Zl {x : J} (hx : x ∈ Zl) : x ∈ Eg uJ 11 := by
  obtain ⟨c, -, rfl⟩ := mem_Zl.1 hx
  exact eta_mem_Eg 11 le_rfl c

theorem final_arith (m : ℕ) (h1 : m ≤ 77) (h2 : 0 < m) (h7 : 7 ∣ m * 283115520)
    (h11 : 11 ∣ m * 283115520) : m = 77 := by
  have c7 : Nat.Coprime 7 283115520 := by decide
  have c11 : Nat.Coprime 11 283115520 := by decide
  have d7 : 7 ∣ m := c7.dvd_of_dvd_mul_right h7
  have d11 : 11 ∣ m := c11.dvd_of_dvd_mul_right h11
  clear h7 h11 c7 c11
  have d77 : 7 * 11 ∣ m := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) d7 d11
  clear d7 d11
  obtain ⟨k, hk⟩ := d77
  have hk0 : k ≠ 0 := by
    rintro rfl
    omega
  have hk1 : k ≤ 1 := by omega
  have : k = 1 := by omega
  subst this
  omega

end CFSG.Sporadic.J4.QT2
