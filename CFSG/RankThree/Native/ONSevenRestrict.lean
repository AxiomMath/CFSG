module

public import CFSG.RankThree.Native.ONSevenArrays
public import CFSG.Sporadic.Schreier.ONThreePoint
public import CFSG.Sporadic.Schreier.ONRestrict
public import CFSG.Sporadic.Schreier.ONOuterDefs

public noncomputable section

namespace CFSG.RankThree.Native

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native CFSG.Certificates
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer

theorem onSeven_eqA_comm {n : ℕ} {t u : Array ℕ} (h : eqA n t u = true) : eqA n u t = true := by
  rw [eqA, CFSG.Monster.B.Co2.allLt_iff] at h ⊢
  intro i hi
  have := h i hi
  rw [beq_iff_eq] at this ⊢
  exact this.symm

theorem onSeven_prep_strong {j : ℕ} (hj : j < 7) :
    PRep N qonStrongArrs[j]! (sgen j) ∧ PRep N onSevenInvArrs[j]! (sgen j)⁻¹ := by
  have hF := chainFacts qon_chain_cert.1
  have hs : j < qonStrongArrs.size := by rw [strong_parts.1]; exact hj
  have h1 := qon_arrays.prep_strong hF j hs
  have h2 := qon_arrays.prep_strongInv hF hs
  have e : strongAt QON j = sgen j := by
    rw [strongAt_of_lt QON (by rw [cert_on_schreier_action_data.2.1]; exact hj)]
    exact cert_on_schreier_action_data.2.2.2.2.1 ⟨j, _⟩
  rw [e] at h1 h2
  exact ⟨h1, h2⟩

theorem prep_onSevenArr {w : List ℤ} (hw : plettersOK 7 w = true) :
    PRep N (onSevenArr w) (evalS w) :=
  prep_pword (gs := sgen) (fun _ hh => (onSeven_prep_strong hh).1)
    (fun _ hh => (onSeven_prep_strong hh).2) w hw

theorem prep_onSevenPow {x : Array ℕ} {X : Equiv.Perm (Fin N)} (hx : PRep N x X) :
    ∀ e, PRep N (onSevenPow x e) (X ^ e)
  | 0 => by simpa [onSevenPow] using (prep_pid (n := N))
  | e + 1 => by
    rw [onSevenPow, pow_succ']
    exact prep_pcomp hx (prep_onSevenPow hx e)

theorem prep_onSevenConj {t x : Array ℕ} {T X : Equiv.Perm (Fin N)} (ht : PRep N t T)
    (hx : PRep N x X) (hinv : pisInv nPts t (pinvCand nPts t) = true) :
    PRep N (onSevenConj t x) (T * X * T⁻¹) :=
  prep_pcomp (prep_pcomp ht hx) (prep_inv_of_pisInv ht hinv)

theorem prep_onSevenConjInv {u x : Array ℕ} {U X : Equiv.Perm (Fin N)} (hu : PRep N u U)
    (hx : PRep N x X) (hinv : pisInv nPts u (pinvCand nPts u) = true) :
    PRep N (onSevenConjInv u x) (U⁻¹ * X * U) :=
  prep_pcomp (prep_pcomp (prep_inv_of_pisInv hu hinv) hx) hu

theorem getElem!_map_onSeven {α β : Type*} [Inhabited α] [Inhabited β] (f : α → β)
    (a : Array α) {i : ℕ} (hi : i < a.size) : (a.map f)[i]! = f a[i]! :=
  getElem!_map' f a hi

theorem evalList_getElem {ws : Array (List ℤ)} {k : ℕ} (hk : k < (evalList ws).length) :
    (evalList ws)[k] = evalS ws[k]! := by
  have hk' : k < ws.size := by simpa [evalList] using hk
  simp only [evalList, List.getElem_map, Array.getElem_toList]
  rw [getElem!_pos ws k hk']

theorem mem_evalList_iff {ws : Array (List ℤ)} {g : Equiv.Perm (Fin N)} :
    g ∈ evalList ws ↔ ∃ k < ws.size, evalS ws[k]! = g := by
  constructor
  · intro hg
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
    exact ⟨k, by simpa [evalList] using hk, (evalList_getElem hk).symm⟩
  · rintro ⟨k, hk, rfl⟩
    rw [← evalList_getElem (by simpa [evalList] using hk)]
    exact List.getElem_mem _

abbrev onSevenGen (ws : Array (List ℤ)) : Subgroup (Equiv.Perm (Fin N)) :=
  Subgroup.closure {g | g ∈ evalList ws}

theorem evalS_mem_onSevenGen {ws : Array (List ℤ)} {k : ℕ} (hk : k < ws.size) :
    evalS ws[k]! ∈ onSevenGen ws :=
  Subgroup.subset_closure (mem_evalList_iff.2 ⟨k, hk, rfl⟩)

theorem onSevenGen_le_Pv (ws : Array (List ℤ)) : onSevenGen ws ≤ Pv := closure_evalList_le ws

@[expose] def onSevenPts (R : Array ℕ) : List (Fin N) :=
  R.toList.map fun p => ⟨p % N, Nat.mod_lt _ (by norm_num)⟩

theorem onSevenPts_length (R : Array ℕ) : (onSevenPts R).length = R.size := by
  simp [onSevenPts]

section Points

variable {R : Array ℕ} (hR : pointsOK nPts R (posArr nPts R) = true)
include hR

theorem onSeven_pointsOK_spec {k : ℕ} (hk : k < R.size) :
    R[k]! < N ∧ (posArr nPts R)[R[k]!]! = k := by
  have h := hR
  simp only [pointsOK, Bool.and_eq_true] at h
  have := allBelowN_spec h.2 hk
  simpa [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using this

theorem onSevenPts_get {k : ℕ} (hk : k < (onSevenPts R).length) :
    (((onSevenPts R)[k] : Fin N) : ℕ) = R[k]! := by
  have hk' : k < R.size := by rw [onSevenPts_length] at hk; exact hk
  simp only [onSevenPts, List.getElem_map, Array.getElem_toList]
  rw [← getElem!_pos R k hk']
  exact Nat.mod_eq_of_lt (onSeven_pointsOK_spec hR hk').1

theorem onSevenPts_nodup : (onSevenPts R).Nodup := by
  rw [List.nodup_iff_injective_get]
  intro a b hab
  have h1 := congrArg (fun x : Fin N => (x : ℕ)) hab
  simp only [List.get_eq_getElem] at h1
  rw [onSevenPts_get hR, onSevenPts_get hR] at h1
  have ha : a.val < R.size := a.isLt.trans_eq (onSevenPts_length R)
  have hb : b.val < R.size := b.isLt.trans_eq (onSevenPts_length R)
  have : (posArr nPts R)[R[a.val]!]! = (posArr nPts R)[R[b.val]!]! := by rw [h1]
  rw [(onSeven_pointsOK_spec hR ha).2, (onSeven_pointsOK_spec hR hb).2] at this
  exact Fin.ext this

theorem onSeven_restrict_get {g : Array ℕ} {G : Equiv.Perm (Fin N)} (hg : PRep N g G)
    {t : Array ℕ} (h : restrictOK g R t = true) {k : ℕ} (hk : k < (onSevenPts R).length) :
    ∃ hk' : t[k]! < (onSevenPts R).length, G (onSevenPts R)[k] = (onSevenPts R)[t[k]!] := by
  have hk1 : k < R.size := by rwa [onSevenPts_length] at hk
  obtain ⟨ht, he⟩ := restrictOK_spec h hk1
  have ht' : t[k]! < (onSevenPts R).length := by rwa [onSevenPts_length]
  refine ⟨ht', Fin.ext ?_⟩
  rw [onSevenPts_get hR ht', he, ← onSevenPts_get hR hk]
  exact (hg _).symm

theorem onSeven_preserve_of_restrict {g : Array ℕ} {G : Equiv.Perm (Fin N)} (hg : PRep N g G)
    {t : Array ℕ} (h : restrictOK g R t = true) : ∀ p ∈ onSevenPts R, G • p ∈ onSevenPts R := by
  intro p hp
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
  obtain ⟨hk', he⟩ := onSeven_restrict_get hR hg h hk
  rw [Equiv.Perm.smul_def, he]
  exact List.getElem_mem hk'

end Points

structure ONSevenRes (R : Array ℕ) (ws : Array (List ℤ)) : Prop where
  pts : pointsOK nPts R (posArr nPts R) = true
  three : 3 ≤ R.size
  b0 : R[0]! = 0
  b1 : R[1]! = 227759
  b2 : R[2]! = 100817
  letters : ∀ k < ws.size, plettersOK 7 ws[k]! = true
  res : ∀ k < ws.size, restrictOK (onSevenArr ws[k]!) R (onSevenTab R (onSevenArr ws[k]!)) = true

@[expose] def onSevenTabsOf (R : Array ℕ) (ws : Array (List ℤ)) : Array (Array ℕ) :=
  (ws.map onSevenArr).map (onSevenTab R)

theorem onSevenTabsOf_size (R : Array ℕ) (ws : Array (List ℤ)) :
    (onSevenTabsOf R ws).size = ws.size := by
  simp [onSevenTabsOf]

theorem onSevenTabsOf_get {R : Array ℕ} {ws : Array (List ℤ)} {k : ℕ} (hk : k < ws.size) :
    (onSevenTabsOf R ws)[k]! = onSevenTab R (onSevenArr ws[k]!) := by
  rw [onSevenTabsOf, getElem!_map_onSeven _ _ (by simpa using hk),
    getElem!_map_onSeven _ _ hk]

namespace ONSevenRes

variable {R : Array ℕ} {ws : Array (List ℤ)} (hD : ONSevenRes R ws)
include hD

theorem prep_gen {k : ℕ} (hk : k < ws.size) : PRep N (onSevenArr ws[k]!) (evalS ws[k]!) :=
  prep_onSevenArr (hD.letters k hk)

theorem preserve : ∀ g ∈ onSevenGen ws, ∀ p ∈ onSevenPts R, g • p ∈ onSevenPts R := by
  apply listInvariant
  intro g hg
  obtain ⟨k, hk, rfl⟩ := mem_evalList_iff.1 hg
  exact onSeven_preserve_of_restrict hD.pts (hD.prep_gen hk) (hD.res k hk)

theorem nodup : (onSevenPts R).Nodup := onSevenPts_nodup hD.pts

omit hD in
@[expose] def rho (hD : ONSevenRes R ws) : onSevenGen ws →* Equiv.Perm (Fin R.size) :=
  (finCongr (onSevenPts_length R)).permCongrHom.toMonoidHom.comp
    (listRestrict (onSevenPts R) (onSevenGen ws) hD.preserve hD.nodup)

theorem rho_spec (g : onSevenGen ws) (k : Fin R.size) :
    (onSevenPts R).get (Fin.cast (onSevenPts_length R).symm (hD.rho g k)) =
      (g : Equiv.Perm (Fin N)) ((onSevenPts R).get (Fin.cast (onSevenPts_length R).symm k)) := by
  have := get_listRestrict (onSevenPts R) (onSevenGen ws) hD.preserve hD.nodup g
    (Fin.cast (onSevenPts_length R).symm k)
  rw [Equiv.Perm.smul_def] at this
  rw [← this]
  congr 1

theorem pts_cast_val (j : Fin R.size) :
    (((onSevenPts R).get (Fin.cast (onSevenPts_length R).symm j) : Fin N) : ℕ) = R[j.val]! := by
  rw [List.get_eq_getElem]
  exact onSevenPts_get hD.pts _

theorem prep_rho {g : Array ℕ} {G : onSevenGen ws} (hg : PRep N g (G : Equiv.Perm (Fin N)))
    {t : Array ℕ} (h : restrictOK g R t = true) : PRep R.size t (hD.rho G) := by
  intro k
  have hk : k.val < (onSevenPts R).length := by rw [onSevenPts_length]; exact k.isLt
  obtain ⟨hk', he⟩ := onSeven_restrict_get hD.pts hg h hk
  have hr := hD.rho_spec G k
  simp only [List.get_eq_getElem, Fin.val_cast] at hr
  rw [he] at hr
  exact ((List.Nodup.getElem_inj_iff hD.nodup).1 hr).symm

theorem eq_of_act {g h : Equiv.Perm (Fin N)} (hg : g ∈ Pv) (hh : h ∈ Pv)
    (hgh : ∀ j : Fin R.size, g ((onSevenPts R).get (Fin.cast (onSevenPts_length R).symm j)) =
      h ((onSevenPts R).get (Fin.cast (onSevenPts_length R).symm j))) : g = h := by
  have h3 := hD.three
  have e : ∀ (j : Fin R.size) (v : ℕ) (hv : v < N), R[j.val]! = v →
      (onSevenPts R).get (Fin.cast (onSevenPts_length R).symm j) = ⟨v, hv⟩ :=
    fun j v hv hj => Fin.ext (by rw [hD.pts_cast_val, hj])
  have k0 := hgh ⟨0, by omega⟩
  have k1 := hgh ⟨1, by omega⟩
  have k2 := hgh ⟨2, by omega⟩
  rw [e ⟨0, by omega⟩ 0 (by norm_num) hD.b0] at k0
  rw [e ⟨1, by omega⟩ 227759 (by norm_num) hD.b1] at k1
  rw [e ⟨2, by omega⟩ 100817 (by norm_num) hD.b2] at k2
  exact eq_of_three hg hh k0 k1 k2

theorem eq_of_rho_eq {g : onSevenGen ws} {h : Equiv.Perm (Fin N)} (hh : h ∈ Pv)
    (hgh : ∀ j : Fin R.size, (onSevenPts R).get (Fin.cast (onSevenPts_length R).symm
      (hD.rho g j)) = h ((onSevenPts R).get (Fin.cast (onSevenPts_length R).symm j))) :
    (g : Equiv.Perm (Fin N)) = h :=
  hD.eq_of_act (onSevenGen_le_Pv _ g.2) hh fun j => by rw [← hD.rho_spec g j, hgh j]

theorem rho_injective : Function.Injective hD.rho := by
  intro g h hgh
  apply Subtype.ext
  apply hD.eq_of_rho_eq (onSevenGen_le_Pv _ h.2)
  intro j
  rw [hgh, hD.rho_spec h j]

omit hD in
@[expose] def gen (ws : Array (List ℤ)) (k : ℕ) : onSevenGen ws :=
  if h : k < ws.size then ⟨evalS ws[k]!, evalS_mem_onSevenGen h⟩ else 1

omit hD in
theorem gen_val {k : ℕ} (hk : k < ws.size) :
    ((gen ws k : onSevenGen ws) : Equiv.Perm (Fin N)) = evalS ws[k]! := by
  rw [gen, dite_eq_left hk]

omit hD in
theorem top_eq :
    (⊤ : Subgroup (onSevenGen ws)) = Subgroup.closure (gen ws '' {k | k < ws.size}) := by
  symm
  rw [eq_top_iff]
  rintro ⟨g, hg⟩ -
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := mem_evalList_iff.1 hx
    exact Subgroup.subset_closure ⟨k, hk, Subtype.ext (gen_val hk)⟩
  | one => exact Subgroup.one_mem _
  | mul x y hx hy ihx ihy => exact Subgroup.mul_mem _ ihx ihy
  | inv x hx ihx => exact Subgroup.inv_mem _ ihx

theorem rep_tab {k : ℕ} (hk : k < ws.size) :
    CFSG.Monster.B.Co2.Rep R.size (onSevenTabsOf R ws)[k]! (hD.rho (gen ws k)) := by
  rw [onSevenTabsOf_get hk]
  apply hD.prep_rho (G := gen ws k) _ (hD.res k hk)
  rw [gen_val hk]
  exact hD.prep_gen hk

theorem rho_range : hD.rho.range = Subgroup.closure (permsA R.size (onSevenTabsOf R ws)) := by
  rw [MonoidHom.range_eq_map, top_eq, MonoidHom.map_closure, ← Set.image_comp]
  congr 1
  unfold permsA
  rw [onSevenTabsOf_size]
  apply Set.image_congr
  intro k hk
  exact (permOfArr_eq_of_rep (hD.rep_tab hk)).symm

section Cert

variable {c : ArrCert} (hc : enumOK R.size (onSevenTabsOf R ws) onSevenKeys c = true)
include hc

omit hc in
theorem keys_lt : ∀ p ∈ onSevenKeys, p < R.size := by
  intro p hp
  have := hD.three
  simp only [onSevenKeys, List.mem_cons, List.not_mem_nil, or_false] at hp
  omega

theorem card_eq : Nat.card (onSevenGen ws) = c.pts.size := by
  rw [Nat.card_congr (MonoidHom.ofInjective hD.rho_injective).toEquiv, hD.rho_range]
  exact (enumOK_spec (hD.keys_lt) hc).2.1

theorem exists_rep (g : onSevenGen ws) :
    ∃ i < c.pts.size, CFSG.Monster.B.Co2.Rep R.size c.pts[i]! (hD.rho g) := by
  have hm : hD.rho g ∈ Subgroup.closure (permsA R.size (onSevenTabsOf R ws)) := by
    rw [← hD.rho_range]; exact ⟨g, rfl⟩
  exact enumOK_exists_rep (hD.keys_lt) hc hm

theorem exists_of_pt {i : ℕ} (hi : i < c.pts.size) :
    ∃ g : onSevenGen ws, CFSG.Monster.B.Co2.Rep R.size c.pts[i]! (hD.rho g) := by
  obtain ⟨hmem, -, hval⟩ := enumOK_spec (hD.keys_lt) hc
  have h := (hmem (CFSG.Monster.B.Co2.permOfArr R.size c.pts[i]!)).2 ⟨i, hi, rfl⟩
  rw [← hD.rho_range] at h
  obtain ⟨g, hg⟩ := h
  refine ⟨g, ?_⟩
  rw [hg]
  exact rep_of_validA (hval i hi)

theorem exists_of_any {t : Array ℕ} (hany : c.pts.toList.any (eqA R.size t) = true) :
    ∃ g : onSevenGen ws, CFSG.Monster.B.Co2.Rep R.size t (hD.rho g) := by
  rw [List.any_eq_true] at hany
  obtain ⟨p, hp, he⟩ := hany
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  have hi' : i < c.pts.size := by simpa using hi
  rw [Array.getElem_toList, ← getElem!_pos c.pts i hi'] at he
  obtain ⟨g, hg⟩ := hD.exists_of_pt hc hi'
  exact ⟨g, rep_of_eqA hg (onSeven_eqA_comm he)⟩

theorem mem_of_any {x : Equiv.Perm (Fin N)} (hx : x ∈ Pv) {a t : Array ℕ} (ha : PRep N a x)
    (ht : restrictOK a R t = true) (hany : c.pts.toList.any (eqA R.size t) = true) :
    x ∈ onSevenGen ws := by
  obtain ⟨g, hgt⟩ := hD.exists_of_any hc hany
  have hxg : (g : Equiv.Perm (Fin N)) = x := by
    apply hD.eq_of_rho_eq hx
    intro j
    have hk : j.val < (onSevenPts R).length := by rw [onSevenPts_length]; exact j.isLt
    obtain ⟨hk', e1⟩ := onSeven_restrict_get hD.pts ha ht hk
    have e1' : x ((onSevenPts R).get (Fin.cast (onSevenPts_length R).symm j)) =
        (onSevenPts R)[t[j.val]!] := e1
    apply Fin.ext
    rw [hD.pts_cast_val, ← hgt j, e1', onSevenPts_get hD.pts]
  rw [← hxg]
  exact g.2

end Cert

theorem mem_of_rho_any {vs : Array (List ℤ)} (hE : ONSevenRes R vs) {c : ArrCert}
    (hc : enumOK R.size (onSevenTabsOf R vs) onSevenKeys c = true) {y : onSevenGen ws}
    {t : Array ℕ} (ht : CFSG.Monster.B.Co2.Rep R.size t (hD.rho y))
    (hany : c.pts.toList.any (eqA R.size t) = true) :
    (y : Equiv.Perm (Fin N)) ∈ onSevenGen vs := by
  obtain ⟨f, hf⟩ := hE.exists_of_any hc hany
  have heq : hE.rho f = hD.rho y := hf.unique ht
  have hfy : (f : Equiv.Perm (Fin N)) = y := by
    apply hE.eq_of_rho_eq (onSevenGen_le_Pv _ y.2)
    intro j
    rw [heq, hD.rho_spec y j]
  rw [← hfy]
  exact f.2

end ONSevenRes

theorem onSevenQF : CChainFacts nPts 2 qonStrongArrs Data.baseList.toArray Data.strongWords
    Data.baseList.toArray (Array.ofFn (n := Data.baseList.toArray.size) fun i => i.val) false 4 :=
  chainFacts qon_chain_cert.1

abbrev onSevenQpts (i k : ℕ) : Fin N := CArrays.levPts QON qonStrongArrs Data.baseList.toArray i k

abbrev onSevenQtr (i k : ℕ) : Equiv.Perm (Fin N) :=
  CArrays.levT QON qonStrongArrs Data.baseList.toArray i k

abbrev onSevenQsize (i : ℕ) : ℕ := (CArrays.lev nPts qonStrongArrs Data.baseList.toArray i).pts.size

theorem onSevenQsize_eq {i : ℕ} (hi : i < 29) :
    onSevenQsize i = ([245520, 52136, 36] ++ List.replicate 26 1)[i]'(by simpa using hi) := by
  have hi' : i < QON.baseCount := by rw [qon_baseCount]; exact hi
  have h := qon_point.2 ⟨i, hi'⟩
  rw [QON.orbitSize_eq_card, qon_card_orbit] at h
  exact h.symm

theorem onSevenQsize1 : onSevenQsize 1 = 52136 := by rw [onSevenQsize_eq (by norm_num)]; rfl

theorem onSevenQsize2 : onSevenQsize 2 = 36 := by rw [onSevenQsize_eq (by norm_num)]; rfl

theorem onSevenQtr_facts {i k : ℕ} (hi : i < QON.baseCount) (hk : k < onSevenQsize i) :
    onSevenQtr i k ∈ QON.levelSubgroup i ∧
      (∀ b ∈ QON.base.toList.take i, onSevenQtr i k b = b) ∧
      onSevenQtr i k (QON.base.get ⟨i, hi⟩) = onSevenQpts i k :=
  QON.transversal_sound ⟨i, hi⟩ _ _ (qon_arrays.transversal_of_lt onSevenQF hi hk)

theorem onSevenQpts_inj {i k k' : ℕ} (hi : i < QON.baseCount) (hk : k < onSevenQsize i)
    (hk' : k' < onSevenQsize i) (h : onSevenQpts i k = onSevenQpts i k') : k = k' := by
  have F := qon_arrays.levelFacts onSevenQF hi
  have h1 := congrArg Fin.val h
  rw [qon_arrays.levPts_val onSevenQF hi hk, qon_arrays.levPts_val onSevenQF hi hk'] at h1
  rw [← F.pos_pts k hk, ← F.pos_pts k' hk', h1]

theorem onSevenQbase0 : QON.base.get ⟨0, by rw [qon_baseCount]; norm_num⟩ = x0 :=
  Fin.ext (by rw [cert_on_schreier_action_data.2.2.2.2.2.2.2.2.1]; rfl)

theorem onSeven_mem_take_of {i j : ℕ} (hj : j < i) (hi : i ≤ QON.baseCount) :
    QON.base.get ⟨j, by omega⟩ ∈ QON.base.toList.take i := by
  rw [List.mem_take_iff_getElem]
  exact ⟨j, by simp; omega, by simp [Vector.get]⟩

@[expose] def onSevenPairT (k₁ k₂ : ℕ) : Equiv.Perm (Fin N) := onSevenQtr 1 k₁ * onSevenQtr 2 k₂

theorem onSevenPairT_mem {k₁ k₂ : ℕ} (h1 : k₁ < onSevenQsize 1) (h2 : k₂ < onSevenQsize 2) :
    onSevenPairT k₁ k₂ ∈ Pv ⊓ fixingSubgroup (Equiv.Perm (Fin N)) {x0} := by
  have hb1 : 1 < QON.baseCount := by rw [qon_baseCount]; norm_num
  have hb2 : 2 < QON.baseCount := by rw [qon_baseCount]; norm_num
  obtain ⟨hL1, hf1, -⟩ := onSevenQtr_facts hb1 h1
  obtain ⟨hL2, hf2, -⟩ := onSevenQtr_facts hb2 h2
  have hP := fun i => QON.levelSubgroup_le_originalSubgroup_of_point qon_point.1 i
  refine Subgroup.mem_inf.2 ⟨?_, (mem_fixingSubgroup_iff (Equiv.Perm (Fin N))).2 ?_⟩
  · rw [← qon_originalSubgroup]
    exact mul_mem (hP 1 hL1) (hP 2 hL2)
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [Equiv.Perm.smul_def, onSevenPairT, Equiv.Perm.mul_apply, ← onSevenQbase0,
      hf2 _ (onSeven_mem_take_of (by norm_num) (by rw [qon_baseCount]; norm_num)),
      hf1 _ (onSeven_mem_take_of (by norm_num) (by rw [qon_baseCount]; norm_num))]

theorem onSevenPairT_inj {k₁ k₂ k₁' k₂' : ℕ} (h1 : k₁ < onSevenQsize 1) (h2 : k₂ < onSevenQsize 2)
    (h1' : k₁' < onSevenQsize 1) (h2' : k₂' < onSevenQsize 2)
    (h : onSevenPairT k₁ k₂ = onSevenPairT k₁' k₂') : k₁ = k₁' ∧ k₂ = k₂' := by
  have hb1 : 1 < QON.baseCount := by rw [qon_baseCount]; norm_num
  have hb2 : 2 < QON.baseCount := by rw [qon_baseCount]; norm_num
  obtain ⟨-, -, he1⟩ := onSevenQtr_facts hb1 h1
  obtain ⟨-, -, he1'⟩ := onSevenQtr_facts hb1 h1'
  obtain ⟨-, hf2, he2⟩ := onSevenQtr_facts hb2 h2
  obtain ⟨-, hf2', he2'⟩ := onSevenQtr_facts hb2 h2'
  have hb : QON.base.get ⟨1, hb1⟩ ∈ QON.base.toList.take 2 :=
    onSeven_mem_take_of (by norm_num) (by rw [qon_baseCount]; norm_num)
  have e1 := DFunLike.congr_fun h (QON.base.get ⟨1, hb1⟩)
  rw [onSevenPairT, onSevenPairT, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hf2 _ hb,
    hf2' _ hb, he1, he1'] at e1
  have hk1 := onSevenQpts_inj hb1 h1 h1' e1
  subst hk1
  refine ⟨rfl, ?_⟩
  have e2 := DFunLike.congr_fun (mul_left_cancel (show onSevenQtr 1 k₁ * onSevenQtr 2 k₂ =
    onSevenQtr 1 k₁ * onSevenQtr 2 k₂' from h)) (QON.base.get ⟨2, hb2⟩)
  rw [he2, he2'] at e2
  exact onSevenQpts_inj hb2 h2 h2' e2

theorem exists_onSevenPairT {g : Equiv.Perm (Fin N)}
    (hg : g ∈ Pv ⊓ fixingSubgroup (Equiv.Perm (Fin N)) {x0}) :
    ∃ k₁ < onSevenQsize 1, ∃ k₂ < onSevenQsize 2, g = onSevenPairT k₁ k₂ := by
  obtain ⟨hgP, hgfix⟩ := Subgroup.mem_inf.1 hg
  have hg0 : g x0 = x0 := by
    have := (mem_fixingSubgroup_iff (Equiv.Perm (Fin N))).1 hgfix x0 rfl
    rwa [Equiv.Perm.smul_def] at this
  obtain ⟨⟨y, w⟩, hyw, -⟩ := PairDecomp.exists_unique_pair QON qon_three qon_valid qon_singleton
    (by rw [qon_originalSubgroup]; exact hgP) (by rw [qon_base_get_l0]; exact hg0)
  have hpts : ∀ (i : ℕ) (hi : i < QON.baseCount) (x : QON.orbitPoints ⟨i, hi⟩),
      ∃ k < onSevenQsize i, (x : Fin N) = onSevenQpts i k ∧
        QON.orbitTransversal ⟨i, hi⟩ x = onSevenQtr i k := by
    intro i hi x
    have h1 := (QON.orbitTransversal_spec ⟨i, hi⟩ x).1
    change (QON.orbitSearch ⟨i, hi⟩).transversal? x = _ at h1
    have h1' := h1
    rw [qon_arrays.orbitSearch_eq onSevenQF hi] at h1'
    change List.lookup (x : Fin N) ((List.range (onSevenQsize i)).map fun k =>
      (onSevenQpts i k, onSevenQtr i k)) = _ at h1'
    obtain ⟨before, after, heq, -⟩ := List.lookup_eq_some_iff.1 h1'
    have hmem : ((x : Fin N), QON.orbitTransversal ⟨i, hi⟩ x) ∈
        (List.range (onSevenQsize i)).map fun k => (onSevenQpts i k, onSevenQtr i k) := by
      rw [heq]
      simp
    simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at hmem
    obtain ⟨k, hk, hxk, htk⟩ := hmem
    exact ⟨k, hk, hxk.symm, htk.symm⟩
  obtain ⟨k₁, hk₁, -, ht₁⟩ := hpts 1 _ y
  obtain ⟨k₂, hk₂, -, ht₂⟩ := hpts 2 _ w
  refine ⟨k₁, hk₁, k₂, hk₂, ?_⟩
  rw [hyw, onSevenPairT]
  exact congrArg₂ (· * ·) ht₁ ht₂

theorem onSeven_tr2App_eq {k₁ k₂ : ℕ} (h1 : k₁ < onSevenQsize 1) (h2 : k₂ < onSevenQsize 2)
    {p : ℕ} (hp : p < N) :
    tr2App onSevenLevels onSevenSteps 1 2 k₁ k₂ p = (onSevenPairT k₁ k₂ ⟨p, hp⟩ : ℕ) := by
  have hb1 : 1 < QON.baseCount := by rw [qon_baseCount]; norm_num
  have hb2 : 2 < QON.baseCount := by rw [qon_baseCount]; norm_num
  unfold tr2App
  rw [qon_arrays.trApp_eq onSevenQF hb2 _ _ h2 h2 p hp,
    qon_arrays.trApp_eq onSevenQF hb1 _ _ h1 h1 _ (Fin.isLt _), onSevenPairT,
    Equiv.Perm.mul_apply]

theorem onSeven_eq_of_base_all {A B : Equiv.Perm (Fin N)} (hA : A ∈ Pv) (hB : B ∈ Pv)
    {f : ℕ → Bool} (hf : ∀ p (hp : p < N), f p = true ↔ A ⟨p, hp⟩ = B ⟨p, hp⟩) :
    onSevenBase.all f = true ↔ A = B := by
  rw [onSevenBase, Array.all_eq_true]
  constructor
  · intro h
    have e0 := (hf 0 (by norm_num)).1 (h 0 (by decide))
    have e1 := (hf 227759 (by norm_num)).1 (h 1 (by decide))
    have e2 := (hf 100817 (by norm_num)).1 (h 2 (by decide))
    exact eq_of_three hA hB e0 e1 e2
  · rintro rfl j hj
    have hj3 : j < 3 := by simpa using hj
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
    · exact (hf 0 (by norm_num)).2 rfl
    · exact (hf 227759 (by norm_num)).2 rfl
    · exact (hf 100817 (by norm_num)).2 rfl

abbrev onSevenTestF (x : Array ℕ) (k₁ k₂ : ℕ) : Bool :=
  onSevenBase.all fun p => tr2App onSevenLevels onSevenSteps 1 2 k₁ k₂ x[p]! ==
    x[tr2App onSevenLevels onSevenSteps 1 2 k₁ k₂ p]!

section Count

variable {x : Array ℕ} {X : Equiv.Perm (Fin N)} (hx : PRep N x X) (hX : X ∈ Pv)
include hx hX

theorem onSevenTestF_iff {k₁ k₂ : ℕ} (h1 : k₁ < onSevenQsize 1) (h2 : k₂ < onSevenQsize 2) :
    onSevenTestF x k₁ k₂ = true ↔ onSevenPairT k₁ k₂ * X = X * onSevenPairT k₁ k₂ := by
  have hP : onSevenPairT k₁ k₂ ∈ Pv := (Subgroup.mem_inf.1 (onSevenPairT_mem h1 h2)).1
  apply onSeven_eq_of_base_all (mul_mem hP hX) (mul_mem hX hP)
  intro p hp
  rw [beq_iff_eq, hx.apply hp, onSeven_tr2App_eq h1 h2 (Fin.isLt _), onSeven_tr2App_eq h1 h2 hp,
    hx.apply (Fin.isLt _), Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Fin.ext_iff]

theorem onSevenCosetTest_iff {u : Array ℕ} {U : Equiv.Perm (Fin N)} (hu : PRep N u U)
    (hU : U ∈ Pv) {k₁ k₂ : ℕ} (h1 : k₁ < onSevenQsize 1) (h2 : k₂ < onSevenQsize 2) :
    onSevenCosetTestAt onSevenLevels onSevenSteps u x k₁ k₂ = true ↔
      U * onSevenPairT k₁ k₂ * X = X * (U * onSevenPairT k₁ k₂) := by
  have hP : onSevenPairT k₁ k₂ ∈ Pv := (Subgroup.mem_inf.1 (onSevenPairT_mem h1 h2)).1
  apply onSeven_eq_of_base_all (mul_mem (mul_mem hU hP) hX) (mul_mem hX (mul_mem hU hP))
  intro p hp
  rw [beq_iff_eq, hx.apply hp, onSeven_tr2App_eq h1 h2 (Fin.isLt _), hu.apply (Fin.isLt _),
    onSeven_tr2App_eq h1 h2 hp, hu.apply (Fin.isLt _), hx.apply (Fin.isLt _),
    Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    Fin.ext_iff]

end Count

theorem onSeven_list_sum_range (m : ℕ) (f : ℕ → ℕ) :
    ((List.range m).map f).sum = ∑ a ∈ Finset.range m, f a := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem onSeven_sum_filter_length (m₁ m₂ : ℕ) (p : ℕ → ℕ → Bool) :
    ((List.range m₁).map fun a => ((List.range m₂).filter (p a)).length).sum =
      ((Finset.range m₁ ×ˢ Finset.range m₂).filter fun x => p x.1 x.2 = true).card := by
  rw [onSeven_list_sum_range, Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.card_filter]
  exact countBelowN_eq m₂ (p a)

abbrev onSevenPassing (x : Array ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (onSevenQsize 1) ×ˢ Finset.range (onSevenQsize 2)).filter
    fun y => onSevenTestF x y.1 y.2 = true

theorem card_onSevenPassing (x : Array ℕ) : (onSevenPassing x).card = onSevenCount x := by
  rw [onSevenCount, commCount, ← onSeven_sum_filter_length]

theorem card_centralizer_P0 {x : Array ℕ} {X : Equiv.Perm (Fin N)} (hx : PRep N x X)
    (hX : X ∈ Pv) :
    Nat.card (Subgroup.centralizer {X} ⊓ (Pv ⊓ fixingSubgroup (Equiv.Perm (Fin N)) {x0}) :
      Subgroup (Equiv.Perm (Fin N))) = onSevenCount x := by
  rw [← card_onSevenPassing, ← Nat.card_eq_finsetCard]
  symm
  refine Nat.card_eq_of_bijective (fun y => ⟨onSevenPairT y.1.1 y.1.2, ?_⟩) ⟨?_, ?_⟩
  · obtain ⟨⟨a, b⟩, hab⟩ := y
    simp only [onSevenPassing, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hab
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2
      ((onSevenTestF_iff hx hX hab.1.1 hab.1.2).1 hab.2), onSevenPairT_mem hab.1.1 hab.1.2⟩
  · rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨c, d⟩, hcd⟩ h
    simp only [onSevenPassing, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hab hcd
    have := onSevenPairT_inj hab.1.1 hab.1.2 hcd.1.1 hcd.1.2 (congrArg Subtype.val h)
    simp only [this.1, this.2]
  · rintro ⟨g, hg⟩
    obtain ⟨hgc, hg0⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := exists_onSevenPairT hg0
    refine ⟨⟨(k₁, k₂), ?_⟩, rfl⟩
    simp only [onSevenPassing, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨hk₁, hk₂⟩, (onSevenTestF_iff hx hX hk₁ hk₂).2
      (Subgroup.mem_centralizer_singleton_iff.1 hgc)⟩

@[expose] def onSevenPt (q : ℕ) : Fin N := ⟨q % N, Nat.mod_lt _ (by norm_num)⟩

theorem stabilizer_x0_eq :
    MulAction.stabilizer (Equiv.Perm (Fin N)) x0 = fixingSubgroup (Equiv.Perm (Fin N)) {x0} := by
  ext g
  rw [MulAction.mem_stabilizer_iff, mem_fixingSubgroup_iff]
  simp

theorem card_centralizer_le_of_good {x : Array ℕ} {X : Equiv.Perm (Fin N)} (hx : PRep N x X)
    (hX : X ∈ Pv) (hx0 : X x0 = x0) {bad : List ℕ}
    (hbad : ∀ q ∈ bad, ∀ g ∈ Pv, g * X = X * g → ((g x0 : Fin N) : ℕ) ≠ q) :
    Nat.card (Subgroup.centralizer {X} ⊓ Pv : Subgroup (Equiv.Perm (Fin N))) ≤
      (onSevenGood x bad).length * onSevenCount x := by
  set K := (Subgroup.centralizer {X} ⊓ Pv : Subgroup (Equiv.Perm (Fin N)))
  have hL : ∀ g ∈ K, g • x0 ∈ (onSevenGood x bad).map onSevenPt := by
    intro g hg
    obtain ⟨hgc, hgP⟩ := Subgroup.mem_inf.1 hg
    have hcomm : g * X = X * g := Subgroup.mem_centralizer_singleton_iff.1 hgc
    have hfix : X (g x0) = g x0 := by
      have := DFunLike.congr_fun hcomm x0
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hx0] at this
      exact this.symm
    rw [List.mem_map]
    refine ⟨((g x0 : Fin N) : ℕ), ?_, ?_⟩
    · rw [onSevenGood, List.mem_filter, List.mem_range]
      refine ⟨(g x0).isLt, ?_⟩
      have hnot : ((g x0 : Fin N) : ℕ) ∉ bad := fun hm => hbad _ hm g hgP hcomm rfl
      rw [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true']
      exact ⟨by rw [hx (g x0), hfix], by simpa using hnot⟩
    · exact Fin.ext (Nat.mod_eq_of_lt (g x0).isLt)
  have h := card_le_of_orbit_subset K x0 _ hL
  rw [List.length_map] at h
  have hstab : (K ⊓ MulAction.stabilizer (Equiv.Perm (Fin N)) x0 : Subgroup _) =
      Subgroup.centralizer {X} ⊓ (Pv ⊓ fixingSubgroup (Equiv.Perm (Fin N)) {x0}) := by
    rw [stabilizer_x0_eq, inf_assoc]
  rw [hstab, card_centralizer_P0 hx hX] at h
  exact h

theorem ne_of_count_ne {x y : Array ℕ} {X U : Equiv.Perm (Fin N)} (hx : PRep N x X)
    (hX : X ∈ Pv) (hU : U ∈ Pv) (hy : PRep N y (U⁻¹ * X * U))
    (hne : onSevenCount y ≠ onSevenCount x) :
    ∀ g ∈ Pv, g * X = X * g → g x0 ≠ U x0 := by
  intro g hg hcomm hgu
  have hr : U⁻¹ * g ∈ Pv ⊓ fixingSubgroup (Equiv.Perm (Fin N)) {x0} := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hU) hg,
      (mem_fixingSubgroup_iff (Equiv.Perm (Fin N))).2 fun z hz => ?_⟩
    rw [Set.mem_singleton_iff] at hz
    subst hz
    rw [Equiv.Perm.smul_def, Equiv.Perm.mul_apply, hgu]
    simp
  have hconj : U⁻¹ * g * X * (U⁻¹ * g)⁻¹ = U⁻¹ * X * U :=
    calc U⁻¹ * g * X * (U⁻¹ * g)⁻¹ = U⁻¹ * (g * X) * g⁻¹ * U := by group
      _ = U⁻¹ * (X * g) * g⁻¹ * U := by rw [hcomm]
      _ = U⁻¹ * X * U := by group
  have hc := card_centralizer_inf_conj (Pv ⊓ fixingSubgroup (Equiv.Perm (Fin N)) {x0}) hr hconj
  rw [card_centralizer_P0 hx hX,
    card_centralizer_P0 hy (mul_mem (mul_mem (inv_mem hU) hX) hU)] at hc
  exact hne hc.symm

theorem ne_of_cosetFree {x u : Array ℕ} {X U : Equiv.Perm (Fin N)} (hx : PRep N x X)
    (hX : X ∈ Pv) (hu : PRep N u U) (hU : U ∈ Pv) (hfree : onSevenCosetFree u x = true) :
    ∀ g ∈ Pv, g * X = X * g → g x0 ≠ U x0 := by
  intro g hg hcomm hgu
  have hr : U⁻¹ * g ∈ Pv ⊓ fixingSubgroup (Equiv.Perm (Fin N)) {x0} := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hU) hg,
      (mem_fixingSubgroup_iff (Equiv.Perm (Fin N))).2 fun z hz => ?_⟩
    rw [Set.mem_singleton_iff] at hz
    subst hz
    rw [Equiv.Perm.smul_def, Equiv.Perm.mul_apply, hgu]
    simp
  obtain ⟨k₁, hk₁, k₂, hk₂, hk⟩ := exists_onSevenPairT hr
  have hg' : g = U * onSevenPairT k₁ k₂ := by rw [← hk]; group
  have ht := (onSevenCosetTest_iff hx hX hu hU hk₁ hk₂).2 (by rw [← hg']; exact hcomm)
  rw [onSevenQsize1] at hk₁
  rw [onSevenQsize2] at hk₂
  have h := allBelowN_spec (allBelowN_spec hfree hk₁) hk₂
  simp [ht] at h

end CFSG.RankThree.Native
