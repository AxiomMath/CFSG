module

public import CFSG.Monster.B.E6.StdF4RadicalWords

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4Radical

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Overlap CFSG.Monster.B.E6.StdF4
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension

@[expose] def groupJ :
    Subgroup (ModGL Tag.E6 K) where
  carrier := {g | g ∈ stdGroup ∧ betaGL g = g}
  mul_mem' {a b} ha hb := ⟨mul_mem ha.1 hb.1, by rw [map_mul, ha.2, hb.2]⟩
  one_mem' := ⟨one_mem _, map_one _⟩
  inv_mem' {a} ha := ⟨inv_mem ha.1, by rw [map_inv, ha.2]⟩

theorem mem_groupJ
    {g : ModGL Tag.E6 K} : g ∈ groupJ ↔ g ∈ stdGroup ∧ betaGL g = g := Iff.rfl

theorem mem_groupJ_iff_betaG
    (g : stdGroup) : (g : ModGL Tag.E6 K) ∈ groupJ ↔ betaG g = g := by
  rw [mem_groupJ]
  exact ⟨fun h => Subtype.ext h.2, fun h => ⟨g.2, congrArg Subtype.val h⟩⟩

theorem groupJ_le_stdGroup :
    groupJ ≤ stdGroup := fun _ h => h.1

abbrev betaStarElt :
    GStar := SemidirectProduct.inr ⟨betaG, Subgroup.mem_zpowers _⟩

theorem mem_groupJ_iff_commute
    (g : stdGroup) :
    (g : ModGL Tag.E6 K) ∈ groupJ ↔ Commute (SemidirectProduct.inl g : GStar) betaStarElt := by
  rw [mem_groupJ_iff_betaG]
  have h := SemidirectProduct.inl_aut (φ := betaGroup.subtype)
    (⟨betaG, Subgroup.mem_zpowers _⟩ : betaGroup) g
  rw [map_inv] at h
  change SemidirectProduct.inl (betaG g) = betaStarElt * SemidirectProduct.inl g * betaStarElt⁻¹
    at h
  constructor
  · intro hb
    rw [hb] at h
    change SemidirectProduct.inl g * betaStarElt = betaStarElt * SemidirectProduct.inl g
    calc SemidirectProduct.inl g * betaStarElt =
        (betaStarElt * SemidirectProduct.inl g * betaStarElt⁻¹) * betaStarElt := by rw [← h]
      _ = betaStarElt * SemidirectProduct.inl g := by group
  · intro hc
    refine SemidirectProduct.inl_injective (φ := betaGroup.subtype) ?_
    rw [h, ← hc.eq, mul_inv_cancel_right]

theorem betaGL_X1
    (a : Fin Tag.E6.rank → ℤ) : betaGL (X1 a) = X1 a :=
  Units.ext (by rw [betaGL_apply, entrywise_pinnedX, map_one])

theorem X1_mem_posUnipotent
    {a : Fin Tag.E6.rank → ℤ} (ha : IsRoot Tag.E6 a)
    (h : 0 < height a) : X1 a ∈ posUnipotent Tag.E6 K :=
  Subgroup.mem_iSup_of_mem a (Subgroup.mem_iSup_of_mem ⟨ha, h⟩
    (Subgroup.subset_closure ⟨1, rfl⟩))

theorem X1_mem_negUnipotent
    {a : Fin Tag.E6.rank → ℤ} (ha : IsRoot Tag.E6 a)
    (h : height a < 0) : X1 a ∈ negUnipotent Tag.E6 K :=
  Subgroup.mem_iSup_of_mem a (Subgroup.mem_iSup_of_mem ⟨ha, h⟩
    (Subgroup.subset_closure ⟨1, rfl⟩))

abbrev Fhom : ModGL Tag.E6 K →* ModGL Tag.E6 K := twistHom TwistTag.E6 K barHom

theorem twistHom_X1
    {a : Fin Tag.E6.rank → ℤ} (ha : IsRoot Tag.E6 a) :
    Fhom (X1 a) = X1 (permLattice (τ := Tag.E6) TwistTag.E6.perm a) := by
  have h1 : Fhom (X1 a) = diagE6GL * betaGL (X1 a) * diagE6GL⁻¹ := twistHom_eq_conj _
  rw [h1, betaGL_X1, ← C2E6Std.twistHom_id_eq]
  exact twistHom_id_pinnedX (t := TwistTag.E6) StdF4.two_eq_zero_K ha 1

theorem mem_groupJ_of_twistHom
    {g : ModGL Tag.E6 K}
    (hU : g ∈ posUnipotent Tag.E6 K ∨ g ∈ negUnipotent Tag.E6 K) (hΓ : g ∈ adjointGroup Tag.E6 K)
    (hF : Fhom g = g) (hβ : betaGL g = g) : g ∈ groupJ := by
  refine ⟨?_, hβ⟩
  have hfix : g ∈ twistedFixedGroup TwistTag.E6 K barHom :=
    (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K barHom).2 ⟨hΓ, hF⟩
  rcases hU with hU | hU
  · exact graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _ ⟨hU, hfix⟩
  · exact graphFixedNegUnipotent_le_graphFixedRootGroup _ _ _ ⟨hU, hfix⟩

@[expose] def rhoIdx (k : ℕ) : ℕ :=
  [0, 1, 3, 2, 5, 4, 6, 8, 7, 9, 11, 10, 13, 12, 14, 15, 17, 16, 18, 19, 20].getD k 0

theorem permLattice_rr {k : ℕ} (hk : k < 21) :
    permLattice (τ := Tag.E6) TwistTag.E6.perm (rr k) = rr (rhoIdx k) := by
  have h : (List.range 21).all (fun k =>
      List.ofFn (permLattice (τ := Tag.E6) TwistTag.E6.perm (rr k)) ==
        List.ofFn (rr (rhoIdx k))) = true := by
    decide +kernel
  simp only [List.all_eq_true, List.mem_range] at h
  exact RootCertificate.eq_of_ofFn_beq (h k hk)

theorem rhoIdx_lt {k : ℕ} (hk : k < 21) : rhoIdx k < 21 := by
  have h : (List.range 21).all (fun k => decide (rhoIdx k < 21)) = true := by decide +kernel
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h k hk

theorem twistHom_xr
    {k : ℕ} (hk : k < 21) : Fhom (xr k) = xr (rhoIdx k) := by
  rw [xr, twistHom_X1 (isRoot_rr hk), permLattice_rr hk]
  rfl

theorem twistHom_evalW
    (w : List ℕ) (hw : ∀ k ∈ w, k < 21) :
    Fhom (evalW w) = evalW (w.map rhoIdx) := by
  rw [evalW, map_list_prod, List.map_map, evalW, List.map_map]
  congr 1
  exact List.map_congr_left fun k hk => twistHom_xr (hw k hk)

theorem betaGL_evalW
    (w : List ℕ) : betaGL (evalW w) = evalW w := by
  rw [evalW, map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun k _ => betaGL_X1 _

theorem evalW_mem_adjointGroup
    (w : List ℕ) : evalW w ∈ adjointGroup Tag.E6 K :=
  list_prod_mem fun g hg => by
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hg
    exact pinnedX_mem_adjointGroup _ _

theorem evalW_mem_posUnipotent
    (w : List ℕ) (hw : ∀ k ∈ w, k < 21) :
    evalW w ∈ posUnipotent Tag.E6 K :=
  list_prod_mem fun g hg => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hg
    exact X1_mem_posUnipotent (isRoot_rr (hw k hk)) (height_rr_pos (hw k hk))

theorem rhoCheck : (List.range 15).all (fun i =>
    nfWM ((orbIdx i).map rhoIdx) == nfWM (orbIdx i)) = true := by decide +kernel

theorem orbIdx_map_rhoIdx_lt {i : ℕ} (hi : i < 15) : ∀ k ∈ (orbIdx i).map rhoIdx, k < 21 := by
  intro k hk
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hk
  exact rhoIdx_lt (orbIdx_lt hi l hl)

theorem twistHom_qr
    {i : ℕ} (hi : i < 15) : Fhom (qr i) = qr i := by
  have h := rhoCheck
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  rw [qr, twistHom_evalW _ (orbIdx_lt hi)]
  exact evalW_eq_of_nfWM_eq (orbIdx_map_rhoIdx_lt hi) (orbIdx_lt hi) (h i hi)

theorem qr_mem_groupJ
    {i : ℕ} (hi : i < 15) : qr i ∈ groupJ :=
  mem_groupJ_of_twistHom (Or.inl (evalW_mem_posUnipotent _ (orbIdx_lt hi)))
    (evalW_mem_adjointGroup _) (twistHom_qr hi) (betaGL_evalW _)

end CFSG.Monster.B.E6.StdF4Radical

namespace CFSG.Monster.B.E6.StdF4Radical

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Overlap CFSG.Monster.B.E6.StdF4
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open scoped commutatorElement

abbrev rho (a : Fin Tag.E6.rank → ℤ) : Fin Tag.E6.rank → ℤ :=
  permLattice (τ := Tag.E6) TwistTag.E6.perm a

@[expose] def orbitProd
    (a : Fin Tag.E6.rank → ℤ) : ModGL Tag.E6 K :=
  if rho a = a then X1 a else X1 a * X1 (rho a)

@[expose] def radicalQ :
    Subgroup (ModGL Tag.E6 K) :=
  Subgroup.closure {g | ∃ a : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 a ∧ 0 < height a ∧ 0 < a 1 ∧
    g = orbitProd a}

@[expose] def orbOf (k : ℕ) : ℕ :=
  [0, 1, 2, 2, 3, 3, 4, 5, 5, 6, 7, 7, 8, 8, 9, 10, 11, 11, 12, 13, 14].getD k 0

theorem orbOfCheck : (List.range 21).all (fun k => decide (orbOf k < 15)) = true := by
  decide +kernel

theorem fixCheck : (List.range 21).all (fun k => rhoIdx k != k || orbIdx (orbOf k) == [k]) =
    true := by decide +kernel

theorem pairCheck : (List.range 21).all (fun k => rhoIdx k == k ||
    nfWM [k, rhoIdx k] == nfWM (orbIdx (orbOf k))) = true := by decide +kernel

theorem headCheck : (List.range 15).all (fun i => decide ((orbIdx i).headD 0 < 21) &&
    orbOf ((orbIdx i).headD 0) == i) = true := by decide +kernel

theorem orbOf_lt {k : ℕ} (hk : k < 21) : orbOf k < 15 := by
  have h := orbOfCheck
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h k hk

theorem orbitProd_rr
    {k : ℕ} (hk : k < 21) : orbitProd (rr k) = qr (orbOf k) := by
  rw [orbitProd, rho, permLattice_rr hk]
  by_cases hr : rhoIdx k = k
  · have h := fixCheck
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq,
      beq_iff_eq] at h
    have hk' := (h k hk).resolve_left (not_not.2 hr)
    rw [hr, ite_eq_left rfl, qr, hk', evalW_singleton]
    rfl
  · have h := pairCheck
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at h
    have hk' := (h k hk).resolve_left hr
    have hne : rr (rhoIdx k) ≠ rr k := fun e => hr (rr_injOn (rhoIdx_lt hk) hk e)
    rw [ite_eq_right hne]
    have hw : ∀ j ∈ [k, rhoIdx k], j < 21 := by
      intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      exacts [hk, rhoIdx_lt hk]
    rw [qr, ← evalW_eq_of_nfWM_eq hw (orbIdx_lt (orbOf_lt hk)) hk']
    simp [evalW, xr]

theorem exists_orbOf_eq {i : ℕ} (hi : i < 15) : ∃ k < 21, orbOf k = i := by
  have h := headCheck
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  exact ⟨_, (h i hi).1, (h i hi).2⟩

@[expose] def qset :
    Set (ModGL Tag.E6 K) := {g | ∃ i < 15, g = qr i}

theorem radicalQ_eq_closure :
    radicalQ = Subgroup.closure qset := by
  rw [radicalQ]
  congr 1
  ext g
  constructor
  · rintro ⟨a, ha, -, h1, rfl⟩
    obtain ⟨k, hk, rfl⟩ := exists_rr_eq ha h1
    exact ⟨orbOf k, orbOf_lt hk, orbitProd_rr hk⟩
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨k, hk, rfl⟩ := exists_orbOf_eq hi
    exact ⟨rr k, isRoot_rr hk, height_rr_pos hk, rr_one_pos hk, (orbitProd_rr hk).symm⟩

theorem qr_mem_radicalQ
    {i : ℕ} (hi : i < 15) : qr i ∈ radicalQ := by
  rw [radicalQ_eq_closure]
  exact Subgroup.subset_closure ⟨i, hi, rfl⟩

theorem radicalQ_le_groupJ :
    radicalQ ≤ groupJ := by
  rw [radicalQ_eq_closure, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact qr_mem_groupJ hi

@[expose] def nfQ
    (u : ℕ → Bool) : ModGL Tag.E6 K := lprod qr (List.range 15) u

@[expose] def stepQ (u : ℕ → Bool) (j : ℕ) : ℕ → Bool :=
  if parAfter bC (List.range 15) u j then
    Function.update (Function.update u j (!u j)) 14 (!(Function.update u j (!u j)) 14)
  else Function.update u j (!u j)

theorem mem_range_15 {j : ℕ} (hj : j < 15) : j ∈ List.range 15 := List.mem_range.2 hj

theorem nfQ_mul_qr
    (u : ℕ → Bool) {j : ℕ} (hj : j < 15) : nfQ u * qr j = nfQ (stepQ u j) := by
  have hsub : ∀ i ∈ List.range 15, i ∈ List.range 15 := fun i hi => hi
  rw [nfQ, lprod_mul_x_of_mem rels_qr (mem_range_15 hj) _ List.nodup_range (mem_range_15 hj) hsub,
    stepQ]
  split_ifs with hp
  · rw [hp, zb_true, ← qr_fourteen,
      lprod_mul_x_of_mem rels_qr (mem_range_15 (by norm_num)) _ List.nodup_range
        (mem_range_15 (by norm_num)) hsub]
    have h14 : parAfter bC (List.range 15) (Function.update u j (!u j)) 14 = false := by
      rw [List.range_succ]
      exact parAfter_append_singleton _ (by simp)
    rw [h14, zb_false, mul_one, nfQ]
  · rw [Bool.not_eq_true] at hp
    rw [hp, zb_false, mul_one, nfQ]

theorem nfQ_false :
    nfQ (fun _ => false) = 1 := by
  simp only [nfQ, lprod, Bool.false_eq_true, ite_false]
  exact List.prod_eq_one fun x hx => by
    obtain ⟨_, _, rfl⟩ := List.mem_map.1 hx
    rfl

theorem nfQ_mem_radicalQ
    (u : ℕ → Bool) : nfQ u ∈ radicalQ :=
  list_prod_mem fun g hg => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
    split_ifs
    · exact qr_mem_radicalQ (List.mem_range.1 hi)
    · exact one_mem _

theorem qr_inv
    {i : ℕ} (hi : i < 15) : (qr i)⁻¹ = qr i :=
  inv_eq_of_mul_eq_one_left (qr_mul_self hi)

theorem mem_radicalQ_iff
    {g : ModGL Tag.E6 K} : g ∈ radicalQ ↔ ∃ u, g = nfQ u := by
  constructor
  · intro hg
    rw [radicalQ_eq_closure] at hg
    induction hg using Subgroup.closure_induction_right with
    | one => exact ⟨fun _ => false, nfQ_false.symm⟩
    | mul_right x _ y hy ih =>
      obtain ⟨u, rfl⟩ := ih
      obtain ⟨j, hj, rfl⟩ := hy
      exact ⟨stepQ u j, nfQ_mul_qr u hj⟩
    | mul_inv_cancel x _ y hy ih =>
      obtain ⟨u, rfl⟩ := ih
      obtain ⟨j, hj, rfl⟩ := hy
      exact ⟨stepQ u j, by rw [qr_inv hj, nfQ_mul_qr u hj]⟩
  · rintro ⟨u, rfl⟩
    exact nfQ_mem_radicalQ u

theorem prod_map_flatMap {α β M : Type*} [Monoid M] (L : List α) (f : α → List β) (g : β → M) :
    ((L.flatMap f).map g).prod = (L.map fun a => ((f a).map g).prod).prod := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, List.map_append, List.prod_append, ih]

@[expose] def orbOfV (a : Fin Tag.E6.rank → ℤ) : ℕ := orbOf (radRootList.idxOf a)

theorem idxCheck : (List.range 21).all (fun k => radRootList.idxOf (rr k) == k) = true := by
  decide +kernel

theorem orbOfV_rr {k : ℕ} (hk : k < 21) : orbOfV (rr k) = orbOf k := by
  have h := idxCheck
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  rw [orbOfV, h k hk]

theorem memOrbCheck : (List.range 15).all (fun i => (orbIdx i).all fun k => orbOf k == i) =
    true := by decide +kernel

theorem orbOf_of_mem {i : ℕ} (hi : i < 15) {k : ℕ} (hk : k ∈ orbIdx i) : orbOf k = i := by
  have h := memOrbCheck
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h i hi k hk

theorem qr_eq_prod
    (i : ℕ) : qr i = ((orbIdx i).map fun k => pinnedX Tag.E6 K (rr k) 1).prod :=
  rfl

theorem factor_eq
    (u : ℕ → Bool) {i : ℕ} (hi : i < 15) : (if u i then qr i else 1) =
    ((orbIdx i).map fun k => pinnedX Tag.E6 K (rr k) (if u (orbOf k) then 1 else 0)).prod := by
  have e : ((orbIdx i).map fun k => pinnedX Tag.E6 K (rr k) (if u (orbOf k) then 1 else 0)) =
      (orbIdx i).map fun k => pinnedX Tag.E6 K (rr k) (if u i then 1 else 0) :=
    List.map_congr_left fun k hk => by rw [orbOf_of_mem hi hk]
  rw [e]
  cases u i
  · simp only [Bool.false_eq_true, ite_false, pinnedX_zero]
    exact (List.prod_eq_one fun x hx => by
      obtain ⟨_, _, rfl⟩ := List.mem_map.1 hx
      rfl).symm
  · simp only [ite_true]
    exact qr_eq_prod i

theorem nfQ_eq_prod (u : ℕ → Bool) :
    nfQ u = (radRootList.map fun a => pinnedX Tag.E6 K a (if u (orbOfV a) then 1 else 0)).prod := by
  have h1 : ((List.range 15).map fun i => if u i then qr i else 1) =
      (List.range 15).map fun i =>
        ((orbIdx i).map fun k => pinnedX Tag.E6 K (rr k) (if u (orbOf k) then 1 else 0)).prod :=
    List.map_congr_left fun i hi => factor_eq u (List.mem_range.1 hi)
  have h2 : (radRootList.map fun a => pinnedX Tag.E6 K a (if u (orbOfV a) then 1 else 0)) =
      (List.range 21).map fun k => pinnedX Tag.E6 K (rr k) (if u (orbOf k) then 1 else 0) := by
    rw [radRootList_eq, List.map_map]
    exact List.map_congr_left fun k hk => by
      simp only [Function.comp_apply, orbOfV_rr (List.mem_range.1 hk)]
  rw [nfQ, lprod, h1, h2, ← range_flatMap_orbIdx, prod_map_flatMap]

theorem radRoot_pos :
    ∀ a ∈ radRootList, IsRoot Tag.E6 a ∧ 0 < height a := fun a ha => by
  have := mem_radRootList_iff.1 ha
  exact ⟨this.1, this.2.1⟩

theorem nfQ_inj
    {u u' : ℕ → Bool} (h : nfQ u = nfQ u') : ∀ i < 15, u i = u' i := by
  rw [nfQ_eq_prod, nfQ_eq_prod] at h
  have hc := pinnedX_list_prod_injective radRootList radRootList_nodup radRoot_pos _ _ h
  intro i hi
  obtain ⟨k, hk, rfl⟩ := exists_orbOf_eq hi
  have hmem : rr k ∈ radRootList := by
    rw [radRootList_eq]
    exact List.mem_map_of_mem (List.mem_range.2 hk)
  have := hc (rr k) hmem
  rw [orbOfV_rr hk] at this
  cases hu : u (orbOf k) <;> cases hu' : u' (orbOf k) <;> rw [hu, hu'] at this <;>
    simp_all

theorem card_radicalQ :
    Nat.card radicalQ = 2 ^ 15 := by
  let f : (Fin 15 → Bool) → radicalQ := fun v =>
    ⟨nfQ fun i => if h : i < 15 then v ⟨i, h⟩ else false, nfQ_mem_radicalQ _⟩
  have hf : Function.Bijective f := by
    constructor
    · intro v v' h
      have := nfQ_inj (u := fun i => if h : i < 15 then v ⟨i, h⟩ else false)
        (u' := fun i => if h : i < 15 then v' ⟨i, h⟩ else false) (congrArg Subtype.val h)
      funext i
      have := this i i.2
      simpa using this
    · rintro ⟨g, hg⟩
      obtain ⟨u, rfl⟩ := mem_radicalQ_iff.1 hg
      refine ⟨fun i => u i, Subtype.ext ?_⟩
      exact lprod_congr fun i hi => by simp [List.mem_range.1 hi]
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_fun]
  simp

@[expose] def radicalZ :
    Subgroup (ModGL Tag.E6 K) :=
  (Subgroup.center radicalQ).map radicalQ.subtype

theorem mem_radicalZ_iff'
    {g : ModGL Tag.E6 K} :
    g ∈ radicalZ ↔ g ∈ radicalQ ∧ ∀ h ∈ radicalQ, h * g = g * h := by
  rw [radicalZ, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, fun h hh => ?_⟩
    have := Subgroup.mem_center_iff.1 hx ⟨h, hh⟩
    exact congrArg Subtype.val this
  · rintro ⟨hg, hc⟩
    refine ⟨⟨g, hg⟩, Subgroup.mem_center_iff.2 fun h => Subtype.ext (hc h h.2), rfl⟩

theorem radicalZ_le_radicalQ :
    radicalZ ≤ radicalQ := fun _ h => (mem_radicalZ_iff'.1 h).1

@[expose] def pf (u : ℕ → Bool) (j : ℕ) : Bool :=
  match j with
  | 0 => u 13
  | 1 => u 12
  | 4 => u 10
  | 6 => u 9
  | 9 => u 6
  | 10 => u 4
  | 12 => u 1
  | 13 => u 0
  | _ => false

theorem par_bC_eq (u : ℕ → Bool) {j : ℕ} (hj : j < 15) : par bC (List.range 15) u j = pf u j := by
  interval_cases j <;>
    simp [par, bC, bRows, List.range_succ, Nat.testBit_succ, Nat.testBit_zero, pf]

theorem nfQ_mul_qr_comm
    (u : ℕ → Bool) {j : ℕ} (hj : j < 15) :
    nfQ u * qr j = qr j * nfQ u * zb rootInvM (pf u j) := by
  rw [nfQ, lprod_mul_x rels_qr (mem_range_15 hj) u (fun i hi => hi), par_bC_eq u hj]

@[expose] def IsCentralExp (u : ℕ → Bool) : Prop :=
  u 0 = false ∧ u 1 = false ∧ u 4 = false ∧ u 6 = false ∧ u 9 = false ∧ u 10 = false ∧
    u 12 = false ∧ u 13 = false

theorem pf_eq_false_iff (u : ℕ → Bool) : (∀ j < 15, pf u j = false) ↔ IsCentralExp u := by
  constructor
  · intro h
    exact ⟨h 13 (by norm_num), h 12 (by norm_num), h 10 (by norm_num), h 9 (by norm_num),
      h 6 (by norm_num), h 4 (by norm_num), h 1 (by norm_num), h 0 (by norm_num)⟩
  · rintro ⟨h0, h1, h4, h6, h9, h10, h12, h13⟩ j hj
    interval_cases j <;> simp [pf, *]

theorem zb_eq_one_iff
    (b : Bool) : zb rootInvM b = 1 ↔ b = false := by
  cases b
  · simp [zb]
  · simp [zb, rootInvM_ne_one]

theorem zb_mem_zpowers
    (b : Bool) : zb rootInvM b ∈ Subgroup.zpowers rootInvM := by
  cases b
  · exact one_mem _
  · exact Subgroup.mem_zpowers _

theorem comm_of_comm_qr
    {g : ModGL Tag.E6 K} (h : ∀ j < 15, qr j * g = g * qr j) :
    ∀ x ∈ radicalQ, x * g = g * x := by
  intro x hx
  rw [radicalQ_eq_closure] at hx
  have hle : Subgroup.closure qset ≤ Subgroup.centralizer {g} := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (h j hj)
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hx)

theorem nfQ_mem_radicalZ_iff
    (u : ℕ → Bool) : nfQ u ∈ radicalZ ↔ IsCentralExp u := by
  rw [mem_radicalZ_iff', ← pf_eq_false_iff]
  constructor
  · rintro ⟨-, hc⟩ j hj
    have h1 := hc (qr j) (qr_mem_radicalQ hj)
    rw [nfQ_mul_qr_comm u hj] at h1
    rw [← zb_eq_one_iff]
    exact (mul_eq_left.1 h1.symm)
  · intro hpf
    refine ⟨nfQ_mem_radicalQ u, comm_of_comm_qr fun j hj => ?_⟩
    rw [nfQ_mul_qr_comm u hj, hpf j hj, zb_false, mul_one]

@[expose] def zIdx (j : ℕ) : ℕ := [14, 2, 3, 5, 7, 8, 11].getD j 0

@[expose] def zB
    (j : ℕ) : ModGL Tag.E6 K := qr (zIdx j)

theorem zB_zero :
    zB 0 = rootInvM := qr_fourteen

theorem centralCheck : (List.range 7).all (fun j => decide (zIdx j < 15) &&
    (List.range 15).all fun k => !bC (zIdx j) k) = true := by decide +kernel

theorem zIdx_lt {j : ℕ} (hj : j < 7) : zIdx j < 15 := by
  have h := centralCheck
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  exact (h j hj).1

theorem zB_mul_qr
    {j : ℕ} (hj : j < 7) {k : ℕ} (hk : k < 15) : zB j * qr k = qr k * zB j := by
  have h := centralCheck
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true'] at h
  rw [zB, qr_mul_qr (zIdx_lt hj) hk, (h j hj).2 k hk, zb_false, mul_one]

theorem zB_mem_radicalQ
    {j : ℕ} (hj : j < 7) : zB j ∈ radicalQ := qr_mem_radicalQ (zIdx_lt hj)

theorem zB_mem_radicalZ
    {j : ℕ} (hj : j < 7) : zB j ∈ radicalZ :=
  mem_radicalZ_iff'.2 ⟨zB_mem_radicalQ hj, comm_of_comm_qr fun _ hk => (zB_mul_qr hj hk).symm⟩

theorem rootInvM_mem_radicalZ :
    rootInvM ∈ radicalZ := zB_zero ▸ zB_mem_radicalZ (by norm_num)

theorem rootInvM_mem_radicalQ :
    rootInvM ∈ radicalQ := radicalZ_le_radicalQ rootInvM_mem_radicalZ

theorem zB_mul_self
    {j : ℕ} (hj : j < 7) : zB j * zB j = 1 := qr_mul_self (zIdx_lt hj)

theorem radicalZ_eq_closure :
    radicalZ = Subgroup.closure {g | ∃ j < 7, g = zB j} := by
  refine le_antisymm ?_ ((Subgroup.closure_le _).2 ?_)
  · intro g hg
    obtain ⟨u, rfl⟩ := mem_radicalQ_iff.1 (radicalZ_le_radicalQ hg)
    obtain ⟨h0, h1, h4, h6, h9, h10, h12, h13⟩ := (nfQ_mem_radicalZ_iff u).1 hg
    refine list_prod_mem fun x hx => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    have hi' := List.mem_range.1 hi
    have hz : ∀ i, i ∈ [14, 2, 3, 5, 7, 8, 11] →
        qr i ∈ Subgroup.closure {g | ∃ j < 7, g = zB j} := by
      intro i hi
      have : ∃ j < 7, zIdx j = i := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        exacts [⟨0, by norm_num, rfl⟩, ⟨1, by norm_num, rfl⟩, ⟨2, by norm_num, rfl⟩,
          ⟨3, by norm_num, rfl⟩, ⟨4, by norm_num, rfl⟩, ⟨5, by norm_num, rfl⟩,
          ⟨6, by norm_num, rfl⟩]
      obtain ⟨j, hj, rfl⟩ := this
      exact Subgroup.subset_closure ⟨j, hj, rfl⟩
    split_ifs with hu
    · interval_cases i <;> first
        | (rw [h0] at hu; cases hu) | (rw [h1] at hu; cases hu) | (rw [h4] at hu; cases hu)
        | (rw [h6] at hu; cases hu) | (rw [h9] at hu; cases hu) | (rw [h10] at hu; cases hu)
        | (rw [h12] at hu; cases hu) | (rw [h13] at hu; cases hu)
        | exact hz _ (by decide)
    · exact one_mem _
  · rintro _ ⟨j, hj, rfl⟩
    exact zB_mem_radicalZ hj

theorem mul_comm_of_mem_radicalZ
    {x y : ModGL Tag.E6 K} (hx : x ∈ radicalZ) (hy : y ∈ radicalZ) :
    x * y = y * x :=
  ((mem_radicalZ_iff'.1 hy).2 x (radicalZ_le_radicalQ hx))

theorem mul_self_of_mem_radicalZ
    {g : ModGL Tag.E6 K} (hg : g ∈ radicalZ) : g * g = 1 := by
  have hg' := hg
  rw [radicalZ_eq_closure] at hg'
  induction hg' using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    exact zB_mul_self hj
  | one => exact mul_one 1
  | mul x y hx hy ihx ihy =>
    have hx' : x ∈ radicalZ := by rw [radicalZ_eq_closure]; exact hx
    have hy' : y ∈ radicalZ := by rw [radicalZ_eq_closure]; exact hy
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [mul_comm_of_mem_radicalZ hy' hx']
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [ihx hx', ihy hy', mul_one]
  | inv x hx ihx =>
    have hx' : x ∈ radicalZ := by rw [radicalZ_eq_closure]; exact hx
    rw [← mul_inv_rev, ihx hx', inv_one]

@[expose] def spreadZ (v : Fin 7 → Bool) (i : ℕ) : Bool :=
  match i with
  | 14 => v 0
  | 2 => v 1
  | 3 => v 2
  | 5 => v 3
  | 7 => v 4
  | 8 => v 5
  | 11 => v 6
  | _ => false

theorem isCentralExp_spreadZ (v : Fin 7 → Bool) : IsCentralExp (spreadZ v) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem card_radicalZ :
    Nat.card radicalZ = 2 ^ 7 := by
  let f : (Fin 7 → Bool) → radicalZ := fun v =>
    ⟨nfQ (spreadZ v), (nfQ_mem_radicalZ_iff _).2 (isCentralExp_spreadZ v)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro v v' h
      have := nfQ_inj (u := spreadZ v) (u' := spreadZ v') (congrArg Subtype.val h)
      funext j
      fin_cases j
      exacts [this 14 (by norm_num), this 2 (by norm_num), this 3 (by norm_num),
        this 5 (by norm_num), this 7 (by norm_num), this 8 (by norm_num), this 11 (by norm_num)]
    · rintro ⟨g, hg⟩
      obtain ⟨u, rfl⟩ := mem_radicalQ_iff.1 (radicalZ_le_radicalQ hg)
      obtain ⟨h0, h1, h4, h6, h9, h10, h12, h13⟩ := (nfQ_mem_radicalZ_iff u).1 hg
      refine ⟨![u 14, u 2, u 3, u 5, u 7, u 8, u 11], Subtype.ext ?_⟩
      refine lprod_congr fun i hi => ?_
      have hi' := List.mem_range.1 hi
      interval_cases i <;> simp [spreadZ, *]
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_fun]
  simp

theorem rootInvM_comm
    {x : ModGL Tag.E6 K} (hx : x ∈ radicalQ) : x * rootInvM = rootInvM * x :=
  (mem_radicalZ_iff'.1 rootInvM_mem_radicalZ).2 x hx

theorem comm_of_mem_zpowers
    {c x : ModGL Tag.E6 K} (hc : c ∈ Subgroup.zpowers rootInvM)
    (hx : x ∈ radicalQ) : x * c = c * x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
  exact (Commute.zpow_right (rootInvM_comm hx) k).eq

theorem conj_qr_mem
    {x : ModGL Tag.E6 K} (hx : x ∈ radicalQ) {j : ℕ} (hj : j < 15) :
    x * qr j * x⁻¹ * (qr j)⁻¹ ∈ Subgroup.zpowers rootInvM := by
  obtain ⟨u, rfl⟩ := mem_radicalQ_iff.1 hx
  have h := nfQ_mul_qr_comm u hj
  have hc := comm_of_mem_zpowers (zb_mem_zpowers (pf u j)) (nfQ_mem_radicalQ u)
  have : nfQ u * qr j * (nfQ u)⁻¹ * (qr j)⁻¹ = zb rootInvM (pf u j) := by
    rw [h, mul_assoc (qr j), hc]
    have hc' := comm_of_mem_zpowers (zb_mem_zpowers (pf u j)) (qr_mem_radicalQ hj)
    calc qr j * (zb rootInvM (pf u j) * nfQ u) * (nfQ u)⁻¹ * (qr j)⁻¹ =
        qr j * zb rootInvM (pf u j) * (qr j)⁻¹ := by group
      _ = zb rootInvM (pf u j) := by rw [hc', mul_inv_cancel_right]
  rw [this]
  exact zb_mem_zpowers _

theorem commutator_mem_zpowers
    {x y : ModGL Tag.E6 K} (hx : x ∈ radicalQ) (hy : y ∈ radicalQ) :
    ⁅x, y⁆ ∈ Subgroup.zpowers rootInvM := by
  rw [commutatorElement_def]
  have hy' := hy
  rw [radicalQ_eq_closure] at hy'
  induction hy' using Subgroup.closure_induction_right with
  | one => simp
  | mul_right y hy₀ q hq ih =>
    obtain ⟨j, hj, rfl⟩ := hq
    have hyQ : y ∈ radicalQ := by rw [radicalQ_eq_closure]; exact hy₀
    have h1 := ih hyQ
    have h2 := conj_qr_mem hx hj
    set c := x * y * x⁻¹ * y⁻¹ with hc
    set d := x * qr j * x⁻¹ * (qr j)⁻¹ with hd
    have e : x * (y * qr j) * x⁻¹ * (y * qr j)⁻¹ = c * (y * d * y⁻¹) := by
      simp only [hc, hd]
      group
    rw [e, comm_of_mem_zpowers h2 hyQ, mul_inv_cancel_right]
    exact mul_mem h1 h2
  | mul_inv_cancel y hy₀ q hq ih =>
    obtain ⟨j, hj, rfl⟩ := hq
    have hyQ : y ∈ radicalQ := by rw [radicalQ_eq_closure]; exact hy₀
    rw [qr_inv hj]
    have h1 := ih hyQ
    have h2 := conj_qr_mem hx hj
    set c := x * y * x⁻¹ * y⁻¹ with hc
    set d := x * qr j * x⁻¹ * (qr j)⁻¹ with hd
    have e : x * (y * qr j) * x⁻¹ * (y * qr j)⁻¹ = c * (y * d * y⁻¹) := by
      simp only [hc, hd]
      group
    rw [e, comm_of_mem_zpowers h2 hyQ, mul_inv_cancel_right]
    exact mul_mem h1 h2

theorem zpowers_rootInvM_eq
    {c : ModGL Tag.E6 K} (hc : c ∈ Subgroup.zpowers rootInvM) :
    c = 1 ∨ c = rootInvM := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
  have h2 : rootInvM ^ (2 : ℤ) = 1 := by rw [zpow_two, rootInvM_mul_self]
  rw [zpow_eq_zpow_emod k h2]
  rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [h]
  · left; rw [zpow_zero]
  · right; rw [zpow_one]

theorem commutator_qr_zero_qr_thirteen :
    ⁅qr 0, qr 13⁆ = rootInvM := by
  have h := qr_mul_qr (by norm_num : 0 < 15) (by norm_num : 13 < 15)
  have hb : bC 0 13 = true := by decide +kernel
  rw [hb, zb_true] at h
  rw [commutatorElement_def, h, qr_inv (by norm_num), qr_inv (by norm_num)]
  have hc := rootInvM_comm (qr_mem_radicalQ (by norm_num : 0 < 15))
  have hc' := rootInvM_comm (qr_mem_radicalQ (by norm_num : 13 < 15))
  calc qr 13 * qr 0 * rootInvM * qr 0 * qr 13 = qr 13 * qr 0 * (rootInvM * qr 0) * qr 13 := by
        group
    _ = qr 13 * (qr 0 * qr 0) * (rootInvM * qr 13) := by rw [← hc]; group
    _ = rootInvM := by
        rw [qr_mul_self (by norm_num), mul_one, ← hc', ← mul_assoc, qr_mul_self (by norm_num),
          one_mul]

theorem commutator_radicalQ :
    ⁅radicalQ, radicalQ⁆ = Subgroup.zpowers rootInvM := by
  refine le_antisymm (Subgroup.commutator_le.2 fun x hx y hy => commutator_mem_zpowers hx hy) ?_
  rw [Subgroup.zpowers_le, ← commutator_qr_zero_qr_thirteen]
  exact Subgroup.commutator_mem_commutator (qr_mem_radicalQ (by norm_num : 0 < 15))
    (qr_mem_radicalQ (by norm_num : 13 < 15))

theorem square_step
    {y : ModGL Tag.E6 K} (hyQ : y ∈ radicalQ) {j : ℕ} (hj : j < 15)
    (ih : y * y ∈ Subgroup.zpowers rootInvM) :
    y * qr j * (y * qr j) ∈ Subgroup.zpowers rootInvM := by
  have hc := commutator_mem_zpowers (qr_mem_radicalQ hj) hyQ
  have h1 : qr j * y = ⁅qr j, y⁆ * y * qr j := by rw [commutatorElement_def]; group
  have h2 := comm_of_mem_zpowers hc hyQ
  have e : y * qr j * (y * qr j) = ⁅qr j, y⁆ * (y * y) := by
    calc y * qr j * (y * qr j) = y * (qr j * y) * qr j := by group
      _ = y * (⁅qr j, y⁆ * y * qr j) * qr j := by rw [h1]
      _ = (y * ⁅qr j, y⁆) * y * (qr j * qr j) := by group
      _ = ⁅qr j, y⁆ * (y * y) := by rw [h2, qr_mul_self hj]; group
  rw [e]
  exact mul_mem hc ih

theorem mul_self_mem_zpowers
    {x : ModGL Tag.E6 K} (hx : x ∈ radicalQ) :
    x * x ∈ Subgroup.zpowers rootInvM := by
  have hx' := hx
  rw [radicalQ_eq_closure] at hx'
  induction hx' using Subgroup.closure_induction_right with
  | one => simp
  | mul_right y hy₀ q hq ih =>
    obtain ⟨j, hj, rfl⟩ := hq
    have hyQ : y ∈ radicalQ := by rw [radicalQ_eq_closure]; exact hy₀
    exact square_step hyQ hj (ih hyQ)
  | mul_inv_cancel y hy₀ q hq ih =>
    obtain ⟨j, hj, rfl⟩ := hq
    have hyQ : y ∈ radicalQ := by rw [radicalQ_eq_closure]; exact hy₀
    rw [qr_inv hj]
    exact square_step hyQ hj (ih hyQ)

theorem index_radicalZ :
    (radicalZ.subgroupOf radicalQ).index = 2 ^ 8 := by
  have h := Subgroup.card_mul_index (radicalZ.subgroupOf radicalQ)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe radicalZ_le_radicalQ).toEquiv, card_radicalZ,
    card_radicalQ] at h
  have : 2 ^ 15 = 2 ^ 7 * 2 ^ 8 := by norm_num
  rw [this] at h
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h

theorem zpowers_rootInvM_le_radicalZ :
    Subgroup.zpowers rootInvM ≤ radicalZ :=
  Subgroup.zpowers_le.2 rootInvM_mem_radicalZ

theorem commutator_eq_one_or_eq
    {x y : ModGL Tag.E6 K} (hx : x ∈ radicalQ) (hy : y ∈ radicalQ) :
    ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = rootInvM :=
  zpowers_rootInvM_eq (commutator_mem_zpowers hx hy)

theorem zpowers_comm
    {c d : ModGL Tag.E6 K} (hc : c ∈ Subgroup.zpowers rootInvM)
    (hd : d ∈ Subgroup.zpowers rootInvM) : c * d = d * c := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
  obtain ⟨k', rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
  exact (Commute.zpow_zpow_self rootInvM k k').eq

theorem commutator_mul_left
    {x x' y : ModGL Tag.E6 K} (hx : x ∈ radicalQ) (hx' : x' ∈ radicalQ)
    (hy : y ∈ radicalQ) : ⁅x * x', y⁆ = ⁅x, y⁆ * ⁅x', y⁆ := by
  have h1 := commutator_mem_zpowers hx hy
  have h2 := commutator_mem_zpowers hx' hy
  have hc := comm_of_mem_zpowers h2 hx
  rw [zpowers_comm h1 h2]
  simp only [commutatorElement_def] at hc ⊢
  calc x * x' * y * (x * x')⁻¹ * y⁻¹ = x * (x' * y * x'⁻¹ * y⁻¹) * y * x⁻¹ * y⁻¹ := by group
    _ = (x' * y * x'⁻¹ * y⁻¹) * x * y * x⁻¹ * y⁻¹ := by rw [hc]
    _ = (x' * y * x'⁻¹ * y⁻¹) * (x * y * x⁻¹ * y⁻¹) := by group

theorem mem_radicalZ_iff_commutator
    {x : ModGL Tag.E6 K} (hx : x ∈ radicalQ) :
    x ∈ radicalZ ↔ ∀ y ∈ radicalQ, ⁅x, y⁆ = 1 := by
  rw [mem_radicalZ_iff']
  constructor
  · rintro ⟨-, h⟩ y hy
    rw [commutatorElement_def, ← h y hy]
    group
  · intro h
    refine ⟨hx, fun y hy => ?_⟩
    have := h y hy
    rw [commutatorElement_def] at this
    calc y * x = (x * y * x⁻¹ * y⁻¹)⁻¹ * (x * y) := by group
      _ = x * y := by rw [this, inv_one, one_mul]

theorem mul_self_mem_radicalZ
    {x : ModGL Tag.E6 K} (hx : x ∈ radicalQ) : x * x ∈ radicalZ :=
  zpowers_rootInvM_le_radicalZ (mul_self_mem_zpowers hx)

theorem commutator_mem_radicalZ
    {x y : ModGL Tag.E6 K} (hx : x ∈ radicalQ) (hy : y ∈ radicalQ) :
    ⁅x, y⁆ ∈ radicalZ :=
  zpowers_rootInvM_le_radicalZ (commutator_mem_zpowers hx hy)

@[expose] def sympA
    (i : Fin 4) : ModGL Tag.E6 K := qr ([0, 1, 4, 6].getD i 0)

@[expose] def sympB
    (i : Fin 4) : ModGL Tag.E6 K := qr ([13, 12, 10, 9].getD i 0)

theorem sympCheck : (List.range 4).all (fun i => (List.range 4).all fun j =>
    let a := [0, 1, 4, 6].getD i 0; let a' := [0, 1, 4, 6].getD j 0
    let b := [13, 12, 10, 9].getD i 0; let b' := [13, 12, 10, 9].getD j 0
    decide (a < 15) && decide (b < 15) && bC a b' == decide (i = j) && !bC a a' && !bC b b') =
    true := by decide +kernel

theorem commutator_of_bC
    {i j : ℕ} (hi : i < 15) (hj : j < 15) :
    ⁅qr i, qr j⁆ = zb rootInvM (bC i j) := by
  rw [commutatorElement_def, qr_mul_qr hi hj, qr_inv hi, qr_inv hj]
  have hc := comm_of_mem_zpowers (zb_mem_zpowers (bC i j)) (qr_mem_radicalQ hi)
  have hc' := comm_of_mem_zpowers (zb_mem_zpowers (bC i j)) (qr_mem_radicalQ hj)
  calc qr j * qr i * zb rootInvM (bC i j) * qr i * qr j =
      qr j * qr i * (zb rootInvM (bC i j) * qr i) * qr j := by group
    _ = qr j * (qr i * qr i) * (zb rootInvM (bC i j) * qr j) := by rw [← hc]; group
    _ = zb rootInvM (bC i j) := by
        rw [qr_mul_self hi, mul_one, ← hc', ← mul_assoc, qr_mul_self hj, one_mul]

theorem sympA_mem
    (i : Fin 4) : sympA i ∈ radicalQ := by
  have h := sympCheck
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  exact qr_mem_radicalQ (h i i.2 i i.2).1.1.1.1

theorem sympB_mem
    (i : Fin 4) : sympB i ∈ radicalQ := by
  have h := sympCheck
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  exact qr_mem_radicalQ (h i i.2 i i.2).1.1.1.2

theorem symp_relations
    (i j : Fin 4) :
    ⁅sympA i, sympB j⁆ = (if i = j then rootInvM else 1) ∧ ⁅sympA i, sympA j⁆ = 1 ∧
      ⁅sympB i, sympB j⁆ = 1 := by
  have h := sympCheck
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨ha, hb⟩, hab⟩, haa⟩, hbb⟩ := h i i.2 j j.2
  have ha' : [0, 1, 4, 6].getD j 0 < 15 := (h j j.2 j j.2).1.1.1.1
  have hb' : [13, 12, 10, 9].getD j 0 < 15 := (h j j.2 j j.2).1.1.1.2
  refine ⟨?_, ?_, ?_⟩
  · rw [sympA, sympB, commutator_of_bC ha hb', hab]
    by_cases hij : i = j
    · rw [ite_eq_left hij, decide_eq_true (congrArg Fin.val hij)]
      rfl
    · rw [ite_eq_right hij, decide_eq_false (fun e => hij (Fin.ext e))]
      rfl
  · rw [sympA, sympA, commutator_of_bC ha ha', haa, zb_false]
  · rw [sympB, sympB, commutator_of_bC hb hb', hbb, zb_false]

theorem radicalQ_eq_sup :
    radicalQ =
    radicalZ ⊔ Subgroup.closure (Set.range sympA ∪ Set.range sympB) := by
  refine le_antisymm ?_ (sup_le radicalZ_le_radicalQ ((Subgroup.closure_le _).2 ?_))
  · rw [radicalQ_eq_closure, Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    have hZ : ∀ {g}, g ∈ radicalZ → g ∈ radicalZ ⊔ Subgroup.closure
        (Set.range sympA ∪ Set.range sympB) := fun h => Subgroup.mem_sup_left h
    have hS : ∀ {g}, g ∈ Set.range sympA ∪ Set.range sympB → g ∈ radicalZ ⊔ Subgroup.closure
        (Set.range sympA ∪ Set.range sympB) := fun h =>
      Subgroup.mem_sup_right (Subgroup.subset_closure h)
    interval_cases i
    · exact hS (Or.inl ⟨0, rfl⟩)
    · exact hS (Or.inl ⟨1, rfl⟩)
    · exact hZ (zB_mem_radicalZ (j := 1) (by norm_num))
    · exact hZ (zB_mem_radicalZ (j := 2) (by norm_num))
    · exact hS (Or.inl ⟨2, rfl⟩)
    · exact hZ (zB_mem_radicalZ (j := 3) (by norm_num))
    · exact hS (Or.inl ⟨3, rfl⟩)
    · exact hZ (zB_mem_radicalZ (j := 4) (by norm_num))
    · exact hZ (zB_mem_radicalZ (j := 5) (by norm_num))
    · exact hS (Or.inr ⟨3, rfl⟩)
    · exact hS (Or.inr ⟨2, rfl⟩)
    · exact hZ (zB_mem_radicalZ (j := 6) (by norm_num))
    · exact hS (Or.inr ⟨1, rfl⟩)
    · exact hS (Or.inr ⟨0, rfl⟩)
    · exact hZ (zB_mem_radicalZ (j := 0) (by norm_num))
  · rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
    exacts [sympA_mem i, sympB_mem i]

end CFSG.Monster.B.E6.StdF4Radical
