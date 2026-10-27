module

public import CFSG.YGroups.Bound
public import CFSG.Monster.B.Co2.PermArr
public import CFSG.Certificates.OrbitChain
public import Certificates.Data.CFSGNative.YGroups.ExactCheck

public section

namespace CFSG.YGroups

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.YGroups.ModelNative
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons)

noncomputable def yModelHom {p q r : ℕ} {H : Type*} [Group H] (img : ℕ → H)
    (h : ∀ w ∈ yRels p q r, evalWord img w = 1) : YGroup p q r →* H :=
  PresentedGroup.toGroup (f := fun c : Fin (ngen p q r) => img c) (by
    rintro x ⟨w, hw, rfl⟩
    rw [lift_wordFG, evalWord_congr (g' := img)]
    · exact h w hw
    · intro c hc
      simp [lt_ngen_of_mem_yRels hw c hc])

theorem yModelHom_yGen {p q r : ℕ} {H : Type*} [Group H] {img : ℕ → H}
    {h : ∀ w ∈ yRels p q r, evalWord img w = 1} {c : ℕ} (hc : c < ngen p q r) :
    yModelHom img h (yGen p q r c) = img c := by
  rw [yGen_of_lt hc, yModelHom, PresentedGroup.toGroup.of]

theorem range_yModelHom {p q r : ℕ} {H : Type*} [Group H] {img : ℕ → H}
    {h : ∀ w ∈ yRels p q r, evalWord img w = 1} :
    (yModelHom img h).range = Subgroup.closure (img '' Set.Iio (ngen p q r)) := by
  rw [MonoidHom.range_eq_map, ← closure_yGen p q r, MonoidHom.map_closure, Set.image_image]
  congr 1
  apply Set.image_congr
  intro c hc
  exact yModelHom_yGen hc

theorem injective_and_card_of_model {G H : Type*} [Group G] [Group H] [Finite G] (φ : G →* H)
    {B : ℕ} (hup : Nat.card G ≤ B) (hlow : B ≤ Nat.card φ.range) :
    Function.Injective φ ∧ Nat.card G = B := by
  have hle : Nat.card φ.range ≤ Nat.card G :=
    Nat.card_le_card_of_surjective _ φ.rangeRestrict_surjective
  have hbij : Function.Bijective φ.rangeRestrict :=
    φ.rangeRestrict_surjective.bijective_of_nat_card_le (by omega)
  refine ⟨?_, by omega⟩
  intro x y hxy
  exact hbij.1 (Subtype.ext hxy)

@[expose] noncomputable def arrGen (n : ℕ) (O : Array (Array ℕ)) (c : ℕ) : Equiv.Perm (Fin n) :=
  if c < O.size then permOfArr n O[c]! else 1

theorem permsOK_spec {n : ℕ} {O : Array (Array ℕ)} (h : permsOK n O = true) {c : ℕ}
    (hc : c < O.size) : isInvA n O[c]! (invCand n O[c]!) = true :=
  allLt_spec h hc

theorem rep_letterOf {n : ℕ} {O : Array (Array ℕ)} (h : permsOK n O = true) (c : ℕ) :
    Rep n (letterOf n O c) (arrGen n O c) := by
  unfold letterOf arrGen
  by_cases hc : c < O.size
  · rw [ite_eq_left hc, ite_eq_left hc]
    exact (rep_permOfArr (permsOK_spec h hc)).1
  · rw [ite_eq_right hc, ite_eq_right hc]
    exact rep_idA

theorem rep_evalW {n : ℕ} {O : Array (Array ℕ)} (h : permsOK n O = true) :
    ∀ w : List ℕ, Rep n (evalW n O w) (evalWord (arrGen n O) w)
  | [] => by
    rw [evalW, evalWord_nil]
    exact rep_idA
  | c :: w => by
    rw [evalW, evalWord_cons]
    exact rep_compA (rep_letterOf h c) (rep_evalW h w)

theorem evalWord_arrGen_eq_one {n : ℕ} {O : Array (Array ℕ)} {rels : List (List ℕ)}
    (hO : permsOK n O = true) (h : relatorsOK n O rels = true) :
    ∀ w ∈ rels, evalWord (arrGen n O) w = 1 := by
  intro w hw
  have h1 : eqA n (evalW n O w) (idA n) = true := by
    simp only [relatorsOK, List.all_eq_true] at h
    exact h w hw
  exact (eqA_iff (rep_evalW hO w) rep_idA).1 h1

theorem evalWord_arrGen_eq_iff {n : ℕ} {O : Array (Array ℕ)} (hO : permsOK n O = true)
    (u v : List ℕ) :
    evalWord (arrGen n O) u = evalWord (arrGen n O) v ↔ eqA n (evalW n O u) (evalW n O v) = true :=
  (eqA_iff (rep_evalW hO u) (rep_evalW hO v)).symm

@[expose] def arrClosure (n : ℕ) (O : Array (Array ℕ)) : Subgroup (Equiv.Perm (Fin n)) :=
  Subgroup.closure {g | ∃ k < O.size, permOfArr n O[k]! = g}

theorem wordA_mem {n j : ℕ} {S Sinv : Array (Array ℕ)} {K : Subgroup (Equiv.Perm (Fin n))}
    (hS : ∀ h < j, Rep n S[h]! (permOfArr n S[h]!))
    (hSinv : ∀ h < j, Rep n Sinv[h]! (permOfArr n S[h]!)⁻¹)
    (hK : ∀ h < j, permOfArr n S[h]! ∈ K) :
    ∀ w : List ℤ, lettersOK j w = true → ∃ g ∈ K, Rep n (wordA n S Sinv w) g
  | [], _ => ⟨1, K.one_mem, rep_idA⟩
  | l :: w, hw => by
    simp only [lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hl0, hlj⟩, hw⟩ := hw
    have hw' : lettersOK j w = true := by
      simpa [lettersOK, List.all_eq_true] using hw
    obtain ⟨g, hgK, hg⟩ := wordA_mem hS hSinv hK w hw'
    have hlet := rep_letterA (gs := fun h => permOfArr n S[h]!) hS hSinv ⟨hl0, hlj⟩
    refine ⟨_, K.mul_mem ?_ hgK, rep_compA hlet hg⟩
    by_cases hpos : decide (0 < l) = true
    · rw [ite_eq_left hpos]
      exact hK _ (by omega)
    · rw [ite_eq_right hpos]
      exact K.inv_mem (hK _ (by omega))

theorem strong_mem {n : ℕ} {O S Sinv : Array (Array ℕ)} {W : Array (List ℤ)}
    (hO : permsOK n O = true)
    (hinv : ∀ j < S.size, isInvA n S[j]! Sinv[j]! = true)
    (hinit : ∀ k < O.size, eqA n S[k]! O[k]! = true)
    (hder : ∀ i < W.size, lettersOK (O.size + i) W[i]! = true ∧
      eqA n S[O.size + i]! (wordA n S Sinv W[i]!) = true)
    (hsize : S.size = O.size + W.size) :
    ∀ j < S.size, permOfArr n S[j]! ∈ arrClosure n O := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    have hrepS := rep_permOfArr (hinv j hj)
    by_cases hk : j < O.size
    · have hrepO := (rep_permOfArr (permsOK_spec hO hk)).1
      have heq : permOfArr n S[j]! = permOfArr n O[j]! :=
        (eqA_iff hrepS.1 hrepO).1 (hinit j hk)
      rw [heq]
      exact Subgroup.subset_closure ⟨j, hk, rfl⟩
    · obtain ⟨hl, he⟩ := hder (j - O.size) (by omega)
      have hj' : O.size + (j - O.size) = j := by omega
      rw [hj'] at hl he
      have hjj : ∀ h < j, h < S.size := fun h hh => lt_trans hh hj
      obtain ⟨g, hgK, hg⟩ := wordA_mem (K := arrClosure n O) (j := j)
        (fun h hh => (rep_permOfArr (hinv h (hjj h hh))).1)
        (fun h hh => (rep_permOfArr (hinv h (hjj h hh))).2)
        (fun h hh => ih h hh (hjj h hh)) _ hl
      have := (eqA_iff hrepS.1 hg).1 he
      rw [this]
      exact hgK

theorem orbit_reach {n root : ℕ} {steps : Array (Array ℕ)} {T : Orbit}
    {K : Subgroup (Equiv.Perm (Fin n))}
    (hsteps : ∀ t ∈ steps, Rep n t (permOfArr n t) ∧ permOfArr n t ∈ K)
    (h : orbitOK n root steps T = true) :
    ∃ b : Fin n, (b : ℕ) = root ∧ ∃ P : Finset (Fin n), P.card = T.pts.size ∧
      ∀ p ∈ P, ∃ g ∈ K, g b = p := by
  simp only [orbitOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨hm, h0⟩, hpts⟩, htree⟩ := h
  have hpt : ∀ k < T.pts.size, T.pts[k]! < n ∧ T.pos[T.pts[k]!]! = k := by
    intro k hk
    have := allLt_spec hpts hk
    simpa [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using this
  have hroot : root < n := by
    have := (hpt 0 hm).1
    rwa [h0] at this
  have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hroot
  have hed : ∀ k < T.pts.size, 0 < k → T.par[k]! < k ∧ T.lab[k]! < steps.size ∧
      (steps[T.lab[k]!]!)[T.pts[T.par[k]!]!]! = T.pts[k]! := by
    intro k hk hk0
    have := allLt_spec htree hk
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at this
    rcases this with h | ⟨⟨h1, h2⟩, h3⟩
    · omega
    · exact ⟨h1, h2, h3⟩
  let f : ℕ → Fin n := fun k => ⟨T.pts[k]! % n, Nat.mod_lt _ hnpos⟩
  have hf : ∀ k < T.pts.size, (f k : ℕ) = T.pts[k]! := fun k hk =>
    Nat.mod_eq_of_lt (hpt k hk).1
  have hf0 : f 0 = ⟨root, hroot⟩ := Fin.ext (by rw [hf 0 hm, h0])
  have hreach : ∀ k, k < T.pts.size → ∃ g ∈ K, g ⟨root, hroot⟩ = f k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk'
      by_cases hk0 : k = 0
      · subst hk0
        exact ⟨1, K.one_mem, by rw [hf0]; rfl⟩
      · obtain ⟨hpar, hlab, hstep⟩ := hed k hk' (Nat.pos_of_ne_zero hk0)
        obtain ⟨g', hg'K, hg'⟩ := ih (T.par[k]!) hpar (lt_trans hpar hk')
        have hts : steps[T.lab[k]!]! ∈ steps := by
          rw [getElem!_pos steps T.lab[k]! hlab]
          exact Array.getElem_mem hlab
        obtain ⟨hrep, hmem⟩ := hsteps _ hts
        refine ⟨permOfArr n steps[T.lab[k]!]! * g', K.mul_mem hmem hg'K, ?_⟩
        apply Fin.ext
        rw [Equiv.Perm.mul_apply, hg']
        have hlt : T.pts[T.par[k]!]! < n := (hpt _ (lt_trans hpar hk')).1
        have hr := hrep ⟨T.pts[T.par[k]!]!, hlt⟩
        rw [hstep] at hr
        have hff : f (T.par[k]!) = ⟨T.pts[T.par[k]!]!, hlt⟩ :=
          Fin.ext (hf _ (lt_trans hpar hk'))
        rw [hff, ← hr]
        exact (hf k hk').symm
  refine ⟨⟨root, hroot⟩, rfl, (Finset.range T.pts.size).image f, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb hab
    have ha' : a < T.pts.size := Finset.mem_range.1 ha
    have hb' : b < T.pts.size := Finset.mem_range.1 hb
    have h1 : T.pts[a]! = T.pts[b]! := by
      rw [← hf a ha', ← hf b hb']
      exact congrArg Fin.val hab
    rw [← (hpt a ha').2, ← (hpt b hb').2, h1]
  · intro p hp
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hp
    exact hreach k (Finset.mem_range.1 hk)

theorem mem_levelGens {S : Array (Array ℕ)} {base : Array ℕ} {i : ℕ} {t : Array ℕ} :
    t ∈ levelGens S base i ↔ t ∈ S ∧ fixesFirst base t i = true := by
  simp [levelGens, Array.mem_filter]

theorem fixesFirst_spec {base t : Array ℕ} {i : ℕ} (h : fixesFirst base t i = true) {k : ℕ}
    (hk : k < i) : t[base[k]!]! = base[k]! := by
  have := allLt_spec h hk
  simpa using this

theorem chainSizes_prod_le_card {n : ℕ} {O : Array (Array ℕ)} {W : Array (List ℤ)}
    {base : Array ℕ} (h : chainOK n O W base = true) :
    (chainSizes n O W base).prod ≤ Nat.card (arrClosure n O) := by
  simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hO, hS⟩, hSinv⟩, hinit⟩, hinv⟩, hder⟩, hbase⟩, horb⟩ := h
  set S := (strongOf n O W).1 with hSdef
  set Sinv := (strongOf n O W).2 with hSinvdef
  have hinit' : ∀ k < O.size, eqA n S[k]! O[k]! = true := fun k hk => allLt_spec hinit hk
  have hinv' : ∀ j < S.size, isInvA n S[j]! Sinv[j]! = true := fun j hj => allLt_spec hinv hj
  have hder' : ∀ i < W.size, lettersOK (O.size + i) W[i]! = true ∧
      eqA n S[O.size + i]! (wordA n S Sinv W[i]!) = true := by
    intro i hi
    have := allLt_spec hder hi
    simpa [Bool.and_eq_true] using this
  have hmem := strong_mem hO hinv' hinit' hder' hS
  let Kl : ℕ → Subgroup (Equiv.Perm (Fin n)) := fun i =>
    Subgroup.closure {g | ∃ t ∈ levelGens S base i, permOfArr n t = g}
  let sz : ℕ → ℕ := fun i => (orbitSearch n base[i]! (levelGens S base i)).pts.size
  have hSmem : ∀ t ∈ S, Rep n t (permOfArr n t) ∧ permOfArr n t ∈ arrClosure n O := by
    intro t ht
    obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 ht
    have hj' : j < S.size := hj
    rw [← getElem!_pos S j hj']
    exact ⟨(rep_permOfArr (hinv' j hj')).1, hmem j hj'⟩
  have hlevel : ∀ i < base.size, sz i * Nat.card (Kl (i + 1)) ≤ Nat.card (Kl i) := by
    intro i hi
    have hor := allLt_spec horb hi
    have hbi : base[i]! < n := of_decide_eq_true (allLt_spec hbase hi)
    have hsteps : ∀ t ∈ levelGens S base i, Rep n t (permOfArr n t) ∧ permOfArr n t ∈ Kl i := by
      intro t ht
      exact ⟨(hSmem t (mem_levelGens.1 ht).1).1, Subgroup.subset_closure ⟨t, ht, rfl⟩⟩
    obtain ⟨b, hb, P, hPcard, hP⟩ := orbit_reach hsteps hor
    have h1 := CFSG.Certificates.card_mul_card_inf_stabilizer_le (Kl i) b P hP
    have hle : Kl (i + 1) ≤ Kl i ⊓ MulAction.stabilizer (Equiv.Perm (Fin n)) b := by
      rw [Subgroup.closure_le]
      rintro _ ⟨t, ht, rfl⟩
      obtain ⟨htS, htf⟩ := mem_levelGens.1 ht
      have ht0 : t ∈ levelGens S base i :=
        mem_levelGens.2 ⟨htS, allLt_iff.2 fun k hk => allLt_spec htf (Nat.lt_succ_of_lt hk)⟩
      rw [SetLike.mem_coe]
      refine Subgroup.mem_inf.2 ⟨Subgroup.subset_closure ⟨t, ht0, rfl⟩, ?_⟩
      rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
      apply Fin.ext
      have hfix : t[base[i]!]! = base[i]! := fixesFirst_spec htf (Nat.lt_succ_self i)
      have hr := (hSmem t htS).1 b
      rw [hb] at hr ⊢
      rw [← hr]
      exact hfix
    have h2 : Nat.card (Kl (i + 1)) ≤
        Nat.card ↥(Kl i ⊓ MulAction.stabilizer (Equiv.Perm (Fin n)) b) :=
      Subgroup.card_le_of_le hle
    calc sz i * Nat.card (Kl (i + 1)) ≤ P.card * Nat.card ↥(Kl i ⊓ MulAction.stabilizer
          (Equiv.Perm (Fin n)) b) := by
            rw [hPcard]
            exact Nat.mul_le_mul_left _ h2
      _ ≤ Nat.card (Kl i) := h1
  have hprod : ∀ j ≤ base.size, ((List.range j).map sz).prod * Nat.card (Kl j) ≤
      Nat.card (Kl 0) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := hlevel j (by omega)
      rw [List.range_succ, List.map_append, List.prod_append]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      calc ((List.range j).map sz).prod * sz j * Nat.card (Kl (j + 1))
          = ((List.range j).map sz).prod * (sz j * Nat.card (Kl (j + 1))) := by ring
        _ ≤ ((List.range j).map sz).prod * Nat.card (Kl j) := Nat.mul_le_mul_left _ h2
        _ ≤ Nat.card (Kl 0) := h1
  have hK0 : Kl 0 ≤ arrClosure n O := by
    rw [Subgroup.closure_le]
    rintro _ ⟨t, ht, rfl⟩
    exact (hSmem t (mem_levelGens.1 ht).1).2
  have hfin := hprod base.size le_rfl
  have hpos : 0 < Nat.card (Kl base.size) := Nat.card_pos
  have hsizes : chainSizes n O W base = (List.range base.size).map sz := rfl
  rw [hsizes]
  calc ((List.range base.size).map sz).prod = ((List.range base.size).map sz).prod * 1 :=
        (mul_one _).symm
    _ ≤ ((List.range base.size).map sz).prod * Nat.card (Kl base.size) :=
        Nat.mul_le_mul_left _ hpos
    _ ≤ Nat.card (Kl 0) := hfin
    _ ≤ Nat.card (arrClosure n O) := Subgroup.card_le_of_le hK0

theorem arrGen_image_eq (n : ℕ) (O : Array (Array ℕ)) :
    arrGen n O '' Set.Iio O.size = {g | ∃ k < O.size, permOfArr n O[k]! = g} := by
  ext g
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, by rw [arrGen, ite_eq_left (Set.mem_Iio.1 hk)]⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, by rw [arrGen, ite_eq_left hk]⟩

theorem arrGen_of_le {n : ℕ} {O : Array (Array ℕ)} {c : ℕ} (hc : O.size ≤ c) :
    arrGen n O c = 1 := by
  rw [arrGen, ite_eq_right (Nat.not_lt.mpr hc)]

theorem yModelHom_injective_and_card {p q r n : ℕ} {O : Array (Array ℕ)} {W : Array (List ℤ)}
    {base : Array ℕ} {B : ℕ} (hcard : Finite (YGroup p q r) ∧ Nat.card (YGroup p q r) ≤ B)
    (hsize : O.size = ngen p q r) (hrel : ∀ w ∈ yRels p q r, evalWord (arrGen n O) w = 1)
    (hchain : chainOK n O W base = true) (hprod : (chainSizes n O W base).prod = B) :
    Function.Injective (yModelHom (arrGen n O) hrel) ∧ Nat.card (YGroup p q r) = B := by
  have := hcard.1
  refine injective_and_card_of_model _ hcard.2 ?_
  rw [range_yModelHom, ← hsize, arrGen_image_eq, ← hprod]
  exact chainSizes_prod_le_card hchain

theorem evalWord_yGen_eq_iff {p q r n : ℕ} {O : Array (Array ℕ)}
    (hsize : O.size = ngen p q r) (hO : permsOK n O = true)
    (hrel : ∀ w ∈ yRels p q r, evalWord (arrGen n O) w = 1)
    (hinj : Function.Injective (yModelHom (arrGen n O) hrel)) (u v : List ℕ) :
    evalWord (yGen p q r) u = evalWord (yGen p q r) v ↔
      eqA n (evalW n O u) (evalW n O v) = true := by
  have hgen : ∀ c, yModelHom (arrGen n O) hrel (yGen p q r c) = arrGen n O c := by
    intro c
    by_cases hc : c < ngen p q r
    · exact yModelHom_yGen hc
    · rw [yGen_of_le (Nat.not_lt.mp hc), map_one, arrGen_of_le (by omega)]
  have hmap : ∀ w : List ℕ, yModelHom (arrGen n O) hrel (evalWord (yGen p q r) w) =
      evalWord (arrGen n O) w := by
    intro w
    induction w with
    | nil => simp
    | cons c w ih => rw [evalWord_cons, map_mul, ih, hgen, evalWord_cons]
  rw [← evalWord_arrGen_eq_iff hO, ← hmap u, ← hmap v]
  exact hinj.eq_iff.symm


theorem evalWord_yGen_eq_one_iff {p q r n : ℕ} {O : Array (Array ℕ)}
    (hsize : O.size = ngen p q r) (hO : permsOK n O = true)
    (hrel : ∀ w ∈ yRels p q r, evalWord (arrGen n O) w = 1)
    (hinj : Function.Injective (yModelHom (arrGen n O) hrel)) (w : List ℕ) :
    evalWord (yGen p q r) w = 1 ↔ eqA n (evalW n O w) (idA n) = true := by
  have := evalWord_yGen_eq_iff hsize hO hrel hinj w []
  simpa [evalWord_nil, evalW] using this

end CFSG.YGroups
