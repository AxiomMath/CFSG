module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TCheck
public import CFSG.Sporadic.Schreier.TitsInv

public noncomputable section

namespace CFSG.Quasithin.H13.Tits614

open CFSG.Sporadic.Schreier.Tits CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates.ChainArrays
open scoped commutatorElement

theorem invCand_eq_foldl614 (n : ℕ) (t : Array ℕ) :
    invCand n t = (List.range n).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0) := by
  unfold invCand
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure, List.range_eq_range']
  rfl

theorem rep_invCand614 {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) :
    Rep n (invCand n t) g⁻¹ := by
  have key : ∀ k ≤ n, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0)).size = n ∧ ∀ i < k, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0))[t[i]!]! = i := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      obtain ⟨hs, hi⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set r := (List.range k).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0)
      have htk : t[k]! < n := ht.lt (by omega)
      refine ⟨by rw [Array.size_set!, hs], fun i hik => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hik with hlt | rfl
      · have hne : t[i]! ≠ t[k]! := by
          intro e
          rw [ht.apply (by omega : i < n), ht.apply (by omega : k < n)] at e
          have := g.injective (Fin.ext e)
          simp at this
          omega
        rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hne)]
        exact hi i hlt
      · rw [Array.getElem!_set!_self _ _ _ (by rw [hs]; exact htk)]
  intro x
  obtain ⟨hs, hi⟩ := key n le_rfl
  rw [invCand_eq_foldl614]
  have e : t[(g⁻¹ x : Fin n).val]! = x.val := by
    rw [ht.apply (g⁻¹ x).2]
    simp
  rw [← e, hi _ (g⁻¹ x).2]

theorem rep_conjArr614 {g x : Array ℕ} {u v : Equiv.Perm (Fin 1755)} (hg : Rep 1755 g u)
    (hx : Rep 1755 x v) : Rep 1755 (conjArr g x) (u * v * u⁻¹) :=
  rep_compA (rep_compA hg hx) (rep_invCand614 hg)

theorem rep_commArr614 {n : ℕ} {u v : Array ℕ} {x y : Equiv.Perm (Fin n)} (hu : Rep n u x)
    (hv : Rep n v y) : Rep n (commArr n u v) (tcomm x y) :=
  rep_compA (rep_compA (rep_compA (rep_invCand614 hu) (rep_invCand614 hv)) hu) hv

theorem rep_of_eqA614 {n : ℕ} {a c : Array ℕ} {g : Equiv.Perm (Fin n)} (he : eqA n a c = true)
    (ha : Rep n a g) : Rep n c g := fun x => by
  have := allLt_spec he x.2
  rw [beq_iff_eq] at this
  rw [← this]
  exact ha x

theorem rep_pow5Arr614 {a : Array ℕ} {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a g) :
    Rep 1755 (pow5Arr a) (g ^ 5) := by
  have := rep_compA ha (rep_compA ha (rep_compA ha (rep_compA ha ha)))
  have e : g * (g * (g * (g * g))) = g ^ 5 := by simp [pow_succ, mul_assoc]
  rw [← e]
  exact this

theorem exists_mem_of_anyEq614 {L : List (Array ℕ)} {a : Array ℕ} {g : Equiv.Perm (Fin 1755)}
    (h : anyEq L a = true) (ha : Rep 1755 a g) : ∃ c ∈ L, Rep 1755 c g := by
  rw [anyEq, List.any_eq_true] at h
  obtain ⟨c, hc, he⟩ := h
  exact ⟨c, hc, rep_of_eqA614 he ha⟩

@[expose] def hGen (i : ℕ) : Equiv.Perm (Fin 1755) := permOfArr 1755 titsHArrs[i]!

@[expose] def jGen (i : ℕ) : Equiv.Perm (Fin 1755) := permOfArr 1755 titsJArrs[i]!

@[expose] def kGen (i : ℕ) : Equiv.Perm (Fin 1755) := permOfArr 1755 titsKArrs[i]!

@[expose] def nGen (i : ℕ) : Equiv.Perm (Fin 1755) := permOfArr 1755 titsNArrs[i]!

theorem hGen_rep {i : ℕ} (hi : i < 9) :
    Rep 1755 titsHArrs[i]! (hGen i) :=
  rep_of_allPermsOK titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (by rw [titsHArrs_size]; omega)

theorem jGen_rep {i : ℕ} (hi : i < 9) :
    Rep 1755 titsJArrs[i]! (jGen i) :=
  rep_of_allPermsOK titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (by rw [titsJArrs_size]; omega)

theorem kGen_rep {i : ℕ} (hi : i < 7) :
    Rep 1755 titsKArrs[i]! (kGen i) :=
  rep_of_allPermsOK titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (by rw [titsKArrs_size]; omega)

theorem nGen_rep {i : ℕ} (hi : i < 10) :
    Rep 1755 titsNArrs[i]! (nGen i) :=
  rep_of_allPermsOK titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (by rw [titsNArrs_size]; omega)

theorem titsH_eq_closure614 :
    titsH = Subgroup.closure (Set.range fun i : Fin 3 => hGen i) := by
  rw [← titsQH_facts.2.2.1, titsQH, originalSubgroup_ofArrays]
  rfl

theorem titsJ_eq_closure614 :
    titsJ = Subgroup.closure (Set.range fun i : Fin 4 => jGen i) := by
  rw [← titsQJ_facts.2.2.1, titsQJ, originalSubgroup_ofArrays]
  rfl

theorem titsK_eq_closure614 :
    titsK = Subgroup.closure (Set.range fun i : Fin 2 => kGen i) := by
  rw [← titsQK_facts.2.2.1, titsQK, originalSubgroup_ofArrays]
  rfl

theorem titsN_eq_closure614 :
    titsN = Subgroup.closure (Set.range fun i : Fin 4 => nGen i) := by
  rw [← titsQN_facts.2.2.1, titsQN, originalSubgroup_ofArrays]
  rfl

theorem hGen_mem {i : ℕ}
    (hi : i < 3) : hGen i ∈ titsH := by
  rw [titsH_eq_closure614]
  exact Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩

theorem jGen_mem {i : ℕ}
    (hi : i < 4) : jGen i ∈ titsJ := by
  rw [titsJ_eq_closure614]
  exact Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩

theorem nGen_mem {i : ℕ}
    (hi : i < 4) : nGen i ∈ titsN := by
  rw [titsN_eq_closure614]
  exact Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩

theorem mem_titsJ_iff_sift614
    {a : Array ℕ} {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a g) :
    inJ a = true ↔ g ∈ titsJ := by
  rw [← titsQJ_facts.2.2.1]
  exact siftA_iff_mem_ofArrays titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (by norm_num : 0 < 4) titsLocalChains_check.2.2.2.1 ha

@[expose] def pElt : Equiv.Perm (Fin 1755) := wordIn 3 hGen pWord

theorem pElt_rep :
    Rep 1755 pArr pElt :=
  rep_wordArr (by rw [titsHArrs_size]; norm_num) (fun _ hi => hGen_rep (by omega))
    (fun _ hi => isInvA_of_allPermsOK titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      (by rw [titsHArrs_size]; omega)) p_check.1

theorem pElt_mem : pElt ∈ titsH :=
  wordIn_mem (fun _ hi => hGen_mem hi) _

theorem pElt_pow_five :
    pElt ^ 5 = 1 :=
  eq_of_eqA (rep_pow5Arr614 pElt_rep) rep_idA p_check.2

@[expose] def eX (i : ℕ) : Equiv.Perm (Fin 1755) := wordIn 4 jGen (eXWord i)

@[expose] def eY (i : ℕ) : Equiv.Perm (Fin 1755) := wordIn 4 jGen (eYWord i)

@[expose] def eGen (i : ℕ) : Equiv.Perm (Fin 1755) := tcomm (eX i) (eY i)

@[expose] def titsE614 : Subgroup (Equiv.Perm (Fin 1755)) :=
  Subgroup.closure (Set.range fun i : Fin 5 => eGen i)

@[expose] def eProd (v : ℕ) : Equiv.Perm (Fin 1755) :=
  (List.range 5).foldl (fun g i => if v.testBit i then g * eGen i else g) 1

theorem jGen_isInv {i : ℕ} (hi : i < 4) :
    isInvA 1755 titsJArrs[i]! (invCand 1755 titsJArrs[i]!) = true :=
  isInvA_of_allPermsOK titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (by rw [titsJArrs_size]; omega)

theorem eX_rep {i : ℕ}
    (hi : i < 5) : Rep 1755 (eXArr i) (eX i) :=
  rep_wordArr (by rw [titsJArrs_size]; norm_num) (fun _ hj => jGen_rep (by omega))
    (fun _ hj => jGen_isInv hj) (e_check.1 i hi).1

theorem eY_rep {i : ℕ}
    (hi : i < 5) : Rep 1755 (eYArr i) (eY i) :=
  rep_wordArr (by rw [titsJArrs_size]; norm_num) (fun _ hj => jGen_rep (by omega))
    (fun _ hj => jGen_isInv hj) (e_check.1 i hi).2

theorem eGen_rep {i : ℕ}
    (hi : i < 5) : Rep 1755 (eGenArr i) (eGen i) :=
  rep_commArr614 (eX_rep hi) (eY_rep hi)

theorem eGen_mem_commutator
    (i : ℕ) : eGen i ∈ ⁅titsJ, titsJ⁆ := by
  rw [eGen, tcomm_eq_commutatorElement]
  exact Subgroup.commutator_mem_commutator (inv_mem (wordIn_mem (fun _ hj => jGen_mem hj) _))
    (inv_mem (wordIn_mem (fun _ hj => jGen_mem hj) _))

theorem eProd_rep (v : ℕ) :
    Rep 1755 (eProdArr v) (eProd v) := by
  have key : ∀ l : List ℕ, (∀ i ∈ l, i < 5) → ∀ (a : Array ℕ) (g : Equiv.Perm (Fin 1755)),
      Rep 1755 a g →
      Rep 1755 (l.foldl (fun a i => if v.testBit i then compA 1755 a (eGenArr i) else a) a)
        (l.foldl (fun g i => if v.testBit i then g * eGen i else g) g) := by
    intro l
    induction l with
    | nil => intro _ a g h; exact h
    | cons i l ih =>
      intro hl a g h
      simp only [List.foldl_cons]
      apply ih (fun j hj => hl j (List.mem_cons_of_mem _ hj))
      split_ifs
      · exact rep_compA h (eGen_rep (hl i List.mem_cons_self))
      · exact h
  exact key _ (fun i hi => List.mem_range.mp hi) _ _ rep_idA

theorem eProd_mem (v : ℕ) : eProd v ∈ titsE614 := by
  have key : ∀ l : List ℕ, (∀ i ∈ l, i < 5) → ∀ g : Equiv.Perm (Fin 1755), g ∈ titsE614 →
      l.foldl (fun g i => if v.testBit i then g * eGen i else g) g ∈ titsE614 := by
    intro l
    induction l with
    | nil => intro _ g h; exact h
    | cons i l ih =>
      intro hl g h
      simp only [List.foldl_cons]
      apply ih (fun j hj => hl j (List.mem_cons_of_mem _ hj))
      split_ifs
      · exact mul_mem h (Subgroup.subset_closure ⟨⟨i, hl i List.mem_cons_self⟩, rfl⟩)
      · exact h
  exact key _ (fun i hi => List.mem_range.mp hi) _ (one_mem _)

theorem mem_eArrs {c : Array ℕ} : c ∈ eArrs ↔ ∃ v < 32, eProdArr v = c := by
  simp [eArrs, List.mem_map, List.mem_range]

theorem mem_titsE614_iff_eProd
    {g : Equiv.Perm (Fin 1755)} : g ∈ titsE614 ↔ ∃ v < 32, eProd v = g := by
  obtain ⟨-, h0, hgen, hmul, hinv, -, -, -, -, -⟩ := e_check
  have hlist : ∀ {a : Array ℕ} {g : Equiv.Perm (Fin 1755)}, Rep 1755 a g → inE a = true →
      ∃ v < 32, eProd v = g := by
    intro a g ha h
    obtain ⟨c, hc, hcg⟩ := exists_mem_of_anyEq614 h ha
    obtain ⟨v, hv, rfl⟩ := mem_eArrs.mp hc
    exact ⟨v, hv, (eProd_rep v).unique hcg⟩
  let EL : Subgroup (Equiv.Perm (Fin 1755)) :=
    { carrier := {g | ∃ v < 32, eProd v = g}
      mul_mem' := by
        rintro _ _ ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
        exact hlist (rep_compA (eProd_rep v) (eProd_rep w))
          (Bool.and_eq_true_iff.mp (allLt_spec (allLt_spec hmul hv) hw)).1
      one_mem' := ⟨0, by norm_num, eq_of_eqA (eProd_rep 0) rep_idA h0⟩
      inv_mem' := by
        rintro _ ⟨v, hv, rfl⟩
        refine ⟨v, hv, ?_⟩
        have h2 : eProd v * eProd v = 1 :=
          eq_of_eqA (rep_compA (eProd_rep v) (eProd_rep v)) rep_idA (allLt_spec hinv hv)
        exact (inv_eq_of_mul_eq_one_right h2).symm }
  constructor
  · intro hg
    have hle : titsE614 ≤ EL := by
      rw [titsE614, Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact hlist (eGen_rep i.2) (allLt_spec hgen i.2)
    exact hle hg
  · rintro ⟨v, -, rfl⟩
    exact eProd_mem v

theorem mem_titsE614_iff_inE
    {a : Array ℕ} {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a g) :
    inE a = true ↔ g ∈ titsE614 := by
  rw [mem_titsE614_iff_eProd]
  constructor
  · intro h
    obtain ⟨c, hc, hcg⟩ := exists_mem_of_anyEq614 h ha
    obtain ⟨v, hv, rfl⟩ := mem_eArrs.mp hc
    exact ⟨v, hv, (eProd_rep v).unique hcg⟩
  · rintro ⟨v, hv, rfl⟩
    rw [inE, anyEq, List.any_eq_true]
    exact ⟨eProdArr v, mem_eArrs.mpr ⟨v, hv, rfl⟩, (eqA_iff ha (eProd_rep v)).mpr rfl⟩

theorem card_titsE614 :
    Nat.card titsE614 = 32 := by
  obtain ⟨-, -, -, -, -, hdist, -, -, -, -⟩ := e_check
  have hinj : Set.InjOn eProd (Set.Iio 32) := by
    intro v hv w hw hvw
    by_contra hne
    have hpw : (List.range 32).Pairwise fun v w => eqA 1755 (eProdArr v) (eProdArr w) = false :=
      List.pairwise_map.mp hdist
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := List.pairwise_iff_getElem.mp hpw v w (by simpa using hv) (by simpa using hw) h
      simp only [List.getElem_range] at this
      rw [(eqA_iff (eProd_rep v) (eProd_rep w)).mpr hvw] at this
      exact absurd this (by simp)
    · have := List.pairwise_iff_getElem.mp hpw w v (by simpa using hw) (by simpa using hv) h
      simp only [List.getElem_range] at this
      rw [(eqA_iff (eProd_rep w) (eProd_rep v)).mpr hvw.symm] at this
      exact absurd this (by simp)
  have hset : (titsE614 : Set (Equiv.Perm (Fin 1755))) = eProd '' Set.Iio 32 := by
    ext g
    rw [SetLike.mem_coe, mem_titsE614_iff_eProd]
    simp [Set.mem_image, Set.mem_Iio]
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hset, hinj.ncard_image,
    Set.ncard_eq_toFinset_card' , Set.toFinset_Iio, Nat.card_Iio]

theorem titsE614_comm
    {a b : Equiv.Perm (Fin 1755)} (ha : a ∈ titsE614) (hb : b ∈ titsE614) : a * b = b * a := by
  obtain ⟨-, -, -, hmul, -, -, -, -, -, -⟩ := e_check
  obtain ⟨v, hv, rfl⟩ := mem_titsE614_iff_eProd.mp ha
  obtain ⟨w, hw, rfl⟩ := mem_titsE614_iff_eProd.mp hb
  exact eq_of_eqA (rep_compA (eProd_rep v) (eProd_rep w)) (rep_compA (eProd_rep w) (eProd_rep v))
    (Bool.and_eq_true_iff.mp (allLt_spec (allLt_spec hmul hv) hw)).2

theorem titsE614_le_J :
    titsE614 ≤ titsJ := by
  obtain ⟨-, -, -, -, -, -, -, hJK, -, -⟩ := e_check
  intro g hg
  obtain ⟨v, hv, rfl⟩ := mem_titsE614_iff_eProd.mp hg
  exact (mem_titsJ_iff_sift614 (eProd_rep v)).mp
    (Bool.and_eq_true_iff.mp (allLt_spec hJK hv)).1

theorem titsE614_le_K :
    titsE614 ≤ titsK := by
  obtain ⟨-, -, -, -, -, -, -, hJK, -, -⟩ := e_check
  intro g hg
  obtain ⟨v, hv, rfl⟩ := mem_titsE614_iff_eProd.mp hg
  exact (mem_titsK_iff_sift (eProd_rep v)).mp (Bool.and_eq_true_iff.mp (allLt_spec hJK hv)).2

theorem titsE614_le_commutator :
    titsE614 ≤ ⁅titsJ, titsJ⁆ := by
  rw [titsE614, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact eGen_mem_commutator i

theorem titsZ_mem_titsE614 :
    titsZ ∈ titsE614 :=
  (mem_titsE614_iff_inE titsZ_rep).mp e_check.2.2.2.2.2.2.2.2.2

theorem pElt_mem_normalizer_E :
    pElt ∈ Subgroup.normalizer (titsE614 : Set (Equiv.Perm (Fin 1755))) := by
  obtain ⟨-, -, -, -, -, -, -, -, hp, -⟩ := e_check
  apply mem_normalizer_of_conj
  have hle : titsE614 ≤ titsE614.comap (MulAut.conj pElt).toMonoidHom := by
    rw [titsE614, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (mem_titsE614_iff_inE (rep_conjArr614 pElt_rep (eGen_rep i.2))).mp (allLt_spec hp i.2)
  intro r hr
  have := Subgroup.mem_comap.mp (hle hr)
  rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

theorem titsS_baseCount614 :
    titsQS.baseCount = 5 := by
  show (finList 1755 titsSBase).length = 5
  simp [finList, titsCentral_check.1]

theorem titsH_baseCount614 :
    titsQH.baseCount = 5 := by
  show (finList 1755 titsHBase).length = 5
  simp [finList, titsCentral_check.2.1]

theorem fix_titsR614
    {x : Fin 1755} (hx : ∀ r ∈ titsR, r x = x) : (x : ℕ) < 3 := by
  have h := allLt_spec fix_check x.2
  by_contra hge
  have hge' : decide ((x : ℕ) < 3) = false := decide_eq_false hge
  rw [hge', Bool.false_or, Bool.not_eq_true'] at h
  have : ¬ ∀ j < 3, ((titsRArrs[j]!)[(x : ℕ)]! == (x : ℕ)) = true := fun hall =>
    Bool.false_ne_true (h ▸ allLt_iff.mpr hall)
  push Not at this
  obtain ⟨j, hj, hne⟩ := this
  apply hne
  rw [beq_iff_eq, titsRGen_rep hj x, hx _ (titsRGen_mem hj)]

theorem eq_of_mem_titsJ_of_commute614
    {x : Equiv.Perm (Fin 1755)} (hx : x ∈ titsJ) (hxp : pElt * x = x * pElt) :
    x = 1 ∨ x = titsZ := by
  have hxS : x ∈ titsQS.originalSubgroup := by rw [titsQS_facts.2.2.1]; exact titsJ_le_titsS hx
  obtain ⟨a, ha, hp⟩ := all5_spec titsS_chainArrays (by norm_num : 0 < 4)
    titsLocalChains_check.2.1 titsS_baseCount614 cjp_check hxS
  have hJ := (mem_titsJ_iff_sift614 ha).mpr hx
  have hc := (eqA_iff (rep_compA ha pElt_rep) (rep_compA pElt_rep ha)).mpr hxp.symm
  simp only [hJ, hc, Bool.not_true, Bool.false_or, Bool.or_eq_true] at hp
  rcases hp with h | h
  · exact Or.inl (eq_of_eqA ha rep_idA h)
  · exact Or.inr (eq_of_eqA ha titsZ_rep h)

theorem mem_titsS_of_normalizes614
    {h : Equiv.Perm (Fin 1755)}
    (hh : h ∈ titsH) (hn : ∀ s ∈ titsS, h * s * h⁻¹ ∈ titsS) : h ∈ titsS := by
  have hhQ : h ∈ titsQH.originalSubgroup := by rw [titsQH_facts.2.2.1]; exact hh
  obtain ⟨a, ha, hp⟩ := all5_spec titsH_chainArrays (by norm_num : 0 < 4)
    titsLocalChains_check.1 titsH_baseCount614 nhs_check hhQ
  have hall : (allLt 3 fun i => inS (conjArr a titsSArrs[i]!)) = true := by
    rw [allLt_iff]
    intro i hi
    exact (mem_titsS_iff_sift (rep_conjArr614 ha (titsSGen_rep hi))).mpr (hn _ (titsSGen_mem hi))
  simp only [hall, Bool.not_true, Bool.false_or] at hp
  exact (mem_titsS_iff_sift ha).mp hp

theorem mem_titsJ_of_conj614
    {s : Equiv.Perm (Fin 1755)}
    (hs : s ∈ titsS) (hps : pElt⁻¹ * s * pElt ∈ titsS) : s ∈ titsJ := by
  have hsQ : s ∈ titsQS.originalSubgroup := by rw [titsQS_facts.2.2.1]; exact hs
  obtain ⟨a, ha, hp⟩ := all5_spec titsS_chainArrays (by norm_num : 0 < 4)
    titsLocalChains_check.2.1 titsS_baseCount614 ssp_check hsQ
  have h1 := (mem_titsS_iff_sift
    (rep_compA (rep_compA (rep_invCand614 pElt_rep) ha) pElt_rep)).mpr hps
  simp only [h1, Bool.not_true, Bool.false_or] at hp
  exact (mem_titsJ_iff_sift614 ha).mp hp

theorem outer_facts614
    {s : Equiv.Perm (Fin 1755)}
    (hs : s ∈ titsS) (hE : ∀ i < 3, tcomm (s * titsGen 1) (hGen i) ∈ titsE614) :
    (∀ j < 2, s * titsGen 1 * kGen j * (s * titsGen 1)⁻¹ ∈ titsK) ∧
      ∀ j < 4, tcomm (s * titsGen 1) (nGen j) ∈ titsK := by
  have hsQ : s ∈ titsQS.originalSubgroup := by rw [titsQS_facts.2.2.1]; exact hs
  obtain ⟨a, ha, hp⟩ := all5_spec titsS_chainArrays (by norm_num : 0 < 4)
    titsLocalChains_check.2.1 titsS_baseCount614 outer_check hsQ
  have hu : Rep 1755 (outerArr a) (s * titsGen 1) := rep_compA ha titsGen1_rep
  have hall : (allLt 3 fun i => inE (commArr 1755 (outerArr a) titsHArrs[i]!)) = true := by
    rw [allLt_iff]
    intro i hi
    exact (mem_titsE614_iff_inE (rep_commArr614 hu (hGen_rep (by omega)))).mpr (hE i hi)
  simp only [hall, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hp
  obtain ⟨hK, hN⟩ := hp
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · exact (mem_titsK_iff_sift (rep_conjArr614 hu (kGen_rep (by omega)))).mp (allLt_spec hK hj)
  · exact (mem_titsK_iff_sift (rep_commArr614 hu (nGen_rep (by omega)))).mp (allLt_spec hN hj)

end CFSG.Quasithin.H13.Tits614
