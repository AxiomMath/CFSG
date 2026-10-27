
module

public import CFSG.Sporadic.Co2Schreier.ChainsBase
public import CFSG.Certificates.SubgroupEnumeration
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Core
public import CFSG.Sporadic.Co2Schreier.CoreCheckInputs

public noncomputable section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.SubgroupEnumeration

structure EnumFacts (gens : Array (Array ℕ)) (m : ℕ) (E : LeftEnum) : Prop where
  pos_m : 0 < m
  size : E.elems.size = m
  zero : eqA 2300 E.elems[0]! (idA 2300) = true
  inv : ∀ k < m, isInvA 2300 E.elems[k]! (invCand 2300 E.elems[k]!) = true
  par : ∀ k < m, k ≠ 0 → E.par[k]! < k ∧ E.lab[k]! < gens.size ∧
    eqA 2300 E.elems[k]! (compA 2300 gens[E.lab[k]!]! E.elems[E.par[k]!]!) = true
  mult : ∀ k < m, ∀ j < gens.size, (E.mult[k]!)[j]! < m ∧
    eqA 2300 E.elems[(E.mult[k]!)[j]!]! (compA 2300 gens[j]! E.elems[k]!) = true
  pos : ∀ k < m, E.pos.getD (keyA E.elems[k]!) 0 = k

theorem enumFacts_of {gens : Array (Array ℕ)} {m : ℕ} {E : LeftEnum} (hm : 0 < m)
    (h : enumOK gens m E = true) : EnumFacts gens m E := by
  simp only [enumOK, Bool.and_eq_true, beq_iff_eq, allLt_iff, Bool.or_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨hm, h1, h2, h3, fun k hk hk0 => ?_, h5, h6⟩
  rcases h4 k hk with h | h
  · exact absurd h hk0
  · exact ⟨h.1.1, h.1.2, h.2⟩

theorem getD_mem {α : Type*} {l : List α} {d : α} {h : ℕ} (hh : h < l.length) :
    l.getD h d ∈ l := by
  rw [List.getD_eq_getElem _ _ hh]
  exact List.getElem_mem hh

@[expose] def eltE (E : LeftEnum) (k : ℕ) : Equiv.Perm (Fin 2300) := permOfArr 2300 E.elems[k]!

section Enum

variable {gens : Array (Array ℕ)} {gs : List (Equiv.Perm (Fin 2300))} {m : ℕ} {E : LeftEnum}
  (hF : EnumFacts gens m E) (hgs : RepTuple 2300 gens gs)
include hF

theorem EnumFacts.rep {k : ℕ} (hk : k < m) : Rep 2300 E.elems[k]! (eltE E k) :=
  (rep_permOfArr (hF.inv k hk)).1

theorem EnumFacts.elt_zero : eltE E 0 = 1 :=
  eq_of_eqA (hF.rep hF.pos_m) rep_idA hF.zero

include hgs

theorem EnumFacts.elt_mul {k : ℕ} (hk : k < m) (hk0 : k ≠ 0) :
    eltE E k = gs.getD (E.lab[k]!) 1 * eltE E (E.par[k]!) := by
  obtain ⟨hp, hl, he⟩ := hF.par k hk hk0
  exact eq_of_eqA (hF.rep hk) (rep_compA (hgs.rep (hgs.1 ▸ hl)) (hF.rep (by omega))) he

theorem EnumFacts.elt_mem {k : ℕ} (hk : k < m) : eltE E k ∈ Subgroup.closure {g | g ∈ gs} := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk0 : k = 0
    · rw [hk0, hF.elt_zero]
      exact Subgroup.one_mem _
    · obtain ⟨hp, hl, -⟩ := hF.par k hk hk0
      rw [hF.elt_mul hgs hk hk0]
      refine Subgroup.mul_mem _ (Subgroup.subset_closure ?_) (ih _ hp (by omega))
      exact getD_mem (by rw [← hgs.1]; exact hl)

theorem EnumFacts.mul_elt {k : ℕ} (hk : k < m) {j : ℕ} (hj : j < gens.size) :
    gs.getD j 1 * eltE E k = eltE E ((E.mult[k]!)[j]!) := by
  obtain ⟨hm, he⟩ := hF.mult k hk j hj
  exact (eq_of_eqA (hF.rep hm) (rep_compA (hgs.rep (hgs.1 ▸ hj)) (hF.rep hk)) he).symm

end Enum

theorem inv_mul_mem_of_mul_mem {G : Type*} [Group G] {X : Set G} (hX : X.Finite) {a : G}
    (h : ∀ e ∈ X, a * e ∈ X) : ∀ e ∈ X, a⁻¹ * e ∈ X := by
  have : Finite X := hX.to_subtype
  let f : X → X := fun e => ⟨a * e, h e e.2⟩
  have hf : Function.Injective f := fun x y hxy => Subtype.ext (mul_left_cancel
    (congrArg Subtype.val hxy))
  intro e he
  obtain ⟨⟨y, hy⟩, hfy⟩ := (Finite.injective_iff_surjective.1 hf) ⟨e, he⟩
  have : a * y = e := congrArg Subtype.val hfy
  rw [← this, inv_mul_cancel_left]
  exact hy

section Enum2

variable {gens : Array (Array ℕ)} {gs : List (Equiv.Perm (Fin 2300))} {m : ℕ} {E : LeftEnum}
  (hF : EnumFacts gens m E) (hgs : RepTuple 2300 gens gs)
include hF hgs

theorem EnumFacts.closure_eq :
    (Subgroup.closure {g | g ∈ gs} : Set (Equiv.Perm (Fin 2300))) =
      Set.range fun k : Fin m => eltE E k := by
  have hfin : (Set.range fun k : Fin m => eltE E k).Finite := Set.finite_range _
  have hleft : ∀ a ∈ {g | g ∈ gs}, ∀ e ∈ Set.range (fun k : Fin m => eltE E k),
      a * e ∈ Set.range (fun k : Fin m => eltE E k) := by
    rintro a ha _ ⟨k, rfl⟩
    obtain ⟨j, hj, rfl⟩ := (mem_iff_exists_getD (d := 1)).1 ha
    have hj' : j < gens.size := hgs.1 ▸ hj
    exact ⟨⟨_, (hF.mult k k.2 j hj').1⟩, (hF.mul_elt hgs k.2 hj').symm⟩
  refine (subgroup_enumeration_completeness_of_transitions {g | g ∈ gs}
    (Set.range fun k : Fin m => eltE E k) ⟨⟨0, hF.pos_m⟩, hF.elt_zero⟩
    ?_ hleft fun a ha => inv_mul_mem_of_mul_mem hfin (hleft a ha)).symm
  rintro _ ⟨k, rfl⟩
  exact wordWitness_of_mem_closure (hF.elt_mem hgs k.2)

theorem EnumFacts.exists_elt {x : Equiv.Perm (Fin 2300)}
    (hx : x ∈ Subgroup.closure {g | g ∈ gs}) : ∃ k < m, eltE E k = x := by
  have : x ∈ (Subgroup.closure {g | g ∈ gs} : Set (Equiv.Perm (Fin 2300))) := hx
  rw [hF.closure_eq hgs] at this
  obtain ⟨k, rfl⟩ := this
  exact ⟨k, k.2, rfl⟩

end Enum2

theorem keyA_eq_of_rep {t u : Array ℕ} {g : Equiv.Perm (Fin 2300)} (ht : Rep 2300 t g)
    (hu : Rep 2300 u g) : keyA t = keyA u := by
  simp only [keyA, ht.apply (show 0 < 2300 by norm_num), hu.apply (show 0 < 2300 by norm_num),
    ht.apply (show 1 < 2300 by norm_num), hu.apply (show 1 < 2300 by norm_num),
    ht.apply (show 3 < 2300 by norm_num), hu.apply (show 3 < 2300 by norm_num)]

section Enum3

variable {gens : Array (Array ℕ)} {m : ℕ} {E : LeftEnum} (hF : EnumFacts gens m E)
include hF

theorem EnumFacts.elt_inj {i j : ℕ} (hi : i < m) (hj : j < m) (h : eltE E i = eltE E j) :
    i = j := by
  have hk : keyA E.elems[i]! = keyA E.elems[j]! := keyA_eq_of_rep (hF.rep hi) (h ▸ hF.rep hj)
  rw [← hF.pos i hi, ← hF.pos j hj, hk]

end Enum3

theorem EnumFacts.card {gens : Array (Array ℕ)} {gs : List (Equiv.Perm (Fin 2300))} {m : ℕ}
    {E : LeftEnum} (hF : EnumFacts gens m E) (hgs : RepTuple 2300 gens gs) :
    Nat.card (Subgroup.closure {g | g ∈ gs}) = m := by
  have hbij : Function.Bijective fun k : Fin m =>
      (⟨eltE E k, hF.elt_mem hgs k.2⟩ : Subgroup.closure {g | g ∈ gs}) := by
    refine ⟨fun a b hab => Fin.ext (hF.elt_inj a.2 b.2 (congrArg Subtype.val hab)), ?_⟩
    rintro ⟨x, hx⟩
    obtain ⟨k, hk, rfl⟩ := hF.exists_elt hgs hx
    exact ⟨⟨k, hk⟩, rfl⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem mem_center_closure_iff {G : Type*} [Group G] {X : Set G} {x : G}
    (hx : x ∈ Subgroup.closure X) :
    x ∈ CFSG.centerIn (Subgroup.closure X) ↔ ∀ g ∈ X, x * g = g * x := by
  rw [CFSG.centerIn, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨-, h⟩ g hg
    exact (h g (Subgroup.subset_closure hg)).symm
  · intro h
    refine ⟨hx, fun y hy => ?_⟩
    have hc : x ∈ Subgroup.centralizer X := by
      rw [Subgroup.mem_centralizer_iff]
      exact fun g hg => (h g hg).symm
    have := Subgroup.closure_le_centralizer_centralizer X hy
    rw [Subgroup.mem_centralizer_iff] at this
    exact (this x hc).symm

theorem EnumFacts.mem_centerIn_iff {gens : Array (Array ℕ)} {gs : List (Equiv.Perm (Fin 2300))}
    {m : ℕ} {E : LeftEnum} (hF : EnumFacts gens m E) (hgs : RepTuple 2300 gens gs)
    {k : ℕ} (hk : k < m) :
    eltE E k ∈ CFSG.centerIn (Subgroup.closure {g | g ∈ gs}) ↔ k ∈ centerIdx gens m E := by
  rw [mem_center_closure_iff (hF.elt_mem hgs hk), centerIdx, List.mem_filter, List.mem_range,
    allLt_iff]
  constructor
  · intro h
    refine ⟨hk, fun j hj => ?_⟩
    exact (commA_iff (hF.rep hk) (hgs.rep (hgs.1 ▸ hj))).2
      (h _ (getD_mem (hgs.1 ▸ hj)))
  · rintro ⟨-, h⟩ g hg
    obtain ⟨j, hj, rfl⟩ := (mem_iff_exists_getD (d := 1)).1 hg
    exact (commA_iff (hF.rep hk) (hgs.rep hj)).1 (h j (hgs.1 ▸ hj))

theorem EnumFacts.card_centerIn {gens : Array (Array ℕ)} {gs : List (Equiv.Perm (Fin 2300))}
    {m : ℕ} {E : LeftEnum} (hF : EnumFacts gens m E) (hgs : RepTuple 2300 gens gs) :
    Nat.card (CFSG.centerIn (Subgroup.closure {g | g ∈ gs})) = (centerIdx gens m E).length := by
  set L := centerIdx gens m E with hL
  have hLm : ∀ k ∈ L, k < m := fun k hk => List.mem_range.1 (List.mem_filter.1 hk).1
  have hnd : L.Nodup := (List.nodup_range).filter _
  have hbij : Function.Bijective fun i : Fin L.length =>
      (⟨eltE E L[i], (hF.mem_centerIn_iff hgs (hLm _ (List.getElem_mem i.2))).2
        (List.getElem_mem i.2)⟩ : CFSG.centerIn (Subgroup.closure {g | g ∈ gs})) := by
    refine ⟨fun a b hab => ?_, ?_⟩
    · have h := hF.elt_inj (hLm _ (List.getElem_mem a.2)) (hLm _ (List.getElem_mem b.2))
        (congrArg Subtype.val hab)
      exact Fin.ext ((hnd.getElem_inj_iff).1 h)
    · rintro ⟨x, hx⟩
      obtain ⟨k, hk, rfl⟩ := hF.exists_elt hgs (Subgroup.mem_inf.1 hx).1
      have hkL := (hF.mem_centerIn_iff hgs hk).1 hx
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hkL
      exact ⟨⟨i, hi⟩, rfl⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem conjOK_spec {conj pis : Array (Array ℕ)} {m : ℕ} {E : LeftEnum}
    (h : conjOK conj pis m E = true) {i : ℕ} (hi : i < conj.size) {k : ℕ} (hk : k < m) :
    (pis[i]!)[k]! < m ∧ eqA 2300 (compA 2300 (compA 2300 conj[i]! E.elems[k]!)
      (invCand 2300 conj[i]!)) E.elems[(pis[i]!)[k]!]! = true := by
  have h1 := allLt_spec (allLt_spec h hi) hk
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using h1

section Conj

variable {gens conj pis : Array (Array ℕ)} {gs cs : List (Equiv.Perm (Fin 2300))} {m : ℕ}
  {E : LeftEnum} (hF : EnumFacts gens m E) (hgs : RepTuple 2300 gens gs)
  (hcs : RepTuple 2300 conj cs) (hcinv : allInv conj = true) (hC : conjOK conj pis m E)
include hF hgs hcs hcinv hC

omit hgs in
theorem EnumFacts.conj_elt {i : ℕ} (hi : i < cs.length) {k : ℕ} (hk : k < m) :
    cs.getD i 1 * eltE E k * (cs.getD i 1)⁻¹ = eltE E ((pis[i]!)[k]!) := by
  have hi' : i < conj.size := hcs.1 ▸ hi
  obtain ⟨hm, he⟩ := conjOK_spec hC hi' hk
  exact eq_of_eqA (rep_compA (rep_compA (hcs.rep hi) (hF.rep hk))
    (rep_inv_of_isInvA (hcs.rep hi) (allInv_spec hcinv hi'))) (hF.rep hm) he

theorem EnumFacts.conj_mem {c : Equiv.Perm (Fin 2300)} (hc : c ∈ Subgroup.closure {x | x ∈ cs})
    {x : Equiv.Perm (Fin 2300)} (hx : x ∈ Subgroup.closure {g | g ∈ gs}) :
    c * x * c⁻¹ ∈ Subgroup.closure {g | g ∈ gs} := by
  set H := Subgroup.closure {g | g ∈ gs}
  have hgen : ∀ a ∈ {x | x ∈ cs}, ∀ y ∈ H, a * y * a⁻¹ ∈ H := by
    intro a ha y hy
    obtain ⟨i, hi, rfl⟩ := (mem_iff_exists_getD (d := 1)).1 ha
    obtain ⟨k, hk, rfl⟩ := hF.exists_elt hgs hy
    rw [hF.conj_elt hcs hcinv hC hi hk]
    exact hF.elt_mem hgs (conjOK_spec hC (hcs.1 ▸ hi) hk).1
  let M : Submonoid (Equiv.Perm (Fin 2300)) :=
    { carrier := {a | ∀ y ∈ H, a * y * a⁻¹ ∈ H}
      mul_mem' := fun {a b} ha hb y hy => by
        have := ha _ (hb y hy)
        simpa [mul_assoc] using this
      one_mem' := fun y hy => by simpa using hy }
  have hM : ∀ a ∈ M, a⁻¹ ∈ M := by
    intro a ha
    have hfa : IsOfFinOrder a := isOfFinOrder_of_finite a
    obtain ⟨n, hn, hpow⟩ := hfa.exists_pow_eq_one
    have hinv : a⁻¹ = a ^ (n - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv]
      rw [← pow_succ, Nat.sub_add_cancel hn, hpow]
    rw [hinv]
    exact M.pow_mem ha _
  have hle : Subgroup.closure {x | x ∈ cs} ≤
      { M with inv_mem' := fun {a} ha => hM a ha } := by
    rw [Subgroup.closure_le]
    exact hgen
  exact hle hc x hx

end Conj

end CFSG.Sporadic.Co2Schreier
