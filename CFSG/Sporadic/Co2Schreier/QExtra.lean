module

public import CFSG.Sporadic.Co2Schreier.QCheck
public import CFSG.Sporadic.Co2Schreier.SixGroup
public import CFSG.Sporadic.Schreier.RuSylowB
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PGroupBasics

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.RuSchreier
open scoped commutatorElement

structure QModFacts : Prop where
  basis : (witRec.wLocal.qQuotientBasisIndices == [1, 2, 3, 4, 5, 6, 7, 8]) = true
  sq : allLt 8 (fun k => isOneOrZ (compA 2300 qArrs[k]! qArrs[k]!)) = true
  comm : allLt 8 (fun k => allLt 8 fun l => isOneOrZ (compA 2300 (compA 2300 (compA 2300
    qArrs[k]! qArrs[l]!) (invCand 2300 qArrs[k]!)) (invCand 2300 qArrs[l]!))) = true
  conj : allLt 2 (fun i => allLt 8 fun l => decide (qCol witRec i l < 256) &&
    isProdOrZ (compA 2300 (compA 2300 cArrs[i]! qArrs[l]!) (invCand 2300 cArrs[i]!))
      (qCol witRec i l)) = true
  col00 : (qCol witRec 0 0 == 143) = true
  span : allLt 255 (fun v => spanIter (qActCols witRec 0) (qActCols witRec 1) 8
    (spanIns 1 (v + 1)) == 2 ^ 256 - 1) = true
  theta : allLt 256 (fun a => decide (thetaN witRec a < 256) &&
    (thetaN witRec a != 0 || a == 0 || a == 218)) = true
  theta218 : (thetaN witRec 218 == 0) = true

theorem qmodFacts : QModFacts := by
  have h := qmod_check
  simp only [qmodCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h4b⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h4b, h5, h6, h7⟩

theorem qmod_theta218 :
    thetaN witRec 218 = 0 := beq_iff_eq.1 qmodFacts.theta218

theorem qmod_sq
    {k : ℕ} (hk : k < 8) : isOneOrZ (compA 2300 qArrs[k]! qArrs[k]!) = true :=
  allLt_iff.1 qmodFacts.sq k hk

theorem qmod_comm {k l : ℕ} (hk : k < 8) (hl : l < 8) :
    isOneOrZ (compA 2300 (compA 2300 (compA 2300 qArrs[k]! qArrs[l]!) (invCand 2300 qArrs[k]!))
      (invCand 2300 qArrs[l]!)) = true :=
  allLt_iff.1 (allLt_iff.1 qmodFacts.comm k hk) l hl

theorem qmod_conj
    {i l : ℕ} (hi : i < 2) (hl : l < 8) : qCol witRec i l < 256 ∧
    isProdOrZ (compA 2300 (compA 2300 cArrs[i]! qArrs[l]!) (invCand 2300 cArrs[i]!))
      (qCol witRec i l) = true := by
  have h := allLt_iff.1 (allLt_iff.1 qmodFacts.conj i hi) l hl
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

theorem qmod_col00 :
    qCol witRec 0 0 = 143 := beq_iff_eq.1 qmodFacts.col00

theorem qmod_span {v : ℕ} (hv : v < 255) :
    spanIter (qActCols witRec 0) (qActCols witRec 1) 8 (spanIns 1 (v + 1)) = 2 ^ 256 - 1 :=
  beq_iff_eq.1 (allLt_iff.1 qmodFacts.span v hv)

theorem qmod_theta_lt
    {a : ℕ} (ha : a < 256) : thetaN witRec a < 256 := by
  have h := allLt_iff.1 qmodFacts.theta a ha
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem qmod_theta
    {a : ℕ} (ha : a < 256) (h0 : thetaN witRec a = 0) : a = 0 ∨ a = 218 := by
  have h := allLt_iff.1 qmodFacts.theta a ha
  rw [Bool.and_eq_true, Bool.or_eq_true, Bool.or_eq_true, beq_iff_eq, beq_iff_eq,
    bne_iff_ne] at h
  rcases h.2 with (h | h) | h
  · exact absurd h0 h
  · exact Or.inl h
  · exact Or.inr h

theorem locZ_mem_Q :
    locZ ∈ locQ := (Subgroup.mem_inf.1 locZ_mem_centerIn_Q).1

@[expose] def toQc (g : Equiv.Perm (Fin 2300)) (hg : g ∈ locQ) : locQ.subgroupOf locC :=
  ⟨⟨g, locQ_le_C hg⟩, Subgroup.mem_subgroupOf.2 hg⟩

theorem coe_toQc (g : Equiv.Perm (Fin 2300)) (hg : g ∈ locQ) :
    (((toQc g hg : locQ.subgroupOf locC) : locC) : Equiv.Perm (Fin 2300)) = g := rfl

theorem toQc_mul {a b : Equiv.Perm (Fin 2300)} (ha : a ∈ locQ) (hb : b ∈ locQ) :
    toQc (a * b) (locQ.mul_mem ha hb) = toQc a ha * toQc b hb := rfl

theorem toQc_eq {a b : Equiv.Perm (Fin 2300)} (ha : a ∈ locQ) (hb : b ∈ locQ) (h : a = b) :
    toQc a ha = toQc b hb := by
  subst h
  rfl

@[expose] def zQc :
    locQ.subgroupOf locC := toQc locZ locZ_mem_Q

theorem qTuple_mem_Q (k : ℕ) : qTuple.getD k 1 ∈ locQ :=
  getD_one_mem_of (fun _ hg => Subgroup.subset_closure hg) k

@[expose] def qcGen (k : ℕ) : locQ.subgroupOf locC := toQc (qTuple.getD k 1) (qTuple_mem_Q k)

@[expose] def qcGens : Set (locQ.subgroupOf locC) :=
  {x | ((x : locC) : Equiv.Perm (Fin 2300)) ∈ ({g | g ∈ qTuple} : Set (Equiv.Perm (Fin 2300)))}

theorem closure_subgroupOf_eq_top {G : Type*} [Group G] {H K : Subgroup G} (hHK : H ≤ K)
    {X : Set G} (hX : Subgroup.closure X = H) :
    Subgroup.closure {x : H.subgroupOf K | ((x : K) : G) ∈ X} = ⊤ := by
  have hXH : X ⊆ H := hX ▸ Subgroup.subset_closure
  set f : H.subgroupOf K →* G := K.subtype.comp (H.subgroupOf K).subtype with hfdef
  have hf : Function.Injective f := fun a b h => Subtype.ext (Subtype.ext h)
  apply Subgroup.map_injective hf
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map]
  have himg : f '' {x : H.subgroupOf K | ((x : K) : G) ∈ X} = X := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hg
      exact ⟨⟨⟨g, hHK (hXH hg)⟩, Subgroup.mem_subgroupOf.2 (hXH hg)⟩, hg, rfl⟩
  rw [himg, hX]
  ext g
  constructor
  · intro hg
    exact ⟨⟨⟨g, hHK hg⟩, Subgroup.mem_subgroupOf.2 hg⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact Subgroup.mem_subgroupOf.1 x.2

theorem qcGens_closure : Subgroup.closure qcGens = ⊤ :=
  closure_subgroupOf_eq_top (X := {g | g ∈ qTuple}) locQ_le_C rfl

theorem mem_qcGens
    {x : locQ.subgroupOf locC} (hx : x ∈ qcGens) : ∃ k < 8, x = qcGen k := by
  obtain ⟨k, hk, h⟩ := (mem_iff_exists_getD (d := 1)).1 (show ((x : locC) : Equiv.Perm
    (Fin 2300)) ∈ qTuple from hx)
  rw [qTuple_length] at hk
  exact ⟨k, hk, Subtype.ext (Subtype.ext h.symm)⟩

theorem qcGen_mem_qcGens {k : ℕ} (hk : k < 8) : qcGen k ∈ qcGens :=
  getD_mem (by rw [qTuple_length]; exact hk)

theorem mem_center_qc_iff (x : locQ.subgroupOf locC) :
    x ∈ Subgroup.center (locQ.subgroupOf locC) ↔
      ((x : locC) : Equiv.Perm (Fin 2300)) ∈ CFSG.centerIn locQ := by
  constructor
  · intro hx
    refine ⟨Subgroup.mem_subgroupOf.1 x.2, fun g hg => ?_⟩
    have h := Subgroup.mem_center_iff.1 hx (toQc g hg)
    exact congrArg (fun y : locQ.subgroupOf locC => ((y : locC) : Equiv.Perm (Fin 2300))) h
  · intro hx
    refine Subgroup.mem_center_iff.2 fun y => Subtype.ext (Subtype.ext ?_)
    exact (Subgroup.mem_inf.1 hx).2 _ (Subgroup.mem_subgroupOf.1 y.2)

theorem zQc_mem_center :
    zQc ∈ Subgroup.center (locQ.subgroupOf locC) :=
  (mem_center_qc_iff _).2 locZ_mem_centerIn_Q

theorem card_center_qc :
    Nat.card (Subgroup.center (locQ.subgroupOf locC)) = 2 := by
  rw [Nat.card_congr (Subgroup.centerCongr (Subgroup.subgroupOfEquivOfLe locQ_le_C)).toEquiv,
    card_center_eq, card_centerIn_Q]

theorem zQc_ne_one :
    zQc ≠ 1 := fun h => locZ_ne_one (congrArg
  (fun y : locQ.subgroupOf locC => ((y : locC) : Equiv.Perm (Fin 2300))) h)

theorem center_qc :
    Subgroup.center (locQ.subgroupOf locC) = Subgroup.zpowers zQc := by
  have hle : Subgroup.zpowers zQc ≤ Subgroup.center (locQ.subgroupOf locC) :=
    (Subgroup.zpowers_le).2 zQc_mem_center
  have hz : Nat.card (Subgroup.zpowers zQc) = 2 := by
    rw [Nat.card_zpowers]
    refine orderOf_eq_prime ?_ zQc_ne_one
    exact Subtype.ext (Subtype.ext (by
      change locZ ^ 2 = 1
      exact locZ_sq))
  exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [hz, card_center_qc]))).symm

theorem mem_center_qc_of_isOneOrZ
    {x : locQ.subgroupOf locC} {t : Array ℕ}
    (ht : Rep 2300 t ((x : locC) : Equiv.Perm (Fin 2300))) (h : isOneOrZ t = true) :
    x ∈ Subgroup.center (locQ.subgroupOf locC) := by
  rw [isOneOrZ, Bool.or_eq_true] at h
  rcases h with h | h
  · have : x = 1 := Subtype.ext (Subtype.ext (eq_of_eqA ht rep_idA h))
    rw [this]
    exact Subgroup.one_mem _
  · have : x = zQc := Subtype.ext (Subtype.ext (eq_of_eqA ht rep_z h))
    rw [this]
    exact zQc_mem_center

theorem rep_qcGen
    {k : ℕ} (hk : k < 8) :
    Rep 2300 qArrs[k]! (((qcGen k : locQ.subgroupOf locC) : locC) : Equiv.Perm (Fin 2300)) :=
  repTuple_q.rep (by rw [qTuple_length]; exact hk)

theorem rep_qcGen_inv
    {k : ℕ} (hk : k < 8) :
    Rep 2300 (invCand 2300 qArrs[k]!)
      (((qcGen k : locQ.subgroupOf locC) : locC) : Equiv.Perm (Fin 2300))⁻¹ :=
  rep_inv_of_isInvA (rep_qcGen hk) (allInv_spec wordFacts.invQ (wordFacts.sizeQ ▸ hk))

theorem quotCenter_comm :
    ∀ a b : locQ.subgroupOf locC ⧸ Subgroup.center (locQ.subgroupOf locC), a * b = b * a := by
  refine quotient_comm_of_gens _ qcGens_closure fun x hx y hy => ?_
  obtain ⟨k, hk, rfl⟩ := mem_qcGens hx
  obtain ⟨l, hl, rfl⟩ := mem_qcGens hy
  exact mem_center_qc_of_isOneOrZ (rep_compA (rep_compA (rep_compA (rep_qcGen hk) (rep_qcGen hl))
    (rep_qcGen_inv hk)) (rep_qcGen_inv hl)) (qmod_comm hk hl)

theorem quotCenter_sq :
    ∀ a : locQ.subgroupOf locC ⧸ Subgroup.center (locQ.subgroupOf locC), a ^ 2 = 1 := by
  refine sq_eq_one_of_gens quotCenter_comm (X := QuotientGroup.mk '' qcGens) ?_ ?_
  · rw [← QuotientGroup.coe_mk', ← MonoidHom.map_closure, qcGens_closure,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨k, hk, rfl⟩ := mem_qcGens hx
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, pow_two]
    exact mem_center_qc_of_isOneOrZ (rep_compA (rep_qcGen hk) (rep_qcGen hk))
      (qmod_sq hk)

theorem card_qc :
    Nat.card (locQ.subgroupOf locC) = 512 := card_locQ_subgroupOf

theorem isPGroup_qc :
    IsPGroup 2 (locQ.subgroupOf locC) :=
  IsPGroup.of_card (n := 9) (by rw [card_qc]; norm_num)

theorem commutator_qc_le :
    commutator (locQ.subgroupOf locC) ≤
    Subgroup.center (locQ.subgroupOf locC) :=
  commutator_le_of_quotient_comm _ quotCenter_comm

theorem frattini_qc_le :
    frattini (locQ.subgroupOf locC) ≤
    Subgroup.center (locQ.subgroupOf locC) :=
  CFSG.SectionRank.Ccomm.frattini_le_of_quotient_elementary (p := 2) _ quotCenter_comm
    quotCenter_sq

theorem commutator_qc_ne_bot :
    commutator (locQ.subgroupOf locC) ≠ ⊥ := by
  intro h
  have htop : Subgroup.center (locQ.subgroupOf locC) = ⊤ := by
    refine eq_top_iff.2 fun x _ => Subgroup.mem_center_iff.2 fun y => ?_
    have hc : ⁅y, x⁆ ∈ commutator (locQ.subgroupOf locC) :=
      CFSG.LocalAnalysis.ComponentInitial.ExtraspecialFixed.commutatorElement_mem_commutator y x
    rw [h, Subgroup.mem_bot] at hc
    exact commutatorElement_eq_one_iff_mul_comm.1 hc
  have := card_center_qc
  rw [htop, Subgroup.card_top, card_qc] at this
  norm_num at this

theorem commutator_qc :
    commutator (locQ.subgroupOf locC) =
    Subgroup.center (locQ.subgroupOf locC) := by
  refine Subgroup.eq_of_le_of_card_ge commutator_qc_le ?_
  rw [card_center_qc]
  have h1 : Nat.card (commutator (locQ.subgroupOf locC)) ≠ 1 := fun h =>
    commutator_qc_ne_bot (Subgroup.card_eq_one.1 h)
  have h2 : Nat.card (commutator (locQ.subgroupOf locC)) ≠ 0 := Nat.card_pos.ne'
  omega

theorem frattini_qc :
    frattini (locQ.subgroupOf locC) = Subgroup.center (locQ.subgroupOf locC) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 (locQ.subgroupOf locC)) := ⟨isPGroup_qc⟩
  refine le_antisymm frattini_qc_le ?_
  rw [← commutator_qc, CFSG.frattini_eq_closure_commutator_union_powers (p := 2)]
  exact fun x hx => Subgroup.subset_closure (Or.inl hx)

theorem qc_extraspecial :
    CFSG.IsExtraspecialPGroup 2 (locQ.subgroupOf locC) :=
  ⟨isPGroup_qc, commutator_qc, frattini_qc, card_center_qc⟩

end CFSG.Sporadic.Co2Schreier
