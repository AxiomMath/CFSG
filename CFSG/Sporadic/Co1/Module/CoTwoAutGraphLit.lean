module

public import CFSG.Sporadic.Co1.Module.CoTwoAutGraphLitInputs
public import CFSG.Sporadic.Co1.Module.CoTwoAutOrbit
public import CFSG.Sporadic.Co2Rank3.Graph

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1.Module.CoTwoAut

open CFSG.Blueprint CFSG.KC.InvFam CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.SortTree
  CFSG.KC.Graph65 CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module
  CFSG.Sporadic.Co1.Module.TwoBK CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2Rank3 CFSG.Monster.B.Co2
  CFSG.Monster.B.Mathieu MulAction

theorem orB_iff {a b : Bool} : orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> simp [orB]

theorem nbeq_iff {a b : ℕ} : Nat.beq a b = true ↔ a = b := ⟨Nat.eq_of_beq_eq_true, fun h => by
  rw [h]; exact Nat.beq_refl b⟩

theorem clsEq_iff {V : ℕ → ℕ} {w y : ℕ} : clsEq V w y = true ↔ w = V y ∨ w = V y ^^^ 2 := by
  unfold clsEq
  rw [orB_iff, nbeq_iff, nbeq_iff]
  rfl

theorem eqvK_cons (GT : ℕ) (V : ℕ → ℕ) (n y : ℕ) (L : List ℕ) (x : ℕ) :
    eqvK GT V n (y :: L) x =
      andB (Nat.blt y n) (andB (clsEq V (vmF 24 GT (V x)) y) (eqvK GT V n L (x + 1))) := rfl

theorem eqvK_spec {GT n : ℕ} {V : ℕ → ℕ} : ∀ (L : List ℕ) (x₀ : ℕ), eqvK GT V n L x₀ = true →
    ∀ j < L.length, L.getD j 0 < n ∧
      (vmF 24 GT (V (x₀ + j)) = V (L.getD j 0) ∨ vmF 24 GT (V (x₀ + j)) = V (L.getD j 0) ^^^ 2)
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | y :: L, x₀, h, j, hj => by
    rw [eqvK_cons] at h
    obtain ⟨h1, h2⟩ := andB_true_iff.1 h
    obtain ⟨h2, h3⟩ := andB_true_iff.1 h2
    cases j with
    | zero => exact ⟨blt_iff.1 h1, by simpa using clsEq_iff.1 h2⟩
    | succ j =>
      have := eqvK_spec L (x₀ + 1) h3 j (by simpa using hj)
      rw [show x₀ + (j + 1) = x₀ + 1 + j by omega]
      simpa using this

variable {W : GraphW}

theorem lit_vert (hW : GraphOK W) : ∀ x < 2300, vtxK x < 2 ^ 24 ∧ inO (vtxK x) = true ∧
    inO (vtxK x ^^^ 2) = true := by
  intro x hx
  have h := (allN_iff _ _).1 hW.vert x hx
  obtain ⟨h1, h2⟩ := andB_true_iff.1 h
  obtain ⟨h2, h3⟩ := andB_true_iff.1 h2
  have h1' := blt_iff.1 h1
  rw [pw2_eq] at h1'
  exact ⟨h1', h2, h3⟩

theorem keyK_xor (v : ℕ) : keyK (v ^^^ 2) = keyK v := by
  unfold keyK
  change min (v ^^^ 2) (v ^^^ 2 ^^^ 2) = min v (v ^^^ 2)
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.min_comm]

theorem xor_eq_iff {a b c : ℕ} (h : a ^^^ b = c) : b = a ^^^ c := by
  rw [← h, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem lit_dist (hW : GraphOK W) : ∀ i < 2300, ∀ j < i,
    (vtxK i ^^^ vtxK j) ≠ 0 ∧ (vtxK i ^^^ vtxK j) ≠ 2 := by
  have hs := (allN_iff _ _).1 hW.dist
  let s : ℕ → ℕ := fun k => W.KS k >>> 24
  let κ : ℕ → ℕ := fun k => W.KS k &&& (2 ^ 24 - 1)
  have hm : maskN 24 = 2 ^ 24 - 1 := by
    unfold maskN
    rw [pw2_eq]
    rfl
  have hk : ∀ k < 2300, s k < 2300 ∧ keyK (vtxK (s k)) = κ k ∧ (k + 1 < 2300 → κ k < κ (k + 1)) := by
    intro k hk
    obtain ⟨h1, h2⟩ := andB_true_iff.1 (hs k hk)
    obtain ⟨h2, h3⟩ := andB_true_iff.1 h2
    refine ⟨blt_iff.1 h1, ?_, fun hk1 => ?_⟩
    · have := nbeq_iff.1 h2
      rw [hm] at this
      exact this
    · rcases orB_iff.1 h3 with h | h
      · have := ble_iff.1 h
        omega
      · have := blt_iff.1 h
        rw [hm] at this
        exact this
  have hmono : ∀ a b, a < b → b < 2300 → κ a < κ b := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h | h
      · exact (ih h (by omega)).trans ((hk b (by omega)).2.2 hb)
      · rw [h]
        exact (hk b (by omega)).2.2 hb
  let f : Fin 2300 → Fin 2300 := fun k => ⟨s k, (hk k k.isLt).1⟩
  have hf : Function.Injective f := by
    intro a b hab
    have e : s a = s b := congrArg Fin.val hab
    have e2 : κ a = κ b := by rw [← (hk a a.isLt).2.1, ← (hk b b.isLt).2.1, e]
    rcases lt_trichotomy a.val b.val with h | h | h
    · exact absurd e2 (ne_of_lt (hmono _ _ h b.isLt))
    · exact Fin.ext h
    · exact absurd e2.symm (ne_of_lt (hmono _ _ h a.isLt))
  have hsurj : Function.Surjective f := Finite.surjective_of_injective hf
  have hkey : ∀ i < 2300, ∀ j < 2300, i ≠ j → keyK (vtxK i) ≠ keyK (vtxK j) := by
    intro i hi j hj hij e
    obtain ⟨a, ha⟩ := hsurj ⟨i, hi⟩
    obtain ⟨b, hb⟩ := hsurj ⟨j, hj⟩
    have ha' : s a = i := congrArg Fin.val ha
    have hb' : s b = j := congrArg Fin.val hb
    have hab : a ≠ b := by
      rintro rfl
      exact hij (ha'.symm.trans hb')
    have e2 : κ a = κ b := by
      rw [← (hk a a.isLt).2.1, ← (hk b b.isLt).2.1, ha', hb', e]
    rcases lt_trichotomy a.val b.val with h | h | h
    · exact absurd e2 (ne_of_lt (hmono _ _ h b.isLt))
    · exact hab (Fin.ext h)
    · exact absurd e2.symm (ne_of_lt (hmono _ _ h a.isLt))
  intro i hi j hj
  refine ⟨fun h0 => ?_, fun h2 => ?_⟩
  · have e := xor_eq_iff h0
    rw [Nat.xor_zero] at e
    exact hkey i hi j (by omega) (by omega) (by rw [e])
  · have e := xor_eq_iff h2
    exact hkey i hi j (by omega) (by omega) (by rw [e, keyK_xor])

theorem co2OrigArrs_eq (k : ℕ) (hk : k < 2) :
    co2OrigArrs[k]! = ([co2G0, co2G1].getD k []).toArray := by
  have e : co2Rec = co2RecLit := by
    unfold co2Rec
    rfl
  have hg : co2Rec.chain.generators = [co2G0, co2G1] := by
    rw [e]
    rfl
  have hl : k < co2Rec.chain.generators.length := by rw [hg]; simpa using hk
  unfold co2OrigArrs
  rw [ChainRecord.origArrs_get _ hl]
  obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
  · simp [hg]
  · simp [hg]

theorem lit_len (hW : GraphOK W) (k : ℕ) (hk : k < 2) : ([co2G0, co2G1].getD k []).length = 2300 := by
  obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
  · have := hW.len.1
    rwa [InvFam.lenL_eq] at this
  · have := hW.len.2
    rwa [InvFam.lenL_eq] at this

theorem lit_eqv (hW : GraphOK W) (k : ℕ) (hk : k < 2) :
    eqvK (getL 0 W.RT (getL 0 W.G k)) vtxK 2300 ([co2G0, co2G1].getD k []) 0 = true := by
  obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
  · exact hW.eqv0
  · exact hW.eqv1


theorem co2Gen_getD (k : ℕ) (hk : k < 2) (x : Fin 2300) :
    ([co2G0, co2G1].getD k []).getD x.val 0 = (co2Gen k x).val := by
  have h := rep_co2Gen hk x
  rw [co2OrigArrs_eq k hk] at h
  rw [← h]
  simp

theorem lit_gen (hW : GraphOK W) (k : ℕ) (hk : k < 2) :
    ∃ g : NativeSporadic.Co1, co1Act g v₂ = v₂ ∧ ∀ x : Fin 2300,
      co1Act g (toVecD 24 (vtxK x)) = toVecD 24 (vtxK (co2Gen k x)) ∨
        co1Act g (toVecD 24 (vtxK x)) = v₂ + toVecD 24 (vtxK (co2Gen k x)) := by
  have hl := InvFam.progK_len W.P 2 hW.prog
  have hG : ∀ i ∈ W.G, i < W.R.length := fun i hi => by
    have := InvFam.bnd_spec hW.idx i hi
    rwa [InvFam.lenL_eq] at this
  have hkG : k < lenL W.G := by rw [hW.lenG]; exact hk
  set i := getL 0 W.G k with hi
  have hiR : i < W.R.length := hG i (InvFam.getL_mem hkG)
  obtain ⟨g, hg⟩ := InvFam.prog_elems W.P 2 hW.prog (fun j hj => by
    obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    · obtain ⟨g, hg⟩ := exists_co1_matA
      refine ⟨g, ?_⟩
      unfold PM
      rw [← hW.rA]
      exact hg
    · obtain ⟨g, hg⟩ := exists_co1_matB
      refine ⟨g, ?_⟩
      unfold PM
      rw [← hW.rB]
      exact hg) i hiR
  have htr : trK 24 (getL 0 W.R i) = getL 0 W.RT i :=
    beq_iff.1 ((allN_iff _ _).1 hW.tr i (by rw [InvFam.lenL_eq]; exact hiR))
  have hact := pm_act hg htr
  refine ⟨g, ?_, fun x => ?_⟩
  · have hf := InvFam.fixAll_spec hW.fix i (InvFam.getL_mem hkG) 2 (by simp)
    rw [← toVecD_v₂, hact, hf]
  · have hlen := lit_len hW k hk
    obtain ⟨-, he⟩ := eqvK_spec _ 0 (lit_eqv hW k hk) x.val (by rw [hlen]; exact x.isLt)
    rw [Nat.zero_add, co2Gen_getD k hk x, ← hi] at he
    rw [hact]
    rcases he with he | he
    · left
      rw [he]
    · right
      rw [he, toVecD_xor, toVecD_v₂, add_comm]

@[expose] def Rel (i j : Fin 2300) : Prop := toVecD 24 (vtxK i) + toVecD 24 (vtxK j) ∈ Tadj

theorem vadd_self (v : Vec24) : v + v = 0 := funext fun i => CharTwo.add_self_eq_zero (v i)

theorem tadj_add {u : Vec24} : v₂ + u ∈ Tadj ↔ u ∈ Tadj := by
  have e : v₂ + (v₂ + u) = u := by rw [← add_assoc, vadd_self, zero_add]
  constructor
  · rintro (h | h)
    · exact Or.inr h
    · rw [e] at h
      exact Or.inl h
  · rintro (h | h)
    · exact Or.inr (by rw [e]; exact h)
    · exact Or.inl h

theorem co1Act_add65 (x : NativeSporadic.Co1) (a b : Vec24) :
    co1Act x (a + b) = co1Act x a + co1Act x b :=
  Matrix.mulVec_add _ _ _

theorem orbit_iff_smul {g : NativeSporadic.Co1} {a t : Vec24} :
    co1Act g t ∈ MulAction.orbit NativeSporadic.Co1 a ↔ t ∈ MulAction.orbit NativeSporadic.Co1 a := by
  constructor
  · intro h
    have h' := Pairs.orbit_smul_mem g⁻¹ h
    change co1Act g⁻¹ (co1Act g t) ∈ MulAction.orbit NativeSporadic.Co1 a at h'
    rwa [← Odd.co1Act_mul', inv_mul_cancel, Odd.co1Act_one'] at h'
  · intro h
    exact Pairs.orbit_smul_mem g h

theorem tadj_smul {g : NativeSporadic.Co1} (hg : co1Act g v₂ = v₂) {u : Vec24} :
    co1Act g u ∈ Tadj ↔ u ∈ Tadj := by
  have hc : ∀ y : Vec24, co1Act g y ∈ Pairs.cls 1 ↔ y ∈ Pairs.cls 1 := by
    intro y
    have e : v₂ + co1Act g y = co1Act g (v₂ + y) := by rw [co1Act_add65, hg]
    change (co1Act g y ∈ MulAction.orbit NativeSporadic.Co1 v₂ ∧
        v₂ + co1Act g y ∈ MulAction.orbit NativeSporadic.Co1 v₄) ↔
      (y ∈ MulAction.orbit NativeSporadic.Co1 v₂ ∧ v₂ + y ∈ MulAction.orbit NativeSporadic.Co1 v₄)
    rw [e, orbit_iff_smul, orbit_iff_smul]
  have e2 : v₂ + co1Act g u = co1Act g (v₂ + u) := by rw [co1Act_add65, hg]
  change (co1Act g u ∈ Pairs.cls 1 ∨ v₂ + co1Act g u ∈ Pairs.cls 1) ↔
    (u ∈ Pairs.cls 1 ∨ v₂ + u ∈ Pairs.cls 1)
  rw [e2, hc, hc]

theorem rel_gen (hW : GraphOK W) (k : ℕ) (hk : k < 2) (x y : Fin 2300) :
    Rel (co2Gen k x) (co2Gen k y) ↔ Rel x y := by
  obtain ⟨g, hg, he⟩ := lit_gen hW k hk
  unfold Rel
  rw [← tadj_smul hg (u := toVecD 24 (vtxK x) + toVecD 24 (vtxK y)), co1Act_add65]
  rcases he x with hx | hx <;> rcases he y with hy | hy <;> rw [hx, hy]
  · rw [add_left_comm, tadj_add]
  · rw [add_assoc, tadj_add]
  · have e : v₂ + toVecD 24 (vtxK (co2Gen k x)) + (v₂ + toVecD 24 (vtxK (co2Gen k y))) =
        toVecD 24 (vtxK (co2Gen k x)) + toVecD 24 (vtxK (co2Gen k y)) := by
      rw [add_add_add_comm, vadd_self, zero_add]
    rw [e]

theorem perm_inv_cancel65 (σ : Equiv.Perm (Fin 2300)) (x : Fin 2300) : σ (σ⁻¹ x) = x := by simp

@[expose] def relStab : Subgroup (Equiv.Perm (Fin 2300)) where
  carrier := {σ | ∀ x y, Rel (σ x) (σ y) ↔ Rel x y}
  mul_mem' {σ τ} hσ hτ x y := by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    exact (hσ _ _).trans (hτ x y)
  one_mem' x y := Iff.rfl
  inv_mem' {σ} hσ x y := by
    rw [← hσ (σ⁻¹ x) (σ⁻¹ y), perm_inv_cancel65, perm_inv_cancel65]

theorem rel_P (hW : GraphOK W) {σ : Equiv.Perm (Fin 2300)} (hσ : σ ∈ co2P) :
    ∀ x y, Rel (σ x) (σ y) ↔ Rel x y := by
  have hle : co2P ≤ relStab := by
    unfold co2P
    rw [Subgroup.closure_le]
    rintro τ (h | h)
    · rw [h]
      exact rel_gen hW 0 (by norm_num)
    · rw [Set.mem_singleton_iff.1 h]
      exact rel_gen hW 1 (by norm_num)
  exact hle hσ

theorem adjB_iff {u : ℕ}
    (hu : u < 2 ^ 24) : adjB labG u = true ↔ toVecD 24 u ∈ Tadj := by
  have hu2 : u ^^^ 2 < 2 ^ 24 := Nat.xor_lt_two_pow hu (by norm_num)
  have e : toVecD 24 (u ^^^ 2) = v₂ + toVecD 24 u := by rw [toVecD_xor, toVecD_v₂, add_comm]
  have l3 : ∀ w < 2 ^ 24, labG w = 3 ↔ toVecD 24 w ∈ MulAction.orbit NativeSporadic.Co1 v₂ :=
    fun w hw => by
      rw [Pairs.orbit_Co1_eq]
      exact Pairs.tyLab_spec w hw 3 (by norm_num)
  have l1 : ∀ w < 2 ^ 24, labG w = 1 ↔ toVecD 24 w ∈ MulAction.orbit NativeSporadic.Co1 v₄ :=
    fun w hw => by
      rw [Pairs.orbit_Co1_eq]
      exact Pairs.tyLab_spec w hw 1 (by norm_num)
  have ev : v₂ + (v₂ + toVecD 24 u) = toVecD 24 u := by rw [← add_assoc, vadd_self, zero_add]
  have hb : adjB labG u = true ↔ ((labG u = 3 ∧ labG (u ^^^ 2) = 1) ∨
      (labG (u ^^^ 2) = 3 ∧ labG u = 1)) := by
    unfold adjB
    rw [orB_iff, andB_true_iff, andB_true_iff, nbeq_iff, nbeq_iff, nbeq_iff, nbeq_iff]
    rfl
  rw [hb, l3 u hu, l1 _ hu2, l3 _ hu2, l1 u hu, e]
  change _ ↔ (toVecD 24 u ∈ MulAction.orbit NativeSporadic.Co1 v₂ ∧
      v₂ + toVecD 24 u ∈ MulAction.orbit NativeSporadic.Co1 v₄) ∨
    (v₂ + toVecD 24 u ∈ MulAction.orbit NativeSporadic.Co1 v₂ ∧
      v₂ + (v₂ + toVecD 24 u) ∈ MulAction.orbit NativeSporadic.Co1 v₄)
  rw [ev]

theorem rel_iff_adjB
    (hW : GraphOK W) (i j : Fin 2300) : Rel i j ↔ adjB labG (vtxK i ^^^ vtxK j) = true := by
  have hi := (lit_vert hW i i.isLt).1
  have hj := (lit_vert hW j j.isLt).1
  rw [adjB_iff (Nat.xor_lt_two_pow hi hj), toVecD_xor]
  rfl

theorem not_rel_self
    (hW : GraphOK W) (i : Fin 2300) : ¬ Rel i i := by
  rw [rel_iff_adjB hW, Nat.xor_self]
  have h0 : labG 0 = 0 := by
    unfold labG Pairs.tyLab
    simp
  have hf : adjB labG 0 = false := by
    unfold adjB
    rw [h0]
    generalize Nat.beq (labG (Nat.xor 0 (nat_lit 2))) (nat_lit 3) = b
    cases b <;> rfl
  rw [hf]
  exact Bool.false_ne_true

theorem lit_adj
    (hW : GraphOK W)
    (i j : Fin 2300) : co2Graph.Adj i j ↔ Rel i j := by
  have h3 : Rel 0 3 := (rel_iff_adjB hW 0 3).2 hW.adj3
  have h1 : ¬ Rel 0 1 := fun h =>
    Bool.false_ne_true (hW.adj1.symm.trans ((rel_iff_adjB hW 0 1).1 h))
  obtain ⟨g, hg, hgi⟩ := co2P_htr i
  have hgi' : g⁻¹ i = 0 := by
    rw [← hgi, Equiv.Perm.smul_def]
    simp
  have hginv := co2P.inv_mem hg
  have e1 : co2Graph.Adj i j ↔ co2Graph.Adj 0 (g⁻¹ j) := by
    rw [← hgi', co2Graph_adj_smul hginv]
  have e2 : Rel i j ↔ Rel 0 (g⁻¹ j) := by
    rw [← hgi', rel_P hW hginv]
  rw [e1, e2, co2Graph_adj_zero]
  have hP0 : ∀ h ∈ co2P0, ∀ z, Rel 0 (h z) ↔ Rel 0 z := by
    intro h hh z
    have h0 : h 0 = 0 := by
      have := mem_stabilizer_iff.1 hh.2
      rwa [Equiv.Perm.smul_def] at this
    conv_lhs => rw [← h0]
    exact rel_P hW hh.1 0 z
  have orb : ∀ (x z : Fin 2300), z ∈ orbit co2P0 x → (Rel 0 z ↔ Rel 0 x) := by
    intro x z hz
    obtain ⟨h, hh, rfl⟩ := mem_orbit_subgroup_iff.1 hz
    rw [Equiv.Perm.smul_def]
    exact hP0 h hh x
  rcases co2P0_cover (g⁻¹ j) with hz | hz | hz
  · rw [hz]
    refine ⟨fun h => ?_, fun h => absurd h (not_rel_self hW 0)⟩
    exact absurd ((orb 3 0 h).2 h3) (not_rel_self hW 0)
  · exact ⟨fun _ => (orb 3 _ hz).2 h3, fun _ => hz⟩
  · refine ⟨fun h => ?_, fun h => absurd ((orb 1 _ hz).1 h) h1⟩
    exact absurd ((orb 1 _ hz).1 ((orb 3 _ h).2 h3)) h1

end CFSG.Sporadic.Co1.Module.CoTwoAut

end
