module

public import CFSG.Quasithin.Recognition.Kleidman.F204.O2Phi

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X Z : Subgroup G}

open Classical in
@[expose] noncomputable def coord (L1 L2 S : Subgroup G) (g z : G) : ZMod 2 :=
  if g⁻¹ * z * g ∈ Q1 L1 L2 S then 0 else 1

omit [Finite G] in
theorem coord_eq_zero_iff {g z : G} : coord L1 L2 S g z = 0 ↔ g⁻¹ * z * g ∈ Q1 L1 L2 S := by
  unfold coord
  split_ifs with h
  · simp [h]
  · simp only [h, iff_false]
    decide

omit [Finite G] in
theorem coord_eq_one_iff {g z : G} : coord L1 L2 S g z = 1 ↔ g⁻¹ * z * g ∉ Q1 L1 L2 S := by
  unfold coord
  split_ifs with h
  · simp only [h, not_true_eq_false, iff_false]
    decide
  · simp [h]

omit [Finite G] in
theorem coord_conj (q g z : G) : coord L1 L2 S g (q * z * q⁻¹) = coord L1 L2 S (q⁻¹ * g) z := by
  unfold coord
  have : g⁻¹ * (q * z * q⁻¹) * g = (q⁻¹ * g)⁻¹ * z * (q⁻¹ * g) := by group
  rw [this]

omit [Finite G] in
theorem coord_zero_or_one (L1 L2 S : Subgroup G) (g z : G) :
    coord L1 L2 S g z = 0 ∨ coord L1 L2 S g z = 1 := by
  by_cases h : g⁻¹ * z * g ∈ Q1 L1 L2 S
  · left; exact coord_eq_zero_iff.mpr h
  · right; exact coord_eq_one_iff.mpr h

omit [Finite G] in
theorem coord_mul_B {g b : G} (hb : b ∈ bigB L1 L2 S) (z : G) :
    coord L1 L2 S (g * b) z = coord L1 L2 S g z := by
  have hbP : b ∈ P1 L1 L2 S := (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) hb
  have hN := P1_le_normalizer_Q1 L1 L2 S
  have e : (g * b)⁻¹ * z * (g * b) = b⁻¹ * (g⁻¹ * z * g) * b := by group
  have hiff : (g * b)⁻¹ * z * (g * b) ∈ Q1 L1 L2 S ↔ g⁻¹ * z * g ∈ Q1 L1 L2 S := by
    rw [e]
    have h1 := Subgroup.mem_normalizer_iff.mp (hN ((P1 L1 L2 S).inv_mem hbP)) (g⁻¹ * z * g)
    simpa using h1.symm
  by_cases h : g⁻¹ * z * g ∈ Q1 L1 L2 S
  · rw [coord_eq_zero_iff.mpr h, coord_eq_zero_iff.mpr (hiff.mpr h)]
  · rw [coord_eq_one_iff.mpr h, coord_eq_one_iff.mpr (fun h' => h (hiff.mp h'))]

section Z2

omit [Finite G] in
theorem Z2_norm {p : G} (hp : p ∈ P2 L1 L2 S) {z : G} (hz : z ∈ Frame.Z2 L1 L2 S Z) :
    p * z * p⁻¹ ∈ Frame.Z2 L1 L2 S Z :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure Z _ hp) z).mp hz

omit [Finite G] in
theorem Z2_norm_inv {p : G} (hp : p ∈ P2 L1 L2 S) {z : G} (hz : z ∈ Frame.Z2 L1 L2 S Z) :
    p⁻¹ * z * p ∈ Frame.Z2 L1 L2 S Z := by
  have := Z2_norm (Z := Z) ((P2 L1 L2 S).inv_mem hp) hz
  simpa using this

variable (F : Frame L1 L2 S D X) (hZ : ZData L1 L2 S Z)
include F hZ

theorem relIndex_Z2_inf_Q1 (hZ2 : ¬ Frame.Z2 L1 L2 S Z ≤ Q1 L1 L2 S) :
    (Frame.Z2 L1 L2 S Z ⊓ Q1 L1 L2 S).relIndex (Frame.Z2 L1 L2 S Z) = 2 := by
  have hle : (Frame.Z2 L1 L2 S Z ⊓ Q1 L1 L2 S).relIndex (Frame.Z2 L1 L2 S Z) ≤ 2 :=
    F.relIndex_inf_Q1_le_two (fun e he => F.Q2_le_S (F.Z2_le_Q2 hZ he))
      (fun e he => by rw [F.Z2_sq hZ e he]; exact (Q1 L1 L2 S).one_mem)
  have h1 : (Frame.Z2 L1 L2 S Z ⊓ Q1 L1 L2 S).relIndex (Frame.Z2 L1 L2 S Z) ≠ 1 := by
    intro h
    exact hZ2 (fun z hz => (Subgroup.relIndex_eq_one.mp h hz).2)
  have h0 : (Frame.Z2 L1 L2 S Z ⊓ Q1 L1 L2 S).relIndex (Frame.Z2 L1 L2 S Z) ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  omega

theorem coord_add (hZ2 : ¬ Frame.Z2 L1 L2 S Z ≤ Q1 L1 L2 S) {g : G} (hg : g ∈ P2 L1 L2 S) {z z' : G}
    (hz : z ∈ Frame.Z2 L1 L2 S Z) (hz' : z' ∈ Frame.Z2 L1 L2 S Z) :
    coord L1 L2 S g (z * z') = coord L1 L2 S g z + coord L1 L2 S g z' := by
  have hu : g⁻¹ * z * g ∈ Frame.Z2 L1 L2 S Z := Z2_norm_inv hg hz
  have hu' : g⁻¹ * z' * g ∈ Frame.Z2 L1 L2 S Z := Z2_norm_inv hg hz'
  have hidx : ((Frame.Z2 L1 L2 S Z ⊓ Q1 L1 L2 S).subgroupOf (Frame.Z2 L1 L2 S Z)).index = 2 :=
    relIndex_Z2_inf_Q1 F hZ hZ2
  have key := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨g⁻¹ * z * g, hu⟩)
    (b := ⟨g⁻¹ * z' * g, hu'⟩))
  have e : g⁻¹ * (z * z') * g = (g⁻¹ * z * g) * (g⁻¹ * z' * g) := by group
  have key' : (g⁻¹ * z * g) * (g⁻¹ * z' * g) ∈ Q1 L1 L2 S ↔
      (g⁻¹ * z * g ∈ Q1 L1 L2 S ↔ g⁻¹ * z' * g ∈ Q1 L1 L2 S) := by
    have h := key
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.coe_mul] at h
    simpa [hu, hu', (Frame.Z2 L1 L2 S Z).mul_mem hu hu'] using h
  have e' : coord L1 L2 S g (z * z') = 0 ↔ (g⁻¹ * z * g) * (g⁻¹ * z' * g) ∈ Q1 L1 L2 S := by
    rw [coord_eq_zero_iff, e]
  by_cases h1 : g⁻¹ * z * g ∈ Q1 L1 L2 S <;> by_cases h2 : g⁻¹ * z' * g ∈ Q1 L1 L2 S
  · have h3 := key'.mpr (iff_of_true h1 h2)
    rw [coord_eq_zero_iff.mpr h1, coord_eq_zero_iff.mpr h2, e'.mpr h3]
    rfl
  · have h3 : (g⁻¹ * z * g) * (g⁻¹ * z' * g) ∉ Q1 L1 L2 S := fun h =>
      h2 ((key'.mp h).mp h1)
    have h4 : coord L1 L2 S g (z * z') = 1 :=
      (coord_zero_or_one _ _ _ _ _).resolve_left (fun h => h3 (e'.mp h))
    rw [coord_eq_zero_iff.mpr h1, coord_eq_one_iff.mpr h2, h4]
    rfl
  · have h3 : (g⁻¹ * z * g) * (g⁻¹ * z' * g) ∉ Q1 L1 L2 S := fun h =>
      h1 ((key'.mp h).mpr h2)
    have h4 : coord L1 L2 S g (z * z') = 1 :=
      (coord_zero_or_one _ _ _ _ _).resolve_left (fun h => h3 (e'.mp h))
    rw [coord_eq_one_iff.mpr h1, coord_eq_zero_iff.mpr h2, h4]
    rfl
  · have h3 := key'.mpr (iff_of_false h1 h2)
    rw [coord_eq_one_iff.mpr h1, coord_eq_one_iff.mpr h2, e'.mpr h3]
    decide

end Z2

section Wt

abbrev Bq (L1 L2 S : Subgroup G) : Subgroup ↥(P2 L1 L2 S) :=
  (bigB L1 L2 S).subgroupOf (P2 L1 L2 S)

@[expose] noncomputable def coordc (L1 L2 S : Subgroup G) (z : G) :
    ↥(P2 L1 L2 S) ⧸ Bq L1 L2 S → ZMod 2 :=
  Quotient.lift (fun g : ↥(P2 L1 L2 S) => coord L1 L2 S (g : G) z) (by
    intro g g' h
    have h1 : ((g : ↥(P2 L1 L2 S))⁻¹ * g' : ↥(P2 L1 L2 S)) ∈ Bq L1 L2 S :=
      QuotientGroup.leftRel_apply.mp h
    have h2 : (g : G)⁻¹ * (g' : G) ∈ bigB L1 L2 S := h1
    have e : (g' : G) = (g : G) * ((g : G)⁻¹ * (g' : G)) := by group
    show coord L1 L2 S (g : G) z = coord L1 L2 S (g' : G) z
    rw [e, coord_mul_B h2])

noncomputable instance instFintypeCosets (L1 L2 S : Subgroup G) :
    Fintype (↥(P2 L1 L2 S) ⧸ Bq L1 L2 S) := Fintype.ofFinite _

@[expose] noncomputable def wt (L1 L2 S : Subgroup G) (z : G) : ZMod 2 :=
  ∑ c : ↥(P2 L1 L2 S) ⧸ Bq L1 L2 S, coordc L1 L2 S z c

omit [Finite G] in
theorem coordc_conj {p : G} (hp : p ∈ P2 L1 L2 S) (z : G) (c : ↥(P2 L1 L2 S) ⧸ Bq L1 L2 S) :
    coordc L1 L2 S (p * z * p⁻¹) c = coordc L1 L2 S z ((⟨p, hp⟩ : ↥(P2 L1 L2 S))⁻¹ • c) := by
  induction c using QuotientGroup.induction_on with
  | H g =>
    show coord L1 L2 S (g : G) (p * z * p⁻¹) = coord L1 L2 S (p⁻¹ * (g : G)) z
    exact coord_conj p g z

theorem wt_conj {p : G} (hp : p ∈ P2 L1 L2 S) (z : G) :
    wt L1 L2 S (p * z * p⁻¹) = wt L1 L2 S z := by
  unfold wt
  simp only [coordc_conj hp]
  exact Equiv.sum_comp (MulAction.toPerm ((⟨p, hp⟩ : ↥(P2 L1 L2 S))⁻¹))
    (fun c => coordc L1 L2 S z c)

section WtZ

variable (F : Frame L1 L2 S D X) (hZ : ZData L1 L2 S Z)
include F hZ

theorem wt_mul (hZ2 : ¬ Frame.Z2 L1 L2 S Z ≤ Q1 L1 L2 S) {z z' : G}
    (hz : z ∈ Frame.Z2 L1 L2 S Z) (hz' : z' ∈ Frame.Z2 L1 L2 S Z) :
    wt L1 L2 S (z * z') = wt L1 L2 S z + wt L1 L2 S z' := by
  unfold wt
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  induction c using QuotientGroup.induction_on with
  | H g => exact coord_add F hZ hZ2 g.2 hz hz'

omit F hZ in
theorem wt_one : wt L1 L2 S (1 : G) = 0 := by
  unfold wt
  refine Finset.sum_eq_zero fun c _ => ?_
  induction c using QuotientGroup.induction_on with
  | H g =>
    show coord L1 L2 S (g : G) 1 = 0
    rw [coord_eq_zero_iff]
    simp

theorem coord_eq_of_Z {p p' z : G} (hp : p ∈ P2 L1 L2 S) (hp' : p' ∈ P2 L1 L2 S)
    (hpB : p ∉ bigB L1 L2 S) (hp'B : p' ∉ bigB L1 L2 S) (hz : z ∈ Z) :
    coord L1 L2 S p' z = coord L1 L2 S p z := by
  obtain ⟨q, hq, hqB⟩ := Q1_trans_P2 F hp hp' hpB hp'B
  have hqS : q ∈ S := F.Q1_le_S hq
  have hc : z * q = q * z := hZ.central z hz q hqS
  have e1 : p' * (p'⁻¹ * (q * p)) = q * p := by group
  have hqB' : p'⁻¹ * (q * p) ∈ bigB L1 L2 S := by simpa [mul_assoc] using hqB
  have h1 : coord L1 L2 S (p' * (p'⁻¹ * (q * p))) z = coord L1 L2 S p' z :=
    coord_mul_B (g := p') hqB' z
  rw [e1] at h1
  have h2 : coord L1 L2 S (q * p) z = coord L1 L2 S p z := by
    have : (q * p)⁻¹ * z * (q * p) = p⁻¹ * z * p := by
      have : q⁻¹ * z * q = z := by
        calc q⁻¹ * z * q = q⁻¹ * (z * q) := by group
          _ = q⁻¹ * (q * z) := by rw [hc]
          _ = z := by group
      calc (q * p)⁻¹ * z * (q * p) = p⁻¹ * (q⁻¹ * z * q) * p := by group
        _ = p⁻¹ * z * p := by rw [this]
    unfold coord
    rw [this]
  rw [← h1, h2]

theorem wt_Z {z : G} (hz : z ∈ Z) : wt L1 L2 S z = 0 := by
  classical
  have hzQ : z ∈ Q1 L1 L2 S := F.Z_le_Q1 hZ hz
  set c0 : ↥(P2 L1 L2 S) ⧸ Bq L1 L2 S := ((1 : ↥(P2 L1 L2 S)) : ↥(P2 L1 L2 S) ⧸ Bq L1 L2 S)
    with hc0
  have hcoord0 : coordc L1 L2 S z c0 = 0 := by
    show coord L1 L2 S ((1 : ↥(P2 L1 L2 S)) : G) z = 0
    rw [coord_eq_zero_iff]
    simpa using hzQ
  have hcard : Fintype.card (↥(P2 L1 L2 S) ⧸ Bq L1 L2 S) = 5 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index]
    exact F.pair.relIndex_bigB_right
  have hnb : ∀ c : ↥(P2 L1 L2 S) ⧸ Bq L1 L2 S, c ≠ c0 →
      ∃ p : ↥(P2 L1 L2 S), (p : G) ∉ bigB L1 L2 S ∧ c = (p : _ ⧸ Bq L1 L2 S) := by
    intro c hc
    induction c using QuotientGroup.induction_on with
    | H g =>
      refine ⟨g, fun hg => hc ?_, rfl⟩
      rw [hc0, QuotientGroup.eq]
      show (g⁻¹ * (1 : ↥(P2 L1 L2 S)) : ↥(P2 L1 L2 S)) ∈ Bq L1 L2 S
      have : g ∈ Bq L1 L2 S := show (g : G) ∈ bigB L1 L2 S from hg
      simpa using this
  have hconst : ∃ v : ZMod 2, ∀ c, c ≠ c0 → coordc L1 L2 S z c = v := by
    have hex : ∃ c : ↥(P2 L1 L2 S) ⧸ Bq L1 L2 S, c ≠ c0 := by
      by_contra h
      push Not at h
      have : Fintype.card (↥(P2 L1 L2 S) ⧸ Bq L1 L2 S) ≤ 1 := by
        rw [Fintype.card_le_one_iff]
        intro a b; rw [h a, h b]
      omega
    obtain ⟨c1, hc1⟩ := hex
    obtain ⟨p1, hp1B, rfl⟩ := hnb c1 hc1
    refine ⟨coord L1 L2 S (p1 : G) z, fun c hc => ?_⟩
    obtain ⟨p, hpB, rfl⟩ := hnb c hc
    exact coord_eq_of_Z F hZ p1.2 p.2 hp1B hpB hz
  obtain ⟨v, hv⟩ := hconst
  unfold wt
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c0)]
  rw [hcoord0, zero_add]
  rw [Finset.sum_congr rfl (fun c hc => hv c (Finset.ne_of_mem_erase hc))]
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcard]
  have h4 : (5 - 1 : ℕ) • v = 0 := by
    have : (((5 - 1 : ℕ)) : ZMod 2) = 0 := by decide
    rw [nsmul_eq_mul, this, zero_mul]
  exact h4

theorem wt_Z2 (hZ2 : ¬ Frame.Z2 L1 L2 S Z ≤ Q1 L1 L2 S) {z : G} (hz : z ∈ Frame.Z2 L1 L2 S Z) :
    wt L1 L2 S z = 0 := by
  let M : Subgroup G :=
    { carrier := {z | z ∈ Frame.Z2 L1 L2 S Z ∧ wt L1 L2 S z = 0}
      mul_mem' := fun {a b} ha hb => ⟨(Frame.Z2 L1 L2 S Z).mul_mem ha.1 hb.1, by
        rw [wt_mul F hZ hZ2 ha.1 hb.1, ha.2, hb.2]; rfl⟩
      one_mem' := ⟨(Frame.Z2 L1 L2 S Z).one_mem, wt_one⟩
      inv_mem' := fun {a} ha => ⟨(Frame.Z2 L1 L2 S Z).inv_mem ha.1, by
        have h := wt_mul F hZ hZ2 ha.1 ((Frame.Z2 L1 L2 S Z).inv_mem ha.1)
        rw [mul_inv_cancel, wt_one, ha.2, zero_add] at h
        exact h.symm⟩ }
  have hle : Frame.Z2 L1 L2 S Z ≤ M := by
    refine conjClosure_le fun p hp w hw => ?_
    have hwZ2 : w ∈ Frame.Z2 L1 L2 S Z := le_conjClosure Z _ hw
    exact ⟨Z2_norm hp hwZ2, by rw [wt_conj hp, wt_Z F hZ hw]⟩
  exact (hle hz).2

end WtZ

section Key

@[expose] noncomputable def mkc (L1 L2 S : Subgroup G) (g : G) (hg : g ∈ P2 L1 L2 S) :
    ↥(P2 L1 L2 S) ⧸ Bq L1 L2 S := ((⟨g, hg⟩ : ↥(P2 L1 L2 S)) : ↥(P2 L1 L2 S) ⧸ Bq L1 L2 S)

omit [Finite G] in
theorem mkc_eq_iff {g g' : G} (hg : g ∈ P2 L1 L2 S) (hg' : g' ∈ P2 L1 L2 S) :
    mkc L1 L2 S g hg = mkc L1 L2 S g' hg' ↔ g⁻¹ * g' ∈ bigB L1 L2 S := by
  unfold mkc
  rw [QuotientGroup.eq]
  exact Iff.rfl

variable (F : Frame L1 L2 S D X)
include F

theorem mkc_ne_mul {p p' r : G} (hp : p ∈ P2 L1 L2 S) (hp' : p' ∈ P2 L1 L2 S)
    (hpB : p ∉ bigB L1 L2 S) (hr : r ∈ Q1 L1 L2 S) (hrQ : r ∉ Q2 L1 L2 S) (hrp : r * p = p') :
    mkc L1 L2 S p hp ≠ mkc L1 L2 S p' hp' := by
  intro h
  rw [mkc_eq_iff] at h
  have e : p⁻¹ * p' = p⁻¹ * r * p := by rw [← hrp]; group
  rw [e] at h
  exact hrQ (Q1_inf_conj_le_Q2 F hp hpB hr h)

omit [Finite G] F in
theorem mkc_ne_one {p : G} (hp : p ∈ P2 L1 L2 S) (hpB : p ∉ bigB L1 L2 S) :
    mkc L1 L2 S (1 : G) (P2 L1 L2 S).one_mem ≠ mkc L1 L2 S p hp := by
  intro h
  rw [mkc_eq_iff] at h
  apply hpB
  simpa using h

omit [Finite G] F in
theorem not_mem_B_mul {u p : G} (hu : u ∈ bigB L1 L2 S) (hpB : p ∉ bigB L1 L2 S) :
    u * p ∉ bigB L1 L2 S := fun h => hpB (by
  have := (bigB L1 L2 S).mul_mem ((bigB L1 L2 S).inv_mem hu) h
  simpa using this)

omit [Finite G] F in
theorem mem_Q2_conj_iff {y r : G} (hy : y ∈ P2 L1 L2 S) :
    y * r * y⁻¹ ∈ Q2 L1 L2 S ↔ r ∈ Q2 L1 L2 S := by
  have := Subgroup.mem_normalizer_iff.mp (P2_le_normalizer_Q2 L1 L2 S hy) r
  exact this.symm

theorem Q1_mem_P2 {x : G} (hx : x ∈ Q1 L1 L2 S) : x ∈ P2 L1 L2 S :=
  (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S) (Q1_le_B F hx)

variable (hZ : ZData L1 L2 S Z)
include hZ

theorem sum_four (hZ2 : ¬ Frame.Z2 L1 L2 S Z ≤ Q1 L1 L2 S) {a g y q : G}
    (ha : a ∈ Frame.Z2 L1 L2 S Z) (haQ : a ∉ Q1 L1 L2 S)
    (hg : g ∈ P2 L1 L2 S) (hgB : g ∉ bigB L1 L2 S) (hy : y ∈ Q1 L1 L2 S) (hq : q ∈ Q1 L1 L2 S)
    (hyQ : y ∉ Q2 L1 L2 S) (hqQ : q ∉ Q2 L1 L2 S) (hyq : y * q ∉ Q2 L1 L2 S)
    (hyq' : y * q⁻¹ ∉ Q2 L1 L2 S) :
    coord L1 L2 S g a + coord L1 L2 S (y⁻¹ * g) a + coord L1 L2 S (q⁻¹ * g) a +
      coord L1 L2 S (q⁻¹ * (y⁻¹ * g)) a = 1 := by
  classical
  have hyi : y⁻¹ ∈ Q1 L1 L2 S := (Q1 L1 L2 S).inv_mem hy
  have hqi : q⁻¹ ∈ Q1 L1 L2 S := (Q1 L1 L2 S).inv_mem hq
  have hyg : y⁻¹ * g ∈ P2 L1 L2 S :=
    (P2 L1 L2 S).mul_mem (Q1_mem_P2 F hyi) hg
  have hqg : q⁻¹ * g ∈ P2 L1 L2 S := (P2 L1 L2 S).mul_mem (Q1_mem_P2 F hqi) hg
  have hqyg : q⁻¹ * (y⁻¹ * g) ∈ P2 L1 L2 S := (P2 L1 L2 S).mul_mem (Q1_mem_P2 F hqi) hyg
  have hygB : y⁻¹ * g ∉ bigB L1 L2 S := not_mem_B_mul (Q1_le_B F hyi) hgB
  have hqgB : q⁻¹ * g ∉ bigB L1 L2 S := not_mem_B_mul (Q1_le_B F hqi) hgB
  have hqygB : q⁻¹ * (y⁻¹ * g) ∉ bigB L1 L2 S := not_mem_B_mul (Q1_le_B F hqi) hygB
  have hy2 : y⁻¹ ∉ Q2 L1 L2 S := fun h => hyQ (by simpa using (Q2 L1 L2 S).inv_mem h)
  have hq2 : q⁻¹ ∉ Q2 L1 L2 S := fun h => hqQ (by simpa using (Q2 L1 L2 S).inv_mem h)
  have hyq2 : q⁻¹ * y⁻¹ ∉ Q2 L1 L2 S := fun h => hyq (by
    have := (Q2 L1 L2 S).inv_mem h
    simpa using this)
  have hyyP : y ∈ P2 L1 L2 S := Q1_mem_P2 F hy
  have hqqP : q ∈ P2 L1 L2 S := Q1_mem_P2 F hq
  set c0 := mkc L1 L2 S (1 : G) (P2 L1 L2 S).one_mem with hc0
  set m1 := mkc L1 L2 S g hg with hm1
  set m2 := mkc L1 L2 S (y⁻¹ * g) hyg with hm2
  set m3 := mkc L1 L2 S (q⁻¹ * g) hqg with hm3
  set m4 := mkc L1 L2 S (q⁻¹ * (y⁻¹ * g)) hqyg with hm4
  have h01 : c0 ≠ m1 := mkc_ne_one hg hgB
  have h02 : c0 ≠ m2 := mkc_ne_one hyg hygB
  have h03 : c0 ≠ m3 := mkc_ne_one hqg hqgB
  have h04 : c0 ≠ m4 := mkc_ne_one hqyg hqygB
  have h12 : m1 ≠ m2 := mkc_ne_mul F hg hyg hgB hyi hy2 rfl
  have h13 : m1 ≠ m3 := mkc_ne_mul F hg hqg hgB hqi hq2 rfl
  have h14 : m1 ≠ m4 :=
    mkc_ne_mul F hg hqyg hgB ((Q1 L1 L2 S).mul_mem hqi hyi) hyq2 (by group)
  have h23 : m2 ≠ m3 := by
    refine mkc_ne_mul F hyg hqg hygB (r := q⁻¹ * y) ((Q1 L1 L2 S).mul_mem hqi hy) ?_ (by group)
    intro h
    apply hyq'
    have := (mem_Q2_conj_iff hyyP (r := q⁻¹ * y)).mpr h
    have e : y * (q⁻¹ * y) * y⁻¹ = y * q⁻¹ := by group
    rw [e] at this
    exact this
  have h24 : m2 ≠ m4 := mkc_ne_mul F hyg hqyg hygB hqi hq2 rfl
  have h34 : m3 ≠ m4 := by
    refine mkc_ne_mul F hqg hqyg hqgB (r := q⁻¹ * y⁻¹ * q)
      ((Q1 L1 L2 S).mul_mem ((Q1 L1 L2 S).mul_mem hqi hyi) hq) ?_ (by group)
    intro h
    apply hyQ
    have := (mem_Q2_conj_iff hqqP (r := q⁻¹ * y⁻¹ * q)).mpr h
    have e : q * (q⁻¹ * y⁻¹ * q) * q⁻¹ = y⁻¹ := by group
    rw [e] at this
    simpa using (Q2 L1 L2 S).inv_mem this
  have hnd : [c0, m1, m2, m3, m4].Nodup := by
    simp [List.nodup_cons, h01, h02, h03, h04, h12, h13, h14, h23, h24, h34]
  have hcard : Fintype.card (↥(P2 L1 L2 S) ⧸ Bq L1 L2 S) = 5 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index]
    exact F.pair.relIndex_bigB_right
  have hu : (Finset.univ : Finset (↥(P2 L1 L2 S) ⧸ Bq L1 L2 S)) = {c0, m1, m2, m3, m4} := by
    symm
    apply Finset.eq_univ_of_card
    rw [hcard]
    simp [List.nodup_cons] at hnd
    simp [Finset.card_insert_of_notMem, hnd]
  have hwt := wt_Z2 F hZ hZ2 ha
  unfold wt at hwt
  rw [hu] at hwt
  simp [List.nodup_cons] at hnd
  simp only [Finset.sum_insert, hnd, Finset.sum_singleton, not_false_eq_true,
    Finset.mem_insert, Finset.mem_singleton, or_self] at hwt
  have hc0v : coordc L1 L2 S a c0 = 1 := by
    show coord L1 L2 S ((1 : ↥(P2 L1 L2 S)) : G) a = 1
    rw [coord_eq_one_iff]
    simpa using haQ
  rw [hc0v] at hwt
  have e1 : coordc L1 L2 S a m1 = coord L1 L2 S g a := rfl
  have e2 : coordc L1 L2 S a m2 = coord L1 L2 S (y⁻¹ * g) a := rfl
  have e3 : coordc L1 L2 S a m3 = coord L1 L2 S (q⁻¹ * g) a := rfl
  have e4 : coordc L1 L2 S a m4 = coord L1 L2 S (q⁻¹ * (y⁻¹ * g)) a := rfl
  rw [e1, e2, e3, e4] at hwt
  have h' : 1 + (coord L1 L2 S g a + coord L1 L2 S (y⁻¹ * g) a + coord L1 L2 S (q⁻¹ * g) a +
      coord L1 L2 S (q⁻¹ * (y⁻¹ * g)) a) = 0 := by
    linear_combination hwt
  have key : ∀ s : ZMod 2, 1 + s = 0 → s = 1 := by decide
  exact key _ h'

@[expose] def kc (y q a : G) : G :=
  y * (q * a * q⁻¹ * a⁻¹) * y⁻¹ * (q * a * q⁻¹ * a⁻¹)⁻¹

omit hZ in
theorem kc_mem {a y q : G}
    (ha : a ∈ Frame.Z2 L1 L2 S Z) (hy : y ∈ Q1 L1 L2 S) (hq : q ∈ Q1 L1 L2 S) :
    kc y q a ∈ Frame.Z2 L1 L2 S Z := by
  have hqa : q * a * q⁻¹ ∈ Frame.Z2 L1 L2 S Z := Z2_norm (Q1_mem_P2 F hq) ha
  have hw : q * a * q⁻¹ * a⁻¹ ∈ Frame.Z2 L1 L2 S Z :=
    (Frame.Z2 L1 L2 S Z).mul_mem hqa ((Frame.Z2 L1 L2 S Z).inv_mem ha)
  have hyw : y * (q * a * q⁻¹ * a⁻¹) * y⁻¹ ∈ Frame.Z2 L1 L2 S Z := Z2_norm (Q1_mem_P2 F hy) hw
  exact (Frame.Z2 L1 L2 S Z).mul_mem hyw ((Frame.Z2 L1 L2 S Z).inv_mem hw)

theorem key_coord (hZ2 : ¬ Frame.Z2 L1 L2 S Z ≤ Q1 L1 L2 S) {a g y q : G}
    (ha : a ∈ Frame.Z2 L1 L2 S Z) (haQ : a ∉ Q1 L1 L2 S)
    (hg : g ∈ P2 L1 L2 S) (hgB : g ∉ bigB L1 L2 S) (hy : y ∈ Q1 L1 L2 S) (hq : q ∈ Q1 L1 L2 S)
    (hyQ : y ∉ Q2 L1 L2 S) (hqQ : q ∉ Q2 L1 L2 S) (hyq : y * q ∉ Q2 L1 L2 S)
    (hyq' : y * q⁻¹ ∉ Q2 L1 L2 S) :
    coord L1 L2 S g (kc y q a) = 1 := by
  have hsum := sum_four F hZ hZ2 ha haQ hg hgB hy hq hyQ hqQ hyq hyq'
  have haa : a * a = 1 := F.Z2_sq hZ a ha
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hqP := Q1_mem_P2 F hq
  have hyP := Q1_mem_P2 F hy
  have hqa : q * a * q⁻¹ ∈ Frame.Z2 L1 L2 S Z := Z2_norm hqP ha
  have hw : q * a * q⁻¹ * a⁻¹ ∈ Frame.Z2 L1 L2 S Z :=
    (Frame.Z2 L1 L2 S Z).mul_mem hqa ((Frame.Z2 L1 L2 S Z).inv_mem ha)
  have hww : (q * a * q⁻¹ * a⁻¹) * (q * a * q⁻¹ * a⁻¹) = 1 := F.Z2_sq hZ _ hw
  have hwi : (q * a * q⁻¹ * a⁻¹)⁻¹ = q * a * q⁻¹ * a⁻¹ := inv_eq_of_mul_eq_one_right hww
  have hcw : ∀ g' : G, g' ∈ P2 L1 L2 S →
      coord L1 L2 S g' (q * a * q⁻¹ * a⁻¹) =
        coord L1 L2 S (q⁻¹ * g') a + coord L1 L2 S g' a := by
    intro g' hg'
    rw [coord_add F hZ hZ2 hg' hqa ((Frame.Z2 L1 L2 S Z).inv_mem ha), coord_conj, hai]
  have hyg : y⁻¹ * g ∈ P2 L1 L2 S := (P2 L1 L2 S).mul_mem ((P2 L1 L2 S).inv_mem hyP) hg
  have hyw : y * (q * a * q⁻¹ * a⁻¹) * y⁻¹ ∈ Frame.Z2 L1 L2 S Z := Z2_norm hyP hw
  unfold kc
  rw [coord_add F hZ hZ2 hg hyw ((Frame.Z2 L1 L2 S Z).inv_mem hw), coord_conj, hwi,
    hcw _ hyg, hcw _ hg]
  linear_combination hsum

theorem kc_avg_ne_one (hZ2 : ¬ Frame.Z2 L1 L2 S Z ≤ Q1 L1 L2 S) {a y q d : G}
    (ha : a ∈ Frame.Z2 L1 L2 S Z) (haQ : a ∉ Q1 L1 L2 S)
    (hy : y ∈ Q1 L1 L2 S) (hq : q ∈ Q1 L1 L2 S)
    (hyQ : y ∉ Q2 L1 L2 S) (hqQ : q ∉ Q2 L1 L2 S) (hyq : y * q ∉ Q2 L1 L2 S)
    (hyq' : y * q⁻¹ ∉ Q2 L1 L2 S) (hd : d ∈ D) :
    kc y q a * (d * kc y q a * d⁻¹) * (d⁻¹ * kc y q a * d) ≠ 1 := by
  have hdB : d ∈ bigB L1 L2 S := F.D_le_B hd
  have hdP : d ∈ P2 L1 L2 S := (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S) hdB
  have hdiB : d⁻¹ ∈ bigB L1 L2 S := (bigB L1 L2 S).inv_mem hdB
  have hdiP : d⁻¹ ∈ P2 L1 L2 S := (P2 L1 L2 S).inv_mem hdP
  obtain ⟨g, hg, hgB⟩ : ∃ g ∈ P2 L1 L2 S, g ∉ bigB L1 L2 S := by
    by_contra hcon
    push Not at hcon
    have h1 : (bigB L1 L2 S).relIndex (P2 L1 L2 S) = 1 :=
      Subgroup.relIndex_eq_one.mpr (fun g hg => hcon g hg)
    have h5 := F.pair.relIndex_bigB_right
    rw [h1] at h5
    exact absurd h5 (by norm_num)
  have hh := kc_mem F ha hy hq
  have hh2 : d * kc y q a * d⁻¹ ∈ Frame.Z2 L1 L2 S Z := Z2_norm hdP hh
  have hh3 : d⁻¹ * kc y q a * d ∈ Frame.Z2 L1 L2 S Z := Z2_norm_inv hdP hh
  have k1 := key_coord F hZ hZ2 ha haQ hg hgB hy hq hyQ hqQ hyq hyq'
  have k2 := key_coord F hZ hZ2 ha haQ ((P2 L1 L2 S).mul_mem hdiP hg)
    (not_mem_B_mul hdiB hgB) hy hq hyQ hqQ hyq hyq'
  have k3 := key_coord F hZ hZ2 ha haQ ((P2 L1 L2 S).mul_mem hdP hg)
    (not_mem_B_mul hdB hgB) hy hq hyQ hqQ hyq hyq'
  have c2 : coord L1 L2 S g (d * kc y q a * d⁻¹) = 1 := by rw [coord_conj]; exact k2
  have c3 : coord L1 L2 S g (d⁻¹ * kc y q a * d) = 1 := by
    have := coord_conj (L1 := L1) (L2 := L2) (S := S) d⁻¹ g (kc y q a)
    simp only [inv_inv] at this
    rw [this]
    exact k3
  intro h1
  have hcoord : coord L1 L2 S g (kc y q a * (d * kc y q a * d⁻¹) * (d⁻¹ * kc y q a * d)) = 1 := by
    rw [coord_add F hZ hZ2 hg ((Frame.Z2 L1 L2 S Z).mul_mem hh hh2) hh3,
      coord_add F hZ hZ2 hg hh hh2, k1, c2, c3]
    decide
  rw [h1] at hcoord
  have : coord L1 L2 S g (1 : G) = 0 := by
    rw [coord_eq_zero_iff]
    simp
  rw [this] at hcoord
  exact absurd hcoord (by decide)

end Key

end Wt

end CFSG.Quasithin.Kleidman.F204
