module

public import CFSG.Certificates.CosetFacts
public import Certificates.Data.CFSGNative.YGroups.Check

public section

namespace CFSG.YGroups

open CFSG.Certificates.CosetEnumeration

namespace Native

theorem reduceStep_eq : Native.reduceStep = Certificates.CosetEnumeration.reduceStep := rfl

theorem freelyTrivial_eq : Native.freelyTrivial = Certificates.CosetEnumeration.freelyTrivial := rfl

theorem wordAt_eq : Native.wordAt = Certificates.CosetEnumeration.wordAt := by
  funext ws n
  induction ws generalizing n with
  | nil => cases n <;> rfl
  | cons w ws ih =>
    cases n with
    | zero => rfl
    | succ n => exact ih n

theorem refOK_eq : Native.refOK = Certificates.CosetEnumeration.refOK := rfl

theorem refNext_eq : Native.refNext = Certificates.CosetEnumeration.refNext := rfl

theorem walkOK_eq : Native.walkOK = Certificates.CosetEnumeration.walkOK := by
  funext fx fc fy inv refs f t o s q cur w
  induction w generalizing q cur with
  | nil => rfl
  | cons c w ih =>
    simp only [Native.walkOK, Certificates.CosetEnumeration.walkOK, ih, refOK_eq, refNext_eq]

theorem factOK_eq : Native.factOK = Certificates.CosetEnumeration.factOK := by
  funext N L' fx fc fy kind wi fs ft fo refs pl inv rels subs f
  simp only [Native.factOK, Certificates.CosetEnumeration.factOK, walkOK_eq, wordAt_eq]
  generalize kind f = k
  rcases k with _ | _ | _ | _ | k <;> rfl

theorem factsOK_eq : Native.factsOK = Certificates.CosetEnumeration.factsOK := by
  funext N L' fx fc fy kind wi fs ft fo refs pl inv rels subs lo n
  induction n generalizing lo with
  | zero => rfl
  | succ n ih => simp only [Native.factsOK, Certificates.CosetEnumeration.factsOK, ih, factOK_eq]

theorem liveCount_eq' : Native.liveCount = Certificates.CosetEnumeration.liveCount := by
  funext live n
  induction n with
  | zero => rfl
  | succ n ih => simp only [Native.liveCount, Certificates.CosetEnumeration.liveCount, ih]

theorem coverOK_eq : Native.coverOK = Certificates.CosetEnumeration.coverOK := by
  funext N L F fx fc fy inv ffi live lo n
  induction n generalizing lo with
  | zero => rfl
  | succ n ih => simp only [Native.coverOK, Certificates.CosetEnumeration.coverOK, ih, refOK_eq, refNext_eq]

end Native

variable {G : Type*} [Group G]

theorem letters_of_lettersOK {L : ℕ} {ws : List (List ℕ)} (h : Native.lettersOK L ws = true) :
    ∀ w ∈ ws, ∀ c ∈ w, c < L := by
  simp only [Native.lettersOK, List.all_eq_true, Nat.blt_eq] at h
  exact h

theorem evalWord_invWord {gen : ℕ → G} (hinv : ∀ c, gen c * gen c = 1) (w : List ℕ) :
    evalWord gen (Native.invWord Native.invId w) = (evalWord gen w)⁻¹ := by
  have hi : ∀ c, (gen c)⁻¹ = gen c := fun c => inv_eq_of_mul_eq_one_right (hinv c)
  induction w with
  | nil => simp [Native.invWord, evalWord]
  | cons c w ih =>
    simp only [Native.invWord, List.map_cons, List.reverse_cons] at ih ⊢
    rw [evalWord_append, ih, evalWord_cons gen c w, mul_inv_rev, hi]
    simp [evalWord, Native.invId]

theorem evalWord_rot_eq_one {gen : ℕ → G} {r : List ℕ} (hr : evalWord gen r = 1) {w : List ℕ}
    (h : Native.isRot w r = true) : evalWord gen w = 1 := by
  simp only [Native.isRot, List.any_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨i, hi, rfl⟩ := h
  rw [← List.rotate_eq_drop_append_take hi.le, evalWord, List.map_rotate]
  exact List.prod_rotate_eq_one_of_prod_eq_one hr i

theorem evalWord_of_relsOK {gen : ℕ → G} {L : ℕ} (hε : gen L = 1)
    (hinv : ∀ c, gen c * gen c = 1) {base ws : List (List ℕ)}
    (hbase : ∀ r ∈ base, evalWord gen r = 1)
    (h : Native.relsOK L Native.invId base ws = true) : ∀ w ∈ ws, evalWord gen w = 1 := by
  have hi : ∀ c < L, gen (Native.invId c) = (gen c)⁻¹ :=
    fun c _ => (inv_eq_of_mul_eq_one_right (hinv c)).symm
  intro w hw
  simp only [Native.relsOK, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true,
    List.any_eq_true, Nat.blt_eq] at h
  obtain ⟨hlet, htriv | ⟨r, hr, hrot | hrot⟩⟩ := h w hw
  · rw [Native.freelyTrivial_eq] at htriv
    exact evalWord_eq_one_of_freelyTrivial hε hi (fun c hc => Nat.lt_succ_iff.mp (hlet c hc)) htriv
  · rw [← evalWord_stripEps hε]
    exact evalWord_rot_eq_one (hbase r hr) hrot
  · rw [← evalWord_stripEps hε]
    refine evalWord_rot_eq_one ?_ hrot
    rw [evalWord_invWord hinv, hbase r hr, inv_one]

theorem index_le_of_enumOK {gen : ℕ → G} {L : ℕ} {base subs : List (List ℕ)} {maxPts k : ℕ}
    {H : Subgroup G} (hgen : Subgroup.closure (gen '' Set.Iio L) = ⊤) (hε : gen L = 1)
    (hinv : ∀ c, gen c * gen c = 1) (hbase : ∀ r ∈ base, evalWord gen r = 1)
    (hsubs : ∀ w ∈ subs, evalWord gen w ∈ H)
    (h : Native.enumOK L base subs maxPts k = true) : H.FiniteIndex ∧ H.index ≤ k := by
  set c := Native.certOf (Native.enumerate L (Array.range L) base subs maxPts)
  have h' : Native.certOK L base subs k c = true := h
  simp only [Native.certOK, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, beq_iff_eq] at h'
  obtain ⟨-, hN, hlive0, hsubsEq, hlet, hrels, hfacts, hcover, hk⟩ := h'
  rw [Native.factsOK_eq] at hfacts
  rw [Native.coverOK_eq] at hcover
  rw [Native.liveCount_eq'] at hk
  have hinv' : ∀ c ≤ L, gen (Native.invId c) = (gen c)⁻¹ :=
    fun c _ => (inv_eq_of_mul_eq_one_right (hinv c)).symm
  have hlet' := letters_of_lettersOK hlet
  have key := index_le_of_facts (H := H) (gen := gen) (L := L) (N := c.N) (F := c.facts.size)
    (rels := c.rels.toList) (subs := subs) (inv := Native.invId) (live := c.liveF)
    hgen hinv' (fun c hc => hc) (fun w hw c hc => Nat.lt_succ_iff.mp (hlet' w hw c hc))
    (evalWord_of_relsOK hε hinv hbase hrels) hsubs hlive0 hN hfacts hcover
  exact ⟨key.1, hk ▸ key.2⟩

end CFSG.YGroups
