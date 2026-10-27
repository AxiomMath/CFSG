
module

public import CFSG.Sporadic.SuzRecog.LevelTwoCoverDefsBase
import all CFSG.Sporadic.SuzRecog.LevelTwoCoverDefsBase

public import CFSG.Sporadic.SuzRecog.LevelTwoComplex
public import Certificates.Certificate15113
import CFSG.Certificates.Kernel.RankElimSound

public section

namespace CFSG.Sporadic.SuzRecog.LevelTwoCover

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog.LevelTwoData
  CFSG.Sporadic.SuzRecog.LevelTwoCoverData CFSG.Sporadic.SuzRecog.ElimCert
  CFSG.Sporadic.SuzRecog.LevelTwo

attribute [local irreducible] nbr volt nbrC vtab vtabs aPts wPts trips aIdx vIdx cells p1 cellReps
  shift deck

theorem cover_base_check : coverBaseOK = true :=
  Certificates.certificate15113.1

theorem cover_lift_check : coverLiftOK = true :=
  Certificates.certificate15113.2.1

theorem cover_deck_check : coverDeckOK = true :=
  Certificates.certificate15113.2.2.1

theorem cover_elim_check : CoverElim :=
  Certificates.certificate15113.2.2.2.1

theorem cover_loc_check : coverLocOK = true :=
  Certificates.certificate15113.2.2.2.2

theorem base_parts {x : ℕ} (hx : x < 2835) :
    (nbr[x]!).size = 36 ∧ ∀ k < 36, (nbr[x]!)[k]! < 2997 ∧ (nbr[x]!)[k]! ≠ x ∧
      (∀ k' < k, (nbr[x]!)[k']! ≠ (nbr[x]!)[k]!) ∧
      ((nbr[x]!)[k]! < 2835 → ∃ k' < 36, (nbr[(nbr[x]!)[k]!]!)[k']! = x ∧
        (volt[36 * x + k]! + volt[36 * (nbr[x]!)[k]! + k']!) % 3 = 0) := by
  have h : baseOf nbr volt = true := cover_base_check
  unfold baseOf at h
  have h1 := allLt_spec h hx
  simp only [Bool.and_eq_true, beq_iff_eq] at h1
  refine ⟨h1.1, fun k hk => ?_⟩
  have h2 := allLt_spec h1.2 hk
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
    List.any_eq_true, List.mem_range, beq_iff_eq] at h2
  obtain ⟨⟨⟨hlt, hne⟩, hdist⟩, hback⟩ := h2
  refine ⟨hlt, hne, fun k' hk' => ?_, fun hy => ?_⟩
  · have := allLt_spec hdist hk'
    simpa [bne_iff_ne] using this
  · rcases hback with hge | ⟨k', hk', e1, e2⟩
    · omega
    · exact ⟨k', hk', e1, e2⟩

theorem nbr_size {x : ℕ} (hx : x < 2835) : (nbr[x]!).size = 36 :=
  (base_parts hx).1

theorem nbr_lt {x : ℕ} (hx : x < 2835) {k : ℕ} (hk : k < 36) :
    (nbr[x]!)[k]! < 2997 :=
  ((base_parts hx).2 k hk).1

theorem nbr_ne {x : ℕ} (hx : x < 2835) {k : ℕ} (hk : k < 36) :
    (nbr[x]!)[k]! ≠ x :=
  ((base_parts hx).2 k hk).2.1

theorem nbr_inj {x : ℕ} (hx : x < 2835) {k₁ k₂ : ℕ}
    (h1 : k₁ < 36) (h2 : k₂ < 36) (h : (nbr[x]!)[k₁]! = (nbr[x]!)[k₂]!) : k₁ = k₂ := by
  rcases lt_trichotomy k₁ k₂ with hlt | heq | hgt
  · exact absurd h (((base_parts hx).2 k₂ h2).2.2.1 k₁ hlt)
  · exact heq
  · exact absurd h.symm (((base_parts hx).2 k₁ h1).2.2.1 k₂ hgt)

theorem nbr_back {x : ℕ} (hx : x < 2835) {k : ℕ} (hk : k < 36)
    (hy : (nbr[x]!)[k]! < 2835) : ∃ k' < 36, (nbr[(nbr[x]!)[k]!]!)[k']! = x ∧
      (volt[36 * x + k]! + volt[36 * (nbr[x]!)[k]! + k']!) % 3 = 0 :=
  ((base_parts hx).2 k hk).2.2.2 hy

theorem adj_iff_of_lt {x y : Fin 2997} (hx : x.1 < 2835) :
    Γ.Adj x y ↔ ∃ k < 36, (nbr[x.1]!)[k]! = y.1 := by
  constructor
  · rintro ⟨-, h | h⟩
    · obtain ⟨k, hk, e⟩ := occB_iff.1 h
      rw [nbr_size hx] at hk
      exact ⟨k, hk, e⟩
    · by_cases hy : y.1 < 2835
      · obtain ⟨k, hk, e⟩ := occB_iff.1 h
        rw [nbr_size hy] at hk
        obtain ⟨k', hk', e', -⟩ := nbr_back hy hk (by rw [e]; exact hx)
        rw [e] at e'
        exact ⟨k', hk', e'⟩
      · rw [occB_nbr_of_ge (by omega)] at h
        exact absurd h (by simp)
  · rintro ⟨k, hk, e⟩
    refine ⟨fun h => nbr_ne hx hk (by rw [e, h]), Or.inl (occB_iff.2 ⟨k, ?_, e⟩)⟩
    rw [nbr_size hx]
    exact hk

theorem nbrC_lt {u : ℕ} (hu : u < 8991) (hx : u % 2997 < 2835)
    {k : ℕ} (hk : k < 36) : (nbrC[u]!)[k]! < 8991 := by
  rw [nbrC_get hu hx hk]
  have := nbr_lt hx hk
  omega

theorem nbrC_mod {u : ℕ} (hu : u < 8991) (hx : u % 2997 < 2835)
    {k : ℕ} (hk : k < 36) : (nbrC[u]!)[k]! % 2997 = (nbr[u % 2997]!)[k]! := by
  rw [nbrC_get hu hx hk]
  have := nbr_lt hx hk
  omega

theorem nbrC_div {u : ℕ} (hu : u < 8991) (hx : u % 2997 < 2835)
    {k : ℕ} (hk : k < 36) :
    (nbrC[u]!)[k]! / 2997 = (u / 2997 + volt[36 * (u % 2997) + k]!) % 3 := by
  rw [nbrC_get hu hx hk]
  have := nbr_lt hx hk
  omega

theorem adjC_iff_of_lt {u w : Fin 8991} (hx : u.1 % 2997 < 2835) :
    Γc.Adj u w ↔ ∃ k < 36, (nbrC[u.1]!)[k]! = w.1 := by
  constructor
  · rintro ⟨-, h | h⟩
    · obtain ⟨k, hk, e⟩ := occB_iff.1 h
      rw [nbrC_size u.2 hx] at hk
      exact ⟨k, hk, e⟩
    · by_cases hw : w.1 % 2997 < 2835
      · obtain ⟨k, hk, e⟩ := occB_iff.1 h
        rw [nbrC_size w.2 hw] at hk
        have em := nbrC_mod w.2 hw hk
        have ed := nbrC_div w.2 hw hk
        rw [e] at em ed
        obtain ⟨k', hk', e1, e2⟩ := nbr_back hw hk (by rw [← em]; exact hx)
        refine ⟨k', hk', ?_⟩
        rw [← em] at e1 e2
        rw [nbrC_get u.2 hx hk', e1]
        have := w.2
        omega
      · rw [occB_nbrC_of_ge w.2 (by omega)] at h
        exact absurd h (by simp)
  · rintro ⟨k, hk, e⟩
    refine ⟨fun h => ?_, Or.inl (occB_iff.2 ⟨k, by rw [nbrC_size u.2 hx]; exact hk, e⟩)⟩
    have em := nbrC_mod u.2 hx hk
    rw [e, ← h] at em
    exact nbr_ne hx hk em.symm

theorem adj_pr {u w : Fin 8991} (h : Γc.Adj u w) :
    Γ.Adj (pr u) (pr w) := by
  by_cases hx : u.1 % 2997 < 2835
  · obtain ⟨k, hk, e⟩ := (adjC_iff_of_lt hx).1 h
    refine (adj_iff_of_lt (x := pr u) hx).2 ⟨k, hk, ?_⟩
    show (nbr[u.1 % 2997]!)[k]! = w.1 % 2997
    rw [← e, nbrC_mod u.2 hx hk]
  · obtain ⟨hw, k, hk, e⟩ := (adjC_iff_of_ge (by omega)).1 h
    refine ((adj_iff_of_lt (x := pr w) hw).2 ⟨k, hk, ?_⟩).symm
    show (nbr[w.1 % 2997]!)[k]! = u.1 % 2997
    rw [← e, nbrC_mod w.2 hw hk]

theorem adjC_inj {u w₁ w₂ : Fin 8991} (h1 : Γc.Adj u w₁)
    (h2 : Γc.Adj u w₂) (hp : pr w₁ = pr w₂) : w₁ = w₂ := by
  have hp' : w₁.1 % 2997 = w₂.1 % 2997 := congrArg Fin.val hp
  by_cases hx : u.1 % 2997 < 2835
  · obtain ⟨k₁, hk₁, e₁⟩ := (adjC_iff_of_lt hx).1 h1
    obtain ⟨k₂, hk₂, e₂⟩ := (adjC_iff_of_lt hx).1 h2
    have m₁ := nbrC_mod u.2 hx hk₁
    have m₂ := nbrC_mod u.2 hx hk₂
    rw [e₁] at m₁
    rw [e₂] at m₂
    have := nbr_inj hx hk₁ hk₂ (by rw [← m₁, ← m₂, hp'])
    subst this
    exact Fin.ext (e₁.symm.trans e₂)
  · obtain ⟨hw₁, k₁, hk₁, e₁⟩ := (adjC_iff_of_ge (by omega)).1 h1
    obtain ⟨hw₂, k₂, hk₂, e₂⟩ := (adjC_iff_of_ge (by omega)).1 h2
    have m₁ := nbrC_mod w₁.2 hw₁ hk₁
    have m₂ := nbrC_mod w₂.2 hw₂ hk₂
    have d₁ := nbrC_div w₁.2 hw₁ hk₁
    have d₂ := nbrC_div w₂.2 hw₂ hk₂
    rw [e₁] at m₁ d₁
    rw [e₂] at m₂ d₂
    rw [hp'] at m₁ d₁
    have := nbr_inj hw₂ hk₁ hk₂ (by rw [← m₁, ← m₂])
    subst this
    have := w₁.2
    have := w₂.2
    exact Fin.ext (by omega)

theorem coverDeckOK_parts :
    presAdj nbrC deckArr = true ∧
    eqA 1782 (powA 1782 (compA 1782 gens[0]! (compA 1782 gens[0]! gens[1]!)) 8) (idA 1782) =
      true ∧
    eqA 8991 (powA 8991 (compA 8991 (liftArr 0) (compA 8991 (liftArr 0) (liftArr 1))) 8)
      deckArr = true := by
  have h := cover_deck_check
  simp only [coverDeckOK, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem adj_deck {a b : Fin 8991} (h : Γc.Adj a b) :
    Γc.Adj (deck a) (deck b) :=
  presAdj_spec rep_deck coverDeckOK_parts.1 h

theorem preconnected_Γc : Γc.Preconnected := by
  obtain ⟨_, _, _, _, _, h⟩ := cover_elim_check
  exact CFSG.KC.RankElim.preconnected_of_ok h

theorem coverLiftOK_parts {s : ℕ} (hs : s < 2) :
    isInvA 8991 (liftArr s) (invCand 8991 (liftArr s)) = true ∧
      presAdj nbrC (liftArr s) = true := by
  have h := allLt_spec cover_lift_check hs
  simpa only [Bool.and_eq_true] using h

theorem rep_liftP {s : ℕ} (hs : s < 2) :
    Rep 8991 (liftArr s) (liftP s) :=
  (rep_permC (coverLiftOK_parts hs).1).1

theorem pr_liftP {s : ℕ}
    (hs : s < 2) (u : Fin 8991) : pr (liftP s u) = genElt s hs • pr u := by
  rw [genElt_smul]
  apply Fin.ext
  show (liftP s u).1 % 2997 = (vtab s)[u.1 % 2997]!
  rw [← rep_liftP hs u, liftArr_get u.2]
  have := (gens_vset hs (Nat.mod_lt u.1 (by norm_num : 0 < 2997))).1
  omega

theorem adj_liftP {s : ℕ} (hs : s < 2) {a b : Fin 8991}
    (h : Γc.Adj a b) : Γc.Adj (liftP s a) (liftP s b) :=
  presAdj_spec (rep_liftP hs) (coverLiftOK_parts hs).2 h

theorem adjC_smul (g : F) {a b : Fin 8991} (h : Γc.Adj a b) :
    Γc.Adj (g • a) (g • b) := by
  rw [smul_def, smul_def]
  revert a b
  refine F_induction (P := fun g => ∀ {a b : Fin 8991}, Γc.Adj a b → Γc.Adj (g.2 a) (g.2 b))
    (fun h => adj_liftP (s := 0) (by norm_num) h) (fun h => adj_liftP (s := 1) (by norm_num) h)
    (fun h => h) (fun x y hx hy a b h => hx (hy h)) g.2

theorem pr_smul (g : F)
    (u : Fin 8991) : pr (g • u) = projX g • pr u := by
  have key : ∃ h : (g : Equiv.Perm (Fin 1782) × Equiv.Perm (Fin 8991)).1 ∈ xGroup,
      ∀ u, pr ((g : Equiv.Perm (Fin 1782) × Equiv.Perm (Fin 8991)).2 u) =
        (⟨_, h⟩ : xGroup) • pr u := by
    refine F_induction (P := fun g => ∃ h : g.1 ∈ xGroup, ∀ u, pr (g.2 u) =
      (⟨g.1, h⟩ : xGroup) • pr u)
      ⟨gens_mem_xGroup (by norm_num), fun u => pr_liftP (s := 0) (by norm_num) u⟩
      ⟨gens_mem_xGroup (by norm_num), fun u => pr_liftP (s := 1) (by norm_num) u⟩
      ⟨one_mem _, fun u => (one_smul _ _).symm⟩ ?_ g.2
    rintro a b ⟨ha, hA⟩ ⟨hb, hB⟩
    refine ⟨mul_mem ha hb, fun u => ?_⟩
    rw [Prod.snd_mul, Equiv.Perm.mul_apply, hA, hB, ← mul_smul]
    rfl
  obtain ⟨_, H⟩ := key
  exact H u

theorem xt_word :
    (xt 0 * (xt 0 * xt 1)) ^ 8 = (1, deck) := by
  obtain ⟨-, h1, h2⟩ := coverDeckOK_parts
  have r0 := (rep_gens (s := 0) (by norm_num)).1
  have r1 := (rep_gens (s := 1) (by norm_num)).1
  have l0 := rep_liftP (s := 0) (by norm_num)
  have l1 := rep_liftP (s := 1) (by norm_num)
  refine Prod.ext ?_ ?_
  · rw [Prod.pow_fst]
    exact eq_of_eqA (rep_powA (rep_compA r0 (rep_compA r0 r1)) 8) rep_idA h1
  · rw [Prod.pow_snd]
    exact eq_of_eqA (rep_powA (rep_compA l0 (rep_compA l0 l1)) 8) rep_deck h2

theorem one_deck_mem :
    ((1, deck) : Equiv.Perm (Fin 1782) × Equiv.Perm (Fin 8991)) ∈ F := by
  rw [← xt_word]
  exact pow_mem (mul_mem (xt_mem (by norm_num)) (mul_mem (xt_mem (by norm_num))
    (xt_mem (by norm_num)))) 8

@[expose] noncomputable def d :
    F :=
  ⟨(1, deck), one_deck_mem⟩

theorem d_smul (u : Fin 8991) :
    d • u = deck u :=
  rfl

theorem projX_d : projX d = 1 :=
  rfl

theorem ker_projX :
    projX.ker = Subgroup.zpowers d := by
  refine le_antisymm (fun g hg => ?_) ((Subgroup.zpowers_le).2 projX_d)
  have hg1 : (g : Equiv.Perm (Fin 1782) × Equiv.Perm (Fin 8991)).1 = 1 :=
    congrArg Subtype.val (MonoidHom.mem_ker.1 hg)
  have hpr : ∀ u, pr ((g : Equiv.Perm (Fin 1782) × Equiv.Perm (Fin 8991)).2 u) = pr u := by
    intro u
    have := pr_smul g u
    rwa [MonoidHom.mem_ker.1 hg, one_smul] at this
  have hlift : ∀ σ : Equiv.Perm (Fin 8991), (∀ {a b}, Γc.Adj a b → Γc.Adj (σ a) (σ b)) →
      (∀ u, pr (σ u) = pr u) →
      σ 0 = (g : Equiv.Perm (Fin 1782) × Equiv.Perm (Fin 8991)).2 0 →
      (g : Equiv.Perm (Fin 1782) × Equiv.Perm (Fin 8991)).2 = σ := fun σ hσ hσp h0 =>
    Equiv.ext (congrFun (eq_of_adj_lift preconnected_Γc pr adjC_inj (fun h => adjC_smul g h) hσ
      (fun u => (hpr u).trans (hσp u).symm) h0.symm))
  have hdeckp : ∀ u, pr (deck u) = pr u := pr_deck
  rcases eq_or_deck (hpr 0) with e | e | e
  · have h2 := hlift 1 (fun h => h) (fun _ => rfl) e.symm
    refine Subgroup.mem_zpowers_iff.2 ⟨0, ?_⟩
    rw [zpow_zero]
    exact Subtype.ext (Prod.ext hg1.symm h2.symm)
  · have h2 := hlift deck (fun h => adj_deck h) hdeckp e.symm
    refine Subgroup.mem_zpowers_iff.2 ⟨1, ?_⟩
    rw [zpow_one]
    exact Subtype.ext (Prod.ext hg1.symm h2.symm)
  · have hm : ∀ u, (deck * deck) u = deck (deck u) := fun u => Equiv.Perm.mul_apply _ _ _
    have h2 := hlift (deck * deck) (fun {a b} h => by rw [hm, hm]; exact adj_deck (adj_deck h))
      (fun u => by rw [hm, pr_deck, pr_deck]) (by rw [hm]; exact e.symm)
    refine Subgroup.mem_zpowers_iff.2 ⟨2, ?_⟩
    rw [zpow_two]
    refine Subtype.ext (Prod.ext ?_ h2.symm)
    show (1 : Equiv.Perm (Fin 1782)) * 1 = _
    rw [hg1, one_mul]

theorem ker_proj :
    proj.ker = Subgroup.zpowers d := by
  rw [← ker_projX]
  ext g
  simp only [MonoidHom.mem_ker, proj, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]

theorem exists_lift (h : xGroup)
    {u v : Fin 8991} (huv : h • pr u = pr v) : ∃ g : F, projX g = h ∧ g • u = v := by
  obtain ⟨g₀, hg₀⟩ := projX_surjective h
  have hp : pr (g₀ • u) = pr v := by rw [pr_smul, hg₀, huv]
  rcases eq_or_deck hp with e | e | e
  · exact ⟨g₀, hg₀, e⟩
  · refine ⟨d⁻¹ * g₀, by rw [map_mul, map_inv, projX_d, inv_one, one_mul, hg₀], ?_⟩
    rw [mul_smul, e, ← d_smul, inv_smul_smul]
  · refine ⟨d⁻¹ * (d⁻¹ * g₀), by rw [map_mul, map_mul, map_inv, projX_d, inv_one, one_mul,
      one_mul, hg₀], ?_⟩
    rw [mul_smul, mul_smul, e, ← d_smul, ← d_smul, inv_smul_smul, inv_smul_smul]

theorem coverLocOK_parts :
    listedAt0 p1 = true ∧ listedAt0 2835 = true ∧
    (∀ k < 4, listedAt0 cellReps[k]! = true ∧ listedAt0 (cellVert' k) = true) ∧
    adjB nbrC p1c (cellc 0) = true ∧ adjB nbrC p1c (cellc 2) = true ∧
    adjB nbrC p1c (cellc 1) = false ∧ adjB nbrC p1c (cellc 3) = false ∧
    adjB nbrC p1c (cellc' 0) = true ∧ adjB nbrC p1c (cellc' 2) = true := by
  have h := cover_loc_check
  simp only [coverLocOK, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨h1, h2, fun k hk => ?_, h4, h5, h6, h7, h8, h9⟩
  have := allLt_spec h3 hk
  simpa only [Bool.and_eq_true] using this

theorem liftAt0_spec {y : ℕ} (hy : listedAt0 y = true) :
    ∃ h : liftAt0 y < 8991, liftAt0 y % 2997 = y ∧ Γc.Adj 0 ⟨liftAt0 y, h⟩ := by
  simp only [listedAt0, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hy
  obtain ⟨hk, e⟩ := hy
  have h00 : (0 : ℕ) % 2997 < 2835 := by norm_num
  have hlt := nbrC_lt (by norm_num : (0 : ℕ) < 8991) h00 hk
  have hm := nbrC_mod (by norm_num : (0 : ℕ) < 8991) h00 hk
  refine ⟨hlt, by rw [liftAt0, hm]; exact e, (adjC_iff_of_lt (u := 0) h00).2 ⟨_, hk, rfl⟩⟩

@[expose] def pt1 : Fin 8991 :=
  ⟨p1c, (liftAt0_spec coverLocOK_parts.1).1⟩

@[expose] def qt : Fin 8991 :=
  ⟨qc, (liftAt0_spec coverLocOK_parts.2.1).1⟩

private theorem pr_val (u : Fin 8991) : (pr u).val = u.val % 2997 := rfl

private theorem pt1_val : pt1.val = liftAt0 p1 := rfl

private theorem qt_val : qt.val = liftAt0 2835 := rfl

private theorem p1V_val : p1V.val = p1 := rfl

private theorem qV_val : qV.val = 2835 := rfl

theorem pr_pt1 : pr pt1 = p1V :=
  Fin.ext (by rw [pr_val, pt1_val, p1V_val]; exact (liftAt0_spec coverLocOK_parts.1).2.1)

theorem pr_qt : pr qt = qV :=
  Fin.ext (by rw [pr_val, qt_val, qV_val]; exact (liftAt0_spec coverLocOK_parts.2.1).2.1)

theorem adj_pt_pt1 : Γc.Adj pt pt1 :=
  (liftAt0_spec coverLocOK_parts.1).2.2

theorem adj_pt_qt : Γc.Adj pt qt :=
  (liftAt0_spec coverLocOK_parts.2.1).2.2

end CFSG.Sporadic.SuzRecog.LevelTwoCover
