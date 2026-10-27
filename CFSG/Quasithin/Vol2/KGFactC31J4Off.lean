module

public import CFSG.Quasithin.Background.F918U8
public import CFSG.Quasithin.Background.F918U2
public import CFSG.Quasithin.Background.F918U6
public import CFSG.Quasithin.Background.F918U7
public import CFSG.Quasithin.Background.F918T7

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.KGC31.Off5

open CFSG.Quasithin CFSG.Quasithin.D35Chk CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.B5.Ln (mat dmat)
open scoped Matrix

@[expose] def fd0 : Nat :=
  Nat.land (Nat.land (Nat.land (look fdTab 1024 1) (look fdTab 1024 2)) (look fdTab 1024 8))
    (look fdTab 1024 64)

@[expose] def nodeOK5 (nd : Node) : Bool :=
  Nat.beq nd.m 0 || !(Nat.ble 10 (Nat.add nd.m (pivotDim nd.FD))) ||
    (Nat.beq nd.m 4 && Nat.beq nd.FD fd0)

@[expose] def runAux5 : Nat → List (Node × Nat) → Bool
  | 0, st => st.isEmpty
  | _ + 1, [] => true
  | f + 1, (nd, rem) :: rest =>
    bif Nat.beq rem 0 then runAux5 f rest else
      let g := topBit rem
      let ch := childOf nd g
      nodeOK5 ch && runAux5 f ((ch, ch.M) :: (nd, Nat.xor rem (Nat.pow 2 g)) :: rest)

@[expose] def run5 : Bool := runAux5 20000 [(root, root.M)]

attribute [local irreducible] invMask

@[expose] def Cov5 (nd : Node) (rem : ℕ) : Prop :=
  ∀ g, rem.testBit g = true → ∀ nd', Relation.ReflTransGen Step (childOf nd g) nd' →
    nodeOK5 nd' = true

private theorem topBit_spec {r : ℕ} (h0 : r ≠ 0) (h1 : r < 2 ^ 1024) :
    r.testBit (topBit r) = true ∧ topBit r < 1024 := by
  rw [topBit_eq_log2 (Nat.pos_of_ne_zero h0) h1]
  exact ⟨Nat.testBit_log2 h0, (Nat.log2_lt h0).2 h1⟩

private theorem xor_pow_lt {r g : ℕ} (h1 : r < 2 ^ 1024) (hg : g < 1024) : r ^^^ 2 ^ g < 2 ^ 1024 :=
  Nat.xor_lt_two_pow h1 (Nat.pow_lt_pow_right Nat.one_lt_two hg)

private theorem testBit_xor_pow (r g g' : ℕ) :
    (r ^^^ 2 ^ g).testBit g' = (r.testBit g' ^^ decide (g = g')) := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow]

theorem runAux5_sound : ∀ (f : ℕ) (st : List (Node × ℕ)), (∀ fr ∈ st, fr.2 < 2 ^ 1024) →
    runAux5 f st = true → ∀ fr ∈ st, Cov5 fr.1 fr.2 := by
  intro f
  induction f with
  | zero =>
    intro st _ h fr hfr
    have : st = [] := by simpa [runAux5] using h
    subst this
    simp at hfr
  | succ f ih =>
    intro st hlt h
    rcases st with _ | ⟨⟨nd, rem⟩, rest⟩
    · intro fr hfr
      simp at hfr
    · have hrest : ∀ fr ∈ rest, fr.2 < 2 ^ 1024 := fun fr hfr =>
        hlt fr (List.mem_cons_of_mem _ hfr)
      have hrem : rem < 2 ^ 1024 := hlt (nd, rem) List.mem_cons_self
      by_cases h0 : rem = 0
      · subst h0
        have h' : runAux5 f rest = true := by simpa [runAux5] using h
        intro fr hfr
        rcases List.mem_cons.1 hfr with rfl | hfr
        · intro g hg
          simp at hg
        · exact ih rest hrest h' fr hfr
      · obtain ⟨hbit, hg1024⟩ := topBit_spec h0 hrem
        have hb : Nat.beq rem 0 = false := by
          rw [Bool.eq_false_iff]
          intro hb
          exact h0 (Nat.eq_of_beq_eq_true hb)
        have h' : nodeOK5 (childOf nd (topBit rem)) = true ∧
            runAux5 f ((childOf nd (topBit rem), (childOf nd (topBit rem)).M) ::
              (nd, Nat.xor rem (Nat.pow 2 (topBit rem))) :: rest) = true := by
          simpa [runAux5, hb] using h
        obtain ⟨hok, hrec⟩ := h'
        have hlt' : ∀ fr ∈ ((childOf nd (topBit rem), (childOf nd (topBit rem)).M) ::
              (nd, Nat.xor rem (Nat.pow 2 (topBit rem))) :: rest), fr.2 < 2 ^ 1024 := by
          intro fr hfr
          rcases List.mem_cons.1 hfr with rfl | hfr
          · exact childOf_M_lt _ _
          · rcases List.mem_cons.1 hfr with rfl | hfr
            · exact xor_pow_lt hrem hg1024
            · exact hrest fr hfr
        have key := ih _ hlt' hrec
        have hCh := key (childOf nd (topBit rem), (childOf nd (topBit rem)).M)
          List.mem_cons_self
        have hNd := key (nd, Nat.xor rem (Nat.pow 2 (topBit rem))) (by simp)
        intro fr hfr
        rcases List.mem_cons.1 hfr with rfl | hfr
        · intro g' hg' nd' hpath
          by_cases hgg : g' = topBit rem
          · subst hgg
            rcases Relation.ReflTransGen.cases_head hpath with rfl | ⟨c, ⟨g'', hg'', rfl⟩, hrest'⟩
            · exact hok
            · exact hCh g'' hg'' nd' hrest'
          · refine hNd g' ?_ nd' hpath
            simp only [Nat.pow_eq, Nat.xor_eq]
            rw [testBit_xor_pow, hg']
            simp [Ne.symm hgg]
        · exact ih _ hlt' hrec _ (by simp [hfr])

private theorem root_M_lt : root.M < 2 ^ 1024 := by
  simp only [root]
  exact invMask_lt

private theorem run5_eq : run5 = runAux5 20000 [(root, root.M)] := rfl

theorem run5_sound (h : run5 = true) : ∀ nd, Reach nd → nodeOK5 nd = true := by
  rw [run5_eq] at h
  have hlt : ∀ fr ∈ [(root, root.M)], fr.2 < 2 ^ 1024 := by
    intro fr hfr
    rw [List.mem_singleton] at hfr
    subst hfr
    exact root_M_lt
  have hcov : Cov5 root root.M :=
    runAux5_sound 20000 [(root, root.M)] hlt h (root, root.M) List.mem_cons_self
  intro nd hnd
  rcases Relation.ReflTransGen.cases_head hnd with rfl | ⟨c, ⟨g, hg, rfl⟩, hrest⟩
  · simp [nodeOK5, root]
  · exact hcov g hg nd hrest

attribute [local irreducible] D35Chk.cmTab D35Chk.fxTab D35Chk.fdTab D35Chk.nbTab D35Chk.full

private theorem isSub_land {a b : ℕ} (ha : D35Chk.IsSub a) (hb : D35Chk.IsSub b) :
    D35Chk.IsSub (a &&& b) := by
  refine ⟨Nat.and_lt_two_pow a hb.1, fun c d hc hd => ?_⟩
  rw [Nat.testBit_and, Bool.and_eq_true] at hc hd ⊢
  exact ⟨ha.2 c d hc.1 hd.1, hb.2 c d hc.2 hd.2⟩

private theorem isSub_land' {a b : ℕ} (ha : D35Chk.IsSub a) (hb : D35Chk.IsSub b) :
    D35Chk.IsSub (Nat.land a b) :=
  isSub_land ha hb

private theorem testBit_land (a b i : ℕ) :
    (Nat.land a b).testBit i = (a.testBit i && b.testBit i) :=
  Nat.testBit_and a b i

private theorem full_eq : D35Chk.full = D35Chk.kerMask (D35Chk.packRows fun _ => 0) := by
  decide +kernel

private theorem colSum_zero_cols (c : ℕ) : D35Chk.colSum (fun _ => 0) c = 0 := by
  unfold D35Chk.colSum
  exact List.foldl_fixed' (fun b => by simp only [Nat.mul_eq, Nat.mul_zero, Nat.xor_eq,
    Nat.xor_zero]) _

private theorem testBit_full {c : ℕ} (hc : c < 1024) : D35Chk.full.testBit c = true := by
  rw [full_eq]
  exact (D35Chk.kerMask_testBit _ c).2 ⟨hc, fun u _ => by rw [colSum_zero_cols, Nat.zero_testBit]⟩

private theorem isSub_full : D35Chk.IsSub D35Chk.full ∧ D35Chk.full.testBit 0 = true := by
  rw [full_eq]
  exact D35Chk.isSub_kerMask _

private theorem card_le_pivot {α : Type*} [Finite α] {S : ℕ} (hS : D35Chk.IsSub S)
    (h0 : S.testBit 0 = true) (f : α → ℕ) (hf : Function.Injective f)
    (hmem : ∀ a, S.testBit (f a) = true) : Nat.card α ≤ 2 ^ D35Chk.pivotDim S := by
  have hlt : ∀ a, f a < 1024 := by
    intro a
    by_contra hge
    have hge := Nat.le_of_not_lt hge
    have hS' : S < 2 ^ f a :=
      lt_of_lt_of_le hS.1 (Nat.pow_le_pow_right Nat.two_pos hge)
    have := Nat.testBit_lt_two_pow hS'
    rw [hmem a] at this
    exact Bool.noConfusion this
  have hcard := D35Chk.card_filter_eq_two_pow_pivotDim hS h0
  let g : α → ((Finset.range 1024).filter fun c => S.testBit c = true) :=
    fun a => ⟨f a, by simp [hlt a, hmem a]⟩
  have hg : Function.Injective g := fun a b h => hf (congrArg Subtype.val h)
  calc Nat.card α ≤ Nat.card ((Finset.range 1024).filter fun c => S.testBit c = true) :=
        Nat.card_le_card_of_injective g hg
    _ = ((Finset.range 1024).filter fun c => S.testBit c = true).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = 2 ^ D35Chk.pivotDim S := hcard

private structure Corr5 (E F : Subgroup ↥(StatedSL 5 (ZMod 2))) (nd : D35Chk.Node) : Prop where
  reach : D35Chk.Reach nd
  le : F ≤ E
  card : Nat.card F = 2 ^ nd.m
  fd : ∀ B : ↥(altMat 5),
    (∀ g ∈ F, dmat g * (B : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (dmat g)ᵀ = B) →
      nd.FD.testBit (D35Chk.codeOfMat (B : Matrix (Fin 5) (Fin 5) (ZMod 2))) = true
  subD : D35Chk.IsSub nd.FD ∧ nd.FD.testBit 0 = true
  cand : ∀ x ∈ E, x ∉ F → (∀ y ∈ F, codeOf x ≤ codeOf (x * y)) → nd.M.testBit (codeOf x) = true

private theorem exists_min_code {S : Set ↥(StatedSL 5 (ZMod 2))} (hS : S.Nonempty) :
    ∃ g ∈ S, ∀ y ∈ S, codeOf g ≤ codeOf y := by
  classical
  have h : ∃ n, ∃ x ∈ S, codeOf x = n := ⟨_, hS.some, hS.some_mem, rfl⟩
  obtain ⟨x, hx, hxn⟩ := Nat.find_spec h
  refine ⟨x, hx, fun y hy => ?_⟩
  rw [hxn]
  exact Nat.find_min' h ⟨y, hy, rfl⟩

private theorem corr_root {E : Subgroup ↥(StatedSL 5 (ZMod 2))} (hEU : E ≤ unitri5)
    (hsq : ∀ a ∈ E, a * a = 1) : Corr5 E ⊥ D35Chk.root where
  reach := Relation.ReflTransGen.refl
  le := bot_le
  card := by
    show Nat.card (⊥ : Subgroup ↥(StatedSL 5 (ZMod 2))) = 2 ^ 0
    rw [Subgroup.card_bot]
    rfl
  fd := fun B _ => by
    show D35Chk.full.testBit _ = true
    exact testBit_full (codeOfMat_lt _)
  subD := isSub_full
  cand := fun x hxE hxF _ => by
    show D35Chk.invMask.testBit (codeOf x) = true
    rw [D35Chk.testBit_invMask]
    exact ⟨codeOf_lt x, isInv_codeOf (hEU hxE) (hsq x hxE) (by simpa using hxF)⟩

private theorem Corr5.step {E F : Subgroup ↥(StatedSL 5 (ZMod 2))} {nd : D35Chk.Node} [Finite E]
    (hEU : E ≤ unitri5) (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hsq : ∀ a ∈ E, a * a = 1)
    (hC : Corr5 E F nd) (hne : ∃ x ∈ E, x ∉ F) :
    ∃ (F' : Subgroup ↥(StatedSL 5 (ZMod 2))) (nd' : D35Chk.Node), Corr5 E F' nd' ∧
      Nat.card F < Nat.card F' := by
  classical
  obtain ⟨g, ⟨hgE, hgF⟩, hgmin⟩ := exists_min_code
    (S := {x | x ∈ E ∧ x ∉ F}) (by obtain ⟨x, hx, hxF⟩ := hne; exact ⟨x, hx, hxF⟩)
  have hgU : g ∈ unitri5 := hEU hgE
  have hg2 : g * g = 1 := hsq g hgE
  have hg1 : g ≠ 1 := fun h => hgF (h ▸ F.one_mem)
  have hinv : D35Chk.isInv (codeOf g) = true := isInv_codeOf hgU hg2 hg1
  have hlt : codeOf g < 1024 := codeOf_lt g
  have hcg0 : codeOf g ≠ 0 := fun h => hg1 (eq_one_of_codeOf_eq_zero hgU h)
  have hcoset : ∀ y ∈ F, codeOf g ≤ codeOf (g * y) := by
    intro y hy
    refine hgmin _ ⟨E.mul_mem hgE (hC.le hy), fun h => hgF ?_⟩
    simpa using F.mul_mem h (F.inv_mem hy)
  have hM : nd.M.testBit (codeOf g) = true := hC.cand g hgE hgF hcoset
  obtain ⟨F', hFF', hgF', hF'E, hcard⟩ := exists_ext hC.le hcomm hsq hgE hgF
  have hfd : (D35Chk.look D35Chk.fdTab 1024 (codeOf g)) =
      D35Chk.kerMask (D35Chk.packRows (D35Chk.fixColD (codeOf g))) := D35Chk.look_fdTab hlt hinv
  have hcm : (D35Chk.look D35Chk.cmTab 1024 (codeOf g)) =
      D35Chk.kerMask (D35Chk.packRows (D35Chk.commCol (codeOf g))) := D35Chk.look_cmTab hlt hinv
  refine ⟨F', D35Chk.childOf nd (codeOf g), ⟨?_, hF'E, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact Relation.ReflTransGen.tail hC.reach ⟨codeOf g, hM, rfl⟩
  · rw [hcard, hC.card]
    show 2 * 2 ^ nd.m = 2 ^ (nd.m + 1)
    rw [pow_succ]
    ring
  · intro B hB
    have h1 := hC.fd B (fun y hy => hB y (hFF' hy))
    have h2 := testBit_fixColD hgU hg2 (hB g hgF')
    rw [← hfd] at h2
    show (Nat.land nd.FD (D35Chk.look D35Chk.fdTab 1024 (codeOf g))).testBit _ = true
    rw [Nat.land_eq, Nat.testBit_and, h1, h2]
    rfl
  · have hs : D35Chk.IsSub (D35Chk.look D35Chk.fdTab 1024 (codeOf g)) ∧
        (D35Chk.look D35Chk.fdTab 1024 (codeOf g)).testBit 0 = true := by
      rw [hfd]
      exact D35Chk.isSub_kerMask _
    refine ⟨isSub_land hC.subD.1 hs.1, ?_⟩
    show (Nat.land nd.FD (D35Chk.look D35Chk.fdTab 1024 (codeOf g))).testBit 0 = true
    rw [Nat.land_eq, Nat.testBit_and, hC.subD.2, hs.2]
    rfl
  · intro x hxE hxF' hmin'
    have hxF : x ∉ F := fun h => hxF' (hFF' h)
    have hxU : x ∈ unitri5 := hEU hxE
    have h1 : codeOf g < codeOf x := by
      rcases (hgmin x ⟨hxE, hxF⟩).lt_or_eq with h | h
      · exact h
      · exact absurd (codeOf_inj hgU hxU h) (fun hgx => hxF' (hgx ▸ hgF'))
    have h2 : nd.M.testBit (codeOf x) = true :=
      hC.cand x hxE hxF (fun y hy => hmin' y (hFF' hy))
    have h3 : (D35Chk.look D35Chk.cmTab 1024 (codeOf g)).testBit (codeOf x) = true := by
      rw [hcm]
      exact testBit_commCol hgU hxU (hcomm g hgE x hxE)
    have h4 : (D35Chk.look D35Chk.nbTab 1024 (D35Chk.topBit (codeOf g))).testBit (codeOf x) =
        true := by
      rw [D35Chk.topBit_eq_log2 (Nat.pos_of_ne_zero hcg0)
        (lt_of_lt_of_le hlt (Nat.lt_two_pow_self).le)]
      have hlog : Nat.log2 (codeOf g) < 10 := (Nat.log2_lt hcg0).2 hlt
      rw [D35Chk.testBit_look_nbTab hlog]
      refine ⟨codeOf_lt x, ?_⟩
      by_contra hbit
      have hbit' : (codeOf x).testBit (Nat.log2 (codeOf g)) = true := by simpa using hbit
      exact absurd (hmin' g hgF') (not_le.2 (codeOf_mul_lt hxU hgU hg1 hbit'))
    show (Nat.land (Nat.land (Nat.shiftLeft (Nat.shiftRight nd.M (Nat.add (codeOf g) 1))
      (Nat.add (codeOf g) 1)) (D35Chk.look D35Chk.cmTab 1024 (codeOf g)))
      (D35Chk.look D35Chk.nbTab 1024 (D35Chk.topBit (codeOf g)))).testBit (codeOf x) = true
    have e : codeOf g + 1 + (codeOf x - (codeOf g + 1)) = codeOf x := by omega
    simp only [Nat.land_eq, Nat.shiftLeft_eq', Nat.shiftRight_eq', Nat.add_eq, Nat.testBit_and,
      Nat.testBit_shiftLeft, Nat.testBit_shiftRight, e, h2, h3, h4, Bool.and_true]
    simpa using h1
  · rw [hcard]
    have : 0 < Nat.card F := Nat.card_pos
    omega

private theorem exists_corr_top {E : Subgroup ↥(StatedSL 5 (ZMod 2))} [Finite E]
    (hEU : E ≤ unitri5) (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hsq : ∀ a ∈ E, a * a = 1) :
    ∀ (n : ℕ) (F : Subgroup ↥(StatedSL 5 (ZMod 2))) (nd : D35Chk.Node),
      Nat.card E ≤ Nat.card F + n → Corr5 E F nd → ∃ nd', Corr5 E E nd' := by
  intro n
  induction n with
  | zero =>
    intro F nd hle hC
    obtain rfl : F = E := Subgroup.eq_of_le_of_card_ge hC.le (by omega)
    exact ⟨nd, hC⟩
  | succ n ih =>
    intro F nd hle hC
    by_cases hEF : ∃ x ∈ E, x ∉ F
    · obtain ⟨F', nd', hC', hlt⟩ := Corr5.step hEU hcomm hsq hC hEF
      exact ih F' nd' (by omega) hC'
    · obtain rfl : F = E := le_antisymm hC.le (fun x hx => by
        by_contra hx'
        exact hEF ⟨x, hx, hx'⟩)
      exact ⟨nd, hC⟩

theorem isSub_fd0 : D35Chk.IsSub fd0 ∧ fd0.testBit 0 = true := by
  have hinv : ∀ c ∈ [1, 2, 8, 64], c < 1024 ∧ D35Chk.isInv c = true := by decide +kernel
  have hs : ∀ c ∈ [1, 2, 8, 64], D35Chk.IsSub (look fdTab 1024 c) ∧
      (look fdTab 1024 c).testBit 0 = true := by
    intro c hc
    obtain ⟨h1, h2⟩ := hinv c hc
    rw [D35Chk.look_fdTab h1 h2]
    exact D35Chk.isSub_kerMask _
  have h1 := hs 1 (by simp)
  have h2 := hs 2 (by simp)
  have h8 := hs 8 (by simp)
  have h64 := hs 64 (by simp)
  have hsub : D35Chk.IsSub (Nat.land (Nat.land (Nat.land (look fdTab 1024 1) (look fdTab 1024 2))
      (look fdTab 1024 8)) (look fdTab 1024 64)) :=
    isSub_land' (isSub_land' (isSub_land' h1.1 h2.1) h8.1) h64.1
  have h0 : (Nat.land (Nat.land (Nat.land (look fdTab 1024 1) (look fdTab 1024 2))
      (look fdTab 1024 8)) (look fdTab 1024 64)).testBit 0 = true := by
    rw [testBit_land, testBit_land, testBit_land, h1.2, h2.2, h8.2, h64.2]
    rfl
  unfold fd0
  exact ⟨hsub, h0⟩

theorem pivotDim_fd0 : D35Chk.pivotDim fd0 = 6 := by decide +kernel

theorem fd0_bits : ∀ p ∈ [2, 4, 5, 7, 8, 9], fd0.testBit (2 ^ p) = true := by decide +kernel

@[expose] def IsOff (E : Subgroup ↥(StatedSL 5 (ZMod 2))) : Prop :=
  E ≠ ⊥ ∧ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a * a = 1) ∧
    2 ^ 10 ≤ Nat.card E * Nat.card {B : ↥(altMat 5) //
      ∀ g ∈ E, dmat g * (B : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (dmat g)ᵀ = B}

theorem offender_unitri (h : run5 = true) {E : Subgroup ↥(StatedSL 5 (ZMod 2))}
    (hEU : E ≤ unitri5) (hE : IsOff E) :
    Nat.card E = 2 ^ 4 ∧ ∀ c < 1024, fd0.testBit c = true → ∀ g ∈ E,
      dmat g * D35Chk.bm (D35Chk.altSum c) * (dmat g)ᵀ = D35Chk.bm (D35Chk.altSum c) := by
  obtain ⟨hEne, hcomm, hsq, hoff⟩ := hE
  have : Finite E := inferInstance
  obtain ⟨nd, hnd⟩ := exists_corr_top hEU hcomm hsq (Nat.card E) ⊥ D35Chk.root
    (by omega) (corr_root hEU hsq)
  have hok := run5_sound h nd hnd.reach
  have hm : nd.m ≠ 0 := by
    intro h0
    apply hEne
    apply Subgroup.eq_bot_of_card_eq
    rw [hnd.card, h0]
    rfl
  have hinj : Function.Injective (fun B : {B : ↥(altMat 5) //
      ∀ g ∈ E, dmat g * (B : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (dmat g)ᵀ = B} =>
        D35Chk.codeOfMat (B.1 : Matrix (Fin 5) (Fin 5) (ZMod 2))) := by
    intro B C hBC
    apply Subtype.ext
    apply Subtype.ext
    have h1 := bm_altSum_codeOfMat B.1.2
    have h2 := bm_altSum_codeOfMat C.1.2
    simp only at hBC
    rw [← h1, ← h2, hBC]
  have hcD : Nat.card {B : ↥(altMat 5) //
      ∀ g ∈ E, dmat g * (B : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (dmat g)ᵀ = B} ≤
        2 ^ D35Chk.pivotDim nd.FD :=
    card_le_pivot hnd.subD.1 hnd.subD.2 _ hinj (fun B => hnd.fd B.1 B.2)
  have h2 : 10 ≤ nd.m + D35Chk.pivotDim nd.FD := by
    by_contra hlt
    have hlt := Nat.lt_of_not_ge hlt
    have : Nat.card E * Nat.card {B : ↥(altMat 5) //
        ∀ g ∈ E, dmat g * (B : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (dmat g)ᵀ = B} < 2 ^ 10 :=
      calc _ ≤ 2 ^ nd.m * 2 ^ D35Chk.pivotDim nd.FD := Nat.mul_le_mul hnd.card.le hcD
        _ = 2 ^ (nd.m + D35Chk.pivotDim nd.FD) := (pow_add _ _ _).symm
        _ < 2 ^ 10 := Nat.pow_lt_pow_right Nat.one_lt_two hlt
    omega
  unfold nodeOK5 at hok
  have hb : Nat.beq nd.m 0 = false := by
    rw [Bool.eq_false_iff]
    intro hb
    exact hm (Nat.eq_of_beq_eq_true hb)
  have hb2 : Nat.ble 10 (Nat.add nd.m (D35Chk.pivotDim nd.FD)) = true := by
    simpa [Nat.ble_eq] using h2
  rw [hb, hb2] at hok
  simp only [Bool.false_or, Bool.not_true, Bool.and_eq_true] at hok
  obtain ⟨hm4, hFD⟩ := hok
  have hm4' : nd.m = 4 := Nat.eq_of_beq_eq_true hm4
  have hFD' : nd.FD = fd0 := Nat.eq_of_beq_eq_true hFD
  have hcardE : Nat.card E = 2 ^ 4 := by rw [hnd.card, hm4']
  refine ⟨hcardE, ?_⟩
  have hCge : 2 ^ 6 ≤ Nat.card {B : ↥(altMat 5) //
      ∀ g ∈ E, dmat g * (B : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (dmat g)ᵀ = B} := by
    rw [hcardE] at hoff
    have e1 : (2 : ℕ) ^ 10 = 2 ^ 4 * 2 ^ 6 := by norm_num
    rw [e1] at hoff
    exact Nat.le_of_mul_le_mul_left hoff (by norm_num)
  have hS := D35Chk.card_filter_eq_two_pow_pivotDim isSub_fd0.1 isSub_fd0.2
  rw [pivotDim_fd0] at hS
  let φ : {B : ↥(altMat 5) //
      ∀ g ∈ E, dmat g * (B : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (dmat g)ᵀ = B} →
      ((Finset.range 1024).filter fun c => fd0.testBit c = true) := fun B =>
    ⟨D35Chk.codeOfMat (B.1 : Matrix (Fin 5) (Fin 5) (ZMod 2)), by
      have h1 := hnd.fd B.1 B.2
      rw [hFD'] at h1
      simp [codeOfMat_lt, h1]⟩
  have hφ : Function.Injective φ := fun B C hBC => hinj (congrArg Subtype.val hBC)
  have hbij := hφ.bijective_of_nat_card_le (by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, hS]
    exact hCge)
  intro c hc hcf g hg
  obtain ⟨B, hB⟩ := hbij.2 ⟨c, by simp [hc, hcf]⟩
  have hBc : D35Chk.codeOfMat (B.1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) = c :=
    congrArg Subtype.val hB
  have hBm : D35Chk.bm (D35Chk.altSum c) = (B.1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) := by
    rw [← hBc]
    exact bm_altSum_codeOfMat B.1.2
  rw [hBm]
  exact B.2 g hg

private theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by fin_cases x <;> rfl

private theorem zmod2_eq_zero_of_ne_one (x : ZMod 2) (h : x ≠ 1) : x = 0 := by
  fin_cases x
  · rfl
  · exact absurd rfl h

theorem mem_unitri5_of_rows {g : ↥(StatedSL 5 (ZMod 2))}
    (hg : ∀ i j : Fin 5, i ≠ 0 → mat g i j = if i = j then 1 else 0) : g ∈ unitri5 := by
  intro i j hji
  have hi : i ≠ 0 := fun h => by subst h; exact absurd hji (Fin.not_lt_zero j)
  rw [hg i j hi, ite_eq_right (ne_of_gt hji)]

theorem mul_self_of_rows {g : ↥(StatedSL 5 (ZMod 2))}
    (hg : ∀ i j : Fin 5, i ≠ 0 → mat g i j = if i = j then 1 else 0) : g * g = 1 := by
  have h00 : mat g 0 0 = 1 := mat_diag_of_mem_unitri5 (mem_unitri5_of_rows hg) 0
  have r1 := fun j => hg 1 j (by decide)
  have r2 := fun j => hg 2 j (by decide)
  have r3 := fun j => hg 3 j (by decide)
  have r4 := fun j => hg 4 j (by decide)
  apply B5.Ln.mat_injective
  rw [B5.Ln.mat_mul, B5.Ln.mat_one]
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  by_cases hi : i = 0
  · subst hi
    rw [Fin.sum_univ_five, r1, r2, r3, r4]
    fin_cases j <;> simp [zmod2_add_self, h00]
  · simp only [hg i _ hi, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true]

@[expose] def T0 : Subgroup ↥(StatedSL 5 (ZMod 2)) where
  carrier := {g | ∀ i j : Fin 5, i ≠ 0 → mat g i j = if i = j then 1 else 0}
  one_mem' := fun i j _ => by rw [B5.Ln.mat_one, Matrix.one_apply]
  mul_mem' := fun {a b} ha hb i j hi => by
    rw [B5.Ln.mat_mul, Matrix.mul_apply]
    simp only [ha i _ hi, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact hb i j hi
  inv_mem' := fun {a} ha => by
    have h := inv_eq_of_mul_eq_one_right (mul_self_of_rows ha)
    show ∀ i j : Fin 5, i ≠ 0 → mat a⁻¹ i j = if i = j then 1 else 0
    rw [h]
    exact ha

theorem card_T0_le : Nat.card T0 ≤ 2 ^ 4 := by
  have hinj : Function.Injective
      (fun g : T0 => fun j : Fin 4 => mat (g : ↥(StatedSL 5 (ZMod 2))) 0 j.succ) := by
    intro g h hgh
    apply Subtype.ext
    apply B5.Ln.mat_injective
    ext i j
    by_cases hi : i = 0
    · subst hi
      by_cases hj : j = 0
      · subst hj
        rw [mat_diag_of_mem_unitri5 (mem_unitri5_of_rows g.2) 0,
          mat_diag_of_mem_unitri5 (mem_unitri5_of_rows h.2) 0]
      · obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj
        exact congrFun hgh j'
    · rw [g.2 i j hi, h.2 i j hi]
  calc Nat.card T0 ≤ Nat.card (Fin 4 → ZMod 2) := Nat.card_le_card_of_injective _ hinj
    _ = 2 ^ 4 := by rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem fix_chk : ∀ c < 1024, D35Chk.isInv c = true →
    (∀ p ∈ [2, 4, 5, 7, 8, 9], D35Chk.bmul (D35Chk.bmul (D35Chk.bT (D35Chk.unitri c))
      (D35Chk.altSum (2 ^ p))) (D35Chk.unitri c) = D35Chk.altSum (2 ^ p)) →
    Nat.land c 948 = 0 := by
  decide +kernel

theorem exists_pos : ∀ i j : Fin 5, i ≠ 0 → i < j →
    ∃ p < 10, D35Chk.upI p = i ∧ D35Chk.upJ p = j ∧ Nat.testBit 948 p = true := by
  decide

theorem le_T0 {g : ↥(StatedSL 5 (ZMod 2))} (hg : g ∈ unitri5) (hsq : g * g = 1)
    (hfix : ∀ p ∈ [2, 4, 5, 7, 8, 9], dmat g * D35Chk.bm (D35Chk.altSum (2 ^ p)) * (dmat g)ᵀ =
      D35Chk.bm (D35Chk.altSum (2 ^ p))) : g ∈ T0 := by
  by_cases h1 : g = 1
  · rw [h1]
    exact T0.one_mem
  have hinv := isInv_codeOf hg hsq h1
  have hd : dmat g = (D35Chk.bm (D35Chk.unitri (codeOf g)))ᵀ := by
    rw [bm_unitri_codeOf hg, B5.Ln.dmat, inv_eq_of_mul_eq_one_right hsq]
  have hland : Nat.land (codeOf g) 948 = 0 := by
    refine fix_chk (codeOf g) (codeOf_lt g) hinv fun p hp => ?_
    apply D35Chk.bm_inj (D35Chk.bmul_lt _ _) (D35Chk.colSum_lt (fun q => D35Chk.altE_lt q) _)
    rw [D35Chk.bm_bmul, D35Chk.bm_bmul, D35Chk.bm_bT]
    have := hfix p hp
    rw [hd, Matrix.transpose_transpose] at this
    exact this
  intro i j hi
  rcases lt_trichotomy j i with hji | rfl | hij
  · rw [mem_unitri5.1 hg i j hji, ite_eq_right (ne_of_gt hji)]
  · rw [mat_diag_of_mem_unitri5 hg, ite_eq_left rfl]
  · rw [ite_eq_right (ne_of_lt hij)]
    obtain ⟨p, hp, hpi, hpj, hbit⟩ := exists_pos i j hi hij
    have hc : (codeOf g).testBit p = false := by
      have h2 := congrArg (fun x => Nat.testBit x p) hland
      simp only [Nat.zero_testBit] at h2
      rw [testBit_land, hbit, Bool.and_true] at h2
      exact h2
    have h3 := testBit_codeOfMat (mat g) hp
    rw [hpi, hpj] at h3
    have h4 : (codeOf g).testBit p = decide (mat g i j = 1) := h3
    rw [hc] at h4
    exact zmod2_eq_zero_of_ne_one _ fun h => by simp [h] at h4

private theorem congr_congr (M N B : Matrix (Fin 5) (Fin 5) (ZMod 2)) :
    M * (N * B * Nᵀ) * Mᵀ = M * N * B * (M * N)ᵀ := by
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

private theorem card_fix_le_map_conj (E : Subgroup ↥(StatedSL 5 (ZMod 2)))
    (h : ↥(StatedSL 5 (ZMod 2))) :
    Nat.card {B : ↥(altMat 5) //
        ∀ g ∈ E, dmat g * (B : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (dmat g)ᵀ = B} ≤
      Nat.card {B : ↥(altMat 5) //
        ∀ g ∈ E.map (MulAut.conj h).toMonoidHom,
          dmat g * (B : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (dmat g)ᵀ = B} := by
  have hinv : dmat h⁻¹ * dmat h = 1 := B5.Ln.dmat_inv_mul h
  have hfix : ∀ B : {B : ↥(altMat 5) //
        ∀ g ∈ E, dmat g * (B : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (dmat g)ᵀ = B},
      ∀ g ∈ E.map (MulAut.conj h).toMonoidHom,
        dmat g * (dmat h * (B.1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (dmat h)ᵀ) * (dmat g)ᵀ =
          dmat h * (B.1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (dmat h)ᵀ := by
    rintro B _ ⟨y, hy, rfl⟩
    have hgh : (MulAut.conj h).toMonoidHom y * h = h * y := by simp
    rw [congr_congr, ← B5.Ln.dmat_mul, hgh, B5.Ln.dmat_mul, ← congr_congr, B.2 y hy]
  refine Nat.card_le_card_of_injective
    (fun B => ⟨⟨dmat h * (B.1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (dmat h)ᵀ,
      congr_mem_altMat _ B.1.2⟩, hfix B⟩) ?_
  intro B C hBC
  have h1 : dmat h * (B.1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (dmat h)ᵀ =
      dmat h * C.1 * (dmat h)ᵀ :=
    congrArg (fun D => ((D.1 : ↥(altMat 5)) : Matrix (Fin 5) (Fin 5) (ZMod 2))) hBC
  have h2 := congrArg (fun D => dmat h⁻¹ * D * (dmat h⁻¹)ᵀ) h1
  simp only [congr_congr, hinv, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one] at h2
  exact Subtype.ext (Subtype.ext h2)

theorem IsOff.conj {E : Subgroup ↥(StatedSL 5 (ZMod 2))} (hE : IsOff E)
    (h : ↥(StatedSL 5 (ZMod 2))) : IsOff (E.map (MulAut.conj h).toMonoidHom) := by
  obtain ⟨hE1, hcomm, hsq, hoff⟩ := hE
  have hinj : Function.Injective (MulAut.conj h).toMonoidHom := (MulAut.conj h).injective
  refine ⟨fun h0 => hE1 ((Subgroup.map_eq_bot_iff_of_injective E hinj).mp h0), ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, hsq a ha, map_one]
  · rw [Subgroup.card_map_of_injective hinj]
    exact hoff.trans (Nat.mul_le_mul_left _ (card_fix_le_map_conj E h))

theorem isPGroup_of_sq {E : Subgroup ↥(StatedSL 5 (ZMod 2))} (hsq : ∀ a ∈ E, a * a = 1) :
    IsPGroup 2 ↥E := fun g =>
  ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, sq]; exact hsq g.1 g.2)⟩

theorem eq_T0_of_le_unitri (h : run5 = true) {E : Subgroup ↥(StatedSL 5 (ZMod 2))}
    (hEU : E ≤ unitri5) (hE : IsOff E) : E = T0 := by
  obtain ⟨hcard, hfix⟩ := offender_unitri h hEU hE
  have hlt : ∀ p ∈ [2, 4, 5, 7, 8, 9], 2 ^ p < 1024 := by decide
  have hle : E ≤ T0 := fun g hg => le_T0 (hEU hg) (hE.2.2.1 g hg) fun p hp =>
    hfix (2 ^ p) (hlt p hp) (fd0_bits p hp) g hg
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard]; exact card_T0_le)

theorem map_conj_inv_map_conj (E : Subgroup ↥(StatedSL 5 (ZMod 2)))
    (g : ↥(StatedSL 5 (ZMod 2))) :
    (E.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = E := by
  rw [Subgroup.map_map]
  have : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id _ := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [this, Subgroup.map_id]

theorem exists_eq_conj_T0 (h : run5 = true) {E : Subgroup ↥(StatedSL 5 (ZMod 2))}
    (hE : IsOff E) : ∃ x : ↥(StatedSL 5 (ZMod 2)), E = T0.map (MulAut.conj x).toMonoidHom := by
  obtain ⟨g, hg⟩ := exists_conj_le_unitri5 (isPGroup_of_sq hE.2.2.1)
  have hU : E.map (MulAut.conj g).toMonoidHom ≤ unitri5 := by
    rintro _ ⟨y, hy, rfl⟩
    exact hg y hy
  refine ⟨g⁻¹, ?_⟩
  rw [← eq_T0_of_le_unitri h hU (hE.conj g), map_conj_inv_map_conj]

theorem offender_unique (h : run5 = true) {P : Subgroup ↥(StatedSL 5 (ZMod 2))}
    (hP : IsPGroup 2 ↥P) {E₁ E₂ : Subgroup ↥(StatedSL 5 (ZMod 2))} (h₁ : E₁ ≤ P) (h₂ : E₂ ≤ P)
    (o₁ : IsOff E₁) (o₂ : IsOff E₂) : E₁ = E₂ := by
  obtain ⟨g, hg⟩ := exists_conj_le_unitri5 hP
  have hU : ∀ E ≤ P, E.map (MulAut.conj g).toMonoidHom ≤ unitri5 := fun E hE => by
    rintro _ ⟨y, hy, rfl⟩
    exact hg y (hE hy)
  have e₁ := eq_T0_of_le_unitri h (hU E₁ h₁) (o₁.conj g)
  have e₂ := eq_T0_of_le_unitri h (hU E₂ h₂) (o₂.conj g)
  exact Subgroup.map_injective (MulAut.conj g).injective (e₁.trans e₂.symm)

@[expose] def stab0 : Subgroup ↥(StatedSL 5 (ZMod 2)) where
  carrier := {g | ∀ i : Fin 5, mat g i 0 = if i = 0 then 1 else 0}
  one_mem' := fun i => by rw [B5.Ln.mat_one, Matrix.one_apply]
  mul_mem' := fun {a b} ha hb i => by
    rw [B5.Ln.mat_mul, Matrix.mul_apply]
    simp only [hb _, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact ha i
  inv_mem' := fun {a} ha i => by
    have h := congrFun (congrFun (B5.Ln.mat_inv_mul a) i) 0
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    simp only [ha _, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true] at h
    exact h

theorem mem_stab0 {g : ↥(StatedSL 5 (ZMod 2))} :
    g ∈ stab0 ↔ ∀ i : Fin 5, mat g i 0 = if i = 0 then 1 else 0 := Iff.rfl

@[expose] noncomputable def tv01 : ↥(StatedSL 5 (ZMod 2)) :=
  specialLinearGroupEquivStatedSL 5 (ZMod 2)
    ⟨Matrix.transvection 0 1 1, Matrix.det_transvection_of_ne 0 1 (by decide) 1⟩

theorem mat_tv01 : mat tv01 = Matrix.transvection (0 : Fin 5) 1 (1 : ZMod 2) :=
  specialLinearGroupEquivStatedSL_coe 5 (ZMod 2) _

theorem tv01_mem_T0 : tv01 ∈ T0 := by
  intro i j hi
  rw [mat_tv01, Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  simp [Ne.symm hi]

theorem normalizer_T0_le : Subgroup.normalizer (T0 : Set ↥(StatedSL 5 (ZMod 2))) ≤ stab0 := by
  intro γ hγ
  have hs : γ * tv01 * γ⁻¹ ∈ T0 := (Subgroup.mem_normalizer_iff.mp hγ tv01).mp tv01_mem_T0
  have h1 : mat γ * mat tv01 = mat (γ * tv01 * γ⁻¹) * mat γ := by
    rw [B5.Ln.mat_mul, B5.Ln.mat_mul, Matrix.mul_assoc (mat γ * mat tv01), B5.Ln.mat_inv_mul,
      Matrix.mul_one]
  have hcol : ∀ i : Fin 5, i ≠ 0 → mat γ i 0 = 0 := by
    intro i hi
    have h2 := congrFun (congrFun h1 i) 1
    rw [Matrix.mul_apply, Matrix.mul_apply] at h2
    simp only [hs i _ hi, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true] at h2
    rw [mat_tv01, Fin.sum_univ_five] at h2
    simp [Matrix.transvection] at h2
    exact h2
  intro i
  by_cases hi : i = 0
  · subst hi
    rw [ite_eq_left rfl]
    have h3 := congrFun (congrFun (B5.Ln.mat_inv_mul γ) 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_five, hcol 1 (by decide), hcol 2 (by decide),
      hcol 3 (by decide), hcol 4 (by decide)] at h3
    simp only [mul_zero, add_zero, Matrix.one_apply_eq] at h3
    by_contra hne
    rw [zmod2_eq_zero_of_ne_one _ hne, mul_zero] at h3
    exact zero_ne_one h3
  · rw [ite_eq_right hi]
    exact hcol i hi

end CFSG.Quasithin.KGC31.Off5

end
