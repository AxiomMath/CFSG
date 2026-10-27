module

public import CFSG.YGroups.DCE.B433Rules
public import CFSG.YGroups.DCE.OmegaBigSpec
public import Certificates.Data.CFSGNative.YGroups.DCE.B433Data
public meta import Certificates.Data.CFSGNative.YGroups.DCE.B433Data
public import Certificates.Certificate10093
public import Certificates.Certificate10095
public import Certificates.Certificate10098
public import Certificates.Certificate10100
public import Certificates.Certificate10101
public import Certificates.Certificate10102
public import Certificates.Certificate10103
public import CFSG.YGroups.Model233F

public section

namespace CFSG.YGroups.DCE.B433

open CFSG.YGroups.DCE.B433Native Pointwise
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons)

theorem lettersB_eq : lettersB () = y432FArrays.map (bofArr 31671) := rfl

theorem lettersB_size : (lettersB ()).size = 10 := by
  rw [lettersB_eq, Array.size_map]
  exact y432F_check.1

theorem lettersB_rep {l : ℕ} (hl : l < 10) :
    RepB 31671 (lettersB ())[l]! (rho432F (yGen 4 3 2 l)) := by
  have hl' : l < y432FArrays.size := by rw [y432F_check.1]; exact hl
  rw [lettersB_eq, BigOmega.getElem!_map_lt hl']
  exact repB_bofArr (by norm_num) (rho432F_rep hl)

theorem wordB_rep {L : Array ByteArray}
    (hL : ∀ l < 10, RepB 31671 L[l]! (rho432F (yGen 4 3 2 l))) (w : Array ℕ)
    (hw : ∀ l ∈ w, l < 10) :
    RepB 31671 (wordB L w) (rho432F (evalWord (yGen 4 3 2) w.toList)) := by
  have hw' : ∀ l ∈ w.toList, l < 10 := fun l hl => hw l (Array.mem_toList_iff.1 hl)
  unfold wordB
  rw [← Array.foldr_toList]
  generalize w.toList = ws at hw' ⊢
  induction ws with
  | nil =>
    simp only [List.foldr_nil, evalWord_nil, map_one]
    exact repB_bid (by norm_num)
  | cons a ws ih =>
    simp only [List.foldr_cons, evalWord_cons, map_mul]
    exact repB_bcomp (by norm_num) (hL a (hw' a List.mem_cons_self))
      (ih fun l hl => hw' l (List.mem_cons_of_mem _ hl))

private theorem foldl_inv {α β : Type} (P : β → Prop) (f : β → α → β) (init : β) (h0 : P init)
    (hf : ∀ b a, P b → P (f b a)) : ∀ l : List α, P (l.foldl f init) := by
  intro l
  induction l generalizing init with
  | nil => exact h0
  | cons a l ih => exact ih (f init a) (hf init a h0)

private theorem inner_lt (sm : UInt64 → UInt64 × UInt64) (s : UInt64) (k : ℕ) :
    ∀ l ∈ (List.foldl (fun b _ => ((sm b.1).1, #[((sm b.1).2 % 10).toNat] ++ b.2))
      (s, (#[] : Array ℕ)) (List.range' 0 k)).2, l < 10 := by
  refine foldl_inv (fun st : UInt64 × Array ℕ => ∀ l ∈ st.2, l < 10) _ _
    (by intro l hl; simp at hl) (fun b _ hb => ?_) _
  intro l hl
  simp only [Array.mem_append, Array.mem_singleton] at hl
  rcases hl with rfl | hl
  · rw [UInt64.toNat_mod]
    exact Nat.mod_lt _ (by decide)
  · exact hb l hl

theorem treeWords_lt : ∀ w ∈ treeWords, ∀ l ∈ w, l < 10 := by
  unfold treeWords
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, bind_pure_comp, map_pure]
  generalize splitmix = sm
  generalize (987654321 : UInt64) = s0
  refine foldl_inv (fun st : UInt64 × Array (Array ℕ) => ∀ w ∈ st.2, ∀ l ∈ w, l < 10) _ _
    (by intro w hw; simp at hw) (fun b _ hb => ?_) _
  intro w hw
  simp only [Array.mem_push] at hw
  rcases hw with hw | hw
  · exact hb w hw
  · rw [hw]
    exact inner_lt sm b.1 _

theorem treeGens_rep
    {L : Array ByteArray}
    (hL : ∀ l < 10, RepB 31671 L[l]! (rho432F (yGen 4 3 2 l))) (hsz : L.size = 10) :
    ∀ l < (treeGens L).size, ∃ e : YGroup 4 3 2, RepB 31671 (treeGens L)[l]! (rho432F e) := by
  intro l hl
  unfold treeGens at hl ⊢
  rw [Array.size_append, Array.size_map] at hl
  by_cases hlL : l < L.size
  · refine ⟨yGen 4 3 2 l, ?_⟩
    have e : (L ++ Array.map (wordB L) treeWords)[l]! = L[l]! := by
      rw [getElem!_pos (L ++ Array.map (wordB L) treeWords) l (by simpa using hl),
        Array.getElem_append_left hlL, getElem!_pos L l hlL]
    rw [e]
    exact hL l (by omega)
  · have hk : l - L.size < treeWords.size := by omega
    have e : (L ++ Array.map (wordB L) treeWords)[l]! = wordB L treeWords[l - L.size]! := by
      rw [getElem!_pos (L ++ Array.map (wordB L) treeWords) l (by simpa using hl),
        Array.getElem_append_right (by omega), Array.getElem_map, getElem!_pos treeWords _ hk]
    rw [e]
    exact ⟨_, wordB_rep hL _ (treeWords_lt _ (by
      rw [getElem!_pos treeWords _ hk]
      exact Array.getElem_mem hk))⟩

theorem gB_rep
    {L : Array ByteArray} (hL : ∀ l < 10, RepB 31671 L[l]! (rho432F (yGen 4 3 2 l))) :
    RepB 31671 (gB L) (rho432F gRel) := by
  refine repB_congr (wordB_rep hL #[1, 2, 5, 0, 8, 9] (by decide)) ?_
  simp only [gRel, evalWord_cons, evalWord_nil, mul_one, mul_assoc]

theorem relHs_spec
    {L : Array ByteArray} (hg : RepB 31671 (gB L) (rho432F gRel)) :
    (relHs L).size = 9 ∧ ∀ s < 9, RepB 31671 (relHs L)[s]! (rho432F (gRel ^ s)) := by
  have key : ∀ m, ((List.range m).foldl
        (fun acc (_ : ℕ) => acc.push (bcomp deg acc.back! (gB L))) #[bid deg]).size = m + 1 ∧
      ∀ s < m + 1, RepB 31671 ((List.range m).foldl
        (fun acc (_ : ℕ) => acc.push (bcomp deg acc.back! (gB L))) #[bid deg])[s]!
          (rho432F (gRel ^ s)) := by
    intro m
    induction m with
    | zero =>
      refine ⟨rfl, fun s hs => ?_⟩
      obtain rfl : s = 0 := by omega
      have h0 : (#[bid deg] : Array ByteArray)[0]! = bid deg := rfl
      rw [List.range_zero, List.foldl_nil, h0, pow_zero, map_one]
      exact repB_bid (n := 31671) (by norm_num)
    | succ m ih =>
      obtain ⟨hs, hrep⟩ := ih
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      generalize (List.foldl (fun acc (_ : ℕ) => acc.push (bcomp deg acc.back! (gB L)))
        #[bid deg] (List.range m)) = acc at hs hrep ⊢
      have hback : RepB 31671 acc.back! (rho432F (gRel ^ m)) := by
        have := hrep m (by omega)
        rw [Array.back!, hs, Nat.add_sub_cancel]
        exact this
      refine ⟨by rw [Array.size_push, hs], fun s hs' => ?_⟩
      by_cases hsm : s < m + 1
      · rw [getElem!_pos (acc.push _) s (by rw [Array.size_push]; omega), Array.getElem_push_lt
          (by omega), ← getElem!_pos acc s (by omega)]
        exact hrep s hsm
      · obtain rfl : s = m + 1 := by omega
        rw [getElem!_pos (acc.push _) (m + 1) (by rw [Array.size_push]; omega),
          Array.getElem_push, dite_eq_right (by omega), pow_succ, map_mul]
        exact repB_bcomp (by norm_num) hback hg
  exact key 8

theorem relPi_rep
    {L : Array ByteArray} (hg : RepB 31671 (gB L) (rho432F gRel))
    (hinv : bisInv deg (gB L) (binvCand deg (gB L)) = true) :
    RepB 31671 (relPi L) (rho432F (gRel⁻¹ ^ 9)) := by
  have hgi : RepB 31671 (binvCand deg (gB L)) (rho432F gRel⁻¹) := by
    rw [map_inv]
    exact repB_binv hg hinv
  have key : ∀ m, RepB 31671 ((List.range m).foldl
      (fun acc (_ : ℕ) => bcomp deg acc (binvCand deg (gB L))) (bid deg))
        (rho432F (gRel⁻¹ ^ m)) := by
    intro m
    induction m with
    | zero =>
      rw [List.range_zero, List.foldl_nil, pow_zero, map_one]
      exact repB_bid (n := 31671) (by norm_num)
    | succ m ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, pow_succ, map_mul]
      exact repB_bcomp (by norm_num) ih hgi
  exact key 9

structure Checked (L : Array ByteArray) (O : BigOmega) (cert : B.Cert) : Prop where
  hL : L = lettersB ()
  hO : O = omegaB433 L
  big : bigOK O L fixB = true
  small : smallOK O L cert = true

namespace Checked

variable {L : Array ByteArray} {O : BigOmega} {cert : B.Cert} (S : Checked L O cert)

include S

theorem letters_rep
    {l : ℕ} (hl : l < 10) : RepB 31671 L[l]! (rho432F (yGen 4 3 2 l)) := by
  rw [S.hL]
  exact lettersB_rep hl

theorem letters_size : L.size = 10 := by
  rw [S.hL]
  exact lettersB_size

theorem n_eq : O.n = 31671 := by
  rw [S.hO]
  rfl

theorem X0_eq : O.X0 = x0B := by
  rw [S.hO]
  rfl

theorem tg_eq : O.tg = treeGens L := by
  rw [S.hO]
  rfl

theorem small_spec : L.size = 10 ∧ O.N = 86316516 ∧
    bisInv deg (gB L) (binvCand deg (gB L)) = true ∧
    ∀ j < cert.words.size, j = 0 ∨ cert.words[j]!.1 < j := by
  have h := S.small
  unfold smallOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, fun j hj => ?_⟩
  have := CFSG.Monster.B.Co2.allLt_iff.1 h4 j hj
  simpa using this

theorem N_eq : O.N = 86316516 := S.small_spec.2.1

theorem exists_g :
    ∃ g : ℕ → Equiv.Perm (Fin 31671),
    ∀ l < O.tg.size, g l ∈ rho432F.range ∧ RepB 31671 O.tg[l]! (g l) := by
  have H : ∀ l < O.tg.size, ∃ γ ∈ rho432F.range, RepB 31671 O.tg[l]! γ := by
    intro l hl
    rw [S.tg_eq] at hl ⊢
    obtain ⟨e, he⟩ := treeGens_rep (fun l hl => S.letters_rep hl) S.letters_size l hl
    exact ⟨rho432F e, ⟨e, rfl⟩, he⟩
  choose! g hg using H
  exact ⟨g, fun l hl => ⟨(hg l hl).1, (hg l hl).2⟩⟩

theorem rowMem
    {p : ℕ} (hp : p < O.N) :
    BigOmega.rowFinset 31671 O p ∈ MulAction.orbit (YGroup 4 3 2) (listFinset 31671 x0B) := by
  obtain ⟨g, hg⟩ := S.exists_g
  have h1 := BigOmega.rowFinset_mem_orbit rho432F.range g hg S.big S.n_eq p hp
  rw [S.X0_eq] at h1
  rwa [orbit_eq]

theorem good :
    Good x0B := by
  obtain ⟨g, hg⟩ := S.exists_g
  refine ⟨fun l hl => ?_, ?_⟩
  · have hu : ∀ l < L.size, rho432F (yGen 4 3 2 l) ∈ rho432F.range ∧
        RepB 31671 L[l]! (rho432F (yGen 4 3 2 l)) :=
      fun l hl' => ⟨⟨_, rfl⟩, S.letters_rep (by rwa [S.letters_size] at hl')⟩
    have h := BigOmega.fix_smul_listFinset (O := O) rho432F.range
      (fun l => rho432F (yGen 4 3 2 l)) hu S.big l (by simp only [fixB, List.mem_cons]; omega)
    rw [S.X0_eq] at h
    exact h
  · have h := BigOmega.card_orbit_ge rho432F.range g hg S.big S.n_eq
    rw [S.X0_eq, ← orbit_eq, S.N_eq] at h
    exact h

theorem hcard :
    (MulAction.orbit rho432F.range (listFinset 31671 O.X0)).ncard ≤ O.N := by
  rw [S.X0_eq, ← orbit_eq, S.N_eq]
  exact ncard_orbit_le S.good

@[expose] def pt :
    ℕ → Pts x0B := fun p =>
  if hp : p < O.N then ⟨BigOmega.rowFinset 31671 O p, S.rowMem hp⟩ else basePt x0B

theorem pt_zero :
    S.pt 0 = basePt x0B := by
  have h0 : 0 < O.N := by rw [S.N_eq]; norm_num
  unfold pt
  rw [dite_eq_left h0]
  apply Subtype.ext
  show BigOmega.rowFinset 31671 O 0 = listFinset 31671 x0B
  rw [BigOmega.rowFinset_zero S.big, S.X0_eq]

theorem pt_of_lt
    {p : ℕ} (hp : p < O.N) : (S.pt p).1 = BigOmega.rowFinset 31671 O p := by
  unfold pt
  rw [dite_eq_left hp]

theorem act_pt
    {σ : ByteArray} {e : YGroup 4 3 2} (hσ : RepB 31671 σ (rho432F e)) {p : ℕ}
    (hp : p < O.N) : O.act σ p < O.N ∧ S.pt (O.act σ p) = e • S.pt p := by
  obtain ⟨g, hg⟩ := S.exists_g
  obtain ⟨h1, h2⟩ := BigOmega.act_spec rho432F.range g hg S.big S.n_eq S.hcard
    (e := ⟨rho432F e, e, rfl⟩) hσ hp
  refine ⟨h1, Subtype.ext ?_⟩
  rw [S.pt_of_lt h1]
  show _ = e • (S.pt p).1
  rw [S.pt_of_lt hp]
  exact h2

theorem actAll_pt
    {σ : ByteArray} {e : YGroup 4 3 2} (hσ : RepB 31671 σ (rho432F e)) {p : ℕ}
    (hp : p < O.N) :
    B.u32get (O.actAll σ) p < O.N ∧ S.pt (B.u32get (O.actAll σ) p) = e • S.pt p := by
  obtain ⟨g, hg⟩ := S.exists_g
  obtain ⟨-, h1, h2⟩ := BigOmega.actAll_spec rho432F.range g hg S.big S.n_eq S.hcard
    (e := ⟨rho432F e, e, rfl⟩) hσ (chunk := 16384) (by norm_num) hp
  have e1 : B.u32get (O.actAll σ) p = u32Entry (O.actAll σ) p := rfl
  rw [e1]
  refine ⟨h1, Subtype.ext ?_⟩
  rw [S.pt_of_lt h1]
  show _ = e • (S.pt p).1
  rw [S.pt_of_lt hp]
  exact h2

theorem pt_surj :
    ∀ ω : Pts x0B, ∃ p < O.N, S.pt p = ω := by
  obtain ⟨g, hg⟩ := S.exists_g
  have hT : (↑((Finset.range O.N).image (BigOmega.rowFinset 31671 O)) :
      Set (Finset (Fin 31671))) = MulAction.orbit rho432F.range (listFinset 31671 O.X0) :=
    Set.eq_of_subset_of_ncard_le (BigOmega.rows_subset_orbit rho432F.range g hg S.big S.n_eq)
      (by
        rw [Set.ncard_coe_finset, BigOmega.rows_card rho432F.range g hg S.big S.n_eq]
        exact S.hcard)
      (Set.toFinite _)
  intro ω
  have hω : ω.1 ∈ MulAction.orbit rho432F.range (listFinset 31671 O.X0) := by
    rw [S.X0_eq, ← orbit_eq]
    exact ω.2
  rw [← hT] at hω
  obtain ⟨j, hj, hjω⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hω)
  have hjN : j < O.N := Finset.mem_range.1 hj
  exact ⟨j, hjN, Subtype.ext (by rw [S.pt_of_lt hjN]; exact hjω)⟩

theorem nodesOK : NodesOK (ctxB433 O L cert) := by
  intro j i p hjp hj
  have hjp' : (cert.words.map fun w => (w.1, O.act (wordB L w.2) 0))[j]? = some (i, p) := hjp
  rw [Array.getElem?_map] at hjp'
  cases hw : cert.words[j]? with
  | none => rw [hw] at hjp'; simp at hjp'
  | some w =>
    rw [hw] at hjp'
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hjp'
    obtain ⟨hi, -⟩ := hjp'
    obtain ⟨hlt, hwj⟩ := Array.getElem?_eq_some_iff.1 hw
    have h4 := S.small_spec.2.2.2 j hlt
    rcases h4 with h4 | h4
    · omega
    · rw [getElem!_pos cert.words j hlt, hwj] at h4
      rw [← hi]
      exact h4

theorem actSpec :

    ActSpec (ctxB433 O L cert) S.pt := fun _ _ hσ _ hp => S.act_pt hσ hp

theorem actAllSpec :

    ∀ (σ : ByteArray) (e : YGroup 4 3 2), RepB 31671 σ (rho432F e) →
    ∀ p < (ctxB433 O L cert).N, B.u32get ((ctxB433 O L cert).actAll σ) p < (ctxB433 O L cert).N ∧
      S.pt (B.u32get ((ctxB433 O L cert).actAll σ) p) = e • S.pt p :=
  fun _ _ hσ _ hp => S.actAll_pt hσ hp

theorem ptSurj :

    ∀ ω : Pts x0B, ∃ p < (ctxB433 O L cert).N, S.pt p = ω := S.pt_surj

theorem ctxGood : CtxGood (ctxB433 O L cert) where
  n_eq := rfl
  N_pos := by
    show 0 < O.N
    rw [S.N_eq]
    norm_num
  letters_size := S.letters_size
  letters_rep := fun l hl => S.letters_rep hl
  cl_eq := rfl
  one_rep := repB_bid (n := 31671) (by norm_num)
  rels_ok := by
    have hg := gB_rep (L := L) fun l hl => S.letters_rep hl
    obtain ⟨hsz, hhs⟩ := relHs_spec hg
    exact rels_ok_single (hs := relHs L) (π := relPi L) rfl hsz hhs
      (relPi_rep hg S.small_spec.2.2.1)

@[expose] def finalCheck
    (order bound : ℕ) : Bool :=
  (env S.good S.ctxGood S.pt S.pt_zero S.actSpec S.nodesOK).finalOK cert.prog cert.fins order
    bound

theorem card_B433_le
    {bound : ℕ} (h : S.finalCheck 4089470473293004800 bound = true) :
    Finite B433 ∧ Nat.card B433 ≤ bound * 4089470473293004800 :=
  card_B433_le_of_finalOK S.good S.ctxGood S.pt S.pt_zero S.actSpec S.nodesOK S.actAllSpec
    S.ptSurj bound cert.prog cert.fins h

theorem Q343_bound
    {bound : ℕ} (hbound : bound ≤ 1015970529280000)
    (h : S.finalCheck 4089470473293004800 bound = true) :
    Finite Q343 ∧ Nat.card Q343 ≤ Q343N :=
  Q343_bound_of_finalOK S.good S.ctxGood S.pt S.pt_zero S.actSpec S.nodesOK S.actAllSpec
    S.ptSurj bound hbound cert.prog cert.fins h

end Checked

@[expose] def b433Check :
    Bool :=
  let L := lettersB ()
  let O := omegaB433 L
  let cert := certB433 ()
  if h : bigOK O L fixB = true ∧ smallOK O L cert = true then
    Checked.finalCheck (⟨rfl, rfl, h.1, h.2⟩ : Checked L O cert) 4089470473293004800
      1015970529280000
  else false

theorem b433_bound_of_check
    (h : b433Check = true) :
    Finite B433 ∧ Nat.card B433 ≤ 1015970529280000 * 4089470473293004800 := by
  unfold b433Check at h
  dsimp only at h
  split at h
  · exact Checked.card_B433_le _ h
  · cases h

theorem Q343_bound_of_check
    (h : b433Check = true) : Finite Q343 ∧ Nat.card Q343 ≤ Q343N := by
  unfold b433Check at h
  dsimp only at h
  split at h
  · exact Checked.Q343_bound _ le_rfl h
  · cases h

end CFSG.YGroups.DCE.B433
