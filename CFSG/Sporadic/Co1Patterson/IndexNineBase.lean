module

public import CFSG.Sporadic.Co1Patterson.IndexNineInputs
public import CFSG.Sporadic.Co1Patterson.TwistNativeCore
public import CFSG.Sporadic.Co1Patterson.GraphSuborbit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.AltLocal17
public import CFSG.Sporadic.Schreier.J4SSylowBase

@[expose] public section

namespace CFSG.Sporadic.Co1Patterson.IndexNine

open Subgroup CFSG.Sporadic.Co1Patterson CFSG.Sporadic.Co1Patterson.Native
open CFSG.Sporadic.Co1Patterson.TwistNative
open CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.Native
  CFSG.Sporadic.SmallF2.Native
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.QuasithinUnique CFSG.Blueprint

@[ext]
structure Co1Flag where
  p : Fin 8 → ZMod 2
  L : Finset (Fin 8 → ZMod 2)
  hp : p ≠ 0
  hpL : p ∈ L
  hcard : L.card = 3
  hsing_p : q₀ p = 0
  hsing_L : ∀ v ∈ L, q₀ v = 0
  hsum : ∀ u ∈ L, ∀ v ∈ L, u ≠ v → u + v ∈ L

noncomputable def Co1Flag.smulFlag (g : L₀) (f : Co1Flag) : Co1Flag where
  p := g.val f.p
  L := f.L.image g.val
  hp := fun h => f.hp (g.val.injective (by simpa using h))
  hpL := Finset.mem_image.2 ⟨f.p, f.hpL, rfl⟩
  hcard := by
    rw [Finset.card_image_of_injective]
    exact f.hcard
    exact g.val.injective
  hsing_p := by
    show q₀ (g.val f.p) = 0
    rw [TwistNative.q₀_L₀ g f.p]
    exact f.hsing_p
  hsing_L := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hv
    show q₀ (g.val u) = 0
    rw [TwistNative.q₀_L₀ g u]
    exact f.hsing_L u hu
  hsum := by
    intro u hu v hv huv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hv
    have hab : a ≠ b := fun h => huv (by rw [h])
    refine Finset.mem_image.2 ⟨a + b, f.hsum a ha b hb hab, ?_⟩
    rw [map_add]

theorem co1Flag_zero_not_mem (f : Co1Flag) : (0 : Fin 8 → ZMod 2) ∉ f.L := by
  have hself : ∀ x : Fin 8 → ZMod 2, x + x = 0 := by
    intro x
    funext i
    exact CharTwo.add_self_eq_zero (x i)
  intro h0
  have hcardErase : (f.L.erase f.p).card = 2 := by
    rw [Finset.card_erase_of_mem f.hpL, f.hcard]
  obtain ⟨q, hq, hq0⟩ :=
    Finset.exists_mem_ne (s := f.L.erase f.p) (by omega : 1 < (f.L.erase f.p).card) 0
  have hqL : q ∈ f.L := (Finset.mem_erase.mp hq).2
  have hqp : q ≠ f.p := (Finset.mem_erase.mp hq).1
  have hsumL : q + f.p ∈ f.L := f.hsum q hqL f.p f.hpL hqp
  have hsum0 : q + f.p ≠ 0 := by
    intro h
    apply hqp
    calc q = q + (f.p + f.p) := by rw [hself, add_zero]
      _ = (q + f.p) + f.p := by rw [add_assoc]
      _ = 0 + f.p := by rw [h]
      _ = f.p := zero_add _
  have hsump : q + f.p ≠ f.p := by
    intro h
    apply hq0
    calc q = q + (f.p + f.p) := by rw [hself, add_zero]
      _ = (q + f.p) + f.p := by rw [add_assoc]
      _ = f.p + f.p := by rw [h]
      _ = 0 := hself f.p
  have hsumq : q + f.p ≠ q := by
    intro h
    apply f.hp
    have h' : (q + f.p) + q = q + q := congrArg (fun x => x + q) h
    calc f.p = f.p + (q + q) := by rw [hself, add_zero]
      _ = (q + f.p) + q := by abel
      _ = q + q := h'
      _ = 0 := hself q
  have hsub : ({f.p, q, q + f.p} : Finset (Fin 8 → ZMod 2)) ⊆ f.L := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact f.hpL
    · exact hqL
    · exact hsumL
  have h3 : ({f.p, q, q + f.p} : Finset (Fin 8 → ZMod 2)).card = 3 := by
    rw [Finset.card_triple_eq_three_iff]
    exact ⟨hqp.symm, hsump.symm, hsumq.symm⟩
  have h0not : (0 : Fin 8 → ZMod 2) ∉ ({f.p, q, q + f.p} : Finset (Fin 8 → ZMod 2)) := by
    intro hx
    rcases Finset.mem_insert.mp hx with h | hx
    · exact f.hp h.symm
    · rcases Finset.mem_insert.mp hx with h | hx
      · exact hq0 h.symm
      · simp only [Finset.mem_singleton] at hx
        exact hsum0 hx.symm
  have h4 : (Finset.card (insert (0 : Fin 8 → ZMod 2) {f.p, q, q + f.p})) = 4 := by
    rw [Finset.card_insert_of_notMem h0not, h3]
  have hsub4 : (insert (0 : Fin 8 → ZMod 2) {f.p, q, q + f.p}) ⊆ f.L := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact h0
    · exact hsub hx
  have hle := Finset.card_le_card hsub4
  rw [h4] at hle
  have hcard3 : f.L.card = 3 := f.hcard
  omega

noncomputable instance : MulAction L₀ Co1Flag where
  smul := Co1Flag.smulFlag
  one_smul f := by
    apply Co1Flag.ext
    · show (1 : L₀).val f.p = f.p
      rfl
    · show f.L.image (1 : L₀).val = f.L
      rw [Subgroup.coe_one, LinearEquiv.coe_one]
      exact Finset.image_id
  mul_smul g h f := by
    apply Co1Flag.ext
    · show (g * h).val f.p = g.val (h.val f.p)
      rfl
    · show f.L.image (g * h).val = (f.L.image h.val).image g.val
      rw [Subgroup.coe_mul]
      have hfun : ((g.val * h.val : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) :
          (Fin 8 → ZMod 2) → (Fin 8 → ZMod 2)) = fun x => g.val (h.val x) := rfl
      rw [hfun, Finset.image_image]
      rfl

noncomputable def co1BaseFlagL : Co1Flag where
  p := bv 8
  L := {bv 4, bv 8, bv 12}
  hp := by
    intro h
    have h' : (8 : ℕ) = 0 := bv_inj (by norm_num) (by norm_num) (h.trans bv_zero.symm)
    omega
  hpL := by simp
  hcard := by
    have h1 : bv 4 ≠ bv 8 := by
      intro h; have := bv_inj (by norm_num) (by norm_num) h; omega
    have h2 : bv 4 ≠ bv 12 := by
      intro h; have := bv_inj (by norm_num) (by norm_num) h; omega
    have h3 : bv 8 ≠ bv 12 := by
      intro h; have := bv_inj (by norm_num) (by norm_num) h; omega
    simp [h1, h2, h3]
  hsing_p := by rw [q₀_bv]; decide
  hsing_L := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl <;> (rw [q₀_bv]; decide)
  hsum := by
    intro u hu v hv huv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
      first
      | exact absurd rfl huv
      | (rw [← bv_xor]
         simp only [Finset.mem_insert, Finset.mem_singleton]
         first
         | left; exact congrArg bv (by decide)
         | right; left; exact congrArg bv (by decide)
         | right; right; exact congrArg bv (by decide))

theorem co1Flag_erase_eq (f : Co1Flag) {q : Fin 8 → ZMod 2} (hq : q ∈ f.L.erase f.p) :
    f.L.erase f.p = {q, q + f.p} := by
  have hself : ∀ x : Fin 8 → ZMod 2, x + x = 0 := by
    intro x
    funext i
    exact CharTwo.add_self_eq_zero (x i)
  have hqL : q ∈ f.L := (Finset.mem_erase.mp hq).2
  have hqp : q ≠ f.p := (Finset.mem_erase.mp hq).1
  have hq0 : q ≠ 0 := fun h => co1Flag_zero_not_mem f (h ▸ hqL)
  have hsumL : q + f.p ∈ f.L := f.hsum q hqL f.p f.hpL hqp
  have hsump : q + f.p ≠ f.p := by
    intro h
    apply hq0
    calc q = q + (f.p + f.p) := by rw [hself, add_zero]
      _ = (q + f.p) + f.p := by rw [add_assoc]
      _ = f.p + f.p := by rw [h]
      _ = 0 := hself f.p
  have hsumq : q ≠ q + f.p := by
    intro h
    apply f.hp
    have h' : q + q = (q + f.p) + q := congrArg (fun x => x + q) h
    calc f.p = f.p + (q + q) := by rw [hself, add_zero]
      _ = (q + f.p) + q := by abel
      _ = q + q := h'.symm
      _ = 0 := hself q
  have hsum_erase : q + f.p ∈ f.L.erase f.p :=
    Finset.mem_erase.mpr ⟨hsump, hsumL⟩
  have hsub : ({q, q + f.p} : Finset (Fin 8 → ZMod 2)) ⊆ f.L.erase f.p := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hq
    · exact hsum_erase
  have hcard : (f.L.erase f.p).card = 2 := by
    rw [Finset.card_erase_of_mem f.hpL, f.hcard]
  have hpair : ({q, q + f.p} : Finset (Fin 8 → ZMod 2)).card = 2 :=
    Finset.card_pair hsumq
  exact Finset.eq_of_superset_of_card_ge hsub (by rw [hcard, hpair])

noncomputable def co1FlagSecond (f : Co1Flag) : Fin 8 → ZMod 2 :=
  Classical.choose (Finset.card_pos.mp (show 0 < (f.L.erase f.p).card from by
    rw [Finset.card_erase_of_mem f.hpL, f.hcard]
    norm_num))

theorem co1FlagSecond_mem (f : Co1Flag) : co1FlagSecond f ∈ f.L.erase f.p := by
  unfold co1FlagSecond
  exact Classical.choose_spec _

theorem co1FlagSecond_mem_L (f : Co1Flag) : co1FlagSecond f ∈ f.L :=
  (Finset.mem_erase.mp (co1FlagSecond_mem f)).2

theorem co1FlagSecond_ne_p (f : Co1Flag) : co1FlagSecond f ≠ f.p :=
  (Finset.mem_erase.mp (co1FlagSecond_mem f)).1

theorem co1FlagSecond_erase (f : Co1Flag) :
    f.L.erase f.p = {co1FlagSecond f, co1FlagSecond f + f.p} :=
  co1Flag_erase_eq f (co1FlagSecond_mem f)

noncomputable def co1FlagCode (f : Co1Flag) : Nat × Nat :=
  let p := enc f.p
  let q := enc (co1FlagSecond f)
  (p, min q (q ^^^ p))

@[simp] theorem co1FlagCode_fst (f : Co1Flag) : (co1FlagCode f).1 = enc f.p := rfl

theorem co1FlagCode_snd (f : Co1Flag) :
    (co1FlagCode f).2 = min (enc (co1FlagSecond f))
      (enc (co1FlagSecond f) ^^^ enc f.p) := rfl

theorem co1Enc_add (u v : Fin 8 → ZMod 2) : enc (u + v) = enc u ^^^ enc v := by
  apply bv_inj (enc_lt _) (by
    simpa using Nat.xor_lt_two_pow (n := 8) (enc_lt u) (enc_lt v))
  rw [bv_enc, bv_xor, bv_enc, bv_enc]

theorem co1FlagStepC_fst (m : List Nat) (f : Nat × Nat) :
    (co1FlagStepC m f).1 = colsApply m f.1 := rfl

theorem co1FlagStepC_snd (m : List Nat) (f : Nat × Nat) :
    (co1FlagStepC m f).2 =
      min (colsApply m f.2) (colsApply m f.2 ^^^ colsApply m f.1) := by
  change (if colsApply m f.2 < (colsApply m f.2 ^^^ colsApply m f.1)
      then colsApply m f.2 else colsApply m f.2 ^^^ colsApply m f.1) =
    min (colsApply m f.2) (colsApply m f.2 ^^^ colsApply m f.1)
  by_cases h : colsApply m f.2 < (colsApply m f.2 ^^^ colsApply m f.1)
  · rw [if_pos h, min_eq_left (le_of_lt h)]
  · rw [if_neg h, min_eq_right (by omega)]

theorem co1FlagSecond_pair_eq (f : Co1Flag) :
    ({co1FlagSecond f, co1FlagSecond f + f.p} : Finset (Fin 8 → ZMod 2)) =
      {bv (co1FlagCode f).2, bv ((co1FlagCode f).2 ^^^ enc f.p)} := by
  let q := co1FlagSecond f
  let p := f.p
  let a := enc q
  let b := enc q ^^^ enc p
  have hs : (co1FlagCode f).2 = min a b := rfl
  rw [hs]
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab]
    rw [show a = enc q from rfl, bv_enc]
    rw [show bv (a ^^^ enc p) = q + p from by
      rw [show a = enc q from rfl, bv_xor, bv_enc, bv_enc]]
  · rw [min_eq_right hba]
    have hb : bv b = q + p := by
      rw [show b = enc q ^^^ enc p from rfl, bv_xor, bv_enc, bv_enc]
    have hbb : b ^^^ enc p = enc q := by
      rw [show b = enc q ^^^ enc p from rfl, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    rw [hb, hbb, bv_enc]
    exact Finset.pair_comm q (q + p)

theorem co1FlagCode_base : co1FlagCode co1BaseFlagL = co1BaseFlag := by
  have hqL : co1FlagSecond co1BaseFlagL ∈
      ({bv 4, bv 8, bv 12} : Finset (Fin 8 → ZMod 2)) := by
    simpa [co1BaseFlagL] using co1FlagSecond_mem_L co1BaseFlagL
  have hqp : co1FlagSecond co1BaseFlagL ≠ bv 8 := by
    have h := co1FlagSecond_ne_p co1BaseFlagL
    simpa [co1BaseFlagL] using h
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hqL
  have hmem : co1FlagSecond co1BaseFlagL = bv 4 ∨ co1FlagSecond co1BaseFlagL = bv 12 := by
    rcases hqL with h | h | h
    · exact Or.inl h
    · exact absurd h hqp
    · exact Or.inr h
  have hp : co1BaseFlagL.p = bv 8 := rfl
  have hp8 : enc co1BaseFlagL.p = 8 := by rw [hp]; exact enc_bv (by norm_num)
  have h4 : enc (bv 4) = 4 := enc_bv (by norm_num)
  have h12 : enc (bv 12) = 12 := enc_bv (by norm_num)
  have hx4 : (4 ^^^ 8) = 12 := by decide
  have hx12 : (12 ^^^ 8) = 4 := by decide
  rcases hmem with h | h
  · simp [co1FlagCode, h, h4, hp8, hx4, co1BaseFlag]
  · simp [co1FlagCode, h, h12, hp8, hx12, co1BaseFlag]

theorem co1FlagCode_injective : Function.Injective co1FlagCode := by
  intro f g hfg
  have hfst : f.p = g.p := by
    have h := congrArg Prod.fst hfg
    simp only [co1FlagCode_fst] at h
    calc f.p = bv (enc f.p) := (bv_enc _).symm
      _ = bv (enc g.p) := by rw [h]
      _ = g.p := bv_enc _
  have hsnd : (co1FlagCode f).2 = (co1FlagCode g).2 := congrArg Prod.snd hfg
  apply Co1Flag.ext
  · exact hfst
  · calc f.L = insert f.p (f.L.erase f.p) := (Finset.insert_erase f.hpL).symm
      _ = insert f.p {co1FlagSecond f, co1FlagSecond f + f.p} := by
          rw [co1FlagSecond_erase f]
      _ = insert f.p {bv (co1FlagCode f).2, bv ((co1FlagCode f).2 ^^^ enc f.p)} := by
          rw [co1FlagSecond_pair_eq f]
      _ = insert g.p {bv (co1FlagCode g).2, bv ((co1FlagCode g).2 ^^^ enc g.p)} := by
          rw [hfst, hsnd]
      _ = insert g.p {co1FlagSecond g, co1FlagSecond g + g.p} := by
          rw [co1FlagSecond_pair_eq g]
      _ = insert g.p (g.L.erase g.p) := by rw [co1FlagSecond_erase g]
      _ = g.L := Finset.insert_erase g.hpL

def co1PairKey (c : Nat × Nat) : Nat := c.1 * 256 + c.2

theorem co1FlagCode_lt (f : Co1Flag) : (co1FlagCode f).1 < 256 ∧ (co1FlagCode f).2 < 256 := by
  constructor
  · exact enc_lt _
  · exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (enc_lt _)

theorem co1PairKey_injective {p q p' q' : Nat} (hp : p < 256) (hq : q < 256)
    (hp' : p' < 256) (hq' : q' < 256) (h : p * 256 + q = p' * 256 + q') :
    p = p' ∧ q = q' := by
  have h' : Nat.ofDigits 256 [q, p] = Nat.ofDigits 256 [q', p'] := by
    simpa [Nat.ofDigits, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_comm] using h
  have hlen : ([q, p] : List Nat).length = ([q', p'] : List Nat).length := rfl
  have hlt1 : ∀ x ∈ ([q, p] : List Nat), x < 256 := by
    intro x hx
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hq
    · exact hp
  have hlt2 : ∀ x ∈ ([q', p'] : List Nat), x < 256 := by
    intro x hx
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hq'
    · exact hp'
  have hlists := Nat.ofDigits_inj_of_len_eq (b := 256) (by norm_num) hlen hlt1 hlt2 h'
  simp only [List.cons.injEq, and_true] at hlists
  exact ⟨hlists.2, hlists.1⟩

theorem co1FlagKey_injective :
    Function.Injective fun f : Co1Flag => co1PairKey (co1FlagCode f) := by
  intro f g h
  have hf := co1FlagCode_lt f
  have hg := co1FlagCode_lt g
  have hpq := co1PairKey_injective hf.1 hf.2 hg.1 hg.2 h
  exact co1FlagCode_injective (Prod.ext hpq.1 hpq.2)

noncomputable def brayC (l : ℕ) (hl : l < brayArr.size) :
    centralizer ({aNC} : Set NativeSporadic.Co1) :=
  ⟨brayNC l, brayNC_mem l hl⟩

theorem mrep_brayC (l : ℕ) (hl : l < brayArr.size) :
    MRep (brayArr[l]!) (nativeEmb (brayNC l)) := by
  have h := CFSG.Sporadic.Co1Patterson.nrep_brayArr l hl
  unfold NRep at h
  rw [matHom_eq_nativeEmb] at h
  exact h.symm

theorem brayC_conj (l : ℕ) (hl : l < brayArr.size) {m : List ℕ}
    (hc : conjOK (brayArr[l]!) m = true) :
    ∀ k < 8, brayC l hl * yH k * (brayC l hl)⁻¹ = yprodH (m.getD k 0) ∨
      brayC l hl * yH k * (brayC l hl)⁻¹ = yprodH (m.getD k 0) * typeSystemC.z := by
  intro k hk
  have hz : centEmb typeSystemC.z = aG := centEmb_zM
  rcases conjOK_spec (mrep_brayC l hl) hc k hk with h1 | h1
  · left
    apply centEmb_injective
    rw [map_mul, map_mul, map_inv, centEmb_yH, centEmb_yprodH]
    simpa [brayC, centEmb] using h1
  · right
    apply centEmb_injective
    rw [map_mul, map_mul, map_inv, centEmb_yH, map_mul, centEmb_yprodH, hz]
    simpa [brayC, centEmb] using h1

theorem hasCols_brayC (l : ℕ) (hl : l < brayArr.size) {m : List ℕ}
    (hc : conjOK (brayArr[l]!) m = true) :
    HasCols (((typeSystemC.φ (brayC l hl) : L₀) :
      (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) :
      (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)) m := fun k hk =>
  (phi_bv_of_conj (brayC l hl) m (brayC_conj l hl hc) (2 ^ k)).trans (bv_colsApply_two_pow m hk)

noncomputable def brayCList (_ : Unit := ()) :
    List (centralizer ({aNC} : Set NativeSporadic.Co1)) :=
  List.ofFn fun l : Fin 8 => brayC l.val (by rw [brayArr_size]; exact l.isLt)

theorem brayCList_length : (brayCList ()).length = 8 := by simp [brayCList]

theorem brayCList_getD {i : ℕ} (hi : i < 8) :
    (brayCList ()).getD i 1 = brayC i (by rw [brayArr_size]; exact hi) := by
  rw [brayCList, List.getD_eq_getElem _ _ (by simpa [brayCList_length] using hi),
    List.getElem_ofFn]

theorem co1MatsC_getD {i : ℕ} (hi : i < 8) :
    (co1MatsC ()).getD i idCols = findCols (brayArr[i]!) := by
  rw [co1MatsC, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
    List.getElem_range]

noncomputable def co1WordElGo :
    List (Nat × Nat) → centralizer ({aNC} : Set NativeSporadic.Co1)
  | [] => 1
  | x :: xs => co1WordElGo xs * ((brayCList ()).getD x.1 1) ^ x.2

noncomputable def co1WordEl (w : List (Nat × Nat)) :
    centralizer ({aNC} : Set NativeSporadic.Co1) :=
  co1WordElGo w.reverse

theorem hasCols_pow {f : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)} {m : List ℕ}
    (hf : HasCols (f : (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)) m) (n : ℕ) :
    HasCols ((f ^ n : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) :
      (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)) (co1PowCols m n) := by
  induction n with
  | zero =>
      rw [pow_zero, co1PowCols]
      simpa using hasCols_id
  | succ n ih =>
      rw [pow_succ, co1PowCols, LinearEquiv.coe_toLinearMap_mul]
      exact HasCols.comp ih hf

theorem hasCols_wordCGo (M : List (List Nat)) (w : List (Nat × Nat))
    (hw : ∀ x ∈ w, x.1 < 8)
    (hM : ∀ i (hi : i < 8), HasCols ((typeSystemC.φ (brayC i (by rw [brayArr_size]; exact hi)) :
      L₀) : (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)) (M.getD i idCols)) :
    HasCols ((typeSystemC.φ (co1WordElGo w) : L₀) :
      (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)) (co1WordCGo M w) := by
  induction w with
  | nil => simpa [co1WordElGo, co1WordCGo] using hasCols_id
  | cons x xs ih =>
      obtain ⟨i, e⟩ := x
      have hi : i < 8 := hw (i, e) (by simp)
      have hwxs : ∀ y ∈ xs, y.1 < 8 := fun y hy => hw y (by simp [hy])
      have hgen := hM i hi
      unfold co1WordElGo co1WordCGo
      rw [brayCList_getD hi]
      rw [map_mul, map_pow]
      exact HasCols.comp (ih hwxs) (hasCols_pow hgen e)

theorem co1XWord_idx_lt : ∀ x ∈ co1XWord, x.1 < 8 := by decide

theorem co1YWord_idx_lt : ∀ x ∈ co1YWord, x.1 < 8 := by decide

theorem co1UWords_idx_lt : ∀ w ∈ co1UWords, ∀ x ∈ w, x.1 < 8 := by decide

theorem hasCols_wordC (M : List (List Nat))
    (hM : ∀ i (hi : i < 8), HasCols ((typeSystemC.φ (brayC i (by rw [brayArr_size]; exact hi)) :
      L₀) : (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)) (M.getD i idCols))
    (w : List (Nat × Nat)) (hw : ∀ x ∈ w, x.1 < 8) :
    HasCols ((typeSystemC.φ (co1WordEl w) : L₀) :
      (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)) (co1WordC M w) := by
  rw [co1WordEl, co1WordC]
  exact hasCols_wordCGo M w.reverse (fun x hx => hw x (List.mem_reverse.mp hx)) hM

noncomputable def co1XEl : L₀ := typeSystemC.φ (co1WordEl co1XWord)

noncomputable def co1YEl : L₀ := typeSystemC.φ (co1WordEl co1YWord)

noncomputable def co1Ubar : Subgroup L₀ :=
  Subgroup.closure (Set.range fun i : Fin co1UWords.length =>
    typeSystemC.φ (co1WordEl (co1UWords.get i)))

noncomputable def co1BrayGens (i : Fin 8) : L₀ :=
  typeSystemC.φ (brayC i.val (by rw [brayArr_size]; exact i.isLt))

noncomputable def co1UGens (i : Fin 4) : L₀ :=
  typeSystemC.φ (co1WordEl (co1UWords.get i))

noncomputable def co1EvalWord {n : Nat} (gens : Fin n → L₀) (w : List (Fin n)) : L₀ :=
  w.foldr (fun i acc => gens i * acc) 1

theorem closure_brayC :
    Subgroup.closure (Set.range fun i : Fin 8 =>
      brayC i.val (by rw [brayArr_size]; exact i.isLt)) = ⊤ := by
  apply (Subgroup.map_injective
    (f := (centralizer ({aNC} : Set NativeSporadic.Co1)).subtype)
    (centralizer ({aNC} : Set NativeSporadic.Co1)).subtype_injective)
  rw [MonoidHom.map_closure]
  have himg : (centralizer ({aNC} : Set NativeSporadic.Co1)).subtype ''
      (Set.range fun i : Fin 8 =>
        brayC i.val (by rw [brayArr_size]; exact i.isLt)) =
      brayNC '' {l | l < 8} := by
    ext y
    constructor
    · rintro ⟨-, ⟨i, rfl⟩, rfl⟩
      exact ⟨i.val, i.isLt, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨brayC l hl, ⟨⟨l, hl⟩, rfl⟩, rfl⟩
  rw [himg, CFSG.Sporadic.Co1Patterson.closure_brayNC]
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem closure_co1Gens : Subgroup.closure (Set.range co1BrayGens) = ⊤ := by
  have hgen : Set.range co1BrayGens = typeSystemC.φ '' (Set.range fun i : Fin 8 =>
      brayC i.val (by rw [brayArr_size]; exact i.isLt)) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨brayC i.val _, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨-, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  rw [hgen, ← MonoidHom.map_closure, closure_brayC]
  exact Subgroup.map_top_of_surjective _ typeSystemC.φ_surj

noncomputable def co1Cols (g : L₀) : List Nat :=
  cols ((g : L₀) : (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2))

theorem hasCols_co1Cols (g : L₀) :
    HasCols ((g : L₀) : (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)) (co1Cols g) :=
  hasCols_cols _

theorem co1Cols_length (g : L₀) : (co1Cols g).length = 8 := by simp [co1Cols, cols]

theorem co1Cols_getD_lt (g : L₀) (k : Nat) : (co1Cols g).getD k 0 < 256 :=
  cols_getD_lt _ k

theorem co1Cols_injective : Function.Injective co1Cols := by
  intro g h hgh
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  exact HasCols.ext (hasCols_co1Cols g) (hgh ▸ hasCols_co1Cols h)

theorem co1Cols_eq_of_hasCols {g : L₀} {m : List Nat} (hm : m.length = 8)
    (hm' : ∀ k, m.getD k 0 < 256)
    (h : HasCols ((g : L₀) : (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)) m) :
    co1Cols g = m := by
  apply List.ext_getElem (by rw [co1Cols_length, hm])
  intro k hk hk'
  rw [← List.getD_eq_getElem m 0 hk', ← List.getD_eq_getElem (co1Cols g) 0 hk]
  exact cols_getD_eq h (fun k _ => hm' k) (by omega)

def co1WordFin {n : Nat} (w : List Nat) (hw : ∀ i ∈ w, i < n) : List (Fin n) :=
  List.pmap (fun i (hi : i < n) => ⟨i, hi⟩) w hw

@[simp] theorem co1WordFin_nil {n : Nat} (hw : ∀ i ∈ ([] : List Nat), i < n) :
    co1WordFin [] hw = [] := rfl

theorem co1WordFin_cons {n : Nat} {i : Nat} {w : List Nat} (hi : i < n)
    (hw : ∀ j ∈ w, j < n) :
    co1WordFin (i :: w) (fun j hj => by
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hi
      · exact hw j hj) = ⟨i, hi⟩ :: co1WordFin w hw := by
  rw [co1WordFin, List.pmap_cons]
  rfl

def co1LetterFin (n : Nat) [NeZero n] (i : Nat) : Fin n :=
  ⟨i % n, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n))⟩

def co1WordMod (n : Nat) [NeZero n] (w : List Nat) : List (Fin n) :=
  w.map (co1LetterFin n)

theorem co1WordMod_eq_wordFin {n : Nat} [NeZero n] (w : List Nat)
    (hw : ∀ i ∈ w, i < n) :
    co1WordMod n w = co1WordFin w hw := by
  rw [co1WordMod, co1WordFin]
  rw [← List.pmap_eq_map (p := fun i => i < n) (f := co1LetterFin n) (l := w) hw]
  exact (List.pmap_congr_left w fun a _ h1 h2 => Fin.ext (Nat.mod_eq_of_lt h1).symm).symm

theorem hasCols_evalWordR {n : Nat} {gens : Fin n → L₀} {cols : Fin n → List Nat}
    (h : ∀ i, HasCols ((gens i : L₀) :
      (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)) (cols i))
    (w : List Nat) (hw : ∀ i ∈ w, i < n) :
    HasCols ((co1EvalWord gens (co1WordFin w hw) : L₀) :
      (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2))
      (co1EvalColsR (List.ofFn cols) w) := by
  induction w with
  | nil => simpa [co1EvalWord, co1EvalColsR] using hasCols_id
  | cons i w ih =>
    have hi : i < n := hw i (by simp)
    have hw' : ∀ j ∈ w, j < n := fun j hj => hw j (by simp [hj])
    rw [co1WordFin_cons hi hw', co1EvalColsR]
    rw [show (List.ofFn cols).getD i idCols = cols ⟨i, hi⟩ from by
      rw [List.getD_eq_getElem _ _ (by simpa [List.length_ofFn] using hi), List.getElem_ofFn]]
    rw [co1EvalWord, List.foldr_cons]
    exact HasCols.comp (h ⟨i, hi⟩) (ih hw')

theorem hasCols_evalWordMod {n : Nat} [NeZero n] {gens : Fin n → L₀}
    {cols : Fin n → List Nat}
    (h : ∀ i, HasCols ((gens i : L₀) :
      (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)) (cols i))
    (w : List Nat) (hw : ∀ i ∈ w, i < n) :
    HasCols ((co1EvalWord gens (co1WordMod n w) : L₀) :
      (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2))
      (co1EvalColsR (List.ofFn cols) w) := by
  rw [co1WordMod_eq_wordFin w hw]
  exact hasCols_evalWordR h w hw

theorem co1PowCols_getD_lt {m : List Nat} (hm : ∀ k, m.getD k 0 < 256) (n : Nat) :
    ∀ k, (co1PowCols m n).getD k 0 < 256 := by
  induction n with
  | zero =>
    intro k
    simpa [co1PowCols] using idCols_getD_lt k
  | succ n ih =>
    intro k
    rw [co1PowCols]
    exact colsMul_getD_lt ih k

theorem co1WordCGo_getD_lt (M : List (List Nat)) (w : List (Nat × Nat)) :
    ∀ k, (co1WordCGo M w).getD k 0 < 256 := by
  induction w with
  | nil =>
    intro k
    simpa [co1WordCGo] using idCols_getD_lt k
  | cons x xs ih =>
    intro k
    rw [co1WordCGo]
    exact colsMul_getD_lt ih k

theorem co1WordC_getD_lt (M : List (List Nat)) (w : List (Nat × Nat)) :
    ∀ k, (co1WordC M w).getD k 0 < 256 :=
  co1WordCGo_getD_lt M w.reverse

theorem co1WordCGo_length (M : List (List Nat)) (w : List (Nat × Nat)) :
    (co1WordCGo M w).length = 8 := by
  induction w with
  | nil => rfl
  | cons x xs ih => simp only [co1WordCGo, colsMul, List.length_map, List.length_range]

theorem co1WordC_length (M : List (List Nat)) (w : List (Nat × Nat)) :
    (co1WordC M w).length = 8 :=
  co1WordCGo_length M w.reverse

theorem co1EvalColsR_length (gens : List (List Nat)) (w : List Nat) :
    (co1EvalColsR gens w).length = 8 := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [co1EvalColsR, colsMul, List.length_map, List.length_range]

theorem co1Ubar_eq_closure : co1Ubar = Subgroup.closure (Set.range co1UGens) := rfl

theorem co1EvalWord_mem_co1Ubar {n : Nat} {gens : Fin n → L₀}
    (hgens : Set.range gens ⊆ (co1Ubar : Set L₀)) (w : List (Fin n)) :
    co1EvalWord gens w ∈ co1Ubar := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons i w ih =>
    rw [co1EvalWord, List.foldr_cons]
    exact Subgroup.mul_mem _ (hgens ⟨i, rfl⟩) ih

theorem co1EvalColsR_getD_lt {gens : List (List Nat)}
    (h : ∀ i k, (gens.getD i idCols).getD k 0 < 256) (w : List Nat) :
    ∀ k, (co1EvalColsR gens w).getD k 0 < 256 := by
  induction w with
  | nil => intro k; simpa [co1EvalColsR] using idCols_getD_lt k
  | cons i w ih =>
    intro k
    rw [co1EvalColsR]
    exact colsMul_getD_lt (h i) k

theorem co1Cols_mem_lt (g : L₀) {x : Nat} (hx : x ∈ co1Cols g) : x < 256 := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
  rw [← List.getD_eq_getElem (co1Cols g) 0 hk]
  exact co1Cols_getD_lt g k

theorem co1Cols_colsApply_xor (g : L₀) (a b : Nat) :
    colsApply (co1Cols g) (a ^^^ b) =
      colsApply (co1Cols g) a ^^^ colsApply (co1Cols g) b := by
  have hlin : ((g : L₀) : (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2))
      (bv (a ^^^ b)) =
      ((g : L₀) : (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)) (bv a) +
        ((g : L₀) : (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)) (bv b) := by
    rw [bv_xor, map_add]
  rw [HasCols.apply (hasCols_co1Cols g) (a ^^^ b),
    HasCols.apply (hasCols_co1Cols g) a,
    HasCols.apply (hasCols_co1Cols g) b, ← bv_xor] at hlin
  have hxorb : colsApply (co1Cols g) a ^^^ colsApply (co1Cols g) b < 256 := by
    have h1 : colsApply (co1Cols g) a < 256 := colsApply_lt (co1Cols_getD_lt g) a
    have h2 : colsApply (co1Cols g) b < 256 := colsApply_lt (co1Cols_getD_lt g) b
    simpa using Nat.xor_lt_two_pow (n := 8) h1 h2
  exact bv_inj (colsApply_lt (co1Cols_getD_lt g) _) hxorb hlin

theorem co1ColsApply_idCols {v : Nat} (hv : v < 256) : colsApply idCols v = v := by
  have h := HasCols.apply (hasCols_id : HasCols (LinearMap.id :
    (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)) idCols) v
  have h2 : bv v = bv (colsApply idCols v) := by simpa using h
  exact bv_inj (colsApply_lt (idCols_getD_lt) v) hv h2.symm

theorem co1ColsMul_idCols_left {m : List Nat} (hm : m.length = 8)
    (hm' : ∀ k, m.getD k 0 < 256) : colsMul idCols m = m := by
  apply List.ext_getElem (by simp [colsMul, hm])
  intro i hi hi'
  have hi8 : i < 8 := by simpa [colsMul] using hi
  rw [show (colsMul idCols m)[i] = colsApply idCols (m.getD i 0) from by
    simp [colsMul, hi8]]
  rw [co1ColsApply_idCols (hm' i)]
  exact List.getD_eq_getElem m 0 hi' 

theorem co1Cols_mul (a b : L₀) :
    co1Cols (a * b) = colsMul (co1Cols a) (co1Cols b) := by
  apply co1Cols_eq_of_hasCols (by simp [colsMul])
    (fun k => colsMul_getD_lt (co1Cols_getD_lt a) k)
  exact hasCols_mul (hasCols_co1Cols a) (hasCols_co1Cols b)

theorem co1Cols_one : co1Cols (1 : L₀) = idCols :=
  co1Cols_eq_of_hasCols (by simp [idCols]) (fun k => idCols_getD_lt k) hasCols_one

theorem co1Cols_pow (a : L₀) (n : Nat) :
    co1Cols (a ^ n) = co1PowCols (co1Cols a) n := by
  have hlen : ∀ n, (co1PowCols (co1Cols a) n).length = 8 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp [co1PowCols, colsMul, List.length_map, List.length_range]
  apply co1Cols_eq_of_hasCols (hlen n) (fun k => co1PowCols_getD_lt (co1Cols_getD_lt a) n k)
  exact hasCols_pow (hasCols_co1Cols a) n

theorem co1PowCols_one {m : List Nat} (hm : m.length = 8)
    (hm' : ∀ k, m.getD k 0 < 256) : co1PowCols m 1 = m := by
  simpa [co1PowCols] using co1ColsMul_idCols_left hm hm'

theorem co1PowCols_two {m : List Nat} (hm : m.length = 8)
    (hm' : ∀ k, m.getD k 0 < 256) : co1PowCols m 2 = colsMul m m := by
  rw [show co1PowCols m 2 = colsMul (co1PowCols m 1) m from rfl, co1PowCols_one hm hm']

theorem co1PowCols_three {m : List Nat} (hm : m.length = 8)
    (hm' : ∀ k, m.getD k 0 < 256) (h : colsMul (colsMul m m) m = idCols) :
    co1PowCols m 3 = idCols := by
  have h1 : co1PowCols m 1 = m := co1PowCols_one hm hm'
  have h2 : co1PowCols m 2 = colsMul m m := by
    rw [show co1PowCols m 2 = colsMul (co1PowCols m 1) m from rfl, h1]
  rw [show co1PowCols m 3 = colsMul (co1PowCols m 2) m from rfl, h2]
  exact h

theorem co1FlagCode_smul (g : L₀) (f : Co1Flag) :
    co1FlagCode (g • f) = co1FlagStepC (co1Cols g) (co1FlagCode f) := by
  classical
  apply Prod.ext
  · rw [co1FlagCode_fst, co1FlagStepC_fst]
    have h := HasCols.apply (hasCols_co1Cols g) (enc f.p)
    have h' : g.val f.p = bv (colsApply (co1Cols g) (enc f.p)) := by
      simpa [bv_enc] using h
    change enc (g.val f.p) = colsApply (co1Cols g) (enc f.p)
    rw [h']
    exact enc_bv (colsApply_lt (co1Cols_getD_lt g) _)
  · rw [co1FlagStepC_snd]
    let q := co1FlagSecond f
    let pv := f.p
    let p := enc pv
    let a := enc q
    let b := a ^^^ p
    have hpair : (g • f).L.erase (g • f).p = (f.L.erase f.p).image g.val := by
      show (f.L.image g.val).erase (g.val f.p) = (f.L.erase f.p).image g.val
      rw [← Finset.image_erase g.val.injective f.L f.p]
    have hmem : co1FlagSecond (g • f) ∈ (f.L.erase f.p).image g.val := by
      rw [← hpair]
      exact co1FlagSecond_mem _
    rw [show f.L.erase f.p = {q, q + pv} from by
      simpa [q, pv] using co1FlagSecond_erase f] at hmem
    rw [Finset.mem_image] at hmem
    obtain ⟨v, hv, hvq⟩ := hmem
    rw [Finset.mem_insert, Finset.mem_singleton] at hv
    have hgp : enc (g.val pv) = colsApply (co1Cols g) p := by
      have h := HasCols.apply (hasCols_co1Cols g) (enc pv)
      have h' : g.val pv = bv (colsApply (co1Cols g) (enc pv)) := by
        simpa [bv_enc] using h
      rw [h']
      exact enc_bv (colsApply_lt (co1Cols_getD_lt g) _)
    have hA : enc (g.val q) = colsApply (co1Cols g) a := by
      have h := HasCols.apply (hasCols_co1Cols g) (enc q)
      have h' : g.val q = bv (colsApply (co1Cols g) (enc q)) := by
        simpa [bv_enc] using h
      rw [h']
      exact enc_bv (colsApply_lt (co1Cols_getD_lt g) _)
    have hbv_b : bv b = q + pv := by
      have hbva : bv a = q := by
        show bv (enc q) = q
        exact bv_enc q
      have hbvp : bv p = pv := by
        show bv (enc pv) = pv
        exact bv_enc pv
      rw [show b = a ^^^ p from rfl, bv_xor, hbva, hbvp]
    have hB : enc (g.val (q + pv)) = colsApply (co1Cols g) b := by
      have h := HasCols.apply (hasCols_co1Cols g) b
      rw [hbv_b] at h
      have h' : g.val (q + pv) = bv (colsApply (co1Cols g) b) := by
        simpa using h
      rw [h']
      exact enc_bv (colsApply_lt (co1Cols_getD_lt g) _)
    have hAB : enc (g.val q) ^^^ enc (g.val pv) = colsApply (co1Cols g) b := by
      rw [← co1Enc_add, ← map_add, hB]
    have hbxp : b ^^^ p = a := by
      rw [show b = a ^^^ p from rfl, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    have hBA : enc (g.val (q + pv)) ^^^ enc (g.val pv) = colsApply (co1Cols g) a := by
      have hqpp : q + pv + pv = q := by
        rw [add_assoc, show pv + pv = 0 from by
          funext i; exact CharTwo.add_self_eq_zero (pv i), add_zero]
      rw [← co1Enc_add, ← map_add, hqpp, hA]
    have hcode_min : (co1FlagCode f).2 = min a b := by
      rw [co1FlagCode_snd]
    rcases le_total a b with hab | hba
    · have hcode : (co1FlagCode f).2 = a := by
        rw [hcode_min, min_eq_left hab]
      rw [hcode, co1FlagCode_snd, co1FlagCode_fst,
        show (g • f).p = g.val pv from rfl]
      rcases hv with rfl | rfl
      · rw [← hvq, hAB, hA, ← co1Cols_colsApply_xor g a p]
      · rw [← hvq, hBA, hB, ← co1Cols_colsApply_xor g a p]
        exact Nat.min_comm _ _
    · have hcode : (co1FlagCode f).2 = b := by
        rw [hcode_min, min_eq_right hba]
      rw [hcode, co1FlagCode_snd, co1FlagCode_fst,
        show (g • f).p = g.val pv from rfl]
      rcases hv with rfl | rfl
      · rw [← hvq, hAB, hA, ← co1Cols_colsApply_xor g b p, hbxp]
        exact Nat.min_comm _ _
      · rw [← hvq, hBA, hB, ← co1Cols_colsApply_xor g b p, hbxp]

theorem co1Key_injective :
    Function.Injective fun g : L₀ => co1RowsKeyC (co1Cols g) := by
  intro g h hk
  apply co1Cols_injective
  exact co1RowsKeyC_injOn (co1Cols_length g) (co1Cols_length h)
    (fun x hx => co1Cols_mem_lt g hx) (fun x hx => co1Cols_mem_lt h hx) hk

theorem findCols_length (h : Co1Schreier.Native.Rows) : (findCols h).length = 8 := by
  simp [findCols]

theorem co1Phi_eq_one_iff {x : centralizer ({aNC} : Set NativeSporadic.Co1)} :
    typeSystemC.φ x = 1 ↔ x ∈ twoAQC := by
  change (Setting.phiV₀ nativeSetting coordIso nativeOmega)
    (show nativeSetting.M from x) = 1 ↔ x ∈ twoAQC
  rw [Setting.phiV₀_eq_one_iff]
  change ((x : NativeSporadic.Co1) ∈ nativeSetting.QG) ↔ x ∈ twoAQC
  rw [show nativeSetting.QG = twoAQC.map
      (Subgroup.subtype (centralizer ({aNC} : Set NativeSporadic.Co1))) from rfl]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hyx' : y = x := Subtype.ext hyx
    simpa [hyx'] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

end CFSG.Sporadic.Co1Patterson.IndexNine
