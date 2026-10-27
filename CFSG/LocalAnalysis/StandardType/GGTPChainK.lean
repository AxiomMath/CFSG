module

public import CFSG.LocalAnalysis.StandardType.GGE6DepModelShapeFin

public section

namespace CFSG.StandardType.GGTPK

open E6Dep

@[expose] def cjP : ℕ := 3526423289371805637162840046296381848144956229458800940124495710990115292950906491428983413614768463848354190758308024049048886791661467973526437993618097172912765829890010771532690351727870725856921185326737845442315917687099472795730093608442108768369604464458795682417464812175148875764761097718295226625262046530443548937413917982383040169428470588182571933610736896759059367210814080078961986372064816192337067587781409475150720615988984521349491415809164929283456928156209467661522635266450534313126222076300846841349813401752496687596153131917836128752501827900440261774442440018213212368826328493865550103069417457231543202462420879608352411420962605839662352133505361524315775664920671207350952839884274659387112760532371927842264219586499056148014024282259589494834130165126828963567411454908203356298097595103805622228808069221303329022622551183030838069878923649254912459263728831640194823945615172959959496272261563300940791821552283725927686072702173249436792703007034695075960595487424660736806388517404495590177824524017993699112510901379220727752993779852560631439197246781064626213788188614954568442814383501797224034394449709823213000555537195262640091329537950837215716051108632625707661169025034360389534417953685620186934617750187467825547077235554084480980004522334003754690121382265082010218588008751039025246783677904929417932550208625145584598988761224196797454336072237344503944177971119593443796377907812827122127430675068653049929565017289957081118138640557425860061898493508054592950037927324620797438174101105570023482068715183573738432905403829677592950927261230440317941362960512815210298296570179393415419945641686130202296328587098056500573943652634145301079891818234120708776488006617105698259516038448042317995162204822637324819669169698157525563239588848593666785383353523419999771854223704718381726619275233541349457743601298961204850660179798225338080464717775183304306441383899841614309037174978306400255280571243786928785147798011843078188776240054741724627940101172056174311820043498269094403008529881406495099400673693418828972593273374453682053404825921349271314210614725246034679167814586995312690303107995145724295777712208825012419193678325391094164828541721837888671959453836199280159544156568769065930410305140483332834183941889405752338395462368448935730539700202847495576614201021541650560

@[expose] def fixP : ℕ := 39432141063364381243141613914569135097850945803351567361061227184571280888259031683286366047406208928540322112298853201872272986790857827600051159110085232810593369483266385449012531870136547449327644233853740153720763222147453918700555583480024173750772898375451313228919518307160893649957332686933860161844908612293897778254272713986146250376397404182562615240902769318687027684922868680

@[expose] def rP : ℕ := 1645504558853707429050056558869967998872230278227305112357044225

@[expose] def cjL (a b : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight cjP (Nat.mul 6 (Nat.add (Nat.mul 36 a) b))) 63

@[expose] def cjK (a b : ℕ) : ℕ :=
  Bool.rec (cjN a b) (cjL a b) (Bool.rec false (Nat.blt b 36) (Nat.blt a 36))

@[expose] def allK (n : ℕ) (f : ℕ → Bool) : Bool :=
  Nat.rec true (fun i acc => Bool.rec false (f i) acc) n

@[expose] def orK (x y : Bool) : Bool := Bool.rec y true x

@[expose] def notK (x : Bool) : Bool := Bool.rec true false x

@[expose] def skip1 (a0 a1 : ℕ) : Bool := orK (Nat.beq a0 a1) (Nat.beq (cjK a0 a1) a1)

@[expose] def skip2 (a0 a1 a2 : ℕ) : Bool :=
  orK (Nat.beq a1 a2) (orK (Nat.beq (cjK a1 a2) a2) (notK (Nat.beq (cjK a0 a2) a2)))

@[expose] def skip3 (a0 a1 a2 a3 : ℕ) : Bool :=
  orK (Nat.beq a2 a3) (orK (Nat.beq (cjK a2 a3) a3)
    (orK (notK (Nat.beq (cjK a0 a3) a3)) (notK (Nat.beq (cjK a1 a3) a3))))

@[expose] def skip4 (a0 a1 a2 a3 a4 : ℕ) : Bool :=
  orK (Nat.beq a3 a4) (orK (Nat.beq (cjK a3 a4) a4)
    (orK (notK (Nat.beq (cjK a0 a4) a4))
      (orK (notK (Nat.beq (cjK a1 a4) a4)) (notK (Nat.beq (cjK a2 a4) a4)))))

@[expose] def lvl4 (leaf : ℕ → ℕ → ℕ → ℕ → ℕ → Bool) (a0 a1 a2 a3 a4 : ℕ) : Bool :=
  Bool.rec (leaf a0 a1 a2 a3 a4) true (skip4 a0 a1 a2 a3 a4)

@[expose] def lvl3 (leaf : ℕ → ℕ → ℕ → ℕ → ℕ → Bool) (a0 a1 a2 a3 : ℕ) : Bool :=
  Bool.rec (allK 36 (lvl4 leaf a0 a1 a2 a3)) true (skip3 a0 a1 a2 a3)

@[expose] def lvl2 (leaf : ℕ → ℕ → ℕ → ℕ → ℕ → Bool) (a0 a1 a2 : ℕ) : Bool :=
  Bool.rec (allK 36 (lvl3 leaf a0 a1 a2)) true (skip2 a0 a1 a2)

@[expose] def lvl1 (leaf : ℕ → ℕ → ℕ → ℕ → ℕ → Bool) (a0 a1 : ℕ) : Bool :=
  Bool.rec (allK 36 (lvl2 leaf a0 a1)) true (skip1 a0 a1)

@[expose] def finK (leaf : ℕ → ℕ → ℕ → ℕ → ℕ → Bool) (a0 : ℕ) : Bool :=
  allK 36 (lvl1 leaf a0)

theorem allK_spec {n : ℕ} {f : ℕ → Bool} (h : allK n f = true) : ∀ i < n, f i = true := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    have h' : Bool.rec (motive := fun _ => Bool) false (f n) (allK n f) = true := h
    cases hA : allK n f with
    | false => rw [hA] at h'; exact absurd h' Bool.false_ne_true
    | true =>
      rw [hA] at h'
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact ih hA i hi
      · exact h'

private theorem rec_of_false {x : Bool} {s : Bool}
    (h : Bool.rec (motive := fun _ => Bool) x true s = true) (hs : s = false) : x = true := by
  subst hs; exact h

private theorem beq_f {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hh : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hh) h

private theorem beq_t {a b : ℕ} (h : a = b) : Nat.beq a b = true := by
  rw [h]; exact Nat.beq_refl b

private theorem cjL_chk : allK 36 (fun a => allK 36 (fun b => Nat.beq (cjL a b) (cjN a b))) = true := by
  decide +kernel

theorem cjN_eq_cjK (a b : ℕ) : cjN a b = cjK a b := by
  unfold cjK
  cases ha : Nat.blt a 36
  · rfl
  · cases hb : Nat.blt b 36
    · rfl
    · exact (Nat.eq_of_beq_eq_true (allK_spec (allK_spec cjL_chk a (Nat.le_of_ble_eq_true ha)) b
        (Nat.le_of_ble_eq_true hb))).symm

private theorem skip1_f {a0 a1 : ℕ} (h : a0 ≠ a1 ∧ cjN a0 a1 ≠ a1) : skip1 a0 a1 = false := by
  unfold skip1
  simp only [← cjN_eq_cjK]
  rw [beq_f h.1, beq_f h.2]
  rfl

private theorem skip2_f {a0 a1 a2 : ℕ} (h : a1 ≠ a2 ∧ cjN a1 a2 ≠ a2 ∧ cjN a0 a2 = a2) :
    skip2 a0 a1 a2 = false := by
  unfold skip2
  simp only [← cjN_eq_cjK]
  rw [beq_f h.1, beq_f h.2.1, beq_t h.2.2]
  rfl

private theorem skip3_f {a0 a1 a2 a3 : ℕ}
    (h : a2 ≠ a3 ∧ cjN a2 a3 ≠ a3 ∧ cjN a0 a3 = a3 ∧ cjN a1 a3 = a3) :
    skip3 a0 a1 a2 a3 = false := by
  unfold skip3
  simp only [← cjN_eq_cjK]
  rw [beq_f h.1, beq_f h.2.1, beq_t h.2.2.1, beq_t h.2.2.2]
  rfl

private theorem skip4_f {a0 a1 a2 a3 a4 : ℕ}
    (h : a3 ≠ a4 ∧ cjN a3 a4 ≠ a4 ∧ cjN a0 a4 = a4 ∧ cjN a1 a4 = a4 ∧ cjN a2 a4 = a4) :
    skip4 a0 a1 a2 a3 a4 = false := by
  unfold skip4
  simp only [← cjN_eq_cjK]
  rw [beq_f h.1, beq_f h.2.1, beq_t h.2.2.1, beq_t h.2.2.2.1, beq_t h.2.2.2.2]
  rfl

theorem finK_sound (leaf : ℕ → ℕ → ℕ → ℕ → ℕ → Bool) (a0 a1 a2 a3 a4 : ℕ)
    (h1 : a1 < 36) (h2 : a2 < 36) (h3 : a3 < 36) (h4 : a4 < 36) (h : finK leaf a0 = true)
    (hv : (((a0 ≠ a1 ∧ cjN a0 a1 ≠ a1) ∧ a1 ≠ a2 ∧ cjN a1 a2 ≠ a2 ∧ cjN a0 a2 = a2) ∧
      a2 ≠ a3 ∧ cjN a2 a3 ≠ a3 ∧ cjN a0 a3 = a3 ∧ cjN a1 a3 = a3) ∧
      a3 ≠ a4 ∧ cjN a3 a4 ≠ a4 ∧ cjN a0 a4 = a4 ∧ cjN a1 a4 = a4 ∧ cjN a2 a4 = a4) :
    leaf a0 a1 a2 a3 a4 = true := by
  have e1 := rec_of_false (allK_spec h a1 h1) (skip1_f hv.1.1.1)
  have e2 := rec_of_false (allK_spec e1 a2 h2) (skip2_f hv.1.1.2)
  have e3 := rec_of_false (allK_spec e2 a3 h3) (skip3_f hv.1.2)
  exact rec_of_false (allK_spec e3 a4 h4) (skip4_f hv.2)

end CFSG.StandardType.GGTPK

end
