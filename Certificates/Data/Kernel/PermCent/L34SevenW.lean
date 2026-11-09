module

public import Certificates.Data.Kernel.PermCent.L34SevenQ
public import Certificates.Data.Kernel.PermCent.L34SevenWData
public import Certificates.Data.Kernel.PermCent.L34SevenWIx
public import Certificates.Data.Kernel.Lnth
public import CFSG.Certificates.Kernel.Common.ListSlices

public section

namespace CFSG.Certificates.Kernel.PkCV.L34T

open CFSG.GH74.KGroups.L34 CFSG.KC CFSG.KC.Enum CFSG.KS CFSG.KS.ListSlices
  CFSG.Certificates.Kernel.PkEnum

@[expose] noncomputable def sevenW (ws : List Nat) (sf : CV 42 → Bool) (a : CV 42) : Bool :=
  !powOneC a 2 || sf a || ws.any fun q =>
    eq22 42 (wC 42) (mask (wC 42)) a.1 q q a.1 || eq3 42 (wC 42) (mask (wC 42)) a.1 q a.1 q

@[expose] noncomputable def canonB (x : Nat) : Bool :=
  Nat.beq (x >>> (42 * wC 42)) 0 && allN 42 (fun i => Nat.blt (img 42 x i) 42) &&
    allN 42 (fun a => allN 42 fun b => Nat.beq a b || !Nat.beq (img 42 x a) (img 42 x b))

theorem canon_of_canonB {x : Nat} (h : canonB x = true) : Canon 42 x := by
  unfold canonB at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, CFSG.KS.PK.allN_iff,
    CFSG.KS.PK.allN_iff] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  refine ⟨h0, fun i hi => Nat.blt_eq.mp (h1 i hi), fun a ha b hb e => ?_⟩
  have h3 := CFSG.KS.PK.allN_iff.mp (h2 a ha) b hb
  rw [Bool.or_eq_true, Nat.beq_eq] at h3
  rcases h3 with h3 | h3
  · exact h3
  · rw [Bool.not_eq_true', Nat.beq_eq.mpr e] at h3
    exact absurd h3 Bool.noConfusion

@[expose] noncomputable def mkCV (x : Nat) : CV 42 :=
  if h : canonB x = true then ⟨x, canon_of_canonB h⟩ else 1

@[expose] noncomputable def LA : List (List (CV 42)) := laC.map fun T => T.map mkCV

@[expose] noncomputable def laOK : Bool :=
  (levelsC QA).map (fun T => T.map Subtype.val) == LA.map (fun T => T.map Subtype.val)

theorem levelsC_QA (h : laOK = true) : levelsC QA = LA := by
  have hinj : Function.Injective (fun T : List (CV 42) => T.map Subtype.val) :=
    List.map_injective_iff.mpr Subtype.val_injective
  exact List.map_injective_iff.mpr hinj (beq_iff_eq.mp h)

@[expose] noncomputable def pkOKB (p : Nat × Nat) : Bool :=
  allN 42 fun i => Nat.blt (CFSG.KS.PK.fd (wd 42) p.1 i) 42 &&
    Nat.blt (CFSG.KS.PK.fd (wd 42) p.2 i) 42 &&
    Nat.beq (CFSG.KS.PK.fd (wd 42) p.2 (CFSG.KS.PK.fd (wd 42) p.1 i)) i &&
    Nat.beq (CFSG.KS.PK.fd (wd 42) p.1 (CFSG.KS.PK.fd (wd 42) p.2 i)) i

theorem pkOK_of_pkOKB {p : Nat × Nat} (h : pkOKB p = true) : PkOK 42 p := by
  intro i hi
  have h1 := CFSG.KS.PK.allN_iff.mp h i hi
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h1
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h1
  exact ⟨a, b, c, d⟩

@[expose] noncomputable def mkF (x : Nat) : Fin 42 :=
  if h : x < 42 then ⟨x, h⟩ else ⟨0, Nat.zero_lt_succ _⟩

@[expose] noncomputable def mkVP (p : Nat × Nat) : VP 42 :=
  if h : pkOKB p = true then ⟨p, pkOK_of_pkOKB h⟩ else oneV 42

@[expose] noncomputable def LP : List (Fin 42 × StV 42) :=
  lpC.map fun e => (mkF e.1, ⟨e.2.map fun x => (mkF x.1, mkVP x.2), []⟩)

@[expose] def entL (L : List (Fin 42 × StV 42)) : List (Fin 42 × List (Fin 42 × VP 42)) :=
  L.map fun bq => (bq.1, bq.2.entries)

@[expose] def codeL (E : List (Fin 42 × List (Fin 42 × VP 42))) :
    List (Nat × List (Nat × Nat × Nat)) :=
  E.map fun be => (be.1.val, be.2.map fun e => (e.1.val, e.2.1))

@[expose] noncomputable def lpOK : Bool :=
  codeL (entL (levelsV (strongV QP) QP.base 0)) == codeL (entL LP)

theorem codeL_inj : Function.Injective codeL := by
  have hG : Function.Injective (fun e : Fin 42 × VP 42 => (e.1.val, e.2.1)) := by
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact Prod.ext (Fin.ext hxy.1) (Subtype.ext hxy.2)
  refine List.map_injective_iff.mpr fun a b h => ?_
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (Fin.ext h.1) (List.map_injective_iff.mpr hG h.2)

theorem siftResV_entL : ∀ (L₁ L₂ : List (Fin 42 × StV 42)), entL L₁ = entL L₂ →
    ∀ h, siftResV L₁ h = siftResV L₂ h
  | [], [], _, _ => rfl
  | [], _ :: _, e, _ => absurd e (by simp [entL])
  | _ :: _, [], e, _ => absurd e (by simp [entL])
  | (b₁, q₁) :: L₁, (b₂, q₂) :: L₂, e, h => by
    simp only [entL, List.map_cons, List.cons.injEq, Prod.mk.injEq] at e
    obtain ⟨⟨rfl, he⟩, e⟩ := e
    simp only [siftResV, he]
    cases q₂.entries.lookup (pkp h b₁) with
    | none => rfl
    | some t => exact siftResV_entL L₁ L₂ e _

theorem siftV_of_codes {L₁ L₂ : List (Fin 42 × StV 42)}
    (h : (codeL (entL L₁) == codeL (entL L₂)) = true) (x : VP 42) : siftV L₁ x = siftV L₂ x := by
  unfold siftV
  rw [siftResV_entL _ _ (codeL_inj (beq_iff_eq.mp h))]

theorem siftC_QP (hP : lpOK = true) (c : CV 42) : siftC QP c 0 = siftV LP (codeV (ev c)) := by
  rw [siftC]
  rw [lpOK] at hP
  exact siftV_of_codes hP _

@[expose] noncomputable def sevenT (t r : CV 42) : Bool :=
  !(sqPt t r 0 && sqPt t r 41) ||
    sevenW (lnth [] wTab (img 42 t.1 0)) (fun a => siftV LP (codeV (ev a))) (t * r)

@[expose] noncomputable def sevenS (s : Nat) : Bool :=
  (productsC LA.tail).all (sevenT (lnth 1 (LA.headD []) s))

@[expose] noncomputable def prodIx (L : List (List (CV 42))) : List Nat → CV 42 :=
  List.rec (motive := fun _ => List Nat → CV 42) (fun _ => 1)
    (fun T _ ih ix => List.rec (motive := fun _ => CV 42) 1 (fun i ix' _ => lnth 1 T i * ih ix') ix)
    L

@[expose] noncomputable def inIx (L : List (List (CV 42))) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun ix => ix.isEmpty)
    (fun T _ ih ix => List.rec (motive := fun _ => Bool) false
      (fun i ix' _ => Nat.blt i T.length && ih ix') ix) L

@[expose] noncomputable def vW (x : Nat) (ix : List Nat) : Bool :=
  inIx (levelsC QP) ix && Nat.beq (prodIx (levelsC QP) ix).1 x &&
    (powOneC (prodIx (levelsC QP) ix) 7 && !powOneC (prodIx (levelsC QP) ix) 1)

@[expose] noncomputable def chkW (xs : List Nat) : List (List Nat) → Bool :=
  List.rec (motive := fun _ => List (List Nat) → Bool) (fun _ => true)
    (fun x _ ih ixs => List.rec (motive := fun _ => Bool) false
      (fun ix ixs' _ => vW x ix && ih ixs') ixs) xs

@[expose] noncomputable def wOK : Bool := chkW wTab.flatten wIx

theorem lnth_mem {α : Type} (d : α) : ∀ (T : List α) (i : Nat), i < T.length → lnth d T i ∈ T
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | a :: T, 0, _ => by rw [lnth_cons_zero]; exact List.mem_cons_self
  | a :: T, i + 1, h => by
    rw [lnth_cons_succ]
    exact List.mem_cons_of_mem a (lnth_mem d T i (by simp at h; omega))

theorem prodIx_mem : ∀ (L : List (List (CV 42))) (ix : List Nat), inIx L ix = true →
    prodIx L ix ∈ productsC L
  | [], _, _ => List.mem_singleton.mpr rfl
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | T :: Ts, i :: ix, h => by
    change (Nat.blt i T.length && inIx Ts ix) = true at h
    rw [Bool.and_eq_true, Nat.blt_eq] at h
    change lnth 1 T i * prodIx Ts ix ∈ T.flatMap fun t => (productsC Ts).map (t * ·)
    exact List.mem_flatMap.mpr ⟨_, lnth_mem 1 T i h.1,
      List.mem_map.mpr ⟨_, prodIx_mem Ts ix h.2, rfl⟩⟩

theorem vW_sound {x : Nat} {ix : List Nat} (h : vW x ix = true) : ∃ q ∈ l7P, q.1 = x := by
  unfold vW at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨hi, hx⟩, h7⟩ := h
  refine ⟨_, List.mem_filter.mpr ⟨?_, h7⟩, hx⟩
  rw [elemsC_eq_levelsC]
  exact prodIx_mem _ ix hi

theorem chkW_sound : ∀ (xs : List Nat) (ixs : List (List Nat)), chkW xs ixs = true →
    ∀ x ∈ xs, ∃ q ∈ l7P, q.1 = x
  | [], _, _, x, hx => absurd hx List.not_mem_nil
  | _ :: _, [], h, _, _ => absurd h Bool.false_ne_true
  | y :: xs, ix :: ixs, h, x, hx => by
    change (vW y ix && chkW xs ixs) = true at h
    rw [Bool.and_eq_true] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact vW_sound h.1
    · exact chkW_sound xs ixs h.2 x hx

@[expose] noncomputable def lenOK : Bool :=
  Nat.beq (LA.headD []).length 42 && !LA.isEmpty

theorem all_lnth {α : Type} (d : α) (f : α → Bool) : ∀ (T : List α),
    (∀ s < T.length, f (lnth d T s) = true) → T.all f = true
  | [], _ => rfl
  | a :: T, h => by
    rw [List.all_cons, Bool.and_eq_true]
    refine ⟨h 0 (by simp), all_lnth d f T fun s hs => ?_⟩
    have := h (s + 1) (by simp; omega)
    rwa [lnth_cons_succ] at this

theorem mem_flatten_of_lnth {α : Type} {x : α} : ∀ {G : List (List α)} {p : Nat},
    x ∈ lnth [] G p → x ∈ G.flatten
  | [], _, h => by rw [lnth_nil] at h; exact absurd h List.not_mem_nil
  | g :: G, 0, h => by
    rw [lnth_cons_zero] at h
    exact List.mem_flatten.mpr ⟨g, List.mem_cons_self, h⟩
  | g :: G, p + 1, h => by
    rw [lnth_cons_succ] at h
    rw [List.flatten_cons]
    exact List.mem_append_right _ (mem_flatten_of_lnth h)

theorem sevenF_of_sevenW {ws : List Nat} {l7 : List (CV 42)} {sf sf' : CV 42 → Bool} {a : CV 42}
    (hw : ∀ x ∈ ws, ∃ q ∈ l7, q.1 = x) (h : sevenW ws sf' a = true) (hsf : ∀ a, sf' a = sf a) :
    sevenF l7 sf a = true := by
  unfold sevenW at h
  unfold sevenF
  rw [Bool.or_eq_true] at h ⊢
  rcases h with h | h
  · rw [hsf] at h
    exact Or.inl h
  · right
    rw [List.any_eq_true] at h ⊢
    obtain ⟨x, hx, hq⟩ := h
    obtain ⟨q, hq7, rfl⟩ := hw x hx
    exact ⟨q, hq7, hq⟩

theorem sevenH_of_slices (hw : wOK = true) (hA : laOK = true) (hP : lpOK = true) (hl : lenOK = true)
    (hS : ∀ s < 42, sevenS s = true) : sevenH = true := by
  unfold lenOK at hl
  rw [Bool.and_eq_true, Nat.beq_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hl
  obtain ⟨hlen, hne⟩ := hl
  have hW : ∀ p, ∀ x ∈ lnth [] wTab p, ∃ q ∈ l7P, q.1 = x := fun p x hx =>
    chkW_sound _ _ hw x (mem_flatten_of_lnth hx)
  unfold sevenH
  rw [levelsC_QA hA]
  unfold sevenS at hS
  generalize LA = L at hS hlen hne
  obtain ⟨T, Ts, rfl⟩ := List.exists_cons_of_ne_nil hne
  rw [List.headD_cons] at hS hlen
  rw [List.tail_cons] at hS
  change T.all (fun t => (productsC Ts).all fun r => _) = true
  apply all_lnth 1
  intro s hs
  have h := hS s (hlen ▸ hs)
  rw [List.all_eq_true] at h ⊢
  intro r hr
  have hr' := h r hr
  unfold sevenT at hr'
  rw [Bool.or_eq_true] at hr' ⊢
  rcases hr' with hp | hp
  · exact Or.inl hp
  · exact Or.inr (sevenF_of_sevenW (hW _) hp fun a => (siftC_QP hP a).symm)

end CFSG.Certificates.Kernel.PkCV.L34T

end
