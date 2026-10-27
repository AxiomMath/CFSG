module

public import CFSG.Quasithin.AppendixH.H12.ModelCore

public section

namespace CFSG.Quasithin.AppendixH.H12.Model

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H12Cert
  CFSG.Quasithin.H13.MatNCert CFSG.Open
open CFSG.ASVolI.ChH (IsConjPt cenIn ptStab)

@[expose] def maskOf (l : List ℕ) : ℕ := l.foldl (fun m v => m ||| (1 <<< v)) 0

private theorem testBit_foldl_mask (l : List ℕ) (m c : ℕ) :
    (l.foldl (fun m v => m ||| (1 <<< v)) m).testBit c =
      (m.testBit c || decide (c ∈ l)) := by
  induction l generalizing m with
  | nil => simp
  | cons v l ih =>
    rw [List.foldl_cons, ih (m ||| (1 <<< v))]
    rw [show decide (c ∈ v :: l) = (decide (v = c) || decide (c ∈ l)) from by
      rw [← Bool.decide_or]
      exact decide_eq_decide.mpr (by
        rw [List.mem_cons]
        constructor
        · rintro (h | h)
          · exact Or.inl h.symm
          · exact Or.inr h
        · rintro (h | h)
          · exact Or.inl h.symm
          · exact Or.inr h)]
    simp only [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_assoc]

theorem testBit_maskOf (l : List ℕ) (c : ℕ) : (maskOf l).testBit c = decide (c ∈ l) := by
  rw [maskOf, testBit_foldl_mask, Nat.zero_testBit, Bool.false_or]

theorem mem_iff_of_maskOf_eq {l l' : List ℕ} (h : maskOf l = maskOf l') (c : ℕ) :
    c ∈ l ↔ c ∈ l' := by
  have h1 : (maskOf l).testBit c = (maskOf l').testBit c := by rw [h]
  rw [testBit_maskOf, testBit_maskOf] at h1
  exact decide_eq_decide.mp h1

@[expose] def treeCheck : List ℕ → List (ℕ × ℕ × ℕ) → Bool
  | _, [] => true
  | seen, (v, p, i) :: rest =>
      seen.contains p && decide (i < 2) && (v == mvN (gG.getD i one12) p) &&
        treeCheck (v :: seen) rest

private theorem gmv_gU' (i c : ℕ) : gmv (gU i) c = mvN (gG.getD i one12) c := by
  rw [gmv, gU_val, colsN_decN (validN_getD validN_gG i)]

theorem treeCheck_reach {root : ℕ} {seen : List ℕ} (hseen : ∀ x ∈ seen, ∃ g ∈ G0, gmv g root = x)
    {t : List (ℕ × ℕ × ℕ)} (h : treeCheck seen t = true) :
    ∀ e ∈ t, ∃ g ∈ G0, gmv g root = e.1 := by
  induction t generalizing seen with
  | nil => simp
  | cons e t ih =>
    rcases e with ⟨v, p, i⟩
    simp only [treeCheck, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq,
      beq_iff_eq] at h
    obtain ⟨⟨⟨hp, hi⟩, hv⟩, hrest⟩ := h
    obtain ⟨g, hg, hgp⟩ := hseen p hp
    have himg : gmv (gU i * g) root = v := by
      rw [gmv_mul, hgp, gmv_gU', hv]
    have hseen' : ∀ x ∈ v :: seen, ∃ g ∈ G0, gmv g root = x := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨gU i * g, G0.mul_mem (gU_mem i) hg, himg⟩
      · exact hseen x hx
    intro e' he'
    rcases List.mem_cons.mp he' with rfl | he'
    · exact ⟨gU i * g, G0.mul_mem (gU_mem i) hg, himg⟩
    · exact ih hseen' hrest e' he'

@[expose] def closedAux (m : ℕ) (vs : List ℕ) : Bool :=
  vs.all fun c =>
    m.testBit (mvN (gG.getD 0 one12) c) && m.testBit (mvN (gG.getD 1 one12) c)

@[expose] def closedCheck (vs : List ℕ) : Bool := closedAux (maskOf vs) vs

theorem closed_of_closedCheck {vs : List ℕ} (h : closedCheck vs = true) {g : Γ12} (hg : g ∈ G0)
    {c : ℕ} (hc : c ∈ vs) : gmv g c ∈ vs := by
  have hall : ∀ c ∈ vs, (maskOf vs).testBit (mvN (gG.getD 0 one12) c) &&
      (maskOf vs).testBit (mvN (gG.getD 1 one12) c) = true :=
    List.all_eq_true.mp h
  refine closed_of_gen (S := fun c => c ∈ vs) ?_ hg hc
  intro i hi c hc
  have hc' := hall c hc
  rw [Bool.and_eq_true] at hc'
  interval_cases i
  · have h0 := hc'.1
    rw [testBit_maskOf] at h0
    exact of_decide_eq_true h0
  · have h1 := hc'.2
    rw [testBit_maskOf] at h1
    exact of_decide_eq_true h1

theorem closed_of_gen_act {α : Type*} (act : Γ12 → α → α) (hone : ∀ x, act 1 x = x)
    (hmul : ∀ g h x, act (g * h) x = act g (act h x)) (S : α → Prop)
    (h : ∀ i < 2, ∀ x, S x → S (act (gU i) x)) {g : Γ12} (hg : g ∈ G0) {x : α} (hx : S x) :
    S (act g x) := by
  refine G_induction (p := fun g => ∀ y, S y → S (act g y)) ?_ ?_ hg x hx
  · intro y hy
    rwa [hone]
  · intro i hi y hy z hz
    rw [hmul]
    exact h i hi (act y z) (hy z hz)

theorem gmv_zero (g : Γ12) : gmv g 0 = 0 := by
  simp only [gmv, mvN_zero]

theorem gmv_eq_zero_iff (g : Γ12) {c : ℕ} (hc : c < 4096) : gmv g c = 0 ↔ c = 0 := by
  constructor
  · intro h
    have h2 : gmv g c = gmv g 0 := by rw [h, gmv_zero]
    refine dc_inj hc (by norm_num) ?_
    apply (glHom g).injective
    rw [glHom_dc, glHom_dc]
    exact congrArg dc h2
  · rintro rfl
    exact gmv_zero g

theorem tU_eq_of_tW_eq {w w' : List ℕ} (h : tW w = tW w') : tU w = tU w' := by
  apply eq_of_colsN_eq
  rw [colsN_tU, colsN_tU, h]

theorem tU_mem_cenIn_spanSub_iff {b : List ℕ} (hb : ∀ c ∈ b, c < 4096) (w : List ℕ) :
    tU w ∈ cenIn glHom G0 (spanSub b) ↔ ∀ c ∈ b, mvN (tW w) c = c := by
  rw [mem_cenIn_iff]
  constructor
  · rintro ⟨_, hfix⟩ c hc
    have h1 := hfix (dc c) (Subgroup.subset_closure ⟨c, hc, rfl⟩)
    rw [glHom_tU] at h1
    exact dc_inj (mvN_lt (validN_evalW gG validN_gG w).2 c) (hb c hc) h1
  · intro hfix
    refine ⟨tU_mem w, ?_⟩
    let K : Subgroup Vec12 :=
      { carrier := {u | glHom (tU w) u = u}
        one_mem' := by change glHom (tU w) 1 = 1; simp
        mul_mem' := by
          intro a b ha hb
          change glHom (tU w) (a * b) = a * b
          rw [map_mul, ha, hb]
        inv_mem' := by
          intro a ha
          change glHom (tU w) (a⁻¹) = a⁻¹
          have hmv : glHom (tU w) (a⁻¹) = (glHom (tU w) a)⁻¹ := MulEquiv.map_inv _ _
          rw [hmv, ha] }
    have hle : spanSub b ≤ K := by
      rw [spanSub, Subgroup.closure_le]
      rintro x ⟨c, hc, rfl⟩
      show glHom (tU w) (dc c) = dc c
      rw [glHom_tU, hfix c hc]
    intro u hu
    exact hle hu

theorem tU_mem_ptStab_spanSub_iff {b : List ℕ} (hb : ∀ c ∈ b, c < 4096) (w : List ℕ) :
    tU w ∈ ptStab glHom G0 (spanSub b) ↔ ∀ c ∈ b, mvN (tW w) c ∈ spanN b := by
  rw [mem_ptStab_iff]
  constructor
  · rintro ⟨_, hstab⟩ c hc
    have hmem : glHom (tU w) (dc c) ∈ smulSub (tU w) (spanSub b) :=
      Subgroup.mem_map_of_mem (glHom (tU w)).toMonoidHom
        (Subgroup.subset_closure ⟨c, hc, rfl⟩)
    rw [hstab] at hmem
    rw [glHom_tU] at hmem
    exact (dc_mem_spanSub_iff hb (mvN_lt (validN_evalW gG validN_gG w).2 c)).mp hmem
  · intro hfix
    refine ⟨tU_mem w, ?_⟩
    have hb' : ∀ c ∈ b.map (gmv (tU w)), c < 4096 := by
      intro c hc
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
      rw [gmv_tU]
      exact spanN_lt hb _ (hfix d hd)
    have hle : smulSub (tU w) (spanSub b) ≤ spanSub b := by
      rw [smulSub_spanSub, spanSub_le_iff hb' hb]
      intro c hc
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
      rw [gmv_tU]
      exact hfix d hd
    exact smulSub_eq_of_le (tU w) (spanSub b) hle

theorem tU_mem_vecStab_iff {c : ℕ} (hc : c < 4096) (w : List ℕ) :
    tU w ∈ vecStab c ↔ mvN (tW w) c = c := by
  rw [mem_vecStab_iff hc]
  constructor
  · rintro ⟨-, h⟩
    simpa only [gmv_tU] using h
  · intro h
    exact ⟨tU_mem w, by simpa only [gmv_tU] using h⟩

theorem isConjPt_symm {G V : Type*} [Group G] [CommGroup V] {ρ : G →* MulAut V} {X : Subgroup G}
    {P P' : Subgroup V} (h : IsConjPt ρ X P P') : IsConjPt ρ X P' P := by
  obtain ⟨g, hg, hPg⟩ := h
  refine ⟨g⁻¹, X.inv_mem hg, ?_⟩
  rw [← hPg, Subgroup.map_map]
  have hcomp : ((ρ g⁻¹).toMonoidHom.comp ((ρ g).toMonoidHom)) = MonoidHom.id V := by
    ext x
    change (ρ g⁻¹ * ρ g) x = x
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  rw [hcomp, Subgroup.map_id]

private theorem card_subtype_mem {α : Type*} (l : List α) (h : l.Nodup) :
    Nat.card {x // x ∈ l} = l.length := by
  have hbij : Function.Bijective
      (fun i : Fin l.length => (⟨l.get i, List.get_mem l i⟩ : {x // x ∈ l})) := by
    constructor
    · intro i j hij
      exact (List.nodup_iff_injective_get.mp h) (Subtype.ext_iff.mp hij)
    · intro x
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp x.2
      exact ⟨i, Subtype.ext hi⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_fin]

theorem length_le_card_range {H K : Type*} [Group H] [Group K] [Finite K] (p : H →* K)
    (l : List H) (hnd : (l.map p).Nodup) : l.length ≤ Nat.card p.range := by
  classical
  have hcard : Nat.card {x // x ∈ l} = l.length := card_subtype_mem l (hnd.of_map p)
  have hinj : Function.Injective
      (fun x : {x // x ∈ l} => (⟨p x.1, MonoidHom.mem_range.mpr ⟨x.1, rfl⟩⟩ : p.range)) := by
    intro x y hxy
    apply Subtype.ext
    exact List.inj_on_of_nodup_map hnd x.2 y.2 (Subtype.ext_iff.mp hxy)
  calc l.length = Nat.card {x // x ∈ l} := hcard.symm
    _ ≤ Nat.card p.range := Nat.card_le_card_of_injective _ hinj

theorem length_le_card_of_words (H : Subgroup Γ12) (ws : List (List ℕ))
    (hnd : (ws.map tW).Nodup) (hmem : ∀ w ∈ ws, tU w ∈ H) : ws.length ≤ Nat.card H := by
  classical
  have hcard : Nat.card {w // w ∈ ws} = ws.length := card_subtype_mem ws (hnd.of_map tW)
  have hinj : Function.Injective
      (fun x : {w // w ∈ ws} => (⟨tU x.1, hmem x.1 x.2⟩ : H)) := by
    intro x y hxy
    apply Subtype.ext
    have h1 : tW x.1 = tW y.1 := by
      have h2 : tU x.1 = tU y.1 := Subtype.ext_iff.mp hxy
      have h3 := congrArg
        (fun u : Γ12 => colsN ((u : Matrix (Fin 12) (Fin 12) (ZMod 2)))) h2
      simpa only [colsN_tU] using h3
    exact List.inj_on_of_nodup_map hnd x.2 y.2 h1
  calc ws.length = Nat.card {w // w ∈ ws} := hcard.symm
    _ ≤ Nat.card H := Nat.card_le_card_of_injective _ hinj

theorem length_le_card_ker_of_words {H : Subgroup Γ12} {n : ℕ} (π : ↥H →* Equiv.Perm (Fin n))
    (ws : List (List ℕ)) (hnd : (ws.map tW).Nodup)
    (hmem : ∀ w ∈ ws, ∃ h : tU w ∈ H, π ⟨tU w, h⟩ = 1) : ws.length ≤ Nat.card π.ker := by
  classical
  have hcard : Nat.card {w // w ∈ ws} = ws.length := card_subtype_mem ws (hnd.of_map tW)
  let g : {w // w ∈ ws} → π.ker := fun x =>
    ⟨⟨tU x.1, (hmem x.1 x.2).choose⟩, by
      rw [MonoidHom.mem_ker]
      exact (hmem x.1 x.2).choose_spec⟩
  have hinj : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    have h1 : tU x.1 = tU y.1 := by
      have h2 : (g x).1 = (g y).1 := Subtype.ext_iff.mp hxy
      exact Subtype.ext_iff.mp h2
    have h3 : tW x.1 = tW y.1 := by
      have h4 := congrArg
        (fun u : Γ12 => colsN ((u : Matrix (Fin 12) (Fin 12) (ZMod 2)))) h1
      simpa only [colsN_tU] using h4
    exact List.inj_on_of_nodup_map hnd x.2 y.2 h3
  calc ws.length = Nat.card {w // w ∈ ws} := hcard.symm
    _ ≤ Nat.card π.ker := Nat.card_le_card_of_injective g hinj

end CFSG.Quasithin.AppendixH.H12.Model
