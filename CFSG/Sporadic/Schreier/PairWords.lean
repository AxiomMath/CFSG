module

public import CFSG.Sporadic.Schreier.CountSpec
public import CFSG.Monster.B.Co2.PermArr
public import Certificates.Data.CFSGNative.PairSchreier.Core

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.PairNative

variable {n : ℕ}

@[expose] def RepW (n : ℕ) (w : List (Array ℕ)) (g : Equiv.Perm (Fin n)) : Prop :=
  ∀ x : Fin n, evR w x = g x

theorem evR_cons (t : Array ℕ) (w : List (Array ℕ)) (p : ℕ) : evR (t :: w) p = evR w t[p]! := rfl

theorem evR_append (w₁ w₂ : List (Array ℕ)) (p : ℕ) : evR (w₁ ++ w₂) p = evR w₂ (evR w₁ p) := by
  simp [evR, List.foldl_append]

theorem repW_nil : RepW n [] (1 : Equiv.Perm (Fin n)) := fun _ => rfl

theorem RepW.cons {t : Array ℕ} {w : List (Array ℕ)} {g h : Equiv.Perm (Fin n)}
    (ht : Rep n t h) (hw : RepW n w g) : RepW n (t :: w) (g * h) := by
  intro x
  rw [evR_cons, ht x, hw (h x), Equiv.Perm.mul_apply]

theorem RepW.append {w₁ w₂ : List (Array ℕ)} {g₁ g₂ : Equiv.Perm (Fin n)} (h₁ : RepW n w₁ g₁)
    (h₂ : RepW n w₂ g₂) : RepW n (w₁ ++ w₂) (g₂ * g₁) := by
  intro x
  rw [evR_append, h₁ x, h₂ (g₁ x), Equiv.Perm.mul_apply]

theorem RepW.single {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) : RepW n [t] g := by
  simpa using RepW.cons ht repW_nil

theorem RepW.flatten {ws : List (List (Array ℕ))} {gs : List (Equiv.Perm (Fin n))}
    (h : List.Forall₂ (RepW n) ws gs) : RepW n ws.flatten gs.reverse.prod := by
  induction h with
  | nil => exact repW_nil
  | cons hw _ ih =>
    rw [List.flatten_cons, List.reverse_cons, List.prod_append, List.prod_singleton]
    exact hw.append ih

theorem RepW.lt {w : List (Array ℕ)} {g : Equiv.Perm (Fin n)} (hw : RepW n w g) {p : ℕ}
    (hp : p < n) : evR w p < n := by
  have := hw ⟨p, hp⟩
  rw [show evR w p = evR w ((⟨p, hp⟩ : Fin n) : ℕ) from rfl, this]
  exact Fin.isLt _

theorem RepW.unique {w : List (Array ℕ)} {g h : Equiv.Perm (Fin n)} (hg : RepW n w g)
    (hh : RepW n w h) : g = h :=
  Equiv.ext fun x => Fin.ext ((hg x).symm.trans (hh x))

theorem evPow_spec {w : List (Array ℕ)} {g : Equiv.Perm (Fin n)} (hw : RepW n w g) (e : ℕ)
    (x : Fin n) : evPow w e x = (g ^ e) x := by
  induction e with
  | zero => rfl
  | succ e ih =>
    rw [evPow, ih, hw ((g ^ e) x), pow_succ', Equiv.Perm.mul_apply]

theorem repW_patW {x y : List (Array ℕ)} {xg yg : Equiv.Perm (Fin n)} (hx : RepW n x xg)
    (hy : RepW n y yg) (pat : List Bool) :
    RepW n (patW x y pat) (pat.map fun b => if b then yg else xg).prod := by
  induction pat with
  | nil => exact repW_nil
  | cons b pat ih =>
    have e : patW x y (b :: pat) = patW x y pat ++ (if b then y else x) := by
      simp [patW, List.map_append, List.flatten_append]
    rw [e, List.map_cons, List.prod_cons]
    refine ih.append ?_
    cases b
    · exact hx
    · exact hy

@[expose] def BaseFaithful (H : Subgroup (Equiv.Perm (Fin n))) (bs : List ℕ) : Prop :=
  ∀ h ∈ H, (∀ x : Fin n, (x : ℕ) ∈ bs → h x = x) → h = 1

theorem fixB_iff {bs : List ℕ} (hbs : ∀ b ∈ bs, b < n) {w : List (Array ℕ)}
    {g : Equiv.Perm (Fin n)} (hw : RepW n w g) (e : ℕ) :
    fixB bs w e = true ↔ ∀ x : Fin n, (x : ℕ) ∈ bs → (g ^ e) x = x := by
  rw [fixB, List.all_eq_true]
  constructor
  · intro h x hx
    have := h x hx
    rw [beq_iff_eq, evPow_spec hw e x] at this
    exact Fin.ext this
  · intro h b hb
    have := h ⟨b, hbs b hb⟩ hb
    rw [beq_iff_eq, show evPow w e b = evPow w e ((⟨b, hbs b hb⟩ : Fin n) : ℕ) from rfl,
      evPow_spec hw e, this]

theorem fixB_iff_eq_one {H : Subgroup (Equiv.Perm (Fin n))} {bs : List ℕ}
    (hH : BaseFaithful H bs) (hbs : ∀ b ∈ bs, b < n) {w : List (Array ℕ)}
    {g : Equiv.Perm (Fin n)} (hw : RepW n w g) (hg : g ∈ H) (e : ℕ) :
    fixB bs w e = true ↔ g ^ e = 1 := by
  rw [fixB_iff hbs hw]
  constructor
  · exact hH _ (H.pow_mem hg e)
  · intro h x _
    rw [h]
    rfl

theorem ordB_iff {H : Subgroup (Equiv.Perm (Fin n))} {bs : List ℕ} (hH : BaseFaithful H bs)
    (hbs : ∀ b ∈ bs, b < n) {w : List (Array ℕ)} {g : Equiv.Perm (Fin n)} (hw : RepW n w g)
    (hg : g ∈ H) {m : ℕ} (hm : 0 < m) : ordB bs w m = true ↔ orderOf g = m := by
  rw [ordB, Bool.and_eq_true, fixB_iff_eq_one hH hbs hw hg, List.all_eq_true]
  constructor
  · rintro ⟨h1, h2⟩
    refine orderOf_eq_of_pow_and_pow_div_prime hm h1 fun p hp hpm hc => ?_
    have hmem : m / p ∈ CFSG.Sporadic.Schreier.Native.divParts m :=
      mem_divParts.2 ⟨p, Nat.le_of_dvd hm hpm, hp.one_lt, hpm, rfl⟩
    have := h2 (m / p) hmem
    rw [(fixB_iff_eq_one hH hbs hw hg _).2 hc] at this
    exact Bool.false_ne_true this
  · intro ho
    refine ⟨ho ▸ pow_orderOf_eq_one _, fun e he => ?_⟩
    obtain ⟨d, hdm, hd1, -, rfl⟩ := mem_divParts.1 he
    have hlt : m / d < m := Nat.div_lt_self hm hd1
    have hne : g ^ (m / d) ≠ 1 :=
      pow_ne_one_of_lt_orderOf (Nat.div_pos hdm (by omega)).ne' (by rw [ho]; exact hlt)
    cases hpf : fixB bs w (m / d)
    · rfl
    · exact absurd ((fixB_iff_eq_one hH hbs hw hg _).1 hpf) hne

theorem patProd_mem (H : Subgroup (Equiv.Perm (Fin n))) {xg yg : Equiv.Perm (Fin n)}
    (hx : xg ∈ H) (hy : yg ∈ H) (pat : List Bool) :
    (pat.map fun b => if b then yg else xg).prod ∈ H := by
  refine H.list_prod_mem fun z hz => ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hz
  cases b
  · exact hx
  · exact hy

theorem condsOK_iff {H : Subgroup (Equiv.Perm (Fin n))} {bs : List ℕ} (hH : BaseFaithful H bs)
    (hbs : ∀ b ∈ bs, b < n) {x y : List (Array ℕ)} {xg yg : Equiv.Perm (Fin n)}
    (hx : RepW n x xg) (hy : RepW n y yg) (hxH : xg ∈ H) (hyH : yg ∈ H)
    {conds : List (List Bool × ℕ)} (hc : ∀ c ∈ conds, 0 < c.2) :
    condsOK bs x y conds = true ↔
      ∀ c ∈ conds, orderOf (c.1.map fun b => if b then yg else xg).prod = c.2 := by
  rw [condsOK, List.all_eq_true]
  refine forall_congr' fun c => forall_congr' fun hcm => ?_
  exact ordB_iff hH hbs (repW_patW hx hy c.1) (patProd_mem H hxH hyH c.1) (hc c hcm)

@[expose] def RepBlocks (n : ℕ) (Bs : List (Array (Array ℕ)))
    (Gs : List (List (Equiv.Perm (Fin n)))) : Prop :=
  List.Forall₂ (fun B G => List.Forall₂ (Rep n) B.toList G) Bs Gs

theorem foldl_array_add_eq_sum {α : Type*} (h : α → ℕ) (B : Array α) :
    B.foldl (fun c t => c + h t) 0 = (B.toList.map h).sum := by
  rw [← Array.foldl_toList, foldl_add_eq_sum, zero_add]

theorem countW_spec {H : Subgroup (Equiv.Perm (Fin n))} {f : List (Array ℕ) → Bool}
    {P : Equiv.Perm (Fin n) → Prop} [DecidablePred P]
    (hfP : ∀ w g, RepW n w g → g ∈ H → (f w = true ↔ P g)) :
    ∀ {Bs : List (Array (Array ℕ))} {Gs : List (List (Equiv.Perm (Fin n)))},
      RepBlocks n Bs Gs → (∀ G ∈ Gs, ∀ t ∈ G, t ∈ H) →
      ∀ {acc : List (Array ℕ)} {g : Equiv.Perm (Fin n)}, RepW n acc g → g ∈ H →
        countW f Bs acc = ((products Gs).map (g * ·)).countP fun h => decide (P h)
  | [], [], .nil, _, acc, g, hg, hgH => by
    simp only [countW, products, List.map_cons, List.map_nil, mul_one]
    by_cases hP : P g
    · simp [hP, (hfP acc g hg hgH).2 hP]
    · have hf : ¬f acc = true := fun hf => hP ((hfP acc g hg hgH).1 hf)
      simp [hP, hf]
  | B :: Bs, G :: Gs, .cons hBG hBs, hH, acc, g, hg, hgH => by
    rw [countW, foldl_array_add_eq_sum, products_map_mul, List.countP_flatMap]
    refine sum_map_eq_of_forall₂ hBG fun t x htx hx => ?_
    exact countW_spec hfP hBs (fun G' hG' => hH G' (List.mem_cons_of_mem G hG'))
      (hg.cons htx) (H.mul_mem hgH (hH G List.mem_cons_self x hx))

theorem countW_spec_nil {H : Subgroup (Equiv.Perm (Fin n))} {f : List (Array ℕ) → Bool}
    {P : Equiv.Perm (Fin n) → Prop} [DecidablePred P]
    (hfP : ∀ w g, RepW n w g → g ∈ H → (f w = true ↔ P g)) {Bs : List (Array (Array ℕ))}
    {Gs : List (List (Equiv.Perm (Fin n)))} (hBG : RepBlocks n Bs Gs)
    (hH : ∀ G ∈ Gs, ∀ t ∈ G, t ∈ H) :
    countW f Bs [] = (products Gs).countP fun h => decide (P h) := by
  rw [countW_spec hfP hBG hH repW_nil H.one_mem]
  simp

theorem flatten_chunksOf {α : Type} {sz : ℕ} (hsz : 0 < sz) :
    ∀ (fuel : ℕ) (l : List α), l.length ≤ fuel → (chunksOf sz fuel l).flatten = l
  | 0, [], _ => rfl
  | 0, _ :: _, h => absurd h (by simp)
  | _ + 1, [], _ => rfl
  | fuel + 1, a :: l, h => by
    rw [chunksOf, List.flatten_cons, flatten_chunksOf hsz fuel _ ?_, List.take_append_drop]
    rw [List.length_drop]
    simp only [List.length_cons] at h ⊢
    omega

theorem countWPar_eq {sz : ℕ} (hsz : 0 < sz) (f : List (Array ℕ) → Bool) (B : Array (Array ℕ))
    (Bs : List (Array (Array ℕ))) : countWPar sz f B Bs = countW f (B :: Bs) [] := by
  have e : countWPar sz f B Bs = (chunksOf sz B.size B.toList).foldl
      (fun c piece => c + piece.foldl (fun c t => c + countW f Bs [t]) 0) 0 := by
    rw [countWPar, List.foldl_map]
    rfl
  rw [e, countW, foldl_array_add_eq_sum, foldl_add_eq_sum, zero_add]
  conv_rhs => rw [← flatten_chunksOf hsz B.size B.toList (by simp)]
  rw [List.map_flatten, List.sum_flatten, List.map_map]
  congr 1
  refine List.map_congr_left fun piece _ => ?_
  rw [Function.comp_apply, foldl_add_eq_sum, zero_add]

theorem toList_foldl_push (R : Array (Array ℕ)) (h : Array ℕ → Array ℕ) (acc : Array (Array ℕ)) :
    (R.foldl (fun acc r => acc.push (h r)) acc).toList = acc.toList ++ R.toList.map h := by
  rw [← Array.foldl_toList, Array.foldl_toList_eq_map]

theorem toList_blockOf_cons (L : Array (Array ℕ)) (Ls : List (Array (Array ℕ))) :
    (blockOf n (L :: Ls)).toList =
      L.toList.flatMap fun t => (blockOf n Ls).toList.map (compA n t) := by
  show (L.foldl (fun acc t => (blockOf n Ls).foldl (fun acc r => acc.push (compA n t r)) acc)
    #[]).toList = _
  rw [← Array.foldl_toList,
    Array.foldl_toList_eq_flatMap (G := fun t => (blockOf n Ls).toList.map (compA n t))]
  · simp
  · intro acc t
    exact toList_foldl_push _ _ acc

theorem forall₂_flatMap_compA {l : List (Array ℕ)} {G : List (Equiv.Perm (Fin n))}
    (hl : List.Forall₂ (Rep n) l G) {R : List (Array ℕ)} {RG : List (Equiv.Perm (Fin n))}
    (hR : List.Forall₂ (Rep n) R RG) :
    List.Forall₂ (Rep n) (l.flatMap fun t => R.map (compA n t))
      (G.flatMap fun x => RG.map (x * ·)) := by
  induction hl with
  | nil => exact .nil
  | cons htx _ ih =>
    rw [List.flatMap_cons, List.flatMap_cons]
    refine forall₂_append ?_ ih
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact hR.imp fun r y hry => rep_compA htx hry

theorem repBlock_blockOf :
    ∀ {Ls : List (Array (Array ℕ))} {Gs : List (List (Equiv.Perm (Fin n)))},
      RepBlocks n Ls Gs → List.Forall₂ (Rep n) (blockOf n Ls).toList (products Gs)
  | [], [], .nil => by
    simp only [blockOf, products, List.toList_toArray]
    exact .cons rep_idA .nil
  | L :: Ls, G :: Gs, .cons hLG hLs => by
    rw [toList_blockOf_cons, products]
    exact forall₂_flatMap_compA hLG (repBlock_blockOf hLs)

theorem products_append {M : Type*} [Monoid M] (A B : List (List M)) :
    products (A ++ B) = (products A).flatMap fun a => (products B).map (a * ·) := by
  induction A with
  | nil => simp [products]
  | cons T A ih =>
    rw [List.cons_append, products, ih, products, List.flatMap_assoc]
    congr 1
    funext t
    rw [List.map_flatMap, List.flatMap_map]
    congr 1
    funext a
    rw [List.map_map]
    congr 1
    funext b
    simp [mul_assoc]

theorem products_map_products {M : Type*} [Monoid M] :
    ∀ groups : List (List (List M)), products (groups.map products) = products groups.flatten
  | [] => rfl
  | A :: groups => by
    rw [List.map_cons, List.flatten_cons, products, products_append,
      products_map_products groups]

end CFSG.Sporadic.Schreier
