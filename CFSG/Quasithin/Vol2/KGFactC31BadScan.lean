
module

public import CFSG.Sporadic.Schreier.PairClasses
public import CFSG.Quasithin.Vol2.KGFactC31Orb

public section

namespace CFSG.Quasithin.KGC31.Native

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.PairNative

@[expose] def countWI (f : List (Array Nat) → List (Array Nat) → Bool) :
    List (Array (Array Nat × Array Nat)) → List (Array Nat) → List (Array Nat) → Nat
  | [], acc, acci => if f acc acci then 1 else 0
  | B :: Bs, acc, acci => B.foldl (fun c tt => c + countWI f Bs (tt.1 :: acc) (acci ++ [tt.2])) 0

@[expose] def levBlockI (L : Array Level) (i : Nat) : Array (Array Nat × Array Nat) :=
  Array.ofFn (n := L[i]!.pts.size) fun k => (L[i]!.tr[k.val]!, L[i]!.trInv[k.val]!)

@[expose] def levBlocksI (L : Array Level) (k : Nat) : List (Array (Array Nat × Array Nat)) :=
  (List.range k).map (levBlockI L)

@[expose] def orbW (t0 : Array Nat) (w wi : List (Array Nat)) : Nat → List (List (Array Nat))
  | 0 => []
  | m + 1 => [t0] :: (orbW t0 w wi m).map fun o => wi ++ o ++ w

@[expose] def commW (bs : List Nat) (t0 : Array Nat) (o : List (Array Nat)) : Bool :=
  baseImgs bs (o ++ [t0]) == baseImgs bs (t0 :: o)

@[expose] def spanAddW (bs : List Nat) (sp : List (List (Array Nat))) (o : List (Array Nat)) :
    List (List (Array Nat)) :=
  if sp.any (fun e => baseImgs bs e == baseImgs bs o) then sp else sp ++ sp.map (· ++ o)

@[expose] def spanW (bs : List Nat) (os : List (List (Array Nat))) : List (List (Array Nat)) :=
  os.foldl (spanAddW bs) [[]]

@[expose] def inSpanW (bs : List Nat) (sp cand : List (List (Array Nat))) : Bool :=
  cand.all fun x => sp.any fun e => baseImgs bs e == baseImgs bs x

@[expose] def normW (bs : List Nat) (w wi : List (Array Nat)) (cand : List (List (Array Nat))) :
    Bool :=
  inSpanW bs (spanW bs cand) (cand.map fun x => wi ++ x ++ w)

@[expose] def candW (bs : List Nat) (norm : Bool) (w wi : List (Array Nat))
    (os : List (List (Array Nat))) (cand : List (List (Array Nat))) : Bool :=
  inSpanW bs (spanW bs os) cand && (!norm || normW bs w wi cand)

@[expose] def goodW (bs : List Nat) (t0 : Array Nat) (ps : List Nat) (norm : Bool)
    (cands : List (List (List (Array Nat)))) (w wi : List (Array Nat)) : Bool :=
  ps.any fun p => fixB bs w p &&
    (!((orbW t0 w wi p).all (commW bs t0)) || cands.any (candW bs norm w wi (orbW t0 w wi p)))

@[expose] def badTest (bs : List Nat) (t0 s : Array Nat) (es ps : List Nat) (norm : Bool)
    (cands : List (List (List (Array Nat)))) (w wi : List (Array Nat)) : Bool :=
  baseImgs bs (wi ++ [s] ++ w ++ [t0]) == baseImgs bs (t0 :: (wi ++ [s] ++ w)) &&
    es.any (fixB bs w) && !(goodW bs t0 ps norm cands w wi)

end CFSG.Quasithin.KGC31.Native

namespace CFSG.Quasithin.KGC31

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.PairNative CFSG.Certificates CFSG.Certificates.Native
  CFSG.Quasithin.KGC31.Native

variable {n : ℕ}

@[expose] def RepBlocksI (n : ℕ) (Bs : List (Array (Array ℕ × Array ℕ)))
    (Gs : List (List (Equiv.Perm (Fin n)))) : Prop :=
  List.Forall₂ (fun B G => List.Forall₂ (fun tt g => Rep n tt.1 g ∧ Rep n tt.2 g⁻¹) B.toList G)
    Bs Gs

theorem sum_eq_zero_iff {α : Type*} {F : α → ℕ} {l : List α} :
    (l.map F).sum = 0 ↔ ∀ a ∈ l, F a = 0 := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

theorem exists_left_of_forall₂ {α β : Type*} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) {b : β} (hb : b ∈ l₂) : ∃ a ∈ l₁, R a b := by
  induction h with
  | nil => exact absurd hb List.not_mem_nil
  | cons hab _ ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨a, ha, h⟩ := ih hb
      exact ⟨a, List.mem_cons_of_mem _ ha, h⟩

theorem exists_right_of_forall₂ {α β : Type*} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) {a : α} (ha : a ∈ l₁) : ∃ b ∈ l₂, R a b := by
  induction h with
  | nil => exact absurd ha List.not_mem_nil
  | cons hab _ ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨b, hb, h⟩ := ih ha
      exact ⟨b, List.mem_cons_of_mem _ hb, h⟩

theorem countWI_eq_zero {f : List (Array ℕ) → List (Array ℕ) → Bool} :
    ∀ {Bs : List (Array (Array ℕ × Array ℕ))} {Gs : List (List (Equiv.Perm (Fin n)))},
      RepBlocksI n Bs Gs → ∀ {acc acci : List (Array ℕ)} {g : Equiv.Perm (Fin n)},
        RepW n acc g → RepW n acci g⁻¹ → countWI f Bs acc acci = 0 →
          ∀ x ∈ products Gs, ∃ w wi, RepW n w (g * x) ∧ RepW n wi (g * x)⁻¹ ∧ f w wi = false
  | [], [], .nil, acc, acci, g, hg, hgi, h0, x, hx => by
    simp only [products, List.mem_singleton] at hx
    subst hx
    refine ⟨acc, acci, by rwa [mul_one], by rwa [mul_one], ?_⟩
    simp only [countWI] at h0
    by_cases hf : f acc acci = true
    · simp [hf] at h0
    · exact Bool.eq_false_iff.mpr hf
  | B :: Bs, G :: Gs, .cons hBG hBs, acc, acci, g, hg, hgi, h0, x, hx => by
    rw [countWI, ← Array.foldl_toList, foldl_add_eq_sum, zero_add, sum_eq_zero_iff] at h0
    simp only [products, List.mem_flatMap, List.mem_map] at hx
    obtain ⟨t, ht, x', hx', rfl⟩ := hx
    obtain ⟨tt, htt, htt1, htt2⟩ := exists_left_of_forall₂ hBG ht
    have hw : RepW n (tt.1 :: acc) (g * t) := hg.cons htt1
    have hwi : RepW n (acci ++ [tt.2]) (g * t)⁻¹ := by
      rw [mul_inv_rev]
      exact hgi.append (RepW.single htt2)
    obtain ⟨w, wi, h1, h2, h3⟩ := countWI_eq_zero hBs hw hwi (h0 tt htt) x' hx'
    exact ⟨w, wi, by rwa [← mul_assoc], by rwa [← mul_assoc], h3⟩

theorem levBlockI_toList (L : Array Level) (i : ℕ) :
    (levBlockI L i).toList =
      (List.range L[i]!.pts.size).map fun k => (L[i]!.tr[k]!, L[i]!.trInv[k]!) := by
  rw [levBlockI, Array.toList_ofFn, List.ofFn_eq_map, ← map_val_finRange, List.map_map]
  rfl

section Chain

variable {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ} {W : Array (List ℤ)}
  {chunks : ℕ}

theorem repBlocksI_levBlocksI (hA : ChainArrays Q O S base W)
    (hF : ChainCheckFacts n O S base W chunks) :
    RepBlocksI n (levBlocksI (rawLevels n S base) Q.baseCount)
      ((List.range Q.baseCount).map (levList n S base)) := by
  rw [RepBlocksI, levBlocksI, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine List.forall₂_same.2 fun i hi => ?_
  have hi' := List.mem_range.1 hi
  rw [levBlockI_toList, levList, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine List.forall₂_same.2 fun k hk => ?_
  exact ⟨hA.rep_levT hF hi' (List.mem_range.1 hk), hA.rep_levTInv hF hi' (List.mem_range.1 hk)⟩

theorem mem_products_of_mem (hA : ChainArrays Q O S base W) (hc : 0 < chunks)
    (h : rawChainOK n O S base W chunks = true) {c : Equiv.Perm (Fin n)}
    (hcQ : c ∈ Q.originalSubgroup) :
    c ∈ products ((List.range Q.baseCount).map (levList n S base)) := by
  have hF := chainCheckFacts h
  have hQ := (validSchreier_of_chainOK hA hc h).1
  rw [← enumeration_eq hA hF]
  exact (mem_enumeration_iff Q hQ c).2 hcQ

end Chain

section Tests

variable {H : Subgroup (Equiv.Perm (Fin n))} {bs : List ℕ}

theorem forall₂_orbW {t0 : Array ℕ} {t₀ y : Equiv.Perm (Fin n)} (ht : Rep n t0 t₀)
    {w wi : List (Array ℕ)} (hw : RepW n w y) (hwi : RepW n wi y⁻¹) :
    ∀ m, List.Forall₂ (RepW n) (orbW t0 w wi m)
      ((List.range m).map fun j => y ^ j * t₀ * (y ^ j)⁻¹)
  | 0 => by simp [orbW]
  | m + 1 => by
    rw [orbW, List.range_succ_eq_map, List.map_cons, List.map_map]
    refine .cons (by simpa using RepW.single ht) ?_
    have ih := forall₂_orbW ht hw hwi m
    rw [List.forall₂_map_right_iff] at ih
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine ih.imp fun {o j} hoj => ?_
    show RepW n (wi ++ o ++ w) (y ^ (j + 1) * t₀ * (y ^ (j + 1))⁻¹)
    have e : y ^ (j + 1) * t₀ * (y ^ (j + 1))⁻¹ = y * (y ^ j * t₀ * (y ^ j)⁻¹ * y⁻¹) := by
      rw [pow_succ']
      group
    rw [e]
    exact (hwi.append hoj).append hw

theorem foldl_spanAddW_mem (K : Subgroup (Equiv.Perm (Fin n))) :
    ∀ {os : List (List (Array ℕ))} {osG : List (Equiv.Perm (Fin n))},
      List.Forall₂ (RepW n) os osG → (∀ g ∈ osG, g ∈ K) →
      ∀ {sp : List (List (Array ℕ))}, (∀ e ∈ sp, ∃ g ∈ K, RepW n e g) →
        ∀ e ∈ os.foldl (spanAddW bs) sp, ∃ g ∈ K, RepW n e g
  | [], [], .nil, _, sp, hsp => hsp
  | o :: os, g :: osG, .cons hog hos, hK, sp, hsp => by
    rw [List.foldl_cons]
    refine foldl_spanAddW_mem K hos (fun x hx => hK x (List.mem_cons_of_mem _ hx)) ?_
    intro e he
    rw [spanAddW] at he
    split_ifs at he with hany
    · exact hsp e he
    · rcases List.mem_append.mp he with he | he
      · exact hsp e he
      · obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
        obtain ⟨g', hg'K, hg'⟩ := hsp e' he'
        exact ⟨g * g', K.mul_mem (hK g List.mem_cons_self) hg'K, hg'.append hog⟩

theorem spanW_mem {os : List (List (Array ℕ))} {osG : List (Equiv.Perm (Fin n))}
    (hos : List.Forall₂ (RepW n) os osG) :
    ∀ e ∈ spanW bs os, ∃ g ∈ Subgroup.closure {x | x ∈ osG}, RepW n e g :=
  foldl_spanAddW_mem _ hos (fun g hg => Subgroup.subset_closure hg) fun e he => by
    rw [List.mem_singleton] at he
    exact ⟨1, Subgroup.one_mem _, he ▸ repW_nil⟩

theorem mem_of_inSpanW (hH : BaseFaithful H bs) (hbs : ∀ b ∈ bs, b < n)
    {K : Subgroup (Equiv.Perm (Fin n))} (hKH : K ≤ H) {sp : List (List (Array ℕ))}
    (hsp : ∀ e ∈ sp, ∃ g ∈ K, RepW n e g) {cand : List (List (Array ℕ))}
    {candG : List (Equiv.Perm (Fin n))} (hc : List.Forall₂ (RepW n) cand candG)
    (hcH : ∀ x ∈ candG, x ∈ H) (h : inSpanW bs sp cand = true) : ∀ x ∈ candG, x ∈ K := by
  intro x hx
  obtain ⟨xw, hxw, hxwx⟩ := exists_left_of_forall₂ hc hx
  rw [inSpanW, List.all_eq_true] at h
  obtain ⟨e, he, heq⟩ := List.any_eq_true.mp (h xw hxw)
  obtain ⟨g, hgK, heg⟩ := hsp e he
  rw [beq_iff_eq] at heq
  rw [← eq_of_baseImgs_eq hH hbs heg hxwx (hKH hgK) (hcH x hx) heq]
  exact hgK

theorem baseImgs_eq_of_eq (hbs : ∀ b ∈ bs, b < n) {w₁ w₂ : List (Array ℕ)}
    {g : Equiv.Perm (Fin n)} (h₁ : RepW n w₁ g) (h₂ : RepW n w₂ g) :
    baseImgs bs w₁ = baseImgs bs w₂ :=
  (baseImgs_eq_iff hbs h₁ h₂).2 fun _ _ => rfl

end Tests

section Scan

variable {H : Subgroup (Equiv.Perm (Fin n))} {bs : List ℕ}

theorem closure_orbit_le (y t₀ : Equiv.Perm (Fin n)) (p : ℕ) :
    Subgroup.closure {x | x ∈ (List.range p).map fun j => y ^ j * t₀ * (y ^ j)⁻¹} ≤
      orbSub y t₀ := by
  rw [Subgroup.closure_le]
  intro x hx
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
  exact conj_mem_orbSub y t₀ j

theorem exists_cand_of_scan {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ}
    {W : Array (List ℤ)} {chunks : ℕ} (hA : ChainArrays Q O S base W) (hc : 0 < chunks)
    (hchk : rawChainOK n O S base W chunks = true) (hH : BaseFaithful H bs)
    (hbs : ∀ b ∈ bs, b < n) (hQH : Q.originalSubgroup ≤ H) {t0 s hT hTi : Array ℕ}
    {t₀ sg h : Equiv.Perm (Fin n)} (ht : Rep n t0 t₀) (hs : Rep n s sg) (hh : Rep n hT h)
    (hhi : Rep n hTi h⁻¹) (ht₀H : t₀ ∈ H) (hhH : h ∈ H) {es ps : List ℕ}
    {norm : Bool} {cands : List (List (List (Array ℕ)))}
    {candG : List (List (Equiv.Perm (Fin n)))}
    (hcands : List.Forall₂ (List.Forall₂ (RepW n)) cands candG)
    (hcandH : ∀ cg ∈ candG, ∀ x ∈ cg, x ∈ H)
    (h0 : countWI (badTest bs t0 s es ps norm cands)
      (levBlocksI (rawLevels n S base) Q.baseCount) [hT] [hTi] = 0)
    {c : Equiv.Perm (Fin n)} (hcQ : c ∈ Q.originalSubgroup)
    (hys : h * c * t₀ * (h * c)⁻¹ = sg) (he : ∃ e ∈ es, (h * c) ^ e = 1)
    (hcomm : ∀ j : ℕ, t₀ * ((h * c) ^ j * t₀ * ((h * c) ^ j)⁻¹) =
      (h * c) ^ j * t₀ * ((h * c) ^ j)⁻¹ * t₀) :
    ∃ cg ∈ candG, (∀ x ∈ cg, x ∈ orbSub (h * c) t₀) ∧
      (norm = true → ∀ x ∈ cg, h * c * x * (h * c)⁻¹ ∈ Subgroup.closure {x | x ∈ cg}) := by
  have hF := chainCheckFacts hchk
  have hmem := mem_products_of_mem hA hc hchk hcQ
  obtain ⟨w, wi, hw, hwi, hf⟩ :=
    countWI_eq_zero (repBlocksI_levBlocksI hA hF) (RepW.single hh) (RepW.single hhi) h0 c hmem
  set y := h * c with hy
  have hyH : y ∈ H := H.mul_mem hhH (hQH hcQ)
  have hysy : RepW n (wi ++ [s] ++ w) (y * (sg * y⁻¹)) := (hwi.append (RepW.single hs)).append hw
  have hA1 : (baseImgs bs (wi ++ [s] ++ w ++ [t0]) == baseImgs bs (t0 :: (wi ++ [s] ++ w))) =
      true := by
    rw [beq_iff_eq]
    have e1 : y * (sg * y⁻¹) = y ^ 2 * t₀ * (y ^ 2)⁻¹ := by
      simp only [← hys, sq, mul_inv_rev, mul_assoc]
    have hc2 := hcomm 2
    have h1 : RepW n (wi ++ [s] ++ w ++ [t0]) (t₀ * (y ^ 2 * t₀ * (y ^ 2)⁻¹)) := by
      rw [← e1]
      exact hysy.append (RepW.single ht)
    have h2 : RepW n (t0 :: (wi ++ [s] ++ w)) (t₀ * (y ^ 2 * t₀ * (y ^ 2)⁻¹)) := by
      rw [hc2, ← e1]
      exact hysy.cons ht
    exact baseImgs_eq_of_eq hbs h1 h2
  have hB : es.any (fixB bs w) = true := by
    obtain ⟨e, hes, hye⟩ := he
    exact List.any_eq_true.mpr ⟨e, hes, (fixB_iff_eq_one hH hbs hw hyH e).2 hye⟩
  rw [badTest, hA1, hB, Bool.true_and, Bool.true_and, Bool.not_eq_false'] at hf
  rw [goodW, List.any_eq_true] at hf
  obtain ⟨p, -, hp⟩ := hf
  rw [Bool.and_eq_true] at hp
  obtain ⟨-, hp⟩ := hp
  have horb := forall₂_orbW ht hw hwi p
  have hall : (orbW t0 w wi p).all (commW bs t0) = true := by
    rw [List.all_eq_true]
    intro o ho
    obtain ⟨g, hg, hog⟩ := exists_right_of_forall₂ horb ho
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hg
    rw [commW, beq_iff_eq]
    refine baseImgs_eq_of_eq hbs (hog.append (RepW.single ht)) ?_
    rw [hcomm j]
    exact hog.cons ht
  rw [hall, Bool.not_true, Bool.false_or, List.any_eq_true] at hp
  obtain ⟨cand, hcand, hok⟩ := hp
  obtain ⟨cg, hcg, hccg⟩ := exists_right_of_forall₂ hcands hcand
  rw [candW, Bool.and_eq_true] at hok
  obtain ⟨hin, hnorm⟩ := hok
  have horbH : ∀ g ∈ (List.range p).map (fun j => y ^ j * t₀ * (y ^ j)⁻¹), g ∈ H := by
    intro g hg
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hg
    exact H.mul_mem (H.mul_mem (H.pow_mem hyH j) ht₀H) (H.inv_mem (H.pow_mem hyH j))
  have hclH : Subgroup.closure {x | x ∈ (List.range p).map (fun j => y ^ j * t₀ * (y ^ j)⁻¹)} ≤
      H := (Subgroup.closure_le H).2 fun g hg => horbH g hg
  refine ⟨cg, hcg, fun x hx => closure_orbit_le y t₀ p
    (mem_of_inSpanW hH hbs hclH (spanW_mem horb) hccg (hcandH cg hcg) hin x hx), ?_⟩
  intro hn x hx
  rw [hn, Bool.not_true, Bool.false_or, normW] at hnorm
  have hcgH := hcandH cg hcg
  have hclcH : Subgroup.closure {x | x ∈ cg} ≤ H := (Subgroup.closure_le H).2 fun g hg => hcgH g hg
  have hconj : List.Forall₂ (RepW n) (cand.map fun x => wi ++ x ++ w)
      (cg.map fun x => y * x * y⁻¹) := by
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine hccg.imp fun {xw xg} hx => ?_
    have := (hwi.append hx).append hw
    rwa [← mul_assoc] at this
  have hconjH : ∀ z ∈ cg.map (fun x => y * x * y⁻¹), z ∈ H := by
    intro z hz
    obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hz
    exact H.mul_mem (H.mul_mem hyH (hcgH x' hx')) (H.inv_mem hyH)
  exact mem_of_inSpanW hH hbs hclcH (spanW_mem hccg) hconj hconjH hnorm _
    (List.mem_map.mpr ⟨x, hx, rfl⟩)

end Scan

end CFSG.Quasithin.KGC31

end
