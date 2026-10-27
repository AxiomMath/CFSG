module

public import CFSG.Sporadic.FischerOddCore.Fi24Free
public import CFSG.Sporadic.FischerOddCore.Fi24TabFacts
public import CFSG.Fischer.Polar.Facts

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
open CFSG.Sporadic.Fi24.Native
open CFSG.Sporadic.Fi24 (R J M MR JR tR D24 jR cls)
open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog
open scoped commutatorElement

attribute [local instance] CFSG.Sporadic.Fi24.rAction

theorem fi24_rep_unique
    {T : Table} {g h : R} (hg : Rep 306936 T g) (hh : Rep 306936 T h) :
    g = h := by
  have hk : ∀ k : Fin 306936, (h⁻¹ * g) • k = k := by
    intro k
    have e : g • k = h • k := Fin.ext (by
      rw [← idx_of_lt g k.isLt, ← idx_of_lt h k.isLt, ← hg k.val k.isLt, ← hh k.val k.isLt])
    rw [mul_smul, e, inv_smul_smul]
  have := Fi24.eq_one_of_smul_eq hk
  rw [inv_mul_eq_one] at this
  exact this.symm

theorem card_fixed1_D24
    {T : Table} {r : R} (hT : Rep 306936 T r) :
    Nat.card {x : D24 // r * x * r⁻¹ = x} = fi24Fix T := by
  have h := card_fixed_D24 [(T, r)] (by simpa using hT)
  have e : {x : D24 // r * x * r⁻¹ = x} ≃
      {x : D24 // ∀ p ∈ [(T, r)], p.2 * x * p.2⁻¹ = x} :=
    Equiv.subtypeEquivRight fun x => by simp
  rw [Nat.card_congr e, h]
  unfold fi24Fix
  exact List.countP_congr fun i _ => by simp

theorem card_fixed2_D24
    {T W : Table} {r w : R} (hT : Rep 306936 T r) (hW : Rep 306936 W w) :
    Nat.card {x : D24 // r * x * r⁻¹ = x ∧ ∀ _i : Fin 1, w * x * w⁻¹ = x} =
      (List.range nPts).countP fun i => ap T i == i && ap W i == i := by
  have h := card_fixed_D24 [(T, r), (W, w)] (by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact hT
    · exact hW)
  have e : {x : D24 // r * x * r⁻¹ = x ∧ ∀ _i : Fin 1, w * x * w⁻¹ = x} ≃
      {x : D24 // ∀ p ∈ [(T, r), (W, w)], p.2 * x * p.2⁻¹ = x} :=
    Equiv.subtypeEquivRight fun x => by simp
  rw [Nat.card_congr e, h]
  exact List.countP_congr fun i _ => by simp

abbrev fi24L : Array Table := Fi24.letters

abbrev fi24TP : Table :=
  tPTable Fi24.orb (wordT nPts (letterJ fi24L) normWords[0]!)
    (wordT nPts (letterJ fi24L) normWords[1]!)

abbrev fi24G23 : ℤ → Table :=
  fi24GenT fi24M0T (invT nPts fi24M0T) fi24M1T (invT nPts fi24M1T)

abbrev fi24DT : Table := powT nPts 7 (wordT nPts fi24G23 CFSG.Sporadic.Fi23.Native.dLetters)

abbrev fi24WT : Table := wordT nPts fi24G23 fi23WordW

abbrev fi24U2T : Table :=
  compT nPts fi24DT (compT nPts fi24M0T (compT nPts fi24DT (invT nPts fi24M0T)))

abbrev fi24U3T : Table :=
  compT nPts fi24U2T (compT nPts fi24WT (compT nPts fi24DT (invT nPts fi24WT)))

abbrev fi24D :
    R := fi23ToR CFSG.Sporadic.Fi23.d

abbrev fi24U2 :
    R := fi23ToR fi23U2

abbrev fi24U3 :
    R := fi23ToR fi23U3

theorem card_fixed_D24_pts (r : R) :
    Nat.card {x : D24 // r * x * r⁻¹ = x} = Nat.card {k : Fin 306936 // r • k = k} := by
  symm
  refine Nat.card_congr (Equiv.subtypeEquiv Fi24.clsEquiv fun k => ?_)
  rw [Fi24.clsEquiv_apply, ← Fi24.cls_smul_R]
  exact ⟨fun h => by rw [h], fun h => Fi24.cls_injective h⟩

theorem rep_fi24TP :
    Rep 306936 fi24TP tR :=
  Fi24.rep_tR_of_tPOK Fi24.rep_nA Fi24.rep_nB
    (tPOK_tPTable _ _ _ fun p hp hpn => (Fi24.tree_facts p hpn hp).1)

theorem rep_fi24G23
    (z : ℤ) : Rep 306936 (fi24G23 z) (fi23ToR (CFSG.Sporadic.Fi23.genG z)) :=
  rep_fi24GenT rep_fi24M0T (rep_invT24 rep_fi24M0T) rep_fi24M1T (rep_invT24 rep_fi24M1T) z

theorem rep_fi24DT :
    Rep 306936 fi24DT fi24D := by
  have h := Rep.powT (n := 306936) (by norm_num)
    (rep_fi24WordT rep_fi24M0T (rep_invT24 rep_fi24M0T) rep_fi24M1T
      (rep_invT24 rep_fi24M1T) CFSG.Sporadic.Fi23.Native.dLetters) 7
  rw [← map_pow, CFSG.Sporadic.Fi23.wordG_dLetters] at h
  exact h

theorem rep_fi24WT :
    Rep 306936 fi24WT (fi23ToR (wordG CFSG.Sporadic.Fi23.genG fi23WordW)) :=
  rep_fi24WordT rep_fi24M0T (rep_invT24 rep_fi24M0T) rep_fi24M1T (rep_invT24 rep_fi24M1T)
    fi23WordW

theorem rep_fi24U2T :
    Rep 306936 fi24U2T fi24U2 := by
  have hAi : Rep 306936 (invT nPts fi24M0T) (fi23ToR (CFSG.Sporadic.Fi23.genG (-1))) := by
    have := rep_invT24 rep_fi24M0T
    rwa [← map_inv, show (CFSG.Sporadic.Fi23.a)⁻¹ = CFSG.Sporadic.Fi23.genG (-1) by
      simp [CFSG.Sporadic.Fi23.genG]] at this
  have hA : Rep 306936 fi24M0T (fi23ToR (CFSG.Sporadic.Fi23.genG 1)) := by
    have := rep_fi24M0T
    rwa [show CFSG.Sporadic.Fi23.a = CFSG.Sporadic.Fi23.genG 1 by
      simp [CFSG.Sporadic.Fi23.genG]] at this
  have h := Rep.compT rep_fi24DT (Rep.compT hA (Rep.compT rep_fi24DT hAi))
  rw [← map_mul, ← map_mul, ← map_mul] at h
  exact h

theorem rep_fi24U3T :
    Rep 306936 fi24U3T fi24U3 := by
  have hWi := rep_invT24 rep_fi24WT
  have h := Rep.compT rep_fi24U2T (Rep.compT rep_fi24WT (Rep.compT rep_fi24DT hWi))
  rw [← map_inv, ← map_mul, ← map_mul, ← map_mul] at h
  exact h

theorem rep7_eq :
    rep7 0 = fi24D ∧ rep7 1 = fi24U2 ∧ rep7 2 = fi24U3 ∧ rep7 3 = tR ∧ rep7 4 = fi24D * tR ∧
      rep7 5 = fi24U2 * tR ∧ rep7 6 = fi24U3 * tR :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem fi24_MR_class
    {m : R} (hm : m ∈ MR) (hm2 : m * m = 1) (hm1 : m ≠ 1) :
    ∃ r ∈ ({fi24D, fi24U2, fi24U3} : Set R), ∃ c ∈ MR, c * r * c⁻¹ = m := by
  obtain ⟨u, rfl⟩ := exists_fi23ToR hm
  have hu2 : u ^ 2 = 1 := fi23ToR_injective (by rw [map_pow, sq, hm2, map_one])
  have hu1 : u ≠ 1 := fun h => hm1 (by rw [h, map_one])
  have key : ∀ v : CFSG.Sporadic.Fi23.J, IsConj v u →
      ∃ c ∈ MR, c * fi23ToR v * c⁻¹ = fi23ToR u := fun v h => by
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    exact ⟨fi23ToR c, fi23ToR_mem c, by rw [← hc, map_mul, map_mul, map_inv]⟩
  rcases fi23_involution_class u hu2 hu1 with h | h | h
  · exact ⟨fi24D, Or.inl rfl, key _ h⟩
  · exact ⟨fi24U2, Or.inr (Or.inl rfl), key _ h⟩
  · exact ⟨fi24U3, Or.inr (Or.inr rfl), key _ h⟩

theorem fi24_involution_class
    {t : R} (ht : t * t = 1) (ht1 : t ≠ 1) :
    ∃ r ∈ ({fi24D, fi24U2, fi24U3, tR, fi24D * tR, fi24U2 * tR, fi24U3 * tR} : Set R),
      IsConj r t := by
  obtain ⟨x, hx, htx⟩ := Fi24.exists_commute_D24 CFSG.Fischer.polarFacts ht
  obtain ⟨g, hg⟩ := Fi24.exists_conj_eq_tR hx
  have hct : IsConj (jR g * t * (jR g)⁻¹) t := (isConj_iff.2 ⟨(jR g)⁻¹, by group⟩)
  have hT : jR g * t * (jR g)⁻¹ * tR = tR * (jR g * t * (jR g)⁻¹) := by
    rw [← hg]
    calc jR g * t * (jR g)⁻¹ * (jR g * x * (jR g)⁻¹) = jR g * (t * x) * (jR g)⁻¹ := by group
      _ = jR g * (x * t) * (jR g)⁻¹ := by rw [htx]
      _ = jR g * x * (jR g)⁻¹ * (jR g * t * (jR g)⁻¹) := by group
  set t' := jR g * t * (jR g)⁻¹ with ht'
  have ht'2 : t' * t' = 1 := by
    rw [ht', show jR g * t * (jR g)⁻¹ * (jR g * t * (jR g)⁻¹) = jR g * (t * t) * (jR g)⁻¹ by
      group, ht, mul_one, mul_inv_cancel]
  have ht'1 : t' ≠ 1 := fun h => ht1 (by
    rw [ht'] at h
    calc t = (jR g)⁻¹ * (jR g * t * (jR g)⁻¹) * jR g := by group
      _ = 1 := by rw [h]; group)
  rcases Fi24.mem_MR_or_of_commute (Subgroup.mem_centralizer_singleton_iff.2 hT) with hm | hm
  · obtain ⟨r, hr, c, -, hc⟩ := fi24_MR_class hm ht'2 ht'1
    refine ⟨r, ?_, ((isConj_iff (α := R)).2 ⟨c, hc⟩).trans hct⟩
    rcases hr with rfl | rfl | rfl <;> simp
  · have hmT := Fi24.commute_tR_of_mem_MR hm
    have hm2 : t' * tR * (t' * tR) = 1 := by
      calc t' * tR * (t' * tR) = t' * (tR * t') * tR := by group
        _ = t' * (t' * tR) * tR := by rw [hT]
        _ = t' * t' * (tR * tR) := by group
        _ = 1 := by rw [ht'2, Fi24.tR_mul_tR, mul_one]
    by_cases h1 : t' * tR = 1
    · refine ⟨tR, by simp, ?_⟩
      have : t' = tR := by
        calc t' = t' * tR * tR := by rw [mul_assoc, Fi24.tR_mul_tR, mul_one]
          _ = tR := by rw [h1, one_mul]
      exact this ▸ hct
    · obtain ⟨r, hr, c, hcM, hc⟩ := fi24_MR_class hm hm2 h1
      have hcT := Fi24.commute_tR_of_mem_MR hcM
      have e : c * (r * tR) * c⁻¹ = t' := by
        calc c * (r * tR) * c⁻¹ = c * r * c⁻¹ * (c * tR * c⁻¹) := by group
          _ = t' * tR * tR := by rw [hc, hcT, mul_inv_cancel_right]
          _ = t' := by rw [mul_assoc, Fi24.tR_mul_tR, mul_one]
      refine ⟨r * tR, ?_, ((isConj_iff (α := R)).2 ⟨c, e⟩).trans hct⟩
      rcases hr with rfl | rfl | rfl <;> simp

theorem CommTerm.eval_congr {G : Type*} [Group G] {f g : ℕ → G} :
    ∀ {t : CommTerm}, (∀ i ∈ t.leaves, f i = g i) → t.eval f = t.eval g
  | .leaf i, h => h i (List.mem_singleton_self i)
  | .comm a b, h => by
    simp only [CommTerm.leaves, List.mem_append] at h
    simp only [CommTerm.eval]
    rw [CommTerm.eval_congr fun i hi => h i (Or.inl hi),
      CommTerm.eval_congr fun i hi => h i (Or.inr hi)]

theorem CommTerm.eval_hom {G H : Type*} [Group G] [Group H] (φ : G →* H) (f : ℕ → G) :
    ∀ t : CommTerm, φ (t.eval f) = t.eval (φ ∘ f)
  | .leaf i => rfl
  | .comm a b => by
    simp only [CommTerm.eval, commutatorElement_def, map_mul, map_inv,
      CommTerm.eval_hom φ f a, CommTerm.eval_hom φ f b]

theorem CommTerm.rep_evalT_of_leaves {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)]
    {F : ℕ → Table} {f : ℕ → G} :
    ∀ {t : CommTerm}, (∀ i ∈ t.leaves, Rep n (F i) (f i)) → t.invsOK n F = true →
      Rep n (t.evalT n F) (t.eval f)
  | .leaf i, hF, _ => hF i (List.mem_singleton_self i)
  | .comm a b, hF, h => by
    simp only [CommTerm.leaves, List.mem_append] at hF
    unfold CommTerm.invsOK at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨ha, hb⟩, -⟩ := h
    have ra := CommTerm.rep_evalT_of_leaves (fun i hi => hF i (Or.inl hi)) ha
    have rb := CommTerm.rep_evalT_of_leaves (fun i hi => hF i (Or.inr hi)) hb
    have h' := Rep.compT ra (Rep.compT rb (Rep.compT
      (Rep.inv_of_invOK ra (CommTerm.invOK_of_invsOK ha))
      (Rep.inv_of_invOK rb (CommTerm.invOK_of_invsOK hb))))
    have e : CommTerm.eval f (.comm a b) =
        a.eval f * (b.eval f * ((a.eval f)⁻¹ * (b.eval f)⁻¹)) := by
      simp only [CommTerm.eval, commutatorElement_def, mul_assoc]
    rw [e]
    exact h'

@[expose] def fi24Bray
    (r g : R) (e : ℕ) (odd : Bool) : R :=
  if odd then g * (r * (g⁻¹ * (r * g))) ^ e else (r * (g⁻¹ * (r * g))) ^ e

theorem rep_fi24BrayT
    {T G Gi : Table} {r g : R} (hT : Rep 306936 T r)
    (hG : Rep 306936 G g) (hGi : Rep 306936 Gi g⁻¹) (e : ℕ) (odd : Bool) :
    Rep 306936 (fi24BrayT T G Gi e odd) (fi24Bray r g e odd) := by
  have hBB := Rep.powT (n := 306936) (by norm_num)
    (Rep.compT hT (Rep.compT hGi (Rep.compT hT hG))) e
  cases odd
  · simp only [fi24BrayT, fi24Bray, Bool.false_eq_true, ↓reduceIte]
    exact hBB
  · simp only [fi24BrayT, fi24Bray, ↓reduceIte]
    exact Rep.compT hG hBB

theorem fi24LeafWords_letters {j : ℕ} (hj : j < 6) : ∀ z ∈ fi24LeafWords[j]!, z.natAbs ≤ 14 := by
  interval_cases j <;> decide

@[expose] def fi24Leaf
    (r : R) (c j : ℕ) : R :=
  fi24Bray r (wordG Fi24.genR fi24LeafWords[j]!) ((fi24LeafExp[c]!)[j]!).1
    ((fi24LeafExp[c]!)[j]!).2

theorem fi24_oddCore_hard
    {T : Table} {r : R} (hT : Rep 306936 T r) (hTP : Rep 306936 fi24TP tR) (hr : orderOf r = 2)
    {c n m : ℕ} (hcase : fi24CaseOK fi24L fi24TP T c n = true) (hn : n = 2 ^ m)
    (hleaves : ∀ i ∈ (fi24Term c).leaves, i < 6) (hdepth : 4 ≤ (fi24Term c).depth)
    (hq : Nat.gcd (Nat.card {x : D24 // r * x * r⁻¹ = x}) 2510411418381323442585600 ∣ 8 * 63 ∨
      Nat.gcd (Nat.card {x : D24 // r * x * r⁻¹ = x}) 2510411418381323442585600 ∣ 8 * 87) :
    CFSG.oddCore ↥(Subgroup.centralizer ({r} : Set R)) = ⊥ := by
  unfold fi24CaseOK at hcase
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hcase
  obtain ⟨⟨hleafs, hinvs⟩, hcount⟩ := hcase
  have hrep : ∀ j < 6, Rep 306936 (fi24LeafT fi24L fi24TP T c j) (fi24Leaf r c j) := by
    intro j hj
    have hG := Fi24.rep_wordT_R hTP (fi24LeafWords_letters hj)
    exact rep_fi24BrayT hT hG (Rep.inv_of_invOK hG (hleafs j hj).1) _ _
  have hcomm : ∀ j < 6, fi24Leaf r c j * r = r * fi24Leaf r c j := fun j hj => by
    have e2 : compT 306936 (fi24LeafT fi24L fi24TP T c j) T =
        compT 306936 T (fi24LeafT fi24L fi24TP T c j) := (hleafs j hj).2
    have h2 : Rep 306936 (compT 306936 (fi24LeafT fi24L fi24TP T c j) T) (r * fi24Leaf r c j) := by
      rw [e2]
      exact Rep.compT hT (hrep j hj)
    exact fi24_rep_unique (Rep.compT (hrep j hj) hT) h2
  set C := Subgroup.centralizer ({r} : Set R)
  let c' : ℕ → C := fun j => if hj : j < 6 then
    ⟨fi24Leaf r c j, Subgroup.mem_centralizer_singleton_iff.2 (hcomm j hj)⟩ else 1
  have hc' : ∀ i ∈ (fi24Term c).leaves, (C.subtype ∘ c') i = fi24Leaf r c i := by
    intro i hi
    simp only [Function.comp, c', dite_eq_left (hleaves i hi)]
    rfl
  have hval : (↑((fi24Term c).eval c') : R) = (fi24Term c).eval (fi24Leaf r c) := by
    rw [show (↑((fi24Term c).eval c') : R) = C.subtype ((fi24Term c).eval c') from rfl,
      CommTerm.eval_hom, CommTerm.eval_congr hc']
  have hW := CommTerm.rep_evalT_of_leaves (fun i hi => hrep i (hleaves i hi)) hinvs
  rw [← hval] at hW
  refine fi24_oddCore_of_wit hr hq (k := 1) (fun _ => (fi24Term c).eval c')
    (fun _ => CommTerm.derivedSeries_antitone hdepth (CommTerm.eval_mem c' _)) (m := m) ?_
  rw [card_fixed2_D24 hT hW, ← hn]
  exact hcount

theorem fi24_oddCore_of_hard
    {r : R} (hr : orderOf r = 2) (hh : HardFacts r)
    (hq : Nat.gcd (Nat.card {x : D24 // r * x * r⁻¹ = x}) 2510411418381323442585600 ∣ 8 * 63 ∨
      Nat.gcd (Nat.card {x : D24 // r * x * r⁻¹ = x}) 2510411418381323442585600 ∣ 8 * 87) :
    CFSG.oddCore ↥(Subgroup.centralizer ({r} : Set R)) = ⊥ := by
  obtain ⟨m, W, hW, hfix⟩ := hh
  exact fi24_oddCore_of_wit hr hq (k := 1) (fun _ => W) (fun _ => hW) (m := m) hfix

theorem orderOf_two_of
    {r : R} (h2 : r * r = 1) (h1 : r ≠ 1) : orderOf r = 2 :=
  orderOf_eq_prime (by rw [sq]; exact h2) h1

theorem fi24_inv_of_fi23
    {u : CFSG.Sporadic.Fi23.J} (hu : u ^ 2 = 1 ∧ u ≠ 1) :
    fi23ToR u * fi23ToR u = 1 ∧ fi23ToR u ≠ 1 :=
  ⟨by rw [← map_mul, ← sq, hu.1, map_one], fun h => hu.2 (fi23ToR_injective (by
    rw [h, map_one]))⟩

theorem fi24D_facts :
    fi24D * fi24D = 1 ∧ fi24D ≠ 1 :=
  fi24_inv_of_fi23 ⟨CFSG.Sporadic.Fi23.d_sq', fun h => by
    have := CFSG.Sporadic.Fi23.orderOf_d
    rw [h, orderOf_one] at this
    exact absurd this (by decide)⟩

theorem fi24U2_facts :
    fi24U2 * fi24U2 = 1 ∧ fi24U2 ≠ 1 := fi24_inv_of_fi23 fi23U2_facts

theorem fi24U3_facts :
    fi24U3 * fi24U3 = 1 ∧ fi24U3 ≠ 1 := fi24_inv_of_fi23 fi23U3_facts

theorem fi24_mul_tR_facts
    {m : R} (hm : m ∈ MR) (h2 : m * m = 1) :
    m * tR * (m * tR) = 1 ∧ m * tR ≠ 1 := by
  have hmT := Fi24.commute_tR_of_mem_MR hm
  refine ⟨?_, fun h => Fi24.tR_not_mem_MR ?_⟩
  · calc m * tR * (m * tR) = m * (tR * m) * tR := by group
      _ = m * (m * tR) * tR := by rw [hmT]
      _ = m * m * (tR * tR) := by group
      _ = 1 := by rw [h2, Fi24.tR_mul_tR, mul_one]
  · have : tR = m⁻¹ := by
      calc tR = m⁻¹ * (m * tR) := by group
        _ = m⁻¹ := by rw [h, mul_one]
    rw [this]
    exact Subgroup.inv_mem _ hm

theorem fi24_gcd_eight
    {r : R} {T : Table} (hT : Rep 306936 T r) {n : ℕ} (hn : fi24Fix T = n)
    (h8 : Nat.gcd n 2510411418381323442585600 ∣ 8) :
    Nat.gcd (Nat.card {x : D24 // r * x * r⁻¹ = x}) 2510411418381323442585600 ∣ 8 := by
  rwa [card_fixed1_D24 hT, hn]

theorem fi24_oddCore_reps :
    ∀ r ∈ ({fi24D, fi24U2, fi24U3, tR, fi24D * tR, fi24U2 * tR, fi24U3 * tR} : Set R),
      CFSG.oddCore ↥(Subgroup.centralizer ({r} : Set R)) = ⊥ := by
  obtain ⟨hcnt, hh2, hh5, hh6⟩ := fi24Wit_facts
  have c : ∀ i < 7, Nat.card {x : D24 // rep7 i * x * (rep7 i)⁻¹ = x} =
      [3512, 3512, 504, 31672, 31672, 696, 696].getD i 0 := hcnt
  obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := rep7_eq
  have hM0 := fi23ToR_mem CFSG.Sporadic.Fi23.d
  have hM1 := fi23ToR_mem fi23U2
  have hM2 := fi23ToR_mem fi23U3
  have hT0 := fi24_mul_tR_facts hM0 fi24D_facts.1
  have hT1 := fi24_mul_tR_facts hM1 fi24U2_facts.1
  have hT2 := fi24_mul_tR_facts hM2 fi24U3_facts.1
  have c0 := c 0 (by norm_num)
  have c1 := c 1 (by norm_num)
  have c2 := c 2 (by norm_num)
  have c3 := c 3 (by norm_num)
  have c4 := c 4 (by norm_num)
  have c5 := c 5 (by norm_num)
  have c6 := c 6 (by norm_num)
  rw [e0] at c0
  rw [e1] at c1
  rw [e2] at c2 hh2
  rw [e3] at c3
  rw [e4] at c4
  rw [e5] at c5 hh5
  rw [e6] at c6 hh6
  intro r hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fi24_oddCore_of_count (orderOf_two_of fi24D_facts.1 fi24D_facts.2)
      (by rw [c0]; norm_num)
  · exact fi24_oddCore_of_count (orderOf_two_of fi24U2_facts.1 fi24U2_facts.2)
      (by rw [c1]; norm_num)
  · exact fi24_oddCore_of_hard (orderOf_two_of fi24U3_facts.1 fi24U3_facts.2) hh2
      (Or.inl (by rw [c2]; norm_num))
  · exact fi24_oddCore_of_count Fi24.orderOf_tR (by rw [c3]; norm_num)
  · exact fi24_oddCore_of_count (orderOf_two_of hT0.1 hT0.2) (by rw [c4]; norm_num)
  · exact fi24_oddCore_of_hard (orderOf_two_of hT1.1 hT1.2) hh5 (Or.inr (by rw [c5]; norm_num))
  · exact fi24_oddCore_of_hard (orderOf_two_of hT2.1 hT2.2) hh6 (Or.inr (by rw [c6]; norm_num))

theorem CTUC_Fi24_all_extension_involution_centralizers_odd_core_trivial :
    ∀ t : R, orderOf t = 2 →
      CFSG.oddCore ↥(Subgroup.centralizer ({t} : Set R)) = ⊥ ∧
        CFSG.oddCore ↥(JR ⊓ Subgroup.centralizer ({t} : Set R)) = ⊥ := by
  intro t ht
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht; exact absurd ht (by decide)
  obtain ⟨r, hr, hrt⟩ := fi24_involution_class ht2 ht1
  have hC := oddCore_centralizer_eq_bot_of_isConj hrt (fi24_oddCore_reps r hr)
  refine ⟨hC, oddCore_eq_bot_of_normal_le inf_le_right ?_ hC⟩
  refine ⟨fun n hn c => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨hnJ, hnc⟩ := Subgroup.mem_inf.1 hn
  exact Subgroup.mem_inf.2 ⟨Fi24.normal_JR.conj_mem _ hnJ _,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ c.2 hnc) (Subgroup.inv_mem _ c.2)⟩

end CFSG.Sporadic.FischerOddCore
