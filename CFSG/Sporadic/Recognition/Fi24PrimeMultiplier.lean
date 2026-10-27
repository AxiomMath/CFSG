module

public import CFSG.Sporadic.Recognition.Fi24PrimeMultiplierInputs
public import CFSG.Sporadic.Recognition.PresentedWords
public import CFSG.Sporadic.Recognition.YCoverSection

public section

namespace CFSG.Sporadic.Recognition.Fi24PrimeMultiplier

open CFSG.CosetTable CFSG.Sporadic.Presentation.Fi24Prime CFSG.Sporadic.Recognition.PresentedWords
  CFSG.Sporadic.Recognition.YCover CFSG.Monster.Schur

theorem mem_subsetOf_iff {m : ℕ} {S : List ℕ} {i : Fin m} : i ∈ subsetOf m S ↔ i.val ∈ S := by
  simp [subsetOf, List.mem_filter, List.mem_finRange]

theorem nodup_subsetOf (m : ℕ) (S : List ℕ) : (subsetOf m S).Nodup :=
  (List.nodup_finRange m).filter _

theorem renumber_isSome {m : ℕ} (S : List (Fin m)) :
    ∀ w : List (Fin m × Bool), (∀ l ∈ w, l.1 ∈ S) → ∃ w', renumber S w = some w'
  | [], _ => ⟨[], rfl⟩
  | l :: w, h => by
    obtain ⟨w', hw'⟩ := renumber_isSome S w fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    have hS : l.1 ∈ S := h l List.mem_cons_self
    obtain ⟨i, hi⟩ : ∃ i, S.finIdxOf? l.1 = some i := by
      cases hc : S.finIdxOf? l.1 with
      | none => exact absurd hS (List.finIdxOf?_eq_none_iff.1 hc)
      | some i => exact ⟨i, rfl⟩
    exact ⟨(i, l.2) :: w', by simp [renumber, hi, hw']⟩

theorem wprod_update {G : Type*} [Group G] {n : ℕ} (y : Fin n → G) (a : Fin n) (z : G)
    (hzc : ∀ g : G, g * z = z * g) (hz2 : z * z = 1) (w : List (Fin n × Bool)) :
    wprod (fun i => if i = a then y i * z else y i) w =
      wprod y w * z ^ (w.filter fun l => decide (l.1 = a)).length := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hletter : ∀ (b : Bool) (g : G), (if b then g * z else (g * z)⁻¹) =
      (if b then g else g⁻¹) * z := by
    intro b g
    cases b
    · simp [mul_inv_rev, hzi, hzc]
    · simp
  induction w with
  | nil => simp
  | cons l w ih =>
    rw [wprod_cons, wprod_cons, ih]
    by_cases h : l.1 = a
    · simp only [h, ↓reduceIte, hletter, List.filter_cons, decide_true, List.length_cons, pow_succ']
      generalize (if l.2 = true then y a else (y a)⁻¹) = L
      generalize wprod y w = W
      generalize z ^ (List.filter (fun l => decide (l.1 = a)) w).length = Zc
      calc L * z * (W * Zc) = L * (z * W) * Zc := by simp only [mul_assoc]
        _ = L * (W * z) * Zc := by rw [← hzc W]
        _ = L * W * (z * Zc) := by simp only [mul_assoc]
    · simp [h, mul_assoc]

theorem wprod_getD_relator {n : ℕ} (ws : List (List (Fin n × Bool))) (k : ℕ) :
    wprod (fun i => (PresentedGroup.of i : PG n ws)) (ws.getD k []) = 1 := by
  by_cases hk : k < ws.length
  · rw [List.getD_eq_getElem _ _ hk]
    exact wprod_of_relator (List.getElem_mem hk)
  · rw [List.getD_eq_default _ _ (by omega)]
    rfl

theorem wprod_xh_nonaj (hm0 : m0 = 11) {E : Type*} [Group E] (s : PG10 →* E) (xh : Fin m0 → E)
    (hxh : ∀ j : Fin (subsetOf m0 S0).length,
      xh ((subsetOf m0 S0).get j) = s (PresentedGroup.of j))
    (v : List (Fin m0 × Bool)) (hvX : v ∈ X0) (hv8 : (!v.any fun l => l.1.val == 8) = true) :
    wprod xh v = 1 := by
  have hS : ∀ l ∈ v, l.1 ∈ subsetOf m0 S0 := by
    intro l hl
    rw [mem_subsetOf_iff]
    have h8 : l.1.val ≠ 8 := by
      intro h
      have : (v.any fun l => l.1.val == 8) = true :=
        List.any_eq_true.2 ⟨l, hl, by simp [h]⟩
      simp [this] at hv8
    have hlt : l.1.val < 11 := hm0 ▸ l.1.isLt
    simp only [S0, List.mem_cons, List.not_mem_nil, or_false]
    omega
  obtain ⟨v', hren⟩ := renumber_isSome (subsetOf m0 S0) v hS
  have hv' : v' ∈ X1 := List.mem_filterMap.2 ⟨v, hvX, hren⟩
  have hmap := map_renumber (subsetOf m0 S0) v v' hren
  calc wprod xh v = wprod xh (v'.map fun l => ((subsetOf m0 S0).get l.1, l.2)) := by rw [hmap]
    _ = wprod (fun j => xh ((subsetOf m0 S0).get j)) v' := wprod_comp_letters _ xh v'
    _ = wprod (fun j => s (PresentedGroup.of j)) v' := by simp only [hxh]
    _ = s (wprod (fun j => (PresentedGroup.of j : PG10)) v') := (map_wprod s _ v').symm
    _ = 1 := by rw [wprod_of_relator hv', map_one]

theorem exists_lifts (hm0 : m0 = 11)
    (hpar : ((X0.getD r0Idx []).filter fun l => l.1.val == 8).length % 2 = 1)
    {E : Type} [Group E] (π : E →* PG m0 X0) (hπ : Function.Surjective π) {z : E}
    (hz : CentralKernel π z) (s : PG10 →* E)
    (hs : ∀ q, π (s q) = restrictHom X0 (subsetOf m0 S0) q) :
    ∃ xh : Fin m0 → E, (∀ i, π (xh i) = PresentedGroup.of i) ∧
      (∀ j : Fin (subsetOf m0 S0).length,
        xh ((subsetOf m0 S0).get j) = s (PresentedGroup.of j)) ∧
      wprod xh (X0.getD r0Idx []) = 1 := by
  have h8 : 8 < m0 := by omega
  obtain ⟨g8, hg8⟩ := hπ (PresentedGroup.of (⟨8, h8⟩ : Fin m0))
  let xh0 : Fin m0 → E := fun i =>
    if h : i ∈ subsetOf m0 S0 then
      s (PresentedGroup.of ⟨(subsetOf m0 S0).idxOf i, List.idxOf_lt_length_iff.2 h⟩)
    else g8
  have hxh0_get : ∀ j : Fin (subsetOf m0 S0).length,
      xh0 ((subsetOf m0 S0).get j) = s (PresentedGroup.of j) := by
    intro j
    have hmem : (subsetOf m0 S0).get j ∈ subsetOf m0 S0 := List.get_mem _ _
    simp only [xh0, hmem, ↓reduceDIte]
    congr 2
    exact Fin.ext (by simp [List.get_eq_getElem, (nodup_subsetOf m0 S0).idxOf_getElem])
  have hπ0 : ∀ i, π (xh0 i) = PresentedGroup.of i := by
    intro i
    by_cases h : i ∈ subsetOf m0 S0
    · simp only [xh0, h, ↓reduceDIte]
      rw [hs, restrictHom_of]
      congr 1
      simp [List.get_eq_getElem]
    · simp only [xh0, h, ↓reduceDIte]
      have hi : i = ⟨8, h8⟩ := by
        rw [mem_subsetOf_iff] at h
        apply Fin.ext
        have := i.isLt
        simp only [S0, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
        show i.val = 8
        omega
      rw [hi]
      exact hg8
  have hv : π (wprod xh0 (X0.getD r0Idx [])) = 1 := by
    rw [map_wprod π xh0, show (fun i => π (xh0 i)) = fun i => (PresentedGroup.of i : PG m0 X0)
      from funext hπ0]
    exact wprod_getD_relator X0 r0Idx
  rcases hz.ker_sub _ hv with hv1 | hvz
  · exact ⟨xh0, hπ0, hxh0_get, hv1⟩
  · refine ⟨fun i => if i = ⟨8, h8⟩ then xh0 i * z else xh0 i, ?_, ?_, ?_⟩
    · intro i
      by_cases hi : i = ⟨8, h8⟩
      · simp only [hi, ↓reduceIte, map_mul, hz.map_eq_one, mul_one]
        exact hπ0 _
      · simp only [hi, ↓reduceIte]
        exact hπ0 i
    · intro j
      have hne : (subsetOf m0 S0).get j ≠ ⟨8, h8⟩ := by
        intro h
        have hmem := mem_subsetOf_iff.1 (List.get_mem (subsetOf m0 S0) j)
        rw [h] at hmem
        simp [S0] at hmem
      simp only [hne, ↓reduceIte]
      exact hxh0_get j
    · rw [wprod_update xh0 ⟨8, h8⟩ z hz.central hz.mul_self, hvz]
      have hfilt : (X0.getD r0Idx []).filter (fun l => decide (l.1 = ⟨8, h8⟩)) =
          (X0.getD r0Idx []).filter (fun l => l.1.val == 8) := by
        apply List.filter_congr
        intro l _
        by_cases h : l.1.val = 8
        · simp [Fin.ext_iff, h]
        · simp [Fin.ext_iff, h]
      have hc : ((X0.getD r0Idx []).filter fun l => decide (l.1 = ⟨8, h8⟩)).length % 2 = 1 := by
        rw [hfilt]; exact hpar
      rw [CFSG.Monster.GMS.R433Cover.IsZ.pow_odd hz.central hz.mul_self (Or.inr rfl) hc]
      exact hz.mul_self

@[expose] def genFam {E : Type*} (xh : Fin m0 → E) (ζE : ℕ → E) (i : Fin nG) : E :=
  if h : i.val < m0 then xh ⟨i.val, h⟩ else ζE (i.val - m0)

theorem genFam_liftL (hm0 : m0 = 11) {E : Type*} (xh : Fin m0 → E) (ζE : ℕ → E)
    (l : Fin m0 × Bool) : genFam xh ζE (liftL l).1 = xh l.1 := by
  have hl : l.1.val % nG = l.1.val := Nat.mod_eq_of_lt (by have := l.1.isLt; unfold nG; omega)
  simp [genFam, liftL, hl]

theorem wprod_genFam_liftL (hm0 : m0 = 11) {E : Type*} [Group E] (xh : Fin m0 → E) (ζE : ℕ → E)
    (w : List (Fin m0 × Bool)) : wprod (genFam xh ζE) (w.map liftL) = wprod xh w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [List.map_cons, wprod_cons, wprod_cons, ih]
    rw [genFam_liftL hm0 xh ζE l]
    rfl

theorem genFam_zeta (hm0 : m0 = 11) {E : Type*} (xh : Fin m0 → E) (ζE : ℕ → E) {k : ℕ}
    (hk : k < 11) : genFam xh ζE (zeta k) = ζE k := by
  have h1 : (zeta k).val = 11 + k := by
    simp only [zeta, Fin.val_ofNat]
    exact Nat.mod_eq_of_lt (by unfold nG; omega)
  simp only [genFam, h1, hm0]
  simp

theorem wprod_genFam_wsN (hm0 : m0 = 11) {E : Type*} [Group E] (xh : Fin m0 → E) (ζE : ℕ → E)
    (hA : ∀ v ∈ X0, (!v.any fun l => l.1.val == 8) = true → wprod xh v = 1)
    (hB : wprod xh (X0.getD r0Idx []) = 1)
    (hdef : ∀ k < 11, ζE k = wprod xh (X0.getD (repIdx.getD k 0) []))
    (hsq : ∀ k, ζE k * ζE k = 1) (hcomm : ∀ k (g : E), g * ζE k = ζE k * g) :
    ∀ w ∈ wsN, wprod (genFam xh ζE) w = 1 := by
  intro w hw
  simp only [wsN, List.mem_append, List.mem_map, List.mem_filter, List.mem_singleton] at hw
  rcases hw with (⟨v, ⟨hvX, hv8⟩, rfl⟩ | rfl) | hw
  · rw [wprod_genFam_liftL hm0]
    exact hA v hvX hv8
  · rw [wprod_genFam_liftL hm0]
    exact hB
  · simp only [centralWords, List.mem_flatMap, List.mem_append, List.mem_cons, List.mem_map,
      List.mem_range, List.not_mem_nil, or_false] at hw
    obtain ⟨k, hk, hw⟩ := hw
    rcases hw with (rfl | rfl) | ⟨i, hi, rfl⟩
    · rw [wprod_append, wprod_genFam_liftL hm0, wprod_cons, wprod_nil, genFam_zeta hm0 xh ζE hk,
        ← hdef k hk]
      simp
    · simp [wprod_cons, genFam_zeta hm0 xh ζE hk, hsq k]
    · simp only [wprod_cons, wprod_nil, genFam_zeta hm0 xh ζE hk]
      have h := hcomm k (genFam xh ζE (Fin.ofNat nG i))
      have key : ζE k * genFam xh ζE (Fin.ofNat nG i) * (ζE k)⁻¹ *
          (genFam xh ζE (Fin.ofNat nG i))⁻¹ = 1 := by
        calc ζE k * genFam xh ζE (Fin.ofNat nG i) * (ζE k)⁻¹ * (genFam xh ζE (Fin.ofNat nG i))⁻¹
            = (ζE k * genFam xh ζE (Fin.ofNat nG i)) *
              (genFam xh ζE (Fin.ofNat nG i) * ζE k)⁻¹ := by group
          _ = 1 := by rw [h]; simp
      simp only [Bool.false_eq_true, ↓reduceIte, mul_one]
      refine Eq.trans ?_ key
      group

theorem noPerfectDoubleCover_PG_of_enumeration (hm0 : m0 = 11)
    (hpar : ((X0.getD r0Idx []).filter fun l => l.1.val == 8).length % 2 = 1)
    (hfin : Finite PG10) (hcard : Nat.card PG10 ≤ 4089470473293004800)
    (hperf : Group.IsPerfect PG10) (hnd : NoPerfectDoubleCover PG10)
    (hidx : (genSub {r : FreeGroup (Fin nG) | r ∈ wsN.map FreeGroup.mk}
        (subsetOf nG S0)).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin nG) | r ∈ wsN.map FreeGroup.mk} (subsetOf nG S0)).index ≤
        306936)
    (hG : 1255205709190661721292800 ≤ Nat.card (PG m0 X0)) :
    NoPerfectDoubleCover (PG m0 X0) := by
  intro E _ π hπ hperfE hk
  obtain ⟨z, hz⟩ := exists_centralKernel_of_card_ker hk
  obtain ⟨s, hs⟩ := exists_section π hπ hk (restrictHom X0 (subsetOf m0 S0)) hperf hnd
  obtain ⟨xh, hxh1, hxh2, hxh3⟩ := exists_lifts hm0 hpar π hπ hz s hs
  let ζE : ℕ → E := fun k => wprod xh (X0.getD (repIdx.getD k 0) [])
  have hζ1 : ∀ k, π (ζE k) = 1 := by
    intro k
    show π (wprod xh _) = 1
    rw [map_wprod π xh, show (fun i => π (xh i)) = fun i => (PresentedGroup.of i : PG m0 X0)
      from funext hxh1]
    exact wprod_getD_relator X0 _
  have hζZ : ∀ k, CFSG.Monster.GMS.R433Cover.IsZ z (ζE k) := fun k => hz.ker_sub _ (hζ1 k)
  have hrel := wprod_genFam_wsN hm0 xh ζE (wprod_xh_nonaj hm0 s xh hxh2) hxh3
    (fun k _ => rfl) (fun k => CFSG.Monster.GMS.R433Cover.IsZ.mul_self hz.central hz.mul_self
      (hζZ k)) (fun k g => CFSG.Monster.GMS.R433Cover.IsZ.comm hz.central hz.mul_self (hζZ k) g)
  let ψ : PG nG wsN →* E := pgHom (genFam xh ζE) hrel
  have hψ : ∀ i : Fin m0, π (ψ (PresentedGroup.of ⟨i.val, by unfold nG; omega⟩)) =
      PresentedGroup.of i := by
    intro i
    rw [pgHom_of, genFam]
    simp [hxh1]
  have hsurj : Function.Surjective ψ := by
    refine surj_of_perfect hz (θ := ψ) (ρ := π.comp ψ) rfl ?_ (Group.isPerfect_def.1 hperfE)
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← PresentedGroup.closure_range_of,
      Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨PresentedGroup.of ⟨i.val, by unfold nG; omega⟩, hψ i⟩
  have hle : (genSub {r : FreeGroup (Fin nG) | r ∈ wsN.map FreeGroup.mk}
      (subsetOf nG S0)).map ψ ≤ s.range := by
    rw [genSub, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    have hi' : i.val ∈ S0 := mem_subsetOf_iff.1 hi
    have hlt : i.val < m0 := by
      simp only [S0, List.mem_cons, List.not_mem_nil, or_false] at hi'
      omega
    have hmem : (⟨i.val, hlt⟩ : Fin m0) ∈ subsetOf m0 S0 := mem_subsetOf_iff.2 hi'
    obtain ⟨j, hj⟩ := List.mem_iff_get.1 hmem
    show ψ (PresentedGroup.of i) ∈ s.range
    rw [pgHom_of]
    have hg : genFam xh ζE i = xh ⟨i.val, hlt⟩ := by simp [genFam, hlt]
    rw [hg, ← hj, hxh2]
    exact ⟨_, rfl⟩
  have := hfin
  have hfin' : Finite s.range := Finite.of_surjective _ s.rangeRestrict_surjective
  have hrange : Nat.card s.range ≤ Nat.card PG10 :=
    Nat.card_le_card_of_surjective _ s.rangeRestrict_surjective
  have hidx2 : ((genSub {r : FreeGroup (Fin nG) | r ∈ wsN.map FreeGroup.mk}
      (subsetOf nG S0)).map ψ).index ≤ 306936 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hidx.1.index_ne_zero)
      (Subgroup.index_map_dvd (genSub {r : FreeGroup (Fin nG) | r ∈ wsN.map FreeGroup.mk}
        (subsetOf nG S0)) hsurj)).trans hidx.2
  have hcardE : Nat.card E ≤ 306936 * 4089470473293004800 := by
    rw [← Subgroup.index_mul_card ((genSub {r : FreeGroup (Fin nG) | r ∈ wsN.map FreeGroup.mk}
      (subsetOf nG S0)).map ψ)]
    exact Nat.mul_le_mul hidx2 ((Subgroup.card_le_of_le hle).trans (hrange.trans hcard))
  have hE2 : Nat.card E = Nat.card (PG m0 X0) * 2 := by
    rw [card_eq_mul_card_ker π hπ, hk]
  omega

end CFSG.Sporadic.Recognition.Fi24PrimeMultiplier
