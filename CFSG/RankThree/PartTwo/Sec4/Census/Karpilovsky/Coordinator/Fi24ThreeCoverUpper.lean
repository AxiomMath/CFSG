module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24ThreeCoverMain
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24ThreeCoverSection

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

open CFSG.CosetTable CFSG.Sporadic.Presentation.Fi24Prime CFSG.Sporadic.Recognition.PresentedWords
  CFSG.Sporadic.Recognition.Fi24PrimeMultiplier CFSG.Certificates.CosetEnumeration
  CFSG.RankThree.PerfectCover Subgroup CFSG.AGLEmbedding
open scoped commutatorElement

theorem shape_of_map_eq {w : List (Fin m0 × Bool)}
    (h : w.map (fun l => (l.1.val, l.2)) = [(8, true), (8, true)]) :
    ∃ l1 l2 : Fin m0 × Bool, w = [l1, l2] ∧ l1.1.val = 8 ∧ l1.2 = true ∧ l2.1.val = 8 ∧
      l2.2 = true := by
  rcases w with _ | ⟨l1, _ | ⟨l2, _ | ⟨l3, t⟩⟩⟩
  · simp at h
  · simp at h
  · simp only [List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq, and_true] at h
    exact ⟨l1, l2, rfl, h.1.1, h.1.2, h.2.1, h.2.2⟩
  · simp at h

theorem exists_lifts3 (hm0 : m0 = 11)
    (hsq : (X0.getD sqIdx []).map (fun l => (l.1.val, l.2)) = [(8, true), (8, true)])
    {E : Type} [Group E] (π : E →* PG m0 X0) (hπ : Function.Surjective π)
    (hker : π.ker ≤ center E) (hp : IsPGroup 3 π.ker) (s : PG10 →* E)
    (hs : ∀ q, π (s q) = restrictHom X0 (subsetOf m0 S0) q) :
    ∃ xh : Fin m0 → E, (∀ i, π (xh i) = PresentedGroup.of i) ∧
      (∀ j : Fin (subsetOf m0 S0).length,
        xh ((subsetOf m0 S0).get j) = s (PresentedGroup.of j)) ∧
      wprod xh (X0.getD sqIdx []) = 1 := by
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
  have hnot8 : (⟨8, h8⟩ : Fin m0) ∉ subsetOf m0 S0 := by
    intro h
    exact ne_eight_of_mem h rfl
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
  have hx8 : xh0 ⟨8, h8⟩ = g8 := by simp [xh0, hnot8]
  obtain ⟨l1, l2, hw, hl1, hb1, hl2, hb2⟩ := shape_of_map_eq hsq
  have hl1' : l1.1 = ⟨8, h8⟩ := Fin.ext hl1
  have hl2' : l2.1 = ⟨8, h8⟩ := Fin.ext hl2
  have hrel := wprod_getD_relator X0 sqIdx
  rw [hw] at hrel
  simp only [wprod_cons, wprod_nil, hb1, hb2, hl1', hl2', ite_true, mul_one] at hrel
  have hc : g8 * g8 ∈ π.ker := by rw [MonoidHom.mem_ker, map_mul, hg8]; exact hrel
  obtain ⟨a, ha⟩ := exists_sq_eq_of_isPGroup_three hp (⟨g8 * g8, hc⟩⁻¹ : π.ker)
  have ha' : (a : E) * (a : E) = (g8 * g8)⁻¹ := congrArg Subtype.val ha
  have hac : g8 * (a : E) = (a : E) * g8 := (mem_center_iff.1 (hker a.2)) g8
  refine ⟨fun i => if i = ⟨8, h8⟩ then xh0 i * a else xh0 i, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i = ⟨8, h8⟩
    · simp only [hi, ↓reduceIte, map_mul, MonoidHom.mem_ker.1 a.2, mul_one]
      exact hπ0 _
    · simp only [hi, ↓reduceIte]
      exact hπ0 i
  · intro j
    have hne : (subsetOf m0 S0).get j ≠ ⟨8, h8⟩ := by
      intro h
      exact hnot8 (h ▸ List.get_mem (subsetOf m0 S0) j)
    simp only [hne, ↓reduceIte]
    exact hxh0_get j
  · rw [hw]
    simp only [wprod_cons, wprod_nil, hb1, hb2, hl1', hl2', mul_one, ↓reduceIte, hx8]
    calc g8 * a * (g8 * a) = g8 * (a * g8) * a := by group
      _ = g8 * (g8 * a) * a := by rw [hac]
      _ = (g8 * g8) * (a * a) := by group
      _ = 1 := by rw [ha']; simp

theorem false_of_card_ker_nine (hm0 : m0 = 11)
    (hindex : (genSub {r : FreeGroup (Fin nG) | r ∈ wsQ.map FreeGroup.mk} (subsetOf nG S0)).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin nG) | r ∈ wsQ.map FreeGroup.mk} (subsetOf nG S0)).index ≤ 920808)
    (hsq : (X0.getD sqIdx []).map (fun l => (l.1.val, l.2)) = [(8, true), (8, true)])
    (hkt : KernelTrivialAt PG10 3) {E : Type} [Group E] [Finite E] [hE : Group.IsPerfect E]
    (π : E →* PG m0 X0) (hπ : Function.Surjective π) (hker : π.ker ≤ center E)
    (hp : IsPGroup 3 π.ker) (h9 : Nat.card π.ker = 9) : False := by
  have hfin10 := card_PG10_le.1
  obtain ⟨s, hs⟩ := exists_section_of_kernelTrivial π hπ hker hp
    (restrictHom X0 (subsetOf m0 S0)) isPerfect_PG10 hkt
  obtain ⟨xh, hxh1, hxh2, hxh3⟩ := exists_lifts3 hm0 hsq π hπ hker hp s hs
  let ζE : ℕ → E := fun k => wprod xh (X0.getD (repIdx3.getD k 0) [])
  have hζ1 : ∀ k, π (ζE k) = 1 := by
    intro k
    show π (wprod xh _) = 1
    rw [map_wprod π xh, show (fun i => π (xh i)) = fun i => (PresentedGroup.of i : PG m0 X0)
      from funext hxh1]
    exact wprod_getD_relator X0 _
  have hζc : ∀ k, ζE k ∈ center E := fun k => hker (MonoidHom.mem_ker.2 (hζ1 k))
  have h9' : ∀ k, ζE k ^ 9 = 1 := by
    intro k
    have h := pow_card_eq_one' (G := π.ker) (x := ⟨ζE k, MonoidHom.mem_ker.2 (hζ1 k)⟩)
    rw [h9] at h
    exact congrArg Subtype.val h
  have hrel := wprod_genFam_wsQ hm0 xh ζE (wprod_xh_nonaj hm0 s xh hxh2) hxh3
    (fun k _ => rfl) h9' (fun k g => (mem_center_iff.1 (hζc k)) g)
  let ψ : Q3 →* E := pgHom (genFam xh ζE) hrel
  have hψ : ∀ i : Fin m0, π (ψ (PresentedGroup.of (gQ i))) = PresentedGroup.of i := by
    intro i
    rw [pgHom_of, gQ, genFam_liftL hm0, hxh1]
  have hsurj0 : Function.Surjective (π.comp ψ) := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← PresentedGroup.closure_range_of,
      Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨PresentedGroup.of (gQ i), hψ i⟩
  have hsurj : Function.Surjective ψ := surjective_of_perfect_central π hker ψ hsurj0 hE
  obtain ⟨hfinQ, hcardQ⟩ := card_Q3_le hm0 hindex
  obtain ⟨-, hG⟩ := perfect_and_card_G
  have h1 : Nat.card E ≤ Nat.card Q3 := Nat.card_le_card_of_surjective ψ hsurj
  have h2 := CFSG.GH74.Generic.card_eq_card_mul_card_ker π hπ
  rw [h9] at h2
  omega

theorem card_ker_dvd_three_PG (hm0 : m0 = 11)
    (hindex : (genSub {r : FreeGroup (Fin nG) | r ∈ wsQ.map FreeGroup.mk} (subsetOf nG S0)).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin nG) | r ∈ wsQ.map FreeGroup.mk} (subsetOf nG S0)).index ≤ 920808)
    (hsq : (X0.getD sqIdx []).map (fun l => (l.1.val, l.2)) = [(8, true), (8, true)])
    (hkt : KernelTrivialAt PG10 3) {E : Type} [Group E] [Finite E] [Group.IsPerfect E]
    (π : E →* PG m0 X0) (hπ : Function.Surjective π) (hker : π.ker ≤ center E)
    (hp : IsPGroup 3 π.ker) : Nat.card π.ker ∣ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := hp.exists_card_eq
  by_cases h : a ≤ 1
  · rw [ha]
    exact (pow_dvd_pow 3 h).trans (by simp)
  · exfalso
    have ha2 : 2 ≤ a := by omega
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := π.ker) 3 (n := a - 2)
      (by rw [ha]; exact pow_dvd_pow 3 (by omega))
    let B : Subgroup E := K.map π.ker.subtype
    have hBle : B ≤ π.ker := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have hBc : B ≤ center E := hBle.trans hker
    have hBn : B.Normal := ⟨fun n hn g => by
      have := mem_center_iff.1 (hBc hn) g
      rw [this, mul_inv_cancel_right]
      exact hn⟩
    have hBcard : Nat.card B = 3 ^ (a - 2) := by
      rw [Subgroup.card_map_of_injective π.ker.subtype_injective, hK]
    let π' : E ⧸ B →* PG m0 X0 := QuotientGroup.lift B π (fun b hb => MonoidHom.mem_ker.1 (hBle hb))
    have hπ'mk : ∀ e : E, π' (QuotientGroup.mk e) = π e := fun e => QuotientGroup.lift_mk B _ e
    have hπ' : Function.Surjective π' := by
      intro g
      obtain ⟨e, he⟩ := hπ g
      exact ⟨QuotientGroup.mk e, by rw [hπ'mk, he]⟩
    have : Group.IsPerfect (E ⧸ B) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' B) (QuotientGroup.mk'_surjective B)
    have hker_mk : ∀ x : E ⧸ B, x ∈ π'.ker → ∃ e ∈ π.ker, x = QuotientGroup.mk e := by
      intro x hx
      obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective x
      refine ⟨e, ?_, rfl⟩
      rw [MonoidHom.mem_ker] at hx ⊢
      rwa [hπ'mk] at hx
    have hker' : π'.ker ≤ center (E ⧸ B) := by
      intro x hx
      obtain ⟨e, he, rfl⟩ := hker_mk x hx
      rw [mem_center_iff]
      intro y
      obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      exact congrArg QuotientGroup.mk (mem_center_iff.1 (hker he) y')
    have hp' : IsPGroup 3 π'.ker := by
      intro x
      obtain ⟨e, he, hx⟩ := hker_mk x.1 x.2
      obtain ⟨n, hn⟩ := hp ⟨e, he⟩
      refine ⟨n, Subtype.ext ?_⟩
      show (x.1) ^ 3 ^ n = 1
      have he3 : e ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
      rw [hx, ← QuotientGroup.mk_pow, he3]
      rfl
    have hGfin : Finite (PG m0 X0) := Finite.of_surjective π hπ
    have hGpos : 0 < Nat.card (PG m0 X0) := Nat.card_pos
    have h1 := CFSG.GH74.Generic.card_eq_card_mul_card_ker π hπ
    have h2 := CFSG.GH74.Generic.card_eq_card_mul_card_ker π' hπ'
    have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup B
    rw [ha] at h1
    have hpow : 3 ^ a = 3 ^ (a - 2) * 9 := by
      rw [show a = (a - 2) + 2 by omega, pow_add]
      norm_num
    have h4 : Nat.card (PG m0 X0) * 3 ^ a = Nat.card (PG m0 X0) * Nat.card π'.ker * 3 ^ (a - 2) := by
      rw [← h1, h3, h2, hBcard]
    rw [hpow] at h4
    have h5 : Nat.card π'.ker = 9 := by
      have hp2 : 0 < 3 ^ (a - 2) := by positivity
      have h6 : Nat.card (PG m0 X0) * 9 * 3 ^ (a - 2) =
          Nat.card (PG m0 X0) * Nat.card π'.ker * 3 ^ (a - 2) := by
        rw [← h4]; ring
      have h7 := Nat.eq_of_mul_eq_mul_right hp2 h6
      exact (Nat.eq_of_mul_eq_mul_left hGpos h7).symm
    exact false_of_card_ker_nine hm0 hindex hsq hkt π' hπ' hker' hp' h5

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three
