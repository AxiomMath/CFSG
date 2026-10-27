module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3OmHyp
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3OmBlock

public section

namespace CFSG.StandardType

namespace CoordOm

open Polynomial Module Multiplicative CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.Assembly
open CFSG.RankThree.Classical2 (orthDerived)

section Pair

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} [Fact p.Prime]
  {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} {F : SevOm.Frame Q p A r} {E J : Subgroup (V ≃ₗ[K] V)}

theorem GGOmA3Hyp.exists_single_mem_centralizer (H : GGOmA3Hyp F E J) :
    ∃ a : Fin r, F.ι (ofAdd (Pi.single a 1)) ∈ Subgroup.centralizer (J : Set (V ≃ₗ[K] V)) := by
  classical
  have hr : 4 ≤ r := H.four_le
  haveI : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp (by omega)
  obtain ⟨k⟩ := (inferInstance : Nonempty (Fin r))
  obtain ⟨t, htE, ht0, htk⟩ := exists_ne_zero_apply_eq_zero F H.le_A H.card_E k
  by_contra hno
  push Not at hno
  obtain ⟨h, hh, _hJB, hU⟩ :=
    exists_factor_of_mem H.nondeg H.tsub H.ne_two F H.le_orthDerived H.max H.le_A H.isComponent htE
  have hkU : F.U k ≤ orbitSpace (F.ι (ofAdd t)).toLinearMap h := hU k (hno k)
  have hX : h = X - 1 :=
    eq_X_sub_one_of_apply_eq_zero H.nondeg H.ne_two F H.le_orthDerived hh htk hkU
  exact ht0 (funext fun m =>
    apply_eq_zero_of_le_orbitSpace_X_sub_one F (by rw [← hX]; exact hU m (hno m)))

theorem GGOmA3Hyp.apply_eq_zero_of_pair (H : GGOmA3Hyp F E J) {a b : Fin r} (hab : a ≠ b)
    (ha : F.ι (ofAdd (Pi.single a 1)) ∈ Subgroup.centralizer (J : Set (V ≃ₗ[K] V)))
    (hb : F.ι (ofAdd (Pi.single b 1)) ∈ Subgroup.centralizer (J : Set (V ≃ₗ[K] V)))
    {s : Fin r → ZMod p} (hs : F.ι (ofAdd s) ∈ E) {m : Fin r} (hma : m ≠ a) (hmb : m ≠ b) :
    s m = 0 := by
  classical
  by_contra hsm
  have hp : p.Prime := Fact.out
  haveI : Finite (V ≃ₗ[K] V) := by
    have : Finite V := Module.finite_of_finite K
    exact Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
      fun _ _ he => LinearEquiv.ext (congrFun he)
  haveI : Finite E := Finite.of_injective Subtype.val fun _ _ h => Subtype.ext h
  have h1 : F.ι (ofAdd (Pi.single a 1)) ∈ E :=
    H.mem_E_of_mem_centralizer (F.mem _) ha
  have h2 : F.ι (ofAdd (Pi.single b 1)) ∈ E :=
    H.mem_E_of_mem_centralizer (F.mem _) hb
  have h3 : p ^ 3 ≤ Nat.card E :=
    card_ge_of_three F h1 h2 hs (k₁ := a) (k₂ := b) (k₃ := m)
      (by rw [Pi.single_eq_same]; exact one_ne_zero)
      (by rw [Pi.single_eq_same]; exact one_ne_zero)
      hsm
      (Pi.single_eq_of_ne (Ne.symm hab) 1)
      (Pi.single_eq_of_ne hma 1)
      (Pi.single_eq_of_ne hmb 1)
  rw [H.card_E] at h3
  exact absurd h3 (not_le.mpr (Nat.pow_lt_pow_right hp.one_lt (by norm_num : 2 < 3)))

theorem GGOmA3Hyp.exists_eq_of_pair (H : GGOmA3Hyp F E J) {a b : Fin r} (hab : a ≠ b)
    (ha : F.ι (ofAdd (Pi.single a 1)) ∈ Subgroup.centralizer (J : Set (V ≃ₗ[K] V)))
    (hb : F.ι (ofAdd (Pi.single b 1)) ∈ Subgroup.centralizer (J : Set (V ≃ₗ[K] V)))
    {e : V ≃ₗ[K] V} (he : e ∈ E) :
    ∃ s : Fin r → ZMod p, F.ι (ofAdd s) = e ∧ ∀ m, m ≠ a → m ≠ b → s m = 0 := by
  obtain ⟨s, hs⟩ := F.exists_eq (H.le_A he)
  have hE' : F.ι s ∈ E := by rw [hs]; exact he
  refine ⟨toAdd s, by rw [ofAdd_toAdd]; exact hs, fun m hma hmb => ?_⟩
  exact H.apply_eq_zero_of_pair hab ha hb (by rwa [ofAdd_toAdd]) hma hmb

theorem GGOmA3Hyp.exists_pair_mem_of_pair (H : GGOmA3Hyp F E J) {a b : Fin r} (hab : a ≠ b)
    (ha : F.ι (ofAdd (Pi.single a 1)) ∈ Subgroup.centralizer (J : Set (V ≃ₗ[K] V)))
    (hb : F.ι (ofAdd (Pi.single b 1)) ∈ Subgroup.centralizer (J : Set (V ≃ₗ[K] V))) :
    ∃ k l : Fin r, k ≠ l ∧ k ≠ a ∧ k ≠ b ∧ l ≠ a ∧ l ≠ b ∧
      F.ι (ofAdd (Pi.single k 1)) ∈ J ∧ F.ι (ofAdd (Pi.single l 1)) ∈ J := by
  classical
  have hp : p.Prime := Fact.out
  have hr : 4 ≤ r := H.four_le
  haveI : Finite (V ≃ₗ[K] V) := by
    have : Finite V := Module.finite_of_finite K
    exact Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
      fun _ _ he => LinearEquiv.ext (congrFun he)
  haveI : Finite E :=
    Finite.of_injective (fun z : E => (z : V ≃ₗ[K] V)) fun _ _ h => Subtype.ext h
  have hS : 1 < (((Finset.univ : Finset (Fin r)).erase a).erase b).card := by
    have h1 : ((Finset.univ : Finset (Fin r)).erase a).card = r - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
    have h2 : (((Finset.univ : Finset (Fin r)).erase a).erase b).card = r - 2 := by
      rw [Finset.card_erase_of_mem
        (Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ b⟩), h1]
      omega
    rw [h2]; omega
  obtain ⟨k, hkS, l, hlS, hkl⟩ := Finset.one_lt_card.mp hS
  have hka : k ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hkS).2).1
  have hkb : k ≠ b := (Finset.mem_erase.mp hkS).1
  have hla : l ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hlS).2).1
  have hlb : l ≠ b := (Finset.mem_erase.mp hlS).1
  set t₀ : Fin r → ZMod p := Pi.single a 1 + Pi.single b 1 with ht₀
  have ht0a : t₀ a = 1 := by rw [ht₀]; simp [Pi.single_eq_of_ne hab]
  have ht0b : t₀ b = 1 := by rw [ht₀]; simp [Pi.single_eq_of_ne (Ne.symm hab)]
  have ht0k : t₀ k = 0 := by rw [ht₀]; simp [Pi.single_eq_of_ne hka, Pi.single_eq_of_ne hkb]
  have ht0l : t₀ l = 0 := by rw [ht₀]; simp [Pi.single_eq_of_ne hla, Pi.single_eq_of_ne hlb]
  have ht0 : t₀ ≠ 0 := by
    intro h
    have h1 : t₀ a = 0 := by rw [h]; rfl
    rw [ht0a] at h1
    exact one_ne_zero h1
  have hb0E : F.ι (ofAdd t₀) ∈ E := by
    have h1 : F.ι (ofAdd (Pi.single a 1)) ∈ E := H.mem_E_of_mem_centralizer (F.mem _) ha
    have h2 : F.ι (ofAdd (Pi.single b 1)) ∈ E := H.mem_E_of_mem_centralizer (F.mem _) hb
    have h3 : F.ι (ofAdd t₀) = F.ι (ofAdd (Pi.single a 1)) * F.ι (ofAdd (Pi.single b 1)) := by
      rw [ht₀, ofAdd_add, map_mul]
    rw [h3]
    exact E.mul_mem h1 h2
  have hk : F.ι (ofAdd (Pi.single k 1)) ∉ Subgroup.centralizer (J : Set (V ≃ₗ[K] V)) := by
    intro hkc
    have hkE : F.ι (ofAdd (Pi.single k 1)) ∈ E := H.mem_E_of_mem_centralizer (F.mem _) hkc
    have h := H.apply_eq_zero_of_pair hab ha hb hkE (m := k) hka hkb
    rw [Pi.single_eq_same] at h
    exact one_ne_zero h
  have hl : F.ι (ofAdd (Pi.single l 1)) ∉ Subgroup.centralizer (J : Set (V ≃ₗ[K] V)) := by
    intro hlc
    have hlE : F.ι (ofAdd (Pi.single l 1)) ∈ E := H.mem_E_of_mem_centralizer (F.mem _) hlc
    have h := H.apply_eq_zero_of_pair hab ha hb hlE (m := l) hla hlb
    rw [Pi.single_eq_same] at h
    exact one_ne_zero h
  obtain ⟨h, hh, hJB, hU⟩ :=
    exists_factor_of_mem H.nondeg H.tsub H.ne_two F H.le_orthDerived H.max H.le_A H.isComponent
      (t := t₀) hb0E
  have hX : h = X - 1 :=
    eq_X_sub_one_of_apply_eq_zero H.nondeg H.ne_two F H.le_orthDerived hh ht0k (hU k hk)
  have hbOdd : OddOrderIsometry Q p (F.ι (ofAdd t₀)) :=
    F.oddOrderIsometry H.nondeg H.ne_two hp H.le_orthDerived (ofAdd t₀)
  have hE : ∀ e ∈ E, ∃ n : ℕ, ∃ y : V ≃ₗ[K] V,
      y ∈ Subgroup.centralizer ({F.ι (ofAdd t₀)} : Set (V ≃ₗ[K] V)) ∧
        e = F.ι (ofAdd t₀) ^ n * y ∧
        ∀ u ∈ orbitSpace (F.ι (ofAdd t₀)).toLinearMap h, y u = u := by
    intro e he
    obtain ⟨s, hs, hsupp⟩ := H.exists_eq_of_pair hab ha hb he
    refine ⟨0, e, ?_, by rw [pow_zero, one_mul], ?_⟩
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (frame_comm F (H.le_A he) (H.le_A hb0E))
    · intro u hu
      rw [← hs]
      rw [hX, orbitSpace_X_sub_one] at hu
      refine (F.fix (ofAdd s) u).mpr fun j hj w hw => ?_
      rw [toAdd_ofAdd] at hj
      have hja : j = a ∨ j = b := by
        by_contra hjab
        push Not at hjab
        exact hj (hsupp j hjab.1 hjab.2)
      have ht0j : t₀ j ≠ 0 := by
        rcases hja with hja | hja
        · rw [hja, ht0a]; exact one_ne_zero
        · rw [hja, ht0b]; exact one_ne_zero
      exact (F.fix (ofAdd t₀) u).mp (mem_fixedSpace.mp hu) j
        (by rw [toAdd_ofAdd]; exact ht0j) w hw
  have hcomp : IsComponentOf J (orthDerived Q ⊓
      Subgroup.centralizer ({F.ι (ofAdd t₀)} : Set (V ≃ₗ[K] V))) :=
    isComponentOf_centralizer_of_le_block (b := F.ι (ofAdd t₀)) hbOdd hh hb0E H.isComponent hJB hE
  have hcard : Nat.card (A ⊓ Subgroup.centralizer (J : Set (V ≃ₗ[K] V)) :
      Subgroup (V ≃ₗ[K] V)) ≤ p ^ 2 := by
    calc Nat.card (A ⊓ Subgroup.centralizer (J : Set (V ≃ₗ[K] V)) : Subgroup (V ≃ₗ[K] V))
        ≤ Nat.card E := Nat.card_le_card_of_injective
          (fun x => (⟨x, H.centralizer_le x.2⟩ : E))
          (fun x y h => Subtype.ext (congrArg (fun z : E => (z : V ≃ₗ[K] V)) h))
      _ = p ^ 2 := H.card_E
  have hres := ggOmFrameCompInput_holds K V p H.ne_two Q H.nondeg H.tsub A H.le_orthDerived
    H.max r F H.four_le H.moves J t₀ ht0 hcomp hcard
  rcases hres with ⟨j, j', hβ, hL⟩ | ⟨k₀, c, ε, hc, _, hβc, _⟩
  ·
    have haj : a = j ∨ a = j' := by
      by_contra hjab
      push Not at hjab
      have h0 : t₀ a = 0 := hβ a hjab.1 hjab.2
      rw [ht0a] at h0
      exact one_ne_zero h0
    have hbj : b = j ∨ b = j' := by
      by_contra hjab
      push Not at hjab
      have h0 : t₀ b = 0 := hβ b hjab.1 hjab.2
      rw [ht0b] at h0
      exact one_ne_zero h0
    have notmem : ∀ {x : Fin r}, x ≠ a → x ≠ b → x ≠ j ∧ x ≠ j' := by
      intro x hxa hxb
      constructor
      · intro hxj
        rcases haj with ha' | ha'
        · exact hxa (hxj.trans ha'.symm)
        · rcases hbj with hb' | hb'
          · exact hxb (hxj.trans hb'.symm)
          · exact hab (ha'.trans hb'.symm)
      · intro hxj
        rcases haj with ha' | ha'
        · rcases hbj with hb' | hb'
          · exact hab (ha'.trans hb'.symm)
          · exact hxb (hxj.trans hb'.symm)
        · exact hxa (hxj.trans ha'.symm)
    obtain ⟨hkj, hkj'⟩ := notmem hka hkb
    obtain ⟨hlj, hlj'⟩ := notmem hla hlb
    exact ⟨k, l, hkl, hka, hkb, hla, hlb,
      hL (Pi.single k 1) (by rw [Pi.single_eq_of_ne hkj.symm])
        (by rw [Pi.single_eq_of_ne hkj'.symm]),
      hL (Pi.single l 1) (by rw [Pi.single_eq_of_ne hlj.symm])
        (by rw [Pi.single_eq_of_ne hlj'.symm])⟩
  ·
    have hkl0 : k ≠ k₀ ∨ l ≠ k₀ := by
      by_contra h
      push Not at h
      exact hkl (h.1.trans h.2.symm)
    rcases hkl0 with hk0 | hl0
    · have h0 : t₀ k = 0 := ht0k
      rw [hβc k hk0] at h0
      exact absurd h0 (mul_ne_zero (Units.ne_zero (ε k)) hc)
    · have h0 : t₀ l = 0 := ht0l
      rw [hβc l hl0] at h0
      exact absurd h0 (mul_ne_zero (Units.ne_zero (ε l)) hc)

end Pair

end CoordOm

end CFSG.StandardType
