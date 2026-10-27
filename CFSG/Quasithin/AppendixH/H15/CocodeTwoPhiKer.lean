module

public import CFSG.Quasithin.AppendixH.H15.CocodeTwoPhi

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code

variable {d : ℕ} {a b : Fin 24} {O : Finset (Fin 24)} {Tr S : Finset (Finset (Fin 24))}
  {B : Finset (Fin 24)} {T₀ Γ : Subgroup S24} {V : Type} [CommGroup V] {ρ : ↥Γ →* MulAut V}
  {β : ↥(⊤ : Subgroup V) →* ↥(mathModel false d a b Γ).sec ⧸
    (mathModel false d a b Γ).ker.subgroupOf (mathModel false d a b Γ).sec}

private theorem zmod2_ne_zero_iff (z : ZMod 2) : z ≠ 0 ↔ z = 1 := by
  revert z; decide

private theorem zmod2_add_eq_zero_of_iff {u v : ZMod 2} (h : u ≠ 0 ↔ v ≠ 0) : u + v = 0 := by
  revert u v; decide

private theorem zmod2_add_eq_one_of_not {u v : ZMod 2} (h : u ≠ 0 ↔ ¬ v ≠ 0) : u + v = 1 := by
  revert u v; decide

private theorem zmod2_add_self_add_one (u : ZMod 2) : u + (u + 1) = 1 := by
  revert u; decide

private theorem zmod2_add_add_one_self (u : ZMod 2) : (u + 1) + u = 1 := by
  revert u; decide

private theorem eY_mul_eY (X Y : Finset (Fin 24)) :
    eY X * eY Y = eY (symmDiff X Y) := by
  apply Multiplicative.toAdd.injective
  funext i
  simp only [toAdd_mul, Pi.add_apply, toAdd_eY, Finset.mem_symmDiff]
  by_cases hx : i ∈ X <;> by_cases hy : i ∈ Y <;> simp [hx, hy] <;> decide

private theorem zpow_eq_one_or_self {G : Type*} [Group G] {p : G} (hp : p * p = 1) (k : ℤ) :
    p ^ k = 1 ∨ p ^ k = p := by
  have hsq : p ^ (2 : ℤ) = 1 := (zpow_two p).trans hp
  obtain ⟨n, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    have h2 : p ^ (2 * n) = (p ^ (2 : ℤ)) ^ n := zpow_mul p 2 n
    rw [h2, hsq, one_zpow]
  · right
    have h3 : p ^ (2 * n + 1) = p ^ (2 * n) * p := zpow_add_one p (2 * n)
    have h2 : p ^ (2 * n) = (p ^ (2 : ℤ)) ^ n := zpow_mul p 2 n
    rw [h3, h2, hsq, one_zpow, one_mul]

private theorem golay_subset_octad {T : Finset (Fin 24)} (hO : IsOctad O)
    (hTO : T ⊆ O) (hT : eY T ∈ golayC) : T = ∅ ∨ T = O := by
  by_cases hTO' : T = O
  · exact Or.inr hTO'
  · left
    have hssub : T ⊂ O := Finset.ssubset_iff_subset_ne.mpr ⟨hTO, hTO'⟩
    have hcard : T.card < 8 := by
      have hlt := Finset.card_lt_card hssub
      have hOcard : O.card = 8 := hO.1
      omega
    exact (eY_mem_golayC_iff T hcard).mp hT

private theorem eq_sdiff_of_symmDiff_eq {T : Finset (Fin 24)} (hTO : T ⊆ O)
    (h : symmDiff T ({a, b} : Finset (Fin 24)) = O) : T = O \ {a, b} := by
  ext q
  constructor
  · intro hq
    rw [Finset.mem_sdiff]
    refine ⟨hTO hq, ?_⟩
    intro hqS
    have hnot : q ∉ symmDiff T ({a, b} : Finset (Fin 24)) := by
      rw [Finset.mem_symmDiff]
      rintro (⟨-, h1⟩ | ⟨-, h1⟩)
      · exact h1 hqS
      · exact h1 hq
    rw [h] at hnot
    exact hnot (hTO hq)
  · intro hq
    rw [Finset.mem_sdiff] at hq
    obtain ⟨hqO, hqS⟩ := hq
    have hmem : q ∈ symmDiff T ({a, b} : Finset (Fin 24)) := by rw [h]; exact hqO
    rw [Finset.mem_symmDiff] at hmem
    rcases hmem with ⟨hqT, -⟩ | ⟨hqS', -⟩
    · exact hqT
    · exact absurd hqS' hqS

private theorem ker_eq_of_ne22 (hd : d ≠ 22) :
    (mathModel false d a b Γ).ker = golayC := by
  unfold mathModel FFModel.golaySec
  exact if_neg hd

private theorem ker_eq_of_eq22 (hd : d = 22) :
    (mathModel false d a b Γ).ker = golayC ⊔ Subgroup.zpowers (pairVec a b) := by
  unfold mathModel FFModel.golaySec
  exact if_pos hd

namespace PhiData

variable (P : PhiData O β)

private theorem o_mem_O (p : Fin 8) : P.o p ∈ O := (P.o_mem (P.o p)).mpr ⟨p, rfl⟩

private theorem o_mem_oSet (x : Multiplicative (Fin 6 → ZMod 2)) (p : Fin 8) :
    P.o p ∈ oSet P.o x ↔ evVec (Multiplicative.toAdd x) p ≠ 0 := by
  unfold oSet
  constructor
  · intro hp
    rw [Finset.mem_image] at hp
    obtain ⟨q, hq, hqp⟩ := hp
    rw [Finset.mem_filter] at hq
    have hq' := hq.2
    rw [P.o_inj hqp] at hq'
    exact hq'
  · intro hp
    exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩, rfl⟩

private theorem o_mem_pair (p : Fin 8) :
    P.o p ∈ ({a, b} : Finset (Fin 24)) ↔ p = 0 ∨ p = 1 := by
  rw [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h)
    · exact Or.inl (P.o_inj (h.trans P.o_zero.symm))
    · exact Or.inr (P.o_inj (h.trans P.o_one.symm))
  · rintro (rfl | rfl)
    · exact Or.inl P.o_zero
    · exact Or.inr P.o_one

private theorem o_mem_sdiff_pair (p : Fin 8) :
    P.o p ∈ O \ ({a, b} : Finset (Fin 24)) ↔ ¬ (p = 0 ∨ p = 1) := by
  rw [Finset.mem_sdiff, o_mem_pair P p]
  exact ⟨fun h => h.2, fun h => ⟨P.o_mem_O p, h⟩⟩

private theorem oSet_subset_O (x : Multiplicative (Fin 6 → ZMod 2)) : oSet P.o x ⊆ O := by
  intro q hq
  unfold oSet at hq
  obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hq
  exact P.o_mem_O p

private theorem oSet_one : oSet P.o (1 : Multiplicative (Fin 6 → ZMod 2)) = ∅ := by
  unfold oSet
  rw [Finset.image_eq_empty, Finset.filter_eq_empty_iff]
  intro p _
  exact fun h => h (by change evVec (0 : Fin 6 → ZMod 2) p = 0; simp [evVec])

private theorem oSet_inj_or_sdiff {x y : Multiplicative (Fin 6 → ZMod 2)}
    (h : oSet P.o x = oSet P.o y ∨ oSet P.o x = O \ oSet P.o y) : x = y := by
  apply Multiplicative.toAdd.injective
  apply evVec_inj
  rcases h with h | h
  · left
    intro p
    have hiff : evVec (Multiplicative.toAdd x) p ≠ 0 ↔
        evVec (Multiplicative.toAdd y) p ≠ 0 := by
      rw [← o_mem_oSet P x p, ← o_mem_oSet P y p, h]
    exact zmod2_add_eq_zero_of_iff hiff
  · right
    intro p
    have hmemO : P.o p ∈ O := P.o_mem_O p
    have hiff : evVec (Multiplicative.toAdd x) p ≠ 0 ↔
        ¬ (evVec (Multiplicative.toAdd y) p ≠ 0) := by
      rw [← o_mem_oSet P x p, h, Finset.mem_sdiff, o_mem_oSet P y p]
      exact ⟨fun hh => hh.2, fun hh => ⟨hmemO, hh⟩⟩
    exact zmod2_add_eq_one_of_not hiff

private theorem evVec_eq_pairInd_of_oSet_pair {x : Multiplicative (Fin 6 → ZMod 2)}
    (hx : oSet P.o x = ({a, b} : Finset (Fin 24))) :
    ∀ p : Fin 8, evVec (Multiplicative.toAdd x) p =
      (if p = 0 ∨ p = 1 then (1 : ZMod 2) else 0) := by
  intro p
  have hmem : evVec (Multiplicative.toAdd x) p ≠ 0 ↔ p = 0 ∨ p = 1 := by
    rw [← o_mem_oSet P x p, hx, o_mem_pair P p]
  by_cases hp : p = 0 ∨ p = 1
  · rw [if_pos hp]
    exact (zmod2_ne_zero_iff _).mp (hmem.mpr hp)
  · rw [if_neg hp]
    by_contra hc
    exact hp (hmem.mp hc)

private theorem evVec_eq_pairInd_add_one_of_oSet_sdiff {x : Multiplicative (Fin 6 → ZMod 2)}
    (hx : oSet P.o x = O \ ({a, b} : Finset (Fin 24))) :
    ∀ p : Fin 8, evVec (Multiplicative.toAdd x) p =
      (if p = 0 ∨ p = 1 then (1 : ZMod 2) else 0) + 1 := by
  intro p
  have hmem : evVec (Multiplicative.toAdd x) p ≠ 0 ↔ ¬ (p = 0 ∨ p = 1) := by
    rw [← o_mem_oSet P x p, hx, o_mem_sdiff_pair P p]
  by_cases hp : p = 0 ∨ p = 1
  · have h0 : evVec (Multiplicative.toAdd x) p = 0 := by
      by_contra hc
      exact (hmem.mp hc) hp
    rw [h0, if_pos hp]; decide
  · have h1 : evVec (Multiplicative.toAdd x) p = 1 :=
      (zmod2_ne_zero_iff _).mp (hmem.mpr hp)
    rw [h1, if_neg hp]; decide

theorem ker_ne22 (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) (hd : d ≠ 22) : P.φ.ker = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hx1 : P.φ x = 1 := MonoidHom.mem_ker.mp hx
  have hker : eY (oSet P.o x) ∈ (mathModel false d a b Γ).ker :=
    (isVecOf_eq_one_iff hM (P.vec x)).mp hx1
  have hgolay : eY (oSet P.o x) ∈ golayC := by
    rwa [ker_eq_of_ne22 (d := d) (a := a) (b := b) (Γ := Γ) hd] at hker
  rcases golay_subset_octad P.o_octad (P.oSet_subset_O x) hgolay with h | h
  · exact P.oSet_inj_or_sdiff (y := 1) (Or.inl (by rw [h, P.oSet_one]))
  · exact P.oSet_inj_or_sdiff (y := 1) (Or.inr (by rw [h, P.oSet_one]; simp))

theorem ker_eq22 (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) (hd : d = 22) :
    P.φ.ker = Subgroup.zpowers (Multiplicative.ofAdd (evPair 0 1)) := by
  let w : Multiplicative (Fin 6 → ZMod 2) := Multiplicative.ofAdd (evPair 0 1)
  have hab : a ≠ b := by
    exact fun h => absurd (P.o_inj (P.o_zero.trans (h.trans P.o_one.symm))) (by decide)
  have hw : P.φ w = 1 := by
    have hpair := P.isVecOf_pair hM (p := 0) (q := 1) (by decide)
    rw [P.o_zero, P.o_one] at hpair
    have hker : pairVec a b ∈ (mathModel false d a b Γ).ker := by
      rw [ker_eq_of_eq22 (d := d) (a := a) (b := b) (Γ := Γ) hd]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    exact (isVecOf_eq_one_iff hM hpair).mpr hker
  refine le_antisymm ?_ ?_
  · intro x hx
    have hx1 : P.φ x = 1 := MonoidHom.mem_ker.mp hx
    have hker0 : eY (oSet P.o x) ∈ (mathModel false d a b Γ).ker :=
      (isVecOf_eq_one_iff hM (P.vec x)).mp hx1
    have hker : eY (oSet P.o x) ∈ golayC ⊔ Subgroup.zpowers (pairVec a b) := by
      rwa [ker_eq_of_eq22 (d := d) (a := a) (b := b) (Γ := Γ) hd] at hker0
    obtain ⟨c, hc, z, hz, hcz⟩ := (Subgroup.mem_sup).mp hker
    obtain ⟨k, hk⟩ := (Subgroup.mem_zpowers_iff).mp hz
    have hpq : pairVec a b * pairVec a b = 1 := sq24 (pairVec a b)
    rcases zpow_eq_one_or_self hpq k with hk1 | hk1
    · have hgolay : eY (oSet P.o x) ∈ golayC := by
        have heq : eY (oSet P.o x) = c := by
          calc eY (oSet P.o x) = c * pairVec a b ^ k := by rw [← hcz, hk]; rfl
            _ = c * 1 := by rw [hk1]
            _ = c := mul_one c
        exact heq.symm ▸ hc
      rcases golay_subset_octad P.o_octad (P.oSet_subset_O x) hgolay with h | h
      · rw [P.oSet_inj_or_sdiff (x := x) (y := 1) (Or.inl (by rw [h, P.oSet_one]))]
        exact Subgroup.one_mem _
      · rw [P.oSet_inj_or_sdiff (x := x) (y := 1) (Or.inr (by rw [h, P.oSet_one]; simp))]
        exact Subgroup.one_mem _
    · have hprod : eY (oSet P.o x) * pairVec a b ∈ golayC := by
        have heq : eY (oSet P.o x) * pairVec a b = c := by
          calc eY (oSet P.o x) * pairVec a b = (c * pairVec a b ^ k) * pairVec a b := by
                rw [← hcz, hk]; rfl
            _ = (c * pairVec a b) * pairVec a b := by rw [hk1]
            _ = c * (pairVec a b * pairVec a b) := mul_assoc c (pairVec a b) (pairVec a b)
            _ = c * 1 := by rw [hpq]
            _ = c := mul_one c
        exact heq.symm ▸ hc
      have hgolay : eY (symmDiff (oSet P.o x) ({a, b} : Finset (Fin 24))) ∈ golayC := by
        rw [← eY_mul_eY, ← pairVec_eq_eY_pair a b hab]
        exact hprod
      have hsub : symmDiff (oSet P.o x) ({a, b} : Finset (Fin 24)) ⊆ O := by
        intro q hq
        rw [Finset.mem_symmDiff] at hq
        rcases hq with ⟨hqT, -⟩ | ⟨hqS, -⟩
        · exact P.oSet_subset_O x hqT
        · rw [Finset.mem_insert, Finset.mem_singleton] at hqS
          rcases hqS with rfl | rfl
          · rw [← P.o_zero]; exact P.o_mem_O 0
          · rw [← P.o_one]; exact P.o_mem_O 1
      have hwvec : Multiplicative.toAdd w = evPair 0 1 := rfl
      have hvv : evVec (evPair 0 1) =
            (fun p => if p = (0 : Fin 8) ∨ p = 1 then (1 : ZMod 2) else 0) ∨
          evVec (evPair 0 1) =
            (fun p => if p = (0 : Fin 8) ∨ p = 1 then (1 : ZMod 2) else 0) + 1 :=
        evVec_evPair (i := (0 : Fin 8)) (j := 1) (by decide)
      rcases golay_subset_octad P.o_octad hsub hgolay with h | h
      · have hT : oSet P.o x = ({a, b} : Finset (Fin 24)) := Finset.symmDiff_eq_empty.mp h
        have hxw : x = w := by
          apply Multiplicative.toAdd.injective
          rw [hwvec]
          apply evVec_inj
          have hxind := P.evVec_eq_pairInd_of_oSet_pair hT
          rcases hvv with hv | hv
          · left; intro p; rw [hxind p, congrFun hv p]
            exact CharTwo.add_self_eq_zero _
          · right; intro p; rw [hxind p, congrFun hv p]
            exact zmod2_add_self_add_one _
        rw [hxw]
        exact Subgroup.mem_zpowers w
      · have hT : oSet P.o x = O \ ({a, b} : Finset (Fin 24)) :=
          eq_sdiff_of_symmDiff_eq (P.oSet_subset_O x) h
        have hxw : x = w := by
          apply Multiplicative.toAdd.injective
          rw [hwvec]
          apply evVec_inj
          have hxind := P.evVec_eq_pairInd_add_one_of_oSet_sdiff hT
          rcases hvv with hv | hv
          · right; intro p; rw [hxind p, congrFun hv p]
            exact zmod2_add_add_one_self _
          · left; intro p; rw [hxind p, congrFun hv p]
            exact CharTwo.add_self_eq_zero _
        rw [hxw]
        exact Subgroup.mem_zpowers w
  · rw [Subgroup.zpowers_le]
    exact MonoidHom.mem_ker.mpr hw

end PhiData

end CFSG.ASVolI.AppH

