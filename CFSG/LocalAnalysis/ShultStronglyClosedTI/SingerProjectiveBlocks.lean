module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SingerProjectiveBlockConfig

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.Singer

open scoped LinearAlgebra.Projectivization Pointwise
open Projectivization Module

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

namespace BlockConfig

variable (C : BlockConfig k V)
include C

theorem false_of_card_eq_two [Finite k] [CharP k 2] [Finite V] [FiniteDimensional k V]
    (hn : 3 ≤ finrank k V) (hb : Nat.card k = 2) : False := by
  have : Fintype k := Fintype.ofFinite k
  obtain ⟨Δ, hΔ⟩ := C.exists_block
  obtain ⟨x, hx, y, hy, hxy⟩ := C.exists_pair hΔ
  obtain ⟨z, hz, hzl⟩ := C.exists_notMem_line hn hΔ x y
  obtain ⟨Γ, hΓ, -, hpart⟩ := C.exists_partner hn hΔ
  have hl : C.l = 2 := (C.l_eq hn).trans hb
  have hone : ∀ a : k, a ≠ 0 → a = 1 := fun a ha => by
    have h := FiniteField.pow_card_sub_one_eq_one a ha
    rwa [Fintype.card_eq_nat_card, hb, pow_one] at h
  have hmk : ∀ {v w : V} (hv : v ≠ 0) (hw : w ≠ 0),
      Projectivization.mk k v hv = Projectivization.mk k w hw → v = w := by
    intro v w hv hw h
    obtain ⟨a, ha⟩ := (mk_eq_mk_iff' k v w hv hw).mp h
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hv (by rw [← ha, zero_smul])
    rw [← ha, hone a ha0, one_smul]
  have hsec : ∀ {Θ : Set (ℙ k V)}, Θ ∈ C.P → ∀ {p q : ℙ k V}, p ∈ Θ → q ∈ Θ → p ≠ q →
      pointsIn (line p q) ∩ Θ = {p, q} := by
    intro Θ hΘ p q hp hq hpq
    refine (Set.eq_of_subset_of_ncard_le ?_ ?_).symm
    · rintro r (rfl | rfl)
      · exact ⟨left_mem_pointsIn_line _ _, hp⟩
      · exact ⟨right_mem_pointsIn_line _ _, hq⟩
    · rw [C.ncard_secant hΘ hp hq hpq, hl, Set.ncard_pair hpq]
  set u := x.rep
  set v := y.rep
  set w := z.rep
  have hli := LinearIndependent.pair_iff.mp (linearIndependent_pair_iff_ne.mpr hxy)
  have hw : w ∉ Submodule.span k {u, v} := by
    rw [← line_eq_span, rep_mem_iff_mem_pointsIn]
    exact hzl
  have hu0 : u ≠ 0 := x.rep_nonzero
  have hv0 : v ≠ 0 := y.rep_nonzero
  have huv : u + v ≠ 0 := fun h => one_ne_zero (hli 1 1 (by rw [one_smul, one_smul, h])).1
  have huw : u + w ≠ 0 := fun h => hw (by
    rw [eq_neg_of_add_eq_zero_right h]
    exact Submodule.neg_mem _ (Submodule.subset_span (Set.mem_insert u {v})))
  have hvw : v + w ≠ 0 := fun h => hw (by
    rw [eq_neg_of_add_eq_zero_right h]
    exact Submodule.neg_mem _ (Submodule.subset_span (Set.mem_insert_of_mem u rfl)))
  have hvwne : v ≠ w := fun h => hw (h ▸ Submodule.subset_span (Set.mem_insert_of_mem u rfl))
  have huwne : u ≠ w := fun h => hw (h ▸ Submodule.subset_span (Set.mem_insert u {v}))
  have huvne : u ≠ v := fun h => hxy (by rw [← mk_rep x, ← mk_rep y]; congr 1)
  have hxz : x ≠ z := fun h => hzl (h ▸ left_mem_pointsIn_line x y)
  have hyz : y ≠ z := fun h => hzl (h ▸ right_mem_pointsIn_line x y)
  have hmiss : ∀ {p q : ℙ k V}, p ∈ Δ → q ∈ Δ → p ≠ q → (hpq : p.rep + q.rep ≠ 0) →
      Projectivization.mk k (p.rep + q.rep) hpq ∈ Γ := by
    intro p q hp hq hpq hs
    have hmem : Projectivization.mk k (p.rep + q.rep) hs ∈ pointsIn (line p q) := by
      rw [mk_mem_pointsIn, line_eq_span]
      exact Submodule.add_mem _ (Submodule.subset_span (Set.mem_insert _ _))
        (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
    refine hpart p hp q hq hpq _ hmem fun hmΔ => ?_
    rcases (hsec hΔ hp hq hpq).subset (Set.mem_inter hmem hmΔ) with h' | h'
    · have := hmk hs p.rep_nonzero (h'.trans (mk_rep p).symm)
      exact q.rep_nonzero (by simpa using this)
    · have := hmk hs q.rep_nonzero ((Set.mem_singleton_iff.mp h').trans (mk_rep q).symm)
      exact p.rep_nonzero (by simpa using this)
  set m₁ := Projectivization.mk k (u + v) huv
  set m₂ := Projectivization.mk k (u + w) huw
  set m₃ := Projectivization.mk k (v + w) hvw
  have hm₁ : m₁ ∈ Γ := hmiss hx hy hxy huv
  have hm₂ : m₂ ∈ Γ := hmiss hx hz hxz huw
  have hm₃ : m₃ ∈ Γ := hmiss hy hz hyz hvw
  have h12 : m₁ ≠ m₂ := fun h => hvwne (add_left_cancel (hmk huv huw h))
  have h13 : m₁ ≠ m₃ := fun h => huwne (by
    have e := hmk huv hvw h
    rw [add_comm v w] at e
    exact add_right_cancel e)
  have h23 : m₂ ≠ m₃ := fun h => huvne (add_right_cancel (hmk huw hvw h))
  have hm₃L : m₃ ∈ pointsIn (line m₁ m₂) := by
    rw [mk_mem_pointsIn, line_def, submodule_mk, submodule_mk]
    have : v + w = (u + v) + (u + w) := by
      have h2 : u + u = 0 := by
        rw [← two_smul k u, show (2 : k) = 0 from CharTwo.two_eq_zero, zero_smul]
      linear_combination (norm := module) -h2
    rw [this]
    exact Submodule.add_mem_sup (Submodule.mem_span_singleton_self _)
      (Submodule.mem_span_singleton_self _)
  rcases (hsec hΓ hm₁ hm₂ h12).subset (Set.mem_inter hm₃L hm₃) with h3 | h3
  · exact h13 h3.symm
  · exact h23 (Set.mem_singleton_iff.mp h3).symm

theorem plane_count [Finite k] [CharP k 2] [Finite V] [FiniteDimensional k V]
    (hn : 3 ≤ finrank k V) {Δ : Set (ℙ k V)} (hΔ : Δ ∈ C.P) {a p₁ p₂ : ℙ k V} (ha : a ∈ Δ)
    (h₁ : p₁ ∈ Δ) (h₂ : p₂ ∈ Δ) (h12 : p₁ ≠ p₂) (ha12 : a ∉ pointsIn (line p₁ p₂)) :
    1 + Nat.card k * (Nat.card k - 1) ≤
      (pointsIn (line p₁ p₂ ⊔ a.submodule) ∩ Δ).ncard := by
  classical
  set E := line p₁ p₂ ⊔ a.submodule
  set Q := pointsIn (line p₁ p₂) ∩ Δ
  have hQ : Q.ncard = Nat.card k := (C.ncard_secant hΔ h₁ h₂ h12).trans (C.l_eq hn)
  have hQfin : Q.Finite := Set.toFinite Q
  have hpa : ∀ p ∈ Q, p ≠ a := fun p hp e => ha12 (e ▸ hp.1)
  have haE : a ∈ pointsIn E := mem_pointsIn.mpr le_sup_right
  have hLE : pointsIn (line p₁ p₂) ⊆ pointsIn E := pointsIn_mono le_sup_left
  set T : ℙ k V → Set (ℙ k V) := fun p => (pointsIn (line a p) ∩ Δ) \ {a}
  have hT : ∀ p ∈ Q, (T p).ncard = Nat.card k - 1 := fun p hp => by
    rw [Set.ncard_sdiff_singleton_of_mem
      (show a ∈ pointsIn (line a p) ∩ Δ from ⟨left_mem_pointsIn_line a p, ha⟩),
      C.ncard_secant hΔ ha hp.2 (hpa p hp).symm, C.l_eq hn]
  have hmeet : ∀ p ∈ Q, ∀ p' ∈ Q, ∀ r, r ≠ a → r ∈ pointsIn (line a p) →
      r ∈ pointsIn (line a p') → p = p' := by
    intro p hp p' hp' r hra hr hr'
    have e : line a p = line a p' :=
      (line_eq_of_mem (hpa p hp).symm hr hra).symm.trans (line_eq_of_mem (hpa p' hp').symm hr' hra)
    by_contra hne
    have hp'L : p' ∈ pointsIn (line a p) := e ▸ right_mem_pointsIn_line a p'
    have e1 : line p p' = line a p :=
      line_eq_line_of_mem (hpa p hp).symm hne (right_mem_pointsIn_line a p) hp'L
    have e2 : line p p' = line p₁ p₂ := line_eq_line_of_mem h12 hne hp.1 hp'.1
    exact ha12 (e2 ▸ e1 ▸ left_mem_pointsIn_line a p)
  have hdisj : (hQfin.toFinset : Set (ℙ k V)).PairwiseDisjoint T := by
    intro p hp p' hp' hne
    rw [Function.onFun, Set.disjoint_left]
    rintro r ⟨⟨hr, -⟩, hra⟩ ⟨⟨hr', -⟩, -⟩
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hp hp'
    exact hne (hmeet p hp p' hp' r hra hr hr')
  have hsub : (⋃ p ∈ hQfin.toFinset, T p) ⊆ (pointsIn E ∩ Δ) \ {a} := by
    refine Set.iUnion₂_subset fun p hp => ?_
    rw [Set.Finite.mem_toFinset] at hp
    rintro r ⟨⟨hr, hrΔ⟩, hra⟩
    refine ⟨⟨pointsIn_mono (line_le_iff.mpr ⟨haE, hLE hp.1⟩) hr, hrΔ⟩, hra⟩
  have hcount := Set.ncard_le_ncard hsub
  rw [ncard_biUnion_of_pairwiseDisjoint _ _ hdisj,
    Finset.sum_congr rfl (fun p hp => hT p ((Set.Finite.mem_toFinset hQfin).mp hp)),
    Finset.sum_const, smul_eq_mul, ← Set.ncard_eq_toFinset_card Q hQfin, hQ,
    Set.ncard_sdiff_singleton_of_mem (show a ∈ pointsIn E ∩ Δ from ⟨haE, ha⟩)] at hcount
  have hpos : 1 ≤ (pointsIn E ∩ Δ).ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨a, haE, ha⟩
  omega

theorem false_of_four_le [Finite k] [CharP k 2] [Finite V] [FiniteDimensional k V]
    (hn : 3 ≤ finrank k V) (hb : 4 ≤ Nat.card k) : False := by
  obtain ⟨Δ, hΔ⟩ := C.exists_block
  obtain ⟨Γ, hΓ, hΓΔ, hpart⟩ := C.exists_partner hn hΔ
  obtain ⟨p₁, h₁⟩ := C.nonempty hΔ
  obtain ⟨p₂, h₂, h₂'⟩ : ∃ p₂ ∈ Δ, p₂ ∉ pointsIn p₁.submodule := by
    by_contra h
    push Not at h
    exact C.not_subset_pointsIn hΔ (by rw [finrank_submodule]; omega) h
  have h12 : p₁ ≠ p₂ := fun e => h₂' (e ▸ mem_pointsIn.mpr le_rfl)
  obtain ⟨a, ha, ha12⟩ := C.exists_notMem_line hn hΔ p₁ p₂
  set E := line p₁ p₂ ⊔ a.submodule with hEdef
  have hE : finrank k E = 3 := finrank_line_sup h12 ha12
  have haE : a ∈ pointsIn E := mem_pointsIn.mpr le_sup_right
  have hLE : line p₁ p₂ ≤ E := le_sup_left
  have h₁E : p₁ ∈ pointsIn E := pointsIn_mono hLE (left_mem_pointsIn_line p₁ p₂)
  have h₂E : p₂ ∈ pointsIn E := pointsIn_mono hLE (right_mem_pointsIn_line p₁ p₂)
  have ha1 : a ≠ p₁ := fun e => ha12 (e ▸ left_mem_pointsIn_line p₁ p₂)
  have ha2 : a ≠ p₂ := fun e => ha12 (e ▸ right_mem_pointsIn_line p₁ p₂)
  have hcountΔ : 1 + Nat.card k * (Nat.card k - 1) ≤ (pointsIn E ∩ Δ).ncard :=
    C.plane_count hn hΔ ha h₁ h₂ h12 ha12
  obtain ⟨o₁, ho₁L, ho₁Δ⟩ := C.exists_notMem_secant hΔ ha h₁ ha1
  obtain ⟨o₂, ho₂L, ho₂Δ⟩ := C.exists_notMem_secant hΔ ha h₂ ha2
  have ho₁E : o₁ ∈ pointsIn E := pointsIn_mono (line_le_iff.mpr ⟨haE, h₁E⟩) ho₁L
  have ho₂E : o₂ ∈ pointsIn E := pointsIn_mono (line_le_iff.mpr ⟨haE, h₂E⟩) ho₂L
  have ho₁Γ : o₁ ∈ Γ := hpart a ha p₁ h₁ ha1 o₁ ho₁L ho₁Δ
  have ho₂Γ : o₂ ∈ Γ := hpart a ha p₂ h₂ ha2 o₂ ho₂L ho₂Δ
  have ho12 : o₁ ≠ o₂ := by
    intro e
    have hoa : o₁ ≠ a := fun e' => ho₁Δ (e' ▸ ha)
    have e1 : line a p₁ = line a p₂ := (line_eq_of_mem ha1 ho₁L hoa).symm.trans
      (line_eq_of_mem ha2 (e ▸ ho₂L) hoa)
    have hp₂L : p₂ ∈ pointsIn (line a p₁) := e1 ▸ right_mem_pointsIn_line a p₂
    have e2 : line p₁ p₂ = line a p₁ :=
      line_eq_line_of_mem ha1 h12 (right_mem_pointsIn_line a p₁) hp₂L
    exact ha12 (e2 ▸ left_mem_pointsIn_line a p₁)
  set D := line o₁ o₂
  have hDE : D ≤ E := line_le_iff.mpr ⟨ho₁E, ho₂E⟩
  have hb4 : 4 * 3 ≤ Nat.card k * (Nat.card k - 1) := Nat.mul_le_mul hb (by omega)
  by_cases hcol : ∃ c ∈ pointsIn E ∩ Γ, c ∉ pointsIn D
  ·
    obtain ⟨c, hc, hcD⟩ := hcol
    have hE' : line o₁ o₂ ⊔ c.submodule = E := by
      have : FiniteDimensional k E := Module.finite_of_finrank_eq_succ hE
      exact Submodule.eq_of_le_of_finrank_eq (sup_le hDE hc.1)
        ((finrank_line_sup ho12 hcD).trans hE.symm)
    have hcountΓ : 1 + Nat.card k * (Nat.card k - 1) ≤ (pointsIn E ∩ Γ).ncard := by
      rw [← hE']
      exact C.plane_count hn hΓ hc.2 ho₁Γ ho₂Γ ho12 hcD
    have hdisj : Disjoint (pointsIn E ∩ Δ) (pointsIn E ∩ Γ) := by
      rw [Set.disjoint_left]
      rintro r ⟨-, hrΔ⟩ ⟨-, hrΓ⟩
      exact C.notMem_of_ne hΔ hΓ hΓΔ hrΔ hrΓ
    have hle : (pointsIn E ∩ Δ ∪ pointsIn E ∩ Γ).ncard ≤ (pointsIn E).ncard :=
      Set.ncard_le_ncard (Set.union_subset Set.inter_subset_left Set.inter_subset_left)
    rw [Set.ncard_union_eq hdisj, ncard_pointsIn_of_finrank_three hE] at hle
    have hsq : Nat.card k ^ 2 = Nat.card k * (Nat.card k - 1) + Nat.card k := by
      rw [sq, ← Nat.mul_add_one, Nat.sub_add_cancel (by omega)]
    have hsq' : 4 * Nat.card k ≤ Nat.card k ^ 2 := by
      rw [sq]
      exact Nat.mul_le_mul_right _ hb
    omega
  push Not at hcol
  obtain ⟨p₀, hp₀⟩ := Set.ncard_eq_one.mp (C.ncard_secant_diff hn hΓ ho₁Γ ho₂Γ ho12)
  have hp₀' : p₀ ∈ pointsIn D \ Γ := hp₀ ▸ Set.mem_singleton p₀
  have hDΓ : ∀ r ∈ pointsIn D, r ∉ Γ → r = p₀ := fun r hr hrΓ => by
    have : r ∈ pointsIn D \ Γ := ⟨hr, hrΓ⟩
    rwa [hp₀] at this
  have hp₀E : p₀ ∈ pointsIn E := pointsIn_mono hDE hp₀'.1
  have hX : ∀ z ∈ pointsIn E ∩ Δ, ∀ z' ∈ pointsIn E ∩ Δ, z ≠ z' →
      p₀ ∉ pointsIn (line z z') := by
    intro z hz z' hz' hzz' hp₀zz'
    obtain ⟨m, hm, hmΔ⟩ := C.exists_notMem_secant hΔ hz.2 hz'.2 hzz'
    have hmΓ : m ∈ Γ := hpart z hz.2 z' hz'.2 hzz' m hm hmΔ
    have hmE : m ∈ pointsIn E := pointsIn_mono (line_le_iff.mpr ⟨hz.1, hz'.1⟩) hm
    have hmD : m ∈ pointsIn D := hcol m ⟨hmE, hmΓ⟩
    have hmp₀ : m ≠ p₀ := fun e => hp₀'.2 (e ▸ hmΓ)
    have e1 : line m p₀ = line z z' := line_eq_line_of_mem hzz' hmp₀ hm hp₀zz'
    have e2 : line m p₀ = D := line_eq_line_of_mem ho12 hmp₀ hmD hp₀'.1
    have hzD : z ∈ pointsIn D := e2 ▸ e1 ▸ left_mem_pointsIn_line z z'
    have hz'D : z' ∈ pointsIn D := e2 ▸ e1 ▸ right_mem_pointsIn_line z z'
    exact hzz' ((hDΓ z hzD (C.notMem_of_ne hΔ hΓ hΓΔ hz.2)).trans
      (hDΓ z' hz'D (C.notMem_of_ne hΔ hΓ hΓΔ hz'.2)).symm)
  obtain ⟨D', hD'2, hD'E, hp₀D'⟩ :
      ∃ D' : Submodule k V, finrank k D' = 2 ∧ D' ≤ E ∧ p₀ ∉ pointsIn D' := by
    by_cases hp₀12 : p₀ ∈ pointsIn (line p₁ p₂)
    · have hp₀a : p₀ ≠ a := fun e => ha12 (e ▸ hp₀12)
      by_cases hp₀1 : p₀ ∈ pointsIn (line a p₁)
      · refine ⟨line a p₂, finrank_line ha2, line_le_iff.mpr ⟨haE, h₂E⟩, fun hp₀2 => ?_⟩
        have e1 : line a p₁ = line a p₂ := (line_eq_of_mem ha1 hp₀1 hp₀a).symm.trans
          (line_eq_of_mem ha2 hp₀2 hp₀a)
        have hp₂L : p₂ ∈ pointsIn (line a p₁) := e1 ▸ right_mem_pointsIn_line a p₂
        have e2 : line p₁ p₂ = line a p₁ :=
          line_eq_line_of_mem ha1 h12 (right_mem_pointsIn_line a p₁) hp₂L
        exact ha12 (e2 ▸ left_mem_pointsIn_line a p₁)
      · exact ⟨line a p₁, finrank_line ha1, line_le_iff.mpr ⟨haE, h₁E⟩, hp₀1⟩
    · exact ⟨line p₁ p₂, finrank_line h12, hLE, hp₀12⟩
  have hproj : ∀ z ∈ (pointsIn E ∩ Δ) \ {p₀}, ∃ r, r ∈ pointsIn (line p₀ z) ∧ r ∈ pointsIn D' :=
    fun z hz => exists_mem_pointsIn_of_le_plane hE
      (finrank_line (Ne.symm (Set.mem_singleton_iff.not.mp hz.2)))
      hD'2 (line_le_iff.mpr ⟨hp₀E, hz.1.1⟩) hD'E
  have : Nonempty (ℙ k V) := ⟨p₀⟩
  choose! π hπ₁ hπ₂ using hproj
  have hinj : Set.InjOn π ((pointsIn E ∩ Δ) \ {p₀}) := by
    intro z hz z' hz' he
    by_contra hne
    have hzp : z ≠ p₀ := Set.mem_singleton_iff.not.mp hz.2
    have hz'p : z' ≠ p₀ := Set.mem_singleton_iff.not.mp hz'.2
    have hrp : π z ≠ p₀ := fun e => hp₀D' (e ▸ hπ₂ z hz)
    have e1 : line p₀ (π z) = line p₀ z := line_eq_of_mem (Ne.symm hzp) (hπ₁ z hz) hrp
    have e2 : line p₀ (π z) = line p₀ z' :=
      line_eq_of_mem (Ne.symm hz'p) (he ▸ hπ₁ z' hz') hrp
    have hz'L : z' ∈ pointsIn (line p₀ z) := e1 ▸ e2 ▸ right_mem_pointsIn_line p₀ z'
    have hl : line z z' = line p₀ z :=
      line_eq_line_of_mem (Ne.symm hzp) hne (right_mem_pointsIn_line p₀ z) hz'L
    exact hX z hz.1 z' hz'.1 hne (hl ▸ left_mem_pointsIn_line p₀ z)
  have hle := Set.ncard_le_ncard_of_injOn π (fun z hz => hπ₂ z hz) hinj
  rw [ncard_pointsIn_of_finrank_two hD'2] at hle
  have hle' := Set.ncard_le_ncard_sdiff_add_ncard (pointsIn E ∩ Δ) {p₀}
  rw [Set.ncard_singleton] at hle'
  have hb3 : Nat.card k * 3 ≤ Nat.card k * (Nat.card k - 1) := Nat.mul_le_mul_left _ (by omega)
  omega

theorem false [Finite k] [CharP k 2] [Finite V] [FiniteDimensional k V]
    (hn : 3 ≤ finrank k V) : False := by
  have h1 : 1 < Nat.card k := Finite.one_lt_card
  have h3 := card_ne_three (k := k)
  rcases (by omega : Nat.card k = 2 ∨ 4 ≤ Nat.card k) with hb | hb
  · exact C.false_of_card_eq_two hn hb
  · exact C.false_of_four_le hn hb

end BlockConfig

theorem not_exists_uniform_doublyTransitive_spanning_blocks [Finite k] [CharP k 2]
    [FiniteDimensional k V] (hn : 3 ≤ finrank k V) :
    ¬ ∃ (G : Subgroup (V ≃ₗ[k] V)) (P : Set (Set (ℙ k V))) (δ : ℕ) (K : Subgroup (V ≃ₗ[k] V)),
      Setoid.IsPartition P ∧ (∀ g ∈ G, ∀ Δ ∈ P, g • Δ ∈ P) ∧ 2 ≤ P.ncard ∧ 1 < δ ∧
      (∀ Δ ∈ P, Δ.ncard = δ) ∧ K ≤ G ∧ (K.subgroupOf G).Normal ∧
      (∀ Δ ∈ P, ∀ Γ ∈ P, ∃ g ∈ G, g • Δ = Γ) ∧ (∀ h ∈ K, ∀ Δ ∈ P, h • Δ = Δ) ∧
      (∀ Δ ∈ P, ∀ x ∈ Δ, ∀ y ∈ Δ, ∀ x' ∈ Δ, ∀ y' ∈ Δ, x ≠ y → x' ≠ y' →
        ∃ h ∈ K, h • x = x' ∧ h • y = y') ∧
      ∀ Δ ∈ P, ⨆ p ∈ Δ, p.submodule = ⊤ := by
  rintro ⟨G, P, δ, K, hP, -, hP2, hδ, hcard, -, -, htrans, hK, h2, hspan⟩
  have : Finite V := Module.finite_of_finite k
  have hne : ∃ Δ ∈ P, ∃ Γ ∈ P, Δ ≠ Γ := by
    obtain ⟨Δ, Γ, hΔ, hΓ, hne⟩ := (Set.one_lt_ncard_iff (Set.toFinite P)).mp hP2
    exact ⟨Δ, hΔ, Γ, hΓ, hne⟩
  let C : BlockConfig k V :=
    { P := P
      K := K
      δ := δ
      existsUnique := hP.2
      ncard_eq := hcard
      one_lt := hδ
      exists_ne := hne
      transitive := fun Δ hΔ Γ hΓ => by
        obtain ⟨g, -, hg⟩ := htrans Δ hΔ Γ hΓ
        exact ⟨g, hg⟩
      smul_eq := hK
      twoTransitive := h2
      spans := hspan }
  exact C.false hn

end CFSG.ShultStronglyClosedTI.Singer
