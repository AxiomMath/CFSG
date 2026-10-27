module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusInterfaces
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusTwoCoord
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusWeightsAlg
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusWeightsSingle
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQBinaryDigit
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusInvol

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.RootSystem CFSG.Quasithin.SmithCurtis

private theorem c2slomqnb_spinMatrix_apply {n : ℕ} {F : Type} [Field F]
    (g : spinGroup (quadPlus n F)) (x y : Fin n ⊕ Fin n) :
    (spinMatrix (quadPlus n F) g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) x y =
      spinAction (quadPlus n F) g (Pi.single y 1) x := by
  rw [coe_spinMatrix, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe]

private theorem c2slomqnb_longCoroot_self {n : ℕ} (hn : 3 ≤ n) {m : Fin n} (hm : m.val = 0) :
    longCoroot (rootIdxD n m) (rootIdxD' n m) true (rootSignD n m) m true = 1 := by
  have h1 : m.val + 1 < n := by omega
  rw [rootIdxD_of_lt n h1, rootIdxD'_of_lt n h1, rootSignD_of_lt n h1]
  have hne : m ≠ (⟨m.val + 1, h1⟩ : Fin n) := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_mk] at hv
    omega
  simp [longCoroot, hne]

private lemma c2slomqnb_exists_wt_ne {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] [Finite F]
    [CharP F 2] {m : ℕ} (hm : m = Nat.card Fˣ) (hodd : Odd m) {k : Type} [Field k]
    (ι : F →+* k) {ν ν' : Fin n → ZMod m} (hne : ν ≠ ν') :
    ∃ h ∈ (omPlusCurtisDatum n F hn).H, omqPlusWt ι ν h ≠ omqPlusWt ι ν' h := by
  by_contra h
  apply hne
  apply omq_omPlus_wt_injective (hn := hn) (hm := hm) hodd ι
  intro g hg
  by_contra hc
  exact h ⟨g, hg, hc⟩

private theorem c2slomqnb_finrank_range_conj {G k V : Type*} [Group G] [Field k] [AddCommGroup V]
    [Module k V] (ρ : Representation k G V) (g y : G) :
    Module.finrank k (LinearMap.range (ρ (g * y * g⁻¹) - 1)) =
      Module.finrank k (LinearMap.range (ρ y - 1)) := by
  have hconj : ρ (g * y * g⁻¹) - 1 = ρ g * (ρ y - 1) * ρ (g⁻¹) := by
    rw [map_mul, map_mul]
    have h2 : ρ g * ρ (g⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    calc ρ g * ρ y * ρ (g⁻¹) - 1 = (ρ g * ρ y - ρ g) * ρ (g⁻¹) := by rw [sub_mul, h2]
      _ = ρ g * (ρ y - 1) * ρ (g⁻¹) := by rw [mul_sub, mul_one]
  have hsurj : Function.Surjective (ρ (g⁻¹)) := fun b =>
    ⟨ρ g b, by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]⟩
  have hrange : LinearMap.range (ρ g * (ρ y - 1) * ρ (g⁻¹)) =
      (LinearMap.range (ρ y - 1)).map (ρ g) := by
    rw [show ρ g * (ρ y - 1) * ρ (g⁻¹) =
      (ρ g).comp ((ρ y - 1).comp (ρ (g⁻¹))) from rfl]
    rw [LinearMap.range_comp, LinearMap.range_comp,
      LinearMap.range_eq_top.mpr hsurj, Submodule.map_top]
  have hleft : Function.LeftInverse (ρ (g⁻¹)) (ρ g) := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hright : Function.RightInverse (ρ (g⁻¹)) (ρ g) := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  let e : V ≃ₗ[k] V := LinearEquiv.ofBijective (ρ g) ⟨hleft.injective, hright.surjective⟩
  rw [hconj, hrange]
  exact e.finrank_map_eq (LinearMap.range (ρ y - 1))

theorem omq_omPlus_nonbinary_rank (h1 : OmqPlusWeightVector) (h2 : OmqRankFromWeights) {n : ℕ}
    (hn : 3 ≤ n) {F : Type} [Field F] [Finite F] [CharP F 2] (hF4 : 4 ≤ Nat.card F)
    {k V : Type} [Field k] [CharP k 2] [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ι : F →+* k) {σ : Representation k (spinGroup (quadPlus n F)) V} (hσ : IsSimpleRep σ)
    {y : V} {χ : spinGroup (quadPlus n F) → k} {μ : Fin n → k}
    (ht : (omPlusCurtisDatum n F hn).IsCurtisType σ y χ μ)
    (hJ : ∀ i : Fin n, μ i = (omPlusCurtisDatum n F hn).dScalar χ i ↔ i.val = 0)
    {c : ℕ} (hc1 : 1 ≤ c) (hcq : c ≤ Nat.card Fˣ)
    (hχ : ∀ h ∈ (omPlusCurtisDatum n F hn).H,
      χ h = ι ((spinMatrix (quadPlus n F) h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
        (Sum.inl ⟨0, by omega⟩) (Sum.inl ⟨0, by omega⟩)) ^ c)
    (hpow : ∀ a : ℕ, c ≠ 2 ^ a) {g : spinGroup (quadPlus n F)} (hg2 : g * g = 1)
    (hσg : σ g ≠ 1) :
    4 ≤ Module.finrank k (LinearMap.range (σ g - 1)) := by
  classical
  obtain ⟨j, hj0, hjc, hjodd⟩ := omq_exists_odd_choose_lt hc1 hpow
  let D := omPlusCurtisDatum n F hn
  let m : ℕ := Nat.card Fˣ
  have hm : m = Nat.card Fˣ := rfl
  have hodd : Odd m := by
    rw [hm, Nat.card_units]
    haveI : Fintype F := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    obtain ⟨k, hk⟩ := Nat.even_iff.mpr (FiniteField.even_card_of_char_two (ringChar.eq F 2))
    have hk1 : 1 ≤ k := by
      have h2 : 2 ≤ Fintype.card F := by
        rw [← Nat.card_eq_fintype_card]
        omega
      omega
    exact ⟨k - 1, by omega⟩
  have hm3 : 3 ≤ m := by
    rw [hm, Nat.card_units]
    omega
  have hjm : j < m := by omega
  let node0 : Fin n := ⟨0, by omega⟩
  let node1 : Fin n := ⟨1, by omega⟩
  have h01 : node0.val + 1 < n := by simp [node0]; omega
  have hidx : (⟨node0.val + 1, h01⟩ : Fin n) = node1 := by
    apply Fin.ext
    simp [node0, node1]
  have hnode : node0 ≠ node1 := by
    intro h
    have hv := congrArg Fin.val h
    simp [node0, node1] at hv
  have hmem : ∀ a : Fˣ, torusD F hn node0 a ∈ D.H := by
    intro a
    change torusD F hn node0 a ∈ (omPlusCurtisDatum n F hn).H
    rw [omPlusCurtisDatum_H (hn := hn)]
    exact Subgroup.mem_iSup_of_mem node0 ⟨a, rfl⟩
  have hentry : ∀ a : Fˣ,
      (spinMatrix (quadPlus n F) (torusD F hn node0 a) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (Sum.inl node0) (Sum.inl node0) = (a : F) := by
    intro a
    rw [c2slomqnb_spinMatrix_apply, ← plusVec_true n F node0, spinAction_torusD]
    have hlc : longCoroot (rootIdxD n node0) (rootIdxD' n node0) true (rootSignD n node0)
        node0 true = 1 := c2slomqnb_longCoroot_self hn (by simp [node0])
    rw [hlc, zpow_one]
    simp [plusVec_true]
  have hχi : ∀ a : Fˣ, χ (torusD F hn node0 a) = ι (a : F) ^ c := by
    intro a
    rw [hχ _ (hmem a)]
    rw [show (spinMatrix (quadPlus n F) (torusD F hn node0 a) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
        (Sum.inl ⟨0, by omega⟩) (Sum.inl ⟨0, by omega⟩) = (a : F) from hentry a]
  have hsep : μ node0 = D.dScalar χ node0 := (hJ node0).mpr (by simp [node0])
  have hχθ : ∀ h ∈ D.H, χ h = omqPlusWt ι (Pi.single node0 (c : ZMod m)) h := by
    intro h hh
    rw [omq_omPlus_wt_single (hn := hn) (m := m) (hm := hm) (ι := ι) node0 c hh]
    exact hχ h hh
  let να : Fin n → ZMod m := fun b => ((toStdD n (Pi.single node0 1) b : ℤ) : ZMod m)
  have hνα : ∀ b, να b = (if b = node0 then (1 : ZMod m) else 0) -
      (if b = node1 then (1 : ZMod m) else 0) := by
    intro b
    change ((toStdD n (Pi.single node0 1) b : ℤ) : ZMod m) = _
    rw [toStdD_single_of_lt (n := n) (k := node0) h01, hidx]
    simp [Pi.sub_apply, Pi.single_apply]
  have hνα0 : να node0 = 1 := by
    rw [hνα node0]
    simp [hnode]
  have hνα1 : να node1 = -1 := by
    rw [hνα node1]
    simp [hnode.symm]
  have hνα_other : ∀ b, b ≠ node0 → b ≠ node1 → να b = 0 := by
    intro b hb0 hb1
    rw [hνα b]
    simp [hb0, hb1]
  have hcjm : c - j < m := by omega
  have hcjp : 0 < c - j := by omega
  let A : ZMod m := (c : ZMod m) - (j : ZMod m)
  let B : ZMod m := (j : ZMod m)
  have hAc : A ≠ 0 := by
    change (c : ZMod m) - (j : ZMod m) ≠ 0
    intro h
    rw [sub_eq_zero] at h
    by_cases hcm : c = m
    · rw [hcm] at h
      have hj0' : (j : ZMod m) = 0 := by
        rw [← h]
        simp
      have hdiv : m ∣ j := (ZMod.natCast_eq_zero_iff j m).mp hj0'
      exact absurd (Nat.le_of_dvd hj0 hdiv) (by omega)
    · have hclt : c < m := lt_of_le_of_ne (by rw [hm]; exact hcq) hcm
      have hmod : c ≡ j [MOD m] := (ZMod.natCast_eq_natCast_iff c j m).mp h
      exact absurd (Nat.ModEq.eq_of_lt_of_lt hmod hclt hjm) (by omega)
  have hBc : B ≠ 0 := by
    change (j : ZMod m) ≠ 0
    intro h
    have hdiv : m ∣ j := (ZMod.natCast_eq_zero_iff j m).mp h
    exact absurd (Nat.le_of_dvd hj0 hdiv) (by omega)
  let νbase : Fin n → ZMod m := Pi.single node0 (c : ZMod m) + j • (-να)
  have hνbase : νbase = Pi.single node0 A + Pi.single node1 B := by
    funext b
    by_cases hb0 : b = node0
    · subst hb0
      simp only [νbase, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hnode,
        Pi.smul_apply, Pi.neg_apply, hνα0]
      rw [nsmul_eq_mul]
      dsimp only [A]
      ring
    · by_cases hb1 : b = node1
      · subst hb1
        simp only [νbase, Pi.add_apply, Pi.single_eq_of_ne hnode.symm, Pi.single_eq_same,
          Pi.smul_apply, Pi.neg_apply, hνα1]
        rw [nsmul_eq_mul]
        dsimp only [B]
        ring
      · simp only [νbase, Pi.add_apply, Pi.single_eq_of_ne hb0, Pi.single_eq_of_ne hb1,
          Pi.smul_apply, Pi.neg_apply, hνα_other b hb0 hb1]
        simp
  have hscalar : ∀ h ∈ D.H, χ h * (omqPlusWt ι να h)⁻¹ ^ j = omqPlusWt ι νbase h := by
    intro h hh
    rw [hχθ h hh,
      ← omq_omPlus_wt_neg (hn := hn) (m := m) (hm := hm) (ι := ι) να hh,
      ← omq_omPlus_wt_nsmul (hn := hn) (m := m) (hm := hm) (ι := ι) j (-να) hh,
      ← omq_omPlus_wt_add (hn := hn) (m := m) (hm := hm) (ι := ι)
        (Pi.single node0 (c : ZMod m)) (j • (-να)) hh]
  obtain ⟨w, hw0, hw1⟩ :=
    h1 (n := n) hn (k := k) ι (V := V) hσ ht node0 hsep hc1 hcq hχi hjodd
  have hw : ∀ h ∈ D.H, σ h w = omqPlusWt ι νbase h • w := by
    intro h hh
    rw [hw1 h hh, hscalar h hh]
  have hg1 : g ≠ 1 := by
    intro h
    exact hσg (by rw [h, map_one])
  obtain ⟨g', π, s, hs, hprod, hshape, hgmat⟩ :=
    exists_conj_spinMatrix_eq_spMonoPerm (n := n) (K := F) hn hg2 hg1
  obtain ⟨x, hxr, hxw⟩ :=
    exists_nW_eq_of_spinMatrix_eq (n := n) (K := F) hn hs hprod hgmat
  obtain ⟨u, hu_inj, hu_mem, hu_move⟩ :=
    omq_exists_four_orbit_two_coord (n := n) (m := m) hn hodd (A := A) (B := B) hAc hBc
      (a := node0) (b := node1) hnode hs hshape
  choose π' s' hs' hprod' hact using hu_mem
  have hxex : ∀ i : Fin 4, ∃ x' : (coxeterMatrix (isFiniteType_cartanD n)).Group,
      OmRealizes n x' (π' i) (s' i) := fun i =>
    exists_omRealizes_of_even (n := n) (by omega) (π' i) (hs' i) (hprod' i)
  choose xi hxi using hxex
  let η : Fin 4 → spinGroup (quadPlus n F) → k := fun i => omqPlusWt ι (u i)
  let wVec : Fin 4 → V := fun i => σ (D.nW (xi i)) w
  have hwnz : ∀ i, wVec i ≠ 0 := by
    intro i h0
    have h2' : w = 0 := by
      have h3 := congrArg (fun z => σ ((D.nW (xi i))⁻¹) z) h0
      rw [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply] at h3
      exact h3
    exact hw0 h2'
  have hchar : ∀ i, ∀ h ∈ D.H, σ h (wVec i) = η i h • wVec i := by
    intro i h hh
    have hconj := omq_omPlus_wt_conj (hn := hn) (m := m) (hm := hm) (ι := ι) (hxi i) (hs' i)
      νbase hh
    obtain ⟨hconjH, hconjW⟩ := hconj
    have hstep : σ h (σ (D.nW (xi i)) w) =
        σ (D.nW (xi i)) (σ ((D.nW (xi i))⁻¹ * h * D.nW (xi i)) w) := by
      have hgm : h * D.nW (xi i) =
          D.nW (xi i) * ((D.nW (xi i))⁻¹ * h * D.nW (xi i)) := by group
      calc σ h (σ (D.nW (xi i)) w)
          = (σ h * σ (D.nW (xi i))) w := by rw [Module.End.mul_apply]
        _ = σ (h * D.nW (xi i)) w := by rw [map_mul]
        _ = σ (D.nW (xi i) * ((D.nW (xi i))⁻¹ * h * D.nW (xi i))) w := by rw [hgm]
        _ = (σ (D.nW (xi i)) * σ ((D.nW (xi i))⁻¹ * h * D.nW (xi i))) w := by rw [map_mul]
        _ = σ (D.nW (xi i)) (σ ((D.nW (xi i))⁻¹ * h * D.nW (xi i)) w) := by
              rw [Module.End.mul_apply]
    rw [hstep, hw _ hconjH, map_smul]
    congr 1
    rw [hconjW, hνbase, hact i]
  have hdistinct : ∀ l l' : Fin 4, l ≠ l' → ∃ h ∈ D.H, η l h ≠ η l' h := fun l l' hll =>
    c2slomqnb_exists_wt_ne (hn := hn) (hm := hm) hodd ι (fun h => hll (hu_inj h))
  have hmove : ∀ l l' : Fin 4, ∃ h ∈ D.H,
      η l ((D.nW x)⁻¹ * h * D.nW x) ≠ η l' h := by
    intro l l'
    have hne : omqSignedAct π s (u l) ≠ u l' := (hu_move l' l).symm
    obtain ⟨h, hh, hdiff⟩ := c2slomqnb_exists_wt_ne (hn := hn) (hm := hm) hodd ι hne
    refine ⟨h, hh, ?_⟩
    rw [show η l ((D.nW x)⁻¹ * h * D.nW x) =
        omqPlusWt ι (omqSignedAct π s (u l)) h from
      (omq_omPlus_wt_conj (hn := hn) (m := m) (hm := hm) (ι := ι) hxr hs (u l) hh).2]
    exact hdiff
  have hnorm : ∀ h ∈ D.H, (D.nW x)⁻¹ * h * D.nW x ∈ D.H := fun h hh =>
    (omq_omPlus_wt_conj (hn := hn) (m := m) (hm := hm) (ι := ι) hxr hs να hh).1
  have h4 : 4 ≤ Module.finrank k (LinearMap.range (σ (D.nW x) - 1)) :=
    h2 (k := k) (V := V) σ D.H (D.nW x) hnorm 4 η wVec hwnz hchar hdistinct hmove
  rw [← c2slomqnb_finrank_range_conj σ g' g, ← hxw]
  exact h4

end CFSG.LocalAnalysis.WeakClosure81
