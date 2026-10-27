module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteXviiFinal
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCalcNF

public section

namespace CFSG.Quasithin.Fan86.Tutte.Seven

variable {H : Type*} [Group H] {r l ξ : H} {Hs : ℕ → Subgroup H}

section Basic

variable (h : IsTutteSys 7 r l ξ Hs) (habel : Abel Hs 4)
include h habel

theorem sq4 {k : ℤ} (hk1 : 1 ≤ k) (hk : k ≤ 4) : tx r l k * tx r l k = 1 := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ k)
  have := abel_sq_eq_one h (i := 4) (k := n) (by norm_num) habel (by omega) (by omega)
  rwa [pow_two] at this

theorem inv4 {k : ℤ} (hk1 : 1 ≤ k) (hk : k ≤ 4) : (tx r l k)⁻¹ = tx r l k :=
  inv_eq_of_mul_eq_one_right (sq4 h habel hk1 hk)

theorem comm4 {a b : ℤ} (ha1 : 1 ≤ a) (ha : a ≤ 4) (hb1 : 1 ≤ b) (hb : b ≤ 4) :
    tx r l a * tx r l b = tx r l b * tx r l a := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ a)
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ b)
  exact Xvii.tx_comm h (by norm_num) habel (by omega) (by omega)

omit habel in
theorem mem5 {k : ℤ} (hk1 : 1 ≤ k) (hk : k ≤ 5) : tx r l k ∈ Hs 5 :=
  tx_int_mem h (by norm_num) hk1 hk

end Basic

theorem x5_sq (h : IsTutteSys 7 r l ξ Hs) (habel : Abel Hs 4) (hnab : ¬ Abel Hs 5) :
    tx r l 5 * tx r l 5 = tx r l 2 * tx r l 3 := by
  have B := xviiInput h
  have hab : Abel Hs (5 - 1) := habel
  have hz2ne := Xvii.sq_ne_one B (i := 5) (by norm_num) (by norm_num) hab hnab
  obtain ⟨T, hTsub, hTz, hTeven, hTsym⟩ := B.sq_support (i := 5) (by norm_num) (by norm_num) hab
  have hTne : T.Nonempty := by
    rcases T.eq_empty_or_nonempty with h0 | h0
    · exfalso
      apply hz2ne
      rw [← pow_two, hTz, h0]
      exact Xvii.pset_empty
    · exact h0
  have hmT : T.min' hTne ∈ T := Finset.min'_mem T hTne
  have hmle : ∀ t ∈ T, T.min' hTne ≤ t := fun t ht => Finset.min'_le T t ht
  obtain ⟨hm1, hm2⟩ := Xvii.xvii_support h B (i := 5) (by norm_num) (by norm_num) hab hnab hTsub
    hTz hTeven hTsym hmT hmle
  have hm : T.min' hTne = 2 := by omega
  have hT23 : T = {2, 3} := by
    ext t
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro ht
      have h1 := hmle t ht
      have h2 := Finset.mem_Icc.1 (hTsub ht)
      have h4 := hmle _ (hTsym t ht)
      omega
    · rintro (rfl | rfl)
      · rw [← hm]
        exact hmT
      · have := hTsym 2 (hm ▸ hmT)
        simpa using this
  have hp : pset r l ({2, 3} : Finset ℕ) = tx r l 2 * tx r l 3 := by
    have h1 := Xvii.pset_insert B (n := 4) (by norm_num) habel (a := 2) (U := {3}) (by simp)
      (by simp) (by simp)
    rw [h1, Xvii.pset_singleton]
    simp
  have : tx r l 5 * tx r l 5 = pset r l T := by
    have := hTz
    rw [pow_two] at this
    simpa using this
  rw [this, hT23, hp]

theorem alg_main {G : Type*} [Group G] {a1 a2 a3 a4 a5 : G} (h11 : a1 * a1 = 1)
    (h22 : a2 * a2 = 1) (h33 : a3 * a3 = 1) (h44 : a4 * a4 = 1) (c24 : a2 * a4 = a4 * a2)
    (c34 : a3 * a4 = a4 * a3) (h5 : a5 * a5 = a2 * a3) :
    a5⁻¹ * a1 = a5 * (a3⁻¹ * (a2 * a1⁻¹)) ∧
      a5⁻¹ * (a4 * (a2⁻¹ * a1)) = a5 * (a4⁻¹ * (a3 * a1⁻¹)) := by
  have i1 : a1⁻¹ = a1 := inv_eq_of_mul_eq_one_right h11
  have i2 : a2⁻¹ = a2 := inv_eq_of_mul_eq_one_right h22
  have i3 : a3⁻¹ = a3 := inv_eq_of_mul_eq_one_right h33
  have i4 : a4⁻¹ = a4 := inv_eq_of_mul_eq_one_right h44
  have i5 : a5⁻¹ = a5 * a3 * a2 := by
    calc a5⁻¹ = a5 * (a5 * a5)⁻¹ := by group
      _ = a5 * (a2 * a3)⁻¹ := by rw [h5]
      _ = a5 * a3 * a2 := by rw [mul_inv_rev, i3, i2]; group
  rw [i5, i3, i2, i1, i4]
  refine ⟨by group, ?_⟩
  calc a5 * a3 * a2 * (a4 * (a2 * a1)) = a5 * (a3 * (a2 * a4) * (a2 * a1)) := by group
    _ = a5 * (a3 * (a4 * a2) * (a2 * a1)) := by rw [c24]
    _ = a5 * (a3 * a4 * (a2 * a2) * a1) := by group
    _ = a5 * (a3 * a4 * 1 * a1) := by rw [h22]
    _ = a5 * (a3 * a4 * a1) := by group
    _ = a5 * (a4 * a3 * a1) := by rw [c34]
    _ = a5 * (a4 * (a3 * a1)) := by group

theorem words (h : IsTutteSys 7 r l ξ Hs) (habel : Abel Hs 4) (hnab : ¬ Abel Hs 5) :
    nfw r l (-1) [4, 2] = nfw r l 1 [4, 2] ∧
    nfw r l (-1) [5, 1] = nfw r l 1 [5, 3, 2, 1] ∧
    nfw r l (-1) [5, 4, 2, 1] = nfw r l 1 [5, 4, 3, 1] := by
  have h24 := comm4 h habel (a := 2) (b := 4) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have h34 := comm4 h habel (a := 3) (b := 4) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have hm := alg_main (sq4 h habel (k := 1) (by norm_num) (by norm_num))
    (sq4 h habel (k := 2) (by norm_num) (by norm_num))
    (sq4 h habel (k := 3) (by norm_num) (by norm_num))
    (sq4 h habel (k := 4) (by norm_num) (by norm_num)) h24 h34 (x5_sq h habel hnab)
  have i2 := inv4 h habel (k := 2) (by norm_num) (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · simp [nfw, inv4 h habel (k := 4) (by norm_num) (by norm_num), i2]
  · simpa [nfw] using hm.1
  · simpa [nfw] using hm.2

theorem conj_alg {G : Type*} [Group G] {x a c : G} (haa : a * a = 1)
    (hA : x * (a * (x * a)) = c) : x * a * x = c * a := by
  calc x * a * x = x * a * x * (a * a) := by rw [haa, mul_one]
    _ = (x * (a * (x * a))) * a := by group
    _ = c * a := by rw [hA]

theorem shift_rel (K : List ℤ) (hK : Even K.length)
    (hrel : tx r l 6 * tx r l 6 = nfw r l 1 K) :
    tx r l 7 * ((tx r l 1)⁻¹ * (tx r l 7 * (tx r l 1)⁻¹)) = nfw r l 1 (K.map (· + 1)) := by
  have e1 := nfw_shift_l r l 1 [6, 0, 6, 0] ⟨2, rfl⟩
  have e2 := nfw_shift_l r l 1 K hK
  have e3 : nfw r l 1 [6, 0, 6, 0] = tx r l 6 * tx r l 6 := by simp [nfw, tx_zero]
  rw [e3, hrel, e2] at e1
  have e4 : nfw r l 1 ([6, 0, 6, 0].map (· + 1)) =
      tx r l 7 * ((tx r l 1)⁻¹ * (tx r l 7 * (tx r l 1)⁻¹)) := by simp [nfw]
  rw [e4] at e1
  exact e1.symm

theorem caseA (h : IsTutteSys 7 r l ξ Hs) (habel : Abel Hs 4)
    (hcl : tx r l 6 * tx r l 6 = 1 ∨ tx r l 6 * tx r l 6 = tx r l 4 * tx r l 2) :
    ∃ d ∈ Hs 5, tx r l 7 * tx r l 1 * tx r l 7 = d := by
  have i1 := inv4 h habel (k := 1) (by norm_num) (by norm_num)
  have h11 := sq4 h habel (k := 1) (by norm_num) (by norm_num)
  have m1 := mem5 h (k := 1) (by norm_num) (by norm_num)
  rcases hcl with hc | hc
  · have := shift_rel (K := []) (by simp) (by simpa [nfw] using hc)
    simp only [List.map_nil, nfw, i1] at this
    exact ⟨tx r l 1, m1, by simpa using conj_alg h11 this⟩
  · have hrel : tx r l 6 * tx r l 6 = nfw r l 1 [4, 2] := by
      rw [hc]
      simp [nfw, inv4 h habel (k := 2) (by norm_num) (by norm_num)]
    have := shift_rel (K := [4, 2]) (by simp) hrel
    simp only [List.map_cons, List.map_nil, nfw, i1] at this
    have e := conj_alg h11 (by simpa using this)
    refine ⟨tx r l 5 * (tx r l 3)⁻¹ * tx r l 1, ?_, by simpa using e⟩
    exact (Hs 5).mul_mem ((Hs 5).mul_mem (mem5 h (k := 5) (by norm_num) (by norm_num))
      ((Hs 5).inv_mem (mem5 h (k := 3) (by norm_num) (by norm_num)))) m1

end CFSG.Quasithin.Fan86.Tutte.Seven
