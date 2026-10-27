module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocConj
public import CFSG.Sporadic.J4.QT2LocCntMainBase
public import CFSG.Sporadic.J4.QT2LocProof
public import CFSG.Sporadic.J4.QT2LocUniqCheck

public section

namespace CFSG.Quasithin.J4Loc

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

@[expose] def Ig (g : J) : Set J := {x | x ∈ Eg uJ 11 ∧ g⁻¹ * x * g ∈ Eg uJ 11}

section Inter

variable (hM : MatFacts)
include hM

theorem conj_pathElt_eta {ℓ : ℕ}
    (hℓ : ℓ < 7) {c c'' : ℕ}
    (h : eqRows (mulRows (mulRows (pathRows (repPaths.getD ℓ []))
        (etaRows (uTab (locMats ()) (locInvs ())) 11 c))
        (invRows (pathRows (repPaths.getD ℓ [])))) (etaRows (uTab (locMats ()) (locInvs ())) 11 c'')
        = true) :
    pathElt (repPaths.getD ℓ []) * eta uJ 11 c * (pathElt (repPaths.getD ℓ []))⁻¹ =
      eta uJ 11 c'' := by
  apply Mx_injective
  set M := pathRows (repPaths.getD ℓ []) with hMdef
  set Mi := invRows M with hMidef
  have hinv := pathInv_get hℓ
  have hMx : Mx (pathElt (repPaths.getD ℓ [])) = rowsMatrix M :=
    Mx_pathElt hM _ (repPaths_letters ℓ hℓ)
  have h1 : rowsMatrix M * rowsMatrix Mi = 1 := by
    have := congrArg rowsMatrix (eqRows_iff.1 hinv)
    rwa [rowsMatrix_mulRows, rowsMatrix_idRows] at this
  have hMxi : Mx (pathElt (repPaths.getD ℓ []))⁻¹ = rowsMatrix Mi := by
    have h2 : Mx (pathElt (repPaths.getD ℓ []))⁻¹ * Mx (pathElt (repPaths.getD ℓ [])) = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    calc Mx (pathElt (repPaths.getD ℓ []))⁻¹
        = Mx (pathElt (repPaths.getD ℓ []))⁻¹ * (rowsMatrix M * rowsMatrix Mi) := by
          rw [h1, mul_one]
      _ = (Mx (pathElt (repPaths.getD ℓ []))⁻¹ * Mx (pathElt (repPaths.getD ℓ []))) *
          rowsMatrix Mi := by rw [hMx, mul_assoc]
      _ = rowsMatrix Mi := by rw [h2, one_mul]
  rw [map_mul, map_mul, hMx, hMxi, Mx_eta hM 11 le_rfl c, Mx_eta hM 11 le_rfl c'',
    ← rowsMatrix_mulRows, ← rowsMatrix_mulRows, eqRows_iff.1 h]

theorem conj_i5Pairs :
    ∀ p ∈ i5Pairs, pathElt (repPaths.getD 5 []) * eta uJ 11 p.1 *
      (pathElt (repPaths.getD 5 []))⁻¹ = eta uJ 11 p.2 := by
  set u := pathElt (repPaths.getD 5 [])
  have hg : ∀ p ∈ ([(965, 1243), (1979, 1979), (165, 165)] : List (ℕ × ℕ)),
      u * eta uJ 11 p.1 * u⁻¹ = eta uJ 11 p.2 := fun p hp =>
    conj_pathElt_eta hM (by norm_num) (eqRows_iff.2 (i5_prop.1 p hp))
  have hxor : ∀ {a a' b b' : ℕ}, u * eta uJ 11 a * u⁻¹ = eta uJ 11 a' →
      u * eta uJ 11 b * u⁻¹ = eta uJ 11 b' → u * eta uJ 11 (a ^^^ b) * u⁻¹ =
        eta uJ 11 (a' ^^^ b') := by
    intro a a' b b' ha hb
    rw [← eta_mul_eta hM, ← eta_mul_eta hM, ← ha, ← hb]
    group
  have g0 : u * eta uJ 11 965 * u⁻¹ = eta uJ 11 1243 := hg (965, 1243) (by simp)
  have g1 : u * eta uJ 11 1979 * u⁻¹ = eta uJ 11 1979 := hg (1979, 1979) (by simp)
  have g2 : u * eta uJ 11 165 * u⁻¹ = eta uJ 11 165 := hg (165, 165) (by simp)
  intro p hp
  simp only [i5Pairs, List.mem_cons, List.not_mem_nil, or_false] at hp
  have x1 : (965 ^^^ 1979 ^^^ 165 : ℕ) = 1243 := by decide
  have x2 : (1243 ^^^ 1979 ^^^ 165 : ℕ) = 965 := by decide
  have x3 : (965 ^^^ 165 : ℕ) = 864 := by decide
  have x4 : (1243 ^^^ 165 : ℕ) = 1150 := by decide
  have x5 : (1979 ^^^ 165 : ℕ) = 1822 := by decide
  have x6 : (965 ^^^ 1979 : ℕ) = 1150 := by decide
  have x7 : (1243 ^^^ 1979 : ℕ) = 864 := by decide
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact g0
  · exact g1
  · have e := hxor (hxor g0 g1) g2
    rwa [x1, x2] at e
  · exact g2
  · have e := hxor g0 g2
    rwa [x3, x4] at e
  · have e := hxor g1 g2
    rwa [x5] at e
  · have e := hxor g0 g1
    rwa [x6, x7] at e

omit hM in
theorem candZ_nodup (ℓ : ℕ) :
    (candZ (locMats ()) (locInvs ()) ℓ).Nodup := by
  unfold candZ
  exact nodup_zMasks.filter _

omit hM in
theorem inter_trio
    (hF : J4Facts) {g : J} (hg : g ∉ Hj) :
    (Ig g).ncard ≤ 2 ∨ ∃ W ∈ trioL, ∀ c < 2048, (eta uJ 11 c ∈ Ig g ↔ c ∈ W) := by
  have hM := hF.mat
  obtain ⟨ℓ, hℓ, h, hh, h', hh', rfl⟩ := exists_rep hF g
  have hℓ0 : ℓ ≠ 0 := by
    rintro rfl
    apply hg
    have : pathElt (repPaths.getD 0 []) = 1 := by simp [repPaths, pathElt]
    rw [this]
    simpa using Hj.mul_mem hh hh'
  have hℓ1 : 1 ≤ ℓ := Nat.pos_of_ne_zero hℓ0
  have hℓ6 : ℓ ≤ 6 := by omega
  obtain ⟨u, hu⟩ : ∃ u : J, u = pathElt (repPaths.getD ℓ []) := ⟨_, rfl⟩
  rw [← hu]
  have F1 : ∀ x : J, x ∈ Ig (h * u⁻¹ * h') ↔
      (h⁻¹ * x * h ∈ Eg uJ 11 ∧ u * (h⁻¹ * x * h) * u⁻¹ ∈ Eg uJ 11) := by
    intro x
    constructor
    · rintro ⟨hxE, hxg⟩
      have hx' : h⁻¹ * x * h ∈ Eg uJ 11 := by
        have := Hj_normalizes_Eg hM h⁻¹ (Hj.inv_mem hh) x hxE
        rwa [inv_inv] at this
      refine ⟨hx', ?_⟩
      have e : u * (h⁻¹ * x * h) * u⁻¹ =
          h' * ((h * u⁻¹ * h')⁻¹ * x * (h * u⁻¹ * h')) * h'⁻¹ := by group
      rw [e]
      exact Hj_normalizes_Eg hM h' hh' _ hxg
    · rintro ⟨hy, hy'⟩
      refine ⟨?_, ?_⟩
      · have := Hj_normalizes_Eg hM h hh _ hy
        have e : h * (h⁻¹ * x * h) * h⁻¹ = x := by group
        rwa [e] at this
      · have e : (h * u⁻¹ * h')⁻¹ * x * (h * u⁻¹ * h') =
            h'⁻¹ * (u * (h⁻¹ * x * h) * u⁻¹) * h' := by group
        rw [e]
        have := Hj_normalizes_Eg hM h'⁻¹ (Hj.inv_mem hh') _ hy'
        rwa [inv_inv] at this
  have F2 : ∀ y ∈ Eg uJ 11, u * y * u⁻¹ ∈ Eg uJ 11 →
      y = 1 ∨ ∃ c ∈ candZ (locMats ()) (locInvs ()) ℓ, c < 2048 ∧ y = eta uJ 11 c := by
    intro y hy hy'
    obtain ⟨c, hcl, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hy
    by_cases hc0 : c = 0
    · left
      rw [hc0, eta_zero]
    · right
      rcases mask_cover c hcl with h0 | hT | hZ
      · exact absurd h0 hc0
      · exfalso
        rw [hu] at hy'
        exact not_mem_Eg_conj hM hℓ1 hℓ6 ⟨c, hT, rfl⟩ hy'
      · refine ⟨c, ?_, hcl, rfl⟩
        unfold candZ
        rw [List.mem_filter]
        refine ⟨hZ, memEVec_of_mem hM hℓ (pathInv_get hℓ) ?_⟩
        rw [hu] at hy'
        exact hy'
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := cands_parts
  have hsmall : ∀ x ∈ Ig (h * u⁻¹ * h'), x = 1 ∨ ∃ c ∈ candZ (locMats ()) (locInvs ()) ℓ,
      x = h * eta uJ 11 c * h⁻¹ := by
    intro x hx
    obtain ⟨hy, hy'⟩ := (F1 x).1 hx
    rcases F2 _ hy hy' with h1 | ⟨c, hc, -, h1⟩
    · left
      have : x = h * (h⁻¹ * x * h) * h⁻¹ := by group
      rw [this, h1]
      group
    · right
      refine ⟨c, hc, ?_⟩
      have : x = h * (h⁻¹ * x * h) * h⁻¹ := by group
      rw [this, h1]
  have hcases : ℓ = 1 ∨ ℓ = 2 ∨ ℓ = 3 ∨ ℓ = 4 ∨ ℓ = 5 ∨ ℓ = 6 := by omega
  have hempty : (candZ (locMats ()) (locInvs ()) ℓ).length = 0 → (Ig (h * u⁻¹ * h')).ncard ≤ 2 := by
    intro hlen
    have hnil : candZ (locMats ()) (locInvs ()) ℓ = [] := List.length_eq_zero_iff.1 hlen
    have hsub : Ig (h * u⁻¹ * h') ⊆ {1} := by
      intro x hx
      rcases hsmall x hx with h1 | ⟨c, hc, -⟩
      · exact h1
      · rw [hnil] at hc
        exact absurd hc (by simp)
    calc (Ig (h * u⁻¹ * h')).ncard ≤ ({1} : Set J).ncard :=
          Set.ncard_le_ncard hsub (Set.finite_singleton _)
      _ = 1 := Set.ncard_singleton _
      _ ≤ 2 := by norm_num
  have hone : (candZ (locMats ()) (locInvs ()) ℓ).length = 1 → (Ig (h * u⁻¹ * h')).ncard ≤ 2 := by
    intro hlen
    obtain ⟨c0, hc0⟩ := List.length_eq_one_iff.1 hlen
    have hsub : Ig (h * u⁻¹ * h') ⊆ {1, h * eta uJ 11 c0 * h⁻¹} := by
      intro x hx
      rcases hsmall x hx with h1 | ⟨c, hc, h1⟩
      · exact Or.inl h1
      · rw [hc0] at hc
        have : c = c0 := by simpa using hc
        subst this
        exact Or.inr h1
    calc (Ig (h * u⁻¹ * h')).ncard ≤ ({1, h * eta uJ 11 c0 * h⁻¹} : Set J).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ ({h * eta uJ 11 c0 * h⁻¹} : Set J).ncard + 1 := Set.ncard_insert_le _ _
      _ = 2 := by rw [Set.ncard_singleton]
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (hempty c1)
  · exact Or.inl (hempty c2)
  · exact Or.inl (hempty c3)
  · exact Or.inl (hempty c4)
  · right
    have hi5c := i5_prop.2
    have hi5b : (i5Pairs.map Prod.fst).Nodup := by decide
    have h5 : ∀ p ∈ i5Pairs, u * eta uJ 11 p.1 * u⁻¹ = eta uJ 11 p.2 := by
      rw [hu]
      exact conj_i5Pairs hM
    have hL5 : ∀ p ∈ i5Pairs, p.1 ∈ candZ (locMats ()) (locInvs ()) 5 := by
      intro p hp
      have hpb : ∀ p ∈ i5Pairs, 0 < p.1 ∧ p.1 < 2048 := by decide
      obtain ⟨hp0, hp1⟩ := hpb p hp
      have hmem : eta uJ 11 p.1 ∈ Eg uJ 11 := eta_mem_Eg 11 le_rfl _
      have hmem2 : u * eta uJ 11 p.1 * u⁻¹ ∈ Eg uJ 11 := by
        rw [h5 p hp]
        exact eta_mem_Eg 11 le_rfl _
      rcases F2 _ hmem hmem2 with h1 | ⟨c, hc, hc2, h1⟩
      · exfalso
        have := eta_inj' hM hp1 (by norm_num : 0 < 2048) (h1.trans (eta_zero _ _).symm)
        omega
      · have := eta_inj' hM hp1 hc2 h1
        rw [this]
        exact hc
    have hlen7 : (i5Pairs.map Prod.fst).length = 7 := by simp [i5Pairs]
    have hLsub : (i5Pairs.map Prod.fst).toFinset ⊆
        (candZ (locMats ()) (locInvs ()) 5).toFinset := by
      intro c hc
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hc)
      exact List.mem_toFinset.2 (hL5 p hp)
    have hLeq : (i5Pairs.map Prod.fst).toFinset = (candZ (locMats ()) (locInvs ()) 5).toFinset := by
      refine Finset.eq_of_subset_of_card_le hLsub ?_
      rw [List.toFinset_card_of_nodup (candZ_nodup 5), List.toFinset_card_of_nodup hi5b, c5, hlen7]
    have hcandL : ∀ c ∈ candZ (locMats ()) (locInvs ()) 5, c ∈ i5Pairs.map Prod.fst := by
      intro c hc
      have : c ∈ (candZ (locMats ()) (locInvs ()) 5).toFinset := List.mem_toFinset.2 hc
      rw [← hLeq] at this
      exact List.mem_toFinset.1 this
    have hmask : ∀ c, c ∈ i5Masks ↔ c = 0 ∨ c ∈ i5Pairs.map Prod.fst := by
      intro c
      simp only [i5Masks, mem_srt, List.mem_cons]
    obtain ⟨W', hW'trio, hImg⟩ := (trio_conj hM hh).1 i5Masks hi5c
    refine ⟨W', hW'trio, fun c' hc' => ?_⟩
    rw [Img_iff hM hW'trio hImg hc']
    constructor
    · intro hx
      rcases hsmall _ hx with h1 | ⟨c, hc, h1⟩
      · refine ⟨0, (hmask 0).2 (Or.inl rfl), ?_⟩
        rw [h1, eta_zero]
        group
      · exact ⟨c, (hmask c).2 (Or.inr (hcandL c hc)), h1.symm⟩
    · rintro ⟨c, hc, e⟩
      rcases (hmask c).1 hc with rfl | hcL
      · rw [eta_zero] at e
        have e' : eta uJ 11 c' = 1 := by rw [← e]; group
        rw [e']
        refine (F1 1).2 ⟨?_, ?_⟩
        · rw [show h⁻¹ * 1 * h = 1 by group]
          exact Eg uJ 11 |>.one_mem
        · rw [show u * (h⁻¹ * 1 * h) * u⁻¹ = 1 by group]
          exact Eg uJ 11 |>.one_mem
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hcL
        refine (F1 _).2 ⟨?_, ?_⟩
        · have : h⁻¹ * eta uJ 11 c' * h = eta uJ 11 p.1 := by
            rw [← e]; group
          rw [this]
          exact eta_mem_Eg 11 le_rfl _
        · have : h⁻¹ * eta uJ 11 c' * h = eta uJ 11 p.1 := by
            rw [← e]; group
          rw [this, h5 p hp]
          exact eta_mem_Eg 11 le_rfl _
  · exact Or.inl (hone c6)

end Inter

end CFSG.Quasithin.J4Loc
