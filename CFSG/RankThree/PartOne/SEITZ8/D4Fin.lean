module

public import CFSG.RankThree.PartOne.SEITZ8.D4Core
public import CFSG.RankThree.PartOne.SEITZ7.D4Close

public section

namespace CFSG.RankThree.PartOne.SEITZ8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.SEITZ7 CFSG.RankThree.PartOne.SEITZ3 CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem

variable {K : Type} [Field K]

section Basic

variable [CharP K 2]

omit [CharP K 2] in
theorem xAB_zero (σ : K →+* K) : xAB σ (0 : K) = 1 := by simp [xAB, xd_zero]

theorem xAB_add (σ : K →+* K) (a b : K) : xAB σ (a + b) = xAB σ a * xAB σ b := by
  have e : ∀ c : K, xAB σ c = xOrbit σ (d4Root 5) c := fun c =>
    (xOrbit_eq σ rho_dict.2.2.2.2.2.1 rho_dict.2.2.2.2.2.2.1 c).symm
  rw [e, e, e]
  exact xOrbit_add σ (isRoot_d4 (by norm_num : 5 < 24)) rho_ne_dict.2.1 a b

theorem xAB_mul_self (σ : K →+* K) (a : K) : xAB σ a * xAB σ a = 1 := by
  rw [← xAB_add, CharTwo.add_self_eq_zero, xAB_zero]

omit [CharP K 2] in
theorem conj_mul3 {G : Type*} [Group G] (n x y z : G) :
    n * (x * y * z) * n⁻¹ = n * x * n⁻¹ * (n * y * n⁻¹) * (n * z * n⁻¹) := by group

omit [CharP K 2] [Field K] in
theorem reflect_AB_check :
    reflect d4 (nd 2) (d4Root 5) = d4Root 0 ∧ reflect d4 (nd 2) (d4Root 7) = d4Root 1 ∧
    reflect d4 (nd 2) (d4Root 9) = d4Root 3 ∧ reflect d4 (nd 2) (d4Root 2) = d4Root 8 := by
  decide +kernel

theorem n0_xAB (σ : K →+* K) (c : K) :
    weylElement d4 K (nd 2) * xAB σ c * (weylElement d4 K (nd 2))⁻¹ = xA σ c := by
  obtain ⟨h5, h7, h9, -⟩ := reflect_AB_check
  unfold xAB xA
  rw [conj_mul3, weylElement_conj_xd (nd 2) (by norm_num) h5,
    weylElement_conj_xd (nd 2) (by norm_num) h7, weylElement_conj_xd (nd 2) (by norm_num) h9]

theorem n0_xB (c : K) :
    weylElement d4 K (nd 2) * xd 2 c * (weylElement d4 K (nd 2))⁻¹ = xd 8 c :=
  weylElement_conj_xd (nd 2) (by norm_num) reflect_AB_check.2.2.2 c

omit [CharP K 2] [Field K] in
theorem cartan_AB_check :
    (∑ j, d4.cartan (nd 2) j * (d4Root 5) j = 1) ∧ (∑ j, d4.cartan (nd 2) j * (d4Root 7) j = 1) ∧
    (∑ j, d4.cartan (nd 2) j * (d4Root 9) j = 1) ∧
    (∑ j, d4.cartan (nd 2) j * (d4Root 12) j = 0) ∧
    (∑ j, d4.cartan (nd 2) j * (d4Root 15) j = 0) ∧
    (∑ j, d4.cartan (nd 2) j * (d4Root 13) j = 0) := by
  decide +kernel

omit [CharP K 2] in
theorem hB_xAB (σ : K →+* K) (t : Kˣ) (ht : σ (t : K) = t) (c : K) :
    torusElement d4 K (nd 2) t * xAB σ c * (torusElement d4 K (nd 2) t)⁻¹ =
      xAB σ ((t : K) * c) := by
  obtain ⟨h5, h7, h9, -⟩ := cartan_AB_check
  have e5 := torusElement_conj_xd (K := K) (nd 2) (p := 5) (by norm_num) t c
  have e7 := torusElement_conj_xd (K := K) (nd 2) (p := 7) (by norm_num) t (σ c)
  have e9 := torusElement_conj_xd (K := K) (nd 2) (p := 9) (by norm_num) t (σ (σ c))
  rw [h5, zpow_one] at e5
  rw [h7, zpow_one] at e7
  rw [h9, zpow_one] at e9
  unfold xAB
  rw [conj_mul3, e5, e7, e9]
  simp only [map_mul, ht]

omit [CharP K 2] in
theorem hB_xAAB (σ : K →+* K) (t : Kˣ) (c : K) :
    torusElement d4 K (nd 2) t * xAAB σ c * (torusElement d4 K (nd 2) t)⁻¹ = xAAB σ c := by
  obtain ⟨-, -, -, h12, h15, h13⟩ := cartan_AB_check
  have e12 := torusElement_conj_xd (K := K) (nd 2) (p := 12) (by norm_num) t c
  have e15 := torusElement_conj_xd (K := K) (nd 2) (p := 15) (by norm_num) t (σ c)
  have e13 := torusElement_conj_xd (K := K) (nd 2) (p := 13) (by norm_num) t (σ (σ c))
  rw [h12, zpow_zero, Units.val_one, one_mul] at e12
  rw [h15, zpow_zero, Units.val_one, one_mul] at e15
  rw [h13, zpow_zero, Units.val_one, one_mul] at e13
  unfold xAAB
  rw [conj_mul3, e12, e15, e13]

theorem conj_xA_xB (σ : K →+* K) (hσ : ∀ c, σ (σ (σ c)) = c) (a d : K) (hd : σ d = d) :
    xA σ a * xB d * (xA σ a)⁻¹ = xB d * xAB σ (d * a) * xAAB σ (d * a * σ a) *
      xN (d * (a * σ a * σ (σ a))) * xH (d ^ 2 * (a * σ a * σ (σ a))) := by
  have h := conj_xB σ hσ (fun n => if n = 1 then a else 0) d hd
  have e : ordT σ (fun n => if n = 1 then a else 0) = xA σ a := by
    simp [ordT, xB, xAB, xAAB, xN, xH, xd_zero]
  rw [e] at h
  simpa using h

end Basic

section Closing


theorem torus_mem (σ : K →+* K) (Hs : Subgroup (adjointGroup d4 K))
    (hup : ∀ c : fixedField σ, xd 2 (c : K) ∈ Hs) (hlo : ∀ c : fixedField σ, xd 8 (c : K) ∈ Hs)
    (ρ : (fixedField σ)ˣ) :
    torusElement d4 K (nd 2) (Units.map (fixedField σ).subtype.toMonoidHom ρ) ∈ Hs := by
  rw [← slLongE_dSL]
  have hcl := CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := fixedField σ)
  have hle : Subgroup.closure (Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Upper
      (fixedField σ)) ∪ Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Lower (fixedField σ))) ≤
        Hs.comap (slLongE σ) := by
    rw [Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · have e : xPar (rootOperatorFamily d4) (Pi.single (nd 2) 1) (c : K) = xd 2 (c : K) := by
        simp only [xd, d4Root_dict.1]
      show slLongE σ (sl2Upper c) ∈ Hs
      rw [slLongE_upper, e]
      exact hup c
    · have e : xPar (rootOperatorFamily d4) (-Pi.single (nd 2) 1) (c : K) = xd 8 (c : K) := by
        simp only [xd, d4Root_dict.2.1]
      show slLongE σ (sl2Lower c) ∈ Hs
      rw [slLongE_lower, e]
      exact hlo c
  have h : dSL ρ ∈ Hs.comap (slLongE σ) := hle (hcl ▸ Subgroup.mem_top _)
  exact h

variable [CharP K 2]

theorem long_closing (σ : K →+* K) (hσ : ∀ c, σ (σ (σ c)) = c) (k : Subfield K)
    (Hs : Subgroup (adjointGroup d4 K)) (hn0 : weylElement d4 K (nd 2) ∈ Hs)
    (hn1 : weylElement d4 K (nd 0) * weylElement d4 K (nd 1) * weylElement d4 K (nd 3) ∈ Hs)
    (hH : ∀ c : K, σ c = c → xH c ∈ Hs) (hA : ∀ a ∈ k, xA σ a ∈ Hs)
    (s : K) (hsσ : σ s = s) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hspan : ∀ x : K, x ∈ AddSubgroup.closure {y | ∃ d : K, σ d = d ∧ ∃ a ∈ k, y = d * a}) :
    (∀ c : K, σ c = c → xB c ∈ Hs) ∧ (∀ a : K, xA σ a ∈ Hs) := by
  have hWt : (Wt : adjointGroup d4 K) ∈ Hs := Hs.mul_mem hn0 hn1
  have hB : ∀ c : K, σ c = c → xB c ∈ Hs := by
    intro c hc
    have h := Wt_xB (K := K) c
    have e : xB c = Wt⁻¹ * xH c * Wt := by
      show xd 2 c = _
      calc xd 2 c = Wt⁻¹ * (Wt * xd 2 c * Wt⁻¹) * Wt := by group
        _ = _ := by rw [h]; rfl
    rw [e]
    exact Hs.mul_mem (Hs.mul_mem (Hs.inv_mem hWt) (hH c hc)) hWt
  have hBm : ∀ c : K, σ c = c → xd 8 c ∈ Hs := by
    intro c hc
    rw [← n0_xB c]
    exact Hs.mul_mem (Hs.mul_mem hn0 (hB c hc)) (Hs.inv_mem hn0)
  have hN : ∀ c : K, σ c = c → xN c ∈ Hs := by
    intro c hc
    have h := nHat1_xN (K := K) c
    rw [nHatE_one] at h
    have e : xN c = (weylElement d4 K (nd 0) * weylElement d4 K (nd 1) *
        weylElement d4 K (nd 3))⁻¹ * xB c * (weylElement d4 K (nd 0) * weylElement d4 K (nd 1) *
          weylElement d4 K (nd 3)) := by
      rw [← h]
      group
    rw [e]
    exact Hs.mul_mem (Hs.mul_mem (Hs.inv_mem hn1) (hB c hc)) hn1
  obtain ⟨ρ, hρ⟩ : ∃ ρ : (fixedField σ)ˣ,
      ((Units.map (fixedField σ).subtype.toMonoidHom ρ : Kˣ) : K) = s :=
    ⟨Units.mk0 ⟨s, hsσ⟩ (fun h => hs0 (congrArg Subtype.val h)), rfl⟩
  set t : Kˣ := Units.map (fixedField σ).subtype.toMonoidHom ρ with ht
  have htσ : σ (t : K) = t := by rw [hρ]; exact hsσ
  have htH : torusElement d4 K (nd 2) t ∈ Hs :=
    torus_mem σ Hs (fun c => hB c c.2) (fun c => hBm c c.2) ρ
  have hE : ∀ d : K, σ d = d → ∀ a ∈ k, xAB σ (d * a) * xAAB σ (d * a * σ a) ∈ Hs := by
    intro d hd a ha
    have hconj := conj_xA_xB σ hσ a d hd
    have hNσ : σ (a * σ a * σ (σ a)) = a * σ a * σ (σ a) := by
      simp only [map_mul, hσ]
      ring
    have h1 : xN (d * (a * σ a * σ (σ a))) ∈ Hs := hN _ (by rw [map_mul, hd, hNσ])
    have h2 : xH (d ^ 2 * (a * σ a * σ (σ a))) ∈ Hs :=
      hH _ (by rw [map_mul, map_pow, hd, hNσ])
    have h3 : xA σ a * xB d * (xA σ a)⁻¹ ∈ Hs :=
      Hs.mul_mem (Hs.mul_mem (hA a ha) (hB d hd)) (Hs.inv_mem (hA a ha))
    have e : xAB σ (d * a) * xAAB σ (d * a * σ a) = (xB d)⁻¹ * (xA σ a * xB d * (xA σ a)⁻¹) *
        (xH (d ^ 2 * (a * σ a * σ (σ a))))⁻¹ * (xN (d * (a * σ a * σ (σ a))))⁻¹ := by
      rw [hconj]
      group
    rw [e]
    exact Hs.mul_mem (Hs.mul_mem (Hs.mul_mem (Hs.inv_mem (hB d hd)) h3) (Hs.inv_mem h2))
      (Hs.inv_mem h1)
  have hs1' : s + 1 ≠ 0 := fun h => hs1 (CharTwo.add_eq_zero.1 h)
  have hAB : ∀ d : K, σ d = d → ∀ a ∈ k, xAB σ (d * a) ∈ Hs := by
    intro d hd a ha
    set d' : K := d / (s + 1) with hd'
    have hd'σ : σ d' = d' := by
      rw [hd', map_div₀, hd, map_add, hsσ, map_one]
    have hE' := hE d' hd'σ a ha
    have hc : torusElement d4 K (nd 2) t * (xAB σ (d' * a) * xAAB σ (d' * a * σ a)) *
        (torusElement d4 K (nd 2) t)⁻¹ = xAB σ (s * (d' * a)) * xAAB σ (d' * a * σ a) := by
      rw [show ∀ n x y : adjointGroup d4 K, n * (x * y) * n⁻¹ = n * x * n⁻¹ * (n * y * n⁻¹) from
        fun n x y => by group, hB_xAB σ t htσ, hB_xAAB σ t, hρ]
    have hmem : torusElement d4 K (nd 2) t * (xAB σ (d' * a) * xAAB σ (d' * a * σ a)) *
        (torusElement d4 K (nd 2) t)⁻¹ ∈ Hs :=
      Hs.mul_mem (Hs.mul_mem htH hE') (Hs.inv_mem htH)
    rw [hc] at hmem
    have hq := Hs.mul_mem hmem (Hs.inv_mem hE')
    have e : xAB σ (s * (d' * a)) * xAAB σ (d' * a * σ a) *
        (xAB σ (d' * a) * xAAB σ (d' * a * σ a))⁻¹ = xAB σ (d * a) := by
      calc _ = xAB σ (s * (d' * a)) * (xAB σ (d' * a))⁻¹ := by group
        _ = xAB σ (s * (d' * a)) * xAB σ (d' * a) := by
          rw [inv_eq_of_mul_eq_one_right (xAB_mul_self σ _)]
        _ = xAB σ (s * (d' * a) + d' * a) := (xAB_add σ _ _).symm
        _ = xAB σ (d * a) := by
          congr 1
          rw [hd']
          field_simp
    rw [e] at hq
    exact hq
  let Ξ : AddSubgroup K :=
    { carrier := {x | xAB σ x ∈ Hs}
      zero_mem' := by
        show xAB σ 0 ∈ Hs
        rw [xAB_zero]
        exact Hs.one_mem
      add_mem' := fun {x y} hx hy => by
        show xAB σ (x + y) ∈ Hs
        rw [xAB_add]
        exact Hs.mul_mem hx hy
      neg_mem' := fun {x} hx => by
        show xAB σ (-x) ∈ Hs
        rw [CharTwo.neg_eq]
        exact hx }
  have hall : ∀ x : K, xAB σ x ∈ Hs := fun x =>
    (AddSubgroup.closure_le Ξ).2 (fun y hy => by
      obtain ⟨d, hd, a, ha, rfl⟩ := hy
      exact hAB d hd a ha) (hspan x)
  refine ⟨hB, fun a => ?_⟩
  rw [← n0_xAB σ a]
  exact Hs.mul_mem (Hs.mul_mem hn0 (hall a)) (Hs.inv_mem hn0)

end Closing

section Final

theorem exists_ne_zero_one {L : Type*} [Field L] [Finite L] (h4 : 4 ∣ Nat.card L) :
    ∃ s : L, s ≠ 0 ∧ s ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have hpos : 0 < Nat.card L := Nat.card_pos
  have h4' : 4 ≤ Nat.card L := Nat.le_of_dvd hpos h4
  have hinj : Function.Injective (fun x : L => decide (x = 0)) := by
    intro x y hxy
    by_cases hx : x = 0
    · by_cases hy : y = 0
      · rw [hx, hy]
      · simp [hx, hy] at hxy
    · by_cases hy : y = 0
      · simp [hx, hy] at hxy
      · rw [hcon x hx, hcon y hy]
  have := Nat.card_le_card_of_injective _ hinj
  simp at this
  omega

variable [CharP K 2] {σ δ : K →+* K}

theorem eq_top_of_long (hσ : ∀ c, σ (σ (σ c)) = c) (k : Subfield K)
    {H : Subgroup (twistedGroup σ)} (hn0 : nHat σ (ng 0) ∈ H) (hn1 : nHat σ (ng 1) ∈ H)
    (hlong : ∀ c : fixedField σ, psiB σ hσ (sl2Upper c) ∈ H)
    (hA : ∀ a ∈ k, slShort σ hσ (sl2Upper a) ∈ H)
    (s : K) (hsσ : σ s = s) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hspan : ∀ x : K, x ∈ AddSubgroup.closure {y | ∃ e : K, σ e = e ∧ ∃ a ∈ k, y = e * a}) :
    H = ⊤ := by
  set Hs : Subgroup (adjointGroup d4 K) := H.map (twistedGroup σ).subtype with hHs
  have hS : ∀ y : twistedGroup σ, (y : adjointGroup d4 K) ∈ Hs ↔ y ∈ H := fun y =>
    Subgroup.mem_map_iff_mem (twistedGroup σ).subtype_injective
  have hn0' : weylElement d4 K (nd 2) ∈ Hs := by
    have := (hS _).2 hn0
    rwa [nHat_val, nHatE_zero] at this
  have hn1' : weylElement d4 K (nd 0) * weylElement d4 K (nd 1) * weylElement d4 K (nd 3) ∈ Hs := by
    have := (hS _).2 hn1
    rwa [nHat_val, nHatE_one] at this
  have hH : ∀ c : K, σ c = c → xH c ∈ Hs := fun c hc => by
    have := (hS _).2 (hlong ⟨c, hc⟩)
    rwa [psiB_upper σ hσ ⟨c, hc⟩] at this
  have hA' : ∀ a ∈ k, xA σ a ∈ Hs := fun a ha => by
    have := (hS _).2 (hA a ha)
    rwa [slShort_upper_xA σ hσ a] at this
  obtain ⟨hB, hAall⟩ := long_closing σ hσ k Hs hn0' hn1' hH hA' s hsσ hs0 hs1 hspan
  apply eq_top_of_simple_tw hσ hn0 hn1
  · intro y hy
    have hy' : (y : adjointGroup d4 K) ∈ twistedRootSubgroupD4 σ (rt 0) := by
      rw [rt0_single]
      exact Subgroup.mem_subgroupOf.1 hy
    obtain ⟨c, hcσ, hyc⟩ := (mem_XB hσ _).1 hy'
    rw [← hS, hyc]
    exact hB c hcσ
  · intro y hy
    have hy' : (y : adjointGroup d4 K) ∈ twistedRootSubgroupD4 σ (rt 1) := by
      rw [rt1_single]
      exact Subgroup.mem_subgroupOf.1 hy
    obtain ⟨a, hya⟩ := (mem_XA hσ _).1 hy'
    rw [← hS, hya]
    exact hAall a

variable [Finite K]
  {k : Subfield K}
  {F0 : Subfield (fixedField σ)} {d q : ℕ}

theorem closure_eq_top (S : D4Setup σ δ k F0 d q) (g : twistedGroup σ) (hg : g ∉ Rg σ δ) :
    Subgroup.closure ((Rg σ δ : Set (twistedGroup σ)) ∪
      (((Rg σ δ).map (MulAut.conj g).toMonoidHom : Subgroup (twistedGroup σ)) :
        Set (twistedGroup σ))) = ⊤ := by
  set H : Subgroup (twistedGroup σ) := Subgroup.closure ((Rg σ δ : Set (twistedGroup σ)) ∪
    (((Rg σ δ).map (MulAut.conj g).toMonoidHom : Subgroup (twistedGroup σ)) :
      Set (twistedGroup σ))) with hH
  have hRH : Rg σ δ ≤ H := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hSp := spanHyp_Rδ S.hσ3 S.hcomm S.hfix S.rat
  have hn0 : nHat σ (ng 0) ∈ H := hRH (by
    rw [mem_Rg, nHat_val, nHatE_zero]
    exact hSp.n0.2)
  have hn1 : nHat σ (ng 1) ∈ H := hRH (by
    rw [mem_Rg, nHat_val, nHatE_one]
    exact hSp.n1.2)
  have hA : ∀ a ∈ k, slShort σ S.hσ3 (sl2Upper a) ∈ H := fun a ha => hRH (by
    rw [mem_Rg, slShort_upper_xA σ S.hσ3 a]
    exact (hSp.A a ha).2)
  obtain ⟨s, hs0, hs1⟩ := exists_ne_zero_one (L := F0) S.four
  exact eq_top_of_long S.hσ3 k hn0 hn1 (long_full S g hg) hA ((s : fixedField σ) : K)
    (s : fixedField σ).2 (fun h => hs0 (Subtype.ext (Subtype.ext h)))
    (fun h => hs1 (Subtype.ext (Subtype.ext h))) S.span

end Final

end CFSG.RankThree.PartOne.SEITZ8
