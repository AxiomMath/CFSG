module

public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenCoherent
public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenFrame
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorusForms

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType

namespace RelDNs

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent CFSG.Open

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V}

theorem charSum_aniso_plane [Finite V] {U : Submodule F V}
    (hU : PolarNondegOn Q U) (hdim : Module.finrank F U = 2)
    (hani : ∀ v ∈ U, Q v = 0 → v = 0) :
    OrdPNsOm.charSum Q U = -(Nat.card F : ℤ) := by
  classical
  have hU' : SUTB.NondegOn (QuadraticMap.polarBilin Q) U := by
    intro m hm h
    refine hU m hm fun n hn => ?_
    have h' := h n hn
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm] at h'
    exact h'
  obtain ⟨c₀, hc₀⟩ := OrdPNsOm.exists_not_mem_range_wp (K := F)
  obtain ⟨τ, a, b, ha, hb, hF, hS⟩ := OrdPNsOm.exists_frame_plane (Q := Q) hc₀ hU' hdim
  have hτ : τ = true := by
    by_contra h
    rw [Bool.not_eq_true] at h
    subst h
    have hQa : Q a = 0 := by simpa using hF.qa
    have ha0 : a ≠ 0 := by
      intro h0
      have hpab : QuadraticMap.polar Q a b = 1 := hF.pab
      rw [h0] at hpab
      simp [QuadraticMap.polar] at hpab
    exact ha0 (hani a ha hQa)
  subst hτ
  rw [hS]
  simp [OrdPNsOm.tailSum]

theorem charSum_biSup {m : ℕ} {U : Fin m → Submodule F V} (hF : IsPlaneSystem Q U)
    (s : Finset (Fin m)) :
    OrdPNsOm.charSum Q (⨆ j ∈ s, U j) = ∏ j ∈ s, OrdPNsOm.charSum Q (U j) := by
  classical
  haveI : Finite V := Module.finite_of_finite F
  induction s using Finset.induction_on with
  | empty =>
    have hbot : (⨆ j ∈ (∅ : Finset (Fin m)), U j) = ⊥ := by simp
    rw [hbot, OrthTorus.charSum_bot]
    simp
  | insert a s ha ih =>
    rw [Finset.iSup_insert, Finset.prod_insert ha, OrdPNsOm.charSum_sup]
    · rw [ih]
    · exact disjoint_iff.mp (hF.disjoint_biSup ha)
    · intro x hx y hy
      exact mem_polarPerp_iff.1 (hF.biSup_le_polarPerp ha hy) x hx

theorem charSum_iSup_eq_neg_pow {k : ℕ} {U : Fin k → Submodule F V} (hF : IsPlaneSystem Q U) :
    OrdPNsOm.charSum Q (⨆ j, U j) = (-(Nat.card F : ℤ)) ^ k := by
  classical
  haveI : Finite V := Module.finite_of_finite F
  have huniv : (⨆ j : Fin k, U j) = ⨆ j ∈ (Finset.univ : Finset (Fin k)), U j := by
    apply le_antisymm
    · refine iSup_le fun j => ?_
      exact le_iSup_of_le j (le_iSup_of_le (Finset.mem_univ j) le_rfl)
    · exact iSup₂_le fun j _ => le_iSup U j
  rw [huniv, charSum_biSup hF Finset.univ]
  have hnd : ∀ j, PolarNondegOn Q (U j) := by
    intro j x hx h0
    have hzero : (⟨x, hx⟩ : U j) = 0 :=
      (hF.nondeg j).1 ⟨x, hx⟩ fun y => by
        rw [QuadraticMap.polarBilin_apply_apply, polar_comp_subtype_cent]
        exact h0 y y.2
    exact congrArg Subtype.val hzero
  have hani : ∀ j, ∀ v ∈ U j, Q v = 0 → v = 0 := by
    intro j v hv hQv
    by_contra hv0
    refine hF.not_isPlusType j ⟨Submodule.span F {⟨v, hv⟩}, ?_, ?_⟩
    · rw [finrank_span_singleton
        (show (⟨v, hv⟩ : U j) ≠ 0 from fun h => hv0 (congrArg Subtype.val h)), hF.finrank_eq j]
    · rintro y hy
      rw [Submodule.mem_span_singleton] at hy
      obtain ⟨a, rfl⟩ := hy
      change Q (a • v) = 0
      rw [QuadraticMap.map_smul, hQv, smul_zero]
  calc ∏ j ∈ (Finset.univ : Finset (Fin k)), OrdPNsOm.charSum Q (U j)
      = ∏ _j ∈ (Finset.univ : Finset (Fin k)), (-(Nat.card F : ℤ)) :=
        Finset.prod_congr rfl fun j _ => charSum_aniso_plane (hnd j) (hF.finrank_eq j) (hani j)
    _ = (-(Nat.card F : ℤ)) ^ k := by simp

theorem isPlaneSystem_reindex {m k : ℕ} {U : Fin m → Submodule F V} (hF : IsPlaneSystem Q U)
    (φ : Fin k ≃ Fin m) : IsPlaneSystem Q (fun j => U (φ j)) where
  finrank_eq j := hF.finrank_eq (φ j)
  nondeg j := hF.nondeg (φ j)
  not_isPlusType j := hF.not_isPlusType (φ j)
  perp i j hij := hF.perp (φ i) (φ j) fun h => hij (φ.injective h)

theorem isPlaneFrame_reindex {m k p : ℕ} {U : Fin m → Submodule F V}
    {e : Fin m → ↥(orthDerived Q)} {E : Subgroup ↥(orthDerived Q)}
    (hF : IsPlaneFrame Q p U e E) (φ : Fin k ≃ Fin m) :
    IsPlaneFrame Q p (fun j => U (φ j)) (fun j => e (φ j)) E where
  toIsPlaneSystem := isPlaneSystem_reindex hF.toIsPlaneSystem φ
  orderOf_eq j := hF.orderOf_eq (φ j)
  apply_of_perp j x hx := hF.apply_of_perp (φ j) x hx
  maps_to j x hx := hF.maps_to (φ j) x hx
  eq_zero_of_apply_eq j x hx h := hF.eq_zero_of_apply_eq (φ j) x hx h
  isElemAbelian := hF.isElemAbelian
  closure_eq := by
    have hrange : Set.range (fun j => e (φ j)) = Set.range e := by
      ext g
      simp only [Set.mem_range]
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨φ j, rfl⟩
      · rintro ⟨j, rfl⟩
        exact ⟨φ.symm j, by rw [φ.apply_symm_apply]⟩
    rw [hrange, hF.closure_eq]

theorem exists_relFrame (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) {ℓ : ℕ}
    (hdim : Module.finrank F V = 2 * ℓ) (hℓ : 4 ≤ ℓ)
    (hS : OrdPNsOm.charSum Q ⊤ ≠ (-(Nat.card F : ℤ)) ^ ℓ)
    {E : Subgroup ↥(orthDerived Q)} (hE : IsElemAbelian p E)
    (hsc : ∀ g : ↥(orthDerived Q), (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E) :
    ∃ (U : Fin (ℓ - 1) → Submodule F V) (e : Fin (ℓ - 1) → ↥(orthDerived Q))
      (u : Fin (ℓ - 1) → V) (c t : F) (f f' : V),
      OmNsRootGen.IsCoherentFrame Q p U e E u c t ∧
      f ∈ polarPerp Q (⨆ j, U j) ∧ f' ∈ polarPerp Q (⨆ j, U j) ∧
      Q f = 0 ∧ Q f' = 0 ∧ QuadraticMap.polar Q f f' = 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, U, e, hframe, hdich⟩ :=
    OmNsRootGen.exists_planeFrame_of_selfCentralizing (Q := Q) hQ hp hp2 hpq hdim (by omega) hE hsc
  rcases hdich with ⟨hk, htop⟩ | ⟨hk, f, f', hf, hf', hQf, hQf', hpol⟩
  ·
    exfalso
    have hsum := charSum_iSup_eq_neg_pow (Q := Q) hframe.toIsPlaneSystem
    rw [htop] at hsum
    exact hS (by rw [hsum, hk])
  ·
    have hlk : ℓ - 1 = k := by omega
    let φ : Fin (ℓ - 1) ≃ Fin k := finCongr hlk
    have hframe' : IsPlaneFrame Q p (fun j => U (φ j)) (fun j => e (φ j)) E :=
      isPlaneFrame_reindex hframe φ
    obtain ⟨e', u, c, t, hcoh, -⟩ :=
      OmNsRootGen.exists_coherentFrame hframe' hp hp2 hpq (by omega : 1 ≤ ℓ - 1)
    have hsup : (⨆ j : Fin (ℓ - 1), U (φ j)) = ⨆ j : Fin k, U j := by
      refine le_antisymm (iSup_le fun j => le_iSup U (φ j)) (iSup_le fun j => ?_)
      have h := le_iSup (fun j : Fin (ℓ - 1) => U (φ j)) (φ.symm j)
      simpa using h
    exact ⟨fun j => U (φ j), e', u, c, t, f, f', hcoh, by rw [hsup]; exact hf,
      by rw [hsup]; exact hf', hQf, hQf', hpol⟩

theorem finrank_qPlusForm {K : Type} [Field K] (ℓ : ℕ) :
    Module.finrank K (Fin ℓ ⊕ Fin ℓ → K) = 2 * ℓ := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  ring

theorem finrank_qMinusForm {K : Type} [Field K] (m : ℕ) :
    Module.finrank K (CFSG.Assembly.LargeEvenMinusIdx m → K) = 2 * (m + 1) := by
  rw [Module.finrank_fintype_fun_eq_card]
  show Fintype.card ((Fin m ⊕ Fin m) ⊕ Fin 2) = 2 * (m + 1)
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_sum, Fintype.card_fin]
  ring

theorem charSum_qPlusForm_ne {K : Type} [Field K] [Finite K] [CharP K 2] {ℓ : ℕ}
    (hℓ : Odd ℓ) :
    OrdPNsOm.charSum (TableBOrth.qPlusForm K ℓ) ⊤ ≠ (-(Nat.card K : ℤ)) ^ ℓ := by
  have hpos : 1 ≤ ℓ := by obtain ⟨m, hm⟩ := hℓ; omega
  have hchar := OrthTorus.charSum_qPlusForm (K := K) (n := ℓ - 1)
  rw [Nat.sub_add_cancel hpos] at hchar
  rw [hchar, hℓ.neg_pow]
  have hq : (Nat.card K : ℤ) ^ ℓ ≠ 0 := by
    haveI : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    have h2 : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
    rw [h2]
    positivity
  intro h
  exact hq (by linarith)

theorem charSum_qMinusForm_ne {K : Type} [Field K] [Finite K] [CharP K 2] {ℓ : ℕ}
    (hℓ2 : 2 ≤ ℓ) (hℓ : Even ℓ) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    OrdPNsOm.charSum (TableBOrth.qMinusForm K (ℓ - 1) b c) ⊤ ≠ (-(Nat.card K : ℤ)) ^ ℓ := by
  obtain ⟨hchar, -⟩ := OrthTorus.charSum_qMinusForm (K := K) (m := ℓ - 1) hirr
  rw [Nat.sub_add_cancel (by omega : 1 ≤ ℓ)] at hchar
  rw [hchar, hℓ.neg_pow]
  have hq : (Nat.card K : ℤ) ^ ℓ ≠ 0 := by
    haveI : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    have h2 : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
    rw [h2]
    positivity
  intro h
  exact hq (by linarith)

end RelDNs

end CFSG.StandardType

end
