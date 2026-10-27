module

public import CFSG.LocalAnalysis.StandardType.GGL45TorusHDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Helpers

private lemma ggL45L976_largeEvenInduces_unique {K : Type*} [Group K] {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) {α : MulAut K} {φ : MulAut R}
    (hind : LargeEvenInduces θ (fun k k' => k' = α k) φ) : φ = ggInducedAut θ α := by
  ext r
  obtain ⟨q, rfl⟩ := θ.surjective r
  induction q using QuotientGroup.induction_on with
  | H l => rw [ggInducedAut_apply]; exact hind l _ rfl

private lemma ggL45L976_pow_apply_zpow {K : Type*} [Group K] {α : MulAut K} {h : K} {c : ℤ}
    (hc : α h = h ^ c) (m : ℕ) : (α ^ m) h = h ^ (c ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', MulAut.mul_apply, ih, map_zpow, hc, ← zpow_mul, ← pow_succ']

private lemma ggL45L976_conj_pow {R : Type*} [Group R] {f u : MulAut R} {c : ℤ}
    (hc : f * u * f⁻¹ = u ^ c) (m : ℕ) : f ^ m * u * (f ^ m)⁻¹ = u ^ (c ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', mul_inv_rev]
    calc (f * f ^ m) * u * ((f ^ m)⁻¹ * f⁻¹)
        = f * (f ^ m * u * (f ^ m)⁻¹) * f⁻¹ := by group
      _ = f * u ^ (c ^ m) * f⁻¹ := by rw [ih]
      _ = (f * u * f⁻¹) ^ (c ^ m) := (conj_zpow (a := f) (b := u) (i := c ^ m)).symm
      _ = (u ^ c) ^ (c ^ m) := by rw [hc]
      _ = u ^ (c * c ^ m) := (zpow_mul u c (c ^ m)).symm
      _ = u ^ (c ^ (m + 1)) := by rw [pow_succ']

private lemma ggL45L976_modEq_pow_pow {p : ℕ} {s : ℕ} (hs : 2 ≤ s) {c₀ : ℤ} {k₀ : ℕ}
    (hc₀ : c₀ ≡ 1 + (p : ℤ) ^ (s - 1) * k₀ [ZMOD (p : ℤ) ^ s]) (m : ℕ) :
    c₀ ^ m ≡ 1 + (p : ℤ) ^ (s - 1) * (m * k₀) [ZMOD (p : ℤ) ^ s] := by
  induction m with
  | zero => simpa using Int.ModEq.refl (1 : ℤ)
  | succ m ih =>
    rw [pow_succ]
    refine (ih.mul hc₀).trans ?_
    rw [Int.modEq_iff_dvd]
    have hP : (p : ℤ) ^ s ∣ ((p : ℤ) ^ (s - 1)) ^ 2 := by
      rw [← pow_mul]
      exact pow_dvd_pow _ (by omega)
    have hdvd : (p : ℤ) ^ s ∣ ((p : ℤ) ^ (s - 1)) ^ 2 * (-((m : ℤ) * k₀ * k₀)) :=
      dvd_mul_of_dvd_left hP _
    convert hdvd using 1
    push_cast
    ring

private lemma ggL45L976_pow_apply_fixed {K : Type*} [Group K] {α : MulAut K} {k : K}
    (h : α k = k) (m : ℕ) : (α ^ m) k = k := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', MulAut.mul_apply, ih, h]

private lemma ggL45L976_pow_mapsTo {K : Type*} [Group K] {α : MulAut K} {Q : Subgroup K}
    (h : ∀ g ∈ Q, α g ∈ Q) (m : ℕ) : ∀ g ∈ Q, (α ^ m) g ∈ Q := by
  induction m with
  | zero => intro g hg; simpa using hg
  | succ m ih =>
    intro g hg
    rw [pow_succ', MulAut.mul_apply]
    exact h _ (ih g hg)

end Helpers

theorem ggL45TorusH_pow {p : ℕ} (hp : p.Prime) {K : Type*} [Group K] {R : Type} [Group R]
    {I : Set (MulAut R)} {θ : K ⧸ Subgroup.center K ≃* R} {ψ : MulAut K}
    {E : Subgroup (MulAut K)} (hψ : ψ ^ p = 1) {j : ℕ} (hj : ¬ p ∣ j)
    (h : GGL45TorusH p I θ (ψ ^ j) E) : GGL45TorusH p I θ ψ E := by
  obtain ⟨s, hs, c₀, k₀, hk₀, hc₀, H1₀, H2₀, H3₀, H4₀⟩ := h
  obtain ⟨j', -, hj'mod⟩ :=
    Nat.exists_mul_mod_eq_one_of_coprime (k := p) (n := j)
      (hp.coprime_iff_not_dvd.mpr hj).symm hp.one_lt
  have hj' : ¬ p ∣ j' := by
    intro hdiv
    have h0 : j * j' % p = 0 := Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right hdiv j)
    omega
  have hdecomp : j * j' = 1 + p * ((j * j') / p) := by
    calc j * j' = (j * j') % p + p * ((j * j') / p) := (Nat.mod_add_div (j * j') p).symm
      _ = 1 + p * ((j * j') / p) := by rw [hj'mod]
  have hpow : (ψ ^ j) ^ j' = ψ := by
    rw [← pow_mul, hdecomp, pow_add, pow_one, pow_mul, hψ, one_pow, mul_one]
  have hf : ggInducedAut θ ψ = (ggInducedAut θ (ψ ^ j)) ^ j' := by
    have hc := congrArg (ggInducedAut θ) hpow
    rw [map_pow] at hc
    exact hc.symm
  refine ⟨s, hs, c₀ ^ j', j' * k₀, ?_, ?_, ?_, ?_, H3₀, ?_⟩
  · intro hdiv
    rcases (hp.dvd_mul).mp hdiv with h | h
    · exact hj' h
    · exact hk₀ h
  · exact ggL45L976_modEq_pow_pow hs hc₀ j'
  · refine ⟨H1₀.1, fun u hu => ⟨(H1₀.2 u hu).1, ?_⟩⟩
    have hconj := ggL45L976_conj_pow (H1₀.2 u hu).2 j'
    rwa [← hf] at hconj
  · refine ⟨H2₀.1, (fun h hh => ⟨(H2₀.2.1 h hh).1, ?_⟩), H2₀.2.2⟩
    have hiter := ggL45L976_pow_apply_zpow (α := ψ ^ j) (h := h) (c := c₀)
      (H2₀.2.1 h hh).2 j'
    rwa [hpow] at hiter
  · intro α hαp hαcomm hαnotI hαpI
    obtain ⟨i, hi, hiI⟩ := H4₀ α hαp hαcomm hαnotI hαpI
    refine ⟨j * i, ?_, ?_⟩
    · intro hdiv
      rcases (hp.dvd_mul).mp hdiv with h | h
      · exact hj h
      · exact hi h
    · have hfi : (ggInducedAut θ ψ) ^ (j * i) = (ggInducedAut θ (ψ ^ j)) ^ i := by
        rw [pow_mul, ← map_pow]
      rwa [hfi]

theorem ggL45TorusKGHyp_pow {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} {R : Type} [Group R]
    {I F : Set (MulAut R)} (hF : ∀ f ∈ F, ∀ n : ℕ, f ^ n ∈ F) {K : Type} [Group K]
    {θ : K ⧸ Subgroup.center K ≃* R} {ψ : MulAut K} {E : Subgroup (MulAut K)} {j : ℕ}
    (hj : ¬ p ∣ j) (h : GGL45TorusKGHyp p lab I F θ ψ E) :
    GGL45TorusKGHyp p lab I F θ (ψ ^ j) E := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  obtain ⟨j', -, hj'mod⟩ :=
    Nat.exists_mul_mod_eq_one_of_coprime (k := p) (n := j)
      (hp.coprime_iff_not_dvd.mpr hj).symm hp.one_lt
  have hj' : ¬ p ∣ j' := by
    intro hdiv
    have h0 : j * j' % p = 0 := Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right hdiv j)
    omega
  have hdecomp : j * j' = 1 + p * ((j * j') / p) := by
    calc j * j' = (j * j') % p + p * ((j * j') / p) := (Nat.mod_add_div (j * j') p).symm
      _ = 1 + p * ((j * j') / p) := by rw [hj'mod]
  have hpow : (ψ ^ j) ^ j' = ψ := by
    rw [← pow_mul, hdecomp, pow_add, pow_one, pow_mul, h1, one_pow, mul_one]
  refine ⟨?_, ?_, h3, h4, h5, h6, ?_, ?_, ?_, ?_⟩
  · rw [← pow_mul, Nat.mul_comm j p, pow_mul, h1, one_pow]
  · obtain ⟨f, hf, u, hu, hford, hind⟩ := h2
    have hcop : (orderOf f).Coprime j := by
      rw [hford]; exact hp.coprime_iff_not_dvd.mpr hj
    have hord : orderOf (f ^ j) = p := by
      rw [Nat.Coprime.orderOf_pow hcop, hford]
    have hψeq : ggInducedAut θ ψ = u * f * u⁻¹ :=
      (ggL45L976_largeEvenInduces_unique θ hind).symm
    have hjeq : ggInducedAut θ (ψ ^ j) = u * f ^ j * u⁻¹ := by
      rw [map_pow, hψeq, conj_pow]
    refine ⟨f ^ j, hF f hf j, u, hu, hord, ?_⟩
    have hind' := ggL45_largeEvenInduces_inducedAut θ (ψ ^ j)
    rwa [hjeq] at hind'
  · intro e he
    have h7e : Commute e ψ := h7 e he
    exact h7e.pow_right j
  · intro k hkp hfix hk
    refine h8 k hkp hfix ?_
    have hiter := ggL45L976_pow_apply_fixed (α := ψ ^ j) (k := k) hk j'
    rwa [hpow] at hiter
  · intro R₀ Q hR₀ hfix hQ hQne hstab hnorm
    have hfixψ : ∀ r ∈ R₀, ψ r = r := by
      intro r hr
      have hiter := ggL45L976_pow_apply_fixed (α := ψ ^ j) (k := r) (hfix r hr) j'
      rwa [hpow] at hiter
    have hstabψ : ∀ g ∈ Q, ψ g ∈ Q := by
      intro g hg
      have hiter := ggL45L976_pow_mapsTo (α := ψ ^ j) (Q := Q) hstab j' g hg
      rwa [hpow] at hiter
    exact h9 R₀ Q hR₀ hfixψ hQ hQne hstabψ hnorm
  · obtain ⟨P, hPle, hPcard, hP⟩ := h10
    refine ⟨P, hPle, hPcard, ?_⟩
    intro e he
    obtain ⟨γ, hγp, hγcomm, hγpg, hγeq⟩ := hP (e ^ j') (Subgroup.pow_mem P he j')
    have heE : e ∈ E := hPle he
    have h7e : Commute e ψ := h7 e heE
    have hcomm : Commute (e ^ j') ψ⁻¹ :=
      Commute.inv_right_iff.mpr (h7e.pow_left j')
    have hW : γ * ψ⁻¹ * γ⁻¹ = (e ^ j') * ψ⁻¹ := by rw [hγeq]; group
    have hmain : γ * (ψ ^ j)⁻¹ * γ⁻¹ * (ψ ^ j) = (e ^ j') ^ j := by
      have h1' : γ * (ψ ^ j)⁻¹ * γ⁻¹ = (γ * ψ⁻¹ * γ⁻¹) ^ j := by
        rw [conj_pow, inv_pow]
      rw [h1', hW, hcomm.mul_pow, ← pow_mul, inv_pow]
      group
    have hep : e ^ p = 1 := h3.2 e heE
    have hjj : e ^ (j' * j) = e := by
      rw [Nat.mul_comm, hdecomp, pow_add, pow_one, pow_mul, hep, one_pow, mul_one]
    have hsub : Subgroup.closure (insert γ (insert (ψ ^ j) (E : Set (MulAut K)))) ≤
        Subgroup.closure (insert γ (insert ψ (E : Set (MulAut K)))) := by
      rw [Subgroup.closure_le]
      intro x hx
      rw [Set.mem_insert_iff] at hx
      rcases hx with rfl | hx
      · exact Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inl rfl))
      · rw [Set.mem_insert_iff] at hx
        rcases hx with rfl | hx
        · exact Subgroup.pow_mem _ (Subgroup.subset_closure
            (Set.mem_insert_iff.mpr (Or.inr (Set.mem_insert_iff.mpr (Or.inl rfl))))) j
        · exact Subgroup.subset_closure
            (Set.mem_insert_iff.mpr (Or.inr (Set.mem_insert_iff.mpr (Or.inr hx))))
    have hfinal : γ * (ψ ^ j)⁻¹ * γ⁻¹ * (ψ ^ j) = e := by
      rw [hmain, ← pow_mul, hjj]
    exact ⟨γ, hγp, hγcomm, IsPGroup.to_le hγpg hsub, hfinal.symm⟩

end CFSG.StandardType
