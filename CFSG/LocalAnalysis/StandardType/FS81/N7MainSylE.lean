module

public import CFSG.LocalAnalysis.StandardType.FS81.N7MainFone
public import CFSG.LocalAnalysis.StandardType.FS81.N7FixGen
public import CFSG.LocalAnalysis.StandardType.FS81.N7FixSylow

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

private theorem nm_F1grp_le_closure_E6 {X : Type} [Group X] [Finite X] (S : N7MSetup X) :
    S.F1grp ≤ Subgroup.closure {x : X | S.ρ x ∈ nmE6} := by
  intro f hf
  obtain ⟨l, hl_mem, hl_prod⟩ := nmF1_eq_prod_E6 ((S.mem_F1grp f).mp hf)
  have h : ∀ l : List (Matrix (Fin 8) (Fin 8) (ZMod 3)),
      (∀ t ∈ l, t ∈ nmE6) →
      ∃ g ∈ Subgroup.closure {x : X | S.ρ x ∈ nmE6}, S.ρ g = l.prod := by
    intro l
    induction l with
    | nil => intro _; exact ⟨1, Subgroup.one_mem _, by simp⟩
    | cons t l ih =>
      intro hl
      have ht_mem : t ∈ nmE6 := hl t (by simp)
      have ht_even : t ∈ evenAll0 7 :=
        nmF_subset_evenAll0 (nmF1_subset_nmF (nmE6_subset_nmF1 ht_mem))
      obtain ⟨x, hx⟩ := S.surj_H1 t ht_even
      obtain ⟨g, hg, hg_prod⟩ := ih (fun u hu => hl u (by simp [hu]))
      refine ⟨x * g, Subgroup.mul_mem _ (Subgroup.subset_closure ?_) hg, ?_⟩
      · rw [Set.mem_setOf_eq, hx]
        exact ht_mem
      · rw [map_mul, hx, hg_prod, List.prod_cons]
  obtain ⟨g, hg, hg_prod⟩ := h l hl_mem
  have hgf : g = f := S.ρ_inj (hg_prod.trans hl_prod.symm)
  rw [← hgf]
  exact hg

private theorem nmSgn_eq_sgn (A : Finset (Fin 8)) : nmSgn A = sgn A := rfl

private theorem nmE6_eq_E6set : nmE6 = E6set := rfl

private theorem nm_F1grp_isPGroup {X : Type} [Group X] [Finite X] (S : N7MSetup X) :
    IsPGroup 2 S.F1grp := by
  intro x
  refine ⟨1, ?_⟩
  apply Subtype.ext
  show (x : X) ^ 2 ^ 1 = 1
  rw [pow_one]
  apply S.ρ_inj
  rw [map_pow, map_one]
  obtain ⟨A, -, -, hA⟩ := (S.mem_F1grp (x : X)).mp x.2
  rw [hA, pow_two, nmSgn_mul_self]

private theorem nm_F1grp_weakly_closed {X : Type} [Group X] [Finite X] (S : N7MSetup X)
    (hW : S.Weak) (y : X) (hy : ∀ f ∈ S.F1grp, y * f * y⁻¹ ∈ S.H1grp) :
    ∀ f ∈ S.F1grp, y * f * y⁻¹ ∈ S.F1grp := by
  have hconj : ∀ g ∈ Subgroup.closure {x : X | S.ρ x ∈ nmE6}, y * g * y⁻¹ ∈ S.F1grp := by
    intro g hg
    refine Subgroup.closure_induction (p := fun g _ => y * g * y⁻¹ ∈ S.F1grp) ?_ ?_ ?_ ?_ hg
    · intro x hx
      have hxF : x ∈ S.F1grp :=
        (S.mem_F1grp x).mpr (nmE6_subset_nmF1 (by simpa using hx))
      have hH : y * x * y⁻¹ ∈ S.H1grp := hy x hxF
      exact (S.mem_F1grp _).mpr
        (nmE6_subset_nmF1 (hW x y (by simpa using hx) ((S.mem_H1grp _).mp hH)))
    · simp only [mul_one, mul_inv_cancel]
      exact S.F1grp.one_mem
    · intro a b _ _ ha hb
      have h : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
      rw [h]
      exact S.F1grp.mul_mem ha hb
    · intro a _ ha
      have h : y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ := by group
      rw [h]
      exact S.F1grp.inv_mem ha
  intro f hf
  exact hconj f (nm_F1grp_le_closure_E6 S hf)

private theorem nm_E6_X_ncard {X : Type} [Group X] [Finite X] (S : N7MSetup X) :
    {x : X | S.ρ x ∈ nmE6}.ncard = 7 := by
  have hpre : {x : X | S.ρ x ∈ nmE6} = S.ρ ⁻¹' nmE6 := rfl
  rw [hpre, Set.ncard_preimage_of_injective_subset_range S.ρ_inj]
  · rw [nmE6_eq_E6set]
    exact q2nN7_E6set_ncard
  · intro M hM
    have hM_even : M ∈ evenAll0 7 :=
      nmF_subset_evenAll0 (nmF1_subset_nmF (nmE6_subset_nmF1 hM))
    obtain ⟨x, hx⟩ := S.surj_H1 M hM_even
    exact ⟨x, hx⟩

private theorem nm_E6_conj_eq {X : Type} [Group X] [Finite X] (S : N7MSetup X)
    {t y : X} (ht : S.ρ t ∈ nmE6) (hy : S.ρ y ∈ nmE6) :
    ∃ m : X, y = m * t * m⁻¹ := by
  obtain ⟨A₀, h0₀, hc₀, htA⟩ := ht
  obtain ⟨A, h0, hc, hyA⟩ := hy
  obtain ⟨π, hπ0, hπA⟩ := q2nN7_exists_perm h0₀ hc₀ h0 hc
  have hmem : spMat π (fun _ => 1) ∈ evenAll0 7 := by
    refine ⟨π, fun _ => 1, fun _ => Or.inl rfl, ⟨hπ0, ?_⟩, rfl⟩
    simp
  obtain ⟨m, hm⟩ := S.surj_H1 _ hmem
  have htA' : S.ρ t = sgn A₀ := by rw [htA, nmSgn_eq_sgn]
  have hyA' : S.ρ y = sgn A := by rw [hyA, nmSgn_eq_sgn]
  have hconj : S.ρ m * sgn A₀ = sgn A * S.ρ m := by
    rw [hm, q2nN7_spMat_mul_sgn, hπA]
  refine ⟨m, ?_⟩
  apply S.ρ_inj
  have hinv : S.ρ m * S.ρ m⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  calc S.ρ y = sgn A := hyA'
    _ = sgn A * (S.ρ m * S.ρ m⁻¹) := by rw [hinv, mul_one]
    _ = (sgn A * S.ρ m) * S.ρ m⁻¹ := by rw [mul_assoc]
    _ = (S.ρ m * sgn A₀) * S.ρ m⁻¹ := by rw [← hconj]
    _ = S.ρ (m * t * m⁻¹) := by rw [map_mul, map_mul, htA']

private theorem nm_F1grp_le_closure_conj {X : Type} [Group X] [Finite X] (S : N7MSetup X)
    {P : Subgroup X} (hF : S.F1grp ≤ P) {t : X} (ht : S.ρ t ∈ nmE6) :
    S.F1grp ≤ Subgroup.closure {y | y ∈ P ∧ ∃ m : X, y = m * t * m⁻¹} := by
  intro f hf
  obtain ⟨l, hl_mem, hl_prod⟩ := nmF1_eq_prod_E6 ((S.mem_F1grp f).mp hf)
  have h : ∀ l : List (Matrix (Fin 8) (Fin 8) (ZMod 3)),
      (∀ M ∈ l, M ∈ nmE6) →
      ∃ g ∈ Subgroup.closure {y | y ∈ P ∧ ∃ m : X, y = m * t * m⁻¹}, S.ρ g = l.prod := by
    intro l
    induction l with
    | nil => intro _; exact ⟨1, Subgroup.one_mem _, by simp⟩
    | cons M l ih =>
      intro hl
      have hM : M ∈ nmE6 := hl M (by simp)
      have hM_even : M ∈ evenAll0 7 :=
        nmF_subset_evenAll0 (nmF1_subset_nmF (nmE6_subset_nmF1 hM))
      obtain ⟨y, hy⟩ := S.surj_H1 M hM_even
      have hyNM : S.ρ y ∈ nmE6 := by rw [hy]; exact hM
      have hyP : y ∈ P := hF ((S.mem_F1grp y).mpr (nmE6_subset_nmF1 hyNM))
      obtain ⟨m, hm⟩ := nm_E6_conj_eq S ht hyNM
      obtain ⟨g, hg, hg_prod⟩ := ih (fun N hN => hl N (by simp [hN]))
      refine ⟨y * g, Subgroup.mul_mem _ (Subgroup.subset_closure ?_) hg, ?_⟩
      · exact ⟨hyP, m, hm⟩
      · rw [map_mul, hy, hg_prod, List.prod_cons]
  obtain ⟨g, hg, hg_prod⟩ := h l hl_mem
  have hgf : g = f := S.ρ_inj (hg_prod.trans hl_prod.symm)
  rw [← hgf]
  exact hg

theorem nm_sylow_E6 {X : Type} [Group X] [Finite X] (S : N7MSetup X) (hW : S.Weak) :
    ∃ (P : Sylow 2 X) (t : X), (P : Subgroup X) ≤ S.H1grp ∧ S.F1grp ≤ (P : Subgroup X) ∧
      S.ρ t ∈ nmE6 ∧ ∀ y ∈ (P : Subgroup X), y * t = t * y := by
  classical
  have hFn : (S.F1grp.subgroupOf S.H1grp).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact S.conj_mem_F1grp g.2 hn
  have hFp : IsPGroup 2 S.F1grp := nm_F1grp_isPGroup S
  have hnorm : Subgroup.normalizer (S.F1grp : Set X) ≤ S.H1grp := by
    intro x hx
    exact (nm_normalizer_F1 S).mp ((Subgroup.mem_normalizer_iff).mp hx)
  have hwc : ∀ y : X, (∀ f ∈ S.F1grp, y * f * y⁻¹ ∈ S.H1grp) →
      ∀ f ∈ S.F1grp, y * f * y⁻¹ ∈ S.F1grp := nm_F1grp_weakly_closed S hW
  obtain ⟨P, hPH⟩ := q2nN7_exists_sylow_le S.H1grp S.F1grp S.F1grp_le_H1grp hFn hFp hnorm hwc
  have hFP : S.F1grp ≤ (P : Subgroup X) :=
    q2nN7_le_sylow_of_normal S.F1grp_le_H1grp hFn hFp P hPH
  have hE7 : {x : X | S.ρ x ∈ nmE6}.ncard = 7 := nm_E6_X_ncard S
  have hE_not_dvd : ¬ 2 ∣ {x : X | S.ρ x ∈ nmE6}.ncard := by
    rw [hE7]
    decide
  have hconjE : ∀ y ∈ (P : Subgroup X), ∀ τ ∈ {x : X | S.ρ x ∈ nmE6},
      y * τ * y⁻¹ ∈ {x : X | S.ρ x ∈ nmE6} := by
    intro y hy τ hτ
    have hτF : τ ∈ S.F1grp := (S.mem_F1grp τ).mpr (nmE6_subset_nmF1 hτ)
    have hτP : τ ∈ (P : Subgroup X) := hFP hτF
    have hyτP : y * τ * y⁻¹ ∈ (P : Subgroup X) :=
      (P : Subgroup X).mul_mem ((P : Subgroup X).mul_mem hy hτP) ((P : Subgroup X).inv_mem hy)
    have hH : y * τ * y⁻¹ ∈ S.H1grp := hPH hyτP
    exact hW τ y hτ ((S.mem_H1grp _).mp hH)
  obtain ⟨t, ht, hcent⟩ := q2nN7_exists_central (P : Subgroup X) P.isPGroup'
    {x : X | S.ρ x ∈ nmE6} (Set.toFinite _) hE_not_dvd hconjE
  exact ⟨P, t, hPH, hFP, ht, hcent⟩

theorem nm_closure_F1 {X : Type} [Group X] [Finite X] (S : N7MSetup X) (hW : S.Weak)
    {P : Subgroup X} (hP : P ≤ S.H1grp) (hF : S.F1grp ≤ P) {t : X} (ht : S.ρ t ∈ nmE6) :
    Subgroup.closure {y | y ∈ P ∧ ∃ m : X, y = m * t * m⁻¹} = S.F1grp := by
  apply le_antisymm
  · refine (Subgroup.closure_le S.F1grp).2 ?_
    rintro y ⟨hyP, m, rfl⟩
    have hH : m * t * m⁻¹ ∈ S.H1grp := hP hyP
    have hmem : S.ρ (m * t * m⁻¹) ∈ evenAll0 7 := (S.mem_H1grp _).mp hH
    exact (S.mem_F1grp _).mpr (nmE6_subset_nmF1 (hW t m ht hmem))
  · exact nm_F1grp_le_closure_conj S hF ht

end CFSG.StandardType.FrameRoute.FS81

end
