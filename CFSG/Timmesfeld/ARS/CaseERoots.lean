module

public import CFSG.Timmesfeld.ARS.CaseEExtremal
public import CFSG.Timmesfeld.ARS.LowestMember

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

section Roots

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem isIndiv_of_divisible_eq_empty (hdiv : D.divisible = ∅) {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) : (RootSystem.ofCartan D.isFiniteType D.divisible).IsIndiv γ := by
  intro δ hδ hγδ
  have hγ' : γ ∈ CFSG.LieType.RootSystem.roots D.isFiniteType D.divisible := hγ
  rw [CFSG.LieType.RootSystem.roots, hdiv] at hγ'
  rcases hγ' with ⟨w, i, rfl⟩ | ⟨w, i, hi, -⟩
  · have h1 := congrArg (weylAction D.isFiniteType w⁻¹) hγδ
    rw [weylAction_inv_apply_apply, map_nsmul] at h1
    have h2 := congrFun h1 i
    simp only [Pi.single_eq_same, Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] at h2
    omega
  · exact absurd hi (Set.notMem_empty i)

theorem exists_eq_weylAction_single (hdiv : D.divisible = ∅) {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) : ∃ w i, γ = weylAction D.isFiniteType w (Pi.single i 1) := by
  have hγ' : γ ∈ CFSG.LieType.RootSystem.roots D.isFiniteType D.divisible := hγ
  rw [CFSG.LieType.RootSystem.roots, hdiv] at hγ'
  rcases hγ' with ⟨w, i, rfl⟩ | ⟨w, i, hi, -⟩
  · exact ⟨w, i, rfl⟩
  · exact absurd hi (Set.notMem_empty i)

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
    (weylAction D.isFiniteType) D.roots D.rootGroup n H)

include hct in
theorem map_rootGroup_mem_leviSet (hR : IsRootClass R) {A A₀ : Subgroup G}
    (hdiv : D.divisible = ∅) (Ψ : K →* G) (hΨV : ∀ g, Ψ g ∈ levi R A A₀)
    (hP : ∀ k, (D.rootGroup (Pi.single k 1)).map Ψ ∈ leviSet R A A₀) {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) : (D.rootGroup γ).map Ψ ∈ leviSet R A A₀ := by
  obtain ⟨w, i, rfl⟩ := exists_eq_weylAction_single hdiv hγ
  rw [← actsAs_nrep hct w _ ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i),
    ← map_conjSub_eq]
  exact Levi.conjSub_mem_leviSet_of_mem_levi hR (hP i) (hΨV _)

theorem commutator_map_rootGroup_le (hext : SteinbergExtras D n H) (Ψ : K →* G)
    {γ δ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) (hδ : δ ∈ D.roots) (hind : LinIndepPair γ δ) :
    ⁅(D.rootGroup γ).map Ψ, (D.rootGroup δ).map Ψ⁆ ≤
      ⨆ ε ∈ openCone D.roots γ δ, (D.rootGroup ε).map Ψ := by
  rw [← Subgroup.map_commutator, Subgroup.map_le_iff_le_comap, Subgroup.commutator_le]
  intro x hx y hy
  have h1 := hext.commutator_mem γ hγ δ hδ hind x hx y hy
  have h2 : Ψ ⁅x, y⁆ ∈ (⨆ ε ∈ openCone D.roots γ δ, D.rootGroup ε).map Ψ :=
    Subgroup.mem_map_of_mem Ψ h1
  simp only [Subgroup.map_iSup] at h2
  exact h2

theorem map_negUnipotent (Ψ : K →* G) :
    (negUnipotent D).map Ψ = ⨆ γ ∈ {γ | γ ∈ D.roots ∧ ht γ < 0}, (D.rootGroup γ).map Ψ := by
  simp only [negUnipotent, Subgroup.map_iSup]

theorem commuting_map_negUnipotent {Ψ : K →* G} {E : Subgroup G}
    (h : ∀ γ ∈ D.roots, ht γ < 0 → Commuting E ((D.rootGroup γ).map Ψ)) :
    Commuting E ((negUnipotent D).map Ψ) := by
  rw [map_negUnipotent, commuting_iff_le_centralizer]
  exact iSup₂_le fun γ hγ => commuting_iff_le_centralizer.1 (h γ hγ.1 hγ.2)

theorem exists_mem_lambdaStar_commuting_negUnipotent (h : Hyp G R) {A A₀ : Subgroup G}
    (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A)
    (hext : SteinbergExtras D n H) (hdiv : D.divisible = ∅) (Ψ : K →* G)
    (hΨ : ∀ γ ∈ D.roots, (D.rootGroup γ).map Ψ ∈ leviSet R A A₀) :
    ∃ E ∈ lambdaStar R A A₀, Commuting E ((negUnipotent D).map Ψ) := by
  set Φ := RootSystem.ofCartan D.isFiniteType D.divisible
  let ι := {γ : Fin D.rank → ℤ // γ ∈ D.roots ∧ ht γ < 0}
  have : Finite ι := ((finite_roots D.isFiniteType D.divisible).subset
    fun γ (hγ : γ ∈ {γ | γ ∈ D.roots ∧ ht γ < 0}) => hγ.1).to_subtype
  let N : ι → Subgroup G := fun a => (D.rootGroup a.1).map Ψ
  have hN : ∀ a, N a ∈ leviSet R A A₀ := fun a => hΨ a.1 a.2.1
  let hgt : ι → ℕ := fun a => (-ht a.1).toNat
  have hcl : ∀ a b, Commuting (N a) (N b) ∨ ∃ S : Set ι,
      (∀ c ∈ S, hgt a < hgt c ∧ hgt b < hgt c) ∧ ⁅N a, N b⁆ ≤ ⨆ c ∈ S, N c := by
    intro a b
    by_cases hab : a = b
    · subst hab
      exact Or.inl (h.root.commuting_self (hN a).1.1)
    right
    have hne : a.1 ≠ b.1 := fun e => hab (Subtype.ext e)
    have hind : LinIndepPair a.1 b.1 :=
      Φ.linIndepPair_of_mem_neg a.2 (isIndiv_of_divisible_eq_empty hdiv a.2.1) b.2
        (isIndiv_of_divisible_eq_empty hdiv b.2.1) hne
    have hcone : ∀ ε ∈ openCone D.roots a.1 b.1,
        ht ε < 0 ∧ -ht a.1 < -ht ε ∧ -ht b.1 < -ht ε := by
      rintro ε ⟨-, p, q, hp, hq, rfl⟩
      have ha := a.2.2
      have hb := b.2.2
      have e : ht (p • a.1 + q • b.1) = p * ht a.1 + q * ht b.1 := by
        rw [ht_add, ht_nsmul, ht_nsmul]
      rw [e]
      have hp1 : (1 : ℤ) ≤ p := by exact_mod_cast hp
      have hq1 : (1 : ℤ) ≤ q := by exact_mod_cast hq
      refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
    refine ⟨{c | c.1 ∈ openCone D.roots a.1 b.1}, fun c hc => ?_, ?_⟩
    · obtain ⟨-, h1, h2⟩ := hcone c.1 hc
      simp only [hgt]
      omega
    · refine (commutator_map_rootGroup_le hext Ψ a.2.1 b.2.1 hind).trans
        (iSup₂_le fun ε hε => ?_)
      exact le_iSup₂_of_le (f := fun c (_ : c ∈ {c : ι | c.1 ∈ openCone D.roots a.1 b.1}) => N c)
        ⟨ε, hε.1, (hcone ε hε).1⟩ hε le_rfl
  obtain ⟨E, hE, hEa⟩ :=
    exists_mem_lambdaStar_forall_commuting_of_height_le h hA hAne hA₀ N hN hgt hcl
  exact ⟨E, hE, commuting_map_negUnipotent fun γ hγ hγ0 => hEa ⟨γ, hγ, hγ0⟩⟩

theorem Sec13.exists_mem_lambdaStar_commuting_negUnipotent {A A₀ : Subgroup G}
    (hS : Sec13 R A A₀) (hext : SteinbergExtras D n H) (hdiv : D.divisible = ∅) (Ψ : K →* G)
    (hΨ : ∀ γ ∈ D.roots, (D.rootGroup γ).map Ψ ∈ leviSet R A A₀) :
    ∃ E ∈ lambdaStar R A A₀, Commuting E ((negUnipotent D).map Ψ) :=
  _root_.CFSG.Timmesfeld.ARS.exists_mem_lambdaStar_commuting_negUnipotent hS.hyp hS.mem hS.sec8.2
    hS.opp hext hdiv Ψ hΨ

end Roots

end CFSG.Timmesfeld.ARS
