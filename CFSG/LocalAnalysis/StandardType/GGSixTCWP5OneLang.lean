module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6TwoLang
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5OneSigma
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5OneChain
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5OneRho

public section

namespace CFSG.StandardType.TableCRes

open CFSG.StandardType.KGCentE6 (iform_comm_E6 iform_add_left_E6 iform_smul_left_E6
  iform_sub_left_E6 iform_right_neg_E6)

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Assembly (LargeEvenLabel LargeEvenInLambda2 LargeEvenLieTag LargeEvenMarking
  LargeEvenSplit)

structure E6OneCfg
    {Lf : Type} [Field Lf] [IsAlgClosed Lf] {p₀ : ℕ}
    (S : LangSetup .E6 Lf p₀) (p : ℕ) {Dg : Subgroup (ModGL .E6 Lf)}
    (a : ↥Dg → Fin Tag.E6.rank → Lfˣ) (i : KernelComponent (famCharHom a)) (xg : ↥Dg) where
  α : Fin Tag.E6.rank → ℤ
  β : Fin Tag.E6.rank → ℤ
  α₃ : Fin Tag.E6.rank → ℤ
  β₃ : Fin Tag.E6.rank → ℤ
  vx : Fin Tag.E6.rank → ℤ
  hαr : IsRoot .E6 α
  hβr : IsRoot .E6 β
  hab : iform α β = -1
  hΨeq : componentRoots (famCharHom a) i = tcA2Set α β
  hα₂r : IsRoot .E6 (S.ρ α)
  hβ₂r : IsRoot .E6 (S.ρ β)
  a2 : iform (S.ρ α) (S.ρ β) = -1
  o1 : iform α (S.ρ α) = 0
  o2 : iform α (S.ρ β) = 0
  o3 : iform β (S.ρ α) = 0
  o4 : iform β (S.ρ β) = 0
  fr : E6Frame α β (S.ρ α) (S.ρ β) α₃ β₃
  himg : (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) '' tcA2Set α β =
    tcA2Set (S.ρ α) (S.ρ β)
  himg2 : (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) '' tcA2Set (S.ρ α) (S.ρ β) =
    tcA2Set α β
  hker : ∀ γ, γ ∈ kernelRoots (famCharHom a) ↔ γ ∈ tcA2Set α β ∪ tcA2Set (S.ρ α) (S.ρ β)
  hu : ∀ γ, IsRoot .E6 γ →
    iform (S.ρ γ) α₃ = iform γ α₃ ∧ iform (S.ρ γ) β₃ = iform γ β₃
  hvx : ∀ γ ∈ tcA2Set α β ∪ tcA2Set (S.ρ α) (S.ρ β), (p : ℤ) ∣ ∑ j, γ j * vx j
  hnx : ¬ ∀ j, (p : ℤ) ∣ vx j
  hcharx : ∀ γ, IsRoot .E6 γ → (rootChar (a xg) γ = 1 ↔ (p : ℤ) ∣ ∑ j, γ j * vx j)

theorem e6one_prep
    {Lf : Type} [Field Lf] [IsAlgClosed Lf] [CharP Lf 2] {p₀ p f : ℕ} (S : LangSetup .E6 Lf p₀)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hqf : S.D.q = 2 ^ f) (hc : orderOf ((2 : ZMod p) ^ f) = 1)
    (hρ : ∃ σ : (Fin Tag.E6.rank → ℤ) →+ (Fin Tag.E6.rank → ℤ), ∀ γ, IsRoot .E6 γ → S.ρ γ = σ γ)
    (Dg : Subgroup (ModGL .E6 Lf)) (hDcard : Nat.card Dg = p ^ 2)
    (a : ↥Dg → Fin Tag.E6.rank → Lfˣ)
    (ha : ∀ u : ↥Dg, (u : ModGL .E6 Lf) = rootDiagUnit .E6 (a u)) (hap : ∀ u j, a u j ^ p = 1)
    (hT : ∀ u, rootDiagUnit .E6 (a u) ∈ S.D.torus)
    (i : KernelComponent (famCharHom a))
    (hΨ : IsRootComponent (componentRoots (famCharHom a) i))
    (hr : Module.finrank ℤ (Submodule.span ℤ (componentRoots (famCharHom a) i)) = 2)
    (horth : ∀ γ ∈ componentRoots (famCharHom a) i,
      ∀ δ ∈ (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) ''
          componentRoots (famCharHom a) i,
        iform γ δ = 0 ∧ ¬ IsRoot .E6 (γ + δ))
    (xg : ↥Dg) (hx : xg ≠ 1) :
    Nonempty (E6OneCfg S p a i xg) := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hρroot : ∀ γ, IsRoot .E6 (S.ρ γ) ↔ IsRoot .E6 γ := S.frob.isRoot_iff
  have hρform : ∀ γ δ, iform (S.ρ γ) (S.ρ δ) = iform γ δ := S.frob.iform_eq
  have hρneg : ∀ γ, S.ρ (-γ) = -S.ρ γ := S.frob.neg_eq
  obtain ⟨σ, hσ⟩ := hρ
  have hρadd : ∀ γ δ, IsRoot .E6 γ → IsRoot .E6 δ → IsRoot .E6 (γ + δ) →
      S.ρ (γ + δ) = S.ρ γ + S.ρ δ := by
    intro γ δ hγ hδ hs
    rw [hσ _ hs, hσ _ hγ, hσ _ hδ, map_add]
  obtain ⟨α, β, hab, hΨeq⟩ := isRootComponent_rank_two_E6 hΨ hr
  have hαΨ : α ∈ componentRoots (famCharHom a) i := by rw [hΨeq]; simp [tcA2Set]
  have hβΨ : β ∈ componentRoots (famCharHom a) i := by rw [hΨeq]; simp [tcA2Set]
  have hαr : IsRoot .E6 α := hΨ.isRoot α hαΨ
  have hβr : IsRoot .E6 β := hΨ.isRoot β hβΨ
  have himg := image_a2Set hαr hβr hab hρneg hρadd
  have hX2 : (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) ''
      componentRoots (famCharHom a) i = tcA2Set (S.ρ α) (S.ρ β) := by
    rw [hΨeq]; exact himg
  have hα₂r : IsRoot .E6 (S.ρ α) := (hρroot α).2 hαr
  have hβ₂r : IsRoot .E6 (S.ρ β) := (hρroot β).2 hβr
  have a2 : iform (S.ρ α) (S.ρ β) = -1 := by rw [hρform]; exact hab
  have o1 : iform α (S.ρ α) = 0 := (horth α hαΨ (S.ρ α) ⟨α, hαΨ, rfl⟩).1
  have o2 : iform α (S.ρ β) = 0 := (horth α hαΨ (S.ρ β) ⟨β, hβΨ, rfl⟩).1
  have o3 : iform β (S.ρ α) = 0 := (horth β hβΨ (S.ρ α) ⟨α, hαΨ, rfl⟩).1
  have o4 : iform β (S.ρ β) = 0 := (horth β hβΨ (S.ρ β) ⟨β, hβΨ, rfl⟩).1
  obtain ⟨α₃, β₃, fr⟩ := e6_frame_lang hαr hβr hα₂r hβ₂r hab a2 o1 o2 o3 o4
  obtain ⟨v, hmul, hinj, hchar, hrho⟩ := family_vectors S hp hp2 Dg a ha hap hT
  have hq1 : (p : ℤ) ∣ (S.D.q : ℤ) - 1 := by
    have h1 : (2 : ZMod p) ^ f = 1 := by
      have h := pow_orderOf_eq_one ((2 : ZMod p) ^ f)
      rw [hc, pow_one] at h
      exact h
    rw [hqf]
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd (((2 ^ f : ℕ) : ℤ) - 1) p).1 ?_
    push_cast
    rw [h1]
    ring
  have hρc : ∀ u γ, IsRoot .E6 γ →
      (p : ℤ) ∣ (∑ j, (S.ρ γ) j * v u j) - ∑ j, γ j * v u j := by
    intro u γ hγ
    have h1 := hrho u γ hγ
    have e : (∑ j, (S.ρ γ) j * v u j) - ∑ j, γ j * v u j =
        ((∑ j, (S.ρ γ) j * v u j) - (S.D.q : ℤ) * ∑ j, γ j * v u j) +
          ((S.D.q : ℤ) - 1) * ∑ j, γ j * v u j := by ring
    rw [e]
    exact dvd_add h1 (dvd_mul_of_dvd_left hq1 _)
  have hXk : ∀ γ ∈ tcA2Set α β ∪ tcA2Set (S.ρ α) (S.ρ β), γ ∈ kernelRoots (famCharHom a) := by
    intro γ hγ
    rcases hγ with hγ | hγ
    · have h : γ ∈ componentRoots (famCharHom a) i := by rw [hΨeq]; exact hγ
      obtain ⟨h', -⟩ := h
      exact h'
    · rw [← hX2] at hγ
      obtain ⟨δ, hδ, rfl⟩ := hγ
      obtain ⟨h', -⟩ := hδ
      exact rho_mem_kernelRoots_famChar S a hT h'
  have hXv : ∀ u, ∀ γ ∈ tcA2Set α β ∪ tcA2Set (S.ρ α) (S.ρ β), (p : ℤ) ∣ ∑ j, γ j * v u j :=
    fun u γ hγ => (hchar u γ (hXk γ hγ).1).1 (((mem_kernelRoots_famChar a).1 (hXk γ hγ)).2 u)
  have hfull := frame_hfull hp hp5 hαr hβr hα₂r hβ₂r fr hab a2 o1 o2 o3 o4 v hmul hinj hDcard hXv
  have hsig := sigma_eq_X hp hp5 fr (W := Set.range v)
    (by rintro _ ⟨u, rfl⟩ γ hγ; exact hXv u γ hγ) hfull
  have hu := rho_u_pos hp hp5 fr (W := Set.range v) (ρ := S.ρ) hρroot
    (by rintro _ ⟨u, rfl⟩ γ hγ; exact hρc u γ hγ) hfull
  have hker : ∀ γ, γ ∈ kernelRoots (famCharHom a) ↔ γ ∈ tcA2Set α β ∪ tcA2Set (S.ρ α) (S.ρ β) := by
    intro γ
    constructor
    · intro hγ
      obtain ⟨hr1, hr2⟩ := (mem_kernelRoots_famChar a).1 hγ
      refine (hsig γ hr1).1 ?_
      rintro _ ⟨u, rfl⟩
      exact (hchar u γ hr1).1 (hr2 u)
    · exact hXk γ
  have hρX : ∀ γ ∈ tcA2Set α β ∪ tcA2Set (S.ρ α) (S.ρ β),
      S.ρ γ ∈ tcA2Set α β ∪ tcA2Set (S.ρ α) (S.ρ β) :=
    fun γ hγ => (hker _).1 (rho_mem_kernelRoots_famChar S a hT ((hker γ).2 hγ))
  have hfinX : (tcA2Set α β ∪ tcA2Set (S.ρ α) (S.ρ β)).Finite := by
    refine Set.Finite.union ?_ ?_ <;> (unfold tcA2Set; exact Set.toFinite _)
  have hO : ∀ x ∈ tcA2Set α β, ∀ y ∈ tcA2Set (S.ρ α) (S.ρ β), iform x y = 0 := by
    intro x hx y hy
    simp only [tcA2Set, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with h | h | h | h | h | h <;> rcases hy with h' | h' | h' | h' | h' | h' <;>
      simp [h, h', iform_add_left_E6, iform_add_right_E6, iform_neg_left_E6, iform_right_neg_E6,
        o1, o2, o3, o4]
  have hdisj : Disjoint (tcA2Set α β) (tcA2Set (S.ρ α) (S.ρ β)) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    have h0 := hO x hx x hx'
    have h2 := e6_iform_self x (mem_rootFinset.2 (isRoot_of_mem_a2Set hαr hβr hab hx))
    omega
  have himg2 := rho_image_X₂ S.ρ hdisj hfinX himg hρX
  refine ⟨⟨α, β, α₃, β₃, v xg, hαr, hβr, hab, hΨeq, hα₂r, hβ₂r, a2, o1, o2, o3, o4, fr, himg,
    himg2, hker, hu, hXv xg, fun h => hx (hinj xg h), fun γ hγ => hchar xg γ hγ⟩⟩

theorem e6one_caseI
    {Lf : Type} [Field Lf] [IsAlgClosed Lf] {p₀ p : ℕ} (S : LangSetup .E6 Lf p₀)
    (Dg : Subgroup (ModGL .E6 Lf)) (a : ↥Dg → Fin Tag.E6.rank → Lfˣ)
    (ha : ∀ u : ↥Dg, (u : ModGL .E6 Lf) = rootDiagUnit .E6 (a u))
    (hT : ∀ u, rootDiagUnit .E6 (a u) ∈ S.D.torus)
    (i : KernelComponent (famCharHom a)) (xg : ↥Dg) (C : E6OneCfg S p a i xg)
    {Jg Lg : Subgroup (ModGL .E6 Lf)} (hJspan : Jg ≤ rootSpan .E6 Lf (famOrbit S.ρ a i))
    (hJc : IsComponentOf Jg (S.Γ ⊓ Subgroup.centralizer (Dg : Set (ModGL .E6 Lf))))
    (hJL : Jg ≤ Lg)
    (i' : KernelComponent (famCharHom (fun _ : PUnit => a xg)))
    (hspan' : Lg ≤ rootSpan .E6 Lf
      {γ | ∃ (k : ℕ) (δ : Fin Tag.E6.rank → ℤ),
        δ ∈ componentRoots (famCharHom (fun _ : PUnit => a xg)) i' ∧
          γ = (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[k] δ})
    (hI : ∀ γ, IsRoot .E6 γ → (p : ℤ) ∣ (∑ j, γ j * C.vx j) →
      γ ∈ tcA2Set C.α C.β ∪ tcA2Set (S.ρ C.α) (S.ρ C.β) ∨
        ∀ m ∈ tcA2Set C.α C.β ∪ tcA2Set (S.ρ C.α) (S.ρ C.β), iform γ m = 0) :
    Lg ≤ Subgroup.centralizer (Dg : Set (ModGL .E6 Lf)) := by
  classical
  have hXroot : ∀ γ ∈ tcA2Set C.α C.β ∪ tcA2Set (S.ρ C.α) (S.ρ C.β), IsRoot .E6 γ :=
    fun γ hγ => ((C.hker γ).2 hγ).1
  have hρX : ∀ γ ∈ tcA2Set C.α C.β ∪ tcA2Set (S.ρ C.α) (S.ρ C.β),
      S.ρ γ ∈ tcA2Set C.α C.β ∪ tcA2Set (S.ρ C.α) (S.ρ C.β) :=
    fun γ hγ => (C.hker _).1 (rho_mem_kernelRoots_famChar S a hT ((C.hker γ).2 hγ))
  have hfin : (tcA2Set C.α C.β ∪ tcA2Set (S.ρ C.α) (S.ρ C.β)).Finite := by
    refine Set.Finite.union ?_ ?_ <;> (unfold tcA2Set; exact Set.toFinite _)
  have himgX : (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) ''
      (tcA2Set C.α C.β ∪ tcA2Set (S.ρ C.α) (S.ρ C.β)) =
        tcA2Set C.α C.β ∪ tcA2Set (S.ρ C.α) (S.ρ C.β) :=
    image_eq_of_finite S.ρ.injective hfin hρX
  have hiter : ∀ k : ℕ, ∀ δ ∈ tcA2Set C.α C.β ∪ tcA2Set (S.ρ C.α) (S.ρ C.β),
      (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[k] δ ∈
        tcA2Set C.α C.β ∪ tcA2Set (S.ρ C.α) (S.ρ C.β) := by
    intro k
    induction k with
    | zero => intro δ hδ; exact hδ
    | succ k ih =>
      intro δ hδ
      rw [Function.iterate_succ_apply']
      exact hρX _ (ih δ hδ)
  have hkerx : ∀ γ, γ ∈ kernelRoots (famCharHom (fun _ : PUnit => a xg)) ↔
      IsRoot .E6 γ ∧ (p : ℤ) ∣ ∑ j, γ j * C.vx j := by
    intro γ
    rw [mem_kernelRoots_famChar]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (C.hcharx γ h1).1 (h2 PUnit.unit)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun _ => (C.hcharx γ h1).2 h2⟩
  have hdich' : ∀ γ ∈ kernelRoots (famCharHom (fun _ : PUnit => a xg)),
      γ ∈ tcA2Set C.α C.β ∪ tcA2Set (S.ρ C.α) (S.ρ C.β) ∨
        ∀ m ∈ tcA2Set C.α C.β ∪ tcA2Set (S.ρ C.α) (S.ρ C.β), iform γ m = 0 := by
    intro γ hγ
    obtain ⟨h1, h2⟩ := (hkerx γ).1 hγ
    exact hI γ h1 h2
  rcases componentRoots_subset_or (famCharHom (fun _ : PUnit => a xg)) _ hdich' i' with
    hsub | horthX
  ·
    have hXorb : tcA2Set C.α C.β ∪ tcA2Set (S.ρ C.α) (S.ρ C.β) ⊆ famOrbit S.ρ a i := by
      intro γ hγ
      rcases hγ with hγ | hγ
      · exact ⟨0, γ, by rw [C.hΨeq]; exact hγ, rfl⟩
      · rw [← C.himg] at hγ
        obtain ⟨δ, hδ, rfl⟩ := hγ
        exact ⟨1, δ, by rw [C.hΨeq]; exact hδ, rfl⟩
    have hle1 : rootSpan .E6 Lf
        {γ | ∃ (k : ℕ) (δ : Fin Tag.E6.rank → ℤ),
          δ ∈ componentRoots (famCharHom (fun _ : PUnit => a xg)) i' ∧
            γ = (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[k] δ} ≤
        rootSpan .E6 Lf (famOrbit S.ρ a i) := by
      refine iSup₂_le fun γ hγ => le_iSup₂_of_le γ ?_ le_rfl
      obtain ⟨k, δ, hδ, rfl⟩ := hγ
      exact hXorb (hiter k δ (hsub hδ))
    exact hspan'.trans (hle1.trans (rootSpan_famOrbit_le_centralizer_group S Dg a ha hT i))
  ·
    exfalso
    have hρinvX : ∀ m ∈ tcA2Set C.α C.β ∪ tcA2Set (S.ρ C.α) (S.ρ C.β),
        ∃ z ∈ tcA2Set C.α C.β ∪ tcA2Set (S.ρ C.α) (S.ρ C.β), S.ρ z = m := by
      intro m hm
      rw [← himgX] at hm
      obtain ⟨z, hz, hzm⟩ := hm
      exact ⟨z, hz, hzm⟩
    have hiter_orth : ∀ k : ℕ, ∀ δ ∈ componentRoots (famCharHom (fun _ : PUnit => a xg)) i',
        ∀ m ∈ tcA2Set C.α C.β ∪ tcA2Set (S.ρ C.α) (S.ρ C.β),
          iform ((S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[k] δ) m = 0 := by
      intro k
      induction k with
      | zero => intro δ hδ m hm; exact horthX δ hδ m hm
      | succ k ih =>
        intro δ hδ m hm
        obtain ⟨z, hz, rfl⟩ := hρinvX m hm
        rw [Function.iterate_succ_apply', S.frob.iform_eq, ih δ hδ z hz]
    have hiter_root : ∀ k : ℕ, ∀ δ, IsRoot .E6 δ →
        IsRoot .E6 ((S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[k] δ) := by
      intro k
      induction k with
      | zero => intro δ hδ; exact hδ
      | succ k ih =>
        intro δ hδ
        rw [Function.iterate_succ_apply']
        exact (S.frob.isRoot_iff _).2 (ih δ hδ)
    have hcomm := CFSG.RankThree.PartOne.KE.rootSpan_commute_of_orth (τ := .E6) (L := Lf)
      (Or.inr (Or.inl rfl))
      (S₁ := {γ | ∃ (k : ℕ) (δ : Fin Tag.E6.rank → ℤ),
        δ ∈ componentRoots (famCharHom (fun _ : PUnit => a xg)) i' ∧
          γ = (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[k] δ})
      (S₂ := tcA2Set C.α C.β ∪ tcA2Set (S.ρ C.α) (S.ρ C.β))
      (by
        rintro _ ⟨k, δ, hδ, rfl⟩
        obtain ⟨h, -⟩ := hδ
        exact hiter_root k δ h.1)
      hXroot
      (by
        rintro _ ⟨k, δ, hδ, rfl⟩ β hβ
        rw [dotProduct_mulVec_eq_iform]
        exact hiter_orth k δ hδ β hβ)
    have hfam : famOrbit S.ρ a i ⊆ tcA2Set C.α C.β ∪ tcA2Set (S.ρ C.α) (S.ρ C.β) := by
      rintro _ ⟨k, δ, hδ, rfl⟩
      exact hiter k δ (Or.inl (by rw [← C.hΨeq]; exact hδ))
    have hJX : Jg ≤ rootSpan .E6 Lf (tcA2Set C.α C.β ∪ tcA2Set (S.ρ C.α) (S.ρ C.β)) :=
      hJspan.trans (iSup₂_le fun γ hγ => le_iSup₂_of_le γ (hfam hγ) le_rfl)
    exact not_abelian_of_isComponentOf hJc fun y hy z hz =>
      (hcomm z (hspan' (hJL hz)) y (hJX hy)).symm

theorem e6one_caseII
    {Lf : Type} [Field Lf] [IsAlgClosed Lf] [CharP Lf 2] {p₀ p f : ℕ} (S : LangSetup .E6 Lf p₀)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hqf : S.D.q = 2 ^ f)
    (hρ : ∃ σ : (Fin Tag.E6.rank → ℤ) →+ (Fin Tag.E6.rank → ℤ), ∀ γ, IsRoot .E6 γ → S.ρ γ = σ γ)
    (hR2 : LangFamilyCompLabel)
    {Dg : Subgroup (ModGL .E6 Lf)} (a : ↥Dg → Fin Tag.E6.rank → Lfˣ)
    (hT : ∀ u, rootDiagUnit .E6 (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (i : KernelComponent (famCharHom a)) (xg : ↥Dg) (C : E6OneCfg S p a i xg)
    {Lg : Subgroup (ModGL .E6 Lf)}
    (hLc' : IsComponentOf Lg (S.Γ ⊓ Subgroup.centralizer
      (Set.range fun u : PUnit.{1} => rootDiagUnit .E6 ((fun _ : PUnit.{1} => a xg) u))))
    (i' : KernelComponent (famCharHom (fun _ : PUnit => a xg)))
    (hspan' : Lg ≤ rootSpan .E6 Lf
      {γ | ∃ (k : ℕ) (δ : Fin Tag.E6.rank → ℤ),
        δ ∈ componentRoots (famCharHom (fun _ : PUnit => a xg)) i' ∧
          γ = (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[k] δ})
    (u₀ : ℤ × ℤ) (hu₀ : u₀ ∈ wtRep)
    (hII : ∀ γ, IsRoot .E6 γ → ((p : ℤ) ∣ (∑ j, γ j * C.vx j) ↔
      (γ ∈ tcA2Set C.α C.β ∪ tcA2Set (S.ρ C.α) (S.ρ C.β) ∨
        (γ ∉ tcA2Set C.α C.β ∪ tcA2Set (S.ρ C.α) (S.ρ C.β) ∧
          ((iform γ C.α₃, iform γ C.β₃) = u₀ ∨
            (iform γ C.α₃, iform γ C.β₃) = (-u₀.1, -u₀.2)))))) :
    GGCompLabelAt ⟨LargeEvenLieTag.twA, 5, f⟩ Lg := by
  classical
  have hp2 : p ≠ 2 := by omega
  obtain ⟨δ, hroot, hgram, h0, h1, h3, h4, h2, -, hch⟩ := C.fr.chain u₀ hu₀
  have hA : A5Chain δ := ⟨hroot, hgram⟩
  have hkerx : ∀ γ, γ ∈ kernelRoots (famCharHom (fun _ : PUnit => a xg)) ↔
      IsRoot .E6 γ ∧ (p : ℤ) ∣ ∑ j, γ j * C.vx j := by
    intro γ
    rw [mem_kernelRoots_famChar]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (C.hcharx γ h1).1 (h2 PUnit.unit)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun _ => (C.hcharx γ h1).2 h2⟩
  have hkerδ : kernelRoots (famCharHom (fun _ : PUnit => a xg)) = tcChainSet δ := by
    ext γ
    constructor
    · intro hγ
      obtain ⟨hr1, hr2⟩ := (hkerx γ).1 hγ
      exact (hch γ hr1).1 ((hII γ hr1).1 hr2)
    · intro hγ
      have hr1 := isRoot_of_mem_chainSet hA hγ
      exact (hkerx γ).2 ⟨hr1, (hII γ hr1).2 ((hch γ hr1).2 hγ)⟩
  have hC : componentRoots (famCharHom (fun _ : PUnit => a xg)) i' = tcChainSet δ :=
    componentRoots_eq_chainSet hA _ hkerδ i'
  have hfin : (tcChainSet δ).Finite :=
    Set.finite_of_ncard_ne_zero (by rw [ncard_chainSet hgram]; norm_num)
  have hρst : ∀ γ ∈ tcChainSet δ, S.ρ γ ∈ tcChainSet δ := by
    intro γ hγ
    rw [← hkerδ] at hγ ⊢
    exact rho_mem_kernelRoots_famChar S (fun _ : PUnit => a xg) (fun _ => hT xg) hγ
  have hst : (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) '' tcChainSet δ =
      tcChainSet δ :=
    image_eq_of_finite S.ρ.injective hfin hρst
  have hswap := a5SwapPos_of_frame C.fr C.hαr C.hβr C.hab C.hα₂r C.hβ₂r C.a2 hA h0 h1 h3 h4 h2
    C.himg C.himg2 C.hu hρst
  have hout := not_twistInner_chainSet_pos hA S.frob.iform_eq hρ hswap
  obtain ⟨n, hn, hlab⟩ := hR2 .E6 Lf p₀ p S (Or.inl rfl) hp hp2 PUnit (fun _ => a xg)
    (fun _ => hT xg) (fun _ j => by simp [hap xg j]) Lg hLc' i' hspan'
  rw [hC, tcE6_componentOrbitLength_eq_one hst, pow_one, hqf] at hn
  have hnf : n = f := Nat.pow_right_injective (le_refl 2) hn
  rw [hC, componentLabel_chainSet_outer hA hst hout n, hnf] at hlab
  exact hlab

theorem e6one_lang
    (hR : LangFamilyCompFieldSL) (hR2 : LangFamilyCompLabel)
    {Lf : Type} [Field Lf] [IsAlgClosed Lf] [CharP Lf 2] {p₀ p f : ℕ} (S : LangSetup .E6 Lf p₀)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hqf : S.D.q = 2 ^ f) (hc : orderOf ((2 : ZMod p) ^ f) = 1)
    (hρ : ∃ σ : (Fin Tag.E6.rank → ℤ) →+ (Fin Tag.E6.rank → ℤ), ∀ γ, IsRoot .E6 γ → S.ρ γ = σ γ)
    (Dg : Subgroup (ModGL .E6 Lf)) (hDcard : Nat.card Dg = p ^ 2)
    (a : ↥Dg → Fin Tag.E6.rank → Lfˣ)
    (ha : ∀ u : ↥Dg, (u : ModGL .E6 Lf) = rootDiagUnit .E6 (a u)) (hap : ∀ u j, a u j ^ p = 1)
    (hT : ∀ u, rootDiagUnit .E6 (a u) ∈ S.D.torus)
    (i : KernelComponent (famCharHom a))
    (hΨ : IsRootComponent (componentRoots (famCharHom a) i))
    (hr : Module.finrank ℤ (Submodule.span ℤ (componentRoots (famCharHom a) i)) = 2)
    (horth : ∀ γ ∈ componentRoots (famCharHom a) i,
      ∀ δ ∈ (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) ''
          componentRoots (famCharHom a) i,
        iform γ δ = 0 ∧ ¬ IsRoot .E6 (γ + δ))
    {Jg Lg : Subgroup (ModGL .E6 Lf)} (hJspan : Jg ≤ rootSpan .E6 Lf (famOrbit S.ρ a i))
    (hJc : IsComponentOf Jg (S.Γ ⊓ Subgroup.centralizer (Dg : Set (ModGL .E6 Lf))))
    (xg : ↥Dg) (hx : xg ≠ 1)
    (hLc : IsComponentOf Lg (S.Γ ⊓ Subgroup.centralizer {(xg : ModGL .E6 Lf)})) (hJL : Jg ≤ Lg) :
    Lg ≤ Subgroup.centralizer (Dg : Set (ModGL .E6 Lf)) ∨
      GGCompLabelAt ⟨LargeEvenLieTag.twA, 5, f⟩ Lg := by
  classical
  have hp2 : p ≠ 2 := by omega
  obtain ⟨C⟩ := e6one_prep S hp hp5 hqf hc hρ Dg hDcard a ha hap hT i hΨ hr horth xg hx
  have hdich := line_dichotomy hp hp5 C.hαr C.hβr C.hα₂r C.hβ₂r C.hab C.a2 C.o1 C.o2 C.o3 C.o4
    C.fr C.vx C.hvx C.hnx
  have hLc' : IsComponentOf Lg (S.Γ ⊓ Subgroup.centralizer
      (Set.range fun u : PUnit.{1} => rootDiagUnit .E6 ((fun _ : PUnit.{1} => a xg) u))) := by
    have : (Set.range fun u : PUnit.{1} => rootDiagUnit .E6 ((fun _ : PUnit.{1} => a xg) u)) =
        {(xg : ModGL .E6 Lf)} := by
      rw [Set.range_const, ← ha xg]
    rw [this]
    exact hLc
  obtain ⟨i', hspan', -⟩ := hR .E6 Lf p₀ p S (Or.inl rfl) hp hp2 PUnit.{1} (fun _ => a xg)
    (fun _ => hT xg) (fun _ j => hap xg j) Lg hLc'
  rcases hdich with hI | ⟨u₀, hu₀, hII⟩
  · exact Or.inl (e6one_caseI S Dg a ha hT i xg C hJspan hJc hJL i' hspan' hI)
  · exact Or.inr (e6one_caseII S hp hp5 hqf hρ hR2 a hT hap i xg C hLc' i' hspan' u₀ hu₀ hII)

end CFSG.StandardType.TableCRes

end
