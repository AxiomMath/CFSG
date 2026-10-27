module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6FrameLang
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6Sigma
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6Vec
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6Rank
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6A2Set
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6Form
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6Chain
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6Dich
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6Fam
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Inputs
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Inputs2
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UData
public import CFSG.RankThree.PartOne.KE.E8TwoA2Family

public section

namespace CFSG.StandardType.TableCRes

open CFSG.StandardType.KGCentE6 (iform_comm_E6 iform_add_left_E6 iform_smul_left_E6
  iform_sub_left_E6 iform_right_neg_E6)

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Assembly (LargeEvenLabel LargeEvenInLambda2 LargeEvenLieTag)

theorem image_eq_of_finite {α : Type*} {f : α → α} (hf : Function.Injective f) {X : Set α}
    (hX : X.Finite) (h : ∀ x ∈ X, f x ∈ X) : f '' X = X := by
  refine Set.eq_of_subset_of_ncard_le ?_ ?_ hX
  · rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  · rw [Set.ncard_image_of_injective _ hf]

theorem image_a2Set
    {ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)} {α β : Fin Tag.E6.rank → ℤ}
    (hα : IsRoot .E6 α) (hβ : IsRoot .E6 β) (hab : iform α β = -1)
    (hρneg : ∀ γ, ρ (-γ) = -ρ γ)
    (hρadd : ∀ γ δ, IsRoot .E6 γ → IsRoot .E6 δ → IsRoot .E6 (γ + δ) →
      ρ (γ + δ) = ρ γ + ρ δ) :
    (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) '' tcA2Set α β = tcA2Set (ρ α) (ρ β) := by
  have n2 : iform β β = 2 := e6_iform_self β (mem_rootFinset.2 hβ)
  have hne : α ≠ -β := by
    intro h
    rw [h, iform_neg_left_E6, n2] at hab
    norm_num at hab
  have hsum : IsRoot .E6 (α + β) :=
    isRoot_add_of_iform_neg hα hβ hne (by rw [hab]; norm_num)
  have e : ρ (α + β) = ρ α + ρ β := hρadd α β hα hβ hsum
  simp only [tcA2Set, Set.image_insert_eq, Set.image_singleton, hρneg, e]

theorem rootSpan_famOrbit_le_centralizer_group
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup .E6 L p₀)
    (Dg : Subgroup (ModGL .E6 L)) (a : ↥Dg → Fin Tag.E6.rank → Lˣ)
    (ha : ∀ u : ↥Dg, (u : ModGL .E6 L) = rootDiagUnit .E6 (a u))
    (hT : ∀ u, rootDiagUnit .E6 (a u) ∈ S.D.torus) (i : KernelComponent (famCharHom a)) :
    rootSpan .E6 L (famOrbit S.ρ a i) ≤ Subgroup.centralizer (Dg : Set (ModGL .E6 L)) := by
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have h1 := rootSpan_rationalRoots_le_centralizer S a i (b := a ⟨g, hg⟩) (hT ⟨g, hg⟩)
    (fun γ hγ => by
      obtain ⟨h, -⟩ := hγ
      exact ((mem_kernelRoots_famChar a).1 h).2 ⟨g, hg⟩) hy
  have h2 := (Subgroup.mem_centralizer_iff.1 h1) (rootDiagUnit .E6 (a ⟨g, hg⟩))
    (Set.mem_singleton _)
  have h3 : g = rootDiagUnit .E6 (a ⟨g, hg⟩) := ha ⟨g, hg⟩
  rw [h3]
  exact h2

theorem not_abelian_of_isComponentOf {G : Type*} [Group G] {J K : Subgroup G}
    (hJ : IsComponentOf J K) (h : ∀ y ∈ J, ∀ z ∈ J, y * z = z * y) : False := by
  obtain ⟨-, -, -, hsimp⟩ := hJ
  haveI := hsimp
  have hc : Subgroup.center ↥J = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (h y y.2 x x.2)
  haveI : Subsingleton (↥J ⧸ Subgroup.center ↥J) := by
    rw [hc]
    exact QuotientGroup.subsingleton_quotient_top
  exact not_subsingleton (↥J ⧸ Subgroup.center ↥J) inferInstance

theorem componentLabel_chainSet
    {δ : Fin 5 → (Fin Tag.E6.rank → ℤ)} (hδ : A5Chain δ) {ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)}
    (hst : (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) '' tcChainSet δ = tcChainSet δ)
    (hin : twistInner (tcChainSet δ) (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)))
    (n : ℕ) :
    componentLabel (compRank (tcChainSet δ)) (tcChainSet δ).ncard (twistKindOf ρ (tcChainSet δ)) n =
      ⟨LargeEvenLieTag.A, 5, n⟩ := by
  have h1 := tcE6_componentOrbitLength_eq_one hst
  have hk : twistKindOf ρ (tcChainSet δ) = .inner := by
    unfold twistKindOf
    rw [h1]
    have hin' : twistInner (tcChainSet δ)
        ((ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[1]) := by
      simpa using hin
    rw [if_pos hin']
  rw [hk, compRank_chainSet hδ.gram, ncard_chainSet hδ.gram]
  simp [componentLabel]

theorem frame_m_orth {α β α₂ β₂ α₃ β₃ : Fin Tag.E6.rank → ℤ}
    (hαr : IsRoot .E6 α) (hβr : IsRoot .E6 β) (hα₂r : IsRoot .E6 α₂) (hβ₂r : IsRoot .E6 β₂)
    (fr : E6Frame α β α₂ β₂ α₃ β₃)
    (o1 : iform α α₂ = 0) (o2 : iform α β₂ = 0) (o3 : iform β α₂ = 0) (o4 : iform β β₂ = 0) :
    (∀ k : Fin 6, iform (![α, β, α₂, β₂, α₃, β₃] k) (![α, β, α₂, β₂, α₃, β₃] k) = 2) ∧
    (∀ i j : Fin 6, i.val / 2 ≠ j.val / 2 →
      iform (![α, β, α₂, β₂, α₃, β₃] i) (![α, β, α₂, β₂, α₃, β₃] j) = 0) := by
  obtain ⟨f1, f2, f3, f4⟩ := fr.orth₁
  obtain ⟨g1, g2, g3, g4⟩ := fr.orth₂
  have s1 : iform α₂ α = 0 := by rw [iform_comm_E6]; exact o1
  have s2 : iform β₂ α = 0 := by rw [iform_comm_E6]; exact o2
  have s3 : iform α₂ β = 0 := by rw [iform_comm_E6]; exact o3
  have s4 : iform β₂ β = 0 := by rw [iform_comm_E6]; exact o4
  have t1 : iform α₃ α = 0 := by rw [iform_comm_E6]; exact f1
  have t2 : iform β₃ α = 0 := by rw [iform_comm_E6]; exact f2
  have t3 : iform α₃ β = 0 := by rw [iform_comm_E6]; exact f3
  have t4 : iform β₃ β = 0 := by rw [iform_comm_E6]; exact f4
  have u1 : iform α₃ α₂ = 0 := by rw [iform_comm_E6]; exact g1
  have u2 : iform β₃ α₂ = 0 := by rw [iform_comm_E6]; exact g2
  have u3 : iform α₃ β₂ = 0 := by rw [iform_comm_E6]; exact g3
  have u4 : iform β₃ β₂ = 0 := by rw [iform_comm_E6]; exact g4
  constructor
  · intro k
    fin_cases k
    · exact e6_iform_self α (mem_rootFinset.2 hαr)
    · exact e6_iform_self β (mem_rootFinset.2 hβr)
    · exact e6_iform_self α₂ (mem_rootFinset.2 hα₂r)
    · exact e6_iform_self β₂ (mem_rootFinset.2 hβ₂r)
    · exact e6_iform_self α₃ (mem_rootFinset.2 fr.root₃)
    · exact e6_iform_self β₃ (mem_rootFinset.2 fr.root₃')
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> assumption

theorem frame_hfull {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {α β α₂ β₂ α₃ β₃ : Fin Tag.E6.rank → ℤ}
    (hαr : IsRoot .E6 α) (hβr : IsRoot .E6 β) (hα₂r : IsRoot .E6 α₂) (hβ₂r : IsRoot .E6 β₂)
    (fr : E6Frame α β α₂ β₂ α₃ β₃) (hab : iform α β = -1) (a2 : iform α₂ β₂ = -1)
    (o1 : iform α α₂ = 0) (o2 : iform α β₂ = 0) (o3 : iform β α₂ = 0) (o4 : iform β β₂ = 0)
    {D : Type*} [Group D] (v : D → (Fin Tag.E6.rank → ℤ))
    (hmul : ∀ u u' : D, ∀ j, (p : ℤ) ∣ v (u * u') j - v u j - v u' j)
    (hinj : ∀ u : D, (∀ j, (p : ℤ) ∣ v u j) → u = 1) (hcard : Nat.card D = p ^ 2)
    (hXv : ∀ u, ∀ γ ∈ tcA2Set α β ∪ tcA2Set α₂ β₂, (p : ℤ) ∣ ∑ j, γ j * v u j) :
    ∀ s t : ℤ, ∃ w ∈ Set.range v, ∀ γ : Fin Tag.E6.rank → ℤ,
      (p : ℤ) ∣ (∑ j, γ j * w j) - (s * iform γ α₃ + t * iform γ β₃) := by
  obtain ⟨hnorm, horth'⟩ := frame_m_orth hαr hβr hα₂r hβ₂r fr o1 o2 o3 o4
  have hvan : ∀ u : D, ∀ k : Fin 6, k.val < 4 →
      (p : ℤ) ∣ ∑ j, (![α, β, α₂, β₂, α₃, β₃] k) j * v u j := by
    intro u k hk
    fin_cases k
    · exact hXv u α (Or.inl (by simp [tcA2Set]))
    · exact hXv u β (Or.inl (by simp [tcA2Set]))
    · exact hXv u α₂ (Or.inr (by simp [tcA2Set]))
    · exact hXv u β₂ (Or.inr (by simp [tcA2Set]))
    · exact absurd hk (by decide)
    · exact absurd hk (by decide)
  have hfullu := dtilde_full hp hp5 ![α, β, α₂, β₂, α₃, β₃] hnorm hab a2 fr.ip₃ horth' v hmul
    hinj hvan hcard
  intro s t
  obtain ⟨u, hu⟩ := hfullu s t
  exact ⟨v u, ⟨u, rfl⟩, hu⟩


structure E6TwoCfg
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
    iform (S.ρ γ) α₃ = - iform γ α₃ ∧ iform (S.ρ γ) β₃ = - iform γ β₃
  hvx : ∀ γ ∈ tcA2Set α β ∪ tcA2Set (S.ρ α) (S.ρ β), (p : ℤ) ∣ ∑ j, γ j * vx j
  hnx : ¬ ∀ j, (p : ℤ) ∣ vx j
  hcharx : ∀ γ, IsRoot .E6 γ → (rootChar (a xg) γ = 1 ↔ (p : ℤ) ∣ ∑ j, γ j * vx j)

theorem e6two_prep
    {Lf : Type} [Field Lf] [IsAlgClosed Lf] [CharP Lf 2] {p₀ p f : ℕ} (S : LangSetup .E6 Lf p₀)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hqf : S.D.q = 2 ^ f) (hc : orderOf ((2 : ZMod p) ^ f) = 2)
    (hρ : ∃ w : WeylGroup .E6, ∀ γ, IsRoot .E6 γ → S.ρ γ = w • γ)
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
    Nonempty (E6TwoCfg S p a i xg) := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hρroot : ∀ γ, IsRoot .E6 (S.ρ γ) ↔ IsRoot .E6 γ := S.frob.isRoot_iff
  have hρform : ∀ γ δ, iform (S.ρ γ) (S.ρ δ) = iform γ δ := S.frob.iform_eq
  have hρneg : ∀ γ, S.ρ (-γ) = -S.ρ γ := S.frob.neg_eq
  obtain ⟨w, hw⟩ := hρ
  have hρadd : ∀ γ δ, IsRoot .E6 γ → IsRoot .E6 δ → IsRoot .E6 (γ + δ) →
      S.ρ (γ + δ) = S.ρ γ + S.ρ δ := by
    intro γ δ hγ hδ hs
    rw [hw _ hs, hw _ hγ, hw _ hδ, smul_add]
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
  have hq1 : (p : ℤ) ∣ (S.D.q : ℤ) + 1 := by
    haveI : Fact p.Prime := ⟨hp⟩
    have h2 : ((2 : ZMod p) ^ f) ^ 2 = 1 := by
      have := pow_orderOf_eq_one ((2 : ZMod p) ^ f)
      rwa [hc] at this
    have h3 : (2 : ZMod p) ^ f ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hc
      omega
    have h22 : (2 : ZMod p) ^ f * (2 : ZMod p) ^ f = 1 := by rw [← sq]; exact h2
    have hm1 : (2 : ZMod p) ^ f = -1 := by
      rcases mul_self_eq_one_iff.1 h22 with h | h
      · exact absurd h h3
      · exact h
    rw [hqf]
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd ((2 : ℤ) ^ f + 1) p).1 ?_
    push_cast
    rw [hm1]
    ring
  have hρc : ∀ u γ, IsRoot .E6 γ →
      (p : ℤ) ∣ (∑ j, (S.ρ γ) j * v u j) + ∑ j, γ j * v u j := by
    intro u γ hγ
    have h1 := hrho u γ hγ
    have e : (∑ j, (S.ρ γ) j * v u j) + ∑ j, γ j * v u j =
        ((∑ j, (S.ρ γ) j * v u j) - (S.D.q : ℤ) * ∑ j, γ j * v u j) +
          ((S.D.q : ℤ) + 1) * ∑ j, γ j * v u j := by ring
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
  have hu := rho_u_neg hp hp5 fr (W := Set.range v) (ρ := S.ρ) hρroot
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

theorem e6two_caseI
    {Lf : Type} [Field Lf] [IsAlgClosed Lf] {p₀ p : ℕ} (S : LangSetup .E6 Lf p₀)
    (Dg : Subgroup (ModGL .E6 Lf)) (a : ↥Dg → Fin Tag.E6.rank → Lfˣ)
    (ha : ∀ u : ↥Dg, (u : ModGL .E6 Lf) = rootDiagUnit .E6 (a u))
    (hT : ∀ u, rootDiagUnit .E6 (a u) ∈ S.D.torus)
    (i : KernelComponent (famCharHom a)) (xg : ↥Dg) (C : E6TwoCfg S p a i xg)
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

theorem e6two_caseII
    {Lf : Type} [Field Lf] [IsAlgClosed Lf] [CharP Lf 2] {p₀ p f : ℕ} (S : LangSetup .E6 Lf p₀)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hqf : S.D.q = 2 ^ f)
    (hρ : ∃ w : WeylGroup .E6, ∀ γ, IsRoot .E6 γ → S.ρ γ = w • γ)
    (hR2 : LangFamilyCompLabel)
    {Dg : Subgroup (ModGL .E6 Lf)} (a : ↥Dg → Fin Tag.E6.rank → Lfˣ)
    (hT : ∀ u, rootDiagUnit .E6 (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (i : KernelComponent (famCharHom a)) (xg : ↥Dg) (C : E6TwoCfg S p a i xg)
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
    GGCompLabelAt ⟨LargeEvenLieTag.A, 5, f⟩ Lg := by
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
  have hst : (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) '' tcChainSet δ = tcChainSet δ :=
    image_eq_of_finite S.ρ.injective hfin hρst
  have hswap := a5Swap_of_frame C.fr C.hαr C.hβr C.hab C.hα₂r C.hβ₂r C.a2 hA h0 h1 h3 h4 h2
    C.himg C.himg2 C.hu hρst
  have hin := twistInner_chainSet hA S.frob.iform_eq hρ hswap
  obtain ⟨n, hn, hlab⟩ := hR2 .E6 Lf p₀ p S (Or.inl rfl) hp hp2 PUnit (fun _ => a xg)
    (fun _ => hT xg) (fun _ j => by simp [hap xg j]) Lg hLc' i' hspan'
  rw [hC, tcE6_componentOrbitLength_eq_one hst, pow_one, hqf] at hn
  have hnf : n = f := Nat.pow_right_injective (le_refl 2) hn
  rw [hC, componentLabel_chainSet hA hst hin n, hnf] at hlab
  exact hlab

theorem e6two_lang
    (hR : LangFamilyCompFieldSL) (hR2 : LangFamilyCompLabel)
    {Lf : Type} [Field Lf] [IsAlgClosed Lf] [CharP Lf 2] {p₀ p f : ℕ} (S : LangSetup .E6 Lf p₀)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hqf : S.D.q = 2 ^ f) (hc : orderOf ((2 : ZMod p) ^ f) = 2)
    (hρ : ∃ w : WeylGroup .E6, ∀ γ, IsRoot .E6 γ → S.ρ γ = w • γ)
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
      GGCompLabelAt ⟨LargeEvenLieTag.A, 5, f⟩ Lg := by
  classical
  have hp2 : p ≠ 2 := by omega
  obtain ⟨C⟩ := e6two_prep S hp hp5 hqf hc hρ Dg hDcard a ha hap hT i hΨ hr horth xg hx
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
  · exact Or.inl (e6two_caseI S Dg a ha hT i xg C hJspan hJc hJL i' hspan' hI)
  · exact Or.inr (e6two_caseII S hp hp5 hqf hρ hR2 a hT hap i xg C hLc' i' hspan' u₀ hu₀ hII)

end CFSG.StandardType.TableCRes

end
