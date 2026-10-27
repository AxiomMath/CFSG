module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneA2Orbit
public import CFSG.LocalAnalysis.StandardType.GGNTPlaneDiag
public import CFSG.LocalAnalysis.StandardType.GGExcCompSLLen
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTamePrime
public import CFSG.LocalAnalysis.ComponentInitial.SwappedQuasisimple
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.HardMathSupport.Cooperstein.Coordinator.StarAux
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcLang

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LocalAnalysis.ComponentInitial

private lemma a2s_rho_image_eq_of_orbitLength_eq_one {L : Type} [Field L] [IsAlgClosed L]
    {p₀ : ℕ}
    (S : LangSetup .E6 L p₀) {a : Fin Tag.E6.rank → Lˣ}
    {i : KernelComponent (rootCharHom a)}
    (h : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1) :
    (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) ''
      componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i := by
  have hne : ({s : ℕ | 0 < s ∧ (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[s] ''
      componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i} : Set ℕ).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have h0 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 0 := by
      simp [componentOrbitLength, hne]
    omega
  have hmem : sInf {s : ℕ | 0 < s ∧
      (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[s] ''
        componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i} ∈
      {s : ℕ | 0 < s ∧ (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[s] ''
        componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i} :=
    Nat.sInf_mem hne
  have h' : sInf {s : ℕ | 0 < s ∧
      (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[s] ''
        componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i} = 1 := h
  rw [h'] at hmem
  simpa using hmem.2

private lemma a2s_rationalRoots_eq {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup .E6 L p₀) {a : Fin Tag.E6.rank → Lˣ}
    (hfix : ∀ i : KernelComponent (rootCharHom a),
      componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    (i : KernelComponent (rootCharHom a)) :
    rationalRoots S.ρ (rootCharHom a) i = componentRoots (rootCharHom a) i := by
  apply le_antisymm
  · rintro γ ⟨k, δ, hδ, rfl⟩
    have hstab : (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[k] ''
        componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Function.iterate_succ', Set.image_comp, ih,
          a2s_rho_image_eq_of_orbitLength_eq_one S (hfix i)]
    have hmem : (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[k] δ ∈
        (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[k] ''
          componentRoots (rootCharHom a) i :=
      Set.mem_image_of_mem _ hδ
    rwa [hstab] at hmem
  · intro γ hγ
    exact ⟨0, γ, hγ, by simp⟩

private lemma a2s_rationalSpan_eq {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup .E6 L p₀) {a : Fin Tag.E6.rank → Lˣ}
    (hfix : ∀ i : KernelComponent (rootCharHom a),
      componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    (i : KernelComponent (rootCharHom a)) :
    rationalSpan S.ρ S.Γ (rootCharHom a) i =
      componentRootSpan L (rootCharHom a) i ⊓ S.Γ := by
  rw [rationalSpan, a2s_rationalRoots_eq S hfix i]
  rfl

private lemma a2s_rationalComponent_eq {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup .E6 L p₀) {a : Fin Tag.E6.rank → Lˣ}
    (hfix : ∀ i : KernelComponent (rootCharHom a),
      componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    (i : KernelComponent (rootCharHom a)) :
    rationalComponent S.ρ S.Γ (rootCharHom a) i =
      ⁅componentRootSpan L (rootCharHom a) i ⊓ S.Γ,
        componentRootSpan L (rootCharHom a) i ⊓ S.Γ⁆ := by
  rw [rationalComponent, a2s_rationalSpan_eq S hfix i]

private lemma a2s_conj_Gamma {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup .E6 L p₀) {n : ModGL .E6 L} (hn : n ∈ S.D.model) :
    S.Γ.map (MulAut.conj n).toMonoidHom = S.Γ := by
  have hmodel : S.D.model.map (MulAut.conj n).toMonoidHom = S.D.model :=
    conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hn)
  change ⁅S.D.model, S.D.model⁆.map (MulAut.conj n).toMonoidHom = ⁅S.D.model, S.D.model⁆
  rw [Subgroup.map_commutator, hmodel]

private lemma a2s_conj_rationalComponent {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup .E6 L p₀) {a : Fin Tag.E6.rank → Lˣ}
    (hfix : ∀ i : KernelComponent (rootCharHom a),
      componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    {n : ModGL .E6 L} (hn : n ∈ S.D.model)
    (σ : Equiv.Perm (KernelComponent (rootCharHom a)))
    (hσ : ∀ i : KernelComponent (rootCharHom a),
      (componentRootSpan L (rootCharHom a) i).map (MulAut.conj n).toMonoidHom =
        componentRootSpan L (rootCharHom a) (σ i))
    (i : KernelComponent (rootCharHom a)) :
    (rationalComponent S.ρ S.Γ (rootCharHom a) i).map (MulAut.conj n).toMonoidHom =
      rationalComponent S.ρ S.Γ (rootCharHom a) (σ i) := by
  rw [a2s_rationalComponent_eq S hfix i, a2s_rationalComponent_eq S hfix (σ i),
    Subgroup.map_commutator]
  rw [Subgroup.map_inf _ _ _ (MulAut.conj n).injective, hσ i, a2s_conj_Gamma S hn]

private lemma a2s_commutator_rationalComponent_eq_bot
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup .E6 L p₀) {a : Fin Tag.E6.rank → Lˣ}
    (hfix : ∀ i : KernelComponent (rootCharHom a),
      componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    {i j : KernelComponent (rootCharHom a)} (hij : i ≠ j) :
    ⁅rationalComponent S.ρ S.Γ (rootCharHom a) i,
      rationalComponent S.ρ S.Γ (rootCharHom a) j⁆ = ⊥ := by
  rw [a2s_rationalComponent_eq S hfix i, a2s_rationalComponent_eq S hfix j,
    Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine (Subgroup.commutator_le_sup _ _).trans ((le_of_eq (sup_idem _)).trans ?_)
  exact (inf_le_left.trans (componentRootSpan_le_centralizer L hij)).trans
    (Subgroup.centralizer_le ((Subgroup.commutator_le_sup _ _).trans
      ((le_of_eq (sup_idem _)).trans inf_le_left)))


private lemma a2s_isQuasisimple_range {K X : Type*} [Group K] [Group X] (ψ : K →* X)
    (hker : ψ.ker ≤ Subgroup.center K) (hK : CFSG.IsQuasisimple K) :
    CFSG.IsQuasisimple ↥(ψ.range) := by
  have htop : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup K) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native
      ↥(⊤ : Subgroup K)).mpr
      ((isQuasisimple_congr Subgroup.topEquiv).mpr hK)
  have h := CFSG.ClassicalInvolution.Balance.Bootstrap.isQuasisimple_map_of_ker_le_center ψ hker
    (R := ⊤) htop
  rw [Subgroup.map_top] at h
  exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥(ψ.range)).mp
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open ↥(ψ.range)).mp h)

private lemma a2s_eq_of_isComponentOf_le_of_quasisimple {G : Type*} [Group G]
    {K Δ C : Subgroup G} (hKC : CFSG.Assembly.IsComponentOf K C)
    (hKΔ : K ≤ Δ) (hΔC : Δ ≤ C) (hΔq : CFSG.Open.IsQuasisimple ↥Δ)
    (hKq : CFSG.IsQuasisimple ↥K) :
    K = Δ := by
  have hKsub : CFSG.Assembly.IsSubnormal K Δ := by
    have h := hKC.2.1.inf_of_le hΔC
    rwa [inf_eq_left.mpr hKΔ] at h
  have hsubM : (K.subgroupOf Δ).IsSubnormal :=
    (CFSG.Assembly.IsSubnormal.iff_subgroupOf hKΔ).mp hKsub
  have hsub : CFSG.Open.IsSubnormal (K.subgroupOf Δ) ⊤ :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isSubnormal_iff_open _ _).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isSubnormal_top_iff_mathlib
        (K.subgroupOf Δ)).mpr hsubM)
  rcases CFSG.ComponentClassification.Quasisimple.subnormal_le_center_or_eq_top hΔq
    (K.subgroupOf Δ) hsub with hc | htop
  · exfalso
    have hab2 : ∀ a b : ↥K, a * b = b * a := by
      intro a b
      let aΔ : ↥Δ := ⟨(a : G), hKΔ a.2⟩
      let bΔ : ↥Δ := ⟨(b : G), hKΔ b.2⟩
      have haΔ : aΔ ∈ K.subgroupOf Δ := by rw [Subgroup.mem_subgroupOf]; exact a.2
      have ha : aΔ ∈ Subgroup.center ↥Δ := hc haΔ
      have h := Subgroup.mem_center_iff.mp ha bΔ
      exact Subtype.ext (Subtype.ext_iff.mp h).symm
    obtain ⟨x, y, hxy⟩ := hKq.2.2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥K) x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥K) y
    refine hxy ?_
    simp only [← map_mul, hab2 a b]
  · exact le_antisymm hKΔ (Subgroup.subgroupOf_eq_top.mp htop)

private theorem a2s_solvable_map {G : Type*} [Group G] (n : G) (H : Subgroup G)
    (hH : Group.IsSolvable H) :
    Group.IsSolvable (H.map (MulAut.conj n).toMonoidHom) := by
  haveI := hH
  exact Group.isSolvable_of_surjective
    (f := ((MulAut.conj n).toMonoidHom.subgroupMap H)) (MonoidHom.subgroupMap_surjective _ _)

private theorem a2s_not_solvable {G : Type*} [Group G] (n : G) (R : Fin 3 → Subgroup G)
    (hcomm : ∀ k l : Fin 3, k ≠ l → ∀ x ∈ R k, ∀ z ∈ R l, Commute x z)
    (hconj : ∀ k : Fin 3, (R k).map (MulAut.conj n).toMonoidHom = R (finRotate 3 k))
    {K : Subgroup G} (hKE : K ≤ ⨆ k, R k) (hKp : commutator K = ⊤) (hKn : Nontrivial K)
    (hsolv : Group.IsSolvable (R 0)) : False := by
  have h1 : Group.IsSolvable (R 1) := by
    have := a2s_solvable_map n (R 0) hsolv
    rwa [hconj 0] at this
  have h2 : Group.IsSolvable (R 2) := by
    have := a2s_solvable_map n (R 1) h1
    rwa [hconj 1] at this
  haveI := hsolv; haveI := h1; haveI := h2
  have c12 : ∀ (x : ↥(R 1)) (y : ↥(R 2)), Commute ((R 1).subtype x) ((R 2).subtype y) :=
    fun x y => hcomm 1 2 (by decide) x x.2 y y.2
  obtain ⟨φ12, h12r, h12⟩ : ∃ φ12 : ↥(R 1) × ↥(R 2) →* G, φ12.range = R 1 ⊔ R 2 ∧
      ∀ y : ↥(R 1), ∀ z : ↥(R 2), φ12 (y, z) = (y : G) * z := by
    refine ⟨MonoidHom.noncommCoprod (R 1).subtype (R 2).subtype c12, ?_, fun y z => rfl⟩
    rw [MonoidHom.noncommCoprod_range]; simp
  have c0 : ∀ (x : ↥(R 0)) (p : ↥(R 1) × ↥(R 2)), Commute ((R 0).subtype x) (φ12 p) := by
    intro x p
    obtain ⟨y, z⟩ := p
    rw [h12]
    exact (hcomm 0 1 (by decide) x x.2 y y.2).mul_right (hcomm 0 2 (by decide) x x.2 z z.2)
  obtain ⟨φ, hφr⟩ : ∃ φ : ↥(R 0) × (↥(R 1) × ↥(R 2)) →* G, φ.range = ⨆ k, R k := by
    refine ⟨MonoidHom.noncommCoprod (R 0).subtype φ12 c0, ?_⟩
    rw [MonoidHom.noncommCoprod_range, h12r]
    simp only [Subgroup.range_subtype]
    apply le_antisymm
    · exact sup_le (le_iSup R 0) (sup_le (le_iSup R 1) (le_iSup R 2))
    · refine iSup_le fun k => ?_
      fin_cases k
      · exact le_sup_left
      · exact le_sup_of_le_right le_sup_left
      · exact le_sup_of_le_right le_sup_right
  haveI : Group.IsSolvable (↥φ.range) := Group.isSolvable_of_surjective (f := φ.rangeRestrict)
    φ.rangeRestrict_surjective
  have hE : Group.IsSolvable (↥(⨆ k, R k)) := by
    rw [← hφr]; exact this
  haveI := hE
  haveI : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion hKE) (Subgroup.inclusion_injective hKE)
  have := Group.IsSolvable.commutator_lt_top_of_nontrivial K
  rw [hKp] at this
  exact lt_irrefl _ this

theorem ntpA2_split
    (hS : LangNontoralStructure) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup .E6 L p₀) (a : Fin Tag.E6.rank → Lˣ) (n : ModGL .E6 L)
    (hpair : OrderThreeOutsideConnected S a n) (hker : (rootCharKernel a).ncard = 18)
    (hfix : ∀ i : KernelComponent (rootCharHom a),
        componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    (K : Subgroup (ModGL .E6 L))
    (hK : IsComponentOf K (S.Γ ⊓ Subgroup.centralizer
      ((Subgroup.zpowers (rootDiagUnit .E6 a) ⊔ Subgroup.zpowers n : Subgroup (ModGL .E6 L)) :
        Set (ModGL .E6 L)))) :
    GGCompFieldAt S.D.q K := by
  classical
  have hpair' := hpair
  obtain ⟨hap, hT, h1, hnM, hn3, hcommd, -⟩ := hpair'
  obtain ⟨hcard3, σ, hσne, hσ3, hσspan, hcompat, hlayer⟩ := hS L p₀ S a n hpair hker
  haveI hFin : Finite (KernelComponent (rootCharHom a)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard3]; norm_num)
  letI : Fintype (KernelComponent (rootCharHom a)) := Fintype.ofFinite _
  have hcardF : Fintype.card (KernelComponent (rootCharHom a)) = 3 := by
    rw [← Nat.card_eq_fintype_card]; exact hcard3
  obtain ⟨e, he⟩ := exists_equiv_finRotate hcardF σ hσne hσ3
  obtain ⟨R, hRdef⟩ : ∃ R : Fin 3 → Subgroup (ModGL .E6 L), ∀ k,
      R k = rationalComponent S.ρ S.Γ (rootCharHom a) (e k) := ⟨_, fun _ => rfl⟩
  have hcomm : ∀ k l : Fin 3, k ≠ l → ∀ x ∈ R k, ∀ z ∈ R l, Commute x z := by
    intro k l hkl x hx z hz
    have hb := a2s_commutator_rationalComponent_eq_bot S hfix
      (i := e k) (j := e l) (fun h => hkl (e.injective h))
    rw [← hRdef k, ← hRdef l] at hb
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hb
    exact (Subgroup.mem_centralizer_iff.mp (hle hx) z hz).symm
  have hconj : ∀ k : Fin 3, (R k).map (MulAut.conj n).toMonoidHom = R (finRotate 3 k) := by
    intro k
    have h := a2s_conj_rationalComponent S hfix hnM σ hσspan (e k)
    rw [he k] at h
    rw [hRdef k, hRdef (finRotate 3 k)]
    exact h
  have hnmem : n ∈ (Subgroup.zpowers (rootDiagUnit .E6 a) ⊔ Subgroup.zpowers n :
      Subgroup (ModGL .E6 L)) := Subgroup.mem_sup_right (Subgroup.mem_zpowers n)
  have hdmem : rootDiagUnit .E6 a ∈ (Subgroup.zpowers (rootDiagUnit .E6 a) ⊔ Subgroup.zpowers n :
      Subgroup (ModGL .E6 L)) := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hKC := hK.1
  have hKΓ : K ≤ S.Γ := hKC.trans inf_le_left
  have hKcent := hKC.trans inf_le_right
  have hKn : ∀ g ∈ K, n * g * n⁻¹ = g := by
    intro g hg
    have := Subgroup.mem_centralizer_iff.mp (hKcent hg) n hnmem
    rw [mul_inv_eq_iff_eq_mul]; exact this
  have hKd : K ≤ Subgroup.centralizer ({rootDiagUnit .E6 a} : Set (ModGL .E6 L)) := by
    intro g hg
    refine Subgroup.mem_centralizer_iff.mpr (fun h hh => ?_)
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact Subgroup.mem_centralizer_iff.mp (hKcent hg) _ hdmem
  have hKq : CFSG.IsQuasisimple ↥K :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥K).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open ↥K).mpr hK.2.2)
  have hKE : K ≤ ⨆ k, R k := by
    have h := hlayer K (le_inf hKΓ hKd) hKq
    have hEI : ⨆ k, R k = ⨆ i, rationalComponent S.ρ S.Γ (rootCharHom a) i := by
      simp_rw [hRdef]
      exact Equiv.iSup_comp (g := fun i => rationalComponent S.ρ S.Γ (rootCharHom a) i) e
    rw [hEI]; exact h
  haveI hKnt : Nontrivial ↥K := by
    haveI := hKq.2.1.toNontrivial
    exact (QuotientGroup.mk_surjective (s := Subgroup.center ↥K)).nontrivial
  have h3L : ((3 : ℕ) : L) ≠ 0 := by
    intro h
    have h2 : (2 : L) = 0 := by exact_mod_cast CharP.cast_eq_zero L 2
    have h3 : (3 : L) = 0 := by exact_mod_cast h
    have : (1 : L) = 0 := by
      calc (1 : L) = 3 - 2 := by norm_num
        _ = 0 := by rw [h3, h2]; simp
    exact one_ne_zero this
  have hR0q : CFSG.IsQuasisimple ↥(R 0) := by
    rcases CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.langSetup_tame_of_prime S
        (p := 3) Nat.prime_three h3L (fun h => absurd h (by decide)) hT hap h1 (e 0) with hq | hsolv
    · rw [hRdef 0]; exact hq
    · exfalso
      exact a2s_not_solvable n R hcomm hconj hKE hKq.1.commutator_eq_top hKnt
        (by rw [hRdef 0]; exact hsolv)
  have hn3' : n ^ 3 = 1 := hn3
  have hr0 : finRotate 3 0 = 1 := by decide
  have hr1 : finRotate 3 1 = 2 := by decide
  have hmem1 : ∀ r ∈ R 0, n * r * n⁻¹ ∈ R 1 := by
    intro r hr
    have h : n * r * n⁻¹ ∈ (R 0).map (MulAut.conj n).toMonoidHom := ⟨r, hr, by simp⟩
    rwa [hconj 0, hr0] at h
  have hmem2 : ∀ r ∈ R 0, n ^ 2 * r * (n ^ 2)⁻¹ ∈ R 2 := by
    intro r hr
    have h : n * (n * r * n⁻¹) * n⁻¹ ∈ (R 1).map (MulAut.conj n).toMonoidHom :=
      ⟨_, hmem1 r hr, by simp⟩
    rw [hconj 1, hr1] at h
    have e2 : n * (n * r * n⁻¹) * n⁻¹ = n ^ 2 * r * (n ^ 2)⁻¹ := by
      simp only [pow_two, mul_inv_rev]; group
    rwa [e2] at h
  have hcomm0 : ∀ r ∈ R 0, ∀ s ∈ R 0, Commute r (n * s * n⁻¹) := fun r hr s hs =>
    hcomm 0 1 (by decide) r hr _ (hmem1 s hs)
  let δ : ↥(R 0) →* ModGL .E6 L :=
    { toFun := fun r => cycConjDiag n (r : ModGL .E6 L)
      map_one' := by simp [cycConjDiag]
      map_mul' := fun r s => cycConjDiag_mul n (R 0) hn3' hcomm0 r.2 s.2 }
  have hδ : ∀ r : ↥(R 0), δ r = (r : ModGL .E6 L) * (n * (r : ModGL .E6 L) * n⁻¹) *
      (n ^ 2 * (r : ModGL .E6 L) * (n ^ 2)⁻¹) := fun r => rfl
  have hδE : ∀ r : ↥(R 0), δ r ∈ ⨆ k, R k := by
    intro r
    rw [hδ]
    exact mul_mem (mul_mem (le_iSup R 0 r.2) (le_iSup R 1 (hmem1 r r.2)))
      (le_iSup R 2 (hmem2 r r.2))
  have hδn : ∀ r : ↥(R 0), n * δ r * n⁻¹ = δ r := fun r =>
    cycConjDiag_conj n (R 0) hn3' hcomm0 r.2
  have hYcent : ∀ i : KernelComponent (rootCharHom a), componentRootSpan L (rootCharHom a) i ≤
      Subgroup.centralizer ({rootDiagUnit .E6 a} : Set (ModGL .E6 L)) := fun i =>
    (componentRootSpan_le L i).trans (rootSpan_le_centralizer a
      (S := kernelRoots (rootCharHom a)) (fun α hα => hα))
  have hRle : ∀ k, R k ≤ componentRootSpan L (rootCharHom a) (e k) ⊓ S.Γ := by
    intro k
    rw [hRdef k, a2s_rationalComponent_eq S hfix (e k)]
    refine Subgroup.commutator_le.mpr (fun g₁ h₁ g₂ h₂ => ?_)
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
  have hRΓ : ∀ k, R k ≤ S.Γ := fun k => (hRle k).trans inf_le_right
  have hRd : ∀ k, R k ≤ Subgroup.centralizer ({rootDiagUnit .E6 a} : Set (ModGL .E6 L)) :=
    fun k => ((hRle k).trans inf_le_left).trans (hYcent (e k))
  have hEΓ : (⨆ k, R k) ≤ S.Γ := iSup_le hRΓ
  have hEd : (⨆ k, R k) ≤ Subgroup.centralizer ({rootDiagUnit .E6 a} : Set (ModGL .E6 L)) :=
    iSup_le hRd
  have hrangeC : δ.range ≤ S.Γ ⊓ Subgroup.centralizer
      ((Subgroup.zpowers (rootDiagUnit .E6 a) ⊔ Subgroup.zpowers n : Subgroup (ModGL .E6 L)) :
        Set (ModGL .E6 L)) := by
    rintro _ ⟨r, rfl⟩
    refine ⟨hEΓ (hδE r), ?_⟩
    have hdc : δ r ∈ Subgroup.centralizer ({rootDiagUnit .E6 a} : Set (ModGL .E6 L)) :=
      hEd (hδE r)
    have hnc : δ r ∈ Subgroup.centralizer ({n} : Set (ModGL .E6 L)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := hδn r
      rw [mul_inv_eq_iff_eq_mul] at h
      exact h.symm
    have hM : (Subgroup.zpowers (rootDiagUnit .E6 a) ⊔ Subgroup.zpowers n :
        Subgroup (ModGL .E6 L)) ≤ Subgroup.centralizer ({δ r} : Set (ModGL .E6 L)) := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact ((Subgroup.mem_centralizer_singleton_iff.mp hdc)).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact ((Subgroup.mem_centralizer_singleton_iff.mp hnc)).symm
    refine Subgroup.mem_centralizer_iff.mpr (fun h hh => ?_)
    have := Subgroup.mem_centralizer_singleton_iff.mp (hM hh)
    exact this
  have hker : δ.ker ≤ Subgroup.center ↥(R 0) := by
    intro r hr
    have hr1 : δ r = 1 := hr
    rw [hδ] at hr1
    rw [Subgroup.mem_center_iff]
    intro t
    have hx := hmem1 r r.2
    have hy := hmem2 r r.2
    have hrr : (r : ModGL .E6 L) =
        ((n * (r : ModGL .E6 L) * n⁻¹) * (n ^ 2 * (r : ModGL .E6 L) * (n ^ 2)⁻¹))⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact hr1)
    have hcx : Commute (t : ModGL .E6 L) (n * (r : ModGL .E6 L) * n⁻¹) :=
      hcomm 0 1 (by decide) t t.2 _ hx
    have hcy : Commute (t : ModGL .E6 L) (n ^ 2 * (r : ModGL .E6 L) * (n ^ 2)⁻¹) :=
      hcomm 0 2 (by decide) t t.2 _ hy
    have hct : Commute (t : ModGL .E6 L) (r : ModGL .E6 L) := by
      rw [hrr]; exact (hcx.mul_right hcy).inv_right
    exact Subtype.ext hct.eq
  have hΔq : CFSG.IsQuasisimple ↥δ.range := a2s_isQuasisimple_range δ hker hR0q
  have hKΔ : K ≤ δ.range := by
    have h1' : K ≤ ⁅K, K⁆ := by
      intro g hg
      have hmem : (⟨g, hg⟩ : ↥K) ∈ ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ := by
        have h := hKq.1.commutator_eq_top
        change ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ at h
        rw [h]; exact Subgroup.mem_top _
      have h := Subgroup.mem_map_of_mem K.subtype hmem
      rwa [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
    have h2 : ⁅K, K⁆ ≤ δ.range := by
      refine Subgroup.commutator_le.mpr (fun g₁ hg₁ g₂ hg₂ => ?_)
      obtain ⟨b₁, hb₁, z₁, hz₁, rfl⟩ := exists_eq_cycConjDiag_mul_of_fixed n hn3' hcomm hconj
        (hKE hg₁) (hKn g₁ hg₁)
      obtain ⟨b₂, hb₂, z₂, hz₂, rfl⟩ := exists_eq_cycConjDiag_mul_of_fixed n hn3' hcomm hconj
        (hKE hg₂) (hKn g₂ hg₂)
      have hu : cycConjDiag n b₁ = δ ⟨b₁, hb₁⟩ := rfl
      have hv : cycConjDiag n b₂ = δ ⟨b₂, hb₂⟩ := rfl
      rw [hu, hv]
      have h1v : Commute z₁ (δ ⟨b₂, hb₂⟩) :=
        (Subgroup.mem_centralizer_iff.mp hz₁.2 _ (hδE _)).symm
      have h2u : Commute z₂ (δ ⟨b₁, hb₁⟩) :=
        (Subgroup.mem_centralizer_iff.mp hz₂.2 _ (hδE _)).symm
      have h12 : Commute z₁ z₂ := (Subgroup.mem_centralizer_iff.mp hz₁.2 _ hz₂.1).symm
      rw [CFSG.LocalAnalysis.ComponentInitial.commutatorElement_mul_mul_of_commute h1v h12 h2u,
        ← map_commutatorElement]
      exact ⟨_, rfl⟩
    exact h1'.trans h2
  have hΔq' : CFSG.Open.IsQuasisimple ↥δ.range :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open ↥δ.range).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native
        ↥δ.range).mpr hΔq)
  have hKeq : K = δ.range :=
    a2s_eq_of_isComponentOf_le_of_quasisimple
      (CFSG.Assembly.isComponentOf_iff_open.mpr hK) hKΔ hrangeC hΔq' hKq
  have hδK : ∀ r : ↥(R 0), δ r ∈ K := fun r => by
    rw [hKeq]; exact ⟨r, rfl⟩
  let ψ : ↥(R 0) →* ↥K := δ.codRestrict K hδK
  have hψs : Function.Surjective ψ := by
    intro k
    have hk : (k : ModGL .E6 L) ∈ δ.range := by rw [← hKeq]; exact k.2
    obtain ⟨r, hr⟩ := hk
    exact ⟨r, Subtype.ext hr⟩
  have hψker : ψ.ker ≤ Subgroup.center ↥(R 0) := by
    intro r hr
    apply hker
    rw [MonoidHom.mem_ker] at hr ⊢
    exact congrArg Subtype.val hr
  obtain ⟨θ⟩ :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.StarAux.nonempty_quotientCenterEquiv_of_central_ker
      ψ hψs hψker hR0q.1.commutator_eq_top
  have hSL := CFSG.StandardType.LangRat.langRatCompFieldLenSL_holds .E6 L p₀ S (Or.inl rfl) 3
    Nat.prime_three (by norm_num) a hT hap h1 (e 0) (by rw [← hRdef 0]; exact hR0q)
  rw [hfix (e 0), pow_one] at hSL
  have hAt : GGCompFieldAt S.D.q (R 0) := by rw [hRdef 0]; exact hSL.toAt
  exact ntpA2_ggCompFieldAt_of_centerQuotEquiv (X := R 0) (Y := K) θ hAt

end CFSG.StandardType.NTPlane

end
