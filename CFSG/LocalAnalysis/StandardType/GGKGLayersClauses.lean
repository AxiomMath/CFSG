module

public import CFSG.LocalAnalysis.StandardType.GGKGAutDict
public import CFSG.LocalAnalysis.StandardType.GGKGLayersTheta

public section

namespace CFSG.StandardType.KGL

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KE8F CFSG.StandardType.LayerSixE
  CFSG.StandardType.TableBExc CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.NoOffRest
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem kgL1_clause {K : Type} [Field K] [Finite K] (h1 : KGAdjL1)
    (hchar : ringChar K = 2) {L' : Type} [Group L'] [Finite L']
    (ψ : L' →* RecipeGroup Tag.E6 K) (A : Subgroup (MulAut L'))
    (ζ : Kˣ) (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3) (g : ModGL Tag.E6 K)
    (hg : g ∈ adjointGroup Tag.E6 K) (κ : A →* Multiplicative (Fin 6 → ZMod 3))
    (hF : KGAutFrame A κ) (hψ : Function.Surjective ψ)
    (hconj : ∀ (a : A) (l : L'), kgThetaHom g (ψ ((a : MulAut L') l)) =
      rootDiagUnit Tag.E6 (kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a))) * kgThetaHom g (ψ l) *
        (rootDiagUnit Tag.E6 (kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a))))⁻¹) :
    ∀ c : ↥A, GGCorootPt 3 (ggTorusAut A) c →
      ∃ E : Subgroup (RecipeGroup Tag.E6 K), GGLayerOf (ggRFix ψ {(c : MulAut L')}) E := by
  intro c hc
  obtain ⟨β, hβroot, hβ⟩ := hF.corootPt hc
  refine ⟨(rootSpan Tag.E6 K (kgKernelE6 {kgZetaE6 ζ hζ (Multiplicative.toAdd (κ c))})).comap
    (kgThetaHom g), ?_⟩
  have h1' := h1 K hchar ζ hζ hζo β hβroot
  rw [← hβ] at h1'
  refine layer_of_famCentralizer ψ hψ (kgThetaHom g) (kgThetaHom_injective g)
    (kgThetaHom_range g hg) {(c : MulAut L')} {kgZetaE6 ζ hζ (Multiplicative.toAdd (κ c))}
    ?_ ?_ h1'
  · rintro f hf
    have hf_eq := Set.mem_singleton_iff.mp hf
    subst hf_eq
    exact ⟨kgZetaE6 ζ hζ (Multiplicative.toAdd (κ c)), rfl, fun l => hconj c l⟩
  · rintro a ha
    have ha_eq := Set.mem_singleton_iff.mp ha
    subst ha_eq
    exact ⟨(c : MulAut L'), rfl, fun l => hconj c l⟩

theorem kgL2_clause {K : Type} [Field K] [Finite K] (h2 : KGAdjL2)
    (hchar : ringChar K = 2) {L' : Type} [Group L'] [Finite L']
    (ψ : L' →* RecipeGroup Tag.E6 K) (A : Subgroup (MulAut L'))
    (ζ : Kˣ) (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3) (g : ModGL Tag.E6 K)
    (hg : g ∈ adjointGroup Tag.E6 K) (κ : A →* Multiplicative (Fin 6 → ZMod 3))
    (hF : KGAutFrame A κ) (hψ : Function.Surjective ψ)
    (hconj : ∀ (a : A) (l : L'), kgThetaHom g (ψ ((a : MulAut L') l)) =
      rootDiagUnit Tag.E6 (kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a))) * kgThetaHom g (ψ l) *
        (rootDiagUnit Tag.E6 (kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a))))⁻¹) :
    ∀ a b : ↥A, GGCorootOrth 3 (ggTorusAut A) a b →
      GGLayerOf (ggRFix ψ {((a : MulAut L') * (b : MulAut L'))})
        ((rootSpan Tag.E6 K
          (kgKernelE6 {kgZetaE6 ζ hζ (Multiplicative.toAdd (κ (a * b)))})).comap (kgThetaHom g)) := by
  intro a b hab
  obtain ⟨α, β, hα, hβ, hαβ, ha, hb⟩ := hF.corootOrth hab
  have h2' := h2 K hchar ζ hζ hζo α β hα hβ hαβ
  have hkey : (Multiplicative.toAdd (κ (a * b)) : Fin Tag.E6.rank → ZMod 3) =
      kgExpVec α + kgExpVec β := by
    rw [kgKappa_toAdd_mul (K := K) κ a b, ha, hb]
    rfl
  rw [← hkey] at h2'
  refine layer_of_famCentralizer ψ hψ (kgThetaHom g) (kgThetaHom_injective g) (kgThetaHom_range g hg)
    {((a : MulAut L') * (b : MulAut L'))} {kgZetaE6 ζ hζ (Multiplicative.toAdd (κ (a * b)))}
    ?_ ?_ h2'
  · rintro f hf
    have hf_eq := Set.mem_singleton_iff.mp hf
    subst hf_eq
    refine ⟨kgZetaE6 ζ hζ (Multiplicative.toAdd (κ (a * b))), rfl, fun l => ?_⟩
    rw [← Subgroup.coe_mul]
    exact hconj (a * b) l
  · rintro a' ha'
    have ha_eq := Set.mem_singleton_iff.mp ha'
    subst ha_eq
    refine ⟨(a : MulAut L') * (b : MulAut L'), rfl, fun l => ?_⟩
    rw [← Subgroup.coe_mul]
    exact hconj (a * b) l

theorem kgL3i_clause {K : Type} [Field K] [Finite K] (h3i : KGAdjL3i)
    (hchar : ringChar K = 2) {L' : Type} [Group L'] [Finite L']
    (ψ : L' →* RecipeGroup Tag.E6 K) (A : Subgroup (MulAut L'))
    (ζ : Kˣ) (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3) (g : ModGL Tag.E6 K)
    (hg : g ∈ adjointGroup Tag.E6 K) (κ : A →* Multiplicative (Fin 6 → ZMod 3))
    (hF : KGAutFrame A κ) (hψ : Function.Surjective ψ)
    (hconj : ∀ (a : A) (l : L'), kgThetaHom g (ψ ((a : MulAut L') l)) =
      rootDiagUnit Tag.E6 (kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a))) * kgThetaHom g (ψ l) *
        (rootDiagUnit Tag.E6 (kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a))))⁻¹) :
    ∀ a b : ↥A, GGCorootOrth 3 (ggTorusAut A) a b →
      GGLayerOf (ggRFix ψ {(a : MulAut L'), (b : MulAut L')})
        ((rootSpan Tag.E6 K (kgKernelE6
          {kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a)),
           kgZetaE6 ζ hζ (Multiplicative.toAdd (κ b))})).comap (kgThetaHom g)) := by
  intro a b hab
  obtain ⟨α, β, hα, hβ, hαβ, ha, hb⟩ := hF.corootOrth hab
  have h3i' := h3i K hchar ζ hζ hζo α β hα hβ hαβ
  rw [← ha, ← hb] at h3i'
  refine layer_of_famCentralizer ψ hψ (kgThetaHom g) (kgThetaHom_injective g) (kgThetaHom_range g hg)
    {(a : MulAut L'), (b : MulAut L')}
    {kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a)), kgZetaE6 ζ hζ (Multiplicative.toAdd (κ b))}
    ?_ ?_ h3i'
  · rintro f hf
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl
    · exact ⟨kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a)), by
        rw [Set.mem_insert_iff]; left; rfl, fun l => hconj a l⟩
    · exact ⟨kgZetaE6 ζ hζ (Multiplicative.toAdd (κ b)), by
        rw [Set.mem_insert_iff]; right; rfl, fun l => hconj b l⟩
  · rintro a' ha'
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ha'
    rcases ha' with rfl | rfl
    · exact ⟨(a : MulAut L'), by rw [Set.mem_insert_iff]; left; rfl, fun l => hconj a l⟩
    · exact ⟨(b : MulAut L'), by rw [Set.mem_insert_iff]; right; rfl, fun l => hconj b l⟩

theorem kgL3ii_clause {K : Type} [Field K] [Finite K] (h3ii : KGAdjL3ii)
    (hchar : ringChar K = 2) {L' : Type} [Group L'] [Finite L']
    (ψ : L' →* RecipeGroup Tag.E6 K) (A : Subgroup (MulAut L'))
    (ζ : Kˣ) (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3) (g : ModGL Tag.E6 K)
    (hg : g ∈ adjointGroup Tag.E6 K) (κ : A →* Multiplicative (Fin 6 → ZMod 3))
    (hF : KGAutFrame A κ) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (hconj : ∀ (a : A) (l : L'), kgThetaHom g (ψ ((a : MulAut L') l)) =
      rootDiagUnit Tag.E6 (kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a))) * kgThetaHom g (ψ l) *
        (rootDiagUnit Tag.E6 (kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a))))⁻¹)
    {a b : A} (hab : GGCorootOrth 3 (ggTorusAut A) a b) :
    ∀ u ∈ ggFixedByCentres 3 (ggTorusAut A) {a, b},
      ∃ l : L', ψ l ∈ (rootSpan Tag.E6 K (kgKernelE6
          {kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a)),
           kgZetaE6 ζ hζ (Multiplicative.toAdd (κ b))})).comap (kgThetaHom g) ∧
        MulAut.conj l = (u : MulAut L') := by
  intro u hu
  obtain ⟨α, β, hα, hβ, hαβ, ha, hb⟩ := hF.corootOrth hab
  have hku := hF.fixedByCentres hα hβ hαβ ha hb hu
  have hdu : rootDiagUnit Tag.E6 (kgZetaE6 ζ hζ (Multiplicative.toAdd (κ u))) ∈
      rootSpan Tag.E6 K (kgKernelE6 {kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a)),
        kgZetaE6 ζ hζ (Multiplicative.toAdd (κ b))}) := by
    refine AddSubgroup.closure_induction
      (p := fun x _ => rootDiagUnit Tag.E6 (kgZetaE6 ζ hζ x) ∈
        rootSpan Tag.E6 K (kgKernelE6 {kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a)),
          kgZetaE6 ζ hζ (Multiplicative.toAdd (κ b))})) ?_ ?_ ?_ ?_ hku
    · rintro x ⟨γ, hγ, hγα, hγβ, rfl⟩
      have h3ii' := h3ii K hchar ζ hζ hζo α β γ hα hβ hαβ hγ hγα hγβ
      rw [← ha, ← hb] at h3ii'
      convert h3ii' using 1
      congr 1
    · rw [kgZetaE6_zero, rootDiagUnit_one]
      exact one_mem _
    · intro x y hx hy hpx hpy
      rw [kgZetaE6_add, rootDiagUnit_mul]
      exact mul_mem hpx hpy
    · intro x hx hpx
      rw [kgZetaE6_neg, ← rootDiagUnit_inv]
      exact inv_mem hpx
  have hdu_adj : rootDiagUnit Tag.E6 (kgZetaE6 ζ hζ (Multiplicative.toAdd (κ u))) ∈
      adjointGroup Tag.E6 K := rootSpan_le_adjointGroup K _ hdu
  obtain ⟨r, hr⟩ := show rootDiagUnit Tag.E6 (kgZetaE6 ζ hζ (Multiplicative.toAdd (κ u))) ∈
      (kgThetaHom g).range from by rw [kgThetaHom_range g hg]; exact hdu_adj
  obtain ⟨l, rfl⟩ := hψ r
  refine ⟨l, ?_, ?_⟩
  · show kgThetaHom g (ψ l) ∈ rootSpan Tag.E6 K (kgKernelE6
      {kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a)), kgZetaE6 ζ hζ (Multiplicative.toAdd (κ b))})
    rw [hr]
    exact hdu
  · refine mulAut_eq_of_comp_eq ψ hker hperf (fun x => ?_)
    apply kgThetaHom_injective g
    rw [kgThetaHom_conj_apply g ψ l x hr, hconj u x]

theorem kgL4_clause {K : Type} [Field K] [Finite K] (h4 : KGAdjL4)
    (hchar : ringChar K = 2) {L' : Type} [Group L'] [Finite L']
    (ψ : L' →* RecipeGroup Tag.E6 K) (A : Subgroup (MulAut L'))
    (ζ : Kˣ) (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3) (g : ModGL Tag.E6 K)
    (hg : g ∈ adjointGroup Tag.E6 K) (κ : A →* Multiplicative (Fin 6 → ZMod 3))
    (hF : KGAutFrame A κ) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (hconj : ∀ (a : A) (l : L'), kgThetaHom g (ψ ((a : MulAut L') l)) =
      rootDiagUnit Tag.E6 (kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a))) * kgThetaHom g (ψ l) *
        (rootDiagUnit Tag.E6 (kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a))))⁻¹)
    {a b : A} (hab : GGCorootOrth 3 (ggTorusAut A) a b) :
    ∃ l : L', ψ l ∈ (rootSpan Tag.E6 K (kgKernelE6
        {kgZetaE6 ζ hζ (Multiplicative.toAdd (κ (a * b)))})).comap (kgThetaHom g) ∧
      MulAut.conj l ∈ Subgroup.normalizer (A : Set (MulAut L')) ∧
      MulAut.conj l * (a : MulAut L') * (MulAut.conj l)⁻¹ ≠ (a : MulAut L') := by
  obtain ⟨α, β, hα, hβ, hαβ, ha, hb⟩ := hF.corootOrth hab
  obtain ⟨j, hjmem, hjnorm, hjmove⟩ := h4 K hchar ζ hζ hζo α β hα hβ hαβ
  have hkey : (Multiplicative.toAdd (κ (a * b)) : Fin Tag.E6.rank → ZMod 3) =
      kgExpVec α + kgExpVec β := by
    rw [kgKappa_toAdd_mul (K := K) κ a b, ha, hb]
    rfl
  have hjmem' : j ∈ rootSpan Tag.E6 K
      (kgKernelE6 {kgZetaE6 ζ hζ (Multiplicative.toAdd (κ (a * b)))}) := by
    rw [hkey]
    simpa only [kgKernelE6, kgZetaE6] using hjmem
  have hjadj : j ∈ adjointGroup Tag.E6 K := rootSpan_le_adjointGroup K _ hjmem'
  obtain ⟨r, hr⟩ := show j ∈ (kgThetaHom g).range from by rw [kgThetaHom_range g hg]; exact hjadj
  obtain ⟨l, rfl⟩ := hψ r
  have hD : ∀ a₁ : A, ∃ a₂ : A, (a₂ : MulAut L') =
      MulAut.conj l * (a₁ : MulAut L') * (MulAut.conj l)⁻¹ := by
    intro a₁
    obtain ⟨y, hy, hy_eq⟩ := hjnorm (Multiplicative.toAdd (κ a₁)) (hF.toAdd_mem_hypE6 a₁)
    obtain ⟨a₂, ha₂⟩ := hF.exists_of_mem_hypE6 hy
    refine ⟨a₂, ?_⟩
    refine mulAut_eq_of_comp_eq ψ hker hperf (fun z => ?_)
    apply kgThetaHom_injective g
    rw [kgThetaHom_conjAut_apply g ψ
        (fun a => rootDiagUnit Tag.E6 (kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a)))) hconj l a₁ z hr,
      hconj a₂ z]
    simp only [kgZetaE6]
    rw [hy_eq, ← ha₂]
    rfl
  choose f hf using hD
  have hfinj : Function.Injective f := by
    intro a₁ a₂ h
    have h1 : (MulAut.conj l * (a₁ : MulAut L') * (MulAut.conj l)⁻¹) =
        (MulAut.conj l * (a₂ : MulAut L') * (MulAut.conj l)⁻¹) := by
      rw [← hf a₁, ← hf a₂, h]
    exact Subtype.ext (by
      have := congrArg (fun m : MulAut L' => (MulAut.conj l)⁻¹ * m * MulAut.conj l) h1
      simpa [mul_assoc] using this)
  have hfsurj : Function.Surjective f := (Function.Injective.bijective_of_finite hfinj).2
  have hnorm : MulAut.conj l ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
    rw [Subgroup.mem_normalizer_iff]
    intro a₁
    constructor
    · intro ha₁
      rw [← hf ⟨a₁, ha₁⟩]
      exact (f ⟨a₁, ha₁⟩).2
    · intro hb
      obtain ⟨a', ha'⟩ := hfsurj ⟨MulAut.conj l * a₁ * (MulAut.conj l)⁻¹, hb⟩
      have h1 : (MulAut.conj l * (a' : MulAut L') * (MulAut.conj l)⁻¹) =
          MulAut.conj l * a₁ * (MulAut.conj l)⁻¹ := by
        rw [← hf a', ha']
      have h2 : (a' : MulAut L') = a₁ := by
        have := congrArg (fun m : MulAut L' => (MulAut.conj l)⁻¹ * m * MulAut.conj l) h1
        simpa [mul_assoc] using this
      rw [← h2]
      exact a'.2
  refine ⟨l, ?_, hnorm, ?_⟩
  · show kgThetaHom g (ψ l) ∈ rootSpan Tag.E6 K
      (kgKernelE6 {kgZetaE6 ζ hζ (Multiplicative.toAdd (κ (a * b)))})
    rw [hr]
    exact hjmem'
  · intro hcontra
    obtain ⟨y, hy, hy_eq⟩ := hjnorm (Multiplicative.toAdd (κ a)) (hF.toAdd_mem_hypE6 a)
    obtain ⟨a₂, ha₂⟩ := hF.exists_of_mem_hypE6 hy
    have hconj_a : (a₂ : MulAut L') =
        MulAut.conj l * (a : MulAut L') * (MulAut.conj l)⁻¹ := by
      refine mulAut_eq_of_comp_eq ψ hker hperf (fun z => ?_)
      apply kgThetaHom_injective g
      rw [kgThetaHom_conjAut_apply g ψ
          (fun a => rootDiagUnit Tag.E6 (kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a)))) hconj l a z hr,
        hconj a₂ z]
      simp only [kgZetaE6]
      rw [hy_eq, ← ha₂]
      rfl
    have h_eq : a₂ = a := Subtype.ext (by rw [hconj_a, hcontra])
    have hyα : y = kgExpVec α := by rw [← ha₂, h_eq, ha]
    have hy_eq' : j * rootDiagUnit Tag.E6 (zetaVec ζ hζ (kgExpVec α)) * j⁻¹ =
        rootDiagUnit Tag.E6 (zetaVec ζ hζ y) := by
      rw [← ha]
      exact hy_eq
    have hgoal : j * rootDiagUnit Tag.E6 (zetaVec ζ hζ (kgExpVec α)) * j⁻¹ =
        rootDiagUnit Tag.E6 (zetaVec ζ hζ (kgExpVec α)) := by
      rw [hy_eq', hyα]
    exact hjmove hgoal

theorem kgM_clause {K : Type} [Field K] [Finite K] (hM : KGAdjM)
    (hchar : ringChar K = 2) {L' : Type} [Group L'] [Finite L']
    (ψ : L' →* RecipeGroup Tag.E6 K) (A : Subgroup (MulAut L'))
    (ζ : Kˣ) (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3) (g : ModGL Tag.E6 K)
    (hg : g ∈ adjointGroup Tag.E6 K) (κ : A →* Multiplicative (Fin 6 → ZMod 3))
    (hF : KGAutFrame A κ) {a b : A}
    (α β : Fin Tag.E6.rank → ℤ) (hα : IsRoot Tag.E6 α) (hβ : IsRoot Tag.E6 β)
    (hαβ : iform α β = 0) (ha : Multiplicative.toAdd (κ a) = kgExpVec α)
    (hb : Multiplicative.toAdd (κ b) = kgExpVec β) :
    ∀ (N : Type) [Group N] [Finite N]
      (π : N →* ↥((rootSpan Tag.E6 K (kgKernelE6
        {kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a)),
         kgZetaE6 ζ hζ (Multiplicative.toAdd (κ b))})).comap (kgThetaHom g))),
      Function.Surjective π → π.ker ≤ Subgroup.center N → commutator N = ⊤ →
        IsCyclic (Subgroup.center N) := by
  intro N _ _ π hπ hk hp
  have hle : rootSpan Tag.E6 K (kgKernelE6
      {kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a)),
       kgZetaE6 ζ hζ (Multiplicative.toAdd (κ b))}) ≤ adjointGroup Tag.E6 K :=
    rootSpan_le_adjointGroup K _
  have hmap : ((rootSpan Tag.E6 K (kgKernelE6
        {kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a)),
         kgZetaE6 ζ hζ (Multiplicative.toAdd (κ b))})).comap (kgThetaHom g)).map (kgThetaHom g) =
      rootSpan Tag.E6 K (kgKernelE6
        {kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a)),
         kgZetaE6 ζ hζ (Multiplicative.toAdd (κ b))}) :=
    Subgroup.map_comap_eq_self (by rw [kgThetaHom_range g hg]; exact hle)
  let e : ↥((rootSpan Tag.E6 K (kgKernelE6
        {kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a)),
         kgZetaE6 ζ hζ (Multiplicative.toAdd (κ b))})).comap (kgThetaHom g)) ≃*
        ↥(rootSpan Tag.E6 K (kgKernelE6
          {kgZetaE6 ζ hζ (Multiplicative.toAdd (κ a)),
           kgZetaE6 ζ hζ (Multiplicative.toAdd (κ b))})) :=
    (Subgroup.equivMapOfInjective _ (kgThetaHom g) (kgThetaHom_injective g)).trans
      (MulEquiv.subgroupCongr hmap)
  have hM' := hM K hchar ζ hζ hζo α β hα hβ hαβ
  rw [← ha, ← hb] at hM'
  exact isCyclic_center_of_equiv e hM' N π hπ hk hp

end CFSG.StandardType.KGL

end
