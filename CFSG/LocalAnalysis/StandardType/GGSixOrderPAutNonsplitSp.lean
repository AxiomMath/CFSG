module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitSpOrder
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalInnerSp
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLNonsplitGroup
public import CFSG.RankThree.SubgroupLists.SymplecticTransvections

public section

namespace CFSG.StandardType

namespace OrdPNsSp

open Matrix Module SUTB NoOffOm OrdPNsGen CFSG.RankThree.SubgroupLists
  CFSG.Assembly.LowTwoRank

variable {n : ℕ} {K : Type} [Field K]

abbrev spIdx (n : ℕ) : Fin n ⊕ Fin n ≃ Fin (n + n) := finSumFinEquiv

variable (n K) in
@[expose] noncomputable def spReindex : GL (Fin n ⊕ Fin n) K ≃* GL (Fin (n + n)) K :=
  Units.mapEquiv (Matrix.reindexAlgEquiv K K (spIdx n)).toMulEquiv

theorem coe_spReindex (A : GL (Fin n ⊕ Fin n) K) :
    ((spReindex n K A : GL (Fin (n + n)) K) : Matrix (Fin (n + n)) (Fin (n + n)) K) =
      (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K).reindex (spIdx n) (spIdx n) :=
  rfl

variable (n K) in
@[expose] noncomputable def spFormD : (Fin (n + n) → K) →ₗ[K] (Fin (n + n) → K) →ₗ[K] K :=
  (spForm n K).compl₁₂ (LinearMap.funLeft K K (spIdx n)) (LinearMap.funLeft K K (spIdx n))

theorem spFormD_apply (v w : Fin (n + n) → K) :
    spFormD n K v w = spForm n K (v ∘ spIdx n) (w ∘ spIdx n) := rfl

theorem glin_spReindex (A : GL (Fin n ⊕ Fin n) K) (v : Fin (n + n) → K) :
    glin (spReindex n K A) v =
      ((A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ (v ∘ spIdx n)) ∘ (spIdx n).symm := by
  rw [glin_apply, coe_spReindex, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv,
    Equiv.symm_symm]

theorem spFormD_glin (A : GL (Fin n ⊕ Fin n) K) (v w : Fin (n + n) → K) :
    spFormD n K (glin (spReindex n K A) v) (glin (spReindex n K A) w) =
      spForm n K ((A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ (v ∘ spIdx n))
        ((A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ (w ∘ spIdx n)) := by
  have h : ∀ u : Fin n ⊕ Fin n → K, (u ∘ (spIdx n).symm) ∘ spIdx n = u := fun u => by
    funext x
    simp
  rw [spFormD_apply, glin_spReindex, glin_spReindex, h, h]

theorem spReindex_mem_isoGL_iff (A : GL (Fin n ⊕ Fin n) K) :
    spReindex n K A ∈ isoGL (spFormD n K) ↔ A ∈ StatedSp n K := by
  rw [mem_isoGL, mem_statedSp_iff_preserves]
  constructor
  · intro h x y
    have h1 := h (x ∘ (spIdx n).symm) (y ∘ (spIdx n).symm)
    rw [spFormD_glin, spFormD_apply] at h1
    simpa [Function.comp_assoc] using h1
  · intro h v w
    rw [spFormD_glin, h, spFormD_apply]

theorem spFormD_isAlt (v : Fin (n + n) → K) : spFormD n K v v = 0 := by
  rw [spFormD_apply]
  exact spForm_self _

theorem spFormD_isSymm [CharP K 2] : (spFormD n K).IsSymm := ⟨fun v w => by
  rw [RingHom.id_apply, spFormD_apply, spFormD_apply,
    ← LinearMap.BilinForm.IsAlt.neg_eq spForm_isAlt, CharTwo.neg_eq]⟩

theorem spFormD_sep (v : Fin (n + n) → K) (hv : ∀ w, spFormD n K v w = 0) : v = 0 := by
  have h1 : v ∘ spIdx n = 0 := spForm_separatingLeft _ fun x => by
    have h2 := hv (x ∘ (spIdx n).symm)
    rw [spFormD_apply] at h2
    simpa [Function.comp_assoc] using h2
  funext i
  have h3 := congrFun h1 ((spIdx n).symm i)
  simpa using h3

section Setting

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Universal.Symplectic

theorem exists_conj_mem_centralizer {G : Type} [Group G] [Finite G] {p : ℕ} {f : ℕ}
    {Bs G₀ : Subgroup G} {ψ : StatedSp n (GaloisField 2 f) →* G}
    (hS : GGSixFusionSetting p Bs G₀ (Symplectic.rootDatum n (GaloisField 2 f)) .PSp n f ψ)
    {y : G} (hyp : y ^ p = 1) (hy : GGPsiInnerDiag (Symplectic.rootDatum n (GaloisField 2 f)) ψ y) :
    ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField 2 f with hFdef
  obtain ⟨⟨hadm, hrank⟩, ⟨hrange, hker⟩, -, -⟩ := hS.presents
  have hf : 1 ≤ f := hadm.2.1
  have hrk : 2 ≤ n := hrank
  have hpp := hS.prime
  have hp2 := hS.ne_two
  have : CharP F 2 := inferInstance
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact hS.centralizer_eq_bot
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hz := hker ha
    rw [Symplectic.center_eq,
      CFSG.LieType.SteinbergBR.EvenSp.statedScalars_subgroupOf_statedSp (by omega)] at hz
    exact Subgroup.mem_bot.mp hz
  have hinner : ∀ c : G, GGPsiInnerDiag (Symplectic.rootDatum n F) ψ c → c ∈ ψ.range := by
    intro c hc
    obtain ⟨g, hg, hcg⟩ := PsiDiag.Symp.exists_mem_centralizer (F := F) hrk ψ hker hc
    rw [hC, Subgroup.mem_bot] at hcg
    rw [eq_inv_of_mul_eq_one_left hcg]
    exact ψ.range.inv_mem hg
  obtain ⟨u₀, rfl⟩ := hinner _ hy
  have hu₀p : u₀ ^ p = 1 := hinj (by rw [map_pow, hyp, map_one])
  by_cases hu1 : u₀ = 1
  · refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [hu1, map_one, inv_one, one_mul, one_mul]
    exact Subgroup.one_mem _
  set B := spFormD n F with hB
  set φ : StatedSp n F →* GL (Fin (n + n)) F :=
    (spReindex n F).toMonoidHom.comp (StatedSp n F).subtype with hφ
  have hφinj : Function.Injective φ := fun a b hab =>
    Subtype.ext ((spReindex n F).injective hab)
  have hφiso : ∀ s : StatedSp n F, φ s ∈ isoGL B := fun s =>
    (spReindex_mem_isoGL_iff (s : GL (Fin n ⊕ Fin n) F)).mpr s.2
  have hφsurj : ∀ g ∈ isoGL B, ∃ s : StatedSp n F, φ s = g := by
    intro g hg
    refine ⟨⟨(spReindex n F).symm g, ?_⟩, ?_⟩
    · rw [← spReindex_mem_isoGL_iff, MulEquiv.apply_symm_apply]
      exact hg
    · change spReindex n F ((spReindex n F).symm g) = g
      exact MulEquiv.apply_symm_apply _ g
  have hBs : B.IsSymm := spFormD_isSymm
  have hBalt : ∀ v, B v v = 0 := spFormD_isAlt
  have hBsep : ∀ v, (∀ w, B v w = 0) → v = 0 := spFormD_sep
  have hp1 : 1 ≤ p := hpp.one_lt.le
  have hBsψ : Bs ≤ ψ.range := fun b hb => hinner b (hS.innerDiag b hb)
  set A := (Bs.comap ψ).map φ with hA
  have hAmax : GenMax B (isoGL B) p A := by
    refine ⟨hBs, hBsep, hpp, hp2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨s, -, rfl⟩
      exact hφiso s
    · rintro _ ⟨s, hs, rfl⟩
      rw [← map_pow]
      have h1 : s ^ p = 1 := hinj (by rw [map_pow, map_one]; exact hS.elem.2 _ hs)
      rw [h1, map_one]
    · rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
      rw [← map_mul, ← map_mul]
      have h1 : s * t = t * s :=
        hinj (by rw [map_mul, map_mul]; exact TableB.IsElemAbelian.comm hS.elem hs ht)
      rw [h1]
    · intro g hg hgp hgA
      obtain ⟨s, rfl⟩ := hφsurj g hg
      have hsp : s ^ p = 1 := hφinj (by rw [map_pow, hgp, map_one])
      have hsc : ψ s ∈ Subgroup.centralizer (Bs : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        obtain ⟨t, rfl⟩ := hBsψ hb
        have h1 := hgA (φ t) ⟨t, hb, rfl⟩
        rw [← map_mul, ← map_mul] at h1
        rw [← map_mul, ← map_mul, hφinj h1]
      exact ⟨s, hS.omega _ hsc (by rw [← map_pow, hsp, map_one]), rfl⟩
    · intro g hg v w
      obtain ⟨s, -, rfl⟩ := hg
      exact hφiso s v w
    · intro c hc W hW hWA
      have hcp : glin c ^ p = 1 := by
        obtain ⟨s, hs, rfl⟩ := hc
        have h1 : s ^ p = 1 := hinj (by rw [map_pow, map_one]; exact hS.elem.2 _ hs)
        rw [← glin_pow, ← map_pow, h1, map_one, glin_one]
      have hciso : c ∈ isoGL B := by
        obtain ⟨s, -, rfl⟩ := hc
        exact hφiso s
      have hzp := restrictElt_pow_eq_one hW (hWA c hc) hcp
      obtain ⟨g, hg⟩ := exists_gl_of_pow hp1 hzp
      refine ⟨g, ?_, hg⟩
      intro v w
      rw [hg]
      exact restrictElt_isometry hW _ hBs hciso v w
  have hAcard : Nat.card A = Nat.card Bs := by
    rw [hA, Subgroup.card_map_of_injective hφinj]
    have h1 : (Bs.comap ψ).map ψ = Bs := Subgroup.map_comap_eq_self hBsψ
    rw [← Subgroup.card_map_of_injective hinj, h1]
  obtain ⟨E, hE, huE⟩ := exists_genMax_mem hBs hBsep hpp hp2 (hφiso u₀)
    (by rw [← map_pow, hu₀p, map_one])
  have hne : ∃ c ∈ E, c ≠ 1 := ⟨φ u₀, huE, fun h1 => hu1 (hφinj (by rw [h1, map_one]))⟩
  have hcardE : Nat.card A ≤ Nat.card E :=
    (card_le_pow_lcm hBalt hAmax).trans (pow_lcm_le_card hBalt hE (fun g hg => hg) hne)
  set E₀ := E.comap φ with hE₀
  have hE₀map : E₀.map φ = E := Subgroup.map_comap_eq_self fun g hg => by
    obtain ⟨s, rfl⟩ := hφsurj g (hE.le hg)
    exact ⟨s, rfl⟩
  have hE₀card : Nat.card E₀ = Nat.card E := by
    rw [← Subgroup.card_map_of_injective hφinj, hE₀map]
  have hE₀el : IsElemAbelian p (E₀.map ψ) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, s, hs, rfl⟩ := a
      obtain ⟨_, t, ht, rfl⟩ := b
      apply Subtype.ext
      change ψ s * ψ t = ψ t * ψ s
      have h1 : s * t = t * s := hφinj (by rw [map_mul, map_mul]; exact hE.comm _ hs _ ht)
      rw [← map_mul, ← map_mul, h1]
    · rintro _ ⟨s, hs, rfl⟩
      have h1 : s ^ p = 1 := hφinj (by rw [map_pow, map_one]; exact hE.pow _ hs)
      rw [← map_pow, h1, map_one]
  have hEM : E₀.map ψ ≤ Subgroup.normalizer (G₀ : Set G) := by
    rintro _ ⟨s, -, rfl⟩
    exact Subgroup.le_normalizer (hrange ▸ ⟨s, rfl⟩)
  refine OrdPNS.exists_conj_mem_centralizer_of_card hS hEM hE₀el ?_ ?_
  · rw [Subgroup.card_map_of_injective hinj, hE₀card, ← hAcard]
    exact hcardE
  · rintro _ ⟨s, hs, rfl⟩
    have h1 : u₀ * s = s * u₀ := hφinj (by rw [map_mul, map_mul]; exact hE.comm _ huE _ hs)
    rw [← map_mul, ← map_mul, h1]

end Setting

end OrdPNsSp

section Family

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

theorem ggOrdPInnerConjPSpNonsplit_holds : GGOrdPInnerConjPSpNonsplit := by
  intro G _ _ p Bs G₀ n f ψ hS _ _ y _ hyo hy
  have hyp : y ^ p = 1 := hyo ▸ pow_orderOf_eq_one y
  exact OrdPNsSp.exists_conj_mem_centralizer hS hyp hy

theorem ggOrdPInnerConjAt_PSp : GGOrdPInnerConjAt .PSp :=
  ggOrdPInnerConjAt_PSp_of_nonsplit ggOrdPInnerConjPSpNonsplit_holds

end Family

end CFSG.StandardType
