module

public import CFSG.LocalAnalysis.StandardType.GGTBJOmTauOm
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
public import CFSG.LocalAnalysis.StandardType.GGTBJSuTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.ComponentInitial.BlockCentralQuotient

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB OrthExc
open CFSG.RankThree.Classical2 (orthDerived)

private theorem ggTBJOmTorAux_card_V (p r : ℕ) :
    Nat.card (Fin r → Multiplicative (ZMod p)) = p ^ r := by
  rw [Nat.card_fun, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod,
    Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem ggTBJOmTorAux_card_centralizer {V : Type} [Group V] {L' : Type} [Group L']
    {A : Subgroup (MulAut L')} {σ : V →* L'} (Θ : V ≃* ↥A)
    (hΘ : ∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f)) (J : Subgroup L') :
    Nat.card ↥(A ⊓ ⨅ j : J, MulAction.stabilizer (MulAut L') (j : L')) =
      Nat.card {f : V // ∀ j ∈ J, σ f * j = j * σ f} := by
  classical
  refine Nat.card_congr ?_
  let toF : ↥(A ⊓ ⨅ j : J, MulAction.stabilizer (MulAut L') (j : L')) →
      {f : V // ∀ j ∈ J, σ f * j = j * σ f} := fun b =>
    let f : V := Θ.symm ⟨(b : MulAut L'), (Subgroup.mem_inf.mp b.2).1⟩
    ⟨f, by
      intro j hj
      have hbj : (b : MulAut L') j = j := by
        have h := MulAction.mem_stabilizer_iff.mp
          (Subgroup.mem_iInf.mp (Subgroup.mem_inf.mp b.2).2 ⟨j, hj⟩)
        simpa [MulAut.smul_def] using h
      have hbf : (b : MulAut L') = MulAut.conj (σ f) := by
        have hfA : Θ f = (⟨(b : MulAut L'), (Subgroup.mem_inf.mp b.2).1⟩ : ↥A) :=
          MulEquiv.apply_symm_apply Θ _
        rw [← hΘ f]
        exact (congrArg Subtype.val hfA).symm
      rw [hbf, MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at hbj
      exact hbj⟩
  let toG : {f : V // ∀ j ∈ J, σ f * j = j * σ f} →
      ↥(A ⊓ ⨅ j : J, MulAction.stabilizer (MulAut L') (j : L')) :=
    fun c => ⟨((Θ c.1 : ↥A) : MulAut L'), by
      refine Subgroup.mem_inf.mpr ⟨(Θ c.1).2, ?_⟩
      rw [Subgroup.mem_iInf]
      intro j
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def, hΘ, MulAut.conj_apply]
      have hcomm := c.2 j j.2
      rw [hcomm]
      group⟩
  refine ⟨toF, toG, ?_, ?_⟩
  · intro b
    apply Subtype.ext
    simp only [toF, toG]
    rw [MulEquiv.apply_symm_apply]
  · intro c
    apply Subtype.ext
    simp only [toF, toG]
    rw [MulEquiv.symm_apply_eq]

private theorem ggTBJOmTorAux_component {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {R : Type} [Group R] {eR : R ≃* ↥(orthDerived Q)} {p r : ℕ} {L' : Type} [Group L']
    {ψ₀ : L' →* R}
    (hψsurj : Function.Surjective ψ₀) (hker : ψ₀.ker ≤ Subgroup.center L')
    {E : Subgroup (V ≃ₗ[K] V)}
    {Δ : OrthTorus.TBJOmData Q p E r}
    {hE : E ≤ orthDerived Q}
    {σ : (Fin r → Multiplicative (ZMod p)) →* L'}
    {A : Subgroup (MulAut L')} {Θ : (Fin r → Multiplicative (ZMod p)) ≃* ↥A}
    (hψσ : ∀ f, ψ₀ (σ f) = eR.symm (Δ.τΩ hE f))
    (hΘ : ∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f))
    {y : MulAut L'} (hy : y ∈ A) {J : Subgroup L'}
    (hJ : CFSG.Open.IsComponentOf J
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup y)) :
    ∃ f₀ : Fin r → Multiplicative (ZMod p),
      y = MulAut.conj (σ f₀) ∧
      CFSG.Assembly.IsComponentOf ((J.map ψ₀).map eR.toMonoidHom)
        (Subgroup.centralizer ({Δ.τΩ hE f₀} :
          Set ↥(orthDerived Q))) := by
  let f₀ : Fin r → Multiplicative (ZMod p) := Θ.symm ⟨y, hy⟩
  have hΘf₀ : Θ f₀ = ⟨y, hy⟩ := MulEquiv.apply_symm_apply Θ _
  have hy_eq : y = MulAut.conj (σ f₀) := by
    have h := hΘ f₀
    rw [hΘf₀] at h
    exact h
  have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup y =
      Subgroup.centralizer ({σ f₀} : Set L') := by
    rw [hy_eq]
    exact ggTBJ_fixSubgroup_conj (σ f₀)
  have hJcent : CFSG.Open.IsComponentOf J (Subgroup.centralizer ({σ f₀} : Set L')) := by
    rw [hfix] at hJ
    exact hJ
  have hJ' : CFSG.Open.IsComponentOf J
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj (σ f₀))) := by
    rw [ggTBJ_fixSubgroup_conj]
    exact hJcent
  have hJgg : CFSG.Assembly.IsComponentOf J (ggFix (MulAut.conj (σ f₀))) :=
    (isComponentOf_iff_open).mpr hJ'
  have hc : ∀ l : L', MulAut.conj (ψ₀ (σ f₀)) (ψ₀ l) = ψ₀ (MulAut.conj (σ f₀) l) := by
    intro l
    rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hSfix : CFSG.Assembly.IsComponentOf (J.map ψ₀)
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (MulAut.conj (ψ₀ (σ f₀)))) :=
    USixTwo.isComponentOf_map_fix hψsurj hker hc hJgg
  have hScent : CFSG.Assembly.IsComponentOf (J.map ψ₀)
      (Subgroup.centralizer ({ψ₀ (σ f₀)} : Set R)) := by
    rw [← ggTBJ_fixSubgroup_conj (ψ₀ (σ f₀))]
    exact hSfix
  refine ⟨f₀, hy_eq, ?_⟩
  have hm := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective hScent
    eR.toMonoidHom eR.injective
  rw [CFSG.LocalAnalysis.ComponentInitial.map_centralizer_singleton_mulEquiv
    eR (ψ₀ (σ f₀)), hψσ f₀,
    MulEquiv.apply_symm_apply] at hm
  exact hm

private theorem ggTBJOmTorAux_centralize_iff {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {R : Type} [Group R] {eR : R ≃* ↥(orthDerived Q)} {p r : ℕ} {L' : Type} [Group L']
    {ψ₀ : L' →* R} (hker : ψ₀.ker ≤ Subgroup.center L')
    {E : Subgroup (V ≃ₗ[K] V)}
    {Δ : OrthTorus.TBJOmData Q p E r}
    {hE : E ≤ orthDerived Q}
    {σ : (Fin r → Multiplicative (ZMod p)) →* L'}
    (hψσ : ∀ f, ψ₀ (σ f) = eR.symm (Δ.τΩ hE f))
    {J : Subgroup L'} (hJperf : ⁅J, J⁆ = J) :
    ∀ f : Fin r → Multiplicative (ZMod p),
      (∀ j ∈ J, σ f * j = j * σ f) ↔
      (∀ j' ∈ (J.map ψ₀).map eR.toMonoidHom,
        Δ.τΩ hE f * j' = j' * Δ.τΩ hE f) := by
  intro f
  constructor
  · intro h j' hj'
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hj'
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hu
    have h1 : Δ.τΩ hE f = eR (ψ₀ (σ f)) := by
      rw [hψσ f, MulEquiv.apply_symm_apply]
    have h2 : ψ₀ (σ f) * ψ₀ j = ψ₀ j * ψ₀ (σ f) := by
      rw [← map_mul, ← map_mul, h j hj]
    rw [h1]
    change eR (ψ₀ (σ f)) * eR (ψ₀ j) = eR (ψ₀ j) * eR (ψ₀ (σ f))
    rw [← MulEquiv.map_mul eR (ψ₀ (σ f)) (ψ₀ j),
      ← MulEquiv.map_mul eR (ψ₀ j) (ψ₀ (σ f)), h2]
  · intro h j hj
    have hj' : eR (ψ₀ j) ∈ (J.map ψ₀).map eR.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨ψ₀ j, Subgroup.mem_map.mpr ⟨j, hj, rfl⟩, rfl⟩
    have hkerj : ∀ t ∈ J, MulAut.conj (σ f) t * t⁻¹ ∈ ψ₀.ker := by
      intro t ht
      rw [MonoidHom.mem_ker]
      have ht' : eR (ψ₀ t) ∈ (J.map ψ₀).map eR.toMonoidHom :=
        Subgroup.mem_map.mpr ⟨ψ₀ t, Subgroup.mem_map.mpr ⟨t, ht, rfl⟩, rfl⟩
      have hcomm : ψ₀ t * ψ₀ (σ f) = ψ₀ (σ f) * ψ₀ t := by
        have h1 : eR (ψ₀ (σ f)) = Δ.τΩ hE f := by
          rw [hψσ f, MulEquiv.apply_symm_apply]
        apply eR.injective
        rw [map_mul, map_mul, h1]
        exact (h _ ht').symm
      rw [MulAut.conj_apply, map_mul, map_inv, map_mul, map_mul, map_inv]
      calc ψ₀ (σ f) * ψ₀ t * (ψ₀ (σ f))⁻¹ * (ψ₀ t)⁻¹
          = ψ₀ t * ψ₀ (σ f) * (ψ₀ (σ f))⁻¹ * (ψ₀ t)⁻¹ := by rw [← hcomm]
        _ = 1 := by group
    have hfixj := USixTwo.fix_of_perfect hker hJperf hkerj j hj
    rw [MulAut.conj_apply] at hfixj
    exact mul_inv_eq_iff_eq_mul.mp hfixj

private theorem ggTBJOmTorAux_hcore_input {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {R : Type} [Group R] {eR : R ≃* ↥(orthDerived Q)} {p r : ℕ} {L' : Type} [Group L']
    {ψ₀ : L' →* R}
    (hψsurj : Function.Surjective ψ₀) (hker : ψ₀.ker ≤ Subgroup.center L')
    {E : Subgroup (V ≃ₗ[K] V)}
    {Δ : OrthTorus.TBJOmData Q p E r}
    {hE : E ≤ orthDerived Q}
    {σ : (Fin r → Multiplicative (ZMod p)) →* L'}
    {A : Subgroup (MulAut L')} {Θ : (Fin r → Multiplicative (ZMod p)) ≃* ↥A}
    (hψσ : ∀ f, ψ₀ (σ f) = eR.symm (Δ.τΩ hE f))
    (hΘ : ∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f))
    {y : MulAut L'} (hy : y ∈ A) {J : Subgroup L'}
    (hJ : CFSG.Open.IsComponentOf J
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup y))
    (hcount : p ^ 2 * Nat.card ↥(A ⊓ ⨅ j : J, MulAction.stabilizer (MulAut L') (j : L')) ≤
      Nat.card ↥A) :
    ∃ f₀ : Fin r → Multiplicative (ZMod p),
      CFSG.Assembly.IsComponentOf ((J.map ψ₀).map eR.toMonoidHom)
        (Subgroup.centralizer ({Δ.τΩ hE f₀} :
          Set ↥(orthDerived Q))) ∧
      p ^ 2 * Nat.card {f : Fin r → Multiplicative (ZMod p) //
        ∀ j ∈ (J.map ψ₀).map eR.toMonoidHom,
        Δ.τΩ hE f * j = j * Δ.τΩ hE f} ≤ p ^ r := by
  obtain ⟨f₀, -, hJ'comp⟩ := ggTBJOmTorAux_component hψsurj hker hψσ hΘ hy hJ
  have hJperf : ⁅J, J⁆ = J := by
    rw [← Subgroup.map_subtype_commutator, hJ.2.2.1, Subgroup.map_top,
      Subgroup.range_subtype]
  have hcardB := ggTBJOmTorAux_card_centralizer Θ hΘ J
  have hcardA : Nat.card ↥A = p ^ r := by
    rw [← Nat.card_congr Θ.toEquiv]
    exact ggTBJOmTorAux_card_V p r
  have hcount' : p ^ 2 * Nat.card {f : Fin r → Multiplicative (ZMod p) //
      ∀ j ∈ J, σ f * j = j * σ f} ≤ p ^ r := by
    rw [← hcardB, ← hcardA]
    exact hcount
  have hiff := ggTBJOmTorAux_centralize_iff hker hψσ hJperf
  have hPQ : Nat.card {f : Fin r → Multiplicative (ZMod p) //
        ∀ j' ∈ (J.map ψ₀).map eR.toMonoidHom,
        Δ.τΩ hE f * j' = j' * Δ.τΩ hE f} =
      Nat.card {f : Fin r → Multiplicative (ZMod p) // ∀ j ∈ J, σ f * j = j * σ f} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun f => (hiff f).symm)
  refine ⟨f₀, hJ'comp, ?_⟩
  rw [hPQ]
  exact hcount'

private theorem ggTBJOmTorAux_lift {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {R : Type} [Group R] {eR : R ≃* ↥(orthDerived Q)} {p r : ℕ} {L' : Type} [Group L']
    {ψ₀ : L' →* R}
    {E : Subgroup (V ≃ₗ[K] V)}
    {Δ : OrthTorus.TBJOmData Q p E r}
    {hE : E ≤ orthDerived Q}
    {σ : (Fin r → Multiplicative (ZMod p)) →* L'}
    (hψσ : ∀ f, ψ₀ (σ f) = eR.symm (Δ.τΩ hE f))
    {J : Subgroup L'} {n : ↥(orthDerived Q)}
    (hn : n ∈ (J.map ψ₀).map eR.toMonoidHom)
    {s : MulAut (Fin r → Multiplicative (ZMod p))}
    (hform : ∀ f, n * Δ.τΩ hE f * n⁻¹ = Δ.τΩ hE (s f)) :
    ∃ l ∈ J, eR (ψ₀ l) = n ∧
      ∀ f, ψ₀ l * ψ₀ (σ f) * (ψ₀ l)⁻¹ = ψ₀ (σ (s f)) := by
  obtain ⟨u, hu, hueq⟩ := Subgroup.mem_map.mp hn
  obtain ⟨l, hlJ, hleq⟩ := Subgroup.mem_map.mp hu
  have heq : eR (ψ₀ l) = n := by
    rw [hleq]
    exact hueq
  refine ⟨l, hlJ, heq, ?_⟩
  intro f
  apply eR.injective
  rw [map_mul, map_mul, map_inv, hψσ f, hψσ (s f), MulEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply, heq]
  exact hform f

private theorem ggTBJOmTorAux_assemble {V : Type} [Group V] {p r : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hV : Nat.card V = p ^ r)
    {L' : Type} [Group L'] [Finite L'] {R : Type} [Group R]
    {ψ₀ : L' →* R} (hker : ψ₀.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')} {σ : V →* L'} (Θ : V ≃* ↥A)
    (hΘ : ∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f))
    (hWeyl : ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      GGTorusWeylElt p A n)
    {l₁ l₂ : L'} {s₁ s₂ : MulAut V}
    (hψform₁ : ∀ f, ψ₀ l₁ * ψ₀ (σ f) * (ψ₀ l₁)⁻¹ = ψ₀ (σ (s₁ f)))
    (hψform₂ : ∀ f, ψ₀ l₂ * ψ₀ (σ f) * (ψ₀ l₂)⁻¹ = ψ₀ (σ (s₂ f)))
    (hs₁ : s₁ ^ 2 = 1) (hs₂ : s₂ ^ 2 = 1)
    (hfix₁ : Nat.card {f : V // s₁ f = f} * p = p ^ r)
    (hfix₂ : Nat.card {f : V // s₂ f = f} * p = p ^ r)
    (hne : s₁ * s₂ ≠ s₂ * s₁) :
    ∃ (h₁ : MulAut.conj l₁ ∈ Subgroup.normalizer (A : Set (MulAut L')))
      (h₂ : MulAut.conj l₂ ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      GGTorusWeylElt p A l₁ ∧ GGTorusWeylElt p A l₂ ∧
      GGIsReflection p (ggConjAut A h₁) ∧ GGIsReflection p (ggConjAut A h₂) ∧
      ggConjAut A h₁ * ggConjAut A h₂ ≠ ggConjAut A h₂ * ggConjAut A h₁ := by
  obtain ⟨h₁, heq₁⟩ := exists_ggConjAut_eq_congr (V := V) (ψ := ψ₀)
    (A := A) (σ := σ) hker Θ hΘ (n := l₁) (s := s₁) hψform₁
  obtain ⟨h₂, heq₂⟩ := exists_ggConjAut_eq_congr (V := V) (ψ := ψ₀)
    (A := A) (σ := σ) hker Θ hΘ (n := l₂) (s := s₂) hψform₂
  have hfixV₁ : Nat.card {f : V // s₁ f = f} * p = Nat.card V := by
    rw [hV]
    exact hfix₁
  have hfixV₂ : Nat.card {f : V // s₂ f = f} * p = Nat.card V := by
    rw [hV]
    exact hfix₂
  have hrefl₁ : GGIsReflection p (MulAut.congr Θ s₁) :=
    ⟨by rw [← map_pow, hs₁, map_one],
      (ggIsPseudoReflection_congr Θ (SpCoord.pow_sub_one_eq_one_of_sq hp hp2 hs₁) hfixV₁).2⟩
  have hrefl₂ : GGIsReflection p (MulAut.congr Θ s₂) :=
    ⟨by rw [← map_pow, hs₂, map_one],
      (ggIsPseudoReflection_congr Θ (SpCoord.pow_sub_one_eq_one_of_sq hp hp2 hs₂) hfixV₂).2⟩
  have hrefl₁' : GGIsReflection p (ggConjAut A h₁) := by rw [heq₁]; exact hrefl₁
  have hrefl₂' : GGIsReflection p (ggConjAut A h₂) := by rw [heq₂]; exact hrefl₂
  have hne' : MulAut.congr Θ s₁ * MulAut.congr Θ s₂ ≠
      MulAut.congr Θ s₂ * MulAut.congr Θ s₁ := by
    intro h
    apply hne
    apply (MulAut.congr Θ).injective
    rw [map_mul, map_mul]
    exact h
  have hconjne : ggConjAut A h₁ * ggConjAut A h₂ ≠
      ggConjAut A h₂ * ggConjAut A h₁ := by
    rw [heq₁, heq₂]
    exact hne'
  exact ⟨h₁, h₂, hWeyl l₁ h₁, hWeyl l₂ h₂, hrefl₁', hrefl₂', hconjne⟩

theorem ggTBJ_om_torus_transport {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {R : Type}
    [Group R] {eR : R ≃* ↥(orthDerived Q)} {p r r₀ : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {L' : Type} [Group L'] [Finite L'] (ψ₀ : L' →* R) (A : Subgroup (MulAut L'))
    (hA : GGTorusTBGroup p r₀ R (Set.range (MulAut.conj : R →* MulAut R)) L' ψ₀ A)
    {E : Subgroup (V ≃ₗ[K] V)} (Δ : OrthTorus.TBJOmData Q p E r) (hE : E ≤ orthDerived Q)
    (σ : (Fin r → Multiplicative (ZMod p)) →* L') (Θ : (Fin r → Multiplicative (ZMod p)) ≃* ↥A)
    (hψσ : ∀ f, ψ₀ (σ f) = eR.symm (Δ.τΩ hE f))
    (hΘ : ∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f))
    (hWeyl : ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      GGTorusWeylElt p A n)
    (hcore : ∀ (f₀ : Fin r → Multiplicative (ZMod p)) (J' : Subgroup ↥(orthDerived Q)),
      CFSG.Assembly.IsComponentOf J'
          (Subgroup.centralizer ({Δ.τΩ hE f₀} : Set ↥(orthDerived Q))) →
        p ^ 2 * Nat.card {f : Fin r → Multiplicative (ZMod p) //
          ∀ j ∈ J', Δ.τΩ hE f * j = j * Δ.τΩ hE f} ≤ p ^ r →
        ∃ (n₁ n₂ : ↥(orthDerived Q)) (s₁ s₂ : MulAut (Fin r → Multiplicative (ZMod p))),
          n₁ ∈ J' ∧ n₂ ∈ J' ∧ (∀ f, n₁ * Δ.τΩ hE f * n₁⁻¹ = Δ.τΩ hE (s₁ f)) ∧
          (∀ f, n₂ * Δ.τΩ hE f * n₂⁻¹ = Δ.τΩ hE (s₂ f)) ∧ s₁ ^ 2 = 1 ∧ s₂ ^ 2 = 1 ∧
          Nat.card {f : Fin r → Multiplicative (ZMod p) // s₁ f = f} * p = p ^ r ∧
          Nat.card {f : Fin r → Multiplicative (ZMod p) // s₂ f = f} * p = p ^ r ∧
          s₁ * s₂ ≠ s₂ * s₁)
    (y : MulAut L') (hy : y ∈ A) {J : Subgroup L'}
    (hJ : CFSG.Open.IsComponentOf J (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup y))
    (hcount : p ^ 2 * Nat.card ↥(A ⊓ ⨅ j : J, MulAction.stabilizer (MulAut L') (j : L')) ≤
      Nat.card ↥A) :
    ∃ (n₁ n₂ : L') (h₁ : MulAut.conj n₁ ∈ Subgroup.normalizer (A : Set (MulAut L')))
      (h₂ : MulAut.conj n₂ ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      n₁ ∈ J ∧ n₂ ∈ J ∧ GGTorusWeylElt p A n₁ ∧ GGTorusWeylElt p A n₂ ∧
      GGIsReflection p (ggConjAut A h₁) ∧ GGIsReflection p (ggConjAut A h₂) ∧
      ggConjAut A h₁ * ggConjAut A h₂ ≠ ggConjAut A h₂ * ggConjAut A h₁ := by
  classical
  obtain ⟨f₀, hJ'comp, hcount_core⟩ :=
    ggTBJOmTorAux_hcore_input hA.1 hA.2.1 hψσ hΘ hy hJ hcount
  obtain ⟨n₁, n₂, s₁, s₂, hn₁, hn₂, hform₁, hform₂, hs₁, hs₂, hfix₁, hfix₂, hne⟩ :=
    hcore f₀ ((J.map ψ₀).map eR.toMonoidHom) hJ'comp hcount_core
  obtain ⟨l₁, hl₁J, -, hψform₁⟩ := ggTBJOmTorAux_lift (J := J) hψσ hn₁ hform₁
  obtain ⟨l₂, hl₂J, -, hψform₂⟩ := ggTBJOmTorAux_lift (J := J) hψσ hn₂ hform₂
  obtain ⟨h₁, h₂, hw₁, hw₂, hr₁, hr₂, hne'⟩ :=
    ggTBJOmTorAux_assemble hp hp2 (ggTBJOmTorAux_card_V p r) hA.2.1 Θ hΘ hWeyl
      hψform₁ hψform₂ hs₁ hs₂ hfix₁ hfix₂ hne
  exact ⟨l₁, l₂, h₁, h₂, hl₁J, hl₂J, hw₁, hw₂, hr₁, hr₂, hne'⟩

end CFSG.StandardType

end
