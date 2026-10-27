module

public import CFSG.LocalAnalysis.StandardType.GGTBJOmTorus
public import CFSG.LocalAnalysis.StandardType.GGTBJOmAutomizer
public import CFSG.LocalAnalysis.StandardType.GGTBJOmCompFixed
public import CFSG.LocalAnalysis.StandardType.GGTBJOmCompNf
public import CFSG.LocalAnalysis.StandardType.GGTBJFrameBs

public section

namespace CFSG.StandardType

namespace OrthTorus

open CFSG CFSG.Assembly SpCoord
open CFSG.RankThree.Classical2 (orthDerived)

theorem eq_of_map_eq_of_center_prime {L' R : Type} [Group L'] [Group R] {ψ₀ : L' →* R} {p : ℕ}
    (hker : ψ₀.ker ≤ Subgroup.center L') (hZ : ∀ z ∈ Subgroup.center L', z ^ p = 1 → z = 1)
    {a b : L'} (ha : a ^ p = 1) (hb : b ^ p = 1) (h : ψ₀ a = ψ₀ b) : a = b := by
  have hz : a⁻¹ * b ∈ Subgroup.center L' :=
    hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel])
  have hcomm : Commute a (a⁻¹ * b) := Subgroup.mem_center_iff.mp hz a
  have hp : (a⁻¹ * b) ^ p = 1 := by
    have hb' : b = a * (a⁻¹ * b) := by group
    have h2 : b ^ p = a ^ p * (a⁻¹ * b) ^ p := by
      conv_lhs => rw [hb']
      exact hcomm.mul_pow p
    rw [hb, ha, one_mul] at h2
    exact h2.symm
  have h3 := hZ _ hz hp
  calc a = a * (a⁻¹ * b) := by rw [h3, mul_one]
    _ = b := by group

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {R : Type} [Group R]
  {eR : R ≃* ↥(orthDerived Q)} {p r : ℕ} {L' : Type} [Group L'] {ψ₀ : L' →* R}
  {E : Subgroup (V ≃ₗ[K] V)} {Δ : TBJOmData Q p E r} {hE : E ≤ orthDerived Q}
  {σ : (Fin r → Multiplicative (ZMod p)) →* L'}

theorem sectionFrameAut_eq_torusAut (hker : ψ₀.ker ≤ Subgroup.center L')
    (hZ : ∀ z ∈ Subgroup.center L', z ^ p = 1 → z = 1)
    (hψσ : ∀ f, ψ₀ (σ f) = eR.symm (Δ.τΩ hE f)) (J : Subgroup L') :
    FrameBs.sectionFrameAut σ J = Δ.torusAut hE ((J.map ψ₀).map eR.toMonoidHom) := by
  have hpσ : ∀ f, σ f ^ p = 1 := fun f => by
    rw [← map_pow, ReflInner.pow_eq_one_of_zmod f, map_one]
  have hτ : ∀ f, eR (ψ₀ (σ f)) = Δ.τΩ hE f := fun f => by
    rw [hψσ f, MulEquiv.apply_symm_apply]
  ext τ
  constructor
  · rintro ⟨n, hn, h⟩
    refine ⟨eR (ψ₀ n), Subgroup.mem_map.mpr ⟨ψ₀ n, Subgroup.mem_map.mpr ⟨n, hn, rfl⟩, rfl⟩,
      fun f => ?_⟩
    have h1 := congrArg (fun x => eR (ψ₀ x)) (h f)
    simp only [map_mul, map_inv, hτ] at h1
    exact h1
  · rintro ⟨j, hj, h⟩
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hj
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hu
    refine ⟨n, hn, fun f => ?_⟩
    refine eq_of_map_eq_of_center_prime hker hZ ?_ (hpσ _) ?_
    · rw [conj_pow, hpσ, mul_one, mul_inv_cancel]
    · apply eR.injective
      have h1 := h f
      simp only [map_mul, map_inv, hτ]
      exact h1

private theorem tbjAut_card_V (p r : ℕ) :
    Nat.card (Fin r → Multiplicative (ZMod p)) = p ^ r := FrameBs.card_zmodFrame p r

theorem card_stabilizer_frame_eq_card_centralizer {V' : Type} [Group V'] {L'' : Type} [Group L'']
    {A : Subgroup (MulAut L'')} {σ' : V' →* L''} (Θ : V' ≃* ↥A)
    (hΘ : ∀ f, ((Θ f : ↥A) : MulAut L'') = MulAut.conj (σ' f)) (J : Subgroup L'') :
    Nat.card ↥(A ⊓ ⨅ j : J, MulAction.stabilizer (MulAut L'') (j : L'')) =
      Nat.card {f : V' // ∀ j ∈ J, σ' f * j = j * σ' f} := by
  classical
  refine Nat.card_congr ?_
  let toF : ↥(A ⊓ ⨅ j : J, MulAction.stabilizer (MulAut L'') (j : L'')) →
      {f : V' // ∀ j ∈ J, σ' f * j = j * σ' f} := fun b =>
    let f : V' := Θ.symm ⟨(b : MulAut L''), (Subgroup.mem_inf.mp b.2).1⟩
    ⟨f, by
      intro j hj
      have hbj : (b : MulAut L'') j = j := by
        have h := MulAction.mem_stabilizer_iff.mp
          (Subgroup.mem_iInf.mp (Subgroup.mem_inf.mp b.2).2 ⟨j, hj⟩)
        simpa [MulAut.smul_def] using h
      have hbf : (b : MulAut L'') = MulAut.conj (σ' f) := by
        have hfA : Θ f = (⟨(b : MulAut L''), (Subgroup.mem_inf.mp b.2).1⟩ : ↥A) :=
          MulEquiv.apply_symm_apply Θ _
        rw [← hΘ f]
        exact (congrArg Subtype.val hfA).symm
      rw [hbf, MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at hbj
      exact hbj⟩
  let toG : {f : V' // ∀ j ∈ J, σ' f * j = j * σ' f} →
      ↥(A ⊓ ⨅ j : J, MulAction.stabilizer (MulAut L'') (j : L'')) :=
    fun c => ⟨((Θ c.1 : ↥A) : MulAut L''), by
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

private theorem tbjAut_component
    (hψsurj : Function.Surjective ψ₀) (hker : ψ₀.ker ≤ Subgroup.center L')
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

private theorem tbjAut_centralize_iff (hker : ψ₀.ker ≤ Subgroup.center L')
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

private theorem tbjAut_hcore_input {k : ℕ}
    (hψsurj : Function.Surjective ψ₀) (hker : ψ₀.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')} {Θ : (Fin r → Multiplicative (ZMod p)) ≃* ↥A}
    (hψσ : ∀ f, ψ₀ (σ f) = eR.symm (Δ.τΩ hE f))
    (hΘ : ∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f))
    {y : MulAut L'} (hy : y ∈ A) {J : Subgroup L'}
    (hJ : CFSG.Open.IsComponentOf J
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup y))
    (hcount : p ^ k * Nat.card ↥(A ⊓ ⨅ j : J, MulAction.stabilizer (MulAut L') (j : L')) ≤
      Nat.card ↥A) :
    ∃ f₀ : Fin r → Multiplicative (ZMod p),
      y = MulAut.conj (σ f₀) ∧
      CFSG.Assembly.IsComponentOf ((J.map ψ₀).map eR.toMonoidHom)
        (Subgroup.centralizer ({Δ.τΩ hE f₀} :
          Set ↥(orthDerived Q))) ∧
      p ^ k * Nat.card {f : Fin r → Multiplicative (ZMod p) //
        ∀ j ∈ (J.map ψ₀).map eR.toMonoidHom,
        Δ.τΩ hE f * j = j * Δ.τΩ hE f} ≤ p ^ r := by
  obtain ⟨f₀, hy_eq, hJ'comp⟩ := tbjAut_component hψsurj hker hψσ hΘ hy hJ
  have hJperf : ⁅J, J⁆ = J := by
    rw [← Subgroup.map_subtype_commutator, hJ.2.2.1, Subgroup.map_top,
      Subgroup.range_subtype]
  have hcardB := card_stabilizer_frame_eq_card_centralizer Θ hΘ J
  have hcardA : Nat.card ↥A = p ^ r := by
    rw [← Nat.card_congr Θ.toEquiv]
    exact tbjAut_card_V p r
  have hcount' : p ^ k * Nat.card {f : Fin r → Multiplicative (ZMod p) //
      ∀ j ∈ J, σ f * j = j * σ f} ≤ p ^ r := by
    rw [← hcardB, ← hcardA]
    exact hcount
  have hiff := tbjAut_centralize_iff hker hψσ hJperf
  have hPQ : Nat.card {f : Fin r → Multiplicative (ZMod p) //
        ∀ j' ∈ (J.map ψ₀).map eR.toMonoidHom,
        Δ.τΩ hE f * j' = j' * Δ.τΩ hE f} =
      Nat.card {f : Fin r → Multiplicative (ZMod p) // ∀ j ∈ J, σ f * j = j * σ f} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun f => (hiff f).symm)
  refine ⟨f₀, hy_eq, hJ'comp, ?_⟩
  rw [hPQ]
  exact hcount'

private theorem tbjAut_map_top (hψsurj : Function.Surjective ψ₀) :
    (((⊤ : Subgroup L').map ψ₀).map eR.toMonoidHom) = ⊤ := by
  rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top_of_surjective _ hψsurj, Subgroup.map_top]
  exact MonoidHom.range_eq_top_of_surjective _ eR.surjective

theorem sectionFrameAut_top_nf [Fact p.Prime] (hp2 : p ≠ 2)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (hψsurj : Function.Surjective ψ₀) (hker : ψ₀.ker ≤ Subgroup.center L')
    (hZ : ∀ z ∈ Subgroup.center L', z ^ p = 1 → z = 1)
    (hψσ : ∀ f, ψ₀ (σ f) = eR.symm (Δ.τΩ hE f))
    (hnf : ∀ v : V, (∀ a ∈ E, a v = v) → v = 0) :
    FrameBs.sectionFrameAut σ ⊤ = TypeDDatum.evenSignedAut r p := by
  rw [sectionFrameAut_eq_torusAut hker hZ hψσ, tbjAut_map_top hψsurj]
  exact Δ.torusAut_top_nf hp2 hQ hT hE hnf

theorem sectionFrameAut_top_fixed [Fact p.Prime] (hp2 : p ≠ 2)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (hψsurj : Function.Surjective ψ₀) (hker : ψ₀.ker ≤ Subgroup.center L')
    (hZ : ∀ z ∈ Subgroup.center L', z ^ p = 1 → z = 1)
    (hψσ : ∀ f, ψ₀ (σ f) = eR.symm (Δ.τΩ hE f))
    (hW : ∃ v : V, v ≠ 0 ∧ ∀ a ∈ E, a v = v) :
    FrameBs.sectionFrameAut σ ⊤ = TypeBDatum.signedAut r p := by
  rw [sectionFrameAut_eq_torusAut hker hZ hψσ, tbjAut_map_top hψsurj]
  exact Δ.torusAut_top_fixed hp2 hQ hT hE hW

theorem ggTBJ_om_torus_aut_nf [Fact p.Prime] (hp2 : p ≠ 2)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (hψsurj : Function.Surjective ψ₀) (hker : ψ₀.ker ≤ Subgroup.center L')
    (hZ : ∀ z ∈ Subgroup.center L', z ^ p = 1 → z = 1)
    {A : Subgroup (MulAut L')} {Θ : (Fin r → Multiplicative (ZMod p)) ≃* ↥A}
    (hψσ : ∀ f, ψ₀ (σ f) = eR.symm (Δ.τΩ hE f))
    (hΘ : ∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f))
    (hnf : ∀ v : V, (∀ a ∈ E, a v = v) → v = 0)
    {y : MulAut L'} (hy : y ∈ A) (hy1 : y ≠ 1) {J : Subgroup L'}
    (hJ : CFSG.Open.IsComponentOf J
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup y))
    (hcount : p ^ 2 * Nat.card ↥(A ⊓ ⨅ j : J, MulAction.stabilizer (MulAut L') (j : L')) ≤
      Nat.card ↥A) :
    ∃ S : Finset (Fin r),
      (∀ f : Fin r → Multiplicative (ZMod p), (∀ τ ∈ FrameBs.sectionFrameAut σ J, τ f = f) →
        ∀ j ∈ J, σ f * j = j * σ f) ∧
      ((3 ≤ S.card ∧ S ≠ Finset.univ ∧
          FrameBs.sectionFrameAut σ J = TypeDDatum.evenSignedSupportedAut r p S) ∨
        ∃ (s : Fin r → ZMod p) (hs : ∀ i, s i * s i = 1), 2 ≤ S.card ∧
          FrameBs.sectionFrameAut σ J = TypeBDatum.twistedPermAut r p S s hs) := by
  classical
  obtain ⟨f₀, hy_eq, hJ'comp, hcnt⟩ := tbjAut_hcore_input hψsurj hker hψσ hΘ hy hJ hcount
  have hf₀ : f₀ ≠ 1 := by
    rintro rfl
    apply hy1
    rw [hy_eq, map_one, map_one]
  obtain ⟨S, hfix, hshape⟩ :=
    Δ.torusAut_component_nf hp2 hQ hT hE hnf hf₀ hJ'comp hcnt
  have hJperf : ⁅J, J⁆ = J := by
    rw [← Subgroup.map_subtype_commutator, hJ.2.2.1, Subgroup.map_top, Subgroup.range_subtype]
  have hFA := sectionFrameAut_eq_torusAut hker hZ hψσ J
  refine ⟨S, fun f hf j hj => ?_, by rw [hFA]; exact hshape⟩
  have h1 := (tbjAut_centralize_iff hker hψσ hJperf f).mpr
    (hfix f (fun τ hτ => hf τ (by rw [hFA]; exact hτ)))
  exact h1 j hj

theorem ggTBJ_om_torus_aut_fixed [Fact p.Prime] (hp2 : p ≠ 2)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (hψsurj : Function.Surjective ψ₀) (hker : ψ₀.ker ≤ Subgroup.center L')
    (hZ : ∀ z ∈ Subgroup.center L', z ^ p = 1 → z = 1)
    {A : Subgroup (MulAut L')} {Θ : (Fin r → Multiplicative (ZMod p)) ≃* ↥A}
    (hψσ : ∀ f, ψ₀ (σ f) = eR.symm (Δ.τΩ hE f))
    (hΘ : ∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f))
    (hW : ∃ v : V, v ≠ 0 ∧ ∀ a ∈ E, a v = v)
    {y : MulAut L'} (hy : y ∈ A) (hy1 : y ≠ 1) {J : Subgroup L'}
    (hJ : CFSG.Open.IsComponentOf J
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup y))
    (hcount : p ^ 2 * Nat.card ↥(A ⊓ ⨅ j : J, MulAction.stabilizer (MulAut L') (j : L')) ≤
      Nat.card ↥A) :
    ∃ S : Finset (Fin r),
      (∀ f : Fin r → Multiplicative (ZMod p), (∀ τ ∈ FrameBs.sectionFrameAut σ J, τ f = f) →
        ∀ j ∈ J, σ f * j = j * σ f) ∧
      ((1 ≤ S.card ∧ S ≠ Finset.univ ∧
          FrameBs.sectionFrameAut σ J = TypeBDatum.signedSupportedAut r p S) ∨
        ∃ (s : Fin r → ZMod p) (hs : ∀ i, s i * s i = 1), 2 ≤ S.card ∧
          FrameBs.sectionFrameAut σ J = TypeBDatum.twistedPermAut r p S s hs) := by
  classical
  obtain ⟨f₀, hy_eq, hJ'comp, hcnt⟩ := tbjAut_hcore_input hψsurj hker hψσ hΘ hy hJ hcount
  have hf₀ : f₀ ≠ 1 := by
    rintro rfl
    apply hy1
    rw [hy_eq, map_one, map_one]
  obtain ⟨S, hfix, hshape⟩ :=
    Δ.torusAut_component_fixed hp2 hQ hT hE hW hf₀ hJ'comp hcnt
  have hJperf : ⁅J, J⁆ = J := by
    rw [← Subgroup.map_subtype_commutator, hJ.2.2.1, Subgroup.map_top, Subgroup.range_subtype]
  have hFA := sectionFrameAut_eq_torusAut hker hZ hψσ J
  refine ⟨S, fun f hf j hj => ?_, ?_⟩
  · have h1 := (tbjAut_centralize_iff hker hψσ hJperf f).mpr
      (hfix f (fun τ hτ => hf τ (by rw [hFA]; exact hτ)))
    exact h1 j hj
  · rw [hFA]
    rcases hshape with ⟨hS, hSne, hEq⟩ | ⟨s, hs, hS, hEq⟩
    · exact Or.inl ⟨le_trans (by norm_num : 1 ≤ 2) hS, hSne, hEq⟩
    · exact Or.inr ⟨s, hs, le_trans (by norm_num : 2 ≤ 3) hS, hEq⟩

theorem ggTBJ_om_component_eq_supportedFixedDerived_one_active [Fact p.Prime] (hp2 : p ≠ 2)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hψsurj : Function.Surjective ψ₀) (hker : ψ₀.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')} {Θ : (Fin r → Multiplicative (ZMod p)) ≃* ↥A}
    (hψσ : ∀ f, ψ₀ (σ f) = eR.symm (Δ.τΩ hE f))
    (hΘ : ∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f))
    (hW : ∃ v : V, v ≠ 0 ∧ ∀ a ∈ E, a v = v) (hr : 3 ≤ r)
    {y : MulAut L'} (hy : y ∈ A) {J : Subgroup L'}
    (hJ : CFSG.Open.IsComponentOf J
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup y))
    {j : Fin r}
    (hj : (Θ.symm ⟨y, hy⟩) j ≠ 1)
    (hf : ∀ i, i ≠ j → (Θ.symm ⟨y, hy⟩) i = 1)
    (hcount : p ^ (r - 1) * Nat.card ↥(A ⊓ ⨅ z : J,
      MulAction.stabilizer (MulAut L') (z : L')) ≤ Nat.card ↥A) :
    ((J.map ψ₀).map eR.toMonoidHom) =
      (CFSG.RankThree.PartOne.KCOrthogonal.supportedFixedDerived Q
        (Δ.τ (Θ.symm ⟨y, hy⟩))).subgroupOf (orthDerived Q) := by
  classical
  obtain ⟨f₀, hy_eq, hJ'comp, hcnt⟩ :=
    tbjAut_hcore_input hψsurj hker hψσ hΘ hy hJ hcount
  have hΘf₀ : Θ f₀ = ⟨y, hy⟩ := by
    refine Subtype.ext ?_
    rw [hΘ f₀]
    exact hy_eq.symm
  have hf₀_eq : f₀ = Θ.symm ⟨y, hy⟩ := by
    rw [← hΘf₀, MulEquiv.symm_apply_apply]
  rw [← hf₀_eq] at hj hf
  have hnat := Δ.component_eq_supportedFixedDerived_one_active hp2 hQ hE hW hr hj hf hJ'comp hcnt
  simpa [hf₀_eq] using hnat

end OrthTorus

end CFSG.StandardType

end
