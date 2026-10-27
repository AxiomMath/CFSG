module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixETwisted
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotHR4
public import CFSG.LieType.Chevalley.GraphFixedF4Canonical
public import CFSG.LieType.Chevalley.E6SecondGraphFixedSubgroup
public import CFSG.LieType.Chevalley.GraphFixedCenterTrivial
public import CFSG.LieType.Chevalley.E6GraphFullDiagonalCoset
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType.NoOffTwE6Three

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.Open CFSG.SeitzReduction.TwistedE6Pilot

private theorem o3_etaAut_fixed_of_xiAut_fixed {f : ℕ} (hf : 1 ≤ f) {k K : Type} [Field k]
    [Field K] [Algebra k K] [CharP K 2] (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (x : ↥(graphFixedRootGroup TwistTag.E6 K σ))
    (hx : xiAut σ (apply_apply_eq hK hσ) x = x) :
    etaAut σ (apply_apply_eq hK hσ) x = x := by
  obtain ⟨-, -, -, -, -, ⟨e₂, -, -, hsec⟩⟩ :=
    even_E6_twisted_E6_second_graph_fixed_subgroup f hf k K hk hK σ hσ
  obtain ⟨htJ, hJC', η₀, hη₀, -, -, -, hfixξ, -, -, -, -⟩ := hsec
  obtain ⟨-, ⟨⟨η', hη', -, -, hfixJ, -⟩, -, -⟩⟩ :=
    even_E6_twisted_E6_canonical_graph_fixed_subgroup f hf k K hk hK σ hσ
  have hη₀e : η₀ = etaAut σ (apply_apply_eq hK hσ) :=
    MulEquiv.ext fun g => Subtype.ext (by rw [hη₀, coe_etaAut])
  have hη'e : η' = etaAut σ (apply_apply_eq hK hσ) :=
    MulEquiv.ext fun g => Subtype.ext (by rw [hη', coe_etaAut])
  have hξe : MulAut.conj (⟨_, hJC' htJ⟩ : ↥(graphFixedRootGroup TwistTag.E6 K σ)) * η₀ =
      xiAut σ (apply_apply_eq hK hσ) := by
    rw [hη₀e]
    rfl
  have hxfix : (MulAut.conj (⟨_, hJC' htJ⟩ : ↥(graphFixedRootGroup TwistTag.E6 K σ)) *
      η₀) x = x := by
    rw [hξe]
    exact hx
  have hxJ : (x : ModGL TwistTag.E6.tag K) ∈
      (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (algebraMap k K)) :=
    ((hfixξ x).1 hxfix).1
  have hfix' : η' x = x := (hfixJ x).2 hxJ
  rwa [hη'e] at hfix'

private theorem o3_exists_conj_of_commute {H : Type*} [Group H]
    (hinj : Function.Injective (MulAut.conj : H →* MulAut H))
    {X : Subgroup (MulAut H)} {φ : MulAut H}
    (hXI : X ≤ (MulAut.conj : H →* MulAut H).range) (hXel : IsElemAbelian 3 X)
    {t' : MulAut H}
    (ht' : ∀ y ∈ X, t' * (MulAut.conj φ) y = (MulAut.conj φ) y * t') :
    ∃ Xh : Subgroup H,
      X.map (MulAut.conj φ).toMonoidHom = Xh.map (MulAut.conj : H →* MulAut H) ∧
      IsElemAbelian 3 Xh ∧ Nat.card Xh = Nat.card X ∧ (∀ x ∈ Xh, t' x = x) := by
  set X' : Subgroup (MulAut H) := X.map (MulAut.conj φ).toMonoidHom with hX'def
  set Xh : Subgroup H := X'.comap (MulAut.conj : H →* MulAut H) with hXhdef
  have hX'I : X' ≤ (MulAut.conj : H →* MulAut H).range := by
    intro y hy
    rw [hX'def] at hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨c, hc⟩ := hXI hx
    exact ⟨φ c, by rw [← hc]; exact (mulAut_mul_conj_mul_inv φ c).symm⟩
  have hmap : Xh.map (MulAut.conj : H →* MulAut H) = X' :=
    Subgroup.map_comap_eq_self hX'I
  have hfirst : X.map (MulAut.conj φ).toMonoidHom = Xh.map (MulAut.conj : H →* MulAut H) := by
    rw [← hX'def, hmap]
  have hcard : Nat.card Xh = Nat.card X := by
    calc Nat.card Xh = Nat.card (Xh.map (MulAut.conj : H →* MulAut H)) :=
          (Subgroup.card_map_of_injective hinj).symm
      _ = Nat.card X' := by rw [hmap]
      _ = Nat.card X := by
          rw [hX'def]
          exact Subgroup.card_map_of_injective (MulAut.conj φ).injective
  have hel : IsElemAbelian 3 Xh := by
    rw [hXhdef, hX'def]
    exact (hXel.map (MulAut.conj φ).toMonoidHom).comap hinj
  have hfix : ∀ x ∈ Xh, t' x = x := by
    intro x hx
    have hxX' : (MulAut.conj : H →* MulAut H) x ∈ X' := by
      rw [hXhdef] at hx
      exact Subgroup.mem_comap.1 hx
    rw [hX'def] at hxX'
    obtain ⟨y, hyX, hy⟩ := Subgroup.mem_map.1 hxX'
    have hcomm : t' * MulAut.conj x = MulAut.conj x * t' := by
      rw [← hy]
      exact ht' y hyX
    have hconj : MulAut.conj (t' x) = MulAut.conj x := by
      rw [← mulAut_mul_conj_mul_inv t' x, hcomm, mul_inv_cancel_right]
    exact hinj hconj
  exact ⟨Xh, hfirst, hel, hcard, hfix⟩

theorem exists_conj_eq_map_conj_of_commute {f : ℕ} (hf : 1 ≤ f)
    {t : MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (ht2 : t ^ 2 = 1) (htI : t ∉ LayerSixE.twInndiagAut f)
    {X : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))}
    (hXel : IsElemAbelian 3 X)
    (hXI : X ≤ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f)) →* MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
        (frobQ 2 f))).range)
    (hXt : ∀ x ∈ X, t * x = x * t) :
    ∃ (φ : MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
      (Xh : Subgroup ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))),
      X.map (MulAut.conj φ).toMonoidHom = Xh.map (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6
        (GaloisField 2 (2 * f)) (frobQ 2 f)) →* MulAut ↥(graphFixedRootGroup TwistTag.E6
          (GaloisField 2 (2 * f)) (frobQ 2 f))) ∧
      IsElemAbelian 3 Xh ∧ Nat.card Xh = Nat.card X ∧
      ∀ x ∈ Xh, diagramMap TwistTag.E6 (GaloisField 2 (2 * f)) *
        (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) *
          (diagramMap TwistTag.E6 (GaloisField 2 (2 * f)))⁻¹ = x := by
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hσ : ∀ c, frobQ 2 f c = c ^ 2 ^ f := fun c => frobQ_apply 2 f c
  have htI' : t ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f)) →* MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
        (frobQ 2 f))).range := by
    intro h
    exact htI (by rw [LayerSixE.twInndiagAut]; exact Subgroup.mem_sup_left h)
  have hex : ∃ φ : MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
        (frobQ 2 f)),
      φ * t * φ⁻¹ = etaAut (frobQ 2 f) (apply_apply_eq hK hσ) ∨
        φ * t * φ⁻¹ = xiAut (frobQ 2 f) (apply_apply_eq hK hσ) := by
    rcases (conj_etaAut_or_xiAut_of_outer hf hK (frobQ 2 f) hσ).1 t ht2 htI' with
      ⟨φ, hφ⟩ | ⟨φ, hφ⟩
    · exact ⟨φ, Or.inl hφ⟩
    · exact ⟨φ, Or.inr hφ⟩
  obtain ⟨φ, hφ⟩ := hex
  set t' : MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) :=
    φ * t * φ⁻¹ with ht'def
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f)) = ⊥ :=
    center_graphFixedRootGroup_eq_bot (Finite.surjective_of_injective (frobQ 2 f).injective)
  have hinj : Function.Injective (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6
      (GaloisField 2 (2 * f)) (frobQ 2 f)) →* MulAut ↥(graphFixedRootGroup TwistTag.E6
        (GaloisField 2 (2 * f)) (frobQ 2 f))) :=
    mulAut_conj_injective_of_center_eq_bot hZ
  have ht' : ∀ y ∈ X, t' * (MulAut.conj φ) y = (MulAut.conj φ) y * t' := by
    intro y hy
    rw [ht'def]
    change (φ * t * φ⁻¹) * (φ * y * φ⁻¹) = (φ * y * φ⁻¹) * (φ * t * φ⁻¹)
    calc (φ * t * φ⁻¹) * (φ * y * φ⁻¹) = φ * (t * y) * φ⁻¹ := by group
      _ = φ * (y * t) * φ⁻¹ := by rw [hXt y hy]
      _ = (φ * y * φ⁻¹) * (φ * t * φ⁻¹) := by group
  obtain ⟨Xh, hfirst, hel, hcard, hfixeq⟩ := o3_exists_conj_of_commute hinj hXI hXel ht'
  refine ⟨φ, Xh, hfirst, hel, hcard, ?_⟩
  intro x hx
  have hfix := hfixeq x hx
  have hgoal : etaAut (frobQ 2 f) (apply_apply_eq hK hσ) x = x := by
    rcases hφ with hφ | hφ
    · rwa [hφ] at hfix
    · rw [hφ] at hfix
      let k := GaloisField 2 f
      have hk : Nat.card k = 2 ^ f := by
        dsimp [k]
        rw [GaloisField.card 2 f (by omega)]
      obtain ⟨ι⟩ := CFSG.LieType.Chevalley.E6GraphFullCoset.nonempty_ringHom_of_card hf hk hK
      letI : Algebra k (GaloisField 2 (2 * f)) := ι.toAlgebra
      exact o3_etaAut_fixed_of_xiAut_fixed hf hk hK (frobQ 2 f) hσ x hfix
  rw [← coe_etaAut (frobQ 2 f) (apply_apply_eq hK hσ) x, hgoal]

end CFSG.StandardType.NoOffTwE6Three
