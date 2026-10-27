module

public import CFSG.LieType.BorelTits.Families
import CFSG.LieType.BorelTits.OrthogonalSingular
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4L2FixFree.Complement
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4L2FixFree.Chi
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4L2FixFree.Tau

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4FF

open CFSG.LieType.BorelTits

private def planeChain_F09 {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (W : Submodule K V) (v : V) : ℕ → Submodule K V :=
  fun k => if k = 0 then ⊥ else if k = 1 then Submodule.span K ({v} : Set V) else W

private lemma planeChain_F09_zero {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (W : Submodule K V) (v : V) : planeChain_F09 W v 0 = ⊥ := by
  unfold planeChain_F09
  rw [if_pos rfl]

private lemma planeChain_F09_one {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (W : Submodule K V) (v : V) : planeChain_F09 W v 1 = Submodule.span K ({v} : Set V) := by
  unfold planeChain_F09
  rw [if_neg (by omega), if_pos rfl]

private lemma planeChain_F09_two {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (W : Submodule K V) (v : V) : planeChain_F09 W v 2 = W := by
  unfold planeChain_F09
  rw [if_neg (by omega), if_neg (by omega)]

private lemma planeChain_F09_add_two {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (W : Submodule K V) (v : V) (k : ℕ) : planeChain_F09 W v (k + 2) = W := by
  unfold planeChain_F09
  rw [if_neg (by omega), if_neg (by omega)]

theorem isPGroup_two_of_plane_flag {K V H : Type} [Field K] [CharP K 2] [AddCommGroup V]
    [Module K V] [Group H] (Φ : QuadForm K V) (ρ : H →* Module.End K V)
    (hρ : Function.Injective ρ) (hQ : ∀ h x, Φ.Q (ρ h x) = Φ.Q x) {W : Submodule K V} {v : V}
    (R : Subgroup H) (hRv : ∀ g ∈ R, ρ g v = v) (hRW : ∀ g ∈ R, ∀ w ∈ W, ρ g w ∈ W)
    (hRW' : ∀ g ∈ R, ∀ w ∈ W, ρ g w - w ∈ Submodule.span K {v})
    (hRP : ∀ g ∈ R, ∀ x ∈ Φ.polar.perp W, ρ g x - x ∈ W) : IsPGroup 2 ↥R := by
  let X : ℕ → Submodule K V := planeChain_F09 W v
  have hX0 : X 0 = ⊥ := planeChain_F09_zero W v
  have hX1 : X 1 = Submodule.span K ({v} : Set V) := planeChain_F09_one W v
  have hX2 : X 2 = W := planeChain_F09_two W v
  have hiso : IsIsometric Φ.polar ρ := Φ.isIsometric_of_Q hQ
  have hG : ∀ g ∈ R, ∀ k, ∀ x ∈ X k, ρ g x ∈ X k := by
    intro g hg k x hx
    rcases k with _ | _ | k
    · rw [hX0, Submodule.mem_bot] at hx
      rw [hx, map_zero]
      exact Submodule.zero_mem _
    · rw [hX1, Submodule.mem_span_singleton] at hx
      obtain ⟨c, rfl⟩ := hx
      rw [map_smul, hRv g hg]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton v))
    · have hXk : X (k + 2) = W := planeChain_F09_add_two W v k
      rw [hXk] at hx ⊢
      exact hRW g hg x hx
  have hstab : R ≤ flagStab ρ (isoCompletion Φ.polar X 2) :=
    le_flagStab_isoCompletion ρ hiso 2 hG
  have htriv : ∀ k < 2, ∀ g ∈ R, ∀ x ∈ X (k + 1), ρ g x - x ∈ X k := by
    intro k hk g hg x hx
    interval_cases k
    · have hx1 : x ∈ X 1 := hx
      rw [hX1, Submodule.mem_span_singleton] at hx1
      obtain ⟨c, rfl⟩ := hx1
      rw [hX0, Submodule.mem_bot, map_smul, hRv g hg, sub_self]
    · have hx2 : x ∈ X 2 := hx
      rw [hX2] at hx2
      rw [hX1]
      exact hRW' g hg x hx2
  have hmid : ∀ g ∈ R, ∀ x ∈ Φ.polar.perp (X 2), ρ g x - x ∈ X 2 := by
    intro g hg x hx
    rw [hX2] at hx ⊢
    exact hRP g hg x hx
  have hker : R ≤ flagKernel ρ (isoCompletion Φ.polar X 2) :=
    le_flagKernel_isoCompletion ρ hiso hX0 hstab htriv hmid
  have hp : IsPGroup 2 ↥(flagKernel ρ (isoCompletion Φ.polar X 2)) :=
    isPGroup_flagKernel (F := isoCompletion Φ.polar X 2) ρ 2 hρ
      (isoCompletion_zero hX0 2) (isoCompletion_top hX0 2)
  exact hp.to_le hker

theorem isSolvable_of_fix_line_in_plane {K V H : Type} [Field K] [CharP K 2] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Group H] [Finite H] (Φ : QuadForm K V)
    (ρ : H →* Module.End K V) (hρ : Function.Injective ρ) (hQ : ∀ h x, Φ.Q (ρ h x) = Φ.Q x)
    (hV : Module.finrank K V = 6) {W : Submodule K V} (hWs : Φ.IsTotallySingular W)
    (hW2 : Module.finrank K ↥W = 2) {v : V} (hvW : v ∈ W) (hv0 : v ≠ 0) (J : Subgroup H)
    (hJv : ∀ g ∈ J, ρ g v = v) (hJW : ∀ g ∈ J, ∀ w ∈ W, ρ g w ∈ W) : Group.IsSolvable ↥J := by
  obtain ⟨A, hd, hs⟩ := exists_complement_in_perp Φ hWs
  obtain ⟨q, hq, hqp⟩ := exists_quadraticForm_restrict Φ A
  have hA2 : Module.finrank K ↥A = 2 := by
    have h := finrank_complement_in_perp Φ hd hs
    omega
  have hnd : (QuadraticMap.polarBilin q).Nondegenerate :=
    nondegenerate_polarBilin_complement Φ hd hs q hqp
  have hsolvO : Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup q) :=
    isSolvable_orthogonalGroup_of_finrank_eq_two q hnd hA2
  obtain ⟨χ, hχ⟩ := exists_chi ρ hW2 hvW hv0 J hJv hJW
  obtain ⟨τ, hτ⟩ := exists_tau Φ ρ hQ hWs hd hs q hq J hJW
  let φ : ↥J →* Kˣ × ↥(TauCeti.QuadraticMap.orthogonalGroup q) := χ.prod τ
  let R : Subgroup ↥J := φ.ker
  have hR2 : IsPGroup 2 ↥R := by
    refine isPGroup_two_of_plane_flag (W := W) (v := v) Φ (ρ.comp J.subtype)
      (hρ.comp J.subtype_injective) (fun g x => hQ ↑g x) R ?_ ?_ ?_ ?_
    · intro g hg
      exact hJv ↑g g.2
    · intro g hg w hw
      exact hJW ↑g g.2 w hw
    · intro g hg w hw
      have hchi : χ g = 1 := by
        have := congrArg Prod.fst (MonoidHom.mem_ker.mp hg)
        simpa [φ, MonoidHom.prod_apply] using this
      exact sub_mem_span_of_chi_eq_one ρ hχ hchi w hw
    · intro g hg x hx
      have htau : τ g = 1 := by
        have := congrArg Prod.snd (MonoidHom.mem_ker.mp hg)
        simpa [φ, MonoidHom.prod_apply] using this
      exact sub_mem_of_tau_eq_one Φ ρ hs hJW hτ htau x hx
  haveI : Group.IsSolvable ↥R := by
    haveI : Group.IsNilpotent ↥R := hR2.isNilpotent
    infer_instance
  haveI : Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup q) := hsolvO
  exact Group.isSolvable_of_ker_le_range R.subtype φ (by rw [Subgroup.range_subtype])

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4FF
