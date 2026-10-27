module

public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
import CFSG.HardMathSupport.Timmesfeld.Coordinator.ElemAbelianComplement
import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeTorus
import CFSG.LocalAnalysis.StandardType.GGTableBTypeACover
import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
import CFSG.LocalAnalysis.StandardType.Marking

public section

namespace CFSG.StandardType.SCFourCover

open Matrix CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Lift

variable {K : Type} [Field K]

private theorem slScalar_eq_one_of_pow_two_pow [CharP K 2] {d k : ℕ}
    {g : SpecialLinearGroup (Fin d) K} (hg : g ∈ scalars d K) (hgk : g ^ 2 ^ k = 1) : g = 1 := by
  obtain ⟨c, -, hc⟩ := mem_scalars.mp hg
  ext i j
  have hpow := Matrix.SpecialLinearGroup.coe_pow g (2 ^ k)
  rw [hgk, Matrix.SpecialLinearGroup.coe_one, hc, scalar_apply, diagonal_pow] at hpow
  have h4 := congrArg (fun M : Matrix (Fin d) (Fin d) K => M i i) hpow
  simp only [one_apply_eq, diagonal_apply_eq, Pi.pow_apply] at h4
  have hc1 : (c : K) = 1 := iterateFrobenius_inj (R := K) (p := 2) (n := k) (by
    rw [iterateFrobenius_def, iterateFrobenius_def, ← h4, one_pow])
  rw [hc, hc1, map_one]
  rfl

private theorem slScalar_eq_one_of_pow_three [Finite K] (h3 : ¬ 3 ∣ Nat.card K - 1) {d : ℕ}
    {g : SpecialLinearGroup (Fin d) K} (hg : g ∈ scalars d K) (hg3 : g ^ 3 = 1) : g = 1 := by
  obtain ⟨c, -, hc⟩ := mem_scalars.mp hg
  ext i j
  have hpow := Matrix.SpecialLinearGroup.coe_pow g 3
  rw [hg3, Matrix.SpecialLinearGroup.coe_one, hc, scalar_apply, diagonal_pow] at hpow
  have h4 := congrArg (fun M : Matrix (Fin d) (Fin d) K => M i i) hpow
  simp only [one_apply_eq, diagonal_apply_eq, Pi.pow_apply] at h4
  have hc3 : c ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, ← h4, Units.val_one])
  have hcop : Nat.Coprime 3 (Nat.card Kˣ) := by
    rw [Nat.card_units]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have ho : orderOf c = 1 := by
    have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hc3) (orderOf_dvd_natCard c)
    rw [Nat.Coprime.gcd_eq_one hcop] at h
    exact Nat.dvd_one.mp h
  rw [hc, orderOf_eq_one_iff.mp ho, Units.val_one, map_one]
  rfl

private theorem ggTorusLift_of_normalizes_scalarFree [CharP K 2] {d p r : ℕ}
    (hsec : TypeA.SLHasSections d K) {E₀ U₀ : Subgroup (SpecialLinearGroup (Fin d) K)}
    (hE₀ : IsElemAbelian p E₀) (hcard : Nat.card E₀ = p ^ r)
    (hscal : ∀ g ∈ E₀, g ∈ scalars d K → g = 1) (hU₀ : U₀ ≠ ⊥) (hU₂ : IsPGroup 2 U₀)
    (hN : E₀ ≤ Subgroup.normalizer (U₀ : Set (SpecialLinearGroup (Fin d) K))) :
    GGTorusLift p r (projectiveSL d K) := by
  intro L' _ _ ψ hψ hker hperf
  obtain ⟨φ, -, hφ⟩ := TypeA.exists_sl_cover hsec ψ hψ hker hperf
  have hkerφ : ∀ g, φ g = 1 → g ∈ scalars d K := fun g hg =>
    proj_eq_one_iff.mp (by rw [← hφ, hg, map_one])
  have hinjE : ∀ g ∈ E₀, ∀ h ∈ E₀, φ g = φ h → g = h := by
    intro g hg h hh hgh
    have h1 : φ (g⁻¹ * h) = 1 := by rw [map_mul, map_inv, hgh, inv_mul_cancel]
    exact inv_mul_eq_one.mp (hscal _ (E₀.mul_mem (E₀.inv_mem hg) hh) (hkerφ _ h1))
  refine ⟨U₀.map φ, E₀.map φ, ?_, hU₂.map φ,
    (Subgroup.map_mono hN).trans (Subgroup.le_normalizer_map φ), TableB.isElemAbelian_map hE₀ φ,
    ?_, ?_⟩
  · obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU₀
    obtain ⟨k, hk⟩ := hU₂ u
    intro hbot
    have hφu : φ u ∈ U₀.map φ := Subgroup.mem_map_of_mem φ u.2
    rw [hbot, Subgroup.mem_bot] at hφu
    refine hu1 (Subtype.ext (slScalar_eq_one_of_pow_two_pow (k := k) (hkerφ _ hφu) ?_))
    rw [← Subgroup.coe_pow, hk, Subgroup.coe_one]
  · rw [← hcard]
    symm
    refine Nat.card_congr (Equiv.ofBijective (fun g : E₀ => (⟨φ g, g, g.2, rfl⟩ : E₀.map φ))
      ⟨fun g h hgh => Subtype.ext (hinjE g g.2 h h.2 (congrArg Subtype.val hgh)), ?_⟩)
    rintro ⟨_, g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩
  · rw [eq_bot_iff]
    rintro x ⟨⟨g, hg, rfl⟩, hx⟩
    have h1 : proj d K g = 1 := by rw [← hφ]; exact hx
    rw [hscal g hg (proj_eq_one_iff.mp h1), map_one]
    exact Subgroup.one_mem _

private theorem ggTorusLift_three_five_typeAPlus [Finite K] [CharP K 2] {d : ℕ} (hd : 10 ≤ d)
    (h3 : ¬ 3 ∣ Nat.card K - 1) : GGTorusLift 3 5 (projectiveSL d K) := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 2 := ⟨d - 2, by omega⟩
  obtain ⟨T, hT, hTcard, hTE⟩ := TwoThree.exists_torus_commSub (K := K) m
  obtain ⟨E₀, hE₀T, hE₀, hE₀card, -⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.exists_elemAbelian_le_inf_eq_bot Nat.prime_three
      hT (bot_le : (⊥ : Subgroup (SpecialLinearGroup (Fin (m + 2)) K)) ≤ T) 5 (by
        rw [Subgroup.card_bot, mul_one, hTcard]
        exact Nat.pow_le_pow_right (by norm_num) (by omega))
  exact ggTorusLift_of_normalizes_scalarFree (TypeA.slHasSections_of_five_le (by omega)) hE₀
    hE₀card (fun g hg hgs => slScalar_eq_one_of_pow_three h3 hgs (hE₀.2 g hg))
    (TwoThree.unipSub_ne_bot (by omega)) (TwoThree.isPGroup_unipSub _)
    ((hE₀T.trans hTE).trans (TwoThree.commSub_le_normalizer_unipSub _))

end Lift

theorem largeEvenLabelAll_torusLift_typeAPlus_threeFive {lab : LargeEvenLabel}
    (htag : lab.tag = .A) (h3 : 3 ∣ 2 ^ lab.n + 1) (h10 : 10 ≤ lab.rank + 1) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 5 R := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag h3 h10 ⊢
  subst htag
  intro Q hQ
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := CFSG.StandardType.charP_two_of_card hK
  have h3K : ¬ 3 ∣ Nat.card K - 1 := by
    rw [hK]
    omega
  exact ⟨K, inferInstance, inferInstance, hK, hQ',
    TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv (l + 1) K)
      (ggTorusLift_three_five_typeAPlus h10 h3K)⟩

end CFSG.StandardType.SCFourCover

end
