module

public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofSignal
public import CFSG.RankThree.PartTwo.Sec14.Item143StepsProofPGL
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofFix
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofTrans
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofInv
import CFSG.RankThree.PartTwo.Sec12.KS128NotHJPGL
import CFSG.RankThree.PartTwo.Sec13.Item13K410
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec14.Proof142Res

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec13 (Sec13Data exists_mul_pow_of_mem_sup pow_three_mem_of_mem_sup
  mul_mem_of_mem_centMod exists_irreducible_structure card_zpowers_sup_zpowers_eq_nine
  sup_zpowers_eq_of_card)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix (ProjGenLinGroup GeneralLinearGroup)
open scoped Matrix

variable {G : Type} [Group G] [Finite G]

theorem not_mem_statedScalars_of_irreducible {K : Type} [Field K] {w : GL (Fin 3) K}
    (hirr : ∀ W : Submodule K (Fin 3 → K),
      (∀ v ∈ W, (w : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) :
    w ∉ StatedScalars (Fin 3) K := by
  rintro ⟨c, rfl⟩
  refine not_irreducible_of_diag (x := GeneralLinearGroup.scalar (Fin 3) c)
    (z := GeneralLinearGroup.scalar (Fin 3) c⁻¹) (g := 1) ⟨c⁻¹, rfl⟩ (d := fun _ => 1) ?_ hirr
  rw [← map_mul, mul_inv_cancel, map_one, inv_one, one_mul, mul_one, Units.val_one,
    Matrix.diagonal_one]

theorem inducesTypeOn_mul_of_eq_one {L : Subgroup G} {x c' : G} {k : ℕ}
    (hx : InducesTypeOn L x k) (hc'N : c' ∈ Subgroup.normalizer (L : Set G))
    (hc' : thetaQuotMulAut L (L.normalizerMonoidHom ⟨c', hc'N⟩) = 1) :
    InducesTypeOn L (x * c') k := by
  obtain ⟨hxN, π, p, f, K, _, hK, hq, e, y, hyH, hyk, hact⟩ := hx
  refine ⟨Subgroup.mul_mem _ hxN hc'N, π, p, f, K, inferInstance, hK, hq, e, y, hyH, hyk,
    fun z => ?_⟩
  have h1 : (⟨x * c', Subgroup.mul_mem _ hxN hc'N⟩ : Subgroup.normalizer (L : Set G)) =
      ⟨x, hxN⟩ * ⟨c', hc'N⟩ := rfl
  rw [h1, map_mul, map_mul, hc', mul_one]
  exact hact z

theorem type1_of_commute_mod_type3 {K : Type} [Field K] {π : Bool} {p f : ℕ}
    (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {y s : GL (Fin 3) K}
    (hy3 : Type123 π (p ^ f) K y 3) (hs : s ∈ slPi π 3 (p ^ f) K)
    (hsZ : s ∉ StatedScalars (Fin 3) K) (hs3 : s ^ 3 ∈ StatedScalars (Fin 3) K)
    (hysZ : y * s * y⁻¹ * s⁻¹ ∈ StatedScalars (Fin 3) K) : Type123 π (p ^ f) K s 1 := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have h3 := hK.three_ne_zero hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hsH : s ∈ glPi π 3 (p ^ f) K := slPi_le_glPi hπ hs
  have hsdet : (s : Matrix (Fin 3) (Fin 3) K).det = 1 := ((mem_slPi_iff hπ).mp hs).2
  obtain ⟨lam, hlam⟩ := hysZ
  have hys : y * s * y⁻¹ = GeneralLinearGroup.scalar (Fin 3) lam * s := by
    rw [hlam]
    group
  have hlam1 : lam ≠ 1 := by
    intro hlam1
    refine Sec12.KS128NotHJTC.false_of_commute_irreducible hτ hτ1 h3 hsdet hs3 hsZ ?_ hy3.2.2
    rw [hlam1, map_one, one_mul] at hys
    calc y * s = y * s * y⁻¹ * y := by group
      _ = s * y := by rw [hys]
  have htr := trace_eq_zero_of_conj_eq_scalar_mul hlam1 hys
  have hsZ' : s ∉ zPi π 3 (p ^ f) K := fun hz =>
    hsZ (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz)
  have hs3' : s ^ 3 ∈ zPi π 3 (p ^ f) K := by
    rw [zPi_eq hπ hq' hτ hτ1]
    exact ⟨pow_mem hsH 3, hs3⟩
  rcases type123_exhaust hK hq hsH hsZ' hs3' with h1 | h2 | h3'
  · exact h1
  · exact absurd htr (trace_ne_zero_of_type2 hK hq h2)
  · exact absurd ⟨s, hs, fun m _ => rfl⟩ (not_inner_of_type3 hK hq hsH h3')

theorem inducesTypeOn_three_mul_zpow {L : Subgroup G} {d x : G} (hdL : d ∈ L) (hd3 : d ^ 3 = 1)
    (hd1 : d ≠ 1) (hxd : x * d = d * x) (hx : InducesTypeOn L x 3) (j : ℤ) :
    InducesTypeOn L (x * d ^ j) 3 := by
  obtain ⟨hxN, π, p, f, K, _, hK, hq, e, y, hyH, hy3, hact⟩ := hx
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have h3 := hK.three_ne_zero hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hdN : d ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hdL
  have hzN : x * d ^ j ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ hxN (Subgroup.zpow_mem _ hdN j)
  set σx := thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hxN⟩) with hσx
  have hact' : ∀ z : L ⧸ aschbacherSolvableCore 3 L,
      ((e (σx z) : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk y * (e z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹ :=
    hact
  set d' : ↥L := ⟨d, hdL⟩ with hd'
  have hd'3 : d' ^ 3 = 1 := Subtype.ext (by simpa using hd3)
  set db : ↥L ⧸ aschbacherSolvableCore 3 ↥L := QuotientGroup.mk' _ d' with hdb
  have hdb3 : db ^ 3 = 1 := by rw [hdb, ← map_pow, hd'3, map_one]
  have hdb1 : db ≠ 1 := by
    intro h1
    have h2 := CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three
      (Sec16.Proof1613Inv.isPGroup_zpowers_three hd'3) (Subgroup.mem_zpowers _)
      (Subgroup.one_mem _) (by rw [map_one]; exact h1)
    exact hd1 (congrArg Subtype.val h2)
  obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp (e db).2
  have hsH : s ∈ glPi π 3 (p ^ f) K := slPi_le_glPi hπ hs
  have hsZ : s ∉ StatedScalars (Fin 3) K := by
    intro hsZ
    apply hdb1
    apply e.injective
    apply Subtype.ext
    rw [← hse, map_one, Subgroup.coe_one, mk_eq_one_iff_mem_statedScalars]
    exact hsZ
  have hs3 : s ^ 3 ∈ StatedScalars (Fin 3) K := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_pow, hse, ← Subgroup.coe_pow, ← map_pow, hdb3,
      map_one, Subgroup.coe_one]
  have hsdet : (s : Matrix (Fin 3) (Fin 3) K).det = 1 := ((mem_slPi_iff hπ).mp hs).2
  have hfix : σx db = db := by
    rw [hσx, hdb, QuotientGroup.mk'_apply, thetaQuotMulAut_mk]
    congr 1
    apply Subtype.ext
    rw [normalizerMonoidHom_apply_coe, hxd, mul_inv_cancel_right]
  have h1 := hact' db
  rw [hfix, ← hse] at h1
  have hysZ : y * s * y⁻¹ * s⁻¹ ∈ StatedScalars (Fin 3) K := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_mul, map_mul, map_mul, map_inv, map_inv, ← h1,
      mul_inv_cancel]
  obtain ⟨lam, hlam⟩ := hysZ
  have hys : y * s * y⁻¹ = GeneralLinearGroup.scalar (Fin 3) lam * s := by
    rw [hlam]
    group
  have hlam3 : lam ^ 3 = 1 := pow_three_eq_one_of_conj_eq_scalar_mul hys
  have hlam1 : lam ≠ 1 := by
    intro hlam1
    refine Sec12.KS128NotHJTC.false_of_commute_irreducible hτ hτ1 h3 hsdet hs3 hsZ ?_ hy3.2.2
    rw [hlam1, map_one, one_mul] at hys
    calc y * s = y * s * y⁻¹ * y := by group
      _ = s * y := by rw [hys]
  have htr := trace_eq_zero_of_conj_eq_scalar_mul hlam1 hys
  have hsZ' : s ∉ zPi π 3 (p ^ f) K := fun hz =>
    hsZ (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz)
  have hs3' : s ^ 3 ∈ zPi π 3 (p ^ f) K := by
    rw [zPi_eq hπ hq' hτ hτ1]
    exact ⟨pow_mem hsH 3, hs3⟩
  have htype : Type123 π (p ^ f) K s 1 := type1_of_commute_mod_type3 hK hq hy3 hs hsZ hs3
    ⟨lam, hlam⟩
  obtain ⟨τ', hτ', hτ'1, z₀, hz₀, g, -, hD⟩ := htype
  obtain ⟨ζ, -, hζ⟩ := exists_scalar_of_mem_zPi hK hq hτ' hτ'1 hz₀
  have hsz : s * z₀ = g * diagTau hτ' * g⁻¹ := by
    rw [← hD]
    group
  have hs3c : s ^ 3 = GeneralLinearGroup.scalar (Fin 3) (ζ⁻¹ ^ 3) := by
    have e1 : (s * z₀) ^ 3 = 1 := by
      rw [hsz, conj_pow, diagTau_pow_three hτ', mul_one, mul_inv_cancel]
    have e2 : (s * z₀) ^ 3 = s ^ 3 * z₀ ^ 3 := by
      rw [← hζ]
      exact (Commute.mul_pow (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ s) 3)
    rw [e2, ← hζ, ← map_pow] at e1
    rw [map_pow, map_inv, inv_pow]
    calc s ^ 3 = s ^ 3 * GeneralLinearGroup.scalar (Fin 3) (ζ ^ 3) *
          (GeneralLinearGroup.scalar (Fin 3) (ζ ^ 3))⁻¹ := by group
      _ = (GeneralLinearGroup.scalar (Fin 3) ζ ^ 3)⁻¹ := by rw [e1, map_pow]; group
  obtain ⟨ℓ, hℓ⟩ := mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hy3.2.1
  have hy3m : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = (ℓ : K) • 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hℓ, coe_scalar_eq_smul]
  have hℓnc : ∀ μ : K, μ ^ 3 ≠ ℓ :=
    Sec12.KS128NotHJTC.not_cube_of_irreducible hτ hτ1 h3 hy3m hy3.2.2
  set w := y * s ^ j with hw
  have hysj : y * s ^ j * y⁻¹ = GeneralLinearGroup.scalar (Fin 3) (lam ^ j) * s ^ j := by
    have e1 : y * s ^ j * y⁻¹ = (y * s * y⁻¹) ^ j := by
      rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
    rw [e1, hys, (Commute.mul_zpow (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar lam s).symm
      j), map_zpow]
  have hlamj3 : (lam ^ j) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hlam3, one_zpow]
  have hw3 : w ^ 3 = GeneralLinearGroup.scalar (Fin 3) ((ζ⁻¹ ^ 3) ^ j * ℓ) := by
    have e3 : (s ^ j) ^ 3 = (s ^ 3) ^ j := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    rw [hw, Sec16.Proof1613Fix.pow_three_mul_of_conj hlamj3 hysj, e3, hs3c, ← map_zpow, ← hℓ,
      ← map_mul]
  have hw3m : (w : Matrix (Fin 3) (Fin 3) K) ^ 3 = (((ζ⁻¹ ^ 3) ^ j * ℓ : Kˣ) : K) • 1 := by
    rw [← Units.val_pow_eq_pow_val, hw3, coe_scalar_eq_smul]
  have hwnc : ∀ μ : K, μ ^ 3 ≠ (((ζ⁻¹ ^ 3) ^ j * ℓ : Kˣ) : K) := by
    intro μ hμ
    apply hℓnc (μ * ((ζ ^ j : Kˣ) : K))
    have hone : (ζ⁻¹ ^ 3) ^ j * (ζ ^ j) ^ 3 = 1 := by group
    have key : (((ζ⁻¹ ^ 3) ^ j * ℓ : Kˣ) : K) * ((ζ ^ j : Kˣ) : K) ^ 3 = (ℓ : K) := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_mul]
      congr 1
      rw [mul_comm _ ℓ, mul_assoc, hone, mul_one]
    rw [mul_pow, hμ, key]
  have hirr : ∀ W : Submodule K (Fin 3 → K),
      (∀ v ∈ W, (w : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤ := fun W hW =>
    eq_bot_or_eq_top_of_invariant hwnc hw3m hW
  have hwH : w ∈ glPi π 3 (p ^ f) K := Subgroup.mul_mem _ hyH (Subgroup.zpow_mem _ hsH j)
  have hwZ : w ∉ zPi π 3 (p ^ f) K := fun hz =>
    not_mem_statedScalars_of_irreducible hirr (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz)
  have hw3Z : w ^ 3 ∈ zPi π 3 (p ^ f) K := by
    rw [zPi_eq hπ hq' hτ hτ1]
    exact ⟨pow_mem hwH 3, ⟨_, hw3.symm⟩⟩
  have hσd : thetaQuotMulAut L (L.normalizerMonoidHom ⟨d, hdN⟩) = MulAut.conj db := by
    ext v
    induction v using QuotientGroup.induction_on with
    | H l =>
      rw [thetaQuotMulAut_mk, MulAut.conj_apply, hdb, QuotientGroup.mk'_apply,
        ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      congr 1
  have hσz : thetaQuotMulAut L (L.normalizerMonoidHom ⟨x * d ^ j, hzN⟩) =
      σx * MulAut.conj (db ^ j) := by
    have e1 : (⟨x * d ^ j, hzN⟩ : Subgroup.normalizer (L : Set G)) =
        ⟨x, hxN⟩ * ⟨d, hdN⟩ ^ j := Subtype.ext (by simp)
    rw [e1, map_mul, map_mul, map_zpow, map_zpow, hσd, map_zpow]
  refine ⟨hzN, π, p, f, K, inferInstance, hK, hq, e, w, hwH, ⟨hwZ, hw3Z, hirr⟩, fun u => ?_⟩
  rw [hσz, MulAut.mul_apply, MulAut.conj_apply, hact', map_mul, map_mul, map_inv,
    Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_zpow, Subgroup.coe_zpow, ← hse,
    hw, map_mul, map_zpow]
  group

theorem thetaFix_eq_of_pow {L : Subgroup G} {e : G} (he : e ∈ Subgroup.normalizer (L : Set G))
    (he3 : e ^ 3 = 1) {m : ℕ} (hm : m = 1 ∨ m = 2)
    (hem : e ^ m ∈ Subgroup.normalizer (L : Set G)) : thetaFix L he = thetaFix L hem := by
  set σ := thetaQuotMulAut L (L.normalizerMonoidHom ⟨e, he⟩) with hσ
  have hσm : thetaQuotMulAut L (L.normalizerMonoidHom ⟨e ^ m, hem⟩) = σ ^ m := by
    have e1 : (⟨e ^ m, hem⟩ : Subgroup.normalizer (L : Set G)) = ⟨e, he⟩ ^ m :=
      Subtype.ext (by simp)
    rw [e1, map_pow, map_pow]
  have hσ3 : σ ^ 3 = 1 := by
    have e1 : (⟨e, he⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using he3)
    rw [hσ, ← map_pow, ← map_pow, e1, map_one, map_one]
  ext z
  rw [mem_thetaFix_iff, mem_thetaFix_iff, hσm]
  rcases hm with rfl | rfl
  · rw [pow_one]
  · constructor
    · intro h
      rw [sq, MulAut.mul_apply, h, h]
    · intro h
      have e1 : σ = (σ ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hσ3, one_mul, pow_one]
      have h2 : σ z = z := by rw [e1, sq, MulAut.mul_apply, h, h]
      exact h2

theorem exists_signal_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (ψ : X ≃* Y)
    {C : Subgroup X} {C' : Subgroup Y} (hCC' : ∀ u ∈ C, ψ u ∈ C')
    (h : ∃ W : Subgroup Y, ¬ 3 ∣ Nat.card W ∧ C' ≤ Subgroup.normalizer (W : Set Y) ∧
      ∀ U : Subgroup Y, U ≤ C' → ¬ 3 ∣ Nat.card U → U ≤ W) :
    ∃ W : Subgroup X, ¬ 3 ∣ Nat.card W ∧ C ≤ Subgroup.normalizer (W : Set X) ∧
      ∀ U : Subgroup X, U ≤ C → ¬ 3 ∣ Nat.card U → U ≤ W := by
  obtain ⟨W, hW3, hWN, hWle⟩ := h
  refine ⟨W.map ψ.symm.toMonoidHom, ?_, ?_, ?_⟩
  · rwa [Subgroup.card_map_of_injective ψ.symm.injective]
  · intro g hg
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact ⟨ψ g, hWN (hCC' g hg), by simp⟩
  · intro U hU hU3 u hu
    have hUC : U.map ψ.toMonoidHom ≤ C' := by
      rintro _ ⟨v, hv, rfl⟩
      exact hCC' v (hU hv)
    have hU3' : ¬ 3 ∣ Nat.card (U.map ψ.toMonoidHom) := by
      rwa [Subgroup.card_map_of_injective ψ.injective]
    exact ⟨ψ u, hWle _ hUC hU3' ⟨u, hu, rfl⟩, by simp⟩

theorem exists_signal_thetaFix_of_type3 {L : Subgroup G} {x : G}
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) (hx : InducesTypeOn L x 3) :
    ∃ W : Subgroup (L ⧸ aschbacherSolvableCore 3 L), ¬ 3 ∣ Nat.card W ∧
      thetaFix L hxN ≤ Subgroup.normalizer (W : Set (L ⧸ aschbacherSolvableCore 3 L)) ∧
      ∀ U : Subgroup (L ⧸ aschbacherSolvableCore 3 L), U ≤ thetaFix L hxN →
        ¬ 3 ∣ Nat.card U → U ≤ W := by
  obtain ⟨hxN', π, p, f, K, _, hK, hq, e, y, hyH, hy3, hact⟩ := hx
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hya : y * y * y⁻¹ * y⁻¹ ∈ StatedScalars (Fin 3) K := by
    rw [mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  obtain ⟨y', ⟨z, hz, rfl⟩, hcyc, -, w₀, -, hw₀3, hcent, -⟩ :=
    exists_irreducible_structure hK hq hyH hy3.1 hy3.2.1 (not_inner_of_type3 hK hq hyH hy3) hy3
      hya
  have hTcomm : ∀ a ∈ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer ({y * z} : Set (GL (Fin 3) K)),
      ∀ c ∈ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer ({y * z} : Set (GL (Fin 3) K)),
        a * c = c * a := by
    intro a ha c hc
    have h1 := (IsCyclic.commGroup (α := ↥(slPi π 3 (p ^ f) K ⊓
      Subgroup.centralizer ({y * z} : Set (GL (Fin 3) K))))).mul_comm ⟨a, ha⟩ ⟨c, hc⟩
    exact congrArg Subtype.val h1
  have hw₀3' : w₀ ^ 3 = 1 := by
    have := pow_orderOf_eq_one w₀
    rwa [hw₀3] at this
  have hw₀c : w₀ ∈ centMod (slPi π 3 (p ^ f) K) (y * z) :=
    hcent ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers w₀)
  have hMcube : ∀ m ∈ centMod (slPi π 3 (p ^ f) K) (y * z),
      m ^ 3 ∈ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer ({y * z} : Set (GL (Fin 3) K)) :=
    fun m hm => pow_three_mem_of_mem_sup hw₀3' (fun t ht => mul_mem_of_mem_centMod hw₀c ht)
      (hcent ▸ hm)
  have hmkz : ProjGenLinGroup.mk z = 1 :=
    mk_eq_one_iff_mem_statedScalars.mpr (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz)
  refine exists_signal_of_mulEquiv e (fun u hu => ?_) (exists_signal_centMod hK hTcomm hMcube)
  rw [mem_centP_iff, map_mul, hmkz, mul_one]
  have h1 := hact u
  rw [show thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hxN'⟩) u = u from hu] at h1
  calc (e u : ProjGenLinGroup (Fin 3) K) * ProjGenLinGroup.mk y =
      (ProjGenLinGroup.mk y * (e u : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹) *
        ProjGenLinGroup.mk y := by rw [← h1]
    _ = ProjGenLinGroup.mk y * (e u : ProjGenLinGroup (Fin 3) K) := by group

theorem exists_pow_mul_eq {A : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (h27 : Nat.card A = 27) {c d e x : G} (hcA : c ∈ A) (hdA : d ∈ A) (heA : e ∈ A)
    (h9 : Nat.card (Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup G) = 9)
    (he : e ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d) (hxA : x ∈ A) :
    ∃ (i j : ℤ) (m : ℕ), m < 3 ∧ x = c ^ i * d ^ j * e ^ m := by
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcdA : Subgroup.zpowers c ⊔ Subgroup.zpowers d ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr hcA) (Subgroup.zpowers_le.mpr hdA)
  have hAeq := sup_zpowers_eq_of_card h27 hcdA h9 heA he
  have heT : ∀ t ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d,
      e * t * e⁻¹ ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d := fun t ht => by
    rw [hcomm e heA t (hcdA ht), mul_inv_cancel_right]
    exact ht
  obtain ⟨t, ht, m, hm, rfl⟩ :=
    exists_mul_pow_of_mem_sup (hA.2 e heA) heT (hAeq.symm ▸ hxA : x ∈ _)
  obtain ⟨i, j, rfl⟩ := exists_zpow_mul_of_mem_sup (hcomm c hcA d hdA) ht
  exact ⟨i, j, m, hm, rfl⟩

end CFSG.RankThree.PartTwo.Sec14.Proof142Res

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec14.Proof142Res
open CFSG.RankThree.PartTwo.Sec13 (card_zpowers_sup_zpowers_eq_nine)

theorem ks142SignalPGL : KS142SignalPGL := by
  intro G _ _ A c L hD hPGL hx B hB hcB hAL e heB hec heN
  obtain ⟨x, hxA, hx⟩ := hx
  have hA := hD.isElemAbelian
  have h27 := hD.card_eq
  have hcA := hD.mem_A
  have hAN := hD.le_normalizer
  have hLc := hD.le_centralizer
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => hD.commute ha hb
  obtain ⟨d, hdAL, hd1, hALd⟩ := Sec5.exists_eq_zpowers_of_card_eq_prime Nat.prime_three
    (Sec16.Proof1614Trans.card_inf_eq_three_of_pgl hD hPGL)
  have hdA : d ∈ A := hdAL.1
  have hdL : d ∈ L := hdAL.2
  have hd3 : d ^ 3 = 1 := hA.2 d hdA
  have hdB : d ∉ B := fun hdB => hAL (hALd ▸ Subgroup.zpowers_le.mpr hdB)
  have hcL : c ∉ L := Sec13.not_mem_of_center_eq_bot hD
    (Sec13.facts_of_isZ3PGLThreePi hD hPGL).2.1
  have hcd : c ∉ Subgroup.zpowers d := fun h => hcL (Subgroup.zpowers_le.mpr hdL h)
  have h9 := card_zpowers_sup_zpowers_eq_nine hA h27 hcA hdA hd1 hcd
  have heA : e ∈ A := hB.1 heB
  have he1 : e ≠ 1 := fun h => hec (h ▸ Subgroup.one_mem _)
  have hce : c ∉ Subgroup.zpowers e := by
    intro hce
    apply hec
    have hle : Subgroup.zpowers c ≤ Subgroup.zpowers e := Subgroup.zpowers_le.mpr hce
    have hord : orderOf e = 3 := orderOf_eq_prime (hA.2 e heA) he1
    have heq : Subgroup.zpowers c = Subgroup.zpowers e := Subgroup.eq_of_le_of_card_ge hle (by
      rw [Nat.card_zpowers, Nat.card_zpowers, hord, hD.orderOf_eq])
    rw [heq]
    exact Subgroup.mem_zpowers e
  have h9e := card_zpowers_sup_zpowers_eq_nine hA h27 hcA heA he1 hce
  have hB9 : Nat.card B = 9 := by
    have := hB.2
    rw [h27] at this
    omega
  have hBeq : Subgroup.zpowers c ⊔ Subgroup.zpowers e = B :=
    Subgroup.eq_of_le_of_card_ge
      (sup_le (Subgroup.zpowers_le.mpr hcB) (Subgroup.zpowers_le.mpr heB)) (by rw [hB9, h9e])
  have hecd : e ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
    intro he
    apply hdB
    have hle : Subgroup.zpowers c ⊔ Subgroup.zpowers e ≤
        Subgroup.zpowers c ⊔ Subgroup.zpowers d := sup_le le_sup_left (Subgroup.zpowers_le.mpr he)
    have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [h9, h9e])
    rw [← hBeq, heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers d)
  have hcN : c ∈ Subgroup.normalizer (L : Set G) := hAN hcA
  have hσc : ∀ k : ℤ, ∀ hk : c ^ k ∈ Subgroup.normalizer (L : Set G),
      thetaQuotMulAut L (L.normalizerMonoidHom ⟨c ^ k, hk⟩) = 1 := by
    intro k hk
    ext v
    induction v using QuotientGroup.induction_on with
    | H l =>
      rw [thetaQuotMulAut_mk, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      rw [normalizerMonoidHom_apply_coe]
      have hlc : (l : G) * c ^ k = c ^ k * l :=
        (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (hLc l.2)) k)
      rw [← hlc, mul_inv_cancel_right]
  obtain ⟨i, j, m, hm3, hxeq⟩ := exists_pow_mul_eq hA h27 hcA hdA heA h9 hecd hxA
  have hcLθ := hD.mem_thetaComponentsAt
  have hxd : x * d = d * x := hcomm x hxA d hdA
  have hm : m = 1 ∨ m = 2 := by
    rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2) with h0 | h1 | h2
    · exfalso
      subst h0
      rw [pow_zero, mul_one] at hxeq
      have hx' := inducesTypeOn_mul_of_eq_one hx (Subgroup.zpow_mem _ hcN (-i))
        (hσc (-i) (Subgroup.zpow_mem _ hcN (-i)))
      apply Sec16.Proof1613Fix.not_mem_of_inducesTypeOn_three hcLθ hx'
      rw [hxeq, mul_assoc, (hcomm _ (Subgroup.zpow_mem _ hdA j) _
        (Subgroup.zpow_mem _ hcA (-i))), ← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero,
        one_mul]
      exact Subgroup.zpow_mem _ hdL j
    · exact Or.inl h1
    · exact Or.inr h2
  have hem : e ^ m = x * d ^ (-j) * c ^ (-i) := by
    rw [hxeq]
    have h1 : c ^ i * d ^ j * e ^ m * d ^ (-j) * c ^ (-i) =
        (c ^ i * c ^ (-i)) * (d ^ j * d ^ (-j)) * e ^ m := by
      have hc1 : Commute (c ^ (-i)) (e ^ m) := Commute.zpow_left
        ((Commute.pow_right (hcomm c hcA e heA) m)) (-i)
      have hc2 : Commute (d ^ (-j)) (e ^ m) := Commute.zpow_left
        ((Commute.pow_right (hcomm d hdA e heA) m)) (-j)
      have hc3 : Commute (c ^ (-i)) (d ^ j) := Commute.zpow_zpow (hcomm c hcA d hdA) (-i) j
      have hc4 : Commute (c ^ (-i)) (d ^ (-j)) := Commute.zpow_zpow (hcomm c hcA d hdA) (-i) (-j)
      calc c ^ i * d ^ j * e ^ m * d ^ (-j) * c ^ (-i) =
          c ^ i * d ^ j * (e ^ m * d ^ (-j)) * c ^ (-i) := by group
        _ = c ^ i * d ^ j * (d ^ (-j) * e ^ m) * c ^ (-i) := by rw [hc2.eq]
        _ = c ^ i * (d ^ j * d ^ (-j)) * (e ^ m * c ^ (-i)) := by group
        _ = c ^ i * (d ^ j * d ^ (-j)) * (c ^ (-i) * e ^ m) := by rw [hc1.eq]
        _ = c ^ i * ((d ^ j * d ^ (-j)) * c ^ (-i)) * e ^ m := by group
        _ = c ^ i * (c ^ (-i) * (d ^ j * d ^ (-j))) * e ^ m := by
          rw [← zpow_add, add_neg_cancel, zpow_zero, mul_one, one_mul]
        _ = (c ^ i * c ^ (-i)) * (d ^ j * d ^ (-j)) * e ^ m := by group
    rw [h1, ← zpow_add, ← zpow_add, add_neg_cancel, add_neg_cancel, zpow_zero, zpow_zero,
      one_mul, one_mul]
  have hx' := inducesTypeOn_three_mul_zpow hdL hd3 hd1 hxd hx (-j)
  have hx'' := inducesTypeOn_mul_of_eq_one hx' (Subgroup.zpow_mem _ hcN (-i))
    (hσc (-i) (Subgroup.zpow_mem _ hcN (-i)))
  rw [← hem] at hx''
  have hemN : e ^ m ∈ Subgroup.normalizer (L : Set G) := Subgroup.pow_mem _ heN m
  rw [thetaFix_eq_of_pow heN (hA.2 e heA) hm hemN]
  exact exists_signal_thetaFix_of_type3 hemN hx''

end CFSG.RankThree.PartTwo.Sec14
