module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvdCore
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeRestOuter

public section

namespace CFSG.StandardType.SmallU

open scoped commutatorElement

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.StandardType.LineU CFSG.StandardType.UnitTB CFSG.Assembly
  CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.StandardType.TableBUE

variable {K : Type} [Field K] {n d p : ℕ} {L' : Type} [Group L']
  {φ : ↥(unitarySU 2 n K d) →* L'}

theorem mem_center_of_scalar {x : ↥(unitarySU 2 n K d)} {c : K}
    (hc : ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal fun _ => c) :
    x ∈ Subgroup.center ↥(unitarySU 2 n K d) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hc]
  ext i j
  simp [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

theorem exists_pair [Finite K] [Finite L'] (hM : Model φ) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hd : 4 ≤ d) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) {R : Type} [Group R] {ψ : L' →* R}
    (hψ : Function.Surjective ψ) (hkerψ : ψ.ker ≤ Subgroup.center L')
    (hZR : Subgroup.center R = ⊥) {A : Subgroup (MulAut L')} (hAp : ∀ a ∈ A, a ^ p = 1)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t) {U : Subgroup R} (hU1 : U ≠ ⊥)
    (hU2 : IsPGroup 2 U) (hAU : ∀ a ∈ A, ∀ l : L', ψ l ∈ U → ψ (a l) ∈ U) :
    ∃ s t : Fin d, s ≠ t ∧ ∀ a ∈ A, ∀ σ : Fin d → Kˣ, ActsU φ a σ → σ s = σ t := by
  classical
  set φG : ↥(unitarySU 2 n K d) →* MulAut L' := (MulAut.conj : L' →* MulAut L').comp φ with hφG
  have hkerG : φG.ker ≤ Subgroup.center ↥(unitarySU 2 n K d) := by
    intro x hx
    have h1 : MulAut.conj (φ x) = 1 := hx
    have h : ∀ y : ↥(unitarySU 2 n K d), φ (x * y * x⁻¹) = φ y := by
      intro y
      have := congrArg (fun f : MulAut L' => f (φ y)) h1
      simpa [MulAut.conj_apply, map_mul, map_inv] using this
    obtain ⟨c, hc⟩ := scalar_of_map_conj_eq hM hK (by omega) h
    exact mem_center_of_scalar hc
  set Y : Subgroup L' := U.comap ψ with hY
  set V : Subgroup (MulAut L') := Y.map (MulAut.conj : L' →* MulAut L') with hV
  have hcentral : ∀ l : L', MulAut.conj l = 1 → l ∈ Subgroup.center L' := by
    intro l hl
    rw [Subgroup.mem_center_iff]
    intro x
    have := congrArg (fun f : MulAut L' => f x) hl
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * l = l * x * l⁻¹ * l := by rw [this]
      _ = l * x := by group
  have hV1 : V ≠ ⊥ := by
    obtain ⟨⟨u, huU⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU1
    obtain ⟨l, hl⟩ := hψ u
    have hlY : l ∈ Y := by
      show ψ l ∈ U
      rw [hl]
      exact huU
    intro hbot
    have h1 : MulAut.conj l ∈ V := ⟨l, hlY, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    have hlc := hcentral l h1
    have hψc : ψ l ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro r
      obtain ⟨x, rfl⟩ := hψ r
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hlc x]
    rw [hZR, Subgroup.mem_bot, hl] at hψc
    exact hu1 (Subtype.ext hψc)
  have hV2 : IsPGroup 2 V := by
    intro g
    obtain ⟨_, ⟨y, hy, rfl⟩⟩ := g
    obtain ⟨k, hk⟩ := hU2 ⟨ψ y, hy⟩
    have hk' : (ψ y) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    refine ⟨k, Subtype.ext ?_⟩
    have hyk : y ^ 2 ^ k ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_pow, hk']
    have hz := Subgroup.mem_center_iff.mp (hkerψ hyk)
    show (MulAut.conj y) ^ 2 ^ k = 1
    rw [← map_pow]
    ext x
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← hz x]
    group
  have hVφ : V ≤ φG.range := by
    rintro _ ⟨y, -, rfl⟩
    obtain ⟨s, rfl⟩ := hM.surj y
    exact ⟨s, rfl⟩
  have hinv : ∀ a ∈ A, ∀ v ∈ V, a * v * a⁻¹ ∈ V := by
    intro a ha v hv
    obtain ⟨y, hy, rfl⟩ := hv
    refine ⟨a y, ?_, ?_⟩
    · exact hAU a ha y hy
    · exact (TableBUR.mul_conj_mul_inv_eq a y).symm
  have hBV : A ≤ Subgroup.normalizer (V : Set (MulAut L')) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · exact hinv a ha v
    · intro h
      have h2 := hinv a⁻¹ (A.inv_mem ha) _ h
      have e : a⁻¹ * (a * v * a⁻¹) * a⁻¹⁻¹ = v := by group
      rwa [e] at h2
  obtain ⟨s, t, hst, hpair⟩ :=
    SURepair.exists_framePair_of_twoSubgroup hM.field hkerG hV1 hV2 hVφ hBV
  refine ⟨s, t, hst, fun a ha σ hσ => ?_⟩
  obtain ⟨ν, hν⟩ := exists_nu_actsU hM (by omega) hdiag s
  set τ : Fin d → Kˣ := ν ⟨a, ha⟩ with hτ
  have hτact : ActsU φ a τ := (hν ⟨a, ha⟩).1
  have hτs : τ s = 1 := (hν ⟨a, ha⟩).2
  have hτpow : ∀ i, τ i ^ p = 1 := fun i => by
    have := ActsU.pow_ratio hM (by omega) hτact (hAp a ha) i s
    rwa [hτs, inv_one, mul_one] at this
  have hτeq : τ s = τ t := by
    refine hpair a ha τ ⟨fun i => ?_, fun x x' hx' => ?_⟩
    · obtain ⟨m, hm⟩ := hpq
      have h1 : (τ i : K) ^ p = 1 := by
        have := congrArg (fun u : Kˣ => (u : K)) (hτpow i)
        simpa using this
      rw [hm, pow_mul, h1, one_pow]
    · obtain ⟨hD, hact⟩ := hτact
      have hx'e : x' = conjN (diagHom d τ) hD x := Subtype.ext (by rw [hx', coe_conjN])
      show a * MulAut.conj (φ x) * a⁻¹ = MulAut.conj (φ x')
      rw [TableBUR.mul_conj_mul_inv_eq, hact x, hx'e]
  have h1 := ActsU.ratio_eq' hM (by omega) hσ hτact s t
  rw [hτeq, mul_inv_cancel] at h1
  exact mul_inv_eq_one.mp h1

end CFSG.StandardType.SmallU

end
