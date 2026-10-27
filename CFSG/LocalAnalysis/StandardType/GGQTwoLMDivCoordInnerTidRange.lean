module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerLift
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerRigid
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerTor
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary Matrix

variable {G : Type} [Group G] [Finite G]

theorem qTwoLMDivCoordInner_tid_range {B Bs L : Subgroup G} (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {m : ℕ} (hm : 4 ≤ m) (h3 : 3 ∣ m)
    {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {L0 : Type} [Group L0]
    {c : ↥L →* L0} {π : Su F0 2 1 m →* L0} {ρ : ↥Bs →* MulAut L0}
    (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) {δ : ↥(sumZero m 3) →* Su F0 2 1 m}
    (hδ : QTwoDivTorus h3 δ) {τ : ↥(sumZero m 3) →* ↥L} (hτ : QTwoDivLift Bs L c π δ τ) :
    ∀ t : ↥L, (t : G) ∈ Bs → ∃ f, τ f = t := by
  intro t ht
  let b : ↥Bs := ⟨(t : G), ht⟩
  obtain ⟨u, hu⟩ := hU.π_surj (c t)
  obtain ⟨g, hgdiag, hgact⟩ := hU.diag b
  let k : GL (Fin m) F0 := (u : GL (Fin m) F0)⁻¹ * g
  have huk : (u : GL (Fin m) F0) * k = g := by
    dsimp only [k]
    group
  have hconj : ∀ s : Su F0 2 1 m, π (u * s * u⁻¹) = ρ b (π s) := by
    intro s
    obtain ⟨l, hcl⟩ := hU.c_surj (π s)
    have hind := hU.induced b l
    rw [hcl] at hind
    have hc : c (⟨(b : G) * l * (b : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hN b.2) l).mp l.2⟩ : ↥L) =
        c t * π s * (c t)⁻¹ := by
      rw [show (⟨(b : G) * l * (b : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hN b.2) l).mp l.2⟩ : ↥L) = t * l * t⁻¹ from
        Subtype.ext rfl]
      rw [map_mul, map_mul, map_inv, hcl]
    have hpu : π (u * s * u⁻¹) = π u * π s * (π u)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [hpu, hu, ← hind, hc]
  have hk : ∀ s : Su F0 2 1 m, ∃ s' : Su F0 2 1 m,
      (s' : GL (Fin m) F0) = k * (s : GL (Fin m) F0) * k⁻¹ ∧ π s' = π s := by
    intro s
    obtain ⟨s', hs'g, hs'π⟩ := hgact s
    refine ⟨u⁻¹ * s' * u, ?_, ?_⟩
    · have h1 : ((u⁻¹ * s' * u : Su F0 2 1 m) : GL (Fin m) F0) =
          (u : GL (Fin m) F0)⁻¹ * (s' : GL (Fin m) F0) * (u : GL (Fin m) F0) := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [h1, hs'g]
      dsimp only [k]
      group
    · have hps' : π s' = π u * π s * (π u)⁻¹ := by
        rw [← hs'π, ← hconj s, map_mul, map_mul, map_inv]
      have hpi : π (u⁻¹ * s' * u) = (π u)⁻¹ * π s' * π u := by
        rw [map_mul, map_mul, map_inv]
      rw [hpi, hps']
      group
  obtain ⟨c₀, hk₀⟩ := qTwoLMDivCoordInner_rigid hU.card hm π hU.π_ker hk
  have hc₀ : c₀ ≠ 0 := by
    intro hc
    have hkt : ((k : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
        (((k⁻¹ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)) = 1 := by
      simpa using congrArg (fun x : GL (Fin m) F0 =>
        ((x : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)) (mul_inv_cancel k)
    have hzero : ((k : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) = 0 := by
      rw [hk₀, hc]
      simp
    rw [hzero, Matrix.zero_mul] at hkt
    have h00 : (0 : F0) = 1 := by
      simpa using congrFun (congrFun hkt ⟨0, by omega⟩) ⟨0, by omega⟩
    exact zero_ne_one h00
  have hudiag : ggIsDiagMat (u : GL (Fin m) F0) := by
    obtain ⟨d, hd⟩ := hgdiag
    have hmult : ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
        (((k : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)) =
        ((g : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) := by
      simpa using congrArg (fun x : GL (Fin m) F0 =>
        ((x : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)) huk
    have hmult' : ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
        Matrix.diagonal (fun _ => c₀) = Matrix.diagonal d := by
      rw [← hk₀, ← hd]
      exact hmult
    refine ⟨fun i => ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) i i, ?_⟩
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
    · have hentry := congrFun (congrFun hmult' i) j
      rw [Matrix.mul_diagonal] at hentry
      rw [Matrix.diagonal_apply_ne
        (fun i => ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) i i) hij]
      rw [Matrix.diagonal_apply_ne d hij, mul_eq_zero] at hentry
      rcases hentry with h | h
      · exact h
      · exact absurd h hc₀
  obtain ⟨f, hf⟩ := hδ.surj_diag u hudiag
  have hct : c t = c (τ f) := by
    rw [← hu, ← hf]
    exact (hτ.comm f).symm
  let z : ↥L := (τ f)⁻¹ * t
  have hzmem : z ∈ c.ker := by
    rw [MonoidHom.mem_ker]
    dsimp only [z]
    rw [map_mul, map_inv, hct, inv_mul_cancel]
  have hzBs : (z : G) ∈ Bs := by
    dsimp only [z]
    simpa using Bs.mul_mem (Bs.inv_mem (hτ.mem f)) ht
  have hz3 : z ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hBs.2.1.2 (z : G) hzBs
  have hz1 : z = 1 := by
    by_contra hne
    have h2dvd : 2 ∣ orderOf z := by
      have hne' : (⟨z, hzmem⟩ : c.ker) ≠ 1 := by
        intro h
        exact hne (Subtype.ext_iff.mp h)
      have hdo := hU.c_two.dvd_orderOf hne'
      rwa [Subgroup.orderOf_mk] at hdo
    have h3dvd : orderOf z ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hz3
    have h23 : (2 : ℕ) ∣ 3 := dvd_trans h2dvd h3dvd
    exact (by norm_num : ¬ (2 : ℕ) ∣ 3) h23
  have htz : t = τ f := by
    have h : (τ f)⁻¹ * t = 1 := by
      have h' := hz1
      dsimp only [z] at h'
      exact h'
    have h2 := congrArg (fun x : ↥L => τ f * x) h
    simpa using h2
  exact ⟨f, htz.symm⟩

end CFSG.StandardType.QTwo

end
