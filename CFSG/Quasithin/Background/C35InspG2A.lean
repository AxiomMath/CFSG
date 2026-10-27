module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieG2Facts
public import CFSG.Quasithin.Background.C35InspLift

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.C35Pf

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank Matrix
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2
open scoped commutatorElement

section Levi

variable {G : Type*} [Group G]

theorem exists_levi_proj [Finite G] {P Q M L : Subgroup G} (hQP : Q ≤ P)
    (hN : P ≤ Subgroup.normalizer (Q : Set G)) (hQM : Q ⊓ M = ⊥) (hP : Q ⊔ M = P)
    (hLM : L ≤ M) (hL : ⁅L, L⁆ = L) (hM : perfectCore M ≤ L) :
    ∃ g : ↥(perfectCore P) →* ↥L, Function.Surjective g ∧
      ∀ x, ((g x : ↥L) : G)⁻¹ * (x : G) ∈ Q := by
  have hMP : M ≤ P := hP ▸ le_sup_right
  have hnorm : (Q.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).mpr hN
  let ψ : ↥M →* ↥P ⧸ Q.subgroupOf P :=
    (QuotientGroup.mk' (Q.subgroupOf P)).comp (Subgroup.inclusion hMP)
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro m hm
    rw [MonoidHom.mem_ker] at hm
    have h1 : Subgroup.inclusion hMP m ∈ Q.subgroupOf P :=
      (QuotientGroup.eq_one_iff _).mp hm
    have h2 : (m : G) ∈ Q ⊓ M := ⟨h1, m.2⟩
    rw [hQM, Subgroup.mem_bot] at h2
    rw [Subgroup.mem_bot]
    exact Subtype.ext h2
  have hψsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective y
    have hp : (p : G) ∈ ((M ⊔ Q : Subgroup G) : Set G) := by
      rw [sup_comm, hP]
      exact p.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right M Q (hMP.trans hN)] at hp
    obtain ⟨m, hm, q, hq, hpmq⟩ := hp
    refine ⟨⟨m, hm⟩, ?_⟩
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have : (((Subgroup.inclusion hMP ⟨m, hm⟩)⁻¹ * p : ↥P) : G) = q := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, ← hpmq]
      simp
    rw [this]
    exact hq
  let e : ↥M ≃* (↥P ⧸ Q.subgroupOf P) := MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  let lev : ↥P →* ↥M := e.symm.toMonoidHom.comp (QuotientGroup.mk' (Q.subgroupOf P))
  have hlev_M : ∀ (m : G) (hm : m ∈ M), lev ⟨m, hMP hm⟩ = ⟨m, hm⟩ := by
    intro m hm
    show e.symm (QuotientGroup.mk' (Q.subgroupOf P) ⟨m, hMP hm⟩) = ⟨m, hm⟩
    rw [MulEquiv.symm_apply_eq]
    rfl
  have hlev_dec : ∀ p : ↥P, ((lev p : ↥M) : G)⁻¹ * (p : G) ∈ Q := by
    intro p
    have h1 : ψ (lev p) = QuotientGroup.mk' (Q.subgroupOf P) p := by
      show e (e.symm (QuotientGroup.mk' (Q.subgroupOf P) p)) = _
      rw [MulEquiv.apply_symm_apply]
    have h2 : (Subgroup.inclusion hMP (lev p))⁻¹ * p ∈ Q.subgroupOf P := by
      rw [← QuotientGroup.eq]
      exact h1
    rw [Subgroup.mem_subgroupOf] at h2
    exact h2
  have hPcore : Group.IsPerfect ↥(perfectCore P) :=
    Subgroup.isPerfect_iff.mpr (perfectCore_perfect P)
  let ι : ↥(perfectCore P) →* ↥P := Subgroup.inclusion (perfectCore_le P)
  let f : ↥(perfectCore P) →* G := M.subtype.comp (lev.comp ι)
  have hrperf : ⁅f.range, f.range⁆ = f.range :=
    Subgroup.isPerfect_iff.mp (Group.IsPerfect.range f)
  have hrM : f.range ≤ M := by
    rintro _ ⟨x, rfl⟩
    exact (lev (ι x)).2
  have hrL : f.range ≤ L := (le_perfectCore_of_perfect hrM hrperf).trans hM
  refine ⟨f.codRestrict L fun x => hrL ⟨x, rfl⟩, ?_, fun x => hlev_dec (ι x)⟩
  intro l
  have hlP : (l : G) ∈ perfectCore P := le_perfectCore_of_perfect (hLM.trans hMP) hL l.2
  refine ⟨⟨l, hlP⟩, Subtype.ext ?_⟩
  have h1 := congrArg (fun m : ↥M => (m : G)) (hlev_M l (hLM l.2))
  exact h1

end Levi

section Data

variable {A : Type} [Group A] [Finite A]

omit [Finite A] in
theorem img_le_pCoreOf {K M₀ X : Subgroup A} {G' : Type} [Group G'] [Finite G']
    (θ : ↥K →* G') (hXM : X ≤ M₀) (hXn : M₀ ≤ Subgroup.normalizer (X : Set A))
    (hX2 : IsPGroup 2 ↥X) (hXK : X ≤ K) : img θ X ≤ pCoreOf 2 (img θ M₀) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.2 (hXM (Subgroup.mem_subgroupOf.1 hx)))
    ?_ ?_
  · rintro _ ⟨m, hm, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hmx : (m : A) * x * (m : A)⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.1 (hXn (Subgroup.mem_subgroupOf.1 hm)) x).1
          (Subgroup.mem_subgroupOf.1 hx)
      refine ⟨m * x * m⁻¹, Subgroup.mem_subgroupOf.2 hmx, ?_⟩
      rw [map_mul, map_mul, map_inv]
    · rintro ⟨z, hz, hzy⟩
      have hmz : (m : A)⁻¹ * z * (m : A) ∈ X := by
        have := (Subgroup.mem_normalizer_iff.1
          (Subgroup.inv_mem _ (hXn (Subgroup.mem_subgroupOf.1 hm))) z).1
          (Subgroup.mem_subgroupOf.1 hz)
        simpa using this
      refine ⟨m⁻¹ * z * m, Subgroup.mem_subgroupOf.2 hmz, ?_⟩
      rw [map_mul, map_mul, map_inv, hzy]
      group
  · have hXK' : IsPGroup 2 ↥(X.subgroupOf K) :=
      hX2.of_equiv (Subgroup.subgroupOfEquivOfLe hXK).symm
    exact hXK'.map θ

end Data

section G2

variable {F : Type} [Field F] [CharP F 2]

theorem g2_action
    (ρ : SL2 F →* ModGL Tag.G2 F) (hu : ∀ c, ρ (uSL c) = xUnit Tag.G2 F i0 c)
    (hH : ∀ t, ρ (HSL t) = torusElt Tag.G2 F i0 t) (hW : ρ WSL = weylElt Tag.G2 F i0 1)
    (D : SL2 F) (w : Fin 2 → F) :
    ρ D * (gX rB (w 1) * gX rC (w 0)) * (ρ D)⁻¹ =
      gX rB (((D : Matrix (Fin 2) (Fin 2) F) *ᵥ w) 1) *
        gX rC (((D : Matrix (Fin 2) (Fin 2) F) *ᵥ w) 0) := by
  have hB : IsRoot Tag.G2 rB := (isRoot_pos_iff.2 (by simp)).1
  have hC : IsRoot Tag.G2 rC := (isRoot_pos_iff.2 (by simp)).1
  revert w
  refine SL2_induction (p := fun D => ∀ w : Fin 2 → F,
    ρ D * (gX rB (w 1) * gX rC (w 0)) * (ρ D)⁻¹ =
      gX rB (((D : Matrix (Fin 2) (Fin 2) F) *ᵥ w) 1) *
        gX rC (((D : Matrix (Fin 2) (Fin 2) F) *ᵥ w) 0)) ?_ ?_ ?_ ?_ D
  · intro g g' hg hg' w
    have e : ρ (g * g') * (gX rB (w 1) * gX rC (w 0)) * (ρ (g * g'))⁻¹ =
        ρ g * (ρ g' * (gX rB (w 1) * gX rC (w 0)) * (ρ g')⁻¹) * (ρ g)⁻¹ := by
      rw [map_mul]
      group
    rw [e, hg', hg]
    have hm : ((g * g' : SL2 F) : Matrix (Fin 2) (Fin 2) F) *ᵥ w =
        (g : Matrix (Fin 2) (Fin 2) F) *ᵥ ((g' : Matrix (Fin 2) (Fin 2) F) *ᵥ w) := by
      rw [Matrix.mulVec_mulVec]
      rfl
    rw [hm]
  · intro c w
    rw [hu, rootOne_gX_i0]
    have h1 : gX rA c * gX rB (w 1) * (gX rA c)⁻¹ = gX rC (c * w 1) * gX rB (w 1) := by
      have h := rel_ab c (w 1)
      rw [commutatorElement_def] at h
      calc gX rA c * gX rB (w 1) * (gX rA c)⁻¹ =
            (gX rA c * gX rB (w 1) * (gX rA c)⁻¹ * (gX rB (w 1))⁻¹) * gX rB (w 1) := by group
        _ = _ := by rw [h]
    have h2 : gX rA c * gX rC (w 0) * (gX rA c)⁻¹ = gX rC (w 0) := by
      rw [(comm_ac c (w 0)).eq, mul_inv_cancel_right]
    have h3 : ((uSL c : SL2 F) : Matrix (Fin 2) (Fin 2) F) *ᵥ w = ![w 0 + c * w 1, w 1] := by
      ext i
      fin_cases i <;> simp [coe_uSL, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [h3]
    have e1 : gX rA c * (gX rB (w 1) * gX rC (w 0)) * (gX rA c)⁻¹ =
        (gX rA c * gX rB (w 1) * (gX rA c)⁻¹) * (gX rA c * gX rC (w 0) * (gX rA c)⁻¹) := by
      group
    have e2 : gX rC (c * w 1) * gX rB (w 1) * gX rC (w 0) =
        gX rB (w 1) * (gX rC (c * w 1) * gX rC (w 0)) := by
      rw [← (comm_bc (w 1) (c * w 1)).eq]
      group
    rw [e1, h1, h2, e2, ← gX_add, add_comm]
    simp
  · intro t w
    rw [hH]
    have hb : ∑ j, Tag.G2.cartan i0 j * rB j = -1 := by decide
    have hc : ∑ j, Tag.G2.cartan i0 j * rC j = 1 := by decide
    have h1 := root_torus_conjugation (R := F) i0 hB t (w 1)
    have h2 := root_torus_conjugation (R := F) i0 hC t (w 0)
    rw [hb, _root_.zpow_neg, zpow_one] at h1
    rw [hc, zpow_one] at h2
    have h3 : ((HSL t : SL2 F) : Matrix (Fin 2) (Fin 2) F) *ᵥ w =
        ![(t : F) * w 0, ((t⁻¹ : Fˣ) : F) * w 1] := by
      ext i
      fin_cases i <;> simp [coe_HSL, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [h3]
    have e1 : torusElt Tag.G2 F i0 t * (gX rB (w 1) * gX rC (w 0)) *
        (torusElt Tag.G2 F i0 t)⁻¹ =
          (torusElt Tag.G2 F i0 t * gX rB (w 1) * (torusElt Tag.G2 F i0 t)⁻¹) *
            (torusElt Tag.G2 F i0 t * gX rC (w 0) * (torusElt Tag.G2 F i0 t)⁻¹) := by
      group
    rw [e1, h1, h2]
    simp
  · intro w
    rw [hW]
    have hrb : reflect Tag.G2 i0 rB = rC := by decide
    have hrc : reflect Tag.G2 i0 rC = rB := by decide
    have hε : ∀ {α : Fin Tag.G2.rank → ℤ}, IsRoot Tag.G2 α → ∀ c : F,
        weylElt Tag.G2 F i0 1 * gX α c * (weylElt Tag.G2 F i0 1)⁻¹ =
          gX (reflect Tag.G2 i0 α) c := by
      intro α hα c
      obtain ⟨ε, hε1, h⟩ := weylElt_mul_pinnedX_mul_inv F i0 hα
      have hε' : ε = 1 := by
        have h2 : (ε - 1) ^ 2 = 0 := by
          linear_combination hε1 + (1 - ε) * (CharTwo.two_eq_zero : (2 : F) = 0)
        exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)
      rw [h, hε', one_mul]
    have h3 : ((WSL : SL2 F) : Matrix (Fin 2) (Fin 2) F) *ᵥ w = ![w 1, w 0] := by
      ext i
      fin_cases i <;> simp [coe_WSL, Matrix.mulVec, dotProduct, Fin.sum_univ_two, CharTwo.neg_eq]
    rw [h3]
    have e1 : weylElt Tag.G2 F i0 1 * (gX rB (w 1) * gX rC (w 0)) *
        (weylElt Tag.G2 F i0 1)⁻¹ =
          (weylElt Tag.G2 F i0 1 * gX rB (w 1) * (weylElt Tag.G2 F i0 1)⁻¹) *
            (weylElt Tag.G2 F i0 1 * gX rC (w 0) * (weylElt Tag.G2 F i0 1)⁻¹) := by
      group
    rw [e1, hε hB, hε hC, hrb, hrc, ← (comm_bc (w 0) (w 1)).eq]
    simp

end G2

end CFSG.Quasithin.C35Pf
