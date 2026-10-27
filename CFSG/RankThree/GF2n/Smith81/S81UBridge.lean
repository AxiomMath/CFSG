module

public import CFSG.RankThree.GF2n.Smith81.S81UModelDef
public import CFSG.RankThree.GF2n.Smith81.S81UModel
public import CFSG.RankThree.GF2n.Smith81.S81UTheta
public import CFSG.RankThree.GF2n.Smith81.S81BA5Def
public import CFSG.RankThree.GF2n.Stroth80.Sec12CaseVIEquiv

public section

namespace CFSG.RankThree.GF2n.Smith81.E3UBridge

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81
  CFSG.RankThree.GF2n.Smith81.EGeom CFSG.RankThree.GF2n.Smith81.U6Cube
  CFSG.RankThree.GF2n.Smith81.A5Cube CFSG.RankThree.GF2n.Smith81.E3LCond
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
  {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F} {e : K ≃+* Fσ σ}
  {ψ : M₀.E ≃ₗ[K] E3UWspace σ e} {φ : Lgen M (LB M Q B) →* (E3UWspace σ e ≃ₗ[K] E3UWspace σ e)}

theorem exists_lift_U (d : EUniData M Q Z B M₀ ψ φ (e3uGam σ e) (e3uP0 σ e) (e3uU0 σ e))
    (g : SUid σ 6) : ∃ s : Lgen M (LB M Q B), φ s = e3uWact σ e g := by
  have hgG : e3uWact σ e g ∈ e3uGam σ e := ⟨g, rfl⟩
  rw [← d.range] at hgG
  obtain ⟨s, hs⟩ := hgG
  exact ⟨s, hs⟩

theorem psi_T_U (d : EUniData M Q Z B M₀ ψ φ (e3uGam σ e) (e3uP0 σ e) (e3uU0 σ e)) {x : G}
    (hxL : x ∈ Lgen M (LB M Q B)) (Tx : XAct M₀ x) {t : SUid σ 6}
    (hφ : φ ⟨x, hxL⟩ = e3uWact σ e t) (e' : M₀.E) : ψ (Tx.T e') = e3uWact σ e t (ψ e') := by
  obtain ⟨y, hy, rfl⟩ := M₀.π_surj e'
  rw [← Tx.hπ y hy, d.equivariant ⟨x, hxL⟩ y hy, hφ]

theorem mem_Cs_iff_U (d : EUniData M Q Z B M₀ ψ φ (e3uGam σ e) (e3uP0 σ e) (e3uU0 σ e))
    {x : G} (hxL : x ∈ Lgen M (LB M Q B)) (Tx : XAct M₀ x) {t : SUid σ 6}
    (hφ : φ ⟨x, hxL⟩ = e3uWact σ e t) {e' : M₀.E} :
    e' ∈ Cs Tx ↔ (show Wform σ from ψ e') ∈ Cw σ t := by
  rw [mem_Cs, ← ψ.injective.eq_iff, psi_T_U d hxL Tx hφ]
  exact Iff.rfl

theorem mem_Rs_iff_U (d : EUniData M Q Z B M₀ ψ φ (e3uGam σ e) (e3uP0 σ e) (e3uU0 σ e))
    {x : G} (hxL : x ∈ Lgen M (LB M Q B)) (Tx : XAct M₀ x) {t : SUid σ 6}
    (hφ : φ ⟨x, hxL⟩ = e3uWact σ e t) {r : M₀.E} :
    r ∈ Rs Tx ↔ (show Wform σ from ψ r) ∈ Rw σ t := by
  rw [mem_Rs]
  constructor
  · rintro ⟨e', he'⟩
    refine ⟨show Wform σ from ψ e', ?_⟩
    have h1 : ψ (Tx.T e' - e') = ψ r := by rw [he']
    rw [map_sub, psi_T_U d hxL Tx hφ] at h1
    exact h1.symm
  · rintro ⟨w, hw⟩
    refine ⟨ψ.symm (show E3UWspace σ e from w), ψ.injective ?_⟩
    rw [map_sub, psi_T_U d hxL Tx hφ, LinearEquiv.apply_symm_apply]
    exact hw.symm

theorem comm_mem_Q_of_lift_U (d : EUniData M Q Z B M₀ ψ φ (e3uGam σ e) (e3uP0 σ e) (e3uU0 σ e))
    {x u : G} (hxL : x ∈ Lgen M (LB M Q B)) (hu : u ∈ Lgen M (LB M Q B)) {t g : SUid σ 6}
    (hφx : φ ⟨x, hxL⟩ = e3uWact σ e t) (hφu : φ ⟨u, hu⟩ = e3uWact σ e g)
    (hcomm : g * t = t * g) : ⁅u, x⁆ ∈ Q := by
  have h1 : φ (⟨u, hu⟩ * ⟨x, hxL⟩ * ⟨u, hu⟩⁻¹ * ⟨x, hxL⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hφx, hφu]
    have : e3uWact σ e g * e3uWact σ e t = e3uWact σ e t * e3uWact σ e g := by
      rw [← map_mul, ← map_mul, hcomm]
    rw [this]
    group
  have := (d.ker _).mp h1
  simpa [commutatorElement_def] using this

private theorem e3uVal_smul_K_U (k : K) (y : E3UWspace σ e) :
    e3uVal (k • y) = ((e k : Fσ σ) : F) • e3uVal y := rfl

private theorem e3uVal_injective_U {w w' : E3UWspace σ e} (h : e3uVal w = e3uVal w') : w = w' :=
  Subtype.ext h

theorem exists_root_group_U
    (hRoot : ∀ ξ ∈ RootPt σ, ∃ (g : SUid σ 6) (c : F), c ≠ 0 ∧ σ c = c ∧
      ξ = c • rho F (g : GL (Fin 6) F) (pt0 F))
    (d : EUniData M Q Z B M₀ ψ φ (e3uGam σ e) (e3uP0 σ e) (e3uU0 σ e)) (Hs : StrothHyp M Q Z)
    {w : E3UWspace σ e} (hw : e3uVal w ∈ RootPt σ) :
    ∃ A : Subgroup G, IsZConjugate Z A ∧ A ≤ Q ∧ A ≠ Z ∧ ∃ a ∈ A, ψ (M₀.π a) = w := by
  obtain ⟨A₀, hctx₀⟩ := exists_ctx_of_strothHyp Hs
  obtain ⟨g₀, hg₀, himg₀, -⟩ := d.point A₀ hctx₀.conj hctx₀.le hctx₀.ne
  have hg₀' : g₀ ∈ (e3uWact σ e).range := hg₀
  obtain ⟨h₀, rfl⟩ := MonoidHom.mem_range.mp hg₀'
  obtain ⟨g, c, hc0, hcs, hw_eq⟩ := hRoot (e3uVal w) hw
  have hcF : c ∈ Fσ σ := mem_Fσ_iff.mpr hcs
  obtain ⟨k, hk⟩ : ∃ k : K, e k = ⟨c, hcF⟩ := ⟨e.symm ⟨c, hcF⟩, e.apply_symm_apply _⟩
  have hkc : ((e k : Fσ σ) : F) = c := congrArg Subtype.val hk
  have hval : e3uVal (e3uP0 σ e) = pt0 F := rfl
  have hwk : w = k • e3uWact σ e g (e3uP0 σ e) := by
    apply e3uVal_injective_U
    rw [e3uVal_smul_K_U, hkc, e3uWact_val, hval]
    exact hw_eq
  have hrho0 : rho F (g : GL (Fin 6) F) (pt0 F) ≠ 0 := fun h =>
    pt0_ne_zero (K := F) ((rhoEquiv F (g : GL (Fin 6) F)).map_eq_zero_iff.mp h)
  have hw0 : w ≠ 0 := by
    intro h0
    have h1 : e3uVal w = 0 := by rw [h0]; rfl
    rw [hw_eq] at h1
    rcases smul_eq_zero.mp h1 with h2 | h2
    · exact hc0 h2
    · exact hrho0 h2
  have hmem : k • e3uWact σ e h₀ (e3uP0 σ e) ∈ (fun a : G => ψ (M₀.π a)) '' (A₀ : Set G) := by
    rw [himg₀]
    exact Submodule.smul_mem _ k (Submodule.mem_span_singleton_self _)
  obtain ⟨a₀, ha₀, ha₀eq⟩ := hmem
  obtain ⟨s, hs⟩ := exists_lift_U d (g * h₀⁻¹)
  have hcomp : e3uWact σ e (g * h₀⁻¹) (e3uWact σ e h₀ (e3uP0 σ e)) =
      e3uWact σ e g (e3uP0 σ e) := by
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel_right]
  obtain ⟨g', hg'⟩ := hctx₀.conj
  have hsQ : ∀ y ∈ Q, (s : G) * y * (s : G)⁻¹ ∈ Q := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (d.le_normalizer s.2) y).mp hy
  have hA₀Q : a₀ ∈ Q := hctx₀.le ha₀
  have haA : (s : G) * a₀ * (s : G)⁻¹ ∈ conjSubgroup (s : G) A₀ := by
    rw [mem_conjSubgroup]
    have e' : (s : G)⁻¹ * ((s : G) * a₀ * (s : G)⁻¹) * (s : G) = a₀ := by group
    rw [e']
    exact ha₀
  have hψa : ψ (M₀.π ((s : G) * a₀ * (s : G)⁻¹)) = w := by
    have ha₀eq' : ψ (M₀.π a₀) = k • e3uWact σ e h₀ (e3uP0 σ e) := ha₀eq
    rw [d.equivariant s a₀ hA₀Q, ha₀eq', hs, LinearEquiv.map_smul, hcomp]
    exact hwk.symm
  have haQ : (s : G) * a₀ * (s : G)⁻¹ ∈ Q := hsQ a₀ hA₀Q
  refine ⟨conjSubgroup (s : G) A₀, ⟨(s : G) * g', by rw [hg', conjSubgroup_mul]⟩, ?_, ?_,
    _, haA, hψa⟩
  · intro y hy
    have h1 : (s : G)⁻¹ * y * (s : G) ∈ Q := hctx₀.le (mem_conjSubgroup.mp hy)
    have e' : y = (s : G) * ((s : G)⁻¹ * y * (s : G)) * (s : G)⁻¹ := by group
    rw [e']
    exact hsQ _ h1
  · intro hAZ
    have haZ : (s : G) * a₀ * (s : G)⁻¹ ∈ Z := hAZ ▸ haA
    apply hw0
    rw [← hψa, (M₀.π_ker _ haQ).mpr haZ, map_zero]

theorem rootPt_of_RootPt_U
    (hRoot : ∀ ξ ∈ RootPt σ, ∃ (g : SUid σ 6) (c : F), c ≠ 0 ∧ σ c = c ∧
      ξ = c • rho F (g : GL (Fin 6) F) (pt0 F))
    (d : EUniData M Q Z B M₀ ψ φ (e3uGam σ e) (e3uP0 σ e) (e3uU0 σ e)) (Hs : StrothHyp M Q Z)
    {w : E3UWspace σ e} (hw : e3uVal w ∈ RootPt σ) : RootPt M₀ (ψ.symm w) := by
  obtain ⟨A, hA, hAQ, hAZ, a, haA, ha⟩ := exists_root_group_U hRoot d Hs hw
  exact Or.inr ⟨A, hA, hAQ, hAZ, a, haA, by rw [← ha, LinearEquiv.symm_apply_apply]⟩

theorem B_invariant_U (hc : Ctx M Q Z B)
    (d : EUniData M Q Z B M₀ ψ φ (e3uGam σ e) (e3uP0 σ e) (e3uU0 σ e)) (g : SUid σ 6)
    (u v : E3UWspace σ e) :
    M₀.B (ψ.symm (e3uWact σ e g u)) (ψ.symm (e3uWact σ e g v)) = M₀.B (ψ.symm u) (ψ.symm v) := by
  obtain ⟨s, hs⟩ := exists_lift_U d g
  obtain ⟨a, ha, haπ⟩ := M₀.π_surj (ψ.symm u)
  obtain ⟨b, hb, hbπ⟩ := M₀.π_surj (ψ.symm v)
  have hsQ : ∀ y ∈ Q, (s : G) * y * (s : G)⁻¹ ∈ Q := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (d.le_normalizer s.2) y).mp hy
  have hsZ : ∀ z ∈ Z, (s : G) * z * (s : G)⁻¹ = z := by
    intro z hz
    have hzs : z * (s : G) = (s : G) * z :=
      Subgroup.mem_centralizer_iff.mp (Lgen_le_H0 hc s.2).2 z hz
    rw [← hzs, mul_inv_cancel_right]
  have hu : ψ (M₀.π a) = u := by rw [haπ, LinearEquiv.apply_symm_apply]
  have hv : ψ (M₀.π b) = v := by rw [hbπ, LinearEquiv.apply_symm_apply]
  have hLa : ψ (M₀.π ((s : G) * a * (s : G)⁻¹)) = e3uWact σ e g u := by
    rw [d.equivariant s a ha, hs, hu]
  have hLb : ψ (M₀.π ((s : G) * b * (s : G)⁻¹)) = e3uWact σ e g v := by
    rw [d.equivariant s b hb, hs, hv]
  have ha' : ψ.symm (e3uWact σ e g u) = M₀.π ((s : G) * a * (s : G)⁻¹) := by
    rw [← hLa, LinearEquiv.symm_apply_apply]
  have hb' : ψ.symm (e3uWact σ e g v) = M₀.π ((s : G) * b * (s : G)⁻¹) := by
    rw [← hLb, LinearEquiv.symm_apply_apply]
  have ha'Q : (s : G) * a * (s : G)⁻¹ ∈ Q := hsQ a ha
  have hb'Q : (s : G) * b * (s : G)⁻¹ ∈ Q := hsQ b hb
  calc M₀.B (ψ.symm (e3uWact σ e g u)) (ψ.symm (e3uWact σ e g v))
      = M₀.B (M₀.π ((s : G) * a * (s : G)⁻¹)) (M₀.π ((s : G) * b * (s : G)⁻¹)) := by
        rw [ha', hb']
    _ = γ ⁅(s : G) * a * (s : G)⁻¹, (s : G) * b * (s : G)⁻¹⁆ :=
        (M₀.comm_eq _ ha'Q _ hb'Q).symm
    _ = γ ((s : G) * ⁅a, b⁆ * (s : G)⁻¹) := by
        congr 1
        simp only [commutatorElement_def]
        group
    _ = γ ⁅a, b⁆ := by rw [hsZ _ (M₀.comm_mem a ha b hb)]
    _ = M₀.B (M₀.π a) (M₀.π b) := M₀.comm_eq a ha b hb
    _ = M₀.B (ψ.symm u) (ψ.symm v) := by rw [haπ, hbπ]

theorem hform_U
    (hForm : ∀ (B' : Wform σ →ₗ[Fσ σ] Wform σ →ₗ[Fσ σ] Fσ σ),
      (∀ (g : SUid σ 6) (u v : Wform σ), B' (Wact σ g u) (Wact σ g v) = B' u v) →
        ∃ lam : F, ∀ u v : Wform σ, ((B' u v : Fσ σ) : F) = lam * beta F (u : Cube F) (v : Cube F))
    (hc : Ctx M Q Z B) (d : EUniData M Q Z B M₀ ψ φ (e3uGam σ e) (e3uP0 σ e) (e3uU0 σ e)) :
    ∃ lam : F, lam ≠ 0 ∧ ∀ e' f' : M₀.E,
      ((e (M₀.B e' f') : Fσ σ) : F) = lam * beta F (e3uVal (ψ e')) (e3uVal (ψ f')) := by
  let toE : Wform σ → E3UWspace σ e := fun w => w
  let fromE : E3UWspace σ e → Wform σ := fun w => w
  have hsm : ∀ (c : Fσ σ) (w : Wform σ), e.symm c • toE w = toE (c • w) := by
    intro c w
    have h := e3uWspace_smul_def σ e (e.symm c) (toE w)
    rw [RingEquiv.apply_symm_apply] at h
    exact h
  have hadd : ∀ x y : Wform σ, toE (x + y) = toE x + toE y := fun _ _ => rfl
  have hψk : ∀ (k : K) (x : E3UWspace σ e), ψ.symm (k • x) = k • ψ.symm x :=
    fun k x => map_smul ψ.symm k x
  have hBk1 : ∀ (k : K) (x y : M₀.E), M₀.B (k • x) y = k • M₀.B x y := by
    intro k x y
    rw [map_smul, LinearMap.smul_apply]
  have hBk : ∀ (k : K) (x y : M₀.E), M₀.B x (k • y) = k • M₀.B x y :=
    fun k x y => map_smul (M₀.B x) k y
  have hBadd1 : ∀ x y z : M₀.E, M₀.B (x + y) z = M₀.B x z + M₀.B y z := by
    intro x y z
    rw [map_add, LinearMap.add_apply]
  have hBadd2 : ∀ x y z : M₀.E, M₀.B x (y + z) = M₀.B x y + M₀.B x z :=
    fun x y z => map_add (M₀.B x) y z
  have L1 : ∀ x y z : E3UWspace σ e,
      e (M₀.B (ψ.symm (x + y)) (ψ.symm z)) =
        e (M₀.B (ψ.symm x) (ψ.symm z)) + e (M₀.B (ψ.symm y) (ψ.symm z)) := by
    intro x y z
    rw [map_add ψ.symm, hBadd1, map_add e]
  have L2 : ∀ x y z : E3UWspace σ e,
      e (M₀.B (ψ.symm x) (ψ.symm (y + z))) =
        e (M₀.B (ψ.symm x) (ψ.symm y)) + e (M₀.B (ψ.symm x) (ψ.symm z)) := by
    intro x y z
    rw [map_add ψ.symm, hBadd2, map_add e]
  have L3 : ∀ (c : Fσ σ) (x y : E3UWspace σ e),
      e (M₀.B (ψ.symm (e.symm c • x)) (ψ.symm y)) = c * e (M₀.B (ψ.symm x) (ψ.symm y)) := by
    intro c x y
    rw [hψk, hBk1, smul_eq_mul, map_mul, RingEquiv.apply_symm_apply]
  have L4 : ∀ (c : Fσ σ) (x y : E3UWspace σ e),
      e (M₀.B (ψ.symm x) (ψ.symm (e.symm c • y))) = c * e (M₀.B (ψ.symm x) (ψ.symm y)) := by
    intro c x y
    rw [hψk, hBk, smul_eq_mul, map_mul, RingEquiv.apply_symm_apply]
  let Bw : Wform σ → Wform σ → Fσ σ := fun u v =>
    e (M₀.B (ψ.symm (toE u)) (ψ.symm (toE v)))
  have H1 : ∀ (m₁ m₂ n : Wform σ), Bw (m₁ + m₂) n = Bw m₁ n + Bw m₂ n := by
    intro m₁ m₂ n
    show e (M₀.B (ψ.symm (toE (m₁ + m₂))) (ψ.symm (toE n))) =
      e (M₀.B (ψ.symm (toE m₁)) (ψ.symm (toE n))) + e (M₀.B (ψ.symm (toE m₂)) (ψ.symm (toE n)))
    rw [hadd]
    exact L1 (toE m₁) (toE m₂) (toE n)
  have H2 : ∀ (c : Fσ σ) (m n : Wform σ), Bw (c • m) n = c • Bw m n := by
    intro c m n
    show e (M₀.B (ψ.symm (toE (c • m))) (ψ.symm (toE n))) =
      c • e (M₀.B (ψ.symm (toE m)) (ψ.symm (toE n)))
    rw [← hsm c m]
    exact L3 c (toE m) (toE n)
  have H3 : ∀ (m n₁ n₂ : Wform σ), Bw m (n₁ + n₂) = Bw m n₁ + Bw m n₂ := by
    intro m n₁ n₂
    show e (M₀.B (ψ.symm (toE m)) (ψ.symm (toE (n₁ + n₂)))) =
      e (M₀.B (ψ.symm (toE m)) (ψ.symm (toE n₁))) + e (M₀.B (ψ.symm (toE m)) (ψ.symm (toE n₂)))
    rw [hadd]
    exact L2 (toE m) (toE n₁) (toE n₂)
  have H4 : ∀ (c : Fσ σ) (m n : Wform σ), Bw m (c • n) = c • Bw m n := by
    intro c m n
    show e (M₀.B (ψ.symm (toE m)) (ψ.symm (toE (c • n)))) =
      c • e (M₀.B (ψ.symm (toE m)) (ψ.symm (toE n)))
    rw [← hsm c n]
    exact L4 c (toE m) (toE n)
  let B' : Wform σ →ₗ[Fσ σ] Wform σ →ₗ[Fσ σ] Fσ σ := LinearMap.mk₂ (Fσ σ) Bw H1 H2 H3 H4
  have hB'app : ∀ u v : Wform σ, B' u v = Bw u v := fun _ _ => rfl
  have hinv : ∀ (g : SUid σ 6) (u v : Wform σ), B' (Wact σ g u) (Wact σ g v) = B' u v := by
    intro g u v
    rw [hB'app, hB'app]
    exact congrArg e (B_invariant_U hc d g (toE u) (toE v))
  obtain ⟨lam, hlam⟩ := hForm B' hinv
  have hformula : ∀ x y : M₀.E,
      ((e (M₀.B x y) : Fσ σ) : F) = lam * beta F (e3uVal (ψ x)) (e3uVal (ψ y)) := by
    intro x y
    have h1 := hlam (fromE (ψ x)) (fromE (ψ y))
    have h2 : B' (fromE (ψ x)) (fromE (ψ y)) = e (M₀.B x y) := by
      rw [hB'app]
      show e (M₀.B (ψ.symm (ψ x)) (ψ.symm (ψ y))) = e (M₀.B x y)
      rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    rw [h2] at h1
    exact h1
  refine ⟨lam, ?_, hformula⟩
  intro h0
  have hzero : ∀ x y : M₀.E, M₀.B x y = 0 := by
    intro x y
    have h1 := hformula x y
    rw [h0, zero_mul] at h1
    apply e.injective
    rw [map_zero]
    exact Subtype.ext h1
  have hall : ∀ x : M₀.E, x = 0 := fun x => M₀.nondeg x (fun y => hzero x y)
  have hP : e3uP0 σ e ≠ 0 := fun h =>
    CFSG.RankThree.GF2n.Smith81.U6Cube.pt0_ne_zero (K := F) (congrArg e3uVal h)
  apply hP
  calc e3uP0 σ e = ψ (ψ.symm (e3uP0 σ e)) := (ψ.apply_symm_apply _).symm
    _ = ψ 0 := by rw [hall (ψ.symm (e3uP0 σ e))]
    _ = 0 := map_zero ψ

theorem mem_closure_symm {A A' : Type*} [AddCommGroup A] [AddCommGroup A'] (f : A ≃+ A')
    {S : Set A} {S' : Set A'} (hS : ∀ b ∈ S', f.symm b ∈ S) {b : A'}
    (hb : b ∈ AddSubgroup.closure S') : f.symm b ∈ AddSubgroup.closure S := by
  induction hb using AddSubgroup.closure_induction with
  | mem b hb => exact AddSubgroup.subset_closure (hS b hb)
  | zero => rw [map_zero]; exact zero_mem _
  | add b c _ _ hb hc => rw [map_add]; exact add_mem hb hc
  | neg b _ hb => rw [map_neg]; exact neg_mem hb

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
  {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F} {e : K ≃+* Fσ σ}
  {ψ : M₀.E ≃ₗ[K] E3UWspace σ e} {φ : Lgen M (LB M Q B) →* (E3UWspace σ e ≃ₗ[K] E3UWspace σ e)}
  {X : Subgroup G} {x : G}

theorem covW_transport (hc : Ctx M Q Z B)
    (d : EUniData M Q Z B M₀ ψ φ (e3uGam σ e) (e3uP0 σ e) (e3uU0 σ e)) {t : SUid σ 6}
    (hW : ∀ w : Wform σ,
      w ∈ AddSubgroup.closure {v | ∃ g ∈ Gcent σ t, ∃ w' : Wform σ, v = Wact σ g w' - w'}) :
    ∀ e' : M₀.E, e' ∈ AddSubgroup.closure {f | ∃ u ∈ {u : G | ∃ hu : u ∈ Lgen M (LB M Q B),
        ∃ g ∈ Gcent σ t, φ ⟨u, hu⟩ = e3uWact σ e g}, ∃ w ∈ Q, f = M₀.π (u * w * u⁻¹) - M₀.π w} := by
  intro e'
  have hb : ψ e' ∈ AddSubgroup.closure {v : E3UWspace σ e | ∃ g ∈ Gcent σ t,
      ∃ w' : E3UWspace σ e, v = e3uWact σ e g w' - w'} :=
    hW (show Wform σ from ψ e')
  have h2 : (LinearEquiv.toAddEquiv ψ).symm (ψ e') = e' := ψ.symm_apply_apply e'
  rw [← h2]
  refine mem_closure_symm (LinearEquiv.toAddEquiv ψ) ?_ hb
  rintro b ⟨g, hg, w', rfl⟩
  show ψ.symm (e3uWact σ e g w' - w') ∈ _
  obtain ⟨s, hs⟩ := exists_lift_U d g
  obtain ⟨a, ha, haπ⟩ := M₀.π_surj (ψ.symm w')
  have key : ψ (M₀.π ((s : G) * a * (s : G)⁻¹)) = e3uWact σ e g w' := by
    rw [d.equivariant s a ha, hs, haπ, ψ.apply_symm_apply]
  have hsym : ψ.symm (e3uWact σ e g w') = M₀.π ((s : G) * a * (s : G)⁻¹) := by
    rw [← key, ψ.symm_apply_apply]
  refine ⟨(s : G), ⟨s.2, g, hg, hs⟩, a, ha, ?_⟩
  rw [map_sub, hsym, haπ]

theorem covC_transport (hc : Ctx M Q Z B)
    (d : EUniData M Q Z B M₀ ψ φ (e3uGam σ e) (e3uP0 σ e) (e3uU0 σ e))
    (hxL : x ∈ Lgen M (LB M Q B)) (Tx : XAct M₀ x) {t : SUid σ 6}
    (hφ : φ ⟨x, hxL⟩ = e3uWact σ e t)
    (hC : ∀ c ∈ Cw σ t, ∃ r ∈ Rw σ t, c - r ∈
      AddSubgroup.closure {v | ∃ g ∈ Gcent σ t, ∃ c' ∈ Cw σ t, v = Wact σ g c' - c'}) :
    ∀ c ∈ Cs Tx, c ∈ (Rs Tx).toAddSubgroup ⊔ AddSubgroup.closure
      {f | ∃ u ∈ {u : G | ∃ hu : u ∈ Lgen M (LB M Q B), ∃ g ∈ Gcent σ t,
        φ ⟨u, hu⟩ = e3uWact σ e g}, ∃ w ∈ Q, M₀.π w ∈ Cs Tx ∧
          f = M₀.π (u * w * u⁻¹) - M₀.π w} := by
  intro c hcCs
  have hcw : (show Wform σ from ψ c) ∈ Cw σ t := (mem_Cs_iff_U d hxL Tx hφ).mp hcCs
  obtain ⟨r, hr, hb⟩ := hC _ hcw
  have hr' : ψ.symm (show E3UWspace σ e from r) ∈ Rs Tx := by
    rw [mem_Rs_iff_U d hxL Tx hφ, LinearEquiv.apply_symm_apply]
    exact hr
  have hS : ∀ b ∈ {v : E3UWspace σ e | ∃ g ∈ Gcent σ t, ∃ c' ∈ Cw σ t, v = Wact σ g c' - c'},
      ψ.toAddEquiv.symm b ∈ {f : M₀.E | ∃ u ∈ {u : G | ∃ hu : u ∈ Lgen M (LB M Q B),
        ∃ g ∈ Gcent σ t, φ ⟨u, hu⟩ = e3uWact σ e g}, ∃ w ∈ Q, M₀.π w ∈ Cs Tx ∧
          f = M₀.π (u * w * u⁻¹) - M₀.π w} := by
    rintro b ⟨g, hg, c', hc', rfl⟩
    obtain ⟨s, hs⟩ := exists_lift_U d g
    obtain ⟨a, ha, hpa⟩ := M₀.π_surj (ψ.symm (show E3UWspace σ e from c'))
    have hψa : ψ (M₀.π a) = (show E3UWspace σ e from c') := by
      rw [hpa, LinearEquiv.apply_symm_apply]
    have hacs : M₀.π a ∈ Cs Tx := by
      rw [mem_Cs_iff_U d hxL Tx hφ, hψa]
      exact hc'
    refine ⟨(s : G), ⟨s.2, g, hg, hs⟩, a, ha, hacs, ?_⟩
    refine (LinearEquiv.symm_apply_eq (e := ψ)).mpr ?_
    rw [map_sub, d.equivariant s a ha, hs, hψa]
    rfl
  have hbS : ψ c - (show E3UWspace σ e from r) ∈ AddSubgroup.closure
      {v : E3UWspace σ e | ∃ g ∈ Gcent σ t, ∃ c' ∈ Cw σ t, v = Wact σ g c' - c'} := hb
  have hz := mem_closure_symm ψ.toAddEquiv hS hbS
  have h2 : ψ.toAddEquiv.symm (ψ c - (show E3UWspace σ e from r)) =
      c - ψ.symm (show E3UWspace σ e from r) := by
    show ψ.symm (ψ c - _) = _
    rw [map_sub, LinearEquiv.symm_apply_apply]
  rw [AddSubgroup.mem_sup]
  exact ⟨ψ.symm (show E3UWspace σ e from r), hr',
    c - ψ.symm (show E3UWspace σ e from r), h2 ▸ hz, by abel⟩

theorem P3_transport (hc : Ctx M Q Z B)
    (d : EUniData M Q Z B M₀ ψ φ (e3uGam σ e) (e3uP0 σ e) (e3uU0 σ e))
    (hxL : x ∈ Lgen M (LB M Q B)) (Tx : XAct M₀ x) {t : SUid σ 6}
    (hφ : φ ⟨x, hxL⟩ = e3uWact σ e t) (U : Set (SUid σ 6))
    (hUc : ∀ u ∈ U, u ∈ Gcent σ t)
    (hUC : ∀ u ∈ U, ∀ c ∈ Cw σ t, Wact σ u c - c ∈ Rw σ t)
    (hUfix : ∀ c ∈ Cw σ t, (∀ u ∈ U, Wact σ u c = c) → c ∈ Rw σ t) :
    (∀ u ∈ {u : G | ∃ hu : u ∈ Lgen M (LB M Q B), ∃ g ∈ U, φ ⟨u, hu⟩ = e3uWact σ e g},
      u ∈ H0 M Z) ∧
    (∀ u ∈ {u : G | ∃ hu : u ∈ Lgen M (LB M Q B), ∃ g ∈ U, φ ⟨u, hu⟩ = e3uWact σ e g},
      ⁅u, x⁆ ∈ Q) ∧
    (∀ u ∈ {u : G | ∃ hu : u ∈ Lgen M (LB M Q B), ∃ g ∈ U, φ ⟨u, hu⟩ = e3uWact σ e g},
      ∀ w ∈ Q, M₀.π w ∈ Cs Tx → M₀.π (u * w * u⁻¹) - M₀.π w ∈ Rs Tx) ∧
    (∀ e' ∈ Cs Tx, (∀ u ∈ {u : G | ∃ hu : u ∈ Lgen M (LB M Q B), ∃ g ∈ U,
        φ ⟨u, hu⟩ = e3uWact σ e g}, ∀ w ∈ Q, M₀.π w = e' → M₀.π (u * w * u⁻¹) = e') →
      e' ∈ Rs Tx) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro u ⟨hu, -⟩
    exact Lgen_le_H0 hc hu
  · rintro u ⟨hu, g, hg, hφu⟩
    exact comm_mem_Q_of_lift_U d hxL hu hφ hφu (hUc g hg)
  · rintro u ⟨hu, g, hg, hφu⟩ w hw hwC
    have hψ : ψ (M₀.π (u * w * u⁻¹)) = e3uWact σ e g (ψ (M₀.π w)) := by
      have := d.equivariant ⟨u, hu⟩ w hw
      rw [hφu] at this
      exact this
    have hsub : (show Wform σ from ψ (M₀.π (u * w * u⁻¹) - M₀.π w)) =
        Wact σ g (show Wform σ from ψ (M₀.π w)) - (show Wform σ from ψ (M₀.π w)) := by
      rw [map_sub, hψ]
      rfl
    rw [mem_Rs_iff_U d hxL Tx hφ, hsub]
    exact hUC g hg _ ((mem_Cs_iff_U d hxL Tx hφ).mp hwC)
  · intro e' he' hfix
    rw [mem_Rs_iff_U d hxL Tx hφ]
    refine hUfix (show Wform σ from ψ e') ((mem_Cs_iff_U d hxL Tx hφ).mp he')
      (fun u₀ hu₀ => ?_)
    obtain ⟨su, hsu⟩ := exists_lift_U d u₀
    obtain ⟨w, hw, hwe⟩ := M₀.π_surj e'
    have h1 := hfix (su : G) ⟨su.2, u₀, hu₀, hsu⟩ w hw hwe
    have h2 := d.equivariant su w hw
    rw [hsu, hwe, h1] at h2
    exact h2.symm

theorem P2_transport (hc : Ctx M Q Z B)
    (hRoot : ∀ ξ ∈ RootPt σ, ∃ (g : SUid σ 6) (c : F), c ≠ 0 ∧ σ c = c ∧
      ξ = c • rho F (g : GL (Fin 6) F) (pt0 F))
    (d : EUniData M Q Z B M₀ ψ φ (e3uGam σ e) (e3uP0 σ e) (e3uU0 σ e))
    (hxL : x ∈ Lgen M (LB M Q B)) (Tx : XAct M₀ x) {t : SUid σ 6}
    (hφ : φ ⟨x, hxL⟩ = e3uWact σ e t)
    (hP2 : ∀ S : AddSubgroup (Wform σ), S ≠ ⊥ → (∀ s ∈ S, s ∈ Rw σ t) →
      (∀ a ∈ Gcent σ t, ∀ b ∈ Gcent σ t, ∀ s ∈ S, Wact σ ⁅a, b⁆ s ∈ S) →
      ∃ p ∈ S, p ≠ 0 ∧ (p : Cube F) ∈ RootPt σ) :
    ∀ S : AddSubgroup M₀.E, S ≠ ⊥ → (∀ s ∈ S, s ∈ Rs Tx) →
      (∀ a b : G, a ∈ H0 M Z → b ∈ H0 M Z → ⁅a, x⁆ ∈ Q → ⁅b, x⁆ ∈ Q → ∀ y ∈ Q,
        M₀.π y ∈ S → M₀.π (⁅a, b⁆ * y * ⁅a, b⁆⁻¹) ∈ S) →
      ∃ e' ∈ S, e' ≠ 0 ∧ RootPt M₀ e' := by
  intro S hS hSR hSstab
  let f : M₀.E →+ Wform σ := ψ.toLinearMap.toAddMonoidHom
  have hS' : (S.map f : AddSubgroup (Wform σ)) ≠ ⊥ := by
    intro h
    apply hS
    rw [eq_bot_iff]
    intro v hv
    have h1 : f v ∈ (S.map f : AddSubgroup (Wform σ)) := ⟨v, hv, rfl⟩
    rw [h, AddSubgroup.mem_bot] at h1
    have h2 : ψ v = 0 := h1
    have h3 : v = 0 := ψ.injective (h2.trans (map_zero ψ).symm)
    simp [h3]
  have hR' : ∀ s ∈ (S.map f : AddSubgroup (Wform σ)), s ∈ Rw σ t := by
    rintro _ ⟨v, hv, rfl⟩
    exact (mem_Rs_iff_U d hxL Tx hφ).mp (hSR v hv)
  have hstab : ∀ a ∈ Gcent σ t, ∀ b ∈ Gcent σ t, ∀ s ∈ (S.map f : AddSubgroup (Wform σ)),
      Wact σ ⁅a, b⁆ s ∈ (S.map f : AddSubgroup (Wform σ)) := by
    intro a ha b hb s hs
    obtain ⟨v, hv, rfl⟩ := hs
    obtain ⟨sa, hsa⟩ := exists_lift_U d a
    obtain ⟨sb, hsb⟩ := exists_lift_U d b
    have hax : ⁅(sa : G), x⁆ ∈ Q :=
      comm_mem_Q_of_lift_U d hxL sa.2 hφ hsa (show a * t = t * a from ha)
    have hbx : ⁅(sb : G), x⁆ ∈ Q :=
      comm_mem_Q_of_lift_U d hxL sb.2 hφ hsb (show b * t = t * b from hb)
    obtain ⟨y, hy, rfl⟩ := M₀.π_surj v
    have key := hSstab (sa : G) (sb : G) (Lgen_le_H0 hc sa.2) (Lgen_le_H0 hc sb.2) hax hbx y hy hv
    refine ⟨M₀.π (⁅(sa : G), (sb : G)⁆ * y * ⁅(sa : G), (sb : G)⁆⁻¹), key, ?_⟩
    have h1 := d.equivariant ⁅sa, sb⁆ y hy
    have h2 : φ ⁅sa, sb⁆ = e3uWact σ e ⁅a, b⁆ := by
      simp only [commutatorElement_def, map_mul, map_inv, hsa, hsb]
    have h3 : ((⁅sa, sb⁆ : Lgen M (LB M Q B)) : G) = ⁅(sa : G), (sb : G)⁆ := by
      simp [commutatorElement_def]
    rw [h2, h3] at h1
    exact h1
  obtain ⟨p, hpS, hp0, hpP⟩ := hP2 (S.map f : AddSubgroup (Wform σ)) hS' hR' hstab
  obtain ⟨v, hv, rfl⟩ := hpS
  refine ⟨v, hv, fun h => hp0 (by rw [h]; exact map_zero f), ?_⟩
  have hw : e3uVal (ψ v) ∈ RootPt σ := hpP
  have hr := rootPt_of_RootPt_U hRoot d hc.hyp hw
  rwa [LinearEquiv.symm_apply_apply] at hr

theorem e3u28_of_involModel12 (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (hRoot : ∀ ξ ∈ RootPt σ, ∃ (g : SUid σ 6) (c : F), c ≠ 0 ∧ σ c = c ∧
      ξ = c • rho F (g : GL (Fin 6) F) (pt0 F))
    (d : EUniData M Q Z B M₀ ψ φ (e3uGam σ e) (e3uP0 σ e) (e3uU0 σ e))
    (hs : Sit M Q Z X x) (hxL : x ∈ Lgen M (LB M Q B)) {t : SUid σ 6}
    (hφ : φ ⟨x, hxL⟩ = e3uWact σ e t) (hM : UInvolModel12 σ t) (hne : Q ⊓ QB X ≠ ⊥) :
    ∃ v : G, IsConj x v ∧ v ∈ Q ∧ v ∈ QB X := by
  classical
  have h12 := smith_1_12 hs
  obtain ⟨Tx⟩ := exists_xact hD hs.memM (hs.x_cent h12)
  obtain ⟨U, hUc, hUC, hUfix⟩ := hM.P3
  obtain ⟨hU0, hUx, hUCG, hUfixG⟩ := P3_transport hc d hxL Tx hφ U hUc hUC hUfix
  have hV0 : ∀ u ∈ {u : G | ∃ hu : u ∈ Lgen M (LB M Q B), ∃ g ∈ Gcent σ t,
      φ ⟨u, hu⟩ = e3uWact σ e g}, u ∈ H0 M Z := by
    rintro u ⟨hu, -⟩
    exact Lgen_le_H0 hc hu
  have hVx : ∀ u ∈ {u : G | ∃ hu : u ∈ Lgen M (LB M Q B), ∃ g ∈ Gcent σ t,
      φ ⟨u, hu⟩ = e3uWact σ e g}, ⁅u, x⁆ ∈ Q := by
    rintro u ⟨hu, g, hg, hφu⟩
    exact comm_mem_Q_of_lift_U d hxL hu hφ hφu hg
  have hQf : ∀ r ∈ Rs Tx, M₀.Qf r = 0 :=
    qf_zero_of_coinv hD hs Tx _ hV0 hVx (covW_transport hc d hM.covW)
  exact e3l28_root_of_coinv hs hD Tx hQf _ hV0 hVx (covC_transport hc d hxL Tx hφ hM.covC)
    _ hU0 hUx hUCG hUfixG (P2_transport hc hRoot d hxL Tx hφ hM.P2) hne

theorem e3u28_of_involModel3 (hD : GlobalModelData M Q Z γ M₀)
    (hRoot : ∀ ξ ∈ RootPt σ, ∃ (g : SUid σ 6) (c : F), c ≠ 0 ∧ σ c = c ∧
      ξ = c • rho F (g : GL (Fin 6) F) (pt0 F))
    (d : EUniData M Q Z B M₀ ψ φ (e3uGam σ e) (e3uP0 σ e) (e3uU0 σ e))
    (hform : ∃ lam : F, lam ≠ 0 ∧ ∀ e' f' : M₀.E,
      ((e (M₀.B e' f') : Fσ σ) : F) = lam * beta F (e3uVal (ψ e')) (e3uVal (ψ f')))
    (hs : Sit M Q Z X x) (hxL : x ∈ Lgen M (LB M Q B)) {t : SUid σ 6}
    (hφ : φ ⟨x, hxL⟩ = e3uWact σ e t) (hM : UInvolModel3 σ t) (hne : Q ⊓ QB X ≠ ⊥) :
    ∃ v : G, IsConj x v ∧ v ∈ Q ∧ v ∈ QB X := by
  classical
  have H : StrothHyp M Q Z := hs.hyp
  have h12 := smith_1_12 hs
  obtain ⟨Tx⟩ := exists_xact hD hs.memM (hs.x_cent h12)
  obtain ⟨lam, hlam, hB⟩ := hform
  refine e3l28_root_of_k3 hs hD Tx ?_ ?_ hne
  · intro e' he'
    rw [mem_Rs_iff_U d hxL Tx hφ]
    exact hM.CR _ ((mem_Cs_iff_U d hxL Tx hφ).mp he')
  · obtain ⟨p₁, p₂, h1, h2, hR, hβ⟩ := hM.beta_ne
    refine ⟨ψ.symm (show E3UWspace σ e from p₁) + ψ.symm (show E3UWspace σ e from p₂), ?_, ?_⟩
    · rw [mem_Rs_iff_U d hxL Tx hφ, map_add, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply]
      exact hR
    · have hr1 : RootPt M₀ (ψ.symm (show E3UWspace σ e from p₁)) :=
        rootPt_of_RootPt_U hRoot d H h1
      have hr2 : RootPt M₀ (ψ.symm (show E3UWspace σ e from p₂)) :=
        rootPt_of_RootPt_U hRoot d H h2
      rw [M₀.Qf_add, Qf_RootPt hD hr1, Qf_RootPt hD hr2, zero_add, zero_add]
      intro hB0
      have h := hB (ψ.symm (show E3UWspace σ e from p₁)) (ψ.symm (show E3UWspace σ e from p₂))
      rw [hB0, map_zero] at h
      have e1 : ψ (ψ.symm (show E3UWspace σ e from p₁)) = (show E3UWspace σ e from p₁) :=
        ψ.apply_symm_apply _
      have e2 : ψ (ψ.symm (show E3UWspace σ e from p₂)) = (show E3UWspace σ e from p₂) :=
        ψ.apply_symm_apply _
      rw [e1, e2] at h
      exact mul_ne_zero hlam hβ (by simpa [e3uVal] using h.symm)

end CFSG.RankThree.GF2n.Smith81.E3UBridge
