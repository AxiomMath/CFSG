module

public import CFSG.RankThree.GF2n.Stroth80.Sec41ii
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatField
public import CFSG.RankThree.GF2n.Stroth80.Sec5SL
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatPsi
public import CFSG.RankThree.GF2n.Stroth80.Sec41iiTensorGlue
public import CFSG.RankThree.GF2n.Stroth80.Sec41iiTensorNat

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

section Transport

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

@[expose] def Ctx.VtSub (hc : Ctx M Q Z B) {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hM : GlobalModelData M Q Z γ M₀) (t : G) :
    Submodule K M₀.E :=
  imgSub M₀ (Vt M (LB M Q B) B Z t) (fun c _ he => hc.smul_mem_img_Vt hM t c he)

theorem Ctx.mem_VtSub (hc : Ctx M Q Z B) {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hM : GlobalModelData M Q Z γ M₀) (t : G) {e : M₀.E} :
    e ∈ hc.VtSub hM t ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t) := Iff.rfl

theorem Ctx.act_mem_VtSub (hc : Ctx M Q Z B) {n : ℕ} {K : Type} [Field K] [Finite K]
    {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)} {b : M₀.E}
    (hS : IsTensorSetup hc n M₀ ρ b) {t : G} (ht : t ∈ LB M Q B) :
    ∀ x ∈ bar M Q (Rt M (LB M Q B) t), ∀ w ∈ hc.VtSub hS.model t,
      (ρ x).toAdd w ∈ hc.VtSub hS.model t := by
  intro x hx w hw
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  have hyR : (y : G) ∈ Rt M (LB M Q B) t := Subgroup.mem_subgroupOf.mp hy
  obtain ⟨v, hvV, hvQ, hwv⟩ := M₀.mem_img.mp ((hc.mem_VtSub hS.model t).mp hw)
  subst hwv
  have hvN : (y : G) * v * (y : G)⁻¹ ∈ Vt M (LB M Q B) B Z t :=
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hyR) v).mp hvV
  have hvNQ : (y : G) * v * (y : G)⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 y.2) v).mp hvQ
  have heq : (ρ (QuotientGroup.mk y)).toAdd (M₀.π v) = M₀.π ((y : G) * v * (y : G)⁻¹) :=
    (hS.conj y v hvQ).symm
  refine (hc.mem_VtSub hS.model t).mpr ?_
  show (ρ (QuotientGroup.mk y)).toAdd (M₀.π v) ∈ M₀.img (Vt M (LB M Q B) B Z t)
  rw [heq]
  exact M₀.pi_mem_img hvN hvNQ

theorem Ctx.irred_VtSub (hc : Ctx M Q Z B) {n : ℕ} {K : Type} [Field K] [Finite K]
    {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)} {b : M₀.E}
    (hS : IsTensorSetup hc n M₀ ρ b)
    (h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G)) {t : G} (ht : t ∈ LB M Q B) :
    ∀ S : Submodule K M₀.E, S ≤ hc.VtSub hS.model t →
      (∀ x ∈ bar M Q (Rt M (LB M Q B) t), ∀ v ∈ S, (ρ x).toAdd v ∈ S) →
        S = ⊥ ∨ S = hc.VtSub hS.model t := by
  intro S hSle hSinv
  by_cases hS0 : S = ⊥
  · exact Or.inl hS0
  refine Or.inr (le_antisymm hSle ?_)
  obtain ⟨jj, -, hZ2, -⟩ := hc.hyp.cp
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hS.card.trans hZ2)
  have hstep : ∀ l ∈ Rt M (LB M Q B) t, ∀ T : M₀.E ≃ₗ[K] M₀.E,
      (∀ x ∈ Q, M₀.π (l * x * l⁻¹) = T (M₀.π x)) → (∀ e, M₀.Qf (T e) = M₀.Qf e) →
        ∀ w ∈ S, T w ∈ S := by
    intro l hl T hT _ w hw
    have hlM : l ∈ M := hc.Rt_le_M t hl
    have hmem : (QuotientGroup.mk (⟨l, hlM⟩ : ↥M) : Mbar M Q) ∈
        bar M Q (Rt M (LB M Q B) t) :=
      Subgroup.mem_map.mpr ⟨⟨l, hlM⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
    have hfun : ∀ e, T e = (ρ (QuotientGroup.mk (⟨l, hlM⟩ : ↥M))).toAdd e := by
      intro e
      obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
      exact (hT x hxQ).symm.trans (hS.conj ⟨l, hlM⟩ x hxQ)
    rw [hfun w]
    exact hSinv _ hmem w hw
  intro v hv
  exact hc.img_Vt_le_of_invariant h35 hS.model t S hS0 hstep v ((hc.mem_VtSub hS.model t).mp hv)

theorem Ctx.act_CN (hc : Ctx M Q Z B) {n : ℕ} {K : Type} [Field K] [Finite K]
    {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)} {b : M₀.E}
    (hS : IsTensorSetup hc n M₀ ρ b) {t : G} (ht : t ∈ LB M Q B) :
    ∀ ν ∈ bar M Q (hc.CN t), ∀ w ∈ hc.VtSub hS.model t, (ρ ν).toAdd w = w := by
  intro ν hν w hw
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hν
  have hyC : (y : G) ∈ hc.CN t := Subgroup.mem_subgroupOf.mp hy
  have hcomm : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅(y : G), v⁆ ∈ Z := (Ctx.mem_CN.mp hyC).2
  obtain ⟨v, hvV, hvQ, hwv⟩ := M₀.mem_img.mp ((hc.mem_VtSub hS.model t).mp hw)
  subst hwv
  have hcZ : ⁅(y : G), v⁆ ∈ Z := hcomm v hvV
  have hcQ : ⁅(y : G), v⁆ ∈ Q := hc.Z_le_Q hcZ
  have hid : (y : G) * v * (y : G)⁻¹ = ⁅(y : G), v⁆ * v := by
    rw [commutatorElement_def]; group
  have hzero : M₀.π ⁅(y : G), v⁆ = 0 := (M₀.π_ker _ hcQ).mpr hcZ
  show (ρ (QuotientGroup.mk y)).toAdd (M₀.π v) = M₀.π v
  rw [← hS.conj y v hvQ, hid, M₀.π_mul _ hcQ v hvQ, hzero, zero_add]


private theorem exists_bar_hom_compat (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {ι : Type}
    [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (φ : ↥(Rt M (LB M Q B) t) →* GL ι K)
    (hφk : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t)) :
    ∃ π : ↥(bar M Q (Rt M (LB M Q B) t)) →* GL ι K, π.range = φ.range ∧
      (∀ x : ↥(bar M Q (Rt M (LB M Q B) t)), π x = 1 ↔ (x : Mbar M Q) ∈ bar M Q (hc.CN t)) ∧
      ∀ (r : ↥(Rt M (LB M Q B) t)) (x : ↥(bar M Q (Rt M (LB M Q B) t))),
        (x : Mbar M Q) = QuotientGroup.mk' (Q.subgroupOf M) ⟨(r : G), hc.Rt_le_M t r.2⟩ →
          π x = φ r := by
  classical
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hQN : Q ≤ hc.CN t := fun x hx =>
    Ctx.mem_CN.mpr ⟨hc.Q_le_Rt ht hx, fun v hv =>
      hc.hyp.toHyp79.comm_mem_V hx (hc.Vt_le_Q t hv)⟩
  let ψ : ↥(Rt M (LB M Q B) t) →* Mbar M Q :=
    (QuotientGroup.mk' (Q.subgroupOf M)).comp (Subgroup.inclusion hRM)
  have hψ : ∀ r : ↥(Rt M (LB M Q B) t),
      ψ r = QuotientGroup.mk' (Q.subgroupOf M) ⟨(r : G), hRM r.2⟩ := fun r => rfl
  have hmem : ∀ r : ↥(Rt M (LB M Q B) t), ψ r ∈ bar M Q (Rt M (LB M Q B) t) := fun r =>
    Subgroup.mem_map.mpr ⟨⟨(r : G), hRM r.2⟩, Subgroup.mem_subgroupOf.mpr r.2, rfl⟩
  let f : ↥(Rt M (LB M Q B) t) →* ↥(bar M Q (Rt M (LB M Q B) t)) := ψ.codRestrict _ hmem
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨r, hr, hry⟩ := Subgroup.mem_map.mp y.2
    have hrR : (r : G) ∈ Rt M (LB M Q B) t := Subgroup.mem_subgroupOf.mp hr
    refine ⟨⟨(r : G), hrR⟩, Subtype.ext ?_⟩
    show ψ ⟨(r : G), hrR⟩ = (y : Mbar M Q)
    rw [hψ]
    have : (⟨((⟨(r : G), hrR⟩ : ↥(Rt M (LB M Q B) t)) : G),
        hRM (⟨(r : G), hrR⟩ : ↥(Rt M (LB M Q B) t)).2⟩ : ↥M) = r := Subtype.ext rfl
    rw [this, hry]
  have hker : f.ker ≤ φ.ker := by
    intro r hr
    have h1 : ψ r = 1 := congrArg Subtype.val hr
    rw [hψ] at h1
    have h2 : (⟨(r : G), hRM r.2⟩ : ↥M) ∈ Q.subgroupOf M :=
      (QuotientGroup.eq_one_iff _).mp h1
    rw [hφk]
    exact Subgroup.mem_subgroupOf.mpr (hQN (Subgroup.mem_subgroupOf.mp h2))
  let π₀ : ↥(bar M Q (Rt M (LB M Q B) t)) →* GL ι K :=
    (MonoidHom.liftOfSurjective f hfsurj) ⟨φ, hker⟩
  have hπ₀ : ∀ r : ↥(Rt M (LB M Q B) t), π₀ (f r) = φ r := fun r =>
    MonoidHom.liftOfRightInverse_comp_apply f (Function.surjInv hfsurj)
      (Function.rightInverse_surjInv hfsurj) ⟨φ, hker⟩ r
  refine ⟨π₀, ?_, ?_, ?_⟩
  · ext g
    rw [MonoidHom.mem_range, MonoidHom.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨r, rfl⟩ := hfsurj x
      exact ⟨r, (hπ₀ r).symm⟩
    · rintro ⟨r, rfl⟩
      exact ⟨f r, hπ₀ r⟩
  · intro x
    obtain ⟨r, rfl⟩ := hfsurj x
    rw [hπ₀]
    constructor
    · intro h
      have h1 : r ∈ φ.ker := h
      rw [hφk] at h1
      have h2 : (r : G) ∈ hc.CN t := Subgroup.mem_subgroupOf.mp h1
      exact ⟨⟨(r : G), hRM r.2⟩, Subgroup.mem_subgroupOf.mpr h2, rfl⟩
    · intro h
      obtain ⟨y, hy, hyr⟩ := h
      have hyCN : (y : G) ∈ hc.CN t := Subgroup.mem_subgroupOf.mp hy
      have h1 : ψ r = QuotientGroup.mk' (Q.subgroupOf M) y := by
        have : ψ r = (f r : Mbar M Q) := rfl
        rw [this, ← hyr]
      rw [hψ] at h1
      have h2 := QuotientGroup.eq.mp h1
      have h3 : ((r : G))⁻¹ * (y : G) ∈ Q := Subgroup.mem_subgroupOf.mp h2
      have h4 : (r : G) ∈ hc.CN t := by
        have e : (r : G) = (y : G) * ((r : G)⁻¹ * (y : G))⁻¹ := by group
        rw [e]
        exact (hc.CN t).mul_mem hyCN ((hc.CN t).inv_mem (hQN h3))
      have h5 : r ∈ φ.ker := by
        rw [hφk]
        exact Subgroup.mem_subgroupOf.mpr h4
      exact h5
  · intro r x hx
    have hxf : x = f r := Subtype.ext (hx.trans (hψ r).symm)
    subst hxf
    exact hπ₀ r

theorem Ctx.natural_transport (hc : Ctx M Q Z B) {n : ℕ} {K : Type} [Field K] [Finite K]
    {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)} {b : M₀.E}
    (hS : IsTensorSetup hc n M₀ ρ b) {t : G} (ht : t ∈ LB M Q B)
    {K' : Type} [Field K'] [Finite K'] {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {Xcl : Subgroup (GL ι K')} (hK' : Nat.card K' = Nat.card Z)
    (hcomm : AddCommutantScalar Xcl)
    (hnat : NaturalRep K' Xcl (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t)) :
    ∃ (θ : K ≃+* K') (Ψ : ↥(hc.VtSub hS.model t) ≃+ (ι → K'))
      (π : ↥(bar M Q (Rt M (LB M Q B) t)) →* GL ι K'),
      π.range = Xcl ∧
      (∀ x : ↥(bar M Q (Rt M (LB M Q B) t)), π x = 1 ↔ (x : Mbar M Q) ∈ bar M Q (hc.CN t)) ∧
      (∀ (c : K) (w : ↥(hc.VtSub hS.model t)), Ψ (c • w) = θ c • Ψ w) ∧
      ∀ (x : ↥(bar M Q (Rt M (LB M Q B) t))) (w : ↥(hc.VtSub hS.model t)),
        Ψ ⟨(ρ (x : Mbar M Q)).toAdd w, hc.act_mem_VtSub hS ht x x.2 w w.2⟩ =
          (π x : Matrix ι ι K') *ᵥ Ψ w := by
  obtain ⟨φ, hφr, hφk, hSA⟩ := hnat
  obtain ⟨hRV, hZV, ψ, hψ⟩ := hSA
  haveI := hZV
  have hSmul : ∀ (c : K) (e : M₀.E), e ∈ M₀.img (Vt M (LB M Q B) B Z t) →
      c • e ∈ M₀.img (Vt M (LB M Q B) B Z t) :=
    fun c e he => hc.smul_mem_img_Vt hS.model t c he
  have hlin : ∀ r ∈ Rt M (LB M Q B) t, ∃ T : M₀.E →ₗ[K] M₀.E,
      ∀ x ∈ Q, M₀.π (r * x * r⁻¹) = T (M₀.π x) := by
    intro r hr
    have hrM : r ∈ M := hc.Rt_le_M t hr
    let g : Mbar M Q := QuotientGroup.mk ⟨r, hrM⟩
    have hg : g ∈ bar M Q (H0 M Z) :=
      Subgroup.mem_map.mpr ⟨⟨r, hrM⟩, Subgroup.mem_subgroupOf.mpr (hc.Rt_le_H0 t hr), rfl⟩
    refine ⟨{ toFun := fun v => (ρ g).toAdd v
              map_add' := fun u v => map_add (ρ g).toAdd u v
              map_smul' := fun c v => hS.lin g hg c v }, fun x hx => ?_⟩
    exact hS.conj ⟨r, hrM⟩ x hx
  have hcard : Nat.card K = Nat.card K' := hS.card.trans hK'.symm
  obtain ⟨θ, hθ⟩ := exists_ringEquiv_natural hcard M₀ (hc.Vt_le_Q t) hcomm hSmul hlin φ hφr
    hRV ψ hψ
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ↥(hc.VtSub hS.model t) ≃+ (ι → K'),
      ∀ (v : ↥(Vt M (LB M Q B) B Z t)) (h : M₀.π v ∈ hc.VtSub hS.model t),
        Ψ ⟨M₀.π v, h⟩ = Multiplicative.toAdd (ψ (QuotientGroup.mk v)) :=
    exists_addEquiv_imgSub M₀ (hc.Vt_le_Q t) hSmul ψ
  obtain ⟨π, hπr, hπk, hπc⟩ := exists_bar_hom_compat hc ht φ hφk
  refine ⟨θ, Ψ, π, hπr.trans hφr, hπk, ?_, ?_⟩
  · intro c w
    have hw : (w : M₀.E) ∈ M₀.img (Vt M (LB M Q B) B Z t) :=
      (hc.mem_VtSub hS.model t).mp w.2
    have hcw : c • (w : M₀.E) ∈ M₀.img (Vt M (LB M Q B) B Z t) := hSmul c _ hw
    obtain ⟨v, hvV, hvQ, hv⟩ := hw
    obtain ⟨v', hv'V, hv'Q, hv'⟩ := hcw
    have e1 : Ψ (c • w) =
        Multiplicative.toAdd (ψ (QuotientGroup.mk (⟨v', hv'V⟩ : ↥(Vt M (LB M Q B) B Z t)))) := by
      have hce : c • w = ⟨M₀.π v', (hc.mem_VtSub hS.model t).mpr (M₀.pi_mem_img hv'V hv'Q)⟩ :=
        Subtype.ext hv'.symm
      rw [hce]
      exact hΨ ⟨v', hv'V⟩ _
    have e2 : Ψ w =
        Multiplicative.toAdd (ψ (QuotientGroup.mk (⟨v, hvV⟩ : ↥(Vt M (LB M Q B) B Z t)))) := by
      have hwe : w = ⟨M₀.π v, (hc.mem_VtSub hS.model t).mpr (M₀.pi_mem_img hvV hvQ)⟩ :=
        Subtype.ext hv.symm
      rw [hwe]
      exact hΨ ⟨v, hvV⟩ _
    have hcu : M₀.π v' = c • M₀.π v := by rw [hv', hv]
    rw [e1, e2]
    exact hθ c ⟨v, hvV⟩ ⟨v', hv'V⟩ hcu
  · intro x w
    obtain ⟨r, hr, hrx⟩ := Subgroup.mem_map.mp x.2
    have hrR : (r : G) ∈ Rt M (LB M Q B) t := Subgroup.mem_subgroupOf.mp hr
    have hw : (w : M₀.E) ∈ M₀.img (Vt M (LB M Q B) B Z t) :=
      (hc.mem_VtSub hS.model t).mp w.2
    obtain ⟨v, hvV, hvQ, hv⟩ := hw
    have hrV : (r : G) * v * (r : G)⁻¹ ∈ Vt M (LB M Q B) B Z t :=
      (Subgroup.mem_normalizer_iff.mp (hRV hrR) v).mp hvV
    have hrQ : (r : G) * v * (r : G)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 r.2) v).mp hvQ
    have hmemV : M₀.π ((r : G) * v * (r : G)⁻¹) ∈ hc.VtSub hS.model t :=
      (hc.mem_VtSub hS.model t).mpr (M₀.pi_mem_img hrV hrQ)
    have hact : (ρ (x : Mbar M Q)).toAdd (w : M₀.E) = M₀.π ((r : G) * v * (r : G)⁻¹) := by
      rw [← hrx, ← hv]
      exact (hS.conj r v hvQ).symm
    have hπx : π x = φ ⟨(r : G), hrR⟩ := hπc ⟨(r : G), hrR⟩ x hrx.symm
    have hψs := hψ ⟨(r : G), hrR⟩ ⟨v, hvV⟩ ⟨(r : G) * v * (r : G)⁻¹, hrV⟩ rfl
    have hLHS : Ψ ⟨(ρ (x : Mbar M Q)).toAdd (w : M₀.E), hc.act_mem_VtSub hS ht x x.2 w w.2⟩ =
        Multiplicative.toAdd (ψ (QuotientGroup.mk
          (⟨(r : G) * v * (r : G)⁻¹, hrV⟩ : ↥(Vt M (LB M Q B) B Z t)))) := by
      have e : (⟨(ρ (x : Mbar M Q)).toAdd (w : M₀.E), hc.act_mem_VtSub hS ht x x.2 w w.2⟩ :
          ↥(hc.VtSub hS.model t)) = ⟨M₀.π ((r : G) * v * (r : G)⁻¹), hmemV⟩ :=
        Subtype.ext hact
      rw [e]
      exact hΨ ⟨(r : G) * v * (r : G)⁻¹, hrV⟩ _
    have hRHS : Ψ w =
        Multiplicative.toAdd (ψ (QuotientGroup.mk (⟨v, hvV⟩ : ↥(Vt M (LB M Q B) B Z t)))) := by
      have e : w = ⟨M₀.π v, (hc.mem_VtSub hS.model t).mpr (M₀.pi_mem_img hvV hvQ)⟩ :=
        Subtype.ext hv.symm
      rw [e]
      exact hΨ ⟨v, hvV⟩ _
    rw [hLHS, hRHS, hπx]
    exact hψs


theorem Ctx.bar_LB_le_normalizer_CN (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) :
    bar M Q (LB M Q B) ≤ Subgroup.normalizer (bar M Q (hc.CN t) : Set (Mbar M Q)) := fun ℓ hℓ =>
  Subgroup.mem_normalizer_fintype fun ν hν =>
    hc.bar_CN_conj_mem ht (hc.bar_LB_le_bar_Rt ht hℓ) hν

theorem act_mul_apply {E : Type*} [AddCommGroup E] {Γ : Type*} [Group Γ]
    (ρ : Γ →* Multiplicative (AddAut E)) (a b : Γ) (v : E) :
    (ρ (a * b)).toAdd v = (ρ a).toAdd ((ρ b).toAdd v) := by
  rw [map_mul]
  rfl

theorem Ctx.sq_inter (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {X : Subgroup (Mbar M Q)}
    (hXN : X ⊓ bar M Q (hc.CN t) = ⊥) :
    ∀ p ∈ X ⊓ (bar M Q (LB M Q B) ⊔ bar M Q (hc.CN t)), p * p = 1 := by
  intro p hp
  obtain ⟨ℓ, hℓ, ν, hν, hp'⟩ :=
    exists_mul_of_mem_sup_of_le_normalizer (hc.bar_LB_le_normalizer_CN ht) hp.2
  have hℓ2 : ℓ * ℓ = 1 := by
    have := hc.isElemAbelian_bar_LB.2 ℓ hℓ
    rwa [pow_two] at this
  have hinv : ℓ⁻¹ = ℓ := inv_eq_of_mul_eq_one_right hℓ2
  have hconj : ℓ * ν * ℓ⁻¹ ∈ bar M Q (hc.CN t) :=
    hc.bar_CN_conj_mem ht (hc.bar_LB_le_bar_Rt ht hℓ) hν
  have hpp : p * p ∈ bar M Q (hc.CN t) := by
    have e : p * p = (ℓ * ν * ℓ⁻¹) * ν := by
      rw [← hp', hinv]
      simp only [mul_assoc]
    rw [e]
    exact (bar M Q (hc.CN t)).mul_mem hconj hν
  have h2 : p * p ∈ X ⊓ bar M Q (hc.CN t) := ⟨X.mul_mem hp.1 hp.1, hpp⟩
  rw [hXN, Subgroup.mem_bot] at h2
  exact h2

theorem Ctx.fix_inter (hc : Ctx M Q Z B) {n : ℕ} {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)} {b : M₀.E}
    (hS : IsTensorSetup hc n M₀ ρ b) {t : G} (ht : t ∈ LB M Q B) {X : Subgroup (Mbar M Q)}
    (hXR : X ≤ bar M Q (Rt M (LB M Q B) t))
    (hsup : bar M Q (Rt M (LB M Q B) t) = bar M Q (hc.CN t) ⊔ X)
    (hCNX : bar M Q (hc.CN t) ≤ Subgroup.normalizer (X : Set (Mbar M Q))) :
    ∀ v ∈ hc.VtSub hS.model t,
      ((∀ p ∈ X ⊓ (bar M Q (LB M Q B) ⊔ bar M Q (hc.CN t)), (ρ p).toAdd v = v) ↔
        v ∈ Submodule.span K {b}) := by
  intro v hv
  rw [← hS.fix v]
  constructor
  · intro h ℓ hℓ
    have hℓR := hc.bar_LB_le_bar_Rt ht hℓ
    rw [hsup] at hℓR
    obtain ⟨ν, hν, x, hx, hνx⟩ := exists_mul_of_mem_sup_of_le_normalizer hCNX hℓR
    have hxP : x ∈ X ⊓ (bar M Q (LB M Q B) ⊔ bar M Q (hc.CN t)) := by
      refine ⟨hx, ?_⟩
      have e : x = ν⁻¹ * ℓ := by rw [← hνx]; group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_right hν))
        (Subgroup.mem_sup_left hℓ)
    have hxv : (ρ x).toAdd v = v := h x hxP
    rw [← hνx, act_mul_apply, hxv]
    exact hc.act_CN hS ht ν hν v hv
  · intro h p hp
    obtain ⟨ℓ, hℓ, ν, hν, hℓν⟩ :=
      exists_mul_of_mem_sup_of_le_normalizer (hc.bar_LB_le_normalizer_CN ht) hp.2
    rw [← hℓν, act_mul_apply, hc.act_CN hS ht ν hν v hv]
    exact h ℓ hℓ


theorem Ctx.norm_inter (hc : Ctx M Q Z B) {n : ℕ} {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)} {b : M₀.E}
    (hS : IsTensorSetup hc n M₀ ρ b) {t : G} (ht : t ∈ LB M Q B) {X : Subgroup (Mbar M Q)}
    (hXR : X ≤ bar M Q (Rt M (LB M Q B) t))
    (hXn : ∀ r ∈ bar M Q (Rt M (LB M Q B) t), ∀ x ∈ X, r * x * r⁻¹ ∈ X) :
    ∀ x ∈ X, (∃ c : K, (ρ x).toAdd b = c • b) →
      ∀ p ∈ X ⊓ (bar M Q (LB M Q B) ⊔ bar M Q (hc.CN t)),
        x * p * x⁻¹ ∈ X ⊓ (bar M Q (LB M Q B) ⊔ bar M Q (hc.CN t)) := by
  intro x hx hcx p hp
  have hxΛ := hS.stab x hcx
  refine ⟨hXn x (hXR hx) p hp.1, ?_⟩
  obtain ⟨ℓ, hℓ, ν, hν, hp'⟩ :=
    exists_mul_of_mem_sup_of_le_normalizer (hc.bar_LB_le_normalizer_CN ht) hp.2
  have e : x * p * x⁻¹ = (x * ℓ * x⁻¹) * (x * ν * x⁻¹) := by
    rw [← hp']
    group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hxΛ ℓ).mp hℓ))
    (Subgroup.mem_sup_right (hc.bar_CN_conj_mem ht (hXR hx) hν))

theorem Ctx.exists_iso_natural (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B)
    {X : Subgroup (Mbar M Q)} (hXR : X ≤ bar M Q (Rt M (LB M Q B) t))
    (hXN : X ⊓ bar M Q (hc.CN t) = ⊥)
    (hsup : bar M Q (Rt M (LB M Q B) t) = bar M Q (hc.CN t) ⊔ X)
    (hCNX : bar M Q (hc.CN t) ≤ Subgroup.normalizer (X : Set (Mbar M Q)))
    {K' : Type} [Field K'] {ι : Type} [Fintype ι] [DecidableEq ι] {Xcl : Subgroup (GL ι K')}
    (hnat : NaturalRep K' Xcl (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t)) :
    Nonempty (↥X ≃* ↥Xcl) := by
  obtain ⟨φ, hφr, hφk, -⟩ := hnat
  obtain ⟨π, hπs, hπk⟩ := hc.exists_bar_hom ht φ hφr hφk
  let f : ↥X →* ↥Xcl := π.comp (Subgroup.inclusion hXR)
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 := (hπk (Subgroup.inclusion hXR x)).mp hx
    have h2 : (x : Mbar M Q) ∈ X ⊓ bar M Q (hc.CN t) := ⟨x.2, h1⟩
    rw [hXN, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hsurj : Function.Surjective f := by
    intro g
    obtain ⟨y, hy⟩ := hπs g
    have hyR : (y : Mbar M Q) ∈ bar M Q (hc.CN t) ⊔ X := hsup ▸ y.2
    obtain ⟨ν, hν, x, hx, hνx⟩ := exists_mul_of_mem_sup_of_le_normalizer hCNX hyR
    have hνR := hc.bar_CN_le_bar_Rt t hν
    refine ⟨⟨x, hx⟩, ?_⟩
    show π ⟨x, hXR hx⟩ = g
    have hy' : y = ⟨ν, hνR⟩ * ⟨x, hXR hx⟩ := Subtype.ext hνx.symm
    rw [← hy, hy', map_mul, (hπk ⟨ν, hνR⟩).mpr hν, one_mul]
  exact ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩⟩

theorem Ctx.tensorSide_uniform (hc : Ctx M Q Z B) {n : ℕ} {K : Type} [Field K] [Finite K]
    {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)} {b : M₀.E}
    (hS : IsTensorSetup hc n M₀ ρ b)
    (h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G)) {t : G} (ht : t ∈ LB M Q B)
    {X : Subgroup (Mbar M Q)} (hXR : X ≤ bar M Q (Rt M (LB M Q B) t))
    (hXn : ∀ r ∈ bar M Q (Rt M (LB M Q B) t), ∀ x ∈ X, r * x * r⁻¹ ∈ X)
    (hXN : X ⊓ bar M Q (hc.CN t) = ⊥)
    (hsup : bar M Q (Rt M (LB M Q B) t) = bar M Q (hc.CN t) ⊔ X)
    {K' : Type} [Field K'] [Finite K'] {ι : Type} [Fintype ι] [DecidableEq ι]
    {Xcl : Subgroup (GL ι K')} (hK' : Nat.card K' = Nat.card Z) (hcl : ClassicalNat K' Xcl)
    (hnat : NaturalRep K' Xcl (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t)) :
    ∃ W : Submodule K M₀.E,
      TensorSide ρ b X (X ⊓ (bar M Q (LB M Q B) ⊔ bar M Q (hc.CN t))) W (Fintype.card ι) := by
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by have := hcl.three_le; omega)
  have hCNX : bar M Q (hc.CN t) ≤ Subgroup.normalizer (X : Set (Mbar M Q)) := fun m hm =>
    Subgroup.mem_normalizer_fintype fun x hx => hXn m (hc.bar_CN_le_bar_Rt _ hm) x hx
  obtain ⟨θ, Ψ, π, hπr, hπk, hΨθ, hΨπ⟩ := hc.natural_transport hS ht hK' hcl.addComm hnat
  have hXH : X ≤ bar M Q (H0 M Z) :=
    hXR.trans ((Ctx.bar_Rt_le_bar_Lgen t).trans hc.bar_Lgen_le_bar_H0)
  have hinv : ∀ x ∈ X, ∀ w ∈ hc.VtSub hS.model t, (ρ x).toAdd w ∈ hc.VtSub hS.model t :=
    fun x hx w hw => hc.act_mem_VtSub hS ht x (hXR hx) w hw
  let φ : ↥X →* GL ι K' := π.comp (Subgroup.inclusion hXR)
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 := (hπk (Subgroup.inclusion hXR x)).mp hx
    have h2 : (x : Mbar M Q) ∈ X ⊓ bar M Q (hc.CN t) := ⟨x.2, h1⟩
    rw [hXN, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hφr : φ.range = Xcl := by
    rw [← hπr]
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨y, rfl⟩
      have hyR : (y : Mbar M Q) ∈ bar M Q (hc.CN t) ⊔ X := hsup ▸ y.2
      obtain ⟨ν, hν, x, hx, hνx⟩ := exists_mul_of_mem_sup_of_le_normalizer hCNX hyR
      have hνR := hc.bar_CN_le_bar_Rt t hν
      refine ⟨⟨x, hx⟩, ?_⟩
      show π ⟨x, hXR hx⟩ = π y
      have hy' : y = ⟨ν, hνR⟩ * ⟨x, hXR hx⟩ := Subtype.ext hνx.symm
      rw [hy', map_mul, (hπk ⟨ν, hνR⟩).mpr hν, one_mul]
  have hbW : b ∈ hc.VtSub hS.model t := by
    obtain ⟨u, huB, huQ, hu⟩ := hS.b_img
    have hB1 : conjSubgroup 1 B ≤ Vt M (LB M Q B) B Z t :=
      sec39_conjB_le_Vt M.one_mem (by rw [conjSubgroup_one]; exact ht)
    refine ⟨u, hB1 (by rw [conjSubgroup_one]; exact huB), huQ, hu⟩
  have hirred : ∀ S : Submodule K M₀.E, S ≤ hc.VtSub hS.model t →
      (∀ x ∈ X, ∀ v ∈ S, (ρ x).toAdd v ∈ S) → S = ⊥ ∨ S = hc.VtSub hS.model t := by
    intro S hSW hSX
    refine hc.irred_VtSub hS h35 ht S hSW (fun x hx v hv => ?_)
    have hxR : x ∈ bar M Q (hc.CN t) ⊔ X := hsup ▸ hx
    obtain ⟨ν, hν, x', hx', hνx⟩ := exists_mul_of_mem_sup_of_le_normalizer hCNX hxR
    rw [← hνx, act_mul_apply, hc.act_CN hS ht ν hν _ (hSW (hSX x' hx' v hv))]
    exact hSX x' hx' v hv
  exact ⟨hc.VtSub hS.model t, tensorSide_of_natural ρ X _ b _ Xcl hcl θ Ψ hΨθ φ hφr hφinj hinv
    (fun x w => hΨπ ⟨x, hXR x.2⟩ w) (fun x hx => hS.lin x (hXH hx)) hirred hbW hS.b_ne inf_le_left
    (hc.sq_inter ht hXN) (hc.fix_inter hS ht hXR hsup hCNX) (hc.norm_inter hS ht hXR hXn)⟩

end Transport

section Final


theorem tensorSide_of_ctx (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (h44 : Stroth44Statement) (hCQ : ClassicalQuasisimpleStatement)
    (hCG : ClassicalPointStatement) : TensorSideStatement := by
  intro G _ _ M Q Z B hN hc n hw hn hno hgen K _ _ γ M₀ ρ b hS X hX hXSL t ht ht1 hcomm
  classical
  have h35 := (stroth_3_5 h34 hc hw hn hno hgen).2.1
  have hcs := hc.compSimple h34 h44 hw hn hno hgen
  have hXc : IsComponent X := isComponent_of_normal_normal hc.normal_bar_Lgen hX.1 hX.2.1 hX.2.2
  have htQ : (t : G) ∉ Q := fun h =>
    ht1 ((QuotientGroup.eq_one_iff t).mpr (Subgroup.mem_subgroupOf.mpr h))
  have hXR : X ≤ bar M Q (Rt M (LB M Q B) (t : G)) :=
    hc.component_le_bar_Rt h34 hw hn hno hgen hcs hXc ht fun x hx => (hcomm x hx).symm
  have hXn : ∀ r ∈ bar M Q (Rt M (LB M Q B) (t : G)), ∀ x ∈ X, r * x * r⁻¹ ∈ X :=
    fun r hr x hx => conj_mem_of_subgroupOf_normal hX.1 hX.2.1
      (Ctx.bar_Rt_le_bar_Lgen (t : G) hr) hx
  have hXN : X ⊓ bar M Q (hc.CN (t : G)) = ⊥ :=
    hc.component_inf_CN_eq_bot h34 hw hn hno hgen hcs ht hXc hXR
  have hsup := hc.Rt_eq_CN_sup h34 h310 hCQ hw hn hno hgen hcs ht htQ hXc hXR hXn hXSL
  have hCNX : bar M Q (hc.CN (t : G)) ≤ Subgroup.normalizer (X : Set (Mbar M Q)) := fun m hm =>
    Subgroup.mem_normalizer_fintype fun x hx => hXn m (hc.bar_CN_le_bar_Rt _ hm) x hx
  haveI := isSimpleGroup_of_center_eq_bot hXc (hcs X hXc)
  have hΛ := hc.swapHyp hw hn hno
  have hRne : Rt M (LB M Q B) (t : G) ≠ LB M Q B := by
    intro hRL
    obtain ⟨a, b', hab⟩ := exists_noncomm_of_isComponent hXc
    have hXΛ : X ≤ bar M Q (LB M Q B) := by
      have := hXR
      rwa [hRL] at this
    exact hab (Subtype.ext (hΛ.comm _ (hXΛ a.2) _ (hXΛ b'.2)))
  rcases h310 G M Q Z B hc n hw hn hno hgen (t : G) ht htQ with hRL | ⟨K', hF', hFin', hK', hnat⟩
  · exact absurd hRL hRne
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  haveI : CharP K' 2 := charP_two_of_card_eq_two_pow (hK'.trans hZ2)
  have hq4 : 4 ≤ Nat.card K' := by rw [hK']; exact hc.hyp.q4
  have hSL2 : CFSG.IsQuasisimple ↥(StatedSL 2 K') := (hCQ K' hq4).1 2 le_rfl
  rcases hnat with ⟨m, hm, hn'⟩ | ⟨m, hm, hn'⟩ | ⟨m, hm, hn'⟩ | ⟨m, b', c', hm, hirr, hn'⟩
  · obtain ⟨e⟩ := hc.exists_iso_natural ht hXR hXN hsup hCNX hn'
    have h3 : 3 ≤ m := by
      by_contra h
      obtain rfl : m = 2 := by omega
      exact hXSL ⟨K', hF', hFin', hK', ⟨e⟩⟩
    obtain ⟨W, hW⟩ := hc.tensorSide_uniform hS h35 ht hXR hXn hXN hsup hK'
      (classicalNat_statedSL hCQ hCG hq4 h3) hn'
    exact ⟨W, _, hW⟩
  · obtain ⟨e⟩ := hc.exists_iso_natural ht hXR hXN hsup hCNX hn'
    have h2 : 2 ≤ m := by
      by_contra h
      obtain rfl : m = 1 := by omega
      obtain ⟨e'⟩ := nonempty_statedSp_one_mulEquiv_statedSL_two K'
      exact hXSL ⟨K', hF', hFin', hK', ⟨e.trans e'⟩⟩
    obtain ⟨W, hW⟩ := hc.tensorSide_uniform hS h35 ht hXR hXn hXN hsup hK'
      (classicalNat_statedSp hCQ hCG hq4 h2) hn'
    exact ⟨W, _, hW⟩
  · obtain ⟨e⟩ := hc.exists_iso_natural ht hXR hXN hsup hCNX hn'
    have h3 : 3 ≤ m := by
      by_contra h
      obtain rfl : m = 2 := by omega
      obtain ⟨e'⟩ := (hCQ K' hq4).2.2.2.2
      exact not_isSimpleGroup_of_prod hSL2 (e.trans e')
    obtain ⟨W, hW⟩ := hc.tensorSide_uniform hS h35 ht hXR hXn hXN hsup hK'
      (classicalNat_statedOmegaPlus hCQ hCG hq4 h3) hn'
    exact ⟨W, _, hW⟩
  · obtain ⟨W, hW⟩ := hc.tensorSide_uniform hS h35 ht hXR hXn hXN hsup hK'
      (classicalNat_statedOmegaMinus hCQ hCG hq4 b' c' hm hirr) hn'
    exact ⟨W, _, hW⟩

end Final

end CFSG.RankThree.GF2n.Stroth80
