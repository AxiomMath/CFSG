module

public import CFSG.RankThree.GF2n.Stroth80.Sec7Transport
public import CFSG.RankThree.GF2n.Stroth80.Sec7HConj
public import CFSG.RankThree.GF2n.Stroth80.Sec41iiTensorSide
public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaPoints
public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaSingular

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

@[expose] def sec7Hset {G : Type} [Group G] {Q Z : Subgroup G} {K : Type} [Field K]
    {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ) (V B' : Subgroup G) : AddSubgroup M₀.E :=
  M₀.img ((V ⊓ QB B') ⊔ Z)

theorem sec7_line_eq {K E : Type*} [Field K] [AddCommGroup E] [Module K E] {S : E → Prop}
    {b e : E} (hS : ∀ v, S v ↔ ∃ s : K, v = s • b) (he : S e) (he0 : e ≠ 0) :
    ∀ v, S v ↔ ∃ s : K, v = s • e := by
  obtain ⟨s₀, hs₀⟩ := (hS e).mp he
  have hs0 : s₀ ≠ 0 := by
    rintro rfl
    exact he0 (by rw [hs₀, zero_smul])
  intro v
  rw [hS v]
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s * s₀⁻¹, by rw [hs₀, smul_smul, mul_assoc, inv_mul_cancel₀ hs0, mul_one]⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s * s₀, by rw [hs₀, smul_smul]⟩

section Model

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem sec7_img_conj_iff (hc : Ctx M Q Z B) {n : ℕ} {K : Type} [Field K] [Finite K]
    {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
    (ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)) (b : M₀.E)
    (hS : IsTensorSetup hc n M₀ ρ b) {m : G} (hm : m ∈ M) {S : Subgroup G}
    (hZS : Z ≤ S) (e : M₀.E) :
    (ρ (QuotientGroup.mk ⟨m, hm⟩)).toAdd e ∈ M₀.img (conjSubgroup m S) ↔ e ∈ M₀.img S := by
  obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
  have hmxQ : m * x * m⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M hm).1 x hxQ
  have h1 : M₀.π (m * x * m⁻¹) = (ρ (QuotientGroup.mk ⟨m, hm⟩)).toAdd (M₀.π x) :=
    hS.conj ⟨m, hm⟩ x hxQ
  have hZ' : Z ≤ conjSubgroup m S := by
    intro z hz
    have hz' : z ∈ conjSubgroup m Z := by rw [hc.conj_Z_eq hm]; exact hz
    exact mem_conjSubgroup.mpr (hZS (mem_conjSubgroup.mp hz'))
  rw [← h1, Tim79.QuadModel.mem_img_iff M₀ hZ' hmxQ, Tim79.QuadModel.mem_img_iff M₀ hZS hxQ]
  have h := mem_conjSubgroup (g := m) (T := S) (x := m * x * m⁻¹)
  rw [show m⁻¹ * (m * x * m⁻¹) * m = x by group] at h
  exact h

theorem sec7_Hset_conj (hc : Ctx M Q Z B) {n : ℕ} {K : Type} [Field K] [Finite K]
    {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
    (ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)) (b : M₀.E)
    (hS : IsTensorSetup hc n M₀ ρ b) {x : G} (hx : x ∈ M) (V : Subgroup G)
    (hxV : conjSubgroup x V = V) (g : G) (e : M₀.E) :
    (ρ (QuotientGroup.mk ⟨x, hx⟩)).toAdd e ∈ sec7Hset M₀ V (conjSubgroup (x * g) B) ↔
      e ∈ sec7Hset M₀ V (conjSubgroup g B) := by
  unfold sec7Hset
  rw [conjSubgroup_mul, sec7H_conj x V Z (conjSubgroup g B) hxV (hc.conj_Z_eq hx)]
  exact sec7_img_conj_iff hc M₀ ρ b hS hx le_sup_right e

theorem sec7_Hset_eq_of_img_le (hc : Ctx M Q Z B) {K : Type} [Field K] [Finite K]
    {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ) {g g' : G} (hg : g ∈ M) (hg' : g' ∈ M)
    (V : Subgroup G) (hZV : Z ≤ V) (hVQ : V ≤ Q)
    (h : M₀.img (conjSubgroup g' B) ≤ M₀.img (conjSubgroup g B)) :
    sec7Hset M₀ V (conjSubgroup g' B) = sec7Hset M₀ V (conjSubgroup g B) := by
  have hle : conjSubgroup g' B ≤ Z ⊔ conjSubgroup g B := by
    intro y hy
    have hyQ : y ∈ Q := (hc.conj_of_mem hg').le hy
    have h1 : M₀.π y ∈ M₀.img (conjSubgroup g B) := h (M₀.pi_mem_img hy hyQ)
    have h2 : M₀.π y ∈ M₀.img (Z ⊔ conjSubgroup g B) := M₀.img_mono le_sup_right h1
    exact (Tim79.QuadModel.mem_img_iff M₀ le_sup_left hyQ).mp h2
  unfold sec7Hset
  rw [sec7H_eq_of_le_ZB (hc.conj_of_mem hg) (hc.conj_of_mem hg') V hZV
    (fun v hv p hp => hc.hyp.toHyp79.comm_mem_V (hVQ hv) hp) hle]

theorem sec7_img_conj_line (hc : Ctx M Q Z B) {n : ℕ} {K : Type} [Field K] [Finite K]
    {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
    (ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)) (b : M₀.E)
    (hS : IsTensorSetup hc n M₀ ρ b) {g : G} (hg : g ∈ M) {e₀ : M₀.E} (he₀ : e₀ ≠ 0)
    (hline : ∀ v, v ∈ M₀.img B ↔ ∃ s : K, v = s • e₀) :
    (ρ (QuotientGroup.mk ⟨g, hg⟩)).toAdd e₀ ≠ 0 ∧
    ∀ v, v ∈ M₀.img (conjSubgroup g B) ↔
      ∃ s : K, v = s • (ρ (QuotientGroup.mk ⟨g, hg⟩)).toAdd e₀ := by
  obtain ⟨bg, -, -, hbg, -⟩ := (hc.conj_of_mem hg).dictB hS.model
  have he₀B : e₀ ∈ M₀.img B := (hline e₀).mpr ⟨1, (one_smul K e₀).symm⟩
  obtain ⟨y, hyB, hyQ, hy⟩ := M₀.mem_img.mp he₀B
  have hgyQ : g * y * g⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M hg).1 y hyQ
  have hmem : (ρ (QuotientGroup.mk ⟨g, hg⟩)).toAdd e₀ ∈ M₀.img (conjSubgroup g B) := by
    have h1 : M₀.π (g * y * g⁻¹) = (ρ (QuotientGroup.mk ⟨g, hg⟩)).toAdd (M₀.π y) :=
      hS.conj ⟨g, hg⟩ y hyQ
    rw [← hy, ← h1]
    refine M₀.pi_mem_img ?_ hgyQ
    rw [mem_conjSubgroup, show g⁻¹ * (g * y * g⁻¹) * g = y by group]
    exact hyB
  have hne : (ρ (QuotientGroup.mk ⟨g, hg⟩)).toAdd e₀ ≠ 0 := by
    intro h0
    exact he₀ ((AddEquiv.map_eq_zero_iff _).mp h0)
  exact ⟨hne, sec7_line_eq (S := fun v => v ∈ M₀.img (conjSubgroup g B)) hbg hmem hne⟩


abbrev Sec7Om4Idx : Type := Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2

theorem sec7_natural_psi (hc : Ctx M Q Z B) {n : ℕ} {K : Type} [Field K] [Finite K]
    {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
    (ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)) (b : M₀.E)
    (hS : IsTensorSetup hc n M₀ ρ b) {t : G} (ht : t ∈ LB M Q B)
    {K' : Type} [Field K'] [Finite K'] {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {Xcl : Subgroup (GL ι K')} (hK' : Nat.card K' = Nat.card Z)
    (hcomm : AddCommutantScalar Xcl) (φ : ↥(Rt M (LB M Q B) t) →* GL ι K')
    (hφ : φ.range = Xcl) [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψs : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (ι → K'))
    (hψs : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψs (QuotientGroup.mk w)) =
        (φ s : Matrix ι ι K') *ᵥ Multiplicative.toAdd (ψs (QuotientGroup.mk v))) :
    ∃ (θ : K ≃+* K') (Ψ : ↥(hc.VtSub hS.model t) ≃+ (ι → K')),
      (∀ (a : K) (w : ↥(hc.VtSub hS.model t)), Ψ (a • w) = θ a • Ψ w) ∧
      (∀ (v : ↥(Vt M (LB M Q B) B Z t)) (h : M₀.π v ∈ hc.VtSub hS.model t),
        Ψ ⟨M₀.π v, h⟩ = secVec ψs v) ∧
      (∀ (r : ↥(Rt M (LB M Q B) t)) (w : ↥(hc.VtSub hS.model t))
        (h : (ρ (QuotientGroup.mk ⟨(r : G), hc.Rt_le_M t r.2⟩)).toAdd (w : M₀.E) ∈
          hc.VtSub hS.model t),
        Ψ ⟨(ρ (QuotientGroup.mk ⟨(r : G), hc.Rt_le_M t r.2⟩)).toAdd (w : M₀.E), h⟩ =
          (φ r : Matrix ι ι K') *ᵥ Ψ w) := by
  classical
  have hRV := hc.Rt_normalizes_Vt ht
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
  obtain ⟨θ, hθ⟩ := exists_ringEquiv_natural hcard M₀ (hc.Vt_le_Q t) hcomm hSmul hlin φ hφ
    hRV ψs hψs
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ↥(hc.VtSub hS.model t) ≃+ (ι → K'),
      ∀ (v : ↥(Vt M (LB M Q B) B Z t)) (h : M₀.π v ∈ hc.VtSub hS.model t),
        Ψ ⟨M₀.π v, h⟩ = Multiplicative.toAdd (ψs (QuotientGroup.mk v)) :=
    exists_addEquiv_imgSub M₀ (hc.Vt_le_Q t) hSmul ψs
  refine ⟨θ, Ψ, ?_, hΨ, ?_⟩
  · intro c w
    have hw : (w : M₀.E) ∈ M₀.img (Vt M (LB M Q B) B Z t) :=
      (hc.mem_VtSub hS.model t).mp w.2
    have hcw : c • (w : M₀.E) ∈ M₀.img (Vt M (LB M Q B) B Z t) := hSmul c _ hw
    obtain ⟨v, hvV, hvQ, hv⟩ := hw
    obtain ⟨v', hv'V, hv'Q, hv'⟩ := hcw
    have e1 : Ψ (c • w) =
        Multiplicative.toAdd (ψs (QuotientGroup.mk (⟨v', hv'V⟩ : ↥(Vt M (LB M Q B) B Z t)))) := by
      have hce : c • w = ⟨M₀.π v', (hc.mem_VtSub hS.model t).mpr (M₀.pi_mem_img hv'V hv'Q)⟩ :=
        Subtype.ext hv'.symm
      rw [hce]
      exact hΨ ⟨v', hv'V⟩ _
    have e2 : Ψ w =
        Multiplicative.toAdd (ψs (QuotientGroup.mk (⟨v, hvV⟩ : ↥(Vt M (LB M Q B) B Z t)))) := by
      have hwe : w = ⟨M₀.π v, (hc.mem_VtSub hS.model t).mpr (M₀.pi_mem_img hvV hvQ)⟩ :=
        Subtype.ext hv.symm
      rw [hwe]
      exact hΨ ⟨v, hvV⟩ _
    have hcu : M₀.π v' = c • M₀.π v := by rw [hv', hv]
    rw [e1, e2]
    exact hθ c ⟨v, hvV⟩ ⟨v', hv'V⟩ hcu
  · intro r w h
    have hrR : (r : G) ∈ Rt M (LB M Q B) t := r.2
    have hrM : (r : G) ∈ M := hc.Rt_le_M t hrR
    have hw : (w : M₀.E) ∈ M₀.img (Vt M (LB M Q B) B Z t) :=
      (hc.mem_VtSub hS.model t).mp w.2
    obtain ⟨v, hvV, hvQ, hv⟩ := hw
    have hrV : (r : G) * v * (r : G)⁻¹ ∈ Vt M (LB M Q B) B Z t :=
      (Subgroup.mem_normalizer_iff.mp (hRV hrR) v).mp hvV
    have hrQ : (r : G) * v * (r : G)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hrM) v).mp hvQ
    have hmemV : M₀.π ((r : G) * v * (r : G)⁻¹) ∈ hc.VtSub hS.model t :=
      (hc.mem_VtSub hS.model t).mpr (M₀.pi_mem_img hrV hrQ)
    have hact : (ρ (QuotientGroup.mk ⟨(r : G), hrM⟩)).toAdd (w : M₀.E) =
        M₀.π ((r : G) * v * (r : G)⁻¹) := by
      rw [← hv]
      exact (hS.conj ⟨(r : G), hrM⟩ v hvQ).symm
    have hψr := hψs r ⟨v, hvV⟩ ⟨(r : G) * v * (r : G)⁻¹, hrV⟩ rfl
    have hLHS : Ψ ⟨(ρ (QuotientGroup.mk ⟨(r : G), hrM⟩)).toAdd (w : M₀.E), h⟩ =
        Multiplicative.toAdd (ψs (QuotientGroup.mk
          (⟨(r : G) * v * (r : G)⁻¹, hrV⟩ : ↥(Vt M (LB M Q B) B Z t)))) := by
      have e : (⟨(ρ (QuotientGroup.mk ⟨(r : G), hrM⟩)).toAdd (w : M₀.E), h⟩ :
          ↥(hc.VtSub hS.model t)) = ⟨M₀.π ((r : G) * v * (r : G)⁻¹), hmemV⟩ :=
        Subtype.ext hact
      rw [e]
      exact hΨ ⟨(r : G) * v * (r : G)⁻¹, hrV⟩ _
    have hRHS : Ψ w =
        Multiplicative.toAdd (ψs (QuotientGroup.mk (⟨v, hvV⟩ : ↥(Vt M (LB M Q B) B Z t)))) := by
      have e : w = ⟨M₀.π v, (hc.mem_VtSub hS.model t).mpr (M₀.pi_mem_img hvV hvQ)⟩ :=
        Subtype.ext hv.symm
      rw [e]
      exact hΨ ⟨v, hvV⟩ _
    rw [hLHS, hRHS]
    exact hψr


open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap in
theorem sec7_om4_setup (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) (hom : OmegaMinusNat hc t 2)
    {K : Type} [Field K] [Finite K] {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
    (ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)) (b : M₀.E)
    (hS : IsTensorSetup hc n M₀ ρ b) :
    ∃ (K' : Type) (_ : Field K') (_ : Finite K') (_ : CharP K' 2) (b' c' : K')
      (_ : ∀ s : K', s ^ 2 + b' * s + c' ≠ 0)
      (φ : ↥(Rt M (LB M Q B) t) →* GL Sec7Om4Idx K')
      (θ : K ≃+* K') (Ψ : ↥(hc.VtSub hS.model t) ≃+ (Sec7Om4Idx → K')),
      Nat.card K' = Nat.card K ∧
      φ.range = StatedOmega (StatedQuadMinus 2 K' b' c') ∧
      (∀ (a : K) (w : ↥(hc.VtSub hS.model t)), Ψ (a • w) = θ a • Ψ w) ∧
      (∀ (r : ↥(Rt M (LB M Q B) t)) (w : ↥(hc.VtSub hS.model t))
        (h : (ρ (QuotientGroup.mk ⟨(r : G), hc.Rt_le_M t r.2⟩)).toAdd (w : M₀.E) ∈
          hc.VtSub hS.model t),
        Ψ ⟨(ρ (QuotientGroup.mk ⟨(r : G), hc.Rt_le_M t r.2⟩)).toAdd (w : M₀.E), h⟩ =
          ((φ r : GL Sec7Om4Idx K') : Matrix Sec7Om4Idx Sec7Om4Idx K') *ᵥ Ψ w) ∧
      ∃ (e₀ : M₀.E) (he₀ : e₀ ∈ hc.VtSub hS.model t), e₀ ≠ 0 ∧
        (∀ v, v ∈ M₀.img B ↔ ∃ s : K, v = s • e₀) ∧
        Ψ ⟨e₀, he₀⟩ ≠ 0 ∧ quadMinus 2 K' b' c' (Ψ ⟨e₀, he₀⟩) = 0 ∧
        (∀ w, ((Ψ.symm w : ↥(hc.VtSub hS.model t)) : M₀.E) ∈
          sec7Hset M₀ (Vt M (LB M Q B) B Z t) B ↔
            polar (quadMinus 2 K' b' c') (Ψ ⟨e₀, he₀⟩) w = 0) := by
  classical
  obtain ⟨K', fK', finK', hK', b', c', hirr, hnat⟩ := hom
  haveI : CharP K' 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK'.trans he)
  haveI : Nonempty Sec7Om4Idx := ⟨Sum.inr (Sum.inr 0)⟩
  obtain ⟨φ, hφ, hker, hnorm, hn, ψs, hψs⟩ := hnat
  haveI := hn
  have hnatSO : SpNat hc t ∨ OmegaNat hc t := Or.inr hs.omegaNat
  have h3 : 3 ≤ Module.finrank K' (Sec7Om4Idx → K') := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp only [Sec7Om4Idx, Fintype.card_sum, Fintype.card_fin]
    omega
  have hE := ElemMatrixIso.minus (K := K') (m := 2) (b := b') (c := c') le_rfl hirr
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite 2 K' hirr
  have hX := addCommutantScalar_statedOmegaMinus (K := K') (m := 2) (b := b') (c := c')
    le_rfl hirr
  obtain ⟨u, hQu, hu0, hBu, hHu, -, -⟩ := hc.omega_points_core h34 hRoot hs.toSec5 hnatSO hK'
    hE hQ h3 hX φ hφ hker ψs hψs
    (hc.omega_singular h34 hRoot hs.toSec5 hnatSO hK' hE hQ h3 hX φ hφ ψs hψs)
  obtain ⟨θ, Ψ, hΨc, hΨsec, hΨr⟩ := sec7_natural_psi hc M₀ ρ b hS hs.toSec5.mem hK' hX φ hφ
    ψs hψs
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  obtain ⟨b₀, hb₀B, hb₀u⟩ := (hBu u).mpr ⟨1, (one_smul K' u).symm⟩
  have hb₀Q : (b₀ : G) ∈ Q := hVQ b₀.2
  have he₀ : M₀.π b₀ ∈ hc.VtSub hS.model t :=
    (hc.mem_VtSub hS.model t).mpr (M₀.pi_mem_img b₀.2 hb₀Q)
  have hΨe₀ : Ψ ⟨M₀.π b₀, he₀⟩ = u := (hΨsec b₀ he₀).trans hb₀u
  have hne : M₀.π b₀ ≠ 0 := by
    intro h0
    have : (⟨M₀.π b₀, he₀⟩ : ↥(hc.VtSub hS.model t)) = 0 := Subtype.ext h0
    rw [this, map_zero] at hΨe₀
    exact hu0 hΨe₀.symm
  obtain ⟨bB, -, -, hbB, -⟩ := hc.dictB hS.model
  have hline : ∀ v, v ∈ M₀.img B ↔ ∃ s : K, v = s • M₀.π b₀ :=
    sec7_line_eq (S := fun v => v ∈ M₀.img B) hbB (M₀.pi_mem_img hb₀B (hc.le hb₀B)) hne
  refine ⟨K', fK', finK', inferInstance, b', c', hirr, φ, θ, Ψ, ?_, hφ, hΨc, hΨr,
    M₀.π b₀, he₀, hne, hline, by rw [hΨe₀]; exact hu0, by rw [hΨe₀]; exact hQu, ?_⟩
  · exact hK'.trans hS.card.symm
  · intro w
    rw [hΨe₀, ← hHu w]
    constructor
    · intro h
      obtain ⟨x, hx, hxQ, hxe⟩ := M₀.mem_img.mp h
      obtain ⟨y, hy, z, hz, rfl⟩ :=
        exists_mul_of_mem_sup (B := Vt M (LB M Q B) B Z t ⊓ QB B) (Z' := Z)
        (fun b hb z hz => by
          have := hc.conj_Z_of_mem_Q (hVQ hb.1) hz
          calc b * z = (b * z * b⁻¹) * b := by group
            _ = z * b := by rw [this]) hx
      have hyV : y ∈ Vt M (LB M Q B) B Z t := hy.1
      have hyQ : y ∈ Q := hVQ hyV
      have hzQ : z ∈ Q := hc.Z_le_Q hz
      have hπz : M₀.π z = 0 := (M₀.π_ker z hzQ).mpr hz
      have hπ : M₀.π (y * z) = M₀.π y := by rw [M₀.π_mul y hyQ z hzQ, hπz, add_zero]
      have hmem : M₀.π y ∈ hc.VtSub hS.model t :=
        (hc.mem_VtSub hS.model t).mpr (M₀.pi_mem_img hyV hyQ)
      refine ⟨⟨y, hyV⟩, hy, ?_⟩
      rw [← hΨsec ⟨y, hyV⟩ hmem]
      have : (Ψ.symm w : ↥(hc.VtSub hS.model t)) = ⟨M₀.π y, hmem⟩ :=
        Subtype.ext (hxe.symm.trans hπ)
      rw [← this, Ψ.apply_symm_apply]
    · rintro ⟨v, hv, hvw⟩
      have hvQ : (v : G) ∈ Q := hVQ v.2
      have hmem : M₀.π v ∈ hc.VtSub hS.model t :=
        (hc.mem_VtSub hS.model t).mpr (M₀.pi_mem_img v.2 hvQ)
      have : Ψ.symm w = ⟨M₀.π v, hmem⟩ := by
        apply Ψ.injective
        rw [Ψ.apply_symm_apply, hΨsec v hmem, hvw]
      rw [this]
      exact M₀.pi_mem_img (Subgroup.mem_sup_left hv) hvQ

end Model

end CFSG.RankThree.GF2n.Stroth80
