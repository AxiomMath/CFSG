module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec64Cor
public import CFSG.RankThree.GF2n.Stroth80.Sec123SL2

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.GF2n
open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement Matrix

namespace HS6

section Basic2

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem conj_Z_of_mem_Q (hc : Ctx M Q Z B) {y z : G} (hy : y ∈ Q) (hz : z ∈ Z) :
    y * z * y⁻¹ = z := by
  have h : z ∈ Subgroup.centralizer (Q : Set G) := by rw [hc.hyp.centralizer_Q]; exact hz
  have := Subgroup.mem_centralizer_iff.mp h y hy
  rw [mul_inv_eq_iff_eq_mul]
  exact this

theorem comm_comm_eq_one (hc : Ctx M Q Z B) {V : Subgroup G} (hVQ : V ≤ Q) {h x v : G}
    (hhZ : ∀ z ∈ Z, h * z * h⁻¹ = z) (hx : x ∈ Q) (hv : v ∈ V) (hhv : ⁅h, v⁆ ∈ Z)
    (hhM : h ∈ M) : ⁅⁅h, x⁆, v⁆ = 1 := by
  have hZQ : Z ≤ Q := hc.hyp.Z_normal.1
  have hz1 : ⁅x, v⁆ ∈ Z := comm_mem_Z_of_Q hc hx (hVQ hv)
  have haQ : h * x * h⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M hhM).1 x hx
  have hz3 : ⁅h * x * h⁻¹, v⁆ ∈ Z := comm_mem_Z_of_Q hc haQ (hVQ hv)
  have hA : ⁅h * x * h⁻¹, h * v * h⁻¹⁆ = ⁅x, v⁆ := by
    have : ⁅h * x * h⁻¹, h * v * h⁻¹⁆ = h * ⁅x, v⁆ * h⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [this]
    exact hhZ _ hz1
  have hB : h * v * h⁻¹ = ⁅h, v⁆ * v := by simp only [commutatorElement_def]; group
  have hC : ⁅h * x * h⁻¹, ⁅h, v⁆ * v⁆ = ⁅h, v⁆ * ⁅h * x * h⁻¹, v⁆ * ⁅h, v⁆⁻¹ := by
    have haz : (h * x * h⁻¹) * ⁅h, v⁆ = ⁅h, v⁆ * (h * x * h⁻¹) := by
      have := conj_Z_of_mem_Q hc haQ hhv
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    generalize ⁅h, v⁆ = z at haz ⊢
    generalize h * x * h⁻¹ = a at haz ⊢
    simp only [commutatorElement_def]
    calc a * (z * v) * a⁻¹ * (z * v)⁻¹ = (a * z) * v * a⁻¹ * v⁻¹ * z⁻¹ := by group
      _ = (z * a) * v * a⁻¹ * v⁻¹ * z⁻¹ := by rw [haz]
      _ = z * (a * v * a⁻¹ * v⁻¹) * z⁻¹ := by group
  have hD : ⁅h * x * h⁻¹, v⁆ = ⁅x, v⁆ := by
    rw [hB, hC, conj_Z_of_mem_Q hc (hZQ hhv) hz3] at hA
    exact hA
  have hE : ⁅h * x * h⁻¹ * x⁻¹, v⁆ =
      (h * x * h⁻¹) * ⁅x⁻¹, v⁆ * (h * x * h⁻¹)⁻¹ * ⁅h * x * h⁻¹, v⁆ := by
    simp only [commutatorElement_def]; group
  have hF : ⁅x⁻¹, v⁆ = ⁅x, v⁆⁻¹ := by
    have e : ⁅x⁻¹, v⁆ = x⁻¹ * ⁅x, v⁆⁻¹ * x := by simp only [commutatorElement_def]; group
    rw [e]
    have := conj_Z_of_mem_Q hc (Q.inv_mem hx) (Z.inv_mem hz1)
    rwa [inv_inv] at this
  have hG : ⁅h * x * h⁻¹ * x⁻¹, v⁆ = 1 := by
    rw [hE, hF, show (h * x * h⁻¹) * ⁅x, v⁆⁻¹ * (h * x * h⁻¹)⁻¹ = ⁅x, v⁆⁻¹ from
      conj_Z_of_mem_Q hc haQ (Z.inv_mem hz1), hD]
    exact inv_mul_cancel _
  have e0 : ⁅h, x⁆ = h * x * h⁻¹ * x⁻¹ := rfl
  rw [e0]
  exact hG

end Basic2

section Lam

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {n : ℕ} {t : G} {m : ℕ} {X : Subgroup G}
  {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K] [CharP K 2]
  {Q' : QuadraticForm K (ι → K)} {X' : Subgroup (GL ι K)} {E : ElemMatrixIso Q' X'}
  {φ : ↥(Rt M (LB M Q B) t) →* GL ι K}
  [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
  {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
    Multiplicative (ι → K)} {u : ι → K}

theorem OmegaModel.exists_mem_X' (e : Env hc n t m X) (hmod : OmegaModel hc t Q' E φ ψ u)
    {g : GL ι K} (hg : g ∈ X') : ∃ x ∈ X, ∃ hx : x ∈ Rt M (LB M Q B) t, φ ⟨x, hx⟩ = g := by
  rw [← hmod.range] at hg
  obtain ⟨r, rfl⟩ := hg
  have hr : (r : G) ∈ X ⊔ hc.CN t := by rw [sup_comm, e.hNX]; exact r.2
  obtain ⟨x, hx, a, ha, hxa⟩ := exists_mul_of_mem_sup_of_le_normalizer e.X_le_normalizer_CN hr
  have hxR : x ∈ Rt M (LB M Q B) t := e.hXR hx
  have haR : a ∈ Rt M (LB M Q B) t := (Ctx.mem_CN.mp ha).1
  refine ⟨x, hx, hxR, ?_⟩
  have h1 : φ ⟨x, hxR⟩ * φ ⟨a, haR⟩ = φ r := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext hxa
  have h2 : φ ⟨a, haR⟩ = 1 := by
    have : (⟨a, haR⟩ : ↥(Rt M (LB M Q B) t)) ∈ φ.ker := by
      rw [hmod.ker]
      exact Subgroup.mem_subgroupOf.mpr ha
    exact this
  rw [h2, mul_one] at h1
  exact h1


theorem OmegaModel.exists_lambda (e : Env hc n t m X) (hX : AddCommutantScalar X')
    (hmod : OmegaModel hc t Q' E φ ψ u) {h : G} (hhM : h ∈ M)
    (hhV : ∀ v ∈ Vt M (LB M Q B) B Z t, h * v * h⁻¹ ∈ Vt M (LB M Q B) B Z t)
    (hhX : ∀ x ∈ X, ⁅h, x⁆ ∈ Q) :
    ∃ lam : K, ∀ v ∈ Vt M (LB M Q B) B Z t, vecOf ψ (h * v * h⁻¹) = lam • vecOf ψ v := by
  classical
  have ht := e.hs.toSec5.mem
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hVR := hc.Rt_normalizes_Vt ht
  let lift : (ι → K) → ↥(Vt M (LB M Q B) B Z t) := fun w =>
    Classical.choose (exists_secVec_eq ψ w)
  have hlift : ∀ w, secVec ψ (lift w) = w := fun w =>
    Classical.choose_spec (exists_secVec_eq ψ w)
  have hvec_lift : ∀ w, vecOf ψ (lift w : G) = w := fun w => by
    rw [vecOf_of_mem ψ (lift w).2]
    exact hlift w
  let σf : (ι → K) → (ι → K) := fun w => vecOf ψ (h * (lift w : G) * h⁻¹)
  have hσ : ∀ g ∈ Vt M (LB M Q B) B Z t, σf (vecOf ψ g) = vecOf ψ (h * g * h⁻¹) := by
    intro g hg
    have h1 : secVec ψ (lift (vecOf ψ g)) = secVec ψ ⟨g, hg⟩ := by
      rw [hlift, vecOf_of_mem ψ hg]
    have h2 := (secVec_eq_iff ψ _ _).mp h1
    show vecOf ψ (h * (lift (vecOf ψ g) : G) * h⁻¹) = _
    rw [vecOf_eq_iff ψ (hhV _ (lift _).2) (hhV g hg)]
    have : h * (lift (vecOf ψ g) : G) * h⁻¹ * (h * g * h⁻¹)⁻¹ =
        h * ((lift (vecOf ψ g) : G) * g⁻¹) * h⁻¹ := by group
    rw [this]
    exact conj_Z_mem hc hhM h2
  have hadd : ∀ w₁ w₂, σf (w₁ + w₂) = σf w₁ + σf w₂ := by
    intro w₁ w₂
    have e1 : w₁ + w₂ = vecOf ψ ((lift w₁ : G) * (lift w₂ : G)) := by
      rw [vecOf_mul ψ (lift w₁).2 (lift w₂).2, hvec_lift, hvec_lift]
    have e2 : σf (w₁ + w₂) = vecOf ψ (h * ((lift w₁ : G) * (lift w₂ : G)) * h⁻¹) := by
      rw [e1]
      exact hσ _ (Subgroup.mul_mem _ (lift w₁).2 (lift w₂).2)
    have e3 : σf w₁ = vecOf ψ (h * (lift w₁ : G) * h⁻¹) := rfl
    have e4 : σf w₂ = vecOf ψ (h * (lift w₂ : G) * h⁻¹) := rfl
    rw [e2, e3, e4, ← vecOf_mul ψ (hhV _ (lift w₁).2) (hhV _ (lift w₂).2)]
    congr 1
    group
  let σ : (ι → K) →+ (ι → K) := AddMonoidHom.mk' σf hadd
  have hconj : ∀ x ∈ X, ∀ v ∈ Vt M (LB M Q B) B Z t,
      vecOf ψ (h * (x * v * x⁻¹) * h⁻¹) = vecOf ψ (x * (h * v * h⁻¹) * x⁻¹) := by
    intro x hx v hv
    have hxM : x ∈ M := e.X_le_M hx
    have hxR : x ∈ Rt M (LB M Q B) t := e.hXR hx
    have hxv : x * v * x⁻¹ ∈ Vt M (LB M Q B) B Z t :=
      (Subgroup.mem_normalizer_iff.mp (hVR hxR) v).mp hv
    have hA : h * (x * v * x⁻¹) * h⁻¹ ∈ Vt M (LB M Q B) B Z t := hhV _ hxv
    have hB : x * (h * v * h⁻¹) * x⁻¹ ∈ Vt M (LB M Q B) B Z t :=
      (Subgroup.mem_normalizer_iff.mp (hVR hxR) _).mp (hhV v hv)
    rw [vecOf_eq_iff ψ hA hB]
    have hq : ⁅h, x⁆ ∈ Q := hhX x hx
    have hy : x * (h * v * h⁻¹) * x⁻¹ ∈ Q := hVQ hB
    have : h * (x * v * x⁻¹) * h⁻¹ * (x * (h * v * h⁻¹) * x⁻¹)⁻¹ =
        ⁅⁅h, x⁆, x * (h * v * h⁻¹) * x⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [this]
    exact comm_mem_Z_of_Q hc hq hy
  have hequi : ∀ A ∈ X', ∀ w, σ ((A : Matrix ι ι K) *ᵥ w) = (A : Matrix ι ι K) *ᵥ σ w := by
    intro A hA w
    obtain ⟨x, hxX, hxR, rfl⟩ := hmod.exists_mem_X' e hA
    have hv : (lift w : G) ∈ Vt M (LB M Q B) B Z t := (lift w).2
    have hxv : x * (lift w : G) * x⁻¹ ∈ Vt M (LB M Q B) B Z t :=
      (Subgroup.mem_normalizer_iff.mp (hVR hxR) _).mp hv
    have hhv : h * (lift w : G) * h⁻¹ ∈ Vt M (LB M Q B) B Z t := hhV _ hv
    have e1 : (φ ⟨x, hxR⟩ : Matrix ι ι K) *ᵥ w = vecOf ψ (x * (lift w : G) * x⁻¹) := by
      conv_lhs => rw [← hvec_lift w]
      exact (vecOf_conj ψ φ hmod.equi hVR ⟨x, hxR⟩ hv).symm
    have e2 : σ w = vecOf ψ (h * (lift w : G) * h⁻¹) := rfl
    have e3 : (φ ⟨x, hxR⟩ : Matrix ι ι K) *ᵥ σ w =
        vecOf ψ (x * (h * (lift w : G) * h⁻¹) * x⁻¹) := by
      rw [e2]
      exact (vecOf_conj ψ φ hmod.equi hVR ⟨x, hxR⟩ hhv).symm
    rw [e1, e3]
    show σf (vecOf ψ (x * (lift w : G) * x⁻¹)) = _
    rw [hσ _ hxv]
    exact hconj x hxX _ hv
  obtain ⟨c, hc⟩ := hX σ hequi
  refine ⟨c, fun v hv => ?_⟩
  rw [← hσ v hv]
  exact hc _


theorem vecOf_conj_triv {a g : G} (hg : g ∈ Vt M (LB M Q B) B Z t) (hz : ⁅a, g⁆ ∈ Z) :
    a * g * a⁻¹ ∈ Vt M (LB M Q B) B Z t ∧ vecOf ψ (a * g * a⁻¹) = vecOf ψ g := by
  have hxg : a * g * a⁻¹ = ⁅a, g⁆ * g := by simp only [commutatorElement_def]; group
  rw [hxg]
  exact ⟨(Vt M (LB M Q B) B Z t).mul_mem (sec39_Z_le_Vt hz) hg, by
    rw [vecOf_mul ψ (sec39_Z_le_Vt hz) hg, vecOf_of_mem_Z ψ hz sec39_Z_le_Vt, zero_add]⟩

theorem OmegaModel.mem_CN_of_trivial (I : Inputs) (e : Env hc n t m X)
    (hX : AddCommutantScalar X') (hK : Nat.card K = Nat.card Z)
    (hmod : OmegaModel hc t Q' E φ ψ u) {h : G} (hhM : h ∈ M)
    (hhZ : ∀ z ∈ Z, h * z * h⁻¹ = z) (hhX : ∀ x ∈ X, ⁅h, x⁆ ∈ Q)
    (hhV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅h, v⁆ ∈ Z) : h ∈ hc.CN t := by
  classical
  have ht := e.hs.toSec5.mem
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hVR := hc.Rt_normalizes_Vt ht
  have hQN : Q ≤ hc.CN t := hc.Q_le_CN ht
  have hW := e.W_eq_V I.h34
  have hi : ∀ x ∈ Q, ⁅h, x⁆ ∈ Vt M (LB M Q B) B Z t := by
    intro x hx
    have hq : ⁅h, x⁆ ∈ Q := by
      have : ⁅h, x⁆ = (h * x * h⁻¹) * x⁻¹ := rfl
      rw [this]
      exact Q.mul_mem ((hc.conj_mem_Q_of_mem_M hhM).1 x hx) (Q.inv_mem hx)
    rw [← hW]
    refine ⟨hq, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    exact (commutatorElement_eq_one_iff_mul_comm.mp
      (comm_comm_eq_one hc hVQ hhZ hx hv (hhV v hv) hhM)).symm
  let κ : G → ι → K := fun x => vecOf ψ ⁅h, x⁆
  have hQV : ∀ x ∈ Q, ∀ g ∈ Vt M (LB M Q B) B Z t,
      x * g * x⁻¹ ∈ Vt M (LB M Q B) B Z t ∧ vecOf ψ (x * g * x⁻¹) = vecOf ψ g :=
    fun x hx g hg => vecOf_conj_triv (ψ := ψ) hg (comm_mem_Z_of_Q hc hx (hVQ hg))
  have hadd : ∀ x ∈ Q, ∀ y ∈ Q, κ (x * y) = κ x + κ y := by
    intro x hx y hy
    have hid : ⁅h, x * y⁆ = ⁅h, x⁆ * (x * ⁅h, y⁆ * x⁻¹) := by
      simp only [commutatorElement_def]; group
    show vecOf ψ ⁅h, x * y⁆ = vecOf ψ ⁅h, x⁆ + vecOf ψ ⁅h, y⁆
    rw [hid, vecOf_mul ψ (hi x hx) (hQV x hx _ (hi y hy)).1, (hQV x hx _ (hi y hy)).2]
  have hV0 : ∀ x ∈ Vt M (LB M Q B) B Z t, κ x = 0 := fun x hx =>
    (vecOf_eq_zero_iff ψ (hi x (hVQ hx))).mpr (hhV x hx)
  have hequi : ∀ (r : ↥X) (x : ↥Q), κ ((r : G) * x * (r : G)⁻¹) =
      (φ ⟨r, e.hXR r.2⟩ : Matrix ι ι K) *ᵥ κ x := by
    intro r x
    have hrX : (r : G) ∈ X := r.2
    have hrM : (r : G) ∈ M := e.X_le_M hrX
    have hq : ⁅h, (r : G)⁻¹⁆ ∈ Q := hhX _ (X.inv_mem hrX)
    have hcQ : h⁻¹ * (r : G)⁻¹ * h * r ∈ Q := by
      have e1 : h⁻¹ * (r : G)⁻¹ * h * r = h⁻¹ * (⁅h, (r : G)⁻¹⁆)⁻¹ * h⁻¹⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e1]
      exact (hc.conj_mem_Q_of_mem_M (M.inv_mem hhM)).1 _ (Q.inv_mem hq)
    have hcx : ⁅h⁻¹ * (r : G)⁻¹ * h * r, (x : G)⁆ ∈ Z := comm_mem_Z_of_Q hc hcQ x.2
    have hid : ⁅h, (r : G) * x * (r : G)⁻¹⁆ =
        (r : G) * ⁅h * (h⁻¹ * (r : G)⁻¹ * h * r), (x : G)⁆ * (r : G)⁻¹ := by
      simp only [commutatorElement_def]; group
    have hid2 : ⁅h * (h⁻¹ * (r : G)⁻¹ * h * r), (x : G)⁆ =
        ⁅h⁻¹ * (r : G)⁻¹ * h * r, (x : G)⁆ * ⁅h, (x : G)⁆ := by
      have : ⁅h * (h⁻¹ * (r : G)⁻¹ * h * r), (x : G)⁆ =
          h * ⁅h⁻¹ * (r : G)⁻¹ * h * r, (x : G)⁆ * h⁻¹ * ⁅h, (x : G)⁆ := by
        simp only [commutatorElement_def]; group
      rw [this, hhZ _ hcx]
    have hhx : ⁅h, (x : G)⁆ ∈ Vt M (LB M Q B) B Z t := hi x x.2
    have hmem : ⁅h * (h⁻¹ * (r : G)⁻¹ * h * r), (x : G)⁆ ∈ Vt M (LB M Q B) B Z t := by
      rw [hid2]
      exact (Vt M (LB M Q B) B Z t).mul_mem (hZV hcx) hhx
    show vecOf ψ ⁅h, (r : G) * x * (r : G)⁻¹⁆ = _
    rw [hid, vecOf_conj ψ φ hmod.equi hVR ⟨r, e.hXR r.2⟩ hmem, hid2,
      vecOf_mul ψ (hZV hcx) hhx, vecOf_of_mem_Z ψ hcx hZV, zero_add]
  let φX : ↥X →* GL ι K := φ.comp (Subgroup.inclusion e.hXR)
  have hφXrange : φX.range = X' := by
    apply le_antisymm
    · rintro _ ⟨r, rfl⟩
      rw [← hmod.range]
      exact ⟨_, rfl⟩
    · intro g hg
      obtain ⟨x, hx, hxR, rfl⟩ := hmod.exists_mem_X' e hg
      exact ⟨⟨x, hx⟩, rfl⟩
  have hχ := e.chi I.h34
  have hχX : IsChiIso Q X (Vt M (LB M Q B) B Z t) (Vt M (LB M Q B) B Z t) Z t :=
    ⟨hχ.1, hχ.2.1, hχ.2.2.1, hχ.2.2.2.1, fun r hr => hχ.2.2.2.2 r (e.hXR hr)⟩
  obtain ⟨θ, hθ⟩ := exists_scalar_of_chi hχX ψ φX
    (fun s v w hw => hmod.equi ⟨s, e.hXR s.2⟩ v w hw)
    (fun r hr => hVR (e.hXR hr))
    (fun r hr x hx => (hc.conj_mem_Q_of_mem_M (e.X_le_M hr)).1 x hx)
    (by rw [hφXrange]; exact hX) κ hadd hV0 (fun r x => hequi r x)
  obtain ⟨a, haN, ha⟩ := hmod.exists_elt_scalar I e hX hK θ
  have haM : a ∈ M := e.CN_le_M haN
  have hainv : a⁻¹ ∈ hc.CN t := (hc.CN t).inv_mem haN
  have hQ1 : a⁻¹ * h ∈ Q := by
    refine hc.hyp.centralizer_Qt _ (M.mul_mem (M.inv_mem haM) hhM) fun x hx => ?_
    have hax : ⁅a, x⁆ ∈ Vt M (LB M Q B) B Z t := e.comm_mem_V I.h34 haN hx
    have hhx : ⁅h, x⁆ ∈ Vt M (LB M Q B) B Z t := hi x hx
    have hax' : ⁅a, x⁆⁻¹ ∈ Vt M (LB M Q B) B Z t := (Vt M (LB M Q B) B Z t).inv_mem hax
    have t1 := vecOf_conj_triv (ψ := ψ) (a := a⁻¹) hhx ((Ctx.mem_CN.mp hainv).2 _ hhx)
    have t2 := vecOf_conj_triv (ψ := ψ) (a := a⁻¹) hax' ((Ctx.mem_CN.mp hainv).2 _ hax')
    rw [inv_inv] at t1 t2
    have e1 : ⁅a⁻¹ * h, x⁆ = (a⁻¹ * ⁅h, x⁆ * a) * (a⁻¹ * ⁅a, x⁆⁻¹ * a) := by
      simp only [commutatorElement_def]; group
    have hmem : ⁅a⁻¹ * h, x⁆ ∈ Vt M (LB M Q B) B Z t := by
      rw [e1]
      exact (Vt M (LB M Q B) B Z t).mul_mem t1.1 t2.1
    rw [← vecOf_eq_zero_iff ψ hmem, e1, vecOf_mul ψ t1.1 t2.1, t1.2, t2.2, vecOf_inv ψ hax]
    have h3 := hθ x hx
    have h4 := ha x hx
    show vecOf ψ ⁅h, x⁆ + -vecOf ψ ⁅a, x⁆ = 0
    have h5 : vecOf ψ ⁅h, x⁆ = θ • vecOf ψ ⁅x, t⁆ := h3
    rw [h5, h4]
    exact add_neg_cancel _
  have : h = a * (a⁻¹ * h) := by group
  rw [this]
  exact (hc.CN t).mul_mem haN (hQN hQ1)


theorem Env.CN_le_H0 (I : Inputs) (e : Env hc n t m X) : hc.CN t ≤ H0 M Z := by
  intro a ha
  have h1 : a ∈ LB M Q B := e.N_le_LB I ha
  have h2 : a ∈ Lgen M (LB M Q B) := by
    have : LB M Q B ≤ Lgen M (LB M Q B) :=
      le_iSup₂_of_le (1 : G) M.one_mem (by rw [conjSubgroup_one])
    exact this h1
  exact ActionData.Lgen_le_H0 hc h2

theorem OmegaModel.card_le_of_lambda (I : Inputs) (e : Env hc n t m X)
    (hX : AddCommutantScalar X') (hK : Nat.card K = Nat.card Z)
    (hmod : OmegaModel hc t Q' E φ ψ u) (C : Subgroup G)
    (hC : ∀ h, h ∈ C ↔ h ∈ H0 M Z ∧ ∀ x ∈ X, ⁅h, x⁆ ∈ Q) :
    Nat.card ↥(C ⊓ Subgroup.normalizer ((Vt M (LB M Q B) B Z t : Subgroup G) : Set G)) ≤
      Nat.card ↥(hc.CN t) * (Nat.card Z - 1) := by
  classical
  have ht := e.hs.toSec5.mem
  have hVR := hc.Rt_normalizes_Vt ht
  set V := Vt M (LB M Q B) B Z t with hVdef
  set 𝒩 : Subgroup G := C ⊓ Subgroup.normalizer (V : Set G) with h𝒩
  have hmemN : ∀ h ∈ 𝒩, h ∈ M ∧ (∀ v ∈ V, h * v * h⁻¹ ∈ V) ∧ (∀ x ∈ X, ⁅h, x⁆ ∈ Q) ∧
      (∀ z ∈ Z, h * z * h⁻¹ = z) := by
    intro h hh
    obtain ⟨hhC, hhN⟩ := hh
    obtain ⟨hH0, hhX⟩ := (hC h).mp hhC
    refine ⟨hH0.1, fun v hv => ?_, hhX, fun z hz => ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hhN v).mp hv
    · have := Subgroup.mem_centralizer_iff.mp hH0.2 z hz
      rw [mul_inv_eq_iff_eq_mul]
      exact this.symm
  have hu : ∀ c c' : K, c • u = c' • u → c = c' := fun c c' h => smul_left_injective K hmod.u0 h
  obtain ⟨v₀, hv₀V, hv₀⟩ : ∃ v ∈ V, vecOf ψ v = u := by
    obtain ⟨x, hxQ, hx⟩ := OmegaModel.exists_chiVec (ψ := ψ) I e u
    exact ⟨⁅x, t⁆, (e.chi I.h34).1 x hxQ, hx⟩
  choose lam hlam using fun h : ↥𝒩 =>
    hmod.exists_lambda e hX (hmemN h.1 h.2).1 (hmemN h.1 h.2).2.1 (hmemN h.1 h.2).2.2.1
  have hmul : ∀ h h' : ↥𝒩, lam (h * h') = lam h * lam h' := by
    intro h h'
    apply hu
    rw [← hv₀]
    calc lam (h * h') • vecOf ψ v₀
        = vecOf ψ (((h * h' : ↥𝒩) : G) * v₀ * ((h * h' : ↥𝒩) : G)⁻¹) :=
          (hlam (h * h') v₀ hv₀V).symm
      _ = vecOf ψ ((h : G) * ((h' : G) * v₀ * (h' : G)⁻¹) * (h : G)⁻¹) := by
          congr 1
          simp only [Subgroup.coe_mul]
          group
      _ = lam h • vecOf ψ ((h' : G) * v₀ * (h' : G)⁻¹) :=
          hlam h _ ((hmemN h'.1 h'.2).2.1 v₀ hv₀V)
      _ = lam h • (lam h' • vecOf ψ v₀) := by rw [hlam h' v₀ hv₀V]
      _ = (lam h * lam h') • vecOf ψ v₀ := (mul_smul _ _ _).symm
  have hone : lam 1 = 1 := by
    apply hu
    rw [← hv₀, one_smul, ← hlam 1 v₀ hv₀V]
    simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one]
  let lamHom : ↥𝒩 →* Kˣ := MonoidHom.toHomUnits
    { toFun := lam, map_one' := hone, map_mul' := hmul }
  have hNle : hc.CN t ≤ 𝒩 := by
    intro a ha
    have haR : a ∈ Rt M (LB M Q B) t := (Ctx.mem_CN.mp ha).1
    refine ⟨(hC a).mpr ⟨e.CN_le_H0 I ha, fun x hx => e.hcen a ha x hx⟩, ?_⟩
    exact hVR haR
  have hker : lamHom.ker = (hc.CN t).subgroupOf 𝒩 := by
    ext h
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Units.ext_iff]
    show lam h = 1 ↔ (h : G) ∈ hc.CN t
    constructor
    · intro h1
      obtain ⟨hhM, hhV, hhX, hhZ⟩ := hmemN h.1 h.2
      refine hmod.mem_CN_of_trivial I e hX hK hhM hhZ hhX fun v hv => ?_
      have h2 := hlam h v hv
      rw [h1, one_smul] at h2
      have hv' : (h : G) * v * (h : G)⁻¹ ∈ V := hhV v hv
      have h3 := (vecOf_eq_iff ψ hv' hv).mp h2
      have e1 : ⁅(h : G), v⁆ = (h : G) * v * (h : G)⁻¹ * v⁻¹ := rfl
      rw [e1]
      exact h3
    · intro hN
      have h1 := hlam h v₀ hv₀V
      have h2 := vecOf_conj_triv (ψ := ψ) hv₀V ((Ctx.mem_CN.mp hN).2 v₀ hv₀V)
      rw [h2.2, hv₀] at h1
      exact hu _ _ (by rw [one_smul]; exact h1.symm)
  have hcardker : Nat.card lamHom.ker = Nat.card ↥(hc.CN t) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNle).toEquiv
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup lamHom.ker
  have h2 : Nat.card (↥𝒩 ⧸ lamHom.ker) = Nat.card lamHom.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange lamHom).toEquiv
  have h3 : Nat.card lamHom.range ≤ Nat.card Kˣ := Subgroup.card_le_card_group _
  have h4 : Nat.card Kˣ = Nat.card K - 1 := Nat.card_units K
  rw [h2, hcardker] at h1
  rw [h1, mul_comm]
  have h5 : Nat.card lamHom.range ≤ Nat.card Z - 1 := by rw [← hK, ← h4]; exact h3
  exact Nat.mul_le_mul_left _ h5

end Lam

end HS6

end CFSG.RankThree.GF2n.Stroth80
