module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec65NNorm
public import CFSG.RankThree.GF2n.Stroth80.HeringSec65NLam
public import CFSG.RankThree.GF2n.Stroth80.HeringSec64DirectIrr
public import CFSG.RankThree.GF2n.Stroth80.HeringSec64DirectRep

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.GF2n
open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement Matrix

namespace HS6

section Conj

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {n : ℕ} {t : G} {m : ℕ} {X : Subgroup G}

theorem Env.exists_conj_ne (I : Inputs) (e : Env hc n t m X) :
    ∃ g ∈ M, conjSubgroup g (hc.CN t) ≠ hc.CN t := by
  by_contra hcon
  push Not at hcon
  have ht := e.hs.toSec5.mem
  have hV : ∀ g ∈ M, conjSubgroup g (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t :=
    fun g hg => e.conj_Vt_eq I hg (hcon g hg)
  have hQV : Q ≤ Vt M (LB M Q B) B Z t := by
    have hgen : Q = ⨆ (g : G) (_ : g ∈ M), conjSubgroup g B := e.hs.toSec5.gen
    refine hgen.le.trans (iSup₂_le fun g hg => ?_)
    calc conjSubgroup g B ≤ conjSubgroup g (Vt M (LB M Q B) B Z t) :=
          Subgroup.map_mono (hc.B_le_Vt ht)
      _ = Vt M (LB M Q B) B Z t := hV g hg
  have hEq : Vt M (LB M Q B) B Z t = Q := le_antisymm (hc.Vt_le_Q t) hQV
  have hcard : Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card ↥Q := by rw [hEq]
  rw [e.card_Vt, e.hs.toSec5.width, e.hn] at hcard
  have hq4 := hc.hyp.q4
  have := Nat.pow_right_injective (by omega : 2 ≤ Nat.card Z) hcard
  have hm := e.hm
  omega

theorem mem_conjSubgroup_of_mem {T : Subgroup G} {x y : G} (hy : y ∈ T) :
    x * y * x⁻¹ ∈ conjSubgroup x T :=
  mem_conjSubgroup.mpr (by rw [show x⁻¹ * (x * y * x⁻¹) * x = y by group]; exact hy)

theorem Env.conj_V_inv (I : Inputs) (e : Env hc n t m X)
    (hD : ∀ g ∈ M, ∀ a ∈ hc.CN t, ∀ x ∈ X, ⁅x, g * a * g⁻¹⁆ ∈ Q) {g : G} (hg : g ∈ M) :
    ∀ x ∈ X, ∀ y ∈ conjSubgroup g (Vt M (LB M Q B) B Z t),
      x * y * x⁻¹ ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
  intro x hx y hy
  obtain ⟨a, ha, haQ⟩ := e.exists_mem_CN_not_mem_Q
  have haM : a ∈ M := e.CN_le_M ha
  have hxM : x ∈ M := e.X_le_M hx
  set c : G := g * a * g⁻¹ with hcdef
  have hcM : c ∈ M := M.mul_mem (M.mul_mem hg haM) (M.inv_mem hg)
  have hQ1c : Q1 hc c = conjSubgroup g (Vt M (LB M Q B) B Z t) := by
    rw [hcdef, Q1_conj hc hg haM, e.Q1_eq_V I ha haQ]
  have hxcQ : ⁅x, c⁆ ∈ Q := hD g hg a ha x hx
  have hcc : c⁻¹ * (x * c * x⁻¹) ∈ Q := by
    have h1 := (hc.conj_mem_Q_of_mem_M (M.inv_mem hcM)).1 _ hxcQ
    have e1 : c⁻¹ * ⁅x, c⁆ * c⁻¹⁻¹ = c⁻¹ * (x * c * x⁻¹) := by
      simp only [commutatorElement_def]; group
    rwa [e1] at h1
  have h1 : Q1 hc (x * c * x⁻¹) = Q1 hc c :=
    Q1_congr hc hcM (M.mul_mem (M.mul_mem hxM hcM) (M.inv_mem hxM)) hcc
  have h2 : Q1 hc (x * c * x⁻¹) = conjSubgroup x (Q1 hc c) := Q1_conj hc hxM hcM
  rw [← hQ1c] at hy ⊢
  rw [← h1, h2]
  exact mem_conjSubgroup_of_mem hy

theorem Env.comm_conj_CN_mem_V' (I : Inputs) (e : Env hc n t m X) {g : G} (hg : g ∈ M) {a : G}
    (ha : a ∈ hc.CN t) {x : G} (hx : x ∈ Q) :
    ⁅g * a * g⁻¹, x⁆ ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
  have hy : g⁻¹ * x * g ∈ Q := (hc.conj_mem_Q_of_mem_M hg).2 x hx
  have h1 := e.comm_mem_V I.h34 ha hy
  have e1 : ⁅g * a * g⁻¹, x⁆ = g * ⁅a, g⁻¹ * x * g⁆ * g⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e1]
  exact mem_conjSubgroup_of_mem h1

theorem Env.comm_conj_CN_mem_Z (e : Env hc n t m X) {g : G} (hg : g ∈ M) {a : G}
    (ha : a ∈ hc.CN t) {y : G} (hy : y ∈ conjSubgroup g (Vt M (LB M Q B) B Z t)) :
    ⁅g * a * g⁻¹, y⁆ ∈ Z := by
  have hv : g⁻¹ * y * g ∈ Vt M (LB M Q B) B Z t := mem_conjSubgroup.mp hy
  have h1 := (Ctx.mem_CN.mp ha).2 _ hv
  have e1 : ⁅g * a * g⁻¹, y⁆ = g * ⁅a, g⁻¹ * y * g⁆ * g⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e1]
  exact conj_Z_mem hc hg h1

end Conj

section Inter

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {n : ℕ} {t : G} {m : ℕ} {X : Subgroup G}
  {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K] [CharP K 2]
  {Q' : QuadraticForm K (ι → K)} {X' : Subgroup (GL ι K)} {E : ElemMatrixIso Q' X'}
  {φ : ↥(Rt M (LB M Q B) t) →* GL ι K}
  [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
  {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
    Multiplicative (ι → K)} {u : ι → K}

theorem OmegaModel.inf_conj_V_le_Z (I : Inputs) (e : Env hc n t m X)
    (h63b : StronglyClosedMod M (hc.CN t) (LB M Q B)) (hg : OmegaGeom Q' m)
    (hmod : OmegaModel hc t Q' E φ ψ u)
    (hD : ∀ g ∈ M, ∀ a ∈ hc.CN t, ∀ x ∈ X, ⁅x, g * a * g⁻¹⁆ ∈ Q) {g : G} (hgM : g ∈ M)
    (hne : conjSubgroup g (hc.CN t) ≠ hc.CN t) :
    ∀ v ∈ Vt M (LB M Q B) B Z t, v ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) → v ∈ Z := by
  classical
  have ht := e.hs.toSec5.mem
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hVR := hc.Rt_normalizes_Vt ht
  have hZV' : Z ≤ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
    intro z hz
    rw [← hc.conj_Z_eq hgM] at hz
    exact Subgroup.map_mono hZV hz
  let U : AddSubgroup (ι → K) :=
    { carrier := {w | ∃ v ∈ Vt M (LB M Q B) B Z t,
        v ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) ∧ vecOf ψ v = w}
      add_mem' := by
        rintro _ _ ⟨v₁, hv₁, hv₁', rfl⟩ ⟨v₂, hv₂, hv₂', rfl⟩
        exact ⟨v₁ * v₂, Subgroup.mul_mem _ hv₁ hv₂, Subgroup.mul_mem _ hv₁' hv₂',
          vecOf_mul ψ hv₁ hv₂⟩
      zero_mem' := ⟨1, Subgroup.one_mem _, Subgroup.one_mem _,
        vecOf_of_mem_Z ψ (Subgroup.one_mem Z) hZV⟩
      neg_mem' := by
        rintro _ ⟨v, hv, hv', rfl⟩
        exact ⟨v⁻¹, Subgroup.inv_mem _ hv, Subgroup.inv_mem _ hv', vecOf_inv ψ hv⟩ }
  have hU : ∀ A ∈ X', ∀ w ∈ U, ((A : GL ι K) : Matrix ι ι K) *ᵥ w ∈ U := by
    intro A hA w hw
    obtain ⟨v, hv, hv', rfl⟩ := hw
    obtain ⟨x, hxX, hxR, rfl⟩ := hmod.exists_mem_X' e hA
    refine ⟨x * v * x⁻¹, (Subgroup.mem_normalizer_iff.mp (hVR hxR) v).mp hv,
      e.conj_V_inv I hD hgM x hxX v hv', ?_⟩
    exact vecOf_conj ψ φ hmod.equi hVR ⟨x, hxR⟩ hv
  obtain ⟨P, P', hPP⟩ := hg.two
  have hP : ∃ P : Fin 2 → HypPair Q', ∀ i j, i ≠ j → (P i).Orth (P j) := by
    refine ⟨![P, P'], fun i j hij => ?_⟩
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hPP
    · exact hPP.symm
    · exact absurd rfl hij
  rcases addSubgroup_eq_bot_or_top_of_elemMatrixIso E hg.nondeg hP U hU with hbot | htop
  · intro v hv hv'
    have : vecOf ψ v ∈ U := ⟨v, hv, hv', rfl⟩
    rw [hbot, AddSubgroup.mem_bot] at this
    exact (vecOf_eq_zero_iff ψ hv).mp this
  · exfalso
    have hVV' : Vt M (LB M Q B) B Z t ≤ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
      intro v hv
      have hvU : vecOf ψ v ∈ U := by rw [htop]; exact AddSubgroup.mem_top _
      obtain ⟨v₁, hv₁, hv₁', hvv⟩ := hvU
      have hz : v * v₁⁻¹ ∈ Z := (vecOf_eq_iff ψ hv hv₁).mp hvv.symm
      have : v = (v * v₁⁻¹) * v₁ := by group
      rw [this]
      exact Subgroup.mul_mem _ (hZV' hz) hv₁'
    apply hne
    refine e.conj_CN_eq_of_B_le I h63b hgM (Subgroup.one_mem _) ?_
    rw [conjSubgroup_one]
    exact (hc.B_le_Vt ht).trans hVV'

end Inter

section Chart

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {n : ℕ} {t : G} {m : ℕ} {X : Subgroup G}
  {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K] [CharP K 2]
  {Q' : QuadraticForm K (ι → K)} {X' : Subgroup (GL ι K)} {E : ElemMatrixIso Q' X'}
  {φ : ↥(Rt M (LB M Q B) t) →* GL ι K}
  [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
  {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
    Multiplicative (ι → K)} {u : ι → K}

theorem OmegaModel.exists_chart (I : Inputs) (e : Env hc n t m X)
    (h63b : StronglyClosedMod M (hc.CN t) (LB M Q B)) (hg : OmegaGeom Q' m)
    (hK : Nat.card K = Nat.card Z) (hX : AddCommutantScalar X')
    (hmod : OmegaModel hc t Q' E φ ψ u)
    (hD : ∀ g ∈ M, ∀ a ∈ hc.CN t, ∀ x ∈ X, ⁅x, g * a * g⁻¹⁆ ∈ Q) {g : G} (hgM : g ∈ M)
    (hne : conjSubgroup g (hc.CN t) ≠ hc.CN t) :
    ∃ (Φ : G → (ι → K) × (ι → K)) (a : G → Matrix ι ι K),
      IsChart Q Z X Φ a ∧
      (∀ x ∈ Q, ((Φ x).2 = 0 ↔ x ∈ Vt M (LB M Q B) B Z t)) ∧
      (∀ x ∈ Q, ((Φ x).1 = 0 ↔ x ∈ conjSubgroup g (Vt M (LB M Q B) B Z t))) := by
  classical
  have ht := e.hs.toSec5.mem
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hVR := hc.Rt_normalizes_Vt ht
  have hZQ : Z ≤ Q := hc.hyp.Z_normal.1
  have hQM : ∀ r ∈ Rt M (LB M Q B) t, ∀ x ∈ Q, r * x * r⁻¹ ∈ Q := fun r hr x hx =>
    (hc.conj_mem_Q_of_mem_M (hc.Rt_le_M t hr)).1 x hx
  have hχ := e.chi I.h34
  have hinter := hmod.inf_conj_V_le_Z I e h63b hg hD hgM hne
  have hV'Q : ∀ y ∈ conjSubgroup g (Vt M (LB M Q B) B Z t), y ∈ Q := by
    intro y hy
    have h1 := hVQ (mem_conjSubgroup.mp hy)
    have := (hc.conj_mem_Q_of_mem_M hgM).1 _ h1
    rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at this
  have hZV' : Z ≤ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
    intro z hz
    rw [← hc.conj_Z_eq hgM] at hz
    exact Subgroup.map_mono hZV hz
  let cv : G → ι → K := fun x => vecOf ψ ⁅x, t⁆
  have hcv_eq : ∀ (x : G) (hx : x ∈ Q), cv x = chiVec hχ ψ ⟨x, hx⟩ := fun x hx =>
    vecOf_of_mem ψ (hχ.1 x hx)
  have hcv_mul : ∀ x ∈ Q, ∀ y ∈ Q, cv (x * y) = cv x + cv y := by
    intro x hx y hy
    rw [hcv_eq _ (Q.mul_mem hx hy), hcv_eq x hx, hcv_eq y hy]
    exact chiVec_mul hχ ψ ⟨x, hx⟩ ⟨y, hy⟩
  have hcv_zero : ∀ x ∈ Q, cv x = 0 ↔ x ∈ Vt M (LB M Q B) B Z t := by
    intro x hx
    rw [hcv_eq x hx]
    exact chiVec_eq_zero_iff hχ ψ ⟨x, hx⟩
  have hcv_conj : ∀ (r : G) (hr : r ∈ Rt M (LB M Q B) t), ∀ y ∈ Q,
      cv (r * y * r⁻¹) = (φ ⟨r, hr⟩ : Matrix ι ι K) *ᵥ cv y := by
    intro r hr y hy
    rw [hcv_eq _ (hQM r hr y hy), hcv_eq y hy]
    exact chiVec_conj hχ ψ φ hmod.equi hVR hQM ⟨r, hr⟩ ⟨y, hy⟩
  have hcv_Z : ∀ z ∈ Z, cv z = 0 := fun z hz => (hcv_zero z (hZQ hz)).mpr (hZV hz)
  obtain ⟨a₁, ha₁, ha₁Q⟩ := e.exists_mem_CN_not_mem_Q
  have ha₁M : a₁ ∈ M := e.CN_le_M ha₁
  set c : G := g * a₁ * g⁻¹ with hcdef
  have hcM : c ∈ M := M.mul_mem (M.mul_mem hgM ha₁M) (M.inv_mem hgM)
  have hQ1c : Q1 hc c = conjSubgroup g (Vt M (LB M Q B) B Z t) := by
    rw [hcdef, Q1_conj hc hgM ha₁M, e.Q1_eq_V I ha₁ ha₁Q]
  have hmemQ1 : ∀ x ∈ Q, x ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) ↔ ⁅c, x⁆ ∈ Z := by
    intro x hx
    rw [← hQ1c, hc.mem_Q1_iff hcM]
    exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
  have hcxV' : ∀ x ∈ Q, ⁅c, x⁆ ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
    intro x hx
    have hy : g⁻¹ * x * g ∈ Q := (hc.conj_mem_Q_of_mem_M hgM).2 x hx
    have h1 := e.comm_mem_V I.h34 ha₁ hy
    have e1 : ⁅c, x⁆ = g * ⁅a₁, g⁻¹ * x * g⁆ * g⁻¹ := by
      simp only [commutatorElement_def, hcdef]; group
    rw [e1]
    exact mem_conjSubgroup_of_mem h1
  have hxcV' : ∀ x ∈ Q, ⁅x, c⁆ ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
    intro x hx
    have := Subgroup.inv_mem _ (hcxV' x hx)
    rwa [commutatorElement_inv] at this
  have hxcQ : ∀ x ∈ Q, ⁅x, c⁆ ∈ Q := fun x hx => hV'Q _ (hxcV' x hx)
  have hfst : ∀ x ∈ Q, cv ⁅x, c⁆ = 0 ↔ x ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
    intro x hx
    rw [hmemQ1 x hx]
    constructor
    · intro h0
      have hV : ⁅x, c⁆ ∈ Vt M (LB M Q B) B Z t := (hcv_zero _ (hxcQ x hx)).mp h0
      have hZ : ⁅x, c⁆ ∈ Z := hinter _ hV (hxcV' x hx)
      have := Z.inv_mem hZ
      rwa [commutatorElement_inv] at this
    · intro h0
      have : ⁅x, c⁆ ∈ Z := by
        have := Z.inv_mem h0
        rwa [commutatorElement_inv] at this
      exact hcv_Z _ this
  have hfst_add : ∀ x ∈ Q, ∀ y ∈ Q, cv ⁅x * y, c⁆ = cv ⁅x, c⁆ + cv ⁅y, c⁆ := by
    intro x hx y hy
    have hyc := hxcQ y hy
    have hz : ⁅x, ⁅y, c⁆⁆ ∈ Z := comm_mem_Z_of_Q hc hx hyc
    have e1 : ⁅x * y, c⁆ = ⁅x, ⁅y, c⁆⁆ * ⁅y, c⁆ * ⁅x, c⁆ := by
      simp only [commutatorElement_def]; group
    rw [e1, hcv_mul _ (Q.mul_mem (hZQ hz) hyc) _ (hxcQ x hx), hcv_mul _ (hZQ hz) _ hyc,
      hcv_Z _ hz, zero_add, add_comm]
  have hfst_conj : ∀ (x₀ : G) (hx₀ : x₀ ∈ X) (y : G), y ∈ Q →
      cv ⁅x₀ * y * x₀⁻¹, c⁆ = (φ ⟨x₀, e.hXR hx₀⟩ : Matrix ι ι K) *ᵥ cv ⁅y, c⁆ := by
    intro x₀ hx₀ y hy
    have hx₀R : x₀ ∈ Rt M (LB M Q B) t := e.hXR hx₀
    have hq : x₀⁻¹ * c * x₀ * c⁻¹ ∈ Q := by
      have := hD g hgM a₁ ha₁ x₀⁻¹ (X.inv_mem hx₀)
      simpa [commutatorElement_def, hcdef, mul_assoc] using this
    set q : G := x₀⁻¹ * c * x₀ * c⁻¹ with hqdef
    have hc' : x₀⁻¹ * c * x₀ = q * c := by rw [hqdef]; group
    have e1 : ⁅x₀ * y * x₀⁻¹, c⁆ = x₀ * ⁅y, q * c⁆ * x₀⁻¹ := by
      have : ⁅y, x₀⁻¹ * c * x₀⁆ = ⁅y, q * c⁆ := by rw [hc']
      rw [← this]
      simp only [commutatorElement_def]; group
    have hyc := hxcQ y hy
    have e2 : ⁅y, q * c⁆ = ⁅y, q⁆ * (q * ⁅y, c⁆ * q⁻¹) := by
      simp only [commutatorElement_def]; group
    have hyq : ⁅y, q⁆ ∈ Z := comm_mem_Z_of_Q hc hy hq
    have hqw : q * ⁅y, c⁆ * q⁻¹ = ⁅q, ⁅y, c⁆⁆ * ⁅y, c⁆ := by
      simp only [commutatorElement_def]; group
    have hqwZ : ⁅q, ⁅y, c⁆⁆ ∈ Z := comm_mem_Z_of_Q hc hq hyc
    have hcvyqc : cv ⁅y, q * c⁆ = cv ⁅y, c⁆ := by
      rw [e2, hqw, hcv_mul _ (hZQ hyq) _ (Q.mul_mem (hZQ hqwZ) hyc),
        hcv_mul _ (hZQ hqwZ) _ hyc, hcv_Z _ hyq, hcv_Z _ hqwZ, zero_add, zero_add]
    have hyqcQ : ⁅y, q * c⁆ ∈ Q := by
      rw [e2, hqw]
      exact Q.mul_mem (hZQ hyq) (Q.mul_mem (hZQ hqwZ) hyc)
    rw [e1, hcv_conj x₀ hx₀R _ hyqcQ, hcvyqc]
  let a : G → Matrix ι ι K := fun x =>
    if hx : x ∈ Rt M (LB M Q B) t then ((φ ⟨x, hx⟩ : GL ι K) : Matrix ι ι K) else 1
  have ha : ∀ (x : G) (hx : x ∈ Rt M (LB M Q B) t),
      a x = ((φ ⟨x, hx⟩ : GL ι K) : Matrix ι ι K) := fun x hx => dif_pos hx
  let Φ : G → (ι → K) × (ι → K) := fun x => (cv ⁅x, c⁆, cv x)
  have hzero : ∀ x ∈ Q, Φ x = 0 ↔ x ∈ Z := by
    intro x hx
    constructor
    · intro h0
      have h1 : cv ⁅x, c⁆ = 0 := congrArg Prod.fst h0
      have h2 : cv x = 0 := congrArg Prod.snd h0
      exact hinter x ((hcv_zero x hx).mp h2) ((hfst x hx).mp h1)
    · intro hxZ
      exact Prod.ext ((hfst x hx).mpr (hZV' hxZ)) (hcv_Z x hxZ)
  have hadd : ∀ x ∈ Q, ∀ y ∈ Q, Φ (x * y) = Φ x + Φ y := fun x hx y hy =>
    Prod.ext (hfst_add x hx y hy) (hcv_mul x hx y hy)
  have hsurj : ∀ w, ∃ x ∈ Q, Φ x = w := by
    refine surj_of_card Φ hZQ hadd hzero ?_
    have hdim : Fintype.card ι = 2 * m := by
      rw [← Module.finrank_fintype_fun_eq_card (R := K)]
      exact hg.dim
    rw [e.hs.toSec5.width, e.hn, Nat.card_prod, Nat.card_fun, Nat.card_eq_fintype_card (α := ι),
      hdim, hK]
    ring
  have hequi : ∀ x ∈ X, ∀ y ∈ Q, Φ (x * y * x⁻¹) = diagM (a x) (Φ y) := by
    intro x hx y hy
    have hxR := e.hXR hx
    refine Prod.ext ?_ ?_
    · show cv ⁅x * y * x⁻¹, c⁆ = a x *ᵥ cv ⁅y, c⁆
      rw [hfst_conj x hx y hy, ha x hxR]
    · show cv (x * y * x⁻¹) = a x *ᵥ cv y
      rw [hcv_conj x hxR y hy, ha x hxR]
  have hschur : ∀ f : (ι → K) →+ (ι → K), (∀ x ∈ X, ∀ v, f (a x *ᵥ v) = a x *ᵥ f v) →
      ∃ c : K, ∀ v, f v = c • v := by
    intro f hf
    refine hX f (fun A hA v => ?_)
    obtain ⟨x, hxX, hxR, rfl⟩ := hmod.exists_mem_X' e hA
    have := hf x hxX v
    rwa [ha x hxR] at this
  exact ⟨Φ, a, ⟨fun x hx y hy => comm_mem_Z_of_Q hc hx hy, hZQ, hadd, hzero, hsurj,
    fun x hx y hy => (hc.conj_mem_Q_of_mem_M (e.X_le_M hx)).1 y hy, hequi, hschur⟩,
    fun x hx => hcv_zero x hx, fun x hx => hfst x hx⟩

end Chart

end HS6

end CFSG.RankThree.GF2n.Stroth80
