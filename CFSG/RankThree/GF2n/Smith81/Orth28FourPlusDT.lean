module

public import CFSG.RankThree.GF2n.Smith81.Orth28FourPlusAct
public import CFSG.RankThree.GF2n.Smith81.Orth28FourPlusPure
public import CFSG.RankThree.GF2n.Smith81.Orth28DT

public section

namespace CFSG.RankThree.GF2n.Smith81.FourPlus

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.RankThree.GF2n.Stroth80 QuadraticMap
open CFSG.RankThree.GF2n.Smith81.OrthTN CFSG.RankThree.GF2n.Smith81.D2
  CFSG.RankThree.GF2n.Smith81.OrthDT
open scoped commutatorElement Matrix MatrixGroups

section URange

variable {K : Type} [Field K] [CharP K 2] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem uRange_eq_span {qU : QuadraticForm K (ι → K)} (hnd : qU.polarBilin.Nondegenerate)
    {o : (ι → K) ≃ₗ[K] (ι → K)} (hO : o ∈ TauCeti.QuadraticMap.orthogonalGroup qU)
    (hoo : o * o = 1) (hev : Even (Module.finrank K (OrthogonalInvolutions.commSpace o)))
    (hdim : Module.finrank K (ι → K) = 4) {u : ι → K} (hu0 : u ≠ 0) (hqu : qU u = 0)
    (hou : o u = u) : uRange qU o u = Submodule.span K {u} := by
  have hodd := odd_finrank_commSpace_add_uRange hnd hO hoo hu0 hqu hou
  have hsum := OrthogonalInvolutions.finrank_commSpace_add_finrank_fixSpace o
  have hle : OrthogonalInvolutions.commSpace o ≤ OrthogonalInvolutions.fixSpace o :=
    OrthogonalInvolutions.commSpace_le_fixSpace hoo
  have hle' := Submodule.finrank_mono hle
  have huF : u ∈ OrthogonalInvolutions.fixSpace o := OrthogonalInvolutions.mem_fixSpace.mpr hou
  have hmapC : (uPerp qU u).map ((o : (ι → K) →ₗ[K] (ι → K)) - 1) ≤
      OrthogonalInvolutions.commSpace o := LinearMap.map_le_range
  have hspan : Submodule.span K {u} ≤ uRange qU o u := le_sup_right
  have hRF : uRange qU o u ≤ OrthogonalInvolutions.fixSpace o :=
    sup_le (hmapC.trans hle) ((Submodule.span_singleton_le_iff_mem _ _).mpr huF)
  have hfs : Module.finrank K (Submodule.span K {u}) = 1 := finrank_span_singleton hu0
  have hR1 := Submodule.finrank_mono hspan
  have hR2 := Submodule.finrank_mono hRF
  by_cases hr0 : Module.finrank K (OrthogonalInvolutions.commSpace o) = 0
  · have hbot : OrthogonalInvolutions.commSpace o = ⊥ := Submodule.finrank_eq_zero.mp hr0
    rw [hbot] at hmapC
    have : (uPerp qU u).map ((o : (ι → K) →ₗ[K] (ι → K)) - 1) = ⊥ := le_bot_iff.mp hmapC
    unfold uRange
    rw [this, bot_sup_eq]
  · refine (Submodule.eq_of_le_of_finrank_eq hspan ?_).symm
    rw [hfs]
    rw [Nat.even_iff] at hev
    rw [Nat.odd_iff] at hodd
    omega

end URange

section Polar

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem polar_eq_D2 {qU : QuadraticForm K (ι → K)} {μ : (ι → K) ≃ₗ[K] Mat2 K}
    (hμ : ∀ v, (μ v).det = qU v) (a b : ι → K) :
    QuadraticMap.polar qU a b = D2.polar (μ a) (μ b) := by
  rw [QuadraticMap.polar, ← hμ, ← hμ, ← hμ, map_add, D2.det_add]
  ring

theorem polar_mul_self (A X : Mat2 K) :
    D2.polar (A * X) X = (A 0 0 + A 1 1) * X.det := by
  simp only [D2.polar, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
  ring

theorem polar_self_mul (X A : Mat2 K) :
    D2.polar (X * A) X = (A 0 0 + A 1 1) * X.det := by
  simp only [D2.polar, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
  ring

theorem exists_mem_D {qU : QuadraticForm K (ι → K)} {μ : (ι → K) ≃ₗ[K] Mat2 K}
    (hμ : ∀ v, (μ v).det = qU v) (c₁ c₂ : K) (u : ι → K) (hqu : qU u = 0) (i : Fin 3)
    (A : Mat2 K) :
    ∃ (w : ι → K) (s t : K), QuadraticMap.polar qU w u = 0 ∧
      thetaC μ (c₁ • w + s • u, c₂ • w + t • u) = actMap i A (thetaC μ (c₁ • u, c₂ • u)) := by
  have hdet : (μ u).det = 0 := by rw [hμ, hqu]
  fin_cases i
  · refine ⟨0, A 0 0 * c₁ + A 0 1 * c₂, A 1 0 * c₁ + A 1 1 * c₂, ?_, ?_⟩
    · simp
    · show _ = actMap 0 A _
      rw [← thetaC_orthTensor_zero]
      congr 1
      refine Prod.ext ?_ ?_ <;> simp [orthTensor, add_smul, smul_smul]
  · refine ⟨swL μ A 1 u, 0, 0, ?_, ?_⟩
    · rw [polar_eq_D2 hμ, mu_swL, Matrix.transpose_one, Matrix.mul_one, polar_mul_self, hdet,
        mul_zero]
    · show _ = actMap 1 A _
      rw [← thetaC_orthTensor_one, orthTensor_one_linear]
      simp
  · refine ⟨swL μ 1 A u, 0, 0, ?_, ?_⟩
    · rw [polar_eq_D2 hμ, mu_swL, Matrix.one_mul, polar_self_mul, hdet, mul_zero]
    · show _ = actMap 2 A _
      rw [← thetaC_orthTensor_two, orthTensor_one_linear]
      simp

end Polar

section CommZA

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem comm_mem_ZA (F : Data M Q Z B) (h52 : Smith52ActStatement) {A : Subgroup G}
    (hcA : Ctx M Q Z A) {y : G} (hyL : y ∈ Lgen M (LB M Q B)) (hy2 : y * y = 1)
    (hyA : ∀ a ∈ A, y * a * y⁻¹ = a) : ∀ s ∈ Q ⊓ QB A, ⁅s, y⁆ ∈ Z ⊔ A := by
  classical
  have H := hcA.hyp
  have hyM : y ∈ M := Lgen_le F.hc.ctx.LB_le_M hyL
  obtain ⟨g, o, hact, hgg, hoo, hiso, hev⟩ := lgen_involution_normalized F.hc F.noA2 F.C hyL hy2
  obtain ⟨c₁, c₂, u, a₀, hc12, hu0, hqu, ha₀A, ha₀1, hpa⟩ := exists_root_data F.C hcA
  set c : Fin 2 → F.C.K := ![c₁, c₂] with hcdef
  have hc0 : c ≠ 0 := by
    intro h0
    rcases hc12 with h1 | h1
    · exact h1 (by simpa [hcdef] using congrFun h0 0)
    · exact h1 (by simpa [hcdef] using congrFun h0 1)
  have hpa' : F.C.φ (F.C.M₀.π a₀) = (c 0 • u, c 1 • u) := by rw [hpa]; simp [hcdef]
  have ha₀Q : a₀ ∈ Q := hcA.le ha₀A
  have hfix : orthTensor g o (c 0 • u, c 1 • u) = (c 0 • u, c 1 • u) := by
    have h1 := hact a₀ ha₀Q
    rw [hyA a₀ ha₀A, hpa'] at h1
    exact h1.symm
  obtain ⟨hgc, hou⟩ := orthTensor_fix_pure hgg hc0 hu0 hfix
  have hoO : o ∈ TauCeti.QuadraticMap.orthogonalGroup F.C.qU :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hiso
  have hoo' : o * o = 1 := LinearEquiv.ext fun v => hoo v
  have hdim : Module.finrank F.C.K (F.C.ι → F.C.K) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card, F.card_ι]
  have hR := uRange_eq_span F.hnd hoO hoo' hev hdim hu0 hqu hou
  have hline := isLineGen_pi hcA F.C.hD ha₀A ha₀1
  have h52A := h52 G M Q Z B F.hc F.C.K F.C.γ F.C.M₀ F.C.hD F.C.ι F.C.qU F.C.φ F.C.hF F.C.hA A
    hcA.conj hcA.le hcA.ne c₁ c₂ u hc12 hu0 hqu ⟨a₀, ha₀A, ha₀1, hpa⟩
  intro s hs
  have hsQ : s ∈ Q := hs.1
  have hyQ' : y * s * y⁻¹ ∈ Q := conj_mem_Q H hyM hsQ
  have hcQ : ⁅s, y⁆ ∈ Q := comm_mem_Q H hyM hsQ
  have hcommπ : F.C.φ (F.C.M₀.π ⁅s, y⁆) =
      F.C.φ (F.C.M₀.π s) - orthTensor g o (F.C.φ (F.C.M₀.π s)) := by
    have e : ⁅s, y⁆ = s * (y * s * y⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
    rw [e, F.C.M₀.π_mul s hsQ _ (Q.inv_mem hyQ'), Tim79.QuadModel.pi_inv F.C.M₀ hyQ', map_add,
      map_neg, ← sub_eq_add_neg, hact s hsQ]
  obtain ⟨w, s', t', hw, hs'⟩ := h52A.1 s hs
  obtain ⟨a, ha⟩ := orthTensor_sub_core hgg hc0 hgc (o := (o : _ →ₗ[_] _)) hou w s' t'
  have hmem : w - o w - a • u ∈ Submodule.span F.C.K {u} := by
    rw [← hR]
    have h1 : -(((o : (F.C.ι → F.C.K) →ₗ[F.C.K] (F.C.ι → F.C.K)) - 1) w) ∈
        (uPerp F.C.qU u).map ((o : (F.C.ι → F.C.K) →ₗ[F.C.K] (F.C.ι → F.C.K)) - 1) :=
      Submodule.neg_mem _ (Submodule.mem_map_of_mem (mem_uPerp.mpr hw))
    have h2 : (-a) • u ∈ Submodule.span F.C.K {u} :=
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
    have h3 := Submodule.add_mem_sup h1 h2
    have e : w - o w - a • u = -(((o : (F.C.ι → F.C.K) →ₗ[F.C.K] (F.C.ι → F.C.K)) - 1) w) +
        (-a) • u := by
      simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply]
      module
    rw [e]
    exact h3
  obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp hmem
  have hπc : F.C.M₀.π ⁅s, y⁆ = z • F.C.M₀.π a₀ := by
    apply F.C.φ.injective
    rw [hcommπ, hs', map_smul, hpa']
    have : ((c₁ • w + s' • u, c₂ • w + t' • u) : (F.C.ι → F.C.K) × (F.C.ι → F.C.K)) -
        orthTensor g o (c₁ • w + s' • u, c₂ • w + t' • u) = cTensor c (w - o w - a • u) := ha
    rw [this, ← hz]
    simp [cTensor_apply, hcdef, smul_smul, mul_comm]
  obtain ⟨a'', ha''A, ha''Q, ha''π⟩ := (hline (z • F.C.M₀.π a₀)).mpr ⟨z, rfl⟩
  have hZx : a''⁻¹ * ⁅s, y⁆ ∈ Z :=
    (Tim79.QuadModel.pi_eq_iff F.C.M₀ ha''Q hcQ).mp (by rw [ha''π, hπc])
  have e : ⁅s, y⁆ = a'' * (a''⁻¹ * ⁅s, y⁆) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ha''A) (Subgroup.mem_sup_left hZx)

end CommZA

section NoPerm

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_vecMulVec (X : Mat2 K) (hX : X ≠ 0) (hdet : X.det = 0) :
    ∃ a b : Fin 2 → K, a ≠ 0 ∧ b ≠ 0 ∧ ∀ i j, X i j = a i * b j := by
  by_cases hc : (fun i => X i 0) = 0
  · have h0 : ∀ i, X i 0 = 0 := fun i => congrFun hc i
    have h1 : (fun i => X i 1) ≠ 0 := by
      intro h1
      apply hX
      ext i j
      fin_cases j
      · simpa using h0 i
      · simpa using congrFun h1 i
    refine ⟨fun i => X i 1, ![0, 1], h1, ?_, fun i j => ?_⟩
    · intro h
      have := congrFun h 1
      simp at this
    · fin_cases j
      · simp [h0 i]
      · simp
  · obtain ⟨s, hs⟩ := exists_smul_of_det_zero (c := fun i => X i 0) (c' := fun i => X i 1) hc
      (by
        rw [Matrix.det_fin_two] at hdet
        show X 0 0 * X 1 1 - X 1 0 * X 0 1 = 0
        linear_combination hdet)
    refine ⟨fun i => X i 0, ![1, s], hc, ?_, fun i j => ?_⟩
    · intro h
      have := congrFun h 0
      simp at this
    · fin_cases j
      · simp
      · have := congrFun hs i
        simpa [mul_comm] using this

theorem thetaC_pure_eq {μ : (ι → K) ≃ₗ[K] Mat2 K} {c₁ c₂ : K} {u : ι → K} (hu0 : u ≠ 0)
    (hdet : (μ u).det = 0) (hc : c₁ ≠ 0 ∨ c₂ ≠ 0) :
    ∃ v : Fin 3 → Fin 2 → K, (∀ i, v i ≠ 0) ∧ thetaC μ (c₁ • u, c₂ • u) = pure3 v := by
  have hX : μ u ≠ 0 := fun h => hu0 (μ.map_eq_zero_iff.mp h)
  obtain ⟨a, b, ha, hb, hab⟩ := exists_vecMulVec (μ u) hX hdet
  refine ⟨![![c₁, c₂], a, b], fun i => ?_, ?_⟩
  · fin_cases i
    · intro h
      rcases hc with hc | hc
      · exact hc (by simpa using congrFun h 0)
      · exact hc (by simpa using congrFun h 1)
    · exact ha
    · exact hb
  · funext x
    rw [thetaC_apply, pure3_apply, Fin.prod_univ_three]
    obtain h | h : x 0 = 0 ∨ x 0 = 1 := by
      generalize x 0 = a
      fin_cases a <;> simp
    · simp [h, hab]
      ring
    · simp [h, hab]
      ring

end NoPerm

section PermOne

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem permHom_eq_one_of_comm (F : Data M Q Z B) (h52 : Smith52ActStatement) {Y : Subgroup G}
    (hcY : Ctx M Q Z Y) (m : ↥(H0 M Z)) (hmY : ∀ a ∈ Y, (m : G) * a * (m : G)⁻¹ = a)
    (hW : ∀ s ∈ Q ⊓ QB Y, ⁅s, (m : G)⁆ ∈ Z ⊔ Y) : permHom F m = 1 := by
  classical
  by_contra hπ
  have H := hcY.hyp
  have hZQ : Z ≤ Q := H.Z_normal.1
  obtain ⟨c₁, c₂, u, a₀, hc12, hu0, hqu, ha₀Y, ha₀1, hpa⟩ := exists_root_data F.C hcY
  have ha₀Q : a₀ ∈ Q := hcY.le ha₀Y
  have hdet : (F.μ u).det = 0 := by rw [F.det_eq, hqu]
  obtain ⟨v, hv, hpv⟩ := thetaC_pure_eq (μ := F.μ) (c₁ := c₁) (c₂ := c₂) hu0 hdet hc12
  have hp : coord F (F.C.M₀.π a₀) = pure3 v := by
    rw [coord, LinearEquiv.trans_apply, hpa, hpv]
  have hTp : rhoC F m (pure3 v) = pure3 v := by
    rw [← hp, rhoC_spec F m a₀ ha₀Q, hmY a₀ ha₀Y]
  obtain ⟨i, A, hA, hmoved⟩ := exists_moved hv hπ hTp fun i A hA => exists_actMap_conj F m i A hA
  obtain ⟨w, s', t', hw, hmem⟩ := exists_mem_D F.det_eq c₁ c₂ u hqu i A
  have h52Y := h52 G M Q Z B F.hc F.C.K F.C.γ F.C.M₀ F.C.hD F.C.ι F.C.qU F.C.φ F.C.hF F.C.hA Y
    hcY.conj hcY.le hcY.ne c₁ c₂ u hc12 hu0 hqu ⟨a₀, ha₀Y, ha₀1, hpa⟩
  obtain ⟨s, hs, hφs⟩ := h52Y.2 w s' t' hw
  have hsQ : s ∈ Q := hs.1
  have hmQ : (m : G) * s * (m : G)⁻¹ ∈ Q := conj_mem_Q H m.2.1 hsQ
  have hcs : coord F (F.C.M₀.π s) = actMap i A (pure3 v) := by
    rw [coord, LinearEquiv.trans_apply, hφs, hmem, ← hpv]
  have hcomm : coord F (F.C.M₀.π ⁅s, (m : G)⁆) =
      coord F (F.C.M₀.π s) - rhoC F m (coord F (F.C.M₀.π s)) := by
    have e : ⁅s, (m : G)⁆ = s * ((m : G) * s * (m : G)⁻¹)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e, F.C.M₀.π_mul s hsQ _ (Q.inv_mem hmQ), Tim79.QuadModel.pi_inv F.C.M₀ hmQ, map_add,
      map_neg, ← sub_eq_add_neg, rhoC_spec F m s hsQ]
  set R : Submodule F.C.K ((F.C.ι → F.C.K) × (F.C.ι → F.C.K)) :=
    Submodule.span F.C.K {((c₁ • u, c₂ • u) : (F.C.ι → F.C.K) × (F.C.ι → F.C.K))} with hR
  have hline := isLineGen_pi hcY F.C.hD ha₀Y ha₀1
  have hPY : Z ⊔ Y ≤ preimSub F.C.M₀ F.C.φ R := by
    refine sup_le (fun z hz => ?_) (fun a ha => ?_)
    · refine ⟨hZQ hz, ?_⟩
      rw [(F.C.M₀.π_ker z (hZQ hz)).mpr hz, map_zero]
      exact R.zero_mem
    · have haQ : a ∈ Q := hcY.le ha
      refine ⟨haQ, ?_⟩
      obtain ⟨t, ht⟩ := (hline _).mp (F.C.M₀.pi_mem_img ha haQ)
      rw [ht, map_smul, hpa]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  obtain ⟨-, hspan⟩ := hPY (hW s hs)
  obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp hspan
  have hcoord : coord F (F.C.M₀.π ⁅s, (m : G)⁆) = z • pure3 v := by
    rw [coord, LinearEquiv.trans_apply, ← hz, map_smul, ← hpv]
  rw [hcomm, hcs] at hcoord
  refine hmoved (-z) ?_
  rw [neg_smul, ← hcoord]
  abel

end PermOne

section DT

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem dt_four (F : Data M Q Z B) (h52 : Smith52ActStatement) {X : Subgroup G} {x : G}
    (hs : Sit M Q Z X x) (hxL : x ∈ Lgen M (LB M Q B)) {q' : G} (hq'Q : q' ∈ Q)
    (hcc : IsConj x ⁅q', x⁆) {g : G} (hcC₀ : ⁅q', x⁆ ∈ conjSubgroup g Z) :
    g⁻¹ * x * g ∈ Lgen M (LB M Q B) := by
  have hcB := F.hc.ctx
  have H := hcB.hyp
  have h12 := smith_1_12 hs
  have hxZ := hs.x_cent h12
  have hx2 := hs.x_sq
  have hxM := hs.memM
  have hZQ : Z ≤ Q := H.Z_normal.1
  by_cases hgZ : conjSubgroup g Z = Z
  ·
    have hgM : g ∈ M := by
      have := conjSubgroup_eq_self_iff.mp hgZ
      rwa [H.normalizer_Z.1] at this
    have hmem := (Subgroup.mem_normalizer_iff.mp
      (Lgen_normalizes M (LB M Q B) (M.inv_mem hgM)) x).mp hxL
    simpa using hmem
  have hc1 : ⁅q', x⁆ ≠ 1 := ne_one_of_isConj_Z hs.ne_one hcc
  have hcQ : ⁅q', x⁆ ∈ Q := comm_mem_Q H hxM hq'Q
  have hc2 : ⁅q', x⁆ * ⁅q', x⁆ = 1 := by
    have h1 : g⁻¹ * ⁅q', x⁆ * g ∈ Z := mem_conjSubgroup.mp hcC₀
    have h2 := Z_sq H h1
    have e : ⁅q', x⁆ * ⁅q', x⁆ = g * ((g⁻¹ * ⁅q', x⁆ * g) ^ 2) * g⁻¹ := by rw [pow_two]; group
    rw [e, h2]; group
  have hxc : x * ⁅q', x⁆ = ⁅q', x⁆ * x := commute_comm_of_sq hx2 hc2
  have hC₀ : IsZConjugate Z (conjSubgroup g Z) := ⟨g, rfl⟩
  have hxN : x ∈ Subgroup.normalizer ((conjSubgroup g Z : Subgroup G) : Set G) :=
    hC₀.mem_normalizer_of_commute H hc1 hcC₀ hxc
  have hC₀Q : conjSubgroup g Z ≤ Q := root_le_Q H hC₀ hcC₀ hcQ hc1
  have hcC : Ctx M Q Z (conjSubgroup g Z) := ⟨H, hC₀, hC₀Q, hgZ⟩
  have hxC : ∀ a ∈ conjSubgroup g Z, x * a * x⁻¹ = a := by
    obtain ⟨T, hTπ, -, -⟩ := F.C.hD.linear_of_centralizes hxM hxZ
    have hline := isLineGen_pi hcC F.C.hD hcC₀ hc1
    have hTc : T (F.C.M₀.π ⁅q', x⁆) = F.C.M₀.π ⁅q', x⁆ := by
      rw [← hTπ _ hcQ]
      congr 1
      have : x * ⁅q', x⁆ * x⁻¹ = ⁅q', x⁆ := by rw [hxc]; group
      rw [this]
    intro a ha
    have haQ : a ∈ Q := hC₀Q ha
    have hxaC : x * a * x⁻¹ ∈ conjSubgroup g Z := by
      have := (Subgroup.mem_normalizer_iff.mp hxN a).mp ha
      exact this
    obtain ⟨t, hsa⟩ := (hline _).mp (F.C.M₀.pi_mem_img ha haQ)
    have hπ : F.C.M₀.π a = F.C.M₀.π (x * a * x⁻¹) := by
      rw [hTπ a haQ, hsa, map_smul, hTc]
    have hZ1 : a⁻¹ * (x * a * x⁻¹) ∈ Z := (Tim79.QuadModel.pi_eq_iff F.C.M₀ haQ
      (conj_mem_Q H hxM haQ)).mp hπ
    have hC1 : a⁻¹ * (x * a * x⁻¹) ∈ conjSubgroup g Z :=
      (conjSubgroup g Z).mul_mem ((conjSubgroup g Z).inv_mem ha) hxaC
    have hbot : a⁻¹ * (x * a * x⁻¹) ∈ Z ⊓ conjSubgroup g Z := ⟨hZ1, hC1⟩
    rw [hcC.inf_eq_bot, Subgroup.mem_bot] at hbot
    have := congrArg (a * ·) hbot
    simpa using this
  set x' : G := g⁻¹ * x * g with hx'def
  set Y : Subgroup G := conjSubgroup g⁻¹ Z with hYdef
  have hx'M : x' ∈ M := by
    have h1 : g⁻¹ * x * g ∈ M := by
      have := hxN
      rw [normalizer_conj_eq H g, mem_conjSubgroup] at this
      exact this
    exact h1
  have hx'Z : ∀ z ∈ Z, x' * z * x'⁻¹ = z := by
    intro z hz
    have hzC : g * z * g⁻¹ ∈ conjSubgroup g Z := by
      rw [mem_conjSubgroup]; simpa [mul_assoc] using hz
    have := hxC _ hzC
    calc x' * z * x'⁻¹ = g⁻¹ * (x * (g * z * g⁻¹) * x⁻¹) * g := by simp only [hx'def]; group
      _ = z := by rw [this]; group
  have hx'2 : x' * x' = 1 := by
    have : x' * x' = g⁻¹ * (x * x) * g := by simp only [hx'def]; group
    rw [this, hx2]; group
  have hx'H0 : x' ∈ H0 M Z := ⟨hx'M, Subgroup.mem_centralizer_iff.mpr fun z hz => by
    have := hx'Z z hz
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm⟩
  have hYQ : Y ≤ Q := by
    have h1 : Z ≤ QB (conjSubgroup g Z) :=
      (IsZConjugate.le_QB_iff H hC₀ (IsZConjugate.self Z)).mpr (by rw [H.QB_Z]; exact hC₀Q)
    have h2 := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) h1
    rw [QB_conj_eq H g] at h2
    have e : conjSubgroup g⁻¹ (conjSubgroup g Q) = Q := by
      rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
    exact h2.trans (le_of_eq e)
  have hYZ : Y ≠ Z := by
    intro h
    apply hgZ
    have h1 : g⁻¹ ∈ Subgroup.normalizer (Z : Set G) := conjSubgroup_eq_self_iff.mp h
    have h2 : g ∈ Subgroup.normalizer (Z : Set G) := by simpa using Subgroup.inv_mem _ h1
    exact conjSubgroup_eq_self_iff.mpr h2
  have hcY : Ctx M Q Z Y := ⟨H, ⟨g⁻¹, rfl⟩, hYQ, hYZ⟩
  have hx'Y : ∀ a ∈ Y, x' * a * x'⁻¹ = a := by
    intro a ha
    have haZ : g * a * g⁻¹ ∈ Z := by
      have := mem_conjSubgroup.mp ha
      simpa using this
    have := hxZ _ haZ
    calc x' * a * x'⁻¹ = g⁻¹ * (x * (g * a * g⁻¹) * x⁻¹) * g := by simp only [hx'def]; group
      _ = a := by rw [this]; group
  have hW0 := comm_mem_ZA F h52 hcC hxL hx2 hxC
  have hZC : Z ⊔ conjSubgroup g Z ≤ (Z ⊔ Y).comap (MulAut.conj g⁻¹).toMonoidHom := by
    refine sup_le (fun z hz => ?_) (fun c hc => ?_)
    · refine Subgroup.mem_sup_right ?_
      rw [hYdef, mem_conjSubgroup]
      simpa [mul_assoc] using hz
    · exact Subgroup.mem_sup_left (by simpa using mem_conjSubgroup.mp hc)
  have hW : ∀ s ∈ Q ⊓ QB Y, ⁅s, x'⁆ ∈ Z ⊔ Y := by
    intro s hs'
    have hQBY : QB Y = conjSubgroup g⁻¹ Q := QB_conj_eq H g⁻¹
    have hsQ : s ∈ Q := hs'.1
    have hsC : g * s * g⁻¹ ∈ Q := by
      have hsB' : s ∈ QB Y := hs'.2
      rw [hQBY] at hsB'
      have := mem_conjSubgroup.mp hsB'
      simpa using this
    have hsB : g * s * g⁻¹ ∈ QB (conjSubgroup g Z) := by
      rw [QB_conj_eq H g, mem_conjSubgroup]
      simpa [mul_assoc] using hsQ
    have h1 := hW0 _ ⟨hsC, hsB⟩
    have h2 : g⁻¹ * ⁅g * s * g⁻¹, x⁆ * g ∈ Z ⊔ Y := by
      have := hZC h1
      rw [Subgroup.mem_comap] at this
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using this
    have e : ⁅s, x'⁆ = g⁻¹ * ⁅g * s * g⁻¹, x⁆ * g := by
      simp only [hx'def, commutatorElement_def]; group
    rw [e]
    exact h2
  have hπ := permHom_eq_one_of_comm F h52 hcY ⟨x', hx'H0⟩ hx'Y hW
  exact mem_Lgen_of_permHom_eq_one F ⟨x', hx'H0⟩ hπ (Subtype.ext hx'2)

end DT

end CFSG.RankThree.GF2n.Smith81.FourPlus

namespace CFSG.RankThree.GF2n.Smith81

theorem orthDTHypFour_of (h52 : Smith52ActStatement)
    (hT : OrthTacitStatement) : OrthDTHypFourStatement := by
  intro G _ _ M Q Z B hc C h4 hTSP X x hs hxL q' hval g hcC₀ _
  exact FourPlus.dt_four (FourPlus.Data.ofFrame hc (noA2_of_tacit hT hc) C h4 hTSP) h52 hs hxL
    hval.1 hval.2.2.1 hcC₀

end CFSG.RankThree.GF2n.Smith81
