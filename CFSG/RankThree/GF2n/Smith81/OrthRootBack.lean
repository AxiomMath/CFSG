module

public import CFSG.RankThree.GF2n.Smith81.OrthFrameChange
public import CFSG.RankThree.GF2n.Stroth80.Sec311OmegaTrans
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClSiegelEichler
public import CFSG.RankThree.GF2n.Stroth80.Sec12CaseVIEquiv
public import CFSG.RankThree.GF2n.Stroth80.Sec34Spure
public import CFSG.RankThree.GF2n.Smith81.TiFusion

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open CFSG.ClassicalGroups.Orthogonal (HypPair eichler eichler_apply elementaryGroup
  eichler_mem_elementaryGroup elementaryGroup_le_orthogonalGroup
  elementaryGroup_le_of_eichler_mem exists_hypPair)
open CFSG.RankThree.GF2n.Stroth80.Classify (ElationFull pointRad orthSubgroup
  orthSubgroup_eq_orthogonalGroup eichler_mem_pointRad orbit_transitive_omega)
open scoped commutatorElement Matrix

section Quad

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem orthRoot_nondeg_of_forall (q : QuadraticForm K V)
    (h : ∀ v, (∀ w, QuadraticMap.polar q v w = 0) → v = 0) :
    q.polarBilin.Nondegenerate :=
  ⟨fun v hv => h v fun w => by simpa using hv w,
    fun w hw => h w fun v => by rw [QuadraticMap.polar_comm]; simpa using hw v⟩

theorem orthRoot_isAlt [CharP K 2] (q : QuadraticForm K V) : q.polarBilin.IsAlt := fun v => by
  change QuadraticMap.polar q v v = 0
  rw [QuadraticMap.polar_self, two_nsmul, CharTwo.add_self_eq_zero]

theorem orthRoot_span_singular [CharP K 2] (q : QuadraticForm K V)
    (hq : q.polarBilin.Nondegenerate) {e : V} (he0 : e ≠ 0) (he : q e = 0) :
    Submodule.span K {v : V | q v = 0} = ⊤ := by
  obtain ⟨P, -⟩ := exists_hypPair hq he he0
  set S := Submodule.span K {v : V | q v = 0}
  have hePS : P.e ∈ S := Submodule.subset_span P.Q_e
  have hfPS : P.f ∈ S := Submodule.subset_span P.Q_f
  refine eq_top_iff.mpr fun v _ => ?_
  obtain ⟨hew, hfw⟩ := HypPair.mem_perp.mp (P.proj_mem_perp v)
  have h1 : QuadraticMap.polar q (P.proj v) P.e = 0 := by
    rw [QuadraticMap.polar_comm]; exact hew
  have h2 : QuadraticMap.polar q (P.proj v) P.f = 0 := by
    rw [QuadraticMap.polar_comm]; exact hfw
  have hs : P.proj v + q (P.proj v) • P.e + P.f ∈ S := by
    refine Submodule.subset_span ?_
    show q (P.proj v + q (P.proj v) • P.e + P.f) = 0
    rw [QuadraticMap.map_add q (P.proj v + q (P.proj v) • P.e) P.f,
      QuadraticMap.map_add q (P.proj v) (q (P.proj v) • P.e), QuadraticMap.map_smul, P.Q_e, P.Q_f,
      QuadraticMap.polar_smul_right, h1, QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left,
      h2, P.polar_ef]
    simp only [smul_eq_mul, mul_zero, mul_one, add_zero, zero_add]
    exact CharTwo.add_self_eq_zero _
  have hw : P.proj v ∈ S := by
    have h := S.sub_mem (S.sub_mem hs hfPS) (S.smul_mem (q (P.proj v)) hePS)
    convert h using 1
    abel
  rw [P.eq_add_proj v]
  exact S.add_mem (S.add_mem (S.smul_mem _ hePS) (S.smul_mem _ hfPS)) hw

end Quad

section Transitive

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem elationFull_elementaryGroup (q : QuadraticForm K V) (hq : q.polarBilin.Nondegenerate)
    {e : V} (he : q e = 0) :
    ElationFull q.polarBilin ((elementaryGroup q : Set (V ≃ₗ[K] V)) ∩ pointRad q.polarBilin e)
      e := by
  intro ψ hψ
  obtain ⟨w, hw⟩ := (LinearMap.BilinForm.toDual q.polarBilin hq).surjective (-ψ)
  have hwv : ∀ v, QuadraticMap.polar q v w = -ψ v := by
    intro v
    have h := congrArg (fun f : Module.Dual K V => f v) hw
    simp only [LinearMap.BilinForm.toDual_def, QuadraticMap.polarBilin_apply_apply,
      LinearMap.neg_apply] at h
    rw [QuadraticMap.polar_comm]
    exact h
  have hwe : QuadraticMap.polar q e w = 0 := by
    rw [hwv e, hψ, neg_zero]
  refine ⟨eichler q e w, ⟨eichler_mem_elementaryGroup q e w, eichler_mem_pointRad he hwe⟩,
    fun v hv => ?_⟩
  have hv' : QuadraticMap.polar q v e = 0 := by simpa using hv
  rw [eichler_apply he hwe v, hv', zero_smul, add_zero, mul_zero, add_zero, hwv v, neg_smul,
    sub_neg_eq_add]

theorem exists_elementary_map_singular [Finite K] [CharP K 2] (q : QuadraticForm K V)
    (hq : q.polarBilin.Nondegenerate) (hdim : 4 ≤ Module.finrank K V) {u u' : V} (hu : u ≠ 0)
    (hqu : q u = 0) (hu' : u' ≠ 0) (hqu' : q u' = 0) :
    ∃ h ∈ elementaryGroup q, ∃ c : K, c ≠ 0 ∧ h u = c • u' := by
  refine orbit_transitive_omega q.polarBilin hq (orthRoot_isAlt q) hdim rfl (elementaryGroup q)
    ?_ {v | v ≠ 0 ∧ q v = 0} (fun e he => he.1) (fun e he => he.2) ?_
    (fun e he => elationFull_elementaryGroup q hq he.2) ⟨hu, hqu⟩ ⟨hu', hqu'⟩
  · rw [orthSubgroup_eq_orthogonalGroup]
    exact elementaryGroup_le_orthogonalGroup q
  · rw [eq_top_iff, ← orthRoot_span_singular q hq hu hqu]
    refine Submodule.span_le.mpr fun v hv => ?_
    by_cases hv0 : v = 0
    · rw [hv0]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨hv0, hv⟩

end Transitive

section SL2

variable {K : Type} [Field K]

theorem exists_SL_mulVec_eq_vec (c c' : Fin 2 → K) (hc : c ≠ 0) (hc' : c' ≠ 0) :
    ∃ g : Matrix (Fin 2) (Fin 2) K, g.det = 1 ∧ g *ᵥ c = c' := by
  obtain ⟨h₁, hdet₁, hh₁⟩ := exists_SL_mulVec_eq c hc
  obtain ⟨h₂, hdet₂, hh₂⟩ := exists_SL_mulVec_eq c' hc'
  refine ⟨((h₂⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
    (h₁ : Matrix (Fin 2) (Fin 2) K), ?_, ?_⟩
  · rw [Matrix.det_mul, det_units_inv_eq_one h₂ hdet₂, hdet₁, one_mul]
  · rw [← Matrix.mulVec_mulVec, hh₁, ← hh₂, Matrix.mulVec_mulVec, Units.inv_mul,
      Matrix.one_mulVec]

end SL2

section Lift

variable {G : Type} [Group G] {Q Z : Subgroup G} {K : Type} [Field K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {ι : Type} [Fintype ι] [DecidableEq ι]
  {qU : QuadraticForm K (ι → K)} {φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)} {S : Subgroup G}

theorem exists_lgen_actsAs_elementary (hAct : OrthAct Q Z M₀ qU φ S)
    (hS : ∀ s ∈ S, ∀ x ∈ Q, s * x * s⁻¹ ∈ Q) {h : (ι → K) ≃ₗ[K] (ι → K)}
    (hh : h ∈ elementaryGroup qU) : ∃ s ∈ S, ActsAsTensor Q Z M₀ φ s 1 h := by
  have hh' : h ∈ Subgroup.closure
      {g : (ι → K) ≃ₗ[K] (ι → K) | ∃ u w, qU u = 0 ∧ QuadraticMap.polar qU u w = 0 ∧
        eichler qU u w = g} := hh
  refine Subgroup.closure_induction
    (p := fun (g : (ι → K) ≃ₗ[K] (ι → K)) _ => ∃ s ∈ S, ActsAsTensor Q Z M₀ φ s 1 g)
    ?_ ?_ ?_ ?_ hh'
  · rintro g ⟨u, w, hu, hw, rfl⟩
    exact hAct.eich u w hu hw
  · exact ⟨1, S.one_mem, ActsAsTensor.of_mem Q.one_mem⟩
  · rintro g g' _ _ ⟨s, hsS, hs⟩ ⟨s', hs'S, hs'⟩
    refine ⟨s * s', S.mul_mem hsS hs'S, ?_⟩
    have := ActsAsTensor.mul (o := (g : (ι → K) →ₗ[K] (ι → K)))
      (o' := (g' : (ι → K) →ₗ[K] (ι → K))) (hS s' hs'S) hs hs'
    rw [mul_one] at this
    exact this
  · rintro g _ ⟨s, hsS, hs⟩
    refine ⟨s⁻¹, S.inv_mem hsS, ?_⟩
    have hs' : ∀ x ∈ Q, s⁻¹ * x * s ∈ Q := by
      intro x hx
      have := hS s⁻¹ (S.inv_mem hsS) x hx
      rwa [inv_inv] at this
    exact ActsAsTensor.inv hs' hs (mul_one 1)

theorem exists_lgen_map_pure [Finite K] [CharP K 2] (hAct : OrthAct Q Z M₀ qU φ S)
    (hS : ∀ s ∈ S, ∀ x ∈ Q, s * x * s⁻¹ ∈ Q)
    (hnd : ∀ v : ι → K, (∀ w, QuadraticMap.polar qU v w = 0) → v = 0)
    (hn : 4 ≤ Fintype.card ι) {c c' : Fin 2 → K} (hc : c ≠ 0) (hc' : c' ≠ 0) {u u' : ι → K}
    (hu : u ≠ 0) (hqu : qU u = 0) (hu' : u' ≠ 0) (hqu' : qU u' = 0) :
    ∃ s ∈ S, ∃ (g : Matrix (Fin 2) (Fin 2) K) (o : (ι → K) → (ι → K)),
      ActsAsTensor Q Z M₀ φ s g o ∧
        orthTensor g o (c 0 • u, c 1 • u) = (c' 0 • u', c' 1 • u') := by
  obtain ⟨h, hh, μ, hμ, hhu⟩ := exists_elementary_map_singular qU
    (orthRoot_nondeg_of_forall qU hnd) (by rwa [Module.finrank_fintype_fun_eq_card]) hu hqu hu'
    hqu'
  obtain ⟨s₂, hs₂S, hs₂⟩ := exists_lgen_actsAs_elementary hAct hS hh
  obtain ⟨g, hg, hgc⟩ := exists_SL_mulVec_eq_vec c (μ⁻¹ • c') hc
    (smul_ne_zero (inv_ne_zero hμ) hc')
  obtain ⟨s₁, hs₁S, hs₁⟩ := hAct.sl g hg
  refine ⟨s₂ * s₁, S.mul_mem hs₂S hs₁S, g, h, ?_, ?_⟩
  · have := ActsAsTensor.mul (o := (h : (ι → K) →ₗ[K] (ι → K))) (o' := LinearMap.id)
      (hS s₁ hs₁S) hs₂ hs₁
    rw [one_mul, LinearMap.comp_id] at this
    exact this
  · have h0 : g 0 0 * c 0 + g 0 1 * c 1 = μ⁻¹ * c' 0 := by
      have := congrFun hgc 0
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
    have h1 : g 1 0 * c 0 + g 1 1 * c 1 = μ⁻¹ * c' 1 := by
      have := congrFun hgc 1
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
    have hscal : ∀ t : K, μ⁻¹ * t * μ = t := fun t => by field_simp
    simp only [orthTensor, map_smul, hhu, Prod.mk.injEq]
    constructor
    · calc g 0 0 • c 0 • μ • u' + g 0 1 • c 1 • μ • u'
          = ((g 0 0 * c 0 + g 0 1 * c 1) * μ) • u' := by module
        _ = c' 0 • u' := by rw [h0, hscal]
    · calc g 1 0 • c 0 • μ • u' + g 1 1 • c 1 • μ • u'
          = ((g 1 0 * c 0 + g 1 1 * c 1) * μ) • u' := by module
        _ = c' 1 • u' := by rw [h1, hscal]

end Lift

section QConj

variable {G : Type} [Group G] {M Q Z : Subgroup G} {K : Type} [Field K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}

theorem exists_conj_of_pi_eq (hD : GlobalModelData M Q Z γ M₀) {b x : G} (hb : b ∈ Q)
    (hbZ : b ∉ Z) (hx : x ∈ Q) (hπ : M₀.π x = M₀.π b) : ∃ q ∈ Q, q * b * q⁻¹ = x := by
  have hxb : x * b⁻¹ ∈ Q := Q.mul_mem hx (Q.inv_mem hb)
  have hz : x * b⁻¹ ∈ Z := by
    refine (M₀.π_ker _ hxb).mp ?_
    rw [M₀.π_mul x hx b⁻¹ (Q.inv_mem hb), Tim79.QuadModel.pi_inv M₀ hb, hπ, add_neg_cancel]
  obtain ⟨q, hqQ, hq⟩ := GM.exists_comm hD hb hbZ (Z.inv_mem hz)
  refine ⟨q, hqQ, ?_⟩
  have h1 : b * q * b⁻¹ * q⁻¹ = b * x⁻¹ := by
    have := hq
    rw [commutatorElement_def] at this
    rw [this]
    group
  have h2 : q * b⁻¹ * q⁻¹ = x⁻¹ := by
    calc q * b⁻¹ * q⁻¹ = b⁻¹ * (b * q * b⁻¹ * q⁻¹) := by group
      _ = x⁻¹ := by rw [h1]; group
  calc q * b * q⁻¹ = (q * b⁻¹ * q⁻¹)⁻¹ := by group
    _ = x := by rw [h2, inv_inv]

end QConj

section Main

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem isConj_of_pairTypeA (hcB : Ctx M Q Z B) {K : Type} [Field K] [Finite K] [CharP K 2]
    {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} (hD : GlobalModelData M Q Z γ M₀)
    {ι : Type} [Fintype ι] [DecidableEq ι] {qU : QuadraticForm K (ι → K)}
    {φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)} (hF : OrthPreFrame Q Z M₀ qU φ)
    (hAct : OrthAct Q Z M₀ qU φ (Lgen M (LB M Q B))) (hn : 4 ≤ Fintype.card ι)
    (hB : ∃ (c₀ : Fin 2 → K) (u₀ : ι → K), c₀ ≠ 0 ∧ u₀ ≠ 0 ∧ qU u₀ = 0 ∧
      ∀ e, e ∈ M₀.img B ↔ ∃ s : K, φ e = s • (c₀ 0 • u₀, c₀ 1 • u₀))
    {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) {x : G} (hxQ : x ∈ Q) (hxZ : x ∉ Z)
    (hx : PairTypeA qU (φ (M₀.π x))) : IsConj z x := by
  obtain ⟨c₀, u₀, hc₀, hu₀, hqu₀, hBimg⟩ := hB
  obtain ⟨c₁, c₂, u, hc, hu, hqu, hpx⟩ := hx
  have hLQ : ∀ s ∈ Lgen M (LB M Q B), ∀ y ∈ Q, s * y * s⁻¹ ∈ Q := fun s hs =>
    (hcB.conj_mem_Q_of_mem_M (Lgen_le_H0 hcB hs).1).1
  have hc' : (![c₁, c₂] : Fin 2 → K) ≠ 0 := by
    intro h0
    rcases hc with h | h
    · exact h (by simpa using congrFun h0 0)
    · exact h (by simpa using congrFun h0 1)
  obtain ⟨b, hbB, hbQ, hπb⟩ : ∃ b ∈ B, b ∈ Q ∧ φ (M₀.π b) = (c₀ 0 • u₀, c₀ 1 • u₀) := by
    obtain ⟨b, hbB, hbQ, hb⟩ := (hBimg (φ.symm (c₀ 0 • u₀, c₀ 1 • u₀))).mpr ⟨1, by simp⟩
    exact ⟨b, hbB, hbQ, by rw [hb, LinearEquiv.apply_symm_apply]⟩
  obtain ⟨s, hsS, g, o, hsa, hgo⟩ := exists_lgen_map_pure hAct hLQ hF.nondeg hn hc₀ hc' hu₀ hqu₀
    hu hqu
  have hb'Q : s * b * s⁻¹ ∈ Q := hLQ s hsS b hbQ
  have hπb' : M₀.π (s * b * s⁻¹) = M₀.π x := by
    apply φ.injective
    rw [hsa b hbQ, hπb, hgo, hpx]
    simp
  have hb'Z : s * b * s⁻¹ ∉ Z := fun h =>
    hxZ ((M₀.π_ker x hxQ).mp (hπb' ▸ (M₀.π_ker _ hb'Q).mpr h))
  have hb1 : b ≠ 1 := by
    rintro rfl
    exact hb'Z (by simpa using Z.one_mem)
  obtain ⟨q, hqQ, hq⟩ := exists_conj_of_pi_eq hD hb'Q hb'Z hxQ hπb'.symm
  obtain ⟨g₀, hg₀⟩ := hcB.conj
  have hz₂ : g₀⁻¹ * b * g₀ ∈ Z := by
    rw [hg₀, mem_conjSubgroup] at hbB
    exact hbB
  have hz₂1 : g₀⁻¹ * b * g₀ ≠ 1 := by
    intro h
    apply hb1
    calc b = g₀ * (g₀⁻¹ * b * g₀) * g₀⁻¹ := by group
      _ = 1 := by rw [h]; group
  obtain ⟨m, -, hm⟩ := Z_isConj hcB.hyp hz hz1 hz₂ hz₂1
  refine isConj_iff.mpr ⟨q * s * g₀ * m, ?_⟩
  calc q * s * g₀ * m * z * (q * s * g₀ * m)⁻¹
      = q * s * g₀ * (m * z * m⁻¹) * g₀⁻¹ * s⁻¹ * q⁻¹ := by group
    _ = q * (s * b * s⁻¹) * q⁻¹ := by rw [hm]; group
    _ = x := hq

end Main

end CFSG.RankThree.GF2n.Smith81
