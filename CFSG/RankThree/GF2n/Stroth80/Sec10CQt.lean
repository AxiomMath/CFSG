module

public import CFSG.RankThree.GF2n.Stroth80.Sec10Five
public import CFSG.RankThree.GF2n.Stroth80.Sec34CaseB
public import CFSG.RankThree.GF2n.Smith81.Lin26Roots

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement Matrix

section LinearAlgebra

variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]

theorem orthogonal_inf_eq_sup {B : LinearMap.BilinForm K E} (hnd : B.Nondegenerate)
    (hrefl : B.IsRefl) (U W : Submodule K E) :
    B.orthogonal (U ⊓ W) = B.orthogonal U ⊔ B.orthogonal W := by
  have h1 : B.orthogonal (B.orthogonal U ⊔ B.orthogonal W) =
      B.orthogonal (B.orthogonal U) ⊓ B.orthogonal (B.orthogonal W) :=
    Submodule.orthogonalBilin_sup (B := B) (B.orthogonal U) (B.orthogonal W)
  rw [LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl,
    LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl] at h1
  calc B.orthogonal (U ⊓ W) = B.orthogonal (B.orthogonal
        (B.orthogonal U ⊔ B.orthogonal W)) := by rw [h1]
    _ = B.orthogonal U ⊔ B.orthogonal W :=
        LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl _

theorem orthogonal_range_sup_inf {B : LinearMap.BilinForm K E} (hnd : B.Nondegenerate)
    (hrefl : B.IsRefl) {R F Abar : Submodule K E} (hFR : F = B.orthogonal R)
    (hRF : R ≤ F) (hA : B.orthogonal Abar = Abar) :
    B.orthogonal (R ⊔ (Abar ⊓ F)) = R ⊔ (Abar ⊓ F) := by
  have hsup : B.orthogonal (R ⊔ (Abar ⊓ F)) =
      B.orthogonal R ⊓ B.orthogonal (Abar ⊓ F) :=
    Submodule.orthogonalBilin_sup (B := B) R (Abar ⊓ F)
  have hinf : B.orthogonal (Abar ⊓ F) = Abar ⊔ R := by
    rw [hFR]
    rw [orthogonal_inf_eq_sup hnd hrefl]
    rw [hA, LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl]
  rw [hsup, ← hFR, hinf]
  rw [inf_comm, sup_comm Abar R]
  exact sup_inf_assoc_of_le Abar hRF

theorem finrank_of_orthogonal_eq_self {B : LinearMap.BilinForm K E} (hnd : B.Nondegenerate)
    {n : ℕ} (hdim : Module.finrank K E = 2 * n) {S : Submodule K E}
    (hS : B.orthogonal S = S) : Module.finrank K S = n := by
  have h1 := LinearMap.BilinForm.finrank_orthogonal hnd S
  rw [hS] at h1
  have h2 : Module.finrank K S ≤ 2 * n := by
    rw [← hdim]
    exact Submodule.finrank_le S
  omega

end LinearAlgebra

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}

private theorem comp_self_eq_id {T : M₀.E ≃ₗ[K] M₀.E} (hT2 : ∀ e, T (T e) = e) :
    (T : M₀.E →ₗ[K] M₀.E) ∘ₗ (T : M₀.E →ₗ[K] M₀.E) = LinearMap.id := by
  ext e
  simpa [LinearMap.comp_apply] using hT2 e

private theorem exists_involution_of_LB (hc : Ctx M Q Z B)
    (h : GlobalModelData M Q Z γ M₀) {t : G} (ht : t ∈ LB M Q B) :
    ∃ T : M₀.E ≃ₗ[K] M₀.E,
      (∀ x ∈ Q, M₀.π (t * x * t⁻¹) = T (M₀.π x)) ∧
      (∀ e f, M₀.B (T e) (T f) = M₀.B e f) ∧
      (∀ e, T (T e) = e) ∧
      (∀ x ∈ Q, (x ∈ Ut Q Z t ↔
        M₀.π x ∈ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1))) := by
  obtain ⟨htQ, htQ'⟩ := hc.conj_mem_Q_of_mem_M (hc.LB_le_M ht)
  obtain ⟨T, hTπ, -, hTB⟩ := h.linear_of_centralizes (hc.LB_le_M ht) (hc.LB_centralizes_Z ht)
  refine ⟨T, hTπ, hTB, fun e => ?_, fun x hx => ?_⟩
  · obtain ⟨y, hyQ, rfl⟩ := M₀.π_surj e
    rw [← hTπ y hyQ, ← hTπ _ (htQ y hyQ)]
    have e2 : t * (t * y * t⁻¹) * t⁻¹ = t ^ 2 * y * (t ^ 2)⁻¹ := by rw [pow_two]; group
    rw [e2, Tim79.QuadModel.pi_conj_self (M₀ := M₀) (hc.sq_mem_Q_of_mem_LB ht) hyQ]
  · exact (M₀.mem_img_iff (le_sup_right : Z ≤ Ut Q Z t) hx).symm.trans
      (mem_img_comm_zpowers_sup_iff M₀ h.reg T htQ htQ' hTπ (M₀.π x))

theorem Ctx.card_Ut_le (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) {t : G}
    (ht : t ∈ LB M Q B) : Nat.card ↥(Ut Q Z t) ≤ Nat.card Z ^ (n + 1) := by
  obtain ⟨m, γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨T, hTπ, -, hT2, -⟩ := exists_involution_of_LB hc h ht
  have hq4 := hc.hyp.q4
  have hK : 1 < Nat.card (GaloisField 2 m) := by rw [h.card]; omega
  have hdim := h.finrank_E hw hK
  have hu := Tim79.QuadModel.finrank_range_le_of_sq_eq_one M₀ hdim (comp_self_eq_id hT2)
  have hcard := card_comm_zpowers_sup M₀ h.reg T
    (hc.conj_mem_Q_of_mem_M (hc.LB_le_M ht)).1
    (hc.conj_mem_Q_of_mem_M (hc.LB_le_M ht)).2 hTπ
  change Nat.card ↥(⁅Q, Subgroup.zpowers t⁆ ⊔ Z) ≤ Nat.card Z ^ (n + 1)
  rw [hcard, ← h.card]
  calc Nat.card (GaloisField 2 m) * Nat.card (GaloisField 2 m) ^
        Module.finrank (GaloisField 2 m)
          (LinearMap.range ((T : M₀.E →ₗ[GaloisField 2 m] M₀.E) - 1))
      = Nat.card (GaloisField 2 m) ^ (Module.finrank (GaloisField 2 m)
          (LinearMap.range ((T : M₀.E →ₗ[GaloisField 2 m] M₀.E) - 1)) + 1) := by
        rw [pow_succ']
    _ ≤ Nat.card (GaloisField 2 m) ^ (n + 1) :=
        Nat.pow_le_pow_right Nat.card_pos (Nat.succ_le_succ hu)

private def commQBHom (hc : Ctx M Q Z B) {t : G} (htB : t ∈ QB B) :
    ↥(Q ⊓ QB B) →* ↥B where
  toFun x := ⟨⁅(x : G), t⁆, Ctx.QB_comm_mem hc x.2.2 htB⟩
  map_one' := Subtype.ext (by simp [commutatorElement_def])
  map_mul' x y := by
    refine Subtype.ext ?_
    have hxQB : (x : G) ∈ QB B := x.2.2
    have hyB : ⁅(y : G), t⁆ ∈ B := Ctx.QB_comm_mem hc y.2.2 htB
    have hxB : ⁅(x : G), t⁆ ∈ B := Ctx.QB_comm_mem hc x.2.2 htB
    have hconj : (x : G) * ⁅(y : G), t⁆ * (x : G)⁻¹ = ⁅(y : G), t⁆ := by
      rw [← Ctx.B_central_QB hc hyB hxQB]; group
    have hcomm : ⁅(y : G), t⁆ * ⁅(x : G), t⁆ = ⁅(x : G), t⁆ * ⁅(y : G), t⁆ :=
      (Ctx.B_central_QB hc hxB (Ctx.B_le_QB hc hyB)).symm
    show ⁅(x : G) * (y : G), t⁆ = ⁅(x : G), t⁆ * ⁅(y : G), t⁆
    rw [show ⁅(x : G) * (y : G), t⁆ =
      (x : G) * ⁅(y : G), t⁆ * (x : G)⁻¹ * ⁅(x : G), t⁆ by
        simp only [commutatorElement_def]; group, hconj, hcomm]

private theorem ker_commQBHom (hc : Ctx M Q Z B) {t : G} (htB : t ∈ QB B) :
    (commQBHom hc htB).ker =
      (Q ⊓ QB B ⊓ Subgroup.centralizer ({t} : Set G)).subgroupOf (Q ⊓ QB B) := by
  ext x
  simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, commQBHom, MonoidHom.coe_mk,
    MonoidHom.coe_coe]
  constructor
  · intro h
    refine ⟨x.2, ?_⟩
    have h1 : ⁅(x : G), t⁆ = 1 := congrArg Subtype.val h
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (commutatorElement_eq_one_iff_mul_comm.mp h1)
  · rintro ⟨-, hx⟩
    refine Subtype.ext ?_
    show ⁅(x : G), t⁆ = 1
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hx)

private theorem card_range_commQBHom_le (hc : Ctx M Q Z B) {t : G} (htB : t ∈ QB B) :
    Nat.card (commQBHom hc htB).range ≤ Nat.card Z := by
  calc Nat.card (commQBHom hc htB).range ≤ Nat.card ↥B :=
        Nat.card_le_card_of_injective (fun y : ↥(commQBHom hc htB).range => y.1)
          (fun a b h => Subtype.ext h)
    _ = Nat.card Z := by
        obtain ⟨g, hg⟩ := hc.conj
        rw [hg]
        exact card_conjSubgroup g Z

theorem Ctx.card_inf_QB_le_mul_card_centralizer (hc : Ctx M Q Z B) {t : G}
    (htB : t ∈ QB B) :
    Nat.card ↥(Q ⊓ QB B) ≤
      Nat.card Z * Nat.card ↥(Q ⊓ QB B ⊓ Subgroup.centralizer ({t} : Set G)) := by
  let A : Subgroup G := Q ⊓ QB B
  let CA : Subgroup G := A ⊓ Subgroup.centralizer ({t} : Set G)
  have hkerCard : Nat.card (commQBHom hc htB).ker = Nat.card ↥CA := by
    rw [ker_commQBHom hc htB]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : CA ≤ A)).toEquiv
  have hAeq : Nat.card ↥A = Nat.card ↥CA * Nat.card (commQBHom hc htB).range := by
    rw [← hkerCard]
    exact (Subgroup.card_ker_mul_card_range (commQBHom hc htB)).symm
  calc Nat.card ↥(Q ⊓ QB B) = Nat.card ↥A := rfl
    _ = Nat.card ↥CA * Nat.card (commQBHom hc htB).range := hAeq
    _ ≤ Nat.card ↥CA * Nat.card ↥Z :=
        Nat.mul_le_mul_left _ (card_range_commQBHom_le hc htB)
    _ = Nat.card Z * Nat.card ↥(Q ⊓ QB B ⊓ Subgroup.centralizer ({t} : Set G)) := by
        rw [mul_comm]

private theorem mem_img_inf_QB_inf_centralizer (hc : Ctx M Q Z B)
    (h : GlobalModelData M Q Z γ M₀) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B)) {t : G} (htM : t ∈ M) (htB : t ∈ QB B)
    {T : M₀.E ≃ₗ[K] M₀.E}
    (hTπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = T (M₀.π x)) (e : M₀.E) :
    e ∈ M₀.img (Q ⊓ QB B ⊓ Subgroup.centralizer ({t} : Set G)) ↔
      e ∈ imgQInfQB M₀ B ∧ e ∈ LinearMap.ker ((T : M₀.E →ₗ[K] M₀.E) - 1) := by
  constructor
  · rintro ⟨a, haCA, haQ, rfl⟩
    have haA : a ∈ Q ⊓ QB B := (Subgroup.mem_inf.mp haCA).1
    refine ⟨(hc.mem_imgQInfQB_iff (X := B) hw hn hno h _).mpr
      (M₀.pi_mem_img haA haQ), ?_⟩
    have hTa : T (M₀.π a) = M₀.π a := by
      rw [← hTπ a haQ]
      have hat : a * t = t * a :=
        Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp haCA).2
      rw [show t * a * t⁻¹ = a by rw [← hat]; group]
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    exact hTa
  · rintro ⟨heA, heF⟩
    obtain ⟨a, haA, haQ, rfl⟩ :=
      (hc.mem_imgQInfQB_iff (X := B) hw hn hno h e).mp heA
    have hTa : T (M₀.π a) = M₀.π a := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at heF
      exact heF
    have htQ : ∀ x ∈ Q, t * x * t⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M htM).1
    have hcommZ : ⁅t, a⁆ ∈ Z := (comm_mem_iff_fix htQ hTπ haQ).mpr hTa
    have hcommB : ⁅t, a⁆ ∈ B := by
      have h := Ctx.QB_comm_mem hc haA.2 htB
      rw [← commutatorElement_inv a t]
      exact B.inv_mem h
    have hmem : ⁅t, a⁆ ∈ Z ⊓ B := Subgroup.mem_inf.mpr ⟨hcommZ, hcommB⟩
    rw [hc.inf_eq_bot] at hmem
    have hbot : ⁅t, a⁆ = 1 := Subgroup.mem_bot.mp hmem
    have hat : a * t = t * a :=
      (commutatorElement_eq_one_iff_mul_comm.mp hbot).symm
    exact ⟨a, ⟨haA, Subgroup.mem_centralizer_singleton_iff.mpr hat⟩, haQ, rfl⟩

private theorem img_centralizer_le_sup {R F Abar : Submodule K M₀.E} {t : G}
    (h : GlobalModelData M Q Z γ M₀) {T : M₀.E ≃ₗ[K] M₀.E}
    (hR : R = LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1))
    (hF : F = LinearMap.ker ((T : M₀.E →ₗ[K] M₀.E) - 1))
    (hFR : F = M₀.B.orthogonal R)
    (hSorth : M₀.B.orthogonal (R ⊔ (Abar ⊓ F)) = R ⊔ (Abar ⊓ F))
    (himgCA : ∀ e, e ∈ M₀.img (Q ⊓ QB B ⊓ Subgroup.centralizer ({t} : Set G)) ↔
      e ∈ Abar ⊓ F)
    (hTπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = T (M₀.π x))
    (hcomm : ∀ x ∈ Q ⊓ QB B ⊓ Subgroup.centralizer ({t} : Set G),
      ∀ a ∈ Q ⊓ Subgroup.centralizer ({t} : Set G), x * a = a * x) :
    ∀ e, e ∈ M₀.img (Q ⊓ Subgroup.centralizer ({t} : Set G)) → e ∈ R ⊔ (Abar ⊓ F) := by
  have hsup : M₀.B.orthogonal (R ⊔ (Abar ⊓ F)) =
      M₀.B.orthogonal R ⊓ M₀.B.orthogonal (Abar ⊓ F) :=
    Submodule.orthogonalBilin_sup (B := M₀.B) R (Abar ⊓ F)
  rintro e ⟨c, hcC, hcQ, rfl⟩
  have hcTc : T (M₀.π c) = M₀.π c := by
    rw [← hTπ c hcQ]
    have hct : c * t = t * c :=
      Subgroup.mem_centralizer_singleton_iff.mp hcC.2
    rw [show t * c * t⁻¹ = c by rw [← hct]; group]
  have hcF : M₀.π c ∈ F := by
    rw [hF, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    exact hcTc
  have hcOrthA : M₀.π c ∈ M₀.B.orthogonal (Abar ⊓ F) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro x hx
    obtain ⟨a, haCA, haQ, rfl⟩ := (himgCA x).mpr (Submodule.mem_inf.mp hx)
    have hca : a * c = c * a := hcomm a haCA c hcC
    exact (M₀.comm_iff_B h.reg haQ hcQ).mp hca
  rw [← hSorth, hsup]
  exact ⟨hFR ▸ hcF, hcOrthA⟩

private theorem range_involution_lagrangian (hc : Ctx M Q Z B)
    (h : GlobalModelData M Q Z γ M₀) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B)) {T : M₀.E ≃ₗ[K] M₀.E}
    (hTB : ∀ e f, M₀.B (T e) (T f) = M₀.B e f) (hT2 : ∀ e, T (T e) = e) :
    (LinearMap.ker ((T : M₀.E →ₗ[K] M₀.E) - 1) =
      M₀.B.orthogonal (LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1))) ∧
    (M₀.B.orthogonal (LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1) ⊔
      (imgQInfQB M₀ B ⊓ LinearMap.ker ((T : M₀.E →ₗ[K] M₀.E) - 1))) =
      LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1) ⊔
        (imgQInfQB M₀ B ⊓ LinearMap.ker ((T : M₀.E →ₗ[K] M₀.E) - 1))) ∧
    Module.finrank K ↥(LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1) ⊔
      (imgQInfQB M₀ B ⊓ LinearMap.ker ((T : M₀.E →ₗ[K] M₀.E) - 1))) = n := by
  let R : Submodule K M₀.E := LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)
  let F : Submodule K M₀.E := LinearMap.ker ((T : M₀.E →ₗ[K] M₀.E) - 1)
  let Abar : Submodule K M₀.E := imgQInfQB M₀ B
  have hR : R = LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1) := rfl
  have hF : F = LinearMap.ker ((T : M₀.E →ₗ[K] M₀.E) - 1) := rfl
  have hnd := modelB_nondegenerate M₀
  have hrefl : M₀.B.IsRefl := fun x y hxy => by
    rw [Tim79.QuadModel.B_comm, hxy, neg_zero]
  have hFR : F = M₀.B.orthogonal R := by
    rw [hF, hR, range_sub_one_eq_orthogonal_ker M₀.B hnd hrefl T hTB hT2]
    exact (LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl
      (LinearMap.ker ((T : M₀.E →ₗ[K] M₀.E) - 1))).symm
  have hRF : R ≤ F := by
    rw [hR, hF]
    exact Tim79.QuadModel.range_le_ker_of_sq_eq_one M₀ (comp_self_eq_id hT2)
  have hAbar : Module.finrank K Abar = n ∧
      (∀ v, (∀ u ∈ Abar, M₀.B v u = 0) → v ∈ Abar) ∧
      ∀ w ∈ Abar, M₀.Qf w = 0 := by
    simpa only [Abar] using hc.imgQInfQB_lagr (X := B) hw hn hno h
  have hA : M₀.B.orthogonal Abar = Abar := by
    refine le_antisymm ?_ ?_
    · intro v hv
      refine hAbar.2.1 v fun u hu => ?_
      rw [Tim79.QuadModel.B_comm,
        (LinearMap.BilinForm.mem_orthogonal_iff.mp hv) u hu, neg_zero]
    · intro a ha
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro u hu
      have h1 := M₀.Qf_add a u
      rw [hAbar.2.2 a ha, hAbar.2.2 u hu,
        hAbar.2.2 (a + u) (Abar.add_mem ha hu)] at h1
      have h1' : M₀.B a u = 0 := by simpa using h1.symm
      rw [Tim79.QuadModel.B_comm, h1', neg_zero]
  have hSorth : M₀.B.orthogonal (R ⊔ (Abar ⊓ F)) = R ⊔ (Abar ⊓ F) :=
    orthogonal_range_sup_inf hnd hrefl hFR hRF hA
  have hq4 := hc.hyp.q4
  have hK : 1 < Nat.card K := by rw [h.card]; omega
  have hSdim : Module.finrank K ↥(R ⊔ (Abar ⊓ F)) = n :=
    finrank_of_orthogonal_eq_self (S := R ⊔ (Abar ⊓ F)) hnd
      (h.finrank_E hw hK) hSorth
  exact ⟨hFR, hSorth, hSdim⟩

private theorem card_img_centralizer_le (hc : Ctx M Q Z B)
    (h : GlobalModelData M Q Z γ M₀) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B)) {t : G} (htM : t ∈ M) (htB : t ∈ QB B)
    {T : M₀.E ≃ₗ[K] M₀.E}
    (hTπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = T (M₀.π x))
    (hTB : ∀ e f, M₀.B (T e) (T f) = M₀.B e f) (hT2 : ∀ e, T (T e) = e)
    (hcomm : ∀ x ∈ Q ⊓ QB B ⊓ Subgroup.centralizer ({t} : Set G),
      ∀ a ∈ Q ⊓ Subgroup.centralizer ({t} : Set G), x * a = a * x) :
    Nat.card (M₀.img (Q ⊓ Subgroup.centralizer ({t} : Set G))) ≤ Nat.card Z ^ n := by
  obtain ⟨hFRexp, hSorthExp, hSdimexp⟩ :=
    range_involution_lagrangian hc h hw hn hno hTB hT2
  let R : Submodule K M₀.E := LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)
  let F : Submodule K M₀.E := LinearMap.ker ((T : M₀.E →ₗ[K] M₀.E) - 1)
  let Abar : Submodule K M₀.E := imgQInfQB M₀ B
  have hR : R = LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1) := rfl
  have hF : F = LinearMap.ker ((T : M₀.E →ₗ[K] M₀.E) - 1) := rfl
  have hFR : F = M₀.B.orthogonal R := hFRexp
  have hSorth : M₀.B.orthogonal (R ⊔ (Abar ⊓ F)) = R ⊔ (Abar ⊓ F) := hSorthExp
  have hSdim : Module.finrank K ↥(R ⊔ (Abar ⊓ F)) = n := hSdimexp
  have himgCA : ∀ e, e ∈ M₀.img (Q ⊓ QB B ⊓ Subgroup.centralizer ({t} : Set G)) ↔
      e ∈ Abar ⊓ F := by
    intro e
    exact mem_img_inf_QB_inf_centralizer hc h hw hn hno htM htB hTπ e
  have himgC := img_centralizer_le_sup h hR hF hFR hSorth himgCA hTπ (t := t) hcomm
  haveI : Finite M₀.E := Module.finite_of_finite K
  haveI : Finite ↥(R ⊔ (Abar ⊓ F)) :=
    Finite.of_injective (Subtype.val) Subtype.val_injective
  have hcard : Nat.card (M₀.img (Q ⊓ Subgroup.centralizer ({t} : Set G))) ≤
      Nat.card ↥(R ⊔ (Abar ⊓ F)) :=
    Nat.card_le_card_of_injective
      (fun y : ↥(M₀.img (Q ⊓ Subgroup.centralizer ({t} : Set G))) =>
        (⟨y.1, himgC y.1 y.2⟩ : ↥(R ⊔ (Abar ⊓ F))))
      (fun a b hab => Subtype.ext
        (congrArg (fun z : ↥(R ⊔ (Abar ⊓ F)) => (z : M₀.E)) hab))
  calc Nat.card (M₀.img (Q ⊓ Subgroup.centralizer ({t} : Set G)))
      ≤ Nat.card ↥(R ⊔ (Abar ⊓ F)) := hcard
    _ = Nat.card K ^ Module.finrank K (↥(R ⊔ (Abar ⊓ F))) :=
        Module.natCard_eq_pow_finrank (K := K) (V := ↥(R ⊔ (Abar ⊓ F)))
    _ = Nat.card K ^ n := by rw [hSdim]
    _ = Nat.card Z ^ n := by rw [h.card]

private theorem card_centralizer_le (hc : Ctx M Q Z B)
    (h : GlobalModelData M Q Z γ M₀) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B)) {t : G} (htM : t ∈ M) (htB : t ∈ QB B)
    {T : M₀.E ≃ₗ[K] M₀.E}
    (hTπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = T (M₀.π x))
    (hTB : ∀ e f, M₀.B (T e) (T f) = M₀.B e f) (hT2 : ∀ e, T (T e) = e)
    (hcomm : ∀ x ∈ Q ⊓ QB B ⊓ Subgroup.centralizer ({t} : Set G),
      ∀ a ∈ Q ⊓ Subgroup.centralizer ({t} : Set G), x * a = a * x) :
    Nat.card ↥(Q ⊓ Subgroup.centralizer ({t} : Set G)) ≤ Nat.card Z ^ (n + 1) := by
  have htLB : t ∈ LB M Q B := Subgroup.mem_sup_right ⟨htB, htM⟩
  have hZC : Z ≤ Q ⊓ Subgroup.centralizer ({t} : Set G) := by
    refine le_inf hc.Z_le_Q fun z hz => ?_
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have h := hc.LB_centralizes_Z htLB z hz
    calc z * t = (t * z * t⁻¹) * t := by rw [h]
      _ = t * z := by group
  have hcard := M₀.card_eq (inf_le_left : Q ⊓ Subgroup.centralizer ({t} : Set G) ≤ Q) hZC
  have himg := card_img_centralizer_le hc h hw hn hno htM htB hTπ hTB hT2 hcomm
  calc Nat.card ↥(Q ⊓ Subgroup.centralizer ({t} : Set G))
      = Nat.card Z * Nat.card (M₀.img (Q ⊓ Subgroup.centralizer ({t} : Set G))) := hcard
    _ ≤ Nat.card Z * Nat.card Z ^ n := Nat.mul_le_mul_left _ himg
    _ = Nat.card Z ^ (n + 1) := by rw [pow_succ']

private theorem card_centralizer_le_mul (hc : Ctx M Q Z B)
    (h : GlobalModelData M Q Z γ M₀) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B)) {t : G} (htM : t ∈ M) (htB : t ∈ QB B)
    {T : M₀.E ≃ₗ[K] M₀.E}
    (hTπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = T (M₀.π x))
    (hTB : ∀ e f, M₀.B (T e) (T f) = M₀.B e f) (hT2 : ∀ e, T (T e) = e)
    (hcomm : ∀ x ∈ Q ⊓ QB B ⊓ Subgroup.centralizer ({t} : Set G),
      ∀ a ∈ Q ⊓ Subgroup.centralizer ({t} : Set G), x * a = a * x) :
    Nat.card ↥(Q ⊓ Subgroup.centralizer ({t} : Set G)) ≤
      Nat.card Z * Nat.card ↥(Q ⊓ QB B ⊓ Subgroup.centralizer ({t} : Set G)) := by
  have hC := card_centralizer_le hc h hw hn hno htM htB hTπ hTB hT2 hcomm
  have hAbarCard : Nat.card ↥(imgQInfQB M₀ B) = Nat.card Z ^ n := by
    have h1 := (hc.imgQInfQB_lagr (X := B) hw hn hno h).1
    rw [Module.natCard_eq_pow_finrank (K := K) (V := ↥(imgQInfQB M₀ B)), h1, h.card]
  have hAcard : Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ (n + 1) := by
    rw [M₀.card_eq (inf_le_left : Q ⊓ QB B ≤ Q) (le_inf hc.Z_le_Q hc.Z_le_QB.1)]
    have himgA : Nat.card (M₀.img (Q ⊓ QB B)) = Nat.card ↥(imgQInfQB M₀ B) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun e =>
        (hc.mem_imgQInfQB_iff (X := B) hw hn hno h e).symm)
    rw [himgA, hAbarCard, pow_succ']
  have hle : Nat.card Z * Nat.card Z ^ n ≤
      Nat.card Z * Nat.card ↥(Q ⊓ QB B ⊓ Subgroup.centralizer ({t} : Set G)) := by
    calc Nat.card Z * Nat.card Z ^ n = Nat.card Z ^ (n + 1) := by rw [pow_succ']
      _ = Nat.card ↥(Q ⊓ QB B) := hAcard.symm
      _ ≤ Nat.card Z * Nat.card ↥(Q ⊓ QB B ⊓ Subgroup.centralizer ({t} : Set G)) :=
          hc.card_inf_QB_le_mul_card_centralizer htB
  have hCA : Nat.card Z ^ n ≤
      Nat.card ↥(Q ⊓ QB B ⊓ Subgroup.centralizer ({t} : Set G)) :=
    Nat.le_of_mul_le_mul_left hle Nat.card_pos
  calc Nat.card ↥(Q ⊓ Subgroup.centralizer ({t} : Set G)) ≤ Nat.card Z ^ (n + 1) := hC
    _ = Nat.card Z * Nat.card Z ^ n := by rw [pow_succ']
    _ ≤ Nat.card Z * Nat.card ↥(Q ⊓ QB B ⊓ Subgroup.centralizer ({t} : Set G)) :=
        Nat.mul_le_mul_left _ hCA

private theorem card_img_Ut_eq_card_range {t : G} {T : M₀.E ≃ₗ[K] M₀.E}
    (hUiff : ∀ x ∈ Q, (x ∈ Ut Q Z t ↔
      M₀.π x ∈ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1))) :
    Nat.card (M₀.img (Ut Q Z t)) =
      Nat.card ↥(LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)) := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun e => ?_)
  constructor
  · rintro ⟨x, hxU, hxQ, rfl⟩
    exact (hUiff x hxQ).mp hxU
  · intro he
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
    exact M₀.pi_mem_img ((hUiff x hxQ).mpr he) hxQ

private theorem card_Ut_eq_mul_card_range (hc : Ctx M Q Z B)
    (h : GlobalModelData M Q Z γ M₀) {t : G} (htM : t ∈ M)
    {T : M₀.E ≃ₗ[K] M₀.E}
    (hUiff : ∀ x ∈ Q, (x ∈ Ut Q Z t ↔
      M₀.π x ∈ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1))) :
    Nat.card ↥(Ut Q Z t) = Nat.card Z *
      Nat.card ↥(LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)) := by
  rw [M₀.card_eq (hc.Ut_le_Q htM) (le_sup_right : Z ≤ Ut Q Z t),
    card_img_Ut_eq_card_range hUiff]

private theorem finrank_range_eq_of_card_Ut (hc : Ctx M Q Z B)
    (h : GlobalModelData M Q Z γ M₀) {t : G} (htM : t ∈ M)
    {T : M₀.E ≃ₗ[K] M₀.E}
    (hUiff : ∀ x ∈ Q, (x ∈ Ut Q Z t ↔
      M₀.π x ∈ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)))
    {k : ℕ} (hk : Nat.card ↥(Ut Q Z t) = Nat.card Z ^ (k + 1)) :
    Module.finrank K ↥(LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)) = k := by
  have hRcard : Nat.card ↥(LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)) =
      Nat.card Z ^ Module.finrank K
        ↥(LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)) := by
    rw [Module.natCard_eq_pow_finrank (K := K)
      (V := ↥(LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1))), h.card]
  have h1 : Nat.card Z * Nat.card
      ↥(LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)) = Nat.card Z ^ (k + 1) := by
    rw [← card_Ut_eq_mul_card_range hc h htM hUiff]
    exact hk
  have h2 : Nat.card Z ^ (Module.finrank K
        ↥(LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)) + 1) =
      Nat.card Z ^ (k + 1) := by
    rw [pow_succ', ← hRcard]
    exact h1
  have hq4 := hc.hyp.q4
  have hq2 : 2 ≤ Nat.card Z := by omega
  have := Nat.pow_right_injective hq2 h2
  omega

private theorem n_le_succ_of_card_Ut (hc : Ctx M Q Z B)
    (h : GlobalModelData M Q Z γ M₀) {n : ℕ} (hw : Width Q Z n) {t : G} (htM : t ∈ M)
    {T : M₀.E ≃ₗ[K] M₀.E}
    (hTπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = T (M₀.π x))
    (hT2 : ∀ e, T (T e) = e)
    (hU : ∀ x ∈ Q, (x ∈ Ut Q Z t ↔
      M₀.π x ∈ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)))
    (hC : Nat.card ↥(Q ⊓ Subgroup.centralizer ({t} : Set G)) ≤ Nat.card Z ^ (n + 1))
    {k : ℕ} (hk : Nat.card ↥(Ut Q Z t) = Nat.card Z ^ (k + 1)) : n ≤ k + 1 := by
  let R : Submodule K M₀.E := LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)
  have hR : R = LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1) := rfl
  have hq4 := hc.hyp.q4
  have htQ : ∀ x ∈ Q, t * x * t⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M htM).1
  have htQ' : ∀ x ∈ Q, t⁻¹ * x * t ∈ Q := (hc.conj_mem_Q_of_mem_M htM).2
  have hu : Module.finrank K ↥R = k := by
    rw [hR]
    exact finrank_range_eq_of_card_Ut hc h htM hU hk
  have hRcard : Nat.card ↥R = Nat.card Z ^ k := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := ↥R), h.card, hu]
  have himgU : Nat.card (M₀.img (Ut Q Z t)) = Nat.card ↥R := by
    rw [hR]
    exact card_img_Ut_eq_card_range hU
  have hcardQ1 := hc.card_Q_eq_card_Q1_mul_img_Ut htM h.reg T htQ htQ' hTπ
  rw [himgU] at hcardQ1
  have hQ1 := hc.card_Q1_le htM
  have hQ1bound : Nat.card ↥(Q1 hc t) ≤ Nat.card Z ^ (n + 2) := by
    calc Nat.card ↥(Q1 hc t) ≤
          Nat.card ↥(Q ⊓ Subgroup.centralizer ({t} : Set G)) * Nat.card Z := hQ1
      _ ≤ Nat.card Z ^ (n + 1) * Nat.card Z := Nat.mul_le_mul_right _ hC
      _ = Nat.card Z ^ (n + 2) := by
          rw [show n + 2 = n + 1 + 1 by omega,
            ← pow_succ (Nat.card Z) (n + 1)]
  have hQcard : Nat.card ↥(Q1 hc t) * Nat.card Z ^ k = Nat.card Z ^ (2 * n + 1) := by
    rw [← hRcard, ← hcardQ1]
    exact hw
  have hmain : Nat.card Z ^ (2 * n + 1) ≤ Nat.card Z ^ (n + 2 + k) := by
    rw [← hQcard]
    calc Nat.card ↥(Q1 hc t) * Nat.card Z ^ k
        ≤ Nat.card Z ^ (n + 2) * Nat.card Z ^ k := Nat.mul_le_mul_right _ hQ1bound
      _ = Nat.card Z ^ (n + 2 + k) := by rw [pow_add (Nat.card Z) (n + 2) k]
  have hineq : 2 * n + 1 ≤ n + 2 + k :=
    (Nat.pow_le_pow_iff_right (by omega : 1 < Nat.card Z)).mp hmain
  omega

theorem Ctx.card_centralizer_le_of_commute (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) {t : G} (htM : t ∈ M) (htB : t ∈ QB B)
    (hcomm : ∀ x ∈ Q ⊓ QB B ⊓ Subgroup.centralizer ({t} : Set G),
      ∀ a ∈ Q ⊓ Subgroup.centralizer ({t} : Set G), x * a = a * x) :
    Nat.card ↥(Q ⊓ Subgroup.centralizer ({t} : Set G)) ≤ Nat.card Z ^ (n + 1) ∧
      Nat.card ↥(Q ⊓ Subgroup.centralizer ({t} : Set G)) ≤
        Nat.card Z * Nat.card ↥(Q ⊓ QB B ⊓ Subgroup.centralizer ({t} : Set G)) ∧
      ∀ k : ℕ, Nat.card ↥(Ut Q Z t) = Nat.card Z ^ (k + 1) → n ≤ k + 1 := by
  obtain ⟨m, γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨T, hTπ, hTB, hT2, hU⟩ :=
    exists_involution_of_LB hc h (Subgroup.mem_sup_right ⟨htB, htM⟩)
  have hC := card_centralizer_le hc h hw hn hno htM htB hTπ hTB hT2 hcomm
  refine ⟨hC, card_centralizer_le_mul hc h hw hn hno htM htB hTπ hTB hT2 hcomm, ?_⟩
  intro k hk
  exact n_le_succ_of_card_Ut hc h hw htM hTπ hT2 hU hC hk

private theorem Q1_eq_Ut_of_involution (hc : Ctx M Q Z B)
    (h : GlobalModelData M Q Z γ M₀) {n : ℕ} (hw : Width Q Z n) {t : G} (htM : t ∈ M)
    {T : M₀.E ≃ₗ[K] M₀.E}
    (hTπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = T (M₀.π x))
    (hT2 : ∀ e, T (T e) = e)
    (hUiff : ∀ x ∈ Q, (x ∈ Ut Q Z t ↔
      M₀.π x ∈ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)))
    (hUq : Nat.card ↥(Ut Q Z t) = Nat.card Z ^ (n + 1)) :
    Q1 hc t = Ut Q Z t := by
  let R : Submodule K M₀.E := LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)
  let F : Submodule K M₀.E := LinearMap.ker ((T : M₀.E →ₗ[K] M₀.E) - 1)
  have hR : R = LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1) := rfl
  have hF : F = LinearMap.ker ((T : M₀.E →ₗ[K] M₀.E) - 1) := rfl
  have htQ : ∀ x ∈ Q, t * x * t⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M htM).1
  have htQ' : ∀ x ∈ Q, t⁻¹ * x * t ∈ Q := (hc.conj_mem_Q_of_mem_M htM).2
  have hRF : R ≤ F := by
    rw [hR, hF]
    exact Tim79.QuadModel.range_le_ker_of_sq_eq_one M₀ (comp_self_eq_id hT2)
  have hRcard : Nat.card ↥R = Nat.card Z ^ Module.finrank K ↥R := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := ↥R), h.card]
  have hu : Module.finrank K ↥R = n := by
    rw [hR]
    exact finrank_range_eq_of_card_Ut hc h htM hUiff hUq
  have himgU : Nat.card (M₀.img (Ut Q Z t)) = Nat.card ↥R := by
    rw [hR]
    exact card_img_Ut_eq_card_range hUiff
  have hQcard := hc.card_Q_eq_card_Q1_mul_img_Ut htM h.reg T htQ htQ' hTπ
  rw [himgU] at hQcard
  have hQ1card : Nat.card ↥(Q1 hc t) = Nat.card Z ^ (n + 1) := by
    have hRcard' : Nat.card ↥R = Nat.card Z ^ n := by rw [hRcard, hu]
    have hQeq : Nat.card ↥(Q1 hc t) * Nat.card Z ^ n = Nat.card Z ^ (2 * n + 1) := by
      rw [← hRcard', ← hQcard]
      exact hw
    have hfactor : Nat.card Z ^ (2 * n + 1) =
        Nat.card Z ^ (n + 1) * Nat.card Z ^ n := by
      rw [← pow_add]
      congr 1
      omega
    rw [hfactor] at hQeq
    exact Nat.mul_right_cancel (pow_pos Nat.card_pos n) hQeq
  have hUQ1 : Ut Q Z t ≤ Q1 hc t := by
    intro x hxU
    have hxQ : x ∈ Q := hc.Ut_le_Q htM hxU
    refine (hc.mem_Q1_iff htM).mpr ⟨hxQ, ?_⟩
    have hxF : M₀.π x ∈ F := hRF ((hUiff x hxQ).mp hxU)
    rw [hF, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hxF
    exact (comm_mem_iff_fix htQ hTπ hxQ).mpr hxF
  have hcardle : Nat.card ↥(Q1 hc t) ≤ Nat.card ↥(Ut Q Z t) := by
    rw [hQ1card, hUq]
  exact (Subgroup.eq_of_le_of_card_ge hUQ1 hcardle).symm

theorem Ctx.Q1_eq_Ut_of_card_Ut (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) {t : G}
    (ht : t ∈ LB M Q B) (hU : Nat.card ↥(Ut Q Z t) = Nat.card Z ^ (n + 1)) :
    Q1 hc t = Ut Q Z t := by
  obtain ⟨m, γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨T, hTπ, -, hT2, hUiff⟩ := exists_involution_of_LB hc h ht
  exact Q1_eq_Ut_of_involution hc h hw (hc.LB_le_M ht) hTπ hT2 hUiff hU

theorem Ctx.no_fuse_of_card_Ut (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) {t : G}
    (ht : t ∈ LB M Q B) (hU : Nat.card ↥(Ut Q Z t) = Nat.card Z ^ (n + 1))
    (hUC : Ut Q Z t ≤ Subgroup.centralizer ({t} : Set G)) :
    ∀ y ∈ Q, ∀ z ∈ Z, y * t * y⁻¹ = t * z → z = 1 := by
  have htM : t ∈ M := hc.LB_le_M ht
  have hQ1U := hc.Q1_eq_Ut_of_card_Ut hw ht hU
  intro y hyQ z hz hconj
  have h1 : ⁅y, t⁆ = z := by
    rw [commutatorElement_def, hconj]
    exact hc.LB_centralizes_Z ht z hz
  have h2 : ⁅t, y⁆ = z⁻¹ := by
    rw [← commutatorElement_inv y t]
    exact congrArg Inv.inv h1
  have hyQ1 : y ∈ Q1 hc t :=
    (hc.mem_Q1_iff htM).mpr ⟨hyQ, by rw [h2]; exact Z.inv_mem hz⟩
  rw [hQ1U] at hyQ1
  have hyC : y ∈ Subgroup.centralizer ({t} : Set G) := hUC hyQ1
  have hyt : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
  have h3 : y * t * y⁻¹ = t := by rw [hyt]; group
  rw [h3] at hconj
  have h4 : t * 1 = t * z := by rw [mul_one]; exact hconj
  exact (mul_left_cancel h4).symm

end Model
