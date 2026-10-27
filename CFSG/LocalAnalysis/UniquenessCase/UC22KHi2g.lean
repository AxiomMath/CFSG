module

public import CFSG.LocalAnalysis.UniquenessCase.UC22KHi2m
public import CFSG.LocalAnalysis.UniquenessCase.UC22KHi2f

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (InClassG oResidualTwo)
open P22x P22s

variable {G : Type} [Group G] [Finite G]

namespace P22k2

theorem gl_oResidualTwo_apply_mem {X : Type} [Group X] (σ : X ≃* X) {x : X} (hx : x ∈ oResidualTwo X) :
    σ x ∈ oResidualTwo X := by
  unfold oResidualTwo at hx ⊢
  rw [Subgroup.mem_sInf] at hx ⊢
  rintro N ⟨hN, hp⟩
  refine hx (N.comap σ.toMonoidHom) ⟨hN.comap _, fun q => ?_⟩
  induction q using QuotientGroup.induction_on with
  | H y =>
    obtain ⟨k, hk⟩ := hp (QuotientGroup.mk (σ y))
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk ⊢
    simpa using hk

theorem gl_conj_mem_map_oResidualTwo {H : Subgroup G} {q : G} (hq : q ∈ normalizer (H : Set G)) {k : G}
    (hk : k ∈ (oResidualTwo ↥H).map H.subtype) : q * k * q⁻¹ ∈ (oResidualTwo ↥H).map H.subtype := by
  obtain ⟨h, hh, rfl⟩ := hk
  refine ⟨H.normalizerMonoidHom ⟨q, hq⟩ h, gl_oResidualTwo_apply_mem _ hh, ?_⟩
  exact Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _

theorem gl_normalizer_le_map_oResidualTwo (H : Subgroup G) :
    normalizer (H : Set G) ≤ normalizer (((oResidualTwo ↥H).map H.subtype : Subgroup G) : Set G) := by
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨fun hk => gl_conj_mem_map_oResidualTwo hq hk, fun hk => ?_⟩
  have := gl_conj_mem_map_oResidualTwo (inv_mem hq) hk
  simpa [mul_assoc] using this

theorem gl_inClassG_of_supplement {S H : Subgroup G} (hSH : S ≤ H) (hS : IsPGroup 2 S)
    (hidx : ¬ 2 ∣ S.relIndex H)
    (hF : H ⊓ centralizer (CFSG.Open.pCoreOf 2 H : Set G) ≤ CFSG.Open.pCoreOf 2 H) (K : Subgroup ↥H) [K.Normal]
    (e : (↥H ⧸ K) ≃* CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 1))
    (hsup : ∀ Y : Subgroup ↥H, Y ⊔ K = ⊤ → CFSG.pCore 2 ↥H ≤ Y → Y = ⊤) :
    InClassG ↥S ↥H (Subgroup.inclusion hSH) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨Subgroup.inclusion_injective hSH, ?_, ?_, ?_⟩
  · refine ⟨le_top, ?_, ?_⟩
    · rw [Subgroup.inclusion_range]
      exact hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
    · rw [Subgroup.inclusion_range, Subgroup.relIndex_top_right]
      exact hidx
  · refine (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore ↥H 2).1 ?_
    intro x hx
    have hxG : (x : G) ∈ H ⊓ centralizer (CFSG.Open.pCoreOf 2 H : Set G) := by
      refine Subgroup.mem_inf.2 ⟨x.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨y, hy, rfl⟩
      exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.1 hx) y hy)
    obtain ⟨y, hy, hyx⟩ := hF hxG
    have : y = x := Subtype.ext hyx
    rwa [← this]
  · refine ⟨1, le_rfl, K, inferInstance, ⟨e⟩, ?_⟩
    intro Y hY hYK hQY
    exact hY.ne (hsup Y hYK hQY)

theorem gl_exists_mulEquiv_aut (D : Data G) {Y : Subgroup (MBar D.M D.U)} {V₀ : Subgroup G}
    {K₃ : Subgroup (MBar D.M D.U)} (kp : KleinPkg D Y V₀ K₃) (hY : Y ≤ mbarImage D.M D.U (proofN D))
    (hY6 : Nat.card ↥Y = 6) (hA6 : Nat.card (MulAut ↥V₀) = 6) : Nonempty (↥Y ≃* MulAut ↥V₀) := by
  have hV := uc22p22xf_hV D
  have hV₀U : V₀ ≤ D.U := kp.le_Ii.trans (proofIi_le D (preN_le_M D Y))
  have hNi : preN D Y ≤ normalizer (V₀ : Set G) := fun x hx =>
    kp.norm x (preN_le_M D Y hx) (Subgroup.le_normalizer hx)
  set ψN : ↥(preN D Y) →* MulAut ↥V₀ := s3_psi hNi with hψN
  let π : ↥(preN D Y) →* ↥Y :=
    ((QuotientGroup.mk' (kerAct D.M D.U).normalCore).comp (Subgroup.inclusion (preN_le_M D Y))).codRestrict Y
      (fun x => ((mem_preN D).1 x.2).2.choose_spec)
  have hπ : ∀ x : ↥(preN D Y), ((π x : ↥Y) : MBar D.M D.U) = QuotientGroup.mk ⟨x.1, preN_le_M D Y x.2⟩ :=
    fun x => rfl
  have hπs : Function.Surjective π := by
    intro y
    have hy' : (y : MBar D.M D.U) ∈ mbarImage D.M D.U (preN D Y) := by
      rw [mbarImage_preN D hY]
      exact y.2
    obtain ⟨n, hn, hny⟩ := hy'
    exact ⟨⟨n, hn⟩, Subtype.ext hny⟩
  have hker : π.ker ≤ ψN.ker := by
    intro x hx
    have h1 : (QuotientGroup.mk ⟨x.1, preN_le_M D Y x.2⟩ : MBar D.M D.U) = 1 := by
      rw [← hπ]
      exact congrArg Subtype.val hx
    have hxC : (x : G) ∈ centralizer (D.U : Set G) :=
      (uc22br_gt_mk_eq_one_iff hV ⟨x.1, preN_le_M D Y x.2⟩).1 h1
    exact (s3_psi_eq_one_iff hNi x).2 (Subgroup.centralizer_le hV₀U hxC)
  set θ : ↥Y →* MulAut ↥V₀ := (π.liftOfSurjective hπs) ⟨ψN, hker⟩ with hθ
  have hθπ : ∀ x, θ (π x) = ψN x := fun x => by simp [hθ]
  have hinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    obtain ⟨x, rfl⟩ := hπs y
    rw [hθπ] at hy
    have hxC : (x : G) ∈ centralizer (V₀ : Set G) := (s3_psi_eq_one_iff hNi x).1 hy
    have hxU : (x : G) ∈ centralizer (D.U : Set G) := kp.faith x x.2 hxC
    have h1 : (QuotientGroup.mk ⟨x.1, preN_le_M D Y x.2⟩ : MBar D.M D.U) = 1 :=
      (uc22br_gt_mk_eq_one_iff hV ⟨x.1, preN_le_M D Y x.2⟩).2 hxU
    exact Subtype.ext (by rw [hπ]; exact h1)
  haveI : Finite (MulAut ↥V₀) := Nat.finite_of_card_ne_zero (by omega)
  exact ⟨MulEquiv.ofBijective θ (hinj.bijective_of_nat_card_le (by rw [hA6, hY6]))⟩

theorem gl_K3_conj {D : Data G} {Y : Subgroup (MBar D.M D.U)} {V₀ : Subgroup G}
    {K₃ : Subgroup (MBar D.M D.U)} (kp : KleinPkg D Y V₀ K₃) {g : MBar D.M D.U}
    (hg : ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) {z : MBar D.M D.U} (hz : z ∈ K₃) : g * z * g⁻¹ ∈ K₃ := by
  have hz3 : z ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥K₃) (x := ⟨z, hz⟩)
    rw [kp.K3_card] at this
    simpa using congrArg Subtype.val this
  refine kp.K3_cube _ (hg z (kp.K3_le hz)) ?_
  rw [conj_pow, hz3]
  group

theorem gl_mem_normalizer_K3 {D : Data G} {Y : Subgroup (MBar D.M D.U)} {V₀ : Subgroup G}
    {K₃ : Subgroup (MBar D.M D.U)} (kp : KleinPkg D Y V₀ K₃) {g : MBar D.M D.U}
    (hg : ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) (hg' : ∀ y ∈ Y, g⁻¹ * y * g⁻¹⁻¹ ∈ Y) :
    g ∈ normalizer (K₃ : Set (MBar D.M D.U)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨fun hz => gl_K3_conj kp hg hz, fun hz => ?_⟩
  have := gl_K3_conj kp hg' hz
  simpa [mul_assoc] using this

theorem gl_le_normalizer_rK3 (D : Data G) {Y : Subgroup (MBar D.M D.U)} {V₀ : Subgroup G}
    {K₃ : Subgroup (MBar D.M D.U)} (kp : KleinPkg D Y V₀ K₃) (hY : Y ≤ mbarImage D.M D.U (proofN D)) :
    (rad118 D ⊓ preMbar D Y) ⊔ T1 D Y ≤ normalizer ((rad118 D ⊓ preMbar D K₃ : Subgroup G) : Set G) := by
  intro x hx
  obtain ⟨ρ, hρ, t, ht, rfl⟩ := exists_mul_of_mem_sup (fr_T1_le_normalizer_rI D hY) hx
  refine mul_mem ?_ ?_
  · obtain ⟨hρM, hρb⟩ := (mem_preMbar D).1 hρ.2
    refine mem_normalizer_inf (M_le_normalizer_rad118 D hρM) (mem_normalizer_preMbar D hρM ?_)
    exact gl_mem_normalizer_K3 kp (fun y hy => Y.mul_mem (Y.mul_mem hρb hy) (Y.inv_mem hρb))
      (fun y hy => Y.mul_mem (Y.mul_mem (Y.inv_mem hρb) hy) (Y.inv_mem (Y.inv_mem hρb)))
  · refine mem_normalizer_inf (M_le_normalizer_rad118 D (T1_le_M D Y ht))
      (mem_normalizer_preMbar D (T1_le_M D Y ht) ?_)
    exact gl_mem_normalizer_K3 kp (fun y hy => T1_conj_mem D hY ht hy)
      (fun y hy => T1_conj_mem D hY (inv_mem ht) hy)

theorem gl_exists_pow_mem_rK3 (D : Data G) {Y : Subgroup (MBar D.M D.U)} {V₀ : Subgroup G}
    {K₃ : Subgroup (MBar D.M D.U)} (kp : KleinPkg D Y V₀ K₃) (hY : Y ≤ mbarImage D.M D.U (proofN D)) {x : G}
    (hx : x ∈ (rad118 D ⊓ preMbar D Y) ⊔ T1 D Y) : ∃ k : ℕ, x ^ 2 ^ k ∈ rad118 D ⊓ preMbar D K₃ := by
  obtain ⟨k, hk⟩ := exists_two_pow_mem_of_mem_sup (isPGroup_T1 D Y) (fr_T1_le_normalizer_rI D hY) hx
  refine ⟨k + 1, ?_⟩
  have e : x ^ 2 ^ (k + 1) = (x ^ 2 ^ k) ^ 2 := by rw [pow_succ, pow_mul]
  rw [e]
  obtain ⟨hxM, hxb⟩ := (mem_preMbar D).1 hk.2
  refine ⟨(rad118 D).pow_mem hk.1 2, (mem_preMbar D).2 ⟨D.M.pow_mem hxM 2, ?_⟩⟩
  have e2 : (QuotientGroup.mk ⟨(x ^ 2 ^ k) ^ 2, D.M.pow_mem hxM 2⟩ : MBar D.M D.U) =
      (QuotientGroup.mk ⟨x ^ 2 ^ k, hxM⟩ : MBar D.M D.U) ^ 2 := rfl
  rw [e2]
  exact kp.K3_sq _ hxb

theorem gl_twoResidual_le_rK3 (D : Data G) {Y : Subgroup (MBar D.M D.U)} {V₀ : Subgroup G}
    {K₃ : Subgroup (MBar D.M D.U)} (kp : KleinPkg D Y V₀ K₃) (hY : Y ≤ mbarImage D.M D.U (proofN D))
    {P : Subgroup G} (hPR : P ≤ (rad118 D ⊓ preMbar D Y) ⊔ T1 D Y) :
    CFSG.Quasithin.twoResidual P ≤ P ⊓ (rad118 D ⊓ preMbar D K₃) :=
  CFSG.Quasithin.twoResidual_le_of_isTwoQuotient inf_le_left
    (fun x hx => mem_normalizer_inf' (Subgroup.le_normalizer hx) (gl_le_normalizer_rK3 D kp hY (hPR hx)))
    (fun y hy => by
      obtain ⟨k, hk⟩ := gl_exists_pow_mem_rK3 D kp hY (hPR hy)
      exact ⟨k, P.pow_mem hy _, hk⟩)

end P22k2

end CFSG.LocalAnalysis.UniquenessCase.UC22
