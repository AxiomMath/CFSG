module

public import CFSG.Quasithin.Vol2.Ch10SecECase1b
public import CFSG.Quasithin.Vol2.Ch11SecHInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmallLinearTwo
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppEPerm
public import CFSG.Quasithin.Vol2.Ch10SecQ34LH
public import CFSG.Quasithin.Vol2.Ch10SecQ3CK
public import CFSG.Quasithin.Vol2.Ch10SecQ4S8

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Components

variable {W : Type*} [CommGroup W] [Finite W]

theorem exists_sl2_of_component {K₀ : Subgroup (MulAut W)}
    {C : Subgroup W} {j : ℕ} (h : E2.IsL2Natural K₀ C j ∧ 2 ≤ j ∨ E2.IsA5Module K₀ ∧ j = 2) :
    IsSimpleGroup ↥(oTwoUpper K₀) ∧
      (∃ a ∈ oTwoUpper K₀, ∃ b ∈ oTwoUpper K₀, a * b ≠ b * a) ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ j ∧
        Nonempty (↥(oTwoUpper K₀) ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  rcases h with ⟨hL, hj⟩ | ⟨hA5, rfl⟩
  · have hO := SecE.oTwoUpper_eq_self_of_isL2Natural hL hj
    obtain ⟨-, F, _, _, hF, e, -⟩ := hL
    let e' : ↥(oTwoUpper K₀) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
      (MulEquiv.subgroupCongr hO).trans e
    have hs : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
      CFSG.QuasithinUnique.AppE.sl2_isSimpleGroup hj hF
    refine ⟨e'.isSimpleGroup, ?_, F, inferInstance, inferInstance,
      by rw [Nat.card_eq_fintype_card, hF], ⟨e'⟩⟩
    let u : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
    let v : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
    refine ⟨e'.symm u, (e'.symm u).2, e'.symm v, (e'.symm v).2, fun huv => ?_⟩
    have h1 : e'.symm (u * v) = e'.symm (v * u) := by
      rw [map_mul, map_mul]
      exact Subtype.ext huv
    have h2 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
      (A : Matrix (Fin 2) (Fin 2) F) 0 0) (e'.symm.injective h1)
    change (!![1, 1; 0, 1] * !![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (!![1, 0; 1, 1] * !![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) 0 0 at h2
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h2
  · refine ⟨SecE.isSimpleGroup_oTwoUpper_of_isA5Module hA5,
      SecF.C10P4F.exists_noncomm_of_isA5Module hA5, ?_⟩
    obtain ⟨θ, -⟩ := hA5
    have : Finite ↥K₀ := Finite.of_equiv _ θ.symm.toEquiv
    have h1 : (oTwoUpper K₀).subgroupOf K₀ = oTwoUpper (⊤ : Subgroup ↥K₀) := by
      apply Subgroup.map_injective K₀.subtype_injective
      rw [← oTwoUpper_map, Subgroup.map_subgroupOf_eq_of_le (oTwoUpper_le K₀),
        ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have h2 : (oTwoUpper (⊤ : Subgroup ↥K₀)).map θ.toMonoidHom = alternatingGroup (Fin 5) := by
      rw [← oTwoUpper_map, Subgroup.map_top_of_surjective _ θ.surjective,
        SecE.oTwoUpper_top_perm_five]
    let e : ↥(oTwoUpper K₀) ≃* ↥(alternatingGroup (Fin 5)) :=
      ((Subgroup.subgroupOfEquivOfLe (oTwoUpper_le K₀)).symm.trans
        (MulEquiv.subgroupCongr h1)).trans
        ((Subgroup.equivMapOfInjective _ θ.toMonoidHom θ.injective).trans
          (MulEquiv.subgroupCongr h2))
    have hcard : Nat.card (GaloisField 2 2) = 4 := by
      rw [GaloisField.card 2 2 (by norm_num)]
      norm_num
    obtain ⟨f⟩ := CFSG.QuasithinUnique.Setup.Family.SL_two_four_equiv_alternating_five hcard
    exact ⟨GaloisField 2 2, inferInstance, inferInstance, hcard, ⟨e.trans f.symm⟩⟩

end Components

variable {G : Type} [Group G]

theorem nonempty_quot_equiv_of_autI [Finite G] (hAS : Ch11.SecH.AS_I_1_3_L2) {V K : Subgroup G}
    (hel : IsElemAbelian 2 V) (hKN : K ≤ Subgroup.normalizer (V : Set G))
    (hKq : CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K))
    (hOK : pCoreOf 2 K ≤ Subgroup.centralizer (V : Set G)) {F : Type} [Field F] [Finite F]
    {k : ℕ} (hk : 2 ≤ k) (hF : Nat.card F = 2 ^ k)
    (e : ↥(autI hel K) ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  suffices h : Nonempty (↥K ⧸ CFSG.Open.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) by
    obtain ⟨e₀⟩ := h
    exact ⟨(QuotientGroup.quotientMulEquivOfEq (SecB.C10P34.open_pCore_eq 2 ↥K)).symm.trans e₀⟩
  set P := CFSG.Open.pCore 2 ↥K with hP
  set f := convK hel hKN with hf
  have hf1 : P ≤ f.ker := fun x hx =>
    (convK_eq_one_iff hel hKN x).mpr (hOK ⟨x, hx, rfl⟩)
  set g : ↥K ⧸ P →* MulAut (IntMod V hel) := QuotientGroup.lift P f hf1 with hg
  have hgr : g.range = autI hel K := by
    rw [← range_convK hel hKN]
    ext φ
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective P x
      exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨QuotientGroup.mk' P y, rfl⟩
  set Z := g.ker with hZ
  let e₁ : (↥K ⧸ P) ⧸ Z ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientKerEquivRange g).trans ((MulEquiv.subgroupCongr hgr).trans e)
  have hZtop : Z ≠ ⊤ := by
    intro htop
    have : Subsingleton ((↥K ⧸ P) ⧸ Z) := by
      rw [htop]
      exact QuotientGroup.subsingleton_quotient_top
    have hs : Subsingleton (Matrix.SpecialLinearGroup (Fin 2) F) := e₁.symm.injective.subsingleton
    let u : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
    have h1 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
      (A : Matrix (Fin 2) (Fin 2) F) 0 1) (Subsingleton.elim u 1)
    simp [u] at h1
  have hZc : Z ≤ Subgroup.center (↥K ⧸ P) :=
    (normal_eq_top_or_le_center hKq (MonoidHom.normal_ker g)).resolve_left hZtop
  have hperf : Group.IsPerfect (↥K ⧸ P) := ⟨hKq.1⟩
  rcases hAS k hk F hF (↥K ⧸ P) hperf Z hZc ⟨e₁⟩ with hbot | ⟨-, h2, -⟩
  · exact ⟨(QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hbot.symm)).trans e₁⟩
  ·
    exfalso
    set Zh := Z.comap (QuotientGroup.mk' P) with hZh
    have hZhn : Zh.Normal := (MonoidHom.normal_ker g).comap _
    have hZh2 : IsPGroup 2 Zh := by
      intro x
      have hx2 : (QuotientGroup.mk' P (x : ↥K)) ^ 2 = 1 := by
        have hZ2 : IsPGroup 2 Z := IsPGroup.of_card (n := 1) (by rw [h2, pow_one])
        obtain ⟨j, hj⟩ := hZ2 ⟨_, x.2⟩
        have h1 : (QuotientGroup.mk' P (x : ↥K)) ^ 2 ^ j = 1 := by
          simpa using congrArg Subtype.val hj
        have h3 : orderOf (QuotientGroup.mk' P (x : ↥K)) ∣ 2 := by
          have := Subgroup.orderOf_dvd_natCard Z (x := QuotientGroup.mk' P (x : ↥K)) x.2
          rwa [h2] at this
        exact orderOf_dvd_iff_pow_eq_one.mp h3
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx2
      obtain ⟨j, hj⟩ := CFSG.LieType.BorelTits.pCore_isPGroup 2 ⟨_, hx2⟩
      refine ⟨j + 1, Subtype.ext ?_⟩
      have h4 : (x : ↥K) ^ 2 ^ (j + 1) = 1 := by
        rw [pow_succ', pow_mul]
        simpa using congrArg Subtype.val hj
      simpa using h4
    have hle : Zh ≤ P := CFSG.LieType.BorelTits.le_pCore 2 hZhn hZh2
    have hZbot : Z = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective P z
      have hy : y ∈ Zh := hz
      exact (QuotientGroup.eq_one_iff y).mpr (hle hy)
    rw [hZbot, Subgroup.card_bot] at h2
    exact absurd h2 (by norm_num)

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
