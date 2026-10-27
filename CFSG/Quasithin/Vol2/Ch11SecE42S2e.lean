module

public import CFSG.Quasithin.Vol2.Ch11SecE42S2d
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.Quasithin.Vol2.Ch1ModO2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

abbrev thetaKJ (T L V₁ : Subgroup G) {K : Subgroup G} {p : ℕ} [Fact p.Prime]
    (φ : ↥K →* SL(2, ZMod p)) :
    ↥(kJ T L V₁ K) →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p) :=
  (Dickson.pslMap p).comp (φ.comp (Subgroup.inclusion ((kJ_le T L V₁ K).trans inf_le_left)))

omit [Finite G] in
theorem le_ker_thetaKJ (T L V₁ : Subgroup G) {K : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (φ : ↥K →* SL(2, ZMod p)) (hθs : Function.Surjective (thetaKJ T L V₁ φ))
    {S : Subgroup ↥(kJ T L V₁ K)} (hS : S.Normal) (h2 : IsPGroup 2 S) :
    S ≤ (thetaKJ T L V₁ φ).ker := by
  have h0 := eq_bot_of_normal_two_psl hp5 (hS.map _ hθs) (h2.map _)
  exact (Subgroup.map_eq_bot_iff _).mp h0

theorem ker_thetaKJ_eq (T L V₁ : Subgroup G) {K : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (φ : ↥K →* SL(2, ZMod p)) (hθs : Function.Surjective (thetaKJ T L V₁ φ))
    (hθR : ∀ k : ↥(kJ T L V₁ K), thetaKJ T L V₁ φ k = 1 → (k : G) ∈ ROf T L V₁) :
    (thetaKJ T L V₁ φ).ker = CFSG.pCore 2 ↥(kJ T L V₁ K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (le_sSup ⟨inferInstance, fun k => ?_⟩)
    (le_ker_thetaKJ T L V₁ hp5 φ hθs CFSG.pCore_normal CFSG.pCore_isPGroup)
  obtain ⟨j, hj⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (LOf L V₁ ⊔ T))
    ⟨_, hθR k k.2⟩
  exact ⟨j, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hj))⟩

theorem kJ_quot_iso (T L V₁ : Subgroup G) {K : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (φ : ↥K →* SL(2, ZMod p)) (hθs : Function.Surjective (thetaKJ T L V₁ φ))
    (hθR : ∀ k : ↥(kJ T L V₁ K), thetaKJ T L V₁ φ k = 1 → (k : G) ∈ ROf T L V₁) :
    Nonempty (↥(kJ T L V₁ K) ⧸ CFSG.pCore 2 ↥(kJ T L V₁ K) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (ker_thetaKJ_eq T L V₁ hp5 φ hθs hθR).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hθs)⟩

theorem kJ_mem_cComp {V₁ K : Subgroup G} (hTK : T ≤ Subgroup.normalizer (K : Set G)) {p : ℕ}
    [Fact p.Prime] (hp5 : 5 ≤ p) (φ : ↥K →* SL(2, ZMod p))
    (hθs : Function.Surjective (thetaKJ T L V₁ φ))
    (hθR : ∀ k : ↥(kJ T L V₁ K), thetaKJ T L V₁ φ k = 1 → (k : G) ∈ ROf T L V₁) :
    kJ T L V₁ K ∈ cComp (kJ T L V₁ K ⊔ T) := by
  obtain ⟨e⟩ := kJ_quot_iso T L V₁ hp5 φ hθs hθR
  have hQ := (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e).2 (isQuasisimple_psl hp5)
  have hne : kJ T L V₁ K ≠ ⊥ := by
    intro h0
    have hs := isSimpleGroup_psl (p := p) hp5
    obtain ⟨a, b, hab⟩ := hs.toNontrivial.exists_pair_ne
    obtain ⟨x, rfl⟩ := hθs a
    obtain ⟨y, rfl⟩ := hθs b
    have hx : x = 1 := Subtype.ext (Subgroup.mem_bot.mp (h0 ▸ x.2))
    have hy : y = 1 := Subtype.ext (Subgroup.mem_bot.mp (h0 ▸ y.2))
    rw [hx, hy] at hab
    exact hab rfl
  have hle : kJ T L V₁ K ≤ kJ T L V₁ K ⊔ T := le_sup_left
  refine SecA.mem_cComp_of_quasisimple hne (perfectCore_perfect _) hQ
    (A3.subnormal_of_normal hle ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
      (sup_le Subgroup.le_normalizer (T_le_normalizer_kJ hTK))))

omit [Finite G] in
theorem range_modO2_eq {N B : Subgroup G} (hBN : B ≤ N) :
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥N)).comp (Subgroup.inclusion hBN)).range =
      modO2Image N B := by
  ext x
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨Subgroup.inclusion hBN b, Subgroup.mem_subgroupOf.mpr b.2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, Subgroup.mem_subgroupOf.mp hy⟩, rfl⟩

omit [Finite G] in
theorem mem_ker_modO2_iff {N B : Subgroup G} (hBN : B ≤ N) (b : ↥B) :
    b ∈ ((QuotientGroup.mk' (CFSG.pCore 2 ↥N)).comp (Subgroup.inclusion hBN)).ker ↔
      (b : G) ∈ pCoreOf 2 N := by
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, ← SecD.pCoreOf_subgroupOf]
  rfl

theorem modO2Image_kJ_iso (T L V₁ : Subgroup G) {K N : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (φ : ↥K →* SL(2, ZMod p)) (hθs : Function.Surjective (thetaKJ T L V₁ φ))
    (hθR : ∀ k : ↥(kJ T L V₁ K), thetaKJ T L V₁ φ k = 1 → (k : G) ∈ ROf T L V₁)
    (hKJN : kJ T L V₁ K ≤ N) (hRN : ROf T L V₁ ≤ pCoreOf 2 N) :
    Nonempty (↥(modO2Image N (kJ T L V₁ K)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f := (QuotientGroup.mk' (CFSG.pCore 2 ↥N)).comp (Subgroup.inclusion hKJN) with hf
  have hker : f.ker = (thetaKJ T L V₁ φ).ker := by
    refine le_antisymm (le_ker_thetaKJ T L V₁ hp5 φ hθs inferInstance fun k => ?_) fun k hk => ?_
    · have hk := (mem_ker_modO2_iff hKJN (k : ↥(kJ T L V₁ K))).mp k.2
      obtain ⟨j, hj⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N) ⟨_, hk⟩
      exact ⟨j, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hj))⟩
    · exact (mem_ker_modO2_iff hKJN k).mpr (hRN (hθR k hk))
  exact ⟨(MulEquiv.subgroupCongr (range_modO2_eq hKJN).symm).trans
    ((QuotientGroup.quotientKerEquivRange f).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective _ hθs)))⟩

theorem exists_modO2Image_lOf_map {N L₁ : Subgroup G} (hLN : L₁ ≤ N) {F : Type} [Field F]
    (e : ↥L₁ ⧸ CFSG.pCore 2 ↥L₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    ∃ φ' : ↥(modO2Image N L₁) →* Matrix.SpecialLinearGroup (Fin 2) F,
      Function.Surjective φ' ∧ IsPGroup 2 ↥φ'.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set β := (QuotientGroup.mk' (CFSG.pCore 2 ↥N)).comp (Subgroup.inclusion hLN) with hβ
  set γ : ↥L₁ →* Matrix.SpecialLinearGroup (Fin 2) F :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L₁)) with hγ
  have hle : β.ker ≤ γ.ker := by
    have hnorm : β.ker ≤ CFSG.pCore 2 ↥L₁ := le_sSup ⟨inferInstance, fun k => by
      have hk := (mem_ker_modO2_iff hLN (k : ↥L₁)).mp k.2
      obtain ⟨j, hj⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N) ⟨_, hk⟩
      exact ⟨j, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hj))⟩⟩
    intro k hk
    rw [MonoidHom.mem_ker, hγ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff k).mpr (hnorm hk), map_one]
  set eB : ↥(modO2Image N L₁) ≃* ↥L₁ ⧸ β.ker :=
    (MulEquiv.subgroupCongr (range_modO2_eq hLN).symm).trans
      (QuotientGroup.quotientKerEquivRange β).symm with heB
  refine ⟨(QuotientGroup.lift β.ker γ hle).comp eB.toMonoidHom, ?_, ?_⟩
  · intro s
    obtain ⟨x, hx⟩ := (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L₁)) (e.symm s)
    refine ⟨eB.symm (QuotientGroup.mk x), ?_⟩
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
      QuotientGroup.lift_mk, hγ, MonoidHom.comp_apply, hx, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply]
  · intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective β.ker (eB y)
    have hγx : γ x = 1 := by
      have h1 : (QuotientGroup.lift β.ker γ hle) (eB y) = 1 := y.2
      rwa [← hx, QuotientGroup.mk'_apply, QuotientGroup.lift_mk] at h1
    have hx2 : QuotientGroup.mk' (CFSG.pCore 2 ↥L₁) x = 1 := e.injective (by simpa [hγ] using hγx)
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx2
    obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L₁)) ⟨x, hx2⟩
    have hxj : x ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    refine ⟨j, Subtype.ext (eB.injective ?_)⟩
    rw [Subgroup.coe_pow, map_pow, ← hx, ← map_pow, hxj, map_one, Subgroup.coe_one, map_one]

end CFSG.Quasithin.Vol2.Ch11.SecE
