module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16NormIdx
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4Frame
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.Unitary CFSG.LocalAnalysis.RankThreeUC Matrix
open CFSG.LieType.Universal.Unitary (SUid)

variable {G : Type} [Group G] [Finite G]

section Frame

variable {X V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem exists_uFrame_of_natSUn
    (h : NatSUn (barSub X V hV L) (⊤ : Subgroup (Vtil X V hV)) ⊥ 4 1) :
    Nonempty (UFrame X V hV L) := by
  obtain ⟨K, instK, hFin, hK, hReal⟩ := h
  letI : Field K := instK
  letI : Finite K := hFin
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_sq (p := 2) (f := 1) hK
  set σ : K ≃+* K := CFSG.LieType.BorelTits.unitaryInvolution K 2 1 with hσdef
  have hσ : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution hK
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hS : SUid σ 4 = StatedSU 4 (2 ^ 1) K :=
    CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK 4
  have hnorm : ∀ c : K, σ c * c = c ^ 3 := by
    intro c
    rw [hσdef, CFSG.LieType.BorelTits.unitaryInvolution_apply, pow_one]
    ring
  obtain ⟨π₀, hπ₀⟩ := hReal
  obtain ⟨hπ₀surj, -, -, -, -, -, -, β₀, hβ₀surj, hβ₀ker, hβ₀act⟩ := hπ₀
  have hβ₀inj : Function.Injective β₀ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    ext u
    simpa [MonoidHom.mem_ker, Subgroup.mem_bot] using hβ₀ker u
  have hbot : (FFModel.nat (StatedSU 4 (2 ^ 1) K)).ker.subgroupOf
      (FFModel.nat (StatedSU 4 (2 ^ 1) K)).sec = ⊥ :=
    Subgroup.bot_subgroupOf _
  let βquo : ↥(FFModel.nat (StatedSU 4 (2 ^ 1) K)).sec ⧸
        ((FFModel.nat (StatedSU 4 (2 ^ 1) K)).ker.subgroupOf
          (FFModel.nat (StatedSU 4 (2 ^ 1) K)).sec) ≃*
      Multiplicative (Fin 4 → K) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans
      ((QuotientGroup.quotientBot).trans Subgroup.topEquiv)
  let β : Vtil X V hV ≃* Multiplicative (Fin 4 → K) :=
    (Subgroup.topEquiv.symm).trans
      ((MulEquiv.ofBijective β₀ ⟨hβ₀inj, hβ₀surj⟩).trans βquo)
  have hβ_eval : ∀ u : ↥(⊤ : Subgroup (Vtil X V hV)),
      β (u : Vtil X V hV) = βquo (β₀ u) := by
    intro u
    rfl
  have hβquo_mk : ∀ m : ↥(FFModel.nat (StatedSU 4 (2 ^ 1) K)).sec,
      βquo (QuotientGroup.mk m) = Subgroup.topEquiv m := by
    intro m
    simp only [βquo, MulEquiv.trans_apply]
    rw [QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  have hequiv_top : ∀ (γ : ↥(StatedSU 4 (2 ^ 1) K)) (w : Vtil X V hV),
      β ((π₀ γ : MulAut (Vtil X V hV)) w) =
        CFSG.Quasithin.natAct (StatedSU 4 (2 ^ 1) K) γ (β w) := by
    intro γ w
    obtain ⟨m, hm⟩ : ∃ m : ↥(FFModel.nat (StatedSU 4 (2 ^ 1) K)).sec,
        β₀ ⟨w, Subgroup.mem_top w⟩ = QuotientGroup.mk m :=
      ⟨Quotient.out (β₀ ⟨w, Subgroup.mem_top w⟩), (Quotient.out_eq _).symm⟩
    have h1 : β w = Subgroup.topEquiv m := by
      have h := hβ_eval (⟨w, Subgroup.mem_top w⟩ : ↥(⊤ : Subgroup (Vtil X V hV)))
      rw [hm, hβquo_mk] at h
      exact h
    have h2 : β ((π₀ γ : MulAut (Vtil X V hV)) w) =
        Subgroup.topEquiv ⟨(FFModel.nat (StatedSU 4 (2 ^ 1) K)).act γ
          (m : (FFModel.nat (StatedSU 4 (2 ^ 1) K)).Amb), Subgroup.mem_top _⟩ := by
      have h := hβ_eval (⟨(π₀ γ : MulAut (Vtil X V hV)) w,
        Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup (Vtil X V hV)))
      rw [hβ₀act γ ⟨w, Subgroup.mem_top w⟩ m trivial trivial hm, hβquo_mk] at h
      exact h
    rw [h2, h1]
    rfl
  let π₁ : ↥(SUid σ 4) →* ↥(lBar X V hV L) :=
    π₀.comp (MulEquiv.subgroupCongr hS).toMonoidHom
  have hπ₁surj : Function.Surjective π₁ :=
    hπ₀surj.comp (MulEquiv.subgroupCongr hS).surjective
  have hπ₁inj : Function.Injective π₁ := by
    intro a b hab
    have hγ : ∀ v : Fin 4 → K, a • v = b • v := by
      intro v
      obtain ⟨w, hw⟩ := β.surjective (Multiplicative.ofAdd v)
      have h1 := hequiv_top (MulEquiv.subgroupCongr hS a) w
      have h2 := hequiv_top (MulEquiv.subgroupCongr hS b) w
      have h3 : π₀ (MulEquiv.subgroupCongr hS a) =
          π₀ (MulEquiv.subgroupCongr hS b) := hab
      rw [h3] at h1
      have h4 : CFSG.Quasithin.natAct (StatedSU 4 (2 ^ 1) K)
            (MulEquiv.subgroupCongr hS a) (β w) =
          CFSG.Quasithin.natAct (StatedSU 4 (2 ^ 1) K)
            (MulEquiv.subgroupCongr hS b) (β w) := h1.symm.trans h2
      have hta : Multiplicative.toAdd (β w) = v := by rw [hw]; rfl
      rw [CFSG.Quasithin.natAct, CFSG.Quasithin.natAct, hta] at h4
      have h5 := Multiplicative.ofAdd.injective h4
      rw [MulEquiv.subgroupCongr_apply hS a, MulEquiv.subgroupCongr_apply hS b] at h5
      simpa only [CFSG.ClassicalGroups.Unitary.smul_def σ] using h5
    refine CFSG.ClassicalGroups.Unitary.ext_smul σ ?_
    intro v
    exact hγ v
  let π : ↥(SUid σ 4) ≃* ↥(lBar X V hV L) :=
    MulEquiv.ofBijective π₁ ⟨hπ₁inj, hπ₁surj⟩
  have hequiv : ∀ (γ : ↥(SUid σ 4)) (w : Vtil X V hV),
      β ((π γ : MulAut (Vtil X V hV)) w) =
        Multiplicative.ofAdd (γ • Multiplicative.toAdd (β w)) := by
    intro γ w
    have h1 := hequiv_top (MulEquiv.subgroupCongr hS γ) w
    change β ((π₀ (MulEquiv.subgroupCongr hS γ) : MulAut (Vtil X V hV)) w) =
      Multiplicative.ofAdd (γ • Multiplicative.toAdd (β w))
    rw [h1, CFSG.Quasithin.natAct, CFSG.ClassicalGroups.Unitary.smul_def]
    rw [MulEquiv.subgroupCongr_apply hS γ]
  exact ⟨⟨K, hK4, σ, hσ, h2, hnorm, β, π, hequiv⟩⟩

theorem UFrame.card_V_of_le (F : UFrame X V hV L) (hle : X ≤ V) :
    Nat.card V = 2 ^ 8 * Nat.card X := by
  have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup (modNull X V hV)
  have h1 : Nat.card V = Nat.card (Vtil X V hV) * Nat.card (modNull X V hV) := hq
  have h2 : Nat.card (modNull X V hV) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [h1, F.card_Vtil, h2]

theorem UFrame.rho_semilinear_of_mem_normalizer (F : UFrame X V hV L)
    {φ : MulAut (Vtil X V hV)}
    (hφN : φ ∈ normalizer (lBar X V hV L : Set (MulAut (Vtil X V hV)))) :
    ∃ θ : F.K →+* F.K, ∀ (c : F.K) (x : Fin 4 → F.K), F.rho φ (c • x) = θ c • F.rho φ x := by
  have hK : Nat.card F.K = (2 ^ 1) ^ 2 := by rw [F.card_K]; norm_num
  refine exists_semilinear_statedSU hK (F.rho φ) ?_
  intro g hg
  have hgSU : g ∈ SUid F.σ 4 := by rw [F.suid_eq_statedSU]; exact hg
  let γ : ↥(SUid F.σ 4) := ⟨g, hgSU⟩
  have hφinvN : φ⁻¹ ∈ normalizer (lBar X V hV L : Set (MulAut (Vtil X V hV))) :=
    (normalizer _).inv_mem hφN
  have hmem : φ⁻¹ * (F.π γ) * φ ∈ lBar X V hV L := by
    have h := (Subgroup.mem_set_normalizer_iff.1 hφinvN (F.π γ)).1 (F.π γ).2
    simpa using h
  let γ' : ↥(SUid F.σ 4) := F.π.symm ⟨φ⁻¹ * (F.π γ) * φ, hmem⟩
  have hπγ' : (F.π γ' : MulAut (Vtil X V hV)) =
      φ⁻¹ * (F.π γ : MulAut (Vtil X V hV)) * φ := by
    simp [γ']
  refine ⟨(γ' : GL (Fin 4) F.K), ?_, ?_⟩
  · rw [← F.suid_eq_statedSU]
    exact γ'.2
  · intro x
    have hsymm : ∀ y : Fin 4 → F.K, (F.rho φ).symm y = F.vec (φ⁻¹ (F.ofVec y)) := by
      intro y
      apply (F.rho φ).injective
      rw [AddEquiv.apply_symm_apply, F.rho_vec]
      simp
    rw [hsymm, hsymm]
    have hx1 : F.ofVec (g *ᵥ x) =
        (F.π γ : MulAut (Vtil X V hV)) (F.ofVec x) := by
      apply F.vec_injective
      rw [F.vec_ofVec, F.vec_action, CFSG.ClassicalGroups.Unitary.smul_def]
      simp [γ]
    rw [hx1, ← CFSG.ClassicalGroups.Unitary.smul_def,
      ← F.vec_action γ' (φ⁻¹ (F.ofVec x)), hπγ']
    simp [MulAut.mul_apply]

theorem UFrame.four_mul_card_centMod_le (F : UFrame X V hV L) (hle : X ≤ V) {m : G}
    (hms : m ∈ stabTil X V)
    (hN : actTil X V hV ⟨m, hms⟩ ∈ normalizer (lBar X V hV L : Set (MulAut (Vtil X V hV))))
    (hnot : ¬ CentralizesMod X V m) :
    2 ^ 2 * Nat.card (centMod X V m) ≤ Nat.card V := by
  have hmod : Nat.card (modNull X V hV) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  let φ : MulAut (Vtil X V hV) := actTil X V hV ⟨m, hms⟩
  have hφne : φ ≠ 1 := by
    intro h1
    exact hnot ((actTil_eq_one_iff X V hV ⟨m, hms⟩).1 h1)
  have hne : ∃ x, F.rho φ x ≠ x := by
    by_contra h
    apply hφne
    refine MulEquiv.ext fun w => ?_
    have hw : F.rho φ (F.vec w) = F.vec w :=
      not_not.mp ((not_exists.mp h) (F.vec w))
    rw [F.rho_vec] at hw
    exact F.vec_injective hw
  obtain ⟨θ, hθ⟩ := F.rho_semilinear_of_mem_normalizer hN
  have hfix := card_fix_mul_le (F := F.K) (θ := θ) (F.rho φ) hθ hne
  rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, F.card_K] at hfix
  norm_num at hfix
  have hcent : (centMod X V m : Set G) =
      (preTil X V hV (fixV (Subgroup.zpowers φ)) : Set G) := by
    ext v
    constructor
    · rintro ⟨hv, hv0⟩
      change v ∈ preTil X V hV (fixV (Subgroup.zpowers φ))
      rw [mem_preTil_iff_of_mem X V hV _ hv, mem_fixV_zpowers]
      change actTil X V hV ⟨m, hms⟩ (mkTil X V hV (IntMod.mk hV ⟨v, hv⟩)) =
        mkTil X V hV (IntMod.mk hV ⟨v, hv⟩)
      rw [actTil_mk, mkTil_eq_iff, actStab_apply_val]
      simpa [IntMod.mk, IntMod.val, mul_assoc] using hv0
    · intro h
      have hv : v ∈ V := preTil_le X V hV _ h
      refine ⟨hv, ?_⟩
      have h' : v ∈ preTil X V hV (fixV (Subgroup.zpowers φ)) := h
      rw [mem_preTil_iff_of_mem X V hV _ hv, mem_fixV_zpowers] at h'
      change actTil X V hV ⟨m, hms⟩ (mkTil X V hV (IntMod.mk hV ⟨v, hv⟩)) =
        mkTil X V hV (IntMod.mk hV ⟨v, hv⟩) at h'
      rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at h'
      simpa [IntMod.mk, IntMod.val, mul_assoc] using h'
  have hfixcard : Nat.card (fixV (Subgroup.zpowers φ)) =
      Nat.card {x : Fin 4 → F.K // F.rho φ x = x} := by
    let e : Vtil X V hV ≃ (Fin 4 → F.K) :=
      Equiv.ofBijective F.vec ⟨F.vec_injective, fun x => ⟨F.ofVec x, F.vec_ofVec x⟩⟩
    refine Nat.card_congr (Equiv.subtypeEquiv e ?_)
    intro w
    show w ∈ fixV (Subgroup.zpowers φ) ↔ F.rho φ (F.vec w) = F.vec w
    rw [mem_fixV_zpowers, F.rho_vec, F.vec_injective.eq_iff]
  have hcentcard : Nat.card (centMod X V m) =
      Nat.card X * Nat.card (fixV (Subgroup.zpowers φ)) := by
    rw [hcent]
    change Nat.card (preTil X V hV (fixV (Subgroup.zpowers φ))) =
      Nat.card X * Nat.card (fixV (Subgroup.zpowers φ))
    unfold preTil
    rw [Subgroup.card_map_of_injective (IntMod.val_injective (hV := hV))]
    have hpre : Nat.card ((fixV (Subgroup.zpowers φ)).comap (mkTil X V hV)) =
        Nat.card (modNull X V hV) * Nat.card (fixV (Subgroup.zpowers φ)) := by
      have h := Nat.card_congr (QuotientGroup.preimageMkEquivSubgroupProdSet
        (modNull X V hV) ((fixV (Subgroup.zpowers φ)) : Set (Vtil X V hV)))
      rw [Nat.card_prod] at h
      exact h
    rw [hpre, hmod]
  calc 2 ^ 2 * Nat.card (centMod X V m)
      = Nat.card X * (Nat.card (fixV (Subgroup.zpowers φ)) * 4) := by
        rw [hcentcard]; norm_num; ring
    _ ≤ Nat.card X * 256 := by
        rw [hfixcard]
        exact Nat.mul_le_mul_left _ hfix
    _ = Nat.card V := by rw [F.card_V_of_le hle]; ring

end Frame

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
