module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary (SUid)

variable {G : Type} [Group G] [Finite G]

@[expose] def Case167_4_V1Eq (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_4 D V₀ V hV L → V₀ = ⊥ → v1Sub D.M V₀ V hV L = V₀

theorem Case167_4_V1Eq.v1Sub_eq {D : Data G} (h : Case167_4_V1Eq D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (h4 : Case167_4 D V₀ V hV L) :
    v1Sub D.M V₀ V hV L = V₀ := by
  by_cases h0 : V₀ = ⊥
  · exact h V₀ V L hV hS h4 h0
  · exact v1Sub_of_ne_bot D.M V₀ V hV L h0

structure UFrame (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (L : Subgroup G) where
  K : Type
  [instField : Field K]
  [instFinite : Finite K]
  card_K : Nat.card K = 4
  σ : K ≃+* K
  isUnitary : IsUnitaryInvolution σ
  two_eq_zero : (2 : K) = 0
  norm_eq : ∀ c : K, σ c * c = c ^ 3
  β : Vtil V₀ V hV ≃* Multiplicative (Fin 4 → K)
  π : ↥(SUid σ 4) ≃* ↥(lBar V₀ V hV L)
  equiv : ∀ (γ : ↥(SUid σ 4)) (w : Vtil V₀ V hV),
    β ((π γ : MulAut (Vtil V₀ V hV)) w) = Multiplicative.ofAdd (γ • Multiplicative.toAdd (β w))

attribute [instance] UFrame.instField UFrame.instFinite

theorem exists_uFrame (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (h4 : Case167_4 D V₀ V hV L) (h1 : v1Sub D.M V₀ V hV L = V₀) :
    Nonempty (UFrame V₀ V hV L) := by
  have hStar : NatSUn (lBar V₀ V hV L) (⊤ : Subgroup (Vtil V₀ V hV)) ⊥ 4 1 :=
    (fun X (hX : X = V₀)
      (h : NatSUn (barSub X V hV L) (⊤ : Subgroup (Vtil X V hV)) ⊥ 4 1) => by
        rw [hX] at h; exact h) (v1Sub D.M V₀ V hV L) h1 h4.2.1
  obtain ⟨K, instK, hFin, hK, hReal⟩ := hStar
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
  let β : Vtil V₀ V hV ≃* Multiplicative (Fin 4 → K) :=
    (Subgroup.topEquiv.symm).trans
      ((MulEquiv.ofBijective β₀ ⟨hβ₀inj, hβ₀surj⟩).trans βquo)
  have hβ_eval : ∀ u : ↥(⊤ : Subgroup (Vtil V₀ V hV)),
      β (u : Vtil V₀ V hV) = βquo (β₀ u) := by
    intro u
    rfl
  have hβquo_mk : ∀ m : ↥(FFModel.nat (StatedSU 4 (2 ^ 1) K)).sec,
      βquo (QuotientGroup.mk m) = Subgroup.topEquiv m := by
    intro m
    simp only [βquo, MulEquiv.trans_apply]
    rw [QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  have hequiv_top : ∀ (γ : ↥(StatedSU 4 (2 ^ 1) K)) (w : Vtil V₀ V hV),
      β ((π₀ γ : MulAut (Vtil V₀ V hV)) w) =
        CFSG.Quasithin.natAct (StatedSU 4 (2 ^ 1) K) γ (β w) := by
    intro γ w
    obtain ⟨m, hm⟩ : ∃ m : ↥(FFModel.nat (StatedSU 4 (2 ^ 1) K)).sec,
        β₀ ⟨w, Subgroup.mem_top w⟩ = QuotientGroup.mk m :=
      ⟨Quotient.out (β₀ ⟨w, Subgroup.mem_top w⟩), (Quotient.out_eq _).symm⟩
    have h1 : β w = Subgroup.topEquiv m := by
      have h := hβ_eval (⟨w, Subgroup.mem_top w⟩ : ↥(⊤ : Subgroup (Vtil V₀ V hV)))
      rw [hm, hβquo_mk] at h
      exact h
    have h2 : β ((π₀ γ : MulAut (Vtil V₀ V hV)) w) =
        Subgroup.topEquiv ⟨(FFModel.nat (StatedSU 4 (2 ^ 1) K)).act γ
          (m : (FFModel.nat (StatedSU 4 (2 ^ 1) K)).Amb), Subgroup.mem_top _⟩ := by
      have h := hβ_eval (⟨(π₀ γ : MulAut (Vtil V₀ V hV)) w,
        Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup (Vtil V₀ V hV)))
      rw [hβ₀act γ ⟨w, Subgroup.mem_top w⟩ m trivial trivial hm, hβquo_mk] at h
      exact h
    rw [h2, h1]
    rfl
  let π₁ : ↥(SUid σ 4) →* ↥(lBar V₀ V hV L) :=
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
  let π : ↥(SUid σ 4) ≃* ↥(lBar V₀ V hV L) :=
    MulEquiv.ofBijective π₁ ⟨hπ₁inj, hπ₁surj⟩
  have hequiv : ∀ (γ : ↥(SUid σ 4)) (w : Vtil V₀ V hV),
      β ((π γ : MulAut (Vtil V₀ V hV)) w) =
        Multiplicative.ofAdd (γ • Multiplicative.toAdd (β w)) := by
    intro γ w
    have h1 := hequiv_top (MulEquiv.subgroupCongr hS γ) w
    change β ((π₀ (MulEquiv.subgroupCongr hS γ) : MulAut (Vtil V₀ V hV)) w) =
      Multiplicative.ofAdd (γ • Multiplicative.toAdd (β w))
    rw [h1, CFSG.Quasithin.natAct, CFSG.ClassicalGroups.Unitary.smul_def]
    rw [MulEquiv.subgroupCongr_apply hS γ]
  exact ⟨⟨K, hK4, σ, hσ, h2, hnorm, β, π, hequiv⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
