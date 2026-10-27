module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Refl2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7Eseven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenWitt

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem card_fixed_gt_of_mQuot_le {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} (hV₀ : V₀ ≤ V)
    (S : OmegaModel (Vtil V₀ V hV)) {m : ℕ} (hSK : Nat.card S.K = 2 ^ m) {n : ℕ} (hn : n < 2 * m)
    {x : G} (hxs : x ∈ stabTil V₀ V)
    (hxn : E3.mQuot V (V ⊓ centralizer ({x} : Set G)) ≤ n) :
    Nat.card S.K ^ 2 < Nat.card {v : Vtil V₀ V hV // actTil V₀ V hV ⟨x, hxs⟩ v = v} := by
  classical
  let U : Subgroup G := V ⊓ centralizer ({x} : Set G)
  have hUV : U ≤ V := inf_le_left
  have hxn' : E3.mQuot V U ≤ n := hxn
  have hfix : ∀ q ∈ imgTil V₀ V hV U, actTil V₀ V hV ⟨x, hxs⟩ q = q := by
    intro q hq
    obtain ⟨y, hy, rfl⟩ := (mem_imgTil V₀ V hV U q).1 hq
    have hy' : y.val ∈ V ⊓ centralizer ({x} : Set G) := hy
    have hyc : y.val ∈ centralizer ({x} : Set G) := (Subgroup.mem_inf.1 hy').2
    have hcomm : y.val * x = x * y.val := Subgroup.mem_centralizer_singleton_iff.1 hyc
    have hstab : actStab V₀ V hV ⟨x, hxs⟩ y = y := by
      apply IntMod.val_injective
      rw [actStab_apply_val]
      show x * y.val * x⁻¹ = y.val
      rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [actTil_mk, hstab]
  have hW2 : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := fun w => by
    rw [pow_two]
    exact S.mul_self_eq_one w
  have hle : Nat.card ↥(imgTil V₀ V hV U) ≤
      Nat.card {v : Vtil V₀ V hV // actTil V₀ V hV ⟨x, hxs⟩ v = v} :=
    Nat.card_le_card_of_injective
      (fun q => (⟨q.1, hfix q.1 q.2⟩ :
        {v : Vtil V₀ V hV // actTil V₀ V hV ⟨x, hxs⟩ v = v}))
      (fun a b hab => Subtype.ext
        (congrArg (Subtype.val (p := fun v : Vtil V₀ V hV =>
          actTil V₀ V hV ⟨x, hxs⟩ v = v)) hab))
  have hmq := mSub_eq_mQuot_add V U hV hUV
  have hU' := s15_Infra_mSub_eq_rk_imgTil_add V₀ V U hV hUV
  have hrk' := rk_top_vtil_add_mSub V₀ V hV hV₀
  have h4 := S.rk_top_eq hSK
  have hmono : mSub (U ⊓ V₀) ≤ mSub V₀ := rk_mono inf_le_right
  have hrk : 2 * m + 1 ≤ rk ↥(imgTil V₀ V hV U) := by omega
  have hcard := card_eq_two_pow hW2 (imgTil V₀ V hV U)
  have hlt : 2 ^ (2 * m) < Nat.card ↥(imgTil V₀ V hV U) := by
    rw [hcard]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hSK2 : Nat.card S.K ^ 2 = 2 ^ (2 * m) := by
    rw [hSK, ← pow_mul, Nat.mul_comm m 2]
  rw [hSK2]
  exact lt_of_lt_of_le hlt hle

theorem exists_ne_one_commute_of_card_lt {C N : Subgroup G} {v : G}
    (hCN : ∀ c ∈ C, c * v * c⁻¹ * v⁻¹ ∈ N) (hcard : Nat.card N < Nat.card C) :
    ∃ c ∈ C, c ≠ 1 ∧ c * v = v * c := by
  classical
  haveI : Fintype ↥C := Fintype.ofFinite ↥C
  haveI : Fintype ↥N := Fintype.ofFinite ↥N
  have hcard' : Fintype.card ↥N < Fintype.card ↥C := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  obtain ⟨c₁, c₂, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun c : C => (⟨c * v * c⁻¹ * v⁻¹, hCN c c.2⟩ : N)) hcard'
  have heq' : (c₁ : G) * v * (c₁ : G)⁻¹ = (c₂ : G) * v * (c₂ : G)⁻¹ :=
    mul_right_cancel (congrArg (Subtype.val) heq)
  refine ⟨(c₂ : G)⁻¹ * (c₁ : G), C.mul_mem (C.inv_mem c₂.2) c₁.2, ?_, ?_⟩
  · intro h1
    refine hne (Subtype.ext ?_)
    calc (c₁ : G) = (c₂ : G) * ((c₂ : G)⁻¹ * (c₁ : G)) := by group
      _ = (c₂ : G) * 1 := by rw [h1]
      _ = (c₂ : G) := by rw [mul_one]
  · have hcv : ((c₂ : G)⁻¹ * (c₁ : G)) * v * ((c₂ : G)⁻¹ * (c₁ : G))⁻¹ = v := by
      have h2 : ((c₂ : G)⁻¹ * (c₁ : G))⁻¹ = (c₁ : G)⁻¹ * (c₂ : G) := by
        rw [mul_inv_rev, inv_inv]
      rw [h2]
      calc (c₂ : G)⁻¹ * (c₁ : G) * v * ((c₁ : G)⁻¹ * (c₂ : G))
          = (c₂ : G)⁻¹ * ((c₁ : G) * v * (c₁ : G)⁻¹) * (c₂ : G) := by group
        _ = (c₂ : G)⁻¹ * ((c₂ : G) * v * (c₂ : G)⁻¹) * (c₂ : G) := by rw [heq']
        _ = v := by group
    calc ((c₂ : G)⁻¹ * (c₁ : G)) * v
        = (((c₂ : G)⁻¹ * (c₁ : G)) * v * ((c₂ : G)⁻¹ * (c₁ : G))⁻¹)
            * ((c₂ : G)⁻¹ * (c₁ : G)) := by group
      _ = v * ((c₂ : G)⁻¹ * (c₁ : G)) := by rw [hcv]

theorem le_of_forall_centralizer_le {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (S : OmegaModel (Vtil V₀ V hV))
    (hSω : S.omega = lBar V₀ V hV L) {m : ℕ} (hSK : Nat.card S.K = 2 ^ m) {n : ℕ}
    (hn : n < 2 * m) {X : Subgroup G} (hXM : X ≤ D.M) (hX : IsElemAbelian 2 X)
    (hXcard : 2 * Nat.card ↥V₀ < Nat.card ↥X)
    (hXn : ∀ x ∈ X, E3.mQuot V (V ⊓ centralizer ({x} : Set G)) ≤ n)
    {N : Subgroup G} (hN : ∀ x ∈ X, x ≠ 1 → centralizer ({x} : Set G) ≤ N) :
    V ≤ N := by
  classical
  have hP : PairFacts D.M V₀ V := hS.setting.hyp16.hyp125.pairFacts
  have hMst : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hXst : X ≤ stabTil V₀ V := hXM.trans hMst
  have hbarN : barSub V₀ V hV X ≤
      Subgroup.normalizer (S.omega : Set (MulAut (Vtil V₀ V hV))) :=
    (barSub_mono V₀ V hV hXM).trans (Mbar_le_normalizer_lBar hS S hSω)
  have hord : ∀ g ∈ barSub V₀ V hV X, g * g = 1 := by
    intro g hg
    obtain ⟨x, hxX, rfl⟩ := (mem_barSub V₀ V hV X g).1 hg
    rw [← map_mul]
    have hx2 : x * x = 1 := Subtype.ext (by
      have := hX.2 (x : G) hxX
      simpa [pow_two] using this)
    rw [hx2, map_one]
  have hfix : ∀ g ∈ barSub V₀ V hV X, g ≠ 1 →
      Nat.card S.K ^ 2 < Nat.card {v : Vtil V₀ V hV // g v = v} := by
    intro g hg _
    obtain ⟨x, hxX, rfl⟩ := (mem_barSub V₀ V hV X g).1 hg
    exact card_fixed_gt_of_mQuot_le hP.le S hSK hn x.2 (hXn (x : G) hxX)
  have hbar2 : Nat.card ↥(barSub V₀ V hV X) ≤ 2 :=
    S.card_le_two_of_card_fixed_gt (barSub V₀ V hV X) hbarN hord hfix
  have hiso := s16c7_card_mul_card_preBarSub (V₀ := V₀) (V := V) (E := X) hV hXst
    (Q := ⊥) bot_le
  rw [Subgroup.card_bot, mul_one] at hiso
  have hCcard : Nat.card ↥V₀ < Nat.card ↥(preBarSub X V₀ V hV ⊥) := by
    have h1 : Nat.card ↥(preBarSub X V₀ V hV ⊥) * Nat.card ↥(barSub V₀ V hV X) ≤
        Nat.card ↥(preBarSub X V₀ V hV ⊥) * 2 := Nat.mul_le_mul_left _ hbar2
    omega
  intro v hv
  have hCN : ∀ c ∈ preBarSub X V₀ V hV ⊥, c * v * c⁻¹ * v⁻¹ ∈ V₀ := by
    intro c hc
    obtain ⟨-, hcs, hc'⟩ := (mem_preBarSub X V₀ V hV ⊥).1 hc
    have h1 : actTil V₀ V hV ⟨c, hcs⟩ = 1 := Subgroup.mem_bot.1 hc'
    exact (actTil_eq_one_iff V₀ V hV ⟨c, hcs⟩).1 h1 v hv
  obtain ⟨c, hcC, hc1, hcv⟩ := exists_ne_one_commute_of_card_lt hCN hCcard
  obtain ⟨hcX, -⟩ := (mem_preBarSub X V₀ V hV ⊥).1 hcC
  exact hN c hcX hc1 (Subgroup.mem_centralizer_singleton_iff.2 hcv.symm)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
