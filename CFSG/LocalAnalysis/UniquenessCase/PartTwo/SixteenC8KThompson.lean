module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8KMeet
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8KOffender
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8KKer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem c8k_amax_le_q {Γ : Type} [Group Γ] [Finite Γ] {B S C₀ : Subgroup Γ} {d : Γ}
    {ρ : Γ →* ↥(StatedSL 2 (ZMod 7))} {O Z : Subgroup Γ} (conf : C8KConf Γ B S C₀ d)
    (nat : C8KNat Γ d ρ O Z) (hker : ρ.ker = O) (hBO : B ⊔ O = ⊤) (hOB : ¬ O ≤ B) {w : Γ}
    (hw : w ∈ S) (hw2 : w ^ 2 = 1) (hwc : ∀ s ∈ S, w * s = s * w)
    (hwB : centralizer ({w} : Set Γ) ≤ B) {A : Subgroup Γ} (hA : IsMaxElemAbelian S A) :
    A ≤ CFSG.pCore 2 Γ := by
  by_contra hAQ
  obtain ⟨a, haA, haQ⟩ := SetLike.not_le_iff_exists.mp hAQ
  obtain ⟨W, hWn, hWe, hWq, hWc, hwW⟩ := c8k_exists_W conf.sylow conf.char2 hw hw2 hwc
  obtain ⟨e, heO, hez⟩ := SetLike.not_le_iff_exists.mp
    (fun h : O ≤ Z => by simpa [nat.index] using Subgroup.relIndex_eq_one.mpr h)
  have ha2 : a ^ 2 = 1 := hA.2.1.2 a haA
  have haO : a ∉ O := by
    intro haO
    obtain ⟨n, hn⟩ := nat.seven a haO
    have h1 : a ^ 7 ^ n = a := by
      have hodd : Odd (7 ^ n) := Odd.pow (by decide)
      obtain ⟨k, hk⟩ := hodd
      rw [hk, pow_succ, pow_mul, ha2, one_pow, one_mul]
    exact haQ (h1 ▸ hn)
  have haρ : ρ a ≠ 1 := fun h => haO (hker ▸ h)
  have hxO : a * (e⁻¹ * a * e) ∈ O := by
    have h1 : a * e⁻¹ * a⁻¹ ∈ O := nat.normal.conj_mem _ (O.inv_mem heO) a
    have h2 : a * (e⁻¹ * a * e) = (a * e⁻¹ * a⁻¹) * e := by
      have : a⁻¹ = a := by
        rw [inv_eq_iff_mul_eq_one, ← sq, ha2]
      rw [this]
      group
    rw [h2]
    exact O.mul_mem h1 heO
  have hcent := c8k_transvection_product hWe
    (a := a) (b := e⁻¹ * a * e)
    (fun x hx => hWn.conj_mem x hx a) (fun x hx => by
      have := hWn.conj_mem x hx (e⁻¹ * a * e)
      exact this)
    (by simpa using c8k_offender_index conf nat hker hWn hWe hWq hWc hA haA 1)
    (c8k_offender_index conf nat hker hWn hWe hWq hWc hA haA e)
  have hx12 : (a * (e⁻¹ * a * e)) ^ 12 ∈ centralizer ({w} : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    have key := hcent w hwW
    generalize (a * (e⁻¹ * a * e)) ^ 12 = y at key ⊢
    calc w * y = (y * w * y⁻¹) * y := by rw [key]
      _ = y * w := by group
  have hz : (a * (e⁻¹ * a * e)) ^ 12 ∈ Z :=
    c8k_o_inf_b_le_z nat (conf.ctx.q_le) hBO hOB
      ⟨O.pow_mem hxO 12, hwB hx12⟩
  exact c8k_x12_not_mem_z nat ha2 haρ heO hez hz

theorem c8k_exists_char_normal_of_amax {Γ : Type} [Group Γ] [Finite Γ] {S : Subgroup Γ}
    (hS : IsSylowIn 2 S ⊤) (hS1 : S ≠ ⊥)
    (hA : ∀ A : Subgroup Γ, IsMaxElemAbelian S A → A ≤ CFSG.pCore 2 Γ) :
    ∃ C : Subgroup Γ, C ≠ ⊥ ∧ C ≤ S ∧ (C.subgroupOf S).Characteristic ∧ C.Normal := by
  haveI : (CFSG.pCore 2 Γ).Normal := CFSG.pCore_normal
  have hQS : CFSG.pCore 2 Γ ≤ S :=
    hS.le_of_normal le_top inferInstance CFSG.pCore_isPGroup
  have hJQ : thompsonJ S ≤ CFSG.pCore 2 Γ := iSup₂_le fun A hA' => hA A hA'
  have hEq : thompsonJ (CFSG.pCore 2 Γ) = thompsonJ S :=
    CFSG.Quasithin.B6.thompsonJ_eq_of_le hJQ hQS
  have hn : Subgroup.normalizer ((CFSG.pCore 2 Γ : Subgroup Γ) : Set Γ) = ⊤ :=
    Subgroup.normalizer_eq_top (CFSG.pCore 2 Γ)
  have hnorm : (thompsonJ S).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr fun g _ => by
      rw [← hEq]
      exact CFSG.Quasithin.normalizer_le_normalizer_thompsonJ (CFSG.pCore 2 Γ)
        (by rw [hn]; exact Subgroup.mem_top g))
  exact ⟨thompsonJ S, CFSG.QuasithinUnique.Setup.thompsonJ_ne_bot hS.isPGroup hS1,
    CFSG.Quasithin.B6.thompsonJ_le S,
    CFSG.QuasithinUnique.Setup.characteristic_thompsonJ S, hnorm⟩

theorem c8k_exists_char_normal {Γ : Type} [Group Γ] [Finite Γ] {B S C₀ : Subgroup Γ} {d : Γ}
    {ρ : Γ →* ↥(StatedSL 2 (ZMod 7))} {O Z : Subgroup Γ} (conf : C8KConf Γ B S C₀ d)
    (nat : C8KNat Γ d ρ O Z) {w : Γ} (hw : w ∈ S) (hw1 : w ≠ 1) (hw2 : w ^ 2 = 1)
    (hwc : ∀ s ∈ S, w * s = s * w) (hwB : centralizer ({w} : Set Γ) ≤ B) :
    ∃ C : Subgroup Γ, C ≠ ⊥ ∧ C ≤ S ∧ (C.subgroupOf S).Characteristic ∧ C.Normal := by
  have hker := c8k_ker_eq_o conf nat
  have hOB := c8k_not_o_le_b conf nat
  have hBO := c8k_b_sup_o conf nat hker
  refine c8k_exists_char_normal_of_amax conf.sylow ?_ fun A hA =>
    c8k_amax_le_q conf nat hker hBO hOB hw hw2 hwc hwB hA
  intro h
  exact hw1 (Subgroup.mem_bot.mp (h ▸ hw))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
