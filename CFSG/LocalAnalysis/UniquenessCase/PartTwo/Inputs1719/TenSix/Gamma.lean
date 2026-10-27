module

public import CFSG.Quasithin.Background.E3Defs
import CFSG.Quasithin.Background.E3Basic
import CFSG.Quasithin.Background.FixVLattice
import CFSG.Quasithin.Background.OddCoprimeFixV
import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma1547Module
import CFSG.GroupTheory.PCore.NormalPCoreOf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix

open CFSG.Quasithin CFSG.Open Subgroup

section Gamma

variable {G : Type*} [Group G]

@[expose] def gammaRk (m : ℕ) (A Y : Subgroup G) : Subgroup G :=
  ⨆ (D : Subgroup G) (_ : D ≤ A) (_ : 2 ^ m ≤ Nat.card D), Y ⊓ normalizer (D : Set G)

theorem gammaRk_le (m : ℕ) (A Y : Subgroup G) : gammaRk m A Y ≤ Y := by
  unfold gammaRk
  exact iSup_le fun D => iSup_le fun _ => iSup_le fun _ => inf_le_left

theorem inf_normalizer_le_gammaRk {m : ℕ} {A Y D : Subgroup G} (hDA : D ≤ A)
    (hD : 2 ^ m ≤ Nat.card D) : Y ⊓ normalizer (D : Set G) ≤ gammaRk m A Y := by
  unfold gammaRk
  exact le_iSup_of_le D (le_iSup_of_le hDA (le_iSup_of_le hD le_rfl))

theorem gammaRk_mono {m : ℕ} {A Y Y' : Subgroup G} (h : Y ≤ Y') :
    gammaRk m A Y ≤ gammaRk m A Y' := by
  unfold gammaRk
  refine iSup_le fun D => iSup_le fun hD => iSup_le fun hDm => ?_
  exact le_iSup_of_le D (le_iSup_of_le hD (le_iSup_of_le hDm (inf_le_inf_right _ h)))

end Gamma

section Module

variable {W : Type} [CommGroup W] [Finite W]

theorem eq_one_of_odd_of_isPGroup_le_normalizer (hW : ∀ w : W, w ^ 2 = 1)
    {Y P : Subgroup (MulAut W)} (hP : IsPGroup 2 P) (hfix : fixV P = fixV Y) {x : MulAut W}
    (hxY : x ∈ Y) (hodd : Odd (orderOf x))
    (hN : P ≤ Subgroup.normalizer (Subgroup.zpowers x : Set (MulAut W))) : x = 1 := by
  by_contra hx1
  have hodd' : Odd (Nat.card (Subgroup.zpowers x)) := by rwa [Nat.card_zpowers]
  have hne : commV (Subgroup.zpowers x) ≠ ⊥ := by
    intro hbot
    have hmem := CFSG.Quasithin.FixVLat.eq_bot_of_commV_eq_bot hbot
    exact hx1 (Subgroup.mem_bot.mp (hmem ▸ Subgroup.mem_zpowers x))
  have hinv : ∀ p ∈ P, ∀ m ∈ commV (Subgroup.zpowers x), p m ∈ commV (Subgroup.zpowers x) :=
    fun p hp m hm => CFSG.Quasithin.commV_apply_mem_of_mem_normalizer (hN hp) hm
  have hU2 : IsPGroup 2 (commV (Subgroup.zpowers x)) :=
    CFSG.Quasithin.isPGroup_two_of_sq_eq_one fun u => Subtype.ext (by simpa using hW (u : W))
  obtain ⟨w, hwU, hw1, hwfix⟩ :=
    CFSG.Quasithin.EmptyFaithfulMultiple.L1547.exists_fixed_of_isPGroup hP hinv hne hU2
  have hwP : w ∈ fixV P := mem_fixV.mpr hwfix
  have hwY : w ∈ fixV Y := hfix ▸ hwP
  have hwX : w ∈ fixV (Subgroup.zpowers x) :=
    mem_fixV.mpr fun y hy => mem_fixV.1 hwY y (Subgroup.zpowers_le.mpr hxY hy)
  have hbot := CFSG.Quasithin.commV_inf_fixV_eq_bot_of_odd_card hW (Subgroup.zpowers x) hodd'
  exact hw1 (Subgroup.mem_bot.mp (hbot ▸ ⟨hwU, hwX⟩))

theorem le_pCoreOf_inf_centralizer_of_mem_aSet (hW : ∀ w : W, w ^ 2 = 1) {k : ℕ}
    {Y A B : Subgroup (MulAut W)} (hA : A ∈ E3.aSet k Y) (hAY : fixV A = fixV Y) (hBA : B ≤ A)
    (hm : E3.mQuot A B = k) :
    A ≤ pCoreOf 2 (Y ⊓ centralizer (B : Set (MulAut W))) := by
  classical
  have hA2 : IsPGroup 2 A := E3.isPGroup_of_isElemAbelian2 hA.2.2.1
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := hA.2.2.1.1
  have hsq : ∀ a ∈ A, a ^ 2 = 1 := hA.2.2.1.2
  have hcz : ∀ x : MulAut W,
      Subgroup.centralizer ((Subgroup.zpowers x : Subgroup (MulAut W)) : Set (MulAut W)) =
        Subgroup.centralizer ({x} : Set (MulAut W)) := fun x => by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hAH : A ≤ Y ⊓ centralizer (B : Set (MulAut W)) := fun a ha =>
    ⟨hA.1 ha, Subgroup.mem_centralizer_iff.mpr fun b hb => (hAab a ha b (hBA hb)).symm⟩
  have hzpow : ∀ a ∈ A, IsPGroup 2 (Subgroup.zpowers a) := by
    intro a ha
    rcases eq_or_ne a 1 with rfl | ha1
    · rw [Subgroup.zpowers_one_eq_bot]
      exact IsPGroup.of_bot
    · have horda : orderOf a = 2 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one (hsq a ha)) with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) ha1
        · exact h
      exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, horda]; norm_num)
  intro a ha
  rcases eq_or_ne a 1 with rfl | ha1
  · exact (pCoreOf 2 (Y ⊓ centralizer (B : Set (MulAut W)))).one_mem
  have haH : a ∈ Y ⊓ centralizer (B : Set (MulAut W)) := hAH ha
  by_cases haB : a ∈ B
  ·
    have hcent : Y ⊓ centralizer (B : Set (MulAut W)) ≤
        Subgroup.centralizer ((Subgroup.zpowers a) : Set (MulAut W)) := by
      rw [hcz a]
      intro h hh
      exact Subgroup.mem_centralizer_iff.mpr fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact Subgroup.mem_centralizer_iff.mp hh.2 a haB
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (Subgroup.zpowers_le.mpr haH)
      (hcent.trans (Subgroup.centralizer_le_normalizer _)) (hzpow a ha) (Subgroup.mem_zpowers a)
  ·
    have hPA : B ⊔ Subgroup.zpowers a ≤ A := sup_le hBA (Subgroup.zpowers_le.mpr ha)
    have hP2 : IsPGroup 2 ↥(B ⊔ Subgroup.zpowers a) := hA2.to_le hPA
    have hBP : B ≤ B ⊔ Subgroup.zpowers a := le_sup_left
    have hne : B ≠ B ⊔ Subgroup.zpowers a := by
      intro heq
      exact haB (le_of_eq heq.symm (Subgroup.mem_sup_right (Subgroup.mem_zpowers a)))
    have hlt : E3.mQuot A (B ⊔ Subgroup.zpowers a) < k := by
      have hadd := E3.mQuot_add (V := A) (U := B) (U' := B ⊔ Subgroup.zpowers a) hBP hPA
      have hpos : 0 < E3.mQuot (B ⊔ Subgroup.zpowers a) B := by
        rcases Nat.eq_zero_or_pos (E3.mQuot (B ⊔ Subgroup.zpowers a) B) with h0 | h0
        · exact absurd ((E3.mQuot_eq_zero_iff hP2 hBP).mp h0) hne
        · exact h0
      omega
    have hfixP : fixV (B ⊔ Subgroup.zpowers a) = fixV Y :=
      (hA.2.2.2 _ hPA hlt).trans hAY
    by_contra hnot
    have hXc : ¬ Subgroup.zpowers (⟨a, haH⟩ : ↥(Y ⊓ centralizer (B : Set (MulAut W)))) ≤
        CFSG.Open.pCore 2 ↥(Y ⊓ centralizer (B : Set (MulAut W))) := by
      intro hle
      have hmem : (⟨a, haH⟩ : ↥(Y ⊓ centralizer (B : Set (MulAut W)))) ∈
          CFSG.Open.pCore 2 ↥(Y ⊓ centralizer (B : Set (MulAut W))) :=
        hle (Subgroup.mem_zpowers _)
      exact hnot (Subgroup.mem_map_of_mem _ hmem)
    have hXcard : Nat.card (Subgroup.zpowers (⟨a, haH⟩ :
        ↥(Y ⊓ centralizer (B : Set (MulAut W))))) = 2 := by
      have horda : orderOf a = 2 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one (hsq a ha)) with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) ha1
        · exact h
      rw [Nat.card_zpowers, ← Subgroup.orderOf_coe, horda]
    obtain ⟨y, hy1, hyodd, hyinv⟩ :=
      CFSG.Quasithin.baer_suzuki_involution (G := ↥(Y ⊓ centralizer (B : Set (MulAut W))))
        (X := Subgroup.zpowers (⟨a, haH⟩ : ↥(Y ⊓ centralizer (B : Set (MulAut W))))) hXcard hXc
    have haconj : a * (y : MulAut W) * a⁻¹ = (y : MulAut W)⁻¹ := by
      have hy := hyinv ⟨a, haH⟩ (Subgroup.mem_zpowers _) (fun h => ha1 (Subtype.ext_iff.mp h))
      simpa using congrArg Subtype.val hy
    have hyY : (y : MulAut W) ∈ Y := y.2.1
    have hyodd' : Odd (orderOf (y : MulAut W)) := by rwa [← Subgroup.orderOf_coe y] at hyodd
    have hPn : B ⊔ Subgroup.zpowers a ≤
        Subgroup.normalizer (Subgroup.zpowers (y : MulAut W) : Set (MulAut W)) := by
      refine sup_le ?_ ?_
      · have h1 : B ≤ Subgroup.centralizer ((Subgroup.zpowers (y : MulAut W) :
            Subgroup (MulAut W)) : Set (MulAut W)) := by
          rw [hcz (y : MulAut W)]
          intro b hb
          exact Subgroup.mem_centralizer_iff.mpr fun z hz => by
            rw [Set.mem_singleton_iff] at hz
            rw [hz]
            exact (Subgroup.mem_centralizer_iff.mp y.2.2 b hb).symm
        exact h1.trans (Subgroup.centralizer_le_normalizer _)
      · rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
        change Subgroup.zpowers (a * (y : MulAut W) * a⁻¹) = Subgroup.zpowers (y : MulAut W)
        rw [haconj, Subgroup.zpowers_inv]
    exact hy1 (Subtype.ext (eq_one_of_odd_of_isPGroup_le_normalizer hW hP2 hfixP hyY hyodd' hPn))

theorem le_pCoreOf_gammaRk_inf_centralizer (hW : ∀ w : W, w ^ 2 = 1) {k n : ℕ}
    {Y A B : Subgroup (MulAut W)} (hk : 0 < k) (hA : A ∈ E3.aSet k Y)
    (hAn : Nat.card A = 2 ^ n) (hBA : B ≤ A) (hm : E3.mQuot A B = k) :
    A ≤ pCoreOf 2 (gammaRk (n + 1 - k) A Y ⊓ centralizer (B : Set (MulAut W))) := by
  classical
  have hA2 : IsPGroup 2 A := E3.isPGroup_of_isElemAbelian2 hA.2.2.1
  set m : ℕ := n + 1 - k with hm_def
  set U : Subgroup W := fixV A with hU
  set Γ : Subgroup (MulAut W) := gammaRk m A Y with hΓ
  have hkn : k ≤ n := by
    have hcard : Nat.card A = 2 ^ E3.mQuot A ⊥ := by
      rw [E3.card_eq_two_pow_mul hA2 (bot_le : (⊥ : Subgroup (MulAut W)) ≤ A),
        Subgroup.card_bot, mul_one]
    have hmq : E3.mQuot A ⊥ = n := by
      have h2 : 2 ^ n = 2 ^ E3.mQuot A ⊥ := by rw [← hAn, hcard]
      exact (Nat.pow_right_injective le_rfl h2).symm
    exact (E3.le_mQuot_bot_of_mem_aSet hA).trans (le_of_eq hmq)
  have hmle : m ≤ n := by omega
  have hmq_lt : ∀ D : Subgroup (MulAut W), D ≤ A → 2 ^ m ≤ Nat.card D → E3.mQuot A D < k := by
    intro D hDA hD
    have hcardD : Nat.card A = 2 ^ E3.mQuot A D * Nat.card D := E3.card_eq_two_pow_mul hA2 hDA
    have hle : E3.mQuot A D + m ≤ n := by
      have hpow : 2 ^ (E3.mQuot A D + m) ≤ 2 ^ n := by
        rw [← hAn, hcardD]
        calc 2 ^ (E3.mQuot A D + m) = 2 ^ E3.mQuot A D * 2 ^ m := pow_add _ _ _
          _ ≤ 2 ^ E3.mQuot A D * Nat.card D := by gcongr
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpow
    omega
  have hstab : Γ ≤ stabSub U := by
    rw [hΓ]
    unfold gammaRk
    refine iSup_le fun D => iSup_le fun hDA => iSup_le fun hD => ?_
    have hfixD : fixV D = U := (hA.2.2.2 D hDA (hmq_lt D hDA hD)).trans hU.symm
    have h1 : Y ⊓ normalizer (D : Set (MulAut W)) ≤ stabSub (fixV D) :=
      CFSG.Quasithin.FixVLat.le_stabSub_fixV_of_le_normalizer inf_le_right
    rwa [hfixD] at h1
  have hAΓ : A ≤ Γ := by
    have h2mA : 2 ^ m ≤ Nat.card A := by
      rw [hAn]
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mpr hmle
    have h1 : A ≤ Y ⊓ normalizer (A : Set (MulAut W)) := le_inf hA.1 Subgroup.le_normalizer
    rw [hΓ]
    exact h1.trans (inf_normalizer_le_gammaRk (m := m) (A := A) (Y := Y) (D := A) le_rfl h2mA)
  set Γ₀ : Subgroup (MulAut W) := Γ ⊓ centSub U with hΓ₀
  have hAΓ₀ : A ≤ Γ₀ := by
    rw [hΓ₀]
    refine le_inf hAΓ fun a ha => ?_
    rw [mem_centSub]
    intro u hu
    have huA : u ∈ fixV A := by rwa [hU] at hu
    exact mem_fixV.1 huA a ha
  have hfixΓ₀ : fixV A = fixV Γ₀ := by
    refine le_antisymm ?_ ?_
    · intro u hu
      rw [mem_fixV]
      intro g hg
      rw [hΓ₀] at hg
      have huU : u ∈ U := by rw [hU]; exact hu
      exact mem_centSub.1 hg.2 u huU
    · intro u hu
      rw [mem_fixV]
      intro a ha
      exact mem_fixV.1 hu a (hAΓ₀ ha)
  have hstabCent : Γ ≤ Subgroup.normalizer (centSub U : Set (MulAut W)) := by
    have key : ∀ h : MulAut W, h ∈ stabSub U → ∀ y ∈ centSub U, h * y * h⁻¹ ∈ centSub U := by
      intro h hh y hy u hu
      have h1 : h⁻¹ u ∈ U := (mem_stabSub.mp ((stabSub U).inv_mem hh) u).2 hu
      show h (y (h⁻¹ u)) = u
      rw [mem_centSub.mp hy (h⁻¹ u) h1]
      simp
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨key g (hstab hg) x, fun hx => by
      have h2 := key g⁻¹ ((stabSub U).inv_mem (hstab hg)) (g * x * g⁻¹) hx
      convert h2 using 1
      group⟩
  have hnormΓ₀ : Γ ≤ Subgroup.normalizer (Γ₀ : Set (MulAut W)) := by
    rw [hΓ₀]
    exact (le_inf Subgroup.le_normalizer hstabCent).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hG0le : Γ₀ ≤ Γ := by rw [hΓ₀]; exact inf_le_left
  have hG0normal : (Γ₀.subgroupOf Γ).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hG0le).mpr hnormΓ₀
  have hA' : A ∈ E3.aSet k Γ₀ := ⟨hAΓ₀, hA.2.1, hA.2.2.1, hA.2.2.2⟩
  have hpc : A ≤ pCoreOf 2 (Γ₀ ⊓ centralizer (B : Set (MulAut W))) :=
    le_pCoreOf_inf_centralizer_of_mem_aSet hW hA' hfixΓ₀ hBA hm
  have hle_inf : Γ₀ ⊓ centralizer (B : Set (MulAut W)) ≤
      Γ ⊓ centralizer (B : Set (MulAut W)) := inf_le_inf_right _ hG0le
  have hnormX : Γ ⊓ centralizer (B : Set (MulAut W)) ≤
      Subgroup.normalizer ((Γ₀ ⊓ centralizer (B : Set (MulAut W))) : Set (MulAut W)) := by
    have h1 : Γ ⊓ centralizer (B : Set (MulAut W)) ≤
        Subgroup.normalizer (Γ₀ : Set (MulAut W)) := inf_le_left.trans hnormΓ₀
    have h2 : Γ ⊓ centralizer (B : Set (MulAut W)) ≤
        Subgroup.normalizer (centralizer (B : Set (MulAut W)) : Set (MulAut W)) :=
      inf_le_right.trans Subgroup.le_normalizer
    exact (le_inf h1 h2).trans Subgroup.inf_normalizer_le_normalizer_inf
  exact hpc.trans (CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hle_inf hnormX)

end Module

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix
