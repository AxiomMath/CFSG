module

public import CFSG.Quasithin.Background.C48PfFourModPf

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.C48Pf.FMod

open Matrix CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Assembly.LowTwoRank

theorem card_le_of_injective_subgroupOf {G : Type} [Group G] {U V : Subgroup G} (hVU : V ≤ U)
    {M : Type} [Group M] [Finite M] (Ψ : ↥(V.subgroupOf U) →* M) (hΨ : Function.Injective Ψ) :
    Nat.card ↥V ≤ Nat.card M := by
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVU).toEquiv]
  exact Nat.card_le_card_of_injective Ψ hΨ

theorem card_multiplicative_fin_fin (k m : ℕ) :
    Nat.card (Multiplicative (Fin k → Fin m → ZMod 2)) = 2 ^ (k * m) := by
  rw [Nat.card_eq_fintype_card]
  simp only [Fintype.card_multiplicative, Fintype.card_fun, Fintype.card_fin, ZMod.card]
  rw [← pow_mul, mul_comm]

theorem card_multiplicative_fin (d : ℕ) :
    Nat.card (Multiplicative (Fin d → ZMod 2)) = 2 ^ d := by
  rw [Nat.card_eq_fintype_card]
  simp only [Fintype.card_multiplicative, Fintype.card_fun, Fintype.card_fin, ZMod.card]

theorem card_le_of_inj_single {G : Type} [Group G] {U V : Subgroup G} (hVU : V ≤ U) {m : ℕ}
    (hm : m ≤ 6) (Ψ : ↥(V.subgroupOf U) →* Multiplicative (Fin 1 → Fin m → ZMod 2))
    (hΨ : Function.Injective Ψ) : Nat.card ↥V ≤ 2 ^ 6 := by
  have h := card_le_of_injective_subgroupOf hVU Ψ hΨ
  rw [card_multiplicative_fin_fin] at h
  exact h.trans (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem card_le_of_inj_six {G : Type} [Group G] {U V : Subgroup G} (hVU : V ≤ U)
    (Ψ : ↥(V.subgroupOf U) →* Multiplicative (Fin 6 → ZMod 2)) (hΨ : Function.Injective Ψ) :
    Nat.card ↥V ≤ 2 ^ 6 := by
  have h := card_le_of_injective_subgroupOf hVU Ψ hΨ
  rwa [card_multiplicative_fin] at h

section Cases

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {K U P P₀ V : Subgroup G} (hU : IsElemAbelian 2 U)
  (hKU : K ≤ Subgroup.normalizer (U : Set G))
  (hCK : K ⊓ Subgroup.centralizer (U : Set G) ≤ pCoreOf 2 K)
  (hpar : IsParabolic2 K P) (hPK : P ≠ K) (hP₀P : P₀ ≤ P)
  (hPN : P ≤ Subgroup.normalizer (P₀ : Set G)) (hperf : ⁅P₀, P₀⁆ = P₀)
  {m : ℕ} (hm : m = 3 ∨ m = 4) (hpm : IsPSL m 2 1 (ModO2 P₀))
  (hV1 : V ≠ ⊥) (hVU : V ≤ U) (hVO : V ≤ Subgroup.centralizer (pCoreOf 2 P₀ : Set G))
  (hVcomm : ⁅V, P₀⁆ = V)
  (hVL : V.subgroupOf U ≤ @commV ↥U (commGroupOfElemAbelian hU) (autOn K U))

include hKU hCK hpar hPK hP₀P hPN hperf hm hpm hV1 hVU hVO hVcomm hVL

theorem card_le_ext5
    (h5 : @SLExteriorTwo ↥U (commGroupOfElemAbelian hU) (autOn K U)
      (@commV ↥U (commGroupOfElemAbelian hU) (autOn K U)) ⊥ 5) :
    Nat.card ↥V ≤ 2 ^ 6 := by
  classical
  let _ : CommGroup ↥U := commGroupOfElemAbelian hU
  obtain ⟨π, hπ⟩ := h5
  have hπb : Function.Bijective π :=
    ⟨injective_of_realizesVia (G64.extSq_faithful (by norm_num)) hπ, hπ.1⟩
  obtain ⟨g, a, hamn, α, θ, hαs, hker, hblk, hρθ, ctx⟩ :=
    reduction hU hKU hCK hpar hPK hP₀P hPN hperf hm hpm hV1 hVU hVO hVcomm (by norm_num) le_rfl
      π hπb
  have hπ' := B69.realizesVia_conj_of_isActionModel (FFModel.extSq_isActionModel (ZMod 2) 5) hπ
    (specialLinearGroupEquivStatedSL 5 (ZMod 2) g)
  obtain ⟨Φ, hΦalt, hΦinj, -, hΦ⟩ := ext5Coords hπ'
  obtain ⟨hm3, -, hprop, hA, hVA, hgen, hcross, hne⟩ := ctx
  rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2) with rfl | rfl | rfl
  · rcases hm with rfl | rfl
    · obtain ⟨Ψ', hΨ'i, -⟩ :=
        extSq_zero_three hΦalt hΦinj hΦ hVL (A := θ.range) hamn hcross
      exact card_le_of_inj_single hVU (by norm_num) Ψ' hΨ'i
    · obtain ⟨Ψ', hΨ'i, -⟩ :=
        extSq_zero_four hΦalt hΦinj hΦ hVL (A := θ.range) hamn hcross
      exact card_le_of_inj_six hVU Ψ' hΨ'i
  · obtain ⟨Ψ', hΨ'i, -⟩ := extSq_one hΦalt hΦinj hΦ hVL (by omega) hamn hA hcross
    exact card_le_of_inj_single hVU (by omega) Ψ' hΨ'i
  · exact absurd (eq_bot_of_forall_fixed hgen
      (extSq_two hΦalt hΦinj hΦ hVL (by omega) hA hVA hcross)) hne

theorem card_le_ext4 {Z : Subgroup ↥U}
    (hZ : Z ≤ @fixV ↥U (commGroupOfElemAbelian hU) (autOn K U) ⊓
      @commV ↥U (commGroupOfElemAbelian hU) (autOn K U))
    (hZ2 : Nat.card Z ≤ 2)
    (h4 : @SLExteriorTwo ↥U (commGroupOfElemAbelian hU) (autOn K U)
      (@commV ↥U (commGroupOfElemAbelian hU) (autOn K U)) Z 4) :
    Nat.card ↥V ≤ 2 ^ 6 := by
  classical
  have hW2 : ∀ w : ↥U, w ^ 2 = 1 := fun w => Subtype.ext (hU.2 w w.2)
  let _ : CommGroup ↥U := commGroupOfElemAbelian hU
  obtain ⟨π, hπ⟩ := h4
  have hπb : Function.Bijective π :=
    ⟨injective_of_realizesVia (G64.extSq_faithful (by norm_num)) hπ, hπ.1⟩
  obtain ⟨g, a, hamn, α, θ, hαs, hker, hblk, hρθ, ctx⟩ :=
    reduction hU hKU hCK hpar hPK hP₀P hPN hperf hm hpm hV1 hVU hVO hVcomm le_rfl (by norm_num)
      π hπb
  have hπ' := B69.realizesVia_conj_of_isActionModel (FFModel.extSq_isActionModel (ZMod 2) 4) hπ
    (specialLinearGroupEquivStatedSL 4 (ZMod 2) g)
  obtain ⟨q, hqs, hqk, hinv, hqe⟩ := ext4Coords hπ'
  obtain ⟨hm3, -, hprop, hA, hVA, hgen, hcross, hne⟩ := ctx
  obtain rfl : m = 3 := by omega
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  rcases (by omega : Nat.card Z = 1 ∨ Nat.card Z = 2) with hZ1 | hZ2'
  · obtain rfl : Z = ⊥ := Subgroup.eq_bot_of_card_eq Z hZ1
    obtain ⟨Φ, hΦalt, hΦinj, hΦ⟩ := alt4Coords q hqk hqe
    rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
    · obtain ⟨Ψ', hΨ'i, -⟩ :=
        extSq_zero_three hΦalt hΦinj hΦ hVL (A := θ.range) hamn hcross
      exact card_le_of_inj_single hVU (by norm_num) Ψ' hΨ'i
    · obtain ⟨Ψ', hΨ'i, -⟩ := extSq_one hΦalt hΦinj hΦ hVL (by norm_num) hamn hA hcross
      exact card_le_of_inj_single hVU (by norm_num) Ψ' hΨ'i
  · exfalso
    have hZL : Z ≤ @commV ↥U (commGroupOfElemAbelian hU) (autOn K U) := fun z hz => (hZ hz).2
    have hcomm := commV_le_closure (by norm_num) hπ'.1
    apply hne
    refine eq_bot_of_forall_fixed hgen fun t _ v hv => ?_
    have hvZ : v ∈ Z := by
      rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
      · refine cover_fixed_031 hW2 hZL hZ2' hinv (fun γ w hw => (hZ hw).1 _ (FLc.rhoOf_mem _ γ))
          hqs hqk hqe hcomm (hVL hv) fun i => ?_
        fin_cases i
        · exact hcross 0 3 (Or.inr ⟨by decide, by decide, by decide⟩) v hv
        · exact hcross 1 3 (Or.inr ⟨by decide, by decide, by decide⟩) v hv
        · exact hcross 2 3 (Or.inr ⟨by decide, by decide, by decide⟩) v hv
      · refine cover_fixed_130 hW2 hZL hZ2' hinv (fun γ w hw => (hZ hw).1 _ (FLc.rhoOf_mem _ γ))
          hqs hqk hqe hcomm (hVL hv) fun i => ?_
        fin_cases i
        · exact hcross 0 1 (Or.inl ⟨by decide, by decide, by decide⟩) v hv
        · exact hcross 0 2 (Or.inl ⟨by decide, by decide, by decide⟩) v hv
        · exact hcross 0 3 (Or.inl ⟨by decide, by decide, by decide⟩) v hv
    exact (hZ hvZ).1 _ (FLc.rhoOf_mem _ t)

theorem card_le_natDual {n : ℕ}
    (hnd : @SumNatDual ↥U (commGroupOfElemAbelian hU) (autOn K U)
      (@commV ↥U (commGroupOfElemAbelian hU) (autOn K U)) n) :
    Nat.card ↥V ≤ 2 ^ 6 := by
  classical
  let _ : CommGroup ↥U := commGroupOfElemAbelian hU
  obtain ⟨hn, π, U₁, U₂, ⟨hsup, hinf⟩, h₁, h₂⟩ := hnd
  obtain ⟨β₀, -, hβ₀s, hinv₀, hβ₀e, hπs⟩ := natCoords h₁
  have hπb : Function.Bijective π := ⟨injective_of_natCoords β₀ hβ₀s hinv₀ hβ₀e, hπs⟩
  obtain ⟨g, a, hamn, α, θ, hαs, hker, hblk, hρθ, ctx⟩ :=
    reduction hU hKU hCK hpar hPK hP₀P hPN hperf hm hpm hV1 hVU hVO hVcomm (by omega) (by omega)
      π hπb
  have h₁' := B69.realizesVia_conj_of_isActionModel (FFModel.nat_isActionModel _) h₁
    (specialLinearGroupEquivStatedSL n (ZMod 2) g)
  have h₂' := B69.realizesVia_conj_of_isActionModel (FFModel.dualNat_isActionModel _) h₂
    (specialLinearGroupEquivStatedSL n (ZMod 2) g)
  obtain ⟨β₁, hβ₁i, -, hinv₁, hβ₁e, -⟩ := natCoords h₁'
  obtain ⟨β₂, hβ₂i, -, hinv₂, hβ₂e⟩ := dualCoords h₂'
  obtain ⟨hm3, -, hprop, hA, hVA, hgen, hcross, hne⟩ := ctx
  have hVU' : V.subgroupOf U ≤ U₁ ⊔ U₂ := by
    rw [hsup]
    exact hVL
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have hV₁ := natDual_zero_le (by omega) (by omega) hA hinf hinv₁ hinv₂ hβ₂i hβ₂e hVU' hgen
      hcross
    obtain ⟨Ψ', hΨ'i, -⟩ := natSum_zero (k := 1) (by omega) hamn hA (fun _ => U₁)
      (indep_fin_one U₁) (fun _ => hinv₁) (fun _ => β₁) (fun _ => hβ₁i) (fun _ => hβ₁e)
      (hV₁.trans (le_iSup (fun _ : Fin 1 => U₁) 0)) hcross
    exact card_le_of_inj_single hVU (by omega) Ψ' hΨ'i
  · rcases (by omega : a + m = n ∨ a + m < n) with hlast | hmid
    · have hV₂ := natDual_last_le ha (by omega) hlast hA hinf hinv₁ hinv₂ hβ₁i hβ₁e hVU' hgen
        hcross
      obtain ⟨Ψ', hΨ'i, -⟩ := dualSingle_last (by omega) hamn hlast hA hβ₂i hβ₂e hV₂ hcross
      exact card_le_of_inj_single hVU (by omega) Ψ' hΨ'i
    · exact absurd (eq_bot_of_forall_fixed hgen (natDual_mid ha (by omega) hmid hA hinf hinv₁
        hinv₂ hβ₁i hβ₁e hβ₂i hβ₂e hVU' hcross)) hne

theorem card_le_of_alt123
    (halt : (∃ Z : Subgroup ↥U, Z ≤ @fixV ↥U (commGroupOfElemAbelian hU) (autOn K U) ⊓
        @commV ↥U (commGroupOfElemAbelian hU) (autOn K U) ∧ Nat.card Z ≤ 2 ∧
        @SLExteriorTwo ↥U (commGroupOfElemAbelian hU) (autOn K U)
          (@commV ↥U (commGroupOfElemAbelian hU) (autOn K U)) Z 4) ∨
      @SLExteriorTwo ↥U (commGroupOfElemAbelian hU) (autOn K U)
        (@commV ↥U (commGroupOfElemAbelian hU) (autOn K U)) ⊥ 5 ∨
      (∃ n : ℕ, @SumNatDual ↥U (commGroupOfElemAbelian hU) (autOn K U)
        (@commV ↥U (commGroupOfElemAbelian hU) (autOn K U)) n)) :
    Nat.card ↥V ≤ 2 ^ 6 := by
  rcases halt with ⟨Z, hZ, hZ2, h4⟩ | h5 | ⟨n, hnd⟩
  · exact card_le_ext4 hU hKU hCK hpar hPK hP₀P hPN hperf hm hpm hV1 hVU hVO hVcomm hVL hZ hZ2 h4
  · exact card_le_ext5 hU hKU hCK hpar hPK hP₀P hPN hperf hm hpm hV1 hVU hVO hVcomm hVL h5
  · exact card_le_natDual hU hKU hCK hpar hPK hP₀P hPN hperf hm hpm hV1 hVU hVO hVcomm hVL hnd

end Cases

end CFSG.Quasithin.C48Pf.FMod
