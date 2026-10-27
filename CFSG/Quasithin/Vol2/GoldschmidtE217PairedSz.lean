module

public import CFSG.Quasithin.Vol2.GoldschmidtE217Torus
public import CFSG.Quasithin.H13.QRCBenderSection
public import CFSG.Quasithin.Vol2.Ch3E213MShare

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6 E2 Ch3E213M
open CFSG.QuasithinUnique.Setup (oddResidualPreimage)

namespace E217R1

variable {G : Type} [Group G] [Finite G] {H T M V K : Subgroup G}

theorem false_of_pairedSz
    (h38 : CFSG.QuasithinUnique.Vol2Native.A38ForSQTKCat) (hS : Setting H T M V K)
    (h1 : Case1 H T M K) {n : ℕ} (hSz : IsSz n ↥(E2.star M H K))
    (hres : twoResidual M ≤ Subgroup.centralizer (V : Set G)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmp := hS.hyp.minParabolic
  have hMH : M ≤ H := hmp.maximal.1.le
  have hVH : V ≤ H := hS.hyp.le_H
  obtain ⟨T', hT', hcharH, hTn, hTM', hMH', hmax', hel, hVT', hTV', hVM', -⟩ :=
    qrcHyp_of_hyp28 hS.hyp hS.charTwo
  have := hel
  have hVQ' : 4 ≤ (V.subgroupOf H ⊓ CFSG.pCore 2 H).relIndex (V.subgroupOf H) := by
    rw [relIndex_subgroupOf_inf_pCore hVH]
    exact hS.four_le
  obtain ⟨a, ha, hna, k, _, _, hk, ⟨θ⟩⟩ := exists_equiv_suzukiGroup_of_isSz hSz
  rw [hna] at hk
  obtain ⟨t₀, ht₀T, -, hK, hc, hd⟩ := exists_paired_of_case1' h38 hS h1
  obtain ⟨φ⟩ := nonempty_mulEquiv_star hMH K
  set π := QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤) with hπ
  set K₁ := barIn M H K with hK₁
  set K₂ := K₁.map (MulAut.conj (π t₀)).toMonoidHom with hK₂
  have θ₁ : K₁ ≃* CFSG.Blueprint.suzukiGroup a k := φ.trans θ
  have θ₂ : K₂ ≃* CFSG.Blueprint.suzukiGroup a k :=
    (K₁.equivMapOfInjective _ (MulAut.conj (π t₀)).injective).symm.trans θ₁
  obtain ⟨-, -, -, hKn, hCK, hKS, ⟨hSB, hBtop, hBmax⟩, -, hEcard, hEO⟩ :=
    H13.QRC.bender_section_setup hS.not_solvable T' hTn hTM' hMH' hmax' hVT' hVM'
  rw [hK] at hKn hCK hKS
  set S := (T' : Subgroup H).map π with hSdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hS2 : IsPGroup 2 S := T'.isPGroup'.map π
  have hSsyl : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ := CFSG.ABGLocalTools.isSylowOf_iff.2
    ⟨le_top, hS2, by
      rw [Subgroup.relIndex_top_right, hSdef, ← Sylow.coe_mapSurjective hπs T']
      exact (T'.mapSurjective hπs).not_dvd_index⟩
  have hs : π t₀ ∈ S := ⟨t₀, by rw [hT']; exact ht₀T, rfl⟩
  set E := (V.subgroupOf H).map π with hEdef
  have : CFSG.IsElementaryAbelian 2 E := CFSG.IsElementaryAbelian.map π
  have hES : E ≤ S := Subgroup.map_mono hVT'
  have hSE : S ≤ Subgroup.normalizer (E : Set _) :=
    (Subgroup.map_mono hTV').trans (Subgroup.le_normalizer_map π)
  have hE4 : 4 ≤ Nat.card E := hEcard ▸ hVQ'
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : Finite (CFSG.Blueprint.suzukiGroup a k) := (CFSG.LieType.Ree.suzuki_simple ha hk).1
  have : IsSimpleGroup (CFSG.Blueprint.suzukiGroup a k) :=
    (CFSG.LieType.Ree.suzuki_simple ha hk).2.2
  have : IsSimpleGroup K₂ := θ₂.isSimpleGroup
  have hc' : ∀ a ∈ K₂, ∀ b ∈ K₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hd' : K₂ ⊓ K₁ = ⊥ := by rw [inf_comm, hd]
  have hKn' : (K₂ ⊔ K₁).Normal := by rwa [sup_comm]
  have h₁ : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ K₁) K₁ := P2.isSylowOf_inf_left hc hSsyl hKn
  have h₂ : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ K₂) K₂ := P2.isSylowOf_inf_left hc' hSsyl hKn'
  obtain ⟨U₁, hU₁⟩ := h₁.exists_sylow_eq_subgroupOf
  have hdSz := H13.QRC.benderData_suzuki ha hk
  obtain ⟨θ', hθU, -⟩ := H13.QRC.exists_mulEquiv_map_sylow θ₁ U₁.isPGroup' U₁.not_dvd_index
    hdSz.isPGroup hdSz.not_dvd_index
  have hD : H13.QRC.BenderData K₁ (U₁ : Subgroup K₁) (2 * a + 1) := by
    have h := hdSz.map θ'.symm
    rwa [H13.QRC.map_symm_eq_of_map_eq θ' hθU] at h
  have hBK₁ := P2.borel_inf_left hc hd hKn hS2 hU₁ hD h₁ h₂ hKS hs rfl hSB hBtop hBmax
  obtain ⟨h', hh', p, hp, hp2, hh'p⟩ := P2.exists_prime_orderOf_mem_normalizer hD (by omega)
  have hhB : ((h' : K₁) : ↥H ⧸ kerIn (M.subgroupOf H) ⊤) ∈ (M.subgroupOf H).map π ⊓ K₁ :=
    hBK₁ ▸ ⟨h', hh', rfl⟩
  have hEK : E ≤ K₁ ⊔ K₂ := hEO.trans (P2.pCore_le_sup ha hk θ₁ θ₂ hc hd hKn hCK hhB.1 hhB.2
    hp hp2 (by rw [Subgroup.orderOf_coe, hh'p]))
  have hEU : E ≤ S ⊓ K₁ ⊔ S ⊓ K₂ :=
    (le_inf hES hEK).trans (P2.inf_sup_eq_of_isSylowOf hc hd hS2 h₁ h₂).le
  have hcent : ∀ b ∈ (M.subgroupOf H).map π, Odd (orderOf b) → ∀ e ∈ E, b * e = e * b :=
    fun b hb hodd e he => commute_of_odd_of_twoResidual hres π hb hodd he
  have hUmap : (U₁ : Subgroup K₁).map K₁.subtype = S ⊓ K₁ := by
    rw [hU₁, Subgroup.map_subgroupOf_eq_of_le inf_le_right]
  have hE₂ : E ≤ S ⊓ K₂ :=
    le_of_paired_torus hD (by omega) hc inf_le_right (by rwa [hUmap])
      (hBK₁ ▸ inf_le_left) hcent
  have hZ₂ : ∀ z ∈ K₂, (∀ y ∈ K₂, z * y = y * z) → z = 1 := fun z hz hzc =>
    P2.eq_one_of_commute_sup hc hCK hz hzc
  have hcard : Nat.card K₂ = Nat.card K₁ :=
    (Nat.card_congr θ₂.toEquiv).trans (Nat.card_congr θ₁.toEquiv).symm
  have hK₂ne : K₂ ≠ ⊥ := fun h0 => by
    have h1 : Nat.card K₂ = 1 := by rw [h0, Subgroup.card_bot]
    rw [Nat.card_congr θ₂.toEquiv] at h1
    exact (Finite.one_lt_card_iff_nontrivial.2
      (CFSG.LieType.Ree.suzuki_simple ha hk).2.1).ne' h1
  have hs₂ := P2.map_conj_eq_left_of_swap hc hd hKn hZ₂ hcard hK₂ne rfl
  have hEs : E.map (MulAut.conj (π t₀)).toMonoidHom = E :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hSE hs)
  have hE₁ : E ≤ K₁ := by
    rw [← hEs, ← hs₂]
    exact Subgroup.map_mono (hE₂.trans inf_le_right)
  have hEb : E ≤ ⊥ := by
    rw [← hd]
    exact le_inf hE₁ (hE₂.trans inf_le_right)
  have hcard1 : Nat.card E ≤ 1 := by
    have := Subgroup.card_le_of_le hEb
    rwa [Subgroup.card_bot] at this
  omega

end E217R1

end CFSG.Quasithin
