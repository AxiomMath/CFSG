module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5FA
import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FSmallGlue
import CFSG.LocalAnalysis.UniquenessCase.UC22S2121E3S13
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Cong
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4XC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22r3e5_exists_centralizing {Q E : Type} [Group Q] [Finite Q] [Group E] [Finite E]
    {p : ℕ} (hp : p.Prime) (hE : IsElemAbelian p (⊤ : Subgroup E)) {F : Subgroup Q}
    (hZ : center ↥F = ⊥) (hrk : CFSG.Open.pRank p (⊤ : Subgroup ↥F) ≤ 1)
    (φ : E →* Q) (hφ : ∀ e, φ e ∈ normalizer (F : Set Q))
    (hinn : ∀ e : E, F.normalizerMonoidHom (φ.codRestrict _ hφ e) ∈
      (MulAut.conj : ↥F →* MulAut ↥F).range) :
    ∃ N : Subgroup E, N.index ≤ p ∧ ∀ e ∈ N, ∀ f ∈ F, φ e * f = f * φ e := by
  have : Fact p.Prime := ⟨hp⟩
  let ψ : E →* MulAut ↥F := F.normalizerMonoidHom.comp (φ.codRestrict _ hφ)
  refine ⟨ψ.ker, ?_, fun e he f hf => ?_⟩
  · rw [Subgroup.index_ker]
    have hR : IsElemAbelian p ψ.range := by
      rw [MonoidHom.range_eq_map]
      exact CFSG.SectionRank.isElemAbelian_map hE ψ
    have hin : ψ.range ≤ (MulAut.conj : ↥F →* MulAut ↥F).range := by
      rintro _ ⟨e, rfl⟩
      exact hinn e
    obtain ⟨P, hP, hPc⟩ := CFSG.LocalAnalysis.GLTheoremA.I141F.i141f_elemAb_of_le_inn hZ hR hin
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hP.isPGroup
    have hk1 := (CFSG.SectionRank.le_pRank hp.one_lt (le_top : P ≤ ⊤) hP hk).trans hrk
    rw [← hPc, hk]
    exact (Nat.pow_le_pow_right hp.pos hk1).trans_eq (pow_one p)
  · have h1 : F.normalizerMonoidHom (φ.codRestrict _ hφ e) = 1 := MonoidHom.mem_ker.1 he
    have h2 := Subgroup.normalizerMonoidHom_apply_apply_coe F (φ.codRestrict _ hφ e) ⟨f, hf⟩
    rw [h1] at h2
    have key : φ e * f * (φ e)⁻¹ = f := h2.symm
    calc φ e * f = φ e * f * (φ e)⁻¹ * φ e := by group
      _ = f * φ e := by rw [key]

private theorem uc22r3h_exists_action {D : Data G} {E : Subgroup G} {p n : ℕ} (hpp : p.Prime)
    (hp2 : p ≠ 2) (hE : IsElemAbelian p E) (hEM : E ≤ D.M) {L K : Subgroup G}
    (hinn : ∀ (x : G) (hxM : x ∈ D.M), x ^ p = 1 → ∀ (Y : Subgroup G), (Y = L ∨ Y = K) →
      ∀ (hN : uc22p21cPi D.M ⟨x, hxM⟩ ∈ normalizer (barImage D.M Y : Set (Bar2 D.M))),
        (barImage D.M Y).normalizerMonoidHom ⟨uc22p21cPi D.M ⟨x, hxM⟩, hN⟩ ∈
          (MulAut.conj : ↥(barImage D.M Y) →* MulAut ↥(barImage D.M Y)).range)
    {Y : Subgroup G} (hY : Y ∈ calC D.M) (hcY : (conjSetOf D.M Y).ncard = 2)
    (hSY : IsL2 (Bar2 Y) n ∨ IsSz (Bar2 Y) n) (hYLK : Y = L ∨ Y = K) :
    ∃ N : Subgroup ↥E, N.index ≤ p ∧ ∀ e ∈ N, ∀ f ∈ barImage D.M Y,
      uc22p21cPi D.M (Subgroup.inclusion hEM e) * f =
        f * uc22p21cPi D.M (Subgroup.inclusion hEM e) := by
  have hEt : IsElemAbelian p (⊤ : Subgroup ↥E) := by
    have h := hE.subgroupOf E
    rwa [Subgroup.subgroupOf_self] at h
  have hodd : ∀ e : ↥E, Odd (orderOf (e : G)) := fun e =>
    (hpp.odd_of_ne_two hp2).of_dvd_nat (orderOf_dvd_of_pow_eq_one (hE.2 e e.2))
  let φ : ↥E →* Bar2 D.M := (uc22p21cPi D.M).comp (Subgroup.inclusion hEM)
  have hφ : ∀ e : ↥E, φ e ∈ normalizer (barImage D.M Y : Set (Bar2 D.M)) := fun e =>
    uc22ine229_mk_mem_normalizer (uc22p2214_mem_normalizer_of_odd hcY (hEM e.2) (hodd e))
  have hF := u4x_shape_barImage hY hSY
  obtain ⟨N, hNi, hN⟩ := uc22r3e5_exists_centralizing hpp hEt (u4x_center_eq_bot hY hSY)
    (pRank_le_one_of_isL2_or_isSz hF hpp hp2) φ hφ (fun e =>
      hinn (e : G) (hEM e.2) (hE.2 (e : G) e.2) Y hYLK (hφ e))
  exact ⟨N, hNi, hN⟩

private theorem uc22r3h_layer_le {D : Data G} {L K : Subgroup G}
    (hno : ∀ L'' ∈ calC D.M, L'' = L ∨ L'' = K) :
    CFSG.layer (Bar2 D.M) ≤ barImage D.M L ⊔ barImage D.M K := by
  rw [CFSG.layer.eq_sSup]
  refine sSup_le fun C hC => ?_
  obtain ⟨L'', hL'', rfl⟩ := PartTwo.s13_exists_calC_of_component D.M hC
  rcases hno L'' hL'' with rfl | rfl
  · exact le_sup_left
  · exact le_sup_right

private theorem uc22r3h_inf_eq_bot {D : Data G} {E : Subgroup G} {p : ℕ} (hpp : p.Prime)
    (hcent : CFSG.Open.pRank p (barPreimage D.M (centE D.M)) = 0) (hEM : E ≤ D.M)
    (hE : IsElemAbelian p E) {L K : Subgroup G}
    (hcomm : ∀ x ∈ barImage D.M L, ∀ y ∈ barImage D.M K, x * y = y * x)
    (hlayer : CFSG.layer (Bar2 D.M) ≤ barImage D.M L ⊔ barImage D.M K)
    {N₁ N₂ : Subgroup ↥E}
    (hN₁ : ∀ e ∈ N₁, ∀ f ∈ barImage D.M L,
      uc22p21cPi D.M (Subgroup.inclusion hEM e) * f =
        f * uc22p21cPi D.M (Subgroup.inclusion hEM e))
    (hN₂ : ∀ e ∈ N₂, ∀ f ∈ barImage D.M K,
      uc22p21cPi D.M (Subgroup.inclusion hEM e) * f =
        f * uc22p21cPi D.M (Subgroup.inclusion hEM e)) :
    N₁ ⊓ N₂ = ⊥ := by
  have : Fact p.Prime := ⟨hpp⟩
  rw [eq_bot_iff]
  intro e he
  rw [Subgroup.mem_bot]
  by_contra he1
  have hc : uc22p21cPi D.M (Subgroup.inclusion hEM e) ∈ centE D.M := by
    rw [centE, mem_centralizer_iff]
    intro h hh
    obtain ⟨a, ha, b, hb, rfl⟩ := u4x_mem_sup hcomm (hlayer hh)
    rw [mul_assoc, ← hN₂ e he.2 b hb, ← mul_assoc, ← hN₁ e he.1 a ha, mul_assoc]
  have hmem : (e : G) ∈ barPreimage D.M (centE D.M) :=
    Subgroup.mem_map.2 ⟨Subgroup.inclusion hEM e, hc, rfl⟩
  have he1' : (e : G) ≠ 1 := fun h => he1 (Subtype.ext h)
  have hcard : Nat.card (zpowers (e : G)) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hE.2 e e.2) he1']
  have h1 := CFSG.SectionRank.le_pRank hpp.one_lt (zpowers_le.2 hmem)
    (CFSG.GroupTheory.isElemAbelian_of_card_prime hcard) (k := 1) (by rw [hcard, pow_one])
  omega

theorem uc22r3h_exists_other_member_of_inner {D : Data G}
    (hSg : UC6S846.SigmaStd D) (he : CFSG.Open.evenRank G = 3) {L K : Subgroup G}
    (hL : L ∈ calC D.M) (hK : K ∈ calC D.M) (hne : K ≠ L) (hset : conjSetOf D.M L = {L, K})
    {n : ℕ} (hS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) {p : ℕ} (hp : p ∈ D.sig)
    (hinn : ∀ (x : G) (hxM : x ∈ D.M), x ^ p = 1 → ∀ (Y : Subgroup G), (Y = L ∨ Y = K) →
      ∀ (hN : uc22p21cPi D.M ⟨x, hxM⟩ ∈ normalizer (barImage D.M Y : Set (Bar2 D.M))),
        (barImage D.M Y).normalizerMonoidHom ⟨uc22p21cPi D.M ⟨x, hxM⟩, hN⟩ ∈
          (MulAut.conj : ↥(barImage D.M Y) →* MulAut ↥(barImage D.M Y)).range)
    (hcent : CFSG.Open.pRank p (barPreimage D.M (centE D.M)) = 0) :
    ∃ L' ∈ calC D.M, L' ≠ L ∧ L' ≠ K := by
  by_contra hno'
  have hno : ∀ L'' ∈ calC D.M, L'' = L ∨ L'' = K := fun L'' hL'' => by
    by_contra h
    exact hno' ⟨L'', hL'', fun h1 => h (Or.inl h1), fun h2 => h (Or.inr h2)⟩
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have : Fact p.Prime := ⟨hpp⟩
  obtain ⟨E, hEM, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hpp.one_lt D.M
  rw [uc22s2121e3_pRank_eq_three hSg he hp] at hEc
  have hmemK : K ∈ conjSetOf D.M L := by rw [hset]; simp
  have hc2 : (conjSetOf D.M L).ncard = 2 := by rw [hset]; exact Set.ncard_pair hne.symm
  have hcK : (conjSetOf D.M K).ncard = 2 := by rw [uc22p2214_conjSetOf_eq hmemK]; exact hc2
  have hSK := uc22s21ru4e_shape_conj hmemK hS
  obtain ⟨N₁, hN₁i, hN₁⟩ :=
    uc22r3h_exists_action hpp hp2 hE hEM hinn hL hc2 hS (Or.inl rfl)
  obtain ⟨N₂, hN₂i, hN₂⟩ :=
    uc22r3h_exists_action hpp hp2 hE hEM hinn hK hcK hSK (Or.inr rfl)
  obtain ⟨hcomm, -⟩ := u4x_bar_structure hL hK hne hset hS
  have hlayer := uc22r3h_layer_le hno
  have hbot := uc22r3h_inf_eq_bot hpp hcent hEM hE hcomm hlayer hN₁ hN₂
  have hi := Subgroup.index_inf_le (H := N₁) (K := N₂)
  rw [hbot, Subgroup.index_bot, hEc] at hi
  have hlt : p * p < p ^ 3 := by
    rw [← sq]
    exact Nat.pow_lt_pow_right hpp.one_lt (by norm_num)
  have := hi.trans (Nat.mul_le_mul hN₁i hN₂i)
  omega

theorem uc22r3h_exists_other_member_of_sig {D : Data G}
    {Ch : Choice2011 G} (st : Standing22 D) (h211 : S21_1 D Ch) (h1930 : H1930 D)
    (c : Ctx21 D Ch) {H₁ H₂ : Subgroup G} (hH₁ : H₁ ∈ hSet D.T D.M)
    (hH₂ : H₂ ∈ hSet D.T D.M)
    (hfX : ∀ X : Subgroup G, X ≤ D.M → D.T ≤ X → F12.InF 1 (⊤ : Subgroup (Bar2 X)) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G))
    (he : CFSG.Open.evenRank G = 3) {L K : Subgroup G} (hL : L ∈ calC D.M)
    (hK : K ∈ calC D.M) (hne : K ≠ L) (hset : conjSetOf D.M L = {L, K}) {n : ℕ}
    (hS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) {p : ℕ} (hp : p ∈ D.sig)
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (hcent : CFSG.Open.pRank p (barPreimage D.M (centE D.M)) = 0) :
    ∃ L' ∈ calC D.M, L' ≠ L ∧ L' ≠ K :=
  uc22r3h_exists_other_member_of_inner st.sigmaStd he hL hK hne hset hS hp
    (fun _x hxM hxp _Y hYLK hN =>
      uc22r3e5_inner_of_sig st h211 h1930 c hH₁ hH₂ hfX hp hsp hL hK hne hset hS hxM hxp hYLK hN)
    hcent

end CFSG.LocalAnalysis.UniquenessCase.UC22
