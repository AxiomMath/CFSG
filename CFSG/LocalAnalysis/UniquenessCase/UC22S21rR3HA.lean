module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UC22S2121E3S13
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4XC
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214d
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Cong
import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FSmallGlue
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

theorem uc22r3h_exists_centralizing {Q E : Type} [Group Q] [Finite Q] [Group E] [Finite E]
    {p : ℕ} (hp : p.Prime) (hE : IsElemAbelian p (⊤ : Subgroup E)) {F : Subgroup Q}
    (hZ : center ↥F = ⊥) (hrk : CFSG.Open.pRank p (⊤ : Subgroup ↥F) ≤ 1)
    (hinn : ∀ α : MulAut ↥F, α ^ p = 1 → α ∈ (MulAut.conj : ↥F →* MulAut ↥F).range)
    (φ : E →* Q) (hφ : ∀ e, φ e ∈ normalizer (F : Set Q)) :
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
      exact hinn _ (by rw [← map_pow, hE.2 e (mem_top e), map_one])
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

variable {G : Type} [Group G] [Finite G]

theorem uc22r3h_exists_other_member {D : Data G}
    (hSg : UC6S846.SigmaStd D) (he : CFSG.Open.evenRank G = 3) {L K : Subgroup G}
    (hL : L ∈ calC D.M) (hK : K ∈ calC D.M) (hne : K ≠ L) (hset : conjSetOf D.M L = {L, K})
    {n : ℕ} (hS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) {p : ℕ} (hp : p ∈ D.sig) (hpn : ¬ p ∣ n)
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
  have hEt : IsElemAbelian p (⊤ : Subgroup ↥E) := by
    have h := hE.subgroupOf E
    rwa [Subgroup.subgroupOf_self] at h
  have hodd : ∀ e : ↥E, Odd (orderOf (e : G)) := fun e =>
    (hpp.odd_of_ne_two hp2).of_dvd_nat (orderOf_dvd_of_pow_eq_one (hE.2 e e.2))
  have hmemK : K ∈ conjSetOf D.M L := by rw [hset]; simp
  have hc2 : (conjSetOf D.M L).ncard = 2 := by rw [hset]; exact Set.ncard_pair hne.symm
  have hcK : (conjSetOf D.M K).ncard = 2 := by rw [uc22p2214_conjSetOf_eq hmemK]; exact hc2
  have hSK := uc22s21ru4e_shape_conj hmemK hS
  let φ : ↥E →* Bar2 D.M := (uc22p21cPi D.M).comp (Subgroup.inclusion hEM)
  have act : ∀ {Y : Subgroup G}, Y ∈ calC D.M → (conjSetOf D.M Y).ncard = 2 →
      (IsL2 (Bar2 Y) n ∨ IsSz (Bar2 Y) n) → ∃ N : Subgroup ↥E, N.index ≤ p ∧
        ∀ e ∈ N, ∀ f ∈ barImage D.M Y, φ e * f = f * φ e := by
    intro Y hY hcY hSY
    have hF := u4x_shape_barImage hY hSY
    refine uc22r3h_exists_centralizing hpp hEt (u4x_center_eq_bot hY hSY)
      (pRank_le_one_of_isL2_or_isSz hF hpp hp2) (fun α hα => ?_) φ fun e =>
        uc22ine229_mk_mem_normalizer (uc22p2214_mem_normalizer_of_odd hcY (hEM e.2) (hodd e))
    rcases hF with h | h
    · exact uc22p2214_inner_of_prime_L2 h hpp hpn hα
    · exact uc22p2214_inner_of_prime_Sz h hpp hpn hα
  obtain ⟨N₁, hN₁i, hN₁⟩ := act hL hc2 hS
  obtain ⟨N₂, hN₂i, hN₂⟩ := act hK hcK hSK
  obtain ⟨hcomm, -⟩ := u4x_bar_structure hL hK hne hset hS
  have hlayer : CFSG.layer (Bar2 D.M) ≤ barImage D.M L ⊔ barImage D.M K := by
    rw [CFSG.layer.eq_sSup]
    refine sSup_le fun C hC => ?_
    obtain ⟨L'', hL'', rfl⟩ := PartTwo.s13_exists_calC_of_component D.M hC
    rcases hno L'' hL'' with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  have hbot : N₁ ⊓ N₂ = ⊥ := by
    rw [eq_bot_iff]
    intro e he
    rw [Subgroup.mem_bot]
    by_contra he1
    have hc : φ e ∈ centE D.M := by
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
  have hi := Subgroup.index_inf_le (H := N₁) (K := N₂)
  rw [hbot, Subgroup.index_bot, hEc] at hi
  have hlt : p * p < p ^ 3 := by
    rw [← sq]
    exact Nat.pow_lt_pow_right hpp.one_lt (by norm_num)
  have := hi.trans (Nat.mul_le_mul hN₁i hN₂i)
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
