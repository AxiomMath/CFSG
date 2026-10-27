module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2251b
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251c
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251L
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataKParam
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

namespace P2251d

theorem mem_range_conj_of_isL3 {X : Type} [Group X] [Finite X] (h : IsL3 X 1) {m : ℕ} (hm : Odd m)
    {σ : MulAut X} (hσ : σ ^ m = 1) : σ ∈ (MulAut.conj : X →* MulAut X).range := by
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    refine (injective_iff_map_eq_one _).2 fun g hg => ?_
    have hgc : g ∈ center X := mem_center_iff.2 fun z =>
      (mul_inv_eq_iff_eq_mul.1 (show g * z * g⁻¹ = z from DFunLike.congr_fun hg z)).symm
    rwa [PartTwo.center_eq_bot_of_isL3 h, mem_bot] at hgc
  have hidx : (MulAut.conj : X →* MulAut X).range.index = 2 := by
    have h1 := (MulAut.conj : X →* MulAut X).range.card_mul_index
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, PartTwo.card_eq_of_isL3 h,
      CFSG.SeitzReduction.LinearPilot.card_mulAut_of_lieModel_PSL_three_two h] at h1
    omega
  obtain ⟨k, rfl⟩ := hm
  rw [show σ = (σ * σ) ^ (k + 1) by
    rw [← pow_two, ← pow_mul, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ, hσ, one_mul]]
  exact pow_mem (mul_self_mem_of_index_two hidx σ) _

theorem exists_orderOf_three_card_le_of_layerShape {X : Type} [Group X] [Finite X] (hX : LayerShape22 X)
    {P : Type} [Group P] [Finite P] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hexp : ∀ x : P, x ^ p = 1)
    (hPab : ∀ x y : P, x * y = y * x) (φ : P →* MulAut X) (hP : p ^ 3 ≤ Nat.card P) :
    ∃ x : X, orderOf x = 3 ∧ ∃ Q : Subgroup P, p ^ 2 ≤ Nat.card Q ∧ ∀ u ∈ Q, φ u x = x := by
  have hZ := hX.center_eq_bot
  have h3 := hX.three_dvd_card
  have hcp : ∀ B : Subgroup X, IsPGroup p B → IsCyclic B := fun B hB => hX.isCyclic_of_isPGroup hp hp2 B hB
  rcases hX with ⟨n, -, h⟩ | h
  · exact P2251L.exists_orderOf_three_card_le (k := 2) h hp hp2 hexp hPab φ hP
  · obtain ⟨x, hx, Q, hQ, hQx⟩ := P2251L.exists_orderOf_three_index_le_of_le_inner hZ hp hcp
      (exists_prime_orderOf_dvd_card' (G := X) 3 h3) hexp hPab φ (by
        rintro _ ⟨u, rfl⟩
        exact mem_range_conj_of_isL3 h (hp.odd_of_ne_two hp2) (by rw [← map_pow, hexp, map_one]))
    exact ⟨x, hx, Q, P2251L.pow_le_card_of_index_le hp.pos hQ hP, hQx⟩

theorem pow_le_card_ker {P Y : Type} [Group P] [Group Y] [Finite Y] {p k : ℕ} [Fact p.Prime]
    (hP : Nat.card P = p ^ (k + 1)) (hY : ¬ p ^ 2 ∣ Nat.card Y) (f : P →* Y) : p ^ k ≤ Nat.card f.ker := by
  have hp : p.Prime := Fact.out
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1
    ((IsPGroup.of_card hP).of_surjective f.rangeRestrict f.rangeRestrict_surjective)
  have ha1 : a ≤ 1 := by
    by_contra h
    exact hY ((pow_dvd_pow p (show 2 ≤ a by omega)).trans (by rw [← ha]; exact f.range.card_subgroup_dvd_card))
  have hr : Nat.card f.range ≤ p := by
    rw [ha]
    exact (Nat.pow_le_pow_right hp.pos ha1).trans_eq (pow_one p)
  refine Nat.le_of_mul_le_mul_right ?_ hp.pos
  calc p ^ k * p = Nat.card f.ker * Nat.card f.range := by
        rw [Subgroup.card_ker_mul_card_range, hP, pow_succ]
    _ ≤ Nat.card f.ker * p := Nat.mul_le_mul_left _ hr

variable {G : Type} [Group G] [Finite G]

theorem inv_mul_conj_mem_of_rhoL {L : Subgroup G} (u : ↥(normalizer (L : Set G))) {b : G} (hb : b ∈ L)
    (h : UC6S846.rhoL L u ((⟨b, hb⟩ : ↥L) : Bar2 L) = ((⟨b, hb⟩ : ↥L) : Bar2 L)) :
    b⁻¹ * ((u : G) * b * (u : G)⁻¹) ∈ pCoreOf 2 L := by
  have h1 := (mem_normalizer_iff.1 (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L
    (le_normalizer (inv_mem hb))) _).1 ((UC6S846.rhoL_fix_iff L u ⟨b, hb⟩).1 h)
  rwa [show b⁻¹ * ((u : G) * b * (u : G)⁻¹ * b⁻¹) * b⁻¹⁻¹ = b⁻¹ * ((u : G) * b * (u : G)⁻¹) by group] at h1

theorem exists_elemAbelian_of_pair {M K L : Subgroup G} (hK : K ∈ calC M) (hKn : (K.subgroupOf M).Normal)
    (hL : L ∈ calC M) (hKL : K ≠ L) (hKs : BadShape22 (Bar2 K)) (hLs : LayerShape22 (Bar2 L))
    (hM3 : CFSG.Open.pRank 3 M ≤ 3) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hM : 4 ≤ CFSG.Open.pRank p M) :
    ∃ R E A : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 R M ∧ E ≤ R ⊓ centralizer (R : Set G) ∧
      IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧ A ≤ M ⊓ centralizer (E : Set G) ∧ IsElemAbelian p A ∧
      Nat.card A = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hMK : M ≤ normalizer (K : Set G) := (normal_subgroupOf_iff_le_normalizer hK.1.le).1 hKn
  have hK3 := hKs.layerShape.three_dvd_card
  have hKZ := hKs.layerShape.center_eq_bot
  have hLN : ∀ H : Subgroup G, H ≤ M → Odd (Nat.card H) → H ≤ normalizer (L : Set G) := fun _ hHM hH =>
    P2251c.le_normalizer_of_pRank_le hK hKn hL hKL hK3 hKZ hLs.three_dvd_card hLs.center_eq_bot hM3 hHM hH
  have hLC := P2251c.le_centralizerMod_of_ne hK hL hKL
  obtain ⟨A₀, hA₀M, hA₀, hA₀c⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hp hM
  have hA₀K := hA₀M.trans hMK
  have hA₀L := hLN A₀ hA₀M (hA₀c ▸ (hp.odd_of_ne_two hp2).pow)
  obtain ⟨B, hBA₀, hBK, hBc⟩ : ∃ B ≤ A₀, B ≤ CFSG.Quasithin.centralizerMod (pCoreOf 2 K)
      (normalizer (K : Set G)) K ∧ p ^ 3 ≤ Nat.card B := by
    let f : ↥A₀ →* MulAut (Bar2 K) := (UC6S846.rhoL K).comp (inclusion hA₀K)
    refine ⟨f.ker.map A₀.subtype, map_subtype_le _, ?_, ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      have h1 : UC6S846.rhoL K (inclusion hA₀K w) = 1 := hw
      refine ⟨hA₀K w.2, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K (hA₀K w.2),
        fun l hl => ?_⟩
      exact (UC6S846.rhoL_fix_iff K (inclusion hA₀K w) ⟨l, hl⟩).1 (by rw [h1, MulAut.one_apply])
    · rw [card_map_of_injective A₀.subtype_injective]
      exact pow_le_card_ker hA₀c (hKs.not_sq_dvd_card_mulAut hp5) f
  obtain ⟨Q, hQB, hQc, b, hbL, hb3, hbQ⟩ : ∃ Q ≤ B, p ^ 2 ≤ Nat.card Q ∧ ∃ b ∈ L, orderOf b = 3 ∧
      ∀ u ∈ Q, b⁻¹ * (u * b * u⁻¹) ∈ pCoreOf 2 L := by
    have hBL : B ≤ normalizer (L : Set G) := hBA₀.trans hA₀L
    obtain ⟨x, hx3, Q, hQc, hQx⟩ := exists_orderOf_three_card_le_of_layerShape hLs hp hp2
      (fun x => Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hA₀.2 _ (hBA₀ x.2)))
      (fun x y => Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact hA₀.comm (hBA₀ x.2) (hBA₀ y.2)))
      ((UC6S846.rhoL L).comp (inclusion hBL)) hBc
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    have h3l : 3 ∣ orderOf l := by
      have h := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) l
      rwa [QuotientGroup.mk'_apply, hx3] at h
    have hfix : ∀ v ∈ Q, UC6S846.rhoL L (inclusion hBL v) ((l ^ (orderOf l / 3) : ↥L) : Bar2 L) =
        ((l ^ (orderOf l / 3) : ↥L) : Bar2 L) := fun v hv => by
      rw [QuotientGroup.mk_pow, map_pow]
      exact congrArg (· ^ (orderOf l / 3)) (hQx v hv)
    refine ⟨Q.map B.subtype, map_subtype_le _, by rwa [card_map_of_injective B.subtype_injective], _,
      (l ^ (orderOf l / 3)).2, by rw [Subgroup.orderOf_coe]; exact orderOf_pow_orderOf_div (orderOf_pos l).ne' h3l, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    exact inv_mul_conj_mem_of_rhoL (inclusion hBL v) (l ^ (orderOf l / 3)).2 (hfix v hv)
  have hQA₀ := hQB.trans hBA₀
  have hQp : IsPGroup p Q := hA₀.isPGroup.to_le hQA₀
  obtain ⟨a₂, ha₂L, ha₂, ha₂Q, -⟩ := P2251c.exists_orderOf_three (P₂ := ⊥) hp2 hQp IsPGroup.of_bot bot_le
    (hQA₀.trans hA₀L) bot_le hbL hb3 hbQ fun u hu => by rw [mem_bot.1 hu]; simp
  obtain ⟨b₁, hb₁K, hb₁⟩ := P2251c.exists_orderOf_three_mem hK3
  obtain ⟨a₁, ha₁K, ha₁, ha₁Q, ha₁₂⟩ := P2251c.exists_orderOf_three (P₂ := zpowers a₂) hp2 hQp
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha₂, pow_one])) (zpowers_le.2 ha₂Q)
    (hQA₀.trans hA₀K) (zpowers_le.2 (hMK (hL.1.le ha₂L))) hb₁K hb₁
    (fun u hu => P2251c.inv_mul_conj_mem_of_mem_centralizerMod (hBK (hQB hu)) hb₁K)
    fun v hv => P2251c.inv_mul_conj_mem_of_mem_centralizerMod (hLC (zpowers_le.2 ha₂L hv)) hb₁K
  have hna : a₂ ∉ zpowers a₁ := fun h => P2251c.not_mem_of_orderOf_eq_three
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K) ha₂
    (P2251c.mem_pCoreOf_of_mem_centralizerMod hKZ (zpowers_le.2 ha₁K h) (hLC ha₂L))
  obtain ⟨hEel, hEc⟩ := CFSG.ComponentClassification.UnbalancedGS.RankOneCenter.pair_isElementaryAbelian_card
    ha₁ ha₂ (mem_centralizer_iff.1 ha₁₂ a₂ (mem_zpowers a₂)).symm hna
  have hEM : zpowers a₁ ⊔ zpowers a₂ ≤ M := sup_le (zpowers_le.2 (hK.1.le ha₁K)) (zpowers_le.2 (hL.1.le ha₂L))
  obtain ⟨R, hR, hER⟩ : ∃ R, CFSG.ABGLocalTools.IsSylowOf 3 R M ∧ zpowers a₁ ⊔ zpowers a₂ ≤ R := by
    obtain ⟨S, hS⟩ := (((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).1
      hEel).isPGroup.comap_subtype (K := M)).exists_le_sylow
    exact ⟨_, ⟨S, rfl⟩, fun y hy => ⟨⟨y, hEM hy⟩, hS (by exact hy), rfl⟩⟩
  have hRodd : Odd (Nat.card R) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hR.isPGroup
    rw [hn]
    exact (Nat.prime_three.odd_of_ne_two (by norm_num)).pow
  have ha₁R : a₁ ∈ R := hER (mem_sup_left (mem_zpowers a₁))
  have ha₂R : a₂ ∈ R := hER (mem_sup_right (mem_zpowers a₂))
  have ha₁C := P2251c.mem_centralizer_of_isCyclic hR.isPGroup (hR.le.trans hMK)
    (uc22p2251b_isCyclic_of_isPGroup hKs.layerShape Nat.prime_three (by norm_num) inf_le_right
      (hR.isPGroup.to_le inf_le_left)) ha₁R ha₁K ha₁
  have ha₂C := P2251c.mem_centralizer_of_isCyclic hR.isPGroup (hLN R hR.le hRodd)
    (uc22p2251b_isCyclic_of_isPGroup hLs Nat.prime_three (by norm_num) inf_le_right
      (hR.isPGroup.to_le inf_le_left)) ha₂R ha₂L ha₂
  obtain ⟨A, hAQ, hA, hAc⟩ := UC6S846.exists_card_p_sq hp (hA₀.mono hQA₀) hQc
  refine ⟨R, _, A, hR, sup_le (zpowers_le.2 (mem_inf.2 ⟨ha₁R, ha₁C⟩)) (zpowers_le.2 (mem_inf.2 ⟨ha₂R, ha₂C⟩)),
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).1 hEel, hEc,
    le_inf (hAQ.trans (hQA₀.trans hA₀M)) (hAQ.trans ?_), hA, hAc⟩
  exact le_centralizer_iff.1 (sup_le (zpowers_le.2 ha₁Q) (zpowers_le.2 ha₂Q))

end P2251d

variable {G : Type} [Group G] [Finite G]

theorem uc22p2251d_eq (D : Data G) (hx : DataExt D) (he : 3 < CFSG.Open.evenRank G)
    (hSg : UC6S846.SigmaStd D) (hk : D.k = 2) (h76 : ∀ L ∈ calC D.M, ∀ p ∈ D.sig, Conclusion76 D.M p)
    (h614 : UC6.R6_14 D) {K L : Subgroup G} (hK : K ∈ calC D.M) (hKn : (K.subgroupOf D.M).Normal)
    (hKs : BadShape22 (Bar2 K)) (hL : L ∈ calC D.M) (hLs : LayerShape22 (Bar2 L)) : L = K := by
  by_contra hLK
  have hns := UC6S846.not_solvable_of_mem_calC hK
  have h3 := (Data.k_eq_two_iff D).1 hk
  have h3σ : 3 ∉ D.sig := fun h => h3 (UC6S846.sp_of_mem_sig hSg hns h)
  have hM3 : CFSG.Open.pRank 3 D.M ≤ 3 := by
    by_contra h
    exact h3σ (hSg.four_mem 3 Nat.prime_three (by norm_num) (by omega))
  obtain ⟨p, hp⟩ := hSg.nonempty
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hp5 : 5 ≤ p := by
    have h2 := hpp.two_le
    have hp3 : p ≠ 3 := fun h => h3σ (h ▸ hp)
    have hp4 : p ≠ 4 := by
      rintro rfl
      norm_num at hpp
    omega
  obtain ⟨R, E, A, hR, hEZ, hEel, hEc, hA, hAel, hAc⟩ := P2251d.exists_elemAbelian_of_pair hK hKn hL
    (Ne.symm hLK) hKs hLs hM3 hpp hp5 (hx.four_le he p hp)
  have hΓ := h76 K hK p hp 3 Nat.prime_three E (hEZ.trans (inf_le_left.trans hR.le)) hEel hEc
    (lt_of_lt_of_le (by norm_num) (UC6S846.le_pRank' hpp hA hAel hAc))
    (fun X hXE _ => lt_of_lt_of_le (by norm_num) (UC6S846.le_pRank' hpp
      (hA.trans (inf_le_inf_left _ ((centralizer_le hXE).trans (centralizer_le_normalizer _)))) hAel hAc))
  exact h3 (h614 (UC6S846.sig_subset_sig1 hSg hns) 3 Nat.prime_three (by norm_num) h3σ R hR E hEZ hEel hEc hΓ)

theorem uc22p2251d_isL2Ev_one (D : Data G) (Ch : Choice2011 G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h119 : R119W D) (h17 : S21_17 D Ch) (hH : H1930 D) (c : Ctx22 D Ch) (he : 3 < CFSG.Open.evenRank G)
    (hSg : UC6S846.SigmaStd D) (hk : D.k = 2) (h76 : ∀ L ∈ calC D.M, ∀ p ∈ D.sig, Conclusion76 D.M p)
    (h614 : UC6.R6_14 D) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)} (hNb : NbarSplit D Nb) {i : Fin m}
    (hbad : ¬ ∃ n : ℕ, IsL2Ev ↥(Nb i) n ∧ n ≠ 2) : ∀ j, j ≠ i → IsL2Ev ↥(Nb j) 1 := by
  intro j hji
  by_contra hj
  obtain ⟨K, hK, hKb, -, hKs, hKn⟩ := uc22p2251b_exists_bad D hx h61 h119 h17 hH c hNb hbad
  obtain ⟨L, hL, hLb, -, hLs⟩ := uc22p2251b_exists_lift_nb D hx h61 h119 c hNb j hj
  exact uc22p2251b_ne D hNb (Ne.symm hji) (P2251b.not_isL2Ev_one_of_bad hbad) hKb hLb
    (uc22p2251d_eq D hx he hSg hk h76 h614 hK hKn hKs hL hLs).symm

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
