module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.InnerTorusFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineAdj
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.BarOutInner
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.SigmaCentZ
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.SL3GeomTransfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.ComponentPermutesGeneric
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22m
public import CFSG.GroupTheory.PCoreSurjective
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightPrelim

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_prime_dvd_two_pow_sub_one_ne_three_not_dvd {n : ℕ} (hn : 3 ≤ n) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ≠ 3 ∧ ¬ r ∣ n ∧ r ∣ 2 ^ n - 1 := by
  by_cases h6 : n = 6
  · subst h6
    exact ⟨7, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · obtain ⟨p, hp, hpdvd, hprim⟩ :=
      CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one n (by omega) h6
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega)).not_two_dvd_nat hpdvd
    have hp3 : p ≠ 3 := by
      rintro rfl
      exact hprim 2 (by norm_num) (by omega) (by norm_num)
    have hfermat : p ∣ 2 ^ (p - 1) - 1 := by
      have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
      exact Nat.dvd_of_mod_eq_zero (Nat.pow_card_sub_one_sub_one_mod_card hp hcop)
    have hpn : ¬ p ∣ n := by
      intro hdvd
      have hple : p ≤ n := Nat.le_of_dvd (by omega) hdvd
      by_cases hlt : p - 1 < n
      · exact hprim (p - 1) (Nat.sub_pos_of_lt hp.one_lt) hlt hfermat
      · omega
    exact ⟨p, hp, hp2, hp3, hpn, hpdvd⟩

theorem exists_conj_of_pow_eq_one_of_coprime_outer {L : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) {r : ℕ} (hxr : x ^ r = 1)
    (hcop : Nat.Coprime r (Nat.card (Outer (Bar2 L)))) :
    ∃ (l : G) (hl : l ∈ L), barConjAut x = MulAut.conj (QuotientGroup.mk ⟨l, hl⟩) := by
  let N : Subgroup G := Subgroup.normalizer (L : Set G)
  let n : ↥N := ⟨x, hx⟩
  have hnr : n ^ r = 1 := Subtype.ext hxr
  have hβ : (barAction L n) ^ r = 1 := by rw [← map_pow, hnr, map_one]
  have hmem : barConjAut x ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L) := by
    rw [barConjAut_of_mem (L := L) hx]
    exact mem_inner_of_pow_eq_one_of_coprime_card_outer hβ hcop
  rw [CFSG.ComponentClassification.OuterAutomorphisms.inner, MonoidHom.mem_range] at hmem
  obtain ⟨q, hq⟩ := hmem
  obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective q
  refine ⟨(l : G), l.2, ?_⟩
  rw [← hl] at hq
  simpa [barConjAut_of_mem (L := L) hx] using hq.symm

private theorem barAction_eq_conj_mk {K : Subgroup G} {y : G} (hyK : y ∈ K) :
    barAction K ⟨y, Subgroup.le_normalizer hyK⟩ =
      MulAut.conj (QuotientGroup.mk ⟨y, hyK⟩) := by
  apply MulEquiv.ext
  intro x
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
  rw [barAction_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  rfl

private theorem mem_openPCoreOf_commutator_of_barAction_eq_one {K : Subgroup G} {d k : G}
    (hdN : d ∈ Subgroup.normalizer (K : Set G)) (hk : k ∈ K)
    (hd : barAction K ⟨d, hdN⟩ = 1) :
    d * k * d⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K := by
  have hconj : d * k * d⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hdN k).mp hk
  have hmem : d * k * d⁻¹ * k⁻¹ ∈ K := K.mul_mem hconj (K.inv_mem hk)
  have h1 : (QuotientGroup.mk ⟨d * k * d⁻¹, hconj⟩ : Bar2 K) =
      QuotientGroup.mk ⟨k, hk⟩ := by
    have h := barAction_mk K ⟨d, hdN⟩ ⟨k, hk⟩
    rw [hd] at h
    have h' : ((K.normalizerMonoidHom ⟨d, hdN⟩) ⟨k, hk⟩) = ⟨d * k * d⁻¹, hconj⟩ :=
      Subtype.ext rfl
    rw [h'] at h
    simpa using h.symm
  have h2 : (QuotientGroup.mk (⟨d * k * d⁻¹ * k⁻¹, hmem⟩ : ↥K) : Bar2 K) = 1 := by
    have h3 : (⟨d * k * d⁻¹ * k⁻¹, hmem⟩ : ↥K) =
        ⟨d * k * d⁻¹, hconj⟩ * ⟨k, hk⟩⁻¹ := Subtype.ext (by simp [mul_assoc])
    rw [h3, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1]
    simp
  have hmemCore : (⟨d * k * d⁻¹ * k⁻¹, hmem⟩ : ↥K) ∈ CFSG.pCore 2 ↥K :=
    (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥K) _).mp h2
  exact (CFSG.mem_openPCoreOf_iff (p := 2) (H := K)
    ⟨d * k * d⁻¹ * k⁻¹, hmem⟩).mpr hmemCore

private theorem exists_centralizing_lift_of_barConjAut {K : Subgroup G} {b : G}
    (hbN : b ∈ Subgroup.normalizer (K : Set G)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hbr : orderOf b = r) (hZ : Subgroup.center (Bar2 K) = ⊥) {l : G} (hl : l ∈ K)
    (hbar : barConjAut b = MulAut.conj (QuotientGroup.mk ⟨l, hl⟩))
    (hlr : (QuotientGroup.mk ⟨l, hl⟩ : Bar2 K) ^ r = 1)
    (hfixl : b * l * b⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 K) :
    ∃ (a : G) (haK : a ∈ K), b * a = a * b ∧ a ^ r = 1 ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥K) (⟨a, haK⟩ : ↥K) =
        QuotientGroup.mk ⟨l, hl⟩ := by
  haveI : Fact r.Prime := ⟨hr⟩
  by_cases hl1 : (QuotientGroup.mk ⟨l, hl⟩ : Bar2 K) = 1
  · refine ⟨1, K.one_mem, by rw [mul_one, one_mul], one_pow r, ?_⟩
    rw [hl1]
    exact map_one _
  · have hlord : orderOf (QuotientGroup.mk ⟨l, hl⟩ : Bar2 K) = r :=
      orderOf_eq_prime hlr hl1
    have hbodd : Odd (orderOf b) := hbr ▸ hr.odd_of_ne_two hr2
    obtain ⟨y, hyC, hyord, hybar⟩ :=
      exists_mem_inf_centralizer_of_bar_fixed hbN hbodd hl hfixl hr hr2 hlord
    refine ⟨(y : G), y.2, ?_, ?_, hybar⟩
    · exact (Subgroup.mem_centralizer_iff.mp hyC) b (Set.mem_singleton b)
    · rw [← hyord]
      exact pow_orderOf_eq_one (y : G)

private theorem barAction_mul_inv_eq_one_of_factor {K : Subgroup G} {b a l : G}
    (hbN : b ∈ Subgroup.normalizer (K : Set G))
    (hdN : b * a⁻¹ ∈ Subgroup.normalizer (K : Set G)) (haK : a ∈ K) (hl : l ∈ K)
    (hbar : barConjAut b = MulAut.conj (QuotientGroup.mk ⟨l, hl⟩))
    (habar : QuotientGroup.mk' (CFSG.pCore 2 ↥K) (⟨a, haK⟩ : ↥K) =
      QuotientGroup.mk ⟨l, hl⟩) :
    barAction K ⟨b * a⁻¹, hdN⟩ = 1 := by
  have h1 : (⟨b * a⁻¹, hdN⟩ : ↥(Subgroup.normalizer (K : Set G))) =
      ⟨b, hbN⟩ * (⟨a, Subgroup.le_normalizer haK⟩ :
        ↥(Subgroup.normalizer (K : Set G)))⁻¹ :=
    Subtype.ext rfl
  have ha_bar : barAction K ⟨a, Subgroup.le_normalizer haK⟩ =
      MulAut.conj (QuotientGroup.mk ⟨l, hl⟩) := by
    rw [barAction_eq_conj_mk haK]
    simpa using congrArg MulAut.conj habar
  rw [h1, map_mul, map_inv, ← barConjAut_of_mem hbN, hbar, ha_bar]
  group

theorem exists_factor_centralizing_bar2 {K : Subgroup G} {b : G}
    (hbN : b ∈ Subgroup.normalizer (K : Set G)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hbr : orderOf b = r) (hZ : Subgroup.center (Bar2 K) = ⊥)
    (hcop : Nat.Coprime r (Nat.card (Outer (Bar2 K)))) :
    ∃ a ∈ K, b * a = a * b ∧ a ^ r = 1 ∧
      ∀ k ∈ K, (b * a⁻¹) * k * (b * a⁻¹)⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K := by
  obtain ⟨l, hl, hbar⟩ := exists_conj_of_pow_eq_one_of_coprime_outer hbN
    (show b ^ r = 1 from hbr ▸ pow_orderOf_eq_one b) hcop
  have hbrB : (barAction K ⟨b, hbN⟩) ^ r = 1 := by
    have h1 : (⟨b, hbN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ r = 1 :=
      Subtype.ext (show b ^ r = 1 from hbr ▸ pow_orderOf_eq_one b)
    rw [← map_pow, h1, map_one]
  have hlr : (QuotientGroup.mk ⟨l, hl⟩ : Bar2 K) ^ r = 1 := by
    apply P22y.conj_injective_of_center_eq_bot hZ
    rw [map_pow, map_one, ← hbar, barConjAut_of_mem hbN, hbrB]
  have hpoint : ∀ y ∈ K, (b * y * b⁻¹) * (l * y * l⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 K := by
    intro y hy
    have hby : b * y * b⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hbN y).mp hy
    have hly : l * y * l⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hl) y).mp hy
    have h1 : barConjAut b (QuotientGroup.mk ⟨y, hy⟩) =
        MulAut.conj (QuotientGroup.mk ⟨l, hl⟩) (QuotientGroup.mk ⟨y, hy⟩) := by
      rw [hbar]
    rw [barConjAut_of_mem hbN, barAction_mk, MulAut.conj_apply] at h1
    simp only [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv] at h1
    rw [QuotientGroup.eq_iff_div_mem] at h1
    have hx := (CFSG.mem_openPCoreOf_iff (p := 2) (H := K)
      ((⟨b * y * b⁻¹, hby⟩ : ↥K) / ⟨l * y * l⁻¹, hly⟩)).mpr h1
    simpa [Subgroup.coe_div, div_eq_mul_inv] using hx
  obtain ⟨a, haK, hcomm, hapow, habar⟩ :=
    exists_centralizing_lift_of_barConjAut hbN hr hr2 hbr hZ hl hbar hlr
      (by simpa using hpoint l hl)
  refine ⟨a, haK, hcomm, hapow, ?_⟩
  intro k hk
  have hdN : b * a⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normalizer (K : Set G)).mul_mem hbN
      ((Subgroup.normalizer (K : Set G)).inv_mem (Subgroup.le_normalizer haK))
  exact mem_openPCoreOf_commutator_of_barAction_eq_one hdN hk
    (barAction_mul_inv_eq_one_of_factor hbN hdN haK hl hbar habar)

private theorem nonempty_bar2_equiv_map_phiL {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) {hV : IsElemAbelian 2 c.V}
    (hker : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L) :
    Nonempty (Bar2 (c.K.subgroupOf c.L) ≃*
      Bar2 ((c.K.subgroupOf c.L).map (c.phiL hV))) := by
  let X : Subgroup ↥c.L := c.K.subgroupOf c.L
  let Kstar : Subgroup ↥(c.H hV) := X.map (c.phiL hV)
  let f : ↥X →* ↥Kstar :=
    { toFun := fun x => ⟨c.phiL hV (x : ↥c.L), Subgroup.mem_map_of_mem _ x.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ _ _) }
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hkerp : IsPGroup 2 f.ker := by
    refine (IsPGroup.comap_of_injective (hH := CFSG.pCore_isPGroup) (ϕ := X.subtype)
      (hϕ := Subtype.val_injective)).to_le ?_
    intro x hx
    rw [Subgroup.mem_comap]
    have hx1 : c.phiL hV (x : ↥c.L) = 1 := by
      have h := congrArg Subtype.val hx
      simpa [f] using h
    have hx2 : (x : ↥c.L) ∈ (c.phiL hV).ker := hx1
    rwa [hker] at hx2
  exact CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker f hf hkerp

theorem Ctx2311.isL2_bar2_K {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (hTd : KTab23d) {hV : IsElemAbelian 2 c.V}
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hSL : IsSLn ↥(c.H hV) 3 (CFSG.Open.pRank 2 D.Z))
    (hnatSL : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z))
    (hker : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L) :
    IsL2 (Bar2 c.K) (CFSG.Open.pRank 2 D.Z) := by
  classical
  letI : MulDistribMulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.toCtx23L.W hV) :=
    MulAction.compHom (c.toCtx23L.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.toCtx23L.W hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar hV) (c.toCtx23L.W hV) :=
    MulDistribMulAction.compHom (c.toCtx23L.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  letI : MulAction ↥(c.sylowStar hV) (c.toCtx23L.W hV) :=
    MulAction.compHom (c.toCtx23L.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  have hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z) :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hSL, hnatSL⟩))))
  have hKstar : Hinf (MulAction.stabilizer ↥(c.H hV)
      (((fixedPointSubgroup ↥(c.sylowStar hV) (c.toCtx23L.W hV) :
        Subgroup (c.toCtx23L.W hV)) : Set (c.toCtx23L.W hV)))) =
      (c.K.subgroupOf c.L).map (c.phiL hV) :=
    c.toCtx23L.Hinf_stabilizer_sylowStar_eq_map_Hinf hV kTab23a_holds h4 h1930 hnat
  have hTab := hTd (c.toCtx23L.W hV) (c.H hV) (CFSG.Open.pRank 2 D.Z) hnat
    (c.commutator_H_eq hV) h3 (c.sylowStar hV)
  have hL2Kstar : IsL2 (Bar2 (Hinf (MulAction.stabilizer ↥(c.H hV)
      (((fixedPointSubgroup ↥(c.sylowStar hV) (c.toCtx23L.W hV) :
        Subgroup (c.toCtx23L.W hV)) : Set (c.toCtx23L.W hV))))))
      (CFSG.Open.pRank 2 D.Z) :=
    hTab.2.2.2.2.1 ⟨hSL, hnatSL⟩
  rw [hKstar] at hL2Kstar
  obtain ⟨e2⟩ := nonempty_bar2_equiv_map_phiL c hker
  obtain ⟨e1⟩ := CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.nonempty_bar2_mulEquiv_map_subtype
    (H := c.L) (X := c.K.subgroupOf c.L)
  rw [Subgroup.map_subgroupOf_eq_of_le c.K_le_L] at e1
  exact LieModel.of_mulEquiv e1 (LieModel.of_mulEquiv e2.symm hL2Kstar)

private theorem factor_ne_one_of_mem_B0 {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    (h4 : S23_4 D Ch) (h1930 : H1930 D) {b a : G} (hbB0 : b ∈ c.B0)
    (hbZ : b ∉ Subgroup.centralizer (D.Z : Set G)) (haK : a ∈ c.K) :
    b * a⁻¹ ≠ 1 := by
  intro hd1
  have hb_eq : b = a := by
    have := congrArg (fun x => x * a) hd1
    simpa using this
  have hKZ : c.K ≤ Subgroup.centralizer (D.Z : Set G) :=
    le_centralizer_Z_of_perfect D Ch h4 h1930 c.toCtx23L
      ((uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_left) (uc22p21c_Hinf_perfect _)
  exact hbZ (hKZ (hb_eq ▸ haK))

theorem Ctx2311.exists_factor_of_mem_B0 {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    (hE : UC22P20gExcFacts) (h207 : S20_7 D) (h52 : S23_5_2 D Ch) (h53 : S23_5_3 D Ch)
    (h4 : S23_4 D Ch) (h1930 : H1930 D) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hL2K : IsL2 (Bar2 c.K) (CFSG.Open.pRank 2 D.Z)) :
    ∃ b ∈ c.B0, ∃ d a : G, ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ≠ 3 ∧ orderOf b = r ∧
      b ∉ Subgroup.centralizer (D.Z : Set G) ∧ b = d * a ∧ a ∈ c.K ∧
      d ∈ D.M ⊓ c.L ∧ orderOf d = r ∧
      ∀ k ∈ c.K, d * k * d⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 c.K := by
  classical
  set m := CFSG.Open.pRank 2 D.Z with hm
  obtain ⟨r, hr, hr2, hr3, hrn, hrdvd⟩ :=
    exists_prime_dvd_two_pow_sub_one_ne_three_not_dvd (n := m) (by omega)
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨-, hb⟩ :=
    Ctx23L.exists_mem_B0_not_mem_centralizer_Z hE h207 h52 h53 h1930 c.toCtx23L
  obtain ⟨b, hbB0, hbr, hbZ⟩ := hb r hr hrdvd
  have hbL : b ∈ c.L := c.hL0L (c.hB0.1 hbB0)
  have hbM : b ∈ D.M := c.hBM hbB0
  have hbML : b ∈ D.M ⊓ c.L := ⟨hbM, hbL⟩
  have hbN : b ∈ Subgroup.normalizer (c.K : Set G) :=
    uc22p22m_le_normalizer_Hinf (D.M ⊓ c.L) hbML
  have hZ : Subgroup.center (Bar2 c.K) = ⊥ := P22y.center_eq_bot_of_isL2Ev hL2K.isL2Ev
  have hOut : Nat.card (Outer (Bar2 c.K)) ∣ m := card_outer_dvd_of_isL2 hL2K
  have hcop : Nat.Coprime r (Nat.card (Outer (Bar2 c.K))) :=
    (Nat.Prime.coprime_iff_not_dvd hr).mpr fun hd => hrn (hd.trans hOut)
  obtain ⟨a, haK, hcomm, hapow, hdcomm⟩ :=
    exists_factor_centralizing_bar2 hbN hr hr2 hbr hZ hcop
  have hKM : c.K ≤ D.M ⊓ c.L := uc22p21c_Hinf_le (D.M ⊓ c.L)
  have haM : a ∈ D.M := (hKM haK).1
  have haL : a ∈ c.L := (hKM haK).2
  have hdML : b * a⁻¹ ∈ D.M ⊓ c.L :=
    ⟨D.M.mul_mem hbM (D.M.inv_mem haM), c.L.mul_mem hbL (c.L.inv_mem haL)⟩
  have hd1 : b * a⁻¹ ≠ 1 := factor_ne_one_of_mem_B0 c h4 h1930 hbB0 hbZ haK
  have hcommC : Commute b a⁻¹ := ((commute_iff_eq b a).2 hcomm).inv_right
  have hdvd : (b * a⁻¹) ^ r = 1 := by
    rw [hcommC.mul_pow r, inv_pow, show b ^ r = 1 from hbr ▸ pow_orderOf_eq_one b,
      hapow, inv_one, mul_one]
  have hdord : orderOf (b * a⁻¹) = r := orderOf_eq_prime hdvd hd1
  exact ⟨b, hbB0, b * a⁻¹, a, r, hr, hr2, hr3, hbr, hbZ, by group, haK, hdML, hdord, hdcomm⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
