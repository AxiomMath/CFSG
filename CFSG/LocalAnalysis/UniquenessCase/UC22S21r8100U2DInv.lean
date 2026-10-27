module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100U2DFr
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101UFr
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r899Sp
import CFSG.LocalAnalysis.UniquenessCase.UC22R8100BFrat
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyFiveStep
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtyEightOq
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace U2DBasis

variable {M L K R E : Subgroup G} {r : ℕ} {b : Fin 2 → G}

theorem exists_conj_eq_zpow (hb : U2DBasis M L K r R E b) (hr : r.Prime) (hr2 : r ≠ 2)
    {m : Bar2 M} {k : Fin 2 → ℤ}
    (h : ∀ i (hi : b i ∈ M), m * uc22p21cPi M ⟨b i, hi⟩ * m⁻¹ = uc22p21cPi M ⟨b i, hi⟩ ^ k i) :
    ∃ t ∈ normalizer (E : Set G) ⊓ M, ∀ i, t * b i * t⁻¹ = b i ^ k i := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEM : E ≤ M := hb.le_R.trans hb.sylow.le
  have hEp : IsPGroup r E := hb.frame.elem.isPGroup
  have hbM : ∀ i, b i ∈ M := fun i => hEM (hb.frame.mem i)
  have hφ : ∀ i, MulAut.conj m (uc22p21cPi M ⟨b i, hbM i⟩) ∈ barImage M E := fun i => by
    rw [MulAut.conj_apply, h i (hbM i)]
    exact zpow_mem (uc22p21c_mem_barImage.2 ⟨_, hb.frame.mem i, rfl⟩) _
  have hmN : m ∈ normalizer ((barImage M E : Subgroup (Bar2 M)) : Set (Bar2 M)) := by
    refine mem_normalizer_fintype fun q hq => ?_
    obtain ⟨x, hxE, rfl⟩ := uc22p21c_mem_barImage.1 hq
    obtain ⟨a, ha⟩ := hb.frame.span _ hxE
    have hxe : x = (⟨b 0, hbM 0⟩ : ↥M) ^ (a 0).val * ⟨b 1, hbM 1⟩ ^ (a 1).val :=
      Subtype.ext (by rw [← ha]; simp only [u2dCoord, Subgroup.coe_mul, Subgroup.coe_pow])
    rw [← MulAut.conj_apply, hxe]
    simp only [map_mul, map_pow]
    exact mul_mem (pow_mem (hφ 0) _) (pow_mem (hφ 1) _)
  have hN2 : ¬ r ∣ Nat.card (CFSG.pCore 2 ↥M) := by
    intro hd
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
    rw [hj] at hd
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow hd))
  have hlift := CFSG.GroupTheory.normal_coprime_quotient_normalizer r
    (CFSG.pCore 2 ↥M) hN2 (E.subgroupOf M) hEp.comap_subtype
  have hm' : m ∈ (normalizer ((E.subgroupOf M : Subgroup ↥M) : Set ↥M)).map
      (uc22p21cPi M) := by
    rw [hlift]
    exact hmN
  obtain ⟨t, htN, rfl⟩ := hm'
  have htG : (t : G) ∈ normalizer (E : Set G) := by
    have h1 := Subgroup.le_normalizer_map M.subtype (Subgroup.mem_map_of_mem M.subtype htN)
    rwa [Subgroup.subgroupOf_map_subtype, inf_of_le_left hEM] at h1
  refine ⟨t, ⟨htG, t.2⟩, fun i => ?_⟩
  have h1 : ((t * ⟨b i, hbM i⟩ * t⁻¹ : ↥M) : G) ∈ E :=
    (mem_normalizer_iff.1 htG _).1 (hb.frame.mem i)
  have h2 : (((⟨b i, hbM i⟩ : ↥M) ^ k i : ↥M) : G) ∈ E := zpow_mem (hb.frame.mem i) _
  have e := u81_eq_of_pi_eq hr hr2 hEp h1 h2 (by
    rw [map_mul, map_mul, map_inv, map_zpow]
    exact h i (hbM i))
  exact congrArg Subtype.val e

end U2DBasis

theorem uc22r8u2d_exists_inv_bar {M L : Subgroup G}
    (hL : L ∈ calC M) {n : ℕ} (hLS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) {x : Bar2 M} (hx : x ∈ barImage M L) (hxo : orderOf x = r) :
    ∃ s ∈ barImage M L, s * x * s⁻¹ = x⁻¹ := by
  obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hL
  have hyo : orderOf (e.symm ⟨x, hx⟩) = r := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hxo]
  obtain ⟨s, -, hs⟩ := PartTwo.S17.exists_involution_inverts_of_shape hLS hr hr2 hyo
  refine ⟨(e s : Bar2 M), (e s).2, ?_⟩
  have h := congrArg (fun y => ((e y : ↥(barImage M L)) : Bar2 M)) hs
  simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul,
    Subgroup.coe_inv] using h

namespace U2DBasis

variable {M L K R E : Subgroup G} {r : ℕ} {b : Fin 2 → G}

theorem exists_inv (hb : U2DBasis M L K r R E b) (hL : L ∈ calC M)
    (hK : K ∈ calC M) (hne : K ≠ L) (hset : conjSetOf M L = {L, K}) {n : ℕ}
    (hLS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) (hr : r.Prime) (hr2 : r ≠ 2) :
    ∃ t ∈ normalizer (E : Set G) ⊓ M, ∀ i, t * b i * t⁻¹ = b i ^ (![-1, 1] : Fin 2 → ℤ) i := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨hcomm, -⟩ := u4x_bar_structure hL hK hne hset hLS
  have h0M : b 0 ∈ M := hb.le_R.trans hb.sylow.le (hb.frame.mem 0)
  obtain ⟨s, hs, hsx⟩ := uc22r8u2d_exists_inv_bar hL hLS hr hr2
    (uc22p21c_mem_barImage.2 ⟨⟨b 0, h0M⟩, hb.mem_L, rfl⟩)
    (orderOf_bar_eq_of_prime h0M hr hr2 (hb.frame.orderOf_eq 0))
  have e0 : ∀ hi : b 0 ∈ M, s * uc22p21cPi M ⟨b 0, hi⟩ * s⁻¹ =
      uc22p21cPi M ⟨b 0, hi⟩ ^ (-1 : ℤ) := fun _ => hsx.trans (zpow_neg_one _).symm
  have e1 : ∀ hi : b 1 ∈ M, s * uc22p21cPi M ⟨b 1, hi⟩ * s⁻¹ =
      uc22p21cPi M ⟨b 1, hi⟩ ^ (1 : ℤ) := fun hi => by
    rw [zpow_one, hcomm s hs _ (uc22p21c_mem_barImage.2 ⟨⟨b 1, hi⟩, hb.mem_K, rfl⟩),
      mul_inv_cancel_right]
  refine hb.exists_conj_eq_zpow hr hr2 (m := s) fun i hi => ?_
  fin_cases i
  · exact e0 hi
  · exact e1 hi

end U2DBasis

theorem uc22r8u2d_exists_orderOf_normalizer {M X S : Subgroup G} (hXM : X ≤ M)
    (hMX : M ≤ normalizer (X : Set G)) {r : ℕ} (hr : r.Prime)
    (hS : CFSG.ABGLocalTools.IsSylowOf r S X) {p : ℕ} (hp : p.Prime) {e : G} (heM : e ∈ M)
    (heX : e ∉ X) (hep : e ^ p = 1) : ∃ y ∈ normalizer (S : Set G) ⊓ M, orderOf y = p := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk, hkN⟩ := uc22r8100b_frattini hS (hMX heM)
  have hkM : k ∈ M := hXM hk
  have hnM : k⁻¹ * e ∈ M := M.mul_mem (M.inv_mem hkM) heM
  have : (X.subgroupOf M).Normal := (normal_subgroupOf_iff_le_normalizer hXM).2 hMX
  set π := QuotientGroup.mk' (X.subgroupOf M) with hπ
  have hπk : π ⟨k, hkM⟩ = 1 := (QuotientGroup.eq_one_iff _).2 hk
  have hπn : π ⟨k⁻¹ * e, hnM⟩ = π ⟨e, heM⟩ := by
    rw [show (⟨k⁻¹ * e, hnM⟩ : ↥M) = (⟨k, hkM⟩ : ↥M)⁻¹ * ⟨e, heM⟩ from rfl, map_mul, map_inv, hπk,
      inv_one, one_mul]
  have hπo : orderOf (π ⟨e, heM⟩) = p := by
    refine orderOf_eq_prime ?_ fun h =>
      heX ((QuotientGroup.eq_one_iff (N := X.subgroupOf M) (⟨e, heM⟩ : ↥M)).1 h)
    rw [← map_pow, show (⟨e, heM⟩ : ↥M) ^ p = 1 from Subtype.ext hep, map_one]
  have hpn : p ∣ orderOf (k⁻¹ * e) := by
    have h := orderOf_map_dvd π ⟨k⁻¹ * e, hnM⟩
    rwa [hπn, hπo, Subgroup.orderOf_mk] at h
  exact ⟨(k⁻¹ * e) ^ (orderOf (k⁻¹ * e) / p), mem_inf.2 ⟨pow_mem hkN _, pow_mem hnM _⟩,
    orderOf_pow_orderOf_div (orderOf_pos _).ne' hpn⟩

theorem uc22r8u2d_exists_pElement {D : Data G} (hSg : UC6S846.SigmaStd D) {L K : Subgroup G}
    (hL : L ∈ calC D.M) (hK : K ∈ calC D.M) (hne : K ≠ L) (hset : conjSetOf D.M L = {L, K})
    {n : ℕ} (hLS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) {p : ℕ} (hp : p ∈ D.sig) {r : ℕ}
    (hr : r.Prime) {R E : Subgroup G} (hR : CFSG.ABGLocalTools.IsSylowOf r R D.M) (hER : E ≤ R)
    (hEX : E ≤ L ⊔ K) (hEel : IsElemAbelian r E) (hΩ : ∀ x ∈ R, x ^ r = 1 → x ∈ E) :
    ∃ y ∈ normalizer (E : Set G) ⊓ D.M, orderOf y = p := by
  obtain ⟨hpP, hp2⟩ := D.sig_prime p hp
  have : Fact p.Prime := ⟨hpP⟩
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLM : L ≤ D.M := uc22p22a_le_of_isSubnormal hL.1
  have hKM : K ≤ D.M := uc22p22a_le_of_isSubnormal hK.1
  have hXM : L ⊔ K ≤ D.M := sup_le hLM hKM
  have hMX : D.M ≤ normalizer ((L ⊔ K : Subgroup G) : Set G) := fun t ht => by
    have h : (L ⊔ K).map (MulAut.conj t).toMonoidHom = L ⊔ K := by
      rw [Subgroup.map_sup]
      rcases uc22r8u2d_conj_cases hne hset ht with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · have h0' : L.map (MulAut.conj t).toMonoidHom = L := mem_normalizer_iff_map_conj_eq.1 h0
        have h1' : K.map (MulAut.conj t).toMonoidHom = K := mem_normalizer_iff_map_conj_eq.1 h1
        rw [h0', h1']
      · rw [h0, h1, sup_comm]
    exact mem_normalizer_iff_map_conj_eq.2 h
  obtain ⟨B, hBM, hBel, hBc⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank hpP (hSg.three_le p hp)
  have hBX : ¬ B ≤ L ⊔ K := by
    intro hle
    obtain ⟨hcomm, hinf, -⟩ := u4x_bar_structure hL hK hne hset hLS
    have hKmem : K ∈ conjSetOf D.M L := by
      rw [hset]
      exact Set.mem_insert_of_mem L (Set.mem_singleton K)
    obtain ⟨eL, -⟩ := uc22p22l_barImage_equiv hL
    obtain ⟨eK, -⟩ := uc22p22l_barImage_equiv hK
    have hbarL : IsL2 (barImage D.M L) n ∨ IsSz (barImage D.M L) n :=
      hLS.imp (fun h => CFSG.Blueprint.LieModel.of_mulEquiv eL h)
        (fun h => CFSG.Blueprint.LieModel.of_mulEquiv eL h)
    have hbarK : IsL2 (barImage D.M K) n ∨ IsSz (barImage D.M K) n :=
      (uc22s21r899_shape_of_mem hKmem hLS).imp (fun h => CFSG.Blueprint.LieModel.of_mulEquiv eK h)
        (fun h => CFSG.Blueprint.LieModel.of_mulEquiv eK h)
    have hdisj : Disjoint (B.subgroupOf D.M) (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)).ker := by
      rw [QuotientGroup.ker_mk']
      exact IsPGroup.disjoint_of_ne _ _ hp2 _ _ hBel.isPGroup.comap_subtype CFSG.pCore_isPGroup
    have hc : Nat.card (barImage D.M B) = p ^ 3 := by
      rw [barImage, UC6S846.card_map_of_disjoint_ker _ _ hdisj, ← hBc]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBM).toEquiv
    have hle' : barImage D.M B ≤ barImage D.M L ⊔ barImage D.M K := by
      rw [← u4x_barImage_sup hLM hKM]
      intro q hq
      obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 hq
      exact uc22p21c_mem_barImage.2 ⟨m, hle hm, rfl⟩
    have hrk := CFSG.SectionRank.le_pRank hpP.one_lt hle' ((hBel.subgroupOf D.M).map _) hc
    rw [PartTwo.s13_pRank_sup_eq_add hpP (fun y hy => mem_centralizer_iff.2
        fun x hx => hcomm x hx y hy) hinf,
      CFSG.SectionRank.pRank_eq_pRank_top_subgroup (barImage D.M L),
      CFSG.SectionRank.pRank_eq_pRank_top_subgroup (barImage D.M K)] at hrk
    have h₀ := pRank_le_one_of_isL2_or_isSz hbarL hpP hp2
    have h₁ := pRank_le_one_of_isL2_or_isSz hbarK hpP hp2
    omega
  obtain ⟨e, heB, heX⟩ := SetLike.not_le_iff_exists.1 hBX
  obtain ⟨y, hyS, hyo⟩ := uc22r8u2d_exists_orderOf_normalizer hXM hMX hr
    (hR.inf_of_le_normalizer hXM hMX) hpP (hBM heB) heX (hBel.2 e heB)
  have hES : E ≤ R ⊓ (L ⊔ K) := le_inf hER hEX
  refine ⟨y, mem_inf.2 ⟨mem_normalizer_fintype fun x hx => ?_, (mem_inf.1 hyS).2⟩, hyo⟩
  refine hΩ _ (mem_inf.1 ((mem_normalizer_iff.1 (mem_inf.1 hyS).1 x).1 (hES hx))).1 ?_
  rw [conj_pow, hEel.2 x hx, mul_one, mul_inv_cancel]

end CFSG.LocalAnalysis.UniquenessCase.UC22
