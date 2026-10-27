module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.CalLCentral
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846g
public import CFSG.GroupTheory.Commutator.ThreeSubgroupsModNormal
public import CFSG.GroupTheory.SubgroupOfLattice
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeBasics

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Quasithin.E1
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem commutator_le_pCoreOf_of_mem_calL {T M L R : Subgroup G} (hL : L ∈ calL T M)
    (hRL : R ≤ L) (hLR : L ≤ Subgroup.normalizer (R : Set G))
    (hTR : T ≤ Subgroup.normalizer (R : Set G))
    (hR : ¬ L ≤ R ⊔ CFSG.Open.pCoreOf 2 L) :
    ⁅R, L⁆ ≤ CFSG.Open.pCoreOf 2 L := by
  have hcomm := commutator_mem_pCoreOf_of_mem_calL (T := T) (M := M) hL hRL hLR hTR hR
  exact Subgroup.commutator_le.mpr fun x hx y hy => by
    simpa only [commutatorElement_def] using hcomm x hx y hy

theorem commutator_le_pCoreOf_of_rotate {H L R Q : Subgroup G} (hLH : L ≤ H) (hRH : R ≤ H)
    (hQH : Q ≤ H) (hHQ : H ≤ Subgroup.normalizer (Q : Set G)) (hLperf : ⁅L, L⁆ = L)
    (hdouble : ⁅⁅R, L⁆, L⁆ ≤ Q) : ⁅R, L⁆ ≤ Q := by
  have hdouble' : ⁅⁅L, R⁆, L⁆ ≤ Q := by
    rw [Subgroup.commutator_comm L R]
    exact hdouble
  have h3 := CFSG.GroupTheory.commutator_commutator_le_of_rotate_normal
    (M := H) (A := L) (B := R) (N := Q) hLH hRH hQH hHQ hdouble' hdouble
  rw [hLperf] at h3
  rw [Subgroup.commutator_comm R L]
  exact h3

theorem Ctx23L.commutator_le_pCoreOf {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {R : Subgroup G} (hR : R ≤ c.L0 ⊔ D.T)
    (hRn : (R.subgroupOf (c.L0 ⊔ D.T)).Normal) (hRM : R ≤ D.M) :
    ⁅R, c.L0⁆ ≤ CFSG.Open.pCoreOf 2 c.L0 := by
  have hHnR : c.L0 ⊔ D.T ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hR).mp hRn
  have hRnL : R ≤ Subgroup.normalizer (c.L0 : Set G) :=
    hR.trans (sup_le Subgroup.le_normalizer c.hL0.1.1)
  have hleL0 : ⁅R, c.L0⁆ ≤ c.L0 :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp hRnL
  have hleR : ⁅R, c.L0⁆ ≤ R :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((le_sup_left : c.L0 ≤ c.L0 ⊔ D.T).trans hHnR)
  have hLR : c.L0 ≤ Subgroup.normalizer ((⁅R, c.L0⁆ : Subgroup G) : Set G) :=
    CFSG.GorensteinWalter.le_normalizer_commutator_of_le_normalizer c.L0 R c.L0
      ((le_sup_left : c.L0 ≤ c.L0 ⊔ D.T).trans hHnR) Subgroup.le_normalizer
  have hTR : D.T ≤ Subgroup.normalizer ((⁅R, c.L0⁆ : Subgroup G) : Set G) :=
    CFSG.GorensteinWalter.le_normalizer_commutator_of_le_normalizer D.T R c.L0
      ((le_sup_right : D.T ≤ c.L0 ⊔ D.T).trans hHnR) c.hL0.1.1
  have hQleL : CFSG.Open.pCoreOf 2 c.L0 ≤ c.L0 :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 c.L0
  have hQleH : CFSG.Open.pCoreOf 2 c.L0 ≤ c.L0 ⊔ D.T := hQleL.trans le_sup_left
  have hQleTL : CFSG.Open.pCoreOf 2 c.L0 ≤ D.T ⊓ c.L0 :=
    pCoreOf_two_le_of_isSylowIn (isSylowIn_T_inf c)
  have hQleT : CFSG.Open.pCoreOf 2 c.L0 ≤ D.T := hQleTL.trans inf_le_left
  have hQleM : CFSG.Open.pCoreOf 2 c.L0 ≤ D.M := hQleT.trans D.sylowM.le
  have hHnQ : c.L0 ⊔ D.T ≤
      Subgroup.normalizer ((CFSG.Open.pCoreOf 2 c.L0 : Subgroup G) : Set G) :=
    sup_le (Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) c.L0))
      (c.hL0.1.1.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) c.L0))
  have hR1not : ¬ c.L0 ≤ ⁅R, c.L0⁆ ⊔ CFSG.Open.pCoreOf 2 c.L0 := by
    intro hle
    exact L0_not_le_M c (hle.trans (sup_le (hleR.trans hRM) hQleM))
  have hdouble : ⁅⁅R, c.L0⁆, c.L0⁆ ≤ CFSG.Open.pCoreOf 2 c.L0 :=
    commutator_le_pCoreOf_of_mem_calL c.hL0.1 hleL0 hLR hTR hR1not
  exact commutator_le_pCoreOf_of_rotate (H := c.L0 ⊔ D.T) le_sup_left hR hQleH hHnQ
    c.hL0.1.2.1 hdouble

theorem Ctx23L.layer_bar2_eq_top {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch) :
    CFSG.layer (Bar2 c.L0) = ⊤ := by
  obtain ⟨K, hK, hLK⟩ := c.hL0.1.2.2.2
  have hKt : ∀ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom ∈ calC c.L0 :=
    fun t => UC6S846.calC_map c.L0 (MulAut.conj (t : G))
      (Subgroup.mem_normalizer_iff_map_conj_eq.1 (c.hL0.1.1 t.2)) hK
  have hFle : ∀ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom ≤ c.L0 := by
    intro t
    rw [hLK]
    exact le_iSup (fun t : D.T => K.map (MulAut.conj (t : G)).toMonoidHom) t
  have hsub : (⨆ t : D.T,
      (K.map (MulAut.conj (t : G)).toMonoidHom).subgroupOf c.L0) = ⊤ := by
    rw [← CFSG.subgroupOf_iSup
      (fun t : D.T => K.map (MulAut.conj (t : G)).toMonoidHom) hFle, ← hLK]
    exact Subgroup.subgroupOf_self c.L0
  have hjoin : (⨆ t : D.T, barImage c.L0 (K.map (MulAut.conj (t : G)).toMonoidHom)) =
      (⨆ t : D.T, (K.map (MulAut.conj (t : G)).toMonoidHom).subgroupOf c.L0).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L0)) := by
    simp only [barImage]
    exact (Subgroup.map_iSup _ _).symm
  have htop : (⨆ t : D.T, barImage c.L0 (K.map (MulAut.conj (t : G)).toMonoidHom)) = ⊤ := by
    rw [hjoin, hsub, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hle : (⊤ : Subgroup (Bar2 c.L0)) ≤ CFSG.layer (Bar2 c.L0) := by
    rw [← htop]
    exact iSup_le fun t => CFSG.LocalCores.component_le_layer
      (uc22p22l_barImage_isComponent (hKt t))
  exact top_le_iff.mp hle

theorem Ctx23L.solvable_normal_le_center_bar2 {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) {N : Subgroup (Bar2 c.L0)} (hN : N.Normal)
    (hNs : Group.IsSolvable ↥N) : N ≤ Subgroup.center (Bar2 c.L0) := by
  obtain ⟨-, hcomm⟩ := CFSG.LocalCores.component_solvable_centralizer hNs hN.isSubnormal
  rw [layer_bar2_eq_top c] at hcomm
  rw [Subgroup.commutator_comm] at hcomm
  have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  simpa only [Subgroup.coe_top, Subgroup.centralizer_univ] using hle

private theorem coprime_card_index_of_isPGroup_quotient {H : Type} [Group H] [Finite H]
    {K : Subgroup H} [K.Normal] (hKodd : Odd (Nat.card K))
    (hquot : IsPGroup 2 (H ⧸ K)) :
    Nat.Coprime (Nat.card K) K.index := by
  have hidx : K.index = Nat.card (H ⧸ K) := Subgroup.index_eq_card (H := K)
  rw [hidx]
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hquot
  rw [ha]
  exact hKodd.coprime_two_right.pow_right a

private theorem exists_two_complement {H : Type} [Group H] [Finite H]
    {K : Subgroup H} [K.Normal] (hKc : K ≤ Subgroup.center H) (hKodd : Odd (Nat.card K))
    (hquot : IsPGroup 2 (H ⧸ K)) :
    ∃ S : Subgroup H, IsPGroup 2 S ∧
      ∀ x : H, (∃ n : ℕ, x ^ (2 ^ n) = 1) → x ∈ S := by
  obtain ⟨S, hS⟩ := Subgroup.exists_right_complement'_of_coprime
    (coprime_card_index_of_isPGroup_quotient hKodd hquot)
  have hKS : K ⊔ S = ⊤ := hS.isCompl.sup_eq_top
  have hKdisj : K ⊓ S = ⊥ := hS.isCompl.inf_eq_bot
  refine ⟨S, IsPGroup.of_equiv hquot hS.symm.QuotientMulEquiv, ?_⟩
  rintro x ⟨n, hn⟩
  obtain ⟨k, hk, s, hs, hks⟩ :=
    Subgroup.mem_sup_of_normal_left.mp (hKS.symm ▸ Subgroup.mem_top x)
  have hcomm : Commute k s :=
    (Subgroup.mem_center_iff.mp (hKc hk) s).symm
  have h1 : k ^ 2 ^ n * s ^ 2 ^ n = 1 := by
    rw [← hcomm.mul_pow, hks, hn]
  have hkpow : k ^ 2 ^ n = 1 := by
    have hm : k ^ 2 ^ n ∈ K ⊓ S :=
      ⟨K.pow_mem hk _, by
        have h2 : k ^ 2 ^ n = (s ^ 2 ^ n)⁻¹ := eq_inv_of_mul_eq_one_left h1
        rw [h2]
        exact S.inv_mem (S.pow_mem hs _)⟩
    rw [hKdisj] at hm
    exact Subgroup.mem_bot.mp hm
  have hk1 : k = 1 := by
    have hdvd : orderOf k ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hkpow
    have hodd : Odd (orderOf k) :=
      Odd.of_dvd_nat hKodd (Subgroup.orderOf_dvd_natCard K hk)
    have hone : orderOf k = 1 :=
      Nat.eq_one_of_dvd_coprimes (a := 2 ^ n) (b := orderOf k) (k := orderOf k)
        (hodd.coprime_two_right.pow_right n).symm hdvd dvd_rfl
    exact orderOf_eq_one_iff.mp hone
  rw [← hks, hk1, one_mul]
  exact hs

theorem isPGroup_two_of_central_odd_quotient {H : Type} [Group H] [Finite H]
    {K : Subgroup H} [K.Normal] (hKc : K ≤ Subgroup.center H) (hKodd : Odd (Nat.card K))
    (hquot : IsPGroup 2 (H ⧸ K))
    (hgen : (⊤ : Subgroup H) ≤ Subgroup.closure {x : H | ∃ n : ℕ, x ^ (2 ^ n) = 1}) :
    IsPGroup 2 H := by
  obtain ⟨S, hS2, hmem⟩ := exists_two_complement hKc hKodd hquot
  have hgenS : Subgroup.closure {x : H | ∃ n : ℕ, x ^ (2 ^ n) = 1} ≤ S :=
    (Subgroup.closure_le S).mpr fun x hx => hmem x hx
  have htop : S = ⊤ := top_le_iff.mp (hgen.trans hgenS)
  rw [htop] at hS2
  exact IsPGroup.of_equiv hS2 Subgroup.topEquiv

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
