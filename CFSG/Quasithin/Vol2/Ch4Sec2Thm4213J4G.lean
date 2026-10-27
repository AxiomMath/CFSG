module

public import CFSG.Quasithin.Vol2.Ch4Sec2Lem4212C

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits CFSG.Quasithin.A4

namespace NoJ4

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizer_le (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    {T M L Mm I H K : Subgroup G} (hy : Hyp4_2_3 G T M L Mm I) (c : Conf4212 G T M L I H K)
    {r : G} (hrK : r ∈ Subgroup.centralizer (K : Set G)) (hr1 : r ≠ 1) (hr2 : r * r = 1)
    (hrI : I ≤ Subgroup.centralizer ({r} : Set G)) :
    pCoreOf 2 (L ⊔ T) ⊓ Subgroup.normalizer (pCoreOf 2 I : Set G) ⊓
      Subgroup.centralizer ({r} : Set G) ≤ pCoreOf 2 I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H₀ := Subgroup.centralizer ({r} : Set G) with hH₀
  set R := pCoreOf 2 I with hR
  set Rp := pCoreOf 2 (L ⊔ T) with hRp
  have h41 : Hyp4_1_1 G T M (conjClosure L T) := lemma_4_2_2 h37 h38 h39 hy.toHyp4_2_1
  have hord : orderOf r = 2 := orderOf_eq_prime (by rw [pow_two]; exact hr2) hr1
  have hrH₀ : r ∈ H₀ := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hZ : Subgroup.zpowers r ≤ pCoreOf 2 H₀ := by
    refine le_pCoreOf_of_le_normalizer 2 (Subgroup.zpowers_le.mpr hrH₀) ?_ ?_
    · intro h hh
      refine Subgroup.mem_normalizer_fintype fun y hy' => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy'
      have hhr : h * r * h⁻¹ = r := by
        rw [Subgroup.mem_centralizer_singleton_iff.mp hh, mul_inv_cancel_right]
      rw [← conj_zpow, hhr]
      exact Subgroup.zpow_mem_zpowers r k
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hO : pCoreOf 2 H₀ ≠ ⊥ := fun h => hr1 (by
    have := hZ (Subgroup.mem_zpowers r)
    rwa [h, Subgroup.mem_bot] at this)
  have hKH₀ : K ≤ H₀ := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hrK k hk)
  have hH₀M : ¬ H₀ ≤ M := fun h => c.K_not_le (hKH₀.trans h)
  have h4 := (lemma_4_1_4_four h41 hy.sigma hy.gammaStar ⟨hrI, hO⟩ hH₀M).1
  rw [c.conjClosure_eq] at h4
  set Hp := oTwoUpper (L ⊓ H₀) with hHp
  have hHpL : Hp ≤ L := (oTwoUpper_le _).trans inf_le_left
  have hLTL : L ⊔ T ≤ Subgroup.normalizer (L : Set G) :=
    _root_.sup_le Subgroup.le_normalizer (c.hyp421.T_le.trans c.normal)
  have hLTRp : L ⊔ T ≤ Subgroup.normalizer (Rp : Set G) := le_normalizer_pCoreOf 2 (L ⊔ T)
  set A := Rp ⊓ Subgroup.normalizer (R : Set G) ⊓ H₀ with hA
  have hAC : A ≤ centralizerSection H₀ Hp (pCoreOf 2 Hp) := by
    intro x hx
    have hxRp : x ∈ Rp := hx.1.1
    have hxLT : x ∈ L ⊔ T := pCoreOf_le 2 (L ⊔ T) hxRp
    have hxH : x ∈ H₀ := hx.2
    have hxN : x ∈ Subgroup.normalizer (Hp : Set G) :=
      normalizer_le_normalizer_oTwoUpper _
        (mem_normalizer_inf (hLTL hxLT) (Subgroup.le_normalizer hxH))
    refine ⟨hxH, hxN, normalizer_le_normalizer_pCoreOf 2 Hp hxN, fun h hh => ?_⟩
    have h1 : h * x * h⁻¹ * x⁻¹ ∈ Hp := by
      have := (Subgroup.mem_normalizer_iff.mp hxN h⁻¹).mp (Hp.inv_mem hh)
      have e : h * x * h⁻¹ * x⁻¹ = h * (x * h⁻¹ * x⁻¹) := by group
      rw [e]
      exact Hp.mul_mem hh this
    have h2 : h * x * h⁻¹ * x⁻¹ ∈ Rp := by
      have := (Subgroup.mem_normalizer_iff.mp (hLTRp (Subgroup.mem_sup_left (hHpL hh))) x).mp
        hxRp
      exact Rp.mul_mem this (Rp.inv_mem hxRp)
    have hn : Hp ≤ Subgroup.normalizer ((Hp ⊓ Rp : Subgroup G) : Set G) := fun y hy' =>
      mem_normalizer_inf (Subgroup.le_normalizer hy') (hLTRp (Subgroup.mem_sup_left (hHpL hy')))
    exact le_pCoreOf_of_le_normalizer 2 inf_le_left hn
      ((pCoreOf_isPGroup 2 (L ⊔ T)).to_le inf_le_right) ⟨h1, h2⟩
  have hA2 : IsPGroup 2 ↥A := (pCoreOf_isPGroup 2 (L ⊔ T)).to_le (inf_le_left.trans inf_le_left)
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := inf_le_left.trans inf_le_right
  have hP2 : IsPGroup 2 ↥(A ⊔ R) :=
    IsPGroup.to_sup_of_normal_right' hA2 (pCoreOf_isPGroup 2 I) hAR
  have hPC : A ⊔ R ≤ centralizerSection H₀ Hp (pCoreOf 2 Hp) := _root_.sup_le hAC h4.1
  exact le_sup_left.trans ((isSylowTwoOf_iff_maximal.mp h4).2.2 _ hPC hP2 le_sup_right)

theorem pCoreOf_lt (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    {T M L Mm I H K : Subgroup G} (hy : Hyp4_2_3 G T M L Mm I) (hIH : InM I H)
    (c : Conf4212 G T M L I H K) (hTin : T ≤ L ⊔ pCoreOf 2 (L ⊔ T)) :
    pCoreOf 2 I < pCoreOf 2 (L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine lt_of_le_of_ne c.R_le fun he => c.not_le ?_
  have hLTL : L ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    (_root_.sup_le Subgroup.le_normalizer (c.hyp421.T_le.trans c.normal)).trans
      (normalizer_le_normalizer_pCoreOf 2 L)
  have hO : pCoreOf 2 L ≤ pCoreOf 2 I := by
    rw [he]
    exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left) hLTL
      (pCoreOf_isPGroup 2 L)
  have hLI : L ≤ I := by
    have h1 : L ≤ I ⊔ pCoreOf 2 L := by
      have := hy.gammaStar.1.1.2.2.1
      rwa [c.conjClosure_eq] at this
    exact h1.trans (_root_.sup_le le_rfl (hO.trans (pCoreOf_le 2 I)))
  have hTI : T ≤ I := by
    refine hTin.trans (_root_.sup_le hLI ?_)
    rw [← he]
    exact pCoreOf_le 2 I
  have hU := (c.hyp421.isUniqueM_sup h37 h38 h39).1
  have hHM : H = M := hU.2 H ⟨hIH.1, (_root_.sup_le hLI hTI).trans hIH.2⟩
  exact hHM.le

theorem lt_inf_normalizer {I L T : Subgroup G} (hlt : pCoreOf 2 I < pCoreOf 2 (L ⊔ T)) :
    pCoreOf 2 I < pCoreOf 2 (L ⊔ T) ⊓ Subgroup.normalizer (pCoreOf 2 I : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hy, hyN, hyR⟩ := exists_mem_normalizer_not_mem (pCoreOf_isPGroup 2 (L ⊔ T)) hlt
  refine lt_of_le_of_ne (le_inf hlt.le Subgroup.le_normalizer) fun he => hyR ?_
  rw [he]
  exact ⟨hy, hyN⟩

end NoJ4

end CFSG.Quasithin.H13.Ch4
