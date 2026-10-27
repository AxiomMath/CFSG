module

public import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarSylow
public import CFSG.RankThree.PartTwo.Sec4.Item426A6Setup
import CFSG.RankThree.PartTwo.Sec11.Item1115Proof
import CFSG.RankThree.PartTwo.KFacts.K71bCentList
public import CFSG.RankThree.PartTwo.Sec11.Item1119Proof

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

namespace Item1120V0Bar

theorem closure_cad_eq_zpowers_sup {G : Type*} [Group G] (c a d : G) :
    Subgroup.closure ({c, a, d} : Set G) =
      Subgroup.zpowers a ⊔ Subgroup.closure ({c, d} : Set G) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy | hy <;> rw [hy]
    · exact (le_sup_right : _ ≤ Subgroup.zpowers a ⊔ _) (Subgroup.subset_closure (by simp))
    · exact (le_sup_left : _ ≤ _ ⊔ Subgroup.closure ({c, d} : Set G)) (Subgroup.mem_zpowers a)
    · exact (le_sup_right : _ ≤ Subgroup.zpowers a ⊔ _) (Subgroup.subset_closure (by simp))
  · refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))) ?_
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy <;> rw [hy] <;> exact Subgroup.subset_closure (by simp)

theorem mem_normalizer_closure_pair_c_d {G : Type*} [Group G] [Finite G] {c d w : G}
    (hc : w * c * w⁻¹ ∈ Subgroup.closure ({c, d} : Set G))
    (hd : w * d * w⁻¹ ∈ Subgroup.closure ({c, d} : Set G)) :
    w ∈ Subgroup.normalizer ((Subgroup.closure ({c, d} : Set G) : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  have hle : Subgroup.closure ({c, d} : Set G) ≤
      (Subgroup.closure ({c, d} : Set G)).comap (MulAut.conj w).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    rcases hy with hy | hy <;> rw [hy]
    · exact hc
    · exact hd
  exact hle hz

theorem zpowers_inf_centralizer_le_cube {G : Type} [Group G] {t b : G} {k : ℕ}
    (hk : t ^ 3 ^ k = 1) (htb : t ∉ Subgroup.centralizer ({b} : Set G)) {y : G}
    (hyt : y ∈ Subgroup.zpowers t) (hyb : y ∈ Subgroup.centralizer ({b} : Set G)) :
    y ∈ Subgroup.zpowers (t ^ 3) := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyt
  by_cases h3 : (3 : ℤ) ∣ m
  · obtain ⟨j, rfl⟩ := h3
    have e : t ^ (3 * j) = (t ^ 3) ^ j := by rw [zpow_mul, zpow_ofNat]
    rw [e]
    exact Subgroup.zpow_mem_zpowers _ j
  · exfalso
    apply htb
    obtain ⟨u, v, huv⟩ := Irreducible.coprime_pow_of_not_dvd k Int.prime_three.irreducible h3
    have hN : t ^ ((3 : ℤ) ^ k) = 1 := by
      have e : (3 : ℤ) ^ k = ((3 ^ k : ℕ) : ℤ) := by norm_cast
      rw [e, zpow_natCast, hk]
    have e1 : t ^ (u * m + v * (3 : ℤ) ^ k) = t ^ (u * m) * t ^ (v * (3 : ℤ) ^ k) :=
      zpow_add t _ _
    have e2 : t ^ (v * (3 : ℤ) ^ k) = 1 := by rw [mul_comm, zpow_mul, hN, one_zpow]
    have e3 : t ^ (u * m) = (t ^ m) ^ u := by rw [mul_comm, zpow_mul]
    have key : t = (t ^ m) ^ u := by
      calc t = t ^ (u * m + v * (3 : ℤ) ^ k) := by rw [huv, zpow_one]
        _ = t ^ (u * m) * t ^ (v * (3 : ℤ) ^ k) := e1
        _ = (t ^ m) ^ u := by rw [e2, mul_one, e3]
    rw [key]
    exact Subgroup.zpow_mem _ hyb u



variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

noncomputable abbrev imgJ (Y L : Subgroup G) (a : G) :
    Subgroup (Y ⧸ aschbacherSolvableCore 3 Y) :=
  ((sec11K L a).subgroupOf Y).map (QuotientGroup.mk' (aschbacherSolvableCore 3 Y))

theorem isSylowOf_inf_centralizer_a (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) :
    IsSylowOf 3 (R ⊓ Subgroup.centralizer ({a} : Set G))
      (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.centralizer ({a} : Set G)) := by
  have hDC : Subgroup.closure ({c, d} : Set G) ≤ Subgroup.centralizer (R : Set G) := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    rcases hy with hy | hy <;> rw [hy]
    · intro u hu
      exact Subgroup.mem_centralizer_singleton_iff.mp (Item1119Proof.R_le_centralizer_c h hu)
    · intro u hu
      exact Item1119Proof.commute_d h113 h117 h (Item1119Proof.R_le_P R g hu)
  have hDR : ∀ u ∈ Subgroup.closure ({c, d} : Set G), ∀ t ∈ R, u * t = t * u :=
    fun u hu t ht => ((Subgroup.mem_centralizer_iff.mp (hDC hu)) t ht).symm
  have hAD : A = Subgroup.zpowers a ⊔ Subgroup.closure ({c, d} : Set G) :=
    h.closure_eq.trans (closure_cad_eq_zpowers_sup c a d)
  have haD : a ∉ Subgroup.closure ({c, d} : Set G) :=
    (h.toSec11Std.not_mem_facts h.inf_eq h.closure_eq).2.1
  have hNH : ∀ w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G),
      w ∈ Subgroup.normalizer (A : Set G) →
        w ∈ Subgroup.normalizer ((Subgroup.closure ({c, d} : Set G) : Subgroup G) : Set G) := by
    intro w hwH hwA
    have hcD : c ∈ Subgroup.closure ({c, d} : Set G) := Subgroup.subset_closure (by simp)
    have hdD : d ∈ Subgroup.closure ({c, d} : Set G) := Subgroup.subset_closure (by simp)
    have hc : w * c * w⁻¹ ∈ Subgroup.closure ({c, d} : Set G) :=
      Subgroup.zpowers_le.mpr hcD
        ((Subgroup.mem_normalizer_iff.mp hwH c).mp (Subgroup.mem_zpowers c))
    have hd : w * d * w⁻¹ ∈ Subgroup.closure ({c, d} : Set G) :=
      Subgroup.zpowers_le.mpr hdD
        ((Subgroup.mem_normalizer_iff.mp (Item1115Proof.W_le_normalizer_d h117 h hwA) d).mp
          (Subgroup.mem_zpowers d))
    exact mem_normalizer_closure_pair_c_d hc hd
  exact isSylowOf_inf_centralizer_of_weakClosure h.isSylowOf (Item1115Proof.A_le_R h.toHyp91)
    (fun y hy => h.mem_partTwoF.1.2 y hy)
    (fun y hyR hy3 => Item1119Proof.mem_A_of_mem_R h113 h hyR hy3)
    (fun u hu v hv => congrArg Subtype.val (h.mem_partTwoF.1.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩))
    h.a_mem (Item1119Proof.closure_cd_le_A h) hDR hAD haD hNH


theorem x_cube_mem_sec11K (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g) :
    x ^ 3 ∈ sec11K L a := by
  obtain ⟨haN, ha3, -, hQ⟩ := h.toSec11Std.a_facts
  have hxL : x ∈ L := by
    have : x ∈ R ⊓ L := by
      rw [h.inf_L_eq]
      exact Subgroup.mem_zpowers x
    exact this.2
  obtain ⟨n, hn⟩ := Item1116Proof.exists_pow_eq_one_of_mem h (Item1116Proof.mem_R h).2.1
  have hxa := (Item1119Proof.a_x_facts h45 h).1
  have hC : x ^ 3 ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x ^ 3 * a = a * x ^ 3 * a⁻¹ * a := by rw [hxa]
      _ = a * x ^ 3 := by group
  refine mem_sec11K_of_pow_eq_one haN ha3 hQ.1 ⟨L.pow_mem hxL 3, hC⟩ (k := n) ?_
  rw [← pow_mul, mul_comm, pow_mul, hn, one_pow]

theorem isSylowOf_zpowers_x_cube (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) :
    IsSylowOf 3 (Subgroup.zpowers (x ^ 3)) (sec11K L a) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hCcH : Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    rw [CFSG.RankThree.GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers]
    exact Subgroup.centralizer_le_normalizer _
  have hLCc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    CFSG.RankThree.PartTwo.Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  obtain ⟨hRCc, hRL⟩ := Item1116Proof.le_centralizer_and_normalizer h45 h
  have hRH : R ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := hRCc.trans hCcH
  have hsyl1 := isSylowOf_inf_centralizer_a h113 h117 h
  have hRN : R ⊓ Subgroup.centralizer ({a} : Set G) ≤
      (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.centralizer ({a} : Set G)) ⊓
        Subgroup.normalizer (L : Set G) := by
    rintro y ⟨hyR, hyC⟩
    exact ⟨⟨hRH hyR, hyC⟩, hRL hyR⟩
  have hsyl2 := hsyl1.of_le hRN inf_le_left
  have hML : L ⊓ Subgroup.centralizer ({a} : Set G) ≤
      (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.centralizer ({a} : Set G)) ⊓
        Subgroup.normalizer (L : Set G) := by
    rintro y ⟨hyL, hyC⟩
    exact ⟨⟨hCcH (hLCc hyL), hyC⟩, Subgroup.le_normalizer hyL⟩
  have hNM : (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.centralizer ({a} : Set G)) ⊓ Subgroup.normalizer (L : Set G) ≤
      Subgroup.normalizer ((L ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) := by
    rintro y ⟨⟨-, hyC⟩, hyN⟩
    exact Item1116Proof.mem_normalizer_inf hyN (Subgroup.le_normalizer hyC)
  have hsyl3 := hsyl2.inf_of_le_normalizer hML hNM
  have hxR : x ∈ R := (Item1116Proof.mem_R h).2.1
  have hxL : x ∈ L := by
    have hx : x ∈ R ⊓ L := by
      rw [h.inf_L_eq]
      exact Subgroup.mem_zpowers x
    exact hx.2
  have hxC : x ∉ Subgroup.centralizer ({a} : Set G) := by
    intro hxC
    apply Item1116Proof.not_le_centralizer_of_isSylowOf h.toSec11Std h.toSec11Std.isSylowOf_inf_L
    rw [h.inf_L_eq]
    exact Subgroup.zpowers_le.mpr hxC
  obtain ⟨k, hk⟩ := Item1116Proof.exists_pow_eq_one_of_mem h hxR
  have hKL : sec11K L a ≤ L := sec11K_le L a
  have hKC : sec11K L a ≤ Subgroup.centralizer ({a} : Set G) :=
    (Subgroup.map_subtype_le _).trans inf_le_right
  have hKLC : sec11K L a ≤ L ⊓ Subgroup.centralizer ({a} : Set G) := le_inf hKL hKC
  have hx3K : x ^ 3 ∈ sec11K L a := x_cube_mem_sec11K h45 h
  have hx3R : x ^ 3 ∈ R := R.pow_mem hxR 3
  have hEq : (R ⊓ Subgroup.centralizer ({a} : Set G)) ⊓ (L ⊓ Subgroup.centralizer ({a} : Set G)) =
      Subgroup.zpowers (x ^ 3) := by
    apply le_antisymm
    · rintro y ⟨⟨hyR, hyC⟩, hyL, -⟩
      have hyx : y ∈ R ⊓ L := ⟨hyR, hyL⟩
      rw [h.inf_L_eq] at hyx
      exact zpowers_inf_centralizer_le_cube hk hxC hyx hyC
    · exact Subgroup.zpowers_le.mpr ⟨⟨hx3R, hKC hx3K⟩, ⟨hKL hx3K, hKC hx3K⟩⟩
  have hsyl4 : IsSylowOf 3 (Subgroup.zpowers (x ^ 3))
      (L ⊓ Subgroup.centralizer ({a} : Set G)) := by
    rw [← hEq]
    exact hsyl3
  exact hsyl4.of_le (Subgroup.zpowers_le.mpr hx3K) hKLC


theorem commutator_mem_theta_sec11K_of_fixes (h : Sec11Std G A c L a R Y) {w : G}
    (hwL : w ∈ Subgroup.normalizer (L : Set G)) (hwa : w * a = a * w)
    (hwY : w ∈ Subgroup.normalizer (Y : Set G))
    (hfix : ∀ j ∈ imgJ Y L a, Sec4.Item426.thetaAut Y hwY j = j) :
    ∀ k ∈ sec11K L a, w * k * w⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) (sec11K L a) := by
  intro k hk
  have hkY : k ∈ Y := h.sec11K_le hk
  have hwN : w ∈ Subgroup.normalizer (sec11K L a : Set G) :=
    GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual _
      (GroupTheory.SteinbergBY.mem_normalizer_inf hwL
        (Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hwa)))
  have h1 : w * k * w⁻¹ * k⁻¹ ∈ sec11K L a :=
    (sec11K L a).mul_mem ((Subgroup.mem_normalizer_iff.mp hwN k).mp hk)
      ((sec11K L a).inv_mem hk)
  have h2 : w * k * w⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) Y := by
    have hj : QuotientGroup.mk' (aschbacherSolvableCore 3 Y) (⟨k, hkY⟩ : Y) ∈ imgJ Y L a :=
      Subgroup.mem_map_of_mem (QuotientGroup.mk' (aschbacherSolvableCore 3 Y))
        (Subgroup.mem_subgroupOf.mpr hk)
    have hf : ((Sec4.compAction Y ⟨w, hwY⟩ ⟨k, hkY⟩ : Y) : Y ⧸ aschbacherSolvableCore 3 Y) =
        ((⟨k, hkY⟩ : Y) : Y ⧸ aschbacherSolvableCore 3 Y) := hfix _ hj
    have hmem : (⟨k, hkY⟩ : Y)⁻¹ * Sec4.compAction Y ⟨w, hwY⟩ ⟨k, hkY⟩ ∈
        aschbacherSolvableCore 3 Y := QuotientGroup.eq.mp hf.symm
    have hG : k⁻¹ * (w * k * w⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) Y := by
      refine Subgroup.mem_map.mpr ⟨_, hmem, ?_⟩
      simp [Sec4.Item426.coe_compAction_apply]
    have e : w * k * w⁻¹ * k⁻¹ = k * (k⁻¹ * (w * k * w⁻¹)) * k⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta Y hkY) _).mp hG
  exact Sec13.inf_inSubgroup_theta_le h.sec11K_le ⟨h1, h2⟩

theorem mem_zpowers_s_sup_zpowers_a_of_fixes (h45 : Sec4.Item4_5)
    (h : Sec11Data G A c L a R Y d x s r g) {w : G} (hwR : w ∈ R) (hwa : w * a = a * w)
    (hwY : w ∈ Subgroup.normalizer (Y : Set G))
    (hfix : ∀ j ∈ imgJ Y L a, Sec4.Item426.thetaAut Y hwY j = j) :
    w ∈ Subgroup.zpowers s ⊔ Subgroup.zpowers a := by
  have hRL := (Item1116Proof.le_centralizer_and_normalizer h45 h).2
  have hout : Sec4.InducesOuterTheta a L := by
    rcases h.inducesStdKind with hf | hf
    · exact KFacts.InducesStdKind.inducesOuterTheta L hf (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta L hf (by decide)
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have haR : a ∈ R := Item1115Proof.A_le_R h.toHyp91 h.a_mem
  have htK := commutator_mem_theta_sec11K_of_fixes h.toSec11Std (hRL hwR) hwa hwY hfix
  obtain ⟨i, hi⟩ := KFacts.exists_mul_pow_mem_thetaQuotCentralizer_of_list h.isList1016 hout ha3
    (hRL hwR) (Item1116Proof.exists_pow_eq_one_of_mem h hwR) hwa htK
  have hus : w * a ^ i ∈ Subgroup.zpowers s := by
    rw [← h.inf_centralizer_eq]
    exact ⟨R.mul_mem hwR (R.pow_mem haR i), hi⟩
  have hmul := Subgroup.mul_mem (Subgroup.zpowers s ⊔ Subgroup.zpowers a)
    (Subgroup.mem_sup_left hus)
    (Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) i)))
  rwa [mul_inv_cancel_right] at hmul


end Item1120V0Bar

end CFSG.RankThree.PartTwo.Sec11

end
