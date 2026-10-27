module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22l
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
import CFSG.LocalAnalysis.UniquenessCase.UC22P20e
import CFSG.LocalAnalysis.UniquenessCase.UC6Dict

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem uc22p22u_calC_mono {X M : Subgroup G} (hX : IsSubnormal X M) : calC X ⊆ calC M := by
  rintro K ⟨hsub, hperf, hq⟩
  exact ⟨CFSG.Quasithin.A3.subnormal_trans hsub hX, hperf, hq⟩

theorem uc22p22u_isSolvable_pCoreOf (X : Subgroup G) : Group.IsSolvable ↥(pCoreOf 2 X) := by
  haveI : Group.IsNilpotent ↥(pCoreOf 2 X) := (uc22p21c_isPGroup_pCoreOf X).isNilpotent
  infer_instance

theorem uc22p22u_le_normalizer_pCoreOf {X K : Subgroup G} (hKX : K ≤ X) :
    K ≤ normalizer (pCoreOf 2 X : Set G) :=
  uc22p20e_le_normalizer_of_conj fun _ hy _ hx => uc22p21c_conj_mem_pCoreOf_self (hKX hy) hx

theorem uc22p22u_pCore_normalizes_calC {X K : Subgroup G} (hK : K ∈ calC X) :
    pCoreOf 2 X ≤ normalizer (K : Set G) := by
  have hKX : K ≤ X := CFSG.Quasithin.A3.subnormal_le hK.1
  have hcomm := (CFSG.Quasithin.cComp_commutator_perfectCore (uc22p20e_cComp_of_calC hK)
    (uc22p21c_pCoreOf_le X) (uc22p22u_isSolvable_pCoreOf X) (uc22p22u_le_normalizer_pCoreOf hKX)).1
  refine uc22p20e_le_normalizer_of_conj fun u hu k hk => ?_
  have h1 : ⁅u, k⁆ ∈ ⁅K, pCoreOf 2 X⁆ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hu hk
  have h2 : u * k * u⁻¹ = ⁅u, k⁆ * k := by
    simp only [commutatorElement_def]
    group
  rw [h2]
  exact K.mul_mem (hcomm h1) hk

theorem uc22p22u_calC_ext {X K₁ K₂ : Subgroup G} (h₁ : K₁ ∈ calC X) (h₂ : K₂ ∈ calC X)
    (h : barImage X K₁ = barImage X K₂) : K₁ = K₂ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hPn : (CFSG.pCore 2 ↥X).Normal := CFSG.pCore_normal
  haveI hPs := uc22p20d_pCore_solvable X
  have hc₁ := uc22p20e_cComp_of_calC h₁
  have hc₂ := uc22p20e_cComp_of_calC h₂
  have hbij := CFSG.Quasithin.cComp_quotient_bijOn (CFSG.pCore 2 ↥X) hPs
  have h1 := hbij.injOn (CFSG.Quasithin.subgroupOf_mem_cComp hc₁)
    (CFSG.Quasithin.subgroupOf_mem_cComp hc₂) h
  have h2 : K₁ ⊓ X = K₂ ⊓ X := Subgroup.subgroupOf_inj.mp h1
  rwa [inf_eq_left.mpr (CFSG.Quasithin.le_of_mem_cComp hc₁),
    inf_eq_left.mpr (CFSG.Quasithin.le_of_mem_cComp hc₂)] at h2

theorem uc22p22u_commutator_mem_pCoreOf {X : Subgroup G} {a b : G} (ha : a ∈ X) (hb : b ∈ X)
    (h : uc22p21cPi X ⟨a, ha⟩ * uc22p21cPi X ⟨b, hb⟩ = uc22p21cPi X ⟨b, hb⟩ * uc22p21cPi X ⟨a, ha⟩) :
    ⁅a, b⁆ ∈ pCoreOf 2 X := by
  have h3 : uc22p21cPi X ⁅(⟨a, ha⟩ : ↥X), ⟨b, hb⟩⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.2 h
  exact ⟨_, (QuotientGroup.eq_one_iff _).1 h3, by simp [commutatorElement_def]⟩

theorem uc22p22u_calC_normalizes {X K₁ K₂ : Subgroup G} (h₁ : K₁ ∈ calC X) (h₂ : K₂ ∈ calC X)
    (hne : K₁ ≠ K₂) : K₂ ≤ normalizer (K₁ : Set G) := by
  have hK₁X : K₁ ≤ X := CFSG.Quasithin.A3.subnormal_le h₁.1
  have hK₂X : K₂ ≤ X := CFSG.Quasithin.A3.subnormal_le h₂.1
  have hperf := (CFSG.Quasithin.cComp_commutator_perfectCore (uc22p20e_cComp_of_calC h₁)
    (uc22p21c_pCoreOf_le X) (uc22p22u_isSolvable_pCoreOf X) (uc22p22u_le_normalizer_pCoreOf hK₁X)).2
  have hcomm := uc22p22l_barImage_commute h₁ h₂ hne
  have hnormJ : K₂ ≤ normalizer ((K₁ ⊔ pCoreOf 2 X : Subgroup G) : Set G) := by
    refine uc22p20e_le_normalizer_of_conj fun y hy x hx => ?_
    have key : K₁ ⊔ pCoreOf 2 X ≤ (K₁ ⊔ pCoreOf 2 X).comap (MulAut.conj y).toMonoidHom := by
      refine sup_le (fun a ha => ?_) (fun u hu => ?_)
      · have hc : ⁅y, a⁆ ∈ pCoreOf 2 X :=
          uc22p22u_commutator_mem_pCoreOf (hK₂X hy) (hK₁X ha) (hcomm _
            (uc22p21c_mem_barImage.2 ⟨_, ha, rfl⟩) _ (uc22p21c_mem_barImage.2 ⟨_, hy, rfl⟩)).symm
        have h2 : y * a * y⁻¹ = ⁅y, a⁆ * a := by
          simp only [commutatorElement_def]
          group
        show y * a * y⁻¹ ∈ K₁ ⊔ pCoreOf 2 X
        rw [h2]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left ha)
      · exact Subgroup.mem_sup_right (uc22p21c_conj_mem_pCoreOf_self (hK₂X hy) hu)
    exact key hx
  have h3 := CFSG.Quasithin.normalizer_le_normalizer_perfectCore (K₁ ⊔ pCoreOf 2 X)
  rw [hperf] at h3
  exact hnormJ.trans h3

theorem uc22p22u_calC_permute {X K₁ K₂ : Subgroup G} (h₁ : K₁ ∈ calC X) (h₂ : K₂ ∈ calC X) :
    (K₁ : Set G) * (K₂ : Set G) = (K₂ : Set G) * (K₁ : Set G) := by
  by_cases hne : K₁ = K₂
  · rw [hne]
  · exact (Subgroup.set_mul_normalizer_comm (K₂ : Set G) K₁
      (uc22p22u_calC_normalizes h₁ h₂ hne)).symm

theorem uc22p22u_calC_conj {X M K : Subgroup G} (hN : M ≤ normalizer (X : Set G)) (hK : K ∈ calC X)
    {m : G} (hm : m ∈ M) : uniqueFourConj m K ∈ calC X := by
  have h := CFSG.Quasithin.cComp_map_mulEquiv (MulAut.conj m⁻¹) (uc22p20e_cComp_of_calC hK)
  have hX : X.map (MulAut.conj m⁻¹).toMonoidHom = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (hN (M.inv_mem hm))
  rw [hX] at h
  obtain ⟨e⟩ := uc22p20d_bar2_conj m⁻¹ K
  exact ⟨CFSG.Quasithin.subnormal_of_mem_cComp h, CFSG.Quasithin.perfect_of_mem_cComp h,
    CFSG.Open.IsQuasisimple.of_mulEquiv e.symm hK.2.2⟩

theorem uc22p22u_prod_list_eq_iSup (l : List (Subgroup G))
    (h : ∀ A ∈ l, ∀ B ∈ l, A ≤ normalizer (B : Set G)) :
    (l.map fun A : Subgroup G => (A : Set G)).prod = ((⨆ A ∈ l, A : Subgroup G) : Set G) := by
  induction l with
  | nil => simp [Set.singleton_one]
  | cons a l ih =>
    have ih' := ih fun A hA B hB => h A (List.mem_cons_of_mem _ hA) B (List.mem_cons_of_mem _ hB)
    have hsup : (⨆ A ∈ a :: l, A : Subgroup G) = a ⊔ ⨆ A ∈ l, A := by
      apply le_antisymm
      · refine iSup₂_le fun A hA => ?_
        rcases List.mem_cons.1 hA with rfl | hA
        · exact le_sup_left
        · exact le_sup_of_le_right (le_iSup₂ (f := fun A (_ : A ∈ l) => A) A hA)
      · refine sup_le (le_iSup₂ (f := fun A (_ : A ∈ a :: l) => A) a List.mem_cons_self) ?_
        exact iSup₂_le fun A hA =>
          le_iSup₂ (f := fun A (_ : A ∈ a :: l) => A) A (List.mem_cons_of_mem _ hA)
    have hnorm : a ≤ normalizer ((⨆ A ∈ l, A : Subgroup G) : Set G) :=
      uc22p20b_le_normalizer_iSup _ a fun B => uc22p20b_le_normalizer_iSup _ a fun hB =>
        h a List.mem_cons_self B (List.mem_cons_of_mem _ hB)
    rw [List.map_cons, List.prod_cons, ih', hsup, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm]

theorem uc22p22u_conjClosure_isProd {M X K : Subgroup G} (hXM : X ≤ M) (hN : M ≤ normalizer (X : Set G))
    (hK : K ∈ calC X) :
    conjClosure M K ≤ X ∧ M ≤ normalizer (conjClosure M K : Set G) ∧ F08.IsProdOfCalC M (conjClosure M K) := by
  classical
  have hXsub : IsSubnormal X M := CFSG.Quasithin.A3.subnormal_of_normal hXM
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hXM).2 hN)
  have hSX : ∀ A ∈ conjSetOf M K, A ∈ calC X := by
    rintro A ⟨g, hg, rfl⟩
    simpa [uniqueFourConj] using uc22p22u_calC_conj hN hK (M.inv_mem hg)
  have hpair : ∀ A ∈ conjSetOf M K, ∀ B ∈ conjSetOf M K, A ≤ normalizer (B : Set G) := by
    intro A hA B hB
    by_cases hAB : B = A
    · rw [hAB]
      exact Subgroup.le_normalizer
    · exact uc22p22u_calC_normalizes (hSX B hB) (hSX A hA) hAB
  set l : List (Subgroup G) := (Set.toFinite (conjSetOf M K)).toFinset.toList with hl
  have hmem : ∀ A, A ∈ l ↔ A ∈ conjSetOf M K := by
    intro A
    simp [hl]
  have hjoin : (⨆ A ∈ l, A : Subgroup G) = conjClosure M K := by
    unfold conjClosure
    exact iSup_congr fun A => iSup_congr_Prop (hmem A) fun _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · exact iSup₂_le fun A hA => CFSG.Quasithin.A3.subnormal_le (hSX A hA).1
  · refine uc22p20e_le_normalizer_of_conj fun m hm x hx => ?_
    have key : conjClosure M K ≤ (conjClosure M K).comap (MulAut.conj m).toMonoidHom := by
      refine iSup₂_le fun A hA => ?_
      obtain ⟨g, hg, rfl⟩ := hA
      rintro _ ⟨k, hk, rfl⟩
      have hmem' : K.map (MulAut.conj (m * g)).toMonoidHom ∈ conjSetOf M K := ⟨m * g, M.mul_mem hm hg, rfl⟩
      have hle : K.map (MulAut.conj (m * g)).toMonoidHom ≤ conjClosure M K :=
        le_iSup₂_of_le (f := fun A (_ : A ∈ conjSetOf M K) => A) _ hmem' le_rfl
      have hk' : m * (g * k * g⁻¹) * m⁻¹ ∈ K.map (MulAut.conj (m * g)).toMonoidHom :=
        ⟨k, hk, by simp [MulAut.conj_apply, mul_assoc]⟩
      exact hle hk'
    exact key hx
  · refine ⟨l.length, fun i => l[(i : ℕ)], fun i => uc22p22u_calC_mono hXsub (hSX _
      ((hmem _).1 (List.getElem_mem _))), ?_⟩
    rw [List.ofFn_getElem_eq_map l (fun A : Subgroup G => (A : Set G)),
      uc22p22u_prod_list_eq_iSup l fun A hA B hB => hpair A ((hmem A).1 hA) B ((hmem B).1 hB), hjoin]

theorem uc22p22u_exists_prod_conj {M X K : Subgroup G} (hXM : X ≤ M) (hN : M ≤ normalizer (X : Set G))
    (hK : K ∈ calC X) :
    ∃ L : Subgroup G, L ≤ X ∧ M ≤ normalizer (L : Set G) ∧ F08.IsProdOfCalC M L ∧
      ∀ m ∈ M, uniqueFourConj m K ≤ L := by
  obtain ⟨h1, h2, h3⟩ := uc22p22u_conjClosure_isProd hXM hN hK
  refine ⟨conjClosure M K, h1, h2, h3, fun m hm => ?_⟩
  exact le_iSup₂_of_le (f := fun A (_ : A ∈ conjSetOf M K) => A) (uniqueFourConj m K)
    ⟨m⁻¹, M.inv_mem hm, rfl⟩ le_rfl

theorem uc22p22u_exists_odd_prime_dvd_index_center {A : Type*} [Group A] [Finite A]
    (hq : CFSG.Open.IsQuasisimple A) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ (Subgroup.center A).index := by
  by_contra hcon
  push Not at hcon
  haveI : IsSimpleGroup (A ⧸ Subgroup.center A) := hq.2
  obtain ⟨a, b, hab⟩ :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian A hq
  have hcard : Nat.card (A ⧸ Subgroup.center A) =
      2 ^ (Nat.card (A ⧸ Subgroup.center A)).primeFactorsList.length := by
    refine Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {d} hd hdvd => ?_
    by_contra hd2
    exact hcon d hd hd2 (by rwa [Subgroup.index_eq_card])
  haveI : Group.IsNilpotent (A ⧸ Subgroup.center A) := (IsPGroup.of_card hcard).isNilpotent
  exact hab ((IsSimpleGroup.comm_iff_isSolvable.2 inferInstance) a b)

theorem uc22p22u_sylow_not_le_center {A : Type*} [Group A] [Finite A] {r : ℕ} [Fact r.Prime]
    (S : Sylow r A) (h : r ∣ (Subgroup.center A).index) :
    ¬ (S : Subgroup A) ≤ Subgroup.center A :=
  fun hle => S.not_dvd_index (h.trans (Subgroup.index_dvd_of_le hle))

theorem uc22p22u_index_center_eq {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (Subgroup.center A).index = (Subgroup.center B).index := by
  rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
  exact Nat.card_congr (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).toEquiv

theorem uc22p22u_noncyclic_of_commuting {Q : Type} [Group Q] [Finite Q] {A B : Subgroup Q}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {r : ℕ} [Fact r.Prime]
    (SA : Sylow r A) (SB : Sylow r B) (hA : ¬ (SA : Subgroup A) ≤ Subgroup.center A)
    (hB : ¬ (SB : Subgroup B) ≤ Subgroup.center B) :
    IsPGroup r ↥((SA : Subgroup A).map A.subtype ⊔ (SB : Subgroup B).map B.subtype) ∧
      ¬ IsCyclic ↥((SA : Subgroup A).map A.subtype ⊔ (SB : Subgroup B).map B.subtype) := by
  set R : Subgroup Q := (SA : Subgroup A).map A.subtype with hR
  set R' : Subgroup Q := (SB : Subgroup B).map B.subtype with hR'
  have hRp : IsPGroup r R := SA.isPGroup'.map A.subtype
  have hRp' : IsPGroup r R' := SB.isPGroup'.map B.subtype
  have hRA : R ≤ A := Subgroup.map_subtype_le _
  have hR'B : R' ≤ B := Subgroup.map_subtype_le _
  have hcommR : ∀ x ∈ R, ∀ y ∈ R', x * y = y * x := fun x hx y hy => hcomm x (hRA hx) y (hR'B hy)
  have hnorm : R ≤ normalizer (R' : Set Q) := by
    refine uc22p20e_le_normalizer_of_conj fun x hx y hy => ?_
    have h : x * y * x⁻¹ = y := by
      rw [hcommR x hx y hy]
      group
    rw [h]
    exact hy
  have hP : IsPGroup r ↥(R ⊔ R') := by
    intro z
    have hz : (z : Q) ∈ (R : Set Q) * (R' : Set Q) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right R R' hnorm]
      exact z.2
    obtain ⟨x, hx, y, hy, hxy⟩ := hz
    obtain ⟨i, hi⟩ := hRp ⟨x, hx⟩
    obtain ⟨j, hj⟩ := hRp' ⟨y, hy⟩
    have hxi : x ^ (r ^ i) = 1 := congrArg Subtype.val hi
    have hyj : y ^ (r ^ j) = 1 := congrArg Subtype.val hj
    refine ⟨i + j, Subtype.ext ?_⟩
    have hx' : x ^ (r ^ (i + j)) = 1 := by rw [pow_add, pow_mul, hxi, one_pow]
    have hy' : y ^ (r ^ (i + j)) = 1 := by rw [add_comm, pow_add, pow_mul, hyj, one_pow]
    show (z : Q) ^ (r ^ (i + j)) = 1
    rw [← hxy, (show Commute x y from hcommR x hx y hy).mul_pow, hx', hy', one_mul]
  refine ⟨hP, fun hcyc => ?_⟩
  have key : ∀ S T : Subgroup Q, S ≤ R ⊔ R' → T ≤ R ⊔ R' → Nat.card S ∣ Nat.card T → S ≤ T := by
    intro S T hS hT hdvd
    have h1 : (S.subgroupOf (R ⊔ R')) ≤ T.subgroupOf (R ⊔ R') :=
      (IsCyclic.subgroup_le_iff_card_dvd (G := ↥(R ⊔ R'))).2
        (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT).toEquiv])
    intro x hx
    exact h1 (show (⟨x, hS hx⟩ : ↥(R ⊔ R')) ∈ S.subgroupOf (R ⊔ R') from hx)
  obtain ⟨a, ha⟩ := hRp.exists_card_eq
  obtain ⟨b, hb⟩ := hRp'.exists_card_eq
  rcases le_total a b with hab | hba
  · have hle : R ≤ R' := key R R' le_sup_left le_sup_right (by rw [ha, hb]; exact pow_dvd_pow r hab)
    refine hA fun x hx => ?_
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hcomm y y.2 x (hR'B (hle ⟨x, hx, rfl⟩)))
  · have hle : R' ≤ R := key R' R le_sup_right le_sup_left (by rw [ha, hb]; exact pow_dvd_pow r hba)
    refine hB fun x hx => ?_
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hcomm x (hRA (hle ⟨x, hx, rfl⟩)) y y.2).symm

theorem uc22p22u_barImage_mono {X K L : Subgroup G} (h : K ≤ L) : barImage X K ≤ barImage X L := by
  intro q hq
  obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 hq
  exact uc22p21c_mem_barImage.2 ⟨m, h hm, rfl⟩

theorem uc22p22u_two_le_pRank_of_bar {X L : Subgroup G} (hLX : L ≤ X) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup (Bar2 X)} (hP : IsPGroup p P) (hnc : ¬ IsCyclic ↥P) (hPL : P ≤ barImage X L) :
    2 ≤ CFSG.Open.pRank p L := by
  haveI : (CFSG.pCore 2 ↥X).Normal := CFSG.pCore_normal
  have h2 := CFSG.LocalAnalysis.UniquenessCase.UC6.two_le_pRank_of_not_isCyclic hp hp2 hP hnc
  obtain ⟨E₀, hE₀P, hE₀, hcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp P
  obtain ⟨E, hEL, hE, hEcard⟩ := uc22p20d_lift_elemAbelian (CFSG.pCore 2 ↥X) CFSG.pCore_isPGroup hp hp2
    (L.subgroupOf X) E₀ hE₀ hcard (hE₀P.trans hPL)
  have hEmap : E.map X.subtype ≤ L :=
    (Subgroup.map_mono hEL).trans (Subgroup.map_subgroupOf_eq_of_le hLX).le
  have h3 := CFSG.LocalAnalysis.UniquenessCase.UC6.le_pRank_of_elemAbelian hp hEmap
    (uc22p20d_isElemAbelian_map X.subtype X.subtype_injective hE)
    (by rw [Subgroup.card_map_of_injective X.subtype_injective]; exact hEcard)
  omega

theorem uc22p22u_not_thin_of_conj {X K K' L : Subgroup G} (hK : K ∈ calC X) (hK' : K' ∈ calC X)
    (hne : K' ≠ K) (hconj : ∃ g : G, K' = uniqueFourConj g K) (hKL : K ≤ L) (hK'L : K' ≤ L) (hLX : L ≤ X) :
    ¬ F08.Thin8 L := by
  intro hthin
  obtain ⟨g, rfl⟩ := hconj
  have hcomm := uc22p22l_barImage_commute hK hK' hne.symm
  obtain ⟨eA, -⟩ := uc22p22l_barImage_equiv hK
  obtain ⟨eB, -⟩ := uc22p22l_barImage_equiv hK'
  obtain ⟨eC⟩ : Nonempty (Bar2 K ≃* Bar2 (uniqueFourConj g K)) := uc22p20d_bar2_conj g⁻¹ K
  have hqA : CFSG.Open.IsQuasisimple ↥(barImage X K) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv eA.symm hK.2.2
  obtain ⟨r, hr, hr2, hrA⟩ := uc22p22u_exists_odd_prime_dvd_index_center hqA
  haveI : Fact r.Prime := ⟨hr⟩
  have hrB : r ∣ (Subgroup.center ↥(barImage X (uniqueFourConj g K))).index := by
    rwa [← uc22p22u_index_center_eq (eA.symm.trans (eC.trans eB))]
  obtain ⟨SA⟩ := (inferInstance : Nonempty (Sylow r ↥(barImage X K)))
  obtain ⟨SB⟩ := (inferInstance : Nonempty (Sylow r ↥(barImage X (uniqueFourConj g K))))
  obtain ⟨hpg, hnc⟩ := uc22p22u_noncyclic_of_commuting hcomm SA SB
    (uc22p22u_sylow_not_le_center SA hrA) (uc22p22u_sylow_not_le_center SB hrB)
  have h2 := uc22p22u_two_le_pRank_of_bar hLX hr hr2 hpg hnc
    (sup_le ((Subgroup.map_subtype_le _).trans (uc22p22u_barImage_mono hKL))
      ((Subgroup.map_subtype_le _).trans (uc22p22u_barImage_mono hK'L)))
  have h1 := hthin r hr hr2
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
