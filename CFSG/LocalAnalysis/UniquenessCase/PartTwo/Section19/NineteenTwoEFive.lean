module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenOneFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwoE
public import CFSG.RankThree.PartTwo.Sec12.Hering129HBasic
import CFSG.GH74.Generic.S45.GL42
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem two_le_pRank_five_of_le_centralizer_barImage {D : Data G} {E : Subgroup G}
    (hEM : E ≤ D.M) (hE3 : IsPGroup 3 E) {Qb : Subgroup (Bar2 D.M)}
    (hQbel : IsElemAbelian 5 Qb) (hQbcard : Nat.card Qb = 25)
    (hQb_le : Qb ≤ Subgroup.centralizer (barImage D.M E : Set (Bar2 D.M))) :
    2 ≤ CFSG.Open.pRank 5 (D.M ⊓ Subgroup.centralizer (E : Set G)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let π : ↥D.M →* Bar2 D.M := QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)
  have hQb5 : IsPGroup 5 Qb := hQbel.isPGroup
  have hN3 : ¬ 3 ∣ Nat.card ↥(CFSG.pCore 2 ↥D.M) := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥D.M)).exists_card_eq
    rw [hk]
    exact fun hd => absurd (Nat.prime_three.dvd_of_dvd_pow hd) (by norm_num)
  have hE3sub : IsPGroup 3 (E.subgroupOf D.M) := by
    rw [← Subgroup.comap_subtype E D.M]
    exact hE3.comap_subtype
  have hmapC := CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime 3
    (CFSG.pCore 2 ↥D.M) hN3 (E.subgroupOf D.M) hE3sub
  let CM : Subgroup ↥D.M := Subgroup.centralizer (E.subgroupOf D.M : Set ↥D.M)
  let Cbar : Subgroup (Bar2 D.M) := Subgroup.centralizer (barImage D.M E : Set (Bar2 D.M))
  have hCMmap : CM.map π = Cbar := by
    simpa [CM, Cbar, barImage] using hmapC
  let f : ↥CM →* ↥Cbar :=
    { toFun := fun x => ⟨π x.1, by
        have hx : π x.1 ∈ CM.map π := Subgroup.mem_map.mpr ⟨x.1, x.2, rfl⟩
        rwa [hCMmap] at hx⟩
      map_one' := by ext; simp [CM]
      map_mul' := by intro a b; ext; simp }
  have hf_surj : Function.Surjective f := by
    intro y
    have hy : (y : Bar2 D.M) ∈ CM.map π := by rw [hCMmap]; exact y.2
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hf_ker : IsPGroup 2 ↥f.ker := by
    have hkerp : IsPGroup 2 ↥π.ker := by
      rw [show π.ker = CFSG.pCore 2 ↥D.M from QuotientGroup.ker_mk' _]
      exact CFSG.pCore_isPGroup
    let h : ↥f.ker →* ↥D.M := CM.subtype.comp f.ker.subtype
    have hh : ∀ x, h x ∈ π.ker := by
      intro x
      have hx : f x.1 = 1 := x.2
      have hx1 : π x.1.1 = 1 := congrArg Subtype.val hx
      exact hx1
    let g : ↥f.ker →* ↥π.ker := h.codRestrict π.ker hh
    refine hkerp.of_injective g ?_
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥π.ker => (z : ↥D.M)) hab
  have hQbC_le : Qb ≤ Cbar := hQb_le
  have hQbC5 : IsPGroup 5 (Qb.subgroupOf Cbar) := by
    rw [← Subgroup.comap_subtype Qb Cbar]
    exact hQb5.comap_subtype
  have hQbCel : IsElemAbelian 5 (Qb.subgroupOf Cbar) := by
    rw [← Subgroup.comap_subtype Qb Cbar]
    exact hQbel.comap Cbar.subtype_injective
  obtain ⟨Q, hQ5, hQmap, hQdisj⟩ := CFSG.LocalAnalysis.UniquenessCase.UC6S846.exists_lift_pGroup
    f hf_surj hf_ker (by norm_num : Nat.Prime 5) (by norm_num) (Qb.subgroupOf Cbar) hQbC5
  have hQel : IsElemAbelian 5 Q :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.isElemAbelian_of_disjoint_ker f Q hQdisj (by
      rw [hQmap]; exact hQbCel)
  let gGD : ↥CM →* G := D.M.subtype.comp CM.subtype
  have hgGDinj : Function.Injective gGD := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hQcard : Nat.card ↥(Q.map gGD) = 5 ^ 2 := by
    rw [Subgroup.card_map_of_injective hgGDinj]
    have h1 : Nat.card ↥Q = Nat.card ↥(Q.map f) :=
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.card_map_of_disjoint_ker f Q hQdisj).symm
    rw [h1, hQmap,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQbC_le).toEquiv, hQbcard]
    norm_num
  have hQleM : Q.map gGD ≤ D.M ⊓ Subgroup.centralizer (E : Set G) := by
    refine le_inf ?_ ?_
    · intro x hx
      obtain ⟨q, -, rfl⟩ := Subgroup.mem_map.mp hx
      exact q.1.2
    · intro x hx
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have hqcent : q.1 ∈ Subgroup.centralizer (E.subgroupOf D.M : Set ↥D.M) := q.2
      let eM : ↥D.M := ⟨e, hEM he⟩
      have hesub : eM ∈ E.subgroupOf D.M := by
        simpa [eM, Subgroup.mem_subgroupOf] using he
      have hcomm := (Subgroup.mem_centralizer_iff.mp hqcent) eM hesub
      simpa [eM, gGD] using congrArg Subtype.val hcomm
  exact CFSG.SectionRank.le_pRank (by norm_num) hQleM (hQel.map gGD) hQcard

theorem two_le_pRank_five_of_centralizes_L (D : Data G)
    {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K)
    (h68 : S17.R17_68At D V₀ V) {E : Subgroup G} (hEM : E ≤ D.M) (hE3 : IsPGroup 3 E)
    (hEL : barImage D.M L ≤ Subgroup.centralizer (barImage D.M E : Set (Bar2 D.M))) :
    2 ≤ CFSG.Open.pRank 5 (D.M ⊓ Subgroup.centralizer (E : Set G)) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hLC : L ∈ calC D.M := h.hyp.hL.1
  obtain ⟨eL, -⟩ := uc22p22l_barImage_equiv hLC
  set Lb : Subgroup (Bar2 D.M) := barImage D.M L with hLb
  rcases h.shape with hL2 | hU3
  · have hA : IsAlt (Bar2 L) 5 := S17.isAlt_five_of_isL2_two hL2
    obtain ⟨eA⟩ := hA
    have hLb60 : Nat.card Lb = 60 := by
      rw [← Nat.card_congr eL.toEquiv]; exact card_bar2_of_isAlt_five ⟨eA⟩
    obtain ⟨l, hl⟩ := exists_prime_orderOf_dvd_card' (G := ↥Lb) 5 (by rw [hLb60]; norm_num)
    have hl5 : orderOf (l : Bar2 D.M) = 5 := by rw [Subgroup.orderOf_coe, hl]
    obtain ⟨f, hf5, hfn⟩ := exists_normal_zpowers_five_bar2 D h h68 hL2
    have hperfsub : ⁅L.subgroupOf D.M, L.subgroupOf D.M⁆ = L.subgroupOf D.M := by
      apply Subgroup.map_injective D.M.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_of_le_left hLC.1.le]
      exact hLC.2.1
    have hperfLb : ⁅Lb, Lb⁆ = Lb := by
      show ⁅(L.subgroupOf D.M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)),
        (L.subgroupOf D.M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M))⁆ =
          (L.subgroupOf D.M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M))
      rw [← Subgroup.map_commutator, hperfsub]
    have hN : ∀ m : Bar2 D.M,
        m ∈ Subgroup.normalizer (Subgroup.zpowers f : Set (Bar2 D.M)) := by
      intro m
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        rw [← conj_zpow]
        exact Subgroup.zpow_mem _ (hfn m) i
      · intro hy
        have hm' : m⁻¹ * (m * y * m⁻¹) * m⁻¹⁻¹ ∈ Subgroup.zpowers f := by
          obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hy
          rw [← hi, ← conj_zpow]
          exact Subgroup.zpow_mem _ (hfn m⁻¹) i
        simpa [mul_assoc] using hm'
    have hLbN : Lb ≤ Subgroup.normalizer (Subgroup.zpowers f : Set (Bar2 D.M)) :=
      fun m _ => hN m
    have hLbC : Lb ≤ Subgroup.centralizer ({f} : Set (Bar2 D.M)) :=
      CFSG.RankThree.PartTwo.Sec12.le_centralizer_of_isPerfect_of_le_normalizer_zpowers
        (Subgroup.isPerfect_iff.mpr hperfLb) hLbN
    have hE3b : IsPGroup 3 (barImage D.M E) := by
      have hE3sub : IsPGroup 3 (E.subgroupOf D.M) := by
        rw [← Subgroup.comap_subtype E D.M]
        exact hE3.comap_subtype
      exact hE3sub.map _
    have hEf : f ∈ Subgroup.centralizer (barImage D.M E : Set (Bar2 D.M)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      obtain ⟨n, hn⟩ := hE3b ⟨e, he⟩
      have he3 : e ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
      exact CFSG.GH74.Generic.S45.commute_of_normalizer_five (by rw [Nat.card_zpowers, hf5])
        (hN e) (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one he3)
          (Nat.Coprime.pow_left n (by norm_num))) (Subgroup.mem_zpowers f)
    have hfL : f ∉ Lb := by
      intro hfL
      let φ : ↥Lb ≃* alternatingGroup (Fin 5) := eL.symm.trans eA
      have hc : φ ⟨f, hfL⟩ ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
        rw [Subgroup.mem_center_iff]
        intro g
        obtain ⟨y, rfl⟩ := φ.surjective g
        rw [← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        exact Subgroup.mem_centralizer_singleton_iff.mp (hLbC y.2)
      rw [alternatingGroup.center_eq_bot (by norm_num), Subgroup.mem_bot] at hc
      have hf1 : (⟨f, hfL⟩ : ↥Lb) = 1 := φ.injective (by rw [hc, map_one])
      have : f = 1 := congrArg Subtype.val hf1
      rw [this, orderOf_one] at hf5
      norm_num at hf5
    have hlf : (l : Bar2 D.M) * f = f * l := Subgroup.mem_centralizer_singleton_iff.mp (hLbC l.2)
    let Qb : Subgroup (Bar2 D.M) := Subgroup.zpowers (l : Bar2 D.M) ⊔ Subgroup.zpowers f
    have hcommQ : ∀ a ∈ Subgroup.zpowers (l : Bar2 D.M), ∀ b ∈ Subgroup.zpowers f,
        a * b = b * a := by
      intro a ha b hb
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact ((show Commute (l : Bar2 D.M) f from hlf).zpow_left m).zpow_right n
    have hQbel : IsElemAbelian 5 Qb :=
      IsElemAbelian.sup_of_commute
        (CFSG.Open.isElemAbelian_zpowers (by simpa [hl5] using pow_orderOf_eq_one (l : Bar2 D.M)))
        (CFSG.Open.isElemAbelian_zpowers (by simpa [hf5] using pow_orderOf_eq_one f)) hcommQ
    have hdisjQ : Disjoint (Subgroup.zpowers (l : Bar2 D.M)) (Subgroup.zpowers f) := by
      rw [Subgroup.disjoint_def]
      intro x hxl hxf
      by_contra hx1
      have hxLb : x ∈ Lb := Subgroup.zpowers_le.mpr l.2 hxl
      have hxo : orderOf x = 5 := by
        have hd : orderOf x ∣ 5 := hf5 ▸ orderOf_dvd_of_mem_zpowers hxf
        rcases (Nat.dvd_prime Nat.prime_five).1 hd with h1 | h1
        · exact absurd (orderOf_eq_one_iff.mp h1) hx1
        · exact h1
      have heq : Subgroup.zpowers x = Subgroup.zpowers f :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxf)
          (by rw [Nat.card_zpowers, Nat.card_zpowers, hxo, hf5])
      have hfx : f ∈ Subgroup.zpowers x := heq ▸ Subgroup.mem_zpowers f
      exact hfL (Subgroup.zpowers_le.mpr hxLb hfx)
    have hnormQ : Subgroup.zpowers f ≤
        Subgroup.normalizer (Subgroup.zpowers (l : Bar2 D.M) : Set (Bar2 D.M)) := by
      refine (show Subgroup.zpowers f ≤
          Subgroup.centralizer (Subgroup.zpowers (l : Bar2 D.M) : Set (Bar2 D.M)) from ?_).trans
        (Subgroup.centralizer_le_normalizer _)
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hcommQ a ha b hb
    have hQbcard : Nat.card Qb = 25 := by
      show Nat.card ↥(Subgroup.zpowers (l : Bar2 D.M) ⊔ Subgroup.zpowers f) = 25
      rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnormQ hdisjQ,
        Nat.card_zpowers, Nat.card_zpowers, hl5, hf5]
    refine two_le_pRank_five_of_le_centralizer_barImage hEM hE3 hQbel hQbcard ?_
    exact sup_le (Subgroup.zpowers_le.mpr (hEL l.2)) (Subgroup.zpowers_le.mpr hEf)
  · have hU3b : IsU3 ↥Lb 2 := CFSG.Blueprint.LieModel.of_mulEquiv eL hU3
    have h5 := Inputs1719.kU34Data_fiveRank ↥Lb hU3b
    have h5' : CFSG.Open.pRank 5 (⊤ : Subgroup ↥Lb) = 2 :=
      ((CFSG.SectionRank.pRank_eq_open_pRank_top 5 ↥(⊤ : Subgroup ↥Lb)).trans
        (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 5)
          (⊤ : Subgroup ↥Lb)).symm).symm.trans h5
    obtain ⟨Q, -, hQel, hQcard⟩ :=
      CFSG.SectionRank.exists_pRank (p := 5) (by norm_num) (⊤ : Subgroup ↥Lb)
    refine two_le_pRank_five_of_le_centralizer_barImage hEM hE3 (Qb := Q.map Lb.subtype)
      (hQel.map _) ?_ ?_
    · rw [Subgroup.card_map_of_injective Lb.subtype_injective, hQcard, h5']
      norm_num
    · rintro _ ⟨q, -, rfl⟩
      exact hEL q.2

theorem barImage_le_centralizer_of_ctx19_1 (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) {z a : G}
    (hz : z ∈ F08.CentOverO2 D.M (S17.Lp D 5)) (haK : a ∈ K) :
    barImage D.M L ≤ Subgroup.centralizer
      (barImage D.M (Subgroup.zpowers z ⊔ Subgroup.zpowers a) : Set (Bar2 D.M)) := by
  classical
  obtain ⟨hzM, hzc⟩ := mem_centOverO2_iff.mp hz
  have hLC : L ∈ calC D.M := h.hyp.hL.1
  have haM : a ∈ D.M := h.hK.1.le haK
  have hO2 : pCoreOf 2 (S17.Lp D 5) ≤ pCoreOf 2 D.M :=
    uc22p21c_pCoreOf_le_of_subnormal (CFSG.Open.IsSubnormal.step (S17.Lp_le_M D 5)
      (s13_Lp_normal D.M 5) (CFSG.Open.IsSubnormal.refl D.M))
  rw [Subgroup.le_centralizer_iff]
  rw [s13_barImage_sup (Subgroup.zpowers_le.mpr hzM) (Subgroup.zpowers_le.mpr haM)]
  refine sup_le ?_ ?_
  · intro e he
    obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 he
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hm
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, hn, rfl⟩ := uc22p21c_mem_barImage.1 hy
    have hnLp : (n : G) ∈ S17.Lp D 5 := by rw [h.hLK]; exact Subgroup.mem_sup_left hn
    have hc : (z : G) * n * z⁻¹ * (n : G)⁻¹ ∈ pCoreOf 2 D.M := hO2 (hzc _ hnLp)
    have hmz : m = (⟨z, hzM⟩ : ↥D.M) ^ i := Subtype.ext (by rw [← hi]; simp)
    have hc' : (⟨z, hzM⟩ : ↥D.M) * n * (⟨z, hzM⟩ : ↥D.M)⁻¹ * n⁻¹ ∈ CFSG.pCore 2 ↥D.M :=
      (CFSG.mem_openPCoreOf_iff _).1 hc
    have h1 : uc22p21cPi D.M ⟨z, hzM⟩ * uc22p21cPi D.M n * (uc22p21cPi D.M ⟨z, hzM⟩)⁻¹ *
        (uc22p21cPi D.M n)⁻¹ = 1 := by
      have h0 : uc22p21cPi D.M ((⟨z, hzM⟩ : ↥D.M) * n * (⟨z, hzM⟩ : ↥D.M)⁻¹ * n⁻¹) = 1 :=
        (QuotientGroup.eq_one_iff _).2 hc'
      simpa only [map_mul, map_inv] using h0
    have h2 : uc22p21cPi D.M ⟨z, hzM⟩ * uc22p21cPi D.M n * (uc22p21cPi D.M ⟨z, hzM⟩)⁻¹ =
        uc22p21cPi D.M n := mul_inv_eq_one.mp h1
    have hcomm : uc22p21cPi D.M ⟨z, hzM⟩ * uc22p21cPi D.M n =
        uc22p21cPi D.M n * uc22p21cPi D.M ⟨z, hzM⟩ := by
      calc uc22p21cPi D.M ⟨z, hzM⟩ * uc22p21cPi D.M n
          = (uc22p21cPi D.M ⟨z, hzM⟩ * uc22p21cPi D.M n * (uc22p21cPi D.M ⟨z, hzM⟩)⁻¹) *
              uc22p21cPi D.M ⟨z, hzM⟩ := by group
        _ = uc22p21cPi D.M n * uc22p21cPi D.M ⟨z, hzM⟩ := by rw [h2]
    rw [hmz, map_zpow]
    exact ((Commute.zpow_left (show Commute _ _ from hcomm) i)).eq.symm
  · intro e he
    have heK : e ∈ barImage D.M K := barImage_mono (Subgroup.zpowers_le.mpr haK) he
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (uc22p22l_barImage_commute hLC h.hK h.hne.symm y hy e heK)

theorem exists_E9_of_ctx19_1 (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (hSg : UC6S846.SigmaStd D) (hk : D.k = 2)
    (h642 : S17.P17_64_2 D 5 2) (hK : Inputs1719.K_A5U34BorelQuotient) {S : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf 3 S D.M) (hSnot : ¬ S ≤ L ⊔ K) :
    ∃ z a : G, z ∈ S ⊓ F08.CentOverO2 D.M (S17.Lp D 5) ∧ orderOf z = 3 ∧
      a ∈ S ⊓ K ∧ orderOf a = 3 ∧
      CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers z ⊔ Subgroup.zpowers a) ∧
      Nat.card ↥(Subgroup.zpowers z ⊔ Subgroup.zpowers a) = 3 ^ 2 ∧
      Subgroup.zpowers z ⊔ Subgroup.zpowers a ≤ S ⊓ Subgroup.centralizer (S : Set G) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Y : Subgroup G := S17.Lp D 5
  let C : Subgroup G := F08.CentOverO2 D.M Y
  let A : Subgroup G := S ⊓ Y
  set R : Subgroup G := S ⊓ C with hR
  have hSnotY : ¬ S ≤ Y := by
    rw [show Y = L ⊔ K from h.hLK]
    exact hSnot
  have hYM : Y ≤ D.M := S17.Lp_le_M D 5
  have hMN : D.M ≤ Subgroup.normalizer (Y : Set G) := by
    rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hYM]
    exact s13_Lp_normal D.M 5
  have hjoin : A ⊔ R = S := (sylow_three_eq_sup_inf_centOverO2 h642 hK hS).symm
  have hcommAR : ⁅A, R⁆ = ⊥ := by
    simpa [A, R] using commutator_sylow_inf_centOverO2 (D := D) (S := S) h642 hS
  have hdisjAR : A ⊓ R = ⊥ := by
    have hCeq : C = S17.centSection D.M Y (CFSG.Open.pCoreOf 2 Y) :=
      S17.centOverO2_eq_centSection
    have hcop : Nat.Coprime 3 (Nat.card (Y ⊓ C : Subgroup G)) := by
      have h2 : IsPGroup 2 ↥(Y ⊓ C) := by
        rw [hCeq]
        have hle : (Y ⊓ S17.centSection D.M Y (CFSG.Open.pCoreOf 2 Y)) ≤
            CFSG.Open.pCoreOf 2 Y := by
          rw [inf_comm]
          exact S17.inf_centSection_Lp_le_pCore h642
        exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y).to_le hle
      exact (Nat.prime_three.coprime_iff_not_dvd).mpr
        (by
          have h3 : ¬ 3 ∣ Nat.card ↥(Y ⊓ C) := fun hd =>
            CFSG.GroupTheory.not_dvd_card_of_isPGroup h2 Nat.prime_three (by norm_num) hd
          simpa using h3)
    have hScop : Nat.Coprime (Nat.card S) (Nat.card (Y ⊓ C : Subgroup G)) := by
      obtain ⟨n, hn⟩ := hS.isPGroup.exists_card_eq
      rw [hn]
      exact hcop.pow_left n
    have hSinf : S ⊓ (Y ⊓ C) = ⊥ := Subgroup.inf_eq_bot_of_coprime hScop
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ S ⊓ (Y ⊓ C) := ⟨hx.1.1, hx.1.2, hx.2.2⟩
    rw [hSinf] at hx'
    exact hx'
  have hRne : R ≠ ⊥ := by
    intro hRbot
    have hjoinA : A = S := by
      rw [← hjoin, hRbot, sup_bot_eq]
    apply hSnotY
    rw [← hjoinA]
    exact inf_le_right
  have hR3 : IsPGroup 3 ↥R := hS.isPGroup.to_le inf_le_left
  have hRcyc : IsCyclic ↥R := by
    simpa [R] using isCyclic_inf_centOverO2 h hSg hk h642 hK hS
  obtain ⟨z, hzR, hzord⟩ := CFSG.Quasithin.exists_orderOf_eq_of_isPGroup_ne_bot hR3 hRne
  have hRcentA : R ≤ Subgroup.centralizer (A : Set G) := by
    have hcommRA : ⁅R, A⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hcommAR
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommRA
  have hzRcent : ∀ r ∈ R, z * r = r * z := by
    intro r hr
    letI : CommGroup ↥R := hRcyc.commGroup
    have hz' : (⟨z, hzR⟩ : ↥R) * (⟨r, hr⟩ : ↥R) = (⟨r, hr⟩ : ↥R) * ⟨z, hzR⟩ :=
      mul_comm _ _
    exact congrArg Subtype.val hz'
  have hzA : ∀ y ∈ A, z * y = y * z := by
    intro y hy
    exact ((Subgroup.mem_centralizer_iff.mp (hRcentA hzR)) y hy).symm
  have hdecomp : ∀ {s : G}, s ∈ S → ∃ aa ∈ A, ∃ rr ∈ R, aa * rr = s := by
    intro s hs
    have hs' : s ∈ A ⊔ R := by rw [hjoin]; exact hs
    exact CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
      (fun x hx y hy => (commutatorElement_eq_one_iff_commute.mp
        (Subgroup.mem_bot.mp (by
          have hm : ⁅x, y⁆ ∈ ⁅A, R⁆ := Subgroup.commutator_mem_commutator hx hy
          rwa [hcommAR] at hm))).eq) hs'
  have hzS : z ∈ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    obtain ⟨aa, haa, rr, hrr, rfl⟩ := hdecomp hs
    calc (aa * rr) * z = aa * (rr * z) := by group
      _ = aa * (z * rr) := by rw [hzRcent rr hrr]
      _ = (aa * z) * rr := by group
      _ = (z * aa) * rr := by rw [hzA aa haa]
      _ = z * (aa * rr) := by group
  have hKY : K ≤ Y := by rw [show Y = L ⊔ K from h.hLK]; exact le_sup_right
  have hYK : Y ≤ Subgroup.normalizer (K : Set G) := by
    rw [show Y = L ⊔ K from h.hLK]
    exact sup_le (calC_le_normalizer_of_ne h.hK h.hyp.hL.1 h.hne) Subgroup.le_normalizer
  have hAsyl : CFSG.ABGLocalTools.IsSylowOf 3 A Y :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hS hYM hMN
  have hSKsyl : CFSG.ABGLocalTools.IsSylowOf 3 (A ⊓ K) K :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hAsyl hKY hYK
  have hAK : A ⊓ K = S ⊓ K := by
    show S ⊓ Y ⊓ K = S ⊓ K
    rw [inf_assoc, inf_of_le_right hKY]
  rw [hAK] at hSKsyl
  have hSKne : S ⊓ K ≠ ⊥ := by
    intro hbot
    obtain ⟨-, -, hndvd⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hSKsyl
    rw [hbot, Subgroup.relIndex_bot_left] at hndvd
    apply hndvd
    have h60 : Nat.card (Bar2 K) = 60 := card_bar2_of_isAlt_five h.hKshape
    have hdvd : Nat.card (Bar2 K) ∣ Nat.card K := Subgroup.card_quotient_dvd_card _
    rw [h60] at hdvd
    exact (show (3 : ℕ) ∣ 60 by norm_num).trans hdvd
  have hSK3 : IsPGroup 3 ↥(S ⊓ K) := hS.isPGroup.to_le inf_le_left
  have hSKA : S ⊓ K ≤ A := hAK ▸ inf_le_left
  have hA3 : IsPGroup 3 ↥A := hS.isPGroup.to_le inf_le_left
  have hAnorm : A ≤ Subgroup.normalizer ((S ⊓ K : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hxS : x ∈ S := hx.1
    have hxK : x ∈ Subgroup.normalizer (K : Set G) := hYK hx.2
    constructor
    · intro hy
      exact ⟨S.mul_mem (S.mul_mem hxS hy.1) (S.inv_mem hxS),
        (Subgroup.mem_normalizer_iff.mp hxK y).mp hy.2⟩
    · intro hy
      have hyS : y ∈ S := by
        have h1 := S.mul_mem (S.mul_mem (S.inv_mem hxS) hy.1) hxS
        simpa [mul_assoc] using h1
      exact ⟨hyS, (Subgroup.mem_normalizer_iff.mp hxK y).mpr hy.2⟩
  have hCne : (S ⊓ K) ⊓ Subgroup.centralizer (A : Set G) ≠ ⊥ :=
    CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.inf_centralizer_ne_bot Nat.prime_three
      hA3 hSK3 hSKne hAnorm
  obtain ⟨a, haC, haord⟩ := CFSG.Quasithin.exists_orderOf_eq_of_isPGroup_ne_bot
    (hSK3.to_le inf_le_left) hCne
  have haSK : a ∈ S ⊓ K := haC.1
  have haA : a ∈ A := hSKA haSK
  have hacentA : a ∈ Subgroup.centralizer (A : Set G) := haC.2
  have haS : a ∈ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    obtain ⟨aa, haa, rr, hrr, rfl⟩ := hdecomp hs
    have h1 : aa * a = a * aa := (Subgroup.mem_centralizer_iff.mp hacentA) aa haa
    have h2 : rr * a = a * rr := (Subgroup.mem_centralizer_iff.mp (hRcentA hrr)) a haA |>.symm
    calc (aa * rr) * a = aa * (rr * a) := by group
      _ = aa * (a * rr) := by rw [h2]
      _ = (aa * a) * rr := by group
      _ = (a * aa) * rr := by rw [h1]
      _ = a * (aa * rr) := by group
  have hzpow : z ^ 3 = 1 := by rw [← hzord]; exact pow_orderOf_eq_one z
  have hapow : a ^ 3 = 1 := by rw [← haord]; exact pow_orderOf_eq_one a
  have hza : z * a = a * z := by
    have h := (Subgroup.mem_centralizer_iff.mp hzS) a haSK.1
    exact h.symm
  have hEel : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers z ⊔ Subgroup.zpowers a) := by
    refine CFSG.Open.IsElemAbelian.sup_of_commute
      (CFSG.Open.isElemAbelian_zpowers hzpow)
      (CFSG.Open.isElemAbelian_zpowers hapow) ?_
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow (show Commute z a from hza) i j).eq
  have hdisjE : Subgroup.zpowers z ⊓ Subgroup.zpowers a = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxR : x ∈ R := (Subgroup.zpowers_le.mpr hzR) hx.1
    have hxA : x ∈ A := (Subgroup.zpowers_le.mpr haA) hx.2
    have : x ∈ A ⊓ R := ⟨hxA, hxR⟩
    rw [hdisjAR] at this
    exact this
  have hcardE : Nat.card ↥(Subgroup.zpowers z ⊔ Subgroup.zpowers a) = 3 ^ 2 := by
    have hzcard : Nat.card (Subgroup.zpowers z) = 3 := by
      rw [Nat.card_zpowers, hzord]
    have hacard : Nat.card (Subgroup.zpowers a) = 3 := by
      rw [Nat.card_zpowers, haord]
    have hnorm : Subgroup.zpowers z ≤
        Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
      have hle : Subgroup.zpowers z ≤
          Subgroup.centralizer (Subgroup.zpowers a : Set G) := by
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact (Commute.zpow_zpow (show Commute z a from hza) i j).eq.symm
      exact hle.trans (Subgroup.centralizer_le_normalizer (Subgroup.zpowers a : Set G))
    have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (Subgroup.zpowers a) (Subgroup.zpowers z) hnorm
      (disjoint_iff.mpr (by rw [inf_comm]; exact hdisjE))
    rw [hzcard, hacard] at h
    rw [show Subgroup.zpowers z ⊔ Subgroup.zpowers a = Subgroup.zpowers a ⊔ Subgroup.zpowers z by
      simp only [sup_comm]]
    simpa [pow_two] using h
  have hRS : R ≤ S := inf_le_left
  refine ⟨z, a, hzR, hzord, haSK, haord, hEel, hcardE, le_inf ?_ ?_⟩
  · exact sup_le ((Subgroup.zpowers_le.mpr hzR).trans hRS)
      (Subgroup.zpowers_le.mpr haSK.1)
  · exact sup_le (Subgroup.zpowers_le.mpr hzS) (Subgroup.zpowers_le.mpr haS)

theorem gap19_2_E_of_ctx (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) (hSg : UC6S846.SigmaStd D) (hk : D.k = 2)
    (h642 : S17.P17_64_2 D 5 2) (hK : Inputs1719.K_A5U34BorelQuotient)
    (h68 : S17.R17_68At D V₀ V) : Gap19_2_E D L K := by
  intro S hS hSnot
  obtain ⟨z, a, hz, hz3, ha, ha3, hel, hcard, hle⟩ :=
    exists_E9_of_ctx19_1 D h hSg hk h642 hK hS hSnot
  refine ⟨_, hel, hcard, hle, two_le_pRank_five_of_centralizes_L D h h68
    (hle.trans (inf_le_left.trans hS.le)) hel.isPGroup
    (barImage_le_centralizer_of_ctx19_1 D h hz.2 ha.2)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
