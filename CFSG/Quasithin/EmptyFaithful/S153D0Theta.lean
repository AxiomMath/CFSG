module

public import CFSG.Quasithin.EmptyFaithful.S153YCases
public import CFSG.Quasithin.EmptyFaithful.S153DGen
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

namespace S153D

section Theta

variable {G : Type} [Group G]

theorem thetaOf_le {A : Subgroup G} : thetaOf A ≤ A :=
  (Subgroup.closure_le A).mpr fun _ hx => hx.1

theorem thetaOf_mono {A B : Subgroup G} (h : A ≤ B) : thetaOf A ≤ thetaOf B :=
  Subgroup.closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

theorem conj_mem_thetaOf {A : Subgroup G} {g x : G} (hg : g ∈ Subgroup.normalizer (A : Set G))
    (hx : x ∈ thetaOf A) : g * x * g⁻¹ ∈ thetaOf A := by
  have : thetaOf A ≤ (thetaOf A).comap (MulAut.conj g).toMonoidHom := by
    refine (Subgroup.closure_le _).mpr fun y hy => ?_
    show g * y * g⁻¹ ∈ thetaOf A
    refine Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.mp hg y).mp hy.1, ?_⟩
    rw [← hy.2]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y
  exact this hx

theorem normalizer_le_normalizer_thetaOf (A : Subgroup G) :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer ((thetaOf A : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_thetaOf hg hx, fun hx => ?_⟩
  have h2 := conj_mem_thetaOf (Subgroup.inv_mem _ hg) hx
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at h2

theorem oTwoUpper_le_thetaOf {A : Subgroup G} (h : ∀ x ∈ A, Odd (orderOf x) → x ^ 3 = 1) :
    oTwoUpper A ≤ thetaOf A := by
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  have h3 : x ^ 3 = 1 := h x hx.1 hx.2
  by_cases h1 : x = 1
  · rw [h1]
    exact Subgroup.one_mem _
  · exact Subgroup.subset_closure ⟨hx.1, orderOf_eq_prime h3 h1⟩

end Theta

section YPart

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

theorem Y153_pow_three_of_odd (h113 : StageLemma14113) (h : Hyp153 G T Mc M) {y : G}
    (hy : y ∈ Y153 Mc M) (hodd : Odd (orderOf y)) : y ^ 3 = 1 := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨-, -, hexp⟩, -⟩ := Hyp153.Ystar_structure h113 h
  have hyM : y ∈ M := Y153_le Mc M hy
  have hu : (QuotientGroup.mk ⟨y, hyM⟩ : OTwoQuot M) ∈ imageOTwoQuot M (Y153 Mc M) :=
    mem_imageOTwoQuot_iff.mpr ⟨y, hyM, hy, rfl⟩
  have h3 := hexp ⟨_, hu⟩
  have h3' : (QuotientGroup.mk ⟨y, hyM⟩ : OTwoQuot M) ^ 3 = 1 := by
    simpa using congrArg Subtype.val h3
  have h4 : y ^ 3 ∈ pCoreOf 2 M := by
    have : (QuotientGroup.mk ((⟨y, hyM⟩ : ↥M) ^ 3) : OTwoQuot M) = 1 := by
      rw [QuotientGroup.mk_pow]
      exact h3'
    exact (mk_eq_one_iff_mem_pCoreOf _).mp this
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 M ⟨y ^ 3, h4⟩
  have hk' : (y ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hdvd : orderOf y ∣ 3 * 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_mul]; exact hk')
  have hcop : Nat.Coprime (orderOf y) (2 ^ k) := (Nat.coprime_two_right.mpr hodd).pow_right k
  exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_right hdvd)

theorem pRank_OTwoQuot_le (h : Hyp153 G T Mc M) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (OTwoQuot M)) ≤ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N : Subgroup ↥M := CFSG.Open.pCore 2 ↥M with hN
  have hnd : ¬ 3 ∣ Nat.card N := by
    intro hd
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥M) 2).exists_card_eq
    rw [hk] at hd
    exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow hd)) (by norm_num)
  have h1 := CFSG.SectionRank.pRank_quotient_eq (p := 3) N hnd
  have h2 := pRank_top_subtype (p := 3) M
  have h3 := pRank_le_two_of_isTwoLocal h.qtfe.qtke h.inM.1.1 Nat.prime_three (by norm_num)
  calc CFSG.Open.pRank 3 (⊤ : Subgroup (OTwoQuot M)) = CFSG.Open.pRank 3 (⊤ : Subgroup ↥M) := h1
    _ = CFSG.Open.pRank 3 M := h2
    _ ≤ 2 := h3

theorem two_le_pRank_Ystar (h113 : StageLemma14113) (h : Hyp153 G T Mc M) :
    2 ≤ CFSG.Open.pRank 3 (imageOTwoQuot M (Y153 Mc M)) := by
  obtain ⟨q, L₁, L₂, t, -, -, -, -, hS, -⟩ := h.exists_ofourStruct
  have hMV : M ≤ Subgroup.normalizer (VZ T M : Set G) := h.le_normalizer
  have hOC : pCoreOf 2 M ≤ Subgroup.centralizer (VZ T M : Set G) :=
    h.hyp14117.pCoreOf_le_centralizer
  have hYM : Y153 Mc M ≤ M := Y153_le Mc M
  obtain ⟨⟨hcl, hΩ, hexp⟩, hZc⟩ := Hyp153.Ystar_structure h113 h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Ys := imageOTwoQuot M (Y153 Mc M) with hYs
  let f : ↥Ys →* MulAut ↥(VZ T M) := (starAct M (VZ T M) hMV hOC).comp Ys.subtype
  have hrange : f.range = oTwoUpper (autOn M (VZ T M)) := by
    show ((starAct M (VZ T M) hMV hOC).comp Ys.subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype, map_starAct hMV hOC hYM]
    exact h.autOn_Y153 h113
  have hcardP : Nat.card f.range = 9 := by
    rw [hrange]
    exact hS.card_oTwoUpper h.isSylowTwoOf_autI
  have h9dvd : 9 ∣ Nat.card ↥Ys := hcardP ▸ Subgroup.card_range_dvd f
  have hexpPG : IsPGroup 3 ↥Ys := fun x => ⟨1, by simpa using hexp x⟩
  have hrank2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥Ys) := by
    by_contra hne
    have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥Ys) ≤ 1 := by omega
    have hbot : (⊤ : Subgroup ↥Ys) ≠ ⊥ := by
      intro hb
      have hc : Nat.card ↥Ys = 1 := by rw [← Subgroup.card_top, hb, Subgroup.card_bot]
      rw [hc] at h9dvd
      omega
    obtain ⟨z, -, hz, hz3⟩ := exists_eq_zpowers_of_pRank_le_one hexpPG hbot (fun x _ => hexp x) h1
    have hc : Nat.card ↥Ys = 3 := by
      rw [← Subgroup.card_top, hz, Nat.card_zpowers, hz3]
    rw [hc] at h9dvd
    omega
  rw [pRank_top_subtype (p := 3) Ys] at hrank2
  exact hrank2

end YPart

section ClaimA

variable {G : Type} [Group G] [Finite G]

theorem three_le_pRank_of_commuting {Q : Type} [Group Q] [Finite Q] {E : Subgroup Q} {z : Q}
    (hE : IsElemAbelian 3 E) (hE9 : Nat.card E = 9) (hz : z ^ 3 = 1)
    (hc : ∀ e ∈ E, e * z = z * e) (hzE : z ∉ E) : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Q) := by
  have hF := isElemAbelian_sup_zpowers hE hz hc
  have hEF : E ≤ E ⊔ Subgroup.zpowers z := le_sup_left
  have hzF : z ∈ E ⊔ Subgroup.zpowers z := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hFp : IsPGroup 3 ↥(E ⊔ Subgroup.zpowers z) := fun x =>
    ⟨1, Subtype.ext (by simpa using hF.2 x x.2)⟩
  obtain ⟨n, hn⟩ := hFp.exists_card_eq
  have h3 : 3 ≤ n := by
    by_contra hn3
    have hle : 3 ^ n ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hEF' : E = E ⊔ Subgroup.zpowers z :=
      Subgroup.eq_of_le_of_card_ge hEF (by rw [hn, hE9]; omega)
    exact hzE (hEF' ▸ hzF)
  exact h3.trans (CFSG.SectionRank.le_pRank (by norm_num) le_top hF hn)

theorem mem_of_mul_mem_pCoreOf {M Y : Subgroup G} (hYM : Y ≤ M)
    (hMY : M ≤ Subgroup.normalizer (Y : Set G)) {x y : G} (hxM : x ∈ M) (hy : y ∈ Y)
    (hx3 : x ^ 3 = 1) (ho : y⁻¹ * x ∈ pCoreOf 2 M) : x ∈ Y := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : (Y.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hYM).mpr hMY
  let q : ↥M →* ↥M ⧸ Y.subgroupOf M := QuotientGroup.mk' (Y.subgroupOf M)
  have hyM : y ∈ M := hYM hy
  have hoM : y⁻¹ * x ∈ M := M.mul_mem (M.inv_mem hyM) hxM
  have hxe : (⟨x, hxM⟩ : ↥M) = ⟨y, hyM⟩ * ⟨y⁻¹ * x, hoM⟩ := Subtype.ext (by simp)
  have hqy : q ⟨y, hyM⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hy)
  have hqx : q ⟨x, hxM⟩ = q ⟨y⁻¹ * x, hoM⟩ := by rw [hxe, map_mul, hqy, one_mul]
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 M ⟨y⁻¹ * x, ho⟩
  have hk' : (y⁻¹ * x) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h2k : (q ⟨x, hxM⟩) ^ 2 ^ k = 1 := by
    rw [hqx, ← map_pow]
    have : (⟨y⁻¹ * x, hoM⟩ : ↥M) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
    rw [this, map_one]
  have h3 : (q ⟨x, hxM⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨x, hxM⟩ : ↥M) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, map_one]
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have hq1 : q ⟨x, hxM⟩ = 1 :=
    orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h3)
      (orderOf_dvd_of_pow_eq_one h2k))
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hq1)

variable {T Mc M : Subgroup G}

theorem mem_Y153_of_pow_three (h113 : StageLemma14113) (h : Hyp153 G T Mc M) {x : G}
    (hxM : x ∈ M) (hx3 : x ^ 3 = 1) : x ∈ Y153 Mc M := by
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hMV : M ≤ Subgroup.normalizer (VZ T M : Set G) := h.le_normalizer
  have hOC : pCoreOf 2 M ≤ Subgroup.centralizer (VZ T M : Set G) :=
    h.hyp14117.pCoreOf_le_centralizer
  have hYM : Y153 Mc M ≤ M := Y153_le Mc M
  have hMY := le_normalizer_Y153 Mc M
  obtain ⟨⟨-, -, hexp⟩, -⟩ := Hyp153.Ystar_structure h113 h
  set Yq := imageOTwoQuot M (Y153 Mc M) with hYq
  set xs : OTwoQuot M := QuotientGroup.mk ⟨x, hxM⟩ with hxs
  have hxs3 : xs ^ 3 = 1 := by
    rw [hxs, ← QuotientGroup.mk_pow]
    have : (⟨x, hxM⟩ : ↥M) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, QuotientGroup.mk_one]
  have hρ : starAct M (VZ T M) hMV hOC xs ∈ autOn (Y153 Mc M) (VZ T M) := by
    rw [h.autOn_Y153 h113]
    refine mem_oTwoUpper_of_odd (mem_autOn_iff_exists.mpr ⟨x, hMV hxM, hxM, rfl⟩) ?_
    refine Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one ?_)
    rw [← map_pow, hxs3, map_one]
  rw [← map_starAct hMV hOC hYM] at hρ
  obtain ⟨ys, hys, hysρ⟩ := Subgroup.mem_map.mp hρ
  have hcs : ys⁻¹ * xs ∈ (starAct M (VZ T M) hMV hOC).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hysρ, inv_mul_cancel]
  rw [ker_starAct] at hcs
  obtain ⟨c, hcM, hcC, hcc⟩ := mem_imageOTwoQuot_iff.mp hcs
  set cs : OTwoQuot M := ys⁻¹ * xs with hcsdef
  have hcomm : ∀ e ∈ Yq, e * cs = cs * e := by
    intro e he
    obtain ⟨y, hyM, hyY, rfl⟩ := mem_imageOTwoQuot_iff.mp he
    rw [← hcc]
    exact (mk_commute_iff ⟨y, hyM⟩ ⟨c, hcM⟩).mpr (h.commutator_Y153_le hyY hcC)
  have hysY : ys * cs = xs := by rw [hcsdef]; group
  have hys3 : ys ^ 3 = 1 := by
    simpa using congrArg Subtype.val (hexp ⟨ys, hys⟩)
  have hcs3 : cs ^ 3 = 1 := by
    have h1 : (ys * cs) ^ 3 = ys ^ 3 * cs ^ 3 := (hcomm ys hys).symm ▸ Commute.mul_pow (hcomm ys hys) 3
    rw [hysY, hxs3, hys3, one_mul] at h1
    exact h1.symm
  by_cases hcY : cs ∈ Yq
  ·
    have hxY : xs ∈ Yq := by rw [← hysY]; exact Yq.mul_mem hys hcY
    obtain ⟨y', hy'M, hy'Y, hy'x⟩ := mem_imageOTwoQuot_iff.mp hxY
    refine mem_of_mul_mem_pCoreOf hYM hMY hxM hy'Y hx3 ?_
    have h1 : (⟨y', hy'M⟩ : ↥M)⁻¹ * ⟨x, hxM⟩ ∈ CFSG.Open.pCore 2 ↥M := QuotientGroup.eq.mp hy'x
    exact (Subgroup.mem_map_iff_mem M.subtype_injective).mpr h1
  · exfalso
    obtain ⟨E, hEY, hE, hE9⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3)
      (k := 2) (two_le_pRank_Ystar h113 h)
    have h3 := three_le_pRank_of_commuting hE (by simpa using hE9) hcs3
      (fun e he => hcomm e (hEY he)) (fun hzE => hcY (hEY hzE))
    exact absurd (pRank_OTwoQuot_le h) (by omega)

end ClaimA

end S153D

end CFSG.Quasithin
