module

public import CFSG.Quasithin.Background.C1PackS15348
public import CFSG.Quasithin.Background.C1PackS15349Gen
public import CFSG.Quasithin.EmptyFaithful.T1531Geom

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

namespace C1Pack153

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

omit [Finite G] in
theorem orderOf_dvd_card_of_mem {X : Subgroup G} [Finite X] {c : G} (hc : c ∈ X) :
    orderOf c ∣ Nat.card X := by
  have := orderOf_dvd_natCard (⟨c, hc⟩ : ↥X)
  rwa [Subgroup.orderOf_mk] at this

theorem oTwoUpper_inf_le (h11 : StageLemma14111) (h : Hyp153 G T Mc M) {H : Subgroup G}
    (hH : IsHTM153 T M H) : oTwoUpper (M ⊓ H) ≤ Subgroup.centralizer (VZ T M : Set G) := by
  have hHMc := le_mc_of_isHTM153 h11 h hH
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  exact mem_centralizer_of_odd_of_mem_inf h ⟨hHMc hx.1.2, hx.1.1⟩ hx.2

theorem convI_mem_autI_T (h : Hyp153 G T Mc M) {x : G} (hx : x ∈ Mc ⊓ M)
    (hxN : x ∈ Subgroup.normalizer (VZ T M : Set G)) :
    convI h.elemAbelian ⟨x, hxN⟩ ∈ autI h.elemAbelian T := by
  have hV := h.elemAbelian
  have hMN := h.le_normalizer
  have hxe : x ∈ (M ⊓ Subgroup.centralizer (VZ T M : Set G)) ⊔ T := by
    rw [← h.lemma_15_3_7_inf]
    exact hx
  have hC : M ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ Subgroup.normalizer (VZ T M : Set G) :=
    inf_le_left.trans hMN
  have hTN : T ≤ Subgroup.normalizer (VZ T M : Set G) := h.T_le.trans hMN
  have hmem : convI hV ⟨x, hxN⟩ ∈ autI hV ((M ⊓ Subgroup.centralizer (VZ T M : Set G)) ⊔ T) :=
    convI_mem_autI hV hxe hxN
  rwa [autI_sup hV hC hTN, autI_eq_bot_of_le_centralizer hV inf_le_right, bot_sup_eq] at hmem

theorem card_autI_Y153 (h113 : StageLemma14113) (h : Hyp153 G T Mc M) :
    Nat.card (autI h.elemAbelian (Y153 Mc M)) = 9 := by
  have hV := h.elemAbelian
  have hYN : Y153 Mc M ≤ Subgroup.normalizer (VZ T M : Set G) :=
    (Y153_le Mc M).trans h.le_normalizer
  have h1 := card_autI_mul_card_inf hV hYN
  have h2 := h.card_Y153 h113
  have hpos : 0 < Nat.card ↥(Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G)) := Nat.card_pos
  rw [h2] at h1
  have := Nat.eq_of_mul_eq_mul_right hpos (h1.trans (by ring) : _ = 9 * _)
  exact this

theorem mem_centralizer_of_mem_Y153_of_mem_Mc (h113 : StageLemma14113) (h : Hyp153 G T Mc M) {y : G}
    (hy : y ∈ Y153 Mc M) (hyMc : y ∈ Mc) : y ∈ Subgroup.centralizer (VZ T M : Set G) := by
  have hV := h.elemAbelian
  have hMN := h.le_normalizer
  have hyM : y ∈ M := Y153_le Mc M hy
  have hyN : y ∈ Subgroup.normalizer (VZ T M : Set G) := hMN hyM
  have hT2 : IsPGroup 2 (autI hV T) := B2F.isPGroup_autI hV h.qtfe.sylow.1 (h.T_le.trans hMN)
  have hmT := convI_mem_autI_T h ⟨hyMc, hyM⟩ hyN
  have hmY : convI hV ⟨y, hyN⟩ ∈ autI hV (Y153 Mc M) := convI_mem_autI hV hy hyN
  obtain ⟨k, hk⟩ := hT2 ⟨convI hV ⟨y, hyN⟩, hmT⟩
  have hk' : convI hV ⟨y, hyN⟩ ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h9 : (convI hV ⟨y, hyN⟩) ^ 9 = 1 := by
    have := pow_card_eq_one' (x := (⟨convI hV ⟨y, hyN⟩, hmY⟩ : ↥(autI hV (Y153 Mc M))))
    rw [card_autI_Y153 h113 h] at this
    exact congrArg Subtype.val this
  have hd1 : orderOf (convI hV ⟨y, hyN⟩) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hd2 : orderOf (convI hV ⟨y, hyN⟩) ∣ 9 := orderOf_dvd_of_pow_eq_one h9
  have hcop : Nat.Coprime (2 ^ k) 9 := Nat.Coprime.pow_left k (by norm_num)
  have h1 : orderOf (convI hV ⟨y, hyN⟩) = 1 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
  exact (convI_eq_one_iff hV ⟨y, hyN⟩).mp (orderOf_eq_one_iff.mp h1)

theorem inf_centralizer_Z_eq (h11 : StageLemma14111) (h113 : StageLemma14113)
    (h : Hyp153 G T Mc M) :
    Y153 Mc M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) =
      Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G) := by
  refine le_antisymm (fun y hy => ⟨hy.1, ?_⟩)
    (inf_le_inf_left _ (Subgroup.centralizer_le h.Z_le_VZ))
  have hyMc : y ∈ Mc := (h.lemma_15_3_4 h11) ▸ hy.2
  exact mem_centralizer_of_mem_Y153_of_mem_Mc h113 h hy.1 hyMc

theorem Y153_eq_oPrimeResidualOf (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    (h3 : IsThreePrimeGroup (M ⊓ Subgroup.centralizer (VZ T M : Set G))) :
    Y153 Mc M = oPrimeResidualOf 3 M := by
  have hV := h.elemAbelian
  have hMN := h.le_normalizer
  have hYM := Y153_le Mc M
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr fun y hy => ?_
    have hyY : y ∈ Y153 Mc M := Subgroup.subset_closure hy
    have hy3 : y ^ 3 ∈ pCoreOf 2 (Y153 Mc M) := h.pow_three_mem_pCoreOf_Y153 h113 hyY
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨j, hj⟩ := pCoreOf_isPGroup 2 (Y153 Mc M) ⟨y ^ 3, hy3⟩
    have hj' : (y ^ 3) ^ 2 ^ j = 1 := congrArg Subtype.val hj
    have hcop : Nat.Coprime (orderOf y) (2 ^ j) :=
      Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hy.2)
    have hy3' : y ^ 3 = 1 := by
      have hd : orderOf (y ^ 3) ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj'
      have hd' : orderOf (y ^ 3) ∣ orderOf y := orderOf_pow_dvd 3
      have := Nat.eq_one_of_dvd_coprimes hcop.symm hd hd'
      exact orderOf_eq_one_iff.mp this
    have hord : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one hy3'
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three (i := orderOf y) (m := 1)).mp (by rw [pow_one]; exact hord)
    exact Subgroup.subset_closure ⟨hYM hyY, k, hk⟩
  · refine (Subgroup.closure_le _).mpr fun x hx => ?_
    obtain ⟨hxM, k, hk⟩ := hx
    have hxN : x ∈ Subgroup.normalizer (VZ T M : Set G) := hMN hxM
    have hodd : Odd (orderOf (convI hV ⟨x, hxN⟩)) := by
      have hxo : convI hV ⟨x, hxN⟩ ^ orderOf x = 1 := by
        rw [← map_pow]
        have : (⟨x, hxN⟩ : Subgroup.normalizer (VZ T M : Set G)) ^ orderOf x = 1 :=
          Subtype.ext (by simp)
        rw [this, map_one]
      have hd : orderOf (convI hV ⟨x, hxN⟩) ∣ 3 ^ k := hk ▸ orderOf_dvd_of_pow_eq_one hxo
      exact Odd.of_dvd_nat (Odd.pow (by decide)) hd
    have hxbar : convI hV ⟨x, hxN⟩ ∈ autI hV (Y153 Mc M) := by
      have e : autI hV (Y153 Mc M) = oTwoUpper (autI hV M) := h.autOn_Y153 h113
      rw [e]
      exact Subgroup.subset_closure ⟨convI_mem_autI hV hxM hxN, hodd⟩
    obtain ⟨g, hgY, hg⟩ := (mem_autI hV).1 hxbar
    have hgM : (g : G) ∈ M := hYM hgY
    have hcC : x * (g : G)⁻¹ ∈ Subgroup.centralizer (VZ T M : Set G) := by
      refine (convI_eq_one_iff hV (⟨x, hxN⟩ * g⁻¹)).mp ?_
      rw [map_mul, map_inv, hg, mul_inv_cancel]
    have hcM : x * (g : G)⁻¹ ∈ M := M.mul_mem hxM (M.inv_mem hgM)
    have hYn : (Y153 Mc M).subgroupOf M ≤ (Y153 Mc M).subgroupOf M := le_rfl
    have : ((Y153 Mc M).subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hYM).mpr (le_normalizer_Y153 Mc M)
    let φ : ↥M →* ↥M ⧸ (Y153 Mc M).subgroupOf M := QuotientGroup.mk' _
    have hφy : φ ⟨(g : G), hgM⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hgY)
    have hxe : (⟨x, hxM⟩ : ↥M) = ⟨x * (g : G)⁻¹, hcM⟩ * ⟨(g : G), hgM⟩ :=
      Subtype.ext (by simp)
    have hφx : φ ⟨x, hxM⟩ = φ ⟨x * (g : G)⁻¹, hcM⟩ := by
      rw [hxe, map_mul, hφy, mul_one]
    have h1 : orderOf (φ ⟨x, hxM⟩) ∣ 3 ^ k := by
      refine (orderOf_map_dvd φ ⟨x, hxM⟩).trans ?_
      rw [Subgroup.orderOf_mk, hk]
    have h2 : orderOf (φ ⟨x, hxM⟩) ∣ orderOf (x * (g : G)⁻¹) := by
      rw [hφx]
      refine (orderOf_map_dvd φ ⟨x * (g : G)⁻¹, hcM⟩).trans ?_
      rw [Subgroup.orderOf_mk]
    have h3' : ¬ 3 ∣ orderOf (x * (g : G)⁻¹) := fun hd =>
      h3 (hd.trans (orderOf_dvd_card_of_mem (X := M ⊓ Subgroup.centralizer (VZ T M : Set G))
        ⟨hcM, hcC⟩))
    have hcop : Nat.Coprime (3 ^ k) (orderOf (x * (g : G)⁻¹)) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3')
    have h4 : orderOf (φ ⟨x, hxM⟩) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    have h5 : φ ⟨x, hxM⟩ = 1 := orderOf_eq_one_iff.mp h4
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h5)

theorem isThreePrimeGroup_inf (h11 : StageLemma14111) (h : Hyp153 G T Mc M) {H : Subgroup G}
    (hH : IsHTM153 T M H)
    (h3 : IsThreePrimeGroup (M ⊓ Subgroup.centralizer (VZ T M : Set G))) :
    IsThreePrimeGroup (M ⊓ H) := by
  intro hdvd
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  have hxo : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  have hHMc := le_mc_of_isHTM153 h11 h hH
  have hxC : (x : G) ∈ Subgroup.centralizer (VZ T M : Set G) :=
    mem_centralizer_of_odd_of_mem_inf h ⟨hHMc x.2.2, x.2.1⟩ (by rw [hxo]; decide)
  apply h3
  have := orderOf_dvd_card_of_mem (X := M ⊓ Subgroup.centralizer (VZ T M : Set G))
    (c := (x : G)) ⟨x.2.1, hxC⟩
  rwa [hxo] at this

theorem centralizes_Z_of_mem_normalizer_ZS (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t)
    {x : G} (hxM : x ∈ M) (hxN : x ∈ Subgroup.normalizer (ZS153 T M V₁ : Set G)) :
    x ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  classical
  obtain ⟨a, haV₁, ha1, -⟩ := exists_gen_inf_centralizer_Sgp153 h D
  obtain ⟨b, hbV₂, hb1, -⟩ := exists_gen_inf_centralizer_Sgp153 h D.swapPlanes
  rw [h.Sgp153_eq_inf_normalizer_V₂ D] at hbV₂
  obtain ⟨z, hz, hz1⟩ := exists_ne_one_mem_Z h
  obtain ⟨hzV₁, hzV₂⟩ := not_mem_V₁_V₂_of_mem_Z h D hz hz1
  have haZ : a ∈ ZS153 T M V₁ := ⟨D.le₁ haV₁.1, haV₁.2⟩
  have hbZ : b ∈ ZS153 T M V₁ := ⟨D.le₂ hbV₂.1, hbV₂.2⟩
  have hzZ : z ∈ ZS153 T M V₁ := Z_le_ZS h hz
  have hab : a ≠ b := fun e => by
    have : a ∈ V₁ ⊓ V₂ := ⟨haV₁.1, e ▸ hbV₂.1⟩
    rw [D.inf, Subgroup.mem_bot] at this
    exact ha1 this
  have haz : a ≠ z := fun e => hzV₁ (e ▸ haV₁.1)
  have hbz : b ≠ z := fun e => hzV₂ (e ▸ hbV₂.1)
  have : Fintype ↥(ZS153 T M V₁) := Fintype.ofFinite _
  have hc4 : Nat.card (ZS153 T M V₁) = 4 := D.card_ZS h
  let Q : Finset G := (ZS153 T M V₁ : Set G).toFinset
  have hQcard : Q.card = 4 := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
    exact hc4
  let P : Finset G := {1, a, b, z}
  have hPQ : P ⊆ Q := by
    intro w hw
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hw
    rw [Set.mem_toFinset]
    rcases hw with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact haZ
    · exact hbZ
    · exact hzZ
  have hPcard : P.card = 4 := by
    have h1 : (1 : G) ∉ ({a, b, z} : Finset G) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨ha1.symm, hb1.symm, hz1.symm⟩
    have h2 : a ∉ ({b, z} : Finset G) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hab, haz⟩
    have h3 : b ∉ ({z} : Finset G) := by
      simp only [Finset.mem_singleton]
      exact hbz
    simp only [P]
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_insert_of_notMem h3, Finset.card_singleton]
  have hPQeq : P = Q := Finset.eq_of_subset_of_card_le hPQ (by rw [hPcard, hQcard])
  have hwZ : x * z * x⁻¹ ∈ ZS153 T M V₁ := (Subgroup.mem_normalizer_iff.mp hxN z).mp hzZ
  have hw1 : x * z * x⁻¹ ≠ 1 := fun e => hz1 (by
    have := congrArg (fun u => x⁻¹ * u * x) e
    simpa [mul_assoc] using this)
  have hwn : ¬ (x * z * x⁻¹ ∈ V₁ ∨ x * z * x⁻¹ ∈ V₂) := fun hw => by
    have h1 := conj_mem_V₁_or_V₂ h D (M.inv_mem hxM) hw
    have e : x⁻¹ * (x * z * x⁻¹) * x⁻¹⁻¹ = z := by group
    rw [e] at h1
    exact h1.elim hzV₁ hzV₂
  have hwP : x * z * x⁻¹ ∈ P := by
    rw [hPQeq, Set.mem_toFinset]
    exact hwZ
  have hxz : x * z * x⁻¹ = z := by
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hwP
    rcases hwP with e | e | e | e
    · exact absurd e hw1
    · exact absurd (Or.inl (e ▸ haV₁.1)) hwn
    · exact absurd (Or.inr (e ▸ hbV₂.1)) hwn
    · exact e
  have hZ2 := h.lemma_15_3_2_two.2
  have hzsq : z ^ 2 = 1 := h.elemAbelian.2 z (h.Z_le_VZ hz)
  have hzord : orderOf z = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hzsq hz1
  have hZeq : Subgroup.zpowers z = quasithinOmegaOneCenter T := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz) ?_
    rw [hZ2, Nat.card_zpowers, hzord]
  rw [← hZeq]
  refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hcomm : Commute z x := by
    have : z * x = x * z := by
      have := hxz
      calc z * x = (x * z * x⁻¹) * x := by rw [hxz]
        _ = x * z := by group
    exact this
  exact (hcomm.zpow_left n).eq

theorem isThreePrimeGroup_normalizer_ZS (h11 : StageLemma14111) (h : Hyp153 G T Mc M)
    (D : Decomp153 T M V₁ V₂ t) (r46 : Res15346 T M V₁ V₂)
    (h3 : IsThreePrimeGroup (M ⊓ Subgroup.centralizer (VZ T M : Set G))) :
    IsThreePrimeGroup (Subgroup.normalizer (ZS153 T M V₁ : Set G)) := by
  intro hdvd
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  have hxo : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  have hxM : (x : G) ∈ M := r46.normalizer_ZS x.2
  have hxZ := centralizes_Z_of_mem_normalizer_ZS h D hxM x.2
  have hxMc : (x : G) ∈ Mc := (h.lemma_15_3_4 h11) ▸ hxZ
  have hxC : (x : G) ∈ Subgroup.centralizer (VZ T M : Set G) :=
    mem_centralizer_of_odd_of_mem_inf h ⟨hxMc, hxM⟩ (by rw [hxo]; decide)
  apply h3
  have := orderOf_dvd_card_of_mem (X := M ⊓ Subgroup.centralizer (VZ T M : Set G))
    (c := (x : G)) ⟨hxM, hxC⟩
  rwa [hxo] at this

theorem isHTM153_mc (h : Hyp153 G T Mc M) : IsHTM153 T M Mc :=
  ⟨⟨h.qtfe.t_le_mc, pCoreOf_ne_bot_of_isTwoLocal h.qtfe.mc_max.1⟩,
    fun hle => h.ne_mc (h.qtfe.mc_max.2 M h.inM.1.1 hle)⟩

theorem le_pCoreOf_of_oTwoFstarIn_le' {H : Subgroup G} (h : oTwoFstarIn H ≤ pCoreOf 2 H) :
    H ≤ pCoreOf 2 H := by
  have hF : CFSG.generalizedFitting (OTwoQuot H) = ⊥ := by
    rw [← imageOTwoQuot_O2Fstar H, map_O2Fstar_eq_oTwoFstarIn]
    refine eq_bot_iff.mpr ?_
    rintro _ ⟨⟨y, hyH⟩, hy, rfl⟩
    have hyQ : y ∈ pCoreOf 2 H := h (Subgroup.mem_subgroupOf.mp hy)
    obtain ⟨z, hz, hzy⟩ := hyQ
    have : z = ⟨y, hyH⟩ := Subtype.ext hzy
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff _).mpr (this ▸ hz)
  have hc := CFSG.centralizer_generalizedFitting_le (OTwoQuot H)
  rw [hF] at hc
  intro x hx
  have h1 : (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H) ⟨x, hx⟩ : OTwoQuot H) ∈
      (⊥ : Subgroup (OTwoQuot H)) := by
    refine hc ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [SetLike.mem_coe, Subgroup.mem_bot] at hz
    rw [hz]
    simp
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact ⟨_, h1, rfl⟩

theorem comm_ZS_of_hypF91 (h11 : StageLemma14111) (c : Ctx153 G T Mc M V₁ V₂ t)
    (hF : HypF91 T (VZ T M) (Y153 Mc M) (quasithinOmegaOneCenter T) (ZS153 T M V₁) Mc) :
    ⁅ZS153 T M V₁, pCoreOf 2 Mc⁆ = quasithinOmegaOneCenter T := by
  classical
  have h := c.hyp
  have hMc := isHTM153_mc h
  have hZ2 := h.lemma_15_3_2_two.2
  have hMcZ : Mc ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    (h.lemma_15_3_4 h11).le
  have hle : ⁅ZS153 T M V₁, pCoreOf 2 Mc⁆ ≤ quasithinOmegaOneCenter T := by
    refine Subgroup.commutator_le.mpr fun u hu q hq => ?_
    have := hF.commutator_conjClosure_le u (le_conjClosure (ZS153 T M V₁) Mc hu) q hq
    rwa [commutatorElement_def]
  rcases HypF98.eq_bot_or_eq_of_card_eq_two hZ2 hle with hbot | heq
  swap
  · exact heq
  exfalso
  have hZsC : ZS153 T M V₁ ≤ Subgroup.centralizer (pCoreOf 2 Mc : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  have hQC : pCoreOf 2 Mc ≤ Subgroup.centralizer (ZS153 T M V₁ : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by rw [Subgroup.commutator_comm]; exact hbot)
  have hUQ : conjClosure (ZS153 T M V₁) Mc ≤ pCoreOf 2 Mc := hF.conjClosure_Vp_le_pCoreOf
  have hUC : conjClosure (ZS153 T M V₁) Mc ≤ Subgroup.centralizer (pCoreOf 2 Mc : Set G) := by
    refine conjClosure_le fun k hk z hz => ?_
    refine Subgroup.mem_centralizer_iff.mpr fun q hq => ?_
    have hq' : k⁻¹ * q * k ∈ pCoreOf 2 Mc := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 Mc (Mc.inv_mem hk)) q).mp hq
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp (hQC hq') z hz
    calc q * (k * z * k⁻¹) = k * ((k⁻¹ * q * k) * z) * k⁻¹ := by group
      _ = k * (z * (k⁻¹ * q * k)) * k⁻¹ := by rw [← h1]
      _ = (k * z * k⁻¹) * q := by group
  have hUel : IsElemAbelian 2 (conjClosure (ZS153 T M V₁) Mc) := by
    refine HypF91.isElemAbelian_conjClosure_of_forall hF.elemAbelian_Vp fun k hk => ?_
    exact hZsC.trans (Subgroup.centralizer_le ((HypF91.conjSub_le_conjClosure hk).trans hUQ))
  have hUΩ : conjClosure (ZS153 T M V₁) Mc ≤ omegaOneCenterOf (pCoreOf 2 Mc) := fun u hu =>
    mem_quasithinOmegaOneCenter_iff.mpr ⟨hUQ hu, hUC hu, isElemAbelian_pow_eq_one hUel hu⟩
  have hFst := C1Pack.oTwoFstarIn_le_centralizer_omegaOneCenter h.qtfe.qtke h.qtfe.sylow
    h.qtfe.faithful_empty hMc.1 hMcZ
  have hFQ : oTwoFstarIn Mc ≤ pCoreOf 2 Mc := by
    intro x hx
    have hxMc : x ∈ Mc := Subgroup.map_subtype_le _ hx
    rw [hF.pCoreOf_eq_centralizerMod]
    refine ⟨hxMc, (Subgroup.centralizer_le_normalizer _) (hMcZ hxMc), fun u hu => ?_⟩
    have hc := Subgroup.mem_centralizer_iff.mp (hFst hx) u (hUΩ hu)
    have : x * u * x⁻¹ * u⁻¹ = 1 := by rw [← hc]; group
    rw [this]
    exact Subgroup.one_mem _
  have hMcle : Mc ≤ pCoreOf 2 Mc := le_pCoreOf_of_oTwoFstarIn_le' hFQ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMc2 : IsPGroup 2 Mc := (pCoreOf_isPGroup 2 Mc).to_le hMcle
  have hsyl : IsSylowTwoOf T Mc := isSylowTwoOf_of_quasithinIsSylowTwo h.qtfe.sylow h.qtfe.t_le_mc
  have hMcT : Mc ≤ T := by
    refine A4.le_of_normal_of_isSylowTwoOf hsyl le_rfl ?_ hMc2
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.normal_top
  exact hMc.2 (hMcT.trans h.T_le)

end C1Pack153

@[expose] def Stage15349Core : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ : Subgroup G) (t : G),
    Ctx153 G T Mc M V₁ V₂ t → Res15345 T Mc M V₁ V₂ → Res15346 T M V₁ V₂ → Res15347 T M V₁ →
      (∀ H : Subgroup G, IsHTM153 T M H →
        (Case157Two T Mc M → Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ H) →
          HypF91 T (VZ T M) (Y153 Mc M) (quasithinOmegaOneCenter T) (ZS153 T M V₁) H) →
      IsThreePrimeGroup (M ⊓ Subgroup.centralizer (VZ T M : Set G))

theorem stage15349_of_core (h11 : StageLemma14111) (h113 : StageLemma14113)
    (i : Stage15349Core) : Stage15349 := by
  intro G _ _ T Mc M V₁ V₂ t c r45 r46 r47 hF91
  have h := c.hyp
  have h3 : IsThreePrimeGroup (M ⊓ Subgroup.centralizer (VZ T M : Set G)) :=
    i G T Mc M V₁ V₂ t c r45 r46 r47 hF91
  have hcase1 : Case157One T Mc M := by
    rcases h.lemma_15_3_7_cases h113 with h1 | h2
    · exact h1
    · exfalso
      have hcardY := h.card_Y153 h113
      have hq27 : Nat.card (OTwoQuot (Y153 Mc M)) = 27 := by
        have := h2.1.2.1
        simpa using this
      have hLag := Subgroup.card_eq_card_quotient_mul_card_subgroup
        (CFSG.Open.pCore 2 ↥(Y153 Mc M))
      have hdvd : 3 ∣ Nat.card ↥(Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G)) := by
        refine ⟨Nat.card (CFSG.Open.pCore 2 ↥(Y153 Mc M)), ?_⟩
        have e : 9 * Nat.card ↥(Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G)) =
            27 * Nat.card (CFSG.Open.pCore 2 ↥(Y153 Mc M)) := by
          rw [← hcardY, hLag]
          exact congrArg (· * _) hq27
        omega
      exact h3 (hdvd.trans (Subgroup.card_dvd_of_le
        (inf_le_inf_right _ (Y153_le Mc M))))
  have hMc := C1Pack153.isHTM153_mc h
  refine
    { oTwoUpper_le := fun H hH => C1Pack153.oTwoUpper_inf_le h11 h hH
      comm_ZS := C1Pack153.comm_ZS_of_hypF91 h11 c
        (hF91 Mc hMc (fun _ => inf_le_right.trans
          ((Subgroup.centralizer_le h.Z_le_VZ).trans (h.lemma_15_3_4 h11).ge)))
      case_one := hcase1
      pCore_eq_centralizer_Z := hcase1.1.trans
        (C1Pack153.inf_centralizer_Z_eq h11 h113 h).symm
      eq_oPrime := C1Pack153.Y153_eq_oPrimeResidualOf h113 h h3
      threePrime_C := h3
      threePrime_MH := fun H hH => C1Pack153.isThreePrimeGroup_inf h11 h hH h3
      normalizer_ZS_eq := le_antisymm (fun x hx => ⟨r46.normalizer_ZS hx, hx⟩) inf_le_right
      threePrime_N := C1Pack153.isThreePrimeGroup_normalizer_ZS h11 h c.decomp r46 h3 }

end CFSG.Quasithin
