module

public import CFSG.Walter.ReeOrder.JT.Section7O
public import CFSG.Walter.ReeOrder.JT.AuxHH
public import CFSG.Walter.ReeOrder.JT.Section7M

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups
open CFSG

variable {G : Type} [Group G] [Finite G]

theorem mul_comm_of_not_eight_dvd {R : Type*} [Group R] [Finite R] (hR : IsPGroup 2 R)
    (h8 : ¬ 8 ∣ Nat.card R) (a b : R) : a * b = b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hR.exists_card_eq
  have hk2 : k ≤ 2 := by
    by_contra hk2
    exact h8 (hk ▸ (pow_dvd_pow 2 (by omega : 3 ≤ k)))
  interval_cases k
  · rw [pow_zero] at hk
    have : Subsingleton R := (Nat.card_eq_one_iff_unique.mp hk).1
    exact Subsingleton.elim _ _
  · rw [pow_one] at hk
    have := isCyclic_of_prime_card hk
    exact (IsCyclic.commGroup.mul_comm a b)
  · have := IsPGroup.isMulCommutative_of_card_eq_prime_sq hk
    exact this.is_comm.comm a b

theorem le_pCore_of_isPGroup {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hX : ∀ S : Sylow p X, (S : Subgroup X) ≤ pCore p X) {Y : Subgroup X} (hY : IsPGroup p Y) :
    Y ≤ pCore p X := by
  obtain ⟨S, hS⟩ := hY.exists_le_sylow
  exact hS.trans (hX S)

namespace JTHyp

variable (h : JTHyp G) (hp3 : h.p = 3)
include hp3

theorem false_of_isCyclic_omegaZ
    (c : TorusConf h) {p : ℕ} [hp : Fact p.Prime]
    (hpq : p ∣ (h.q - 1) / 2) (P : Sylow p G)
    (hT₀P : c.T₀ ≤ Subgroup.normalizer ((P : Subgroup G) : Set G))
    (hPc : ¬ IsCyclic (P : Subgroup G)) (hW : IsCyclic (omegaZ (P : Subgroup G) p)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp7 := h.seven_le_of_pi hp3 hpq
  have hp2 : p ≠ 2 := by omega
  obtain ⟨e₀, he₀P, he₀o, he₀c, he₀W, hTe₀, u, huT, hu1, he₀u⟩ :=
    h.exists_E₀ hp3 c hpq P hT₀P hPc hW
  set W := omegaZ (P : Subgroup G) p with hWdef
  have hWc : ∀ w ∈ W, ∀ y ∈ (P : Subgroup G), w * y = y * w := fun w hw y hy => hw.2.1 y hy
  have hWP : W ≤ P := omegaZ_le
  have hP1 : (P : Subgroup G) ≠ ⊥ := fun h0 => hPc (by rw [h0]; infer_instance)
  have hW1 : W ≠ ⊥ := omegaZ_ne_bot P.isPGroup' hP1
  have hWcard : Nat.card W = p :=
    card_eq_of_isCyclic_of_pow_eq_one hW hW1 fun w hw => pow_eq_one_of_mem_omegaZ hw
  have he₀1 : e₀ ≠ 1 := fun h0 => he₀W (h0 ▸ W.one_mem)
  have hdisj : ∀ a ∈ Subgroup.zpowers e₀, a ∈ W → a = 1 := by
    intro a ha haW
    by_contra ha1
    have hza : Subgroup.zpowers a = Subgroup.zpowers e₀ := by
      refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr ha) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, he₀o]
      have hao : orderOf a ∣ p := (orderOf_dvd_of_mem_zpowers ha).trans (dvd_of_eq he₀o)
      rcases (Nat.dvd_prime hp.out).mp hao with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) ha1
      · exact h1.ge
    apply he₀W
    have : e₀ ∈ Subgroup.zpowers a := hza ▸ Subgroup.mem_zpowers e₀
    exact (Subgroup.zpowers_le.mpr haW) this
  have hconj : ∀ x ∈ (P : Subgroup G), ∃ w ∈ W, x⁻¹ * e₀ * x = w * e₀ := by
    intro x hx
    have h1 := he₀c x⁻¹ (P.inv_mem hx)
    refine ⟨(e₀ * x⁻¹ * e₀⁻¹ * x⁻¹⁻¹)⁻¹, W.inv_mem h1, ?_⟩
    group
  set P₀ := (P : Subgroup G) ⊓ Subgroup.centralizer ({e₀} : Set G) with hP₀def
  have hP₀P : P₀ ≤ P := inf_le_left
  have hP₀p : IsPGroup p P₀ := P.isPGroup'.to_le hP₀P
  have hPN₀ : (P : Subgroup G) ≤ Subgroup.normalizer (P₀ : Set G) := by
    intro x hx
    refine mem_normalizer_of_conj_mem fun z hz => ⟨P.mul_mem (P.mul_mem hx hz.1) (P.inv_mem hx), ?_⟩
    obtain ⟨w, hw, hwx⟩ := hconj x hx
    have hz' : z * e₀ = e₀ * z := Subgroup.mem_centralizer_singleton_iff.mp hz.2
    have hzw : w * z = z * w := hWc w hw z hz.1
    show x * z * x⁻¹ ∈ Subgroup.centralizer ({e₀} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have key : z * (x⁻¹ * e₀ * x) = (x⁻¹ * e₀ * x) * z := by
      rw [hwx, ← mul_assoc, ← hzw, mul_assoc, hz', ← mul_assoc]
    calc x * z * x⁻¹ * e₀ = x * (z * (x⁻¹ * e₀ * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * e₀ * x) * z) * x⁻¹ := by rw [key]
      _ = e₀ * (x * z * x⁻¹) := by group
  have hTN₀ : c.T₀ ≤ Subgroup.normalizer (P₀ : Set G) := by
    intro τ hτ
    refine mem_normalizer_of_conj_mem fun z hz =>
      ⟨(Subgroup.mem_normalizer_iff.mp (hT₀P hτ) z).mp hz.1, ?_⟩
    have hz' : z * e₀ = e₀ * z := Subgroup.mem_centralizer_singleton_iff.mp hz.2
    have hτe : τ⁻¹ * e₀ * τ ∈ Subgroup.zpowers e₀ := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hTe₀ hτ)) e₀).mp
        (Subgroup.mem_zpowers e₀)
      simpa using this
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hτe
    have hzk : z * e₀ ^ k = e₀ ^ k * z := ((Commute.zpow_right (hz' : Commute z e₀) k)).eq
    rw [hk] at hzk
    show τ * z * τ⁻¹ ∈ Subgroup.centralizer ({e₀} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc τ * z * τ⁻¹ * e₀ = τ * (z * (τ⁻¹ * e₀ * τ)) * τ⁻¹ := by group
      _ = τ * ((τ⁻¹ * e₀ * τ) * z) * τ⁻¹ := by rw [hzk]
      _ = e₀ * (τ * z * τ⁻¹) := by group
  have hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb => hWc a ha b (hWP hb)
  have hmemW : ∀ x ∈ (P : Subgroup G), x * e₀ * x⁻¹ * e₀⁻¹ ∈ W := by
    intro x hx
    have := W.inv_mem (he₀c x hx)
    convert this using 1
    group
  let φ : (P : Subgroup G) →* W :=
    { toFun := fun x => ⟨x * e₀ * x⁻¹ * e₀⁻¹, hmemW x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        have ha := hmemW y y.2
        set a := (y : G) * e₀ * (y : G)⁻¹ * e₀⁻¹ with hadef
        have hya : (y : G) * e₀ * (y : G)⁻¹ = a * e₀ := by rw [hadef]; group
        have hxa : (x : G) * a = a * x := (hWc a ha x x.2).symm
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulMemClass.mk_mul_mk]
        rw [hWcomm _ (hmemW x x.2) _ ha]
        calc (x : G) * y * e₀ * ((x : G) * y)⁻¹ * e₀⁻¹
            = (x : G) * ((y : G) * e₀ * (y : G)⁻¹) * (x : G)⁻¹ * e₀⁻¹ := by group
          _ = (x : G) * (a * e₀) * (x : G)⁻¹ * e₀⁻¹ := by rw [hya]
          _ = ((x : G) * a) * e₀ * (x : G)⁻¹ * e₀⁻¹ := by group
          _ = (a * x) * e₀ * (x : G)⁻¹ * e₀⁻¹ := by rw [hxa]
          _ = a * ((x : G) * e₀ * (x : G)⁻¹ * e₀⁻¹) := by group) }
  have hker : φ.ker = P₀.subgroupOf P := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have h1 : (x : G) * e₀ * (x : G)⁻¹ * e₀⁻¹ = 1 := congrArg Subtype.val hx
      refine ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have : (x : G) * e₀ = e₀ * x := by
        rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
        exact h1
      exact this
    · intro hx
      apply Subtype.ext
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp hx.2
      change (x : G) * e₀ * (x : G)⁻¹ * e₀⁻¹ = 1
      rw [h1]
      group
  have hrange : Nat.card φ.range = p := by
    have hdvd : Nat.card φ.range ∣ p :=
      (Subgroup.card_subgroup_dvd_card _).trans (dvd_of_eq hWcard)
    rcases (Nat.dvd_prime hp.out).mp hdvd with h1 | h1
    · exfalso
      have htop : φ.ker = ⊤ := by
        rw [← Subgroup.index_eq_one, Subgroup.index_ker, h1]
      apply he₀W
      refine ⟨he₀P, fun y hy => ?_, by rw [← he₀o, pow_orderOf_eq_one]⟩
      have : (⟨y, hy⟩ : (P : Subgroup G)) ∈ φ.ker := htop ▸ Subgroup.mem_top _
      rw [hker, Subgroup.mem_subgroupOf] at this
      exact (Subgroup.mem_centralizer_singleton_iff.mp this.2).symm
    · exact h1
  have hcardP₀ : Nat.card (P : Subgroup G) = p * Nat.card P₀ := by
    have h1 := φ.ker.card_mul_index
    rw [Subgroup.index_ker, hrange, hker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₀P).toEquiv] at h1
    rw [← h1, mul_comm]
  set Es := omegaZ P₀ p with hEsdef
  have hEsP₀ : Es ≤ P₀ := omegaZ_le
  have hEsp : IsPGroup p Es := hP₀p.to_le hEsP₀
  have hEsexp : ∀ x ∈ Es, x ^ p = 1 := fun x hx => pow_eq_one_of_mem_omegaZ hx
  have he₀p : e₀ ^ p = 1 := by rw [← he₀o, pow_orderOf_eq_one]
  have he₀P₀ : e₀ ∈ P₀ := ⟨he₀P, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have he₀Es : e₀ ∈ Es :=
    ⟨he₀P₀, fun y hy => (Subgroup.mem_centralizer_singleton_iff.mp hy.2).symm, he₀p⟩
  have hWEs : W ≤ Es := fun w hw =>
    ⟨⟨hWP hw, Subgroup.mem_centralizer_singleton_iff.mpr (hWc w hw e₀ he₀P)⟩,
      fun y hy => hWc w hw y hy.1, pow_eq_one_of_mem_omegaZ hw⟩
  have hTEs : c.T₀ ≤ Subgroup.normalizer (Es : Set G) :=
    hTN₀.trans normalizer_le_normalizer_omegaZ
  have hPEs : (P : Subgroup G) ≤ Subgroup.normalizer (Es : Set G) :=
    hPN₀.trans normalizer_le_normalizer_omegaZ
  have hEscard : Nat.card Es ≤ p ^ 3 :=
    h.card_le_cube hp3 hpq hEsp hEsexp c.isKleinFour_T₀ hTEs
  have hEs1 : Es ≠ ⊥ := fun h0 => he₀1 (by
    have : e₀ ∈ (⊥ : Subgroup G) := h0 ▸ he₀Es
    exact Subgroup.mem_bot.mp this)
  have hEsnc : ¬ IsCyclic Es := by
    intro hc
    apply he₀W
    have : Subgroup.zpowers e₀ = W := eq_of_le_of_isCyclic hc ((Subgroup.zpowers_le).mpr he₀Es)
      hWEs (by rw [Nat.card_zpowers, he₀o, hWcard])
    exact this ▸ Subgroup.mem_zpowers e₀
  obtain ⟨u', hu'T, hu'1, hWu'⟩ : ∃ u' ∈ c.T₀, u' ≠ 1 ∧
      W ≤ Subgroup.centralizer ({u'} : Set G) := by
    have hBW := h.card_eq_mul_of_le_normalizer hp3 c hpq (P.isPGroup'.to_le hWP)
      (hT₀P.trans normalizer_le_normalizer_omegaZ)
    rw [hWcard] at hBW
    have hfull : ∀ v : G, Nat.card (W ⊓ Subgroup.centralizer ({v} : Set G) : Subgroup G) = p →
        W ≤ Subgroup.centralizer ({v} : Set G) := fun v hv =>
      fun w hw => (Subgroup.eq_of_le_of_card_ge (inf_le_left :
        W ⊓ Subgroup.centralizer ({v} : Set G) ≤ W) (by rw [hv, hWcard])).symm ▸ hw |>.2
    have hp' := hp.out
    set A := Nat.card (W ⊓ Subgroup.centralizer ({h.t} : Set G) : Subgroup G)
    set B := Nat.card (W ⊓ Subgroup.centralizer ({c.w} : Set G) : Subgroup G)
    set D := Nat.card (W ⊓ Subgroup.centralizer ({h.t * c.w} : Set G) : Subgroup G)
    have hA : A ∣ p := ⟨B * D, by rw [hBW]; ring⟩
    have hB : B ∣ p := ⟨A * D, by rw [hBW]; ring⟩
    rcases (Nat.dvd_prime hp').mp hA with h1 | h1
    · rcases (Nat.dvd_prime hp').mp hB with h2 | h2
      · rw [h1, h2, one_mul, one_mul] at hBW
        exact ⟨_, c.tw_mem_T₀, c.tw_ne_one, hfull _ hBW.symm⟩
      · exact ⟨_, c.w_mem_T₀, c.w_ne_one, hfull _ h2⟩
    · exact ⟨_, c.t_mem_T₀, h.t_ne_one, hfull _ h1⟩
  obtain ⟨⟨w₀, hw₀W⟩, hw₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW1
  have hw₀1' : w₀ ≠ 1 := fun h0 => hw₀1 (Subtype.ext h0)
  have hw₀o : orderOf w₀ = p := orderOf_eq_prime (pow_eq_one_of_mem_omegaZ hw₀W) hw₀1'
  obtain ⟨g, k, hgk⟩ := h.exists_conj_zpow_eq hp3 c hpq hw₀o he₀o (c.orderOf_of_mem hu'T hu'1)
    (c.orderOf_of_mem huT hu1)
    (Subgroup.mem_centralizer_singleton_iff.mp (hWu' hw₀W)) he₀u
  have hw₀k : w₀ ^ k ∈ W := Subgroup.zpow_mem _ hw₀W k
  set C₀ := Subgroup.centralizer ({e₀} : Set G) with hC₀def
  have hPg : (P : Subgroup G).map (MulAut.conj g).toMonoidHom ≤ C₀ := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hgk]
    have hc : x * w₀ ^ k = w₀ ^ k * x := (hWc _ hw₀k x hx).symm
    change g * x * g⁻¹ * (g * w₀ ^ k * g⁻¹) = g * w₀ ^ k * g⁻¹ * (g * x * g⁻¹)
    calc g * x * g⁻¹ * (g * w₀ ^ k * g⁻¹) = g * (x * w₀ ^ k) * g⁻¹ := by group
      _ = g * (w₀ ^ k * x) * g⁻¹ := by rw [hc]
      _ = g * w₀ ^ k * g⁻¹ * (g * x * g⁻¹) := by group
  have hP₀C₀ : P₀ ≤ C₀ := inf_le_right
  obtain ⟨S, hS⟩ := (hP₀p.comap_subtype (K := C₀)).exists_le_sylow
  set Ps : Subgroup G := (S : Subgroup C₀).map C₀.subtype with hPsdef
  have hPsC₀ : Ps ≤ C₀ := Subgroup.map_subtype_le _
  have hP₀Ps : P₀ ≤ Ps := fun x hx =>
    ⟨⟨x, hP₀C₀ hx⟩, hS (by rw [Subgroup.mem_comap]; exact hx), rfl⟩
  have hPsp : IsPGroup p Ps := S.isPGroup'.map _
  have hPscard : Nat.card Ps = Nat.card (P : Subgroup G) := by
    apply le_antisymm
    · obtain ⟨Q, hQ⟩ := hPsp.exists_le_sylow
      calc Nat.card Ps ≤ Nat.card (Q : Subgroup G) := Subgroup.card_le_of_le hQ
        _ = Nat.card (P : Subgroup G) := by
          rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
    · have hPgp : IsPGroup p ((P : Subgroup G).map (MulAut.conj g).toMonoidHom) :=
        P.isPGroup'.map _
      obtain ⟨S', hS'⟩ := (hPgp.comap_subtype (K := C₀)).exists_le_sylow
      have h1 : Nat.card (((P : Subgroup G).map (MulAut.conj g).toMonoidHom).comap
          C₀.subtype) = Nat.card (P : Subgroup G) := by
        rw [← Subgroup.card_map_of_injective C₀.subtype_injective,
          Subgroup.map_comap_eq_self (by rw [Subgroup.range_subtype]; exact hPg),
          Subgroup.card_map_of_injective (MulAut.conj g).injective]
      calc Nat.card (P : Subgroup G) = _ := h1.symm
        _ ≤ Nat.card (S' : Subgroup C₀) := Subgroup.card_le_of_le hS'
        _ = Nat.card (S : Subgroup C₀) := by
          rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
        _ = Nat.card Ps := (Subgroup.card_map_of_injective C₀.subtype_injective).symm
  let Ps' : Sylow p G := Sylow.ofCard Ps (by rw [hPscard, Sylow.card_eq_multiplicity])
  have hPs'coe : (Ps' : Subgroup G) = Ps := rfl
  obtain ⟨g', hg'⟩ := MulAction.exists_smul_eq G P Ps'
  have hPsmap : Ps = (P : Subgroup G).map (MulAut.conj g').toMonoidHom := by
    rw [← hPs'coe, ← hg', Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hWscard : Nat.card (omegaZ Ps p) = p := by
    rw [hPsmap, ← map_omegaZ (MulAut.conj g') (P : Subgroup G) p,
      Subgroup.card_map_of_injective (MulAut.conj g').injective, hWcard]
  have he₀Ws : e₀ ∈ omegaZ Ps p :=
    ⟨hP₀Ps he₀P₀, fun y hy => (Subgroup.mem_centralizer_singleton_iff.mp (hPsC₀ hy)).symm, he₀p⟩
  have hWse₀ : omegaZ Ps p = Subgroup.zpowers e₀ :=
    (Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr he₀Ws)
      (by rw [hWscard, Nat.card_zpowers, he₀o])).symm
  have hPsN₀ : Ps ≤ Subgroup.normalizer (P₀ : Set G) :=
    le_normalizer_of_card_eq_mul hP₀Ps hPsp (by rw [hPscard, hcardP₀])
  have hPsEs : Ps ≤ Subgroup.normalizer (Es : Set G) :=
    hPsN₀.trans normalizer_le_normalizer_omegaZ
  have : IsElementaryAbelian p Es := isElementaryAbelian_omegaZ
  set NE := Subgroup.normalizer (Es : Set G) with hNEdef
  set X := (conjHom Es).range with hXdef
  set ψ : NE →* X := (conjHom Es).rangeRestrict
  have hψ : Function.Surjective ψ := (conjHom Es).rangeRestrict_surjective
  have hNEs : Group.IsSolvable NE := h.isSolvable_normalizer_of_isPGroup_pi hp3 hpq hEsp hEs1
  have hXs : Group.IsSolvable X := Group.isSolvable_of_surjective hψ
  have h8 : ¬ 8 ∣ Nat.card NE := h.not_eight_dvd_card_normalizer_of_pi hp3 hpq hEsp hEs1
  have hXdvd : Nat.card X ∣ Nat.card NE := by
    have := ψ.ker.card_mul_index
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hψ, Subgroup.card_top] at this
    exact ⟨_, by rw [← this, mul_comm]⟩
  have hkerodd : ¬ 2 ∣ Nat.card ψ.ker := by
    intro h2
    obtain ⟨n, hn⟩ := exists_prime_orderOf_dvd_card' (G := ψ.ker) 2 h2
    have hn' : ((n : NE) : G) ∈ Subgroup.centralizer (Es : Set G) := by
      have : conjHom Es (n : NE) = 1 := by
        have := n.2
        rw [MonoidHom.mem_ker] at this
        exact congrArg Subtype.val this
      exact (conjHom_eq_one_iff Es n).mp this
    have hno : orderOf ((n : NE) : G) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hn]
    apply hEsnc
    refine h.isCyclic_of_le_centralizer_pi hp3 hpq hEsp hno fun x hx => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hn' x hx)
  have hXp : ∀ S : Sylow p X, (S : Subgroup X) ≤ pCore p X := by
    refine sylow_le_pCore_of_le_mulAut' (A := Es) hEscard (by omega) hXs ?_
    rintro R (hR2 | hR3) hRn
    ·
      have hR8 : ¬ 8 ∣ Nat.card R := fun h8' =>
        h8 ((h8'.trans (Subgroup.card_subgroup_dvd_card R)).trans hXdvd)
      intro a ha b hb
      have := mul_comm_of_not_eight_dvd hR2 hR8 ⟨a, ha⟩ ⟨b, hb⟩
      exact congrArg Subtype.val this
    ·
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      set M := R ⊔ pCore p X
      set M₁ := M.comap ψ
      have hM₁n : M₁.Normal := hRn.comap ψ
      set MG : Subgroup G := M₁.map NE.subtype
      have hTMG : c.T₀ ≤ Subgroup.normalizer (MG : Set G) := by
        intro τ hτ
        refine map_normalizer_le M₁ ⟨⟨τ, hTEs hτ⟩, ?_, rfl⟩
        have := hM₁n
        rw [Subgroup.normalizer_eq_top]
        exact Subgroup.mem_top _
      have hMcard : Nat.card M = Nat.card R * Nat.card (pCore p X) := by
        refine card_sup_eq_mul_of_disjoint (fun r _ => Subgroup.le_normalizer_of_normal
          (Subgroup.mem_top r)) ?_
        apply Subgroup.disjoint_of_coprime_natCard
        obtain ⟨a, ha⟩ := hR3.exists_card_eq
        obtain ⟨b, hb⟩ := (pCore_isPGroup (p := p) (G := X)).exists_card_eq
        rw [ha, hb]
        exact Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_three hp.out).mpr (by omega))
      have hMGcard : Nat.card MG = Nat.card R * Nat.card (pCore p X) * Nat.card ψ.ker := by
        rw [Subgroup.card_map_of_injective NE.subtype_injective, card_comap_of_surjective hψ,
          hMcard]
      have hMG2 : ¬ 2 ∣ Nat.card MG := by
        rw [hMGcard]
        intro h2
        rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h2 | h2
        · rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h2 | h2
          · obtain ⟨a, ha⟩ := hR3.exists_card_eq
            rw [ha] at h2
            have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two Nat.prime_three).mp
              (Nat.prime_two.dvd_of_dvd_pow h2)
            omega
          · obtain ⟨b, hb⟩ := (pCore_isPGroup (p := p) (G := X)).exists_card_eq
            rw [hb] at h2
            have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.out).mp
              (Nat.prime_two.dvd_of_dvd_pow h2)
            omega
        · exact hkerodd h2
      obtain ⟨S₃, hS₃⟩ := exists_sylow_normalized_of_coprime c.isPGroup_T₀ hTMG hMG2 3
      have hS₃bot := h.eq_bot_of_isPGroup_three_of_le_normalizer hp3 (S₃.isPGroup'.map _)
        c.isPGroup_T₀ (by rw [c.isKleinFour_T₀.card_four]) hS₃
      have hS₃1 : Nat.card (S₃ : Subgroup MG) = 1 := by
        rw [← Subgroup.card_map_of_injective MG.subtype_injective, hS₃bot, Subgroup.card_bot]
      rw [Sylow.card_eq_multiplicity] at hS₃1
      have h3MG : ¬ 3 ∣ Nat.card MG := by
        intro h3
        have := (Nat.Prime.factorization_pos_of_dvd Nat.prime_three Nat.card_pos.ne' h3)
        have : 3 ^ (Nat.card MG).factorization 3 ≠ 1 := (Nat.one_lt_pow this.ne' (by norm_num)).ne'
        exact this hS₃1
      have hR1 : Nat.card R = 1 := by
        obtain ⟨a, ha⟩ := hR3.exists_card_eq
        rcases a with _ | a
        · rw [ha, pow_zero]
        · exfalso
          apply h3MG
          rw [hMGcard, ha]
          exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow_self 3 (by omega)) _) _
      intro a ha b hb
      have hRb : R = ⊥ := Subgroup.card_eq_one.mp hR1
      rw [hRb, Subgroup.mem_bot] at ha hb
      rw [ha, hb]
  have himage : ∀ {H : Subgroup G}, IsPGroup p H → (hHN : H ≤ NE) →
      ∀ x (hx : x ∈ H), ψ ⟨x, hHN hx⟩ ∈ pCore p X := by
    intro H hH hHN x hx
    have hHp : IsPGroup p ((H.subgroupOf NE).map ψ) :=
      (hH.comap_subtype (K := NE)).map ψ
    exact le_pCore_of_isPGroup hXp hHp ⟨⟨x, hHN hx⟩, hx, rfl⟩
  have hYp : IsPGroup p ((pCore p X).map X.subtype) := pCore_isPGroup.map _
  have hEs1' : 1 < Nat.card Es := by
    rw [Finite.one_lt_card_iff_nontrivial]
    exact ⟨⟨⟨e₀, he₀Es⟩, 1, fun h0 => he₀1 (congrArg Subtype.val h0)⟩⟩
  obtain ⟨a, ha1, hafix⟩ := exists_ne_one_fixed hEsp hEs1' hYp
  have hfixG : ∀ {H : Subgroup G}, IsPGroup p H → (hHN : H ≤ NE) → ∀ x ∈ H,
      x * (a : G) = (a : G) * x := by
    intro H hH hHN x hx
    have hmem : (ψ ⟨x, hHN hx⟩ : MulAut Es) ∈ (pCore p X).map X.subtype :=
      ⟨_, himage hH hHN x hx, rfl⟩
    have := congrArg Subtype.val (hafix _ hmem)
    change ((conjHom Es ⟨x, hHN hx⟩ a : Es) : G) = a at this
    rw [conjHom_apply_coe] at this
    calc x * (a : G) = (x * a * x⁻¹) * x := by group
      _ = (a : G) * x := by rw [this]
  have haP : (a : G) ∈ (P : Subgroup G) := hP₀P (hEsP₀ a.2)
  have haW : (a : G) ∈ W := ⟨haP, fun y hy => (hfixG P.isPGroup' hPEs y hy).symm,
    hEsexp _ a.2⟩
  have haWs : (a : G) ∈ omegaZ Ps p := ⟨hP₀Ps (hEsP₀ a.2),
    fun y hy => (hfixG hPsp hPsEs y hy).symm, hEsexp _ a.2⟩
  rw [hWse₀] at haWs
  exact ha1 (Subtype.ext (hdisj _ haWs haW))

end JTHyp

end CFSG.Walter.JT
