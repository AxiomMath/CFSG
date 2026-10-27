module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem15B

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits CFSG.Quasithin.ASInputs
open scoped Pointwise

theorem mul_eq_one_of_ne_one_ch615 {a b : Multiplicative (ZMod 2)} (ha : a ≠ 1) (hb : b ≠ 1) :
    a * b = 1 := by
  revert a b
  decide

section General

variable {G : Type} [Group G] [Finite G]

theorem extraspecial_facts_ch615 {U Z D : Subgroup G} (hZ2 : Nat.card Z = 2) (hDU : D ≤ U)
    (hZc : ∀ z ∈ Z, ∀ u ∈ U, u * z = z * u)
    (hcomm : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ Z) (hDes : CFSG.IsExtraspecial 2 ↥D) :
    (∃ a ∈ D, ∃ b ∈ D, a * b ≠ b * a) ∧ Z ≤ D ∧ ∀ x ∈ D, x ∈ centerOf U → x ∈ Z := by
  have hDna : ∃ a ∈ D, ∃ b ∈ D, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have := CFSG.IsExtraspecial.quotient_nontrivial 2 ↥D
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥D ⧸ Subgroup.center ↥D)
    induction x using QuotientGroup.induction_on with
    | H a =>
      apply hx
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
      intro b
      exact Subtype.ext (hcon b b.2 a a.2)
  have hZD : Z ≤ D := by
    obtain ⟨a, ha, b, hb, hab⟩ := hDna
    have hc : a * b * a⁻¹ * b⁻¹ ∈ Z := hcomm a (hDU ha) b (hDU hb)
    have hcD : a * b * a⁻¹ * b⁻¹ ∈ D :=
      D.mul_mem (D.mul_mem (D.mul_mem ha hb) (D.inv_mem ha)) (D.inv_mem hb)
    have hc1 : a * b * a⁻¹ * b⁻¹ ≠ 1 := by
      intro h1
      apply hab
      calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
        _ = b * a := by rw [h1, one_mul]
    have hne : Z ⊓ D ≠ ⊥ := fun he => by
      have h2 : a * b * a⁻¹ * b⁻¹ ∈ Z ⊓ D := ⟨hc, hcD⟩
      rw [he, Subgroup.mem_bot] at h2
      exact hc1 h2
    have h1 : 1 < Nat.card ↥(Z ⊓ D) := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
    have h2 : Nat.card ↥(Z ⊓ D) ∣ 2 := hZ2 ▸ Subgroup.card_dvd_of_le inf_le_left
    have h3 : Nat.card ↥(Z ⊓ D) = 2 := by
      have := Nat.le_of_dvd two_pos h2
      omega
    have heq : Z ⊓ D = Z := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hZ2])
    rw [← heq]
    exact inf_le_right
  refine ⟨hDna, hZD, fun x hxD hxZ => ?_⟩
  have hxc : (⟨x, hxD⟩ : ↥D) ∈ Subgroup.center ↥D := Subgroup.mem_center_iff.mpr fun y =>
    Subtype.ext (Subgroup.mem_centralizer_iff.mp hxZ.2 y (hDU y.2))
  have hZc' : Z.subgroupOf D ≤ Subgroup.center ↥D := fun z hz =>
    Subgroup.mem_center_iff.mpr fun y =>
      Subtype.ext (hZc z (Subgroup.mem_subgroupOf.mp hz) y (hDU y.2))
  have hceq : Z.subgroupOf D = Subgroup.center ↥D := by
    apply Subgroup.eq_of_le_of_card_ge hZc'
    rw [CFSG.IsExtraspecial.center_order_p 2 ↥D,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZD).toEquiv, hZ2]
  rw [← hceq] at hxc
  exact Subgroup.mem_subgroupOf.mp hxc

theorem exists_complement_ch615 {U Z D : Subgroup G}
    (hZc : ∀ z ∈ Z, ∀ u ∈ U, u * z = z * u) (hsq : ∀ u ∈ U, u ^ 2 ∈ Z)
    (hcomm : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ Z) (hDU : D ≤ U) (hZD : Z ≤ D)
    (hcenD : ∀ x ∈ D, x ∈ centerOf U → x ∈ Z) :
    ∃ U₀ : Subgroup G, D ≤ U₀ ∧ U₀ ≤ U ∧ U₀ ⊔ centerOf U = U ∧
      ∀ y ∈ U₀, y ∈ centerOf U → y ∈ Z := by
  classical
  obtain ⟨U₀, ⟨hDU₀, hU₀U, hsup⟩, hmin⟩ : ∃ U₀ : Subgroup G,
      (D ≤ U₀ ∧ U₀ ≤ U ∧ U₀ ⊔ centerOf U = U) ∧
      ∀ K : Subgroup G, (D ≤ K ∧ K ≤ U ∧ K ⊔ centerOf U = U) → K ≤ U₀ → U₀ ≤ K := by
    obtain ⟨b, -, hmax⟩ := Finite.exists_le_maximal (α := (Subgroup G)ᵒᵈ)
      (p := fun x => D ≤ OrderDual.ofDual x ∧ OrderDual.ofDual x ≤ U ∧
        OrderDual.ofDual x ⊔ centerOf U = U)
      (a := OrderDual.toDual U) ⟨hDU, le_rfl, sup_eq_left.mpr inf_le_left⟩
    exact ⟨OrderDual.ofDual b, hmax.1, fun K hK hKb => hmax.2 hK hKb⟩
  refine ⟨U₀, hDU₀, hU₀U, hsup, fun y hyU₀ hyZ => ?_⟩
  by_contra hyZ'
  have hcm : CommModCh611 U₀ Z := ⟨fun a ha b hb => hcomm a (hU₀U ha) b (hU₀U hb)⟩
  have hn : (Z.subgroupOf U₀).Normal := ⟨fun x hx g' => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hZc x hx g' (hU₀U g'.2), mul_inv_cancel_right]
    exact hx⟩
  have hQ2 : ∀ q : ↥U₀ ⧸ Z.subgroupOf U₀, q ^ 2 = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using hsq a (hU₀U a.2)
  have hyW : (QuotientGroup.mk ⟨y, hyU₀⟩ : ↥U₀ ⧸ Z.subgroupOf U₀) ∉
      (D.subgroupOf U₀).map (QuotientGroup.mk' (Z.subgroupOf U₀)) := by
    rintro ⟨d, hd, hde⟩
    apply hyZ'
    rw [QuotientGroup.mk'_apply] at hde
    have h1 := QuotientGroup.eq.mp hde
    rw [Subgroup.mem_subgroupOf] at h1
    have hdD : (d : G) ∈ D := Subgroup.mem_subgroupOf.mp hd
    have hyD : y ∈ D := by
      have := D.mul_mem hdD (hZD h1)
      simpa using this
    exact hcenD y hyD hyZ
  obtain ⟨f, hfW, hfy⟩ := exists_hom_sep_ch611 hQ2 hyW
  obtain ⟨K, hK⟩ : ∃ K : Subgroup G,
      K = (f.comp (QuotientGroup.mk' (Z.subgroupOf U₀))).ker.map U₀.subtype := ⟨_, rfl⟩
  have hmemK : ∀ x (hx : x ∈ U₀), x ∈ K ↔ f (QuotientGroup.mk ⟨x, hx⟩) = 1 := by
    intro x hx
    rw [hK, Subgroup.mem_map]
    constructor
    · rintro ⟨x', hx', hx'e⟩
      obtain rfl : x' = ⟨x, hx⟩ := Subtype.ext hx'e
      rwa [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply] at hx'
    · intro h1
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      rwa [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
  have hKU₀ : K ≤ U₀ := hK ▸ Subgroup.map_subtype_le _
  have hDK : D ≤ K := fun d hd => (hmemK d (hDU₀ hd)).mpr
    (hfW _ ⟨⟨d, hDU₀ hd⟩, Subgroup.mem_subgroupOf.mpr hd, rfl⟩)
  have hKsup : K ⊔ centerOf U = U := by
    refine le_antisymm (sup_le (hKU₀.trans hU₀U) inf_le_left) ?_
    refine le_trans hsup.symm.le (sup_le (fun x hx => ?_) le_sup_right)
    by_cases hx1 : f (QuotientGroup.mk ⟨x, hx⟩) = 1
    · exact Subgroup.mem_sup_left ((hmemK x hx).mpr hx1)
    · have hxy : x * y ∈ K := (hmemK _ (U₀.mul_mem hx hyU₀)).mpr (by
        have e : (QuotientGroup.mk ⟨x * y, U₀.mul_mem hx hyU₀⟩ : ↥U₀ ⧸ Z.subgroupOf U₀) =
            QuotientGroup.mk ⟨x, hx⟩ * QuotientGroup.mk ⟨y, hyU₀⟩ := rfl
        rw [e, map_mul]
        exact mul_eq_one_of_ne_one_ch615 hx1 hfy)
      have e : x = (x * y) * y⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hxy)
        (Subgroup.mem_sup_right ((centerOf U).inv_mem hyZ))
  exact hfy ((hmemK y hyU₀).mp (hmin K ⟨hDK, hKU₀.trans hU₀U, hKsup⟩ hKU₀ hyU₀))

theorem isExtraspecial_ch615 {U Z U₀ : Subgroup G} (hZ2 : Nat.card Z = 2) (hZU₀ : Z ≤ U₀)
    (hU₀U : U₀ ≤ U) (hsup : U₀ ⊔ centerOf U = U) (hcap : ∀ y ∈ U₀, y ∈ centerOf U → y ∈ Z)
    (hZc : ∀ z ∈ Z, ∀ u ∈ U, u * z = z * u) (hsq : ∀ u ∈ U, u ^ 2 ∈ Z)
    (hcomm : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ Z)
    (hna : ∃ a ∈ U₀, ∃ b ∈ U₀, a * b ≠ b * a) : CFSG.IsExtraspecial 2 ↥U₀ := by
  have hZUc : ∀ z ∈ centerOf U, ∀ x ∈ U, x * z = z * x := fun z hz x hx =>
    Subgroup.mem_centralizer_iff.mp hz.2 x hx
  have hU₀N : U₀ ≤ Subgroup.normalizer (centerOf U : Set G) := fun x hx =>
    mem_normalizer_of_forall_conj_mem_of_le fun z hz => by
      rw [hZUc z hz x (hU₀U hx), mul_inv_cancel_right]
      exact hz
  have hcoe : ((U₀ ⊔ centerOf U : Subgroup G) : Set G) = (U₀ : Set G) * (centerOf U : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hU₀N
  have hcenter : ∀ x : ↥U₀, x ∈ Subgroup.center ↥U₀ ↔ (x : G) ∈ Z := by
    intro x
    constructor
    · intro hx
      apply hcap x x.2
      refine ⟨hU₀U x.2, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
      have hu' : u ∈ ((U₀ ⊔ centerOf U : Subgroup G) : Set G) := by
        rw [hsup]
        exact hu
      rw [hcoe] at hu'
      obtain ⟨a, ha, c, hc, rfl⟩ := hu'
      have h1 : a * x = x * a := congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨a, ha⟩)
      have h2 : (x : G) * c = c * x := hZUc c hc x (hU₀U x.2)
      calc a * c * x = a * (c * x) := by group
        _ = a * (x * c) := by rw [h2]
        _ = (a * x) * c := by group
        _ = (x * a) * c := by rw [h1]
        _ = x * (a * c) := by group
    · intro hx
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hZc x hx y (hU₀U y.2))
  have hcenter_eq : Subgroup.center ↥U₀ = Z.subgroupOf U₀ := by
    ext x
    rw [hcenter x, Subgroup.mem_subgroupOf]
  have hcard : Nat.card (Subgroup.center ↥U₀) = 2 := by
    rw [hcenter_eq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU₀).toEquiv, hZ2]
  have hQcomm : ∀ x y : ↥U₀ ⧸ Subgroup.center ↥U₀, x * y = y * x := by
    intro x y
    refine QuotientGroup.induction_on x fun a => QuotientGroup.induction_on y fun b => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hcenter]
    have h1 := hcomm _ (U.inv_mem (hU₀U b.2)) _ (U.inv_mem (hU₀U a.2))
    have e : ((a : G) * b)⁻¹ * ((b : G) * a) =
        (b : G)⁻¹ * (a : G)⁻¹ * (b : G)⁻¹⁻¹ * (a : G)⁻¹⁻¹ := by group
    show ((a : G) * b)⁻¹ * ((b : G) * a) ∈ Z
    rw [e]
    exact h1
  have hQsq : ∀ x : ↥U₀ ⧸ Subgroup.center ↥U₀, x * x = 1 := by
    intro x
    refine QuotientGroup.induction_on x fun a => ?_
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, hcenter]
    have := hsq a (hU₀U a.2)
    rw [pow_two] at this
    exact this
  have hnt : Nontrivial (↥U₀ ⧸ Subgroup.center ↥U₀) := by
    obtain ⟨a, ha, b, hb, hab⟩ := hna
    refine ⟨⟨1, QuotientGroup.mk ⟨a, ha⟩, fun he => hab ?_⟩⟩
    have h1 : (⟨a, ha⟩ : ↥U₀) ∈ Subgroup.center ↥U₀ :=
      (QuotientGroup.eq_one_iff _).mp he.symm
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp h1 ⟨b, hb⟩).symm
  have hQmc : IsMulCommutative (↥U₀ ⧸ Subgroup.center ↥U₀) := ⟨⟨hQcomm⟩⟩
  have hEA : CFSG.IsElementaryAbelian 2 (↥U₀ ⧸ Subgroup.center ↥U₀) :=
    { exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
        rw [pow_two]
        exact hQsq x }
  exact
    { center_order_p := hcard
      quotient_elementary_abelian := hEA
      quotient_nontrivial := hnt }

end General

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem not_mem_C_ch615 (h6210 : Stmt6_2_10) (h6211 : Stmt6_2_11) (h6212 : Stmt6_2_12)
    (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) {v : G} (hv : v ∈ V) (hvU : v ∉ uCh611 T L V) :
    v ∉ centralizerMod (zCh611 T) (hCh611 T) (uCh611 T L V) := by
  intro hvC
  obtain ⟨-, -, hCQ⟩ := h6212 G T M L V h
  have hCQ' : centralizerMod (zCh611 T) (hCh611 T) (uCh611 T L V) = pCoreOf 2 (hCh611 T) := hCQ
  have h14 : V ⊓ uCh611 T L V = V ⊓ pCoreOf 2 (hCh611 T) :=
    (stmt6_2_14_of h6210 h6211 h6212 G T M L V h hlt).1
  have : v ∈ V ⊓ pCoreOf 2 (hCh611 T) := ⟨hv, hCQ' ▸ hvC⟩
  rw [← h14] at this
  exact hvU this.2

theorem exists_not_mem_U_ch615 (h6210 : Stmt6_2_10) (h6211 : Stmt6_2_11) (h6212 : Stmt6_2_12)
    (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) : ∃ v ∈ V, v ∉ uCh611 T L V := by
  by_contra hcon
  push Not at hcon
  have h8 : Nat.card ↥(V ⊓ uCh611 T L V) = 2 ^ 3 :=
    (stmt6_2_14_of h6210 h6211 h6212 G T M L V h hlt).2
  have : V ⊓ uCh611 T L V = V := inf_eq_left.mpr hcon
  rw [this, h.natural.card_eq] at h8
  norm_num at h8

theorem exists_extraspecial_ch615 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h626 : Stmt6_2_6) (h6210 : Stmt6_2_10)
    (h6211 : Stmt6_2_11) (h6212 : Stmt6_2_12) (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) :
    ∃ U₀ : Subgroup G, U₀ ≤ uCh611 T L V ∧ uCh611 T L V = centerOf (uCh611 T L V) ⊔ U₀ ∧
      CFSG.IsExtraspecial 2 ↥U₀ ∧ 2 ^ 5 ≤ Nat.card U₀ ∧
      ∃ A : Subgroup G, A ≤ U₀ ∧ IsElemAbelian 2 A ∧ Nat.card A = 2 ^ 3 := by
  have hZ2 : Nat.card (zCh611 T) = 2 := h.card_omega h331 h432 h512 h614 h615
  have hUH : uCh611 T L V ≤ hCh611 T := h.uCh611_le_h h331 h432 h512 h614 h615
  have hZc : ∀ z ∈ zCh611 T, ∀ u ∈ uCh611 T L V, u * z = z * u := fun z hz u hu =>
    (Subgroup.mem_centralizer_iff.mp (hUH hu) z hz).symm
  have hsq : ∀ u ∈ uCh611 T L V, u ^ 2 ∈ zCh611 T := fun u hu =>
    h.sq_mem_ch615 h331 h432 h512 h614 h615 hu
  have hcomm : ∀ a ∈ uCh611 T L V, ∀ b ∈ uCh611 T L V, a * b * a⁻¹ * b⁻¹ ∈ zCh611 T :=
    fun a ha b hb => h.comm_mem_ch615 h331 h432 h512 h614 h615 ha hb
  obtain ⟨v, hv, hvU⟩ := h.exists_not_mem_U_ch615 h6210 h6211 h6212 hlt
  obtain ⟨g, hg, hgk⟩ := h.exists_not_two_ch615 h6210 hv
    (h.not_mem_C_ch615 h6210 h6211 h6212 hlt hv hvU)
  obtain ⟨-, ⟨D, hDX, hXD, hDext, -⟩, -, hOU⟩ :=
    h.two_six_ch615 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hv hg hgk
  obtain ⟨hDes, hD32, E, hED, hEab, hE8⟩ := hDext
  have hD2 : IsPGroup 2 D := IsPGroup.of_card (n := 5) (by rw [hD32])
  have hDU : D ≤ uCh611 T L V := (le_pCoreOf_of_le_normalizer 2 hDX hXD hD2).trans hOU
  obtain ⟨hDna, hZD, hcenD⟩ := extraspecial_facts_ch615 hZ2 hDU hZc hcomm hDes
  obtain ⟨U₀, hDU₀, hU₀U, hsup, hcap⟩ :=
    exists_complement_ch615 hZc hsq hcomm hDU hZD hcenD
  have hna : ∃ a ∈ U₀, ∃ b ∈ U₀, a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hDna
    exact ⟨a, hDU₀ ha, b, hDU₀ hb, hab⟩
  refine ⟨U₀, hU₀U, by rw [sup_comm, hsup],
    isExtraspecial_ch615 hZ2 (hZD.trans hDU₀) hU₀U hsup hcap hZc hsq hcomm hna, ?_,
    E, hED.trans hDU₀, hEab, hE8⟩
  exact (show 2 ^ 5 = Nat.card D by rw [hD32]).trans_le (Subgroup.card_le_of_le hDU₀)

end Hyp6Sec2

end CFSG.Quasithin.H13
