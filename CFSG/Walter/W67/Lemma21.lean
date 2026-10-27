module

public import CFSG.Walter.W67.Statements
public import CFSG.Walter.W67.PSL2Aux
public import CFSG.Walter.JRFacts

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups
open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

namespace Hyp

variable (h : Hyp G)

theorem odd_p : Odd h.p := (Fact.out : h.p.Prime).odd_of_ne_two h.p_ne_two

theorem J_mul_J : h.J * h.J = 1 := by
  rw [← pow_two, ← h.orderOf_J, pow_orderOf_eq_one]

theorem J_ne_one : h.J ≠ 1 := fun h1 => by
  have := h.orderOf_J
  rw [h1, orderOf_one] at this
  omega

theorem J_inv : h.J⁻¹ = h.J := inv_eq_of_mul_eq_one_right h.J_mul_J

theorem J_mem_H : h.J ∈ h.H := Subgroup.mem_centralizer_singleton_iff.mpr rfl

theorem K_le_H : h.K ≤ h.H := h.le_centralizer

theorem mem_H_iff {x : G} : x ∈ h.H ↔ x * h.J = h.J * x :=
  Subgroup.mem_centralizer_singleton_iff

theorem commute_J {x : G} (hx : x ∈ h.H) : x * h.J = h.J * x := h.mem_H_iff.mp hx

theorem conj_mem_K {x : G} (hx : x ∈ h.H) {k : G} (hk : k ∈ h.K) : x * k * x⁻¹ ∈ h.K :=
  (Subgroup.normal_subgroupOf_iff h.K_le_H).mp h.normal k x hk hx

theorem H_le_normalizer : h.H ≤ Subgroup.normalizer (h.K : Set G) := fun _ hx =>
  JT.mem_normalizer_of_conj_mem fun _ hk => h.conj_mem_K hx hk

theorem eq_one_of_mem_K {x : G} (hx : x ∈ h.K) (hc : ∀ k ∈ h.K, x * k = k * x) : x = 1 :=
  PSL2Sub.eq_one_of_commute h.iso hx hc

theorem J_not_mem_K : h.J ∉ h.K := fun hJ =>
  h.J_ne_one (h.eq_one_of_mem_K hJ fun _ hk => (h.commute_J (h.K_le_H hk)).symm)

theorem J_mem_CK : h.J ∈ h.CK :=
  ⟨h.J_mem_H, Subgroup.mem_centralizer_iff.mpr fun _ hk => h.commute_J (h.K_le_H hk)⟩

theorem CK_le_H : h.CK ≤ h.H := inf_le_left

theorem CK_le_centralizer : h.CK ≤ Subgroup.centralizer (h.K : Set G) := inf_le_right

theorem K_inf_CK : h.K ⊓ h.CK = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  refine h.eq_one_of_mem_K hx.1 fun k hk => ?_
  exact (Subgroup.mem_centralizer_iff.mp hx.2.2 k hk).symm

theorem isPGroup_zpowers_J : IsPGroup 2 (Subgroup.zpowers h.J) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.orderOf_J, pow_one])

theorem card_zpowers_J : Nat.card (Subgroup.zpowers h.J) = 2 := by
  rw [Nat.card_zpowers, h.orderOf_J]

include h in
theorem card_le_eight {W : Subgroup G} (hW : IsPGroup 2 W) : Nat.card W ≤ 8 := by
  obtain ⟨S, hS⟩ := hW.exists_le_sylow
  rw [← h.card_sylow S]
  exact Subgroup.card_le_of_le hS

include h in
theorem isMulCommutative_of_isPGroup {W : Subgroup G} (hW : IsPGroup 2 W) :
    IsMulCommutative W := by
  obtain ⟨S, hS⟩ := hW.exists_le_sylow
  have := h.abelian_sylow S
  exact ⟨⟨fun a b => Subtype.ext (by
    have hab := congrArg Subtype.val (this.is_comm.comm ⟨a, hS a.2⟩ ⟨b, hS b.2⟩)
    exact hab)⟩⟩

theorem card_zpowers_J_sup {W : Subgroup G} (hWK : W ≤ h.K) :
    Nat.card (Subgroup.zpowers h.J ⊔ W : Subgroup G) = 2 * Nat.card W := by
  have hc : ∀ x ∈ Subgroup.zpowers h.J, ∀ y ∈ W, x * y = y * x := by
    intro x hx y hy
    have hyH : y ∈ h.H := h.K_le_H (hWK hy)
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((Commute.zpow_left (h.commute_J hyH).symm n)).eq
  have hd : Subgroup.zpowers h.J ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases eq_one_or_eq_of_mem_zpowers h.orderOf_J hx.1 with h1 | h1
    · exact h1
    · exact absurd (hWK (h1 ▸ hx.2)) h.J_not_mem_K
  obtain ⟨hcard, -⟩ := card_sup_mul_card_inf_of_commute _ _ hc
  rw [hd, Subgroup.card_bot, mul_one, h.card_zpowers_J] at hcard
  exact hcard

theorem mod_eight : h.q % 8 = 3 ∨ h.q % 8 = 5 :=
  PSL2Sub.mod_eight h.iso h.odd_p h.f_pos fun _ _ hP => h.isMulCommutative_of_isPGroup hP

theorem odd_card_F : Odd (Nat.card h.F) := odd_card_oddPart _

theorem F_le_CK : h.F ≤ h.CK := oddPart_le _

theorem F_le_H : h.F ≤ h.H := h.F_le_CK.trans h.CK_le_H

end Hyp

theorem Frame.nonempty : S_Frame_nonempty := by
  intro G _ _ h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hPK, hP2, hP4, hPmax⟩ := PSL2Sub.exists_sylow h.iso h.odd_p h.f_pos
  have hPN : (Subgroup.zpowers h.J) ≤ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.zpowers_le]
    exact JT.mem_normalizer_of_conj_mem fun x hx => by
      rw [← h.commute_J (h.K_le_H (hPK hx)), mul_inv_cancel_right]
      exact hx
  have hJP2 : IsPGroup 2 (Subgroup.zpowers h.J ⊔ P : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' h.isPGroup_zpowers_J hP2 hPN
  obtain ⟨S, hS⟩ := hJP2.exists_le_sylow
  have hcardJP := h.card_zpowers_J_sup hPK
  have hP4' : Nat.card P = 4 := by
    have := h.card_le_eight hJP2
    omega
  refine ⟨⟨S, hS (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)), ?_⟩⟩
  have hPle : P ≤ (S : Subgroup G) ⊓ h.K := le_inf (le_sup_right.trans hS) hPK
  have hSK2 : IsPGroup 2 ((S : Subgroup G) ⊓ h.K : Subgroup G) := S.isPGroup'.to_le inf_le_left
  have hdvd := hPmax _ inf_le_right hSK2
  have hle := Subgroup.card_le_of_le hPle
  have hpos : 0 < Nat.card ((S : Subgroup G) ⊓ h.K : Subgroup G) := Nat.card_pos
  rw [hP4'] at hdvd hle
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

namespace Frame

variable {h : Hyp G} (fr : Frame h)

theorem T_le_K : fr.T ≤ h.K := inf_le_right

theorem T_le_S : fr.T ≤ (fr.S : Subgroup G) := inf_le_left

theorem isPGroup_T : IsPGroup 2 fr.T := fr.S.isPGroup'.to_le inf_le_left

theorem comm_of_mem_S {x y : G} (hx : x ∈ (fr.S : Subgroup G)) (hy : y ∈ (fr.S : Subgroup G)) :
    x * y = y * x :=
  congrArg Subtype.val ((h.abelian_sylow fr.S).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem S_le_H : (fr.S : Subgroup G) ≤ h.H := fun _ hx =>
  h.mem_H_iff.mpr (fr.comm_of_mem_S hx fr.J_mem)

theorem S_le_CS : (fr.S : Subgroup G) ≤ fr.CS := fun _ hx =>
  Subgroup.mem_centralizer_iff.mpr fun _ hy => fr.comm_of_mem_S hy hx

theorem CS_le_H : fr.CS ≤ h.H := fun _ hx =>
  h.mem_H_iff.mpr ((Subgroup.mem_centralizer_iff.mp hx _ fr.J_mem).symm)

theorem CS_le_centralizer_T : fr.CS ≤ Subgroup.centralizer (fr.T : Set G) :=
  Subgroup.centralizer_le fr.T_le_S

theorem isKleinFour_T : IsKleinFour fr.T :=
  PSL2Sub.isKleinFour_of_card h.iso h.odd_p h.f_pos h.mod_eight fr.T_le_K fr.card_T

theorem J_not_mem_T : h.J ∉ fr.T := fun hJ => h.J_not_mem_K hJ.2

theorem card_S : Nat.card (fr.S : Subgroup G) = 8 := h.card_sylow fr.S

theorem zpowers_J_sup_T : Subgroup.zpowers h.J ⊔ fr.T = fr.S := by
  have hle : Subgroup.zpowers h.J ⊔ fr.T ≤ fr.S :=
    sup_le ((Subgroup.zpowers_le).mpr fr.J_mem) fr.T_le_S
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [fr.card_S, h.card_zpowers_J_sup fr.T_le_K, fr.card_T]

theorem isInternalDirectProduct_S :
    JT.IsInternalDirectProduct (Subgroup.zpowers h.J) fr.T fr.S := by
  refine ⟨fr.zpowers_J_sup_T, ?_, ?_⟩
  · rw [Subgroup.disjoint_def]
    intro x hx hxT
    rcases eq_one_or_eq_of_mem_zpowers h.orderOf_J hx with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hxT) fr.J_not_mem_T
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.mpr fun y hy => h.commute_J (h.K_le_H hy.2)

theorem mul_self_of_mem_S {x : G} (hx : x ∈ (fr.S : Subgroup G)) : x * x = 1 := by
  rw [← fr.zpowers_J_sup_T] at hx
  have hTN : Subgroup.zpowers h.J ≤ Subgroup.normalizer (fr.T : Set G) := by
    rw [Subgroup.zpowers_le]
    exact JT.mem_normalizer_of_conj_mem fun y hy => by
      rw [← h.commute_J (h.K_le_H hy.2), mul_inv_cancel_right]
      exact hy
  rw [sup_comm] at hx
  obtain ⟨t, ht, j, hj, rfl⟩ := (mem_sup_iff_of_le_normalizer hTN).mp hx
  have htt : t * t = 1 := JT.mul_self_of_isKleinFour fr.isKleinFour_T ht
  have hjj : j * j = 1 := by
    rcases eq_one_or_eq_of_mem_zpowers h.orderOf_J hj with rfl | rfl
    · exact mul_one 1
    · exact h.J_mul_J
  have hc : j * t = t * j := by
    rcases eq_one_or_eq_of_mem_zpowers h.orderOf_J hj with rfl | rfl
    · rw [one_mul, mul_one]
    · exact (h.commute_J (h.K_le_H ht.2)).symm
  calc t * j * (t * j) = t * (j * t) * j := by group
    _ = t * (t * j) * j := by rw [hc]
    _ = (t * t) * (j * j) := by group
    _ = 1 := by rw [htt, hjj, one_mul]

theorem isElementaryAbelian_S : IsElementaryAbelian 2 (fr.S : Subgroup G) := by
  have := h.abelian_sylow fr.S
  refine ⟨Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, pow_two]
  exact fr.mul_self_of_mem_S x.2

theorem H_inf_centralizer_T : h.H ⊓ Subgroup.centralizer (fr.T : Set G) = fr.CS := by
  apply le_antisymm
  · rintro x ⟨hxH, hxT⟩
    have hle : Subgroup.zpowers h.J ⊔ fr.T ≤ Subgroup.centralizer ({x} : Set G) := by
      refine sup_le ((Subgroup.zpowers_le).mpr ?_) fun t ht => ?_
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (h.commute_J hxH).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hxT t ht)
    rw [fr.zpowers_J_sup_T] at hle
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hs)
  · exact le_inf fr.CS_le_H fr.CS_le_centralizer_T

theorem isInternalDirectProduct_CS :
    JT.IsInternalDirectProduct (fr.S : Subgroup G) fr.E fr.CS ∧
      ∀ y ∈ fr.CS, Odd (orderOf y) → y ∈ fr.E := by
  refine isInternalDirectProduct_oddPart fr.S_le_CS fr.S.isPGroup' ?_ ?_
  · intro h2
    exact fr.S.not_dvd_index (h2.trans (Subgroup.relIndex_dvd_index_of_le fr.S_le_CS))
  · intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (Subgroup.mem_centralizer_iff.mp hc s hs).symm

theorem E_le_CS : fr.E ≤ fr.CS := oddPart_le _

theorem odd_card_E : Odd (Nat.card fr.E) := odd_card_oddPart _

theorem E_le_H : fr.E ≤ h.H := fr.E_le_CS.trans fr.CS_le_H

theorem mem_E_of_odd {y : G} (hy : y ∈ fr.CS) (hodd : Odd (orderOf y)) : y ∈ fr.E :=
  fr.isInternalDirectProduct_CS.2 y hy hodd

include fr in
theorem card_le_two_of_le_CK {W : Subgroup G} (hW : W ≤ h.CK) (hW2 : IsPGroup 2 W) :
    Nat.card W ≤ 2 := by
  have hc : ∀ x ∈ fr.T, ∀ y ∈ W, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp (hW hy).2 x hx.2
  have hd : fr.T ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ h.K ⊓ h.CK := ⟨hx.1.2, hW hx.2⟩
    rw [h.K_inf_CK] at this
    exact this
  have hWN : W ≤ Subgroup.normalizer (fr.T : Set G) := fun y hy =>
    JT.mem_normalizer_of_conj_mem fun x hx => by
      rw [← hc x hx y hy, mul_inv_cancel_right]
      exact hx
  have h2 : IsPGroup 2 (fr.T ⊔ W : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' fr.isPGroup_T hW2 hWN
  obtain ⟨hcard, -⟩ := card_sup_mul_card_inf_of_commute _ _ hc
  rw [hd, Subgroup.card_bot, mul_one, fr.card_T] at hcard
  have := h.card_le_eight h2
  omega

include fr in
theorem isInternalDirectProduct_CK :
    JT.IsInternalDirectProduct (Subgroup.zpowers h.J) h.F h.CK ∧
      ∀ y ∈ h.CK, Odd (orderOf y) → y ∈ h.F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJCK : Subgroup.zpowers h.J ≤ h.CK := (Subgroup.zpowers_le).mpr h.J_mem_CK
  refine isInternalDirectProduct_oddPart hJCK h.isPGroup_zpowers_J ?_ ?_
  · rintro ⟨k, hk⟩
    have hcard : Nat.card h.CK = 2 * (Subgroup.zpowers h.J).relIndex h.CK := by
      have := ((Subgroup.zpowers h.J).subgroupOf h.CK).card_mul_index
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJCK).toEquiv, h.card_zpowers_J] at this
      exact this.symm
    have h4 : 2 ^ 2 ∣ Nat.card h.CK := by
      rw [hcard]
      change 2 ^ 2 ∣ 2 * ((Subgroup.zpowers h.J).subgroupOf h.CK).index
      rw [hk]
      exact ⟨k, by ring⟩
    obtain ⟨W, hW⟩ := Sylow.exists_subgroup_card_pow_prime (G := h.CK) 2 h4
    have hW2 : IsPGroup 2 (W.map h.CK.subtype) := (IsPGroup.of_card hW).map _
    have := fr.card_le_two_of_le_CK (Subgroup.map_subtype_le W) hW2
    rw [Subgroup.card_map_of_injective h.CK.subtype_injective, hW] at this
    omega
  · rw [Subgroup.zpowers_le]
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (h.commute_J (h.CK_le_H hy))

include fr in
theorem mem_F_of_odd {y : G} (hy : y ∈ h.CK) (hodd : Odd (orderOf y)) : y ∈ h.F :=
  fr.isInternalDirectProduct_CK.2 y hy hodd

include fr in
theorem conj_mem_F {y x : G} (hy : y ∈ h.H) (hx : x ∈ h.F) : y * x * y⁻¹ ∈ h.F := by
  have hxCK := h.F_le_CK hx
  refine fr.mem_F_of_odd ⟨h.H.mul_mem (h.H.mul_mem hy hxCK.1) (h.H.inv_mem hy),
    Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩ ?_
  · have hk' : y⁻¹ * k * y⁻¹⁻¹ ∈ h.K := h.conj_mem_K (h.H.inv_mem hy) hk
    have hc := Subgroup.mem_centralizer_iff.mp hxCK.2 _ hk'
    calc k * (y * x * y⁻¹) = y * ((y⁻¹ * k * y⁻¹⁻¹) * x) * y⁻¹ := by group
      _ = y * (x * (y⁻¹ * k * y⁻¹⁻¹)) * y⁻¹ := by rw [hc]
      _ = y * x * y⁻¹ * k := by group
  · rw [orderOf_conj_mul]
    exact odd_orderOf_of_mem_oddPart hx

theorem F_le_E : h.F ≤ fr.E := by
  intro x hx
  have hxCK := h.F_le_CK hx
  refine fr.mem_E_of_odd ?_ (odd_orderOf_of_mem_oddPart hx)
  rw [← fr.H_inf_centralizer_T]
  exact ⟨hxCK.1, Subgroup.centralizer_le fr.T_le_K hxCK.2⟩

theorem F_normal_E : (h.F.subgroupOf fr.E).Normal :=
  (Subgroup.normal_subgroupOf_iff fr.F_le_E).mpr fun _ _ hx hy => fr.conj_mem_F (fr.E_le_H hy) hx

theorem E_inf_centralizer_K : fr.E ⊓ Subgroup.centralizer (h.K : Set G) = h.F := by
  apply le_antisymm
  · rintro x ⟨hxE, hxK⟩
    exact fr.mem_F_of_odd ⟨fr.E_le_H hxE, hxK⟩ (odd_orderOf_of_mem_oddPart hxE)
  · exact le_inf fr.F_le_E (h.F_le_CK.trans h.CK_le_centralizer)

theorem K_inf_E : h.K ⊓ fr.E = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxK, hxE⟩
  have hxT : x ∈ h.K ⊓ Subgroup.centralizer (fr.T : Set G) :=
    ⟨hxK, fr.CS_le_centralizer_T (fr.E_le_CS hxE)⟩
  rw [PSL2Sub.inf_centralizer_eq h.iso h.odd_p h.f_pos fr.T_le_K fr.isKleinFour_T] at hxT
  exact eq_one_of_odd_of_isPGroup fr.isPGroup_T hxT (odd_orderOf_of_mem_oddPart hxE)

theorem CS_le_normalizer_T : fr.CS ≤ h.H ⊓ Subgroup.normalizer (fr.T : Set G) :=
  le_inf fr.CS_le_H (fr.CS_le_centralizer_T.trans (Subgroup.centralizer_le_normalizer _))

theorem le_centralizer_T_of_isPGroup {P : Subgroup G}
    (hPN : P ≤ Subgroup.normalizer (fr.T : Set G)) (hP : IsPGroup 2 P) :
    P ≤ Subgroup.centralizer (fr.T : Set G) := by
  have h2 : IsPGroup 2 (fr.T ⊔ P : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' fr.isPGroup_T hP hPN
  have hab := h.isMulCommutative_of_isPGroup h2
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact congrArg Subtype.val (hab.is_comm.comm ⟨y, Subgroup.mem_sup_left hy⟩
    ⟨x, Subgroup.mem_sup_right hx⟩)

theorem index_CS_and_normalizer_T :
    (fr.CS.subgroupOf (h.H ⊓ Subgroup.normalizer (fr.T : Set G))).index = 3 ∧
      h.H ⊓ Subgroup.normalizer (fr.T : Set G) =
        (h.K ⊓ Subgroup.normalizer (fr.T : Set G)) ⊔ fr.CS := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := h.H ⊓ Subgroup.normalizer (fr.T : Set G) with hNdef
  set T := fr.T
  have hT := fr.isKleinFour_T
  let := JT.conjAct N T inf_le_right
  let φ : N →* MulAut T := MulDistribMulAction.toMulAut N T
  have hφ : ∀ (n : N) (t : T), ((φ n t : T) : G) = n * t * (n : G)⁻¹ := fun _ _ => rfl
  have hker : φ.ker = fr.CS.subgroupOf N := by
    ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← fr.H_inf_centralizer_T]
    constructor
    · intro hn
      refine ⟨n.2.1, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
      have := congrArg Subtype.val (DFunLike.congr_fun hn ⟨t, ht⟩)
      rw [hφ] at this
      change (n : G) * t * (n : G)⁻¹ = t at this
      calc t * n = ((n : G) * t * (n : G)⁻¹) * n := by rw [this]
        _ = n * t := by group
    · rintro ⟨-, hnC⟩
      ext t
      rw [hφ]
      change (n : G) * t * (n : G)⁻¹ = t
      rw [← Subgroup.mem_centralizer_iff.mp hnC t t.2, mul_inv_cancel_right]
  have hidx : (fr.CS.subgroupOf N).index = Nat.card φ.range := by
    rw [← hker, Subgroup.index_ker]
  have hdvd6 : Nat.card φ.range ∣ 6 := by
    rw [← JT.PSL2Facts.card_mulAut_of_isKleinFour T]
    exact Subgroup.card_subgroup_dvd_card _
  have hodd : ¬ 2 ∣ Nat.card φ.range := by
    rw [← hidx]
    intro h2
    obtain ⟨P⟩ : Nonempty (Sylow 2 N) := inferInstance
    have hPC : (P : Subgroup N) ≤ fr.CS.subgroupOf N := by
      intro x hx
      rw [Subgroup.mem_subgroupOf, ← fr.H_inf_centralizer_T]
      refine ⟨x.2.1, ?_⟩
      have hle := fr.le_centralizer_T_of_isPGroup (P := (P : Subgroup N).map N.subtype)
        ((Subgroup.map_subtype_le _).trans inf_le_right) (P.isPGroup'.map _)
      exact hle ⟨x, hx, rfl⟩
    exact P.not_dvd_index (h2.trans (Subgroup.index_dvd_of_le hPC))
  have h12 := PSL2Sub.card_inf_normalizer h.iso h.odd_p h.f_pos h.mod_eight fr.T_le_K hT
  obtain ⟨a, haKN, haC⟩ : ∃ a ∈ h.K ⊓ Subgroup.normalizer (T : Set G),
      a ∉ Subgroup.centralizer (T : Set G) := by
    by_contra hcon
    push Not at hcon
    have hle : h.K ⊓ Subgroup.normalizer (T : Set G) ≤ h.K ⊓ Subgroup.centralizer (T : Set G) :=
      fun x hx => ⟨hx.1, hcon x hx⟩
    rw [PSL2Sub.inf_centralizer_eq h.iso h.odd_p h.f_pos fr.T_le_K hT] at hle
    have := Subgroup.card_le_of_le hle
    rw [h12, fr.card_T] at this
    omega
  have haN : a ∈ N := ⟨h.K_le_H haKN.1, haKN.2⟩
  have hφa : φ ⟨a, haN⟩ ≠ 1 := by
    intro h1
    have : (⟨a, haN⟩ : N) ∈ φ.ker := h1
    rw [hker, Subgroup.mem_subgroupOf] at this
    exact haC (fr.CS_le_centralizer_T this)
  have hne1 : Nat.card φ.range ≠ 1 := by
    intro h1
    have := Subgroup.card_eq_one.mp h1
    have hmem : φ ⟨a, haN⟩ ∈ φ.range := ⟨_, rfl⟩
    rw [this] at hmem
    exact hφa hmem
  have h3 : Nat.card φ.range = 3 := by
    have hpos : 0 < Nat.card φ.range := Nat.card_pos
    have hle : Nat.card φ.range ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd6
    interval_cases hc : Nat.card φ.range <;> simp_all
  refine ⟨hidx.trans h3, ?_⟩
  apply le_antisymm
  · intro n hn
    have : Fact (Nat.Prime (Nat.card φ.range)) := ⟨by rw [h3]; exact Nat.prime_three⟩
    set A : Subgroup φ.range := Subgroup.zpowers ⟨φ ⟨a, haN⟩, ⟨_, rfl⟩⟩
    have hA : A = ⊤ := by
      rcases Subgroup.eq_bot_or_eq_top_of_prime_card A with hb | ht
      · exfalso
        have hmem : (⟨φ ⟨a, haN⟩, ⟨_, rfl⟩⟩ : φ.range) ∈ A := Subgroup.mem_zpowers _
        rw [hb, Subgroup.mem_bot] at hmem
        exact hφa (congrArg Subtype.val hmem)
      · exact ht
    have hmem : (⟨φ ⟨n, hn⟩, ⟨_, rfl⟩⟩ : φ.range) ∈ A := by rw [hA]; exact Subgroup.mem_top _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hk' : φ (⟨a, haN⟩ ^ k) = φ ⟨n, hn⟩ := by
      have := congrArg Subtype.val hk
      simpa [map_zpow] using this
    have hker' : (⟨a, haN⟩ ^ k)⁻¹ * ⟨n, hn⟩ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hk', inv_mul_cancel]
    rw [hker, Subgroup.mem_subgroupOf] at hker'
    have hn' : n = (a ^ k) * ((a ^ k)⁻¹ * n) := by group
    rw [hn']
    refine mul_mem (Subgroup.mem_sup_left (Subgroup.zpow_mem _ haKN k)) (Subgroup.mem_sup_right ?_)
    simpa using hker'
  · exact sup_le (le_inf_iff.mpr ⟨inf_le_left.trans h.K_le_H, inf_le_right⟩) fr.CS_le_normalizer_T

theorem H_eq_K_sup_normalizer : h.H = h.K ⊔ (h.H ⊓ Subgroup.normalizer (fr.T : Set G)) := by
  apply le_antisymm
  · intro x hx
    set T' := fr.T.map (MulAut.conj x).toMonoidHom
    have hT'K : T' ≤ h.K := by
      rintro _ ⟨t, ht, rfl⟩
      exact h.conj_mem_K hx ht.2
    have hT' : Nat.card T' = 4 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, fr.card_T]
    obtain ⟨k, hkK, hk⟩ := PSL2Sub.exists_conj_of_card_four h.iso h.odd_p h.f_pos h.mod_eight
      fr.T_le_K hT'K fr.card_T hT'
    have hkx : k * x ∈ h.H ⊓ Subgroup.normalizer (fr.T : Set G) := by
      refine ⟨h.H.mul_mem (h.K_le_H hkK) hx, JT.mem_normalizer_of_conj_mem fun t ht => ?_⟩
      have := hk (x * t * x⁻¹) ⟨t, ht, rfl⟩
      have heq : k * x * t * (k * x)⁻¹ = k * (x * t * x⁻¹) * k⁻¹ := by group
      rw [heq]
      exact this
    have : x = k⁻¹ * (k * x) := by group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left (h.K.inv_mem hkK)) (Subgroup.mem_sup_right hkx)
  · exact sup_le h.K_le_H inf_le_left

theorem isInternalDirectProduct_H :
    JT.IsInternalDirectProduct (Subgroup.zpowers h.J) (h.K ⊔ fr.E) h.H := by
  have hEN : fr.E ≤ Subgroup.normalizer (h.K : Set G) := fr.E_le_H.trans h.H_le_normalizer
  refine ⟨?_, ?_, ?_⟩
  · apply le_antisymm
    · exact sup_le ((Subgroup.zpowers_le).mpr h.J_mem_H) (sup_le h.K_le_H fr.E_le_H)
    · rw [fr.H_eq_K_sup_normalizer, fr.index_CS_and_normalizer_T.2,
        fr.isInternalDirectProduct_CS.1.1.symm, ← fr.zpowers_J_sup_T]
      refine sup_le (le_sup_of_le_right le_sup_left) (sup_le ?_ ?_)
      · exact le_sup_of_le_right (inf_le_left.trans le_sup_left)
      · refine sup_le (sup_le le_sup_left (le_sup_of_le_right (fr.T_le_K.trans le_sup_left)))
          (le_sup_of_le_right le_sup_right)
  · rw [Subgroup.disjoint_def]
    intro x hxJ hxKE
    rcases eq_one_or_eq_of_mem_zpowers h.orderOf_J hxJ with h1 | rfl
    · exact h1
    exfalso
    obtain ⟨k, hk, e, he, hke⟩ := (mem_sup_iff_of_le_normalizer hEN).mp hxKE
    have he' : e = k⁻¹ * h.J := by rw [← hke]; group
    have hc : k⁻¹ * h.J = h.J * k⁻¹ := h.commute_J (h.K_le_H (h.K.inv_mem hk))
    obtain ⟨m, hm⟩ := odd_orderOf_of_mem_oddPart he
    have hcomm : Commute k⁻¹ h.J := hc
    have hem : (k⁻¹ * h.J) ^ orderOf e = 1 := by rw [← he']; exact pow_orderOf_eq_one e
    have hJpow : h.J ^ (2 * m + 1) = h.J := by
      rw [pow_succ, pow_mul, sq, h.J_mul_J, one_pow, one_mul]
    rw [hcomm.mul_pow, hm, hJpow] at hem
    have hJ : h.J = ((k⁻¹) ^ (2 * m + 1))⁻¹ := eq_inv_of_mul_eq_one_right hem
    exact h.J_not_mem_K (hJ ▸ h.K.inv_mem (h.K.pow_mem (h.K.inv_mem hk) _))
  · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro y hy
    exact h.commute_J (sup_le h.K_le_H fr.E_le_H hy)

theorem exists_coords :
    ∃ (e' : h.K ≃* PSL(2, GaloisField h.p h.f)) (P₀ : Sylow 2 PSL(2, ZMod h.p)),
      fr.T = ((P₀ : Subgroup PSL(2, ZMod h.p)).map
        (psl2Map (algebraMap (ZMod h.p) (GaloisField h.p h.f)))).map (psl2Emb e') :=
  PSL2Sub.exists_coords h.iso h.odd_p h.f_pos h.mod_eight fr.T_le_K fr.card_T

theorem E_le_normalizer_K : fr.E ≤ Subgroup.normalizer (h.K : Set G) :=
  fr.E_le_H.trans h.H_le_normalizer

theorem conj_eq_fieldAut
    {e' : h.K ≃* PSL(2, GaloisField h.p h.f)} {P₀ : Sylow 2 PSL(2, ZMod h.p)}
    (hT : fr.T = ((P₀ : Subgroup PSL(2, ZMod h.p)).map
      (psl2Map (algebraMap (ZMod h.p) (GaloisField h.p h.f)))).map (psl2Emb e'))
    {x : G} (hx : x ∈ fr.E) :
    ∃ σ : GaloisField h.p h.f ≃+* GaloisField h.p h.f,
      ∀ y, x * psl2Emb e' y * x⁻¹ = psl2Emb e' (psl2FieldAut _ σ y) :=
  PSL2Sub.conj_eq_fieldAut e' h.odd_p h.f_pos hT h.mod_eight (fr.E_le_normalizer_K hx)
    (fr.CS_le_centralizer_T (fr.E_le_CS hx)) (odd_orderOf_of_mem_oddPart hx)

theorem exists_generator_E :
    ∃ g ∈ fr.E, Subgroup.zpowers g ⊔ h.F = fr.E := by
  obtain ⟨e', P₀, hT⟩ := fr.exists_coords
  set F := GaloisField h.p h.f
  let ψ : fr.E →* MulAut PSL(2, F) :=
    (PSL2Sub.conjHom e').comp (Subgroup.inclusion fr.E_le_normalizer_K)
  have hψ : ∀ x : fr.E, ψ x ∈ (psl2FieldAut F).range := by
    intro x
    obtain ⟨σ, hσ⟩ := fr.conj_eq_fieldAut hT x.2
    exact ⟨σ, ((PSL2Sub.conjHom_eq_iff e' _ _).mpr hσ).symm⟩
  have hcyc : IsCyclic (psl2FieldAut F).range := by
    have := isCyclic_ringEquiv_galoisField (p := h.p) (f := h.f)
    exact isCyclic_of_surjective (psl2FieldAut F).rangeRestrict
      (psl2FieldAut F).rangeRestrict_surjective
  have hle : ψ.range ≤ (psl2FieldAut F).range := by
    rintro _ ⟨x, rfl⟩
    exact hψ x
  have : IsCyclic ψ.range := Subgroup.isCyclic_of_le hle
  obtain ⟨⟨_, ⟨x₀, rfl⟩⟩, hg⟩ := IsCyclic.exists_generator (α := ψ.range)
  refine ⟨x₀, x₀.2, le_antisymm (sup_le ((Subgroup.zpowers_le).mpr x₀.2) fr.F_le_E) ?_⟩
  intro x hx
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨ψ ⟨x, hx⟩, ⟨_, rfl⟩⟩)
  have hk' : ψ (x₀ ^ k) = ψ ⟨x, hx⟩ := by
    have := congrArg Subtype.val hk
    simpa [map_zpow] using this
  have hker : ψ ((x₀ ^ k)⁻¹ * ⟨x, hx⟩) = 1 := by
    rw [map_mul, map_inv, hk', inv_mul_cancel]
  set z : fr.E := (x₀ ^ k)⁻¹ * ⟨x, hx⟩
  have hzF : (z : G) ∈ h.F := by
    rw [← fr.E_inf_centralizer_K]
    refine ⟨z.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    obtain ⟨y', rfl⟩ := PSL2Sub.exists_emb_eq e' hy
    have h1 := (PSL2Sub.conjHom_eq_iff e' (Subgroup.inclusion fr.E_le_normalizer_K z) 1).mp hker y'
    change (z : G) * psl2Emb e' y' * (z : G)⁻¹ = psl2Emb e' y' at h1
    calc psl2Emb e' y' * z = ((z : G) * psl2Emb e' y' * (z : G)⁻¹) * z := by rw [h1]
      _ = z * psl2Emb e' y' := by group
  have hx' : x = ((x₀ : G) ^ k) * z := by
    simp only [z, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
    group
  rw [hx']
  exact mul_mem (Subgroup.mem_sup_left (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k))
    (Subgroup.mem_sup_right hzF)

end Frame

theorem lemma_2_1 :
    S_lemma_2_1 := by
  intro G _ _ h fr
  exact ⟨h.mod_eight, fr.isInternalDirectProduct_CK.1, h.odd_card_F, h.K_inf_CK,
    fr.isElementaryAbelian_S, fr.card_S, fr.isInternalDirectProduct_S, fr.H_inf_centralizer_T,
    fr.isInternalDirectProduct_CS.1, fr.F_le_E, fr.F_normal_E, fr.exists_generator_E,
    fr.E_inf_centralizer_K, fr.K_inf_E, fr.isInternalDirectProduct_H⟩

theorem case2_of_E_eq_bot :
    ∀ (G : Type) [Group G] [Finite G] (h : Hyp G) (fr : Frame h), commutator G = ⊤ → fr.E = ⊥ →
      Case2 h := by
  intro G _ _ h fr _ hE
  have hH := fr.isInternalDirectProduct_H.1
  rw [hE, sup_bot_eq] at hH
  refine ⟨⊤, Subgroup.normal_top, by rw [Subgroup.index_top]; exact odd_one, ⟨1, ?_⟩,
    ⟨h.K, le_inf le_top h.K_le_H, h.J_not_mem_K, ?_, ⟨h.iso⟩⟩, h.mod_eight⟩
  · exact eq_top_iff.mpr (le_sup_of_le_right le_sup_left)
  · rw [top_inf_eq]
    exact hH.symm

end CFSG.Walter.W67
