module

public import CFSG.Quasithin.Recognition.RuTypeJ47j
public import CFSG.Quasithin.Recognition.RuTypeJ47f
public import CFSG.Quasithin.Recognition.CertTwoF4AmalgamLocalFinal
public import CFSG.Quasithin.Recognition.RuTypeJ44e
public import CFSG.Quasithin.Recognition.RuTypeJ44f

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Sporadic.Schreier.Tits

namespace J47

theorem twoF4N_le_M
    : twoF4N ≤ twoF4M := extSub_mono titsN_le_titsD

theorem exists_amalgamIso_of_case2F4
    {G : Type} [Group G] [Finite G] {H L2 : Subgroup G} (hCase : Case2F4 H L2) :
    Nonempty ((RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso
      (RankTwoAmalgam.ofSubgroups H L2)) := by
  obtain ⟨⟨Y, _, hTw, T, M₁, M₂, hpair, ⟨iso⟩⟩, -, -, -, hP2⟩ := hCase
  obtain ⟨e⟩ : Nonempty (Y ≃* MulAut CFSG.Open.quasithinTits) := by
    rcases hTw with ⟨-, h⟩ | ⟨h, -, -⟩
    · exact h
    · omega
  let φ : Y ≃* twoF4M := e.trans (twoF4AutEquiv titsOutBound)
  have hpair' := IsYAmalgamPair.map φ hpair
  obtain ⟨ρ, hρ⟩ := exists_mulEquiv_map_sylow twoF4Lattice.isSylowTwoOf_top hpair'.1
  let f : Y ≃* twoF4M := φ.trans ρ
  have hmap : ∀ M : Subgroup Y,
      (M.map φ.toMonoidHom).map ρ.toMonoidHom = M.map f.toMonoidHom := fun M =>
    Subgroup.map_map _ _ _
  have hpairf := IsYAmalgamPair.map ρ hpair'
  rw [hρ, hmap, hmap] at hpairf
  have hlocal : ∀ M : Subgroup Y, (M = M₁ ∨ M = M₂) →
      (M.map f.toMonoidHom = twoF4Lattice.P₁ ∨ M.map f.toMonoidHom = twoF4Lattice.P₂) := by
    intro M hM
    obtain ⟨hmax, hnorm⟩ := (hpairf.2.2 (M.map f.toMonoidHom)).2
      (by rcases hM with rfl | rfl <;> simp)
    exact twoF4Lattice.eq_P₁_or_P₂_of_maxTwoLocal hmax (Subgroup.le_normalizer.trans hnorm)
  have hne : M₁.map f.toMonoidHom ≠ M₂.map f.toMonoidHom := fun h =>
    hpair.2.1 (Subgroup.map_injective f.injective h)
  rcases hlocal M₁ (Or.inl rfl) with h1 | h1 <;> rcases hlocal M₂ (Or.inr rfl) with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  ·
    have h1' : M₁.map (f : Y →* twoF4M) = twoF4H.subgroupOf twoF4M := h1.trans twoF4Lattice_P₁
    have h2' : M₂.map (f : Y →* twoF4M) = twoF4N.subgroupOf twoF4M := h2.trans twoF4Lattice_P₂
    exact ⟨amIsoSymm (amIsoTrans iso (amIsoTrans (ofSubgroupsMapIso f M₁ M₂)
      (amIsoTrans (ofSubgroupsCongr h1' h2')
        (ofSubgroupsSubgroupOfIso twoF4H_le_twoF4M twoF4N_le_M))))⟩
  ·
    exfalso
    let ψ : ↥L2 ≃* ↥twoF4H := (iso.φ2.trans (f.subgroupMap M₂)).trans
      ((MulEquiv.subgroupCongr h2).trans ((MulEquiv.subgroupCongr twoF4Lattice_P₁).trans
        (Subgroup.subgroupOfEquivOfLe twoF4H_le_twoF4M)))
    have := card_pCoreOf_eq_of_mulEquiv ψ
    rw [hP2, card_pCoreOf_twoF4H] at this
    norm_num at this
  · exact absurd (h1.trans h2.symm) hne

end J47

namespace RuDataM

variable {G : Type} [Group G] (M : RuDataM G) [Finite G]

theorem exists_phiG_eq_pow_of_mem_F1 {x : G} (hx : x ∈ M.F1)
    (hx5 : x ^ 5 = 1) : ∃ k : ℕ, M.phiG x = M.phiG M.b5el ^ k := by
  have hp : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set R := M.ψF1.range
  set U : Subgroup R := Subgroup.zpowers M.uF1
  have hU : U.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ (M.uF1_normal g) k
  have hcardU : Nat.card U = 5 := by rw [Nat.card_zpowers, M.orderOf_uF1]
  have hcardQ : Nat.card (R ⧸ U) = 4 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup U
    rw [M.card_range_ψF1, hcardU] at h
    omega
  set x' : R := ⟨M.ψF1 ⟨x, hx⟩, ⟨_, rfl⟩⟩
  have hx'5 : x' ^ 5 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    show (M.ψF1 ⟨x, hx⟩) ^ 5 = 1
    rw [← map_pow]
    have : (⟨x, hx⟩ : M.F1) ^ 5 = 1 := Subtype.ext (by simpa using hx5)
    rw [this, map_one]
  have hq4 : (QuotientGroup.mk x' : R ⧸ U) ^ 4 = 1 := by
    rw [← hcardQ]
    exact pow_card_eq_one'
  have hq5 : (QuotientGroup.mk x' : R ⧸ U) ^ 5 = 1 := by
    rw [← QuotientGroup.mk_pow, hx'5, QuotientGroup.mk_one]
  have hq1 : (QuotientGroup.mk x' : R ⧸ U) = 1 := by
    have := (pow_gcd_eq_one (a := (QuotientGroup.mk x' : R ⧸ U))).mpr ⟨hq4, hq5⟩
    rwa [show Nat.gcd 4 5 = 1 by norm_num, pow_one] at this
  have hxU : x' ∈ U := (QuotientGroup.eq_one_iff x').mp hq1
  obtain ⟨k, hk⟩ := exists_pow_of_mem_zpowers hxU
  refine ⟨k, ?_⟩
  have hk' := congrArg Subtype.val hk
  rw [Subgroup.coe_pow] at hk'
  rw [M.phiG_of_mem (M.F1_le_H hx), M.phiG_of_mem M.b5el_mem_H]
  exact hk'.symm

theorem F1_norm_of_order_five {c : G} (hc : c ∈ M.F1)
    (hc5 : c ^ 5 = 1) (hc1 : M.phiG c ≠ 1) (f : G) (hf : f ∈ M.F1) :
    ∃ k : ℕ, M.phiG (f * c * f⁻¹) = M.phiG c ^ k := by
  have hfc : f * c * f⁻¹ ∈ M.F1 := mul_mem (mul_mem hf hc) (inv_mem hf)
  have hfc5 : (f * c * f⁻¹) ^ 5 = 1 := by rw [conj_pow, hc5]; group
  obtain ⟨k1, hk1⟩ := M.exists_phiG_eq_pow_of_mem_F1 hfc hfc5
  obtain ⟨k2, hk2⟩ := M.exists_phiG_eq_pow_of_mem_F1 hc hc5
  have hb5 : M.phiG M.b5el ^ 5 = 1 := by
    rw [← M.phiG_pow M.b5el_mem_H, pow_five_of_orderOf M.orderOf_b5el, M.phiG_one47]
  obtain ⟨r, hr⟩ := Conf47.exists_pow_pow_eq hb5 (show M.phiG M.b5el ^ k2 ≠ 1 by
    rw [← hk2]; exact hc1)
  refine ⟨r * k1, ?_⟩
  rw [hk1, hk2, pow_mul, hr]

variable {M}

open J47 in
theorem zG_eq_z
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups M.F1 M.F2)) :
    zG e = M.z := by
  have hzA : M.z ∈ M.Agrp := M.W_le_Agrp (M.U_le_W (M.V_le_U M.z_mem_V))
  exact zG_eq e (M.Agrp_le_F1 hzA) (M.Agrp_le_F2 hzA) M.z_mul_self M.z_ne_one
    (fun x hx => (M.Z_comm_H M.z_mem_Z (M.F1_le_H hx)).symm)

open J47 in
@[expose] noncomputable def conf47
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups M.F1 M.F2)) :
    Conf47 M where
  F1 := M.F1
  b := bG e
  u := uG e
  j := jG e
  y := yG e
  iEl := iG e
  F1_le_H := M.F1_le_H
  card_F1 := M.card_F1
  card_F1_inf_Q := by rw [M.F1_inf_Q, M.card_Y]
  b_mem := hom1_mem e _
  orderOf_b := by
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    exact orderOf_eq_prime (bG_pow_five e) (bG_ne_one e)
  u_mem := hom1_mem e _
  u_mul_self := uG_mul_self e
  u_inv_b := uG_inv_bG e
  j_mul_self := jG_mul_self e
  j_conj_z := by rw [← zG_eq_z e]; exact jG_conj_zG e
  conj_mem_F1 := fun _ hc hcu => jG_conj_mem_F1 e hc hcu
  iEl_inj := fun _ hp _ hq h => iG_inj e hp hq h
  iEl_mem := iG_mem e
  iEl_comm := iG_comm_uG e
  iEl_norm := iG_norm_bG e
  iEl_inv := fun _ hp h2 => by
    have h := iG_inv e hp h2
    rwa [zG_eq_z e] at h
  conj_u_ne := fun _ hg => by
    have h := conj_uG_ne e hg
    rwa [zG_eq_z e] at h
  y_pow_three := yG_pow_three e
  y_ne_one := yG_ne_one e
  y_comm_t := by
    have h := yG_comm_tG e
    rwa [zG_eq_z e] at h
  y_conj_z := by rw [← zG_eq_z e]; exact yG_conj_zG e
  F1_norm := fun f hf =>
    M.F1_norm_of_order_five (hom1_mem e _) (bG_pow_five e)
      (M.phiG_ne_one_of_pow_five (M.F1_le_H (hom1_mem e _)) (bG_pow_five e) (bG_ne_one e)) f hf

end RuDataM

end CFSG.Quasithin.RuType
