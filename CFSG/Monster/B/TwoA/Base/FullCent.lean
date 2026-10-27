module

public import CFSG.Monster.B.Cbar.SylowTwo

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B

theorem map_inf_centralizer {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Function.Injective f) (A B : Subgroup G) :
    (A ⊓ Subgroup.centralizer (B : Set G)).map f =
      A.map f ⊓ Subgroup.centralizer ((B.map f : Subgroup H) : Set H) := by
  ext y
  constructor
  · rintro ⟨a, ⟨ha, hc⟩, rfl⟩
    refine ⟨⟨a, ha, rfl⟩, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.1 hc) b hb]
  · rintro ⟨⟨a, ha, rfl⟩, hc⟩
    refine ⟨a, ⟨ha, Subgroup.mem_centralizer_iff.2 fun b hb => hf ?_⟩, rfl⟩
    rw [map_mul, map_mul]
    exact (Subgroup.mem_centralizer_iff.1 hc) (f b) ⟨b, hb, rfl⟩

@[expose] noncomputable def Cfull : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB) :=
  Gmat ⊓ Subgroup.centralizer {tStar}

theorem Cgen_le_Cfull : Cgen ≤ Cfull := Cgen_le

instance : Finite Cfull :=
  Finite.of_injective (Subgroup.inclusion (inf_le_left : Cfull ≤ Gmat))
    (Subgroup.inclusion_injective _)

theorem tStar_mem_Cfull : tStar ∈ Cfull := Cgen_le_Cfull tStar_mem_Cgen

theorem commute_tStar_of_mem_Cfull {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Cfull) :
    g * tStar = tStar * g :=
  Subgroup.mem_centralizer_singleton_iff.1 hg.2

@[expose] noncomputable def tStarF : Cfull := ⟨tStar, tStar_mem_Cfull⟩

@[expose] noncomputable def ZstarF : Subgroup Cfull := Subgroup.zpowers tStarF

theorem tStarF_mem_center : tStarF ∈ Subgroup.center Cfull := by
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (commute_tStar_of_mem_Cfull g.2)

theorem ZstarF_le_center : ZstarF ≤ Subgroup.center Cfull :=
  (Subgroup.zpowers_le).2 tStarF_mem_center

instance ZstarF_normal : ZstarF.Normal := Subgroup.normal_of_le_center ZstarF_le_center

theorem orderOf_tStarF : orderOf tStarF = 2 := by
  have h := orderOf_injective Cfull.subtype Subtype.coe_injective tStarF
  rw [Subgroup.coe_subtype] at h
  rw [← h]
  exact orderOf_tStar

abbrev Dfull : Type := Cfull ⧸ ZstarF

@[expose] noncomputable def piD : Cfull →* Dfull := QuotientGroup.mk' ZstarF

theorem piD_surjective : Function.Surjective piD := QuotientGroup.mk'_surjective ZstarF

theorem ker_piD : piD.ker = ZstarF := QuotientGroup.ker_mk' ZstarF

theorem piD_eq_one_iff (g : Cfull) : piD g = 1 ↔ g = 1 ∨ g = tStarF := by
  rw [← MonoidHom.mem_ker, ker_piD, ZstarF]
  exact Short.mem_zpowers_iff_of_orderOf_eq_two orderOf_tStarF

instance : Finite Dfull := Finite.of_surjective piD piD_surjective

@[expose] noncomputable def inclGen : Cgen →* Cfull := Subgroup.inclusion Cgen_le_Cfull

theorem Zstar_le_comap : Zstar ≤ ZstarF.comap inclGen := by
  rw [Zstar, Subgroup.zpowers_le, Subgroup.mem_comap]
  exact Subgroup.mem_zpowers _

@[expose] noncomputable def iotaD : Cbar →* Dfull :=
  QuotientGroup.map Zstar ZstarF inclGen Zstar_le_comap

theorem iotaD_kappa (g : Cgen) : iotaD (kappa g) = piD (inclGen g) := rfl

theorem iotaD_injective : Function.Injective iotaD := by
  rw [injective_iff_map_eq_one]
  intro c hc
  obtain ⟨g, rfl⟩ := kappa_surjective c
  rw [iotaD_kappa, piD_eq_one_iff] at hc
  rw [kappa_eq_one_iff]
  rcases hc with h | h
  · exact .inl (Subtype.ext (show (g : SpaceB ≃ₗ[ℚ] SpaceB) = 1 from congrArg Subtype.val h))
  · exact .inr (Subtype.ext (show (g : SpaceB ≃ₗ[ℚ] SpaceB) = tStar from congrArg Subtype.val h))

@[expose] noncomputable def xF : Cfull := inclGen xC

@[expose] noncomputable def xhat : Dfull := piD xF

theorem iotaD_xbar : iotaD xbar = xhat := rfl

@[expose] noncomputable def Jhat : Subgroup Dfull := (Jstar.subgroupOf Cfull).map piD

@[expose] noncomputable def Ehat : Subgroup Dfull := Ebar.map iotaD

@[expose] noncomputable def Shat : Subgroup Dfull := iotaD.range

@[expose] noncomputable def tauhat : Dfull := iotaD taubar

theorem Jhat_eq_map : Jhat = Jbar.map iotaD := by
  rw [Jhat, Jbar, Subgroup.map_map]
  ext d
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, Jstar_le_Cgen hg⟩, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨inclGen g, hg, rfl⟩

theorem orderOf_xhat : orderOf xhat = 2 := by
  rw [← iotaD_xbar, orderOf_injective iotaD iotaD_injective, orderOf_xbar]

theorem Jhat_le_centralizer_xhat :
    Jhat ≤ Subgroup.centralizer {xhat} := by
  rw [Jhat_eq_map, ← iotaD_xbar]
  rintro _ ⟨c, hc, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  rw [← centralizer_xbar] at hc
  rw [(Subgroup.mem_centralizer_singleton_iff.1 hc)]

theorem centralizer_xhat_le_Jhat :
    Subgroup.centralizer {xhat} ≤ Jhat := by
  intro d hd
  obtain ⟨g, rfl⟩ := piD_surjective d
  rw [Subgroup.mem_centralizer_singleton_iff] at hd
  have h1 : piD (g * xF * g⁻¹ * xF⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    change piD g * xhat * (piD g)⁻¹ * xhat⁻¹ = 1
    rw [hd]
    group
  have hcomm : (g : SpaceB ≃ₗ[ℚ] SpaceB) * xmat * (g : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ = xmat := by
    rcases (piD_eq_one_iff _).1 h1 with h2 | h2
    · have h3 := congrArg Subtype.val h2
      change (g : SpaceB ≃ₗ[ℚ] SpaceB) * xmat * (g : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ * xmat⁻¹ = 1 at h3
      exact mul_inv_eq_one.1 h3
    · exfalso
      have h3 := congrArg Subtype.val h2
      change (g : SpaceB ≃ₗ[ℚ] SpaceB) * xmat * (g : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ * xmat⁻¹ =
        tStar at h3
      have h4 : (g : SpaceB ≃ₗ[ℚ] SpaceB) * xmat * (g : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ =
          rhoEquiv (zQ * rStar) := by
        rw [← tStar_mul_xmat, ← h3]
        group
      have e1 := trace_conj (g : SpaceB ≃ₗ[ℚ] SpaceB) xmat
      rw [h4, trace_rho_short isShortCoord_zQ_mul_rStar, trace_xmat] at e1
      norm_num at e1
  have hgx : (g : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gmat ⊓ Subgroup.centralizer {xmat} := by
    refine ⟨g.2.1, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    calc (g : SpaceB ≃ₗ[ℚ] SpaceB) * xmat =
        (g : SpaceB ≃ₗ[ℚ] SpaceB) * xmat * (g : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ *
          (g : SpaceB ≃ₗ[ℚ] SpaceB) := by group
      _ = xmat * (g : SpaceB ≃ₗ[ℚ] SpaceB) := by rw [hcomm]
  rw [Gmat_inf_centralizer_xmat] at hgx
  exact ⟨g, ⟨hgx, Subgroup.mem_centralizer_singleton_iff.2 (commute_tStar_of_mem_Cfull g.2)⟩, rfl⟩

theorem centralizer_xhat : Subgroup.centralizer {xhat} = Jhat :=
  le_antisymm centralizer_xhat_le_Jhat Jhat_le_centralizer_xhat

theorem center_Ehat : (Subgroup.center Ehat).map Ehat.subtype = Subgroup.zpowers xhat := by
  rw [map_center_eq_inf_centralizer, Ehat, ← map_inf_centralizer iotaD_injective,
    ← map_center_eq_inf_centralizer, map_center_Ebar, MonoidHom.map_zpowers, iotaD_xbar]

theorem centralizer_Ehat :
    Jhat ⊓ Subgroup.centralizer (Ehat : Set Dfull) = Subgroup.zpowers xhat := by
  rw [Jhat_eq_map, Ehat, ← map_inf_centralizer iotaD_injective, centralizer_Ebar,
    MonoidHom.map_zpowers, iotaD_xbar]

theorem Ehat_le_Jhat : Ehat ≤ Jhat := by
  rw [Jhat_eq_map]
  exact Subgroup.map_mono Ebar_le_Jbar

theorem conj_mem_Ehat {g e : Dfull} (hg : g ∈ Jhat) (he : e ∈ Ehat) : g⁻¹ * e * g ∈ Ehat := by
  rw [Jhat_eq_map] at hg
  obtain ⟨g₀, hg₀, rfl⟩ := hg
  obtain ⟨e₀, he₀, rfl⟩ := he
  exact ⟨g₀⁻¹ * e₀ * g₀, conj_mem_Ebar hg₀ he₀, by rw [map_mul, map_mul, map_inv]⟩

instance Ehat_subgroupOf_normal : (Ehat.subgroupOf Jhat).Normal where
  conj_mem n hn g := by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h := conj_mem_Ehat (g⁻¹).2 hn
    simpa using h

theorem isPGroup_Ehat : IsPGroup 2 Ehat := by
  have hE := Ebar_extraspecial.1.1
  exact hE.of_equiv (Ebar.equivMapOfInjective iotaD iotaD_injective)

theorem natCard_Jhat :
    Nat.card Jhat = 2 ^ 41 * 161382375 := by
  rw [Jhat_eq_map, ← Nat.card_congr (Jbar.equivMapOfInjective iotaD iotaD_injective).toEquiv,
    natCard_Jbar_eq]

theorem ZstarF_le_Jstar : ZstarF ≤ Jstar.subgroupOf Cfull := by
  rw [ZstarF, Subgroup.zpowers_le, Subgroup.mem_subgroupOf]
  exact tStar_mem_Jstar

theorem ZstarF_le_Cgen : ZstarF ≤ Cgen.subgroupOf Cfull := by
  rw [ZstarF, Subgroup.zpowers_le, Subgroup.mem_subgroupOf]
  exact tStar_mem_Cgen

theorem preimage_Jhat (g : Cfull) : piD g ∈ Jhat ↔ (g : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Jstar := by
  have h : Jhat.comap piD = Jstar.subgroupOf Cfull := by
    rw [Jhat, Subgroup.comap_map_eq, ker_piD, sup_of_le_left ZstarF_le_Jstar]
  rw [← Subgroup.mem_comap, h, Subgroup.mem_subgroupOf]

theorem Shat_eq_map : Shat = (Cgen.subgroupOf Cfull).map piD := by
  ext d
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨g, rfl⟩ := kappa_surjective c
    exact ⟨inclGen g, g.2, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨kappa ⟨g, hg⟩, rfl⟩

theorem index_Jhat : Jhat.index = (Jstar.subgroupOf Cfull).index :=
  Subgroup.index_map_eq _ piD_surjective (by rw [ker_piD]; exact ZstarF_le_Jstar)

theorem index_Shat : Shat.index = (Cgen.subgroupOf Cfull).index := by
  rw [Shat_eq_map]
  exact Subgroup.index_map_eq _ piD_surjective (by rw [ker_piD]; exact ZstarF_le_Cgen)

theorem natCard_Cfull : Nat.card Cfull = 2 * Nat.card Dfull := by
  have h2 : Nat.card ZstarF = 2 := by rw [ZstarF, Nat.card_zpowers, orderOf_tStarF]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ZstarF, h2, mul_comm]

theorem Jhat_le_Shat : Jhat ≤ Shat := by
  rw [Jhat_eq_map]
  rintro _ ⟨c, -, rfl⟩
  exact ⟨c, rfl⟩

theorem tauhat_conj_xhat : tauhat * xhat * tauhat⁻¹ = iotaD ybar := by
  rw [tauhat, ← iotaD_xbar, ← map_inv, ← map_mul, ← map_mul, taubar_conj_xbar]

theorem xhat_ne_iotaD_ybar : xhat ≠ iotaD ybar := by
  rw [← iotaD_xbar]
  exact iotaD_injective.ne xbar_ne_ybar

theorem mem_zpowers_xhat_iff {d : Dfull} : d ∈ Subgroup.zpowers xhat ↔ d = 1 ∨ d = xhat :=
  Short.mem_zpowers_iff_of_orderOf_eq_two orderOf_xhat

theorem eq_one_of_commute {d : Dfull} (hx : d * xhat = xhat * d)
    (hE : ∀ e ∈ Ehat, e * d = d * e) (ht : d * tauhat = tauhat * d) : d = 1 := by
  have hJ : d ∈ Jhat := by
    rw [← centralizer_xhat]
    exact Subgroup.mem_centralizer_singleton_iff.2 hx
  have hd : d ∈ Jhat ⊓ Subgroup.centralizer (Ehat : Set Dfull) :=
    ⟨hJ, Subgroup.mem_centralizer_iff.2 hE⟩
  rw [centralizer_Ehat, mem_zpowers_xhat_iff] at hd
  rcases hd with h | h
  · exact h
  · exfalso
    subst h
    have h1 : tauhat * xhat * tauhat⁻¹ = xhat := by rw [← ht, mul_inv_cancel_right]
    exact xhat_ne_iotaD_ybar (h1.symm.trans tauhat_conj_xhat)

theorem center_Dfull : Subgroup.center Dfull = ⊥ := by
  rw [eq_bot_iff]
  intro d hd
  rw [Subgroup.mem_bot]
  have h := Subgroup.mem_center_iff.1 hd
  exact eq_one_of_commute (h xhat).symm (fun e _ => h e) (h tauhat).symm

theorem center_Cfull : Subgroup.center Cfull = ZstarF := by
  apply le_antisymm
  · intro g hg
    rw [← ker_piD, MonoidHom.mem_ker]
    have h : piD g ∈ Subgroup.center Dfull :=
      Subgroup.map_center_le_center piD_surjective ⟨g, hg, rfl⟩
    rw [center_Dfull, Subgroup.mem_bot] at h
    exact h
  · exact ZstarF_le_center

theorem centralizer_Cgen :
    Subgroup.centralizer ((Cgen.subgroupOf Cfull : Subgroup Cfull) : Set Cfull) = ZstarF := by
  apply le_antisymm
  · intro g hg
    rw [← ker_piD, MonoidHom.mem_ker]
    have hc := Subgroup.mem_centralizer_iff.1 hg
    have key : ∀ c : Cgen, inclGen c * g = g * inclGen c := fun c => hc _ c.2
    apply eq_one_of_commute
    · have := congrArg piD (key xC)
      rw [map_mul, map_mul] at this
      exact this.symm
    · rintro _ ⟨e, -, rfl⟩
      obtain ⟨c, rfl⟩ := kappa_surjective e
      rw [iotaD_kappa, ← map_mul, ← map_mul, key c]
    · have := congrArg piD (key tauC)
      rw [map_mul, map_mul] at this
      exact this.symm
  · intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h _
    exact (Subgroup.mem_center_iff.1 (ZstarF_le_center hg) h)

theorem full_short_centralizer_odd_index :
    Function.Injective iotaD ∧ iotaD xbar = xhat ∧ Jbar.map iotaD = Jhat ∧
    Subgroup.centralizer {xhat} = Jhat ∧
    (Subgroup.center Ehat).map Ehat.subtype = Subgroup.zpowers xhat ∧
    Jhat ⊓ Subgroup.centralizer (Ehat : Set Dfull) = Subgroup.zpowers xhat ∧
    (∀ P : Sylow 2 Jhat, ∃ S : Sylow 2 Dfull,
      (S : Subgroup Dfull) = (P : Subgroup Jhat).map Jhat.subtype ∧
      (Subgroup.center (S : Subgroup Dfull)).map (S : Subgroup Dfull).subtype =
        Subgroup.zpowers xhat) ∧
    (∃ m : ℕ, Odd m ∧ Nat.card Dfull = 2 ^ 41 * m) ∧
    (∃ m : ℕ, Odd m ∧ Nat.card Cfull = 2 ^ 42 * m) ∧
    Shat.index = (Cgen.subgroupOf Cfull).index ∧ Odd Shat.index ∧
    Odd (Jstar.subgroupOf Cfull).index ∧
    (∀ g : Cfull, (∃ n : ℕ, g ^ 2 ^ n = 1) →
      ∃ c : Cfull, ((c * g * c⁻¹ : Cfull) : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Jstar) ∧
    Subgroup.center Dfull = ⊥ ∧ Subgroup.center Cfull = ZstarF ∧
    Subgroup.centralizer ((Cgen.subgroupOf Cfull : Subgroup Cfull) : Set Cfull) = ZstarF := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQH : Ehat ≤ Subgroup.centralizer {xhat} := centralizer_xhat ▸ Ehat_le_Jhat
  have hQn : (Ehat.subgroupOf (Subgroup.centralizer {xhat})).Normal := by
    rw [centralizer_xhat]
    infer_instance
  have hCQ : Subgroup.centralizer {xhat} ⊓ Subgroup.centralizer (Ehat : Set Dfull) =
      Subgroup.zpowers xhat := by
    rw [centralizer_xhat]
    exact centralizer_Ehat
  obtain ⟨h1, h2, h3, -⟩ :=
    prime_centralizer_sylow_control orderOf_xhat hQH hQn isPGroup_Ehat center_Ehat hCQ
  rw [centralizer_xhat] at h1 h2 h3
  have hodd : Odd Jhat.index := Nat.coprime_two_right.1 h2
  have hD : Nat.card Dfull = 2 ^ 41 * (161382375 * Jhat.index) := by
    rw [← Jhat.card_mul_index, natCard_Jhat, mul_assoc]
  have hm : Odd (161382375 * Jhat.index) := (by decide : Odd 161382375).mul hodd
  have hS : Odd Shat.index := by
    have hdvd : Shat.index ∣ Jhat.index := Subgroup.index_dvd_of_le Jhat_le_Shat
    exact Odd.of_dvd_nat hodd hdvd
  refine ⟨iotaD_injective, iotaD_xbar, Jhat_eq_map.symm, centralizer_xhat, center_Ehat,
    centralizer_Ehat, h1, ⟨_, hm, hD⟩, ⟨_, hm, ?_⟩, index_Shat, hS, index_Jhat ▸ hodd, ?_,
    center_Dfull, center_Cfull, centralizer_Cgen⟩
  · rw [natCard_Cfull, hD, pow_succ]
    ring
  · intro g ⟨n, hn⟩
    obtain ⟨c, hc⟩ := h3 (piD g) ⟨n, by rw [← map_pow, hn, map_one]⟩
    obtain ⟨c₀, rfl⟩ := piD_surjective c
    refine ⟨c₀, (preimage_Jhat _).1 ?_⟩
    rw [map_mul, map_mul, map_inv]
    exact hc

end CFSG.Monster.B.TwoA
