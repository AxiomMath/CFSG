module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Esimple5
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma41Base
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Esimple4

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {H : Type} [Group H] [Finite H]

theorem ap_E_simple {β : MulAut H} {Z K : Subgroup H} {z₀ : H} (hd : FF79APData β Z K z₀) :
    layer H ≠ ⊥ ∧ IsSimpleGroup ↥(layer H) ∧ K ≤ layer H ∧
      ∀ x : H, x ∈ layer H → β x ∈ layer H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKE := e34_K_le_layer hd
  have hE := e34_layer_ne_bot hd
  have hS := hd.absyl
  have hO := hd.core
  obtain ⟨e⟩ := hd.K_a5
  obtain ⟨x, hxK, hx3, V, hVK, hV2, hV1, hVx⟩ := e34_a5_data e
  have hx3' : x ^ 3 = 1 := hx3 ▸ pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx3
    exact absurd hx3 (by decide)
  haveI := e34_K_simple hd
  obtain ⟨C0, hC0, k0, hk0, w0, hw0, hkw0⟩ :
      ∃ C : Subgroup H, IsComponent C ∧ ∃ k ∈ K, ∃ w ∈ C, k * w ≠ w * k := by
    by_contra hno
    push Not at hno
    have hcen : ∀ k ∈ K, k = 1 := by
      intro k hk
      refine e34_center_layer_trivial hO hS (hKE hk) fun w hw => ?_
      have hle : layer H ≤ Subgroup.centralizer ({k} : Set H) := by
        refine sSup_le fun C hC => ?_
        intro w hw
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hno C hC k hk w hw).symm
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)
    exact hx1 (hcen x hxK)
  obtain ⟨ρ, hρ⟩ := e34_exists_rho hO hS hC0
  let ρK : ↥K →* ↥C0 := ρ.comp (Subgroup.inclusion hKE)
  have hρK : ∀ (k : ↥K) (w : H), w ∈ C0 →
      (k : H) * w * (k : H)⁻¹ = (ρK k : H) * w * (ρK k : H)⁻¹ := fun k w hw =>
    hρ (Subgroup.inclusion hKE k) w hw
  have hinj : Function.Injective ρK := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases (MonoidHom.normal_ker ρK).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      have h1 : ρK ⟨k0, hk0⟩ = 1 := by
        have : (⟨k0, hk0⟩ : ↥K) ∈ ρK.ker := by rw [h]; trivial
        exact this
      apply hkw0
      have := hρK ⟨k0, hk0⟩ w0 hw0
      rw [h1] at this
      simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one] at this
      calc k0 * w0 = k0 * w0 * k0⁻¹ * k0 := by group
        _ = w0 * k0 := by rw [this]
  let V' : Subgroup ↥K := V.subgroupOf K
  have hV'2 : IsPGroup 2 V' := hV2.of_equiv (Subgroup.subgroupOfEquivOfLe hVK).symm
  let V1 : Subgroup H := (V'.map ρK).map C0.subtype
  have hV1le : V1 ≤ C0 := Subgroup.map_subtype_le _
  have hV1mem : ∀ v : H, ∀ hv : v ∈ V, ((ρK ⟨v, hVK hv⟩ : ↥C0) : H) ∈ V1 := fun v hv =>
    ⟨_, ⟨⟨v, hVK hv⟩, hv, rfl⟩, rfl⟩
  have hV1p : IsPGroup 2 V1 := (hV'2.map ρK).map C0.subtype
  have hV1ne : V1 ≠ ⊥ := by
    intro h
    obtain ⟨v, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV1
    have hm := hV1mem v v.2
    rw [h, Subgroup.mem_bot] at hm
    have : ρK ⟨v, hVK v.2⟩ = 1 := Subtype.ext hm
    have h2 := hinj (this.trans (map_one ρK).symm)
    have h3 : (v : H) = 1 := congrArg Subtype.val h2
    exact hv1 (Subtype.ext h3)
  set u0 : H := ((ρK ⟨x, hxK⟩ : ↥C0) : H) with hu0
  have hu0C : u0 ∈ C0 := (ρK ⟨x, hxK⟩).2
  have hu03 : u0 ^ 3 = 1 := by
    have : (ρK ⟨x, hxK⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨x, hxK⟩ : ↥K) ^ 3 = 1 := Subtype.ext hx3'
      rw [this, map_one]
    exact congrArg Subtype.val this
  have hu01 : u0 ≠ 1 := by
    intro h
    have : ρK ⟨x, hxK⟩ = 1 := Subtype.ext h
    have h2 := hinj (this.trans (map_one ρK).symm)
    exact hx1 (congrArg Subtype.val h2)
  have hu0o : orderOf u0 = 3 := orderOf_eq_prime hu03 hu01
  have hu0N : u0 ∈ Nor V1 := by
    refine L41.mem_nor_of_forall fun y hy => ?_
    obtain ⟨_, ⟨b, hb, rfl⟩, rfl⟩ := hy
    have hxv := hVx (b : H) hb
    have h1 : ((ρK ⟨x * (b : H) * x⁻¹, hVK hxv⟩ : ↥C0) : H) =
        u0 * ((ρK b : ↥C0) : H) * u0⁻¹ := by
      have : (⟨x * (b : H) * x⁻¹, hVK hxv⟩ : ↥K) = ⟨x, hxK⟩ * b * ⟨x, hxK⟩⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv]
      rfl
    have h2 := hV1mem _ hxv
    rw [h1] at h2
    exact h2
  have hall : ∀ D : Subgroup H, IsComponent D → D = C0 := by
    intro D hD
    by_contra hne
    have hDC : D ≤ Subgroup.centralizer (C0 : Set H) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        ((LocalCores.distinct_components_commute hD hC0).resolve_left hne)
    have hDc : ∀ d ∈ D, ∀ w ∈ C0, w * d = d * w := fun d hd w hw =>
      Subgroup.mem_centralizer_iff.mp (hDC hd) w hw
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥D) 3
      (e34_comp_three_dvd hO hD (e34_comp_ne_bot hD))
    have hgo : orderOf (g : H) = 3 := by rw [Subgroup.orderOf_coe]; exact hg
    have hgD : (g : H) ∈ D := g.2
    have hinf : Subgroup.zpowers u0 ⊓ Subgroup.zpowers (g : H) = ⊥ := by
      rw [eq_bot_iff]
      rintro t ⟨ht0, ht2⟩
      rw [Subgroup.mem_bot]
      have htC : t ∈ C0 := (Subgroup.zpowers_le.mpr hu0C) ht0
      have htD : t ∈ D := (Subgroup.zpowers_le.mpr hgD) ht2
      exact e34_comp_center_trivial hO hS hC0 htC fun w hw => hDc t htD w hw
    have hcomm : ∀ a ∈ Subgroup.zpowers u0, ∀ b ∈ Subgroup.zpowers (g : H), a * b = b * a :=
      fun a ha b hb => hDc b ((Subgroup.zpowers_le.mpr hgD) hb) a
        ((Subgroup.zpowers_le.mpr hu0C) ha)
    have hT : IsElemAb 3 (1 + 1) (Subgroup.zpowers u0 ⊔ Subgroup.zpowers (g : H)) :=
      e34_elemAb_sup (e34_elemAb_zpowers hu0o) (e34_elemAb_zpowers hgo) hcomm hinf
    have hTZ : (Subgroup.zpowers u0 ⊔ Subgroup.zpowers (g : H)) ⊓ Z = ⊥ := by
      rw [eq_bot_iff]
      rintro t ⟨htT, htZ⟩
      rw [Subgroup.mem_bot]
      have hTE : Subgroup.zpowers u0 ⊔ Subgroup.zpowers (g : H) ≤ layer H :=
        sup_le (Subgroup.zpowers_le.mpr (LocalCores.component_le_layer hC0 hu0C))
          (Subgroup.zpowers_le.mpr (LocalCores.component_le_layer hD hgD))
      refine e34_center_layer_trivial hO hS (hTE htT) fun w _ => ?_
      exact (Subgroup.mem_center_iff.mp (hd.Z_central htZ) w)
    have hgN : (g : H) ∈ Nor V1 := by
      refine L41.mem_nor_of_forall fun y hy => ?_
      have := hDc (g : H) hgD y (hV1le hy)
      have h2 : (g : H) * y * (g : H)⁻¹ = y := by
        rw [← this]; group
      rw [h2]
      exact hy
    have hTN : Subgroup.zpowers u0 ⊔ Subgroup.zpowers (g : H) ≤ Nor V1 :=
      sup_le (Subgroup.zpowers_le.mpr hu0N) (Subgroup.zpowers_le.mpr hgN)
    exact hd.no_rank2 V1 _ hV1p hV1ne (by simpa using hT) hTZ hTN
  have hlay : layer H = C0 :=
    le_antisymm (sSup_le fun D hD => (hall D hD).le) (LocalCores.component_le_layer hC0)
  refine ⟨hE, ?_, hKE, fun y hy => e34_layer_inv β hy⟩
  rw [hlay]
  exact e34_comp_simple hO hS hC0

end CFSG.RankThree.PartTwo.Sec21.FF79
