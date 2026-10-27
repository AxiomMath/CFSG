module

public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationElevenT2
public import CFSG.Quasithin.Background.I4Recognition

public section

namespace CFSG.Quasithin.A10

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.CT

variable {G : Type} [Group G]

namespace Emb

variable {T M : Subgroup G} (E : Emb G T M)

noncomputable def T₂equiv : DihedralGroup 4 ≃* E.T₂ :=
  ((MonoidHom.ofInjective dhom_injective).trans (MulEquiv.subgroupCongr dhom_range)).trans
    (Subgroup.equivMapOfInjective T2h E.ι E.injective)

theorem pt_mul_pt_mem {ℓ : Bool} {c : G} (hcs : E.Acts ℓ c s3) :
    c * E.tz * c⁻¹ = E.pt ℓ 0 * E.pt ℓ 4 ∧
      c * (E.pt ℓ 0 * E.pt ℓ 4) * c⁻¹ = E.pt ℓ 0 * E.pt ℓ 3 := by
  have hs : s3 3 = 4 ∧ s3 4 = 0 ∧ s3 0 = 3 := ⟨s3_apply.2.1, s3_apply.2.2.1, s3_apply.1⟩
  constructor
  · have hk := E.acts_conj_pair hcs 3 4
    rw [hs.1, hs.2.1] at hk
    rw [E.tz_eq_pt ℓ, hk, E.pt_comm ℓ 4 0]
  · have hk := E.acts_conj_pair hcs 0 4
    rw [hs.2.2, hs.2.1] at hk
    rw [hk, E.pt_comm ℓ 3 0]

theorem invol_T₂_conj {c : G} (hcs : E.Acts false c s3) (hcH : c ∈ E.HH) {y : G} (hy : y ∈ E.T₂)
    (hy1 : y ≠ 1) (hy2 : y * y = 1) : ∃ h ∈ E.HH, h⁻¹ * y * h = E.tz := by
  obtain ⟨w, hw, rfl⟩ := hy
  have hw1 : w ≠ 1 := fun h => hy1 (by rw [h, map_one])
  have hw2 : w * w = 1 := E.ι_sq_eq_one.1 hy2
  obtain ⟨hk1, hk2⟩ := E.pt_mul_pt_mem hcs
  rcases T2h_inv w hw hw1 hw2 with hV | hW
  · obtain ⟨m, hm, hmw⟩ := V2_conj w hV hw1
    refine ⟨E.ι m, E.H₁_le_HH ⟨m, hm, rfl⟩, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul, hmw]
    rfl
  · rcases mem_Wm_iff.1 hW with h | h | h | h
    · exact absurd h hw1
    · refine ⟨1, E.HH.one_mem, ?_⟩
      rw [h, map_mul, E.tz_eq_pt false]
      show 1⁻¹ * (E.pt false 3 * E.pt false 4) * 1 = E.pt false 3 * E.pt false 4
      group
    · refine ⟨c * c, E.HH.mul_mem hcH hcH, ?_⟩
      rw [h, map_mul]
      have e1 : E.ι (ptm false 0) * E.ι (ptm false 3) = E.pt false 0 * E.pt false 3 := rfl
      rw [e1, ← hk2, ← hk1]
      group
    · refine ⟨c, hcH, ?_⟩
      rw [h, map_mul]
      have e1 : E.ι (ptm false 0) * E.ι (ptm false 4) = E.pt false 0 * E.pt false 4 := rfl
      rw [e1, ← hk1]
      group

theorem exists_conj_mem_T₂ [Finite G] (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M)
    (hT₂H : E.T₂ ≤ E.HH) {u : G} (hu : u ∈ E.HH) (hu2 : u * u = 1) :
    ∃ g ∈ E.HH, g⁻¹ * u * g ∈ E.T₂ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T' : Subgroup ↥E.HH := E.T₂.subgroupOf E.HH
  have hT'p : IsPGroup 2 T' := E.T₂_isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hT₂H).symm
  have hT'card : Nat.card T' = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT₂H).toEquiv, E.card_T₂]
  obtain ⟨ST, hST⟩ := hT'p.exists_le_sylow
  have hSTcard : Nat.card (ST : Subgroup ↥E.HH) ≤ 8 := by
    have h := E.card_le_8 hT hM (P := (ST : Subgroup ↥E.HH).map E.HH.subtype)
      (ST.isPGroup'.map _) (Subgroup.map_subtype_le _)
    rwa [Subgroup.card_map_of_injective E.HH.subtype_injective] at h
  have hSTeq : T' = (ST : Subgroup ↥E.HH) :=
    Subgroup.eq_of_le_of_card_ge hST (by rw [hT'card]; exact hSTcard)
  let u' : ↥E.HH := ⟨u, hu⟩
  have hu'2 : u' ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hu2)
  have hord : orderOf u' ∣ 2 ^ 1 := by
    rw [pow_one]
    exact orderOf_dvd_of_pow_eq_one hu'2
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
  have hZp : IsPGroup 2 (Subgroup.zpowers u') :=
    IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  obtain ⟨Su, hSu⟩ := hZp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥E.HH Su ST
  have hu'Su : u' ∈ (Su : Subgroup ↥E.HH) := hSu (Subgroup.mem_zpowers u')
  have h1 : g * u' * g⁻¹ ∈ ((g • Su : Sylow 2 ↥E.HH) : Subgroup ↥E.HH) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨u', hu'Su, by simp [MulAut.conj_apply]⟩
  rw [hg, ← hSTeq] at h1
  refine ⟨(g : G)⁻¹, E.HH.inv_mem g.2, ?_⟩
  have h2 := Subgroup.mem_subgroupOf.1 h1
  simpa using h2

theorem exists_conj_tz [Finite G] (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M)
    (hT₂H : E.T₂ ≤ E.HH) {c : G} (hcs : E.Acts false c s3) (hcH : c ∈ E.HH) {u : G}
    (hu : u ∈ E.HH) (hu1 : u ≠ 1) (hu2 : u * u = 1) : ∃ h ∈ E.HH, h⁻¹ * u * h = E.tz := by
  obtain ⟨g, hgH, hgu⟩ := E.exists_conj_mem_T₂ hT hM hT₂H hu hu2
  have hu1' : g⁻¹ * u * g ≠ 1 := by
    intro h
    apply hu1
    calc u = g * (g⁻¹ * u * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hsq' : (g⁻¹ * u * g) * (g⁻¹ * u * g) = 1 := by
    calc (g⁻¹ * u * g) * (g⁻¹ * u * g) = g⁻¹ * (u * u) * g := by group
      _ = 1 := by rw [hu2]; group
  obtain ⟨h, hh, hht⟩ := E.invol_T₂_conj hcs hcH hgu hu1' hsq'
  refine ⟨g * h, E.HH.mul_mem hgH hh, ?_⟩
  rw [← hht]
  group

theorem H_iso
    [Finite G] (hEven : quasithinEvenCharacteristic G) (hT : quasithinIsSylowTwo T)
    (hM : quasithinIsMaxTwoLocal M) {c : G} (hcs : E.Acts false c s3) (hc3 : c ^ 3 = 1)
    (hEc : ∀ x ∈ E.E₀, x * c = c * x) (hEW : ∀ x ∈ E.E₀, ∀ w ∈ E.W false, x * w = w * x) :
    Nonempty (↥E.HH ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) ∨
      Nonempty (↥E.HH ≃* alternatingGroup (Fin 6)) := by
  have hT₂H : E.T₂ ≤ E.HH := E.T₂_le_HH hcs hc3 hEc hEW
  have hcH : c ∈ E.HH := E.mem_HH_of_pow_three (E.mem_CE.2 hEc) hc3
  have hz : E.tz ∈ E.HH := hT₂H E.tz_mem_T₂
  let z₀ : ↥E.HH := ⟨E.tz, hz⟩
  have hz₀ : orderOf z₀ = 2 := by
    refine orderOf_eq_prime (by exact Subtype.ext (by simpa [pow_two] using E.tz_sq)) ?_
    intro h
    exact E.tz_ne_one (congrArg Subtype.val h)
  have hconj : ∀ u : ↥E.HH, orderOf u = 2 → IsConj u z₀ := by
    intro u hu
    obtain ⟨hu2, hu1⟩ := orderOf_eq_prime_iff.1 hu
    have hu2' : (u : G) * (u : G) = 1 := by simpa [pow_two] using congrArg Subtype.val hu2
    have hu1' : (u : G) ≠ 1 := fun h => hu1 (Subtype.ext h)
    obtain ⟨h, hh, hht⟩ := E.exists_conj_tz hT hM hT₂H hcs hcH u.2 hu1' hu2'
    rw [isConj_iff]
    refine ⟨⟨h⁻¹, E.HH.inv_mem hh⟩, Subtype.ext ?_⟩
    simpa using hht
  refine CFSG.Quasithin.I4.lemma_I_4_1_two ↥E.HH (fun u v hu hv => (hconj u hu).trans
    (hconj v hv).symm) (z := z₀) hz₀ ?_
  have hcent : Subgroup.centralizer ({z₀} : Set ↥E.HH) = E.T₂.subgroupOf E.HH := by
    ext y
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro hy
      refine E.mem_T₂_of_centralizes_tz hEven hT hM hT₂H y.2 ?_
      have := hy z₀ rfl
      exact (congrArg Subtype.val this).symm
    · intro hy h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact Subtype.ext (E.T₂_comm_tz hy).symm
  exact ⟨(MulEquiv.subgroupCongr hcent).trans
    ((Subgroup.subgroupOfEquivOfLe hT₂H).trans E.T₂equiv.symm)⟩

end Emb

end CFSG.Quasithin.A10
