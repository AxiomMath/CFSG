module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer

namespace CFSG
end CFSG
open CFSG

/-!
# Suzuki V.2.27(v)

Control of fusion by a Sylow subgroup implies the existence of a normal
`p`-complement.
-/

namespace CFSG.BenderSuzuki
namespace External
namespace Suzuki
namespace V

universe u

open scoped Pointwise commutatorElement

private noncomputable def sylowSubgroupOfNormal
    {H : Type u} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (S : Sylow p H) (K : Subgroup H) [K.Normal] :
    Sylow p K := by
  classical
  let I : Subgroup K := (S : Subgroup H).comap K.subtype
  have hIp : IsPGroup p I := S.2.comap_subtype
  apply hIp.toSylow
  let R : Sylow p K := Classical.choice inferInstance
  obtain ⟨Q, hQcomap⟩ := R.exists_comap_subtype_eq
  obtain ⟨h, hQconj⟩ := MulAction.exists_smul_eq H Q S
  have hQconjSub :
      MulAut.conj h • (Q : Subgroup H) = (S : Subgroup H) :=
    congrArg (fun R : Sylow p H => (R : Subgroup H)) hQconj
  have hsmul :
      (MulAut.conjNormal h : MulAut K) •
          ((Q : Subgroup H).comap K.subtype) = I := by
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    change
      (((MulAut.conjNormal h : MulAut K)⁻¹ x : K) : H) ∈ (Q : Subgroup H) ↔
        (x : H) ∈ (S : Subgroup H)
    rw [← hQconjSub]
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    change
      (((MulAut.conjNormal h : MulAut K)⁻¹ x : K) : H) ∈ (Q : Subgroup H) ↔
        h⁻¹ * (x : H) * h ∈ (Q : Subgroup H)
    rw [MulAut.conjNormal_inv_apply]
  have hcardQI :
      Nat.card ((Q : Subgroup H).comap K.subtype) = Nat.card I := by
    let e :
        ((Q : Subgroup H).comap K.subtype) ≃*
          ↥((MulAut.conjNormal h : MulAut K) •
            ((Q : Subgroup H).comap K.subtype)) :=
      Subgroup.equivSMul (MulAut.conjNormal h : MulAut K)
        ((Q : Subgroup H).comap K.subtype)
    exact Nat.card_congr
      (e.trans (MulEquiv.subgroupCongr hsmul)).toEquiv
  have hcardQR :
      Nat.card ((Q : Subgroup H).comap K.subtype) = Nat.card R := by
    rw [hQcomap]
  have hcardIR : Nat.card I = Nat.card R :=
    hcardQI.symm.trans hcardQR
  have hindex : I.index = R.index := by
    apply Nat.mul_left_cancel (Nat.card_pos (α := I))
    calc
      Nat.card I * I.index = Nat.card K := Subgroup.card_mul_index I
      _ = Nat.card R * R.index :=
        (Subgroup.card_mul_index (R : Subgroup K)).symm
      _ = Nat.card I * R.index := by rw [hcardIR]
  simpa [hindex] using R.not_dvd_index

private theorem sylowSubgroupOfNormal_coe
    {H : Type u} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (S : Sylow p H) (K : Subgroup H) [K.Normal] :
    (sylowSubgroupOfNormal S K : Subgroup K) =
      (S : Subgroup H).comap K.subtype := rfl
private theorem commutator_lt_of_normal_subgroup_pgroup
    {P : Type u} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) (N : Subgroup P) [N.Normal] (hN : N ≠ ⊥) :
    ⁅N, (⊤ : Subgroup P)⁆ < N := by
  have hle : ⁅N, (⊤ : Subgroup P)⁆ ≤ N :=
    Subgroup.commutator_le_left N ⊤
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hN_le_lcs : ∀ n, N ≤ (⊤ : Subgroup P).lowerCentralSeries n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          N = ⁅N, (⊤ : Subgroup P)⁆ := heq.symm
          _ ≤ ⁅(⊤ : Subgroup P).lowerCentralSeries n, (⊤ : Subgroup P)⁆ :=
            Subgroup.commutator_mono ih le_rfl
          _ = (⊤ : Subgroup P).lowerCentralSeries (n + 1) := rfl
  have hnil : Group.IsNilpotent P := IsPGroup.isNilpotent (p := p) hP
  obtain ⟨n, hn⟩ := (Subgroup.nilpotent_iff_lowerCentralSeries (G := P)).mp hnil
  apply hN
  rw [eq_bot_iff]
  simpa [hn] using hN_le_lcs n
private theorem focalSubgroupOf_lt_top_of_controlled_fusion
    {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] (f : H →* G) (hf : Function.Injective f)
    (P : Sylow p G) (T : Sylow p H)
    (hTmap : (T : Subgroup H).map f ≤ (P : Subgroup G))
    (hTne : (T : Subgroup H) ≠ ⊥)
    (hfusion : ∀ {x y : G}, x ∈ (P : Subgroup G) → y ∈ (P : Subgroup G) →
      (∃ g : G, g * x * g⁻¹ = y) →
        ∃ h : P, (h : G) * x * (h : G)⁻¹ = y) :
    (T : Subgroup H).feitThompsonFocalSubgroupOf < ⊤ := by
  classical
  let j : T →* P :=
    (f.comp (T : Subgroup H).subtype).codRestrict (P : Subgroup G) (by
      intro x
      exact hTmap (Subgroup.mem_map_of_mem f x.2))
  have hj : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    apply hf
    exact congrArg Subtype.val hxy
  let N : Subgroup P := Subgroup.normalClosure (Set.range j)
  have hNne : N ≠ ⊥ := by
    intro hN
    apply hTne
    rw [eq_bot_iff]
    intro x hx
    have hxN : j ⟨x, hx⟩ ∈ N :=
      Subgroup.subset_normalClosure ⟨⟨x, hx⟩, rfl⟩
    rw [hN] at hxN
    have hjone : j ⟨x, hx⟩ = 1 := by simpa using hxN
    have hxeq : (⟨x, hx⟩ : T) = 1 := hj (by simpa using hjone)
    simpa using congrArg Subtype.val hxeq
  let C : Subgroup P := ⁅N, (⊤ : Subgroup P)⁆
  have hClt : C < N := by
    exact commutator_lt_of_normal_subgroup_pgroup P.isPGroup' N hNne
  have hFmap :
      (T : Subgroup H).feitThompsonFocalSubgroup.map f ≤ C.map (P : Subgroup G).subtype := by
    rw [Subgroup.feitThompsonFocalSubgroup_def, Subgroup.map_le_iff_le_comap,
      Subgroup.closure_le]
    rintro g ⟨x, hx, y, hy, ⟨u, hu⟩, hg⟩
    have hfxP : f x ∈ (P : Subgroup G) :=
      hTmap (Subgroup.mem_map_of_mem f hx)
    have hfyP : f y ∈ (P : Subgroup G) :=
      hTmap (Subgroup.mem_map_of_mem f hy)
    have hxy : (u : H) * x * (u : H)⁻¹ = y := by
      calc
        (u : H) * x * (u : H)⁻¹ = y * (u : H) * (u : H)⁻¹ := by rw [hu]
        _ = y := by simp
    obtain ⟨z, hz⟩ := hfusion hfxP hfyP ⟨f (u : H), by simpa using congrArg f hxy⟩
    have hgT : g ∈ (T : Subgroup H) := by
      rw [hg]
      exact (T : Subgroup H).mul_mem ((T : Subgroup H).inv_mem hx) hy
    have hfg : f g = ⁅(f x)⁻¹, (z : G)⁆ := by
      calc
        f g = (f x)⁻¹ * f y := by rw [hg]; simp
        _ = (f x)⁻¹ * ((z : G) * f x * (z : G)⁻¹) := by rw [hz]
        _ = ⁅(f x)⁻¹, (z : G)⁆ := by
          simp only [commutatorElement_def]
          group
    have hjg :
        j ⟨g, hgT⟩ =
          ⁅j ⟨x⁻¹, (T : Subgroup H).inv_mem hx⟩, z⁆ := by
      apply Subtype.ext
      have hright :
          ((⁅j ⟨x⁻¹, (T : Subgroup H).inv_mem hx⟩, z⁆ : P) : G) =
            ⁅(f x)⁻¹, (z : G)⁆ := by
        calc
          ((⁅j ⟨x⁻¹, (T : Subgroup H).inv_mem hx⟩, z⁆ : P) : G) =
              ⁅((j ⟨x⁻¹, (T : Subgroup H).inv_mem hx⟩ : P) : G), (z : G)⁆ :=
            map_commutatorElement (P : Subgroup G).subtype
              (j ⟨x⁻¹, (T : Subgroup H).inv_mem hx⟩) z
          _ = ⁅f (x⁻¹), (z : G)⁆ := rfl
          _ = ⁅(f x)⁻¹, (z : G)⁆ := by rw [map_inv]
      calc
        ((j ⟨g, hgT⟩ : P) : G) = f g := rfl
        _ = ⁅(f x)⁻¹, (z : G)⁆ := hfg
        _ = ((⁅j ⟨x⁻¹, (T : Subgroup H).inv_mem hx⟩, z⁆ : P) : G) := hright.symm
    have hC :
        j ⟨g, hgT⟩ ∈ C := by
      rw [hjg]
      exact Subgroup.commutator_mem_commutator
        (Subgroup.subset_normalClosure
          ⟨⟨x⁻¹, (T : Subgroup H).inv_mem hx⟩, rfl⟩)
        (Subgroup.mem_top z)
    exact Subgroup.mem_map.mpr
      ⟨j ⟨g, hgT⟩,
        hC, rfl⟩
  have hfoc_le :
      (T : Subgroup H).feitThompsonFocalSubgroupOf ≤ C.comap j := by
    intro g hg
    have hgF : (g : H) ∈ (T : Subgroup H).feitThompsonFocalSubgroup := by
      change (g : H) ∈ (T : Subgroup H).feitThompsonFocalSubgroup at hg
      exact hg
    have hfgMap : f (g : H) ∈ C.map (P : Subgroup G).subtype :=
      hFmap (Subgroup.mem_map_of_mem f hgF)
    rcases Subgroup.mem_map.mp hfgMap with ⟨c, hc, hceq⟩
    change j g ∈ C
    have hjc : j g = c := by
      apply Subtype.ext
      exact hceq.symm
    rw [hjc]
    exact hc
  rw [lt_top_iff_ne_top]
  intro hfoc
  have hNleC : N ≤ C := by
    apply Subgroup.normalClosure_le_normal
    rintro y ⟨t, rfl⟩
    exact hfoc_le (by simp [hfoc])
  exact (not_le_of_gt hClt) hNleC
private theorem hasNormalPComplement_of_controlled_fusion_embedding
    {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] (f : H →* G) (hf : Function.Injective f)
    (P : Sylow p G) (T : Sylow p H)
    (hTmap : (T : Subgroup H).map f ≤ (P : Subgroup G))
    (hfusion : ∀ {x y : G}, x ∈ (P : Subgroup G) → y ∈ (P : Subgroup G) →
      (∃ g : G, g * x * g⁻¹ = y) →
        ∃ h : P, (h : G) * x * (h : G)⁻¹ = y) :
    HasNormalPComplement p H := by
  classical
  by_cases hTbot : (T : Subgroup H) = ⊥
  · apply hkt_hasNormalPComplement_of_not_dvd_card
    simpa [hTbot] using T.not_dvd_index
  let H0 : Subgroup H := T
  let V : H →* H0 ⧸ H0.feitThompsonFocalSubgroupOf := H0.feitThompsonTransferFocal
  let K : Subgroup H := V.ker
  haveI : K.Normal := inferInstance
  have hfoc : H0.feitThompsonFocalSubgroupOf < ⊤ := by
    exact focalSubgroupOf_lt_top_of_controlled_fusion
      f hf P T hTmap hTbot hfusion
  have hfocCard : Nat.card H0.feitThompsonFocalSubgroupOf < Nat.card T := by
    letI : Fintype H0.feitThompsonFocalSubgroupOf := Fintype.ofFinite _
    letI : Fintype T := Fintype.ofFinite _
    have hnotSurj : ¬ Function.Surjective H0.feitThompsonFocalSubgroupOf.subtype := by
      intro hsurj
      apply hfoc.ne
      apply top_unique
      intro x _
      obtain ⟨y, rfl⟩ := hsurj x
      exact y.2
    simpa only [Nat.card_eq_fintype_card] using
      Fintype.card_lt_of_injective_not_surjective
        H0.feitThompsonFocalSubgroupOf.subtype H0.feitThompsonFocalSubgroupOf.subtype_injective hnotSurj
  have hVsurj : Function.Surjective V := by
    intro y
    obtain ⟨x, hx⟩ := hkt_transferFocal_restrict_surjective (S := T) y
    exact ⟨x, by simpa [V, H0, MonoidHom.restrict_apply] using hx⟩
  have hkerinf : K ⊓ H0 = H0.feitThompsonFocalSubgroup := by
    simpa [K, V, H0] using
      (Subgroup.ker_feitThompsonTransferFocal_inf_eq_feitThompsonFocalSubgroup (P := T))
  let TK : Sylow p K := sylowSubgroupOfNormal T K
  have hTKmap :
      (TK : Subgroup K).map K.subtype = H0.feitThompsonFocalSubgroup := by
    rw [sylowSubgroupOfNormal_coe, Subgroup.comap_subtype,
      Subgroup.subgroupOf_map_subtype]
    simpa [inf_comm] using hkerinf
  have hTKcardEq : Nat.card TK = Nat.card H0.feitThompsonFocalSubgroupOf := by
    calc
      Nat.card TK = Nat.card ((TK : Subgroup K).map K.subtype) :=
        (Subgroup.card_map_of_injective
          (K := (TK : Subgroup K)) (f := K.subtype) K.subtype_injective).symm
      _ = Nat.card H0.feitThompsonFocalSubgroup := congrArg (fun L : Subgroup H => Nat.card L) hTKmap
      _ = Nat.card (H0.feitThompsonFocalSubgroupOf.map H0.subtype) :=
        congrArg (fun L : Subgroup H => Nat.card L) H0.map_feitThompsonFocalSubgroupOf.symm
      _ = Nat.card H0.feitThompsonFocalSubgroupOf :=
        Subgroup.card_map_of_injective
          (K := H0.feitThompsonFocalSubgroupOf) (f := H0.subtype) H0.subtype_injective
  have hTKcard : Nat.card TK < Nat.card T := hTKcardEq.trans_lt hfocCard
  have hTKmapP :
      (TK : Subgroup K).map (f.comp K.subtype) ≤ (P : Subgroup G) := by
    rw [sylowSubgroupOfNormal_coe]
    rintro z ⟨y, hy, rfl⟩
    apply hTmap
    exact Subgroup.mem_map.mpr ⟨(y : H), hy, rfl⟩
  have hKcomp : HasNormalPComplement p K :=
    hasNormalPComplement_of_controlled_fusion_embedding
      (f.comp K.subtype) (hf.comp K.subtype_injective) P TK hTKmapP hfusion
  have htargetP : IsPGroup p (H0 ⧸ H0.feitThompsonFocalSubgroupOf) :=
    T.isPGroup'.to_quotient H0.feitThompsonFocalSubgroupOf
  let e : H ⧸ K ≃* H0 ⧸ H0.feitThompsonFocalSubgroupOf :=
    QuotientGroup.quotientKerEquivOfSurjective V hVsurj
  have hquotP : IsPGroup p (H ⧸ K) := htargetP.of_equiv e.symm
  exact hkt_hasNormalPComplement_of_normal_subgroup_and_pgroup_quotient
    K hquotP hKcomp
termination_by Nat.card T
/-- Suzuki, *Group Theory II*, Chapter 5, Theorem 2.27, condition (v). -/
public theorem suzuki_ch5_theorem_2_27_v
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G)
    (hfusion : ∀ {x y : G}, x ∈ (P : Subgroup G) → y ∈ (P : Subgroup G) →
      (∃ g : G, g * x * g⁻¹ = y) →
        ∃ h : P, (h : G) * x * (h : G)⁻¹ = y) :
    HasNormalPComplement p G := by
  exact hasNormalPComplement_of_controlled_fusion_embedding
    (MonoidHom.id G) Function.injective_id P P (by simp) hfusion

end V
end Suzuki
end External
end CFSG.BenderSuzuki
