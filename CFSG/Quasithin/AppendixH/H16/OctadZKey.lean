module

public import CFSG.Quasithin.AppendixH.H16.OctadZIso
public import CFSG.Quasithin.AppendixH.H16.OctadZGroup
public import CFSG.Quasithin.AppendixH.H16.OctadZSpaces
public import CFSG.Quasithin.AppendixH.H16.OctadBetaInduce

public section

open scoped Pointwise

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.LU24
  CFSG.Monster.Code CFSG.ASVolI.AppH CFSG.Quasithin.H156

theorem card_ker_octPhi : Nat.card octPhi.ker = 16 := by
  rw [ker_octPhi, ← octFix_octad0]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (octFix_le_octStab octad0)).toEquiv).trans
    (card_octFix isOctad_octad0)

theorem octBeta_wz_gens :
    5 ∈ combos wz0Basis ∧ 453 ∈ combos wz0Basis ∧ 160 ∈ combos wz0Basis ∧
      actM octBetaCols 5 = 2 ∧ actM octBetaCols 453 = 8 ∧ actM octBetaCols 160 = 32 := by
  decide +kernel

@[expose] noncomputable def octT3 : Subgroup (Wn 6) := octWz.map octBeta

@[expose] noncomputable def octHs : Subgroup ↥(octStab octad0) :=
  (centSub octT3).comap octPhi

theorem mem_octHs_iff (γ : ↥(octStab octad0)) :
    γ ∈ octHs ↔ ∀ w ∈ octWz, octPhi γ (octBeta w) = octBeta w := by
  rw [octHs, Subgroup.mem_comap, mem_centSub, octT3]
  constructor
  · intro h w hw
    exact h (octBeta w) (Subgroup.mem_map.mpr ⟨w, hw, rfl⟩)
  · intro h t ht
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp ht
    exact h w hw

theorem ker_octPhi_le_octHs : octPhi.ker ≤ octHs := by
  intro γ hγ
  rw [mem_octHs_iff]
  intro w hw
  have h1 : octPhi γ = 1 := MonoidHom.mem_ker.mp hγ
  rw [h1]
  rfl

theorem dGrp_subgroupOf_le_octHs : dGrp.subgroupOf (octStab octad0) ≤ octHs := by
  intro γ hγ
  rw [mem_octHs_iff]
  intro w hw
  rw [Subgroup.mem_subgroupOf] at hγ
  obtain ⟨u, hu⟩ := mem_dGrp_iff.mp hγ
  rw [octWz, mem_maskSub] at hw
  obtain ⟨m, hm, rfl⟩ := hw
  have hρ : octRho γ (toW 11 m) = toW 11 (actC11 (dArr ↑u) m) := by
    rw [octRho_apply]
    have hsub : (⟨(γ : S24), octStab_octad0_le_AutPerm γ.2⟩ : ↥AutPerm) =
        ⟨dPerm u, dPerm_mem_M24g u⟩ := Subtype.ext hu.symm
    rw [hsub, rhoC11_dPerm]
  rw [octPhi_apply, hρ]
  have hker : toW 11 (actC11 (dArr ↑u) m ^^^ m) ∈ octV5 := by
    rw [octV5]
    exact toW_mem_maskSub (dArr_triv_wz_mod (u : ℕ) u.2 m hm)
  have hone : octBeta (toW 11 (actC11 (dArr ↑u) m ^^^ m)) = 1 :=
    (octBeta_eq_one_iff _).2 hker
  have hsplit : toW 11 (actC11 (dArr ↑u) m) =
      toW 11 (actC11 (dArr ↑u) m ^^^ m) * toW 11 m := by
    rw [← toW_xor]
    congr 1
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  rw [hsplit, map_mul, hone, one_mul]

theorem card_le_of_hom_range {G N : Type*} [Group G] [Group N] [Finite G] [Finite N] (φ : G →* N)
    {s : Set N} (hs : ∀ g, φ g ∈ s) {c : ℕ} (hc : Nat.card ↥s ≤ c) :
    Nat.card G ≤ Nat.card φ.ker * c := by
  have hsub : (φ.range : Set N) ⊆ s := by
    intro x hx
    obtain ⟨g, rfl⟩ := hx
    exact hs g
  have hinj : Function.Injective (Set.inclusion hsub : ↥φ.range → ↥s) :=
    Set.inclusion_injective hsub
  have hle : Nat.card ↥φ.range ≤ c :=
    (Nat.card_le_card_of_injective _ hinj).trans hc
  rw [← Subgroup.card_ker_mul_card_range φ]
  exact Nat.mul_le_mul_left _ hle

theorem card_octHs_le : Nat.card ↥octHs ≤ 128 := by
  classical
  obtain ⟨h5mem, h453mem, h160mem, h5, h453, h160⟩ := octBeta_wz_gens
  let s : Set (MulAut (Wn 6)) := {f | (∀ x : Fin 6 → ZMod 2,
      qPlus6 (Multiplicative.toAdd (f (Multiplicative.ofAdd x))) = qPlus6 x) ∧
      f (toW 6 2) = toW 6 2 ∧ f (toW 6 8) = toW 6 8 ∧ f (toW 6 32) = toW 6 32}
  have hc : Nat.card ↥s ≤ 8 := card_iso_fix_le
  haveI : Finite (MulAut (Wn 6)) :=
    Finite.of_injective (fun f : MulAut (Wn 6) => (f : Wn 6 → Wn 6))
      (fun f g h => MulEquiv.ext (congrFun h))
  haveI : Finite ↥octHs := Subtype.finite
  have hvect : ∀ g : ↥octHs, ∀ (a b : ℕ), a ∈ combos wz0Basis → actM octBetaCols a = b →
      (octPhi.comp octHs.subtype) g (toW 6 b) = toW 6 b := by
    intro g a b ha hab
    have h := (mem_octHs_iff g.1).1 g.2 (toW 11 a) (toW_mem_maskSub ha)
    have ha' : octBeta (toW 11 a) = toW 6 b := by rw [octBeta_toW, hab]
    show octPhi g.1 (toW 6 b) = toW 6 b
    rw [← ha']
    exact h
  have hs : ∀ g : ↥octHs, (octPhi.comp octHs.subtype) g ∈ s :=
    fun g => ⟨octPhi_isometry g.1, hvect g 5 2 h5mem h5, hvect g 453 8 h453mem h453,
      hvect g 160 32 h160mem h160⟩
  have hφker : (octPhi.comp octHs.subtype).ker = octPhi.ker.subgroupOf octHs := by
    rw [← MonoidHom.comap_ker octPhi octHs.subtype, Subgroup.comap_subtype]
  have h16 : Nat.card ↥(octPhi.ker.subgroupOf octHs) = 16 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe ker_octPhi_le_octHs).toEquiv).trans
      card_ker_octPhi
  calc Nat.card ↥octHs ≤ Nat.card ↥(octPhi.comp octHs.subtype).ker * 8 :=
        card_le_of_hom_range (octPhi.comp octHs.subtype) hs hc
    _ = 128 := by rw [hφker, h16]

theorem octHs_eq :
    octHs = (fixO ⊔ dGrp).subgroupOf (octStab octad0) := by
  have hsup : (fixO ⊔ dGrp).subgroupOf (octStab octad0) =
      fixO.subgroupOf (octStab octad0) ⊔ dGrp.subgroupOf (octStab octad0) :=
    Subgroup.subgroupOf_sup fixO_le_octStab_octad0 dGrp_le_octStab
  have hle : (fixO ⊔ dGrp).subgroupOf (octStab octad0) ≤ octHs := by
    rw [hsup]
    exact sup_le (by rw [← ker_octPhi]; exact ker_octPhi_le_octHs) dGrp_subgroupOf_le_octHs
  have hKG : fixO ⊔ dGrp ≤ octStab octad0 := sup_le fixO_le_octStab_octad0 dGrp_le_octStab
  have hcard : Nat.card ↥((fixO ⊔ dGrp).subgroupOf (octStab octad0)) = 128 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKG).toEquiv).trans card_fixO_sup_dGrp
  have hcardle : Nat.card ↥octHs ≤ Nat.card ↥((fixO ⊔ dGrp).subgroupOf (octStab octad0)) := by
    rw [hcard]
    exact card_octHs_le
  exact (Subgroup.eq_of_le_of_card_ge hle hcardle).symm

theorem key8 (γ : ↥AutPerm) (hγ : (γ : S24) ∈ octStab octad0)
    (h : ∀ w ∈ octWz, rhoC11 AutPerm le_rfl γ w * w⁻¹ ∈ octV5) : (γ : S24) ∈ fixO ⊔ dGrp := by
  let γ' : ↥(octStab octad0) := ⟨(γ : S24), hγ⟩
  have hγ' : γ' ∈ octHs := by
    rw [mem_octHs_iff]
    intro w hw
    have hfix : octBeta (rhoC11 AutPerm le_rfl γ w) = octBeta w := by
      have h1 := (octBeta_eq_one_iff (rhoC11 AutPerm le_rfl γ w * w⁻¹)).2 (h w hw)
      rw [map_mul, map_inv] at h1
      exact mul_inv_eq_one.mp h1
    rw [octPhi_apply, octRho_apply]
    have hsub : (⟨(γ' : S24), octStab_octad0_le_AutPerm γ'.2⟩ : ↥AutPerm) = γ := Subtype.ext rfl
    rw [hsub, hfix]
  rw [octHs_eq] at hγ'
  exact Subgroup.mem_subgroupOf.mp hγ'

end CFSG.ASVolI.H16
