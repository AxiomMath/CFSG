module

public import CFSG.LocalAnalysis.StandardType.GGTwE6KGA1Defs
public import CFSG.LocalAnalysis.StandardType.GGTwE6KGA1Bridge
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType.NoOffTwE6Three

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.Open

private theorem o4_conj_mem_torusGroup {f : ℕ} (hf : 1 ≤ f)
    {Xh : Subgroup ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hel : IsElemAbelian 3 Xh) (hc : Nat.card Xh = 3 ^ 4)
    (hη : ∀ x ∈ Xh, diagramMap TwistTag.E6 (GaloisField 2 (2 * f)) *
      (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) *
        (diagramMap TwistTag.E6 (GaloisField 2 (2 * f)))⁻¹ = x) :
    ∃ γ : twistedFixedGroup TwistTag.E6 (GaloisField 2 (2 * f))
        (RingHom.id (GaloisField 2 (2 * f))),
      ∀ x ∈ Xh, (γ : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) *
        (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) *
          (γ : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))⁻¹ ∈
            torusGroup Tag.E6 (GaloisField 2 (2 * f)) := by
  let K := GaloisField 2 (2 * f)
  let C₀ : Subgroup (ModGL TwistTag.E6.tag K) :=
    graphFixedRootGroup TwistTag.E6 K (frobQ 2 f)
  let Γ : Subgroup (ModGL TwistTag.E6.tag K) := twistedFixedGroup TwistTag.E6 K (RingHom.id K)
  let Ψ : Γ ≃* adjointGroup Tag.F4 K :=
    CFSG.HardMathSupport.Lang.AnisoE6.e6FixedF4EquivAll K
  have hle : C₀ ≤ twistedFixedGroup TwistTag.E6 K (frobQ 2 f) :=
    graphFixedRootGroup_le TwistTag.E6 K (frobQ 2 f)
  let H : Subgroup ↥C₀ := Γ.comap (Subgroup.subtype C₀)
  have hη' : ∀ x ∈ Xh, diagramMap TwistTag.E6 K * (x : ModGL TwistTag.E6.tag K) =
      (x : ModGL TwistTag.E6.tag K) * diagramMap TwistTag.E6 K := by
    intro x hx
    calc diagramMap TwistTag.E6 K * (x : ModGL TwistTag.E6.tag K)
        = diagramMap TwistTag.E6 K * (x : ModGL TwistTag.E6.tag K) *
            (diagramMap TwistTag.E6 K)⁻¹ * diagramMap TwistTag.E6 K := by group
      _ = (x : ModGL TwistTag.E6.tag K) * diagramMap TwistTag.E6 K := by rw [hη x hx]
  have hXH : Xh ≤ H := by
    intro x hx
    rw [Subgroup.mem_comap]
    exact mem_twistedFixedGroup_id_iff.mpr ⟨(hle x.2).1, hη' x hx⟩
  let pC : ↥H →* ↥Γ :=
    ((Subgroup.subtype C₀).comp (Subgroup.subtype H)).codRestrict Γ
      (fun y => Subgroup.mem_comap.mp y.2)
  let XhH : Subgroup ↥H := Xh.subgroupOf H
  let XΓ : Subgroup ↥Γ := XhH.map pC
  have hpCinj : Function.Injective pC := by
    intro a b h
    have h' : (a.1 : ModGL TwistTag.E6.tag K) = (b.1 : ModGL TwistTag.E6.tag K) :=
      congrArg (fun z : ↥Γ => (z : ModGL TwistTag.E6.tag K)) h
    exact Subtype.ext (Subtype.ext h')
  have hXΓ : IsElemAbelian 3 XΓ := (hel.subgroupOf H).map pC
  let E : Subgroup (adjointGroup Tag.F4 K) := XΓ.map Ψ.toMonoidHom
  have hE : IsElemAbelian 3 E := hXΓ.map Ψ.toMonoidHom
  have hcardXhH : Nat.card XhH = Nat.card Xh :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv
  have hcardXΓ : Nat.card XΓ = Nat.card XhH :=
    Subgroup.card_map_of_injective hpCinj
  have hcardE : Nat.card E = Nat.card XΓ :=
    Subgroup.card_map_of_injective Ψ.injective
  have hcard : Nat.card E = 3 ^ 4 := by
    rw [hcardE, hcardXΓ, hcardXhH, hc]
  have h3 : 3 ∣ Nat.card K - 1 := by
    have hK : Nat.card K = 4 ^ f := by
      change Nat.card (GaloisField 2 (2 * f)) = 4 ^ f
      rw [GaloisField.card 2 (2 * f) (by omega), pow_mul]
      norm_num
    rw [hK]
    simpa using Nat.sub_dvd_pow_sub_pow 4 1 f
  obtain ⟨g₄, hg₄⟩ :=
    TableBF4.ggF4ToralRankInput_three (K := K) h3 E hE (le_of_eq hcard.symm)
  let γ : ↥Γ := Ψ.symm g₄
  refine ⟨γ, ?_⟩
  intro x hx
  have hxΓ : (x : ModGL TwistTag.E6.tag K) ∈ Γ :=
    mem_twistedFixedGroup_id_iff.mpr ⟨(hle x.2).1, hη' x hx⟩
  let xF : ↥Γ := ⟨x, hxΓ⟩
  have hxF_mem_XΓ : xF ∈ XΓ := by
    change xF ∈ XhH.map pC
    rw [Subgroup.mem_map]
    refine ⟨⟨x, hXH hx⟩, ?_, ?_⟩
    · change x ∈ Xh
      exact hx
    · exact Subtype.ext rfl
  have hxF_mem_E : Ψ xF ∈ E := by
    change Ψ xF ∈ XΓ.map Ψ.toMonoidHom
    rw [Subgroup.mem_map]
    exact ⟨xF, hxF_mem_XΓ, rfl⟩
  have hconj : (MulAut.conj g₄).toMonoidHom (Ψ xF) ∈ TableBF4.torusPow K 3 := by
    rw [← hg₄, Subgroup.mem_map]
    exact ⟨Ψ xF, hxF_mem_E, rfl⟩
  have hΨγ : Ψ γ = g₄ := MulEquiv.apply_symm_apply Ψ g₄
  have hbridge : (Ψ (γ * xF * γ⁻¹) : ModGL Tag.F4 K) ∈ torusGroup Tag.F4 K := by
    have hval : Ψ (γ * xF * γ⁻¹) = (MulAut.conj g₄).toMonoidHom (Ψ xF) := by
      rw [map_mul, map_mul, map_inv, hΨγ]
      rfl
    rw [hval]
    exact (TableBF4.mem_torusPow.mp hconj).1
  have hbridge2 : ((γ * xF * γ⁻¹ : ↥Γ) : ModGL TwistTag.E6.tag K) ∈ torusGroup Tag.E6 K :=
    e6FixedF4EquivAll_symm_mem_torusGroup (γ * xF * γ⁻¹) hbridge
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hbridge2

theorem isToralE6_map_baseChange_of_diagramMap_commute {f : ℕ} (hf : 1 ≤ f) (Ω : Type) [Field Ω]
    [Algebra (GaloisField 2 (2 * f)) Ω] [IsAlgClosure (GaloisField 2 (2 * f)) Ω]
    {Xh : Subgroup ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hel : IsElemAbelian 3 Xh) (hc : Nat.card Xh = 3 ^ 4)
    (hη : ∀ x ∈ Xh, diagramMap TwistTag.E6 (GaloisField 2 (2 * f)) *
      (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) *
        (diagramMap TwistTag.E6 (GaloisField 2 (2 * f)))⁻¹ = x) :
    IsToralE6 Ω (Xh.map ((baseChangeGL (algebraMap (GaloisField 2 (2 * f)) Ω)).comp
      (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)).subtype)) := by
  obtain ⟨γ, hγ⟩ := o4_conj_mem_torusGroup hf hel hc hη
  refine ⟨(baseChangeGL (algebraMap (GaloisField 2 (2 * f)) Ω)
    (γ : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))))⁻¹, ?_, ?_⟩
  · exact inv_mem (baseChangeGL_mem_adjointGroup
      (algebraMap (GaloisField 2 (2 * f)) Ω) γ.2.1)
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    change (baseChangeGL (algebraMap (GaloisField 2 (2 * f)) Ω)
        (γ : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))))⁻¹⁻¹ *
      baseChangeGL (algebraMap (GaloisField 2 (2 * f)) Ω)
        (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) *
      (baseChangeGL (algebraMap (GaloisField 2 (2 * f)) Ω)
        (γ : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))))⁻¹ ∈ torusGroup Tag.E6 Ω
    rw [inv_inv]
    have hh : baseChangeGL (algebraMap (GaloisField 2 (2 * f)) Ω)
        ((γ : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) *
          (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) *
            (γ : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))⁻¹) ∈
          torusGroup Tag.E6 Ω :=
      CFSG.RankThree.Classical2.baseChangeGL_mem_torusGroup
        (algebraMap (GaloisField 2 (2 * f)) Ω) (hγ x hx)
    rw [map_mul, map_mul, map_inv] at hh
    exact hh

end CFSG.StandardType.NoOffTwE6Three
