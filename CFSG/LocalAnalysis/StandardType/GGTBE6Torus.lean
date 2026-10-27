module

public import CFSG.LocalAnalysis.StandardType.GGTBTorDefs
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryDesc
public import CFSG.LieType.Steinberg.Isogeny.E6
public import CFSG.LieType.Steinberg.CentralExt.MinusculeCenter
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeScLift
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelClassify
public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier

public noncomputable section

namespace CFSG.StandardType.TBE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


section Coordinates

variable {K L : Type} [Field K] [Group L]
  (ρ : MulAut L →* MulAut (adjointGroup .E6 K))
  (e : Kˣ ≃* Multiplicative (ZMod (Nat.card K - 1)))

@[expose] def torus : Subgroup (MulAut L) :=
  (rootDiagAutHom .E6 K).range.comap ρ

@[expose] def root (i : Fin Tag.E6.rank) (τ : MulAut L) :
    Multiplicative (ZMod (Nat.card K - 1)) :=
  e (Function.invFun (rootDiagAutHom .E6 K) (ρ τ) i)

@[expose] def coroot (φ : e6Data_valid.minGroup K →* L) (i : Fin Tag.E6.rank) :
    Multiplicative (ZMod (Nat.card K - 1)) →* L :=
  (φ.comp (e6Data_valid.hHom K i)).comp e.symm.toMonoidHom

theorem root_apply (i : Fin Tag.E6.rank) {τ : MulAut L}
    {b : Fin Tag.E6.rank → Kˣ} (hb : ρ τ = rootDiagAutHom .E6 K b) :
    root ρ e i τ = e (b i) := by
  rw [root, hb, Function.leftInverse_invFun rootDiagAutHom_injective b]

theorem root_mul (i : Fin Tag.E6.rank)
    {τ υ : MulAut L} (hτ : τ ∈ torus ρ) (hυ : υ ∈ torus ρ) :
    root ρ e i (τ * υ) = root ρ e i τ * root ρ e i υ := by
  obtain ⟨b, hb⟩ := hτ
  obtain ⟨c, hc⟩ := hυ
  have hbc : ρ (τ * υ) = rootDiagAutHom .E6 K (b * c) := by
    rw [map_mul, ← hb, ← hc, map_mul]
  rw [root_apply ρ e i hbc, root_apply ρ e i hb.symm, root_apply ρ e i hc.symm]
  exact map_mul e (b i) (c i)

theorem root_separates (hρ : Function.Injective ρ) {τ : MulAut L}
    (hτ : τ ∈ torus ρ) (h : ∀ i, root ρ e i τ = 1) : τ = 1 := by
  obtain ⟨b, hb⟩ := hτ
  have hb1 : b = 1 := by
    funext i
    apply e.injective
    change e (b i) = e 1
    rw [map_one]
    exact (root_apply ρ e i hb.symm).symm.trans (h i)
  apply hρ
  rw [← hb, hb1, map_one, map_one]

theorem torus_comm (hρ : Function.Injective ρ) {τ υ : MulAut L}
    (hτ : τ ∈ torus ρ) (hυ : υ ∈ torus ρ) : τ * υ = υ * τ := by
  obtain ⟨b, hb⟩ := hτ
  obtain ⟨c, hc⟩ := hυ
  apply hρ
  rw [map_mul, map_mul, ← hb, ← hc, ← map_mul, ← map_mul, mul_comm b c]

end Coordinates

section Coroots

variable {K L : Type} [Field K] [Group L]

section Isogeny


variable [Finite K]
  (ψ : L →* adjointGroup .E6 K) (φ : e6Data_valid.minGroup K →* L)
  (hφ : ∀ x, ψ (φ x) = e6Isogeny K x)

include hφ

theorem coroot_injective
    (e : Kˣ ≃* Multiplicative (ZMod (Nat.card K - 1))) (i : Fin Tag.E6.rank) :
    Function.Injective (coroot e φ i) := by
  intro s t hst
  have hst' := congrArg (fun l => (ψ l : ModGL .E6 K)) hst
  change (ψ (φ (e6Data_valid.hm K i (e.symm s))) : ModGL .E6 K) =
    (ψ (φ (e6Data_valid.hm K i (e.symm t))) : ModGL .E6 K) at hst'
  rw [hφ, hφ, e6Isogeny_hm_eq, e6Isogeny_hm_eq] at hst'
  have hu := (CFSG.LieType.Chevalley.rootDiagUnit_injective (K := K)) hst'
  obtain ⟨j, hj⟩ := neighbour_E6 i
  have hij : Tag.E6.cartan i j = -1 := by
    rw [show Tag.E6.cartan i j = Tag.E6.cartan j i from by
      change Tag.cartanE 6 i j = Tag.cartanE 6 j i
      unfold Tag.cartanE
      split_ifs <;> omega]
    exact hj
  have hst'' := congrFun hu j
  rw [hij, zpow_neg_one, zpow_neg_one] at hst''
  have he : e.symm s = e.symm t := inv_injective hst''
  exact e.symm.injective he

theorem coroot_desc
    (ρ : MulAut L →* MulAut (adjointGroup .E6 K))
    (hρ : ∀ a l, ρ a (ψ l) = ψ (a l))
    (hψ : Function.Surjective ψ)
    (e : Kˣ ≃* Multiplicative (ZMod (Nat.card K - 1)))
    (i : Fin Tag.E6.rank) (s : Multiplicative (ZMod (Nat.card K - 1))) :
    ρ (MulAut.conj (coroot e φ i s)) =
      rootDiagAutHom .E6 K (fun j => e.symm s ^ Tag.E6.cartan i j) := by
  rw [E6ThreeModel.rho_conj hψ hρ]
  refine MulEquiv.ext fun g => Subtype.ext ?_
  change (ψ (coroot e φ i s) : ModGL .E6 K) * g *
      (ψ (coroot e φ i s) : ModGL .E6 K)⁻¹ =
    rootDiagUnit .E6 (fun j => e.symm s ^ Tag.E6.cartan i j) * g *
      (rootDiagUnit .E6 (fun j => e.symm s ^ Tag.E6.cartan i j))⁻¹
  change (ψ (φ (e6Data_valid.hm K i (e.symm s))) : ModGL .E6 K) * g *
      (ψ (φ (e6Data_valid.hm K i (e.symm s))) : ModGL .E6 K)⁻¹ = _
  rw [hφ, e6Isogeny_hm_eq]

theorem coroot_mem_torus
    (ρ : MulAut L →* MulAut (adjointGroup .E6 K))
    (hρ : ∀ a l, ρ a (ψ l) = ψ (a l))
    (hψ : Function.Surjective ψ)
    (e : Kˣ ≃* Multiplicative (ZMod (Nat.card K - 1)))
    (i : Fin Tag.E6.rank) (s : Multiplicative (ZMod (Nat.card K - 1))) :
    MulAut.conj (coroot e φ i s) ∈ torus ρ :=
  ⟨_, (coroot_desc ψ φ hφ ρ hρ hψ e i s).symm⟩

theorem root_coroot
    (ρ : MulAut L →* MulAut (adjointGroup .E6 K))
    (hρ : ∀ a l, ρ a (ψ l) = ψ (a l))
    (hψ : Function.Surjective ψ)
    (e : Kˣ ≃* Multiplicative (ZMod (Nat.card K - 1)))
    (i j : Fin Tag.E6.rank) (s : Multiplicative (ZMod (Nat.card K - 1))) :
    root ρ e j (MulAut.conj (coroot e φ i s)) = s ^ Tag.E6.cartan i j := by
  rw [root_apply ρ e j (coroot_desc ψ φ hφ ρ hρ hψ e i s), map_zpow,
    e.apply_symm_apply]

omit hφ in
theorem torusGroup_le_map_minTorus :
    torusGroup .E6 K ≤ (minTorus e6Data_valid K).range.map
      ((adjointGroup .E6 K).subtype.comp (e6Isogeny K)) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨⟨i, s⟩, rfl⟩
  refine ⟨e6Data_valid.hm K i s,
    ⟨Pi.mulSingle i s, minTorus_mulSingle e6Data_valid K i s⟩, ?_⟩
  change (e6Isogeny K (e6Data_valid.hm K i s) : ModGL .E6 K) = torusElt .E6 K i s
  rw [e6Isogeny_hm_eq, torusElt_eq_rootDiagUnit]

omit hφ in
theorem mem_minTorus_range_of_isogeny_mem_torus {x : e6Data_valid.minGroup K}
    (hx : (e6Isogeny K x : ModGL .E6 K) ∈ torusGroup .E6 K) :
    x ∈ (minTorus e6Data_valid K).range := by
  obtain ⟨y, hy, hyx⟩ := (torusGroup_le_map_minTorus (K := K)) hx
  have hz : y⁻¹ * x ∈ (e6Isogeny K).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
    exact Subtype.ext hyx
  have hzT := center_le_range_minTorus e6Data_valid K isFiniteType_cartan_E6
    (e6Datum_isCTGroupDatum K) (e6Datum_steinbergExtras K) (e6Datum_bruhatExtras K)
    ((CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center
      (K := K)) ▸ hz)
  simpa using mul_mem hy hzT

theorem mem_coroot_torus_of_map_mem_torus
    (hφs : Function.Surjective φ)
    (_e : Kˣ ≃* Multiplicative (ZMod (Nat.card K - 1))) {l : L}
    (hl : (ψ l : ModGL .E6 K) ∈ torusGroup .E6 K) :
    l ∈ (φ.comp (minTorus e6Data_valid K)).range := by
  obtain ⟨x, rfl⟩ := hφs l
  have hx : x ∈ (minTorus e6Data_valid K).range :=
    mem_minTorus_range_of_isogeny_mem_torus (by rwa [hφ] at hl)
  obtain ⟨u, hu⟩ := hx
  exact ⟨u, by rw [MonoidHom.comp_apply, hu]⟩

end Isogeny

theorem coroot_commute (φ : e6Data_valid.minGroup K →* L)
    (e : Kˣ ≃* Multiplicative (ZMod (Nat.card K - 1)))
    (i j : Fin Tag.E6.rank) (s t : Multiplicative (ZMod (Nat.card K - 1))) :
    Commute (coroot e φ i s) (coroot e φ j t) := by
  change Commute (φ (e6Data_valid.hm K i (e.symm s)))
    (φ (e6Data_valid.hm K j (e.symm t)))
  exact (show Commute (e6Data_valid.hm K i (e.symm s))
      (e6Data_valid.hm K j (e.symm t)) from
    e6Data_valid.torus_commute K i j
      (e6Data_valid.hm_mem_torus K i (e.symm s))
      (e6Data_valid.hm_mem_torus K j (e.symm t))).map φ

theorem iSup_coroot_range (φ : e6Data_valid.minGroup K →* L)
    (e : Kˣ ≃* Multiplicative (ZMod (Nat.card K - 1))) :
    (⨆ i, (coroot e φ i).range) = (φ.comp (minTorus e6Data_valid K)).range := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    rintro _ ⟨s, rfl⟩
    refine ⟨Pi.mulSingle i (e.symm s), ?_⟩
    change φ (minTorus e6Data_valid K (Pi.mulSingle i (e.symm s))) =
      φ (e6Data_valid.hm K i (e.symm s))
    rw [minTorus_mulSingle]
  · rintro _ ⟨u, rfl⟩
    induction u using CFSG.LieType.Chevalley.ExceptionalCover.torusVec_induction with
    | h1 => simp
    | hmul u v hu hv =>
      simpa only [MonoidHom.comp_apply, map_mul] using
        (⨆ i, (coroot e φ i).range).mul_mem hu hv
    | hsingle i s =>
      rw [MonoidHom.comp_apply, minTorus_mulSingle]
      exact Subgroup.mem_iSup_of_mem i ⟨e s, by
        change φ (e6Data_valid.hm K i (e.symm (e s))) = φ (e6Data_valid.hm K i s)
        rw [e.symm_apply_apply]⟩

end Coroots

end CFSG.StandardType.TBE6
