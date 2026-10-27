module

public import CFSG.Quasithin.Background.FFC4Zmod
public import CFSG.RankThree.GF2n.Stroth80.CarterSec11OmegaIrr
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Matrix

private theorem s16k_tri8_two_eq_zero_or_one {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (c : K) : c = 0 ∨ c = 1 := by
  by_cases hc : c = 0
  · exact Or.inl hc
  · right
    have hsub : Subsingleton Kˣ := by
      have hunits : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
      exact (Nat.card_eq_one_iff_unique.mp hunits).1
    haveI := hsub
    exact congrArg Units.val (Subsingleton.elim (Units.mk0 c hc) (1 : Kˣ))

theorem s16k_tri8_statedOmega_stable_eq_bot_or_top {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2)
    {S : Subgroup (Multiplicative (Fin 4 ⊕ Fin 4 → K))}
    (hS : ∀ γ : ↥(StatedOmega (StatedQuadPlus 4 K)), ∀ s ∈ S,
      natAct (StatedOmega (StatedQuadPlus 4 K)) γ s ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1)
    (by rw [Fintype.card_eq_nat_card, hK, pow_one])
  let W : Submodule K (Fin 4 ⊕ Fin 4 → K) :=
    { carrier := {w | Multiplicative.ofAdd w ∈ S}
      add_mem' := fun {a b} ha hb => S.mul_mem ha hb
      zero_mem' := S.one_mem
      smul_mem' := fun c w hw => by
        rcases s16k_tri8_two_eq_zero_or_one hK c with hc | hc
        · rw [hc, zero_smul]
          exact S.one_mem
        · rw [hc, one_smul]
          exact hw }
  have hW : ∀ g ∈ StatedOmega (StatedQuadPlus 4 K), ∀ w ∈ W,
      (g : Matrix.GeneralLinearGroup (Fin 4 ⊕ Fin 4) K) *ᵥ w ∈ W := by
    intro g hg w hw
    exact hS ⟨g, hg⟩ (Multiplicative.ofAdd w) hw
  rcases CFSG.RankThree.GF2n.Stroth80.submodule_eq_bot_or_top_of_statedOmega_quadPlus
    (m := 4) (K := K) (by norm_num) W hW with h | h
  · left
    refine (Subgroup.eq_bot_iff_forall S).2 fun p hp => ?_
    have h1 : Multiplicative.toAdd p ∈ W := hp
    rw [h, Submodule.mem_bot] at h1
    exact Multiplicative.toAdd.injective h1
  · right
    rw [Subgroup.eq_top_iff']
    intro p
    have h1 : Multiplicative.toAdd p ∈ W := by rw [h]; exact Submodule.mem_top
    exact h1

theorem s16k_tri8_isIrrOn_of_realizes {V : Type} [CommGroup V] [Finite V]
    {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {π : ↥(StatedOmega (StatedQuadPlus 4 K)) →* ↥H}
    (hR : (FFModel.nat (StatedOmega (StatedQuadPlus 4 K))).RealizesVia H U Z π) :
    IsIrrOn H U Z := by
  obtain ⟨f, hfs, hfk, hfe⟩ := CFSG.Quasithin.FFC.exists_natMap
    (Γ := StatedOmega (StatedQuadPlus 4 K)) hR
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine lt_of_le_of_ne hR.2.1 fun hZU => ?_
    let m : Multiplicative (Fin 4 ⊕ Fin 4 → K) :=
      Multiplicative.ofAdd (Pi.single (Sum.inl 0) (1 : K))
    have hm1 : m ≠ 1 := by
      intro h
      have h1 : (Pi.single (Sum.inl 0) (1 : K) : Fin 4 ⊕ Fin 4 → K) = 0 :=
        ofAdd_eq_one.mp h
      have h2 := congrFun h1 (Sum.inl 0)
      simp at h2
    obtain ⟨u, hu⟩ := hfs m
    have : f u = 1 := by
      apply (hfk u).2
      rw [hZU]
      exact u.2
    exact hm1 (hu.symm.trans this)
  · intro x hx u hu
    exact hR.2.2.2.1 ⟨x, hx⟩ u hu
  · intro x hx z hz
    exact hR.2.2.2.2.1 ⟨x, hx⟩ z hz
  · intro J hJstab hZJ hJU
    let S : Subgroup (Multiplicative (Fin 4 ⊕ Fin 4 → K)) := (J.subgroupOf U).map f
    have hSstable : ∀ γ : ↥(StatedOmega (StatedQuadPlus 4 K)), ∀ s ∈ S,
        natAct (StatedOmega (StatedQuadPlus 4 K)) γ s ∈ S := by
      intro γ s hs
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hs
      have hxu : (x : V) ∈ U := x.2
      have hxJ : (x : V) ∈ J := Subgroup.mem_subgroupOf.1 hx
      have hhu : (((π γ : ↥H) : MulAut V) (x : V)) ∈ U := hR.2.2.2.1 (π γ) _ hxu
      have hmemJ : (((π γ : ↥H) : MulAut V) (x : V)) ∈ J := hJstab (π γ) (π γ).2 _ hxJ
      have hx' : (⟨((π γ : ↥H) : MulAut V) (x : V), hhu⟩ : ↥U) ∈
          J.subgroupOf U := Subgroup.mem_subgroupOf.2 hmemJ
      rw [← hfe γ x hhu]
      exact Subgroup.mem_map.2 ⟨⟨_, hhu⟩, hx', rfl⟩
    rcases s16k_tri8_statedOmega_stable_eq_bot_or_top hK hSstable with hS | hS
    · left
      refine le_antisymm ?_ hZJ
      intro j hj
      have hjU : j ∈ U := hJU hj
      have hxJ : (⟨j, hjU⟩ : ↥U) ∈ J.subgroupOf U := Subgroup.mem_subgroupOf.2 hj
      have hxS : f ⟨j, hjU⟩ ∈ S := Subgroup.mem_map.2 ⟨⟨j, hjU⟩, hxJ, rfl⟩
      rw [hS, Subgroup.mem_bot] at hxS
      exact (hfk ⟨j, hjU⟩).1 hxS
    · right
      refine le_antisymm hJU ?_
      intro u hu
      have huS : f ⟨u, hu⟩ ∈ S := by rw [hS]; exact Subgroup.mem_top _
      obtain ⟨x, hx, hxf⟩ := Subgroup.mem_map.1 huS
      have hxJ : (x : V) ∈ J := Subgroup.mem_subgroupOf.1 hx
      have h1 : f (x⁻¹ * ⟨u, hu⟩) = 1 := by
        rw [map_mul, map_inv, hxf, inv_mul_cancel]
      have h2 : ((x⁻¹ * ⟨u, hu⟩ : ↥U) : V) ∈ Z := (hfk _).1 h1
      have h3 : ((x⁻¹ * ⟨u, hu⟩ : ↥U) : V) ∈ J := hZJ h2
      have hux : (⟨u, hu⟩ : ↥U) = x * (x⁻¹ * ⟨u, hu⟩) := by group
      show ((⟨u, hu⟩ : ↥U) : V) ∈ J
      rw [hux]
      show ((x * (x⁻¹ * ⟨u, hu⟩) : ↥U) : V) ∈ J
      rw [show ((x * (x⁻¹ * ⟨u, hu⟩) : ↥U) : V) =
          (x : V) * ((x⁻¹ * ⟨u, hu⟩ : ↥U) : V) from rfl]
      exact J.mul_mem hxJ h3

theorem s16k_tri8_map_fixV_le {V : Type} [CommGroup V] {H : Subgroup (MulAut V)}
    {s : MulAut V} (hs : s ∈ Subgroup.normalizer (H : Set (MulAut V))) :
    (fixV H).map s.toMonoidHom ≤ fixV H := by
  rintro w ⟨v, hv, rfl⟩
  refine mem_fixV.2 fun x hx => ?_
  have hconj : s * (s⁻¹ * x * s) * s⁻¹ = x := by group
  have hxt : s⁻¹ * x * s ∈ H :=
    (Subgroup.mem_normalizer_iff.1 hs (s⁻¹ * x * s)).2 (hconj.symm ▸ hx)
  have h1 : x * s = s * (s⁻¹ * x * s) := by group
  calc x (s v) = (x * s) v := rfl
    _ = (s * (s⁻¹ * x * s)) v := by rw [h1]
    _ = s ((s⁻¹ * x * s) v) := rfl
    _ = s v := by rw [hv (s⁻¹ * x * s) hxt]

theorem s16k_tri8_map_fixV_eq {V : Type} [CommGroup V] {H : Subgroup (MulAut V)}
    {s : MulAut V} (hs : s ∈ Subgroup.normalizer (H : Set (MulAut V))) :
    (fixV H).map s.toMonoidHom = fixV H := by
  refine le_antisymm (s16k_tri8_map_fixV_le hs) ?_
  have hsin : s⁻¹ ∈ Subgroup.normalizer (H : Set (MulAut V)) := Subgroup.inv_mem _ hs
  have hcomp : ((fixV H).map s⁻¹.toMonoidHom).map s.toMonoidHom = fixV H := by
    rw [Subgroup.map_map]
    have hone : s.toMonoidHom.comp s⁻¹.toMonoidHom = MonoidHom.id V := by ext v; simp
    rw [hone, Subgroup.map_id]
  calc fixV H = ((fixV H).map s⁻¹.toMonoidHom).map s.toMonoidHom := hcomp.symm
    _ ≤ (fixV H).map s.toMonoidHom := Subgroup.map_mono (s16k_tri8_map_fixV_le hsin)

theorem s16k_tri8_isIrrOn_map {V : Type} [CommGroup V] {H : Subgroup (MulAut V)}
    {I Z : Subgroup V} {g : MulAut V}
    (hg : g ∈ Subgroup.normalizer (H : Set (MulAut V)))
    (hZ : Z.map g.toMonoidHom = Z) (hirr : IsIrrOn H I Z) :
    IsIrrOn H (I.map g.toMonoidHom) Z := by
  have hZsymm : Z.map g.symm.toMonoidHom = Z := by
    have h := congrArg (fun S : Subgroup V => S.map g.symm.toMonoidHom) hZ
    rw [Subgroup.map_map,
      show g.symm.toMonoidHom.comp g.toMonoidHom = MonoidHom.id V from by ext v; simp,
      Subgroup.map_id] at h
    exact h.symm
  refine ⟨lt_of_le_of_ne (hZ ▸ Subgroup.map_mono (le_of_lt hirr.1)) ?_, ?_, hirr.2.2.1, ?_⟩
  · intro hge
    have h1 : I ≤ Z := by
      have h2 : I = Z := by
        calc I = (I.map g.toMonoidHom).map g.symm.toMonoidHom := by
              rw [Subgroup.map_map,
                show g.symm.toMonoidHom.comp g.toMonoidHom = MonoidHom.id V from by ext v; simp,
                Subgroup.map_id]
          _ = Z.map g.symm.toMonoidHom := by rw [← hge]
          _ = Z := hZsymm
      exact le_of_eq h2
    exact not_le_of_gt hirr.1 h1
  · intro x hx y hy
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hy
    refine Subgroup.mem_map.2 ⟨(g⁻¹ * x * g) w, ?_, ?_⟩
    · have hmem : g⁻¹ * x * g ∈ H :=
        (Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * x * g)).2 (by
          rw [show g * (g⁻¹ * x * g) * g⁻¹ = x by group]; exact hx)
      exact hirr.2.1 (g⁻¹ * x * g) hmem w hw
    · show g ((g⁻¹ * x * g) w) = x (g w)
      simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.apply_symm_apply]
  · intro J hJstab hZJ hJle
    have hJle' : J.map g.symm.toMonoidHom ≤ I := by
      calc J.map g.symm.toMonoidHom ≤ (I.map g.toMonoidHom).map g.symm.toMonoidHom :=
            Subgroup.map_mono hJle
        _ = I := by
            rw [Subgroup.map_map,
              show g.symm.toMonoidHom.comp g.toMonoidHom = MonoidHom.id V from by ext v; simp,
              Subgroup.map_id]
    have hZJ' : Z ≤ J.map g.symm.toMonoidHom := by
      calc Z = Z.map g.symm.toMonoidHom := hZsymm.symm
        _ ≤ J.map g.symm.toMonoidHom := Subgroup.map_mono hZJ
    have hJstab' : StableUnder H (J.map g.symm.toMonoidHom) := by
      intro x hx y hy
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hy
      refine Subgroup.mem_map.2 ⟨(g * x * g⁻¹) w, ?_, ?_⟩
      · exact hJstab (g * x * g⁻¹) ((Subgroup.mem_normalizer_iff.1 hg x).1 hx) w hw
      · show g.symm ((g * x * g⁻¹) w) = x (g.symm w)
        simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
    rcases hirr.2.2.2 (J.map g.symm.toMonoidHom) hJstab' hZJ' hJle' with h | h
    · left
      have := congrArg (fun S : Subgroup V => S.map g.toMonoidHom) h
      rwa [Subgroup.map_map,
        show g.toMonoidHom.comp g.symm.toMonoidHom = MonoidHom.id V from by ext v; simp,
        Subgroup.map_id, hZ] at this
    · right
      have := congrArg (fun S : Subgroup V => S.map g.toMonoidHom) h
      rwa [Subgroup.map_map,
        show g.toMonoidHom.comp g.symm.toMonoidHom = MonoidHom.id V from by ext v; simp,
        Subgroup.map_id] at this

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
