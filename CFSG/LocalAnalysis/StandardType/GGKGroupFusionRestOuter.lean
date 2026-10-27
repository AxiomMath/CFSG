module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionAltDefining
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def GGLieOutRankTwoInput : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, Finite (TauCeti.CFSGIndex.lie d).Group →
    IsSimpleGroup (TauCeti.CFSGIndex.lie d).Group →
      (∃ a b : (TauCeti.CFSGIndex.lie d).Group, a * b ≠ b * a) → d.1.characteristic ≠ 2 →
        ∀ E : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group),
          IsElemAbelian d.1.characteristic E → Nat.card E = d.1.characteristic ^ 2 →
            E ⊓ (MulAut.conj : (TauCeti.CFSGIndex.lie d).Group →* MulAut _).range = ⊥ →
              ∃ q : TauCeti.PrimePower, d.1 = .D 4 q ∧ q.p = 3 ∧ 3 ∣ q.exponent

@[expose] def GGD4FieldAutMaximalInput : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower), d.1 = .D 4 q → q.p = 3 →
    3 ∣ q.exponent → Finite (TauCeti.CFSGIndex.lie d).Group →
      IsSimpleGroup (TauCeti.CFSGIndex.lie d).Group →
        (∃ a b : (TauCeti.CFSGIndex.lie d).Group, a * b ≠ b * a) →
          ∀ E : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group), IsElemAbelian 3 E →
            Nat.card E = 9 →
              E ⊓ (MulAut.conj : (TauCeti.CFSGIndex.lie d).Group →* MulAut _).range = ⊥ →
                ∃ e ∈ E, e ≠ 1 ∧ IsCoatom (fixedSubgroup e) ∧ 3 ∣ (fixedSubgroup e).index

theorem ggLieOuterFieldAutInput_of (h1 : GGLieOutRankTwoInput) (h2 : GGD4FieldAutMaximalInput) :
    GGLieOuterFieldAutInput := by
  intro W _ _ E d hsimple hnab ⟨φ⟩ hp2 hE hEcard hEK
  have hKn : (CFSG.generalizedFitting W).Normal :=
    CFSG.LocalCores.generalized_fitting_characteristic.2
  set K := CFSG.generalizedFitting W with hKdef
  set ρ : W →* MulAut (TauCeti.CFSGIndex.lie d).Group :=
    (MulAut.congr φ).toMonoidHom.comp (MulAut.conjNormal (H := K)) with hρ
  have hρapply : ∀ (w : W) (k : ↥K), ρ w (φ k) = φ ⟨w * k * w⁻¹, hKn.conj_mem _ k.2 w⟩ := by
    intro w k
    rw [hρ, MonoidHom.comp_apply]
    change (MulAut.congr φ (MulAut.conjNormal w)) (φ k) = _
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
    congr 1
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro w hw
    rw [MonoidHom.mem_ker] at hw
    rw [Subgroup.mem_bot]
    apply ggEq_one_of_commute_generalizedFitting hsimple hnab
    intro k hk
    have h := congrArg (fun α : MulAut (TauCeti.CFSGIndex.lie d).Group => α (φ ⟨k, hk⟩)) hw
    simp only [hρapply, MulAut.one_apply] at h
    have h' : w * k * w⁻¹ = k := congrArg Subtype.val (φ.injective h)
    calc w * k = w * k * w⁻¹ * w := by group
      _ = k * w := by rw [h']
  have hρinner : ∀ k : ↥K, ρ k = MulAut.conj (φ k) := by
    intro k
    ext c
    obtain ⟨k', rfl⟩ := φ.surjective c
    rw [hρapply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
  set Ebar := E.map ρ with hEbar
  have hEbarE : IsElemAbelian d.1.characteristic Ebar := ggIsElemAbelian_map hE ρ
  have hEbarCard : Nat.card Ebar = d.1.characteristic ^ 2 := by
    rw [hEbar, Subgroup.card_map_of_injective hρinj, hEcard]
  have hEbarInn : Ebar ⊓ (MulAut.conj : (TauCeti.CFSGIndex.lie d).Group →* MulAut _).range = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨e, he, rfl⟩, ⟨c, hc⟩⟩
    obtain ⟨k, rfl⟩ := φ.surjective c
    have hek : e = k := hρinj (hc.symm.trans (hρinner k).symm)
    have heK : e ∈ E ⊓ K := ⟨he, hek ▸ k.2⟩
    rw [hEK, Subgroup.mem_bot] at heK
    rw [Subgroup.mem_bot, heK, map_one]
  have hfin : Finite (TauCeti.CFSGIndex.lie d).Group := Finite.of_equiv _ φ.toEquiv
  have hsimple' : IsSimpleGroup (TauCeti.CFSGIndex.lie d).Group :=
    (MulEquiv.isSimpleGroup_congr φ).mp hsimple
  have hnab' : ∃ a b : (TauCeti.CFSGIndex.lie d).Group, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨φ a, φ b, fun h => hab (φ.injective ?_)⟩
    rw [map_mul, map_mul, h]
  obtain ⟨q, hdq, hq3, hq3a⟩ := h1 d hfin hsimple' hnab' hp2 Ebar hEbarE hEbarCard hEbarInn
  have hp3 : d.1.characteristic = 3 := by
    rw [hdq, TauCeti.LieTypeIndex.characteristic_D]
    exact hq3
  rw [hp3] at hEbarE hEbarCard
  obtain ⟨_, ⟨e, he, rfl⟩, hebar1, hcoatom, hidx⟩ :=
    h2 d q hdq hq3 hq3a hfin hsimple' hnab' Ebar hEbarE (by rw [hEbarCard]; norm_num) hEbarInn
  refine ⟨e, he, fun h => hebar1 (by rw [h, map_one]), fun Y hYK hCY hidxY => ?_⟩
  set Y' : Subgroup (TauCeti.CFSGIndex.lie d).Group :=
    (Y.subgroupOf K).map (φ : ↥K →* (TauCeti.CFSGIndex.lie d).Group) with hY'
  have hCY' : fixedSubgroup (ρ e) ≤ Y' := by
    intro c hc
    obtain ⟨k, rfl⟩ := φ.surjective c
    have hfix : ρ e (φ k) = φ k := hc
    rw [hρapply] at hfix
    have hk : e * k * e⁻¹ = k := congrArg Subtype.val (φ.injective hfix)
    have hkC : (k : W) ∈ Subgroup.centralizer ({e} : Set W) ⊓ K := by
      refine ⟨Subgroup.mem_centralizer_iff.mpr ?_, k.2⟩
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      calc e * k = e * k * e⁻¹ * e := by group
        _ = k * e := by rw [hk]
    exact ⟨k, Subgroup.mem_subgroupOf.mpr (hCY hkC), rfl⟩
  have hidx' : Y'.index = Y.relIndex K := Subgroup.index_map_equiv (Y.subgroupOf K) φ
  rcases hcoatom.le_iff.mp hCY' with htop | heq
  · apply le_antisymm hYK
    intro k hk
    have hk' : φ ⟨k, hk⟩ ∈ (Y.subgroupOf K).map (φ : ↥K →* (TauCeti.CFSGIndex.lie d).Group) := by
      rw [← hY', htop]
      exact Subgroup.mem_top _
    obtain ⟨k', hk'Y, hkk'⟩ := hk'
    have hk'eq : k' = ⟨k, hk⟩ := φ.injective hkk'
    rw [hk'eq] at hk'Y
    exact Subgroup.mem_subgroupOf.mp hk'Y
  · exfalso
    apply hidxY
    rw [hp3, ← hidx', heq]
    exact hidx

end CFSG.StandardType
