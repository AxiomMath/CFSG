module

public import CFSG.LocalAnalysis.UniquenessCase.UC22SeedAct
public import CFSG.LocalAnalysis.UniquenessCase.UC22SeedSF
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellSeed
public import CFSG.Quasithin.Background.E2Three

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique.Setup.Campbell
open Matrix (SpecialLinearGroup)
open scoped commutatorElement

section Transport

variable {G : Type} [Group G] {V : Subgroup G} [V.Normal] (hV : IsElemAbelian 2 V)

@[expose] def natSeedValHom : IntMod V hV →* G where
  toFun := IntMod.val
  map_one' := IntMod.val_one
  map_mul' := IntMod.val_mul

theorem commutator_top_eq_map_commV :
    ⁅V, (⊤ : Subgroup G)⁆ = (commV (autI hV (⊤ : Subgroup G))).map (natSeedValHom hV) := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro v hv l _
    set w : IntMod V hV := IntMod.mk hV ⟨v, hv⟩ with hw
    refine ⟨convI hV ⟨l, mem_normalizer_of_normal l⟩ w⁻¹ * (w⁻¹)⁻¹,
      Subgroup.subset_closure ⟨_, convI_mem_autI hV (Subgroup.mem_top l) (mem_normalizer_of_normal l), w⁻¹, rfl⟩,
      ?_⟩
    change IntMod.val (convI hV ⟨l, mem_normalizer_of_normal l⟩ w⁻¹ * (w⁻¹)⁻¹) = ⁅v, l⁆
    rw [IntMod.val_mul, convI_apply_val, inv_inv, IntMod.val_inv]
    have hv' : w.val = v := rfl
    rw [hv', commutatorElement_def]
    have hc : l * v⁻¹ * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (mem_normalizer_of_normal l) v⁻¹).1 (V.inv_mem hv)
    have := IntMod.val_comm (IntMod.mk hV ⟨l * v⁻¹ * l⁻¹, hc⟩) w
    calc l * v⁻¹ * l⁻¹ * v = v * (l * v⁻¹ * l⁻¹) := this
      _ = v * l * v⁻¹ * l⁻¹ := by group
  · rw [Subgroup.map_le_iff_le_comap]
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨φ, hφ, v, rfl⟩ := hx
      obtain ⟨g, -, rfl⟩ := (mem_autI hV).1 hφ
      change IntMod.val (convI hV g v * v⁻¹) ∈ ⁅V, (⊤ : Subgroup G)⁆
      rw [IntMod.val_mul, convI_apply_val, IntMod.val_inv, Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) v.val_mem
    | one => exact Subgroup.one_mem _
    | mul x y _ _ hx hy => exact Subgroup.mul_mem _ hx hy
    | inv x _ hx => exact Subgroup.inv_mem _ hx

theorem mk_mem_commV_autI_top {w : G} (hw : w ∈ ⁅V, (⊤ : Subgroup G)⁆) (hwV : w ∈ V) :
    IntMod.mk hV ⟨w, hwV⟩ ∈ commV (autI hV (⊤ : Subgroup G)) := by
  rw [commutator_top_eq_map_commV hV] at hw
  obtain ⟨u, hu, huw⟩ := hw
  have : u = IntMod.mk hV ⟨w, hwV⟩ := IntMod.val_injective huw
  rwa [← this]

theorem val_mem_commutator_top {m : IntMod V hV} (hm : m ∈ commV (autI hV (⊤ : Subgroup G))) :
    m.val ∈ ⁅V, (⊤ : Subgroup G)⁆ := by
  rw [commutator_top_eq_map_commV hV]
  exact ⟨m, hm, rfl⟩

@[expose] def natSeedCommTo :
    ↥(⁅V, (⊤ : Subgroup G)⁆) →* ↥(commV (autI hV (⊤ : Subgroup G))) where
  toFun x := ⟨IntMod.mk hV ⟨x.1, Subgroup.commutator_le_left V ⊤ x.2⟩, mk_mem_commV_autI_top hV x.2 _⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

theorem natSeedCommTo_val (x : ↥(⁅V, (⊤ : Subgroup G)⁆)) :
    ((natSeedCommTo hV x : ↥(commV (autI hV (⊤ : Subgroup G)))) : IntMod V hV).val = (x : G) :=
  rfl

end Transport

section TwoResidual

variable {G : Type} [Group G] [Finite G] {V : Subgroup G} [V.Normal] (hV : IsElemAbelian 2 V)

theorem autI_top_le_normalizer_autI_twoResidual :
    autI hV (⊤ : Subgroup G) ≤
      Subgroup.normalizer (autI hV (twoResidual (⊤ : Subgroup G)) : Set (MulAut (IntMod V hV))) := by
  have key : ∀ (g : G), ∀ ψ ∈ autI hV (twoResidual (⊤ : Subgroup G)),
      actHom hV g * ψ * (actHom hV g)⁻¹ ∈ autI hV (twoResidual (⊤ : Subgroup G)) := by
    intro g ψ hψ
    obtain ⟨b, hb, rfl⟩ := (mem_autI hV).1 hψ
    refine (mem_autI hV).2 ⟨⟨g * b * g⁻¹, mem_normalizer_of_normal _⟩, ?_, ?_⟩
    · have h := (Subgroup.mem_normalizer_iff.1
        (le_normalizer_twoResidual (⊤ : Subgroup G) (Subgroup.mem_top g)) (b : G)).1 hb
      simpa using h
    · show convI hV (⟨g, mem_normalizer_of_normal g⟩ * b * ⟨g, mem_normalizer_of_normal g⟩⁻¹) =
        convI hV ⟨g, mem_normalizer_of_normal g⟩ * convI hV b *
          (convI hV ⟨g, mem_normalizer_of_normal g⟩)⁻¹
      rw [map_mul, map_mul, map_inv]
  intro φ hφ
  obtain ⟨g, rfl⟩ := exists_actHom_eq hV hφ
  refine B6.mem_normalizer_of_forall_mem (fun ψ hψ => key g ψ hψ) fun ψ hψ => ?_
  have h := key g⁻¹ ψ hψ
  rwa [map_inv, inv_inv] at h

theorem twoResidual_autI_top_le :
    twoResidual (autI hV (⊤ : Subgroup G)) ≤ autI hV (twoResidual (⊤ : Subgroup G)) := by
  refine twoResidual_le_of_isTwoQuotient (autI_mono hV (twoResidual_le _))
    (autI_top_le_normalizer_autI_twoResidual hV) ?_
  intro y hy
  obtain ⟨g, rfl⟩ := exists_actHom_eq hV hy
  obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient (⊤ : Subgroup G) g (Subgroup.mem_top g)
  exact ⟨k, (mem_autI hV).2 ⟨⟨g ^ 2 ^ k, mem_normalizer_of_normal _⟩, hk, map_pow (actHom hV) g (2 ^ k)⟩⟩

end TwoResidual

theorem exists_isSeed_of_natural {G : Type} [Group G] [Finite G] {V : Subgroup G} [V.Normal]
    (hV : IsElemAbelian 2 V) (P : Sylow 2 G) (hVE : V ≤ Ecore G)
    (hO : CFSG.pCore 2 G ≤ Subgroup.centralizer (V : Set G))
    (hfr : (Subgroup.centralizer (V : Set G)).map (QuotientGroup.mk' (CFSG.pCore 2 G)) ≤
      frattini (G ⧸ CFSG.pCore 2 G))
    {n : ℕ} (hnat : E2.IsL2Natural (autI hV (⊤ : Subgroup G))
      (fixV (autI hV (twoResidual (⊤ : Subgroup G)))) n)
    (hJ : ¬ thompsonJ (P : Subgroup G) ≤ CFSG.pCore 2 G) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (ρ : G →* SpecialLinearGroup (Fin 2) F)
      (ψ : Ecore G →* Multiplicative (Fin 2 → F)), IsSeed P ρ (Ecore G) ψ := by
  obtain ⟨hn1, F, hFld, hFin, hcard, e, β, hβs, hβk, hβe⟩ := hnat
  haveI : Finite F := Finite.of_fintype F
  have hcardN : Nat.card F = 2 ^ n := by
    rw [Nat.card_eq_fintype_card]
    exact hcard
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn1 hcardN
  have hXV : ⁅V, (⊤ : Subgroup G)⁆ ≤ V := Subgroup.commutator_le_left V ⊤
  let ρ : G →* SpecialLinearGroup (Fin 2) F := e.toMonoidHom.comp (actA hV)
  let ψ : ↥(⁅V, (⊤ : Subgroup G)⁆) →* Multiplicative (Fin 2 → F) := β.comp (natSeedCommTo hV)
  have hker : ρ.ker = Subgroup.centralizer (V : Set G) := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact ker_actA hV
  have hseed : IsSeed P ρ ⁅V, (⊤ : Subgroup G)⁆ ψ := by
    refine ⟨⟨⟨n, hn1, hcardN⟩, e.surjective.comp (actA_surjective hV), ?_, ?_, inferInstance,
      hXV.trans hVE, ?_, ?_, ?_⟩, hJ⟩
    · rw [hker]
      exact hO
    · rw [hker]
      exact hfr
    · intro w
      obtain ⟨u, hu⟩ := hβs w
      refine ⟨⟨u.1.val, val_mem_commutator_top hV u.2⟩, ?_⟩
      have h1 : natSeedCommTo hV ⟨u.1.val, val_mem_commutator_top hV u.2⟩ = u :=
        Subtype.ext (IntMod.val_injective rfl)
      show β (natSeedCommTo hV _) = w
      rw [h1, hu]
    · intro g x x' hx'
      have key : ((actA hV g : MulAut (IntMod V hV))
          ((natSeedCommTo hV x : ↥(commV (autI hV (⊤ : Subgroup G)))) : IntMod V hV)) =
          ((natSeedCommTo hV x' : ↥(commV (autI hV (⊤ : Subgroup G)))) : IntMod V hV) := by
        refine IntMod.val_injective ?_
        rw [coe_actA, actHom_apply_val, natSeedCommTo_val, natSeedCommTo_val, hx']
      have hu : ((actA hV g : MulAut (IntMod V hV))
          ((natSeedCommTo hV x : ↥(commV (autI hV (⊤ : Subgroup G)))) : IntMod V hV)) ∈
          commV (autI hV (⊤ : Subgroup G)) := key ▸ (natSeedCommTo hV x').2
      have h := hβe (actA hV g) (natSeedCommTo hV x) hu
      have h2 : (⟨(actA hV g : MulAut (IntMod V hV))
          ((natSeedCommTo hV x : ↥(commV (autI hV (⊤ : Subgroup G)))) : IntMod V hV), hu⟩ :
          ↥(commV (autI hV (⊤ : Subgroup G)))) = natSeedCommTo hV x' := Subtype.ext key
      rw [h2] at h
      exact h
    · ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      have hfix : ∀ y : ↥(commV (autI hV (⊤ : Subgroup G))),
          β y = 1 ↔ (y : IntMod V hV) ∈ fixV (autI hV (twoResidual (⊤ : Subgroup G))) := by
        intro y
        rw [← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        exact ⟨fun h => h.2, fun h => ⟨y.2, h⟩⟩
      show β (natSeedCommTo hV x) = 1 ↔ _
      rw [hfix, mem_fixV_autI hV (fun g _ => mem_normalizer_of_normal g) _]
      constructor
      · intro h
        refine ⟨x.2, ?_⟩
        have h1 : ((natSeedCommTo hV x : ↥(commV (autI hV (⊤ : Subgroup G)))) : IntMod V hV) ∈
            fixV (twoResidual (autI hV (⊤ : Subgroup G))) := fun y hy =>
          ((mem_fixV_autI hV (fun g _ => mem_normalizer_of_normal g) _).2 h) y
            (twoResidual_autI_top_le hV hy)
        have h2 := commV_inf_fixV_twoResidual_le (fun w : IntMod V hV => IntMod.sq_eq_one w) e
          ⟨(natSeedCommTo hV x).2, h1⟩
        have h3 := (mem_fixV_autI hV (fun g _ => mem_normalizer_of_normal g) _).1 h2
        exact Subgroup.mem_center_iff.2 fun g => Subgroup.mem_centralizer_iff.1 h3 g (Subgroup.mem_top g)
      · rintro ⟨-, hc⟩
        exact Subgroup.mem_centralizer_iff.2 fun h _ => Subgroup.mem_center_iff.1 hc h
  obtain ⟨ψE, hψE, -⟩ := hseed.toEcore
  exact ⟨F, hFld, inferInstance, ρ, ψE, hψE⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
