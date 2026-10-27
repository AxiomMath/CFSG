module

public import CFSG.Milestones.ASVolI.F411.Cent
public import CFSG.Milestones.ASVolI.F4Aut
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF CFSG.ASVolI.ChF.ExceptionalRoots
open scoped commutatorElement

section Generic

theorem burnsideF411_autCentSylow_of_inner {X : Type} [Group X] (p : ℕ)
    (h : ∀ α : MulAut X, ∃ g : X, α = MulAut.conj g) : burnsideF411_AutCentSylow X p :=
  fun α _ _ => h α

theorem burnsideF411_commutator_eq_top_of_simple {S : Type} [Group S] [IsSimpleGroup S]
    (hS : Subgroup.center S = ⊥) : ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ = (⊤ : Subgroup S) := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ with h | h
  · exfalso
    have hle : (⊤ : Subgroup S) ≤ Subgroup.center S := by
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      have hc : ⁅y, x⁆ ∈ ⁅(⊤ : Subgroup S), ⊤⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top y) (Subgroup.mem_top x)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hc
    rw [hS] at hle
    obtain ⟨a, b, hab⟩ := exists_pair_ne S
    exact hab ((Subgroup.mem_bot.mp (hle (Subgroup.mem_top a))).trans
      (Subgroup.mem_bot.mp (hle (Subgroup.mem_top b))).symm)
  · exact h

theorem burnsideF411_inner_of_conjOn_bijective {S G : Type} [Group S] [Group G] [Finite G]
    (f : S →* G) (hf : Function.Injective f) (hR : f.range.index = 2) [IsSimpleGroup S]
    (hS : Subgroup.center S = ⊥)
    (hbij : Function.Bijective (burnsideF45_conjOn f hf (Subgroup.normal_of_index_eq_two hR)))
    (α : MulAut G) : ∃ g : G, α = MulAut.conj g := by
  classical
  have hN : f.range.Normal := Subgroup.normal_of_index_eq_two hR
  haveI : Finite S := Finite.of_injective f hf
  have hcomm : f.range = ⁅(⊤ : Subgroup G), ⊤⁆ := by
    apply le_antisymm
    · rw [MonoidHom.range_eq_map f, ← burnsideF411_commutator_eq_top_of_simple hS,
        Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    · rw [Subgroup.commutator_le]
      intro a _ b _
      rw [commutatorElement_def, Subgroup.mul_mem_iff_of_index_two hR,
        Subgroup.mul_mem_iff_of_index_two hR, Subgroup.mul_mem_iff_of_index_two hR,
        Subgroup.inv_mem_iff, Subgroup.inv_mem_iff]
      tauto
  have hmap : f.range.map α.toMonoidHom = f.range := by
    rw [hcomm, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (MulEquiv.surjective α)]
  have hmem : ∀ x : G, x ∈ f.range → α x ∈ f.range := by
    intro x hx
    rw [← hmap]
    exact ⟨x, hx, rfl⟩
  have hex : ∀ s : S, ∃ t : S, f t = α (f s) := fun s => hmem (f s) ⟨s, rfl⟩
  choose a ha using hex
  have hainj : Function.Injective a := by
    intro s s' h
    apply hf
    apply α.injective
    rw [← ha, ← ha, h]
  have hamul : ∀ s s', a (s * s') = a s * a s' := by
    intro s s'
    apply hf
    rw [ha, map_mul, map_mul, map_mul, ha, ha]
  have hasurj : Function.Surjective a := Finite.injective_iff_surjective.mp hainj
  let αS : MulAut S := MulEquiv.ofBijective (MonoidHom.mk' a hamul) ⟨hainj, hasurj⟩
  have hαS : ∀ s, f (αS s) = α (f s) := fun s => ha s
  obtain ⟨g, hg⟩ := hbij.2 αS
  have hconj : ∀ s : S, α (f s) = g * f s * g⁻¹ := by
    intro s
    rw [← hαS, ← hg, burnsideF45_conjOn_apply]
  refine ⟨g, MulEquiv.ext fun x => ?_⟩
  rw [MulAut.conj_apply]
  set y : G := x⁻¹ * (g⁻¹ * α x * g) with hy
  have hyc : ∀ s : S, y * f s * y⁻¹ = f s := by
    intro s
    obtain ⟨t, ht⟩ : x * f s * x⁻¹ ∈ f.range := hN.conj_mem _ ⟨s, rfl⟩ x
    have h1 : α (f t) = g * f t * g⁻¹ := hconj t
    rw [ht, map_mul, map_mul, map_inv, hconj s] at h1
    calc y * f s * y⁻¹ = x⁻¹ * (g⁻¹ * (α x * (g * f s * g⁻¹) * (α x)⁻¹) * g) * x := by
          rw [hy]; group
      _ = x⁻¹ * (g⁻¹ * (g * (x * f s * x⁻¹) * g⁻¹) * g) * x := by rw [h1]
      _ = f s := by group
  have hy1 : y = 1 := by
    apply hbij.1
    rw [map_one]
    ext s
    apply hf
    rw [burnsideF45_conjOn_apply, MulAut.one_apply, hyc s]
  have hx : g⁻¹ * α x * g = x := by
    have h := hy1
    rw [hy] at h
    exact (inv_mul_eq_one.mp h).symm
  calc α x = g * (g⁻¹ * α x * g) * g⁻¹ := by group
    _ = g * x * g⁻¹ := by rw [hx]

end Generic

section G2Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley


variable {K : Type} [Field K] [Finite K]

theorem burnsideF411_g2Two_inner (hK : Nat.card K = 2) (α : MulAut (G2Native.FullModel K)) :
    ∃ g : G2Native.FullModel K, α = MulAut.conj g := by
  haveI := CFSG.Quasithin.isSimpleGroup_u33Pres
  haveI : IsSimpleGroup (G2Native.SmallModel K) := (burnsideF4h_g2_psi K hK).symm.isSimpleGroup
  exact burnsideF411_inner_of_conjOn_bijective (burnsideF4h_g2_incl K hK)
    (burnsideF4h_g2_incl_injective hK) (burnsideF4h_g2_incl_index hK)
    (burnsideF45_g2_center_small hK) (burnsideF45_g2_conj_bijective hK) α

theorem burnsideF411_autCentSylow_g2Two (hK : Nat.card K = 2) (p : ℕ) :
    burnsideF411_AutCentSylow (G2Native.FullModel K) p :=
  burnsideF411_autCentSylow_of_inner p (burnsideF411_g2Two_inner hK)

end G2Two

section TwoF4Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Sporadic.Schreier.Tits


variable {K : Type} [Field K] [Finite K]

theorem burnsideF411_twoF4Two_inner [CharP K 2] (hK : Nat.card K = 2)
    (α : MulAut (↥(reeGroup K 0) ⧸ Subgroup.center ↥(reeGroup K 0))) :
    ∃ g : ↥(reeGroup K 0) ⧸ Subgroup.center ↥(reeGroup K 0), α = MulAut.conj g := by
  haveI : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := inferInstanceAs (CharP K 2)
  have hscope : Nat.card K = 2 ^ (2 * 0 + 1) := by rw [hK]; norm_num
  obtain ⟨-, -, -, ι, hιinj, hιidx, -⟩ := burnsideF4h_titsParentAssembly K hscope
  have hZfull : Subgroup.center (↥(reeGroup K 0) ⧸ Subgroup.center ↥(reeGroup K 0)) = ⊥ :=
    burnsideF45_center_quotient_eq_bot (burnsideF4h_ree_center_trivial hscope)
  obtain ⟨Φ, -⟩ := burnsideF4h_tits_gammaEquiv hK
  obtain ⟨Θ, -⟩ := burnsideF4h_tits_commutator_equiv (reeGroup K 0) Φ
  have hZ : Subgroup.center ↥⁅reeGroup K 0, reeGroup K 0⁆ = ⊥ :=
    burnsideF4h_tits_center_eq_bot_of_equiv Θ burnsideF4h_tits_center_titsD
  have hZsmall : Subgroup.center (DerivedCentralQuotient (reeGroup K 0)) = ⊥ :=
    burnsideF45_center_quotient_eq_bot hZ
  obtain ⟨eC, -⟩ := burnsideF4h_tits_exists_derivedEquiv (reeGroup K 0) _ rfl hZ
  haveI : IsSimpleGroup ↥titsD := titsD_simple
  haveI : IsSimpleGroup (DerivedCentralQuotient (reeGroup K 0)) := (eC.trans Θ).isSimpleGroup
  have hinj := burnsideF45_conjOn_injective ι hιinj hιidx hZsmall hZfull
  have hbij := hinj.bijective_of_nat_card_le (by
    rw [burnsideF45_card_of_index_two ι hιinj hιidx,
      Nat.card_congr (MulAut.congr (eC.trans Θ)).toEquiv, Nat.card_congr (eC.trans Θ).toEquiv]
    exact card_mulAut_titsD_le titsOuter_card_le_two)
  exact burnsideF411_inner_of_conjOn_bijective ι hιinj hιidx hZsmall hbij α

theorem burnsideF411_autCentSylow_twoF4Two [CharP K 2] (hK : Nat.card K = 2) (p : ℕ) :
    burnsideF411_AutCentSylow (↥(reeGroup K 0) ⧸ Subgroup.center ↥(reeGroup K 0)) p :=
  burnsideF411_autCentSylow_of_inner p (burnsideF411_twoF4Two_inner hK)

end TwoF4Two

end CFSG.ASVolI
