module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCRedInj
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.TC914R

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement

variable {G : Type} [Group G] {N L : Subgroup G} {X : Type} [Group X]

theorem liftSub_barSub_eq (hLN : L ≤ N) (ψ : ↥N →* X)
    (hψk : ∀ x : ↥N, ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 N) :
    NFW.liftSub ψ (NFW.barSub ψ L) = L ⊔ pCoreOf 2 N := by
  refine le_antisymm (fun x hx => ?_)
    (sup_le ((NFW.barSub_le_iff hLN).mp le_rfl) (NFW.pCoreOf_le_liftSub hψk _))
  obtain ⟨hxN, l, hl, hlx⟩ := NFW.mem_liftSub.mp hx
  have h1 : ψ (l⁻¹ * ⟨x, hxN⟩) = 1 := by rw [map_mul, map_inv, hlx, inv_mul_cancel]
  have h2 : (l : G)⁻¹ * x ∈ pCoreOf 2 N := (hψk _).mp h1
  have h3 := mul_mem_sup (mem_subgroupOf.mp hl) h2
  simpa using h3

theorem mem_normalizer_iff_map (hLN : L ≤ N) (hL : L = perfectCore (L ⊔ pCoreOf 2 N))
    (ψ : ↥N →* X) (hψk : ∀ x : ↥N, ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 N) (x : ↥N) :
    (x : G) ∈ normalizer (L : Set G) ↔ ψ x ∈ normalizer (NFW.barSub ψ L : Set X) := by
  refine ⟨NFW.mem_normalizer_barSub, fun h => ?_⟩
  have h1 := NFW.mem_normalizer_liftSub x.2 h
  rw [liftSub_barSub_eq hLN ψ hψk] at h1
  rw [hL]
  exact normalizer_le_normalizer_perfectCore _ h1

theorem pCoreOf_le_pCoreOf [Finite G] [Finite X] {T : Subgroup G} (hLN : L ≤ N)
    (hL : L = perfectCore (L ⊔ pCoreOf 2 N)) (ψ : ↥N →* X) (hψs : Function.Surjective ψ)
    (hψk : ∀ x : ↥N, ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 N)
    (c : Pre (NFW.barSub ψ L) (NFW.barSub ψ T)) : pCoreOf 2 L ≤ pCoreOf 2 N := by
  set P := NFW.barSub ψ (pCoreOf 2 L)
  have hPL : P ≤ NFW.barSub ψ L := NFW.barSub_mono (CFSG.LieType.BorelTits.pCoreOf_le 2 L)
  have hN1 : tcN1 (NFW.barSub ψ L) (NFW.barSub ψ T) ≤ normalizer (NFW.barSub ψ L : Set X) :=
    sup_le le_normalizer inf_le_right
  have hPn : tcN1 (NFW.barSub ψ L) (NFW.barSub ψ T) ≤ normalizer (P : Set X) := by
    intro y hy
    obtain ⟨x, rfl⟩ := hψs y
    have hxL := (mem_normalizer_iff_map hLN hL ψ hψk x).mpr (hN1 hy)
    exact NFW.mem_normalizer_barSub
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L hxL)
  have hP2 : IsPGroup 2 P :=
    NFW.isPGroup_barSub (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hPL.trans le_sup_left) hPn hP2
  have hbot : P = ⊥ := le_bot_iff.mp ((le_inf hle hPL).trans_eq c.pCore_inf_Lb)
  exact (NFW.barSub_eq_bot_iff hψk ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLN)).mp hbot

theorem isPGroup_map_oTwoThreeIn (hO2L : pCoreOf 2 L ≤ pCoreOf 2 N) (ψ : ↥N →* X)
    (hψk : ∀ x : ↥N, ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 N) :
    IsPGroup 3 (((oTwoThreeIn L).subgroupOf N).map ψ) := by
  rintro ⟨_, y, hy, rfl⟩
  rw [SetLike.mem_coe, mem_subgroupOf] at hy
  obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.mp hy
  have hw' : QuotientGroup.mk' (CFSG.pCore 2 ↥L) w ∈ CFSG.pCore 3 (↥L ⧸ CFSG.pCore 2 ↥L) :=
    Subgroup.mem_comap.mp hw
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 3) ⟨_, hw'⟩
  refine ⟨k, Subtype.ext ?_⟩
  have hk' : QuotientGroup.mk' (CFSG.pCore 2 ↥L) (w ^ 3 ^ k) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val hk
  have hwL : ((w ^ 3 ^ k : ↥L) : G) ∈ pCoreOf 2 L :=
    (CFSG.mem_openPCoreOf_iff _).mpr ((QuotientGroup.eq_one_iff _).mp hk')
  have hyN : ((y ^ 3 ^ k : ↥N) : G) ∈ pCoreOf 2 N := by
    have he : ((y ^ 3 ^ k : ↥N) : G) = ((w ^ 3 ^ k : ↥L) : G) := by
      simp only [Subgroup.coe_pow, Subgroup.coe_subtype] at hwy ⊢
      rw [hwy]
    rw [he]
    exact hO2L hwL
  have h1 := (hψk _).mpr hyN
  rw [map_pow] at h1
  simpa using h1

theorem map_oTwoThreeIn_le_center [Finite X] (hO2L : pCoreOf 2 L ≤ pCoreOf 2 N) (ψ : ↥N →* X)
    (hψk : ∀ x : ↥N, ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 N)
    (hq : CFSG.IsQuasisimple (NFW.barSub ψ L)) :
    ((oTwoThreeIn L).subgroupOf N).map ψ ≤
      (center (NFW.barSub ψ L)).map (NFW.barSub ψ L).subtype := by
  refine NF914.le_map_center_of_isPGroup hq ?_ ?_ (isPGroup_map_oTwoThreeIn hO2L ψ hψk)
  · exact Subgroup.map_mono fun y hy => by
      rw [mem_subgroupOf] at hy ⊢
      exact NF914.oTwoThreeIn_le L hy
  · rintro _ ⟨l, hl, rfl⟩ _ ⟨h, hh, rfl⟩
    refine ⟨l * h * l⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    rw [SetLike.mem_coe, mem_subgroupOf] at hl hh ⊢
    have hlN : (l : G) ∈ normalizer (oTwoThreeIn L : Set G) :=
      NF914.normalizer_le_normalizer_oTwoThreeIn L (Subgroup.le_normalizer hl)
    simpa using (mem_normalizer_iff.mp hlN h).mp hh

theorem mem_centralizer_of_mem_centSection [Finite X] (hO2L : pCoreOf 2 L ≤ pCoreOf 2 N)
    (ψ : ↥N →* X) (hψk : ∀ x : ↥N, ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 N)
    (hq : CFSG.IsQuasisimple (NFW.barSub ψ L)) {x : ↥N}
    (hx : (x : G) ∈ S17.centSection N L (oTwoThreeIn L)) :
    ψ x ∈ centralizer (NFW.barSub ψ L : Set X) := by
  have hHbZ := map_oTwoThreeIn_le_center hO2L ψ hψk hq
  set Lb := NFW.barSub ψ L with hLb
  set Cb := ((S17.centSection N L (oTwoThreeIn L)).subgroupOf N).map ψ with hCb
  have hcomm : ∀ c ∈ Cb, ∀ l ∈ Lb, c * l * c⁻¹ * l⁻¹ ∈ (center Lb).map Lb.subtype := by
    rintro _ ⟨c, hc, rfl⟩ _ ⟨l, hl, rfl⟩
    apply hHbZ
    refine ⟨c * l * c⁻¹ * l⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    rw [SetLike.mem_coe, mem_subgroupOf] at hl hc ⊢
    obtain ⟨-, -, -, hcent⟩ := hc
    simpa using hcent (l : G) hl
  have hZc : ∀ a ∈ (center Lb).map Lb.subtype, ∀ b ∈ Lb, b * a = a * b := by
    rintro _ ⟨z, hz, rfl⟩ b hb
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨b, hb⟩)
  have hLC : ⁅Lb, Cb⁆ = ⊥ := by
    refine CFSG.LocalCores.perfect_double_commutator hq.1 ?_
    have h1 : ⁅Lb, Cb⁆ ≤ (center Lb).map Lb.subtype := by
      rw [Subgroup.commutator_le]
      intro l hl c hc
      rw [← commutatorElement_inv]
      exact Subgroup.inv_mem _ (hcomm c hc l hl)
    have h2 : ⁅(center Lb).map Lb.subtype, Lb⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun a ha =>
        Subgroup.mem_centralizer_iff.mpr fun b hb => hZc a ha b hb
    exact le_bot_iff.mp (h2 ▸ Subgroup.commutator_mono_left h1)
  have hxC : ψ x ∈ Cb := Subgroup.mem_map_of_mem ψ (by rw [mem_subgroupOf]; exact hx)
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact (Subgroup.mem_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hLC hl) _ hxC).symm

theorem mem_centSection_of_mem_centralizer (hLN : L ≤ N) (ψ : ↥N →* X)
    (hψk : ∀ x : ↥N, ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 N) {x : ↥N}
    (hxL : (x : G) ∈ normalizer (L : Set G))
    (hx : ψ x ∈ centralizer (NFW.barSub ψ L : Set X)) :
    (x : G) ∈ S17.centSection N L (oTwoThreeIn L) := by
  refine ⟨x.2, hxL, NF914.normalizer_le_normalizer_oTwoThreeIn L hxL, fun a ha => ?_⟩
  have h1 : (x : G) * a * (x : G)⁻¹ * a⁻¹ ∈ L :=
    L.mul_mem ((mem_normalizer_iff.mp hxL a).mp ha) (L.inv_mem ha)
  set a' : ↥N := ⟨a, hLN ha⟩ with ha'
  have haL : ψ a' ∈ NFW.barSub ψ L := NFW.mem_barSub_of_mem' ha
  have hψ1 : ψ (x * a' * x⁻¹ * a'⁻¹) = 1 := by
    have hc := Subgroup.mem_centralizer_iff.mp hx _ haL
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hc]
    group
  have h2 : (x : G) * a * (x : G)⁻¹ * a⁻¹ ∈ pCoreOf 2 N := (hψk _).mp hψ1
  exact NF914.pCoreOf_le_oTwoThreeIn L (CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hLN ⟨h1, h2⟩)

theorem exists_automizer_bar [Finite X] (hLN : L ≤ N) (hL : L = perfectCore (L ⊔ pCoreOf 2 N))
    (hO2L : pCoreOf 2 L ≤ pCoreOf 2 N) (ψ : ↥N →* X) (hψs : Function.Surjective ψ)
    (hψk : ∀ x : ↥N, ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 N) (hq : CFSG.IsQuasisimple (NFW.barSub ψ L))
    {A : Type} [Group A] (φ : ↥(N ⊓ normalizer (L : Set G)) →* A) (hφs : Function.Surjective φ)
    (hφk : ∀ x, φ x = 1 ↔ (x : G) ∈ S17.centSection N L (oTwoThreeIn L)) :
    ∃ φb : ↥(normalizer (NFW.barSub ψ L : Set X)) →* A, Function.Surjective φb ∧
      ∀ y, φb y = 1 ↔ (y : X) ∈ centralizer (NFW.barSub ψ L : Set X) := by
  let ψ₁ : ↥(N ⊓ normalizer (L : Set G)) →* ↥(normalizer (NFW.barSub ψ L : Set X)) :=
    (ψ.comp (Subgroup.inclusion inf_le_left)).codRestrict _ fun x =>
      NFW.mem_normalizer_barSub (mem_inf.mp x.2).2
  have hψ₁ : ∀ x, (ψ₁ x : X) = ψ (Subgroup.inclusion inf_le_left x) := fun _ => rfl
  have hψ₁s : Function.Surjective ψ₁ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hψs y
    exact ⟨⟨(x : G), x.2, (mem_normalizer_iff_map hLN hL ψ hψk x).mpr hy⟩, rfl⟩
  have hiff : ∀ x, φ x = 1 ↔ (ψ₁ x : X) ∈ centralizer (NFW.barSub ψ L : Set X) := fun x => by
    rw [hφk, hψ₁]
    exact ⟨mem_centralizer_of_mem_centSection (x := Subgroup.inclusion inf_le_left x) hO2L ψ hψk
      hq, mem_centSection_of_mem_centralizer (x := Subgroup.inclusion inf_le_left x) hLN ψ hψk
        (mem_inf.mp x.2).2⟩
  have hle : ψ₁.ker ≤ φ.ker := fun x hx => by
    rw [MonoidHom.mem_ker] at hx ⊢
    rw [hiff, hx]
    exact one_mem _
  set φb := ψ₁.liftOfRightInverse (Function.surjInv hψ₁s)
    (Function.rightInverse_surjInv hψ₁s) ⟨φ, hle⟩
  have hφb : ∀ x, φb (ψ₁ x) = φ x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x
  refine ⟨φb, fun a => ?_, fun y => ?_⟩
  · obtain ⟨x, rfl⟩ := hφs a
    exact ⟨ψ₁ x, hφb x⟩
  · obtain ⟨x, rfl⟩ := hψ₁s y
    rw [hφb, hiff]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.TC914R
