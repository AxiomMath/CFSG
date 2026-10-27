module

public import CFSG.GroupActions.SubgroupStabilizerOuterBound
public import CFSG.LocalAnalysis.ComponentInitial.SelfCentralizingCoreAutomorphisms
import CFSG.Sporadic.SchreierLemmas.LocalRestrictionSchreier

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBK

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.LocalAnalysis.ComponentInitial (pointwiseFixingAut)
open CFSG.GroupActions (subgroupStabAut subgroupStabRestrict subgroupStabRestrict_apply)

theorem not_dvd_card_of_ker_range {X Y : Type*} [Group X] [Group Y] [Finite X] {p : ℕ}
    (hp : p.Prime) (f : X →* Y) (hker : ¬ p ∣ Nat.card f.ker)
    (hrange : ¬ p ∣ Nat.card f.range) : ¬ p ∣ Nat.card X := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  intro h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  exacts [hrange h, hker h]

theorem conjugacy_invariant_two_centralizer_outer_prime_support {G : Type*} [Group G]
    [Finite G] {p : ℕ} (hp : p.Prime) (M : Subgroup G)
    (hconj : ∀ α : MulAut G, ∃ g : G, M.map α.toMonoidHom = M.map (MulAut.conj g).toMonoidHom)
    {t : G} (ht : t ∈ M) (hgen : M ⊔ centralizer {t} = ⊤)
    (hOM : ¬ p ∣ Nat.card (Outer M))
    (hOM1 : ¬ p ∣ Nat.card (Outer (centralizer {t} : Subgroup G)))
    (hD : ¬ p ∣ Nat.card ↥(centralizer {t} ⊓
      centralizer ((M ⊓ centralizer {t} : Subgroup G) : Set G))) :
    ¬ p ∣ Nat.card (Outer G) := by
  classical
  have : Finite (MulAut G) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut G))
  set M1 : Subgroup G := centralizer {t} with hM1
  set N := subgroupStabAut M with hN
  set C := pointwiseFixingAut M with hC
  have hCN : C ≤ N := fun α hα => CFSG.LieType.Ree.map_eq_of_fixes hα
  have hCp : ¬ p ∣ Nat.card C := by
    have hCM1 : C ≤ subgroupStabAut M1 := fun α hα =>
      CFSG.Sporadic.SchreierLemmas.map_centralizer_eq_of_forall_apply_eq (by
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact hα _ ht)
    set r : C →* MulAut M1 := (subgroupStabRestrict M1).comp (Subgroup.inclusion hCM1) with hr
    have hrinj : Function.Injective r := by
      rw [injective_iff_map_eq_one]
      intro α hα1
      have hle : M ⊔ M1 ≤ MonoidHom.eqLocus (α : MulAut G).toMonoidHom (MonoidHom.id G) := by
        refine sup_le (fun x hx => α.2 x hx) fun x hx => ?_
        exact congrArg Subtype.val (DFunLike.congr_fun hα1 ⟨x, hx⟩)
      rw [hgen] at hle
      exact Subtype.ext (MulEquiv.ext fun g => hle (Subgroup.mem_top g))
    rw [Nat.card_congr (MonoidHom.ofInjective hrinj).toEquiv]
    set τ : r.range →* Outer M1 := (QuotientGroup.mk' (inner M1)).comp r.range.subtype with hτ
    refine not_dvd_card_of_ker_range hp τ ?_
      fun h => hOM1 (h.trans (Subgroup.card_subgroup_dvd_card _))
    set Z : Subgroup M1 := (centralizer ((M ⊓ M1 : Subgroup G) : Set G)).subgroupOf M1 with hZ
    have hZcard : Nat.card Z = Nat.card ↥(M1 ⊓ centralizer ((M ⊓ M1 : Subgroup G) : Set G)) := by
      rw [hZ, ← Subgroup.card_map_of_injective M1.subtype_injective,
        Subgroup.subgroupOf_map_subtype, inf_comm]
    have hle : τ.ker.map r.range.subtype ≤ Z.map (MulAut.conj : M1 →* MulAut M1) := by
      rintro _ ⟨β, hβ, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, hτ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hβ
      obtain ⟨x, hx⟩ := hβ
      refine ⟨x, ?_, hx⟩
      obtain ⟨⟨α, hα⟩, hαβ⟩ := β.2
      rw [SetLike.mem_coe, hZ, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
      intro d hd
      have hd' : d ∈ M1 := (Subgroup.mem_inf.mp hd).2
      have h1 := congrArg (fun φ : MulAut M1 => ((φ ⟨d, hd'⟩ : M1) : G)) (hx.trans hαβ.symm)
      simp only [MulAut.conj_apply, hr, MonoidHom.comp_apply, subgroupStabRestrict_apply,
        Subgroup.coe_mul, Subgroup.coe_inv] at h1
      change (x : G) * d * (x : G)⁻¹ = α d at h1
      rw [hα d (Subgroup.mem_inf.mp hd).1, mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm
    intro hdvd
    refine hD (hZcard ▸ hdvd.trans ?_)
    rw [← Subgroup.card_map_of_injective r.range.subtype_injective]
    exact (Subgroup.card_dvd_of_le hle).trans (Subgroup.card_map_dvd _ _)
  set π : N →* Outer G := (QuotientGroup.mk' (inner G)).comp N.subtype with hπ
  have hπs : Function.Surjective π := by
    intro x
    obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective (inner G) x
    obtain ⟨g, hg⟩ := hconj α
    refine ⟨⟨(MulAut.conj g)⁻¹ * α, ?_⟩, ?_⟩
    · change M.map ((MulAut.conj g)⁻¹ * α).toMonoidHom = M
      rw [show ((MulAut.conj g)⁻¹ * α).toMonoidHom =
        ((MulAut.conj g)⁻¹).toMonoidHom.comp α.toMonoidHom from rfl, ← Subgroup.map_map, hg,
        Subgroup.map_map]
      have hid : ((MulAut.conj g)⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
          MonoidHom.id G := MonoidHom.ext fun x => MulAut.inv_apply_self G (MulAut.conj g) x
      rw [hid, Subgroup.map_id]
    · change (((MulAut.conj g)⁻¹ * α : MulAut G) : Outer G) = (α : Outer G)
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (N := inner G)
        ((MulAut.conj g)⁻¹)).2 ⟨g⁻¹, by rw [map_inv]⟩, one_mul]
  set ρ : N →* Outer M := (QuotientGroup.mk' (inner M)).comp (subgroupStabRestrict M) with hρ
  set X := ρ.ker.map π with hX
  have hidx : ¬ p ∣ X.index := by
    intro h
    have h1 := h.trans (Subgroup.index_map_dvd ρ.ker hπs)
    rw [Subgroup.index_ker] at h1
    exact hOM (h1.trans (Subgroup.card_subgroup_dvd_card _))
  have hXC : X ≤ (C.subgroupOf N).map π := by
    rintro _ ⟨α, hα, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, hρ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hα
    obtain ⟨m, hm⟩ := hα
    have hmN : MulAut.conj (m : G) ∈ N := by
      change M.map (MulAut.conj (m : G)).toMonoidHom = M
      ext x
      rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
      constructor
      · intro hx
        have := mul_mem (mul_mem m.2 hx) (inv_mem m.2)
        simpa [mul_assoc] using this
      · intro hx
        exact mul_mem (mul_mem (inv_mem m.2) hx) m.2
    refine ⟨⟨(MulAut.conj (m : G))⁻¹ * α, mul_mem (inv_mem hmN) α.2⟩, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      intro x hx
      have h1 := congrArg (fun φ : MulAut M => ((φ ⟨x, hx⟩ : M) : G)) hm
      change (m : G) * x * (m : G)⁻¹ = (α : MulAut G) x at h1
      change ((MulAut.conj (m : G))⁻¹ * (α : MulAut G)) x = x
      rw [MulAut.mul_apply, ← h1, MulAut.conj_inv_apply]
      group
    · change (((MulAut.conj (m : G))⁻¹ * α : MulAut G) : Outer G) = ((α : MulAut G) : Outer G)
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (N := inner G)
        ((MulAut.conj (m : G))⁻¹)).2 ⟨(m : G)⁻¹, by rw [map_inv]⟩, one_mul]
  have hXp : ¬ p ∣ Nat.card X := by
    intro h
    refine hCp (h.trans ((Subgroup.card_dvd_of_le hXC).trans
      ((Subgroup.card_map_dvd _ _).trans ?_)))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv]
  rw [← Subgroup.card_mul_index X]
  intro h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  exacts [hXp h, hidx h]

end CFSG.RankThree.GroupTheory.SteinbergBK
