module

public import CFSG.Quasithin.MS93.S33SpDich
public import CFSG.Quasithin.MS93.S6Bridge

public section

namespace CFSG.Quasithin.MS93.S33

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem isSp4DerSec_one_of_sp4Two (h : PUHyp M T L) {α : ↥M →* ↥(StatedSp 2 (ZMod 2))}
    (hα : Function.Surjective α)
    (hnat : IsSumOfNaturalModulesVia M (Uq M T L)
      (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) α false 1) :
    IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Zq M L) 1 := by
  rw [← h.Uq_inf_Zq] at hnat
  obtain ⟨c⟩ := MSP.nonempty_natCoord hnat
  obtain ⟨hMV, hCV, β, hβ, hβker, hβα⟩ := id hnat
  refine Or.inl ⟨rfl, ?_⟩
  set θ := S6B.thetaTwo with hθ
  let αL : ↥L →* ↥(StatedSp 2 (ZMod 2)) := α.comp (Subgroup.inclusion h.L_le)
  have hsign : ∀ l : ↥L, Equiv.Perm.sign (θ.symm (αL l)) = 1 := by
    have hperf : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr h.perfect
    let φ : ↥L →* ℤˣ := Equiv.Perm.sign.comp (θ.symm.toMonoidHom.comp αL)
    intro l
    have hl : l ∈ commutator ↥L := by
      rw [hperf.commutator_eq_top]
      exact Subgroup.mem_top l
    exact Abelianization.commutator_subset_ker φ hl
  let α₀ : ↥L →* alternatingGroup (Fin 6) :=
    (θ.symm.toMonoidHom.comp αL).codRestrict (alternatingGroup (Fin 6))
      fun l => Equiv.Perm.mem_alternatingGroup.2 (hsign l)
  have hα₀ : ∀ l : ↥L, ((α₀ l : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) =
      θ.symm (αL l) := fun _ => rfl
  have hα₀s : Function.Surjective α₀ := by
    have hsimple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by simp)
    have hnorm : α₀.range.Normal := by
      refine ⟨fun k hk σ => ?_⟩
      obtain ⟨l, rfl⟩ := hk
      obtain ⟨m, hm⟩ := hα (θ σ)
      have hml : (m : G) * l * (m : G)⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.1 (h.le_normalizer m.2) l).1 l.2
      refine ⟨⟨_, hml⟩, Subtype.ext ?_⟩
      rw [hα₀, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hα₀]
      have e : αL ⟨_, hml⟩ = α m * αL l * (α m)⁻¹ := by
        simp only [αL, MonoidHom.comp_apply]
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [e, map_mul, map_mul, map_inv, hm, MulEquiv.symm_apply_apply]
    rcases hsimple.eq_bot_or_eq_top_of_normal α₀.range with hbot | htop
    · exfalso
      apply not_le_actTriv h
      intro l hl
      have h1 : α₀ ⟨l, hl⟩ = 1 := by
        have : α₀ ⟨l, hl⟩ ∈ α₀.range := ⟨_, rfl⟩
        rw [hbot] at this
        exact this
      have h2 : αL ⟨l, hl⟩ = 1 := by
        have := congrArg Subtype.val h1
        rw [hα₀] at this
        simpa using congrArg θ this
      exact (image_eq_one_iff h le_rfl c ⟨l, h.L_le hl⟩).1 h2
    · exact MonoidHom.range_eq_top.1 htop
  let ι : Multiplicative (Fin 1 → MSP.V4 (ZMod 2)) →* Multiplicative (Fin 2 ⊕ Fin 2 → ZMod 2) :=
    { toFun := fun x => Multiplicative.ofAdd (Multiplicative.toAdd x 0)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hιinj : Function.Injective ι := by
    intro x y hxy
    apply Multiplicative.toAdd.injective
    funext i
    rw [Subsingleton.elim i 0]
    exact congrArg Multiplicative.toAdd hxy
  let e := MulEquiv.ofBijective S6B.crdHom S6B.crdHom_bijective
  let β₀ : ↥(Uq M T L) →* Multiplicative (AltHeart 6) := e.symm.toMonoidHom.comp (ι.comp β)
  have hβ₀ : ∀ u, S6B.crdHom (β₀ u) = ι (β u) := fun u => e.apply_symm_apply _
  refine ⟨α₀.ker, h.L_le.trans hMV, α₀, hα₀s, rfl, β₀, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd fun _ => Multiplicative.toAdd (e y))
    refine ⟨u, e.injective ?_⟩
    show S6B.crdHom (β₀ u) = e y
    rw [hβ₀, hu]
    rfl
  · rw [← hβker]
    ext u
    simp only [MonoidHom.mem_ker, β₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [MulEquiv.map_eq_one_iff, (map_eq_one_iff ι hιinj)]
  · intro l u v huv x hx
    apply S6B.heartCrd_bijective.1
    have h1 := S6B.heartCrd_perm (α₀ l : Equiv.Perm (Fin 6)) x
    have hθl : S6B.thetaTwo (α₀ l : Equiv.Perm (Fin 6)) = αL l := by
      rw [hα₀, ← hθ, MulEquiv.apply_symm_apply]
    rw [hθl] at h1
    rw [h1, hx, ← S6B.toAdd_crdHom, ← S6B.toAdd_crdHom, hβ₀, hβ₀]
    have h2 := hβα (Subgroup.inclusion h.L_le l) u v huv 0
    simpa [ι, moduleAct, αL] using h2.symm

theorem isSp4DerSec_of_isSp4U (h : PUHyp M T L) (hU : IsSp4U M T L) :
    ∃ k, IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Zq M L) k := by
  rcases hU with ⟨k, F, iF, fF, α, hk, hF, hα, hnat⟩ | ⟨α, hα, hnat⟩
  · refine ⟨k, Or.inr ⟨hk, F, iF, fF, α, hF, hα, ?_⟩⟩
    rwa [h.Uq_inf_Zq]
  · exact ⟨1, isSp4DerSec_one_of_sp4Two h hα hnat⟩

end CFSG.Quasithin.MS93.S33
