module

public import CFSG.Sporadic.FischerOddCore.AlmostSimple
public import CFSG.Sporadic.FischerOddCore.Fi22AllInv
public import CFSG.Monster.B.Fischer.Fi22Model

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2 CFSG.Monster.B.Fischer
open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

theorem mem_fi22P_of_odd
    {r : Equiv.Perm (Fin 3510)} (hr : r ∈ fi22R) (ho : Odd (orderOf r)) :
    r ∈ fi22P := by
  obtain ⟨m, hm⟩ := ho
  have hsq : r ^ 2 ∈ fi22P := by
    have h := Subgroup.sq_mem_of_index_two index_fi22P_subgroupOf_R ⟨r, hr⟩
    rw [Subgroup.mem_subgroupOf] at h
    exact h
  have e : r = (r ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf r + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [e]
  exact Subgroup.pow_mem _ hsq _

variable {X : Type*} [Group X] {S : Subgroup X} [S.Normal]

@[expose] def fi22Embed
    (θ : S ≃* fi22P) : X →* Equiv.Perm (Fin 3510) :=
  fi22R.subtype.comp (fi22RAut.symm.toMonoidHom.comp (conjTransport θ))

theorem fi22Embed_mem
    (θ : S ≃* fi22P) (x : X) : fi22Embed θ x ∈ fi22R :=
  (fi22RAut.symm (conjTransport θ x)).2

theorem fi22Embed_injective
    (θ : S ≃* fi22P) (hC : Subgroup.centralizer (S : Set X) = ⊥) :
    Function.Injective (fi22Embed θ) :=
  fi22R.subtype_injective.comp (fi22RAut.symm.injective.comp (conjTransport_injective θ hC))

theorem fi22Embed_of_mem
    (θ : S ≃* fi22P) (s : S) :
    fi22Embed θ s = (θ s : Equiv.Perm (Fin 3510)) := by
  have h : fi22RAut ⟨(θ s : Equiv.Perm (Fin 3510)), fi22P_le_R (θ s).2⟩ =
      conjTransport θ s := by
    rw [conjTransport_of_mem]
    ext g
    rw [fi22RAut_apply, fi22ConjHom_apply, MulAut.conj_apply]
    rfl
  change ((fi22RAut.symm (conjTransport θ s) : fi22R) : Equiv.Perm (Fin 3510)) = _
  rw [← h, MulEquiv.symm_apply_apply]

theorem mem_of_odd_fi22Embed
    (θ : S ≃* fi22P) (hC : Subgroup.centralizer (S : Set X) = ⊥)
    {x : X} (ho : Odd (orderOf x)) : x ∈ S := by
  have hf := fi22Embed_injective θ hC
  have hP : fi22Embed θ x ∈ fi22P :=
    mem_fi22P_of_odd (fi22Embed_mem θ x) (by rwa [orderOf_injective _ hf x])
  have e : fi22Embed θ (θ.symm ⟨_, hP⟩ : X) = fi22Embed θ x := by
    rw [fi22Embed_of_mem, MulEquiv.apply_symm_apply]
  rw [← hf e]
  exact (θ.symm ⟨_, hP⟩).2

theorem CTUC_Fi22_almost_simple_involution_centralizer_odd_core_trivial
    {X : Type*} [Group X]
    [Finite X] (S : Subgroup X) [S.Normal] (hS : Nonempty (S ≃* Blueprint.NativeSporadic.Fi22))
    (hC : Subgroup.centralizer (S : Set X) = ⊥) (t : X) (ht : orderOf t = 2) :
    CFSG.oddCore ↥(Subgroup.centralizer ({t} : Set X)) = ⊥ := by
  set θ : S ≃* fi22P := hS.some.trans fi22PermEquiv
  set f := fi22Embed θ
  have hf : Function.Injective f := fi22Embed_injective θ hC
  have hτR : f t ∈ fi22R := fi22Embed_mem θ t
  have hτ : orderOf (f t) = 2 := by rw [orderOf_injective f hf t, ht]
  set K := S ⊓ Subgroup.centralizer ({t} : Set X)
  have hmap : K.map f = fi22P ⊓ Subgroup.centralizer {f t} := by
    ext p
    rw [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨hxS, hxt⟩ := Subgroup.mem_inf.1 hx
      rw [Subgroup.mem_centralizer_singleton_iff] at hxt
      refine ⟨?_, ?_⟩
      · rw [show f x = f ((⟨x, hxS⟩ : S) : X) from rfl, fi22Embed_of_mem]
        exact (θ _).2
      · rw [← map_mul, hxt, map_mul]
    · rintro ⟨hpP, hpt⟩
      have hs : f (θ.symm ⟨p, hpP⟩ : X) = p := by
        rw [fi22Embed_of_mem, MulEquiv.apply_symm_apply]
      refine ⟨θ.symm ⟨p, hpP⟩, Subgroup.mem_inf.2 ⟨(θ.symm ⟨p, hpP⟩).2,
        Subgroup.mem_centralizer_singleton_iff.2 ?_⟩, hs⟩
      apply hf
      rw [map_mul, map_mul, hs, hpt]
  have hK : CFSG.oddCore K = ⊥ := by
    have e : K ≃* ↥(fi22P ⊓ Subgroup.centralizer {f t}) :=
      (K.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hmap)
    exact oddCore_eq_bot_of_mulEquiv e.symm
      (CTUC_Fi22_all_involution_fixed_subgroups_odd_core_trivial (f t) hτR hτ)
  have hKC : K ≤ Subgroup.centralizer ({t} : Set X) := inf_le_right
  refine oddCore_eq_bot_of_le (K.subgroupOf (Subgroup.centralizer ({t} : Set X))) ?_
    (oddCore_eq_bot_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKC).symm hK)
  intro x hx
  rw [Subgroup.mem_subgroupOf]
  refine ⟨mem_of_odd_fi22Embed θ hC ?_, x.2⟩
  rw [Subgroup.orderOf_coe]
  exact odd_orderOf_of_mem_oddCore hx

end CFSG.Sporadic.FischerOddCore
