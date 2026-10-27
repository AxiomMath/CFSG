module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Core
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Blk
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312WordsHat
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312WordsIdx
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312WordsDefs
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBase
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatLat
public import Certificates.Certificate4170

public section

namespace CFSG.Quasithin.A312M23

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin.A312Words
open scoped Pointwise

theorem no_member_of_action {G : Type} [Group G] [Finite G] {α : Type} [MulAction G α]
    {S B Y : Subgroup G} (hS : IsPGroup 2 S) (hB : B ∈ lFamily S) (hY : B ⊔ S = Y) {m : ℕ}
    (hm : m = 3) (pt : Fin m → α) (hpt : Function.Injective pt)
    (hYp : ∀ z ∈ Y, ∀ i, ∃ j, z • pt i = pt j) {x : G} (hx : x ∈ Y) {k : ℕ} (hk : k % 2 = 1)
    (hxk : x ^ k = 1) (hmov : ∃ i, x • pt i ≠ pt i) : False := by
  subst hm
  classical
  have hxA : x ∈ perfectCore Y := by
    rw [← hY]
    exact odd_mem_perfectCore' hS hB (hY ▸ hx) hk hxk
  have hAY : perfectCore Y ≤ Y := perfectCore_le Y
  let ρ := actHom Y pt hpt hYp
  let ρA : ↥(perfectCore Y) →* Equiv.Perm (Fin 3) := ρ.comp (Subgroup.inclusion hAY)
  have hperf : Group.IsPerfect ↥(perfectCore Y) :=
    Subgroup.isPerfect_iff.mpr (perfectCore_perfect Y)
  have hR : Group.IsPerfect ↥ρA.range := Group.IsPerfect.range ρA
  have hsolv : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
  have hRs : Group.IsSolvable ↥ρA.range :=
    Group.isSolvable_of_isSolvable_injective (f := ρA.range.subtype)
      (Subgroup.subtype_injective _)
  have hsub : Subsingleton ↥ρA.range := by
    by_contra hns
    have : Nontrivial ↥ρA.range := not_subsingleton_iff_nontrivial.mp hns
    exact Group.IsPerfect.not_isSolvable ↥ρA.range hRs
  have h1 : ρA ⟨x, hxA⟩ = 1 := by
    have := Subsingleton.elim (⟨ρA ⟨x, hxA⟩, ⟨_, rfl⟩⟩ : ↥ρA.range) 1
    exact congrArg Subtype.val this
  obtain ⟨i, hi⟩ := hmov
  exact hi ((actHom_eq_one_iff Y pt hpt hYp ⟨x, hx⟩).mp h1 i)

theorem not_member_of_triFacts {G : Type} [Group G] [Finite G] {α : Type} [MulAction G α]
    {S B Y : Subgroup G} (hS : IsPGroup 2 S) (hB : B ∈ lFamily S) (hY : B ⊔ S = Y)
    (hF : TriFacts α Y) : False := by
  obtain ⟨pt, hpt, hYp, x, hx, k, hk, hxk, hmov⟩ := hF
  exact no_member_of_action hS hB hY rfl pt hpt hYp hx hk hxk hmov

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]
  {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]

end CFSG.Quasithin.A312M23
