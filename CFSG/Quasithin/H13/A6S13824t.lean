module

public import CFSG.Quasithin.H13.A6S13824a
public import CFSG.Quasithin.H13.A6S13824p

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise IsMulCommutative

namespace S7C

theorem isSolvable_S43 : Group.IsSolvable ↥S43 := by
  have hp : ∀ σ : ↥S43, ∀ x : Fin 7, (σ.1 x).val < 4 ↔ x.val < 4 := fun σ x => by
    have h := (mem_relSub.mp σ.2) x x
    simpa [rS4] using h
  let φ : ↥S43 →* Perm {x : Fin 7 // x.val < 4} × Perm {x : Fin 7 // ¬ x.val < 4} :=
    { toFun := fun σ => ((σ : Perm (Fin 7)).subtypePerm (hp σ),
        (σ : Perm (Fin 7)).subtypePerm fun x => not_congr (hp σ x))
      map_one' := by
        ext x <;> rfl
      map_mul' := fun σ τ => by
        ext x <;> rfl }
  have hφ : Function.Injective φ := by
    intro σ τ h
    apply Subtype.ext
    ext x
    by_cases hx : x.val < 4
    · have := congrArg (fun p => ((p.1 ⟨x, hx⟩ : {x : Fin 7 // x.val < 4}) : Fin 7)) h
      simpa [φ] using congrArg Fin.val this
    · have := congrArg (fun p => ((p.2 ⟨x, hx⟩ : {x : Fin 7 // ¬ x.val < 4}) : Fin 7)) h
      simpa [φ] using congrArg Fin.val this
  have : Group.IsSolvable (Perm {x : Fin 7 // x.val < 4}) :=
    Equiv.Perm.isSolvable (by rw [Nat.card_eq_fintype_card]; decide)
  have : Group.IsSolvable (Perm {x : Fin 7 // ¬ x.val < 4}) :=
    Equiv.Perm.isSolvable (by rw [Nat.card_eq_fintype_card]; decide)
  exact Group.isSolvable_of_isSolvable_injective hφ

end S7C

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

namespace DK

variable {H K : Subgroup G} (hd : S.DK H K)
include hd

theorem irrSec_of_alt [IsMulCommutative ↥(conjClosure S.V3 H)] {W : Subgroup G}
    (hs : S.SecHyp H K (conjClosure S.V3 H) W)
    (hmax : ∀ W' : Subgroup G, W ≤ W' → W' ≤ conjClosure S.V3 H →
      H ≤ Subgroup.normalizer (W' : Set G) → W' = W ∨ W' = conjClosure S.V3 H)
    {α : ↥K →* alternatingGroup (Fin 7)} (hαs : Function.Surjective α)
    {ρ : ↥H →* Perm (Fin 7)} (hρα : ∀ k : ↥K, ρ ⟨(k : G), hd.hKH k.2⟩ = (α k : Perm (Fin 7)))
    (hρk : ∀ h : ↥H, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 H)
    (hA7 : ∀ h : ↥H, ρ h ∈ alternatingGroup (Fin 7)) :
    XMod.IsIrrSec ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      (W.subgroupOf (conjClosure S.V3 H)))
      (⊥ : Subgroup (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
        (W.subgroupOf (conjClosure S.V3 H)))) ⊤ := by
  refine ⟨bot_lt_iff_ne_bot.2 hs.top_ne_bot, fun J hJ _ _ => ?_⟩
  refine hs.irr hmax J fun h y hy => ?_
  obtain ⟨k, hk⟩ := hαs ⟨ρ h, hA7 h⟩
  set k' : ↥H := ⟨(k : G), hd.hKH k.2⟩ with hk'
  have hρ1 : ρ (k'⁻¹ * h) = 1 := by
    rw [map_mul, map_inv, hρα, hk, inv_mul_cancel]
  have hact : hs.act (k'⁻¹ * h) = 1 := (hs.act_eq_one_iff _).2 ((hρk _).1 hρ1)
  have e : hs.act h = hs.act k' := by
    rw [map_mul, map_inv, inv_mul_eq_one] at hact
    exact hact.symm
  rw [e]
  exact hJ ⟨_, (hs.mem_autSec_iff hs.hKH).2 ⟨k', k.2, rfl⟩⟩ y hy

theorem exists_coords7 {α : ↥K →* alternatingGroup (Fin 7)} (hαs : Function.Surjective α)
    {ρ : ↥H →* Perm (Fin 7)} (hρα : ∀ k : ↥K, ρ ⟨(k : G), hd.hKH k.2⟩ = (α k : Perm (Fin 7)))
    (hρk : ∀ h : ↥H, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 H)
    (hodd : ∃ t : ↥H, (t : G) ∈ T ∧ ρ t ∉ alternatingGroup (Fin 7)) :
    ∃ ρ' : ↥H →* Perm (Fin 7), Function.Surjective ρ' ∧
      (∀ h : ↥H, ρ' h = 1 ↔ (h : G) ∈ pCoreOf 2 H) ∧
      (∀ t : ↥H, (t : G) ∈ T → ρ' t ∈ S7C.T0) ∧
      ∀ s ∈ S7C.T0, ∃ t : ↥H, (t : G) ∈ T ∧ ρ' t = s := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t₀, ht₀T, ht₀⟩ := hodd
  have hsign : ∀ x : Perm (Fin 7), x ∉ alternatingGroup (Fin 7) → Perm.sign x = -1 := by
    intro x hx
    rw [Perm.mem_alternatingGroup] at hx
    rcases Int.units_eq_one_or (Perm.sign x) with h | h
    · exact absurd h hx
    · exact h
  have hρs : Function.Surjective ρ := by
    intro x
    by_cases hx : x ∈ alternatingGroup (Fin 7)
    · obtain ⟨k, hk⟩ := hαs ⟨x, hx⟩
      exact ⟨⟨(k : G), hd.hKH k.2⟩, by rw [hρα, hk]⟩
    · have hx' : x * (ρ t₀)⁻¹ ∈ alternatingGroup (Fin 7) := by
        rw [Perm.mem_alternatingGroup, map_mul, map_inv, hsign x hx, hsign _ ht₀]
        rfl
      obtain ⟨k, hk⟩ := hαs ⟨_, hx'⟩
      refine ⟨⟨(k : G), hd.hKH k.2⟩ * t₀, ?_⟩
      rw [map_mul, hρα, hk]
      simp
  have hTsyl := A5.isSylowTwoOf_of_le S.h13.sylow hd.hTH
  set T' := (T.subgroupOf H).map ρ with hT'
  have hT'p : IsPGroup 2 T' :=
    (hTsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hd.hTH).symm).map ρ
  have hT'i : ¬ 2 ∣ T'.index := fun h2 =>
    hTsyl.2.2 (h2.trans (Subgroup.index_map_dvd _ hρs))
  have hcard7 : Nat.card (Perm (Fin 7)) = 16 * 315 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have hT0i : ¬ 2 ∣ S7C.T0.index := by
    have h := S7C.T0.index_mul_card
    rw [S7C.card_T0, hcard7] at h
    have : S7C.T0.index = 315 := by omega
    rw [this]
    decide
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 7)) (hT'p.toSylow hT'i)
    (S7C.isPGroup_T0.toSylow hT0i)
  have hgT : (MulAut.conj g • T' : Subgroup (Perm (Fin 7))) = S7C.T0 := by
    have := congrArg (fun P : Sylow 2 (Perm (Fin 7)) => (P : Subgroup (Perm (Fin 7)))) hg
    simpa [Sylow.coe_subgroup_smul] using this
  refine ⟨(MulAut.conj g).toMonoidHom.comp ρ, ?_, fun h => ?_, fun t ht => ?_, fun s hs => ?_⟩
  · exact (MulAut.conj g).surjective.comp hρs
  · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    exact hρk h
  · rw [← hgT, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ ⟨t, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  · rw [← hgT] at hs
    obtain ⟨y, ⟨t, ht, rfl⟩, hy⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hs
    exact ⟨t, Subgroup.mem_subgroupOf.mp ht, hy⟩

end DK

end Setting4

end CFSG.Quasithin.H13.A6
