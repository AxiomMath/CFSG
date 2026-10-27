module

public import CFSG.SignalizerFunctorTheorem.Quadratic.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Core

public section

namespace CFSG.SignalizerFunctorTheorem.Quadratic

section Qp

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (H : Subgroup G)

omit [Finite G] [Fact p.Prime] in
theorem Qp_le : Qp p H ≤ H :=
  iSup₂_le fun _ hN => hN.1

omit [Finite G] [Fact p.Prime] in
theorem le_Qp {N : Subgroup G} (hNH : N ≤ H) (hN : (N.subgroupOf H).Normal)
    (hcop : Nat.Coprime p (Nat.card N)) : N ≤ Qp p H :=
  le_iSup₂_of_le N ⟨hNH, hN, hcop⟩ le_rfl

theorem Qp_eq_map_pPrimeCore : Qp p H = (CFSG.pPrimeCore p H).map H.subtype := by
  apply le_antisymm
  · refine iSup₂_le fun N hN => ?_
    obtain ⟨hNH, hNn, hNc⟩ := hN
    rw [← Subgroup.map_subgroupOf_eq_of_le hNH]
    refine Subgroup.map_mono (le_sSup ⟨hNn, ?_⟩)
    rwa [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv] at hNc
  · refine le_Qp H (Subgroup.map_subtype_le _) ?_ ?_
    · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
      exact CFSG.pPrimeCore_normal
    · rw [Subgroup.card_map_of_injective H.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card

theorem Qp_normal : ((Qp p H).subgroupOf H).Normal := by
  rw [Qp_eq_map_pPrimeCore, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  exact CFSG.pPrimeCore_normal

theorem coprime_card_Qp : Nat.Coprime p (Nat.card (Qp p H)) := by
  rw [Qp_eq_map_pPrimeCore, Subgroup.card_map_of_injective H.subtype_injective]
  exact CFSG.pPrimeCore_coprime_card

theorem Qp_cj {g : G} (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    (Qp p H).map (MulAut.conj g).toMonoidHom = Qp p H := by
  have key : ∀ g ∈ Subgroup.normalizer (H : Set G),
      (Qp p H).map (MulAut.conj g).toMonoidHom ≤ Qp p H := by
    intro g hg
    refine le_Qp H ?_ ⟨fun n hn k => ?_⟩ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hg x).mp (Qp_le H hx)
    · obtain ⟨y, hy, hyn⟩ := hn
      have hn' : (n : G) = g * y * g⁻¹ := hyn.symm
      have hk : g⁻¹ * k * g ∈ H := by
        refine (Subgroup.mem_normalizer_iff.mp hg _).mpr ?_
        have : g * (g⁻¹ * (k : G) * g) * g⁻¹ = k := by group
        rw [this]
        exact k.2
      have h1 : g⁻¹ * k * g * y * (g⁻¹ * k * g)⁻¹ ∈ Qp p H :=
        (Qp_normal H).conj_mem ⟨y, Qp_le H hy⟩ hy ⟨_, hk⟩
      refine ⟨_, h1, ?_⟩
      show g * (g⁻¹ * (k : G) * g * y * (g⁻¹ * (k : G) * g)⁻¹) * g⁻¹ =
        (k : G) * (n : G) * (k : G)⁻¹
      rw [hn']
      group
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact coprime_card_Qp H
  refine le_antisymm (key g hg) fun x hx => ?_
  refine ⟨g⁻¹ * x * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
  have := key g⁻¹ (inv_mem hg) ⟨x, hx, rfl⟩
  simpa [MulAut.conj_apply, mul_assoc] using this

end Qp

section S1

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {H : Subgroup G}

theorem centralizer_le_Qp (hsolv : Group.IsSolvable H)
    (hnoP : ∀ N : Subgroup G, N ≤ H → (N.subgroupOf H).Normal → IsPGroup p N → N = ⊥) :
    H ⊓ Subgroup.centralizer (Qp p H : Set G) ≤ Qp p H := by
  have hpc : CFSG.pCore p H = ⊥ := by
    refine le_bot_iff.mp (sSup_le fun N ⟨hNn, hNp⟩ => ?_)
    have hN' : N.map H.subtype = ⊥ := by
      refine hnoP _ (Subgroup.map_subtype_le N) ?_ (hNp.map _)
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
      exact hNn
    exact le_bot_iff.mpr ((Subgroup.map_eq_bot_iff_of_injective N H.subtype_injective).mp hN')
  have hFit : CFSG.fittingSubgroup H ≤ CFSG.pPrimeCore p H := by
    rw [CFSG.fitting_eq_sup_pCore]
    refine iSup_le fun q => ?_
    by_cases hqp : q.1.1 = p
    · have : CFSG.pCore q.1.1 H = ⊥ := by rw [hqp]; exact hpc
      rw [this]
      exact bot_le
    · refine le_sSup ⟨CFSG.pCore_normal, ?_⟩
      obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (G := H) (p := q.1.1)).exists_card_eq
      rw [hn]
      exact Nat.Coprime.pow_right n
        ((Nat.coprime_primes (Fact.out : p.Prime) (Fact.out : q.1.1.Prime)).mpr (Ne.symm hqp))
  rintro x ⟨hxH, hxC⟩
  have h1 : (⟨x, hxH⟩ : H) ∈ Subgroup.centralizer (CFSG.fittingSubgroup H : Set H) := by
    intro y hy
    have hyQ : (y : G) ∈ Qp p H := by
      rw [Qp_eq_map_pPrimeCore]
      exact Subgroup.mem_map_of_mem _ (hFit hy)
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC _ hyQ)
  have h2 := CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv h1
  rw [Qp_eq_map_pPrimeCore]
  exact ⟨_, hFit h2, rfl⟩

end S1

section HypSection

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
  {H : Subgroup (LGL p V)}

theorem Hyp.centralizer_le_Qp (hH : Hyp H) :
    H ⊓ Subgroup.centralizer (Qp p H : Set (LGL p V)) ≤ Qp p H :=
  Quadratic.centralizer_le_Qp hH.solvable hH.noP

end HypSection

end CFSG.SignalizerFunctorTheorem.Quadratic
