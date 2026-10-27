module

public import CFSG.Milestones.ASVolI.F4Conjugacy
public import CFSG.Milestones.ASVolI.F4Sylow

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

section Generic

variable {G : Type} [Group G]

theorem burnsideF429_perfectCore_le_of_odd_index [Finite G] {P N : Subgroup G} (hNP : N ≤ P)
    (hnorm : ∀ g ∈ P, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (hodd : ¬ 2 ∣ N.relIndex P) :
    perfectCore P ≤ N := by
  haveI hN : (N.subgroupOf P).Normal := ⟨fun n hn k => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hnorm k.1 k.2 n.1 hn⟩
  have hcard : Odd (Nat.card (↥P ⧸ N.subgroupOf P)) := by
    rw [← Subgroup.index_eq_card]
    exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hodd)
  have hsolv : Group.IsSolvable (↥P ⧸ N.subgroupOf P) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hcard
  obtain ⟨n, hn⟩ := (isSolvable_def (G := ↥P ⧸ N.subgroupOf P)).1 hsolv
  have hle : derivedSeries ↥P n ≤ N.subgroupOf P := by
    intro x hx
    have h1 := map_derivedSeries_le_derivedSeries (QuotientGroup.mk' (N.subgroupOf P)) n
      ⟨x, hx, rfl⟩
    rw [hn, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  intro x hx
  have h2 := perfectCore_le_derivedSeriesOf P n hx
  rw [derivedSeriesOf_eq_map_derivedSeries] at h2
  obtain ⟨y, hy, rfl⟩ := h2
  exact Subgroup.mem_subgroupOf.1 (hle hy)

theorem burnsideF429_perfectCore_conj_mem {P : Subgroup G} {g : G} (hg : g ∈ P) {x : G}
    (hx : x ∈ perfectCore P) : g * x * g⁻¹ ∈ perfectCore P :=
  (Subgroup.mem_normalizer_iff.1 (normalizer_le_normalizer_perfectCore P
    (Subgroup.le_normalizer hg)) x).1 hx

theorem burnsideF429_oPPrime_eq_perfectCore [Finite G] {P S : Subgroup G}
    (hS : ChF.IsSylowOf 2 S P) (hSP : S ≤ perfectCore P) : oPPrime 2 P = perfectCore P := by
  refine le_antisymm ?_ ?_
  · exact burnsideF4gD4Inv_oPPrime_le_of_sylow (S := S) (perfectCore_le P)
      (fun g hg n hn => burnsideF429_perfectCore_conj_mem hg hn) hS hSP
  · have hOP : oPPrime 2 P ≤ P := (Subgroup.closure_le P).2 fun _ hx => hx.1
    have hSO : S ≤ oPPrime 2 P := by
      intro s hs
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hS.2.1) ⟨s, hs⟩
      refine Subgroup.subset_closure ⟨hS.1 hs, k, ?_⟩
      rw [← hk, Subgroup.orderOf_mk]
    refine burnsideF429_perfectCore_le_of_odd_index hOP ?_ ?_
    · intro g hg n hn
      have hc : g * n * g⁻¹ ∈ (oPPrime 2 P).map (MulAut.conj g).toMonoidHom := ⟨n, hn, rfl⟩
      have hmap : (oPPrime 2 P).map (MulAut.conj g).toMonoidHom ≤ oPPrime 2 P := by
        unfold oPPrime
        rw [MonoidHom.map_closure]
        refine Subgroup.closure_mono ?_
        rintro _ ⟨y, ⟨hyP, k, hk⟩, rfl⟩
        refine ⟨P.mul_mem (P.mul_mem hg hyP) (P.inv_mem hg), k, ?_⟩
        have h3 := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y
        rw [h3, hk]
      exact hmap hc
    · intro h
      exact hS.2.2 (h.trans (Subgroup.relIndex_dvd_of_le_left P hSO))

theorem burnsideF429_le_perfectCore_of_sylow [Finite G] {P S S' : Subgroup G}
    (hS' : ChF.IsSylowOf 2 S' P) (hS'P : S' ≤ perfectCore P) (hSP : S ≤ P) (hS : IsPGroup 2 S) :
    S ≤ perfectCore P := by
  obtain ⟨x, hx, hle⟩ := F7.isSylowTwoOf_exists_conj_le hS' hSP hS
  intro s hs
  have h1 : x⁻¹ * s * x ∈ S' := mem_conjSub.1 (hle hs)
  have h2 := burnsideF429_perfectCore_conj_mem hx (hS'P h1)
  simpa [mul_assoc] using h2

theorem burnsideF429_isSylowOf_of_le {S H P : Subgroup G} (hS : ChF.IsSylowOf 2 S H) (hSP : S ≤ P)
    (hPH : P ≤ H) : ChF.IsSylowOf 2 S P := by
  refine ⟨hSP, hS.2.1, fun h => hS.2.2 ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex S P H hSP hPH]
  exact Dvd.dvd.mul_right h _

theorem burnsideF429_perfectCore_map {C : Type} [Group C] (φ : C →* G)
    (hφ : Function.Injective φ) (P : Subgroup C) :
    perfectCore (P.map φ) = (perfectCore P).map φ := by
  unfold perfectCore
  rw [Subgroup.map_iInf φ hφ]
  congr 1
  funext n
  exact (map_derivedSeriesOf φ P n).symm

theorem burnsideF429_isSylowOf_map {C : Type} [Group C] (φ : C →* G)
    (hφ : Function.Injective φ) {U P : Subgroup C} (hU : ChF.IsSylowOf 2 U P) :
    ChF.IsSylowOf 2 (U.map φ) (P.map φ) := by
  refine ⟨Subgroup.map_mono hU.1, hU.2.1.map φ, ?_⟩
  rw [Subgroup.relIndex_map_map_of_injective U P hφ]
  exact hU.2.2

theorem burnsideF429_inf_eq_map {Gp M : Subgroup G} {D : Type} [Group D] (Ψ : D ≃* ↥Gp)
    {P : Subgroup D} (h : M.subgroupOf Gp = P.map Ψ.toMonoidHom) :
    Gp ⊓ M = P.map (Gp.subtype.comp Ψ.toMonoidHom) := by
  rw [← Subgroup.map_map, ← h, Subgroup.subgroupOf_map_subtype, inf_comm]

theorem burnsideF429_le_perfectCore_of_model [Finite G] {Gp M : Subgroup G} {C : Type} [Group C]
    (Ψ : C ≃* ↥Gp) {P U : Subgroup C} (hP : M.subgroupOf Gp = P.map Ψ.toMonoidHom)
    (hU : ChF.IsSylowOf 2 U P) (hUP : U ≤ perfectCore P) {S : Subgroup G} (hS : S ≤ Gp ⊓ M)
    (hS2 : IsPGroup 2 S) : S ≤ perfectCore (Gp ⊓ M) := by
  have hφ : Function.Injective (Gp.subtype.comp Ψ.toMonoidHom) :=
    Gp.subtype_injective.comp Ψ.injective
  rw [burnsideF429_inf_eq_map Ψ hP] at hS ⊢
  rw [burnsideF429_perfectCore_map _ hφ] at ⊢
  rw [← burnsideF429_perfectCore_map _ hφ]
  exact burnsideF429_le_perfectCore_of_sylow (burnsideF429_isSylowOf_map _ hφ hU)
    (by rw [burnsideF429_perfectCore_map _ hφ]; exact Subgroup.map_mono hUP) hS hS2

end Generic

section Setting


theorem burnsideF429_sylowBar_inf {κ : GLKind} {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 κ p f Gp M₁ M₂) {M : Subgroup E}
    (hM : M₁ ⊓ M₂ ≤ M) : ChF.IsSylowOf p (pCoreOf p (Gp ⊓ (M₁ ⊓ M₂))) (Gp ⊓ M) := by
  have hS := burnsideF45_sylow hyp
  have hSB : pCoreOf p (Gp ⊓ (M₁ ⊓ M₂)) ≤ Gp ⊓ (M₁ ⊓ M₂) := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  refine ⟨hSB.trans (inf_le_inf_left Gp hM), hS.2.1, fun h => hS.2.2 ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex _ (Gp ⊓ M) Gp (hSB.trans (inf_le_inf_left Gp hM))
    inf_le_left]
  exact Dvd.dvd.mul_right h _

theorem burnsideF429_clause3_of {κ : GLKind} {f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 κ 2 f Gp M₁ M₂)
    (h1 : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₁))
    (h2 : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₂)) :
    oPPrime 2 (Gp ⊓ M₁) = perfectCore (Gp ⊓ M₁) ∧
      oPPrime 2 (Gp ⊓ M₂) = perfectCore (Gp ⊓ M₂) := by
  haveI := hyp.finite
  exact ⟨burnsideF429_oPPrime_eq_perfectCore (burnsideF429_sylowBar_inf hyp inf_le_left) h1,
    burnsideF429_oPPrime_eq_perfectCore (burnsideF429_sylowBar_inf hyp inf_le_right) h2⟩

end Setting

end CFSG.ASVolI
