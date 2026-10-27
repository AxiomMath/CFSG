module

public import CFSG.Quasithin.Vol2.Ch11SecBRootLiftAux

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Quasithin.A1b
open scoped commutatorElement

section Criterion

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_tauOf_self {H T A : Subgroup G} (hTH : T ≤ H) (hAT : A ≤ T)
    (hA : IsElemAbelian 2 A) : A ≤ tauOf H T A := by
  intro a ha
  refine ⟨hAT ha, CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hTH (hAT ha)),
    fun b hb => ?_⟩
  have hab : a * b = b * a := congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  rw [commutatorElement_def, hab]
  simp

theorem le_nParam_of_tau {H T A U : Subgroup G} {f : ℕ} (hT : IsSylowIn 2 T H) (hAT : A ≤ T)
    (hA : IsElemAbelian 2 A) (hf : 2 ≤ f)
    (huniq : ∀ h ∈ H, A1b.conjSub h A ≤ T → A1b.conjSub h A = A) (hUτ : U ≤ tauOf H T A)
    (hS : ¬ H ≤ Subgroup.normalizer (A : Set G))
    (hR : ∀ K : Subgroup G, K ≤ H → U ≤ K → A ≤ K → ¬ K ≤ Subgroup.normalizer (A : Set G) →
      ¬ Group.IsSolvable ↥K ∧ 2 ^ f ≤ Nat.card ↥(barRad ↥K (A.subgroupOf K))) :
    (f : ℕ∞) ≤ nParam H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := hT.1
  have hAH : A ≤ H := hAT.trans hTH
  set Ω : Set (Subgroup G) := {B | ∃ h ∈ H, B = A1b.conjSub h A} with hΩdef
  have hΩ : IsInvColl H Ω := by
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨h, hh, rfl⟩ x hx
      rw [A1b.mem_conjSub_iff] at hx
      have e : x = h * (h⁻¹ * x * h) * h⁻¹ := by group
      rw [e]
      exact H.mul_mem (H.mul_mem hh (hAH hx)) (H.inv_mem hh)
    · rintro _ ⟨h, hh, rfl⟩
      exact isElemAbelian_map' _ hA
    · rintro _ ⟨h, hh, rfl⟩ g hg
      exact ⟨g * h, H.mul_mem hg hh, by rw [A1b.conjSub_mul]⟩
  have hAΩ : A ∈ Ω := ⟨1, H.one_mem, (A1b.conjSub_one A).symm⟩
  have hW : weakClosure T Ω = A := by
    refine le_antisymm (iSup₂_le fun B hB => iSup_le fun hBT => ?_) (le_weakClosure hAΩ hAT)
    obtain ⟨h, hh, rfl⟩ := hB
    exact (huniq h hh hBT).le
  have hAτ := le_tauOf_self hTH hAT hA
  have hE : ∀ A' ∈ Ω, A' ≤ T → ∀ K, IsE (f - 1) H T A' K →
      K ≤ Subgroup.normalizer (A : Set G) := by
    rintro _ ⟨h, hh, rfl⟩ hA'T K ⟨hKH, hτ, -, hrank⟩
    rw [huniq h hh hA'T] at hτ hrank
    by_contra hKN
    obtain ⟨hns, hcard⟩ := hR K hKH (fun u hu => (hτ (hUτ hu)).2) (fun a ha => (hτ (hAτ ha)).2)
      hKN
    rcases hrank with ⟨h1, -⟩ | ⟨-, hc⟩
    · exact hns (RootLift.isSolvable_of_eOne h1)
    · have hlt : 2 ^ (f - 1) < 2 ^ f := Nat.pow_lt_pow_right (by norm_num) (by omega)
      exact absurd (hcard.trans hc) (not_le.mpr hlt)
  by_contra hlt
  rw [not_le] at hlt
  have hf' : (f : ℕ∞) = ((f - 1 : ℕ) : ℕ∞) + 1 := by
    rw [show f = (f - 1) + 1 from (Nat.sub_add_cancel (by omega : 1 ≤ f)).symm]
    simp
  rw [hf', ENat.lt_add_one_iff (ENat.natCast_ne_top _)] at hlt
  have hInE : InE (f - 1) H := (nParam_le_iff (by omega)).1 hlt
  have hgen := hInE T hT Ω hΩ
  apply hS
  rw [← hgen]
  refine sup_le ?_ ?_
  · exact iSup₂_le fun A' hA' => iSup_le fun hA'T => iSup₂_le fun K hK => hE A' hA' hA'T K hK
  · rw [hW]
    exact inf_le_right

end Criterion

end CFSG.Quasithin.Vol2.Ch11.SecE3
