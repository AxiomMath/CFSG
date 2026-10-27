module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeFour
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeSub

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K K₀ S X Y : Subgroup G} {p : ℕ} {g x : G}

def Nine3Minimal (V T A K : Subgroup G) : Prop :=
  ∀ K' : Subgroup G, K' ∈ calPMTA V T A → K' ≤ K → K' = K

theorem Nine3Minimal.eq_of_mem_le (h : Nine3Minimal V T A K) {K' : Subgroup G}
    (hK' : K' ∈ calPMTA V T A) (hle : K' ≤ K) : K' = K := h K' hK' hle

theorem exists_nine3Minimal_le (hK : K ∈ calPMTA V T A) :
    ∃ K₀ : Subgroup G, K₀ ∈ calPMTA V T A ∧ K₀ ≤ K ∧ Nine3Minimal V T A K₀ := by
  classical
  let s : Set (Subgroup G) := {K' | K' ∈ calPMTA V T A ∧ K' ≤ K}
  have hsne : s.Nonempty := ⟨K, hK, le_rfl⟩
  have hfin : s.Finite := Set.toFinite _
  let t := hfin.toFinset
  have htne : t.Nonempty := by
    obtain ⟨K', hK'⟩ := hsne
    exact ⟨K', by simpa [t] using hK'⟩
  obtain ⟨K₀, hK₀t, hmin⟩ := Finset.exists_min_image t (fun K : Subgroup G => Nat.card ↥K) htne
  have hK₀s : K₀ ∈ s := by simpa [t] using hK₀t
  refine ⟨K₀, hK₀s.1, hK₀s.2, ?_⟩
  intro K' hK' hle
  have hK's : K' ∈ s := ⟨hK', hle.trans hK₀s.2⟩
  have hK't : K' ∈ t := by simpa [t] using hK's
  have hcard : Nat.card ↥K₀ ≤ Nat.card ↥K' := hmin K' hK't
  have hinj : Function.Injective fun z : ↥K' => (⟨z.1, hle z.2⟩ : ↥K₀) := by
    intro z w hzw
    exact Subtype.ext (congrArg (fun q : ↥K₀ => (q : G)) hzw)
  have hcard' : Nat.card ↥K' ≤ Nat.card ↥K₀ := Nat.card_le_card_of_injective _ hinj
  exact Subgroup.eq_of_le_of_card_ge hle (by omega)

structure Nine3CoreMin (V T A K S X : Subgroup G) (p : ℕ) : Prop where
  core : Nine3Core V T A K S X p
  minimal : Nine3Minimal V T A K

@[expose] def Nine3ReduceInP (V T A : Subgroup G) : Prop :=
  ∀ (K S X : Subgroup G) (p : ℕ), Nine3Seed V T A K S X p →
    ∀ (Y : Subgroup G), Nine3Fam K S X A Y →
      (∀ Y' : Subgroup G, Nine3Fam K S X A Y' → Y' ≤ Y → Y' = Y) →
        Nine3Core V T A (S ⊔ Y) S Y p → (S ⊔ Y) ∈ calPMTA V T A

theorem nine3ReduceInP_holds (V T A : Subgroup G) : Nine3ReduceInP V T A := by
  intro K S X p hseed Y hY _hYmin hcore
  classical
  have hAab : IsElemAbelian 2 A := by
    obtain ⟨k, hk⟩ := hseed.conj
    rw [hk]
    exact E3.isElemAbelian_conjSubgroup hseed.h9.hyp7.1 k
  have hTinf : T ⊓ (S ⊔ Y) = S := by
    have hQ2 : IsPGroup 2 ↥(T ⊓ (S ⊔ Y)) := hseed.h9.sylow.isPGroup.to_le inf_le_left
    have hSQ : S ≤ T ⊓ (S ⊔ Y) := le_inf hcore.leS le_sup_left
    have hQle : T ⊓ (S ⊔ Y) ≤ S ⊔ Y := inf_le_right
    have hcardQ : Nat.card ↥(T ⊓ (S ⊔ Y)) = S.relIndex (T ⊓ (S ⊔ Y)) * Nat.card ↥S := by
      rw [← Subgroup.relIndex_mul_card (H := S) (K := T ⊓ (S ⊔ Y)),
        inf_eq_left.mpr hSQ]
    obtain ⟨n, hn⟩ := hQ2.exists_card_eq
    have hrel_dvd_pow : S.relIndex (T ⊓ (S ⊔ Y)) ∣ 2 ^ n := by
      rw [← hn, hcardQ]
      exact dvd_mul_right _ _
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hrel_dvd_pow
    have hrel_dvd : S.relIndex (T ⊓ (S ⊔ Y)) ∣ S.relIndex (S ⊔ Y) := by
      rw [← Subgroup.relIndex_mul_relIndex (H := S) (K := T ⊓ (S ⊔ Y))
        (L := S ⊔ Y) hSQ hQle]
      exact dvd_mul_right _ _
    have hodd : ¬ 2 ∣ S.relIndex (S ⊔ Y) := hcore.hyp.base.sylowTwo.not_dvd_relIndex
    have hk0 : k = 0 := by
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · rfl
      · exfalso
        apply hodd
        refine (?_ : 2 ∣ S.relIndex (T ⊓ (S ⊔ Y))).trans hrel_dvd
        rw [hk]
        exact pow_dvd_pow 2 (Nat.succ_le_of_lt hkpos)
    have hrel1 : S.relIndex (T ⊓ (S ⊔ Y)) = 1 := by rw [hk, hk0]; simp
    exact le_antisymm (Subgroup.relIndex_eq_one.mp hrel1) hSQ
  have hIsE : E1.IsE 1 (S ⊔ Y) (T ⊓ (S ⊔ Y)) A (S ⊔ Y) := by
    rw [hTinf]
    exact nine_two_isE hseed.h9.hyp7 hseed.h9.rk_gt hcore.hyp hcore.A_mem_nineOmegaIn
  have hτ : E1.tauOf (normalizer (V : Set G)) T A ≤ T ⊓ (S ⊔ Y) :=
    le_inf (hcore.tau.trans hcore.leS) (hcore.tau.trans le_sup_left)
  have hSyl : IsSylowIn 2 (T ⊓ (S ⊔ Y)) (S ⊔ Y) := by
    rw [hTinf]
    exact hcore.hyp.base.sylowTwo
  have hEany : E1.IsEAny (normalizer (V : Set G)) T A (S ⊔ Y) :=
    ⟨1, E1.eight_two hseed.h9.sylow hcore.leT hAab hcore.hyp.base.le hτ hSyl hIsE⟩
  refine ⟨hEany, Y, hcore.hyp.mem, ?_⟩
  rw [hTinf]
  exact hcore.hyp.base.toTwoPTwo.coe_sup_eq_mul le_rfl
    (fun s hs y hy => (Subgroup.mem_normalizer_iff.mp hs.2 y).mp hy)

end CFSG.LocalAnalysis.WeakClosure81

end
