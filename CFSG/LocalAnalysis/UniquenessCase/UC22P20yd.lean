module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20yb

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def uc22pwIndHom (K S : Subgroup G) (hS : S ≤ normalizer (K : Set G)) :
    ↥S →* MulAut (Bar2 K) where
  toFun t := uc22p20uInd K (t : G) (hS t.2)
  map_one' := by
    ext x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    show uc22p20uInd K ((1 : S) : G) _ (QuotientGroup.mk l) = QuotientGroup.mk l
    rw [uc22p20uInd_mk]
    congr 1
    exact Subtype.ext (by simp)
  map_mul' t t' := by
    ext x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    show uc22p20uInd K ((t * t' : S) : G) _ (QuotientGroup.mk l) =
      uc22p20uInd K (t : G) _ (uc22p20uInd K (t' : G) _ (QuotientGroup.mk l))
    rw [uc22p20uInd_mk, uc22p20uInd_mk, uc22p20uInd_mk]
    congr 1
    exact Subtype.ext (by simp [mul_assoc])

theorem uc22pwIndHom_apply (K S : Subgroup G) (hS : S ≤ normalizer (K : Set G)) (t : S) (x : Bar2 K) :
    uc22pwIndHom K S hS t x = uc22p20uInd K (t : G) (hS t.2) x := rfl

theorem uc22pw_two_pow_mul_unique {e m e' m' : ℕ} (hm : Odd m) (hm' : Odd m')
    (h : 2 ^ e * m = 2 ^ e' * m') : e = e' ∧ m = m' := by
  have hv : ∀ {a b : ℕ}, Odd b → padicValNat 2 (2 ^ a * b) = a := by
    intro a b hb
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hb0 : b ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hb)
    rw [padicValNat.mul (by positivity) hb0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by simpa [even_iff_two_dvd] using Nat.not_even_iff_odd.2 hb)]
    simp
  have he : e = e' := by
    have := congrArg (padicValNat 2) h
    rwa [hv hm, hv hm'] at this
  subst he
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by positivity) h⟩

theorem uc22pw_good_of_induced (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M) {n e m' : ℕ}
    (hm' : Odd m') (hnem : n = 2 ^ e * m') {E : Subgroup (Bar2 L)}
    (hEU : E ≤ normalizer ((uc22p20iSylowBar D L : Subgroup (Bar2 L)) : Set (Bar2 L)))
    (hab : IsMulCommutative E) (hodd : Odd (Nat.card E))
    (hrank : ∀ p : ℕ, p.Prime → ∃ Q : Sylow p E, IsElemAbelian p (Q : Subgroup E) ∧ Nat.card Q ≤ p ^ 2)
    (hpi : piSet E = etaSet n)
    (hinv : ∀ g : ↥D.T, ∀ x ∈ E, uc22pwIndHom L D.T hL.1 g x ∈ E ⊔ uc22p20iSylowBar D L)
    (hα : ∀ g : ↥D.T, ∀ x ∈ oPi {p | p.Prime ∧ p ∣ 2 ^ m' - 1} E,
      uc22pwIndHom L D.T hL.1 g x * x⁻¹ ∈ uc22p20iSylowBar D L)
    (hw : ∃ w : Bar2 L, w ^ 2 = 1 ∧ (∀ x ∈ E, w * x * w⁻¹ = x⁻¹) ∧
      normalizer ((uc22p20iSylowBar D L : Subgroup (Bar2 L)) : Set (Bar2 L)) ⊔
        Subgroup.zpowers w = ⊤) :
    uc22pwGood D L n E := by
  refine ⟨hEU, hab, hodd, hrank, hpi, ?_, ?_, hw⟩
  · intro t ht htT x hx
    exact hinv ⟨t, htT⟩ x hx
  · intro e₂ m₂ hm₂ hn₂ t ht htT x hx
    obtain ⟨rfl, rfl⟩ := uc22pw_two_pow_mul_unique hm₂ hm' (hn₂.symm.trans hnem)
    exact hα ⟨t, htT⟩ x hx

end CFSG.LocalAnalysis.UniquenessCase.UC22
