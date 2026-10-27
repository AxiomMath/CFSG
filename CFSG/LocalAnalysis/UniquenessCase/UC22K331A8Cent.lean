module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K331Basic
public import CFSG.SignalizerFunctorTheorem.Inheritance.Sections
public import CFSG.RankThree.PartTwo.Sec21.FF84LemmaFHolds
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpSylowAlt8

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

open CFSG.SignalizerFunctorTheorem

theorem k331_isSectionOf_centralizer {L : Type} [Group L] [Finite L]
    (h8 : ∀ E : Subgroup L, (∀ x ∈ E, x * x = 1) → Nat.card E ≤ 8) {K : Subgroup L}
    (hK : IsAlt (Bar2 K) 8) :
    ∃ z : L, orderOf z = 2 ∧
      IsSectionOf (alternatingGroup (Fin 8)) (Subgroup.centralizer ({z} : Set L)) := by
  obtain ⟨e⟩ := hK
  have : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  let f : ↥K →* alternatingGroup (Fin 8) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hfker : f.ker = CFSG.pCore 2 ↥K := by
    ext k
    simp [f, MonoidHom.mem_ker]
  have hQ : CFSG.pCore 2 ↥K ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp (hfker.trans hbot)
    obtain ⟨E, -, hE16, hEsq⟩ :=
      CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer.exists_elemAbelian_sixteen_of_equiv_alt8
        (MulEquiv.ofBijective f ⟨hinj, hf⟩)
    have := h8 E hEsq
    omega
  obtain ⟨E, hEn, hE1, -, hEsq, -⟩ :=
    CFSG.RankThree.PartTwo.Sec21.FF84.exists_normal_elemAbelian_of_pGroup (CFSG.pCore 2 ↥K)
      CFSG.pCore_isPGroup hQ
  have hE8 : Nat.card E ≤ 8 := by
    have h := h8 (E.map K.subtype) (by
      rintro _ ⟨x, hx, rfl⟩
      exact congrArg Subtype.val (hEsq x hx))
    rwa [Subgroup.card_map_of_injective K.subtype_injective] at h
  have := hEn
  rcases (IsSectionOf.of_surjective f hf).of_hom (MulAut.conjNormal (H := E)) with hker | hout
  ·
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE1
    have ha2 : ((a : ↥K) : L) * ((a : ↥K) : L) = 1 := congrArg Subtype.val (hEsq a a.2)
    have ha1 : ((a : ↥K) : L) ≠ 1 := fun h => ha (Subtype.ext (Subtype.ext h))
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine ⟨((a : ↥K) : L), orderOf_eq_prime (by rw [sq]; exact ha2) ha1, ?_⟩
    refine hker.of_injective
      ((K.subtype.comp (MulAut.conjNormal (H := E)).ker.subtype).codRestrict _ fun k => ?_)
      fun x y hxy => Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hxy))
    have hk : (MulAut.conjNormal (H := E) (k : ↥K)) a = a := by
      rw [MonoidHom.mem_ker.mp k.2]
      rfl
    have hk' : (k : ↥K) * (a : ↥K) * (k : ↥K)⁻¹ = (a : ↥K) := by
      rw [← MulAut.conjNormal_apply, hk]
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hk')
  ·
    exfalso
    let φ : MulAut ↥E → Equiv.Perm {x : ↥E // x ≠ 1} := fun σ =>
      Equiv.Perm.subtypePerm σ.toEquiv fun x => by simp
    have hφ : Function.Injective φ := by
      intro σ τ h
      ext x
      by_cases hx : x = 1
      · rw [hx, map_one, map_one]
      · simpa [φ] using congrArg (fun π : Equiv.Perm {x : ↥E // x ≠ 1} => (π ⟨x, hx⟩ : ↥E)) h
    have : Finite (MulAut ↥E) := Finite.of_injective φ hφ
    have hlt : Nat.card {x : ↥E // x ≠ 1} < Nat.card ↥E :=
      Finite.card_subtype_lt (p := fun x : ↥E => x ≠ 1) (x := 1) (by simp)
    have hAut : Nat.card (MulAut ↥E) ≤ 5040 :=
      calc Nat.card (MulAut ↥E) ≤ Nat.card (Equiv.Perm {x : ↥E // x ≠ 1}) :=
            Nat.card_le_card_of_injective φ hφ
        _ = (Nat.card {x : ↥E // x ≠ 1}).factorial := Nat.card_perm
        _ ≤ (7 : ℕ).factorial := Nat.factorial_le (by omega)
        _ = 5040 := rfl
    obtain ⟨H, g, hg⟩ := hout
    have hcard := (Nat.card_le_card_of_surjective g hg).trans (Subgroup.card_le_card_group H)
    rw [nat_card_alt_eight] at hcard
    omega

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3
