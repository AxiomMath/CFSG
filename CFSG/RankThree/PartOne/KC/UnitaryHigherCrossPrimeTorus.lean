module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSetting

public section

namespace CFSG.RankThree.PartOne

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCPrimary
open scoped commutatorElement

theorem higher_unitary_cross_prime_isotypic_local_core_torus {ℓ f n p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hq : 3 < ℓ ^ f) (hn3 : 3 ≤ n) (hnp : n < p) (hp : p.Prime)
    (hpℓ : p ≠ ℓ) (B : Subgroup (MulAut (primeFormP h (idGram K n))))
    (hB : (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range ≤ B)
    (t : MulAut (primeFormP h (idGram K n)))
    (ht : t ∈ (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range) (htp : orderOf t = p) :
    (∃! x : gramSU h (idGram K n),
      orderOf x = p ∧ MulAut.conj (x : primeFormP h (idGram K n)) = t) ∧
    ∀ x : gramSU h (idGram K n), orderOf x = p →
      MulAut.conj (x : primeFormP h (idGram K n)) = t →
        (idCentralizerD h t =
          (Subgroup.centralizer ({liftUnitary x} :
            Set (primeFormUnitary h (idGram K n)))).map (primeFormConjHom h (idGram K n)) ∧
          ∀ A : primeFormUnitary h (idGram K n),
            primeFormConjHom h (idGram K n) A = 1 ↔ A ∈ idScalarKernel h n) ∧
        (∀ A : primeFormUnitary h (idGram K n), A ∈ idCenterUnits h x ↔
          ∃ hz : Matrix.toLin' ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∈
              commutant (Matrix.toLin' ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)),
            (⟨Matrix.toLin' ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), hz⟩ :
              commutant (Matrix.toLin' ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) ∈
            Subalgebra.center K
              (commutant (Matrix.toLin' ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))) ∧
        (∀ a : BlockIdx h x,
          idBlockImage h x (a.1 : K[X]) ≤ (MulAut.conj : primeFormP h (idGram K n) →*
            MulAut (primeFormP h (idGram K n))).range ∧
          CFSG.IsComponent ((idBlockImage h x (a.1 : K[X])).subgroupOf
            (B ⊓ Subgroup.centralizer ({t} : Set (MulAut (primeFormP h (idGram K n))))))) ∧
        (∀ a b : BlockIdx h x, (b.1 : K[X]) = dualPoly h.bar (a.1 : K[X]) →
          idBlockImage h x (b.1 : K[X]) = idBlockImage h x (a.1 : K[X])) ∧
        (∀ a b : BlockIdx h x, (b.1 : K[X]) ≠ (a.1 : K[X]) →
          (b.1 : K[X]) ≠ dualPoly h.bar (a.1 : K[X]) →
          ∀ g ∈ idBlockImage h x (a.1 : K[X]), ∀ g' ∈ idBlockImage h x (b.1 : K[X]),
            Commute g g') ∧
        ⁅idCentralizerD h t, idCentralizerD h t⁆ =
          ⨆ a : BlockIdx h x, idBlockImage h x (a.1 : K[X]) ∧
        CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore p)
            (B ⊓ Subgroup.centralizer ({t} : Set (MulAut (primeFormP h (idGram K n))))) ≤
          Subgroup.centralizer ((⁅idCentralizerD h t, idCentralizerD h t⁆ :
            Subgroup (MulAut (primeFormP h (idGram K n)))) :
              Set (MulAut (primeFormP h (idGram K n)))) ∧
        (idCentralizerD h t ⊓ Subgroup.centralizer ((⁅idCentralizerD h t, idCentralizerD h t⁆ :
            Subgroup (MulAut (primeFormP h (idGram K n)))) :
              Set (MulAut (primeFormP h (idGram K n)))) = idCenterN h t ∧
          idCenterN h t = (idCenterUnits h x).map (primeFormConjHom h (idGram K n)) ∧
          ∃ e : (idCenterUnits h x ⧸ (idScalarKernel h n).subgroupOf (idCenterUnits h x)) ≃*
              ↥(idCenterN h t),
            ∀ z : idCenterUnits h x, ((e (QuotientGroup.mk z) : ↥(idCenterN h t)) :
              MulAut (primeFormP h (idGram K n))) = primeFormConjHom h (idGram K n) z) ∧
        ((∀ a ∈ idCenterN h t ⊓ (B ⊓ Subgroup.centralizer ({t} :
              Set (MulAut (primeFormP h (idGram K n))))),
            ∀ b ∈ idCenterN h t ⊓ (B ⊓ Subgroup.centralizer ({t} :
              Set (MulAut (primeFormP h (idGram K n))))), a * b = b * a) ∧
          ((idCenterN h t ⊓ (B ⊓ Subgroup.centralizer ({t} :
              Set (MulAut (primeFormP h (idGram K n))))) ).subgroupOf
            (B ⊓ Subgroup.centralizer ({t} :
              Set (MulAut (primeFormP h (idGram K n)))))).Normal) := by
  have hq4 : 4 ≤ ℓ ^ f := hq
  have hZp : ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ p = 1 → c = 1 := by
    intro c _ hcn hcp
    have hcop : Nat.Coprime n p :=
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr (Nat.not_dvd_of_pos_of_lt (by omega) hnp)).symm
    have : c ^ Nat.gcd n p = 1 := pow_gcd_eq_one.mpr ⟨hcn, hcp⟩
    rwa [hcop, pow_one] at this
  obtain ⟨x₀, hx₀p, hx₀o, hx₀t⟩ := exists_lift_of_orderOf (h := h) hn3 hq hp hZp ht htp
  refine ⟨⟨x₀, ⟨hx₀o, hx₀t⟩, ?_⟩, ?_⟩
  · rintro y ⟨hyo, hyt⟩
    have hyp : y ^ p = 1 := by
      rw [← hyo]
      exact pow_orderOf_eq_one y
    have hπ : (y : primeFormP h (idGram K n)) = (x₀ : primeFormP h (idGram K n)) :=
      conj_injective hn3 hq (hyt.trans hx₀t.symm)
    exact eq_of_mk_eq_of_pow_eq_one_of_noTorsion hZp (by omega) hyp hx₀p hπ
  · intro x hxo hxt
    have hxp : x ^ p = 1 := by
      rw [← hxo]
      exact pow_orderOf_eq_one x
    have : Finite (primeFormP h (idGram K n)) := finite_primeFormP
    have L : LiftData h n p x := ⟨hn3, hq, hp, hpℓ, hZp, hxp⟩
    have S := L.projSetting B hB
    have H := L.primaryData
    have ht' : t = primeFormConjHom h (idGram K n) (liftUnitary x) := by
      rw [primeFormConjHom_liftUnitary, hxt]
    subst ht'
    have hC1 : idCentralizerD h (primeFormConjHom h (idGram K n) (liftUnitary x)) =
        (Subgroup.centralizer ({liftUnitary x} :
          Set (primeFormUnitary h (idGram K n)))).map (primeFormConjHom h (idGram K n)) :=
      L.centralizer_image
    have key : ∀ N' : Subgroup (MulAut (primeFormP h (idGram K n))),
        idCentralizerD h (primeFormConjHom h (idGram K n) (liftUnitary x)) = N' →
        idCenterN h (primeFormConjHom h (idGram K n) (liftUnitary x)) =
          (Subgroup.center ↥N').map N'.subtype := by
      intro N' hN'
      subst hN'
      rfl
    have hQ := key _ hC1
    have hker : (primeFormConjHom h (idGram K n)).ker = idScalarKernel h n :=
      Subgroup.ext fun A => primeFormConjHom_eq_one_iff hn3 hq A
    refine ⟨⟨hC1, fun A => primeFormConjHom_eq_one_iff hn3 hq A⟩,
      mem_idCenterUnits_iff, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a
      refine ⟨?_, S.isComponent_image a⟩
      have := Subgroup.map_mono (f := primeFormConjHom h (idGram K n)) (S.F_le_Hs a)
      rwa [map_gramSU_eq_range_conj] at this
    · intro a b hbd
      have hb : (b.1 : K[X]) = (dualFactor H a.1 : K[X]) := hbd
      unfold idBlockImage idSpecialBlock
      rw [hb, specialBlock_dualFactor H hq4 a.1 a.2]
    · rintro a b hba hbd _ ⟨A, hA, rfl⟩ _ ⟨A', hA', rfl⟩
      have h1 := commute_specialBlock_of_ne H a.1 b.1 hba hbd hA hA'
      have h2 : toLinU h n (A * A') = toLinU h n (A' * A) := by
        rw [map_mul, map_mul]
        exact h1.eq
      have h3 : A * A' = A' * A := toLinU_injective h2
      show primeFormConjHom h (idGram K n) A * primeFormConjHom h (idGram K n) A' = _
      rw [← map_mul, ← map_mul, h3]
    · rw [hC1]
      exact S.commutator_image_eq
    · rw [hC1]
      exact S.core_le_centralizer_derived hp
    · refine ⟨?_, ?_, ?_⟩
      · rw [hQ, hC1]
        exact S.inf_centralizer_derived_eq_center
      · rw [hQ]
        exact S.center_image_eq
      · obtain ⟨e0, he0⟩ := exists_quotient_equiv (primeFormConjHom h (idGram K n))
          (idCenterUnits h x)
        have hQ' : idCenterN h (primeFormConjHom h (idGram K n) (liftUnitary x)) =
            (idCenterUnits h x).map (primeFormConjHom h (idGram K n)) := by
          rw [hQ]
          exact S.center_image_eq
        refine ⟨((QuotientGroup.quotientMulEquivOfEq (by rw [hker])).trans e0).trans
          (MulEquiv.subgroupCongr hQ'.symm), fun z => ?_⟩
        exact he0 z
    · rw [hQ]
      exact ⟨fun a ha b hb => ProjSetting.center_inf_comm (Subgroup.mem_inf.mp ha).1
        (Subgroup.mem_inf.mp hb).1, S.center_inf_normal⟩

end CFSG.RankThree.PartOne
