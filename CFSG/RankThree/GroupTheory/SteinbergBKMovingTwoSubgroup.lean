module

public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBK

open Subgroup CFSG.RankThree.LocalRank

instance thetaOddCore_normal (p : ℕ) (L : Type*) [Group L] :
    (inSubgroup (pPrimeCore 2) (aschbacherSolvableCore p L)).Normal :=
  ConjAct.normal_of_characteristic_of_normal

theorem moving_two_subgroup_normally_generates {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    {L A : Type*} [Group L] [Finite L] [Group A] [MulDistribMulAction A L]
    (hLperf : Group.IsPerfect L)
    (hLq : IsQuasisimple (L ⧸ inSubgroup (pPrimeCore 2) (aschbacherSolvableCore p L)))
    (hcent : ∀ U : Subgroup L, U ≤ aschbacherSolvableCore p L → IsPGroup 2 U →
      (∀ a : A, ∀ x ∈ U, a • x ∈ U) → ∀ a : A, ∀ x ∈ U, a • x = x)
    (T : Subgroup L) (hT1 : T ≠ ⊥) (hT2 : IsPGroup 2 T) (hTinv : ∀ a : A, ∀ x ∈ T, a • x ∈ T)
    (hTA : commutatorSubgroup A L T = T) :
    normalClosure (T : Set L) = ⊤ := by
  classical
  set N := aschbacherSolvableCore p L with hNdef
  set O := inSubgroup (pPrimeCore 2) N with hOdef
  obtain ⟨hNsolv, -, hNp, hNmax, -⟩ := solvable_prime_complement_core_characterization
    (H := L) hp
  have hON : O ≤ N := map_subtype_le _
  have hOsolv : Group.IsSolvable O :=
    Group.isSolvable_of_isSolvable_injective (f := ((pPrimeCore 2 N).equivMapOfInjective
      N.subtype N.subtype_injective).symm.toMonoidHom) (MulEquiv.injective _)
  have hOp : ¬ p ∣ Nat.card O := fun h => hNp (h.trans (card_dvd_of_le hON))
  set π := QuotientGroup.mk' O with hπ
  have hnc : ¬ T.map π ≤ center (L ⧸ O) := by
    intro hcen
    set TO := (T.map π).comap π with hTO
    have hTTO : T ≤ TO := le_comap_map π T
    have hOTO : O ≤ TO := by
      intro x hx
      change π x ∈ T.map π
      rw [hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
      exact one_mem _
    have hTmapn : (T.map π).Normal := ⟨fun x hx g => by
      rw [mem_center_iff.mp (hcen hx) g, mul_inv_cancel_right]
      exact hx⟩
    have hTOn : TO.Normal := hTmapn.comap π
    have hTOsolv : Group.IsSolvable TO := by
      let g : TO →* T.map π := (π.comp TO.subtype).codRestrict (T.map π) fun x => x.2
      let f : O.subgroupOf TO →* TO := (O.subgroupOf TO).subtype
      have hcomm : IsMulCommutative (T.map π) := ⟨⟨fun a b => Subtype.ext
        ((mem_center_iff.mp (hcen a.2) b).symm)⟩⟩
      have : Group.IsSolvable (O.subgroupOf TO) :=
        Group.isSolvable_of_isSolvable_injective
          (f := (subgroupOfEquivOfLe hOTO).toMonoidHom) (MulEquiv.injective _)
      refine Group.isSolvable_of_ker_le_range f g fun x hx => ?_
      have hx1 : π (x : L) = 1 := congrArg Subtype.val hx
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
      exact ⟨⟨x, hx1⟩, rfl⟩
    have hTOp : ¬ p ∣ Nat.card TO := by
      intro hdvd
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
      have hπx : π (x : L) ∈ T.map π := x.2
      obtain ⟨y, hy, hyx⟩ := hπx
      obtain ⟨k, hk⟩ := hT2 ⟨y, hy⟩
      have h1 : π (x : L) ^ 2 ^ k = 1 := by
        rw [← hyx, ← map_pow]
        have := congrArg Subtype.val hk
        simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
        rw [this, map_one]
      have hxp := pow_orderOf_eq_one x
      rw [hx] at hxp
      have h2 : π (x : L) ^ p = 1 := by
        rw [← map_pow, ← Subgroup.coe_pow, hxp, Subgroup.coe_one, map_one]
      have hcop : Nat.Coprime (2 ^ k) p :=
        Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hodd))
      have h3 : π (x : L) = 1 := by
        have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
        rwa [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
      apply hOp
      have hxp' : orderOf (⟨x, h3⟩ : O) = p :=
        (Subgroup.orderOf_coe (⟨x, h3⟩ : O)).symm.trans ((Subgroup.orderOf_coe x).trans hx)
      rw [← hxp']
      exact orderOf_dvd_natCard _
    have hTN : T ≤ N := hTTO.trans (hNmax TO hTOn hTOsolv hTOp)
    have hfix := hcent T hTN hT2 hTinv
    apply hT1
    rw [← hTA, eq_bot_iff, commutatorSubgroup, closure_le]
    rintro _ ⟨a, h, hh, rfl⟩
    rw [hfix a h hh, inv_mul_cancel]
    exact one_mem _
  set M := normalClosure (T : Set L) with hM
  have hMn : M.Normal := normalClosure_normal
  have hTM : T ≤ M := subset_normalClosure
  have hMπ : M.map π = ⊤ := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hLq (hMn.map π
      (QuotientGroup.mk'_surjective O)) with h | h
    · exact h
    · exact absurd ((map_mono hTM).trans h) hnc
  have hMO : M ⊔ O = ⊤ := by
    have h := comap_map_eq π M
    rw [hMπ, comap_top, QuotientGroup.ker_mk'] at h
    exact h.symm
  have hsurj : Function.Surjective ((QuotientGroup.mk' M).comp O.subtype) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective M q
    have hg : g ∈ ((M ⊔ O : Subgroup L) : Set L) := hMO ▸ mem_top g
    rw [normal_mul] at hg
    obtain ⟨m, hm, o, ho, rfl⟩ := hg
    refine ⟨⟨o, ho⟩, ?_⟩
    have hm1 : QuotientGroup.mk' M m = 1 := (QuotientGroup.eq_one_iff m).mpr hm
    rw [MonoidHom.comp_apply, map_mul, hm1, one_mul]
    rfl
  have hsolv : Group.IsSolvable (L ⧸ M) := Group.isSolvable_of_surjective hsurj
  have htop : commutator (L ⧸ M) = ⊤ := by
    rw [_root_.commutator_def, ← map_top_of_surjective _ (QuotientGroup.mk'_surjective M),
      ← map_commutator, ← _root_.commutator_def, Group.IsPerfect.commutator_eq_top]
  have hsub : Subsingleton (L ⧸ M) := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := L ⧸ M)).ne htop
  refine eq_top_iff.mpr fun g _ => ?_
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

end CFSG.RankThree.GroupTheory.SteinbergBK
