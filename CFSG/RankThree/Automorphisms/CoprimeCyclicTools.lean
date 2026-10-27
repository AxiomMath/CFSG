module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.RankThree.Automorphisms

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {p : ℕ}

theorem inf_eq_bot_of_isPGroup_of_coprime {H : Type*} [Group H] [Finite H] [Fact p.Prime]
    {P N : Subgroup H} (hP : IsPGroup p P) (hN : Nat.Coprime (Nat.card N) p) : P ⊓ N = ⊥ := by
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  refine disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard ?_)
  rw [hk]
  exact Nat.Coprime.pow_left k hN.symm

theorem card_map_of_injective_comp {H Q : Type*} [Group H] [Group Q] (f : H →* Q)
    (S : Subgroup H) (hf : Function.Injective (f.comp S.subtype)) :
    Nat.card (S.map f) = Nat.card S := by
  have h : S.map f = (f.comp S.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [h]
  exact (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm

theorem isCyclic_of_injective_comp_of_isCyclic_map {H Q : Type*} [Group H] [Group Q]
    (f : H →* Q) (S : Subgroup H) (hf : Function.Injective (f.comp S.subtype))
    [IsCyclic (S.map f)] : IsCyclic S := by
  have hmem : ∀ x : S, f x ∈ S.map f := fun x => Subgroup.mem_map_of_mem f x.2
  refine isCyclic_of_injective ((f.comp S.subtype).codRestrict _ hmem) fun x y hxy => hf ?_
  exact congrArg Subtype.val hxy

theorem injective_comp_of_isPGroup {H Q : Type*} [Group H] [Finite H] [Group Q] [Fact p.Prime]
    (f : H →* Q) (hf : Nat.Coprime (Nat.card f.ker) p) {P : Subgroup H} (hP : IsPGroup p P) :
    Function.Injective (f.comp P.subtype) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hmem : (x : H) ∈ P ⊓ f.ker := ⟨x.2, hx⟩
  rw [inf_eq_bot_of_isPGroup_of_coprime hP hf, Subgroup.mem_bot] at hmem
  exact Subtype.ext hmem

theorem isCyclic_of_le_of_inf_eq_bot {Y : Type*} [Group Y] {D E P : Subgroup Y}
    [(D.subgroupOf E).Normal] [IsCyclic (E ⧸ D.subgroupOf E)] (hPE : P ≤ E) (hPD : P ⊓ D = ⊥) :
    IsCyclic P := by
  refine isCyclic_of_injective
    ((QuotientGroup.mk' (D.subgroupOf E)).comp (Subgroup.inclusion hPE)) ?_
  rw [injective_iff_map_eq_one]
  intro v hv
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at hv
  have hmem : (v : Y) ∈ P ⊓ D := ⟨v.2, hv⟩
  rw [hPD, Subgroup.mem_bot] at hmem
  exact Subtype.ext hmem

theorem isCyclic_of_isPGroup_of_normal_mul {H : Type*} [Group H] [Finite H] [Fact p.Prime]
    {I A : Subgroup H} [I.Normal] (hI : Nat.Coprime (Nat.card I) p)
    (hIA : ∀ h : H, ∃ i ∈ I, ∃ a ∈ A, h = i * a)
    (hA : ∀ Q : Subgroup H, Q ≤ A → IsPGroup p Q → IsCyclic Q)
    {P : Subgroup H} (hP : IsPGroup p P) : IsCyclic P := by
  set π := QuotientGroup.mk' I with hπ
  have hπker : π.ker = I := QuotientGroup.ker_mk' I
  have hinj : ∀ Q : Subgroup H, IsPGroup p Q → Function.Injective (π.comp Q.subtype) :=
    fun Q hQ => injective_comp_of_isPGroup π (by rw [hπker]; exact hI) hQ
  set Pb := P.map π with hPb
  set B := A ⊓ Pb.comap π with hB
  have hBmap : B.map π = Pb := by
    refine le_antisymm (Subgroup.map_le_iff_le_comap.2 inf_le_right) ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hi, a, ha, rfl⟩ := hIA x
    have hi1 : π i = 1 := by
      rw [← MonoidHom.mem_ker, hπker]
      exact hi
    have hia : π (i * a) = π a := by
      rw [map_mul, hi1, one_mul]
    refine ⟨a, ⟨ha, ?_⟩, hia.symm⟩
    change π a ∈ Pb
    rw [← hia]
    exact Subgroup.mem_map_of_mem π hx
  have hcardPb : Nat.card Pb = Nat.card P := card_map_of_injective_comp π P (hinj P hP)
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hdvd : p ^ k ∣ Nat.card B := by
    rw [← hk, ← hcardPb, ← hBmap]
    exact Subgroup.card_map_dvd B π
  obtain ⟨S', hS'⟩ := Sylow.exists_subgroup_card_pow_prime p hdvd
  set S := S'.map B.subtype with hS
  have hcardS : Nat.card S = p ^ k := by
    rw [hS, Subgroup.card_map_of_injective B.subtype_injective, hS']
  have hSB : S ≤ B := Subgroup.map_subtype_le S'
  have hSp : IsPGroup p S := IsPGroup.of_card hcardS
  have : IsCyclic S := hA S (hSB.trans inf_le_left) hSp
  have hSmap : S.map π = Pb := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [← hBmap]
      exact Subgroup.map_mono hSB
    · rw [hcardPb, hk, card_map_of_injective_comp π S (hinj S hSp), hcardS]
  have : IsCyclic (S.map π) := by
    have h : S.map π = (π.comp S.subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [h]
    exact isCyclic_of_surjective _ (π.comp S.subtype).rangeRestrict_surjective
  have : IsCyclic Pb := by
    rw [← hSmap]
    infer_instance
  exact isCyclic_of_injective_comp_of_isCyclic_map π P (hinj P hP)

theorem coprime_card_inner {G : Type*} [Group G] [Finite G] (hp : p.Prime)
    (hpG : ¬ p ∣ Nat.card G) : Nat.Coprime (Nat.card (inner G)) p :=
  Nat.Coprime.coprime_dvd_left (Subgroup.card_range_dvd _)
    ((Nat.Prime.coprime_iff_not_dvd hp).2 hpG).symm

theorem isCyclic_of_isPGroup_of_outer {G : Type*} [Group G] [Finite G] (hp : p.Prime)
    (hpG : ¬ p ∣ Nat.card G) (hout : ∀ Q : Subgroup (Outer G), IsPGroup p Q → IsCyclic Q)
    {P : Subgroup (MulAut G)} (hP : IsPGroup p P) : IsCyclic P := by
  have : Fact p.Prime := ⟨hp⟩
  have hinj := injective_comp_of_isPGroup (QuotientGroup.mk' (inner G))
    (by rw [QuotientGroup.ker_mk']; exact coprime_card_inner hp hpG) hP
  have := hout _ (hP.map (QuotientGroup.mk' (inner G)))
  exact isCyclic_of_injective_comp_of_isCyclic_map _ P hinj

theorem isCyclic_of_isPGroup_of_mulEquiv {T G : Type*} [Group T] [Group G] (e : T ≃* G)
    (hG : ∀ P : Subgroup (MulAut G), IsPGroup p P → IsCyclic P)
    {P : Subgroup (MulAut T)} (hP : IsPGroup p P) : IsCyclic P := by
  have hinj : Function.Injective ((MulAut.congr e).toMonoidHom.comp P.subtype) :=
    (MulAut.congr e).injective.comp Subtype.val_injective
  have := hG _ (hP.map (MulAut.congr e).toMonoidHom)
  exact isCyclic_of_injective_comp_of_isCyclic_map _ P hinj

theorem le_card_ker_of_isElementaryAbelian {H : Type*} [Group H] (hp : p.Prime)
    (hH : ∀ P : Subgroup H, IsPGroup p P → IsCyclic P) {E : Type*} [Group E]
    [IsElementaryAbelian p E] (hE : Nat.card E = p ^ 2) (α : E →* H) :
    p ≤ Nat.card α.ker := by
  have hrp : IsPGroup p α.range :=
    (IsElementaryAbelian.isPGroup p E).of_surjective α.rangeRestrict α.rangeRestrict_surjective
  have := hH α.range hrp
  have hexp : Monoid.exponent α.range ∣ p := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun y => ?_
    obtain ⟨x, rfl⟩ := α.rangeRestrict_surjective y
    rw [← map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p E) x, map_one]
  rw [IsCyclic.exponent_eq_card] at hexp
  have hsplit : Nat.card E = Nat.card α.range * Nat.card α.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange α).toEquiv]
  have hrle : Nat.card α.range ≤ p := Nat.le_of_dvd hp.pos hexp
  refine le_of_not_gt fun hlt => ?_
  have h1 : Nat.card α.range * Nat.card α.ker < p * p :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ hrle) (Nat.mul_lt_mul_of_pos_left hlt hp.pos)
  rw [← hsplit, hE, sq] at h1
  exact lt_irrefl _ h1

end CFSG.RankThree.Automorphisms
