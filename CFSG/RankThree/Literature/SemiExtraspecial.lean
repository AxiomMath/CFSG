module

public import CFSG.Monster.B.Short.InvolutionCentralizer

public section

namespace CFSG.RankThree.Literature

open Subgroup
open scoped commutatorElement

variable {p : ℕ} {P : Type*} [Group P]

@[expose] def IsSemiExtraspecial (p : ℕ) (P : Type*) [Group P] : Prop :=
  ∀ (N : Subgroup P) [N.Normal], N < center P →
    (∀ K : Subgroup P, N < K → K ≤ center P → K = center P) → IsExtraspecialPGroup p (P ⧸ N)

namespace Beisiegel

theorem commutatorElement_mem (x y : P) : ⁅x, y⁆ ∈ commutator P := by
  rw [_root_.commutator_def]
  exact commutator_mem_commutator (mem_top x) (mem_top y)

theorem exists_maximal_between [Finite P] {K H : Subgroup P} (hKH : K < H) :
    ∃ N : Subgroup P, K ≤ N ∧ N < H ∧ ∀ L : Subgroup P, N < L → L ≤ H → L = H := by
  obtain ⟨N, ⟨hKN, hNH⟩, hmax⟩ :=
    (Set.toFinite {L : Subgroup P | K ≤ L ∧ L < H}).exists_maximal ⟨K, le_rfl, hKH⟩
  refine ⟨N, hKN, hNH, fun L hNL hLH => ?_⟩
  by_contra hne
  exact hNL.not_ge (hmax ⟨hKN.trans hNL.le, lt_of_le_of_ne hLH hne⟩ hNL.le)

theorem map_center_le (N : Subgroup P) [N.Normal] :
    (center P).map (QuotientGroup.mk' N) ≤ center (P ⧸ N) := by
  rintro _ ⟨z, hz, rfl⟩
  rw [mem_center_iff]
  intro y
  induction y using QuotientGroup.induction_on with
  | H y =>
    change (y : P ⧸ N) * (z : P ⧸ N) = (z : P ⧸ N) * (y : P ⧸ N)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.mp hz y]

theorem map_commutator_mk (N : Subgroup P) [N.Normal] :
    (commutator P).map (QuotientGroup.mk' N) = commutator (P ⧸ N) := by
  rw [_root_.commutator_def, _root_.commutator_def, map_commutator,
    map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]

theorem sup_eq_of_map_eq {N H₁ H₂ : Subgroup P} [N.Normal] (hN : N ≤ H₂)
    (h : H₁.map (QuotientGroup.mk' N) = H₂.map (QuotientGroup.mk' N)) : H₁ ⊔ N = H₂ := by
  have := congrArg (comap (QuotientGroup.mk' N)) h
  rwa [comap_map_eq, comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hN] at this

theorem center_quotient_eq_map [Finite P] (hp : p.Prime) {N : Subgroup P} [N.Normal]
    (hNZ : N < center P) (hE : IsExtraspecialPGroup p (P ⧸ N)) :
    center (P ⧸ N) = (center P).map (QuotientGroup.mk' N) := by
  have hle := map_center_le (P := P) N
  have hne : Nat.card ((center P).map (QuotientGroup.mk' N)) ≠ 1 := by
    intro h1
    obtain ⟨z, hz, hzN⟩ := IsConcreteLE.exists_of_lt hNZ
    have h := Subgroup.eq_bot_of_card_eq _ h1
    have : (QuotientGroup.mk' N z) ∈ (center P).map (QuotientGroup.mk' N) := mem_map_of_mem _ hz
    rw [h, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact hzN this
  have hdvd : Nat.card ((center P).map (QuotientGroup.mk' N)) ∣ p := by
    rw [← hE.2.2.2]
    exact card_dvd_of_le hle
  have hcard : Nat.card ((center P).map (QuotientGroup.mk' N)) = p :=
    ((Nat.dvd_prime hp).mp hdvd).resolve_left hne
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hE.2.2.2])).symm

theorem commutator_sup_eq [Finite P] (hp : p.Prime) (hS : IsSemiExtraspecial p P)
    {N : Subgroup P} [N.Normal] (hNZ : N < center P)
    (hmax : ∀ K : Subgroup P, N < K → K ≤ center P → K = center P) :
    commutator P ⊔ N = center P := by
  have hE := hS N hNZ hmax
  refine sup_eq_of_map_eq hNZ.le ?_
  rw [map_commutator_mk, hE.2.1, center_quotient_eq_map hp hNZ hE]

theorem frattini_le_center [Finite P] (hp : p.Prime) (hS : IsSemiExtraspecial p P)
    {N : Subgroup P} [N.Normal] (hNZ : N < center P)
    (hmax : ∀ K : Subgroup P, N < K → K ≤ center P → K = center P) :
    frattini P ≤ center P := by
  have hE := hS N hNZ hmax
  have h1 : frattini P ≤ (frattini (P ⧸ N)).comap (QuotientGroup.mk' N) :=
    frattini_le_comap_frattini_of_surjective (QuotientGroup.mk'_surjective N)
  rwa [hE.2.2.1, center_quotient_eq_map hp hNZ hE, comap_map_eq, QuotientGroup.ker_mk',
    sup_eq_left.mpr hNZ.le] at h1

theorem isCoatom_map_mk {N M : Subgroup P} [N.Normal] (hNM : N ≤ M) (hM : IsCoatom M) :
    IsCoatom (M.map (QuotientGroup.mk' N)) := by
  have hcm : (M.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) = M := by
    rw [comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hNM]
  refine ⟨fun h => hM.1 ?_, fun K hK => ?_⟩
  · rw [← hcm, h, comap_top]
  · have h1 : M < K.comap (QuotientGroup.mk' N) := by
      rw [← hcm]
      exact (comap_lt_comap_of_surjective (QuotientGroup.mk'_surjective N)).mpr hK
    have h2 := hM.2 _ h1
    rw [← map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) K, h2,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]

theorem frattini_quotient_le_map [Finite P] {N : Subgroup P} [N.Normal] (hN : N ≤ frattini P) :
    frattini (P ⧸ N) ≤ (frattini P).map (QuotientGroup.mk' N) := by
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
  refine mem_map_of_mem _ ?_
  have hmem : ∀ M : Subgroup P, IsCoatom M → y ∈ M := by
    intro M hM
    have hNM : N ≤ M := hN.trans (frattini_le_coatom hM)
    have h1 : QuotientGroup.mk' N y ∈ M.map (QuotientGroup.mk' N) :=
      frattini_le_coatom (isCoatom_map_mk hNM hM) hx
    have h2 : y ∈ (M.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) := h1
    rwa [comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hNM] at h2
  change y ∈ Order.radical (Subgroup P)
  simp only [Order.radical, mem_iInf]
  exact fun M hM => hmem M hM

end Beisiegel

open Beisiegel

theorem IsSemiExtraspecial.special [Finite P] (hp : p.Prime) (hP : IsPGroup p P) [Nontrivial P]
    (hS : IsSemiExtraspecial p P) :
    commutator P = center P ∧ frattini P = center P ∧ IsElementaryAbelian p (center P) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (IsPGroup p P) := ⟨hP⟩
  have hZbot : ⊥ < center P := by
    have := hP.center_nontrivial
    exact bot_lt_iff_ne_bot.mpr ((nontrivial_iff_ne_bot _).mp this)
  obtain ⟨N₀, -, hN₀Z, hN₀max⟩ := exists_maximal_between hZbot
  have : N₀.Normal := normal_of_le_center hN₀Z.le
  have hcomm_le : commutator P ≤ center P :=
    le_sup_left.trans (commutator_sup_eq hp hS hN₀Z hN₀max).le
  have hcomm : commutator P = center P := by
    by_contra hne
    obtain ⟨N, hcN, hNZ, hNmax⟩ := exists_maximal_between (lt_of_le_of_ne hcomm_le hne)
    have : N.Normal := normal_of_le_center hNZ.le
    have h := commutator_sup_eq hp hS hNZ hNmax
    rw [sup_eq_right.mpr hcN] at h
    exact hNZ.ne h
  have hfr : frattini P = center P :=
    le_antisymm (frattini_le_center hp hS hN₀Z hN₀max)
      (hcomm ▸ commutator_le_frattini_of_isPGroup (p := p))
  have hpow : ∀ x : P, x ^ p ∈ center P := fun x => hfr ▸ pth_power_mem_frattini_of_isPGroup x
  have hcommp : ∀ x y : P, ⁅x, y⁆ ^ p = 1 := by
    intro x y
    have hc : Commute x ⁅x, y⁆ :=
      (mem_center_iff.mp (hcomm_le (commutatorElement_mem x y)) x)
    rw [hc.commutatorElement_pow_left p, commutatorElement_eq_one_iff_mul_comm]
    exact (mem_center_iff.mp (hpow x) y).symm
  have hexp : ∀ z ∈ center P, z ^ p = 1 := by
    intro z hz
    rw [← hcomm, commutator_eq_closure] at hz
    induction hz using closure_induction with
    | mem z hz =>
      obtain ⟨x, y, rfl⟩ := hz
      exact hcommp x y
    | one => exact one_pow p
    | mul z w hz _ ihz ihw =>
      have hzc : z ∈ center P := hcomm_le (by rw [commutator_eq_closure]; exact hz)
      have hzw : Commute z w := (mem_center_iff.mp hzc w).symm
      rw [hzw.mul_pow, ihz, ihw, one_mul]
    | inv z _ ih => rw [inv_pow, ih, inv_one]
  refine ⟨hcomm, hfr, ?_⟩
  exact
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun z =>
        Subtype.ext (by simpa using hexp z z.2) }

theorem IsSemiExtraspecial.commutator_map [Finite P] (hp : p.Prime) (hP : IsPGroup p P)
    [Nontrivial P] (hS : IsSemiExtraspecial p P) {x : P} (hx : x ∉ center P) :
    (∃ f : P →* center P, (∀ y, (f y : P) = ⁅x, y⁆) ∧ Function.Surjective f ∧
      f.ker = centralizer {x}) ∧
      Set.range (fun y => ⁅x, y⁆) = (center P : Set P) ∧
      closure (Set.range fun y => ⁅x, y⁆) = center P ∧
      (centralizer {x}).index = Nat.card (center P) := by
  have hspec := hS.special hp hP
  have hc : commutator P ≤ center P := hspec.1.le
  set f := CFSG.Monster.B.Short.commHom hc x with hf
  have hfapp : ∀ y, (f y : P) = ⁅x, y⁆ := fun y => CFSG.Monster.B.Short.commHom_apply hc x y
  have hsurj : Function.Surjective f := by
    rw [← MonoidHom.range_eq_top]
    by_contra hne
    have hlt : f.range.map (center P).subtype < center P := by
      refine lt_of_le_of_ne (map_subtype_le f.range) ?_
      intro h
      apply hne
      rw [eq_top_iff]
      intro z _
      have hz : (z : P) ∈ f.range.map (center P).subtype := by rw [h]; exact z.2
      obtain ⟨w, hw, hwz⟩ := hz
      rwa [← Subtype.ext hwz]
    obtain ⟨N, hHN, hNZ, hNmax⟩ := exists_maximal_between hlt
    have : N.Normal := normal_of_le_center hNZ.le
    have hE := hS N hNZ hNmax
    have hxc : QuotientGroup.mk' N x ∈ center (P ⧸ N) := by
      rw [mem_center_iff]
      intro y
      induction y using QuotientGroup.induction_on with
      | H y =>
        have hmem : ⁅x, y⁆ ∈ N := hHN ⟨f y, ⟨y, rfl⟩, by simp [hfapp]⟩
        have h1 : ((⁅x, y⁆ : P) : P ⧸ N) = 1 := (QuotientGroup.eq_one_iff _).mpr hmem
        rw [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
          QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv] at h1
        change (y : P ⧸ N) * (x : P ⧸ N) = (x : P ⧸ N) * (y : P ⧸ N)
        have h2 : (x : P ⧸ N) * (y : P ⧸ N) = (y : P ⧸ N) * (x : P ⧸ N) :=
          commutatorElement_eq_one_iff_mul_comm.mp (by rw [commutatorElement_def]; exact h1)
        exact h2.symm
    rw [center_quotient_eq_map hp hNZ hE] at hxc
    have h2 : x ∈ (center P ⊔ N) := by
      rw [← QuotientGroup.ker_mk' N, ← comap_map_eq]
      exact hxc
    rw [sup_eq_left.mpr hNZ.le] at h2
    exact hx h2
  have hker : f.ker = centralizer {x} := CFSG.Monster.B.Short.ker_commHom hc x
  have hrange : Set.range (fun y => ⁅x, y⁆) = (center P : Set P) := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact hc (commutatorElement_mem x y)
    · intro hz
      obtain ⟨y, hy⟩ := hsurj ⟨z, hz⟩
      exact ⟨y, by show ⁅x, y⁆ = z; rw [← hfapp, hy]⟩
  refine ⟨⟨f, hfapp, hsurj, hker⟩, hrange, by rw [hrange, closure_eq], ?_⟩
  rw [← hker, index_ker, MonoidHom.range_eq_top.mpr hsurj, card_top]

theorem isSemiExtraspecial_of_special {Q : Type*} [Group Q] [Finite Q] (hp : p.Prime)
    (hQ : IsPGroup p Q) (hcomm : commutator Q = center Q) (hfr : frattini Q = center Q)
    (hx : ∀ x : Q, x ∉ center Q → closure (Set.range fun y => ⁅x, y⁆) = center Q) :
    IsSemiExtraspecial p Q := by
  have : Fact p.Prime := ⟨hp⟩
  intro N _ hNZ hNmax
  have hcen : center (Q ⧸ N) = (center Q).map (QuotientGroup.mk' N) := by
    refine le_antisymm (fun q hq => ?_) (map_center_le N)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
    by_cases hxZ : x ∈ center Q
    · exact mem_map_of_mem _ hxZ
    · exfalso
      have hle : closure (Set.range fun y => ⁅x, y⁆) ≤ N := by
        rw [closure_le]
        rintro _ ⟨y, rfl⟩
        show ⁅x, y⁆ ∈ N
        rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, map_commutatorElement,
          commutatorElement_eq_one_iff_mul_comm]
        exact (mem_center_iff.mp hq (QuotientGroup.mk' N y)).symm
      rw [hx x hxZ] at hle
      exact hNZ.not_ge hle
  have hindex : N.relIndex (center Q) = p := by
    have hZp : IsPGroup p (center Q) := hQ.to_subgroup (center Q)
    have : Group.IsNilpotent (center Q) := hZp.isNilpotent
    have hco : IsCoatom (N.subgroupOf (center Q)) := by
      refine ⟨fun h => hNZ.not_ge (subgroupOf_eq_top.mp h), fun K hK => ?_⟩
      have hinj := (center Q).subtype_injective
      have hNK : N < K.map (center Q).subtype := by
        have := (map_lt_map_iff_of_injective hinj).mpr hK
        rwa [subgroupOf_map_subtype, inf_eq_left.mpr hNZ.le] at this
      have hKZ := hNmax _ hNK (map_subtype_le K)
      rw [← comap_map_eq_self_of_injective hinj K, hKZ]
      exact subgroupOf_self _
    exact (hZp.isCoatom_iff_index_eq_prime).mp hco
  have hcard : Nat.card ((center Q).map (QuotientGroup.mk' N)) = p := by
    have h := index_ker ((QuotientGroup.mk' N).comp (center Q).subtype)
    rw [MonoidHom.range_comp, range_subtype, ← MonoidHom.comap_ker, QuotientGroup.ker_mk'] at h
    rw [← h, ← hindex]
    rfl
  refine ⟨hQ.to_quotient N, ?_, ?_, ?_⟩
  · rw [← map_commutator_mk, hcomm, hcen]
  · refine le_antisymm ?_ ?_
    · rw [hcen, ← hfr]
      exact Beisiegel.frattini_quotient_le_map (hfr ▸ hNZ.le)
    · rw [hcen, ← hfr, map_le_iff_le_comap]
      exact frattini_le_comap_frattini_of_surjective (QuotientGroup.mk'_surjective N)
  · rw [hcen, hcard]

end CFSG.RankThree.Literature
