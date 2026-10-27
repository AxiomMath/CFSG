module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Defs

namespace CFSG
end CFSG
open CFSG

open scoped commutatorElement

variable (p : ℕ) (G : Type*) [Group G]

section pCore_properties

-- Lemmas from pCore.lean

lemma CFSG.normalPSubgroups_nonempty : (normalPSubgroups p G).Nonempty :=
    ⟨⊥, ⟨inferInstance, IsPGroup.of_bot⟩⟩

lemma CFSG.directedOn_normal_pGroups :
    DirectedOn (· ≤ ·) (normalPSubgroups p G) := by
  intro A hA B hB
  have hA_normal := hA.1
  have hB_normal := hB.1
  have hA_p := hA.2
  have hB_p := hB.2
  refine ⟨A ⊔ B, ⟨?_, ?_⟩, le_sup_left, le_sup_right⟩
  · exact Subgroup.sup_normal A B
  · exact IsPGroup.to_sup_of_normal_right hA.2 hB.2

variable {G} {p}

/-- `p`-core of `G` is normal. -/
@[instance]
public theorem CFSG.pCore_normal : (pCore p G).Normal := by
  refine ⟨?_⟩
  intro n hn g
  have hdir := directedOn_normal_pGroups p G
  have hne := normalPSubgroups_nonempty p G
  rcases ((Subgroup.mem_sSup_of_directedOn hne hdir).mp hn) with ⟨K, hK, hnK⟩
  exact Subgroup.mem_sSup_of_mem hK (hK.1.conj_mem n hnK g)

/-- `p`-core of `G` is a `p`-group. -/
public theorem CFSG.pCore_isPGroup : IsPGroup p (pCore p G) := by
  intro g
  have hg := g.2
  dsimp [pCore] at hg
  have hdir := directedOn_normal_pGroups G (p := p)
  have hne : (normalPSubgroups p G : Set (Subgroup G)).Nonempty :=
    ⟨⊥, ⟨inferInstance, IsPGroup.of_bot⟩⟩
  rcases ((Subgroup.mem_sSup_of_directedOn hne hdir).mp hg) with ⟨K, hK, hgK⟩
  have hn := hK.2 ⟨g, hgK⟩
  rcases hn with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  apply Subtype.ext
  simpa using hn

/-- The `p`-core is preserved under group isomorphisms. -/
public theorem CFSG.pCore_map_iso {G G' : Type*} [Group G] [Group G'] (p : ℕ)
    (f : G ≃* G') : (pCore p G).map f.toMonoidHom = pCore p G' := by
  let S : Set (Subgroup G) := {K | K.Normal ∧ IsPGroup p K}
  let S' : Set (Subgroup G') := {K' | K'.Normal ∧ IsPGroup p K'}
  let F : Subgroup G ≃o Subgroup G' := MulEquiv.mapSubgroup f
  have h_image : F '' S = S' := by
    ext K'
    constructor
    · rintro ⟨K, ⟨hK_normal, hK_p⟩, h⟩
      have : F K = K.map f.toMonoidHom := rfl
      rw [this] at h
      subst h
      constructor
      · exact Subgroup.Normal.map hK_normal f.toMonoidHom f.surjective
      · exact IsPGroup.map hK_p f.toMonoidHom
    · intro ⟨hK'_normal, hK'_p⟩
      have h_symm_normal : (F.symm K').Normal := by
        dsimp [F]
        exact Subgroup.Normal.map hK'_normal f.symm.toMonoidHom f.symm.surjective
      have h_symm_p : IsPGroup p (F.symm K') := by
        dsimp [F]
        exact IsPGroup.map hK'_p f.symm.toMonoidHom
      refine ⟨F.symm K', ⟨h_symm_normal, h_symm_p⟩, ?_⟩
      simp [F, Subgroup.map_map]
  calc
    (pCore p G).map f.toMonoidHom = (sSup S).map f.toMonoidHom := rfl
    _ = F (sSup S) := rfl
    _ = ⨆ K ∈ S, F K := OrderIso.map_sSup F S
    _ = sSup (F '' S) := by simp [sSup_image]
    _ = sSup S' := by rw [h_image]
    _ = pCore p G' := rfl

/-- The `p`-core is characteristic. -/
public instance CFSG.pCore_characteristic : (pCore p G).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  simpa using (pCore_map_iso (G := G) (G' := G) (p := p) (f := φ))

variable [Fact p.Prime]

public theorem CFSG.pCore_isNilpotent [Finite G] : Group.IsNilpotent (↥(pCore p G)) :=
  pCore_isPGroup.isNilpotent

lemma CFSG.pCore_disjoint_of_ne (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hne : p ≠ q) :
    Disjoint (pCore p G) (pCore q G) :=
  IsPGroup.disjoint_of_ne p q hne (pCore p G) (pCore q G) pCore_isPGroup pCore_isPGroup

lemma CFSG.pCore_commute_of_ne (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hne : p ≠ q) :
    ∀ x ∈ pCore p G, ∀ y ∈ pCore q G, x * y = y * x := by
  intro x hx y hy
  have hdisj : Disjoint (pCore p G) (pCore q G) :=
    pCore_disjoint_of_ne p q hne
  have hmem_comm : ⁅x, y⁆ ∈ ⁅pCore p G, pCore q G⁆ :=
    Subgroup.commutator_mem_commutator hx hy
  have hle : ⁅pCore p G, pCore q G⁆ ≤ pCore p G ⊓ pCore q G :=
    Subgroup.commutator_le_inf (H₁ := pCore p G) (H₂ := pCore q G)
  have hmem_inf : ⁅x, y⁆ ∈ pCore p G ⊓ pCore q G := hle hmem_comm
  have hinf_eq : (pCore p G ⊓ pCore q G : Subgroup G) = ⊥ := hdisj.eq_bot
  rw [hinf_eq] at hmem_inf
  have h1 : ⁅x, y⁆ = (1 : G) := by simpa using hmem_inf
  rwa [commutatorElement_eq_one_iff_mul_comm] at h1

-- Lemma from sylow_normal.lean

lemma Sylow.isPGroup_map {N : Subgroup G} (p : ℕ) (P : Sylow p (↥N)) :
    IsPGroup p (P.map N.subtype) := P.isPGroup'.map N.subtype

variable [Finite G]

public theorem Group.IsNilpotent.sylow_normal (h : Group.IsNilpotent G)
    (p : ℕ) [Fact p.Prime] (P : Sylow p G) : (P : Subgroup G).Normal :=
  have h_nc : NormalizerCondition G := @Group.normalizerCondition_of_isNilpotent G _ h
  have h_coatom : ∀ H : Subgroup G, IsCoatom H → H.Normal :=
    fun H hH => Subgroup.NormalizerCondition.normal_of_coatom H h_nc hH
  Sylow.normal_of_all_max_subgroups_normal h_coatom P

-- Sylow lemmas for normal nilpotent subgroups
lemma Sylow.normal_of_nilpotent_normal {N : Subgroup G} (hN : N.Normal) (hnil : Group.IsNilpotent (↥N))
    (p : ℕ) [Fact p.Prime] (P : Sylow p (↥N)) : (P.map N.subtype).Normal :=
  have hP_normal : (P : Subgroup (↥N)).Normal :=
    Group.IsNilpotent.sylow_normal hnil p P
  have : P.Characteristic :=
    Sylow.characteristic_of_normal P hP_normal
  inferInstance

public lemma Sylow.map_le_pCore {N : Subgroup G} (hN : N.Normal) (hnil : Group.IsNilpotent (↥N))
    (p : ℕ) [Fact p.Prime] (P : Sylow p (↥N)) :
    P.map N.subtype ≤ pCore p G :=
  have hmem : P.map N.subtype ∈ { K : Subgroup G | K.Normal ∧ IsPGroup p K } :=
    ⟨Sylow.normal_of_nilpotent_normal hN hnil p P, Sylow.isPGroup_map p P⟩
  le_sSup hmem

lemma CFSG.primeFactors_subset (N : Subgroup G) : (Nat.card (↥N)).primeFactors ⊆ (Nat.card G).primeFactors := fun p hp =>
  have hdvd : Nat.card (↥N) ∣ Nat.card G := Subgroup.card_subgroup_dvd_card N
  have hpdvd : p ∣ Nat.card G := (Nat.dvd_of_mem_primeFactors hp).trans hdvd
  Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp, hpdvd, Nat.card_pos.ne'⟩

public theorem CFSG.isNilpotent_iSup_pCore : Group.IsNilpotent (↥(⨆ (p : (Nat.card G).primeFactors.attach), pCore p.1.1 G)) := by
  haveI : Fintype G := Fintype.ofFinite G
  let π := (Nat.card G).primeFactors.attach
  let H : π → Subgroup G := fun p => pCore p.1.1 G
  have hcomm : Pairwise fun (i j : π) => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y := by
    intro i j hij
    have hij' : i.1.1 ≠ j.1.1 := by
      intro h
      apply hij
      exact Subtype.ext (Subtype.ext h)
    intro x y hx hy
    exact pCore_commute_of_ne i.1.1 j.1.1 hij' x hx y hy
  haveI : Fintype π := inferInstance
  haveI : ∀ i, Fintype (↥(H i)) := by
    intro i
    haveI : DecidablePred (· ∈ H i) := Classical.decPred _
    exact Subtype.fintype (fun x : G => x ∈ H i)
  have hcoprime : Pairwise fun (i j : π) => Nat.Coprime (Fintype.card (H i)) (Fintype.card (H j)) := by
    intro i j hij
    have hij' : i.1.1 ≠ j.1.1 := by
      intro h
      apply hij
      exact Subtype.ext (Subtype.ext h)
    haveI : Finite ↥(H i) := inferInstance
    haveI : Finite ↥(H j) := inferInstance
    have hcard := IsPGroup.coprime_card_of_ne i.1.1 j.1.1 hij' (H i) (H j) pCore_isPGroup pCore_isPGroup
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
    exact hcard
  have hind : iSupIndep H :=
    Subgroup.independent_of_coprime_order hcomm hcoprime
  let ϕ := Subgroup.noncommPiCoprod (hcomm := hcomm)
  have h_range : ϕ.range = ⨆ i, H i := Subgroup.noncommPiCoprod_range
  have hinj : Function.Injective ϕ :=
    Subgroup.injective_noncommPiCoprod_of_iSupIndep (hind := hind)
  let hcod : ∀ a, ϕ a ∈ ⨆ i, H i := by
    intro a
    rw [← h_range]
    exact ⟨a, rfl⟩
  let ϕ' : (∀ i : π, H i) →* ↥(⨆ i, H i) := ϕ.codRestrict (⨆ i, H i) hcod
  have hinj' : Function.Injective ϕ' := (ϕ.injective_codRestrict (⨆ i, H i) hcod).mpr hinj
  have h_surj' : Function.Surjective ϕ' := by
    intro x
    have hx : x.1 ∈ ϕ.range := by
      rw [h_range]
      exact x.2
    rcases hx with ⟨a, ha⟩
    refine ⟨a, Subtype.ext ha⟩
  let e : (∀ i : π, H i) ≃* ↥(⨆ i, H i) :=
    MulEquiv.ofBijective ϕ' ⟨hinj', h_surj'⟩
  haveI : Group.IsNilpotent (∀ i : π, H i) := by
    have : ∀ i, Group.IsNilpotent (H i) := by
      intro i
      exact pCore_isPGroup.isNilpotent
    infer_instance
  exact Group.nilpotent_of_mulEquiv e

/-- A finite nilpotent group is the supremum of its Sylow subgroups. -/
public theorem Sylow.iSup_sylow_eq_top :
    ⨆ p ∈ (Nat.card G).primeFactors, ((default : Sylow p G) : Subgroup G) = ⊤ := by
  set S := ⨆ p ∈ (Nat.card G).primeFactors, ((default : Sylow p G) : Subgroup G)
  rw[← Subgroup.card_eq_iff_eq_top]
  apply Nat.eq_of_factorization_eq Nat.card_pos.ne' Nat.card_pos.ne'
  intro p
  by_cases hp : p.Prime
  · by_cases hd : p ∈ (Nat.card G).primeFactors
    · letI := Fact.mk hp
      let P := (default : Sylow p G)
      have hl : P ≤ S := by
        refine le_iSup_of_le p (le_iSup_of_le hd ?_)
        simp_all only [P, le_refl]
      refine le_antisymm ?_ ?_
      · suffices (Nat.card S).factorization ≤ (Nat.card G).factorization by exact String.Pos.Raw.mk_le_mk.mp (this p)
        rw [Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne']
        exact Subgroup.card_subgroup_dvd_card S
      rw[← pow_le_pow_iff_right₀ (Nat.Prime.one_lt hp), ← card_eq_multiplicity P]
      have hc : Nat.card P = Nat.card (P.subgroupOf S) := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hl).symm
      have hpP : IsPGroup p (P.subgroupOf S) := by
        refine IsPGroup.of_card (n := (Nat.card G).factorization p) ?_;
        rw[← hc, ← card_eq_multiplicity P]
      rcases IsPGroup.exists_le_sylow hpP with ⟨P', hP'⟩
      rw[← card_eq_multiplicity P', hc]
      exact Subgroup.card_le_of_le hP'
    · have hnH : ¬p ∣ Nat.card G := by
        have : Nat.card G ≠ 0 := Nat.card_pos.ne'
        rw[Nat.mem_primeFactors_of_ne_zero this] at hd
        simp_all only [true_and, not_false_eq_true]
      have hnS : ¬p ∣ Nat.card S := (flip dvd_trans (Subgroup.card_subgroup_dvd_card S)).mt hnH
      rw[Nat.factorization_eq_zero_of_not_dvd hnH, Nat.factorization_eq_zero_of_not_dvd hnS]
  · simp_all only [not_false_eq_true, Nat.factorization_eq_zero_of_not_prime]

lemma Sylow.iSup_sylow_map_eq_top {N : Subgroup G} :
    (⨆ p ∈ (Nat.card (↥N)).primeFactors, ((default : Sylow p (↥N)) : Subgroup (↥N))).map N.subtype = N := by
  rw[Sylow.iSup_sylow_eq_top (G := N), ← (MonoidHom.range_eq_map N.subtype), Subgroup.range_subtype]

public theorem CFSG.normal_nilpotent_le_sup_pCore {N : Subgroup G} (hN : N.Normal) (hnil : Group.IsNilpotent (↥N)) :
    N ≤ ⨆ (p : (Nat.card G).primeFactors.attach), pCore p.1 G := by
  let π_N := (Nat.card (↥N)).primeFactors
  have hsup := (Sylow.iSup_sylow_map_eq_top (N := N)).symm
  have hsup_eq : N = ⨆ p ∈ π_N, ((default : Sylow p (↥N)).map N.subtype) := by
    calc
      N = ((⨆ p ∈ π_N, ((default : Sylow p (↥N)) : Subgroup (↥N))).map N.subtype) := hsup
      _ = (⨆ p ∈ π_N, ((default : Sylow p (↥N)).map N.subtype)) := by simp [Subgroup.map_iSup]
  rw [hsup_eq]
  refine iSup₂_le fun p hp => ?_
  have hpG : p ∈ (Nat.card G).primeFactors := primeFactors_subset N hp
  haveI : Fact (Nat.Prime p) := ⟨Nat.prime_of_mem_primeFactors hp⟩
  have hle1 : ((default : Sylow p (↥N)).map N.subtype) ≤ pCore p G :=
    Sylow.map_le_pCore hN hnil p (default : Sylow p (↥N))
  -- Show pCore p G ≤ ⨆ (p : (Nat.card G).primeFactors.attach), pCore p G.1
  let q : (Nat.card G).primeFactors.attach := ⟨⟨p, hpG⟩, Finset.mem_attach _ _⟩
  have hle2 : pCore p G ≤ ⨆ (r : (Nat.card G).primeFactors.attach), pCore r.1.1 G := by
    -- `q.1.1 = p` definitionally, so `pCore q G.1.1` is `pCore p G`.
    exact le_iSup (fun r : (Nat.card G).primeFactors.attach => pCore r.1.1 G) q
  exact hle1.trans hle2

end pCore_properties
