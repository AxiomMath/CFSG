module

public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.Quasithin.EmptyFaithfulMultiple.Inspection15418Basic

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace Insp15418

theorem charTwo_of_no_component {G : Type*} [Group G] [Finite G] {X : Subgroup G}
    (hE : ∀ K : Subgroup ↥X, ¬ CFSG.IsComponent K) (hodd : oddCoreIn X = ⊥) : CharTwo X := by
  have hlayer : CFSG.layer ↥X = ⊥ := CFSG.LocalCores.layer_eq_bot_of_forall hE
  have hF : CFSG.generalizedFitting ↥X = CFSG.fittingSubgroup ↥X := by
    rw [CFSG.generalizedFitting, hlayer, sup_bot_eq]
  have hfit : CFSG.fittingSubgroup ↥X ≤ CFSG.pCore 2 ↥X ⊔ CFSG.oddCore ↥X := by
    rw [CFSG.fitting_eq_sup_pCore]
    refine iSup_le fun p => ?_
    by_cases hp : p.1.1 = 2
    · rw [hp]
      exact le_sup_left
    · refine le_trans ?_ le_sup_right
      have hq : Nat.Prime p.1.1 := Nat.prime_of_mem_primeFactors p.1.2
      have hqodd : Odd p.1.1 := hq.odd_of_ne_two hp
      refine le_sSup ⟨CFSG.pCore_normal, ?_⟩
      obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := p.1.1) (G := ↥X)).exists_card_eq
      rw [hn]
      exact hqodd.pow
  have hmap : (CFSG.pCore 2 ↥X ⊔ CFSG.oddCore ↥X).map X.subtype =
      pCoreOf 2 X ⊔ oddCoreIn X := by
    rw [Subgroup.map_sup, pCoreOf]
    rfl
  intro x hx
  have hx' : (⟨x, hx.1⟩ : ↥X) ∈ Subgroup.centralizer (CFSG.generalizedFitting ↥X : Set ↥X) := by
    rw [hF, Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : (w : G) ∈ pCoreOf 2 X ⊔ oddCoreIn X := by
      rw [← hmap]
      exact ⟨w, hfit hw, rfl⟩
    rw [hodd, sup_bot_eq] at hw'
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 _ hw')
  have := CFSG.centralizer_generalizedFitting_le ↥X hx'
  rw [hF] at this
  have hmem : x ∈ pCoreOf 2 X ⊔ oddCoreIn X := by
    rw [← hmap]
    exact ⟨_, hfit this, rfl⟩
  rw [hodd, sup_bot_eq] at hmem
  exact hmem

theorem exists_two_ne_one {G : Type*} [Group G] {Z : Subgroup G} (hcard : Nat.card Z = 4)
    (hsq : ∀ z ∈ Z, z ^ 2 = 1) : ∃ a ∈ Z, ∃ b ∈ Z, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  have : Finite Z := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hnt : Nontrivial Z := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    norm_num
  obtain ⟨⟨a, ha⟩, ha1⟩ := exists_ne (1 : Z)
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hza : Nat.card (Subgroup.zpowers a) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hsq a ha) ha1'
  have hlt : Subgroup.zpowers a < Z := by
    refine lt_of_le_of_ne ((Subgroup.zpowers_le).mpr ha) fun h => ?_
    rw [h, hcard] at hza
    norm_num at hza
  obtain ⟨b, hb, hbn⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨a, ha, b, hb, ha1', fun h => hbn (h ▸ Subgroup.one_mem _), fun h => ?_⟩
  exact hbn (h ▸ Subgroup.mem_zpowers a)

theorem eq_of_isCyclic_center {P : Type*} [Group P] [Fintype ↥(Subgroup.center P)]
    [IsCyclic ↥(Subgroup.center P)] {a b : P} (ha : ∀ x, a * x = x * a)
    (hb : ∀ x, b * x = x * b) (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    a = b := by
  classical
  have hle := IsCyclic.card_pow_eq_one_le (α := ↥(Subgroup.center P)) (n := 2) (by norm_num)
  set a' : ↥(Subgroup.center P) := ⟨a, Subgroup.mem_center_iff.mpr fun x => (ha x).symm⟩
  set b' : ↥(Subgroup.center P) := ⟨b, Subgroup.mem_center_iff.mpr fun x => (hb x).symm⟩
  by_contra hab
  have h3 : ({1, a', b'} : Finset ↥(Subgroup.center P)) ⊆
      Finset.univ.filter fun x => x ^ 2 = 1 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · exact one_pow 2
    · exact Subtype.ext ha2
    · exact Subtype.ext hb2
  have hcard := Finset.card_le_card h3
  have h1a : (1 : ↥(Subgroup.center P)) ≠ a' := fun h => ha1 (congrArg Subtype.val h).symm
  have h1b : (1 : ↥(Subgroup.center P)) ≠ b' := fun h => hb1 (congrArg Subtype.val h).symm
  have hab' : a' ≠ b' := fun h => hab (congrArg Subtype.val h)
  rw [Finset.card_insert_of_notMem (by simp [h1a, h1b]), Finset.card_pair hab'] at hcard
  omega

end Insp15418

namespace InspectionData15418

variable {G : Type} [Group G] [Finite G] {I G₁ G₂ S T Z : Subgroup G}
  (d : InspectionData15418 I G₁ G₂ S T Z)
include d

theorem exists_isComponent (hc : ¬ CharTwo I) : ∃ K : Subgroup ↥I, CFSG.IsComponent K := by
  by_contra h
  push Not at h
  exact hc (Insp15418.charTwo_of_no_component h d.oddCoreIn_eq_bot)

omit [Finite G] d in
theorem isComponentIn_map {K : Subgroup ↥I} (hK : CFSG.IsComponent K) :
    IsComponentIn (K.map I.subtype) I := by
  refine ⟨Subgroup.map_subtype_le K, ?_⟩
  have : (K.map I.subtype).subgroupOf I = K :=
    Subgroup.comap_map_eq_self_of_injective Subtype.val_injective K
  rw [this]
  exact hK

theorem not_forall_commute {K : Subgroup ↥I} (hK : CFSG.IsComponent K) {z : G} (hz : z ∈ Z)
    (hz1 : z ≠ 1) : ¬ ∀ k ∈ K, (k : G) * z = z * k := by
  intro hcomm
  have h := d.component _ (isComponentIn_map hK) z hz hz1
  have hbot : ⁅K.map I.subtype, Subgroup.zpowers z⁆ = ⊥ := by
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (Subgroup.le_centralizer_iff.mpr ((Subgroup.zpowers_le).mpr ?_))
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, hk, rfl⟩
    exact hcomm k hk
  rw [hbot] at h
  have : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
  obtain ⟨k, hk1⟩ := exists_ne (1 : K)
  apply hk1
  have hk : (k : G) ∈ K.map I.subtype := ⟨k, k.2, rfl⟩
  rw [← h, Subgroup.mem_bot] at hk
  exact Subtype.ext (Subtype.ext hk)

theorem commutator_pPrimeCore_eq_bot {K : Subgroup ↥I} (hK : CFSG.IsComponent K) :
    ⁅K, CFSG.pPrimeCore 3 ↥I⁆ = ⊥ :=
  (CFSG.LocalCores.component_solvable_centralizer (F6.isSolvable_pPrimeCore d.triple.subgroupOf)
    (inferInstance : (CFSG.pPrimeCore 3 ↥I).Normal).isSubnormal).1 K hK

theorem eq_one_of_mem_pPrimeCore {K : Subgroup ↥I} (hK : CFSG.IsComponent K) {z : ↥I}
    (hz : (z : G) ∈ Z) (hzO : z ∈ CFSG.pPrimeCore 3 ↥I) : z = 1 := by
  by_contra hz1
  refine d.not_forall_commute hK hz (fun h => hz1 (Subtype.ext h)) fun k hk => ?_
  have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.mp (d.commutator_pPrimeCore_eq_bot hK) hk
  exact (congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hc z hzO)).symm

theorem eq_of_mk_eq {K : Subgroup ↥I} (hK : CFSG.IsComponent K) {a b : ↥I} (ha : (a : G) ∈ Z)
    (hb : (b : G) ∈ Z)
    (h : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I) a = QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I) b) :
    a = b := by
  have h1 : a⁻¹ * b ∈ CFSG.pPrimeCore 3 ↥I := by
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I) (a⁻¹ * b) = 1
    rw [map_mul, map_inv, h, inv_mul_cancel]
  have h2 : ((a⁻¹ * b : ↥I) : G) ∈ Z := by
    simpa using Z.mul_mem (Z.inv_mem ha) hb
  have := d.eq_one_of_mem_pPrimeCore hK h2 h1
  rw [inv_mul_eq_one] at this
  exact this

theorem exists_central_involutions (hc : ¬ CharTwo I) :
    ∃ a ∈ (S.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)),
      ∃ b ∈ (S.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)),
      a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a ^ 2 = 1 ∧ b ^ 2 = 1 ∧
      (∀ x ∈ (S.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)), a * x = x * a) ∧
      (∀ x ∈ (S.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)), b * x = x * b) := by
  obtain ⟨K, hK⟩ := d.exists_isComponent hc
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I) with hπ
  obtain ⟨a, ha, b, hb, ha1, hb1, hab⟩ := Insp15418.exists_two_ne_one d.card d.sq_eq_one
  have hZI : ∀ {z}, z ∈ Z → z ∈ I := fun hz => d.S_le (d.le hz)
  set a' : ↥I := ⟨a, hZI ha⟩
  set b' : ↥I := ⟨b, hZI hb⟩
  have hmem : ∀ {z} (hz : z ∈ Z), π ⟨z, hZI hz⟩ ∈ (S.subgroupOf I).map π := fun {z} hz =>
    ⟨⟨z, hZI hz⟩, d.le hz, rfl⟩
  have hne1 : ∀ {z} (hz : z ∈ Z), z ≠ 1 → π ⟨z, hZI hz⟩ ≠ 1 := by
    intro z hz hz1 h
    have := d.eq_of_mk_eq hK (a := ⟨z, hZI hz⟩) (b := 1) hz Z.one_mem (by rw [h, map_one])
    exact hz1 (congrArg Subtype.val this)
  have hsq : ∀ {z} (hz : z ∈ Z), π ⟨z, hZI hz⟩ ^ 2 = 1 := by
    intro z hz
    rw [← map_pow]
    have : (⟨z, hZI hz⟩ : ↥I) ^ 2 = 1 := Subtype.ext (d.sq_eq_one z hz)
    rw [this, map_one]
  have hcent : ∀ {z} (hz : z ∈ Z), ∀ x ∈ (S.subgroupOf I).map π,
      π ⟨z, hZI hz⟩ * x = x * π ⟨z, hZI hz⟩ := by
    rintro z hz _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hs' : (s : G) ∈ I ⊓ Subgroup.centralizer (Z : Set G) := d.centralizer_eq ▸ hs
    exact Subgroup.mem_centralizer_iff.mp hs'.2 z hz
  refine ⟨π a', hmem ha, π b', hmem hb, hne1 ha ha1, hne1 hb hb1, fun h => hab ?_, hsq ha,
    hsq hb, hcent ha, hcent hb⟩
  exact congrArg Subtype.val (d.eq_of_mk_eq hK ha hb h)

theorem false_of_mulEquiv (hc : ¬ CharTwo I) {P : Type*} [Group P]
    (e : ↥((G₁.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) ⊓
      (G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))) ≃* P)
    (hP : ∀ a b : P, (∀ x, a * x = x * a) → (∀ x, b * x = x * b) → a ^ 2 = 1 → b ^ 2 = 1 →
      a ≠ 1 → b ≠ 1 → a = b) : False := by
  obtain ⟨a, ha, b, hb, ha1, hb1, hab, ha2, hb2, hac, hbc⟩ := d.exists_central_involutions hc
  rw [← d.isGoldschmidtAmalgam.1] at ha hb hac hbc
  have hcent : ∀ {y} (hy : y ∈ (G₁.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) ⊓
      (G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))),
      (∀ x ∈ (G₁.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) ⊓
        (G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)), y * x = x * y) →
      ∀ u, e ⟨y, hy⟩ * u = u * e ⟨y, hy⟩ := by
    intro y hy hyc u
    obtain ⟨x, rfl⟩ := e.surjective u
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (hyc x x.2))
  have hsq : ∀ {y} (hy : y ∈ (G₁.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) ⊓
      (G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))), y ^ 2 = 1 →
      e ⟨y, hy⟩ ^ 2 = 1 := by
    intro y hy hy2
    rw [← map_pow]
    have : (⟨y, hy⟩ : ↥((G₁.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) ⊓
        (G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)))) ^ 2 = 1 :=
      Subtype.ext hy2
    rw [this, map_one]
  have hne : ∀ {y} (hy : y ∈ (G₁.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) ⊓
      (G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))), y ≠ 1 →
      e ⟨y, hy⟩ ≠ 1 := by
    intro y hy hy1 h
    rw [map_eq_one_iff e e.injective] at h
    exact hy1 (congrArg Subtype.val h)
  have := hP _ _ (hcent ha hac) (hcent hb hbc) (hsq ha ha2) (hsq hb hb2) (hne ha ha1) (hne hb hb1)
  exact hab (congrArg Subtype.val (e.injective this))

theorem false_of_isCyclic_center (hc : ¬ CharTwo I)
    (h : IsCyclic ↥(Subgroup.center ↥((G₁.subgroupOf I).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) ⊓
        (G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))))) : False := by
  classical
  refine d.false_of_mulEquiv hc (MulEquiv.refl _) fun a b ha hb ha2 hb2 ha1 hb1 => ?_
  have : Fintype ↥(Subgroup.center ↥((G₁.subgroupOf I).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) ⊓
        (G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)))) :=
    Fintype.ofFinite _
  exact Insp15418.eq_of_isCyclic_center ha hb ha2 hb2 ha1 hb1

end InspectionData15418

end CFSG.Quasithin.EmptyFaithfulMultiple
