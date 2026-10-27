module

public import CFSG.RankThree.PartTwo.Sec11.Item116R1Alg
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.GroupTheory.BaerSuzuki.Helpers
public import CFSG.RankThree.LocalRank.ThetaCoreQuotients
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import Certificates.Data.ExceptionalSL3

public section

open Subgroup

theorem isCyclic_sylow_of_surjective_of_injOn {K W Z : Type*} [Group K] [Group W] [Group Z]
    [Finite K] [Finite W] [Finite Z] (g : K →* W)
    (hg : ∀ k : K, IsPGroup 3 (Subgroup.zpowers k) → g k = 1 → k = 1)
    (hW : ∀ S : Sylow 3 W, IsCyclic S) (f : K →* Z) (hf : Function.Surjective f) :
    ∀ S : Sylow 3 Z, IsCyclic S := by
  intro S
  obtain ⟨T, hT⟩ := Sylow.mapSurjective_surjective hf 3 S
  have hHS : (T : Subgroup K).map f = (S : Subgroup Z) :=
    congrArg (fun P : Sylow 3 Z => (P : Subgroup Z)) hT
  set H : Subgroup K := (T : Subgroup K) with hH
  have hHp : IsPGroup 3 H := T.isPGroup'
  have hinj : Function.Injective (g.comp H.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hP : IsPGroup 3 (Subgroup.zpowers (x : K)) :=
      hHp.to_le (Subgroup.zpowers_le.mpr x.2)
    exact Subtype.ext (hg (x : K) hP hx)
  obtain ⟨Q, hQ⟩ := (hHp.map g).exists_le_sylow
  haveI : IsCyclic (Q : Subgroup W) := hW Q
  have hφQ : ∀ x : H, (g.comp H.subtype) x ∈ (Q : Subgroup W) := fun x =>
    hQ (Subgroup.mem_map_of_mem g x.2)
  have hHc : IsCyclic H := by
    refine isCyclic_of_injective ((g.comp H.subtype).codRestrict (Q : Subgroup W) hφQ) ?_
    intro a b h
    apply hinj
    exact congrArg Subtype.val h
  have hψ : ∀ x : H, (f.comp H.subtype) x ∈ (S : Subgroup Z) := fun x => by
    rw [← hHS]
    exact Subgroup.mem_map_of_mem f x.2
  have hSc : IsCyclic (S : Subgroup Z) := by
    refine isCyclic_of_surjective ((f.comp H.subtype).codRestrict (S : Subgroup Z) hψ) ?_
    intro y
    have hy : (y : Z) ∈ H.map f := by
      rw [hHS]
      exact y.2
    obtain ⟨x, hx, hfx⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hfx⟩
  exact hSc

theorem injOn_three_of_card_coprime {L : Type*} [Group L] [Finite L] (N : Subgroup L) [N.Normal]
    (hN : ¬ 3 ∣ Nat.card N) {K : Type*} [Group K] (ι : K →* L) (hι : Function.Injective ι) :
    ∀ k : K, IsPGroup 3 (Subgroup.zpowers k) → (QuotientGroup.mk' N).comp ι k = 1 → k = 1 := by
  intro k hk hmk
  have hmem : ι k ∈ N := by
    have h' : ((ι k : L) : L ⧸ N) = 1 := hmk
    exact (QuotientGroup.eq_one_iff (N := N) (ι k)).mp h'
  obtain ⟨n, hn⟩ := hk ⟨k, Subgroup.mem_zpowers k⟩
  have hkn : k ^ 3 ^ n = 1 := by
    simpa using congrArg Subtype.val hn
  have hιn : (ι k) ^ 3 ^ n = 1 := by
    rw [← map_pow, hkn, map_one]
  have h1 : orderOf (ι k) ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one hιn
  have h2 : orderOf (ι k) ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hmem
  have hcop : Nat.Coprime (3 ^ n) (Nat.card N) :=
    Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN)
  have h3 : orderOf (ι k) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have h4 : ι k = 1 := orderOf_eq_one_iff.mp h3
  exact hι (h4.trans (map_one ι).symm)

open CFSG CFSG.RankThree.LocalRank Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

theorem aq_centralizer_zpowers_eq {G : Type*} [Group G] (g : G) :
    Subgroup.centralizer ((Subgroup.zpowers g : Subgroup G) : Set G) =
      Subgroup.centralizer ({g} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem aschbacherSolvableCore_quotient_eq_bot (H : Type*) [Group H] [Finite H] :
    aschbacherSolvableCore 3 (H ⧸ aschbacherSolvableCore 3 H) = ⊥ := by
  have hθ := solvable_prime_complement_core_characterization (H := H) Nat.prime_three
  exact (solvable_prime_complement_core_quotient_centralizers Nat.prime_three
    (aschbacherSolvableCore 3 H) hθ.1 hθ.2.2.1).2.2.1

theorem map_pCore_two_centralizer_le {H : Type*} [Group H] [Finite H] (N : Subgroup H) [N.Normal]
    (hN : ¬ 3 ∣ Nat.card N) {y : H} (hy : y ^ 3 = 1) :
    (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({y} : Set H))).map (QuotientGroup.mk' N) ≤
      inSubgroup (CFSG.pCore 2)
        (Subgroup.centralizer ({QuotientGroup.mk' N y} : Set (H ⧸ N))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : Nat.Coprime 3 (Nat.card N) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN
  have hZ3 : IsPGroup 3 (Subgroup.zpowers y) := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hy) with h1 | h1
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h1, pow_one])
  haveI : Fact (IsPGroup 3 (Subgroup.zpowers y)) := ⟨hZ3⟩
  have hkey : Subgroup.centralizer
      (((Subgroup.zpowers y).map (QuotientGroup.mk' N) : Subgroup (H ⧸ N)) : Set (H ⧸ N)) =
      (Subgroup.centralizer ((Subgroup.zpowers y : Subgroup H) : Set H)).map
        (QuotientGroup.mk' N) :=
    CFSG.centralizer_map_quotient_eq_map_centralizer 3 (Subgroup.zpowers y) N inferInstance hcop
  have hC' : Subgroup.centralizer ({QuotientGroup.mk' N y} : Set (H ⧸ N)) =
      (Subgroup.centralizer ({y} : Set H)).map (QuotientGroup.mk' N) := by
    rw [← aq_centralizer_zpowers_eq (QuotientGroup.mk' N y), ← MonoidHom.map_zpowers, hkey,
      aq_centralizer_zpowers_eq]
  rw [hC']
  set Cy : Subgroup H := Subgroup.centralizer ({y} : Set H) with hCy
  have hψ : ∀ x : ↥Cy, ((QuotientGroup.mk' N).comp Cy.subtype) x ∈ Cy.map (QuotientGroup.mk' N) :=
    fun x => Subgroup.mem_map_of_mem (QuotientGroup.mk' N) x.2
  let ψ : ↥Cy →* ↥(Cy.map (QuotientGroup.mk' N)) :=
    ((QuotientGroup.mk' N).comp Cy.subtype).codRestrict _ hψ
  have hψs : Function.Surjective ψ := by
    rintro ⟨c, hc⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hc
    exact ⟨⟨x, hx⟩, rfl⟩
  have hQn : ((CFSG.pCore 2 ↥Cy).map ψ).Normal :=
    (BaerSuzuki.Helpers.pCore_normal (G := ↥Cy) 2).map ψ hψs
  have hQp : IsPGroup 2 ((CFSG.pCore 2 ↥Cy).map ψ) :=
    (BaerSuzuki.Helpers.pCore_isPGroup (G := ↥Cy) 2).map ψ
  have hle : (CFSG.pCore 2 ↥Cy).map ψ ≤ CFSG.pCore 2 ↥(Cy.map (QuotientGroup.mk' N)) :=
    BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hQn hQp
  have hcomp : (QuotientGroup.mk' N).comp Cy.subtype =
      (Cy.map (QuotientGroup.mk' N)).subtype.comp ψ :=
    MonoidHom.ext fun _ => rfl
  calc (inSubgroup (CFSG.pCore 2) Cy).map (QuotientGroup.mk' N)
      = ((CFSG.pCore 2 ↥Cy).map ψ).map (Cy.map (QuotientGroup.mk' N)).subtype := by
        rw [inSubgroup, Subgroup.map_map, Subgroup.map_map, hcomp]
    _ ≤ (CFSG.pCore 2 ↥(Cy.map (QuotientGroup.mk' N))).map
          (Cy.map (QuotientGroup.mk' N)).subtype :=
        Subgroup.map_mono hle
    _ = inSubgroup (CFSG.pCore 2) (Cy.map (QuotientGroup.mk' N)) := rfl

end CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree.LocalRank Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

theorem aq4_center_layer_le_fitting {X : Type*} [Group X] [Finite X] :
    (Subgroup.center (CFSG.layer X)).map (CFSG.layer X).subtype ≤ CFSG.fittingSubgroup X := by
  haveI : (CFSG.layer X).Characteristic := CFSG.LocalCores.layer_characteristic
  have hnormal : ((Subgroup.center (CFSG.layer X)).map (CFSG.layer X).subtype).Normal :=
    inferInstance
  have hcomm : (Subgroup.center (CFSG.layer X)).map (CFSG.layer X).subtype ≤
      Subgroup.centralizer
        (((Subgroup.center (CFSG.layer X)).map (CFSG.layer X).subtype : Subgroup X) : Set X) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp (SetLike.mem_coe.mp hh)
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hw z)).symm
  haveI : IsMulCommutative ((Subgroup.center (CFSG.layer X)).map (CFSG.layer X).subtype) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mp hcomm
  exact le_sSup (s := {N : Subgroup X | N.Normal ∧ Group.IsNilpotent N}) ⟨hnormal, inferInstance⟩

theorem aq4_fitting_le_pCore_three {X : Type*} [Group X] [Finite X]
    (hθ : aschbacherSolvableCore 3 X = ⊥) : CFSG.fittingSubgroup X ≤ CFSG.pCore 3 X := by
  rw [CFSG.fitting_eq_sup_pCore X]
  refine iSup_le fun p => ?_
  have hp : (p.1.1).Prime := Nat.prime_of_mem_primeFactors p.1.2
  by_cases h3 : p.1.1 = 3
  · exact le_of_eq (congrArg (fun q => CFSG.pCore q X) h3)
  · have hle := (solvable_prime_complement_core_characterization (H := X) Nat.prime_three).2.2.2.2.2.2
      p.1.1 hp h3
    rw [hθ] at hle
    exact hle.trans bot_le

theorem center_eq_bot_of_component_of_cyclic_sylow {X : Type*} [Group X] [Finite X]
    (hθ : aschbacherSolvableCore 3 X = ⊥) {J : Subgroup X} (hJ : CFSG.IsComponent J)
    (hsyl : ∀ S : Sylow 3 J, IsCyclic S) : Subgroup.center J = ⊥ := by
  have hZ0 : (Subgroup.center J).map J.subtype ≤ CFSG.pCore 3 X :=
    (CFSG.LocalCores.center_component_le_center_layer hJ).trans
      ((aq4_center_layer_le_fitting (X := X)).trans (aq4_fitting_le_pCore_three hθ))
  have hZ3 : IsPGroup 3 (Subgroup.center J) := by
    intro g
    have hmem : (g.1 : X) ∈ CFSG.pCore 3 X :=
      hZ0 (Subgroup.mem_map.mpr ⟨g.1, g.2, rfl⟩)
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup : IsPGroup 3 (CFSG.pCore 3 X)) ⟨(g.1 : X), hmem⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  have hperf := Group.isPerfect_def.mp hJ.1.1
  exact central_threeGroup_eq_bot_of_perfect hperf hsyl (Subgroup.center J) le_rfl hZ3

end CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

variable {G : Type} [Group G] [Finite G]

abbrev CAt (a : G) : Type := ↥(Subgroup.centralizer ({a} : Set G))

abbrev QAt (a : G) : Type := CAt a ⧸ aschbacherSolvableCore 3 (CAt a)

theorem inSubgroup_pCore_map_of_injective {Hh : Type*} [Group Hh] {p : ℕ} (ι : Hh →* G)
    (hι : Function.Injective ι) (S : Subgroup Hh) :
    inSubgroup (CFSG.pCore p) (S.map ι) = (inSubgroup (CFSG.pCore p) S).map ι := by
  have hiso := CFSG.pCore_map_iso p (Subgroup.equivMapOfInjective S ι hι)
  unfold CFSG.inSubgroup
  rw [← hiso, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem inSubgroup_pCore_centralizer_inf (a : G) (y' : CAt a) :
    inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({a} : Set G) ⊓
      Subgroup.centralizer ({(y' : G)} : Set G)) =
    (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({y'} : Set (CAt a)))).map
      (Subgroup.centralizer ({a} : Set G)).subtype := by
  have hset : Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({(y' : G)} : Set G) =
      (Subgroup.centralizer ({y'} : Set (CAt a))).map
        (Subgroup.centralizer ({a} : Set G)).subtype := by
    ext g
    rw [Subgroup.mem_inf, Subgroup.mem_map]
    constructor
    · rintro ⟨ha, hy⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hy
      refine ⟨⟨g, ha⟩, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext hy
    · rintro ⟨x, hx, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hx
      refine ⟨x.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val hx
  rw [hset]
  exact inSubgroup_pCore_map_of_injective (Subgroup.centralizer ({a} : Set G)).subtype
    (Subgroup.subtype_injective _) _

theorem exists_pow_mul_mem_closure_pair {A : Subgroup G} {a c d : G}
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hAcl : Subgroup.closure ({c, d, a} : Set G) = A)
    {y : G} (hy : y ∈ A) : ∃ i : ℕ, ∃ b ∈ Subgroup.closure ({c, d} : Set G), y = a ^ i * b := by
  have hBA : ∀ b ∈ Subgroup.closure ({c, d} : Set G), b ∈ A := by
    intro b hb
    rw [← hAcl]
    refine Subgroup.closure_mono ?_ hb
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  have haA : a ∈ A := by
    rw [← hAcl]
    exact Subgroup.subset_closure (by simp)
  have hcomm : ∀ (j : ℕ) (b : G), b ∈ Subgroup.closure ({c, d} : Set G) →
      b * a ^ j = a ^ j * b := by
    intro j b hb
    have hc : Commute b a := (hAc a haA b (hBA b hb)).symm
    exact (hc.pow_right j).eq
  have hinvpow : ∀ i : ℕ, ∃ j : ℕ, (a ^ i)⁻¹ = a ^ j := by
    intro i
    refine ⟨i * (orderOf a - 1), ?_⟩
    have hn : 0 < orderOf a := orderOf_pos a
    have h1 : i + i * (orderOf a - 1) = i * orderOf a := by
      have h2 : 1 + (orderOf a - 1) = orderOf a := by omega
      calc i + i * (orderOf a - 1) = i * (1 + (orderOf a - 1)) := by rw [mul_add, mul_one]
        _ = i * orderOf a := by rw [h2]
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add, h1, pow_mul', pow_orderOf_eq_one, one_pow]
  rw [← hAcl] at hy
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h
    · rw [h]
      exact ⟨0, c, Subgroup.subset_closure (by simp), by simp⟩
    · rw [h]
      exact ⟨0, d, Subgroup.subset_closure (by simp), by simp⟩
    · rw [h]
      exact ⟨1, 1, (Subgroup.closure ({c, d} : Set G)).one_mem, by simp⟩
  | one => exact ⟨0, 1, (Subgroup.closure ({c, d} : Set G)).one_mem, by simp⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨i, b, hb, rfl⟩ := ihx
    obtain ⟨j, b', hb', rfl⟩ := ihy
    refine ⟨i + j, b * b', (Subgroup.closure ({c, d} : Set G)).mul_mem hb hb', ?_⟩
    calc a ^ i * b * (a ^ j * b') = a ^ i * (b * a ^ j) * b' := by simp only [mul_assoc]
      _ = a ^ i * (a ^ j * b) * b' := by rw [hcomm j b hb]
      _ = a ^ (i + j) * (b * b') := by rw [pow_add]; simp only [mul_assoc]
  | inv x _ ihx =>
    obtain ⟨i, b, hb, rfl⟩ := ihx
    obtain ⟨j, hj⟩ := hinvpow i
    refine ⟨j, b⁻¹, (Subgroup.closure ({c, d} : Set G)).inv_mem hb, ?_⟩
    rw [mul_inv_rev, hj, hcomm j b⁻¹ ((Subgroup.closure ({c, d} : Set G)).inv_mem hb)]

end CFSG.RankThree.PartTwo.Sec11
