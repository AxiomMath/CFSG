module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Nilpotent
public import CFSG.Adapters.GeneralizedFitting

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

section Generic

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem s15_Three_top_of_fstar {B : Subgroup Γ} (hF : Fstar B = B) :
    CFSG.fittingSubgroup ↥B ⊔ CFSG.layer ↥B = ⊤ := by
  have hmap : (genFittingFStar ↥B).map B.subtype = B := hF
  have htop : genFittingFStar ↥B = ⊤ := by
    apply Subgroup.map_injective (f := B.subtype) B.subtype_injective
    rw [hmap, Subgroup.map_top, Subgroup.range_subtype]
  rw [CFSG.Adapters.genFittingFStar_eq_foundations ↥B,
    CFSG.generalizedFitting.eq_sup] at htop
  exact htop

theorem s15_Three_fitting_odd {B : Subgroup Γ}
    (hO : ∀ P : Subgroup ↥B, P.Normal → IsPGroup 2 ↥P → P = ⊥) :
    Odd (Nat.card ↥(CFSG.fittingSubgroup ↥B)) := by
  let F := CFSG.fittingSubgroup ↥B
  have hQp : IsPGroup 2 ↥((CFSG.pCore 2 ↥F).map F.subtype) :=
    IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := ↥F)) F.subtype
  have hQn : ((CFSG.pCore 2 ↥F).map F.subtype).Normal := inferInstance
  have hQbot : (CFSG.pCore 2 ↥F).map F.subtype = ⊥ := hO _ hQn hQp
  have hpCore_bot : CFSG.pCore 2 ↥F = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (CFSG.pCore 2 ↥F) F.subtype_injective).mp hQbot
  have htop : CFSG.pPrimeCore 2 ↥F = ⊤ := by
    have h := CFSG.nilpotent_top_le_pCore_sup_pPrimeCore (Q := ↥F) (p := 2)
      (hQnil := inferInstance)
    rw [hpCore_bot, bot_sup_eq] at h
    exact top_le_iff.mp h
  have hcop : Nat.Coprime 2 (Nat.card ↥(CFSG.pPrimeCore 2 ↥F)) :=
    CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥F)
  rw [htop, Subgroup.card_top] at hcop
  exact Nat.coprime_two_left.mp hcop

theorem s15_Three_odd_le_of_two_index {X : Type} [Group X] [Finite X] {F N : Subgroup X}
    (hF : Odd (Nat.card ↥F)) (hN : N.Normal) (hidx : ∃ n : ℕ, N.index = 2 ^ n) : F ≤ N := by
  intro x hx
  obtain ⟨n, hn⟩ := hidx
  have hcard : Nat.card (X ⧸ N) = 2 ^ n := hn
  have hodd : Odd (orderOf x) := hF.of_dvd_nat (Subgroup.orderOf_dvd_natCard F hx)
  have hdvd2 : orderOf ((QuotientGroup.mk' N) x) ∣ 2 ^ n := by
    have h := orderOf_dvd_natCard ((QuotientGroup.mk' N) x)
    rwa [hcard] at h
  have hcop : Nat.Coprime (2 ^ n) (orderOf x) := (hodd.coprime_two_left).pow_left n
  have hdvd1 : orderOf ((QuotientGroup.mk' N) x) ∣ 1 := by
    have hg : orderOf ((QuotientGroup.mk' N) x) ∣ Nat.gcd (2 ^ n) (orderOf x) :=
      Nat.dvd_gcd hdvd2 (orderOf_map_dvd (QuotientGroup.mk' N) x)
    rwa [hcop.gcd_eq_one] at hg
  have hone : orderOf ((QuotientGroup.mk' N) x) = 1 := Nat.dvd_one.mp hdvd1
  rw [← QuotientGroup.eq_one_iff x]
  exact orderOf_eq_one_iff.mp hone

theorem s15_Three_perfect_le_of_two_index {X : Type} [Group X] [Finite X] {C N : Subgroup X}
    (hC : Group.IsPerfect ↥C) (hN : N.Normal) (hidx : ∃ n : ℕ, N.index = 2 ^ n) : C ≤ N := by
  obtain ⟨n, hn⟩ := hidx
  have hcard : Nat.card (X ⧸ N) = 2 ^ n := hn
  have hP : IsPGroup 2 (X ⧸ N) := IsPGroup.of_card (p := 2) hcard
  haveI : Group.IsNilpotent (X ⧸ N) := hP.isNilpotent
  have hbot : C.map (QuotientGroup.mk' N) = ⊥ := by
    by_contra hne
    haveI : Nontrivial ↥(C.map (QuotientGroup.mk' N)) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    haveI : Group.IsPerfect ↥C := hC
    have hperf : Group.IsPerfect ↥(C.map (QuotientGroup.mk' N)) :=
      Group.IsPerfect.map (QuotientGroup.mk' N)
    have hsol : Group.IsSolvable ↥(C.map (QuotientGroup.mk' N)) :=
      Group.isSolvable_of_isSolvable_injective
        (C.map (QuotientGroup.mk' N)).subtype_injective
    exact (Group.IsPerfect.not_isSolvable _) hsol
  rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot

theorem s15_Three_layer_le_of_two_index {X : Type} [Group X] [Finite X] {N : Subgroup X}
    (hN : N.Normal) (hidx : ∃ n : ℕ, N.index = 2 ^ n) : CFSG.layer X ≤ N := by
  rw [CFSG.layer.eq_sSup]
  refine sSup_le fun C hC => ?_
  exact s15_Three_perfect_le_of_two_index hC.1.1 hN hidx

theorem s15_Three_mem_layer_of_odd {X : Type} [Group X] [Finite X] {x : X} (hx : x * x = 1)
    (hF : CFSG.fittingSubgroup X ⊔ CFSG.layer X = ⊤)
    (hodd : Odd (Nat.card ↥(CFSG.fittingSubgroup X))) : x ∈ CFSG.layer X := by
  let F := CFSG.fittingSubgroup X
  let E := CFSG.layer X
  haveI hEchar : E.Characteristic := CFSG.LocalCores.layer_characteristic (G := X)
  have hxFE : x ∈ F ⊔ E := by
    change x ∈ CFSG.fittingSubgroup X ⊔ CFSG.layer X
    rw [hF]
    exact Subgroup.mem_top x
  have hxmul : x ∈ (F : Set X) * (E : Set X) := by
    rw [← Subgroup.mul_normal F E]
    exact hxFE
  obtain ⟨f, hf, e, he, hfe⟩ := hxmul
  have hfE : f ∈ E := by
    rw [← QuotientGroup.ker_mk' E, MonoidHom.mem_ker]
    have hfeq : QuotientGroup.mk' E f = QuotientGroup.mk' E x := by
      have he1 : QuotientGroup.mk' E e = 1 := (QuotientGroup.eq_one_iff e).2 he
      rw [← hfe, map_mul, he1, mul_one]
    have hdvd2 : orderOf (QuotientGroup.mk' E f) ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one, hfeq, pow_two, ← map_mul, hx, map_one]
    have hdvdf : orderOf f ∣ Nat.card ↥F := Subgroup.orderOf_dvd_natCard F hf
    have hoddg : Odd (orderOf (QuotientGroup.mk' E f)) :=
      (hodd.of_dvd_nat hdvdf).of_dvd_nat (orderOf_map_dvd (QuotientGroup.mk' E) f)
    have hcg : Nat.Coprime (orderOf (QuotientGroup.mk' E f)) 2 := hoddg.coprime_two_right
    have hone : orderOf (QuotientGroup.mk' E f) = 1 := by
      have hdvd1 : orderOf (QuotientGroup.mk' E f) ∣ 1 := by
        have : orderOf (QuotientGroup.mk' E f) ∣ 1 * 2 := by simpa using hdvd2
        exact (Nat.Coprime.dvd_mul_right hcg).mp this
      exact Nat.dvd_one.mp hdvd1
    exact orderOf_eq_one_iff.mp hone
  rw [← hfe]
  exact mul_mem hfE he

theorem s15_Three_no_two_quotient {B : Subgroup Γ} (hF : Fstar B = B)
    (hO : ∀ P : Subgroup ↥B, P.Normal → IsPGroup 2 ↥P → P = ⊥) :
    ∀ N : Subgroup ↥B, N.Normal → (∃ n : ℕ, N.index = 2 ^ n) → N = ⊤ := by
  intro N hN hidx
  have htop := s15_Three_top_of_fstar (B := B) hF
  have hFN : CFSG.fittingSubgroup ↥B ≤ N :=
    s15_Three_odd_le_of_two_index (s15_Three_fitting_odd (B := B) hO) hN hidx
  have hEN : CFSG.layer ↥B ≤ N := s15_Three_layer_le_of_two_index hN hidx
  rw [eq_top_iff, ← htop]
  exact sup_le hFN hEN

theorem s15_Three_twoCore_of_normal {A B : Subgroup Γ} (hBA : B ≤ A)
    (hn : (B.subgroupOf A).Normal)
    (hO : ∀ P : Subgroup ↥A, P.Normal → IsPGroup 2 ↥P → P = ⊥) :
    ∀ P : Subgroup ↥B, P.Normal → IsPGroup 2 ↥P → P = ⊥ := by
  intro P hPN hPp
  haveI : (B.subgroupOf A).Normal := hn
  let e : ↥(B.subgroupOf A) ≃* ↥B := Subgroup.subgroupOfEquivOfLe hBA
  let Q : Subgroup ↥A := (CFSG.pCore 2 ↥(B.subgroupOf A)).map (B.subgroupOf A).subtype
  have hQp : IsPGroup 2 ↥Q :=
    IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := ↥(B.subgroupOf A)))
      (B.subgroupOf A).subtype
  have hQn : Q.Normal := by
    dsimp only [Q]
    infer_instance
  have hQbot : Q = ⊥ := hO Q hQn hQp
  have hcore_bot : CFSG.pCore 2 ↥(B.subgroupOf A) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (CFSG.pCore 2 ↥(B.subgroupOf A))
      (B.subgroupOf A).subtype_injective).mp hQbot
  have hpcmap : (CFSG.pCore 2 ↥(B.subgroupOf A)).map e.toMonoidHom = CFSG.pCore 2 ↥B :=
    CFSG.pCore_map_iso (G := ↥(B.subgroupOf A)) (G' := ↥B) 2 e
  rw [hcore_bot, Subgroup.map_bot] at hpcmap
  have hPle : P ≤ CFSG.pCore 2 ↥B := le_sSup ⟨hPN, hPp⟩
  exact le_bot_iff.mp (hpcmap.symm ▸ hPle)

theorem s15_Three_involution_mem_layer {B : Subgroup Γ} (hF : Fstar B = B)
    (hO : ∀ P : Subgroup ↥B, P.Normal → IsPGroup 2 ↥P → P = ⊥) {t : Γ} (htB : t ∈ B)
    (ht2 : t * t = 1) : (⟨t, htB⟩ : ↥B) ∈ CFSG.layer ↥B := by
  have htop := s15_Three_top_of_fstar (B := B) hF
  have hodd := s15_Three_fitting_odd (B := B) hO
  exact s15_Three_mem_layer_of_odd (x := (⟨t, htB⟩ : ↥B)) (by
    apply Subtype.ext
    simpa using ht2) htop hodd

end Generic

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
