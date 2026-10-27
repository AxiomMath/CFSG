module

public import CFSG.RankThree.PartTwo.Sec15.Item15Inputs
public import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.RankThree.PartTwo.Sec6.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1423

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec6
open scoped commutatorElement

section Exists

variable {H : Type*} [Group H] [Finite H]

theorem exists_isComponent_of_theta_eq_bot {Γ : Type*} [Group Γ] [Finite Γ] [Nontrivial Γ]
    (h3 : ¬ 3 ∣ Nat.card Γ) (hθ : aschbacherSolvableCore 3 Γ = ⊥) :
    ∃ J : Subgroup Γ, IsComponent J := by
  have hF : fittingSubgroup Γ = ⊥ := by
    have hmax :=
      (solvable_prime_complement_core_characterization (H := Γ) Nat.prime_three).2.2.2.1
    have hle := hmax (fittingSubgroup Γ) inferInstance inferInstance
      (fun h => h3 (h.trans (Subgroup.card_subgroup_dvd_card _)))
    rwa [hθ, le_bot_iff] at hle
  by_contra hno
  push Not at hno
  have hE : layer Γ = ⊥ := LocalCores.layer_eq_bot_of_forall hno
  have hC := centralizer_generalizedFitting_le Γ
  rw [generalizedFitting, hF, hE, bot_sup_eq, Subgroup.coe_bot,
    Subgroup.centralizer_eq_top_iff_subset.mpr (by simp), top_le_iff] at hC
  obtain ⟨x, y, hxy⟩ := exists_pair_ne Γ
  have hx : x ∈ (⊥ : Subgroup Γ) := hC ▸ Subgroup.mem_top x
  have hy : y ∈ (⊥ : Subgroup Γ) := hC ▸ Subgroup.mem_top y
  rw [Subgroup.mem_bot] at hx hy
  exact hxy (hx.trans hy.symm)

theorem exists_mem_thetaComponents_of_not_isSolvable (h3 : ¬ 3 ∣ Nat.card H)
    (hs : ¬ Group.IsSolvable H) : ∃ K : Subgroup H, K ∈ thetaComponents 3 H := by
  set N := aschbacherSolvableCore 3 H with hN
  have hNs : Group.IsSolvable N :=
    (solvable_prime_complement_core_characterization (H := H) Nat.prime_three).1
  have hnt : Nontrivial (H ⧸ N) := by
    rcases subsingleton_or_nontrivial (H ⧸ N) with h | h
    · exfalso
      apply hs
      have htop : N = ⊤ := by
        rw [eq_top_iff]
        intro x _
        have : (x : H ⧸ N) = 1 := Subsingleton.elim _ _
        exact (QuotientGroup.eq_one_iff x).mp this
      have e : N ≃* H := (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
      exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    · exact h
  have h3' : ¬ 3 ∣ Nat.card (H ⧸ N) := fun h => h3 (h.trans (Subgroup.card_quotient_dvd_card N))
  obtain ⟨J, hJ⟩ := exists_isComponent_of_theta_eq_bot h3' theta_quotient_core_and_ranks.1
  exact ⟨_, (perfectResidual_comap_mem_thetaComponents Nat.prime_three hJ).1⟩

end Exists

section Members

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isSubnormal_subgroupOf_trans1423 {E Y X : Subgroup G} (hEY : E ≤ Y) (hYX : Y ≤ X)
    (hE : (E.subgroupOf Y).IsSubnormal) (hY : (Y.subgroupOf X).IsSubnormal) :
    (E.subgroupOf X).IsSubnormal := by
  let ι : ↥(Y.subgroupOf X) →* ↥Y := (Subgroup.subgroupOfEquivOfLe hYX).toMonoidHom
  have hcomap : (E.subgroupOf Y).comap ι = (E.subgroupOf X).subgroupOf (Y.subgroupOf X) := by
    ext g
    exact Iff.rfl
  have h1 : ((E.subgroupOf X).subgroupOf (Y.subgroupOf X)).IsSubnormal := by
    rw [← hcomap]
    exact hE.comap ι
  exact Subgroup.IsSubnormal.trans (fun x hx => hEY hx) h1 hY

theorem isQuasisimple_of_mem_thetaComponentsIn1423 {M K : Subgroup G}
    (hK : K ∈ thetaComponentsIn M) : IsQuasisimple (K ⧸ aschbacherSolvableCore 3 K) := by
  obtain ⟨hKM, hK'⟩ := mem_thetaComponentsIn_iff.mp hK
  set e := Subgroup.subgroupOfEquivOfLe hKM
  exact LocalCores.isQuasisimple_of_mulEquiv
    (QuotientGroup.congr _ _ e (aschbacherSolvableCore_map_mulEquiv Nat.prime_three e)) hK'.2.2

theorem mem_thetaComponentsIn_of_isSubnormal {N M K : Subgroup G} (hK : K ∈ thetaComponentsIn N)
    (hNM : N ≤ M) (hN : (N.subgroupOf M).IsSubnormal) : K ∈ thetaComponentsIn M := by
  obtain ⟨hKN, hK'⟩ := mem_thetaComponentsIn_iff.mp hK
  exact mem_thetaComponentsIn_of (hKN.trans hNM) (isPerfect_of_mem_thetaComponentsIn hK)
    (isSubnormal_subgroupOf_trans1423 hKN hNM hK'.2.1 hN)
    (isQuasisimple_of_mem_thetaComponentsIn1423 hK)

theorem map_conj_mem_thetaComponentsIn1423 {M : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (M : Set G)) {X : Subgroup G}
    (hX : X ∈ thetaComponentsIn M) :
    X.map (MulAut.conj a).toMonoidHom ∈ thetaComponentsIn M := by
  have hM : M.map (MulAut.conj a).toMonoidHom = M := Subgroup.mem_normalizer_iff_map_conj_eq.mp ha
  set σ : ↥M ≃* ↥M := ((MulAut.conj a).subgroupMap M).trans (MulEquiv.subgroupCongr hM)
  obtain ⟨X', hX', rfl⟩ := hX
  refine ⟨X'.map σ.toMonoidHom, map_mulEquiv_mem_thetaComponents Nat.prime_three σ hX', ?_⟩
  change (X'.map σ.toMonoidHom).map M.subtype = (X'.map M.subtype).map (MulAut.conj a).toMonoidHom
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem not_le_thetaQuotCentralizer_self {M K : Subgroup G} (hK : K ∈ thetaComponentsIn M) :
    ¬ K ≤ thetaQuotCentralizer K := by
  intro hKC
  have hKp := isPerfect_of_mem_thetaComponentsIn hK
  have hle : ⁅K, K⁆ ≤ inSubgroup (aschbacherSolvableCore 3) K :=
    (commutator_le_theta_iff Subgroup.le_normalizer).mpr hKC
  rw [commutator_self_eq_of_isPerfect hKp] at hle
  have htop : aschbacherSolvableCore 3 K = ⊤ := by
    rw [eq_top_iff]
    intro k _
    obtain ⟨t, ht, htk⟩ := hle k.2
    have : t = k := Subtype.ext htk
    exact this ▸ ht
  have hnt := LocalCores.isQuasisimple_nontrivial (isQuasisimple_of_mem_thetaComponentsIn1423 hK)
  have : Subsingleton (K ⧸ aschbacherSolvableCore 3 K) := by
    rw [htop]
    exact QuotientGroup.subsingleton_quotient_top
  exact not_nontrivial _ hnt

end Members

section Conj

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_map_conj_iff1423 {K : Subgroup G} {g y : G} :
    y ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ K := by
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem map_conj_theta1423 (K : Subgroup G) (g : G) :
    (inSubgroup (aschbacherSolvableCore 3) K).map (MulAut.conj g).toMonoidHom =
      inSubgroup (aschbacherSolvableCore 3) (K.map (MulAut.conj g).toMonoidHom) := by
  set e : K ≃* K.map (MulAut.conj g).toMonoidHom :=
    K.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  rw [inSubgroup, inSubgroup, ← aschbacherSolvableCore_map_mulEquiv Nat.prime_three e,
    Subgroup.map_map, Subgroup.map_map]
  rfl

theorem conj_mem_thetaQuotCentralizer_map {K : Subgroup G} {x : G}
    (hx : x ∈ thetaQuotCentralizer K) (g : G) :
    g * x * g⁻¹ ∈ thetaQuotCentralizer (K.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hxN, hxl⟩ := mem_thetaQuotCentralizer_iff.mp hx
  refine mem_thetaQuotCentralizer_iff.mpr ⟨?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [mem_map_conj_iff1423, mem_map_conj_iff1423]
    have := Subgroup.mem_normalizer_iff.mp hxN (g⁻¹ * y * g)
    rw [this]
    constructor <;> intro h <;> convert h using 1 <;> group
  · intro l hl
    rw [← map_conj_theta1423, mem_map_conj_iff1423]
    rw [mem_map_conj_iff1423] at hl
    have h := hxl _ hl
    convert h using 1
    group

omit [Finite G] in
theorem map_conj_map_conj_inv (K : Subgroup G) (g : G) :
    (K.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = K := by
  ext y
  rw [mem_map_conj_iff1423, mem_map_conj_iff1423]
  constructor <;> intro h <;> convert h using 1 <;> group

end Conj

section Reduction

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_normalClosureSub_of_forall {X E : Subgroup G} (hX3 : ¬ 3 ∣ Nat.card X)
    (hcent : ∀ K ∈ thetaComponentsIn X, E ≤ thetaQuotCentralizer K) :
    Group.IsSolvable (normalClosureSub X E) := by
  set S : Set X := ((E.subgroupOf X : Subgroup X) : Set X) with hS
  set N := normalClosureSub X E with hN
  have hNdef : N = (Subgroup.normalClosure S).map X.subtype := rfl
  have hNC : ∀ K ∈ thetaComponentsIn X, N ≤ thetaQuotCentralizer K := by
    intro K hK
    rw [hNdef, Subgroup.map_le_iff_le_comap, Subgroup.normalClosure, Subgroup.closure_le]
    intro y hy
    obtain ⟨a, ha, hay⟩ := Group.mem_conjugatesOfSet_iff.mp hy
    obtain ⟨x, rfl⟩ := isConj_iff.mp hay
    have haE : (a : G) ∈ E := Subgroup.mem_subgroupOf.mp ha
    have hxN : (x⁻¹ : G) ∈ Subgroup.normalizer (X : Set G) :=
      Subgroup.le_normalizer (X.inv_mem x.2)
    have hK' := map_conj_mem_thetaComponentsIn1423 hxN hK
    have h1 := conj_mem_thetaQuotCentralizer_map (hcent _ hK' haE) (x : G)
    rw [map_conj_map_conj_inv] at h1
    change ((x * a * x⁻¹ : X) : G) ∈ thetaQuotCentralizer K
    simpa using h1
  by_contra hs
  have hNX : N ≤ X := Subgroup.map_subtype_le _
  have hN3 : ¬ 3 ∣ Nat.card N := fun h => hX3 (h.trans (Subgroup.card_dvd_of_le hNX))
  obtain ⟨K₀, hK₀⟩ := exists_mem_thetaComponents_of_not_isSolvable hN3 hs
  have hKN : K₀.map N.subtype ∈ thetaComponentsIn N := ⟨K₀, hK₀, rfl⟩
  have hNnorm : (N.subgroupOf X).Normal := by
    have : N.subgroupOf X = Subgroup.normalClosure S := by
      rw [hNdef, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective X.subtype_injective]
    rw [this]
    exact Subgroup.normalClosure_normal
  have hKX := mem_thetaComponentsIn_of_isSubnormal hKN hNX hNnorm.isSubnormal
  exact not_le_thetaQuotCentralizer_self hKX
    ((le_of_mem_thetaComponentsIn hKN).trans (hNC _ hKX))

end Reduction

section Comm

variable {G : Type} [Group G] [Finite G]

theorem commutator_le_theta_of_normalizes {L M : Subgroup G}
    (hLq : IsQuasisimple (↥L ⧸ aschbacherSolvableCore 3 ↥L)) (hLp : Group.IsPerfect L)
    (hL3 : 3 ∣ Nat.card L) (hM3 : ¬ 3 ∣ Nat.card M)
    (hML : M ≤ Subgroup.normalizer (L : Set G)) (hLM : L ≤ Subgroup.normalizer (M : Set G)) :
    ⁅M, L⁆ ≤ inSubgroup (aschbacherSolvableCore 3) L := by
  set θL := inSubgroup (aschbacherSolvableCore 3) L with hθL
  have hMLM : ⁅M, L⁆ ≤ M := Subgroup.le_normalizer_iff_commutator_le_right.mp hLM |>.trans' (by
    rw [Subgroup.commutator_comm])
  have hMLL : ⁅M, L⁆ ≤ L := Subgroup.le_normalizer_iff_commutator_le_right.mp hML
  have hLN : L ≤ Subgroup.normalizer ((M ⊓ L : Subgroup G) : Set G) :=
    le_inf hLM Subgroup.le_normalizer |>.trans Subgroup.inf_normalizer_le_normalizer_inf
  have hθN : L ≤ Subgroup.normalizer (θL : Set G) := le_normalizer_theta L
  rcases sup_theta_eq_or_commutator_le hLq inf_le_right hLN with h | h
  · exfalso
    have h1 : ¬ 3 ∣ Nat.card (M ⊓ L : Subgroup G) :=
      fun h' => hM3 (h'.trans (Subgroup.card_dvd_of_le inf_le_left))
    have h2 := not_dvd_card_sup Nat.prime_three (inf_le_right.trans hθN) h1
      (theta_solvable_and_not_dvd L).2
    rw [h] at h2
    exact h2 hL3
  · have hMθ : M ≤ Subgroup.normalizer (θL : Set G) :=
      hML.trans (normalizer_le_normalizer_theta L)
    have h2 : ⁅⁅M, L⁆, L⁆ ≤ θL :=
      (Subgroup.commutator_mono (le_inf hMLM hMLL) le_rfl).trans h
    have h1 : ⁅⁅L, M⁆, L⁆ ≤ θL := by rwa [Subgroup.commutator_comm L M]
    have h3 := three_subgroups_mod hθN hMθ hθN h1 h2
    rwa [commutator_self_eq_of_isPerfect hLp, Subgroup.commutator_comm] at h3

omit [Finite G] in
theorem le_of_isPerfect_of_commutator_le {D H N : Subgroup G} (hDp : Group.IsPerfect D)
    (hDH : D ≤ H) (hHN : ⁅H, H⁆ ≤ N) : D ≤ N := by
  rw [← commutator_self_eq_of_isPerfect hDp]
  exact (Subgroup.commutator_mono hDH hDH).trans hHN

end Comm

end CFSG.RankThree.PartTwo.Sec15.Proof1423
