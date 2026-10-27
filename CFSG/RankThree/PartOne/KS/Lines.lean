module

public import CFSG.RankThree.PartOne.KS.Model
public import CFSG.RankThree.PartOne.KS.Basic

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.Sporadic.SmallOddCore
open scoped Pointwise commutatorElement

theorem isQuasisimple_of_isSimpleGroup {D : Type*} [Group D] [IsSimpleGroup D]
    (hnab : ∃ a b : D, a * b ≠ b * a) : IsQuasisimple D := by
  have hc : center D = ⊥ := center_eq_bot_of_simple hnab
  let e : D ⧸ center D ≃* D :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  have hcomm : commutator D = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator D) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have hmem : ⁅a, b⁆ ∈ commutator D := Subgroup.commutator_mem_commutator
        (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
        at hmem
      exact hmem
    · exact h
  refine ⟨Group.isPerfect_def.mpr hcomm, ?_, ?_⟩
  · exact @MulEquiv.isSimpleGroup _ _ _ _ ‹IsSimpleGroup D› e
  · obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by simpa using h))⟩

@[expose] def AlmostSimpleLocalCoresTrivial (p : ℕ) (A : Type) [Group A] : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (K : Subgroup H) [K.Normal], Nonempty (K ≃* A) →
    centralizer (K : Set H) = ⊥ → ∀ x : H, orderOf x = p →
      inSubgroup (aschbacherSolvableCore p) (centralizer ({x} : Set H)) = ⊥

theorem almostSimplePlaneOdd_of_localCoresTrivial {p : ℕ} (hp : p.Prime) {A : Type} [Group A]
    (h : AlmostSimpleLocalCoresTrivial p A) : AlmostSimplePlaneOdd p A := by
  intro H _ _ K _ hK hCK E hE hEcard t htE ht1
  have : Fact p.Prime := ⟨hp⟩
  have hord : orderOf t = p :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian t htE) ht1
  have hbot := h H K hK hCK t hord
  have hI : thetaT p E ≤ inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set H)) :=
    iInf_le_of_le t (iInf_le_of_le htE (iInf_le_of_le ht1 le_rfl))
  have hW : localCoreProduct p E t = ⊥ := by
    rw [localCoreProduct, hbot, Subgroup.commutator_bot_left, bot_sup_eq]
    exact le_bot_iff.mp (hI.trans hbot.le)
  rw [hW, Subgroup.card_bot]
  omega

theorem line_core_bot_of_normal_pgroup {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    {P R B Z : Subgroup M} {x : M} (hPB : P ≤ B) (hBR : B ≤ R) (hZP : Z ≤ P)
    (hZp : IsPGroup p Z) (hZx : Z ≤ centralizer ({x} : Set M))
    (hZn : R ⊓ centralizer ({x} : Set M) ≤ normalizer (Z : Set M))
    (hc : IsPGroup p ↥(R ⊓ centralizer ({x} : Set M) ⊓ centralizer (Z : Set M))) :
    inSubgroup (aschbacherSolvableCore p) (B ⊓ centralizer ({x} : Set M)) = ⊥ := by
  set C : Subgroup M := B ⊓ centralizer ({x} : Set M) with hC
  have hZC : Z ≤ C := le_inf (hZP.trans hPB) hZx
  have hCR : C ≤ R ⊓ centralizer ({x} : Set M) := inf_le_inf_right _ hBR
  have hnorm : (Z.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZC).mpr (hCR.trans hZn)
  have hZ' : IsPGroup p (Z.subgroupOf C) :=
    hZp.of_equiv (Subgroup.subgroupOfEquivOfLe hZC).symm
  have hc' : IsPGroup p (centralizer ((Z.subgroupOf C : Subgroup C) : Set C)) := by
    let ϕ : ↥(centralizer ((Z.subgroupOf C : Subgroup C) : Set C)) →*
        ↥(R ⊓ centralizer ({x} : Set M) ⊓ centralizer (Z : Set M)) :=
      { toFun := fun c => ⟨(c : C), ⟨hCR c.1.2, fun z hz => by
          have := Subgroup.mem_centralizer_iff.mp c.2 (⟨z, hZC hz⟩ : C)
            (Subgroup.mem_subgroupOf.mpr hz)
          exact congrArg Subtype.val this⟩⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine hc.of_injective ϕ fun a b hab => ?_
    have h' := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h')
  have := aschbacherCore_bot_of_normal_pgroup hp hZ' hc'
  rw [inSubgroup, this, Subgroup.map_bot]

theorem line_core_bot_of_normal_component {M : Type*} [Group M] [Finite M] {p : ℕ}
    (hp : p.Prime) {P R B D : Subgroup M} {x : M} (hPB : P ≤ B) (hBR : B ≤ R) (hDP : D ≤ P)
    (hDq : IsQuasisimple D) (hDx : D ≤ centralizer ({x} : Set M))
    (hDn : R ⊓ centralizer ({x} : Set M) ≤ normalizer (D : Set M))
    (hc : IsPGroup p ↥(R ⊓ centralizer ({x} : Set M) ⊓ centralizer (D : Set M))) :
    inSubgroup (aschbacherSolvableCore p) (B ⊓ centralizer ({x} : Set M)) = ⊥ := by
  set C : Subgroup M := B ⊓ centralizer ({x} : Set M) with hC
  have hDC : D ≤ C := le_inf (hDP.trans hPB) hDx
  have hCR : C ≤ R ⊓ centralizer ({x} : Set M) := inf_le_inf_right _ hBR
  have hnorm : (D.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDC).mpr (hCR.trans hDn)
  have hD' : IsQuasisimple (D.subgroupOf C) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hDC).symm hDq
  have hc' : IsPGroup p (centralizer ((D.subgroupOf C : Subgroup C) : Set C)) := by
    let ϕ : ↥(centralizer ((D.subgroupOf C : Subgroup C) : Set C)) →*
        ↥(R ⊓ centralizer ({x} : Set M) ⊓ centralizer (D : Set M)) :=
      { toFun := fun c => ⟨(c : C), ⟨hCR c.1.2, fun z hz => by
          have := Subgroup.mem_centralizer_iff.mp c.2 (⟨z, hDC hz⟩ : C)
            (Subgroup.mem_subgroupOf.mpr hz)
          exact congrArg Subtype.val this⟩⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine hc.of_injective ϕ fun a b hab => ?_
    have h' := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h')
  have := aschbacherCore_bot_of_normal_component hp hD' hc'
  rw [inSubgroup, this, Subgroup.map_bot]

theorem map_conj_eq_self_of_mem {G : Type*} [Group G] {H : Subgroup G} {g : G} (hg : g ∈ H) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  ext z
  rw [Subgroup.mem_map_equiv]
  constructor
  · intro hz
    have := H.mul_mem (H.mul_mem hg hz) (H.inv_mem hg)
    simpa [MulAut.conj_symm_apply, mul_assoc] using this
  · intro hz
    have := H.mul_mem (H.mul_mem (H.inv_mem hg) hz) hg
    simpa [MulAut.conj_symm_apply, mul_assoc] using this

theorem closure_le_centralizer_closure_of_forall_comm {G : Type*} [Group G] {S : Set G}
    (h : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) :
    Subgroup.closure S ≤ centralizer (Subgroup.closure S : Set G) := by
  have h1 : Subgroup.closure S ≤ centralizer S :=
    (Subgroup.closure_le _).2 fun a ha => Subgroup.mem_centralizer_iff.2 fun b hb => h b hb a ha
  rw [Subgroup.closure_le]
  intro a ha
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro x hx
  exact (Subgroup.mem_centralizer_iff.1 (h1 hx) a ha).symm

theorem commutator_self_le {G : Type*} [Group G] (C : Subgroup G) : ⁅C, C⁆ ≤ C :=
  Subgroup.commutator_le.mpr fun g hg h hh => by
    rw [commutatorElement_def]
    exact C.mul_mem (C.mul_mem (C.mul_mem hg hh) (C.inv_mem hg)) (C.inv_mem hh)

theorem le_normalizer_commutator_self {G : Type*} [Group G] (C : Subgroup G) :
    C ≤ normalizer ((⁅C, C⁆ : Subgroup G) : Set G) := by
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  have hmap : (⁅C, C⁆ : Subgroup G).map (MulAut.conj c).toMonoidHom = ⁅C, C⁆ := by
    rw [Subgroup.map_commutator, map_conj_eq_self_of_mem hc]
  intro z
  have h : c * z * c⁻¹ ∈ (⁅C, C⁆ : Subgroup G).map (MulAut.conj c).toMonoidHom ↔
      z ∈ (⁅C, C⁆ : Subgroup G) := by
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    simp [mul_assoc]
  rw [hmap] at h
  exact h.symm

theorem card_core_conj {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    (B : Subgroup M) {g : M} (hg : g ∈ B) (y' : M) :
    Nat.card (inSubgroup (aschbacherSolvableCore p) (B ⊓ centralizer ({g * y' * g⁻¹} : Set M))) =
      Nat.card (inSubgroup (aschbacherSolvableCore p) (B ⊓ centralizer ({y'} : Set M))) := by
  have hBconj : B.map (MulAut.conj g).toMonoidHom = B := map_conj_eq_self_of_mem hg
  have hmap : (B ⊓ centralizer ({y'} : Set M)).map (MulAut.conj g).toMonoidHom =
      B ⊓ centralizer ({g * y' * g⁻¹} : Set M) := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hBconj,
      map_centralizer_singleton_mulEquiv (MulAut.conj g) y']
    simp [MulAut.conj_apply]
  have h1 := SteinbergBY.map_inSubgroup_aschbacherSolvableCore_mulEquiv hp (MulAut.conj g)
    (B ⊓ centralizer ({y'} : Set M))
  rw [hmap] at h1
  rw [← h1]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem line_core_le_of_normal_component {M : Type*} [Group M] [Finite M] {p : ℕ}
    (hp : p.Prime) {P R B D : Subgroup M} {x : M} (hPB : P ≤ B) (hBR : B ≤ R) (hDP : D ≤ P)
    (hDq : IsQuasisimple D) (hDx : D ≤ centralizer ({x} : Set M))
    (hDn : R ⊓ centralizer ({x} : Set M) ≤ normalizer (D : Set M)) :
    inSubgroup (aschbacherSolvableCore p) (B ⊓ centralizer ({x} : Set M)) ≤
      R ⊓ centralizer ({x} : Set M) ⊓ centralizer (D : Set M) := by
  set C : Subgroup M := B ⊓ centralizer ({x} : Set M) with hC
  have hDC : D ≤ C := le_inf (hDP.trans hPB) hDx
  have hCR : C ≤ R ⊓ centralizer ({x} : Set M) := inf_le_inf_right _ hBR
  have hnorm : (D.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDC).mpr (hCR.trans hDn)
  have hD' : IsQuasisimple (D.subgroupOf C) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hDC).symm hDq
  have hle := aschbacherCore_le_centralizer_of_normal_component hp hD'
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨hCR y.2, ?_⟩
  show (y : M) ∈ centralizer (D : Set M)
  rw [mem_centralizer_iff]
  intro z hz
  have := Subgroup.mem_centralizer_iff.mp (hle hy) (⟨z, hDC hz⟩ : C)
    (Subgroup.mem_subgroupOf.mpr hz)
  exact congrArg Subtype.val this

theorem exists_conj_line {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    {P Q : Subgroup M} {ι : Type*} {xs : ι → M}
    (hSyl : ∃ S : Sylow p P, (S : Subgroup P) = Q.subgroupOf P)
    (hlines : {H : Subgroup M | H ≤ Q ∧ Nat.card H = p} =
      Set.range (fun i : ι => zpowers (xs i)))
    {y : M} (hyP : y ∈ P) (hord : orderOf y = p) :
    ∃ g : M, g ∈ P ∧ ∃ i : ι,
      centralizer ({g⁻¹ * y * g} : Set M) = centralizer ({xs i} : Set M) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S₀, hS₀⟩ := hSyl
  have hpgrp : IsPGroup p (zpowers (⟨y, hyP⟩ : P)) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, hord, pow_one])
  obtain ⟨S, hS⟩ := hpgrp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P S₀ S
  have hyS : (⟨y, hyP⟩ : P) ∈ (S : Subgroup P) := hS (Subgroup.mem_zpowers _)
  have hy'Q : (g : M)⁻¹ * y * (g : M) ∈ Q := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hyS
    rw [hS₀, Subgroup.mem_subgroupOf] at hyS
    simpa [MulAut.smul_def, ← map_inv, MulAut.conj_apply, mul_assoc] using hyS
  have hord' : orderOf ((g : M)⁻¹ * y * (g : M)) = p := by
    have := orderOf_injective (MulAut.conj (g : M)⁻¹).toMonoidHom
      (MulAut.conj (g : M)⁻¹).injective y
    rw [hord] at this
    rw [← this]
    simp [mul_assoc]
  have hmem : zpowers ((g : M)⁻¹ * y * (g : M)) ∈ {H : Subgroup M | H ≤ Q ∧ Nat.card H = p} :=
    ⟨zpowers_le.mpr hy'Q, by rw [Nat.card_zpowers, hord']⟩
  rw [hlines] at hmem
  obtain ⟨i, hi⟩ := hmem
  refine ⟨g, g.2, i, ?_⟩
  rw [SteinbergBY.centralizer_singleton_eq_centralizer_zpowers,
    SteinbergBY.centralizer_singleton_eq_centralizer_zpowers (xs i)]
  simp only at hi
  rw [hi]

theorem core_bot_of_lines {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    {P R Q : Subgroup M} {ι : Type*} {xs : ι → M}
    (hSyl : ∃ S : Sylow p P, (S : Subgroup P) = Q.subgroupOf P)
    (hlines : {H : Subgroup M | H ≤ Q ∧ Nat.card H = p} =
      Set.range (fun i : ι => zpowers (xs i)))
    (hgood : ∀ i, ∀ B : Subgroup M, P ≤ B → B ≤ R →
      inSubgroup (aschbacherSolvableCore p) (B ⊓ centralizer ({xs i} : Set M)) = ⊥) :
    ∀ B : Subgroup M, P ≤ B → B ≤ R → ∀ y ∈ P, orderOf y = p →
      inSubgroup (aschbacherSolvableCore p) (B ⊓ centralizer ({y} : Set M)) = ⊥ := by
  intro B hPB hBR y hyP hord
  obtain ⟨g, hgP, i, hcent⟩ := exists_conj_line hp hSyl hlines hyP hord
  have h1 := card_core_conj hp B (hPB hgP) ((g : M)⁻¹ * y * (g : M))
  rw [show (g : M) * ((g : M)⁻¹ * y * (g : M)) * (g : M)⁻¹ = y by group, hcent,
    hgood i B hPB hBR, Subgroup.card_bot] at h1
  exact Subgroup.card_eq_one.mp h1

theorem core_card_le_of_lines {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    {P R Q : Subgroup M} {ι : Type*} {xs : ι → M} {k : ℕ}
    (hSyl : ∃ S : Sylow p P, (S : Subgroup P) = Q.subgroupOf P)
    (hlines : {H : Subgroup M | H ≤ Q ∧ Nat.card H = p} =
      Set.range (fun i : ι => zpowers (xs i)))
    (hbound : ∀ i, ∀ B : Subgroup M, P ≤ B → B ≤ R →
      Nat.card (inSubgroup (aschbacherSolvableCore p) (B ⊓ centralizer ({xs i} : Set M))) ≤ k) :
    ∀ B : Subgroup M, P ≤ B → B ≤ R → ∀ y ∈ P, orderOf y = p →
      Nat.card (inSubgroup (aschbacherSolvableCore p) (B ⊓ centralizer ({y} : Set M))) ≤ k := by
  intro B hPB hBR y hyP hord
  obtain ⟨g, hgP, i, hcent⟩ := exists_conj_line hp hSyl hlines hyP hord
  have h1 := card_core_conj hp B (hPB hgP) ((g : M)⁻¹ * y * (g : M))
  rw [show (g : M) * ((g : M)⁻¹ * y * (g : M)) * (g : M)⁻¹ = y by group, hcent] at h1
  rw [h1]
  exact hbound i B hPB hBR

end CFSG.RankThree.PartOne
