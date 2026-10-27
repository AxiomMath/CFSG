module

public import CFSG.Quasithin.Vol2.Ch12Sec2Inputs
public import CFSG.Quasithin.Vol2.Ch1Chief
public import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.Quasithin.EmptyFaithful.Setting

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

section A142

variable {G : Type} [Group G] {L J K : Subgroup G}

theorem le_normalizer_commutator (hJ : L ≤ Subgroup.normalizer (J : Set G))
    (hK : L ≤ Subgroup.normalizer (K : Set G)) :
    L ≤ Subgroup.normalizer ((⁅J, K⁆ : Subgroup G) : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hJ hh),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hK hh)]

theorem commutator_le_self (hJ : L ≤ Subgroup.normalizer (J : Set G)) : ⁅J, L⁆ ≤ J := by
  rw [Subgroup.commutator_le]
  intro j hj l hl
  have h1 : l * j⁻¹ * l⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hJ hl) j⁻¹).mp (J.inv_mem hj)
  rw [commutatorElement_def, show j * l * j⁻¹ * l⁻¹ = j * (l * j⁻¹ * l⁻¹) by group]
  exact J.mul_mem hj h1

theorem le_normalizer_self' : L ≤ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer

theorem commutator_commutator_eq (hO2 : ∀ N : Subgroup G, N ≤ L → (N.subgroupOf L).Normal →
      (∀ x ∈ L, ∃ k : ℕ, x ^ 2 ^ k ∈ N) → N = L)
    (hJ : L ≤ Subgroup.normalizer (J : Set G)) (h2 : ∀ c ∈ ⁅J, L⁆, c * c = 1) :
    ⁅⁅J, L⁆, L⁆ = ⁅J, L⁆ := by
  set K₁ := ⁅J, L⁆ with hK₁
  set K₂ := ⁅K₁, L⁆ with hK₂
  have hLK₁ : L ≤ Subgroup.normalizer (K₁ : Set G) :=
    le_normalizer_commutator hJ le_normalizer_self'
  have hLK₂ : L ≤ Subgroup.normalizer (K₂ : Set G) :=
    le_normalizer_commutator hLK₁ le_normalizer_self'
  refine le_antisymm (commutator_le_self hLK₁) ?_
  let N : Subgroup G :=
    { carrier := {l | l ∈ L ∧ ∀ j ∈ J, ⁅j, l⁆ ∈ K₂}
      one_mem' := ⟨L.one_mem, fun j _ => by rw [commutatorElement_one_right]; exact K₂.one_mem⟩
      mul_mem' := fun {a b} ha hb => ⟨L.mul_mem ha.1 hb.1, fun j hj => by
        have e : ⁅j, a * b⁆ = ⁅j, a⁆ * (a * ⁅j, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact K₂.mul_mem (ha.2 j hj)
          ((Subgroup.mem_normalizer_iff.mp (hLK₂ ha.1) _).mp (hb.2 j hj))⟩
      inv_mem' := fun {a} ha => ⟨L.inv_mem ha.1, fun j hj => by
        have e : ⁅j, a⁻¹⁆ = a⁻¹ * ⁅j, a⁆⁻¹ * a := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have h1 := K₂.inv_mem (ha.2 _ hj)
        have := (Subgroup.mem_normalizer_iff.mp (hLK₂ (L.inv_mem ha.1)) _).mp h1
        simpa using this⟩ }
  have hNL : N ≤ L := fun _ h => h.1
  have hNn : (N.subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨L.mul_mem (L.mul_mem g.2 hn.1) (L.inv_mem g.2), fun j hj => ?_⟩
    have hj' : (g : G)⁻¹ * j * g ∈ J := by
      have := (Subgroup.mem_normalizer_iff.mp (hJ (L.inv_mem g.2)) j).mp hj
      simpa using this
    have e : ⁅j, (g : G) * (n : G) * (g : G)⁻¹⁆ =
        (g : G) * ⁅(g : G)⁻¹ * j * g, (n : G)⁆ * (g : G)⁻¹ := by
      simp only [commutatorElement_def]
      group
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hLK₂ g.2) _).mp (hn.2 _ hj')
  have hsq : ∀ x ∈ L, ∃ k : ℕ, x ^ 2 ^ k ∈ N := fun x hx => ⟨1, by
    rw [pow_one, pow_two]
    refine ⟨L.mul_mem hx hx, fun j hj => ?_⟩
    set c := ⁅j, x⁆ with hc
    have hcK₁ : c ∈ K₁ := Subgroup.commutator_mem_commutator hj hx
    have hcinv : c⁻¹ ∈ K₁ := K₁.inv_mem hcK₁
    have e : ⁅j, x * x⁆ = (c * c) * ⁅c⁻¹, x⁆ := by
      simp only [hc, commutatorElement_def]
      group
    rw [e, h2 c hcK₁, one_mul]
    exact Subgroup.commutator_mem_commutator hcinv hx⟩
  have hNeq := hO2 N hNL hNn hsq
  rw [Subgroup.commutator_le]
  intro j hj l hl
  have hlN : l ∈ N := hNeq ▸ hl
  exact hlN.2 j hj

theorem exists_irrPlusBase [Finite G] {R : Subgroup G}
    (hO2 : ∀ N : Subgroup G, N ≤ L → (N.subgroupOf L).Normal →
      (∀ x ∈ L, ∃ k : ℕ, x ^ 2 ^ k ∈ N) → N = L)
    (hR2 : ∀ x ∈ R, x * x = 1) (hLR : L ≤ Subgroup.normalizer (R : Set G)) (hne : ⁅R, L⁆ ≠ ⊥) :
    ∃ I : Subgroup G, IsIrrPlusBase L R I := by
  let P : Subgroup G → Prop := fun J =>
    J ≤ R ∧ L ≤ Subgroup.normalizer (J : Set G) ∧ ⁅J, L⁆ = J ∧ J ≠ ⊥
  have hP : ∀ J : Subgroup G, J ≤ R → L ≤ Subgroup.normalizer (J : Set G) → ⁅J, L⁆ ≠ ⊥ →
      P ⁅J, L⁆ := fun J hJR hLJ hc =>
    ⟨(commutator_le_self hLJ).trans hJR, le_normalizer_commutator hLJ le_normalizer_self',
      commutator_commutator_eq hO2 hLJ fun c hc' => hR2 c ((commutator_le_self hLJ).trans hJR hc'),
      hc⟩
  obtain ⟨I, hPI, hmin⟩ := (wellFounded_lt (α := Subgroup G)).has_min {J | P J}
    ⟨_, hP R le_rfl hLR hne⟩
  obtain ⟨hIR, hLI, hII, hI1⟩ := hPI
  refine ⟨I, hIR, hI1, hLI, hII, ?_, fun J hCJ hJI hLJ => ?_⟩
  · refine lt_of_le_of_ne inf_le_left fun h => hI1 ?_
    have hIC : I ≤ Subgroup.centralizer (L : Set G) := h ▸ inf_le_right
    rw [← hII]
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hIC
  · by_cases hc : ⁅J, L⁆ = ⊥
    · left
      exact le_antisymm (le_inf hJI ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp hc)) hCJ
    · right
      have hJ'I : ⁅J, L⁆ ≤ I := (commutator_le_self hLJ).trans hJI
      have heq : ⁅J, L⁆ = I :=
        hJ'I.eq_or_lt.resolve_right (hmin _ (hP J (hJI.trans hIR) hLJ hc))
      exact le_antisymm hJI (heq ▸ commutator_le_self hLJ)

end A142

theorem irrPlusBaseNonempty_of_a36 (h36 : A36ForSQTK) : IrrPlusBaseNonempty := by
  intro G _ _ T L hs hnab hQ hT _ hf _ _
  obtain ⟨S, hS⟩ := CFSG.Quasithin.exists_sylow_of_quasithinIsSylowTwo hT
  have hInH : InH (S : Subgroup G) (L ⊔ T) := ⟨hS ▸ le_sup_right, hf.1.2.2.2⟩
  have hcc : L ∈ cComp (L ⊔ T) := hf.1.2.1
  have hf' : quasithinIsFaithfulLocal (S : Subgroup G) L := by rw [hS]; exact hf
  have hRL := ((lemma_1_2_10_of_a36 hQ hs hnab h36 S hInH hcc).out 1 3).mp hf'
  obtain ⟨-, hLR, ⟨-, hR2⟩, -⟩ := A4.isTwoReducedIn_twoReducedJoin (L ⊔ T)
  obtain ⟨I, hI⟩ := exists_irrPlusBase hf.2.1 (fun x hx => by rw [← pow_two]; exact hR2 x hx)
    (le_sup_left.trans hLR) hRL
  refine ⟨I, ?_⟩
  rw [show reducedAggregate (L ⊔ T) = twoReducedJoin (L ⊔ T) from
    primeReducedAggregate_map_subtype_eq_twoReducedJoin (L ⊔ T)]
  exact hI

end CFSG.Quasithin.H13
