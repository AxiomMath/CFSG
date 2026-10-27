module

public import CFSG.RankThree.GF2n.Tim78S4Setting
import CFSG.RankThree.GF2n.Tim78Lemma218
import CFSG.RankThree.GF2n.Tim77TI
import CFSG.RankThree.GF2n.Tim78Frattini
import CFSG.RankThree.GF2n.Tim78Normal

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

theorem normalizer_conjSubgroup (g : G) (X : Subgroup G) :
    Subgroup.normalizer (conjSubgroup g X : Set G) =
      conjSubgroup g (Subgroup.normalizer (X : Set G)) := by
  ext c
  rw [mem_conjSubgroup, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    have := h (g * y * g⁻¹)
    simp only [SetLike.mem_coe, mem_conjSubgroup] at this ⊢
    rw [show g⁻¹ * (g * y * g⁻¹) * g = y by group,
      show g⁻¹ * (c * (g * y * g⁻¹) * c⁻¹) * g = (g⁻¹ * c * g) * y * (g⁻¹ * c * g)⁻¹ by group]
      at this
    exact this
  · intro h y
    have := h (g⁻¹ * y * g)
    simp only [SetLike.mem_coe, mem_conjSubgroup] at this ⊢
    rw [show (g⁻¹ * c * g) * (g⁻¹ * y * g) * (g⁻¹ * c * g)⁻¹ = g⁻¹ * (c * y * c⁻¹) * g by group]
      at this
    exact this

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T)
include H

omit [Finite G] in
theorem B_le_M : B ≤ M := H.maxAb.prop.1

omit [Finite G] in
theorem M_le_normalizer_B : M ≤ Subgroup.normalizer (B : Set G) := H.maxAb.prop.2.1

omit [Finite G] in
theorem elemAb : Assembly.IsElemAbelian 2 B := ⟨H.maxAb.prop.2.2, H.sq_eq_one⟩

omit [Finite G] in
theorem B_comm {a b : G} (ha : a ∈ B) (hb : b ∈ B) : a * b = b * a :=
  comm_of_isElemAbelian H.elemAb ha hb

omit [Finite G] in
theorem isPGroup_B : IsPGroup 2 B := fun x => ⟨1, Subtype.ext (by simpa using H.sq_eq_one x x.2)⟩

omit [Finite G] in
theorem B_ne_bot : B ≠ ⊥ := by
  intro h
  have := H.q4
  rw [h, Subgroup.card_bot] at this
  omega

omit [Finite G] in
theorem normalizer_B : Subgroup.normalizer (B : Set G) = M := by
  have hloc : IsPLocal 2 (Subgroup.normalizer (B : Set G)) :=
    ⟨B, H.B_ne_bot, H.isPGroup_B, rfl⟩
  by_contra hne
  exact H.maxLocal.2 _ (lt_of_le_of_ne H.M_le_normalizer_B (Ne.symm hne)) hloc

omit [Finite G] in
theorem isPGroup_Q : IsPGroup 2 Q := H.hQ ▸ (inSubgroup_pCore_two M).1

omit [Finite G] in
theorem Q_le_M : Q ≤ M := H.hQ ▸ (inSubgroup_pCore_two M).2.1

omit [Finite G] in
theorem M_le_normalizer_Q : M ≤ Subgroup.normalizer (Q : Set G) :=
  H.hQ ▸ (inSubgroup_pCore_two M).2.2

omit [Finite G] in
theorem B_le_Q : B ≤ Q :=
  H.hQ ▸ le_inSubgroup_pCore H.B_le_M H.M_le_normalizer_B H.isPGroup_B

omit [Finite G] in
theorem P_le_Q : P ≤ Q := H.hP ▸ iSup₂_le fun _ hg => hg

omit [Finite G] in
theorem P_le_M : P ≤ M := H.P_le_Q.trans H.Q_le_M

omit [Finite G] in
theorem isPGroup_P : IsPGroup 2 P := H.isPGroup_Q.to_le H.P_le_Q

omit [Finite G] in
theorem conj_le_P {g : G} (hg : conjSubgroup g B ≤ Q) : conjSubgroup g B ≤ P := by
  rw [H.hP]
  exact le_iSup₂ (f := fun (g : G) (_ : conjSubgroup g B ≤ Q) => conjSubgroup g B) g hg

omit [Finite G] in
theorem B_le_P : B ≤ P := by
  have := H.conj_le_P (g := 1) (by rw [conjSubgroup_one]; exact H.B_le_Q)
  rwa [conjSubgroup_one] at this

theorem M_le_normalizer_P : M ≤ Subgroup.normalizer (P : Set G) := fun m hm => by
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  have hmQ : ∀ y ∈ Q, m * y * m⁻¹ ∈ Q := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (H.M_le_normalizer_Q hm) y).mp hy
  have h1 : conjSubgroup m P ≤ P := by
    rw [conjSubgroup, Subgroup.map_le_iff_le_comap]
    refine H.hP.le.trans (iSup₂_le fun g hg => ?_)
    rw [← Subgroup.map_le_iff_le_comap]
    have h2 : conjSubgroup m (conjSubgroup g B) ≤ P := by
      rw [← conjSubgroup_mul]
      refine H.conj_le_P ?_
      rw [conjSubgroup_mul]
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      exact hmQ z (hg hz)
    exact h2
  have : m * x * m⁻¹ ∈ conjSubgroup m P := by
    rw [mem_conjSubgroup, show m⁻¹ * (m * x * m⁻¹) * m = x by group]
    exact hx
  exact h1 this

theorem M_le_normalizer_T : M ≤ Subgroup.normalizer (T : Set G) := fun m hm => by
  rw [H.hT]
  exact mem_normalizer_inf (H.M_le_normalizer_Q hm)
    (mem_normalizer_centralizer (H.M_le_normalizer_P hm))


omit [Finite G] in
theorem T_le_Q : T ≤ Q := H.hT ▸ inf_le_left

omit [Finite G] in
theorem T_le_centralizer_P : T ≤ Subgroup.centralizer (P : Set G) := H.hT ▸ inf_le_right

omit [Finite G] in
theorem conj_eq_iff {g : G} : conjSubgroup g B = B ↔ g ∈ M := by
  rw [conjSubgroup_eq_self_iff, H.normalizer_B]

omit [Finite G] in
theorem normalizer_conj_eq (g : G) :
    Subgroup.normalizer (conjSubgroup g B : Set G) = conjSubgroup g M := by
  rw [normalizer_conjSubgroup, H.normalizer_B]

theorem centralizer_le_conj {g x : G} (hx : x ∈ conjSubgroup g B) (hx1 : x ≠ 1) :
    Subgroup.centralizer ({x} : Set G) ≤ conjSubgroup g M := by
  intro c hc
  rw [← H.normalizer_conj_eq, ← conjSubgroup_eq_self_iff]
  refine conjSubgroup_eq_of_isTI (isTI_conjSubgroup H.ti g) fun hbot => ?_
  have hxc : x ∈ conjSubgroup g B ⊓ conjSubgroup c (conjSubgroup g B) := by
    refine Subgroup.mem_inf.mpr ⟨hx, ?_⟩
    rw [mem_conjSubgroup]
    have h1 : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    rw [show c⁻¹ * x * c = x by rw [mul_assoc, ← h1]; group]
    exact hx
  rw [hbot, Subgroup.mem_bot] at hxc
  exact hx1 hxc


theorem normalizer_eq_and_centralizer_le :
    Subgroup.normalizer (B : Set G) = M ∧
      ∀ x ∈ B, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ M := by
  refine ⟨H.normalizer_B, fun x hx hx1 => ?_⟩
  have := H.centralizer_le_conj (g := 1) (by rwa [conjSubgroup_one]) hx1
  rwa [conjSubgroup_one] at this

theorem commute_of_conj_le_M {g : G} (hg : conjSubgroup g B ≤ M) :
    ∀ a ∈ B, ∀ b ∈ conjSubgroup g B, a * b = b * a := fun _ ha _ hb =>
  comm_of_isElemAbelian (Tim77.tim77_2_3 H.elemAb H.ti (by rw [H.normalizer_B]; exact hg))
    (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)

theorem conj_le_M_symm {g : G} (hg : conjSubgroup g B ≤ M) : conjSubgroup g⁻¹ B ≤ M := by
  intro x hx
  rw [mem_conjSubgroup, inv_inv] at hx
  have hb : g * x * g⁻¹ ∈ Subgroup.normalizer (conjSubgroup g B : Set G) :=
    le_normalizer_of_comm (fun b hb a ha => H.commute_of_conj_le_M hg b hb a ha) hx
  rw [H.normalizer_conj_eq, mem_conjSubgroup] at hb
  rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at hb

theorem conj_le_M_of_le_conj {g : G} (hg : B ≤ conjSubgroup g M) : conjSubgroup g B ≤ M := by
  have h1 : conjSubgroup g⁻¹ B ≤ M := by
    intro z hz
    rw [mem_conjSubgroup, inv_inv] at hz
    have := hg hz
    rwa [mem_conjSubgroup, show g⁻¹ * (g * z * g⁻¹) * g = z by group] at this
  have := H.conj_le_M_symm h1
  rwa [inv_inv] at this

section Certified


theorem base_facts :
    inSubgroup frattini Q = B ∧ Q ⊓ Subgroup.centralizer (Q : Set G) = B ∧ ⁅Q, Q⁆ = B ∧
    ∃ k ∈ M, orderOf k = Nat.card B - 1 ∧
      ∀ i : ℕ, 0 < i → i < Nat.card B - 1 → ∀ v ∈ B, k ^ i * v = v * k ^ i → v = 1 := by
  obtain ⟨g, hgQ, hgne⟩ := H.notWC
  have h : Hyp218 M B Q (Q ⊓ Subgroup.centralizer (B : Set G)) (B ⊔ conjSubgroup g B) g :=
    ⟨H.maxLocal, H.fitting, H.maxAb, H.sq_eq_one, H.ti, hgne, hgQ, H.hQ, rfl, rfl⟩
  obtain ⟨-, -, -, -, hfr, hcent, hcomm, -, k, hk, hko, hkreg⟩ :=
    h.conclusions H.q4 (H := (Q ⊓ Subgroup.centralizer (B : Set G)) ⊔
      conjSubgroup g (Q ⊓ Subgroup.centralizer (B : Set G))) rfl
  exact ⟨hfr, hcent, hcomm, k, hk.1, hko, hkreg⟩

theorem le_conjSubgroup_Q {g : G} (hgQ : conjSubgroup g B ≤ Q) (hgB : conjSubgroup g B ≠ B) :
    B ≤ conjSubgroup g Q :=
  (tim78_2_18 (M := M) (V := B) (Q := Q) (P := Q ⊓ Subgroup.centralizer (B : Set G))
    (W := B ⊔ conjSubgroup g B)
    (H := (Q ⊓ Subgroup.centralizer (B : Set G)) ⊔
      conjSubgroup g (Q ⊓ Subgroup.centralizer (B : Set G))) (g := g)
    H.maxLocal H.fitting H.maxAb H.sq_eq_one H.ti H.hQ hgB hgQ H.q4 rfl rfl rfl).1

theorem conj_inv_le_Q {g : G} (hg : conjSubgroup g B ≤ Q) : conjSubgroup g⁻¹ B ≤ Q := by
  by_cases hgB : conjSubgroup g B = B
  · have hgM : g ∈ M := H.conj_eq_iff.mp hgB
    rw [H.conj_eq_iff.mpr (inv_mem hgM)]
    exact H.B_le_Q
  · intro x hx
    rw [mem_conjSubgroup, inv_inv] at hx
    have := H.le_conjSubgroup_Q hg hgB hx
    rw [mem_conjSubgroup] at this
    rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this

theorem conj_inv_le_P_of_conj_le_P {g : G} (hg : conjSubgroup g B ≤ P) :
    conjSubgroup g⁻¹ B ≤ P :=
  H.conj_le_P (H.conj_inv_le_Q (hg.trans H.P_le_Q))

theorem center_Q {b x : G} (hb : b ∈ B) (hx : x ∈ Q) : b * x = x * b := by
  have h : b ∈ Q ⊓ Subgroup.centralizer (Q : Set G) := by
    rw [H.base_facts.2.1]
    exact hb
  exact (Subgroup.mem_centralizer_iff.mp h.2 x hx).symm

theorem commutator_mem {a b : G} (ha : a ∈ Q) (hb : b ∈ Q) : ⁅a, b⁆ ∈ B := by
  have := Subgroup.commutator_mem_commutator ha hb
  rwa [H.base_facts.2.2.1] at this

theorem sq_mem {a : G} (ha : a ∈ Q) : a ^ 2 ∈ B := by
  have := sq_mem_inSubgroup_frattini H.isPGroup_Q ha
  rwa [H.base_facts.1] at this


theorem B_le_T : B ≤ T := by
  rw [H.hT]
  exact le_inf H.B_le_Q fun b hb => Subgroup.mem_centralizer_iff.mpr fun x hx =>
    (H.center_Q hb (H.P_le_Q hx)).symm

theorem eq_B_of_normalized {D : Subgroup G} (hDB : D ≤ B) (hD : D ≠ ⊥)
    (hMD : M ≤ Subgroup.normalizer (D : Set G)) : D = B := by
  obtain ⟨-, -, -, k, hkM, hko, hkreg⟩ := H.base_facts
  obtain ⟨⟨d, hdD⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD
  have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
  have hdB : d ∈ B := hDB hdD
  have hconj : ∀ i : ℕ, k ^ i * d * (k ^ i)⁻¹ ∈ D := fun i =>
    (Subgroup.mem_normalizer_iff.mp (hMD (pow_mem hkM i)) d).mp hdD
  set n := Nat.card B - 1 with hn
  have hlt : ∀ i j : ℕ, i < j → j < n → k ^ i * d * (k ^ i)⁻¹ ≠ k ^ j * d * (k ^ j)⁻¹ := by
    intro i j hij hjn heq
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hij
    have h1 : k ^ (m + 1) * d = d * k ^ (m + 1) := by
      have h2 : d = k ^ (m + 1) * d * (k ^ (m + 1))⁻¹ := by
        have h3 : k ^ (i + m + 1) = k ^ i * k ^ (m + 1) := by rw [Nat.add_assoc, pow_add]
        rw [h3] at heq
        have h4 : k ^ i * d * (k ^ i)⁻¹ =
            k ^ i * (k ^ (m + 1) * d * (k ^ (m + 1))⁻¹) * (k ^ i)⁻¹ := by
          rw [heq]; group
        have h5 := mul_left_cancel (mul_right_cancel h4)
        exact h5
      calc k ^ (m + 1) * d = k ^ (m + 1) * d * (k ^ (m + 1))⁻¹ * k ^ (m + 1) := by group
        _ = d * k ^ (m + 1) := by rw [← h2]
    exact hd1' (hkreg (m + 1) (Nat.succ_pos m) (by omega) d hdB h1)
  let g : Option (Fin n) → D := fun o => match o with
    | none => 1
    | some i => ⟨k ^ (i : ℕ) * d * (k ^ (i : ℕ))⁻¹, hconj i⟩
  have hinj : Function.Injective g := by
    intro a b hab
    rcases a with _ | i <;> rcases b with _ | j
    · rfl
    · exfalso
      have h1 : (1 : G) = k ^ (j : ℕ) * d * (k ^ (j : ℕ))⁻¹ := congrArg Subtype.val hab
      apply hd1'
      have h2 : k ^ (j : ℕ) * d * (k ^ (j : ℕ))⁻¹ = 1 := h1.symm
      calc d = (k ^ (j : ℕ))⁻¹ * (k ^ (j : ℕ) * d * (k ^ (j : ℕ))⁻¹) * k ^ (j : ℕ) := by group
        _ = 1 := by rw [h2]; group
    · exfalso
      have h1 : k ^ (i : ℕ) * d * (k ^ (i : ℕ))⁻¹ = 1 := congrArg Subtype.val hab
      apply hd1'
      calc d = (k ^ (i : ℕ))⁻¹ * (k ^ (i : ℕ) * d * (k ^ (i : ℕ))⁻¹) * k ^ (i : ℕ) := by group
        _ = 1 := by rw [h1]; group
    · have h1 : k ^ (i : ℕ) * d * (k ^ (i : ℕ))⁻¹ = k ^ (j : ℕ) * d * (k ^ (j : ℕ))⁻¹ :=
        congrArg Subtype.val hab
      rcases lt_trichotomy (i : ℕ) j with h | h | h
      · exact absurd h1 (hlt _ _ h j.2)
      · exact congrArg some (Fin.ext h)
      · exact absurd h1.symm (hlt _ _ h i.2)
  have hcard : n + 1 ≤ Nat.card D := by
    have := Nat.card_le_card_of_injective g hinj
    simpa using this
  have hq := H.q4
  exact Subgroup.eq_of_le_of_card_ge hDB (by omega)

end Certified

theorem exists_hyperplane : ∃ Hh : Subgroup G, Hh ≤ B ∧ Nat.card Hh * 2 = Nat.card B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp H.isPGroup_B
  have hm2 : 2 ≤ m := by
    have := H.q4
    rw [hm] at this
    by_contra hlt
    interval_cases m <;> simp at this
  obtain ⟨K, hK, -, hKB⟩ := Sylow.exists_subgroup_card_pow_prime_le_le (G := G) Nat.prime_two
    (n := m - 1) (H := ⊥) (L := B) (by rw [Subgroup.card_bot]; exact one_dvd _)
    (by rw [hm]; exact pow_dvd_pow 2 (Nat.sub_le m 1)) bot_le
  refine ⟨K, hKB, ?_⟩
  rw [hK, hm, ← pow_succ]
  congr 1
  omega

end Hyp4

end CFSG.RankThree.GF2n.Tim78
