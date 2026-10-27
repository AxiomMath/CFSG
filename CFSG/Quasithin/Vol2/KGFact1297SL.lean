module

public import CFSG.Quasithin.Vol2.KGFact1297Par
public import CFSG.Quasithin.Vol2.KGFact1296
public import CFSG.Quasithin.Vol2.KGFact1297Red

public section

namespace CFSG.Quasithin.H13.KG1297

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.QuasithinUnique.Vol2Native.L239.L52 CFSG.Quasithin.SLnTwo
open scoped Pointwise

theorem exists_conj_sylow {G : Type*} [Group G] [Finite G] {P : Subgroup G} (T T' : Sylow 2 G)
    (hT : (T : Subgroup G) ≤ P) (hT' : (T' : Subgroup G) ≤ P) :
    ∃ g ∈ P, (T : Subgroup G).map (MulAut.conj g).toMonoidHom = T' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥P (T.subtype hT) (T'.subtype hT')
  rw [Sylow.smul_subtype] at hg
  have h := Sylow.subtype_injective hg
  refine ⟨g, g.2, ?_⟩
  rw [← h]
  apply SetLike.coe_injective
  rw [Subgroup.coe_map]
  rfl

theorem map_conj_self {G : Type*} [Group G] {P : Subgroup G} {g : G} (hg : g ∈ P) :
    P.map (MulAut.conj g).toMonoidHom = P := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact P.mul_mem (P.mul_mem hg hx) (P.inv_mem hg)
  · intro x hx
    refine ⟨g⁻¹ * x * g, P.mul_mem (P.mul_mem (P.inv_mem hg) hx) hg, ?_⟩
    show g * (g⁻¹ * x * g) * g⁻¹ = x
    group

theorem latHyp_of_unitriangular {n : ℕ} (hn : 1 ≤ n)
    {P : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))} {m : ℕ}
    (hUP : unitriangular n (ZMod 2) ≤ P)
    (h : ∀ Y : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2)), unitriangular n (ZMod 2) ≤ Y →
      ¬ Y ≤ P → NoE9 Y → (P ⊓ Y).relIndex P = 2 ^ m - 1 → LatOut P Y m) : LatHyp P m := by
  intro T Y hTP hTY hYP hY hidx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U₀, hU₀⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 (n := n) hn
  obtain ⟨g, hgP, hg⟩ := exists_conj_sylow T U₀ hTP (hU₀ ▸ hUP)
  set c := MulAut.conj g with hc
  have hcP := map_conj_self (P := P) hgP
  have hinj : Function.Injective (c.toMonoidHom : _ → _) := c.injective
  apply LatOut.of_map c
  rw [hcP]
  refine h (Y.map c.toMonoidHom) ?_ ?_ (noE9_map c hY) ?_
  · rw [← hU₀, ← hg]
    exact Subgroup.map_mono hTY
  · rwa [← hcP, Subgroup.map_le_map_iff_of_injective hinj]
  · conv_lhs => rw [← hcP]
    rw [← Subgroup.map_inf_eq _ _ _ hinj, Subgroup.relIndex_map_map_of_injective _ _ hinj, hidx]

theorem unitriangular_le_flag {n : ℕ} (J : Set ℕ) :
    unitriangular n (ZMod 2) ≤ flagStabilizer n (ZMod 2) J := by
  rw [← BinaryParabolic.upperTriangular_eq_unitriangular]
  exact upperTriangular_le_flagStabilizer J

@[expose] noncomputable def omg {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    SpecialLinearGroup (Fin n) (ZMod 2) :=
  SpecialLinearGroup.transvection hij.symm 1 * SpecialLinearGroup.transvection hij 1

theorem omg_mem {n : ℕ} {J : Set ℕ} {i j : Fin n} (hij : (i : ℕ) = j + 1) (hJ : (i : ℕ) ∉ J) :
    omg i j (fun h => by rw [h] at hij; omega) ∈ flagStabilizer n (ZMod 2) J :=
  Subgroup.mul_mem _ (transvection_mem_flagStabilizer (by
    show (j : ℕ) < i
    omega) 1 J) (lowTv_mem hij hJ)

theorem small_of_all {n : ℕ} {J : Set ℕ} (hJ : ∀ i, 1 ≤ i → i < n → i ∈ J) :
    ∀ a m : ℕ, a + m ≤ n → (a = 0 ∨ a ∈ J) → (a + m = n ∨ a + m ∈ J) →
      (∀ c ∈ J, ¬ (a < c ∧ c < a + m)) → m ≤ 1 := by
  intro a m h _ _ hno
  by_contra hm
  exact hno (a + 1) (hJ _ (by omega) (by omega)) ⟨by omega, by omega⟩

theorem card_GL_le_one_not_dvd_three {m : ℕ} (hm : m ≤ 1) :
    ¬ 3 ∣ Nat.card (GL (Fin m) (ZMod 2)) := by
  rw [card_GL_small (by omega)]
  interval_cases m <;> decide

theorem card_GL_le_two_not_dvd_seven {m : ℕ} (hm : m ≤ 2) :
    ¬ 7 ∣ Nat.card (GL (Fin m) (ZMod 2)) := by
  rw [card_GL_small (by omega)]
  interval_cases m <;> decide

theorem card_eq_relIndex_mul {G : Type*} [Group G] (B Y : Subgroup G) :
    Nat.card B = (B ⊓ Y).relIndex B * Nat.card ↥(B ⊓ Y) := by
  rw [← Subgroup.relIndex_mul_card (H := B ⊓ Y) (K := B), inf_eq_left.2 inf_le_left]

theorem modO2_congr {G : Type} [Group G] {H H' : Subgroup G} (h : H = H') :
    Nonempty (ModO2 H ≃* ModO2 H') := by
  subst h
  exact ⟨MulEquiv.refl _⟩

theorem card_modO2_dvd {G : Type} [Group G] (B : Subgroup G) :
    Nat.card (ModO2 B) ∣ Nat.card B :=
  Subgroup.card_quotient_dvd_card _

theorem exists_orderOf_of_dvd {G : Type} [Group G] [Finite G] {B Y : Subgroup G} {p k : ℕ}
    (hp : p.Prime) (hidx : (B ⊓ Y).relIndex B = k) (hpk : ¬ p ∣ k) (hpB : p ∣ Nat.card B) :
    ∃ x ∈ B ⊓ Y, orderOf x = p := by
  have : Fact p.Prime := ⟨hp⟩
  rw [card_eq_relIndex_mul B Y, hidx] at hpB
  have h := (Nat.Prime.dvd_mul hp).1 hpB
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(B ⊓ Y)) p (h.resolve_left hpk)
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe, hx]⟩

local notation "SL₄" => SpecialLinearGroup (Fin 4) (ZMod 2)
local notation "SL₅" => SpecialLinearGroup (Fin 5) (ZMod 2)

theorem modO2_four_one :
    Nonempty (ModO2 (flagStabilizer 4 (ZMod 2) {1}) ≃* SpecialLinearGroup (Fin 3) (ZMod 2)) :=
  modO2_flag (a := 1) (by norm_num) (Or.inr rfl) (Or.inl rfl) (fun c hc => by
    rw [Set.mem_singleton_iff] at hc; omega) le_rfl (fun a' m' h' ha' hb' hno' => by
    have h1 := hno' 1 rfl
    rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb' <;>
      (try simp only [Set.mem_singleton_iff] at ha' hb') <;> omega)

theorem modO2_four_three :
    Nonempty (ModO2 (flagStabilizer 4 (ZMod 2) {3}) ≃* SpecialLinearGroup (Fin 3) (ZMod 2)) :=
  modO2_flag (a := 0) (by norm_num) (Or.inl rfl) (Or.inr rfl) (fun c hc => by
    rw [Set.mem_singleton_iff] at hc; omega) le_rfl (fun a' m' h' ha' hb' hno' => by
    have h1 := hno' 3 rfl
    rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb' <;>
      (try simp only [Set.mem_singleton_iff] at ha' hb') <;> omega)

theorem modO2_four_empty :
    Nonempty (ModO2 (flagStabilizer 4 (ZMod 2) ∅) ≃* SpecialLinearGroup (Fin 4) (ZMod 2)) :=
  modO2_flag (a := 0) (by norm_num) (Or.inl rfl) (Or.inl rfl) (fun c hc => hc.elim)
    (by norm_num) (fun a' m' h' ha' hb' _ => by
      rcases ha' with ha' | ha'
      · rcases hb' with hb' | hb'
        · omega
        · exact hb'.elim
      · exact ha'.elim)

theorem latOut_four (Y : Subgroup SL₄) (hU : unitriangular 4 (ZMod 2) ≤ Y)
    (hYB : ¬ Y ≤ flagStabilizer 4 (ZMod 2) {1}) (hY : NoE9 Y)
    (hidx : (flagStabilizer 4 (ZMod 2) {1} ⊓ Y).relIndex (flagStabilizer 4 (ZMod 2) {1}) = 7) :
    LatOut (flagStabilizer 4 (ZMod 2) {1}) Y 3 := by
  obtain ⟨J, hJ, rfl⟩ := exists_eq_flagStabilizer hU
  have h1 : 1 ∉ J := fun h => hYB (flagStabilizer_anti (Set.singleton_subset_iff.2 h))
  have h3 : 3 ∈ J := by
    by_contra h3
    refine not_noE9 (a := omg (1 : Fin 4) 0 (by decide)) (b := omg (3 : Fin 4) 2 (by decide))
      (omg_mem (by decide) h1) (omg_mem (by decide) h3) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hY
  have h2 : 2 ∉ J := by
    intro h2
    have hB3 : 3 ∣ Nat.card (flagStabilizer 4 (ZMod 2) {1}) := by
      obtain ⟨e⟩ := modO2_four_one
      refine Dvd.dvd.trans ?_ (card_modO2_dvd _)
      rw [Nat.card_congr e.toEquiv, card_SL_eq (by norm_num), Nat.card_zmod]
      decide
    obtain ⟨x, hx, hxo⟩ := exists_orderOf_of_dvd Nat.prime_three hidx (by decide) hB3
    rw [flagStabilizer_inf] at hx
    refine orderOf_ne_of_small (by norm_num) Nat.prime_three (by decide) (k := 1) ?_
      (fun m hm => card_GL_le_one_not_dvd_three hm) hx hxo
    refine small_of_all fun i hi hin => ?_
    interval_cases i
    · exact Or.inl rfl
    · exact Or.inr h2
    · exact Or.inr h3
  have hJ3 : J = {3} := by
    ext i
    rw [Set.mem_singleton_iff]
    constructor
    · intro hi
      obtain ⟨hi1, hi4⟩ := hJ i hi
      interval_cases i
      · exact absurd hi h1
      · exact absurd hi h2
      · rfl
    · rintro rfl
      exact h3
  subst hJ3
  have hsup : flagStabilizer 4 (ZMod 2) {1} ⊔ flagStabilizer 4 (ZMod 2) {3} =
      flagStabilizer 4 (ZMod 2) ∅ := by
    rw [flagStabilizer_sup]
    congr 1
    ext i
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    omega
  refine ⟨rfl, modO2_four_three, Or.inr ?_, ?_⟩
  · obtain ⟨e1⟩ := modO2_congr hsup
    obtain ⟨e2⟩ := modO2_four_empty
    exact ⟨e1.trans e2⟩
  · rw [hsup]
    refine ⟨lt_of_le_of_ne (flagStabilizer_anti (Set.empty_subset _)) fun h => ?_, ?_⟩
    · have := subset_of_flagStabilizer_le (I := {3}) (J := ∅) (n := 4)
        (fun i hi => by rw [Set.mem_singleton_iff] at hi; omega) h.ge
      exact (this rfl).elim
    · intro W hW _
      have hUW : unitriangular 4 (ZMod 2) ≤ W :=
        (unitriangular_le_flag {3}).trans hW.le
      obtain ⟨J', hJ', rfl⟩ := exists_eq_flagStabilizer hUW
      have hsub := subset_of_flagStabilizer_le hJ' hW.le
      rcases Set.subset_singleton_iff_eq.1 hsub with h | h
      · rw [h]
      · exact absurd (by rw [h]) hW.ne

theorem latOut_five_four (Y : Subgroup SL₅) (hU : unitriangular 5 (ZMod 2) ≤ Y)
    (hYB : ¬ Y ≤ flagStabilizer 5 (ZMod 2) {1}) (hY : NoE9 Y)
    (hB7 : 7 ∣ Nat.card (flagStabilizer 5 (ZMod 2) {1}))
    (hidx : (flagStabilizer 5 (ZMod 2) {1} ⊓ Y).relIndex (flagStabilizer 5 (ZMod 2) {1}) = 15) :
    False := by
  obtain ⟨J, hJ, rfl⟩ := exists_eq_flagStabilizer hU
  have h1 : 1 ∉ J := fun h => hYB (flagStabilizer_anti (Set.singleton_subset_iff.2 h))
  have h3 : 3 ∈ J := by
    by_contra h3
    refine not_noE9 (a := omg (1 : Fin 5) 0 (by decide)) (b := omg (3 : Fin 5) 2 (by decide))
      (omg_mem (by decide) h1) (omg_mem (by decide) h3) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hY
  have h4 : 4 ∈ J := by
    by_contra h4
    refine not_noE9 (a := omg (1 : Fin 5) 0 (by decide)) (b := omg (4 : Fin 5) 3 (by decide))
      (omg_mem (by decide) h1) (omg_mem (by decide) h4) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hY
  obtain ⟨x, hx, hxo⟩ := exists_orderOf_of_dvd (by norm_num : Nat.Prime 7) hidx (by decide) hB7
  rw [flagStabilizer_inf] at hx
  refine orderOf_ne_of_small (by norm_num) (by norm_num : Nat.Prime 7) (by decide) (k := 2) ?_
    (fun m hm => card_GL_le_two_not_dvd_seven hm) hx hxo
  intro a m h ha hb hno
  have c1 := hno 1 (Or.inl rfl)
  have c3 := hno 3 (Or.inr h3)
  have c4 := hno 4 (Or.inr h4)
  omega

theorem modO2_five_12 :
    Nonempty (ModO2 (flagStabilizer 5 (ZMod 2) {1, 2}) ≃* SpecialLinearGroup (Fin 3) (ZMod 2)) :=
  modO2_flag (a := 2) (by norm_num) (Or.inr (by simp)) (Or.inl rfl) (fun c hc => by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc; omega) le_rfl
    (fun a' m' h' ha' hb' hno' => by
      have c1 := hno' 1 (by simp)
      have c2 := hno' 2 (by simp)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha' hb'
      omega)

theorem modO2_five_34 :
    Nonempty (ModO2 (flagStabilizer 5 (ZMod 2) {3, 4}) ≃* SpecialLinearGroup (Fin 3) (ZMod 2)) :=
  modO2_flag (a := 0) (by norm_num) (Or.inl rfl) (Or.inr (by simp)) (fun c hc => by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc; omega) le_rfl
    (fun a' m' h' ha' hb' hno' => by
      have c3 := hno' 3 (by simp)
      have c4 := hno' 4 (by simp)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha' hb'
      omega)

theorem modO2_five_1 :
    Nonempty (ModO2 (flagStabilizer 5 (ZMod 2) {1}) ≃* SpecialLinearGroup (Fin 4) (ZMod 2)) :=
  modO2_flag (a := 1) (by norm_num) (Or.inr rfl) (Or.inl rfl) (fun c hc => by
    rw [Set.mem_singleton_iff] at hc; omega) (by norm_num) (fun a' m' h' ha' hb' hno' => by
    have c1 := hno' 1 rfl
    rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb' <;>
      (try simp only [Set.mem_singleton_iff] at ha' hb') <;> omega)

theorem modO2_five_4 :
    Nonempty (ModO2 (flagStabilizer 5 (ZMod 2) {4}) ≃* SpecialLinearGroup (Fin 4) (ZMod 2)) :=
  modO2_flag (a := 0) (by norm_num) (Or.inl rfl) (Or.inr rfl) (fun c hc => by
    rw [Set.mem_singleton_iff] at hc; omega) (by norm_num) (fun a' m' h' ha' hb' hno' => by
    have c4 := hno' 4 rfl
    rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb' <;>
      (try simp only [Set.mem_singleton_iff] at ha' hb') <;> omega)

theorem isMax_flag {n : ℕ} {I J : Set ℕ} {j : ℕ} (hJ : ∀ i ∈ J, 1 ≤ i ∧ i < n) (hj : j ∈ J)
    (hIJ : I = J \ {j}) :
    IsMaxSubgroupIn (flagStabilizer n (ZMod 2) I) (flagStabilizer n (ZMod 2) J) := by
  have hIsub : I ⊆ J := hIJ ▸ Set.sdiff_subset
  have hI : ∀ i ∈ I, 1 ≤ i ∧ i < n := fun i hi => hJ i (hIsub hi)
  refine ⟨lt_of_le_of_ne (flagStabilizer_anti hIsub) fun h => ?_, fun W hW hWI => ?_⟩
  · have := subset_of_flagStabilizer_le hJ h.ge
    have hjI := this hj
    rw [hIJ] at hjI
    exact hjI.2 rfl
  · have hUW : unitriangular n (ZMod 2) ≤ W := (unitriangular_le_flag J).trans hW.le
    obtain ⟨J', hJ', rfl⟩ := exists_eq_flagStabilizer hUW
    have h1 := subset_of_flagStabilizer_le hJ' hW.le
    have h2 := subset_of_flagStabilizer_le hI hWI
    congr 1
    by_cases hjJ' : j ∈ J'
    · exfalso
      apply hW.ne
      congr 1
      ext i
      refine ⟨fun hi => ?_, fun hi => h1 hi⟩
      by_cases hij : i = j
      · rw [hij]
        exact hjJ'
      · exact h2 (by rw [hIJ]; exact ⟨hi, hij⟩)
    · ext i
      refine ⟨fun hi => ?_, fun hi => h2 hi⟩
      rw [hIJ]
      exact ⟨h1 hi, fun hij => hjJ' (hij ▸ hi)⟩

theorem latOut_five_three (Y : Subgroup SL₅) (hU : unitriangular 5 (ZMod 2) ≤ Y)
    (hYB : ¬ Y ≤ flagStabilizer 5 (ZMod 2) {1, 4}) (hY : NoE9 Y)
    (hidx : (flagStabilizer 5 (ZMod 2) {1, 4} ⊓ Y).relIndex (flagStabilizer 5 (ZMod 2) {1, 4}) =
      7) :
    LatOut (flagStabilizer 5 (ZMod 2) {1, 4}) Y 3 := by
  obtain ⟨J, hJ, rfl⟩ := exists_eq_flagStabilizer hU
  have h14 : ¬ (1 ∈ J ∧ 4 ∈ J) := fun ⟨h1, h4⟩ => hYB (flagStabilizer_anti (by
    intro i hi
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    rcases hi with rfl | rfl
    · exact h1
    · exact h4))
  have e1 : ¬ (1 ∉ J ∧ 4 ∉ J) := fun ⟨h1, h4⟩ =>
    not_noE9 (a := omg (1 : Fin 5) 0 (by decide)) (b := omg (4 : Fin 5) 3 (by decide))
      (omg_mem (by decide) h1) (omg_mem (by decide) h4) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hY
  have e2 : ¬ (1 ∉ J ∧ 3 ∉ J) := fun ⟨h1, h3⟩ =>
    not_noE9 (a := omg (1 : Fin 5) 0 (by decide)) (b := omg (3 : Fin 5) 2 (by decide))
      (omg_mem (by decide) h1) (omg_mem (by decide) h3) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hY
  have e3 : ¬ (2 ∉ J ∧ 4 ∉ J) := fun ⟨h2, h4⟩ =>
    not_noE9 (a := omg (2 : Fin 5) 1 (by decide)) (b := omg (4 : Fin 5) 3 (by decide))
      (omg_mem (by decide) h2) (omg_mem (by decide) h4) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hY
  have hfull : ¬ (2 ∈ J ∧ 3 ∈ J) := by
    rintro ⟨h2, h3⟩
    have hB3 : 3 ∣ Nat.card (flagStabilizer 5 (ZMod 2) {1, 4}) := by
      rw [← KG1296.Ct_eq]
      refine Dvd.dvd.trans ?_ (Subgroup.card_dvd_of_surjective KG1296.qCt_surjective)
      rw [card_SL_eq (by norm_num), Nat.card_zmod]
      decide
    obtain ⟨x, hx, hxo⟩ := exists_orderOf_of_dvd Nat.prime_three hidx (by decide) hB3
    rw [flagStabilizer_inf] at hx
    refine orderOf_ne_of_small (by norm_num) Nat.prime_three (by decide) (k := 1) ?_
      (fun m hm => card_GL_le_one_not_dvd_three hm) hx hxo
    refine small_of_all fun i hi hin => ?_
    interval_cases i
    · exact Or.inl (by simp)
    · exact Or.inr h2
    · exact Or.inr h3
    · exact Or.inl (by simp)
  have hJeq : ∀ T : Set ℕ, (∀ i, 1 ≤ i → i < 5 → (i ∈ J ↔ i ∈ T)) → (∀ i ∈ T, 1 ≤ i ∧ i < 5) →
      J = T := by
    intro T hT hT'
    ext i
    constructor
    · intro hi
      obtain ⟨hi1, hi5⟩ := hJ i hi
      exact (hT i hi1 hi5).1 hi
    · intro hi
      obtain ⟨hi1, hi5⟩ := hT' i hi
      exact (hT i hi1 hi5).2 hi
  by_cases h1 : 1 ∈ J
  ·
    have h4 : 4 ∉ J := fun h4 => h14 ⟨h1, h4⟩
    have h2 : 2 ∈ J := by by_contra h2; exact e3 ⟨h2, h4⟩
    have h3 : 3 ∉ J := fun h3 => hfull ⟨h2, h3⟩
    have hJ12 : J = {1, 2} := hJeq _ (fun i hi1 hi5 => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      interval_cases i <;> simp [h1, h2, h3, h4]) (fun i hi => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi; omega)
    subst hJ12
    have hsup : flagStabilizer 5 (ZMod 2) {1, 4} ⊔ flagStabilizer 5 (ZMod 2) {1, 2} =
        flagStabilizer 5 (ZMod 2) {1} := by
      rw [flagStabilizer_sup]
      congr 1
      ext i
      simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
      omega
    refine ⟨rfl, modO2_five_12, Or.inr ?_, ?_⟩
    · obtain ⟨e1⟩ := modO2_congr hsup
      obtain ⟨e2⟩ := modO2_five_1
      exact ⟨e1.trans e2⟩
    · rw [hsup]
      exact isMax_flag (j := 2) (fun i hi => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi; omega) (by simp) (by
        ext i
        simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
        omega)
  ·
    have h4 : 4 ∈ J := by by_contra h4; exact e1 ⟨h1, h4⟩
    have h3 : 3 ∈ J := by by_contra h3; exact e2 ⟨h1, h3⟩
    have h2 : 2 ∉ J := fun h2 => hfull ⟨h2, h3⟩
    have hJ34 : J = {3, 4} := hJeq _ (fun i hi1 hi5 => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      interval_cases i <;> simp [h1, h2, h3, h4]) (fun i hi => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi; omega)
    subst hJ34
    have hsup : flagStabilizer 5 (ZMod 2) {1, 4} ⊔ flagStabilizer 5 (ZMod 2) {3, 4} =
        flagStabilizer 5 (ZMod 2) {4} := by
      rw [flagStabilizer_sup]
      congr 1
      ext i
      simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
      omega
    refine ⟨rfl, modO2_five_34, Or.inr ?_, ?_⟩
    · obtain ⟨e1⟩ := modO2_congr hsup
      obtain ⟨e2⟩ := modO2_five_4
      exact ⟨e1.trans e2⟩
    · rw [hsup]
      exact isMax_flag (j := 3) (fun i hi => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi; omega) (by simp) (by
        ext i
        simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
        omega)

theorem latHyp_four_Pone : LatHyp (flagStabilizer 4 (ZMod 2) {1}) 3 :=
  latHyp_of_unitriangular (by norm_num) (unitriangular_le_flag _)
    fun Y hU hYB hY hidx => latOut_four Y hU hYB hY hidx

theorem latHyp_five_Pone : LatHyp (flagStabilizer 5 (ZMod 2) {1}) 4 := by
  refine latHyp_of_unitriangular (by norm_num) (unitriangular_le_flag _)
    fun Y hU hYB hY hidx => (latOut_five_four Y hU hYB hY ?_ hidx).elim
  obtain ⟨e⟩ := modO2_five_1
  refine Dvd.dvd.trans ?_ (card_modO2_dvd _)
  rw [Nat.card_congr e.toEquiv, card_SL_eq (by norm_num), Nat.card_zmod]
  decide

theorem latHyp_Ct : LatHyp KG1296.Ct 3 := by
  refine latHyp_of_unitriangular (by norm_num) (KG1296.Ct_eq ▸ unitriangular_le_flag _)
    fun Y hU hYB hY hidx => ?_
  rw [KG1296.Ct_eq] at hYB hidx ⊢
  exact latOut_five_three Y hU hYB hY hidx

theorem latHyp_of_eq_map {M : Type} [Group M] [Finite M] {B B₀ : Subgroup M} {m : ℕ}
    (ι : M ≃* M) (hB : B = B₀.map ι.toMonoidHom) (h : LatHyp B₀ m) : LatHyp B m := by
  refine LatHyp.of_map ι.symm ?_
  have : B.map ι.symm.toMonoidHom = B₀ := by
    rw [hB, Subgroup.map_map]
    convert Subgroup.map_id B₀
    ext x
    simp
  rw [this]
  exact h

theorem latHyp_four {B : Subgroup SL₄}
    (hB : Nonempty (ModO2 B ≃* SpecialLinearGroup (Fin 3) (ZMod 2))) : LatHyp B 3 := by
  intro T Y hTB
  obtain ⟨ι, hι⟩ := KG1296.exists_mulAut_Pone (k := 3) (Or.inl rfl) T
    (hTB.trans Subgroup.le_normalizer) hB
  exact latHyp_of_eq_map ι hι latHyp_four_Pone T Y hTB

theorem latHyp_five {B : Subgroup SL₅}
    (hB : Nonempty (ModO2 B ≃* SpecialLinearGroup (Fin 4) (ZMod 2))) : LatHyp B 4 := by
  intro T Y hTB
  obtain ⟨ι, hι⟩ := KG1296.exists_mulAut_Pone (k := 4) (Or.inr rfl) T
    (hTB.trans Subgroup.le_normalizer) hB
  exact latHyp_of_eq_map ι hι latHyp_five_Pone T Y hTB

theorem latHyp_four_top {B : Subgroup SL₄}
    (hB : Nonempty (ModO2 B ≃* SpecialLinearGroup (Fin 4) (ZMod 2))) : LatHyp B 4 := by
  intro T Y _ _ hYB
  rw [KG1296.eq_top_of_modO2_SL4 hB] at hYB
  exact absurd le_top hYB

end CFSG.Quasithin.H13.KG1297
