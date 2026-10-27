
module

public import CFSG.LocalAnalysis.StandardType.L34SylowOvergroupBase
public import CFSG.Certificates.SuborbitCoatom
public import CFSG.Certificates.Kernel.L34Syl.Group
public import Certificates.Certificate465003Base
public import CFSG.Certificates.Kernel.Spor.PK.Perm.Inv

public section

namespace CFSG.StandardType.L34Sylow

open CFSG.PSL3Four.Native
open scoped Pointwise

theorem exists_le_of_sylow_records {G : Type*} [Group G] {S P Z : Subgroup G} [Finite S]
    {ℓ N : ℕ} [Fact ℓ.Prime] {T : Subgroup G → Prop} (hS : Nat.card S = ℓ * N)
    (hℓN : ¬ ℓ ∣ N) (L : List G) (hLS : ∀ X ∈ L, X ∈ S ∧ X ≠ 1 ∧ X ^ ℓ = 1)
    (hnd : L.Pairwise fun X Y => Subgroup.zpowers X ≠ Subgroup.zpowers Y)
    (hcount : Nat.card (Sylow ℓ S) ≤ L.length)
    (hrep : ∀ X ∈ L, ∃ c ∈ P, ∃ r : G, r ^ ℓ = 1 ∧ c⁻¹ * X * c ∈ Subgroup.zpowers r ∧
      T (P ⊔ Subgroup.zpowers r))
    (hPZ : P ≤ Z) (hZS : Z ≤ S) (hx : ∃ x ∈ Z, x ≠ 1 ∧ x ^ ℓ = 1) :
    ∃ Y, T Y ∧ Y ≤ Z := by
  obtain ⟨x, hxZ, hx1, hxl⟩ := hx
  obtain ⟨X, hXL, hXx⟩ := CFSG.KC.L34Syl.exists_mem_zpowers_eq S hS hℓN L
    (fun X hX => ⟨(hLS X hX).1, orderOf_eq_prime (hLS X hX).2.2 (hLS X hX).2.1⟩) hnd hcount
    (hZS hxZ) (orderOf_eq_prime hxl hx1)
  have hXZ : X ∈ Z := by
    have hXx' : X ∈ Subgroup.zpowers x := by
      rw [← hXx]
      exact Subgroup.mem_zpowers _
    exact (Subgroup.zpowers_le.mpr hxZ) hXx'
  obtain ⟨-, hX1, hXl⟩ := hLS X hXL
  obtain ⟨c, hcP, r, hrl, hcr, hT⟩ := hrep X hXL
  have hyZ : c⁻¹ * X * c ∈ Z := mul_mem (mul_mem (inv_mem (hPZ hcP)) hXZ) (hPZ hcP)
  have hy1 : c⁻¹ * X * c ≠ 1 := by
    intro h
    apply hX1
    have e : X = c * (c⁻¹ * X * c) * c⁻¹ := by group
    rw [e, h]
    group
  have hyl : (c⁻¹ * X * c) ^ ℓ = 1 := by
    have e : c⁻¹ * X * c = c⁻¹ * X * c⁻¹⁻¹ := by rw [inv_inv]
    rw [e, conj_pow, hXl]
    group
  have hr1 : r ≠ 1 := by
    rintro rfl
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hcr
    exact hy1 hcr
  have hrfin : Finite (Subgroup.zpowers r) := Nat.finite_of_card_ne_zero (by
    rw [Nat.card_zpowers, orderOf_eq_prime hrl hr1]
    exact (Fact.out : ℓ.Prime).ne_zero)
  have hyr : Subgroup.zpowers (c⁻¹ * X * c) = Subgroup.zpowers r := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcr)
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hrl hr1, orderOf_eq_prime hyl hy1]
  have hrZ : r ∈ Z := by
    have hr : r ∈ Subgroup.zpowers (c⁻¹ * X * c) := by
      rw [hyr]
      exact Subgroup.mem_zpowers r
    exact (Subgroup.zpowers_le.mpr hyZ) hr
  exact ⟨_, hT, sup_le hPZ (Subgroup.zpowers_le.mpr hrZ)⟩

theorem aSix_of_suborbits {α : Type} [DecidableEq α] {S M : Subgroup (Equiv.Perm α)}
    (hcardS : Nat.card S = 20160) (hMS : M ≤ S) (o : Fin 6 → α) (ho : Function.Injective o)
    (hMH : ∀ m ∈ M, ⇑m '' Set.range o = Set.range o) (Q : Subgroup (Equiv.Perm (Fin 6)))
    (hQ : 360 ≤ Nat.card Q) (hreal : ∀ τ ∈ Q, ∃ m ∈ M, ∀ i, m (o i) = o (τ i))
    (hperf : M ≤ ⁅M, M⁆) (B : Fin 3 → Set (Set α))
    (hB0 : B 0 = {Set.range o})
    (hBorb : ∀ c, ∀ y ∈ B c, ∃ g ∈ S, ⇑g '' Set.range o = y)
    (hcover : ∀ g ∈ S, ∃ c, ⇑g '' Set.range o ∈ B c)
    (hdisj : ∀ c d, c ≠ d → Disjoint (B c) (B d))
    (htrans : ∀ c, ∀ y ∈ B c, ∀ z ∈ B c, ∃ m ∈ M, ⇑m '' y = z)
    (hB12 : ((B 1).ncard = 10 ∧ (B 2).ncard = 45) ∨ ((B 1).ncard = 45 ∧ (B 2).ncard = 10)) :
    Nat.card M = 360 ∧ commutator ↥M = ⊤ ∧ Nonempty (↥M ≃* alternatingGroup (Fin 6)) ∧
      ∀ Z : Subgroup (Equiv.Perm α), M ≤ Z → Z ≤ S → Z = M ∨ Z = S := by
  classical
  set H : Set α := Set.range o with hH
  have hSfin : Finite S := Nat.finite_of_card_ne_zero (by rw [hcardS]; norm_num)
  have hstab : ∀ m ∈ M, ∀ i, ∃ j, m (o i) = o j := by
    intro m hm i
    have h : m (o i) ∈ ⇑m '' H := Set.mem_image_of_mem _ ⟨i, rfl⟩
    rw [hMH m hm] at h
    obtain ⟨j, hj⟩ := h
    exact ⟨j, hj.symm⟩
  set K : Subgroup ↥S := MulAction.stabilizer (↥S) H with hK
  set M' : Subgroup ↥S := M.subgroupOf S with hM'
  have hM'K : M' ≤ K := by
    intro m hm
    rw [hK, MulAction.mem_stabilizer_iff]
    exact hMH m (Subgroup.mem_subgroupOf.mp hm)
  have horb : ∀ y, y ∈ MulAction.orbit (↥S) H ↔ ∃ c, y ∈ B c := by
    intro y
    constructor
    · rintro ⟨g, rfl⟩
      exact hcover g g.2
    · rintro ⟨c, hc⟩
      obtain ⟨g, hg, rfl⟩ := hBorb c y hc
      exact ⟨⟨g, hg⟩, rfl⟩
  have hBorb' : ∀ c, B c ⊆ MulAction.orbit (↥S) H := fun c y hy => (horb y).2 ⟨c, hy⟩
  have hcover' : ∀ y ∈ MulAction.orbit (↥S) H, ∃ c, y ∈ B c := fun y hy => (horb y).1 hy
  have hfin : ∀ c, (B c).Finite := fun c => (Set.finite_range _).subset (hBorb' c)
  have hB0c : (B 0).ncard = 1 := by rw [hB0, Set.ncard_singleton]
  have hB12s : (B 1).ncard + (B 2).ncard = 55 := by omega
  have hunion : MulAction.orbit (↥S) H = B 0 ∪ B 1 ∪ B 2 := by
    ext y
    rw [horb]
    constructor
    · rintro ⟨c, hc⟩
      fin_cases c
      · exact Or.inl (Or.inl hc)
      · exact Or.inl (Or.inr hc)
      · exact Or.inr hc
    · rintro ((h | h) | h)
      · exact ⟨_, h⟩
      · exact ⟨_, h⟩
      · exact ⟨_, h⟩
  have horb56 : (MulAction.orbit (↥S) H).ncard = 56 := by
    rw [hunion, Set.ncard_union_eq _ ((hfin 0).union (hfin 1)) (hfin 2),
      Set.ncard_union_eq (hdisj 0 1 (by decide)) (hfin 0) (hfin 1), hB0c]
    · omega
    · exact Set.disjoint_union_left.mpr ⟨hdisj 0 2 (by decide), hdisj 1 2 (by decide)⟩
  have hKcard : Nat.card K = 360 := by
    have h1 := (MulAction.stabilizer (↥S) H).card_mul_index
    rw [MulAction.index_stabilizer, horb56, hcardS] at h1
    rw [hK]
    omega
  have hMcard : Nat.card M' = Nat.card M :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMS).toEquiv
  choose! g hgM hg using hreal
  let g' : ↥Q → ↥M := fun τ => ⟨g τ.1, hgM τ.1 τ.2⟩
  have hg'inj : Function.Injective g' := by
    intro τ σ h
    have h' : g τ.1 = g σ.1 := congrArg Subtype.val h
    apply Subtype.ext
    refine Equiv.ext fun i => ho ?_
    rw [← hg τ.1 τ.2 i, ← hg σ.1 σ.2 i, h']
  have hMfin : Finite ↥M := Finite.of_injective (fun m : ↥M => (⟨m, hMS m.2⟩ : ↥S))
    (fun a b h => Subtype.ext (Subtype.mk.inj h))
  have hMge : 360 ≤ Nat.card ↥M := by
    have := Nat.card_le_card_of_injective g' hg'inj
    omega
  have hMK : M' = K :=
    Subgroup.eq_of_le_of_card_ge hM'K (by rw [hKcard, hMcard]; exact hMge)
  have hM360 : Nat.card ↥M = 360 := by rw [← hMcard, hMK, hKcard]
  have hg'bij : Function.Bijective g' := hg'inj.bijective_of_nat_card_le (by omega)
  have hfaith : ∀ m ∈ M, (∀ i, m (o i) = o i) → m = 1 := by
    have hfix : ∀ τ : ↥Q, (∀ i, g τ.1 (o i) = o i) → τ.1 = 1 := by
      intro τ h
      refine Equiv.ext fun i => ho ?_
      rw [← hg τ.1 τ.2 i, h i, Equiv.Perm.one_apply]
    intro m hm h
    obtain ⟨τ, hτ⟩ := hg'bij.2 ⟨m, hm⟩
    obtain ⟨σ, hσ⟩ := hg'bij.2 1
    have hτm : g τ.1 = m := congrArg Subtype.val hτ
    have hσ1 : g σ.1 = 1 := congrArg Subtype.val hσ
    have hτ1 : τ.1 = 1 := hfix τ (by rw [hτm]; exact h)
    have hσ1' : σ.1 = 1 := hfix σ (by rw [hσ1]; exact fun i => rfl)
    rw [← hτm, hτ1, ← hσ1', hσ1]
  have hcomm : ⁅M, M⁆ = M :=
    le_antisymm (M.map_subtype_commutator ▸ Subgroup.map_subtype_le _) hperf
  have hperf' : commutator ↥M = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    calc Nat.card (commutator ↥M)
        = Nat.card ((commutator ↥M).map M.subtype) :=
          (Subgroup.card_map_of_injective M.subtype_injective).symm
      _ = Nat.card ↥M := by rw [M.map_subtype_commutator, hcomm]
  have hprim : ∀ T : Finset (Fin 3), 0 ∈ T →
      (∑ c ∈ T, (B c).ncard) ∣ ∑ c, (B c).ncard → T = {0} ∨ T = Finset.univ := by
    rcases hB12 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hncard : ∀ c, (B c).ncard = (![1, 10, 45] : Fin 3 → ℕ) c := by
        intro c
        fin_cases c
        · exact hB0c
        · exact h1
        · exact h2
      have key : ∀ T : Finset (Fin 3), 0 ∈ T →
          (∑ c ∈ T, (![1, 10, 45] : Fin 3 → ℕ) c) ∣ ∑ c, (![1, 10, 45] : Fin 3 → ℕ) c →
          T = {0} ∨ T = Finset.univ := by decide
      intro T hT
      simp only [hncard]
      exact key T hT
    · have hncard : ∀ c, (B c).ncard = (![1, 45, 10] : Fin 3 → ℕ) c := by
        intro c
        fin_cases c
        · exact hB0c
        · exact h1
        · exact h2
      have key : ∀ T : Finset (Fin 3), 0 ∈ T →
          (∑ c ∈ T, (![1, 45, 10] : Fin 3 → ℕ) c) ∣ ∑ c, (![1, 45, 10] : Fin 3 → ℕ) c →
          T = {0} ∨ T = Finset.univ := by decide
      intro T hT
      simp only [hncard]
      exact key T hT
  have hcoat := CFSG.Certificates.isCoatom_stabilizer_of_suborbits (G := ↥S) H M' hM'K B hB0
    hBorb' hcover' hdisj
    (fun c y hy z hz => by
      obtain ⟨m, hm, hmz⟩ := htrans c y hy z hz
      exact ⟨⟨m, hMS hm⟩, Subgroup.mem_subgroupOf.mpr hm, hmz⟩)
    hprim
    ⟨1, by decide, Set.nonempty_of_ncard_ne_zero (by omega)⟩
  refine ⟨hM360, hperf',
    CFSG.StandardType.AltSix.nonempty_mulEquiv_alternatingGroup_fin_six M o ho hstab hfaith
      hperf' hM360, fun Z hMZ hZS => ?_⟩
  have hKZ : K ≤ Z.subgroupOf S := by
    rw [← hMK]
    intro m hm
    exact Subgroup.mem_subgroupOf.mpr (hMZ (Subgroup.mem_subgroupOf.mp hm))
  rcases hcoat.le_iff.mp hKZ with htop | heq
  · exact Or.inr (le_antisymm hZS (Subgroup.subgroupOf_eq_top.mp htop))
  · left
    have heq' : Z.subgroupOf S = M.subgroupOf S := by rw [heq, ← hK, ← hMK, hM']
    rwa [Subgroup.subgroupOf_inj, inf_of_le_left hZS, inf_of_le_left hMS] at heq'

theorem certificate465003_of_facts
    (hcardS : Nat.card ↥(closureTabs gensS) = 20160)
    (hP9 : Nat.card ↥(closureTabs pGens) = 9) (hPS : closureTabs pGens ≤ closureTabs gensS)
    (hM : ∀ j < 6, commutator ↥(closureTabs (pGensWith mRs[j]!)) = ⊤ ∧
      Nonempty (↥(closureTabs (pGensWith mRs[j]!)) ≃* alternatingGroup (Fin 6)) ∧
      ∀ Z : Subgroup (Equiv.Perm (Fin 42)), closureTabs (pGensWith mRs[j]!) ≤ Z →
        Z ≤ closureTabs gensS → Z = closureTabs (pGensWith mRs[j]!) ∨ Z = closureTabs gensS)
    (h5 : ∀ Z : Subgroup (Equiv.Perm (Fin 42)), closureTabs pGens ≤ Z →
      Z ≤ closureTabs gensS → (∃ x ∈ Z, x ≠ 1 ∧ x ^ 5 = 1) →
        closureTabs gensS ≤ Z ∨ ∃ j < 6, closureTabs (pGensWith mRs[j]!) ≤ Z)
    (h7 : ∀ Z : Subgroup (Equiv.Perm (Fin 42)), closureTabs pGens ≤ Z →
      Z ≤ closureTabs gensS → (∃ x ∈ Z, x ≠ 1 ∧ x ^ 7 = 1) → closureTabs gensS ≤ Z) :
    Certificates.Facts465003 where
  card_P := hP9
  P_le_S := hPS
  aSix j hj := ⟨(hM j hj).1, (hM j hj).2.1⟩
  trichotomy Z hPZ hZS := by
    by_cases hx5 : ∃ x ∈ Z, x ≠ 1 ∧ x ^ 5 = 1
    · rcases h5 Z hPZ hZS hx5 with h | ⟨j, hj, h⟩
      · exact Or.inl (le_antisymm hZS h)
      · rcases (hM j hj).2.2 Z h hZS with h' | h'
        · exact Or.inr (Or.inl ⟨j, hj, h'⟩)
        · exact Or.inl h'
    by_cases hx7 : ∃ x ∈ Z, x ≠ 1 ∧ x ^ 7 = 1
    · exact Or.inl (le_antisymm hZS (h7 Z hPZ hZS hx7))
    · exact Or.inr (Or.inr (isSolvable_of_no_order hcardS hZS hx5 hx7))
  seven Z hPZ hZS hx7 := le_antisymm hZS (h7 Z hPZ hZS hx7)

@[expose] def ASixData (S M : Subgroup (Equiv.Perm (Fin 42))) : Prop :=
  M ≤ S ∧ M ≤ ⁅M, M⁆ ∧ ∃ o : Fin 6 → Fin 42, Function.Injective o ∧
    (∀ m ∈ M, ⇑m '' Set.range o = Set.range o) ∧
    (∃ Q : Subgroup (Equiv.Perm (Fin 6)), 360 ≤ Nat.card Q ∧
      ∀ τ ∈ Q, ∃ m ∈ M, ∀ i, m (o i) = o (τ i)) ∧
    ∃ B : Fin 3 → Set (Set (Fin 42)), B 0 = {Set.range o} ∧
      (∀ c, ∀ y ∈ B c, ∃ g ∈ S, ⇑g '' Set.range o = y) ∧
      (∀ g ∈ S, ∃ c, ⇑g '' Set.range o ∈ B c) ∧
      (∀ c d, c ≠ d → Disjoint (B c) (B d)) ∧
      (∀ c, ∀ y ∈ B c, ∀ z ∈ B c, ∃ m ∈ M, ⇑m '' y = z) ∧
      (((B 1).ncard = 10 ∧ (B 2).ncard = 45) ∨ ((B 1).ncard = 45 ∧ (B 2).ncard = 10))

theorem certificate465003_of_lists
    (hcardS : Nat.card ↥(closureTabs gensS) = 20160)
    (hP9 : Nat.card ↥(closureTabs pGens) = 9) (hPS : closureTabs pGens ≤ closureTabs gensS)
    (hM : ∀ j < 6, ASixData (closureTabs gensS) (closureTabs (pGensWith mRs[j]!)))
    (L5 : List (Equiv.Perm (Fin 42))) (hlen5 : 2016 ≤ L5.length)
    (hL5 : ∀ X ∈ L5, X ∈ closureTabs gensS ∧ X ≠ 1 ∧ X ^ 5 = 1)
    (hnd5 : L5.Pairwise fun X Y => Subgroup.zpowers X ≠ Subgroup.zpowers Y)
    (hrep5 : ∀ X ∈ L5, ∃ c ∈ closureTabs pGens, ∃ r : Equiv.Perm (Fin 42), r ^ 5 = 1 ∧
      c⁻¹ * X * c ∈ Subgroup.zpowers r ∧
      (closureTabs gensS ≤ closureTabs pGens ⊔ Subgroup.zpowers r ∨
        ∃ j < 6, closureTabs (pGensWith mRs[j]!) ≤ closureTabs pGens ⊔ Subgroup.zpowers r))
    (L7 : List (Equiv.Perm (Fin 42))) (hlen7 : 960 ≤ L7.length)
    (hL7 : ∀ X ∈ L7, X ∈ closureTabs gensS ∧ X ≠ 1 ∧ X ^ 7 = 1)
    (hnd7 : L7.Pairwise fun X Y => Subgroup.zpowers X ≠ Subgroup.zpowers Y)
    (hrep7 : ∀ X ∈ L7, ∃ c ∈ closureTabs pGens, ∃ r : Equiv.Perm (Fin 42), r ^ 7 = 1 ∧
      c⁻¹ * X * c ∈ Subgroup.zpowers r ∧
      closureTabs gensS ≤ closureTabs pGens ⊔ Subgroup.zpowers r) :
    Certificates.Facts465003 := by
  have : Finite ↥(closureTabs gensS) := Nat.finite_of_card_ne_zero (by rw [hcardS]; norm_num)
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hc5 := CFSG.KC.L34Syl.card_sylow_five_le hcardS
  have hc7 := CFSG.KC.L34Syl.card_sylow_seven_le hcardS
  refine certificate465003_of_facts hcardS hP9 hPS (fun j hj => ?_) (fun Z hPZ hZS hx => ?_)
    (fun Z hPZ hZS hx => ?_)
  · obtain ⟨hMS, hperf, o, ho, hMH, ⟨Q, hQ, hreal⟩, B, hB0, hBorb, hcover, hdisj, htrans,
      hB12⟩ := hM j hj
    have h := aSix_of_suborbits hcardS hMS o ho hMH Q hQ hreal hperf B hB0 hBorb hcover hdisj
      htrans hB12
    exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩
  · obtain ⟨Y, hY, hYZ⟩ := exists_le_of_sylow_records (N := 4032)
      (T := fun Y => closureTabs gensS ≤ Y ∨ ∃ j < 6, closureTabs (pGensWith mRs[j]!) ≤ Y)
      (by rw [hcardS]) (by norm_num) L5 hL5 hnd5 (by omega) hrep5 hPZ hZS hx
    rcases hY with h | ⟨j, hj, h⟩
    · exact Or.inl (h.trans hYZ)
    · exact Or.inr ⟨j, hj, h.trans hYZ⟩
  · obtain ⟨Y, hY, hYZ⟩ := exists_le_of_sylow_records (N := 2880)
      (T := fun Y => closureTabs gensS ≤ Y) (by rw [hcardS]) (by norm_num) L7 hL7 hnd7
      (by omega) hrep7 hPZ hZS hx
    exact hY.trans hYZ

end CFSG.StandardType.L34Sylow
