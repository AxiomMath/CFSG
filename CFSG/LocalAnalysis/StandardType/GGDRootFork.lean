module

public import CFSG.LocalAnalysis.StandardType.GGResIClassify
public import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRootsPairs

public section

namespace CFSG.StandardType

def ggRootSupp {k : ℕ} (γ : Fin k → ℤ) : Finset (Fin k) :=
  Finset.univ.filter fun x => γ x ≠ 0

theorem ggRootSupp_mem {k : ℕ} {γ : Fin k → ℤ} {x : Fin k} :
    x ∈ ggRootSupp γ ↔ γ x ≠ 0 := by
  simp [ggRootSupp]

theorem ggRootSupp_card {k : ℕ} {γ : Fin k → ℤ} (hγ : γ ∈ ggDRootSet k) :
    (ggRootSupp γ).card = 2 := by
  obtain ⟨a, b, hab, ha, hb⟩ := ggDRootSet_exists_pair hγ
  have heq : ggRootSupp γ = {a, b} := by
    ext x
    rw [ggRootSupp_mem, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hx
      by_contra h
      push Not at h
      exact hx (ggDRootSet_eq_zero hγ hab ha hb h.1 h.2)
    · rintro (rfl | rfl)
      · exact ha
      · exact hb
  rw [heq]
  exact Finset.card_pair hab

theorem ggRootSupp_eq_pair {k : ℕ} {γ : Fin k → ℤ} (hγ : γ ∈ ggDRootSet k)
    {a b : Fin k} (hab : a ≠ b) (ha : γ a ≠ 0) (hb : γ b ≠ 0) :
    ggRootSupp γ = {a, b} := by
  have hsub : ({a, b} : Finset (Fin k)) ⊆ ggRootSupp γ := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [ggRootSupp_mem]
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  have hcard : (ggRootSupp γ).card = 2 := ggRootSupp_card hγ
  have hcardab : ({a, b} : Finset (Fin k)).card = 2 := Finset.card_pair hab
  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
  omega

theorem ggDDot_mem_range {k : ℕ} {γ δ : Fin k → ℤ} (hγ : γ ∈ ggDRootSet k)
    (hδ : δ ∈ ggDRootSet k) : -2 ≤ ggDDot γ δ ∧ ggDDot γ δ ≤ 2 := by
  obtain ⟨a, b, hab, ha, hb⟩ := ggDRootSet_exists_pair hγ
  have hγa := ggDRootSet_sign hγ ha
  have hγb := ggDRootSet_sign hγ hb
  have hδa := ggDRootSet_apply hδ a
  have hδb := ggDRootSet_apply hδ b
  rw [ggDRootSet_dot_eq hγ hab ha hb δ]
  rcases hγa with h1 | h1 <;> rcases hγb with h2 | h2 <;>
  rcases hδa with h3 | h3 | h3 <;> rcases hδb with h4 | h4 | h4 <;>
  rw [h1, h2, h3, h4] <;> norm_num

theorem ggDDot_eq_or_of_ggRootSupp_eq {k : ℕ} {γ δ : Fin k → ℤ}
    (hγ : γ ∈ ggDRootSet k) (hδ : δ ∈ ggDRootSet k)
    (h : ggRootSupp γ = ggRootSupp δ) :
    ggDDot γ δ = -2 ∨ ggDDot γ δ = 0 ∨ ggDDot γ δ = 2 := by
  obtain ⟨a, b, hab, ha, hb⟩ := ggDRootSet_exists_pair hγ
  have hδa : δ a ≠ 0 := by
    rw [← ggRootSupp_mem, ← h, ggRootSupp_mem]
    exact ha
  have hδb : δ b ≠ 0 := by
    rw [← ggRootSupp_mem, ← h, ggRootSupp_mem]
    exact hb
  have hγa := ggDRootSet_sign hγ ha
  have hγb := ggDRootSet_sign hγ hb
  have hδa' := ggDRootSet_sign hδ hδa
  have hδb' := ggDRootSet_sign hδ hδb
  rw [ggDRootSet_dot_eq hγ hab ha hb δ]
  rcases hγa with h1 | h1 <;> rcases hγb with h2 | h2 <;>
  rcases hδa' with h3 | h3 <;> rcases hδb' with h4 | h4 <;>
  rw [h1, h2, h3, h4] <;> norm_num

theorem ggDDot_eq_mul_of_shared {k : ℕ} {γ δ : Fin k → ℤ} (hγ : γ ∈ ggDRootSet k)
    (hδ : δ ∈ ggDRootSet k) {a b : Fin k} (hab : a ≠ b) (ha : γ a ≠ 0)
    (hb : γ b ≠ 0) (hδa : δ a ≠ 0) (hne : ggRootSupp γ ≠ ggRootSupp δ) :
    ggDDot γ δ = γ a * δ a := by
  have hsuppγ : ggRootSupp γ = {a, b} := ggRootSupp_eq_pair hγ hab ha hb
  have hδb : δ b = 0 := by
    by_contra hδb0
    have hsub : ({a, b} : Finset (Fin k)) ⊆ ggRootSupp δ := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [ggRootSupp_mem]
      rcases hx with rfl | rfl
      · exact hδa
      · exact hδb0
    have heq : ({a, b} : Finset (Fin k)) = ggRootSupp δ := by
      refine Finset.eq_of_subset_of_card_le hsub ?_
      rw [ggRootSupp_card hδ, Finset.card_pair hab]
    exact hne (by rw [hsuppγ, heq])
  rw [ggDRootSet_dot_eq hγ hab ha hb δ, hδb, mul_zero, add_zero]

theorem ggDDot_ne_zero_of_sameSupp_orth_pair {k : ℕ} {γ δ η : Fin k → ℤ}
    (hγ : γ ∈ ggDRootSet k) (hδ : δ ∈ ggDRootSet k) (hη : η ∈ ggDRootSet k)
    {x y : Fin k} (hxy : x ≠ y) (hγx : γ x ≠ 0) (hγy : γ y ≠ 0)
    (hδsupp : ggRootSupp δ = ggRootSupp γ) (hηsupp : ggRootSupp η = ggRootSupp γ)
    (hγδ : ggDDot γ δ = 0) (hηγ : ggDDot η γ = 0) :
    ggDDot η δ ≠ 0 := by
  have hδx : δ x ≠ 0 := by
    rw [← ggRootSupp_mem, hδsupp, ggRootSupp_mem]
    exact hγx
  have hδy : δ y ≠ 0 := by
    rw [← ggRootSupp_mem, hδsupp, ggRootSupp_mem]
    exact hγy
  have hηx : η x ≠ 0 := by
    rw [← ggRootSupp_mem, hηsupp, ggRootSupp_mem]
    exact hγx
  have hηy : η y ≠ 0 := by
    rw [← ggRootSupp_mem, hηsupp, ggRootSupp_mem]
    exact hγy
  have h1 : γ x * δ x + γ y * δ y = 0 := by
    have h := ggDRootSet_dot_eq hγ hxy hγx hγy δ
    rw [hγδ] at h
    exact h.symm
  have h2 : γ x * η x + γ y * η y = 0 := by
    have hcomm : ggDDot γ η = 0 := by rw [ggDDot_comm]; exact hηγ
    have h := ggDRootSet_dot_eq hγ hxy hγx hγy η
    rw [hcomm] at h
    exact h.symm
  have h3 : ggDDot δ η = δ x * η x + δ y * η y :=
    ggDRootSet_dot_eq hδ hxy hδx hδy η
  rw [ggDDot_comm η δ, h3]
  have hγx' := ggDRootSet_sign hγ hγx
  have hγy' := ggDRootSet_sign hγ hγy
  have hδx' := ggDRootSet_sign hδ hδx
  have hδy' := ggDRootSet_sign hδ hδy
  have hηx' := ggDRootSet_sign hη hηx
  have hηy' := ggDRootSet_sign hη hηy
  rcases hγx' with gx | gx <;> rcases hγy' with gy | gy <;>
  rcases hδx' with dx | dx <;> rcases hδy' with dy | dy <;>
  rcases hηx' with ex | ex <;> rcases hηy' with ey | ey <;>
  rw [gx, gy, dx, dy] at h1 <;> rw [gx, gy, ex, ey] at h2 <;>
  rw [dx, dy, ex, ey] <;> omega

theorem ggIntCartan_zero_iff {Λ : Type} {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    (hC : GGIntCartan M C) {i j : Λ} (hij : i ≠ j) : C i j = 0 ↔ M i j = 2 := by
  constructor
  · intro h0
    rcases hC.2 i j hij with ⟨hm, -, -⟩ | ⟨hm, h1, -⟩ | ⟨hm, h1, -, -⟩ | ⟨hm, h1, -, -⟩
    · exact hm
    · rw [h0] at h1
      omega
    · rw [h0, zero_mul] at h1
      omega
    · rw [h0, zero_mul] at h1
      omega
  · intro hm
    rcases hC.2 i j hij with ⟨-, h1, -⟩ | ⟨h3, h1, -⟩ | ⟨h3, h1, -, -⟩ | ⟨h3, h1, -, -⟩
    · exact h1
    · rw [hm] at h3
      omega
    · rw [hm] at h3
      omega
    · rw [hm] at h3
      omega

theorem ggIntCartan_offdiag_eq_zero_or_neg_one {Λ : Type} {M : CoxeterMatrix Λ}
    {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C) {i j : Λ} (hij : i ≠ j)
    (hsymm : C i j = C j i) (hlo : -2 ≤ C i j) (hhi : C i j ≤ 2) :
    C i j = 0 ∨ C i j = -1 := by
  rcases hC.2 i j hij with ⟨-, h1, -⟩ | ⟨-, h1, -⟩ | ⟨-, h1, -, -⟩ | ⟨-, h1, -, -⟩
  · exact Or.inl h1
  · exact Or.inr h1
  · exfalso
    rw [← hsymm] at h1
    set t := C i j with ht
    have htlo : -2 ≤ t := by simpa [ht] using hlo
    have hthi : t ≤ 2 := by simpa [ht] using hhi
    have hsq : t * t = 2 := by simpa [ht] using h1
    have h5 : t = -2 ∨ t = -1 ∨ t = 0 ∨ t = 1 ∨ t = 2 := by omega
    rcases h5 with h | h | h | h | h <;> rw [h] at hsq <;> norm_num at hsq
  · exfalso
    rw [← hsymm] at h1
    set t := C i j with ht
    have htlo : -2 ≤ t := by simpa [ht] using hlo
    have hthi : t ≤ 2 := by simpa [ht] using hhi
    have hsq : t * t = 3 := by simpa [ht] using h1
    have h5 : t = -2 ∨ t = -1 ∨ t = 0 ∨ t = 1 ∨ t = 2 := by omega
    rcases h5 with h | h | h | h | h <;> rw [h] at hsq <;> norm_num at hsq

theorem ggIntCartan_offdiag_of_gram {k : ℕ} {Λ : Type} {M : CoxeterMatrix Λ}
    {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C) (ρ : Λ → Fin k → ℤ)
    (hρ : ∀ i, ρ i ∈ ggDRootSet k) (hgram : ∀ i j, ggDDot (ρ i) (ρ j) = C i j) :
    ∀ i j : Λ, i ≠ j → C i j = 0 ∨ C i j = -1 := by
  intro i j hij
  have hsymm : C i j = C j i := by
    rw [← hgram i j, ← hgram j i, ggDDot_comm]
  have hlo := (ggDDot_mem_range (hρ i) (hρ j)).1
  have hhi := (ggDDot_mem_range (hρ i) (hρ j)).2
  refine ggIntCartan_offdiag_eq_zero_or_neg_one hC hij hsymm ?_ ?_
  · simpa [hgram i j] using hlo
  · simpa [hgram i j] using hhi

theorem exists_ggTwoCore {Λ : Type} [DecidableEq Λ] {k : ℕ} (supp : Λ → Finset (Fin k))
    (hcard : ∀ i, (supp i).card = 2) :
    ∀ S : Finset Λ, S.Nonempty → (S.biUnion supp).card ≤ S.card →
      ∃ S' : Finset Λ, S' ⊆ S ∧ S' ≠ ∅ ∧
        ∀ x ∈ S'.biUnion supp, 2 ≤ (S'.filter fun i => x ∈ supp i).card := by
  intro S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro hS hineq
    by_cases hall : ∀ x ∈ S.biUnion supp, 2 ≤ (S.filter fun i => x ∈ supp i).card
    · exact ⟨S, Finset.Subset.refl _, hS.ne_empty, hall⟩
    · push Not at hall
      obtain ⟨x, hxmem, hxle⟩ := hall
      obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hxmem
      have huniq : ∀ j ∈ S, ∀ l ∈ S, x ∈ supp j → x ∈ supp l → j = l := by
        intro j hj l hl hxj hxl
        by_contra hne
        have hsub : ({j, l} : Finset Λ) ⊆ S.filter (fun z => x ∈ supp z) := by
          intro z hz
          rw [Finset.mem_insert, Finset.mem_singleton] at hz
          rw [Finset.mem_filter]
          rcases hz with rfl | rfl
          · exact ⟨hj, hxj⟩
          · exact ⟨hl, hxl⟩
        have hcard2 : ({j, l} : Finset Λ).card = 2 := Finset.card_pair hne
        have := Finset.card_le_card hsub
        omega
      have hTne : (S.erase i).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h0
        have hSeq : S = {i} := by
          refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hi, fun z hz => ?_⟩
          by_contra hzi
          have : z ∈ S.erase i := Finset.mem_erase.mpr ⟨hzi, hz⟩
          rw [h0] at this
          exact Finset.notMem_empty z this
        have hbcard : (S.biUnion supp).card = 2 := by
          rw [hSeq, Finset.singleton_biUnion, hcard i]
        have hScard : S.card = 1 := by rw [hSeq]; simp
        omega
      have hineqT : ((S.erase i).biUnion supp).card ≤ (S.erase i).card := by
        have hxsub : ({x} : Finset (Fin k)) ⊆ S.biUnion supp := by
          intro z hz
          rw [Finset.mem_singleton] at hz
          rwa [hz]
        have hsub : (S.erase i).biUnion supp ⊆ S.biUnion supp \ {x} := by
          intro z hz
          rw [Finset.mem_sdiff]
          constructor
          · rw [Finset.mem_biUnion] at hz ⊢
            obtain ⟨j, hj, hzj⟩ := hz
            exact ⟨j, Finset.mem_of_mem_erase hj, hzj⟩
          · intro hzx
            rw [Finset.mem_singleton] at hzx
            rw [Finset.mem_biUnion] at hz
            obtain ⟨j, hj, hzj⟩ := hz
            have hji : j ≠ i := Finset.ne_of_mem_erase hj
            exact hji (huniq j (Finset.mem_of_mem_erase hj) i hi (hzx ▸ hzj) hxi)
        calc ((S.erase i).biUnion supp).card ≤ (S.biUnion supp \ {x}).card :=
              Finset.card_le_card hsub
          _ = (S.biUnion supp).card - 1 := by
              rw [Finset.card_sdiff_of_subset hxsub, Finset.card_singleton]
          _ ≤ S.card - 1 := by omega
          _ = (S.erase i).card := by rw [Finset.card_erase_of_mem hi]
      have hssub : S.erase i ⊂ S := Finset.erase_ssubset hi
      obtain ⟨S', hS'sub, hS'ne, hS'core⟩ := ih (S.erase i) hssub hTne hineqT
      exact ⟨S', hS'sub.trans (Finset.erase_subset i S), hS'ne, hS'core⟩

theorem exists_ne_mem_of_two_le_filter_card {Λ : Type} [DecidableEq Λ] {k : ℕ}
    {supp : Λ → Finset (Fin k)} {S : Finset Λ} {x : Fin k} {i : Λ}
    (h : 2 ≤ (S.filter fun j => x ∈ supp j).card) :
    ∃ j ∈ S, j ≠ i ∧ x ∈ supp j := by
  have hlt : 1 < (S.filter fun j => x ∈ supp j).card := by omega
  obtain ⟨j, hj, l, hl, hjl⟩ := Finset.one_lt_card.mp hlt
  have hmemj := Finset.mem_filter.mp hj
  have hmeml := Finset.mem_filter.mp hl
  by_cases hji : j = i
  · refine ⟨l, hmeml.1, ?_, hmeml.2⟩
    intro hli
    exact hjl (hji.trans hli.symm)
  · exact ⟨j, hmemj.1, hji, hmemj.2⟩

theorem exists_eq_ggRootSupp {k : ℕ} {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ} (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    (ρ : Λ → Fin k → ℤ) (hρ : ∀ i, ρ i ∈ ggDRootSet k)
    (hgram : ∀ i j, ggDDot (ρ i) (ρ j) = C i j)
    (hk : 3 ≤ k) (hcard : k ≤ Fintype.card Λ) :
    ∃ i j : Λ, i ≠ j ∧ ggRootSupp (ρ i) = ggRootSupp (ρ j) := by
  classical
  have hFT : TauCeti.IsFiniteType C :=
    isFiniteType_of_ggIsWeylMatrixFixed (M := M) hM hC
  have hCval := ggIntCartan_offdiag_of_gram hC ρ hρ hgram
  have hcardpos : 0 < (Finset.univ : Finset Λ).card := by
    simp only [Finset.card_univ]
    omega
  have hne : (Finset.univ : Finset Λ).Nonempty := Finset.card_pos.mp hcardpos
  have hineq : ((Finset.univ : Finset Λ).biUnion fun i => ggRootSupp (ρ i)).card ≤
      (Finset.univ : Finset Λ).card := by
    have h1 : ((Finset.univ : Finset Λ).biUnion fun i => ggRootSupp (ρ i)).card ≤
        (Finset.univ : Finset (Fin k)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    have h2 : (Finset.univ : Finset (Fin k)).card = k := by simp
    have h3 : (Finset.univ : Finset Λ).card = Fintype.card Λ := by simp
    omega
  obtain ⟨S, _, hSne, hScore⟩ := exists_ggTwoCore (fun i => ggRootSupp (ρ i))
    (fun i => ggRootSupp_card (hρ i)) Finset.univ hne hineq
  by_contra hcon
  push Not at hcon
  apply ggResI_no_cycle hFT S (Finset.nonempty_iff_ne_empty.2 hSne)
  intro i hi
  obtain ⟨a, b, hab, ha, hb⟩ := ggDRootSet_exists_pair (hρ i)
  have hsuppi : ggRootSupp (ρ i) = {a, b} := ggRootSupp_eq_pair (hρ i) hab ha hb
  have ha_mem : a ∈ (S.biUnion fun j => ggRootSupp (ρ j)) :=
    Finset.mem_biUnion.mpr ⟨i, hi, ggRootSupp_mem.mpr ha⟩
  have hb_mem : b ∈ (S.biUnion fun j => ggRootSupp (ρ j)) :=
    Finset.mem_biUnion.mpr ⟨i, hi, ggRootSupp_mem.mpr hb⟩
  obtain ⟨ja, hja, hja_ne, hja_mem⟩ :=
    exists_ne_mem_of_two_le_filter_card (hScore a ha_mem)
  obtain ⟨lb, hlb, hlb_ne, hlb_mem⟩ :=
    exists_ne_mem_of_two_le_filter_card (hScore b hb_mem)
  have hja_supp : ggRootSupp (ρ i) ≠ ggRootSupp (ρ ja) := hcon i ja hja_ne.symm
  have hlb_supp : ggRootSupp (ρ i) ≠ ggRootSupp (ρ lb) := hcon i lb hlb_ne.symm
  have hja_b : b ∉ ggRootSupp (ρ ja) := by
    intro hbja
    have hsub : ({a, b} : Finset (Fin k)) ⊆ ggRootSupp (ρ ja) := by
      intro z hz
      rw [Finset.mem_insert, Finset.mem_singleton] at hz
      rw [ggRootSupp_mem]
      rcases hz with rfl | rfl
      · exact ggRootSupp_mem.mp hja_mem
      · exact ggRootSupp_mem.mp hbja
    have heq : ({a, b} : Finset (Fin k)) = ggRootSupp (ρ ja) := by
      refine Finset.eq_of_subset_of_card_le hsub ?_
      rw [ggRootSupp_card (hρ ja), Finset.card_pair hab]
    exact hja_supp (by rw [hsuppi, heq])
  have hjab : ja ≠ lb := by
    intro h
    apply hja_b
    rwa [← h] at hlb_mem
  have hCija : C i ja = -1 := by
    have hdot : ggDDot (ρ i) (ρ ja) = ρ i a * ρ ja a :=
      ggDDot_eq_mul_of_shared (hρ i) (hρ ja) hab ha hb
        (ggRootSupp_mem.mp hja_mem) hja_supp
    have hprod : ρ i a * ρ ja a ≠ 0 := by
      have h1 := ggDRootSet_sign (hρ i) ha
      have h2 := ggDRootSet_sign (hρ ja) (ggRootSupp_mem.mp hja_mem)
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;> norm_num
    have hne0 : C i ja ≠ 0 := by
      intro h0
      apply hprod
      rw [← hdot, hgram i ja]
      exact h0
    rcases hCval i ja hja_ne.symm with h0 | h1
    · exact absurd h0 hne0
    · exact h1
  have hCilb : C i lb = -1 := by
    have hdot : ggDDot (ρ i) (ρ lb) = ρ i b * ρ lb b :=
      ggDDot_eq_mul_of_shared (hρ i) (hρ lb) hab.symm hb ha
        (ggRootSupp_mem.mp hlb_mem) hlb_supp
    have hprod : ρ i b * ρ lb b ≠ 0 := by
      have h1 := ggDRootSet_sign (hρ i) hb
      have h2 := ggDRootSet_sign (hρ lb) (ggRootSupp_mem.mp hlb_mem)
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;> norm_num
    have hne0 : C i lb ≠ 0 := by
      intro h0
      apply hprod
      rw [← hdot, hgram i lb]
      exact h0
    rcases hCval i lb hlb_ne.symm with h0 | h1
    · exact absurd h0 hne0
    · exact h1
  have hmemja : ja ∈ S.filter (fun j => j ≠ i ∧ C i j ≠ 0) := by
    refine Finset.mem_filter.mpr ⟨hja, hja_ne, ?_⟩
    rw [hCija]
    norm_num
  have hmemlb : lb ∈ S.filter (fun j => j ≠ i ∧ C i j ≠ 0) := by
    refine Finset.mem_filter.mpr ⟨hlb, hlb_ne, ?_⟩
    rw [hCilb]
    norm_num
  have hlt : 1 < (S.filter fun j => j ≠ i ∧ C i j ≠ 0).card :=
    Finset.one_lt_card.mpr ⟨ja, hmemja, lb, hmemlb, hjab⟩
  omega

theorem ggSupp_ne_of_ne {k : ℕ} {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (ρ : Λ → Fin k → ℤ) (hρ : ∀ i, ρ i ∈ ggDRootSet k)
    (hgram : ∀ i j, ggDDot (ρ i) (ρ j) = C i j)
    {i j m : Λ} (hij : i ≠ j) (hmi : m ≠ i) (hmj : m ≠ j)
    (hsuppij : ggRootSupp (ρ i) = ggRootSupp (ρ j)) :
    ggRootSupp (ρ m) ≠ ggRootSupp (ρ i) := by
  classical
  intro hsupp
  have hCval := ggIntCartan_offdiag_of_gram hC ρ hρ hgram
  obtain ⟨x, y, hxy, hx, hy⟩ := ggDRootSet_exists_pair (hρ i)
  have hdmi : ggDDot (ρ i) (ρ m) = 0 := by
    have h2 := ggDDot_eq_or_of_ggRootSupp_eq (hρ i) (hρ m) hsupp.symm
    rw [hgram i m] at h2
    rw [hgram i m]
    rcases h2 with h | h | h <;> rcases hCval i m hmi.symm with h0 | h0 <;> omega
  have hdjm : ggDDot (ρ j) (ρ m) = 0 := by
    have h2 := ggDDot_eq_or_of_ggRootSupp_eq (hρ j) (hρ m)
      (hsuppij.symm.trans hsupp.symm)
    rw [hgram j m] at h2
    rw [hgram j m]
    rcases h2 with h | h | h <;> rcases hCval j m hmj.symm with h0 | h0 <;> omega
  have hCij : C i j = 0 := by
    have h2 := ggDDot_eq_or_of_ggRootSupp_eq (hρ i) (hρ j) hsuppij
    rw [hgram i j] at h2
    rcases h2 with h | h | h <;> rcases hCval i j hij with h0 | h0 <;> omega
  have hγδ : ggDDot (ρ i) (ρ j) = 0 := by rw [hgram i j, hCij]
  have hηγ : ggDDot (ρ m) (ρ i) = 0 := by rw [ggDDot_comm]; exact hdmi
  have hzero := ggDDot_ne_zero_of_sameSupp_orth_pair (hρ i) (hρ j) (hρ m) hxy hx hy
    hsuppij.symm hsupp hγδ hηγ
  exact hzero (by rw [ggDDot_comm]; exact hdjm)

theorem ggPrivateCoord_of_sameSupp {k : ℕ} {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ} (hM : GGIsWeylMatrix M)
    (hC : GGIntCartan M C) (ρ : Λ → Fin k → ℤ) (hρ : ∀ i, ρ i ∈ ggDRootSet k)
    (hgram : ∀ i j, ggDDot (ρ i) (ρ j) = C i j)
    {i j l : Λ} {p s : Fin k} (hij : i ≠ j) (hli : l ≠ i) (hlj : l ≠ j)
    (hsuppi : ggRootSupp (ρ i) = {p, s}) (hsuppj : ggRootSupp (ρ j) = {p, s})
    (hps : p ≠ s) (hlp : ρ l p = 0)
    (hCil : C i l = -1) (hCjl : C j l = -1) :
    ∀ m, m ≠ i → m ≠ j → ρ m p = 0 := by
  classical
  have hFT : TauCeti.IsFiniteType C :=
    isFiniteType_of_ggIsWeylMatrixFixed (M := M) hM hC
  have hCval := ggIntCartan_offdiag_of_gram hC ρ hρ hgram
  have hsuppij : ggRootSupp (ρ i) = ggRootSupp (ρ j) := hsuppi.trans hsuppj.symm
  have hpi : ρ i p ≠ 0 := ggRootSupp_mem.mp (by rw [hsuppi]; simp)
  have hsi : ρ i s ≠ 0 := ggRootSupp_mem.mp (by rw [hsuppi]; simp)
  have hpj : ρ j p ≠ 0 := ggRootSupp_mem.mp (by rw [hsuppj]; simp)
  have hsj : ρ j s ≠ 0 := ggRootSupp_mem.mp (by rw [hsuppj]; simp)
  intro m hmi hmj
  by_contra hmp
  have hsuppm_ne : ggRootSupp (ρ m) ≠ ggRootSupp (ρ i) :=
    ggSupp_ne_of_ne hC ρ hρ hgram hij hmi hmj hsuppij
  have hdotim : ggDDot (ρ i) (ρ m) = ρ i p * ρ m p :=
    ggDDot_eq_mul_of_shared (hρ i) (hρ m) hps hpi hsi hmp hsuppm_ne.symm
  have hprod : ρ i p * ρ m p ≠ 0 := by
    have h1 := ggDRootSet_sign (hρ i) hpi
    have h2 := ggDRootSet_sign (hρ m) hmp
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;> norm_num
  have hCim : C i m = -1 := by
    have hne0 : C i m ≠ 0 := by
      intro h0
      apply hprod
      rw [← hdotim, hgram i m]
      exact h0
    rcases hCval i m hmi.symm with h0 | h1
    · exact absurd h0 hne0
    · exact h1
  have hsuppm_ne_j : ggRootSupp (ρ m) ≠ ggRootSupp (ρ j) := by
    intro h
    exact hsuppm_ne (by rw [h, hsuppj, hsuppi])
  have hdotjm : ggDDot (ρ j) (ρ m) = ρ j p * ρ m p :=
    ggDDot_eq_mul_of_shared (hρ j) (hρ m) hps hpj hsj hmp hsuppm_ne_j.symm
  have hprodj : ρ j p * ρ m p ≠ 0 := by
    have h1 := ggDRootSet_sign (hρ j) hpj
    have h2 := ggDRootSet_sign (hρ m) hmp
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;> norm_num
  have hCjm : C j m = -1 := by
    have hne0 : C j m ≠ 0 := by
      intro h0
      apply hprodj
      rw [← hdotjm, hgram j m]
      exact h0
    rcases hCval j m hmj.symm with h0 | h1
    · exact absurd h0 hne0
    · exact h1
  have hml : m ≠ l := by
    intro h
    apply hmp
    rw [h]
    exact hlp
  have hCli : C l i = -1 := by
    rw [← hgram l i, ggDDot_comm, hgram i l]
    exact hCil
  have hClj : C l j = -1 := by
    rw [← hgram l j, ggDDot_comm, hgram j l]
    exact hCjl
  have hCmi : C m i = -1 := by
    rw [← hgram m i, ggDDot_comm, hgram i m]
    exact hCim
  have hCmj : C m j = -1 := by
    rw [← hgram m j, ggDDot_comm, hgram j m]
    exact hCjm
  have hdeg_i : 2 ≤ (({i, j, l, m} : Finset Λ).filter fun w => w ≠ i ∧ C i w ≠ 0).card := by
    have hsub : ({l, m} : Finset Λ) ⊆
        ({i, j, l, m} : Finset Λ).filter fun w => w ≠ i ∧ C i w ≠ 0 := by
      intro w hw
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [Finset.mem_filter]
      rcases hw with hw | hw
      · rw [hw]
        exact ⟨by simp, hli, by rw [hCil]; norm_num⟩
      · rw [hw]
        exact ⟨by simp, hmi, by rw [hCim]; norm_num⟩
    have hcard : ({l, m} : Finset Λ).card = 2 := Finset.card_pair hml.symm
    have := Finset.card_le_card hsub
    omega
  have hdeg_j : 2 ≤ (({i, j, l, m} : Finset Λ).filter fun w => w ≠ j ∧ C j w ≠ 0).card := by
    have hsub : ({l, m} : Finset Λ) ⊆
        ({i, j, l, m} : Finset Λ).filter fun w => w ≠ j ∧ C j w ≠ 0 := by
      intro w hw
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [Finset.mem_filter]
      rcases hw with hw | hw
      · rw [hw]
        exact ⟨by simp, hlj, by rw [hCjl]; norm_num⟩
      · rw [hw]
        exact ⟨by simp, hmj, by rw [hCjm]; norm_num⟩
    have hcard : ({l, m} : Finset Λ).card = 2 := Finset.card_pair hml.symm
    have := Finset.card_le_card hsub
    omega
  have hdeg_l : 2 ≤ (({i, j, l, m} : Finset Λ).filter fun w => w ≠ l ∧ C l w ≠ 0).card := by
    have hsub : ({i, j} : Finset Λ) ⊆
        ({i, j, l, m} : Finset Λ).filter fun w => w ≠ l ∧ C l w ≠ 0 := by
      intro w hw
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [Finset.mem_filter]
      rcases hw with hw | hw
      · rw [hw]
        exact ⟨by simp, hli.symm, by rw [hCli]; norm_num⟩
      · rw [hw]
        exact ⟨by simp, hlj.symm, by rw [hClj]; norm_num⟩
    have hcard : ({i, j} : Finset Λ).card = 2 := Finset.card_pair hij
    have := Finset.card_le_card hsub
    omega
  have hdeg_m : 2 ≤ (({i, j, l, m} : Finset Λ).filter fun w => w ≠ m ∧ C m w ≠ 0).card := by
    have hsub : ({i, j} : Finset Λ) ⊆
        ({i, j, l, m} : Finset Λ).filter fun w => w ≠ m ∧ C m w ≠ 0 := by
      intro w hw
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [Finset.mem_filter]
      rcases hw with hw | hw
      · rw [hw]
        exact ⟨by simp, hmi.symm, by rw [hCmi]; norm_num⟩
      · rw [hw]
        exact ⟨by simp, hmj.symm, by rw [hCmj]; norm_num⟩
    have hcard : ({i, j} : Finset Λ).card = 2 := Finset.card_pair hij
    have := Finset.card_le_card hsub
    omega
  have hdeg : ∀ z, z ∈ ({i, j, l, m} : Finset Λ) →
      2 ≤ (({i, j, l, m} : Finset Λ).filter fun w => w ≠ z ∧ C z w ≠ 0).card := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz | hz | hz
    · rw [hz]
      exact hdeg_i
    · rw [hz]
      exact hdeg_j
    · rw [hz]
      exact hdeg_l
    · rw [hz]
      exact hdeg_m
  exact ggResI_no_cycle hFT ({i, j, l, m} : Finset Λ) (by simp) hdeg

theorem exists_fork_of_sameSupp {k : ℕ} {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ} (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    (ρ : Λ → Fin k → ℤ) (hρ : ∀ i, ρ i ∈ ggDRootSet k)
    (hgram : ∀ i j, ggDDot (ρ i) (ρ j) = C i j)
    {i j : Λ} (hij : i ≠ j) (hsuppij : ggRootSupp (ρ i) = ggRootSupp (ρ j))
    (hthree : 3 ≤ Fintype.card Λ) :
    ∃ (y : Fin k) (i j : Λ), i ≠ j ∧ ρ i y ≠ 0 ∧
      ρ j = Function.update (ρ i) y (-ρ i y) ∧
      ∀ m, m ≠ i → m ≠ j → ρ m y = 0 := by
  classical
  have hCval := ggIntCartan_offdiag_of_gram hC ρ hρ hgram
  have hCij0 : C i j = 0 := by
    rcases hCval i j hij with h0 | h1
    · exact h0
    · exfalso
      have h2 := ggDDot_eq_or_of_ggRootSupp_eq (hρ i) (hρ j) hsuppij
      rw [hgram i j] at h2
      rcases h2 with h | h | h <;> omega
  have hMij : M i j = 2 := (ggIntCartan_zero_iff hC hij).1 hCij0
  have hthird : ∃ m : Λ, m ≠ i ∧ m ≠ j := by
    by_contra h
    have hforall : ∀ m : Λ, m = i ∨ m = j := by
      intro m
      by_contra hm
      push Not at hm
      exact h ⟨m, hm.1, hm.2⟩
    have hsub : (Finset.univ : Finset Λ) ⊆ ({i, j} : Finset Λ) := by
      intro m _
      rcases hforall m with hm | hm <;> rw [hm] <;> simp
    have hle : Fintype.card Λ ≤ 2 := by
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_univ, Finset.card_pair hij] at h1
      exact h1
    omega
  obtain ⟨m0, hm0i, hm0j⟩ := hthird
  have hpath : Relation.ReflTransGen (fun u v : Λ => u ≠ v ∧ M.M u v ≠ 2) i m0 :=
    ggRC_weyl_connected hM i m0
  rcases Relation.ReflTransGen.cases_head hpath with hEq | ⟨l, hl, -⟩
  · exact absurd hEq.symm hm0i
  · have hil : i ≠ l := hl.1
    have hMil : M i l ≠ 2 := hl.2
    have hli : l ≠ i := hil.symm
    have hCil_ne : C i l ≠ 0 := by
      intro h0
      exact hMil ((ggIntCartan_zero_iff hC hil).1 h0)
    have hlj : l ≠ j := by
      intro h
      apply hMil
      rw [h]
      exact hMij
    have hCil : C i l = -1 := by
      rcases hCval i l hil with h0 | h1
      · exact absurd h0 hCil_ne
      · exact h1
    have hdotil : ggDDot (ρ i) (ρ l) = -1 := by
      rw [hgram i l]
      exact hCil
    obtain ⟨p, s, z, hps, hsz, hpz, hpi, hsi, hsl, hzl, _, hlp⟩ :=
      ggDRootSet_dot_eq_neg_one (hρ i) (hρ l) hdotil
    have hsuppi : ggRootSupp (ρ i) = {p, s} := ggRootSupp_eq_pair (hρ i) hps hpi hsi
    have hsuppj : ggRootSupp (ρ j) = {p, s} := by
      rw [← hsuppij]
      exact hsuppi
    have hpj : ρ j p ≠ 0 := ggRootSupp_mem.mp (by rw [hsuppj]; simp)
    have hsj : ρ j s ≠ 0 := ggRootSupp_mem.mp (by rw [hsuppj]; simp)
    have hsuppjl_ne : ggRootSupp (ρ j) ≠ ggRootSupp (ρ l) := by
      intro heq
      have hzmem : z ∈ ggRootSupp (ρ l) := ggRootSupp_mem.mpr hzl
      have hzmemj : z ∈ ggRootSupp (ρ j) := by rw [heq]; exact hzmem
      have hzp : z ∈ ({p, s} : Finset (Fin k)) := by rw [← hsuppj]; exact hzmemj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzp
      rcases hzp with h | h
      · exact hpz h.symm
      · exact hsz h.symm
    have hdotjl : ggDDot (ρ j) (ρ l) = ρ j s * ρ l s :=
      ggDDot_eq_mul_of_shared (hρ j) (hρ l) hps.symm hsj hpj hsl hsuppjl_ne
    have hprodjl : ρ j s * ρ l s ≠ 0 := by
      have h1 := ggDRootSet_sign (hρ j) hsj
      have h2 := ggDRootSet_sign (hρ l) hsl
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;> norm_num
    have hCjl : C j l = -1 := by
      have hne0 : C j l ≠ 0 := by
        intro h0
        apply hprodjl
        rw [← hdotjl, hgram j l]
        exact h0
      rcases hCval j l hlj.symm with h0 | h1
      · exact absurd h0 hne0
      · exact h1
    have hpriv : ∀ m, m ≠ i → m ≠ j → ρ m p = 0 :=
      ggPrivateCoord_of_sameSupp hM hC ρ hρ hgram hij hli hlj hsuppi hsuppj hps hlp
        hCil hCjl
    have hdotij : ggDDot (ρ i) (ρ j) = 0 := by rw [hgram i j, hCij0]
    have hdotij_formula : ggDDot (ρ i) (ρ j) =
        ρ i p * ρ j p + ρ i s * ρ j s :=
      ggDRootSet_dot_eq (hρ i) hps hpi hsi (ρ j)
    have hdotil_formula : ggDDot (ρ i) (ρ l) =
        ρ i p * ρ l p + ρ i s * ρ l s :=
      ggDRootSet_dot_eq (hρ i) hps hpi hsi (ρ l)
    have hdotjl_formula : ggDDot (ρ j) (ρ l) =
        ρ j p * ρ l p + ρ j s * ρ l s :=
      ggDRootSet_dot_eq (hρ j) hps hpj hsj (ρ l)
    have hdotjl' : ggDDot (ρ j) (ρ l) = -1 := by rw [hgram j l]; exact hCjl
    have hisl : ρ i s * ρ l s = -1 := by
      have h := hdotil_formula
      rw [hlp, mul_zero, zero_add] at h
      rw [← h]
      exact hdotil
    have hjsl : ρ j s * ρ l s = -1 := by
      have h := hdotjl_formula
      rw [hlp, mul_zero, zero_add] at h
      rw [← h]
      exact hdotjl'
    have hsj_eq : ρ i s = ρ j s := by
      refine mul_right_cancel₀ hsl ?_
      rw [hisl, hjsl]
    have hss : ρ i s * ρ i s = 1 := by
      rcases ggDRootSet_sign (hρ i) hsi with h | h <;> rw [h] <;> norm_num
    have h2 : ρ i p * ρ j p = -1 := by
      have h := hdotij_formula
      rw [hdotij] at h
      have hssj : ρ i s * ρ j s = 1 := by rw [← hsj_eq]; exact hss
      rw [hssj] at h
      omega
    have hpp : ρ i p * ρ i p = 1 := by
      rcases ggDRootSet_sign (hρ i) hpi with h | h <;> rw [h] <;> norm_num
    have hjp : ρ j p = -ρ i p := by
      refine mul_left_cancel₀ hpi ?_
      rw [mul_neg, hpp]
      exact h2
    refine ⟨p, i, j, hij, hpi, ?_, hpriv⟩
    funext c
    by_cases hcp : c = p
    · subst hcp
      simpa [Function.update_apply] using hjp
    · by_cases hcs : c = s
      · subst hcs
        simpa [Function.update_apply, hps, Ne.symm hps] using hsj_eq.symm
      · have hci : ρ i c = 0 := by
          have hcnot : c ∉ ggRootSupp (ρ i) := by
            rw [hsuppi]
            simp [hcp, hcs]
          simpa [ggRootSupp] using hcnot
        have hcj : ρ j c = 0 := by
          have hcnot : c ∉ ggRootSupp (ρ j) := by
            rw [hsuppj]
            simp [hcp, hcs]
          simpa [ggRootSupp] using hcnot
        simp [hcp, hci, hcj]

theorem exists_dRoot_fork {k : ℕ} {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ} (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    (ρ : Λ → Fin k → ℤ) (hρ : ∀ i, ρ i ∈ ggDRootSet k)
    (hgram : ∀ i j, ggDDot (ρ i) (ρ j) = C i j)
    (hk : 3 ≤ k) (hcard : k ≤ Fintype.card Λ) :
    ∃ (y : Fin k) (i j : Λ), i ≠ j ∧ ρ i y ≠ 0 ∧ ρ j = Function.update (ρ i) y (-ρ i y) ∧
      ∀ m, m ≠ i → m ≠ j → ρ m y = 0 := by
  obtain ⟨i, j, hij, hsupp⟩ := exists_eq_ggRootSupp hM hC ρ hρ hgram hk hcard
  exact exists_fork_of_sameSupp hM hC ρ hρ hgram hij hsupp (by omega)

end CFSG.StandardType

end
