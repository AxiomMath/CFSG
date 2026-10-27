module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42MElem
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42MFacts

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly (InCatalog)

variable {G : Type} [Group G] [Finite G] {b : G} {J B : Subgroup G} {b₁ b₂ : G}

namespace FF79Sec4

variable (h : FF79Sec4 b J B b₁ b₂)
include h

theorem card_B : Nat.card B = 27 := by
  have := h.mono.1.2
  simpa using this

theorem comm_B {x y : G} (hx : x ∈ B) (hy : y ∈ B) : x * y = y * x := by
  haveI := h.mono.1.1
  have := (IsMulCommutative.is_comm (M := ↥B)).comm (⟨x, hx⟩ : ↥B) ⟨y, hy⟩
  exact congrArg Subtype.val this

theorem pow3_B {x : G} (hx : x ∈ B) : x ^ 3 = 1 := by
  haveI := h.mono.1.1
  exact elemPow_eq_one_of_isElementaryAbelian x hx

theorem b_mem : b ∈ B := by
  rw [h.mono.2.1]; exact Subgroup.subset_closure (by simp)

theorem b₁_mem : b₁ ∈ B := (Subgroup.mem_inf.mp h.hb₁).1

theorem b₂_mem : b₂ ∈ B := (Subgroup.mem_inf.mp h.hb₂).1

theorem ord_b : orderOf b = 3 := h.hyp.ord

theorem ord_b₁ : orderOf b₁ = 3 := by
  obtain ⟨n, -, hn, -, -⟩ := h.mono.2.2.2.2.1
  rw [← hn, m42_orderOf_conj, h.ord_b]

theorem b₂_not_mem : b₂ ∉ Subgroup.closure ({b, b₁} : Set G) := by
  intro hmem
  have hle : B ≤ Subgroup.closure ({b, b₁} : Set G) := by
    rw [h.mono.2.1, Subgroup.closure_le]
    rintro y (rfl | rfl | rfl)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact hmem
  have h1 := Subgroup.card_le_of_le hle
  have h2 := m42_card_pair_le h.ord_b h.ord_b₁ (h.comm_B h.b_mem h.b₁_mem)
  have := h.card_B
  omega

theorem β_ne_one : b₁ * b₂ ≠ 1 := by
  intro hβ
  apply h.b₂_not_mem
  have : b₂ = b₁⁻¹ := eq_inv_of_mul_eq_one_right hβ
  rw [this]
  exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))

theorem γ_ne_one : b₁ ^ 2 * b₂ ≠ 1 := by
  intro hγ
  apply h.b₂_not_mem
  have : b₂ = (b₁ ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right hγ
  rw [this]
  exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) 2)

theorem β_mem : b₁ * b₂ ∈ B := B.mul_mem h.b₁_mem h.b₂_mem

theorem γ_mem : b₁ ^ 2 * b₂ ∈ B := B.mul_mem (B.pow_mem h.b₁_mem 2) h.b₂_mem

theorem ord_β : orderOf (b₁ * b₂) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (h.pow3_B h.β_mem) h.β_ne_one

theorem ord_γ : orderOf (b₁ ^ 2 * b₂) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (h.pow3_B h.γ_mem) h.γ_ne_one

theorem comm_bγ : b * (b₁ ^ 2 * b₂) = (b₁ ^ 2 * b₂) * b := h.comm_B h.b_mem h.γ_mem

theorem comm_bβ : b * (b₁ * b₂) = (b₁ * b₂) * b := h.comm_B h.b_mem h.β_mem

theorem comm_γβ : (b₁ ^ 2 * b₂) * (b₁ * b₂) = (b₁ * b₂) * (b₁ ^ 2 * b₂) :=
  h.comm_B h.γ_mem h.β_mem

theorem Cen_β_ne_top : Cen (b₁ * b₂) ≠ ⊤ := by
  intro htop
  have hcen : (b₁ * b₂) ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have : g ∈ Cen (b₁ * b₂) := by rw [htop]; exact Subgroup.mem_top _
    exact (m42_cen_comm this).symm
  haveI := h.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h0 | h0
  · rw [h0, Subgroup.mem_bot] at hcen
    exact h.β_ne_one hcen
  · obtain ⟨x, y, hxy⟩ := h.nonab
    apply hxy
    have : x ∈ Subgroup.center G := by rw [h0]; exact Subgroup.mem_top _
    exact ((Subgroup.mem_center_iff.mp this) y).symm

theorem kgn {M : Subgroup G} (hM : M ≤ Cen (b₁ * b₂)) : KCore.KGroupNonab InCatalog ↥M := by
  refine KCore.KProperNonab.kGroupNonab CFSG.Assembly.inCatalog_isoInvariant h.kp M ?_
  intro htop
  apply h.Cen_β_ne_top
  rw [eq_top_iff, ← htop]; exact hM

theorem closure_ne_top {x y : G} (hx : x ∈ B) (hy : y ∈ B) (hox : orderOf x = 3)
    (hoy : orderOf y = 3) (hc : x * y = y * x) : Subgroup.closure ({x, y} : Set G) < B := by
  refine lt_of_le_of_ne ((Subgroup.closure_le B).mpr ?_) ?_
  · rintro z (rfl | rfl)
    · exact hx
    · exact hy
  · intro heq
    have h1 := m42_card_pair_le hox hoy hc
    rw [heq, h.card_B] at h1
    omega

end FF79Sec4

theorem m42_OUp_le (p : ℕ) (M : Subgroup G) : OUp p M ≤ M := Subgroup.map_subtype_le _

theorem m42_OUp_conj_mem {p : ℕ} {M : Subgroup G} {g z : G} (hg : g ∈ M) (hz : z ∈ OUp p M) :
    g * z * g⁻¹ ∈ OUp p M := by
  obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
  refine Subgroup.mem_map.mpr ⟨⟨g, hg⟩ * z' * ⟨g, hg⟩⁻¹, ?_, by simp⟩
  exact (Subgroup.normalClosure_normal).conj_mem z' hz' ⟨g, hg⟩

theorem m42_mem_OUp {p : ℕ} {M : Subgroup G} {g : G} (hg : g ∈ M)
    (hc : Nat.Coprime p (orderOf g)) : g ∈ OUp p M := by
  refine Subgroup.mem_map.mpr ⟨⟨g, hg⟩, Subgroup.subset_normalClosure ?_, rfl⟩
  show Nat.Coprime p (orderOf (⟨g, hg⟩ : ↥M))
  rwa [Subgroup.orderOf_mk]

namespace FF79Sec4

variable (h : FF79Sec4 b J B b₁ b₂)
include h

theorem lemma14 (h14 : FF79_1_4) (h41 : FF79_4_1) :
    Opp 3 (Cen b) ≤ CenS B ∧
      (∀ g ∈ CenS B, ∀ x ∈ Opp 3 (Cen b), g * x * g⁻¹ ∈ Opp 3 (Cen b)) ∧
      Nat.Coprime 3 (Nat.card (Opp 3 (Cen b))) ∧
      (∀ A : Subgroup G, A < B → ConjInto b A → Opp 3 (CenS A) = Opp 3 (Cen b)) := by
  obtain ⟨h1, h2, h3, -, h5, -⟩ := h14 G 5 (Or.inr rfl) b J h.hyp B h.sylB (h41 G b J B b₁ b₂ h)
    (Or.inr rfl)
  refine ⟨h1, fun g hg x hx => ?_, ?_, h5⟩
  · have := h2.conj_mem ⟨x, h1 hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨g, hg⟩
    simpa using Subgroup.mem_subgroupOf.mp this
  · exact (Nat.Coprime.coprime_dvd_right (by norm_num : 3 ∣ 6) h3).symm

theorem X_b (h14 : FF79_1_4) (h41 : FF79_4_1) :
    Opp 3 (Cen b ⊓ Cen (b₁ * b₂)) = Opp 3 (Cen b) := by
  have hA := h.closure_ne_top h.b_mem h.β_mem h.ord_b h.ord_β h.comm_bβ
  have := (h.lemma14 h14 h41).2.2.2 _ hA ⟨1, by simpa using Subgroup.subset_closure (by simp)⟩
  rwa [m42_cenS_closure_pair] at this

theorem X_γ (h14 : FF79_1_4) (h41 : FF79_4_1) :
    Opp 3 (Cen (b₁ ^ 2 * b₂) ⊓ Cen (b₁ * b₂)) = Opp 3 (Cen b) := by
  have hA := h.closure_ne_top h.γ_mem h.β_mem h.ord_γ h.ord_β h.comm_γβ
  obtain ⟨n, -, hn, -, -⟩ := h.mono.2.2.2.2.1
  have hb₁ : b₁ ∈ Subgroup.closure ({b₁ ^ 2 * b₂, b₁ * b₂} : Set G) := by
    have e1 : b₁ = (b₁ ^ 2 * b₂) * (b₁ * b₂)⁻¹ := by group
    have hmem : (b₁ ^ 2 * b₂) * (b₁ * b₂)⁻¹ ∈
        Subgroup.closure ({b₁ ^ 2 * b₂, b₁ * b₂} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
    rw [← e1] at hmem
    exact hmem
  have := (h.lemma14 h14 h41).2.2.2 _ hA ⟨n, by rw [hn]; exact hb₁⟩
  rwa [m42_cenS_closure_pair] at this

theorem kgn_H {M : Subgroup G} (hM : M ≤ OUp 3 (Cen (b₁ * b₂))) :
    KCore.KGroupNonab InCatalog ↥M :=
  h.kgn (hM.trans (m42_OUp_le 3 _ |>.trans le_rfl))

end FF79Sec4

end CFSG.RankThree.PartTwo.Sec21.FF79
