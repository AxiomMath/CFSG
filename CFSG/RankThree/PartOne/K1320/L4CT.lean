module

public import CFSG.RankThree.PartOne.K1320.L4Frame
public import CFSG.RankThree.PartOne.K1320.L4Lift
public import CFSG.RankThree.PartOne.K1320.L4TorusAlg

public section

namespace CFSG.RankThree.PartOne.K1320

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSL)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_sup_mul_of_commute {A B : Subgroup G} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {g : G} (hg : g ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, g = a * b := by
  rw [Subgroup.sup_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, B.one_mem, (mul_one x).symm⟩
    · exact ⟨1, A.one_mem, x, hx, (one_mul x).symm⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    obtain ⟨a', ha', b', hb', rfl⟩ := hy
    refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
    have h : b * a' = a' * b := (hAB a' ha' b hb).symm
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [h]
      _ = a * a' * (b * b') := by group
  | inv x _ hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    have h : Commute a b := hAB a ha b hb
    rw [mul_inv_rev, h.inv_inv.eq]

omit [Finite G] in
theorem inf_centralizer_self_eq_bot {K₃ : Subgroup G} (hz : Subgroup.center ↥K₃ = ⊥) :
    K₃ ⊓ Subgroup.centralizer (K₃ : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hmem : (⟨x, hx.1⟩ : ↥K₃) ∈ Subgroup.center ↥K₃ := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.1 hx.2 y y.2)
  rw [hz, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val hmem

omit [Finite G] in
theorem le_centralizer_symm {A B : Subgroup G} (h : A ≤ Subgroup.centralizer (B : Set G)) :
    B ≤ Subgroup.centralizer (A : Set G) := fun x hx => by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (Subgroup.mem_centralizer_iff.1 (h hy) x hx).symm

namespace Row8Frame

variable {p : ℕ} {A L E : Subgroup G} {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
  (fr : Row8Frame p A L E f K)

@[expose] noncomputable def lft (S : Subgroup ↥(M8 K)) : Subgroup G := liftM fr.ε (q8 K) S

omit [Finite G] in
theorem lft_le (S : Subgroup ↥(M8 K)) : fr.lft S ≤ L := liftM_le S

omit [Finite G] in
theorem lft_inf (S T : Subgroup ↥(M8 K)) : fr.lft (S ⊓ T) = fr.lft S ⊓ fr.lft T :=
  liftM_inf (q8_inj (K := K)) S T

omit [Finite G] in
theorem lft_sup (hZ : Subgroup.center L = ⊥) (S T : Subgroup ↥(M8 K)) :
    fr.lft (S ⊔ T) = fr.lft S ⊔ fr.lft T :=
  liftM_sup fr.surj (fr.inj hZ) S T

omit [Finite G] in
theorem lft_cent (hZ : Subgroup.center L = ⊥) (S T : Subgroup ↥(M8 K)) :
    fr.lft S ⊓ Subgroup.centralizer (fr.lft T : Set G) =
      fr.lft (S ⊓ Subgroup.centralizer (T : Set ↥(M8 K))) :=
  liftM_inf_centralizer fr.surj (fr.inj hZ) (q8_inj (K := K)) S T

omit [Finite G] in
theorem lft_card (hZ : Subgroup.center L = ⊥) (S : Subgroup ↥(M8 K)) :
    Nat.card (fr.lft S) = Nat.card S :=
  card_liftM fr.surj (fr.inj hZ) (q8_inj (K := K)) S

theorem lft_relIndex (hZ : Subgroup.center L = ⊥) (S T : Subgroup ↥(M8 K)) :
    (fr.lft S).relIndex (fr.lft T) = S.relIndex T :=
  relIndex_liftM fr.surj (fr.inj hZ) (q8_inj (K := K)) S T

omit [Finite G] in
theorem lft_le_iff {S T : Subgroup ↥(M8 K)} : fr.lft S ≤ fr.lft T ↔ S ≤ T := by
  unfold lft liftM
  rw [pullG_le_iff fr.surj, Subgroup.map_le_map_iff_of_injective (q8_inj (K := K))]


theorem torus_facts {c : G} (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hZ : Subgroup.center L = ⊥) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrq : r ∣ Nat.card K - 1) {K₃ : Subgroup G}
    (hc1 : K₃ ≤ Subgroup.centralizer (kZero p E fr.r₀ : Set G))
    (hc2 : K₃ ≤ Subgroup.centralizer (kZero p E fr.r₀' : Set G))
    (hRK : fr.lft (Rr K r) ≤ K₃) (hz3 : Subgroup.center ↥K₃ = ⊥) :
    CTTorusCondition r (fr.lft (torusF K r)) ![kZero p E fr.r₀, fr.lft (slB K 1 2), K₃] ∧
      ¬ (fr.lft (torusF K r) ⊓ fr.lft (slB K 1 2) ≤ Subgroup.centralizer (K₃ : Set G)) ∧
      Nat.card ↥(fr.lft (torusF K r) ⊓ K₃) = r ∧
      Nat.card ↥(fr.lft (torusF K r) ⊓ fr.lft (slB K 1 2)) = r ∧
      (fr.lft (torusF K r) ⊓ K₃) ⊓ (fr.lft (torusF K r) ⊓ fr.lft (slB K 1 2)) = ⊥ ∧
      fr.lft (torusF K r) = (fr.lft (torusF K r) ⊓ Subgroup.centralizer (K₃ : Set G)) ⊔
        (fr.lft (torusF K r) ⊓ K₃) ∧
      fr.lft (torusF K r) = (fr.lft (torusF K r) ⊓
          Subgroup.centralizer (fr.lft (slB K 1 2) : Set G)) ⊔
        (fr.lft (torusF K r) ⊓ fr.lft (slB K 1 2)) := by
  have hK1 : kZero p E fr.r₀ = fr.lft (slB K 0 1) := fr.kz₀ h hF13 hZ
  have hK1' : kZero p E fr.r₀' = fr.lft (slB K 2 3) := fr.kz₀' h hF13 hZ
  rw [hK1] at hc1 ⊢
  rw [hK1'] at hc2
  have hi := fr.inj hZ
  have hψ := q8_inj (K := K)
  have hs := fr.surj
  have hmu : Nat.card (Rr K r) = r := rootsOfUnity_card hr hrq
  obtain ⟨htc1, htc2, htc3⟩ := torusF_condition (K := K) hr hr2 hrq
  obtain ⟨hdec3, hrel3⟩ := torusF_decomp_three (K := K) hr hr2 hrq
  have hb13 := relIndex_torusF_one_three (K := K) hr hr2 hrq
  have hb23 := relIndex_torusF_two_three (K := K) hr hr2 hrq
  have hnot := torusF_inf_slB_one_two_not_le (K := K) hr hr2 hrq
  have hcard12 := card_torusF_inf_slB_one_two (K := K) hr hr2 hrq
  have hRB12 := Rr_inf_slB_one_two (K := K) r
  set T : Subgroup ↥(M8 K) := torusF K r with hT
  set Pm : Subgroup ↥(M8 K) := (T ⊓ slB K 0 1) ⊔ (T ⊓ slB K 2 3) with hPm
  set F : Subgroup G := fr.lft T with hF
  have hFe : IsElementaryAbelian r ↥F :=
    isElementaryAbelian_liftM hs hi hψ (torusF_isElementaryAbelian hr)
  have hFcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hFe.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hK1c3 : fr.lft (slB K 0 1) ≤ Subgroup.centralizer (K₃ : Set G) := le_centralizer_symm hc1
  have hK1'c3 : fr.lft (slB K 2 3) ≤ Subgroup.centralizer (K₃ : Set G) := le_centralizer_symm hc2
  have hPmF : fr.lft Pm ≤ F := (fr.lft_le_iff).2 (sup_le inf_le_left inf_le_left)
  have hRF : fr.lft (Rr K r) ≤ F := (fr.lft_le_iff).2 (Rr_le_torusF r)
  have hQ_le : fr.lft Pm ≤ F ⊓ Subgroup.centralizer (K₃ : Set G) := by
    refine le_inf hPmF ?_
    rw [hPm, fr.lft_sup hZ, fr.lft_inf, fr.lft_inf]
    refine sup_le ?_ ?_
    · exact inf_le_right.trans hK1c3
    · exact inf_le_right.trans hK1'c3
  have hdecG : F = fr.lft Pm ⊔ fr.lft (Rr K r) := by
    have := congrArg fr.lft hdec3
    rwa [fr.lft_sup hZ] at this
  have hcomm_QR : ∀ a ∈ fr.lft Pm, ∀ b ∈ fr.lft (Rr K r), a * b = b * a := fun a ha b hb =>
    hFcomm a (hPmF ha) b (hRF hb)
  have hbot3 : K₃ ⊓ Subgroup.centralizer (K₃ : Set G) = ⊥ := inf_centralizer_self_eq_bot hz3
  have hFK3 : F ⊓ K₃ = fr.lft (Rr K r) := by
    refine le_antisymm ?_ (le_inf hRF hRK)
    intro x hx
    have hxs : x ∈ fr.lft Pm ⊔ fr.lft (Rr K r) := hdecG ▸ hx.1
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_mul_of_commute hcomm_QR hxs
    have haC : a ∈ Subgroup.centralizer (K₃ : Set G) := (hQ_le ha).2
    have haK : a ∈ K₃ := by
      have := K₃.mul_mem hx.2 (K₃.inv_mem (hRK hb))
      simpa using this
    have ha1 : a = 1 := by
      have : a ∈ K₃ ⊓ Subgroup.centralizer (K₃ : Set G) := ⟨haK, haC⟩
      rw [hbot3] at this
      exact this
    rw [ha1, one_mul]
    exact hb
  have hCF3 : F ⊓ Subgroup.centralizer (K₃ : Set G) = fr.lft Pm := by
    refine le_antisymm ?_ hQ_le
    intro x hx
    have hxs : x ∈ fr.lft Pm ⊔ fr.lft (Rr K r) := hdecG ▸ hx.1
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_mul_of_commute hcomm_QR hxs
    have haC : a ∈ Subgroup.centralizer (K₃ : Set G) := (hQ_le ha).2
    have hbC : b ∈ Subgroup.centralizer (K₃ : Set G) := by
      have := (Subgroup.centralizer (K₃ : Set G)).mul_mem
        ((Subgroup.centralizer (K₃ : Set G)).inv_mem haC) hx.2
      simpa using this
    have hb1 : b = 1 := by
      have : b ∈ K₃ ⊓ Subgroup.centralizer (K₃ : Set G) := ⟨hRK hb, hbC⟩
      rw [hbot3] at this
      exact this
    rw [hb1, mul_one]
    exact ha
  have hdec1 : F = (F ⊓ Subgroup.centralizer (fr.lft (slB K 0 1) : Set G)) ⊔
      (F ⊓ fr.lft (slB K 0 1)) := by
    rw [hF, fr.lft_cent hZ, ← fr.lft_inf, ← fr.lft_sup hZ]
    exact congrArg fr.lft htc1.1
  have hdec2 : F = (F ⊓ Subgroup.centralizer (fr.lft (slB K 1 2) : Set G)) ⊔
      (F ⊓ fr.lft (slB K 1 2)) := by
    rw [hF, fr.lft_cent hZ, ← fr.lft_inf, ← fr.lft_sup hZ]
    exact congrArg fr.lft htc2.1
  have hdec3' : F = (F ⊓ Subgroup.centralizer (K₃ : Set G)) ⊔ (F ⊓ K₃) := by
    rw [hCF3, hFK3]
    exact hdecG
  have hri1 : (F ⊓ Subgroup.centralizer (fr.lft (slB K 0 1) : Set G)).relIndex F = r := by
    rw [hF, fr.lft_cent hZ, fr.lft_relIndex hZ]
    exact htc1.2
  have hri2 : (F ⊓ Subgroup.centralizer (fr.lft (slB K 1 2) : Set G)).relIndex F = r := by
    rw [hF, fr.lft_cent hZ, fr.lft_relIndex hZ]
    exact htc2.2
  have hri3 : (F ⊓ Subgroup.centralizer (K₃ : Set G)).relIndex F = r := by
    rw [hCF3, hF, fr.lft_relIndex hZ]
    exact hrel3
  have hp12 : (F ⊓ Subgroup.centralizer ((fr.lft (slB K 0 1) ⊔ fr.lft (slB K 1 2) : Subgroup G) :
      Set G)).relIndex F = r ^ 2 := by
    rw [← fr.lft_sup hZ, hF, fr.lft_cent hZ, fr.lft_relIndex hZ]
    exact htc3
  have hp13 : (F ⊓ Subgroup.centralizer ((fr.lft (slB K 0 1) ⊔ K₃ : Subgroup G) :
      Set G)).relIndex F = r ^ 2 := by
    have : F ⊓ Subgroup.centralizer ((fr.lft (slB K 0 1) ⊔ K₃ : Subgroup G) : Set G) =
        fr.lft ((T ⊓ Subgroup.centralizer (slB K 0 1 : Set ↥(M8 K))) ⊓ Pm) := by
      rw [fr.lft_inf, ← fr.lft_cent hZ, ← hCF3]
      ext x
      simp only [Subgroup.mem_inf, mem_centralizer_sup, hF]
      tauto
    rw [this, hF, fr.lft_relIndex hZ]
    exact hb13
  have hp23 : (F ⊓ Subgroup.centralizer ((fr.lft (slB K 1 2) ⊔ K₃ : Subgroup G) :
      Set G)).relIndex F = r ^ 2 := by
    have : F ⊓ Subgroup.centralizer ((fr.lft (slB K 1 2) ⊔ K₃ : Subgroup G) : Set G) =
        fr.lft ((T ⊓ Subgroup.centralizer (slB K 1 2 : Set ↥(M8 K))) ⊓ Pm) := by
      rw [fr.lft_inf, ← fr.lft_cent hZ, ← hCF3]
      ext x
      simp only [Subgroup.mem_inf, mem_centralizer_sup, hF]
      tauto
    rw [this, hF, fr.lft_relIndex hZ]
    exact hb23
  have hCT : CTTorusCondition r F ![fr.lft (slB K 0 1), fr.lft (slB K 1 2), K₃] := by
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · fin_cases i
      · exact ⟨hdec1, hri1⟩
      · exact ⟨hdec2, hri2⟩
      · exact ⟨hdec3', hri3⟩
    · fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hp12
      · exact hp13
      · rw [sup_comm]; exact hp12
      · exact absurd rfl hij
      · exact hp23
      · rw [sup_comm]; exact hp13
      · rw [sup_comm]; exact hp23
      · exact absurd rfl hij
  have hnotle : ¬ (F ⊓ fr.lft (slB K 1 2) ≤ Subgroup.centralizer (K₃ : Set G)) := by
    intro hle
    have h1 : F ⊓ fr.lft (slB K 1 2) ≤ fr.lft Pm := hCF3 ▸ le_inf inf_le_left hle
    rw [hF, ← fr.lft_inf, fr.lft_le_iff] at h1
    exact hnot h1
  refine ⟨hCT, hnotle, ?_, ?_, ?_, hdec3', hdec2⟩
  · rw [hFK3, fr.lft_card hZ]
    exact hmu
  · rw [hF, ← fr.lft_inf, fr.lft_card hZ]
    exact hcard12
  · rw [hFK3, hF, ← fr.lft_inf, ← fr.lft_inf, eq_bot_iff]
    have : Rr K r ⊓ (T ⊓ slB K 1 2) = ⊥ :=
      eq_bot_iff.2 (le_trans (inf_le_inf_left _ inf_le_right) hRB12.le)
    rw [this]
    exact (liftM_bot (ψ := q8 K) hi).le

end Row8Frame

end CFSG.RankThree.PartOne.K1320
