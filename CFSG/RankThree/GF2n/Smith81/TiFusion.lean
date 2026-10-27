module

public import CFSG.RankThree.GF2n.Smith81.Sec1Fusion
public import CFSG.Timmesfeld.CorollaryBBasic
public import CFSG.RankThree.GF2n.Stroth80.Conj2

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def TIFusion (M Q Z : Subgroup G) : Prop :=
  ∀ g z : G, z ∈ Z → z ≠ 1 → g * z * g⁻¹ ∈ M → g * z * g⁻¹ ∈ Q

section ZClass

variable [Finite G] {M Q Z : Subgroup G}

theorem exists_ctx_of_strothHyp (H : StrothHyp M Q Z) : ∃ B : Subgroup G, Ctx M Q Z B := by
  obtain ⟨g, hgZ, hgQ⟩ := H.toHyp79.exists_opposite
  exact ⟨conjSubgroup g Z, ⟨H, ⟨g, rfl⟩, hgQ, hgZ⟩⟩

theorem Z_isConj (H : StrothHyp M Q Z) {z z' : G} (hz : z ∈ Z) (hz1 : z ≠ 1) (hz' : z' ∈ Z)
    (hz1' : z' ≠ 1) : ∃ m ∈ M, m * z * m⁻¹ = z' := by
  classical
  obtain ⟨B, hc⟩ := exists_ctx_of_strothHyp H
  obtain ⟨k, hkM, hko, hkreg⟩ := hc.cartan
  have hkM' : k ∈ M := (Subgroup.mem_inf.mp hkM).1
  haveI : Fintype G := Fintype.ofFinite G
  set q := Nat.card Z with hq
  have hq4 : 4 ≤ q := H.q4
  have hconjZ : ∀ (m : G), m ∈ M → ∀ v ∈ Z, m * v * m⁻¹ ∈ Z := fun m hm v hv =>
    (Subgroup.mem_normalizer_iff.mp (H.Z_normal.2 hm) v).mp hv
  let f : ℕ → G := fun i => k ^ i * z * (k ^ i)⁻¹
  have hfmem : ∀ i, f i ∈ Z := fun i => hconjZ _ (pow_mem hkM' i) z hz
  have hfne : ∀ i, f i ≠ 1 := by
    intro i h
    apply hz1
    have : z = (k ^ i)⁻¹ * f i * k ^ i := by simp only [f]; group
    rw [this, h]; group
  have hinj : ∀ i j, i < j → j < q - 1 → f i ≠ f j := by
    intro i j hij hjq hfe
    obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
    have hd0 : 0 < d := by omega
    have hdq : d < q - 1 := by omega
    have h1 : k ^ d * z = z * k ^ d := by
      have h2 : k ^ i * z * (k ^ i)⁻¹ = k ^ i * (k ^ d * z * (k ^ d)⁻¹) * (k ^ i)⁻¹ := by
        have := hfe
        simp only [f, pow_add, mul_inv_rev] at this
        calc k ^ i * z * (k ^ i)⁻¹ = k ^ i * k ^ d * z * ((k ^ d)⁻¹ * (k ^ i)⁻¹) := this
          _ = _ := by group
      have h3 : z = k ^ d * z * (k ^ d)⁻¹ := by
        have := mul_left_cancel (mul_right_cancel (b := (k ^ i)⁻¹) h2)
        simpa [mul_assoc] using this
      calc k ^ d * z = (k ^ d * z * (k ^ d)⁻¹) * k ^ d := by group
        _ = z * k ^ d := by rw [← h3]
    exact hz1 (hkreg d hd0 (by omega) z hz h1)
  let S : Finset G := Finset.univ.filter (fun x => x ∈ Z ∧ x ≠ 1)
  have hSc : S.card = q - 1 := by
    have h1 : (Finset.univ.filter (fun x => x ∈ Z)).card = q := by
      rw [hq, Nat.card_eq_fintype_card, Fintype.card_subtype]
    have h2 : S = (Finset.univ.filter (fun x => x ∈ Z)).erase 1 := by
      ext x
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      tauto
    rw [h2, Finset.card_erase_of_mem (by simp [Z.one_mem]), h1]
  let T : Finset G := (Finset.range (q - 1)).image f
  have hTc : T.card = q - 1 := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact hinj i j h hj hij
    · exact hinj j i h hi hij.symm
  have hTS : T ⊆ S := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hfmem i, hfne i⟩
  have hTS' : T = S := Finset.eq_of_subset_of_card_le hTS (by rw [hSc, hTc])
  have hz'S : z' ∈ S := by simp [S, hz', hz1']
  rw [← hTS'] at hz'S
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hz'S
  exact ⟨k ^ i, pow_mem hkM' i, hi⟩

theorem mem_M_of_commute_Z (H : StrothHyp M Q Z) {z c : G} (hz : z ∈ Z) (hz1 : z ≠ 1)
    (hc : c * z = z * c) : c ∈ M := by
  have := Tim77.mem_normalizer_of_commute_of_isTI H.ti hz hz1 hc
  rwa [H.normalizer_Z.1] at this

theorem _root_.CFSG.RankThree.GF2n.Stroth80.Ctx.exists_conj_mem_Z {B : Subgroup G}
    (hc : Ctx M Q Z B)
    {w : G} (hw : w ∈ Z ⊔ B) (hw1 : w ≠ 1) : ∃ h : G, h⁻¹ * w * h ∈ Z := by
  obtain ⟨g, hg⟩ := hc.conj
  have hgV : conjSubgroup g Z ≠ Z := hg ▸ hc.ne
  have hgQ : conjSubgroup g Z ≤ Q := hg ▸ hc.le
  have hinf : Q ⊓ Subgroup.centralizer (Z : Set G) = Q :=
    inf_eq_left.mpr fun y hy => Subgroup.mem_centralizer_iff.mpr fun z hz =>
      hc.hyp.toHyp79.V_central hz hy
  obtain ⟨-, ⟨hpart, -⟩, -⟩ := Tim78.tim78_2_18 (g := g) (W := Z ⊔ B) (H := Q ⊔ conjSubgroup g Q)
    hc.hyp.maxLocal hc.hyp.fitting hc.hyp.maxAb hc.hyp.toHyp79.sq_eq_one hc.hyp.ti hc.hyp.hQ
    hgV hgQ hc.hyp.q4 hinf.symm (by rw [hg]) rfl
  obtain ⟨U, ⟨⟨⟨h, rfl⟩, -⟩, hwU⟩, -⟩ := hpart w hw hw1
  exact ⟨h, mem_conjSubgroup.mp hwU⟩

theorem tiFusion_of_not_sit (H : StrothHyp M Q Z)
    (h : ∀ (X : Subgroup G) (x : G), ¬ Sit M Q Z X x) : TIFusion M Q Z := by
  intro g z hz hz1 hM
  by_contra hQ
  exact h _ _ (Sit.of_conj H hz hz1 hM hQ)

theorem TIFusion.mem_Q (hT : TIFusion M Q Z) (H : StrothHyp M Q Z) {z τ : G} (hz : z ∈ Z)
    (hz1 : z ≠ 1) (hcomm : τ * z = z * τ) (hconj : IsConj z τ) : τ ∈ Q := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hτM : τ ∈ M := mem_M_of_commute_Z H hz hz1 hcomm
  rw [← hc] at hτM ⊢
  exact hT c z hz hz1 hτM

theorem corB_setup_of_tiFusion (H : StrothHyp M Q Z) (hT : TIFusion M Q Z) {z : G} (hz : z ∈ Z)
    (hz1 : z ≠ 1) : CFSG.Timmesfeld.CorB.Setup z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 Q := by
    rw [H.hQ]
    exact (CFSG.RankThree.GF2n.inSubgroup_pCore_two M).1
  have hZQ : Z ≤ Q := H.Z_normal.1
  have hmemQ : ∀ τ : G, τ * z = z * τ → IsConj z τ → τ ∈ Q := fun τ hc hj =>
    hT.mem_Q H hz hz1 hc hj
  have hW : CFSG.Timmesfeld.CorB.weakClosure z ≤ Q := by
    unfold CFSG.Timmesfeld.CorB.weakClosure
    rw [Subgroup.closure_le]
    rintro τ ⟨hc, hj⟩
    exact hmemQ τ hc hj
  have hsq : z * z = 1 := by rw [← pow_two]; exact Z_sq H hz
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hsq
  refine ⟨orderOf_eq_prime (by rw [pow_two]; exact hsq) hz1, hQ2.to_le hW, ?_, ?_⟩
  · rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    have haZ : a ∈ Z := by
      have : ⁅CFSG.Timmesfeld.CorB.weakClosure z, CFSG.Timmesfeld.CorB.weakClosure z⁆ ≤ Z := by
        rw [Subgroup.commutator_le]
        intro x hx y hy
        exact comm_mem_Z H (hW hx) (hW hy)
      exact this ha
    have := Z_central H haZ (hW hb)
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.mpr this
  · intro τ hc hj hne
    have hτQ : τ ∈ Q := hmemQ τ hc hj
    have hzτ1 : τ ∉ Z → z * τ ≠ 1 := by
      intro hτZ h
      apply hτZ
      have : τ = z⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [this]
      exact Z.inv_mem hz
    by_cases hτZ : τ ∈ Z
    · have hzτ : z * τ ∈ Z := Z.mul_mem hz hτZ
      have hzτ1' : z * τ ≠ 1 := by
        intro h
        apply hne
        rw [eq_inv_of_mul_eq_one_right h, hzinv]
      obtain ⟨m, -, hm⟩ := Z_isConj H hz hz1 hzτ hzτ1'
      exact isConj_iff.mpr ⟨m, hm⟩
    · obtain ⟨g, hgQ, hτg⟩ := stroth_2_6 H hτQ hτZ
        (by
          obtain ⟨c', hc'⟩ := isConj_iff.mp hj
          exact ⟨c', z, hz, hc'.symm⟩)
      have hBne : conjSubgroup g Z ≠ Z := fun h => hτZ (h ▸ hτg)
      have hctx : Ctx M Q Z (conjSubgroup g Z) := ⟨H, ⟨g, rfl⟩, hgQ, hBne⟩
      have hw : z * τ ∈ Z ⊔ conjSubgroup g Z := Subgroup.mul_mem_sup hz hτg
      have hw1 := hzτ1 hτZ
      obtain ⟨h, hh⟩ := hctx.exists_conj_mem_Z hw hw1
      have hh1 : h⁻¹ * (z * τ) * h ≠ 1 := by
        intro h1
        apply hw1
        have : z * τ = h * (h⁻¹ * (z * τ) * h) * h⁻¹ := by group
        rw [this, h1]; group
      obtain ⟨m, -, hm⟩ := Z_isConj H hz hz1 hh hh1
      refine isConj_iff.mpr ⟨h * m, ?_⟩
      calc h * m * z * (h * m)⁻¹ = h * (m * z * m⁻¹) * h⁻¹ := by group
        _ = z * τ := by rw [hm]; group

end ZClass

end CFSG.RankThree.GF2n.Smith81
