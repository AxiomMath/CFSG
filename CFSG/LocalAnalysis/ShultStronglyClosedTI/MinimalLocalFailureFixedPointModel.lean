module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFixedPointModelHypotheses
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFixedPointModelRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFixedPointModelHull
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFixedPointModelCount
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.PairInvolutionFixedField

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.FixedPointModel

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type} [Group G] [Finite G]

theorem fixed_point_model_at_member
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} {u : G}
    (hQ : IsElemAbelian 2 (minimalLocalFailurePairActionPointHull H z))
    (hQclass : (minimalLocalFailurePairActionPointHull H z : Set G) \ {1} = conjugacyWithin H z)
    (hE4 : 4 ≤ Nat.card (minimalLocalFailurePairActionPointHull H z ⊓
      Subgroup.centralizer ({u} : Set G) : Subgroup G))
    (hYtop : Subgroup.centralizer ({u} : Set G) ≠ ⊤)
    (hYH : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    {tu : G} (htucomm : Commute tu u) (htuflip : tu ∈ rightPairFlipFiber H z beta)
    (horbit : {omega : rightCosetSpace H | ∃ y ∈ Subgroup.centralizer ({u} : Set G),
        rightCosetTranslate H (rightCosetMk H 1) y = omega} =
      {omega : rightCosetSpace H | rightCosetTranslate H omega u = omega})
    {r : G} (hr : r ∈ minimalLocalFailurePairActionPointHull H z ⊓
      Subgroup.centralizer ({u} : Set G)) (hr1 : r ≠ 1)
    (hEL : minimalLocalFailurePairActionPointHull H z ⊓ Subgroup.centralizer ({u} : Set G) ≤
      Subgroup.closure (conjugacyWithin (Subgroup.centralizer ({u} : Set G)) r)) :
    let B := pairPointStabilizer H beta
    let Q := minimalLocalFailurePairActionPointHull H z
    let Y := Subgroup.centralizer ({u} : Set G)
    let E := Q ⊓ Y
    let R := (CFSG.oddCore Y).map Y.subtype
    let α := rightCosetMk H 1
    let Δ := {omega : rightCosetSpace H | rightCosetTranslate H omega u = omega}
    let L := Subgroup.closure (conjugacyWithin Y r)
    2 ≤ twoRank L ∧ fusionStronglyEmbedded (H.subgroupOf L) ∧ R ≤ B ∧ ⁅R, L⁆ = ⊥ ∧
      (CFSG.oddCore L).map L.subtype ≤ R ⊓ (Subgroup.center L).map L.subtype ∧
      Nat.card {x : L | x ∈ H.subgroupOf L ∧ orderOf x = 2} = Nat.card E - 1 ∧
      Δ = {omega | ∃ l ∈ L, rightCosetTranslate H α l = omega} ∧
      (∃ ι : L ⧸ H.subgroupOf L → rightCosetSpace H, Function.Injective ι ∧
        Set.range ι = Δ ∧ ι (QuotientGroup.mk 1) = α ∧
        ∀ (l : L) (x : L ⧸ H.subgroupOf L),
          ι (l • x) = rightCosetTranslate H (ι x) (l : G)⁻¹) ∧
      ∃ i : ℕ, IsModelCosetAction L (H.subgroupOf L) (Nat.card E) i ∧
        Nat.card Δ = Nat.card E ^ i + 1 := by
  intro B Q Y E R α Δ L
  have hrQ : r ∈ (Q : Set G) \ {1} := ⟨hr.1, hr1⟩
  have hrc : r ∈ conjugacyWithin H z := hQclass ▸ hrQ
  obtain ⟨hr_fail, -, -⟩ := minimalLocalFailure_at_point_class_member h hrc
  have hrD : r ∈ involutionPointClass z := point_subgroup_class h.local_datum hQclass hrQ
  have hQH : Q ≤ H := point_subgroup_le h.local_datum.distinguished_mem hQclass
  have hEab : IsElemAbelian 2 E := isElemAbelian_of_le hQ inf_le_left
  obtain ⟨hrank, hstrong, -, hRL, hRH, hRLR, hcenter, hcoreM, -, hmodel, horbitL⟩ :=
    class_hull_rank_two hr_fail hcomm hsmallerR1 (lt_top_iff_ne_top.mpr hYtop) hr.2 hYH hEab
      hE4 hEL
  have hLY : L ≤ Y := properHull_le Y hr.2
  have hrL : r ∈ L := distinguished_mem_properHull Y r
  have htuY : tu ∈ Y := Subgroup.mem_centralizer_singleton_iff.mpr htucomm.eq
  have hRB : R ≤ B := by
    intro x hx
    have hconj : tu * x * tu⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp (subgroup_normalizes_properOddCore Y htuY) x).mp hx
    refine ⟨(mem_rightCosetStabilizer_iff H _ x).mpr ((translate_base_iff H x).mpr (hRH hx)),
      (mem_rightCosetStabilizer_iff H _ x).mpr ?_⟩
    rw [← htuflip.2, rightCosetTranslate_mul, show tu * x = (tu * x * tu⁻¹) * tu by group,
      ← rightCosetTranslate_mul, (translate_base_iff H _).mpr (hRH hconj)]
  have hRLZ : (CFSG.oddCore L).map L.subtype ≤ R ⊓ (Subgroup.center L).map L.subtype :=
    le_inf hRLR (Subgroup.map_mono hcenter)
  have hinvM : Nat.card {x : L | x ∈ H.subgroupOf L ∧ orderOf x = 2} = Nat.card E - 1 := by
    rw [← card_diff_one E]
    let rL : L := ⟨r, hrL⟩
    have hrM : rL ∈ H.subgroupOf L := hQH hr.1
    have hrinv : IsInvolution rL := by
      have hr2 : orderOf rL = 2 := (Subgroup.orderOf_mk r hrL).trans
        (order_two_of_mem_pointClass h.local_datum.distinguished_order hrD)
      exact ⟨(orderOf_eq_prime_iff.mp hr2).2, (orderOf_eq_prime_iff.mp hr2).1⟩
    have hforward : ∀ x : L, x ∈ H.subgroupOf L → orderOf x = 2 →
        (x : G) ∈ (E : Set G) \ {1} := by
      intro x hxM hx2
      have hxinv : IsInvolution x := ⟨(orderOf_eq_prime_iff.mp hx2).2,
        (orderOf_eq_prime_iff.mp hx2).1⟩
      obtain ⟨g, -, hg⟩ := IsStronglyEmbedded.involutions_conjugate_in
        (fusionStronglyEmbedded.to_native hstrong) hrM hrinv hxM hxinv
      have hxD : (x : G) ∈ involutionPointClass z := by
        rw [← hg]
        exact conj_mem_pointClass hrD (g : G)
      have hxQ : (x : G) ∈ (Q : Set G) \ {1} := by
        rw [← class_inter_point h.local_datum hQclass]
        exact ⟨hxD, hxM⟩
      exact ⟨⟨hxQ.1, hLY x.2⟩, hxQ.2⟩
    apply Nat.card_congr
    refine Equiv.ofBijective (fun x => ⟨(x : L), hforward x x.2.1 x.2.2⟩) ⟨?_, ?_⟩
    · intro x y hxy
      have h' := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h')
    · rintro ⟨w, hw⟩
      have hwD : w ∈ involutionPointClass z :=
        point_subgroup_class h.local_datum hQclass ⟨hw.1.1, hw.2⟩
      refine ⟨⟨⟨w, hEL hw.1⟩, hQH hw.1.1, ?_⟩, rfl⟩
      exact (Subgroup.orderOf_mk w (hEL hw.1)).trans
        (order_two_of_mem_pointClass h.local_datum.distinguished_order hwD)
  have hΔL : Δ = {omega | ∃ l ∈ L, rightCosetTranslate H α l = omega} :=
    horbit.symm.trans horbitL
  obtain ⟨ι, hιinj, hιrange, hι1, hι⟩ := orbit_coset_embedding H L
  rw [← hΔL] at hιrange
  obtain ⟨-, -, i, hi, hindex⟩ :=
    fixed_point_model_recognition hstrong hcoreM hcenter hmodel hinvM
  have hΔcard : Nat.card Δ = (H.subgroupOf L).index := by
    rw [← hιrange, Nat.card_range_of_injective hιinj]
    rfl
  exact ⟨hrank, hstrong, hRB, hRL, hRLZ, hinvM, hΔL, ⟨ι, hιinj, hιrange, hι1, hι⟩, i, hi,
    hΔcard.trans hindex⟩

theorem involution_centralizer_fixed_point_model
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {u : G} (huB : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2) :
    let B := pairPointStabilizer H beta
    let Q := minimalLocalFailurePairActionPointHull H z
    let D := involutionPointClass z
    let Y := Subgroup.centralizer ({u} : Set G)
    let E := Q ⊓ Y
    let q₀ := Nat.card E
    let R := (CFSG.oddCore Y).map Y.subtype
    let α := rightCosetMk H 1
    let Δ := {omega : rightCosetSpace H | rightCosetTranslate H omega u = omega}
    4 ≤ q₀ ∧ Y < ⊤ ∧
      (∀ ω₁ ∈ Δ, ∀ ω₂ ∈ Δ, ∀ ω₃ ∈ Δ, ∀ ω₄ ∈ Δ, ω₁ ≠ ω₂ → ω₃ ≠ ω₄ →
        ∃ y ∈ Y, rightCosetTranslate H ω₁ y = ω₃ ∧ rightCosetTranslate H ω₂ y = ω₄) ∧
      (Q ≤ Y → Nat.card Q = q₀) ∧ (¬ Q ≤ Y → Nat.card Q = q₀ ^ 2) ∧
      (∀ a ∈ (E : Set G) \ {1}, ∀ b ∈ (E : Set G) \ {1}, ∃ c ∈ H ⊓ Y, c⁻¹ * a * c = b) ∧
      Δ = {omega | ∃ y ∈ Y, rightCosetTranslate H α y = omega} ∧
      ∃ i : ℕ, (i = 1 ∨ i = 2 ∨ i = 3) ∧ Nat.card Δ = q₀ ^ i + 1 ∧
        Nat.card ↥(D ∩ (Y : Set G)) = (q₀ ^ i + 1) * (q₀ - 1) ∧
        Nat.card {p : G × G // p.1 ∈ D ∩ (Y : Set G) ∧ p.2 ∈ D ∩ (Y : Set G) ∧
            Odd (orderOf (p.1 * p.2))} =
          (q₀ ^ i + 1) * (q₀ - 1) * (q₀ ^ i * (q₀ - 1) + 1) ∧
        ∀ r ∈ (E : Set G) \ {1},
          let L := Subgroup.closure (conjugacyWithin Y r)
          E ≤ L ∧ 2 ≤ twoRank L ∧ fusionStronglyEmbedded (H.subgroupOf L) ∧ R ≤ B ∧
            ⁅R, L⁆ = ⊥ ∧ (CFSG.oddCore L).map L.subtype ≤ R ⊓ (Subgroup.center L).map L.subtype ∧
            D ∩ (Y : Set G) = conjugacyWithin Y r ∧
            Δ = {omega | ∃ l ∈ L, rightCosetTranslate H α l = omega} ∧
            (∃ ι : L ⧸ H.subgroupOf L → rightCosetSpace H, Function.Injective ι ∧
              Set.range ι = Δ ∧ ι (QuotientGroup.mk 1) = α ∧
              ∀ (l : L) (x : L ⧸ H.subgroupOf L),
                ι (l • x) = rightCosetTranslate H (ι x) (l : G)⁻¹) ∧
            IsModelCosetAction L (H.subgroupOf L) q₀ i := by
  intro B Q D Y E q₀ R α Δ
  obtain ⟨hQ, ⟨e, hQcard⟩, hQ4, hQclass, hXB, hXnormal, hXcyclic, hXcard, hXreg, htB⟩ :=
    proper_pair_fixed_field_hypotheses h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨hsimple, hnonab⟩ := minimalLocalFailure_nonabelian_simple h
  obtain ⟨hE4, hcentralcase, hnoncentral, -, -, hX₀reg, ⟨tu, -, htucomm, htuflip, -⟩, hYtop,
    hYH, horbit, hinherit, hDYcard⟩ :=
    pair_involution_fixed_field_and_orbit hsimple hnonab h.local_datum h.central_sylow hQ hQcard
      hQ4 hQclass hbeta ht hXB hXnormal hXcyclic hXcard hXreg htB huB hu
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, heven, -⟩ :=
    CyclicPair.proper_pair_cyclic_commutator h hcomm hsmallerR1 hbeta ht hproper
  have hq₀4 : 4 ≤ q₀ := hE4
  have hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hQ.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hat : ∀ r ∈ (E : Set G) \ {1}, _ := fun r hr =>
    fixed_point_model_at_member h hcomm hsmallerR1 (beta := beta) hQ hQclass hE4 hYtop hYH
      htucomm htuflip horbit hr.1 hr.2 (hinherit r hr.1 hr.2).2.2.2
  have hEne : (E : Set G) \ {1} |>.Nonempty := by
    have hpos : 0 < Nat.card ↥((E : Set G) \ {1}) := by
      rw [card_diff_one]
      change 0 < q₀ - 1
      omega
    obtain ⟨⟨r, hr⟩⟩ := (Nat.card_pos_iff.mp hpos).1
    exact ⟨r, hr⟩
  obtain ⟨r₀, hr₀⟩ := hEne
  obtain ⟨-, -, -, -, -, -, -, ⟨ι₀, -, hι₀range, -, hι₀⟩, i, hi, hΔcard⟩ := hat r₀ hr₀
  have hq₀ : 2 ≤ q₀ := by omega
  have hi123 : i = 1 ∨ i = 2 ∨ i = 3 := by
    rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have hDY : Nat.card ↥(D ∩ (Y : Set G)) = (q₀ ^ i + 1) * (q₀ - 1) := by
    rw [hDYcard, mul_comm]
    exact congrArg (· * (q₀ - 1)) hΔcard
  refine ⟨hE4, lt_top_iff_ne_top.mpr hYtop, ?_, fun hQY => (hcentralcase hQY).1.symm,
    fun hQY => (hnoncentral hQY).2.2, ?_, horbit.symm, i, hi123, hΔcard, hDY, ?_, ?_⟩
  ·
    intro ω₁ hω₁ ω₂ hω₂ ω₃ hω₃ ω₄ hω₄ h₁₂ h₃₄
    have hrange : ∀ ω ∈ Δ, ω ∈ Set.range ι₀ := fun ω hω => by
      rw [hι₀range]
      exact hω
    obtain ⟨x₁, rfl⟩ := hrange ω₁ hω₁
    obtain ⟨x₂, rfl⟩ := hrange ω₂ hω₂
    obtain ⟨x₃, rfl⟩ := hrange ω₃ hω₃
    obtain ⟨x₄, rfl⟩ := hrange ω₄ hω₄
    obtain ⟨l, hl₁, hl₂⟩ := hi.two_transitive x₁ x₂ x₃ x₄ (fun h' => h₁₂ (by rw [h']))
      (fun h' => h₃₄ (by rw [h']))
    refine ⟨(l : G)⁻¹, Y.inv_mem (properHull_le Y hr₀.1.2 l.2), ?_, ?_⟩
    · rw [← hl₁, hι₀]
    · rw [← hl₂, hι₀]
  ·
    intro a ha b hb
    obtain ⟨x, hx, -⟩ := hX₀reg a ha b hb
    exact ⟨x, ⟨pairPointStabilizer_le_point H beta (hXB x.2.1), x.2.2⟩, hx⟩
  ·
    rw [odd_product_pair_count h.local_datum hQab hQclass heven horbit, hDY]
    congr 1
    rw [add_mul, one_mul, Nat.add_sub_cancel]
  · intro r hr L
    obtain ⟨hrank, hstrong, hRB, hRL, hRLZ, -, hΔL, hιdata, j, hj, hΔj⟩ := hat r hr
    have hΔi : Nat.card Δ = q₀ ^ i + 1 := hΔcard
    have hΔj' : Nat.card Δ = q₀ ^ j + 1 := hΔj
    have hij : j = i := Nat.pow_right_injective hq₀ (by
      change q₀ ^ j = q₀ ^ i
      omega)
    subst hij
    exact ⟨(hinherit r hr.1 hr.2).2.2.2, hrank, hstrong, hRB, hRL, hRLZ,
      (hinherit r hr.1 hr.2).2.2.1, hΔL, hιdata, hj⟩

end CFSG.ShultStronglyClosedTI.FixedPointModel
