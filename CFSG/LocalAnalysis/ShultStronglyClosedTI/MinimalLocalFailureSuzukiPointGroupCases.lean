module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSuzukiPointGroupCount
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPairHullRegularComplement
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSuzukiPointGroupCoset
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSuzukiPointGroupDegree
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSuzukiPointGroupSylow

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.SuzukiExclusion

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.Blueprint CFSG.LieType.Ree
open CFSG.ShultStronglyClosedTI.ProperPairModel
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem relIndex_inf_left_of_le {H A N : Subgroup G} (hN : N ≤ H) :
    (H ⊓ A).relIndex N = A.relIndex N := by
  change ((H ⊓ A).subgroupOf N).index = (A.subgroupOf N).index
  congr 1
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => h.2, fun h => ⟨hN x.2, h⟩⟩

theorem odd_suzuki_norm {q : ℕ} (hq : Even q) : Odd (q ^ 2 - q + 1) := by
  have hle : q ≤ q ^ 2 := by nlinarith [Nat.zero_le q]
  have h1 : Even (q ^ 2 - q) :=
    (Nat.even_sub hle).mpr ⟨fun _ => hq, fun _ => (Nat.even_pow' two_ne_zero).mpr hq⟩
  exact h1.add_one

omit [Finite G] in
theorem relIndex_map_subtype {J : Subgroup G} (P : Subgroup J) :
    (P.map J.subtype).relIndex J = P.index := by
  change ((P.map J.subtype).subgroupOf J).index = _
  rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective J.subtype_injective]

theorem point_root_conj_mem
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    let Q := minimalLocalFailurePairActionPointHull H z
    let C := H ⊓ Subgroup.centralizer (Q : Set G)
    (∀ g ∈ H, ∀ y ∈ Q, g * y * g⁻¹ ∈ Q) ∧ H ≤ Subgroup.normalizer (Q : Set G) ∧
      ∀ g ∈ H, ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
  intro Q C
  obtain ⟨hQH, -, hQnormal, -⟩ := CyclicPair.proper_pair_point_root h hcomm hbeta ht hproper
  have hHQ : ∀ g ∈ H, ∀ y ∈ Q, g * y * g⁻¹ ∈ Q := fun g hg y hy =>
    hQnormal.conj_mem ⟨y, hQH hy⟩ hy ⟨g, hg⟩
  refine ⟨hHQ, fun g hg => Subgroup.mem_normalizer_iff.mpr fun y =>
    ⟨fun hy => hHQ g hg y hy, fun hy => ?_⟩, fun g hg c hc => ?_⟩
  · have := hHQ g⁻¹ (H.inv_mem hg) _ hy
    rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at this
  · refine ⟨H.mul_mem (H.mul_mem hg hc.1) (H.inv_mem hg),
      Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hy' := hHQ g⁻¹ (H.inv_mem hg) y hy
    rw [inv_inv] at hy'
    have hcy := Subgroup.mem_centralizer_iff.mp hc.2 _ hy'
    calc y * (g * c * g⁻¹) = g * ((g⁻¹ * y * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * y * g)) * g⁻¹ := by rw [hcy]
      _ = g * c * g⁻¹ * y := by group

theorem odd_relIndex_hull_centralizer_of_exclusion
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hBinv : ∃ u ∈ pairPointStabilizer H beta, orderOf u = 2)
    (hSz : ∃ (m : ℕ) (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (2 * m + 1) ∧
      Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
      Nonempty (minimalLocalFailureProperPairHull H z beta t ≃* suzukiGroup m k))
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u) :
    Odd ((Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G)).relIndex
      (pairPointStabilizer H beta)) := by
  obtain ⟨m, k, _, _, hk, hm, -, -, ψ, -, -, -, hQK, hQZ, T, hTM, -, -, -, hBT, -, -, hTU, -,
    -, -, -, e, he⟩ := proper_pair_suzuki_structure h hcomm hsmallerR1 hbeta ht hproper hSz
  obtain ⟨-, hHN, -⟩ := point_root_conj_mem h hcomm hbeta ht hproper
  have hTbot : T ≤ Subgroup.centralizer ((⊥ : Subgroup G) : Set G) := fun x _ =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Subgroup.mem_bot.mp hy, one_mul, mul_one]
  have h1 := (relIndex_centralizer_dvd_of_normalizes hm hk ψ (fun x hx => (hTM hx).2) hQK hTU
    hQZ hTbot (inf_bot_eq T) e he (N := pairPointStabilizer H beta)
    (by rw [sup_bot_eq]; exact hBT) ((pairPointStabilizer_le_point H beta).trans hHN)).2
  rwa [hull_centralizer_eq_of_exclusion h hcomm hsmallerR1 hbeta ht hproper hBinv hSz hexcl,
    Subgroup.inf_relIndex_left]

theorem suzuki_point_action_cases_of_exclusion
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hBinv : ∃ u ∈ pairPointStabilizer H beta, orderOf u = 2)
    (hSz : ∃ (m : ℕ) (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (2 * m + 1) ∧
      Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
      Nonempty (minimalLocalFailureProperPairHull H z beta t ≃* suzukiGroup m k))
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u)
    {T : Subgroup G}
    (hall : ∀ S : Sylow 2 ↥(H ⊓ minimalLocalFailureProperPairHull H z beta t),
      (S : Subgroup _).map (H ⊓ minimalLocalFailureProperPairHull H z beta t).subtype = T)
    (P : Sylow 2 ↥(Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G)))
    {u : G}
    (huP : u ∈ (P : Subgroup _).map
      (Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G)).subtype)
    (huZ : ∀ y ∈ (P : Subgroup _).map
      (Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G)).subtype,
      u * y = y * u)
    (hu : orderOf u = 2) :
    let K := minimalLocalFailureProperPairHull H z beta t
    let Q := minimalLocalFailurePairActionPointHull H z
    let C := H ⊓ Subgroup.centralizer (Q : Set G)
    let J₀ := Subgroup.centralizer (K : Set G)
    let Pg := (P : Subgroup ↥J₀).map J₀.subtype
    let NS := C ⊓ Subgroup.normalizer (u • (Q : Set G))
    (∀ c ∈ NS, ∃ y ∈ Q, ∀ σ ∈ u • (Q : Set G), c⁻¹ * σ * c = σ * y) ∧
      (((∀ y ∈ Q, ∃ c ∈ NS, ∀ σ ∈ u • (Q : Set G), c⁻¹ * σ * c = σ * y) ∧
          ∃ S : Sylow 2 ↥H, (S : Subgroup ↥H).map H.subtype ≤ C) ∨
        ((∀ c ∈ NS, ∀ σ ∈ u • (Q : Set G), c⁻¹ * σ * c = σ) ∧
          (∃ S : Sylow 2 ↥C, (S : Subgroup ↥C).map C.subtype = T ⊔ Pg) ∧
          Odd (C.relIndex (H ⊓ Subgroup.normalizer ((T ⊔ Pg : Subgroup G) : Set G))))) ∧
      Odd (C.relIndex H) := by
  intro K Q C J₀ Pg NS
  let B := pairPointStabilizer H beta
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, k, _, _, hk, hm, hQcard, hKB, ψ, -, -, -, hQK, hQZ, T₀, hT₀M, hT₀2, hall₀, hT₀card,
    hBT₀, hNeq, hT₀B, hTU, -, -, hTQ, hsq, e, he⟩ :=
    proper_pair_suzuki_structure h hcomm hsmallerR1 hbeta ht hproper hSz
  obtain rfl : T = T₀ := by rw [← hall default, hall₀ default]
  have hJ : J₀ = B ⊓ Subgroup.centralizer (Q : Set G) :=
    hull_centralizer_eq_of_exclusion h hcomm hsmallerR1 hbeta ht hproper hBinv hSz hexcl
  have hTK : T ≤ K := fun x hx => (hT₀M hx).2
  obtain ⟨hNCK, hTJ, hTJc⟩ := point_centralizer_normalizer_eq hNeq hBT₀ hT₀B hTQ hTK hJ
  obtain ⟨-, -, hQnormal, hQab, -, hQ4, -⟩ :=
    CyclicPair.proper_pair_point_root h hcomm hbeta ht hproper
  obtain ⟨-, -, -, -, hXB, -, -, -, hXreg, -⟩ :=
    FixedPointModel.proper_pair_fixed_field_hypotheses h hcomm hsmallerR1 hbeta ht hproper
  have hBH : B ≤ H := pairPointStabilizer_le_point H beta
  have hJB : J₀ ≤ B := by rw [hJ]; exact inf_le_left
  have hJQ : J₀ ≤ Subgroup.centralizer (Q : Set G) := by rw [hJ]; exact inf_le_right
  have hPgJ : Pg ≤ J₀ := Subgroup.map_subtype_le _
  have huJ : u ∈ J₀ := hPgJ huP
  have huB : u ∈ B := hJB huJ
  have hreg := fun v (hvB : v ∈ B) (hv : orderOf v = 2) =>
    proper_pair_hull_regular_complement_of_conclusions h hcomm hsmallerR1 hbeta ht hproper hexcl
      hvB hv
  obtain ⟨hHQ, hHN, hHC⟩ := point_root_conj_mem h hcomm hbeta ht hproper
  have hCQ : C ≤ Subgroup.centralizer (Q : Set G) := inf_le_right
  have hCH : C ≤ H := inf_le_left
  have hQcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hQab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨τ, hτ, hτker⟩ := exists_coset_translation hCQ u
  have hact : ∀ c ∈ NS, ∃ y ∈ Q, ∀ σ ∈ u • (Q : Set G), c⁻¹ * σ * c = σ * y := fun c hc =>
    ⟨_, (τ (⟨c, hc⟩ : NS)⁻¹).2, fun σ hσ => conj_coset_eq_mul hQcomm hCQ τ hτ ⟨c, hc⟩ hσ⟩
  have hXK : rightInvolutionCommutatorSubgroup t (pairOddCore H beta) ≤ K := hKB ▸ inf_le_left
  have hXH : rightInvolutionCommutatorSubgroup t (pairOddCore H beta) ≤ H := hXB.trans hBH
  have hXu : ∀ x ∈ rightInvolutionCommutatorSubgroup t (pairOddCore H beta), x * u = u * x :=
    fun x hx => Subgroup.mem_centralizer_iff.mp huJ x (hXK hx)
  have hXreg' : ∀ a ∈ (Q : Set G) \ {1}, ∀ b ∈ (Q : Set G) \ {1},
      ∃ x ∈ rightInvolutionCommutatorSubgroup t (pairOddCore H beta), x * a * x⁻¹ = b :=
    fun a ha b hb => by
      obtain ⟨⟨x, hx⟩, hxab, -⟩ := hXreg a ha b hb
      exact ⟨x⁻¹, Subgroup.inv_mem _ hx, by rw [inv_inv]; exact hxab⟩
  have hBodd : Odd (J₀.relIndex B) :=
    odd_relIndex_hull_centralizer_of_exclusion h hcomm hsmallerR1 hbeta ht hproper hBinv hSz hexcl
  have hPodd : Odd (Pg.relIndex J₀) := by
    rw [relIndex_map_subtype]
    exact Nat.not_even_iff_odd.mp fun h2 => P.not_dvd_index (even_iff_two_dvd.mp h2)
  obtain ⟨-, hHB⟩ :=
    pair_stabilizer_relIndex_eq_of_exclusion h hcomm hsmallerR1 hbeta ht hproper hBinv hSz hexcl
  have hqeven : Even (Nat.card Q) := hQcard ▸ (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  have hqpos : 0 < Nat.card Q := by have : 4 ≤ Nat.card Q := hQ4; omega
  rcases translation_range_eq_bot_or_top τ hτ (fun x hx c hc => hHC x (hXH hx) c hc)
    (fun x hx y hy => hHQ x (hXH hx) y hy) hXu hXreg' with hbot | htop
  ·
    have hτ1 : ∀ c : NS, τ c = 1 := fun c => by
      have hc : τ c ∈ τ.range := ⟨c, rfl⟩
      rwa [hbot, Subgroup.mem_bot] at hc
    have htriv' : ∀ c ∈ NS, ∀ σ ∈ u • (Q : Set G), c⁻¹ * σ * c = σ := fun c hc σ hσ => by
      rw [conj_coset_eq_mul hQcomm hCQ τ hτ ⟨c, hc⟩ hσ, hτ1, OneMemClass.coe_one, mul_one]
    have htriv : ∀ c ∈ C, u⁻¹ * (c * u * c⁻¹) ∈ Q → c * u * c⁻¹ = u := fun c hcC hcu => by
      have hcN := mem_coset_normalizer_of_conj_mem hCQ hcC hcu
      have h2 := (hτker ⟨c, hcC, hcN⟩).mp (hτ1 _)
      rw [Subgroup.mem_centralizer_singleton_iff.mp h2, mul_inv_cancel_right]
    have hTP : T ≤ Subgroup.centralizer (Pg : Set G) := hTJc.trans (Subgroup.centralizer_le hPgJ)
    have hinfP : T ⊓ Pg = ⊥ := eq_bot_iff.mpr ((inf_le_inf_left T hPgJ).trans hTJ.le)
    have hPgT : Pg ≤ Subgroup.normalizer (T : Set G) := hPgJ.trans (hJB.trans hBT₀)
    have hPg2 : IsPGroup 2 Pg := P.isPGroup'.map _
    have hW2 : IsPGroup 2 (T ⊔ Pg : Subgroup G) :=
      IsPGroup.to_sup_of_normal_left' hT₀2 hPg2 hPgT
    have hdecomp : ∀ v ∈ T ⊔ Pg, v ^ 2 = 1 → ∃ y ∈ Q, ∃ j ∈ Pg, v = y * j := by
      intro v hv hv2
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left T Pg hPgT] at hv
      obtain ⟨y, hy, j, hj, rfl⟩ := Set.mem_mul.mp hv
      have hyj : Commute y j := (Subgroup.mem_centralizer_iff.mp (hTP hy) j hj).symm
      have h1 : y ^ 2 * j ^ 2 = 1 := by rw [← hyj.mul_pow, hv2]
      have hmem : y ^ 2 ∈ T ⊓ Pg := ⟨T.pow_mem hy 2, by
        rw [eq_inv_of_mul_eq_one_left h1]
        exact Pg.inv_mem (Pg.pow_mem hj 2)⟩
      rw [hinfP, Subgroup.mem_bot] at hmem
      exact ⟨y, hsq y hy hmem, j, hj, rfl⟩
    have hX : ∀ y ∈ Q, y ≠ 1 → ∃ x : G, x * y * x⁻¹ ≠ y ∧ x * y * x⁻¹ ∈ Q ∧
        (∀ c ∈ C, x * c * x⁻¹ ∈ C) ∧ x * u = u * x ∧ ∀ j ∈ Pg, x * j = j * x := by
      intro y hy hy1
      obtain ⟨y'', hy''1, hy''y⟩ := exists_ne_ne_of_three_le_card (Ω := Q) (by
        have : 4 ≤ Nat.card Q := hQ4
        omega) 1 ⟨y, hy⟩
      have hy''1' : (y'' : G) ≠ 1 := fun h1 => hy''1 (Subtype.ext h1)
      have hy''y' : (y'' : G) ≠ y := fun h1 => hy''y (Subtype.ext h1)
      obtain ⟨x, hxX, hx⟩ := hXreg' y ⟨hy, hy1⟩ y'' ⟨y''.2, hy''1'⟩
      exact ⟨x, by rw [hx]; exact hy''y', by rw [hx]; exact y''.2,
        fun c hc => hHC x (hXH hxX) c hc, hXu x hxX,
        fun j hj => Subgroup.mem_centralizer_iff.mp (hPgJ hj) x (hXK hxX)⟩
    have hnorm : ∀ g : G, g * u * g⁻¹ ∈ Pg → g ∈ Subgroup.normalizer (K : Set G) := by
      intro g hg
      have hv2 : orderOf (g * u * g⁻¹) = 2 := by
        rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
        exact hu
      have h2 := localHull_map_conj z u g
      rw [(hreg u huB hu).1, (hreg _ (hJB (hPgJ hg)) hv2).1] at h2
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h2
    have hWN : T ⊔ Pg ≤ C ⊓ Subgroup.normalizer (K : Set G) := by
      rw [hNCK]
      exact sup_le_sup_left hPgJ T
    have hWodd : ¬ 2 ∣ (T ⊔ Pg).relIndex (C ⊓ Subgroup.normalizer (K : Set G)) := by
      rw [hNCK, relIndex_sup_eq hTJc hTJ hPgJ]
      exact fun h2 => (Nat.not_even_iff_odd.mpr hPodd) (even_iff_two_dvd.mpr h2)
    have hWC : T ⊔ Pg ≤ C := hWN.trans inf_le_left
    obtain ⟨S₁, hS₁⟩ := (hW2.comap_subtype (K := C)).exists_le_sylow
    have hS₁eq : (S₁ : Subgroup C).map C.subtype = T ⊔ Pg :=
      eq_of_trivial_translation hCQ (Subgroup.mem_sup_right huP)
        (hu ▸ pow_orderOf_eq_one u) hdecomp (hPgJ.trans hJQ) hX htriv hnorm
        hWN hWodd (Subgroup.map_subtype_le _) (S₁.isPGroup'.map _)
        (fun w hw => ⟨⟨w, hWC hw⟩, hS₁ hw, rfl⟩)
    have hNodd := (relIndex_centralizer_dvd_of_normalizes hm hk ψ hTK hQK hTU hQZ hTP hinfP e he
      (N := H ⊓ Subgroup.normalizer ((T ⊔ Pg : Subgroup G) : Set G)) inf_le_right
      (inf_le_left.trans hHN)).2
    rw [← relIndex_inf_left_of_le (H := H) inf_le_left] at hNodd
    refine ⟨hact, Or.inr ⟨htriv', ⟨S₁, hS₁eq⟩, hNodd⟩, ?_⟩
    rw [relIndex_eq_relIndex_normalizer hCH hHC S₁ hS₁eq]
    exact hNodd
  ·
    have hfull : ∀ y ∈ Q, ∃ c ∈ NS, ∀ σ ∈ u • (Q : Set G), c⁻¹ * σ * c = σ * y := by
      intro y hy
      obtain ⟨c, hc⟩ : (⟨y, hy⟩ : Q) ∈ τ.range := htop ▸ Subgroup.mem_top _
      refine ⟨((c⁻¹ : NS) : G), (c⁻¹).2, fun σ hσ => ?_⟩
      rw [conj_coset_eq_mul hQcomm hCQ τ hτ c⁻¹ hσ, inv_inv, hc]
    have hTu : T ≤ Subgroup.centralizer ({u} : Set G) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp huJ x (hTK hx))
    have hCuK : C ⊓ Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (K : Set G) :=
      fun c hc => by
        have := mem_normalizer_of_mem_centralizer_hull (z := z) hc.2
        rwa [(hreg u huB hu).1] at this
    have hCu : C ⊓ Subgroup.centralizer ({u} : Set G) =
        T ⊔ (J₀ ⊓ Subgroup.centralizer ({u} : Set G)) := by
      have h1 : C ⊓ Subgroup.centralizer ({u} : Set G) =
          (C ⊓ Subgroup.normalizer (K : Set G)) ⊓ Subgroup.centralizer ({u} : Set G) :=
        le_antisymm (fun x hx => ⟨⟨hx.1, hCuK hx⟩, hx.2⟩) fun x hx => ⟨hx.1.1, hx.2⟩
      apply SetLike.coe_injective
      rw [h1, hNCK, Subgroup.coe_inf,
        Subgroup.coe_mul_of_right_le_normalizer_left T J₀ (hJB.trans hBT₀),
        ← Subgroup.mul_inf_assoc T J₀ _ hTu,
        Subgroup.coe_mul_of_right_le_normalizer_left T _ ((inf_le_left.trans hJB).trans hBT₀)]
    have hTL : T ≤ Subgroup.centralizer
        ((J₀ ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) : Set G) :=
      hTJc.trans (Subgroup.centralizer_le inf_le_left)
    have hTLinf : T ⊓ (J₀ ⊓ Subgroup.centralizer ({u} : Set G)) = ⊥ :=
      eq_bot_iff.mpr ((inf_le_inf_left T inf_le_left).trans hTJ.le)
    have hNScard : Nat.card NS =
        Nat.card Q ^ 3 * Nat.card (J₀ ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) := by
      rw [card_coset_normalizer hCQ u τ hτker, htop, Subgroup.card_top, hCu,
        card_sup_of_commute hTL hTLinf, hT₀card]
      ring
    have hPu : Pg ≤ J₀ ⊓ Subgroup.centralizer ({u} : Set G) := fun y hy =>
      ⟨hPgJ hy, Subgroup.mem_centralizer_singleton_iff.mpr (huZ y hy).symm⟩
    have hLodd : Odd ((J₀ ⊓ Subgroup.centralizer ({u} : Set G)).relIndex J₀) :=
      hPodd.of_dvd_nat (Subgroup.relIndex_dvd_of_le_left J₀ hPu)
    have hodd := odd_relIndex_of_card hBH hJB inf_le_left (inf_le_left.trans hCH) hqpos hHB
      (odd_suzuki_norm hqeven) hBodd hLodd hNScard
    obtain ⟨hS, hCodd⟩ := exists_sylow_le_of_odd_relIndex inf_le_left hCH hodd
    exact ⟨hact, Or.inl ⟨hfull, hS⟩, hCodd⟩

end CFSG.ShultStronglyClosedTI.SuzukiExclusion
