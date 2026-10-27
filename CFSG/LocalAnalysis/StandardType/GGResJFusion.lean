module

public import CFSG.LocalAnalysis.StandardType.GGResJTwA5Sylow
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
import CFSG.GroupTheory.ConjTransport
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291NilpGrp

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open scoped Pointwise

theorem ggFusion_exists_automizer {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {Bs J : Subgroup G} (hBs : IsMulCommutative Bs) (hBp : ∀ b ∈ Bs, b ^ p = 1)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hA : ∀ a ∈ ggAutomizer J Bs, ∀ k : ℕ, a ^ p ^ k = 1 → a = 1)
    {u n : G} (hu : u ∈ Bs) (hn : n ∈ J) (hnu : n * u * n⁻¹ ∈ Bs) :
    ∃ a ∈ ggAutomizer J Bs, ((a ⟨u, hu⟩ : ↥Bs) : G) = n * u * n⁻¹ := by
  classical
  have hcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBs.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hBsp : IsPGroup p Bs := fun b => ⟨1, Subtype.ext (by simpa using hBp b b.2)⟩
  have hHmul : ((Bs ⊔ J : Subgroup G) : Set G) = (Bs : Set G) * (J : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right Bs J hN
  set v : G := n * u * n⁻¹ with hv
  set Y : Subgroup G := (Bs ⊔ J) ⊓ Subgroup.centralizer ({v} : Set G) with hYdef
  have hBsY : Bs ≤ Y := fun b hb =>
    ⟨Subgroup.mem_sup_left hb, Subgroup.mem_centralizer_singleton_iff.mpr (hcomm b hb v hnu)⟩
  have hnY : ∀ b ∈ Bs, n * b * n⁻¹ ∈ Y := by
    intro b hb
    refine Subgroup.mem_inf.mpr ⟨(Bs ⊔ J).mul_mem ((Bs ⊔ J).mul_mem
      (Subgroup.mem_sup_right hn) (Subgroup.mem_sup_left hb))
      (Subgroup.mem_sup_right (J.inv_mem hn)), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hv]
    calc n * b * n⁻¹ * (n * u * n⁻¹) = n * (b * u) * n⁻¹ := by group
      _ = n * (u * b) * n⁻¹ := by rw [hcomm b hb u hu]
      _ = n * u * n⁻¹ * (n * b * n⁻¹) := by group
  obtain ⟨Q, hQ⟩ := (hBsp.comap_of_injective Y.subtype Subtype.coe_injective).exists_le_sylow
  set S : Subgroup G := (Q : Subgroup Y).map Y.subtype with hSdef
  have hSp : IsPGroup p S := Q.isPGroup'.map _
  have hSY : S ≤ Y := Subgroup.map_subtype_le _
  have hBsS : Bs ≤ S := fun b hb => ⟨⟨b, hBsY hb⟩, hQ (Subgroup.mem_comap.mpr hb), rfl⟩
  have hSC' : S ≤ Subgroup.centralizer (Bs : Set G) :=
    ggPGroup_le_centralizer_of_automizer hBs hBp hSC hN hA hSp hBsS (hSY.trans inf_le_left)
  have hPp : IsPGroup p (Bs.map (MulAut.conj n).toMonoidHom) := hBsp.map _
  obtain ⟨Q₁, hQ₁⟩ := (hPp.comap_of_injective Y.subtype Subtype.coe_injective).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq Y Q₁ Q
  have hcS : ∀ b ∈ Bs, (c : G) * (n * b * n⁻¹) * (c : G)⁻¹ ∈ S := by
    intro b hb
    have hb' : (⟨n * b * n⁻¹, hnY b hb⟩ : Y) ∈ (Q₁ : Subgroup Y) :=
      hQ₁ (Subgroup.mem_comap.mpr ⟨b, hb, rfl⟩)
    have hmem : MulAut.conj c • (⟨n * b * n⁻¹, hnY b hb⟩ : Y) ∈ (Q : Subgroup Y) := by
      rw [← hc, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hb'
    exact ⟨_, hmem, rfl⟩
  have hzBs : ∀ b ∈ Bs, ((c : G) * n) * b * ((c : G) * n)⁻¹ ∈ Bs := by
    intro b hb
    have he : ((c : G) * n) * b * ((c : G) * n)⁻¹ = (c : G) * (n * b * n⁻¹) * (c : G)⁻¹ := by
      group
    refine hSC _ (he ▸ hSC' (hcS b hb)) ?_
    rw [conj_pow, hBp b hb, mul_one, mul_inv_cancel]
  have hzN : (c : G) * n ∈ Subgroup.normalizer (Bs : Set G) :=
    CFSG.GroupTheory.mem_normalizer_of_conj_mem hzBs
  have hzu : ((c : G) * n) * u * ((c : G) * n)⁻¹ = v := by
    have hcv : (c : G) * v = v * (c : G) := Subgroup.mem_centralizer_singleton_iff.mp c.2.2
    calc ((c : G) * n) * u * ((c : G) * n)⁻¹ = (c : G) * v * (c : G)⁻¹ := by rw [hv]; group
      _ = v := by rw [hcv, mul_inv_cancel_right]
  have hzH : (c : G) * n ∈ ((Bs ⊔ J : Subgroup G) : Set G) :=
    (Bs ⊔ J).mul_mem c.2.1 (Subgroup.mem_sup_right hn)
  rw [hHmul] at hzH
  obtain ⟨b, hb, j, hj, hbj⟩ := Set.mem_mul.mp hzH
  have hjN : j ∈ Subgroup.normalizer (Bs : Set G) := by
    have hj' : j = b⁻¹ * ((c : G) * n) := by rw [← hbj]; group
    rw [hj']
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hb)) hzN
  refine ⟨Bs.normalizerMonoidHom ⟨j, hjN⟩, Subgroup.subset_closure ⟨j, hj, hjN, fun _ => rfl⟩,
    ?_⟩
  change j * u * j⁻¹ = v
  calc j * u * j⁻¹ = b⁻¹ * (((c : G) * n) * u * ((c : G) * n)⁻¹) * b := by rw [← hbj]; group
    _ = b⁻¹ * v * b := by rw [hzu]
    _ = v := by rw [mul_assoc, hcomm v hnu b hb, ← mul_assoc, inv_mul_cancel, one_mul]

theorem ggExists_conj_automizer {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {Bs J : Subgroup G} (hBs : IsMulCommutative Bs) (hBp : ∀ b ∈ Bs, b ^ p = 1)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hA : ∀ a ∈ ggAutomizer J Bs, ∀ k : ℕ, a ^ p ^ k = 1 → a = 1)
    {Q : Subgroup G} (hQ : IsPGroup p Q) (hQJ : Q ≤ J) :
    ∃ g ∈ J, ∀ w ∈ Q, w ^ p = 1 → g * w * g⁻¹ ∈ Bs ∧
      ∀ (hw : g * w * g⁻¹ ∈ Bs), ∀ m ∈ J, m * w * m⁻¹ ∈ Q →
        ∃ a ∈ ggAutomizer J Bs, ((a ⟨g * w * g⁻¹, hw⟩ : ↥Bs) : G) = g * (m * w * m⁻¹) * g⁻¹ := by
  obtain ⟨g, hg, hgC⟩ := ggSylow_exists_conj_mem_centralizer hBs hBp hSC hN hA hQ hQJ
  refine ⟨g, hg, fun w hw hwp => ⟨hSC _ (hgC w hw) (by rw [conj_pow, hwp, mul_one,
    mul_inv_cancel]), fun hu m hm hmw => ?_⟩⟩
  have hmwp : (m * w * m⁻¹) ^ p = 1 := by rw [conj_pow, hwp, mul_one, mul_inv_cancel]
  have hu' : (g * m * g⁻¹) * (g * w * g⁻¹) * (g * m * g⁻¹)⁻¹ ∈ Bs := by
    have he : (g * m * g⁻¹) * (g * w * g⁻¹) * (g * m * g⁻¹)⁻¹ = g * (m * w * m⁻¹) * g⁻¹ := by
      group
    rw [he]
    exact hSC _ (hgC _ hmw) (by rw [conj_pow, hmwp, mul_one, mul_inv_cancel])
  obtain ⟨a, ha, he⟩ := ggFusion_exists_automizer hBs hBp hSC hN hA hu
    (J.mul_mem (J.mul_mem hg hm) (J.inv_mem hg)) hu'
  refine ⟨a, ha, he.trans ?_⟩
  group

theorem GGResHyp.automizer_J_ne_bot_of_dvd {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hpJ : p ∣ Nat.card J) :
    ggAutomizer J Bs ≠ ⊥ := by
  intro hA1
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs := hH.1.tableB_facts.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hH.1.2.1.2.2.2
  have hJperf : commutator ↥J = ⊤ := hH.1.2.2.1.2.2.2.2.2.1.2.2.1
  have hA : ∀ a ∈ ggAutomizer J Bs, ∀ k : ℕ, a ^ p ^ k = 1 → a = 1 := by
    intro a ha _ _
    rwa [hA1, Subgroup.mem_bot] at ha
  have hnpc : CFSG.HasNormalPComplement p ↥J := by
    refine CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291N.hasNormalPComplement_of_fix_omega
      hp2 fun Q hQ n hn w hw hwp => ?_
    obtain ⟨g, -, hg⟩ := ggExists_conj_automizer hBs.1 hBs.2 hSC hH.Bs_le_normalizer_J hA
      (hQ.map J.subtype) (Subgroup.map_subtype_le Q)
    have hnw : (n : G) * w * (n : G)⁻¹ ∈ Q.map J.subtype :=
      ⟨n * w * n⁻¹, (Subgroup.mem_normalizer_iff.mp hn w).mp hw, rfl⟩
    obtain ⟨hu, h⟩ := hg w ⟨w, hw, rfl⟩ (by simpa using congrArg Subtype.val hwp)
    obtain ⟨a, ha, he⟩ := h hu n n.2 hnw
    rw [hA1, Subgroup.mem_bot] at ha
    subst ha
    simp only [MulAut.one_apply] at he
    exact Subtype.ext (mul_left_cancel (mul_right_cancel he)).symm
  have : Group.IsPerfect ↥J := ⟨hJperf⟩
  obtain ⟨N, hN, hc, hq⟩ := hnpc
  have := hN
  have hNtop : N = ⊤ := by
    rw [← QuotientGroup.subsingleton_iff]
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    have := hnt
    exact Group.IsPerfect.not_isNilpotent (↥J ⧸ N) hq.isNilpotent
  rw [hNtop, Subgroup.card_top] at hc
  exact (Nat.Prime.coprime_iff_not_dvd hp).mp hc hpJ

theorem GGResHyp.automizer_J_ne_bot (hP : GGStdSubPrimeInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) : ggAutomizer J Bs ≠ ⊥ :=
  hH.automizer_J_ne_bot_of_dvd (hP G p B x L D J hH.1.1 hH.1.2.2)

section Refl

theorem GGResHyp.automizer_J_refl_of_exact3_nonsingular_L (hP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hL : ¬ ggSingularWeylOrder p (Nat.card ↥(ggAutomizer L Bs)))
    (hD : GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny) (hBs : Nat.card Bs < p ^ 6) :
    Nat.card Bs = p ^ 5 ∧
      ∃ τ : MulAut ↥Bs, GGIsReflection p τ ∧ ggAutomizer J Bs = Subgroup.zpowers τ :=
  (hH.automizer_J_bot_or_refl_of_exact3_nonsingular_L hL hD hBs).resolve_left
    (hH.automizer_J_ne_bot hP)

theorem GGResHyp.automizer_J_refl_of_exact3_nonsingular_K (hP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hK : ¬ ggSingularWeylOrder p (Nat.card ↥(ggAutomizer K Bs)))
    (hD : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) (hBs : Nat.card Bs < p ^ 6) :
    Nat.card Bs = p ^ 5 ∧
      ∃ τ : MulAut ↥Bs, GGIsReflection p τ ∧ ggAutomizer J Bs = Subgroup.zpowers τ :=
  (hH.automizer_J_bot_or_refl_of_exact3_nonsingular_K hK hD hBs).resolve_left
    (hH.automizer_J_ne_bot hP)

end Refl

theorem GGResHyp.card_lt_of_card_gamma_J_lt {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (h3 : Nat.card (ggGamma J hH.Bs_le_normalizer_J).range < p ^ 3) : Nat.card Bs < p ^ 6 := by
  have hmul := NbrU63.card_range_ggGamma_mul_card_inf hH.Bs_le_normalizer_J
  have hC := hH.1.card_bstar_inf_centralizer_J_le
  rw [← hmul, show p ^ 6 = p ^ 3 * p ^ 3 by ring]
  exact Nat.mul_lt_mul_of_lt_of_le h3 hC (pow_pos (Fact.out : p.Prime).pos 3)

theorem GGResHyp.card_gamma_J_eq_sq_of_lt {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (h3 : Nat.card (ggGamma J hH.Bs_le_normalizer_J).range < p ^ 3) :
    Nat.card (ggGamma J hH.Bs_le_normalizer_J).range = p ^ 2 := by
  have hp : p.Prime := Fact.out
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hpg : IsPGroup p (ggGamma J hH.Bs_le_normalizer_J).range :=
    (CFSG.Open.IsElemAbelian.isPGroup hBs).of_surjective
      (ggGamma J hH.Bs_le_normalizer_J).rangeRestrict
      (ggGamma J hH.Bs_le_normalizer_J).rangeRestrict_surjective
  obtain ⟨k, hk⟩ := hpg.exists_card_eq
  have h2 := hH.sq_le_card_gamma_J
  rw [hk] at h2 h3 ⊢
  have hk2 : 2 ≤ k := (Nat.pow_le_pow_iff_right hp.one_lt).mp h2
  have hk3 : k < 3 := (Nat.pow_lt_pow_iff_right hp.one_lt).mp h3
  rw [show k = 2 by omega]

theorem GGResHyp.torusLift_rank_le_one_of_card_gamma_sq {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (h5 : Nat.card Bs = p ^ 5)
    (h2 : Nat.card (ggGamma J hH.Bs_le_normalizer_J).range = p ^ 2) {R : Type} [Group R]
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* R) {r : ℕ} (hT : GGTorusLift p r R) : r ≤ 1 := by
  have hp : p.Prime := Fact.out
  have hBs := hH.1.tableB_facts.2.1
  have hJperf : commutator ↥J = ⊤ := hH.1.2.2.1.2.2.2.2.2.1.2.2.1
  have hC := CFSG.LocalAnalysis.GLTheoremA.S265.SF.pow_mul_card_le_of_torusLift
    (Ω := G) (K := J) (D := Bs ⊓ Subgroup.centralizer (J : Set G)) hp hJperf θ hT
    (CFSG.Open.IsElemAbelian.mono hBs inf_le_left) inf_le_right
  have hrank : CFSG.Open.GLATwoLocalRank p G = LargeEvenTwoLocalRank p G := rfl
  rw [hrank] at hC
  have hm : LargeEvenTwoLocalRank p G ≤ 4 := by
    have hle : p ^ (LargeEvenTwoLocalRank p G - 2) ≤ p ^ 2 := by
      rw [← h2]
      exact hH.pow_le_card_gamma_J
    have := (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
    omega
  have hmul := NbrU63.card_range_ggGamma_mul_card_inf hH.Bs_le_normalizer_J
  rw [h2, h5, show p ^ 5 = p ^ 2 * p ^ 3 by ring] at hmul
  rw [Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) hmul, ← pow_add] at hC
  have := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hC.trans (Nat.pow_le_pow_right hp.pos hm))
  omega

@[expose] def GGResJOneReflLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ∀ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ) (M : CoxeterMatrix (Fin N)),
    GGTBTorRowAt p lab r m N C M → r ≤ 1

theorem GGResHyp.false_of_not_oneReflLabel (hLift : GGTBTorLiftRows) {G : Type} [Group G]
    [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (h5 : Nat.card Bs = p ^ 5)
    (h2 : Nat.card (ggGamma J hH.Bs_le_normalizer_J).range = p ^ 2)
    (hJ : GGInnerDiagOnLabel (fun p lab => ¬ GGResJOneReflLabel p lab) p Bs J) : False := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  obtain ⟨-, lab, -, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => ¬ GGResJOneReflLabel p lab)
    (P' := fun R _ _ _ => ∃ r, 2 ≤ r ∧ GGTorusLift p r R)
    (fun lab hΛ h => by
      simp only [GGResJOneReflLabel, not_forall, not_le, exists_prop] at h
      obtain ⟨r, m, N, C, M, hrow, hr⟩ := h
      exact (hLift p lab r m N C M hp hp2 hΛ hrow).mono fun _ _ _ _ hT => ⟨r, hr, hT⟩)
    (fun _ _ _ _ _ _ hP => hP.1) hJ
  obtain ⟨R, _, I, F, -, -, θ, -, r, hr, hT⟩ := largeEvenRawDatum_exists hraw
  have := hH.torusLift_rank_le_one_of_card_gamma_sq h5 h2 θ hT
  omega

@[expose] def GGResJOneReflInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G) (hH : GGResHyp p B Bs x L D J y K),
    Nat.card Bs = p ^ 5 → GGInnerDiagOnLabel GGResJOneReflLabel p Bs J →
    ∀ τ : MulAut ↥Bs, GGIsReflection p τ → ggAutomizer J Bs = Subgroup.zpowers τ →
    Nat.card (ggGamma J hH.Bs_le_normalizer_J).range = p ^ 2 → False

theorem GGResHyp.false_of_oneRefl (hLift : GGTBTorLiftRows) (hR : GGResJOneReflInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (h5 : Nat.card Bs = p ^ 5) (hJ : GGInnerDiagOn Bs J) {τ : MulAut ↥Bs}
    (hτ : GGIsReflection p τ) (hA : ggAutomizer J Bs = Subgroup.zpowers τ)
    (h2 : Nat.card (ggGamma J hH.Bs_le_normalizer_J).range = p ^ 2) : False := by
  rcases (hJ.label GGResJOneReflLabel p).elim_or with hJ1 | hJ2
  · exact hR G p B Bs x L D J y K hH h5 hJ1 τ hτ hA h2
  · exact hH.false_of_not_oneReflLabel hLift h5 h2 hJ2

end CFSG.StandardType

end
