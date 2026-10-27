module

public import CFSG.LocalAnalysis.StandardType.GGTBJSpBlock
import CFSG.LocalAnalysis.StandardType.GGClassicalBlockSpSelected
import CFSG.LocalAnalysis.StandardType.GGTBJSpCoreAux
import CFSG.LocalAnalysis.StandardType.GGTBJSpParabolicAut
import CFSG.LocalAnalysis.StandardType.GGHalfCentGroup
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSpRes
import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
import CFSG.Adapters.RankTwoModelTransports
import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagModel
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockSpIsoOneLinear
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagLinear
public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUDvd
public import CFSG.Fischer.Classification.Recognition.Basic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open CFSG.Open (StatedSp StatedSL)
open CFSG.SeitzReduction.SymplecticPilot
open CFSG.StandardType.ClassicalPosition
open CFSG.StandardType.ClassicalBlocks
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)

theorem ggCommonJSpSplit_component_block {K : Type} [Field K] [Finite K] {f p r : ℕ}
    (hK : Nat.card K = 2 ^ f) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f - 1)
    (hr : 3 ≤ r) {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    (f₀ : Fin r → Multiplicative (ZMod p)) {J : Subgroup (StatedSp r K)}
    (hJ : CFSG.Assembly.IsComponentOf J
      (Subgroup.centralizer ({TableBSymp.spTorusSp (m := r) hζ f₀} : Set (StatedSp r K)))) :
    ∃ lam : Multiplicative (ZMod p),
      ((lam = 1 ∧
          Nonempty (↥J ≃* StatedSp (Nat.card {i : Fin r // f₀ i = 1}) K)) ∨
        (lam ≠ 1 ∧ 1 ≤ Nat.card {i : Fin r // f₀ i = lam ∨ f₀ i = lam⁻¹} ∧
          Nonempty (↥J ≃*
            Matrix.SpecialLinearGroup
              (Fin (Nat.card {i : Fin r // f₀ i = lam ∨ f₀ i = lam⁻¹})) K))) ∧
      (∀ g : Fin r → Multiplicative (ZMod p),
        (∀ j ∈ J,
            TableBSymp.spTorusSp (m := r) hζ g * j = j * TableBSymp.spTorusSp (m := r) hζ g) ↔
          ((lam = 1 ∧ ∀ i, f₀ i = 1 → g i = 1) ∨
            (lam ≠ 1 ∧ ∃ c : Multiplicative (ZMod p), ∀ i,
              (f₀ i = lam → g i = c) ∧ (f₀ i = lam⁻¹ → g i = c⁻¹)))) := by
  classical
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hK
  have hK2 : Nat.card K ≠ 2 := by
    intro h2
    have hf1 : f = 1 := by
      have h : 2 ^ f = 2 ^ 1 := by rw [pow_one, ← hK, h2]
      exact Nat.pow_right_injective (le_refl 2) h
    rw [hf1, pow_one] at hpq
    exact hp.ne_one (Nat.dvd_one.mp (by simpa using hpq))
  have hpqK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpq
  let t : Fin r → Kˣ := fun i => TableBSymp.zmodPowHom hζ (f₀ i)
  have hsp : TableBSymp.spTorusSp hζ f₀ = diagSp K r t := ggTBJSpC_spTorusSp_eq_diagSp hζ f₀
  have hJ' : CFSG.Assembly.IsComponentOf J
      (Subgroup.centralizer ({diagSp K r t} : Set (StatedSp r K))) := by
    rw [← hsp]; exact hJ
  have hoddS : Odd (orderOf (diagSp K r t : StatedSp r K)) := by
    rw [← orderOf_injective (Subgroup.subtype (StatedSp r K))
      (Subgroup.subtype_injective (StatedSp r K))]
    exact ggTBJSpB_odd_orderOf_diagSp t
  obtain ⟨ε, hε, hJε⟩ :=
    CFSG.StandardType.ClassicalBlocks.exists_isPrimAdjIdemIn_isComponentOf_glBlockCentralizer_Sp
      (diagSp K r t) hoddS J hJ'
  obtain ⟨v, hεv, hv, hconst, hsym, lam0, hlam0ne, hsupp0⟩ :=
    exists_eq_diagonal_of_isPrimAdjIdemIn_diagSp t hε
  have hvne : ∃ a, v a = 1 := by
    by_contra h
    apply hε.2.2.1
    rw [hεv]
    ext a b
    have h0 : v a = 0 := by
      rcases hv a with h0 | h1
      · exact h0
      · exact absurd h1 (fun h1 => h (⟨a, h1⟩))
    simp [Matrix.diagonal_apply, h0]
  have hb0 : ∃ b0, v b0 = 1 ∧ diagSpEntry t b0 = lam0 := by
    obtain ⟨a0, ha0⟩ := hvne
    rcases hsupp0 a0 ha0 with h | h
    · exact ⟨a0, ha0, h⟩
    · refine ⟨Equiv.sumComm (Fin r) (Fin r) a0, ?_, ?_⟩
      · rw [← hsym a0]; exact ha0
      · rw [diagSpEntry_sumComm t a0, h, inv_inv]
  have hsupp1 : ∀ a, (diagSpEntry t a = lam0 ∨ diagSpEntry t a = lam0⁻¹) → v a = 1 := by
    obtain ⟨b0, hb0v, hb0e⟩ := hb0
    intro a ha
    rcases ha with h | h
    · rw [hconst a b0 (h.trans hb0e.symm)]; exact hb0v
    · have h1 : diagSpEntry t (Equiv.sumComm (Fin r) (Fin r) a) = lam0 := by
        rw [diagSpEntry_sumComm t a, h, inv_inv]
      rw [hsym a, hconst _ _ (h1.trans hb0e.symm)]
      exact hb0v
  let lamK : Kˣ := Units.mk0 lam0 hlam0ne
  have hlam_val : (lamK : K) = lam0 := rfl
  have hlam_inv_val : ((lamK⁻¹ : Kˣ) : K) = lam0⁻¹ := by
    rw [Units.val_inv_eq_inv_val, hlam_val]
  have hlam_iff : ∀ u : Kˣ, u = lamK ↔ (u : K) = lam0 := by
    intro u; constructor
    · intro h; rw [h, hlam_val]
    · intro h; exact Units.ext h
  have hlam_inv_iff : ∀ u : Kˣ, u = lamK⁻¹ ↔ (u : K) = lam0⁻¹ := by
    intro u; constructor
    · intro h; rw [h, hlam_inv_val]
    · intro h; exact Units.ext (by rw [h, hlam_inv_val])
  have hmem : lamK ∈ (TableBSymp.zmodPowHom hζ).range := by
    obtain ⟨b0, -, hb0e⟩ := hb0
    rcases b0 with i | i
    · refine ⟨f₀ i, ?_⟩
      apply Units.ext
      rw [hlam_val, ← hb0e]
      rfl
    · refine ⟨(f₀ i)⁻¹, ?_⟩
      apply Units.ext
      rw [map_inv, hlam_val, ← hb0e, diagSpEntry_inr, Units.val_inv_eq_inv_val]
  obtain ⟨lam, hlam_eq⟩ := hmem
  have hlamK_one_iff : lamK = 1 ↔ lam = 1 := by
    constructor
    · intro h
      exact ReflSp.zmodPowHom_injective hζ hζo (by rw [hlam_eq, h, map_one])
    · intro h; rw [← hlam_eq, h, map_one]
  have hlammem_iff : ∀ i : Fin r, TableBSymp.zmodPowHom hζ (f₀ i) = lamK ↔ f₀ i = lam := by
    intro i; constructor
    · intro h; exact ReflSp.zmodPowHom_injective hζ hζo (h.trans hlam_eq.symm)
    · intro h; rw [h, hlam_eq]
  have hlammem_inv_iff : ∀ i : Fin r,
      TableBSymp.zmodPowHom hζ (f₀ i) = lamK⁻¹ ↔ f₀ i = lam⁻¹ := by
    intro i; constructor
    · intro h
      apply ReflSp.zmodPowHom_injective hζ hζo
      rw [h, map_inv, hlam_eq]
    · intro h; rw [h, map_inv, hlam_eq]
  have hclass_inl : ∀ i : Fin r,
      (diagSpEntry t (Sum.inl i) = lam0 ∨ diagSpEntry t (Sum.inl i) = lam0⁻¹) ↔
        (f₀ i = lam ∨ f₀ i = lam⁻¹) := by
    intro i
    rw [diagSpEntry_inl]
    change ((TableBSymp.zmodPowHom hζ (f₀ i) : K) = lam0 ∨
      (TableBSymp.zmodPowHom hζ (f₀ i) : K) = lam0⁻¹) ↔
      (f₀ i = lam ∨ f₀ i = lam⁻¹)
    rw [← hlam_iff (TableBSymp.zmodPowHom hζ (f₀ i)),
      ← hlam_inv_iff (TableBSymp.zmodPowHom hζ (f₀ i)), hlammem_iff i, hlammem_inv_iff i]
  have hclass_inr : ∀ i : Fin r,
      (diagSpEntry t (Sum.inr i) = lam0 ∨ diagSpEntry t (Sum.inr i) = lam0⁻¹) ↔
        (f₀ i = lam ∨ f₀ i = lam⁻¹) := by
    intro i
    rw [diagSpEntry_inr]
    change (((TableBSymp.zmodPowHom hζ (f₀ i))⁻¹ : Kˣ) : K) = lam0 ∨
      (((TableBSymp.zmodPowHom hζ (f₀ i))⁻¹ : Kˣ) : K) = lam0⁻¹ ↔
      (f₀ i = lam ∨ f₀ i = lam⁻¹)
    have h2 : (((TableBSymp.zmodPowHom hζ (f₀ i))⁻¹ : Kˣ) : K) = lam0 ↔ f₀ i = lam⁻¹ := by
      rw [Units.val_inv_eq_inv_val, inv_eq_iff_eq_inv,
        ← hlam_inv_iff (TableBSymp.zmodPowHom hζ (f₀ i)), hlammem_inv_iff i]
    have h3 : (((TableBSymp.zmodPowHom hζ (f₀ i))⁻¹ : Kˣ) : K) = lam0⁻¹ ↔ f₀ i = lam := by
      rw [Units.val_inv_eq_inv_val, inv_inj,
        ← hlam_iff (TableBSymp.zmodPowHom hζ (f₀ i)), hlammem_iff i]
    rw [h2, h3]
    exact or_comm
  have hsupp_iff : ∀ a : Fin r ⊕ Fin r, v a = 1 ↔
      (∃ i : Fin r, a = Sum.inl i ∧ (f₀ i = lam ∨ f₀ i = lam⁻¹)) ∨
      (∃ i : Fin r, a = Sum.inr i ∧ (f₀ i = lam ∨ f₀ i = lam⁻¹)) := by
    intro a
    constructor
    · intro ha
      rcases hsupp0 a ha with h | h
      · rcases a with i | i
        · exact Or.inl ⟨i, rfl, (hclass_inl i).mp (Or.inl h)⟩
        · exact Or.inr ⟨i, rfl, (hclass_inr i).mp (Or.inl h)⟩
      · rcases a with i | i
        · exact Or.inl ⟨i, rfl, (hclass_inl i).mp (Or.inr h)⟩
        · exact Or.inr ⟨i, rfl, (hclass_inr i).mp (Or.inr h)⟩
    · rintro (⟨i, rfl, hi⟩ | ⟨i, rfl, hi⟩)
      · exact hsupp1 _ ((hclass_inl i).mpr hi)
      · exact hsupp1 _ ((hclass_inr i).mpr hi)
  let m : ℕ := Nat.card {i : Fin r // f₀ i = lam ∨ f₀ i = lam⁻¹}
  have hcard_supp : Fintype.card {a : Fin r ⊕ Fin r // v a = 1} = 2 * m := by
    let fwd : {a : Fin r ⊕ Fin r // v a = 1} →
        {i : Fin r // f₀ i = lam ∨ f₀ i = lam⁻¹} × Bool := fun a => by
      rcases a with ⟨a, ha⟩
      rcases a with i | i
      · exact (⟨i, (hclass_inl i).mp (hsupp0 _ ha)⟩, true)
      · exact (⟨i, (hclass_inr i).mp (hsupp0 _ ha)⟩, false)
    let bwd : {i : Fin r // f₀ i = lam ∨ f₀ i = lam⁻¹} × Bool →
        {a : Fin r ⊕ Fin r // v a = 1} := fun q => by
      rcases q with ⟨⟨i, hi⟩, b⟩
      cases b
      · exact ⟨Sum.inr i, hsupp1 _ ((hclass_inr i).mpr hi)⟩
      · exact ⟨Sum.inl i, hsupp1 _ ((hclass_inl i).mpr hi)⟩
    have hleft : Function.LeftInverse bwd fwd := by
      rintro ⟨⟨i | i, ha⟩⟩ <;> exact Subtype.ext rfl
    have hright : Function.RightInverse bwd fwd := by
      rintro ⟨⟨i, hi⟩, b⟩
      cases b <;> exact Prod.ext (Subtype.ext rfl) rfl
    have hbij : Function.Bijective fwd := ⟨hleft.injective, hright.surjective⟩
    have h1 : Fintype.card {a : Fin r ⊕ Fin r // v a = 1} =
        Fintype.card ({i : Fin r // f₀ i = lam ∨ f₀ i = lam⁻¹} × Bool) :=
      Fintype.card_congr (Equiv.ofBijective fwd hbij)
    rw [h1, Fintype.card_prod, Fintype.card_bool]
    simp [m, Nat.mul_comm]
  have hfinrank : Module.finrank K (LinearMap.range (Matrix.toLin' ε)) = 2 * m := by
    rw [hεv, finrank_diagonal_eq_card v hv, hcard_supp]
  let b : GL (Fin r ⊕ Fin r) K := ((diagSp K r t : StatedSp r K) : GL (Fin r ⊕ Fin r) K)
  let Gε : Subgroup (StatedSp r K) := glBlockCentralizer (StatedSp r K).subtype {b} ε
  have hbSp : b ∈ StatedSp r K := (diagSp K r t).2
  have hJε' : CFSG.Assembly.IsComponentOf J Gε := hJε
  have hmpos : 1 ≤ m := by
    obtain ⟨a, ha⟩ := hvne
    have hne : Nonempty {i : Fin r // f₀ i = lam ∨ f₀ i = lam⁻¹} := by
      rcases (hsupp_iff a).mp ha with ⟨i, -, hi⟩ | ⟨i, -, hi⟩
      · exact ⟨⟨i, hi⟩⟩
      · exact ⟨⟨i, hi⟩⟩
    haveI := hne
    have hpos : 0 < m := by
      show 0 < Nat.card {i : Fin r // f₀ i = lam ∨ f₀ i = lam⁻¹}
      exact Nat.card_pos
    omega
  by_cases hlam_one : lam = 1
  ·
    have hlamK_one : lamK = 1 := hlamK_one_iff.mpr hlam_one
    have hlam0_one : lam0 = 1 := by
      rw [← hlam_val]
      rw [hlamK_one]
      rfl
    have hbε : b * ε = ε := by
      have hbm : (b : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
          Matrix.diagonal (diagSpEntry t) := by
        simpa [b, mat_apply] using mat_diagSp t
      rw [hεv, hbm, Matrix.diagonal_mul_diagonal]
      congr 1
      funext a
      by_cases ha : v a = 1
      · have h1 : diagSpEntry t a = 1 := by
          rcases hsupp0 a ha with h | h
          · rw [h, hlam0_one]
          · rw [h, hlam0_one, inv_one]
        rw [h1, one_mul, ha]
      · rcases hv a with h0 | h1
        · rw [h0, mul_zero]
        · exact absurd h1 ha
    obtain ⟨n1, hrank1, ⟨eiso⟩⟩ :=
      blockGroup_iso_Sp_one (K := K) b hbSp (ggTBJSpB_odd_orderOf_diagSp t) hε hbε
    have hn1 : n1 = m := by
      have h2 : 2 * n1 = 2 * m := by rw [hrank1, hfinrank]
      omega
    have hqA : CFSG.Assembly.IsQuasisimple ↥(StatedSp n1 K) :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mpr
        (isQuasisimple_statedSp_of_not_small (K := K) (by omega)
          (fun h => hK2 h.2) (fun h => hK2 h.2))
    have hqG : CFSG.Assembly.IsQuasisimple ↥Gε :=
      CFSG.Assembly.IsQuasisimple.of_mulEquiv eiso hqA
    have hJG : J = Gε := CFSG.StandardType.GGHalf.eq_of_isComponentOf_isQuasisimple hqG hJε'
    have hm_eq : m = Nat.card {i : Fin r // f₀ i = 1} := by
      show Nat.card {i : Fin r // f₀ i = lam ∨ f₀ i = lam⁻¹} = Nat.card {i : Fin r // f₀ i = 1}
      refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl (Fin r)) ?_)
      intro i
      rw [hlam_one]
      simp
    have hiso : Nonempty (↥J ≃* StatedSp (Nat.card {i : Fin r // f₀ i = 1}) K) := by
      refine ⟨(MulEquiv.subgroupCongr hJG).trans ?_⟩
      rw [← hm_eq, ← hn1]
      exact eiso
    have hfix : ∀ g : Fin r → Multiplicative (ZMod p),
        (∀ j ∈ J,
            TableBSymp.spTorusSp hζ g * j = j * TableBSymp.spTorusSp hζ g) ↔
          ((lam = 1 ∧ ∀ i, f₀ i = 1 → g i = 1) ∨
            (lam ≠ 1 ∧ ∃ c : Multiplicative (ZMod p), ∀ i,
              (f₀ i = lam → g i = c) ∧ (f₀ i = lam⁻¹ → g i = c⁻¹))) := by
      intro g
      constructor
      · intro hcomm
        refine Or.inl ⟨hlam_one, ?_⟩
        intro i hi
        have hti : t i = 1 := by
          show TableBSymp.zmodPowHom hζ (f₀ i) = 1
          rw [hi, map_one]
        have hvi : v (Sum.inl i) = 1 := by
          apply hsupp1
          left
          rw [diagSpEntry_inl, hti]
          exact hlam0_one.symm
        have hmemG : TableBSymp.spSwapSp i ∈ Gε := by
          have h := ggTBJSpB_spSwapSp_mem_glBlockCentralizer_diagSp t v hv hsym hti hvi
          simpa [Gε, b, hεv] using h
        have hmemJ : TableBSymp.spSwapSp i ∈ J := by
          rw [hJG]; exact hmemG
        have hc := hcomm _ hmemJ
        have hconj : TableBSymp.spSwapSp i * TableBSymp.spTorusSp hζ g *
            (TableBSymp.spSwapSp i)⁻¹ = TableBSymp.spTorusSp hζ g := by
          rw [hc.symm, mul_assoc, mul_inv_cancel, mul_one]
        have hconj2 := ggTBJSpC_conj_spSwapSp (K := K) hζ i g
        have hsgn : SpCoord.sgnAut i g = g :=
          TableBSymp.spTorusSp_injective (m := r) hζ hζo (hconj2.symm.trans hconj)
        have hgi : g i = (g i)⁻¹ := by
          have h := congrFun hsgn i
          simpa [SpCoord.sgnAut_apply] using h.symm
        have hsq : g i * g i = 1 := by
          nth_rewrite 2 [hgi]
          exact mul_inv_cancel (g i)
        have hp1 : (g i) ^ p = 1 := by
          rw [← ofAdd_toAdd (g i), ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
            ofAdd_zero]
        have hdvd2 : orderOf (g i) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
        have hdvdp : orderOf (g i) ∣ p := orderOf_dvd_of_pow_eq_one hp1
        have hcop : Nat.Coprime 2 p := hpodd.coprime_two_left
        have hone : orderOf (g i) = 1 := by
          refine Nat.dvd_one.mp ?_
          have h := Nat.dvd_gcd hdvd2 hdvdp
          rwa [hcop] at h
        exact orderOf_eq_one_iff.mp hone
      · rintro (⟨-, hg1⟩ | ⟨hne, -⟩)
        · intro j hj
          have hjG : j ∈ Gε := by rw [hJG] at hj; exact hj
          have hjmem : ((j : StatedSp r K) : GL (Fin r ⊕ Fin r) K) ∈
              Subgroup.centralizer ({b} : Set (GL (Fin r ⊕ Fin r) K)) ⊓
                glFixing (1 - Matrix.diagonal v) := by
            have h := hjG
            simp only [Gε, glBlockCentralizer, Subgroup.mem_comap, hεv] at h
            exact h
          have hjfix : ((j : StatedSp r K) : GL (Fin r ⊕ Fin r) K) *
              (1 - Matrix.diagonal v) = 1 - Matrix.diagonal v :=
            (Subgroup.mem_inf.mp hjmem).2
          have hjcomm : ((j : StatedSp r K) : GL (Fin r ⊕ Fin r) K) * b =
              b * ((j : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :=
            Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hjmem).1
          have hbm : (b : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
              Matrix.diagonal (diagSpEntry t) := by
            simpa [b, mat_apply] using mat_diagSp t
          have hjm : (((j : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
                Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * Matrix.diagonal (diagSpEntry t) =
              Matrix.diagonal (diagSpEntry t) *
                (((j : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
                  Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
            have h := congrArg (fun y : GL (Fin r ⊕ Fin r) K =>
              ((y : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))) hjcomm
            simpa [hbm, Units.val_mul] using h
          let x : Fin r → Kˣ := fun i => TableBSymp.zmodPowHom hζ (g i)
          have hdv_one : ∀ a, v a = 1 → diagSpEntry x a = 1 := by
            intro a ha
            rcases (hsupp_iff a).mp ha with ⟨i, rfl, hi⟩ | ⟨i, rfl, hi⟩
            · rcases hi with h | h
              · have hg1' : g i = 1 := hg1 i (by rwa [hlam_one] at h)
                simp [diagSpEntry, x, hg1']
              · have h' : f₀ i = 1 := by rwa [hlam_one, inv_one] at h
                have hg1' : g i = 1 := hg1 i h'
                simp [diagSpEntry, x, hg1']
            · rcases hi with h | h
              · have hg1' : g i = 1 := hg1 i (by rwa [hlam_one] at h)
                simp [diagSpEntry, x, hg1']
              · have h' : f₀ i = 1 := by rwa [hlam_one, inv_one] at h
                have hg1' : g i = 1 := hg1 i h'
                simp [diagSpEntry, x, hg1']
          have hx : ∀ a b, v a = 1 → v b = 1 → diagSpEntry t a = diagSpEntry t b →
              diagSpEntry x a = diagSpEntry x b := by
            intro a b ha hb _
            rw [hdv_one a ha, hdv_one b hb]
          have hkey := ggTBJSpB_diagonal_mul_eq_mul_of_block v (diagSpEntry t) (diagSpEntry x)
            (((j : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
              Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) hv hjfix hjm hconst hx
          refine Subtype.ext ?_
          rw [Subgroup.coe_mul, Subgroup.coe_mul, ggTBJSpC_spTorusSp_eq_diagSp hζ g]
          refine Units.ext ?_
          rw [Units.val_mul, Units.val_mul, ← mat_apply (diagSp K r x), ← mat_apply j, mat_diagSp]
          exact hkey
        · exact absurd hlam_one hne
    exact ⟨lam, Or.inl ⟨hlam_one, hiso⟩, hfix⟩
  ·
    have hlamK_ne : lamK ≠ 1 := fun h => hlam_one (hlamK_one_iff.mp h)
    have hlam0_ne : lam0 ≠ 1 := by
      intro h
      apply hlamK_ne
      apply Units.ext
      rw [hlam_val, h]
      rfl
    have hlam_ne_inv : lam ≠ lam⁻¹ := by
      intro h
      apply hlam_one
      have h2 : lam * lam = 1 := by
        nth_rewrite 2 [h]
        exact mul_inv_cancel lam
      have hp1 : lam ^ p = 1 := by
        rw [← ofAdd_toAdd lam, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
          ofAdd_zero]
      have hdvd2 : orderOf lam ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
      have hdvdp : orderOf lam ∣ p := orderOf_dvd_of_pow_eq_one hp1
      have hcop : Nat.Coprime 2 p := hpodd.coprime_two_left
      have hone : orderOf lam = 1 := by
        refine Nat.dvd_one.mp ?_
        have hh := Nat.dvd_gcd hdvd2 hdvdp
        rwa [hcop] at hh
      exact orderOf_eq_one_iff.mp hone
    have hlamK_ne_inv : lamK ≠ lamK⁻¹ := by
      intro h
      apply hlam_ne_inv
      apply ReflSp.zmodPowHom_injective hζ hζo
      rw [map_inv, hlam_eq]
      exact h
    let A : Subalgebra K (Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) :=
      Algebra.adjoin K (Units.val '' ({b} : Set (GL (Fin r ⊕ Fin r) K)))
    let Gr : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K := Matrix.fromBlocks 0 1 (-1) 0
    have hneg : (-1 : K) = 1 := CharTwo.neg_eq 1
    have hnegm : (-1 : Matrix (Fin r) (Fin r) K) = 1 := by
      ext i j; rw [Matrix.neg_apply, Matrix.one_apply]
      by_cases h : i = j <;> simp [h, hneg]
    have hGG : Gr * Gr = 1 := by
      rw [show Gr = Matrix.fromBlocks (0 : Matrix (Fin r) (Fin r) K) 1 (-1) 0 from rfl,
        Matrix.fromBlocks_multiply, hnegm]
      simp [Matrix.fromBlocks_one]
    have hG : IsUnit Gr.det := by
      rw [isUnit_iff_ne_zero]; intro h0
      have h := congrArg Matrix.det hGG; rw [Matrix.det_mul, h0, zero_mul] at h; simp at h
    have hGh : Matrix.transpose (Gr.map (RingHom.id K)) = Gr := by
      rw [show (RingHom.id K : K → K) = id from rfl, Matrix.map_id]; ext a b
      rcases a with i | i <;> rcases b with j | j <;>
        simp [Gr, hnegm, Matrix.one_apply, eq_comm]
    have hS : ∀ s ∈ ({b} : Set (GL (Fin r ⊕ Fin r) K)),
        ∀ s' ∈ ({b} : Set (GL (Fin r ⊕ Fin r) K)), Commute s s' := by
      intro s hs s' hs'; rw [Set.mem_singleton_iff] at hs hs'; rw [hs, hs']
    have hSU : ∀ s ∈ ({b} : Set (GL (Fin r ⊕ Fin r) K)),
        Matrix.transpose ((s : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map (RingHom.id K)) *
          Gr * (s : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = Gr := by
      intro s hs; rw [Set.mem_singleton_iff] at hs
      subst hs
      simpa [Gr, Matrix.map_id] using CFSG.Open.StatedAPI.mem_statedSp_iff.mp hbSp
    obtain ⟨e1, he1, -, hcases⟩ :=
      exists_isPrimIdemIn_of_isPrimAdjIdemIn (RingHom.id K) (fun x => rfl) hG hGh hS hSU hε
    have hGt : Matrix.transpose Gr = Gr := by simpa [Matrix.map_id] using hGh
    have hstar : IsPrimIdemIn A (formAdj (RingHom.id K) Gr e1) :=
      TableC.isPrimIdemIn_formAdj_gram K Gr hGt hG hSU hS he1
    rcases hcases with heq | ⟨hne, hstar_ne, hεsum⟩
    · exfalso
      have hprim : IsPrimIdemIn A ε := heq ▸ he1
      have hbε : (b : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * ε = ε :=
        diagSp_mul_eq_of_isPrimAdjIdemIn t hε hprim
      have hbm : (b : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
          Matrix.diagonal (diagSpEntry t) := by
        simpa [b, mat_apply] using mat_diagSp t
      obtain ⟨a0, ha0⟩ := hvne
      have h2 : diagSpEntry t a0 = 1 := by
        have h := congrArg (fun M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K => M a0 a0) hbε
        rw [hbm, hεv, Matrix.diagonal_mul_diagonal] at h
        simp only [Matrix.diagonal_apply, if_pos rfl] at h
        rw [ha0, mul_one] at h
        exact h
      rcases hsupp0 a0 ha0 with h | h
      · exact hlam0_ne (h.symm.trans h2)
      · exact hlam0_ne (inv_eq_one.mp (h.symm.trans h2))
    · obtain ⟨d, mm, E, hEfield, hEfin, hd, hEcard, hrank, hdeg, ⟨eiso⟩⟩ :=
        blockGroup_iso_Sp_linear b hbSp (ggTBJSpB_odd_orderOf_diagSp t) hε he1 hstar
          (fun h => hstar_ne h.symm) hεsum
      letI : Field E := hEfield
      letI : Fintype E := hEfin
      have hEpow : Nat.card E = 2 ^ (f * d) := by
        rw [Nat.card_eq_fintype_card, hEcard]
        have hK' : Fintype.card K = 2 ^ f := by rw [← Nat.card_eq_fintype_card]; exact hK
        rw [hK', pow_mul]
      letI : CharP E 2 := charP_two_of_card hEpow
      have hcompJ : IsComponentOf (J.subgroupOf Gε) ⊤ := by
        have hC₀ : (J.subgroupOf Gε).map Gε.subtype = J := by
          rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hJε'.1]
        have hH : (⊤ : Subgroup ↥Gε).map Gε.subtype = Gε := by
          rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
        rw [← CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff Gε.subtype_injective,
          hC₀, hH]
        exact hJε'
      have himg : IsComponentOf ((J.subgroupOf Gε).map eiso.toMonoidHom) ⊤ := by
        have h := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
          (f := eiso.toMonoidHom) eiso.injective).2 hcompJ
        rwa [Subgroup.map_top_of_surjective _ eiso.surjective] at h
      have hSL : (J.subgroupOf Gε).map eiso.toMonoidHom = StatedSL mm E :=
        eq_statedSL_of_isComponentOf_top himg
      have hJinv : ∀ y ∈ Gε, y * y = 1 → y ∈ J := by
        intro y hy hy2
        have hsq : eiso ⟨y, hy⟩ * eiso ⟨y, hy⟩ = 1 := by
          have h1 : (⟨y, hy⟩ : Gε) * ⟨y, hy⟩ = 1 := by
            apply Subtype.ext
            exact hy2
          rw [← map_mul, h1, map_one]
        have hmem : eiso ⟨y, hy⟩ ∈ StatedSL mm E := ggTBJSpB_mem_statedSL_of_mul_self hsq
        rw [← hSL] at hmem
        obtain ⟨k, hk, hke⟩ := Subgroup.mem_map.mp hmem
        have hke' : k = ⟨y, hy⟩ := eiso.injective hke
        have hkJ : (k : StatedSp r K) ∈ J := hk
        rwa [hke'] at hkJ
      have ht_pow : ∀ k : Fin r, t k ^ p = 1 := by
        intro k
        show (TableBSymp.zmodPowHom hζ (f₀ k)) ^ p = 1
        rw [← map_pow]
        have h1 : f₀ k ^ p = 1 := by
          rw [← ofAdd_toAdd (f₀ k), ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
            ofAdd_zero]
        rw [h1, map_one]
      have hbpow : (b : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) ^ p = 1 := by
        have hbm : (b : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
            Matrix.diagonal (diagSpEntry t) := by
          simpa [b, mat_apply] using mat_diagSp t
        rw [hbm, Matrix.diagonal_pow]
        ext i j
        by_cases hij : i = j
        · subst hij
          simp only [Matrix.diagonal_apply, if_pos rfl, Matrix.one_apply]
          rcases i with k | k
          · simp only [Pi.pow_apply, if_true]
            rw [diagSpEntry_inl, ← Units.val_pow_eq_pow_val, ht_pow k, Units.val_one]
          · simp only [Pi.pow_apply, if_true]
            rw [diagSpEntry_inr, ← Units.val_pow_eq_pow_val, inv_pow, ht_pow k, inv_one,
              Units.val_one]
        · simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
      have hpqK' : p ∣ Nat.card Kˣ := by
        rw [Nat.card_units]; exact hpqK
      have hpow : ∀ s ∈ ({b} : Set (GL (Fin r ⊕ Fin r) K)), ∃ c : K,
          (s : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) ^ p =
            Matrix.scalar (Fin r ⊕ Fin r) (c ^ p) := by
        intro s hs
        rw [Set.mem_singleton_iff] at hs
        subst hs
        exact ⟨1, by simpa using hbpow⟩
      have hodd_b : ∀ s ∈ ({b} : Set (GL (Fin r ⊕ Fin r) K)), Odd (orderOf s) := by
        intro s hs
        rw [Set.mem_singleton_iff] at hs
        subst hs
        exact ggTBJSpB_odd_orderOf_diagSp t
      have hdeg1 : blockDegree A e1 = 1 :=
        CFSG.StandardType.TableCRes.blockDegree_eq_one_of_pow_eq_pow (p := p)
          (ι := Fin r ⊕ Fin r) (F := K) hp hpqK' hS hodd_b hpow he1
      have hd1 : d = 1 := by rw [← hdeg]; exact hdeg1
      have hmm : mm = m := by
        have h2 : 2 * d * mm = 2 * m := by rw [hrank, hfinrank]
        rw [hd1] at h2
        omega
      have hEcard1 : Fintype.card E = Fintype.card K := by
        rw [hEcard, hd1, pow_one]
      let σ : E ≃+* K := FiniteField.ringEquivOfCardEq hEcard1
      let glc : GL (Fin mm) E ≃* GL (Fin mm) K :=
        CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin mm) σ
      have hmapSL : (StatedSL mm E).map glc.toMonoidHom = StatedSL mm K :=
        CFSG.Adapters.RankTwoModelTransports.glCongr_statedSL (K := E) (L := K) σ mm
      let eSLfield : ↥(StatedSL mm E) ≃* ↥(StatedSL mm K) :=
        (Subgroup.equivMapOfInjective (StatedSL mm E) glc.toMonoidHom glc.injective).trans
          (MulEquiv.subgroupCongr hmapSL)
      have hSLiso : Nonempty (↥J ≃* Matrix.SpecialLinearGroup (Fin mm) K) := by
        refine ⟨((Subgroup.subgroupOfEquivOfLe hJε'.1).symm.trans
          (Subgroup.equivMapOfInjective _ eiso.toMonoidHom eiso.injective)).trans
          ((MulEquiv.subgroupCongr hSL).trans (eSLfield.trans
            (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL mm K).symm))⟩
      have hiso : Nonempty (↥J ≃* Matrix.SpecialLinearGroup (Fin m) K) := by
        rw [← hmm]
        exact hSLiso
      have ht_of_lam : ∀ i : Fin r, f₀ i = lam → t i = lamK := by
        intro i h
        change TableBSymp.zmodPowHom hζ (f₀ i) = lamK
        rw [h]; exact hlam_eq
      have ht_of_lam_inv : ∀ i : Fin r, f₀ i = lam⁻¹ → t i = lamK⁻¹ := by
        intro i h
        change TableBSymp.zmodPowHom hζ (f₀ i) = lamK⁻¹
        rw [h, map_inv]; exact congrArg Inv.inv hlam_eq
      have hfix : ∀ g : Fin r → Multiplicative (ZMod p),
          (∀ j ∈ J,
              TableBSymp.spTorusSp hζ g * j = j * TableBSymp.spTorusSp hζ g) ↔
            ((lam = 1 ∧ ∀ i, f₀ i = 1 → g i = 1) ∨
              (lam ≠ 1 ∧ ∃ c : Multiplicative (ZMod p), ∀ i,
                (f₀ i = lam → g i = c) ∧ (f₀ i = lam⁻¹ → g i = c⁻¹))) := by
        intro g
        constructor
        · intro hcomm
          refine Or.inr ⟨hlam_one, ?_⟩
          have hperm_mem : ∀ i k : Fin r, i ≠ k → t i = t k → (t i = lamK ∨ t i = lamK⁻¹) →
              permSp K (Equiv.swap i k) ∈ J := by
            intro i k hik htik hti
            have hti' : (t i : K) = lam0 ∨ (t i : K) = lam0⁻¹ := by
              rcases hti with h | h
              · exact Or.inl ((hlam_iff (t i)).mp h)
              · exact Or.inr ((hlam_inv_iff (t i)).mp h)
            have htk' : (t k : K) = lam0 ∨ (t k : K) = lam0⁻¹ := by rw [← htik]; exact hti'
            have hi : v (Sum.inl i) = 1 := by apply hsupp1; simpa using hti'
            have hk : v (Sum.inl k) = 1 := by apply hsupp1; simpa using htk'
            have hg : permSp K (Equiv.swap i k) ∈ Gε := by
              have h := permSp_swap_mem_glBlockCentralizer_diagSp t v hv hsym htik.symm hi hk
              simpa [Gε, b, hεv] using h
            exact hJinv _ hg (ggTBJSpB_permSp_swap_mul_self i k)
          have hmixed_mem : ∀ i k : Fin r, t i = lamK → t k = lamK⁻¹ →
              TableBSymp.spSwapSp i * TableBSymp.spSwapSp k * permSp K (Equiv.swap i k) ∈ J := by
            intro i k hti htk
            have hikne : i ≠ k := by
              intro h
              exact hlamK_ne_inv (hti.symm.trans ((by rw [h] : t i = t k).trans htk))
            have hti' : (t i : K) = lam0 := (hlam_iff (t i)).mp hti
            have htk' : (t k : K) = lam0⁻¹ := (hlam_inv_iff (t k)).mp htk
            have hi : v (Sum.inl i) = 1 := by apply hsupp1; exact Or.inl hti'
            have hk : v (Sum.inl k) = 1 := by apply hsupp1; exact Or.inr htk'
            have hik : t k = (t i)⁻¹ := by rw [htk, hti]
            have hg : TableBSymp.spSwapSp i * TableBSymp.spSwapSp k *
                permSp K (Equiv.swap i k) ∈ Gε := by
              have h := spSwapSp_mul_permSp_swap_mem_glBlockCentralizer_diagSp t v hv hsym hik hi hk
              simpa [Gε, b, hεv] using h
            exact hJinv _ hg (ggTBJSpB_spSwapSp_mul_permSp_swap_mul_self hikne)
          have hsame : ∀ i k : Fin r, i ≠ k → t i = t k → (t i = lamK ∨ t i = lamK⁻¹) →
              g i = g k := by
            intro i k hik htik hti
            have hm := hperm_mem i k hik htik hti
            have hc := hcomm _ hm
            have hconj : permSp K (Equiv.swap i k) * TableBSymp.spTorusSp hζ g *
                (permSp K (Equiv.swap i k))⁻¹ = TableBSymp.spTorusSp hζ g := by
              rw [hc.symm, mul_assoc, mul_inv_cancel, mul_one]
            have hconj2 := ggTBJSpC_conj_permSp (K := K) hζ (Equiv.swap i k) g
            have hfixeq := TableBSymp.spTorusSp_injective (m := r) hζ hζo
              (hconj2.symm.trans hconj)
            exact (ggTBJSpC_permAut_swap_eq_self_iff (p := p) hik g).mp hfixeq
          have hmixedrel : ∀ i k : Fin r, t i = lamK → t k = lamK⁻¹ → g i = (g k)⁻¹ := by
            intro i k hti htk
            have hikne : i ≠ k := by
              intro h
              exact hlamK_ne_inv (hti.symm.trans ((by rw [h] : t i = t k).trans htk))
            have hne : t i ≠ t k := by rw [hti, htk]; exact hlamK_ne_inv
            have hm : ggTBJSpC_reflElt t i k ∈ J := by
              rw [ggTBJSpC_reflElt_eq_mixed (K := K) hne]
              exact hmixed_mem i k hti htk
            have hc := hcomm _ hm
            have hconj : ggTBJSpC_reflElt t i k * TableBSymp.spTorusSp hζ g *
                (ggTBJSpC_reflElt t i k)⁻¹ = TableBSymp.spTorusSp hζ g := by
              rw [hc.symm, mul_assoc, mul_inv_cancel, mul_one]
            have hconj2 := ggTBJSpC_reflElt_conj_mixed (K := K) hζ hne g
            have hfixeq := TableBSymp.spTorusSp_injective (m := r) hζ hζo
              (hconj2.symm.trans hconj)
            rw [ggTBJSpC_reflAut_apply_mixed hne] at hfixeq
            exact (ggTBJSpC_invSwapAut_eq_self_iff hikne g).mp hfixeq
          obtain ⟨a, ha⟩ := hvne
          have hex : ∃ i0, f₀ i0 = lam ∨ f₀ i0 = lam⁻¹ := by
            rcases (hsupp_iff a).mp ha with ⟨i, -, hi⟩ | ⟨i, -, hi⟩
            · exact ⟨i, hi⟩
            · exact ⟨i, hi⟩
          obtain ⟨i0, hi0⟩ := hex
          rcases hi0 with hi0lam | hi0inv
          · refine ⟨g i0, ?_⟩
            intro i
            constructor
            · intro hi
              by_cases hii : i = i0
              · subst hii; rfl
              · exact hsame i i0 hii (by rw [ht_of_lam i hi, ht_of_lam i0 hi0lam])
                  (Or.inl (ht_of_lam i hi))
            · intro hi
              have h := hmixedrel i0 i (ht_of_lam i0 hi0lam) (ht_of_lam_inv i hi)
              rw [h, inv_inv]
          · refine ⟨(g i0)⁻¹, ?_⟩
            intro i
            constructor
            · intro hi
              exact hmixedrel i i0 (ht_of_lam i hi) (ht_of_lam_inv i0 hi0inv)
            · intro hi
              have hti : t i = lamK⁻¹ := ht_of_lam_inv i hi
              have hti0 : t i0 = lamK⁻¹ := ht_of_lam_inv i0 hi0inv
              by_cases hii : i = i0
              · subst hii; rw [inv_inv]
              · have heq := hsame i i0 hii (by rw [hti, hti0]) (Or.inr hti)
                rw [heq, inv_inv]
        · rintro (⟨h1, -⟩ | ⟨-, ⟨c, hc⟩⟩)
          · exact absurd h1 hlam_one
          · intro j hj
            have hjG : j ∈ Gε := hJε'.1 hj
            have hjmem : ((j : StatedSp r K) : GL (Fin r ⊕ Fin r) K) ∈
                Subgroup.centralizer ({b} : Set (GL (Fin r ⊕ Fin r) K)) ⊓
                  glFixing (1 - Matrix.diagonal v) := by
              have h := hjG
              simp only [Gε, glBlockCentralizer, Subgroup.mem_comap, hεv] at h
              exact h
            have hjfix : ((j : StatedSp r K) : GL (Fin r ⊕ Fin r) K) *
                (1 - Matrix.diagonal v) = 1 - Matrix.diagonal v :=
              (Subgroup.mem_inf.mp hjmem).2
            have hjcomm : ((j : StatedSp r K) : GL (Fin r ⊕ Fin r) K) * b =
                b * ((j : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :=
              Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hjmem).1
            have hbm : (b : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
                Matrix.diagonal (diagSpEntry t) := by
              simpa [b, mat_apply] using mat_diagSp t
            have hjm : (((j : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
                  Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * Matrix.diagonal (diagSpEntry t) =
                Matrix.diagonal (diagSpEntry t) *
                  (((j : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
                    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
              have h := congrArg (fun y : GL (Fin r ⊕ Fin r) K =>
                ((y : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))) hjcomm
              simpa [hbm, Units.val_mul] using h
            let x : Fin r → Kˣ := fun i => TableBSymp.zmodPowHom hζ (g i)
            let cK : K := ((TableBSymp.zmodPowHom hζ c : Kˣ) : K)
            have hdv_lam : ∀ a, v a = 1 → diagSpEntry t a = lam0 →
                diagSpEntry x a = cK := by
              intro a ha h
              rcases a with i | i
              · have hti' : (t i : K) = lam0 := by simpa [diagSpEntry] using h
                have hti : t i = lamK := (hlam_iff (t i)).mpr hti'
                have hi : f₀ i = lam := (hlammem_iff i).mp hti
                have hg' : g i = c := (hc i).1 hi
                simp [diagSpEntry, x, cK, hg']
              · have hti' : ((t i : K))⁻¹ = lam0 := by simpa [diagSpEntry] using h
                have hti : t i = lamK⁻¹ := by
                  apply (hlam_inv_iff (t i)).mpr
                  have h2 := congrArg (fun z : K => z⁻¹) hti'
                  simpa using h2
                have hi : f₀ i = lam⁻¹ := (hlammem_inv_iff i).mp hti
                have hg' : g i = c⁻¹ := (hc i).2 hi
                simp [diagSpEntry, x, cK, hg', map_inv]
            have hdv_lam_inv : ∀ a, v a = 1 → diagSpEntry t a = lam0⁻¹ →
                diagSpEntry x a = cK⁻¹ := by
              intro a ha h
              rcases a with i | i
              · have hti' : (t i : K) = lam0⁻¹ := by simpa [diagSpEntry] using h
                have hti : t i = lamK⁻¹ := (hlam_inv_iff (t i)).mpr hti'
                have hi : f₀ i = lam⁻¹ := (hlammem_inv_iff i).mp hti
                have hg' : g i = c⁻¹ := (hc i).2 hi
                simp [diagSpEntry, x, cK, hg', map_inv]
              · have hti' : ((t i : K))⁻¹ = lam0⁻¹ := by simpa [diagSpEntry] using h
                have hti : t i = lamK := by
                  apply (hlam_iff (t i)).mpr
                  have h2 := congrArg (fun z : K => z⁻¹) hti'
                  simpa using h2
                have hi : f₀ i = lam := (hlammem_iff i).mp hti
                have hg' : g i = c := (hc i).1 hi
                simp [diagSpEntry, x, cK, hg']
            have hlam0_ne_inv : lam0 ≠ lam0⁻¹ := by
              intro h
              apply hlamK_ne_inv
              apply Units.ext
              rw [hlam_val, hlam_inv_val]
              exact h
            have hx : ∀ a b, v a = 1 → v b = 1 → diagSpEntry t a = diagSpEntry t b →
                diagSpEntry x a = diagSpEntry x b := by
              intro a b ha hb hab
              rcases hsupp0 a ha with h | h
              · rw [hdv_lam a ha h]
                exact (hdv_lam b hb (hab.symm.trans h)).symm
              · rw [hdv_lam_inv a ha h]
                exact (hdv_lam_inv b hb (hab.symm.trans h)).symm
            have hkey := ggTBJSpB_diagonal_mul_eq_mul_of_block v (diagSpEntry t) (diagSpEntry x)
              (((j : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
                Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) hv hjfix hjm hconst hx
            refine Subtype.ext ?_
            rw [Subgroup.coe_mul, Subgroup.coe_mul, ggTBJSpC_spTorusSp_eq_diagSp hζ g]
            refine Units.ext ?_
            rw [Units.val_mul, Units.val_mul, ← mat_apply (diagSp K r x), ← mat_apply j, mat_diagSp]
            exact hkey
      exact ⟨lam, Or.inr ⟨hlam_one, hmpos, hiso⟩, hfix⟩

end CFSG.StandardType

end
