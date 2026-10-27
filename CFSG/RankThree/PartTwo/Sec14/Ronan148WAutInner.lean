module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148WFieldE27Amb
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentConfig
import CFSG.RankThree.PartTwo.Sec11.KS11LieProofAut
import CFSG.RankThree.PartTwo.Sec4.LThreePiFieldB
import CFSG.RankThree.PartTwo.Sec4.LThreePiFrob
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseI
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix

local notation "pmk" => Matrix.ProjGenLinGroup.mk

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem mem_inner_of_pgl_of_elemAbelian (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) {E : Subgroup (MulAut (projImage (slPi π 3 (p ^ f) K)))}
    (hE : CFSG.Open.IsElemAbelian 3 E) (h9 : 9 < Nat.card E)
    {a : MulAut (projImage (slPi π 3 (p ^ f) K))} (haE : a ∈ E) {y : GL (Fin 3) K}
    (hy : y ∈ glPi π 3 (p ^ f) K)
    (hay : ∀ m : projImage (slPi π 3 (p ^ f) K),
      (a m : ProjGenLinGroup (Fin 3) K) = pmk y * m * (pmk y)⁻¹) :
    a ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (projImage (slPi π 3 (p ^ f) K)) := by
  classical
  have := hK.finite
  haveI : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective (ProjGenLinGroup.mk : GL (Fin 3) K →* _) (QuotientGroup.mk'_surjective _)
  haveI : Finite (MulAut (projImage (slPi π 3 (p ^ f) K))) :=
    Finite.of_injective (fun α : MulAut (projImage (slPi π 3 (p ^ f) K)) =>
      (α : projImage (slPi π 3 (p ^ f) K) → projImage (slPi π 3 (p ^ f) K)))
      fun _ _ h => MulEquiv.ext (congrFun h)
  haveI := Sec13.isPerfect_projImage_slPi hK hq2
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have h3K := hK.three_ne_zero hq
  set L := CFSG.ComponentClassification.OuterAutomorphisms.inner
    (projImage (slPi π 3 (p ^ f) K)) with hLdef
  set e₀ := innerEquiv hK hq hq2 with he₀
  have hCbot : Subgroup.centralizer (L : Set (MulAut (projImage (slPi π 3 (p ^ f) K)))) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun β hβ => MulEquiv.ext fun m => ?_
    have h1 := Subgroup.mem_centralizer_iff.mp hβ (MulAut.conj m) ⟨m, rfl⟩
    have h2 : MulAut.conj (β m) = MulAut.conj m := by
      rw [mulAut_conj_apply_eq, ← h1, mul_inv_cancel_right]
    exact conj_injective_projImage hK hq hq2 h2
  have hinnerpgl : ∀ (e : L ≃* projImage (slPi π 3 (p ^ f) K)),
      ∀ b ∈ L ⊔ Subgroup.centralizer (L : Set (MulAut (projImage (slPi π 3 (p ^ f) K)))),
        ∃ y, IsPGLAtP e b y := by
    intro e b hb
    obtain ⟨l, hl, u, hu, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hb
    obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp (e ⟨l, hl⟩).2
    exact ⟨_, isPGLAtP_mul e (isPGLAtP_of_mem e hπ hl hs hse.symm)
      (isPGLAtP_of_mem_centralizer e hu)⟩
  have haP : IsPGLAtP e₀ a y := ⟨hy, fun m => by rw [he₀, slAct_innerEquiv]; exact hay m⟩
  by_contra haL
  obtain ⟨σ, hσE, hσP⟩ : ∃ σ ∈ E, ¬ ∃ y, IsPGLAtP e₀ σ y := by
    by_contra hall
    push Not at hall
    have hcard := card_eq_card_inf_mul_card_rangeP (hK := hK) (hq := hq) (e := e₀) (A' := E)
      (hA' := hall)
    rw [hCbot, inf_bot_eq, Subgroup.card_bot, one_mul] at hcard
    have hle := card_le_nine_of_comm h3K hτ hτ1 (pglHomP hK hq E hall).range
      (range_pglHomP_comm (hA' := hall) fun a ha b hb =>
        congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
      (range_pglHomP_pow (hA' := hall) fun b hb => hE.2 b hb)
    omega
  have hσ3 : σ ^ 3 = 1 := hE.2 σ hσE
  rcases Sec11.KS11LieProof.aut_pgl_or_field hK hq2 (slAct e₀ ⟨σ, mem_normalizer_of_normal σ⟩)
      (slAct_pow_three_of e₀ (mem_normalizer_of_normal σ) hσ3) with
    ⟨y', hy', hys'⟩ | ⟨f₀, hf, ψ, hψa, g, hg, hga⟩
  · exact absurd ⟨y', hy', hys'⟩ hσP
  obtain ⟨φ, hφ, hφ3⟩ := exists_frob hK hf
  have hψ : ψ = φ ∨ ψ = φ ^ 2 := eq_or_eq_sq_of_pow hφ hψa
  obtain ⟨e', he'⟩ := exists_normalized_fieldP hK hq hf hφ hφ3 hψ e₀ hσ3 hg hga
  have hσB : σ ∉ L ⊔ Subgroup.centralizer (L : Set (MulAut (projImage (slPi π 3 (p ^ f) K)))) :=
    fun h => hσP (hinnerpgl e₀ σ h)
  obtain ⟨-, hcardE⟩ :=
    fieldB_structure_of_elemAbelian hK hq hq2 hf hφ hφ3 hψ e' hE hσE hσB he'
  have hσ1 : σ ≠ 1 := fun h =>
    hσP ⟨1, by rw [h]; exact isPGLAtP_of_mem_centralizer e₀ (Subgroup.one_mem _)⟩
  have hσo : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  have hinf := inf_zpowers_eq_bot (H := E ⊓ (L ⊔ Subgroup.centralizer
    (L : Set (MulAut (projImage (slPi π 3 (p ^ f) K)))))) hσ3 (fun h => hσB h.2)
  have hcomm : ∀ x ∈ E ⊓ (L ⊔ Subgroup.centralizer
      (L : Set (MulAut (projImage (slPi π 3 (p ^ f) K))))),
      ∀ z ∈ Subgroup.zpowers σ, x * z = z * x := fun x hx z hz =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx.1⟩ ⟨z, (Subgroup.zpowers_le.mpr hσE) hz⟩)
  obtain ⟨hcard, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hσo, ← hcardE] at hcard
  have hEeq := Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left (Subgroup.zpowers_le.mpr hσE))
    hcard.ge
  have haBS : a ∈ ((E ⊓ (L ⊔ Subgroup.centralizer
      (L : Set (MulAut (projImage (slPi π 3 (p ^ f) K))))) ⊔ Subgroup.zpowers σ :
      Subgroup _) : Set _) := by
    rw [hEeq]
    exact haE
  rw [hset] at haBS
  obtain ⟨b, hb, s, hs, rfl⟩ := Set.mem_mul.mp haBS
  obtain ⟨yb, hyb⟩ := hinnerpgl e₀ b hb.2
  have hb3 : b ^ 3 = 1 := hE.2 b hb.1
  have hsP : IsPGLAtP e₀ s (yb ^ 2 * y) := by
    have e1 : s = b ^ 2 * (b * s) := by
      rw [← mul_assoc, ← pow_succ, hb3, one_mul]
    rw [e1]
    exact isPGLAtP_mul e₀ (isPGLAtP_pow hyb 2) haP
  by_cases hs1 : s = 1
  · apply haL
    have hbL := hb.2
    rw [hCbot, sup_bot_eq] at hbL
    rwa [hs1, mul_one]
  · have hs3 : s ^ 3 = 1 := hE.2 s ((Subgroup.zpowers_le.mpr hσE) hs)
    have hso : orderOf s = 3 := orderOf_eq_prime hs3 hs1
    have hzs : Subgroup.zpowers s = Subgroup.zpowers σ :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hs)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hso, hσo])
    have hσs : σ ∈ Subgroup.zpowers s := hzs ▸ Subgroup.mem_zpowers σ
    obtain ⟨n, hn⟩ := mem_powers_iff_mem_zpowers.mpr hσs
    have hn' : s ^ n = σ := hn
    exact hσP ⟨_, hn' ▸ isPGLAtP_pow hsP n⟩

theorem not_mem_inner_of_type_three (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) {a : MulAut (projImage (slPi π 3 (p ^ f) K))} {y : GL (Fin 3) K}
    (hy : y ∈ glPi π 3 (p ^ f) K) (h3 : Type123 π (p ^ f) K y 3)
    (hay : ∀ m : projImage (slPi π 3 (p ^ f) K),
      (a m : ProjGenLinGroup (Fin 3) K) = pmk y * m * (pmk y)⁻¹) :
    a ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (projImage (slPi π 3 (p ^ f) K)) := by
  haveI := Sec13.isPerfect_projImage_slPi hK hq2
  rintro ⟨m₀, rfl⟩
  obtain ⟨⟨l, hl⟩, rfl⟩ := projOf_surjective _ m₀
  apply not_inner_of_type3 hK hq hy h3
  have hw : l⁻¹ * y ∈ StatedScalars (Fin 3) K := by
    refine mem_statedScalars_of_comm_mod hK hq fun s hs => ?_
    rw [← mk_eq_one_iff_mem_statedScalars]
    have h1 := hay (projOf _ ⟨s, hs⟩)
    rw [MulAut.conj_apply] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_projOf] at h1
    simp only [map_mul, map_inv]
    calc (pmk l)⁻¹ * pmk y * pmk s * ((pmk l)⁻¹ * pmk y)⁻¹ * (pmk s)⁻¹ =
        (pmk l)⁻¹ * (pmk y * pmk s * (pmk y)⁻¹) * pmk l * (pmk s)⁻¹ := by group
      _ = (pmk l)⁻¹ * (pmk l * pmk s * (pmk l)⁻¹) * pmk l * (pmk s)⁻¹ := by rw [← h1]
      _ = 1 := by group
  obtain ⟨c, hc⟩ := hw
  refine ⟨l, hl, fun s _ => ?_⟩
  have hy' : y = l * GeneralLinearGroup.scalar (Fin 3) c := by rw [hc]; group
  have hcs : GeneralLinearGroup.scalar (Fin 3) c * s = s * GeneralLinearGroup.scalar (Fin 3) c :=
    (commute_of_mem_statedScalars ⟨c, rfl⟩ s).symm
  rw [hy']
  calc l * GeneralLinearGroup.scalar (Fin 3) c * s * (l * GeneralLinearGroup.scalar (Fin 3) c)⁻¹ =
      l * (GeneralLinearGroup.scalar (Fin 3) c * s) * (GeneralLinearGroup.scalar (Fin 3) c)⁻¹ *
        l⁻¹ := by group
    _ = l * s * l⁻¹ := by rw [hcs]; group

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
