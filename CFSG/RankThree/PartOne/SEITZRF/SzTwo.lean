module

public import CFSG.RankThree.PartOne.SEITZRF.Rank1
public import CFSG.RankThree.PartOne.SEITZ10.SzCase2
public import CFSG.RankThree.PartOne.KE.SuzukiDescent
public import CFSG.RankThree.PartOne.SEITZ9.SzModule
public import CFSG.RankThree.PartOne.SEITZ9.SzTorus

public section

namespace CFSG.RankThree.PartOne.SEITZRF

open CFSG.Blueprint CFSG.LieType.Ree CFSG.RankThree.PartOne.SEITZ9 CFSG.RankThree.PartOne.SEITZ10
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut)

open CFSG.RankThree.PartOne.KE (fixField)

open CFSG.RankThree.PartOne.CTP (fixedSubgroup)


namespace SzTwo

section Suzuki

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem exists_central_of_S_mem (hK : Nat.card K = 2 ^ (2 * a + 1)) (σ : K ≃+* K)
    {Y : Subgroup (suzukiGroup a K)} (hRY : fixedSubgroup (szFieldAut a K σ) ≤ Y) {u v : K}
    (huv : ¬ (σ u = u ∧ σ v = v)) (hY : suzukiSElt a K u v ∈ Y) :
    ∃ w : K, σ w ≠ w ∧ suzukiSElt a K 0 w ∈ Y := by
  obtain ⟨h2, -⟩ := suzuki_frob_data a hK
  have hθ0 : (2 : ℕ) ^ (a + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  by_cases hu : σ u = u
  · have hv : σ v ≠ v := fun hv => huv ⟨hu, hv⟩
    refine ⟨v, hv, ?_⟩
    have h1 : suzukiSElt a K u 0 ∈ Y := hRY (suzukiSElt_mem_fixed σ hu (map_zero σ))
    have e : suzukiSElt a K 0 v = suzukiSElt a K u v * (suzukiSElt a K u 0)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq, suzukiSElt_mul hK]
      simp [zero_pow hθ0]
    rw [e]
    exact Y.mul_mem hY (Y.inv_mem h1)
  · refine ⟨u ^ (2 ^ (a + 1) + 1), fun h => hu (mem_of_pow_theta_succ_mem (k := fixField σ) hK h),
      ?_⟩
    have h := Y.mul_mem hY hY
    rw [suzukiSElt_mul hK] at h
    convert h using 2
    · linear_combination (-u) * h2
    · rw [pow_succ]
      linear_combination (-v) * h2

end Suzuki

section Rank

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution
open CFSG.SectionRank.LargeRee (blockMat vLabel blockX)

open CFSG.LieType.Steinberg.Adjoint (endHom endHom_apply)


variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem sylowB_mem_Rf_iff (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K) (b c : K) :
    sylowB a K b c ∈ Rf K a β ↔ β b = b ∧ β c = c := by
  have e : sylowB a K b c = sylowVec a K ![0, b, c, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
    simp [sylowVec, sylowV, sylowA_zero, sylowD_zero_zero, sylowF_zero_zero, sylowJ_zero,
      sylowK_zero, sylowH, sylowL, sylowX, largeReeSigma_zero, pinnedX_zero]
  rw [e, sylowVec_mem_Rf_iff hK]
  constructor
  · intro h
    exact ⟨by simpa using h 1, by simpa using h 2⟩
  · rintro ⟨hb, hc⟩ i
    fin_cases i <;> simp [hb, hc]

theorem exists_rankOneEquivSuzuki_sylowB (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (b c : K) : ∃ u v : K,
      rankOneEquivSuzuki K a ha hK ⟨sylowB a K b c, sylowB_mem_rankOneGroupTwo hK b c⟩ =
        suzukiSElt a K u v := by
  have hU2 := sylowB_mem_U2 hK b c
  rw [← map_blockX_one (K := K) (a := a)] at hU2
  obtain ⟨x, hx, hxr⟩ := hU2
  obtain ⟨u, v, huv⟩ := CFSG.SectionRank.LargeRee.exists_vMat_eq_suzukiS
    (CFSG.SectionRank.LargeRee.mem_blockX_one.1 hx) x.2
  refine ⟨u, v, suzukiSElt_ext ?_⟩
  rw [coe_rankOneEquivSuzuki ha hK, coe_suzukiSElt, ← huv]
  change blockMat vLabel ((sylowB a K b c : ModGL F4.tag K) : Module.End K (RootModule F4.tag K)) =
    blockMat vLabel (endHom K (x : adjointGroup F4.tag K))
  rw [endHom_apply]
  exact congrArg
    (fun y : ModGL F4.tag K => blockMat vLabel (y : Module.End K (RootModule F4.tag K))) hxr.symm

end Rank

end SzTwo

theorem suzuki_eq_top_of_S_mem_two
    {a : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (hd : (2 * a + 1).Prime) (σ : K ≃+* K)
    (hk : Nat.card (fixField σ) = 2) {Y : Subgroup (suzukiGroup a K)}
    (hRY : fixedSubgroup (szFieldAut a K σ) ≤ Y) {u v : K}
    (huv : ¬ (σ u = u ∧ σ v = v)) (hY : suzukiSElt a K u v ∈ Y) : Y = ⊤ := by
  classical
  have hfinG : Finite (suzukiGroup a K) := finite_suzukiGroup hK
  set k : Subfield K := fixField σ with hkdef
  have hσk : ∀ c ∈ k, σ c = c := fun c hc => hc
  have hUk : ∀ u ∈ k, ∀ v ∈ k, suzukiSElt a K u v ∈ Y := fun u hu v hv =>
    hRY (suzukiSElt_mem_fixed σ (hσk u hu) (hσk v hv))
  have hTk : ∀ l : Kˣ, (l : K) ∈ k → suzukiDElt a K l ∈ Y := fun l hl =>
    hRY (suzukiDElt_mem_fixed σ (hσk _ hl))
  have hW : suzukiWElt a K ∈ Y := hRY (suzukiWElt_mem_fixed σ)
  have hKk : Nat.card K = Nat.card k ^ (2 * a + 1) := by rw [hK, hk]
  by_cases hcase : ∀ g' : suzukiB a K, (g' : suzukiGroup a K) ∈ Y →
      ((torusPart hK g' : Kˣ) : K) ∈ k
  · exfalso
    obtain ⟨w, hwk, hwY⟩ := SzTwo.exists_central_of_S_mem hK σ hRY huv hY
    have hw0 : w ≠ 0 := fun h => hwk (by rw [h]; exact map_zero σ)
    have hw1 : w ≠ 1 := fun h => hwk (by rw [h]; exact map_one σ)
    have hz : suzukiSElt a K 0 1 ∈ Y := hUk 0 k.zero_mem 1 k.one_mem
    have hu1 : suzukiSElt a K 1 0 ∈ Y := hUk 1 k.one_mem 0 k.zero_mem
    obtain ⟨N, hNn, hNo, hNB⟩ := exists_bender_normal hK hw0 hw1 hW hz hwY
    obtain ⟨Sy, hSy⟩ := exists_sylow_inf_U hK hW hz
    obtain ⟨Q, hQ⟩ := exists_sylow_N Sy hSy N hNo
    obtain ⟨a', ha', ⟨e⟩, hB, -⟩ := bender_type hK hNo hQ hNB hu1
    exact hwk (hσk w (mem_of_Z0_mem_case2 hK hNo hQ hW hz (hB Q).1 (hB Q).2.2.1 hcase hwY))
  · obtain ⟨g', hg'Y, hg'k⟩ : ∃ g' : suzukiB a K, (g' : suzukiGroup a K) ∈ Y ∧
        ((torusPart hK g' : Kˣ) : K) ∉ k := by
      by_contra hcon
      exact hcase fun g' hg' => by_contra fun hk' => hcon ⟨g', hg', hk'⟩
    obtain ⟨u, v, hgg⟩ := torusPart_spec hK g'
    exact suzuki_eq_top_of_irrational_torus hK hd hKk Y hUk hTk hW hg'k (hgg ▸ hg'Y)

section Transport

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution

variable {K : Type} [Field K] [Finite K]
  [CharP K F4.prime] {a : ℕ}

theorem eq_rankOneGroupTwo_of_sylowB_mem_two (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (β : K ≃+* K) (hk : Nat.card (CFSG.LieType.Chevalley.fixSubfield β) = 2)
    (hd : (2 * a + 1).Prime) {Y : Subgroup (ModGL F4.tag K)} (hY : Y ≤ rankOneGroupTwo K a)
    (hRY : rankOneGroupTwo K a ⊓ Rf K a β ≤ Y) {b c : K} (hbc : ¬ (β b = b ∧ β c = c))
    (hbY : sylowB a K b c ∈ Y) : Y = rankOneGroupTwo K a := by
  classical
  have hΓ : ∀ r : rankOneGroupTwo K a, (r : ModGL F4.tag K) ∈ F4.reeGamma K a := fun r =>
    rankOneGroupTwo_le_reeGamma hK r.2
  obtain ⟨u, v, hEuv⟩ := SzTwo.exists_rankOneEquivSuzuki_sylowB ha hK b c
  set E := rankOneEquivSuzuki K a ha hK
  have hMmem : ∀ r : rankOneGroupTwo K a,
      E r ∈ Y.comap ((rankOneGroupTwo K a).subtype.comp E.symm.toMonoidHom) ↔
        (r : ModGL F4.tag K) ∈ Y := fun r => by
    simp
  have hRM : fixedSubgroup (szFieldAut a K β) ≤
      Y.comap ((rankOneGroupTwo K a).subtype.comp E.symm.toMonoidHom) := fun s hs => by
    obtain ⟨r, rfl⟩ := E.surjective s
    rw [hMmem]
    exact hRY ⟨r.2, hΓ r, (rankOneEquivSuzuki_mem_fixedSubgroup_iff ha hK β r).1 hs⟩
  have huv : ¬ (β u = u ∧ β v = v) := by
    rintro ⟨hu, hv⟩
    have h1 : E ⟨sylowB a K b c, sylowB_mem_rankOneGroupTwo hK b c⟩ ∈
        fixedSubgroup (szFieldAut a K β) := by
      rw [hEuv]
      exact suzukiSElt_mem_fixed β hu hv
    have h2 := (rankOneEquivSuzuki_mem_fixedSubgroup_iff ha hK β
      ⟨sylowB a K b c, sylowB_mem_rankOneGroupTwo hK b c⟩).1 h1
    exact hbc ((SzTwo.sylowB_mem_Rf_iff hK β b c).1
      ⟨hΓ ⟨sylowB a K b c, sylowB_mem_rankOneGroupTwo hK b c⟩, h2⟩)
  have hM := suzuki_eq_top_of_S_mem_two hK hd β hk hRM huv (by
    rw [← hEuv, hMmem]
    exact hbY)
  refine le_antisymm hY (fun y hy => ?_)
  have : E ⟨y, hy⟩ ∈ Y.comap ((rankOneGroupTwo K a).subtype.comp E.symm.toMonoidHom) := by
    rw [hM]
    exact Subgroup.mem_top _
  exact (hMmem ⟨y, hy⟩).1 this

end Transport

end CFSG.RankThree.PartOne.SEITZRF
