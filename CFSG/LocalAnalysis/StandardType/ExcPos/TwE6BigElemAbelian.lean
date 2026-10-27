module

public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6UnitaryThree
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6CubeDecomp
public import CFSG.LieType.Chevalley.E6GraphLeviIntersections
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.Open.StatedCenterThree
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.U62ThreeCentDet

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LieType.Chevalley.E6GraphHighestRoot
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.SeitzReduction
  CFSG.SeitzReduction.TwistedE6Pilot CFSG.Open

theorem not_nine_dvd_card_units {f : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) (h3 : 3 ∣ 2 ^ f + 1) (h9 : ¬ 9 ∣ 2 ^ f + 1) :
    ¬ 9 ∣ Nat.card Kˣ := by
  intro hdiv
  rw [Nat.card_units, hK] at hdiv
  have hfac : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
    simpa using Nat.pow_two_sub_pow_two (2 ^ f) 1
  rw [hfac] at hdiv
  have hnot3 : ¬ 3 ∣ 2 ^ f - 1 := by
    intro hd
    have h2 : 3 ∣ (2 ^ f + 1) - (2 ^ f - 1) := Nat.dvd_sub h3 hd
    have hsub : (2 ^ f + 1) - (2 ^ f - 1) = 2 := by
      have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      omega
    rw [hsub] at h2
    norm_num at h2
  have hcop9 : Nat.Coprime 9 (2 ^ f - 1) := by
    have hc3 : Nat.Coprime 3 (2 ^ f - 1) :=
      (Nat.prime_three.coprime_iff_not_dvd).mpr hnot3
    have h := (Nat.coprime_pow_left_iff (n := 2) (by norm_num) 3 (2 ^ f - 1)).mpr hc3
    simpa [show (9 : ℕ) = 3 ^ 2 by norm_num] using h
  exact h9 (hcop9.dvd_of_dvd_mul_right hdiv)


section Model


theorem unitarySL_pow_three_eq_one {f : ℕ} {K : Type} [Field K] [Finite K] (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (h3 : 3 ∣ 2 ^ f + 1) (h9 : ¬ 9 ∣ 2 ^ f + 1) (B : unitarySL σ)
    (hB : realize (two_eq_zero_of_card_sq hf hK)
      (B : Matrix.SpecialLinearGroup (Fin 6) K) ^ 3 = 1) :
    B ^ 3 = 1 := by
  haveI : CharP K 2 := CFSG.SeitzReduction.TwistedE6Pilot.charP_two_of_card hf hK
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : K) = 0 := two_eq_zero_of_card_sq hf hK
  have hker : B ^ 3 ∈ ((realize h2).comp (unitarySL σ).subtype).ker := by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, Subgroup.coe_pow, map_pow]
    exact hB
  rw [ker_realize_comp_subtype hK hσ h2] at hker
  obtain ⟨l, hl⟩ := (mem_center_unitarySL_iff hK hσ (B ^ 3)).mp hker
  have hM : ((B : Matrix.SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) ^ 3 =
      l • (1 : Matrix (Fin 6) (Fin 6) K) := by
    have h := hl
    rw [Subgroup.coe_pow, Matrix.SpecialLinearGroup.coe_pow] at h
    rw [h, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hdet : ((B : Matrix.SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 :=
    (B : Matrix.SpecialLinearGroup (Fin 6) K).2
  have hl1 : l = 1 :=
    CFSG.AGLEmbedding.U62ThreeCent.eq_one_of_det_eq_one_of_pow_three_eq_smul_of_char_two_of_not_nine_dvd
      (not_nine_dvd_card_units hK h3 h9) hdet hM
  refine Subtype.ext (Subtype.ext ?_)
  rw [hl, hl1]
  simp

theorem card_ker_realize_unitarySL_le {f : ℕ} {K : Type} [Field K] [Finite K] (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (h3 : 3 ∣ 2 ^ f + 1) :
    Nat.card ((realize (two_eq_zero_of_card_sq hf hK)).comp (unitarySL σ).subtype).ker ≤ 3 := by
  haveI : CharP K 2 := CFSG.SeitzReduction.TwistedE6Pilot.charP_two_of_card hf hK
  have h2 : (2 : K) = 0 := two_eq_zero_of_card_sq hf hK
  have h3K : 3 ∣ Nat.card K - 1 := by
    rw [hK]
    have hq1 : 2 ^ f + 1 ≡ 0 [MOD 3] := Nat.modEq_zero_iff_dvd.mpr h3
    have hq2 : 2 ^ f ≡ 2 [MOD 3] := by
      have h3' : 2 + 1 ≡ 0 [MOD 3] := by norm_num [Nat.ModEq]
      exact Nat.ModEq.add_right_cancel' 1 (hq1.trans h3'.symm)
    have hq2sq : (2 ^ f) ^ 2 ≡ 1 [MOD 3] := by
      have h := Nat.ModEq.pow 2 hq2
      have h4 : (2 ^ 2 : ℕ) ≡ 1 [MOD 3] := by norm_num [Nat.ModEq]
      exact h.trans h4
    exact hq2sq.symm.dvd'
  have hmu : Nat.card (rootsOfUnity 3 K) = 3 :=
    CFSG.Open.StatedCenterThree.card_rootsOfUnity_three h3K
  have hex : ∀ B : ((realize h2).comp (unitarySL σ).subtype).ker, ∃ l : K, l ^ 3 = 1 ∧
      ((B.1 : unitarySL σ) : Matrix.SpecialLinearGroup (Fin 6) K).1 = Matrix.scalar (Fin 6) l := by
    intro B
    have hB : ((B.1 : unitarySL σ) : Matrix.SpecialLinearGroup (Fin 6) K) ∈ (realize h2).ker := by
      have := B.2
      rwa [MonoidHom.mem_ker, MonoidHom.comp_apply] at this
    exact (mem_ker_realize h2 _).mp hB
  choose l hl3 hlB using hex
  have hl0 : ∀ B, l B ≠ 0 := fun B h0 => by
    have := hl3 B
    rw [h0] at this
    norm_num at this
  let g : ((realize h2).comp (unitarySL σ).subtype).ker → rootsOfUnity 3 K := fun B =>
    ⟨Units.mk0 (l B) (hl0 B), by
      rw [mem_rootsOfUnity]
      exact Units.ext (by simpa using hl3 B)⟩
  have hg : Function.Injective g := by
    intro B B' h
    have hll : l B = l B' := by
      have := congrArg (fun u : rootsOfUnity 3 K => ((u : Kˣ) : K)) h
      simpa [g] using this
    refine Subtype.ext (Subtype.ext (Subtype.ext ?_))
    rw [hlB B, hlB B', hll]
  calc Nat.card ((realize h2).comp (unitarySL σ).subtype).ker
      ≤ Nat.card (rootsOfUnity 3 K) := Nat.card_le_card_of_injective g hg
    _ = 3 := hmu

theorem exists_big_elemAbelian_of_model {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]
    [Finite K] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) (h3 : 3 ∣ 2 ^ f + 1) (h9 : ¬ 9 ∣ 2 ^ f + 1)
    {A : SL2 k} (hA : orderOf A = Nat.card k + 1) {m : ℕ} (hm : orderOf (A ^ m) = 3)
    {G : Type*} [Group G] (ι : G →* ModGL TwistTag.E6.tag K) (hι : Function.Injective ι)
    (hroot : ∀ g, ι g ∈ graphFixedRootGroup TwistTag.E6 K σ) {x₀ d : G}
    (hx₀ : ι x₀ = (thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K)) (A ^ m))
    (hd3 : d ^ 3 = 1) (hdx : d * x₀ = x₀ * d) (hL : su6Levi σ ≤ ι.range) :
    ∃ E : Subgroup G, IsElemAbelian 3 E ∧ x₀ ∈ E ∧ d ∈ E ∧ 3 ^ 5 ≤ Nat.card E := by
  classical
  haveI : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  haveI : CharP K 2 := CFSG.SeitzReduction.TwistedE6Pilot.charP_two_of_card hf hK
  haveI : CharP k 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero
    (two_eq_zero_of_card hf hk)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hK2 : (2 : K) = 0 := two_eq_zero_of_card_sq hf hK
  set ρ := (thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K)) with hρ
  have hρinj : Function.Injective ρ := injective_thetaSL2_comp_map hK2 (algebraMap k K)
  set x' := ρ (A ^ m) with hx'
  have hAm3 : (A ^ m) ^ 3 = 1 := by
    rw [← hm]
    exact pow_orderOf_eq_one _
  have hAm1 : A ^ m ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hm
    omega
  have hx'3 : x' ^ 3 = 1 := by rw [hx', ← map_pow, hAm3, map_one]
  have hx'ne : x' ≠ 1 := fun h1 => hAm1 (hρinj (by rw [map_one]; exact h1))
  have hgx : ι d * x' = x' * ι d := by
    rw [← hx₀, ← map_mul, ← map_mul, hdx]
  have hg3 : (ι d) ^ 3 = 1 := by rw [← map_pow, hd3, map_one]
  obtain ⟨j, hj, δ, hδ, hjδ, hδ3⟩ :=
    exists_cube_decomp_of_commute_rho hf hk hK hσ h3 h9 hA hm (hroot d) hgx hg3
  have hsu : su6Levi σ = (unitarySL σ).map (realize hK2) :=
    (subsystemGroup_inf_eq_map_realize hK hσ hK2).1
  have hδ' : δ ∈ (unitarySL σ).map (realize hK2) := by rw [← hsu]; exact hδ
  obtain ⟨B, hB, hBδ⟩ := Subgroup.mem_map.mp hδ'
  let B' : unitarySL σ := ⟨B, hB⟩
  have hB'3 : B' ^ 3 = 1 :=
    unitarySL_pow_three_eq_one hf hK hσ h3 h9 B' (by
      show realize hK2 B ^ 3 = 1
      rw [hBδ]
      exact hδ3)
  obtain ⟨EB, hEBel, hBEB, hEBcard⟩ :=
    exists_elemAbelian_three_pow_five_of_cube_eq_one hf hK hσ h3 B' hB'3
  let φ : unitarySL σ →* ModGL TwistTag.E6.tag K := (realize hK2).comp (unitarySL σ).subtype
  have hφB : φ B' = δ := hBδ
  set R : Subgroup (ModGL TwistTag.E6.tag K) := EB.map φ with hR
  have hRel : IsElemAbelian 3 R := hEBel.map φ
  have hRsu : R ≤ su6Levi σ := by
    rintro _ ⟨b, -, rfl⟩
    rw [hsu]
    exact ⟨(b : Matrix.SpecialLinearGroup (Fin 6) K), b.2, rfl⟩
  have hδR : δ ∈ R := ⟨B', hBEB, hφB⟩
  have hRcard : 3 ^ 4 ≤ Nat.card R := by
    let ψ : EB →* ModGL TwistTag.E6.tag K := φ.comp EB.subtype
    have h1 := Subgroup.card_ker_mul_card_range ψ
    have hψrange : ψ.range = R := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hψker : Nat.card ψ.ker ≤ 3 := by
      have hinj : Function.Injective (fun b : ψ.ker => (⟨b.1.1, b.2⟩ : φ.ker)) := by
        intro b b' h
        have h' : b.1.1 = b'.1.1 := congrArg (fun z : φ.ker => (z : unitarySL σ)) h
        exact Subtype.ext (Subtype.ext h')
      exact (Nat.card_le_card_of_injective _ hinj).trans
        (card_ker_realize_unitarySL_le hf hK h3)
    rw [hψrange] at h1
    have h2' : 3 ^ 5 ≤ Nat.card ψ.ker * Nat.card R := h1 ▸ hEBcard
    have h3' : Nat.card ψ.ker * Nat.card R ≤ 3 * Nat.card R := Nat.mul_le_mul_right _ hψker
    have h5 : 3 * 3 ^ 4 ≤ 3 * Nat.card R :=
      calc 3 * 3 ^ 4 = 3 ^ 5 := by norm_num
        _ ≤ 3 * Nat.card R := h2'.trans h3'
    exact Nat.le_of_mul_le_mul_left h5 (by norm_num)
  have hxb : ∀ b ∈ su6Levi σ, x' * b = b * x' := by
    intro b hb
    obtain ⟨hcent, -⟩ := su6Levi_facts (k := k) hf hk hK hσ
    have hx'J : x' ∈ thetaRankOneGroup (algebraMap k K) := by
      rw [thetaRankOneGroup_eq_range hK2 (algebraMap k K)]
      exact ⟨A ^ m, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp (hcent hb) x' hx'J
  have hx'notin : x' ∉ su6Levi σ := by
    intro hx
    have hcentral : A ^ m ∈ Subgroup.center (SL2 k) := by
      rw [Subgroup.mem_center_iff]
      intro C
      apply hρinj
      rw [map_mul, map_mul]
      obtain ⟨hcent, -⟩ := su6Levi_facts (k := k) hf hk hK hσ
      have hCJ : ρ C ∈ thetaRankOneGroup (algebraMap k K) := by
        rw [thetaRankOneGroup_eq_range hK2 (algebraMap k K)]
        exact ⟨C, rfl⟩
      exact Subgroup.mem_centralizer_iff.mp (hcent hx) (ρ C) hCJ
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcentral
    exact CFSG.StandardType.TwE6CorootCore.coe_not_mem_range_scalar hAm1
      ⟨r, by rw [← hr]⟩
  set Esu : Subgroup (ModGL TwistTag.E6.tag K) := Subgroup.zpowers x' ⊔ R with hEsu
  have hEsu_el : IsElemAbelian 3 Esu := by
    refine (isElemAbelian_zpowers hx'3).sup_of_commute hRel ?_
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (Commute.zpow_left (hxb b (hRsu hb)) i).eq
  have hx'Esu : x' ∈ Esu := Subgroup.mem_sup_left (Subgroup.mem_zpowers x')
  have hRle : R ≤ Esu := le_sup_right
  have hEsucard : 3 ^ 5 ≤ Nat.card Esu := by
    have hRne : R ≠ Esu := fun h => hx'notin (hRsu (h ▸ hx'Esu))
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hRel.isPGroup
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hEsu_el.isPGroup
    have hlt : Nat.card R < Nat.card Esu :=
      lt_of_le_of_ne (Subgroup.card_le_of_le hRle)
        fun h => hRne (Subgroup.eq_of_le_of_card_ge hRle h.ge)
    rw [ha, hb] at hlt
    have hab : a < b := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
    have h4a : 3 ^ 4 ≤ 3 ^ a := ha ▸ hRcard
    have h4 : 4 ≤ a := (Nat.pow_le_pow_iff_right (by norm_num)).mp h4a
    rw [hb]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hEsule : Esu ≤ ι.range :=
    sup_le (Subgroup.zpowers_le.2 ⟨x₀, hx₀⟩) (hRsu.trans hL)
  refine ⟨Esu.comap ι, hEsu_el.comap hι, ?_, ?_, ?_⟩
  · exact (Subgroup.mem_comap).2 (by rw [hx₀]; exact hx'Esu)
  · refine (Subgroup.mem_comap).2 ?_
    rw [hjδ]
    exact mul_mem (Subgroup.mem_sup_left (by rwa [← hx'] at hj))
      (Subgroup.mem_sup_right (hδR))
  · have hmap : (Esu.comap ι).map ι = Esu := by
      rw [Subgroup.map_comap_eq, inf_of_le_right hEsule]
    calc 3 ^ 5 ≤ Nat.card Esu := hEsucard
      _ = Nat.card ((Esu.comap ι).map ι) := by rw [hmap]
      _ = Nat.card (Esu.comap ι) := Subgroup.card_map_of_injective hι

end Model

end CFSG.StandardType.LieKnownR2.ExcPos
