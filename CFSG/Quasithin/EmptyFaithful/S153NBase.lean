module

public import CFSG.Quasithin.EmptyFaithful.S153NDef
public import CFSG.Quasithin.Background.InternalSecB51
public import CFSG.Quasithin.Background.FFC4G2

public section

namespace CFSG.Quasithin.S153N

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Basic

variable {W : Type} [CommGroup W]

theorem ffJ_subgroupOf_normal (Γ : Subgroup (MulAut W)) : ((ffJ Γ).subgroupOf Γ).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (B6.ffJ_le Γ)).2 (B6.le_normalizer_ffJ Γ)

theorem isQuotientOfSQTKTauCeti_of_le {Γ K : Subgroup (MulAut W)} (hq : IsQuotientOfSQTKTauCeti ↥Γ)
    (hKΓ : K ≤ Γ) : IsQuotientOfSQTKTauCeti ↥K := by
  obtain ⟨S, _, _, hst, hkg, φ, hφ⟩ := hq
  have hS : SQTKGroup S := ⟨hst, hkg⟩
  set H : Subgroup S := (K.subgroupOf Γ).comap φ with hH
  have hSH : SQTKGroup ↥H := InternalSec.sqtkGroup_subgroup hS H
  refine ⟨↥H, inferInstance, inferInstance, hSH.1, hSH.2, ?_, ?_⟩
  · exact
      { toFun := fun h => ⟨((φ (h : S) : ↥Γ) : MulAut W), (Subgroup.mem_subgroupOf.mp h.2)⟩
        map_one' := by
          apply Subtype.ext
          simp
        map_mul' := fun a b => by
          apply Subtype.ext
          simp }
  · rintro ⟨k, hk⟩
    obtain ⟨s, hs⟩ := hφ ⟨k, hKΓ hk⟩
    refine ⟨⟨s, ?_⟩, ?_⟩
    · show φ s ∈ K.subgroupOf Γ
      rw [hs]
      exact hk
    · apply Subtype.ext
      show ((φ s : ↥Γ) : MulAut W) = k
      rw [hs]

theorem b53Hyp_ffJ_of_quot {Γ : Subgroup (MulAut W)} (hq : IsQuotientOfSQTKTauCeti ↥Γ)
    (ho : pCoreOf 2 Γ = ⊥) : B53Hyp (ffJ Γ) := by
  have hJΓ : ffJ Γ ≤ Γ := B6.ffJ_le Γ
  have hQ : pCoreOf 2 (ffJ Γ) = ⊥ := by
    have := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 (ffJ Γ) Γ hJΓ
      (ffJ_subgroupOf_normal Γ)
    rw [ho] at this
    exact le_bot_iff.1 this
  exact ⟨hQ, (InternalSec.ffJ_ffJ Γ).symm,
    FFC.b53_clause_of_isQuotientOfSQTKTauCeti (isQuotientOfSQTKTauCeti_of_le hq hJΓ)⟩

theorem not_mem_fixV_of_gen {Γ J : Subgroup (MulAut W)} {w : W} (hgen : orbitSpan Γ w = ⊤)
    (hJΓ : J ≤ Γ) (hJn : (J.subgroupOf Γ).Normal) (hJne : J ≠ ⊥) : w ∉ fixV J := by
  intro hw
  apply hJne
  rw [Subgroup.eq_bot_iff_forall]
  intro j hj
  have hle : orbitSpan Γ w ≤ fixV J := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨g, hg, rfl⟩
    intro j' hj'
    have hn : g⁻¹ * j' * g ∈ J := by
      have h1 := hJn.conj_mem ⟨j', hJΓ hj'⟩ (Subgroup.mem_subgroupOf.mpr hj') ⟨g⁻¹, Γ.inv_mem hg⟩
      have h2 := Subgroup.mem_subgroupOf.mp h1
      simpa [mul_assoc] using h2
    have := hw _ hn
    have h2 : (g⁻¹ * j' * g) w = w := this
    calc j' (g w) = (g * (g⁻¹ * j' * g)) w := by
          simp [mul_assoc]
      _ = g ((g⁻¹ * j' * g) w) := rfl
      _ = g w := by rw [h2]
  rw [hgen] at hle
  ext x
  have := hle (Subgroup.mem_top x) j hj
  simpa using this

theorem exists_sylow_le_stab {Γ : Subgroup (MulAut W)} {w : W} {𝒪 : Set (Subgroup (MulAut W))}
    (hD : Insp67Data Γ w 𝒪) : ∃ S : Subgroup (MulAut W), IsSylowTwoOf S Γ ∧ S ≤ stabAt Γ w := by
  have hN : ((Γ : Subgroup (MulAut W)).subgroupOf Γ).Normal := by
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.normal_top
  obtain ⟨-, S, hS, hN'⟩ := hD.frattini Γ le_rfl hN (fun B hB => (hD.offender B hB).1)
  exact ⟨S, hS, fun s hs => hN' ⟨Subgroup.le_normalizer hs, hS.1 hs⟩⟩

theorem apply_eq_of_cube (hW : ∀ v : W, v ^ 2 = 1) {J : Subgroup (MulAut W)} {g : MulAut W} (hg3 : g ^ 3 = 1)
    {w : W} (h : g w * w⁻¹ ∈ fixV J) (hgJ : g ∈ J) : g w = w := by
  set z : W := g w * w⁻¹ with hz
  have hgz : g z = z := h g hgJ
  have hgw : g w = z * w := by rw [hz]; group
  have hz2 : z * z = 1 := by
    have := hW z
    rwa [pow_two] at this
  have hg2w : (g * g) w = w := by
    show g (g w) = w
    rw [hgw, map_mul, hgz, hgw, ← mul_assoc, hz2, one_mul]
  have hg3w : (g * (g * g)) w = w := by
    have : g * (g * g) = 1 := by
      have h' : g ^ 3 = g * (g * g) := by simp [pow_succ, mul_assoc]
      rw [← h', hg3]
    rw [this]
    rfl
  have : (g * (g * g)) w = g w := by
    show g ((g * g) w) = g w
    rw [hg2w]
  rw [← this, hg3w]

theorem false_of_lift (hW : ∀ v : W, v ^ 2 = 1) {Γ J : Subgroup (MulAut W)} {w : W} (hJΓ : J ≤ Γ)
    (h3 : ¬ 3 ∣ Nat.card ↥(stabAt Γ w)) {g : MulAut W} (hgJ : g ∈ J) (hg1 : g ≠ 1) (hg3 : g ^ 3 = 1)
    (h : g w * w⁻¹ ∈ fixV J) : False := by
  have hfix : g w = w := apply_eq_of_cube hW hg3 h hgJ
  have hmem : g ∈ stabAt Γ w := ⟨hJΓ hgJ, hfix⟩
  apply h3
  have hord : orderOf (⟨g, hmem⟩ : ↥(stabAt Γ w)) = 3 := by
    have : orderOf g = 3 := orderOf_eq_prime hg3 hg1
    rw [← this]
    simp
  rw [← hord]
  exact orderOf_dvd_natCard _

variable [Finite W]

theorem sort_b56 (h56 : AsB56)
    (hW : ∀ v : W, v ^ 2 = 1) {J : Subgroup (MulAut W)} (hb : B53Hyp J) (hne : J ≠ ⊥)
    (hno : ¬ FFC.ThreeRank2 ↥J) : B56Case2 J ∨ (B56Case1 J ∧ FFC.GoodFactor J) := by
  rcases h56 W hW J hne hb with hc1 | hc2 | hc3 | hc4 | hc5
  · exact Or.inr ⟨hc1, FFC.good_of_case1 FFC.b58Inputs W hW J hb hne hno hc1⟩
  · exact Or.inl hc2
  · exact absurd (FFC.threeRank2_of_case3 hc3) hno
  · exact absurd (FFC.threeRank2_of_case4 hc4) hno
  · exact absurd (FFC.threeRank2_of_case5 hc5) hno

theorem not_isStrongFFModule_of_ffJ (hW : ∀ v : W, v ^ 2 = 1) {Γ : Subgroup (MulAut W)}
    (h : ¬ IsStrongFFModule (ffJ Γ)) : ¬ IsStrongFFModule Γ := by
  intro hs
  obtain ⟨A, hA, hr⟩ := (isStrongFFModule_iff hW).1 hs
  obtain ⟨B, -, hB, hrB⟩ := B1_4_4_lt hW hA hr
  apply h
  rw [isStrongFFModule_iff hW]
  exact ⟨B, ⟨B6.le_ffJ hB, hB.2.1, hB.2.2.1⟩, hrB⟩

theorem offenders_le_ffJ (hW : ∀ v : W, v ^ 2 = 1) {Γ : Subgroup (MulAut W)}
    (hns : ¬ IsStrongFFModule Γ) {B : Subgroup (MulAut W)} (hB : B ≤ Γ) (hB0 : B ≠ ⊥)
    (hel : IsElemAbelian2 B) (hoff : Nat.card W ≤ Nat.card ↥B * Nat.card ↥(fixV B)) :
    B ≤ ffJ Γ := by
  have hA2 : IsA2 Γ B := ⟨hB, hB0, hel⟩
  have hr : rAV B ≤ 1 := (rAV_le_one_iff hW hA2).2 hoff
  have hP := B1_4_6 hW hns
  have hmem : B ∈ {A | IsA2 Γ A ∧ rAV A = 1} :=
    ⟨hA2, le_antisymm hr (not_lt.1 fun hlt => hns ((isStrongFFModule_iff hW).2 ⟨B, hA2, hlt⟩))⟩
  rw [← hP] at hmem
  exact B6.le_ffJ hmem

end Basic

end CFSG.Quasithin.S153N
