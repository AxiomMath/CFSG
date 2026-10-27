module

public import CFSG.Quasithin.Vol2.Ch3Sec1L319Common
public import CFSG.Quasithin.Vol2.Ch3Sec1L319Form

public section

namespace CFSG.Quasithin.H13.L319

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Ch3z

@[expose] def NoNatBlockAt (P : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G → quasithinIsSylowTwo T →
    ∀ M M₀ H V : Subgroup G, InM T M → ∀ h : Hyp315Base T M M₀ H V, Hyp315.CaseII M H V →
      qInt M₀ V h.reduced.2.2.1 = 2 → IsUniqueM M₀ M → V ≤ pCoreOf 2 H → ¬ IsDualFFOn M₀ V →
      Concl319 T M V H False → Six6i T M V → Six6iiiImg T M V →
      ∀ A : Subgroup G, IsMinOffender T H V A →
      ∀ L N : Subgroup G, ∀ hstep : IsChiefStep H (conjClosure V H) L N, ¬ IsCentralStep H L N →
      ∀ z : G, z ∈ V → z ∈ N → z ∉ L → (∀ t ∈ T, t * z * t⁻¹ * z⁻¹ ∈ L) →
      ∀ hset : Ch3z.Setting H T (H ⊓ M) (conjClosure V H) A,
      ∀ 𝓗 : Finset (Subgroup (MulAut ↥(chiefMod L N))),
      @Ch3z.BlkCtx ↥(chiefMod L N) (chiefCG (hset.hE hstep)) (chiefAut H L N)
          (chiefImg (Setting.hHL hstep) (Setting.hHN hstep) T)
          (chiefImg (Setting.hHL hstep) (Setting.hHN hstep) (H ⊓ M)) 𝓗 →
      ∀ H' ∈ 𝓗, ∀ e : ℕ, P e →
        @Ch3z.NatBlockData ↥(chiefMod L N) (chiefCG (hset.hE hstep)) H'
          (@CFSG.Quasithin.commV ↥(chiefMod L N) (chiefCG (hset.hE hstep)) H') e → False

@[expose] def Lemma319SixGoodBig : Prop := NoNatBlockAt (fun e => 3 ≤ e)

@[expose] def Lemma319SixGoodTwo : Prop := NoNatBlockAt (fun e => e = 2)

section Good

variable {G : Type} [Group G] [Finite G] {H T M₂ U A L N : Subgroup G}

theorem chiefGood_of_symBlk (hB1 : B69One) (h : Ch3z.Setting H T M₂ U A)
    (hstep : IsChiefStep H U L N) (hnc : ¬ IsCentralStep H L N)
    {𝓗 : Finset (Subgroup (MulAut ↥(chiefMod L N)))}
    (hctx : @BlkCtx ↥(chiefMod L N) (chiefCG (h.hE hstep)) (chiefAut H L N)
        (chiefImg (Setting.hHL hstep) (Setting.hHN hstep) T)
        (chiefImg (Setting.hHL hstep) (Setting.hHN hstep) M₂) 𝓗)
    (hsym : ∀ H' ∈ 𝓗, ∃ m, @SymBlk ↥(chiefMod L N) (chiefCG (h.hE hstep))
        (chiefImg (Setting.hHL hstep) (Setting.hHN hstep) M₂) H' m) :
    ∃ χ₀ : ↥H →* ℤˣ, (∀ g : ↥H, (g : G) ∈ centralizerMod L H N → χ₀ g = 1) ∧
      ∃ a ∈ A, ∃ ha : a ∈ H, χ₀ ⟨a, ha⟩ = -1 := by
  have hHL := Setting.hHL hstep
  have hHN := Setting.hHN hstep
  have hE := h.hE hstep
  have hNL := h.hNL hstep
  let _ : CommGroup ↥(chiefMod L N) := chiefCG hE
  have hstrong := h.noStrong hB1 hstep hnc
  obtain ⟨hAe, hA1, hoff⟩ := h.offender hstep hnc
  have hAX : chiefImg hHL hHN A ≤ chiefAut H L N := chiefImg_le_chiefAut hHL hHN A
  have hshape := hctx.shape_wit (h.rank hstep) hsym hstrong hAX hAe hA1 hoff
  have hhom : ∃ χ : ↥(chiefAut H L N) →* ℤˣ, ∃ a ∈ chiefImg hHL hHN A,
      ∃ ha : a ∈ chiefAut H L N, χ ⟨a, ha⟩ = -1 := by
    rcases hshape with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact hm.exists_hom
    · exact hm.exists_hom
  obtain ⟨χ, a', ha'A, ha'X, hχ⟩ := hhom
  obtain ⟨x, hxA, hxa⟩ := ha'A
  refine ⟨χ.comp (chiefHom hHL hHN), fun g hg => ?_, x.1, Subgroup.mem_subgroupOf.mp hxA, x.2, ?_⟩
  · show χ (chiefHom hHL hHN g) = 1
    rw [(chiefHom_eq_one_iff hHL hHN hNL g).2 hg, map_one]
  · show χ (chiefHom hHL hHN x) = -1
    have : chiefHom hHL hHN x = ⟨a', ha'X⟩ := Subtype.ext hxa
    rw [this]
    exact hχ

theorem lemma319SixGood_of (hB69 : B69Struct) (hB1 : B69One)
    (hBig : Lemma319SixGoodBig) (hTwo : Lemma319SixGoodTwo) : Lemma319SixGood := by
  intro G _ _ T hs hnab hK hT M M₀ H V hM hbase hII hq hMu hVH hdual hconcl h6i h6iii A hA
  obtain ⟨-, -, -, hsetAll, ⟨L, N, hstep, hnc, z, hzV, hzN, hzL, hzT⟩, -⟩ :=
    lemma319Common_of_inputs hB69 G T hs hnab hK hT M M₀ H V hM hbase hII hq hMu hVH hdual hconcl
  have hset := hsetAll A hA
  obtain ⟨𝓗, hctx⟩ := hset.blkCtx hB69 hstep hnc
  let _ : CommGroup ↥(chiefMod L N) := chiefCG (hset.hE hstep)
  have hsym : ∀ H' ∈ 𝓗, ∃ m, @SymBlk ↥(chiefMod L N) (chiefCG (hset.hE hstep))
      (chiefImg (Setting.hHL hstep) (Setting.hHN hstep) (H ⊓ M)) H' m := by
    intro H' hH'
    rcases hctx.symBlk_or_bad hH' with hs' | ⟨e, he, hN', -⟩
    · exact hs'
    · by_cases he2 : e = 2
      · exact (hTwo G T hs hnab hK hT M M₀ H V hM hbase hII hq hMu hVH hdual hconcl h6i h6iii A hA
          L N hstep hnc z hzV hzN hzL hzT hset 𝓗 hctx H' hH' e he2 hN').elim
      · exact (hBig G T hs hnab hK hT M M₀ H V hM hbase hII hq hMu hVH hdual hconcl h6i h6iii A hA
          L N hstep hnc z hzV hzN hzL hzT hset 𝓗 hctx H' hH' e (show 3 ≤ e by omega) hN').elim
  obtain ⟨χ₀, hχC, a, haA, haH, hχa⟩ := chiefGood_of_symBlk hB1 hset hstep hnc hctx hsym
  exact ⟨L, N, hstep, hnc, χ₀, hχC, a, haA, haH, hχa⟩

end Good

end CFSG.Quasithin.H13.L319
