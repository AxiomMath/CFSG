module

public import CFSG.Quasithin.EmptyFaithful.S146C6

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

section Fixed

variable [Finite G] {K Z U₁ : Subgroup G}

omit [Finite G] in
theorem Sec8.exists_nc_of_not_mem (h : Sec8 K Z U₁) {a : G} (haU : a ∈ U₁) (haZ : a ∉ Z) :
    ∃ k ∈ K, a * k * a⁻¹ * k⁻¹ ∉ Z := by
  by_contra hcon
  push Not at hcon
  have hZF : Z ≤ centralizerMod Z U₁ K := fun z hz => by
    refine mem_centralizerMod.mpr ⟨h.le hz, Subgroup.le_normalizer hz, fun k hk => ?_⟩
    have e : z * k * z⁻¹ * k⁻¹ = z * (k * z⁻¹ * k⁻¹) := by group
    rw [e]
    exact Z.mul_mem hz ((Subgroup.mem_normalizer_iff.mp (h.KZ hk) z⁻¹).mp (Z.inv_mem hz))
  have hKF : K ≤ Subgroup.normalizer ((centralizerMod Z U₁ K : Subgroup G) : Set G) := by
    have key : ∀ k₀ ∈ K, ∀ x ∈ centralizerMod Z U₁ K, k₀ * x * k₀⁻¹ ∈ centralizerMod Z U₁ K := by
      intro k₀ hk₀ x hx
      obtain ⟨hxU, hxN, hxk⟩ := mem_centralizerMod.mp hx
      refine mem_centralizerMod.mpr ⟨?_, ?_, fun k hk => ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (h.KU hk₀) x).mp hxU
        exact this
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (h.KZ hk₀) hxN)
          (Subgroup.inv_mem _ (h.KZ hk₀))
      · have hk' : k₀⁻¹ * k * k₀ ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hk₀) hk) hk₀
        have h1 := hxk _ hk'
        have e : k₀ * x * k₀⁻¹ * k * (k₀ * x * k₀⁻¹)⁻¹ * k⁻¹ =
            k₀ * (x * (k₀⁻¹ * k * k₀) * x⁻¹ * (k₀⁻¹ * k * k₀)⁻¹) * k₀⁻¹ := by group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (h.KZ hk₀) _).mp h1
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => key k hk x hx, fun hx => ?_⟩
    have h1 := key k⁻¹ (K.inv_mem hk) _ hx
    have e : k⁻¹ * (k * x * k⁻¹) * k⁻¹⁻¹ = x := by group
    rwa [e] at h1
  have hFU : centralizerMod Z U₁ K ≤ U₁ := centralizerMod_le_left _ _ _
  rcases h.irr _ hZF hFU hKF with hF | hF
  · exact haZ (by rw [← hF]; exact mem_centralizerMod.mpr ⟨haU, h.norm haU, hcon⟩)
  · obtain ⟨k, hk, u, hu, hnc⟩ := h.exists_nc
    apply hnc
    have hu' : u ∈ centralizerMod Z U₁ K := by rw [hF]; exact hu
    have h1 := (mem_centralizerMod.mp hu').2.2 k hk
    have e : k * u * k⁻¹ * u⁻¹ = (u * k * u⁻¹ * k⁻¹)⁻¹ := by group
    rw [e]
    exact Z.inv_mem h1

end Fixed

section Choice

variable [Finite G] {T M : Subgroup G}

@[expose] def Stage146D4A6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M → HypB146 T M →
    ∀ K ∈ cComp (mcOf T), Conc14621 T K → Conc14622 T M K → Conc14623 T M →
      ∀ (U₁ U₂ : Subgroup G) (s : G), IsDecompUK T M K U₁ U₂ s → KbarIsA6 K →
        ∃ u : G, IsChoiceU T M K U₁ u

theorem stage146D4_of (h6 : Stage146D4A6) : Stage146D4 := by
  intro G _ _ T M S hB K hK c21 c22 c23 U₁ U₂ s hdec
  by_cases hA : KbarIsA6 K
  · exact h6 G T M S hB K hK c21 c22 c23 U₁ U₂ s hdec hA
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hKG : K ≤ mcOf T := le_of_mem_cComp hK
  have hTG : T ≤ mcOf T := hG.1.1
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) (mcOf T)) := S.lemma_14_5_15_two hG
  have hUQ : conjClosure (VZ T M) (mcOf T) ≤ pCoreOf 2 (mcOf T) := S.conjClosure_le_pCoreOf hG
  have hQT : pCoreOf 2 (mcOf T) ≤ T := S.pCoreOf_le_T hG
  have hUN : conjClosure (VZ T M) (mcOf T) ≤
      Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := S.conjClosure_le_normalizer_Z hG
  have hZU : quasithinOmegaOneCenter T ≤ conjClosure (VZ T M) (mcOf T) :=
    Z_le_conjClosure_VZ T M (mcOf T)
  have hG₁U : mcOf T ≤ Subgroup.normalizer (conjClosure (VZ T M) (mcOf T) : Set G) :=
    le_normalizer_conjClosure _ _
  have hG₁Z : mcOf T ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := fun x hx =>
    S.normalizer_Z.ge hx
  have hTZ : T ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := fun x hx =>
    hG₁Z (hTG hx)
  have hKU : K ≤ Subgroup.normalizer (conjClosure (VZ T M) (mcOf T) : Set G) := hKG.trans hG₁U
  have hnat : mIdx U₁ (quasithinOmegaOneCenter T) = 3 ∧
      IsIrredOnSection K U₁ (quasithinOmegaOneCenter T) := by
    rcases hdec.natural with ⟨-, h3, hirr⟩ | ⟨h6', -⟩
    · exact ⟨h3, hirr⟩
    · exact (hA h6').elim
  have hsup : ⁅conjClosure (VZ T M) (mcOf T), K⁆ ⊔ quasithinOmegaOneCenter T = U₁ ⊔ U₂ := hdec.sup
  have hU₁U : U₁ ≤ conjClosure (VZ T M) (mcOf T) := by
    have h1 : ⁅conjClosure (VZ T M) (mcOf T), K⁆ ≤ conjClosure (VZ T M) (mcOf T) :=
      S145.commutator_le_of_le_normalizer hKU
    have h2 : U₁ ⊔ U₂ ≤ conjClosure (VZ T M) (mcOf T) := by
      rw [← hsup]
      exact sup_le h1 hZU
    exact le_sup_left.trans h2
  have hU₁2 : IsPGroup 2 U₁ := (pCoreOf_isPGroup 2 (mcOf T)).to_le (hU₁U.trans hUQ)
  have hSec : Sec8 K (quasithinOmegaOneCenter T) U₁ :=
    { le := hdec.Z₁
      norm := hU₁U.trans hUN
      sq := fun a ha => by
        rw [isElemAbelian_pow_eq_one hUab (hU₁U ha)]
        exact Subgroup.one_mem _
      comm := fun a ha b hb => by
        have e : a * b * a⁻¹ * b⁻¹ = 1 := by
          rw [isElemAbelian_comm hUab (hU₁U ha) (hU₁U hb)]
          group
        rw [e]
        exact Subgroup.one_mem _
      card := by rw [HypF98.relIndex_eq_two_pow_mIdx hU₁2, hnat.1]; norm_num
      KZ := hKG.trans hG₁Z
      KU := hnat.2.2.1
      irr := hnat.2.2.2.2 }
  have hlt : quasithinOmegaOneCenter T < U₁ := hnat.2.1
  by_cases hC2 : IsCase2 T K
  ·
    set P : Subgroup G := T ⊓ Subgroup.normalizer (K : Set G) with hP
    set V : Subgroup G := ⁅conjClosure (VZ T M) (mcOf T), K⁆ with hV
    have hVZ : ¬ V ≤ quasithinOmegaOneCenter T := by
      intro hle
      have h1 : U₁ ⊔ U₂ ≤ quasithinOmegaOneCenter T := by
        rw [← hsup]
        exact sup_le hle le_rfl
      exact hlt.not_ge (le_sup_left.trans h1)
    have hVU : V ≤ conjClosure (VZ T M) (mcOf T) := S145.commutator_le_of_le_normalizer hKU
    have hVT : V ≤ T := hVU.trans (hUQ.trans hQT)
    have hPT : P ≤ T := inf_le_left
    have hPU : P ≤ Subgroup.normalizer (conjClosure (VZ T M) (mcOf T) : Set G) := fun x hx =>
      hG₁U (hTG hx.1)
    have hPV : P ≤ Subgroup.normalizer (V : Set G) :=
      S145.le_normalizer_commutator hPU inf_le_right
    have hPVT : P ⊔ V ≤ T := sup_le hPT hVT
    have hTV : P ⊔ V ≤ Subgroup.normalizer (V : Set G) :=
      sup_le hPV Subgroup.le_normalizer
    have hTV₁ : P ⊔ V ≤ Subgroup.normalizer ((V ⊓ quasithinOmegaOneCenter T : Subgroup G) : Set G) :=
      fun x hx => Subgroup.inf_normalizer_le_normalizer_inf ⟨hTV hx, hTZ (hPVT hx)⟩
    have hlt' : V ⊓ quasithinOmegaOneCenter T < V :=
      lt_of_le_of_ne inf_le_left (fun h => hVZ (h ▸ inf_le_right))
    obtain ⟨z, hzV, hzZ, hz⟩ := exists_fixed_mod (T := P ⊔ V) (V := V)
      (V₁ := V ⊓ quasithinOmegaOneCenter T) (hT2.to_le hPVT) le_sup_right hlt' hTV hTV₁
    have huG : z ∈ mcOf T := S.mem_mcOf_of_mem_conjClosure hG (hVU hzV)
    refine ⟨z, Or.inr ⟨hC2, hzV, fun hz' => hzZ ⟨hzV, hz'⟩, fun t ht => ?_⟩⟩
    exact (S146T.mem_tZero_iff huG).mpr ⟨ht.1, (hz t (Subgroup.mem_sup_left ht)).2⟩
  ·
    have hU₁T : U₁ ≤ T := hU₁U.trans (hUQ.trans hQT)
    obtain ⟨z, hzU, hzZ, hz⟩ := exists_fixed_mod (T := T ⊓ Subgroup.normalizer (U₁ : Set G))
      (V := U₁) (V₁ := quasithinOmegaOneCenter T) (hT2.to_le inf_le_left)
      (le_inf hU₁T Subgroup.le_normalizer) hlt inf_le_right (fun x hx => hTZ hx.1)
    have huG : z ∈ mcOf T := S.mem_mcOf_of_mem_conjClosure hG (hU₁U hzU)
    refine ⟨z, Or.inl ⟨hC2, hzU, ?_, fun t ht => ?_⟩⟩
    · intro hle
      obtain ⟨k, hk, hnc⟩ := hSec.exists_nc_of_not_mem hzU hzZ
      exact hnc (Subgroup.commutator_le.mp hle z (Subgroup.mem_zpowers z) k hk)
    · exact (S146T.mem_tZero_iff huG).mpr ⟨ht.1, hz t ht⟩

@[expose] def Stage146FH2S3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M → HypB146 T M →
    ∀ (K U₁ U₂ : Subgroup G) (s u : G), BData146 T M K U₁ U₂ s u →
      Nonempty (OTwoQuot (centralizerMod (quasithinOmegaOneCenter T) (mcOf T)
          (Subgroup.zpowers u)) ≃* Equiv.Perm (Fin 3))

theorem stage146FH2_of (h : Stage146FH2S3) : Stage146FH2 := by
  intro G _ _ T M S hB K U₁ U₂ s u hd
  obtain ⟨e⟩ := h G T M S hB K U₁ U₂ s u hd
  refine ⟨⟨e⟩, fun hle => ?_⟩
  set H₂ := centralizerMod (quasithinOmegaOneCenter T) (mcOf T) (Subgroup.zpowers u) with hH₂
  have hH₂G : H₂ ≤ mcOf T := centralizerMod_le_left _ _ _
  have hT : H₂ ≤ T := by
    have h1 : T = M ⊓ mcOf T := hd.c23.2.1.2
    rw [h1]
    exact le_inf hle hH₂G
  have hp : IsPGroup 2 H₂ := S.hyp.sylow.1.to_le hT
  have hnormal : (⊤ : Subgroup ↥H₂).Normal := Subgroup.normal_top
  have hptop : (⊤ : Subgroup ↥H₂) ≤ CFSG.Open.pCore 2 ↥H₂ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CFSG.LieType.BorelTits.le_pCore 2 hnormal
      (hp.of_equiv (Subgroup.topEquiv (G := ↥H₂)).symm)
  have h1 : Nat.card (OTwoQuot H₂) = 1 := by
    have : (CFSG.Open.pCore 2 ↥H₂).index = 1 := Subgroup.index_eq_one.mpr (top_le_iff.mp hptop)
    exact this
  have h6 : Nat.card (OTwoQuot H₂) = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  omega

theorem stageSection146_of_inputs_nine (h1413 : StageLemma1413) (h11 : StageLemma14111)
    (h113 : StageLemma14113) (hedge : GoldschmidtEdgeBoundSubgroups.{0})
    (h2 : Stage1461Two) (h3 : Stage1461Three) (h5 : Stage1461Five)
    (h12 : Stage14612Part) (h15 : Stage14615) (h17 : Stage14617)
    (h20 : Stage14620) (h21 : Stage14621) (h22 : Stage14622)
    (h23 : Stage14623) (hD4 : Stage146D4A6) (h24 : Stage14624)
    (hF2 : Stage146FH2S3) (hF3 : Stage146FFour)
    (h9 : Stage1469) (h105 : Stage14610Five) (h634 : Stage1463Four) : StageSection146 :=
  stageSection146_of_inputs_eight h1413 h11 h113 hedge h2 h3 h5 h12 h15 h17 h20 h21 h22 h23
    (stage146D4_of hD4) h24 (stage146FH2_of hF2) hF3 h9 h105 h634

end Choice

end CFSG.Quasithin
