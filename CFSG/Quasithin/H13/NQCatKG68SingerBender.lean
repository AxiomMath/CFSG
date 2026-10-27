module

public import CFSG.Quasithin.H13.NQCatKG68Singer
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneModels

public section

namespace CFSG.Quasithin.H13.KG68.Singer

open CFSG.Open CFSG.QuasithinUnique

variable {S : Type} [Group S]

theorem cartanSingerConcl_of_regular [Finite S] {P V : Subgroup S} (hP : IsSylowTwoOf P ⊤)
    (hV : ∀ v, v ∈ V ↔ v ∈ P ∧ ∀ t ∈ P, v * t = t * v)
    (hcyc : IsCyclic V.normalizerMonoidHom.range)
    (hreg : ∀ v w : V, v ≠ 1 → w ≠ 1 →
      ∃! α : V.normalizerMonoidHom.range, (α : MulAut V) v = w)
    (hNVP : ∀ n ∈ Subgroup.normalizer (V : Set S), n ∈ Subgroup.normalizer (P : Set S))
    {𝓡 : Subgroup (MulAut S)} {G : Subgroup S} (hG : CartanSingerHyp P 𝓡 G) :
    CartanSingerConcl P 𝓡 G := by
  classical
  set A := V.normalizerMonoidHom.range with hAdef
  have hNPV : ∀ n ∈ Subgroup.normalizer (P : Set S), n ∈ Subgroup.normalizer (V : Set S) := by
    intro n hn
    have key : ∀ m ∈ Subgroup.normalizer (P : Set S), ∀ v ∈ V, m * v * m⁻¹ ∈ V := by
      intro m hm v hv
      obtain ⟨hvP, hvc⟩ := (hV v).1 hv
      refine (hV _).2 ⟨(Subgroup.mem_normalizer_iff.1 hm v).1 hvP, fun t ht => ?_⟩
      have ht' : m⁻¹ * t * m ∈ P := by
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem hm) t).1 ht
        rwa [inv_inv] at this
      have h1 := hvc _ ht'
      calc m * v * m⁻¹ * t = m * (v * (m⁻¹ * t * m)) * m⁻¹ := by group
        _ = m * ((m⁻¹ * t * m) * v) * m⁻¹ := by rw [h1]
        _ = t * (m * v * m⁻¹) := by group
    refine Subgroup.mem_normalizer_iff.2 fun v => ⟨key n hn v, fun hv => ?_⟩
    have := key n⁻¹ (inv_mem hn) _ hv
    rwa [inv_inv, show n⁻¹ * (n * v * n⁻¹) * n = v by group] at this
  let act : ↥(Subgroup.normalizer (P : Set S)) →* ↥A := (V.normalizerMonoidHom.rangeRestrict).comp
    (Subgroup.inclusion fun n hn => hNPV n hn)
  have hact : ∀ (n : ↥(Subgroup.normalizer (P : Set S))) (v : ↥V),
      (((act n : MulAut ↥V) v : ↥V) : S) = (n : S) * (v : S) * (n : S)⁻¹ :=
    fun n v => rfl
  have hact_surj : Function.Surjective act := by
    rintro ⟨α, ⟨m, rfl⟩⟩
    exact ⟨⟨m, hNVP m m.2⟩, rfl⟩
  obtain ⟨g₀, hg₀G, hg₀⟩ : ∃ g ∈ G, g ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : G = ⊥ := (Subgroup.eq_bot_iff_forall G).2 hcon
    have := hG.four_le
    rw [hbot, Subgroup.card_bot] at this
    omega
  have hGV : ∀ g ∈ G, g ∈ V := fun g hg => (hV g).2 (hG.le g hg)
  let v₀ : ↥V := ⟨g₀, hGV g₀ hg₀G⟩
  have hv₀1 : v₀ ≠ 1 := fun h => hg₀ (congrArg Subtype.val h)
  have hcancel : ∀ α β : ↥A, (α : MulAut ↥V) v₀ = (β : MulAut ↥V) v₀ → α = β := by
    intro α β h
    have hw : (α : MulAut ↥V) v₀ ≠ 1 := fun h1 => hv₀1 (by
      rw [← map_one (α : MulAut ↥V)] at h1
      exact (α : MulAut ↥V).injective h1)
    exact (hreg v₀ _ hv₀1 hw).unique rfl h.symm
  have : IsCyclic ↥A := hcyc
  refine cartanSingerConcl_of_hom hP Subgroup.le_normalizer le_rfl act hact_surj hG
    (fun ρ hρ n hn => hG.apply_mem_normalizer hρ hn) hg₀G hg₀ (fun n n' h => ?_)
    (fun g hg hg1 => ?_) (fun n hn g hg => ?_) fun Λ _ => inferInstance
  · exact hcancel _ _ (Subtype.ext (by rw [hact, hact]; exact h))
  · obtain ⟨α, hα, -⟩ := hreg v₀ ⟨g, hGV g hg⟩ hv₀1 (fun h => hg1 (congrArg Subtype.val h))
    obtain ⟨n, rfl⟩ := hact_surj α
    refine ⟨n, ?_⟩
    change (((act n : MulAut ↥V) v₀ : ↥V) : S) = g
    rw [hα]
  · have h1 : (n : S) * g * (n : S)⁻¹ = g := by
      have h2 := hact n ⟨g, hGV g hg⟩
      rw [hn, OneMemClass.coe_one, MulAut.one_apply] at h2
      exact h2.symm
    calc (n : S) * g = (n : S) * g * (n : S)⁻¹ * n := by group
      _ = g * n := by rw [h1]

theorem cartanSingerCover_of_hasFieldScalarStructure [Finite S] (Q : Sylow 2 S)
    {V : Subgroup S} {q : ℕ}
    (hVZ : V = (Subgroup.center (Q : Subgroup S)).map (Q : Subgroup S).subtype)
    (hS : HasFieldScalarStructure V q) (hq : Even q)
    (hemb : fusionStronglyEmbedded (Subgroup.normalizer ((Q : Subgroup S) : Set S))) :
    CartanSingerCover S := by
  have hV : ∀ v, v ∈ V ↔ v ∈ (Q : Subgroup S) ∧ ∀ t ∈ (Q : Subgroup S), v * t = t * v := by
    intro v
    rw [hVZ]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, fun t ht => (congrArg Subtype.val (Subgroup.mem_center_iff.1 hw ⟨t, ht⟩)).symm⟩
    · rintro ⟨hvQ, hv⟩
      exact ⟨⟨v, hvQ⟩, Subgroup.mem_center_iff.2 fun t => Subtype.ext (hv t t.2).symm, rfl⟩
  have hNVQ : ∀ n ∈ Subgroup.normalizer (V : Set S),
      n ∈ Subgroup.normalizer ((Q : Subgroup S) : Set S) := by
    intro n hn
    by_contra hnQ
    set M := Subgroup.normalizer ((Q : Subgroup S) : Set S)
    have hodd := hemb.2.2 n hnQ
    have hVM : V ≤ M ⊓ M.map (MulAut.conj n⁻¹).toMonoidHom := by
      intro v hv
      refine ⟨Subgroup.le_normalizer ((hV v).1 hv).1, ⟨n * v * n⁻¹, ?_, ?_⟩⟩
      · exact Subgroup.le_normalizer
          ((hV _).1 ((Subgroup.mem_normalizer_iff.1 hn v).1 hv)).1
      · change n⁻¹ * (n * v * n⁻¹) * n⁻¹⁻¹ = v
        group
    have h1 := Subgroup.card_dvd_of_le hVM
    rw [hS.card_eq] at h1
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (hq.two_dvd.trans h1))
  obtain ⟨hcyc, -, hreg⟩ := hS.normalizer_action
  exact cartanSingerCover_of_sylow Q fun _ _ hG =>
    cartanSingerConcl_of_regular (isSylowTwoOf_top_of_sylow Q) hV hcyc hreg hNVQ hG

theorem cartanSingerCover_psu3 {f : ℕ} (hf : 2 ≤ f) : CartanSingerCover ↥(PSU3 2 f) := by
  have := finite_psu3 f
  obtain ⟨P, hP⟩ := unitary_standard f hf
  have Q : Sylow 2 ↥(PSU3 2 f) := P
  set V := (CFSG.omega₁ (G := (P : Subgroup ↥(PSU3 2 f))) (p := 2)).map
    (P : Subgroup ↥(PSU3 2 f)).subtype with hVdef
  have hVZ := (unitary_rank_one_involution_normalizer f hf P V hVdef).1
  exact cartanSingerCover_of_hasFieldScalarStructure P hVZ hP
    ((Nat.even_pow' (by omega)).2 even_two) ((bender_psu3_borel_full f hf P).1)

theorem cartanSingerCover_sz {a : ℕ} (ha : 1 ≤ a) :
    CartanSingerCover ↥(Sz a) := by
  have := finite_sz a
  obtain ⟨P, hP⟩ := suzuki_standard a ha
  set V := (CFSG.omega₁ (G := (P : Subgroup ↥(Sz a))) (p := 2)).map
    (P : Subgroup ↥(Sz a)).subtype with hVdef
  have hVZ := (suzuki_rank_one_involution_normalizer a ha P V hVdef).1
  exact cartanSingerCover_of_hasFieldScalarStructure P hVZ hP
    ((Nat.even_pow' (by omega)).2 even_two) ((bender_suzuki_borel_full a ha P).1)

end CFSG.Quasithin.H13.KG68.Singer
