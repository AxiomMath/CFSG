module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Hypotheses
public import CFSG.Quasithin.EmptyFaithful.S1421STC2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S1421

variable {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}

@[expose] def g0Of (T M H K1 : Subgroup G) : Subgroup G :=
  K1 ⊔ l2Of T H (yOfL22 T M) ⊔ sOf T K1

theorem exists_generator (st : Setting1427 T M H K1) :
    ∃ z : G, z ∈ quasithinOmegaOneCenter T ∧ z ≠ 1 ∧ z ^ 2 = 1 ∧
      (∀ t ∈ T, t * z = z * t) ∧ quasithinOmegaOneCenter T = Subgroup.zpowers z := by
  have hc := st.hyp.card_omegaOneCenter
  have hnt : Nontrivial (quasithinOmegaOneCenter T) :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (1 : quasithinOmegaOneCenter T)
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  obtain ⟨hzT, hzC, hz2⟩ := mem_quasithinOmegaOneCenter_iff.mp hz
  refine ⟨z, hz, hz1', hz2, fun t ht => Subgroup.mem_centralizer_iff.mp hzC t ht, ?_⟩
  have hle : Subgroup.zpowers z ≤ quasithinOmegaOneCenter T := (Subgroup.zpowers_le).mpr hz
  have hord : orderOf z = 2 := orderOf_eq_prime hz2 hz1'
  symm
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [hc, Nat.card_zpowers, hord]

omit [Finite G] in
theorem centralizer_le_mcOf {z : G} (hZ : quasithinOmegaOneCenter T = Subgroup.zpowers z) :
    Subgroup.centralizer ({z} : Set G) ≤ mcOf T := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff] at hg ⊢
  intro x hx
  rw [hZ] at hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hc : Commute z g := hg z rfl
  exact (hc.zpow_left k).eq

theorem z_mem_sOf (st : Setting1427 T M H K1) {z : G} (hz : z ∈ quasithinOmegaOneCenter T) :
    z ∈ sOf T K1 := by
  have hzT : z ∈ T := ((quasithinOmegaOneCenter_le_center T).trans inf_le_left) hz
  refine Subgroup.mem_inf.mpr ⟨hzT, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro k
  have hk : ∀ k ∈ K1, z * k = k * z := fun k hk =>
    Subgroup.mem_centralizer_iff.mp (K1_le_mcOf st hk) z hz
  constructor
  · intro hkK
    have : z * k * z⁻¹ = k := by rw [hk k hkK]; group
    rw [this]
    exact hkK
  · intro hkK
    have h1 := hk _ hkK
    have : k = z * k * z⁻¹ := by
      calc k = z⁻¹ * (z * k * z⁻¹) * z := by group
        _ = z⁻¹ * (z * k * z⁻¹ * z) := by rw [mul_assoc]
        _ = z⁻¹ * (z * (z * k * z⁻¹)) := by rw [← h1]
        _ = z * k * z⁻¹ := by group
    rw [this]
    exact hkK

theorem isSylowTwoOf_g0 {M₁ : Subgroup G} (hM₁ : InM (g0Of T M H K1) M₁)
    (hS : IsSylowTwoOf (sOf T K1) M₁) : IsSylowTwoOf (sOf T K1) (g0Of T M H K1) :=
  A4.isSylowTwoOf_mono hS (le_sup_right : sOf T K1 ≤ g0Of T M H K1) hM₁.2

theorem lemma115Hyp_g0 (st : Setting1427 T M H K1) {M₁ : Subgroup G}
    (hne : pCoreOf 2 (g0Of T M H K1) ≠ ⊥) (hM₁ : InM (g0Of T M H K1) M₁)
    (hS : IsSylowTwoOf (sOf T K1) M₁) {z : G} (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1)
    (hz2 : z ^ 2 = 1) (hzc : ∀ t ∈ T, t * z = z * t)
    (hZ : quasithinOmegaOneCenter T = Subgroup.zpowers z) :
    Lemma115Hyp (g0Of T M H K1) (sOf T K1) (mcOf T) z := by
  have hyp := st.hyp
  have hTMc : T ≤ mcOf T := hyp.toQTFE14.t_le_mc
  have hTSyl : IsSylowTwoOf T (mcOf T) := isSylowTwoOf_of_isSylowTwo hyp.sylow hTMc
  have hMcO : pCoreOf 2 (mcOf T) ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hyp.mc_max.1
  have hMcchar : CharTwo (mcOf T) := charTwo_of_inH' hyp.qtke hyp.sylow ⟨hTMc, hMcO⟩
  have hSG0 : sOf T K1 ≤ g0Of T M H K1 := le_sup_right
  have hSylG0 : IsSylowTwoOf (sOf T K1) (g0Of T M H K1) := isSylowTwoOf_g0 hM₁ hS
  have hSMc : sOf T K1 ≤ mcOf T := sOf_le_T.trans hTMc
  have hzS : z ∈ sOf T K1 := z_mem_sOf st hz
  refine ⟨hne, hSylG0, hMcchar, hMcO, hSMc, ?_, centralizer_le_mcOf hZ, hz1, hzS, ?_, hz2⟩
  · intro x hx
    obtain ⟨hxO, hxC⟩ := hx
    have hxT : x ∈ T := pCoreOf_two_le_of_isSylowTwoOf hTSyl hxO
    have hO2M₁ : pCoreOf 2 M₁ ≤ sOf T K1 := pCoreOf_two_le_of_isSylowTwoOf hS
    have hO2G0 : pCoreOf 2 M₁ ≤ pCoreOf 2 (g0Of T M H K1) :=
      le_pCoreOf_of_le_normalizer (hO2M₁.trans hSG0)
        (hM₁.2.trans (le_normalizer_pCoreOf 2 M₁)) (pCoreOf_isPGroup 2 M₁)
    have hG0O : pCoreOf 2 (g0Of T M H K1) ≤ pCoreOf 2 (g0Of T M H K1 ⊓ mcOf T) :=
      le_pCoreOf_of_le_normalizer
        (le_inf (pCoreOf_le 2 _) ((pCoreOf_two_le_of_isSylowTwoOf hSylG0).trans hSMc))
        (inf_le_left.trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
    have hxM₁ : x ∈ M₁ := by
      have hC : x ∈ Subgroup.centralizer (pCoreOf 2 M₁ : Set G) :=
        Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (hO2G0.trans hG0O)) hxC
      rw [← eq_normalizer_pCoreOf_of_isMaxTwoLocal hM₁.1]
      exact (Subgroup.centralizer_le_normalizer (s := (pCoreOf 2 M₁ : Set G))) hC
    have hxS : x ∈ sOf T K1 :=
      (A4.isSylowTwoOf_iff_maximal.mp hS).2.2 (T ⊓ M₁) inf_le_right hyp.sylow.1.to_inf_left
        (le_inf sOf_le_T hS.1) ⟨hxT, hxM₁⟩
    exact hSG0 hxS
  · rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact hzc s (sOf_le_T hs)

end S1421

end CFSG.Quasithin
