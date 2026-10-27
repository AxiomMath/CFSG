module

public import CFSG.Quasithin.EmptyFaithful.SBc14Pair
public import CFSG.Quasithin.EmptyFaithful.SBc13C
public import CFSG.Quasithin.EmptyFaithful.S146P14

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

namespace SBc14

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ K₁ K₂ : Subgroup G}
  {t s : G}

theorem Z_le_pCoreOf_K₂ (S : Setting146 G T M) (h5 : Stage1461Five) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (hdec : IsDecP T M H p H₀ H₁ H₂ t)
    (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s) : quasithinOmegaOneCenter T ≤ pCoreOf 2 K₂ := by
  have hH : IsHTM T M H := hred.isHTM
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have hG1 : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hK₂G : K₂ ≤ mcOf T := hset.le_mcOf S hred
  obtain ⟨-, hZ₂⟩ := Z_le_commutator_of_isDecP h5 S hred hdec
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) (mcOf T)) := S.lemma_14_5_15_two hG1
  have hUG : conjClosure (VZ T M) (mcOf T) ≤ mcOf T := fun u hu =>
    S.mem_mcOf_of_mem_conjClosure hG1 hu
  have hUp : IsPGroup 2 (conjClosure (VZ T M) (mcOf T)) := fun g =>
    ⟨1, Subtype.ext (by simpa using hUab.2 g g.2)⟩
  have hUQ : conjClosure (VZ T M) (mcOf T) ≤ pCoreOf 2 (mcOf T) :=
    le_pCoreOf_of_le_normalizer 2 hUG (le_normalizer_conjClosure _ _) hUp
  have hUU : conjClosure (VZ T M) H ≤ conjClosure (VZ T M) (mcOf T) :=
    conjClosure_mono le_rfl hHG
  have hZW : quasithinOmegaOneCenter T ≤ ⁅conjClosure (VZ T M) (mcOf T), K₂⁆ :=
    hZ₂.trans (Subgroup.commutator_mono hUU hset.oTwo₂)
  have hQ₂ := pCoreOf_mcOf_le_g2 S hred hdec hset
  have hWK : ⁅conjClosure (VZ T M) (mcOf T), K₂⁆ ≤ K₂ := by
    refine Subgroup.commutator_le.mpr fun u hu k hk => ?_
    have h1 : u * k * u⁻¹ ∈ K₂ :=
      (Subgroup.mem_normalizer_iff.mp (hQ₂ (hUQ hu)) k).mp hk
    rw [commutatorElement_def]
    exact K₂.mul_mem h1 (K₂.inv_mem hk)
  have hWU : ⁅conjClosure (VZ T M) (mcOf T), K₂⁆ ≤ conjClosure (VZ T M) (mcOf T) :=
    S145.commutator_le_of_le_normalizer (hK₂G.trans (le_normalizer_conjClosure _ _))
  have hW2 : IsPGroup 2 ↥(⁅conjClosure (VZ T M) (mcOf T), K₂⁆ : Subgroup G) :=
    ((pCoreOf_isPGroup 2 (mcOf T)).to_le hUQ).to_le hWU
  have hKN : K₂ ≤ Subgroup.normalizer
      ((⁅conjClosure (VZ T M) (mcOf T), K₂⁆ : Subgroup G) : Set G) := fun k hk =>
    mem_normalizer_commutator_P14 ((le_normalizer_conjClosure _ _) (hK₂G hk))
      (Subgroup.le_normalizer hk)
  exact hZW.trans (le_pCoreOf_of_le_normalizer 2 hWK hKN hW2)

theorem sqtkGroup_g2 (S : Setting146 G T M) (h5 : Stage1461Five) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (hdec : IsDecP T M H p H₀ H₁ H₂ t)
    (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s) : SQTKGroup ↥(g2_14615 K₂) := by
  have hZK := Z_le_pCoreOf_K₂ S h5 hred hdec hset
  have hP : pCoreOf 2 (g2_14615 K₂) ≠ ⊥ := by
    intro hbot
    have hle : pCoreOf 2 K₂ ≤ pCoreOf 2 (g2_14615 K₂) :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K₂).trans Subgroup.le_normalizer)
        (normalizer_le_normalizer_pCoreOf 2 K₂) (pCoreOf_isPGroup 2 K₂)
    have hZb : quasithinOmegaOneCenter T ≤ ⊥ := hbot ▸ (hZK.trans hle)
    have h1 : Nat.card (quasithinOmegaOneCenter T) = 1 := by
      rw [le_bot_iff.mp hZb]
      exact Subgroup.card_bot
    have h2 := S.card_Z
    omega
  exact ⟨stronglyQuasithin_of_pCoreOf_ne_bot S.hyp.qtke hP,
    kGroup_of_pCoreOf_ne_bot S.hyp.qtke S.hyp.simple S.hyp.nonabelian hP⟩

theorem hypC23_of_ctx (S : Setting146 G T M) (h5 : Stage1461Five) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (hdec : IsDecP T M H p H₀ H₁ H₂ t)
    (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s) (hG₂ : ¬ g2_14615 K₂ ≤ mcOf T) :
    HypC23 (g2_14615 K₂) (pCoreOf 2 (mcOf T)) (g12_14615 T K₂) ∧
      ¬ oTwoFstarIn (g2_14615 K₂) ≤ g12_14615 T K₂ := by
  have hQ₂ := pCoreOf_mcOf_le_g2 S hred hdec hset
  have hOeq := pCoreOf_g12_eq S hred hdec hset
  have hQbot : pCoreOf 2 (mcOf T) ≠ ⊥ := by
    intro hbot
    have hZb : quasithinOmegaOneCenter T ≤ ⊥ := hbot ▸ SBc13.Z_le_pCoreOf_mcOf S
    have h1 : Nat.card (quasithinOmegaOneCenter T) = 1 := by
      rw [le_bot_iff.mp hZb]
      exact Subgroup.card_bot
    have h2 := S.card_Z
    omega
  have hNQ : Subgroup.normalizer (pCoreOf 2 (mcOf T) : Set G) = mcOf T := by
    refine SBc13.normalizer_eq_mcOf_of_char S le_rfl hQbot ?_
    rw [Subgroup.subgroupOf_self]
    infer_instance
  have hinf : g2_14615 K₂ ⊓ Subgroup.normalizer (pCoreOf 2 (mcOf T) : Set G) =
      g12_14615 T K₂ := by
    rw [hNQ, inf_comm]
    rfl
  refine ⟨⟨sqtkGroup_g2 S h5 hred hdec hset, ⟨hQ₂, hQbot, ?_⟩,
    inf_le_right, ?_, ?_⟩, ?_⟩
  · rw [hinf, hOeq]
  · refine iSup_le fun C => iSup_le fun hCQ => iSup_le fun hC => iSup_le fun hchar => ?_
    rw [SBc13.normalizer_eq_mcOf_of_char S hCQ hC hchar, inf_comm]
    exact le_rfl
  · have hcc : conjClosure (pCoreOf 2 (mcOf T)) (g12_14615 T K₂) = pCoreOf 2 (mcOf T) := by
      refine le_antisymm (conjClosure_le fun h hh x hx => ?_) (le_conjClosure _ _)
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (mcOf T) hh.1) x).mp hx
    rw [hcc]
    refine ⟨le_rfl, pCoreOf_isPGroup 2 _, ?_⟩
    rw [Subgroup.subgroupOf_self, Subgroup.index_top]
    norm_num
  · intro hle
    have hX : oTwoFstarIn (g2_14615 K₂) ≤ g2_14615 K₂ ⊓ mcOf T :=
      le_inf (oTwoFstarIn_le _) (hle.trans inf_le_left)
    have h1 : pCoreOf 2 (g2_14615 K₂ ⊓ mcOf T) = pCoreOf 2 (g2_14615 K₂) :=
      a4_4_1 (pCoreOf_le_oTwoFstarIn _) hX (a44Hyp_oTwoFstarIn _)
    have h2 : pCoreOf 2 (g2_14615 K₂) = pCoreOf 2 (mcOf T) := by
      rw [← h1, inf_comm]
      exact hOeq
    have h3 : g2_14615 K₂ ≤ mcOf T := by
      have := le_normalizer_pCoreOf 2 (g2_14615 K₂)
      rw [h2, hNQ] at this
      exact this
    exact hG₂ h3

theorem charTwo_g12 (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (hdec : IsDecP T M H p H₀ H₁ H₂ t) (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s) :
    CharTwo (g12_14615 T K₂) := by
  have hchar : CharTwo (mcOf T) := charTwo_of_inH' S.hyp.qtke S.hyp.sylow S.isHTM_mcOf.1
  have hO := pCoreOf_g12_eq S hred hdec hset
  intro y hy
  rw [hO] at hy ⊢
  exact hchar ⟨hy.1.1, hy.2⟩

theorem charTwo_g2 (S : Setting146 G T M) (h5 : Stage1461Five) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (hdec : IsDecP T M H p H₀ H₁ H₂ t)
    (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s) : CharTwo (g2_14615 K₂) := by
  set Q := pCoreOf 2 (g2_14615 K₂) with hQ
  set U : Subgroup G := g2_14615 K₂ ⊓ Subgroup.centralizer (Q : Set G) with hU
  have hZK := Z_le_pCoreOf_K₂ S h5 hred hdec hset
  have hKQ : pCoreOf 2 K₂ ≤ Q :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K₂).trans Subgroup.le_normalizer)
      (normalizer_le_normalizer_pCoreOf 2 K₂) (pCoreOf_isPGroup 2 K₂)
  have hZQ : quasithinOmegaOneCenter T ≤ Q := hZK.trans hKQ
  have hUG₁₂ : U ≤ g12_14615 T K₂ :=
    le_inf (inf_le_right.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hZQ)))
      inf_le_left
  have hUn : ∀ g ∈ g2_14615 K₂, ∀ u ∈ U, g * u * g⁻¹ ∈ U := by
    intro g hg u hu
    obtain ⟨huG, huC⟩ := Subgroup.mem_inf.mp hu
    refine Subgroup.mem_inf.mpr
      ⟨(g2_14615 K₂).mul_mem ((g2_14615 K₂).mul_mem hg huG) ((g2_14615 K₂).inv_mem hg),
        Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
    have hq' : g⁻¹ * q * g ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_pCoreOf 2 (g2_14615 K₂) ((g2_14615 K₂).inv_mem hg)) q).mp hq
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp huC _ hq'
    calc q * (g * u * g⁻¹) = g * ((g⁻¹ * q * g) * u) * g⁻¹ := by group
      _ = g * (u * (g⁻¹ * q * g)) * g⁻¹ := by rw [h1]
      _ = g * u * g⁻¹ * q := by group
  have hGN : g2_14615 K₂ ≤ Subgroup.normalizer (U : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hUn g hg h hh, fun hh => ?_⟩
    have := hUn g⁻¹ ((g2_14615 K₂).inv_mem hg) _ hh
    simpa [mul_assoc] using this
  have hG₁₂G₂ : g12_14615 T K₂ ≤ g2_14615 K₂ := inf_le_right
  have hCU : CharTwo U :=
    CharTwo.of_normal (charTwo_g12 S hred hdec hset) hUG₁₂
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hUG₁₂).mpr (hG₁₂G₂.trans hGN))
  exact CharTwo.of_normal_of_centralizer_le hCU inf_le_left
    ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hGN) le_rfl

end SBc14

end CFSG.Quasithin
