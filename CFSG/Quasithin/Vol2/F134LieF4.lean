module

public import CFSG.Quasithin.Vol2.F134LieF4Borel
public import CFSG.LieType.BorelTits.Ree
public import CFSG.LieType.Ree.LargeReeInvolutionTCentralizer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6LargeRee

public section

namespace CFSG.Quasithin.F134.LieF4

open CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.ABGLocalTools CFSG.QuasithinUnique.Setup.X6
  CFSG.Assembly.LowTwoRank CFSG.Quasithin.P134


theorem false_of_twistedF4 {X : Type} [Group X] [Finite X] {n : ℕ}
    (hX : ReeTitsModel X .twistedF4 2 n) {P U : Subgroup X} (hP : Nat.card P = 9)
    (hexp : ∀ x ∈ P, x ^ 3 = 1) (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤)
    (hmul : ∀ u ∈ U, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ U, u * x = y * s) : False := by
  obtain ⟨a, K, _, _, _, ha, hn, hK, ⟨e⟩⟩ := exists_mulEquiv_largeRee_model hX
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := hn ▸ hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL F4.tag K) := finite_modGL
  have hU' : IsSylowOf 2 U ⊤ := isSylowTwoOf_iff_isSylowOf.1 hU
  have hU₀ : IsSylowOf 2 (F4.reeFixedPosUnipotent K a) (F4.reeGamma K a) :=
    isSylowOf_iff.2 ⟨reeFixedPosUnipotent_le_reeGamma,
      (isPGroup_posUnipotent 2 F4.tag).to_le inf_le_left,
      not_dvd_index_reeFixedPosUnipotent (t := F4)⟩
  set φ₀ : X →* ModGL F4.tag K := (F4.reeGamma K a).subtype.comp e.toMonoidHom with hφ₀
  have hφ₀i : Function.Injective φ₀ := Subtype.val_injective.comp e.injective
  have hφ₀r : (⊤ : Subgroup X).map φ₀ = F4.reeGamma K a := by
    rw [hφ₀, ← Subgroup.map_map, Subgroup.map_top_of_surjective _ e.surjective, Subgroup.map_top,
      Subgroup.range_subtype]
  have hUφ₀ : IsSylowOf 2 (U.map φ₀) (F4.reeGamma K a) := by
    rw [← hφ₀r]
    exact isSylowOf_map_injective φ₀ hφ₀i hU'
  obtain ⟨g, hg, hgU⟩ := exists_mem_eq_map_conj_of_isSylowOf hUφ₀ hU₀
  set φ : X →* ModGL F4.tag K := (MulAut.conj g).toMonoidHom.comp φ₀ with hφ
  have hφi : Function.Injective φ := (MulAut.conj g).injective.comp hφ₀i
  have hφU : U.map φ = F4.reeFixedPosUnipotent K a := by
    rw [hφ, ← Subgroup.map_map, hgU]
  have hφr : φ.range = F4.reeGamma K a := by
    rw [MonoidHom.range_eq_map, hφ, ← Subgroup.map_map, hφ₀r]
    refine le_antisymm ?_ fun x hx => ⟨g⁻¹ * x * g, ?_, by simp [mul_assoc]⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact (F4.reeGamma K a).mul_mem ((F4.reeGamma K a).mul_mem hg hx)
        ((F4.reeGamma K a).inv_mem hg)
    · exact (F4.reeGamma K a).mul_mem ((F4.reeGamma K a).mul_mem
        ((F4.reeGamma K a).inv_mem hg) hx) hg
  have hH : Nat.card (P ⊔ U : Subgroup X) = 9 * Nat.card U :=
    card_sup_eq_of_mul hP hU.2.1 hmul
  have hcardU : Nat.card U = (2 ^ (2 * a + 1)) ^ 12 := by
    rw [← Subgroup.card_map_of_injective hφi, hφU,
      LargeReeInvolution.card_reeFixedPosUnipotent hK']
  have hrel : (U.subgroupOf (P ⊔ U)).index = 9 := by
    have h := Subgroup.relIndex_mul_card U (P ⊔ U)
    rw [inf_eq_left.2 le_sup_right, hH] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hBT : CFSG.LieType.BorelTits.Holds X 2 :=
    CFSG.LieType.BorelTits.holds_of_reeTitsModel hX (by decide)
  obtain ⟨Q, hQ, hHQ, hNQ⟩ := exists_proper_overgroup_of_holds hBT hU' le_sup_right (by
    rw [hrel, hH, hcardU]
    have h8 : 8 ^ 12 ≤ (2 ^ (2 * a + 1)) ^ 12 := Nat.pow_le_pow_left (by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)) 12
    have : Nat.factorial 9 = 362880 := by decide
    omega)
  refine false_of_le_reeGamma (Q := Q.map φ) (H := (P ⊔ U).map φ) (P := P.map φ) ha hK' ?_
    (Subgroup.map_le_range φ Q |>.trans hφr.le) ?_ (Subgroup.map_mono hHQ) ?_ ?_
    (Subgroup.map_mono le_sup_left) ?_ ?_
  ·
    intro b hb
    rw [← reeGamma_inf_normalizer_reeFixedPosUnipotent] at hb
    obtain ⟨hbΓ, hbN⟩ := hb
    rw [← hφr] at hbΓ
    obtain ⟨x, rfl⟩ := hbΓ
    refine ⟨x, hNQ ?_, rfl⟩
    have hle : F4.reeFixedPosUnipotent K a ≤ φ.range := by
      rw [← hφU]
      exact Subgroup.map_le_range φ U
    have hx : x ∈ (Subgroup.normalizer
        (F4.reeFixedPosUnipotent K a : Set (ModGL F4.tag K))).comap φ := hbN
    rwa [Subgroup.comap_normalizer_eq_of_le_range hle, ← hφU,
      Subgroup.comap_map_eq_self_of_injective hφi] at hx
  ·
    intro h
    apply hQ
    apply Subgroup.map_injective hφi
    rw [h, ← MonoidHom.range_eq_map, hφr]
  · rw [← hφU]
    exact Subgroup.map_mono le_sup_right
  · rw [Subgroup.card_map_of_injective hφi, hH, ← Subgroup.card_map_of_injective hφi, hφU]
  · rw [Subgroup.card_map_of_injective hφi, hP]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hexp x hx, map_one]

end CFSG.Quasithin.F134.LieF4

namespace CFSG.Quasithin.P134

open CFSG.Quasithin.F134 CFSG.Quasithin.F134.LieF4 CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem facts134E9_f4Even
    : ∀ n : ℕ,
    NoE9Config fun (X : Type) [Group X] => ReeTitsModel X .twistedF4 2 n := by
  intro n A _ _ L P T hL hcfg
  have hS := E9Config.isSylowTwoOf_inf hcfg
  refine false_of_twistedF4 hL (P := P.subgroupOf L) (U := (T ⊓ L).subgroupOf L) ?_ ?_
    (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_subgroupOf_top hS) ?_
  · rw [← hcfg.card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcfg.le).toEquiv
  · intro x hx
    exact Subtype.ext (by simpa using hcfg.exp x (Subgroup.mem_subgroupOf.mp hx))
  · intro u hu x hx
    obtain ⟨y, hy, s, hs, he⟩ := E9Config.mul_inf hcfg u (Subgroup.mem_subgroupOf.mp hu) x
      (Subgroup.mem_subgroupOf.mp hx)
    exact ⟨⟨y, hcfg.le hy⟩, Subgroup.mem_subgroupOf.mpr hy, ⟨s, hs.2⟩,
      Subgroup.mem_subgroupOf.mpr hs, Subtype.ext he⟩

end CFSG.Quasithin.P134
