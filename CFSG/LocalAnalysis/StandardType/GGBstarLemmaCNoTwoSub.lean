module

public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLCx
public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTwE6

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

section Config

variable {G : Type} [Group G] [Finite G]

theorem twoSub_centralizer_eq_bot_of_rank {p : ℕ} (hp : p.Prime) {x : G} {L E T₀ : Subgroup G}
    (hE : IsElemAbelian p E) (hEL : E ≤ L ⊔ Subgroup.zpowers x)
    (hcard : p ^ (LargeEvenTwoLocalRank p G + 1) ≤ Nat.card E)
    (hTL : T₀ ≤ Subgroup.centralizer (L : Set G))
    (hTx : T₀ ≤ Subgroup.centralizer ({x} : Set G)) (hT2 : IsPGroup 2 T₀) : T₀ = ⊥ := by
  by_contra hT1
  have hcent : L ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer (T₀ : Set G) := by
    refine sup_le (fun l hl => ?_) ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro t ht
      exact (Subgroup.mem_centralizer_iff.mp (hTL ht) l hl).symm
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro t ht
      exact (Subgroup.mem_centralizer_iff.mp (hTx ht) x rfl).symm
  have hEN : E ≤ Subgroup.normalizer (T₀ : Set G) := fun e he =>
    Subgroup.centralizer_le_normalizer _ (hcent (hEL he))
  have := Fact.mk hp
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (isPGroup_of_isElemAbelian hE)
  have h1 := le_twoLocalRank_of_normalizes hp hT1 hT2 hE hEN hk
  rw [hk] at hcard
  have h2 := (Nat.pow_le_pow_iff_right hp.one_lt).mp hcard
  omega

theorem GGConfig.innLocal_of_noTwoSub {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig p B Bs x L D J) (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hL : commutator L = ⊤) {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    {I : Set (MulAut R)} (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hOD : GGOutdiagOdd p R I)
    (hY : ∀ T₀ : Subgroup G, T₀ ≤ Subgroup.centralizer (L : Set G) →
      T₀ ≤ Subgroup.centralizer ({x} : Set G) → IsPGroup 2 T₀ → T₀ = ⊥) :
    ∃ U : Subgroup G, U ≤ L ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set G) := by
  obtain ⟨-, -, -, -, -, hβ, hS, hst⟩ := hC.1
  rcases ggInnLocal_or_delta hβ.1 hβ.2.1 hS hnc hL θ hBN h3 hOD hst.2.1 with hU | hδ
  · exact hU
  · obtain ⟨T₀, hTL, hTx, hT2, -, hcomm⟩ := hδ
    exact absurd (by rw [hY T₀ hTL hTx hT2]; exact Subgroup.commutator_bot_left B) hcomm

theorem GGConfig.beta_twoLocal_of_noTwoSub {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hC : GGConfig p B Bs x L D J)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hL : commutator L = ⊤) {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    {I : Set (MulAut R)} (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hOD : GGOutdiagOdd p R I)
    (hY : ∀ T₀ : Subgroup G, T₀ ≤ Subgroup.centralizer (L : Set G) →
      T₀ ≤ Subgroup.centralizer ({x} : Set G) → IsPGroup 2 T₀ → T₀ = ⊥) :
    ∃ V : Subgroup R, V ≠ ⊥ ∧ IsPGroup 2 V ∧
      ∀ φ ∈ (ggBeta L θ hBN).range, ∀ v ∈ V, φ v ∈ V := by
  obtain ⟨U, hUL, hU1, hU2, hBU⟩ := hC.innLocal_of_noTwoSub hnc hL θ hBN h3 hOD hY
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hC.1.2.2.2.2.2.2.1.2.2.2.1.1
  set UL : Subgroup L := U.subgroupOf L with hUL'
  have hUL2 : IsPGroup 2 UL := hU2.comap_subtype
  refine ⟨UL.map (ggQuotHom θ), fun h => hU1 ?_, hUL2.map _, ?_⟩
  · have hZ : UL ≤ Subgroup.center L := by
      rw [← ker_ggQuotHom θ, ← Subgroup.map_eq_bot_iff]
      exact h
    refine hY U (fun u hu => ?_) (fun u hu => hLx (hUL hu)) hU2
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hz := Subgroup.mem_center_iff.mp (hZ (show (⟨u, hUL hu⟩ : L) ∈ UL from hu)) ⟨l, hl⟩
    exact (congrArg Subtype.val hz)
  · rintro _ ⟨b, rfl⟩ _ ⟨l, hl, rfl⟩
    refine ⟨ggGamma L hBN b l, ?_, (ggBeta_ggQuotHom L hBN θ b l).symm⟩
    show ((ggGamma L hBN b l : L) : G) ∈ U
    rw [ggGamma_coe]
    have hb := hBU b.2
    exact (Subgroup.mem_normalizer_iff.mp hb (l : G)).mp hl

theorem GGConfig.eq_bstar_of_card_range_lt {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) (hL : commutator L = ⊤) {R : Type} [Group R]
    (θ : L ⧸ Subgroup.center L ≃* R) (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hlift : GGTorusLift 3 4 R) (hlt : Nat.card (ggGamma L hN).range < 3 ^ 5) :
    B = Bs ∧ LargeEvenTwoLocalRank 3 G = 5 ∧ Nat.card (ggGamma L hN).range = 3 ^ 4 := by
  obtain ⟨hp, hBsE, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hm : 4 + 1 ≤ LargeEvenTwoLocalRank 3 G :=
    succ_le_twoLocalRank_of_torusLift hp hLx (hS.1.1.2 x hS.2.1) hS.2.2.1 hL θ hlift
  have hcard : Nat.card (ggGamma L hN).range * 3 = Nat.card Bs :=
    card_range_ggGamma_mul_of hp hBsE hxBs hS.2.2.1 hLx hS.2.2.2.2 hN
  have h4 : 3 ^ 4 ≤ Nat.card (ggGamma L hN).range :=
    (card_range_ggGamma_bstar_ge hcfg hL θ hN hlift).1
  have := Fact.mk hp
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (isPGroup_of_isElemAbelian hBsE)
  have hBc : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G := hS.1.2.1
  have hBle : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hcfg.2.1.1
  have hk5 : Nat.card Bs = 3 ^ 5 := by
    have h1 : 3 ^ 5 ≤ 3 ^ k := by rw [← hk, ← hcard]; omega
    have h2 : 3 ^ k < 3 ^ 6 := by rw [← hk, ← hcard]; omega
    have h1' := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h1
    have h2' := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp h2
    rw [hk]
    congr 1
    omega
  have hm5 : LargeEvenTwoLocalRank 3 G = 5 := by
    have h1 : 3 ^ LargeEvenTwoLocalRank 3 G ≤ 3 ^ 5 := by rw [← hBc, ← hk5]; exact hBle
    have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h1
    omega
  refine ⟨Subgroup.eq_of_le_of_card_ge hcfg.2.1.1 ?_, hm5, ?_⟩
  · rw [hk5, hBc, hm5]
  · rw [hk5] at hcard
    omega

@[expose] def GGTwE6CoverRank (R : Type) [Group R] : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    (∃ E : Subgroup L', IsElemAbelian 3 E ∧ 3 ^ 5 ≤ Nat.card E) ∧
    (3 ∣ Nat.card (Subgroup.center L') → ∃ E : Subgroup L', IsElemAbelian 3 E ∧ 3 ^ 6 ≤ Nat.card E)

theorem GGConfig.exists_elemAbelian_three_six {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) (hL : commutator L = ⊤) {R : Type} [Group R]
    (θ : L ⧸ Subgroup.center L ≃* R) (hcov : GGTwE6CoverRank R) :
    ∃ E : Subgroup G, IsElemAbelian 3 E ∧ E ≤ L ⊔ Subgroup.zpowers x ∧ 3 ^ 6 ≤ Nat.card E := by
  obtain ⟨hp, -, -, hLx, -⟩ := hcfg.tableB_facts
  have := Fact.mk hp
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hx3 : x ^ 3 = 1 := hS.1.1.2 x hS.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  obtain ⟨h5, h6⟩ := hcov L (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hL
  have hcardmap : ∀ E : Subgroup L, Nat.card (E.map L.subtype) = Nat.card E := fun E =>
    (Nat.card_congr (E.equivMapOfInjective _ L.subtype_injective).toEquiv).symm
  by_cases hZ : 3 ∣ Nat.card (Subgroup.center L)
  · obtain ⟨E, hE, hcard⟩ := h6 hZ
    exact ⟨E.map L.subtype, isElemAbelian_map hE L.subtype,
      (Subgroup.map_subtype_le E).trans le_sup_left, by rw [hcardmap]; exact hcard⟩
  · obtain ⟨E, hE, hcard⟩ := h5
    have hE' : IsElemAbelian 3 (E.map L.subtype) := isElemAbelian_map hE L.subtype
    have hxL : x ∉ L := by
      intro hxL
      apply hZ
      have hxc : (⟨x, hxL⟩ : L) ∈ Subgroup.center L := by
        rw [Subgroup.mem_center_iff]
        intro l
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hLx l.2))
      set z : Subgroup.center L := ⟨⟨x, hxL⟩, hxc⟩ with hz
      have hz3 : z ^ 3 = 1 := Subtype.ext (Subtype.ext hx3)
      have hz1 : z ≠ 1 := fun h => hx1 (congrArg (fun w : Subgroup.center L => ((w : L) : G)) h)
      rw [← orderOf_eq_prime hz3 hz1]
      exact orderOf_dvd_natCard z
    have hxE : x ∉ E.map L.subtype := fun h => hxL (Subgroup.map_subtype_le E h)
    have hcomm : ∀ e ∈ E.map L.subtype, e * x = x * e := fun e he =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLx (Subgroup.map_subtype_le E he))
    obtain ⟨k, hk⟩ := (isPGroup_of_isElemAbelian hE').exists_card_eq
    obtain ⟨hab, hc⟩ := isElemAbelian_sup_zpowers_of_card hp hE' hk hx3 hxE hcomm
    refine ⟨_, hab, sup_le_sup_right (Subgroup.map_subtype_le E) _, ?_⟩
    rw [hc]
    have h5k : 3 ^ 5 ≤ 3 ^ k := by rw [← hk, hcardmap]; exact hcard
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h5k
    exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem ggGamma_range_hypsKG {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {R : Type} [Group R]
    (θ : L ⧸ Subgroup.center L ≃* R) {I : Set (MulAut R)}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    IsElemAbelian p (ggGamma L hBsN).range ∧
      (∀ a ∈ (ggGamma L hBsN).range, ∃ φ ∈ I, ∀ l : L,
        φ (ggQuotHom θ l) = ggQuotHom θ (a l)) ∧
      GGTorusSelfCent p (ggGamma L hBsN).range := by
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  refine ⟨isElemAbelian_range hBc hBp _, ?_, ggTorusSelfCent_ggGamma hBsN hcfg.2.1.2.2.2⟩
  rintro _ ⟨b, rfl⟩
  exact ⟨ggBeta L θ hBsN b, ggBeta_mem L θ hBsN hBs3 b, fun l => ggBeta_ggQuotHom L hBsN θ b l⟩

end Config

end CFSG.StandardType
