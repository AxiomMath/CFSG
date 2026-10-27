module

public import CFSG.Quasithin.Background.C126Defs
public import CFSG.Quasithin.Background.C1PackC19
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3CompBasic

public section

namespace CFSG.Quasithin.C126

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

@[expose] def Blocks (H T : Subgroup G) : Prop :=
  ∃ (r : ℕ) (K : Fin r → Subgroup G), 1 ≤ r ∧
    (∀ i, IsChi0Block H (K i) ∧ ⁅K i, thompsonJ T⁆ = K i) ∧
    (∀ i j, i ≠ j → ⁅K i, K j⁆ = ⊥) ∧ twoResidual H = ⨆ i, K i ∧
    (∀ t ∈ T, ∀ i, ∃ j, B6.conjSub t (K i) = K j) ∧
    (∀ i j, ∃ t ∈ T, B6.conjSub t (K i) = K j)

theorem le_twoResidual_of_short {X B : Subgroup G} (hBX : B ≤ X) (hB : IsShort2 B) :
    B ≤ twoResidual X := by
  set K := twoResidual X with hK
  have hXN : X ≤ Subgroup.normalizer (K : Set G) := le_normalizer_twoResidual X
  set N : Subgroup ↥B := K.subgroupOf B with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    show ((g : G) * n * (g : G)⁻¹) ∈ K
    exact (Subgroup.mem_normalizer_iff.mp (hXN (hBX g.2)) n).mp hn
  have hp : IsPGroup 2 (↥B ⧸ N) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H b =>
      obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient X b (hBX b.2)
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hk
  have htop := hB.1 N hp
  intro b hb
  have : (⟨b, hb⟩ : ↥B) ∈ N := htop ▸ Subgroup.mem_top _
  exact this

omit [Finite G] in
theorem conjSub_eq_map (t : G) (K : Subgroup G) :
    B6.conjSub t K = K.map (MulAut.conj t).toMonoidHom := rfl

omit [Finite G] in
theorem isChi0Block_conjSub {H T K : Subgroup G} (hT : T ≤ H) (hK : IsChi0Block H K) {t : G}
    (ht : t ∈ T) : IsChi0Block H (B6.conjSub t K) := by
  rw [conjSub_eq_map]
  exact CFSG.QuasithinUnique.A5.G3.isChi0Block_conj hK (hT ht)

omit [Finite G] in
theorem commutator_conjSub_thompsonJ {T K : Subgroup G} (hKJ : ⁅K, thompsonJ T⁆ = K) {t : G}
    (ht : t ∈ T) : ⁅B6.conjSub t K, thompsonJ T⁆ = B6.conjSub t K := by
  have hJ : B6.conjSub t (thompsonJ T) = thompsonJ T :=
    B6.conjSub_eq_self (B6.le_normalizer_thompsonJ T ht)
  conv_lhs => rw [← hJ]
  rw [conjSub_eq_map, conjSub_eq_map, ← Subgroup.map_commutator, hKJ]

omit [Finite G] in
theorem conjClosure_eq_conjJoin (K T : Subgroup G) : conjClosure K T = conjJoin T K := by
  apply le_antisymm
  · refine conjClosure_le fun h hh z hz => ?_
    have : h * z * h⁻¹ ∈ K.map (MulAut.conj h).toMonoidHom :=
      ⟨z, hz, by simp [MulAut.conj_apply]⟩
    exact le_iSup (fun s : T => K.map (MulAut.conj (s : G)).toMonoidHom) ⟨h, hh⟩ this
  · refine iSup_le fun s => ?_
    rintro _ ⟨z, hz, rfl⟩
    exact mem_conjClosure s.2 hz

theorem blocks_of_oneBlock {H T : Subgroup G} (hF : CharTwo H) (hT : IsSylowTwoOf T H)
    (h : OneBlock H T) : Blocks H T := by
  classical
  obtain ⟨K, hK, hKJ, hH⟩ := h
  have hfin : Finite (Subgroup G) :=
    Finite.of_injective (SetLike.coe : Subgroup G → Set G) SetLike.coe_injective
  let 𝒦 : Set (Subgroup G) := {K' | ∃ t ∈ T, K' = B6.conjSub t K}
  obtain ⟨r, ⟨e⟩⟩ := Finite.exists_equiv_fin ↥𝒦
  let Kf : Fin r → Subgroup G := fun i => (e.symm i).1
  have hmem : ∀ i, ∃ t ∈ T, Kf i = B6.conjSub t K := fun i => (e.symm i).2
  have hKf : ∀ t ∈ T, ∃ j, Kf j = B6.conjSub t K := fun t ht =>
    ⟨e ⟨B6.conjSub t K, t, ht, rfl⟩, by simp [Kf]⟩
  have hblock : ∀ i, IsChi0Block H (Kf i) := fun i => by
    obtain ⟨t, ht, hti⟩ := hmem i
    rw [hti]
    exact isChi0Block_conjSub hT.1 hK ht
  have hne : ∀ i j, i ≠ j → Kf i ≠ Kf j := fun i j hij hKij =>
    hij (e.symm.injective (Subtype.ext hKij))
  have hsup_eq : (⨆ i, Kf i) = conjJoin T K := by
    apply le_antisymm
    · refine iSup_le fun i => ?_
      obtain ⟨t, ht, hti⟩ := hmem i
      rw [hti]
      exact le_iSup (fun s : T => K.map (MulAut.conj (s : G)).toMonoidHom) ⟨t, ht⟩
    · refine iSup_le fun s => ?_
      obtain ⟨j, hj⟩ := hKf s s.2
      show B6.conjSub (s : G) K ≤ _
      rw [← hj]
      exact le_iSup Kf j
  have hNH : conjJoin T K ≤ H :=
    CFSG.QuasithinUnique.A5.G3.conjJoin_le_of_le hT.1 hK.1.2.1
  have hTN : T ≤ Subgroup.normalizer (conjJoin T K : Set G) :=
    CFSG.QuasithinUnique.A5.G3.le_normalizer_conjJoin' T K
  have hHsup : T ⊔ conjJoin T K = H := by
    rw [← conjClosure_eq_conjJoin]
    exact hH.symm
  have hHN : H ≤ Subgroup.normalizer (conjJoin T K : Set G) := by
    rw [← hHsup]
    exact sup_le hTN Subgroup.le_normalizer
  have h2 := B6.isTwoQuotient_of_sup_eq hT.2.1 hHN hHsup
  have hres : twoResidual H = conjJoin T K := by
    apply le_antisymm
    · exact twoResidual_le_of_isTwoQuotient hNH hHN h2
    · refine iSup_le fun s => ?_
      have hb : IsChi0Block H (B6.conjSub (s : G) K) := isChi0Block_conjSub hT.1 hK s.2
      exact le_twoResidual_of_short hb.1.2.1 hb.1.1
  have hone : 1 ≤ r := (e ⟨K, 1, T.one_mem, (B6.conjSub_one K).symm⟩).pos
  refine ⟨r, Kf, hone, fun i => ⟨hblock i, ?_⟩, fun i j hij => ?_, hres.trans hsup_eq.symm,
    fun t ht i => ?_, fun i j => ?_⟩
  · obtain ⟨t, ht, hti⟩ := hmem i
    rw [hti]
    exact commutator_conjSub_thompsonJ hKJ ht
  · exact distinctBlocksCommuteStatement H (Kf i) (Kf j) hF (hblock i).1 (hblock j).1 (hne i j hij)
  · obtain ⟨t', ht', hti⟩ := hmem i
    obtain ⟨j, hj⟩ := hKf (t * t') (T.mul_mem ht ht')
    exact ⟨j, by rw [hj, hti, B6.conjSub_mul]⟩
  · obtain ⟨t₁, ht₁, hi⟩ := hmem i
    obtain ⟨t₂, ht₂, hj⟩ := hmem j
    refine ⟨t₂ * t₁⁻¹, T.mul_mem ht₂ (T.inv_mem ht₁), ?_⟩
    rw [hi, hj, ← B6.conjSub_mul, mul_assoc, inv_mul_cancel, mul_one]

end CFSG.Quasithin.C126
