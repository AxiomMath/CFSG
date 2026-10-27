module

public import CFSG.Quasithin.Recognition.St84.Gen.BigL2Slice
public import CFSG.Quasithin.Recognition.St84.Gen.PerfectGen
public import CFSG.Quasithin.Recognition.GoldschmidtF112RG24
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Rk2A

public section

namespace CFSG.Quasithin.F112R

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement

section Abstract

variable {G : Type} [Group G]

theorem le_centralizer_of_perfect_of_isL2Quot [Finite G] {L Z : Subgroup G} (hL : ⁅L, L⁆ = L)
    (hLZ : L ≤ Subgroup.normalizer (Z : Set G)) (hZpow : ∀ z : ↥Z, z ^ 2 = 1) {f : ℕ}
    (hf : 2 ≤ f) (hq : IsL2Quot f (oTwoQuot ↥L)) (hZcard : Nat.card Z ≤ 2 ^ f) :
    L ≤ Subgroup.centralizer (Z : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ2 : IsPGroup 2 ↥Z := fun z => ⟨1, by simpa using hZpow z⟩
  obtain ⟨d, hd⟩ := hZ2.exists_card_eq
  have hdf : d ≤ f :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (hd ▸ hZcard)
  have hdf' : d < 2 * f := by omega
  let ρ : ↥L →* MulAut ↥Z := Z.normalizerMonoidHom.comp (Subgroup.inclusion hLZ)
  have hperf : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hL
  have hρ : ρ = 1 :=
    CFSG.Quasithin.H13.Sec526.eq_one_of_isL2Quot (n := f) (f := d) hf hdf' hperf hq ρ hd
  intro ℓ hℓ
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have h2 : ρ ⟨ℓ, hℓ⟩ = 1 := by rw [hρ]; rfl
  have h3 : (ρ ⟨ℓ, hℓ⟩) ⟨z, hz⟩ = ⟨z, hz⟩ := by rw [h2]; rfl
  have h4 : ℓ * z * ℓ⁻¹ = z := by
    have h5 := congrArg (fun w : ↥Z => (w : G)) h3
    simpa [ρ, Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion] using h5
  calc z * ℓ = ℓ * z * ℓ⁻¹ * ℓ := by rw [h4]
    _ = ℓ * z := by group

theorem centerOf_le_centralizer_of_card [Finite G] {L P S : Subgroup G} (hL : ⁅L, L⁆ = L)
    (hLP : L ≤ P) (hct : CharTwo P) (hSP : S ≤ P) (hQS : pCoreOf 2 P ≤ S)
    {f : ℕ} (hf : 2 ≤ f) (hq : IsL2Quot f (oTwoQuot ↥L))
    (hZ : Nat.card (Subgroup.center ↥(pCoreOf 2 P)) ≤ 2 ^ f)
    (hZpow : ∀ z ∈ Subgroup.center ↥(pCoreOf 2 P), z ^ 2 = 1) :
    centerOf S ≤ Subgroup.centralizer (L : Set G) := by
  set Q := pCoreOf 2 P with hQ
  have hLZ : L ≤ Subgroup.normalizer (centerOf Q : Set G) := fun ℓ hℓ =>
    CFSG.Quasithin.H13.NQCat.G2Rad.mem_normalizer_centerOf
      (le_normalizer_pCoreOf 2 P (hLP hℓ))
  have hcard : Nat.card (centerOf Q) ≤ 2 ^ f := by
    rw [centerOf_eq_map_center, Subgroup.card_map_of_injective Q.subtype_injective]
    exact hZ
  have hpow : ∀ z : ↥(centerOf Q), z ^ 2 = 1 := by
    intro z
    let y : ↥Q := ⟨z, z.2.1⟩
    have hy : y ∈ Subgroup.center ↥Q :=
      Subgroup.mem_center_iff.mpr fun w => Subtype.ext
        (Subgroup.mem_centralizer_iff.mp z.2.2 (w : G) w.2)
    have hyz : Q.subtype y = (z : G) := rfl
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hyz, ← map_pow, hZpow y hy, map_one]
  have hLC := le_centralizer_of_perfect_of_isL2Quot hL hLZ hpow hf hq hcard
  rintro z ⟨hzS, hzc⟩
  have hzQ : z ∈ Q := hct ⟨hSP hzS, Subgroup.mem_centralizer_iff.mpr fun q hq' =>
    Subgroup.mem_centralizer_iff.mp hzc q (hQS hq')⟩
  have hzZ : z ∈ centerOf Q := ⟨hzQ, Subgroup.mem_centralizer_iff.mpr fun q hq' =>
    Subgroup.mem_centralizer_iff.mp hzc q (hQS hq')⟩
  rw [Subgroup.mem_centralizer_iff]
  intro ℓ hℓ
  exact (Subgroup.mem_centralizer_iff.mp (hLC hℓ) z hzZ).symm

end Abstract

section Model

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2 CFSG.Quasithin.H13.NQCat.G2Rad


variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem pow_eq_one_of_mem_center_of_isSpecialPGroup {p : ℕ} {P : Type*} [Group P]
    (h : IsSpecialPGroup p P) {z : P} (hz : z ∈ Subgroup.center P) : z ^ p = 1 := by
  obtain ⟨-, h | h⟩ := h
  · exact h.2 z
  · exact h.2.2 z hz

theorem isSpecialPow_radical_one_of_card {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    IsSpecialPow 2 (2 ^ f) 2 ↥(parabolicRadical Tag.G2 K {i1}) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := parabolicRadical Tag.G2 K {i1} with hQdef
  have hcQ : Nat.card ↥Q = (2 ^ f) ^ 5 := by
    rw [card_radical, hK]
  have hcQ' : Nat.card ↥Q = 2 ^ (5 * f) := by
    rw [hcQ, ← pow_mul, mul_comm]
  have hP : IsPGroup 2 ↥Q := IsPGroup.of_card hcQ'
  have hN1Q : (N1 : Subgroup (ModGL Tag.G2 K)) ≤ Q := by
    rw [← centerOf_parabolicRadical_one]
    exact inf_le_left
  have hmemN : ∀ x : ↥Q, (x : ModGL Tag.G2 K) ∈ (N1 : Subgroup (ModGL Tag.G2 K)) ↔
      coord (x : ModGL Tag.G2 K) = 0 := fun x => mem_N1_iff x.2
  have hZ : Subgroup.center ↥Q = (N1 : Subgroup (ModGL Tag.G2 K)).subgroupOf Q := by
    ext z
    rw [Subgroup.mem_subgroupOf, ← centerOf_parabolicRadical_one, centerOf_eq_map_center]
    exact (Subgroup.mem_map_iff_mem Q.subtype_injective).symm
  have hC : commutator ↥Q = Subgroup.center ↥Q := by
    apply le_antisymm
    · rw [hZ, commutator_def, Subgroup.commutator_le]
      intro x _ y _
      rw [Subgroup.mem_subgroupOf, hmemN, commutatorElement_def]
      push_cast
      rw [coord_mul (Q.mul_mem (Q.mul_mem x.2 y.2) (Q.inv_mem x.2)) (Q.inv_mem y.2),
        coord_mul (Q.mul_mem x.2 y.2) (Q.inv_mem x.2), coord_mul x.2 y.2, coord_inv' x.2,
        coord_inv' y.2]
      abel
    · intro z hz
      have h1 : (z : ModGL Tag.G2 K) ∈ ⁅Q, Q⁆ := by
        apply center_le_one
        rw [← centerOf, centerOf_eq_map_center]
        exact ⟨z, hz, rfl⟩
      rw [← Subgroup.map_subtype_commutator] at h1
      obtain ⟨w, hw, hwz⟩ := h1
      rwa [← Q.subtype_injective hwz]
  refine ⟨⟨hP, Or.inr ⟨hC, ?_, ?_⟩⟩, ?_, ?_⟩
  · haveI : (Subgroup.center ↥Q).Normal := inferInstance
    refine CFSG.Sporadic.Recognition.LyonsSims.frattini_eq_of_commutator_eq hP ?_ ?_
    · rw [← commutator_def]
      exact hC
    · intro a
      rw [hZ, Subgroup.mem_subgroupOf, hmemN, pow_two, Subgroup.coe_mul, coord_mul a.2 a.2]
      exact CharTwo.add_self_eq_zero _
  · intro z hz
    rw [hZ, Subgroup.mem_subgroupOf] at hz
    obtain ⟨c, hc⟩ := exists_of_mem_N1 hz
    apply Subtype.ext
    rw [Subgroup.coe_pow, hc, pow_two, gX_self]
    rfl
  · rw [hcQ]
  · rw [hZ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN1Q).toEquiv, card_N1, hK]

end Model

section Main

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2 CFSG.Quasithin.H13.Ch9.F112Pf
  CFSG.QuasithinUnique.Setup.X6


theorem y9G2q : Y9G2q := by
  intro G _ _ L1 L2 S f hF hf3 h1 h2 hA
  have hf2 : 2 ≤ f := by omega
  have hMF := hasModelFacts_g2 f hf2
  have hPO := perfectOver_of_hasModelFacts_of_isL2Quot hF.1 hf2 h1 hf2 h2 hMF hA
  obtain ⟨hB, hV1, hV2⟩ := vFact_of_hasModelFacts_of_isL2Quot hf2 h1 hf2 h2 hMF hA
  obtain ⟨hB1, hB2⟩ := bigB_le_normalizer hF.1
  have hc1 := perfectCore_vertex hB1 hB hPO.1
  have hc2 := perfectCore_vertex hB2 hB hPO.2.1
  have hn1 : L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    sup_le Subgroup.le_normalizer hB1
  have hn2 : L2 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) :=
    sup_le Subgroup.le_normalizer hB2
  have ho1 : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) = pCoreOf 2 L1 := by
    have := hV1.1
    rw [hc1] at this
    exact pCoreOf_eq_of_odd le_sup_left hn1 this
  have ho2 : pCoreOf 2 (L2 ⊔ bigB L1 L2 S) = pCoreOf 2 L2 := by
    have := hV2.1
    rw [hc2] at this
    exact pCoreOf_eq_of_odd le_sup_left hn2 this
  have hct1 : CharTwo (L1 ⊔ bigB L1 L2 S) := by
    rw [F1.parabolic_eq]
    exact hF.1.h1.charTwo
  have hct2 : CharTwo (L2 ⊔ bigB L1 L2 S) := by
    rw [← bigB_comm L1 L2 S, F1.parabolic_eq]
    exact hF.1.h2.charTwo
  have hQS : ∀ L : Subgroup G, S ≤ L → IsSylowTwoOf (S ⊓ L) L →
      pCoreOf 2 L ≤ S := by
    intro L hSL hsy
    rw [inf_eq_left.mpr hSL] at hsy
    exact hsy.le_of_normalizes (pCoreOf_le 2 L) (le_normalizer_pCoreOf 2 L)
      (pCoreOf_isPGroup 2 L)
  have hQS1 : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ S := ho1 ▸ hQS L1 hPO.2.2.1 hF.1.h1.sylow
  have hQS2 : pCoreOf 2 (L2 ⊔ bigB L1 L2 S) ≤ S := ho2 ▸ hQS L2 hPO.2.2.2 hF.1.h2.sylow
  have hp1 : ⁅L1, L1⁆ = L1 := (perfectCore_eq_self_iff L1).mp hPO.1
  have hp2 : ⁅L2, L2⁆ = L2 := (perfectCore_eq_self_iff L2).mp hPO.2.1
  obtain ⟨Y, _, hY, T, M₁, M₂, hp, ⟨iso0⟩⟩ := hA
  obtain ⟨hfinY, -⟩ := hMF Y hY
  have hX : ChevalleyExceptionalModel Y .G2 2 f := by
    rcases hY with ⟨h, -⟩ | ⟨-, hL⟩
    · omega
    · rcases hL with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
      · exact absurd h (by decide)
      · exact h
      · exact absurd h (by decide)
      · exact absurd h (by decide)
  obtain ⟨K, _, _, _, φ, hK, hφ, hres, -⟩ := even_rank_two_residual_G2 hX hp.1
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hT' : T = ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)).map
      φ.symm.toMonoidHom := by
    rw [← hφ, Subgroup.map_map]
    have e : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id Y := by
      ext
      simp
    rw [e, Subgroup.map_id]
  have ha : ∀ j : Fin 2, T ≤ perfectCore (((parabolicSubgroup Tag.G2 K {g2Index j}).subgroupOf
      (adjointGroup Tag.G2 K)).map φ.symm.toMonoidHom) := by
    intro j
    rw [hT', perfectCore_map_inj _ φ.symm.injective]
    apply Subgroup.map_mono
    intro x hx
    rw [CFSG.Quasithin.H13.Sec53F.G2.mem_perfectCore_subgroupOf
      (parabolicSubgroup_le_adjointGroup Tag.G2 K {g2Index j})]
    exact posUnipotent_le_perfectCore_g2 hK4 _ hx
  have hns : ∀ (L : Subgroup G) (M : Subgroup Y), (↥(L ⊔ bigB L1 L2 S) ≃* ↥M) →
      IsL2Quot f (oTwoQuot ↥L) → ¬ Group.IsSolvable ↥M := by
    intro L M e hq hs
    apply not_isSolvable_of_isL2Quot hf2 hq
    have : Group.IsSolvable ↥(L ⊔ bigB L1 L2 S) :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (le_sup_left : L ≤ L ⊔ bigB L1 L2 S))
  obtain ⟨j₁, j₂, hj, hd₁, hd₂⟩ := exists_residual_indices hres ha hp
    (hns L1 M₁ iso0.φ1 h1) (hns L2 M₂ iso0.φ2 h2)
  have E : ∀ (L : Subgroup G) (M : Subgroup Y) (j : Fin 2),
      perfectCore (L ⊔ bigB L1 L2 S) = L → (↥(L ⊔ bigB L1 L2 S) ≃* ↥M) →
      perfectCore M = perfectCore (((parabolicSubgroup Tag.G2 K {g2Index j}).subgroupOf
        (adjointGroup Tag.G2 K)).map φ.symm.toMonoidHom) →
      pCoreOf 2 (L ⊔ bigB L1 L2 S) = pCoreOf 2 L →
      Nonempty (↥(pCoreOf 2 (L ⊔ bigB L1 L2 S)) ≃*
        ↥(parabolicRadical Tag.G2 K {g2Index j})) := by
    intro L M j hc ψ hd ho
    obtain ⟨e⟩ := nonempty_perfectCore_mulEquiv ψ
    rw [hc, hd] at e
    obtain ⟨e'⟩ := nonempty_pCore_equiv φ hK hf2 (g2Index j)
    exact ⟨(MulEquiv.subgroupCongr ho).trans ((pCoreOfMulEquiv e 2).trans e')⟩
  obtain ⟨e1⟩ := E L1 M₁ j₁ hc1 iso0.φ1 hd₁ ho1
  obtain ⟨e2⟩ := E L2 M₂ j₂ hc2 iso0.φ2 hd₂ ho2
  have hcard : ∀ (j : Fin 2) (A : Subgroup G),
      (↥A ≃* ↥(parabolicRadical Tag.G2 K {g2Index j})) → Nat.card A = (2 ^ f) ^ 5 := by
    intro j A e
    rw [Nat.card_congr e.toEquiv, card_radical, hK]
  have hspec : ∀ (j : Fin 2) (A : Subgroup G), g2Index j = i1 →
      (↥A ≃* ↥(parabolicRadical Tag.G2 K {g2Index j})) → IsSpecialPow 2 (2 ^ f) 2 ↥A := by
    intro j A hj' e
    rw [hj'] at e
    exact IsSpecialPow.of_mulEquiv e.symm (isSpecialPow_radical_one_of_card hK)
  obtain ⟨j, hjI⟩ := g2Index_surjective i1
  have hjj : j = j₁ ∨ j = j₂ :=
    (by decide : ∀ a b c : Fin 2, a ≠ b → c = a ∨ c = b) j₁ j₂ j hj
  refine ⟨?_, hPO⟩
  rcases hjj with rfl | rfl
  · have hs := hspec j _ hjI e1
    refine Or.inl ⟨fun _ => centerOf_le_centralizer_of_card hp1 le_sup_left hct1
      (hPO.2.2.1.trans le_sup_left) hQS1 hf2 h1 (by rw [hs.2.2])
      (fun z hz => pow_eq_one_of_mem_center_of_isSpecialPGroup hs.1 hz), hs, hcard j₂ _ e2⟩
  · have hs := hspec j _ hjI e2
    refine Or.inr ?_
    have hbc : bigB L2 L1 S = bigB L1 L2 S := bigB_comm L1 L2 S
    unfold G2qOriented
    rw [hbc]
    refine ⟨fun _ => centerOf_le_centralizer_of_card hp2 le_sup_left hct2
      (hPO.2.2.2.trans le_sup_left) hQS2 hf2 h2 (by rw [hs.2.2])
      (fun z hz => pow_eq_one_of_mem_center_of_isSpecialPGroup hs.1 hz), hs, hcard j₁ _ e1⟩

end Main

end CFSG.Quasithin.F112R
