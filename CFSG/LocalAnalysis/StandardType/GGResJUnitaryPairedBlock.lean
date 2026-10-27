module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitSU
public import CFSG.LocalAnalysis.StandardType.GGResJUnitaryActorNormalization
public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenCore
public import CFSG.LocalAnalysis.StandardType.GGNsFrameCompFrame
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LieType.SeitzGeneration.NonabLinear
public import CFSG.RankThree.PartOne.CTP.SeitzUSplit
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.StandardType.GGResIPumpLineTransfer
public import CFSG.LocalAnalysis.StandardType.GGResJLineA3
public import CFSG.LocalAnalysis.StandardType.GGResJUnitaryCubicBlock
public import CFSG.LocalAnalysis.StandardType.GGResJLineBCGamma
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpElt
public import CFSG.LocalAnalysis.StandardType.GGSignedPermCount
public import CFSG.LocalAnalysis.StandardType.GGTwSUSigned
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeProp1010
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalUnitHypLift
public import CFSG.LocalAnalysis.StandardType.GGKGForkUSplitOddL
public import CFSG.LocalAnalysis.StandardType.GGKGForkUSplitC
public import CFSG.LocalAnalysis.StandardType.GGKGForkUSplitOddC
public import CFSG.LocalAnalysis.StandardType.GGKGForkUSplitE
public import CFSG.LocalAnalysis.StandardType.GGKGForkUSplitOddE
public import CFSG.GroupTheory.WeirSylow.CrossRankUnitary
public import CFSG.GroupTheory.WeirSylow.UniqueE27Symplectic
public import CFSG.GroupTheory.ElemAbelianRank

public section

namespace CFSG.StandardType

namespace ResJUnitaryPaired

open Module Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LinearGroups SUTB NoOffOm NsFrameComp
  CFSG.RankThree.PartOne.KCUnitaryPlane

theorem two_le_of_three_dvd_two_pow_sub_one {f : ℕ} {K : Type} [Field K]
    (hK : UnitaryFieldData 2 f K) (h : 3 ∣ 2 ^ f - 1) : 2 ≤ f := by
  rcases Nat.lt_or_ge f 2 with hf | hf
  · interval_cases f
    · have h1 := hK.one_le
      omega
    · norm_num at h
  · exact hf

theorem not_three_dvd_two_pow_add_one {f : ℕ} (h : 3 ∣ 2 ^ f - 1) :
    ¬ 3 ∣ 2 ^ f + 1 := by
  intro h3
  have hsub := Nat.dvd_sub h3 h
  have h1 : 1 ≤ 2 ^ f := Nat.one_le_pow _ _ (by norm_num)
  have h2 : 3 ∣ 2 := by
    rwa [show 2 ^ f + 1 - (2 ^ f - 1) = 2 by omega] at hsub
  norm_num at h2

theorem finrank_rng_eq_two_of_three_dvd_sub_one {f n : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData 2 f K) {A : Subgroup ↥(unitarySU 2 f K n)}
    (hA : MaxElemAb 3 A) (hpq : 3 ∣ 2 ^ f - 1)
    (F : NsFrameComp.PieceFrame f n K h 3 A) (i : Fin F.r) :
    finrank K (rng (F.y i)) = 2 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP K 2 := h.charP
  have he : ordNegQ 2 f 3 = 2 :=
    CFSG.RankThree.PartOne.CTP.ordNegQ_eq_two_of_dvd_sub_one
      Nat.prime_two Nat.prime_three (by norm_num) hpq
  have hpow : (F.y i) ^ 3 = 1 := hA.pow _ (F.y_mem i)
  have hdvd : ordNegQ 2 f 3 ∣ finrank K (rng (F.y i)) :=
    OrdPNsU.ordNegQ_dvd_finrank_rng h hA.prime hA.ne_two hpow
  have hU0 : rng (F.y i) ≠ ⊥ := rng_ne_bot (F.y_ne_one i)
  have hUnd : NondegOn (stdHermForm h n) (rng (F.y i)) := nondegOn_rng hA (F.y_mem i)
  have hmin : ∀ W : Submodule K (Fin n → K), W ≤ rng (F.y i) → W ≠ ⊥ →
      NondegOn (stdHermForm h n) W → (∀ w ∈ W, lin (F.y i) w ∈ W) → W = rng (F.y i) := by
    intro W hWle hW0 hWnd hWy
    refine F.minimal i W hWle hW0 hWnd ?_
    intro a ha w hw
    obtain ⟨k, hk⟩ := F.cyc i a ha
    have hiter : ∀ k : ℕ, ∀ w ∈ W, lin (F.y i ^ k) w ∈ W := by
      intro k
      induction k with
      | zero => intro w hw; rw [pow_zero, lin_one, Module.End.one_apply]; exact hw
      | succ k ih =>
          intro w hw
          rw [pow_succ', lin_mul, Module.End.mul_apply]
          exact hWy _ (ih w hw)
    rw [hk w (hWle hw)]
    exact hiter k w hw
  have hle : finrank K (rng (F.y i)) ≤ ordNegQ 2 f 3 :=
    OrdPNsU.finrank_le_ordNegQ_of_minimal h hA.prime hA.ne_two hpow le_rfl hU0 hUnd
      (fun u hu => rng_inv (A := A) (y := F.y i) (a := F.y i) hA (F.y_mem i) (F.y_mem i) u hu)
      hmin
  have hpos : 0 < finrank K (rng (F.y i)) := by
    rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact hU0
  have hdvd2 : 2 ∣ finrank K (rng (F.y i)) := by simpa [he] using hdvd
  have hge : 2 ≤ finrank K (rng (F.y i)) := Nat.le_of_dvd hpos hdvd2
  omega

theorem exists_two_plane_pieces_of_card_nine {f n : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData 2 f K) {A : Subgroup ↥(unitarySU 2 f K n)}
    (hA : MaxElemAb 3 A) (hpq : 3 ∣ 2 ^ f - 1) (h9 : 9 ≤ Nat.card A) :
    ∃ (r : ℕ) (F : NsFrameComp.PieceFrame f n K h 3 A),
      F.r = r ∧ 2 ≤ r ∧ (∀ i, finrank K (rng (F.y i)) = 2) ∧
      (∀ i j, i ≠ j → ∀ u ∈ rng (F.y i), ∀ v ∈ rng (F.y j),
        stdHermForm h n u v = 0) := by
  classical
  obtain ⟨F⟩ := NsFrameComp.exists_pieceFrame' (h := h) (A := A) hA
  have hcard : Nat.card A = 3 ^ F.r := by
    have h1 : Nat.card A = Nat.card F.ι.range := by rw [F.ι_range]
    have h2 : Nat.card F.ι.range = Nat.card (Multiplicative (Fin F.r → ZMod 3)) :=
      (Nat.card_congr (MonoidHom.ofInjective F.ι_injective).toEquiv).symm
    rw [h1, h2]
    simp
  have h9' : 3 ^ 2 ≤ 3 ^ F.r := by simpa [hcard] using h9
  have hr : 2 ≤ F.r := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h9'
  exact ⟨F.r, F, rfl, hr,
    fun i => finrank_rng_eq_two_of_three_dvd_sub_one h hA hpq F i,
    fun i j hij => F.orth i j hij⟩

theorem exists_maxElemAb_of_normalizedFamily {G : Type} [Group G] [Finite G]
    {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : UnitaryFieldData 2 f K)
    {Bs J : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (φ : ↥(unitarySU 2 f K n) →* ↥J) (hφ : Function.Surjective φ)
    (U : ↥Bs → ↥(unitarySU 2 f K n))
    (hpow : ∀ b, U b ^ 3 = 1)
    (hcomm : ∀ b c, U b * U c = U c * U b)
    (hact : ∀ (b : ↥Bs) (g : ↥(unitarySU 2 f K n)),
      (b : G) * ((φ g : ↥J) : G) * (b : G)⁻¹ =
        ((φ (U b * g * (U b)⁻¹) : ↥J) : G))
    (hpq : 3 ∣ 2 ^ f - 1)
    (hA9 : 9 ≤ Nat.card (ggGamma J hN).range) :
    ∃ P : Subgroup ↥(unitarySU 2 f K n), MaxElemAb 3 P ∧ (∀ b, U b ∈ P) ∧
      9 ≤ Nat.card P := by
  classical
  obtain ⟨P, hPmax, hUP⟩ :=
    OrdPNsU.exists_maxElemAb_containing (f := f) (n := n) (K := K)
      (p := 3) hK Nat.prime_three (by norm_num)
      (not_three_dvd_two_pow_add_one hpq) U hpow hcomm
  let Q : Subgroup ↥(unitarySU 2 f K n) := Subgroup.closure (Set.range U)
  have hQ_le_P : Q ≤ P := by
    rw [Subgroup.closure_le]
    rintro _ ⟨b, rfl⟩
    exact hUP b
  have hmap_le : Q.map (MulAut.conj.comp φ) ≤ (ggGamma J hN).range := by
    rw [Subgroup.map_le_iff_le_comap]
    rw [Subgroup.closure_le]
    rintro _ ⟨b, rfl⟩
    refine ⟨b, ?_⟩
    ext g
    obtain ⟨x, rfl⟩ := hφ g
    change (b : G) * ((φ x : ↥J) : G) * (b : G)⁻¹ =
      ((MulAut.conj (φ (U b)) (φ x) : ↥J) : G)
    rw [MulAut.conj_apply]
    simpa only [map_mul, map_inv] using hact b x
  have hA_le_map : (ggGamma J hN).range ≤ Q.map (MulAut.conj.comp φ) := by
    rintro _ ⟨b, rfl⟩
    refine ⟨U b, Subgroup.subset_closure ⟨b, rfl⟩, ?_⟩
    ext g
    obtain ⟨x, rfl⟩ := hφ g
    change ((MulAut.conj (φ (U b)) (φ x) : ↥J) : G) =
      (b : G) * ((φ x : ↥J) : G) * (b : G)⁻¹
    rw [MulAut.conj_apply]
    simpa only [map_mul, map_inv] using (hact b x).symm
  have hmap_eq : Q.map (MulAut.conj.comp φ) = (ggGamma J hN).range :=
    le_antisymm hmap_le hA_le_map
  have hsurj : Function.Surjective (fun q : Q =>
      (⟨MulAut.conj (φ (q : ↥(unitarySU 2 f K n))), by
        have hmem : MulAut.conj (φ (q : ↥(unitarySU 2 f K n))) ∈
            Q.map (MulAut.conj.comp φ) := ⟨q, q.2, rfl⟩
        rwa [hmap_eq] at hmem⟩ : (ggGamma J hN).range)) := by
    intro a
    have ha : (a : MulAut ↥J) ∈ Q.map (MulAut.conj.comp φ) := by
      rw [hmap_eq]
      exact a.2
    obtain ⟨q, hq, hqeq⟩ := Subgroup.mem_map.mp ha
    exact ⟨⟨q, hq⟩, Subtype.ext hqeq⟩
  have hcard : Nat.card (ggGamma J hN).range ≤ Nat.card Q :=
    Nat.card_le_card_of_surjective _ hsurj
  exact ⟨P, hPmax, hUP, le_trans hA9 (le_trans hcard (Subgroup.card_le_of_le hQ_le_P))⟩

theorem exists_maxElemAb_of_actualActors {G : Type} [Group G] [Finite G]
    {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : UnitaryFieldData 2 f K)
    {Bs J : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (φ : ↥(unitarySU 2 f K n) →* ↥J) (hφ : Function.Surjective φ)
    (hPerf : Group.IsPerfect ↥(unitarySU 2 f K n))
    (hBs : CFSG.Open.IsElemAbelian 3 Bs)
    (hker : ∀ g : ↥(unitarySU 2 f K n), φ g = 1 →
      ∃ a : K, (((g : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) = a • 1)
    (Y : ↥Bs → GL (Fin n) K)
    (hYiso : ∀ b, ∀ x y, stdHermForm hK n (((Y b : Matrix (Fin n) (Fin n) K)) *ᵥ x)
      ((Y b : Matrix (Fin n) (Fin n) K) *ᵥ y) = stdHermForm hK n x y)
    (hYact : ∀ (b : ↥Bs) (g : ↥(unitarySU 2 f K n)),
      (b : G) * ((φ g : ↥J) : G) * (b : G)⁻¹ =
        ((φ (CFSG.StandardType.ResJUnitaryActor.conjSU hK (Y b) (hYiso b) g) : ↥J) : G))
    (hpq : 3 ∣ 2 ^ f - 1)
    (hA9 : 9 ≤ Nat.card (ggGamma J hN).range)
    (hSC : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)
    (hn3 : 3 ≤ n) :
    ∃ P : Subgroup ↥(unitarySU 2 f K n), MaxElemAb 3 P ∧
      9 ≤ Nat.card P ∧ (∀ p ∈ P, ((φ p : ↥J) : G) ∈ Bs) ∧
        (∀ p ∈ P, φ p = 1 → p = 1) := by
  classical
  have hn : 1 ≤ n := by omega
  have hpq' : ¬ 3 ∣ 2 ^ f + 1 := not_three_dvd_two_pow_add_one hpq
  obtain ⟨U, hpow, hcomm, hactU⟩ :=
    CFSG.StandardType.ResJUnitaryActor.exists_normalizedFamily_of_commuting_actors
      (f := f) (n := n) (K := K) hK hPerf hBs φ hker Y hYiso hYact hpq' hn hn3
  obtain ⟨P, hPmax, hUP, hcard⟩ :=
    exists_maxElemAb_of_normalizedFamily (G := G) (f := f) (n := n) (K := K)
      hK hN φ hφ U hpow hcomm hactU hpq hA9
  refine ⟨P, hPmax, hcard, ?_, ?_⟩
  · intro p hp
    apply hSC ((φ p : ↥J) : G)
    · rw [Subgroup.mem_centralizer_iff]
      intro b hb
      let bs : ↥Bs := ⟨b, hb⟩
      have hpcomm : p * U bs = U bs * p := hPmax.comm p hp (U bs) (hUP bs)
      have h := hactU bs p
      have hconj : U bs * p * (U bs)⁻¹ = p := by
        rw [← hpcomm]; group
      rw [hconj] at h
      calc (b : G) * ((φ p : ↥J) : G)
          = ((b : G) * ((φ p : ↥J) : G) * (b : G)⁻¹) * (b : G) := by group
        _ = ((φ p : ↥J) : G) * (b : G) := by rw [h]
    · have hpowJ : (φ p : ↥J) ^ 3 = 1 := by
        rw [← map_pow, hPmax.pow p hp, map_one]
      simpa using congrArg (fun z : ↥J => (z : G)) hpowJ
  · intro p hp hφp
    obtain ⟨a, ha⟩ := hker p hφp
    exact CFSG.StandardType.ResJUnitaryActor.eq_one_of_scalar_cube_of_mem_unitarySU
      hK hpq' hn (hPmax.pow p hp) ⟨a, ha⟩

theorem exists_two_plane_pieces_of_actualActors {G : Type} [Group G] [Finite G]
    {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : UnitaryFieldData 2 f K)
    {Bs J : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (φ : ↥(unitarySU 2 f K n) →* ↥J) (hφ : Function.Surjective φ)
    (hPerf : Group.IsPerfect ↥(unitarySU 2 f K n))
    (hBs : CFSG.Open.IsElemAbelian 3 Bs)
    (hker : ∀ g : ↥(unitarySU 2 f K n), φ g = 1 →
      ∃ a : K, (((g : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) = a • 1)
    (Y : ↥Bs → GL (Fin n) K)
    (hYiso : ∀ b, ∀ x y, stdHermForm hK n (((Y b : Matrix (Fin n) (Fin n) K)) *ᵥ x)
      ((Y b : Matrix (Fin n) (Fin n) K) *ᵥ y) = stdHermForm hK n x y)
    (hYact : ∀ (b : ↥Bs) (g : ↥(unitarySU 2 f K n)),
      (b : G) * ((φ g : ↥J) : G) * (b : G)⁻¹ =
        ((φ (CFSG.StandardType.ResJUnitaryActor.conjSU hK (Y b) (hYiso b) g) : ↥J) : G))
    (hpq : 3 ∣ 2 ^ f - 1)
    (hA9 : 9 ≤ Nat.card (ggGamma J hN).range)
    (hSC : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)
    (hn3 : 3 ≤ n) :
    ∃ P : Subgroup ↥(unitarySU 2 f K n), MaxElemAb 3 P ∧
      9 ≤ Nat.card P ∧ (∀ p ∈ P, ((φ p : ↥J) : G) ∈ Bs) ∧
        (∀ p ∈ P, φ p = 1 → p = 1) ∧
        ∃ (r : ℕ) (F : NsFrameComp.PieceFrame f n K hK 3 P),
          F.r = r ∧ 2 ≤ r ∧ (∀ i, finrank K (rng (F.y i)) = 2) ∧
          (∀ i j, i ≠ j → ∀ u ∈ rng (F.y i), ∀ v ∈ rng (F.y j),
            stdHermForm hK n u v = 0) := by
  obtain ⟨P, hPmax, hPcard, hPBs, hPinj⟩ :=
    exists_maxElemAb_of_actualActors (G := G) (f := f) (n := n) (K := K)
      hK hN φ hφ hPerf hBs hker Y hYiso hYact hpq hA9 hSC hn3
  obtain ⟨r, F, hFr, hr, hplane, horth⟩ :=
    exists_two_plane_pieces_of_card_nine (h := hK) (A := P) hPmax hpq hPcard
  exact ⟨P, hPmax, hPcard, hPBs, hPinj, r, F, hFr, hr, hplane, horth⟩

end ResJUnitaryPaired

section A3OppositeRecognition



open CFSG.Open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LinearGroups
open Matrix Module Multiplicative
open CFSG.StandardType.ResJUnitaryActor CFSG.StandardType.ResJUnitaryPaired CFSG.LieType.SemisimpleCentralizers.Held
open scoped BigOperators Matrix

private theorem prod_sgnAut_list_apply {p r : ℕ} (L : List (Fin r)) (hL : L.Nodup)
    (f : Fin r → Multiplicative (ZMod p)) (j : Fin r) :
    ((L.map fun i => SpCoord.sgnAut (p := p) i).prod f) j =
      if j ∈ L then (f j)⁻¹ else f j := by
  induction L with
  | nil => simp
  | cons a l ih =>
      rw [List.nodup_cons] at hL
      obtain ⟨ha, hl⟩ := hL
      rw [List.map_cons, List.prod_cons, MulAut.mul_apply, SpCoord.sgnAut_apply]
      by_cases hja : j = a
      · subst hja
        rw [Function.update_self, ih hl]
        simp [ha]
      · rw [Function.update_of_ne hja, ih hl]
        simp [hja, ha]

private theorem conj_list_prod_sgnAut {G : Type} [Group G] {p r : ℕ}
    (τ : (Fin r → Multiplicative (ZMod p)) →* G) (w : Fin r → G)
    (hw : ∀ i f, w i * τ f * (w i)⁻¹ = τ (SpCoord.sgnAut (p := p) i f))
    (L : List (Fin r)) (f : Fin r → Multiplicative (ZMod p)) :
    (L.map w).prod * τ f * (L.map w).prod⁻¹ =
      τ ((L.map fun i => SpCoord.sgnAut (p := p) i).prod f) := by
  induction L with
  | nil => simp
  | cons a l ih =>
      rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons]
      calc (w a * (l.map w).prod) * τ f * (w a * (l.map w).prod)⁻¹
          = w a * ((l.map w).prod * τ f * (l.map w).prod⁻¹) * (w a)⁻¹ := by group
        _ = w a * τ ((l.map fun i => SpCoord.sgnAut (p := p) i).prod f) * (w a)⁻¹ := by
            rw [ih]
        _ = τ (SpCoord.sgnAut (p := p) a
              ((l.map fun i => SpCoord.sgnAut (p := p) i).prod f)) := hw a _
        _ = τ ((SpCoord.sgnAut (p := p) a *
              (l.map fun i => SpCoord.sgnAut (p := p) i).prod) f) := by
            rw [MulAut.mul_apply]
        _ = τ (((a :: l).map fun i => SpCoord.sgnAut (p := p) i).prod f) := by
            rw [List.map_cons, List.prod_cons]

private theorem inversion_of_signed_frame {G : Type} [Group G] {p r : ℕ} (hp : p.Prime)
    (E : Subgroup G) {k : ℕ} (τ : (Fin k → Multiplicative (ZMod p)) →* G)
    (hτinj : Function.Injective τ) (hτrange : τ.range = E)
    (hcard : Nat.card E = p ^ r)
    (hsign : ∀ i : Fin k, ∃ w : G, ∀ f,
      w * τ f * w⁻¹ = τ (SpCoord.sgnAut (p := p) i f)) :
    ∃ s : G, ∀ x ∈ E, s * x * s⁻¹ = x⁻¹ := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hk : k = r := by
    have hcardM : Nat.card (Multiplicative (ZMod p)) = p := by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    have h1 : Nat.card (Fin k → Multiplicative (ZMod p)) = p ^ k := by
      rw [Nat.card_pi]
      simp [hcardM]
    have hcard_k : Nat.card E = p ^ k := by
      rw [← hτrange]
      exact (Nat.card_congr (MonoidHom.ofInjective hτinj).toEquiv).symm.trans h1
    have hpk : p ^ k = p ^ r := by rw [← hcard_k, hcard]
    exact Nat.pow_right_injective hp.two_le hpk
  subst k
  choose w hw' using hsign
  let L : List (Fin r) := List.finRange r
  have hLnodup : L.Nodup := List.nodup_finRange r
  have hLmem : ∀ j : Fin r, j ∈ L := fun j => List.mem_finRange j
  refine ⟨(L.map w).prod, ?_⟩
  intro x hx
  rw [← hτrange] at hx
  obtain ⟨f, rfl⟩ := hx
  have hprod : ((L.map fun i => SpCoord.sgnAut (p := p) i).prod f) = f⁻¹ := by
    funext j
    rw [prod_sgnAut_list_apply L hLnodup f j, if_pos (hLmem j)]
    rfl
  rw [conj_list_prod_sgnAut τ w (fun i f => hw' i f) L f, hprod, map_inv]

private theorem inversion_hypSU_even {f r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (hpq : 3 ∣ 2 ^ f - 1) (hr : 1 ≤ r)
    (E : Subgroup (hypSU h r 0)) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ r) :
    ∃ s : hypSU h r 0, ∀ x ∈ E, s * x * s⁻¹ = x⁻¹ := by
  classical
  obtain ⟨k, τ, hτinj, hτrange, hsign, -, -⟩ :=
    ggKGUs_signed_frame_hypSU h Nat.prime_three (by norm_num) hpq hr E hE (le_of_eq hcard.symm)
  exact inversion_of_signed_frame Nat.prime_three E τ hτinj hτrange hcard (fun i => hsign i)

private theorem inversion_hypSU_odd {f r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (hpq : 3 ∣ 2 ^ f - 1) (hr : 1 ≤ r)
    (E : Subgroup (hypSU h r 1)) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ r) :
    ∃ s : hypSU h r 1, ∀ x ∈ E, s * x * s⁻¹ = x⁻¹ := by
  classical
  obtain ⟨k, τ, hτinj, hτrange, hsign, -, -⟩ :=
    ggKGUs_signed_frame_hypSU_odd h Nat.prime_three (by norm_num) hpq hr E hE
      (le_of_eq hcard.symm)
  exact inversion_of_signed_frame Nat.prime_three E τ hτinj hτrange hcard (fun i => hsign i)

private theorem inversion_hypSU_any {f r ε : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (hpq : 3 ∣ 2 ^ f - 1) (hr : 1 ≤ r) (hε : ε ≤ 1)
    (E : Subgroup (hypSU h r ε)) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ r) :
    ∃ s : hypSU h r ε, ∀ x ∈ E, s * x * s⁻¹ = x⁻¹ := by
  cases ε with
  | zero => exact inversion_hypSU_even h hpq hr E hE hcard
  | succ ε' =>
      have hε' : ε' = 0 := by omega
      subst ε'
      exact inversion_hypSU_odd h hpq hr E hE hcard

private structure OppositeUnitarySetup
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {Ksub : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y Ksub)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n - 1) 3 Bs J)
    (F : Type) [Field F] [Finite F]
    (n d r ε : ℕ) (lab : LargeEvenLabel) where
  [instCharP : CharP F 2]
  hΛ : LargeEvenInLambda2 lab
  htag : lab.tag = .twA
  h3n : 3 ∣ 2 ^ lab.n - 1
  hd : d = lab.rank + 1
  hdr : d = 2 * r + ε
  hε : ε ≤ 1
  hr1 : 1 ≤ r
  hr2 : 2 ≤ r
  hn1 : 1 ≤ n
  hd3 : 3 ≤ d
  hFcard : Nat.card F = (2 ^ n) ^ 2
  hpqF : 3 ∣ 2 ^ n - 1
  hU : UnitaryFieldData 2 n F
  θ : (↥J ⧸ Subgroup.center ↥J) ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n))
  φ : unitarySU 2 n F d →* ↥J
  hφsurj : Function.Surjective φ
  hφker : ∀ g : unitarySU 2 n F d, φ g = 1 →
    ∃ c : Fˣ, (g : GL (Fin d) F) = GeneralLinearGroup.scalar (Fin d) c
  U : ↥Bs → unitarySU 2 n F d
  hpow : ∀ b, U b ^ 3 = 1
  hactU : ∀ (b : ↥Bs) (g : ↥(unitarySU 2 n F d)),
      (b : G) * ((φ g : ↥J) : G) * (b : G)⁻¹ = ((φ (U b * g * (U b)⁻¹) : ↥J) : G)
  P : Subgroup (unitarySU 2 n F d)
  hPmax : CFSG.StandardType.SUTB.MaxElemAb 3 P
  hUP : ∀ b, U b ∈ P
  hPele : IsElemAbelian 3 P
  hPcard : Nat.card P = 3 ^ r
  A0 : Subgroup (MulAut ↥J)
  hA0 : A0 = (ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range
  hA0card : Nat.card A0 = 3 ^ r
  hSignedSC : 3 ≤ r →
    GGTorusSignedEltSC 3 (LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n)))
  hW : 3 ≤ r → ∀ w : ↥J,
      MulAut.conj w ∈ Subgroup.normalizer (A0 : Set (MulAut ↥J)) →
        GGTorusWeylElt 3 A0 w
  hcard : 3 ≤ r → Nat.card (ggAutomizer J Bs) = 2 ^ r * r.factorial
  hHas : GGHasLabel lab (↥J ⧸ Subgroup.center ↥J)

private theorem GGResHyp.exists_opposite_unitary_setup
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {Ksub : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y Ksub)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n - 1) 3 Bs J) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (n d r ε : ℕ) (lab : LargeEvenLabel),
      Nonempty (OppositeUnitarySetup hH hMark F n d r ε lab) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBs : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hH.1.2.1.2.2.2
  obtain ⟨hperfJ, lab, hΛ, hraw⟩ := hMark
  have h2rk : 2 ≤ lab.rank := by
    obtain ⟨R0, _, I0, F0, hQ0⟩ := CFSG.GGQ2Prime.rawDatumLegacy_exists hraw
    obtain ⟨_hs0, _hna0, _θ0, hP0⟩ := hQ0
    obtain ⟨hS0, _, _⟩ := hP0
    have h := hΛ
    simp only [LargeEvenInLambda2, hS0.1] at h
    exact h.2.1
  let Sgood : ℕ → LargeEvenLabel → Prop :=
    fun _ lab' => lab' = lab ∧ lab'.tag = .twA ∧ 3 ∣ 2 ^ lab'.n - 1
  have hSgood : ∀ lab' : LargeEvenLabel, Sgood 3 lab' →
      lab'.tag = .twA ∧ 3 ≤ lab'.rank + 1 ∧ lab'.n ≠ 1 := by
    intro lab' h
    refine ⟨h.2.1, ?_, ?_⟩
    · rw [h.1]; omega
    · intro hn
      have hdiv : 3 ∣ 2 ^ 1 - 1 := by simpa [hn] using h.2.2
      norm_num at hdiv
  have hMarkGood : GGInnerDiagOnLabel Sgood 3 Bs J := by
    refine ⟨hperfJ, lab, hΛ, ?_⟩
    refine largeEvenRawDatum_mono (lab := lab) ?_ hraw
    rintro R _ I F ⟨hs, hna, θ, hP⟩
    exact ⟨hs, hna, θ, ⟨rfl, hP.1.1, hP.1.2⟩, hP.2.1, hP.2.2⟩
  obtain ⟨F, hF, hFfin, d, f, lab', hSlab', htag', hd, hf, hlab', hf2, hd3, hFcard,
    θ, φ, hU, A, ρ, hN, hAGU, hAiso, hφsurj, hφker, hφquot, hAprime, hAproj, hYact, hAρ⟩ :=
    CFSG.StandardType.GGInnerDiagOnLabel.exists_general_unitary_cover_actors
      hMarkGood hSgood
  letI : Field F := hF
  letI : Finite F := hFfin
  haveI : CharP F 2 := hU.charP
  have hpqF : 3 ∣ 2 ^ f - 1 := by simpa [hf] using hSlab'.2.2
  have hf1 : 1 ≤ f := by omega
  let r : ℕ := d / 2
  let ε : ℕ := d % 2
  have hdr : d = 2 * r + ε := by
    dsimp [r, ε]
    exact (Nat.div_add_mod d 2).symm
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    have := Nat.mod_lt d (by norm_num : 0 < 2)
    omega
  have hr1 : 1 ≤ r := by
    dsimp [r]
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    omega
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hnq : (d, 2 ^ f) ≠ (3, 2) := by
    intro h
    have h2 : 2 ^ f = 2 := congrArg Prod.snd h
    omega
  have hT : GGTorusLift 3 r (LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ f))) := by
    by_cases hε0 : ε = 0
    · have hd2r : d = 2 * r := by omega
      have hr2' : 2 ≤ r := by
        by_contra h
        have hrle : r ≤ 1 := by omega
        have hd4 := hd3
        omega
      rw [hd2r]
      exact ggTorusLift_unitaryHypEven (K := F) (n := f) (p := 3) (r := r)
        hFcard hf1 (by norm_num) (by norm_num) hpqF hr2'
    · have hε1' : ε = 1 := by omega
      have hd2r1 : d = 2 * r + 1 := by omega
      rw [hd2r1]
      exact ggTorusLift_unitarySplit_odd (K := F) (n := f) (r := r) (p := 3)
        hFcard hf1 hr1 (by norm_num) (by norm_num) hpqF
  let φU : unitarySU 2 f F d →* ↥J := φ
  have hφUsurj : Function.Surjective φU := hφsurj
  have hφUker : ∀ g : unitarySU 2 f F d, φU g = 1 →
      ∃ a : F, (((g : GL (Fin d) F)) : Matrix (Fin d) (Fin d) F) = a • 1 := by
    intro g hg
    obtain ⟨c, hc⟩ := hφker g hg
    refine ⟨(c : F), ?_⟩
    rw [hc, Matrix.GeneralLinearGroup.coe_scalar]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.diagonal_apply, hij]
  have hPerf : Group.IsPerfect ↥(unitarySU 2 f F d) := by
    simpa [unitarySU] using
      CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (p := 2) (f := f) hFcard hd3 hnq
  obtain ⟨U, hpow, hcomm, hactU⟩ :=
    CFSG.StandardType.ResJUnitaryActor.exists_normalizedFamily_of_commuting_actors
      (f := f) (n := d) (K := F) hU hPerf hBs φU hφUker A hAiso hYact
      (not_three_dvd_two_pow_add_one hpqF) (by omega) hd3
  let hN0 : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  have hA9 : 9 ≤ Nat.card (ggGamma J hN0).range := by
    simpa using GGResHyp.sq_le_card_gamma_J (p := 3) hH
  obtain ⟨P, hPmax, hUP, _hP9⟩ :=
    CFSG.StandardType.ResJUnitaryPaired.exists_maxElemAb_of_normalizedFamily
      (G := G) (f := f) (n := d) (K := F) hU hN0 φU hφUsurj U hpow hcomm hactU hpqF hA9
  let A0 : Subgroup (MulAut ↥J) := (ggGamma J hN0).range
  let Q : Subgroup ↥(unitarySU 2 f F d) := Subgroup.closure (Set.range U)
  have hQ_le_P : Q ≤ P := by
    rw [Subgroup.closure_le]
    rintro _ ⟨b, rfl⟩
    exact hUP b
  have hQele : IsElemAbelian 3 Q := by
    refine CFSG.Open.IsElemAbelian.closure_of_commute (p := 3) ?_ ?_
    · rintro _ ⟨b, rfl⟩ _ ⟨c, rfl⟩
      exact hcomm b c
    · rintro _ ⟨b, rfl⟩
      exact hpow b
  have hmap_le : Q.map (MulAut.conj.comp φU) ≤ A0 := by
    rw [Subgroup.map_le_iff_le_comap]
    rw [Subgroup.closure_le]
    rintro _ ⟨b, rfl⟩
    refine ⟨b, ?_⟩
    ext g
    obtain ⟨x, rfl⟩ := hφUsurj g
    change (b : G) * ((φU x : ↥J) : G) * (b : G)⁻¹ =
      ((MulAut.conj (φU (U b)) (φU x) : ↥J) : G)
    rw [MulAut.conj_apply]
    simpa only [map_mul, map_inv] using hactU b x
  have hA_le_map : A0 ≤ Q.map (MulAut.conj.comp φU) := by
    rintro _ ⟨b, rfl⟩
    refine ⟨U b, Subgroup.subset_closure ⟨b, rfl⟩, ?_⟩
    ext g
    obtain ⟨x, rfl⟩ := hφUsurj g
    change ((MulAut.conj (φU (U b)) (φU x) : ↥J) : G) =
      (b : G) * ((φU x : ↥J) : G) * (b : G)⁻¹
    rw [MulAut.conj_apply]
    simpa only [map_mul, map_inv] using (hactU b x).symm
  have hmap_eq : Q.map (MulAut.conj.comp φU) = A0 := le_antisymm hmap_le hA_le_map
  have hsurjA : Function.Surjective (fun q : Q =>
      (⟨MulAut.conj (φU (q : unitarySU 2 f F d)), by
        have hmem : MulAut.conj (φU (q : unitarySU 2 f F d)) ∈
            Q.map (MulAut.conj.comp φU) := ⟨q, q.2, rfl⟩
        rwa [hmap_eq] at hmem⟩ : A0)) := by
    intro a
    have ha : (a : MulAut ↥J) ∈ Q.map (MulAut.conj.comp φU) := by
      rw [hmap_eq]
      exact a.2
    obtain ⟨q, hq, hqeq⟩ := Subgroup.mem_map.mp ha
    exact ⟨⟨q, hq⟩, Subtype.ext hqeq⟩
  have hA_le_Q : Nat.card A0 ≤ Nat.card Q := Nat.card_le_card_of_surjective _ hsurjA
  have hnotdvd : ¬ 3 ∣ 2 ^ f := by
    intro h3
    have h1 : 3 ∣ 2 ^ f - 1 := hpqF
    have hd := Nat.dvd_sub h3 h1
    have hle : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have hsub : 2 ^ f - (2 ^ f - 1) = 1 := by omega
    have h2 : 3 ∣ 1 := by rwa [hsub] at hd
    omega
  have hmod : (2 ^ f) % 3 = 1 := by
    obtain ⟨k, hk⟩ := hpqF
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have hq : 2 ^ f = 3 * k + 1 := by omega
    rw [hq, Nat.add_comm (3 * k) 1, Nat.add_mul_mod_self_left]
  have hord := CFSG.GroupTheory.WeirSylow.orderOf_neg_natCast_zmod_three_of_mod_eq_one hmod
  have htop_le_r : CFSG.Open.pRank 3 (⊤ : Subgroup (unitarySU 2 f F d)) ≤ r := by
    have hbound := CFSG.GroupTheory.WeirSylow.pRank_top_statedSU_le (p := 3) (L := F)
      (q := 2 ^ f) (n := d) (by norm_num) hFcard hnotdvd (by omega)
    rw [hord] at hbound
    simpa [r, unitarySU] using hbound
  have hQrank_le : CFSG.Open.pRank 3 Q ≤ r :=
    (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) (le_top : Q ≤ ⊤)).trans htop_le_r
  have hQcard_le : Nat.card Q ≤ 3 ^ r := by
    rw [CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_three hQele]
    exact Nat.pow_le_pow_right (by norm_num) hQrank_le
  have hA_lower : 3 ^ r ≤ Nat.card A0 := by
    dsimp [A0]
    simpa using GGResHyp.pow_le_card_range_gamma_J_of_torusLift hH θ hT
  have hA0card : Nat.card A0 = 3 ^ r := le_antisymm (hA_le_Q.trans hQcard_le) hA_lower
  have hA9 : 9 ≤ Nat.card A0 := by
    dsimp [A0]
    simpa using GGResHyp.sq_le_card_gamma_J (p := 3) hH
  have hA_lower_P : 3 ^ r ≤ Nat.card P :=
    le_trans hA_lower (le_trans hA_le_Q (Subgroup.card_le_of_le hQ_le_P))
  have hPele : IsElemAbelian 3 P := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · exact Subtype.ext (hPmax.comm a a.2 b b.2)
    · intro a ha
      exact hPmax.pow a ha
  have hPlog : Nat.card P = 3 ^ CFSG.Open.pRank 3 P :=
    CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_three hPele
  have hPrank_le_top : CFSG.Open.pRank 3 P ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup (unitarySU 2 f F d)) :=
    CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) le_top
  have hPcard_le : Nat.card P ≤ 3 ^ r := by
    rw [hPlog]
    exact Nat.pow_le_pow_right (by norm_num) (hPrank_le_top.trans htop_le_r)
  have hPcard : Nat.card P = 3 ^ r := le_antisymm hPcard_le hA_lower_P
  have hr2 : 2 ≤ r := by
    have h9 : 9 ≤ 3 ^ r := by rw [← hA0card]; exact hA9
    by_contra h
    have hrle : r ≤ 1 := by omega
    have hle : 3 ^ r ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hrle
    norm_num at h9 hle
    omega
  have hd2r : d = 2 * r ∨ d = 2 * r + 1 := by
    rcases (by omega : ε = 0 ∨ ε = 1) with h0 | h1
    · left; omega
    · right; omega
  have hSignedSCfun : 3 ≤ r →
      GGTorusSignedEltSC 3 (LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ f))) := by
    intro hr3
    have hd2r : 2 * r ≤ d ∧ d ≤ 2 * r + 1 := by omega
    exact ggTwSU_signed_rec (K := F) (n := f) (d := d) (r := r)
      hFcard hf1 hr3 hd2r hpqF
  have hframe : 3 ≤ r →
      (∀ w : ↥J, MulAut.conj w ∈ Subgroup.normalizer (A0 : Set (MulAut ↥J)) →
        GGTorusWeylElt 3 A0 w) ∧
      Nat.card (ggAutomizer J Bs) = 2 ^ r * r.factorial := by
    intro hr3
    let R : Type := LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ f))
    let I : Set (MulAut R) := Set.range (MulAut.conj : R →* MulAut R)
    have hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R) := subset_rfl
    have hd2r : 2 * r ≤ d ∧ d ≤ 2 * r + 1 := by omega
    obtain ⟨hZ, _, hcp⟩ := ggTwSU_facts_rec (K := F) (n := f) (d := d) (r := r)
      hFcard hf1 hr3 hd2r hpqF
    have hSignedSC : GGTorusSignedEltSC 3 R := hSignedSCfun hr3
    have hA : IsElemAbelian 3 A0 := by
      dsimp [A0]
      exact isElemAbelian_range
        (fun a b : ↥Bs => (@IsMulCommutative.is_comm ↥Bs _ hH.1.2.1.2.1.1).comm a b)
        (fun b : ↥Bs => Subtype.ext (by simpa using hH.1.2.1.2.1.2 b b.2))
        (ggGamma J hN0)
    have hAI : ∀ a ∈ A0, ∃ ψ ∈ I, ∀ l : ↥J, ψ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
      rintro a ⟨b, rfl⟩
      refine ⟨MulAut.conj (ggQuotHom θ (φU (U b))),
        ⟨ggQuotHom θ (φU (U b)), rfl⟩, fun l => ?_⟩
      obtain ⟨g, rfl⟩ := hφUsurj l
      have hb : ((ggGamma J hN0 b) (φU g)) =
          φU (U b) * φU g * (φU (U b))⁻¹ := by
        apply Subtype.ext
        change (b : G) * ((φU g : ↥J) : G) * (b : G)⁻¹ =
          ((φU (U b) * φU g * (φU (U b))⁻¹ : ↥J) : G)
        calc (b : G) * ((φU g : ↥J) : G) * (b : G)⁻¹
            = ((φU (U b * g * (U b)⁻¹) : ↥J) : G) := hactU b g
          _ = ((φU (U b) * φU g * (φU (U b))⁻¹ : ↥J) : G) := by simp
      rw [hb, MulAut.conj_apply]
      simp only [map_mul, map_inv]
    have h3A : 3 ^ 3 ≤ Nat.card A0 := by
      rw [hA0card]
      exact Nat.pow_le_pow_right (by norm_num) hr3
    have hsc : GGTorusSelfCent 3 A0 := GGResHyp.gamma_J_selfCent hH
    obtain ⟨k, Θ, _hk3, hW, hsgn, hperm, hsp⟩ :=
      exists_signedModelSC (p := 3) (R := R) (I := I)
        Nat.prime_three (by norm_num) hI hZ hcp hSignedSC
        (L' := ↥J) (ψ := ggQuotHom θ) (ggQuotHom_surjective θ)
        (by rw [ker_ggQuotHom]) hperfJ hA hAI h3A hsc
    have hcardModel : Nat.card (ggAutomizer (MulAut.conj : ↥J →* MulAut ↥J).range A0) =
        2 ^ k * k.factorial :=
      CFSG.StandardType.SignedPermCount.ggAutomizer_card_eq_signed_of_model
        (p := 3) (k := k) Nat.prime_three (by norm_num) (A := A0) Θ hsp hsgn hperm
    have hWeyl : ∀ n : ↥J,
        MulAut.conj n ∈ Subgroup.normalizer (A0 : Set (MulAut ↥J)) →
          GGTorusWeylElt 3 A0 n := hW
    have hsurjGamma : Function.Surjective (ggAutomizerGammaHom hN0) :=
      ggAutomizerGammaHom_surjective_of_weyl_normalizers (p := 3) hN0 hSC hWeyl
    have hinjGamma : Function.Injective (ggAutomizerGammaHom hN0) :=
      ggAutomizerGammaHom_injective (p := 3) Nat.prime_three hBs hH.2.2.2.1 hN0
        (GGResHyp.card_bstar_inf_center_J_le hH)
    have hcardOrig : Nat.card (ggAutomizer J Bs) =
        Nat.card (ggAutomizer (MulAut.conj : ↥J →* MulAut ↥J).range A0) :=
      Nat.card_congr (Equiv.ofBijective (ggAutomizerGammaHom hN0) ⟨hinjGamma, hsurjGamma⟩)
    have hcV : Nat.card (Fin k → Multiplicative (ZMod 3)) = 3 ^ k := by
      rw [Nat.card_pi]
      simp [Nat.card_fin, Nat.card_zmod]
    have hcardA_k : Nat.card A0 = 3 ^ k := by
      rw [← Nat.card_congr Θ.toEquiv]
      exact hcV
    have hkr : k = r := by
      have hpow : 3 ^ k = 3 ^ r := by rw [← hcardA_k, hA0card]
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) hpow
    refine ⟨hWeyl, ?_⟩
    rw [hcardOrig, hcardModel, hkr]
  have hlab'_eq : lab' = lab := hSlab'.1
  have hHas : GGHasLabel lab' (J ⧸ Subgroup.center J) := by
    rw [hlab'_eq]
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨hs, hna, θ, -⟩
    exact ⟨θ⟩
  refine ⟨F, hF, hFfin, f, d, r, ε, lab', ?_⟩
  exact ⟨
    { instCharP := hU.charP
      hΛ := by simpa [hlab'_eq] using hΛ
      htag := htag'
      h3n := hSlab'.2.2
      hd := hd
      hdr := hdr
      hε := hε1
      hr1 := hr1
      hr2 := hr2
      hn1 := hf1
      hd3 := hd3
      hFcard := hFcard
      hpqF := hpqF
      hU := hU
      θ := θ
      φ := φU
      hφsurj := hφUsurj
      hφker := hφker
      U := U
      hpow := hpow
      hactU := hactU
      P := P
      hPmax := hPmax
      hUP := hUP
      hPele := hPele
      hPcard := hPcard
      A0 := A0
      hA0 := rfl
      hA0card := hA0card
      hSignedSC := hSignedSCfun
      hW := fun hr3 => (hframe hr3).1
      hcard := fun hr3 => (hframe hr3).2
      hHas := hHas }⟩

theorem GGResHyp.exists_opposite_unitary_signedModel
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {Ksub : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y Ksub)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n - 1) 3 Bs J) :
    ∃ (r : ℕ) (lab : LargeEvenLabel),
      LargeEvenInLambda2 lab ∧ lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n - 1 ∧ 2 ≤ r ∧
      (3 ≤ r → Nat.card (ggAutomizer J Bs) = 2 ^ r * r.factorial) ∧
      GGHasLabel lab (J ⧸ Subgroup.center J) ∧
      ∃ (d : ℕ), d = lab.rank + 1 ∧ (d = 2 * r ∨ d = 2 * r + 1) ∧
        Nat.card (ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range = 3 ^ r := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨F, hF, hFfin, n, d, r, ε, lab, hne⟩ :=
    GGResHyp.exists_opposite_unitary_setup hH hMark
  let setup : OppositeUnitarySetup hH hMark F n d r ε lab := Classical.choice hne
  letI : Field F := hF
  letI : Finite F := hFfin
  letI : CharP F 2 := setup.instCharP
  have hε1 : ε ≤ 1 := setup.hε
  have hdr : d = 2 * r + ε := setup.hdr
  have hd2r : d = 2 * r ∨ d = 2 * r + 1 := by
    rcases (by omega : ε = 0 ∨ ε = 1) with h0 | h1
    · left; omega
    · right; omega
  exact ⟨r, lab, setup.hΛ, setup.htag, setup.h3n, setup.hr2, setup.hcard, setup.hHas,
    d, setup.hd, hd2r, by simpa [setup.hA0] using setup.hA0card⟩

theorem GGResHyp.exists_inversion_mem_ggTorusWeylAut_of_opposite_unitary_marking
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {Ksub : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y Ksub)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n - 1) 3 Bs J) :
    ∃ Φ ∈ ggTorusWeylAut 3 (ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range,
      ∀ a : ↥(ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range, Φ a = a⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨F, hF, hFfin, n, d, r, ε, lab, hne⟩ :=
    GGResHyp.exists_opposite_unitary_setup hH hMark
  let setup : OppositeUnitarySetup hH hMark F n d r ε lab := Classical.choice hne
  letI : Field F := hF
  letI : Finite F := hFfin
  letI : CharP F 2 := setup.instCharP
  let hN : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  let φU : unitarySU 2 n F d →* ↥J := setup.φ
  let A0 : Subgroup (MulAut ↥J) := setup.A0
  have hA0 : A0 = (ggGamma J hN).range := by
    dsimp [A0, hN]
    exact setup.hA0
  have hU : UnitaryFieldData 2 n F := setup.hU
  obtain ⟨R, hR⟩ := exists_isHypTransport (K := F) (h := hU) (r := r) (ε := ε)
  let e0 : hypSU hU r ε ≃* unitarySU 2 n F (2 * r + ε) :=
    hypTransport hU hR
  let e : hypSU hU r ε ≃* unitarySU 2 n F d :=
    Eq.mp (by rw [setup.hdr]) e0
  let E : Subgroup (hypSU hU r ε) := setup.P.map e.symm.toMonoidHom
  have hEele : IsElemAbelian 3 E := setup.hPele.map e.symm.toMonoidHom
  have hEcard : Nat.card E = 3 ^ r := by
    rw [Subgroup.card_map_of_injective e.symm.injective, setup.hPcard]
  have hs_hyp : ∃ s : hypSU hU r ε, ∀ x ∈ E, s * x * s⁻¹ = x⁻¹ :=
    inversion_hypSU_any hU setup.hpqF setup.hr1 setup.hε E hEele hEcard
  obtain ⟨s_hyp, hs_hyp⟩ := hs_hyp
  let s : unitarySU 2 n F d := e s_hyp
  have hs : ∀ x ∈ setup.P, s * x * s⁻¹ = x⁻¹ := by
    intro x hx
    have hxE : e.symm x ∈ E := ⟨x, hx, by simp⟩
    have h1 := hs_hyp (e.symm x) hxE
    have h2 := congrArg (fun y => e y) h1
    simpa [s, map_mul, map_inv] using h2
  let w : ↥J := φU s
  have hconj : ∀ b : ↥Bs, ggGamma J hN b = MulAut.conj (φU (setup.U b)) := by
    intro b
    apply MulEquiv.ext
    intro j
    obtain ⟨x, rfl⟩ := setup.hφsurj j
    apply Subtype.ext
    change (b : G) * ((setup.φ x : ↥J) : G) * (b : G)⁻¹ =
      ((MulAut.conj (φU (setup.U b)) (setup.φ x) : ↥J) : G)
    rw [MulAut.conj_apply]
    calc (b : G) * ((setup.φ x : ↥J) : G) * (b : G)⁻¹
        = ((setup.φ (setup.U b * x * (setup.U b)⁻¹) : ↥J) : G) := setup.hactU b x
      _ = ((setup.φ (setup.U b) * setup.φ x * (setup.φ (setup.U b))⁻¹ : ↥J) : G) := by simp
  have hWeyl : GGTorusWeylElt 3 A0 w := by
    intro a ha
    have ha_range : (a : MulAut ↥J) ∈ (ggGamma J hN).range := by
      rw [hA0] at ha
      exact ha
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp ha_range
    have hval : w * ((ggGamma J hN b) w)⁻¹ = φU (setup.U b) := by
      rw [hconj b]
      dsimp [w]
      calc φU s * (φU (setup.U b) * φU s * (φU (setup.U b))⁻¹)⁻¹
          = φU s * (φU (setup.U b) * (φU s)⁻¹ * (φU (setup.U b))⁻¹) := by group
        _ = φU (s * setup.U b * s⁻¹ * (setup.U b)⁻¹) := by
              simp only [map_mul, map_inv]
              group
        _ = φU (setup.U b) := by
              rw [hs (setup.U b) (setup.hUP b)]
              congr 1
              have h3 : setup.U b ^ 3 = 1 := setup.hpow b
              have hinv : (setup.U b)⁻¹ = setup.U b ^ 2 := by
                apply inv_eq_of_mul_eq_one_right
                calc setup.U b * setup.U b ^ 2 = setup.U b ^ 3 := by group
                  _ = 1 := h3
              calc (setup.U b)⁻¹ * (setup.U b)⁻¹ = setup.U b ^ 2 * setup.U b ^ 2 := by rw [hinv]
                _ = setup.U b ^ 4 := by rw [← pow_add]
                _ = setup.U b := by
                    rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, h3, one_mul]
    refine ⟨?_, ?_⟩
    · rw [hval, ← map_pow, setup.hpow b, map_one]
    · intro a' ha'
      have ha'_range : (a' : MulAut ↥J) ∈ (ggGamma J hN).range := by
        rw [hA0] at ha'
        exact ha'
      obtain ⟨b', rfl⟩ := MonoidHom.mem_range.mp ha'_range
      rw [hconj b', hval, MulAut.conj_apply]
      rw [← map_mul, ← map_inv, ← map_mul]
      congr 1
      have hcommP : setup.U b' * setup.U b = setup.U b * setup.U b' :=
        setup.hPmax.comm (setup.U b') (setup.hUP b') (setup.U b) (setup.hUP b)
      rw [hcommP]
      group
  have hAinv : ∀ a ∈ A0, MulAut.conj w * a * (MulAut.conj w)⁻¹ = a⁻¹ := by
    rintro a ha
    have ha_range : (a : MulAut ↥J) ∈ (ggGamma J hN).range := by
      rw [hA0] at ha
      exact ha
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp ha_range
    have hw : w * φU (setup.U b) * w⁻¹ = φU (setup.U b)⁻¹ := by
      dsimp [w]
      rw [show (φU s)⁻¹ = φU s⁻¹ by rw [map_inv]]
      rw [← map_mul, ← map_mul, hs (setup.U b) (setup.hUP b), map_inv]
    calc MulAut.conj w * ggGamma J hN b * (MulAut.conj w)⁻¹
        = MulAut.conj w * MulAut.conj (φU (setup.U b)) * (MulAut.conj w)⁻¹ := by rw [hconj b]
      _ = MulAut.conj (w * φU (setup.U b) * w⁻¹) := by
          rw [← map_mul, ← map_inv, ← map_mul]
      _ = MulAut.conj (φU (setup.U b))⁻¹ := by rw [hw, map_inv]
      _ = (ggGamma J hN b)⁻¹ := by rw [hconj b, map_inv]
  have hn : MulAut.conj w ∈ Subgroup.normalizer (A0 : Set (MulAut ↥J)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hmap_le : A0.map (MulAut.conj (MulAut.conj w)).toMonoidHom ≤ A0 := by
      rintro x ⟨a, ha, rfl⟩
      change MulAut.conj w * a * (MulAut.conj w)⁻¹ ∈ A0
      rw [hAinv a ha]
      exact A0.inv_mem ha
    refine Subgroup.eq_of_le_of_card_ge hmap_le ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj (MulAut.conj w)).injective]
  let Φ : MulAut ↥A0 := ggConjAut A0 hn
  have hΦW : Φ ∈ ggTorusWeylAut 3 A0 := ⟨w, hn, hWeyl, rfl⟩
  have hΦinv : ∀ a : ↥A0, Φ a = a⁻¹ := by
    intro a
    apply Subtype.ext
    rw [ggConjAut_apply]
    exact hAinv a a.2
  have hfinal : ∃ Φ : MulAut ↥A0, Φ ∈ ggTorusWeylAut 3 A0 ∧ ∀ a : ↥A0, Φ a = a⁻¹ :=
    ⟨Φ, hΦW, hΦinv⟩
  have hfinal' : ∃ Φ : MulAut ↥(ggGamma J hN).range,
      Φ ∈ ggTorusWeylAut 3 (ggGamma J hN).range ∧
        ∀ a : ↥(ggGamma J hN).range, Φ a = a⁻¹ := hA0 ▸ hfinal
  simpa [hN] using hfinal'

theorem GGResHyp.actual_J_not_opposite_unitary_for_A3
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {Ksub : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y Ksub)
    (hD : GGResLineJDatum 3 Bs J .A3)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n - 1) 3 Bs J) :
    False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (GGResHyp.not_exists_inversion_mem_ggTorusWeylAut_of_lineJDatum_A3 hH rfl hD)
    (GGResHyp.exists_inversion_mem_ggTorusWeylAut_of_opposite_unitary_marking hH hMark)

theorem GGResHyp.actual_J_not_opposite_unitary_for_A2
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {Ksub : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y Ksub)
    (hD : GGResLineJDatum 3 Bs J .A2)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n - 1) 3 Bs J) :
    False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA2 : 2 ≤ Nat.card (ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range :=
    (by norm_num : 2 ≤ 3 ^ 2).trans (GGResHyp.sq_le_card_gamma_J hH)
  exact (not_exists_inversion_mem_ggTorusWeylAut_of_lineJDatum_A2
    (GGResHyp.Bs_le_normalizer_J hH) hH.1.2.1.2.1 hH.1.2.1.2.2.2 hH.2.2.2.1
    (GGResHyp.card_bstar_inf_center_J_le hH) rfl hA2 hD)
    (GGResHyp.exists_inversion_mem_ggTorusWeylAut_of_opposite_unitary_marking hH hMark)

theorem GGResHyp.exists_lineJLabel_of_opposite_unitary_B2
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {Ksub : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y Ksub)
    (hD : GGResLineJDatum 3 Bs J .B2)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n - 1) 3 Bs J) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ ggResLineJLabel .B2 lab ∧
      GGHasLabel lab (J ⧸ Subgroup.center J) := by
  classical
  obtain ⟨r, lab, hΛ, htag, h3n, _hr2, hcond, hHas, d, hd, hd2r, _hA0card⟩ :=
    GGResHyp.exists_opposite_unitary_signedModel hH hMark
  have hAut8 : Nat.card (ggAutomizer J Bs) = 8 :=
    ggAutomizer_card_of_lineJDatum_B2 (p := 3) rfl hD
  have hrle2 : r ≤ 2 := by
    by_contra h
    have hr3 : 3 ≤ r := by omega
    have hEq := hcond hr3
    rw [hAut8] at hEq
    have hpow : 8 ≤ 2 ^ r := by
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hr3
      norm_num at this ⊢
      exact this
    have hfact : 6 ≤ r.factorial := by
      have := Nat.factorial_le hr3
      norm_num at this ⊢
      exact this
    have hge : 48 ≤ 2 ^ r * r.factorial := Nat.mul_le_mul hpow hfact
    omega
  have hr : r = 2 := by omega
  have hdval : d = 4 ∨ d = 5 := by
    rcases hd2r with h | h <;> omega
  have hrank : lab.rank = 3 ∨ lab.rank = 4 := by
    rcases hdval with h | h <;> omega
  refine ⟨lab, hΛ, ?_, hHas⟩
  unfold ggResLineJLabel
  exact Or.inr (Or.inr (Or.inr ⟨Or.inl ⟨htag, hrank⟩, h3n⟩))

theorem GGResHyp.exists_lineJLabel_of_opposite_unitary_B3C3
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {Ksub : Subgroup G}
    {T : GGResLineJType}
    (hH : GGResHyp 3 B Bs x L D J y Ksub)
    (hD : GGResLineJDatum 3 Bs J T)
    (hT : T = .B3 ∨ T = .C3)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n - 1) 3 Bs J) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ ggResLineJLabel T lab ∧
      GGHasLabel lab (J ⧸ Subgroup.center J) := by
  classical
  obtain ⟨r, lab, hΛ, htag, h3n, _hr2, hcond, hHas, d, hd, hd2r, hA0card⟩ :=
    GGResHyp.exists_opposite_unitary_signedModel hH hMark
  have hN : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  have h27 : 3 ^ 3 ≤ Nat.card (ggGamma J hN).range := by
    simpa using cube_le_card_gamma_of_B3C3 hN hD hT
  have hr3 : 3 ≤ r := by
    rw [hA0card] at h27
    by_contra h
    have hrle : r ≤ 2 := by omega
    have hle : 3 ^ r ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hrle
    norm_num at h27 hle
    omega
  have hEq := hcond hr3
  have hAut48 : Nat.card (ggAutomizer J Bs) = 48 := by
    rcases hT with rfl | rfl
    · exact ggAutomizer_card_of_lineJDatum_B3 (p := 3) rfl hD
    · exact ggAutomizer_card_of_lineJDatum_C3 (p := 3) rfl hD
  have h48 : 48 = 2 ^ r * r.factorial := by
    rw [← hAut48]
    exact hEq
  have hrle3 : r ≤ 3 := by
    by_contra h
    have h4 : 4 ≤ r := by omega
    have hpow : 16 ≤ 2 ^ r := by
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h4
      norm_num at this ⊢
      exact this
    have hfact : 24 ≤ r.factorial := by
      have := Nat.factorial_le h4
      norm_num at this ⊢
      exact this
    have hge : 384 ≤ 2 ^ r * r.factorial := Nat.mul_le_mul hpow hfact
    omega
  have hr : r = 3 := by omega
  have hdval : d = 6 ∨ d = 7 := by
    rcases hd2r with h | h <;> omega
  have hrank : lab.rank = 5 ∨ lab.rank = 6 := by
    rcases hdval with h | h <;> omega
  refine ⟨lab, hΛ, ?_, hHas⟩
  rcases hT with rfl | rfl <;>
    · unfold ggResLineJLabel
      exact Or.inr (Or.inr (Or.inl ⟨htag, hrank, h3n⟩))

end A3OppositeRecognition

end CFSG.StandardType
