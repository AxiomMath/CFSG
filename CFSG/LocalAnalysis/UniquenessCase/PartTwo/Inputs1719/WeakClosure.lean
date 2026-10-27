module

public import CFSG.LocalAnalysis.WeakClosure81.SixFiveTwo
public import CFSG.LocalAnalysis.WeakClosure81.SevenKDefs
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs
public import CFSG.LocalAnalysis.WeakClosure81.NineDefs
public import CFSG.Timmesfeld.Bridge.Asc72Defs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Quasithin.Background.E3ClosedTwo
public import CFSG.Quasithin.Background.E3Weak
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isE_not_le_pCoreOf {H S A : Subgroup G} {k : ℕ} (hK : E1.IsE k H S A H) :
    ¬ A ≤ pCoreOf 2 H := by
  intro hA
  have hAle : A.subgroupOf H ≤ CFSG.Open.pCore 2 ↥H := by
    intro x hx
    have hxA : (x : G) ∈ A := Subgroup.mem_subgroupOf.mp hx
    have hxP : (x : G) ∈ CFSG.Open.pCoreOf 2 H := hA hxA
    simp only [CFSG.Open.pCoreOf] at hxP
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hxP
    have hyeq : y = x := H.subtype_injective (by simpa using hyx)
    rwa [← hyeq]
  have hbarO2 : E1.barO2 ↥H (A.subgroupOf H) = ⊥ := by
    rw [E1.barO2, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hAle
  have hbarRad : E1.barRad ↥H (A.subgroupOf H) = ⊥ := by
    rw [E1.barRad, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hAle.trans E3.pCore_two_le_solvableRadical
  have hcard_bot : Nat.card (⊥ : Subgroup (↥H ⧸ CFSG.Open.pCore 2 ↥H)) = 1 := Subgroup.card_bot
  have hcard_bot' : Nat.card (⊥ : Subgroup (↥H ⧸ CFSG.solvableRadical ↥H)) = 1 := Subgroup.card_bot
  rcases hK.2.2.2 with ⟨h1, -⟩ | ⟨h2, -⟩
  · obtain ⟨p, -, -, -, -, -, hcard⟩ := h1
    rw [hbarO2, hcard_bot] at hcard
    exact absurd hcard (by norm_num)
  · obtain ⟨-, -, -, L, hL, -, hdisj⟩ := h2
    have hLne : L ≠ ⊥ :=
      (Subgroup.nontrivial_iff_ne_bot L).mp
        (CFSG.LocalCores.isQuasisimple_nontrivial hL.1)
    rcases hdisj with hLeq | ⟨-, hcard⟩
    · exact hLne (by rw [hLeq, hbarRad]; simp)
    · rw [hbarRad, hcard_bot'] at hcard
      exact absurd hcard (by norm_num)

private theorem map_conj_eq_conjSubgroup (X : Subgroup G) (x : G) :
    X.map (MulAut.conj x).toMonoidHom = conjSubgroup X x⁻¹ := by
  rw [CFSG.Quasithin.conjSubgroup, inv_inv]

private theorem twoResidual_map_conj (H : Subgroup G) (x : G) :
    twoResidual (conjSubgroup H x⁻¹) = conjSubgroup (twoResidual H) x⁻¹ := by
  have h1 : H.map (MulAut.conj x).toMonoidHom = conjSubgroup H x⁻¹ :=
    map_conj_eq_conjSubgroup H x
  have h2 : (twoResidual H).map (MulAut.conj x).toMonoidHom = conjSubgroup (twoResidual H) x⁻¹ :=
    map_conj_eq_conjSubgroup (twoResidual H) x
  have h := E1.twoResidual_map_mulEquiv (e := MulAut.conj x) H
  rw [h1, h2] at h
  exact h.symm

private theorem isE_conj' {x : G} {i : ℕ} {H S A K : Subgroup G} :
    E1.IsE i (conjSubgroup H x⁻¹) (conjSubgroup S x⁻¹) (conjSubgroup A x⁻¹)
      (conjSubgroup K x⁻¹) ↔ E1.IsE i H S A K := by
  have h := E1.isE_map_mulEquiv (e := MulAut.conj x) (i := i) (H := H) (T := S) (A := A) (K := K)
  simpa only [map_conj_eq_conjSubgroup] using h

private theorem isSylowIn_conj' {x : G} {p : ℕ} {P H : Subgroup G} :
    IsSylowIn p (conjSubgroup P x⁻¹) (conjSubgroup H x⁻¹) ↔ IsSylowIn p P H := by
  have h := E1.isSylowIn_conj_iff (g := x) (p := p) (P := P) (H := H)
  simpa only [A1b.conjSub, map_conj_eq_conjSubgroup] using h

theorem conj_reduction {V H S A : Subgroup G} {i k n : ℕ}
    (hS : IsSylowIn 2 S H) (hA : A ∈ E3.gammaSet V i S) (hK : E1.IsE k H S A H)
    (hne : ⁅twoResidual H, E3.cClos V n S⁆ ≠ ⊥) :
    ∃ H' S' A' : Subgroup G,
      IsSylowIn 2 S' H' ∧ E1.IsE k H' S' A' H' ∧ A' ∈ E3.gammaSet V i S' ∧ A' ≤ V ∧
        ¬ A' ≤ pCoreOf 2 H' ∧ ⁅twoResidual H', E3.cClos V n S'⁆ ≠ ⊥ := by
  obtain ⟨hAS, x, hAx, hmx⟩ := hA
  have hAg : A ∈ E3.gammaSet V i S := ⟨hAS, x, hAx, hmx⟩
  have hS' : IsSylowIn 2 (conjSubgroup S x⁻¹) (conjSubgroup H x⁻¹) :=
    (isSylowIn_conj' (x := x)).2 hS
  have hK' : E1.IsE k (conjSubgroup H x⁻¹) (conjSubgroup S x⁻¹) (conjSubgroup A x⁻¹)
      (conjSubgroup H x⁻¹) := (isE_conj' (x := x) (i := k)).2 hK
  have hAg' : conjSubgroup A x⁻¹ ∈ E3.gammaSet V i (conjSubgroup S x⁻¹) :=
    E3.conj_mem_gammaSet (V := V) (i := i) x⁻¹ hAg
  have hAV' : conjSubgroup A x⁻¹ ≤ V := by
    have h1 := E3.conjSubgroup_mono_left (A := A) (B := conjSubgroup V x) x⁻¹ hAx
    rwa [E3.conjSubgroup_conj_inv] at h1
  have hAne' : ¬ conjSubgroup A x⁻¹ ≤ pCoreOf 2 (conjSubgroup H x⁻¹) := isE_not_le_pCoreOf hK'
  have hne' : ⁅twoResidual (conjSubgroup H x⁻¹), E3.cClos V n (conjSubgroup S x⁻¹)⁆ ≠ ⊥ := by
    rw [twoResidual_map_conj, E3.cClos_conj]
    rw [show conjSubgroup (twoResidual H) x⁻¹ =
        (twoResidual H).map (MulAut.conj x).toMonoidHom from
        (map_conj_eq_conjSubgroup _ _).symm,
      show conjSubgroup (E3.cClos V n S) x⁻¹ =
        (E3.cClos V n S).map (MulAut.conj x).toMonoidHom from
        (map_conj_eq_conjSubgroup _ _).symm,
      ← Subgroup.map_commutator]
    intro hbot
    obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    have hzmap : (MulAut.conj x) z ∈
        (⁅twoResidual H, E3.cClos V n S⁆).map (MulAut.conj x).toMonoidHom :=
      Subgroup.mem_map.2 ⟨z, hz, rfl⟩
    rw [hbot] at hzmap
    have hz1' : z = 1 :=
      (MulAut.conj x).injective (by rw [Subgroup.mem_bot.mp hzmap, map_one])
    exact hz1 (Subtype.ext hz1')
  exact ⟨conjSubgroup H x⁻¹, conjSubgroup S x⁻¹, conjSubgroup A x⁻¹,
    hS', hK', hAg', hAV', hAne', hne'⟩

@[expose] def W3Lem71 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (V : Subgroup G) (g : G), Hyp7 V → g ∉ normalizer (V : Set G) →
    let U := V ⊓ normalizer (conjSubgroup V g)
    let B := conjSubgroup V g ⊓ normalizer (V : Set G)
    let X := V ⊔ conjSubgroup V g
    U ≠ ⊥ → U ≠ V → ⁅V, conjSubgroup V g⁆ ≠ ⊥ →
      pCoreOf 2 X = U ⊔ B ∧ U ⊓ B = ⊥ ∧ ⁅U, B⁆ = ⊥ ∧
      HasQuotShape X (pCoreOf 2 X)
        (fun Z _ => (∃ n : ℕ, IsL2 Z n ∧ E3.mQuot V U = n) ∨
          (∃ n : ℕ, IsSz Z n ∧ E3.mQuot V U = n) ∨
          (∃ m : ℕ, Odd m ∧ Nonempty (Z ≃* DihedralGroup m) ∧ E3.mQuot V U = 1)) ∧
      (∀ v ∈ V, v ∉ U → ∀ x ∈ conjSubgroup V g, x ∉ B → Odd (orderOf (v * x))) ∧
      ((∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
          Nat.card F = 2 ^ n ∧ E3.mQuot V U = n ∧
          ∃ act : ↥X →* Matrix (Fin 2) (Fin 2) F,
            (∀ x : ↥X, act x = 1 ↔ (x : G) ∈ pCoreOf 2 X) ∧
            IsNaturalSum (fun x => act x) ((pCoreOf 2 X).subgroupOf X)) ∨
        (∃ (a : ℕ) (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
          Nat.card F = 2 ^ (2 * a + 1) ∧ E3.mQuot V U = 2 * a + 1 ∧
          ∃ act : ↥X →* Matrix (Fin 4) (Fin 4) F,
            (∀ x : ↥X, act x = 1 ↔ (x : G) ∈ pCoreOf 2 X) ∧
            IsNaturalSum (fun x => act x) ((pCoreOf 2 X).subgroupOf X)) ∨
        (∃ m : ℕ, Odd m ∧ E3.mQuot V U = 1 ∧
          HasQuotShape X (pCoreOf 2 X) (fun Z _ => Nonempty (Z ≃* DihedralGroup m)) ∧
          ∃ s : Finset (Subgroup G), s.SupIndep id ∧ s.sup id = pCoreOf 2 X ∧
            ∀ W ∈ s, W ≤ pCoreOf 2 X ∧ X ≤ Subgroup.normalizer (W : Set G) ∧ W ≠ ⊥ ∧
              ∀ W' : Subgroup G, W' ≤ W → X ≤ Subgroup.normalizer (W' : Set G) →
                W' = ⊥ ∨ W' = W))

@[expose] def W3Lem711 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (V H E : Subgroup G), SevenK.Hyp711 V H E →
    let K := kSub V H E
    let J := pCoreOf 2 K
    (∀ u ∈ dSet V H E, ∀ v ∈ dSet V H E, ∃ k ∈ K, u = k * v * k⁻¹) ∧
    ∀ (X : Type) [Group X] (φ : ↥K →* X), SevenK.IsBarMap K J φ →
      ((∃ m n : ℕ, HasQuotShape K (centerPre K J)
            (fun Z _ => IsSpGp Z m n ∨ IsPSUGp Z m n ∨ IsSz Z n) ∧
          CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp (SevenK.barSet K φ (dSet V H E))) ∨
        (∃ m n : ℕ, HasQuotShape K (centerPre K J)
            (fun Z _ => CFSG.Blueprint.LieModel Z .PSL m 2 n) ∧
          ∃ S : Subgroup G, V ≤ S ∧ IsSylowIn 2 S K ∧
            IsWeaklyClosedIn (SevenK.barSub K φ V) (SevenK.barSub K φ S)) ∨
        ((∃ (Y : Type) (_ : Group Y) (ψ : X →* Y), Function.Surjective ψ ∧
            Nat.card ψ.ker = 3 ∧ ψ.ker ≤ Subgroup.center X ∧
            Nonempty (Y ≃* alternatingGroup (Fin 6))) ∧
          Nat.card (SevenK.barSub K φ V) = 4 ∧
          ∃ S : Subgroup G, V ≤ S ∧ IsSylowIn 2 S K ∧
            IsWeaklyClosedIn (SevenK.barSub K φ V) (SevenK.barSub K φ S)) ∨
        (∃ m n : ℕ, Nat.card (SevenK.barSub K φ V) = 2 ∧
          HasQuotShape K (centerPre K J) (fun Z _ => IsSpGp Z m n ∨ IsPSUGp Z m n ∨
            IsOrthGp Z m n ∨ IsL2WrSymGp Z n m)) ∨
        (∃ n : ℕ, Nat.card (SevenK.barSub K φ V) = 2 ∧
          HasQuotShape K
            {g : G | g ∈ K ∧ ∀ h : g ∈ K, φ ⟨g, h⟩ ∈ fusionOddCoreOf (⊤ : Subgroup X)}
            (fun Z _ => IsSymGp Z n)) ∨
        (Nat.card (SevenK.barSub K φ V) = 2 ∧ IsThreeCoverOrth6Minus X))

@[expose] def W3Lem915 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (V T N L : Subgroup G), Hyp9 V T → T ≤ N → N ≤ normalizer (V : Set G) → N = T ⊔ L →
    L = CFSG.Quasithin.perfectCore (L ⊔ pCoreOf 2 N) →
    (∃ (Z : Type) (_ : Group Z) (ψ : ↥N →* Z), Function.Surjective ψ ∧
      (∀ x : ↥N, ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 N) ∧
      CFSG.IsComponent ((L.subgroupOf N).map ψ) ∧
      IsL3 ↥((L.subgroupOf N).map ψ) 1) →
    ∀ (L₁ L₂ : Subgroup G), L₁ = L → (∃ t ∈ T, L₂ = conjSubgroup L t) → L₁ ≠ L₂ →
      (∀ t ∈ T, conjSubgroup L t = L₁ ∨ conjSubgroup L t = L₂) →
      ∀ X : Subgroup G, IsSylowIn 3 X N → X ⊓ L₁ ∈ calP V → X ⊓ L₂ ∈ calP V →
        normalizer (E3.wClos V 1 T : Set G) ≤ normalizer (V : Set G) ∨
          N ≤ normalizer (E3.wClos V 0 T : Set G)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
