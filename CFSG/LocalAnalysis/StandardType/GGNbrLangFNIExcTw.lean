module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIExcUntw
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIVacTwisted
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcDataTw

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.GLTheoremA.K155X (excTw_transport)


@[expose] def kgfniTwTag : TwistTag → LargeEvenLieTag
  | .E6 => .twE6
  | .D4 => .triD4

theorem largeEvenRawDatum_kgfniTwTag (t : TwistTag) (r n : ℕ) (Q : LargeEvenRawCont) :
    LargeEvenRawDatum ⟨kgfniTwTag t, r, n⟩ Q ↔
      LargeEvenRecipeTwisted t.tag.cartan t.perm t.order n Q := by
  cases t <;> exact Iff.rfl

theorem excTw_perfect {t : TwistTag} {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ t.order) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n)) :
    ⁅twistedFixedGroup t K σ.toRingHom, twistedFixedGroup t K σ.toRingHom⁆ =
      graphFixedRootGroup t K σ.toRingHom := by
  cases t
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, hcomm, -⟩ :=
      twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hn K hK σ hσ
    exact hcomm
  · obtain ⟨-, -, -, -, -, hcomm, -⟩ := even_triality_exact_automorphism_normal_form hn K hK σ hσ
    exact hcomm

theorem kgfniTw_hOne_recipe {t : TwistTag} {K : Type} [Field K] [Finite K] {n p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ t.order) :
    kgfni_hOneProp p (LargeEvenCenterQuot (LargeEvenTwistedH t.tag.cartan K t.perm n))
      (LargeEvenChevIDImage t.tag.cartan K _) (LargeEvenChevFieldImage t.tag.cartan K _) := by
  have hlab : LargeEvenInLambda2 ⟨kgfniTwTag t, 0, n⟩ := by
    cases t <;> exact ⟨hn, rfl⟩
  have htw : KGFNITwistedLabel ⟨kgfniTwTag t, 0, n⟩ := by
    cases t
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  have hself : LargeEvenRawDatum ⟨kgfniTwTag t, 0, n⟩
      (fun R' _ _ F' =>
        ∃ e : LargeEvenCenterQuot (LargeEvenTwistedH t.tag.cartan K t.perm n) ≃* R',
          F' = MulAut.congr e '' LargeEvenChevFieldImage t.tag.cartan K
            (LargeEvenTwistedH t.tag.cartan K t.perm n)) := by
    rw [largeEvenRawDatum_kgfniTwTag]
    dsimp only [LargeEvenRecipeTwisted]
    refine ⟨K, inferInstance, inferInstance, hK, MulEquiv.refl _, ?_⟩
    ext φ
    simp only [Set.mem_image]
    constructor
    · intro h
      exact ⟨φ, h, rfl⟩
    · rintro ⟨x, hx, hφx⟩
      rw [← hφx]
      exact hx
  exact fun f hf hord h hh hhp hcomm hh1 J hJ f' hf' =>
    kgFieldRestriction_hOne_of_rawImage hp hp2 hlab (kgfni_rawSimple_twisted _ hlab htw) hself
      f hf hord J (by simpa [hh1] using hJ) f' hf'

theorem kgfniTw_hOne_model {t : TwistTag} {K : Type} [Field K] [Finite K] {n p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ t.order)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n)) :
    kgfni_hOneProp p (LargeEvenCenterQuot (graphFixedRootGroup t K σ.toRingHom))
      (RecipeExcLang.markIDImage (IsRoot t.tag) K (graphFixedRootGroup t K σ.toRingHom))
      (RecipeFieldExcInn.markFieldImage (IsRoot t.tag) K
        (graphFixedRootGroup t K σ.toRingHom)) :=
  excTw_transport σ hσ (excTw_perfect hn hK σ hσ) (Q := kgfni_hOneProp p)
    (kgfniTw_hOne_recipe hp hp2 hn hK)

theorem kgFieldRestrictionOn_of_excTw_model {t : TwistTag} {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = kgfniTwTag t)
    (hmodel : ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K),
      Nat.card K = (2 ^ lab.n) ^ t.order → (∀ c, σ c = c ^ (2 ^ lab.n)) →
      KGFieldRestrictionCont p (LargeEvenCenterQuot (graphFixedRootGroup t K σ.toRingHom))
        (RecipeExcLang.markIDImage (IsRoot t.tag) K (graphFixedRootGroup t K σ.toRingHom))
        (RecipeFieldExcInn.markFieldImage (IsRoot t.tag) K
          (graphFixedRootGroup t K σ.toRingHom))) :
    LargeEvenLabelAll lab (KGFieldRestrictionCont p) := by
  obtain ⟨tg, r, n⟩ := lab
  dsimp only at htag hmodel
  subst htag
  have hn : 1 ≤ n := hlab.1
  intro Q hraw
  rw [largeEvenRawDatum_kgfniTwTag] at hraw ⊢
  dsimp only [LargeEvenRecipeTwisted] at hraw ⊢
  obtain ⟨K, hF, hfin, hK, hQ⟩ := hraw
  letI := hF
  haveI := hfin
  haveI : CharP K 2 :=
    CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (f := n * t.order) (by rw [hK, ← pow_mul])
  set σ := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  have hRec : KGFieldRestrictionCont p
      (LargeEvenCenterQuot (LargeEvenTwistedH t.tag.cartan K t.perm n))
      (LargeEvenChevIDImage t.tag.cartan K _) (LargeEvenChevFieldImage t.tag.cartan K _) := by
    by_contra hnc
    exact (excTw_transport σ hσ (excTw_perfect hn hK σ hσ)
      (Q := fun R _ I F => ¬ KGFieldRestrictionCont p R I F) hnc) (hmodel K σ hK hσ)
  exact ⟨K, hF, hfin, hK, hQ, hRec⟩

end CFSG.StandardType

end
