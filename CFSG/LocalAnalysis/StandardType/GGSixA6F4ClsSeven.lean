module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedF4ClassDefs
public import CFSG.HardMathSupport.Dickson.Bal207.FamF42Class
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6
public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane
public import CFSG.LocalAnalysis.StandardType.GGLieCoreCent
public import CFSG.LocalAnalysis.StandardType.GGSixA6F4ClsEmbed
public import CFSG.LocalAnalysis.StandardType.GGSixA6F4ClsRegular
public import CFSG.LocalAnalysis.StandardType.GGLieCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGLieCoreToralHolds
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobeniusOnRoots
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToral

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Assembly.LowTwoRank
  CFSG.StandardType.LieCore CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)

private theorem ggA6F4_isElemAbelian_map {G H : Type*} [Group G] [Group H] {p : ℕ}
    {D : Subgroup G} (f : G →* H) (hinj : Function.Injective f) (hD : IsElemAbelian p D) :
    IsElemAbelian p (D.map f) := by
  constructor
  · rw [isMulCommutative_iff]
    intro a b
    obtain ⟨a', ha', ha'eq⟩ := a.2
    obtain ⟨b', hb', hb'eq⟩ := b.2
    have hcomm : a' * b' = b' * a' :=
      congrArg Subtype.val (isMulCommutative_iff.1 hD.1 ⟨a', ha'⟩ ⟨b', hb'⟩)
    apply Subtype.ext
    show a.1 * b.1 = b.1 * a.1
    rw [← ha'eq, ← hb'eq, ← map_mul, ← map_mul, hcomm]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hD.2 a ha, map_one]

theorem ggA6F4_not_seven
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {G : Type} [Group G] [Finite G]
    (e : G ≃* ↥(adjointGroup .F4 K)) {D J : Subgroup G} (hD : IsElemAbelian 7 D)
    (hDc : Nat.card D = 7 ^ 2) (hJ : Nonempty (↥J ≃* alternatingGroup (Fin 6)))
    (hDJ : D ≤ Subgroup.centralizer (J : Set G)) : False := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = 2 ^ 1 := by
    rw [← Nat.card_eq_fintype_card, hK]
    norm_num
  haveI : CharP K 2 := charP_of_card_eq_prime_pow hcardK
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Φ, hΦ, ι, hιinj, hιrange⟩ := ggA6F4_embed (K := K) hK
  let f : G →* ModGL Tag.F4 (AlgebraicClosure K) := ι.comp e.toMonoidHom
  let A : Subgroup (ModGL Tag.F4 (AlgebraicClosure K)) := D.map f
  have hfinj : Function.Injective f := hιinj.comp e.injective
  have hAcard : Nat.card A = 7 ^ 2 := by
    rw [Subgroup.card_map_of_injective (K := D) (f := f) hfinj, hDc]
  have hAel : IsElemAbelian 7 A := ggA6F4_isElemAbelian_map f hfinj hD
  have hArat : A ≤ ratPoints Φ := by
    rintro x ⟨d, hd, rfl⟩
    exact hιrange ⟨e d, rfl⟩
  have hcardlt : Nat.card A < 7 ^ nontoralMinRank Tag.F4 7 := by
    rw [hAcard]
    exact Nat.pow_lt_pow_right (by norm_num) (by decide)
  have halg : letI := ZMod.algebra (AlgebraicClosure K) 2
      Algebra.IsAlgebraic (ZMod 2) (AlgebraicClosure K) :=
    isAlgebraic_zmod_algebraicClosure_of_finite K 2
  have hT : IsToralSubgroup Tag.F4 (AlgebraicClosure K) A :=
    ggLieToralPosition_holds Tag.F4 (isExcTag Tag.F4) (AlgebraicClosure K) halg 1 (le_refl 1) Φ
      (isSteinbergEndZ_of_isSteinbergEnd hΦ)
      (finite_ratPoints (q := 2 ^ 1) (by norm_num) (isSteinbergEndZ_of_isSteinbergEnd hΦ))
      7 Nat.prime_seven (by norm_num) A hArat hAel hcardlt
  obtain ⟨w, g, hg, hlang, a₁, a₂, _hmodel, htorus1, htorus2, hpow1, hpow2, hmap⟩ :=
    ggLiePlaneFrame (f := 1) (le_refl 1) hΦ Nat.prime_seven (by norm_num) hArat hAel hAcard hT
  let Dd : LangDatum Tag.F4 (AlgebraicClosure K) := langDatumOfPosition hΦ w g hg hlang
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved Tag.F4 (AlgebraicClosure K) Dd
  let h : ModGL Tag.F4 (AlgebraicClosure K) →* ModGL Tag.F4 (AlgebraicClosure K) :=
    (MulAut.conj g⁻¹).toMonoidHom
  let ψ : G →* ModGL Tag.F4 (AlgebraicClosure K) := h.comp f
  let A' : Subgroup (ModGL Tag.F4 (AlgebraicClosure K)) := A.map h
  let J' : Subgroup (ModGL Tag.F4 (AlgebraicClosure K)) := J.map ψ
  have hhinj : Function.Injective h := (MulAut.conj g⁻¹).injective
  have hψinj : Function.Injective ψ := hhinj.comp hfinj
  have hA'map : A' = Subgroup.closure {rootDiagUnit Tag.F4 a₁, rootDiagUnit Tag.F4 a₂} := hmap
  have hA'card : Nat.card A' = 7 ^ 2 := by
    rw [Subgroup.card_map_of_injective (K := A) (f := h) hhinj, hAcard]
  have hroot : ∀ γ, IsRoot Tag.F4 (ρ γ) ↔ IsRoot Tag.F4 γ := hρ.isRoot_iff
  have hDq : Dd.q = 2 := by
    change (2 : ℕ) ^ 1 = 2
    norm_num
  have hchar : ∀ γ, IsRoot Tag.F4 γ →
      rootChar a₁ (ρ γ) = rootChar a₁ γ ^ 2 ∧ rootChar a₂ (ρ γ) = rootChar a₂ γ ^ 2 := by
    intro γ hγ
    refine ⟨?_, ?_⟩
    · have h := hρ.rootChar_eq a₁ htorus1 γ hγ
      rwa [hDq] at h
    · have h := hρ.rootChar_eq a₂ htorus2 γ hγ
      rwa [hDq] at h
  have hcard' : Nat.card (Subgroup.closure {rootDiagUnit Tag.F4 a₁, rootDiagUnit Tag.F4 a₂}) =
      7 ^ 2 := by
    rw [← hA'map]
    exact hA'card
  have hrt : rootsTrivialOn
      (Subgroup.closure {rootDiagUnit Tag.F4 a₁, rootDiagUnit Tag.F4 a₂}) = ∅ :=
    ggA6F4_rootsTrivialOn_eq_empty a₁ a₂ hpow1 hpow2 hcard' ρ hroot hchar
  have hcent : centConn
      (Subgroup.closure {rootDiagUnit Tag.F4 a₁, rootDiagUnit Tag.F4 a₂}) =
      torusGroup Tag.F4 (AlgebraicClosure K) := by
    unfold centConn
    rw [hrt, rootSpan, iSup_emptyset, sup_bot_eq]
  have hcommDJ : ∀ d ∈ D, ∀ j ∈ J, j * d = d * j :=
    fun d hd j hj => (Subgroup.mem_centralizer_iff.1 (hDJ hd)) j hj
  have hAJ' : A' ≤ Subgroup.centralizer (J' : Set (ModGL Tag.F4 (AlgebraicClosure K))) := by
    rintro y ⟨a, ha, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro x ⟨j, hj, rfl⟩
    obtain ⟨d, hd, rfl⟩ := ha
    show ψ j * ψ d = ψ d * ψ j
    rw [← map_mul ψ j d, ← map_mul ψ d j, hcommDJ d hd j hj]
  have hJ'cent : J' ≤ Subgroup.centralizer (A' : Set (ModGL Tag.F4 (AlgebraicClosure K))) :=
    (Subgroup.le_centralizer_iff).2 hAJ'
  have hJ'adj : J' ≤ adjointGroup Tag.F4 (AlgebraicClosure K) := by
    rintro x ⟨j, hj, rfl⟩
    have hconj : h (f j) = g⁻¹ * f j * g := by
      change (MulAut.conj g⁻¹) (f j) = g⁻¹ * f j * g
      rw [MulAut.conj_apply, inv_inv]
    show h (f j) ∈ adjointGroup Tag.F4 (AlgebraicClosure K)
    rw [hconj]
    exact mul_mem (mul_mem (inv_mem hg) (hιrange ⟨e j, rfl⟩).1) hg
  have hpowmem : ∀ x ∈ J', ∃ k, x ^ 7 ^ k ∈ torusGroup Tag.F4 (AlgebraicClosure K) := by
    intro x hx
    have hx' : x ∈ Subgroup.centralizer (A' : Set (ModGL Tag.F4 (AlgebraicClosure K))) :=
      hJ'cent hx
    have hxcl : x ∈ Subgroup.centralizer
        (Subgroup.closure {rootDiagUnit Tag.F4 a₁, rootDiagUnit Tag.F4 a₂} :
          Set (ModGL Tag.F4 (AlgebraicClosure K))) := by
      rw [hA'map] at hx'
      exact hx'
    obtain ⟨k, hk⟩ := ggLieCentStructure_pow_mem (p := 7) Nat.prime_seven (by norm_num)
      a₁ a₂ hpow1 hpow2 x ⟨hJ'adj hx, hxcl⟩
    exact ⟨k, by rw [hcent] at hk; exact hk⟩
  have hJ'card : Nat.card J' = 360 := by
    rw [Subgroup.card_map_of_injective (K := J) (f := ψ) hψinj]
    obtain ⟨φ⟩ := hJ
    rw [Nat.card_congr φ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hJ'torus : J' ≤ torusGroup Tag.F4 (AlgebraicClosure K) := by
    intro x hx
    obtain ⟨k, hk⟩ := hpowmem x hx
    have hdvd : orderOf x ∣ 360 := by
      rw [← hJ'card]
      exact Subgroup.orderOf_dvd_natCard J' hx
    have h7 : ¬ 7 ∣ orderOf x := fun h =>
      (by norm_num : ¬ (7 : ℕ) ∣ 360) (dvd_trans h hdvd)
    have hcop : Nat.Coprime (7 ^ k) (orderOf x) :=
      (Nat.Prime.coprime_pow_of_not_dvd Nat.prime_seven h7).symm
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm]
    exact Subgroup.pow_mem _ hk m
  have hcommJ : IsMulCommutative ↥J := by
    rw [isMulCommutative_iff]
    intro a b
    apply Subtype.ext
    apply hψinj
    show ψ (a.1 * b.1) = ψ (b.1 * a.1)
    rw [map_mul, map_mul]
    exact torusGroup_comm (hJ'torus (Subgroup.mem_map_of_mem ψ a.2))
      (hJ'torus (Subgroup.mem_map_of_mem ψ b.2))
  obtain ⟨φ⟩ := hJ
  have hcommA6 : IsMulCommutative (alternatingGroup (Fin 6)) := by
    rw [isMulCommutative_iff]
    intro a b
    obtain ⟨a', rfl⟩ := φ.surjective a
    obtain ⟨b', rfl⟩ := φ.surjective b
    calc φ a' * φ b' = φ (a' * b') := (map_mul φ a' b').symm
      _ = φ (b' * a') := by rw [isMulCommutative_iff.1 hcommJ a' b']
      _ = φ b' * φ a' := map_mul φ b' a'
  have hnotcomm : ¬ IsMulCommutative (alternatingGroup (Fin 6)) := by
    rw [alternatingGroup.isMulCommutative_iff_card_le_three, Nat.card_fin]
    norm_num
  exact hnotcomm hcommA6

end CFSG.StandardType.A6Red
