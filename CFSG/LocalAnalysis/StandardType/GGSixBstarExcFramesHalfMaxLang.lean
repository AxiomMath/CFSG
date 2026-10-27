module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxDefs
public import CFSG.HardMathSupport.Timmesfeld.Torality.LangAssembly

public section

namespace CFSG.StandardType

namespace ExcFramesHalf

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.CrossChar

section Lang


theorem exists_langTorus_of_toral_bar {τ : Tag} {p : ℕ} (hp : p.Prime)
    (hbar : BigElemAbelianToralBar τ p) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hpK : ¬ p ∣ Nat.card K) (E : Subgroup (adjointGroup τ K)) (hE : IsElemAbelian p E)
    (hcard : p ^ (τ.rank - 1) ≤ Nat.card E) :
    ∃ w : WeylGroup τ, ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K,
      (∀ c, Fr c = c ^ Nat.card K) ∧
      ∃ g0 ∈ adjointGroup τ (AlgebraicClosure K),
        Units.map (entrywiseHom Fr) g0 =
          g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w ∧
        ∀ x ∈ E, baseChangeGL (algebraMap K (AlgebraicClosure K)) ((x : adjointGroup τ K) : ModGL τ K) ∈
          (twistedTorusOf (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
            (Units.map (entrywiseHom Fr))).map (MulAut.conj g0).toMonoidHom := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set L := AlgebraicClosure K with hLdef
  set ι : K →+* L := algebraMap K L with hι
  set φ : ↥(adjointGroup τ K) →* ModGL τ L :=
    (baseChangeGL ι).comp (adjointGroup τ K).subtype with hφ
  have hφinj : Function.Injective φ :=
    (baseChangeGL_injective ι).comp Subtype.val_injective
  set AL : Subgroup (ModGL τ L) := E.map φ with hAL
  have hAL_le : AL ≤ adjointGroup τ L := by
    rintro _ ⟨x, -, rfl⟩
    exact CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup ι x.2
  have hALp : ∀ y ∈ AL, y ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE.2 x hx, map_one]
  have hALcard : p ^ (τ.rank - 1) ≤ Nat.card AL := by
    rw [hAL, ← Nat.card_congr (Subgroup.equivMapOfInjective E φ hφinj).toEquiv]
    exact hcard
  have hALcomm : ∀ x ∈ AL, ∀ y ∈ AL, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have hc := hE.1.is_comm
    rw [← map_mul, ← map_mul]
    exact congrArg φ (congrArg Subtype.val (hc.comm ⟨x, hx⟩ ⟨y, hy⟩))
  obtain ⟨g, hgG, hg⟩ := hbar K hpK AL hAL_le hALcomm hALp hALcard
  have hchar : CharP K (ringChar K) := ringChar.charP K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  set ℓ := ringChar K with hℓdef
  have hq : Nat.card K = ℓ ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have he : 1 ≤ (f : ℕ) := f.pos
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective _
  have hpq : Nat.Coprime p (ℓ ^ (f : ℕ)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 (hq ▸ hpK)
  have hT : ∀ x : E, g⁻¹ * φ x * g ∈ torusGroup τ L := fun x => hg _ ⟨x, x.2, rfl⟩
  choose a ha using fun x : E => exists_rootDiagUnit_eq_of_mem_torusGroup (hT x)
  have hexp : ∀ (x : E) i, a x i ^ p = 1 := by
    intro x
    have h1 : rootDiagUnit τ (a x ^ p) = rootDiagUnit τ 1 := by
      have : rootDiagUnit τ (a x ^ p) = rootDiagUnit τ (a x) ^ p :=
        ((rootDiagUnitHom τ L).map_pow (a x) p)
      rw [this, ← ha x, rootDiagUnit_one]
      calc (g⁻¹ * φ x * g) ^ p = g⁻¹ * (φ x) ^ p * g := by
            have := conj_pow (a := g⁻¹) (b := φ x) (i := p)
            rwa [inv_inv] at this
        _ = 1 := by
            rw [← map_pow, hE.2 x x.2, map_one]
            group
    have h2 : a x ^ p = 1 := CFSG.LieType.Chevalley.rootDiagUnit_injective h1
    exact fun i => congrFun h2 i
  have hFix : ∀ y : ModGL τ K,
      entrywiseFrobGL τ L ℓ (f : ℕ) (baseChangeGL ι y) = baseChangeGL ι y := by
    intro y
    have hcomp : (iterateFrobenius L ℓ (f : ℕ)).comp ι = ι := by
      refine RingHom.ext fun c => ?_
      change (iterateFrobenius L ℓ f) (ι c) = ι c
      rw [iterateFrobenius_def, ← map_pow]
      congr 1
      rw [← hf]
      exact FiniteField.pow_card c
    rw [entrywiseFrobGL, CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL,
      CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hcomp]
  have hFix' : ∀ x : E, entrywiseFrobGL τ L ℓ (f : ℕ) (φ x) = φ x := fun x =>
    hFix ((x : adjointGroup τ K) : ModGL τ K)
  have hn : ∀ x : E, (g⁻¹ * entrywiseFrobGL τ L ℓ (f : ℕ) g) *
      entrywiseFrobGL τ L ℓ (f : ℕ) (rootDiagUnit τ (a x)) *
      (g⁻¹ * entrywiseFrobGL τ L ℓ (f : ℕ) g)⁻¹ = rootDiagUnit τ (a x) := by
    intro x
    rw [← ha x, map_mul, map_mul, map_inv, hFix' x]
    group
  obtain ⟨w', z, hz, hlang⟩ := exists_lang_datum_of_plane ℓ (f : ℕ) he hpq a hexp hgG hn
  have hzC := familyGroup_le_familyCentralizer (K := L) a hz
  obtain ⟨hzG, hzcomm⟩ := mem_familyCentralizer.1 hzC
  have hu : entrywiseFrobGL τ L ℓ (f : ℕ) (g * z) =
      (g * z) * canonicalRep (coxeterSystem τ) L w' := inv_mul_eq_iff_eq_mul.1 hlang
  refine ⟨w', iterateFrobenius L ℓ (f : ℕ), fun c => ?_, g * z, mul_mem hgG hzG, hu, ?_⟩
  · rw [iterateFrobenius_def, hq]
  · intro x hx
    set xA : E := ⟨x, hx⟩ with hxA
    set d := rootDiagUnit τ (a xA) with hd
    have hzd : z⁻¹ * d * z = d := by
      have := hzcomm xA
      rw [← hd, mul_inv_eq_iff_eq_mul] at this
      calc z⁻¹ * d * z = z⁻¹ * (d * z) := by group
        _ = z⁻¹ * (z * d) := by rw [this]
        _ = d := by group
    have ht : (g * z)⁻¹ * baseChangeGL ι ((x : adjointGroup τ K) : ModGL τ K) * (g * z) = d := by
      have h0 : φ xA = baseChangeGL ι ((x : adjointGroup τ K) : ModGL τ K) := rfl
      calc (g * z)⁻¹ * baseChangeGL ι ((x : adjointGroup τ K) : ModGL τ K) * (g * z)
          = z⁻¹ * (g⁻¹ * φ xA * g) * z := by rw [h0]; group
        _ = d := by rw [ha xA, hzd]
    refine ⟨(g * z)⁻¹ * baseChangeGL ι ((x : adjointGroup τ K) : ModGL τ K) * (g * z), ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_twistedTorusOf, ht]
      refine ⟨rootDiagUnit_mem_torusGroup _, ?_⟩
      have hfx : entrywiseFrobGL τ L ℓ (f : ℕ)
          (baseChangeGL ι ((x : adjointGroup τ K) : ModGL τ K)) =
          baseChangeGL ι ((x : adjointGroup τ K) : ModGL τ K) := hFix _
      have hFd : entrywiseFrobGL τ L ℓ (f : ℕ) d =
          (canonicalRep (coxeterSystem τ) L w')⁻¹ * d * canonicalRep (coxeterSystem τ) L w' := by
        rw [← ht, map_mul, map_mul, map_inv, hfx, hu]
        group
      change canonicalRep (coxeterSystem τ) L w' * entrywiseFrobGL τ L ℓ (f : ℕ) d *
        (canonicalRep (coxeterSystem τ) L w')⁻¹ = d
      rw [hFd]
      group
    · change (g * z) * ((g * z)⁻¹ * baseChangeGL ι ((x : adjointGroup τ K) : ModGL τ K) *
        (g * z)) * (g * z)⁻¹ = baseChangeGL ι ((x : adjointGroup τ K) : ModGL τ K)
      group

end Lang

end ExcFramesHalf

end CFSG.StandardType
