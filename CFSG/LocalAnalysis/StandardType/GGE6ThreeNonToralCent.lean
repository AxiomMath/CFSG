module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeNonToralWeyl
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeNonToralRegular
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeNonToralCount
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveFrameCentralizer
public import CFSG.Mathlib.RingTheory.UnitOrderOf

public section

namespace CFSG.StandardType.E6NonToralThree

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley TableBExc.Three TableBExc.E6Three

open CFSG.HardMathSupport.Timmesfeld.Torality

private theorem exists_zeta {L : Type} [Field L] [IsAlgClosed L] (hL : ringChar L ≠ 3) :
    ∃ ζ : Lˣ, orderOf ζ = 3 ∧ ζ ^ 3 = 1 := by
  have h3L : (3 : L) ≠ 0 := by
    intro h0
    have h1 : ringChar L ∣ 3 :=
      (CharP.cast_eq_zero_iff L (ringChar L) 3).1 (by exact_mod_cast h0)
    rcases CharP.char_is_prime_or_zero L (ringChar L) with hp | hp
    · exact hL ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h1)
    · rw [hp] at h1
      exact absurd (Nat.eq_zero_of_zero_dvd h1) (by norm_num)
  obtain ⟨ζ, hζo⟩ := CFSG.exists_unit_orderOf_eq_of_isAlgClosed (k := L) (n := 3) h3L
  exact ⟨ζ, hζo, hζo ▸ pow_orderOf_eq_one ζ⟩

private theorem mem_weylImage_iff
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)}
    (hEM : E ≤ monomialSubgroup .E6 L) {w : WeylGroup .E6} :
    w ∈ ((weylQuotientHom .E6 L).comp (Subgroup.inclusion hEM)).range ↔
      ∃ e, ∃ he : e ∈ E, weylQuotientHom .E6 L ⟨e, hEM he⟩ = w := by
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨e, e.2, rfl⟩
  · rintro ⟨e, he, hw⟩
    exact ⟨⟨e, he⟩, hw⟩

private theorem isElemAbelian_weylImage
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)}
    (hEM : E ≤ monomialSubgroup .E6 L) (hE : IsElemAbelian 3 E) :
    IsElemAbelian 3 ((weylQuotientHom .E6 L).comp (Subgroup.inclusion hEM)).range := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨e, he, hae⟩ :=
      (mem_weylImage_iff (hEM := hEM) (w := (a : WeylGroup .E6))).1 a.2
    obtain ⟨e', he', hbe⟩ :=
      (mem_weylImage_iff (hEM := hEM) (w := (b : WeylGroup .E6))).1 b.2
    have hcomm : e * e' = e' * e := hE.comm he he'
    change (a : WeylGroup .E6) * b = (b : WeylGroup .E6) * a
    rw [← hae, ← hbe, ← map_mul, ← map_mul]
    exact congrArg (weylQuotientHom .E6 L) (Subtype.ext hcomm)
  · obtain ⟨e, he, hxe⟩ := (mem_weylImage_iff (hEM := hEM) (w := x)).1 hx
    have h3 : (⟨e, hEM he⟩ : monomialSubgroup .E6 L) ^ 3 = 1 := Subtype.ext (hE.2 e he)
    calc x ^ 3 = (weylQuotientHom .E6 L ⟨e, hEM he⟩) ^ 3 := by rw [← hxe]
      _ = 1 := by
        calc (weylQuotientHom .E6 L ⟨e, hEM he⟩) ^ 3 =
            weylQuotientHom .E6 L ((⟨e, hEM he⟩ : monomialSubgroup .E6 L) ^ 3) :=
              (map_pow (weylQuotientHom .E6 L) ⟨e, hEM he⟩ 3).symm
          _ = weylQuotientHom .E6 L 1 := by rw [h3]
          _ = 1 := map_one _

private theorem weylImage_le_modelRange
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)}
    (hEM : E ≤ monomialSubgroup .E6 L)
    (hAS : ∀ e (he : e ∈ E), weylQuotientHom .E6 L ⟨e, hEM he⟩ ∈ modelHomE6.range) :
    ((weylQuotientHom .E6 L).comp (Subgroup.inclusion hEM)).range ≤ modelHomE6.range := by
  rintro w hw
  obtain ⟨e, he, rfl⟩ := (mem_weylImage_iff (hEM := hEM) (w := w)).1 hw
  exact hAS e he

private theorem weylImage_ne_bot
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)}
    (hEM : E ≤ monomialSubgroup .E6 L) (hET : ¬ E ≤ torusGroup .E6 L) :
    ((weylQuotientHom .E6 L).comp (Subgroup.inclusion hEM)).range ≠ ⊥ := by
  intro hbot
  apply hET
  intro e he
  have hmem : weylQuotientHom .E6 L ⟨e, hEM he⟩ ∈
      ((weylQuotientHom .E6 L).comp (Subgroup.inclusion hEM)).range :=
    (mem_weylImage_iff (hEM := hEM) (w := weylQuotientHom .E6 L ⟨e, hEM he⟩)).2
      ⟨e, he, rfl⟩
  rw [hbot] at hmem
  have h1 : weylQuotientHom .E6 L ⟨e, hEM he⟩ = 1 := Subgroup.mem_bot.1 hmem
  have hker : (⟨e, hEM he⟩ : monomialSubgroup .E6 L) ∈ (weylQuotientHom .E6 L).ker := h1
  rw [CFSG.StandardType.TableBExc.weylQuotientHom_surjective_ker.2,
    Subgroup.mem_subgroupOf] at hker
  exact hker

private theorem weylImage_ne_zpowers
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)}
    (hEM : E ≤ monomialSubgroup .E6 L)
    (hAg : ∀ e (he : e ∈ E) i, weylQuotientHom .E6 L ⟨e, hEM he⟩ ≠ gE6 i) :
    ∀ i, ((weylQuotientHom .E6 L).comp (Subgroup.inclusion hEM)).range ≠
      Subgroup.zpowers (gE6 i) := by
  intro i hAeq
  have hmem : gE6 i ∈ ((weylQuotientHom .E6 L).comp (Subgroup.inclusion hEM)).range := by
    rw [hAeq]
    exact Subgroup.mem_zpowers (gE6 i)
  obtain ⟨e, he, hρ⟩ := (mem_weylImage_iff (hEM := hEM) (w := gE6 i)).1 hmem
  exact hAg e he i hρ

private theorem exists_weylImage
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)}
    (hEM : E ≤ monomialSubgroup .E6 L) (hE : IsElemAbelian 3 E)
    (hET : ¬ E ≤ torusGroup .E6 L)
    (hAS : ∀ e (he : e ∈ E), weylQuotientHom .E6 L ⟨e, hEM he⟩ ∈ modelHomE6.range)
    (hAg : ∀ e (he : e ∈ E) i, weylQuotientHom .E6 L ⟨e, hEM he⟩ ≠ gE6 i) :
    ∃ A : Subgroup (WeylGroup .E6),
      (∀ w, w ∈ A ↔ ∃ e, ∃ he : e ∈ E,
        weylQuotientHom .E6 L ⟨e, hEM he⟩ = w) ∧
      A ≤ modelHomE6.range ∧ IsElemAbelian 3 A ∧ A ≠ ⊥ ∧
      (∀ i, A ≠ Subgroup.zpowers (gE6 i)) := by
  exact ⟨((weylQuotientHom .E6 L).comp (Subgroup.inclusion hEM)).range,
    fun w => mem_weylImage_iff (hEM := hEM) (w := w),
    weylImage_le_modelRange hEM hAS, isElemAbelian_weylImage hEM hE,
    weylImage_ne_bot hEM hET, weylImage_ne_zpowers hEM hAg⟩

private theorem familyKernel_zetaVec_eq_empty
    {L : Type} [Field L] {ζ : Lˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {E : Subgroup (ModGL .E6 L)} (hEM : E ≤ monomialSubgroup .E6 L)
    {A : Subgroup (WeylGroup .E6)}
    (hEA : ∀ w, w ∈ A ↔ ∃ e, ∃ he : e ∈ E,
      weylQuotientHom .E6 L ⟨e, hEM he⟩ = w)
    (hAS : A ≤ modelHomE6.range) (hA : IsElemAbelian 3 A)
    (hAg0 : ∀ e (he : e ∈ E) i, weylQuotientHom .E6 L ⟨e, hEM he⟩ ≠ gE6 i) :
    familyKernel (fun x : {x : Fin Tag.E6.rank → ZMod 3 //
        ∀ a ∈ A, adAct .E6 3 a x = x} => zetaVec ζ hζ x.1) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro α ⟨hαroot, hαchar⟩
  have hgA : ∀ i, gE6 i ∉ A := by
    intro i hi
    obtain ⟨e, he, hρ⟩ := (hEA _).1 hi
    exact hAg0 e he i hρ
  obtain ⟨x, hxfix, hxdot⟩ := exists_fix_dot_ne_zero A hAS hA hgA hαroot
  have hchar1 : rootChar (zetaVec ζ hζ x) α = 1 := hαchar ⟨x, hxfix⟩
  have h1 : CFSG.RankThree.CentralCover.zmodPowHom ζ hζ
      (Multiplicative.ofAdd (∑ j, (α j : ZMod 3) * x j)) = 1 := by
    rw [← NoOffE8Five.rootChar_zetaVec hζ x α]
    exact hchar1
  have h2 : Multiplicative.ofAdd (∑ j, (α j : ZMod 3) * x j) = 1 :=
    CFSG.RankThree.CentralCover.zmodPowHom_injective hζo hζ (h1.trans (map_one _).symm)
  exact hxdot (by simpa using congrArg Multiplicative.toAdd h2)

private theorem adAct_eq_of_mem_familyStabilizer_zetaVec {L : Type} [Field L] {ζ : Lˣ}
    (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) {A : Subgroup (WeylGroup .E6)}
    {w : WeylGroup .E6}
    (hw : w ∈ familyStabilizer (fun x : {x : Fin Tag.E6.rank → ZMod 3 //
        ∀ a ∈ A, adAct .E6 3 a x = x} => zetaVec ζ hζ x.1))
    {x : Fin Tag.E6.rank → ZMod 3} (hx : ∀ a ∈ A, adAct .E6 3 a x = x) :
    adAct .E6 3 w x = x := by
  have htuple : weylTuple w (zetaVec ζ hζ x) = zetaVec ζ hζ x := by
    funext i
    have h1 := (hw ⟨x, hx⟩) (w⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ))
    rw [smul_inv_smul] at h1
    have hsingle : rootChar (zetaVec ζ hζ x) (Pi.single i 1) = zetaVec ζ hζ x i := by
      simpa using rootChar_nsmul_single (zetaVec ζ hζ x) i 1
    exact h1.symm.trans hsingle
  have h2 := weylTuple_zetaVec ζ hζ w x
  rw [htuple] at h2
  exact zetaVec_injective hζo hζ h2.symm

private theorem adAct_eq_of_conj_rootDiagUnit_eq
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)}
    (hEM : E ≤ monomialSubgroup .E6 L)
    {A : Subgroup (WeylGroup .E6)}
    (hEA : ∀ w, w ∈ A ↔ ∃ e, ∃ he : e ∈ E,
      weylQuotientHom .E6 L ⟨e, hEM he⟩ = w)
    {t : ModGL .E6 L} (htE : ∀ e ∈ E, t * e = e * t)
    {u : Fin Tag.E6.rank → Lˣ} (hu : t = rootDiagUnit .E6 u)
    {ζ : Lˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {x : Fin Tag.E6.rank → ZMod 3} (hx : zetaVec ζ hζ x = u) :
    ∀ a ∈ A, adAct .E6 3 a x = x := by
  intro a ha
  obtain ⟨e, he, rfl⟩ := (hEA a).1 ha
  have hconj : e * rootDiagUnit .E6 u * e⁻¹ = rootDiagUnit .E6 u := by
    rw [← hu, ← htE e he]
    group
  have h1 := monomial_conj_rootDiagUnit_weylTuple (hEM he)
    (mapsRootLines_weylQuotientHom ⟨e, hEM he⟩) u
  have h2 : weylTuple (weylQuotientHom .E6 L ⟨e, hEM he⟩) u = u :=
    rootDiagUnit_injective (h1.symm.trans hconj)
  have h3 : weylTuple (weylQuotientHom .E6 L ⟨e, hEM he⟩) (zetaVec ζ hζ x) =
      zetaVec ζ hζ x := by
    rw [hx, h2]
  have h4 : zetaVec ζ hζ (adAct .E6 3 (weylQuotientHom .E6 L ⟨e, hEM he⟩) x) =
      zetaVec ζ hζ x := by
    rw [← weylTuple_zetaVec ζ hζ]
    exact h3
  exact zetaVec_injective hζo hζ h4

private theorem mem_monomialSubgroup_of_eq_mul_canonicalRep
    {L : Type} [Field L] {c m : ModGL .E6 L} {w : WeylGroup .E6}
    (hmT : m ∈ torusGroup .E6 L) (hcm : c = m * canonicalRep (coxeterSystem .E6) L w) :
    c ∈ monomialSubgroup .E6 L := by
  rw [hcm]
  exact mul_mem (torusGroup_le_monomialSubgroup hmT)
    (canonicalRep_mem_monomialSubgroup L w)

private theorem weylQuotientHom_eq_of_eq_mul_canonicalRep
    {L : Type} [Field L] {c m : ModGL .E6 L} {w : WeylGroup .E6}
    (hmT : m ∈ torusGroup .E6 L) (hcm : c = m * canonicalRep (coxeterSystem .E6) L w)
    (hcN : c ∈ monomialSubgroup .E6 L) :
    weylQuotientHom .E6 L ⟨c, hcN⟩ = w := by
  refine weylQuotientHom_eq ?_
  show MapsRootLines c w
  rw [hcm]
  exact mapsRootLines_mul_canonicalRep hmT w

private theorem commute_weylImage_of_commute
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)}
    (hEM : E ≤ monomialSubgroup .E6 L)
    {A : Subgroup (WeylGroup .E6)}
    (hEA : ∀ w, w ∈ A ↔ ∃ e, ∃ he : e ∈ E,
      weylQuotientHom .E6 L ⟨e, hEM he⟩ = w)
    {c : ModGL .E6 L} {w : WeylGroup .E6}
    (hcN : c ∈ monomialSubgroup .E6 L)
    (hρc : weylQuotientHom .E6 L ⟨c, hcN⟩ = w)
    (hcE : ∀ e ∈ E, c * e = e * c) :
    ∀ a ∈ A, w * a = a * w := by
  intro a ha
  obtain ⟨e, he, rfl⟩ := (hEA a).1 ha
  have hce : (⟨c, hcN⟩ : monomialSubgroup .E6 L) * ⟨e, hEM he⟩ =
      ⟨e, hEM he⟩ * ⟨c, hcN⟩ := Subtype.ext (hcE e he)
  have h := congrArg (weylQuotientHom .E6 L) hce
  rw [map_mul, map_mul] at h
  simpa [hρc] using h

private theorem exists_factor_of_commute
    {L : Type} [Field L] {ζ : Lˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {E : Subgroup (ModGL .E6 L)} (hEM : E ≤ monomialSubgroup .E6 L)
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 4)
    {A : Subgroup (WeylGroup .E6)}
    (hEA : ∀ w, w ∈ A ↔ ∃ e, ∃ he : e ∈ E,
      weylQuotientHom .E6 L ⟨e, hEM he⟩ = w)
    (hAS : A ≤ modelHomE6.range) (hA : IsElemAbelian 3 A) (hA1 : A ≠ ⊥)
    (hAg0 : ∀ e (he : e ∈ E) i, weylQuotientHom .E6 L ⟨e, hEM he⟩ ≠ gE6 i)
    (hAg : ∀ i, A ≠ Subgroup.zpowers (gE6 i))
    {c : ModGL .E6 L} (hc : c ∈ adjointGroup .E6 L)
    (hcE : ∀ e ∈ E, c * e = e * c) :
    ∃ w ∈ A, ∃ m ∈ torusGroup .E6 L, ∃ hcN : c ∈ monomialSubgroup .E6 L,
      c = m * canonicalRep (coxeterSystem .E6) L w ∧
      weylQuotientHom .E6 L ⟨c, hcN⟩ = w := by
  classical
  let a : {x : Fin Tag.E6.rank → ZMod 3 // ∀ a ∈ A, adAct .E6 3 a x = x} →
      Fin Tag.E6.rank → Lˣ := fun x => zetaVec ζ hζ x.1
  have hcardE : 3 ^ 4 ≤ Nat.card E := le_of_eq hcard.symm
  have hcardA : Nat.card A * Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
      ∀ a ∈ A, adAct .E6 3 a x = x} = 3 ^ 4 :=
    card_mul_card_fix_eq hζo hEM hE hcardE hEA hAS hA1 hAg
  have hker : familyKernel a = ∅ :=
    familyKernel_zetaVec_eq_empty hζo hζ hEM hEA hAS hA hAg0
  have hcFam : c ∈ familyCentralizer .E6 L a := by
    refine mem_familyCentralizer.2 ⟨hc, fun x => ?_⟩
    have hd : rootDiagUnit .E6 (a x) ∈ E :=
      rootDiagUnit_zetaVec_mem hζo hζ hEM hE hcardE hEA hAS hA1 hAg x.2
    rw [← hcE _ hd]
    group
  obtain ⟨w, hwStab, m, hmFam, hcm⟩ := familyCentralizer_le_mul .E6 L a hcFam
  have hmT : m ∈ torusGroup .E6 L := by
    have hroot : rootSpan .E6 L (∅ : Set (Fin Tag.E6.rank → ℤ)) = ⊥ := by
      simp [rootSpan]
    have h := hmFam
    rw [familyGroup, hker, hroot, sup_bot_eq] at h
    exact h
  have hcN : c ∈ monomialSubgroup .E6 L :=
    mem_monomialSubgroup_of_eq_mul_canonicalRep hmT hcm
  have hρc : weylQuotientHom .E6 L ⟨c, hcN⟩ = w :=
    weylQuotientHom_eq_of_eq_mul_canonicalRep hmT hcm hcN
  have hwx : ∀ x : Fin Tag.E6.rank → ZMod 3,
      (∀ a' ∈ A, adAct .E6 3 a' x = x) → adAct .E6 3 w x = x := by
    intro x hx
    exact adAct_eq_of_mem_familyStabilizer_zetaVec hζo hζ hwStab hx
  have hwA : ∀ a' ∈ A, w * a' = a' * w :=
    commute_weylImage_of_commute hEM hEA hcN hρc hcE
  have hcardA' : 3 ^ 4 ≤ Nat.card A * Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
      ∀ a ∈ A, adAct .E6 3 a x = x} := le_of_eq hcardA.symm
  have hwmem : w ∈ A :=
    mem_of_commute_of_fix A hAS hA hcardA' (fun a' ha' => hwA a' ha') hwx
  exact ⟨w, hwmem, m, hmT, hcN, hcm, hρc⟩

theorem exists_mul_torus_of_commute
    {L : Type} [Field L] [IsAlgClosed L] (hL : ringChar L ≠ 3)
    {E : Subgroup (ModGL .E6 L)} (hEM : E ≤ monomialSubgroup .E6 L) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hET : ¬ E ≤ torusGroup .E6 L)
    (hAS : ∀ e (he : e ∈ E), weylQuotientHom .E6 L ⟨e, hEM he⟩ ∈ modelHomE6.range)
    (hAg : ∀ e (he : e ∈ E) i, weylQuotientHom .E6 L ⟨e, hEM he⟩ ≠ gE6 i)
    {c : ModGL .E6 L} (hc : c ∈ adjointGroup .E6 L) (hcE : ∀ e ∈ E, c * e = e * c) :
    ∃ e ∈ E, ∃ t ∈ torusGroup .E6 L, (∀ e' ∈ E, t * e' = e' * t) ∧ c = e * t := by
  classical
  obtain ⟨ζ, hζo, hζ⟩ := exists_zeta hL
  obtain ⟨A, hEA, hAS', hA, hA1, hAg'⟩ := exists_weylImage hEM hE hET hAS hAg
  obtain ⟨w, hwA, m, hmT, hcN, hcm, hρc⟩ :=
    exists_factor_of_commute hζo hζ hEM hE hcard hEA hAS' hA hA1 hAg hAg' hc hcE
  obtain ⟨e, he, hρe⟩ := (hEA w).1 hwA
  refine ⟨e, he, e⁻¹ * c, ?_, ?_, ?_⟩
  · have htN : e⁻¹ * c ∈ monomialSubgroup .E6 L :=
      mul_mem (inv_mem (hEM he)) hcN
    have hker : (⟨e⁻¹ * c, htN⟩ : monomialSubgroup .E6 L) ∈
        (weylQuotientHom .E6 L).ker := by
      have hmul : (⟨e⁻¹ * c, htN⟩ : monomialSubgroup .E6 L) =
          (⟨e, hEM he⟩ : monomialSubgroup .E6 L)⁻¹ * ⟨c, hcN⟩ := by
        apply Subtype.ext
        rfl
      rw [hmul, MonoidHom.mem_ker, map_mul, map_inv, hρe, hρc, inv_mul_cancel]
    rw [CFSG.StandardType.TableBExc.weylQuotientHom_surjective_ker.2,
      Subgroup.mem_subgroupOf] at hker
    exact hker
  · intro e' he'
    have hcomm : Commute e e' := hE.comm he he'
    have hinv : Commute e⁻¹ e' := hcomm.inv_left
    calc (e⁻¹ * c) * e' = e⁻¹ * (c * e') := by group
      _ = e⁻¹ * (e' * c) := by rw [hcE e' he']
      _ = (e⁻¹ * e') * c := by group
      _ = (e' * e⁻¹) * c := by rw [hinv.eq]
      _ = e' * (e⁻¹ * c) := by group
  · group

theorem mem_of_torus_of_commute
    {L : Type} [Field L] [IsAlgClosed L] (hL : ringChar L ≠ 3)
    {E : Subgroup (ModGL .E6 L)} (hEM : E ≤ monomialSubgroup .E6 L) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hET : ¬ E ≤ torusGroup .E6 L)
    (hAS : ∀ e (he : e ∈ E), weylQuotientHom .E6 L ⟨e, hEM he⟩ ∈ modelHomE6.range)
    (hAg : ∀ e (he : e ∈ E) i, weylQuotientHom .E6 L ⟨e, hEM he⟩ ≠ gE6 i)
    {t : ModGL .E6 L} (ht : t ∈ torusGroup .E6 L) (htE : ∀ e ∈ E, t * e = e * t)
    (ht3 : t ^ 3 = 1) : t ∈ E := by
  classical
  obtain ⟨ζ, hζo, hζ⟩ := exists_zeta hL
  obtain ⟨A, hEA, hAS', hA, hA1, hAg'⟩ := exists_weylImage hEM hE hET hAS hAg
  obtain ⟨u, hu⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have hu3 : u ^ 3 = 1 := by
    apply rootDiagUnit_injective (τ := .E6) (K := L)
    calc rootDiagUnit .E6 (u ^ 3) = rootDiagUnit .E6 u ^ 3 := (rootDiagUnit_pow u 3).symm
      _ = t ^ 3 := by rw [hu]
      _ = 1 := ht3
      _ = rootDiagUnit .E6 (1 : Fin Tag.E6.rank → Lˣ) := rootDiagUnit_one.symm
  obtain ⟨x, hx⟩ := exists_zetaVec_eq hζo hζ hu3
  have hfix : ∀ a ∈ A, adAct .E6 3 a x = x :=
    adAct_eq_of_conj_rootDiagUnit_eq hEM hEA htE hu hζo hζ hx
  have hmem : rootDiagUnit .E6 (zetaVec ζ hζ x) ∈ E :=
    rootDiagUnit_zetaVec_mem hζo hζ hEM hE (le_of_eq hcard.symm) hEA hAS' hA1 hAg' hfix
  rwa [hx, ← hu] at hmem

end CFSG.StandardType.E6NonToralThree
