module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90S4
import CFSG.Quasithin.Recognition.Stroth.BenderNoFF
import CFSG.HardMathSupport.Cooperstein.Proving.SporadicNoIrrFF
import CFSG.Quasithin.EmptyFaithful.S153EB6D
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.OpCoreSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase

private theorem k90ufs_j2_nonabelian :
    ∃ a b : CFSG.Blueprint.NativeSporadic.J2, a * b ≠ b * a := by
  have := CFSG.Sporadic.J2.isSimpleGroup_J2
  by_contra hcon
  have hcomm : ∀ a b : CFSG.Blueprint.NativeSporadic.J2, a * b = b * a := fun a b => by
    by_contra hne
    exact hcon ⟨a, b, hne⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := CFSG.Blueprint.NativeSporadic.J2) 2
    (by rw [CFSG.Sporadic.J2.card_J2]; norm_num)
  have hnorm : (Subgroup.zpowers g).Normal :=
    ⟨fun n hn x => by
      have h1 : x * n * x⁻¹ = n := by rw [hcomm x n, mul_inv_cancel_right]
      rw [h1]
      exact hn⟩
  have := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers g) with hbot | htop
  · have hg1 : g ∈ Subgroup.zpowers g := Subgroup.mem_zpowers g
    rw [hbot, Subgroup.mem_bot] at hg1
    rw [hg1, orderOf_one] at hg
    norm_num at hg
  · have h1 : Nat.card (Subgroup.zpowers g) = Nat.card CFSG.Blueprint.NativeSporadic.J2 := by
      rw [htop, Subgroup.card_top]
    rw [Nat.card_zpowers, hg, CFSG.Sporadic.J2.card_J2] at h1
    norm_num at h1

theorem r890u_not_isFFModule_of_fstar_J2
    {W : Type} [CommGroup W] [Finite W] {H L : Subgroup (MulAut W)} (hW : ∀ w : W, w * w = 1)
    (hLF : L = CFSG.Open.quasithinGenFitting H) (hO2 : CFSG.pCore 2 ↥H = ⊥)
    (hL : Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    ¬ CFSG.Quasithin.IsFFModule H := by
  obtain ⟨e⟩ := hL
  have := CFSG.Sporadic.J2.isSimpleGroup_J2
  have : IsSimpleGroup ↥L := e.isSimpleGroup
  obtain ⟨a, b, hab⟩ := k90ufs_j2_nonabelian
  have hnab : ∃ x y : ↥L, x * y ≠ y * x :=
    ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  obtain ⟨hq, hZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (Q := ↥L) hnab
  obtain ⟨f⟩ := CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv
  exact CFSG.Quasithin.Stroth.not_isFFModule_of_noIrrFFOffender hW hLF hq hO2
    CFSG.HardMathSupport.Cooperstein.Proving.noIrrFFOffender_J2
    ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans (e.trans f))⟩

theorem r890u_nonempty_autI_mulEquiv_J2 {X : Type} [Group X]
    [Finite X] {V L : Subgroup X} (hV : IsElemAbelian 2 V)
    (hLN : L ≤ Subgroup.normalizer (V : Set X))
    (hO2 : pCoreOf 2 (CFSG.Quasithin.autI hV L) = ⊥)
    (hLV : ¬ L ≤ Subgroup.centralizer (V : Set X)) (hJ : IsSpor (Bar2 L) .J2) :
    Nonempty (↥(CFSG.Quasithin.autI hV L) ≃* CFSG.Blueprint.NativeSporadic.J2) := by
  change Nonempty (↥(CFSG.Quasithin.autOn L V) ≃* CFSG.Blueprint.NativeSporadic.J2)
  have hle := CFSG.Quasithin.InternalSec.pCore_le_ker_autOnHom hLN hO2
  set ρ : Bar2 L →* ↥(CFSG.Quasithin.autOn L V) :=
    QuotientGroup.lift (CFSG.pCore 2 ↥L) (CFSG.Quasithin.InternalSec.autOnHom hLN) hle
    with hρ
  have hsurj : Function.Surjective ρ := by
    intro y
    obtain ⟨l, rfl⟩ := CFSG.Quasithin.InternalSec.autOnHom_surjective hLN y
    exact ⟨QuotientGroup.mk l, rfl⟩
  have hker : ρ.ker ≠ ⊤ := by
    intro h
    apply CFSG.Quasithin.InternalSec.ker_autOnHom_ne_top hLN hLV
    rw [eq_top_iff]
    intro l _
    have : (QuotientGroup.mk l : Bar2 L) ∈ ρ.ker := by rw [h]; trivial
    exact this
  obtain ⟨e⟩ := hJ
  have hJ2simple : IsSimpleGroup
      (CFSG.Blueprint.NativeSporadic.Carrier TauCeti.SporadicName.J2) :=
    CFSG.Sporadic.J2.isSimpleGroup_J2
  have hsimple : IsSimpleGroup (Bar2 L) :=
    @MulEquiv.isSimpleGroup (Bar2 L) _
      (CFSG.Blueprint.NativeSporadic.Carrier TauCeti.SporadicName.J2) _ hJ2simple e
  have hbot : ρ.ker = ⊥ := by
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal (Bar2 L) _ hsimple ρ.ker inferInstance with
      h | h
    · exact h
    · exact absurd h hker
  have hinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).1 hbot
  exact ⟨(MulEquiv.ofBijective ρ ⟨hinj, hsurj⟩).symm.trans e⟩

private theorem k90unf_irr_of_map {V : Type*} [CommGroup V] {X : Subgroup (MulAut V)}
    (hirr : ∀ U : Subgroup V, (∀ x ∈ X, U.map (x : MulAut V).toMonoidHom ≤ U) →
      U = ⊥ ∨ U = ⊤) :
    ∀ B : Subgroup V, (∀ k ∈ X, ∀ b ∈ B, k b ∈ B) → B = ⊥ ∨ B = ⊤ := by
  intro B hB
  exact hirr B fun x hx => by
    rintro _ ⟨b, hb, rfl⟩
    simpa using hB x hx b hb

private theorem k90unf_pCoreOf_two_eq_bot {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v * v = 1) {X : Subgroup (MulAut V)}
    (hirr : ∀ U : Subgroup V, (∀ x ∈ X, U.map (x : MulAut V).toMonoidHom ≤ U) →
      U = ⊥ ∨ U = ⊤) :
    pCoreOf 2 X = ⊥ :=
  CFSG.Quasithin.S153EB6.pCoreOf_two_eq_bot_of_irr (G := X) (Kb := X)
    (fun v : V => by rw [pow_two]; exact hV v) (le_refl X) (k90unf_irr_of_map hirr)

private theorem k90unf_conj_mem {V : Type*} [CommGroup V] {X : Subgroup (MulAut V)}
    {S : Subgroup ↥X} (hSn : S.Normal) :
    ∀ y ∈ X, ∀ l ∈ S.map X.subtype, y * l * y⁻¹ ∈ S.map X.subtype := by
  intro y hy l hl
  obtain ⟨s, hs, hsl⟩ := hl
  rw [← hsl]
  refine ⟨⟨y, hy⟩ * s * ⟨y, hy⟩⁻¹, hSn.conj_mem s hs ⟨y, hy⟩, ?_⟩
  simp

private theorem k90unf_pow_two_mem {V : Type*} [CommGroup V] [Finite V] {X : Subgroup (MulAut V)}
    {S : Subgroup ↥X} (hSn : S.Normal) (hidx : S.index ≤ 2) :
    ∀ y ∈ X, ∃ k : ℕ, y ^ 2 ^ k ∈ S.map X.subtype := by
  intro y hy
  have hpow : (⟨y, hy⟩ : ↥X) ^ S.index ∈ S :=
    @Subgroup.pow_index_mem ↥X _ S hSn ⟨y, hy⟩
  have hne : S.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hcases : S.index = 1 ∨ S.index = 2 := by omega
  have hy2 : (⟨y, hy⟩ : ↥X) ^ 2 ∈ S := by
    rcases hcases with h | h
    · rw [Subgroup.index_eq_one] at h
      rw [h]
      exact Subgroup.mem_top _
    · rw [← h]
      exact hpow
  exact ⟨1, ⟨(⟨y, hy⟩ : ↥X) ^ 2, hy2, by simp⟩⟩

theorem j2NoFF_890_holds :
    J2NoFF_890 := by
  intro V _ _ hV X hirr S hSn hS hidx
  have e₁ : ↥S ≃* ↥(S.map X.subtype) :=
    S.equivMapOfInjective X.subtype X.subtype_injective
  obtain ⟨e⟩ := hS
  let eL : ↥(S.map X.subtype) ≃* CFSG.Blueprint.NativeSporadic.J2 := e₁.symm.trans e
  have hnab : ∃ a b : ↥(S.map X.subtype), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := CFSG.Sporadic.SmallOddCore.j2_not_comm
    exact ⟨eL.symm a, eL.symm b, fun h => hab (by
      have := congrArg eL h
      simpa using this)⟩
  have hsimple : IsSimpleGroup ↥(S.map X.subtype) :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J2.isSimpleGroup_J2 eL
  have hLq : CFSG.Open.IsQuasisimple ↥(S.map X.subtype) :=
    CFSG.Quasithin.B1Red.isQuasisimple_to_open
      (@CFSG.LocalCores.isQuasisimple_of_isSimpleGroup _ _ hsimple hnab).1
  have hO2X : pCoreOf 2 X = ⊥ := k90unf_pCoreOf_two_eq_bot hV hirr
  refine r890u_not_isFFModule_of_fstar_J2 (W := V) (H := X) (L := S.map X.subtype)
    hV ?_ ?_ ⟨eL⟩
  · exact (CFSG.Quasithin.C124.quasithinGenFitting_eq_of_two_group_quot
      (Subgroup.map_subtype_le S) (k90unf_conj_mem hSn) (Or.inl hLq)
      (k90unf_pow_two_mem hSn hidx) hO2X).symm
  · have hmap : (CFSG.pCore 2 ↥X).map X.subtype = ⊥ := by
      simpa only [CFSG.Open.pCoreOf] using hO2X
    exact (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).1 hmap

open CFSG.Quasithin CFSG.ASVolI.ChB in
theorem puJ2Offender_890_holds :
    PUJ2Offender_890 := by
  intro _ X _ _ V hV _ R L hR _ hLV _ hJ hO2 hLF heq
  have hNV : Subgroup.normalizer (V : Set X) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr inferInstance
  have hLN : L ≤ Subgroup.normalizer (V : Set X) := by rw [hNV]; exact le_top
  have hVR : V ≤ R := by
    have hVp : V ≤ pCoreOf 2 (⊤ : Subgroup X) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_top
        (by rw [hNV]) (CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian hV)
    exact hVp.trans (CFSG.LocalAnalysis.AGL81TheoremCD.Section12.pCoreOf_le_of_isSylowOf
      (CFSG.ABGLocalTools.isSylowOf_iff.2 hR))
  by_cases hne : (starOffendersR hV R).Nonempty
  · obtain ⟨B, hB⟩ := hne
    obtain ⟨A, ⟨g, hgA⟩, hA1, rfl⟩ := hB
    let A' : Subgroup X := A.map (MulAut.conj g).toMonoidHom
    have hAN : A ≤ Subgroup.normalizer (V : Set X) := by rw [hNV]; exact le_top
    have hA'N : A' ≤ Subgroup.normalizer (V : Set X) := by rw [hNV]; exact le_top
    have hA'1 : autI hV A' ≠ ⊥ := by
      intro hbot
      have hA'C : A' ≤ Subgroup.centralizer (V : Set X) := (autI_eq_bot_iff hV hA'N).1 hbot
      have hAC : A ≤ Subgroup.centralizer (V : Set X) := by
        intro a ha
        have h1 : MulAut.conj g a ∈ A' := Subgroup.mem_map_of_mem _ ha
        have h2 : MulAut.conj g a ∈ Subgroup.centralizer (V : Set X) := hA'C h1
        have h3 := (inferInstance : (Subgroup.centralizer (V : Set X)).Normal).conj_mem'
          (MulAut.conj g a) h2 g
        have h4 : g⁻¹ * MulAut.conj g a * g = a := by
          rw [MulAut.conj_apply]
          group
        exact h4 ▸ h3
      exact hA1 ((autI_eq_bot_iff hV hAN).2 hAC)
    have hFF : IsFFModule (autI hV ⊤) :=
      ((CFSG.ASVolI.as_B_2_4 X V hV R 0 A' hR.2.1 hVR hgA hA'1).1.2 rfl).2
    have hO2' : CFSG.pCore 2 ↥(autI hV ⊤) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ (autI hV ⊤).subtype_injective).1 hO2
    have hO2L : pCoreOf 2 (autI hV L) = ⊥ := by
      refine le_bot_iff.mp ?_
      have hle : pCoreOf 2 (autI hV L) ≤ autI hV ⊤ :=
        (CFSG.LieType.BorelTits.pCoreOf_le 2 (autI hV L)).trans (autI_mono hV le_top)
      have hnorm : autI hV ⊤ ≤
          Subgroup.normalizer (pCoreOf 2 (autI hV L) : Set (MulAut (IntMod V hV))) := by
        have hN1 : autI hV ⊤ ≤
            Subgroup.normalizer (autI hV L : Set (MulAut (IntMod V hV))) := by
          rw [hLF]
          exact CFSG.Quasithin.le_normalizer_quasithinGenFitting _
        exact hN1.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (autI hV L))
      calc pCoreOf 2 (autI hV L) ≤ pCoreOf 2 (autI hV ⊤) :=
            CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hle hnorm
              (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (autI hV L))
        _ = ⊥ := hO2
    have hLJ : Nonempty (↥(autI hV L) ≃* CFSG.Blueprint.NativeSporadic.J2) :=
      r890u_nonempty_autI_mulEquiv_J2 hV hLN hO2L hLV hJ
    exact (r890u_not_isFFModule_of_fstar_J2 (W := IntMod V hV)
      (fun w => by simpa [pow_two] using IntMod.sq_eq_one w) hLF hO2' hLJ) hFF
  · have hempty : starOffendersR hV R = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hbot : ffJP (starOffendersR hV R) (autI hV ⊤) = ⊥ := by
      refine eq_bot_iff.2 (iSup₂_le fun A hA => ?_)
      exact absurd hA (by rw [hempty]; exact Set.notMem_empty A)
    have hbotL : autI hV L = ⊥ := by
      rw [heq, hbot]
      exact le_bot_iff.mp (CFSG.Quasithin.quasithinGenFitting_le ⊥)
    exact hLV ((autI_eq_bot_iff hV hLN).1 hbotL)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
