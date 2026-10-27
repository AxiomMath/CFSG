module

public import CFSG.RankThree.PartTwo.Sec15.Item153Twin2ProofTypes
import CFSG.RankThree.PartTwo.Sec14.Item148PtRes2ProofInner
import CFSG.RankThree.PartTwo.Sec14.Item148ProofLift
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofRead
import CFSG.RankThree.PartTwo.Sec18.Components
import CFSG.RankThree.PartTwo.Late.GammaZero
public import CFSG.RankThree.PartTwo.Sec13.Item136PGL
public import CFSG.RankThree.PartTwo.Sec13.Item13Models

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.RankThree.PartTwo.Sec4 (slPi glPi PiField ModThree)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open scoped commutatorElement

namespace Proof153Twin3

section Faithful

variable {G : Type} [Group G] [Finite G]

theorem hasFaithfulE9_of_quot_pPrimeCore {Y : Subgroup G} {T : Type*} [Group T]
    (φ : ↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* T) (hZ : Subgroup.center T = ⊥)
    (hE : ∃ E : Subgroup T, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9) :
    HasFaithfulE9 Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZQ : Subgroup.center (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) = ⊥ := by
    have hmap := Subgroup.map_center_eq φ
    rw [hZ] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp hmap
  obtain ⟨E', hE', h9'⟩ := exists_e9_of_mulEquiv φ hE
  have hP3 : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥Y) := fun h =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card h
  have h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y)) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_top hE' (by rw [h9']; norm_num)
  rw [CFSG.SectionRank.pRank_quotient_eq _ hP3] at h2
  obtain ⟨E₀, -, hE₀, hcard⟩ := Late.exists_elemAbelian_le_of_le_pRank_three h2
  refine ⟨E₀.map Y.subtype, Subgroup.map_subtype_le _,
    CFSG.SectionRank.isElemAbelian_map hE₀ _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective Y.subtype_injective, hcard]
    norm_num
  obtain ⟨-, hθc, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥Y) Nat.prime_three
  have : (aschbacherSolvableCore 3 ↥Y).Normal := Subgroup.normal_of_characteristic _
  have hθle : aschbacherSolvableCore 3 ↥Y ≤ CFSG.pPrimeCore 3 ↥Y :=
    le_sSup ⟨inferInstance, (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3⟩
  rintro e ⟨he, hc⟩
  obtain ⟨ê, hê, rfl⟩ := he
  have hcen : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y) ê ∈
      Subgroup.center (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥Y) g
    have h1 : ⁅ê, y⁆ ∈ CFSG.pPrimeCore 3 ↥Y := by
      obtain ⟨w, hw, hweq⟩ := hc y y.2
      have hw' : w = ⁅ê, y⁆ := by
        apply Subtype.ext
        rw [commutatorElement_def]
        exact hweq
      exact hθle (hw' ▸ hw)
    have h2 : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y) ⁅ê, y⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr h1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2.symm
  rw [hZQ, Subgroup.mem_bot] at hcen
  have hêP : ê ∈ CFSG.pPrimeCore 3 ↥Y := (QuotientGroup.eq_one_iff _).mp hcen
  have hê1 : ê = 1 := eq_one_of_mem_of_pow_three hP3 hêP (hE₀.2 ê hê)
  rw [hê1]
  rfl

end Faithful

section Abstract

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem center_eq_bot_of_mulEquiv {X T : Type*} [Group X] [Group T] (e : X ≃* T)
    (hT : Subgroup.center T = ⊥) : Subgroup.center X = ⊥ := by
  refine Subgroup.eq_bot_of_card_eq _ ?_
  rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, hT, Subgroup.card_bot]

theorem le_or_le_of_isQuasisimple {D J₁ J₂ : Subgroup Γ} (hJ : J₁ ⊔ J₂ = D)
    (hc : ⁅J₁, J₂⁆ = ⊥) {U : Subgroup ↥D} (hU : U.IsSubnormal) (hUq : IsQuasisimple ↥U) :
    U.map D.subtype ≤ J₁ ∨ U.map D.subtype ≤ J₂ := by
  have hJ₁D : J₁ ≤ D := hJ ▸ le_sup_left
  have hJ₂D : J₂ ≤ D := hJ ▸ le_sup_right
  have hJ₂J₁ : J₂ ≤ Subgroup.centralizer (J₁ : Set Γ) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hc
  have hJ₁J₂ : J₁ ≤ Subgroup.centralizer (J₂ : Set Γ) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hc
  have hn₁ : (J₁.subgroupOf D).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hJ₁D, ← hJ]
    exact sup_le Subgroup.le_normalizer (hJ₂J₁.trans (Subgroup.centralizer_le_normalizer _))
  have hn₂ : (J₂.subgroupOf D).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hJ₂D, ← hJ]
    exact sup_le (hJ₁J₂.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  have hK : IsComponent U := ⟨hUq, hU⟩
  have hmap : ∀ {J : Subgroup Γ}, U ≤ J.subgroupOf D → U.map D.subtype ≤ J := fun h =>
    (Subgroup.map_mono h).trans (by rw [Subgroup.subgroupOf_map_subtype]; exact inf_le_left)
  rcases CFSG.LocalCores.component_normal_subgroup hK hn₁ with h₁ | h₁
  · exact Or.inl (hmap h₁)
  rcases CFSG.LocalCores.component_normal_subgroup hK hn₂ with h₂ | h₂
  · exact Or.inr (hmap h₂)
  exfalso
  have hc₁ : J₁.subgroupOf D ≤ Subgroup.centralizer (U : Set ↥D) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact h₁
  have hc₂ : J₂.subgroupOf D ≤ Subgroup.centralizer (U : Set ↥D) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact h₂
  have htop : J₁.subgroupOf D ⊔ J₂.subgroupOf D = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hJ₁D hJ₂D, hJ, Subgroup.subgroupOf_self]
  have hcen : U ≤ Subgroup.center ↥D := by
    intro u hu
    rw [Subgroup.mem_center_iff]
    intro x
    have hx : x ∈ Subgroup.centralizer (U : Set ↥D) :=
      (sup_le hc₁ hc₂) (htop ▸ Subgroup.mem_top x)
    exact (Subgroup.mem_centralizer_iff.mp hx u hu).symm
  have hU1 := Proof153Twin2.eq_bot_of_isPerfect_of_le_center hUq.1 hcen
  have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hUq
  obtain ⟨x, hx⟩ := exists_ne (1 : ↥U)
  apply hx
  have hx' : (x : ↥D) ∈ (⊥ : Subgroup ↥D) := hU1 ▸ x.2
  exact Subtype.ext ((Subgroup.mem_bot).mp hx')

omit [Finite Γ] in
theorem center_eq_bot_and_e9_of_le_factor {D B J : Subgroup Γ} (hBc : IsMulCommutative B)
    (hBD : B ≤ Subgroup.normalizer (D : Set Γ)) (hJD : J ≤ D) {p f : ℕ}
    (hP : IsZ3PGLThreeAt ↥(J ⊔ B) p f) {U : Subgroup ↥D} (hU : U.IsSubnormal)
    (hUq : IsQuasisimple ↥U) (hUJ : U.map D.subtype ≤ J) :
    Subgroup.center ↥U = ⊥ ∧
      ∃ E : Subgroup ↥U, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨π, K, _, hK, hq, ⟨φ⟩⟩ := hP
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  set P := J ⊔ B with hPdef
  set Q := projImage (glPi π 3 (p ^ f) K) with hQ
  set S := projImage (slPi π 3 (p ^ f) K) with hS
  have hSQ : S ≤ Q := Subgroup.map_mono (Sec4.slPi_le_glPi hπ)
  set U' := U.map D.subtype with hU'
  set eU : ↥U ≃* ↥U' := Subgroup.equivMapOfInjective U D.subtype D.subtype_injective with heU
  have hU'q : IsQuasisimple ↥U' := CFSG.LocalCores.isQuasisimple_of_mulEquiv eU hUq
  have hU'p : ⁅U', U'⁆ = U' := Subgroup.isPerfect_iff.mp hU'q.1
  have hU'D : U'.subgroupOf D = U :=
    Subgroup.comap_map_eq_self_of_injective D.subtype_injective U
  have hU'sn : (U'.subgroupOf D).IsSubnormal := hU'D ▸ hU
  set σ : ↥P →* ↥Q := (MonoidHom.snd _ _).comp φ.toMonoidHom with hσ
  have hσs : Function.Surjective σ := fun y => ⟨φ.symm (1, y), by simp [hσ]⟩
  set C : Subgroup ↥P := commutator ↥P with hC
  have hC1 : ∀ x ∈ C, (φ x).1 = 1 := fun x hx =>
    (Abelianization.commutator_subset_ker ((MonoidHom.fst _ _).comp φ.toMonoidHom)) hx
  have hσinj : ∀ x ∈ C, σ x = 1 → x = 1 := by
    intro x hx h1
    have h2 : φ x = 1 := Prod.ext (hC1 x hx) h1
    exact φ.injective (h2.trans φ.map_one.symm)
  have hσC : C.map σ = commutator ↥Q := by
    rw [hC, commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective σ hσs]
  set Cg := C.map P.subtype with hCg
  have hPtop : (⊤ : Subgroup ↥P).map P.subtype = P := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hCgP : Cg = ⁅P, P⁆ := by
    rw [hCg, hC, commutator_def, Subgroup.map_commutator, hPtop]
  have hCgD : Cg ≤ D := by
    rw [hCgP]
    have hPDB : P ≤ D ⊔ B := sup_le_sup_right hJD B
    exact (Subgroup.commutator_mono hPDB hPDB).trans
      (commutator_sup_le_of_le_normalizer hBc hBD)
  have hU'Cg : U' ≤ Cg := by
    rw [hCgP, ← hU'p]
    have hU'P : U' ≤ P := hUJ.trans le_sup_left
    exact Subgroup.commutator_mono hU'P hU'P
  have hQQ : ⁅Q, Q⁆ ≤ S := Item148PtRes2.commutator_projImage_glPi_le hπ
  have hQtop : (⊤ : Subgroup ↥Q).map Q.subtype = Q := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hcomQ : (commutator ↥Q).map Q.subtype = ⁅Q, Q⁆ := by
    rw [commutator_def, Subgroup.map_commutator, hQtop]
  set ι₀ : ↥C →* Matrix.ProjGenLinGroup (Fin 3) K := Q.subtype.comp (σ.comp C.subtype)
    with hι₀
  have hι₀S : ∀ x : ↥C, ι₀ x ∈ S := by
    intro x
    have h1 : σ x ∈ commutator ↥Q := hσC ▸ Subgroup.mem_map_of_mem σ x.2
    exact hQQ (hcomQ ▸ Subgroup.mem_map_of_mem Q.subtype h1)
  set ι : ↥C →* ↥S := ι₀.codRestrict S hι₀S with hι
  have hιinj : Function.Injective ι := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : ι₀ x = 1 := congrArg Subtype.val hx
    have h2 : σ x = 1 := Subtype.ext h1
    exact (Subgroup.mem_bot).mpr (Subtype.ext (hσinj x x.2 h2))
  set eC : ↥C ≃* ↥Cg := Subgroup.equivMapOfInjective C P.subtype P.subtype_injective with heC
  rcases Item148PtRes2.solvable_or_simple hK hq with hsol | ⟨hq2, hsimp⟩
  ·
    exfalso
    have hCs : Group.IsSolvable ↥C := Group.isSolvable_of_isSolvable_injective hιinj
    have hCgs : Group.IsSolvable ↥Cg :=
      Group.isSolvable_of_isSolvable_injective (f := eC.symm.toMonoidHom) eC.symm.injective
    have hU's : Group.IsSolvable ↥U' :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hU'Cg)
    have : Nontrivial ↥U' := CFSG.LocalCores.isQuasisimple_nontrivial hU'q
    have : Group.IsPerfect ↥U' := hU'q.1
    exact Group.IsPerfect.not_isSolvable ↥U' hU's
  ·
    have hιsurj : Function.Surjective ι := by
      intro s
      have hs : (⟨s, hSQ s.2⟩ : ↥Q) ∈ commutator ↥Q := by
        rw [Sec13.commutator_projImage_glPi hK hq2, Subgroup.mem_subgroupOf]
        exact s.2
      rw [← hσC] at hs
      obtain ⟨x, hx, hxs⟩ := hs
      refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
      change ((σ x : ↥Q) : Matrix.ProjGenLinGroup (Fin 3) K) = s
      rw [hxs]
    set eS : ↥Cg ≃* ↥S := eC.symm.trans (MulEquiv.ofBijective ι ⟨hιinj, hιsurj⟩) with heS
    have : IsSimpleGroup ↥Cg := eS.isSimpleGroup
    have hsn : (U'.subgroupOf Cg).IsSubnormal := Sec18.isSubnormal_subgroupOf_of_le hU'sn hCgD
    have hU'eq : U' = Cg := by
      rcases hsn.eq_bot_or_top_of_isSimpleGroup inferInstance with hb | ht
      · exfalso
        have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hU'q
        obtain ⟨x, hx⟩ := exists_ne (1 : ↥U')
        apply hx
        have hx' : (⟨x, hU'Cg x.2⟩ : ↥Cg) ∈ U'.subgroupOf Cg := Subgroup.mem_subgroupOf.mpr x.2
        rw [hb, Subgroup.mem_bot] at hx'
        have h1 := congrArg Subtype.val hx'
        exact Subtype.ext h1
      · refine le_antisymm hU'Cg fun x hx => ?_
        have hx' : (⟨x, hx⟩ : ↥Cg) ∈ U'.subgroupOf Cg := ht ▸ Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.mp hx'
    set e : ↥U ≃* ↥S := (eU.trans (MulEquiv.subgroupCongr hU'eq)).trans eS with he
    exact ⟨center_eq_bot_of_mulEquiv e (Sec13.center_projImage_slPi hK hq hq2),
      exists_e9_of_mulEquiv e (Sec13.exists_elemAbelian_nine_projImage_slPi hK hq)⟩

end Abstract

end Proof153Twin3

open Proof153Twin3

theorem claim153TwinCase7_of (h149 : Sec16.Item149S14) (h152 : Item152R) :
    Claim153TwinCase7 := by
  intro G _ _ A c L hR Y hY hE M hM hMY hAN
  rintro ⟨a₁, a₂, L₁, L₂, J₁, J₂, p₁, f₁, e₁, p₂, f₂, e₂, _, _, -, -, -, -, hJ₁, hJ₂, hsup, -,
    hcomm, -, -, -, -, hP₁, hP₂, -, -⟩
  have h := hR.toSec14Std
  let := ker148_normal hAN
  obtain ⟨U, -, hU, -, -, -, -, -, -, -, ⟨eY⟩⟩ :=
    Proof153Twin2.exists_pair_of_twin h (h149 G A c L h) (h152 G A c L hR) hY hM hMY hAN
  have hUq : IsQuasisimple ↥U := CFSG.LocalCores.isQuasisimple_of_mulEquiv eY
    (Proof1515.isQuasisimple_quot_pPrimeCore hY.prop.1)
  have hAab : IsMulCommutative ↥A := h.isElemAbelian.1
  have hBc : IsMulCommutative ↥(img148 A M A) := ⟨⟨fun x y => img148_comm hAab x y⟩⟩
  have hBD : img148 A M A ≤
      Subgroup.normalizer (img148 A M (deltaZero A (lB A) M) : Set _) :=
    Sec14.img148_le_normalizer (Sec16.le_normalizer_deltaZero (A := A) (LB := lB A) M)
  have hJ₁M : J₁ ≤ M ⊔ A := hJ₁.trans (inf_le_right.trans le_sup_left)
  have hJ₂M : J₂ ≤ M ⊔ A := hJ₂.trans (inf_le_right.trans le_sup_left)
  rw [img148_sup hJ₁M le_sup_right] at hP₁
  rw [img148_sup hJ₂M le_sup_right] at hP₂
  have hJ₁D : img148 A M J₁ ≤ img148 A M (deltaZero A (lB A) M) := hsup ▸ le_sup_left
  have hJ₂D : img148 A M J₂ ≤ img148 A M (deltaZero A (lB A) M) := hsup ▸ le_sup_right
  obtain ⟨hZ, hE9⟩ : Subgroup.center ↥U = ⊥ ∧
      ∃ E : Subgroup ↥U, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
    rcases le_or_le_of_isQuasisimple hsup hcomm hU hUq with h1 | h2
    · exact center_eq_bot_and_e9_of_le_factor hBc hBD hJ₁D hP₁ hU hUq h1
    · exact center_eq_bot_and_e9_of_le_factor hBc hBD hJ₂D hP₂ hU hUq h2
  exact hE (hasFaithfulE9_of_quot_pPrimeCore eY hZ hE9)

end CFSG.RankThree.PartTwo.Sec15
