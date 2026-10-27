module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiveA6Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.AltLocal17A6
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.VZeroSmallPermuting
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFifteenOuter
public import CFSG.Quasithin.EmptyFaithful.S152He16C
import CFSG.GroupTheory.PerfectCoreSup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pCore_three_le_center_bar2_of_calC {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    (hshape : Nonempty (BarO2Z17 L ≃* alternatingGroup (Fin 6))) :
    CFSG.pCore 3 (Bar2 L) ≤ Subgroup.center (Bar2 L) := by
  have hq : CFSG.IsQuasisimple (Bar2 L) :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hL.2.2
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq
    (CFSG.pCore_normal (p := 3) (G := Bar2 L)) with htop | hle
  · exfalso
    have h3 : IsPGroup 3 (Bar2 L) := by
      have h := CFSG.pCore_isPGroup (p := 3) (G := Bar2 L)
      rw [htop] at h
      exact h.of_equiv Subgroup.topEquiv
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h3
    have h2 : 2 ∣ Nat.card (Bar2 L) := by
      have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
        (Subgroup.center (Bar2 L))
      obtain ⟨e1⟩ := barO2Z17_equiv_barInf hL
      obtain ⟨e2⟩ := uc22p21k_barInf_equiv_of_calC hL
      obtain ⟨e3⟩ := hshape
      have h360 : Nat.card (BarO2Z17 L) = 360 := by
        rw [Nat.card_congr e3.toEquiv,
          CFSG.Alternating.Multipliers.nat_card_alternatingGroup_fin 4]
        norm_num
      rw [← Nat.card_congr (e1.trans e2).toEquiv, h360] at hcard
      rw [hcard]
      exact dvd_mul_of_dvd_left (by norm_num : 2 ∣ 360) _
    rw [hk] at h2
    exact absurd (Nat.prime_two.dvd_of_dvd_pow h2) (by norm_num)
  · exact hle

theorem mem_oTwoThreeIn_iff_mem_pCore_three {L : Subgroup G} {y : G} (hy : y ∈ L) :
    y ∈ CFSG.Quasithin.oTwoThreeIn L ↔
      (QuotientGroup.mk ⟨y, hy⟩ : Bar2 L) ∈ CFSG.pCore 3 (Bar2 L) := by
  change y ∈ CFSG.Quasithin.preimageModTwoCore L (CFSG.pCore 3 (Bar2 L)) ↔
    (QuotientGroup.mk ⟨y, hy⟩ : Bar2 L) ∈ CFSG.pCore 3 (Bar2 L)
  rw [CFSG.Quasithin.He16.mem_preimageModTwoCore]
  exact ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩

theorem centSection_oTwoThreeIn_eq_of_calC {D : Data G} {L N : Subgroup G} (hL : L ∈ calC D.M)
    (hshape : Nonempty (BarO2Z17 L ≃* alternatingGroup (Fin 6))) :
    centSection N L (CFSG.Quasithin.oTwoThreeIn L) = centSection N L (CFSG.Open.pCoreOf 2 L) := by
  have ho23le : CFSG.Quasithin.oTwoThreeIn L ≤ L := by
    change CFSG.Quasithin.preimageModTwoCore L (CFSG.pCore 3 (Bar2 L)) ≤ L
    exact Subgroup.map_subtype_le _
  have hPleZ : CFSG.pCore 3 (Bar2 L) ≤ Subgroup.center (Bar2 L) :=
    pCore_three_le_center_bar2_of_calC hL hshape
  have hperf : commutator (Bar2 L) = ⊤ := hL.2.2.1
  have hO2le : CFSG.Open.pCoreOf 2 L ≤ CFSG.Quasithin.oTwoThreeIn L := by
    intro y hy
    have hyL : y ∈ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L hy
    refine (mem_oTwoThreeIn_iff_mem_pCore_three hyL).mpr ?_
    have h1 : ((⟨y, hyL⟩ : ↥L) : Bar2 L) = 1 := by
      rw [QuotientGroup.eq_one_iff]
      exact (Subgroup.mem_map_iff_mem L.subtype_injective).mp hy
    rw [h1]
    exact (CFSG.pCore 3 (Bar2 L)).one_mem
  apply le_antisymm
  · intro x hx
    obtain ⟨hxN, hxNL, -, hxcomm⟩ := hx
    have hxinf : x ∈ N ⊓ normalizer (L : Set G) := Subgroup.mem_inf.mpr ⟨hxN, hxNL⟩
    refine (autBar2_eq_one_iff (L := L) (N := N) ⟨x, hxinf⟩).mp ?_
    have hcent : ∀ q : Bar2 L,
        autBar2 (L := L) (N := N) ⟨x, hxinf⟩ q * q⁻¹ ∈
          Subgroup.center (Bar2 L) := by
      intro q
      obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
      have happly := autBar2_apply_mk_coe (L := L) (N := N) ⟨x, hxinf⟩ v
      rw [happly]
      have hxyL : x * (v : G) * x⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp hxNL (v : G)).mp v.2
      have hmem : x * (v : G) * x⁻¹ * (v : G)⁻¹ ∈ CFSG.Quasithin.oTwoThreeIn L :=
        hxcomm (v : G) v.2
      have hmemP : ((⟨x * (v : G) * x⁻¹ * (v : G)⁻¹, ho23le hmem⟩ : ↥L) : Bar2 L) ∈
          CFSG.pCore 3 (Bar2 L) :=
        (mem_oTwoThreeIn_iff_mem_pCore_three (ho23le hmem)).mp hmem
      have hfirst : ((Subgroup.normalizerMonoidHom L
          (Subgroup.inclusion inf_le_right ⟨x, hxinf⟩) v : ↥L) : Bar2 L) =
          ((⟨x * (v : G) * x⁻¹, hxyL⟩ : ↥L) : Bar2 L) := by
        exact congrArg (fun w : ↥L => (w : Bar2 L))
          (Subtype.ext (Subgroup.normalizerMonoidHom_apply_apply_coe L _ v))
      have heq : ((Subgroup.normalizerMonoidHom L
            (Subgroup.inclusion inf_le_right ⟨x, hxinf⟩) v : ↥L) : Bar2 L) *
          (((v : ↥L)) : Bar2 L)⁻¹ =
          ((⟨x * (v : G) * x⁻¹ * (v : G)⁻¹, ho23le hmem⟩ : ↥L) : Bar2 L) := by
        rw [hfirst]
        change (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨x * (v : G) * x⁻¹, hxyL⟩) *
            (QuotientGroup.mk' (CFSG.pCore 2 ↥L) v)⁻¹ =
          (QuotientGroup.mk' (CFSG.pCore 2 ↥L)
            ⟨x * (v : G) * x⁻¹ * (v : G)⁻¹, ho23le hmem⟩)
        rw [← map_inv, ← map_mul]
        rfl
      rw [heq]
      exact hPleZ hmemP
    have hker : CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot (Bar2 L)
        (autBar2 (L := L) (N := N) ⟨x, hxinf⟩) = 1 := by
      ext q
      obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (Bar2 L)) q
      change CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot (Bar2 L)
          (autBar2 (L := L) (N := N) ⟨x, hxinf⟩) (QuotientGroup.mk v) =
        (QuotientGroup.mk v)
      rw [CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot_mk]
      exact QuotientGroup.eq_iff_div_mem.mpr (by simpa [div_eq_mul_inv] using hcent v)
    have hker1 : CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot (Bar2 L)
        (autBar2 (L := L) (N := N) ⟨x, hxinf⟩) =
        CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot (Bar2 L) 1 := by
      rw [map_one]
      exact hker
    exact CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot_injective_of_perfect
      hperf hker1
  · intro x hx
    obtain ⟨hxN, hxNL, -, hxcomm⟩ := hx
    refine ⟨hxN, hxNL, ?_, ?_⟩
    · have hxinf : x ∈ N ⊓ normalizer (L : Set G) := Subgroup.mem_inf.mpr ⟨hxN, hxNL⟩
      let x' : ↥(N ⊓ normalizer (L : Set G)) := ⟨x, hxinf⟩
      let β : MulAut (Bar2 L) := autBar2 (L := L) (N := N) x'
      have hβ : (CFSG.pCore 3 (Bar2 L)).map β.toMonoidHom = CFSG.pCore 3 (Bar2 L) :=
        Subgroup.characteristic_iff_map_eq.mp
          (inferInstance : (CFSG.pCore 3 (Bar2 L)).Characteristic) β
      have hmap : ∀ v : ↥L, β ((v : ↥L) : Bar2 L) =
          ((⟨x * (v : G) * x⁻¹,
            (Subgroup.mem_normalizer_iff.mp hxNL (v : G)).mp v.2⟩ : ↥L) : Bar2 L) := by
        intro v
        have happly := autBar2_apply_mk_coe (L := L) (N := N) x' v
        rw [show β = autBar2 (L := L) (N := N) x' from rfl, happly]
        exact congrArg (fun w : ↥L => (w : Bar2 L))
          (Subtype.ext (Subgroup.normalizerMonoidHom_apply_apply_coe L _ v))
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        have hyL : y ∈ L := ho23le hy
        have hmemP : ((⟨y, hyL⟩ : ↥L) : Bar2 L) ∈ CFSG.pCore 3 (Bar2 L) :=
          (mem_oTwoThreeIn_iff_mem_pCore_three hyL).mp hy
        have hxyL : x * y * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hxNL y).mp hyL
        have hmem : β ((⟨y, hyL⟩ : ↥L) : Bar2 L) ∈
            (CFSG.pCore 3 (Bar2 L)).map β.toMonoidHom :=
          Subgroup.mem_map_of_mem β.toMonoidHom hmemP
        rw [hβ, hmap ⟨y, hyL⟩] at hmem
        exact (mem_oTwoThreeIn_iff_mem_pCore_three hxyL).mpr hmem
      · intro hy
        have hxyL : x * y * x⁻¹ ∈ L := ho23le hy
        have hyL : y ∈ L := (Subgroup.mem_normalizer_iff.mp hxNL y).mpr hxyL
        have hmemP : ((⟨x * y * x⁻¹, hxyL⟩ : ↥L) : Bar2 L) ∈
            CFSG.pCore 3 (Bar2 L) :=
          (mem_oTwoThreeIn_iff_mem_pCore_three hxyL).mp hy
        have hmem : β ((⟨y, hyL⟩ : ↥L) : Bar2 L) ∈
            (CFSG.pCore 3 (Bar2 L)).map β.toMonoidHom := by
          rw [hmap ⟨y, hyL⟩, hβ]
          exact hmemP
        have hpre : β.symm (β ((⟨y, hyL⟩ : ↥L) : Bar2 L)) ∈
            CFSG.pCore 3 (Bar2 L) :=
          (Subgroup.mem_map_equiv (f := β) (K := CFSG.pCore 3 (Bar2 L))).mp hmem
        exact (mem_oTwoThreeIn_iff_mem_pCore_three hyL).mpr (by simpa using hpre)
    · intro a ha
      exact hO2le (hxcomm a ha)

theorem exists_aut_A6_of_not_expFour {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    (hshape : Nonempty (BarO2Z17 L ≃* alternatingGroup (Fin 6)))
    (hK : Inputs1719.K_A6AutOrder8) (hexp : ¬ ExpFourAut17 D L) :
    ∃ (A : Type) (_ : Group A) (φ : ↥((L ⊔ D.T) ⊓ Subgroup.normalizer (L : Set G)) →* A),
      Function.Surjective φ ∧
      (∀ x : ↥((L ⊔ D.T) ⊓ Subgroup.normalizer (L : Set G)),
        φ x = 1 ↔ (x : G) ∈ centSection (L ⊔ D.T) L (CFSG.Quasithin.oTwoThreeIn L)) ∧
      (CFSG.Quasithin.F6.IsPGL2 7 A ∨ Inputs1719.IsAutOf A (alternatingGroup (Fin 6)) ∨
        Inputs1719.IsM10 A ∨ CFSG.Quasithin.F6.IsPGL2 9 A) := by
  classical
  let N : Subgroup G := L ⊔ D.T
  let K : Subgroup G := N ⊓ Subgroup.normalizer (L : Set G)
  let ψ : ↥K →* MulAut (Bar2 L) := autBar2 (L := L) (N := N)
  let A : Type := ↥ψ.range
  let φ : ↥K →* A := ψ.rangeRestrict
  have hLN : L ≤ K := le_inf le_sup_left Subgroup.le_normalizer
  let ψL : ↥L →* A := φ.comp (Subgroup.inclusion hLN)
  let L₀ : Subgroup A := ψL.range
  have hφsurj : Function.Surjective φ := MonoidHom.rangeRestrict_surjective ψ
  have hφcoe : ∀ x : ↥K, ((φ x : A) : MulAut (Bar2 L)) = ψ x := fun x => rfl
  have hperf : commutator (Bar2 L) = ⊤ := hL.2.2.1
  have hφker : ∀ x : ↥K,
      φ x = 1 ↔ (x : G) ∈ centSection N L (CFSG.Quasithin.oTwoThreeIn L) := by
    intro x
    have hcoe1 : φ x = 1 ↔ ψ x = 1 := by
      constructor
      · intro h
        have := congrArg (fun a : A => (a : MulAut (Bar2 L))) h
        simpa [hφcoe] using this
      · intro h
        apply Subtype.ext
        simpa [hφcoe] using h
    rw [hcoe1, autBar2_eq_one_iff, centSection_oTwoThreeIn_eq_of_calC hL hshape]
  have hinnerL : ∀ v : ↥L, (ψL v : MulAut (Bar2 L)) =
      MulAut.conj ((v : ↥L) : Bar2 L) := by
    intro v
    ext y
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective y
    change autBar2 (L := L) (N := N) (Subgroup.inclusion hLN v) ((w : ↥L) : Bar2 L) =
      MulAut.conj ((v : ↥L) : Bar2 L) ((w : ↥L) : Bar2 L)
    rw [autBar2_apply_mk_coe, MulAut.conj_apply]
    have hval : (Subgroup.normalizerMonoidHom L
        (Subgroup.inclusion inf_le_right (Subgroup.inclusion hLN v)) w : ↥L) =
        (⟨(v : G) * (w : G) * (v : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer v.2) (w : G)).mp w.2⟩ : ↥L) :=
      Subtype.ext (by rw [Subgroup.normalizerMonoidHom_apply_apply_coe]; rfl)
    rw [hval]
    change (QuotientGroup.mk' (CFSG.pCore 2 ↥L)
        ⟨(v : G) * (w : G) * (v : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer v.2) (w : G)).mp w.2⟩) =
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L) v) *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L) w) *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L) v)⁻¹
    simp only [← map_mul, ← map_inv]
    rfl
  have hconj_eq_one_iff : ∀ q : Bar2 L,
      MulAut.conj q = 1 ↔ q ∈ Subgroup.center (Bar2 L) := by
    intro q
    constructor
    · intro h
      rw [Subgroup.mem_center_iff]
      intro x
      have hx := congrArg (fun f : MulAut (Bar2 L) => f x) h
      rw [MulAut.conj_apply, MulAut.one_apply] at hx
      calc x * q = (q * x * q⁻¹) * q := by rw [hx]
        _ = q * x := by group
    · intro h
      ext x
      rw [MulAut.conj_apply, MulAut.one_apply]
      have hx := Subgroup.mem_center_iff.mp h x
      calc q * x * q⁻¹ = (x * q) * q⁻¹ := by rw [← hx]
        _ = x := by group
  have hcent_iff : ∀ v : ↥L,
      (v : G) ∈ centSection N L (CFSG.Open.pCoreOf 2 L) ↔
        ((v : ↥L) : Bar2 L) ∈ Subgroup.center (Bar2 L) := by
    intro v
    constructor
    · intro hv
      obtain ⟨-, -, -, hcomm⟩ := hv
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
      have h := hcomm (a : G) a.2
      have hmemL : (v : G) * (a : G) * (v : G)⁻¹ * (a : G)⁻¹ ∈ L :=
        L.mul_mem (L.mul_mem (L.mul_mem v.2 a.2) (L.inv_mem v.2)) (L.inv_mem a.2)
      have h1 : ((⟨(v : G) * (a : G) * (v : G)⁻¹ * (a : G)⁻¹, hmemL⟩ : ↥L) :
          Bar2 L) = 1 := by
        rw [QuotientGroup.eq_one_iff]
        exact (Subgroup.mem_map_iff_mem L.subtype_injective).mp h
      have h2 : ((v : ↥L) : Bar2 L) * ((a : ↥L) : Bar2 L) *
          (((v : ↥L) : Bar2 L))⁻¹ * (((a : ↥L) : Bar2 L))⁻¹ = 1 := by
        rw [← h1]
        exact congrArg (fun z : ↥L => (z : Bar2 L)) (Subtype.ext rfl)
      have h2' : ((v : ↥L) : Bar2 L) * ((a : ↥L) : Bar2 L) =
          ((a : ↥L) : Bar2 L) * ((v : ↥L) : Bar2 L) := by
        calc ((v : ↥L) : Bar2 L) * ((a : ↥L) : Bar2 L) =
            (((v : ↥L) : Bar2 L) * ((a : ↥L) : Bar2 L) *
              (((v : ↥L) : Bar2 L))⁻¹ * (((a : ↥L) : Bar2 L))⁻¹) *
              (((a : ↥L) : Bar2 L) * ((v : ↥L) : Bar2 L)) := by group
          _ = ((a : ↥L) : Bar2 L) * ((v : ↥L) : Bar2 L) := by rw [h2, one_mul]
      exact h2'.symm
    · intro hv
      refine ⟨Subgroup.mem_sup_left v.2, Subgroup.le_normalizer v.2,
        CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L v.2, ?_⟩
      intro a ha
      have hmemL : (v : G) * a * (v : G)⁻¹ * a⁻¹ ∈ L :=
        L.mul_mem (L.mul_mem (L.mul_mem v.2 ha) (L.inv_mem v.2)) (L.inv_mem ha)
      have hmem : ((⟨(v : G) * a * (v : G)⁻¹ * a⁻¹, hmemL⟩ : ↥L)) ∈ CFSG.pCore 2 ↥L := by
        rw [← QuotientGroup.eq_one_iff]
        rw [show ((⟨(v : G) * a * (v : G)⁻¹ * a⁻¹, hmemL⟩ : ↥L) : Bar2 L) =
            ((v : ↥L) : Bar2 L) * ((⟨a, ha⟩ : ↥L) : Bar2 L) *
              (((v : ↥L) : Bar2 L))⁻¹ * (((⟨a, ha⟩ : ↥L) : Bar2 L))⁻¹ from by
          change (QuotientGroup.mk' (CFSG.pCore 2 ↥L)
              ⟨(v : G) * a * (v : G)⁻¹ * a⁻¹, hmemL⟩) =
            (QuotientGroup.mk' (CFSG.pCore 2 ↥L) v) *
            (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨a, ha⟩) *
            (QuotientGroup.mk' (CFSG.pCore 2 ↥L) v)⁻¹ *
            (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨a, ha⟩)⁻¹
          simp only [← map_mul, ← map_inv]
          rfl]
        have hca := Subgroup.mem_center_iff.mp hv ((⟨a, ha⟩ : ↥L) : Bar2 L)
        rw [← hca]
        group
      exact (Subgroup.mem_map_iff_mem L.subtype_injective).mpr hmem
  have hkerL : ψL.ker = O2ZIn17 L := by
    ext v
    rw [MonoidHom.mem_ker]
    have h1 : ψL v = 1 ↔ ((Subgroup.inclusion hLN v : ↥K) : G) ∈
        centSection N L (CFSG.Quasithin.oTwoThreeIn L) :=
      hφker (Subgroup.inclusion hLN v)
    rw [h1]
    change (v : G) ∈ centSection N L (CFSG.Quasithin.oTwoThreeIn L) ↔ v ∈ O2ZIn17 L
    rw [centSection_oTwoThreeIn_eq_of_calC hL hshape, hcent_iff v]
    rw [O2ZIn17, Subgroup.mem_comap]
    rfl
  have hL₀A6 : Nonempty (↥L₀ ≃* alternatingGroup (Fin 6)) := by
    obtain ⟨e⟩ := hshape
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hkerL.symm).trans
      (QuotientGroup.quotientKerEquivRange ψL)).symm.trans e⟩
  have hL₀normal : L₀.Normal := by
    have hnorm : (L.subgroupOf K).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).mpr inf_le_right
    have heq : L₀ = (L.subgroupOf K).map φ := by
      rw [show L₀ = ψL.range from rfl,
        show ψL = φ.comp (Subgroup.inclusion hLN) from rfl,
        MonoidHom.range_comp, Subgroup.inclusion_range]
    rw [heq]
    exact hnorm.map φ hφsurj
  have hCL₀ : Subgroup.centralizer (L₀ : Set A) = ⊥ := by
    rw [eq_bot_iff]
    intro α hα
    rw [Subgroup.mem_bot]
    have htriv : ∀ q : Bar2 L,
        (α : MulAut (Bar2 L)) q * q⁻¹ ∈ Subgroup.center (Bar2 L) := by
      intro q
      obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective q
      rw [← hv]
      have hcomm : ψL v * α = α * ψL v :=
        Subgroup.mem_centralizer_iff.mp hα (ψL v) ⟨v, rfl⟩
      have hcomm' : MulAut.conj ((v : ↥L) : Bar2 L) * (α : MulAut (Bar2 L)) =
          (α : MulAut (Bar2 L)) * MulAut.conj ((v : ↥L) : Bar2 L) := by
        rw [← hinnerL v]
        exact congrArg (fun a : A => (a : MulAut (Bar2 L))) hcomm
      have hconj_apply : ∀ h : Bar2 L,
          MulAut.conj ((v : ↥L) : Bar2 L) ((α : MulAut (Bar2 L)) h) =
            (α : MulAut (Bar2 L)) (MulAut.conj ((v : ↥L) : Bar2 L) h) := by
        intro h
        have := congrArg (fun f : MulAut (Bar2 L) => f h) hcomm'
        simpa [MulAut.mul_apply] using this
      have hconj2 : ∀ h : Bar2 L,
          ((v : ↥L) : Bar2 L) * h * ((v : ↥L) : Bar2 L)⁻¹ =
          (α : MulAut (Bar2 L)) ((v : ↥L) : Bar2 L) * h *
            ((α : MulAut (Bar2 L)) ((v : ↥L) : Bar2 L))⁻¹ := by
        intro h
        have := hconj_apply ((α : MulAut (Bar2 L))⁻¹ h)
        simpa [MulAut.conj_apply] using this
      have hq' : ∀ x : Bar2 L,
          (α : MulAut (Bar2 L)) ((v : ↥L) : Bar2 L) * ((v : ↥L) : Bar2 L)⁻¹ *
            x * ((v : ↥L) : Bar2 L) *
            ((α : MulAut (Bar2 L)) ((v : ↥L) : Bar2 L))⁻¹ = x := by
        intro x
        have := hconj2 (((v : ↥L) : Bar2 L)⁻¹ * x * ((v : ↥L) : Bar2 L))
        simpa [mul_assoc] using this.symm
      rw [Subgroup.mem_center_iff]
      intro h'
      have hcentral : (α : MulAut (Bar2 L)) ((v : ↥L) : Bar2 L) *
          ((v : ↥L) : Bar2 L)⁻¹ * h' =
          h' * ((α : MulAut (Bar2 L)) ((v : ↥L) : Bar2 L) * ((v : ↥L) : Bar2 L)⁻¹) := by
        calc (α : MulAut (Bar2 L)) ((v : ↥L) : Bar2 L) * ((v : ↥L) : Bar2 L)⁻¹ * h'
            = ((α : MulAut (Bar2 L)) ((v : ↥L) : Bar2 L) * ((v : ↥L) : Bar2 L)⁻¹ *
                h' * ((v : ↥L) : Bar2 L) *
                ((α : MulAut (Bar2 L)) ((v : ↥L) : Bar2 L))⁻¹) *
                ((α : MulAut (Bar2 L)) ((v : ↥L) : Bar2 L) *
                  ((v : ↥L) : Bar2 L)⁻¹) := by group
          _ = h' * ((α : MulAut (Bar2 L)) ((v : ↥L) : Bar2 L) *
                ((v : ↥L) : Bar2 L)⁻¹) := by rw [hq' h']
      exact hcentral.symm
    have hker : CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot (Bar2 L)
        (α : MulAut (Bar2 L)) = 1 := by
      ext q
      obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (Bar2 L)) q
      change CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot (Bar2 L)
          (α : MulAut (Bar2 L)) (QuotientGroup.mk v) = (QuotientGroup.mk v)
      rw [CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot_mk]
      exact QuotientGroup.eq_iff_div_mem.mpr (by simpa [div_eq_mul_inv] using htriv v)
    have hα1 : (α : MulAut (Bar2 L)) = 1 :=
      CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot_injective_of_perfect hperf
        (by rw [map_one]; exact hker)
    exact Subtype.ext hα1
  have h2elt : ∃ a : A, a ^ 4 ≠ 1 ∧ ∃ n : ℕ, a ^ 2 ^ n = 1 := by
    rw [ExpFourAut17] at hexp
    push Not at hexp
    obtain ⟨t, ht, ht4⟩ := hexp
    have htT : t ∈ D.T := ht.1
    have htNL : t ∈ Subgroup.normalizer (L : Set G) := ht.2
    have htK : t ∈ K := Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_right htT, htNL⟩
    refine ⟨φ ⟨t, htK⟩, ?_, ?_⟩
    · intro h
      have h4 : φ (⟨t, htK⟩ ^ 4) = 1 := by rw [map_pow]; exact h
      have hmem : ((⟨t, htK⟩ ^ 4 : ↥K) : G) ∈
          centSection N L (CFSG.Quasithin.oTwoThreeIn L) := (hφker _).mp h4
      rw [centSection_oTwoThreeIn_eq_of_calC hL hshape] at hmem
      apply ht4
      simpa using hmem
    · obtain ⟨n, hn⟩ := D.sylowM.isPGroup ⟨t, htT⟩
      refine ⟨n, ?_⟩
      rw [← map_pow]
      have h1 : (⟨t, htK⟩ : ↥K) ^ 2 ^ n = 1 := by
        apply Subtype.ext
        change t ^ 2 ^ n = 1
        simpa using congrArg Subtype.val hn
      rw [h1, map_one]
  refine ⟨A, inferInstance, φ, hφsurj, hφker, Or.inr ?_⟩
  exact hK A L₀ hL₀normal hL₀A6 hCL₀ h2elt

theorem card_vzero_le_four_of_not_expFour (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (D : Data G) (h66 : UC6.R6_6 D) (h86 : W3Lem86_1 G)
    (h88 : W3Thm88 G) (h126 : R126 D) (h914 : W3Lem914 G) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hshape : Nonempty (BarO2Z17 L ≃* alternatingGroup (Fin 6)))
    (hK : Inputs1719.K_A6AutOrder8) (hexp : ¬ ExpFourAut17 D L)
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M)
    (hU : UniqueMax D.M (L ⊔ D.T)) : Nat.card V₀ ≤ 4 := by
  have hLM : L ≤ D.M := hL.1.le
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hNM : L ⊔ D.T ≤ D.M := sup_le hLM hTM
  have hsubN : CFSG.Open.IsSubnormal L (L ⊔ D.T) :=
    CFSG.Quasithin.A3.subnormal_of_le_of_le hL.1 le_sup_left hNM
  have hLperfect : L = CFSG.Quasithin.perfectCore (L ⊔ CFSG.Open.pCoreOf 2 (L ⊔ D.T)) :=
    (CFSG.GroupTheory.perfectCore_sup_pCoreOf_eq le_sup_left hsubN hL.2.1).symm
  have hψ : ∃ (Z : Type) (_ : Group Z) (ψ : ↥(L ⊔ D.T) →* Z), Function.Surjective ψ ∧
      (∀ x : ↥(L ⊔ D.T), ψ x = 1 ↔ (x : G) ∈ CFSG.Open.pCoreOf 2 (L ⊔ D.T)) ∧
      CFSG.IsComponent ((L.subgroupOf (L ⊔ D.T)).map ψ) :=
    exists_bar2_data le_sup_left hsubN hL.2.1 hL.2.2
  have hAut := exists_aut_A6_of_not_expFour hL hshape hK hexp
  exact card_vzero_le_four_of_w3Lem914 hTim hcat D h66 h86 h88 h126 h914 h hL hLperfect hψ hAut
    hsp hU

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
