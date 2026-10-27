module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndDefs
public import CFSG.GH74.Uniqueness.SU.SU13TA3PermE
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CComponents
import CFSG.GroupTheory.MulAutCongr
import CFSG.GroupTheory.ConjActionModPCore
import CFSG.Walter.Bender1970.S3.Tools
import CFSG.GroupTheory.Frattini.PSubgroupLift
import CFSG.GroupTheory.PGroup.CardCoprime
import CFSG.GroupTheory.CardMapInfKer
import CFSG.RankThree.PartTwo.Sec15.ThmDA10Core

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace CoprimeImage

private lemma map_relPPrimeCore_le {Γ Δ : Type*} [Group Γ] [Group Δ] {p : ℕ}
    (f : Γ →* Δ) (X : Subgroup Γ) :
    (CFSG.Open.relPPrimeCore p X).map f ≤ CFSG.Open.relPPrimeCore p (X.map f) := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun N hN => ?_
  obtain ⟨hNX, hNnorm, hNcop⟩ := hN
  exact (Subgroup.map_le_iff_le_comap).mp (by
    refine le_sSup ?_
    refine ⟨Subgroup.map_mono hNX, ?_, ?_⟩
    · rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hNX)]
      rintro _ _ ⟨n, hn, rfl⟩ ⟨k, hk, rfl⟩
      simpa only [map_mul, map_inv] using
        Subgroup.mem_map_of_mem f ((Subgroup.normal_subgroupOf_iff hNX).mp hNnorm n k hn hk)
    · exact Nat.Coprime.of_dvd_right (Subgroup.card_map_dvd N f) hNcop)

private lemma normal_inf_comap {Γ Δ : Type*} [Group Γ] [Group Δ] (f : Γ →* Δ)
    {X : Subgroup Γ} {N : Subgroup Δ} (hNle : N ≤ X.map f)
    (hNnorm : (N.subgroupOf (X.map f)).Normal) :
    ((X ⊓ Subgroup.comap f N).subgroupOf X).Normal := by
  rw [Subgroup.normal_subgroupOf_iff inf_le_left]
  intro h k hh hk
  refine ⟨X.mul_mem (X.mul_mem hk hh.1) (X.inv_mem hk), ?_⟩
  have hk' : f k ∈ X.map f := Subgroup.mem_map_of_mem f hk
  have hconj := (Subgroup.normal_subgroupOf_iff hNle).mp hNnorm
    (f h) (f k) hh.2 hk'
  change f (k * h * k⁻¹) ∈ N
  simpa only [map_mul, map_inv] using hconj

private lemma coprime_card_inf_comap {Γ Δ : Type*} [Group Γ] [Finite Γ] [Group Δ] {p : ℕ}
    (f : Γ →* Δ) (hf : Nat.Coprime (Nat.card f.ker) p) {X : Subgroup Γ} {N : Subgroup Δ}
    (hNle : N ≤ X.map f) (hNcop : Nat.Coprime p (Nat.card N)) :
    Nat.Coprime p (Nat.card (X ⊓ Subgroup.comap f N : Subgroup Γ)) := by
  let N' : Subgroup Γ := X ⊓ Subgroup.comap f N
  let ψ : ↥N' →* Δ := f.comp N'.subtype
  have hrange : ψ.range = N := by
    apply le_antisymm
    · intro y hy
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
      exact x.2.2
    · intro y hy
      obtain ⟨x, hxX, rfl⟩ := Subgroup.mem_map.mp (hNle hy)
      exact MonoidHom.mem_range.mpr ⟨⟨x, ⟨hxX, hy⟩⟩, rfl⟩
  have hker : Nat.card ψ.ker = Nat.card ↥(N' ⊓ f.ker : Subgroup Γ) := by
    refine Nat.card_congr ?_
    exact
      { toFun := fun x => ⟨((x : N') : Γ), x.1.2, x.2⟩
        invFun := fun y => ⟨⟨y, y.2.1⟩, y.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hcard := Subgroup.card_ker_mul_card_range ψ
  rw [hker, hrange] at hcard
  have hkercop : Nat.Coprime p (Nat.card ↥(N' ⊓ f.ker : Subgroup Γ)) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le inf_le_right) hf.symm
  rw [← hcard]
  exact hkercop.mul_right hNcop

theorem relPPrimeCore_map_of_coprime_ker {Γ Δ : Type*} [Group Γ] [Finite Γ] [Group Δ] {p : ℕ}
    (f : Γ →* Δ) (hf : Nat.Coprime (Nat.card f.ker) p) (X : Subgroup Γ) :
    (CFSG.Open.relPPrimeCore p X).map f = CFSG.Open.relPPrimeCore p (X.map f) := by
  apply le_antisymm
  · exact map_relPPrimeCore_le f X
  · refine sSup_le fun N hN => ?_
    obtain ⟨hNle, hNnorm, hNcop⟩ := hN
    have hNnorm' := normal_inf_comap f hNle hNnorm
    have hNcop' := coprime_card_inf_comap f hf hNle hNcop
    have hN'mem : X ⊓ Subgroup.comap f N ≤ CFSG.Open.relPPrimeCore p X :=
      le_sSup ⟨inf_le_left, hNnorm', hNcop'⟩
    have hmapN : (X ⊓ Subgroup.comap f N).map f = N := by
      apply le_antisymm
      · rintro y ⟨x, hx, rfl⟩
        exact hx.2
      · intro y hy
        obtain ⟨x, hxX, rfl⟩ := Subgroup.mem_map.mp (hNle hy)
        exact Subgroup.mem_map.mpr ⟨x, ⟨hxX, hy⟩, rfl⟩
    calc N = (X ⊓ Subgroup.comap f N).map f := hmapN.symm
      _ ≤ (CFSG.Open.relPPrimeCore p X).map f := Subgroup.map_mono hN'mem

theorem map_inf_centralizer_of_coprime_ker {Γ Δ : Type*} [Group Γ] [Finite Γ] [Group Δ] {p : ℕ}
    (hp : p.Prime) (f : Γ →* Δ) (hf : Nat.Coprime (Nat.card f.ker) p) {X B : Subgroup Γ}
    (hB : IsPGroup p B) (hBX : B ≤ X) :
    (X ⊓ Subgroup.centralizer (B : Set Γ)).map f =
      X.map f ⊓ Subgroup.centralizer ((B.map f : Subgroup Δ) : Set Δ) := by
  classical
  let X' : Subgroup Δ := X.map f
  let φ : ↥X →* ↥X' := f.subgroupMap X
  have hφsurj : Function.Surjective φ := f.subgroupMap_surjective X
  have hker_eq : φ.ker = f.ker.subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · intro hx
      have := congrArg (fun y : ↥X' => (y : Δ)) hx
      change f (x : Γ) = 1 at this
      simpa using this
    · intro hx
      apply Subtype.ext
      change f (x : Γ) = 1
      simpa using hx
  have hker_dvd : Nat.card φ.ker ∣ Nat.card f.ker := by
    rw [hker_eq, ← Subgroup.inf_subgroupOf_right (H := f.ker) (K := X),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hkernot : ¬ p ∣ Nat.card φ.ker :=
    (hp.coprime_iff_not_dvd).mp
      (Nat.Coprime.of_dvd_right hker_dvd hf.symm)
  let BX : Subgroup ↥X := B.subgroupOf X
  have hBXp : IsPGroup p BX := hB.of_equiv (Subgroup.subgroupOfEquivOfLe hBX).symm
  have hcent :=
    CFSG.RankThreeEvenClassification.Helpers.centralizer_map_eq_of_pGroup_prime_complement_kernel
      p hp φ hφsurj hkernot BX hBXp
  have hcomp : X'.subtype.comp φ = f.comp X.subtype := by ext x; rfl
  have hA : (Subgroup.centralizer (BX : Set ↥X)).map X.subtype =
      X ⊓ Subgroup.centralizer (B : Set Γ) :=
    CFSG.Walter.map_subtype_centralizer_subgroupOf hBX
  have hEeq : (BX.map φ).map X'.subtype = B.map f := by
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hBX]
  have hX'cent : (Subgroup.centralizer (BX.map φ : Set ↥X')).map X'.subtype =
      X' ⊓ Subgroup.centralizer ((B.map f : Subgroup Δ) : Set Δ) := by
    have h := CFSG.Walter.map_subtype_centralizer_subgroupOf
      (X := X') (U := (BX.map φ).map X'.subtype) (Subgroup.map_subtype_le _)
    rw [show (((BX.map φ).map X'.subtype).subgroupOf X') = BX.map φ from by
      rw [Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective X'.subtype_injective]] at h
    rwa [hEeq] at h
  have hmap := congrArg (Subgroup.map X'.subtype) hcent
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hA] at hmap
  rw [hX'cent] at hmap
  exact hmap

private lemma inf_ker_le_relPPrimeCore {Γ Δ : Type*} [Group Γ] [Finite Γ] [Group Δ] {p : ℕ}
    (f : Γ →* Δ) (hf : Nat.Coprime (Nat.card f.ker) p) (X : Subgroup Γ) :
    X ⊓ f.ker ≤ CFSG.Open.relPPrimeCore p X := by
  refine le_sSup ⟨inf_le_left, ?_, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro h k hh hk
    refine ⟨X.mul_mem (X.mul_mem hk hh.1) (X.inv_mem hk), ?_⟩
    have hh1 : f h = 1 := MonoidHom.mem_ker.mp hh.2
    change f (k * h * k⁻¹) = 1
    simp [map_mul, map_inv, hh1]
  · exact Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le inf_le_right) hf.symm

theorem le_relPPrimeCore_of_map_le {Γ Δ : Type*} [Group Γ] [Finite Γ] [Group Δ] {p : ℕ}
    (f : Γ →* Δ) (hf : Nat.Coprime (Nat.card f.ker) p) {X W : Subgroup Γ} (hWX : W ≤ X)
    (hW : W.map f ≤ CFSG.Open.relPPrimeCore p (X.map f)) :
    W ≤ CFSG.Open.relPPrimeCore p X := by
  have hcore_le : CFSG.Open.relPPrimeCore p X ≤ X := sSup_le fun _ hN => hN.1
  intro w hw
  have hwX : w ∈ X := hWX hw
  have hwf : f w ∈ CFSG.Open.relPPrimeCore p (X.map f) :=
    hW (Subgroup.mem_map_of_mem f hw)
  rw [← relPPrimeCore_map_of_coprime_ker f hf X] at hwf
  obtain ⟨o, ho, hfo⟩ := Subgroup.mem_map.mp hwf
  have hoX : o ∈ X := hcore_le ho
  have hker_mem : o⁻¹ * w ∈ X ⊓ f.ker := by
    refine ⟨X.mul_mem (X.inv_mem hoX) hwX, ?_⟩
    change f (o⁻¹ * w) = 1
    rw [map_mul, map_inv, hfo]
    simp
  have hmem : o⁻¹ * w ∈ CFSG.Open.relPPrimeCore p X :=
    inf_ker_le_relPPrimeCore f hf X hker_mem
  have hwEq : w = o * (o⁻¹ * w) := by group
  rw [hwEq]
  exact Subgroup.mul_mem _ ho hmem

theorem map_le_normalizer_map {Γ Δ : Type*} [Group Γ] [Group Δ] (f : Γ →* Δ)
    {A W : Subgroup Γ} (hA : A ≤ Subgroup.normalizer (W : Set Γ)) :
    A.map f ≤ Subgroup.normalizer ((W.map f : Subgroup Δ) : Set Δ) :=
  (Subgroup.map_mono hA).trans (Subgroup.le_normalizer_map f)

end CoprimeImage

namespace Ctx82E3

private noncomputable def conjCenterAction (c : Ctx82E3 D) :
    ↥D.M →* MulAut (c.Lbar ⧸ Subgroup.center c.Lbar) :=
  CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction
    (CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L)
    (Subgroup.center c.Lbar)
    (fun m n hn => by
      have hchar := Subgroup.characteristic_iff_map_eq.mp Subgroup.centerCharacteristic
        ((CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L m : MulAut c.Lbar) :
          c.Lbar ≃* c.Lbar)
      have hmem : (CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L m) n ∈
          Subgroup.map ((CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L m :
            MulAut c.Lbar) : c.Lbar ≃* c.Lbar).toMonoidHom (Subgroup.center c.Lbar) :=
        Subgroup.mem_map_of_mem _ hn
      rwa [hchar] at hmem)

private noncomputable def a10AutAction (c : Ctx82E3 D)
    (iso : c.Lbar ⧸ Subgroup.center c.Lbar ≃* alternatingGroup (Fin 10)) :
    ↥D.M →* MulAut (alternatingGroup (Fin 10)) :=
  (MulAut.congr iso).toMonoidHom.comp (conjCenterAction c)

private noncomputable def permMulAutAlt :
    Equiv.Perm (Fin 10) ≃* MulAut (alternatingGroup (Fin 10)) :=
  MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 10)))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 10
      (by norm_num) (by norm_num))

noncomputable def a10Hom (c : Ctx82E3 D)
    (iso : c.Lbar ⧸ Subgroup.center c.Lbar ≃* alternatingGroup (Fin 10)) :
    ↥D.M →* Equiv.Perm (Fin 10) :=
  permMulAutAlt.symm.toMonoidHom.comp (a10AutAction c iso)

private lemma conjCenterAction_apply_of_mem_L (c : Ctx82E3 D) {m : G}
    (hmM : m ∈ D.M) (hmL : m ∈ c.L) :
    conjCenterAction c ⟨m, hmM⟩ =
      MulAut.conj (QuotientGroup.mk (QuotientGroup.mk (⟨m, hmL⟩ : ↥c.L) : c.Lbar)) := by
  unfold conjCenterAction
  apply MulEquiv.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  rw [CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk]
  rw [CFSG.GroupTheory.conjModPCore_apply_eq_conj_mk 2 c.L D.M c.le_normalizer_L hmM hmL]
  rfl

theorem a10Hom_apply_of_mem_L (c : Ctx82E3 D)
    (iso : c.Lbar ⧸ Subgroup.center c.Lbar ≃* alternatingGroup (Fin 10)) {m : G}
    (hmM : m ∈ D.M) (hmL : m ∈ c.L) :
    c.a10Hom iso ⟨m, hmM⟩ =
      (iso (QuotientGroup.mk (QuotientGroup.mk (⟨m, hmL⟩ : ↥c.L) : c.Lbar)) :
        Equiv.Perm (Fin 10)) := by
  classical
  let z0 : c.Lbar ⧸ Subgroup.center c.Lbar :=
    QuotientGroup.mk (QuotientGroup.mk (⟨m, hmL⟩ : ↥c.L) : c.Lbar)
  have hdef : c.a10Hom iso = permMulAutAlt.symm.toMonoidHom.comp (a10AutAction c iso) := rfl
  rw [hdef]
  apply permMulAutAlt.injective
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  change MulAut.congr iso (conjCenterAction c ⟨m, hmM⟩) = permMulAutAlt (iso z0)
  rw [conjCenterAction_apply_of_mem_L c hmM hmL, CFSG.mulAut_congr_conj]
  have hconjNormal : permMulAutAlt (iso z0) =
      MulAut.conjNormal (H := alternatingGroup (Fin 10))
        (((iso z0 : alternatingGroup (Fin 10))) : Equiv.Perm (Fin 10)) := rfl
  rw [hconjNormal]
  apply MulEquiv.ext
  intro y
  apply Subtype.ext
  simp [z0, MulAut.conj_apply, MulAut.conjNormal_apply]

theorem alternatingGroup_le_range_a10Hom (c : Ctx82E3 D)
    (iso : c.Lbar ⧸ Subgroup.center c.Lbar ≃* alternatingGroup (Fin 10)) :
    alternatingGroup (Fin 10) ≤ (c.a10Hom iso).range := by
  intro a ha
  obtain ⟨q, hq⟩ := iso.surjective ⟨a, ha⟩
  have haeq : a = (iso q : Equiv.Perm (Fin 10)) := congrArg Subtype.val hq.symm
  rw [haeq]
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨⟨(x : c.L), c.hyp81.1 x.2⟩,
    c.a10Hom_apply_of_mem_L iso (c.hyp81.1 x.2) x.2⟩

private lemma mem_L_of_orderOf_eq_three (c : Ctx82E3 D)
    (hPL : ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P D.M → P ≤ c.L)
    {x : ↥D.M} (hx : orderOf x = 3) : (x : G) ∈ c.L := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hzp : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx]; norm_num)
  obtain ⟨Q, hQle⟩ := hzp.exists_le_sylow (G := ↥D.M)
  have hQx : x ∈ (Q : Subgroup ↥D.M) := hQle (Subgroup.mem_zpowers x)
  let P : Subgroup G := (Q : Subgroup ↥D.M).map D.M.subtype
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf 3 P D.M := ⟨Q, rfl⟩
  exact hPL P hPsyl (Subgroup.mem_map_of_mem D.M.subtype hQx)

private lemma mem_comap_center_of_a10Hom_eq_one (c : Ctx82E3 D)
    (iso : c.Lbar ⧸ Subgroup.center c.Lbar ≃* alternatingGroup (Fin 10)) {x : ↥c.L}
    (hx : c.a10Hom iso ⟨(x : G), c.hyp81.1 x.2⟩ = 1) :
    x ∈ (Subgroup.center c.Lbar).comap (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)) := by
  have hval : (iso (QuotientGroup.mk (QuotientGroup.mk x)) : Equiv.Perm (Fin 10)) = 1 := by
    rw [← c.a10Hom_apply_of_mem_L iso (c.hyp81.1 x.2) x.2]
    exact hx
  have hiso_one : iso (QuotientGroup.mk (QuotientGroup.mk x)) = 1 := by
    apply Subtype.ext
    simpa using hval
  have hq_one : QuotientGroup.mk (QuotientGroup.mk x) = 1 :=
    iso.injective (by simpa using hiso_one)
  have hxcenter : (QuotientGroup.mk x : c.Lbar) ∈ Subgroup.center c.Lbar :=
    (QuotientGroup.eq_one_iff (QuotientGroup.mk x)).mp hq_one
  rw [Subgroup.mem_comap]
  simpa using hxcenter

private lemma not_dvd_card_comap_center (c : Ctx82E3 D)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar)) :
    ¬ 3 ∣ Nat.card ((Subgroup.center c.Lbar).comap
      (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L))) := by
  have hcard : Nat.card ((Subgroup.center c.Lbar).comap
        (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L))) =
      Nat.card (CFSG.Open.pCore 2 ↥c.L) * Nat.card (Subgroup.center c.Lbar) := by
    have h := CFSG.GroupTheory.card_comap_eq_card_ker_mul_card
      (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L))
      (QuotientGroup.mk'_surjective _) (Subgroup.center c.Lbar)
    rwa [QuotientGroup.ker_mk'] at h
  have hO2 : ¬ 3 ∣ Nat.card (CFSG.Open.pCore 2 ↥c.L) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L))
      Nat.prime_three (by norm_num)
  rw [hcard, Nat.Prime.dvd_mul Nat.prime_three]
  rintro (h | h)
  · exact hO2 h
  · exact hZ h

theorem coprime_card_ker_a10Hom (c : Ctx82E3 D)
    (iso : c.Lbar ⧸ Subgroup.center c.Lbar ≃* alternatingGroup (Fin 10))
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar))
    (hPL : ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P D.M → P ≤ c.L) :
    Nat.Coprime (Nat.card (c.a10Hom iso).ker) 3 := by
  classical
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 3)]
  intro h3
  obtain ⟨k, hkord⟩ := exists_prime_orderOf_dvd_card' (G := (c.a10Hom iso).ker) 3 h3
  let km : ↥D.M := k.1
  have hkmord : orderOf km = 3 := by
    have h := (Subgroup.orderOf_coe k).trans hkord
    simpa [km] using h
  have hkmL : (km : G) ∈ c.L := mem_L_of_orderOf_eq_three c hPL hkmord
  let x : ↥c.L := ⟨km, hkmL⟩
  have hxord : orderOf x = 3 := by
    rw [← Subgroup.orderOf_coe x]
    change orderOf (km : G) = 3
    rw [Subgroup.orderOf_coe km, hkmord]
  have hxker : c.a10Hom iso ⟨(x : G), c.hyp81.1 x.2⟩ = 1 := by
    have h := MonoidHom.mem_ker.mp k.2
    simpa [x, km] using h
  have hxZ := mem_comap_center_of_a10Hom_eq_one c iso hxker
  have hdvd : orderOf x ∣ Nat.card ((Subgroup.center c.Lbar).comap
      (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L))) :=
    Subgroup.orderOf_dvd_natCard _ hxZ
  have h3dvd : 3 ∣ orderOf x := by rw [hxord]
  exact not_dvd_card_comap_center c hZ (h3dvd.trans hdvd)

end Ctx82E3

namespace Ctx82E3.A10Frame

variable {c : Ctx82E3 D}

theorem le_L_of_isSylowOf (F : A10Frame c) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) : P ≤ c.L := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨k, hkM, hconj⟩ := hP.exists_mem_conj F.sylow
  intro x hx
  have hx'' : k⁻¹ * (k * x * k⁻¹) * k ∈ P := by
    rw [show k⁻¹ * (k * x * k⁻¹) * k = x by group]
    exact hx
  have hx' : k * x * k⁻¹ ∈ F.P := (hconj (k * x * k⁻¹)).mpr hx''
  have hyL : k * x * k⁻¹ ∈ c.L := F.P_le_L hx'
  have hxeq : x = k⁻¹ * (k * x * k⁻¹) * k := by group
  rw [hxeq]
  simpa using (Subgroup.mem_normalizer_iff.mp (c.le_normalizer_L (D.M.inv_mem hkM))
    (k * x * k⁻¹)).mp hyL

theorem deg_zpowers (F : A10Frame c) {b : G} (hb : b ∈ c.L) :
    F.deg (Subgroup.zpowers b) = (c.a10Hom F.iso ⟨b, c.hyp81.1 hb⟩).support.card := by
  classical
  let σ : Equiv.Perm (Fin 10) := c.a10Hom F.iso ⟨b, c.hyp81.1 hb⟩
  have hset : {i : Fin 10 | ∃ x : c.L, (x : G) ∈ Subgroup.zpowers b ∧
      (F.iso (QuotientGroup.mk (QuotientGroup.mk x : c.Lbar)) : Equiv.Perm (Fin 10)) i ≠ i}
      = (σ.support : Set (Fin 10)) := by
    ext i
    constructor
    · rintro ⟨x, hx, hxi⟩
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hxsub : x = (⟨b, hb⟩ : ↥c.L) ^ n := by
        apply Subtype.ext
        rw [Subgroup.coe_zpow]
        exact hn.symm
      have hpow : (F.iso (QuotientGroup.mk (QuotientGroup.mk x : c.Lbar)) :
          Equiv.Perm (Fin 10)) = σ ^ n := by
        have hxM : (x : G) ∈ D.M := c.hyp81.1 x.2
        rw [← c.a10Hom_apply_of_mem_L F.iso hxM x.2]
        have hxM' : (⟨(x : G), hxM⟩ : ↥D.M) = (⟨b, c.hyp81.1 hb⟩ : ↥D.M) ^ n := by
          apply Subtype.ext
          rw [Subgroup.coe_zpow]
          exact congrArg Subtype.val hxsub
        rw [hxM']
        simp [σ]
      rw [hpow] at hxi
      change i ∈ σ.support
      rw [Equiv.Perm.mem_support]
      intro hfix
      exact hxi (Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hfix n)
    · intro hi
      refine ⟨⟨b, hb⟩, Subgroup.mem_zpowers b, ?_⟩
      have hbM : b ∈ D.M := c.hyp81.1 hb
      rw [← c.a10Hom_apply_of_mem_L F.iso hbM hb]
      simpa [σ] using (Equiv.Perm.mem_support.mp hi)
  simp only [A10Frame.deg, hset, Set.ncard_coe_finset]
  rfl

private lemma inf_ker_a10Hom_eq_bot (F : A10Frame c)
    (hker : Nat.Coprime (Nat.card (c.a10Hom F.iso).ker) 3) :
    F.A.subgroupOf D.M ⊓ (c.a10Hom F.iso).ker = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxA, hxK⟩ := Subgroup.mem_inf.mp hx
  have hx3M : x ^ 3 = 1 := by
    apply Subtype.ext
    have h := F.elemAbelian.2 (x : G) (Subgroup.mem_subgroupOf.mp hxA)
    simpa [Subgroup.coe_pow] using h
  have hord3 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3M
  have hordker : orderOf x ∣ Nat.card (c.a10Hom F.iso).ker :=
    Subgroup.orderOf_dvd_natCard _ hxK
  have hcop : Nat.Coprime 3 (Nat.card (c.a10Hom F.iso).ker) := hker.symm
  have hone : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop hord3 hordker
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp hone)

private lemma map_A_le_alternatingGroup (F : A10Frame c) :
    (F.A.subgroupOf D.M).map (c.a10Hom F.iso) ≤ alternatingGroup (Fin 10) := by
  rintro y ⟨m, hmA, rfl⟩
  rw [Equiv.Perm.mem_alternatingGroup]
  have hm3 : m ^ 3 = 1 := by
    apply Subtype.ext
    have h := F.elemAbelian.2 (m : G) (Subgroup.mem_subgroupOf.mp hmA)
    simpa [Subgroup.coe_pow] using h
  have hy3 : (c.a10Hom F.iso m) ^ 3 = 1 := by rw [← map_pow, hm3, map_one]
  have hsign3 : (Equiv.Perm.sign (c.a10Hom F.iso m)) ^ 3 = 1 := by
    rw [← map_pow, hy3, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (c.a10Hom F.iso m)) with h | h
  · exact h
  · rw [h] at hsign3
    norm_num at hsign3

private lemma map_A_commute (F : A10Frame c) :
    ∀ u ∈ (F.A.subgroupOf D.M).map (c.a10Hom F.iso),
      ∀ v ∈ (F.A.subgroupOf D.M).map (c.a10Hom F.iso), Commute u v := by
  intro u hu v hv
  obtain ⟨mx, hmx, rfl⟩ := Subgroup.mem_map.mp hu
  obtain ⟨my, hmy, rfl⟩ := Subgroup.mem_map.mp hv
  have hx' : (mx : G) ∈ F.A := Subgroup.mem_subgroupOf.mp hmx
  have hy' : (my : G) ∈ F.A := Subgroup.mem_subgroupOf.mp hmy
  have hcommA : Commute (⟨(mx : G), hx'⟩ : ↥F.A) ⟨(my : G), hy'⟩ :=
    (F.elemAbelian.1.is_comm.comm ⟨(mx : G), hx'⟩ ⟨(my : G), hy'⟩)
  have hcommM : Commute mx my := by
    apply Subtype.ext
    have := congrArg (fun z : ↥F.A => (z : G)) hcommA
    simpa using this
  exact hcommM.map (c.a10Hom F.iso)

theorem exists_conj_map_A (F : A10Frame c) :
    ∃ σ : Equiv.Perm (Fin 10),
      (F.A.subgroupOf D.M).map ((MulAut.conj σ).toMonoidHom.comp (c.a10Hom F.iso)) =
        CFSG.GH74.Uniqueness.SU.SU13.TA.L10.Ebar.map
          (alternatingGroup (Fin 10)).subtype := by
  classical
  have hA_le_M : F.A ≤ D.M := F.A_le.trans (F.P_le_L.trans c.hyp81.1)
  let AM : Subgroup ↥D.M := F.A.subgroupOf D.M
  let f : ↥D.M →* Equiv.Perm (Fin 10) := c.a10Hom F.iso
  have hker : Nat.Coprime (Nat.card f.ker) 3 :=
    c.coprime_card_ker_a10Hom F.iso F.center (fun P hP => F.le_L_of_isSylowOf hP)
  have hdisj : AM ⊓ f.ker = ⊥ := inf_ker_a10Hom_eq_bot F hker
  have hcardImg : Nat.card (AM.map f) = 27 := by
    rw [CFSG.card_map_eq_card_of_inf_ker_eq_bot f hdisj]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA_le_M).toEquiv, F.card_A]
  have hleA10 : AM.map f ≤ alternatingGroup (Fin 10) := map_A_le_alternatingGroup F
  let B : Subgroup (alternatingGroup (Fin 10)) :=
    (AM.map f).subgroupOf (alternatingGroup (Fin 10))
  have hBcard : Nat.card B = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hleA10).toEquiv]
    exact hcardImg
  have hBab : ∀ x ∈ B, ∀ y ∈ B, Commute x y := by
    intro x hx y hy
    apply Subtype.ext
    exact (map_A_commute F (x : Equiv.Perm (Fin 10)) (Subgroup.mem_subgroupOf.mp hx)
      (y : Equiv.Perm (Fin 10)) (Subgroup.mem_subgroupOf.mp hy)).eq
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec15.ThmD.exists_conj_eq_Ebar hBcard hBab
  refine ⟨((g⁻¹ : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10)), ?_⟩
  have hBmap : B.map (alternatingGroup (Fin 10)).subtype = AM.map f :=
    Subgroup.map_subgroupOf_eq_of_le hleA10
  have hcomp : (alternatingGroup (Fin 10)).subtype.comp (MulAut.conj g⁻¹).toMonoidHom =
      (MulAut.conj ((g⁻¹ : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10))).toMonoidHom.comp
        (alternatingGroup (Fin 10)).subtype := by
    ext x
    simp [MulAut.conj_apply]
  have hmap := congrArg (Subgroup.map (alternatingGroup (Fin 10)).subtype) hg
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hBmap] at hmap
  rw [← Subgroup.map_map]
  exact hmap

end Ctx82E3.A10Frame

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
