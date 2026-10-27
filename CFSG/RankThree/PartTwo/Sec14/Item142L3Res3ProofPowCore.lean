module

public import CFSG.RankThree.PartTwo.Sec14.Item142L3Res3ProofPowBase
import CFSG.RankThree.PartOne.S9.Vanishing.Basic
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
import CFSG.RankThree.PartOne.S10.HyperplaneObstructionSupplement
import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
import CFSG.RankThree.PartTwo.Sec14.Concl143Std

public section

namespace CFSG.RankThree.PartTwo.Sec14.L3PGLPow

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS Item148PtRes2 Res5Types
open CFSG.RankThree.PartTwo.Sec14.L3PGL (sigmaOf)
open CFSG.RankThree.GroupTheory.SteinbergBY
  (normalizer_le_normalizer_inSubgroup_aschbacherSolvableCore)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem commutator_mem_theta_of_sigma_eq_one {L : Subgroup G} {r : G}
    (hrN : r ∈ Subgroup.normalizer (L : Set G)) (hσ : sigmaOf L hrN = 1) {l : G} (hl : l ∈ L) :
    ⁅r, l⁆ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  have h1 := congrArg (fun φ : MulAut (↥L ⧸ θ) => φ (QuotientGroup.mk' θ ⟨l⁻¹, inv_mem hl⟩))
    hσ
  change QuotientGroup.mk' θ (L.normalizerMonoidHom ⟨r, hrN⟩ ⟨l⁻¹, inv_mem hl⟩) =
    QuotientGroup.mk' θ ⟨l⁻¹, inv_mem hl⟩ at h1
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
  refine ⟨_, h1, ?_⟩
  simp [commutatorElement_def, mul_assoc]

@[expose] noncomputable def sigmaHom {L R : Subgroup G}
    (hRN : R ≤ Subgroup.normalizer (L : Set G)) :
    ↥R →* MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
  (Sec4.thetaQuotMulAut L).comp (L.normalizerMonoidHom.comp (Subgroup.inclusion hRN))

theorem sigmaOf_commutator {L : Subgroup G} {a b : G} (haN : a ∈ Subgroup.normalizer (L : Set G))
    (hbN : b ∈ Subgroup.normalizer (L : Set G)) (hab : ⁅a, b⁆ ∈ Subgroup.normalizer (L : Set G)) :
    sigmaOf L hab = ⁅sigmaOf L haN, sigmaOf L hbN⁆ := by
  have e : (⟨⁅a, b⁆, hab⟩ : Subgroup.normalizer (L : Set G)) =
      ⁅(⟨a, haN⟩ : Subgroup.normalizer (L : Set G)), ⟨b, hbN⟩⁆ :=
    Subtype.ext rfl
  rw [sigmaOf, e, map_commutatorElement, map_commutatorElement]
  rfl

theorem le_normalizer_k142 (A : Subgroup G) (c : G) :
    A ≤ Subgroup.normalizer (k142 A (lB A) c : Set G) :=
  le_normalizer_sSup fun _ hQ => hQ.1.1.2.2

namespace Pow142

variable {A L : Subgroup G} {c : G} (d : Pow142 A c L)
include d

theorem o''_le_normalizerL : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤
    Subgroup.normalizer (L : Set G) :=
  d.o''_le.trans d.k_le_normalizer

theorem commutator_le : ⁅k142 A (lB A) c, A⁆ ≤ L ⊔ pPrimeCoreOf 3 (k142 A (lB A) c) := by
  have hD := d.std.toSec13Data
  set K := k142 A (lB A) c with hKdef
  set R := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hR
  set M := L ⊔ pPrimeCoreOf 3 K with hM
  have hAM : A ≤ Subgroup.normalizer (M : Set G) :=
    le_normalizer_sup hD.le_normalizer
      ((le_normalizer_k142 A c).trans (normalizer_le_normalizer_pPrimeCoreOf 3 K))
  rw [Subgroup.commutator_le]
  intro k hk a ha
  have hx : k ∈ (M : Set G) * (R : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left M R d.o''_le_normalizer, hM, hR,
      ← d.eq_sup_o'']
    exact hk
  obtain ⟨m, hm, r, hr, rfl⟩ := hx
  have hra : r * a = a * r := by
    have hrA : r ∈ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _ hr
    exact (Subgroup.mem_centralizer_iff.mp hrA a ha).symm
  have e : ⁅m * r, a⁆ = m * (a * m⁻¹ * a⁻¹) := by
    rw [commutatorElement_def]
    calc m * r * a * (m * r)⁻¹ * a⁻¹ = m * (r * a * r⁻¹) * m⁻¹ * a⁻¹ := by group
      _ = m * (a * m⁻¹ * a⁻¹) := by rw [hra]; group
  rw [e]
  exact mul_mem hm ((Subgroup.mem_normalizer_iff.mp (hAM ha) m⁻¹).mp (inv_mem hm))

theorem mem_pCore_of_sigma_eq_one {r : G}
    (hr : r ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)))
    (hσ : sigmaOf L (d.o''_le_normalizerL hr) = 1) : r ∈ pPrimeCoreOf 3 (k142 A (lB A) c) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := k142 A (lB A) c with hKdef
  set R := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hR
  set OK := pPrimeCoreOf 3 K with hOK
  set ψ := sigmaHom d.o''_le_normalizerL with hψ
  set R₀ : Subgroup G := ψ.ker.map R.subtype with hR₀
  have hR₀R : R₀ ≤ R := Subgroup.map_subtype_le _
  have hrR₀ : r ∈ R₀ := ⟨⟨r, hr⟩, MonoidHom.mem_ker.mpr hσ, rfl⟩
  have hR₀3 : ¬ 3 ∣ Nat.card R₀ := fun h3 => (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
    (coprime_card_pPrimeCoreOf 3 _) (h3.trans (Subgroup.card_dvd_of_le hR₀R))
  have hOK3 : ¬ 3 ∣ Nat.card OK :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 K)
  have hKOK : K ≤ Subgroup.normalizer (OK : Set G) := le_normalizer_pPrimeCoreOf 3 K
  have hR₀K : R₀ ≤ K := hR₀R.trans d.o''_le
  set M := R₀ ⊔ OK with hM
  have hMK : M ≤ K := sup_le hR₀K (pPrimeCoreOf_le 3 K)
  have hM3 : IsPiSubgroup (piCompl 3) M :=
    isPiSubgroup_piCompl_sup ((isPiSubgroup_piCompl_iff Nat.prime_three _).mpr hR₀3)
      ((isPiSubgroup_piCompl_iff Nat.prime_three _).mpr hOK3) (hR₀K.trans hKOK)
  have hLM : L ≤ Subgroup.normalizer (M : Set G) := by
    intro l hl
    refine Subgroup.mem_normalizer_fintype fun m hm => ?_
    have hle : M ≤ M.comap (MulAut.conj l).toMonoidHom := by
      refine sup_le (fun x hx => ?_) (fun o ho => ?_)
      · obtain ⟨⟨y, hyR⟩, hy1, rfl⟩ := hx
        show l * y * l⁻¹ ∈ M
        have hc := commutator_mem_theta_of_sigma_eq_one (d.o''_le_normalizerL hyR)
          (MonoidHom.mem_ker.mp hy1) hl
        rw [show l * y * l⁻¹ = ⁅y, l⁆⁻¹ * y by rw [commutatorElement_def]; group]
        exact mul_mem (Subgroup.mem_sup_right (d.theta_le (inv_mem hc)))
          (Subgroup.mem_sup_left ⟨⟨y, hyR⟩, hy1, rfl⟩)
      · show l * o * l⁻¹ ∈ M
        exact Subgroup.mem_sup_right
          ((Subgroup.mem_normalizer_iff.mp (hKOK (d.l_le hl)) o).mp ho)
    exact hle hm
  have hRM : R ≤ Subgroup.normalizer (M : Set G) := by
    refine le_normalizer_sup ?_ (d.o''_le.trans hKOK)
    intro r' hr'
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨⟨y, hyR⟩, hy1, rfl⟩ := hy
    have hmem : (⟨r', hr'⟩ * ⟨y, hyR⟩ * ⟨r', hr'⟩⁻¹ : ↥R) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, MonoidHom.mem_ker.mp hy1, mul_one,
        mul_inv_cancel]
    exact ⟨_, hmem, rfl⟩
  have hKM : K ≤ Subgroup.normalizer (M : Set G) := by
    rw [hKdef, d.eq_k]
    refine sup_le (sup_le hLM ?_) hRM
    exact d.o'_le_pCore.trans (le_sup_right.trans Subgroup.le_normalizer)
  have hMO : M ≤ OK := le_pPrimeCoreOf hMK hKM
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      ((isPiSubgroup_piCompl_iff Nat.prime_three M).mp hM3))
  exact hMO (Subgroup.mem_sup_left hrR₀)

end Pow142

namespace Pow142

variable {A L : Subgroup G} {c : G} (d : Pow142 A c L)
include d

variable [(ker142 A (lB A) c).Normal]

theorem img_o''_comm
    (hcomm : ∀ r₁ ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)),
      ∀ r₂ ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)),
      ∀ (h₁ : r₁ ∈ Subgroup.normalizer (L : Set G)) (h₂ : r₂ ∈ Subgroup.normalizer (L : Set G)),
        sigmaOf L h₁ * sigmaOf L h₂ = sigmaOf L h₂ * sigmaOf L h₁)
    {x y : ↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c}
    (hx : x ∈ img142 A (lB A) c (pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))))
    (hy : y ∈ img142 A (lB A) c (pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)))) :
    x * y = y * x := by
  set R := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hR
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  have hu' : (u : G) ∈ R := Subgroup.mem_subgroupOf.mp hu
  have hv' : (v : G) ∈ R := Subgroup.mem_subgroupOf.mp hv
  have hcR : ⁅(u : G), (v : G)⁆ ∈ R := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hu' hv') (inv_mem hu')) (inv_mem hv')
  have hσ : sigmaOf L (d.o''_le_normalizerL hcR) = 1 := by
    rw [sigmaOf_commutator (d.o''_le_normalizerL hu') (d.o''_le_normalizerL hv'),
      commutatorElement_eq_one_iff_mul_comm]
    exact hcomm _ hu' _ hv' _ _
  have hO := d.mem_pCore_of_sigma_eq_one hcR hσ
  have h1 : QuotientGroup.mk' (ker142 A (lB A) c) ⁅u, v⁆ = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ker142, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_sup_left hO
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

theorem exists_centralizer_lift {k : G} (hk : k ∈ k142 A (lB A) c)
    (hkc : QuotientGroup.mk' (ker142 A (lB A) c) ⟨k, Subgroup.mem_sup_left hk⟩ ∈
      Subgroup.centralizer
        (img142 A (lB A) c A : Set (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c))) :
    ∃ k' : G, ∃ hk' : k' ∈ k142 A (lB A) c, k' ∈ Subgroup.centralizer (A : Set G) ∧
      QuotientGroup.mk' (ker142 A (lB A) c) ⟨k', Subgroup.mem_sup_left hk'⟩ =
        QuotientGroup.mk' (ker142 A (lB A) c) ⟨k, Subgroup.mem_sup_left hk⟩ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := d.std.toSec13Data
  set K := k142 A (lB A) c with hKdef
  set KA := kA142 A (lB A) c with hKAdef
  set OK := pPrimeCoreOf 3 K with hOK
  have hOKKA : OK ≤ KA := (pPrimeCoreOf_le 3 K).trans le_sup_left
  set N₀ : Subgroup ↥KA := OK.subgroupOf KA with hN₀
  have hN₀n : N₀.Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hOKKA).mpr (sup_le ?_ ?_)
    · exact le_normalizer_pPrimeCoreOf 3 K
    · exact (le_normalizer_k142 A c).trans (normalizer_le_normalizer_pPrimeCoreOf 3 K)
  have hN₀3 : ¬ 3 ∣ Nat.card N₀ := by
    rw [hN₀, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOKKA).toEquiv]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 K)
  set A' : Subgroup ↥KA := A.subgroupOf KA with hA'
  have hA'3 : IsPGroup 3 A' := by
    intro g
    refine ⟨1, ?_⟩
    have hg : ((g : ↥KA) : G) ∈ A := Subgroup.mem_subgroupOf.mp g.2
    apply Subtype.ext
    apply Subtype.ext
    simpa using hD.isElemAbelian.2 _ hg
  have hcent := CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime 3 N₀ hN₀3 A' hA'3
  set kk : ↥KA := ⟨k, Subgroup.mem_sup_left hk⟩ with hkk
  have hkkc : QuotientGroup.mk' N₀ kk ∈ Subgroup.centralizer
      ((A'.map (QuotientGroup.mk' N₀) : Subgroup (↥KA ⧸ N₀)) : Set (↥KA ⧸ N₀)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a', ha', rfl⟩
    have ha : (a' : G) ∈ A := Subgroup.mem_subgroupOf.mp ha'
    have h1 := Subgroup.mem_centralizer_iff.mp hkc (alpha142 A (lB A) c a' ha)
      ⟨a', Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    change QuotientGroup.mk' (ker142 A (lB A) c) a' * QuotientGroup.mk' _ kk =
      QuotientGroup.mk' _ kk * QuotientGroup.mk' _ a' at h1
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, ker142, Subgroup.mem_subgroupOf] at h1
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, hN₀, Subgroup.mem_subgroupOf]
    refine d.mem_pCore_of_mem ?_ h1
    have haK : (a' : G)⁻¹ * k * (a' : G) ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp ((le_normalizer_k142 A c) (inv_mem ha)) k).mp hk
      simpa using this
    change ((a' : G) * k)⁻¹ * (k * (a' : G)) ∈ K
    rw [show ((a' : G) * k)⁻¹ * (k * (a' : G)) = k⁻¹ * ((a' : G)⁻¹ * k * (a' : G)) by group]
    exact mul_mem (inv_mem hk) haK
  rw [← hcent] at hkkc
  obtain ⟨x, hx, hxk⟩ := hkkc
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hxk
  have hxk' : x⁻¹ * kk ∈ N₀ := QuotientGroup.eq.mp hxk
  have hxO : ((x⁻¹ * kk : ↥KA) : G) ∈ OK := Subgroup.mem_subgroupOf.mp hxk'
  have hxK : (x : G) ∈ K := by
    have e : (x : G) = k * ((x⁻¹ * kk : ↥KA) : G)⁻¹ := by
      simp [hkk]
    rw [e]
    exact mul_mem hk (inv_mem (pPrimeCoreOf_le 3 K hxO))
  have hxA : (x : G) ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h2 := Subgroup.mem_centralizer_iff.mp hx ⟨a, Subgroup.mem_sup_right ha⟩
      (Subgroup.mem_subgroupOf.mpr ha)
    exact congrArg Subtype.val h2
  refine ⟨x, hxK, hxA, ?_⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, ker142,
    Subgroup.mem_subgroupOf]
  exact Subgroup.mem_sup_left hxO

theorem img_o''_le_normalizer : img142 A (lB A) c (k142 A (lB A) c) ⊓
      Subgroup.centralizer
        (img142 A (lB A) c A : Set (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)) ≤
    Subgroup.normalizer (img142 A (lB A) c (pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) :
      Set (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)) := by
  rintro w ⟨hwK, hwA⟩
  obtain ⟨k, hk, rfl⟩ := hwK
  have hk' : (k : G) ∈ k142 A (lB A) c := Subgroup.mem_subgroupOf.mp hk
  obtain ⟨k', hk'K, hk'A, hk'e⟩ := d.exists_centralizer_lift hk' hwA
  have e : QuotientGroup.mk' (ker142 A (lB A) c) k =
      QuotientGroup.mk' (ker142 A (lB A) c) ⟨k', Subgroup.mem_sup_left hk'K⟩ := hk'e.symm
  rw [e]
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  obtain ⟨v, hv, rfl⟩ := hy
  have hv' := Subgroup.mem_subgroupOf.mp hv
  refine ⟨⟨k', Subgroup.mem_sup_left hk'K⟩ * v * ⟨k', Subgroup.mem_sup_left hk'K⟩⁻¹, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.mpr
      ((Subgroup.mem_normalizer_iff.mp (le_normalizer_pPrimeCoreOf 3 _ hk'A) _).mp hv')
  · rw [map_mul, map_mul, map_inv]

theorem img_o''_le_thetaCA
    (hcomm : ∀ r₁ ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)),
      ∀ r₂ ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)),
      ∀ (h₁ : r₁ ∈ Subgroup.normalizer (L : Set G)) (h₂ : r₂ ∈ Subgroup.normalizer (L : Set G)),
        sigmaOf L h₁ * sigmaOf L h₂ = sigmaOf L h₂ * sigmaOf L h₁) :
    img142 A (lB A) c (pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) ≤
      thetaCA142 A (lB A) c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set R := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hR
  have hRKA : R ≤ kA142 A (lB A) c := d.o''_le.trans le_sup_left
  have hRW : img142 A (lB A) c R ≤ img142 A (lB A) c (k142 A (lB A) c) ⊓
      Subgroup.centralizer
        (img142 A (lB A) c A : Set (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)) := by
    refine le_inf (Subgroup.map_mono (Subgroup.comap_mono d.o''_le)) ?_
    rintro _ ⟨v, hv, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨u, hu, rfl⟩
    have hv' : (v : G) ∈ Subgroup.centralizer (A : Set G) :=
      pPrimeCoreOf_le 3 _ (Subgroup.mem_subgroupOf.mp hv)
    have huv := Subgroup.mem_centralizer_iff.mp hv' (u : G) (Subgroup.mem_subgroupOf.mp hu)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext huv
  unfold thetaCA142
  refine CFSG.RankThree.PartOne.HyperplaneObstruction.le_inSubgroup_theta_of_normal_solvable
    Nat.prime_three hRW d.img_o''_le_normalizer ?_ ?_
  · exact Group.isSolvable_of_comm fun x y => Subtype.ext (d.img_o''_comm hcomm x.2 y.2)
  · intro h3
    have h1 : Nat.card (img142 A (lB A) c R) ∣ Nat.card R := by
      refine (Subgroup.card_map_dvd _ _).trans ?_
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRKA).toEquiv]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
      (h3.trans h1)

end Pow142

section Img

variable {A : Subgroup G} {c : G} [(ker142 A (lB A) c).Normal]

theorem img_mono {X Y : Subgroup G} (h : X ≤ Y) : img142 A (lB A) c X ≤ img142 A (lB A) c Y :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem img_le_normalizer_img {X Y : Subgroup G} (hXY : X ≤ Subgroup.normalizer (Y : Set G)) :
    img142 A (lB A) c X ≤ Subgroup.normalizer (img142 A (lB A) c Y :
      Set (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)) := by
  rintro _ ⟨u, hu, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨u * v * u⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact Subgroup.mem_subgroupOf.mpr
      ((Subgroup.mem_normalizer_iff.mp (hXY (Subgroup.mem_subgroupOf.mp hu)) _).mp
        (Subgroup.mem_subgroupOf.mp hv))
  · rintro ⟨v, hv, hve⟩
    refine ⟨u⁻¹ * v * u, ?_, ?_⟩
    · have h1 := (Subgroup.mem_normalizer_iff.mp (inv_mem (hXY (Subgroup.mem_subgroupOf.mp hu)))
        (v : G)).mp (Subgroup.mem_subgroupOf.mp hv)
      exact Subgroup.mem_subgroupOf.mpr (by simpa using h1)
    · rw [map_mul, map_mul, map_inv, hve]
      group

end Img

theorem mem_normalizer_inf {Γ : Type*} [Group Γ] [Finite Γ] {X Y : Subgroup Γ} {g : Γ}
    (hX : g ∈ Subgroup.normalizer (X : Set Γ)) (hY : g ∈ Subgroup.normalizer (Y : Set Γ)) :
    g ∈ Subgroup.normalizer ((X ⊓ Y : Subgroup Γ) : Set Γ) :=
  Subgroup.mem_normalizer_fintype fun y hy =>
    ⟨(Subgroup.mem_normalizer_iff.mp hX y).mp hy.1, (Subgroup.mem_normalizer_iff.mp hY y).mp hy.2⟩

namespace Pow142

variable {A L : Subgroup G} {c : G} (d : Pow142 A c L)
include d

variable [(ker142 A (lB A) c).Normal]

theorem eq_img_of_le {Q : Subgroup G}
    (hQ : Q ∈ maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3))
    {V : Subgroup (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)}
    (hVK : V ≤ img142 A (lB A) c (k142 A (lB A) c)) (hV3 : ¬ 3 ∣ Nat.card V)
    (hVA : ∀ (a : G) (ha : a ∈ A), ∀ y ∈ V,
      alpha142 A (lB A) c a ha * y * (alpha142 A (lB A) c a ha)⁻¹ ∈ V)
    (hQV : img142 A (lB A) c Q ≤ V) : V = img142 A (lB A) c Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := k142 A (lB A) c with hKdef
  set KA := kA142 A (lB A) c with hKAdef
  set N := ker142 A (lB A) c with hN
  set πα := QuotientGroup.mk' N with hπα
  have hQK : Q ≤ K := d.le_k Q hQ.prop
  have hQKA : Q ≤ KA := hQK.trans le_sup_left
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := le_normalizer_k142 A c
  set Yh : Subgroup G := (V.comap πα).map KA.subtype ⊓ K with hYh
  have hYhK : Yh ≤ K := inf_le_right
  have hYhKA : Yh ≤ KA := hYhK.trans le_sup_left
  have hmemYh : ∀ {g : G} (hg : g ∈ KA), g ∈ K → πα ⟨g, hg⟩ ∈ V → g ∈ Yh := by
    intro g hg hgK hgY
    exact ⟨⟨⟨g, hg⟩, hgY, rfl⟩, hgK⟩
  have hYhmem : ∀ {g : G} (hg : g ∈ Yh), πα ⟨g, hYhKA hg⟩ ∈ V := by
    intro g hg
    obtain ⟨⟨x, hx, rfl⟩, -⟩ := hg
    exact hx
  have hQYh : Q ≤ Yh := fun q hq =>
    hmemYh (hQKA hq) (hQK hq) (hQV ⟨⟨q, hQKA hq⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩)
  have hAYh : A ≤ Subgroup.normalizer (Yh : Set G) := by
    intro a ha
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    have hy' := hYhmem hy
    have h1 := hVA a ha _ hy'
    have e : alpha142 A (lB A) c a ha * πα ⟨y, hYhKA hy⟩ * (alpha142 A (lB A) c a ha)⁻¹ =
        πα ⟨a * y * a⁻¹, (Subgroup.mem_normalizer_iff.mp
          ((le_sup_right : A ≤ KA).trans Subgroup.le_normalizer ha) y).mp (hYhKA hy)⟩ := by
      rw [alpha142, ← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e] at h1
    exact hmemYh _ ((Subgroup.mem_normalizer_iff.mp (hAK ha) y).mp (hYhK hy)) h1
  have hYh3 : ¬ 3 ∣ Nat.card Yh := by
    set f : ↥Yh →* ↥KA ⧸ N := πα.comp (Subgroup.inclusion hYhKA) with hf
    have hcard : Nat.card Yh = Nat.card f.range * Nat.card f.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    have hrange : f.range ≤ V := by
      rintro _ ⟨y, rfl⟩
      exact hYhmem y.2
    have hkerO : f.ker.map Yh.subtype ≤ pPrimeCoreOf 3 K := by
      rintro _ ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, hf, MonoidHom.comp_apply, hπα,
        QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, hN, ker142, Subgroup.mem_subgroupOf] at hy
      exact d.mem_pCore_of_mem (hYhK y.2) hy
    have hker3 : ¬ 3 ∣ Nat.card f.ker := by
      intro h3
      have h1 := Subgroup.card_dvd_of_le hkerO
      rw [Subgroup.card_map_of_injective Yh.subtype_injective] at h1
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 K)
        (h3.trans h1)
    rw [hcard]
    intro h3
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
    · exact hV3 (h.trans (Subgroup.card_dvd_of_le hrange))
    · exact hker3 h
  have hYhmemI : Yh ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3) :=
    ⟨hYhK.trans (delta_le _), (isPiSubgroup_piCompl_iff Nat.prime_three Yh).mpr hYh3, hAYh⟩
  have hYhQ : Yh ≤ Q := hQ.2 hYhmemI hQYh
  refine le_antisymm (fun z hz => ?_) hQV
  obtain ⟨k, hk, rfl⟩ := hVK hz
  have hkK : ((k : ↥KA) : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
  have hkY : ((k : ↥KA) : G) ∈ Yh := hmemYh k.2 hkK hz
  exact ⟨k, Subgroup.mem_subgroupOf.mpr (hYhQ hkY), rfl⟩

theorem exists_le_thetaC_of_list
    (hlist : ∀ Y : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L), ¬ 3 ∣ Nat.card Y →
      (∀ σ ∈ Sec4.autThetaQuot A L, Y.map σ.toMonoidHom ≤ Y) →
      ∃ (a : G) (_ : a ∈ A) (haN : a ∈ Subgroup.normalizer (L : Set G)),
        sigmaOf L haN ≠ 1 ∧
          Y ≤ inSubgroup (aschbacherSolvableCore 3) (Res5Types.fixSubgroup (sigmaOf L haN)))
    {W : Subgroup (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)} (hWL : W ≤ img142 A (lB A) c L)
    (hW3 : ¬ 3 ∣ Nat.card W)
    (hWA : ∀ (a : G) (ha : a ∈ A), ∀ y ∈ W,
      alpha142 A (lB A) c a ha * y * (alpha142 A (lB A) c a ha)⁻¹ ∈ W) :
    ∃ (a : G) (ha : a ∈ A), alpha142 A (lB A) c a ha ≠ 1 ∧
      W ≤ inSubgroup (aschbacherSolvableCore 3) (img142 A (lB A) c L ⊓
        Subgroup.centralizer
          ({alpha142 A (lB A) c a ha} : Set (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c))) := by
  set Lα := img142 A (lB A) c L with hLα
  set ψ := d.lbarEquiv with hψ
  set Y : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    (W.subgroupOf Lα).map ψ.symm.toMonoidHom with hY
  have hY3 : ¬ 3 ∣ Nat.card Y := by
    rw [hY, Subgroup.card_map_of_injective ψ.symm.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWL).toEquiv]
    exact hW3
  have hYinv : ∀ σ ∈ Sec4.autThetaQuot A L, Y.map σ.toMonoidHom ≤ Y := by
    intro σ hσ
    obtain ⟨a, haN, haA, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hσ
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    have hw' := Subgroup.mem_subgroupOf.mp hw
    have hact := d.lbarEquiv_act haA haN (ψ.symm w)
    rw [← hψ, MulEquiv.apply_symm_apply] at hact
    have hmem : ((ψ (sigmaOf L haN (ψ.symm w)) : ↥Lα) :
        ↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c) ∈ W := by
      rw [hact]
      exact hWA a haA _ hw'
    refine ⟨ψ (sigmaOf L haN (ψ.symm w)), Subgroup.mem_subgroupOf.mpr hmem, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rfl
  obtain ⟨a, ha, haN, hσ1, hle⟩ := hlist Y hY3 hYinv
  refine ⟨a, ha, fun h1 => hσ1 (d.sigmaOf_eq_one_of_alpha ha haN h1), ?_⟩
  set x := alpha142 A (lB A) c a ha with hx
  set C' : Subgroup ↥Lα := (Res5Types.fixSubgroup (sigmaOf L haN)).map ψ.toMonoidHom with hC'
  have hW' : Lα ⊓ Subgroup.centralizer ({x} : Set _) = C'.map Lα.subtype := by
    ext w
    constructor
    · rintro ⟨hwL, hwc⟩
      have hwc' : w * x = x * w := Subgroup.mem_centralizer_singleton_iff.mp hwc
      refine ⟨⟨w, hwL⟩, ⟨ψ.symm ⟨w, hwL⟩, ?_, by simp⟩, rfl⟩
      change sigmaOf L haN (ψ.symm ⟨w, hwL⟩) = ψ.symm ⟨w, hwL⟩
      apply ψ.injective
      apply Subtype.ext
      rw [hψ, d.lbarEquiv_act ha haN, ← hψ, MulEquiv.apply_symm_apply]
      change x * w * x⁻¹ = w
      rw [← hwc', mul_inv_cancel_right]
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨(ψ z).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have h1 := d.lbarEquiv_act ha haN z
      rw [Res5Types.mem_fixSubgroup.mp hz] at h1
      change ((ψ z : ↥Lα) : ↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c) * x =
        x * ((ψ z : ↥Lα) : ↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)
      calc ((ψ z : ↥Lα) : ↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c) * x =
          (x * (ψ z : ↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c) * x⁻¹) * x := by rw [← h1]
        _ = x * ((ψ z : ↥Lα) : ↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c) := by group
  have hθ : inSubgroup (aschbacherSolvableCore 3) (Lα ⊓ Subgroup.centralizer ({x} : Set _)) =
      ((inSubgroup (aschbacherSolvableCore 3) (Res5Types.fixSubgroup (sigmaOf L haN))).map
        ψ.toMonoidHom).map Lα.subtype := by
    rw [hW', ← Sec6.map_inSubgroup_theta_of_injective Lα.subtype Lα.subtype_injective, hC',
      ← Sec6.map_inSubgroup_theta_of_injective ψ.toMonoidHom ψ.injective]
  rw [hθ]
  intro w hw
  have hzY : ψ.symm ⟨w, hWL hw⟩ ∈ Y := ⟨⟨w, hWL hw⟩, Subgroup.mem_subgroupOf.mpr hw, rfl⟩
  exact ⟨⟨w, hWL hw⟩, ⟨ψ.symm ⟨w, hWL hw⟩, hle hzY, by simp⟩, rfl⟩

theorem typesOne_of_list_comm {Q : Subgroup G}
    (hQ : Q ∈ maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3))
    (hlist : ∀ Y : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L), ¬ 3 ∣ Nat.card Y →
      (∀ σ ∈ Sec4.autThetaQuot A L, Y.map σ.toMonoidHom ≤ Y) →
      ∃ (a : G) (_ : a ∈ A) (haN : a ∈ Subgroup.normalizer (L : Set G)),
        sigmaOf L haN ≠ 1 ∧
          Y ≤ inSubgroup (aschbacherSolvableCore 3) (Res5Types.fixSubgroup (sigmaOf L haN)))
    (hcomm : ∀ r₁ ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)),
      ∀ r₂ ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)),
      ∀ (h₁ : r₁ ∈ Subgroup.normalizer (L : Set G)) (h₂ : r₂ ∈ Subgroup.normalizer (L : Set G)),
        sigmaOf L h₁ * sigmaOf L h₂ = sigmaOf L h₂ * sigmaOf L h₁) :
    ∃ (a : G) (ha : a ∈ A), alpha142 A (lB A) c a ha ≠ 1 ∧
      img142 A (lB A) c Q =
        thetaC142 A (lB A) c (alpha142 A (lB A) c a ha) ⊔ thetaCA142 A (lB A) c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := d.std.toSec13Data
  set K := k142 A (lB A) c with hKdef
  set KA := kA142 A (lB A) c with hKAdef
  set R := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hR
  have hQK : Q ≤ K := d.le_k Q hQ.prop
  have hQKA : Q ≤ KA := hQK.trans le_sup_left
  have hQ3 : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.prop.2.1
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := hQ.prop.2.2
  have hA3 : IsPGroup 3 A := fun a => ⟨1, Subtype.ext (by simpa using hD.isElemAbelian.2 a a.2)⟩
  have hfac :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization 3
      Nat.prime_three A Q hA3 hQ3 hAQ
  have hcQ : ⁅Q, A⁆ ≤ Q := Subgroup.le_normalizer_iff_commutator_le_left.mp hAQ
  have hcL : ⁅Q, A⁆ ≤ L ⊔ pPrimeCoreOf 3 K :=
    (Subgroup.commutator_mono hQK le_rfl).trans d.commutator_le
  have hCR : Q ⊓ Subgroup.centralizer (A : Set G) ≤ R :=
    inf_centralizer_le_xA (Sec14Std.maximal_isElemAbelian d.std) hQ3
  have himgQ : img142 A (lB A) c Q = img142 A (lB A) c ⁅Q, A⁆ ⊔
      img142 A (lB A) c (Q ⊓ Subgroup.centralizer (A : Set G)) := by
    conv_lhs => rw [hfac]
    rw [img142, img142, img142, Subgroup.subgroupOf_sup (hcQ.trans hQKA)
      (inf_le_left.trans hQKA), Subgroup.map_sup]
  have hc1 : img142 A (lB A) c ⁅Q, A⁆ ≤ img142 A (lB A) c Q ⊓ img142 A (lB A) c L := by
    refine le_inf (img_mono hcQ) ?_
    calc img142 A (lB A) c ⁅Q, A⁆ ≤ img142 A (lB A) c (L ⊔ pPrimeCoreOf 3 K) := img_mono hcL
      _ = img142 A (lB A) c L := img_sup_pCore d.l_le_kA
  set W := img142 A (lB A) c Q ⊓ img142 A (lB A) c L with hW
  have hW3 : ¬ 3 ∣ Nat.card W := by
    intro h3
    apply hQ3
    refine h3.trans ((Subgroup.card_dvd_of_le inf_le_left).trans
      ((Subgroup.card_map_dvd _ _).trans ?_))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQKA).toEquiv]
  have hαN : ∀ (b : G) (hb : b ∈ A) {X : Subgroup G}, A ≤ Subgroup.normalizer (X : Set G) →
      alpha142 A (lB A) c b hb ∈ Subgroup.normalizer (img142 A (lB A) c X :
        Set (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)) := by
    intro b hb X hX
    exact img_le_normalizer_img hX
      ⟨⟨b, Subgroup.mem_sup_right hb⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
  have hWA : ∀ (b : G) (hb : b ∈ A), ∀ y ∈ W,
      alpha142 A (lB A) c b hb * y * (alpha142 A (lB A) c b hb)⁻¹ ∈ W := by
    intro b hb y hy
    exact (Subgroup.mem_normalizer_iff.mp
      (mem_normalizer_inf (hαN b hb hAQ) (hαN b hb hD.le_normalizer)) y).mp hy
  obtain ⟨a, ha, ha1, hle⟩ := d.exists_le_thetaC_of_list hlist inf_le_right hW3 hWA
  set x := alpha142 A (lB A) c a ha with hx
  have hθ : inSubgroup (aschbacherSolvableCore 3) (img142 A (lB A) c L ⊓
        Subgroup.centralizer ({x} : Set (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c))) ≤
      thetaC142 A (lB A) c x := by
    unfold thetaC142
    refine Sec13.inSubgroup_theta_le_of_normal (inf_le_inf_right _ (img_mono d.l_le)) ?_
    rintro w ⟨hwK, hwx⟩
    exact mem_normalizer_inf (img_le_normalizer_img d.k_le_normalizer hwK)
      (Subgroup.le_normalizer hwx)
  set θ₁ := thetaC142 A (lB A) c x with hθ₁
  set θ₂ := thetaCA142 A (lB A) c with hθ₂
  have hxA : x ∈ img142 A (lB A) c A :=
    ⟨⟨a, Subgroup.mem_sup_right ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
  have hX₂X₁ : img142 A (lB A) c K ⊓
        Subgroup.centralizer (img142 A (lB A) c A :
          Set (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)) ≤
      img142 A (lB A) c K ⊓
        Subgroup.centralizer ({x} : Set (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)) :=
    inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxA))
  have hθ₂N : θ₂ ≤ Subgroup.normalizer (θ₁ : Set (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)) :=
    (Subgroup.map_subtype_le _).trans (hX₂X₁.trans
      (CFSG.RankThree.PartOne.Vanish.le_normalizer_inSubgroup_aschbacherSolvableCore 3 _))
  have hQV : img142 A (lB A) c Q ≤ θ₁ ⊔ θ₂ := by
    rw [himgQ]
    exact sup_le_sup (hc1.trans (hle.trans hθ))
      ((img_mono hCR).trans (d.img_o''_le_thetaCA hcomm))
  have hVK : θ₁ ⊔ θ₂ ≤ img142 A (lB A) c K :=
    sup_le ((Subgroup.map_subtype_le _).trans inf_le_left)
      ((Subgroup.map_subtype_le _).trans inf_le_left)
  have hV3 : ¬ 3 ∣ Nat.card (θ₁ ⊔ θ₂ : Subgroup (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)) := by
    rw [sup_comm]
    exact (isPiSubgroup_piCompl_iff Nat.prime_three _).mp (isPiSubgroup_piCompl_sup
      ((isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
        (CFSG.RankThree.PartOne.Vanish.not_dvd_card_inSubgroup_aschbacherSolvableCore
          Nat.prime_three _))
      ((isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
        (CFSG.RankThree.PartOne.Vanish.not_dvd_card_inSubgroup_aschbacherSolvableCore
          Nat.prime_three _))
      hθ₂N)
  have hVA : ∀ (b : G) (hb : b ∈ A), ∀ y ∈ θ₁ ⊔ θ₂,
      alpha142 A (lB A) c b hb * y * (alpha142 A (lB A) c b hb)⁻¹ ∈ θ₁ ⊔ θ₂ := by
    intro b hb y hy
    set z := alpha142 A (lB A) c b hb with hz
    have hzK : z ∈ Subgroup.normalizer (img142 A (lB A) c K :
        Set (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)) := hαN b hb (le_normalizer_k142 A c)
    have hzCA : z ∈ Subgroup.centralizer (img142 A (lB A) c A :
        Set (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨u, hu, rfl⟩
      rw [hz, alpha142, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hD.commute (Subgroup.mem_subgroupOf.mp hu) hb)
    have hzx : z ∈ Subgroup.centralizer ({x} : Set (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxA) hzCA
    have h1 : z ∈ Subgroup.normalizer (θ₁ : Set (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)) :=
      normalizer_le_normalizer_inSubgroup_aschbacherSolvableCore 3 _
        (mem_normalizer_inf hzK (Subgroup.le_normalizer hzx))
    have h2 : z ∈ Subgroup.normalizer (θ₂ : Set (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)) :=
      normalizer_le_normalizer_inSubgroup_aschbacherSolvableCore 3 _
        (mem_normalizer_inf hzK (Subgroup.le_normalizer hzCA))
    have h3 : z ∈ Subgroup.normalizer ((θ₁ ⊔ θ₂ : Subgroup _) :
        Set (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)) :=
      le_normalizer_sup (Subgroup.zpowers_le.mpr h1) (Subgroup.zpowers_le.mpr h2)
        (Subgroup.mem_zpowers z)
    exact (Subgroup.mem_normalizer_iff.mp h3 y).mp hy
  exact ⟨a, ha, ha1, (d.eq_img_of_le hQ hVK hV3 hVA hQV).symm⟩

end Pow142

end CFSG.RankThree.PartTwo.Sec14.L3PGLPow
