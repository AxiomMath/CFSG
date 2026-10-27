module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeIWChoiceNorm
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeIWChoiceSetup

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

theorem nine3Norm_mem_J (hc : Nine3Choice V T A K S X p g x) (hI : Nine3IFacts V K S)
    {P : Subgroup G} [Fintype ↥P] [IsMulCommutative ↥(nineI V K)]
    (hPnormI : P ≤ Subgroup.normalizer (nineI V K : Set G))
    (hPcard : Nat.card ↥P = p) {a : G} (ha : a ∈ A)
    (hinv : ∀ y ∈ P, a⁻¹ * y * a = y⁻¹)
    {B : Subgroup G} (hB : B ∈ nineOmegaIn V K S) {b : G}
    (hb : b ∈ B ⊓ pCoreOf 2 K) :
    (nine3Norm (nineI V K) P hPnormI
      ⟨b, (by
        have hbBI : b ∈ B ⊓ nineI V K := by
          rw [Nine3Core.nineI_inf_eq hc.core hB]
          exact hb
        exact hbBI.2)⟩ : G) ∈
      ⨆ B ∈ nineOmegaIn V K S, B ⊓ pCoreOf 2 K := by
  classical
  haveI : Fact (Nat.Prime p) := ⟨hc.core.hyp.base.prime⟩
  let I := nineI V K
  let R := pCoreOf 2 K
  let J := ⨆ B ∈ nineOmegaIn V K S, B ⊓ R
  let A₀ := A ⊓ R
  have ha2 : a * a = 1 := by
    have h := (isElemAbelian_of_mem_omegaSet hc.core.hyp7.1
      hc.core.A_mem_nineOmegaIn.1).2 a ha
    simpa [pow_two] using h
  have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha2
  have hbI : b ∈ I := by
    have hbBI : b ∈ B ⊓ I := by
      rw [Nine3Core.nineI_inf_eq hc.core hB]
      exact hb
    exact hbBI.2
  have hA0I : A₀ ≤ I := by
    rw [show A₀ = A ⊓ R from rfl, ← Nine3Core.nineI_inf_eq hc.core hc.core.A_mem_nineOmegaIn]
    exact inf_le_right
  have hB_le_J : B ⊓ R ≤ J := le_iSup₂_of_le B hB le_rfl
  have hA0J : A₀ ≤ J := le_iSup₂_of_le A hc.core.A_mem_nineOmegaIn le_rfl
  have hb2 : b * b = 1 := by
    have h := (isElemAbelian_of_mem_omegaSet hc.core.hyp7.1 hB.1).2 b hb.1
    simpa [pow_two] using h
  have ha_b_comm : a * b = b * a := by
    have hAW : A ≤ nineW V S := le_iSup₂_of_le A hc.core.A_mem_nineDelta le_rfl
    have hBW : B ≤ nineW V S :=
      le_iSup₂_of_le B (hc.core.mem_nineDelta_iff.mpr (Or.inr hB)) le_rfl
    exact hc.core.nineW_mul_comm (hAW ha) (hBW hb.1)
  have hag : ∀ g ∈ P, a * g * a = g⁻¹ := by
    intro g hg
    have h := hinv g hg
    rwa [ha_inv] at h
  have hag' : ∀ g ∈ P, a * g⁻¹ * a = g := by
    intro g hg
    calc a * g⁻¹ * a = (a⁻¹ * g * a⁻¹)⁻¹ := by group
      _ = (a * g * a)⁻¹ := by rw [ha_inv]
      _ = (g⁻¹)⁻¹ := by rw [hag g hg]
      _ = g := inv_inv g
  let f : ↥P → ↥I := fun g =>
    ⟨g * b * g⁻¹, (Subgroup.mem_normalizer_iff.mp (hPnormI g.2) b).mp hbI⟩
  have hpair : ∀ g : ↥P, f g * f g⁻¹ ∈ A₀.subgroupOf I := by
    intro g
    have hg : (g : G) ∈ P := g.2
    have hxI : (g : G) * b * (g : G)⁻¹ ∈ I :=
      (Subgroup.mem_normalizer_iff.mp (hPnormI hg) b).mp hbI
    have hx2 : ((g : G) * b * (g : G)⁻¹) * ((g : G) * b * (g : G)⁻¹) = 1 := by
      calc ((g : G) * b * (g : G)⁻¹) * ((g : G) * b * (g : G)⁻¹)
          = (g : G) * (b * b) * (g : G)⁻¹ := by group
        _ = 1 := by rw [hb2]; group
    have hx_inv : ((g : G) * b * (g : G)⁻¹)⁻¹ = (g : G) * b * (g : G)⁻¹ :=
      inv_eq_of_mul_eq_one_left hx2
    have hab : a * b * a = b := by
      rw [ha_b_comm, mul_assoc, ha2, mul_one]
    have hconj_g : (MulAut.conj a) (g : G) = (g : G)⁻¹ := by
      simpa [MulAut.conj_apply, ha_inv] using hag (g : G) hg
    have hconj_b : (MulAut.conj a) b = b := by
      simpa [MulAut.conj_apply, ha_inv] using hab
    have hconj_gi : (MulAut.conj a) ((g : G)⁻¹) = (g : G) := by
      rw [map_inv, hconj_g, inv_inv]
    have hax : a * ((g : G) * b * (g : G)⁻¹) * a = (g : G)⁻¹ * b * (g : G) := by
      have h1 : (MulAut.conj a) ((g : G) * b * (g : G)⁻¹) =
          ((MulAut.conj a) (g : G)) * ((MulAut.conj a) b) * ((MulAut.conj a) ((g : G)⁻¹)) := by
        simp only [map_mul]
      rw [hconj_g, hconj_b, hconj_gi] at h1
      simpa [MulAut.conj_apply, ha_inv] using h1
    have hcomm := Subgroup.commutator_mem_commutator hxI ha
    rw [hI.comm A hc.core.A_mem_nineOmegaIn] at hcomm
    have hval : ((g : G) * b * (g : G)⁻¹) * ((g : G)⁻¹ * b * (g : G)) =
        ⁅(g : G) * b * (g : G)⁻¹, a⁆ := by
      rw [commutatorElement_def, hx_inv, ha_inv]
      rw [← hax]
      group
    rw [Subgroup.mem_subgroupOf]
    change (f g : G) * (f g⁻¹ : G) ∈ A₀
    simp only [f, Subtype.coe_mk, inv_inv, Subgroup.coe_inv]
    rw [hval]
    exact hcomm
  let Nsub : Subgroup ↥I := A₀.subgroupOf I
  haveI : Nsub.Normal := inferInstance
  let qf : ↥P → (↥I ⧸ Nsub) := fun g => QuotientGroup.mk' Nsub (f g)
  have hprodQ : ∏ g ∈ (Finset.univ.erase (1 : ↥P)), qf g = 1 := by
    refine Finset.prod_involution (s := Finset.univ.erase (1 : ↥P)) (f := qf)
      (g := fun g _ => g⁻¹) ?_ ?_ ?_ ?_
    · intro g hg
      have := (QuotientGroup.eq_one_iff (N := Nsub) (f g * f g⁻¹)).mpr (hpair g)
      simpa [qf, QuotientGroup.mk_mul] using this
    · intro g hg hfg
      have hg1 : g ≠ 1 := (Finset.mem_erase.mp hg).1
      intro hginv
      apply hg1
      have h2 : g * g = 1 := by
        simpa [hginv] using inv_mul_cancel g
      have hdvd2 : orderOf (g : G) ∣ 2 :=
        orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using congrArg Subtype.val h2)
      have hdvdp : orderOf (g : G) ∣ p := by
        rw [← hPcard]
        exact Subgroup.orderOf_dvd_natCard P g.2
      have hcop : Nat.Coprime 2 p :=
        Nat.coprime_two_left.mpr (hc.core.hyp.base.prime.odd_of_ne_two hc.core.hyp.base.odd)
      have h1G : orderOf (g : G) = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd2 hdvdp
      have h1P : orderOf g = 1 := by rw [Subgroup.orderOf_mk]; exact h1G
      exact orderOf_eq_one_iff.mp h1P
    · intro g hg
      rw [Finset.mem_erase] at hg ⊢
      exact ⟨inv_ne_one.mpr hg.1, Finset.mem_univ _⟩
    · intro g hg
      simp
  let Psub : ↥I := ∏ g ∈ (Finset.univ.erase (1 : ↥P)), f g
  have hmk : QuotientGroup.mk' Nsub Psub = 1 := by
    have hmap : QuotientGroup.mk' Nsub Psub =
        ∏ g ∈ (Finset.univ.erase (1 : ↥P)), qf g := by
      dsimp only [Psub]
      exact map_prod (QuotientGroup.mk' Nsub) f _
    rw [hmap, hprodQ]
  have hPsub : Psub ∈ Nsub := (QuotientGroup.eq_one_iff Psub).mp hmk
  have hPsubA : (Psub : G) ∈ A₀ := Subgroup.mem_subgroupOf.mp hPsub
  have hPsubJ : (Psub : G) ∈ J := hA0J hPsubA
  have hN : (nine3Norm I P hPnormI ⟨b, hbI⟩ : G) = b * (Psub : G) := by
    have h1 : (nine3Norm I P hPnormI ⟨b, hbI⟩) =
        f 1 * ∏ g ∈ (Finset.univ.erase (1 : ↥P)), f g := by
      change (∏ g : ↥P, f g) = f 1 * ∏ g ∈ (Finset.univ.erase (1 : ↥P)), f g
      exact (Finset.mul_prod_erase Finset.univ f (Finset.mem_univ 1)).symm
    have h1' : (nine3Norm I P hPnormI ⟨b, hbI⟩) = f 1 * Psub := h1
    have hf1 : f 1 = ⟨b, hbI⟩ := Subtype.ext (by simp [f])
    calc (nine3Norm I P hPnormI ⟨b, hbI⟩ : G)
        = ((f 1 * Psub : ↥I) : G) := congrArg Subtype.val h1'
      _ = (f 1 : G) * (Psub : G) := rfl
      _ = b * (Psub : G) := by rw [hf1]
  rw [hN]
  exact J.mul_mem (hB_le_J hb) hPsubJ

theorem nine3Norm_image_conj (hc : Nine3Choice V T A K S X p g x)
    (hI : Nine3IFacts V K S) [IsMulCommutative ↥(nineI V K)]
    {P : Subgroup G} [Fintype ↥P] (hPnormI : P ≤ Subgroup.normalizer (nineI V K : Set G))
    (hPK : P ≤ K) {U : Subgroup G} (hU : U ∈ omegaIn V K (nineE V K)) {z : G} (hz : z ∈ P) :
    ((CFSG.Quasithin.conjSubgroup U z ⊓ pCoreOf 2 K).subgroupOf (nineI V K)).map
        (nine3Norm (nineI V K) P hPnormI) =
      ((U ⊓ pCoreOf 2 K).subgroupOf (nineI V K)).map
        (nine3Norm (nineI V K) P hPnormI) := by
  have hzK : z ∈ K := hPK hz
  have hUzω : CFSG.Quasithin.conjSubgroup U z ∈ omegaIn V K (nineE V K) :=
    conjSubgroup_mem_omegaIn hU hzK
  have hUI : U ⊓ pCoreOf 2 K ≤ nineI V K :=
    le_iSup₂_of_le U hU le_rfl
  have hUIz : CFSG.Quasithin.conjSubgroup U z ⊓ pCoreOf 2 K ≤ nineI V K :=
    le_iSup₂_of_le (CFSG.Quasithin.conjSubgroup U z) hUzω le_rfl
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    have hyinf : (y : G) ∈ CFSG.Quasithin.conjSubgroup U z ⊓ pCoreOf 2 K :=
      Subgroup.mem_subgroupOf.mp hy
    have hvU : z * (y : G) * z⁻¹ ∈ U :=
      CFSG.Quasithin.mem_conjSubgroup_iff.mp hyinf.1
    have hvR : z * (y : G) * z⁻¹ ∈ pCoreOf 2 K :=
      (Nine3Core.mem_pCoreOf_conj_iff K hzK).mp hyinf.2
    have hvI : z * (y : G) * z⁻¹ ∈ nineI V K := hUI ⟨hvU, hvR⟩
    have h : nine3Norm (nineI V K) P hPnormI y =
        nine3Norm (nineI V K) P hPnormI ⟨z * (y : G) * z⁻¹, hvI⟩ := by
      let vElem : ↥(nineI V K) := ⟨z * (y : G) * z⁻¹, hvI⟩
      have hmemConj : z⁻¹ * (vElem : G) * (z⁻¹)⁻¹ ∈ nineI V K := by
        have hy : z⁻¹ * (vElem : G) * (z⁻¹)⁻¹ = (y : G) := by
          dsimp [vElem]
          group
        rw [hy]
        exact y.2
      have h := nine3Norm_conj (I := nineI V K) (P := P) hPnormI (P.inv_mem hz) vElem hmemConj
      have hyEq : (⟨z⁻¹ * (vElem : G) * (z⁻¹)⁻¹, hmemConj⟩ : ↥(nineI V K)) = y := by
        apply Subtype.ext
        dsimp [vElem]
        group
      rw [hyEq] at h
      exact h
    rw [h]
    exact Subgroup.mem_map_of_mem (nine3Norm (nineI V K) P hPnormI)
      (Subgroup.mem_subgroupOf.mpr ⟨hvU, hvR⟩)
  · rintro x ⟨y, hy, rfl⟩
    have hyinf : (y : G) ∈ U ⊓ pCoreOf 2 K := Subgroup.mem_subgroupOf.mp hy
    have hvR : z⁻¹ * (y : G) * z ∈ pCoreOf 2 K := by
      have h := (Nine3Core.mem_pCoreOf_conj_iff K (K.inv_mem hzK)).mp hyinf.2
      simpa using h
    have hvU : z⁻¹ * (y : G) * z ∈ CFSG.Quasithin.conjSubgroup U z := by
      rw [CFSG.Quasithin.mem_conjSubgroup_iff]
      have h : z * (z⁻¹ * (y : G) * z) * z⁻¹ = (y : G) := by group
      rw [h]
      exact hyinf.1
    have hvI : z⁻¹ * (y : G) * z ∈ nineI V K := hUIz ⟨hvU, hvR⟩
    have h : nine3Norm (nineI V K) P hPnormI ⟨z⁻¹ * (y : G) * z, hvI⟩ =
        nine3Norm (nineI V K) P hPnormI y := by
      have hmemConj : z⁻¹ * (y : G) * (z⁻¹)⁻¹ ∈ nineI V K := by
        simpa using hvI
      have h := nine3Norm_conj (I := nineI V K) (P := P) hPnormI (P.inv_mem hz) y hmemConj
      have hyEq : (⟨z⁻¹ * (y : G) * (z⁻¹)⁻¹, hmemConj⟩ : ↥(nineI V K)) =
          ⟨z⁻¹ * (y : G) * z, hvI⟩ := by
        apply Subtype.ext
        simp
      rwa [hyEq] at h
    rw [← h]
    exact Subgroup.mem_map_of_mem (nine3Norm (nineI V K) P hPnormI)
      (Subgroup.mem_subgroupOf.mpr ⟨hvU, hvR⟩)

theorem nine3_exists_conj_mem_omega (hc : Nine3Choice V T A K S X p g x)
    {P : Subgroup G} (hPK : P ≤ K) (hXP : X ≤ pCoreOf 2 K ⊔ P)
    {U : Subgroup G} (hU : U ∈ omegaIn V K (nineE V K)) :
    ∃ B ∈ nineOmegaIn V K S, ∃ y ∈ P, U = conjSubgroup B y := by
  obtain ⟨k, hk, hUk⟩ :=
    nine_two_transitive hc.core.hyp7 hc.core.rk_gt hc.core.hyp.base.toTwoPTwoIrred
      A (nine3_A_mem_omega hc) U hU
  have hmul : (K : Set G) = (S : Set G) * (X : Set G) :=
    TwoPTwo.mul_eq hc.core.hyp.base.toTwoPTwo
  have hk' : k ∈ (S : Set G) * (X : Set G) := hmul ▸ hk
  obtain ⟨s, hs, u, hu, hsu⟩ := Set.mem_mul.mp hk'
  have hB0ω : conjSubgroup A s ∈ omegaIn V K (nineE V K) :=
    conjSubgroup_mem_omegaIn (nine3_A_mem_omega hc) (hc.core.S_le_K hs)
  have hB0S : conjSubgroup A s ≤ S := by
    intro y hy
    have hyA : s * y * s⁻¹ ∈ A := CFSG.Quasithin.mem_conjSubgroup_iff.mp hy
    have h : y = s⁻¹ * (s * y * s⁻¹) * s := by group
    rw [h]
    exact S.mul_mem (S.mul_mem (S.inv_mem hs) (hc.core.A_mem_nineOmegaIn.2 hyA)) hs
  have hB0Ω : conjSubgroup A s ∈ nineOmegaIn V K S := ⟨hB0ω.1, hB0S⟩
  have huK : u ∈ K := hc.core.hyp.base.sylowP.le hu
  let uK : ↥K := ⟨u, huK⟩
  have hRsub : (pCoreOf 2 K).subgroupOf K = CFSG.pCore 2 ↥K :=
    CFSG.openPCoreOf_subgroupOf 2 K
  haveI : ((pCoreOf 2 K).subgroupOf K).Normal := by
    rw [hRsub]
    exact CFSG.pCore_normal
  have huKsup : uK ∈ (pCoreOf 2 K).subgroupOf K ⊔ P.subgroupOf K := by
    rw [← Subgroup.subgroupOf_sup (CFSG.LieType.BorelTits.pCoreOf_le 2 K) hPK]
    exact Subgroup.mem_subgroupOf.mpr (hXP hu)
  obtain ⟨rK, hrK, yK, hyK, hryK⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := (pCoreOf 2 K).subgroupOf K)
      (t := P.subgroupOf K) (x := uK)).mp huKsup
  have hr : (rK : G) ∈ pCoreOf 2 K := Subgroup.mem_subgroupOf.mp hrK
  have hy : (yK : G) ∈ P := Subgroup.mem_subgroupOf.mp hyK
  have hry : u = (rK : G) * (yK : G) := (congrArg Subtype.val hryK).symm
  have hBΩ : conjSubgroup (conjSubgroup A s) (rK : G) ∈ nineOmegaIn V K S :=
    hc.core.conjSubgroup_mem_nineOmegaIn hB0Ω hr
  refine ⟨conjSubgroup (conjSubgroup A s) (rK : G), hBΩ, (yK : G), hy, ?_⟩
  calc U = conjSubgroup A (s * u) := by rw [hUk, hsu]
    _ = conjSubgroup (conjSubgroup A s) u :=
        (CFSG.Quasithin.conjSubgroup_conjSubgroup A s u).symm
    _ = conjSubgroup (conjSubgroup A s) ((rK : G) * (yK : G)) := by rw [hry]
    _ = conjSubgroup (conjSubgroup (conjSubgroup A s) (rK : G)) (yK : G) :=
        (CFSG.Quasithin.conjSubgroup_conjSubgroup (conjSubgroup A s) (rK : G) (yK : G)).symm

theorem nine3_centralizer_P_le_J (hc : Nine3Choice V T A K S X p g x) (hI : Nine3IFacts V K S)
    [IsMulCommutative ↥(nineI V K)]
    {a : G} {P : Subgroup G} [Fintype ↥P] (ha : a ∈ A) (hPK : P ≤ K)
    (hPcard : Nat.card ↥P = p) (hodd : Odd (Nat.card ↥P))
    (hXP : X ≤ pCoreOf 2 K ⊔ P)
    (hinv : ∀ y ∈ P, a⁻¹ * y * a = y⁻¹) :
    nineI V K ⊓ Subgroup.centralizer (P : Set G) ≤
      ⨆ B ∈ nineOmegaIn V K S, B ⊓ pCoreOf 2 K := by
  classical
  let I := nineI V K
  let R := pCoreOf 2 K
  let J := ⨆ B ∈ nineOmegaIn V K S, B ⊓ R
  have hPnormI : P ≤ Subgroup.normalizer (nineI V K : Set G) := by
    intro z hz
    rw [← CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer]
    exact Nine3Core.conjSubgroup_nineI (hPK hz)
  have hpodd : Odd p := hc.core.hyp.base.prime.odd_of_ne_two hc.core.hyp.base.odd
  have hC_le_range : (Subgroup.centralizer (P : Set G) ⊓ I).subgroupOf I ≤
      (nine3Norm I P hPnormI).range := by
    intro x hx
    have hxG : ((x : G) ∈ Subgroup.centralizer (P : Set G)) := (Subgroup.mem_subgroupOf.mp hx).1
    have hxI : (x : G) ∈ I := (Subgroup.mem_subgroupOf.mp hx).2
    have hv : ∀ g ∈ P, g * (x : G) = (x : G) * g :=
      fun g hg => Subgroup.mem_centralizer_iff.mp hxG g hg
    have hexp : (x : G) * (x : G) = 1 := by
      have h := hI.abelian.2 (x : G) hxI
      simpa [pow_two] using h
    exact ⟨x, Subtype.ext (nine3Norm_of_centralizer hPnormI hPcard hpodd x hv hexp)⟩
  have hrange_le_J : (nine3Norm I P hPnormI).range ≤ J.subgroupOf I := by
    apply nine3Norm_range_le_of_image_le (I := I) (P := P) hPnormI
      (S := fun U : {U // U ∈ omegaIn V K (nineE V K)} => U.1 ⊓ R)
    · intro U
      exact le_iSup₂_of_le U.1 U.2 le_rfl
    · dsimp only [I, R]
      rw [nineI, iSup_subtype']
    · intro U
      obtain ⟨B, hB, y, hy, hUeq⟩ := nine3_exists_conj_mem_omega hc hPK hXP U.2
      rw [hUeq]
      rw [nine3Norm_image_conj (U := B) hc hI hPnormI hPK
        ⟨hB.1, hB.2.trans hc.core.S_le_K⟩ hy]
      intro z hz
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hz
      have hbR : (b : G) ∈ B ⊓ pCoreOf 2 K :=
        (Subgroup.mem_subgroupOf (H := B ⊓ R) (K := I) (h := b)).mp hb
      change (nine3Norm I P hPnormI b : G) ∈ J
      simpa using nine3Norm_mem_J hc hI hPnormI hPcard ha hinv hB hbR
  have hC_eq_range : (Subgroup.centralizer (P : Set G) ⊓ I).subgroupOf I =
      (nine3Norm I P hPnormI).range :=
    le_antisymm hC_le_range (nine3Norm_range_le_centralizer hPnormI)
  rintro x ⟨hxI, hxC⟩
  let xI : ↥I := ⟨x, hxI⟩
  have hx' : xI ∈ (Subgroup.centralizer (P : Set G) ⊓ I).subgroupOf I := ⟨hxC, hxI⟩
  have hxr : xI ∈ (nine3Norm I P hPnormI).range := hC_eq_range ▸ hx'
  have hxJ : xI ∈ J.subgroupOf I := hrange_le_J hxr
  have hxJ' : (xI : G) ∈ J :=
    (Subgroup.mem_subgroupOf (H := J) (K := I) (h := xI)).mp hxJ
  simpa using hxJ'

end CFSG.LocalAnalysis.WeakClosure81
