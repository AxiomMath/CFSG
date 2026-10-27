module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IModel
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IRootField
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IRootFieldTri
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1ILemmaA
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1ILemmaATri
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IK1b
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IPerfect
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.CurtisTits.ExceptionalQuasisimple
public import CFSG.LieType.CurtisTits.TwistedE6
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OddCenter

public section

namespace CFSG.StandardType.RCKK1I

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.RCKRP
  CFSG.StandardType.LieOddCover
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.StandardType.RCKSmall (RCKSmallTag)

private theorem rckK1Ias_center_quotient_bot_of_center_bot {K : Type*} [Group K]
    (h : Subgroup.center K = ⊥) :
    Subgroup.center (K ⧸ Subgroup.center K) = ⊥ := by
  let e : K ⧸ Subgroup.center K ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq h).trans (QuotientGroup.quotientBot (G := K))
  rw [eq_bot_iff]
  intro q hq
  rw [Subgroup.mem_bot]
  apply e.injective
  rw [map_one]
  have hqe : e q ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨q', rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hq q']
  exact Subgroup.mem_bot.mp (le_of_eq h hqe)

private theorem rckK1Ias_ker_comp_mk_le_center {K Jb : Type*} [Group K] [Group Jb]
    (φ : K →* Jb) (hkerφ : φ.ker ≤ Subgroup.center K)
    (hZ2 : Subgroup.center (K ⧸ Subgroup.center K) = ⊥) :
    ((QuotientGroup.mk' (Subgroup.center Jb)).comp φ).ker ≤ Subgroup.center K := by
  intro x hx
  have hxφ : φ x ∈ Subgroup.center Jb := by
    have hx' : (QuotientGroup.mk' (Subgroup.center Jb)) (φ x) = 1 := hx
    exact (QuotientGroup.eq_one_iff (N := Subgroup.center Jb) (φ x)).mp hx'
  rw [Subgroup.mem_center_iff] at hxφ
  have hmkx : (QuotientGroup.mk' (Subgroup.center K)) x ∈
      Subgroup.center (K ⧸ Subgroup.center K) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) q
    have hcomm : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center K := by
      apply hkerφ
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [(hxφ (φ y)).symm]
      group
    have h1 : (QuotientGroup.mk' (Subgroup.center K)) (x * y * x⁻¹ * y⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff (N := Subgroup.center K) _).mpr hcomm
    have h1' : (QuotientGroup.mk' (Subgroup.center K)) x *
        (QuotientGroup.mk' (Subgroup.center K)) y *
        ((QuotientGroup.mk' (Subgroup.center K)) x)⁻¹ *
        ((QuotientGroup.mk' (Subgroup.center K)) y)⁻¹ = 1 := by
      simpa only [map_mul, map_inv] using h1
    have key : (QuotientGroup.mk' (Subgroup.center K)) x *
        (QuotientGroup.mk' (Subgroup.center K)) y =
        ((QuotientGroup.mk' (Subgroup.center K)) x *
          (QuotientGroup.mk' (Subgroup.center K)) y *
          ((QuotientGroup.mk' (Subgroup.center K)) x)⁻¹ *
          ((QuotientGroup.mk' (Subgroup.center K)) y)⁻¹) *
          ((QuotientGroup.mk' (Subgroup.center K)) y *
          (QuotientGroup.mk' (Subgroup.center K)) x) := by group
    rw [key, h1', one_mul]
  rw [hZ2, Subgroup.mem_bot] at hmkx
  rw [Subgroup.mem_center_iff]
  intro y
  exact (Subgroup.mem_center_iff.mp
    ((QuotientGroup.eq_one_iff (N := Subgroup.center K) x).mp hmkx)) y

private theorem rckK1Ias_simple_centerQuot {Jb : Type*} [Group Jb]
    (hmark : LargeEvenMarking Jb (fun lab _ _ _ _ _ =>
      ggSixRCKLabelRow lab = .I ∧ ¬ RCKSmallTag lab.tag)) :
    IsSimpleGroup (Jb ⧸ Subgroup.center Jb) := by
  obtain ⟨-, lab, hlab, hraw⟩ := hmark
  obtain ⟨R, _, I, F, hq⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨hRsimple, -, hθ⟩ := hq
  obtain ⟨θ, -⟩ := hθ
  exact θ.isSimpleGroup

private theorem rckK1Ias_center_bot_triD4
    {F : Type} [Field F] [Finite F] {σ : F →+* F}
    {g : ℕ} (hF : TriField F σ g) :
    Subgroup.center (triD4Universal F σ).K = ⊥ := by
  have hq : 2 ≤ 2 ^ g := Nat.le_self_pow (by have := hF.1; omega) 2
  have h := CFSG.LieType.Steinberg.CentralExt.TrialityClosed.twistedGroup_center_eq_bot_of_card
    (K := F) hq hF.2.1 hF.2.2
  exact h

private theorem rckK1Ias_le_of_isPGroup_le_sup {K : Type*} [Group K] [Finite K]
    {H Z P : Subgroup K} [Z.Normal]
    (hH2 : IsPGroup 2 H) (hZcent : Z ≤ Subgroup.center K) (hZodd : Odd (Nat.card Z))
    (hdisj : H ⊓ Z = ⊥) (hP2 : IsPGroup 2 P) (hP : P ≤ H ⊔ Z) : P ≤ H := by
  classical
  let M : Subgroup K := H ⊔ Z
  have hHM : H ≤ M := le_sup_left
  have hZM : Z ≤ M := le_sup_right
  have hHnorm : (H.subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hHM]
    intro h k hh hk
    obtain ⟨y, hy, z, hz, rfl⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := H) (t := Z)).mp hk
    have hzh : z * h * z⁻¹ = h := by
      have hc := Subgroup.mem_center_iff.mp (hZcent hz) h
      rw [hc.symm]
      group
    have h1 : (y * z) * h * (y * z)⁻¹ = y * (z * h * z⁻¹) * y⁻¹ := by group
    rw [h1, hzh]
    exact H.mul_mem (H.mul_mem hy hh) (H.inv_mem hy)
  have hZrelH : Z.relIndex H = Nat.card H := by
    have h := Subgroup.relIndex_mul_card (H := Z) (K := H)
    rw [inf_comm, hdisj, Subgroup.card_bot, mul_one] at h
    exact h
  have hMcard : Nat.card M = Nat.card H * Nat.card Z := by
    have h := Subgroup.relIndex_mul_card (H := Z) (K := M)
    rw [show Z ⊓ M = Z from (inf_eq_left).mpr hZM,
      Subgroup.relIndex_sup_right (K := Z) (H := H), hZrelH] at h
    exact h.symm
  have hsubcard : Nat.card (H.subgroupOf M) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHM).toEquiv
  have hindex : (H.subgroupOf M).index = Nat.card Z := by
    rw [Subgroup.index_eq_card_div, hsubcard, hMcard]
    exact Nat.mul_div_right (Nat.card Z) (Nat.card_pos (α := H))
  haveI : (H.subgroupOf M).Normal := hHnorm
  intro p hp
  let q : M →* M ⧸ (H.subgroupOf M) := QuotientGroup.mk' (H.subgroupOf M)
  have hP'2 : IsPGroup 2 (P.subgroupOf M) := hP2.comap_subtype
  have hq2 : IsPGroup 2 ((P.subgroupOf M).map q) := hP'2.map q
  have hcard_dvd : Nat.card ((P.subgroupOf M).map q) ∣ (H.subgroupOf M).index := by
    rw [Subgroup.index_eq_card]
    exact Subgroup.card_subgroup_dvd_card _
  have hcard_odd : Odd (Nat.card ((P.subgroupOf M).map q)) := by
    rw [hindex] at hcard_dvd
    exact hZodd.of_dvd_nat hcard_dvd
  have hcard1 : Nat.card ((P.subgroupOf M).map q) = 1 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hq2
    have hcop : Nat.Coprime (2 ^ k) (H.subgroupOf M).index := by
      rw [hindex]
      exact (hZodd.coprime_two_right.symm).pow_left k
    rw [hk] at hcard_dvd ⊢
    exact Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hcard_dvd
  have hmapbot : (P.subgroupOf M).map q = ⊥ :=
    (Subgroup.eq_bot_iff_card _).mpr hcard1
  have hle : P.subgroupOf M ≤ H.subgroupOf M := by
    rw [← QuotientGroup.ker_mk' (H.subgroupOf M)]
    exact (Subgroup.map_eq_bot_iff _).mp hmapbot
  have hpM : p ∈ M := hP hp
  have hmemP' : (⟨p, hpM⟩ : M) ∈ P.subgroupOf M := by
    rw [Subgroup.mem_subgroupOf]
    exact hp
  exact Subgroup.mem_subgroupOf.mp (hle hmemP')

private theorem rckK1Ias_rootFieldExact_map {K X : Type*} [Group K] [Group X] [Finite K]
    (ψ : K →* X) (H : Subgroup K) {Fq : Type} [Field Fq]
    (ε : Multiplicative Fq ≃* ↥H) (hRF : RCKRootFieldExact H Fq ε)
    (hψsurj : Function.Surjective ψ) (hcent : ψ.ker ≤ Subgroup.center K)
    (hZodd : Odd (Nat.card ψ.ker)) (hdisj : H ⊓ ψ.ker = ⊥) (hH2 : IsPGroup 2 H) :
    ∃ ε' : Multiplicative Fq ≃* ↥(H.map ψ), RCKRootFieldExact (H.map ψ) Fq ε' ∧
      ∀ t : Fq, (ε' (Multiplicative.ofAdd t) : X) = ψ (ε (Multiplicative.ofAdd t)) := by
  classical
  have hinj : Function.Injective (ψ.comp H.subtype) := by
    intro a b hab
    have hmem : (a : K)⁻¹ * b ∈ H ⊓ ψ.ker := by
      refine ⟨H.mul_mem (H.inv_mem a.2) b.2, ?_⟩
      change ψ ((a : K)⁻¹ * b) = 1
      have hab' : ψ (a : K) = ψ (b : K) := hab
      rw [map_mul, map_inv, hab', inv_mul_cancel]
    rw [hdisj, Subgroup.mem_bot] at hmem
    exact Subtype.ext (inv_mul_eq_one.mp hmem)
  let g0 : ↥H →* ↥(H.map ψ) :=
    (ψ.comp H.subtype).codRestrict (H.map ψ) (fun x => Subgroup.mem_map_of_mem ψ x.2)
  have hg0_inj : Function.Injective g0 := by
    intro a b hab
    apply hinj
    simpa only [g0, MonoidHom.codRestrict_apply, MonoidHom.comp_apply, Subgroup.subtype_apply]
      using congrArg Subtype.val hab
  have hg0_surj : Function.Surjective g0 := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let e : ↥H ≃* ↥(H.map ψ) := MulEquiv.ofBijective g0 ⟨hg0_inj, hg0_surj⟩
  let ε' : Multiplicative Fq ≃* ↥(H.map ψ) := ε.trans e
  have hε' : ∀ t : Fq, (ε' (Multiplicative.ofAdd t) : X) = ψ (ε (Multiplicative.ofAdd t)) := by
    intro t
    rfl
  refine ⟨ε', ?_, hε'⟩
  refine ⟨?_, ?_⟩
  · intro l hl
    obtain ⟨h, hh⟩ := hRF.1 l hl
    refine ⟨ψ h, ?_⟩
    intro t
    change ψ h * (ε' (Multiplicative.ofAdd t) : X) * (ψ h)⁻¹ =
      (ε' (Multiplicative.ofAdd (l * t)) : X)
    rw [hε' t, hε' (l * t), ← map_mul, ← map_inv, ← map_mul, hh]
  · intro n hn
    obtain ⟨k, rfl⟩ := hψsurj n
    have hconj_le : H.map (MulAut.conj k).toMonoidHom ≤ H ⊔ ψ.ker := by
      intro x hx
      obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hx
      have hmem : ψ (k * h * k⁻¹) ∈ H.map ψ := by
        have hh' : ψ h ∈ H.map ψ := Subgroup.mem_map_of_mem ψ hh
        have hn' := (Subgroup.mem_normalizer_iff.mp hn (ψ h)).mp hh'
        simpa only [map_mul, map_inv] using hn'
      obtain ⟨h', hh', hh''⟩ := Subgroup.mem_map.mp hmem
      refine (Subgroup.mem_sup_of_normal_right (s := H) (t := ψ.ker)).mpr
        ⟨h', hh', h'⁻¹ * (k * h * k⁻¹), ?_, by
          change h' * (h'⁻¹ * (k * h * k⁻¹)) = k * h * k⁻¹
          group⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      have hh4 : ψ (k * h * k⁻¹) = ψ h' := hh''.symm
      rw [hh4]
      group
    have hP2 : IsPGroup 2 (H.map (MulAut.conj k).toMonoidHom) :=
      hH2.map (MulAut.conj k).toMonoidHom
    have hleH : H.map (MulAut.conj k).toMonoidHom ≤ H :=
      rckK1Ias_le_of_isPGroup_le_sup hH2 hcent hZodd hdisj hP2 hconj_le
    have hconj_eq : H.map (MulAut.conj k).toMonoidHom = H :=
      Subgroup.eq_of_le_of_card_ge hleH
        (by rw [Subgroup.card_map_of_injective (MulAut.conj k).injective])
    have hk : k ∈ Subgroup.normalizer (H : Set K) :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).mpr hconj_eq
    obtain ⟨l, hl, hh⟩ := hRF.2 k hk
    refine ⟨l, hl, ?_⟩
    intro t
    change ψ k * (ε' (Multiplicative.ofAdd t) : X) * (ψ k)⁻¹ =
      (ε' (Multiplicative.ofAdd (l * t)) : X)
    rw [hε' t, hε' (l * t), ← map_mul, ← map_inv, ← map_mul, hh]

theorem rckRowK1_I_of
    (hcov : GGLieOddCover) (hIRG : RCKIntrinsicRoot) : RCKRowK1NS .I RCKPosRootSub := by
  intro Jb _ _ hodd hmark
  have hXsimple : IsSimpleGroup (Jb ⧸ Subgroup.center Jb) := rckK1Ias_simple_centerQuot hmark
  rcases rckK1I_model hcov hodd hmark with
    ⟨t, n, f, φ, ht, hadm, hf2, hφsurj, hφker⟩ |
    ⟨F, hFfield, hFfinite, σ, g, φ, hTri, hg2, hφsurj, hφker⟩
  ·
    have hZ2 : Subgroup.center ((ggU t n f).K ⧸ Subgroup.center (ggU t n f).K) = ⊥ := by
      haveI : Group.IsPerfect (ggU t n f).K := ⟨rckK1I_ggU_perfect ht hadm⟩
      exact Group.IsPerfect.center_quotient_center_eq_bot _
    let ψ : (ggU t n f).K →* Jb ⧸ Subgroup.center Jb :=
      (QuotientGroup.mk' (Subgroup.center Jb)).comp φ
    have hψsurj : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hφsurj
    have hψker : ψ.ker ≤ Subgroup.center (ggU t n f).K :=
      rckK1Ias_ker_comp_mk_le_center φ hφker hZ2
    haveI hfin : Finite (ggU t n f).K :=
      CFSG.StandardType.LieKnownR2.OddCenter.finite_ggU ht hadm
    have hZodd : Odd (Nat.card ψ.ker) :=
      (CFSG.StandardType.LieKnownR2.OddCenter.odd_card_center_ggU
        (t := t) (n := n) (f := f) ht hadm).of_dvd_nat
        (Subgroup.card_dvd_of_le hψker)
    obtain ⟨β, hβ, hlong, Fq, hFqfield, hFqfinite, ε, hcardFq, hRF⟩ :=
      rckK1I_rootField_ggU ht hadm
    have hcardH : Nat.card ((ggU t n f).D.rootGroup β) = 2 ^ f := by
      rw [← Nat.card_congr ε.toEquiv, Nat.card_congr Multiplicative.toAdd, hcardFq]
    have hH2 : IsPGroup 2 ((ggU t n f).D.rootGroup β) := IsPGroup.of_card hcardH
    haveI : Fintype Fq := Fintype.ofFinite Fq
    haveI : CharP Fq 2 := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact charP_of_card_eq_prime_pow (p := 2) (f := f) (by
        rw [← Nat.card_eq_fintype_card]; exact hcardFq)
    have hdisj : (ggU t n f).D.rootGroup β ⊓ ψ.ker = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      obtain ⟨hxH, hxker⟩ := hx
      have hdvdH : orderOf x ∣ Nat.card ((ggU t n f).D.rootGroup β) :=
        Subgroup.orderOf_dvd_natCard _ hxH
      have hdvdZ : orderOf x ∣ Nat.card ψ.ker := Subgroup.orderOf_dvd_natCard _ hxker
      have hcop : Nat.Coprime (Nat.card ((ggU t n f).D.rootGroup β)) (Nat.card ψ.ker) := by
        rw [hcardH]
        exact (hZodd.coprime_two_right.symm).pow_left f
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvdH hdvdZ)
    obtain ⟨ε', hRF', hε'⟩ := rckK1Ias_rootFieldExact_map ψ ((ggU t n f).D.rootGroup β)
      ε hRF hψsurj hψker hZodd hdisj hH2
    have hq : 4 ≤ Nat.card Fq := by rw [hcardFq]; exact four_le_two_pow hf2
    have hA : ∀ α : MulAut (Jb ⧸ Subgroup.center Jb),
        α (ε' (Multiplicative.ofAdd 1) : Jb ⧸ Subgroup.center Jb) =
          (ε' (Multiplicative.ofAdd 1) : Jb ⧸ Subgroup.center Jb) →
        (((ggU t n f).D.rootGroup β).map ψ).map α.toMonoidHom =
          ((ggU t n f).D.rootGroup β).map ψ := by
      intro α hα
      let x₀ : (ggU t n f).K := ε (Multiplicative.ofAdd (1 : Fq))
      have hx0 : x₀ ∈ (ggU t n f).D.rootGroup β :=
        (ε (Multiplicative.ofAdd (1 : Fq))).2
      have hx01 : ψ x₀ ≠ 1 := by
        intro h
        have hmem : x₀ ∈ (ggU t n f).D.rootGroup β ⊓ ψ.ker := ⟨hx0, h⟩
        rw [hdisj, Subgroup.mem_bot] at hmem
        have h1 : Multiplicative.ofAdd (1 : Fq) = 1 := by
          apply ε.injective
          apply Subtype.ext
          show (ε (Multiplicative.ofAdd (1 : Fq)) : (ggU t n f).K) =
            (ε 1 : (ggU t n f).K)
          rw [map_one ε]
          simpa only [x₀, Subgroup.coe_one] using hmem
        have h2 : (1 : Fq) = 0 := by
          have := congrArg Multiplicative.toAdd h1
          simpa using this
        exact one_ne_zero h2
      exact rckK1I_lemmaA hIRG hXsimple ⟨ht, hadm⟩ ψ hψsurj hψker hβ hlong hx0 hx01 α (by
        rwa [hε' 1] at hα)
    obtain ⟨Vb, hVbR, hdata⟩ := rckK1I_K1b hq ε' hRF' hA
    refine ⟨(ε' (Multiplicative.ofAdd 1) : Jb ⧸ Subgroup.center Jb), Vb, hdata, ?_⟩
    have hsubβ : ((ggU t n f).D.rootGroup β).map
        (MulAut.conj (1 : (ggU t n f).K)).toMonoidHom = (ggU t n f).D.rootGroup β := by
      rw [map_one MulAut.conj]
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro hx
        exact ⟨x, hx, by simp⟩
    have hsubmβ : ((ggU t n f).D.rootGroup (-β)).map
        (MulAut.conj (1 : (ggU t n f).K)).toMonoidHom = (ggU t n f).D.rootGroup (-β) := by
      rw [map_one MulAut.conj]
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro hx
        exact ⟨x, hx, by simp⟩
    have hpos : GGRootPosJ (⊤ : Subgroup Jb)
        (((ggU t n f).D.rootGroup β).map φ)
        (((ggU t n f).D.rootGroup (-β)).map φ) :=
      Or.inl ⟨t, n, f, β, ht, hadm.2.1, hlong,
        ⟨φ, MonoidHom.range_eq_top_of_surjective φ hφsurj, hφker, 1,
          by rw [ggRootSub, hsubβ], by rw [ggRootSub, hsubmβ]⟩⟩
    have hmap : ((ggU t n f).D.rootGroup β).map ψ =
        (((ggU t n f).D.rootGroup β).map φ).map
          (QuotientGroup.mk' (Subgroup.center Jb)) := by
      rw [Subgroup.map_map]
    exact ⟨((ggU t n f).D.rootGroup β).map φ,
      ((ggU t n f).D.rootGroup (-β)).map φ, hpos, by rwa [hmap] at hVbR⟩
  ·
    haveI : Fintype F := Fintype.ofFinite F
    haveI hfin : Finite (triD4Universal F σ).K := by
      change Finite (CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ)
      infer_instance
    have hZcenter : Subgroup.center (triD4Universal F σ).K = ⊥ :=
      rckK1Ias_center_bot_triD4 hTri
    have hZ2 : Subgroup.center ((triD4Universal F σ).K ⧸
        Subgroup.center (triD4Universal F σ).K) = ⊥ :=
      rckK1Ias_center_quotient_bot_of_center_bot hZcenter
    let ψ : (triD4Universal F σ).K →* Jb ⧸ Subgroup.center Jb :=
      (QuotientGroup.mk' (Subgroup.center Jb)).comp φ
    have hψsurj : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hφsurj
    have hψker : ψ.ker ≤ Subgroup.center (triD4Universal F σ).K :=
      rckK1Ias_ker_comp_mk_le_center φ hφker hZ2
    have hZodd : Odd (Nat.card ψ.ker) := by
      have hZoddK : Odd (Nat.card (Subgroup.center (triD4Universal F σ).K)) := by
        rw [hZcenter]
        rw [Subgroup.card_bot]
        exact ⟨0, by norm_num⟩
      exact hZoddK.of_dvd_nat (Subgroup.card_dvd_of_le hψker)
    obtain ⟨β, hβ, hlong, Fq, hFqfield, hFqfinite, ε, hcardFq, hRF⟩ :=
      rckK1I_rootField_triD4 hTri
    have hcardH : Nat.card ((triD4Universal F σ).D.rootGroup β) = 2 ^ g := by
      rw [← Nat.card_congr ε.toEquiv, Nat.card_congr Multiplicative.toAdd, hcardFq]
    have hH2 : IsPGroup 2 ((triD4Universal F σ).D.rootGroup β) := IsPGroup.of_card hcardH
    haveI : Fintype Fq := Fintype.ofFinite Fq
    haveI : CharP Fq 2 := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact charP_of_card_eq_prime_pow (p := 2) (f := g) (by
        rw [← Nat.card_eq_fintype_card]; exact hcardFq)
    have hdisj : (triD4Universal F σ).D.rootGroup β ⊓ ψ.ker = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      obtain ⟨hxH, hxker⟩ := hx
      have hdvdH : orderOf x ∣ Nat.card ((triD4Universal F σ).D.rootGroup β) :=
        Subgroup.orderOf_dvd_natCard _ hxH
      have hdvdZ : orderOf x ∣ Nat.card ψ.ker := Subgroup.orderOf_dvd_natCard _ hxker
      have hcop : Nat.Coprime (Nat.card ((triD4Universal F σ).D.rootGroup β))
          (Nat.card ψ.ker) := by
        rw [hcardH]
        exact (hZodd.coprime_two_right.symm).pow_left g
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvdH hdvdZ)
    obtain ⟨ε', hRF', hε'⟩ := rckK1Ias_rootFieldExact_map ψ ((triD4Universal F σ).D.rootGroup β)
      ε hRF hψsurj hψker hZodd hdisj hH2
    have hq : 4 ≤ Nat.card Fq := by rw [hcardFq]; exact four_le_two_pow hg2
    have hA : ∀ α : MulAut (Jb ⧸ Subgroup.center Jb),
        α (ε' (Multiplicative.ofAdd 1) : Jb ⧸ Subgroup.center Jb) =
          (ε' (Multiplicative.ofAdd 1) : Jb ⧸ Subgroup.center Jb) →
        (((triD4Universal F σ).D.rootGroup β).map ψ).map α.toMonoidHom =
          ((triD4Universal F σ).D.rootGroup β).map ψ := by
      intro α hα
      let x₀ : (triD4Universal F σ).K := ε (Multiplicative.ofAdd (1 : Fq))
      have hx0 : x₀ ∈ (triD4Universal F σ).D.rootGroup β :=
        (ε (Multiplicative.ofAdd (1 : Fq))).2
      have hx01 : ψ x₀ ≠ 1 := by
        intro h
        have hmem : x₀ ∈ (triD4Universal F σ).D.rootGroup β ⊓ ψ.ker := ⟨hx0, h⟩
        rw [hdisj, Subgroup.mem_bot] at hmem
        have h1 : Multiplicative.ofAdd (1 : Fq) = 1 := by
          apply ε.injective
          apply Subtype.ext
          show (ε (Multiplicative.ofAdd (1 : Fq)) : (triD4Universal F σ).K) =
            (ε 1 : (triD4Universal F σ).K)
          rw [map_one ε]
          simpa only [x₀, Subgroup.coe_one] using hmem
        have h2 : (1 : Fq) = 0 := by
          have := congrArg Multiplicative.toAdd h1
          simpa using this
        exact one_ne_zero h2
      exact rckK1I_lemmaA_triD4 hIRG hXsimple hTri ψ hψsurj hψker hβ hlong hx0 hx01 α (by
        rwa [hε' 1] at hα)
    obtain ⟨Vb, hVbR, hdata⟩ := rckK1I_K1b hq ε' hRF' hA
    refine ⟨(ε' (Multiplicative.ofAdd 1) : Jb ⧸ Subgroup.center Jb), Vb, hdata, ?_⟩
    have hsubβ : ((triD4Universal F σ).D.rootGroup β).map
        (MulAut.conj (1 : (triD4Universal F σ).K)).toMonoidHom =
          (triD4Universal F σ).D.rootGroup β := by
      rw [map_one MulAut.conj]
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro hx
        exact ⟨x, hx, by simp⟩
    have hsubmβ : ((triD4Universal F σ).D.rootGroup (-β)).map
        (MulAut.conj (1 : (triD4Universal F σ).K)).toMonoidHom =
          (triD4Universal F σ).D.rootGroup (-β) := by
      rw [map_one MulAut.conj]
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro hx
        exact ⟨x, hx, by simp⟩
    have hpos : GGRootPosJ (⊤ : Subgroup Jb)
        (((triD4Universal F σ).D.rootGroup β).map φ)
        (((triD4Universal F σ).D.rootGroup (-β)).map φ) :=
      Or.inr ⟨F, hFfield, hFfinite, σ, g, β, hTri, hlong,
        ⟨φ, MonoidHom.range_eq_top_of_surjective φ hφsurj, hφker, 1,
          by rw [ggRootSub, hsubβ], by rw [ggRootSub, hsubmβ]⟩⟩
    have hmap : ((triD4Universal F σ).D.rootGroup β).map ψ =
        (((triD4Universal F σ).D.rootGroup β).map φ).map
          (QuotientGroup.mk' (Subgroup.center Jb)) := by
      rw [Subgroup.map_map]
    exact ⟨((triD4Universal F σ).D.rootGroup β).map φ,
      ((triD4Universal F σ).D.rootGroup (-β)).map φ, hpos, by rwa [hmap] at hVbR⟩

end CFSG.StandardType.RCKK1I
