module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIModel
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIBInner
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IPerfect
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2Items
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OddCenter
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortTransport

public section

namespace CFSG.StandardType.RCKK1II

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.RCKRP
  CFSG.StandardType.LieOddCover CFSG.Open
open scoped commutatorElement

@[expose] def RCKIIPair
    (t : StatedLieTag) (n : ℕ) : Prop :=
  ∃ (β : Fin (ggU t n 1).D.rank → ℤ) (x : (ggU t n 1).K) (V : Subgroup (ggU t n 1).K),
    β ∈ (ggU t n 1).D.roots ∧ GGLongRoot (ggU t n 1).D β ∧
    (ggU t n 1).D.rootGroup β = Subgroup.zpowers x ∧ x * x = 1 ∧ x ≠ 1 ∧
    x ∈ V ∧ IsElemAbelian 2 V ∧ Nat.card V = 4 ∧
    V ≤ pCoreOf 2 (Subgroup.normalizer ((ggU t n 1).D.rootGroup β : Set (ggU t n 1).K)) ∧
    ∀ v ∈ V, v ≠ 1 → ∃ j : (ggU t n 1).K, v = j * x * j⁻¹

private theorem rckBP_orderOf_eq_two {G : Type*} [Group G] {x : G} (hx1 : x ≠ 1)
    (hx2 : x * x = 1) : orderOf x = 2 := by
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hx2)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hx1
  · exact h

private theorem rckBP_ker_conj {G : Type*} [Group G] :
    (MulAut.conj : G →* MulAut G).ker = Subgroup.center G := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h y
    have h1 : MulAut.conj x y = y := by
      have h2 := congrArg (fun f : MulAut G => f y) h
      simpa using h2
    rw [MulAut.conj_apply] at h1
    calc y * x = (x * y * x⁻¹) * x := by rw [h1]
      _ = x * y := by group
  · intro h
    ext y
    have h1 : MulAut.conj x y = y := by
      rw [MulAut.conj_apply]
      rw [← h y]
      group
    simpa using h1

private theorem rckBP_ker_comp_mk_le_center {K Jb : Type*} [Group K] [Group Jb]
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

private theorem rckBP_inf_ker_eq_bot {G H : Type*} [Group G] [Group H] [Finite G]
    (ψ : G →* H) {V : Subgroup G} (hV2 : IsPGroup 2 V) (hodd : Odd (Nat.card ψ.ker)) :
    V ⊓ ψ.ker = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  obtain ⟨hyV, hyK⟩ := hy
  have hdvdV : orderOf y ∣ Nat.card V := Subgroup.orderOf_dvd_natCard _ hyV
  have hdvdK : orderOf y ∣ Nat.card ψ.ker := Subgroup.orderOf_dvd_natCard _ hyK
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hV2
  have hcop : Nat.Coprime (2 ^ k) (Nat.card ψ.ker) := hodd.coprime_two_right.symm.pow_left k
  rw [hk] at hdvdV
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvdV hdvdK)

private theorem rckBP_card_map_of_disjoint {G H : Type*} [Group G] [Group H]
    (ψ : G →* H) {V : Subgroup G} (hdisj : V ⊓ ψ.ker = ⊥) :
    Nat.card (V.map ψ) = Nat.card V := by
  have hinj : Function.Injective (ψ.comp V.subtype) := by
    intro a b hab
    have hab' : ψ (a : G) = ψ (b : G) := hab
    have hmem : (a : G)⁻¹ * b ∈ V ⊓ ψ.ker := by
      refine ⟨V.mul_mem (V.inv_mem a.2) b.2, ?_⟩
      show ψ ((a : G)⁻¹ * b) = 1
      rw [map_mul, map_inv, hab']
      group
    rw [hdisj, Subgroup.mem_bot] at hmem
    exact Subtype.ext (inv_mul_eq_one.mp hmem)
  let g0 : ↥V →* ↥(V.map ψ) :=
    (ψ.comp V.subtype).codRestrict (V.map ψ) (fun x => Subgroup.mem_map_of_mem ψ x.2)
  have hg0inj : Function.Injective g0 := by
    intro a b hab
    apply hinj
    simpa only [g0, MonoidHom.codRestrict_apply, MonoidHom.comp_apply, Subgroup.subtype_apply]
      using congrArg Subtype.val hab
  have hg0surj : Function.Surjective g0 := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let e : ↥V ≃* ↥(V.map ψ) := MulEquiv.ofBijective g0 ⟨hg0inj, hg0surj⟩
  exact (Nat.card_congr e.toEquiv).symm

private theorem rckBP_commutator_pCore_le {U X : Type} [Group U] [Group X] [Finite X]
    {ψ : U →* X} (hker : ψ.ker ≤ Subgroup.center U) (hodd : Odd (Nat.card ψ.ker))
    {Rr Q : Subgroup U} (hRr : IsPGroup 2 Rr)
    (hC2 : pCoreOf 2 (Subgroup.normalizer (Rr : Set U)) ≤ Q) (hcomm : ⁅Q, Q⁆ ≤ Rr) :
    ⁅pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer ((Rr.map ψ : Subgroup X) : Set X)),
        pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer ((Rr.map ψ : Subgroup X) : Set X))⁆ ≤
      Rr.map ψ := by
  have hkerN : ψ.ker ≤ Subgroup.normalizer (Rr : Set U) :=
    hker.trans (Subgroup.center_le_normalizer (Rr : Set U))
  have hNmap : (Subgroup.normalizer (Rr : Set U)).map ψ =
      ψ.range ⊓ Subgroup.normalizer ((Rr.map ψ : Subgroup X) : Set X) :=
    CFSG.StandardType.LieKnownR2.map_normalizer_eq_range_inf_normalizer_map hker hodd hRr
  have hpCore : (pCoreOf 2 (Subgroup.normalizer (Rr : Set U))).map ψ =
      pCoreOf 2 ((Subgroup.normalizer (Rr : Set U)).map ψ) :=
    CFSG.StandardType.LieKnownR2.map_pCoreOf_eq_of_odd_central_ker hker hodd hkerN
  rw [← hNmap, ← hpCore]
  have hle : (pCoreOf 2 (Subgroup.normalizer (Rr : Set U))).map ψ ≤ Q.map ψ :=
    Subgroup.map_mono hC2
  exact (Subgroup.commutator_le_map_commutator hle hle).trans (Subgroup.map_mono hcomm)

theorem rckRowIIAt_of_pair
    (t : StatedLieTag) (n : ℕ) (hpos : GGPosTag t) (hadm : StatedLieAdmissible t n 2 1)
    (hI : ∀ (X : Type) [Group X] [Finite X] (φ : (ggU t n 1).K →* X),
      φ.ker ≤ Subgroup.center (ggU t n 1).K →
      ∀ (β : Fin (ggU t n 1).D.rank → ℤ), β ∈ (ggU t n 1).D.roots →
        GGLongRoot (ggU t n 1).D β → ∀ u : (ggU t n 1).K,
          GGRootInnerAt φ.range (ggRootSub (ggU t n 1).D φ β u))
    (hC : ∀ (β : Fin (ggU t n 1).D.rank → ℤ), β ∈ (ggU t n 1).D.roots →
      GGLongRoot (ggU t n 1).D β → ∀ (u : (ggU t n 1).K) (Rr Q : Subgroup (ggU t n 1).K),
        Rr = ggRootSub (ggU t n 1).D (MonoidHom.id (ggU t n 1).K) β u →
        Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set (ggU t n 1).K)) → ⁅Q, Q⁆ ≤ Rr)
    (hP : RCKIIPair t n) : RCKRowIIAt t n := by
  intro Jb _ _ hoddJb φ hφsurj hφker
  haveI hperfU : Group.IsPerfect (ggU t n 1).K := ⟨RCKK1I.rckK1I_ggU_perfect hpos hadm⟩
  haveI hfinU : Finite (ggU t n 1).K :=
    CFSG.StandardType.LieKnownR2.OddCenter.finite_ggU hpos hadm
  have hZoddU : Odd (Nat.card (Subgroup.center (ggU t n 1).K)) :=
    CFSG.StandardType.LieKnownR2.OddCenter.odd_card_center_ggU hpos hadm
  have hZ2U : Subgroup.center ((ggU t n 1).K ⧸ Subgroup.center (ggU t n 1).K) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot _
  haveI hperfJb : Group.IsPerfect Jb := Group.IsPerfect.ofSurjective hφsurj
  have hZJb : Subgroup.center (Jb ⧸ Subgroup.center Jb) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot _
  let ψ : (ggU t n 1).K →* Jb ⧸ Subgroup.center Jb :=
    (QuotientGroup.mk' (Subgroup.center Jb)).comp φ
  have hψsurj : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hφsurj
  have hψrange : ψ.range = ⊤ := MonoidHom.range_eq_top.mpr hψsurj
  have hψker : ψ.ker ≤ Subgroup.center (ggU t n 1).K :=
    rckBP_ker_comp_mk_le_center φ hφker hZ2U
  have hψodd : Odd (Nat.card ψ.ker) := hZoddU.of_dvd_nat (Subgroup.card_dvd_of_le hψker)
  obtain ⟨β, x, V, hβ, hlong, hroot, hx2, hx1, hxV, hVab, hVcard, hVN, hconj⟩ := hP
  let rb : Jb ⧸ Subgroup.center Jb := ψ x
  let Vb : Subgroup (Jb ⧸ Subgroup.center Jb) := V.map ψ
  have hxroot : x ∈ (ggU t n 1).D.rootGroup β := by
    rw [hroot]; exact Subgroup.mem_zpowers x
  have hxord : orderOf x = 2 := rckBP_orderOf_eq_two hx1 hx2
  have hrb2 : rb * rb = 1 := by
    show ψ x * ψ x = 1
    rw [← map_mul, hx2, map_one]
  have hrb1 : rb ≠ 1 := by
    intro h
    have hxker : x ∈ ψ.ker := h
    have hdvd2 : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hx2)
    have hdvdZ : orderOf x ∣ Nat.card ψ.ker := Subgroup.orderOf_dvd_natCard _ hxker
    have hcop : Nat.Coprime 2 (Nat.card ψ.ker) := hψodd.coprime_two_right.symm
    have hone : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd2 hdvdZ
    exact hx1 (orderOf_eq_one_iff.mp hone)
  have hrbord : orderOf rb = 2 := rckBP_orderOf_eq_two hrb1 hrb2
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (p := 2) (n := 2) (by rw [hVcard]; norm_num)
  have hVdisj : V ⊓ ψ.ker = ⊥ := rckBP_inf_ker_eq_bot ψ hV2 hψodd
  let Rr : Subgroup (ggU t n 1).K := (ggU t n 1).D.rootGroup β
  let Q : Subgroup (ggU t n 1).K := pCoreOf 2 (Subgroup.normalizer (Rr : Set _))
  have hRr2 : IsPGroup 2 Rr := by
    show IsPGroup 2 ((ggU t n 1).D.rootGroup β)
    rw [hroot]
    exact IsPGroup.of_card (p := 2) (n := 1) (by rw [Nat.card_zpowers, hxord]; norm_num)
  have hRrmap : Rr.map ψ = Subgroup.zpowers rb := by
    show ((ggU t n 1).D.rootGroup β).map ψ = Subgroup.zpowers rb
    rw [hroot, MonoidHom.map_zpowers]
  have hggid : ggRootSub (ggU t n 1).D (MonoidHom.id (ggU t n 1).K) β 1 =
      (ggU t n 1).D.rootGroup β := by
    rw [ggRootSub]
    ext y
    simp [MulAut.conj_apply]
  have hRrEq : Rr = ggRootSub (ggU t n 1).D (MonoidHom.id (ggU t n 1).K) β 1 := by
    show (ggU t n 1).D.rootGroup β = ggRootSub (ggU t n 1).D (MonoidHom.id _) β 1
    rw [hggid]
  have hQEq : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set _)) := rfl
  have hcomm : ⁅Q, Q⁆ ≤ Rr := hC β hβ hlong 1 Rr Q hRrEq hQEq
  have hkerconj : (MulAut.conj : Jb ⧸ Subgroup.center Jb →* MulAut _).ker =
      Subgroup.center (Jb ⧸ Subgroup.center Jb) := rckBP_ker_conj
  have hI' : GGRootInnerAt (MulAut.conj : Jb ⧸ Subgroup.center Jb →* MulAut _).range
      ((Subgroup.zpowers rb).map (MulAut.conj : Jb ⧸ Subgroup.center Jb →* MulAut _)) := by
    let φ' : (ggU t n 1).K →* MulAut (Jb ⧸ Subgroup.center Jb) :=
      (MulAut.conj : Jb ⧸ Subgroup.center Jb →* MulAut _).comp ψ
    have hφ'ker : φ'.ker ≤ Subgroup.center (ggU t n 1).K := by
      intro z hz
      apply hψker
      have hz1 : (MulAut.conj (ψ z) : MulAut _) = 1 := MonoidHom.mem_ker.mp hz
      have hz2 : ψ z ∈ (MulAut.conj : Jb ⧸ Subgroup.center Jb →* MulAut _).ker :=
        MonoidHom.mem_ker.mpr hz1
      rwa [hkerconj, hZJb, Subgroup.mem_bot] at hz2
    have hrange : φ'.range = (MulAut.conj : Jb ⧸ Subgroup.center Jb →* MulAut _).range := by
      rw [MonoidHom.range_comp, hψrange, Subgroup.map_top]
    have hroot' : ggRootSub (ggU t n 1).D φ' β 1 =
        (Subgroup.zpowers rb).map (MulAut.conj : Jb ⧸ Subgroup.center Jb →* MulAut _) := by
      have h1 : ggRootSub (ggU t n 1).D φ' β 1 =
          (ggRootSub (ggU t n 1).D ψ β 1).map
            (MulAut.conj : Jb ⧸ Subgroup.center Jb →* MulAut _) := by
        simp only [ggRootSub, φ', Subgroup.map_map, MonoidHom.comp_assoc]
      have h2 : ggRootSub (ggU t n 1).D ψ β 1 = Subgroup.zpowers rb := by
        rw [CFSG.StandardType.LieKnownR2.Short.ggRootSub_eq_map, hggid, hroot,
          MonoidHom.map_zpowers]
      rw [h1, h2]
    have h := hI (MulAut (Jb ⧸ Subgroup.center Jb)) φ' hφ'ker β hβ hlong 1
    rwa [hrange, hroot'] at h
  have hQ' : ⁅pCoreOf 2 (Subgroup.centralizer ({rb} : Set _)),
      pCoreOf 2 (Subgroup.centralizer ({rb} : Set _))⁆ ≤ Subgroup.zpowers rb := by
    have hmain := rckBP_commutator_pCore_le hψker hψodd hRr2 (le_refl _) hcomm
    have hN : Subgroup.normalizer (Subgroup.zpowers rb : Set _) =
        Subgroup.centralizer ({rb} : Set _) := ggNormalizer_zpowers_eq_centralizer hrbord
    rw [hψrange, top_inf_eq, hRrmap, hN] at hmain
    exact hmain
  have hV' : Vb ≤ pCoreOf 2 (Subgroup.centralizer ({rb} : Set _)) := by
    have hkerN : ψ.ker ≤ Subgroup.normalizer (Rr : Set (ggU t n 1).K) :=
      hψker.trans (Subgroup.center_le_normalizer (Rr : Set (ggU t n 1).K))
    have h1 : (pCoreOf 2 (Subgroup.normalizer (Rr : Set _))).map ψ =
        pCoreOf 2 ((Subgroup.normalizer (Rr : Set _)).map ψ) :=
      CFSG.StandardType.LieKnownR2.map_pCoreOf_eq_of_odd_central_ker hψker hψodd hkerN
    have h2 : (Subgroup.normalizer (Rr : Set _)).map ψ =
        ψ.range ⊓ Subgroup.normalizer ((Rr.map ψ : Subgroup _) : Set _) :=
      CFSG.StandardType.LieKnownR2.map_normalizer_eq_range_inf_normalizer_map hψker hψodd hRr2
    have hle : Vb ≤ (pCoreOf 2 (Subgroup.normalizer (Rr : Set _))).map ψ := by
      show V.map ψ ≤ _
      exact Subgroup.map_mono hVN
    have hN : Subgroup.normalizer (Subgroup.zpowers rb : Set _) =
        Subgroup.centralizer ({rb} : Set _) := ggNormalizer_zpowers_eq_centralizer hrbord
    rw [h1, h2, hψrange, top_inf_eq, hRrmap, hN] at hle
    exact hle
  have hVbdata : RCKK1Data rb Vb := by
    refine ⟨?_, hrb1, ?_, ?_, ?_, ?_⟩
    · show ψ x ∈ V.map ψ
      exact Subgroup.mem_map.mpr ⟨x, hxV, rfl⟩
    · show IsElemAbelian 2 (V.map ψ)
      exact ggIsElemAbelian_map hVab ψ
    · show Nat.card (V.map ψ) = 4
      rw [rckBP_card_map_of_disjoint ψ hVdisj, hVcard]
    · intro v hv hv1
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hv
      have hu1 : u ≠ 1 := by intro h; exact hv1 (by rw [h, map_one])
      obtain ⟨j, hj⟩ := hconj u hu hu1
      refine ⟨ψ j, ?_⟩
      show ψ u = ψ j * rb * (ψ j)⁻¹
      rw [hj, map_mul, map_mul, map_inv]
    · exact rckK1b_of_inner hZJb rb hrb2 hI' hQ' Vb hV'
  have hggφ : ggRootSub (ggU t n 1).D φ β 1 = ((ggU t n 1).D.rootGroup β).map φ := by
    rw [CFSG.StandardType.LieKnownR2.Short.ggRootSub_eq_map, hggid]
  have hφkerodd : Odd (Nat.card φ.ker) := hZoddU.of_dvd_nat (Subgroup.card_dvd_of_le hφker)
  have hdisjφ : (ggU t n 1).D.rootGroup β ⊓ φ.ker = ⊥ :=
    rckBP_inf_ker_eq_bot φ hRr2 hφkerodd
  refine ⟨rb, Vb, hVbdata, ?_⟩
  refine ⟨ggRootSub (ggU t n 1).D φ β 1, ggRootSub (ggU t n 1).D φ (-β) 1, ?_, ?_, ?_⟩
  · refine Or.inl ⟨t, n, 1, β, hpos, le_refl 1, hlong, ?_⟩
    exact ⟨φ, MonoidHom.range_eq_top.mpr hφsurj, hφker, 1, rfl, rfl⟩
  · rw [hggφ, rckBP_card_map_of_disjoint φ hdisjφ, hroot, Nat.card_zpowers, hxord]
  · refine Subgroup.mem_map.mpr ⟨φ x, ?_, rfl⟩
    rw [hggφ]
    exact Subgroup.mem_map.mpr ⟨x, hxroot, rfl⟩

end CFSG.StandardType.RCKK1II
