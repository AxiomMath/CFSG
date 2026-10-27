module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoTorus
public import CFSG.Open.LocalVocabulary
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.GroupTheory.ConjTransport
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.Open
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]

lemma mulAut_eq_one_of_forall_mul_inv_mem_center {L : Subgroup G}
    (hperf : commutator ↥L = ⊤) (φ : MulAut ↥L)
    (h : ∀ x : ↥L, φ x * x⁻¹ ∈ Subgroup.center ↥L) : φ = 1 := by
  classical
  let f : ↥L →* Subgroup.center ↥L :=
    { toFun := fun x => ⟨φ x * x⁻¹, h x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        have hcomm : (φ y * y⁻¹) * x⁻¹ = x⁻¹ * (φ y * y⁻¹) :=
          (Subgroup.mem_center_iff.mp (h y) x⁻¹).symm
        change φ (x * y) * (x * y)⁻¹ = (φ x * x⁻¹) * (φ y * y⁻¹)
        rw [map_mul, mul_inv_rev]
        calc φ x * φ y * (y⁻¹ * x⁻¹)
            = φ x * (φ y * y⁻¹) * x⁻¹ := by group
          _ = φ x * ((φ y * y⁻¹) * x⁻¹) := by group
          _ = φ x * (x⁻¹ * (φ y * y⁻¹)) := by rw [hcomm]
          _ = φ x * x⁻¹ * (φ y * y⁻¹) := by group }
  have hker : f.ker = ⊤ := by
    rw [eq_top_iff, ← hperf]
    exact Abelianization.commutator_subset_ker f
  ext x
  have hx : f x = 1 := by rw [← MonoidHom.mem_ker, hker]; trivial
  have hx' : φ x * x⁻¹ = 1 := congrArg Subtype.val hx
  simpa using mul_inv_eq_one.mp hx'

theorem false_of_isPGroup_two_of_orderOf_eq_three {H : Type*} [Group H] [Finite H]
    (h2 : IsPGroup 2 H) {z : H} (hz : orderOf z = 3) : False := by
  obtain ⟨n, hn⟩ := h2 z
  have hdvd : orderOf z ∣ 2 ^ n := (orderOf_dvd_iff_pow_eq_one).mpr hn
  rw [hz] at hdvd
  have h3 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  norm_num at h3

theorem not_mem_of_isPGroup_two_center {L : Subgroup G} {b : G}
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hb : orderOf b = 3)
    (hbC : b ∈ Subgroup.centralizer (L : Set G)) : b ∉ L := by
  intro hbL
  have hmem : (⟨b, hbL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro x
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hbC x x.2)
  let z : ↥(Subgroup.center ↥L) := ⟨⟨b, hbL⟩, hmem⟩
  refine false_of_isPGroup_two_of_orderOf_eq_three hZ2 (z := z) ?_
  rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hb]

theorem card_inf_Bstar_L (hK : Nat.card K = 4) {Bs L : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    (hmap : ((Bs ⊓ L).subgroupOf L).map
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) = USixTwo.torU K) :
    Nat.card ↥(Bs ⊓ L) = 3 ^ 4 := by
  classical
  let R := LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))
  let π : ↥L →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hker : ∀ x : ↥((Bs ⊓ L).subgroupOf L), π x = 1 → x = 1 := by
    intro x hx
    have hxL : (x : ↥L) ∈ Subgroup.center ↥L := by
      refine (QuotientGroup.eq_one_iff (x : ↥L)).mp (θ.injective ?_)
      exact hx.trans (map_one θ).symm
    have hxBs : ((x : ↥L) : G) ∈ Bs := (Subgroup.mem_subgroupOf.mp x.2).1
    have hx3 : (x : ↥L) ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hBs.2 ((x : ↥L) : G) hxBs
    have hord3 : orderOf (x : ↥L) ∣ 3 := (orderOf_dvd_iff_pow_eq_one).mpr hx3
    let z : ↥(Subgroup.center ↥L) := ⟨(x : ↥L), hxL⟩
    obtain ⟨n, hn⟩ := hZ2 z
    have hord2 : orderOf (x : ↥L) ∣ 2 ^ n := by
      have h := (orderOf_dvd_iff_pow_eq_one).mpr hn
      rwa [Subgroup.orderOf_mk] at h
    have hcop : Nat.Coprime 3 (2 ^ n) := (by norm_num : Nat.Coprime 3 2).pow_right n
    have h1 : orderOf (x : ↥L) = 1 := Nat.eq_one_of_dvd_coprimes hcop hord3 hord2
    exact Subtype.ext (orderOf_eq_one_iff.mp h1)
  let φ : ↥((Bs ⊓ L).subgroupOf L) → ↥(USixTwo.torU K) := fun x =>
    ⟨π x, by rw [← hmap]; exact Subgroup.mem_map_of_mem π x.2⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro x y hxy
      have hxy' : π x = π y := congrArg Subtype.val hxy
      have h1 : π (x / y) = 1 := by rw [map_div, hxy']; simp
      exact div_eq_one.mp (hker (x / y) h1)
    · intro y
      have hy : (y : R) ∈ ((Bs ⊓ L).subgroupOf L).map π := by
        rw [hmap]; exact y.2
      obtain ⟨x, hx, hxπ⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨x, hx⟩, Subtype.ext hxπ⟩
  calc Nat.card ↥(Bs ⊓ L) = Nat.card ↥((Bs ⊓ L).subgroupOf L) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : Bs ⊓ L ≤ L)).toEquiv).symm
    _ = Nat.card (USixTwo.torU K) := Nat.card_congr (Equiv.ofBijective φ hφ)
    _ = 3 ^ 4 := USixTwo.card_torU hK

theorem zpowers_inf_Bstar_inf_L_eq_bot {Bs L : Subgroup G} {b : G}
    (hb : orderOf b = 3) (hbL : b ∉ L) :
    Subgroup.zpowers b ⊓ (Bs ⊓ L) = ⊥ := by
  classical
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxP, hxB⟩ := hx
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxP
  have hb3 : b ^ 3 = 1 := (orderOf_dvd_iff_pow_eq_one).mp (by rw [hb])
  have hkred : b ^ (k % 3) = x := by
    have h1 : b ^ (k % (orderOf b : ℤ)) = b ^ k := zpow_mod_orderOf b k
    rw [show (orderOf b : ℤ) = 3 by rw [hb]; norm_num] at h1
    rw [h1, hk]
  have hk0 : (0 : ℤ) ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have hklt : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  set r : ℤ := k % 3 with hrdef
  have hr0 : 0 ≤ r := hk0
  have hrlt : r < 3 := hklt
  have hr : b ^ r = x := hkred
  rw [Subgroup.mem_bot]
  interval_cases r
  · rw [← hr]; simp
  · rw [← hr] at hxB
    exact absurd (by simpa using hxB.2) hbL
  · exfalso
    apply hbL
    have hb4 : b ^ 4 = b := by
      rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_add, hb3, one_mul, pow_one]
    have hb2 : b = (b ^ 2) ^ 2 := by
      rw [← pow_mul]
      norm_num
      exact hb4.symm
    have hb2L : b ^ 2 ∈ L := by simpa [← hr] using hxB.2
    rw [hb2]
    exact L.pow_mem hb2L 2

theorem Bstar_eq_zpowers_sup_inf (hK : Nat.card K = 4) {Bs L : Subgroup G} {b : G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hb : orderOf b = 3)
    (hbC : b ∈ Subgroup.centralizer (L : Set G))
    (hBs : IsElemAbelian 3 Bs) (hbBs : b ∈ Bs) (hcard : Nat.card Bs = 3 ^ 5)
    (hmap : ((Bs ⊓ L).subgroupOf L).map
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) = USixTwo.torU K) :
    Bs = Subgroup.zpowers b ⊔ (Bs ⊓ L) := by
  have hnorm : (Bs ⊓ L) ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
    intro y hy
    have hyb : y * b * y⁻¹ = b := by
      have hcomm : y * b = b * y :=
        congrArg Subtype.val (hBs.1.is_comm.comm ⟨y, hy.1⟩ ⟨b, hbBs⟩)
      calc y * b * y⁻¹ = b * y * y⁻¹ := by rw [hcomm]
        _ = b := by group
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    simpa [CFSG.GroupTheory.map_conj_zpowers, hyb]
  have hdisj : Disjoint (Subgroup.zpowers b) (Bs ⊓ L) :=
    disjoint_iff.mpr (zpowers_inf_Bstar_inf_L_eq_bot hb (not_mem_of_isPGroup_two_center hZ2 hb hbC))
  have hcard' := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (Subgroup.zpowers b) (Bs ⊓ L) hnorm hdisj
  have hcardz : Nat.card (Subgroup.zpowers b) = 3 := by
    rw [Nat.card_zpowers, hb]
  have hcardB : Nat.card ↥(Bs ⊓ L) = 3 ^ 4 := card_inf_Bstar_L hK θ hZ2 hBs hmap
  have hle : Subgroup.zpowers b ⊔ (Bs ⊓ L) ≤ Bs :=
    sup_le (Subgroup.zpowers_le.mpr hbBs) inf_le_left
  have hsupcard : Nat.card ↥(Subgroup.zpowers b ⊔ (Bs ⊓ L)) = 3 ^ 5 := by
    rw [hcard', hcardz, hcardB]
    norm_num
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hsupcard])).symm

theorem exists_mul_eq_of_mem_Bstar (hK : Nat.card K = 4) {Bs L : Subgroup G} {b : G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hb : orderOf b = 3)
    (hbC : b ∈ Subgroup.centralizer (L : Set G))
    (hBs : IsElemAbelian 3 Bs) (hbBs : b ∈ Bs) (hcard : Nat.card Bs = 3 ^ 5)
    (hmap : ((Bs ⊓ L).subgroupOf L).map
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) = USixTwo.torU K)
    {x : G} (hx : x ∈ Bs) :
    ∃ p ∈ Subgroup.zpowers b, ∃ y ∈ Bs ⊓ L, p * y = x := by
  classical
  haveI hcomm : IsMulCommutative ↥Bs := hBs.1
  let A : Subgroup ↥Bs := (Subgroup.zpowers b).subgroupOf Bs
  let B : Subgroup ↥Bs := (Bs ⊓ L).subgroupOf Bs
  have hBsEq : Bs = Subgroup.zpowers b ⊔ (Bs ⊓ L) :=
    Bstar_eq_zpowers_sup_inf hK θ hZ2 hb hbC hBs hbBs hcard hmap
  have hsub : (Subgroup.zpowers b ⊔ (Bs ⊓ L)).subgroupOf Bs = A ⊔ B := by
    rw [Subgroup.subgroupOf_sup (Subgroup.zpowers_le.mpr hbBs) inf_le_left]
  have htop : A ⊔ B = ⊤ := by
    rw [← hsub, ← hBsEq, Subgroup.subgroupOf_self]
  have hx' : (⟨x, hx⟩ : ↥Bs) ∈ A ⊔ B := by rw [htop]; trivial
  rw [Subgroup.mem_sup_of_normal_left] at hx'
  obtain ⟨a, ha, y, hy, hay⟩ := hx'
  refine ⟨(a : ↥Bs), ?_, (y : ↥Bs), ?_, ?_⟩
  · exact ha
  · exact hy
  · have := congrArg Subtype.val hay
    simpa using this

theorem centralizer_Bstar_le_centralizer_b {Bs : Subgroup G} {b : G} (hbBs : b ∈ Bs) :
    Subgroup.centralizer (Bs : Set G) ≤ Subgroup.centralizer ({b} : Set G) :=
  Subgroup.centralizer_le (by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hbBs)

theorem centralizer_b_le_normalizer {b : G} {L : Subgroup G}
    (hLb : L ≤ Subgroup.centralizer {b})
    (hN : (L.subgroupOf (Subgroup.centralizer {b})).Normal) :
    Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer hLb).mp hN

lemma eq_or_inv_of_orderOf_eq_three_of_mem_zpowers {H : Type*} [Group H] [Finite H]
    {x y : H} (hx : orderOf x = 3) (hy : orderOf y = 3) (h : x ∈ Subgroup.zpowers y) :
    x = y ∨ x = y⁻¹ := by
  classical
  obtain ⟨k, hk, hkx⟩ :=
    Finset.mem_image.mp ((mem_zpowers_iff_mem_range_orderOf (x := y)).mp h)
  rw [Finset.mem_range, hy] at hk
  interval_cases k
  · exfalso
    rw [pow_zero] at hkx
    rw [← hkx] at hx
    simp at hx
  · left
    rw [pow_one] at hkx
    exact hkx.symm
  · right
    rw [pow_two] at hkx
    rw [← hkx]
    have hy3 : y ^ 3 = 1 := (orderOf_dvd_iff_pow_eq_one).mp (by rw [hy])
    have h1 : y * (y * y) = 1 := by
      rw [← pow_two, ← pow_succ']
      exact hy3
    exact eq_inv_of_mul_eq_one_right h1

theorem normalizerMonoidHom_pow_three_eq_one (hK : Nat.card K = 4) {Bs L : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤)
    (hmap : ((Bs ⊓ L).subgroupOf L).map
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) = USixTwo.torU K)
    {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    (hfix : ∀ z ∈ Bs ⊓ L, g * z * g⁻¹ = z) :
    Subgroup.normalizerMonoidHom L ⟨g, hg⟩ ^ 3 = 1 := by
  classical
  let R := LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))
  let c : MulAut ↥L := Subgroup.normalizerMonoidHom L ⟨g, hg⟩
  have hc : ∀ x : ↥L, ((c x : ↥L) : G) = g * x * g⁻¹ :=
    fun x => Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨g, hg⟩ x
  let qc : MulAut (↥L ⧸ Subgroup.center ↥L) :=
    QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥L) c
      (Subgroup.map_center_eq c)
  have hqc : ∀ x : ↥L, qc (QuotientGroup.mk x) = QuotientGroup.mk (c x) :=
    fun x => QuotientGroup.congr_mk _ _ _ _ x
  let α : MulAut R := MulAut.congr θ qc
  have hα : ∀ x : ↥L,
      α ((θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))) x) =
        (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))) (c x) := by
    intro x
    change (MulAut.congr θ qc) (θ (QuotientGroup.mk x)) = _
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [hqc]
    rfl
  have hfix_tor : ∀ u ∈ USixTwo.torU K, α u = u := by
    intro u hu
    rw [← hmap] at hu
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hu
    rw [hα]
    congr 1
    apply Subtype.ext
    rw [hc]
    exact hfix x.1 hx
  have hα3 : α ^ 3 = 1 := USixTwo.pow_three_eq_one_of_forall_fix_torU hK α hfix_tor
  have hα3' : α ^ 3 = MulAut.congr θ (qc ^ 3) := by
    change (MulAut.congr θ) qc ^ 3 = MulAut.congr θ (qc ^ 3)
    rw [map_pow]
  have hc3 : c ^ 3 = 1 := by
    apply mulAut_eq_one_of_forall_mul_inv_mem_center hperf (c ^ 3)
    intro x
    have hqc3 : (qc ^ 3) (QuotientGroup.mk x) = QuotientGroup.mk ((c ^ 3) x) := by
      change qc (qc (qc (QuotientGroup.mk x))) = QuotientGroup.mk ((c ^ 3) x)
      rw [hqc, hqc, hqc]
      rfl
    have h1 : (α ^ 3) (θ (QuotientGroup.mk x)) = θ (QuotientGroup.mk x) := by
      rw [hα3]
      rfl
    rw [hα3', MulAut.congr_apply] at h1
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hqc3] at h1
    have h2 : QuotientGroup.mk ((c ^ 3) x) = QuotientGroup.mk x := θ.injective h1
    obtain ⟨z, hz, hzx⟩ := (QuotientGroup.mk'_eq_mk' (Subgroup.center ↥L)).mp h2
    have hzinv : z⁻¹ ∈ Subgroup.center ↥L := Subgroup.inv_mem _ hz
    have hzc : (c ^ 3) x * z⁻¹ = z⁻¹ * (c ^ 3) x :=
      Subgroup.mem_center_iff.mp hzinv ((c ^ 3) x)
    have hval : (c ^ 3) x * x⁻¹ = z⁻¹ := by
      calc (c ^ 3) x * x⁻¹ = (c ^ 3) x * ((c ^ 3) x * z)⁻¹ := by rw [hzx]
        _ = (c ^ 3) x * (z⁻¹ * ((c ^ 3) x)⁻¹) := by rw [mul_inv_rev]
        _ = (c ^ 3) x * z⁻¹ * ((c ^ 3) x)⁻¹ := by group
        _ = z⁻¹ * (c ^ 3) x * ((c ^ 3) x)⁻¹ := by rw [hzc]
        _ = z⁻¹ := by group
    rw [hval]
    exact hzinv
  exact hc3

theorem relPPrimeCore_inf_subgroupOf_le_center (hK : Nat.card K = 4) {b : G} {L : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hLb : L ≤ Subgroup.centralizer {b})
    (hN : (L.subgroupOf (Subgroup.centralizer {b})).Normal) :
    (relPPrimeCore 3 (Subgroup.centralizer {b}) ⊓ L).subgroupOf L ≤
      Subgroup.center ↥L := by
  classical
  let R := LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))
  let C : Subgroup G := Subgroup.centralizer ({b} : Set G)
  let O : Subgroup G := relPPrimeCore 3 C
  let π : ↥L →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπsurj : Function.Surjective π :=
    θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hOle : O ≤ C :=
    AlmostSimple.relPPrimeCore_le (p := 3) C
  have hOnorm : (O.subgroupOf C).Normal :=
    AlmostSimple.relPPrimeCore_normal
      Nat.prime_three C
  have hOcop : Nat.Coprime 3 (Nat.card O) :=
    AlmostSimple.coprime_card_relPPrimeCore
      Nat.prime_three C
  have hCn : C ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLb).mp hN
  let Q : Subgroup ↥L := (O ⊓ L).subgroupOf L
  have hQnorm : Q.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨hxO, hxL⟩ := Subgroup.mem_subgroupOf.mp hx
    refine Subgroup.mem_subgroupOf.mpr ⟨?_, ?_⟩
    · have hconj : (⟨(g : G), hLb g.2⟩ : ↥C) * ⟨x, hOle hxO⟩ * (⟨(g : G), hLb g.2⟩ : ↥C)⁻¹ ∈
          O.subgroupOf C :=
        hOnorm.conj_mem ⟨x, hOle hxO⟩ hxO ⟨(g : G), hLb g.2⟩
      exact Subgroup.mem_subgroupOf.mp hconj
    · exact L.mul_mem (L.mul_mem g.2 hxL) (L.inv_mem g.2)
  have hQmap_normal : (Q.map π).Normal := hQnorm.map π hπsurj
  have hQcop : Nat.Coprime 3 (Nat.card (Q.map π)) := by
    refine Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd Q π) ?_
    have h1 : Nat.card ↥Q = Nat.card ↥(O ⊓ L) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : O ⊓ L ≤ L)).toEquiv
    rw [h1]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hOcop
  have h3R : 3 ∣ Nat.card R := by
    have h1 : 3 ∣ Nat.card ↥(USixTwo.torU K) := by
      rw [USixTwo.card_torU hK]
      norm_num
    exact h1.trans (Subgroup.card_subgroup_dvd_card (USixTwo.torU K))
  have hQbot : Q.map π = ⊥ := by
    haveI : IsSimpleGroup R :=
      CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 1
        (by rw [hK]; norm_num) 6 (by norm_num) (by norm_num)
    rcases Subgroup.Normal.eq_bot_or_eq_top (Q.map π) with h | h
    · exact h
    · exfalso
      have hcopR : Nat.Coprime 3 (Nat.card R) := by
        rw [h] at hQcop
        simpa using hQcop
      have hgcd : 3 ∣ Nat.gcd 3 (Nat.card R) := Nat.dvd_gcd dvd_rfl h3R
      rw [show Nat.gcd 3 (Nat.card R) = 1 from hcopR] at hgcd
      norm_num at hgcd
  have hker : π.ker = Subgroup.center ↥L := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      exact (QuotientGroup.eq_one_iff (x : ↥L)).mp (θ.injective (hx.trans (map_one θ).symm))
    · intro hx
      have h1 : QuotientGroup.mk (x : ↥L) = 1 := (QuotientGroup.eq_one_iff (x : ↥L)).mpr hx
      show π x = 1
      rw [show π x = θ (QuotientGroup.mk (x : ↥L)) from rfl, h1, map_one]
  have hQle_center : Q ≤ Subgroup.center ↥L := by
    intro x hx
    rw [← hker, MonoidHom.mem_ker]
    have hmem : π x ∈ Q.map π := ⟨x, hx, rfl⟩
    rw [hQbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  exact hQle_center

end CFSG.StandardType.E6QTwo

end
