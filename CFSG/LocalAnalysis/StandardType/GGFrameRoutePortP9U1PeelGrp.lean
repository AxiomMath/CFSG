module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowXUnStructGrp

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn.Struct
open scoped commutatorElement

variable {G : Type*} [Group G]

private def p9uPeel_kappa {Z Q : Subgroup G} (hZ : ScalarLike Z) (hQ : IsGoodIn Z Q) {g h : G}
    (hg : g ∈ Q) (hh : h ∈ Q) : Q →* Z × Z :=
  (commHomLeft hZ hQ hg).prod (commHomLeft hZ hQ hh)

private lemma p9uPeel_kappa_fst {Z Q : Subgroup G} (hZ : ScalarLike Z) (hQ : IsGoodIn Z Q)
    {g h : G} (hg : g ∈ Q) (hh : h ∈ Q) (x : Q) :
    (p9uPeel_kappa hZ hQ hg hh x).1 = commHomLeft hZ hQ hg x := rfl

private lemma p9uPeel_kappa_snd {Z Q : Subgroup G} (hZ : ScalarLike Z) (hQ : IsGoodIn Z Q)
    {g h : G} (hg : g ∈ Q) (hh : h ∈ Q) (x : Q) :
    (p9uPeel_kappa hZ hQ hg hh x).2 = commHomLeft hZ hQ hh x := rfl

private lemma p9uPeel_card_Z_eq_three {Z Q : Subgroup G} [Finite ↥Z] (hZ : ScalarLike Z)
    (hQ : IsGoodIn Z Q) {g h : G} (hg : g ∈ Q) (hh : h ∈ Q) (hgh : g * h ≠ h * g) :
    Nat.card Z = 3 := by
  have hcZ : ⁅g, h⁆ ∈ Z := hQ.1 g hg h hh
  have hc1 : ⁅g, h⁆ ≠ 1 := fun h1 => hgh (commutatorElement_eq_one_iff_mul_comm.1 h1)
  have hc3 : ⁅g, h⁆ ^ 3 = 1 := hZ.cube _ hcZ
  have hcard : Nat.card (Subgroup.zpowers ⁅g, h⁆) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hc3 hc1]
  exact le_antisymm hZ.card_le
    (hcard ▸ Subgroup.card_le_of_le (Subgroup.zpowers_le.2 hcZ))

private lemma p9uPeel_ker_map_eq {Z Q : Subgroup G} (hZ : ScalarLike Z) (hQ : IsGoodIn Z Q)
    {g h : G} (hg : g ∈ Q) (hh : h ∈ Q) :
    (p9uPeel_kappa hZ hQ hg hh).ker.map Q.subtype
      = Q ⊓ Subgroup.centralizer ({g, h} : Set G) := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx1 : p9uPeel_kappa hZ hQ hg hh x = 1 := MonoidHom.mem_ker.1 hx
    have hxg : ⁅(x : G), g⁆ = 1 := by
      have h := congrArg (fun p : Z × Z => (p.1 : G)) hx1
      simpa [p9uPeel_kappa, commHomLeft] using h
    have hxh : ⁅(x : G), h⁆ = 1 := by
      have h := congrArg (fun p : Z × Z => (p.2 : G)) hx1
      simpa [p9uPeel_kappa, commHomLeft] using h
    refine ⟨x.2, ?_⟩
    refine Subgroup.mem_centralizer_iff.2 ?_
    intro z hz
    rcases hz with rfl | rfl
    · exact (commutatorElement_eq_one_iff_mul_comm.1 hxg).symm
    · exact (commutatorElement_eq_one_iff_mul_comm.1 hxh).symm
  · rintro ⟨hyQ, hycent⟩
    refine ⟨⟨y, hyQ⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    have hgy : ⁅y, g⁆ = 1 := by
      have h := Subgroup.mem_centralizer_iff.1 hycent g (by simp)
      exact commutatorElement_eq_one_iff_mul_comm.2 h.symm
    have hhy : ⁅y, h⁆ = 1 := by
      have h := Subgroup.mem_centralizer_iff.1 hycent h (by simp)
      exact commutatorElement_eq_one_iff_mul_comm.2 h.symm
    apply Prod.ext
    · rw [p9uPeel_kappa_fst]
      exact Subtype.ext hgy
    · rw [p9uPeel_kappa_snd]
      exact Subtype.ext hhy

private lemma p9uPeel_exists_pow_mul {Z Q : Subgroup G} [Finite ↥Z] (hZ : ScalarLike Z)
    (hQ : IsGoodIn Z Q) {g h : G} (hg : g ∈ Q) (hh : h ∈ Q) (hgh : g * h ≠ h * g)
    (t : Z × Z) :
    ∃ a b : ℤ,
      p9uPeel_kappa hZ hQ hg hh ((⟨h, hh⟩ : Q) ^ a * (⟨g, hg⟩ : Q) ^ b) = t := by
  have hcZ : ⁅g, h⁆ ∈ Z := hQ.1 g hg h hh
  have hc1 : ⁅g, h⁆ ≠ 1 := fun h1 => hgh (commutatorElement_eq_one_iff_mul_comm.1 h1)
  have hc3 : ⁅g, h⁆ ^ 3 = 1 := hZ.cube _ hcZ
  have hcard : Nat.card (Subgroup.zpowers ⁅g, h⁆) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hc3 hc1]
  have hgen : Subgroup.zpowers ⁅g, h⁆ = Z := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hcZ)
    rw [hcard]
    exact hZ.card_le
  have ht1 : (t.1 : G)⁻¹ ∈ Subgroup.zpowers ⁅g, h⁆ := by
    rw [hgen]
    exact Subgroup.inv_mem Z t.1.2
  have ht2 : (t.2 : G) ∈ Subgroup.zpowers ⁅g, h⁆ := by
    rw [hgen]
    exact t.2.2
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.1 ht1
  obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.1 ht2
  have hgg : (commHomLeft hZ hQ hg) (⟨g, hg⟩ : Q) = 1 := by
    apply Subtype.ext
    show ⁅g, g⁆ = (1 : G)
    simp
  have hhg : (commHomLeft hZ hQ hg) (⟨h, hh⟩ : Q) =
      ⟨(⁅g, h⁆)⁻¹, Subgroup.inv_mem Z hcZ⟩ := by
    apply Subtype.ext
    show ⁅h, g⁆ = (⁅g, h⁆)⁻¹
    exact (commutatorElement_inv (g₁ := g) (g₂ := h)).symm
  have hhh : (commHomLeft hZ hQ hh) (⟨h, hh⟩ : Q) = 1 := by
    apply Subtype.ext
    show ⁅h, h⁆ = (1 : G)
    simp
  have hgh' : (commHomLeft hZ hQ hh) (⟨g, hg⟩ : Q) = ⟨⁅g, h⁆, hcZ⟩ := by
    apply Subtype.ext
    rfl
  refine ⟨a, b, ?_⟩
  apply Prod.ext
  · rw [p9uPeel_kappa_fst]
    rw [map_mul, map_zpow, map_zpow, hhg, hgg, one_zpow, mul_one]
    apply Subtype.ext
    rw [Subgroup.coe_zpow, inv_zpow, ha, inv_inv]
  · rw [p9uPeel_kappa_snd]
    rw [map_mul, map_zpow, map_zpow, hhh, hgh', one_zpow, one_mul]
    apply Subtype.ext
    rw [Subgroup.coe_zpow, hb]

private lemma p9uPeel_factor {Z Q : Subgroup G} [Finite ↥Z] (hZ : ScalarLike Z)
    (hQ : IsGoodIn Z Q) {g h : G} (hg : g ∈ Q) (hh : h ∈ Q) (hgh : g * h ≠ h * g)
    (y : Q) :
    ∃ a b : ℤ, ∃ q : Q, q ∈ (p9uPeel_kappa hZ hQ hg hh).ker ∧
      ((⟨h, hh⟩ : Q) ^ a * (⟨g, hg⟩ : Q) ^ b) * q = y := by
  obtain ⟨a, b, hab⟩ :=
    p9uPeel_exists_pow_mul hZ hQ hg hh hgh (p9uPeel_kappa hZ hQ hg hh y)
  refine ⟨a, b, ((⟨h, hh⟩ : Q) ^ a * (⟨g, hg⟩ : Q) ^ b)⁻¹ * y, ?_, ?_⟩
  · rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
  · group

private lemma p9uPeel_mem_center_map_iff (H : Subgroup G) (x : G) :
    x ∈ (Subgroup.center ↥H).map H.subtype ↔ x ∈ H ∧ ∀ y ∈ H, y * x = x * y := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.2, fun y hy => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz (⟨y, hy⟩ : ↥H))
  · rintro ⟨hxH, hcomm⟩
    refine ⟨⟨x, hxH⟩, ?_, rfl⟩
    exact Subgroup.mem_center_iff.2
      (fun y => Subtype.ext (by simpa [Subgroup.coe_mul] using hcomm y y.2))

theorem card_eq_nine_mul_card_inf_centralizer_pair {Z Q : Subgroup G} [Finite ↥Z]
    (hZ : ScalarLike Z) (hQ : IsGoodIn Z Q) {g h : G} (hg : g ∈ Q) (hh : h ∈ Q)
    (hgh : g * h ≠ h * g) :
    Nat.card Q = 9 * Nat.card ↥(Q ⊓ Subgroup.centralizer ({g, h} : Set G)) := by
  have hZcard := p9uPeel_card_Z_eq_three hZ hQ hg hh hgh
  have hker := p9uPeel_ker_map_eq hZ hQ hg hh
  have hsurj : Function.Surjective (p9uPeel_kappa hZ hQ hg hh) := fun t => by
    obtain ⟨a, b, hab⟩ := p9uPeel_exists_pow_mul hZ hQ hg hh hgh t
    exact ⟨_, hab⟩
  have hrange : (p9uPeel_kappa hZ hQ hg hh).range = ⊤ := MonoidHom.range_eq_top.2 hsurj
  have htop : Nat.card (p9uPeel_kappa hZ hQ hg hh).range = 9 := by
    rw [hrange, Subgroup.card_top, Nat.card_prod, hZcard]
  have hkerQ : Nat.card (p9uPeel_kappa hZ hQ hg hh).ker =
      Nat.card ↥(Q ⊓ Subgroup.centralizer ({g, h} : Set G)) := by
    rw [← hker, Subgroup.card_map_of_injective Q.subtype_injective]
  have h := Subgroup.card_ker_mul_card_range (p9uPeel_kappa hZ hQ hg hh)
  rw [hkerQ, htop] at h
  omega

theorem card_center_inf_centralizer_pair {Z Q : Subgroup G} [Finite ↥Z]
    (hZ : ScalarLike Z) (hQ : IsGoodIn Z Q) {g h : G} (hg : g ∈ Q) (hh : h ∈ Q)
    (hgh : g * h ≠ h * g) :
    Nat.card (Subgroup.center ↥(Q ⊓ Subgroup.centralizer ({g, h} : Set G))) =
      Nat.card (Subgroup.center ↥Q) := by
  have hcenter : (Subgroup.center ↥(Q ⊓ Subgroup.centralizer ({g, h} : Set G))).map
        (Q ⊓ Subgroup.centralizer ({g, h} : Set G)).subtype
      = (Subgroup.center ↥Q).map Q.subtype := by
    ext x
    rw [p9uPeel_mem_center_map_iff (Q ⊓ Subgroup.centralizer ({g, h} : Set G)) x,
      p9uPeel_mem_center_map_iff Q x]
    constructor
    · rintro ⟨hxQ₁, hcommQ₁⟩
      have hxQ : x ∈ Q := (Subgroup.mem_inf.1 hxQ₁).1
      have hxcent : x ∈ Subgroup.centralizer ({g, h} : Set G) :=
        (Subgroup.mem_inf.1 hxQ₁).2
      refine ⟨hxQ, fun y hy => ?_⟩
      obtain ⟨a, b, q, hqker, hyq⟩ := p9uPeel_factor hZ hQ hg hh hgh ⟨y, hy⟩
      have hqmem : (q : G) ∈ Q ⊓ Subgroup.centralizer ({g, h} : Set G) := by
        rw [← p9uPeel_ker_map_eq hZ hQ hg hh]
        exact ⟨q, hqker, rfl⟩
      have hqx : (q : G) * x = x * (q : G) := hcommQ₁ (q : G) hqmem
      have hxgh : x * (h ^ a * g ^ b) = (h ^ a * g ^ b) * x := by
        have hhx : Commute x h :=
          (Subgroup.mem_centralizer_iff.1 hxcent h (by simp)).symm
        have hgx : Commute x g :=
          (Subgroup.mem_centralizer_iff.1 hxcent g (by simp)).symm
        exact ((hhx.zpow_right a).mul_right (hgx.zpow_right b)).eq
      have hy_val : y = (h ^ a * g ^ b) * (q : G) := by
        have h := congrArg Subtype.val hyq
        simpa [Subgroup.coe_mul, Subgroup.coe_zpow] using h.symm
      rw [hy_val]
      rw [mul_assoc (h ^ a * g ^ b) (q : G) x, hqx,
        ← mul_assoc (h ^ a * g ^ b) x (q : G), ← hxgh,
        mul_assoc x (h ^ a * g ^ b) (q : G)]
    · rintro ⟨hxQ, hcommQ⟩
      have hxQ₁ : x ∈ Q ⊓ Subgroup.centralizer ({g, h} : Set G) := by
        rw [Subgroup.mem_inf]
        refine ⟨hxQ, ?_⟩
        refine Subgroup.mem_centralizer_iff.2 ?_
        intro z hz
        have hzg : z = g ∨ z = h := by simpa using hz
        rcases hzg with hzg | hzg
        · rw [hzg]
          exact hcommQ g hg
        · rw [hzg]
          exact hcommQ h hh
      refine ⟨hxQ₁, fun y hy => ?_⟩
      exact hcommQ y (Subgroup.mem_inf.1 hy).1
  calc Nat.card (Subgroup.center ↥(Q ⊓ Subgroup.centralizer ({g, h} : Set G)))
      = Nat.card ((Subgroup.center ↥(Q ⊓ Subgroup.centralizer ({g, h} : Set G))).map
          (Q ⊓ Subgroup.centralizer ({g, h} : Set G)).subtype) :=
        (Subgroup.card_subtype _ _).symm
    _ = Nat.card ((Subgroup.center ↥Q).map Q.subtype) := by rw [hcenter]
    _ = Nat.card (Subgroup.center ↥Q) := Subgroup.card_subtype Q (Subgroup.center ↥Q)

end CFSG.StandardType.FrameRoute

end
