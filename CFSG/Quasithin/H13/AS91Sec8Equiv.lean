module

public import CFSG.Quasithin.Recognition.UniquenessSystemCriterion
import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Commute.Basic

public section

namespace CFSG.Quasithin.H13.AS91

open CFSG.Quasithin.Asc94 MulAction

universe u v u' v'

variable {G : Type v} [Group G] {X : Type u} [MulAction G X]
  {Gb : Type v'} [Group Gb] {Xb : Type u'} [MulAction Gb Xb]
  {x y : X} {xb yb : Xb} {I : Subgroup G} {Ib : Subgroup Gb}
  {β : stabilizer G x ≃* stabilizer Gb xb} {ζ : I ≃* Ib}

@[expose] noncomputable def conjD (β : stabilizer G x ≃* stabilizer Gb xb) (ζ : I ≃* Ib) (n : I)
    (k : G) : G :=
  totFun β.symm ((ζ n : Gb)⁻¹ * totFun β k * ζ n)

theorem conjD_conj_mem {K : Subgroup G} (hK : K ≤ stabilizer G x) {n : I}
    (hnβ : (ζ n : Gb) ∈ Subgroup.normalizer (stabImage β K : Set Gb)) {k : G} (hk : k ∈ K) :
    (ζ n : Gb)⁻¹ * totFun β k * ζ n ∈ stabImage β K := by
  have hzinv : (ζ n : Gb)⁻¹ ∈ Subgroup.normalizer (stabImage β K : Set Gb) := inv_mem hnβ
  have := (Subgroup.mem_normalizer_iff.mp hzinv _).mp (totFun_mem_stabImage hK hk)
  simpa using this

theorem conjD_mem {K : Subgroup G} (hK : K ≤ stabilizer G x) {n : I}
    (hnβ : (ζ n : Gb) ∈ Subgroup.normalizer (stabImage β K : Set Gb)) {k : G} (hk : k ∈ K) :
    conjD β ζ n k ∈ K :=
  totFun_symm_mem_of_stabImage (conjD_conj_mem hK hnβ hk)

theorem totFun_conjD {K : Subgroup G} (hK : K ≤ stabilizer G x) {n : I}
    (hnβ : (ζ n : Gb) ∈ Subgroup.normalizer (stabImage β K : Set Gb)) {k : G} (hk : k ∈ K) :
    totFun β (conjD β ζ n k) = (ζ n : Gb)⁻¹ * totFun β k * ζ n :=
  totFun_totFun_symm β (stabImage_le K (conjD_conj_mem hK hnβ hk))

theorem exists_w_of_conjD (hs : IsSimilarity I x y Ib xb yb β ζ) (K : Subgroup G)
    (hK : K ≤ stabilizer G x)
    (h1 : ∀ α : K ≃* K, (∀ k : K, (k : G) ∈ I → α k = k) →
      ∃ w : G, w ∈ I ∧ w ∈ Subgroup.normalizer (K : Set G) ∧ (∀ i ∈ I, w * i = i * w) ∧
        ∀ k : K, (α k : G) = w * k * w⁻¹)
    (n : I) (hnK : (n : G) ∈ Subgroup.normalizer (K : Set G))
    (hnβ : (ζ n : Gb) ∈ Subgroup.normalizer (stabImage β K : Set Gb)) :
    ∃ w : G, w ∈ I ∧ w ∈ Subgroup.normalizer (K : Set G) ∧ (∀ i ∈ I, w * i = i * w) ∧
      ∀ k ∈ K, conjD β ζ n k = (n : G)⁻¹ * (w * k * w⁻¹) * n := by
  set z : Gb := (ζ n : Gb) with hz
  have hzinv : z⁻¹ ∈ Subgroup.normalizer (stabImage β K : Set Gb) := inv_mem hnβ
  have hA : ∀ {k : G}, k ∈ K → z⁻¹ * totFun β k * z ∈ stabImage β K := fun hk =>
    conjD_conj_mem hK hnβ hk
  have hB : ∀ {k : G}, k ∈ K → z * totFun β k * z⁻¹ ∈ stabImage β K := fun hk =>
    (Subgroup.mem_normalizer_iff.mp hnβ _).mp (totFun_mem_stabImage hK hk)
  let f : K → K := fun k => ⟨(n : G) * totFun β.symm (z⁻¹ * totFun β k * z) * (n : G)⁻¹,
    conj_mem_of_normalizer' hnK (totFun_symm_mem_of_stabImage (hA k.2))⟩
  let g : K → K := fun k => ⟨totFun β.symm (z * totFun β ((n : G)⁻¹ * k * n) * z⁻¹),
    totFun_symm_mem_of_stabImage (hB (conj_mem_of_normalizer hnK k.2))⟩
  have hfg : ∀ k, g (f k) = k := by
    intro k
    apply Subtype.ext
    change totFun β.symm (z * totFun β ((n : G)⁻¹ * ((n : G) * totFun β.symm
      (z⁻¹ * totFun β k * z) * (n : G)⁻¹) * n) * z⁻¹) = k
    rw [show (n : G)⁻¹ * ((n : G) * totFun β.symm (z⁻¹ * totFun β k * z) * (n : G)⁻¹) * n =
      totFun β.symm (z⁻¹ * totFun β k * z) by group]
    rw [totFun_totFun_symm β (stabImage_le K (hA k.2))]
    rw [show z * (z⁻¹ * totFun β k * z) * z⁻¹ = totFun β k by group]
    exact totFun_symm_totFun β (hK k.2)
  have hgf : ∀ k, f (g k) = k := by
    intro k
    apply Subtype.ext
    change (n : G) * totFun β.symm (z⁻¹ * totFun β (totFun β.symm
      (z * totFun β ((n : G)⁻¹ * k * n) * z⁻¹)) * z) * (n : G)⁻¹ = k
    rw [totFun_totFun_symm β (stabImage_le K (hB (conj_mem_of_normalizer hnK k.2)))]
    rw [show z⁻¹ * (z * totFun β ((n : G)⁻¹ * k * n) * z⁻¹) * z =
      totFun β ((n : G)⁻¹ * k * n) by group]
    rw [totFun_symm_totFun β (hK (conj_mem_of_normalizer hnK k.2))]
    group
  have hfmul : ∀ a b : K, f (a * b) = f a * f b := by
    intro a b
    apply Subtype.ext
    change (n : G) * totFun β.symm (z⁻¹ * totFun β ((a : G) * b) * z) * (n : G)⁻¹ =
      ((n : G) * totFun β.symm (z⁻¹ * totFun β a * z) * (n : G)⁻¹) *
        ((n : G) * totFun β.symm (z⁻¹ * totFun β b * z) * (n : G)⁻¹)
    rw [totFun_mul β (hK a.2) (hK b.2)]
    rw [show z⁻¹ * (totFun β a * totFun β b) * z =
      (z⁻¹ * totFun β a * z) * (z⁻¹ * totFun β b * z) by group]
    rw [totFun_mul β.symm (stabImage_le K (hA a.2)) (stabImage_le K (hA b.2))]
    group
  let α : K ≃* K :=
    { toFun := f
      invFun := g
      left_inv := hfg
      right_inv := hgf
      map_mul' := hfmul }
  have hfix : ∀ k : K, (k : G) ∈ I → α k = k := by
    intro k hkI
    apply Subtype.ext
    change (n : G) * totFun β.symm (z⁻¹ * totFun β k * z) * (n : G)⁻¹ = k
    have hk' : (n : G)⁻¹ * k * n ∈ I := I.mul_mem (I.mul_mem (I.inv_mem n.2) hkI) n.2
    have hkx : (n : G)⁻¹ * k * n ∈ stabilizer G x := hK (conj_mem_of_normalizer hnK k.2)
    have e1 : totFun β k = ζ ⟨k, hkI⟩ := by
      rw [totFun_of_mem β (hK k.2)]; exact hs.eq_on ⟨k, hkI⟩ (hK k.2)
    have e2 : totFun β ((n : G)⁻¹ * k * n) = z⁻¹ * totFun β k * z := by
      rw [totFun_of_mem β hkx, hs.eq_on ⟨_, hk'⟩ hkx, e1]
      rw [show (⟨(n : G)⁻¹ * k * n, hk'⟩ : I) = n⁻¹ * ⟨k, hkI⟩ * n from rfl]
      rw [map_mul, map_mul, map_inv]
      rfl
    rw [← e2, totFun_symm_totFun β hkx]
    group
  obtain ⟨w, hwI, hwK, hwc, hw⟩ := h1 α hfix
  refine ⟨w, hwI, hwK, hwc, fun k hk => ?_⟩
  have hfk := hw ⟨k, hk⟩
  change (n : G) * totFun β.symm (z⁻¹ * totFun β k * z) * (n : G)⁻¹ = w * k * w⁻¹ at hfk
  change totFun β.symm (z⁻¹ * totFun β k * z) = (n : G)⁻¹ * (w * k * w⁻¹) * n
  rw [← hfk]
  group

theorem totFun_conj_of_conj_mem (hs : IsSimilarity I x y Ib xb yb β ζ) (K : Subgroup G)
    (hK : K ≤ stabilizer G x)
    (h1 : ∀ α : K ≃* K, (∀ k : K, (k : G) ∈ I → α k = k) →
      ∃ w : G, w ∈ I ∧ w ∈ Subgroup.normalizer (K : Set G) ∧ (∀ i ∈ I, w * i = i * w) ∧
        ∀ k : K, (α k : G) = w * k * w⁻¹)
    (t h : I) (hth : (h : G)⁻¹ * t * h ∈ stabilizer G x)
    (htK : (t : G) ∈ Subgroup.normalizer (K : Set G))
    (hhK : (h : G) ∈ Subgroup.normalizer (K : Set G))
    (hhβ : (ζ h : Gb) ∈ Subgroup.normalizer (stabImage β K : Set Gb))
    {k : G} (hk : k ∈ K) :
    totFun β ((t : G)⁻¹ * k * t) = (ζ t : Gb)⁻¹ * totFun β k * ζ t := by
  set g : I := h⁻¹ * t * h with hg
  have hgcoe : (g : G) = (h : G)⁻¹ * t * h := by simp [hg]
  have hgx : (g : G) ∈ stabilizer G x := by rw [hgcoe]; exact hth
  have htgh : t = h * g * h⁻¹ := by rw [hg]; group
  have hgK : (g : G) ∈ Subgroup.normalizer (K : Set G) := by
    rw [hgcoe]; exact mul_mem (mul_mem (inv_mem hhK) htK) hhK
  have hhinvK : ((h⁻¹ : I) : G) ∈ Subgroup.normalizer (K : Set G) := by
    rw [Subgroup.coe_inv]; exact inv_mem hhK
  have hhinvβ : (ζ h⁻¹ : Gb) ∈ Subgroup.normalizer (stabImage β K : Set Gb) := by
    rw [map_inv, Subgroup.coe_inv]; exact inv_mem hhβ
  obtain ⟨w₁, hw₁I, hw₁K, hw₁c, hw₁⟩ := exists_w_of_conjD hs K hK h1 h hhK hhβ
  obtain ⟨w₃, hw₃I, hw₃K, hw₃c, hw₃⟩ := exists_w_of_conjD hs K hK h1 h⁻¹ hhinvK hhinvβ
  have hDhinv : ∀ m ∈ K, conjD β ζ h⁻¹ m = (h : G) * (w₃ * m * w₃⁻¹) * (h : G)⁻¹ := by
    intro m hm
    rw [hw₃ m hm]
    simp only [Subgroup.coe_inv, inv_inv]
  have hc : (h : G) * w₃ * (h : G)⁻¹ = w₃ := by
    have : w₃ * (h : G) = (h : G) * w₃ := hw₃c h h.2
    rw [← this]; group
  have hCd : ∀ k' ∈ K, conjD β ζ h⁻¹ (conjD β ζ h k') = k' := by
    intro k' hk'
    have hm1 : conjD β ζ h k' ∈ K := conjD_mem hK hhβ hk'
    have e : totFun β (conjD β ζ h⁻¹ (conjD β ζ h k')) = totFun β k' := by
      rw [totFun_conjD hK hhinvβ hm1, totFun_conjD hK hhβ hk', map_inv, Subgroup.coe_inv]
      group
    exact totFun_injOn β (hK (conjD_mem hK hhinvβ hm1)) (hK hk') e
  have hV : ∀ k' ∈ K, (w₃ * w₁) * k' * (w₃ * w₁)⁻¹ = k' := by
    intro k' hk'
    have := hCd k' hk'
    rw [hDhinv _ (conjD_mem hK hhβ hk'), hw₁ k' hk'] at this
    calc (w₃ * w₁) * k' * (w₃ * w₁)⁻¹
        = ((h : G) * w₃ * (h : G)⁻¹) * (w₁ * k' * w₁⁻¹) * ((h : G) * w₃ * (h : G)⁻¹)⁻¹ := by
          rw [hc]; group
      _ = (h : G) * (w₃ * ((h : G)⁻¹ * (w₁ * k' * w₁⁻¹) * h) * w₃⁻¹) * (h : G)⁻¹ := by group
      _ = k' := this
  have hm₁ : conjD β ζ h k ∈ K := conjD_mem hK hhβ hk
  have hm₂ : (g : G)⁻¹ * conjD β ζ h k * g ∈ K := conj_mem_of_normalizer hgK hm₁
  have e1 : totFun β ((g : G)⁻¹ * conjD β ζ h k * g) =
      (ζ g : Gb)⁻¹ * totFun β (conjD β ζ h k) * ζ g := by
    have hk1 := hK hm₁
    rw [totFun_mul β (Subgroup.mul_mem _ (inv_mem hgx) hk1) hgx,
      totFun_mul β (inv_mem hgx) hk1, totFun_inv β hgx, totFun_of_mem β hgx, hs.eq_on g hgx]
  have hm₃ : totFun β (conjD β ζ h⁻¹ ((g : G)⁻¹ * conjD β ζ h k * g)) =
      (ζ h : Gb) * ((ζ g : Gb)⁻¹ * ((ζ h : Gb)⁻¹ * totFun β k * ζ h) * ζ g) * (ζ h : Gb)⁻¹ := by
    rw [totFun_conjD hK hhinvβ hm₂, e1, totFun_conjD hK hhβ hk, map_inv, Subgroup.coe_inv]
    group
  have hm3eq : conjD β ζ h⁻¹ ((g : G)⁻¹ * conjD β ζ h k * g) = (t : G)⁻¹ * k * t := by
    have hc1 : w₁ * (t : G) = (t : G) * w₁ := hw₁c t t.2
    have hc2 : (t : G)⁻¹ * w₁ = w₁ * (t : G)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hc1]; group
    have hc3 : w₁⁻¹ * (t : G) = (t : G) * w₁⁻¹ :=
      (Commute.inv_left (show Commute w₁ (t : G) from hc1)).eq
    have hc' : (h : G) * w₃⁻¹ * (h : G)⁻¹ = w₃⁻¹ := by
      rw [← inv_inj]; simpa [mul_assoc] using hc
    calc conjD β ζ h⁻¹ ((g : G)⁻¹ * conjD β ζ h k * g)
        = ((h : G) * w₃ * (h : G)⁻¹) * ((t : G)⁻¹ * w₁) * k * (w₁⁻¹ * (t : G)) *
            ((h : G) * w₃⁻¹ * (h : G)⁻¹) := by
          rw [hDhinv _ hm₂, hw₁ k hk, hgcoe]; group
      _ = w₃ * (w₁ * (t : G)⁻¹) * k * ((t : G) * w₁⁻¹) * w₃⁻¹ := by
          rw [hc, hc', hc2, hc3]
      _ = (w₃ * w₁) * ((t : G)⁻¹ * k * t) * (w₃ * w₁)⁻¹ := by group
      _ = (t : G)⁻¹ * k * t := hV _ (conj_mem_of_normalizer htK hk)
  have hζt : (ζ t : Gb) = (ζ h : Gb) * (ζ g : Gb) * (ζ h : Gb)⁻¹ := by
    rw [htgh]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [← hm3eq, hm₃, hζt]
  group

theorem equivalence_criterion_Z (hs : IsSimilarity I x y Ib xb yb β ζ) (K : Subgroup G)
    (t h : I) (hK : K ≤ stabilizer G x)
    (h1 : ∀ α : K ≃* K, (∀ k : K, (k : G) ∈ I → α k = k) →
      ∃ w : G, w ∈ I ∧ w ∈ Subgroup.normalizer (K : Set G) ∧ (∀ i ∈ I, w * i = i * w) ∧
        ∀ k : K, (α k : G) = w * k * w⁻¹)
    (htx : (t : G) • x = y) (hty : (t : G) • y = x)
    (hth : (h : G)⁻¹ * t * h ∈ stabilizer G x)
    (htK : (t : G) ∈ Subgroup.normalizer (K : Set G))
    (hhK : (h : G) ∈ Subgroup.normalizer (K : Set G))
    (hhβ : (ζ h : Gb) ∈ Subgroup.normalizer (stabImage β K : Set Gb))
    (h3 : stabilizer G x ⊓ stabilizer G y =
      K ⊓ stabilizer G y ⊔ I ⊓ stabilizer G x ⊓ stabilizer G y) :
    (∀ b c : stabilizer G x, (b : G) • y = y → (c : G) = (t : G)⁻¹ * b * t →
      (β c : Gb) = (ζ t : Gb)⁻¹ * β b * ζ t) ∧ IsEquivalence I x y Ib xb yb β ζ := by
  have hconj : ∀ {b : G}, b ∈ stabilizer G x ⊓ stabilizer G y →
      (t : G)⁻¹ * b * t ∈ stabilizer G x := by
    intro b hb
    rw [mem_stabilizer_iff, mul_smul, mul_smul, htx, mem_stabilizer_iff.mp hb.2]
    exact inv_smul_eq_iff.mpr htx.symm
  have key : ∀ b : G, b ∈ stabilizer G x ⊓ stabilizer G y →
      totFun β ((t : G)⁻¹ * b * t) = (ζ t : Gb)⁻¹ * totFun β b * ζ t := by
    intro b hb
    rw [h3, Subgroup.sup_eq_closure] at hb
    induction hb using Subgroup.closure_induction with
    | mem b hb =>
      rcases hb with hb | hb
      · exact totFun_conj_of_conj_mem hs K hK h1 t h hth htK hhK hhβ hb.1
      · have hbI : b ∈ I := hb.1.1
        have hbxy : b ∈ stabilizer G x ⊓ stabilizer G y := ⟨hb.1.2, hb.2⟩
        have hc : (t : G)⁻¹ * b * t ∈ stabilizer G x := hconj hbxy
        have hcI : (t : G)⁻¹ * b * t ∈ I := I.mul_mem (I.mul_mem (I.inv_mem t.2) hbI) t.2
        rw [totFun_of_mem β hc, hs.eq_on ⟨_, hcI⟩ hc, totFun_of_mem β hb.1.2,
          hs.eq_on ⟨b, hbI⟩ hb.1.2]
        rw [show (⟨(t : G)⁻¹ * b * t, hcI⟩ : I) = t⁻¹ * ⟨b, hbI⟩ * t from rfl]
        rw [map_mul, map_mul, map_inv]
        rfl
    | one =>
      have h1x : (1 : G) ∈ stabilizer G x := one_mem _
      rw [show (t : G)⁻¹ * 1 * t = 1 by group, totFun_of_mem β h1x]
      simp [show (⟨1, h1x⟩ : stabilizer G x) = 1 from rfl]
    | mul a b ha hb iha ihb =>
      have ha' : a ∈ stabilizer G x ⊓ stabilizer G y := by
        rw [h3, Subgroup.sup_eq_closure]; exact ha
      have hb' : b ∈ stabilizer G x ⊓ stabilizer G y := by
        rw [h3, Subgroup.sup_eq_closure]; exact hb
      rw [show (t : G)⁻¹ * (a * b) * t = ((t : G)⁻¹ * a * t) * ((t : G)⁻¹ * b * t) by group]
      rw [totFun_mul β (hconj ha') (hconj hb'), iha, ihb, totFun_mul β ha'.1 hb'.1]
      group
    | inv a ha iha =>
      have ha' : a ∈ stabilizer G x ⊓ stabilizer G y := by
        rw [h3, Subgroup.sup_eq_closure]; exact ha
      rw [show (t : G)⁻¹ * a⁻¹ * t = ((t : G)⁻¹ * a * t)⁻¹ by group]
      rw [totFun_inv β (hconj ha'), iha, totFun_inv β ha'.1]
      group
  have main : ∀ b c : stabilizer G x, (b : G) • y = y → (c : G) = (t : G)⁻¹ * b * t →
      (β c : Gb) = (ζ t : Gb)⁻¹ * β b * ζ t := by
    intro b c hby hc
    have := key b ⟨b.2, hby⟩
    rw [← hc, totFun_coe, totFun_coe] at this
    exact this
  exact ⟨main, hs, t, htx, hty, main⟩

end CFSG.Quasithin.H13.AS91
