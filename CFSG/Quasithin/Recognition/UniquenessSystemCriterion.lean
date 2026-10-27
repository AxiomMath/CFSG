module

public import CFSG.Quasithin.Recognition.UniquenessSystemDefs
import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.Asc94

open MulAction

universe u v u' v'

section TotFun

variable {G : Type v} [Group G] {Gb : Type v'} [Group Gb] {A : Subgroup G} {B : Subgroup Gb}

@[expose] noncomputable def totFun (e : A ≃* B) (g : G) : Gb :=
  open Classical in if hg : g ∈ A then (e ⟨g, hg⟩ : Gb) else 1

theorem totFun_coe (e : A ≃* B) (a : A) : totFun e a = e a := by
  simp [totFun, a.2]

theorem totFun_of_mem (e : A ≃* B) {g : G} (hg : g ∈ A) : totFun e g = e ⟨g, hg⟩ :=
  totFun_coe e ⟨g, hg⟩

theorem totFun_mem (e : A ≃* B) {g : G} (hg : g ∈ A) : totFun e g ∈ B := by
  rw [totFun_of_mem e hg]; exact (e _).2

theorem totFun_mul (e : A ≃* B) {g g' : G} (hg : g ∈ A) (hg' : g' ∈ A) :
    totFun e (g * g') = totFun e g * totFun e g' := by
  rw [totFun_of_mem e hg, totFun_of_mem e hg', totFun_of_mem e (A.mul_mem hg hg')]
  rw [show (⟨g * g', A.mul_mem hg hg'⟩ : A) = ⟨g, hg⟩ * ⟨g', hg'⟩ from rfl, map_mul]
  rfl

theorem totFun_inv (e : A ≃* B) {g : G} (hg : g ∈ A) : totFun e g⁻¹ = (totFun e g)⁻¹ := by
  rw [totFun_of_mem e hg, totFun_of_mem e (A.inv_mem hg)]
  rw [show (⟨g⁻¹, A.inv_mem hg⟩ : A) = (⟨g, hg⟩ : A)⁻¹ from rfl, map_inv]
  rfl

theorem totFun_symm_totFun (e : A ≃* B) {g : G} (hg : g ∈ A) :
    totFun e.symm (totFun e g) = g := by
  rw [totFun_of_mem e hg, totFun_coe, MulEquiv.symm_apply_apply]

theorem totFun_totFun_symm (e : A ≃* B) {w : Gb} (hw : w ∈ B) :
    totFun e (totFun e.symm w) = w := by
  rw [totFun_of_mem e.symm hw, totFun_coe, MulEquiv.apply_symm_apply]

theorem totFun_injOn (e : A ≃* B) {g g' : G} (hg : g ∈ A) (hg' : g' ∈ A)
    (h : totFun e g = totFun e g') : g = g' := by
  rw [← totFun_symm_totFun e hg, h, totFun_symm_totFun e hg']

end TotFun

variable {G : Type v} [Group G] {X : Type u} [MulAction G X]
  {Gb : Type v'} [Group Gb] {Xb : Type u'} [MulAction Gb Xb]
  {x y : X} {xb yb : Xb} {I : Subgroup G} {Ib : Subgroup Gb}
  {β : stabilizer G x ≃* stabilizer Gb xb} {ζ : I ≃* Ib}

@[expose] def stabImage (β : stabilizer G x ≃* stabilizer Gb xb) (K : Subgroup G) :
    Subgroup Gb :=
  (K.subgroupOf (stabilizer G x)).map ((stabilizer Gb xb).subtype.comp β.toMonoidHom)

theorem mem_stabImage {K : Subgroup G} {g : Gb} :
    g ∈ stabImage β K ↔ ∃ k : stabilizer G x, (k : G) ∈ K ∧ (β k : Gb) = g := by
  simp only [stabImage, Subgroup.mem_map, Subgroup.mem_subgroupOf, MonoidHom.coe_comp,
    Function.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom]

theorem stabImage_le (K : Subgroup G) : stabImage β K ≤ stabilizer Gb xb := by
  intro g hg
  obtain ⟨k, -, rfl⟩ := mem_stabImage.mp hg
  exact (β k).2

theorem totFun_mem_stabImage {K : Subgroup G} (hK : K ≤ stabilizer G x) {k : G}
    (hk : k ∈ K) : totFun β k ∈ stabImage β K :=
  mem_stabImage.mpr ⟨⟨k, hK hk⟩, hk, (totFun_of_mem β (hK hk)).symm⟩

theorem totFun_symm_mem_of_stabImage {K : Subgroup G} {w : Gb} (hw : w ∈ stabImage β K) :
    totFun β.symm w ∈ K := by
  obtain ⟨k, hk, rfl⟩ := mem_stabImage.mp hw
  rw [totFun_coe, MulEquiv.symm_apply_apply]
  exact hk

theorem conj_mem_of_normalizer {K : Subgroup G} {h : G}
    (hh : h ∈ Subgroup.normalizer (K : Set G)) {k : G} (hk : k ∈ K) : h⁻¹ * k * h ∈ K := by
  have hh' : h⁻¹ ∈ Subgroup.normalizer (K : Set G) := inv_mem hh
  have := (Subgroup.mem_normalizer_iff.mp hh' k).mp hk
  simpa using this

theorem conj_mem_of_normalizer' {K : Subgroup G} {h : G}
    (hh : h ∈ Subgroup.normalizer (K : Set G)) {k : G} (hk : k ∈ K) : h * k * h⁻¹ ∈ K :=
  (Subgroup.mem_normalizer_iff.mp hh k).mp hk

theorem conj_eq_of_aut (hs : IsSimilarity I x y Ib xb yb β ζ) (K : Subgroup G) (h : I)
    (hK : K ≤ stabilizer G x)
    (h1 : ∀ α : K ≃* K, (∀ k : K, (k : G) ∈ I → α k = k) → α = MulEquiv.refl K)
    (hhK : (h : G) ∈ Subgroup.normalizer (K : Set G))
    (hhβ : (ζ h : Gb) ∈ Subgroup.normalizer (stabImage β K : Set Gb))
    {k : G} (hk : k ∈ K) :
    totFun β ((h : G)⁻¹ * k * h) = (ζ h : Gb)⁻¹ * totFun β k * ζ h := by
  set z : Gb := (ζ h : Gb) with hz
  have hzinv : z⁻¹ ∈ Subgroup.normalizer (stabImage β K : Set Gb) := inv_mem hhβ
  have hA : ∀ {k : G}, k ∈ K → z⁻¹ * totFun β k * z ∈ stabImage β K := fun hk => by
    have := (Subgroup.mem_normalizer_iff.mp hzinv _).mp (totFun_mem_stabImage hK hk)
    simpa using this
  have hB : ∀ {k : G}, k ∈ K → z * totFun β k * z⁻¹ ∈ stabImage β K := fun hk =>
    (Subgroup.mem_normalizer_iff.mp hhβ _).mp (totFun_mem_stabImage hK hk)
  let f : K → K := fun k => ⟨(h : G) * totFun β.symm (z⁻¹ * totFun β k * z) * (h : G)⁻¹,
    conj_mem_of_normalizer' hhK (totFun_symm_mem_of_stabImage (hA k.2))⟩
  let g : K → K := fun k => ⟨totFun β.symm (z * totFun β ((h : G)⁻¹ * k * h) * z⁻¹),
    totFun_symm_mem_of_stabImage (hB (conj_mem_of_normalizer hhK k.2))⟩
  have hfg : ∀ k, g (f k) = k := by
    intro k
    apply Subtype.ext
    change totFun β.symm (z * totFun β ((h : G)⁻¹ * ((h : G) * totFun β.symm
      (z⁻¹ * totFun β k * z) * (h : G)⁻¹) * h) * z⁻¹) = k
    rw [show (h : G)⁻¹ * ((h : G) * totFun β.symm (z⁻¹ * totFun β k * z) * (h : G)⁻¹) * h =
      totFun β.symm (z⁻¹ * totFun β k * z) by group]
    rw [totFun_totFun_symm β (stabImage_le K (hA k.2))]
    rw [show z * (z⁻¹ * totFun β k * z) * z⁻¹ = totFun β k by group]
    exact totFun_symm_totFun β (hK k.2)
  have hgf : ∀ k, f (g k) = k := by
    intro k
    apply Subtype.ext
    change (h : G) * totFun β.symm (z⁻¹ * totFun β (totFun β.symm
      (z * totFun β ((h : G)⁻¹ * k * h) * z⁻¹)) * z) * (h : G)⁻¹ = k
    rw [totFun_totFun_symm β (stabImage_le K (hB (conj_mem_of_normalizer hhK k.2)))]
    rw [show z⁻¹ * (z * totFun β ((h : G)⁻¹ * k * h) * z⁻¹) * z =
      totFun β ((h : G)⁻¹ * k * h) by group]
    rw [totFun_symm_totFun β (hK (conj_mem_of_normalizer hhK k.2))]
    group
  have hfmul : ∀ a b : K, f (a * b) = f a * f b := by
    intro a b
    apply Subtype.ext
    change (h : G) * totFun β.symm (z⁻¹ * totFun β ((a : G) * b) * z) * (h : G)⁻¹ =
      ((h : G) * totFun β.symm (z⁻¹ * totFun β a * z) * (h : G)⁻¹) *
        ((h : G) * totFun β.symm (z⁻¹ * totFun β b * z) * (h : G)⁻¹)
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
    change (h : G) * totFun β.symm (z⁻¹ * totFun β k * z) * (h : G)⁻¹ = k
    have hk' : (h : G)⁻¹ * k * h ∈ I := I.mul_mem (I.mul_mem (I.inv_mem h.2) hkI) h.2
    have hkx : (h : G)⁻¹ * k * h ∈ stabilizer G x := hK (conj_mem_of_normalizer hhK k.2)
    have e1 : totFun β k = ζ ⟨k, hkI⟩ := by
      rw [totFun_of_mem β (hK k.2)]; exact hs.eq_on ⟨k, hkI⟩ (hK k.2)
    have e2 : totFun β ((h : G)⁻¹ * k * h) = z⁻¹ * totFun β k * z := by
      rw [totFun_of_mem β hkx, hs.eq_on ⟨_, hk'⟩ hkx, e1]
      rw [show (⟨(h : G)⁻¹ * k * h, hk'⟩ : I) = h⁻¹ * ⟨k, hkI⟩ * h from rfl]
      rw [map_mul, map_mul, map_inv]
      rfl
    rw [← e2, totFun_symm_totFun β hkx]
    group
  have hα : α = MulEquiv.refl K := h1 α hfix
  have hfk : (f ⟨k, hk⟩ : G) = k := by
    have := congrArg (fun e : K ≃* K => (e ⟨k, hk⟩ : G)) hα
    exact this
  change (h : G) * totFun β.symm (z⁻¹ * totFun β k * z) * (h : G)⁻¹ = k at hfk
  have hval : totFun β.symm (z⁻¹ * totFun β k * z) = (h : G)⁻¹ * k * h := by
    calc totFun β.symm (z⁻¹ * totFun β k * z)
        = (h : G)⁻¹ * ((h : G) * totFun β.symm (z⁻¹ * totFun β k * z) * (h : G)⁻¹) * h := by
          group
      _ = (h : G)⁻¹ * k * h := by rw [hfk]
  rw [← hval, totFun_totFun_symm β (stabImage_le K (hA hk))]

theorem equivalence_criterion (hs : IsSimilarity I x y Ib xb yb β ζ) (K : Subgroup G)
    (t h : I) (hK : K ≤ stabilizer G x)
    (h1 : ∀ α : K ≃* K, (∀ k : K, (k : G) ∈ I → α k = k) → α = MulEquiv.refl K)
    (htx : (t : G) • x = y) (hty : (t : G) • y = x) (hth : (t : G) * h ∈ stabilizer G x)
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
      ·
        have hbK : b ∈ K := hb.1
        set g : I := t * h with hg
        have hgx : (g : G) ∈ stabilizer G x := hth
        have hbg : (g : G)⁻¹ * b * g ∈ K := conj_mem_of_normalizer
          ((Subgroup.normalizer (K : Set G)).mul_mem htK hhK) hbK
        have e1 : totFun β ((g : G)⁻¹ * b * g) = (ζ g : Gb)⁻¹ * totFun β b * ζ g := by
          rw [totFun_mul β (Subgroup.mul_mem _ (inv_mem hgx) (hK hbK)) hgx,
            totFun_mul β (inv_mem hgx) (hK hbK), totFun_inv β hgx, totFun_of_mem β hgx,
            hs.eq_on g hgx]
        have e2 := conj_eq_of_aut hs K h hK h1 hhK hhβ
          (conj_mem_of_normalizer' hhK hbg)
        rw [show (h : G)⁻¹ * ((h : G) * ((g : G)⁻¹ * b * g) * (h : G)⁻¹) * h =
          (g : G)⁻¹ * b * g by group] at e2
        have e3 : totFun β ((t : G)⁻¹ * b * t) =
            (ζ h : Gb) * totFun β ((g : G)⁻¹ * b * g) * (ζ h : Gb)⁻¹ := by
          rw [show (t : G)⁻¹ * b * t = (h : G) * ((g : G)⁻¹ * b * g) * (h : G)⁻¹ by
            rw [hg]; simp only [Subgroup.coe_mul]; group]
          rw [e2]; group
        rw [e3, e1, hg, map_mul]
        simp only [Subgroup.coe_mul]
        group
      ·
        have hbI : b ∈ I := hb.1.1
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

end CFSG.Quasithin.Asc94
