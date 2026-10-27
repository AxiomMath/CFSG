module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3InnerBase
import CFSG.LocalAnalysis.WeakClosure81.W183K3Lift
public import CFSG.LocalAnalysis.WeakClosure81.W183B2Fin

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace W183K3

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Y R T L N : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V}

private theorem w183k3_isSylowIn_imgOf_range {R L N : Subgroup (LGL 2 V)}
    (hcore : QuasiCore R L N) {T : Subgroup (LGL 2 V)} (hTR : IsSylowIn 2 T R) :
    IsSylowIn 2 (imgOf (psiQuot R L hcore.normal) T)
      (psiQuot R L hcore.normal).range := by
  let ψ := psiQuot R L hcore.normal
  have hT2 : IsPGroup 2 T := hTR.isPGroup
  refine ⟨?_, ?_, ?_⟩
  · rw [imgOf, ← Subgroup.map_top ψ]
    exact Subgroup.map_mono le_top
  · rw [imgOf]
    exact (hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTR.le).symm).map ψ
  · rw [imgOf, ← Subgroup.map_top ψ]
    rw [Subgroup.relIndex_map_map, top_sup_eq]
    intro h2
    have hdvd : ((T.subgroupOf R) ⊔ ψ.ker).relIndex ⊤ ∣ (T.subgroupOf R).relIndex ⊤ := by
      refine ⟨(T.subgroupOf R).relIndex ((T.subgroupOf R) ⊔ ψ.ker), ?_⟩
      rw [← Subgroup.relIndex_mul_relIndex (H := T.subgroupOf R)
        (K := (T.subgroupOf R) ⊔ ψ.ker) (L := ⊤) le_sup_left le_top, mul_comm]
    have h2' : 2 ∣ (T.subgroupOf R).relIndex ⊤ := h2.trans hdvd
    rw [Subgroup.relIndex_top_right] at h2'
    exact hTR.not_dvd_relIndex (by simpa [Subgroup.relIndex] using h2')

theorem w183k3_isSylowIn_imgOf_inf (hcore : QuasiCore R L N)
    (hTR : IsSylowIn 2 (T ⊓ R) R)
    {X₀ : Subgroup (MulAut (↥L ⧸ Subgroup.center ↥L))}
    (hX₀ : X₀ ≤ (psiQuot R L hcore.normal).range)
    (hX₀n : ∀ r : ↥R, ∀ x ∈ X₀,
      psiQuot R L hcore.normal r * x * (psiQuot R L hcore.normal r)⁻¹ ∈ X₀) :
    IsSylowIn 2 (imgOf (psiQuot R L hcore.normal) (T ⊓ R) ⊓ X₀) X₀ := by
  let ψ := psiQuot R L hcore.normal
  have hnorm : (X₀.subgroupOf ψ.range).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hX₀]
    intro g hg
    obtain ⟨r, hr⟩ := MonoidHom.mem_range.1 hg
    rw [← hr, Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hX₀n r x hx
    · intro hx
      have h := hX₀n r⁻¹ (ψ r * x * (ψ r)⁻¹) hx
      simpa [ψ, map_inv, mul_assoc] using h
  exact IsSylowIn.inf_normal (w183k3_isSylowIn_imgOf_range hcore hTR) hX₀ hnorm

private theorem w183k3_ker_psiQuot_odd (c : QuasiCore R L N) :
    Odd (Nat.card ↥(psiQuot R L c.normal).ker) := by
  let ψ := psiQuot R L c.normal
  have hle : ψ.ker ≤ N.subgroupOf R := by
    intro r hr
    exact Subgroup.mem_subgroupOf.mpr
      (c.cent (r : LGL 2 V) r.2
        ((QuasiCore.mem_ker_psiQuot_iff_centralizes c r).mp hr))
  have hdvd1 : Nat.card ↥ψ.ker ∣ Nat.card ↥(N.subgroupOf R) := Subgroup.card_dvd_of_le hle
  have hdvd2 : Nat.card ↥(N.subgroupOf R) ∣ Nat.card ↥N := by
    have hle' : (N.subgroupOf R).map R.subtype ≤ N := by
      rintro x ⟨n, hn, rfl⟩
      exact Subgroup.mem_subgroupOf.mp hn
    rw [Nat.card_congr
      (Subgroup.equivMapOfInjective (N.subgroupOf R) R.subtype R.subtype_injective).toEquiv]
    exact Subgroup.card_dvd_of_le hle'
  exact Odd.of_dvd_nat c.odd (hdvd1.trans hdvd2)

private theorem w183k3_psiQuot_injOn_S (hcore : QuasiCore R L N)
    (hTR : IsSylowIn 2 (T ⊓ R) R) {x y : ↥R}
    (hx : x ∈ (T ⊓ R).subgroupOf R) (hy : y ∈ (T ⊓ R).subgroupOf R)
    (h : psiQuot R L hcore.normal x = psiQuot R L hcore.normal y) : x = y := by
  have hker : (T ⊓ R).subgroupOf R ⊓ (psiQuot R L hcore.normal).ker = ⊥ :=
    hcore.inf_ker_psiQuot_eq_bot hTR.le hTR.isPGroup
  have hmem : x⁻¹ * y ∈ (T ⊓ R).subgroupOf R ⊓ (psiQuot R L hcore.normal).ker := by
    refine ⟨?_, ?_⟩
    · exact ((T ⊓ R).subgroupOf R).mul_mem (((T ⊓ R).subgroupOf R).inv_mem hx) hy
    · exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, h, inv_mul_cancel])
  rw [hker, Subgroup.mem_bot] at hmem
  exact inv_mul_eq_one.mp hmem

private theorem w183k3_subgroupOf_cj {A R : Subgroup (LGL 2 V)} (hA : A ≤ R) {n : ↥R} :
    (cj (n : LGL 2 V) A).subgroupOf R =
      (A.subgroupOf R).map (MulAut.conj n).toMonoidHom := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_subgroupOf, cj, Subgroup.mem_map] at hx
    obtain ⟨a, ha, han⟩ := hx
    refine Subgroup.mem_map.mpr ⟨⟨a, hA ha⟩, ha, ?_⟩
    apply Subtype.ext
    show (n : LGL 2 V) * a * (n : LGL 2 V)⁻¹ = (x : LGL 2 V)
    simpa [MulAut.conj_apply] using han
  · intro hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨a, ha, han⟩ := hx
    rw [Subgroup.mem_subgroupOf, cj, Subgroup.mem_map]
    exact ⟨(a : LGL 2 V), Subgroup.mem_subgroupOf.mp ha,
      by simpa [MulAut.conj_apply] using congrArg Subtype.val han⟩

private theorem w183k3_autConj_one {M : Type} [Group M] (A : Subgroup (MulAut M)) :
    autConj (1 : MulAut M) A = A := by
  change A.map (MulAut.conj (1 : MulAut M)).toMonoidHom = A
  rw [show MulAut.conj (1 : MulAut M) = 1 from map_one _, MulAut.one_def]
  exact Subgroup.map_id A

private theorem w183k3_imgOf_injOn_S (hcore : QuasiCore R L N)
    (hTR : IsSylowIn 2 (T ⊓ R) R) {A C : Subgroup (LGL 2 V)}
    (hA : A ≤ T ⊓ R) (hC : C ≤ T ⊓ R)
    (h : imgOf (psiQuot R L hcore.normal) A = imgOf (psiQuot R L hcore.normal) C) :
    A = C := by
  let ψ := psiQuot R L hcore.normal
  apply le_antisymm
  · intro a ha
    have haS : a ∈ T ⊓ R := hA ha
    have hmem : ψ ⟨a, haS.2⟩ ∈ imgOf ψ C := by
      have hmemA : ψ ⟨a, haS.2⟩ ∈ imgOf ψ A := apply_mem_imgOf ψ ha haS.2
      rw [h] at hmemA
      exact hmemA
    obtain ⟨c, hc, hψc⟩ := Subgroup.mem_map.mp hmem
    have hcS : c ∈ (T ⊓ R).subgroupOf R :=
      Subgroup.mem_subgroupOf.mpr (hC (Subgroup.mem_subgroupOf.mp hc))
    have hca : c = ⟨a, haS.2⟩ :=
      w183k3_psiQuot_injOn_S hcore hTR hcS (Subgroup.mem_subgroupOf.mpr haS) hψc
    rw [show a = (c : LGL 2 V) from congrArg Subtype.val hca.symm]
    exact Subgroup.mem_subgroupOf.mp hc
  · intro c hc
    have hcS : c ∈ T ⊓ R := hC hc
    have hmem : ψ ⟨c, hcS.2⟩ ∈ imgOf ψ A := by
      have hmemC : ψ ⟨c, hcS.2⟩ ∈ imgOf ψ C := apply_mem_imgOf ψ hc hcS.2
      rw [← h] at hmemC
      exact hmemC
    obtain ⟨a, ha, hψa⟩ := Subgroup.mem_map.mp hmem
    have haS : a ∈ (T ⊓ R).subgroupOf R :=
      Subgroup.mem_subgroupOf.mpr (hA (Subgroup.mem_subgroupOf.mp ha))
    have hac : a = ⟨c, hcS.2⟩ :=
      w183k3_psiQuot_injOn_S hcore hTR haS (Subgroup.mem_subgroupOf.mpr hcS) hψa
    rw [show c = (a : LGL 2 V) from congrArg Subtype.val hac.symm]
    exact Subgroup.mem_subgroupOf.mp ha

theorem w183k3_exists_normal_member {i : ℕ} (hc : Assumption131 Y Γ VA i) (hRY : R ≤ Y)
    (hcore : QuasiCore R L N) (hTR : IsSylowIn 2 (T ⊓ R) R)
    {X₀ : Subgroup (MulAut (↥L ⧸ Subgroup.center ↥L))}
    (hX₀ : X₀ ≤ (psiQuot R L hcore.normal).range)
    (hX₀n : ∀ r : ↥R, ∀ x ∈ X₀,
      psiQuot R L hcore.normal r * x * (psiQuot R L hcore.normal r)⁻¹ ∈ X₀)
    (hnc : Br2NormalConj (↥L ⧸ Subgroup.center ↥L) X₀) {D₀ : Subgroup (LGL 2 V)} (hD₀ : D₀ ∈ Γ)
    (hD₀R : D₀ ≤ R) (hD₀X : imgOf (psiQuot R L hcore.normal) D₀ ≤ X₀)
    (hD₀card : 8 ≤ Nat.card D₀) :
    ∃ D ∈ Γ, D ≤ T ⊓ R ∧ 8 ≤ Nat.card D ∧ imgOf (psiQuot R L hcore.normal) D ≤ X₀ ∧
      imgOf (psiQuot R L hcore.normal) (T ⊓ R) ⊓ X₀ ≤
        Subgroup.normalizer
          (imgOf (psiQuot R L hcore.normal) D : Set (MulAut (↥L ⧸ Subgroup.center ↥L))) ∧
      ∀ B : Subgroup (LGL 2 V), B ≤ T ⊓ R → imgOf (psiQuot R L hcore.normal) B ≤ X₀ →
        B ≤ Subgroup.normalizer (D : Set (LGL 2 V)) := by
  let ψ := psiQuot R L hcore.normal
  have hP₀ : IsSylowIn 2 (imgOf ψ (T ⊓ R) ⊓ X₀) X₀ :=
    w183k3_isSylowIn_imgOf_inf hcore hTR hX₀ hX₀n
  have hD₀2 : IsPGroup 2 D₀ := (hc.isElemAb D₀ hD₀).isPGroup
  have hEA₀ : IsElemAbelian 2 (imgOf ψ D₀) := by
    rw [imgOf]
    exact IsElemAbelian.map (IsElemAbelian.subgroupOf (hc.isElemAb D₀ hD₀) R) ψ
  have hcard₀ : 8 ≤ Nat.card (imgOf ψ D₀) := by
    rw [QuasiCore.card_imgOf_psiQuot hcore hD₀R hD₀2]
    exact hD₀card
  obtain ⟨g, hg_inn, hg_le, hg_norm⟩ :=
    hnc (imgOf ψ (T ⊓ R) ⊓ X₀) hP₀ (imgOf ψ D₀) hD₀X hEA₀ hcard₀
  obtain ⟨l, hl, hlg⟩ := exists_psiQuot_eq_of_mem_innAutOf hcore hg_inn
  let D₁ : Subgroup (LGL 2 V) := cj l D₀
  have hlR : l ∈ R := hcore.le hl
  have hlY : l ∈ Y := hRY hlR
  have hD₁mem : D₁ ∈ Γ := hc.invariant D₀ hD₀ l hlY
  have hD₁R : D₁ ≤ R := by
    change D₀.map (MulAut.conj l).toMonoidHom ≤ R
    rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    rw [Subgroup.mem_comap]
    show l * x * l⁻¹ ∈ R
    exact R.mul_mem (R.mul_mem hlR (hD₀R hx)) (R.inv_mem hlR)
  have hD₁img : imgOf ψ D₁ = autConj g (imgOf ψ D₀) := by
    change imgOf ψ (cj l D₀) = autConj g (imgOf ψ D₀)
    rw [imgOf_cj ψ hD₀R hlR]
    rw [show ψ ⟨l, hcore.le hl⟩ = g from hlg]
    rfl
  have hD₁le : imgOf ψ D₁ ≤ imgOf ψ (T ⊓ R) := by
    rw [hD₁img]
    exact hg_le.trans inf_le_left
  have hD₁2 : IsPGroup 2 D₁ := (hc.isElemAb D₁ hD₁mem).isPGroup
  let A₁ : Subgroup ↥R := D₁.subgroupOf R
  have hA₁2 : IsPGroup 2 A₁ :=
    hD₁2.of_equiv (Subgroup.subgroupOfEquivOfLe hD₁R).symm
  let B₁ : Subgroup ↥R := (T ⊓ R).subgroupOf R ⊓ (A₁.map ψ).comap ψ
  have hB₁S : B₁ ≤ (T ⊓ R).subgroupOf R := inf_le_left
  have hS'2 : IsPGroup 2 ((T ⊓ R).subgroupOf R) :=
    hTR.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hTR.le).symm
  have hB₁2 : IsPGroup 2 B₁ := hS'2.to_le hB₁S
  have hmap : A₁.map (QuotientGroup.mk' ψ.ker) = B₁.map (QuotientGroup.mk' ψ.ker) := by
    apply le_antisymm
    · rintro y ⟨a, ha, rfl⟩
      have hψaA : ψ a ∈ A₁.map ψ := Subgroup.mem_map_of_mem ψ ha
      have hψaS : ψ a ∈ ((T ⊓ R).subgroupOf R).map ψ := hD₁le hψaA
      obtain ⟨s, hs, hψs⟩ := Subgroup.mem_map.mp hψaS
      refine Subgroup.mem_map.mpr ⟨s, ?_, ?_⟩
      · rw [Subgroup.mem_inf]
        exact ⟨hs, Subgroup.mem_comap.mpr (by rw [hψs]; exact hψaA)⟩
      · exact QuotientGroup.eq_iff_div_mem.mpr (by
          rw [MonoidHom.mem_ker, div_eq_mul_inv, map_mul, map_inv, hψs, mul_inv_cancel])
    · rintro y ⟨b, hb, rfl⟩
      change b ∈ (T ⊓ R).subgroupOf R ⊓ (A₁.map ψ).comap ψ at hb
      rw [Subgroup.mem_inf] at hb
      obtain ⟨hbS, hbA⟩ := hb
      rw [Subgroup.mem_comap] at hbA
      obtain ⟨a, ha, hψa⟩ := Subgroup.mem_map.mp hbA
      refine Subgroup.mem_map.mpr ⟨a, ha, ?_⟩
      exact QuotientGroup.eq_iff_div_mem.mpr (by
        rw [MonoidHom.mem_ker, div_eq_mul_inv, map_mul, map_inv, hψa, mul_inv_cancel])
  obtain ⟨n, hnK, hn⟩ :=
    exists_conj_of_map_mk_eq (w183k3_ker_psiQuot_odd hcore) hA₁2 hB₁2 hmap
  let D : Subgroup (LGL 2 V) := cj (n : LGL 2 V) D₁
  have hnR : (n : LGL 2 V) ∈ R := n.2
  have hDT : D ≤ T ⊓ R := by
    have hmaple : A₁.map (MulAut.conj n).toMonoidHom ≤ (T ⊓ R).subgroupOf R := by
      rw [← hn]
      exact hB₁S
    intro x hx
    have hxR : x ∈ R := by
      obtain ⟨d, hd, hxd⟩ := Subgroup.mem_map.mp hx
      rw [← hxd]
      change (MulAut.conj (n : LGL 2 V)) d ∈ R
      rw [MulAut.conj_apply]
      exact R.mul_mem (R.mul_mem n.2 (hD₁R hd)) (R.inv_mem n.2)
    have hxsub : (⟨x, hxR⟩ : ↥R) ∈ (cj (n : LGL 2 V) D₁).subgroupOf R :=
      Subgroup.mem_subgroupOf.mpr hx
    rw [w183k3_subgroupOf_cj hD₁R] at hxsub
    exact Subgroup.mem_subgroupOf.mp (hmaple hxsub)
  have hDR : D ≤ R := hDT.trans inf_le_right
  have hDmem : D ∈ Γ := hc.invariant D₁ hD₁mem (n : LGL 2 V) (hRY hnR)
  have hD_img : imgOf ψ D = imgOf ψ D₁ := by
    change imgOf ψ (cj (n : LGL 2 V) D₁) = imgOf ψ D₁
    have hn1 : ψ n = 1 := MonoidHom.mem_ker.mp hnK
    rw [imgOf_cj ψ hD₁R n.2, hn1]
    exact w183k3_autConj_one (imgOf ψ D₁)
  have hDcard : 8 ≤ Nat.card D := by
    change 8 ≤ Nat.card (cj (n : LGL 2 V) (cj l D₀))
    rw [card_cj (g := (n : LGL 2 V)), card_cj (g := l)]
    exact hD₀card
  have hD_X : imgOf ψ D ≤ X₀ := by
    rw [hD_img, hD₁img]
    exact hg_le.trans inf_le_right
  have hDnorm : imgOf ψ (T ⊓ R) ⊓ X₀ ≤
      Subgroup.normalizer (imgOf ψ D : Set (MulAut (↥L ⧸ Subgroup.center ↥L))) := by
    rw [hD_img, hD₁img]
    exact hg_norm
  refine ⟨D, hDmem, hDT, hDcard, hD_X, hDnorm, ?_⟩
  intro B hBT hBX b hb
  have hbS : b ∈ T ⊓ R := hBT hb
  have hbR : b ∈ R := hbS.2
  have hψbN : ψ ⟨b, hbR⟩ ∈
      Subgroup.normalizer (imgOf ψ D : Set (MulAut (↥L ⧸ Subgroup.center ↥L))) :=
    hDnorm (le_inf (imgOf_mono ψ hBT) hBX (apply_mem_imgOf ψ hb hbR))
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hcjD : cj b D ≤ T ⊓ R := by
    have hSb : cj b (T ⊓ R) = T ⊓ R :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hbS)
    calc cj b D ≤ cj b (T ⊓ R) := Subgroup.map_mono hDT
      _ = T ⊓ R := hSb
  have himg : imgOf ψ (cj b D) = imgOf ψ D := by
    rw [imgOf_cj ψ hDR hbR]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hψbN
  exact w183k3_imgOf_injOn_S hcore hTR hcjD hDT himg

end W183K3

end CFSG.LocalAnalysis.WeakClosure81

end
