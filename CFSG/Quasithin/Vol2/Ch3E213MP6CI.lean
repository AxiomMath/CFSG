module

public import CFSG.Quasithin.Vol2.Ch3E213MSp4
public import CFSG.Quasithin.Vol2.Ch3E213MP6CB

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.Open CFSG.QuasithinUnique B6
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  (antiSp glMat minorJ minorJ_apply uElt uMat glMat_uElt antiUnipotent antiUnipotentCenter
    uElt_mem_antiUnipotent mem_antiSp transpose_mul_minorJ_mul_apply antiSp_ext)

variable {G : Type} [Group G]

theorem barIn_inf (M H X : Subgroup G) :
    barIn M H (M ⊓ X) = barIn M H M ⊓ barIn M H X := by
  refine le_antisymm (le_inf ?_ ?_) ?_
  · exact Subgroup.map_mono fun _ hx => hx.1
  · exact Subgroup.map_mono fun _ hx => hx.2
  · rintro z ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
    have hk : a⁻¹ * b ∈ kerIn (M.subgroupOf H) ⊤ := by
      rw [← QuotientGroup.eq]
      exact hab.symm
    have hkM : a⁻¹ * b ∈ M.subgroupOf H := by
      simpa using hk 1 (Subgroup.mem_top 1)
    have hbM : b ∈ M.subgroupOf H := by
      have := (M.subgroupOf H).mul_mem ha hkM
      rwa [mul_inv_cancel_left] at this
    exact ⟨b, ⟨hbM, hb⟩, hab⟩

theorem barIn_mono {M H X Y : Subgroup G} (h : X ≤ Y) : barIn M H X ≤ barIn M H Y :=
  Subgroup.map_mono fun _ hx => h hx

theorem star_inf {M H : Subgroup G} (hMH : M ≤ H) (X : Subgroup G) :
    E2.star M H (M ⊓ X) = E2.star M H M ⊓ E2.star M H X := by
  rw [← map_barIn_starEquiv hMH, ← map_barIn_starEquiv hMH, ← map_barIn_starEquiv hMH,
    barIn_inf, Subgroup.map_inf_eq _ _ _ (starEquiv hMH).injective]

section Coord

variable {H T M V K : Subgroup G} {k : Type} [Field k] [Finite k] [CharP k 2]

@[expose] noncomputable def coordMap (D : Sp4Data H T M V K k) :
    antiSp k →* (↥H ⧸ kerIn (M.subgroupOf H) ⊤) :=
  (kZero H M).subtype.comp D.θ.symm.toMonoidHom

theorem coordMap_injective (D : Sp4Data H T M V K k) : Function.Injective (coordMap D) :=
  (Subgroup.subtype_injective _).comp D.θ.symm.injective

theorem coordMap_mem_barIn_iff (D : Sp4Data H T M V K k) (X : Subgroup G) (y : antiSp k) :
    coordMap D y ∈ barIn M H X ↔ y ∈ coordIn D.θ X := by
  constructor
  · intro h
    exact ⟨D.θ.symm y, h, by simp⟩
  · rintro ⟨x, hx, rfl⟩
    have e : coordMap D (D.θ x) = x := by simp [coordMap]
    change coordMap D (D.θ x) ∈ barIn M H X
    rw [e]
    exact Subgroup.mem_subgroupOf.mp hx

theorem barIn_inf_map_coordMap (D : Sp4Data H T M V K k) (X : Subgroup G)
    (Z : Subgroup (antiSp k)) :
    barIn M H X ⊓ Z.map (coordMap D) = (coordIn D.θ X ⊓ Z).map (coordMap D) := by
  ext a
  constructor
  · rintro ⟨ha, z, hz, rfl⟩
    exact ⟨z, ⟨(coordMap_mem_barIn_iff D X z).mp ha, hz⟩, rfl⟩
  · rintro ⟨z, ⟨hzX, hz⟩, rfl⟩
    exact ⟨(coordMap_mem_barIn_iff D X z).mpr hzX, z, hz, rfl⟩

theorem map_coordMap_coordIn (D : Sp4Data H T M V K k) {X : Subgroup G}
    (hX : barIn M H X ≤ kZero H M) : (coordIn D.θ X).map (coordMap D) = barIn M H X := by
  ext a
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (coordMap_mem_barIn_iff D X z).mpr hz
  · intro ha
    refine ⟨D.θ ⟨a, hX ha⟩, (coordMap_mem_barIn_iff D X _).mp ?_, ?_⟩
    · simpa [coordMap] using ha
    · simp [coordMap]

theorem coordMap_mem_kZero (D : Sp4Data H T M V K k) (y : antiSp k) :
    coordMap D y ∈ kZero H M :=
  (D.θ.symm y).2

theorem exists_coordMap_eq (D : Sp4Data H T M V K k) {a : ↥H ⧸ kerIn (M.subgroupOf H) ⊤}
    (ha : a ∈ kZero H M) : ∃ a' : antiSp k, coordMap D a' = a :=
  ⟨D.θ ⟨a, ha⟩, by simp [coordMap]⟩

theorem normalizer_le_coordIn_M (D : Sp4Data H T M V K k) :
    Subgroup.normalizer (antiUnipotent k : Set (antiSp k)) ≤ coordIn D.θ M := by
  intro y hy
  rw [← coordMap_mem_barIn_iff]
  refine D.borel_le (Subgroup.mem_inf.mpr ⟨coordMap_mem_kZero D y, ?_⟩)
  rw [Subgroup.mem_normalizer_iff]
  intro a
  have key : ∀ a' : antiSp k, coordMap D a' ∈ barIn M H T ⊓ kZero H M ↔
      a' ∈ antiUnipotent k := fun a' => by
    rw [← D.sylow, ← coordMap_mem_barIn_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, coordMap_mem_kZero D a'⟩⟩
  have hconj : ∀ a' : antiSp k, coordMap D y * coordMap D a' * (coordMap D y)⁻¹ =
      coordMap D (y * a' * y⁻¹) := fun a' => by rw [map_mul, map_mul, map_inv]
  constructor
  · intro ha
    obtain ⟨a', rfl⟩ := exists_coordMap_eq D ha.2
    rw [hconj, key]
    exact (Subgroup.mem_normalizer_iff.mp hy a').mp ((key a').mp ha)
  · intro ha
    have haK : a ∈ kZero H M := by
      have h1 := (kZero H M).mul_mem ((kZero H M).mul_mem
        ((kZero H M).inv_mem (coordMap_mem_kZero D y)) ha.2) (coordMap_mem_kZero D y)
      rwa [show (coordMap D y)⁻¹ * (coordMap D y * a * (coordMap D y)⁻¹) * coordMap D y = a by
        group] at h1
    obtain ⟨a', rfl⟩ := exists_coordMap_eq D haK
    rw [hconj, key] at ha
    exact (key a').mpr ((Subgroup.mem_normalizer_iff.mp hy a').mpr ha)

theorem coordIn_M_le_normalizer [Finite G] (hMH : M ≤ H)
    (hB : E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K))) (D : Sp4Data H T M V K k)
    (hTM : T ≤ M) :
    coordIn D.θ M ≤ Subgroup.normalizer (antiUnipotent k : Set (antiSp k)) := by
  set e := starEquiv hMH with he
  set Ψ : antiSp k →* E2.StarQuot M H := e.toMonoidHom.comp (coordMap D) with hΨ
  have hΨinj : Function.Injective Ψ := e.injective.comp (coordMap_injective D)
  have hΨmem : ∀ (X : Subgroup G) (y : antiSp k), Ψ y ∈ E2.star M H X ↔ y ∈ coordIn D.θ X := by
    intro X y
    rw [← map_barIn_starEquiv hMH X, ← coordMap_mem_barIn_iff]
    constructor
    · rintro ⟨z, hz, hze⟩
      rwa [← e.injective hze]
    · intro h
      exact ⟨_, h, rfl⟩
  have hΨK : ∀ y, Ψ y ∈ E2.star M H K := fun y => by
    rw [hΨmem, ← coordMap_mem_barIn_iff, ← D.kZero_eq]
    exact coordMap_mem_kZero D y
  obtain ⟨S, hSyl, hMK⟩ := hB
  have hMN : ∀ y ∈ coordIn D.θ M, Ψ y ∈ Subgroup.normalizer (S : Set (E2.StarQuot M H)) := by
    intro y hy
    have h1 : Ψ y ∈ E2.star M H (M ⊓ K) := by
      rw [star_inf hMH]
      exact ⟨(hΨmem M y).mpr hy, hΨK y⟩
    rw [hMK] at h1
    exact h1.2
  have hU := (CFSG.QuasithinUnique.Setup.X7b.card_and_isSylowTwoOf_antiUnipotent (K := k)).2
  have hUT : antiUnipotent k ≤ coordIn D.θ M := by
    rw [← D.sylow]
    exact Subgroup.map_mono fun _ hx => barIn_mono hTM hx
  have hR : (antiUnipotent k).map Ψ ≤ S := by
    have hRN : (antiUnipotent k).map Ψ ≤ Subgroup.normalizer (S : Set (E2.StarQuot M H)) := by
      rintro _ ⟨u, hu, rfl⟩
      exact hMN u (hUT hu)
    have h2 : IsPGroup 2 ((antiUnipotent k).map Ψ) := hU.isPGroup.map Ψ
    have hsup := h2.to_sup_of_normal_right' hSyl.isPGroup hRN
    have hle : (antiUnipotent k).map Ψ ⊔ S ≤ E2.star M H K :=
      sup_le (by rintro _ ⟨u, -, rfl⟩; exact hΨK u) hSyl.le
    have h3 := hSyl.eq_of_le le_sup_right hle hsup
    rw [← h3]
    exact le_sup_left
  have hSig : S.comap Ψ = antiUnipotent k :=
    hU.eq_of_le (fun u hu => hR ⟨u, hu, rfl⟩) le_top (hSyl.isPGroup.comap_of_injective Ψ hΨinj)
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro u
  rw [← SetLike.mem_coe, ← SetLike.mem_coe, ← hSig]
  simp only [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_inv]
  exact Subgroup.mem_normalizer_iff.mp (hMN y hy) (Ψ u)

theorem coordIn_M_eq [Finite G] (hMH : M ≤ H)
    (hB : E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K))) (D : Sp4Data H T M V K k)
    (hTM : T ≤ M) :
    coordIn D.θ M = Subgroup.normalizer (antiUnipotent k : Set (antiSp k)) :=
  le_antisymm (coordIn_M_le_normalizer hMH hB D hTM) (normalizer_le_coordIn_M D)

end Coord

section Core

variable {k : Type} [Field k] [CharP k 2]

theorem kerIn_inf_normalizer_eq_bot {F₀ : Subfield k} {c : antiSp k} (hc : IsUpper c) :
    kerIn ((subfieldSp F₀).map (MulAut.conj c).toMonoidHom ⊓
        Subgroup.normalizer (antiUnipotent k : Set (antiSp k)))
      ((subfieldSp F₀).map (MulAut.conj c).toMonoidHom) = ⊥ := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  set N := Subgroup.normalizer (antiUnipotent k : Set (antiSp k)) with hNdef
  have hNci : c⁻¹ ∈ N := mem_normalizer_of_isUpper (isUpper_inv hc)
  rw [eq_bot_iff]
  intro z hz
  set z' := c⁻¹ * z * c with hz'
  have hN : ∀ w ∈ subfieldSp F₀, w * z' * w⁻¹ ∈ N := by
    intro w hw
    have h1 := (hz (c * w * c⁻¹) ⟨w, hw, rfl⟩).2
    have e : w * z' * w⁻¹ = c⁻¹ * ((c * w * c⁻¹) * z * (c * w * c⁻¹)⁻¹) * c⁻¹⁻¹ := by
      rw [hz']
      group
    rw [e]
    exact N.mul_mem (N.mul_mem hNci h1) (N.inv_mem hNci)
  have hN1 : z' ∈ N := by simpa using hN 1 (subfieldSp F₀).one_mem
  have hwu1 : wLong * uElt 1 0 0 0 ∈ subfieldSp F₀ :=
    (subfieldSp F₀).mul_mem (wLong_mem_subfieldSp F₀)
      (uElt_mem_subfieldSp F₀.one_mem F₀.zero_mem F₀.zero_mem F₀.zero_mem)
  have hwu2 : wLong * uElt 0 0 0 1 ∈ subfieldSp F₀ :=
    (subfieldSp F₀).mul_mem (wLong_mem_subfieldSp F₀)
      (uElt_mem_subfieldSp F₀.zero_mem F₀.zero_mem F₀.zero_mem F₀.one_mem)
  have hA := CFSG.Quasithin.SteinbergBS.upper_of_mem_normalizer hN1
  have hJ := CFSG.Quasithin.SteinbergBS.upper_of_mem_normalizer
    (hN wLong (wLong_mem_subfieldSp F₀))
  have hU1 := CFSG.Quasithin.SteinbergBS.upper_of_mem_normalizer (hN _ hwu1)
  have hU2 := CFSG.Quasithin.SteinbergBS.upper_of_mem_normalizer (hN _ hwu2)
  set A := glMat (z' : GL (Fin 4) k) with hAdef
  have mJ : glMat ((wLong * z' * wLong⁻¹ : antiSp k) : GL (Fin 4) k) =
      minorJ k * A * minorJ k := rfl
  have m1 : glMat (((wLong * uElt 1 0 0 0) * z' * (wLong * uElt 1 0 0 0)⁻¹ : antiSp k) :
      GL (Fin 4) k) = minorJ k * uMat 1 0 0 0 * A * (uMat 1 (0 + 1 * 0) 0 0 * minorJ k) := rfl
  have m2 : glMat (((wLong * uElt 0 0 0 1) * z' * (wLong * uElt 0 0 0 1)⁻¹ : antiSp k) :
      GL (Fin 4) k) = minorJ k * uMat 0 0 0 1 * A * (uMat 0 (0 + 0 * 1) 0 1 * minorJ k) := rfl
  have l10 := hA 1 0 (by decide)
  have l20 := hA 2 0 (by decide)
  have l30 := hA 3 0 (by decide)
  have l21 := hA 2 1 (by decide)
  have l31 := hA 3 1 (by decide)
  have l32 := hA 3 2 (by decide)
  have u01 := hJ 3 2 (by decide)
  have u02 := hJ 3 1 (by decide)
  have u03 := hJ 3 0 (by decide)
  have u12 := hJ 2 1 (by decide)
  have u13 := hJ 2 0 (by decide)
  have u23 := hJ 1 0 (by decide)
  rw [mJ] at u01 u02 u03 u12 u13 u23
  simp [Matrix.mul_apply, Fin.sum_univ_four, minorJ_apply] at u01 u02 u03 u12 u13 u23
  have d01 := hU1 3 2 (by decide)
  have d23 := hU1 1 0 (by decide)
  have d12 := hU2 2 1 (by decide)
  rw [m1] at d01 d23
  rw [m2] at d12
  simp [Matrix.mul_apply, Fin.sum_univ_four, minorJ_apply, uMat, Matrix.vecMul, dotProduct,
    l10, l20, l30, l21, l31, l32, u01, u02, u03, u12, u13, u23] at d01 d23 d12
  have hJz := CFSG.ComponentClassification.UnbalancedCatalog.SpChain.mem_antiSp.mp z'.2
  have e03 := congrFun (congrFun hJz 0) 3
  have e12 := congrFun (congrFun hJz 1) 2
  rw [transpose_mul_minorJ_mul_apply, minorJ_apply] at e03 e12
  simp only [← hAdef, l10, l20, l30, l21, l31, l32, u01, u02, u03, u12, u13, u23] at e03 e12
  norm_num at e03 e12
  have h01 : A 1 1 = A 0 0 := by linear_combination d01 - A 0 0 * h2
  have h12 : A 2 2 = A 1 1 := by linear_combination d12 - A 1 1 * h2
  have h23 : A 3 3 = A 2 2 := by linear_combination d23 - A 2 2 * h2
  have hsq : (A 1 1 - 1) ^ 2 = 0 := by
    rw [h12] at e12
    linear_combination e12 + (1 - A 1 1) * h2
  have a11 : A 1 1 = 1 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    linear_combination this
  have a00 : A 0 0 = 1 := by rw [← h01, a11]
  have a22 : A 2 2 = 1 := by rw [h12, a11]
  have a33 : A 3 3 = 1 := by rw [h23, a22]
  have hz'1 : z' = 1 := by
    apply antiSp_ext
    rw [← hAdef]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [l10, l20, l30, l21, l31, l32, u01, u02, u03, u12, u13, u23, a00, a11, a22, a33]
  rw [Subgroup.mem_bot]
  calc z = c * z' * c⁻¹ := by rw [hz']; group
    _ = 1 := by rw [hz'1]; group

end Core

end CFSG.Quasithin.Ch3E213M
