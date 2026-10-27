module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowHS119Rule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowHS119Syl
import CFSG.Quasithin.Background.HTransport
import CFSG.Quasithin.Background.B3Four2
public import CFSG.Quasithin.Background.E3Weak

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row.HS119

open CFSG.Quasithin CFSG.Quasithin.B45Exc.HSRu CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier
open CFSG.Quasithin.B1 CFSG.Quasithin.B3

section

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
private theorem congrHom_eq_conj (y : MulAut W) : H.congrHom y = MulAut.conj y := by
  ext f
  simp [MulAut.congr_apply, MulAut.conj_apply, MulAut.mul_apply]

omit [Finite W] in
private theorem map_congrHom_eq_map_conj (y : MulAut W) (A : Subgroup (MulAut W)) :
    A.map (H.congrHom y) = A.map (MulAut.conj y).toMonoidHom := by
  rw [congrHom_eq_conj y]
  rfl

private theorem card_ge_eight_of_mem_aSet_three {Y A : Subgroup (MulAut W)}
    (hA : A ∈ E3.aSet 3 Y) : 8 ≤ Nat.card A := by
  have hA2 : IsPGroup 2 A := E3.isPGroup_of_isElemAbelian2 hA.2.2.1
  have hm : 3 ≤ E3.mQuot A ⊥ := E3.le_mQuot_bot_of_mem_aSet hA
  have hrel := E3.relIndex_eq_two_pow (G := MulAut W) hA2 (⊥ : Subgroup (MulAut W))
  have hcard : Nat.card A = 2 ^ E3.mQuot A ⊥ := by
    rw [← Subgroup.relIndex_bot_left]
    exact hrel
  rw [hcard]
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ E3.mQuot A ⊥ := Nat.pow_le_pow_right (by norm_num) hm

omit [Finite W] in
private theorem mem_aSet_three_conj {Y A : Subgroup (MulAut W)} (hA : A ∈ E3.aSet 3 Y)
    {y : MulAut W} (hy : y ∈ Y) :
    A.map (MulAut.conj y).toMonoidHom ∈ E3.aSet 3 Y := by
  have hYmap : Y.map (MulAut.conj y).toMonoidHom = Y := by
    ext a
    rw [Subgroup.mem_map_equiv]
    constructor
    · intro ha
      rw [MulAut.conj_symm_apply] at ha
      exact by simpa [mul_assoc] using Y.mul_mem (Y.mul_mem hy ha) (Y.inv_mem hy)
    · intro ha
      exact Y.mul_mem (Y.mul_mem (Y.inv_mem hy) ha) hy
  have hYmap' : Y.map (H.congrHom y) = Y := by
    rw [congrHom_eq_conj y]
    exact hYmap
  have h := (H.map_mem_aSet_iff (e := y)).mpr hA
  rwa [hYmap', map_congrHom_eq_map_conj y A] at h

private theorem le_stabilizer_of_card_le {Y A : Subgroup (MulAut W)} (hA : A ∈ E3.aSet 3 Y)
    {z : W}
    (hcard : Nat.card A ≤
      4 * Nat.card ↥(A ⊓ (Y ⊓ MulAction.stabilizer (MulAut W) z))) :
    A ≤ Y ⊓ MulAction.stabilizer (MulAut W) z := by
  have hA2 : IsPGroup 2 A := E3.isPGroup_of_isElemAbelian2 hA.2.2.1
  let B : Subgroup (MulAut W) := A ⊓ (Y ⊓ MulAction.stabilizer (MulAut W) z)
  have hBA : B ≤ A := inf_le_left
  have hBpos : 0 < Nat.card ↥B := Nat.card_pos
  have hmul := E3.card_eq_two_pow_mul (G := MulAut W) hA2 hBA
  have hm : E3.mQuot A B ≤ 2 := by
    have h1 : 2 ^ E3.mQuot A B * Nat.card ↥B ≤ 2 ^ 2 * Nat.card ↥B := by
      calc 2 ^ E3.mQuot A B * Nat.card ↥B = Nat.card ↥A := hmul.symm
        _ ≤ 4 * Nat.card ↥B := hcard
        _ = 2 ^ 2 * Nat.card ↥B := by norm_num
    have h2 : 2 ^ E3.mQuot A B ≤ 2 ^ 2 := Nat.le_of_mul_le_mul_right h1 hBpos
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
  have hm3 : E3.mQuot A B < 3 := by omega
  have hfix : fixV B = fixV A := hA.2.2.2 B hBA hm3
  have hzB : z ∈ fixV B := by
    refine mem_fixV.2 fun b hb => ?_
    have hbC : b ∈ Y ⊓ MulAction.stabilizer (MulAut W) z := (Subgroup.mem_inf.1 hb).2
    simpa [MulAut.smul_def] using MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hbC).2
  have hzA : z ∈ fixV A := by rwa [← hfix]
  intro a ha
  refine ⟨hA.1 ha, ?_⟩
  refine MulAction.mem_stabilizer_iff.2 ?_
  simpa [MulAut.smul_def] using mem_fixV.1 hzA a ha

omit [Finite W] in
private theorem map_mem_fixV_iff {Y : Subgroup (MulAut W)} {g : MulAut W} (hg : g ∈ Y)
    (v : W) : g v ∈ fixV Y ↔ v ∈ fixV Y := by
  constructor
  · intro hv
    have h1 : g⁻¹ (g v) = g v := mem_fixV.1 hv g⁻¹ (Y.inv_mem hg)
    rw [MulAut.inv_apply_self] at h1
    rw [h1]
    exact hv
  · intro hv
    refine mem_fixV.2 fun y hy => ?_
    have h1 : (y * g) v = v := mem_fixV.1 hv (y * g) (Y.mul_mem hy hg)
    rw [MulAut.mul_apply] at h1
    rw [h1]
    exact (mem_fixV.1 hv g hg).symm

private theorem exists_mem_fixV_of_isSylowIn_ne {Y T T₂ : Subgroup (MulAut W)}
    (hT : IsSylowIn 2 T Y) (hT₂ : IsSylowIn 2 T₂ Y) (hfix : fixV T ≠ fixV Y) :
    ∃ z ∈ fixV T₂, z ∉ fixV Y := by
  have hle : fixV Y ≤ fixV T := by
    intro v hv
    exact mem_fixV.2 fun t ht => hv t (hT.le ht)
  have hnot : ¬ fixV T ≤ fixV Y := fun h => hfix (le_antisymm h hle)
  obtain ⟨w, hwT, hwY⟩ := Set.not_subset.1 hnot
  obtain ⟨x, hxY, hleT₂⟩ :=
    E3.exists_le_conj_of_isSylowIn hT hT₂.le hT₂.isPGroup
  have hcard : Nat.card T₂ = Nat.card T := by rw [hT₂.card_eq, hT.card_eq]
  have hcardConj : Nat.card (conjSubgroup T x) = Nat.card T :=
    Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective
  have heq : T₂ = conjSubgroup T x :=
    Subgroup.eq_of_le_of_card_ge hleT₂ (by rw [hcardConj, ← hcard])
  refine ⟨x⁻¹ • w, ?_, ?_⟩
  · have hconj : conjSubgroup T x = B1.conjAut x⁻¹ T := by
      change T.map (MulAut.conj x⁻¹).toMonoidHom = B1.conjAut x⁻¹ T
      rw [conjAut_eq_map_conj]
    rw [heq, hconj, B1.fixV_conjAut]
    exact Subgroup.mem_map_of_mem (x⁻¹).toMonoidHom hwT
  · intro hz
    have hxz : x (x⁻¹ w) = w := by rw [MulAut.apply_inv_self]
    have hxmem : x (x⁻¹ w) ∈ fixV Y := (map_mem_fixV_iff hxY (x⁻¹ w)).2 hz
    exact hwY (by rwa [hxz] at hxmem)

omit [Finite W] in
private theorem map_subgroupOf_conj_map {Y : Subgroup (MulAut W)}
    (φ : ↥Y →* Equiv.Perm (Fin 3850)) {X : Subgroup (MulAut W)} (hX : X ≤ Y)
    (y : ↥Y) :
    ((X.map (MulAut.conj (y : MulAut W)).toMonoidHom).subgroupOf Y).map φ =
      ((X.subgroupOf Y).map φ).map (MulAut.conj (φ y)).toMonoidHom := by
  ext p
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨a, ⟨b, hb, hba⟩, hap⟩
    let bY : ↥Y := ⟨b, hX hb⟩
    have hmem : (MulAut.conj (y : MulAut W)) b ∈ Y := by
      simp only [MulAut.conj_apply]
      exact Y.mul_mem (Y.mul_mem y.2 (hX hb)) (Y.inv_mem y.2)
    have heq : a = y * bY * y⁻¹ := by
      ext
      rw [← hba]
      rfl
    refine ⟨φ bY, ⟨bY, hb, rfl⟩, ?_⟩
    change (MulAut.conj (φ y)) (φ bY) = p
    rw [← hap, MulAut.conj_apply, heq, map_mul, map_mul, map_inv]
  · rintro ⟨x, ⟨bY, hb, hbx⟩, hxp⟩
    have hmem : (MulAut.conj (y : MulAut W)) (bY : MulAut W) ∈ Y := by
      simp only [MulAut.conj_apply]
      exact Y.mul_mem (Y.mul_mem y.2 bY.2) (Y.inv_mem y.2)
    have hsub : (⟨(MulAut.conj (y : MulAut W)) (bY : MulAut W), hmem⟩ : ↥Y) =
        y * bY * y⁻¹ := by
      ext
      rfl
    refine ⟨⟨(MulAut.conj (y : MulAut W)) (bY : MulAut W), hmem⟩,
      ⟨bY, hb, rfl⟩, ?_⟩
    rw [hsub, map_mul, map_mul, map_inv, ← hxp, ← hbx]
    exact (MulAut.conj_apply (φ y) (φ bY)).symm

omit [Finite W] in
private theorem exists_liftRange {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y)
    (ψ : Lift L Y hsR hsP) :
    ∃ (φ : ↥Y →* Equiv.Perm (Fin 3850)) (_ : Function.Injective φ)
      (R' : Subgroup (Equiv.Perm (Fin 3850))),
      R' = φ.range ∧ hsP ≤ R' ∧ R' ≤ hsR := by
  let e : ↥(L ⊔ Y) ≃* ↥Y := MulEquiv.subgroupCongr (sup_eq_right.2 hLY)
  let φ : ↥Y →* Equiv.Perm (Fin 3850) := hsR.subtype.comp (ψ.hom.comp e.symm.toMonoidHom)
  have hφinj : Function.Injective φ := by
    intro a b hab
    apply e.symm.injective
    apply ψ.inj
    exact Subtype.ext hab
  let R' : Subgroup (Equiv.Perm (Fin 3850)) := φ.range
  refine ⟨φ, hφinj, R', rfl, ?_, ?_⟩
  · intro p hp
    obtain ⟨x, -, hx⟩ := ψ.surj p hp
    refine ⟨e x, ?_⟩
    show ((ψ.hom (e.symm (e x)) : ↥hsR) : Equiv.Perm (Fin 3850)) = p
    rw [e.symm_apply_apply]
    exact hx
  · rintro a ⟨x, rfl⟩
    exact (ψ.hom (e.symm x)).2

private theorem quarterRule_transport {Y : Subgroup (MulAut W)}
    {φ : ↥Y →* Equiv.Perm (Fin 3850)} (hφinj : Function.Injective φ)
    {R' : Subgroup (Equiv.Perm (Fin 3850))} (hR' : R' = φ.range)
    {A₁ : Subgroup (MulAut W)} (hA₁ : A₁ ∈ E3.aSet 3 Y) (hA₁Y : A₁ ≤ Y) (z : W) :
    ∀ g ∈ R', Nat.card ↥((A₁.subgroupOf Y).map φ) ≤
      4 * Nat.card ↥(((A₁.subgroupOf Y).map φ).map (MulAut.conj g).toMonoidHom ⊓
        ((Y ⊓ MulAction.stabilizer (MulAut W) z).subgroupOf Y).map φ) →
      ((A₁.subgroupOf Y).map φ).map (MulAut.conj g).toMonoidHom ≤
        ((Y ⊓ MulAction.stabilizer (MulAut W) z).subgroupOf Y).map φ := by
  intro g hg hcard
  rw [hR'] at hg
  let C : Subgroup (MulAut W) := Y ⊓ MulAction.stabilizer (MulAut W) z
  let C' : Subgroup (Equiv.Perm (Fin 3850)) := (C.subgroupOf Y).map φ
  let A₁' : Subgroup (Equiv.Perm (Fin 3850)) := (A₁.subgroupOf Y).map φ
  change Nat.card ↥A₁' ≤
    4 * Nat.card ↥(A₁'.map (MulAut.conj g).toMonoidHom ⊓ C') at hcard
  change A₁'.map (MulAut.conj g).toMonoidHom ≤ C'
  obtain ⟨x, hx⟩ := hg
  rw [← hx] at hcard ⊢
  let A₂ : Subgroup (MulAut W) := A₁.map (MulAut.conj (x : MulAut W)).toMonoidHom
  have hA₂aSet : A₂ ∈ E3.aSet 3 Y := mem_aSet_three_conj hA₁ x.2
  have hconj : (A₂.subgroupOf Y).map φ = A₁'.map (MulAut.conj (φ x)).toMonoidHom :=
    map_subgroupOf_conj_map φ hA₁Y x
  have hsubInf : (A₂ ⊓ C).subgroupOf Y = A₂.subgroupOf Y ⊓ C.subgroupOf Y := by
    ext u
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  have hInfMap : (A₂.subgroupOf Y ⊓ C.subgroupOf Y).map φ =
      A₁'.map (MulAut.conj (φ x)).toMonoidHom ⊓ C' := by
    rw [Subgroup.map_inf _ _ _ hφinj, hconj]
  have hcardA₂ : Nat.card ↥A₂ = Nat.card ↥A₁ :=
    Subgroup.card_map_of_injective
      (f := (MulAut.conj (x : MulAut W)).toMonoidHom)
      (MulAut.conj (x : MulAut W)).injective
  have hcardA₁' : Nat.card ↥A₁' = Nat.card ↥A₂ := by
    change Nat.card ↥((A₁.subgroupOf Y).map φ) = Nat.card ↥A₂
    rw [Subgroup.card_map_of_injective hφinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₁Y).toEquiv, hcardA₂]
  have hcardInf : Nat.card ↥(A₁'.map (MulAut.conj (φ x)).toMonoidHom ⊓ C') =
      Nat.card ↥(A₂ ⊓ C) := by
    rw [← hInfMap, ← hsubInf, Subgroup.card_map_of_injective hφinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      ((inf_le_right : A₂ ⊓ C ≤ C).trans (inf_le_left : C ≤ Y))).toEquiv
  have hcard₂ : Nat.card ↥A₂ ≤ 4 * Nat.card ↥(A₂ ⊓ C) := by
    rw [← hcardA₁', ← hcardInf]
    exact hcard
  have hA₂C : A₂ ≤ C := le_stabilizer_of_card_le hA₂aSet hcard₂
  have hmap : (A₂.subgroupOf Y).map φ ≤ C' :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono Y hA₂C)
  rwa [hconj] at hmap

private theorem exists_conj_transport {Y : Subgroup (MulAut W)}
    {φ : ↥Y →* Equiv.Perm (Fin 3850)} (hφinj : Function.Injective φ)
    {R' : Subgroup (Equiv.Perm (Fin 3850))}
    {T₂ : Subgroup (MulAut W)} (hT₂syl : IsSylowIn 2 T₂ Y)
    (hT₂' : (T₂.subgroupOf Y).map φ = hsS ⊓ R')
    {A : Subgroup (MulAut W)} (hA : A ∈ E3.aSet 3 Y) :
    ∃ (A₁ : Subgroup (MulAut W)) (A₁' : Subgroup (Equiv.Perm (Fin 3850))),
      A₁ ∈ E3.aSet 3 Y ∧ A₁ ≤ T₂ ∧ A₁' = (A₁.subgroupOf Y).map φ ∧
      A₁' ≤ hsS ⊓ R' ∧ (∀ a ∈ A₁', a * a = 1) ∧ 8 ≤ Nat.card ↥A₁' := by
  have hA2 : IsPGroup 2 A := E3.isPGroup_of_isElemAbelian2 hA.2.2.1
  obtain ⟨y, hyY, hAy⟩ := E3.exists_le_conj_of_isSylowIn hT₂syl hA.1 hA2
  let A₁ : Subgroup (MulAut W) := A.map (MulAut.conj y).toMonoidHom
  have hA₁T₂ : A₁ ≤ T₂ := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨t, ht, htb⟩ := Subgroup.mem_map.1 (hAy hb)
    rw [← htb]
    simpa [MulAut.conj_apply, mul_assoc] using ht
  have hA₁Y : A₁ ≤ Y := hA₁T₂.trans hT₂syl.le
  have hA₁aSet : A₁ ∈ E3.aSet 3 Y := mem_aSet_three_conj hA hyY
  have hA₁8 : 8 ≤ Nat.card ↥A₁ := by
    change 8 ≤ Nat.card ↥(A.map (MulAut.conj y).toMonoidHom)
    rw [Subgroup.card_map_of_injective (MulAut.conj y).injective]
    exact card_ge_eight_of_mem_aSet_three hA
  let A₁' : Subgroup (Equiv.Perm (Fin 3850)) := (A₁.subgroupOf Y).map φ
  have hA₁'K : A₁' ≤ hsS ⊓ R' := by
    rw [← hT₂']
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono Y hA₁T₂)
  have hA₁'2 : ∀ a ∈ A₁', a * a = 1 := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 ha
    have hb2 : (b : MulAut W) * (b : MulAut W) = 1 := by
      simpa [pow_two] using hA₁aSet.2.2.1.2 (b : MulAut W) hb
    have hb2' : b * b = 1 := Subtype.ext hb2
    rw [← map_mul, hb2', map_one]
  have hA₁'8 : 8 ≤ Nat.card ↥A₁' := by
    change 8 ≤ Nat.card ↥((A₁.subgroupOf Y).map φ)
    rw [Subgroup.card_map_of_injective (f := φ) hφinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₁Y).toEquiv]
    exact hA₁8
  exact ⟨A₁, A₁', hA₁aSet, hA₁T₂, rfl, hA₁'K, hA₁'2, hA₁'8⟩

end


private theorem exists_transportSylow {W : Type} [CommGroup W] [Finite W]
    {Y T : Subgroup (MulAut W)}
    (hT : IsSylowIn 2 T Y) (hfix : fixV T ≠ fixV Y)
    {φ : ↥Y →* Equiv.Perm (Fin 3850)} (hφinj : Function.Injective φ)
    {R' : Subgroup (Equiv.Perm (Fin 3850))} (hR' : R' = φ.range)
    (hPR : hsP ≤ R') (hRR : R' ≤ hsR) :
    ∃ (T₂ : Subgroup (MulAut W)), IsSylowIn 2 T₂ Y ∧
      (T₂.subgroupOf Y).map φ = hsS ⊓ R' ∧ ∃ z ∈ fixV T₂, z ∉ fixV Y := by
  let K : Subgroup (Equiv.Perm (Fin 3850)) := hsS ⊓ R'
  let T₂ : Subgroup (MulAut W) := (K.comap φ).map Y.subtype
  have hK : IsSylowIn 2 K R' := isSylowIn_hsS_inf hPR hRR
  have hcardR' : Nat.card ↥R' = Nat.card ↥Y := by
    rw [hR', MonoidHom.range_eq_map, Subgroup.card_map_of_injective hφinj]
    simp
  have hsubT₂ : T₂.subgroupOf Y = K.comap φ := by
    ext x
    simp only [Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hyx' : y = x := Subtype.ext hyx
      simpa [hyx'] using hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hKR : K ≤ φ.range := by
    rw [← hR']
    exact inf_le_right
  have hT₂' : (T₂.subgroupOf Y).map φ = K := by
    rw [hsubT₂]
    exact Subgroup.map_comap_eq_self hKR
  have hcardT₂ : Nat.card ↥T₂ = Nat.card ↥K := by
    change Nat.card ↥((K.comap φ).map Y.subtype) = Nat.card ↥K
    rw [Subgroup.card_map_of_injective (f := Y.subtype) (by intro a b h; exact Subtype.ext h)]
    rw [← Subgroup.card_map_of_injective (f := φ) hφinj,
      Subgroup.map_comap_eq_self hKR]
  have hT₂syl : IsSylowIn 2 T₂ Y := by
    refine isSylowIn_of_card_eq (Subgroup.map_subtype_le _) ?_
    rw [hcardT₂, hK.card_eq, hcardR']
  exact ⟨T₂, hT₂syl, hT₂', exists_mem_fixV_of_isSylowIn_ne hT hT₂syl hfix⟩


theorem not_mem_aSet_three_of_lift {W : Type} [CommGroup W] [Finite W]
    {Y L T : Subgroup (MulAut W)} (hLY : L ≤ Y) (ψ : Lift L Y hsR hsP) (hT : IsSylowIn 2 T Y)
    (hfix : fixV T ≠ fixV Y) (A : Subgroup (MulAut W)) : A ∉ E3.aSet 3 Y := by
  intro hA
  obtain ⟨φ, hφinj, R', hR', hPR, hRR⟩ := exists_liftRange hLY ψ
  obtain ⟨T₂, hT₂syl, hT₂', z, hzT₂, hzY⟩ :=
    exists_transportSylow hT hfix hφinj hR' hPR hRR
  obtain ⟨A₁, A₁', hA₁aSet, hA₁T₂, hA₁'eq, hA₁'K, hA₁'2, hA₁'8⟩ :=
    exists_conj_transport hφinj hT₂syl hT₂' hA
  let C : Subgroup (MulAut W) := Y ⊓ MulAction.stabilizer (MulAut W) z
  let C' : Subgroup (Equiv.Perm (Fin 3850)) := (C.subgroupOf Y).map φ
  have hT₂C : T₂ ≤ C := by
    intro t ht
    refine ⟨hT₂syl.le ht, MulAction.mem_stabilizer_iff.2 ?_⟩
    simpa [MulAut.smul_def] using mem_fixV.1 hzT₂ t ht
  have hKC' : hsS ⊓ R' ≤ C' := by
    rw [← hT₂']
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono Y hT₂C)
  have hcl : ∀ g ∈ R', Nat.card ↥A₁' ≤
      4 * Nat.card ↥(A₁'.map (MulAut.conj g).toMonoidHom ⊓ C') →
      A₁'.map (MulAut.conj g).toMonoidHom ≤ C' := by
    intro g hg hcard
    rw [hA₁'eq] at hcard ⊢
    exact quarterRule_transport hφinj hR' hA₁aSet (hA₁T₂.trans hT₂syl.le) z g hg hcard
  have hR'C' : R' ≤ C' :=
    hs119_le_of_ruleClosed hPR hRR hA₁'K hA₁'2 hA₁'8 hKC' hcl
  have hYC : Y ≤ C := by
    intro y hy
    have hyR' : φ ⟨y, hy⟩ ∈ R' := by rw [hR']; exact ⟨⟨y, hy⟩, rfl⟩
    have hyC' : φ ⟨y, hy⟩ ∈ C' := hR'C' hyR'
    change φ ⟨y, hy⟩ ∈ (C.subgroupOf Y).map φ at hyC'
    obtain ⟨c, hc, hcy⟩ := Subgroup.mem_map.1 hyC'
    have hceq : c = ⟨y, hy⟩ := hφinj hcy
    have hcy' : (c : MulAut W) ∈ C := hc
    rw [hceq] at hcy'
    simpa using hcy'
  have hzfixY : z ∈ fixV Y := by
    refine mem_fixV.2 fun y hy => ?_
    have hyC := hYC hy
    have hyStab : y ∈ MulAction.stabilizer (MulAut W) z := (Subgroup.mem_inf.1 hyC).2
    simpa [MulAut.smul_def] using MulAction.mem_stabilizer_iff.1 hyStab
  exact hzY hzfixY

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row.HS119
