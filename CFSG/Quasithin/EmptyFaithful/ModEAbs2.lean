module

public import CFSG.Quasithin.EmptyFaithful.ModEAbs
public import CFSG.Quasithin.Background.F6GoldschmidtList
public import CFSG.Quasithin.Background.F6Basic

public section

namespace CFSG.Quasithin.ModE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F6

theorem d12_aux : ∀ y : DihedralGroup 6, y * y = 1 →
    (∀ g : DihedralGroup 6, y * (g * y * g⁻¹) = (g * y * g⁻¹) * y) → y = 1 ∨ y = DihedralGroup.r 3 := by
  decide

theorem s3_aux : ∀ y : Equiv.Perm (Fin 3), y * y = 1 →
    (∀ g : Equiv.Perm (Fin 3), y * (g * y * g⁻¹) = (g * y * g⁻¹) * y) → y = 1 := by
  decide

theorem z4sq_card :
    Nat.card {x : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) // x * x = 1} = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem q8sq_card : Nat.card {x : QuaternionGroup 2 // x * x = 1} = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem z2d8_noncomm : ¬ ∀ x y : Multiplicative (ZMod 2) × DihedralGroup 4, x * y = y * x := by
  decide

theorem card_z2d8 : Nat.card (Multiplicative (ZMod 2) × DihedralGroup 4) = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem z2d8_bound (B : Subgroup (Multiplicative (ZMod 2) × DihedralGroup 4))
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) : Nat.card B ≤ 8 := by
  by_contra h8
  push Not at h8
  have hdvd := Subgroup.card_subgroup_dvd_card B
  rw [card_z2d8] at hdvd
  obtain ⟨k, hk⟩ := hdvd
  have hk1 : k = 1 := by
    rcases Nat.lt_or_ge k 2 with h | h
    · rcases k with _ | _ | k
      · omega
      · rfl
      · omega
    · nlinarith
  rw [hk1, mul_one] at hk
  have htop : B = ⊤ := Subgroup.eq_top_of_card_eq B (by rw [card_z2d8]; exact hk.symm)
  apply z2d8_noncomm
  intro x y
  have hx : x ∈ B := by rw [htop]; exact Subgroup.mem_top x
  have hy : y ∈ B := by rw [htop]; exact Subgroup.mem_top y
  exact hcomm x hx y hy

theorem wreath_bound (E : Subgroup (Multiplicative (ZMod 4) ≀ᵣ Multiplicative (ZMod 2)))
    (hsq : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 8 := by
  have h := card_eq_ker_mul (RegularWreathProduct.rightHom :
    Multiplicative (ZMod 4) ≀ᵣ Multiplicative (ZMod 2) →* Multiplicative (ZMod 2)) E
  have h1 : Nat.card (E ⊓ (RegularWreathProduct.rightHom :
      Multiplicative (ZMod 4) ≀ᵣ Multiplicative (ZMod 2) →* Multiplicative (ZMod 2)).ker :
      Subgroup _) ≤ 4 := by
    let f : ↥(E ⊓ (RegularWreathProduct.rightHom :
        Multiplicative (ZMod 4) ≀ᵣ Multiplicative (ZMod 2) →* Multiplicative (ZMod 2)).ker) →
        {g : Multiplicative (ZMod 2) → Multiplicative (ZMod 4) // ∀ i, g i * g i = 1} :=
      fun x => ⟨x.1.left, fun i => by
        have hx := hsq x.1 x.2.1
        have hr : x.1.right = 1 := x.2.2
        have hmul : (x.1 * x.1).left i = x.1.left i * x.1.left (x.1.right⁻¹ * i) := rfl
        rw [hr, hx] at hmul
        have h1 : ∀ j : Multiplicative (ZMod 2), (1 : Multiplicative (ZMod 2))⁻¹ * j = j := by decide
        rw [h1 i] at hmul
        exact hmul.symm⟩
    have hf : Function.Injective f := by
      intro a b hab
      have h1 : a.1.left = b.1.left := congrArg Subtype.val hab
      have hra : a.1.right = 1 := a.2.2
      have hrb : b.1.right = 1 := b.2.2
      exact Subtype.ext (RegularWreathProduct.ext h1 (hra.trans hrb.symm))
    have hcard : Nat.card {g : Multiplicative (ZMod 2) → Multiplicative (ZMod 4) // ∀ i, g i * g i = 1} = 4 := by
      rw [Nat.card_eq_fintype_card]
      decide
    exact (Nat.card_le_card_of_injective f hf).trans hcard.le
  have h2 : Nat.card (E.map (RegularWreathProduct.rightHom :
      Multiplicative (ZMod 4) ≀ᵣ Multiplicative (ZMod 2) →* Multiplicative (ZMod 2))) ≤ 2 := by
    refine (Subgroup.card_le_card_group _).trans ?_
    rw [Nat.card_eq_fintype_card]
    decide
  rw [h]
  calc _ ≤ 4 * 2 := Nat.mul_le_mul h1 h2
    _ = 8 := rfl

theorem tb_of_iso {D X : Type*} [Group D] [Group X] {T : Subgroup D} (e : ↥T ≃* X)
    (hX : ∀ B' : Subgroup X, (∀ x ∈ B', x * x = 1) → Nat.card B' ≤ 8) :
    ∀ B : Subgroup D, B ≤ T → IsElemAbelian 2 B → Nat.card B ≤ 8 := by
  intro B hBT hB
  let B' : Subgroup X := (B.subgroupOf T).map e.toMonoidHom
  have hcard : Nat.card B' = Nat.card B := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBT).toEquiv
  have hsq : ∀ x ∈ B', x * x = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    have h1 : b * b = 1 := Subtype.ext (by
      have := hB.2 (b : D) hb
      rw [Subgroup.coe_mul, ← pow_two]
      exact this)
    show e b * e b = 1
    rw [← map_mul, h1, map_one]
  rw [← hcard]
  exact hX B' hsq

theorem cp_bound {K : Type*} [Group K] [Finite K] {N E : Subgroup K}
    (hN : IsCentralProduct₂ ↥N (QuaternionGroup 2) (QuaternionGroup 2)) (hEN : E ≤ N)
    (hsq : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 8 := by
  obtain ⟨A', B', hgen, hcomm, ⟨eA⟩, ⟨eB⟩, hZ⟩ := hN
  have hAB : A' ≤ Subgroup.normalizer (B' : Set ↥N) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have h1 := hcomm a ha h hh
      rw [mul_inv_eq_iff_eq_mul.2 h1]
      exact hh
    · intro hh
      have h1 := hcomm a⁻¹ (A'.inv_mem ha) _ hh
      have h2 : h * a⁻¹ = (a * h * a⁻¹) * a⁻¹ := by
        calc h * a⁻¹ = a⁻¹ * (a * h * a⁻¹) := by group
          _ = (a * h * a⁻¹) * a⁻¹ := h1
      have h3 : h = a * h * a⁻¹ := mul_right_cancel h2
      rw [h3]
      exact hh
  have hBnorm : B'.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hgen]
    exact sup_le hAB Subgroup.le_normalizer
  let ψ : ↥N →* ↥N ⧸ B' := QuotientGroup.mk' B'
  have hker : ψ.ker = B' := QuotientGroup.ker_mk' B'
  have hsurj : Function.Surjective (ψ.comp A'.subtype) := by
    intro q
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
    have hn : n ∈ ((A' ⊔ B' : Subgroup ↥N) : Set ↥N) := by rw [hgen]; trivial
    rw [Subgroup.coe_mul_of_left_le_normalizer_right A' B' hAB] at hn
    obtain ⟨a, ha, b, hb, rfl⟩ := hn
    refine ⟨⟨a, ha⟩, ?_⟩
    have hψb : ψ b = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact hb
    show ψ a = ψ (a * b)
    rw [map_mul, hψb, mul_one]
  have hjker := Subgroup.card_ker_mul_card_of_surjective hsurj
  have hA8 : Nat.card A' = 8 := by
    rw [Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card]
    decide
  have hZle : ((A' ⊓ B' : Subgroup ↥N).subgroupOf A') ≤ (ψ.comp A'.subtype).ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hx1 : (x : ↥N) ∈ B' := (Subgroup.mem_subgroupOf.1 hx).2
    show ψ x = 1
    rw [← MonoidHom.mem_ker, hker]
    exact hx1
  have hZcard : Nat.card ((A' ⊓ B' : Subgroup ↥N).subgroupOf A') = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : A' ⊓ B' ≤ A')).toEquiv]
    exact hZ
  have hjk2 : 2 ≤ Nat.card (ψ.comp A'.subtype).ker := by
    rw [← hZcard]
    exact Subgroup.card_le_of_le hZle
  have hq4 : Nat.card (↥N ⧸ B') ≤ 4 := by
    rw [hA8] at hjker
    have := Nat.mul_le_mul_right (Nat.card (↥N ⧸ B')) hjk2
    omega
  let E' : Subgroup ↥N := E.subgroupOf N
  have hE'card : Nat.card E' = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv
  have hE'sq : ∀ x ∈ E', x * x = 1 := fun x hx => Subtype.ext (by
    have := hsq (x : K) (Subgroup.mem_subgroupOf.1 hx)
    rw [Subgroup.coe_mul]
    exact this)
  have h := card_eq_ker_mul ψ E'
  let e : ↥ψ.ker ≃* QuaternionGroup 2 := (MulEquiv.subgroupCongr hker).trans eB
  have h1 : Nat.card (E' ⊓ ψ.ker : Subgroup ↥N) ≤ 2 :=
    (card_ker_part ψ e E' hE'sq).trans q8sq_card.le
  have h2 : Nat.card (E'.map ψ) ≤ 4 := (Subgroup.card_le_card_group _).trans hq4
  rw [← hE'card, h]
  calc _ ≤ 2 * 4 := Nat.mul_le_mul h1 h2
    _ = 8 := rfl

theorem ori1 {D : Type*} [Group D] [Finite D] {K A : Subgroup D} (hAK : A ≤ K) (hAel : IsElemAbelian 2 A)
    (hAn : K ≤ Subgroup.normalizer (A : Set D)) (φ : ↥K →* DihedralGroup 6)
    (hφ : Function.Surjective φ)
    (e : ↥φ.ker ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) : Nat.card A ≤ 8 := by
  let B : Subgroup ↥K := A.subgroupOf K
  have hBcard : Nat.card B = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv
  have hBsq : ∀ b ∈ B, b * b = 1 := fun b hb => Subtype.ext (by
    have := hAel.2 (b : D) (Subgroup.mem_subgroupOf.1 hb)
    rw [Subgroup.coe_mul, ← pow_two]
    exact this)
  have hBcomm : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b := fun b hb b' hb' => Subtype.ext (by
    have h := congrArg Subtype.val (hAel.1.is_comm.comm ⟨(b : D), Subgroup.mem_subgroupOf.1 hb⟩
      ⟨(b' : D), Subgroup.mem_subgroupOf.1 hb'⟩)
    exact h)
  have hBnorm : ∀ k : ↥K, ∀ b ∈ B, k * b * k⁻¹ ∈ B := fun k b hb =>
    Subgroup.mem_subgroupOf.2 (by
      have := (Subgroup.mem_normalizer_iff.1 (hAn k.2) (b : D)).1 (Subgroup.mem_subgroupOf.1 hb)
      simpa using this)
  have h := card_eq_ker_mul φ B
  have h1 : Nat.card (B ⊓ φ.ker : Subgroup ↥K) ≤ 4 := (card_ker_part φ e B hBsq).trans z4sq_card.le
  have h2 : Nat.card (B.map φ) ≤ 2 := by
    have hsub : ((B.map φ : Subgroup (DihedralGroup 6)) : Set (DihedralGroup 6)) ⊆
        {1, DihedralGroup.r 3} := by
      rintro _ ⟨b, hb, rfl⟩
      refine d12_aux (φ b) ?_ ?_
      · rw [← map_mul, hBsq b hb, map_one]
      · intro g
        obtain ⟨k, rfl⟩ := hφ g
        have h3 := congrArg φ (hBcomm b hb (k * b * k⁻¹) (hBnorm k b hb))
        simpa only [map_mul, map_inv] using h3
    have e1 : Nat.card (B.map φ) =
        ((B.map φ : Subgroup (DihedralGroup 6)) : Set (DihedralGroup 6)).ncard :=
      (Nat.card_coe_set_eq ((B.map φ : Subgroup (DihedralGroup 6)) : Set (DihedralGroup 6))).symm
    rw [e1]
    refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
    refine (Set.ncard_insert_le _ _).trans ?_
    rw [Set.ncard_singleton]
  rw [← hBcard, h]
  calc _ ≤ 4 * 2 := Nat.mul_le_mul h1 h2
    _ = 8 := rfl

theorem ori2 {D : Type*} [Group D] [Finite D] {K A : Subgroup D} (hAK : A ≤ K) (hAel : IsElemAbelian 2 A)
    (hAn : K ≤ Subgroup.normalizer (A : Set D)) (φ : ↥K →* Equiv.Perm (Fin 3))
    (hφ : Function.Surjective φ)
    (hN : IsCentralProduct₂ ↥φ.ker (QuaternionGroup 2) (QuaternionGroup 2)) : Nat.card A ≤ 8 := by
  let B : Subgroup ↥K := A.subgroupOf K
  have hBcard : Nat.card B = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv
  have hBsq : ∀ b ∈ B, b * b = 1 := fun b hb => Subtype.ext (by
    have := hAel.2 (b : D) (Subgroup.mem_subgroupOf.1 hb)
    rw [Subgroup.coe_mul, ← pow_two]
    exact this)
  have hBcomm : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b := fun b hb b' hb' => Subtype.ext (by
    have h := congrArg Subtype.val (hAel.1.is_comm.comm ⟨(b : D), Subgroup.mem_subgroupOf.1 hb⟩
      ⟨(b' : D), Subgroup.mem_subgroupOf.1 hb'⟩)
    exact h)
  have hBnorm : ∀ k : ↥K, ∀ b ∈ B, k * b * k⁻¹ ∈ B := fun k b hb =>
    Subgroup.mem_subgroupOf.2 (by
      have := (Subgroup.mem_normalizer_iff.1 (hAn k.2) (b : D)).1 (Subgroup.mem_subgroupOf.1 hb)
      simpa using this)
  have h := card_eq_ker_mul φ B
  have h1 : Nat.card (B ⊓ φ.ker : Subgroup ↥K) ≤ 8 :=
    cp_bound hN (inf_le_right) (fun x hx => hBsq x hx.1)
  have h2 : Nat.card (B.map φ) ≤ 1 := by
    have hsub : ((B.map φ : Subgroup (Equiv.Perm (Fin 3))) : Set (Equiv.Perm (Fin 3))) ⊆ {1} := by
      rintro _ ⟨b, hb, rfl⟩
      refine s3_aux (φ b) ?_ ?_
      · rw [← map_mul, hBsq b hb, map_one]
      · intro g
        obtain ⟨k, rfl⟩ := hφ g
        have h3 := congrArg φ (hBcomm b hb (k * b * k⁻¹) (hBnorm k b hb))
        simpa only [map_mul, map_inv] using h3
    have e1 : Nat.card (B.map φ) =
        ((B.map φ : Subgroup (Equiv.Perm (Fin 3))) : Set (Equiv.Perm (Fin 3))).ncard :=
      (Nat.card_coe_set_eq ((B.map φ : Subgroup (Equiv.Perm (Fin 3))) : Set (Equiv.Perm (Fin 3)))).symm
    rw [e1]
    refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
    rw [Set.ncard_singleton]
  rw [← hBcard, h]
  calc _ ≤ 8 * 1 := Nat.mul_le_mul h1 h2
    _ = 8 := rfl

end CFSG.Quasithin.ModE
