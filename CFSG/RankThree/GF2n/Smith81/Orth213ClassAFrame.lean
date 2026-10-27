module

public import CFSG.RankThree.GF2n.Smith81.Orth213ClassTensor
public import CFSG.RankThree.GF2n.Smith81.Orth213ClassNormal

public section

namespace CFSG.RankThree.GF2n.Smith81.OrthClass

open QuadraticMap CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.ClassicalGroups.Orthogonal
open scoped Matrix

section LinAlg

variable {K ι : Type} [Field K] (qU : QuadraticForm K (ι → K))

@[expose] def Wz (d₀ d₁ : K) (uz : ι → K) : Set ((ι → K) × (ι → K)) :=
  {p | ∃ (w : ι → K) (s t : K), polar qU w uz = 0 ∧ p = (d₀ • w + s • uz, d₁ • w + t • uz)}

@[expose] def Bperp (c₀ c₁ : K) (ux : ι → K) (p : (ι → K) × (ι → K)) : Prop :=
  polar qU p.1 (c₁ • ux) + polar qU (c₀ • ux) p.2 = 0

theorem exists_smul_of_cross [CharP K 2] {c₀ c₁ d₀ d₁ : K} (hd : d₀ ≠ 0 ∨ d₁ ≠ 0)
    (h : c₀ * d₁ + c₁ * d₀ = 0) : ∃ l : K, c₀ = l * d₀ ∧ c₁ = l * d₁ := by
  have h' : c₁ * d₀ = c₀ * d₁ := by
    have := CharTwo.add_eq_zero.mp h
    exact this.symm
  by_cases hd0 : d₀ = 0
  · have hd1 : d₁ ≠ 0 := hd.resolve_left (fun h => h hd0)
    rw [hd0, mul_zero] at h'
    have hc0 : c₀ = 0 := by
      rcases mul_eq_zero.mp h'.symm with h | h
      · exact h
      · exact absurd h hd1
    exact ⟨c₁ / d₁, by rw [hc0, hd0, mul_zero], by field_simp⟩
  · exact ⟨c₀ / d₀, by field_simp, by field_simp; linear_combination h'⟩

theorem Bperp_Wz {c₀ c₁ d₀ d₁ s t : K} {uz ux w : ι → K} :
    Bperp qU c₀ c₁ ux (d₀ • w + s • uz, d₁ • w + t • uz) ↔
      (c₁ * d₀ + c₀ * d₁) * polar qU w ux + (c₁ * s + c₀ * t) * polar qU uz ux = 0 := by
  unfold Bperp
  simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq]
  rw [polar_comm qU ux w, polar_comm qU ux uz]
  constructor <;> intro h <;> linear_combination h

theorem Wz_Bperp_IV [CharP K 2] {c₀ c₁ d₀ d₁ : K} (hd : d₀ ≠ 0 ∨ d₁ ≠ 0) (hc : c₀ ≠ 0 ∨ c₁ ≠ 0)
    {uz ux : ι → K} (hκ : c₀ * d₁ + c₁ * d₀ = 0) (hf : polar qU uz ux ≠ 0) :
    {p | p ∈ Wz qU d₀ d₁ uz ∧ Bperp qU c₀ c₁ ux p} =
      {p | ∃ w, polar qU w uz = 0 ∧ p = (d₀ • w, d₁ • w)} := by
  obtain ⟨l, hl0, hl1⟩ := exists_smul_of_cross hd hκ
  have hl : l ≠ 0 := by
    rintro rfl
    rcases hc with h | h
    · exact h (by rw [hl0, zero_mul])
    · exact h (by rw [hl1, zero_mul])
  have h2 : c₁ * d₀ + c₀ * d₁ = 0 := by
    rw [hl0, hl1]
    linear_combination (l * d₀ * d₁) * (CharTwo.two_eq_zero : (2 : K) = 0)
  ext p
  constructor
  · rintro ⟨⟨w, s, t, hw, rfl⟩, hB⟩
    rw [Bperp_Wz, h2, zero_mul, zero_add] at hB
    have h3 : c₁ * s + c₀ * t = 0 := (mul_eq_zero.mp hB).resolve_right hf
    have h4 : s * d₁ + t * d₀ = 0 := by
      have : l * (s * d₁ + t * d₀) = 0 := by
        rw [hl0, hl1] at h3
        linear_combination h3
      exact (mul_eq_zero.mp this).resolve_left hl
    obtain ⟨μ, hμs, hμt⟩ := exists_smul_of_cross hd h4
    refine ⟨w + μ • uz, ?_, ?_⟩
    · rw [polar_add_left, polar_smul_left_eq, hw, polar_self_of_charTwo, mul_zero, add_zero]
    · rw [hμs, hμt]
      refine Prod.ext ?_ ?_ <;> dsimp only <;> module
  · rintro ⟨w, hw, rfl⟩
    refine ⟨⟨w, 0, 0, hw, by simp⟩, ?_⟩
    have := (Bperp_Wz qU (c₀ := c₀) (c₁ := c₁) (d₀ := d₀) (d₁ := d₁) (s := 0) (t := 0)
      (uz := uz) (ux := ux) (w := w)).mpr (by rw [h2]; ring)
    simpa using this

theorem Wz_Bperp_III [CharP K 2] {c₀ c₁ d₀ d₁ : K} (hd : d₀ ≠ 0 ∨ d₁ ≠ 0)
    (hκ : c₀ * d₁ + c₁ * d₀ ≠ 0) {uz ux : ι → K} (hzx : polar qU uz ux = 0) :
    ∃ H : Matrix (Fin 2) (Fin 2) K, H.det ≠ 0 ∧
      (fun p => orthTensor H id p) '' {p | p ∈ Wz qU d₀ d₁ uz ∧ Bperp qU c₀ c₁ ux p} =
        Ish qU uz ux 0 := by
  have hne : (![d₀, d₁] : Fin 2 → K) ≠ 0 := by
    intro h
    rcases hd with h0 | h1
    · exact h0 (by simpa using congrFun h 0)
    · exact h1 (by simpa using congrFun h 1)
  obtain ⟨h, hdet, hmul⟩ := exists_SL_mulVec_eq (![d₀, d₁]) hne
  set H : Matrix (Fin 2) (Fin 2) K := (h : Matrix (Fin 2) (Fin 2) K) with hH
  set Hi : Matrix (Fin 2) (Fin 2) K := ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
    with hHi
  have hHHi : H * Hi = 1 := by
    rw [hH, hHi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hHiH : Hi * H = 1 := by
    rw [hH, hHi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have e0 : H 0 0 * d₀ + H 0 1 * d₁ = 1 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hmul 0
  have e1 : H 1 0 * d₀ + H 1 1 * d₁ = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hmul 1
  have hHid : Hi *ᵥ ![1, 0] = ![d₀, d₁] := by
    rw [← hmul, Matrix.mulVec_mulVec, hHiH, Matrix.one_mulVec]
  have f0 : Hi 0 0 = d₀ := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hHid 0
  have f1 : Hi 1 0 = d₁ := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hHid 1
  refine ⟨H, by rw [hH, hdet]; exact one_ne_zero, ?_⟩
  ext ⟨a, b⟩
  constructor
  · rintro ⟨p, ⟨⟨w, s, t, hw, rfl⟩, hB⟩, hp⟩
    rw [Bperp_Wz, hzx, mul_zero, add_zero] at hB
    have hwx : polar qU w ux = 0 := by
      have hκ' : c₁ * d₀ + c₀ * d₁ ≠ 0 := by rw [add_comm]; exact hκ
      exact (mul_eq_zero.mp hB).resolve_left hκ'
    have k1 : H 0 0 • (d₀ • w + s • uz) + H 0 1 • (d₁ • w + t • uz) =
        w + (H 0 0 * s + H 0 1 * t) • uz := by
      have : H 0 0 • (d₀ • w + s • uz) + H 0 1 • (d₁ • w + t • uz) =
          (H 0 0 * d₀ + H 0 1 * d₁) • w + (H 0 0 * s + H 0 1 * t) • uz := by module
      rw [this, e0, one_smul]
    have k2 : H 1 0 • (d₀ • w + s • uz) + H 1 1 • (d₁ • w + t • uz) =
        (H 1 0 * s + H 1 1 * t) • uz := by
      have : H 1 0 • (d₀ • w + s • uz) + H 1 1 • (d₁ • w + t • uz) =
          (H 1 0 * d₀ + H 1 1 * d₁) • w + (H 1 0 * s + H 1 1 * t) • uz := by module
      rw [this, e1, zero_smul, zero_add]
    have hp' : (a, b) = (w + (H 0 0 * s + H 0 1 * t) • uz, (H 1 0 * s + H 1 1 * t) • uz) := by
      rw [← hp, ← k1, ← k2]
      rfl
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp'
    refine ⟨?_, H 1 0 * s + H 1 1 * t, rfl, ?_⟩
    · show polar qU (w + (H 0 0 * s + H 0 1 * t) • uz) uz = 0
      rw [polar_add_left, polar_smul_left_eq, hw, polar_self_of_charTwo, mul_zero, add_zero]
    · show polar qU (w + (H 0 0 * s + H 0 1 * t) • uz) ux = 0 * (H 1 0 * s + H 1 1 * t)
      rw [polar_add_left, polar_smul_left_eq, hwx, hzx]
      ring
  · rintro ⟨hau, t, hb, hax⟩
    have hb' : b = t • uz := hb
    subst hb'
    have hax' : polar qU a ux = 0 := by simpa using hax
    refine ⟨orthTensor Hi id (a, t • uz), ⟨⟨a, Hi 0 1 * t, Hi 1 1 * t, hau, ?_⟩, ?_⟩, ?_⟩
    · simp only [orthTensor, id_eq, f0, f1]
      refine Prod.ext ?_ ?_ <;> simp only [smul_smul]
    · have := (Bperp_Wz qU (c₀ := c₀) (c₁ := c₁) (d₀ := d₀) (d₁ := d₁) (s := Hi 0 1 * t)
        (t := Hi 1 1 * t) (uz := uz) (ux := ux) (w := a)).mpr (by rw [hax', hzx]; ring)
      simp only [orthTensor, id_eq, f0, f1, smul_smul]
      exact this
    · show orthTensor H id (orthTensor Hi id (a, t • uz)) = (a, t • uz)
      rw [orthTensor_id_comp, hHHi, orthTensor_one_id]

theorem tCount_AFrame [Finite K] [CharP K 2] [Fintype ι] [DecidableEq ι] {c₀ c₁ d₀ d₁ : K}
    (hd : d₀ ≠ 0 ∨ d₁ ≠ 0) (hc : c₀ ≠ 0 ∨ c₁ ≠ 0) {uz ux : ι → K} (huz : uz ≠ 0) (hqz : qU uz = 0)
    (hcomm : (c₀ * d₁ + c₁ * d₀) * polar qU ux uz = 0)
    (hnot : ((c₀ • ux, c₁ • ux) : (ι → K) × (ι → K)) ∉ Wz qU d₀ d₁ uz) :
    tCount qU {p | p ∈ Wz qU d₀ d₁ uz ∧ Bperp qU c₀ c₁ ux p} + 1 =
        nSing qU (fun s => polar qU s uz = 0) ∨
      (polar qU uz ux = 0 ∧ (∀ a b : K, a • uz + b • ux = 0 → a = 0 ∧ b = 0) ∧
        tCount qU {p | p ∈ Wz qU d₀ d₁ uz ∧ Bperp qU c₀ c₁ ux p} + 1 + Nat.card K =
          nSing qU (fun s => polar qU s uz = 0 ∧ polar qU s ux = 0) + Nat.card K ^ 2) := by
  by_cases hf : polar qU uz ux = 0
  · by_cases hκ : c₀ * d₁ + c₁ * d₀ = 0
    · exfalso
      apply hnot
      obtain ⟨l, hl0, hl1⟩ := exists_smul_of_cross hd hκ
      refine ⟨l • ux, 0, 0, ?_, ?_⟩
      · rw [polar_smul_left_eq, polar_comm, hf, mul_zero]
      · rw [hl0, hl1]
        refine Prod.ext ?_ ?_ <;> simp [smul_smul, mul_comm]
    · by_cases hmu : ∃ μ : K, ux = μ • uz
      · exfalso
        apply hnot
        obtain ⟨μ, rfl⟩ := hmu
        refine ⟨0, c₀ * μ, c₁ * μ, polar_zero_left _ _, ?_⟩
        refine Prod.ext ?_ ?_ <;> simp [smul_smul]
      · right
        have hind : ∀ a b : K, a • uz + b • ux = 0 → a = 0 ∧ b = 0 := by
          intro a b hab
          by_cases hb : b = 0
          · subst hb
            rw [zero_smul, add_zero] at hab
            exact ⟨(smul_eq_zero.mp hab).resolve_right huz, rfl⟩
          · exfalso
            apply hmu
            refine ⟨-(a / b), ?_⟩
            have h1 : b • ux = -(a • uz) := eq_neg_of_add_eq_zero_right hab
            calc ux = b⁻¹ • (b • ux) := (inv_smul_smul₀ hb _).symm
              _ = b⁻¹ • -(a • uz) := by rw [h1]
              _ = -(a / b) • uz := by rw [smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
        obtain ⟨H, hH, himg⟩ := Wz_Bperp_III qU hd hκ hf
        have h1 := tCount_image (qU := qU) H hH
          {p | p ∈ Wz qU d₀ d₁ uz ∧ Bperp qU c₀ c₁ ux p}
        rw [himg] at h1
        refine ⟨hf, hind, ?_⟩
        rw [← h1]
        exact tCount_Ish_zero huz hqz hf
  · left
    have hκ : c₀ * d₁ + c₁ * d₀ = 0 := by
      rcases mul_eq_zero.mp hcomm with h | h
      · exact h
      · exact absurd (by rw [polar_comm]; exact h) hf
    rw [Wz_Bperp_IV qU hd hc hκ hf]
    exact tCount_pureLine hd uz

end LinAlg

section Group

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem isConj_of_sit (hc : SmithOrthCfg M Q Z B) {X : Subgroup G} {x : G}
    (hs : Sit M Q Z X x) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) : IsConj z x := by
  obtain ⟨g₀, hg₀⟩ := hs.conj
  have hz₀ : g₀⁻¹ * x * g₀ ∈ Z := mem_conjSubgroup.mp (hg₀ ▸ hs.mem)
  have hz₀1 : g₀⁻¹ * x * g₀ ≠ 1 := by
    intro h
    apply hs.ne_one
    have : x = g₀ * (g₀⁻¹ * x * g₀) * g₀⁻¹ := by group
    rw [this, h]
    group
  obtain ⟨m, -, hm⟩ := Z_isConj hc.ctx.hyp hz hz1 hz₀ hz₀1
  refine isConj_iff.mpr ⟨g₀ * m, ?_⟩
  calc g₀ * m * z * (g₀ * m)⁻¹ = g₀ * (m * z * m⁻¹) * g₀⁻¹ := by group
    _ = g₀ * (g₀⁻¹ * x * g₀) * g₀⁻¹ := by rw [hm]
    _ = x := by group

theorem aframe_count (h52 : Smith52ActStatement) (hc : SmithOrthCfg M Q Z B)
    (C : OrthCtx M Q Z B) {X : Subgroup G} {x : G} (hs : Sit M Q Z X x) {g : G}
    (hAQ : conjSubgroup g Z ≤ Q) (hAX : conjSubgroup g Z ≤ QB X) :
    (∃ uz : C.ι → C.K, uz ≠ 0 ∧ C.qU uz = 0 ∧
      tCount C.qU (imgSet C ((Q ⊓ QB (conjSubgroup g Z)) ⊓
          Subgroup.centralizer ({x} : Set G))) + 1 =
        nSing C.qU (fun s => polar C.qU s uz = 0)) ∨
    (∃ uz ux : C.ι → C.K, uz ≠ 0 ∧ C.qU uz = 0 ∧ C.qU ux = 0 ∧ polar C.qU uz ux = 0 ∧
      (∀ a b : C.K, a • uz + b • ux = 0 → a = 0 ∧ b = 0) ∧
      tCount C.qU (imgSet C ((Q ⊓ QB (conjSubgroup g Z)) ⊓
          Subgroup.centralizer ({x} : Set G))) + 1 + Nat.card C.K =
        nSing C.qU (fun s => polar C.qU s uz = 0 ∧ polar C.qU s ux = 0) + Nat.card C.K ^ 2) := by
  have H := hc.ctx.hyp
  have h12 := smith_1_12 hs
  have hA : IsZConjugate Z (conjSubgroup g Z) := ⟨g, rfl⟩
  have hAZ : conjSubgroup g Z ≠ Z := (lin29_of_sit hs hA hAQ hAX).1
  have hX' : IsZConjugate Z X := hs.conj
  have hXA : X ≤ QB (conjSubgroup g Z) := (IsZConjugate.le_QB_iff H hA hX').mpr hAX
  have hZA : Z ≤ QB (conjSubgroup g Z) :=
    (IsZConjugate.le_QB_iff H hA (IsZConjugate.self Z)).mpr (by rw [H.QB_Z]; exact hAQ)
  have hQB : QB (conjSubgroup g Z) = conjSubgroup g Q := QB_conj_eq H g
  have hZQ : Z ≤ Q := H.Z_normal.1
  have hZ₁ : IsZConjugate Z (conjSubgroup g⁻¹ Z) := ⟨g⁻¹, rfl⟩
  have hQB₁ : QB (conjSubgroup g⁻¹ Z) = conjSubgroup g⁻¹ Q := QB_conj_eq H g⁻¹
  have hgg : conjSubgroup g (conjSubgroup g⁻¹ Z) = Z := by
    rw [← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]
  have hZ₁Z : conjSubgroup g⁻¹ Z ≠ Z := by
    intro h
    apply hAZ
    calc conjSubgroup g Z = conjSubgroup g (conjSubgroup g⁻¹ Z) := by rw [h]
      _ = Z := hgg
  have hZ₁Q : conjSubgroup g⁻¹ Z ≤ Q := by
    intro y hy
    have h1 : g * y * g⁻¹ ∈ Z := by simpa using mem_conjSubgroup.mp hy
    have h2 : g * y * g⁻¹ ∈ conjSubgroup g Q := hQB ▸ hZA h1
    have h3 := mem_conjSubgroup.mp h2
    have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rwa [e] at h3
  obtain ⟨z, hz, hz1⟩ : ∃ z ∈ Z, z ≠ 1 := by
    have hZne : Z ≠ ⊥ := by
      intro h
      have h4 := H.q4
      rw [h, Subgroup.card_bot] at h4
      omega
    obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
    exact ⟨z, z.2, fun h => hz1 (Subtype.ext h)⟩
  have hxz : x * z * x⁻¹ = z := hs.x_cent h12 z hz
  have hz₁Z₁ : g⁻¹ * z * g ∈ conjSubgroup g⁻¹ Z := by
    rw [mem_conjSubgroup]
    simpa [mul_assoc] using hz
  have hz₁Q : g⁻¹ * z * g ∈ Q := hZ₁Q hz₁Z₁
  have hz₁1 : g⁻¹ * z * g ≠ 1 := by
    intro h
    apply hz1
    have : z = g * (g⁻¹ * z * g) * g⁻¹ := by group
    rw [this, h]
    group
  have hz₁Z : g⁻¹ * z * g ∉ Z := by
    intro h
    have hm : g⁻¹ * z * g ∈ Z ⊓ conjSubgroup g⁻¹ Z := ⟨h, hz₁Z₁⟩
    rw [inf_conjSubgroup_eq_bot_of_isTI H.ti hZ₁Z, Subgroup.mem_bot] at hm
    exact hz₁1 hm
  have hz₁c : IsConj z (g⁻¹ * z * g) := isConj_iff.mpr ⟨g⁻¹, by group⟩
  have hx₁Q : g⁻¹ * x * g ∈ Q := by
    have hm : x ∈ conjSubgroup g Q := hQB ▸ hXA hs.mem
    exact mem_conjSubgroup.mp hm
  have hx₁Z : g⁻¹ * x * g ∉ Z := by
    intro hm
    exact hs.notQ (hAQ (mem_conjSubgroup.mpr hm))
  have hx₁c : IsConj z (g⁻¹ * x * g) :=
    (isConj_of_sit hc hs hz hz1).trans (isConj_iff.mpr ⟨g⁻¹, by group⟩)
  obtain ⟨c₀, c₁, ux, hc01, hux0, hqux, hφx⟩ := (C.hF.root z hz hz1 _ hx₁Q hx₁Z).mp hx₁c
  obtain ⟨d₀, d₁, uz, hd01, huz0, hquz, hφz⟩ := (C.hF.root z hz hz1 _ hz₁Q hz₁Z).mp hz₁c
  have hcomm : (c₀ * d₁ + c₁ * d₀) * polar C.qU ux uz = 0 := by
    have h1 : (g⁻¹ * x * g) * (g⁻¹ * z * g) = (g⁻¹ * z * g) * (g⁻¹ * x * g) := by
      have : x * z = z * x := by
        have := hxz
        rw [mul_inv_eq_iff_eq_mul] at this
        exact this
      calc (g⁻¹ * x * g) * (g⁻¹ * z * g) = g⁻¹ * (x * z) * g := by group
        _ = g⁻¹ * (z * x) * g := by rw [this]
        _ = (g⁻¹ * z * g) * (g⁻¹ * x * g) := by group
    have h2 := (Tim79.QuadModel.comm_iff_B C.M₀ C.hD.reg hx₁Q hz₁Q).mp h1
    rw [OrthCaseI.B_phi C, hφx, hφz] at h2
    simp only [polar_smul_left_eq, polar_smul_right_eq] at h2
    rw [polar_comm C.qU uz ux] at h2
    linear_combination h2
  obtain ⟨hforw, hconv⟩ := h52 G M Q Z B hc C.K C.γ C.M₀ C.hD C.ι C.qU C.φ C.hF C.hA
    (conjSubgroup g⁻¹ Z) hZ₁ hZ₁Q hZ₁Z d₀ d₁ uz hd01 huz0 hquz ⟨g⁻¹ * z * g, hz₁Z₁, hz₁1, hφz⟩
  have hnot : ((c₀ • ux, c₁ • ux) : (C.ι → C.K) × (C.ι → C.K)) ∉ Wz C.qU d₀ d₁ uz := by
    rintro ⟨w, s, t, hw, hmem⟩
    obtain ⟨v, hv, hφv⟩ := hconv w s t hw
    have hφeq : C.φ (C.M₀.π v) = C.φ (C.M₀.π (g⁻¹ * x * g)) := by
      rw [hφv, hφx, ← hmem]
    have hπ : C.M₀.π v = C.M₀.π (g⁻¹ * x * g) := C.φ.injective hφeq
    have hvz : v⁻¹ * (g⁻¹ * x * g) ∈ Z := (Tim79.QuadModel.pi_eq_iff C.M₀ hv.1 hx₁Q).mp hπ
    have hZ₁A : Z ≤ QB (conjSubgroup g⁻¹ Z) :=
      (IsZConjugate.le_QB_iff H hZ₁ (IsZConjugate.self Z)).mpr (by rw [H.QB_Z]; exact hZ₁Q)
    have hx₁B : g⁻¹ * x * g ∈ QB (conjSubgroup g⁻¹ Z) := by
      have : g⁻¹ * x * g = v * (v⁻¹ * (g⁻¹ * x * g)) := by group
      rw [this]
      exact (QB _).mul_mem hv.2 (hZ₁A hvz)
    rw [hQB₁, mem_conjSubgroup] at hx₁B
    apply hs.notQ
    have e : g⁻¹⁻¹ * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [e] at hx₁B
  set S : Subgroup G := (Q ⊓ QB (conjSubgroup g Z)) ⊓ Subgroup.centralizer ({x} : Set G)
    with hSdef
  set S₁ : Subgroup G := conjSubgroup g⁻¹ S with hS₁def
  have hS₁mem : ∀ y, y ∈ S₁ ↔ g * y * g⁻¹ ∈ S := fun y => by
    rw [hS₁def, mem_conjSubgroup, inv_inv]
  have hSQ : S ≤ Q := fun y hy => hy.1.1
  have hZS : Z ≤ S := fun y hy => ⟨⟨hZQ hy, hZA hy⟩, Subgroup.mem_centralizer_singleton_iff.mpr
    (by
      have := hs.x_cent h12 y hy
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm)⟩
  have hgQ : ∀ y, g * y * g⁻¹ ∈ conjSubgroup g Q ↔ y ∈ Q := fun y => by
    rw [mem_conjSubgroup]
    have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rw [e]
  have hgQ₁ : ∀ y, y ∈ conjSubgroup g⁻¹ Q ↔ g * y * g⁻¹ ∈ Q := fun y => by
    rw [mem_conjSubgroup, inv_inv]
  have hS₁Q : S₁ ≤ Q := fun y hy => by
    have h1 := ((hS₁mem y).mp hy).1.2
    rw [hQB] at h1
    exact (hgQ y).mp h1
  have hZS₁ : Z ≤ S₁ := fun y hy => by
    rw [hS₁mem]
    have hyA : g * y * g⁻¹ ∈ conjSubgroup g Z := by
      rw [mem_conjSubgroup]
      have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
      rw [e]
      exact hy
    refine ⟨⟨hAQ hyA, IsZConjugate.le_QB_self H hA hyA⟩, Subgroup.mem_centralizer_singleton_iff.mpr
      (hs.QB_comm_X hs.mem (hAX hyA)).symm⟩
  have himg : imgSet C S₁ = {p | p ∈ Wz C.qU d₀ d₁ uz ∧ Bperp C.qU c₀ c₁ ux p} := by
    ext p
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨⟨hyQ', hyQA'⟩, hycent'⟩ := (hS₁mem y).mp hy
      have hyQ : y ∈ Q := by
        rw [hQB] at hyQA'
        exact (hgQ y).mp hyQA'
      have hyB : y ∈ QB (conjSubgroup g⁻¹ Z) := by
        rw [hQB₁, hgQ₁]
        exact hyQ'
      have hcomm' : y * (g⁻¹ * x * g) = (g⁻¹ * x * g) * y := by
        have := Subgroup.mem_centralizer_singleton_iff.mp hycent'
        calc y * (g⁻¹ * x * g) = g⁻¹ * ((g * y * g⁻¹) * x) * g := by group
          _ = g⁻¹ * (x * (g * y * g⁻¹)) * g := by rw [this]
          _ = (g⁻¹ * x * g) * y := by group
      obtain ⟨w, s, t, hw, hφ⟩ := hforw y ⟨hyQ, hyB⟩
      refine ⟨⟨w, s, t, hw, hφ⟩, ?_⟩
      have hB := (Tim79.QuadModel.comm_iff_B C.M₀ C.hD.reg hyQ hx₁Q).mp hcomm'
      rw [OrthCaseI.B_phi C, hφx] at hB
      exact hB
    · rintro ⟨⟨w, s, t, hw, rfl⟩, hB⟩
      obtain ⟨v, hv, hφv⟩ := hconv w s t hw
      refine ⟨v, ?_, hφv⟩
      rw [hS₁mem]
      have hvB : v ∈ QB (conjSubgroup g⁻¹ Z) := hv.2
      rw [hQB₁, hgQ₁] at hvB
      have hcomm1 : v * (g⁻¹ * x * g) = (g⁻¹ * x * g) * v := by
        refine (Tim79.QuadModel.comm_iff_B C.M₀ C.hD.reg hv.1 hx₁Q).mpr ?_
        rw [OrthCaseI.B_phi C, hφv, hφx]
        exact hB
      refine ⟨⟨hvB, ?_⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      · rw [hQB]
        exact (hgQ v).mpr hv.1
      · calc (g * v * g⁻¹) * x = g * (v * (g⁻¹ * x * g)) * g⁻¹ := by group
          _ = g * ((g⁻¹ * x * g) * v) * g⁻¹ := by rw [hcomm1]
          _ = x * (g * v * g⁻¹) := by group
  have heq := tCount_eq_of_conj hc C hz hz1 hSQ hZS hS₁Q hZS₁ hS₁mem
  rw [heq, himg]
  rcases tCount_AFrame C.qU hd01 hc01 huz0 hquz hcomm hnot with h | ⟨hf, hind, h⟩
  · exact Or.inl ⟨uz, huz0, hquz, h⟩
  · exact Or.inr ⟨uz, ux, huz0, hquz, hqux, hf, hind, h⟩

end Group

end CFSG.RankThree.GF2n.Smith81.OrthClass
