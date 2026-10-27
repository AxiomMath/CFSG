module

public import CFSG.Quasithin.Background.HTriSp4

public section

namespace CFSG.Quasithin

namespace H

namespace Tri

open Matrix CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

section Group

variable {G : Type*} [Group G]

theorem isSolvable_sup_of_permute [Finite G] {B U : Subgroup G}
    (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hBodd : Odd (Nat.card B)) (hU : IsPGroup 2 U)
    (hBU : (B : Set G) * U = U * B) : Group.IsSolvable ↥(B ⊔ U) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := B ⊔ U with hQ
  have hBQ : B ≤ Q := le_sup_left
  have hUQ : U ≤ Q := le_sup_right
  obtain ⟨k, hk⟩ := hU.exists_card_eq
  have hcop : Nat.Coprime (Nat.card B) (Nat.card U) := by
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hBodd)
  set B' := B.subgroupOf Q with hB'
  set U' := U.subgroupOf Q with hU'
  have hB'card : Nat.card B' = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBQ).toEquiv
  have hU'card : Nat.card U' = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUQ).toEquiv
  have hU'p : IsPGroup 2 U' := hU.of_equiv (Subgroup.subgroupOfEquivOfLe hUQ).symm
  have hB'comm : IsMulCommutative ↥B' :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext (hBab _ a.2 _ b.2))⟩⟩
  refine CFSG.GroupTheory.WielandtProduct.wielandt_coprime_product B' U'
    (CommGroup.isNilpotent) hU'p.isNilpotent (by rw [hB'card, hU'card]; exact hcop) ?_
  intro g
  have hg : (g : G) ∈ ((B ⊔ U : Subgroup G) : Set G) := g.2
  rw [coe_sup_eq_mul hBU] at hg
  obtain ⟨b, hb, u, hu, hbu⟩ := hg
  exact ⟨⟨b, hBQ hb⟩, hb, ⟨u, hUQ hu⟩, hu, Subtype.ext hbu.symm⟩

theorem pCore_ne_bot_of_solvable [Finite G] {R U E : Subgroup G} (hR : Group.IsSolvable ↥R)
    (hUR : U ≤ R) (hU : IsPGroup 2 U) (hU1 : U ≠ ⊥) (hEU : E ≤ U)
    (hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE2 : ∀ e ∈ E, e * e = 1)
    (hE4 : 4 ≤ Nat.card E)
    (hC : ∀ e ∈ E, e ≠ 1 → ∀ x : G, e * x = x * e → x ∈ Subgroup.normalizer (U : Set G)) :
    CFSG.pCore 2 ↥R ≠ ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hP
  set F := CFSG.fittingSubgroup ↥R with hF
  have hFodd : ¬ 2 ∣ Nat.card F := by
    intro h2
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 ↥F))
    have hle := Sylow.map_le_pCore (CFSG.fittingSubgroup_normal) (CFSG.fittingSubgroup_nilpotent)
      2 P
    rw [hP, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ F.subtype_injective] at hle
    have h1 : Nat.card ↥(P : Subgroup ↥F) = 1 := by rw [hle, Subgroup.card_bot]
    rw [Sylow.card_eq_multiplicity] at h1
    have h0 : (Nat.card ↥F).factorization 2 = 0 := by
      by_contra hne
      have : 2 ≤ 2 ^ (Nat.card ↥F).factorization 2 := Nat.le_self_pow hne 2
      omega
    have h3 := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two Nat.card_pos.ne').mp h2
    omega
  set F' := F.map R.subtype with hF'
  have hF'R : F' ≤ R := Subgroup.map_subtype_le _
  have hF'card : Nat.card F' = Nat.card F := Subgroup.card_map_of_injective R.subtype_injective
  have hF'odd : Odd (Nat.card F') := by
    rw [hF'card, ← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact hFodd
  have hRN : R ≤ Subgroup.normalizer (F' : Set G) := by
    have hFsub : F'.subgroupOf R = F :=
      Subgroup.comap_map_eq_self_of_injective R.subtype_injective _
    have hnorm : (F'.subgroupOf R).Normal := by
      rw [hFsub]
      exact CFSG.fittingSubgroup_normal
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hF'R).mp hnorm
  have hFU : F' ≤ Subgroup.normalizer (U : Set G) :=
    le_of_commute ((hEU.trans hUR).trans hRN) hEab hE2 hE4 hF'odd
      fun e he he1 b _ heb => hC e he he1 b heb
  obtain ⟨k, hk⟩ := hU.exists_card_eq
  have hcop : Nat.Coprime (Nat.card F') (Nat.card U) := by
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hF'odd)
  have hinf : F' ⊓ U = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hcomm : ∀ f ∈ F', ∀ u ∈ U, f * u = u * f := by
    intro f hf u hu
    have h1 : f * u * f⁻¹ * u⁻¹ ∈ U := by
      have := (Subgroup.mem_normalizer_iff.mp (hFU hf) u).mp hu
      exact U.mul_mem this (U.inv_mem hu)
    have h2 : f * u * f⁻¹ * u⁻¹ ∈ F' := by
      have := (Subgroup.mem_normalizer_iff.mp (hRN (hUR hu)) f⁻¹).mp (F'.inv_mem hf)
      have e : f * u * f⁻¹ * u⁻¹ = f * (u * f⁻¹ * u⁻¹) := by group
      rw [e]
      exact F'.mul_mem hf this
    have h3 : f * u * f⁻¹ * u⁻¹ = 1 := by
      have : f * u * f⁻¹ * u⁻¹ ∈ F' ⊓ U := ⟨h2, h1⟩
      rw [hinf] at this
      exact this
    calc f * u = f * u * f⁻¹ * u⁻¹ * (u * f) := by group
      _ = u * f := by rw [h3, one_mul]
  have hUF : U.subgroupOf R ≤ F := by
    refine le_trans ?_ (CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hR)
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact Subtype.ext (hcomm _ ⟨f, hf, rfl⟩ _ hu)
  apply hU1
  rw [eq_bot_iff]
  intro u hu
  have h1 : u ∈ F' := ⟨⟨u, hUR hu⟩, hUF hu, rfl⟩
  have : u ∈ F' ⊓ U := ⟨h1, hu⟩
  rwa [hinf] at this

end Group

variable {K : Type*} [Field K]

theorem conj_mem_uniGL {n : ℕ} {b u : GL (Fin n) K} (hb : b ∈ borGL n K)
    (hu : u ∈ uniGL n K) : b * u * b⁻¹ ∈ uniGL n K := by
  obtain ⟨-, hd⟩ := uniGL_entries hu
  have hbu : b * u ∈ borGL n K := (borGL n K).mul_mem hb (uniGL_le_borGL n hu)
  have hbi : b⁻¹ ∈ borGL n K := (borGL n K).inv_mem hb
  have hbub : b * u * b⁻¹ ∈ borGL n K := (borGL n K).mul_mem hbu hbi
  refine mem_uniGL_of (mem_borGL.mp hbub) fun i => ?_
  have h1 : ((b * u * b⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i i =
      ((b * b⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i i := by
    rw [Units.val_mul, LinearFlag.mul_apply_self_of_isUpperTriangular hbu hbi, Units.val_mul,
      LinearFlag.mul_apply_self_of_isUpperTriangular hb (uniGL_le_borGL n hu), hd i, mul_one,
      Units.val_mul, LinearFlag.mul_apply_self_of_isUpperTriangular hb hbi]
  rw [h1, mul_inv_cancel, Units.val_one, one_apply_eq]

theorem borGL_le_normalizer_uniGL (n : ℕ) :
    borGL n K ≤ Subgroup.normalizer (uniGL n K : Set (GL (Fin n) K)) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · exact conj_mem_uniGL hb
  · intro h
    have h1 := conj_mem_uniGL ((borGL n K).inv_mem hb) h
    have e : b⁻¹ * (b * u * b⁻¹) * b⁻¹⁻¹ = u := by group
    rwa [e] at h1

theorem uni2_eq_uniGL : uni2 K = uniGL 2 K := by
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    refine mem_uniGL_of (fun i j hij => ?_) (fun i => ?_)
    · fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) |
        simp [trHom_apply, coe_trGL, transvection]
    · fin_cases i <;> simp [trHom_apply, coe_trGL, transvection]
  · intro g hg
    obtain ⟨hl, hd⟩ := uniGL_entries hg
    refine mem_rootGL.mpr ⟨(g : Matrix (Fin 2) (Fin 2) K) 0 1, Units.ext ?_⟩
    rw [coe_trGL]
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [transvection] using hd 0
    · simp [transvection]
    · simpa [transvection] using hl 1 0 (by decide)
    · simpa [transvection] using hd 1

theorem isPGroup_uni2 [Finite K] [CharP K 2] : IsPGroup 2 (uni2 K) := fun g =>
  ⟨1, by rw [pow_one, pow_two]; exact Subtype.ext (rootGL_mul_self _ g.2)⟩

theorem le_uniGL_of_isPGroup [Finite K] [CharP K 2] {n : ℕ} (hn : 1 ≤ n)
    {P : Subgroup (GL (Fin n) K)} (hP : IsPGroup 2 P) (hUP : uniGL n K ≤ P) :
    P ≤ uniGL n K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdet : ∀ x ∈ P, (x : Matrix (Fin n) (Fin n) K).det = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
    have hxk : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h1 : ((x : Matrix (Fin n) (Fin n) K).det) ^ 2 ^ k = 1 := by
      rw [← Matrix.det_pow, ← Units.val_pow_eq_pow_val, hxk, Units.val_one, Matrix.det_one]
    have h : ((x : Matrix (Fin n) (Fin n) K).det - 1) ^ 2 ^ k = 0 := by
      rw [sub_pow_char_pow, one_pow, h1, sub_self]
    exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero k two_ne_zero)).mp h)
  obtain ⟨S, hS⟩ := LinearFlag.exists_sylow_unitriangular (K := K) 2 hn
  set P' := P.comap Matrix.SpecialLinearGroup.toGL with hP'
  have hP'p : IsPGroup 2 P' := hP.comap_of_injective _ Matrix.SpecialLinearGroup.toGL_injective
  have hle : (S : Subgroup (Matrix.SpecialLinearGroup (Fin n) K)) ≤ P' := by
    rw [hS]
    intro u hu
    exact hUP ⟨u, hu, rfl⟩
  have heq := S.is_maximal' hP'p hle
  intro x hx
  let u : Matrix.SpecialLinearGroup (Fin n) K := ⟨x, hdet x hx⟩
  have hu : u ∈ P' := by
    change Matrix.SpecialLinearGroup.toGL u ∈ P
    have e : Matrix.SpecialLinearGroup.toGL u = x := Units.ext rfl
    rw [e]
    exact hx
  rw [heq, hS] at hu
  exact ⟨u, hu, Units.ext rfl⟩

theorem le_normalizer_pCore_map {G : Type*} [Group G] (R : Subgroup G) :
    R ≤ Subgroup.normalizer (((CFSG.pCore 2 ↥R).map R.subtype : Subgroup G) : Set G) := by
  have hOR : (CFSG.pCore 2 ↥R).map R.subtype ≤ R := Subgroup.map_subtype_le _
  have hOsub : ((CFSG.pCore 2 ↥R).map R.subtype).subgroupOf R = CFSG.pCore 2 ↥R :=
    Subgroup.comap_map_eq_self_of_injective R.subtype_injective _
  have hnorm : (((CFSG.pCore 2 ↥R).map R.subtype).subgroupOf R).Normal := by
    rw [hOsub]
    infer_instance
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hOR).mp hnorm

theorem le_borGL_two_of_solvable [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {R : Subgroup (GL (Fin 2) K)} (hR : Group.IsSolvable ↥R) (hUR : uni2 K ≤ R) :
    R ≤ borGL 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU1 : uni2 K ≠ ⊥ := by
    intro h
    have h1 : Nat.card (uni2 K) = Nat.card K := card_rootGL (K := K) (0 : Fin 2) 1 (by decide)
    rw [h, Subgroup.card_bot] at h1
    omega
  have hC : ∀ e ∈ uni2 K, e ≠ 1 → ∀ x : GL (Fin 2) K,
      e * x = x * e → x ∈ Subgroup.normalizer (uni2 K : Set (GL (Fin 2) K)) := by
    intro e he he1 x hx
    obtain ⟨c, rfl⟩ := mem_rootGL.mp he
    have hc0 := ne_zero_of_trGL_ne_one he1
    have h1 := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) hx
    simp only [Units.val_mul, coe_trGL] at h1
    have hx10 := (entry_eq_zero_of_commute hc0 h1).1 1 (by decide)
    rw [uni2_eq_uniGL]
    exact borGL_le_normalizer_uniGL 2 (mem_borGL_two.mpr hx10)
  have hP := pCore_ne_bot_of_solvable hR hUR isPGroup_uni2 hU1 le_rfl rootGL_comm
    rootGL_mul_self (by rw [card_rootGL]; exact hK) hC
  set O := (CFSG.pCore 2 ↥R).map R.subtype with hO
  have hO1 : O ≠ ⊥ := by
    rw [hO, Ne, Subgroup.map_eq_bot_iff_of_injective _ R.subtype_injective]
    exact hP
  have hOp : IsPGroup 2 O := (CFSG.pCore_isPGroup (p := 2) (G := ↥R)).map R.subtype
  have hRN := le_normalizer_pCore_map R
  have hOU : O ≤ uni2 K := by
    rw [uni2_eq_uniGL]
    have hUp' : IsPGroup 2 (uniGL 2 K) := uni2_eq_uniGL (K := K) ▸ isPGroup_uni2
    have hUN' : uniGL 2 K ≤ Subgroup.normalizer (O : Set (GL (Fin 2) K)) :=
      uni2_eq_uniGL (K := K) ▸ (hUR.trans hRN)
    have hsup := hOp.to_sup_of_normal_left' hUp' hUN'
    exact le_sup_left.trans (le_uniGL_of_isPGroup (by norm_num) hsup le_sup_right)
  obtain ⟨o, ho1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hO1
  obtain ⟨c, hc⟩ := mem_rootGL.mp (hOU o.2)
  have hc0 : c ≠ 0 := ne_zero_of_trGL_ne_one (by
    rw [← hc]
    exact fun h => ho1 (Subtype.ext h))
  intro b hb
  have h1 : b * o * b⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp (hRN hb) o).mp o.2
  obtain ⟨d, hd⟩ := mem_rootGL.mp (hOU h1)
  have h2 : (b : Matrix (Fin 2) (Fin 2) K) * transvection 0 1 c =
      transvection 0 1 d * (b : Matrix (Fin 2) (Fin 2) K) := by
    have h3 : b * (o : GL (Fin 2) K) = trGL 0 1 (by decide) d * b := by
      rw [← hd]
      group
    have h4 := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) h3
    simp only [Units.val_mul, hc, coe_trGL] at h4
    exact h4
  have h5 := congrFun (congrFun h2 1) 1
  rw [mul_transvection_apply_same, transvection_mul_apply_of_ne 0 1 1 1 (by decide)] at h5
  have h6 : c * (b : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := add_eq_left.mp h5
  rw [mem_borGL_two]
  exact (mul_eq_zero.mp h6).resolve_left hc0

theorem le_borGL_three_of_solvable [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {R : Subgroup (GL (Fin 3) K)} (hR : Group.IsSolvable ↥R) (hUR : uni3 K ≤ R) :
    R ≤ borGL 3 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU1 : uni3 K ≠ ⊥ := by
    intro h
    have h1 := card_uni3 (K := K)
    have h2 : Nat.card (uni3 K) = 1 := by rw [h, Subgroup.card_bot]
    have h3 : 4 ^ 3 ≤ Nat.card K ^ 3 := Nat.pow_le_pow_left hK 3
    omega
  have hC : ∀ e ∈ rootGL (K := K) (0 : Fin 3) 2 (by decide), e ≠ 1 → ∀ x : GL (Fin 3) K,
      e * x = x * e → x ∈ Subgroup.normalizer (uni3 K : Set (GL (Fin 3) K)) := by
    intro e he he1 x hx
    obtain ⟨c, rfl⟩ := mem_rootGL.mp he
    have hc0 := ne_zero_of_trGL_ne_one he1
    have h1 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hx
    simp only [Units.val_mul, coe_trGL] at h1
    obtain ⟨hr, hs⟩ := entry_eq_zero_of_commute hc0 h1
    exact borGL_le_normalizer_uniGL 3
      (mem_borGL_three.mpr ⟨hr 1 (by decide), hr 2 (by decide), hs 1 (by decide)⟩)
  have hP := pCore_ne_bot_of_solvable hR hUR isPGroup_uni3 hU1 rootGL_le_uni3 rootGL_comm
    rootGL_mul_self (by rw [card_rootGL]; exact hK) hC
  set O := (CFSG.pCore 2 ↥R).map R.subtype with hO
  have hO1 : O ≠ ⊥ := by
    rw [hO, Ne, Subgroup.map_eq_bot_iff_of_injective _ R.subtype_injective]
    exact hP
  have hOp : IsPGroup 2 O := (CFSG.pCore_isPGroup (p := 2) (G := ↥R)).map R.subtype
  have hRN := le_normalizer_pCore_map R
  have hOU : O ≤ uni3 K := by
    have hsup := hOp.to_sup_of_normal_left' isPGroup_uni3 (hUR.trans hRN)
    exact le_sup_left.trans (le_uniGL_of_isPGroup (n := 3) (by norm_num) hsup le_sup_right)
  have hsolv : ∀ ψ : ↥R →* GL (Fin 2) K, Group.IsSolvable ↥ψ.range := fun ψ => by
    have := hR
    exact Group.isSolvable_of_surjective ψ.rangeRestrict_surjective
  rcases stab_of_normal hUR hO1 hOU hRN with h1 | h2
  · intro g hg
    obtain ⟨hg10, hg20⟩ := h1 g hg
    have hU2 : uni2 K ≤ (lowerHom h1).range := by
      rw [← map_lowerHom_uni3 h1 hUR]
      exact Subgroup.map_le_range _ _
    have hle := le_borGL_two_of_solvable hK (hsolv _) hU2
    have hg' : lowerHom h1 ⟨g, hg⟩ ∈ borGL 2 K := hle ⟨⟨g, hg⟩, rfl⟩
    rw [mem_borGL_two] at hg'
    exact mem_borGL_three.mpr ⟨hg10, hg20, hg'⟩
  · intro g hg
    obtain ⟨hg20, hg21⟩ := h2 g hg
    have hU2 : uni2 K ≤ (upperHom h2).range := by
      rw [← map_upperHom_uni3 h2 hUR]
      exact Subgroup.map_le_range _ _
    have hle := le_borGL_two_of_solvable hK (hsolv _) hU2
    have hg' : upperHom h2 ⟨g, hg⟩ ∈ borGL 2 K := hle ⟨⟨g, hg⟩, rfl⟩
    rw [mem_borGL_two] at hg'
    exact mem_borGL_three.mpr ⟨hg', hg20, hg21⟩

end Tri

end H

end CFSG.Quasithin
