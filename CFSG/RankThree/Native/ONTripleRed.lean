module

public import CFSG.RankThree.Native.ONTripleSig

public noncomputable section

namespace CFSG.RankThree.Native.ONTriple

open CFSG.ONSchreier CFSG.ONSchreier.Native Subgroup Equiv
open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Sporadic

attribute [local irreducible] dotProduct

theorem zG_mem_K0' : zG ∈ K0G := zG_mem_K0

theorem centralizer_base {α : ℕ} (hα : α % 3 ≠ 0) (c : ℕ) :
    centralizer {xG 0 ^ α * zG ^ c} = zpowers (xG 0 ^ α * zG ^ c) ⊔ K0G ∧
      zpowers (xG 0 ^ α * zG ^ c) ⊓ K0G = ⊥ := by
  have hcube : xG 0 ^ 3 = 1 := xG0_cube
  set a := xG 0 ^ α * zG ^ c with ha
  have hc : centralizer {a} = centralizer {xG 0} := by
    rw [ha, centralizer_mul_zpow, centralizer_pow_of_cube hcube hα]
  refine ⟨?_, ?_⟩
  · rw [hc, centralizer_x0_eq.1]
    apply le_antisymm
    · refine sup_le ?_ le_sup_right
      rw [zpowers_le]
      have hx : xG 0 = a ^ α * (zG ^ c)⁻¹ ^ α := by
        have hcom : Commute (xG 0 ^ α) (zG ^ c) :=
          ((Commute.pow_left (zG_central (xG 0)) c).pow_right α).symm
        have hs : α * α % 3 = 1 := by
          have : α % 3 = 1 ∨ α % 3 = 2 := by omega
          rcases this with h | h <;> simp [Nat.mul_mod, h]
        rw [ha, hcom.mul_pow, mul_assoc, inv_pow, mul_inv_cancel, mul_one, ← pow_mul,
          ← pow_mod_three hcube, hs, pow_one]
      rw [hx]
      exact mul_mem (pow_mem (mem_sup_left (mem_zpowers a)) α)
        (pow_mem (inv_mem (mem_sup_right (pow_mem zG_mem_K0' c))) α)
    · refine sup_le ?_ le_sup_right
      rw [zpowers_le]
      exact mul_mem (mem_sup_left (pow_mem (mem_zpowers _) α))
        (mem_sup_right (pow_mem zG_mem_K0' c))
  · rw [eq_bot_iff]
    intro g hg
    rw [mem_bot]
    obtain ⟨hg1, hg2⟩ := mem_inf.1 hg
    obtain ⟨k, rfl⟩ := (mem_powers_iff_mem_zpowers).2 hg1
    beta_reduce at hg2 ⊢
    have hcom : Commute (xG 0 ^ α) (zG ^ c) :=
      ((Commute.pow_left (zG_central (xG 0)) c).pow_right α).symm
    have e : a ^ k = xG 0 ^ (α * k) * zG ^ (c * k) := by
      rw [ha, hcom.mul_pow, ← pow_mul, ← pow_mul]
    rw [e] at hg2 ⊢
    have h1 : xG 0 ^ (α * k) ∈ K0G := by
      have := mul_mem hg2 (inv_mem (pow_mem zG_mem_K0' (c * k)))
      rwa [mul_inv_cancel_right] at this
    have h3 := three_dvd_of_pow_x0 (pow_x0_mem_K0 h1)
    have h3k : 3 ∣ k := by
      rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h | h
      · omega
      · exact h
    obtain ⟨q, rfl⟩ := h3k
    rw [show α * (3 * q) = 3 * (α * q) by ring, show c * (3 * q) = 3 * (c * q) by ring,
      pow_mul (xG 0) 3, pow_mul zG 3, hcube, relG.xcube, one_pow, one_pow, one_mul]

theorem map_conj_K0 (n : GM) : CFSG.RankThree.PartTwo.Sec4.IsExtOf
    (K0G.map (MulAut.conj n).toMonoidHom) (alternatingGroup (Fin 6)) (Multiplicative (ZMod 3)) :=
  CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.isExtOf_of_mulEquiv
    (K0G.equivMapOfInjective _ (MulAut.conj n).injective).symm isExtOf_K0

theorem centralizer_conj (n : GM) {α : ℕ} (hα : α % 3 ≠ 0) (c : ℕ) :
    centralizer {n * (xG 0 ^ α * zG ^ c) * n⁻¹} =
        zpowers (n * (xG 0 ^ α * zG ^ c) * n⁻¹) ⊔ K0G.map (MulAut.conj n).toMonoidHom ∧
      zpowers (n * (xG 0 ^ α * zG ^ c) * n⁻¹) ⊓ K0G.map (MulAut.conj n).toMonoidHom = ⊥ := by
  obtain ⟨h1, h2⟩ := centralizer_base hα c
  have hz : zpowers (n * (xG 0 ^ α * zG ^ c) * n⁻¹) =
      (zpowers (xG 0 ^ α * zG ^ c)).map (MulAut.conj n).toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    rfl
  refine ⟨?_, ?_⟩
  · rw [← map_conj_centralizer, h1, Subgroup.map_sup, hz]
  · rw [hz, ← map_inf_eq _ _ _ (MulAut.conj n).injective, h2, Subgroup.map_bot]

theorem comm_of_E27 {A : Subgroup GM} (hA : Late.IsE27 A) : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a :=
  fun a ha b hb => congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem isPGroup_of_E27 {A : Subgroup GM} (hA : Late.IsE27 A) : IsPGroup 3 A :=
  IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num)

theorem card_le_27 {B : Subgroup GM} (hB : B ≤ P0G) (hab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) :
    Nat.card B ≤ 27 := by
  have h := relG.card_le_of_abelian (B.subgroupOf P0G)
    (fun a ha b hb => Subtype.ext (hab _ ha _ hb))
  rwa [Nat.card_congr (subgroupOfEquivOfLe hB).toEquiv] at h

theorem zG_mem_of_27 {B : Subgroup GM} (hB : B ≤ P0G) (hab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (h27 : Nat.card B = 27) : zG ∈ B := by
  have h := relG.center_le_of_abelian (B.subgroupOf P0G)
    (fun a ha b hb => Subtype.ext (hab _ ha _ hb))
    (by rw [Nat.card_congr (subgroupOfEquivOfLe hB).toEquiv, h27])
  have hz : (⟨zG, ThreeQRel.x_mem⟩ : P0G) ∈ center P0G := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (zG_central g).symm
  exact h hz

theorem map_conj_comm {A : Subgroup GM} (hab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (g : GM) :
    ∀ a ∈ A.map (MulAut.conj g).toMonoidHom, ∀ b ∈ A.map (MulAut.conj g).toMonoidHom,
      a * b = b * a := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul, hab a ha b hb]

theorem card_map_conj (A : Subgroup GM) (g : GM) :
    Nat.card (A.map (MulAut.conj g).toMonoidHom) = Nat.card A :=
  card_map_of_injective (MulAut.conj g).injective

theorem map_conj_map_conj (A : Subgroup GM) (g h : GM) :
    (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      A.map (MulAut.conj (h * g)).toMonoidHom := by
  rw [map_map]
  congr 1
  refine MonoidHom.ext fun x => ?_
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem exists_word_conj_x0 {g : GM} (hg : g ∈ P0G) (hgz : g ∉ zpowers zG) :
    ∃ w : List ℕ, (∀ k ∈ w, k < 2) ∧ ∃ c : ℕ, (wordN w)⁻¹ * g * wordN w = xG 0 * zG ^ c := by
  set v := relG.coord ⟨g, hg⟩ with hv
  have hv0 : v ≠ 0 := fun h0 => hgz ((relG.coord_eq_zero_iff _).1 h0)
  refine ⟨vw v, vw_lt v, ?_⟩
  have hc := coord_conjW (vw v) (vw_lt v) hg
  rw [← hv, vecWord_spec v hv0] at hc
  exact eq_mul_zpow_of_coord (conjW_mem _ (vw_lt v) hg) (ThreeQRel.v_mem 0)
    (by rw [hc, coord_xG0])

@[expose] def inE0 (v : Fin 4 → ZMod 3) : Prop := v 1 = 0 ∧ v 2 = 0 ∧ v 3 = 0

instance : DecidablePred inE0 := fun v => by unfold inE0; infer_instance

@[expose] def B0 : Subgroup GM where
  carrier := {g | ∃ h : g ∈ P0G, inE0 (relG.coord ⟨g, h⟩)}
  one_mem' := ⟨one_mem _, by
    have : relG.coord ⟨1, one_mem _⟩ = 0 := (relG.coord_eq_zero_iff _).2 (one_mem _)
    rw [this]
    exact ⟨rfl, rfl, rfl⟩⟩
  mul_mem' := by
    rintro a b ⟨ha, hla⟩ ⟨hb, hlb⟩
    refine ⟨mul_mem ha hb, ?_⟩
    rw [coord_mul' ha hb]
    exact ⟨by simp [hla.1, hlb.1], by simp [hla.2.1, hlb.2.1], by simp [hla.2.2, hlb.2.2]⟩
  inv_mem' := by
    rintro a ⟨ha, hla⟩
    refine ⟨inv_mem ha, ?_⟩
    have e : relG.coord ⟨a⁻¹, inv_mem ha⟩ = - relG.coord ⟨a, ha⟩ := by
      have h0 : relG.coord ⟨a⁻¹ * a, mul_mem (inv_mem ha) ha⟩ = 0 :=
        (relG.coord_eq_zero_iff _).2 (by
          show a⁻¹ * a ∈ zpowers zG
          rw [inv_mul_cancel]
          exact one_mem _)
      rw [coord_mul' (inv_mem ha) ha] at h0
      exact eq_neg_of_add_eq_zero_left h0
    rw [e]
    refine ⟨?_, ?_, ?_⟩ <;> simp only [Pi.neg_apply]
    · rw [hla.1]; decide
    · rw [hla.2.1]; decide
    · rw [hla.2.2]; decide

theorem B0_lt_AG0 : B0 < AG 0 := by
  refine lt_of_le_of_ne (fun g hg => ?_) fun h => ?_
  · obtain ⟨h, hl⟩ := hg
    exact mem_AG.2 ⟨h, ⟨hl.2.2, hl.2.1⟩⟩
  · have hx : xG 1 ∈ AG 0 := by
      rw [← yG_zero]
      exact yG_mem_AG (by norm_num)
    rw [← h] at hx
    obtain ⟨h1, hl⟩ := hx
    have : relG.coord ⟨xG 1, h1⟩ 1 = 0 := hl.1
    rw [coord_xG] at this
    exact absurd this (by decide)

theorem card_B0_lt : Nat.card B0 < 27 := by
  have h1 := Subgroup.card_lt_of_lt B0_lt_AG0
  have h2 := card_le_27 (AG_le_P0 0) (fun a ha b hb => AG_comm (by norm_num) ha hb)
  omega

@[expose] def jOf (v : Fin 4 → ZMod 3) : ℕ := if v 2 = 0 ∨ v 1 = 0 then 0 else 1

@[expose] def wOf (v : Fin 4 → ZMod 3) : List ℕ := if v 2 = 0 ∨ v 1 = v 2 then [] else [0]

theorem jOf_lt (v : Fin 4 → ZMod 3) : jOf v < 2 := by
  unfold jOf
  split_ifs <;> norm_num

theorem wOf_lt (v : Fin 4 → ZMod 3) : ∀ k ∈ wOf v, k < 2 := by
  unfold wOf
  split_ifs <;> simp

theorem plane_select : ∀ v : Fin 4 → ZMod 3, v 3 = 0 → ¬ inE0 v → ∀ u : Fin 4 → ZMod 3,
    u 3 = 0 → ThreeQRel.threePair omegaZ v u = 0 → inL (jOf v) (vecWord (wOf v) u) := by
  decide +kernel

theorem threePair_e0 :
    ∀ u : Fin 4 → ZMod 3, ThreeQRel.threePair omegaZ (Pi.single 0 1) u = u 3 := by
  decide +kernel

theorem exists_conj_AG {A : Subgroup GM} (hA : Late.IsE27 A) :
    ∃ h : GM, ∃ j < 2, A.map (MulAut.conj h).toMonoidHom = AG j := by
  have hab := comm_of_E27 hA
  obtain ⟨P, hAP⟩ := (isPGroup_of_E27 hA).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq GM P P0Syl
  set A1 := A.map (MulAut.conj g).toMonoidHom with hA1
  have hA1P : A1 ≤ P0G := by
    rw [← P0Syl_coe, ← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact map_mono hAP
  have hab1 := map_conj_comm hab g
  have h27 : Nat.card A1 = 27 := by rw [card_map_conj, hA.2]
  obtain ⟨a1, ha1, ha1z⟩ : ∃ a1 ∈ A1, a1 ∉ zpowers zG := by
    by_contra hne
    push Not at hne
    have hle : A1 ≤ zpowers zG := hne
    have := Subgroup.card_le_of_le hle
    rw [h27, Nat.card_zpowers, relG.orderOf_x] at this
    omega
  obtain ⟨w, hw, c, hwc⟩ := exists_word_conj_x0 (hA1P ha1) ha1z
  set A2 := A1.map (MulAut.conj (wordN w)⁻¹).toMonoidHom with hA2
  have hA2P : A2 ≤ P0G := by
    rintro _ ⟨x, hx, rfl⟩
    have := conjW_mem w hw (hA1P hx)
    simpa [MulAut.conj_apply] using this
  have hab2 := map_conj_comm hab1 (wordN w)⁻¹
  have h272 : Nat.card A2 = 27 := by rw [card_map_conj, h27]
  have hz2 : zG ∈ A2 := zG_mem_of_27 hA2P hab2 h272
  have hx2 : xG 0 ∈ A2 := by
    have h1 : xG 0 * zG ^ c ∈ A2 := by
      rw [← hwc]
      exact ⟨a1, ha1, by simp⟩
    have := mul_mem h1 (inv_mem (pow_mem hz2 c))
    rwa [mul_inv_cancel_right] at this
  obtain ⟨y, hy, hyB⟩ : ∃ y ∈ A2, y ∉ B0 := by
    by_contra hne
    push Not at hne
    have := Subgroup.card_le_of_le (show A2 ≤ B0 from hne)
    have := card_B0_lt
    omega
  set v := relG.coord ⟨y, hA2P hy⟩ with hv
  have hv3 : v 3 = 0 := by
    have hc := (relG.commute_iff ⟨xG 0, ThreeQRel.v_mem 0⟩ ⟨y, hA2P hy⟩).1
      (Subtype.ext (hab2 _ hx2 _ hy))
    rw [coord_xG0, threePair_e0] at hc
    exact hc
  have hvE : ¬ inE0 v := fun h => hyB ⟨hA2P hy, h⟩
  set j := jOf v
  set A3 := A2.map (MulAut.conj (wordN (wOf v))⁻¹).toMonoidHom with hA3
  have hA3le : A3 ≤ AG j := by
    rintro _ ⟨u, hu, rfl⟩
    have hmem := conjW_mem (wOf v) (wOf_lt v) (hA2P hu)
    have hcoord := coord_conjW (wOf v) (wOf_lt v) (hA2P hu)
    have hu3 : relG.coord ⟨u, hA2P hu⟩ 3 = 0 := by
      have hc := (relG.commute_iff ⟨xG 0, ThreeQRel.v_mem 0⟩ ⟨u, hA2P hu⟩).1
        (Subtype.ext (hab2 _ hx2 _ hu))
      rw [coord_xG0, threePair_e0] at hc
      exact hc
    have hyu : ThreeQRel.threePair omegaZ v (relG.coord ⟨u, hA2P hu⟩) = 0 :=
      (relG.commute_iff ⟨y, hA2P hy⟩ ⟨u, hA2P hu⟩).1 (Subtype.ext (hab2 _ hy _ hu))
    have hin := plane_select v hv3 hvE _ hu3 hyu
    rw [← hcoord] at hin
    have e : (MulAut.conj (wordN (wOf v))⁻¹).toMonoidHom u =
        (wordN (wOf v))⁻¹ * u * wordN (wOf v) := by simp
    rw [e]
    exact mem_AG.2 ⟨hmem, hin⟩
  have hA3eq : A3 = AG j := by
    apply eq_of_le_of_card_ge hA3le
    rw [card_map_conj, h272]
    exact card_le_27 (AG_le_P0 j) (fun a ha b hb => AG_comm (jOf_lt v) ha hb)
  refine ⟨(wordN (wOf v))⁻¹ * ((wordN w)⁻¹ * g), j, jOf_lt v, ?_⟩
  rw [← map_conj_map_conj, ← map_conj_map_conj]
  exact hA3eq

theorem part_two_M {A : Subgroup GM} (hA : Late.IsE27 A) {a : GM} (ha : a ∈ A)
    (haz : a ∉ zpowers zG) :
    ∃ K : Subgroup GM, IsExtOf K (alternatingGroup (Fin 6)) (Multiplicative (ZMod 3)) ∧
      centralizer {a} = zpowers a ⊔ K ∧ zpowers a ⊓ K = ⊥ := by
  obtain ⟨P, hAP⟩ := (isPGroup_of_E27 hA).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq GM P P0Syl
  have hP : (MulAut.conj g).toMonoidHom a ∈ P0G := by
    rw [← P0Syl_coe, ← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact mem_map_of_mem _ (hAP ha)
  have hz : (MulAut.conj g).toMonoidHom a ∉ zpowers zG := by
    intro h
    apply haz
    have h' := (MulAut.conj g⁻¹).toMonoidHom.map_zpowers zG ▸ mem_map_of_mem
      (MulAut.conj g⁻¹).toMonoidHom h
    have e1 : (MulAut.conj g⁻¹).toMonoidHom ((MulAut.conj g).toMonoidHom a) = a := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    have e2 : (MulAut.conj g⁻¹).toMonoidHom zG = zG := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [mul_assoc, zG_central, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [e1, e2] at h'
    exact h'
  obtain ⟨w, hw, c, hwc⟩ := exists_word_conj_x0 hP hz
  set n := g⁻¹ * wordN w
  have han : a = n * (xG 0 ^ 1 * zG ^ c) * n⁻¹ := by
    rw [pow_one, ← hwc]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, n]
    group
  obtain ⟨h1, h2⟩ := centralizer_conj n (α := 1) (by norm_num) c
  rw [← han] at h1 h2
  exact ⟨_, map_conj_K0 n, h1, h2⟩

theorem conj_zG (g : GM) : (MulAut.conj g).toMonoidHom zG = zG := by
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [mul_assoc, zG_central, ← mul_assoc, mul_inv_cancel, one_mul]

theorem conj_not_mem_zpowers {a : GM} (haz : a ∉ zpowers zG) (g : GM) :
    (MulAut.conj g).toMonoidHom a ∉ zpowers zG := by
  intro h
  apply haz
  have h' := mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom h
  rw [MonoidHom.map_zpowers, conj_zG] at h'
  have e1 : (MulAut.conj g⁻¹).toMonoidHom ((MulAut.conj g).toMonoidHom a) = a := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  rwa [e1] at h'

theorem isKleinFour_of_card_sq {H : Subgroup GM} (h4 : Nat.card H = 4)
    (h2 : ∀ g ∈ H, g ^ 2 = 1) : IsKleinFour H := by
  refine ⟨h4, ?_⟩
  have : Nontrivial H := by
    rw [← Finite.one_lt_card_iff_nontrivial, h4]
    norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
  intro g hg
  exact orderOf_eq_prime (Subtype.ext (h2 g g.2)) hg

theorem smul_uL_eq_zero {j l s : ℕ} (hs : s % 3 = 0) : s • uL j l = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod 3),
    (ZMod.natCast_eq_zero_iff s 3).2 (Nat.dvd_of_mod_eq_zero hs), zero_smul]

theorem map_conj_one (A : Subgroup GM) : A.map (MulAut.conj (1 : GM)).toMonoidHom = A := by
  ext x
  simp

theorem part_three_M {A : Subgroup GM} (hA : Late.IsE27 A) {a : GM} (ha : a ∈ A)
    (haz : a ∉ zpowers zG) {S : Subgroup GM}
    (hS : S ∈ maxInvariantPiSubgroups ⊤ A (piOf 2)) :
    IsKleinFour S ∧ ∃ K : Subgroup GM,
      IsExtOf K (alternatingGroup (Fin 6)) (Multiplicative (ZMod 3)) ∧
        centralizer {a} = zpowers a ⊔ K ∧ zpowers a ⊓ K = ⊥ ∧
        (a ∈ centralizer (S : Set GM) → S ≤ K) := by
  obtain ⟨h, j, hj, hAh⟩ := exists_conj_AG hA
  set φ := MulAut.conj h with hφ
  have hS' : S.map φ.toMonoidHom ∈ maxInvariantPiSubgroups ⊤ (AG j) (piOf 2) := by
    have himg := image_maxInvariantPiSubgroups φ ⊤ A (piOf 2)
    rw [map_top_of_surjective _ φ.surjective, hAh] at himg
    rw [← himg]
    exact ⟨S, hS, rfl⟩
  obtain ⟨l, hl, m, hm, hSX⟩ := maxInv_AG hj hS'
  have hSback : S = (XG j l m hj hm).map (MulAut.conj h⁻¹).toMonoidHom := by
    rw [← hSX, map_conj_map_conj, inv_mul_cancel, map_conj_one]
  refine ⟨?_, ?_⟩
  · apply isKleinFour_of_card_sq
    · rw [hSback, card_map_conj, card_XG hj hm]
    · intro g hg
      rw [hSback] at hg
      obtain ⟨x, hx, rfl⟩ := hg
      rw [← map_pow, XG_sq hx, map_one]
  · by_cases hc : a ∈ centralizer (S : Set GM)
    · have ha' : φ.toMonoidHom a ∈ AG j := hAh ▸ mem_map_of_mem _ ha
      have hc' : φ.toMonoidHom a ∈ centralizer (XG j l m hj hm : Set GM) := by
        rw [← hSX, mem_centralizer_iff]
        rintro _ ⟨s, hs, rfl⟩
        have := (mem_centralizer_iff.1 hc) s hs
        rw [← map_mul, ← map_mul, this]
      obtain ⟨s, hs⟩ := coord_of_centralizes_XG hj hl hm ha' hc'
      have hs3 : s % 3 ≠ 0 := by
        intro h0
        rw [smul_uL_eq_zero h0] at hs
        exact conj_not_mem_zpowers haz h ((relG.coord_eq_zero_iff _).1 hs)
      have hmL := coord_pow' (mL_mem_P0 hj hl) s
      rw [coord_mL hj hl] at hmL
      obtain ⟨c, hcz⟩ := eq_mul_zpow_of_coord (AG_le_P0 j ha') (pow_mem (mL_mem_P0 hj hl) s)
        (by rw [hs, hmL])
      set n := h⁻¹ * (nL j l)⁻¹ with hn
      have han : a = n * (xG 0 ^ s * zG ^ c) * n⁻¹ := by
        have e1 : a = h⁻¹ * φ.toMonoidHom a * h := by
          simp only [hφ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
        have e2 : mL j l ^ s = (nL j l)⁻¹ * xG 0 ^ s * nL j l := by
          rw [mL]
          have := conj_pow (a := (nL j l)⁻¹) (b := xG 0) (i := s)
          rwa [inv_inv] at this
        rw [e1, hcz, e2, hn]
        have hzc : Commute (zG ^ c) (nL j l) := Commute.pow_left (zG_central _) c
        calc h⁻¹ * ((nL j l)⁻¹ * xG 0 ^ s * nL j l * zG ^ c) * h
            = h⁻¹ * ((nL j l)⁻¹ * xG 0 ^ s * (nL j l * zG ^ c)) * h := by group
          _ = h⁻¹ * ((nL j l)⁻¹ * xG 0 ^ s * (zG ^ c * nL j l)) * h := by rw [hzc.eq]
          _ = h⁻¹ * (nL j l)⁻¹ * (xG 0 ^ s * zG ^ c) * (h⁻¹ * (nL j l)⁻¹)⁻¹ := by group
      obtain ⟨h1, h2⟩ := centralizer_conj n hs3 c
      rw [← han] at h1 h2
      refine ⟨_, map_conj_K0 n, h1, h2, fun _ => ?_⟩
      rw [hSback, hn, ← map_conj_map_conj]
      exact map_mono (XG_le_K hj hm)
    · obtain ⟨K, hK1, hK2, hK3⟩ := part_two_M hA ha haz
      exact ⟨K, hK1, hK2, hK3, fun h' => absurd h' hc⟩

instance : IsSimpleGroup Pv :=
  @MulEquiv.isSimpleGroup Pv _ Blueprint.NativeSporadic.ON _ CFSG.Sporadic.ON.isSimpleGroup_ON
    onEquivPv.symm

theorem phiM_n1_x0 : phiM (nG 0) * phiM (xG 0) ≠ phiM (xG 0) * phiM (nG 0) := by
  intro h
  have hw : wordN [0] = nG 0 := by simp [wordN]
  have hw2 : ∀ k ∈ [0], k < 2 := by simp
  set g := (wordN [0])⁻¹ * xG 0 * wordN [0] with hg
  have hgP : g ∈ P0G := conjW_mem [0] hw2 (ThreeQRel.v_mem 0)
  have hk : g * (xG 0)⁻¹ ∈ zpowers zG := by
    rw [← ker_phiM, MonoidHom.mem_ker, hg, hw, map_mul, map_mul, map_mul, map_inv, map_inv,
      mul_assoc ((phiM (nG 0))⁻¹) (phiM (xG 0)) (phiM (nG 0)), ← h]
    group
  obtain ⟨c, hc⟩ := (mem_powers_iff_mem_zpowers).2 hk
  have hc' : zG ^ c = g * (xG 0)⁻¹ := hc
  have e : g = zG ^ c * xG 0 := by rw [hc', inv_mul_cancel_right]
  have h1 : relG.coord ⟨g, hgP⟩ = relG.coord ⟨xG 0, ThreeQRel.v_mem 0⟩ := by
    have ex : (⟨g, hgP⟩ : P0G) = ⟨zG ^ c * xG 0, mul_mem (pow_mem ThreeQRel.x_mem c)
        (ThreeQRel.v_mem 0)⟩ := Subtype.ext e
    rw [ex, coord_mul' (pow_mem ThreeQRel.x_mem c) (ThreeQRel.v_mem 0),
      (relG.coord_eq_zero_iff _).2 (pow_mem (mem_zpowers zG) c), zero_add]
  have h2 := coord_conjW [0] hw2 (ThreeQRel.v_mem 0)
  have h3 := h1.symm.trans h2
  rw [coord_xG0] at h3
  exact absurd h3 (by decide +kernel)

theorem center_GM : center GM = zpowers zG := by
  apply le_antisymm
  · have hN : ((center GM).map phiM).Normal :=
      Subgroup.Normal.map inferInstance phiM phiM_surjective
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((center GM).map phiM) with h | h
    · intro g hg
      rw [← ker_phiM, MonoidHom.mem_ker]
      have : phiM g ∈ (center GM).map phiM := mem_map_of_mem _ hg
      rw [h] at this
      exact this
    · exfalso
      apply phiM_n1_x0
      have : phiM (nG 0) ∈ (center GM).map phiM := by rw [h]; trivial
      obtain ⟨c, hc, hce⟩ := this
      rw [← hce, ← map_mul, ← map_mul, mem_center_iff.1 hc (xG 0)]
  · rw [zpowers_le, mem_center_iff]
    intro g
    exact (zG_central g).symm

theorem zG_mem_E27 {A : Subgroup GM} (hA : Late.IsE27 A) : zG ∈ A := by
  obtain ⟨h, j, -, hAh⟩ := exists_conj_AG hA
  have hz : zG ∈ A.map (MulAut.conj h).toMonoidHom := hAh ▸ zG_mem_AG j
  obtain ⟨x, hx, hxz⟩ := hz
  have : x = zG := by
    apply (MulAut.conj h).injective
    rw [← MulEquiv.coe_toMonoidHom, hxz, conj_zG]
  rwa [this] at hx

@[expose] def AutFixZInner : Prop :=
  ∀ β : GM ≃* GM, β zG = zG → ∃ g : GM, ∀ x, β x = g * x * g⁻¹

end CFSG.RankThree.Native.ONTriple
