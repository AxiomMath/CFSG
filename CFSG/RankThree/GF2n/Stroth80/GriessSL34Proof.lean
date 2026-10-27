module

public import CFSG.RankThree.GF2n.Stroth80.GriessSL34Section
public import CFSG.RankThree.GF2n.Stroth80.GriessSL34

public section

namespace CFSG.RankThree.GF2n.Stroth80

open scoped MatrixGroups commutatorElement
open Matrix Module CFSG.RankThree.FFModules CFSG.Open CFSG.Open.StatedAPI

section Group

variable {E H : Type*} [Group E] [Group H]

theorem commutatorElement_mul_central {a b z w : E} (hz : ∀ g, g * z = z * g)
    (hw : ∀ g, g * w = w * g) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  simp only [commutatorElement_def, _root_.mul_inv_rev]
  calc a * z * (b * w) * (z⁻¹ * a⁻¹) * (w⁻¹ * b⁻¹)
      = a * ((z * (b * w)) * z⁻¹) * a⁻¹ * (w⁻¹ * b⁻¹) := by group
    _ = a * (b * w) * a⁻¹ * (w⁻¹ * b⁻¹) := by rw [← hz (b * w), mul_inv_cancel_right]
    _ = a * b * (w * a⁻¹) * (w⁻¹ * b⁻¹) := by group
    _ = a * b * (a⁻¹ * w) * (w⁻¹ * b⁻¹) := by rw [← hw a⁻¹]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem ker_eq_bot_of_section (hperf : commutator E = ⊤) (ρ : E →* H)
    (hcent : ρ.ker ≤ Subgroup.center E) (φ : H →* E) (hφ : ∀ g, ρ (φ g) = g) : ρ.ker = ⊥ := by
  have hdec : ∀ a : E, φ (ρ a) * ((φ (ρ a))⁻¹ * a) = a := fun a => by group
  have hkerz : ∀ a : E, (φ (ρ a))⁻¹ * a ∈ ρ.ker := fun a => by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hφ, inv_mul_cancel]
  have hcentral : ∀ a g : E, g * ((φ (ρ a))⁻¹ * a) = ((φ (ρ a))⁻¹ * a) * g := fun a g =>
    Subgroup.mem_center_iff.1 (hcent (hkerz a)) g
  have hrange : φ.range = ⊤ := by
    rw [eq_top_iff, ← hperf, commutator_def]
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    have e := commutatorElement_mul_central (a := φ (ρ a)) (b := φ (ρ b)) (hcentral a)
      (hcentral b)
    rw [hdec a, hdec b] at e
    rw [e, ← map_commutatorElement]
    exact ⟨_, rfl⟩
  refine eq_bot_iff.2 fun y hy => ?_
  obtain ⟨s, rfl⟩ : y ∈ φ.range := hrange ▸ Subgroup.mem_top y
  have hs : s = 1 := by
    rw [← hφ s]
    exact hy
  rw [hs, map_one]
  exact Subgroup.one_mem _

theorem card_le_card_map_of_inf_ker [Finite H] {ρ : E →* H} {A : Subgroup E}
    (hA : A ⊓ ρ.ker = ⊥) : Nat.card A ≤ Nat.card (A.map ρ) :=
  Nat.card_le_card_of_injective (fun a => ⟨ρ a, Subgroup.mem_map_of_mem ρ a.2⟩) fun a b hab =>
    Subtype.ext (eq_of_map_eq_of_inf_ker hA a.2 b.2 (congrArg Subtype.val hab))

theorem conj_mem_normalizer_of_iff {L L' : Subgroup E} {g n : E}
    (hL : ∀ y, y ∈ L' ↔ g * y * g⁻¹ ∈ L) (hn : n ∈ Subgroup.normalizer (L : Set E)) :
    g⁻¹ * n * g ∈ Subgroup.normalizer (L' : Set E) := by
  refine Subgroup.mem_normalizer_iff.2 fun y => ?_
  rw [hL, hL, Subgroup.mem_normalizer_iff.1 hn (g * y * g⁻¹)]
  constructor <;> intro h <;> convert h using 1 <;> group

theorem mem_map_conj_iff {A : Subgroup E} {g x : E} :
    x ∈ A.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    have e : g⁻¹ * (MulAut.conj g).toMonoidHom a * g = a := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact ha
  · intro hx
    refine ⟨g⁻¹ * x * g, hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

end Group

section Field

variable {K : Type} [Field K]

theorem charP_two_of_card_four [Fintype K] (hK : Nat.card K = 4) : CharP K 2 := by
  obtain ⟨p, hchar, n, hp, hcard⟩ := FiniteField.card' K
  rw [← Nat.card_eq_fintype_card, hK] at hcard
  have h4 : p ∣ 2 ^ 2 := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, hcard]
    exact dvd_pow_self p (PNat.ne_zero n)
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h4)
  exact hp2 ▸ hchar

theorem exists_eq_span_singleton_of_finrank_eq_one {S : Submodule K (Fin 3 → K)}
    (hS : finrank K S = 1) : ∃ v : Fin 3 → K, v ≠ 0 ∧ S = K ∙ v := by
  obtain ⟨v, hv, hall⟩ := finrank_eq_one_iff'.1 hS
  refine ⟨v, fun h => hv (Subtype.ext h), le_antisymm (fun x hx => ?_) ?_⟩
  · obtain ⟨c, hc⟩ := hall ⟨x, hx⟩
    rw [Submodule.mem_span_singleton]
    exact ⟨c, congrArg Subtype.val hc⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact v.2

theorem dualHom_dualHom (g : SL(3, K)) : dualHom (dualHom g) = g := by
  apply Subtype.ext
  rw [coe_dualHom, dualMat, ← map_inv, coe_dualHom, dualMat, inv_inv, Matrix.transpose_transpose]

noncomputable def toSL3 {E : Type*} [Group E] (π : E →* GL (Fin 3) K)
    (h : ∀ e, π e ∈ StatedSL 3 K) : E →* SL(3, K) where
  toFun e := ⟨(π e : Matrix (Fin 3) (Fin 3) K), det_of_mem_statedSL (h e)⟩
  map_one' := Subtype.ext (show ((π 1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 by
    rw [map_one, Units.val_one])
  map_mul' a b := Subtype.ext (show ((π (a * b) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (π a : Matrix (Fin 3) (Fin 3) K) * (π b : Matrix (Fin 3) (Fin 3) K) by
    rw [map_mul, Units.val_mul])

theorem toSL3_ker {E : Type*} [Group E] (π : E →* GL (Fin 3) K)
    (h : ∀ e, π e ∈ StatedSL 3 K) : (toSL3 π h).ker = π.ker := by
  ext e
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  constructor
  · intro he
    exact Units.ext (congrArg (fun g : SL(3, K) => (g : Matrix (Fin 3) (Fin 3) K)) he)
  · intro he
    exact Subtype.ext (by change (π e : Matrix (Fin 3) (Fin 3) K) = 1; rw [he]; rfl)

theorem toSL3_surjective {E : Type*} [Group E] (π : E →* GL (Fin 3) K)
    (h : ∀ e, π e ∈ StatedSL 3 K) (hr : π.range = StatedSL 3 K) :
    Function.Surjective (toSL3 π h) := by
  intro g
  have hg : Matrix.SpecialLinearGroup.toGL g ∈ π.range := by
    rw [hr, statedSL_eq_range_toGL]
    exact ⟨g, rfl⟩
  obtain ⟨e, he⟩ := hg
  refine ⟨e, Subtype.ext ?_⟩
  change (π e : Matrix (Fin 3) (Fin 3) K) = g
  rw [he]
  rfl

variable [Finite K]

theorem ker_eq_bot_of_line_lift {E : Type} [Group E] (hperf : commutator E = ⊤)
    (ρ : E →* SL(3, K)) (hρ : Function.Surjective ρ) (hcent : ρ.ker ≤ Subgroup.center E)
    (A : Subgroup E) (hAY : A ⊓ ρ.ker = ⊥) {v : Fin 3 → K} (hv : v ≠ 0)
    (hAS : A.map ρ = transvectionGroup (K ∙ v))
    (hAn : ∀ e ∈ Subgroup.normalizer ((A ⊔ ρ.ker : Subgroup E) : Set E),
      e ∈ Subgroup.normalizer (A : Set E)) : ρ.ker = ⊥ := by
  have hN : ∀ e, ρ e ∈ Subgroup.normalizer (transvectionGroup (K ∙ v) : Set SL(3, K)) →
      e ∈ Subgroup.normalizer (A : Set E) := fun e he =>
    hAn e (by rw [← Subgroup.comap_map_eq, hAS]; exact Subgroup.le_normalizer_comap ρ he)
  choose g hg using fun r : Fin 3 => exists_map_span_eq_single hv r
  choose ĝ hĝ using fun r => hρ (g r)
  have hT : ∀ r y, y ∈ transvectionGroup (K ∙ v) ↔
      g r * y * (g r)⁻¹ ∈ transvectionGroup (K ∙ (Pi.single r 1 : Fin 3 → K)) := fun r y => by
    rw [mem_transvectionGroup_iff_conj (K ∙ v) (g r) y, hg r]
  have hinj : ∀ r, A.map (MulAut.conj (ĝ r)).toMonoidHom ⊓ ρ.ker = ⊥ := fun r => by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨hxA, hxk⟩ := Subgroup.mem_inf.1 hx
    have ha := mem_map_conj_iff.1 hxA
    have hak : (ĝ r)⁻¹ * x * ĝ r ∈ ρ.ker := by
      rw [MonoidHom.mem_ker] at hxk ⊢
      rw [map_mul, map_mul, hxk, mul_one, map_inv, inv_mul_cancel]
    have h1 : (ĝ r)⁻¹ * x * ĝ r = 1 := by
      have := Subgroup.mem_inf.2 ⟨ha, hak⟩
      rwa [hAY, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    calc x = ĝ r * ((ĝ r)⁻¹ * x * ĝ r) * (ĝ r)⁻¹ := by group
      _ = 1 := by rw [h1, mul_one, mul_inv_cancel]
  have hsurj : ∀ r, transvectionGroup (K ∙ (Pi.single r 1 : Fin 3 → K)) ≤
      (A.map (MulAut.conj (ĝ r)).toMonoidHom).map ρ := fun r x hx => by
    have hy : (g r)⁻¹ * x * g r ∈ transvectionGroup (K ∙ v) := by
      rw [hT r]
      convert hx using 1
      group
    rw [← hAS] at hy
    obtain ⟨a, ha, hay⟩ := hy
    have e : (ĝ r)⁻¹ * (ĝ r * a * (ĝ r)⁻¹) * ĝ r = a := by group
    refine ⟨ĝ r * a * (ĝ r)⁻¹, mem_map_conj_iff.2 (by rw [e]; exact ha), ?_⟩
    rw [map_mul, map_mul, map_inv, hĝ, hay]
    group
  have hnorm : ∀ r (e : E), ρ e ∈ Subgroup.normalizer
      (transvectionGroup (K ∙ (Pi.single r 1 : Fin 3 → K)) : Set SL(3, K)) →
      e ∈ Subgroup.normalizer (A.map (MulAut.conj (ĝ r)).toMonoidHom : Set E) := fun r e he => by
    have hρe : (g r)⁻¹ * ρ e * g r ∈
        Subgroup.normalizer (transvectionGroup (K ∙ v) : Set SL(3, K)) :=
      conj_mem_normalizer_of_iff (hT r) he
    have he' : (ĝ r)⁻¹ * e * ĝ r ∈ Subgroup.normalizer (A : Set E) := by
      refine hN _ ?_
      rwa [map_mul, map_mul, map_inv, hĝ]
    have := conj_mem_normalizer_of_iff (L := A)
      (L' := A.map (MulAut.conj (ĝ r)).toMonoidHom) (g := (ĝ r)⁻¹)
      (fun y => by rw [mem_map_conj_iff, inv_inv]) he'
    convert this using 1
    group
  obtain ⟨φ, hφ⟩ := exists_section_of_rowLifts ρ
    (fun r => A.map (MulAut.conj (ĝ r)).toMonoidHom) hinj hsurj hnorm
  exact ker_eq_bot_of_section hperf ρ hcent φ hφ

theorem ker_eq_bot_of_rootLift [Fintype K] [CharP K 2] (hK : Nat.card K = 4) {E : Type}
    [Group E] (hperf : commutator E = ⊤) (ρ : E →* SL(3, K)) (hρ : Function.Surjective ρ)
    (hcent : ρ.ker ≤ Subgroup.center E) (A : Subgroup E) (hAY : A ⊓ ρ.ker = ⊥)
    (hAel : IsElemAbelian 2 A)
    (hAn : ∀ e ∈ Subgroup.normalizer ((A ⊔ ρ.ker : Subgroup E) : Set E),
      e ∈ Subgroup.normalizer (A : Set E))
    (h16 : 16 ≤ Nat.card A) : ρ.ker = ⊥ := by
  classical
  have hq : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have hB2 : ∀ b ∈ A.map ρ, b * b = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← pow_two, hAel.2 a ha, map_one]
  have hBc : ∀ b ∈ A.map ρ, ∀ c ∈ A.map ρ, b * c = c * b := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg ρ (congrArg Subtype.val (hAel.1.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩))
  have hcardB : Nat.card (A.map ρ) = Fintype.card K ^ 2 := by
    refine le_antisymm (card_le_sq_of_elementary hB2 hBc) ?_
    rw [hq]
    exact le_trans (by norm_num) (h16.trans (card_le_card_map_of_inf_ker hAY))
  obtain ⟨S, hS, hBS⟩ := eq_transvectionGroup_of_card hB2 hBc hcardB
  rcases hS with hS1 | hS2
  · obtain ⟨v, hv, rfl⟩ := exists_eq_span_singleton_of_finrank_eq_one hS1
    exact ker_eq_bot_of_line_lift hperf ρ hρ hcent A hAY hv hBS hAn
  · have hker : (dualHom.comp ρ).ker = ρ.ker := by
      ext e
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply]
      exact ⟨fun h => dualHom_injective (h.trans (map_one _).symm), fun h => by rw [h, map_one]⟩
    have hsurj : Function.Surjective (dualHom.comp ρ) := fun g => by
      obtain ⟨e, he⟩ := hρ (dualHom g)
      exact ⟨e, by rw [MonoidHom.coe_comp, Function.comp_apply, he, dualHom_dualHom]⟩
    have hS1 : finrank K (dotOrth S) = 1 := by
      have := finrank_dotOrth S
      omega
    have hBS' : A.map (dualHom.comp ρ) = transvectionGroup (dotOrth S) := by
      have hle : A.map (dualHom.comp ρ) ≤ transvectionGroup (dotOrth S) := by
        rintro _ ⟨a, ha, rfl⟩
        refine dualHom_mem ?_
        rw [← hBS]
        exact Subgroup.mem_map_of_mem ρ ha
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [← Subgroup.map_map, Subgroup.card_map_of_injective dualHom_injective, hcardB]
      exact card_transvectionGroup_le (Or.inl hS1)
    obtain ⟨v, hv, hv'⟩ := exists_eq_span_singleton_of_finrank_eq_one hS1
    rw [← hker]
    rw [← hker] at hcent hAY hAn
    exact ker_eq_bot_of_line_lift hperf _ hsurj hcent A hAY hv (hv' ▸ hBS') hAn

theorem griessSL34Statement_holds : GriessSL34Statement := by
  intro K _ _ hK E _ _ Y hYc hperf π hrange hker
  classical
  by_cases hY : Y = ⊥
  · exact Or.inl hY
  refine Or.inr fun A hAY hAel hAn => ?_
  by_contra h16
  replace h16 := not_lt.1 h16
  apply hY
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_two_of_card_four hK
  have hπSL : ∀ e, π e ∈ StatedSL 3 K := fun e => hrange ▸ ⟨e, rfl⟩
  have hker' : (toSL3 π hπSL).ker = Y := (toSL3_ker π hπSL).trans hker
  rw [← hker'] at hYc hAY hAn ⊢
  exact ker_eq_bot_of_rootLift hK hperf _ (toSL3_surjective π hπSL hrange) hYc A hAY hAel hAn
    h16

end Field

end CFSG.RankThree.GF2n.Stroth80
