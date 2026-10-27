module

public import CFSG.LocalAnalysis.WeakClosure81.SevenNineDefs
import CFSG.LocalAnalysis.WeakClosure81.SevenNineOrthThree
import CFSG.LocalAnalysis.WeakClosure81.SevenNineOrthTransport
import CFSG.GroupTheory.CardMapInfKer

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent

section Map

variable {X X' : Type} [Group X] [Group X']

private theorem le_of_map_le (φ : X →* X') {Y A A' : Subgroup X} (hY : Y ⊓ φ.ker = ⊥)
    (hA : A ≤ Y) (hA' : A' ≤ Y) (h : A.map φ ≤ A'.map φ) : A ≤ A' := by
  intro a ha
  obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp (h (Subgroup.mem_map_of_mem φ ha))
  have hmem : b⁻¹ * a ∈ Y ⊓ φ.ker :=
    Subgroup.mem_inf.mpr ⟨Y.mul_mem (Y.inv_mem (hA' hb)) (hA ha), by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hba, inv_mul_cancel]⟩
  rw [hY, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  exact hmem ▸ hb

private theorem commutator_le_of_le_normalizer {Y S : Subgroup X}
    (h : S ≤ Subgroup.normalizer (Y : Set X)) : ⁅Y, S⁆ ≤ Y := by
  rw [Subgroup.commutator_le]
  intro y hy s hs
  have h1 : s * y⁻¹ * s⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (h hs) y⁻¹).mp (Y.inv_mem hy)
  rw [commutatorElement_def, show y * s * y⁻¹ * s⁻¹ = y * (s * y⁻¹ * s⁻¹) by group]
  exact Y.mul_mem hy h1

theorem SevenNineConfig.map {L S Y Z : Subgroup X} {p : ℕ} (h : SevenNineConfig L S p Y Z)
    (φ : X →* X') (hY : Y ⊓ φ.ker = ⊥) (hS : S ⊓ φ.ker = ⊥) :
    SevenNineConfig (L.map φ) (S.map φ) p (Y.map φ) (Z.map φ) := by
  have hZY : Z ≤ Y := by
    rw [h.z_eq]
    exact inf_le_left
  have hZ : Z ⊓ φ.ker = ⊥ := eq_bot_mono (inf_le_inf_right _ hZY) hY
  refine
    { prime := h.prime
      ne_two := h.ne_two
      card_s := (CFSG.card_map_eq_card_of_inf_ker_eq_bot φ hS).trans h.card_s
      le := Subgroup.map_mono h.le
      elemAbelian := h.elemAbelian.map φ
      s_le := (Subgroup.map_mono h.s_le).trans (Subgroup.le_normalizer_map φ)
      z_eq := ?_
      card_z := ?_
      z_le := ?_
      exists_conj := ?_ }
  · refine le_antisymm (le_inf (Subgroup.map_mono hZY) ?_) ?_
    · calc Z.map φ ≤ (Subgroup.centralizer (S : Set X)).map φ := by
            refine Subgroup.map_mono ?_
            rw [h.z_eq]
            exact inf_le_right
        _ ≤ Subgroup.centralizer (φ '' (S : Set X)) :=
            Subgroup.map_centralizer_le_centralizer_image _ φ
        _ = Subgroup.centralizer ((S.map φ : Subgroup X') : Set X') := by
            rw [Subgroup.coe_map]
    · rintro _ ⟨⟨y, hy, rfl⟩, hc⟩
      refine Subgroup.mem_map_of_mem φ ?_
      rw [h.z_eq]
      refine ⟨hy, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
      have hcs : φ s * φ y = φ y * φ s :=
        Subgroup.mem_centralizer_iff.mp hc (φ s) (Subgroup.mem_map_of_mem φ hs)
      have h1 : s * y⁻¹ * s⁻¹ ∈ Y :=
        (Subgroup.mem_normalizer_iff.mp (h.s_le hs) y⁻¹).mp (Y.inv_mem hy)
      have hmem : y * (s * y⁻¹ * s⁻¹) ∈ Y ⊓ φ.ker := Subgroup.mem_inf.mpr ⟨Y.mul_mem hy h1, by
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, ← mul_assoc,
          ← mul_assoc, ← hcs]
        group⟩
      rw [hY, Subgroup.mem_bot] at hmem
      calc s * y = (y * (s * y⁻¹ * s⁻¹))⁻¹ * y * s := by group
        _ = y * s := by rw [hmem, inv_one, one_mul]
  · rw [CFSG.card_map_eq_card_of_inf_ker_eq_bot φ hZ, CFSG.card_map_eq_card_of_inf_ker_eq_bot φ hY]
    exact h.card_z
  · refine (Subgroup.map_mono h.z_le).trans ?_
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup_le fun g => iSup_le fun hg => iSup_le fun h2 => ?_
    rw [← Subgroup.map_le_iff_le_comap, ← map_conjSubgroup_hom]
    have h2' : IsPGroup 2 ↥(S.map φ ⊔ conjSubgroup (S.map φ) (φ g)) := by
      rw [map_conjSubgroup_hom, ← Subgroup.map_sup]
      exact h2.map φ
    exact le_iSup_of_le (φ g) (le_iSup_of_le (Subgroup.mem_map_of_mem φ hg)
      (le_iSup_of_le h2' le_rfl))
  · intro B' hB'Y hB'card
    have hBY : Y ⊓ B'.comap φ ≤ Y := inf_le_left
    have hBmap : (Y ⊓ B'.comap φ).map φ = B' := by
      refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr inf_le_right) fun b hb => ?_
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp (hB'Y hb)
      exact Subgroup.mem_map_of_mem φ ⟨hy, hb⟩
    have hBk : (Y ⊓ B'.comap φ) ⊓ φ.ker = ⊥ := eq_bot_mono (inf_le_inf_right _ hBY) hY
    have hBcard : Nat.card ↥(Y ⊓ B'.comap φ) * p = Nat.card Y := by
      rw [← CFSG.card_map_eq_card_of_inf_ker_eq_bot φ hBk, hBmap, hB'card,
        CFSG.card_map_eq_card_of_inf_ker_eq_bot φ hY]
    obtain ⟨g, hgL, hgN, hne, hnle⟩ := h.exists_conj _ hBY hBcard
    have hgY : conjSubgroup (Y ⊓ B'.comap φ) g ≤ Y := fun x hx => by
      rw [mem_conjSubgroup_iff] at hx
      exact (Subgroup.mem_normalizer_iff.mp hgN x).mpr (hBY hx)
    refine ⟨φ g, Subgroup.mem_map_of_mem φ hgL,
      Subgroup.le_normalizer_map φ (Subgroup.mem_map_of_mem φ hgN), ?_, ?_⟩
    · rw [← hBmap, map_conjSubgroup_hom]
      intro heq
      exact hne (le_antisymm (le_of_map_le φ hY hgY hZY heq.le)
        (le_of_map_le φ hY hZY hgY heq.ge))
    · rw [← hBmap, map_conjSubgroup_hom, ← Subgroup.map_commutator]
      exact fun hle => hnle (le_of_map_le φ hY (commutator_le_of_le_normalizer h.s_le) hgY hle)

theorem SevenNineConfig.inf_centralizer_eq_bot {L S Y Z : Subgroup X} {p : ℕ}
    (h : SevenNineConfig L S p Y Z) [Finite Y] : S ⊓ Subgroup.centralizer (Y : Set X) = ⊥ := by
  have : Fact (Nat.card S).Prime := ⟨by rw [h.card_s]; exact Nat.prime_two⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card
      ((Subgroup.centralizer (Y : Set X)).subgroupOf S) with h1 | h1
  · exact disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp h1).symm
  · exfalso
    have hZ : Z = Y := by
      rw [h.z_eq]
      exact inf_eq_left.mpr (Subgroup.le_centralizer_iff.mp (Subgroup.subgroupOf_eq_top.mp h1))
    have hc := h.card_z
    rw [hZ] at hc
    have hp := h.prime.one_lt
    have hpos : 0 < Nat.card Y := Nat.card_pos
    nlinarith

end Map

section Quot

variable {f : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3)}

private theorem orthReflSet_three_eq_reflSet {m : ℕ}
    (f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)) :
    orthReflSet 3 m f = CFSG.Fischer.Classification.F3.reflSet f := by
  ext g
  simp only [orthReflSet, CFSG.Fischer.Classification.F3.reflSet, fischerTransvections,
    Set.mem_setOf_eq, show (-2 : ZMod 3) = 1 by decide]

theorem coe_eq_of_mem_center_orthRefl_three (hf : ∀ x y, f x y = f y x)
    (hnd : ∀ x, (∀ y, f x y = 0) → x = 0) {z : ↥(Subgroup.closure (orthReflSet 3 6 f))}
    (hz : z ∈ Subgroup.center ↥(Subgroup.closure (orthReflSet 3 6 f))) :
    (z : GL (Fin 6) (ZMod 3)) = 1 ∨ (z : GL (Fin 6) (ZMod 3)) = -1 := by
  have hR : Subgroup.closure (orthReflSet 3 6 f) =
      CFSG.Fischer.Classification.F3.reflGroup f := by
    rw [orthReflSet_three_eq_reflSet]
  have hz' : (⟨z, by rw [← hR]; exact z.2⟩ : ↥(CFSG.Fischer.Classification.F3.reflGroup f)) ∈
      Subgroup.center ↥(CFSG.Fischer.Classification.F3.reflGroup f) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    exact Subtype.ext (congrArg Subtype.val (hz ⟨g, by rw [hR]; exact g.2⟩))
  exact CFSG.Fischer.Classification.F3.coe_eq_of_mem_center ⟨hf, hnd⟩ (by norm_num) hz'

private theorem det_coe_mul (g h : ↥(Subgroup.closure (orthReflSet 3 6 f))) :
    (((g * h : ↥(Subgroup.closure (orthReflSet 3 6 f))) : GL (Fin 6) (ZMod 3)) :
      Matrix (Fin 6) (Fin 6) (ZMod 3)).det =
      ((g : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)).det *
        ((h : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)).det := by
  rw [Subgroup.coe_mul, Units.val_mul, Matrix.det_mul]

private theorem det_of_mem_orthReflSet {g : GL (Fin 6) (ZMod 3)} (hg : g ∈ orthReflSet 3 6 f) :
    (g : Matrix (Fin 6) (Fin 6) (ZMod 3)).det = -1 := by
  obtain ⟨v, hv, rfl⟩ := exists_eq_orthRefl_of_mem f hg
  exact orthRefl_det f hv

private theorem det_coe_of_mem_center (hf : ∀ x y, f x y = f y x)
    (hnd : ∀ x, (∀ y, f x y = 0) → x = 0) {z : ↥(Subgroup.closure (orthReflSet 3 6 f))}
    (hz : z ∈ Subgroup.center ↥(Subgroup.closure (orthReflSet 3 6 f))) :
    ((z : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)).det = 1 := by
  rcases coe_eq_of_mem_center_orthRefl_three hf hnd hz with h | h <;> rw [h]
  · rw [Units.val_one, Matrix.det_one]
  · rw [Units.val_neg, Units.val_one, Matrix.det_neg, Matrix.det_one, Fintype.card_fin]
    decide

private theorem pow_three_ne_one_of_coe_eq_neg_one
    {z : ↥(Subgroup.closure (orthReflSet 3 6 f))} (h : (z : GL (Fin 6) (ZMod 3)) = -1) :
    z ^ 3 ≠ 1 := by
  intro hz3
  have h3 : ((z : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, hz3]
    rfl
  rw [h, Units.val_neg, Units.val_one, Odd.neg_one_pow (show Odd 3 by decide)] at h3
  have h00 := congrFun (congrFun h3 0) 0
  rw [Matrix.neg_apply, Matrix.one_apply_eq] at h00
  exact absurd h00 (by decide)

private theorem exists_refl_of_reflQuot {X : Type} [Group X] {L S : Subgroup X} (hSL : S ≤ L)
    (hS : S ≠ ⊥) (hf : ∀ x y, f x y = f y x) (hnd : ∀ x, (∀ y, f x y = 0) → x = 0)
    (e : ↥L ≃* ↥(Subgroup.closure (orthReflSet 3 6 f)) ⧸
      Subgroup.center ↥(Subgroup.closure (orthReflSet 3 6 f)))
    (he : ∀ d ∈ {x : ↥L | (x : X) ∈ S ∧ x ≠ 1}, ∃ r : ↥(Subgroup.closure (orthReflSet 3 6 f)),
      (r : GL (Fin 6) (ZMod 3)) ∈ orthReflSet 3 6 f ∧ e d = QuotientGroup.mk r) :
    ∃ r : ↥(Subgroup.closure (orthReflSet 3 6 f)),
      (∃ a, f a a = -2 ∧ (r : GL (Fin 6) (ZMod 3)) = orthRefl f a) ∧
      ∀ x : ↥L, (x : X) ∈ S ↔ e x ∈ Subgroup.zpowers (QuotientGroup.mk r :
        ↥(Subgroup.closure (orthReflSet 3 6 f)) ⧸
          Subgroup.center ↥(Subgroup.closure (orthReflSet 3 6 f))) := by
  obtain ⟨s, hs1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hS
  let d₀ : ↥L := ⟨(s : X), hSL s.2⟩
  have hd₀S : (d₀ : X) ∈ S := s.2
  have hd₀1 : d₀ ≠ 1 := fun h =>
    hs1 (Subtype.ext (by simpa [d₀] using congrArg Subtype.val h))
  obtain ⟨r₀, hr₀, hd₀⟩ := he d₀ ⟨hd₀S, hd₀1⟩
  obtain ⟨a, ha, hr₀a⟩ := exists_eq_orthRefl_of_mem f hr₀
  have hr₀sq : r₀ * r₀ = 1 :=
    Subtype.ext (by rw [Subgroup.coe_mul, hr₀a, orthRefl_mul_self f ha]; rfl)
  have hd₀sq : d₀ * d₀ = 1 := e.injective (by
    rw [map_mul, map_one, hd₀, ← QuotientGroup.mk_mul, hr₀sq, QuotientGroup.mk_one])
  have key : ∀ x : ↥L, (x : X) ∈ S → x ≠ 1 → x = d₀ := by
    intro x hxS hx1
    by_contra hxd
    have hxd1 : x * d₀ ≠ 1 := fun h => hxd (by
      calc x = x * d₀ * d₀ := by rw [mul_assoc, hd₀sq, mul_one]
        _ = d₀ := by rw [h, one_mul])
    obtain ⟨r₁, hr₁, hx⟩ := he x ⟨hxS, hx1⟩
    obtain ⟨r₂, hr₂, hx₂⟩ := he (x * d₀) ⟨S.mul_mem hxS hd₀S, hxd1⟩
    have hq : (QuotientGroup.mk (r₁ * r₀) : ↥(Subgroup.closure (orthReflSet 3 6 f)) ⧸
        Subgroup.center ↥(Subgroup.closure (orthReflSet 3 6 f))) = QuotientGroup.mk r₂ := by
      rw [QuotientGroup.mk_mul, ← hx, ← hd₀, ← map_mul, hx₂]
    obtain ⟨z, hz, hr₂z⟩ : ∃ z ∈ Subgroup.center ↥(Subgroup.closure (orthReflSet 3 6 f)),
        r₂ = r₁ * r₀ * z := ⟨_, QuotientGroup.eq.mp hq, by group⟩
    have hdet := congrArg (fun g : ↥(Subgroup.closure (orthReflSet 3 6 f)) =>
      ((g : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)).det) hr₂z
    rw [det_coe_mul, det_coe_mul, det_coe_of_mem_center hf hnd hz, det_of_mem_orthReflSet hr₁,
      det_of_mem_orthReflSet hr₀, det_of_mem_orthReflSet hr₂] at hdet
    exact absurd hdet (by decide)
  refine ⟨r₀, ⟨a, ha, hr₀a⟩, fun x => ⟨fun hxS => ?_, fun hx => ?_⟩⟩
  · by_cases hx1 : x = 1
    · rw [hx1, map_one]
      exact Subgroup.one_mem _
    · rw [key x hxS hx1, hd₀]
      exact Subgroup.mem_zpowers _
  · have hmap : (Subgroup.zpowers d₀).map e.toMonoidHom = Subgroup.zpowers (QuotientGroup.mk r₀ :
        ↥(Subgroup.closure (orthReflSet 3 6 f)) ⧸
          Subgroup.center ↥(Subgroup.closure (orthReflSet 3 6 f))) := by
      rw [MonoidHom.map_zpowers]
      exact congrArg Subgroup.zpowers hd₀
    rw [← hmap] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hyx' : y = x := e.injective hyx
    have hle : Subgroup.zpowers d₀ ≤ S.subgroupOf L :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_subgroupOf.mpr hd₀S)
    rw [← hyx']
    exact Subgroup.mem_subgroupOf.mp (hle hy)

theorem exists_sevenNineConfig_of_reflQuot {X : Type} [Group X] {L S : Subgroup X}
    (hSL : S ≤ L) (hS : S ≠ ⊥) (hf : ∀ x y, f x y = f y x)
    (hnd : ∀ x, (∀ y, f x y = 0) → x = 0)
    (e : ↥L ≃* ↥(Subgroup.closure (orthReflSet 3 6 f)) ⧸
      Subgroup.center ↥(Subgroup.closure (orthReflSet 3 6 f)))
    (he : ∀ d ∈ {x : ↥L | (x : X) ∈ S ∧ x ≠ 1}, ∃ r : ↥(Subgroup.closure (orthReflSet 3 6 f)),
      (r : GL (Fin 6) (ZMod 3)) ∈ orthReflSet 3 6 f ∧ e d = QuotientGroup.mk r) :
    ∃ Y Z : Subgroup X, SevenNineConfig L S 3 Y Z := by
  obtain ⟨r₀, ⟨a, ha, hr₀a⟩, hSr⟩ := exists_refl_of_reflQuot hSL hS hf hnd e he
  obtain ⟨F, rfl⟩ := exists_orthFrameThree f hf hnd ha
  have hS₁ : ∀ x : ↥(⊤ : Subgroup ↥(Subgroup.closure (orthReflSet 3 6 f))),
      (x : ↥(Subgroup.closure (orthReflSet 3 6 f))) ∈ Subgroup.zpowers r₀ ↔
        ((Subgroup.topEquiv x : ↥(Subgroup.closure (orthReflSet 3 6 f))) :
          GL (Fin 6) (ZMod 3)) ∈ Subgroup.zpowers F.refl := by
    intro x
    have hm : (Subgroup.zpowers r₀).map (Subgroup.closure (orthReflSet 3 6 f)).subtype =
        Subgroup.zpowers F.refl := by
      rw [MonoidHom.map_zpowers]
      exact congrArg Subgroup.zpowers hr₀a
    rw [← hm]
    exact (Subgroup.mem_map_iff_mem (Subgroup.subtype_injective _)).symm
  obtain ⟨Y₁, Z₁, c₁⟩ : ∃ Y₁ Z₁ : Subgroup ↥(Subgroup.closure (orthReflSet 3 6 f)),
      SevenNineConfig ⊤ (Subgroup.zpowers r₀) 3 Y₁ Z₁ :=
    ⟨_, _, F.sevenNineConfig.of_mulEquiv Subgroup.topEquiv le_top
      (Subgroup.zpowers_le.mpr F.refl_mem_closure) hS₁⟩
  have hYk : Y₁ ⊓ (QuotientGroup.mk' (Subgroup.center
      ↥(Subgroup.closure (orthReflSet 3 6 f)))).ker = ⊥ := by
    rw [QuotientGroup.ker_mk', eq_bot_iff]
    rintro z ⟨hzY, hzc⟩
    rw [Subgroup.mem_bot]
    rcases coe_eq_of_mem_center_orthRefl_three hf hnd hzc with h | h
    · exact Subtype.ext h
    · exact absurd (c₁.elemAbelian.2 z hzY) (pow_three_ne_one_of_coe_eq_neg_one h)
  have hSk : Subgroup.zpowers r₀ ⊓ (QuotientGroup.mk' (Subgroup.center
      ↥(Subgroup.closure (orthReflSet 3 6 f)))).ker = ⊥ := by
    rw [QuotientGroup.ker_mk']
    exact eq_bot_mono (inf_le_inf_left _ (Subgroup.center_le_centralizer _))
      c₁.inf_centralizer_eq_bot
  have c₂ := c₁.map _ hYk hSk
  have hπ : (⊤ : Subgroup ↥(Subgroup.closure (orthReflSet 3 6 f))).map
      (QuotientGroup.mk' (Subgroup.center ↥(Subgroup.closure (orthReflSet 3 6 f)))) = ⊤ :=
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  refine ⟨_, _, c₂.of_mulEquiv (e.trans (Subgroup.topEquiv.symm.trans
    (MulEquiv.subgroupCongr hπ.symm))) hSL (Subgroup.map_mono le_top) fun x => ?_⟩
  rw [MonoidHom.map_zpowers]
  exact hSr x

end Quot

end CFSG.LocalAnalysis.WeakClosure81
