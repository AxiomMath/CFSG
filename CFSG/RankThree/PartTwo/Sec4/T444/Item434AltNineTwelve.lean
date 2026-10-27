module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltGenProof
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltNinePerm
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Source.GammaTwoSubgroups

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434Alt

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open Equiv Equiv.Perm Subgroup Item434AltPerm

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G} {n : ℕ}

theorem altPerm_injOn (h : Ctx434Core G A M Q) (hn : n = 5 ∨ 7 ≤ n)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* alternatingGroup (Fin n))
    (hZ : Subgroup.center (layer G) = ⊥) {x y : G} (hx : x ∈ layer G) (hy : y ∈ layer G)
    (hxy : altPerm hn e x = altPerm hn e y) : x = y := by
  have hLk : layer G ⊓ (altPerm hn e).ker = ⊥ := by
    rw [layer_inf_ker_altPerm h.isQuasisimple, hZ, Subgroup.map_bot]
  have hmem : x⁻¹ * y ∈ layer G ⊓ (altPerm hn e).ker :=
    Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hx) hy,
      by rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]⟩
  rw [hLk, Subgroup.mem_bot] at hmem
  exact inv_mul_eq_one.mp hmem

theorem preimage_isElemAbelian (h : Ctx434Core G A M Q) (hn : n = 5 ∨ 7 ≤ n)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* alternatingGroup (Fin n))
    (hZ : Subgroup.center (layer G) = ⊥) {P : Subgroup (Perm (Fin n))}
    (hPA : P ≤ alternatingGroup (Fin n)) (hP : IsMulCommutative P ∧ ∀ x ∈ P, x ^ 3 = 1) :
    CFSG.Assembly.IsElemAbelian 3 (layer G ⊓ P.comap (altPerm hn e)) ∧
      Nat.card (layer G ⊓ P.comap (altPerm hn e) : Subgroup G) = Nat.card P := by
  set β := altPerm hn e with hβ
  have hLk : layer G ⊓ β.ker = ⊥ := by
    rw [layer_inf_ker_altPerm h.isQuasisimple, hZ, Subgroup.map_bot]
  have hPL : P ≤ (layer G).map β := by
    rw [map_layer_altPerm]
    exact hPA
  refine ⟨⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨haL, haP⟩ := Subgroup.mem_inf.mp a.2
    obtain ⟨hbL, hbP⟩ := Subgroup.mem_inf.mp b.2
    refine altPerm_injOn h hn e hZ (mul_mem haL hbL) (mul_mem hbL haL) ?_
    change β ((a : G) * b) = β ((b : G) * a)
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hP.1.is_comm.comm ⟨_, haP⟩ ⟨_, hbP⟩)
  · intro x hx
    obtain ⟨hxL, hxP⟩ := Subgroup.mem_inf.mp hx
    refine altPerm_injOn h hn e hZ (pow_mem hxL 3) (one_mem _) ?_
    rw [map_pow, map_one]
    exact hP.2 _ hxP
  · rw [card_inf_comap β hPL, hLk, Subgroup.card_bot, one_mul]

theorem commute_of_altPerm (h : Ctx434Core G A M Q) (hn : n = 5 ∨ 7 ≤ n)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* alternatingGroup (Fin n))
    (hZ : Subgroup.center (layer G) = ⊥) {x g : G} (hx : x ∈ layer G)
    (hc : altPerm hn e g * altPerm hn e x = altPerm hn e x * altPerm hn e g) :
    g * x = x * g := by
  have : (layer G).Characteristic := layer_characteristic
  have hN : (layer G).Normal := inferInstance
  have h1 : g * x * g⁻¹ = x := by
    refine altPerm_injOn h hn e hZ (hN.conj_mem x hx g) hx ?_
    rw [map_mul, map_mul, map_inv, hc, mul_inv_cancel_right]
  calc g * x = g * x * g⁻¹ * g := by group
    _ = x * g := by rw [h1]

theorem isElemAbelian_F12 :
    CFSG.Assembly.IsElemAbelian 3 (A0 12 ⊔ zpowers (dd 12)) ∧
      Nat.card (A0 12 ⊔ zpowers (dd 12) : Subgroup _) = 81 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf := w12Facts
  have hA := hf.w.toA0Facts
  have hab := isElemAbelian_A0 hA
  have hdd : dd 12 ∉ A0 12 := fun hd => dd_notMem_W hf (mem_sup_left hd)
  obtain ⟨he, hc⟩ := Sec5.isElemAbelian_sup_zpowers (A := A0 12) ⟨hab.1, hab.2⟩ hdd hf.dd_pow
    fun a ha => (mem_centralizer_singleton_iff.mp (W_le_centralizer_dd hf (mem_sup_left ha)))
  exact ⟨he, by rw [hc, card_A0 hA]⟩

theorem false_of_alt_twelve (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* alternatingGroup (Fin 12)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn : 12 = 5 ∨ 7 ≤ 12 := Or.inr (by norm_num)
  have hf := w12Facts
  have hA0 := hf.w.toA0Facts
  set β := altPerm hn e with hβ
  have hZ := center_layer_eq_bot_of_eight_le h e (by norm_num)
  obtain ⟨g, hg⟩ := exists_le_map_conj_W12 hf (h.isE27.isPGroup.map β)
  set z := vecPerm 12 ![1, 1, 1] with hz
  set F := A0 12 ⊔ zpowers (dd 12) with hF
  obtain ⟨hFe, hF81⟩ := isElemAbelian_F12
  have hzF : z ∈ F := mem_sup_left (vecPerm_mem_A0 hA0 _)
  have hdF : dd 12 ∈ F := mem_sup_right (mem_zpowers _)
  have hFA : F ≤ alternatingGroup (Fin 12) := fun x hx => sign_eq_one_of_pow_three (hFe.2 x hx)
  set Fg := F.map (MulAut.conj g).toMonoidHom with hFg
  have hFgA : Fg ≤ alternatingGroup (Fin 12) := by
    rw [hFg, ← map_conj_alternatingGroup g]
    exact Subgroup.map_mono hFA
  have hFge : IsMulCommutative Fg ∧ ∀ x ∈ Fg, x ^ 3 = 1 :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ F hFe
  have hFgc : ∀ x ∈ Fg, ∀ y ∈ Fg, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hFge.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hz1 : g * z * g⁻¹ ∈ Fg := ⟨z, hzF, rfl⟩
  have hz2 : g * dd 12 * g⁻¹ ∈ Fg := ⟨dd 12, hdF, rfl⟩
  have hLmap := map_layer_altPerm hn e
  obtain ⟨l₁, hl₁L, hl₁⟩ : g * z * g⁻¹ ∈ (layer G).map β := by
    rw [hLmap]
    exact hFgA hz1
  obtain ⟨l₂, hl₂L, hl₂⟩ : g * dd 12 * g⁻¹ ∈ (layer G).map β := by
    rw [hLmap]
    exact hFgA hz2
  have hcen : ∀ {l : G}, l ∈ layer G → (∀ a ∈ A, β a * β l = β l * β a) →
      l ∈ Subgroup.centralizer (A : Set G) := by
    intro l hl hc
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (commute_of_altPerm h hn e hZ hl (hc a ha))
  have hl₁A : l₁ ∈ A := by
    refine h.rank3II_4_35 (hcen hl₁L fun a ha => ?_) ?_
    · rw [hl₁]
      exact commute_z_of_mem_map hf (hg ⟨a, ha, rfl⟩)
    · refine altPerm_injOn h hn e hZ (pow_mem hl₁L 3) (one_mem _) ?_
      rw [map_pow, hl₁, map_one]
      exact hFge.2 _ hz1
  have hl₂A : l₂ ∈ A := by
    refine h.rank3II_4_35 (hcen hl₂L fun a ha => ?_) ?_
    · rw [hl₂]
      exact commute_dd_of_mem_map hf (hg ⟨a, ha, rfl⟩)
    · refine altPerm_injOn h hn e hZ (pow_mem hl₂L 3) (one_mem _) ?_
      rw [map_pow, hl₂, map_one]
      exact hFge.2 _ hz2
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (h.isE27.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hl₁e : CFSG.Assembly.IsElemAbelian 3 (zpowers l₁) :=
    Source.isElemAbelian_of_le h.isE27.1 (zpowers_le.mpr hl₁A)
  have hl₂x : l₂ ∉ zpowers l₁ := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hk' := congrArg β hk
    rw [map_zpow, hl₁, hl₂] at hk'
    have hdz : dd 12 = z ^ k := by
      have : g * dd 12 * g⁻¹ = g * z ^ k * g⁻¹ := by rw [← hk', conj_zpow]
      exact mul_left_cancel (mul_right_cancel this)
    apply hf.dd9
    have hzs : z ∈ MulAction.stabilizer (Perm (Fin 12)) (9 : Fin 12) :=
      W_le_stabilizer_nine hf (mem_sup_left (vecPerm_mem_A0 hA0 _))
    have := zpow_mem hzs k
    rw [← hdz] at this
    exact this
  obtain ⟨hBe, hBcard⟩ := Sec5.isElemAbelian_sup_zpowers hl₁e hl₂x (h.isE27.1.2 _ hl₂A)
    fun a ha => hAc _ (zpowers_le.mpr hl₁A ha) _ hl₂A
  set B := zpowers l₁ ⊔ zpowers l₂ with hB
  have hBA : B ≤ A := sup_le (zpowers_le.mpr hl₁A) (zpowers_le.mpr hl₂A)
  have hl₁1 : l₁ ≠ 1 := by
    rintro rfl
    rw [map_one] at hl₁
    have hz1' : z = 1 := by
      have := congrArg (fun x => g⁻¹ * x * g) hl₁
      simpa [mul_assoc] using this.symm
    have := hA0.inj ![1, 1, 1] hz1'
    exact absurd (congrFun this 0) (by simp)
  have hl₁o : Nat.card (zpowers l₁) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (h.isE27.1.2 _ hl₁A) hl₁1
  have hB2 : 2 ≤ CFSG.Open.pRank 3 B :=
    le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three B)
      ⟨B, le_rfl, hBe, by rw [hBcard, hl₁o]; norm_num⟩
  obtain ⟨hDe, hDcard⟩ := preimage_isElemAbelian h hn e hZ hFgA hFge
  set D := layer G ⊓ Fg.comap β with hD
  have hDB : D ≤ Subgroup.centralizer (B : Set G) := by
    rw [Subgroup.le_centralizer_iff, hB, sup_le_iff, zpowers_le, zpowers_le]
    refine ⟨Subgroup.mem_centralizer_iff.mpr fun x hx => ?_,
      Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    · obtain ⟨-, hxF⟩ := Subgroup.mem_inf.mp hx
      refine commute_of_altPerm h hn e hZ hl₁L ?_
      rw [hl₁]
      exact hFgc _ hxF _ hz1
    · obtain ⟨-, hxF⟩ := Subgroup.mem_inf.mp hx
      refine commute_of_altPerm h hn e hZ hl₂L ?_
      rw [hl₂]
      exact hFgc _ hxF _ hz2
  have hDM : D ≤ M := hDB.trans ((Subgroup.centralizer_le_normalizer _).trans
    ((normalizer_le_gamma hBA hB2).trans h.gamma_le))
  have h4 : 4 ≤ CFSG.Open.pRank 3 M :=
    le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three M)
      ⟨D, hDM, hDe, by
        rw [hDcard, hFg, Subgroup.card_map_of_injective (MulAut.conj g).injective, hF81]
        norm_num⟩
  rw [h.pRank_eq] at h4
  omega

theorem false_of_alt_nine (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* alternatingGroup (Fin 9)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn : 9 = 5 ∨ 7 ≤ 9 := Or.inr (by norm_num)
  have hf := wFacts_nine
  set β := altPerm hn e with hβ
  have hker : β.ker = Subgroup.centralizer (layer G : Set G) := ker_altPerm h.isQuasisimple hn e
  have hZ := center_layer_eq_bot_of_eight_le h e (by norm_num)
  obtain ⟨D, hDL, hDe, hD27⟩ := exists_E27_le_layer h hn e hf.toA0Facts hZ
  have hC1 := inf_centralizer_layer_eq_bot_of_le h hZ hDL hDe hD27
  have hA27 := card_eq_card_inf_ker_mul_card_map β A
  rw [h.isE27.2, hker, hC1, Subgroup.card_bot, one_mul] at hA27
  have hEe := CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 β A h.isE27.1
  obtain ⟨g, hg⟩ := exists_eq_map_conj_A0 hf factorization_nine hEe hA27.symm
  obtain ⟨-, hQ3, hAQ⟩ := (mem_invariantPiSubgroups_piCompl_iff Nat.prime_three).mp
    h.mem_invariant
  have hQC := Item434.inf_centralizer_layer_eq_bot h
  set β' := (MulAut.conj g⁻¹).toMonoidHom.comp β with hβ'
  have hker' : β'.ker = Subgroup.centralizer (layer G : Set G) := by
    rw [← hker]
    ext x
    simp only [hβ', MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  have hXcard : Nat.card (Q.map β') = Nat.card Q := by
    have h1 := card_eq_card_inf_ker_mul_card_map β' Q
    rw [hker', hQC, Subgroup.card_bot, one_mul] at h1
    exact h1.symm
  have hAmap : A.map β' = A0 9 := by
    rw [hβ', ← Subgroup.map_map, hg]
    have h1 := map_conj_map_conj_inv (A0 9) g⁻¹
    rwa [inv_inv] at h1
  have hA0X : A0 9 ≤ normalizer ((Q.map β' : Subgroup _) : Set (Perm (Fin 9))) := by
    rw [← hAmap]
    exact (Subgroup.map_mono hAQ).trans (Subgroup.le_normalizer_map β')
  have hXbot := eq_bot_of_A0_le_normalizer (by rw [hXcard]; exact hQ3) hA0X
  apply h.ne_bot
  rw [← Subgroup.card_eq_one, ← hXcard, hXbot, Subgroup.card_bot]

end CFSG.RankThree.PartTwo.Sec4.Item434Alt
