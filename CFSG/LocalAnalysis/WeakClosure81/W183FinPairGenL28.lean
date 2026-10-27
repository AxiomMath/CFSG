module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2PairGen
import CFSG.GH74.KGroups.PSL2
import CFSG.LocalAnalysis.WeakClosure81.W183FinPairGenL28Aux1
public import CFSG.CGT.Timmesfeld75.L2Basic
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin (GF8)
open CFSG.CGT.Timmesfeld75
open scoped MatrixGroups
open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2)

private instance w183finCharPGF8 : CharP GF8 2 := by
  refine ⟨fun x => ?_⟩
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' x
  · have h2 : (2 : GF8) = 0 := by decide
    simp [h2]
  · have h2 : (2 : GF8) = 0 := by decide
    simp [h2, Nat.cast_add, Nat.cast_mul]

private theorem w183finCoeUtriElt (s : GF8) :
    ((utriElt s : SL(2, GF8)) : w183finM2) = w183finU s := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [w183finU, utriElt_apply_00, utriElt_apply_01,
    utriElt_apply_10, utriElt_apply_11]

private theorem w183finCoeLtriElt (s : GF8) :
    ((ltriElt s : SL(2, GF8)) : w183finM2) = w183finL s := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [w183finL, ltriElt_apply_00, ltriElt_apply_01,
    ltriElt_apply_10, ltriElt_apply_11]

private def w183finEvalS (g : Fin 4 → SL(2, GF8)) (w : List (Fin 4)) : SL(2, GF8) :=
  w.foldl (fun X i => X * g i) 1

private theorem w183finCoeEvalS (g : Fin 4 → SL(2, GF8)) (w : List (Fin 4)) :
    ((w183finEvalS g w : SL(2, GF8)) : w183finM2) =
      w183finEvalW (fun i => (g i : w183finM2)) w := by
  unfold w183finEvalS w183finEvalW
  suffices h : ∀ X : SL(2, GF8), ((w.foldl (fun X i => X * g i) X : SL(2, GF8)) : w183finM2) =
      w.foldl (fun Y i => Y * (g i : w183finM2)) (X : w183finM2) by simpa using h 1
  induction w with
  | nil => intro X; rfl
  | cons i w ih => intro X; simp only [List.foldl_cons]; rw [ih]; simp

private theorem w183finEvalS_mem (g : Fin 4 → SL(2, GF8)) (H : Subgroup SL(2, GF8))
    (hg : ∀ i, g i ∈ H) (w : List (Fin 4)) : w183finEvalS g w ∈ H := by
  unfold w183finEvalS
  suffices h : ∀ X : SL(2, GF8), X ∈ H → w.foldl (fun X i => X * g i) X ∈ H by
    simpa using h 1 H.one_mem
  induction w with
  | nil => intro X hX; exact hX
  | cons i w ih => intro X hX; simp only [List.foldl_cons]; exact ih _ (H.mul_mem hX (hg i))

private theorem w183finExistsTwoNeOne {G : Type*} [Group G] (E : Subgroup G)
    (h : 3 ≤ Nat.card E) : ∃ x ∈ E, ∃ y ∈ E, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y := by
  classical
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by omega)
  have h3 : Nat.card (E : Set G) = Nat.card E := rfl
  have h2 : 1 < ((E : Set G) \ {1}).ncard := by
    rw [Set.ncard_diff_singleton_of_mem E.one_mem, ← Nat.card_coe_set_eq]
    omega
  obtain ⟨x, y, hx, hy, hxy⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).1 h2
  exact ⟨x, hx.1, y, hy.1, hx.2, hy.2, hxy⟩

private theorem w183finCoeGens (a₁ a₂ b₁ b₂ : GF8) :
    (fun i => ((![utriElt a₁, utriElt a₂, ltriElt b₁, ltriElt b₂] i : SL(2, GF8)) :
      w183finM2)) = ![w183finU a₁, w183finU a₂, w183finL b₁, w183finL b₂] := by
  funext i
  fin_cases i <;> simp [w183finCoeUtriElt, w183finCoeLtriElt]

private theorem w183finSpan : ∀ a₁ a₂ c s : GF8, a₁ ≠ 0 → a₂ ≠ 0 → a₁ ≠ a₂ → c ≠ 0 →
    c ≠ a₁ → c ≠ a₂ → c ≠ a₁ + a₂ → ∃ x y z : Bool,
      s = (if x then a₁ else 0) + (if y then a₂ else 0) + (if z then c else 0) := by
  decide +kernel

private theorem w183finSupEqTop {E F : Subgroup SL(2, GF8)} (hE : E ≤ utri GF8)
    (hF : F ≤ ltri GF8) (hE4 : 4 ≤ Nat.card E) (hF4 : 4 ≤ Nat.card F) : E ⊔ F = ⊤ := by
  obtain ⟨x, hx, y, hy, hx1, hy1, hxy⟩ := w183finExistsTwoNeOne E (by omega)
  obtain ⟨x', hx', y', hy', hx1', hy1', hxy'⟩ := w183finExistsTwoNeOne F (by omega)
  obtain ⟨a₁, rfl⟩ := mem_utri_iff.1 (hE hx)
  obtain ⟨a₂, rfl⟩ := mem_utri_iff.1 (hE hy)
  obtain ⟨b₁, rfl⟩ := mem_ltri_iff.1 (hF hx')
  obtain ⟨b₂, rfl⟩ := mem_ltri_iff.1 (hF hy')
  have ha₁ : a₁ ≠ 0 := fun h => hx1 (by rw [h, utriElt_zero])
  have ha₂ : a₂ ≠ 0 := fun h => hy1 (by rw [h, utriElt_zero])
  have ha12 : a₁ ≠ a₂ := fun h => hxy (by rw [h])
  have hb₁ : b₁ ≠ 0 := fun h => hx1' (by
    rw [h]; apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [ltriElt])
  have hb₂ : b₂ ≠ 0 := fun h => hy1' (by
    rw [h]; apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [ltriElt])
  have hb12 : b₁ ≠ b₂ := fun h => hxy' (by rw [h])
  obtain ⟨w, -, c, hc0, hc1, hc2, hc3, hw⟩ :=
    w183finKey a₁ a₂ b₁ b₂ ha₁ ha₂ ha12 hb₁ hb₂ hb12
  set H := E ⊔ F with hH
  have hgen : ∀ i, ![utriElt a₁, utriElt a₂, ltriElt b₁, ltriElt b₂] i ∈ H := by
    intro i
    fin_cases i
    · exact Subgroup.mem_sup_left hx
    · exact Subgroup.mem_sup_left hy
    · exact Subgroup.mem_sup_right hx'
    · exact Subgroup.mem_sup_right hy'
  have hw' := w183finEvalS_mem _ H hgen w
  have hval : w183finEvalS ![utriElt a₁, utriElt a₂, ltriElt b₁, ltriElt b₂] w = utriElt c := by
    apply Subtype.ext
    rw [w183finCoeEvalS, w183finCoeGens, hw, w183finCoeUtriElt]
  rw [hval] at hw'
  have hu : ∀ s, (utriElt s : SL(2, GF8)) ∈ H := by
    intro s
    obtain ⟨p, q, r, hs⟩ := w183finSpan a₁ a₂ c s ha₁ ha₂ ha12 hc0 hc1 hc2 hc3
    rw [hs, utriElt_add, utriElt_add]
    refine H.mul_mem (H.mul_mem ?_ ?_) ?_
    · split_ifs
      · exact Subgroup.mem_sup_left hx
      · rw [utriElt_zero]; exact H.one_mem
    · split_ifs
      · exact Subgroup.mem_sup_left hy
      · rw [utriElt_zero]; exact H.one_mem
    · split_ifs
      · exact hw'
      · rw [utriElt_zero]; exact H.one_mem
  have hutri : utri GF8 ≤ H := fun g hg => by
    obtain ⟨s, rfl⟩ := mem_utri_iff.1 hg
    exact hu s
  have hl : (ltriElt b₁ : SL(2, GF8)) ∈ H := Subgroup.mem_sup_right hx'
  have hne : conjSubgroup 1 (utri GF8) ≠ conjSubgroup (ltriElt b₁) (utri GF8) := by
    intro h
    rw [conjSubgroup_eq_conjSubgroup_iff, normalizer_utri, inv_one, one_mul, mem_borel_iff] at h
    exact hb₁ (by simpa [ltriElt_apply_10] using h)
  have htop := sup_conjSubgroup_utri_eq_top hne
  rw [eq_top_iff, ← htop]
  refine sup_le ?_ ?_
  · rw [conjSubgroup_one]; exact hutri
  · intro z hz
    rw [mem_conjSubgroup] at hz
    have h1 := hutri hz
    have h2 : (ltriElt b₁ : SL(2, GF8)) * ((ltriElt b₁)⁻¹ * z * ltriElt b₁) *
        (ltriElt b₁)⁻¹ ∈ H := H.mul_mem (H.mul_mem hl h1) (H.inv_mem hl)
    simpa [mul_assoc] using h2

private theorem w183finCardGF8 : Nat.card GF8 = 8 := by
  rw [Nat.card_eq_fintype_card]; decide

private theorem w183finPairGenL28Gen : ∀ (Y : Type) [Group Y], IsL2 Y 3 → ∀ P₁ P₂ : Subgroup Y,
    IsElemAbelian 2 P₁ → IsElemAbelian 2 P₂ → Nat.card P₁ = 8 → Nat.card P₂ = 8 → P₁ ≠ P₂ →
    ∀ E F : Subgroup Y, E ≤ P₁ → F ≤ P₂ → 4 ≤ Nat.card E → 4 ≤ Nat.card F → E ⊔ F = ⊤ := by
  intro Y _ hY P₁ P₂ h₁ h₂ c₁ c₂ hne E F hE hF hE4 hF4
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel (F := GF8) 2 3 (by norm_num)
    (by rw [w183finCardGF8]; norm_num) hY
  let φ : Y ≃* SL(2, GF8) := e.trans pslMulEquivSL
  let P₁' : Subgroup SL(2, GF8) := P₁.map φ.toMonoidHom
  let P₂' : Subgroup SL(2, GF8) := P₂.map φ.toMonoidHom
  let E' : Subgroup SL(2, GF8) := E.map φ.toMonoidHom
  let F' : Subgroup SL(2, GF8) := F.map φ.toMonoidHom
  have hinj : Function.Injective φ.toMonoidHom := φ.injective
  have hc₁' : Nat.card P₁' = 8 := by
    rw [Subgroup.card_map_of_injective hinj, c₁]
  have hc₂' : Nat.card P₂' = 8 := by
    rw [Subgroup.card_map_of_injective hinj, c₂]
  have hE4' : 4 ≤ Nat.card E' := by rw [Subgroup.card_map_of_injective hinj]; exact hE4
  have hF4' : 4 ≤ Nat.card F' := by rw [Subgroup.card_map_of_injective hinj]; exact hF4
  have hP₁2 : IsPGroup 2 P₁' := (CFSG.Open.IsElemAbelian.isPGroup h₁).map φ.toMonoidHom
  have hP₂2 : IsPGroup 2 P₂' := (CFSG.Open.IsElemAbelian.isPGroup h₂).map φ.toMonoidHom
  have hL : Nat.card SL(2, GF8) = 504 := by rw [card_sl2, w183finCardGF8]; norm_num
  have hidx : ∀ P : Subgroup SL(2, GF8), Nat.card P = 8 → ¬ 2 ∣ P.index := by
    intro P hP hdvd
    have := Subgroup.card_mul_index P
    rw [hP, hL] at this
    omega
  let S₁ : Sylow 2 SL(2, GF8) := IsPGroup.toSylow hP₁2 (hidx _ hc₁')
  let S₂ : Sylow 2 SL(2, GF8) := IsPGroup.toSylow hP₂2 (hidx _ hc₂')
  have hS : S₁ ≠ S₂ := by
    intro h
    apply hne
    have : (S₁ : Subgroup SL(2, GF8)) = S₂ := congrArg _ h
    exact Subgroup.map_injective hinj this
  obtain ⟨a, b, ha, hb, hab⟩ := exists_conj_of_sylow_ne hS
  obtain ⟨g, hga, hgb⟩ := exists_conj_utri_ltri_of_ne hab
  have hP₁g : P₁' = conjSubgroup g (utri GF8) := by rw [← hga, ha]; rfl
  have hP₂g : P₂' = conjSubgroup g (ltri GF8) := by rw [← hgb, hb]; rfl
  let E₀ : Subgroup SL(2, GF8) := conjSubgroup g⁻¹ E'
  let F₀ : Subgroup SL(2, GF8) := conjSubgroup g⁻¹ F'
  have hE' : E' ≤ P₁' := Subgroup.map_mono hE
  have hF' : F' ≤ P₂' := Subgroup.map_mono hF
  have hE₀ : E₀ ≤ utri GF8 := by
    intro x hx
    rw [mem_conjSubgroup, inv_inv] at hx
    have := hE' hx
    rw [hP₁g, mem_conjSubgroup] at this
    simpa [mul_assoc] using this
  have hF₀ : F₀ ≤ ltri GF8 := by
    intro x hx
    rw [mem_conjSubgroup, inv_inv] at hx
    have := hF' hx
    rw [hP₂g, mem_conjSubgroup] at this
    simpa [mul_assoc] using this
  have hcE₀ : 4 ≤ Nat.card E₀ := by
    change 4 ≤ Nat.card (E'.map (MulAut.conj g⁻¹).toMonoidHom)
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]; exact hE4'
  have hcF₀ : 4 ≤ Nat.card F₀ := by
    change 4 ≤ Nat.card (F'.map (MulAut.conj g⁻¹).toMonoidHom)
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]; exact hF4'
  have htop := w183finSupEqTop hE₀ hF₀ hcE₀ hcF₀
  have h1 : E' ⊔ F' = ⊤ := by
    have := congrArg (conjSubgroup g) htop
    rw [conjSubgroup_sup_eq_sup, conjSubgroup_top] at this
    simpa [E₀, F₀, conjSubgroup_conjSubgroup, conjSubgroup_one] using this
  have h2 : (E ⊔ F).map φ.toMonoidHom = ⊤ := by
    rw [Subgroup.map_sup]; exact h1
  have := congrArg (Subgroup.comap φ.toMonoidHom) h2
  rwa [Subgroup.comap_map_eq_self_of_injective hinj, Subgroup.comap_top] at this

private theorem w183finOddOrderOfMul {G : Type*} [Group G] [Finite G] {P₁ P₂ : Subgroup G}
    {a b : G} (hTI : P₁ ⊓ P₂ = ⊥) (ha2 : a * a = 1) (hb2 : b * b = 1)
    (ha : Subgroup.centralizer ({a} : Set G) ≤ P₁)
    (hb : Subgroup.centralizer ({b} : Set G) ≤ P₂) : Odd (orderOf (a * b)) := by
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨k, hk⟩ := even_iff_exists_two_mul.mp hodd
  have hnpos : 0 < orderOf (a * b) := orderOf_pos _
  have hkpos : 0 < k := by omega
  let z : G := (a * b) ^ k
  have hz2 : z * z = 1 := by
    dsimp only [z]
    rw [← pow_add, ← two_mul, ← hk, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    intro hz
    have hdvd : orderOf (a * b) ∣ k := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact hz
    have hle : orderOf (a * b) ≤ k := Nat.le_of_dvd hkpos hdvd
    omega
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hconj : ∀ c : G, c * c = 1 → c * (a * b) * c⁻¹ = (a * b)⁻¹ → c * z * c⁻¹ = z := by
    intro c hc hcab
    calc c * z * c⁻¹ = (c * (a * b) * c⁻¹) ^ k := by
          rw [← MulAut.conj_apply, ← MulAut.conj_apply, ← map_pow]
      _ = ((a * b)⁻¹) ^ k := by rw [hcab]
      _ = z⁻¹ := by rw [inv_pow]
      _ = z := inv_eq_of_mul_eq_one_right hz2
  have haz : a * z * a⁻¹ = z := by
    refine hconj a ha2 ?_
    rw [mul_inv_rev, ha', hb']
    calc a * (a * b) * a = (a * a) * b * a := by group
      _ = b * a := by rw [ha2, one_mul]
  have hbz : b * z * b⁻¹ = z := by
    refine hconj b hb2 ?_
    rw [mul_inv_rev, ha', hb']
    calc b * (a * b) * b = b * a * (b * b) := by group
      _ = b * a := by rw [hb2, mul_one]
  have hzCa : z ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.mp haz).symm
  have hzCb : z ∈ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.mp hbz).symm
  have hmem : z ∈ P₁ ⊓ P₂ := Subgroup.mem_inf.mpr ⟨ha hzCa, hb hzCb⟩
  rw [hTI] at hmem
  exact hz1 (Subgroup.mem_bot.mp hmem)

private theorem w183finPairGenL28Odd : ∀ (Y : Type) [Group Y], IsL2 Y 3 → ∀ P₁ P₂ : Subgroup Y,
    IsElemAbelian 2 P₁ → IsElemAbelian 2 P₂ → Nat.card P₁ = 8 → Nat.card P₂ = 8 → P₁ ≠ P₂ →
    ∀ a ∈ P₁, ∀ b ∈ P₂, a ≠ 1 → b ≠ 1 → Odd (orderOf (a * b)) := by
  intro Y _ hY P₁ P₂ h₁ h₂ c₁ c₂ hne a ha b hb ha1 hb1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel (F := GF8) 2 3 (by norm_num)
    (by rw [w183finCardGF8]; norm_num) hY
  let φ : Y ≃* SL(2, GF8) := e.trans pslMulEquivSL
  let P₁' : Subgroup SL(2, GF8) := P₁.map φ.toMonoidHom
  let P₂' : Subgroup SL(2, GF8) := P₂.map φ.toMonoidHom
  have hinj : Function.Injective φ.toMonoidHom := φ.injective
  have hc₁' : Nat.card P₁' = 8 := by
    rw [Subgroup.card_map_of_injective hinj, c₁]
  have hc₂' : Nat.card P₂' = 8 := by
    rw [Subgroup.card_map_of_injective hinj, c₂]
  have hP₁2 : IsPGroup 2 P₁' := (CFSG.Open.IsElemAbelian.isPGroup h₁).map φ.toMonoidHom
  have hP₂2 : IsPGroup 2 P₂' := (CFSG.Open.IsElemAbelian.isPGroup h₂).map φ.toMonoidHom
  have hL : Nat.card SL(2, GF8) = 504 := by rw [card_sl2, w183finCardGF8]; norm_num
  have hidx : ∀ P : Subgroup SL(2, GF8), Nat.card P = 8 → ¬ 2 ∣ P.index := by
    intro P hP hdvd
    have := Subgroup.card_mul_index P
    rw [hP, hL] at this
    omega
  let S₁ : Sylow 2 SL(2, GF8) := IsPGroup.toSylow hP₁2 (hidx _ hc₁')
  let S₂ : Sylow 2 SL(2, GF8) := IsPGroup.toSylow hP₂2 (hidx _ hc₂')
  have hS : S₁ ≠ S₂ := by
    intro h
    apply hne
    have : (S₁ : Subgroup SL(2, GF8)) = S₂ := congrArg _ h
    exact Subgroup.map_injective hinj this
  have hS₁ : (S₁ : Subgroup SL(2, GF8)) = P₁' := rfl
  have hS₂ : (S₂ : Subgroup SL(2, GF8)) = P₂' := rfl
  have hTI : P₁' ⊓ P₂' = ⊥ := by
    by_contra hbot
    obtain ⟨x, hx, hx1⟩ : ∃ x : SL(2, GF8), x ∈ P₁' ⊓ P₂' ∧ x ≠ 1 := by
      obtain ⟨w, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hbot
      exact ⟨(w : SL(2, GF8)), w.2, fun hh => hw1 (Subtype.ext hh)⟩
    have h1 := centralizer_eq_of_mem_sylow hx1 (P := S₁) (hS₁ ▸ (Subgroup.mem_inf.mp hx).1)
    have h2 := centralizer_eq_of_mem_sylow hx1 (P := S₂) (hS₂ ▸ (Subgroup.mem_inf.mp hx).2)
    exact hS (Sylow.ext (h1.symm.trans h2))
  have hφa : φ a ∈ P₁' := Subgroup.mem_map_of_mem _ ha
  have hφb : φ b ∈ P₂' := Subgroup.mem_map_of_mem _ hb
  have hφa1 : φ a ≠ 1 := fun h => ha1 (φ.injective (by simpa using h))
  have hφb1 : φ b ≠ 1 := fun h => hb1 (φ.injective (by simpa using h))
  have ha2 : φ a * φ a = 1 := by
    rw [← map_mul]
    have := h₁.2 a ha
    rw [pow_two] at this
    rw [this, map_one]
  have hb2 : φ b * φ b = 1 := by
    rw [← map_mul]
    have := h₂.2 b hb
    rw [pow_two] at this
    rw [this, map_one]
  have hCa : Subgroup.centralizer ({φ a} : Set SL(2, GF8)) ≤ P₁' :=
    (centralizer_eq_of_mem_sylow hφa1 (P := S₁) (hS₁ ▸ hφa)).le
  have hCb : Subgroup.centralizer ({φ b} : Set SL(2, GF8)) ≤ P₂' :=
    (centralizer_eq_of_mem_sylow hφb1 (P := S₂) (hS₂ ▸ hφb)).le
  have hodd := w183finOddOrderOfMul hTI ha2 hb2 hCa hCb
  rwa [← map_mul, MulEquiv.orderOf_eq φ] at hodd

theorem finPairGenL28_holds : FinPairGenL28 := by
  intro Y _ hY P₁ P₂ h₁ h₂ c₁ c₂ hne
  exact ⟨w183finPairGenL28Gen Y hY P₁ P₂ h₁ h₂ c₁ c₂ hne,
    w183finPairGenL28Odd Y hY P₁ P₂ h₁ h₂ c₁ c₂ hne⟩

end CFSG.LocalAnalysis.WeakClosure81

end
