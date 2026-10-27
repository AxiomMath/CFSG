module

public import CFSG.Quasithin.Background.S1549DLnStar
public import CFSG.Quasithin.Background.S1549DA6Geo
public import CFSG.Quasithin.Background.S1549CC

public section

namespace CFSG.Quasithin

namespace S1549E

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
  CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom CFSG.Quasithin.S1549C CFSG.Quasithin.S1549D
open scoped commutatorElement Pointwise

@[expose] def LnParabolicOvergroups : Prop :=
  ∀ (n : ℕ), (n = 4 ∨ n = 5) → ∀ (A : Type) [Group A] [Finite A] (L X S P₀ : Subgroup A),
    Nonempty (↥L ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL n (ZMod 2))) → L ≤ X →
    (∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ ∈ L) → IsSylowTwoOf S X → X ≤ L ⊔ S → pCoreOf 2 X = ⊥ →
    IsMinParabolicOf L P₀ → (∀ s ∈ S, ∀ p ∈ P₀, s * p * s⁻¹ ∈ P₀) →
      (∃ K₁ K₂ : Subgroup A, IsMaxSubgroupIn X K₁ ∧ IsMaxSubgroupIn X K₂ ∧ K₁ ≠ K₂ ∧
          P₀ ⊔ S ≤ K₁ ∧ P₀ ⊔ S ≤ K₂) ∨
        (n = 4 ∧ L ≠ X ∧ IsMaxSubgroupIn X (P₀ ⊔ S))

@[expose] def LnSumNatDual : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X L S P₀ : Subgroup (MulAut V)) (z : V),
      Nonempty (↥L ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2))) → L ≤ X →
      (∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ ∈ L) → IsSylowTwoOf S X → X ≤ L ⊔ S → L ≠ X →
      pCoreOf 2 X = ⊥ → B51Hyp (ffJ X) L → IsMinParabolicOf L P₀ →
      (∀ s ∈ S, ∀ p ∈ P₀, s * p * s⁻¹ ∈ P₀) → IsMaxSubgroupIn X (P₀ ⊔ S) →
      (∀ s ∈ S, s z = z) → Subgroup.closure {v : V | ∃ g ∈ X, g z = v} = ⊤ →
      (∀ g ∈ X, g z = z → g ∈ P₀ ⊔ S) → B51Case1iii (ffJ X) L 4

@[expose] def LnInvariantParabolic : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L X S P₀ P : Subgroup A),
    Nonempty (↥L ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2))) → L ≤ X →
    (∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ ∈ L) → IsSylowTwoOf S X → X ≤ L ⊔ S → L ≠ X →
    pCoreOf 2 X = ⊥ → IsMinParabolicOf L P₀ → (∀ s ∈ S, ∀ p ∈ P₀, s * p * s⁻¹ ∈ P₀) →
    S ⊓ L ≤ P → P ≤ L → (∀ s ∈ S, ∀ p ∈ P, s * p * s⁻¹ ∈ P) → Nat.card ↥P = 192 → P = P₀

variable {G : Type} [Group G]

theorem conj_mem_sup_EA {A B : Subgroup G} {x : G} (hA : ∀ a ∈ A, x * a * x⁻¹ ∈ A)
    (hB : ∀ b ∈ B, x * b * x⁻¹ ∈ B) : ∀ y ∈ A ⊔ B, x * y * x⁻¹ ∈ A ⊔ B := by
  have hle : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj x).toMonoidHom :=
    sup_le (fun a ha => (le_sup_left : A ≤ A ⊔ B) (hA a ha))
      (fun b hb => (le_sup_right : B ≤ A ⊔ B) (hB b hb))
  intro y hy
  have := hle hy
  simpa [Subgroup.mem_comap, MulAut.conj_apply] using this

theorem le_of_isMaxSubgroupIn_EA {X K : Subgroup G} (h : IsMaxSubgroupIn X K) : K ≤ X := h.1.le

theorem ne_of_isMaxSubgroupIn_EA {X K : Subgroup G} (h : IsMaxSubgroupIn X K) : K ≠ X := h.1.ne

theorem sup_eq_of_isMaxSubgroupIn_EA {X K₁ K₂ : Subgroup G} (h₁ : IsMaxSubgroupIn X K₁)
    (h₂ : IsMaxSubgroupIn X K₂) (hne : K₁ ≠ K₂) : K₁ ⊔ K₂ = X := by
  have hle : K₁ ⊔ K₂ ≤ X := sup_le h₁.1.le h₂.1.le
  have hlt : K₁ < K₁ ⊔ K₂ := by
    refine lt_of_le_of_ne le_sup_left fun heq => ?_
    have h21 : K₂ ≤ K₁ := heq ▸ le_sup_right
    rcases h21.lt_or_eq with hlt | heq'
    · exact absurd (h₂.2 K₁ hlt h₁.1.le) (ne_of_lt h₁.1)
    · exact hne heq'.symm
  exact h₁.2 _ hlt hle

theorem eq_of_isMaxSubgroupIn_of_le_EA {X Q M' : Subgroup G} (hmax : IsMaxSubgroupIn X Q) (hQM : Q ≤ M')
    (hMX : M' ≤ X) (hne : M' ≠ X) : M' = Q := by
  by_contra hne'
  exact hne (hmax.2 M' (lt_of_le_of_ne hQM (Ne.symm hne')) hMX)

theorem isQuasisimple_of_equiv_aux {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : CFSG.IsQuasisimple X) : CFSG.IsQuasisimple Y :=
  h.of_mulEquiv e.symm

theorem isQuasisimple_of_equiv_statedSL_four_five {Y : Type} [Group Y] {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : Y ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL n (ZMod 2))) : CFSG.IsQuasisimple Y := by
  rcases hn with rfl | rfl
  · exact isQuasisimple_of_equiv_aux e.symm (isQuasisimple_of_equiv_aux
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL (3 + 1) (ZMod 2))
      (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 3 (ZMod 2) (by norm_num)))
  · exact isQuasisimple_of_equiv_aux e.symm (isQuasisimple_of_equiv_aux
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL (4 + 1) (ZMod 2))
      (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 4 (ZMod 2) (by norm_num)))

theorem card_of_equiv_statedSL_four_five {Y : Type} [Group Y] {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : Y ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL n (ZMod 2))) :
    Nat.card Y = 20160 ∨ Nat.card Y = 9999360 := by
  rcases hn with rfl | rfl
  · left
    rw [Nat.card_congr e.toEquiv]
    exact card_statedSL_four_zmod1527d
  · right
    rw [Nat.card_congr e.toEquiv]
    exact card_statedSL_five_zmod1527d

theorem mem_sup_prod_of_normalizes_EA {P₀ S : Subgroup G} (hn : ∀ s ∈ S, ∀ p ∈ P₀, s * p * s⁻¹ ∈ P₀) :
    ∀ x ∈ P₀ ⊔ S, ∃ p ∈ P₀, ∃ s ∈ S, x = p * s := by
  let PS : Subgroup G :=
    { carrier := {x | ∃ p ∈ P₀, ∃ s ∈ S, x = p * s}
      one_mem' := ⟨1, P₀.one_mem, 1, S.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨p, hp, s, hs, rfl⟩ ⟨p', hp', s', hs', rfl⟩
        refine ⟨p * (s * p' * s⁻¹), P₀.mul_mem hp (hn s hs p' hp'), s * s', S.mul_mem hs hs', ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨p, hp, s, hs, rfl⟩
        refine ⟨s⁻¹ * p⁻¹ * s⁻¹⁻¹, ?_, s⁻¹, S.inv_mem hs, ?_⟩
        · exact hn s⁻¹ (S.inv_mem hs) p⁻¹ (P₀.inv_mem hp)
        · group }
  have hle : P₀ ⊔ S ≤ PS :=
    sup_le (fun p hp => ⟨p, hp, 1, S.one_mem, by simp⟩) (fun s hs => ⟨1, P₀.one_mem, s, hs, by simp⟩)
  intro x hx
  exact hle hx

theorem centSub_inf_invariant_EA {V : Type} [CommGroup V] {L T : Subgroup (MulAut V)} {s : MulAut V}
    (hsL : ∀ l ∈ L, s * l * s⁻¹ ∈ L) (hsT : ∀ t ∈ T, s * t * s⁻¹ ∈ T) {p : MulAut V}
    (hp : p ∈ L ⊓ centSub (fixV T)) : s * p * s⁻¹ ∈ L ⊓ centSub (fixV T) := by
  refine ⟨hsL p hp.1, fun v hv => ?_⟩
  have hsv : s⁻¹ v ∈ fixV T := by
    intro t ht
    have h1 : (s * t * s⁻¹) v = v := hv _ (hsT t ht)
    have h2 : s⁻¹ ((s * t * s⁻¹) v) = t (s⁻¹ v) := by simp
    rw [← h2, h1]
  have hpv : p (s⁻¹ v) = s⁻¹ v := hp.2 _ hsv
  calc (s * p * s⁻¹) v = s (p (s⁻¹ v)) := by simp
    _ = s (s⁻¹ v) := by rw [hpv]
    _ = v := by simp

theorem card_GL_two_zmod_two_EA : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) = 6 := by
  rw [Matrix.card_GL_field]
  simp [Fin.prod_univ_two, ZMod.card]

section SecondCase

variable {V : Type} [CommGroup V] [Finite V]

theorem ln_second_case (hB51 : AsB51) (hB : LnSumNatDual) (hC : LnInvariantParabolic)
    (hV : ∀ v : V, v ^ 2 = 1) {X L S P₀ B : Subgroup (MulAut V)} {z : V}
    (hiso : Nonempty (↥L ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)))) (hLX : L ≤ X)
    (hLn : ∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ ∈ L) (hS : IsSylowTwoOf S X) (hXLS : X ≤ L ⊔ S)
    (hne : L ≠ X) (hO2 : pCoreOf 2 X = ⊥) (hHyp : B51Hyp (ffJ X) L) (hpar : IsMinParabolicOf L P₀)
    (hPn : ∀ s ∈ S, ∀ p ∈ P₀, s * p * s⁻¹ ∈ P₀) (hmax : IsMaxSubgroupIn X (P₀ ⊔ S))
    (hzS : ∀ s ∈ S, s z = z) (hgen : Subgroup.closure {v : V | ∃ g ∈ X, g z = v} = ⊤)
    (hMz : ∀ g ∈ X, g z = z → g ∈ P₀ ⊔ S) (hoff : IsFFStarOffender X B)
    (hBP : B ≤ pCoreOf 2 (P₀ ⊔ S)) : False := by
  classical
  have h3 : B51Case1iii (ffJ X) L 4 :=
    hB V hV X L S P₀ z hiso hLX hLn hS hXLS hne hO2 hHyp hpar hPn hmax hzS hgen hMz
  have hGL : ffJ X = L := h3.1
  have hpart6 : B51Part6 (ffJ X) L := (hB51 V hV (ffJ X) L hHyp).2.2.2.2.2
  have hXn : X ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_conj hLn
  have hTL : IsSylowTwoOf (S ⊓ L) L := B6.isSylowTwoOf_inf_normal hS hLX hXn
  have hTG : IsSylowTwoOf (S ⊓ L) (ffJ X) := by rw [hGL]; exact hTL
  obtain ⟨⟨R, hRle, -, hRcard, hRn, ⟨hRiso⟩⟩, hnoff⟩ := hpart6 4 h3 (S ⊓ L) hTG
  rw [hGL] at hnoff
  have hC192 : Nat.card ↥(L ⊓ centSub (fixV (S ⊓ L))) = 192 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (R.subgroupOf (L ⊓ centSub (fixV (S ⊓ L))))
    rw [Nat.card_congr hRiso.toEquiv, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRle).toEquiv,
      hRcard] at h1
    have h2 : Nat.card (Matrix.GeneralLinearGroup (Fin (4 - 2)) (ZMod 2)) = 6 :=
      card_GL_two_zmod_two_EA
    rw [h2] at h1
    omega
  have hTC : S ⊓ L ≤ L ⊓ centSub (fixV (S ⊓ L)) := fun t ht => ⟨ht.2, fun u hu => hu t ht⟩
  have hCS : ∀ s ∈ S, ∀ p ∈ L ⊓ centSub (fixV (S ⊓ L)), s * p * s⁻¹ ∈ L ⊓ centSub (fixV (S ⊓ L)) := by
    intro s hs p hp
    refine centSub_inf_invariant_EA (fun l hl => hLn s (hS.1 hs) l hl) (fun t ht => ?_) hp
    exact ⟨S.mul_mem (S.mul_mem hs ht.1) (S.inv_mem hs), hLn s (hS.1 hs) t ht.2⟩
  have hCeq : L ⊓ centSub (fixV (S ⊓ L)) = P₀ :=
    hC (MulAut V) L X S P₀ _ hiso hLX hLn hS hXLS hne hO2 hpar hPn hTC inf_le_left hCS hC192
  have hP₀L : P₀ ≤ L := by
    obtain ⟨T', -, hP⟩ := hpar
    exact hP.1.1
  have hTP : S ⊓ L ≤ P₀ := hCeq ▸ hTC
  have hKL : (P₀ ⊔ S) ⊓ L ≤ P₀ := by
    rintro x ⟨hxK, hxL⟩
    obtain ⟨p, hp, s, hs, rfl⟩ := mem_sup_prod_of_normalizes_EA hPn x hxK
    have hsL : s ∈ L := by
      have := L.mul_mem (L.inv_mem (hP₀L hp)) hxL
      simpa [mul_assoc] using this
    exact P₀.mul_mem hp (hTP ⟨hs, hsL⟩)
  have hBL : B ≤ L := by
    have := B6.le_ffJ hoff
    rwa [hGL] at this
  have hBK : B ≤ P₀ ⊔ S := hBP.trans (pCoreOf_le 2 _)
  have hBP₀ : B ≤ P₀ := fun b hb => hKL ⟨hBK hb, hBL hb⟩
  have hBO : B ≤ pCoreOf 2 P₀ := (le_inf hBP hBP₀).trans (F7.pCoreOf_inf_le (le_sup_left : P₀ ≤ P₀ ⊔ S))
  exact hnoff B ⟨hBL, hoff.2⟩ (by rw [hCeq]; exact hBO)

end SecondCase

theorem _root_.CFSG.Quasithin.S1549C.input49Ln_of_named_inputs
    (h113 : StageLemma14113) (hB51 : AsB51) (hA : LnParabolicOvergroups) (hB : LnSumNatDual)
    (hC : LnInvariantParabolic) : S1549C.Input49Ln := by
  intro G _ _ T Mc M V₁ V₂ t cx H hb W B od L e n hn
  rintro ⟨iso⟩
  classical
  have h := hb.hF98.toHypF91
  let _ : CommGroup (UTil T M V₁ H) := modInst h
  have hV : ∀ v : UTil T M V₁ H, v ^ 2 = 1 := fun w => by
    apply Subtype.ext
    have := h.isElemAbelian_tilde.2
      (w : SecQuot (Subgroup.normalizer ((quasithinOmegaOneCenter T : Subgroup G) : Set G))
        (quasithinOmegaOneCenter T)) w.2
    simpa using this
  have hLH : L ≤ H := (le_of_mem_cComp e.lctx.comp).trans (preStar_le _ _)
  have hTH : T ≤ H := h.T_le_H
  have hY0H : Y0 T Mc M ≤ H := le_sup_left.trans hb.adm.hY0
  have hY0L : Y0 T Mc M ≤ L := e.k.trans (le_of_eq e.l.eq)
  have hHeq : H = L ⊔ T := by
    calc H = conjClosure L T ⊔ Y0 T Mc M ⊔ T := e.lctx.eq
      _ = L ⊔ Y0 T Mc M ⊔ T := by rw [e.l.eq]
      _ = L ⊔ T := by rw [sup_eq_left.mpr hY0L]
  have hTnL : ∀ y ∈ T, ∀ l' ∈ L, y * l' * y⁻¹ ∈ L := fun y hy l' hl' =>
    e.l.eq ▸ mem_conjClosure hy hl'
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := by
    rw [hHeq]
    refine sup_le Subgroup.le_normalizer ?_
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro l
    exact ⟨fun hl => hTnL x hx l hl, fun hl => by simpa [mul_assoc] using hTnL x⁻¹ (T.inv_mem hx) _ hl⟩
  have hTMH : T ≤ M ⊓ H := le_inf cx.c.hyp.T_le hTH
  have hY0M : Y0 T Mc M ≤ M :=
    (Y0_le T Mc M).trans (inf_le_left.trans (Y153_le Mc M))
  have iso' : Nonempty (↥(starOfSub h L) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL n (ZMod 2))) := by
    rw [← starOf_eq_starOfSub cx hb hLH]
    exact ⟨iso⟩
  obtain ⟨iso''⟩ := iso'
  have hLq : CFSG.IsQuasisimple ↥(starOfSub h L) := isQuasisimple_of_equiv_statedSL_four_five hn iso''
  have hLc : Nat.card ↥(starOfSub h L) = 20160 ∨ Nat.card ↥(starOfSub h L) = 9999360 :=
    card_of_equiv_statedSL_four_five hn iso''
  have hLc' : Nat.card ↥(StarOf T M V₁ H L) = 20160 ∨ Nat.card ↥(StarOf T M V₁ H L) = 9999360 := by
    rw [starOf_eq_starOfSub cx hb hLH]
    exact hLc
  have hLs : SQTKGroup ↥(starOfSub h L) := sqtkGroup_starOfSub cx hb hLH
  have hLX : starOfSub h L ≤ starOfSub h H := starOfSub_mono h hLH
  have hXLS : starOfSub h H ≤ starOfSub h L ⊔ starOfSub h T := by
    rw [congrArg (starOfSub h) hHeq, starOfSub_sup h hLH hTH]
  have hLn : ∀ x ∈ starOfSub h H, ∀ l ∈ starOfSub h L, x * l * x⁻¹ ∈ starOfSub h L := by
    intro x hx l hl
    obtain ⟨x', -, rfl⟩ := (mem_starOfSub h).mp hx
    obtain ⟨l', hl'L, rfl⟩ := (mem_starOfSub h).mp hl
    refine (mem_starOfSub h).mpr ⟨x' * l' * x'⁻¹, ?_, by simp [map_mul, map_inv]⟩
    have := (Subgroup.mem_normalizer_iff.mp (hHL x'.2) (l' : G)).mp hl'L
    simpa using this
  have hS : IsSylowTwoOf (starOfSub h T) (starOfSub h H) := by
    rw [starOfSub_H h]
    exact isSylowTwoOf_starOfSub_T h
  have hO2 : pCoreOf 2 (starOfSub h H) = ⊥ := pCoreOf_starOfSub_H h
  have hLJ := starOfSub_le_ffJ cx hb od e.lctx
  have hpar : IsMinParabolicOf (starOfSub h L) (starOfSub h (Y0 T Mc M ⊔ (T ⊓ L))) := by
    rcases e.l.par with h7 | hhat | hmp
    · exfalso
      obtain ⟨e7⟩ := h7
      have h1 := Nat.card_congr e7.toEquiv
      rw [card_alternatingGroup1527d 7 (by norm_num)] at h1
      norm_num [Nat.factorial] at h1
      omega
    · exfalso
      have h1 := card_of_isHat1527d hhat (by
        rw [card_alternatingGroup1527d 6 (by norm_num)]
        norm_num [Nat.factorial])
      omega
    · rwa [starOf_eq_starOfSub cx hb hLH,
        starOf_eq_starOfSub cx hb (sup_le hY0H (inf_le_left.trans hTH))] at hmp
  have hPS : starOfSub h (Y0 T Mc M ⊔ T) =
      starOfSub h (Y0 T Mc M ⊔ (T ⊓ L)) ⊔ starOfSub h T := by
    rw [← starOfSub_sup h (sup_le hY0H (inf_le_left.trans hTH)) hTH]
    congr 1
    exact le_antisymm (sup_le (le_sup_of_le_left le_sup_left) le_sup_right)
      (sup_le (sup_le le_sup_left (inf_le_left.trans le_sup_right)) le_sup_right)
  have hPnorm : ∀ s ∈ starOfSub h T, ∀ p ∈ starOfSub h (Y0 T Mc M ⊔ (T ⊓ L)),
      s * p * s⁻¹ ∈ starOfSub h (Y0 T Mc M ⊔ (T ⊓ L)) := by
    intro s hs p hp
    obtain ⟨x, hxT, rfl⟩ := (mem_starOfSub h).mp hs
    obtain ⟨y, hyP, rfl⟩ := (mem_starOfSub h).mp hp
    refine (mem_starOfSub h).mpr ⟨x * y * x⁻¹, ?_, by simp [map_mul, map_inv]⟩
    have hN : ∀ g ∈ (Y0 T Mc M ⊔ (T ⊓ L)), (x : G) * g * (x : G)⁻¹ ∈ (Y0 T Mc M ⊔ (T ⊓ L)) := by
      refine conj_mem_sup_EA (fun g hg => ?_) (fun g hg => ?_)
      · exact (Subgroup.mem_normalizer_iff.mp
          (le_normalizer_Y0 cx.c.hyp (cx.c.hyp.T_le hxT)) g).mp hg
      · exact ⟨T.mul_mem (T.mul_mem hxT hg.1) (T.inv_mem hxT), hTnL _ hxT _ hg.2⟩
    simpa using hN y hyP
  rcases hA n hn (MulAut (UTil T M V₁ H)) (starOfSub h L) (starOfSub h H) (starOfSub h T)
      (starOfSub h (Y0 T Mc M ⊔ (T ⊓ L))) ⟨iso''⟩ hLX hLn hS hXLS hO2 hpar hPnorm with
    ⟨K₁, K₂, hK₁, hK₂, hne, hQ₁, hQ₂⟩ | ⟨hn4, hLne, hmax⟩
  ·
    exfalso
    have hK₁M := S1549D.overgroup_le_M_of_minimal cx hb (hPS.le.trans hQ₁) (le_of_isMaxSubgroupIn_EA hK₁) (ne_of_isMaxSubgroupIn_EA hK₁)
    have hK₂M := S1549D.overgroup_le_M_of_minimal cx hb (hPS.le.trans hQ₂) (le_of_isMaxSubgroupIn_EA hK₂) (ne_of_isMaxSubgroupIn_EA hK₂)
    have hsup := sup_eq_of_isMaxSubgroupIn_EA hK₁ hK₂ hne
    have hXM : starOfSub h H ≤ starOfSub h (M ⊓ H) := by
      rw [← hsup]
      exact sup_le hK₁M hK₂M
    exact not_starOfSub_L_le_M h113 cx hb od e.lctx (hLX.trans hXM)
  ·
    subst hn4
    have hQM : starOfSub h (Y0 T Mc M ⊔ T) ≤ starOfSub h (M ⊓ H) :=
      starOfSub_mono h (sup_le (le_inf hY0M hY0H) hTMH)
    have hMX : starOfSub h (M ⊓ H) ≤ starOfSub h H := starOfSub_mono h inf_le_right
    have hMne : starOfSub h (M ⊓ H) ≠ starOfSub h H := fun heq =>
      not_starOfSub_L_le_M h113 cx hb od e.lctx (hLX.trans heq.ge)
    have hMQ : starOfSub h (M ⊓ H) = starOfSub h (Y0 T Mc M ⊔ (T ⊓ L)) ⊔ starOfSub h T :=
      eq_of_isMaxSubgroupIn_of_le_EA hmax (hPS.symm.le.trans hQM) hMX hMne
    obtain ⟨a, haS, haZ⟩ := exists_zvec cx.c
    have hzS : ∀ s ∈ starOfSub h T, s (vecOf h a (le_conjClosure _ _ haS)) =
        vecOf h a (le_conjClosure _ _ haS) := by
      intro s hs
      obtain ⟨x, hxT, rfl⟩ := (mem_starOfSub h).mp hs
      exact starHom_T_zvec cx.c h haS hxT
    have hgen : Subgroup.closure {v | ∃ g ∈ starOfSub h H,
        g (vecOf h a (le_conjClosure _ _ haS)) = v} = ⊤ := by
      have := closure_orbit_zvec cx.c h haS haZ
      rwa [← starOfSub_H h] at this
    have hMz : ∀ g ∈ starOfSub h H, g (vecOf h a (le_conjClosure _ _ haS)) =
        vecOf h a (le_conjClosure _ _ haS) →
          g ∈ starOfSub h (Y0 T Mc M ⊔ (T ⊓ L)) ⊔ starOfSub h T := by
      intro g hg hgz
      obtain ⟨x, -, rfl⟩ := (mem_starOfSub h).mp hg
      rw [← hMQ]
      exact (mem_starOfSub h).mpr ⟨x, ⟨mem_M_of_fix_zvec cx.c cx.r46 h haS haZ hgz, x.2⟩, rfl⟩
    have hoff : IsFFStarOffender (V := UTil T M V₁ H) (starOfSub h H) B := by
      have := od.off
      rwa [starOf_eq_starOfSub cx hb le_rfl] at this
    have hWH : W ≤ H := (od.W_le.trans (pCoreOf_le 2 _)).trans (sup_le hY0H hTH)
    have hBP : B ≤ pCoreOf 2 (starOfSub h (Y0 T Mc M ⊔ (T ⊓ L)) ⊔ starOfSub h T) := by
      have h1 : B ≤ starOfSub h (pCoreOf 2 (Y0 T Mc M ⊔ T)) := by
        have := od.B_le
        rw [starOf_eq_starOfSub cx hb hWH] at this
        exact this.trans (starOfSub_mono h od.W_le)
      rw [← hPS]
      exact h1.trans (starOfSub_pCoreOf_le h (sup_le hY0H hTH))
    have hHyp := b51Hyp_ffJ (V := UTil T M V₁ H) hLn hLq hLs hS hXLS hO2 hLJ
    exact ln_second_case hB51 hB hC hV ⟨iso''⟩ hLX hLn hS hXLS hLne hO2 hHyp hpar hPnorm hmax hzS
      hgen hMz hoff hBP

end S1549E

end CFSG.Quasithin
