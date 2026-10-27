module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3Split
import CFSG.Quasithin.Background.B4L3Coord

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
private theorem s16h_e3_l3_iSup_inv {L : Subgroup (MulAut W)} {ι : Sort*} (A : ι → Subgroup W)
    (hA : ∀ i, ∀ l ∈ L, ∀ x ∈ A i, l x ∈ A i) :
    ∀ l ∈ L, ∀ x ∈ ⨆ i, A i, l x ∈ ⨆ i, A i := by
  intro l hl x hx
  refine Subgroup.iSup_induction (C := fun t => l t ∈ ⨆ i, A i) A hx ?_ ?_ ?_
  · intro i y hy
    exact Subgroup.mem_iSup_of_mem i (hA i l hl y hy)
  · rw [map_one]
    exact (⨆ i, A i).one_mem
  · intro y z hy hz
    rw [map_mul]
    exact (⨆ i, A i).mul_mem hy hz

omit [Finite W] in
private theorem s16h_e3_l3_sup_inv {L : Subgroup (MulAut W)} {A B : Subgroup W}
    (hA : ∀ l ∈ L, ∀ x ∈ A, l x ∈ A) (hB : ∀ l ∈ L, ∀ x ∈ B, l x ∈ B) :
    ∀ l ∈ L, ∀ x ∈ A ⊔ B, l x ∈ A ⊔ B := by
  intro l hl x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hx
  rw [map_mul]
  exact Subgroup.mul_mem_sup (hA l hl a ha) (hB l hl b hb)

omit [Finite W] in
private theorem s16h_e3_l3_inf_inv {L : Subgroup (MulAut W)} {A B : Subgroup W}
    (hA : ∀ l ∈ L, ∀ x ∈ A, l x ∈ A) (hB : ∀ l ∈ L, ∀ x ∈ B, l x ∈ B) :
    ∀ l ∈ L, ∀ x ∈ A ⊓ B, l x ∈ A ⊓ B := by
  intro l hl x hx
  exact ⟨hA l hl x hx.1, hB l hl x hx.2⟩

theorem s16h_e3_l3_mem_of_comm_mem {L : Subgroup (MulAut W)} {I Z : Subgroup W}
    (hI : BinaryNaturalSL L I Z 3 1) {x : W} (hx : x ∈ I) (hxl : ∀ l ∈ L, l x * x⁻¹ ∈ Z) :
    x ∈ Z := by
  obtain ⟨D⟩ := hI.toL3Coord
  have key : D.β ⟨x, hx⟩ = 1 := by
    by_contra hne
    have hv : Multiplicative.toAdd (D.β ⟨x, hx⟩) ≠ 0 := by
      intro h
      exact hne (Multiplicative.toAdd.injective h)
    obtain ⟨γ, hγ⟩ := L3.act_nofix _ hv
    have hZmem : D.rho γ x * x⁻¹ ∈ Z := hxl (D.rho γ) (D.rho_mem γ)
    have hmemI : D.rho γ x ∈ I := D.inv_U _ (D.rho_mem γ) _ hx
    have h1 : D.β ⟨D.rho γ x * x⁻¹, I.mul_mem hmemI (I.inv_mem hx)⟩ = 1 :=
      (D.ker_β _).mpr hZmem
    have h2 : D.β ⟨D.rho γ x, hmemI⟩ * (D.β ⟨x, hx⟩)⁻¹ = 1 := by
      have := h1
      rwa [show (⟨D.rho γ x * x⁻¹, I.mul_mem hmemI (I.inv_mem hx)⟩ : ↥I) =
            ⟨D.rho γ x, hmemI⟩ * ⟨x, hx⟩⁻¹ from Subtype.ext rfl,
           map_mul, map_inv] at this
    have h3 := D.β_rho γ x hx hmemI
    have h4 : L3.act γ (Multiplicative.toAdd (D.β ⟨x, hx⟩)) =
        Multiplicative.toAdd (D.β ⟨x, hx⟩) :=
      Multiplicative.ofAdd.injective (by
        show Multiplicative.ofAdd (L3.act γ (Multiplicative.toAdd (D.β ⟨x, hx⟩))) =
          D.β ⟨x, hx⟩
        rw [← h3]
        exact (mul_inv_eq_one).mp h2)
    exact hγ h4
  exact (D.ker_β ⟨x, hx⟩).mp key

theorem s16h_e3_l3_eq_of_not_le_fixV {L : Subgroup (MulAut W)} {J : Subgroup W}
    (hJ : BinaryNaturalSL L J (J ⊓ fixV L) 3 1) (hJc : commSub J L = J) {Y : Subgroup W}
    (hYJ : Y ≤ J) (hYinv : ∀ l ∈ L, ∀ y ∈ Y, l y ∈ Y) (hY : ¬ Y ≤ J ⊓ fixV L) :
    Y = J := by
  obtain ⟨D⟩ := hJ.toL3Coord
  have hsupJ : Y ⊔ (J ⊓ fixV L) ≤ J := sup_le hYJ (inf_le_left : J ⊓ fixV L ≤ J)
  have hFinv : ∀ l ∈ L, ∀ x ∈ J ⊓ fixV L, l x ∈ J ⊓ fixV L := by
    intro l hl x hx
    refine ⟨D.inv_U l hl x hx.1, ?_⟩
    rw [hx.2 l hl]
    exact hx.2
  have hYinv' : ∀ l ∈ L, ∀ x ∈ Y ⊔ (J ⊓ fixV L), l x ∈ Y ⊔ (J ⊓ fixV L) :=
    s16h_e3_l3_sup_inv hYinv hFinv
  have hY' : Y ⊔ (J ⊓ fixV L) = J := by
    let f : ↥(Y ⊔ (J ⊓ fixV L)) →* Multiplicative L3.Vec :=
      D.β.comp (Subgroup.inclusion hsupJ)
    let K : Subgroup (Multiplicative L3.Vec) := f.range
    obtain ⟨y, hyY, hyF⟩ := Set.not_subset.mp hY
    let y0 : ↥(Y ⊔ (J ⊓ fixV L)) := ⟨y, Subgroup.mem_sup_left hyY⟩
    have hfy : f y0 ≠ 1 := by
      intro h
      apply hyF
      have h1 : f y0 = D.β ⟨y, hsupJ (Subgroup.mem_sup_left hyY)⟩ := rfl
      rw [h1] at h
      exact (D.ker_β _).mp h
    have hfy0 : Multiplicative.toAdd (f y0) ≠ 0 := by
      intro h
      exact hfy (Multiplicative.toAdd.injective h)
    have hKinv : ∀ (γ : L3.Γ) (v : Multiplicative L3.Vec), v ∈ K →
        Multiplicative.ofAdd (L3.act γ (Multiplicative.toAdd v)) ∈ K := by
      intro γ v hv
      obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hv
      refine MonoidHom.mem_range.mpr
        ⟨⟨D.rho γ (u : W), hYinv' (D.rho γ) (D.rho_mem γ) (u : W) u.2⟩, ?_⟩
      change D.β ⟨D.rho γ (u : W),
          hsupJ (hYinv' (D.rho γ) (D.rho_mem γ) (u : W) u.2)⟩ =
        Multiplicative.ofAdd (L3.act γ
          (Multiplicative.toAdd (D.β ⟨(u : W), hsupJ u.2⟩)))
      exact D.β_rho γ (u : W) (hsupJ u.2)
        (D.inv_U (D.rho γ) (D.rho_mem γ) (u : W) (hsupJ u.2))
    have hKtop : K = ⊤ := by
      apply eq_top_iff.mpr
      intro w _
      by_cases hw : w = 1
      · rw [hw]; exact K.one_mem
      · have hw0 : Multiplicative.toAdd w ≠ 0 := fun h =>
          hw (Multiplicative.toAdd.injective h)
        obtain ⟨γ, hγ⟩ := L3.act_trans (Multiplicative.toAdd (f y0))
          (Multiplicative.toAdd w) hfy0 hw0
        have hmem := hKinv γ (f y0) (MonoidHom.mem_range.mpr ⟨y0, rfl⟩)
        rw [hγ] at hmem
        simpa using hmem
    apply le_antisymm hsupJ _
    intro u hu
    have hmemK : D.β ⟨u, hu⟩ ∈ K := by rw [hKtop]; exact Subgroup.mem_top _
    obtain ⟨u', hu'⟩ := MonoidHom.mem_range.mp hmemK
    have huβ : D.β (Subgroup.inclusion hsupJ u') = D.β ⟨u, hu⟩ := by
      show f u' = D.β ⟨u, hu⟩
      exact hu'
    have hker : (u' : W) * u⁻¹ ∈ J ⊓ fixV L := by
      have h1 : D.β (Subgroup.inclusion hsupJ u' * ⟨u, hu⟩⁻¹) = 1 := by
        rw [map_mul, map_inv, huβ]
        exact mul_inv_cancel _
      have h2 := (D.ker_β _).mp h1
      simpa using h2
    have huu : u = ((u' : W) * u⁻¹)⁻¹ * (u' : W) := by group
    rw [huu]
    exact (Y ⊔ (J ⊓ fixV L)).mul_mem
      ((Y ⊔ (J ⊓ fixV L)).inv_mem (Subgroup.mem_sup_right hker)) u'.2
  have hcomm_le : commSub (Y ⊔ (J ⊓ fixV L)) L ≤ Y := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨l, hl, w, hw, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hw
    have hlf : l b = b := hb.2 l hl
    have h1 : l (a * b) * (a * b)⁻¹ = l a * a⁻¹ := by
      rw [map_mul, hlf]
      group
    rw [h1]
    exact Y.mul_mem (hYinv l hl a ha) (Y.inv_mem ha)
  apply le_antisymm hYJ
  calc J = commSub J L := hJc.symm
    _ = commSub (Y ⊔ (J ⊓ fixV L)) L := by rw [hY']
    _ ≤ Y := hcomm_le

theorem s16h_e3_l3_fixV_le_of_inv (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    {J : Subgroup W} (hJ : BinaryNaturalSL L J (J ⊓ fixV L) 3 1) (hJc : commSub J L = J)
    (hJr : rk ↥(J ⊓ fixV L) = 1) {Y : Subgroup W} (hYJ : Y ≤ J)
    (hYinv : ∀ l ∈ L, ∀ y ∈ Y, l y ∈ Y) (hY : Y ≠ ⊥) :
    J ⊓ fixV L ≤ Y := by
  have hFcard : Nat.card ↥(J ⊓ fixV L) = 2 := by
    have := card_eq_two_pow hW (J ⊓ fixV L)
    rw [hJr] at this
    simpa using this
  by_cases hle : Y ≤ J ⊓ fixV L
  · have hYcard : Nat.card Y ≠ 1 := by
      intro h
      exact hY (Subgroup.card_eq_one.mp h)
    have hdvd : Nat.card Y ∣ Nat.card ↥(J ⊓ fixV L) := Subgroup.card_dvd_of_le hle
    rw [hFcard] at hdvd
    have h2 : Nat.card Y = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact absurd h hYcard
      · exact h
    exact le_of_eq (Subgroup.eq_of_le_of_card_ge hle (by rw [h2, hFcard])).symm
  · rw [s16h_e3_l3_eq_of_not_le_fixV hJ hJc hYJ hYinv hle]
    exact inf_le_left

theorem s16h_e3_l3_inf_fixV_ne_bot (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} {k : ℕ}
    (S : S16hL3Split L k) (T : Finset (Fin k)) {X : Subgroup W}
    (hXT : X ≤ ⨆ j ∈ T, S.J j) (hXinv : ∀ l ∈ L, ∀ x ∈ X, l x ∈ X) (hX : X ≠ ⊥) :
    X ⊓ fixV L ≠ ⊥ := by
  classical
  have main : ∀ T : Finset (Fin k), ∀ X : Subgroup W, X ≤ ⨆ j ∈ T, S.J j →
      (∀ l ∈ L, ∀ x ∈ X, l x ∈ X) → X ≠ ⊥ → X ⊓ fixV L ≠ ⊥ := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro X hXT hXinv hX
      have h : X ≤ ⊥ := by simpa using hXT
      exact absurd (le_bot_iff.mp h) hX
    | insert j T' hj ih =>
      intro X hXT hXinv hX
      set P : Subgroup W := ⨆ i ∈ T', S.J i with hP
      have hXT' : X ≤ S.J j ⊔ P := by
        rw [Finset.iSup_insert, ← hP] at hXT
        exact hXT
      have hPinv : ∀ l ∈ L, ∀ p ∈ P, l p ∈ P := by
        intro l hl p hp
        rw [hP] at hp ⊢
        exact s16h_e3_l3_iSup_inv (fun i : Fin k => ⨆ (_ : i ∈ T'), S.J i)
          (fun i => s16h_e3_l3_iSup_inv (fun _ : i ∈ T' => S.J i) (fun _ => S.J_inv i))
          l hl p hp
      have hJjinv : ∀ l ∈ L, ∀ x ∈ S.J j, l x ∈ S.J j := S.J_inv j
      have hPle : P ≤ ⨆ (i : Fin k) (_ : i ≠ j), S.J i := by
        rw [hP]
        apply iSup_le
        intro i
        apply iSup_le
        intro hi
        exact le_iSup_of_le i (le_iSup_of_le (fun hji => hj (hji ▸ hi)) le_rfl)
      have hJP : S.J j ⊓ P = ⊥ := by
        have h1 : S.J j ⊓ P ≤ S.J j ⊓ (⨆ (i : Fin k) (_ : i ≠ j), S.J i) :=
          inf_le_inf le_rfl hPle
        exact le_bot_iff.mp (h1.trans (le_of_eq (S.J_ind j)))
      by_cases hXP : X ⊓ P = ⊥
      · set X' : Subgroup W := (X ⊔ P) ⊓ S.J j with hX'def
        have hX'J : X' ≤ S.J j := inf_le_right
        have hXPinv : ∀ l ∈ L, ∀ x ∈ X ⊔ P, l x ∈ X ⊔ P :=
          s16h_e3_l3_sup_inv hXinv hPinv
        have hX'inv : ∀ l ∈ L, ∀ x ∈ X', l x ∈ X' :=
          s16h_e3_l3_inf_inv hXPinv hJjinv
        have hX'ne : X' ≠ ⊥ := by
          obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hX
          have hxX : (x : W) ∈ X := x.2
          have hxW1 : (x : W) ≠ 1 := fun h => hx1 (Subtype.ext h)
          have hxmem : (x : W) ∈ S.J j ⊔ P := hXT' hxX
          obtain ⟨a, haJ, b, hbP, hab⟩ := Subgroup.mem_sup.mp hxmem
          have haX' : a ∈ X' := by
            refine ⟨?_, haJ⟩
            have haeq : a = (x : W) * b⁻¹ := by
              rw [← hab]; group
            rw [haeq]
            exact Subgroup.mul_mem_sup hxX (P.inv_mem hbP)
          have ha1 : a ≠ 1 := by
            intro ha
            have hxP : (x : W) ∈ P := by
              rw [← hab, ha, one_mul]
              exact hbP
            have : (x : W) ∈ X ⊓ P := ⟨hxX, hxP⟩
            rw [hXP, Subgroup.mem_bot] at this
            exact hxW1 this
          intro hbot
          exact ha1 ((Subgroup.mem_bot).mp (hbot ▸ haX'))
        have hfixle : S.J j ⊓ fixV L ≤ X' :=
          s16h_e3_l3_fixV_le_of_inv hW (S.J_nat j) (S.J_comm j) (S.J_fix_rk j) hX'J hX'inv hX'ne
        have hneF : S.J j ⊓ fixV L ≠ ⊥ := by
          intro h
          have h1 := (rk_eq_zero_iff hW).mpr h
          rw [S.J_fix_rk j] at h1
          exact Nat.one_ne_zero h1
        obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hneF
        have hzX' : z.1 ∈ X' := hfixle z.2
        have hzmem : z.1 ∈ (X ⊔ P) ⊓ S.J j := hX'def ▸ hzX'
        have hzXP : z.1 ∈ X ⊔ P := (Subgroup.mem_inf.mp hzmem).1
        have hzJ : z.1 ∈ S.J j := (Subgroup.mem_inf.mp hzmem).2
        obtain ⟨x, hxX, b, hbP, hxb⟩ := Subgroup.mem_sup.mp hzXP
        have hxfix : x ∈ fixV L := by
          rw [mem_fixV]
          intro l hl
          have hzfix : l z.1 = z.1 := (Subgroup.mem_inf.mp z.2).2 l hl
          have h1 : l x * l b = x * b := by
            rw [← map_mul, hxb]
            exact hzfix
          have h2 : l x * x⁻¹ = b * (l b)⁻¹ := by
            rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul]
            rw [mul_comm b x]
            exact h1
          have hmemX : l x * x⁻¹ ∈ X := X.mul_mem (hXinv l hl x hxX) (X.inv_mem hxX)
          have hmemP : b * (l b)⁻¹ ∈ P := P.mul_mem hbP (P.inv_mem (hPinv l hl b hbP))
          have hmemP' : l x * x⁻¹ ∈ P := by rw [h2]; exact hmemP
          have hmemXP : l x * x⁻¹ ∈ X ⊓ P := ⟨hmemX, hmemP'⟩
          rw [hXP, Subgroup.mem_bot] at hmemXP
          exact mul_inv_eq_one.mp hmemXP
        have hx1 : x ≠ 1 := by
          intro hx0
          have hzP : z.1 ∈ P := by
            rw [← hxb, hx0, one_mul]
            exact hbP
          have : z.1 ∈ S.J j ⊓ P := ⟨hzJ, hzP⟩
          rw [hJP, Subgroup.mem_bot] at this
          exact hz1 (Subtype.ext this)
        intro h
        have : x ∈ (⊥ : Subgroup W) := h ▸ ⟨hxX, hxfix⟩
        rw [Subgroup.mem_bot] at this
        exact hx1 this
      · have hle : X ⊓ P ≤ P := inf_le_right
        have hinv : ∀ l ∈ L, ∀ x ∈ X ⊓ P, l x ∈ X ⊓ P :=
          s16h_e3_l3_inf_inv hXinv hPinv
        have hres := ih (X ⊓ P) hle hinv hXP
        intro h
        have h2 : (X ⊓ P) ⊓ fixV L ≤ ⊥ := by
          rw [← h]
          exact inf_le_inf inf_le_left le_rfl
        exact hres (le_bot_iff.mp h2)
  exact main T X hXT hXinv hX

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
