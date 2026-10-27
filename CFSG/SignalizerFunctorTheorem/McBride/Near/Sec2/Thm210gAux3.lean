module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210gAux2
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210a

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

open Thm210 Thm210g

variable {Γ : Type*} [Group Γ] {p : ℕ} {A G J : Subgroup Γ}

theorem Thm210g.admits_inf_centralizer {Q Y B : Subgroup Γ} (hQY : Admits Q Y)
    (hQB : Q ≤ Subgroup.centralizer (B : Set Γ)) :
    Admits Q (Y ⊓ Subgroup.centralizer (B : Set Γ)) := by
  refine Thm210.le_normalizer_of_conj_mem fun c hc x hx => ?_
  obtain ⟨hxY, hxB⟩ := Subgroup.mem_inf.1 hx
  exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hQY hc) x).1 hxY,
    mul_mem (mul_mem (hQB hc) hxB) (inv_mem (hQB hc))⟩

theorem Thm210g.admits_inf {Q X Y : Subgroup Γ} (hQX : Admits Q X) (hQY : Admits Q Y) :
    Admits Q (X ⊓ Y) := by
  refine Thm210.le_normalizer_of_conj_mem fun c hc x hx => ?_
  obtain ⟨hxX, hxY⟩ := Subgroup.mem_inf.1 hx
  exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hQX hc) x).1 hxX,
    (Subgroup.mem_normalizer_iff.1 (hQY hc) x).1 hxY⟩

theorem Thm210g.coord_conj_of_normalizer [Finite Γ] {S : Set (Subgroup Γ)} {L : Subgroup Γ}
    (hL : IsDirectProduct S L) {a : Γ} (ha : ∀ K ∈ S, K.map (MulAut.conj a).toMonoidHom ∈ S)
    {J : Subgroup Γ} (hJ : J ∈ S) (haJ : a ∈ Subgroup.normalizer (J : Set Γ)) (z : L) :
    ((hL.coord hJ ⟨a * z * a⁻¹, hL.conj_mem ha z.2⟩ : J) : Γ) =
      a * ((hL.coord hJ z : J) : Γ) * a⁻¹ := by
  have h1 := hL.coord_conj ha hJ z.2
  have hJn : J.map (MulAut.conj a).toMonoidHom = J := Subgroup.mem_normalizer_iff_map_conj_eq.1 haJ
  exact (hL.coord_val_congr (ha J hJ) hJ hJn ⟨a * z * a⁻¹, hL.conj_mem ha z.2⟩).symm.trans h1

section Finite

variable [Finite Γ]

theorem Thm210g.p_le_card
    (h : SemisimpleAction p A G) (hJ : J ∈ lcal G) :
    p ≤ Nat.card A := by
  obtain ⟨a₀, f, ha₀, hfx, hord, -, -⟩ := h.exists_frame hJ
  have hf1 : f ≠ 1 := by
    intro hf
    rw [hf, orderOf_one] at hord
    exact h.prime.ne_one hord.symm
  have ha₀A : a₀ ∈ A := (Thm210.mem_norIn_iff.1 ha₀).1
  have ha₀1 : a₀ ≠ 1 := by
    rintro rfl
    refine hf1 (MulEquiv.ext fun x => Subtype.ext ?_)
    rw [hfx]
    simp
  have := Fact.mk h.prime
  have hord' : orderOf a₀ = p := orderOf_eq_prime (h.elemAbelian.2 a₀ ha₀A) ha₀1
  rw [← hord']
  exact Nat.le_of_dvd Nat.card_pos (Subgroup.orderOf_dvd_natCard A ha₀A)

omit [Finite Γ] in
theorem Thm210g.coprime_card (h : SemisimpleAction p A G) {Y : Subgroup Γ} (hYG : Y ≤ G) :
    Nat.Coprime p (Nat.card Y) :=
  (signalizerNearPSolvable_iff.1 h.nearPSolvable).1.coprime_dvd_right
    (Subgroup.card_dvd_of_le hYG)

omit [Finite Γ] in
theorem Thm210g.commute_of_mem (h : SemisimpleAction p A G) {x y : Γ} (hx : x ∈ A)
    (hy : y ∈ A) : Commute x y := by
  have := h.elemAbelian.1
  exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : A) ⟨y, hy⟩)

omit [Finite Γ] in
theorem Thm210g.le_centralizer_of_le (h : SemisimpleAction p A G) {B : Subgroup Γ}
    (hBA : B ≤ A) : A ≤ Subgroup.centralizer (B : Set Γ) := by
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact (Thm210g.commute_of_mem h (hBA hb) ha).eq

omit [Finite Γ] in
theorem Thm210g.cenIn_le_centralizer_of_le (G : Subgroup Γ) {A B : Subgroup Γ} (hBA : B ≤ A) :
    cenIn G A ≤ Subgroup.centralizer (B : Set Γ) :=
  inf_le_right.trans (Subgroup.centralizer_le hBA)

theorem SemisimpleAction.inf_smear_ne_bot
    (h : SemisimpleAction p A G) (hJ : J ∈ lcal G)
    {Y : Subgroup Γ} (hYG₁ : Y ≤ orbitClosure J A) (hYA : Admits A Y)
    (hYD : Admits (cenIn G A) Y) (hYn : ¬ Y ≤ fProd A G) : Y ⊓ smear J A ≠ ⊥ := by
  have hp := h.prime
  have hYG : Y ≤ G := hYG₁.trans (orbitClosure_le_group h hJ)
  obtain ⟨B, hB, hBn⟩ := exists_hyperplane_not_le hp h.elemAbelian (p_le_card h hJ) hYA
    (coprime_card h hYG) hYn
  have hAB := le_centralizer_of_le h hB.1
  have hDB := cenIn_le_centralizer_of_le G hB.1
  have hZA : Admits A (Y ⊓ Subgroup.centralizer (B : Set Γ)) := admits_inf_centralizer hYA hAB
  have hZ : Admits (cenIn G A ⊔ A) (Y ⊓ Subgroup.centralizer (B : Set Γ)) :=
    sup_le (admits_inf_centralizer hYD hDB) hZA
  have hZnil : ¬ Group.IsNilpotent ↥(Y ⊓ Subgroup.centralizer (B : Set Γ)) := fun hnil => hBn (by
    have := thm210f h (inf_le_left.trans hYG) hZ hnil
    rwa [h.mOf_eq_kProd, h.fittingSubgroupOf_kProd] at this)
  have hne := inf_centralizer_ne_bot_of_hyperplane hp h.elemAbelian hB hZA inf_le_right hZnil
  intro hbot
  apply hne
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨⟨hzY, -⟩, hzA⟩ := Subgroup.mem_inf.1 hz
  have : z ∈ Y ⊓ smear J A := Subgroup.mem_inf.2 ⟨hzY, Subgroup.mem_inf.2 ⟨hYG₁ hzY, hzA⟩⟩
  rwa [hbot] at this

theorem SemisimpleAction.eq_one_of_coord_eq_one (h : SemisimpleAction p A G) (hJ : J ∈ lcal G)
    {B E : Subgroup Γ} (hBA : B ≤ A) (hEN : E ≤ Subgroup.normalizer (J : Set Γ))
    (hAeq : B ⊔ E = A) (y : ↥G) (hyG₁ : (y : Γ) ∈ orbitClosure J A)
    (hyB : (y : Γ) ∈ Subgroup.centralizer (B : Set Γ))
    (hy : h.isDirectProduct_lcal.coord hJ y = 1) : (y : Γ) = 1 := by
  have hG := h.isDirectProduct_lcal
  have hEA : E ≤ A := le_sup_right.trans hAeq.le
  have h1 : y = 1 := by
    refine hG.ext_coord fun K hK => ?_
    rw [map_one]
    by_cases hKo : K ∈ orbSet A J
    · obtain ⟨a, haA, rfl⟩ := hKo
      rw [← hAeq] at haA
      obtain ⟨b, hb, e, he, rfl⟩ := (mem_sup_iff_of_commute
        fun x hx z hz => Thm210g.commute_of_mem h (hBA hx) (hEA hz)).1 haA
      have hJe : J.map (MulAut.conj e).toMonoidHom = J :=
        Subgroup.mem_normalizer_iff_map_conj_eq.1 (hEN he)
      have hKb : J.map (MulAut.conj (b * e)).toMonoidHom = J.map (MulAut.conj b).toMonoidHom := by
        rw [← map_conj_map_conj J e b, hJe]
      have hperm : ∀ K ∈ lcal G, K.map (MulAut.conj b).toMonoidHom ∈ lcal G :=
        fun K hK => h.permutes_lcal b (hBA hb) K hK
      have hbyb : b * (y : Γ) * b⁻¹ = y := by
        rw [Subgroup.mem_centralizer_iff.1 hyB b hb]
        group
      have e1 : (⟨b * (y : Γ) * b⁻¹, hG.conj_mem hperm y.2⟩ : ↥G) = y := Subtype.ext hbyb
      have key := hG.coord_conj hperm hJ y.2
      rw [e1] at key
      have hy' : hG.coord hJ ⟨(y : Γ), y.2⟩ = 1 := hy
      have hc : ((hG.coord (hperm J hJ) y : J.map (MulAut.conj b).toMonoidHom) : Γ) = 1 := by
        rw [key, hy']
        simp
      exact Subtype.ext ((hG.coord_val_congr (h.permutes_lcal (b * e) (mul_mem (hBA hb)
        (hEA he)) J hJ) (hperm J hJ) hKb y).trans hc)
    · have hsub : orbSet A J ⊆ lcal G \ {K} := fun K' hK' =>
        ⟨orbSet_subset_lcal h hJ hK', fun heq => hKo (Set.mem_singleton_iff.1 heq ▸ hK')⟩
      have hyK : (y : Γ) ∈ sSup (lcal G \ {K}) := by
        have := sSup_le_sSup hsub
        rw [sSup_orbSet] at this
        exact this hyG₁
      exact (hG.coord_eq_one_iff hK y).2 hyK
  exact congrArg Subtype.val h1

theorem SemisimpleAction.smear_le_of_projIn_eq
    (h : SemisimpleAction p A G) (hJ : J ∈ lcal G)
    {Y : Subgroup Γ} (hYG₁ : Y ≤ orbitClosure J A) (hYA : Admits A Y)
    (hYD : Admits (cenIn G A) Y) (hPJ : projIn (lcal G) J Y = J) : smear J A ≤ Y := by
  have hp := h.prime
  have hG := h.isDirectProduct_lcal
  have hYG : Y ≤ G := hYG₁.trans (orbitClosure_le_group h hJ)
  have hJs : IsSimpleGroup ↥J := (mem_lcal_iff.1 hJ).2.2.1
  obtain ⟨B, hB, hBJ⟩ : ∃ B ∈ Coprime.hyperplanes p A,
      projIn (lcal G) J (Y ⊓ Subgroup.centralizer (B : Set Γ)) = J := by
    by_contra hcon
    push Not at hcon
    have hle : ∀ B ∈ Coprime.hyperplanes p A,
        projIn (lcal G) J (Y ⊓ Subgroup.centralizer (B : Set Γ)) ≤ kJ A J := by
      intro B hB
      have hZD : Admits (cenIn G A) (Y ⊓ Subgroup.centralizer (B : Set Γ)) :=
        admits_inf_centralizer hYD (cenIn_le_centralizer_of_le G hB.1)
      have hCZ : cenIn J (norIn A J) ≤ Subgroup.normalizer
          (projIn (lcal G) J (Y ⊓ Subgroup.centralizer (B : Set Γ)) : Set Γ) := by
        rw [← h.projIn_cenIn hJ]
        exact Thm210.le_normalizer_of_conj_mem (projIn_conj_mem hG hJ fun d hd z hz =>
          (Subgroup.mem_normalizer_iff.1 (hZD hd) z).1 hz)
      rcases h.le_kJ_or_le_normalizer hJ (projIn_le J _) hCZ Subgroup.le_normalizer with h1 | h1
      · exact h1
      · rcases eq_bot_or_eq_of_le_normalizer hJs (projIn_le J _) h1 with h2 | h2
        · rw [h2]
          exact bot_le
        · exact absurd h2 (hcon B hB)
    have hsup := iSup_centralizer_hyperplanes hp h.elemAbelian (p_le_card h hJ) hYA
      (coprime_card h hYG)
    have hall : projIn (lcal G) J (⨆ B ∈ Coprime.hyperplanes p A,
        Y ⊓ Subgroup.centralizer (B : Set Γ)) ≤ kJ A J := by
      refine projIn_iSup_le hG hJ _ (fun B => iSup_le fun _ => inf_le_left.trans hYG) fun B => ?_
      exact projIn_iSup_le hG hJ _ (fun _ => inf_le_left.trans hYG) fun hB' => hle B hB'
    rw [hsup, hPJ] at hall
    exact h.kJ_ne hJ (le_antisymm (kJ_le A J) hall)
  obtain ⟨a₀, f, ha₀, hfx, hord, -, -⟩ := h.exists_frame hJ
  have ha₀A : a₀ ∈ A := (Thm210.mem_norIn_iff.1 ha₀).1
  have ha₀J : a₀ ∈ Subgroup.normalizer (J : Set Γ) := (Thm210.mem_norIn_iff.1 ha₀).2
  have hf1 : f ≠ 1 := by
    intro hf
    rw [hf, orderOf_one] at hord
    exact hp.ne_one hord.symm
  have hperm₀ : ∀ K ∈ lcal G, K.map (MulAut.conj a₀).toMonoidHom ∈ lcal G :=
    fun K hK => h.permutes_lcal a₀ ha₀A K hK
  have ha₀B : a₀ ∉ B := by
    intro ha₀B
    apply hf1
    refine MulEquiv.ext fun x => Subtype.ext ?_
    have hx : (x : Γ) ∈ projIn (lcal G) J (Y ⊓ Subgroup.centralizer (B : Set Γ)) := by
      rw [hBJ]
      exact x.2
    obtain ⟨z, hz, hzx⟩ := (hG.mem_projIn_iff hJ).1 hx
    have hzC := (Subgroup.mem_inf.1 hz).2
    have hza : a₀ * (z : Γ) * a₀⁻¹ = z := by
      rw [Subgroup.mem_centralizer_iff.1 hzC a₀ ha₀B]
      group
    have e1 : (⟨a₀ * (z : Γ) * a₀⁻¹, hG.conj_mem hperm₀ z.2⟩ : ↥G) = z := Subtype.ext hza
    have key := coord_conj_of_normalizer hG hperm₀ hJ ha₀J z
    rw [e1, hzx] at key
    rw [hfx]
    exact key.symm
  have hAeq : B ⊔ Subgroup.zpowers a₀ = A :=
    sup_eq_of_mem_hyperplanes hp hB (Subgroup.zpowers_le.2 ha₀A) fun hle =>
      ha₀B (hle (Subgroup.mem_zpowers a₀))
  have hEN : Subgroup.zpowers a₀ ≤ Subgroup.normalizer (J : Set Γ) :=
    Subgroup.zpowers_le.2 ha₀J
  have hfull : orbitClosure J A ⊓ Subgroup.centralizer (B : Set Γ) ≤ Y := by
    intro z hz
    obtain ⟨hzG₁, hzB⟩ := Subgroup.mem_inf.1 hz
    have hzG : z ∈ G := orbitClosure_le_group h hJ hzG₁
    have hx : ((hG.coord hJ ⟨z, hzG⟩ : J) : Γ) ∈
        projIn (lcal G) J (Y ⊓ Subgroup.centralizer (B : Set Γ)) := by
      rw [hBJ]
      exact (hG.coord hJ ⟨z, hzG⟩).2
    obtain ⟨y, hy, hyz⟩ := (hG.mem_projIn_iff hJ).1 hx
    obtain ⟨hyY, hyB⟩ := Subgroup.mem_inf.1 hy
    have hw := h.eq_one_of_coord_eq_one hJ hB.1 hEN hAeq (y⁻¹ * ⟨z, hzG⟩)
      (mul_mem (inv_mem (hYG₁ hyY)) hzG₁) (mul_mem (inv_mem hyB) hzB) (by
        rw [map_mul, map_inv, Subtype.ext hyz]
        exact inv_mul_cancel _)
    have hzy : z = y := by
      have : (y : Γ)⁻¹ * z = 1 := hw
      rw [inv_mul_eq_one] at this
      exact this.symm
    exact hzy ▸ hyY
  intro z hz
  obtain ⟨hzG₁, hzA⟩ := Subgroup.mem_inf.1 hz
  exact hfull (Subgroup.mem_inf.2 ⟨hzG₁, Subgroup.centralizer_le hB.1 hzA⟩)

end Finite

end CFSG.SignalizerFunctorTheorem.McBride.Near
