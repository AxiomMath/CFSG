module

public import CFSG.Quasithin.Background.F918P0
public import CFSG.Quasithin.Background.D2Misc

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section OrbSup

variable {W : Type} [CommGroup W] {T : Subgroup (MulAut W)} {V : Subgroup W}

theorem map_le_orbSup {t : MulAut W} (ht : t ∈ T) : V.map t.toMonoidHom ≤ orbSup T V :=
  le_iSup₂_of_le t ht le_rfl

theorem le_orbSup (T : Subgroup (MulAut W)) (V : Subgroup W) : V ≤ orbSup T V := by
  intro v hv
  exact map_le_orbSup (V := V) T.one_mem ⟨v, hv, rfl⟩

theorem map_orbSup_le {t : MulAut W} (ht : t ∈ T) :
    (orbSup T V).map t.toMonoidHom ≤ orbSup T V := by
  simp only [orbSup, Subgroup.map_iSup]
  refine iSup_le fun s => iSup_le fun hs => ?_
  rw [Subgroup.map_map]
  exact le_iSup₂_of_le (t * s) (T.mul_mem ht hs) le_rfl

theorem orbSup_le {U : Subgroup W} (h : ∀ t ∈ T, V.map t.toMonoidHom ≤ U) : orbSup T V ≤ U :=
  iSup₂_le h

theorem mem_orbSup_of_mem_map {t : MulAut W} (ht : t ∈ T) {u : W} (hu : u ∈ orbSup T V) :
    t u ∈ orbSup T V :=
  map_orbSup_le ht ⟨u, hu, rfl⟩

theorem le_stabSub_orbSup (T : Subgroup (MulAut W)) (V : Subgroup W) : T ≤ stabSub (orbSup T V) := by
  intro t ht u
  refine ⟨fun h => ?_, fun h => mem_orbSup_of_mem_map ht h⟩
  have := mem_orbSup_of_mem_map (T.inv_mem ht) h
  simpa using this

theorem orbSup_eq_of_stab (h : ∀ t ∈ T, t ∈ stabSub V) : orbSup T V = V := by
  refine le_antisymm (orbSup_le fun t ht => ?_) (le_orbSup T V)
  rintro _ ⟨v, hv, rfl⟩
  exact (h t ht v).2 hv

theorem stab_of_orbSup_eq (h : orbSup T V = V) : ∀ t ∈ T, t ∈ stabSub V := by
  intro t ht
  rw [← h]
  exact le_stabSub_orbSup T V ht

end OrbSup

section SumMod

variable {W : Type} [CommGroup W]

theorem isSumMod_top_of_isIntDirect {Mp : Subgroup (MulAut W)} {A B : Subgroup W}
    (hA : ∀ x ∈ Mp, ∀ a ∈ A, x a ∈ A) (hB : ∀ x ∈ Mp, ∀ b ∈ B, x b ∈ B)
    (h : IsIntDirect A B ⊤) : IsSumMod (fixV Mp) A B ⊤ := by
  refine ⟨?_, ?_⟩
  · rw [h.1]
    exact (top_sup_eq _).symm
  · intro w ⟨hw1, hw2⟩
    obtain ⟨a, ha, c₁, hc₁, rfl⟩ := Subgroup.mem_sup.mp hw1
    obtain ⟨b, hb, c₂, hc₂, hab⟩ := Subgroup.mem_sup.mp hw2
    have hab' : a * c₁ = b * c₂ := hab.symm
    have hfix : ∀ x ∈ Mp, x a = a := by
      intro x hx
      have e1 : x a * c₁ = x b * c₂ := by
        have := congrArg x hab'
        rwa [map_mul, map_mul, hc₁ x hx, hc₂ x hx] at this
      have h2 : x a / a = x b / b := by
        have : (x a * c₁) / (a * c₁) = (x b * c₂) / (b * c₂) := by rw [e1, hab']
        rwa [mul_div_mul_right_eq_div, mul_div_mul_right_eq_div] at this
      have h3 : x a / a ∈ A ⊓ B :=
        ⟨A.div_mem (hA x hx a ha) ha, h2 ▸ B.div_mem (hB x hx b hb) hb⟩
      rw [h.2, Subgroup.mem_bot, div_eq_one] at h3
      exact h3
    exact (fixV Mp).mul_mem (fun x hx => hfix x hx) hc₁

end SumMod

section Offender

variable {W : Type} [CommGroup W]

theorem rAV_autSub_le_of_faithful [Finite W] (hexp : ∀ w : W, w ^ 2 = 1)
    {A : Subgroup (MulAut W)} {U : Subgroup W} (hA : A ≤ stabSub U) (hf : A ⊓ centSub U = ⊥) :
    rAV (autSub A U) ≤ rAV A := by
  unfold rAV
  have h1 : rk (autSub A U) = rk A := rk_autSub_eq_of_faithful hA hf
  have h2 : rkIdx (fixV (autSub A U)) ≤ rkIdx (fixV A) := by
    have := (rkIdx_add_le hexp hA).1
    have h3 : rkIdx (fixV (A ⊓ centSub U)) = 0 := by
      rw [hf]
      have : fixV (⊥ : Subgroup (MulAut W)) = ⊤ := by
        ext w
        simp [mem_fixV]
      rw [this]
      simp [rkIdx]
    omega
  rw [h1]
  exact div_le_div_of_nonneg_right (by exact_mod_cast h2) (by positivity)

structure QOff (Mp T A : Subgroup (MulAut W)) (VT : Subgroup W) : Prop where
  le : A ≤ T
  ne : A ≠ ⊥
  elem : IsElemAbelian2 A
  quad : commSeries A 2 = ⊥
  rat : rAV A ≤ 2
  faithMp : ∀ a ∈ A, (∀ x ∈ Mp, a * x = x * a) → a = 1
  faithVT : A ⊓ centSub VT = ⊥

variable [Finite W] {Mp T A : Subgroup (MulAut W)}

theorem QOff.qhat_M {VT : Subgroup W} {M : Subgroup (MulAut W)} (hA : QOff Mp T A VT)
    (hTM : T ≤ M) : qhatOf M ≤ ((2 : ℚ) : WithTop ℚ) :=
  kq_le_iff.mpr ⟨A, ⟨hA.le.trans hTM, hA.ne, hA.elem⟩,
    commSeries_eq_bot_of_le (by norm_num) hA.quad, hA.rat⟩

theorem QOff.qhat_VT (hexp : ∀ w : W, w ^ 2 = 1) {V : Subgroup W}
    (hA : QOff Mp T A (orbSup T V)) :
    qhatOf (autSub (Mp ⊔ T) (orbSup T V)) ≤ ((2 : ℚ) : WithTop ℚ) := by
  have hAst : A ≤ stabSub (orbSup T V) := hA.le.trans (le_stabSub_orbSup T V)
  have hA2 : IsA2 (Mp ⊔ T) A := ⟨hA.le.trans le_sup_right, hA.ne, hA.elem⟩
  have hU : commSub (orbSup T V) A ≠ ⊥ := by
    intro h
    rw [commSub_eq_bot_iff] at h
    apply hA.ne
    rw [eq_bot_iff, ← hA.faithVT]
    exact le_inf le_rfl (fun a ha u hu => h hu a ha)
  exact kq_le_iff.mpr ⟨autSub A (orbSup T V), IsA2.autSub hA2 hAst hU,
    commSeries_autSub_eq_bot hAst (commSeries_eq_bot_of_le (by norm_num) hA.quad),
    (rAV_autSub_le_of_faithful hexp hAst hA.faithVT).trans hA.rat⟩

theorem QOff.qOf_VT (hexp : ∀ w : W, w ^ 2 = 1) {V : Subgroup W}
    (hA : QOff Mp T A (orbSup T V)) :
    qOf (autSub (Mp ⊔ T) (orbSup T V)) ≤ ((2 : ℚ) : WithTop ℚ) := by
  have hAst : A ≤ stabSub (orbSup T V) := hA.le.trans (le_stabSub_orbSup T V)
  have hA2 : IsA2 (Mp ⊔ T) A := ⟨hA.le.trans le_sup_right, hA.ne, hA.elem⟩
  have hU : commSub (orbSup T V) A ≠ ⊥ := by
    intro h
    rw [commSub_eq_bot_iff] at h
    apply hA.ne
    rw [eq_bot_iff, ← hA.faithVT]
    exact le_inf le_rfl (fun a ha u hu => h hu a ha)
  exact kq_le_iff.mpr ⟨autSub A (orbSup T V), IsA2.autSub hA2 hAst hU,
    commSeries_autSub_eq_bot hAst hA.quad,
    (rAV_autSub_le_of_faithful hexp hAst hA.faithVT).trans hA.rat⟩

end Offender

section ShapeCongr

variable {X Y : Type} [Group X] [Group Y]

theorem isPSL_congr {n p e : ℕ} (φ : X ≃* Y) (h : IsPSL n p e X) : IsPSL n p e Y := by
  obtain ⟨hadm, K, x, hfin, hK, ⟨e'⟩⟩ := h
  exact ⟨hadm, K, x, hfin, hK, ⟨φ.symm.trans e'⟩⟩

theorem isPSU_congr {n p e : ℕ} (φ : X ≃* Y) (h : IsPSU n p e X) : IsPSU n p e Y := by
  obtain ⟨hadm, K, x, hfin, hK, ⟨e'⟩⟩ := h
  exact ⟨hadm, K, x, hfin, hK, ⟨φ.symm.trans e'⟩⟩

theorem isPSp4_congr {p e : ℕ} (φ : X ≃* Y) (h : IsPSp4 p e X) : IsPSp4 p e Y := by
  obtain ⟨hadm, K, x, hfin, hK, ⟨e'⟩⟩ := h
  exact ⟨hadm, K, x, hfin, hK, ⟨φ.symm.trans e'⟩⟩

theorem isSz_congr {e : ℕ} (φ : X ≃* Y) (h : IsSz e X) : IsSz e Y := by
  obtain ⟨h2, a, ha, K, x, hfin, hfa, hK, ⟨e'⟩⟩ := h
  exact ⟨h2, a, ha, K, x, hfin, hfa, hK, ⟨φ.symm.trans e'⟩⟩

theorem isAlt_congr {n : ℕ} (φ : X ≃* Y) (h : IsAlt n X) : IsAlt n Y := by
  obtain ⟨e'⟩ := h
  exact ⟨φ.symm.trans e'⟩

theorem isSporadic_congr {s : TauCeti.SporadicName} (φ : X ≃* Y) (h : IsSporadic s X) :
    IsSporadic s Y := by
  obtain ⟨e'⟩ := h
  exact ⟨φ.symm.trans e'⟩

theorem a38Types_congr (φ : X ≃* Y) (h : A38Types X) : A38Types Y := by
  rcases h with ⟨n, h⟩ | ⟨n, h⟩ | h | ⟨p, hp, h3, h⟩
  · exact Or.inl ⟨n, isPSL_congr φ h⟩
  · exact Or.inr (Or.inl ⟨n, isSz_congr φ h⟩)
  · exact Or.inr (Or.inr (Or.inl (isSporadic_congr φ h)))
  · exact Or.inr (Or.inr (Or.inr ⟨p, hp, h3, isPSL_congr φ h⟩))

end ShapeCongr

end CFSG.Quasithin
