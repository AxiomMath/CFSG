module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TSStdBase
public import CFSG.Quasithin.Vol2.GoldschmidtF431TSLocK

public section

namespace CFSG.Quasithin.H13.F431.Lift

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin.H13.F431.NF
open scoped commutatorElement

section Two

structure StdTwo (C : Type) [Group C] (U P P' : Subgroup C) (z t : C) : Prop where
  z_mem : z ∈ U
  t_mem : t ∈ U
  z_two : orderOf z = 2
  t_two : orderOf t = 2
  cls : ∀ x : C, orderOf x = 2 → IsConj z x ∨ IsConj t x
  noconj : ∀ φ : MulAut C, φ z ≠ t
  center : ∀ w ∈ U, (∀ y ∈ U, y * w = w * y) → w ≠ 1 → ∃ h ∈ P ⊓ P', h * z * h⁻¹ = w
  aut_z : ∀ φ : MulAut C, φ ∈ autStab P → φ ∈ autStab P' →
    ∃ b ∈ P ⊓ P', φ z = b * z * b⁻¹
  aut_t : ∀ φ : MulAut C, φ ∈ autStab P → φ ∈ autStab P' →
    ∃ b ∈ P ⊓ P', φ t = b * t * b⁻¹
  cent_z : Subgroup.centralizer ({z} : Set C) ≤ P ∨ Subgroup.centralizer ({z} : Set C) ≤ P'
  cent_t : Subgroup.centralizer ({t} : Set C) ≤ P ∨ Subgroup.centralizer ({t} : Set C) ≤ P'

variable {D C : Type} [Group D] [Group C] (A : LieAmalgamExt D) (ε : D ≃* C)

theorem inf_iff_of_orient {Q Q' : Subgroup D}
    (hQ : (Q = A.P1 ∧ Q' = A.P2) ∨ (Q = A.P2 ∧ Q' = A.P1)) (x : D) :
    x ∈ A.P1 ⊓ A.P2 ↔ x ∈ Q ∧ x ∈ Q' := by
  rcases hQ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Iff.rfl
  · exact and_comm

theorem stab_of_orient {Q Q' : Subgroup D}
    (hQ : (Q = A.P1 ∧ Q' = A.P2) ∨ (Q = A.P2 ∧ Q' = A.P1)) {φ : MulAut D}
    (h : φ ∈ A.N1 ⊓ A.N2) : φ ∈ autStab Q ∧ φ ∈ autStab Q' := by
  rcases hQ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨h.1.2, h.2.2⟩
  · exact ⟨h.2.2, h.1.2⟩

theorem twoClassD_of_std {U P P' : Subgroup C} {z t : C} (S : StdTwo C U P P' z t)
    {Q Q' : Subgroup D} (hQ : (Q = A.P1 ∧ Q' = A.P2) ∨ (Q = A.P2 ∧ Q' = A.P1))
    (hQP : Q.map ε.toMonoidHom = P) (hQP' : Q'.map ε.toMonoidHom = P')
    (hU : A.TD.map ε.toMonoidHom = U) : TwoClassD A (ε.symm z) (ε.symm t) := by
  have hmemU : ∀ {w : C}, w ∈ U → ε.symm w ∈ A.TD := fun {w} hw =>
    (mem_symm_iff_of_map_eq ε hU).mpr hw
  have hmemU' : ∀ {w : D}, w ∈ A.TD → ε w ∈ U := fun {w} hw => (mem_iff_of_map_eq ε hU).mpr hw
  have hinf : ∀ {h : C}, h ∈ P ⊓ P' → ε.symm h ∈ A.P1 ⊓ A.P2 := fun {h} hh =>
    (inf_iff_of_orient A hQ _).mpr ⟨(mem_symm_iff_of_map_eq ε hQP).mpr hh.1,
      (mem_symm_iff_of_map_eq ε hQP').mpr hh.2⟩
  have hinf' : ∀ {x : D}, x ∈ A.P1 ⊓ A.P2 → ε x ∈ P ⊓ P' := fun {x} hx =>
    ⟨(mem_iff_of_map_eq ε hQP).mpr ((inf_iff_of_orient A hQ x).mp hx).1,
      (mem_iff_of_map_eq ε hQP').mpr ((inf_iff_of_orient A hQ x).mp hx).2⟩
  have hstab : ∀ {φ : MulAut D}, φ ∈ A.N1 ⊓ A.N2 →
      MulAut.congr ε φ ∈ autStab P ∧ MulAut.congr ε φ ∈ autStab P' := fun {φ} h =>
    ⟨congr_mem_autStab ε hQP (stab_of_orient A hQ h).1,
      congr_mem_autStab ε hQP' (stab_of_orient A hQ h).2⟩
  have hcongr : ∀ (φ : MulAut D) (x : D), (MulAut.congr ε φ) (ε x) = ε (φ x) := fun φ x => by
    simp [MulAut.congr_apply]
  refine ⟨hmemU S.z_mem, hmemU S.t_mem, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq, S.z_two]
  · rw [MulEquiv.orderOf_eq, S.t_two]
  · intro x hx
    have h2 : orderOf (ε x) = 2 := by rw [MulEquiv.orderOf_eq]; exact hx
    rcases S.cls (ε x) h2 with h | h
    · left
      have := ε.symm.toMonoidHom.map_isConj h
      simpa using this
    · right
      have := ε.symm.toMonoidHom.map_isConj h
      simpa using this
  · intro φ hφ
    apply S.noconj (MulAut.congr ε φ)
    have := congrArg ε hφ
    rw [← hcongr, MulEquiv.apply_symm_apply] at this
    simpa using this
  · intro w hw hc hw1
    obtain ⟨h, hh, hhw⟩ := S.center (ε w) (hmemU' hw) (fun y hy => by
      have hy' := hmemU hy
      have := hc _ hy'
      apply ε.symm.injective
      simpa using this) (fun h => hw1 (ε.injective (by rw [h, map_one])))
    refine ⟨ε.symm h, hinf hh, ε.injective ?_⟩
    simp [hhw]
  · intro φ hφ
    obtain ⟨b, hb, hbz⟩ := S.aut_z _ (hstab hφ).1 (hstab hφ).2
    refine ⟨ε.symm b, hinf hb, ε.injective ?_⟩
    have := hbz
    rw [← MulEquiv.apply_symm_apply ε z, hcongr] at this
    simpa [map_mul, map_inv] using this
  · intro φ hφ
    obtain ⟨b, hb, hbt⟩ := S.aut_t _ (hstab hφ).1 (hstab hφ).2
    refine ⟨ε.symm b, hinf hb, ε.injective ?_⟩
    have := hbt
    rw [← MulEquiv.apply_symm_apply ε t, hcongr] at this
    simpa [map_mul, map_inv] using this
  · have key : ∀ (w : C) (R : Subgroup D) (R' : Subgroup C), R.map ε.toMonoidHom = R' →
        Subgroup.centralizer ({w} : Set C) ≤ R' → Subgroup.centralizer ({ε.symm w} : Set D) ≤ R :=
      fun w R R' hR hc d hd => by
        have h1 : ε d ∈ Subgroup.centralizer ({w} : Set C) := by
          have := (map_centralizer_singleton ε (ε.symm w))
          rw [MulEquiv.apply_symm_apply] at this
          rw [← this]
          exact Subgroup.mem_map_of_mem _ hd
        exact (mem_iff_of_map_eq ε hR).mp (hc h1)
    rcases S.cent_z with h | h
    · exact ⟨Q, hQ.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1), key z Q P hQP h⟩
    · exact ⟨Q', hQ.elim (fun h => Or.inr h.2) (fun h => Or.inl h.2), key z Q' P' hQP' h⟩
  · have key : ∀ (w : C) (R : Subgroup D) (R' : Subgroup C), R.map ε.toMonoidHom = R' →
        Subgroup.centralizer ({w} : Set C) ≤ R' → Subgroup.centralizer ({ε.symm w} : Set D) ≤ R :=
      fun w R R' hR hc d hd => by
        have h1 : ε d ∈ Subgroup.centralizer ({w} : Set C) := by
          have := (map_centralizer_singleton ε (ε.symm w))
          rw [MulEquiv.apply_symm_apply] at this
          rw [← this]
          exact Subgroup.mem_map_of_mem _ hd
        exact (mem_iff_of_map_eq ε hR).mp (hc h1)
    rcases S.cent_t with h | h
    · exact ⟨Q, hQ.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1), key t Q P hQP h⟩
    · exact ⟨Q', hQ.elim (fun h => Or.inr h.2) (fun h => Or.inl h.2), key t Q' P' hQP' h⟩

end Two

section Loc

structure StdLoc (C : Type) [Group C] (U : Subgroup C) (z t : C) (V L : Subgroup C) : Prop where
  comm : z * t = t * z
  sylow_t : IsSylowTwoOf (U ⊓ Subgroup.centralizer ({t} : Set C))
    (Subgroup.centralizer ({t} : Set C))
  V_le : V ≤ Subgroup.centralizer ({t} : Set C)
  V_ab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a
  V_two : ∀ a ∈ V, a ^ 2 = 1
  V_ne : V ≠ ⊥
  V_aut : ∀ φ : MulAut C, φ t = t → ∀ v ∈ V, φ v ∈ V
  V_z : ∀ v ∈ V, v ≠ 1 → ∃ x ∈ Subgroup.centralizer ({t} : Set C), v = x * z * x⁻¹
  L_le : L ≤ Subgroup.centralizer ({t} : Set C)
  L_ns : ¬ Group.IsSolvable ↥L
  L_V : Group.IsSolvable ↥(L ⊓ Subgroup.centralizer (V : Set C))

variable {D C : Type} [Group D] [Group C] (A : LieAmalgamExt D) (ε : D ≃* C)

theorem locD_of_std {U : Subgroup C} {z t : C} {V L : Subgroup C} (S : StdLoc C U z t V L)
    (hU : A.TD.map ε.toMonoidHom = U) :
    LocD A (ε.symm z) (ε.symm t) (V.map ε.symm.toMonoidHom) (L.map ε.symm.toMonoidHom) := by
  have hTD : A.TD = U.map ε.symm.toMonoidHom := (map_symm_eq_of_map_eq ε hU).symm
  have hcent : (Subgroup.centralizer ({t} : Set C)).map ε.symm.toMonoidHom =
      Subgroup.centralizer ({ε.symm t} : Set D) := map_centralizer_singleton ε.symm t
  have hcongr : ∀ (φ : MulAut D) (x : C), (MulAut.congr ε φ) x = ε (φ (ε.symm x)) := fun φ x => by
    simp [MulAut.congr_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, S.comm]
  · have := isSylowTwoOf_map_inj ε.symm.toMonoidHom ε.symm.injective S.sylow_t
    rwa [Subgroup.map_inf _ _ _ ε.symm.injective, ← hTD, hcent] at this
  · rw [← hcent]
    exact Subgroup.map_mono S.V_le
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul, S.V_ab a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_pow, S.V_two a ha, map_one]
  · intro h
    apply S.V_ne
    rw [eq_bot_iff]
    intro v hv
    have : ε.symm v ∈ V.map ε.symm.toMonoidHom := ⟨v, hv, rfl⟩
    rw [h] at this
    have := Subgroup.mem_bot.mp this
    rw [Subgroup.mem_bot]
    exact ε.symm.injective (this.trans (map_one _).symm)
  · rintro φ _ hφ _ ⟨v, hv, rfl⟩
    refine ⟨(MulAut.congr ε φ) v, S.V_aut _ ?_ v hv, ?_⟩
    · show (MulAut.congr ε φ) t = t
      rw [hcongr, hφ, MulEquiv.apply_symm_apply]
    · show ε.symm ((MulAut.congr ε φ) v) = φ (ε.symm v)
      rw [hcongr, MulEquiv.symm_apply_apply]
  · rintro _ ⟨v, hv, rfl⟩ hv1
    obtain ⟨x, hx, hxv⟩ := S.V_z v hv (fun h => hv1 (by rw [MulEquiv.coe_toMonoidHom, h, map_one]))
    refine ⟨ε.symm x, ?_, ?_⟩
    · rw [← hcent]
      exact ⟨x, hx, rfl⟩
    · rw [MulEquiv.coe_toMonoidHom, hxv, map_mul, map_mul, map_inv]
  · rw [← hcent]
    exact Subgroup.map_mono S.L_le
  · exact not_solvable_map_equiv ε.symm S.L_ns
  · rw [map_inf_centralizer_equiv ε.symm]
    exact solvable_map_equiv ε.symm S.L_V

end Loc
end CFSG.Quasithin.H13.F431.Lift
