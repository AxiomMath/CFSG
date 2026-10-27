module

public import CFSG.LargeExtraspecial.DWRed

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.S127.L715

open CFSG.LargeExtraspecial Module QuadraticMap CFSG.RankThree.Literature.FSmith

variable {G : Type*} [Group G] [Finite G] (S : Setting G)

theorem exists_invariant_compl (T : Subgroup S.M) (hT : ¬ 2 ∣ T.index)
    {W₁ E : Submodule (ZMod 2) S.Qt} (hc : IsCompl W₁ E)
    (hW₁ : ∀ m : S.M, ∀ w ∈ W₁, ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W₁)
    (hE : ∀ t ∈ T, ∀ e ∈ E, ((S.ρ t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) e ∈ E) :
    ∃ W₂ : Submodule (ZMod 2) S.Qt, IsCompl W₁ W₂ ∧
      ∀ m : S.M, ∀ w ∈ W₂, ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W₂ := by
  classical
  let ρ : S.M → (S.Qt →ₗ[ZMod 2] S.Qt) :=
    fun m => ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap
  have hρmul : ∀ a b : S.M, ∀ v, ρ (a * b) v = ρ a (ρ b v) := fun a b v => by
    simp only [ρ, map_mul, Subgroup.coe_mul, LinearEquiv.coe_toLinearMap, LinearEquiv.mul_apply]
  have hρone : ∀ v, ρ 1 v = v := fun v => by
    simp only [ρ, map_one, OneMemClass.coe_one, LinearEquiv.coe_toLinearMap]
    rfl
  have hρinv : ∀ a : S.M, ∀ v, ρ a (ρ a⁻¹ v) = v := fun a v => by
    rw [← hρmul, mul_inv_cancel, hρone]
  have hρinv' : ∀ a : S.M, ∀ v, ρ a⁻¹ (ρ a v) = v := fun a v => by
    rw [← hρmul, inv_mul_cancel, hρone]
  have hW₁' : ∀ m : S.M, ∀ w ∈ W₁, ρ m w ∈ W₁ := hW₁
  have hE' : ∀ t ∈ T, ∀ e ∈ E, ρ t e ∈ E := hE
  set π : S.Qt →ₗ[ZMod 2] S.Qt := W₁.projection E hc with hπ
  have hπmem : ∀ v, π v ∈ W₁ := fun v => Submodule.projection_apply_mem hc v
  have hπW : ∀ w ∈ W₁, π w = w := fun w hw => Submodule.projection_apply_of_mem_left hc hw
  have hπE : ∀ e ∈ E, π e = 0 := fun e he => (Submodule.projection_apply_eq_zero_iff hc).mpr he
  have hsub : ∀ v, v - π v ∈ E := fun v => Submodule.sub_projection_mem hc v
  have hπT : ∀ t ∈ T, ∀ v, π (ρ t v) = ρ t (π v) := by
    intro t ht v
    have h1 : ρ t (π v) ∈ W₁ := hW₁' t _ (hπmem v)
    have h2 : ρ t (v - π v) ∈ E := hE' t ht _ (hsub v)
    have e : ρ t v = ρ t (π v) + ρ t (v - π v) := by rw [← map_add, add_sub_cancel]
    rw [e, map_add, hπW _ h1, hπE _ h2, add_zero]
  let f₀ : S.M → (S.Qt →ₗ[ZMod 2] S.Qt) := fun g => ρ g ∘ₗ π ∘ₗ ρ g⁻¹
  have hf₀ : ∀ a b : S.M, a⁻¹ * b ∈ T → f₀ a = f₀ b := by
    intro a b hab
    ext v
    show ρ a (π (ρ a⁻¹ v)) = ρ b (π (ρ b⁻¹ v))
    obtain ⟨t, ht, rfl⟩ : ∃ t ∈ T, b = a * t := ⟨a⁻¹ * b, hab, by group⟩
    rw [mul_inv_rev, hρmul t⁻¹ a⁻¹, hρmul a t, ← hπT t ht, hρinv]
  let f : S.M ⧸ T → (S.Qt →ₗ[ZMod 2] S.Qt) :=
    Quotient.lift f₀ fun a b h => hf₀ a b (QuotientGroup.leftRel_apply.mp h)
  have hf : ∀ g : S.M, f (QuotientGroup.mk g) = f₀ g := fun _ => rfl
  let _ : Fintype (S.M ⧸ T) := Fintype.ofFinite _
  set P : S.Qt →ₗ[ZMod 2] S.Qt := ∑ c : S.M ⧸ T, f c with hP
  have hPapply : ∀ v, P v = ∑ c : S.M ⧸ T, f c v := fun v => by
    rw [hP, LinearMap.sum_apply]
  have hPmem : ∀ v, P v ∈ W₁ := by
    intro v
    rw [hPapply]
    refine Submodule.sum_mem _ fun c _ => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    rw [hf]
    exact hW₁' g _ (hπmem _)
  have hPW : ∀ w ∈ W₁, P w = w := by
    intro w hw
    have hterm : ∀ c : S.M ⧸ T, f c w = w := by
      intro c
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
      rw [hf]
      show ρ g (π (ρ g⁻¹ w)) = w
      rw [hπW _ (hW₁' g⁻¹ w hw), hρinv]
    rw [hPapply, Finset.sum_congr rfl fun c _ => hterm c, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul (ZMod 2)]
    have hodd : (Fintype.card (S.M ⧸ T) : ZMod 2) = 1 := by
      rw [← Nat.card_eq_fintype_card, ← Subgroup.index, ← ZMod.natCast_mod,
        Nat.two_dvd_ne_zero.mp hT, Nat.cast_one]
    rw [hodd, one_smul]
  have hPρ : ∀ h : S.M, ∀ v, P (ρ h v) = ρ h (P v) := by
    intro h v
    rw [hPapply, hPapply, map_sum]
    have hterm : ∀ c : S.M ⧸ T, ρ h (f c v) = f (h • c) (ρ h v) := by
      intro c
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
      rw [MulAction.Quotient.smul_mk, hf, hf]
      show ρ h (ρ g (π (ρ g⁻¹ v))) = ρ (h * g) (π (ρ (h * g)⁻¹ (ρ h v)))
      rw [mul_inv_rev, hρmul g⁻¹ h⁻¹, hρinv' h v, hρmul]
    rw [Finset.sum_congr rfl fun c _ => hterm c]
    exact (Fintype.sum_equiv (MulAction.toPerm h) _ _ fun _ => rfl).symm
  let P' : S.Qt →ₗ[ZMod 2] ↥W₁ := P.codRestrict W₁ hPmem
  have hP' : ∀ x : ↥W₁, P' x = x := fun x => Subtype.ext (hPW x x.2)
  refine ⟨LinearMap.ker P', LinearMap.isCompl_of_proj hP', fun m w hw => ?_⟩
  rw [LinearMap.mem_ker] at hw ⊢
  have hw' : P w = 0 := congrArg Subtype.val hw
  refine Subtype.ext ?_
  show P (ρ m w) = 0
  rw [hPρ, hw', map_zero]

theorem exists_singular_compl (hw : S.width = 3) {A Y : Submodule (ZMod 2) S.Qt} {v : S.Qt}
    (hA : ∀ a ∈ A, S.q a = 0) (hA3 : finrank (ZMod 2) A = 3) (hYA : Y ≤ A)
    (hY2 : finrank (ZMod 2) Y = 2) (hvA : v ∈ A) (hvY : v ∉ Y) :
    ∃ e ∈ LinearMap.BilinForm.orthogonal S.q.polarBilin Y, S.q e = 0 ∧ polar S.q e v = 1 ∧
      ∀ e' ∈ LinearMap.BilinForm.orthogonal S.q.polarBilin Y, S.q e' = 0 →
        polar S.q e' v = 1 → e' - e ∈ Y := by
  classical
  have hdim : finrank (ZMod 2) S.Qt = 6 := by rw [S.finrank_Qt_eq_two_mul_width, hw]
  have hpol : ∀ a ∈ A, ∀ b ∈ A, polar S.q a b = 0 := by
    intro a ha b hb
    rw [polar, hA _ (A.add_mem ha hb), hA a ha, hA b hb]
    simp
  have hsymm : ∀ a b : S.Qt, polar S.q a b = polar S.q b a := fun a b => polar_comm S.q a b
  set Yp := LinearMap.BilinForm.orthogonal S.q.polarBilin Y with hYp
  have hmemYp : ∀ x, x ∈ Yp ↔ ∀ y ∈ Y, polar S.q y x = 0 := fun x => DW.mem_perp
  have hYv : Disjoint Y (Submodule.span (ZMod 2) {v}) := by
    rw [Submodule.disjoint_span_singleton]
    exact fun h => absurd h hvY
  have hAeq : A = Y ⊔ Submodule.span (ZMod 2) {v} := by
    have hle : Y ⊔ Submodule.span (ZMod 2) {v} ≤ A :=
      sup_le hYA ((Submodule.span_singleton_le_iff_mem v A).mpr hvA)
    have hv0 : v ≠ 0 := fun h => hvY (h ▸ Y.zero_mem)
    have hfin := Submodule.finrank_sup_add_finrank_inf_eq Y (Submodule.span (ZMod 2) {v})
    rw [hYv.eq_bot, finrank_bot, add_zero, finrank_span_singleton hv0, hY2] at hfin
    exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hfin, hA3])).symm
  have hAperp : ∀ x, (∀ a ∈ A, polar S.q a x = 0) → x ∈ A := by
    intro x hx
    have hle : A ≤ LinearMap.BilinForm.orthogonal S.q.polarBilin A := fun a ha =>
      DW.mem_perp.mpr fun b hb => hpol b hb a ha
    have hf := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate A
    have heq : LinearMap.BilinForm.orthogonal S.q.polarBilin A = A :=
      (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm
    have : x ∈ LinearMap.BilinForm.orthogonal S.q.polarBilin A := DW.mem_perp.mpr hx
    rwa [heq] at this
  have hmemA : ∀ x ∈ Yp, polar S.q x v = 0 → x ∈ A := by
    intro x hx hxv
    refine hAperp x fun a ha => ?_
    rw [hAeq] at ha
    obtain ⟨y, hy, w, hw', rfl⟩ := Submodule.mem_sup.mp ha
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw'
    rw [polar_add_left, polar_smul_left, (hmemYp x).mp hx y hy, hsymm v x, hxv, smul_zero,
      add_zero]
  obtain ⟨e₀, he₀, he₀v⟩ : ∃ e₀ ∈ Yp, polar S.q e₀ v = 1 := by
    by_contra hno
    push Not at hno
    have hle : Yp ≤ A := fun x hx => hmemA x hx (by
      rcases zmod2_cases (polar S.q x v) with h | h
      · exact h
      · exact absurd h (hno x hx))
    have hf := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate Y
    have h2 := Submodule.finrank_mono hle
    rw [← hYp] at hf
    omega
  have hvYp : v ∈ Yp := (hmemYp v).mpr fun y hy => hpol y (hYA hy) v hvA
  have hqv : S.q v = 0 := hA v hvA
  have hvv : polar S.q v v = 0 := by
    rw [polar_self, hqv, smul_zero]
  obtain ⟨e, he, heq, hev⟩ : ∃ e ∈ Yp, S.q e = 0 ∧ polar S.q e v = 1 := by
    rcases zmod2_cases (S.q e₀) with h | h
    · exact ⟨e₀, he₀, h, he₀v⟩
    · refine ⟨e₀ + v, Yp.add_mem he₀ hvYp, ?_, ?_⟩
      · rw [show S.q (e₀ + v) = S.q e₀ + S.q v + polar S.q e₀ v by rw [polar]; ring, h, hqv,
          he₀v]
        decide
      · rw [polar_add_left, he₀v, hvv, add_zero]
  refine ⟨e, he, heq, hev, fun e' he' he'q he'v => ?_⟩
  have hd : e' - e ∈ A := hmemA _ (Yp.sub_mem he' he) (by rw [polar_sub_left, he'v, hev, sub_self])
  rw [hAeq] at hd
  obtain ⟨y, hy, w, hw', hyw⟩ := Submodule.mem_sup.mp hd
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw'
  have he'eq : e' = e + y + c • v := by rw [add_assoc, hyw]; abel
  have hq : S.q e' = c := by
    rw [he'eq]
    have h1 : S.q (e + y + c • v) = S.q (e + y) + S.q (c • v) + polar S.q (e + y) (c • v) := by
      rw [polar]; ring
    have h2 : S.q (e + y) = S.q e + S.q y + polar S.q e y := by rw [polar]; ring
    rw [h1, h2, heq, hA y (hYA hy), QuadraticMap.map_smul, hqv, polar_add_left, polar_smul_right,
      polar_smul_right, hev, hsymm e y, (hmemYp e).mp he y hy, hpol y (hYA hy) v hvA]
    simp
  rw [he'q] at hq
  rw [← hq, zero_smul, add_zero] at hyw
  rw [← hyw]
  exact hy

end CFSG.Quasithin.H13.S127.L715
