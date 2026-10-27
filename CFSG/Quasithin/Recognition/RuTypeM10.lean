module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16FactsA6Model
public import CFSG.LieType.SteinbergBRAutGL32
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms

public section

namespace CFSG.Quasithin.RuType

open CFSG.QuasithinUnique

section Extension

variable {X : Type*} [Group X] [Finite X] (N : Subgroup X) [N.Normal]

omit [Finite X] in
theorem conjNormal_injective (hN2 : N.index = 2) (hinv : ∀ x : X, x ^ 2 = 1 → x ∈ N)
    (hZ : ∀ n ∈ N, (∀ m ∈ N, n * m = m * n) → n = 1) :
    Function.Injective (MulAut.conjNormal : X →* MulAut N) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hc : ∀ m ∈ N, x * m = m * x := by
    intro m hm
    have h := congrArg (fun f : MulAut N => ((f ⟨m, hm⟩ : N) : X)) hx
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
    calc x * m = x * m * x⁻¹ * x := by group
      _ = m * x := by rw [h]
  rw [Subgroup.mem_bot]
  by_cases hxN : x ∈ N
  · exact hZ x hxN (fun m hm => hc m hm)
  · exfalso
    apply hxN
    apply hinv
    have hx2 : x ^ 2 ∈ N := by rw [pow_two]; exact Subgroup.mul_self_mem_of_index_two hN2 x
    refine hZ _ hx2 fun m hm => ?_
    calc x ^ 2 * m = x * (x * m) := by rw [pow_two, mul_assoc]
      _ = x * (m * x) := by rw [hc m hm]
      _ = (x * m) * x := by rw [mul_assoc]
      _ = (m * x) * x := by rw [hc m hm]
      _ = m * x ^ 2 := by rw [pow_two, mul_assoc]

omit [Finite X] [N.Normal] in
theorem card_eq_two_mul (hN2 : N.index = 2) : Nat.card X = 2 * Nat.card N := by
  rw [← Subgroup.card_mul_index N, hN2, mul_comm]

@[expose] def pglInv : Equiv.Perm (Fin 10) := A6Models.tMul * A6Models.tInv

theorem pglInv_mem : pglInv ∈ A6Models.pgl29 :=
  mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

theorem pglInv_sq : pglInv * pglInv = 1 := by decide +kernel

theorem pglInv_not_mem_psl29 : pglInv ∉ A6Models.psl29 := by
  rw [A6Facts.mem_psl29_iff]
  have : A6Facts.Core.pslLit.contains (A6Facts.code pglInv) = false := by decide +kernel
  simpa [List.contains_eq_any_beq] using this

theorem tFrob_sq : A6Models.tFrob * A6Models.tFrob = 1 := by decide +kernel

omit [Finite X] in
theorem nonempty_mulEquiv_m10 (hN2 : N.index = 2) (hinv : ∀ x : X, x ^ 2 = 1 → x ∈ N)
    (e : N ≃* alternatingGroup (Fin 6)) : Nonempty (X ≃* A6Models.m10) := by
  classical
  have hZ : ∀ n ∈ N, (∀ m ∈ N, n * m = m * n) → n = 1 := by
    intro n hn hc
    have hcen : e ⟨n, hn⟩ ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨m, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hc m m.2).symm
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot,
      map_eq_one_iff _ e.injective] at hcen
    exact congrArg Subtype.val hcen
  obtain ⟨-, ψ, -, -⟩ := Unc25K1.A6Model.exists_pslEquiv
  set φ : N ≃* A6Models.psl29 := e.trans ψ.symm with hφ
  set Θ := Unc25K1.A6Model.thetaEquiv φ with hΘ
  let ι : X →* A6Models.autA6 := Θ.toMonoidHom.comp MulAut.conjNormal
  have hι : Function.Injective ι := Θ.injective.comp (conjNormal_injective N hN2 hinv hZ)
  have hιN : ∀ n : N, ((ι n : A6Models.autA6) : Equiv.Perm (Fin 10)) =
      ((φ n : A6Models.psl29) : Equiv.Perm (Fin 10)) := by
    intro n
    have h := Unc25K1.A6Model.thetaEquiv_eq φ (MulAut.conjNormal (n : X))
      ⟨φ n, A6Facts.psl29_le_autA6 (φ n).2⟩ (fun k => by
        have hk : (MulAut.conjNormal (n : X)) k = n * k * n⁻¹ :=
          Subtype.ext (by rw [MulAut.conjNormal_apply]; rfl)
        rw [hk, map_mul, map_mul, map_inv]
        rfl)
    exact congrArg Subtype.val h
  let Bm : Subgroup (Equiv.Perm (Fin 10)) := ι.range.map A6Models.autA6.subtype
  have hBA : Bm ≤ A6Models.autA6 := fun x hx => by
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  have hmem : ∀ x : X, ((ι x : A6Models.autA6) : Equiv.Perm (Fin 10)) ∈ Bm :=
    fun x => ⟨ι x, ⟨x, rfl⟩, rfl⟩
  have hpsl : A6Models.psl29 ≤ Bm := by
    intro p hp
    have h := hmem (φ.symm ⟨p, hp⟩ : X)
    rw [hιN, MulEquiv.apply_symm_apply] at h
    exact h
  have hcardB : Nat.card Bm = 720 := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective,
      ← Nat.card_congr (MonoidHom.ofInjective hι).toEquiv, card_eq_two_mul N hN2,
      Nat.card_congr e.toEquiv, Unc25K1.A6Model.card_alt6]
  have hBinv : ∀ σ ∈ Bm, σ * σ = 1 → σ ∈ A6Models.psl29 := by
    rintro σ ⟨y, ⟨x, rfl⟩, rfl⟩ hσ
    have hx2 : x ^ 2 = 1 := by
      apply hι
      rw [map_pow, map_one, pow_two]
      exact Subtype.ext hσ
    have hxN := hinv x hx2
    have h := hιN ⟨x, hxN⟩
    show ((ι x : A6Models.autA6) : Equiv.Perm (Fin 10)) ∈ A6Models.psl29
    rw [show ((ι x : A6Models.autA6) : Equiv.Perm (Fin 10)) =
      ((φ ⟨x, hxN⟩ : A6Models.psl29) : Equiv.Perm (Fin 10)) from h]
    exact (φ _).2
  have hnot : ∃ σ ∈ Bm, σ ∉ A6Facts.s6 := by
    by_contra hall
    push Not at hall
    have hlt : ∃ x ∈ Bm, x ∉ A6Models.psl29 := by
      by_contra h
      push Not at h
      have := Subgroup.card_le_of_le h
      rw [hcardB, A6Facts.card_psl29] at this
      omega
    obtain ⟨x, hxB, hxp⟩ := hlt
    obtain ⟨r, hr, hxr⟩ := (A6Facts.mem_s6_iff_exists x).1 (hall x hxB)
    simp only [A6Facts.s6RepsP, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hxp (by simpa using hxr)
    · have hF : A6Models.tFrob ∈ Bm := by
        have e1 : A6Models.tFrob = (x * A6Models.tFrob⁻¹)⁻¹ * x := by group
        rw [e1]
        exact mul_mem (inv_mem (hpsl hxr)) hxB
      exact A6Facts.tFrob_not_mem_psl (hBinv _ hF tFrob_sq)
  rcases Unc25K1.A6Model.classify Bm hBA hpsl hnot with h | h | h
  · exact absurd (hBinv _ (h ▸ pglInv_mem) pglInv_sq) pglInv_not_mem_psl29
  · exact ⟨((MonoidHom.ofInjective hι).trans
      (Subgroup.equivMapOfInjective ι.range A6Models.autA6.subtype
        Subtype.val_injective)).trans (MulEquiv.subgroupCongr h)⟩
  · exfalso
    have := hcardB
    rw [h, A6Facts.card_autA6] at this
    omega

omit [Finite X] in
theorem false_of_psl32 (hN2 : N.index = 2) (hinv : ∀ x : X, x ^ 2 = 1 → x ∈ N)
    (e : N ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) : False := by
  classical
  let e₂ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq
      CFSG.LocalAnalysis.ComponentInitial.center_SL_three_zmod_two_eq_bot).trans
      QuotientGroup.quotientBot
  let e₃ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃* Setup.Family.GL32 :=
    MulEquiv.ofBijective _ CFSG.LocalAnalysis.ComponentInitial.bijective_toGL_three_zmod_two
  let f : N ≃* Setup.Family.GL32 := (e.trans e₂).trans e₃
  have hZ : ∀ n ∈ N, (∀ m ∈ N, n * m = m * n) → n = 1 := by
    intro n hn hc
    have hcen : f ⟨n, hn⟩ ∈ Subgroup.center Setup.Family.GL32 := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨m, rfl⟩ := f.surjective g
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hc m m.2).symm
    rw [Setup.Family.center_GL32, Subgroup.mem_bot, map_eq_one_iff _ f.injective] at hcen
    exact congrArg Subtype.val hcen
  let ι : X →* MulAut Setup.Family.GL32 := (MulAut.congr f).toMonoidHom.comp MulAut.conjNormal
  have hι : Function.Injective ι :=
    (MulAut.congr f).injective.comp (conjNormal_injective N hN2 hinv hZ)
  have : Finite (MulAut Setup.Family.GL32) := by
    have := Nat.card_pos_iff.mp (by
      rw [CFSG.LieType.SteinbergBR.AutGL32.card_mulAut_GL32]; norm_num :
        0 < Nat.card (MulAut Setup.Family.GL32))
    exact this.2
  have hbij : Function.Bijective ι := hι.bijective_of_nat_card_le (by
    rw [CFSG.LieType.SteinbergBR.AutGL32.card_mulAut_GL32, card_eq_two_mul N hN2,
      Nat.card_congr f.toEquiv, CFSG.LieType.SteinbergBR.AutGL32.card_GL32])
  obtain ⟨x, hx⟩ := hbij.2 CFSG.LieType.SteinbergBR.AutGL32.tau
  have hx2 : x ^ 2 = 1 := by
    apply hι
    rw [map_pow, hx, map_one, pow_two]
    exact CFSG.LieType.SteinbergBR.AutGL32.tau_mul_tau
  have hxN := hinv x hx2
  apply CFSG.LieType.SteinbergBR.AutGL32.tau_not_mem_inner
  refine ⟨f ⟨x, hxN⟩, ?_⟩
  rw [← hx]
  ext g : 1
  obtain ⟨m, rfl⟩ := f.surjective g
  rw [MulAut.conj_apply]
  show _ = f ((MulAut.conjNormal x) (f.symm (f m)))
  rw [MulEquiv.symm_apply_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1

end Extension

end CFSG.Quasithin.RuType
