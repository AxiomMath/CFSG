module

public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
import CFSG.ClassicalInvolution.RouteD.TWYType
import CFSG.LieType.SeitzGeneration.OrthNonsplitTools
import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Generic
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BSClTwo
import CFSG.RankThree.OddKernel.SectionRep
import CFSG.RankThree.PartOne.K159.RowFourType
import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusFourExtract

public section

namespace CFSG.GGQ2Prime

open Module CFSG.Open CFSG.RankThree.Classical2 CFSG.RankThree.OddKernel

namespace OmegaMinusTwelve

private theorem even_of_two_pow_modEq_one {d : ℕ} (h : 2 ^ d ≡ 1 [MOD 3]) : Even d := by
  rcases Nat.even_or_odd d with he | ⟨j, rfl⟩
  · exact he
  · exfalso
    have h4 : 4 ^ j ≡ 1 [MOD 3] := by
      simpa using Nat.ModEq.pow j (show 4 ≡ 1 [MOD 3] by decide)
    have h2 : 2 ^ (2 * j + 1) ≡ 2 [MOD 3] := by
      calc 2 ^ (2 * j + 1) = 4 ^ j * 2 := by rw [pow_succ, pow_mul]; norm_num
        _ ≡ 1 * 2 [MOD 3] := h4.mul_right 2
        _ = 2 := one_mul 2
    exact absurd (h2.symm.trans h) (by decide)

private theorem card_linearEquiv_of_card_two {F M : Type*} [Field F] [Finite F] [AddCommGroup M]
    [Module F M] [FiniteDimensional F M] (hF : Nat.card F = 2) :
    Nat.card (M ≃ₗ[F] M) = ∏ i : Fin (finrank F M), (2 ^ finrank F M - 2 ^ (i : ℕ)) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  let b : Module.Basis (Fin (finrank F M)) F M := Module.finBasisOfFinrankEq F M rfl
  let e : GL (Fin (finrank F M)) F ≃* (M ≃ₗ[F] M) :=
    (Matrix.GeneralLinearGroup.toLin' b).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv F M)
  rw [← Nat.card_congr e.toEquiv, Matrix.card_GL_field, ← Nat.card_eq_fintype_card, hF]

private theorem not_dvd_card_GL_two {n : ℕ} (hn : n ≤ 6) :
    ¬ 3 ^ 5 ∣ ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) := by
  interval_cases n <;> simp [Fin.prod_univ_succ]

private theorem eq_one_of_chain {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (hF : (2 : F) = 0)
    {g : V ≃ₗ[F] V} (hg : g ^ 3 = 1) {U₁ U₂ : Submodule F V} (h₁ : ∀ v ∈ U₁, g v = v)
    (h₂ : ∀ v ∈ U₂, g v - v ∈ U₁) (h₃ : ∀ v, g v - v ∈ U₂) : g = 1 := by
  have h2 : ∀ x : V, x + x = 0 := fun x => by rw [← two_smul F x, hF, zero_smul]
  have hneg : ∀ x : V, -x = x := fun x => by rw [neg_eq_iff_add_eq_zero, h2]
  have hg3 : ∀ v, g (g (g v)) = v := fun v => by
    have h := LinearEquiv.congr_fun hg v
    simpa [pow_succ, LinearEquiv.mul_apply] using h
  have hfix2 : ∀ a, g (g a) = a → g a = a := fun a ha => by
    have := hg3 a
    rw [ha] at this
    exact this
  have hstep : ∀ a, g (g a - a) = g a - a → g a = a := fun a ha => by
    apply hfix2
    rw [map_sub] at ha
    have : g (g a) = g a + (g a - a) := by rw [← ha]; abel
    rw [this, ← add_sub_assoc, h2, zero_sub, hneg]
  refine LinearEquiv.ext fun v => ?_
  have ha := h₃ v
  have hb := h₂ _ ha
  have hc := h₁ _ hb
  exact hstep v (hstep _ hc)

section Gen

private def fixSp
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (x : V ≃ₗ[F] V) : Submodule F V := LinearMap.ker (x.toLinearMap - LinearMap.id)

private def triSp
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (x : V ≃ₗ[F] V) : Submodule F V :=
  LinearMap.ker (x.toLinearMap ∘ₗ x.toLinearMap + x.toLinearMap + LinearMap.id)

private theorem mem_fixSp
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {x : V ≃ₗ[F] V} {v : V} : v ∈ fixSp x ↔ x v = v := by
  rw [fixSp, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  rfl

private theorem mem_triSp
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {x : V ≃ₗ[F] V} {v : V} : v ∈ triSp x ↔ x (x v) + x v + v = 0 := by
  rw [triSp, LinearMap.mem_ker]
  rfl

private theorem apply_three
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {x : V ≃ₗ[F] V} (hx : x ^ 3 = 1) (v : V) : x (x (x v)) = v := by
  have h := congrArg (fun g : V ≃ₗ[F] V => g v) hx
  simpa only [pow_three, LinearEquiv.mul_apply, LinearEquiv.coe_one, id_eq] using h

private theorem fixed_pi
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {x : V ≃ₗ[F] V} (hx : x ^ 3 = 1) (v : V) :
    x (x (x v) + x v + v) = x (x v) + x v + v := by
  rw [map_add, map_add, apply_three hx]
  abel

private theorem apply_mem_fixSp
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {x y : V ≃ₗ[F] V} (hxy : y * x = x * y) {v : V} (hv : v ∈ fixSp x) :
    y v ∈ fixSp x := by
  rw [mem_fixSp] at hv ⊢
  have h := LinearEquiv.congr_fun hxy v
  simp only [LinearEquiv.mul_apply] at h
  rw [← h, hv]

private theorem apply_mem_triSp
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {x y : V ≃ₗ[F] V} (hxy : y * x = x * y) {v : V} (hv : v ∈ triSp x) :
    y v ∈ triSp x := by
  rw [mem_triSp] at hv ⊢
  have h : ∀ u, y (x u) = x (y u) := fun u => by
    have := LinearEquiv.congr_fun hxy u
    simpa only [LinearEquiv.mul_apply] using this
  rw [← h v, ← h (x v), ← map_add, ← map_add, hv, map_zero]

private theorem polarNondegOn_left
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {Q : QuadraticForm F V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {A B : Submodule F V} (hc : IsCompl A B)
    (horth : ∀ a ∈ A, ∀ b ∈ B, QuadraticMap.polar Q a b = 0) :
    CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q A := by
  intro a ha h
  refine hQ.1 a fun v => ?_
  obtain ⟨p, hp, u, hu, rfl⟩ :=
    Submodule.mem_sup.mp (hc.codisjoint.eq_top ▸ Submodule.mem_top : v ∈ A ⊔ B)
  rw [map_add, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply,
    h p hp, horth a ha u hu, add_zero]

private theorem polarNondegOn_right
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {Q : QuadraticForm F V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {A B : Submodule F V} (hc : IsCompl A B)
    (horth : ∀ a ∈ A, ∀ b ∈ B, QuadraticMap.polar Q a b = 0) :
    CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q B := by
  intro b hb h
  refine hQ.1 b fun v => ?_
  obtain ⟨p, hp, u, hu, rfl⟩ :=
    Submodule.mem_sup.mp (hc.codisjoint.eq_top ▸ Submodule.mem_top : v ∈ A ⊔ B)
  rw [map_add, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply,
    h u hu, QuadraticMap.polar_comm, horth p hp b hb, add_zero]

section CharTwo

private theorem vadd_self (F : Type*) {V : Type*} [Field F] [CharP F 2] [AddCommGroup V]
    [Module F V] (v : V) : v + v = 0 := by
  rw [← two_smul F v, CharTwo.two_eq_zero, zero_smul]

private theorem tri_rest
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [CharP F 2]
    {x : V ≃ₗ[F] V} (hx : x ^ 3 = 1) (v : V) :
    x (x (x (x v) + x v)) + x (x (x v) + x v) + (x (x v) + x v) = 0 := by
  have e : x (x (x (x v) + x v)) + x (x (x v) + x v) + (x (x v) + x v) =
      (x v + x v) + (v + v) + (x (x v) + x (x v)) := by
    simp only [map_add, apply_three hx]
    abel
  rw [e]
  simp only [vadd_self F]

private theorem decomp
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [CharP F 2]
    (x : V ≃ₗ[F] V) (v : V) : v = (x (x v) + x v + v) + (x (x v) + x v) := by
  have e : (x (x v) + x v + v) + (x (x v) + x v) = v + ((x (x v) + x (x v)) + (x v + x v)) := by
    abel
  rw [e]
  simp only [vadd_self F, add_zero]

private theorem isCompl_fixSp_triSp
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [CharP F 2]
    {x : V ≃ₗ[F] V} (hx : x ^ 3 = 1) : IsCompl (fixSp x) (triSp x) := by
  refine ⟨Submodule.disjoint_def.mpr fun v hvP hvU => ?_, ?_⟩
  · rw [mem_fixSp] at hvP
    rw [mem_triSp, hvP, hvP, vadd_self F, zero_add] at hvU
    exact hvU
  · refine codisjoint_iff.mpr (eq_top_iff.mpr fun v _ => Submodule.mem_sup.mpr ?_)
    exact ⟨_, mem_fixSp.mpr (fixed_pi hx v), _, mem_triSp.mpr (tri_rest hx v), (decomp x v).symm⟩

private theorem eq_zero_of_mem_triSp
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [CharP F 2]
    {x : V ≃ₗ[F] V} {v : V} (hv : v ∈ triSp x) (hxv : x v = v) :
    v = 0 := by
  rw [mem_triSp, hxv, hxv, vadd_self F, zero_add] at hv
  exact hv

private theorem polar_eq_zero_of_mem
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [CharP F 2]
    {Q : QuadraticForm F V} {x : V ≃ₗ[F] V}
    (hxQ : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {a b : V} (ha : a ∈ fixSp x)
    (hb : b ∈ triSp x) : QuadraticMap.polar Q a b = 0 := by
  rw [mem_fixSp] at ha
  rw [mem_triSp] at hb
  have h1 : QuadraticMap.polar Q a (x b) = QuadraticMap.polar Q a b := by
    have := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hxQ a b
    rwa [ha] at this
  have h2 : QuadraticMap.polar Q a (x (x b)) = QuadraticMap.polar Q a b := by
    have := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hxQ a (x b)
    rwa [ha, h1] at this
  have h0 := congrArg (QuadraticMap.polar Q a) hb
  rw [QuadraticMap.polar_add_right, QuadraticMap.polar_add_right, h1, h2,
    QuadraticMap.polar_zero_right, CharTwo.add_self_eq_zero, zero_add] at h0
  exact h0

private theorem triSp_le_triSp
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [CharP F 2]
    {x z : V ≃ₗ[F] V} (hz : z ^ 3 = 1) (hxz : x * z = z * x)
    (hxC : ∀ v, z v = v → x v = v) : triSp x ≤ triSp z := by
  intro v hv
  set π : V →ₗ[F] V := z.toLinearMap ∘ₗ z.toLinearMap + z.toLinearMap + LinearMap.id with hπ
  have hπapp : ∀ u, π u = z (z u) + z u + u := fun u => rfl
  have hcomm : ∀ u, x (z u) = z (x u) := fun u => by
    have := LinearEquiv.congr_fun hxz u
    simpa only [LinearEquiv.mul_apply] using this
  have hπx : ∀ u, π (x u) = π u := fun u => by
    rw [hπapp, hπapp, ← hcomm u, ← hcomm (z u), ← map_add, ← map_add]
    exact hxC _ (fixed_pi hz u)
  have h0 : π (x (x v) + x v + v) = 0 := by rw [mem_triSp.mp hv, map_zero]
  rw [map_add, map_add, hπx, hπx, vadd_self F, zero_add] at h0
  exact h0

end CharTwo

end Gen

section TwoField

private theorem even_finrank
    {F V : Type*} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hF : Nat.card F = 2) {z : V ≃ₗ[F] V} (hz : z ^ 3 = 1)
    {S : Submodule F V} (hS : ∀ v ∈ S, z v ∈ S) (hfix : ∀ v ∈ S, z v = v → v = 0) :
    Even (finrank F S) := by
  have hz3 : ∀ v, z (z (z v)) = v := fun v => by
    have h := LinearEquiv.congr_fun hz v
    simpa [pow_succ, LinearEquiv.mul_apply] using h
  have hmap : S.map (z : V →ₗ[F] V) = S := by
    refine le_antisymm ?_ fun v hv => ⟨z (z v), hS _ (hS _ hv), hz3 v⟩
    rintro _ ⟨v, hv, rfl⟩
    exact hS v hv
  let zS : S ≃ₗ[F] S := z.ofSubmodules S S hmap
  have hzS : zS ^ 3 = 1 := LinearEquiv.ext fun s => Subtype.ext (by
    simpa [pow_succ, LinearEquiv.mul_apply, zS] using hz3 s)
  let A := Subgroup.zpowers zS
  have hA : ∀ a : A, a ^ 3 = 1 := fun a => by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 a.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      hzS, one_zpow, Subgroup.coe_one]
  let ρ : Representation F A S := toRep A.subtype
  haveI : Finite S := Module.finite_of_finite F
  let _ : MulAction A S := MulAction.compHom S ρ
  have hp : IsPGroup 3 A := fun a => ⟨1, by simp [hA]⟩
  have hmod := hp.card_modEq_card_fixedPoints S
  haveI : Unique (MulAction.fixedPoints A S) := by
    refine ⟨⟨⟨0, fun a => map_zero (ρ a)⟩⟩, fun x => Subtype.ext ?_⟩
    have hx : zS x.1 = x.1 := x.2 ⟨zS, Subgroup.mem_zpowers zS⟩
    exact Subtype.ext (hfix _ x.1.2 (congrArg Subtype.val hx))
  have hfp : Nat.card (MulAction.fixedPoints A S) = 1 := Nat.card_unique
  rw [hfp, Module.natCard_eq_pow_finrank (K := F), hF] at hmod
  exact even_of_two_pow_modEq_one hmod

private theorem sub_mem_of_section
    {F V : Type*} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hF : Nat.card F = 2) {Y : Type*} [Group Y] [Finite Y]
    [IsSimpleGroup Y] (hY : 3 ^ 4 ∣ Nat.card Y) (α : Y →* (V ≃ₗ[F] V)) {z : V ≃ₗ[F] V}
    (hz : z ^ 3 = 1) (hzα : ∀ y, z * α y = α y * z)
    {U U' : Submodule F V} (hU : ∀ y, ∀ v ∈ U, α y v ∈ U) (hU' : ∀ y, ∀ v ∈ U', α y v ∈ U')
    (hzU : ∀ v ∈ U, z v ∈ U) (hzU' : ∀ v ∈ U', z v ∈ U') (hle : U ≤ U')
    (hfix : ∀ v ∈ U', z (z v) + z v + v ∈ U)
    (hdim : finrank F U' ≤ finrank F U + 6) (y : Y) {v : V} (hv : v ∈ U') : α y v - v ∈ U := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2F : (2 : F) = 0 := by
    letI : Fintype F := Fintype.ofFinite F
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP F 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hF])
    exact_mod_cast CharP.cast_eq_zero F 2
  have hmap : ∀ {g : V ≃ₗ[F] V} {S : Submodule F V}, (∀ v ∈ S, g v ∈ S) →
      S.map (g : V →ₗ[F] V) = S := fun {g S} h => by
    refine Submodule.eq_of_le_of_finrank_eq ?_ (LinearEquiv.finrank_map_eq g S)
    rintro _ ⟨w, hw, rfl⟩
    exact h w hw
  have hinv : ∀ {g : V ≃ₗ[F] V} {S : Submodule F V}, (∀ v ∈ S, g v ∈ S) →
      ∀ v ∈ S, g⁻¹ v ∈ S := fun {g S} h v hv => by
    have hv' : v ∈ S.map (g : V →ₗ[F] V) := (hmap h).symm ▸ hv
    obtain ⟨u, hu, rfl⟩ := hv'
    simpa using hu
  let H : Subgroup (V ≃ₗ[F] V) :=
    { carrier := {g | (∀ w ∈ U, g w ∈ U) ∧ ∀ w ∈ U', g w ∈ U'}
      one_mem' := ⟨fun w hw => hw, fun w hw => hw⟩
      mul_mem' := fun {a b} ha hb => ⟨fun w hw => ha.1 _ (hb.1 w hw),
        fun w hw => ha.2 _ (hb.2 w hw)⟩
      inv_mem' := fun {a} ha => ⟨hinv ha.1, hinv ha.2⟩ }
  have hmemU : ∀ h : H, ∀ w ∈ U, (h : V ≃ₗ[F] V) w ∈ U := fun h w hw => h.2.1 w hw
  have hmemU' : ∀ h : H, ∀ w ∈ U', (h : V ≃ₗ[F] V) w ∈ U' := fun h w hw => h.2.2 w hw
  have hαH : ∀ y, α y ∈ H := fun y => ⟨hU y, hU' y⟩
  have hzH : z ∈ H := ⟨hzU, hzU'⟩
  let σ := sectionRep H.subtype (fun h w hw => hmemU h w hw) (fun h w hw => hmemU' h w hw)
  let ρH := Representation.asGroupHom σ
  let αH : Y →* H := α.codRestrict H hαH
  let ρ : Y →* (Module.End F (U' ⧸ U.comap U'.subtype))ˣ := ρH.comp αH
  have hρ : ∀ y (w : U'), (((ρ y : (Module.End F (U' ⧸ U.comap U'.subtype))ˣ) :
      Module.End F (U' ⧸ U.comap U'.subtype)) (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk w ↔ α y w - w ∈ U) := fun y w =>
    sectionRep_mk_eq_mk_iff H.subtype _ _ (αH y) w
  by_cases htriv : ∀ y, ρ y = 1
  · exact (hρ y ⟨v, hv⟩).1 (by rw [htriv y]; rfl)
  exfalso
  push Not at htriv
  obtain ⟨y₀, hy₀⟩ := htriv
  have hker : ρ.ker = ⊥ :=
    (ρ.normal_ker.eq_bot_or_eq_top).resolve_right fun h =>
      hy₀ (h ▸ Subgroup.mem_top y₀ : y₀ ∈ ρ.ker)
  have hρinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).1 hker
  let zb := ρH ⟨z, hzH⟩
  have hzb3 : zb ^ 3 = 1 := by
    rw [← map_pow]
    convert map_one ρH
    exact Subtype.ext hz
  have hcomm : ∀ y, ρ y * zb = zb * ρ y := fun y => by
    change ρH (αH y) * ρH ⟨z, hzH⟩ = ρH ⟨z, hzH⟩ * ρH (αH y)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hzα y).symm
  have hzb1 : zb ≠ 1 := by
    intro h1
    have hsub : ∀ w ∈ U', w ∈ U := fun w hw => by
      have hfixb : ∀ x ∈ U', z x - x ∈ U := fun x hx => by
        have h' : σ ⟨z, hzH⟩ (Submodule.Quotient.mk ⟨x, hx⟩) = Submodule.Quotient.mk ⟨x, hx⟩ :=
          congrArg (fun u : (Module.End F (U' ⧸ U.comap U'.subtype))ˣ =>
            (u : Module.End F (U' ⧸ U.comap U'.subtype)) (Submodule.Quotient.mk ⟨x, hx⟩)) h1
        exact (sectionRep_mk_eq_mk_iff H.subtype _ _ ⟨z, hzH⟩ ⟨x, hx⟩).1 h'
      have h2' := hfixb (z w) (hzU' w hw)
      have h0 := hfix w hw
      have e1 : z w + z w = 0 := by rw [← two_smul F (z w), h2F, zero_smul]
      have key : w = (z (z w) + z w + w) - (z (z w) - z w) - (z w + z w) := by abel
      rw [key, e1]
      exact U.sub_mem (U.sub_mem h0 h2') U.zero_mem
    obtain ⟨s, hs⟩ : ∃ s, ((ρ y₀ : (Module.End F (U' ⧸ U.comap U'.subtype))ˣ) :
        Module.End F (U' ⧸ U.comap U'.subtype)) s ≠ s := by
      by_contra hcon
      push Not at hcon
      exact hy₀ (Units.ext (LinearMap.ext fun s => (hcon s).trans rfl))
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ s
    have hwU : (w : V) ∈ U := hsub w w.2
    have h0 : (Submodule.Quotient.mk w : U' ⧸ U.comap U'.subtype) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 hwU
    rw [h0, map_zero] at hs
    exact hs rfl
  have hord : orderOf zb = 3 := orderOf_eq_prime hzb3 hzb1
  have hcomm' : ∀ (y : Y) (c : Subgroup.zpowers zb),
      Commute (ρ y) ((Subgroup.zpowers zb).subtype c) :=
    fun y c => by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 c.2
      rw [Subgroup.coe_subtype, ← hk]
      exact (Commute.zpow_right (hcomm y) k)
  let Ψ := ρ.noncommCoprod (Subgroup.zpowers zb).subtype hcomm'
  have hYp : ¬ (Nat.card Y).Prime := fun hp => by
    have h81 : 81 ∣ Nat.card Y := by simpa using hY
    rcases (Nat.dvd_prime hp).1 h81 with h | h
    · norm_num at h
    · rw [← h] at hp
      rcases hp.eq_one_or_self_of_dvd 3 (by norm_num) with h3 | h3 <;> norm_num at h3
  have hcenter : ∀ a : Y, (∀ b : Y, a * b = b * a) → a = 1 := fun a ha => by
    have ha' : a ∈ Subgroup.center Y := Subgroup.mem_center_iff.2 fun b => (ha b).symm
    rwa [CFSG.EvenSporadicStandard.HypOne.center_eq_bot_of_isSimpleGroup hYp,
      Subgroup.mem_bot] at ha'
  have hΨ : Function.Injective Ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨a, c⟩ hac
    rw [MonoidHom.mem_ker, MonoidHom.noncommCoprod_apply] at hac
    have hρa : ρ a = ((c : (Module.End F (U' ⧸ U.comap U'.subtype))ˣ))⁻¹ :=
      eq_inv_of_mul_eq_one_left hac
    have ha1 : a = 1 := hcenter a fun b => by
      apply hρinj
      rw [map_mul, map_mul, hρa]
      exact ((hcomm' b c).inv_right).eq.symm
    subst ha1
    rw [map_one, one_mul] at hac
    exact (Prod.mk_eq_one.2 ⟨rfl, Subtype.ext hac⟩ : ((1 : Y), c) = 1) ▸ Subgroup.one_mem ⊥
  have hdvd : Nat.card (Y × Subgroup.zpowers zb) ∣
      Nat.card (Module.End F (U' ⧸ U.comap U'.subtype))ˣ := by
    rw [Nat.card_congr (MonoidHom.ofInjective hΨ).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  rw [Nat.card_prod, Nat.card_zpowers, hord,
    Nat.card_congr (LinearMap.GeneralLinearGroup.generalLinearEquiv F _).toEquiv,
    card_linearEquiv_of_card_two hF] at hdvd
  have hfin : finrank F (U' ⧸ U.comap U'.subtype) ≤ 6 := by
    have h1 := Submodule.finrank_quotient_add_finrank (U.comap U'.subtype)
    rw [LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hle)] at h1
    omega
  exact not_dvd_card_GL_two hfin ((pow_succ 3 4 ▸ Nat.mul_dvd_mul_right hY 3).trans hdvd)

private theorem apply_eq_of_small
    {F V : Type*} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hF : Nat.card F = 2) {Y : Type*} [Group Y] [Finite Y]
    [IsSimpleGroup Y] (hY : 3 ^ 4 ∣ Nat.card Y) (α : Y →* (V ≃ₗ[F] V)) {z : V ≃ₗ[F] V}
    (hz : z ^ 3 = 1) (hzα : ∀ y, z * α y = α y * z) {S : Submodule F V}
    (hS : ∀ y, ∀ v ∈ S, α y v ∈ S) (hzS : ∀ v ∈ S, z v ∈ S)
    (hfix : ∀ v ∈ S, z (z v) + z v + v = 0) (hdim : finrank F S ≤ 6) (y : Y) {v : V}
    (hv : v ∈ S) : α y v = v := by
  have h := sub_mem_of_section hF hY α hz hzα (U := ⊥) (U' := S)
    (fun y v hv => by rw [(Submodule.mem_bot F).1 hv, map_zero]; exact Submodule.zero_mem _) hS
    (fun v hv => by rw [(Submodule.mem_bot F).1 hv, map_zero]; exact Submodule.zero_mem _) hzS
    bot_le (fun v hv => by rw [hfix v hv]; exact Submodule.zero_mem _)
    (by rw [finrank_bot]; omega) y hv
  rwa [Submodule.mem_bot, sub_eq_zero] at h

end TwoField

section Main

private theorem exists_fixSp_four
    {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hF : Nat.card F = 2) (hV : finrank F V = 12)
    {z : V ≃ₗ[F] V} (hz3 : z ^ 3 = 1) (hzd : finrank F (fixSp z) = 2)
    {Wk : Subgroup (V ≃ₗ[F] V)} [IsSimpleGroup Wk] (hWk : Nat.card Wk = 25920)
    (hWkz : ∀ x ∈ Wk, x * z = z * x) (hWkC : ∀ x ∈ Wk, ∀ v, z v = v → x v = v)
    {w : V ≃ₗ[F] V} (hw3 : w ^ 3 = 1) (hwz : w * z = z * w) (hwC : ∀ v, z v = v → w v = v)
    (hwnz : w ∉ Subgroup.zpowers z) (hwWk : ∀ x ∈ Wk, w * x = x * w) :
    ∃ b : ℕ, finrank F (fixSp (w * z ^ b)) = 4 ∧
      ∀ x ∈ Wk, ∀ v ∈ fixSp (w * z ^ b), x v = v := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card]; exact hF)
  haveI : Finite Wk := Nat.finite_of_card_ne_zero (by rw [hWk]; norm_num)
  have hY3 : 3 ^ 4 ∣ Nat.card Wk := by rw [hWk]; norm_num
  have hzα : ∀ y : Wk, z * Wk.subtype y = Wk.subtype y * z := fun y => (hWkz y y.2).symm
  have hCU : IsCompl (fixSp z) (triSp z) := isCompl_fixSp_triSp hz3
  have hdec : ∀ v : V, v ∈ fixSp z ⊔ triSp z := fun v =>
    hCU.codisjoint.eq_top ▸ Submodule.mem_top
  have hUd : finrank F (triSp z) = 10 := by
    have := Submodule.finrank_add_eq_of_isCompl hCU
    omega
  have hz3' : ∀ v, z (z (z v)) = v := apply_three hz3
  have hcz : ∀ u, w (z u) = z (w u) := fun u => by
    have := LinearEquiv.congr_fun hwz u
    simpa only [LinearEquiv.mul_apply] using this
  have hh3 : ∀ i : ℕ, (w * z ^ i) ^ 3 = 1 := fun i => by
    rw [(Commute.pow_right (hwz : Commute w z) i).mul_pow, hw3, ← pow_mul, mul_comm i 3, pow_mul,
      hz3, one_pow, one_mul]
  have hhz : ∀ i : ℕ, z * (w * z ^ i) = (w * z ^ i) * z := fun i =>
    (Commute.mul_left (hwz : Commute w z) (Commute.pow_left (Commute.refl z) i)).symm
  have hhWk : ∀ i : ℕ, ∀ x ∈ Wk, x * (w * z ^ i) = (w * z ^ i) * x := fun i x hx =>
    Commute.mul_right (hwWk x hx : Commute w x).symm (Commute.pow_right (hWkz x hx : Commute x z) i)
  have hhC : ∀ i : ℕ, ∀ v, z v = v → (w * z ^ i) v = v := fun i v hv => by
    rw [LinearEquiv.mul_apply, LinearEquiv.pow_apply, Function.iterate_fixed hv, hwC v hv]
  have hh1 : ∀ i : ℕ, w * z ^ i ≠ 1 := fun i h1 => hwnz (by
    rw [eq_inv_of_mul_eq_one_left h1]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers z) i))
  have hzUi : ∀ i : ℕ, ∀ v ∈ fixSp (w * z ^ i) ⊓ triSp z, z v ∈ fixSp (w * z ^ i) ⊓ triSp z :=
    fun i v hv => ⟨apply_mem_fixSp (hhz i) hv.1, apply_mem_triSp rfl hv.2⟩
  have hWkUi : ∀ i : ℕ, ∀ x ∈ Wk, ∀ v ∈ fixSp (w * z ^ i) ⊓ triSp z,
      x v ∈ fixSp (w * z ^ i) ⊓ triSp z := fun i x hx v hv =>
    ⟨apply_mem_fixSp (hhWk i x hx) hv.1, apply_mem_triSp (hWkz x hx) hv.2⟩
  have heven : ∀ i : ℕ, Even (finrank F ↥(fixSp (w * z ^ i) ⊓ triSp z)) := fun i =>
    even_finrank hF hz3 (hzUi i) (fun v hv hzv => eq_zero_of_mem_triSp hv.2 hzv)
  have htriv : ∀ i : ℕ, finrank F ↥(fixSp (w * z ^ i) ⊓ triSp z) ≤ 6 →
      ∀ x ∈ Wk, ∀ v ∈ fixSp (w * z ^ i) ⊓ triSp z, x v = v := fun i hi x hx v hv =>
    apply_eq_of_small hF hY3 Wk.subtype hz3 hzα (fun y v hv => hWkUi i y y.2 v hv) (hzUi i)
      (fun v hv => mem_triSp.mp hv.2) hi ⟨x, hx⟩ hv
  have hne10 : ∀ i : ℕ, finrank F ↥(fixSp (w * z ^ i) ⊓ triSp z) ≠ 10 := by
    intro i h10
    have hUi : fixSp (w * z ^ i) ⊓ triSp z = triSp z :=
      Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [h10, hUd])
    apply hh1 i
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨c, hc, u, hu, rfl⟩ := Submodule.mem_sup.mp (hdec v)
    have hu' : u ∈ fixSp (w * z ^ i) ⊓ triSp z := hUi.symm ▸ hu
    rw [map_add, hhC i c (mem_fixSp.mp hc), mem_fixSp.mp hu'.1]
    rfl
  have hspan : triSp z ≤ (fixSp (w * z ^ 0) ⊓ triSp z) ⊔
      ((fixSp (w * z ^ 1) ⊓ triSp z) ⊔ (fixSp (w * z ^ 2) ⊓ triSp z)) := by
    intro u hu
    have hu0 := mem_triSp.mp hu
    have hE : ∀ i : ℕ, u + (w * z ^ i) u + (w * z ^ i) ((w * z ^ i) u) ∈
        fixSp (w * z ^ i) ⊓ triSp z := fun i => by
      have hi : ∀ v ∈ triSp z, (w * z ^ i) v ∈ triSp z := fun v hv =>
        apply_mem_triSp (hhz i).symm hv
      refine ⟨mem_fixSp.mpr ?_, (triSp z).add_mem ((triSp z).add_mem hu (hi u hu))
        (hi _ (hi u hu))⟩
      rw [map_add, map_add, apply_three (hh3 i)]
      abel
    have k1 : w (z (z u)) + w (z u) + w u = 0 := by rw [← map_add, ← map_add, hu0, map_zero]
    have k2 : w (w (z (z u))) + w (w (z u)) + w (w u) = 0 := by
      rw [← map_add, ← map_add, ← map_add, ← map_add, hu0, map_zero, map_zero]
    have hsum : (u + (w * z ^ 0) u + (w * z ^ 0) ((w * z ^ 0) u)) +
        ((u + (w * z ^ 1) u + (w * z ^ 1) ((w * z ^ 1) u)) +
          (u + (w * z ^ 2) u + (w * z ^ 2) ((w * z ^ 2) u))) = u := by
      simp only [LinearEquiv.mul_apply, pow_zero, mul_one, pow_one, pow_two, ← hcz, hz3']
      calc _ = (u + u + u) + (w (z (z u)) + w (z u) + w u) +
            (w (w (z (z u))) + w (w (z u)) + w (w u)) := by abel
        _ = u := by rw [k1, k2, vadd_self F, zero_add, add_zero, add_zero]
    rw [← hsum]
    exact Submodule.add_mem_sup (hE 0) (Submodule.add_mem_sup (hE 1) (hE 2))
  have hdisj12 : (fixSp (w * z ^ 1) ⊓ triSp z) ⊓ (fixSp (w * z ^ 2) ⊓ triSp z) = ⊥ := by
    rw [eq_bot_iff]
    rintro u ⟨⟨h1, hu⟩, h2, -⟩
    rw [SetLike.mem_coe, mem_fixSp, LinearEquiv.mul_apply, pow_one] at h1
    rw [SetLike.mem_coe, mem_fixSp, LinearEquiv.mul_apply, pow_two, LinearEquiv.mul_apply] at h2
    have e : z (z u) = z u := w.injective (h2.trans h1.symm)
    rw [Submodule.mem_bot]
    exact eq_zero_of_mem_triSp hu (z.injective e)
  have hdisj0 : (fixSp (w * z ^ 0) ⊓ triSp z) ⊓
      ((fixSp (w * z ^ 1) ⊓ triSp z) ⊔ (fixSp (w * z ^ 2) ⊓ triSp z)) = ⊥ := by
    rw [eq_bot_iff]
    rintro u ⟨⟨h0, -⟩, h12⟩
    obtain ⟨a, ⟨ha1, haU⟩, b, ⟨hb2, hbU⟩, rfl⟩ := Submodule.mem_sup.mp h12
    rw [SetLike.mem_coe, mem_fixSp, pow_zero, mul_one] at h0
    rw [SetLike.mem_coe, mem_fixSp, LinearEquiv.mul_apply, pow_one] at ha1
    rw [SetLike.mem_coe, mem_fixSp, LinearEquiv.mul_apply, pow_two, LinearEquiv.mul_apply] at hb2
    have hwa : w a = z (z a) := by
      calc w a = w (z (z (z a))) := by rw [hz3']
        _ = z (z (w (z a))) := by rw [hcz, hcz]
        _ = z (z a) := by rw [ha1]
    have hwwa : w (w a) = z a := by rw [hwa, hcz, ha1]
    have hwb : w b = z b := by
      calc w b = w (z (z (z b))) := by rw [hz3']
        _ = z (w (z (z b))) := by rw [hcz]
        _ = z b := by rw [hb2]
    have hwwb : w (w b) = z (z b) := by rw [hwb, hcz, hwb]
    have hE : (a + b) + w (a + b) + w (w (a + b)) =
        (a + w a + w (w a)) + (b + w b + w (w b)) := by
      simp only [map_add]
      abel
    rw [h0, h0, hwwa, hwa, hwwb, hwb] at hE
    have hA : a + z (z a) + z a = 0 := by
      have := mem_triSp.mp haU
      calc a + z (z a) + z a = z (z a) + z a + a := by abel
        _ = 0 := this
    have hB : b + z b + z (z b) = 0 := by
      have := mem_triSp.mp hbU
      calc b + z b + z (z b) = z (z b) + z b + b := by abel
        _ = 0 := this
    rw [hA, hB, add_zero, vadd_self F, zero_add] at hE
    rw [Submodule.mem_bot]
    exact hE
  have hsup : (fixSp (w * z ^ 0) ⊓ triSp z) ⊔
      ((fixSp (w * z ^ 1) ⊓ triSp z) ⊔ (fixSp (w * z ^ 2) ⊓ triSp z)) = triSp z :=
    le_antisymm (sup_le inf_le_right (sup_le inf_le_right inf_le_right)) hspan
  have e12 := Submodule.finrank_sup_add_finrank_inf_eq (fixSp (w * z ^ 1) ⊓ triSp z)
    (fixSp (w * z ^ 2) ⊓ triSp z)
  have e012 := Submodule.finrank_sup_add_finrank_inf_eq (fixSp (w * z ^ 0) ⊓ triSp z)
    ((fixSp (w * z ^ 1) ⊓ triSp z) ⊔ (fixSp (w * z ^ 2) ⊓ triSp z))
  rw [hdisj12, finrank_bot] at e12
  rw [hdisj0, finrank_bot, hsup, hUd] at e012
  have hbig : ¬ (finrank F ↥(fixSp (w * z ^ 0) ⊓ triSp z) ≤ 6 ∧
      finrank F ↥(fixSp (w * z ^ 1) ⊓ triSp z) ≤ 6 ∧
      finrank F ↥(fixSp (w * z ^ 2) ⊓ triSp z) ≤ 6) := by
    rintro ⟨h0, h1, h2⟩
    obtain ⟨x, hx1⟩ := exists_ne (1 : Wk)
    apply hx1
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    obtain ⟨c, hc, u, hu, rfl⟩ := Submodule.mem_sup.mp (hdec v)
    obtain ⟨a, ha, bc, hbc, rfl⟩ := Submodule.mem_sup.mp (hspan hu)
    obtain ⟨b', hb', c', hc', rfl⟩ := Submodule.mem_sup.mp hbc
    show (x : V ≃ₗ[F] V) (c + (a + (b' + c'))) = c + (a + (b' + c'))
    rw [map_add, map_add, map_add, hWkC x x.2 c (mem_fixSp.mp hc), htriv 0 h0 x x.2 a ha,
      htriv 1 h1 x x.2 b' hb', htriv 2 h2 x x.2 c' hc']
  obtain ⟨k0, hk0⟩ := heven 0
  obtain ⟨k1, hk1⟩ := heven 1
  obtain ⟨k2, hk2⟩ := heven 2
  have n0 := hne10 0
  have n1 := hne10 1
  have n2 := hne10 2
  obtain ⟨b, hb⟩ : ∃ b : ℕ, finrank F ↥(fixSp (w * z ^ b) ⊓ triSp z) = 2 := by
    rcases (by omega : finrank F ↥(fixSp (w * z ^ 0) ⊓ triSp z) = 2 ∨
        finrank F ↥(fixSp (w * z ^ 1) ⊓ triSp z) = 2 ∨
        finrank F ↥(fixSp (w * z ^ 2) ⊓ triSp z) = 2) with h | h | h
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]
  refine ⟨b, ?_, fun x hx v hv => ?_⟩
  · have hsup' : fixSp (w * z ^ b) ⊔ triSp z = ⊤ := by
      rw [eq_top_iff, ← hCU.codisjoint.eq_top]
      exact sup_le_sup_right (fun v hv => mem_fixSp.mpr (hhC b v (mem_fixSp.mp hv))) _
    have := Submodule.finrank_sup_add_finrank_inf_eq (fixSp (w * z ^ b)) (triSp z)
    rw [hsup', finrank_top, hV, hUd, hb] at this
    omega
  · obtain ⟨c, hc, u, hu, rfl⟩ := Submodule.mem_sup.mp (hdec v)
    have hcb : c ∈ fixSp (w * z ^ b) := mem_fixSp.mpr (hhC b c (mem_fixSp.mp hc))
    have hub : u ∈ fixSp (w * z ^ b) := by
      have := (fixSp (w * z ^ b)).sub_mem hv hcb
      rwa [add_sub_cancel_left] at this
    rw [map_add, hWkC x hx c (mem_fixSp.mp hc), htriv b (by omega) x hx u ⟨hub, hu⟩]

private theorem fix_of_four
    {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hF : Nat.card F = 2) (hV : finrank F V = 12)
    {Q : QuadraticForm F V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {z : V ≃ₗ[F] V} (hz3 : z ^ 3 = 1)
    {Wk P : Subgroup (V ≃ₗ[F] V)} [IsSimpleGroup Wk] (hWk : Nat.card Wk = 25920)
    (hWkz : ∀ x ∈ Wk, x * z = z * x)
    (hPO : P ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hP4 : Nat.card P = 4)
    (hPWk : ∀ p ∈ P, ∀ x ∈ Wk, p * x = x * p)
    (hzP : z ∈ Subgroup.normalizer (P : Set (V ≃ₗ[F] V)))
    {h : V ≃ₗ[F] V} (hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hh3 : h ^ 3 = 1)
    (hhz : h * z = z * h) (hhC : ∀ v, z v = v → h v = v) (hhWk : ∀ x ∈ Wk, x * h = h * x)
    (hd : finrank F (fixSp h) = 4) (hWkY : ∀ x ∈ Wk, ∀ v ∈ fixSp h, x v = v) :
    (∀ p ∈ P, ∀ u ∈ triSp h, p u = u) ∧ ∀ p ∈ P, ∀ y ∈ fixSp h, p y ∈ fixSp h := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card]; exact hF)
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite Wk := Nat.finite_of_card_ne_zero (by rw [hWk]; norm_num)
  have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
  have hY3 : 3 ^ 4 ∣ Nat.card Wk := by rw [hWk]; norm_num
  have hzα : ∀ y : Wk, z * Wk.subtype y = Wk.subtype y * z := fun y => (hWkz y y.2).symm
  have hc : IsCompl (fixSp h) (triSp h) := isCompl_fixSp_triSp hh3
  have hdec : ∀ v : V, v ∈ fixSp h ⊔ triSp h := fun v => hc.codisjoint.eq_top ▸ Submodule.mem_top
  have horth : ∀ a ∈ fixSp h, ∀ b ∈ triSp h, QuadraticMap.polar Q a b = 0 :=
    fun a ha b hb => polar_eq_zero_of_mem hhO ha hb
  have hYreg := polarNondegOn_left hQ hc horth
  have hU'd : finrank F (triSp h) = 8 := by
    have := Submodule.finrank_add_eq_of_isCompl hc
    omega
  have hU'U : triSp h ≤ triSp z := triSp_le_triSp hz3 hhz hhC
  have hzU' : ∀ v ∈ triSp h, z v ∈ triSp h := fun v hv => apply_mem_triSp hhz.symm hv
  have hWkU' : ∀ x ∈ Wk, ∀ v ∈ triSp h, x v ∈ triSp h := fun x hx v hv =>
    apply_mem_triSp (hhWk x hx) hv
  let FW : Submodule F V :=
    { carrier := {v | ∀ x ∈ Wk, x v = v}
      add_mem' := fun {a b} ha hb x hx => by rw [map_add, ha x hx, hb x hx]
      zero_mem' := fun x _ => map_zero x
      smul_mem' := fun c {v} hv x hx => by rw [map_smul, hv x hx] }
  have hC'0 : triSp h ⊓ FW = ⊥ := by
    by_contra hne
    have hzC' : ∀ v ∈ triSp h ⊓ FW, z v ∈ triSp h ⊓ FW := fun v hv => ⟨hzU' v hv.1, fun x hx => by
      have := LinearEquiv.congr_fun (hWkz x hx) v
      simp only [LinearEquiv.mul_apply] at this
      rw [this, hv.2 x hx]⟩
    have hWkC' : ∀ x ∈ Wk, ∀ v ∈ triSp h ⊓ FW, x v ∈ triSp h ⊓ FW := fun x hx v hv => by
      rw [hv.2 x hx]
      exact hv
    obtain ⟨k, hk⟩ :=
      even_finrank hF hz3 hzC' (fun v hv hzv => eq_zero_of_mem_triSp (hU'U hv.1) hzv)
    have hpos : finrank F ↥(triSp h ⊓ FW) ≠ 0 := fun h0 => hne (Submodule.finrank_eq_zero.mp h0)
    have hsec : ∀ x ∈ Wk, ∀ v ∈ triSp h, x v - v ∈ triSp h ⊓ FW := fun x hx v hv =>
      sub_mem_of_section hF hY3 Wk.subtype hz3 hzα (fun y v hv => hWkC' y y.2 v hv)
        (fun y v hv => hWkU' y y.2 v hv) hzC' hzU' inf_le_left
        (fun v hv => by rw [mem_triSp.mp (hU'U hv)]; exact Submodule.zero_mem _)
        (by omega) ⟨x, hx⟩ hv
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨y₃, hy₃⟩ := exists_prime_orderOf_dvd_card' (G := Wk) 3 (by rw [hWk]; norm_num)
    have hg3 : (y₃ : V ≃ₗ[F] V) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, ← hy₃, pow_orderOf_eq_one, Subgroup.coe_one]
    have hg1 : (y₃ : V ≃ₗ[F] V) ≠ 1 := fun h1 => by
      have : y₃ = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hy₃
      norm_num at hy₃
    refine hg1 (eq_one_of_chain h2F hg3 (U₁ := triSp h ⊓ FW) (U₂ := triSp h)
      (fun v hv => hv.2 _ y₃.2) (fun v hv => hsec _ y₃.2 v hv) fun v => ?_)
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (hdec v)
    rw [map_add, hWkY _ y₃.2 a ha, add_sub_add_left_eq_sub]
    exact (triSp h).sub_mem (hWkU' _ y₃.2 b hb) hb
  have hFWY : ∀ v, (∀ x ∈ Wk, x v = v) → v ∈ fixSp h := by
    intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (hdec v)
    have hbFW : b ∈ triSp h ⊓ FW := ⟨hb, fun x hx => by
      have h1 := hv x hx
      rw [map_add, hWkY x hx a ha] at h1
      exact add_left_cancel h1⟩
    rw [hC'0, Submodule.mem_bot] at hbFW
    rw [hbFW, add_zero]
    exact ha
  have hPY : ∀ p ∈ P, ∀ y ∈ fixSp h, p y ∈ fixSp h := fun p hp y hy => hFWY _ fun x hx => by
    have := LinearEquiv.congr_fun (hPWk p hp x hx) y
    simp only [LinearEquiv.mul_apply] at this
    rw [← this, hWkY x hx y hy]
  have hPU' : ∀ p ∈ P, ∀ u ∈ triSp h, p u ∈ triSp h := by
    intro p hp u hu
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (hdec (p u))
    have ha0 : a = 0 := by
      refine hYreg a ha fun y hy => ?_
      have hy' : p⁻¹ y ∈ fixSp h := hPY _ (P.inv_mem hp) y hy
      have hpp : p (p⁻¹ y) = y := p.apply_symm_apply y
      have h1 : QuadraticMap.polar Q y (p u) = 0 := by
        have := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (hPO hp) (p⁻¹ y) u
        rw [hpp] at this
        rw [this]
        exact horth _ hy' u hu
      rw [← hab, QuadraticMap.polar_add_right, horth y hy b hb, add_zero] at h1
      rw [QuadraticMap.polar_comm]
      exact h1
    rw [← hab, ha0, zero_add]
    exact hb
  have hP2 : IsPGroup 2 P := IsPGroup.of_card (n := 2) (by rw [hP4]; norm_num)
  have hU'ne : triSp h ≠ ⊥ := fun h0 => by
    rw [h0, finrank_bot] at hU'd
    norm_num at hU'd
  obtain ⟨u₀, hu₀, hu₀0, hu₀fix⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.S265.BSCl.exists_fixed_ne_zero_of_card_two hF hP2 P.subtype
      (U := triSp h) (fun x u hu => hPU' x x.2 u hu) hU'ne
  let FP : Submodule F V :=
    { carrier := {v | ∀ p ∈ P, p v = v}
      add_mem' := fun {a b} ha hb p hp => by rw [map_add, ha p hp, hb p hp]
      zero_mem' := fun p _ => map_zero p
      smul_mem' := fun c {v} hv p hp => by rw [map_smul, hv p hp] }
  have hconj : ∀ p ∈ P, z⁻¹ * p * z ∈ P := fun p hp =>
    (Subgroup.mem_normalizer_iff.1 hzP _).2 (by simpa [mul_assoc] using hp)
  have hzM : ∀ v ∈ triSp h ⊓ FP, z v ∈ triSp h ⊓ FP := fun v hv =>
    ⟨hzU' v hv.1, fun p hp => by
      have e : p (z v) = z ((z⁻¹ * p * z) v) := by simp [LinearEquiv.mul_apply]
      rw [e, hv.2 _ (hconj p hp)]⟩
  have hWkM : ∀ x ∈ Wk, ∀ v ∈ triSp h ⊓ FP, x v ∈ triSp h ⊓ FP := fun x hx v hv =>
    ⟨hWkU' x hx v hv.1, fun p hp => by
      have := LinearEquiv.congr_fun (hPWk p hp x hx) v
      simp only [LinearEquiv.mul_apply] at this
      rw [this, hv.2 p hp]⟩
  have hMne : triSp h ⊓ FP ≠ ⊥ := fun h0 => hu₀0 (by
    have : u₀ ∈ triSp h ⊓ FP := ⟨hu₀, fun p hp => hu₀fix ⟨p, hp⟩⟩
    rw [h0, Submodule.mem_bot] at this
    exact this)
  obtain ⟨k, hk⟩ :=
    even_finrank hF hz3 hzM (fun v hv hzv => eq_zero_of_mem_triSp (hU'U hv.1) hzv)
  have hMle : finrank F ↥(triSp h ⊓ FP) ≤ finrank F ↥(triSp h) :=
    Submodule.finrank_mono inf_le_left
  have hM8 : finrank F ↥(triSp h ⊓ FP) = 8 := by
    by_contra hne8
    apply hMne
    rw [eq_bot_iff, ← hC'0]
    intro v hv
    exact ⟨hv.1, fun x hx => apply_eq_of_small hF hY3 Wk.subtype hz3 hzα
      (fun y v hv => hWkM y y.2 v hv) hzM (fun v hv => mem_triSp.mp (hU'U hv.1)) (by omega)
      ⟨x, hx⟩ hv⟩
  have hMU' : triSp h ⊓ FP = triSp h :=
    Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [hM8, hU'd])
  refine ⟨fun p hp u hu => ?_, hPY⟩
  have hu' : u ∈ triSp h ⊓ FP := hMU'.symm ▸ hu
  exact hu'.2 p hp

end Main

private theorem zpow_eq_one {F V : Type*} [Field F] [CharP F 2] [AddCommGroup V] [Module F V]
    {z h : V ≃ₗ[F] V} (hz3 : z ^ 3 = 1) (hh3 : h ^ 3 = 1) (hhz : h * z = z * h)
    {P : Subgroup (V ≃ₗ[F] V)} (hP4 : Nat.card P = 4)
    (hPfix : ∀ p ∈ P, z * p * z⁻¹ = p → p = 1)
    (hPU : ∀ p ∈ P, ∀ u ∈ triSp h, p u = u) (hPY : ∀ p ∈ P, ∀ y ∈ fixSp h, p y ∈ fixSp h)
    (n : ℤ) (hgP : ∀ p ∈ P, (h * z ^ n) * p = p * (h * z ^ n)) : z ^ n = 1 := by
  have hc : IsCompl (fixSp h) (triSp h) := isCompl_fixSp_triSp hh3
  have hdec : ∀ v : V, v ∈ fixSp h ⊔ triSp h := fun v => hc.codisjoint.eq_top ▸ Submodule.mem_top
  have hsh : z ^ n * h = h * z ^ n := Commute.zpow_left (hhz : Commute h z).symm n
  have hsY : ∀ y ∈ fixSp h, (h * z ^ n) y = (z ^ n) y := fun y hy => by
    rw [LinearEquiv.mul_apply]
    exact mem_fixSp.mp (apply_mem_fixSp hsh hy)
  have hcomm : ∀ p ∈ P, z ^ n * p = p * z ^ n := by
    intro p hp
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (hdec v)
    simp only [LinearEquiv.mul_apply, map_add]
    congr 1
    · rw [← hsY _ (hPY p hp a ha), ← hsY a ha]
      have := LinearEquiv.congr_fun (hgP p hp) a
      simpa only [LinearEquiv.mul_apply] using this
    · rw [hPU p hp b hb, hPU p hp _ (apply_mem_triSp hsh hb)]
  have hPbot : (∀ p ∈ P, z * p = p * z) → False := fun hzc => by
    have h1 : ∀ p ∈ P, p = 1 := fun p hp => hPfix p hp (by rw [hzc p hp, mul_inv_cancel_right])
    have hbot : P = ⊥ := (Subgroup.eq_bot_iff_forall P).2 h1
    rw [hbot, Subgroup.card_bot] at hP4
    norm_num at hP4
  rw [zpow_eq_zpow_emod' n hz3] at hcomm ⊢
  have hr : n % ((3 : ℕ) : ℤ) = 0 ∨ n % ((3 : ℕ) : ℤ) = 1 ∨ n % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases hr with hr | hr | hr
  · rw [hr, zpow_zero]
  · exfalso
    rw [hr, zpow_one] at hcomm
    exact hPbot hcomm
  · exfalso
    rw [hr] at hcomm
    refine hPbot fun p hp => ?_
    have h4 : Commute (z ^ ((2 : ℤ) * 2)) p := by
      rw [zpow_mul]
      exact Commute.zpow_left (hcomm p hp) 2
    rw [zpow_eq_zpow_emod' _ hz3] at h4
    norm_num at h4
    exact h4

end OmegaMinusTwelve

open OmegaMinusTwelve

private theorem twMinus_struct {F V : Type} [Field F] [Finite F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (hF : Nat.card F = 2) (hV : finrank F V = 12)
    {Q : QuadraticForm F V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hnp : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) {z : V ≃ₗ[F] V} (hz : z ∈ orthDerived Q)
    (hz3 : z ^ 3 = 1) (hzd : finrank F (LinearMap.ker (z.toLinearMap - LinearMap.id)) = 2)
    {Wk P : Subgroup (V ≃ₗ[F] V)} [IsSimpleGroup Wk] (hWk : Nat.card Wk = 25920)
    (hWkz : ∀ x ∈ Wk, x * z = z * x) (hWkC : ∀ x ∈ Wk, ∀ v, z v = v → x v = v)
    (hPO : P ≤ orthDerived Q) (hP4 : Nat.card P = 4) (hPWk : ∀ p ∈ P, ∀ x ∈ Wk, p * x = x * p)
    (hzP : z ∈ Subgroup.normalizer (P : Set (V ≃ₗ[F] V)))
    (hPfix : ∀ p ∈ P, z * p * z⁻¹ = p → p = 1) {w : V ≃ₗ[F] V} (hw : w ∈ orthDerived Q)
    (hw3 : w ^ 3 = 1) (hwz : w * z = z * w) (hwC : ∀ v, z v = v → w v = v)
    (hwnz : w ∉ Subgroup.zpowers z) (hwWk : ∀ x ∈ Wk, w * x = x * w) (j : ℤ)
    (hgP : ∀ p ∈ P, (w * z ^ j) * p = p * (w * z ^ j)) :
    ∃ Y U' : Submodule F V, IsCompl Y U' ∧
      (∀ y ∈ Y, ∀ u ∈ U', QuadraticMap.polar Q y u = 0) ∧ finrank F Y = 4 ∧
      ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp Y.subtype) ∧
      (∀ p ∈ P, ∀ u ∈ U', p u = u) ∧ (∀ y ∈ Y, (w * z ^ j) y = y) ∧
      (∀ u ∈ U', (w * z ^ j) u ∈ U') := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card]; exact hF)
  have hOD : ∀ x, x ∈ orthDerived Q → x ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun x hx =>
    (Subgroup.commutator_le.mpr fun a ha b hb => by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
        (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)) hx
  obtain ⟨b, hb4, hWkY⟩ := exists_fixSp_four hF hV hz3 hzd hWk hWkz hWkC hw3 hwz hwC hwnz hwWk
  have hhO : w * z ^ b ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    hOD _ (mul_mem hw (pow_mem hz b))
  have hh3 : (w * z ^ b) ^ 3 = 1 := by
    rw [(Commute.pow_right (hwz : Commute w z) b).mul_pow, hw3, ← pow_mul, mul_comm b 3, pow_mul,
      hz3, one_pow, one_mul]
  have hhz : (w * z ^ b) * z = z * (w * z ^ b) :=
    Commute.mul_left (hwz : Commute w z) (Commute.pow_left (Commute.refl z) b)
  have hhC : ∀ v, z v = v → (w * z ^ b) v = v := fun v hv => by
    rw [LinearEquiv.mul_apply, LinearEquiv.pow_apply, Function.iterate_fixed hv, hwC v hv]
  have hhWk : ∀ x ∈ Wk, x * (w * z ^ b) = (w * z ^ b) * x := fun x hx =>
    Commute.mul_right (hwWk x hx : Commute w x).symm (Commute.pow_right (hWkz x hx : Commute x z) b)
  obtain ⟨hPU, hPY⟩ := fix_of_four hF hV hQ hz3 hWk hWkz (fun p hp => hOD p (hPO hp)) hP4 hPWk
    hzP hhO hh3 hhz hhC hhWk hb4 hWkY
  have hg : w * z ^ j = (w * z ^ b) * z ^ (j - b) := by
    rw [mul_assoc, ← zpow_natCast, ← zpow_add, show (b : ℤ) + (j - b) = j by omega]
  have hzn : z ^ (j - b) = 1 := zpow_eq_one hz3 hh3 hhz hP4 hPfix hPU hPY (j - b)
    (fun p hp => by rw [← hg]; exact hgP p hp)
  have hgh : w * z ^ j = w * z ^ b := by rw [hg, hzn, mul_one]
  have hc := isCompl_fixSp_triSp hh3
  have horth : ∀ a ∈ fixSp (w * z ^ b), ∀ c ∈ triSp (w * z ^ b), QuadraticMap.polar Q a c = 0 :=
    fun a ha c hc' => polar_eq_zero_of_mem hhO ha hc'
  have hYreg := polarNondegOn_left hQ hc horth
  have hU'reg := polarNondegOn_right hQ hc horth
  have hU'd : finrank F (triSp (w * z ^ b)) = 8 := by
    have := Submodule.finrank_add_eq_of_isCompl hc
    omega
  have hodd : CFSG.RankThree.PartOne.KCOrthogonal.OddOrderIsometry Q 3 (w * z ^ b) := by
    refine ⟨hhO, hh3, ?_, fun v hv => hQ.1 v fun u => by
      rw [QuadraticMap.polarBilin_apply_apply]; exact hv u⟩
    rw [Ne, CharP.cast_eq_zero_iff F 2]
    decide
  have hU'plus : CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (triSp (w * z ^ b)).subtype) := by
    rw [CFSG.RankThree.PartOne.K159.isPlusType_iff_even_of_fixedFree hodd Nat.prime_three
      (by norm_num) (by rw [hF]) 4 (triSp (w * z ^ b)) (fun u hu => apply_mem_triSp rfl hu)
      hU'reg (fun u hu hu' => eq_zero_of_mem_triSp hu hu') hU'd]
    decide
  have hiff := CFSG.ClassicalInvolution.RouteD.TWY.isPlusType_iff_of_isCompl hc horth hYreg
    hU'reg (a := 2) (b := 4) (by norm_num) (by norm_num) (by rw [hb4]) (by rw [hU'd])
  refine ⟨fixSp (w * z ^ b), triSp (w * z ^ b), hc, horth, hb4,
    fun hY => hnp (hiff.mpr (iff_of_true hY hU'plus)), hPU, fun y hy => ?_, fun u hu => ?_⟩
  · rw [hgh]
    exact mem_fixSp.mp hy
  · rw [hgh]
    exact apply_mem_triSp rfl hu

section A5

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.SeitzGeneration

private theorem false_of_isSimpleGroup_le_normalizer {G : Type*} [Group G] {N P H : Subgroup G}
    [IsSimpleGroup N] (hN : Nat.card N = 60) (hP : Nat.card P = 4) (hH : Nat.card H = 120)
    (hNH : N ≤ H) (hPH : P ≤ H) (hnorm : N ≤ Subgroup.normalizer (P : Set G)) : False := by
  have hnormal : (P.subgroupOf N).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hnorm g.2) x).mp hx⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P.subgroupOf N) with hbot | htop
  · have : Finite H := Nat.finite_of_card_ne_zero (by rw [hH]; norm_num)
    have hinj : Function.Injective fun x : N × P =>
        (⟨x.1 * x.2, H.mul_mem (hNH x.1.2) (hPH x.2.2)⟩ : H) := by
      rintro ⟨n₁, p₁⟩ ⟨n₂, p₂⟩ h
      have h' : (n₁ : G) * p₁ = n₂ * p₂ := congrArg Subtype.val h
      have hmem : n₂⁻¹ * n₁ ∈ P.subgroupOf N := by
        rw [Subgroup.mem_subgroupOf]
        have e : ((n₂⁻¹ * n₁ : N) : G) = p₂ * (p₁ : G)⁻¹ := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h',
            mul_inv_cancel_right]
        rw [e]
        exact P.mul_mem p₂.2 (P.inv_mem p₁.2)
      rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at hmem
      subst hmem
      rw [Subtype.ext (mul_left_cancel h')]
    have := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod, hN, hP, hH] at this
    omega
  · have hle : N ≤ P := fun x hx => by
      have : (⟨x, hx⟩ : N) ∈ P.subgroupOf N := htop ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
    have : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; norm_num)
    have := Subgroup.card_le_of_le hle
    rw [hN, hP] at this
    omega

private theorem twMinus_A5 {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (hF2 : Nat.card F = 2) {Q : QuadraticForm F V}
    (hQ : (polarBilin Q).Nondegenerate)
    {Y U' : Submodule F V} (hYU : IsCompl Y U') (horth : ∀ y ∈ Y, ∀ u ∈ U', polar Q y u = 0)
    (hdim : finrank F Y = 4) (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp Y.subtype))
    {P : Subgroup (V ≃ₗ[F] V)} (hPO : P ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hP4 : Nat.card P = 4) (hPfix : ∀ p ∈ P, ∀ u ∈ U', p u = u) :
    ∃ t ∈ orthDerived Q, (∀ u ∈ U', t u = u) ∧ (∀ y ∈ Y, t y ∈ Y) ∧
      t ∉ Subgroup.normalizer (P : Set (V ≃ₗ[F] V)) := by
  by_contra hcon
  push Not at hcon
  have h2 : (2 : F) = 0 := by
    have : Fintype F := Fintype.ofFinite F
    have h := FiniteField.cast_card_eq_zero F
    rw [Fintype.card_eq_nat_card, hF2] at h
    exact_mod_cast h
  have : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  have hdec : ∀ v : V, ∃ y ∈ Y, ∃ u ∈ U', y + u = v := fun v =>
    Submodule.mem_sup.mp (hYU.sup_eq_top ▸ Submodule.mem_top (x := v))
  have hzero : ∀ v : V, (∀ w, polar Q v w = 0) → v = 0 := fun v hv =>
    hQ.1 v fun w => by rw [polarBilin_apply_apply]; exact hv w
  have hYnd : PolarNondegOn Q Y := fun y hy hyy => hzero y fun w => by
    obtain ⟨y', hy', u, hu, rfl⟩ := hdec w
    rw [polar_add_right, hyy y' hy', horth y hy u hu, add_zero]
  have hUperp : ∀ u ∈ U', u ∈ OrthBlk.perp Q Y := fun u hu =>
    OrthBlk.mem_perp.mpr fun y hy => horth y hy u hu
  have hperpY : ∀ r ∈ OrthBlk.perp Q Y, r ∈ U' := by
    intro r hr
    rw [OrthBlk.mem_perp] at hr
    obtain ⟨y₁, hy₁, u₁, hu₁, rfl⟩ := hdec r
    have : y₁ = 0 := hYnd y₁ hy₁ fun y hy => by
      have := hr y hy
      rw [polar_add_right, horth y hy u₁ hu₁, add_zero, polar_comm] at this
      exact this
    rw [this, zero_add]
    exact hu₁
  have hperpU : ∀ v, (∀ u ∈ U', polar Q v u = 0) → v ∈ Y := by
    intro v hv
    obtain ⟨y₁, hy₁, u₁, hu₁, rfl⟩ := hdec v
    have : u₁ = 0 := hzero u₁ fun w => by
      obtain ⟨y₂, hy₂, u₂, hu₂, rfl⟩ := hdec w
      have := hv u₂ hu₂
      rw [polar_add_left, horth y₁ hy₁ u₂ hu₂, zero_add] at this
      rw [polar_add_right, polar_comm, horth y₂ hy₂ u₁ hu₁, zero_add, this]
    rw [this, add_zero]
    exact hy₁
  have hPY : ∀ g ∈ P, ∀ y ∈ Y, g y ∈ Y := fun g hg y hy => hperpU _ fun u hu => by
    rw [← hPfix g hg u hu, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (hPO hg)]
    exact horth y hy u hu
  have hRnd : (polarBilin (Q.comp Y.subtype)).Nondegenerate :=
    CFSG.LieType.SeitzGeneration.nondegenerate_comp_subtype hYnd
  have hts : ∀ W : Submodule F Y, finrank F W = 2 → ∃ w ∈ W, (Q.comp Y.subtype) w ≠ 0 := by
    intro W hW
    by_contra! h
    exact hminus ⟨W, by rw [hW, hdim], h⟩
  obtain ⟨E, _, _, D, ψ, ρ, -, -, -, -, hcomm, hsimple, -, -, hcard, hidx, -, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_actual_derived_extraction (Q.comp Y.subtype) hRnd
      hdim hts
  set OR := TauCeti.QuadraticMap.orthogonalGroup (Q.comp Y.subtype) with hOR
  have hΩsimple : IsSimpleGroup ↥⁅OR, OR⁆ := hcomm ▸ hsimple
  have hΩcard : Nat.card ↥⁅OR, OR⁆ = 60 := by
    rw [hcomm, hcard, hF2]
    norm_num
  have hΩle : ⁅OR, OR⁆ ≤ OR := Subgroup.commutator_le_of_le le_rfl le_rfl
  have hORcard : Nat.card OR = 120 := by
    have h := Subgroup.relIndex_mul_card ρ.range OR
    have hle : ρ.range ≤ OR := by
      rw [← hcomm]
      exact hΩle
    have hri : ρ.range.relIndex OR = 2 := hidx
    rw [inf_of_le_left hle, hcard, hF2, hri] at h
    omega
  have hΦinj : Function.Injective (OrthNS.extU hYnd) := OrthNS.extU_injective hYnd
  have hΦO : ∀ a ∈ OR, OrthNS.extU hYnd a ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    intro a ha
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    obtain ⟨y, hy, u, hu, rfl⟩ := hdec v
    rw [map_add, OrthNS.extU_apply_mem hYnd a hy, OrthNS.extU_apply_perp hYnd a (hUperp u hu),
      QuadraticMap.map_add Q, QuadraticMap.map_add Q, horth _ (a ⟨y, hy⟩).2 u hu,
      horth y hy u hu]
    have := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup ha ⟨y, hy⟩
    rw [QuadraticMap.comp_apply, QuadraticMap.comp_apply] at this
    rw [show Q (a ⟨y, hy⟩ : V) = Q y from this]
  have hHO : OR.map (OrthNS.extU hYnd) ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨a, ha, rfl⟩
    exact hΦO a ha
  have hNΩ : (⁅OR, OR⁆).map (OrthNS.extU hYnd) ≤ orthDerived Q := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hHO hHO
  have : IsSimpleGroup ((⁅OR, OR⁆).map (OrthNS.extU hYnd)) :=
    (Subgroup.equivMapOfInjective _ _ hΦinj).symm.isSimpleGroup
  have hNcard : Nat.card ((⁅OR, OR⁆).map (OrthNS.extU hYnd)) = 60 := by
    rw [Subgroup.card_map_of_injective hΦinj, hΩcard]
  have hHcard : Nat.card (OR.map (OrthNS.extU hYnd)) = 120 := by
    rw [Subgroup.card_map_of_injective hΦinj, hORcard]
  have hPH : P ≤ OR.map (OrthNS.extU hYnd) := by
    intro p hp
    have h1 : ∀ y ∈ Y, p y ∈ Y := hPY p hp
    have h2 : ∀ y ∈ Y, p.symm y ∈ Y := hPY p⁻¹ (P.inv_mem hp)
    refine Subgroup.mem_map.mpr ⟨CFSG.RankThree.PartOne.KCOrthogonal.restrictEquiv Y p h1 h2,
      ?_, ?_⟩
    · rw [hOR, TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
      intro y
      exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (hPO hp) (y : V)
    · exact OrthNS.extU_eq_of_agree hYnd (fun y => rfl) fun r hr => hPfix p hp r (hperpY r hr)
  have hnorm : (⁅OR, OR⁆).map (OrthNS.extU hYnd) ≤
      Subgroup.normalizer (P : Set (V ≃ₗ[F] V)) := by
    rintro _ ⟨a, ha, rfl⟩
    refine hcon _ (hNΩ (Subgroup.mem_map_of_mem _ ha))
      (fun u hu => OrthNS.extU_apply_perp hYnd a (hUperp u hu)) fun y hy => ?_
    rw [OrthNS.extU_apply_mem hYnd a hy]
    exact (a ⟨y, hy⟩).2
  exact false_of_isSimpleGroup_le_normalizer hNcard hP4 hHcard (Subgroup.map_mono hΩle) hPH
    hnorm

end A5

theorem false_of_twelve_omegaMinus_config {F V : Type} [Field F] [Finite F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (hF : Nat.card F = 2) (hV : Module.finrank F V = 12)
    {Q : QuadraticForm F V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) {z : V ≃ₗ[F] V}
    (hzΩ : z ∈ CFSG.RankThree.Classical2.orthDerived Q) (hz3 : z ^ 3 = 1)
    (hC : Module.finrank F (LinearMap.ker (z.toLinearMap - LinearMap.id)) = 2)
    {Wk P : Subgroup (V ≃ₗ[F] V)} [IsSimpleGroup Wk] (hWkc : Nat.card Wk = 25920)
    (hWkz : ∀ x ∈ Wk, x * z = z * x) (hWkC : ∀ x ∈ Wk, ∀ v, z v = v → x v = v)
    (hPΩ : P ≤ CFSG.RankThree.Classical2.orthDerived Q) (hPc : Nat.card P = 4)
    (hPWk : ∀ p ∈ P, ∀ x ∈ Wk, p * x = x * p)
    (hzP : z ∈ Subgroup.normalizer (P : Set (V ≃ₗ[F] V)))
    (hzfpf : ∀ p ∈ P, z * p * z⁻¹ = p → p = 1) {w : V ≃ₗ[F] V}
    (hwΩ : w ∈ CFSG.RankThree.Classical2.orthDerived Q) (hw3 : w ^ 3 = 1) (hwz : w * z = z * w)
    (hwC : ∀ v, z v = v → w v = v) (hwnz : w ∉ Subgroup.zpowers z)
    (hwWk : ∀ x ∈ Wk, w * x = x * w) (j : ℤ) (hgP : ∀ p ∈ P, (w * z ^ j) * p = p * (w * z ^ j))
    (hnorm : ∀ t ∈ CFSG.RankThree.Classical2.orthDerived Q, t * (w * z ^ j) = (w * z ^ j) * t →
      t ∈ Subgroup.normalizer (P : Set (V ≃ₗ[F] V))) : False := by
  have hPO : P ≤ TauCeti.QuadraticMap.orthogonalGroup Q := fun p hp =>
    (Subgroup.commutator_le.mpr fun a ha b hb => by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
        (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)) (hPΩ hp)
  obtain ⟨Y, U', hYU, horth, hY4, hYminus, hPU, hgY, hgU⟩ :=
    twMinus_struct hF hV hQ hminus hzΩ hz3 hC hWkc hWkz hWkC hPΩ hPc hPWk hzP hzfpf hwΩ hw3 hwz
      hwC hwnz hwWk j hgP
  obtain ⟨t, htΩ, htU, htY, htN⟩ := twMinus_A5 hF hQ hYU horth hY4 hYminus hPO hPc hPU
  refine htN (hnorm t htΩ ?_)
  generalize w * z ^ j = g at hgY hgU ⊢
  refine LinearEquiv.ext fun v => ?_
  have hv : v ∈ Y ⊔ U' := hYU.sup_eq_top ▸ Submodule.mem_top
  obtain ⟨y, hy, u, hu, rfl⟩ := Submodule.mem_sup.1 hv
  simp only [LinearEquiv.mul_apply, map_add]
  rw [hgY y hy, htU u hu, hgY _ (htY y hy), htU _ (hgU u hu)]

end CFSG.GGQ2Prime
