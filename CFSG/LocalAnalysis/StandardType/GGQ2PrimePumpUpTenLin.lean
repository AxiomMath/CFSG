module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.Dimension.Finrank
import CFSG.RankThree.OddKernel.SectionRep
import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Generic

public section

namespace CFSG.GGQ2Prime

open Module CFSG.RankThree.OddKernel

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

private theorem exists_ne_zero_fixed_of_card_two {F M : Type*} [Field F] [Finite F] [AddCommGroup M]
    [Module F M] [FiniteDimensional F M] [Nontrivial M] (hF : Nat.card F = 2) {Q : Type*} [Group Q]
    [Finite Q] (hQ : IsPGroup 2 Q) (ρ : Representation F Q M) :
    ∃ m : M, m ≠ 0 ∧ ∀ q, ρ q m = m := by
  let _ : MulAction Q M := MulAction.compHom M ρ
  have : Finite M := Module.finite_of_finite F
  have hcard : 2 ∣ Nat.card M := by
    rw [Module.natCard_eq_pow_finrank (K := F), hF]
    exact dvd_pow_self 2 (Module.finrank_pos (R := F) (M := M)).ne'
  have h0 : (0 : M) ∈ MulAction.fixedPoints Q M := fun q => map_zero (ρ q)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm, hne⟩ := hQ.exists_fixed_point_of_prime_dvd_card_of_fixed_point M hcard h0
  exact ⟨m, hne.symm, fun q => hm q⟩

private theorem even_finrank_of_fpf {F V : Type*} [Field F] [Finite F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (hF : Nat.card F = 2) {z : V ≃ₗ[F] V} (hz : z ^ 3 = 1)
    (hfix : ∀ v, z v = v → v = 0) {S : Submodule F V} (hS : ∀ v ∈ S, z v ∈ S) :
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
    exact Subtype.ext (hfix _ (congrArg Subtype.val hx))
  have hfp : Nat.card (MulAction.fixedPoints A S) = 1 := Nat.card_unique
  rw [hfp, Module.natCard_eq_pow_finrank (K := F), hF] at hmod
  exact even_of_two_pow_modEq_one hmod

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

private theorem add_add_eq_zero_of_fpf {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {z : V ≃ₗ[F] V} (hz : z ^ 3 = 1) (hfix : ∀ v, z v = v → v = 0) (v : V) :
    z (z v) + z v + v = 0 := by
  have hz3 : z (z (z v)) = v := by
    have h := LinearEquiv.congr_fun hz v
    simpa [pow_succ, LinearEquiv.mul_apply] using h
  apply hfix
  rw [map_add, map_add, hz3]
  abel

private theorem sub_mem_of_simple_section {F V : Type*} [Field F] [Finite F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (hF : Nat.card F = 2) {Y : Type*} [Group Y] [Finite Y]
    [IsSimpleGroup Y] (hY : 3 ^ 4 ∣ Nat.card Y) (α : Y →* (V ≃ₗ[F] V)) {z : V ≃ₗ[F] V}
    (hz : z ^ 3 = 1) (hfix : ∀ v, z v = v → v = 0) (hzα : ∀ y, z * α y = α y * z)
    {U U' : Submodule F V} (hU : ∀ y, ∀ v ∈ U, α y v ∈ U) (hU' : ∀ y, ∀ v ∈ U', α y v ∈ U')
    (hzU : ∀ v ∈ U, z v ∈ U) (hzU' : ∀ v ∈ U', z v ∈ U') (hle : U ≤ U')
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
      have h0 := add_add_eq_zero_of_fpf hz hfix w
      have e1 : z w + z w = 0 := by rw [← two_smul F (z w), h2F, zero_smul]
      have key : w = (z (z w) + z w + w) - (z (z w) - z w) - (z w + z w) := by abel
      rw [key, h0, e1]
      exact U.sub_mem (U.sub_mem U.zero_mem h2') U.zero_mem
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

theorem eq_bot_of_commute_simple_finrank_ten {F V : Type*} [Field F] [Finite F] [AddCommGroup V]
    [Module F V] (hF : Nat.card F = 2) (hV : finrank F V = 10) {Y : Type*} [Group Y] [Finite Y]
    [IsSimpleGroup Y] (hY : 3 ^ 4 ∣ Nat.card Y) (α : Y →* (V ≃ₗ[F] V))
    (hα : Function.Injective α) {z : V ≃ₗ[F] V} (hz : z ^ 3 = 1) (hfix : ∀ v, z v = v → v = 0)
    (hzα : ∀ y, z * α y = α y * z) {P : Subgroup (V ≃ₗ[F] V)} (hP : IsPGroup 2 P)
    (hPz : z ∈ Subgroup.normalizer (P : Set (V ≃ₗ[F] V)))
    (hPα : ∀ p ∈ P, ∀ y, p * α y = α y * p) : P = ⊥ := by
  classical
  haveI : FiniteDimensional F V := Module.finite_of_finrank_pos (by omega)
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (V ≃ₗ[F] V) :=
    Finite.of_injective (fun e : V ≃ₗ[F] V => (e : V → V)) fun a b h =>
      LinearEquiv.ext (congrFun h)
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2F : (2 : F) = 0 := by
    letI : Fintype F := Fintype.ofFinite F
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP F 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hF])
    exact_mod_cast CharP.cast_eq_zero F 2
  obtain ⟨y₃, hy₃⟩ :=
    exists_prime_orderOf_dvd_card' 3 ((dvd_pow_self 3 (by norm_num : (4 : ℕ) ≠ 0)).trans hY)
  have hg3 : α y₃ ^ 3 = 1 := by rw [← map_pow, ← hy₃, pow_orderOf_eq_one, map_one]
  have hg1 : α y₃ ≠ 1 := fun h => by
    have : y₃ = 1 := hα (h.trans (map_one α).symm)
    rw [this, orderOf_one] at hy₃
    norm_num at hy₃
  have hchain : ∀ U₁ U₂ : Submodule F V, (∀ v ∈ U₁, α y₃ v = v) →
      (∀ v ∈ U₂, α y₃ v - v ∈ U₁) → (∀ v, α y₃ v - v ∈ U₂) → False :=
    fun U₁ U₂ h₁ h₂ h₃ => hg1 (eq_one_of_chain h2F hg3 h₁ h₂ h₃)
  have hsec : ∀ {U U' : Submodule F V}, (∀ y, ∀ v ∈ U, α y v ∈ U) →
      (∀ y, ∀ v ∈ U', α y v ∈ U') → (∀ v ∈ U, z v ∈ U) → (∀ v ∈ U', z v ∈ U') → U ≤ U' →
      finrank F U' ≤ finrank F U + 6 → ∀ y, ∀ v ∈ U', α y v - v ∈ U :=
    fun hU hU' hzU hzU' hle hdim y _ hv =>
      sub_mem_of_simple_section hF hY α hz hfix hzα hU hU' hzU hzU' hle hdim y hv
  have hdims : ∀ S : Submodule F V, (∀ v ∈ S, z v ∈ S) → S ≠ ⊥ → S ≠ ⊤ →
      2 ≤ finrank F S ∧ finrank F S ≤ 8 := fun S hS h0 h1 => by
    obtain ⟨k, hk⟩ := even_finrank_of_fpf hF hz hfix hS
    have hpos : finrank F S ≠ 0 := fun h => h0 (Submodule.finrank_eq_zero.1 h)
    have hlt := Submodule.finrank_lt h1
    rw [hV] at hlt
    omega
  have hαbot : ∀ y, ∀ v ∈ (⊥ : Submodule F V), α y v ∈ (⊥ : Submodule F V) := fun y v hv => by
    rw [(Submodule.mem_bot F).1 hv, map_zero]
    exact Submodule.zero_mem _
  have hzbot : ∀ v ∈ (⊥ : Submodule F V), z v ∈ (⊥ : Submodule F V) := fun v hv => by
    rw [(Submodule.mem_bot F).1 hv, map_zero]
    exact Submodule.zero_mem _
  have hαtop : ∀ y, ∀ v ∈ (⊤ : Submodule F V), α y v ∈ (⊤ : Submodule F V) :=
    fun _ _ _ => Submodule.mem_top
  have hztop : ∀ v ∈ (⊤ : Submodule F V), z v ∈ (⊤ : Submodule F V) := fun _ _ => Submodule.mem_top
  have hconj : ∀ p ∈ P, z⁻¹ * p * z ∈ P := fun p hp =>
    (Subgroup.mem_normalizer_iff.1 hPz _).2 (by simpa [mul_assoc] using hp)
  have hpz : ∀ p : V ≃ₗ[F] V, ∀ v, p (z v) = z ((z⁻¹ * p * z) v) := fun p v => by
    simp [LinearEquiv.mul_apply]
  have hpα : ∀ p ∈ P, ∀ y v, p (α y v) = α y (p v) := fun p hp y v =>
    LinearEquiv.congr_fun (hPα p hp y) v
  have hzαv : ∀ y v, z (α y v) = α y (z v) := fun y v => LinearEquiv.congr_fun (hzα y) v
  have hbot : (∀ p ∈ P, ∀ v, p v = v) → P = ⊥ := fun h =>
    (Subgroup.eq_bot_iff_forall P).2 fun p hp => LinearEquiv.ext (h p hp)
  let C : Submodule F V :=
    { carrier := {v | ∀ p ∈ P, p v = v}
      add_mem' := fun {a b} ha hb p hp => by rw [map_add, ha p hp, hb p hp]
      zero_mem' := fun p _ => map_zero p
      smul_mem' := fun c {v} hv p hp => by rw [map_smul, hv p hp] }
  have hzC : ∀ v ∈ C, z v ∈ C := fun v hv p hp => by
    rw [hpz p, hv _ (hconj p hp)]
  have hαC : ∀ y, ∀ v ∈ C, α y v ∈ C := fun y v hv p hp => by
    rw [hpα p hp, hv p hp]
  have hPC : ∀ p ∈ P, ∀ v ∈ C, p v ∈ C := fun p hp v hv => by
    rw [hv p hp]
    exact hv
  have hfixsec : ∀ U : Submodule F V, (∀ p ∈ P, ∀ v ∈ U, p v ∈ U) → U ≠ ⊤ →
      ∃ w, w ∉ U ∧ ∀ p ∈ P, p w - w ∈ U := fun U hU hne => by
    let ρ := sectionRep P.subtype (U := U) (U' := ⊤) (fun p v hv => hU p p.2 v hv)
      (fun _ _ _ => Submodule.mem_top)
    haveI : Nontrivial ((⊤ : Submodule F V) ⧸ U.comap (⊤ : Submodule F V).subtype) := by
      refine Submodule.Quotient.nontrivial_iff.2 fun h => hne ?_
      rw [eq_top_iff]
      intro v _
      have : (⟨v, Submodule.mem_top⟩ : (⊤ : Submodule F V)) ∈ U.comap (⊤ : Submodule F V).subtype :=
        h ▸ Submodule.mem_top
      exact this
    obtain ⟨m, hm0, hm⟩ := exists_ne_zero_fixed_of_card_two hF hP ρ
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    refine ⟨w, fun hw => hm0 ((Submodule.Quotient.mk_eq_zero _).2 hw), fun p hp => ?_⟩
    exact (sectionRep_mk_eq_mk_iff P.subtype _ _ ⟨p, hp⟩ w).1 (hm ⟨p, hp⟩)
  have hC0 : C ≠ ⊥ := by
    obtain ⟨w, hw, hwP⟩ := hfixsec ⊥ (fun p _ v hv => by
      rw [(Submodule.mem_bot F).1 hv, map_zero]
      exact Submodule.zero_mem _) bot_ne_top
    intro hC
    apply hw
    have hwC : w ∈ C := fun p hp => sub_eq_zero.1 ((Submodule.mem_bot F).1 (hwP p hp))
    rw [hC] at hwC
    exact hwC
  by_cases hCtop : C = ⊤
  · exact hbot fun p hp v => (hCtop ▸ Submodule.mem_top : v ∈ C) p hp
  obtain ⟨hC2, hC8⟩ := hdims C hzC hC0 hCtop
  let D : Submodule F V :=
    { carrier := {v | ∀ p ∈ P, p v - v ∈ C}
      add_mem' := fun {a b} ha hb p hp => by
        rw [map_add, add_sub_add_comm]
        exact C.add_mem (ha p hp) (hb p hp)
      zero_mem' := fun p _ => by
        rw [map_zero, sub_zero]
        exact C.zero_mem
      smul_mem' := fun c {v} hv p hp => by
        rw [map_smul, ← smul_sub]
        exact C.smul_mem c (hv p hp) }
  have hCD : C ≤ D := fun v hv p hp => by
    rw [hv p hp, sub_self]
    exact C.zero_mem
  have hzD : ∀ v ∈ D, z v ∈ D := fun v hv p hp => by
    rw [hpz p, ← map_sub]
    exact hzC _ (hv _ (hconj p hp))
  have hαD : ∀ y, ∀ v ∈ D, α y v ∈ D := fun y v hv p hp => by
    rw [hpα p hp, ← map_sub]
    exact hαC y _ (hv p hp)
  have hDC : C < D := by
    obtain ⟨w, hw, hwP⟩ := hfixsec C hPC hCtop
    exact lt_of_le_of_ne hCD fun h => hw (h ▸ (hwP : w ∈ D))
  have hDC' := Submodule.finrank_lt_finrank_of_lt hDC
  have hDeven := even_finrank_of_fpf hF hz hfix hzD
  rcases (by obtain ⟨k, hk⟩ := even_finrank_of_fpf hF hz hfix hzC; omega :
      finrank F C = 2 ∨ finrank F C = 4 ∨ finrank F C = 6 ∨ finrank F C = 8) with
    h2 | h46 | h46 | h8
  ·
    have hGC : ∀ y, ∀ v ∈ C, α y v = v := fun y v hv => sub_eq_zero.1 ((Submodule.mem_bot F).1
      (hsec hαbot hαC hzbot hzC bot_le (by rw [finrank_bot]; omega) y v hv))
    by_cases hDtop : D = ⊤
    · have hD : ∀ p ∈ P, ∀ v, p v - v ∈ C := fun p hp v => (hDtop ▸ Submodule.mem_top : v ∈ D) p hp
      let B : Submodule F V := Submodule.span F (Set.range fun yv : Y × V => α yv.1 yv.2 - yv.2)
      have hgen : ∀ y v, α y v - v ∈ B := fun y v => Submodule.subset_span ⟨(y, v), rfl⟩
      have hzB : ∀ v ∈ B, z v ∈ B := fun v hv => by
        have hle : B ≤ B.comap (z : V →ₗ[F] V) := Submodule.span_le.2 (by
          rintro _ ⟨⟨y, u⟩, rfl⟩
          change z (α y u - u) ∈ B
          rw [map_sub, hzαv]
          exact hgen y (z u))
        exact hle hv
      have hαB : ∀ y, ∀ v ∈ B, α y v ∈ B := fun y v hv => by
        have hle : B ≤ B.comap (α y : V →ₗ[F] V) := Submodule.span_le.2 (by
          rintro _ ⟨⟨y', u⟩, rfl⟩
          change α y (α y' u - u) ∈ B
          have : α y (α y' u - u) = (α (y * y') u - u) - (α y u - u) := by
            rw [map_sub, map_mul, LinearEquiv.mul_apply]
            abel
          rw [this]
          exact B.sub_mem (hgen _ _) (hgen _ _))
        exact hle hv
      let E : Submodule F V := C ⊔ B
      have hzE : ∀ v ∈ E, z v ∈ E := fun v hv => by
        obtain ⟨c, hc, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
        rw [map_add]
        exact Submodule.add_mem_sup (hzC c hc) (hzB b hb)
      have hαE : ∀ y, ∀ v ∈ E, α y v ∈ E := fun y v hv => by
        obtain ⟨c, hc, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
        rw [map_add]
        exact Submodule.add_mem_sup (hαC y c hc) (hαB y b hb)
      by_cases hEtop : E = ⊤
      · refine hbot fun p hp => ?_
        have hker : E ≤ LinearMap.ker ((p : V →ₗ[F] V) - LinearMap.id) := by
          refine sup_le (fun c hc => ?_) (Submodule.span_le.2 ?_)
          · rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
            exact hc p hp
          · rintro _ ⟨⟨y, v⟩, rfl⟩
            dsimp only
            rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
              sub_eq_zero, LinearEquiv.coe_coe]
            have hc : α y (p v - v) = p v - v := hGC y _ (hD p hp v)
            rw [map_sub] at hc
            rw [map_sub, hpα p hp, sub_eq_sub_iff_sub_eq_sub]
            exact hc
        intro v
        have := hker (hEtop ▸ Submodule.mem_top : v ∈ E)
        rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
      · exfalso
        have hE0 : E ≠ ⊥ := fun h => hC0 (eq_bot_iff.2 (h ▸ le_sup_left))
        obtain ⟨-, hE8⟩ := hdims E hzE hE0 hEtop
        have hCE : C ≤ E := le_sup_left
        exact hchain C E (hGC y₃)
          (hsec hαC hαE hzC hzE hCE (by omega) y₃)
          (fun v => (le_sup_right : B ≤ E) (hgen y₃ v))
    · exfalso
      have hD0 : D ≠ ⊥ := fun h => hC0 (eq_bot_iff.2 (h ▸ hCD))
      obtain ⟨-, hD8⟩ := hdims D hzD hD0 hDtop
      obtain ⟨k, hk⟩ := hDeven
      exact hchain C D (hGC y₃) (hsec hαC hαD hzC hzD hCD (by omega) y₃)
        (fun v => hsec hαD hαtop hzD hztop le_top (by rw [finrank_top, hV]; omega) y₃ v
          Submodule.mem_top)
  ·
    exfalso
    have hGC : ∀ v ∈ C, α y₃ v = v := fun v hv => sub_eq_zero.1 ((Submodule.mem_bot F).1
      (hsec hαbot hαC hzbot hzC bot_le (by rw [finrank_bot]; omega) y₃ v hv))
    exact hchain C C hGC (fun v hv => by rw [hGC v hv, sub_self]; exact C.zero_mem)
      (fun v => hsec hαC hαtop hzC hztop le_top (by rw [finrank_top, hV]; omega) y₃ v
        Submodule.mem_top)
  · exfalso
    have hGC : ∀ v ∈ C, α y₃ v = v := fun v hv => sub_eq_zero.1 ((Submodule.mem_bot F).1
      (hsec hαbot hαC hzbot hzC bot_le (by rw [finrank_bot]; omega) y₃ v hv))
    exact hchain C C hGC (fun v hv => by rw [hGC v hv, sub_self]; exact C.zero_mem)
      (fun v => hsec hαC hαtop hzC hztop le_top (by rw [finrank_top, hV]; omega) y₃ v
        Submodule.mem_top)
  ·
    have hDtop : D = ⊤ := by
      obtain ⟨k, hk⟩ := hDeven
      have hle := Submodule.finrank_le D
      rw [hV] at hle
      exact Submodule.eq_top_of_finrank_eq (by rw [hV]; omega)
    have hD : ∀ p ∈ P, ∀ v, p v - v ∈ C := fun p hp v => (hDtop ▸ Submodule.mem_top : v ∈ D) p hp
    have hGV : ∀ y v, α y v - v ∈ C := fun y v =>
      hsec hαC hαtop hzC hztop le_top (by rw [finrank_top, hV]; omega) y v Submodule.mem_top
    let G₀ : Submodule F V :=
      { carrier := {v | ∀ y, α y v = v}
        add_mem' := fun {a b} ha hb y => by rw [map_add, ha y, hb y]
        zero_mem' := fun y => map_zero (α y)
        smul_mem' := fun c {v} hv y => by rw [map_smul, hv y] }
    let F₀ : Submodule F V := C ⊓ G₀
    have hzF₀ : ∀ v ∈ F₀, z v ∈ F₀ := fun v hv =>
      ⟨hzC v hv.1, fun y => by rw [← hzαv, hv.2 y]⟩
    have hαF₀ : ∀ y, ∀ v ∈ F₀, α y v ∈ F₀ := fun y v hv => by
      rw [hv.2 y]
      exact hv
    have hpF₀ : ∀ p ∈ P, ∀ v, p v - v ∈ F₀ := fun p hp v => by
      refine ⟨hD p hp v, fun y => ?_⟩
      have h1 : p (α y v - v) = α y v - v := hGV y v p hp
      rw [map_sub] at h1
      rw [map_sub, ← hpα p hp, sub_eq_sub_iff_sub_eq_sub]
      exact h1
    by_cases hF₀ : F₀ = ⊥
    · exact hbot fun p hp v => sub_eq_zero.1 ((Submodule.mem_bot F).1 (hF₀ ▸ hpF₀ p hp v))
    · exfalso
      obtain ⟨hF2, -⟩ := hdims F₀ hzF₀ hF₀ (fun h => hCtop (eq_top_iff.2 (h ▸ inf_le_left)))
      exact hchain F₀ C (fun v hv => hv.2 y₃)
        (hsec hαF₀ hαC hzF₀ hzC inf_le_left (by omega) y₃) (hGV y₃)

end CFSG.GGQ2Prime
