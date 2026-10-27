module

public import CFSG.Quasithin.Recognition.G112A2ModStmts
public import CFSG.Quasithin.Recognition.G112A2ModTenLin
public import CFSG.GF2Type.Aschbacher1976Full.HSTransFinClass

public section

namespace CFSG.Quasithin.G112A2

open CFSG.Quasithin CFSG.ASVolI.ChG CFSG.Open
open CFSG.GF2Type.Aschbacher1976Full.HS.TransFin

section Ten

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem ten_sup_mul {E P : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hcomm : ∀ e ∈ E, ∀ p ∈ P, e * p = p * e) (s : V ≃ₗ[ZMod 2] V) (hs : s ∈ E ⊔ P) :
    ∃ e ∈ E, ∃ p ∈ P, s = e * p := by
  let Z : Subgroup (V ≃ₗ[ZMod 2] V) :=
    { carrier := {s | ∃ e ∈ E, ∃ p ∈ P, s = e * p}
      mul_mem' := by
        rintro _ _ ⟨e, he, p, hp, rfl⟩ ⟨e', he', p', hp', rfl⟩
        refine ⟨e * e', E.mul_mem he he', p * p', P.mul_mem hp hp', ?_⟩
        calc e * p * (e' * p') = e * (p * e') * p' := by group
          _ = e * (e' * p) * p' := by rw [hcomm e' he' p hp]
          _ = e * e' * (p * p') := by group
      one_mem' := ⟨1, E.one_mem, 1, P.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨e, he, p, hp, rfl⟩
        refine ⟨e⁻¹, E.inv_mem he, p⁻¹, P.inv_mem hp, ?_⟩
        have h := congrArg (fun g : V ≃ₗ[ZMod 2] V => g⁻¹) (hcomm e he p hp)
        simp only [mul_inv_rev] at h
        rw [mul_inv_rev]
        exact h }
  have hsub : E ⊔ P ≤ Z :=
    sup_le (fun e he => ⟨e, he, 1, P.one_mem, by simp⟩) (fun p hp => ⟨1, E.one_mem, p, hp, by simp⟩)
  obtain ⟨e, he, p, hp, h⟩ := hsub hs
  exact ⟨e, he, p, hp, h⟩

theorem ten_comm_of_card_three {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {P : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hPcard : Nat.card P = 3) : ∀ p ∈ P, ∀ p' ∈ P, p * p' = p' * p := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : IsCyclic P := isCyclic_of_prime_card hPcard
  intro p hp p' hp'
  letI : CommGroup ↥P := IsCyclic.commGroup
  have h : (⟨p, hp⟩ : ↥P) * ⟨p', hp'⟩ = ⟨p', hp'⟩ * ⟨p, hp⟩ := mul_comm _ _
  exact congrArg Subtype.val h

theorem ten_decomp {Γ E P : Subgroup (V ≃ₗ[ZMod 2] V)} {x : V ≃ₗ[ZMod 2] V}
    (hΓeq : Γ = (E ⊔ P) ⊔ Subgroup.zpowers x) (hxx : x * x = 1)
    (hEx : ∀ e ∈ E, x * e * x⁻¹ ∈ E) (hPx : ∀ p ∈ P, x * p * x⁻¹ ∈ P)
    {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ Γ) : t ∈ E ⊔ P ∨ t * x ∈ E ⊔ P := by
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hxxy : ∀ y : V ≃ₗ[ZMod 2] V, x * (x * y) = y := fun y => by
    rw [← mul_assoc, hxx, one_mul]
  have hxS : ∀ s ∈ E ⊔ P, x * s * x⁻¹ ∈ E ⊔ P := by
    intro s hs
    have hle : E ⊔ P ≤ (E ⊔ P).comap (MulAut.conj x).toMonoidHom :=
      sup_le (fun e he => show x * e * x⁻¹ ∈ E ⊔ P from Subgroup.mem_sup_left (hEx e he))
        (fun p hp => show x * p * x⁻¹ ∈ E ⊔ P from Subgroup.mem_sup_right (hPx p hp))
    exact hle hs
  let Y : Subgroup (V ≃ₗ[ZMod 2] V) :=
    { carrier := {t | t ∈ E ⊔ P ∨ t * x ∈ E ⊔ P}
      mul_mem' := by
        rintro t₁ t₂ (h1 | h1) (h2 | h2)
        · exact Or.inl ((E ⊔ P).mul_mem h1 h2)
        · right
          rw [mul_assoc]
          exact (E ⊔ P).mul_mem h1 h2
        · right
          have e1 : t₁ * t₂ * x = (t₁ * x) * (x * t₂ * x⁻¹) := by
            rw [hx']
            simp only [mul_assoc, hxx, mul_one, hxxy]
          rw [e1]
          exact (E ⊔ P).mul_mem h1 (hxS t₂ h2)
        · left
          have e2 : t₁ * t₂ = (t₁ * x) * (x * (t₂ * x) * x⁻¹) := by
            rw [hx']
            simp only [mul_assoc, hxx, mul_one, hxxy]
          rw [e2]
          exact (E ⊔ P).mul_mem h1 (hxS _ h2)
      one_mem' := Or.inl (E ⊔ P).one_mem
      inv_mem' := by
        intro t h
        rcases h with h | h
        · exact Or.inl ((E ⊔ P).inv_mem h)
        · right
          have e3 : t⁻¹ * x = x * (t * x)⁻¹ * x⁻¹ := by
            rw [mul_inv_rev, hx']
            simp only [mul_assoc, hxxy]
          rw [e3]
          exact hxS _ ((E ⊔ P).inv_mem h) }
  have hY : Γ ≤ Y := by
    rw [hΓeq]
    refine sup_le (fun s hs => Or.inl hs) ?_
    rw [Subgroup.zpowers_le]
    exact Or.inr (by rw [hxx]; exact (E ⊔ P).one_mem)
  exact hY ht

theorem ten_pow_three_of_mem {P : Subgroup (V ≃ₗ[ZMod 2] V)} (hPcard : Nat.card P = 3) :
    ∀ q ∈ P, q ^ 3 = 1 := by
  intro q hq
  have h := pow_card_eq_one' (G := ↥P) (x := (⟨q, hq⟩ : ↥P))
  rw [hPcard] at h
  simpa using congrArg Subtype.val h

theorem finrank_range_ne_two_of_ten {Γ X : Subgroup (V ≃ₗ[ZMod 2] V)} (h10 : IsG112Ten Γ X)
    (hX : ∀ y ∈ X, y * y = 1) {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ Γ) (ht2 : t * t = 1) :
    Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) ≠ 2 := by
  obtain ⟨hV, E, P, x, hE, hP, hPcard, hEP, hcomm, _hF, hxX, hxΓ, hΓeq, hinv, φ, _τ, _hτ,
    hTens, _hcompat⟩ := h10
  obtain ⟨θ, β, hsurj, hker, hequ, hmult⟩ := hTens
  have hxx : x * x = 1 := hX x hxX
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hEN : ∀ g ∈ Γ, ∀ e ∈ E, g * e * g⁻¹ ∈ E := by
    intro g hg e he
    rw [hE] at he ⊢
    obtain ⟨e', he', rfl⟩ := Subgroup.mem_map.1 he
    refine Subgroup.mem_map.2 ⟨⟨g, hg⟩ * e' * ⟨g, hg⟩⁻¹, ?_, ?_⟩
    · exact (CFSG.ComponentClassification.Layer.normal ↥Γ).conj_mem e' he' _
    · simp
  have hEx : ∀ e ∈ E, x * e * x⁻¹ ∈ E := fun e he => hEN x hxΓ e he
  have hPx : ∀ q ∈ P, x * q * x⁻¹ ∈ P := fun q hq => by
    rw [hinv q hq]
    exact P.inv_mem hq
  have hdec := ten_decomp hΓeq hxx hEx hPx ht
  have hP3 := ten_pow_three_of_mem hPcard
  have hPcomm := ten_comm_of_card_three hPcard
  obtain ⟨p₀, hp₀, hp₀1⟩ : ∃ q ∈ P, q ≠ 1 := by
    haveI : Nontrivial ↥P := Finite.one_lt_card_iff_nontrivial.mp (by rw [hPcard]; norm_num)
    obtain ⟨q, hq⟩ := exists_ne (1 : ↥P)
    exact ⟨q.1, q.2, fun h => hq (Subtype.ext h)⟩
  have hp₀3 : p₀ ^ 3 = 1 := hP3 p₀ hp₀
  have hω1 : ((θ ⟨p₀, hp₀⟩ : (GaloisField 2 2)ˣ) : GaloisField 2 2) ≠ 1 := by
    intro h
    apply hp₀1
    have h' : θ ⟨p₀, hp₀⟩ = 1 := Units.ext h
    have h'' : (⟨p₀, hp₀⟩ : ↥P) = 1 := θ.injective (h'.trans (map_one θ).symm)
    exact congrArg Subtype.val h''
  have hmul : ∀ (a : ↥(permCore 6)) (b : GaloisField 2 2),
      β (a ⊗ₜ (((θ ⟨p₀, hp₀⟩ : (GaloisField 2 2)ˣ) : GaloisField 2 2) * b)) = p₀ (β (a ⊗ₜ b)) :=
    fun a b => hmult ⟨p₀, hp₀⟩ a b
  have hfix : ∀ v : V, p₀ v = v → v = 0 :=
    fun v hv => ten_fixed_free β hsurj hker p₀ hω1 hmul v hv
  have hV8 : Module.finrank (ZMod 2) V = 8 := hV
  rcases hdec with hS | hSx
  ·
    obtain ⟨e, he, p, hp, rfl⟩ := ten_sup_mul hcomm _ hS
    have hpp : p * p = 1 ∧ e * e = 1 := by
      have hcalc : e * e * (p * p) = 1 := by
        calc e * e * (p * p) = e * p * (e * p) := by
              calc e * e * (p * p) = e * (e * p) * p := by group
                _ = e * (p * e) * p := by rw [hcomm e he p hp]
                _ = e * p * (e * p) := by group
          _ = 1 := ht2
      have hinvP : (p * p)⁻¹ ∈ P := P.inv_mem (P.mul_mem hp hp)
      have heeP : e * e ∈ E ⊓ P := by
        refine Subgroup.mem_inf.2 ⟨E.mul_mem he he, ?_⟩
        have h1 : e * e = (p * p)⁻¹ := eq_inv_of_mul_eq_one_left hcalc
        rw [h1]
        exact hinvP
      rw [hEP, Subgroup.mem_bot] at heeP
      have hpp' : p * p = 1 := by
        have h2 : (p * p)⁻¹ = 1 := by
          have h1 : e * e = (p * p)⁻¹ := eq_inv_of_mul_eq_one_left hcalc
          rw [← h1, heeP]
        exact inv_eq_one.1 h2
      exact ⟨hpp', heeP⟩
    obtain ⟨hpp, hee⟩ := hpp
    have hp1 : p = 1 := by
      have h3 := hP3 p hp
      rw [show p ^ 3 = p * p * p by rw [pow_succ, pow_two], hpp, one_mul] at h3
      exact h3
    subst hp1
    rw [mul_one]
    by_cases he1 : e = 1
    · subst he1
      have h0 : ((1 : V ≃ₗ[ZMod 2] V).toLinearMap - LinearMap.id) = 0 := by
        ext v
        simp
      rw [h0, LinearMap.range_zero, finrank_bot]
      norm_num
    ·
      have hee' : (⟨e, he⟩ : ↥E) * ⟨e, he⟩ = 1 := Subtype.ext hee
      have hσ2' : (φ ⟨e, he⟩ : ↥(alternatingGroup (Fin 6))) * φ ⟨e, he⟩ = 1 := by
        rw [← map_mul, hee', map_one]
      have hσ2 : ((φ ⟨e, he⟩ : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6)) *
          ((φ ⟨e, he⟩ : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6)) = 1 := by
        have h := congrArg Subtype.val hσ2'
        simpa using h
      have hσ1 : ((φ ⟨e, he⟩ : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6)) ≠ 1 := by
        intro h
        apply he1
        have h' : φ ⟨e, he⟩ = 1 := Subtype.ext (by simpa using h)
        have h'' : (⟨e, he⟩ : ↥E) = 1 := φ.injective (h'.trans (map_one φ).symm)
        exact congrArg Subtype.val h''
      have hsign : Equiv.Perm.sign ((φ ⟨e, he⟩ : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6)) = 1 :=
        Equiv.Perm.mem_alternatingGroup.1 (φ ⟨e, he⟩).2
      have hsupp := even_invol_supp hσ2 hσ1 hsign
      have hres := ten_inner_three_le β hker _ hσ2 hsupp e (fun a a' b h => hequ ⟨e, he⟩ a a' b h)
      intro h2
      omega
  ·
    obtain ⟨e, he, p', hp', hs⟩ := ten_sup_mul hcomm _ hSx
    have hsc : ∀ q ∈ P, (t * x) * q = q * (t * x) := by
      intro q hq
      rw [hs]
      calc e * p' * q = e * (p' * q) := by group
        _ = e * (q * p') := by rw [hPcomm p' hp' q hq]
        _ = (e * q) * p' := by group
        _ = (q * e) * p' := by rw [hcomm e he q hq]
        _ = q * (e * p') := by group
    have hinvx : x⁻¹ * p₀ * x = p₀⁻¹ := by
      rw [hx']
      have h := hinv p₀ hp₀
      rw [hx'] at h
      exact h
    have hinvt : t * p₀ * t⁻¹ = p₀⁻¹ := by
      have hsp : (t * x) * p₀⁻¹ = p₀⁻¹ * (t * x) := hsc p₀⁻¹ (P.inv_mem hp₀)
      calc t * p₀ * t⁻¹ = (t * x) * (x⁻¹ * p₀ * x) * (t * x)⁻¹ := by group
        _ = (t * x) * p₀⁻¹ * (t * x)⁻¹ := by rw [hinvx]
        _ = p₀⁻¹ * (t * x) * (t * x)⁻¹ := by rw [hsp]
        _ = p₀⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
    have hinvt' : t * p₀ = p₀⁻¹ * t := mul_inv_eq_iff_eq_mul.1 hinvt
    have hge := ten_finrank_range_ge_four hV8 t p₀ hp₀3 hinvt' hfix
    omega

theorem g112ConclA2_concl10Mod {B : LinearMap.BilinForm (ZMod 2) V} {Γ X : Subgroup (V ≃ₗ[ZMod 2] V)}
    {v₁ : V} {W : Submodule (ZMod 2) V} {X₀ : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hH : G111Hyp B Γ v₁ W X X₀) (h10 : IsG112Ten Γ X) : A2ClauseAt B Γ X v₁ := by
  intro t ht hr _ _
  exact absurd hr (finrank_range_ne_two_of_ten h10 hH.X_sq (hH.X_le ht) (hH.X_sq t ht))

end Ten

end CFSG.Quasithin.G112A2
