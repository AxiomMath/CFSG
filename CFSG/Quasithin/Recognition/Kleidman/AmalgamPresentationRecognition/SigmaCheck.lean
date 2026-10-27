module

public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.A2Check
public import Certificates.Certificate272036
public import Mathlib.Algebra.Order.Ring.Star
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition

open CFSG.Quasithin.J2Cz CFSG.Quasithin.J2Cz.QM CFSG.Quasithin.J2Cz.F2 Equiv

@[expose] def mixedRels : List (List (Fin 7 × Bool)) :=
  j3WordsRest.filter fun r => (r.any fun x => x.1.val == 6) && (r.any fun x => x.1.val == 4)

theorem sigma_forced (σ : KK →* KK)
    (hy : ((σ (gK 0) : KK) : Model) = elY) (hx : ((σ (gK 1) : KK) : Model) = elX)
    (hz : ((σ (gK 2) : KK) : Model) = elZ * elX)
    (hsq : ∀ k : KK, ((σ (σ k) : KK) : Model) = elA * (k : Model) * elA⁻¹) :
    ((σ (gK 3) : KK) : Model) = elT :=
  Certificates.certificate272036 σ hy hx hz hsq

section Final

theorem model_facts : modelTuple 2 * modelTuple 2 = 1 ∧ modelTuple 3 * modelTuple 3 = 1 ∧
    modelTuple 2 * modelTuple 3 = modelTuple 3 * modelTuple 2 ∧
    modelTuple 0 * modelTuple 2 = modelTuple 2 * modelTuple 0 ∧
    modelTuple 1 * modelTuple 1 = 1 ∧
    (modelTuple 4)⁻¹ * (modelTuple 4)⁻¹ * (modelTuple 0)⁻¹ * (modelTuple 4)⁻¹ *
      (modelTuple 4)⁻¹ * (modelTuple 0)⁻¹ * modelTuple 2 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply enc_injective <;>
    simp only [enc_mul, enc_inv, enc_one, enc_modelTuple] <;> decide +kernel

theorem beta_facts {G : Type*} [Group G] (y x z b : G) (hxx : x * x = 1) (hzz : z * z = 1)
    (hxz : x * z = z * x) (hyx : y * x = x * y)
    (r27 : x * b * x * b⁻¹ = 1) (r19 : b * y * b * x = 1) (r20 : b⁻¹ * b⁻¹ * y⁻¹ * x = 1)
    (r21 : b⁻¹ * z * b⁻¹ * z * y⁻¹ = 1) :
    b * b = y⁻¹ * x ∧ b * x * b⁻¹ = x ∧ b * y * b⁻¹ = y ∧ b * z * b⁻¹ = z * x := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hbb : b * b = y⁻¹ * x := by
    have h : (b * b)⁻¹ = x⁻¹ * y := by
      rw [mul_inv_rev]
      have := r20
      calc b⁻¹ * b⁻¹ = (b⁻¹ * b⁻¹ * y⁻¹ * x) * x⁻¹ * y := by group
        _ = x⁻¹ * y := by rw [this]; group
    have := congrArg (·⁻¹) h
    simpa using this
  have hbx : b * x * b⁻¹ = x := by
    have : b * x * b⁻¹ = x⁻¹ := by
      calc b * x * b⁻¹ = x⁻¹ * (x * b * x * b⁻¹) := by group
        _ = x⁻¹ := by rw [r27]; group
    rw [this, hxi]
  have hbyb : b * y * b = x := by
    have : b * y * b = x⁻¹ := by
      calc b * y * b = (b * y * b * x) * x⁻¹ := by group
        _ = x⁻¹ := by rw [r19]; group
    rw [this, hxi]
  have hby : b * y * b⁻¹ = y := by
    calc b * y * b⁻¹ = (b * y * b) * (b * b)⁻¹ := by group
      _ = x * (y⁻¹ * x)⁻¹ := by rw [hbyb, hbb]
      _ = y := by group
  have h2 : b⁻¹ * z * b⁻¹ = y * z⁻¹ := by
    calc b⁻¹ * z * b⁻¹ = (b⁻¹ * z * b⁻¹ * z * y⁻¹) * y * z⁻¹ := by group
      _ = y * z⁻¹ := by rw [r21]; group
  have hbz : b * z * b⁻¹ = z * x := by
    calc b * z * b⁻¹ = (b * b) * (b⁻¹ * z * b⁻¹) := by group
      _ = (y⁻¹ * x) * (y * z⁻¹) := by rw [hbb, h2]
      _ = y⁻¹ * (x * y) * z⁻¹ := by group
      _ = y⁻¹ * (y * x) * z⁻¹ := by rw [← hyx]
      _ = x * z := by rw [hzi]; group
      _ = z * x := hxz
  exact ⟨hbb, hbx, hby, hbz⟩

theorem conj_comm {G : Type*} [Group G] (b p c : G) (h : p * c = c * p) :
    (b * p * b⁻¹) * (b * c * b⁻¹) = (b * c * b⁻¹) * (b * p * b⁻¹) := by
  calc (b * p * b⁻¹) * (b * c * b⁻¹) = b * (p * c) * b⁻¹ := by group
    _ = b * (c * p) * b⁻¹ := by rw [h]
    _ = _ := by group

theorem mixedRels_eq : mixedRels =
    [[(4, false), (4, false), (0, false), (4, false), (4, false), (6, true), (6, true)],
     [(3, true), (6, true), (4, false), (1, true), (6, false), (4, true), (1, true)]] := by
  decide +kernel

theorem mixed_rels_of_beta {G : Type*} [Group G]
    (ψ : Model →* G) (hψ : Function.Injective ψ) (e : Fin 7 → G)
    (he : ∀ i : Fin 7, i.val < 6 → e i = ψ (modelTuple7 i))
    (hrange : ∀ g : G, g ∈ Subgroup.centralizer ({e 3} : Set G) → g ∈ ψ.range)
    (β : G) (hβ : ∀ r ∈ relsA2, evalWord (Function.update e 6 β) r = 1) :
    ∀ r ∈ mixedRels, evalWord (Function.update e 6 β) r = 1 := by
  obtain ⟨fXX, fZZ, fXZ, fYX, fE1, fT25⟩ := model_facts
  have h0 : e 0 = ψ (modelTuple 0) := by simpa [modelTuple7] using he 0 (by decide)
  have h1 : e 1 = ψ (modelTuple 1) := by simpa [modelTuple7] using he 1 (by decide)
  have h2 : e 2 = ψ (modelTuple 2) := by simpa [modelTuple7] using he 2 (by decide)
  have h3 : e 3 = ψ (modelTuple 3) := by simpa [modelTuple7] using he 3 (by decide)
  have h4 : e 4 = ψ (modelTuple 4) := by simpa [modelTuple7] using he 4 (by decide)
  have hu0 : Function.update e 6 β 0 = e 0 := Function.update_of_ne (by decide) _ _
  have hu1 : Function.update e 6 β 1 = e 1 := Function.update_of_ne (by decide) _ _
  have hu2 : Function.update e 6 β 2 = e 2 := Function.update_of_ne (by decide) _ _
  have hu3 : Function.update e 6 β 3 = e 3 := Function.update_of_ne (by decide) _ _
  have hu4 : Function.update e 6 β 4 = e 4 := Function.update_of_ne (by decide) _ _
  have hu6 : Function.update e 6 β 6 = β := Function.update_self _ _ _
  have hxx : e 2 * e 2 = 1 := by rw [h2, ← map_mul, fXX, map_one]
  have hzz : e 3 * e 3 = 1 := by rw [h3, ← map_mul, fZZ, map_one]
  have hxz : e 2 * e 3 = e 3 * e 2 := by rw [h2, h3, ← map_mul, ← map_mul, fXZ]
  have hyx : e 0 * e 2 = e 2 * e 0 := by rw [h0, h2, ← map_mul, ← map_mul, fYX]
  have he11 : e 1 * e 1 = 1 := by rw [h1, ← map_mul, fE1, map_one]
  have hT25 : (e 4)⁻¹ * (e 4)⁻¹ * (e 0)⁻¹ * (e 4)⁻¹ * (e 4)⁻¹ * (e 0)⁻¹ * e 2 = 1 := by
    rw [h4, h0, h2]
    simpa [map_mul, map_inv] using congrArg ψ fT25
  have r27 := hβ [(2, true), (6, true), (2, true), (6, false)] (by decide +kernel)
  have r19 := hβ [(6, true), (0, true), (6, true), (2, true)] (by decide +kernel)
  have r20 := hβ [(6, false), (6, false), (0, false), (2, true)] (by decide +kernel)
  have r21 := hβ [(6, false), (3, true), (6, false), (3, true), (0, false)] (by decide +kernel)
  simp only [evalWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    Bool.cond_true, Bool.cond_false, hu0, hu2, hu3, hu6, ← mul_assoc] at r27 r19 r20 r21
  obtain ⟨hbb, hbx, hby, hbz⟩ := beta_facts (e 0) (e 2) (e 3) β hxx hzz hxz hyx r27 r19 r20 r21
  have hbxc : β * e 2 * β⁻¹ = e 2 := hbx
  have hconj : ∀ k : KK, ∃ m : KK, ψ (m : Model) = β * ψ (k : Model) * β⁻¹ := by
    intro k
    obtain ⟨hk1, hk2⟩ := mem_KK.1 k.2
    have hkx : ψ (k : Model) * e 2 = e 2 * ψ (k : Model) := by
      rw [h2, ← map_mul, ← map_mul]; exact congrArg ψ hk1.symm
    have hkz : ψ (k : Model) * e 3 = e 3 * ψ (k : Model) := by
      rw [h3, ← map_mul, ← map_mul]; exact congrArg ψ hk2.symm
    have cx := conj_comm β _ _ hkx
    have cz := conj_comm β _ _ hkz
    rw [hbx] at cx
    rw [hbz] at cz
    set q := β * ψ (k : Model) * β⁻¹ with hq
    have cz' : q * e 3 = e 3 * q := by
      have hz3 : e 3 = e 3 * e 2 * e 2 := by rw [mul_assoc, hxx, mul_one]
      calc q * e 3 = q * (e 3 * e 2 * e 2) := by rw [← hz3]
        _ = (q * (e 3 * e 2)) * e 2 := (mul_assoc _ _ _).symm
        _ = ((e 3 * e 2) * q) * e 2 := by rw [cz]
        _ = (e 3 * e 2) * (q * e 2) := mul_assoc _ _ _
        _ = (e 3 * e 2) * (e 2 * q) := by rw [cx]
        _ = e 3 * (e 2 * e 2) * q := by group
        _ = e 3 * q := by rw [hxx, mul_one]
    have hqmem : q ∈ Subgroup.centralizer ({e 3} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff.mp hg]
      exact cz'.symm
    obtain ⟨m, hm⟩ := hrange q hqmem
    refine ⟨⟨m, mem_KK.2 ⟨?_, ?_⟩⟩, hm⟩
    · show modelTuple 2 * m = m * modelTuple 2
      apply hψ
      rw [map_mul, map_mul, hm, ← h2]
      exact cx.symm
    · show modelTuple 3 * m = m * modelTuple 3
      apply hψ
      rw [map_mul, map_mul, hm, ← h3]
      exact cz'.symm
  choose f hf using hconj
  have hψK : ∀ a b : KK, ψ (a : Model) = ψ (b : Model) → a = b :=
    fun a b h => Subtype.ext (hψ h)
  let σ : KK →* KK :=
    { toFun := f
      map_one' := hψK _ _ (by rw [hf]; simp)
      map_mul' := fun a b => hψK _ _ (by
        rw [Subgroup.coe_mul, map_mul, hf, hf, hf, Subgroup.coe_mul, map_mul]; group) }
  have hσ : ∀ k : KK, ψ ((σ k : KK) : Model) = β * ψ (k : Model) * β⁻¹ := hf
  have hy' : ((σ (gK 0) : KK) : Model) = elY := by
    apply hψ
    rw [hσ]
    show β * ψ (modelTuple 0) * β⁻¹ = ψ (modelTuple 0)
    rw [← h0]; exact hby
  have hx' : ((σ (gK 1) : KK) : Model) = elX := by
    apply hψ
    rw [hσ]
    show β * ψ (modelTuple 2) * β⁻¹ = ψ (modelTuple 2)
    rw [← h2]; exact hbx
  have hz' : ((σ (gK 2) : KK) : Model) = elZ * elX := by
    apply hψ
    rw [hσ, map_mul]
    show β * ψ (modelTuple 3) * β⁻¹ = ψ (modelTuple 3) * ψ (modelTuple 2)
    rw [← h2, ← h3]; exact hbz
  have hsq : ∀ k : KK, ((σ (σ k) : KK) : Model) = elA * (k : Model) * elA⁻¹ := by
    intro k
    apply hψ
    have hA : ψ elA = (e 0)⁻¹ * e 2 := by
      simp only [elA, elY, elX, map_mul, map_inv]
      rw [h0, h2]
    rw [hσ, hσ, map_mul, map_mul, map_inv, hA, ← hbb]
    group
  have key := sigma_forced σ hy' hx' hz' hsq
  have hU : β * ((e 4)⁻¹ * e 1) * β⁻¹ = e 3 * e 1 * (e 4)⁻¹ := by
    have := hσ (gK 3)
    rw [key] at this
    have h5 : ψ elT = e 3 * e 1 * (e 4)⁻¹ := by
      simp only [elT, map_mul, map_inv]
      rw [h3, h1, h4]
    have h6 : ψ (((gK 3 : KK)) : Model) = (e 4)⁻¹ * e 1 := by
      show ψ ((modelTuple 4)⁻¹ * modelTuple 1) = _
      rw [map_mul, map_inv, h4, h1]
    rw [← h5, this, h6]
  rw [mixedRels_eq]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · simp only [evalWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      Bool.cond_true, Bool.cond_false, hu0, hu4, hu6, ← mul_assoc]
    calc (e 4)⁻¹ * (e 4)⁻¹ * (e 0)⁻¹ * (e 4)⁻¹ * (e 4)⁻¹ * β * β
        = (e 4)⁻¹ * (e 4)⁻¹ * (e 0)⁻¹ * (e 4)⁻¹ * (e 4)⁻¹ * (β * β) := by group
      _ = (e 4)⁻¹ * (e 4)⁻¹ * (e 0)⁻¹ * (e 4)⁻¹ * (e 4)⁻¹ * ((e 0)⁻¹ * e 2) := by rw [hbb]
      _ = 1 := by rw [← hT25]; group
  · simp only [evalWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      Bool.cond_true, Bool.cond_false, hu1, hu3, hu4, hu6, ← mul_assoc]
    calc e 3 * β * (e 4)⁻¹ * e 1 * β⁻¹ * e 4 * e 1
        = e 3 * (β * ((e 4)⁻¹ * e 1) * β⁻¹) * e 4 * e 1 := by group
      _ = e 3 * (e 3 * e 1 * (e 4)⁻¹) * e 4 * e 1 := by rw [hU]
      _ = (e 3 * e 3) * (e 1 * e 1) := by group
      _ = 1 := by rw [hzz, he11, mul_one]

end Final

end CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition
