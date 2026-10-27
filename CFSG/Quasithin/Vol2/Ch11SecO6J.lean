module

public import CFSG.Quasithin.Vol2.Ch11SecO6C

public section

namespace CFSG.Quasithin.Vol2.Ch11.O6

open CFSG.Quasithin

variable {X : Type} [Group X] [Finite X] (r : ℕ) [Fact r.Prime]

theorem inv_of_actsScalar (hr2 : r ≠ 2)
    (hab : ∀ d ∈ CFSG.pCore r X, ∀ e ∈ CFSG.pCore r X, d * e = e * d)
    {s : X} (hs2 : s ^ 2 = 1) (hs : ActsScalar r (MulAut.conj s) (r - 1)) :
    ∀ d ∈ CFSG.pCore r X, s * d * s⁻¹ = d⁻¹ := by
  set A := CFSG.pCore r X with hA
  have hsA : ∀ d ∈ A, s * d * s⁻¹ ∈ A := fun d hd =>
    Subgroup.Normal.conj_mem CFSG.pCore_normal d hd s
  have hss : ∀ d : X, s * (s * d * s⁻¹) * s⁻¹ = d := by
    intro d
    have h1 : s * s = 1 := by rw [← sq, hs2]
    calc s * (s * d * s⁻¹) * s⁻¹ = (s * s) * d * (s * s)⁻¹ := by group
      _ = d := by rw [h1]; group
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := r) (G := X))
  have hodd : Odd (Nat.card A) := by
    rw [hk]
    exact Odd.pow ((Fact.out : r.Prime).odd_of_ne_two hr2)
  obtain ⟨h, hh⟩ := hodd
  have hroot : ∀ d ∈ A, (d * d) ^ (h + 1) = d := by
    intro d hd
    have h1 : d ^ Nat.card A = 1 := by
      have := pow_card_eq_one' (G := A) (x := ⟨d, hd⟩)
      exact congrArg Subtype.val this
    calc (d * d) ^ (h + 1) = d ^ (2 * h + 1) * d := by
          rw [← sq, ← pow_mul, show 2 * (h + 1) = 2 * h + 1 + 1 by ring, pow_succ]
      _ = d := by rw [← hh, h1, one_mul]
  let I : Subgroup ↥A :=
    { carrier := {d | s * (d : X) * s⁻¹ = (d : X)⁻¹}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, Subgroup.coe_mul] at ha hb ⊢
        calc s * (↑a * ↑b) * s⁻¹ = (s * ↑a * s⁻¹) * (s * ↑b * s⁻¹) := by group
          _ = (↑a)⁻¹ * (↑b)⁻¹ := by rw [ha, hb]
          _ = (↑a * ↑b)⁻¹ := by
            rw [mul_inv_rev, hab _ (inv_mem a.2) _ (inv_mem b.2)]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq, Subgroup.coe_inv] at ha ⊢
        calc s * (↑a)⁻¹ * s⁻¹ = (s * ↑a * s⁻¹)⁻¹ := by group
          _ = (↑a)⁻¹⁻¹ := by rw [ha] }
  have : Fact (IsPGroup r ↥A) := ⟨CFSG.pCore_isPGroup⟩
  have hItop : I ⊔ frattini ↥A = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨d, hd⟩ -
    set θ := s * d * s⁻¹ with hθ
    have hθA : θ ∈ A := hsA d hd
    have hPA : d * θ ∈ A := mul_mem hd hθA
    have hMA : d * θ⁻¹ ∈ A := mul_mem hd (inv_mem hθA)
    have hdθ : d * θ = θ * d := hab d hd θ hθA
    have hMP : Commute (d * θ⁻¹) (d * θ) := hab _ hMA _ hPA
    have hdec : d = (d * θ⁻¹) ^ (h + 1) * (d * θ) ^ (h + 1) := by
      rw [← hMP.mul_pow]
      have e : d * θ⁻¹ * (d * θ) = d * d := by
        calc d * θ⁻¹ * (d * θ) = d * θ⁻¹ * (θ * d) := by rw [hdθ]
          _ = d * d := by group
      rw [e, hroot d hd]
    have hMI : s * (d * θ⁻¹) ^ (h + 1) * s⁻¹ = ((d * θ⁻¹) ^ (h + 1))⁻¹ := by
      have h1 : s * (d * θ⁻¹) * s⁻¹ = (d * θ⁻¹)⁻¹ := by
        calc s * (d * θ⁻¹) * s⁻¹ = (s * d * s⁻¹) * (s * θ * s⁻¹)⁻¹ := by group
          _ = θ * d⁻¹ := by rw [← hθ, hθ, hss]
          _ = (d * θ⁻¹)⁻¹ := by group
      rw [← conj_pow, h1, inv_pow]
    have hPΦ : d * θ ∈ frattiniIn A := by
      have h1 := hs d hd
      rw [MulAut.conj_apply] at h1
      have h2 := pow_mem_frattiniIn (r := r) hd
      have e : d * θ = d ^ r * ((d ^ (r - 1))⁻¹ * θ) := by
        rw [← mul_pow_sub_one (Fact.out : r.Prime).ne_zero d]
        group
      rw [e]
      exact Subgroup.mul_mem _ h2 h1
    have hPΦ' : (⟨d * θ, hPA⟩ : ↥A) ∈ frattini ↥A := by
      obtain ⟨u, hu, hue⟩ := hPΦ
      have e : u = ⟨d * θ, hPA⟩ := Subtype.ext hue
      rw [← e]
      exact hu
    have hMI' : (⟨d * θ⁻¹, hMA⟩ : ↥A) ^ (h + 1) ∈ I := by
      change s * (((⟨d * θ⁻¹, hMA⟩ : ↥A) ^ (h + 1) : ↥A) : X) * s⁻¹ =
        (((⟨d * θ⁻¹, hMA⟩ : ↥A) ^ (h + 1) : ↥A) : X)⁻¹
      rw [SubgroupClass.coe_pow]
      exact hMI
    have hmem := Subgroup.mul_mem_sup hMI' (Subgroup.pow_mem _ hPΦ' (h + 1))
    convert hmem using 1
    apply Subtype.ext
    rw [Subgroup.coe_mul, SubgroupClass.coe_pow, SubgroupClass.coe_pow]
    exact hdec
  have hI := CFSG.lemma_1_7_a (R := ↥A) (p := r) I hItop
  intro d hd
  have h1 : (⟨d, hd⟩ : ↥A) ∈ I := by
    rw [hI]
    exact Subgroup.mem_top _
  exact h1

end CFSG.Quasithin.Vol2.Ch11.O6
