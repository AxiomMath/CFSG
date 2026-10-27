module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseModA

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even.C14

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F53Mod Equiv
open scoped commutatorElement

set_option maxRecDepth 100000 in
theorem fixS4F : ∀ σ : Perm (Fin 5), σ 4 = 4 → ∀ w : orth.W,
    (∀ b ∈ S5SylF, orth.act b w = w) → orth.act σ w = w := by
  decide +kernel

@[expose] def outF (r : orth.W) : Finset (Perm (Fin 5)) :=
  Finset.univ.filter fun σ => σ ^ 4 = 1 ∧ σ ∉ S5SylF ∧ orth.act σ r = r

@[expose] def FO4P (r : orth.W) : Prop :=
  ∀ σ ∈ outF r, ∀ τ ∈ outF r, (σ⁻¹ * τ) ^ 4 = 1 → σ⁻¹ * τ ∈ S5SylF

instance (r : orth.W) : Decidable (FO4P r) := by unfold FO4P; infer_instance

@[expose] def YLine (r : orth.W) : Prop := r ∈ commTwoF ∧ ¬ ∀ b ∈ S5SylF, orth.act b r = r

instance (r : orth.W) : Decidable (YLine r) := by unfold YLine; infer_instance

set_option maxRecDepth 100000 in
theorem fo4F : ∀ r : orth.W, YLine r → FO4P r := by
  decide +kernel

@[expose] def FixComm (t σ : Perm (Fin 5)) : Prop :=
  ∀ u : orth.W, orth.act σ (orth.act t u * u⁻¹) = orth.act t u * u⁻¹

instance (t σ : Perm (Fin 5)) : Decidable (FixComm t σ) := by unfold FixComm; infer_instance

@[expose] def cTwoF (t : Perm (Fin 5)) : Finset (Perm (Fin 5)) :=
  Finset.univ.filter fun σ => σ ^ 4 = 1 ∧ FixComm t σ

@[expose] def FO8P (t s : Perm (Fin 5)) : Prop :=
  ∃ x₀ : orth.W, orth.act t x₀ ≠ x₀ ∧ ∀ σ ∈ cTwoF t, (s⁻¹ * σ) ^ 4 = 1 →
    (orth.act σ x₀ = x₀ ∨ orth.act (t * σ) x₀ = x₀)

instance (t s : Perm (Fin 5)) : Decidable (FO8P t s) := by unfold FO8P; infer_instance

@[expose] def FO8H (x y : Fin 5) (s : Perm (Fin 5)) : Prop :=
  x ≠ y ∧ swap x y ∈ S5SylF ∧ s ∈ cTwoF (swap x y) ∧ s ≠ 1 ∧ s ≠ swap x y

instance (x y : Fin 5) (s : Perm (Fin 5)) : Decidable (FO8H x y s) := by
  unfold FO8H; infer_instance

set_option maxRecDepth 100000 in
theorem fo8F : ∀ x y : Fin 5, ∀ s : Perm (Fin 5), FO8H x y s → FO8P (swap x y) s := by
  decide +kernel

variable {G : Type} [Group G] {X S Z : Subgroup G}

theorem act_eq_of_commute (D : Dict5 X S Z) (x : ↥X) (v : orth.W)
    (h : (x : G) * D.φ v = D.φ v * x) : orth.act (D.ψ x) v = v := by
  apply D.inj
  rw [D.act_eq, h, mul_inv_cancel_right]

theorem commute_of_act_eq (D : Dict5 X S Z) (x : ↥X) (v : orth.W)
    (h : orth.act (D.ψ x) v = v) : (x : G) * D.φ v = D.φ v * x := by
  have e := D.act_eq x v
  rw [h] at e
  calc (x : G) * D.φ v = ((x : G) * D.φ v * (x : G)⁻¹) * x := by group
    _ = D.φ v * x := by rw [← e]

theorem psi_pow_four (D : Dict5 X S Z) (x : ↥X) (h : (x : G) ^ 4 = 1) : D.ψ x ^ 4 = 1 := by
  have hx : x ^ 4 = 1 := Subtype.ext (by simpa using h)
  rw [← map_pow, hx, map_one]

theorem mem_centralizer_fix (D : Dict5 X S Z) (x : ↥X) (h4 : D.ψ x 4 = 4) :
    (x : G) ∈ Subgroup.centralizer
      ((Z ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) : Set G) := by
  rw [D.fix_eq]
  exact (D.mem_centralizer_map_iff _ x).mpr fun w hw =>
    fixS4F _ h4 w fun b hb => hw b ((mem_S5Syl_iff b).mpr hb)

theorem inv_mul_mem_of_commute (D : Dict5 X S Z) {y : G} (hyY : y ∈ ⁅⁅Z, S⁆, S⁆)
    (hyC : y ∉ Z ⊓ Subgroup.centralizer (S : Set G)) {a b : G} (ha : a ∈ X) (hb : b ∈ X)
    (hay : a * y = y * a) (hby : b * y = y * b) (ha4 : a ^ 4 = 1) (hb4 : b ^ 4 = 1)
    (hab4 : (a⁻¹ * b) ^ 4 = 1) (haS : a ∉ S) (hbS : b ∉ S) : a⁻¹ * b ∈ S := by
  rw [D.comm_comm_eq] at hyY
  obtain ⟨r, hr, rfl⟩ := hyY
  have hline : YLine r := by
    refine ⟨(mem_commIter_two_iff r).mp hr, fun hfix => hyC ?_⟩
    rw [D.fix_eq]
    exact ⟨r, fun b' hb' => hfix b' ((mem_S5Syl_iff b').mp hb'), rfl⟩
  have hout : ∀ (c : G) (hc : c ∈ X), c * D.φ r = D.φ r * c → c ^ 4 = 1 → c ∉ S →
      D.ψ ⟨c, hc⟩ ∈ outF r := by
    intro c hc hcy hc4 hcS
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, psi_pow_four D _ hc4, fun hm => ?_,
      act_eq_of_commute D _ r hcy⟩
    exact hcS ((D.mem_S_iff ⟨c, hc⟩).mpr ((mem_S5Syl_iff _).mpr hm))
  have hst : (D.ψ ⟨a, ha⟩)⁻¹ * D.ψ ⟨b, hb⟩ = D.ψ (⟨a, ha⟩⁻¹ * ⟨b, hb⟩) := by
    rw [map_mul, map_inv]
  have h4 : ((D.ψ ⟨a, ha⟩)⁻¹ * D.ψ ⟨b, hb⟩) ^ 4 = 1 := by
    rw [hst]
    exact psi_pow_four D _ (by simpa using hab4)
  have hm := fo4F r hline _ (hout a ha hay ha4 haS) _ (hout b hb hby hb4 hbS) h4
  rw [hst] at hm
  exact (D.mem_S_iff _).mpr ((mem_S5Syl_iff _).mpr hm)

theorem fixComm_of_commute (D : Dict5 X S Z) (xz x : ↥X)
    (h : ∀ w ∈ Z, (x : G) * ⁅(xz : G), w⁆ = ⁅(xz : G), w⁆ * x) : FixComm (D.ψ xz) (D.ψ x) := by
  intro u
  refine act_eq_of_commute D x _ ?_
  have e : D.φ (orth.act (D.ψ xz) u * u⁻¹) = ⁅(xz : G), D.φ u⁆ := by
    rw [map_mul, map_inv, D.act_eq, commutatorElement_def]
  rw [e]
  exact h _ (D.φ_mem u)

theorem exists_of_transposition (D : Dict5 X S Z) {z : G} (hzS : z ∈ S)
    (hzQ : z ∉ pCoreOf 2 X) (hzidx : (Z ⊓ Subgroup.centralizer ({z} : Set G)).relIndex Z = 2)
    {y : G} (hy : y ∈ X) (hy4 : y ^ 4 = 1) (hyc : ∀ w ∈ Z, y * ⁅z, w⁆ = ⁅z, w⁆ * y)
    (hy1 : y ∉ pCoreOf 2 X) (hyz : z⁻¹ * y ∉ pCoreOf 2 X) :
    ∃ x ∈ Z, z * x ≠ x * z ∧ ∀ h ∈ X, h ^ 4 = 1 → (y⁻¹ * h) ^ 4 = 1 →
      (∀ w ∈ Z, h * ⁅z, w⁆ = ⁅z, w⁆ * h) → h * x = x * h ∨ z * h * x = x * (z * h) := by
  set xz : ↥X := ⟨z, D.S_le hzS⟩ with hxz
  set xy : ↥X := ⟨y, hy⟩ with hxy
  have ht1 : D.ψ xz ≠ 1 := fun h => hzQ ((D.ker_iff xz).mp h)
  have hidx : idx orth (D.ψ xz) = 2 := by
    rw [← D.relIndex_centralizer_eq xz]
    exact hzidx
  obtain ⟨p, q, hpq, htpq⟩ := ((transvections _ ht1).2).mp hidx
  have htS : D.ψ xz ∈ S5SylF := (mem_S5Syl_iff _).mp (D.ψ_mem_S5Syl hzS)
  have hmemc : ∀ (c : G) (hc : c ∈ X), c ^ 4 = 1 → (∀ w ∈ Z, c * ⁅z, w⁆ = ⁅z, w⁆ * c) →
      D.ψ ⟨c, hc⟩ ∈ cTwoF (D.ψ xz) := fun c hc hc4 hcc =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, psi_pow_four D _ hc4,
      fixComm_of_commute D xz ⟨c, hc⟩ hcc⟩
  have hs1 : D.ψ xy ≠ 1 := fun h => hy1 ((D.ker_iff xy).mp h)
  have hst : D.ψ xy ≠ D.ψ xz := fun h =>
    hyz ((D.ker_iff (xz⁻¹ * xy)).mp (by rw [map_mul, map_inv, h, inv_mul_cancel]))
  have hH : FO8H p q (D.ψ xy) := by
    unfold FO8H
    rw [← htpq]
    exact ⟨hpq, htS, hmemc y hy hy4 hyc, hs1, hst⟩
  obtain ⟨x₀, hx₀t, hx₀⟩ := fo8F p q _ hH
  rw [← htpq] at hx₀t hx₀
  refine ⟨D.φ x₀, D.φ_mem x₀, fun h => hx₀t (act_eq_of_commute D xz x₀ h), ?_⟩
  intro h hh hh4 hyh4 hhc
  have h4 : ((D.ψ xy)⁻¹ * D.ψ ⟨h, hh⟩) ^ 4 = 1 := by
    rw [← map_inv, ← map_mul]
    exact psi_pow_four D _ (by simpa using hyh4)
  rcases hx₀ _ (hmemc h hh hh4 hhc) h4 with h1 | h1
  · exact Or.inl (commute_of_act_eq D ⟨h, hh⟩ x₀ h1)
  · rw [← map_mul] at h1
    have h2 := commute_of_act_eq D (xz * (⟨h, hh⟩ : ↥X)) x₀ h1
    have e : ((xz * (⟨h, hh⟩ : ↥X) : ↥X) : G) = z * h := rfl
    rw [e] at h2
    exact Or.inr h2

end CFSG.Quasithin.F53.Stellmacher.S43.Even.C14
