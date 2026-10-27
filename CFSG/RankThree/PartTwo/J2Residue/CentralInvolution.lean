module

public import CFSG.RankThree.PartTwo.J2Residue.LinAlg
import CFSG.RankThree.PartTwo.Sec16.Kcd166.KleinDim
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.RankThree.PartTwo.J2Residue

variable {K : Type*} [Field K] {Γ : Type*} [Group Γ] {V : Type*} [AddCommGroup V] [Module K V]

private lemma mem_ker_sub_one {ρ : Representation K Γ V} {s : Γ} {w : V} :
    w ∈ LinearMap.ker (ρ s - 1) ↔ ρ s w = w := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]

private lemma rho_mul_self {ρ : Representation K Γ V} {s : Γ} (hs : s * s = 1) :
    ρ s * ρ s = 1 := by
  rw [← map_mul, hs, map_one]

private lemma rho_comm {ρ : Representation K Γ V} {s t : Γ} (hst : s * t = t * s) :
    ρ s * ρ t = ρ t * ρ s := by
  rw [← map_mul, ← map_mul, hst]

private lemma mapsTo_ker_sub_one {ρ : Representation K Γ V} {s t : Γ}
    (hst : s * t = t * s) :
    ∀ w ∈ LinearMap.ker (ρ s - 1), ρ t w ∈ LinearMap.ker (ρ s - 1) := by
  intro w hw
  rw [mem_ker_sub_one] at hw ⊢
  have h := congrArg (fun f : V →ₗ[K] V => f w) (rho_comm (ρ := ρ) hst)
  simpa [Module.End.mul_apply, hw] using h

private lemma eq_neg_one_of_inf_ker_eq_bot (h2 : (2 : K) ≠ 0)
    {ρ : Representation K Γ V} {s : Γ} (hs : s * s = 1) {W : Submodule K V}
    (hW : ∀ w ∈ W, ρ s w ∈ W) (hbot : W ⊓ LinearMap.ker (ρ s - 1) = ⊥) :
    ∀ w ∈ W, ρ s w = -w := by
  intro w hw
  have hss : ρ s (ρ s w) = w := by
    have h := congrArg (fun f : V →ₗ[K] V => f w) (rho_mul_self (ρ := ρ) hs)
    simpa [Module.End.mul_apply] using h
  have hfix : ρ s ((2 : K)⁻¹ • (w + ρ s w)) = (2 : K)⁻¹ • (w + ρ s w) := by
    rw [map_smul, map_add, hss, add_comm (ρ s w) w]
  have hmem : (2 : K)⁻¹ • (w + ρ s w) ∈ W ⊓ LinearMap.ker (ρ s - 1) :=
    ⟨W.smul_mem _ (W.add_mem hw (hW w hw)), (mem_ker_sub_one (ρ := ρ)).mpr hfix⟩
  have hzero : (2 : K)⁻¹ • (w + ρ s w) = 0 := by
    have h := hmem
    rw [hbot] at h
    simpa using h
  have hsum : w + ρ s w = 0 := by
    have h := congrArg (fun x : V => (2 : K) • x) hzero
    simpa [smul_smul, mul_inv_cancel₀ h2] using h
  exact eq_neg_of_add_eq_zero_right hsum

private theorem finrank_formula (h2 : (2 : K) ≠ 0) [FiniteDimensional K V]
    {ρ : Representation K Γ V} {s t : Γ} (hs : s * s = 1) (ht : t * t = 1)
    (hst : s * t = t * s) :
    Module.finrank K V +
        2 * Module.finrank K ↥(LinearMap.ker (ρ s - 1) ⊓ LinearMap.ker (ρ t - 1)) =
      Module.finrank K (LinearMap.ker (ρ s - 1)) +
          Module.finrank K (LinearMap.ker (ρ t - 1)) +
        Module.finrank K (LinearMap.ker (ρ (s * t) - 1)) := by
  have h := CFSG.RankThree.PartTwo.Sec16.Kcd166.finrank_add_two_mul_finrank_inf
    (𝕜 := K) (V := V) h2 (s := ρ s) (t := ρ t)
    (rho_mul_self (ρ := ρ) hs) (rho_mul_self (ρ := ρ) ht) (rho_comm (ρ := ρ) hst)
  have hker : LinearMap.ker (ρ s * ρ t - 1) = LinearMap.ker (ρ (s * t) - 1) := by
    rw [← map_mul]
  rw [hker] at h
  exact h

private lemma mul_comm_of_sq_eq_one {s t : Γ} (hs : s * s = 1) (ht : t * t = 1)
    (hst : (s * t) * (s * t) = 1) : s * t = t * s := by
  have h1 : (s * t) * s = t := by
    have h : ((s * t) * s) * t = t * t := by rw [mul_assoc, hst, ht]
    exact mul_right_cancel h
  have h2 : (t * s) * s = t := by rw [mul_assoc, hs, mul_one]
  exact mul_right_cancel (h1.trans h2.symm)

private abbrev Esharp (E : Subgroup Γ) : Type _ := {x : Γ // x ∈ E ∧ x ≠ 1}

private def conjPerm {E : Subgroup Γ} [E.Normal] (g : Γ) : Equiv.Perm (Esharp E) where
  toFun x := ⟨g * x.1 * g⁻¹, Subgroup.Normal.conj_mem (inferInstance : E.Normal) x.1 x.2.1 g, by
    intro h
    apply x.2.2
    have := congrArg (fun y : Γ => g⁻¹ * y * g) h
    simpa [mul_assoc] using this⟩
  invFun x := ⟨g⁻¹ * x.1 * g, Subgroup.Normal.conj_mem' (inferInstance : E.Normal) x.1 x.2.1 g,
    by
      intro h
      apply x.2.2
      have := congrArg (fun y : Γ => g * y * g⁻¹) h
      simpa [mul_assoc] using this⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])

private def conjHom {E : Subgroup Γ} [E.Normal] : Γ →* Equiv.Perm (Esharp E) where
  toFun := conjPerm (E := E)
  map_one' := Equiv.ext fun x => by apply Subtype.ext; simp [conjPerm]
  map_mul' g h := Equiv.ext fun x => by apply Subtype.ext; simp [conjPerm, mul_assoc]

private lemma eq_one_of_isPerfect_of_isSolvable {G H : Type*} [Group G] [Group H]
    [Group.IsPerfect G] [Group.IsSolvable H] (f : G →* H) : f = 1 := by
  haveI : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hsub : Subsingleton f.range := by
    by_contra h
    haveI : Nontrivial f.range := not_subsingleton_iff_nontrivial.mp h
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  ext g
  have h1 : (⟨f g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩ : f.range) = 1 := Subsingleton.elim _ _
  exact congrArg Subtype.val h1

private lemma centralizes_of_card_four [Finite Γ] {E Λ : Subgroup Γ} [E.Normal]
    (hcard : Nat.card ↥E = 4) (hΛ : Group.IsPerfect Λ) (hEΛ : E ≤ Λ) :
    ∀ l ∈ Λ, ∀ s ∈ E, l * s = s * l := by
  classical
  have hcardsharp : Nat.card (Esharp E) ≤ 4 := by
    have h := Nat.card_le_card_of_injective (fun x : Esharp E => (⟨x.1, x.2.1⟩ : ↥E)) ?_
    · omega
    · intro x y hxy
      exact Subtype.ext (congrArg (fun z : ↥E => (z : Γ)) hxy)
  haveI : Group.IsPerfect ↥Λ := hΛ
  haveI : Group.IsSolvable (Equiv.Perm (Esharp E)) := Equiv.Perm.isSolvable hcardsharp
  let φ : ↥Λ →* Equiv.Perm (Esharp E) := (conjHom (E := E)).comp Λ.subtype
  have hφ : φ = 1 := eq_one_of_isPerfect_of_isSolvable φ
  intro l hl s hs
  by_cases hs1 : s = 1
  · subst hs1
    simp
  · have h1 : φ ⟨l, hl⟩ = 1 := by rw [hφ]; rfl
    have h2 := congrArg (fun σ : Equiv.Perm (Esharp E) =>
      ((σ ⟨s, hs, hs1⟩ : Esharp E) : Γ)) h1
    have h3 : l * s * l⁻¹ = s := by
      simpa [φ, conjHom, conjPerm] using h2
    calc l * s = (l * s * l⁻¹) * l := by group
      _ = s * l := by rw [h3]

private lemma exists_two_ne_one [Finite Γ] {E : Subgroup Γ} (hcard : 4 ≤ Nat.card ↥E) :
    ∃ a ∈ E, ∃ b ∈ E, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  classical
  haveI : Fintype ↥E := Fintype.ofFinite ↥E
  let S : Finset ↥E := Finset.univ.erase 1
  have hS : 3 ≤ S.card := by
    have h := Finset.card_erase_of_mem (Finset.mem_univ (1 : ↥E))
    have hc : Fintype.card ↥E = Nat.card ↥E := Nat.card_eq_fintype_card.symm
    rw [show S.card = (Finset.univ.erase (1 : ↥E)).card from rfl, h, Finset.card_univ]
    omega
  obtain ⟨a, haS⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  obtain ⟨b, hbS, hba⟩ := Finset.exists_mem_ne (show 1 < S.card by omega) a
  refine ⟨a.1, a.2, b.1, b.2, ?_, ?_, ?_⟩
  · intro h
    exact (show a ≠ (1 : ↥E) by simpa [S] using haS) (Subtype.ext h)
  · intro h
    exact (show b ≠ (1 : ↥E) by simpa [S] using hbS) (Subtype.ext h)
  · intro h
    exact hba (Subtype.ext h.symm)

private lemma exists_three_with_ne_mul [Finite Γ] {E : Subgroup Γ}
    (hE2 : ∀ s ∈ E, s * s = 1) (hcard : 8 ≤ Nat.card ↥E) :
    ∃ u ∈ E, ∃ a ∈ E, ∃ b ∈ E,
      u ≠ 1 ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ u ∧ b ≠ u ∧ b ≠ a ∧ b ≠ u * a := by
  classical
  haveI : Fintype ↥E := Fintype.ofFinite ↥E
  let S : Finset ↥E := Finset.univ.erase 1
  have hS : 7 ≤ S.card := by
    have h := Finset.card_erase_of_mem (Finset.mem_univ (1 : ↥E))
    have hc : Fintype.card ↥E = Nat.card ↥E := Nat.card_eq_fintype_card.symm
    rw [show S.card = (Finset.univ.erase (1 : ↥E)).card from rfl, h, Finset.card_univ]
    omega
  obtain ⟨u, huS⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  have hu1 : u ≠ 1 :=
    (Finset.mem_erase.mp (show u ∈ Finset.univ.erase (1 : ↥E) from huS)).1
  let T : Finset ↥E := S.erase u
  have hT : 6 ≤ T.card := by
    rw [show T.card = (S.erase u).card from rfl, Finset.card_erase_of_mem huS]
    omega
  obtain ⟨a, haT⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
  have haT' : a ∈ S.erase u := haT
  have hau : a ≠ u := (Finset.mem_erase.mp haT').1
  have haS : a ∈ S := (Finset.mem_erase.mp haT').2
  have ha1 : a ≠ 1 := (Finset.mem_erase.mp
    (show a ∈ Finset.univ.erase (1 : ↥E) from haS)).1
  have ha2 : a * a = (1 : ↥E) := Subtype.ext (hE2 a a.2)
  have hu2 : u * u = (1 : ↥E) := Subtype.ext (hE2 u u.2)
  have hua_a : u * a ≠ a := by
    intro h
    apply hu1
    have h1 : (u * a) * a = a * a := by rw [h]
    rw [mul_assoc, ha2, mul_one] at h1
    exact h1
  have hua_u : u * a ≠ u := by
    intro h
    apply ha1
    have h1 : u * (u * a) = u * u := by rw [h]
    rw [← mul_assoc, hu2, one_mul] at h1
    exact h1
  have hua_1 : u * a ≠ 1 := by
    intro h
    apply hau
    have h1 : (u * a) * a = (1 : ↥E) * a := by rw [h]
    rw [mul_assoc, ha2, mul_one, one_mul] at h1
    exact h1.symm
  have huaS : u * a ∈ S := Finset.mem_erase.mpr ⟨hua_1, Finset.mem_univ _⟩
  have huaT : u * a ∈ T.erase a :=
    Finset.mem_erase.mpr ⟨hua_a, Finset.mem_erase.mpr ⟨hua_u, huaS⟩⟩
  let U : Finset ↥E := (T.erase a).erase (u * a)
  have hU : 4 ≤ U.card := by
    rw [show U.card = ((T.erase a).erase (u * a)).card from rfl,
      Finset.card_erase_of_mem huaT, Finset.card_erase_of_mem haT]
    omega
  obtain ⟨b, hbU⟩ := Finset.card_pos.mp (show 0 < U.card by omega)
  have hbU' : b ∈ (T.erase a).erase (u * a) := hbU
  have hbua : b ≠ u * a := (Finset.mem_erase.mp hbU').1
  have hbTa : b ∈ T.erase a := (Finset.mem_erase.mp hbU').2
  have hba : b ≠ a := (Finset.mem_erase.mp hbTa).1
  have hbT : b ∈ T := (Finset.mem_erase.mp hbTa).2
  have hbu : b ≠ u := (Finset.mem_erase.mp (show b ∈ S.erase u from hbT)).1
  have hbS : b ∈ S := (Finset.mem_erase.mp (show b ∈ S.erase u from hbT)).2
  have hb1 : b ≠ 1 := (Finset.mem_erase.mp
    (show b ∈ Finset.univ.erase (1 : ↥E) from hbS)).1
  refine ⟨u.1, u.2, a.1, a.2, b.1, b.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; exact hu1 (Subtype.ext h)
  · intro h; exact ha1 (Subtype.ext h)
  · intro h; exact hb1 (Subtype.ext h)
  · intro h; exact hau (Subtype.ext h)
  · intro h; exact hbu (Subtype.ext h)
  · intro h; exact hba (Subtype.ext h)
  · intro h; exact hbua (Subtype.ext h)

private lemma exists_unique_nontrivial_of_card_two [Finite Γ] {E : Subgroup Γ}
    (hcard : Nat.card ↥E = 2) :
    ∃ z : Γ, z ∈ E ∧ z ≠ 1 ∧ ∀ s ∈ E, s = 1 ∨ s = z := by
  obtain ⟨z0, hz0, hzuniq⟩ := (Nat.card_eq_two_iff' (1 : ↥E)).mp hcard
  refine ⟨z0.1, z0.2, ?_, ?_⟩
  · intro h
    exact hz0 (Subtype.ext h)
  · intro s hs
    by_cases hs1 : s = 1
    · exact Or.inl hs1
    · right
      have hs' : (⟨s, hs⟩ : ↥E) ≠ 1 := by
        intro h
        exact hs1 (congrArg Subtype.val h)
      have h := hzuniq ⟨s, hs⟩ hs'
      exact congrArg Subtype.val h

private lemma nontrivial_of_isIrreducible {ρ : Representation K Γ V} (hρ : ρ.IsIrreducible) :
    Nontrivial V := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  haveI : Subsingleton V := h
  haveI : IsSimpleOrder (Subrepresentation ρ) := hρ
  haveI : Nontrivial (Subrepresentation ρ) := IsSimpleOrder.toNontrivial
  obtain ⟨x, y, hxy⟩ := (inferInstance : Nontrivial (Subrepresentation ρ)).exists_pair_ne
  apply hxy
  apply Subrepresentation.toSubmodule_injective
  have hx : x.toSubmodule = ⊥ :=
    (Submodule.eq_bot_iff _).mpr (fun v _ => Subsingleton.elim v 0)
  have hy : y.toSubmodule = ⊥ :=
    (Submodule.eq_bot_iff _).mpr (fun v _ => Subsingleton.elim v 0)
  rw [hx, hy]

private theorem eight_le_inf_eq_bot (h2 : (2 : K) ≠ 0) [FiniteDimensional K V]
    {ρ : Representation K Γ V} {E : Subgroup Γ}
    (hE2 : ∀ s ∈ E, s * s = 1)
    (h3 : ∀ s ∈ E, s ≠ 1 → Module.finrank K (LinearMap.ker (ρ s - 1)) ≤ 3)
    (h8 : 8 ≤ Module.finrank K V)
    {a b : Γ} (ha : a ∈ E) (hb : b ∈ E) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) :
    LinearMap.ker (ρ a - 1) ⊓ LinearMap.ker (ρ b - 1) = ⊥ := by
  have ha2 : a * a = 1 := hE2 a ha
  have hb2 : b * b = 1 := hE2 b hb
  have habE : a * b ∈ E := E.mul_mem ha hb
  have hab2 : (a * b) * (a * b) = 1 := hE2 (a * b) habE
  have hcomm : a * b = b * a := mul_comm_of_sq_eq_one ha2 hb2 hab2
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hab
    have h1 : (a * b) * b = (1 : Γ) * b := by rw [h]
    rw [mul_assoc, hb2, mul_one, one_mul] at h1
    exact h1
  have hf := finrank_formula (ρ := ρ) h2 ha2 hb2 hcomm
  have hca := h3 a ha ha1
  have hcb := h3 b hb hb1
  have hcab := h3 (a * b) habE hab1
  have hd : Module.finrank K
      ↥(LinearMap.ker (ρ a - 1) ⊓ LinearMap.ker (ρ b - 1)) = 0 := by omega
  exact Submodule.finrank_eq_zero.mp hd

private theorem eight_le_card_lt_eight (h2 : (2 : K) ≠ 0) [Finite Γ] [FiniteDimensional K V]
    {ρ : Representation K Γ V} {E : Subgroup Γ}
    (hE2 : ∀ s ∈ E, s * s = 1)
    (h3 : ∀ s ∈ E, s ≠ 1 → Module.finrank K (LinearMap.ker (ρ s - 1)) ≤ 3)
    (h8 : 8 ≤ Module.finrank K V) : Nat.card ↥E < 8 := by
  by_contra hlt
  have hlt8 : 8 ≤ Nat.card ↥E := by omega
  obtain ⟨u, huE, a, haE, b, hbE, hu1, ha1, hb1, hau, hbu, hba, hbua⟩ :=
    exists_three_with_ne_mul hE2 hlt8
  have hu2 : u * u = 1 := hE2 u huE
  have ha2 : a * a = 1 := hE2 a haE
  have hb2 : b * b = 1 := hE2 b hbE
  have hu_mul_a : u * a = a * u :=
    mul_comm_of_sq_eq_one hu2 ha2 (hE2 (u * a) (E.mul_mem huE haE))
  have hu_mul_b : u * b = b * u :=
    mul_comm_of_sq_eq_one hu2 hb2 (hE2 (u * b) (E.mul_mem huE hbE))
  have hpert_ua : LinearMap.ker (ρ u - 1) ⊓ LinearMap.ker (ρ a - 1) = ⊥ :=
    eight_le_inf_eq_bot (ρ := ρ) h2 hE2 h3 h8 huE haE hu1 ha1 hau.symm
  have hpert_ub : LinearMap.ker (ρ u - 1) ⊓ LinearMap.ker (ρ b - 1) = ⊥ :=
    eight_le_inf_eq_bot (ρ := ρ) h2 hE2 h3 h8 huE hbE hu1 hb1 hbu.symm
  have hua1 : u * a ≠ 1 := by
    intro h
    apply hau
    have h1 : (u * a) * a = (1 : Γ) * a := by rw [h]
    rw [mul_assoc, ha2, mul_one, one_mul] at h1
    exact h1.symm
  have hab_ne_u : a * b ≠ u := by
    intro h
    apply hbua
    have h1 : a * (a * b) = a * u := by rw [h]
    rw [← mul_assoc, ha2, one_mul] at h1
    exact h1.trans (mul_comm_of_sq_eq_one ha2 hu2 (hE2 (a * u) (E.mul_mem haE huE)))
  have habE : a * b ∈ E := E.mul_mem haE hbE
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hba
    have h1 : (a * b) * b = (1 : Γ) * b := by rw [h]
    rw [mul_assoc, hb2, mul_one, one_mul] at h1
    exact h1.symm
  have hpert_uab : LinearMap.ker (ρ u - 1) ⊓ LinearMap.ker (ρ (a * b) - 1) = ⊥ :=
    eight_le_inf_eq_bot (ρ := ρ) (a := u) (b := a * b) h2 hE2 h3 h8 huE habE hu1 hab1
      hab_ne_u.symm
  have hfix_u : LinearMap.ker (ρ u - 1) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    have ha_neg : ρ a w = -w :=
      eq_neg_one_of_inf_ker_eq_bot (s := a) h2 ha2
        (mapsTo_ker_sub_one (ρ := ρ) (s := u) (t := a) hu_mul_a) hpert_ua w hw
    have hb_neg : ρ b w = -w :=
      eq_neg_one_of_inf_ker_eq_bot (s := b) h2 hb2
        (mapsTo_ker_sub_one (ρ := ρ) (s := u) (t := b) hu_mul_b) hpert_ub w hw
    have hwab : w ∈ LinearMap.ker (ρ (a * b) - 1) := by
      rw [mem_ker_sub_one, map_mul, Module.End.mul_apply, hb_neg, map_neg, ha_neg, neg_neg]
    have hmem : w ∈ LinearMap.ker (ρ u - 1) ⊓ LinearMap.ker (ρ (a * b) - 1) := ⟨hw, hwab⟩
    rw [hpert_uab] at hmem
    simpa using hmem
  have hf := finrank_formula (ρ := ρ) (s := u) (t := a) h2 hu2 ha2 hu_mul_a
  have hcu0 : Module.finrank K (LinearMap.ker (ρ u - 1)) = 0 := by
    rw [hfix_u]
    simp
  have hinf0 : Module.finrank K
      ↥(LinearMap.ker (ρ u - 1) ⊓ LinearMap.ker (ρ a - 1)) = 0 := by
    rw [hpert_ua]
    simp
  have hca := h3 a haE ha1
  have hcua : Module.finrank K (LinearMap.ker (ρ (u * a) - 1)) ≤ 3 :=
    h3 (u * a) (E.mul_mem huE haE) hua1
  omega

theorem exists_neg_one_of_eight_le (h2 : (2 : K) ≠ 0) [Finite Γ] [FiniteDimensional K V]
    {ρ : Representation K Γ V} (hρ : ρ.IsIrreducible) {E Λ : Subgroup Γ} (hEn : E.Normal)
    (hE2 : ∀ s ∈ E, s * s = 1) (hE : E ≠ ⊥) (hΛ : Group.IsPerfect Λ) (hEΛ : E ≤ Λ)
    (h3 : ∀ s ∈ E, s ≠ 1 → Module.finrank K (LinearMap.ker (ρ s - 1)) ≤ 3)
    (h8 : 8 ≤ Module.finrank K V) :
    ∃ z ∈ E, z ≠ 1 ∧ ρ z = -1 ∧ ∀ s ∈ E, s = 1 ∨ s = z := by
  classical
  haveI : E.Normal := hEn
  have hcardlt : Nat.card ↥E < 8 := eight_le_card_lt_eight h2 hE2 h3 h8
  have hE2grp : IsPGroup 2 ↥E := by
    intro x
    refine ⟨1, ?_⟩
    have hx : (x : Γ) * (x : Γ) = 1 := hE2 x x.2
    rw [show 2 ^ 1 = 2 by norm_num]
    exact Subtype.ext (by simpa [pow_two] using hx)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hE2grp
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hpos
    · exfalso
      apply hE
      rw [Subgroup.eq_bot_iff_card, hk, hk0]
      norm_num
    · exact hpos
  have hk3 : k < 3 := by
    have h2k : 2 ^ k < 8 := by rw [← hk]; exact hcardlt
    have h : 2 ^ k < 2 ^ 3 := by simpa using h2k
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h
  have hkcases : k = 1 ∨ k = 2 := by omega
  rcases hkcases with hk1 | hk2
  · have hcard2 : Nat.card ↥E = 2 := by rw [hk, hk1]; norm_num
    obtain ⟨z, hzE, hz1, hzall⟩ := exists_unique_nontrivial_of_card_two hcard2
    have hz2 : z * z = 1 := hE2 z hzE
    have hzcentral : ∀ g : Γ, z * g = g * z := by
      intro g
      have hmem : g * z * g⁻¹ ∈ E :=
        Subgroup.Normal.conj_mem (inferInstance : E.Normal) z hzE g
      have hne : g * z * g⁻¹ ≠ 1 := by
        intro h
        apply hz1
        have h' := congrArg (fun y : Γ => g⁻¹ * y * g) h
        simpa [mul_assoc] using h'
      have hz' : g * z * g⁻¹ = z := by
        rcases hzall (g * z * g⁻¹) hmem with h1 | h1
        · exact absurd h1 hne
        · exact h1
      have h2' := congrArg (fun y : Γ => y * g) hz'
      have h2'' : g * z = z * g := by simpa [mul_assoc] using h2'
      exact h2''.symm
    have hzρne : ρ z ≠ 1 := by
      intro h
      have htop : LinearMap.ker (ρ z - 1) = ⊤ := by
        rw [h]
        simp
      have hle := h3 z hzE hz1
      rw [htop] at hle
      simp at hle
      omega
    refine ⟨z, hzE, hz1, ?_, hzall⟩
    apply rho_eq_neg_one_of_commute hρ _ hz2 hzρne
    intro g
    rw [← map_mul, ← map_mul, hzcentral g]
  · exfalso
    have hcard4 : Nat.card ↥E = 4 := by rw [hk, hk2]; norm_num
    obtain ⟨a, haE, b, hbE, ha1, hb1, hab⟩ :=
      exists_two_ne_one (by omega : 4 ≤ Nat.card ↥E)
    have hcent := centralizes_of_card_four hcard4 hΛ hEΛ
    have ha2 : a * a = 1 := hE2 a haE
    have hb2 : b * b = 1 := hE2 b hbE
    have habE : a * b ∈ E := E.mul_mem haE hbE
    have hab2 : (a * b) * (a * b) = 1 := hE2 (a * b) habE
    have hab_comm : a * b = b * a := mul_comm_of_sq_eq_one ha2 hb2 hab2
    have hab1 : a * b ≠ 1 := by
      intro h
      apply hab
      have h1 : (a * b) * b = (1 : Γ) * b := by rw [h]
      rw [mul_assoc, hb2, mul_one, one_mul] at h1
      exact h1
    have hinv_a : ∀ g ∈ Λ, ∀ w ∈ LinearMap.ker (ρ a - 1),
        ρ g w ∈ LinearMap.ker (ρ a - 1) := by
      intro g hg w hw
      have hga : g * a = a * g := hcent g hg a haE
      exact mapsTo_ker_sub_one (ρ := ρ) (s := a) (t := g) hga.symm w hw
    have hinv_ab : ∀ w ∈ LinearMap.ker (ρ a - 1), ρ b w ∈ LinearMap.ker (ρ a - 1) :=
      mapsTo_ker_sub_one (ρ := ρ) (s := a) (t := b) hab_comm
    have hbot_ab : LinearMap.ker (ρ a - 1) ⊓ LinearMap.ker (ρ b - 1) = ⊥ :=
      eight_le_inf_eq_bot (ρ := ρ) h2 hE2 h3 h8 haE hbE ha1 hb1 hab
    have hneg_b : ∀ w ∈ LinearMap.ker (ρ a - 1), ρ b w = -w :=
      eq_neg_one_of_inf_ker_eq_bot h2 hb2 hinv_ab hbot_ab
    have heven_a : Even (Module.finrank K (LinearMap.ker (ρ a - 1))) :=
      even_finrank_of_isPerfect h2 ρ hΛ (LinearMap.ker (ρ a - 1)) hinv_a (hEΛ hbE) hneg_b
    have hinv_b : ∀ g ∈ Λ, ∀ w ∈ LinearMap.ker (ρ b - 1),
        ρ g w ∈ LinearMap.ker (ρ b - 1) := by
      intro g hg w hw
      have hgb : g * b = b * g := hcent g hg b hbE
      exact mapsTo_ker_sub_one (ρ := ρ) (s := b) (t := g) hgb.symm w hw
    have hinv_ba : ∀ w ∈ LinearMap.ker (ρ b - 1), ρ a w ∈ LinearMap.ker (ρ b - 1) :=
      mapsTo_ker_sub_one (ρ := ρ) (s := b) (t := a) hab_comm.symm
    have hbot_ba : LinearMap.ker (ρ b - 1) ⊓ LinearMap.ker (ρ a - 1) = ⊥ :=
      eight_le_inf_eq_bot (ρ := ρ) (a := b) (b := a) h2 hE2 h3 h8 hbE haE hb1 ha1 hab.symm
    have hneg_a : ∀ w ∈ LinearMap.ker (ρ b - 1), ρ a w = -w :=
      eq_neg_one_of_inf_ker_eq_bot h2 ha2 hinv_ba hbot_ba
    have heven_b : Even (Module.finrank K (LinearMap.ker (ρ b - 1))) :=
      even_finrank_of_isPerfect h2 ρ hΛ (LinearMap.ker (ρ b - 1)) hinv_b (hEΛ haE) hneg_a
    have hf := finrank_formula (ρ := ρ) (s := a) (t := b) h2 ha2 hb2 hab_comm
    have hinf0 : Module.finrank K
        ↥(LinearMap.ker (ρ a - 1) ⊓ LinearMap.ker (ρ b - 1)) = 0 := by
      rw [hbot_ab]
      simp
    have hca := h3 a haE ha1
    have hcb := h3 b hbE hb1
    have hcab := h3 (a * b) habE hab1
    obtain ⟨ra, hra⟩ := heven_a
    obtain ⟨rb, hrb⟩ := heven_b
    omega

private lemma apply_quadratic {ρ : Representation K Γ V} {σ : Γ}
    (hσ3 : ρ σ * ρ σ + ρ σ + 1 = 0) (w : V) :
    ρ σ (ρ σ w) + ρ σ w + w = 0 := by
  have h := congrArg (fun f : V →ₗ[K] V => f w) hσ3
  simpa [Module.End.mul_apply] using h

private theorem cube_parity (h2 : (2 : K) ≠ 0) [FiniteDimensional K V]
    {ρ : Representation K Γ V} {E Λ : Subgroup Γ}
    (hΛ : Group.IsPerfect Λ) (hEΛ : E ≤ Λ) (hE2 : ∀ s ∈ E, s * s = 1)
    {s : Γ} (hs : s ∈ E) (hs1 : s ≠ 1) :
    ∃ m : ℕ, Module.finrank K V =
      Module.finrank K (LinearMap.ker (ρ s - 1)) + 2 * m := by
  have hs2 : s * s = 1 := hE2 s hs
  have heven : Even (Module.finrank K (LinearMap.ker (ρ s + 1))) :=
    even_finrank_ker_add_one_of_isPerfect h2 ρ hΛ (hEΛ hs) hs2
  obtain ⟨m, hm⟩ := heven
  have hf := finrank_eq_add_of_eq_neg_one (h2 := h2) (V := V) (x := ρ s)
    (z := (-1 : V →ₗ[K] V)) (rho_mul_self (ρ := ρ) hs2) rfl
  have hker : LinearMap.ker (ρ s * (-1) - 1) = LinearMap.ker (ρ s + 1) := by
    have hneg : ρ s * (-1) - 1 = -(ρ s + 1) := by
      rw [mul_neg_one]
      abel
    rw [hneg, LinearMap.ker_neg]
  rw [hker] at hf
  exact ⟨m, by omega⟩

private theorem cube_structure (h2 : (2 : K) ≠ 0) [Finite Γ] [FiniteDimensional K V]
    {ρ : Representation K Γ V} {E Λ : Subgroup Γ}
    (hΛ : Group.IsPerfect Λ) (hEΛ : E ≤ Λ) (hE2 : ∀ s ∈ E, s * s = 1)
    (h2' : ∀ s ∈ E, s ≠ 1 → Module.finrank K (LinearMap.ker (ρ s - 1)) ≤ 2)
    {a0 b0 : Γ} (ha0 : a0 ∈ E) (hb0 : b0 ∈ E) (ha01 : a0 ≠ 1) (hb01 : b0 ≠ 1)
    (ha0b0 : a0 ≠ b0)
    (hn : Module.finrank K V = 3 ∨ Module.finrank K V = 6) :
    ((∀ s ∈ E, s ≠ 1 → Module.finrank K (LinearMap.ker (ρ s - 1)) = 1) ∧
      (∀ a ∈ E, ∀ b ∈ E, a ≠ 1 → b ≠ 1 → a ≠ b →
        LinearMap.ker (ρ a - 1) ⊓ LinearMap.ker (ρ b - 1) = ⊥)) ∨
    ((∀ s ∈ E, s ≠ 1 → Module.finrank K (LinearMap.ker (ρ s - 1)) = 2) ∧
      (∀ a ∈ E, ∀ b ∈ E, a ≠ 1 → b ≠ 1 → a ≠ b →
        LinearMap.ker (ρ a - 1) ⊓ LinearMap.ker (ρ b - 1) = ⊥)) := by
  rcases hn with hn3 | hn6
  · have hc1 : ∀ s ∈ E, s ≠ 1 →
        Module.finrank K (LinearMap.ker (ρ s - 1)) = 1 := by
      intro s hs hs1
      obtain ⟨m, hm⟩ := cube_parity (ρ := ρ) h2 hΛ hEΛ hE2 hs hs1
      have hle := h2' s hs hs1
      omega
    refine Or.inl ⟨hc1, ?_⟩
    intro a ha b hb ha1 hb1 hab
    have ha2 : a * a = 1 := hE2 a ha
    have hb2 : b * b = 1 := hE2 b hb
    have habE : a * b ∈ E := E.mul_mem ha hb
    have hab2 : (a * b) * (a * b) = 1 := hE2 (a * b) habE
    have hcomm : a * b = b * a := mul_comm_of_sq_eq_one ha2 hb2 hab2
    have hab1 : a * b ≠ 1 := by
      intro h
      apply hab
      have h1 : (a * b) * b = (1 : Γ) * b := by rw [h]
      rw [mul_assoc, hb2, mul_one, one_mul] at h1
      exact h1
    have hf := finrank_formula (ρ := ρ) h2 ha2 hb2 hcomm
    have hca := hc1 a ha ha1
    have hcb := hc1 b hb hb1
    have hcab := hc1 (a * b) habE hab1
    have hd : Module.finrank K
        ↥(LinearMap.ker (ρ a - 1) ⊓ LinearMap.ker (ρ b - 1)) = 0 := by omega
    exact Submodule.finrank_eq_zero.mp hd
  · have hc0 : Module.finrank K (LinearMap.ker (ρ a0 - 1)) = 2 ∧
        Module.finrank K (LinearMap.ker (ρ b0 - 1)) = 2 ∧
        Module.finrank K (LinearMap.ker (ρ (a0 * b0) - 1)) = 2 := by
      have ha02 : a0 * a0 = 1 := hE2 a0 ha0
      have hb02 : b0 * b0 = 1 := hE2 b0 hb0
      have hab0E : a0 * b0 ∈ E := E.mul_mem ha0 hb0
      have hab02 : (a0 * b0) * (a0 * b0) = 1 := hE2 (a0 * b0) hab0E
      have hcomm0 : a0 * b0 = b0 * a0 := mul_comm_of_sq_eq_one ha02 hb02 hab02
      have hab01 : a0 * b0 ≠ 1 := by
        intro h
        apply ha0b0
        have h1 : (a0 * b0) * b0 = (1 : Γ) * b0 := by rw [h]
        rw [mul_assoc, hb02, mul_one, one_mul] at h1
        exact h1
      have hf0 := finrank_formula (ρ := ρ) h2 ha02 hb02 hcomm0
      have hca0 := h2' a0 ha0 ha01
      have hcb0 := h2' b0 hb0 hb01
      have hcab0 := h2' (a0 * b0) hab0E hab01
      have hca0eq : Module.finrank K (LinearMap.ker (ρ a0 - 1)) = 2 := by omega
      have hcb0eq : Module.finrank K (LinearMap.ker (ρ b0 - 1)) = 2 := by omega
      have hcab0eq : Module.finrank K (LinearMap.ker (ρ (a0 * b0) - 1)) = 2 := by omega
      exact ⟨hca0eq, hcb0eq, hcab0eq⟩
    have hc2 : ∀ s ∈ E, s ≠ 1 →
        Module.finrank K (LinearMap.ker (ρ s - 1)) = 2 := by
      intro s hs hs1
      by_cases hsa : s = a0
      · subst hsa
        exact hc0.1
      · have ha02 : a0 * a0 = 1 := hE2 a0 ha0
        have hs2 : s * s = 1 := hE2 s hs
        have hsa0E : s * a0 ∈ E := E.mul_mem hs ha0
        have hsa02 : (s * a0) * (s * a0) = 1 := hE2 (s * a0) hsa0E
        have hcomm : s * a0 = a0 * s := mul_comm_of_sq_eq_one hs2 ha02 hsa02
        have hsa01 : s * a0 ≠ 1 := by
          intro h
          apply hsa
          have h1 : (s * a0) * a0 = (1 : Γ) * a0 := by rw [h]
          rw [mul_assoc, ha02, mul_one, one_mul] at h1
          exact h1
        have hf := finrank_formula (ρ := ρ) (s := s) (t := a0) h2 hs2 ha02 hcomm
        have hcs := h2' s hs hs1
        have hcsa0 := h2' (s * a0) hsa0E hsa01
        omega
    refine Or.inr ⟨hc2, ?_⟩
    intro a ha b hb ha1 hb1 hab
    have ha2 : a * a = 1 := hE2 a ha
    have hb2 : b * b = 1 := hE2 b hb
    have habE : a * b ∈ E := E.mul_mem ha hb
    have hab2 : (a * b) * (a * b) = 1 := hE2 (a * b) habE
    have hcomm : a * b = b * a := mul_comm_of_sq_eq_one ha2 hb2 hab2
    have hab1 : a * b ≠ 1 := by
      intro h
      apply hab
      have h1 : (a * b) * b = (1 : Γ) * b := by rw [h]
      rw [mul_assoc, hb2, mul_one, one_mul] at h1
      exact h1
    have hf := finrank_formula (ρ := ρ) h2 ha2 hb2 hcomm
    have hca := hc2 a ha ha1
    have hcb := hc2 b hb hb1
    have hcab := hc2 (a * b) habE hab1
    have hd : Module.finrank K
        ↥(LinearMap.ker (ρ a - 1) ⊓ LinearMap.ker (ρ b - 1)) = 0 := by omega
    exact Submodule.finrank_eq_zero.mp hd

private theorem cube_no_card_ge_eight (h2 : (2 : K) ≠ 0) [Finite Γ] [FiniteDimensional K V]
    {ρ : Representation K Γ V} {E : Subgroup Γ}
    (hE2 : ∀ s ∈ E, s * s = 1)
    (hperp : ∀ a ∈ E, ∀ b ∈ E, a ≠ 1 → b ≠ 1 → a ≠ b →
      LinearMap.ker (ρ a - 1) ⊓ LinearMap.ker (ρ b - 1) = ⊥)
    (hcpos : ∀ s ∈ E, s ≠ 1 → 0 < Module.finrank K (LinearMap.ker (ρ s - 1)))
    (h8E : 8 ≤ Nat.card ↥E) : False := by
  obtain ⟨u, huE, a, haE, b, hbE, hu1, ha1, hb1, hau, hbu, hba, hbua⟩ :=
    exists_three_with_ne_mul hE2 h8E
  have hu2 : u * u = 1 := hE2 u huE
  have ha2 : a * a = 1 := hE2 a haE
  have hb2 : b * b = 1 := hE2 b hbE
  have hu_mul_a : u * a = a * u :=
    mul_comm_of_sq_eq_one hu2 ha2 (hE2 (u * a) (E.mul_mem huE haE))
  have hu_mul_b : u * b = b * u :=
    mul_comm_of_sq_eq_one hu2 hb2 (hE2 (u * b) (E.mul_mem huE hbE))
  have hpert_ua : LinearMap.ker (ρ u - 1) ⊓ LinearMap.ker (ρ a - 1) = ⊥ :=
    hperp u huE a haE hu1 ha1 hau.symm
  have hpert_ub : LinearMap.ker (ρ u - 1) ⊓ LinearMap.ker (ρ b - 1) = ⊥ :=
    hperp u huE b hbE hu1 hb1 hbu.symm
  have habE : a * b ∈ E := E.mul_mem haE hbE
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hba
    have h1 : (a * b) * b = (1 : Γ) * b := by rw [h]
    rw [mul_assoc, hb2, mul_one, one_mul] at h1
    exact h1.symm
  have hab_ne_u : a * b ≠ u := by
    intro h
    apply hbua
    have h1 : a * (a * b) = a * u := by rw [h]
    rw [← mul_assoc, ha2, one_mul] at h1
    exact h1.trans (mul_comm_of_sq_eq_one ha2 hu2 (hE2 (a * u) (E.mul_mem haE huE)))
  have hpert_uab : LinearMap.ker (ρ u - 1) ⊓ LinearMap.ker (ρ (a * b) - 1) = ⊥ :=
    hperp u huE (a * b) habE hu1 hab1 hab_ne_u.symm
  have hfix_u : LinearMap.ker (ρ u - 1) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    have ha_neg : ρ a w = -w :=
      eq_neg_one_of_inf_ker_eq_bot (s := a) h2 ha2
        (mapsTo_ker_sub_one (ρ := ρ) (s := u) (t := a) hu_mul_a) hpert_ua w hw
    have hb_neg : ρ b w = -w :=
      eq_neg_one_of_inf_ker_eq_bot (s := b) h2 hb2
        (mapsTo_ker_sub_one (ρ := ρ) (s := u) (t := b) hu_mul_b) hpert_ub w hw
    have hwab : w ∈ LinearMap.ker (ρ (a * b) - 1) := by
      rw [mem_ker_sub_one, map_mul, Module.End.mul_apply, hb_neg, map_neg, ha_neg, neg_neg]
    have hmem : w ∈ LinearMap.ker (ρ u - 1) ⊓ LinearMap.ker (ρ (a * b) - 1) := ⟨hw, hwab⟩
    rw [hpert_uab] at hmem
    simpa using hmem
  have hcu0 : Module.finrank K (LinearMap.ker (ρ u - 1)) = 0 := by
    rw [hfix_u]
    simp
  exact (hcpos u huE hu1).ne' hcu0

private theorem cube_no_card_four (h3 : (3 : K) ≠ 0) [Finite Γ] [FiniteDimensional K V]
    {ρ : Representation K Γ V} {E Λ : Subgroup Γ} (hEn : E.Normal)
    (hE2 : ∀ s ∈ E, s * s = 1) (hΛ : Group.IsPerfect Λ) (hEΛ : E ≤ Λ)
    {σ : Γ} (hσΛ : σ ∈ Λ) (hσ : ∀ g : Γ, ρ σ * ρ g = ρ g * ρ σ)
    (hσ3 : ρ σ * ρ σ + ρ σ + 1 = 0)
    (h2' : ∀ s ∈ E, s ≠ 1 → Module.finrank K (LinearMap.ker (ρ s - 1)) ≤ 2)
    (hcpos : ∀ s ∈ E, s ≠ 1 → 0 < Module.finrank K (LinearMap.ker (ρ s - 1)))
    (hcard : Nat.card ↥E = 4) : False := by
  classical
  haveI : E.Normal := hEn
  have hne : E ≠ ⊥ := by
    intro h
    rw [Subgroup.eq_bot_iff_card] at h
    omega
  obtain ⟨s0, hs0⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hsE : (s0 : Γ) ∈ E := s0.2
  have hs1 : (s0 : Γ) ≠ 1 := by
    intro h
    exact hs0 (Subtype.ext h)
  have hcent := centralizes_of_card_four hcard hΛ hEΛ
  have hinv : ∀ g ∈ Λ, ∀ w ∈ LinearMap.ker (ρ (s0 : Γ) - 1),
      ρ g w ∈ LinearMap.ker (ρ (s0 : Γ) - 1) := by
    intro g hg w hw
    have hgs : g * (s0 : Γ) = (s0 : Γ) * g := hcent g hg (s0 : Γ) hsE
    exact mapsTo_ker_sub_one (ρ := ρ) (s := (s0 : Γ)) (t := g) hgs.symm w hw
  have h3dvd : 3 ∣ Module.finrank K (LinearMap.ker (ρ (s0 : Γ) - 1)) :=
    three_dvd_finrank_of_isPerfect h3 ρ hΛ (LinearMap.ker (ρ (s0 : Γ) - 1)) hinv hσΛ
      (fun g hg => hσ g) (fun w hw => apply_quadratic hσ3 w)
  have hle := h2' (s0 : Γ) hsE hs1
  have hpos := hcpos (s0 : Γ) hsE hs1
  obtain ⟨t, ht⟩ := h3dvd
  omega

theorem exists_neg_one_of_cube (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) [Finite Γ]
    [FiniteDimensional K V] {ρ : Representation K Γ V} (hρ : ρ.IsIrreducible) {E Λ : Subgroup Γ}
    (hEn : E.Normal) (hE2 : ∀ s ∈ E, s * s = 1) (hE : E ≠ ⊥) (hΛ : Group.IsPerfect Λ)
    (hEΛ : E ≤ Λ) {σ : Γ} (hσΛ : σ ∈ Λ) (hσ : ∀ g : Γ, ρ σ * ρ g = ρ g * ρ σ)
    (hσ3 : ρ σ * ρ σ + ρ σ + 1 = 0)
    (h2' : ∀ s ∈ E, s ≠ 1 → Module.finrank K (LinearMap.ker (ρ s - 1)) ≤ 2) :
    ∃ z ∈ E, z ≠ 1 ∧ ρ z = -1 ∧ ∀ s ∈ E, s = 1 ∨ s = z := by
  classical
  haveI : E.Normal := hEn
  haveI hV : Nontrivial V := nontrivial_of_isIrreducible hρ
  have hnpos : 0 < Module.finrank K V := Module.finrank_pos
  have hn3 : 3 ∣ Module.finrank K V := by
    have h := three_dvd_finrank_of_isPerfect h3 ρ hΛ ⊤
      (by intro g hg w hw; exact Submodule.mem_top)
      hσΛ (fun g hg => hσ g) (fun w hw => apply_quadratic hσ3 w)
    simpa using h
  have hE2grp : IsPGroup 2 ↥E := by
    intro x
    refine ⟨1, ?_⟩
    have hx : (x : Γ) * (x : Γ) = 1 := hE2 x x.2
    rw [show 2 ^ 1 = 2 by norm_num]
    exact Subtype.ext (by simpa [pow_two] using hx)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hE2grp
  by_cases hk1 : k = 1
  · have hcard2 : Nat.card ↥E = 2 := by rw [hk, hk1]; norm_num
    obtain ⟨z, hzE, hz1, hzall⟩ := exists_unique_nontrivial_of_card_two hcard2
    have hz2 : z * z = 1 := hE2 z hzE
    have hzcentral : ∀ g : Γ, z * g = g * z := by
      intro g
      have hmem : g * z * g⁻¹ ∈ E :=
        Subgroup.Normal.conj_mem (inferInstance : E.Normal) z hzE g
      have hne : g * z * g⁻¹ ≠ 1 := by
        intro h
        apply hz1
        have h' := congrArg (fun y : Γ => g⁻¹ * y * g) h
        simpa [mul_assoc] using h'
      have hz' : g * z * g⁻¹ = z := by
        rcases hzall (g * z * g⁻¹) hmem with h1 | h1
        · exact absurd h1 hne
        · exact h1
      have h2z := congrArg (fun y : Γ => y * g) hz'
      have h2zz : g * z = z * g := by simpa [mul_assoc] using h2z
      exact h2zz.symm
    have hzρne : ρ z ≠ 1 := by
      intro h
      have htop : LinearMap.ker (ρ z - 1) = ⊤ := by
        rw [h]
        simp
      have hle := h2' z hzE hz1
      rw [htop] at hle
      simp at hle
      omega
    refine ⟨z, hzE, hz1, ?_, hzall⟩
    apply rho_eq_neg_one_of_commute hρ _ hz2 hzρne
    intro g
    rw [← map_mul, ← map_mul, hzcentral g]
  · exfalso
    have hkge2 : 2 ≤ k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · exfalso
        apply hE
        rw [Subgroup.eq_bot_iff_card, hk, hk0]
        norm_num
      · omega
    have hcard4 : 4 ≤ Nat.card ↥E := by
      have h4 : 4 ≤ 2 ^ k := by
        have hpow := Nat.pow_le_pow_right (n := 2) (by norm_num : 0 < 2) hkge2
        norm_num at hpow ⊢
        exact hpow
      rwa [← hk] at h4
    obtain ⟨a0, ha0, b0, hb0, ha01, hb01, ha0b0⟩ := exists_two_ne_one hcard4
    have ha02 : a0 * a0 = 1 := hE2 a0 ha0
    have hb02 : b0 * b0 = 1 := hE2 b0 hb0
    have hab0E : a0 * b0 ∈ E := E.mul_mem ha0 hb0
    have hab02 : (a0 * b0) * (a0 * b0) = 1 := hE2 (a0 * b0) hab0E
    have hcomm0 : a0 * b0 = b0 * a0 := mul_comm_of_sq_eq_one ha02 hb02 hab02
    have hab01 : a0 * b0 ≠ 1 := by
      intro h
      apply ha0b0
      have h1 : (a0 * b0) * b0 = (1 : Γ) * b0 := by rw [h]
      rw [mul_assoc, hb02, mul_one, one_mul] at h1
      exact h1
    have hf0 := finrank_formula (ρ := ρ) h2 ha02 hb02 hcomm0
    have hca0 := h2' a0 ha0 ha01
    have hcb0 := h2' b0 hb0 hb01
    have hcab0 := h2' (a0 * b0) hab0E hab01
    have hnle6 : Module.finrank K V ≤ 6 := by omega
    have hn36 : Module.finrank K V = 3 ∨ Module.finrank K V = 6 := by
      obtain ⟨t, ht⟩ := hn3
      have htpos : 0 < t := by omega
      have htle : t ≤ 2 := by omega
      interval_cases t <;> omega
    have hstruct := cube_structure (ρ := ρ) h2 hΛ hEΛ hE2 h2' ha0 hb0 ha01 hb01 ha0b0 hn36
    have hperp : ∀ a ∈ E, ∀ b ∈ E, a ≠ 1 → b ≠ 1 → a ≠ b →
        LinearMap.ker (ρ a - 1) ⊓ LinearMap.ker (ρ b - 1) = ⊥ := by
      rcases hstruct with h | h
      · exact h.2
      · exact h.2
    have hcpos : ∀ s ∈ E, s ≠ 1 → 0 < Module.finrank K (LinearMap.ker (ρ s - 1)) := by
      intro s hs hs1
      rcases hstruct with ⟨hc, _⟩ | ⟨hc, _⟩
      · rw [hc s hs hs1]; norm_num
      · rw [hc s hs hs1]; norm_num
    by_cases h8E : 8 ≤ Nat.card ↥E
    · exact cube_no_card_ge_eight h2 hE2 hperp hcpos h8E
    · have hlt : Nat.card ↥E < 8 := by omega
      have hk3 : k < 3 := by
        have h2k : 2 ^ k < 8 := by rw [← hk]; exact hlt
        have h : 2 ^ k < 2 ^ 3 := by simpa using h2k
        exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h
      have hk2 : k = 2 := by omega
      have hcard4' : Nat.card ↥E = 4 := by rw [hk, hk2]; norm_num
      exact cube_no_card_four h3 hEn hE2 hΛ hEΛ hσΛ hσ hσ3 h2' hcpos hcard4'

end CFSG.RankThree.PartTwo.J2Residue
