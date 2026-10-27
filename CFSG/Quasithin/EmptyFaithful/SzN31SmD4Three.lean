module

public import CFSG.Quasithin.EmptyFaithful.SzN31SmD4Five
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzN31

open CFSG.Quasithin.G11 CFSG.Open

namespace SmD4Three

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem exists_generator_three {P : Subgroup (GLV V)} (hP : Nat.card P = 3) :
    ∃ w : GLV V, w ∈ P ∧ w ≠ 1 ∧ w ^ 3 = 1 ∧ orderOf w = 3 ∧ P = Subgroup.zpowers w := by
  have := finite_linearEquiv_zmod2 V
  have hPne : P ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hP
    omega
  obtain ⟨w', hw'1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hPne
  have hw1 : (w' : GLV V) ≠ 1 := fun h => hw'1 (Subtype.ext h)
  have hw3 : (w' : GLV V) ^ 3 = 1 := by
    have := pow_card_eq_one' (G := P) (x := w')
    rw [hP] at this
    exact congrArg Subtype.val this
  have hord : orderOf (w' : GLV V) = 3 := orderOf_eq_prime hw3 hw1
  refine ⟨w', w'.2, hw1, hw3, hord, ?_⟩
  symm
  apply Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 w'.2)
  rw [hP, Nat.card_zpowers, hord]

omit [Finite V] in
theorem mem_zpowers_cases {w : GLV V} (hw3 : w ^ 3 = 1) (hord : orderOf w = 3) {x : GLV V}
    (hx : x ∈ Subgroup.zpowers w) : x = 1 ∨ x = w ∨ x = w⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have hk : w ^ k = w ^ (k % 3) := by
    have := zpow_mod_orderOf w k
    rw [hord] at this
    exact_mod_cast this.symm
  rw [hk]
  have h3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases h3 with h | h | h
  · left
    rw [h]
    simp
  · right
    left
    rw [h]
    simp
  · right
    right
    rw [h, zpow_two]
    exact (inv_eq_of_mul_eq_one_right ((pow_three w).symm.trans hw3)).symm

theorem centralizer_le_of_card_three {Γ A : Subgroup (GLV V)} {m : ℕ} (hyp : G94Hyp Γ A m)
    (hsolv : Group.IsSolvable ↥Γ) (hV : Module.finrank (ZMod 2) V = 4)
    (hR5 : pCoreOf 5 Γ = ⊥) (hP : Nat.card (pCoreOf 3 Γ) = 3) :
    ∀ γ ∈ Γ, (∀ x ∈ pCoreOf 3 Γ, γ * x = x * γ) → γ ∈ pCoreOf 3 Γ := by
  have := finite_linearEquiv_zmod2 V
  have hbot : ∀ d : ℕ, d.Prime → d ≠ 3 → pCoreOf d Γ = ⊥ := by
    intro d hd hd3
    by_contra hne
    rcases prime_three_or_five_of_pCoreOf_ne_bot hyp hV hd hne with h | h
    · exact hd3 h
    · subst h
      exact hne hR5
  set F : Subgroup (GLV V) := (genFittingFitting ↥Γ).map Γ.subtype with hFdef
  have hF3 : Nat.card F = 3 := by
    have hpos : Nat.card F ≠ 0 := Nat.card_pos.ne'
    have huniq : ∀ {d : ℕ}, d.Prime → d ∣ Nat.card F → d = 3 := by
      intro d hd hdvd
      by_contra hd3
      have h1 : Nat.card (pCoreOf d Γ) = d ^ (Nat.card F).factorization d :=
        card_pCoreOf_eq_fitting hd Γ
      rw [hbot d hd hd3, Subgroup.card_bot] at h1
      have hf := hd.factorization_pos_of_dvd hpos hdvd
      have : 1 < d ^ (Nat.card F).factorization d := Nat.one_lt_pow hf.ne' hd.one_lt
      omega
    obtain ⟨L, hL⟩ : ∃ L : ℕ, Nat.card F = 3 ^ L :=
      ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hpos huniq⟩
    have h3 : Nat.card (pCoreOf 3 Γ) = 3 ^ (Nat.card F).factorization 3 :=
      card_pCoreOf_eq_fitting Nat.prime_three Γ
    rw [hP, hL, Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same] at h3
    rw [hL, ← h3]
  have hPF : pCoreOf 3 Γ = F :=
    Subgroup.eq_of_le_of_card_ge (pCoreOf_le_fitting Nat.prime_three Γ) (by rw [hF3, hP])
  intro γ hγ hc
  have hmem : (⟨γ, hγ⟩ : ↥Γ) ∈ Subgroup.centralizer (CFSG.fittingSubgroup ↥Γ : Set ↥Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyF : (y : GLV V) ∈ F := Subgroup.mem_map.2 ⟨y, hy, rfl⟩
    have hyP : (y : GLV V) ∈ pCoreOf 3 Γ := by rw [hPF]; exact hyF
    exact Subtype.ext (hc _ hyP).symm
  have h1 := CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv hmem
  have h2 : γ ∈ F := Subgroup.mem_map.2 ⟨⟨γ, hγ⟩, h1, rfl⟩
  rw [← hPF] at h2
  exact h2

theorem three_false {Γ A : Subgroup (GLV V)} {m : ℕ} (hyp : G94Hyp Γ A m)
    (hsolv : Group.IsSolvable ↥Γ) (hV : Module.finrank (ZMod 2) V = 4)
    (hR5 : pCoreOf 5 Γ = ⊥) (hP : Nat.card (pCoreOf 3 Γ) = 3) : False := by
  classical
  have := finite_linearEquiv_zmod2 V
  have hcent := centralizer_le_of_card_three hyp hsolv hV hR5 hP
  have hPne : pCoreOf 3 Γ ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hP
    omega
  have hfixP : fixedSpace (pCoreOf 3 Γ) = ⊥ := g94_fixedSpace_pCoreOf_eq_bot hyp hPne
  obtain ⟨w, hwP, hw1, hw3, hord, hPz⟩ := exists_generator_three hP
  set P := pCoreOf 3 Γ with hPdef
  have hAne : A ≠ ⊥ := by
    intro h
    have h1 := hyp.A_card
    rw [h, Subgroup.card_bot] at h1
    have := Nat.one_lt_two_pow (n := m) (by have := hyp.A_ne; omega)
    omega
  obtain ⟨a', ha'1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hAne
  set a : GLV V := (a' : GLV V) with hadef
  have haA : a ∈ A := a'.2
  have ha1 : a ≠ 1 := fun h => ha'1 (Subtype.ext h)
  have ha2 : a * a = 1 := by
    have := hyp.A_elem.2 a haA
    rwa [pow_two] at this
  have haΓ : a ∈ Γ := hyp.A_le haA
  have haP : a ∉ P := by
    intro hmem
    have h3 : a ^ 3 = 1 := by
      have := pow_card_eq_one' (G := P) (x := ⟨a, hmem⟩)
      rw [hP] at this
      exact congrArg Subtype.val this
    apply ha1
    calc a = a ^ 3 * (a * a)⁻¹ := by group
      _ = 1 := by rw [h3, ha2]; simp
  have hnormP : ∀ x ∈ P, a * x * a⁻¹ ∈ P := fun x hx => pCoreOf_normal_conj 3 Γ a haΓ x hx
  have hcommP : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    rw [hPz] at hx hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_zpow_self w i j).eq
  have hinvP : ∀ x ∈ P, a * x * a⁻¹ = x⁻¹ := by
    rcases SmD4Five.centralizes_or_inverts Nat.prime_three hP hcommP ha2 hnormP with h | h
    · exfalso
      apply haP
      apply hcent a haΓ
      intro x hx
      exact mul_inv_eq_iff_eq_mul.1 (h x hx)
    · exact h
  have hcases : ∀ γ ∈ Γ, γ ∈ P ∨ ∃ p ∈ P, γ = a * p := by
    intro γ hγ
    have hx : γ * w * γ⁻¹ ∈ Subgroup.zpowers w := by
      rw [← hPz]
      exact pCoreOf_normal_conj 3 Γ γ hγ w hwP
    rcases mem_zpowers_cases hw3 hord hx with h | h | h
    · exfalso
      apply hw1
      have : w = γ⁻¹ * (γ * w * γ⁻¹) * γ := by group
      rw [this, h]
      group
    · left
      apply hcent γ hγ
      intro x hx'
      rw [hPz] at hx'
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx'
      have hc : Commute γ w := mul_inv_eq_iff_eq_mul.1 h
      exact (hc.zpow_right k).eq
    · right
      refine ⟨a⁻¹ * γ, ?_, by group⟩
      apply hcent _ (Γ.mul_mem (Γ.inv_mem haΓ) hγ)
      intro x hx'
      rw [hPz] at hx'
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx'
      have e : (a⁻¹ * γ) * w * (a⁻¹ * γ)⁻¹ = w := by
        calc (a⁻¹ * γ) * w * (a⁻¹ * γ)⁻¹ = a⁻¹ * (γ * w * γ⁻¹) * a := by group
          _ = a⁻¹ * (a * w * a⁻¹) * a := by rw [h, hinvP w hwP]
          _ = w := by group
      have hc : Commute (a⁻¹ * γ) w := mul_inv_eq_iff_eq_mul.1 e
      exact (hc.zpow_right k).eq
  obtain ⟨v, hvS, hv0⟩ : ∃ v ∈ fixSp V a ⊤, v ≠ 0 := by
    have hpos : 0 < Module.finrank (ZMod 2) ↥(fixSp V a ⊤) := by
      have := SmD4Five.two_le_finrank_fixSp hV ha2
      omega
    obtain ⟨⟨v, hv⟩, hvne⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
    exact ⟨v, hv, fun h => hvne (Subtype.ext h)⟩
  have hav : a v = v := (CntLin.mem_fixSp.1 hvS).2
  have hw3v : w (w (w v)) = v := by
    have := DFunLike.congr_fun hw3 v
    simpa [pow_succ, LinearEquiv.mul_apply] using this
  have hs : v + w v + w (w v) = 0 := by
    have hmem : v + w v + w (w v) ∈ fixedSpace P := by
      rw [hPz]
      refine mem_fixedSpace_zpowers_iff.2 ?_
      rw [map_add, map_add, hw3v]
      abel
    rw [hfixP] at hmem
    simpa using hmem
  have hw2 : w (w v) = v + w v := by
    have h1 : w (w v) = -(v + w v) := eq_neg_of_add_eq_zero_right hs
    rw [h1, CntLin.zmod2_neg]
  let U : Submodule (ZMod 2) V := Submodule.span (ZMod 2) (({v, w v} : Finset V) : Set V)
  have hU2 : Module.finrank (ZMod 2) U ≤ 2 :=
    (finrank_span_finset_le_card _).trans Finset.card_le_two
  have hvU : v ∈ U := Submodule.subset_span (by simp)
  have hwvU : w v ∈ U := Submodule.subset_span (by simp)
  have hm : ∀ x ∈ U, ∃ c d : ZMod 2, c • v + d • w v = x := by
    intro x hx
    have hx' : x ∈ Submodule.span (ZMod 2) (({v, w v} : Finset V) : Set V) := hx
    simp only [Finset.coe_insert, Finset.coe_singleton] at hx'
    exact Submodule.mem_span_pair.1 hx'
  have hgen : ∀ g : GLV V, g v ∈ U → g (w v) ∈ U → ∀ u ∈ U, g u ∈ U := by
    intro g h1 h2 u hu
    obtain ⟨c, d, rfl⟩ := hm u hu
    rw [map_add, map_smul, map_smul]
    exact U.add_mem (U.smul_mem c h1) (U.smul_mem d h2)
  have hw2U : w (w v) ∈ U := by
    rw [hw2]
    exact U.add_mem hvU hwvU
  have hwU : ∀ u ∈ U, w u ∈ U := hgen w hwvU hw2U
  have haU : ∀ u ∈ U, a u ∈ U := by
    refine hgen a (by rw [hav]; exact hvU) ?_
    have hwinv : w⁻¹ = w * w := inv_eq_of_mul_eq_one_right ((pow_three w).symm.trans hw3)
    have hconj : a * w = w⁻¹ * a := mul_inv_eq_iff_eq_mul.1 (hinvP w hwP)
    have := DFunLike.congr_fun hconj v
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hav, hwinv, LinearEquiv.mul_apply] at this
    rw [this, hw2]
    exact U.add_mem hvU hwvU
  have hPU : ∀ x ∈ P, ∀ u ∈ U, x u ∈ U := by
    intro x hx u hu
    rw [hPz] at hx
    have hx' : x ∈ Submonoid.powers w := by
      rw [mem_powers_iff_mem_zpowers]
      exact hx
    obtain ⟨n, rfl⟩ := hx'
    exact CntLin.pow_apply_mem hwU n hu
  have hΓU : Invariant Γ U := by
    intro γ hγ u hu
    rcases hcases γ hγ with h | ⟨p, hp, rfl⟩
    · exact hPU γ h u hu
    · rw [LinearEquiv.mul_apply]
      exact haU _ (hPU p hp u hu)
  rcases hyp.irreducible.eq_bot_or_eq hΓU le_top with h | h
  · have : v ∈ (⊥ : Submodule (ZMod 2) V) := h ▸ hvU
    exact hv0 (by simpa using this)
  · have h4 : Module.finrank (ZMod 2) U = 4 := by
      rw [h, finrank_top, hV]
    omega

end SmD4Three

end CFSG.Quasithin.SzN31
