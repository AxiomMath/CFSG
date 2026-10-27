module

public import CFSG.RankThree.Asc83Table.Automizer
public import CFSG.RankThree.Asc83Table.GL23

public section

namespace CFSG.RankThree.Asc83Table

open Subgroup

variable {L : Type*} [Group L]

omit [Group L] in
theorem range_pair (a b : L) : Set.range ![a, b] = {a, b} := by
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union]

structure E9Basis (L : Type*) [Group L] where
  a : L
  b : L
  ha : a ^ 3 = 1
  hb : b ^ 3 = 1
  hab : Commute a b
  card : Nat.card (closure ({a, b} : Set L)) = 9

namespace E9Basis

variable (E : E9Basis L)

abbrev sub : Subgroup L := closure ({E.a, E.b} : Set L)

abbrev vec : Fin 2 → L := ![E.a, E.b]

theorem vec_pow (i : Fin 2) : E.vec i ^ 3 = 1 := by
  fin_cases i
  · exact E.ha
  · exact E.hb

theorem vec_comm (i j : Fin 2) : Commute (E.vec i) (E.vec j) := by
  fin_cases i <;> fin_cases j
  · exact Commute.refl _
  · exact E.hab
  · exact E.hab.symm
  · exact Commute.refl _

theorem closure_range : closure (Set.range E.vec) = E.sub := by
  rw [range_pair]

theorem basisProd_vec (v : Fin 2 → ZMod 3) :
    basisProd E.vec v = E.a ^ (v 0).val * E.b ^ (v 1).val := by
  simp [basisProd, List.ofFn_succ]

theorem card_range : Nat.card (closure (Set.range E.vec)) = 3 ^ 2 := by
  rw [closure_range, E.card]
  norm_num

theorem basisProd_injective : Function.Injective (basisProd E.vec) := by
  have hs := basisHom_surjective E.vec_pow E.vec_comm
  have hb : Function.Bijective (basisHom E.vec_pow E.vec_comm) :=
    hs.bijective_of_nat_card_le (by rw [E.card_range]; simp [Nat.card_eq_fintype_card])
  intro u v huv
  have := hb.1 (a₁ := Multiplicative.ofAdd u) (a₂ := Multiplicative.ofAdd v)
    (Subtype.ext (by rw [coe_basisHom, coe_basisHom]; exact huv))
  exact Multiplicative.ofAdd.injective this

@[expose] noncomputable def equiv : Multiplicative (Fin 2 → ZMod 3) ≃* closure (Set.range E.vec) :=
  basisEquiv E.vec_pow E.vec_comm E.basisProd_injective

@[expose] noncomputable def rhoE : normalizer (closure (Set.range E.vec) : Set L) →* GL23 :=
  rho E.equiv

instance : Finite E.sub := Nat.finite_of_card_ne_zero (by rw [E.card]; norm_num)

theorem pow_val_natCast {x : L} (hx : x ^ 3 = 1) (n : ℕ) : x ^ ((n : ZMod 3).val) = x ^ n := by
  rw [ZMod.val_natCast, ← pow_eq_pow_mod n hx]

theorem mem_normalizer_of_conj {g : L} (p q r s : ℕ)
    (h₁ : g * E.a * g⁻¹ = E.a ^ p * E.b ^ r) (h₂ : g * E.b * g⁻¹ = E.a ^ q * E.b ^ s) :
    g ∈ normalizer (closure (Set.range E.vec) : Set L) := by
  have : Finite (closure (Set.range E.vec)) := by rw [closure_range]; infer_instance
  refine mem_normalizer_closure_of_conj_mem ?_
  have ha : E.a ∈ closure (Set.range E.vec) := subset_closure ⟨0, rfl⟩
  have hb : E.b ∈ closure (Set.range E.vec) := subset_closure ⟨1, rfl⟩
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · change g * E.a * g⁻¹ ∈ _
    rw [h₁]
    exact mul_mem (pow_mem ha _) (pow_mem hb _)
  · change g * E.b * g⁻¹ ∈ _
    rw [h₂]
    exact mul_mem (pow_mem ha _) (pow_mem hb _)

theorem rhoE_apply_of_conj {g : L} (hg : g ∈ normalizer (closure (Set.range E.vec) : Set L))
    (p q r s : ℕ) (h₁ : g * E.a * g⁻¹ = E.a ^ p * E.b ^ r)
    (h₂ : g * E.b * g⁻¹ = E.a ^ q * E.b ^ s) :
    ((E.rhoE ⟨g, hg⟩ : GL23) : Matrix (Fin 2) (Fin 2) (ZMod 3)) = !![(p : ZMod 3), q; r, s] := by
  refine rho_basis_eq E.vec_pow E.vec_comm E.basisProd_injective _ _ (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
  · rw [basisProd_vec]
    show g * E.a * g⁻¹ = E.a ^ (p : ZMod 3).val * E.b ^ (r : ZMod 3).val
    rw [pow_val_natCast E.ha, pow_val_natCast E.hb]
    exact h₁
  · rw [basisProd_vec]
    show g * E.b * g⁻¹ = E.a ^ (q : ZMod 3).val * E.b ^ (s : ZMod 3).val
    rw [pow_val_natCast E.ha, pow_val_natCast E.hb]
    exact h₂

theorem mem_range_of_conj {g : L} {M : GL23} (p q r s : ℕ)
    (h₁ : g * E.a * g⁻¹ = E.a ^ p * E.b ^ r) (h₂ : g * E.b * g⁻¹ = E.a ^ q * E.b ^ s)
    (hM : (M : Matrix (Fin 2) (Fin 2) (ZMod 3)) = !![(p : ZMod 3), q; r, s]) :
    M ∈ E.rhoE.range :=
  ⟨⟨g, E.mem_normalizer_of_conj p q r s h₁ h₂⟩, Units.ext
    ((E.rhoE_apply_of_conj _ p q r s h₁ h₂).trans hM.symm)⟩

theorem exists_pow_mul_pow {c : L} (hc : c ∈ E.sub) :
    ∃ i j : ℕ, i < 3 ∧ j < 3 ∧ c = E.a ^ i * E.b ^ j := by
  rw [← E.closure_range] at hc
  obtain ⟨v, hv⟩ := basisHom_surjective E.vec_pow E.vec_comm ⟨c, hc⟩
  have := congrArg Subtype.val hv
  rw [coe_basisHom, E.basisProd_vec] at this
  exact ⟨_, _, ZMod.val_lt _, ZMod.val_lt _, this.symm⟩

theorem exists_conj_of_mem_normalizer {g : L}
    (hg : g ∈ normalizer (closure (Set.range E.vec) : Set L)) :
    ∃ p q r s : ℕ, p < 3 ∧ q < 3 ∧ r < 3 ∧ s < 3 ∧ g * E.a * g⁻¹ = E.a ^ p * E.b ^ r ∧
      g * E.b * g⁻¹ = E.a ^ q * E.b ^ s ∧
      ((E.rhoE ⟨g, hg⟩ : GL23) : Matrix (Fin 2) (Fin 2) (ZMod 3)) = !![(p : ZMod 3), q; r, s] := by
  have ha : E.a ∈ closure (Set.range E.vec) := subset_closure ⟨0, rfl⟩
  have hb : E.b ∈ closure (Set.range E.vec) := subset_closure ⟨1, rfl⟩
  have h₁ := (mem_normalizer_iff.1 hg E.a).1 ha
  have h₂ := (mem_normalizer_iff.1 hg E.b).1 hb
  rw [E.closure_range] at h₁ h₂
  obtain ⟨p, r, hp, hr, e₁⟩ := E.exists_pow_mul_pow h₁
  obtain ⟨q, s, hq, hs, e₂⟩ := E.exists_pow_mul_pow h₂
  exact ⟨p, q, r, s, hp, hq, hr, hs, e₁, e₂, E.rhoE_apply_of_conj hg p q r s e₁ e₂⟩

noncomputable def automizerEquiv : Automizer E.sub ≃* E.rhoE.range :=
  (automizerCongr (MulEquiv.refl L) E.sub).trans (by
    rw [show E.sub.map (MulEquiv.refl L).toMonoidHom = closure (Set.range E.vec) by
      rw [closure_range]; exact Subgroup.map_id _]
    exact automizerEquivRange E.equiv)

theorem nonempty_quaternion (hI : qI ∈ E.rhoE.range) (hJ : qJ ∈ E.rhoE.range)
    (hup : E.rhoE.range ≤ quatHom.range) : Nonempty (Automizer E.sub ≃* QuaternionGroup 2) := by
  have heq : E.rhoE.range = quatHom.range := by
    refine le_antisymm hup ?_
    rw [range_quatHom, closure_le]
    rintro _ (rfl | rfl)
    · exact hI
    · exact hJ
  exact ⟨E.automizerEquiv.trans ((MulEquiv.subgroupCongr heq).trans
    (MonoidHom.ofInjective quatHom_injective).symm)⟩

theorem card_range_dvd : Nat.card E.rhoE.range ∣ 48 :=
  card_GL23 ▸ Subgroup.card_subgroup_dvd_card _

theorem nonempty_semidihedral (h3 : ¬ 3 ∣ Nat.card (Automizer E.sub)) {R S : GL23}
    (hR : R ∈ E.rhoE.range) (hS : S ∈ E.rhoE.range) (h8 : R ^ 8 = 1) (h2 : S ^ 2 = 1)
    (hc : S * R * S⁻¹ = R ^ 3)
    (hne : ∀ i : Fin 8, ∀ e : Fin 2, R ^ (i : ℕ) * S ^ (e : ℕ) = 1 → i = 0 ∧ e = 0) :
    Nonempty (Automizer E.sub ≃* CFSG.Open.SemidihedralGroup 4) := by
  have hcard : Nat.card E.rhoE.range = Nat.card (Automizer E.sub) :=
    (Nat.card_congr E.automizerEquiv.toEquiv).symm
  have h16 : Nat.card E.rhoE.range ∣ 16 := by
    have hcop : Nat.Coprime (Nat.card E.rhoE.range) 3 := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (by norm_num), hcard]
      exact h3
    exact hcop.dvd_of_dvd_mul_right (by simpa using E.card_range_dvd)
  obtain ⟨e⟩ := nonempty_mulEquiv_semidihedral h16 hR hS h8 h2 hc hne
  exact ⟨E.automizerEquiv.trans e⟩

theorem dihedral_or_gl (hR : bR ∈ E.rhoE.range) (hS : bS ∈ E.rhoE.range) :
    Nonempty (Automizer E.sub ≃* DihedralGroup 6) ∨ Nonempty (Automizer E.sub ≃* GL23) := by
  have hB : borel ≤ E.rhoE.range := by
    rw [borel_eq_closure, closure_le]
    rintro _ (rfl | rfl)
    · exact hR
    · exact hS
  rcases eq_borel_or_eq_top hB with h | h
  · left
    exact ⟨E.automizerEquiv.trans ((MulEquiv.subgroupCongr (h.trans range_dihedralHom.symm)).trans
      (MonoidHom.ofInjective dihedralHom_injective).symm)⟩
  · right
    exact ⟨E.automizerEquiv.trans ((MulEquiv.subgroupCongr h).trans Subgroup.topEquiv)⟩

theorem nonempty_gl (hR : bR ∈ E.rhoE.range) (hS : bS ∈ E.rhoE.range) (hw : w0 ∈ E.rhoE.range) :
    Nonempty (Automizer E.sub ≃* GL23) := by
  have hB : borel ≤ E.rhoE.range := by
    rw [borel_eq_closure, closure_le]
    rintro _ (rfl | rfl)
    · exact hR
    · exact hS
  exact ⟨E.automizerEquiv.trans ((MulEquiv.subgroupCongr (eq_top_of_borel_le hB hw)).trans
    Subgroup.topEquiv)⟩

theorem three_not_dvd [Finite L] (hL : ¬ 27 ∣ Nat.card L) : ¬ 3 ∣ Nat.card (Automizer E.sub) := by
  intro h3
  set N := normalizer (E.sub : Set L)
  set C := centralizer (E.sub : Set L)
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer _
  have hsubC : E.sub ≤ C := by
    rw [le_centralizer_iff_isMulCommutative]
    refine isMulCommutative_closure ?_
    rintro u (rfl | rfl) v (rfl | rfl) -
    · exact Commute.refl _
    · exact E.hab
    · exact E.hab.symm
    · exact Commute.refl _
  have h9 : 9 ∣ Nat.card C := E.card ▸ Subgroup.card_dvd_of_le hsubC
  have hN : Nat.card N = Nat.card (Automizer E.sub) * Nat.card (C.subgroupOf N) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hC : Nat.card (C.subgroupOf N) = Nat.card C :=
    Nat.card_congr (subgroupOfEquivOfLe hCN).toEquiv
  apply hL
  calc 27 ∣ Nat.card N := by
        rw [hN, hC, show 27 = 3 * 9 by rfl]
        exact Nat.mul_dvd_mul h3 h9
    _ ∣ Nat.card L := Subgroup.card_subgroup_dvd_card N

@[expose] def map {L' : Type*} [Group L'] (f : L →* L') (hf : Function.Injective f) :
    E9Basis L' where
  a := f E.a
  b := f E.b
  ha := by rw [← map_pow, E.ha, map_one]
  hb := by rw [← map_pow, E.hb, map_one]
  hab := E.hab.map f
  card := by
    rw [← Set.image_pair, ← MonoidHom.map_closure, Subgroup.card_map_of_injective hf, E.card]

theorem map_sub {L' : Type*} [Group L'] (f : L →* L') (hf : Function.Injective f) :
    (E.map f hf).sub = E.sub.map f := by
  rw [sub, sub, MonoidHom.map_closure, Set.image_pair]
  rfl

end E9Basis

theorem not_mem_zpowers_of_ne {x y : L} (hx : x ^ 3 = 1) (h0 : y ≠ 1) (h1 : y ≠ x)
    (h2 : y ≠ x ^ 2) : y ∉ zpowers x := by
  rintro ⟨k, rfl⟩
  have : x ^ k = x ^ (k % 3) := zpow_eq_zpow_emod' k hx
  have h0' : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
  have h3' : k % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  change x ^ k ≠ 1 at h0
  change x ^ k ≠ x at h1
  change x ^ k ≠ x ^ 2 at h2
  rw [this] at h0 h1 h2
  interval_cases (k % 3) <;> simp_all

theorem card_closure_pair_eq_nine {x y : L} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hxy : Commute x y)
    (hx1 : x ≠ 1) (hyx : y ∉ zpowers x) : Nat.card (closure ({x, y} : Set L)) = 9 := by
  set v : Fin 2 → L := ![x, y]
  have hv : ∀ i, v i ^ 3 = 1 := fun i => by fin_cases i <;> assumption
  have hc : ∀ i j, Commute (v i) (v j) := fun i j => by
    fin_cases i <;> fin_cases j
    · exact Commute.refl _
    · exact hxy
    · exact hxy.symm
    · exact Commute.refl _
  have hrange : closure (Set.range v) = closure {x, y} := by rw [range_pair]
  have hdvd : Nat.card (closure (Set.range v)) ∣ 9 := by
    have := Subgroup.card_dvd_of_surjective (basisHom_surjective hv hc)
    simpa [Nat.card_eq_fintype_card] using this
  rw [hrange] at hdvd
  have hzle : zpowers x ≤ closure ({x, y} : Set L) := by
    rw [zpowers_le]; exact subset_closure (by simp)
  have hz3 : Nat.card (zpowers x) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hx hx1
  have h3 : 3 ∣ Nat.card (closure ({x, y} : Set L)) := hz3 ▸ Subgroup.card_dvd_of_le hzle
  have hne3 : Nat.card (closure ({x, y} : Set L)) ≠ 3 := by
    intro h
    have : Finite (closure ({x, y} : Set L)) := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
    have heq := Subgroup.eq_of_le_of_card_ge hzle (by rw [h, hz3])
    exact hyx (heq ▸ subset_closure (by simp))
  have hmem : Nat.card (closure ({x, y} : Set L)) ∈ Nat.divisors 9 :=
    Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
  rw [show Nat.divisors 9 = {1, 3, 9} by decide] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h
  · rw [h] at h3; norm_num at h3
  · exact absurd h hne3
  · exact h

@[expose] noncomputable def E9Basis.ofNe {x y : L} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hxy : Commute x y) (hx1 : x ≠ 1) (h0 : y ≠ 1) (h1 : y ≠ x) (h2 : y ≠ x ^ 2) : E9Basis L :=
  ⟨x, y, hx, hy, hxy, card_closure_pair_eq_nine hx hy hxy hx1 (not_mem_zpowers_of_ne hx h0 h1 h2)⟩


end CFSG.RankThree.Asc83Table
