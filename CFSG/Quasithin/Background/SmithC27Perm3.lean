module

public import CFSG.Quasithin.Background.SmithC27Perm2
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralGenerators

public section

set_option maxRecDepth 100000

namespace CFSG.Quasithin.SmithC27

open Equiv Equiv.Perm
open scoped Pointwise

theorem threeCycle012_mem_quadStab_five : (swap 0 2 * swap 0 1 : Perm (Fin 5)) ∈ quadStab 5 := by
  rw [quadStab, mem_alt_inf_stabilizer_iff]
  decide +kernel

theorem threeCycle012_mem_quadStab_seven :
    (swap 0 2 * swap 0 1 : Perm (Fin 7)) ∈ quadStab 7 := by
  rw [quadStab, mem_alt_inf_stabilizer_iff]
  decide +kernel

theorem threeCycle012_mem_quadStab {n : ℕ} [NeZero n] (hn : n = 5 ∨ n = 7) :
    (swap 0 2 * swap 0 1 : Perm (Fin n)) ∈ quadStab n := by
  rcases hn with rfl | rfl
  · exact threeCycle012_mem_quadStab_five
  · exact threeCycle012_mem_quadStab_seven

theorem threeCycle012_not_mem_kJ_stdT2_five :
    (swap 0 2 * swap 0 1 : Perm (Fin 5)) ∉ kJ (stdT2 5) := by
  rw [kJ_stdT2_five, mem_alt_inf_centralizer_iff]
  decide +kernel

theorem threeCycle012_not_mem_kJ_stdT2_seven :
    (swap 0 2 * swap 0 1 : Perm (Fin 7)) ∉ kJ (stdT2 7) := by
  rw [kJ_stdT2_seven, mem_alt_inf_centralizer_iff]
  decide +kernel

theorem threeCycle012_not_mem_kJ_stdT2 {n : ℕ} [NeZero n] (hn : n = 5 ∨ n = 7) :
    (swap 0 2 * swap 0 1 : Perm (Fin n)) ∉ kJ (stdT2 n) := by
  rcases hn with rfl | rfl
  · exact threeCycle012_not_mem_kJ_stdT2_five
  · exact threeCycle012_not_mem_kJ_stdT2_seven

private def k4Five : Subgroup (Perm (Fin 5)) where
  carrier := {g | g = 1 ∨ g = swap 0 1 * swap 2 3 ∨ g = swap 0 2 * swap 1 3 ∨
    g = swap 0 3 * swap 1 2}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro a b (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;> decide +kernel
  inv_mem' := by
    rintro a (rfl | rfl | rfl | rfl) <;> decide +kernel

private def k4Seven : Subgroup (Perm (Fin 7)) where
  carrier := {g | g = 1 ∨ g = swap 0 1 * swap 2 3 ∨ g = swap 0 2 * swap 1 3 ∨
    g = swap 0 3 * swap 1 2}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro a b (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;> decide +kernel
  inv_mem' := by
    rintro a (rfl | rfl | rfl | rfl) <;> decide +kernel

private theorem V4_five_eq_k4 : V4 5 = k4Five := by
  apply le_antisymm
  · rw [V4, Subgroup.closure_le]
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  · rintro g (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact swap01_23_mem_V4 5
    · exact swap02_13_mem_V4 5
    · rw [show (swap 0 3 * swap 1 2 : Perm (Fin 5)) = swap 0 1 * swap 2 3 * (swap 0 2 * swap 1 3)
        by decide +kernel]
      exact Subgroup.mul_mem _ (swap01_23_mem_V4 5) (swap02_13_mem_V4 5)

private theorem V4_seven_eq_k4 : V4 7 = k4Seven := by
  apply le_antisymm
  · rw [V4, Subgroup.closure_le]
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  · rintro g (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact swap01_23_mem_V4 7
    · exact swap02_13_mem_V4 7
    · rw [show (swap 0 3 * swap 1 2 : Perm (Fin 7)) = swap 0 1 * swap 2 3 * (swap 0 2 * swap 1 3)
        by decide +kernel]
      exact Subgroup.mul_mem _ (swap01_23_mem_V4 7) (swap02_13_mem_V4 7)

theorem sq_eq_one_of_mem_V4 {n : ℕ} [NeZero n] (hn : n = 5 ∨ n = 7) {g : Perm (Fin n)}
    (hg : g ∈ V4 n) : g ^ 2 = 1 := by
  rcases hn with rfl | rfl
  · have hg' : g ∈ k4Five := V4_five_eq_k4 ▸ hg
    rcases hg' with rfl | rfl | rfl | rfl <;> decide +kernel
  · have hg' : g ∈ k4Seven := V4_seven_eq_k4 ▸ hg
    rcases hg' with rfl | rfl | rfl | rfl <;> decide +kernel

theorem isPGroup_V4 {n : ℕ} [NeZero n] (hn : n = 5 ∨ n = 7) : IsPGroup 2 (V4 n) := by
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  rw [Subgroup.coe_pow, pow_one]
  exact sq_eq_one_of_mem_V4 hn g.2

section SymQuad

variable (n : ℕ) [NeZero n]

@[expose] def symQuad : Subgroup (Perm (Fin n)) :=
  fixingSubgroup (Perm (Fin n)) ((quad n : Set (Fin n))ᶜ)

end SymQuad

theorem mem_symQuad_iff {n : ℕ} [NeZero n] {g : Perm (Fin n)} :
    g ∈ symQuad n ↔ ∀ x, x ∉ quad n → g x = x := by
  rw [symQuad, mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    have := h x (by simpa using hx)
    rwa [Perm.smul_def] at this
  · intro h x hx
    rw [Perm.smul_def]
    exact h x (by simpa using hx)

theorem card_symQuad (n : ℕ) [NeZero n] (h4 : (quad n).card = 4) : Nat.card (symQuad n) = 24 := by
  have hrange : (Perm.ofSubtype : Perm {x // x ∈ quad n} →* Perm (Fin n)).range = symQuad n := by
    ext g
    rw [Perm.mem_range_ofSubtype_iff, mem_symQuad_iff]
    constructor
    · intro h x hx
      by_contra hne
      exact hx (h (Perm.mem_support.mpr hne))
    · intro h x hx
      by_contra hne
      exact (Perm.mem_support.mp hx) (h x hne)
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective Perm.ofSubtype_injective).toEquiv,
    Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_coe, h4]
  rfl

theorem conj_mem_symQuad {n : ℕ} [NeZero n] {g s : Perm (Fin n)}
    (hg : g ∈ MulAction.stabilizer (Perm (Fin n)) ((quad n : Finset (Fin n)) : Set (Fin n)))
    (hs : s ∈ symQuad n) : g * s * g⁻¹ ∈ symQuad n := by
  rw [mem_stabilizer_coe_finset_iff] at hg
  rw [mem_symQuad_iff] at hs ⊢
  intro x hx
  have happ : g (g⁻¹ x) = x := g.apply_symm_apply x
  have hgx : g⁻¹ x ∉ quad n := fun h => hx (by rw [← hg (g⁻¹ x), happ] at h; exact h)
  simp only [Perm.mul_apply, hs _ hgx, happ]

@[expose] def quadWit {n : ℕ} [NeZero n] (a b : Fin n) : Perm (Fin n) :=
  if sign (swap 0 a * swap 1 (swap 0 a b)) = 1 then swap 0 a * swap 1 (swap 0 a b)
  else swap 0 a * swap 1 (swap 0 a b) * swap 2 3

private theorem quadWit_spec_five : ∀ a b : Fin 5, a ≠ b → a ∈ quad 5 → b ∈ quad 5 →
    sign (quadWit a b) = 1 ∧ (∀ x, quadWit a b x ∈ quad 5 ↔ x ∈ quad 5) ∧
      quadWit a b 0 = a ∧ quadWit a b 1 = b := by
  decide +kernel

private theorem quadWit_spec_seven : ∀ a b : Fin 7, a ≠ b → a ∈ quad 7 → b ∈ quad 7 →
    sign (quadWit a b) = 1 ∧ (∀ x, quadWit a b x ∈ quad 7 ↔ x ∈ quad 7) ∧
      quadWit a b 0 = a ∧ quadWit a b 1 = b := by
  decide +kernel

theorem symQuad_le_closure_conj_quadStab {n : ℕ} [NeZero n] (hn : n = 5 ∨ n = 7) :
    symQuad n ≤ Subgroup.closure {x | ∃ y ∈ quadStab n, x = y * swap 0 1 * y⁻¹} := by
  have hwit : ∀ a b : Fin n, a ≠ b → a ∈ quad n → b ∈ quad n →
      sign (quadWit a b) = 1 ∧ (∀ x, quadWit a b x ∈ quad n ↔ x ∈ quad n) ∧
        quadWit a b 0 = a ∧ quadWit a b 1 = b := by
    rcases hn with rfl | rfl
    · exact quadWit_spec_five
    · exact quadWit_spec_seven
  intro g hg
  rw [mem_symQuad_iff] at hg
  refine (Subgroup.closure_le _).mpr ?_ (mem_closure_swaps_of_fix (fun x => x ∈ quad n) hg)
  rintro _ ⟨a, b, ha, hb, hab, rfl⟩
  obtain ⟨hs, hq, h0, h1⟩ := hwit a b hab ha hb
  have hmem : quadWit a b ∈ quadStab n := by
    rw [quadStab, mem_alt_inf_stabilizer_iff]
    exact ⟨hs, hq⟩
  refine Subgroup.subset_closure ⟨quadWit a b, hmem, ?_⟩
  rw [← swap_apply_apply, h0, h1]

theorem eight_dvd_card_closure_conj_quadStab {n : ℕ} [NeZero n] (hn : n = 5 ∨ n = 7) :
    8 ∣ Nat.card (Subgroup.closure {x | ∃ y ∈ quadStab n, x = y * swap 0 1 * y⁻¹}) := by
  have h4 : (quad n).card = 4 := by
    rcases hn with rfl | rfl <;> rfl
  have h := Subgroup.card_dvd_of_le (symQuad_le_closure_conj_quadStab hn)
  rw [card_symQuad n h4] at h
  exact dvd_trans (by norm_num) h

section DEight

private def r4 : Perm (Fin 7) := swap 0 3 * swap 0 2 * swap 0 1

private def s2 : Perm (Fin 7) := swap 0 2

private theorem r4_facts : r4 ^ 4 = 1 ∧ r4 ^ 2 ≠ 1 ∧ r4 ≠ 1 ∧ r4 ^ 3 ≠ 1 ∧ s2 ^ 2 = 1 ∧
    s2 * r4 * s2⁻¹ = r4⁻¹ ∧ r4 * s2 ≠ s2 * r4 := by
  decide +kernel

private theorem r4_orderOf : orderOf r4 = 4 := by
  obtain ⟨h4, h2, h1, h3, -⟩ := r4_facts
  apply (orderOf_eq_iff (by norm_num)).mpr
  refine ⟨h4, fun m hm hm0 => ?_⟩
  interval_cases m
  · simpa using h1
  · exact h2
  · exact h3

private def d8q : Subgroup (Perm (Fin 7)) := Subgroup.zpowers r4 ⊔ Subgroup.zpowers s2

private theorem d8q_iso : Nonempty (↥d8q ≃* DihedralGroup 4) := by
  obtain ⟨-, -, -, -, hs2, hrel0, hne⟩ := r4_facts
  let ρ' : d8q := ⟨r4, Subgroup.mem_sup_left (Subgroup.mem_zpowers r4)⟩
  let σ' : d8q := ⟨s2, Subgroup.mem_sup_right (Subgroup.mem_zpowers s2)⟩
  have hgen : ⊤ = Subgroup.zpowers ρ' ⊔ Subgroup.zpowers σ' := by
    have hmap : Subgroup.map d8q.subtype ⊤ =
        Subgroup.map d8q.subtype (Subgroup.zpowers ρ' ⊔ Subgroup.zpowers σ') := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      rfl
    exact (Subgroup.map_injective (f := d8q.subtype) Subtype.coe_injective) hmap
  have hσ2 : σ' ^ 2 = 1 := by
    apply Subtype.ext
    simpa [σ'] using hs2
  have hrel : σ' * ρ' * σ'⁻¹ = ρ'⁻¹ := by
    apply Subtype.ext
    simpa [σ', ρ'] using hrel0
  have hord : orderOf ρ' = 4 := by
    rw [← Subgroup.orderOf_coe ρ']
    exact r4_orderOf
  rcases CFSG.GorensteinWalter.isCyclic_or_dihedral_of_generators ρ' σ' hgen hσ2 hrel with
    hcyc | hdih
  · exfalso
    have hcomm : ρ' * σ' = σ' * ρ' := IsMulCommutative.is_comm.comm ρ' σ'
    exact hne (congrArg (fun x : d8q => (x : Perm (Fin 7))) hcomm)
  · obtain ⟨e⟩ := hdih
    rw [hord] at e
    exact ⟨e⟩

private theorem card_d8q : Nat.card d8q = 8 := by
  obtain ⟨e⟩ := d8q_iso
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

private theorem d8q_le_symQuad : d8q ≤ symQuad 7 := by
  refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_) <;>
    rw [mem_symQuad_iff] <;> decide +kernel

theorem nonempty_dihedral_of_le_symQuad {P : Subgroup (Perm (Fin 7))} (hP : P ≤ symQuad 7)
    (hcard : Nat.card P = 8) : Nonempty (P ≃* DihedralGroup 4) := by
  have hS : Nat.card (symQuad 7) = 24 := card_symQuad 7 rfl
  let PS : Subgroup ↥(symQuad 7) := P.subgroupOf (symQuad 7)
  let DS : Subgroup ↥(symQuad 7) := d8q.subgroupOf (symQuad 7)
  have hPS : Nat.card PS = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP).toEquiv, hcard]
  have hDS : Nat.card DS = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe d8q_le_symQuad).toEquiv, card_d8q]
  have hiP : PS.index = 3 := by
    have h := Subgroup.card_mul_index PS
    rw [hPS, hS] at h
    omega
  have hiD : DS.index = 3 := by
    have h := Subgroup.card_mul_index DS
    rw [hDS, hS] at h
    omega
  have hpP : IsPGroup 2 PS := IsPGroup.of_card (n := 3) (by rw [hPS]; norm_num)
  have hpD : IsPGroup 2 DS := IsPGroup.of_card (n := 3) (by rw [hDS]; norm_num)
  let Psyl : Sylow 2 ↥(symQuad 7) := hpP.toSylow (by rw [hiP]; decide)
  let Dsyl : Sylow 2 ↥(symQuad 7) := hpD.toSylow (by rw [hiD]; decide)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥(symQuad 7)) Psyl Dsyl
  have heq : MulAut.conj g • PS = DS := by
    have h := congrArg (fun Q : Sylow 2 ↥(symQuad 7) => (Q : Subgroup ↥(symQuad 7))) hg
    simp only [Sylow.coe_subgroup_smul] at h
    exact h
  obtain ⟨e⟩ := d8q_iso
  exact ⟨((Subgroup.subgroupOfEquivOfLe hP).symm.trans
    ((Subgroup.equivSMul (MulAut.conj g) PS).trans (MulEquiv.subgroupCongr heq))).trans
      ((Subgroup.subgroupOfEquivOfLe d8q_le_symQuad).trans e)⟩

theorem nonempty_dihedral_of_sylow {Y P : Subgroup (Perm (Fin 7))}
    (hY : Y ≤ MulAction.stabilizer (Perm (Fin 7)) ((quad 7 : Finset (Fin 7)) : Set (Fin 7)))
    (hcl : Subgroup.closure {x | ∃ y ∈ quadStab 7, x = y * swap 0 1 * y⁻¹} ≤ Y)
    (h16 : ¬ 16 ∣ Nat.card Y) (hP : CFSG.QuasithinUnique.IsSylowTwoOf P Y) :
    Nonempty (P ≃* DihedralGroup 4) := by
  obtain ⟨hPY, hP2, hPidx⟩ := hP
  have hSY : symQuad 7 ≤ Y := (symQuad_le_closure_conj_quadStab (Or.inr rfl)).trans hcl
  have hS : Nat.card (symQuad 7) = 24 := card_symQuad 7 rfl
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hP2
  have hr := relIndex_mul_card_of_le hPY
  have hodd : ¬ 2 ∣ P.relIndex Y := hPidx
  have h24 : 24 ∣ Nat.card Y := hS ▸ Subgroup.card_dvd_of_le hSY
  have h8m : 2 ^ 3 ∣ 2 ^ m := by
    have h8 : 2 ^ 3 ∣ P.relIndex Y * 2 ^ m := by
      rw [← hm, hr]
      exact dvd_trans (by norm_num) h24
    have hcop : Nat.Coprime (2 ^ 3) (P.relIndex Y) :=
      Nat.Coprime.pow_left 3 (Nat.prime_two.coprime_iff_not_dvd.mpr hodd)
    exact hcop.dvd_of_dvd_mul_left h8
  have hm3 : 3 ≤ m := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h8m
  have hm4 : m < 4 := by
    by_contra hge
    push Not at hge
    apply h16
    rw [← hr, hm]
    exact Dvd.dvd.mul_left (dvd_trans (by norm_num : 16 ∣ 2 ^ 4) (pow_dvd_pow 2 hge)) _
  have hcardP : Nat.card P = 8 := by
    rw [hm, show m = 3 by omega]
    rfl
  let N : Subgroup ↥Y := (symQuad 7).subgroupOf Y
  have hNn : N.Normal := by
    constructor
    intro x hx g
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact conj_mem_symQuad (hY g.2) hx
  let P' : Subgroup ↥Y := P.subgroupOf Y
  have hcardN : Nat.card N = 24 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSY).toEquiv, hS]
  have hcardP' : Nat.card P' = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPY).toEquiv, hcardP]
  have e1 := Subgroup.relIndex_sup_right P' N
  have e2 := relIndex_mul_card_of_le (le_sup_right : N ≤ P' ⊔ N)
  have e3 : Nat.card ↥(P' ⊔ N) ∣ Nat.card ↥Y := Subgroup.card_subgroup_dvd_card _
  have e4 : N.relIndex P' ∣ 2 ^ 3 := by
    have := Subgroup.relIndex_dvd_card N P'
    rwa [hcardP'] at this
  have hi : N.relIndex P' = 1 := by
    obtain ⟨k, -, hik⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp e4
    by_contra hne
    have hk : k ≠ 0 := by
      rintro rfl
      exact hne hik
    apply h16
    have h1 : N.relIndex P' * 24 ∣ Nat.card Y := by
      rw [← e1, ← hcardN, e2]
      exact e3
    rw [hik] at h1
    exact dvd_trans (dvd_trans (by norm_num : 16 ∣ 2 * 24)
      (Nat.mul_dvd_mul_right (dvd_pow_self 2 hk) 24)) h1
  rw [Subgroup.relIndex_eq_one] at hi
  have hPS : P ≤ symQuad 7 := by
    intro p hp
    have hp' : (⟨p, hPY hp⟩ : ↥Y) ∈ P' := hp
    exact hi hp'
  exact nonempty_dihedral_of_le_symQuad hPS hcardP

end DEight

section EEight

private def e8hom : Multiplicative (Fin 3 → ZMod 2) →* Perm (Fin 7) where
  toFun v := swap 0 1 ^ (Multiplicative.toAdd v 0).val *
    swap 2 3 ^ (Multiplicative.toAdd v 1).val * swap 4 5 ^ (Multiplicative.toAdd v 2).val
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

private theorem e8hom_injective : Function.Injective e8hom := by
  intro v w h
  revert v w
  decide +kernel

private theorem e8hom_mem : ∀ v : Multiplicative (Fin 3 → ZMod 2), ∀ x : Fin 7,
    e8hom v x = x ∨ e8hom v x = z3 7 x := by
  decide +kernel

private def e8vec (a b c : Fin 7) : Multiplicative (Fin 3 → ZMod 2) :=
  Multiplicative.ofAdd ![if a = 0 then 0 else 1, if b = 2 then 0 else 1, if c = 4 then 0 else 1]

private theorem e8_values : ∀ a0 a2 a4 : Fin 7, (a0 = 0 ∨ a0 = 1) → (a2 = 2 ∨ a2 = 3) →
    (a4 = 4 ∨ a4 = 5) →
    e8hom (e8vec a0 a2 a4) 0 = a0 ∧ e8hom (e8vec a0 a2 a4) 1 = z3 7 a0 ∧
    e8hom (e8vec a0 a2 a4) 2 = a2 ∧ e8hom (e8vec a0 a2 a4) 3 = z3 7 a2 ∧
    e8hom (e8vec a0 a2 a4) 4 = a4 ∧ e8hom (e8vec a0 a2 a4) 5 = z3 7 a4 ∧
    e8hom (e8vec a0 a2 a4) 6 = 6 := by
  decide +kernel

private theorem e8_partner : ∀ a b : Fin 7, ((a = 0 ∨ a = 1) ∧ (b = 1 ∨ b = 0) ∨
    (a = 2 ∨ a = 3) ∧ (b = 3 ∨ b = 2) ∨ (a = 4 ∨ a = 5) ∧ (b = 5 ∨ b = 4)) → b ≠ a →
    b = z3 7 a := by
  decide +kernel

private theorem range_e8hom {J : Subgroup (Perm (Fin 7))}
    (hJ : ∀ g, g ∈ J ↔ ∀ x, g x = x ∨ g x = z3 7 x) : e8hom.range = J := by
  ext g
  constructor
  · rintro ⟨v, rfl⟩
    exact (hJ _).mpr (e8hom_mem v)
  · intro hg
    rw [hJ] at hg
    have hz : ∀ x : Fin 7, z3 7 x = ![1, 0, 3, 2, 5, 4, 6] x := by decide
    have h := fun x => (hg x).imp id (fun e => e.trans (hz x))
    have hne : ∀ {x y : Fin 7}, x ≠ y → g x ≠ g y := fun hxy e => hxy (g.injective e)
    have p1 : g 1 = z3 7 (g 0) :=
      e8_partner _ _ (Or.inl ⟨h 0, (h 1).symm.imp id id |>.symm⟩) (hne (by decide))
    have p3 : g 3 = z3 7 (g 2) :=
      e8_partner _ _ (Or.inr (Or.inl ⟨h 2, (h 3).symm.imp id id |>.symm⟩)) (hne (by decide))
    have p5 : g 5 = z3 7 (g 4) :=
      e8_partner _ _ (Or.inr (Or.inr ⟨h 4, (h 5).symm.imp id id |>.symm⟩)) (hne (by decide))
    have h6 : g 6 = 6 := (h 6).elim id id
    obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := e8_values (g 0) (g 2) (g 4) (h 0) (h 2) (h 4)
    refine ⟨e8vec (g 0) (g 2) (g 4), Equiv.ext fun x => ?_⟩
    fin_cases x
    · exact e0
    · exact e1.trans p1.symm
    · exact e2
    · exact e3.trans p3.symm
    · exact e4
    · exact e5.trans p5.symm
    · exact e6.trans h6.symm

private theorem nonempty_mulEquiv_E8 {J : Subgroup (Perm (Fin 7))}
    (hJ : ∀ g, g ∈ J ↔ ∀ x, g x = x ∨ g x = z3 7 x) :
    Nonempty (↥J ≃* Multiplicative (Fin 3 → ZMod 2)) :=
  ⟨((MonoidHom.ofInjective e8hom_injective).trans
    (MulEquiv.subgroupCongr (range_e8hom hJ))).symm⟩

theorem isE2_three_of_mem_iff {J : Subgroup (Perm (Fin 7))}
    (hJ : ∀ g, g ∈ J ↔ ∀ x, g x = x ∨ g x = z3 7 x) : IsE2 3 ↥J :=
  nonempty_mulEquiv_E8 hJ

theorem card_eq_eight_of_mem_iff {J : Subgroup (Perm (Fin 7))}
    (hJ : ∀ g, g ∈ J ↔ ∀ x, g x = x ∨ g x = z3 7 x) : Nat.card J = 8 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_E8 hJ
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
  rfl

theorem eq_or_card_eq_sixteen_of_le_normalizer {J : Subgroup (Perm (Fin 7))}
    (hJ : ∀ g, g ∈ J ↔ ∀ x, g x = x ∨ g x = z3 7 x) {P : Subgroup (Perm (Fin 7))}
    (hP : IsPGroup 2 P) (h1 : J ≤ P)
    (h2 : P ≤ Subgroup.normalizer (J : Set (Perm (Fin 7)))) : P = J ∨ Nat.card P = 16 := by
  rw [normalizer_eq_centralizer_of_mem_iff z3_invol hJ] at h2
  have h48 := Subgroup.card_dvd_of_le h2
  rw [card_centralizer_z3] at h48
  have h8 := Subgroup.card_dvd_of_le h1
  rw [card_eq_eight_of_mem_iff hJ] at h8
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hP
  rw [hm] at h48 h8
  have hm3 : 3 ≤ m := (Nat.pow_dvd_pow_iff_le_right (x := 2) (by norm_num)).mp
    (by rw [show (2 : ℕ) ^ 3 = 8 by norm_num]; exact h8)
  have hm4 : m ≤ 4 := by
    have hcop : Nat.Coprime (2 ^ m) 3 := Nat.Coprime.pow_left m (by norm_num)
    have : 2 ^ m ∣ 2 ^ 4 :=
      hcop.dvd_of_dvd_mul_right (by rw [show (2 : ℕ) ^ 4 * 3 = 48 by norm_num]; exact h48)
    exact (Nat.pow_dvd_pow_iff_le_right (x := 2) (by norm_num)).mp this
  rcases (show m = 3 ∨ m = 4 by omega) with rfl | rfl
  · left
    exact (Subgroup.eq_of_le_of_card_ge h1 (by rw [hm, card_eq_eight_of_mem_iff hJ]; rfl)).symm
  · right
    rw [hm]
    rfl

end EEight

end CFSG.Quasithin.SmithC27
