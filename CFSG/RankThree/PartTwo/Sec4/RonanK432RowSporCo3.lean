module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432CoverIndex
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import Certificates.Certificate36903

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.Blueprint
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.Sporadic.Schreier.Co3 (co3P card_co3P co3PermEquiv)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T
open CFSG.HardMathSupport.Solomon.Coordinator.Co3Pump (fuseGens fuseCheck tPar tGen tDep kA kB)

theorem co3_conj_witness {G : Type} [Group G] {s c g h : G} (hk : h * s * h⁻¹ = g * c * g⁻¹) :
    h⁻¹ * g * c * (h⁻¹ * g)⁻¹ = s := by
  calc h⁻¹ * g * c * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * c * g⁻¹) * h := by group
    _ = h⁻¹ * (h * s * h⁻¹) * h := by rw [hk]
    _ = s := by group

theorem co3_conj_witness' {G : Type} [Group G] {s c h : G} (hk : h * s * h⁻¹ = c) :
    h⁻¹ * c * (h⁻¹)⁻¹ = s := by
  rw [← hk]
  group

section Fusion


theorem co3_fuse_parts :
    (∀ i < 2, validA 276 (fuseGens ())[i]! = true ∧ inP (levels ()) (fuseGens ())[i]! = true) ∧
    (∀ k < 243, k = 0 ∨ (tPar[k]! = k ∧ (k = kA ∨ k = kB)) ∨
      (tPar[k]! < 243 ∧ tPar[k]! ≠ 0 ∧ tGen[k]! < 2 ∧ tDep[tPar[k]!]! < tDep[k]! ∧
        eqA 276 (dElts ())[k]! (conjA 276 (fuseGens ())[tGen[k]!]! (dElts ())[tPar[k]!]!) =
          true)) := by
  have h : fuseCheck () = true := Certificates.certificate36903.1
  simp only [fuseCheck, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun i hi => ?_, fun k hk => ?_⟩
  · have := allLt_spec h1 hi
    simp only [Bool.and_eq_true] at this
    exact this
  · have := allLt_spec h2 hk
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    rcases this with (h0 | h1) | ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr ⟨a, b, c, d, e⟩)

noncomputable def co3XA : Equiv.Perm (Fin 276) := φ (Multiplicative.ofAdd (vec kA))

noncomputable def co3XB : Equiv.Perm (Fin 276) := φ (Multiplicative.ofAdd (vec kB))

theorem co3_fuse_sound : ∀ k < 243, k ≠ 0 → ∃ h ∈ co3P,
    h * co3XA * h⁻¹ = φ (Multiplicative.ofAdd (vec k)) ∨
      h * co3XB * h⁻¹ = φ (Multiplicative.ofAdd (vec k)) := by
  obtain ⟨hgens, hforest⟩ := co3_fuse_parts
  suffices H : ∀ d, ∀ k < 243, tDep[k]! = d → k ≠ 0 → ∃ h ∈ co3P,
      h * co3XA * h⁻¹ = φ (Multiplicative.ofAdd (vec k)) ∨
        h * co3XB * h⁻¹ = φ (Multiplicative.ofAdd (vec k)) from
    fun k hk hk0 => H _ k hk rfl hk0
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro k hk hd hk0
    rcases hforest k hk with h0 | ⟨_, hkAB⟩ | ⟨hp, hp0, hg, hdep, he⟩
    · exact absurd h0 hk0
    · rcases hkAB with rfl | rfl
      · exact ⟨1, co3P.one_mem, Or.inl (by simp [co3XA])⟩
      · exact ⟨1, co3P.one_mem, Or.inr (by simp [co3XB])⟩
    · obtain ⟨h, hh, hcase⟩ := ih (tDep[tPar[k]!]!) (hd ▸ hdep) (tPar[k]!) hp rfl hp0
      obtain ⟨hv, hP⟩ := hgens (tGen[k]!) hg
      have hn : permOfArr 276 (fuseGens ())[tGen[k]!]! ∈ co3P :=
        mem_co3P_of_inP (rep_of_validA hv) hP
      have hkD := rep_dElts hk
      have hpD := rep_dElts hp
      have hconj := (eqA_iff hkD (rep_conjA hv hpD)).1 he
      refine ⟨permOfArr 276 (fuseGens ())[tGen[k]!]! * h, co3P.mul_mem hn hh, ?_⟩
      rcases hcase with hcase | hcase
      · left
        rw [hconj, ← hcase]
        group
      · right
        rw [hconj, ← hcase]
        group

theorem co3_child {k p : ℕ} (hk : k < 243) (hk0 : k ≠ 0) (hp : tPar[k]! = p) (hpk : p ≠ k) :
    ∃ n ∈ co3P, n * φ (Multiplicative.ofAdd (vec p)) * n⁻¹ = φ (Multiplicative.ofAdd (vec k)) := by
  rcases co3_fuse_parts.2 k hk with h0 | ⟨h1, _⟩ | ⟨hp243, _, hg, _, he⟩
  · exact absurd h0 hk0
  · exact absurd (hp ▸ h1) hpk
  · obtain ⟨hv, hP⟩ := co3_fuse_parts.1 (tGen[k]!) hg
    have hn : permOfArr 276 (fuseGens ())[tGen[k]!]! ∈ co3P :=
      mem_co3P_of_inP (rep_of_validA hv) hP
    have hpD : p < 243 := hp ▸ hp243
    rw [hp] at he
    have hconj := (eqA_iff (rep_dElts hk) (rep_conjA hv (rep_dElts hpD))).1 he
    exact ⟨_, hn, hconj.symm⟩

theorem co3_phi_ne_one {a : Fin 5 → ZMod 3} (ha : a ≠ 0) : φ (Multiplicative.ofAdd a) ≠ 1 := by
  intro h
  exact ha (ofAdd_eq_one.mp (φ_injective (h.trans (map_one φ).symm)))

theorem co3_phi_zpow_ne {a b : Fin 5 → ZMod 3} {i : Fin 5} (hb : b i = 0) (ha : a i ≠ 0)
    (m : ℤ) : φ (Multiplicative.ofAdd a) ≠ φ (Multiplicative.ofAdd b) ^ m := by
  intro h
  have h1 : Multiplicative.ofAdd a = Multiplicative.ofAdd (m • b) := by
    apply φ_injective
    rw [h, ← map_zpow, ← ofAdd_zsmul]
  have h2 : a = m • b := Multiplicative.ofAdd.injective h1
  have h3 := congrFun h2 i
  rw [Pi.smul_apply, hb, smul_zero] at h3
  exact ha h3

theorem co3_vec_kA_ne : vec kA ≠ 0 := by decide

theorem co3_vec_203_zero_ne : vec 203 0 ≠ 0 := by decide

theorem co3_vec_kB_four : vec kB 4 = 0 := by decide

theorem co3_vec_81_four_ne : vec 81 4 ≠ 0 := by decide

theorem co3_mem_Dg (a : Fin 5 → ZMod 3) : φ (Multiplicative.ofAdd a) ∈ Dg :=
  MonoidHom.mem_range.mpr ⟨_, rfl⟩

theorem co3XA_mem : co3XA ∈ co3P := Dg_le (co3_mem_Dg _)

theorem co3XB_mem : co3XB ∈ co3P := Dg_le (co3_mem_Dg _)

noncomputable def co3SA : ↥co3P := ⟨co3XA, co3XA_mem⟩

noncomputable def co3SB : ↥co3P := ⟨co3XB, co3XB_mem⟩

noncomputable def co3SY : ↥co3P := ⟨yPerm, yPerm_mem⟩

theorem co3XA_pow : co3XA ^ 3 = 1 := Dg_pow_three _ (co3_mem_Dg _)

theorem co3XB_pow : co3XB ^ 3 = 1 := Dg_pow_three _ (co3_mem_Dg _)

theorem co3XA_ne : co3XA ≠ 1 := co3_phi_ne_one co3_vec_kA_ne

theorem co3XB_ne : co3XB ≠ 1 := co3_phi_ne_one (a := vec kB) (by decide)

theorem co3_hR : ∀ c ∈ ({co3SA, co3SB, co3SY} : Set ↥co3P), orderOf c = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro c hc
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
  rcases hc with rfl | rfl | rfl
  · rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime co3XA_pow co3XA_ne
  · rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime co3XB_pow co3XB_ne
  · rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime yPerm_pow yPerm_ne_one

theorem co3_card_centralizer_y :
    Nat.card (Subgroup.centralizer ({co3SY} : Set ↥co3P)) = 4536 := by
  have hmap : (Subgroup.centralizer ({co3SY} : Set ↥co3P)).map co3P.subtype =
      Subgroup.centralizer ({yPerm} : Set (Equiv.Perm (Fin 276))) ⊓ co3P := by
    ext x
    constructor
    · intro hx
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
      rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
      refine ⟨?_, s.2⟩
      have := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hs)
      simpa [co3SY] using this
    · intro hx
      rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff] at hx
      refine Subgroup.mem_map.mpr ⟨⟨x, hx.2⟩, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      simpa [co3SY] using hx.1
  rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective co3P), hmap,
    ← Cy_eq.1]
  exact Cy_eq.2

theorem co3_three_dvd_index_y : 3 ∣ (Subgroup.centralizer ({co3SY} : Set ↥co3P)).index := by
  have h := Subgroup.card_mul_index (Subgroup.centralizer ({co3SY} : Set ↥co3P))
  rw [co3_card_centralizer_y, card_co3P] at h
  exact ⟨36432000, by omega⟩

theorem co3_hcov : ∀ s : ↥co3P, orderOf s = 3 →
    ∃ k c : ↥co3P, c ∈ ({co3SA, co3SB, co3SY} : Set ↥co3P) ∧
      ∃ e : ℕ, (e = 1 ∨ e = 2) ∧ k * c ^ e * k⁻¹ = s := by
  intro s hs
  have hs' : orderOf (s : Equiv.Perm (Fin 276)) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hs
  have hs1 : (s : Equiv.Perm (Fin 276)) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hs'
    omega
  obtain ⟨h, hh, hcase⟩ := exists_conj_D_or_y s.2 hs'
  rcases hcase with hD | hy | hy2
  · have hD' : h * (s : Equiv.Perm (Fin 276)) * h⁻¹ ∈ φ.range := hD
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hD'
    have hxa : φ (Multiplicative.ofAdd (Multiplicative.toAdd x)) =
        h * (s : Equiv.Perm (Fin 276)) * h⁻¹ := by
      rw [ofAdd_toAdd]
      exact hx
    generalize Multiplicative.toAdd x = a at hxa
    have ha0 : a ≠ 0 := by
      intro h0
      apply hs1
      have h1 : h * (s : Equiv.Perm (Fin 276)) * h⁻¹ = 1 := by
        rw [← hxa, h0, ofAdd_zero, map_one]
      calc (s : Equiv.Perm (Fin 276)) = h⁻¹ * (h * s * h⁻¹) * h := by group
        _ = 1 := by rw [h1]; group
    have hk0 : idx a ≠ 0 := fun h0 => ha0 ((idx_eq_zero_iff a).1 h0)
    obtain ⟨g, hg, hgk⟩ := co3_fuse_sound (idx a) (idx_lt a) hk0
    rw [vec_idx] at hgk
    rcases hgk with hgA | hgB
    · refine ⟨⟨h⁻¹ * g, co3P.mul_mem (co3P.inv_mem hh) hg⟩, co3SA, by simp, 1, Or.inl rfl, ?_⟩
      rw [pow_one]
      exact Subtype.ext (co3_conj_witness (hxa.symm.trans hgA.symm))
    · refine ⟨⟨h⁻¹ * g, co3P.mul_mem (co3P.inv_mem hh) hg⟩, co3SB, by simp, 1, Or.inl rfl, ?_⟩
      rw [pow_one]
      exact Subtype.ext (co3_conj_witness (hxa.symm.trans hgB.symm))
  · refine ⟨⟨h⁻¹, co3P.inv_mem hh⟩, co3SY, by simp, 1, Or.inl rfl, ?_⟩
    rw [pow_one]
    exact Subtype.ext (co3_conj_witness' hy)
  · refine ⟨⟨h⁻¹, co3P.inv_mem hh⟩, co3SY, by simp, 2, Or.inr rfl, ?_⟩
    exact Subtype.ext (co3_conj_witness' hy2)

theorem co3_hw : ∀ c ∈ ({co3SA, co3SB, co3SY} : Set ↥co3P),
    3 ∣ (Subgroup.centralizer ({c} : Set ↥co3P)).index ∨
      ∃ g : ↥co3P, g * c * g⁻¹ * c = c * (g * c * g⁻¹) ∧ g * c * g⁻¹ ∉ Subgroup.zpowers c := by
  intro c hc
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
  rcases hc with rfl | rfl | rfl
  · right
    obtain ⟨n, hn, hnk⟩ := co3_child (k := 203) (p := 9) (by norm_num) (by norm_num)
      (by decide +kernel) (by norm_num)
    have hnk' : n * co3XA * n⁻¹ = φ (Multiplicative.ofAdd (vec 203)) := hnk
    refine ⟨⟨n, hn⟩, ?_, ?_⟩
    · apply Subtype.ext
      show n * co3XA * n⁻¹ * co3XA = co3XA * (n * co3XA * n⁻¹)
      rw [hnk']
      exact Dg_comm _ (co3_mem_Dg _) _ (co3_mem_Dg _)
    · intro hmem
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have h1 := congrArg Subtype.val hm
      have h2 : co3XA ^ m = φ (Multiplicative.ofAdd (vec 203)) := h1.trans hnk'
      exact co3_phi_zpow_ne (i := 0) (by decide) co3_vec_203_zero_ne m h2.symm
  · right
    obtain ⟨n, hn, hnk⟩ := co3_child (k := 81) (p := 1) (by norm_num) (by norm_num)
      (by decide +kernel) (by norm_num)
    have hnk' : n * co3XB * n⁻¹ = φ (Multiplicative.ofAdd (vec 81)) := hnk
    refine ⟨⟨n, hn⟩, ?_, ?_⟩
    · apply Subtype.ext
      show n * co3XB * n⁻¹ * co3XB = co3XB * (n * co3XB * n⁻¹)
      rw [hnk']
      exact Dg_comm _ (co3_mem_Dg _) _ (co3_mem_Dg _)
    · intro hmem
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have h1 := congrArg Subtype.val hm
      have h2 : co3XB ^ m = φ (Multiplicative.ofAdd (vec 81)) := h1.trans hnk'
      exact co3_phi_zpow_ne (i := 4) co3_vec_kB_four co3_vec_81_four_ne m h2.symm
  · left
    exact co3_three_dvd_index_y

theorem listRow_co3P : ListRow ↥co3P :=
  listRow_of_cover_or_index ({co3SA, co3SB, co3SY} : Set ↥co3P) co3_hR co3_hcov co3_hw

end Fusion

theorem listRow_co3 :
    ListRow Blueprint.NativeSporadic.Co3 := by
  haveI : Finite Blueprint.NativeSporadic.Co3 := Finite.of_equiv _ co3PermEquiv.symm.toEquiv
  exact ListRow.of_mulEquiv co3PermEquiv.symm listRow_co3P

theorem outerRow_co3 :
    OuterRow Blueprint.NativeSporadic.Co3 := by
  haveI : Finite Blueprint.NativeSporadic.Co3 := Finite.of_equiv _ co3PermEquiv.symm.toEquiv
  refine outerRow_of_forall_pow_three_inner fun σ _ => ?_
  obtain ⟨g, rfl⟩ := (CFSG.RankThree.PartOne.CTUC_Co3_all_automorphisms_inner.{0}).2.1 σ
  exact ⟨g, rfl⟩

theorem row_carrier_co3 :
    RowOf (NativeSporadic.Carrier .Co3) := by
  haveI : Finite Blueprint.NativeSporadic.Co3 := Finite.of_equiv _ co3PermEquiv.symm.toEquiv
  intro S _ _ _ _ ⟨e⟩
  exact GoodRow.of_mulEquiv (S := Blueprint.NativeSporadic.Co3) e.symm
    ⟨listRow_co3, outerRow_co3⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
