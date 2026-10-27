module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE9FamDefs
public import CFSG.Quasithin.EmptyFaithful.T1521SL2EAll
public import CFSG.Quasithin.EmptyFaithful.T1521SBlkAutTK

public section

namespace CFSG.Quasithin.E9.L2

open CFSG.PSL2Table CFSG.Quasithin.L21521 CFSG.QuasithinUnique CFSG.Quasithin
open scoped MatrixGroups

section Model

variable {K : Type} [Field K]

theorem unip_eq_zero_of_commute_diag {a : Kˣ} (ha : (a : K) ^ 2 ≠ 1) {c : K}
    (h : mk (unip c) * mk (diag a) = mk (diag a) * mk (unip c)) : c = 0 := by
  have key : mk (unip c) * mk (diag a) * (mk (unip c))⁻¹ =
      mk (diag a) * mk (unip (((a⁻¹ : Kˣ) : K) ^ 2 * c - c)) := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, unip_mul_diag_mul_unip_inv]
  have h1 : mk (unip c) * mk (diag a) * (mk (unip c))⁻¹ = mk (diag a) := by
    rw [h, mul_assoc, mul_inv_cancel, mul_one]
  rw [h1] at key
  have h2 : mk (unip (((a⁻¹ : Kˣ) : K) ^ 2 * c - c)) = 1 :=
    mul_left_cancel (a := mk (diag a)) (key.symm.trans (mul_one _).symm)
  have h3 : ((a⁻¹ : Kˣ) : K) ^ 2 * c - c = 0 :=
    (mk_unip_eq_mk_unip_iff' _ 0).mp (by rw [h2, unip_zero, map_one])
  have ha' : ((a⁻¹ : Kˣ) : K) ^ 2 - 1 ≠ 0 := by
    intro h
    apply ha
    have h1 : ((a⁻¹ : Kˣ) : K) ^ 2 = 1 := sub_eq_zero.mp h
    have hinv : ((a⁻¹ : Kˣ) : K) = (a : K)⁻¹ := by simp
    rw [hinv, inv_pow, inv_eq_one] at h1
    exact h1
  have h4 : (((a⁻¹ : Kˣ) : K) ^ 2 - 1) * c = 0 := by linear_combination h3
  exact (mul_eq_zero.mp h4).resolve_left ha'

theorem eq_one_of_fixes_conj [Finite K] {a : Kˣ} (ha : (a : K) ^ 2 ≠ 1) (g : PSL(2, K))
    (β : MulAut PSL(2, K)) (hu : ∀ u ∈ unipotent K, β (g * u * g⁻¹) = g * u * g⁻¹)
    (hd : β (g * mk (diag a) * g⁻¹) = g * mk (diag a) * g⁻¹) : β = 1 := by
  have key : ∀ y : PSL(2, K), β (g * y * g⁻¹) = g * y * g⁻¹ →
      ((MulAut.conj g)⁻¹ * β * MulAut.conj g) y = y := by
    intro y hy
    have e1 : ((MulAut.conj g)⁻¹ * β * MulAut.conj g) y = g⁻¹ * β (g * y * g⁻¹) * g := by
      simp [MulAut.inv_apply, MulAut.conj_symm_apply, mul_assoc]
    rw [e1, hy]
    group
  have h1 := eq_one_of_forall_unipotent_diag ha ((MulAut.conj g)⁻¹ * β * MulAut.conj g)
    (fun u hu' => key u (hu u hu')) (key _ hd)
  calc β = MulAut.conj g * ((MulAut.conj g)⁻¹ * β * MulAut.conj g) * (MulAut.conj g)⁻¹ := by
        group
    _ = 1 := by rw [h1]; group

theorem exists_unit_cube_sq_ne_one [Finite K] {n : ℕ} (hn : 3 ≤ n) (hK : Nat.card K = 2 ^ n) :
    ∃ c : Kˣ, ((c ^ 3 : Kˣ) : K) ^ 2 ≠ 1 := by
  obtain ⟨c, hc⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  refine ⟨c, fun h => ?_⟩
  have h6 : c ^ 6 = 1 := by
    have h' : ((c ^ 3 : Kˣ) ^ 2 : Kˣ) = 1 := Units.ext (by simpa using h)
    rw [← pow_mul] at h'
    exact h'
  have hcard : 7 ≤ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    have h8 : 8 ≤ 2 ^ n :=
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have h7 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h6)
  omega

end Model

section Transport

variable {G : Type} [Group G]

theorem mem_normalizer_of_mem_normalizer_map {L P : Subgroup G} (hP : P ≤ L) {M : Type} [Group M]
    (φ : ↥L ≃* M) {w : M}
    (hw : w ∈ Subgroup.normalizer (((P.subgroupOf L).map φ.toMonoidHom : Subgroup M) : Set M)) :
    ((φ.symm w : ↥L) : G) ∈ Subgroup.normalizer (P : Set G) := by
  set z' : ↥L := φ.symm w with hz'
  have hz'N : ∀ x : ↥L, x ∈ P.subgroupOf L ↔ z' * x * z'⁻¹ ∈ P.subgroupOf L := by
    intro x
    have h := Subgroup.mem_normalizer_iff.mp hw (φ x)
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv] at h
    simpa [hz', map_mul, map_inv] using h
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    have hgL : g ∈ L := hP hg
    have := (hz'N ⟨g, hgL⟩).mp hg
    simpa [Subgroup.mem_subgroupOf] using this
  · intro hg
    have hgL : (z' : G) * g * (z' : G)⁻¹ ∈ L := hP hg
    have hgL' : g ∈ L := by
      have h1 : (z' : G)⁻¹ * ((z' : G) * g * (z' : G)⁻¹) * (z' : G) ∈ L :=
        L.mul_mem (L.mul_mem (L.inv_mem z'.2) hgL) z'.2
      simpa [mul_assoc] using h1
    exact Subgroup.mem_subgroupOf.mp ((hz'N ⟨g, hgL'⟩).mpr (by
      simpa [Subgroup.mem_subgroupOf] using hg))

theorem exists_torus [Finite G] {L P : Subgroup G} {n : ℕ} (hn : 3 ≤ n) (hL : IsPSL 2 2 n ↥L)
    (hP : IsSylowTwoOf P L) :
    ∃ z : G, z ∈ L ∧ z ∈ Subgroup.normalizer (P : Set G) ∧ Odd (orderOf z) ∧
      (∀ v ∈ Subgroup.normalizer (L : Set G), (∀ x ∈ P, v * x = x * v) →
        v * z ^ 3 = z ^ 3 * v → ∀ l ∈ L, v * l = l * v) ∧
      (∀ x ∈ P, x * z ^ 3 = z ^ 3 * x → x = 1) := by
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hL
  let φ : ↥L ≃* PSL(2, K) :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Sylow 2 PSL(2, K) := (A4.toSylow hP).mapSurjective (f := φ.toMonoidHom) φ.surjective
  have hQ : (Q : Subgroup PSL(2, K)) = (P.subgroupOf L).map φ.toMonoidHom := rfl
  obtain ⟨g, hg⟩ := exists_conj_unipotent_of_sylow (by omega) hK Q
  obtain ⟨c, hc⟩ := exists_unit_cube_sq_ne_one hn hK
  have hodd : Odd (Nat.card Kˣ) := by
    rw [Nat.card_units, hK]
    exact odd_two_pow_sub_one' (by omega)
  set t : PSL(2, K) := g * mk (diag c) * g⁻¹ with ht
  set z' : ↥L := φ.symm t with hz'
  have ht3 : t ^ 3 = g * mk (diag (c ^ 3)) * g⁻¹ := by
    rw [ht, conj_pow, diag_pow, map_pow]
  have hz3 : φ (z' ^ 3) = g * mk (diag (c ^ 3)) * g⁻¹ := by
    rw [map_pow, hz', MulEquiv.apply_symm_apply, ht3]
  have hmemQ : ∀ u ∈ unipotent K, ∃ y ∈ P.subgroupOf L, φ y = g * u * g⁻¹ := by
    intro u hu
    have hmem : g * u * g⁻¹ ∈ (Q : Subgroup PSL(2, K)) := by
      rw [hg]
      simpa [mul_assoc] using hu
    rw [hQ] at hmem
    exact Subgroup.mem_map.mp hmem
  refine ⟨(z' : G), z'.2, ?_, ?_, ?_, ?_⟩
  · refine mem_normalizer_of_mem_normalizer_map hP.1 φ ?_
    rw [← hQ]
    exact conj_mem_normalizer_of_conj hg (mk_diag_mem_normalizer c)
  · rw [Subgroup.orderOf_coe, hz', MulEquiv.orderOf_eq, ht, ← MulAut.conj_apply,
      MulEquiv.orderOf_eq]
    exact odd_orderOf_mk_diag hodd c
  · intro v hv hcP hcz l hl
    let α : MulAut ↥L := conjAct L ⟨v, hv⟩
    let β : MulAut PSL(2, K) := MulAut.congr φ α
    have hαfix : ∀ y : ↥L, v * (y : G) = (y : G) * v → α y = y := by
      intro y hy
      apply Subtype.ext
      change v * (y : G) * v⁻¹ = (y : G)
      rw [hy]
      group
    have hβ1 : β = 1 := by
      refine eq_one_of_fixes_conj hc g β ?_ ?_
      · intro u hu
        obtain ⟨y, hy, hyu⟩ := hmemQ u hu
        rw [← hyu]
        change φ (α (φ.symm (φ y))) = φ y
        rw [MulEquiv.symm_apply_apply, hαfix y (hcP _ (Subgroup.mem_subgroupOf.mp hy))]
      · rw [← hz3]
        change φ (α (φ.symm (φ (z' ^ 3)))) = φ (z' ^ 3)
        rw [MulEquiv.symm_apply_apply, hαfix _ (by simpa using hcz)]
    have h1 : α ⟨l, hl⟩ = ⟨l, hl⟩ := by
      have := congrArg (fun γ : MulAut PSL(2, K) => φ.symm (γ (φ ⟨l, hl⟩))) hβ1
      simpa [β, MulAut.congr] using this
    have h2 := congrArg (fun x : ↥L => (x : G)) h1
    have h3 : v * l * v⁻¹ = l := h2
    calc v * l = (v * l * v⁻¹) * v := by group
      _ = l * v := by rw [h3]
  · intro x hx hxz
    have hxL : x ∈ L := hP.1 hx
    have hx' : (⟨x, hxL⟩ : ↥L) ∈ P.subgroupOf L := hx
    have hmem : φ ⟨x, hxL⟩ ∈ (Q : Subgroup PSL(2, K)) := by
      rw [hQ]
      exact Subgroup.mem_map.mpr ⟨_, hx', rfl⟩
    obtain ⟨s, hs⟩ := (mem_unipotent_iff_exists _).mp ((hg _).mp hmem)
    have hcomm : φ ⟨x, hxL⟩ * (g * mk (diag (c ^ 3)) * g⁻¹) =
        (g * mk (diag (c ^ 3)) * g⁻¹) * φ ⟨x, hxL⟩ := by
      rw [← hz3, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (by simpa [pow_succ] using hxz)
    have hxe : φ ⟨x, hxL⟩ = g * mk (unip s) * g⁻¹ := by
      have := congrArg (fun w => g * w * g⁻¹) hs
      simpa [mul_assoc] using this
    rw [hxe] at hcomm
    have hu0 : s = 0 := by
      refine unip_eq_zero_of_commute_diag (a := c ^ 3) hc ?_
      have := congrArg (fun w => g⁻¹ * w * g) hcomm
      simpa [mul_assoc] using this
    have hx1 : φ ⟨x, hxL⟩ = 1 := by
      rw [hxe, hu0, unip_zero, map_one]
      group
    have := φ.injective (hx1.trans (map_one φ).symm)
    exact congrArg Subtype.val this

end Transport

end CFSG.Quasithin.E9.L2

namespace CFSG.Quasithin.E9

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.L21521E

variable {G : Type} [Group G] [Finite G]

theorem nrmE9_L2_big (horb : A3Orbits G) {X S L : Subgroup G} {n : ℕ} (hn : 3 ≤ n)
    (hL : IsPSL 2 2 n ↥L) (hc : IsComponentOf L X) (h : Std1521 X S L) : NrmE9 S L := by
  obtain ⟨-, hcase⟩ := horb X S L h.sqtk h.sylow h.comp
  have hJ : thompsonJ S ≤ innerPart1521 S L := by
    rcases hcase with hnorm | ⟨t, htS, htn, hset, -, -, -⟩
    · exact thompsonJ_le_innerPart_l2 hn hL h.sylowL (fun t ht => hnorm t ht)
    · exact thompsonJ_le_innerPart_l2_wreath hn hL hc h.sylow.1 h.sylowL htS htn hset
  obtain ⟨z, hzL, hzN, hzodd, hEa, hEb⟩ := L2.exists_torus hn hL h.sylowL
  refine nrmE9_of_inner hJ (H := Subgroup.zpowers z) ?_ ?_ ?_
  · rw [Subgroup.zpowers_le]
    exact ⟨hzL, hzN⟩
  · rw [Nat.card_zpowers]
    exact hzodd
  · intro H₀ _ hidx
    have hcomm : ∀ a ∈ Subgroup.zpowers z, ∀ b ∈ Subgroup.zpowers z, a * b = b * a := by
      intro a ha b hb
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (Commute.zpow_zpow_self z i j).eq
    have hz3 : z ^ 3 ∈ H₀ :=
      pow_three_mem_of_relIndex_dvd_three hcomm hidx z (Subgroup.mem_zpowers z)
    refine ⟨fun v _ hvN hvP hvH l hl => hEa v hvN hvP (hvH _ hz3) l hl, fun x hx hxH => ?_⟩
    have hx1 : x = 1 := hEb x hx.1 (hxH _ hz3)
    rw [hx1]
    exact (centerOf L).one_mem

end CFSG.Quasithin.E9
