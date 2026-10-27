module

public import CFSG.Quasithin.H13.A6S1372L76Oe2
public import CFSG.Quasithin.H13.A6S1372L76Of2

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative Matrix commutatorElement

namespace A6L76N3

section Eight

variable {M : Type*} [CommGroup M]

@[expose] def lineW (hM2 : ∀ m : M, m * m = 1) (x y : M) : Subgroup M where
  carrier := {m | m = 1 ∨ m = x ∨ m = y ∨ m = x * y}
  mul_mem' := by
    have h1 : ∀ a b : M, a * (a * b) = b := fun a b => by rw [← mul_assoc, hM2, one_mul]
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rcases ha with ha | ha | ha | ha <;> rcases hb with hb | hb | hb | hb <;> rw [ha, hb] <;>
      simp [mul_comm, mul_left_comm, hM2, h1]
  one_mem' := Or.inl rfl
  inv_mem' := by
    intro m hm
    rwa [show m⁻¹ = m from inv_eq_of_mul_eq_one_right (hM2 m)]

theorem mem_lineW (hM2 : ∀ m : M, m * m = 1) {x y m : M} :
    m ∈ lineW hM2 x y ↔ m = 1 ∨ m = x ∨ m = y ∨ m = x * y := Iff.rfl

theorem card_lineW [Finite M] (hM2 : ∀ m : M, m * m = 1) {x y : M} (hx : x ≠ 1) (hy : y ≠ 1)
    (hxy : x ≠ y) : Nat.card ↥(lineW hM2 x y) = 4 := by
  classical
  have h1 : x * y ≠ 1 := fun h => hxy (by
    rw [← mul_one x, ← h, ← mul_assoc, hM2, one_mul])
  have h2 : x * y ≠ x := fun h => hy (by
    rw [← one_mul y, ← hM2 x, mul_assoc, h, hM2])
  have h3 : x * y ≠ y := fun h => hx (by
    rw [← mul_one x, ← hM2 y, ← mul_assoc, h, hM2])
  have e : ((lineW hM2 x y : Subgroup M) : Set M) = (({1, x, y, x * y} : Finset M) : Set M) := by
    ext m
    simp [mem_lineW]
  rw [← SetLike.coe_sort_coe, e, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rw [Finset.card_insert_of_notMem (by simp [hx.symm, hy.symm, h1.symm]),
    Finset.card_insert_of_notMem (by simp [hxy, h2.symm]),
    Finset.card_insert_of_notMem (by simp [h3.symm]), Finset.card_singleton]

theorem index_lineW [Finite M] (hM2 : ∀ m : M, m * m = 1) (h8 : Nat.card M = 8) {x y : M}
    (hx : x ≠ 1) (hy : y ≠ 1) (hxy : x ≠ y) : (lineW hM2 x y).index = 2 := by
  have h := (lineW hM2 x y).card_mul_index
  rw [card_lineW hM2 hx hy hxy, h8] at h
  omega

theorem apply_three {a : MulAut M} (ha3 : a ^ 3 = 1) (m : M) : a (a (a m)) = m := by
  have h := congrArg (fun f : MulAut M => f m) ha3
  simpa [pow_succ, MulAut.mul_apply] using h

theorem apply_mem_lineW (hM2 : ∀ m : M, m * m = 1) {x y : M} {a : MulAut M} (hax : a x = y)
    (hay : a y = x * y) {m : M} (hm : m ∈ lineW hM2 x y) : a m ∈ lineW hM2 x y := by
  rcases hm with h | h | h | h <;> rw [h]
  · exact Or.inl (map_one a)
  · exact Or.inr (Or.inr (Or.inl hax))
  · exact Or.inr (Or.inr (Or.inr hay))
  · refine Or.inr (Or.inl ?_)
    rw [map_mul, hax, hay, mul_comm x y, ← mul_assoc, hM2, one_mul]

theorem eq_one_of_mem_lineW (hM2 : ∀ m : M, m * m = 1) {x y : M} (hx : x ≠ 1) (hy : y ≠ 1)
    (hxy : x ≠ y) {a : MulAut M} (hax : a x = y) (hay : a y = x * y) {m : M}
    (hm : m ∈ lineW hM2 x y) (ham : a m = m) : m = 1 := by
  have h1 : ∀ a b : M, a * (a * b) = b := fun a b => by rw [← mul_assoc, hM2, one_mul]
  rcases hm with h | h | h | h
  · exact h
  · rw [h] at ham
    exact absurd (hax.symm.trans ham) (Ne.symm hxy)
  · rw [h] at ham
    exfalso
    apply hx
    exact mul_right_cancel ((hay.symm.trans ham).trans (one_mul y).symm)
  · rw [h] at ham
    exfalso
    apply hy
    have h2 : a (x * y) = x := by
      rw [map_mul, hax, hay, mul_comm x y, h1]
    rw [h2] at ham
    rw [← h1 x y, ← ham, hM2]

theorem exists_fixed_off_line [Finite M] (hM2 : ∀ m : M, m * m = 1) (h8 : Nat.card M = 8)
    {x y : M} (hx : x ≠ 1) (hy : y ≠ 1) (hxy : x ≠ y) {a : MulAut M} (hax : a x = y)
    (hay : a y = x * y) (ha3 : a ^ 3 = 1) :
    ∃ p : M, p ∉ lineW hM2 x y ∧ a p = p ∧ ∀ n, a n = n → n = 1 ∨ n = p := by
  classical
  have hidx := index_lineW hM2 h8 hx hy hxy
  have hmul := fun {u v : M} => Subgroup.mul_mem_iff_of_index_two hidx (a := u) (b := v)
  obtain ⟨m, hm⟩ : ∃ m, m ∉ lineW hM2 x y := by
    by_contra h
    push Not at h
    have htop : lineW hM2 x y = ⊤ := eq_top_iff.2 fun m _ => h m
    rw [htop, Subgroup.index_top] at hidx
    exact absurd hidx (by norm_num)
  have hW : ∀ {n : M}, n ∉ lineW hM2 x y → a n ∉ lineW hM2 x y := fun {n} hn h => hn (by
    have := apply_mem_lineW hM2 hax hay (apply_mem_lineW hM2 hax hay h)
    rwa [apply_three ha3] at this)
  set p := m * a m * a (a m) with hp
  have hpW : p ∉ lineW hM2 x y := by
    intro h
    have h1 : m * a m ∈ lineW hM2 x y := hmul.2 (iff_of_false hm (hW hm))
    exact hW (hW hm) ((hmul.1 h).1 h1)
  have hap : a p = p := by
    rw [hp, map_mul, map_mul, apply_three ha3]
    ac_rfl
  refine ⟨p, hpW, hap, fun n hn => ?_⟩
  by_cases hnW : n ∈ lineW hM2 x y
  · exact Or.inl (eq_one_of_mem_lineW hM2 hx hy hxy hax hay hnW hn)
  · right
    have hu : p * n ∈ lineW hM2 x y := hmul.2 (iff_of_false hpW hnW)
    have hu1 := eq_one_of_mem_lineW hM2 hx hy hxy hax hay hu (by rw [map_mul, hap, hn])
    exact (eq_inv_of_mul_eq_one_right hu1).trans (inv_eq_of_mul_eq_one_right (hM2 p))

theorem eq_one_of_comm [Finite M] (hM2 : ∀ m : M, m * m = 1) (h8 : Nat.card M = 8)
    {x y : M} (hx : x ≠ 1) (hy : y ≠ 1) (hxy : x ≠ y) {a : MulAut M} (hax : a x = y)
    (hay : a y = x * y) (ha3 : a ^ 3 = 1) {g : MulAut M} (hgx : g x = x) (hgy : g y = y)
    (hga : g * a = a * g) : g = 1 := by
  classical
  have hidx := index_lineW hM2 h8 hx hy hxy
  have hmul := fun {u v : M} => Subgroup.mul_mem_iff_of_index_two hidx (a := u) (b := v)
  obtain ⟨p, hpW, hap, -⟩ := exists_fixed_off_line hM2 h8 hx hy hxy hax hay ha3
  have hgW : ∀ {n : M}, n ∈ lineW hM2 x y → g n = n := by
    intro n hn
    rcases hn with h | h | h | h <;> rw [h]
    · exact map_one g
    · exact hgx
    · exact hgy
    · rw [map_mul, hgx, hgy]
  have hgp : g p = p := by
    have hgpW : g p ∉ lineW hM2 x y := fun h => hpW (by
      have h1 := hgW h
      rwa [g.injective h1] at h)
    have hu : g p * p ∈ lineW hM2 x y := hmul.2 (iff_of_false hgpW hpW)
    have hau : a (g p * p) = g p * p := by
      have h1 : a (g p) = g p := by
        rw [← MulAut.mul_apply, ← hga, MulAut.mul_apply, hap]
      rw [map_mul, h1, hap]
    have h1 := eq_one_of_mem_lineW hM2 hx hy hxy hax hay hu hau
    exact (eq_inv_of_mul_eq_one_left h1).trans (inv_eq_of_mul_eq_one_right (hM2 p))
  ext n
  by_cases hnW : n ∈ lineW hM2 x y
  · exact hgW hnW
  · have hu : p * n ∈ lineW hM2 x y := hmul.2 (iff_of_false hpW hnW)
    have e : n = p * (p * n) := by rw [← mul_assoc, hM2, one_mul]
    rw [MulAut.one_apply, e, map_mul, hgp, hgW hu]

end Eight

section Nat

open CFSG.Assembly.LowTwoRank A6L76Of
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (unitriangular)

variable {F : Type} [Field F]

theorem eq_zero_or_eq_one [Finite F] (hF : Nat.card F = 2) (c : F) : c = 0 ∨ c = 1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  by_contra h
  push Not at h
  have h3 : ({0, 1, c} : Finset F).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h.1.symm]),
      Finset.card_insert_of_notMem (by simp [h.2.symm]), Finset.card_singleton]
  have h4 := Finset.card_le_univ ({0, 1, c} : Finset F)
  rw [h3, ← Nat.card_eq_fintype_card, hF] at h4
  omega

theorem natHom_injective : Function.Injective (natHom (F := F)) := by
  intro γ δ h
  apply Subtype.ext
  apply Units.ext
  ext i j
  have h1 := congrArg (fun f : MulAut (Multiplicative (Fin 3 → F)) =>
    Multiplicative.toAdd (f (Multiplicative.ofAdd (Pi.single j 1)))) h
  simp only [natHom_apply, toAdd_ofAdd] at h1
  have h2 := congrFun h1 i
  simpa [Matrix.mulVec_single] using h2

theorem eq_of_fix_sylow [Finite F] (hF : Nat.card F = 2) {P : Subgroup ↥(StatedSL 3 F)}
    (hP : IsPGroup 2 ↥P)
    (hodd : ¬ 2 ∣ P.index) {m m' : Multiplicative (Fin 3 → F)} (hm : m ≠ 1) (hm' : m' ≠ 1)
    (hfm : ∀ γ ∈ P, natHom γ m = m) (hfm' : ∀ γ ∈ P, natHom γ m' = m') : m = m' := by
  have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (le_refl 1) (by rw [hF, pow_one])
  obtain ⟨g, hg⟩ := exists_conj_unitriangular_stated hP hodd
  have hgU : ∀ u : Matrix.SpecialLinearGroup (Fin 3) F,
      specialLinearGroupEquivStatedSL 3 F u * g =
        g * (g⁻¹ * specialLinearGroupEquivStatedSL 3 F u * g) := fun u => by group
  have key : ∀ n : Multiplicative (Fin 3 → F), n ≠ 1 → (∀ γ ∈ P, natHom γ n = n) →
      Multiplicative.toAdd (natHom g n) = Pi.single 0 1 := by
    intro n hn hfn
    obtain ⟨v, hv⟩ : ∃ v, Multiplicative.toAdd (natHom g n) = v := ⟨_, rfl⟩
    have hvfix : ∀ u ∈ unitriangular 3 F, (u : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v := by
      intro u hu
      have h3 : natHom (specialLinearGroupEquivStatedSL 3 F u) (natHom g n) = natHom g n := by
        rw [← MulAut.mul_apply, ← map_mul, hgU u, map_mul, MulAut.mul_apply, hfn _ (hg u hu)]
      have h4 := congrArg Multiplicative.toAdd h3
      rw [natHom_apply (specialLinearGroupEquivStatedSL 3 F u) (natHom g n), hv] at h4
      exact h4
    obtain ⟨hv1, hv2⟩ := unitriangular_fix hvfix
    have hv0 : v ≠ 0 := by
      intro h0
      apply hn
      rw [← hv, toAdd_eq_zero, MulEquiv.map_eq_one_iff] at h0
      exact h0
    rw [hv]
    rcases eq_zero_or_eq_one hF (v 0) with h | h
    · exfalso
      apply hv0
      funext i
      fin_cases i
      · exact h
      · exact hv1
      · exact hv2
    · funext i
      fin_cases i
      · simpa using h
      · simpa using hv1
      · simpa using hv2
  have h1 := key m hm hfm
  have h2 := key m' hm' hfm'
  rw [← h2] at h1
  exact (natHom g).injective (Multiplicative.toAdd.injective h1)

end Nat

open CFSG.Assembly.LowTwoRank A6L76Of in
theorem false_of_natSL32 {W : Type*} [CommGroup W] {Y : Subgroup (MulAut W)}
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) {π : ↥(StatedSL 3 F) →* ↥Y}
    (hπ : (FFModel.nat (StatedSL 3 F)).RealizesVia Y (commV Y) (fixV Y ⊓ commV Y) π)
    {a : MulAut W} (haY : a ∈ Y) (ha3 : a ^ 3 = 1)
    {P : Subgroup (MulAut W)} (hP2 : IsPGroup 2 ↥P)
    (hPodd : Odd (P.subgroupOf Y).index) {v₂ : W} (hPv : ∀ p ∈ P, p v₂ = v₂)
    (ha2 : a (a v₂) = v₂ * a v₂) (hv : v₂ ∉ fixV Y)
    {O : Set (MulAut W)} (hOY : O ⊆ Y) (hOv : ∀ o ∈ O, o v₂ = v₂ ∧ o (a v₂) = a v₂)
    (hOa : ∀ o ∈ O, o * a = a * o)
    (hPn : ∀ p ∈ P, ∃ i : ℤ, ∃ o ∈ O, p * a * p⁻¹ = a ^ i * o) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (le_refl 1) (by rw [hF, pow_one])
  obtain ⟨hs, -, β, hβs, hβk, hβe0⟩ := A6L76Z.natRealizes_clean hπ
  have hβe : ∀ (γ : ↥(StatedSL 3 F)) (u : ↥(commV Y))
      (hu : ((π γ : ↥Y) : MulAut W) (u : W) ∈ commV Y), β ⟨_, hu⟩ = natHom γ (β u) :=
    fun γ u hu => hβe0 γ u hu
  have hinj : Function.Injective π :=
    FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ
  have h2 : ∀ m : Multiplicative (Fin 3 → F), m * m = 1 := fun m => by
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_one]
    funext i
    exact CharTwo.add_self_eq_zero _
  have h8 : Nat.card (Multiplicative (Fin 3 → F)) = 8 := by
    rw [show Nat.card (Multiplicative (Fin 3 → F)) = Nat.card (Fin 3 → F) from rfl,
      Nat.card_fun, hF, Nat.card_fin]
    norm_num
  have hv₂c : v₂ ∈ commV Y := by
    have h := A6L76Oe.gen_mem_commV haY (a v₂)
    rwa [ha2, mul_inv_cancel_right] at h
  have hav₂c : a v₂ ∈ commV Y := A6L76Oe.apply_mem_commV haY hv₂c
  obtain ⟨γa, hγa⟩ := hs ⟨a, haY⟩
  have hπa : ∀ w, ((π γa : ↥Y) : MulAut W) w = a w := fun w =>
    congrArg (fun f : MulAut W => f w) (congrArg Subtype.val hγa)
  set x := β ⟨v₂, hv₂c⟩ with hxdef
  set y := β ⟨a v₂, hav₂c⟩ with hydef
  have hm1 : ((π γa : ↥Y) : MulAut W) v₂ ∈ commV Y := by
    rw [hπa]
    exact hav₂c
  have hm2 : ((π γa : ↥Y) : MulAut W) (a v₂) ∈ commV Y := by
    rw [hπa, ha2]
    exact (commV Y).mul_mem hv₂c hav₂c
  have hax : natHom γa x = y := by
    rw [hxdef, ← hβe γa ⟨v₂, hv₂c⟩ hm1]
    congr 1
    exact Subtype.ext (hπa v₂)
  have hay : natHom γa y = x * y := by
    rw [hydef, ← hβe γa ⟨a v₂, hav₂c⟩ hm2, ← map_mul]
    congr 1
    exact Subtype.ext ((hπa (a v₂)).trans ha2)
  have hx : x ≠ 1 := fun h => hv ((hβk _).1 h).1
  have hy : y ≠ 1 := fun h => by
    have h1 := ((hβk _).1 h).1
    have h3 : a⁻¹ (a v₂) = a v₂ := h1 _ (Y.inv_mem haY)
    rw [MulAut.inv_apply_self] at h3
    exact hv (by rw [h3]; exact h1)
  have hxy : x ≠ y := fun h => hy (by
    have h1 := hay
    rw [← h, hax, h2] at h1
    exact h1)
  have hγa3 : γa ^ 3 = 1 := hinj (by
    rw [map_pow, hγa, map_one]
    exact Subtype.ext (by simpa using ha3))
  have hna3 : natHom γa ^ 3 = 1 := by rw [← map_pow, hγa3, map_one]
  obtain ⟨p, hpW, hap, hpu⟩ := exists_fixed_off_line h2 h8 hx hy hxy hax hay hna3
  have hp1 : p ≠ 1 := fun h => hpW (h ▸ Or.inl rfl)
  have hO1 : ∀ o ∈ O, o = 1 := by
    intro o ho
    obtain ⟨γo, hγo⟩ := hs ⟨o, hOY ho⟩
    have hπo : ((π γo : ↥Y) : MulAut W) = o := congrArg Subtype.val hγo
    have hπo' : ∀ w, ((π γo : ↥Y) : MulAut W) w = o w := fun w =>
      congrArg (fun f : MulAut W => f w) hπo
    have hm3 : ((π γo : ↥Y) : MulAut W) v₂ ∈ commV Y := by
      rw [hπo', (hOv o ho).1]
      exact hv₂c
    have hm4 : ((π γo : ↥Y) : MulAut W) (a v₂) ∈ commV Y := by
      rw [hπo', (hOv o ho).2]
      exact hav₂c
    have hox : natHom γo x = x := by
      rw [hxdef, ← hβe γo ⟨v₂, hv₂c⟩ hm3]
      congr 1
      exact Subtype.ext ((hπo' v₂).trans (hOv o ho).1)
    have hoy : natHom γo y = y := by
      rw [hydef, ← hβe γo ⟨a v₂, hav₂c⟩ hm4]
      congr 1
      exact Subtype.ext ((hπo' (a v₂)).trans (hOv o ho).2)
    have hoa : natHom γo * natHom γa = natHom γa * natHom γo := by
      rw [← map_mul, ← map_mul]
      congr 1
      apply hinj
      rw [map_mul, map_mul, hγa, hγo]
      exact Subtype.ext (hOa o ho)
    have h1 := eq_one_of_comm h2 h8 hx hy hxy hax hay hna3 hox hoy hoa
    have h3 : γo = 1 := natHom_injective (by rw [h1, map_one])
    rw [← hπo, h3, map_one]
    rfl
  set P' : Subgroup ↥(StatedSL 3 F) := (P.subgroupOf Y).comap π with hP'
  have hP'2 : IsPGroup 2 ↥P' :=
    (hP2.comap_of_injective Y.subtype Y.subtype_injective).comap_of_injective π hinj
  have hP'odd : ¬ 2 ∣ P'.index := by
    rw [hP', Subgroup.index_comap_of_surjective _ hs]
    obtain ⟨k, hk⟩ := hPodd
    omega
  have hPx : ∀ γ ∈ P', natHom γ x = x := by
    intro γ hγ
    have hγP : ((π γ : ↥Y) : MulAut W) ∈ P := hγ
    have hm5 : ((π γ : ↥Y) : MulAut W) v₂ ∈ commV Y := by
      rw [hPv _ hγP]
      exact hv₂c
    rw [hxdef, ← hβe γ ⟨v₂, hv₂c⟩ hm5]
    congr 1
    exact Subtype.ext (hPv _ hγP)
  have hPp : ∀ γ ∈ P', natHom γ p = p := by
    intro γ hγ
    have hγP : ((π γ⁻¹ : ↥Y) : MulAut W) ∈ P := by
      have h1 : ((π γ : ↥Y) : MulAut W) ∈ P := hγ
      rw [map_inv, Subgroup.coe_inv]
      exact P.inv_mem h1
    obtain ⟨j, o, ho, hj⟩ := hPn _ hγP
    rw [hO1 o ho, mul_one] at hj
    have hj' : γ⁻¹ * γa * γ = γa ^ j := hinj (Subtype.ext (by
      rw [map_mul, map_mul, map_zpow, hγa, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_zpow]
      rw [show ((π γ : ↥Y) : MulAut W) = ((π γ⁻¹ : ↥Y) : MulAut W)⁻¹ by
        rw [map_inv, Subgroup.coe_inv, inv_inv]]
      exact hj))
    have hfix : natHom γa (natHom γ p) = natHom γ p := by
      have e1 : natHom γa * natHom γ = natHom γ * natHom (γ⁻¹ * γa * γ) := by
        rw [← map_mul, ← map_mul]
        congr 1
        group
      have hpz : natHom γa ^ j ∈ MulAction.stabilizer (MulAut (Multiplicative (Fin 3 → F))) p :=
        Subgroup.zpow_mem _ (by rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]; exact hap) j
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def] at hpz
      rw [← MulAut.mul_apply, e1, hj', MulAut.mul_apply, map_zpow, hpz]
    rcases hpu _ hfix with h | h
    · exact absurd ((MulEquiv.map_eq_one_iff _).1 h) hp1
    · exact h
  have hxp := eq_of_fix_sylow hF hP'2 hP'odd hx hp1 hPx hPp
  exact hpW (hxp ▸ Or.inr (Or.inl rfl))

end A6L76N3

namespace Setting4

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)

theorem exists_O2L1_comm_not_mem_QH (h139 : Stmt13_3_9)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
    (hNS : ¬ LieModel G .PSp 3 2 1) (hhat : ¬ IsHatA6 L) {H : Subgroup G} (hH : H ∈ S.Hz)
    [IsMulCommutative ↥(conjClosure S.V3 H)] {K : Subgroup G} (hK : K ∈ cComp H)
    (hL1K : S.L1 ≤ K)
    (hSL : BinaryNaturalSL (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 3 1) :
    ∃ o ∈ pCoreOf 2 S.L1, (S.cL1 hhat : G) * o * (S.cL1 hhat : G)⁻¹ * o⁻¹ ∉ pCoreOf 2 H := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨F, _, _, hF, π, hπ⟩ := id hSL
  have hF2 : Nat.card F = 2 := by rw [hF, pow_one]
  set g := S.cL1 hhat with hgdef
  have hgL1 : (g : G) ∈ S.L1 := S.cL1_mem hhat
  have hgX : (g : G) ∈ S.X1375 := by
    rw [S.X1375_of_not_hat hhat]
    exact hgL1
  have hg : S.frame.ρ g = swap 0 1 * swap 1 2 := S.cL1_rho hhat
  have hg3 : (g : G) ^ 3 = 1 := S.cL1_cube hhat
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHV := S.le_normalizer_UV1 hH
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hL1H : S.L1 ≤ H := hL1K.trans hKH
  have hgH : (g : G) ∈ H := hL1H hgL1
  have hF91 := S.hypF91 hNS h13315 h1356two hH
  obtain ⟨a, P, v₂, ha, hP, hv₂, -, -, hP2, hPodd, hPv, -, ha2, hv⟩ :=
    S.exists_odd_config_of hH hK rfl h139 h37 h38 h13315 hgX hg
  have hmemK : ∀ (k : G) (hk : k ∈ K), A6Mod.secAct hHU hHV ⟨k, hKH hk⟩ ∈
      autSec (autOn K (conjClosure S.V3 H)) ⊤ ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) :=
    fun k hk => (A6Mod.mem_autSec_iff hHU hHV hKH).2 ⟨⟨k, hKH hk⟩, hk, rfl⟩
  have hQ1 : ∀ (q : G) (hq : q ∈ pCoreOf 2 H), A6Mod.secAct hHU hHV ⟨q, pCoreOf_le 2 H hq⟩ = 1 := by
    intro q hq
    refine MulEquiv.ext fun w => ?_
    obtain ⟨u, rfl⟩ := InternalSec.secMk_surjective _ w
    rw [A6Mod.secAct_secMk, MulAut.one_apply]
    apply secMk_eq_of_mem_V1
    rw [Setup.rho_apply_coe]
    exact KeyData.comm_QH_mem hF91 hq u.2
  have haY : a ∈ autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) := by
    rw [ha]
    exact hmemK g (hL1K hgL1)
  have ha3 : a ^ 3 = 1 := by
    rw [ha, ← map_pow]
    have : (⟨g, hgH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hg3)
    rw [this, map_one]
  set O : Set (MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) :=
    {f | ∃ (o : G) (ho : o ∈ pCoreOf 2 S.L1),
      f = A6Mod.secAct hHU hHV ⟨o, hL1H (pCoreOf_le 2 S.L1 ho)⟩} with hOdef
  have hOY : O ⊆ autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) := by
    rintro f ⟨o, ho, rfl⟩
    exact hmemK o (hL1K (pCoreOf_le 2 _ ho))
  have hOv : ∀ f ∈ O, f v₂ = v₂ ∧ f (a v₂) = a v₂ := by
    rintro f ⟨o, ho, rfl⟩
    rw [hv₂, ha, A6Mod.secAct_secMk, A6Mod.secAct_secMk, A6Mod.secAct_secMk]
    constructor
    · apply secMk_eq_of_mem_V1
      rw [Setup.rho_apply_coe]
      exact S.comm_O2L1_V3 ho S.v2_mem_V3
    · apply secMk_eq_of_mem_V1
      rw [Setup.rho_apply_coe, Setup.rho_apply_coe]
      exact S.comm_O2L1_V3 ho (S.conj_v2_mem_V3 hg)
  have hOa : ∀ f ∈ O, f * a = a * f := by
    rintro f ⟨o, ho, rfl⟩
    have hoH : o ∈ H := hL1H (pCoreOf_le 2 S.L1 ho)
    have h2 := hQ1 _ (hcon o ho)
    have e : (⟨(g : G) * o * (g : G)⁻¹ * o⁻¹, pCoreOf_le 2 H (hcon o ho)⟩ : ↥H) =
        ⁅(⟨g, hgH⟩ : ↥H), ⟨o, hoH⟩⁆ := rfl
    rw [e, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
    rw [ha]
    exact h2.symm
  have hPn : ∀ p ∈ P, ∃ i : ℤ, ∃ f ∈ O, p * a * p⁻¹ = a ^ i * f := by
    rw [hP]
    rintro _ ⟨t, ht, rfl⟩
    have ht' : (t : G) ∈ T ⊓ K := ht
    have hx : (t : G) * g * (t : G)⁻¹ ∈ S.L1 :=
      (Subgroup.mem_normalizer_iff.mp (S.T_le_normalizer_L1 ht'.1) g).mp hgL1
    rw [ha]
    rcases S.L1_decomp hhat hx with h | h | h <;> try rw [← hgdef] at h
    · refine ⟨0, _, ⟨_, h, rfl⟩, ?_⟩
      rw [zpow_zero, one_mul, ← map_inv, ← map_mul, ← map_mul]
      rfl
    · refine ⟨-2, _, ⟨_, h, rfl⟩, ?_⟩
      rw [← map_inv, ← map_mul, ← map_mul, ← map_zpow, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
      group
    · refine ⟨-1, _, ⟨_, h, rfl⟩, ?_⟩
      rw [← map_inv, ← map_mul, ← map_mul, ← map_zpow, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
      group
  exact A6L76N3.false_of_natSL32 hF2 hπ haY ha3 hP2 hPodd hPv ha2 hv hOY hOv hOa hPn

end Setting4

end CFSG.Quasithin.H13.A6
