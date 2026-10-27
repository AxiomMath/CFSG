module

public import CFSG.Quasithin.Recognition.SzR1Fam
public import CFSG.Quasithin.Recognition.SzR1Gram

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SzR1 CFSG.Quasithin.F7

open Classical in
@[expose] noncomputable def zbit {G : Type} [Group G] (x : G) : ZMod 2 := if x = 1 then 0 else 1

theorem zbit_one {G : Type} [Group G] : zbit (1 : G) = 0 := by simp [zbit]

theorem zbit_eq_zero_iff {G : Type} [Group G] {x : G} : zbit x = 0 ↔ x = 1 := by
  unfold zbit
  split_ifs with h <;> simp [h]

theorem zbit_mul {G : Type} [Group G] {z x y : G} (hzz : z * z = 1) (hz1 : z ≠ 1)
    (hx : x = 1 ∨ x = z) (hy : y = 1 ∨ y = z) : zbit (x * y) = zbit x + zbit y := by
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy]
  · simp [zbit]
  · rw [one_mul, zbit_one, zero_add]
  · rw [mul_one, zbit_one, add_zero]
  · rw [hzz]
    have : zbit z = 1 := by simp [zbit, hz1]
    rw [this, zbit_one]
    decide

theorem exists_ne_of_one_lt {Ω : Type} [Fintype Ω] (hn : 1 < Fintype.card Ω) :
    ∃ i j : Ω, i ≠ j := Fintype.exists_pair_of_one_lt_card hn

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G} {Ω : Type}
  (C : FamCtx K1 L2 S Zs Ω) [Fintype Ω] [DecidableEq Ω]

@[expose] noncomputable def fb (q : G) (ω : Ω) : ZMod 2 :=
  zbit (q * C.zf ω * q⁻¹ * (C.zf ω)⁻¹)

variable {z : G} (hzZ : z ∈ Zs) (hz1 : z ≠ 1)

include C hzZ hz1

omit [Fintype Ω] [DecidableEq Ω] in
theorem Zs_cases {x : G} (hx : x ∈ Zs) : x = 1 ∨ x = z := by
  have hz2 : z * z = 1 := C.Zs_sq hzZ
  rw [C.Zs_eq_zpowers hzZ hz1] at hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have h1 : z ^ k = z ^ (k % (orderOf z : ℤ)) := (zpow_mod_orderOf z k).symm
  rw [h1, hord]
  have : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by
    push_cast
    omega
  rcases this with h | h <;> rw [h] <;> simp

omit [Fintype Ω] [DecidableEq Ω] hzZ hz1 in
theorem comm_mem_Zs {q : G} (hq : q ∈ vBeta K1 L2 S Zs) (ω : Ω) :
    q * C.zf ω * q⁻¹ * (C.zf ω)⁻¹ ∈ Zs := C.U_comm_mem hq (C.zf_mem_U ω)

omit [Fintype Ω] [DecidableEq Ω] in
theorem fb_mul {q q' : G} (hq : q ∈ vBeta K1 L2 S Zs) (hq' : q' ∈ vBeta K1 L2 S Zs) (ω : Ω) :
    fb C (q * q') ω = fb C q ω + fb C q' ω := by
  have hc := comm_mem_Zs C hq ω
  have hc' := comm_mem_Zs C hq' ω
  have e : q * q' * C.zf ω * (q * q')⁻¹ * (C.zf ω)⁻¹ =
      (q' * C.zf ω * q'⁻¹ * (C.zf ω)⁻¹) * (q * C.zf ω * q⁻¹ * (C.zf ω)⁻¹) := by
    have hcomm := C.Zs_central hq hc'
    calc q * q' * C.zf ω * (q * q')⁻¹ * (C.zf ω)⁻¹
        = q * (q' * C.zf ω * q'⁻¹ * (C.zf ω)⁻¹) * q⁻¹ * (q * C.zf ω * q⁻¹ * (C.zf ω)⁻¹) := by
          group
      _ = ((q' * C.zf ω * q'⁻¹ * (C.zf ω)⁻¹) * q) * q⁻¹ *
          (q * C.zf ω * q⁻¹ * (C.zf ω)⁻¹) := by rw [hcomm]
      _ = _ := by group
  unfold fb
  rw [e, zbit_mul (C.Zs_sq hzZ) hz1 (Zs_cases C hzZ hz1 hc') (Zs_cases C hzZ hz1 hc), add_comm]

omit [Fintype Ω] [DecidableEq Ω] hzZ hz1 in
theorem fb_one (ω : Ω) : fb C (1 : G) ω = 0 := by
  unfold fb
  have : (1 : G) * C.zf ω * (1 : G)⁻¹ * (C.zf ω)⁻¹ = 1 := by group
  rw [this, zbit_one]

omit [Fintype Ω] hzZ hz1 in
theorem fb_zf {a : Ω} (ω : Ω) (hij : ∃ i j : Ω, i ≠ j) :
    fb C (C.zf a) ω = if a = ω then 0 else 1 := by
  obtain ⟨i₀, j₀, hij⟩ := hij
  unfold fb
  by_cases h : a = ω
  · subst h
    have : C.zf a * C.zf a * (C.zf a)⁻¹ * (C.zf a)⁻¹ = 1 := by group
    rw [this, zbit_one]; simp
  · have hcm : C.cm a ω = C.cm i₀ j₀ := C.cm_const hij h
    have hne : C.cm i₀ j₀ ≠ 1 := C.cm_ne_one hij
    have : C.zf a * C.zf ω * (C.zf a)⁻¹ * (C.zf ω)⁻¹ = C.cm i₀ j₀ := hcm
    rw [this]
    simp [zbit, hne, h]


omit [Fintype Ω] [DecidableEq Ω] in
theorem fb_inv {q : G} (hq : q ∈ vBeta K1 L2 S Zs) (ω : Ω) : fb C q⁻¹ ω = fb C q ω := by
  have := fb_mul C hzZ hz1 hq ((vBeta K1 L2 S Zs).inv_mem hq) ω
  rw [mul_inv_cancel, fb_one] at this
  have key : ∀ a b : ZMod 2, 0 = a + b → b = a := by decide
  exact key _ _ this

theorem fb_pair {i j : Ω} (hij : i ≠ j) (hn : 1 < Fintype.card Ω) (ω : Ω) :
    fb C (C.zf i * C.zf j) ω = (if ω = i then 1 else 0) + (if ω = j then 1 else 0) := by
  rw [fb_mul C hzZ hz1 (C.zf_mem_U i) (C.zf_mem_U j), fb_zf C (a := i) ω (exists_ne_of_one_lt hn),
    fb_zf C (a := j) ω (exists_ne_of_one_lt hn)]
  have hji : j ≠ i := Ne.symm hij
  by_cases h1 : ω = i
  · simp [h1, hij, hji]
  · by_cases h2 : ω = j
    · simp [h2, hij, hji]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]
      decide

theorem sum_fb (hodd : Odd (Fintype.card Ω)) (hn : 1 < Fintype.card Ω) {q : G}
    (hq : q ∈ vBeta K1 L2 S Zs) : ∑ ω, fb C q ω = 0 := by
  obtain ⟨i₀, j₀, hij⟩ := exists_ne_of_one_lt hn
  have hcl := C.U_eq_closure hzZ hz1
  have hWcl : ∀ x ∈ Subgroup.closure (insert z (Set.range C.zf)), x ∈ vBeta K1 L2 S Zs := by
    intro x hx; rw [hcl]; exact hx
  rw [hcl] at hq
  induction hq using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | ⟨a, rfl⟩
    · have h0 : ∀ ω, fb C x ω = 0 := by
        intro ω
        unfold fb
        have h := C.Zs_central (C.zf_mem_U ω) hzZ
        have h1 : x * C.zf ω * x⁻¹ * (C.zf ω)⁻¹ = 1 := by rw [← h]; group
        rw [h1, zbit_one]
      simp [h0]
    · have hf : ∀ ω, fb C (C.zf a) ω = if a = ω then 0 else 1 := fun ω =>
        fb_zf C ω ⟨i₀, j₀, hij⟩
      have hoth : ∀ ω ∈ Finset.univ.erase a, fb C (C.zf a) ω = 1 := fun ω hω => by
        rw [hf]; simp [Ne.symm (Finset.ne_of_mem_erase hω)]
      have h0 : fb C (C.zf a) a = 0 := by rw [hf]; simp
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), h0, Finset.sum_congr rfl hoth]
      simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ,
        nsmul_eq_mul, mul_one, zero_add]
      obtain ⟨r, hr⟩ := hodd
      rw [hr, Nat.add_sub_cancel]
      push_cast
      have h2 : (2 : ZMod 2) = 0 := by decide
      simp [h2]
  | one => simp [fb_one]
  | mul x y hx hy ihx ihy =>
    simp only [fb_mul C hzZ hz1 (hWcl x hx) (hWcl y hy), Finset.sum_add_distrib, ihx, ihy, add_zero]
  | inv x hx ih =>
    have hxW := hWcl x hx
    have h1 : ∀ ω, fb C x⁻¹ ω = fb C x ω := by
      intro ω
      have := fb_mul C hzZ hz1 hxW ((vBeta K1 L2 S Zs).inv_mem hxW) ω
      rw [mul_inv_cancel, fb_one] at this
      have key : ∀ a b : ZMod 2, 0 = a + b → b = a := by decide
      exact key _ _ this
    simp only [h1]
    exact ih


theorem exists_fb_eq_indicator (hn : 1 < Fintype.card Ω) :
    ∀ (m : ℕ) (U : Finset Ω), U.card = m → Even m →
      ∃ q ∈ vBeta K1 L2 S Zs, ∀ ω, fb C q ω = if ω ∈ U then 1 else 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro U hS hev
    by_cases hm0 : m = 0
    · subst hm0
      rw [Finset.card_eq_zero] at hS
      subst hS
      exact ⟨1, (vBeta K1 L2 S Zs).one_mem, fun ω => by simp [fb_one]⟩
    · have hm2 : 1 < U.card := by
        rw [hS]; obtain ⟨r, hr⟩ := hev; omega
      obtain ⟨i, hi⟩ : U.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨j, hj, hji⟩ := Finset.exists_mem_ne hm2 i
      have hcard : ((U.erase i).erase j).card = m - 2 := by
        rw [Finset.card_erase_of_mem (by simp [Finset.mem_erase, hj, hji]),
          Finset.card_erase_of_mem hi, hS]
        omega
      have hev' : Even (m - 2) := by
        obtain ⟨r, hr⟩ := hev
        exact ⟨r - 1, by omega⟩
      obtain ⟨q', hq'W, hq'⟩ := ih (m - 2) (by omega) ((U.erase i).erase j) hcard hev'
      refine ⟨q' * (C.zf i * C.zf j),
        (vBeta K1 L2 S Zs).mul_mem hq'W
          ((vBeta K1 L2 S Zs).mul_mem (C.zf_mem_U i) (C.zf_mem_U j)), fun ω => ?_⟩
      rw [fb_mul C hzZ hz1 hq'W ((vBeta K1 L2 S Zs).mul_mem (C.zf_mem_U i) (C.zf_mem_U j)),
        hq', fb_pair C hzZ hz1 (Ne.symm hji) hn]
      by_cases h1 : ω = i
      · subst h1
        simp [hi, Ne.symm hji]
      · by_cases h2 : ω = j
        · subst h2
          simp [hj, hji]
        · simp [h1, h2, Finset.mem_erase]

theorem exists_fb_eq (hn : 1 < Fintype.card Ω) (g : Ω → ZMod 2) (hsum : ∑ ω, g ω = 0) :
    ∃ q ∈ vBeta K1 L2 S Zs, ∀ ω, fb C q ω = g ω := by
  have h01 : ∀ x : ZMod 2, x = if x ≠ 0 then 1 else 0 := by decide
  set T := Finset.univ.filter (fun ω => g ω ≠ 0) with hT
  have hsumT : ∑ ω, g ω = (T.card : ZMod 2) := by
    calc ∑ ω, g ω = ∑ ω, (if g ω ≠ 0 then (1 : ZMod 2) else 0) :=
          Finset.sum_congr rfl (fun ω _ => h01 (g ω))
      _ = (T.card : ZMod 2) := by rw [Finset.sum_boole]
  have hev : Even T.card := by
    rw [hsumT] at hsum
    exact (even_iff_two_dvd).mpr ((ZMod.natCast_eq_zero_iff _ 2).mp hsum)
  obtain ⟨q, hqW, hq⟩ := exists_fb_eq_indicator C hzZ hz1 hn T.card T rfl hev
  refine ⟨q, hqW, fun ω => ?_⟩
  rw [hq]
  simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (h01 (g ω)).symm

end CFSG.Quasithin.Background.Harris.R1
