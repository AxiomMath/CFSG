module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Quasithin.H13.R2

open CFSG.Open
open scoped commutatorElement

variable {P : Type} [Group P] [Finite P]

structure Hyp (P : Type) [Group P] [Finite P] (x y : P) (a s : MulAut P) : Prop where
  p3 : IsPGroup 3 P
  index : (frattini P).index = 9
  m3 : ∀ E : Subgroup P, IsElemAbelian 3 E → Nat.card E ≤ 9
  gen : Subgroup.closure {x, y} = ⊤
  ax : a x * x ∈ frattini P
  ay : y⁻¹ * a y ∈ frattini P
  sx : y⁻¹ * s x ∈ frattini P
  sy : x⁻¹ * s y ∈ frattini P

omit [Finite P] in
theorem mem_frattini_of_mulAut (φ : MulAut P) {g : P} (hg : g ∈ frattini P) :
    φ g ∈ frattini P := by
  have h := (Subgroup.characteristic_iff_comap_eq.mp
    (inferInstance : (frattini P).Characteristic)) φ
  rw [← h] at hg
  exact hg

omit [Finite P] in
@[expose] noncomputable def barMap (φ : MulAut P) : P ⧸ frattini P →* P ⧸ frattini P :=
  QuotientGroup.map (frattini P) (frattini P) φ.toMonoidHom fun _ hg =>
    mem_frattini_of_mulAut φ hg

omit [Finite P] in
theorem barMap_mk (φ : MulAut P) (g : P) :
    barMap φ (g : P ⧸ frattini P) = ((φ g : P) : P ⧸ frattini P) := rfl

section Quot

variable {x y : P} {a s : MulAut P} (h : Hyp P x y a s)
include h

theorem quot_comm (q q' : P ⧸ frattini P) : q * q' = q' * q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (IsPGroup 3 P) := ⟨h.p3⟩
  induction q using QuotientGroup.induction_on with
  | H g =>
  induction q' using QuotientGroup.induction_on with
  | H g' =>
  have hc : ⁅g, g'⁆ ∈ frattini P := CFSG.commutator_le_frattini_of_isPGroup (p := 3)
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top g'))
  have h1 : QuotientGroup.mk' (frattini P) ⁅g, g'⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hc
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

theorem quot_cube (q : P ⧸ frattini P) : q ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (IsPGroup 3 P) := ⟨h.p3⟩
  induction q using QuotientGroup.induction_on with
  | H g =>
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact CFSG.pth_power_mem_frattini_of_isPGroup g

noncomputable abbrev quotComm : CommGroup (P ⧸ frattini P) :=
  { (inferInstance : Group (P ⧸ frattini P)) with mul_comm := quot_comm h }

theorem bar_a_x : barMap a (x : P ⧸ frattini P) = (x : P ⧸ frattini P)⁻¹ := by
  rw [barMap_mk]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
  exact h.ax

theorem bar_a_y : barMap a (y : P ⧸ frattini P) = (y : P ⧸ frattini P) := by
  rw [barMap_mk]
  refine (QuotientGroup.eq.mpr ?_).symm
  exact h.ay

theorem bar_s_x : barMap s (x : P ⧸ frattini P) = (y : P ⧸ frattini P) := by
  rw [barMap_mk]
  exact (QuotientGroup.eq.mpr h.sx).symm

theorem bar_s_y : barMap s (y : P ⧸ frattini P) = (x : P ⧸ frattini P) := by
  rw [barMap_mk]
  exact (QuotientGroup.eq.mpr h.sy).symm

theorem quot_gen (q : P ⧸ frattini P) :
    ∃ i j : ℕ, q = (x : P ⧸ frattini P) ^ i * (y : P ⧸ frattini P) ^ j := by
  let _ := quotComm h
  have hcl : Subgroup.closure {(x : P ⧸ frattini P), (y : P ⧸ frattini P)} = ⊤ := by
    have := congrArg (Subgroup.map (QuotientGroup.mk' (frattini P))) h.gen
    rw [MonoidHom.map_closure, Set.image_pair,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at this
    exact this
  have hq : q ∈ Subgroup.closure {(x : P ⧸ frattini P), (y : P ⧸ frattini P)} :=
    hcl ▸ Subgroup.mem_top q
  induction hq using Subgroup.closure_induction with
  | mem z hz =>
    rcases hz with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul z w _ _ ihz ihw =>
    obtain ⟨i, j, rfl⟩ := ihz
    obtain ⟨k, l, rfl⟩ := ihw
    exact ⟨i + k, j + l, by rw [pow_add, pow_add, mul_mul_mul_comm]⟩
  | inv z _ ihz =>
    obtain ⟨i, j, rfl⟩ := ihz
    refine ⟨2 * i, 2 * j, ?_⟩
    have h3 := quot_cube h ((x : P ⧸ frattini P) ^ i * (y : P ⧸ frattini P) ^ j)
    rw [pow_mul', pow_mul', ← mul_pow]
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [← pow_succ]
    exact h3

theorem quot_card : Nat.card (P ⧸ frattini P) = 9 := h.index

theorem quot_indep {i j : ℕ}
    (hij : (x : P ⧸ frattini P) ^ i * (y : P ⧸ frattini P) ^ j = 1) : 3 ∣ i ∧ 3 ∣ j := by
  set u := (x : P ⧸ frattini P)
  set v := (y : P ⧸ frattini P)
  have hu : u ^ 3 = 1 := quot_cube h u
  have hv : v ^ 3 = 1 := quot_cube h v
  have hred : ∀ (w : P ⧸ frattini P), w ^ 3 = 1 → ∀ k : ℕ, w ^ k = w ^ (k % 3) := by
    intro w hw k
    conv_lhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, hw, one_pow, one_mul]
  let f : Fin 3 × Fin 3 → P ⧸ frattini P := fun ij => u ^ (ij.1 : ℕ) * v ^ (ij.2 : ℕ)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨i, j, rfl⟩ := quot_gen h q
    refine ⟨(⟨i % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨j % 3, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
    simp only [f]
    rw [← hred u hu, ← hred v hv]
  have hcard : Nat.card (Fin 3 × Fin 3) ≤ Nat.card (P ⧸ frattini P) := by
    rw [quot_card h, Nat.card_eq_fintype_card]; simp
  have hinj := (hf.bijective_of_nat_card_le hcard).1
  have h0 : f (⟨i % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨j % 3, Nat.mod_lt _ (by norm_num)⟩) =
      f (0, 0) := by
    simp only [f]
    rw [← hred u hu, ← hred v hv, hij]
    simp
  have := hinj h0
  simp only [Prod.mk.injEq, Fin.ext_iff, Fin.val_zero] at this
  exact ⟨Nat.dvd_of_mod_eq_zero this.1, Nat.dvd_of_mod_eq_zero this.2⟩

theorem pow_eq_one_of_dvd {w : P ⧸ frattini P} {k : ℕ} (hk : 3 ∣ k) : w ^ k = 1 := by
  obtain ⟨m, rfl⟩ := hk
  rw [pow_mul, quot_cube h, one_pow]

theorem quot_inv_eq (H : Subgroup (P ⧸ frattini P)) (ha : ∀ q ∈ H, barMap a q ∈ H)
    (hs : ∀ q ∈ H, barMap s q ∈ H) : H = ⊥ ∨ H = ⊤ := by
  let _ := quotComm h
  set u := (x : P ⧸ frattini P)
  set v := (y : P ⧸ frattini P)
  by_cases hb : H = ⊥
  · exact Or.inl hb
  right
  obtain ⟨⟨q, hqH⟩, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hb
  have hq1' : q ≠ 1 := fun e => hq1 (Subtype.ext e)
  obtain ⟨i, j, rfl⟩ := quot_gen h q
  have haq : barMap a (u ^ i * v ^ j) = u⁻¹ ^ i * v ^ j := by
    rw [map_mul, map_pow, map_pow, bar_a_x h, bar_a_y h]
  have h1 : v ^ (2 * j) ∈ H := by
    have := H.mul_mem hqH (ha _ hqH)
    rw [haq] at this
    convert this using 1
    rw [mul_mul_mul_comm, inv_pow, mul_inv_cancel, one_mul, ← pow_add, two_mul]
  have h2 : u ^ (2 * i) ∈ H := by
    have := H.mul_mem hqH (H.inv_mem (ha _ hqH))
    rw [haq] at this
    convert this using 1
    rw [mul_inv, inv_pow, inv_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one, ← pow_add,
      two_mul]
  have hgen : ∀ w : P ⧸ frattini P, w ^ 3 = 1 → w ^ (2 * i) ∈ H → ¬ 3 ∣ i → w ∈ H := by
    intro w hw hwH hi
    have hr : i % 3 = 1 ∨ i % 3 = 2 := by omega
    have hred : w ^ (2 * i) = w ^ ((2 * i) % 3) := by
      conv_lhs => rw [← Nat.div_add_mod (2 * i) 3, pow_add, pow_mul, hw, one_pow, one_mul]
    rcases hr with hr | hr
    · have e : (2 * i) % 3 = 2 := by omega
      rw [hred, e] at hwH
      have := H.mul_mem hwH hwH
      rwa [← pow_add, show 2 + 2 = 3 + 1 by rfl, pow_add, hw, one_mul, pow_one] at this
    · have e : (2 * i) % 3 = 1 := by omega
      rwa [hred, e, pow_one] at hwH
  have hall : u ∈ H → v ∈ H → H = ⊤ := by
    intro hu hv
    rw [eq_top_iff]
    intro q _
    obtain ⟨k, l, rfl⟩ := quot_gen h q
    exact H.mul_mem (H.pow_mem hu _) (H.pow_mem hv _)
  by_cases hi : 3 ∣ i
  · have hj : ¬ 3 ∣ j := by
      intro hj
      apply hq1'
      rw [pow_eq_one_of_dvd h hi, pow_eq_one_of_dvd h hj, one_mul]
    have hv : v ∈ H := by
      have hr : j % 3 = 1 ∨ j % 3 = 2 := by omega
      have hred : v ^ (2 * j) = v ^ ((2 * j) % 3) := by
        conv_lhs => rw [← Nat.div_add_mod (2 * j) 3, pow_add, pow_mul, quot_cube h v, one_pow,
          one_mul]
      rcases hr with hr | hr
      · have e : (2 * j) % 3 = 2 := by omega
        have h1' := h1
        rw [hred, e] at h1'
        have := H.mul_mem h1' h1'
        rwa [← pow_add, show 2 + 2 = 3 + 1 by rfl, pow_add, quot_cube h v, one_mul,
          pow_one] at this
      · have e : (2 * j) % 3 = 1 := by omega
        have h1' := h1
        rwa [hred, e, pow_one] at h1'
    have hu : u ∈ H := by
      have := hs _ hv
      rwa [bar_s_y h] at this
    exact hall hu hv
  · have hu : u ∈ H := hgen u (quot_cube h u) h2 hi
    have hv : v ∈ H := by
      have := hs _ hu
      rwa [bar_s_x h] at this
    exact hall hu hv

theorem quot_eq_one_of_inv {q : P ⧸ frattini P} (ha : barMap a q = q⁻¹)
    (hs : barMap s q = q⁻¹) : q = 1 := by
  let _ := quotComm h
  set u := (x : P ⧸ frattini P)
  set v := (y : P ⧸ frattini P)
  obtain ⟨i, j, rfl⟩ := quot_gen h q
  rw [map_mul, map_pow, map_pow, bar_a_x h, bar_a_y h, mul_inv, inv_pow] at ha
  rw [map_mul, map_pow, map_pow, bar_s_x h, bar_s_y h, mul_inv] at hs
  have hv' : v ^ j = (v ^ j)⁻¹ := mul_left_cancel ha
  have hj : 3 ∣ j := by
    have e : v ^ (2 * j) = 1 := by
      rw [two_mul, pow_add]
      nth_rewrite 1 [hv']
      exact inv_mul_cancel _
    have := quot_indep h (i := 0) (j := 2 * j) (by rw [pow_zero, one_mul, e])
    omega
  have huj : u ^ j = 1 := pow_eq_one_of_dvd h hj
  have hvj : v ^ j = 1 := pow_eq_one_of_dvd h hj
  rw [huj, hvj, mul_one, inv_one, mul_one] at hs
  have hi : 3 ∣ i := by
    have e : u ^ i * v ^ i = 1 := by rw [hs, mul_inv_cancel]
    exact (quot_indep h e).1
  rw [pow_eq_one_of_dvd h hi, hvj, mul_one]

theorem quot_eq_one_of_fix {q : P ⧸ frattini P} (ha : barMap a q = q) (hs : barMap s q = q) :
    q = 1 := by
  let _ := quotComm h
  set u := (x : P ⧸ frattini P)
  set v := (y : P ⧸ frattini P)
  obtain ⟨i, j, rfl⟩ := quot_gen h q
  rw [map_mul, map_pow, map_pow, bar_a_x h, bar_a_y h, inv_pow] at ha
  rw [map_mul, map_pow, map_pow, bar_s_x h, bar_s_y h] at hs
  have hu' : (u ^ i)⁻¹ = u ^ i := mul_right_cancel ha
  have hi : 3 ∣ i := by
    have e : u ^ (2 * i) = 1 := by
      rw [two_mul, pow_add]
      nth_rewrite 1 [← hu']
      exact inv_mul_cancel _
    have := quot_indep h (i := 2 * i) (j := 0) (by rw [pow_zero, mul_one, e])
    omega
  have hui : u ^ i = 1 := pow_eq_one_of_dvd h hi
  have hvi : v ^ i = 1 := pow_eq_one_of_dvd h hi
  rw [hui, hvi, one_mul, one_mul] at hs
  have hj : 3 ∣ j := by
    have e : u ^ j * v ^ (2 * j) = 1 := by
      rw [hs, ← pow_add, show j + 2 * j = 3 * j by ring, pow_mul, quot_cube h v, one_pow]
    exact (quot_indep h e).1
  rw [hui, pow_eq_one_of_dvd h hj, mul_one]

end Quot

section Transfer

variable {x y : P} {a s : MulAut P} (h : Hyp P x y a s)
include h

theorem eq_frattini_or_top {H : Subgroup P} (hH : frattini P ≤ H) (ha : ∀ g ∈ H, a g ∈ H)
    (hs : ∀ g ∈ H, s g ∈ H) : H = frattini P ∨ H = ⊤ := by
  set π := QuotientGroup.mk' (frattini P) with hπ
  have ha' : ∀ q ∈ H.map π, barMap a q ∈ H.map π := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨a g, ha g hg, rfl⟩
  have hs' : ∀ q ∈ H.map π, barMap s q ∈ H.map π := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨s g, hs g hg, rfl⟩
  rcases quot_inv_eq h (H.map π) ha' hs' with hb | ht
  · left
    refine le_antisymm (fun g hg => ?_) hH
    have : π g ∈ H.map π := ⟨g, hg, rfl⟩
    rw [hb, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact this
  · right
    rw [eq_top_iff]
    intro g _
    have : π g ∈ H.map π := ht ▸ Subgroup.mem_top _
    obtain ⟨g', hg', he⟩ := this
    have hk : g'⁻¹ * g ∈ frattini P := QuotientGroup.eq.mp he
    have := H.mul_mem hg' (hH hk)
    simpa using this

theorem le_frattini_or_eq_top {H : Subgroup P} (ha : ∀ g ∈ H, a g ∈ H) (hs : ∀ g ∈ H, s g ∈ H) :
    H ≤ frattini P ∨ H = ⊤ := by
  have hsup : ∀ φ : MulAut P, (∀ g ∈ H, φ g ∈ H) →
      ∀ g ∈ H ⊔ frattini P, φ g ∈ H ⊔ frattini P := by
    intro φ hφ g hg
    have hle : H ⊔ frattini P ≤ (H ⊔ frattini P).comap φ.toMonoidHom :=
      sup_le (fun k hk => Subgroup.mem_sup_left (hφ k hk))
        (fun k hk => Subgroup.mem_sup_right (mem_frattini_of_mulAut φ hk))
    exact hle hg
  rcases eq_frattini_or_top h le_sup_right (hsup a ha) (hsup s hs) with he | ht
  · exact Or.inl (le_sup_left.trans he.le)
  · exact Or.inr (frattini_nongenerating ht)

theorem mem_frattini_of_inv {g : P} (ha : a g * g ∈ frattini P) (hs : s g * g ∈ frattini P) :
    g ∈ frattini P := by
  have h1 : (g : P ⧸ frattini P) = 1 := by
    refine quot_eq_one_of_inv h ?_ ?_
    · rw [barMap_mk]
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
      exact ha
    · rw [barMap_mk]
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
      exact hs
  exact (QuotientGroup.eq_one_iff _).mp h1

theorem mem_frattini_of_fix {g : P} (ha : g⁻¹ * a g ∈ frattini P)
    (hs : g⁻¹ * s g ∈ frattini P) : g ∈ frattini P := by
  have h1 : (g : P ⧸ frattini P) = 1 :=
    quot_eq_one_of_fix h (by rw [barMap_mk]; exact (QuotientGroup.eq.mpr ha).symm)
      (by rw [barMap_mk]; exact (QuotientGroup.eq.mpr hs).symm)
  exact (QuotientGroup.eq_one_iff _).mp h1

end Transfer

end CFSG.Quasithin.H13.R2
