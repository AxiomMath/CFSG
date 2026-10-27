module

public import CFSG.Milestones.ASVolI.F4K.Iface
public import CFSG.Milestones.ASVolI.F4K.Base

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF
open scoped Pointwise

section General

variable {V : Type*}

theorem burnsideF4k_pb_mod (z : ℕ → V) (hper : ∀ i, z (i + 2 * 6) = z i) (n : ℕ) :
    z ((n : ZMod 12).val) = z n := by
  rw [ZMod.val_natCast]
  exact Function.Periodic.map_mod_nat (fun x => hper x) n

theorem burnsideF4k_pb_refl {Γ : SimpleGraph V} {H : Type*} [Group H] [MulAction H V]
    [GraphAction H Γ] (z : ℕ → V) (hz : ∀ i, Γ.Adj (z i) (z (i + 1)))
    (hper : ∀ i, z (i + 2 * 6) = z i) (g : H) (i : ℕ)
    (h1 : g • GPath.arc₁ z hz 6 i = GPath.arc₂ z hz 6 i)
    (h2 : g • GPath.arc₂ z hz 6 i = GPath.arc₁ z hz 6 i) (a : ZMod 12) :
    g • z a.val = z (2 * (i : ZMod 12) - a).val := by
  have e1 : ∀ j, j ≤ 6 → (GPath.arc₁ z hz 6 i).toFun j = z (i + j) := fun j hj =>
    GPath.seqPath_apply z hz i 6 hj
  have e2 : ∀ j, j ≤ 6 → (GPath.arc₂ z hz 6 i).toFun j = z (i + 2 * 6 - j) := fun j hj =>
    GPath.seqPathRev_apply z hz (i + 2 * 6) 6 (by omega) hj
  have hA : ∀ j, j ≤ 6 → g • z (i + j) = z (i + 2 * 6 - j) := by
    intro j hj
    have h := (GPath.smul_eq_iff.mp h1) j hj
    rwa [e1 j hj, e2 j hj] at h
  have hB : ∀ j, j ≤ 6 → g • z (i + 2 * 6 - j) = z (i + j) := by
    intro j hj
    have h := (GPath.smul_eq_iff.mp h2) j hj
    rwa [e1 j hj, e2 j hj] at h
  have h12 : (12 : ZMod 12) = 0 := rfl
  obtain ⟨d, hd⟩ : ∃ d, d = (a - (i : ZMod 12)).val := ⟨_, rfl⟩
  have hdlt : d < 12 := hd ▸ ZMod.val_lt _
  have hdcast : (d : ZMod 12) = a - i := by rw [hd, ZMod.natCast_zmod_val]
  by_cases h6 : d ≤ 6
  · have f1 : a = ((i + d : ℕ) : ZMod 12) := by
      push_cast
      rw [hdcast]
      ring
    have f2 : 2 * (i : ZMod 12) - a = ((i + 2 * 6 - d : ℕ) : ZMod 12) := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      linear_combination hdcast - h12
    rw [f2, f1, burnsideF4k_pb_mod z hper, burnsideF4k_pb_mod z hper]
    exact hA d h6
  · have hj : i + 2 * 6 - (12 - d) = i + d := by omega
    have f1 : a = ((i + 2 * 6 - (12 - d) : ℕ) : ZMod 12) := by
      rw [hj]
      push_cast
      rw [hdcast]
      ring
    have f2 : 2 * (i : ZMod 12) - a = ((i + (12 - d) : ℕ) : ZMod 12) := by
      rw [Nat.cast_add, Nat.cast_sub hdlt.le]
      push_cast
      linear_combination hdcast - h12
    rw [f2, f1, burnsideF4k_pb_mod z hper, burnsideF4k_pb_mod z hper]
    exact hB (12 - d) (by omega)

@[expose] def burnsideF4k_pb_DihAct {H : Type*} [SMul H V] (z : ℕ → V) (w : H) : Prop :=
  ∃ b : ZMod 12, (∀ a : ZMod 12, w • z a.val = z (a + 4 * b).val) ∨
    ∀ a : ZMod 12, w • z a.val = z (2 + 4 * b - a).val

variable {H : Type*} [Group H] [MulAction H V]

theorem burnsideF4k_pb_dihAct_one (z : ℕ → V) : burnsideF4k_pb_DihAct z (1 : H) :=
  ⟨0, Or.inl fun a => by rw [one_smul, mul_zero, add_zero]⟩

theorem burnsideF4k_pb_dihAct_mul {z : ℕ → V} {w₁ w₂ : H} (h₁ : burnsideF4k_pb_DihAct z w₁)
    (h₂ : burnsideF4k_pb_DihAct z w₂) : burnsideF4k_pb_DihAct z (w₁ * w₂) := by
  obtain ⟨b₁, h₁ | h₁⟩ := h₁ <;> obtain ⟨b₂, h₂ | h₂⟩ := h₂
  · refine ⟨b₁ + b₂, Or.inl fun a => ?_⟩
    rw [mul_smul, h₂, h₁]
    congr 2
    ring
  · refine ⟨b₁ + b₂, Or.inr fun a => ?_⟩
    rw [mul_smul, h₂, h₁]
    congr 2
    ring
  · refine ⟨b₁ - b₂, Or.inr fun a => ?_⟩
    rw [mul_smul, h₂, h₁]
    congr 2
    ring
  · refine ⟨b₁ - b₂, Or.inl fun a => ?_⟩
    rw [mul_smul, h₂, h₁]
    congr 2
    ring

theorem burnsideF4k_pb_dihAct_inv {z : ℕ → V} {w : H} (h : burnsideF4k_pb_DihAct z w) :
    burnsideF4k_pb_DihAct z w⁻¹ := by
  obtain ⟨b, h | h⟩ := h
  · refine ⟨-b, Or.inl fun a => ?_⟩
    rw [inv_smul_eq_iff, h]
    congr 2
    ring
  · refine ⟨b, Or.inr fun a => ?_⟩
    rw [inv_smul_eq_iff, h]
    congr 2
    ring

end General

theorem burnsideF4k_pb_orbit_one (b : ZMod 12) :
    ((1 + 4 * b).val = 1 ∨ (1 + 4 * b).val = 5 ∨ (1 + 4 * b).val = 9) ∧
      ((2 + 4 * b - 1).val = 1 ∨ (2 + 4 * b - 1).val = 5 ∨ (2 + 4 * b - 1).val = 9) := by
  revert b
  decide

theorem burnsideF4k_pb_orbit_eleven (b : ZMod 12) :
    ((11 + 4 * b).val = 11 ∨ (11 + 4 * b).val = 3 ∨ (11 + 4 * b).val = 7) ∧
      ((2 + 4 * b - 11).val = 11 ∨ (2 + 4 * b - 11).val = 3 ∨ (2 + 4 * b - 11).val = 7) := by
  revert b
  decide

theorem burnsideF4k_pb_fix_one_five (b : ZMod 12) :
    ((1 + 4 * b).val = 1 → (0 + 4 * b).val = 0) ∧
      ((2 + 4 * b - 1).val = 1 → (2 + 4 * b - 5).val ≠ 5) := by
  revert b
  decide

section Completion

variable {α : RankTwoAmalgam.{0}} {Z : Type} [Group Z] (c : α.Completion Z)

theorem burnsideF4k_pb_vtype (z : ℕ → c.Γ) (hz : ∀ i, c.graph.Adj (z i) (z (i + 1)))
    (hz0 : z 0 = c.xv) (n : ℕ) : CosetGeom.vtype (z n) = n.bodd := by
  induction n with
  | zero =>
    rw [hz0]
    exact CosetGeom.vtype_γ₀
  | succ n ih =>
    have h := CosetGeom.vtype_ne_of_adj (hz n)
    rw [ih] at h
    have hb : (n + 1).bodd = !n.bodd := Nat.bodd_succ n
    rw [hb]
    revert h
    cases CosetGeom.vtype (z (n + 1)) <;> cases Nat.bodd n <;> simp

theorem burnsideF4k_pb_inj (hU : UniqueGeod c.graph 6) (z : ℕ → c.Γ)
    (hz : ∀ i, c.graph.Adj (z i) (z (i + 1))) (hnb : ∀ i, z i ≠ z (i + 2))
    (hper : ∀ i, z (i + 2 * 6) = z i) (i j : ℕ) (hi : i < 12) (hj : j < 12) (h : z i = z j) :
    i = j := by
  have := (GPath.periodic_eq_iff (c := CosetGeom.vtype) (connected_graph c)
    (fun _ _ h => CosetGeom.vtype_ne_of_adj h) (by norm_num) hU z hz hnb hper i j).mp h
  rwa [Nat.mod_eq_of_lt (show i < 2 * 6 by omega), Nat.mod_eq_of_lt (show j < 2 * 6 by omega)]
    at this

theorem burnsideF4k_pb_mem_setStab (z : ℕ → c.Γ) (hper : ∀ i, z (i + 2 * 6) = z i) {w : c.G0}
    (hw : burnsideF4k_pb_DihAct z w) : w ∈ setStab c (Set.range z) := by
  obtain ⟨f, hf, hfs⟩ : ∃ f : ZMod 12 → ZMod 12, (∀ a, w • z a.val = z (f a).val) ∧
      Function.Surjective f := by
    obtain ⟨b, h | h⟩ := hw
    · exact ⟨fun a => a + 4 * b, h, fun a => ⟨a - 4 * b, sub_add_cancel a (4 * b)⟩⟩
    · exact ⟨fun a => 2 + 4 * b - a, h, fun a => ⟨2 + 4 * b - a, sub_sub_cancel _ a⟩⟩
  refine MulAction.mem_stabilizer_iff.mpr ?_
  ext u
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
    rw [← burnsideF4k_pb_mod z hper n, hf]
    exact ⟨_, rfl⟩
  · rintro ⟨n, rfl⟩
    obtain ⟨a', ha'⟩ := hfs (n : ZMod 12)
    exact ⟨z a'.val, ⟨_, rfl⟩, by rw [hf, ha', burnsideF4k_pb_mod z hper]⟩

end Completion

theorem burnsideF4k_polyG2d : burnsideF4k_PolyG2d := by
  intro α Z _ c hU z hz hnb hper hz0 hz1 sl sc hsl1 hsl2 hsc1 hsc2 hfree
  have h12 : (12 : ZMod 12) = 0 := rfl
  have hmod := burnsideF4k_pb_mod z hper
  have hvt := burnsideF4k_pb_vtype c z hz hz0
  have hinj := burnsideF4k_pb_inj c hU z hz hnb hper
  have hlv : c.lv = z 1 := hz1.symm
  have hval1 : (1 : ZMod 12).val = 1 := rfl
  have hval5 : (5 : ZMod 12).val = 5 := rfl
  have hval11 : (11 : ZMod 12).val = 11 := rfl
  have hsl' : ∀ a : ZMod 12, sl • z a.val = z (2 - a).val := by
    intro a
    rw [burnsideF4k_pb_refl z hz hper sl 1 hsl1 hsl2 a]
    congr 2
  have hsc' : ∀ a : ZMod 12, sc • z a.val = z (10 - a).val := by
    intro a
    rw [burnsideF4k_pb_refl z hz hper sc 11 hsc1 hsc2 a]
    congr 2
  have hW : ∀ w ∈ Subgroup.closure ({sl, sc} : Set c.G0), burnsideF4k_pb_DihAct z w := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨0, Or.inr fun a => by rw [hsl']; congr 2⟩
      · exact ⟨2, Or.inr fun a => by rw [hsc']; congr 2⟩
    | one => exact burnsideF4k_pb_dihAct_one z
    | mul x y _ _ hx hy => exact burnsideF4k_pb_dihAct_mul hx hy
    | inv x _ hx => exact burnsideF4k_pb_dihAct_inv hx
  have hslW : sl ∈ Subgroup.closure ({sl, sc} : Set c.G0) := Subgroup.subset_closure (by simp)
  have hscW : sc ∈ Subgroup.closure ({sl, sc} : Set c.G0) := Subgroup.subset_closure (by simp)
  have hρ : ∀ a : ZMod 12, (sl * sc) • z a.val = z (a + 4).val := by
    intro a
    rw [mul_smul, hsc', hsl']
    congr 2
    linear_combination -1 * h12
  have hρn : ∀ n : ℕ, ∀ a : ZMod 12, ((sl * sc) ^ n) • z a.val = z (a + 4 * n).val := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      rw [pow_succ, mul_smul, hρ, ih]
      congr 2
      push_cast
      ring
  have hrot : ∀ b : ZMod 12, ∃ w ∈ Subgroup.closure ({sl, sc} : Set c.G0),
      ∀ a : ZMod 12, w • z a.val = z (a + 4 * b).val := by
    intro b
    refine ⟨(sl * sc) ^ b.val, pow_mem (mul_mem hslW hscW) _, fun a => ?_⟩
    rw [hρn, ZMod.natCast_zmod_val]
  have hrefl : ∀ b : ZMod 12, ∃ w ∈ Subgroup.closure ({sl, sc} : Set c.G0),
      ∀ a : ZMod 12, w • z a.val = z (2 + 4 * b - a).val := by
    intro b
    refine ⟨(sl * sc) ^ b.val * sl, mul_mem (pow_mem (mul_mem hslW hscW) _) hslW, fun a => ?_⟩
    rw [mul_smul, hsl', hρn, ZMod.natCast_zmod_val]
    congr 2
    ring
  have hWle : Subgroup.closure ({sl, sc} : Set c.G0) ≤ setStab c (Set.range z) :=
    fun w hw => burnsideF4k_pb_mem_setStab c z hper (hW w hw)
  have hpt : ∀ t : ℕ, t.bodd = false →
      ∃ w ∈ Subgroup.closure ({sl, sc} : Set c.G0), w • z 0 = z t := by
    intro t ht
    have h2 : t % 2 = 0 := by
      have := Nat.mod_two_of_bodd t
      rw [ht] at this
      exact this
    obtain ⟨q, hq | hq⟩ : ∃ q, t = 4 * q ∨ t = 4 * q + 2 := ⟨t / 4, by omega⟩
    · obtain ⟨w, hw, hwa⟩ := hrot (q : ZMod 12)
      refine ⟨w, hw, ?_⟩
      have := hwa 0
      rw [ZMod.val_zero] at this
      rw [this, ← hmod t, hq]
      congr 2
      push_cast
      ring
    · obtain ⟨w, hw, hwa⟩ := hrefl (q : ZMod 12)
      refine ⟨w, hw, ?_⟩
      have := hwa 0
      rw [ZMod.val_zero] at this
      rw [this, ← hmod t, hq]
      congr 2
      push_cast
      ring
  have hle : setStab c (Set.range z) ≤ Subgroup.closure ({sl, sc} : Set c.G0) := by
    intro g hg
    obtain ⟨t, ht⟩ : g • z 0 ∈ Set.range z := burnsideF4k_setStab_mem c hg ⟨0, rfl⟩
    have htb : t.bodd = false := by
      have h1 := hvt t
      rw [ht, CosetGeom.vtype_smul, hvt 0, Nat.bodd_zero] at h1
      exact h1.symm
    obtain ⟨w, hw, hwt⟩ := hpt t htb
    have h1 : w⁻¹ * g ∈ setStab c (Set.range z) := mul_mem (inv_mem (hWle hw)) hg
    have h2 : (w⁻¹ * g) • z 0 = z 0 := by rw [mul_smul, ← ht, ← hwt, inv_smul_smul]
    have h3 := hfree _ h1 h2
    have hgw : g = w := by
      calc g = w * (w⁻¹ * g) := by group
        _ = w := by rw [h3, mul_one]
    rw [hgw]
    exact hw
  have hSW : setStab c (Set.range z) = Subgroup.closure ({sl, sc} : Set c.G0) :=
    le_antisymm hle hWle
  have hpt' : ∀ u ∈ Set.range z, CosetGeom.vtype u = false →
      ∃ w ∈ setStab c (Set.range z), w • z 0 = u := by
    rintro u ⟨t, rfl⟩ ht
    rw [hvt] at ht
    obtain ⟨w, hw, hwt⟩ := hpt t ht
    exact ⟨w, hWle hw, hwt⟩
  have hP : {u : c.Γ | u ∈ Set.range z ∧ CosetGeom.vtype u = false} =
      Set.range (fun k : Fin 6 => z (2 * k.val)) := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_range]
    constructor
    · rintro ⟨⟨t, rfl⟩, ht⟩
      rw [hvt] at ht
      have h2 : t % 2 = 0 := by
        have := Nat.mod_two_of_bodd t
        rw [ht] at this
        exact this
      refine ⟨⟨t % 12 / 2, by omega⟩, ?_⟩
      show z (2 * (t % 12 / 2)) = z t
      rw [show 2 * (t % 12 / 2) = t % 12 by omega]
      exact Function.Periodic.map_mod_nat (fun x => hper x) t
    · rintro ⟨k, rfl⟩
      refine ⟨⟨_, rfl⟩, ?_⟩
      rw [hvt, Nat.bodd_mul, Nat.bodd_two, Bool.false_and]
  have hPcard : Set.ncard {u : c.Γ | u ∈ Set.range z ∧ CosetGeom.vtype u = false} = 6 := by
    rw [hP, Set.ncard_range_of_injective, Nat.card_fin]
    intro i j hij
    have := hinj _ _ (by have := i.isLt; omega) (by have := j.isLt; omega) hij
    exact Fin.ext (by omega)
  have hreg : ∀ u ∈ Set.range z, CosetGeom.vtype u = false → ∀ v ∈ Set.range z,
      CosetGeom.vtype v = false → ∃! w : ↥(setStab c (Set.range z)), (w : c.G0) • u = v := by
    intro u hu hut v hv hvt'
    obtain ⟨w₁, hw₁, rfl⟩ := hpt' u hu hut
    obtain ⟨w₂, hw₂, rfl⟩ := hpt' v hv hvt'
    refine ⟨⟨w₂ * w₁⁻¹, mul_mem hw₂ (inv_mem hw₁)⟩, ?_, ?_⟩
    · show (w₂ * w₁⁻¹) • w₁ • z 0 = w₂ • z 0
      rw [mul_smul, inv_smul_smul]
    · rintro ⟨w, hw⟩ hwe
      have hwe' : w • w₁ • z 0 = w₂ • z 0 := hwe
      apply Subtype.ext
      show w = w₂ * w₁⁻¹
      have h1 : w₂⁻¹ * w * w₁ ∈ setStab c (Set.range z) :=
        mul_mem (mul_mem (inv_mem hw₂) hw) hw₁
      have h2 : (w₂⁻¹ * w * w₁) • z 0 = z 0 := by
        rw [mul_smul, mul_smul, hwe', inv_smul_smul]
      have h3 := hfree _ h1 h2
      calc w = w₂ * (w₂⁻¹ * w * w₁) * w₁⁻¹ := by group
        _ = w₂ * w₁⁻¹ := by rw [h3, mul_one]
  have hOl : {u : c.Γ | ∃ w ∈ setStab c (Set.range z), w • c.lv = u} = {z 1, z 5, z 9} := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hSW] at hw
      rw [hlv]
      obtain ⟨b, h | h⟩ := hW w hw
      · have e := h 1
        rw [hval1] at e
        rw [e]
        rcases (burnsideF4k_pb_orbit_one b).1 with h' | h' | h' <;> rw [h'] <;> simp
      · have e := h 1
        rw [hval1] at e
        rw [e]
        rcases (burnsideF4k_pb_orbit_one b).2 with h' | h' | h' <;> rw [h'] <;> simp
    · rintro (rfl | rfl | rfl)
      · exact ⟨1, one_mem _, by rw [one_smul, hlv]⟩
      · obtain ⟨w, hw, hwa⟩ := hrot 1
        refine ⟨w, hWle hw, ?_⟩
        rw [hlv, ← hval1, hwa]
        rfl
      · obtain ⟨w, hw, hwa⟩ := hrot 2
        refine ⟨w, hWle hw, ?_⟩
        rw [hlv, ← hval1, hwa]
        rfl
  have hOc : {u : c.Γ | ∃ w ∈ setStab c (Set.range z), w • z 11 = u} = {z 11, z 3, z 7} := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hSW] at hw
      obtain ⟨b, h | h⟩ := hW w hw
      · have e := h 11
        rw [hval11] at e
        rw [e]
        rcases (burnsideF4k_pb_orbit_eleven b).1 with h' | h' | h' <;> rw [h'] <;> simp
      · have e := h 11
        rw [hval11] at e
        rw [e]
        rcases (burnsideF4k_pb_orbit_eleven b).2 with h' | h' | h' <;> rw [h'] <;> simp
    · rintro (rfl | rfl | rfl)
      · exact ⟨1, one_mem _, one_smul _ _⟩
      · obtain ⟨w, hw, hwa⟩ := hrot 1
        refine ⟨w, hWle hw, ?_⟩
        rw [← hval11, hwa]
        rfl
      · obtain ⟨w, hw, hwa⟩ := hrot 2
        refine ⟨w, hWle hw, ?_⟩
        rw [← hval11, hwa]
        rfl
  have hne : ∀ i j : ℕ, i < 12 → j < 12 → i ≠ j → z i ≠ z j := fun i j hi hj hij h =>
    hij (hinj i j hi hj h)
  have hOlcard : Set.ncard {u : c.Γ | ∃ w ∈ setStab c (Set.range z), w • c.lv = u} = 3 := by
    rw [hOl]
    exact Set.ncard_eq_three.mpr ⟨z 1, z 5, z 9, hne 1 5 (by norm_num) (by norm_num) (by norm_num),
      hne 1 9 (by norm_num) (by norm_num) (by norm_num),
      hne 5 9 (by norm_num) (by norm_num) (by norm_num), rfl⟩
  have hOccard : Set.ncard {u : c.Γ | ∃ w ∈ setStab c (Set.range z), w • z 11 = u} = 3 := by
    rw [hOc]
    exact Set.ncard_eq_three.mpr ⟨z 11, z 3, z 7,
      hne 11 3 (by norm_num) (by norm_num) (by norm_num),
      hne 11 7 (by norm_num) (by norm_num) (by norm_num),
      hne 3 7 (by norm_num) (by norm_num) (by norm_num), rfl⟩
  have hlines : {u : c.Γ | u ∈ Set.range z ∧ CosetGeom.vtype u = true} =
      {u | ∃ w ∈ setStab c (Set.range z), w • c.lv = u} ∪
        {u | ∃ w ∈ setStab c (Set.range z), w • z 11 = u} := by
    rw [hOl, hOc]
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨t, rfl⟩, ht⟩
      rw [hvt] at ht
      have h2 : t % 2 = 1 := by
        have := Nat.mod_two_of_bodd t
        rw [ht] at this
        exact this
      rw [← Function.Periodic.map_mod_nat (fun x => hper x) t]
      have : t % (2 * 6) = 1 ∨ t % (2 * 6) = 5 ∨ t % (2 * 6) = 9 ∨ t % (2 * 6) = 11 ∨
          t % (2 * 6) = 3 ∨ t % (2 * 6) = 7 := by omega
      rcases this with h | h | h | h | h | h <;> rw [h] <;> simp
    · rintro ((rfl | rfl | rfl) | (rfl | rfl | rfl)) <;>
        exact ⟨⟨_, rfl⟩, by rw [hvt]; rfl⟩
  have hdisj : Disjoint {u : c.Γ | ∃ w ∈ setStab c (Set.range z), w • c.lv = u}
      {u | ∃ w ∈ setStab c (Set.range z), w • z 11 = u} := by
    rw [hOl, hOc, Set.disjoint_left]
    rintro u (rfl | rfl | rfl) (h | h | h) <;>
      exact absurd (hinj _ _ (by norm_num) (by norm_num) h) (by norm_num)
  have hiso : Nonempty (↥(setStab c (Set.range z)) ≃* Equiv.Perm (Fin 3)) := by
    let K := setStab c (Set.range z)
    let T : Set c.Γ := {u | ∃ w ∈ K, w • c.lv = u}
    letI : MulAction ↥K ↥T :=
      { smul := fun g u => ⟨(g : c.G0) • (u : c.Γ), by
          obtain ⟨w, hw, hwu⟩ := u.2
          exact ⟨g * w, mul_mem g.2 hw, by rw [mul_smul, hwu]⟩⟩
        one_smul := fun u => Subtype.ext (one_smul c.G0 (u : c.Γ))
        mul_smul := fun g h u => Subtype.ext (mul_smul (g : c.G0) (h : c.G0) (u : c.Γ)) }
    have hT : T = {z 1, z 5, z 9} := hOl
    have hTcard : Nat.card ↥T = 3 := by
      rw [Nat.card_coe_set_eq]
      exact hOlcard
    have h1T : z 1 ∈ T := by rw [hT]; simp
    have h5T : z 5 ∈ T := by rw [hT]; simp
    let eT : ↥T ≃ Fin 3 :=
      (Nat.equivFinOfCardPos (by rw [hTcard]; norm_num)).trans (finCongr hTcard)
    let χ : ↥K →* Equiv.Perm (Fin 3) :=
      (Equiv.permCongrHom eT).toMonoidHom.comp (MulAction.toPermHom ↥K ↥T)
    have hχ : Function.Injective χ := by
      rw [injective_iff_map_eq_one]
      intro g hg
      have hg' : MulAction.toPermHom ↥K ↥T g = 1 := by
        apply (Equiv.permCongrHom eT).injective
        rw [map_one]
        exact hg
      have hfix : ∀ u (hu : u ∈ T), (g : c.G0) • u = u := by
        intro u hu
        have := congrArg Subtype.val (DFunLike.congr_fun hg' ⟨u, hu⟩)
        exact this
      have e1 := hfix _ h1T
      have e5 := hfix _ h5T
      have hgW : (g : c.G0) ∈ Subgroup.closure ({sl, sc} : Set c.G0) := hle g.2
      apply Subtype.ext
      show (g : c.G0) = 1
      obtain ⟨b, h | h⟩ := hW _ hgW
      · have h1' := h 1
        rw [hval1, e1] at h1'
        have hb := hinj _ _ (by norm_num) (ZMod.val_lt _) h1'
        have h0 := (burnsideF4k_pb_fix_one_five b).1 hb.symm
        apply hfree _ g.2
        have := h 0
        rw [ZMod.val_zero, h0] at this
        exact this
      · have h1' := h 1
        rw [hval1, e1] at h1'
        have h5' := h 5
        rw [hval5, e5] at h5'
        have hb1 := hinj _ _ (by norm_num) (ZMod.val_lt _) h1'
        have hb5 := hinj _ _ (by norm_num) (ZMod.val_lt _) h5'
        exact absurd hb5.symm ((burnsideF4k_pb_fix_one_five b).2 hb1.symm)
    have hKcard : Nat.card ↥K = 6 := by
      let f : ↥K → ↥{u : c.Γ | u ∈ Set.range z ∧ CosetGeom.vtype u = false} := fun g =>
        ⟨(g : c.G0) • z 0, burnsideF4k_setStab_mem c g.2 ⟨0, rfl⟩, by
          rw [CosetGeom.vtype_smul, hvt, Nat.bodd_zero]⟩
      have hf : Function.Bijective f := by
        constructor
        · intro g h hgh
          have e : (g : c.G0) • z 0 = (h : c.G0) • z 0 := congrArg Subtype.val hgh
          have h1 : (h : c.G0)⁻¹ * g ∈ K := mul_mem (inv_mem h.2) g.2
          have h2 : ((h : c.G0)⁻¹ * g) • z 0 = z 0 := by rw [mul_smul, e, inv_smul_smul]
          have h3 := hfree _ h1 h2
          apply Subtype.ext
          calc (g : c.G0) = h * ((h : c.G0)⁻¹ * g) := by group
            _ = h := by rw [h3, mul_one]
        · rintro ⟨u, hu, hut⟩
          obtain ⟨w, hw, rfl⟩ := hpt' u hu hut
          exact ⟨⟨w, hw⟩, rfl⟩
      rw [Nat.card_eq_of_bijective f hf, Nat.card_coe_set_eq, hPcard]
    have hbij : Function.Bijective χ := by
      rw [Nat.bijective_iff_injective_and_card]
      refine ⟨hχ, ?_⟩
      rw [hKcard, Nat.card_perm, Nat.card_fin]
      rfl
    exact ⟨MulEquiv.ofBijective χ hbij⟩
  exact ⟨hSW, hiso, hPcard, hreg, hlines, hdisj, hOlcard, hOccard⟩

end CFSG.ASVolI
