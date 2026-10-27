module

public import CFSG.RankThree.S4Free.Stellmacher25
public import CFSG.RankThree.S4Free.StellmacherW
public import CFSG.Quasithin.EmptyFaithful.S1421QA5Fix
import CFSG.GroupTheory.SubgroupCardMul

public section

namespace CFSG.RankThree.S4Free

theorem IsSym3Free.forall_inv_eq_one {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsSym3Free H) :
    ∀ a ∈ H, ∀ y ∈ H, a ^ 2 = 1 → y ^ 3 = 1 → a * y * a⁻¹ = y⁻¹ → y = 1 := by
  intro a ha y hy ha2 hy3 hay
  have h := hH.eq_one_of_inv (a := ⟨a, ha⟩) (y := ⟨y, hy⟩) (Subtype.ext (by simpa using ha2))
    (Subtype.ext (by simpa using hy3)) (Subtype.ext (by simpa using hay))
  exact congrArg Subtype.val h

end CFSG.RankThree.S4Free

namespace CFSG.RankThree.S4Free.Stell

open CFSG.Quasithin Subgroup

universe u

variable {V : Type*} [CommGroup V]

section FixedMod

private theorem comm_comm_eq (hV : ∀ v : V, v ^ 2 = 1) (t : MulAut V) (w : V) :
    t (t w * w⁻¹) * (t w * w⁻¹)⁻¹ = (t ^ 2) w * w⁻¹ := by
  have hinv : ∀ v : V, v⁻¹ = v := fun v => inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hV v)
  simp only [hinv, map_mul, pow_two, MulAut.mul_apply]
  have h1 : t w * t w = 1 := by rw [← pow_two]; exact hV _
  calc t (t w) * t w * (t w * w) = t (t w) * (t w * t w) * w := by
        simp only [mul_assoc]
    _ = t (t w) * w := by rw [h1, mul_one]

private theorem iterate_two_pow (hV : ∀ v : V, v ^ 2 = 1) (t : MulAut V) (j : ℕ) :
    (fun w => t w * w⁻¹)^[2 ^ j] = fun w => (t ^ 2 ^ j) w * w⁻¹ := by
  induction j generalizing t with
  | zero => funext w; simp
  | succ j ih =>
    have h2 : (fun w => t w * w⁻¹)^[2] = fun w => (t ^ 2) w * w⁻¹ := by
      funext w
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply]
      exact comm_comm_eq hV t w
    rw [pow_succ', Function.iterate_mul, h2, ih (t ^ 2), ← pow_mul, ← pow_succ']

theorem exists_comm_mem_of_pow_two_pow (hV : ∀ v : V, v ^ 2 = 1) {t : MulAut V} {k : ℕ}
    (ht : t ^ 2 ^ k = 1) {F C : Subgroup V} (hF : ∀ w ∈ F, t w ∈ F) (hlt : ¬ F ≤ C) :
    ∃ u ∈ F, u ∉ C ∧ t u * u⁻¹ ∈ C := by
  classical
  obtain ⟨u, huF, huC⟩ := Set.not_subset.1 hlt
  set φ : V → V := fun w => t w * w⁻¹ with hφ
  have hφF : ∀ w ∈ F, φ w ∈ F := fun w hw => F.mul_mem (hF w hw) (F.inv_mem hw)
  have hiter : ∀ n : ℕ, φ^[n] u ∈ F := by
    intro n
    induction n with
    | zero => exact huF
    | succ n ih => rw [Function.iterate_succ_apply']; exact hφF _ ih
  have hex : ∃ n : ℕ, φ^[n] u ∈ C :=
    ⟨2 ^ k, by rw [hφ, iterate_two_pow hV t k, ht]; simp [C.one_mem]⟩
  have hn0 : Nat.find hex ≠ 0 := by
    intro h
    have := Nat.find_spec hex
    rw [h, Function.iterate_zero, id] at this
    exact huC this
  refine ⟨φ^[Nat.find hex - 1] u, hiter _, Nat.find_min hex (by omega), ?_⟩
  have := Nat.find_spec hex
  rwa [show Nat.find hex = (Nat.find hex - 1) + 1 by omega, Function.iterate_succ_apply'] at this

theorem forall_mem_of_pow_two_pow (hV : ∀ v : V, v ^ 2 = 1) {g : MulAut V} {U C : Subgroup V}
    (hgU : g ∈ stabSub U) (hCU : C ≤ U) (hgC : ∀ c ∈ C, g c = c)
    (hfpf : ∀ w ∈ U, g w * w⁻¹ ∈ C → w ∈ C) {k m : ℕ} (hm : Odd m)
    (hord : orderOf g = 2 ^ k * m) : ∀ w ∈ U, (g ^ 2 ^ k) w * w⁻¹ ∈ C → w ∈ C := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using hfpf
  set y := g ^ 2 ^ k with hy
  have hyC : ∀ c ∈ C, y c = c := by
    intro c hc
    have : ∀ n : ℕ, (g ^ n) c = c := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, MulAut.mul_apply, hgC c hc, ih]
    exact this _
  let F : Subgroup V :=
    { carrier := {w | w ∈ U ∧ y w * w⁻¹ ∈ C}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨U.mul_mem ha hb, ?_⟩
        have : y (a * b) * (a * b)⁻¹ = (y a * a⁻¹) * (y b * b⁻¹) := by
          rw [map_mul, mul_inv_rev]; ac_rfl
        rw [this]; exact C.mul_mem ha' hb'
      one_mem' := ⟨U.one_mem, by simp [C.one_mem]⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨U.inv_mem ha, ?_⟩
        have : y a⁻¹ * a⁻¹⁻¹ = (y a * a⁻¹)⁻¹ := by
          rw [map_inv, inv_inv, mul_inv_rev, inv_inv, mul_comm]
        rw [this]; exact C.inv_mem ha' }
  have hgF : ∀ w ∈ F, g w ∈ F := by
    rintro w ⟨hw, hw'⟩
    refine ⟨(hgU w).2 hw, ?_⟩
    have hcomm : y (g w) = g (y w) := by
      rw [hy, ← MulAut.mul_apply, ← MulAut.mul_apply, ← pow_succ, ← pow_succ']
    have : y (g w) * (g w)⁻¹ = g (y w * w⁻¹) := by rw [hcomm, map_mul, map_inv]
    rw [this, hgC _ hw']
    exact hw'
  have hcop : Nat.Coprime m (2 ^ k) := Nat.Coprime.pow_right _ hm.coprime_two_right
  obtain ⟨m', -, hm'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop
    (Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.mp hk))
  set c := m * m' / 2 ^ k with hc
  have hmm' : m * m' = 2 ^ k * c + 1 := by
    rw [hc]; have := Nat.div_add_mod (m * m') (2 ^ k); omega
  set t := g ^ (m * m') with ht
  have ht2 : t ^ 2 ^ k = 1 := by
    rw [ht, ← pow_mul, mul_comm, ← mul_assoc, pow_mul, ← hord, pow_orderOf_eq_one, one_pow]
  have htF : ∀ w ∈ F, t w ∈ F := by
    intro w hw
    have : ∀ n : ℕ, (g ^ n) w ∈ F := by
      intro n
      induction n with
      | zero => exact hw
      | succ n ih => rw [pow_succ', MulAut.mul_apply]; exact hgF _ ih
    exact this _
  have hyc : ∀ w ∈ F, ∀ n : ℕ, (y ^ n) w * w⁻¹ ∈ C := by
    rintro w ⟨hw, hw'⟩ n
    induction n with
    | zero => simp [C.one_mem]
    | succ n ih =>
      have : (y ^ (n + 1)) w * w⁻¹ = y ((y ^ n) w * w⁻¹) * (y w * w⁻¹) := by
        rw [pow_succ', MulAut.mul_apply, map_mul, map_inv]; group
      rw [this, hyC _ ih]
      exact C.mul_mem ih hw'
  have htg : ∀ w ∈ F, t w * w⁻¹ ∈ C → g w * w⁻¹ ∈ C := by
    intro w hw htw
    have h1 : t = g * y ^ c := by
      rw [ht, hmm', pow_succ, pow_mul, hy]
      exact (((Commute.refl g).pow_left _).pow_left _).eq
    have h2 : t w = g ((y ^ c) w) := by rw [h1, MulAut.mul_apply]
    have h3 : g ((y ^ c) w) * w⁻¹ = g ((y ^ c) w * w⁻¹) * (g w * w⁻¹) := by
      rw [map_mul, map_inv]; group
    rw [h2, h3, hgC _ (hyc w hw c)] at htw
    have := C.mul_mem (C.inv_mem (hyc w hw c)) htw
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
  intro w hw hyw
  by_contra hwC
  obtain ⟨u, huF, huC, hu⟩ := exists_comm_mem_of_pow_two_pow hV ht2 htF (C := C)
    (fun h => hwC (h ⟨hw, hyw⟩))
  exact huC (hfpf u huF.1 (htg u huF hu))

end FixedMod

section Restrict

variable [Finite V]

theorem mem_autSub_of_mem {X : Subgroup (MulAut V)} {U : Subgroup V} {g : MulAut V}
    (hg : g ∈ X) (hgU : g ∈ stabSub U) : resHom U ⟨g, hgU⟩ ∈ autSub X U :=
  mem_autSub.mpr ⟨⟨g, hgU⟩, hg, rfl⟩

theorem codimOn_autSub {B : Subgroup (MulAut V)} {U W : Subgroup V} (hB : B ≤ stabSub U)
    (hWU : W ≤ U) : codimOn (autSub B U) (W.subgroupOf U) = codimOn B W := by
  unfold codimOn mRel
  congr 1
  rw [← Subgroup.relIndex_map_map_of_injective _ _ U.subtype_injective,
    map_subtype_fixV_autSub hB, Subgroup.map_subgroupOf_eq_of_le hWU,
    ← Subgroup.inf_relIndex_right, ← Subgroup.inf_relIndex_right (H := fixV B)]
  congr 1
  rw [inf_comm U, inf_assoc, inf_eq_right.mpr hWU]

theorem autSub_inf_centSub {B : Subgroup (MulAut V)} {U W : Subgroup V} (hWU : W ≤ U) :
    autSub (B ⊓ centSub W) U = centSub (W.subgroupOf U) ⊓ autSub B U := by
  ext φ
  rw [Subgroup.mem_inf, mem_autSub, mem_autSub, mem_centSub]
  constructor
  · rintro ⟨g, ⟨hgB, hgW⟩, rfl⟩
    refine ⟨fun w hw => Subtype.ext ?_, g, hgB, rfl⟩
    rw [resHom_apply]
    exact hgW _ (by simpa [Subgroup.mem_subgroupOf] using hw)
  · rintro ⟨hφ, g, hgB, rfl⟩
    refine ⟨g, ⟨hgB, fun w hw => ?_⟩, rfl⟩
    have := hφ ⟨w, hWU hw⟩ (by simpa [Subgroup.mem_subgroupOf] using hw)
    simpa [resHom_apply] using congrArg Subtype.val this

theorem dimOn_autSub {B : Subgroup (MulAut V)} {U W : Subgroup V} (hB : B ≤ stabSub U)
    (hWU : W ≤ U) : dimOn (autSub B U) (W.subgroupOf U) = dimOn B W := by
  unfold dimOn mRel
  congr 1
  have h1 := Subgroup.relIndex_mul_card (centSub (W.subgroupOf U)) (autSub B U)
  have h2 := Subgroup.relIndex_mul_card (centSub W) B
  have h3 := card_autSub_mul hB
  have h4 := card_autSub_mul (A := B ⊓ centSub W) (U := U) (inf_le_left.trans hB)
  have hcU : centSub U ≤ centSub W := fun g hg w hw => hg w (hWU hw)
  rw [autSub_inf_centSub hWU, inf_assoc, inf_eq_right.mpr hcU] at h4
  rw [inf_comm (centSub W) B] at h2
  have hpos : 0 < Nat.card ↥(centSub (W.subgroupOf U) ⊓ autSub B U) *
      Nat.card ↥(B ⊓ centSub U) := Nat.mul_pos Nat.card_pos Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc (centSub (W.subgroupOf U)).relIndex (autSub B U) *
        (Nat.card ↥(centSub (W.subgroupOf U) ⊓ autSub B U) * Nat.card ↥(B ⊓ centSub U))
      = Nat.card (autSub B U) * Nat.card ↥(B ⊓ centSub U) := by rw [← mul_assoc, h1]
    _ = Nat.card B := h3
    _ = (centSub W).relIndex B * Nat.card ↥(B ⊓ centSub W) := h2.symm
    _ = (centSub W).relIndex B *
        (Nat.card ↥(centSub (W.subgroupOf U) ⊓ autSub B U) * Nat.card ↥(B ⊓ centSub U)) := by
      rw [h4]

theorem subgroupOf_le_fixV_autSub_iff {B : Subgroup (MulAut V)} {U W : Subgroup V}
    (hB : B ≤ stabSub U) (hWU : W ≤ U) : W.subgroupOf U ≤ fixV (autSub B U) ↔ W ≤ fixV B := by
  constructor
  · intro h w hw g hg
    have := (mem_fixV_autSub.mp (h (show (⟨w, hWU hw⟩ : U) ∈ W.subgroupOf U from hw))) g hg (hB hg)
    exact this
  · intro h w hw
    exact mem_fixV_autSub.mpr fun g hg _ => h hw g hg

theorem elemAbOn_autSub_iff {B : Subgroup (MulAut V)} {U W : Subgroup V} (hB : B ≤ stabSub U)
    (hWU : W ≤ U) : ElemAbOn (autSub B U) (W.subgroupOf U) ↔ ElemAbOn B W := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun a ha b hb w hw => ?_, fun a ha w hw => ?_⟩
    · have := h1 _ (mem_autSub_of_mem ha (hB ha)) _ (mem_autSub_of_mem hb (hB hb))
        ⟨w, hWU hw⟩ (by simpa [Subgroup.mem_subgroupOf] using hw)
      simpa [resHom_apply] using congrArg Subtype.val this
    · have := h2 _ (mem_autSub_of_mem ha (hB ha)) ⟨w, hWU hw⟩
        (by simpa [Subgroup.mem_subgroupOf] using hw)
      simpa [resHom_apply] using congrArg Subtype.val this
  · rintro ⟨h1, h2⟩
    refine ⟨fun φ hφ ψ hψ w hw => ?_, fun φ hφ w hw => ?_⟩
    · obtain ⟨a, ha, rfl⟩ := mem_autSub.mp hφ
      obtain ⟨b, hb, rfl⟩ := mem_autSub.mp hψ
      exact Subtype.ext (by simpa [resHom_apply] using h1 a ha b hb w hw)
    · obtain ⟨a, ha, rfl⟩ := mem_autSub.mp hφ
      exact Subtype.ext (by simpa [resHom_apply] using h2 a ha w hw)

theorem exists_le_autSub_eq {T : Subgroup (MulAut V)} {U : Subgroup V} (hT : T ≤ stabSub U)
    {B' : Subgroup (MulAut U)} (hB' : B' ≤ autSub T U) :
    ∃ B : Subgroup (MulAut V), B ≤ T ∧ autSub B U = B' := by
  refine ⟨T ⊓ (B'.comap (resHom U)).map (stabSub U).subtype, inf_le_left, ?_⟩
  ext φ
  rw [mem_autSub]
  constructor
  · rintro ⟨g, ⟨-, g', hg', hgg'⟩, rfl⟩
    have : g' = g := Subtype.ext hgg'
    subst this
    exact hg'
  · intro hφ
    obtain ⟨g, hgT, rfl⟩ := mem_autSub.mp (hB' hφ)
    exact ⟨g, ⟨hgT, g, hφ, rfl⟩, rfl⟩

theorem ale_autSub_iff {T : Subgroup (MulAut V)} {U W : Subgroup V} (hT : T ≤ stabSub U)
    (hWU : W ≤ U) {e : ℚ} : ALe (autSub T U) (W.subgroupOf U) e ↔ ALe T W e := by
  constructor
  · rintro ⟨B', ⟨hB'T, hB'W, hB'el⟩, hle⟩
    obtain ⟨B, hBT, rfl⟩ := exists_le_autSub_eq hT hB'T
    have hB : B ≤ stabSub U := hBT.trans hT
    refine ⟨B, ⟨hBT, fun h => hB'W ((subgroupOf_le_fixV_autSub_iff hB hWU).mpr h),
      (elemAbOn_autSub_iff hB hWU).mp hB'el⟩, ?_⟩
    rwa [codimOn_autSub hB hWU, dimOn_autSub hB hWU] at hle
  · rintro ⟨B, ⟨hBT, hBW, hBel⟩, hle⟩
    have hB : B ≤ stabSub U := hBT.trans hT
    refine ⟨autSub B U, ⟨autSub_mono hBT U,
      fun h => hBW ((subgroupOf_le_fixV_autSub_iff hB hWU).mp h),
      (elemAbOn_autSub_iff hB hWU).mpr hBel⟩, ?_⟩
    rwa [codimOn_autSub hB hWU, dimOn_autSub hB hWU]

theorem agt_autSub_iff {T : Subgroup (MulAut V)} {U W : Subgroup V} (hT : T ≤ stabSub U)
    (hWU : W ≤ U) {e : ℚ} : AGt (autSub T U) (W.subgroupOf U) e ↔ AGt T W e := by
  rw [← not_ale_iff, ← not_ale_iff, ale_autSub_iff hT hWU]

end Restrict

section Counting

theorem card_le_card_fixSub_sq {P : Type*} [Group P] [Finite P] (hc : ∀ p q : P, p * q = q * p)
    (h2 : ∀ p : P, p * p = 1) (α : MulAut P) (hα : ∀ p, α (α p) = p) :
    Nat.card P ≤ Nat.card (AutQ8D8.fixSub α) ^ 2 := by
  have hinv : ∀ p : P, p⁻¹ = p := fun p => inv_eq_of_mul_eq_one_right (h2 p)
  let ψ : P →* P :=
    { toFun := fun p => p⁻¹ * α p
      map_one' := by simp
      map_mul' := fun p q => by
        simp only [map_mul, mul_inv_rev]
        calc q⁻¹ * p⁻¹ * (α p * α q) = p⁻¹ * (q⁻¹ * α p) * α q := by
              rw [hc q⁻¹ p⁻¹]; group
          _ = p⁻¹ * (α p * q⁻¹) * α q := by rw [hc q⁻¹ (α p)]
          _ = p⁻¹ * α p * (q⁻¹ * α q) := by group }
  have hker : ψ.ker = AutQ8D8.fixSub α := by
    ext p
    rw [MonoidHom.mem_ker, AutQ8D8.mem_fixSub]
    change p⁻¹ * α p = 1 ↔ α p = p
    rw [inv_mul_eq_one, eq_comm]
  have hrange : ψ.range ≤ AutQ8D8.fixSub α := by
    rintro _ ⟨p, rfl⟩
    rw [AutQ8D8.mem_fixSub]
    change α (p⁻¹ * α p) = p⁻¹ * α p
    rw [map_mul, map_inv, hα, hinv, hinv, hc]
  have h := Subgroup.card_ker_mul_card_range ψ
  rw [hker] at h
  rw [← h, sq]
  exact Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hrange)

theorem relIndex_le_two_of_forall {G : Type*} [Group G] {A A₀ : Subgroup G} {a : G}
    (ha : a ∈ A) (h : ∀ b ∈ A, b ∈ A₀ ∨ a⁻¹ * b ∈ A₀) : A₀.relIndex A ≤ 2 := by
  classical
  rw [Subgroup.relIndex, Subgroup.index]
  have hsurj : Function.Surjective (fun i : Bool =>
      (QuotientGroup.mk (if i then (⟨a, ha⟩ : ↥A) else 1) : ↥A ⧸ A₀.subgroupOf A)) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H b =>
      rcases h b b.2 with hb | hb
      · refine ⟨false, ?_⟩
        simp only [Bool.false_eq_true, if_false]
        rw [QuotientGroup.eq]
        simpa [Subgroup.mem_subgroupOf] using hb
      · refine ⟨true, ?_⟩
        simp only [if_true]
        rw [QuotientGroup.eq]
        simpa [Subgroup.mem_subgroupOf] using hb
  calc Nat.card (↥A ⧸ A₀.subgroupOf A) ≤ Nat.card Bool := Nat.card_le_card_of_surjective _ hsurj
    _ = 2 := by simp

variable [Finite V]

theorem dimOn_le_dimOn_add_one {A A₀ : Subgroup (MulAut V)} (hA : IsPGroup 2 A) (hA₀ : A₀ ≤ A)
    (hidx : A₀.relIndex A ≤ 2) (U : Subgroup V) : dimOn A U ≤ dimOn A₀ U + 1 := by
  have h1 := Subgroup.relIndex_mul_relIndex (centSub U ⊓ A₀) A₀ A inf_le_right hA₀
  rw [Subgroup.inf_relIndex_right] at h1
  have h2 : (centSub U).relIndex A ≤ (centSub U ⊓ A₀).relIndex A :=
    Subgroup.relIndex_le_of_le_left inf_le_left (relIndex_ne_zero_of_finite _ _)
  have h3 : (centSub U).relIndex A ≤ 2 ^ (dimOn A₀ U + 1) := by
    rw [pow_succ]
    calc (centSub U).relIndex A ≤ (centSub U ⊓ A₀).relIndex A := h2
      _ = (centSub U).relIndex A₀ * A₀.relIndex A := h1.symm
      _ ≤ 2 ^ dimOn A₀ U * 2 := by
        rw [relIndex_eq_two_pow (hA.to_le hA₀)]
        exact Nat.mul_le_mul_left _ hidx
  rw [relIndex_eq_two_pow hA] at h3
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h3

theorem card_autSub_eq_two_pow {X : Subgroup (MulAut V)} {U : Subgroup V} (hX : X ≤ stabSub U)
    (h2 : IsPGroup 2 X) : Nat.card (autSub X U) = 2 ^ dimOn X U := by
  have h1 := card_autSub_mul hX
  have h3 := Subgroup.relIndex_mul_card (centSub U) X
  rw [inf_comm] at h3
  rw [relIndex_eq_two_pow h2] at h3
  have hpos : 0 < Nat.card ↥(X ⊓ centSub U) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h3.symm)

end Counting

section Dihedral

private theorem zmod_eq_zero_of_two_mul {n : ℕ} (hn : Odd n) {x : ZMod n} (hx : 2 * x = 0) :
    x = 0 := by
  have hcop : Nat.Coprime 2 n := Nat.coprime_two_left.mpr hn
  set u : (ZMod n)ˣ := ZMod.unitOfCoprime 2 hcop with hu_def
  have hu : (u : ZMod n) = 2 := by
    rw [hu_def, ZMod.coe_unitOfCoprime]
    norm_num
  calc x = ((u⁻¹ : (ZMod n)ˣ) : ZMod n) * ((u : ZMod n) * x) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = 0 := by rw [hu, hx, mul_zero]

theorem dihedral_pow_eq_one_of_odd {n : ℕ} {d : DihedralGroup n} (hd : Odd (orderOf d)) :
    d ^ n = 1 := by
  rcases d with i | i
  · rw [DihedralGroup.r_pow, ZMod.natCast_self, mul_zero, DihedralGroup.r_zero]
  · rw [DihedralGroup.orderOf_sr] at hd
    exact absurd hd (Nat.not_odd_iff_even.mpr even_two)

theorem dihedral_eq_of_commute {n : ℕ} (hn : Odd n) {d e : DihedralGroup n} (hd1 : d ≠ 1)
    (hd2 : d ^ 2 = 1) (he1 : e ≠ 1) (he2 : e ^ 2 = 1) (hde : d * e = e * d) : d = e := by
  have hrot : ∀ i : ZMod n, (DihedralGroup.r i) ^ 2 = 1 → DihedralGroup.r i = 1 := by
    intro i hi
    rw [DihedralGroup.r_pow, ← DihedralGroup.r_zero] at hi
    have h0 := DihedralGroup.r.inj hi
    push_cast at h0
    have h2 : 2 * i = 0 := by linear_combination h0
    rw [zmod_eq_zero_of_two_mul hn h2, DihedralGroup.r_zero]
  rcases d with i | i
  · exact absurd (hrot i hd2) hd1
  rcases e with j | j
  · exact absurd (hrot j he2) he1
  rw [DihedralGroup.sr_mul_sr, DihedralGroup.sr_mul_sr] at hde
  have h := DihedralGroup.r.inj hde
  have h2 : 2 * (j - i) = 0 := by linear_combination h
  have := zmod_eq_zero_of_two_mul hn h2
  rw [sub_eq_zero] at this
  rw [this]

end Dihedral

section L24Facts

variable [Finite V] {S M A L : Subgroup (MulAut V)}

theorem IsL24.oTwo_le_inf (hL : IsL24 S M A L) (hS : IsPGroup 2 S) :
    (oTwo ↥L).map L.subtype ≤ S ⊓ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (S.subgroupOf L) := hS.comap_subtype
  have hle : oTwo ↥L ≤ S.subgroupOf L := by
    have h1 := (oTwo_isPGroup ↥L).le_sylow_of_normal
      (hP.toSylow (show ¬ 2 ∣ (S.subgroupOf L).index from hL.not_dvd_relIndex))
    rwa [IsPGroup.toSylow_coe] at h1
  calc (oTwo ↥L).map L.subtype ≤ (S.subgroupOf L).map L.subtype := Subgroup.map_mono hle
    _ = S ⊓ L := Subgroup.subgroupOf_map_subtype S L

theorem conj_mem_map_oTwo {l o : MulAut V} (hl : l ∈ L) (ho : o ∈ (oTwo ↥L).map L.subtype) :
    l * o * l⁻¹ ∈ (oTwo ↥L).map L.subtype := by
  obtain ⟨o', ho', rfl⟩ := ho
  exact ⟨⟨l, hl⟩ * o' * ⟨l, hl⟩⁻¹, (inferInstance : (oTwo ↥L).Normal).conj_mem _ ho' _, rfl⟩

theorem IsL24.exists_prime_pow (hL : IsL24 S M A L) (hA : CFSG.Open.IsElemAbelian 2 A)
    {a : MulAut V} (haA : a ∈ A) (haO : a ∉ (oTwo ↥L).map L.subtype) :
    ∃ r t : ℕ, r.Prime ∧ r ≠ 2 ∧ (∀ y ∈ L, Odd (orderOf y) → y ^ r ^ t = 1) ∧
      ∀ b ∈ A, b ∈ (oTwo ↥L).map L.subtype ∨ a⁻¹ * b ∈ (oTwo ↥L).map L.subtype := by
  obtain ⟨r, t, hr, hr2, -, ⟨e⟩⟩ := hL.dihedral
  set φ : ↥L →* DihedralGroup (r ^ t) := e.toMonoidHom.comp (QuotientGroup.mk' (oTwo ↥L))
    with hφ
  have hker : ∀ g : ↥L, φ g = 1 ↔ g ∈ oTwo ↥L := by
    intro g
    rw [hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hodd : Odd (r ^ t) := (hr.odd_of_ne_two hr2).pow
  refine ⟨r, t, hr, hr2, fun y hy hyo => ?_, fun b hb => ?_⟩
  · set y' : ↥L := ⟨y, hy⟩ with hy'
    have hy'o : Odd (orderOf y') := by rwa [hy', Subgroup.orderOf_mk]
    have h1 : φ (y' ^ r ^ t) = 1 := by
      rw [map_pow]
      exact dihedral_pow_eq_one_of_odd (Odd.of_dvd_nat hy'o (orderOf_map_dvd φ y'))
    have h2 : y' ^ r ^ t = 1 := by
      refine eq_one_of_mem_oTwo ((hker _).mp h1) fun h2 => ?_
      have := Odd.of_dvd_nat hy'o (orderOf_pow_dvd (r ^ t))
      exact (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr h2)
    simpa [hy'] using congrArg Subtype.val h2
  · have haL : a ∈ L := hL.le haA
    have hbL : b ∈ L := hL.le hb
    set a' : ↥L := ⟨a, haL⟩ with ha'
    set b' : ↥L := ⟨b, hbL⟩ with hb'
    by_cases hφb : φ b' = 1
    · exact Or.inl ⟨b', (hker b').mp hφb, rfl⟩
    · right
      have hφa : φ a' ≠ 1 := fun h => haO ⟨a', (hker a').mp h, rfl⟩
      have hsq : ∀ c ∈ A, ∀ hc : c ∈ L, φ ⟨c, hc⟩ ^ 2 = 1 := by
        intro c hcA hc
        rw [← map_pow]
        have : (⟨c, hc⟩ : ↥L) ^ 2 = 1 := Subtype.ext (by simpa using hA.2 c hcA)
        rw [this, map_one]
      have hcomm : φ a' * φ b' = φ b' * φ a' := by
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (isElemAbelian_comm hA haA hb)
      have heq := dihedral_eq_of_commute hodd hφa (hsq a haA haL) hφb (hsq b hb hbL) hcomm
      have h1 : φ (a'⁻¹ * b') = 1 := by rw [map_mul, map_inv, heq, inv_mul_cancel]
      exact ⟨a'⁻¹ * b', (hker _).mp h1, rfl⟩

end L24Facts

section QuotTriv

@[expose] def quotTriv (U C : Subgroup V) : Subgroup (MulAut V) where
  carrier := {g | g ∈ stabSub U ∧ ∀ w ∈ U, g w * w⁻¹ ∈ C}
  one_mem' := ⟨(stabSub U).one_mem, fun w _ => by simp [C.one_mem]⟩
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨(stabSub U).mul_mem hx1 hy1, fun w hw => ?_⟩
    have hyw : y w ∈ U := (hy1 w).2 hw
    have e : (x * y) w * w⁻¹ = (x (y w) * (y w)⁻¹) * (y w * w⁻¹) := by
      rw [MulAut.mul_apply]; group
    rw [e]
    exact C.mul_mem (hx2 _ hyw) (hy2 w hw)
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨(stabSub U).inv_mem hx1, fun w hw => ?_⟩
    have hxw : x⁻¹ w ∈ U := ((stabSub U).inv_mem hx1 w).2 hw
    have h := C.inv_mem (hx2 _ hxw)
    rwa [MulAut.apply_inv_self, show (w * (x⁻¹ w)⁻¹)⁻¹ = x⁻¹ w * w⁻¹ by group] at h

theorem mem_quotTriv {U C : Subgroup V} {g : MulAut V} :
    g ∈ quotTriv U C ↔ g ∈ stabSub U ∧ ∀ w ∈ U, g w * w⁻¹ ∈ C := Iff.rfl

theorem elemAbOn_of_le_quotTriv (hV : ∀ v : V, v ^ 2 = 1) {Q : Subgroup (MulAut V)}
    {U C : Subgroup V} (hQ : Q ≤ quotTriv U C) (hQC : ∀ q ∈ Q, ∀ c ∈ C, q c = c) :
    ElemAbOn Q U := by
  have hinv : ∀ v : V, v⁻¹ = v :=
    fun v => inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hV v)
  have hdec : ∀ p ∈ Q, ∀ q ∈ Q, ∀ w ∈ U, p (q w) = (q w * w⁻¹) * p w := by
    intro p hp q hq w hw
    have h := map_mul p (q w * w⁻¹) w
    rwa [show q w * w⁻¹ * w = q w by group, hQC p hp _ ((hQ hq).2 w hw)] at h
  refine ⟨fun p hp q hq w hw => ?_, fun p hp w hw => ?_⟩
  · rw [hdec p hp q hq w hw, hdec q hq p hp w hw]
    ac_rfl
  · rw [hdec p hp p hp w hw]
    calc p w * w⁻¹ * p w = (p w * p w) * w⁻¹ := by ac_rfl
      _ = w := by rw [← pow_two, hV, one_mul, hinv]

theorem conj_mem_quotTriv {U C : Subgroup V} {l q : MulAut V} (hlU : l ∈ stabSub U)
    (hlC : ∀ c ∈ C, l c = c) (hq : q ∈ quotTriv U C) : l * q * l⁻¹ ∈ quotTriv U C := by
  refine ⟨(stabSub U).mul_mem ((stabSub U).mul_mem hlU hq.1) ((stabSub U).inv_mem hlU),
    fun w hw => ?_⟩
  have hw' : l⁻¹ w ∈ U := ((stabSub U).inv_mem hlU w).2 hw
  have hc := hq.2 _ hw'
  have e : (l * q * l⁻¹) w * w⁻¹ = l (q (l⁻¹ w) * (l⁻¹ w)⁻¹) := by
    rw [map_mul, map_inv, MulAut.apply_inv_self]
    rfl
  rw [e, hlC _ hc]
  exact hc

theorem commSub_sup_le_fixV {U C : Subgroup V} {q g : MulAut V} (hq : q ∈ quotTriv U C)
    (hqC : ∀ c ∈ C, q c = c) (hgU : g ∈ stabSub U) (hgC : ∀ c ∈ C, g c = c)
    (hqg : ∀ w ∈ U, q (g w) = g (q w)) :
    commSub U (Subgroup.zpowers g) ⊔ C ≤ fixV (Subgroup.zpowers q) := by
  rw [commSub_zpowers_eq_map_commMulHom hgU]
  refine sup_le ?_ fun c hc => mem_fixV_zpowers_iff_apply.mpr (hqC c hc)
  rintro _ ⟨w, hw, rfl⟩
  rw [mem_fixV_zpowers_iff_apply, commMulHom_apply]
  have hc := hq.2 w hw
  have e : q w = (q w * w⁻¹) * w := by group
  rw [map_mul, map_inv, hqg w hw, e, map_mul, hgC _ hc, ← div_eq_mul_inv, ← div_eq_mul_inv,
    mul_div_mul_left_eq_div, div_eq_mul_inv]

theorem commSub_zpowers_sup_eq [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {y : MulAut V}
    {U C : Subgroup V} (hyU : y ∈ stabSub U) (hCU : C ≤ U) (hyC : ∀ c ∈ C, y c = c)
    (hfpf : ∀ w ∈ U, y w * w⁻¹ ∈ C → w ∈ C) : commSub U (Subgroup.zpowers y) ⊔ C = U := by
  have h1 := rk_commSub_add_rk_inf_fixV hyU
  have hfixC : U ⊓ fixV (Subgroup.zpowers y) = C := by
    apply le_antisymm
    · rintro w ⟨hw, hwy⟩
      apply hfpf w hw
      rw [mem_fixV_zpowers_iff_apply.mp hwy, mul_inv_cancel]
      exact C.one_mem
    · exact le_inf hCU fun c hc => mem_fixV_zpowers_iff_apply.mpr (hyC c hc)
  have hinf : commSub U (Subgroup.zpowers y) ⊓ C = ⊥ := by
    rw [commSub_zpowers_eq_map_commMulHom hyU, eq_bot_iff]
    rintro _ ⟨⟨w, hw, rfl⟩, hc⟩
    rw [Subgroup.mem_bot, commMulHom_apply]
    rw [commMulHom_apply] at hc
    rw [hyC w (hfpf w hw hc), mul_inv_cancel]
  have h2 := rk_sup_add_rk_inf (commSub U (Subgroup.zpowers y)) C
  rw [hfixC] at h1
  rw [hinf, rk_bot] at h2
  have hle : commSub U (Subgroup.zpowers y) ⊔ C ≤ U :=
    sup_le (commSub_le_of_invariant fun g hg w hw =>
      ((Subgroup.zpowers_le.mpr hyU) hg w).2 hw) hCU
  exact eq_of_le_of_rk_le hV hle (by omega)

theorem resHom_mem_normalizer {X : Subgroup (MulAut V)} {U : Subgroup V} {g : MulAut V}
    (hgU : g ∈ stabSub U) (hX : X ≤ stabSub U)
    (hg : g ∈ Subgroup.normalizer (X : Set (MulAut V))) :
    resHom U ⟨g, hgU⟩ ∈ Subgroup.normalizer (autSub X U : Set (MulAut U)) := by
  have key : ∀ (h : MulAut V) (hhU : h ∈ stabSub U),
      h ∈ Subgroup.normalizer (X : Set (MulAut V)) → ∀ φ ∈ autSub X U,
        resHom U ⟨h, hhU⟩ * φ * (resHom U ⟨h, hhU⟩)⁻¹ ∈ autSub X U := by
    intro h hhU hh φ hφ
    obtain ⟨q, hqX, rfl⟩ := mem_autSub.mp hφ
    rw [← map_inv, ← map_mul, ← map_mul]
    exact mem_autSub.mpr ⟨_, (Subgroup.mem_normalizer_iff.mp hh q).mp hqX, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro φ
  refine ⟨key g hgU hg φ, fun hφ => ?_⟩
  have h := key g⁻¹ ((stabSub U).inv_mem hgU) (Subgroup.inv_mem _ hg) _ hφ
  have hinv : resHom U ⟨g⁻¹, (stabSub U).inv_mem hgU⟩ = (resHom U ⟨g, hgU⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  rw [hinv, inv_inv] at h
  have e : (resHom U ⟨g, hgU⟩)⁻¹ * (resHom U ⟨g, hgU⟩ * φ * (resHom U ⟨g, hgU⟩)⁻¹) *
      resHom U ⟨g, hgU⟩ = φ := by group
  rwa [e] at h

theorem card_modEq_of_forall_mem [Finite V] {y : MulAut V} {U C : Subgroup V} {r t : ℕ} [hr : Fact r.Prime]
    (hyU : y ∈ stabSub U) (hy : y ^ r ^ t = 1) (hCU : C ≤ U) (hyC : ∀ c ∈ C, y c = c)
    (hfpf : ∀ w ∈ U, y w * w⁻¹ ∈ C → w ∈ C) : Nat.card U ≡ Nat.card C [MOD r] := by
  set yR := resHom U ⟨y, hyU⟩ with hyR
  have h1 : yR ^ r ^ t = 1 := by
    have : (⟨y, hyU⟩ : stabSub U) ^ r ^ t = 1 := Subtype.ext (by simpa using hy)
    rw [hyR, ← map_pow, this, map_one]
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hr.out).mp (orderOf_dvd_of_pow_eq_one h1)
  have h := AutQ8D8.card_modEq_fixSub yR hk
  have hfix : AutQ8D8.fixSub yR = C.subgroupOf U := by
    ext w
    rw [AutQ8D8.mem_fixSub, Subgroup.mem_subgroupOf]
    constructor
    · intro hw
      apply hfpf w w.2
      have hyw : y w = w := congrArg Subtype.val hw
      rw [hyw, mul_inv_cancel]
      exact C.one_mem
    · intro hw
      exact Subtype.ext (hyC _ hw)
  rw [hfix, show Nat.card (C.subgroupOf U) = Nat.card C from
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCU).toEquiv] at h
  exact h

theorem card_autSub_modEq_one [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {Q : Subgroup (MulAut V)}
    {y : MulAut V} {U C : Subgroup V} {r t : ℕ} [hr : Fact r.Prime] (hQ : Q ≤ quotTriv U C)
    (hQC : ∀ q ∈ Q, ∀ c ∈ C, q c = c) (hyU : y ∈ stabSub U) (hy : y ^ r ^ t = 1)
    (hyQ : y ∈ Subgroup.normalizer (Q : Set (MulAut V))) (hCU : C ≤ U)
    (hyC : ∀ c ∈ C, y c = c) (hfpf : ∀ w ∈ U, y w * w⁻¹ ∈ C → w ∈ C) :
    Nat.card (autSub Q U) ≡ 1 [MOD r] := by
  have hQU : Q ≤ stabSub U := fun q hq => (hQ hq).1
  set Q' := autSub Q U with hQ'
  set yR := resHom U ⟨y, hyU⟩ with hyR
  have hyRN : yR ∈ Subgroup.normalizer (Q' : Set (MulAut U)) := resHom_mem_normalizer hyU hQU hyQ
  set α := Q'.normalizerMonoidHom ⟨yR, hyRN⟩ with hα
  have hαapp : ∀ p : Q', ((α p : Q') : MulAut U) = yR * p * yR⁻¹ := fun p => rfl
  have hαr : α ^ r ^ t = 1 := by
    have h1 : (⟨yR, hyRN⟩ : Subgroup.normalizer (Q' : Set (MulAut U))) ^ r ^ t = 1 := by
      apply Subtype.ext
      have : (⟨y, hyU⟩ : stabSub U) ^ r ^ t = 1 := Subtype.ext (by simpa using hy)
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [hyR, ← map_pow, this, map_one]
    rw [hα, ← map_pow, h1, map_one]
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hr.out).mp (orderOf_dvd_of_pow_eq_one hαr)
  have hmod := AutQ8D8.card_modEq_fixSub α hk
  have hU := commSub_zpowers_sup_eq hV hyU hCU hyC hfpf
  have hfix : AutQ8D8.fixSub α = ⊥ := by
    rw [eq_bot_iff]
    intro p hp
    rw [AutQ8D8.mem_fixSub] at hp
    rw [Subgroup.mem_bot]
    obtain ⟨q, hqQ, hpq⟩ := mem_autSub.mp p.2
    have hcomm : ∀ w ∈ U, (q : MulAut V) (y w) = y ((q : MulAut V) w) := by
      intro w hw
      have h1 : yR * (p : MulAut U) * yR⁻¹ = p := by rw [← hαapp, hp]
      have h2 : (p : MulAut U) * yR = yR * p := by
        calc (p : MulAut U) * yR = yR * p * yR⁻¹ * yR := by rw [h1]
          _ = yR * p := by group
      have h3 := congrArg (fun φ : MulAut U => ((φ ⟨w, hw⟩ : U) : V)) h2
      simp only [MulAut.mul_apply] at h3
      rw [← hpq] at h3
      exact h3
    have hle := commSub_sup_le_fixV (hQ hqQ) (hQC q hqQ) hyU hyC hcomm
    rw [hU] at hle
    apply Subtype.ext
    change (p : MulAut U) = 1
    rw [← hpq]
    ext w
    exact mem_fixV_zpowers_iff_apply.mp (hle w.2)
  rw [hfix, Subgroup.card_bot] at hmod
  exact hmod

variable [Finite V]

theorem dimOn_le_two_mul_dimOn (hV : ∀ v : V, v ^ 2 = 1) {Q : Subgroup (MulAut V)}
    {a : MulAut V} {U C : Subgroup V} (hQ2 : IsPGroup 2 Q) (hQ : Q ≤ quotTriv U C)
    (hQC : ∀ q ∈ Q, ∀ c ∈ C, q c = c) (haU : a ∈ stabSub U) (ha2 : a ^ 2 = 1)
    (haQ : a ∈ Subgroup.normalizer (Q : Set (MulAut V))) (haC : ∀ c ∈ C, a c = c) :
    dimOn Q U ≤ 2 * dimOn (Q ⊓ centSub (commSub U (Subgroup.zpowers a) ⊔ C)) U := by
  have hQU : Q ≤ stabSub U := fun q hq => (hQ hq).1
  set B := Q ⊓ centSub (commSub U (Subgroup.zpowers a) ⊔ C) with hB
  set Q' := autSub Q U with hQ'
  set aR := resHom U ⟨a, haU⟩ with haR
  have haRN : aR ∈ Subgroup.normalizer (Q' : Set (MulAut U)) := resHom_mem_normalizer haU hQU haQ
  set α := Q'.normalizerMonoidHom ⟨aR, haRN⟩ with hα
  have hαapp : ∀ p : Q', ((α p : Q') : MulAut U) = aR * p * aR⁻¹ := fun p => rfl
  have hel := elemAbOn_of_le_quotTriv hV hQ hQC
  have haR2 : aR * aR = 1 := by
    have : (⟨a, haU⟩ : stabSub U) * ⟨a, haU⟩ = 1 :=
      Subtype.ext (show a * a = 1 by rw [← pow_two]; exact ha2)
    rw [haR, ← map_mul, this, map_one]
  have hc : ∀ p q : Q', p * q = q * p := by
    rintro ⟨φ, hφ⟩ ⟨ψ, hψ⟩
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
    obtain ⟨h, hh, rfl⟩ := mem_autSub.mp hψ
    apply Subtype.ext
    ext w
    exact hel.1 _ hg _ hh w w.2
  have h2 : ∀ p : Q', p * p = 1 := by
    rintro ⟨φ, hφ⟩
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
    apply Subtype.ext
    ext w
    exact hel.2 _ hg w w.2
  have hαα : ∀ p, α (α p) = p := by
    intro p
    apply Subtype.ext
    rw [hαapp, hαapp]
    calc aR * (aR * (p : MulAut U) * aR⁻¹) * aR⁻¹ = (aR * aR) * p * (aR * aR)⁻¹ := by group
      _ = p := by rw [haR2]; group
  have hsq := card_le_card_fixSub_sq hc h2 α hαα
  have hfixB : ∀ p : Q', p ∈ AutQ8D8.fixSub α → (p : MulAut U) ∈ autSub B U := by
    intro p hp
    rw [AutQ8D8.mem_fixSub] at hp
    obtain ⟨q, hqQ, hpq⟩ := mem_autSub.mp p.2
    have hcomm : ∀ w ∈ U, (q : MulAut V) (a w) = a ((q : MulAut V) w) := by
      intro w hw
      have h1 : aR * (p : MulAut U) * aR⁻¹ = p := by rw [← hαapp, hp]
      have h2 : (p : MulAut U) * aR = aR * p := by
        calc (p : MulAut U) * aR = aR * p * aR⁻¹ * aR := by rw [h1]
          _ = aR * p := by group
      have h3 := congrArg (fun φ : MulAut U => ((φ ⟨w, hw⟩ : U) : V)) h2
      simp only [MulAut.mul_apply] at h3
      rw [← hpq] at h3
      exact h3
    have hle := commSub_sup_le_fixV (hQ hqQ) (hQC q hqQ) haU haC hcomm
    exact mem_autSub.mpr ⟨q, ⟨hqQ, fun v hv => mem_fixV_zpowers_iff_apply.mp (hle hv)⟩, hpq⟩
  have hcard : Nat.card (AutQ8D8.fixSub α) ≤ Nat.card (autSub B U) := by
    refine Nat.card_le_card_of_injective
      (fun p => (⟨((p : Q') : MulAut U), hfixB p p.2⟩ : autSub B U)) ?_
    intro p p' h
    have h' := congrArg (fun x : autSub B U => (x : MulAut U)) h
    exact Subtype.ext (Subtype.ext h')
  have e1 := card_autSub_eq_two_pow hQU hQ2
  have e2 := card_autSub_eq_two_pow (inf_le_left.trans hQU) (hQ2.to_le inf_le_left : IsPGroup 2 B)
  have : 2 ^ dimOn Q U ≤ 2 ^ (2 * dimOn B U) := by
    rw [← e1, pow_mul', ← e2]
    exact hsq.trans (Nat.pow_le_pow_left hcard 2)
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this

theorem dimOn_add_dimOn_le {Q B B' : Subgroup (MulAut V)} {U F F' : Subgroup V}
    (hQU : Q ≤ stabSub U) (hQ2 : IsPGroup 2 Q) (hB : B ≤ Q) (hB' : B' ≤ Q)
    (hBF : B ≤ centSub F) (hB'F' : B' ≤ centSub F') (hFF : F ⊔ F' = U) :
    dimOn B U + dimOn B' U ≤ dimOn Q U := by
  have hFU : F ≤ U := by rw [← hFF]; exact le_sup_left
  have hinf : autSub B U ⊓ autSub B' U = ⊥ := by
    rw [eq_bot_iff]
    rintro φ ⟨h1, h2⟩
    obtain ⟨b, hb, rfl⟩ := mem_autSub.mp h1
    obtain ⟨b', hb', hbb'⟩ := mem_autSub.mp h2
    rw [Subgroup.mem_bot, ← hbb']
    have hfix : F ⊔ F' ≤ fixV (Subgroup.zpowers (b' : MulAut V)) := by
      refine sup_le (fun v hv => ?_) fun v hv => mem_fixV_zpowers_iff_apply.mpr (hB'F' hb' v hv)
      rw [mem_fixV_zpowers_iff_apply]
      have := congrArg (fun φ : MulAut U => ((φ ⟨v, hFU hv⟩ : U) : V)) hbb'
      simp only [resHom_apply] at this
      rw [this]
      exact hBF hb v hv
    ext w
    exact mem_fixV_zpowers_iff_apply.mp (hfix (by rw [hFF]; exact w.2))
  have h := card_mul_card_le_of_inf_eq_bot (autSub_mono hB U) (autSub_mono hB' U) hinf
  rw [card_autSub_eq_two_pow (hB.trans hQU) (hQ2.to_le hB),
    card_autSub_eq_two_pow (hB'.trans hQU) (hQ2.to_le hB'), card_autSub_eq_two_pow hQU hQ2,
    ← pow_add] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h

theorem inf_oTwo_le_quotTriv {S M A L : Subgroup (MulAut V)} {Z₀ U : Subgroup V}
    (hS : IsPGroup 2 S) (hSZ : S ≤ stabSub Z₀) (hMZ : M ≤ stabSub Z₀) (hq : IsQuadratic A)
    (hZA : Z₀ ≤ fixV A) (hL : IsL24 S M A L) (hZU : Z₀ ≤ U) (hLU : L ≤ stabSub U)
    (hgen : ∀ W : Subgroup V, (∀ l ∈ L, Z₀.map l.toMonoidHom ≤ W) → U ≤ W) :
    A ⊓ (oTwo ↥L).map L.subtype ≤ quotTriv U (U ⊓ fixV L) := by
  rintro b ⟨hbA, hbO⟩
  have hbL : b ∈ L := hL.le hbA
  have hbU : b ∈ stabSub U := hLU hbL
  refine ⟨hbU, ?_⟩
  let W : Subgroup V := U ⊓ (U ⊓ fixV L).comap (commMulHom b)
  suffices hUW : U ≤ W from fun w hw => (hUW hw).2
  refine hgen W fun l hl => ?_
  rintro _ ⟨z, hz, rfl⟩
  have hlz : l z ∈ U := (hLU hl z).2 (hZU hz)
  refine ⟨hlz, ?_⟩
  change b (l z) * (l z)⁻¹ ∈ U ⊓ fixV L
  refine ⟨U.mul_mem ((hbU _).2 hlz) (U.inv_mem hlz), ?_⟩
  by_cases hlM : l ∈ M
  · have hlz' : l z ∈ Z₀ := (hMZ hlM z).2 hz
    rw [hZA hlz' b hbA, mul_inv_cancel]
    exact (fixV L).one_mem
  · rw [← hL.sup_conj l hl hlM, fixV_sup_eq_inf]
    refine ⟨hq (Subgroup.subset_closure ⟨b, hbA, l z, rfl⟩), ?_⟩
    rw [fixV_map_conj]
    have hb' : l⁻¹ * b * l ∈ S := by
      have := conj_mem_map_oTwo (L := L) (L.inv_mem hl) hbO
      rw [inv_inv] at this
      exact ((hL.oTwo_le_inf hS) this).1
    have hz' : (l⁻¹ * b * l) z ∈ Z₀ := (hSZ hb' z).2 hz
    refine ⟨(l⁻¹ * b * l) z * z⁻¹, hZA (Z₀.mul_mem hz' (Z₀.inv_mem hz)), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, MulAut.mul_apply,
      MulAut.apply_inv_self]

end QuotTriv

section Dihedral29

variable [Finite V]

theorem false_of_isL24 (hV : ∀ v : V, v ^ 2 = 1) {S M A L : Subgroup (MulAut V)}
    {Z₀ U : Subgroup V} (hS : IsPGroup 2 S) (hSM : S ≤ M) (hMZ : M ≤ stabSub Z₀)
    (hLM : L ⊓ stabSub Z₀ ≤ M) (hAel : CFSG.Open.IsElemAbelian 2 A) (hq : IsQuadratic A)
    (hZA : Z₀ ≤ fixV A) (hgt : AGt S Z₀ 1) (hL : IsL24 S M A L)
    (hS3 : ∀ a ∈ L, ∀ y ∈ L, a ^ 2 = 1 → y ^ 3 = 1 → a * y * a⁻¹ = y⁻¹ → y = 1)
    (hZU : Z₀ ≤ U) (hLU : L ≤ stabSub U)
    (hgen : ∀ W : Subgroup V, (∀ l ∈ L, Z₀.map l.toMonoidHom ≤ W) → U ≤ W)
    (hAU : codimOn A U ≤ dimOn A U) : False := by
  have hSZ : S ≤ stabSub Z₀ := hSM.trans hMZ
  have h25 : Hyp25 S M A L Z₀ U := ⟨hL, hS, hSM, hAel, hq, hZA, hZU, hLU, hgen⟩
  have hOS : (oTwo ↥L).map L.subtype ≤ S := fun o ho => ((hL.oTwo_le_inf hS) ho).1
  have hCU : U ⊓ fixV L ≤ U := inf_le_left
  have hLC : ∀ l ∈ L, ∀ c ∈ U ⊓ fixV L, l c = c := fun l hl c hc => hc.2 l hl
  obtain ⟨a, haA, haO⟩ := hL.exists_mem_not_mem_oTwo
  obtain ⟨x, hxL, hxM⟩ := Set.not_subset.mp hL.not_le
  have haL : a ∈ L := hL.le haA
  have ha2 : a ^ 2 = 1 := hAel.2 a haA
  obtain ⟨b1, b2, -, b4, b5⟩ := h25.fixV_eq hV haA haO
  have hsup := h25.sup_fixV_conj_eq hV hxL hxM
  have hr1 := rk_sup_add_rk_inf (commSub U (Subgroup.zpowers a)) (U ⊓ fixV L)
  rw [b2, b4, rk_bot] at hr1
  have hr2 : codimOn A U + rk ↥(U ⊓ fixV A) = rk U := by
    have := mRel_add_rk_of_le (inf_le_left : U ⊓ fixV A ≤ U)
    rwa [show mRel (U ⊓ fixV A) U = codimOn A U by
      unfold codimOn mRel; rw [inf_comm, Subgroup.inf_relIndex_right]] at this
  have hr3 := mRel_add_rk_of_le hCU
  have hUC : mRel (U ⊓ fixV L) U = 2 * codimOn A U := by omega
  have hs1 : 1 ≤ codimOn A U := by
    by_contra h0
    have hC0 : mRel (U ⊓ fixV L) U = 0 := by omega
    rw [mRel_eq_zero_iff (isPGroup_subgroup hV U)] at hC0
    exact hxM (hLM ⟨hxL, centSub_le_stabSub Z₀ fun z hz => (hC0 (hZU hz)).2 x hxL⟩)
  obtain ⟨r, t, hr, hr2', hodd, hAO⟩ := hL.exists_prime_pow hAel haA haO
  haveI : Fact r.Prime := ⟨hr⟩
  have hA2 : IsPGroup 2 A := fun g => ⟨1, Subtype.ext (by simpa using hAel.2 g g.2)⟩
  have hidx : (A ⊓ (oTwo ↥L).map L.subtype).relIndex A ≤ 2 := by
    refine relIndex_le_two_of_forall haA fun b hb => ?_
    rcases hAO b hb with h | h
    · exact Or.inl ⟨hb, h⟩
    · exact Or.inr ⟨A.mul_mem (A.inv_mem haA) hb, h⟩
  have hdA := dimOn_le_dimOn_add_one hA2 inf_le_left hidx U
  obtain ⟨Q, hQ⟩ : ∃ Q : Subgroup (MulAut V),
      Q = (oTwo ↥L).map L.subtype ⊓ quotTriv U (U ⊓ fixV L) := ⟨_, rfl⟩
  have hQO : Q ≤ (oTwo ↥L).map L.subtype := hQ ▸ inf_le_left
  have hQT : Q ≤ quotTriv U (U ⊓ fixV L) := hQ ▸ inf_le_right
  have hQS : Q ≤ S := hQO.trans hOS
  have hQ2 : IsPGroup 2 Q := hS.to_le hQS
  have hQL : Q ≤ L := hQO.trans (Subgroup.map_subtype_le _)
  have hQC : ∀ q ∈ Q, ∀ c ∈ U ⊓ fixV L, q c = c := fun q hq => hLC q (hQL hq)
  have hQU : Q ≤ stabSub U := hQL.trans hLU
  have hconj : ∀ l ∈ L, ∀ q ∈ Q, l * q * l⁻¹ ∈ Q := by
    intro l hl q hq
    rw [hQ] at hq ⊢
    exact ⟨conj_mem_map_oTwo hl hq.1, conj_mem_quotTriv (hLU hl) (hLC l hl) hq.2⟩
  have hQN : L ≤ Subgroup.normalizer (Q : Set (MulAut V)) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro q
    refine ⟨hconj l hl q, fun h => ?_⟩
    have := hconj l⁻¹ (L.inv_mem hl) _ h
    rwa [show l⁻¹ * (l * q * l⁻¹) * l⁻¹⁻¹ = q by group] at this
  have hel := elemAbOn_of_le_quotTriv hV hQT hQC
  have hA₀Q : A ⊓ (oTwo ↥L).map L.subtype ≤ Q := by
    rw [hQ]
    exact le_inf inf_le_right (inf_oTwo_le_quotTriv hS hSZ hMZ hq hZA hL hZU hLU hgen)
  obtain ⟨B₀, hB₀⟩ : ∃ B : Subgroup (MulAut V), B = Q ⊓ centSub (U ⊓ fixV A) := ⟨_, rfl⟩
  have hB₀Q : B₀ ≤ Q := hB₀ ▸ inf_le_left
  have hB₀F : B₀ ≤ centSub (U ⊓ fixV A) := hB₀ ▸ inf_le_right
  have hA₀B₀ : A ⊓ (oTwo ↥L).map L.subtype ≤ B₀ := by
    rw [hB₀]
    exact le_inf hA₀Q fun b hb w hw => hw.2 b hb.1
  have hdA₀ : dimOn (A ⊓ (oTwo ↥L).map L.subtype) U ≤ dimOn B₀ U :=
    mRel_le_of_le_right (hQ2.to_le hB₀Q) hA₀B₀
  have hcB₀ : codimOn B₀ U ≤ codimOn A U := by
    have h1 : fixV A ⊓ U ≤ fixV B₀ := fun v hv b hb => hB₀F hb v ⟨hv.2, hv.1⟩
    have h2 := mRel_le_of_le_left (isPGroup_subgroup hV U) h1
    rwa [show mRel (fixV A ⊓ U) U = codimOn A U by
      unfold codimOn mRel; rw [Subgroup.inf_relIndex_right]] at h2
  have hdB₀ : dimOn B₀ U < codimOn A U := by
    by_cases hfix : U ≤ fixV B₀
    · have h0 : dimOn B₀ U = 0 := by
        rw [mRel_eq_zero_iff (hQ2.to_le hB₀Q)]
        exact fun g hg u hu => hfix hu g hg
      omega
    · have h := mul_dimOn_lt_codimOn hV (H := L) hQ2 hQS hQN hLU hZU hgen hgt (A := B₀) hB₀Q
        (hel.mono hB₀Q le_rfl) hfix
      rw [one_mul] at h
      have h' : dimOn B₀ U < codimOn B₀ U := by exact_mod_cast h
      omega
  have hsk : codimOn A U = dimOn B₀ U + 1 := by omega
  obtain ⟨B₀x, hB₀x⟩ : ∃ B : Subgroup (MulAut V), B = B₀.map (MulAut.conj x).toMonoidHom :=
    ⟨_, rfl⟩
  have hB₀xQ : B₀x ≤ Q := by
    rw [hB₀x]
    rintro _ ⟨b, hb, rfl⟩
    exact hconj x hxL b (hB₀Q hb)
  have hB₀xF : B₀x ≤ centSub (U ⊓ fixV (A.map (MulAut.conj x).toMonoidHom)) := by
    rw [hB₀x]
    rintro _ ⟨b, hb, rfl⟩
    intro w hw
    obtain ⟨hwU, hwA⟩ := hw
    rw [fixV_map_conj] at hwA
    obtain ⟨v, hv, rfl⟩ := hwA
    have hvU : v ∈ U := ((hLU hxL) v).1 hwU
    have hbv : b v = v := hB₀F hb v ⟨hvU, hv⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.mul_apply,
      MulAut.inv_apply_self, hbv]
  have hdB₀x : dimOn B₀x U = dimOn B₀ U := by
    have h := dimOn_map_conj x B₀ U
    rwa [map_eq_self_of_mem_stabSub (hLU hxL), ← hB₀x] at h
  have hlow := dimOn_add_dimOn_le hQU hQ2 hB₀Q hB₀xQ hB₀F hB₀xF hsup
  have hup := dimOn_le_two_mul_dimOn hV hQ2 hQT hQC (hLU haL) ha2 (hQN haL) (hLC a haL)
  rw [b2, ← hB₀] at hup
  have hQk : dimOn Q U = 2 * dimOn B₀ U := by omega
  obtain ⟨g, hg⟩ : ∃ g : MulAut V, g = a * (x * a * x⁻¹) := ⟨_, rfl⟩
  have hgL : g ∈ L := hg ▸ L.mul_mem haL (L.mul_mem (L.mul_mem hxL haL) (L.inv_mem hxL))
  have hfpf : ∀ w ∈ U, g w * w⁻¹ ∈ U ⊓ fixV L → w ∈ U ⊓ fixV L := fun w hw hc =>
    h25.mem_of_comm_mem hV haA haO hxL hxM hw (hg ▸ hc)
  obtain ⟨j, m, hm, hgo⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  obtain ⟨y, hy⟩ : ∃ y : MulAut V, y = g ^ 2 ^ j := ⟨_, rfl⟩
  have hyL : y ∈ L := hy ▸ L.pow_mem hgL _
  have hyfpf : ∀ w ∈ U, y w * w⁻¹ ∈ U ⊓ fixV L → w ∈ U ⊓ fixV L := by
    rw [hy]
    exact forall_mem_of_pow_two_pow hV (hLU hgL) hCU (hLC g hgL) hfpf hm hgo
  have hyo : Odd (orderOf y) := by
    rw [hy, orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨m, hgo⟩, hgo,
      Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
    exact hm
  have hyr : y ^ r ^ t = 1 := hodd y hyL hyo
  have hay : a * y * a⁻¹ = y⁻¹ := by
    have ha' : a * a = 1 := by rw [← pow_two]; exact ha2
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha'
    have hag : a * g * a⁻¹ = g⁻¹ := by
      calc a * g * a⁻¹ = (a * a) * (x * a * x⁻¹) * a⁻¹ := by rw [hg]; group
        _ = x * a⁻¹ * x⁻¹ * a⁻¹ := by rw [ha', hai]; group
        _ = g⁻¹ := by rw [hg]; group
    rw [hy, ← conj_pow, hag, inv_pow]
  have hc1 := card_modEq_of_forall_mem (hLU hyL) hyr hCU (hLC y hyL) hyfpf
  rw [card_eq_two_pow hV U, card_eq_two_pow hV (U ⊓ fixV L),
    show rk U = rk ↥(U ⊓ fixV L) + 2 * codimOn A U by omega, pow_add] at hc1
  have hgcd : Nat.gcd r (2 ^ rk ↥(U ⊓ fixV L)) = 1 :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hr Nat.prime_two).mpr hr2')
  have h4s : 2 ^ (2 * codimOn A U) ≡ 1 [MOD r] :=
    Nat.ModEq.cancel_left_of_coprime hgcd (by rwa [mul_one])
  have hc2 := card_autSub_modEq_one hV hQT hQC (hLU hyL) hyr (hQN hyL) hCU (hLC y hyL) hyfpf
  rw [card_autSub_eq_two_pow hQU hQ2, hQk] at hc2
  have h3 : r ∣ 3 := by
    rw [hsk, show 2 * (dimOn B₀ U + 1) = 2 * dimOn B₀ U + 2 by ring, pow_add] at h4s
    have h4 : 2 ^ (2 * dimOn B₀ U) * 2 ^ 2 ≡ 1 * 2 ^ 2 [MOD r] := Nat.ModEq.mul_right _ hc2
    have h41 : 1 ≡ 4 [MOD r] := by
      have := h4s.symm.trans h4
      norm_num at this
      exact this
    exact (Nat.modEq_iff_dvd' (by norm_num)).mp h41
  have hr3 : r = 3 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h3
  subst hr3
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hyr)
  rcases e with _ | e
  · rw [pow_zero, orderOf_eq_one_iff] at he
    have hUC' : U ≤ U ⊓ fixV L := fun w hw => hyfpf w hw (by
      rw [he, MulAut.one_apply, mul_inv_cancel]; exact (U ⊓ fixV L).one_mem)
    have := (mRel_eq_zero_iff (isPGroup_subgroup hV U)).mpr hUC'
    omega
  · obtain ⟨z, hz⟩ : ∃ z : MulAut V, z = y ^ 3 ^ e := ⟨_, rfl⟩
    have hzo : orderOf z = 3 := by
      rw [hz, orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num)) ⟨3, by rw [he, pow_succ]⟩, he,
        pow_succ, Nat.mul_div_cancel_left _ (pow_pos (by norm_num) _)]
    have hz3 : z ^ 3 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one z
    have hz1 : z ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hzo
      norm_num at hzo
    have haz : a * z * a⁻¹ = z⁻¹ := by rw [hz, ← conj_pow, hay, inv_pow]
    exact hz1 (hS3 a haL z (hz ▸ L.pow_mem hyL _) ha2 hz3 haz)

end Dihedral29

section SpanOrbit

@[expose] def spanOrbit (X : Subgroup (MulAut V)) (Z : Subgroup V) : Subgroup V :=
  ⨆ x : X, Z.map (x : MulAut V).toMonoidHom

theorem map_le_spanOrbit {X : Subgroup (MulAut V)} {Z : Subgroup V} {x : MulAut V} (hx : x ∈ X) :
    Z.map x.toMonoidHom ≤ spanOrbit X Z :=
  le_iSup (fun x : X => Z.map (x : MulAut V).toMonoidHom) ⟨x, hx⟩

theorem le_spanOrbit (X : Subgroup (MulAut V)) (Z : Subgroup V) : Z ≤ spanOrbit X Z := by
  have h := map_le_spanOrbit (Z := Z) X.one_mem
  rwa [show (1 : MulAut V).toMonoidHom = MonoidHom.id V from rfl, Subgroup.map_id] at h

theorem spanOrbit_le {X : Subgroup (MulAut V)} {Z W : Subgroup V}
    (h : ∀ x ∈ X, Z.map x.toMonoidHom ≤ W) : spanOrbit X Z ≤ W :=
  iSup_le fun x => h x x.2

theorem le_stabSub_spanOrbit (X : Subgroup (MulAut V)) (Z : Subgroup V) :
    X ≤ stabSub (spanOrbit X Z) := by
  refine le_stabSub_of_forall_apply_mem fun g hg u hu => ?_
  have h : (spanOrbit X Z).map g.toMonoidHom ≤ spanOrbit X Z := by
    rw [spanOrbit, Subgroup.map_iSup]
    refine iSup_le fun x => ?_
    rw [Subgroup.map_map]
    exact map_le_spanOrbit (x := g * (x : MulAut V)) (X.mul_mem hg x.2)
  exact h ⟨u, hu, rfl⟩

end SpanOrbit

section Setting

structure Setting29 (𝒦 : HostClass) {V : Type*} [CommGroup V] (H S : Subgroup (MulAut V))
    (Z₀ : Subgroup V) : Prop where
  sq : ∀ v : V, v ^ 2 = 1
  holds : 𝒦.Holds H
  sym3Free : IsSym3Free H
  le : S ≤ H
  isPGroup : IsPGroup 2 S
  not_dvd : ¬ 2 ∣ S.relIndex H
  stab : S ≤ stabSub Z₀
  gen : ∀ W : Subgroup V, (∀ h ∈ H, Z₀.map h.toMonoidHom ≤ W) → ⊤ ≤ W

theorem holds_autSub {𝒦 : HostClass} {X : Subgroup (MulAut V)} {U : Subgroup V}
    (hXU : X ≤ stabSub U) (h : 𝒦.Holds X) : 𝒦.Holds (autSub X U) := by
  let f : X →* MulAut U := (resHom U).comp (Subgroup.inclusion hXU)
  have hf : f.range = autSub X U := by
    ext φ
    rw [MonoidHom.mem_range, mem_autSub]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hXU x, x.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  exact HostClass.Holds.of_mulEquiv ((QuotientGroup.quotientKerEquivRange f).trans
    (MulEquiv.subgroupCongr hf)) (h.quotient f.ker)

theorem isSym3Free_autSub {X : Subgroup (MulAut V)} {U : Subgroup V} (hXU : X ≤ stabSub U)
    (h : IsSym3Free X) : IsSym3Free (autSub X U) := by
  let f : X →* MulAut U := (resHom U).comp (Subgroup.inclusion hXU)
  have hf : f.range = autSub X U := by
    ext φ
    rw [MonoidHom.mem_range, mem_autSub]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hXU x, x.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  exact IsSym3Free.of_mulEquiv ((QuotientGroup.quotientKerEquivRange f).trans
    (MulEquiv.subgroupCongr hf)) (h.quotient f.ker)

theorem holds_of_le {𝒦 : HostClass} {G : Type*} [Group G] {X H : Subgroup G} (hXH : X ≤ H)
    (h : 𝒦.Holds H) : 𝒦.Holds X :=
  HostClass.Holds.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hXH) (h.subgroup (X.subgroupOf H))

theorem isSym3Free_of_le {G : Type*} [Group G] {X H : Subgroup G} (hXH : X ≤ H)
    (h : IsSym3Free H) : IsSym3Free X :=
  IsSym3Free.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hXH) (h.subgroup (X.subgroupOf H))

variable [Finite V]

theorem relIndex_autSub_dvd {S X : Subgroup (MulAut V)} {U : Subgroup V} (hSX : S ≤ X)
    (hXU : X ≤ stabSub U) : (autSub S U).relIndex (autSub X U) ∣ S.relIndex X := by
  have hSU : S ≤ stabSub U := hSX.trans hXU
  have h1 := Subgroup.relIndex_mul_card (autSub S U) (autSub X U)
  rw [inf_eq_left.mpr (autSub_mono hSX U)] at h1
  have h2 := card_autSub_mul hXU
  have h3 := card_autSub_mul hSU
  have h4 := Subgroup.relIndex_mul_card S X
  rw [inf_eq_left.mpr hSX] at h4
  have h5 := Subgroup.relIndex_mul_card (S ⊓ centSub U) (X ⊓ centSub U)
  rw [inf_eq_left.mpr (inf_le_inf_right _ hSX)] at h5
  refine ⟨(S ⊓ centSub U).relIndex (X ⊓ centSub U), ?_⟩
  have hpos : 0 < Nat.card (autSub S U) * Nat.card ↥(S ⊓ centSub U) :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc S.relIndex X * (Nat.card (autSub S U) * Nat.card ↥(S ⊓ centSub U))
      = S.relIndex X * Nat.card S := by rw [h3]
    _ = Nat.card X := h4
    _ = Nat.card (autSub X U) * Nat.card ↥(X ⊓ centSub U) := h2.symm
    _ = (autSub S U).relIndex (autSub X U) * (S ⊓ centSub U).relIndex (X ⊓ centSub U) *
        (Nat.card (autSub S U) * Nat.card ↥(S ⊓ centSub U)) := by
      rw [← h1, ← h5]
      ring

theorem Setting29.restrict {𝒦 : HostClass} {H S : Subgroup (MulAut V)} {Z₀ : Subgroup V}
    (h : Setting29 𝒦 H S Z₀) {X : Subgroup (MulAut V)} {U : Subgroup V} (hSX : S ≤ X)
    (hXH : X ≤ H) (hZU : Z₀ ≤ U) (hXU : X ≤ stabSub U)
    (hgen : ∀ W : Subgroup V, (∀ x ∈ X, Z₀.map x.toMonoidHom ≤ W) → U ≤ W) :
    Setting29 𝒦 (autSub X U) (autSub S U) (Z₀.subgroupOf U) where
  sq v := Subtype.ext (by simpa using h.sq v)
  holds := holds_autSub hXU (holds_of_le hXH h.holds)
  sym3Free := isSym3Free_autSub hXU (isSym3Free_of_le hXH h.sym3Free)
  le := autSub_mono hSX U
  isPGroup := by
    have : IsPGroup 2 (S.subgroupOf (stabSub U)) := h.isPGroup.comap_subtype
    exact this.map (resHom U)
  not_dvd := by
    have hdvd : S.relIndex X ∣ S.relIndex H := by
      rw [← Subgroup.relIndex_mul_relIndex S X H hSX hXH]
      exact dvd_mul_right _ _
    exact fun h2 => h.not_dvd (h2.trans ((relIndex_autSub_dvd hSX hXU).trans hdvd))
  stab := by
    intro φ hφ
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
    intro u
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, resHom_apply]
    exact h.stab hg u
  gen := by
    intro W hW
    have hle : U ≤ W.map U.subtype := by
      refine hgen _ fun x hx => ?_
      rintro _ ⟨z, hz, rfl⟩
      have hzU : z ∈ U := hZU hz
      have h1 := hW (resHom U ⟨x, hXU hx⟩) (mem_autSub.mpr ⟨⟨x, hXU hx⟩, hx, rfl⟩)
        ⟨⟨z, hzU⟩, show z ∈ Z₀ from hz, rfl⟩
      exact ⟨_, h1, rfl⟩
    intro u _
    obtain ⟨w, hw, hwu⟩ := hle u.2
    rwa [show w = u from Subtype.ext hwu] at hw

theorem Setting29.mono {𝒦 : HostClass} {H S : Subgroup (MulAut V)} {Z₀ Z₁ : Subgroup V}
    (h : Setting29 𝒦 H S Z₀) (hZ : Z₀ ≤ Z₁) (hS : S ≤ stabSub Z₁) : Setting29 𝒦 H S Z₁ :=
  { h with
    stab := hS
    gen := fun W hW => h.gen W fun g hg => (Subgroup.map_mono hZ).trans (hW g hg) }

theorem index_mul_card_autSub_lt {Z₀ U : Subgroup V} {X H : Subgroup (MulAut V)} (hZU : Z₀ ≤ U)
    (hXH : X ≤ H) (hXU : X ≤ stabSub U) (hne : U ≠ ⊤ ∨ X ≠ H) :
    (Z₀.subgroupOf U).index * Nat.card (autSub X U) < Z₀.index * Nat.card H := by
  have h1 : (Z₀.subgroupOf U).index = Z₀.relIndex U := rfl
  have h2 := Subgroup.relIndex_mul_index hZU
  have h3 : Nat.card (autSub X U) ≤ Nat.card X := by
    have := card_autSub_mul hXU
    calc Nat.card (autSub X U) ≤ Nat.card (autSub X U) * Nat.card ↥(X ⊓ centSub U) :=
          Nat.le_mul_of_pos_right _ Nat.card_pos
      _ = Nat.card X := this
  have h4 : Nat.card X ≤ Nat.card H := Subgroup.card_le_of_le hXH
  have hr : 0 < Z₀.relIndex U := Nat.pos_of_ne_zero (relIndex_ne_zero_of_finite _ _)
  have hH : 0 < Nat.card H := Nat.card_pos
  rw [h1, ← h2]
  rcases hne with hU | hX
  · have hi : 2 ≤ U.index := by
      have h0 : U.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have h1' : U.index ≠ 1 := fun h => hU (Subgroup.index_eq_one.mp h)
      omega
    calc Z₀.relIndex U * Nat.card (autSub X U) ≤ Z₀.relIndex U * Nat.card H :=
          Nat.mul_le_mul_left _ (h3.trans h4)
      _ < Z₀.relIndex U * U.index * Nat.card H := by
        rw [mul_assoc]
        exact Nat.mul_lt_mul_of_pos_left (by nlinarith) hr
  · have hlt : Nat.card X < Nat.card H := Subgroup.card_lt_of_lt (lt_of_le_of_ne hXH hX)
    have hi : 0 < U.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    calc Z₀.relIndex U * Nat.card (autSub X U) ≤ Z₀.relIndex U * Nat.card X :=
          Nat.mul_le_mul_left _ h3
      _ < Z₀.relIndex U * Nat.card H := Nat.mul_lt_mul_of_pos_left hlt hr
      _ ≤ Z₀.relIndex U * U.index * Nat.card H := by
        rw [mul_assoc]
        exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hi)

theorem Setting29.ale_of_restrict {𝒦 : HostClass} {H S : Subgroup (MulAut V)}
    {Z₀ : Subgroup V} (h : Setting29 𝒦 H S Z₀) {X : Subgroup (MulAut V)} {U : Subgroup V}
    (hSX : S ≤ X) (hXH : X ≤ H) (hZU : Z₀ ≤ U) (hXU : X ≤ stabSub U)
    (hgen : ∀ W : Subgroup V, (∀ x ∈ X, Z₀.map x.toMonoidHom ≤ W) → U ≤ W) (hU1 : ALe S U 1)
    (ih : Setting29 𝒦 (autSub X U) (autSub S U) (Z₀.subgroupOf U) →
      ALe (autSub S U) ⊤ 1 → ALe (autSub S U) (Z₀.subgroupOf U) 1) : ALe S Z₀ 1 := by
  have hSU : S ≤ stabSub U := hSX.trans hXU
  have h1 : ALe (autSub S U) ⊤ 1 := by
    rw [← Subgroup.subgroupOf_self U]
    exact (ale_autSub_iff hSU le_rfl).mpr hU1
  exact (ale_autSub_iff hSU hZU).mp (ih (h.restrict hSX hXH hZU hXU hgen) h1)

end Setting

section JSV

variable [Finite V]

@[expose] def IsMinOff0 (S A : Subgroup (MulAut V)) : Prop :=
  IsMinOff S A ⊤ ∧ ∀ B, IsMinOff S B ⊤ → Nat.card A ≤ Nat.card B

@[expose] def jSV (S : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  ⨆ (A : Subgroup (MulAut V)) (_ : IsMinOff0 S A), A

theorem le_jSV {S A : Subgroup (MulAut V)} (hA : IsMinOff0 S A) : A ≤ jSV S :=
  le_iSup₂ (f := fun A (_ : IsMinOff0 S A) => A) A hA

theorem le_fixV_jSV {S : Subgroup (MulAut V)} {Z : Subgroup V}
    (h : ∀ A, IsMinOff0 S A → Z ≤ fixV A) : Z ≤ fixV (jSV S) := by
  intro v hv g hg
  have hle : jSV S ≤ MulAction.stabilizer (MulAut V) v :=
    iSup₂_le fun A hA a ha => MulAction.mem_stabilizer_iff.mpr (h A hA hv a ha)
  exact MulAction.mem_stabilizer_iff.mp (hle hg)

theorem map_conj_map_conj_inv (g : MulAut V) (B : Subgroup (MulAut V)) :
    (B.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = B := by
  rw [Subgroup.map_map]
  have : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom = MonoidHom.id _ := by
    ext x v
    simp
  rw [this, Subgroup.map_id]

theorem map_conj_inv_map_conj (g : MulAut V) (B : Subgroup (MulAut V)) :
    (B.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = B := by
  simpa using map_conj_map_conj_inv g⁻¹ B

theorem dimOn_map_conj_top (g : MulAut V) (B : Subgroup (MulAut V)) :
    dimOn (B.map (MulAut.conj g).toMonoidHom) ⊤ = dimOn B ⊤ := by
  have := dimOn_map_conj g B ⊤
  rwa [Subgroup.map_top_of_surjective _ g.surjective] at this

theorem codimOn_map_conj_top (g : MulAut V) (B : Subgroup (MulAut V)) :
    codimOn (B.map (MulAut.conj g).toMonoidHom) ⊤ = codimOn B ⊤ := by
  have := codimOn_map_conj g B ⊤
  rwa [Subgroup.map_top_of_surjective _ g.surjective] at this

theorem IsOff.map_conj {S B : Subgroup (MulAut V)} (h : IsOff S B ⊤) (g : MulAut V) :
    IsOff (S.map (MulAut.conj g).toMonoidHom) (B.map (MulAut.conj g).toMonoidHom) ⊤ := by
  refine ⟨Subgroup.map_mono h.1, fun hle => h.2.1 ?_, ?_⟩
  · rw [fixV_map_conj] at hle
    intro v _
    obtain ⟨w, hw, hwv⟩ := hle (Subgroup.mem_top (g v))
    have : w = v := g.injective hwv
    rw [← this]
    exact hw
  · have hel := elemAbOn_top_iff.mp h.2.2
    refine elemAbOn_top_iff.mpr ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ by group, hel.1 a ha b hb]
      group
    · rintro _ ⟨a, ha, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [conj_pow, hel.2 a ha]
      group

theorem IsMinOff.map_conj {S B : Subgroup (MulAut V)} (h : IsMinOff S B ⊤) (g : MulAut V) :
    IsMinOff (S.map (MulAut.conj g).toMonoidHom) (B.map (MulAut.conj g).toMonoidHom) ⊤ := by
  refine ⟨h.1.map_conj g, fun C hC => ?_⟩
  have hC' := hC.map_conj g⁻¹
  rw [map_conj_inv_map_conj] at hC'
  have h1 := h.2 _ hC'
  rw [codimOn_map_conj_top g⁻¹ C, dimOn_map_conj_top g⁻¹ C] at h1
  rw [dimOn_map_conj_top, codimOn_map_conj_top]
  exact h1

theorem IsMinOff0.map_conj {S B : Subgroup (MulAut V)} (h : IsMinOff0 S B) (g : MulAut V) :
    IsMinOff0 (S.map (MulAut.conj g).toMonoidHom) (B.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨h.1.map_conj g, fun C hC => ?_⟩
  have hC' := hC.map_conj g⁻¹
  rw [map_conj_inv_map_conj] at hC'
  have h1 := h.2 _ hC'
  have e1 : Nat.card ↥(B.map (MulAut.conj g).toMonoidHom) = Nat.card B :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have e2 : Nat.card ↥(C.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card C :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  rw [e1]
  rw [e2] at h1
  exact h1

theorem map_conj_eq_of_mem_normalizer {S : Subgroup (MulAut V)} {g : MulAut V}
    (hg : g ∈ Subgroup.normalizer (S : Set (MulAut V))) : S.map (MulAut.conj g).toMonoidHom = S := by
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg s).mp hs
  · intro ht
    have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) t).mp ht
    refine ⟨g⁻¹ * t * g⁻¹⁻¹, h1, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem mem_normalizer_jSV {S : Subgroup (MulAut V)} {g : MulAut V}
    (hg : g ∈ Subgroup.normalizer (S : Set (MulAut V))) :
    g ∈ Subgroup.normalizer (jSV S : Set (MulAut V)) := by
  have key : ∀ g ∈ Subgroup.normalizer (S : Set (MulAut V)),
      (jSV S).map (MulAut.conj g).toMonoidHom ≤ jSV S := by
    intro g hg
    rw [jSV, Subgroup.map_iSup]
    refine iSup_le fun A => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hA => ?_
    have := hA.map_conj g
    rw [map_conj_eq_of_mem_normalizer hg] at this
    exact le_jSV this
  rw [Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · intro ht
    exact key g hg ⟨t, ht, rfl⟩
  · intro ht
    have := key g⁻¹ (Subgroup.inv_mem _ hg) ⟨_, ht, rfl⟩
    rwa [show (MulAut.conj g⁻¹).toMonoidHom (g * t * g⁻¹) = t by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group] at this

theorem IsMinOff.of_ratio_le {S A B : Subgroup (MulAut V)} (hS : IsPGroup 2 S)
    (hA : IsMinOff S A ⊤) (hB : IsOff S B ⊤)
    (hBA : codimOn B ⊤ * dimOn A ⊤ ≤ codimOn A ⊤ * dimOn B ⊤) : IsMinOff S B ⊤ := by
  refine ⟨hB, fun C hC => ?_⟩
  have h2 := hA.2 C hC
  have hd : 0 < dimOn A ⊤ := hA.1.dimOn_pos hS
  have key : codimOn B ⊤ * dimOn C ⊤ * dimOn A ⊤ ≤ codimOn C ⊤ * dimOn B ⊤ * dimOn A ⊤ := by
    nlinarith [Nat.mul_le_mul_right (dimOn C ⊤) hBA, Nat.mul_le_mul_right (dimOn B ⊤) h2]
  exact Nat.le_of_mul_le_mul_right key hd

theorem isMinOff0_iff_of_le {S T : Subgroup (MulAut V)} (hS : IsPGroup 2 S) (hTS : T ≤ S)
    (hT : ∀ A, IsMinOff0 S A → A ≤ T) {A₀ : Subgroup (MulAut V)} (hA₀ : IsMinOff0 S A₀)
    (A : Subgroup (MulAut V)) : IsMinOff0 T A ↔ IsMinOff0 S A := by
  have hT2 : IsPGroup 2 T := hS.to_le hTS
  have back : ∀ A, IsMinOff0 S A → IsMinOff0 T A := by
    intro A hA
    refine ⟨⟨⟨hT A hA, hA.1.1.2⟩, fun C hC => hA.1.2 C ⟨hC.1.trans hTS, hC.2⟩⟩, fun B hB => ?_⟩
    have hBA := hB.2 A ⟨hT A hA, hA.1.1.2⟩
    exact hA.2 B (hA.1.of_ratio_le hS ⟨hB.1.1.trans hTS, hB.1.2⟩ hBA)
  refine ⟨fun hA => ⟨?_, fun B hB => ?_⟩, back A⟩
  · have hAA₀ := hA.1.2 A₀ ⟨hT A₀ hA₀, hA₀.1.1.2⟩
    exact hA₀.1.of_ratio_le hS ⟨hA.1.1.1.trans hTS, hA.1.1.2⟩ hAA₀
  · exact (hA.2 A₀ (back A₀ hA₀).1).trans (hA₀.2 B hB)

theorem jSV_eq_of_le {S T : Subgroup (MulAut V)} (hS : IsPGroup 2 S) (hTS : T ≤ S)
    (hT : ∀ A, IsMinOff0 S A → A ≤ T) {A₀ : Subgroup (MulAut V)} (hA₀ : IsMinOff0 S A₀) :
    jSV T = jSV S := by
  apply le_antisymm
  · exact iSup₂_le fun A hA => le_jSV ((isMinOff0_iff_of_le hS hTS hT hA₀ A).mp hA)
  · exact iSup₂_le fun A hA => le_jSV ((isMinOff0_iff_of_le hS hTS hT hA₀ A).mpr hA)

theorem exists_mul_of_frattini {H S D : Subgroup (MulAut V)} (hSH : S ≤ H) (hS : IsPGroup 2 S)
    (hSi : ¬ 2 ∣ S.relIndex H) (hDH : D ≤ H) (hDn : ∀ h ∈ H, ∀ d ∈ D, h * d * h⁻¹ ∈ D)
    {h : MulAut V} (hh : h ∈ H) :
    ∃ n ∈ H, n ∈ Subgroup.normalizer ((S ⊓ D : Subgroup (MulAut V)) : Set (MulAut V)) ∧
      ∃ d ∈ D, h = n * d := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S' := S.subgroupOf H with hS'
  set D' := D.subgroupOf H with hD'
  haveI hD'n : D'.Normal := ⟨fun d hd g => by
    rw [hD', Subgroup.mem_subgroupOf] at hd ⊢
    exact hDn g g.2 d hd⟩
  have hS'i : ¬ 2 ∣ S'.index := hSi
  have hS'2 : IsPGroup 2 S' := hS.comap_subtype
  have hi : ¬ 2 ∣ ((S' ⊓ D').subgroupOf D').index := by
    change ¬ 2 ∣ (S' ⊓ D').relIndex D'
    rw [Subgroup.inf_relIndex_right, ← relIndex_sup_of_normal S' D']
    exact fun hd => hS'i (hd.trans (Subgroup.relIndex_dvd_index_of_le le_sup_left))
  have hp : IsPGroup 2 ((S' ⊓ D').subgroupOf D') := hS'2.to_inf_left.comap_subtype
  have hF := Sylow.normalizer_sup_eq_top (hp.toSylow hi)
  rw [IsPGroup.toSylow_coe, Subgroup.subgroupOf_map_subtype, inf_of_le_left inf_le_right] at hF
  have hmem : (⟨h, hh⟩ : H) ∈ Subgroup.normalizer ((S' ⊓ D' : Subgroup H) : Set H) ⊔ D' := by
    rw [hF]
    exact Subgroup.mem_top _
  obtain ⟨n', hn', d', hd', hnd⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
  refine ⟨n', n'.2, ?_, d', hd', (congrArg Subtype.val hnd).symm⟩
  rw [Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · rintro ⟨htS, htD⟩
    have := (Subgroup.mem_normalizer_iff.mp hn' ⟨t, hSH htS⟩).mp ⟨htS, htD⟩
    exact ⟨this.1, this.2⟩
  · intro ht
    have htH : t ∈ H := by
      have h1 : t = (n' : MulAut V)⁻¹ * ((n' : MulAut V) * t * (n' : MulAut V)⁻¹) * n' := by group
      rw [h1]
      exact H.mul_mem (H.mul_mem (H.inv_mem n'.2) (hSH ht.1)) n'.2
    have := (Subgroup.mem_normalizer_iff.mp hn' ⟨t, htH⟩).mpr ⟨ht.1, ht.2⟩
    exact ⟨this.1, this.2⟩

theorem exists_isMinOff0_not_mem {H S : Subgroup (MulAut V)} {Z₀ : Subgroup V} (hSH : S ≤ H)
    (hS : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.relIndex H)
    (hJ : H ⊓ Subgroup.normalizer (jSV S : Set (MulAut V)) ≤ stabSub Z₀)
    (hH : ¬ H ≤ stabSub Z₀) {A₀ : Subgroup (MulAut V)} (hA₀ : IsMinOff0 S A₀) :
    ∃ A, IsMinOff0 S A ∧ ∃ h ∈ H, ∃ a ∈ A, h * a * h⁻¹ ∉ H ⊓ stabSub Z₀ := by
  by_contra hcon
  push Not at hcon
  let D : Subgroup (MulAut V) :=
    { carrier := {g | g ∈ H ∧ ∀ h ∈ H, h * g * h⁻¹ ∈ H ⊓ stabSub Z₀}
      one_mem' := ⟨H.one_mem, fun h _ => by simp [Subgroup.one_mem]⟩
      mul_mem' := by
        rintro a b ⟨haH, ha⟩ ⟨hbH, hb⟩
        refine ⟨H.mul_mem haH hbH, fun h hh => ?_⟩
        have e : h * (a * b) * h⁻¹ = (h * a * h⁻¹) * (h * b * h⁻¹) := by group
        rw [e]
        exact Subgroup.mul_mem _ (ha h hh) (hb h hh)
      inv_mem' := by
        rintro a ⟨haH, ha⟩
        refine ⟨H.inv_mem haH, fun h hh => ?_⟩
        have e : h * a⁻¹ * h⁻¹ = (h * a * h⁻¹)⁻¹ := by group
        rw [e]
        exact Subgroup.inv_mem _ (ha h hh) }
  have hDH : D ≤ H := fun g hg => hg.1
  have hDM : D ≤ H ⊓ stabSub Z₀ := fun g hg => by
    have := hg.2 1 H.one_mem
    simpa using this
  have hDn : ∀ h ∈ H, ∀ d ∈ D, h * d * h⁻¹ ∈ D := by
    rintro h hh d ⟨hdH, hd⟩
    refine ⟨H.mul_mem (H.mul_mem hh hdH) (H.inv_mem hh), fun h' hh' => ?_⟩
    have e : h' * (h * d * h⁻¹) * h'⁻¹ = (h' * h) * d * (h' * h)⁻¹ := by group
    rw [e]
    exact hd _ (H.mul_mem hh' hh)
  have hT : ∀ A, IsMinOff0 S A → A ≤ S ⊓ D := fun A hA a ha =>
    ⟨hA.1.1.1 ha, hSH (hA.1.1.1 ha), fun h hh => hcon A hA h hh a ha⟩
  have hjeq : jSV (S ⊓ D) = jSV S := jSV_eq_of_le hS inf_le_left hT hA₀
  apply hH
  intro h hh
  obtain ⟨n, hnH, hnN, d, hd, rfl⟩ := exists_mul_of_frattini hSH hS hSi hDH hDn hh
  have hnJ : n ∈ Subgroup.normalizer (jSV S : Set (MulAut V)) := by
    rw [← hjeq]
    exact mem_normalizer_jSV hnN
  exact (stabSub Z₀).mul_mem (hJ ⟨hnH, hnJ⟩) (hDM hd).2

end JSV

section Main

variable [Finite V]

theorem index_mul_card_lt_of_lt {Z₀ Z₁ : Subgroup V} (h : Z₀ < Z₁) (H : Subgroup (MulAut V)) :
    Z₁.index * Nat.card H < Z₀.index * Nat.card H := by
  have h2 := Subgroup.relIndex_mul_index h.le
  have hr : Z₀.relIndex Z₁ ≠ 1 := fun h1 => h.not_ge (Subgroup.relIndex_eq_one.mp h1)
  have hr0 : Z₀.relIndex Z₁ ≠ 0 := relIndex_ne_zero_of_finite _ _
  have hi : 0 < Z₁.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hH : 0 < Nat.card H := Nat.card_pos
  rw [← h2]
  have : Z₁.index < Z₀.relIndex Z₁ * Z₁.index := by
    have : 2 ≤ Z₀.relIndex Z₁ := by omega
    nlinarith
  exact Nat.mul_lt_mul_of_pos_right this hH

end Main

@[expose] def Hyp29 (𝒦 : HostClass) : Prop :=
  ∀ (V : Type u) [CommGroup V] [Finite V] (H S A : Subgroup (MulAut V)) (Z₀ : Subgroup V),
    Setting29 𝒦 H S Z₀ → IsCoatom ((H ⊓ stabSub Z₀).subgroupOf H) → A ≤ S →
    CFSG.Open.IsElemAbelian 2 A → (∃ h ∈ H, ∃ a ∈ A, h * a * h⁻¹ ∉ H ⊓ stabSub Z₀) →
    IsQuadratic A → Z₀ ≤ fixV A → IsMinOff S A ⊤ → codimOn A ⊤ ≤ dimOn A ⊤ → AGt S Z₀ 1 →
    (∃ L ≤ H, IsL24 S (H ⊓ stabSub Z₀) A L) ∨ ALe S Z₀ 1

theorem ale_of_ale_aux {𝒦 : HostClass} (h24 : Hyp29.{u} 𝒦) (n : ℕ) :
    ∀ (V : Type u) [CommGroup V] [Finite V] (H S : Subgroup (MulAut V)) (Z₀ : Subgroup V),
      Z₀.index * Nat.card H = n → Setting29 𝒦 H S Z₀ → ALe S ⊤ 1 → ALe S Z₀ 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ H S Z₀ hn hset hV1
  have hV := hset.sq
  have hS := hset.isPGroup
  by_contra hZ
  rw [not_ale_iff] at hZ
  have hZtop : Z₀ ≠ ⊤ := by
    rintro rfl
    exact not_ale_iff.mpr hZ hV1
  obtain ⟨B, hB, hBle⟩ := id hV1
  obtain ⟨A₀, hA₀, hA₀min⟩ := exists_isMinOff_card hS hB
  have hA₀0 : IsMinOff0 S A₀ := ⟨hA₀, hA₀min⟩
  have hle1 : ∀ A, IsMinOff S A ⊤ → codimOn A ⊤ ≤ dimOn A ⊤ := by
    intro A hA
    have h1 := hA.2 B hB
    have hBd : 0 < dimOn B ⊤ := hB.dimOn_pos hS
    have hBle' : codimOn B ⊤ ≤ dimOn B ⊤ := by
      rw [one_mul] at hBle
      exact_mod_cast hBle
    have : codimOn A ⊤ * dimOn B ⊤ ≤ dimOn A ⊤ * dimOn B ⊤ := by nlinarith
    exact Nat.le_of_mul_le_mul_right this hBd
  have hZA : ∀ A, IsMinOff S A ⊤ → Z₀ ≤ fixV A := by
    intro A hA
    by_contra hnot
    refine not_ale_iff.mpr hZ (ale_of_isMinOff hV hS hA le_top hnot hA.1.1 ?_)
    rw [one_mul]
    exact_mod_cast hle1 A hA
  have hSM₀ : S ≤ H ⊓ Subgroup.normalizer (jSV S : Set (MulAut V)) :=
    le_inf hset.le fun s hs => mem_normalizer_jSV (Subgroup.le_normalizer hs)
  have hZJ : Z₀ ≤ fixV (jSV S) := le_fixV_jSV fun A hA => hZA A hA.1
  obtain ⟨Z₁, hZ₁⟩ : ∃ Z₁ : Subgroup V,
      Z₁ = spanOrbit (H ⊓ Subgroup.normalizer (jSV S : Set (MulAut V))) Z₀ := ⟨_, rfl⟩
  have hZZ₁ : Z₀ ≤ Z₁ := hZ₁ ▸ le_spanOrbit _ _
  have hM₀Z₁ : H ⊓ Subgroup.normalizer (jSV S : Set (MulAut V)) ≤ stabSub Z₁ :=
    hZ₁ ▸ le_stabSub_spanOrbit _ _
  have hgen₁ : ∀ W : Subgroup V, (∀ x ∈ H ⊓ Subgroup.normalizer (jSV S : Set (MulAut V)),
      Z₀.map x.toMonoidHom ≤ W) → Z₁ ≤ W := fun W hW => hZ₁ ▸ spanOrbit_le hW
  have hZ₁J : Z₁ ≤ fixV (jSV S) := by
    rw [hZ₁]
    refine spanOrbit_le fun m hm => ?_
    rintro _ ⟨z, hz, rfl⟩ j hj
    have hj' : m⁻¹ * j * m ∈ jSV S := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hm.2) j).mp hj
      rwa [inv_inv] at this
    have h1 : (m⁻¹ * j * m) z = z := hZJ hz _ hj'
    simp only [MulAut.mul_apply] at h1
    have h2 := congrArg m h1
    simpa using h2
  have hZ₁top : Z₁ ≠ ⊤ := by
    intro htop
    apply hA₀.1.2.1
    exact (htop ▸ hZ₁J).trans (fixV_le_fixV_of_le (le_jSV hA₀0))
  have hZ₁eq : Z₁ = Z₀ := by
    by_contra hne
    have hlt : Z₀ < Z₁ := lt_of_le_of_ne hZZ₁ (Ne.symm hne)
    have h1 : ALe S Z₁ 1 := ih _ (hn ▸ index_mul_card_lt_of_lt hlt H) V H S Z₁ rfl
      (hset.mono hZZ₁ (hSM₀.trans hM₀Z₁)) hV1
    exact not_ale_iff.mpr hZ (hset.ale_of_restrict hSM₀ inf_le_left hZZ₁ hM₀Z₁ hgen₁ h1
      fun hs h1' => ih _ (hn ▸ index_mul_card_autSub_lt hZZ₁ inf_le_left hM₀Z₁
        (Or.inl hZ₁top)) _ _ _ _ rfl hs h1')
  rw [hZ₁eq] at hM₀Z₁
  have hSM : S ≤ H ⊓ stabSub Z₀ := le_inf hset.le hset.stab
  have hHZ : ¬ H ≤ stabSub Z₀ := by
    intro hle
    apply hZtop
    rw [eq_top_iff]
    exact hset.gen Z₀ fun h hh => (map_eq_self_of_mem_stabSub (hle hh)).le
  have hcoatom : IsCoatom ((H ⊓ stabSub Z₀).subgroupOf H) := by
    refine ⟨fun htop => hHZ fun h hh => ?_, fun K hK => ?_⟩
    · have : (⟨h, hh⟩ : H) ∈ (H ⊓ stabSub Z₀).subgroupOf H := htop ▸ Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp this).2
    · by_contra hKtop
      obtain ⟨H₀, hH₀⟩ : ∃ H₀ : Subgroup (MulAut V), H₀ = K.map H.subtype := ⟨_, rfl⟩
      have hH₀H : H₀ ≤ H := hH₀ ▸ Subgroup.map_subtype_le K
      have hMH₀ : H ⊓ stabSub Z₀ ≤ H₀ := by
        intro g hg
        rw [hH₀]
        exact ⟨⟨g, hg.1⟩, hK.le (Subgroup.mem_subgroupOf.mpr hg), rfl⟩
      have hH₀ne : H₀ ≠ H := by
        intro heq
        apply hKtop
        rw [eq_top_iff]
        intro h _
        have : (h : MulAut V) ∈ H₀ := heq ▸ h.2
        rw [hH₀] at this
        obtain ⟨k, hk, hkh⟩ := this
        rwa [show k = h from Subtype.ext hkh] at hk
      obtain ⟨k, hkK, hkM⟩ := SetLike.exists_of_lt hK
      have hkZ : (k : MulAut V) ∉ stabSub Z₀ := fun h =>
        hkM (Subgroup.mem_subgroupOf.mpr ⟨k.2, h⟩)
      have hkH₀ : (k : MulAut V) ∈ H₀ := hH₀ ▸ ⟨k, hkK, rfl⟩
      obtain ⟨Z₂, hZ₂⟩ : ∃ Z₂ : Subgroup V, Z₂ = spanOrbit H₀ Z₀ := ⟨_, rfl⟩
      have hZZ₂ : Z₀ ≤ Z₂ := hZ₂ ▸ le_spanOrbit _ _
      have hH₀Z₂ : H₀ ≤ stabSub Z₂ := hZ₂ ▸ le_stabSub_spanOrbit _ _
      have hgen₂ : ∀ W : Subgroup V, (∀ x ∈ H₀, Z₀.map x.toMonoidHom ≤ W) → Z₂ ≤ W :=
        fun W hW => hZ₂ ▸ spanOrbit_le hW
      have hlt : Z₀ < Z₂ := by
        refine lt_of_le_of_ne hZZ₂ fun heq => hkZ ?_
        rw [heq]
        exact hH₀Z₂ hkH₀
      have h1 : ALe S Z₂ 1 := ih _ (hn ▸ index_mul_card_lt_of_lt hlt H) V H S Z₂ rfl
        (hset.mono hZZ₂ ((hSM.trans hMH₀).trans hH₀Z₂)) hV1
      exact not_ale_iff.mpr hZ (hset.ale_of_restrict (hSM.trans hMH₀) hH₀H hZZ₂ hH₀Z₂ hgen₂ h1
        fun hs h1' => ih _ (hn ▸ index_mul_card_autSub_lt hZZ₂ hH₀H hH₀Z₂ (Or.inr hH₀ne))
          _ _ _ _ rfl hs h1')
  obtain ⟨A, hA, h, hh, a, haA, hha⟩ :=
    exists_isMinOff0_not_mem hset.le hS hset.not_dvd hM₀Z₁ hHZ hA₀0
  have hq : IsQuadratic A := isQuadratic_of_isMinOff hV hS hA.1 (hle1 A hA.1) hA.2
  have hel := elemAbOn_top_iff.mp hA.1.1.2.2
  have hAel : CFSG.Open.IsElemAbelian 2 A := isElemAbelian_of_forall hel.1 hel.2
  rcases h24 V H S A Z₀ hset hcoatom hA.1.1.1 hAel ⟨h, hh, a, haA, hha⟩ hq (hZA A hA.1) hA.1
      (hle1 A hA.1) hZ with ⟨L, hLH, hL⟩ | hle
  ·
    have hS3 := IsSym3Free.forall_inv_eq_one hset.sym3Free
    have hAU : codimOn A (spanOrbit L Z₀) ≤ dimOn A (spanOrbit L Z₀) := by
      have h1 := codimOn_mul_le_of_isMinOff hV hS hA.1 (le_top : spanOrbit L Z₀ ≤ ⊤)
      have hd : 0 < dimOn A ⊤ := hA.1.1.dimOn_pos hS
      have h2 := hle1 A hA.1
      have : codimOn A (spanOrbit L Z₀) * dimOn A ⊤ ≤ dimOn A (spanOrbit L Z₀) * dimOn A ⊤ :=
        h1.trans (Nat.mul_le_mul_left _ h2)
      exact Nat.le_of_mul_le_mul_right this hd
    exact false_of_isL24 hV hS hSM inf_le_right (fun g hg => ⟨hLH hg.1, hg.2⟩) hAel hq
      (hZA A hA.1) hZ hL (fun a ha y hy => hS3 a (hLH ha) y (hLH hy)) (le_spanOrbit L Z₀)
      (le_stabSub_spanOrbit L Z₀) (fun W hW => spanOrbit_le hW) hAU
  · exact not_ale_iff.mpr hZ hle

theorem ale_of_ale {𝒦 : HostClass} (h24 : Hyp29.{u} 𝒦) {V : Type u} [CommGroup V] [Finite V]
    {H S : Subgroup (MulAut V)} {Z₀ : Subgroup V} (hset : Setting29 𝒦 H S Z₀)
    (hV1 : ALe S ⊤ 1) : ALe S Z₀ 1 :=
  ale_of_ale_aux h24 _ V H S Z₀ rfl hset hV1

end CFSG.RankThree.S4Free.Stell
