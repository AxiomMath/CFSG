module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL4Wr
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL4Ext

public section

namespace CFSG.Quasithin.F6.GoldAmL4

variable {E : Type*} [Group E]

structure TRel (a b s : E) : Prop where
  ha : a ^ 4 = 1
  hb : b ^ 4 = 1
  hs : s ^ 2 = 1
  hab : a * b = b * a
  hsa : s * a * s = b
  hsb : s * b * s = a

structure ARel (a b s x : E) : Prop extends TRel a b s where
  hx : x ^ 3 = 1
  hxa : x⁻¹ * a * x = b
  hxb : x⁻¹ * b * x = a⁻¹ * b⁻¹
  hxs : x * s * x = s

structure BConj (a b s y : E) : Prop extends TRel a b s where
  hy : y ^ 3 = 1
  hyc : y⁻¹ * (a * b) * y = a * b
  hyp : y⁻¹ * (a * a) * y = s
  hyq : y⁻¹ * s * y = a * b⁻¹ * s

structure BRel (a b s y : E) : Prop extends BConj a b s y where
  hyt : y * (s * a) * y = s * a

theorem BRel.toTRel' {a b s y : E} (h : BRel a b s y) : TRel a b s := h.toBConj.toTRel

theorem tcRel : TRel tA tB tS where
  ha := tA_pow_four
  hb := tB_pow_four
  hs := tS_sq
  hab := tA_mul_tB
  hsa := tS_tA_tS
  hsb := tS_tB_tS

namespace TRel

variable {a b s : E} (h : TRel a b s)

include h

theorem ss : s * s = 1 := by rw [← pow_two]; exact h.hs

theorem s_inv : s⁻¹ = s := by
  rw [inv_eq_iff_mul_eq_one]; exact h.ss

theorem pow_a (n : ℕ) : a ^ (n % 4) = a ^ n := (pow_eq_pow_mod n h.ha).symm

theorem pow_b (n : ℕ) : b ^ (n % 4) = b ^ n := (pow_eq_pow_mod n h.hb).symm

theorem pow_s (n : ℕ) : s ^ (n % 2) = s ^ n := (pow_eq_pow_mod n h.hs).symm

theorem comm_pow (m n : ℕ) : b ^ n * a ^ m = a ^ m * b ^ n :=
  ((Commute.pow_pow (show Commute a b from h.hab) m n).eq).symm

theorem s_a_pow (n : ℕ) : s * a ^ n * s = b ^ n := by
  induction n with
  | zero => simp [h.ss]
  | succ n ih =>
    calc s * a ^ (n + 1) * s = (s * a ^ n * s) * (s * a * s) := by
          rw [pow_succ]; simp only [mul_assoc]
          rw [← mul_assoc s s, h.ss, one_mul]
      _ = b ^ (n + 1) := by rw [ih, h.hsa, pow_succ]

theorem s_b_pow (n : ℕ) : s * b ^ n * s = a ^ n := by
  induction n with
  | zero => simp [h.ss]
  | succ n ih =>
    calc s * b ^ (n + 1) * s = (s * b ^ n * s) * (s * b * s) := by
          rw [pow_succ]; simp only [mul_assoc]
          rw [← mul_assoc s s, h.ss, one_mul]
      _ = a ^ (n + 1) := by rw [ih, h.hsb, pow_succ]

theorem s_swap (k l : ℕ) : s * (a ^ k * b ^ l) * s = b ^ k * a ^ l := by
  calc s * (a ^ k * b ^ l) * s = (s * a ^ k * s) * (s * b ^ l * s) := by
        simp only [mul_assoc]
        rw [← mul_assoc s s, h.ss, one_mul]
    _ = b ^ k * a ^ l := by rw [h.s_a_pow, h.s_b_pow]

theorem word_mul (i j k l : ℕ) : (a ^ i * b ^ j) * (a ^ k * b ^ l) = a ^ (i + k) * b ^ (j + l) := by
  calc a ^ i * b ^ j * (a ^ k * b ^ l) = a ^ i * (b ^ j * a ^ k) * b ^ l := by
        simp only [mul_assoc]
    _ = a ^ i * (a ^ k * b ^ j) * b ^ l := by rw [h.comm_pow]
    _ = a ^ (i + k) * b ^ (j + l) := by rw [pow_add, pow_add]; simp only [mul_assoc]

theorem s_swap' (k l : ℕ) : s * (a ^ k * b ^ l) = (a ^ l * b ^ k) * s := by
  have h1 := h.s_swap k l
  have h2 : s * (a ^ k * b ^ l) = s * (a ^ k * b ^ l) * s * s := by
    rw [mul_assoc _ s s, h.ss, mul_one]
  rw [h2, h1, h.comm_pow]

end TRel

namespace TRel

variable {a b s : E}

@[expose] def embFun (a b s : E) (x : Tc) : E := a ^ x.i.val * b ^ x.j.val * s ^ x.e.val

variable (h : TRel a b s)

include h

theorem embFun_mul (x y : Tc) : embFun a b s (x * y) = embFun a b s x * embFun a b s y := by
  obtain ⟨i, j, e⟩ := x
  obtain ⟨k, l, f⟩ := y
  have hi4 : ∀ m n : Fin 4, a ^ (m + n).val = a ^ m.val * a ^ n.val := fun m n => by
    rw [Fin.val_add, h.pow_a, pow_add]
  have hj4 : ∀ m n : Fin 4, b ^ (m + n).val = b ^ m.val * b ^ n.val := fun m n => by
    rw [Fin.val_add, h.pow_b, pow_add]
  have hss : s * s = 1 := h.ss
  have hw : ∀ i j k l : Fin 4, a ^ (i + k).val * b ^ (j + l).val =
      (a ^ i.val * b ^ j.val) * (a ^ k.val * b ^ l.val) := fun i j k l => by
    rw [Fin.val_add, Fin.val_add, h.pow_a, h.pow_b, ← h.word_mul]
  fin_cases e <;> fin_cases f <;> simp only [embFun, Tc.mul_def] <;> simp
  · rw [hw]
  · rw [hw, mul_assoc]
  · calc a ^ (i + l).val * b ^ (j + k).val * s
        = (a ^ i.val * b ^ j.val) * (a ^ l.val * b ^ k.val) * s := by rw [hw]
      _ = a ^ i.val * b ^ j.val * ((a ^ l.val * b ^ k.val) * s) := by rw [mul_assoc]
      _ = a ^ i.val * b ^ j.val * (s * (a ^ k.val * b ^ l.val)) := by rw [h.s_swap']
      _ = a ^ i.val * b ^ j.val * s * (a ^ k.val * b ^ l.val) := by simp only [mul_assoc]
  · calc a ^ (i + l).val * b ^ (j + k).val
        = (a ^ i.val * b ^ j.val) * (a ^ l.val * b ^ k.val) := by rw [hw]
      _ = a ^ i.val * b ^ j.val * (s * (a ^ k.val * b ^ l.val) * s) := by
          rw [h.s_swap k.val l.val, h.comm_pow]
      _ = a ^ i.val * b ^ j.val * s * (a ^ k.val * b ^ l.val * s) := by
          simp only [mul_assoc]

end TRel

namespace TRel

variable {a b s : E} (h : TRel a b s)

include h

@[expose] def emb : Tc →* E where
  toFun := embFun a b s
  map_one' := by
    show a ^ (0 : Fin 4).val * b ^ (0 : Fin 4).val * s ^ (0 : Fin 2).val = 1
    simp
  map_mul' := h.embFun_mul

theorem emb_apply (x : Tc) : h.emb x = a ^ x.i.val * b ^ x.j.val * s ^ x.e.val := rfl

theorem emb_tA : h.emb tA = a := by
  rw [emb_apply]; simp [tA]

theorem emb_tB : h.emb tB = b := by
  rw [emb_apply]; simp [tB]

theorem emb_tS : h.emb tS = s := by
  rw [emb_apply]; simp [tS]

theorem emb_range : h.emb.range = Subgroup.closure ({a, b, s} : Set E) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [emb_apply]
    have ha : a ∈ Subgroup.closure ({a, b, s} : Set E) := Subgroup.subset_closure (by simp)
    have hb : b ∈ Subgroup.closure ({a, b, s} : Set E) := Subgroup.subset_closure (by simp)
    have hs : s ∈ Subgroup.closure ({a, b, s} : Set E) := Subgroup.subset_closure (by simp)
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ ha _)
      (Subgroup.pow_mem _ hb _)) (Subgroup.pow_mem _ hs _)
  · rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact ⟨tA, h.emb_tA⟩
    · exact ⟨tB, h.emb_tB⟩
    · exact ⟨tS, h.emb_tS⟩

theorem emb_injective (hcard : Nat.card (Subgroup.closure ({a, b, s} : Set E)) = 32) :
    Function.Injective h.emb := by
  have hsurj : Function.Surjective h.emb.rangeRestrict := MonoidHom.rangeRestrict_surjective _
  have hfin : Finite h.emb.range := Finite.of_surjective _ hsurj
  have hcard' : Nat.card Tc ≤ Nat.card h.emb.range := by
    rw [h.emb_range, hcard, card_Tc]
  have hbij := hsurj.bijective_of_nat_card_le hcard'
  intro x y hxy
  exact hbij.1 (Subtype.ext hxy)

theorem T_pow32 {t : E} (ht : t ∈ Subgroup.closure ({a, b, s} : Set E)) : t ^ 32 = 1 := by
  rw [← h.emb_range] at ht
  obtain ⟨w, rfl⟩ := ht
  rw [← map_pow, tc_pow32, map_one]

theorem eq_one_of_pow_three {y : E} (hy : y ^ 3 = 1)
    (hmem : y ∈ Subgroup.closure ({a, b, s} : Set E)) : y = 1 := by
  have h32 := h.T_pow32 hmem
  have h1 : orderOf y ∣ 32 := orderOf_dvd_of_pow_eq_one h32
  have h2 : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one hy
  have h3 : orderOf y ∣ Nat.gcd 32 3 := Nat.dvd_gcd h1 h2
  have : Nat.gcd 32 3 = 1 := by norm_num
  rw [this, Nat.dvd_one, orderOf_eq_one_iff] at h3
  exact h3

theorem emb_tC : h.emb tC = a * b := by rw [tC_eq, map_mul, h.emb_tA, h.emb_tB]

theorem emb_tP : h.emb tP = a * a := by rw [tP_eq, map_mul, h.emb_tA]

theorem emb_tT0 : h.emb tT0 = s * a := by rw [tT0_eq, map_mul, h.emb_tS, h.emb_tA]

theorem emb_alpha : h.emb (⟨1, 3, 1⟩ : Tc) = a * b⁻¹ * s := by
  rw [tc_alpha0, map_mul, map_mul, map_inv, h.emb_tA, h.emb_tB, h.emb_tS]

end TRel

namespace TRel

variable {a b s : E} (h : TRel a b s)

include h

open Classical in
noncomputable def coord : E → Tc := Function.invFun h.emb

theorem coord_emb (hinj : Function.Injective h.emb) (x : Tc) : h.coord (h.emb x) = x :=
  Function.leftInverse_invFun hinj x

theorem emb_coord {d : E} (hd : d ∈ h.emb.range) : h.emb (h.coord d) = d :=
  Function.invFun_eq (by simpa using hd)

theorem coord_mul (hinj : Function.Injective h.emb) {t₁ t₂ : E} (h₁ : t₁ ∈ h.emb.range)
    (h₂ : t₂ ∈ h.emb.range) : h.coord (t₁ * t₂) = h.coord t₁ * h.coord t₂ := by
  apply hinj
  rw [map_mul, h.emb_coord h₁, h.emb_coord h₂, h.emb_coord (h.emb.range.mul_mem h₁ h₂)]

end TRel

namespace ARel

variable {a b s x : E} (hA : ARel a b s x)

include hA

theorem conj_emb (w : Tc) (hw : w ∈ baseSub) :
    x⁻¹ * hA.toTRel.emb w * x = hA.toTRel.emb (xAct w) := by
  have hT := hA.toTRel
  obtain ⟨i, j, e⟩ := w
  have he : e = 0 := mem_baseSub.mp hw
  subst he
  have hconj : ∀ (g : E) (n : ℕ), x⁻¹ * g ^ n * x = (x⁻¹ * g * x) ^ n := fun g n => by
    have := conj_pow (a := x⁻¹) (b := g) (i := n)
    simpa using this.symm
  rw [hT.emb_apply, xAct_eq]
  show x⁻¹ * (a ^ i.val * b ^ j.val * s ^ (0 : Fin 2).val) * x = _
  simp only [Fin.val_zero, pow_zero, mul_one]
  calc x⁻¹ * (a ^ i.val * b ^ j.val) * x
      = (x⁻¹ * a ^ i.val * x) * (x⁻¹ * b ^ j.val * x) := by group
    _ = (x⁻¹ * a * x) ^ i.val * (x⁻¹ * b * x) ^ j.val := by rw [hconj, hconj]
    _ = b ^ i.val * (a⁻¹ * b⁻¹) ^ j.val := by rw [hA.hxa, hA.hxb]
    _ = hT.emb (tB ^ i.val * (tA⁻¹ * tB⁻¹) ^ j.val) := by
        simp [map_mul, map_pow, map_inv, hT.emb_tA, hT.emb_tB]

end ARel

namespace BConj

variable {a b s y : E} (hB : BConj a b s y)

include hB

theorem conj_emb (w : Tc) (hw : w ∈ m2Sub) :
    y⁻¹ * hB.toTRel.emb w * y = hB.toTRel.emb (Fu alpha0 w) := by
  have hT := hB.toTRel
  let κ : E →* E := (MulAut.conj y⁻¹).toMonoidHom
  have hκ : ∀ g, κ g = y⁻¹ * g * y := fun g => by
    show y⁻¹ * g * y⁻¹⁻¹ = _
    rw [inv_inv]
  have hmul : ∀ u v : E, κ (u * v) = κ u * κ v := map_mul κ
  have hemul : ∀ u v : Tc, hT.emb (u * v) = hT.emb u * hT.emb v := map_mul hT.emb
  have e1 : hT.emb tC = a * b := by rw [tC_eq, map_mul, hT.emb_tA, hT.emb_tB]
  have e2 : hT.emb tP = a * a := by rw [tP_eq, map_mul, hT.emb_tA]
  have e3 : hT.emb (⟨1, 3, 1⟩ : Tc) = a * b⁻¹ * s := by
    rw [tc_alpha0, map_mul, map_mul, map_inv, hT.emb_tA, hT.emb_tB, hT.emb_tS]
  have hk1 : κ (a * b) = a * b := by rw [hκ]; exact hB.hyc
  have hk2 : κ (a * a) = s := by rw [hκ]; exact hB.hyp
  have hk3 : κ s = a * b⁻¹ * s := by rw [hκ]; exact hB.hyq
  have hspec : w = tC ^ (nfOf w).1 * evalFrom tP tS 1 (nfOf w).2 := nf_spec w hw
  have key : ∀ (k : ℕ) (wd : List Bool), y⁻¹ * hT.emb (tC ^ k * evalFrom tP tS 1 wd) * y =
      (a * b) ^ k * evalFrom s (a * b⁻¹ * s) 1 wd := by
    intro k wd
    rw [← hκ]
    rw [map_mul, map_pow, map_evalFrom hT.emb hemul tP tS wd 1, e1, e2, hT.emb_tS, map_one]
    rw [map_mul, map_pow, map_evalFrom κ hmul (a * a) s wd 1, hk1, hk2, hk3, map_one]
  have hL : y⁻¹ * hT.emb w * y = (a * b) ^ (nfOf w).1 *
      evalFrom s (a * b⁻¹ * s) 1 (nfOf w).2 := by
    have := key (nfOf w).1 (nfOf w).2
    rwa [← hspec] at this
  have hR : hT.emb (Fu alpha0 w) = (a * b) ^ (nfOf w).1 *
      evalFrom s (a * b⁻¹ * s) 1 (nfOf w).2 := by
    unfold Fu alpha0
    show hT.emb (tC ^ (nfOf w).1 * evalFrom tS ⟨1, 3, 1⟩ 1 (nfOf w).2) = _
    rw [map_mul, map_pow, map_evalFrom hT.emb hemul tS ⟨1, 3, 1⟩ (nfOf w).2 1, e1, hT.emb_tS,
      e3, map_one]
  rw [hL, hR]

end BConj

section Vertex

variable {E' : Type*} [Group E']

structure VertexSpec {a b s : E} (hT : TRel a b s) (Qc : Subgroup Tc) (t₀c : Tc) (y : E)
    (act : Tc → Tc) (u₁ u₂ : Tc) : Prop where
  y_cube : y ^ 3 = 1
  y_ne : y ≠ 1
  act_mem : ∀ w ∈ Qc, act w ∈ Qc
  conj : ∀ w ∈ Qc, y⁻¹ * hT.emb w * y = hT.emb (act w)
  t₁ : y * hT.emb t₀c * y = hT.emb u₁
  t₂ : y⁻¹ * hT.emb t₀c * y⁻¹ = hT.emb u₂

namespace VertexSpec

variable {a b s y : E} {hT : TRel a b s} {Qc : Subgroup Tc} {t₀c : Tc} {act : Tc → Tc}
  {u₁ u₂ : Tc} (hv : VertexSpec hT Qc t₀c y act u₁ u₂)

include hv

theorem y_not_mem : y ∉ hT.emb.range := by
  intro hy
  rw [hT.emb_range] at hy
  have h32 := hT.T_pow32 hy
  apply hv.y_ne
  have h1 : orderOf y ∣ 32 := orderOf_dvd_of_pow_eq_one h32
  have h2 : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one hv.y_cube
  have h3 : orderOf y ∣ Nat.gcd 32 3 := Nat.dvd_gcd h1 h2
  have : Nat.gcd 32 3 = 1 := by norm_num
  rw [this, Nat.dvd_one, orderOf_eq_one_iff] at h3
  exact h3

theorem yy : y * y = y⁻¹ := by
  rw [eq_inv_iff_mul_eq_one]
  calc y * y * y = y ^ 3 := by rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two]
    _ = 1 := hv.y_cube

theorem yy' : y⁻¹ * y⁻¹ = y := by
  have := congrArg Inv.inv hv.yy
  simpa using this

theorem conj_pos {w : Tc} (hw : w ∈ Qc) :
    y * hT.emb w * y⁻¹ = hT.emb (act (act w)) := by
  have e1 := hv.conj w hw
  have e2 := hv.conj _ (hv.act_mem w hw)
  calc y * hT.emb w * y⁻¹ = (y⁻¹ * y⁻¹) * hT.emb w * (y * y) := by rw [hv.yy', hv.yy]
    _ = y⁻¹ * (y⁻¹ * hT.emb w * y) * y := by group
    _ = hT.emb (act (act w)) := by rw [e1, e2]

theorem ext3Data (hQ : ∀ w : Tc, w ∈ Qc ∨ w * t₀c⁻¹ ∈ Qc) :
    Ext3Data hT.emb.range (Qc.map hT.emb) y (hT.emb t₀c) := by
  have hconj' : ∀ q ∈ Qc.map hT.emb, y⁻¹ * q * y ∈ Qc.map hT.emb := by
    intro q hq
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hq
    rw [hv.conj w hw]
    exact Subgroup.mem_map_of_mem _ (hv.act_mem w hw)
  refine ⟨Subgroup.map_le_range _ _, hv.y_cube, hv.y_not_mem, ⟨t₀c, rfl⟩, ?_, ?_, hconj', ?_, ?_⟩
  · rintro t ⟨w, rfl⟩
    rcases hQ w with hw | hw
    · exact Or.inl (Subgroup.mem_map_of_mem _ hw)
    · refine Or.inr ?_
      rw [← map_inv, ← map_mul]
      exact Subgroup.mem_map_of_mem _ hw
  · intro q hq
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hq
    rw [hv.conj_pos hw]
    exact Subgroup.mem_map_of_mem _ (hv.act_mem _ (hv.act_mem w hw))
  · rw [hv.t₁]; exact ⟨u₁, rfl⟩
  · rw [hv.t₂]; exact ⟨u₂, rfl⟩

end VertexSpec

namespace VertexSpec

variable {a b s y : E} {hT : TRel a b s} {Qc : Subgroup Tc} {t₀c : Tc} {act : Tc → Tc}
  {u₁ u₂ : Tc} {a' b' s' : E'} {y' : E'} {hT' : TRel a' b' s'}

theorem ext3Compat (hinj : Function.Injective hT.emb) (hinj' : Function.Injective hT'.emb)
    (hv : VertexSpec hT Qc t₀c y act u₁ u₂) (hv' : VertexSpec hT' Qc t₀c y' act u₁ u₂) :
    Ext3Compat hT.emb.range (Qc.map hT.emb) hT'.emb.range y (hT.emb t₀c) y'
      (fun d => hT'.emb (hT.coord d)) := by
  have hι : ∀ x : Tc, hT'.emb (hT.coord (hT.emb x)) = hT'.emb x := fun x => by
    rw [hT.coord_emb hinj]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t₁ h₁ t₂ h₂
    show hT'.emb (hT.coord (t₁ * t₂)) = hT'.emb (hT.coord t₁) * hT'.emb (hT.coord t₂)
    rw [hT.coord_mul hinj h₁ h₂, map_mul]
  · intro t _
    exact ⟨hT.coord t, rfl⟩
  · intro t₁ h₁ t₂ h₂ e
    have e' : hT.coord t₁ = hT.coord t₂ := hinj' e
    rw [← hT.emb_coord h₁, ← hT.emb_coord h₂, e']
  · rintro _ ⟨x, rfl⟩
    exact ⟨hT.emb x, ⟨x, rfl⟩, hι x⟩
  · intro q hq
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hq
    show hT'.emb (hT.coord (y * hT.emb w * y⁻¹)) = y' * hT'.emb (hT.coord (hT.emb w)) * y'⁻¹
    rw [hv.conj_pos hw, hι, hι, hv'.conj_pos hw]
  · show hT'.emb (hT.coord (y * hT.emb t₀c * y)) = y' * hT'.emb (hT.coord (hT.emb t₀c)) * y'
    rw [hv.t₁, hι, hι, hv'.t₁]
  · show hT'.emb (hT.coord (y⁻¹ * hT.emb t₀c * y⁻¹)) =
      y'⁻¹ * hT'.emb (hT.coord (hT.emb t₀c)) * y'⁻¹
    rw [hv.t₂, hι, hι, hv'.t₂]

theorem vertex_iso (hinj : Function.Injective hT.emb) (hinj' : Function.Injective hT'.emb)
    (hQ : ∀ w : Tc, w ∈ Qc ∨ w * t₀c⁻¹ ∈ Qc)
    (hv : VertexSpec hT Qc t₀c y act u₁ u₂) (hv' : VertexSpec hT' Qc t₀c y' act u₁ u₂) :
    ∃ φ : ↥(Subgroup.closure ((hT.emb.range : Set E) ∪ {y})) ≃*
        ↥(Subgroup.closure ((hT'.emb.range : Set E') ∪ {y'})),
      (∀ w : Tc, ((φ ⟨hT.emb w, Subgroup.subset_closure (Or.inl ⟨w, rfl⟩)⟩ :
        ↥(Subgroup.closure ((hT'.emb.range : Set E') ∪ {y'}))) : E') = hT'.emb w) ∧
      ((φ ⟨y, Subgroup.subset_closure (Or.inr rfl)⟩ :
        ↥(Subgroup.closure ((hT'.emb.range : Set E') ∪ {y'}))) : E') = y' := by
  obtain ⟨φ, hφ, hφy⟩ := (hv.ext3Data hQ).exists_mulEquiv (hv.ext3Compat hinj hinj' hv')
    hv'.y_cube hv'.y_not_mem
  refine ⟨φ, fun w => ?_, hφy⟩
  rw [hφ _ ⟨w, rfl⟩]
  show hT'.emb (hT.coord (hT.emb w)) = hT'.emb w
  rw [hT.coord_emb hinj]

end VertexSpec

end Vertex

namespace ARel

variable {a b s x : E} (hA : ARel a b s x)

include hA

theorem vertexSpec (hinj : Function.Injective hA.toTRel.emb) :
    VertexSpec hA.toTRel baseSub tS x xAct tS tS := by
  have hT := hA.toTRel
  refine ⟨hA.hx, ?_, xAct_mem, hA.conj_emb, ?_, ?_⟩
  · intro hx1
    have h1 := hA.hxa
    rw [hx1] at h1
    simp only [inv_one, one_mul, mul_one] at h1
    apply tA_ne_tB
    apply hinj
    rw [hT.emb_tA, hT.emb_tB]
    exact h1
  · rw [hT.emb_tS]; exact hA.hxs
  · rw [hT.emb_tS]
    calc x⁻¹ * s * x⁻¹ = x⁻¹ * (x * s * x) * x⁻¹ := by rw [hA.hxs]
      _ = s := by group

end ARel

namespace BRel

variable {a b s y : E} (hB : BRel a b s y)

include hB

theorem vertexSpec (hinj : Function.Injective hB.toTRel'.emb) :
    VertexSpec hB.toTRel' m2Sub tT0 y (Fu alpha0) tT0 tT0 := by
  have hT := hB.toTRel'
  have hconj : ∀ w ∈ m2Sub, y⁻¹ * hT.emb w * y = hT.emb (Fu alpha0 w) := hB.toBConj.conj_emb
  have e0 : hT.emb tT0 = s * a := by rw [tT0_eq, map_mul, hT.emb_tS, hT.emb_tA]
  refine ⟨hB.hy, ?_, Fu_alpha0_mem, hconj, ?_, ?_⟩
  · intro hy1
    have h1 := hB.hyp
    rw [hy1] at h1
    simp only [inv_one, one_mul, mul_one] at h1
    apply tP_ne_tS
    apply hinj
    rw [tP_eq, map_mul, hT.emb_tA, hT.emb_tS]
    exact h1
  · rw [e0]; exact hB.hyt
  · rw [e0]
    calc y⁻¹ * (s * a) * y⁻¹ = y⁻¹ * (y * (s * a) * y) * y⁻¹ := by rw [hB.hyt]
      _ = s * a := by group

end BRel

theorem TRel.of_relators {a b s : E} (R1 : a * a * a * a = 1) (R2 : b * b * b * b = 1)
    (R3 : s * s = 1) (R4 : a⁻¹ * b⁻¹ * a * b = 1) (R5 : s * a * s * b⁻¹ = 1)
    (R6 : s * b * s * a⁻¹ = 1) : TRel a b s where
  ha := by simpa [pow_succ, mul_assoc] using R1
  hb := by simpa [pow_succ, mul_assoc] using R2
  hs := by rw [pow_two]; exact R3
  hab := by
    calc a * b = b * a * (a⁻¹ * b⁻¹ * a * b) := by group
      _ = b * a := by rw [R4, mul_one]
  hsa := mul_inv_eq_one.mp R5
  hsb := mul_inv_eq_one.mp R6

theorem ARel.of_relators {a b s x : E} (hT : TRel a b s) (R1 : x * x * x = 1)
    (R2 : x⁻¹ * a * x * b⁻¹ = 1) (R3 : x⁻¹ * b * x * b * a = 1) (R4 : x * s * x * s = 1) :
    ARel a b s x where
  toTRel := hT
  hx := by rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two]; exact R1
  hxa := mul_inv_eq_one.mp R2
  hxb := by
    have h : x⁻¹ * b * x * (b * a) = 1 := by rw [← R3]; group
    rw [eq_inv_of_mul_eq_one_left h, mul_inv_rev]
  hxs := by
    have h := eq_inv_of_mul_eq_one_left R4
    rwa [hT.s_inv] at h

theorem BRel.of_relators {a b s y : E} (hT : TRel a b s) (R1 : y * y * y = 1)
    (R2 : y⁻¹ * a * b * s * y * s * a * a = 1) (R3 : y⁻¹ * s * a * a * y * b * a⁻¹ = 1)
    (R4 : a⁻¹ * s * y * s * a * y = 1) : BRel a b s y := by
  have hs : s⁻¹ = s := hT.s_inv
  have hyt : y * (s * a) * y = s * a := by
    have h : (a⁻¹ * s) * (y * (s * a) * y) = 1 := by rw [← R4]; group
    have h2 := eq_inv_of_mul_eq_one_right h
    rw [mul_inv_rev, hs, inv_inv] at h2
    exact h2
  have hb2 : (s * a) * (s * a) = a * b := by
    calc (s * a) * (s * a) = (s * a * s) * a := by group
      _ = b * a := by rw [hT.hsa]
      _ = a * b := hT.hab.symm
  have E1 : (s * a) * y = y⁻¹ * (s * a) := by
    calc (s * a) * y = y⁻¹ * (y * (s * a) * y) := by group
      _ = y⁻¹ * (s * a) := by rw [hyt]
  have hyc : y⁻¹ * (a * b) * y = a * b := by
    calc y⁻¹ * (a * b) * y = y⁻¹ * ((s * a) * (s * a)) * y := by rw [hb2]
      _ = (y⁻¹ * (s * a)) * ((s * a) * y) := by group
      _ = ((s * a) * y) * ((s * a) * y) := by rw [← E1]
      _ = (s * a) * (y * (s * a) * y) := by group
      _ = (s * a) * (s * a) := by rw [hyt]
      _ = a * b := hb2
  have ha3 : a⁻¹ * a⁻¹ * a⁻¹ = a := by
    have h4 : a * a * a * a = 1 := by simpa [pow_succ, mul_assoc] using hT.ha
    calc a⁻¹ * a⁻¹ * a⁻¹ = (a⁻¹ * a⁻¹ * a⁻¹) * (a * a * a * a) := by rw [h4, mul_one]
      _ = a := by group
  have hab' : b⁻¹ * a = a * b⁻¹ := by
    calc b⁻¹ * a = b⁻¹ * (a * b) * b⁻¹ := by group
      _ = b⁻¹ * (b * a) * b⁻¹ := by rw [hT.hab]
      _ = a * b⁻¹ := by group
  have hyq : y⁻¹ * s * y = a * b⁻¹ * s := by
    have hu : (a * b) * (y⁻¹ * s * y) * (s * a * a) = 1 := by
      calc (a * b) * (y⁻¹ * s * y) * (s * a * a)
          = (y⁻¹ * (a * b) * y) * (y⁻¹ * s * y) * (s * a * a) := by rw [hyc]
        _ = y⁻¹ * a * b * s * y * s * a * a := by group
        _ = 1 := R2
    calc y⁻¹ * s * y = (a * b)⁻¹ * ((a * b) * (y⁻¹ * s * y) * (s * a * a)) * (s * a * a)⁻¹ := by
          group
      _ = (a * b)⁻¹ * (s * a * a)⁻¹ := by rw [hu]; group
      _ = b⁻¹ * (a⁻¹ * a⁻¹ * a⁻¹) * s⁻¹ := by group
      _ = b⁻¹ * a * s := by rw [ha3, hs]
      _ = a * b⁻¹ * s := by rw [hab']
  have hyp : y⁻¹ * (a * a) * y = s := by
    have hv : (a * b⁻¹ * s) * (y⁻¹ * (a * a) * y) * (b * a⁻¹) = 1 := by
      rw [← hyq]
      calc y⁻¹ * s * y * (y⁻¹ * (a * a) * y) * (b * a⁻¹) = y⁻¹ * s * a * a * y * b * a⁻¹ := by
            group
        _ = 1 := R3
    calc y⁻¹ * (a * a) * y = (a * b⁻¹ * s)⁻¹ * ((a * b⁻¹ * s) * (y⁻¹ * (a * a) * y) *
          (b * a⁻¹)) * (b * a⁻¹)⁻¹ := by group
      _ = (a * b⁻¹ * s)⁻¹ * (b * a⁻¹)⁻¹ := by rw [hv]; group
      _ = s⁻¹ := by group
      _ = s := hs
  exact ⟨⟨hT, by rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two]; exact R1, hyc, hyp, hyq⟩,
    hyt⟩

namespace BRel

variable {a b s y : E} (hB : BRel a b s y)

theorem ne_one (hinj : Function.Injective hB.toTRel'.emb) : y ≠ 1 := by
  intro hy1
  have h1 := hB.hyp
  rw [hy1] at h1
  simp only [inv_one, one_mul, mul_one] at h1
  apply tP_ne_tS
  apply hinj
  rw [hB.toTRel'.emb_tP, hB.toTRel'.emb_tS]
  exact h1

end BRel

end CFSG.Quasithin.F6.GoldAmL4
