module

public import CFSG.Quasithin.Background.SmithD37Cent
public import CFSG.Quasithin.Background.SmithD37Diag
public import CFSG.Quasithin.Background.SmithD37Num

public section

namespace CFSG.Quasithin.SmithD37

variable {U : Type} [CommGroup U] {L₁ L₂ : Subgroup (MulAut U)}

theorem mem_normalizer_iff_map_eq {a : MulAut U} {L : Subgroup (MulAut U)} :
    a ∈ Subgroup.normalizer (L : Set (MulAut U)) ↔ L.map (MulAut.conj a).toMonoidHom = L := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (h y).1 hy
    · intro hx
      refine ⟨a⁻¹ * x * a, (h _).2 ?_, by group⟩
      rwa [show a * (a⁻¹ * x * a) * a⁻¹ = x by group]
  · intro h y
    constructor
    · intro hy
      rw [← h]
      exact ⟨y, hy, rfl⟩
    · intro hy
      rw [← h] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hzy
      have : z = y := by
        have := congrArg (fun w => a⁻¹ * w * a) hzy
        simpa [mul_assoc] using this
      exact this ▸ hz

theorem mul_mem_of_mem_normalizer {a l : MulAut U} {L : Subgroup (MulAut U)}
    (ha : a ∈ Subgroup.normalizer (L : Set (MulAut U))) (hl : l ∈ L) : a * l * a⁻¹ ∈ L :=
  (Subgroup.mem_normalizer_iff.mp ha l).1 hl

theorem mem_fixV_zpowers_iff {t : MulAut U} {u : U} :
    u ∈ fixV (Subgroup.zpowers t) ↔ t u = u :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem MatModel.not_comm {F : Type} [Field F] {d : ℕ} (Mm : MatModel L₁ L₂ F d) (hd : 2 ≤ d) :
    ∃ x y : ↥L₁, x * y ≠ y * x := by
  by_contra h
  push Not at h
  let S := Set.range fun l : ↥L₁ =>
    ((Mm.R₁ l : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F)
  have hS : ∀ M ∈ S, ∀ N ∈ S, M * N = N * M := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← Matrix.GeneralLinearGroup.coe_mul, ← map_mul, h, map_mul,
      Matrix.GeneralLinearGroup.coe_mul]
  have hspan : ∀ M ∈ Submodule.span F S, ∀ N ∈ Submodule.span F S, M * N = N * M := by
    intro M hM N hN
    induction hN using Submodule.span_induction with
    | mem N hN' =>
      induction hM using Submodule.span_induction with
      | mem M hM' => exact hS M hM' N hN'
      | zero => simp
      | add a b _ _ ha hb => rw [add_mul, mul_add, ha, hb]
      | smul c a _ ha => rw [smul_mul_assoc, mul_smul_comm, ha]
    | zero => simp
    | add a b _ _ ha hb => rw [add_mul, mul_add, ha, hb]
    | smul c a _ ha => rw [smul_mul_assoc, mul_smul_comm, ha]
  have hall : ∀ M N : Matrix (Fin d) (Fin d) F, M * N = N * M := fun M N =>
    hspan M (Mm.span₁ ▸ Submodule.mem_top) N (Mm.span₁ ▸ Submodule.mem_top)
  let i : Fin d := ⟨0, by omega⟩
  let j : Fin d := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
  have h1 := congrFun (congrFun (hall (Matrix.single i j 1) (Matrix.single j i 1)) i) i
  simp [Matrix.mul_apply, Matrix.single_apply, hij.symm] at h1

theorem conj_mul_toMonoidHom (a t : MulAut U) :
    (MulAut.conj (a * t)).toMonoidHom =
      (MulAut.conj a).toMonoidHom.comp (MulAut.conj t).toMonoidHom := by
  ext x : 1
  simp [mul_assoc]

theorem map_conj_mul (L : Subgroup (MulAut U)) (a t : MulAut U) :
    L.map (MulAut.conj (a * t)).toMonoidHom =
      (L.map (MulAut.conj t).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map, conj_mul_toMonoidHom]

theorem commute_of_swap {a t : MulAut U} (ht₂ : ∀ k ∈ L₂, t * k * t⁻¹ ∈ L₁)
    (hat : a * t = t * a) (hc : ∀ l ∈ L₁, a * l = l * a) : ∀ k ∈ L₂, a * k = k * a := by
  intro k hk
  have hat' : Commute a t := hat
  have hk' : k = t⁻¹ * (t * k * t⁻¹) * t := by group
  rw [hk']
  exact ((hat'.inv_right).mul_right (hc _ (ht₂ k hk))).mul_right hat'

section Core

variable [Finite U] {X : Subgroup (MulAut U)} {s : MulAut U}

theorem Core.ne_bot (hC : Core X L₁ L₂ s) : L₁ ≠ ⊥ := by
  have := hC.simple
  have : Nontrivial ↥L₁ := IsSimpleGroup.toNontrivial
  exact (Subgroup.nontrivial_iff_ne_bot L₁).mp this

theorem Core.not_mem_normalizer (hC : Core X L₁ L₂ s) {t : MulAut U}
    (ht₁ : L₁.map (MulAut.conj t).toMonoidHom = L₂) :
    t ∉ Subgroup.normalizer (L₁ : Set (MulAut U)) := by
  intro htN
  rw [mem_normalizer_iff_map_eq, ht₁] at htN
  apply hC.ne_bot
  rw [← inf_idem L₁]
  nth_rewrite 2 [← htN]
  exact hC.inf

theorem Core.swap_of_not_mem (hC : Core X L₁ L₂ s) {x : MulAut U} (hx : x ∈ X)
    (hxN : x ∉ Subgroup.normalizer (L₁ : Set (MulAut U))) :
    L₁.map (MulAut.conj x).toMonoidHom = L₂ ∧ L₂.map (MulAut.conj x).toMonoidHom = L₁ := by
  rcases hC.perm x hx with h | h
  · exact absurd (mem_normalizer_iff_map_eq.mpr h.1) hxN
  · exact h

theorem Core.mem_normalizer₂ (hC : Core X L₁ L₂ s) {x : MulAut U} (hx : x ∈ X)
    (hxN : x ∈ Subgroup.normalizer (L₁ : Set (MulAut U))) :
    x ∈ Subgroup.normalizer (L₂ : Set (MulAut U)) := by
  rw [mem_normalizer_iff_map_eq] at hxN ⊢
  rcases hC.perm x hx with h | h
  · exact h.2
  · exact absurd (hxN.symm.trans h.1) (hC.not_mem_normalizer h.1 ∘ fun h' =>
      mem_normalizer_iff_map_eq.mpr (h.1.trans h'.symm))

theorem Core.mul_mem_normalizer (hC : Core X L₁ L₂ s) {a t : MulAut U} (ha : a ∈ X) (ht : t ∈ X)
    (haN : a ∉ Subgroup.normalizer (L₁ : Set (MulAut U)))
    (htN : t ∉ Subgroup.normalizer (L₁ : Set (MulAut U))) :
    a * t ∈ Subgroup.normalizer (L₁ : Set (MulAut U)) := by
  rw [mem_normalizer_iff_map_eq, map_conj_mul, (hC.swap_of_not_mem ht htN).1,
    (hC.swap_of_not_mem ha haN).2]

theorem Core.card_eq_two_mul (hC : Core X L₁ L₂ s) {A : Subgroup (MulAut U)} (hAX : A ≤ X)
    {t : MulAut U} (htA : t ∈ A) (htN : t ∉ Subgroup.normalizer (L₁ : Set (MulAut U))) :
    Nat.card A = 2 * Nat.card ↥(A ⊓ Subgroup.normalizer (L₁ : Set (MulAut U))) := by
  set N := Subgroup.normalizer (L₁ : Set (MulAut U))
  have hidx : ((A ⊓ N).subgroupOf A).index = 2 := by
    refine Subgroup.index_eq_two_iff.mpr ⟨⟨t, htA⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.mem_inf,
      A.mul_mem b.2 htA, b.2, true_and]
    by_cases hb : (b : MulAut U) ∈ N
    · refine Or.inr ⟨hb, fun hbt => htN ?_⟩
      have := N.mul_mem (N.inv_mem hb) hbt
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
    · exact Or.inl ⟨hC.mul_mem_normalizer (hAX b.2) (hAX htA) hb htN, hb⟩
  have h1 := ((A ⊓ N).subgroupOf A).card_mul_index
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h1
  omega

end Core

section Bound

variable [Finite U] {X : Subgroup (MulAut U)} {s : MulAut U} {F : Type} [Field F] [Fintype F]
  [CharP F 2] {d : ℕ}

theorem three_le_choose (hd : 3 ≤ d) : 3 ≤ d * (d - 1) / 2 := by
  have h : 6 ≤ d * (d - 1) := by
    calc 6 = 3 * 2 := by norm_num
      _ ≤ d * (d - 1) := Nat.mul_le_mul hd (by omega)
  omega

theorem out_bound (hC : Core X L₁ L₂ s) (Mm : MatModel L₁ L₂ F d) (hd : 3 ≤ d)
    {A : Subgroup (MulAut U)} (hA2 : IsA2 X A) (hAr : rAV A ≤ 2) {t : MulAut U} (htA : t ∈ A)
    (ht₁ : L₁.map (MulAut.conj t).toMonoidHom = L₂)
    (ht₂ : L₂.map (MulAut.conj t).toMonoidHom = L₁) :
    A ⊓ Subgroup.normalizer (L₁ : Set (MulAut U)) ≠ ⊥ ∧
      Nat.card F ^ (d * (d - 1) / 2) ≤
        2 * Nat.card ↥(A ⊓ Subgroup.normalizer (L₁ : Set (MulAut U))) ^ 2 := by
  set A₀ := A ⊓ Subgroup.normalizer (L₁ : Set (MulAut U)) with hA₀
  have hexp := hC.exp
  have ht : t * t = 1 := by rw [← pow_two]; exact hA2.2.2.2 t htA
  have htN := hC.not_mem_normalizer ht₁
  have hcardA := hC.card_eq_two_mul hA2.1 htA htN
  have hflip := card_fixV_swap_le Mm t ht ht₁ ht₂
  have hle : fixV A ≤ fixV (Subgroup.zpowers t) := fixV_anti (Subgroup.zpowers_le.mpr htA)
  have hr := card_le_sq_mul_fixV hexp hA2 hAr
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hk := three_le_choose hd
  have hq8 : 8 ≤ Nat.card F ^ (d * (d - 1) / 2) :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ Nat.card F ^ 3 := Nat.pow_le_pow_left hq 3
      _ ≤ Nat.card F ^ (d * (d - 1) / 2) := Nat.pow_le_pow_right (by omega) hk
  have hpos : 0 < Nat.card (fixV A) := Nat.card_pos
  have hpos' : 0 < Nat.card (fixV (Subgroup.zpowers t)) := Nat.card_pos
  have hsw₁ : ∀ l ∈ L₁, t * l * t⁻¹ ∈ L₂ := fun l hl => by
    rw [← ht₁]
    exact ⟨l, hl, rfl⟩
  have hsw₂ : ∀ k ∈ L₂, t * k * t⁻¹ ∈ L₁ := fun k hk => by
    rw [← ht₂]
    exact ⟨k, hk, rfl⟩
  by_cases hA0 : A₀ = ⊥
  · exfalso
    have h1 : Nat.card A₀ = 1 := by rw [hA0]; exact Subgroup.card_bot
    have hCt : Nat.card (fixV A) ≤ Nat.card (fixV (Subgroup.zpowers t)) :=
      Subgroup.card_le_of_le hle
    have h2 : Nat.card F ^ (d * (d - 1) / 2) * Nat.card (fixV (Subgroup.zpowers t)) ≤
        4 * Nat.card (fixV (Subgroup.zpowers t)) :=
      calc _ ≤ Nat.card U := hflip
        _ ≤ Nat.card A ^ 2 * Nat.card (fixV A) := hr
        _ = 4 * Nat.card (fixV A) := by rw [hcardA, h1]; ring
        _ ≤ 4 * Nat.card (fixV (Subgroup.zpowers t)) := Nat.mul_le_mul_left _ hCt
    have := Nat.le_of_mul_le_mul_right h2 hpos'
    omega
  · refine ⟨hA0, ?_⟩
    obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA0
    have haA : (a : MulAut U) ∈ A := a.2.1
    have haN : (a : MulAut U) ∈ Subgroup.normalizer (L₁ : Set (MulAut U)) := a.2.2
    have hne : fixV A ≠ fixV (Subgroup.zpowers t) := by
      intro heq
      apply ha1
      have hat : (a : MulAut U) * t = t * a := hA2.2.2.1 _ haA _ htA
      have hfix : ∀ u, t u = u → (a : MulAut U) u = u := by
        intro u hu
        have hu' : u ∈ fixV A := heq ▸ mem_fixV_zpowers_iff.mpr hu
        exact hu' _ haA
      have := hC.simple
      have hc₁ := commute_of_fix_t ht hC.comm hsw₁ hexp hC.inf (Mm.not_comm (by omega)) hat
        (fun l hl => mul_mem_of_mem_normalizer haN hl) hfix
      have hc₂ := commute_of_swap hsw₂ hat hc₁
      have h1 := eq_one_of_comm Mm hc₁ hc₂ (e := 1) (by rw [pow_one]; exact hA2.2.2.2 _ haA)
      exact Subtype.ext h1
    have h2 : 2 * Nat.card (fixV A) ≤ Nat.card (fixV (Subgroup.zpowers t)) := by
      obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hle
      rcases Nat.lt_or_ge c 2 with hc2 | hc2
      · exfalso
        interval_cases c
        · omega
        · apply hne
          exact Subgroup.eq_of_le_of_card_ge hle (by omega)
      · rw [hc]
        calc 2 * Nat.card (fixV A) = Nat.card (fixV A) * 2 := by ring
          _ ≤ Nat.card (fixV A) * c := Nat.mul_le_mul_left _ hc2
    have h3 : Nat.card F ^ (d * (d - 1) / 2) * 2 * Nat.card (fixV A) ≤
        4 * Nat.card A₀ ^ 2 * Nat.card (fixV A) :=
      calc _ = Nat.card F ^ (d * (d - 1) / 2) * (2 * Nat.card (fixV A)) := by ring
        _ ≤ Nat.card F ^ (d * (d - 1) / 2) * Nat.card (fixV (Subgroup.zpowers t)) :=
          Nat.mul_le_mul_left _ h2
        _ ≤ Nat.card U := hflip
        _ ≤ Nat.card A ^ 2 * Nat.card (fixV A) := hr
        _ = 4 * Nat.card A₀ ^ 2 * Nat.card (fixV A) := by rw [hcardA]; ring
    have := Nat.le_of_mul_le_mul_right h3 hpos
    omega

end Bound

end CFSG.Quasithin.SmithD37
