module

public import CFSG.Quasithin.EmptyFaithful.R3c23Def
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

namespace R3c23

section Decomposition

variable {V : Type} [CommGroup V]

theorem exists_decomp {G₁ G₂ : Subgroup (MulAut V)} (hcomm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a)
    {x : MulAut V} (hx : x ∈ G₁ ⊔ G₂) : ∃ a ∈ G₁, ∃ b ∈ G₂, x = a * b := by
  let S : Subgroup (MulAut V) :=
    { carrier := {x | ∃ a ∈ G₁, ∃ b ∈ G₂, x = a * b}
      one_mem' := ⟨1, G₁.one_mem, 1, G₂.one_mem, (mul_one 1).symm⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', G₁.mul_mem ha ha', b * b', G₂.mul_mem hb hb', ?_⟩
        have hc := hcomm a' ha' b hb
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [hc]
          _ = a * a' * (b * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, G₁.inv_mem ha, b⁻¹, G₂.inv_mem hb, ?_⟩
        rw [mul_inv_rev, hcomm a⁻¹ (G₁.inv_mem ha) b⁻¹ (G₂.inv_mem hb)] }
  have hle : G₁ ⊔ G₂ ≤ S := sup_le (fun a ha => ⟨a, ha, 1, G₂.one_mem, (mul_one a).symm⟩)
    (fun b hb => ⟨1, G₁.one_mem, b, hb, (one_mul b).symm⟩)
  exact hle hx

theorem decomp_unique {G₁ G₂ : Subgroup (MulAut V)} (hbot : G₁ ⊓ G₂ = ⊥)
    {a a' b b' : MulAut V} (ha : a ∈ G₁) (ha' : a' ∈ G₁) (hb : b ∈ G₂) (hb' : b' ∈ G₂)
    (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have hmem : a'⁻¹ * a ∈ G₁ ⊓ G₂ :=
    ⟨G₁.mul_mem (G₁.inv_mem ha') ha, by rw [h1]; exact G₂.mul_mem hb' (G₂.inv_mem hb)⟩
  rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  subst hmem
  exact ⟨rfl, mul_left_cancel h⟩

theorem prod_mul_prod {G₁ G₂ : Subgroup (MulAut V)} (hcomm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a)
    {x x' y y' : MulAut V} (hx' : x' ∈ G₁) (hy : y ∈ G₂) :
    x * y * (x' * y') = x * x' * (y * y') := by
  have hc := hcomm x' hx' y hy
  calc x * y * (x' * y') = x * (y * x') * y' := by group
    _ = x * (x' * y) * y' := by rw [hc]
    _ = x * x' * (y * y') := by group

end Decomposition

section Projection

variable {V : Type} [CommGroup V]

def projSub (G H A : Subgroup (MulAut V)) (hcomm : ∀ a ∈ G, ∀ b ∈ H, a * b = b * a) :
    Subgroup (MulAut V) where
  carrier := {x | x ∈ G ∧ ∃ y ∈ H, x * y ∈ A}
  one_mem' := ⟨G.one_mem, 1, H.one_mem, by rw [mul_one]; exact A.one_mem⟩
  mul_mem' := by
    rintro x x' ⟨hx, y, hy, hxy⟩ ⟨hx', y', hy', hxy'⟩
    refine ⟨G.mul_mem hx hx', y * y', H.mul_mem hy hy', ?_⟩
    rw [← prod_mul_prod hcomm hx' hy]
    exact A.mul_mem hxy hxy'
  inv_mem' := by
    rintro x ⟨hx, y, hy, hxy⟩
    refine ⟨G.inv_mem hx, y⁻¹, H.inv_mem hy, ?_⟩
    have h : x⁻¹ * y⁻¹ = (x * y)⁻¹ := by
      rw [mul_inv_rev]
      exact hcomm x⁻¹ (G.inv_mem hx) y⁻¹ (H.inv_mem hy)
    rw [h]
    exact A.inv_mem hxy

theorem mem_projSub {G H A : Subgroup (MulAut V)} {hcomm : ∀ a ∈ G, ∀ b ∈ H, a * b = b * a}
    {x : MulAut V} : x ∈ projSub G H A hcomm ↔ x ∈ G ∧ ∃ y ∈ H, x * y ∈ A := Iff.rfl

theorem projSub_le {G H A : Subgroup (MulAut V)} (hcomm : ∀ a ∈ G, ∀ b ∈ H, a * b = b * a) :
    projSub G H A hcomm ≤ G := fun _ hx => (mem_projSub.mp hx).1

theorem isElemAbelian2_projSub {G H A : Subgroup (MulAut V)}
    (hcomm : ∀ a ∈ G, ∀ b ∈ H, a * b = b * a) (hbot : G ⊓ H = ⊥) (hA : IsElemAbelian2 A) :
    IsElemAbelian2 (projSub G H A hcomm) := by
  refine ⟨fun x hx x' hx' => ?_, fun x hx => ?_⟩
  · obtain ⟨hxG, y, hyH, hxy⟩ := mem_projSub.mp hx
    obtain ⟨hxG', y', hyH', hxy'⟩ := mem_projSub.mp hx'
    have h := hA.1 _ hxy _ hxy'
    have e1 : x * y * (x' * y') = x * x' * (y * y') := prod_mul_prod hcomm hxG' hyH
    have e2 : x' * y' * (x * y) = x' * x * (y' * y) := prod_mul_prod hcomm hxG hyH'
    rw [e1, e2] at h
    exact (decomp_unique hbot (G.mul_mem hxG hxG') (G.mul_mem hxG' hxG) (H.mul_mem hyH hyH')
      (H.mul_mem hyH' hyH) h).1
  · obtain ⟨hxG, y, hyH, hxy⟩ := mem_projSub.mp hx
    have h := hA.2 _ hxy
    have e : (x * y) ^ 2 = x * x * (y * y) := by
      rw [sq]
      exact prod_mul_prod hcomm hxG hyH
    rw [e] at h
    have h1 : x * x = 1 :=
      (decomp_unique hbot (G.mul_mem hxG hxG) G.one_mem (H.mul_mem hyH hyH) H.one_mem
        (by rw [h, mul_one])).1
    rw [sq]
    exact h1

theorem card_le_projSub_mul [Finite V] {G H A : Subgroup (MulAut V)}
    (hcomm : ∀ a ∈ G, ∀ b ∈ H, a * b = b * a) (hcomm' : ∀ b ∈ H, ∀ a ∈ G, b * a = a * b)
    (hA : A ≤ G ⊔ H) :
    Nat.card A ≤ Nat.card (projSub G H A hcomm) * Nat.card (projSub H G A hcomm') := by
  have hdec : ∀ a : A, ∃ x ∈ G, ∃ y ∈ H, (a : MulAut V) = x * y := fun a =>
    exists_decomp hcomm (hA a.2)
  choose x hx y hy hxy using hdec
  have hx1 : ∀ a : A, x a ∈ projSub G H A hcomm := fun a =>
    mem_projSub.mpr ⟨hx a, y a, hy a, by rw [← hxy a]; exact a.2⟩
  have hy1 : ∀ a : A, y a ∈ projSub H G A hcomm' := fun a =>
    mem_projSub.mpr ⟨hy a, x a, hx a, by rw [hcomm' _ (hy a) _ (hx a), ← hxy a]; exact a.2⟩
  let f : A → projSub G H A hcomm × projSub H G A hcomm' := fun a =>
    (⟨x a, hx1 a⟩, ⟨y a, hy1 a⟩)
  have hf : Function.Injective f := by
    intro a a' h
    have h1 : x a = x a' := congrArg (fun p => (p.1 : MulAut V)) h
    have h2 : y a = y a' := congrArg (fun p => (p.2 : MulAut V)) h
    apply Subtype.ext
    rw [hxy a, hxy a', h1, h2]
  calc Nat.card A ≤ Nat.card (projSub G H A hcomm × projSub H G A hcomm') :=
        Nat.card_le_card_of_injective f hf
    _ = _ := Nat.card_prod _ _

theorem fixMod_projSub {G H A : Subgroup (MulAut V)} (hcomm : ∀ a ∈ G, ∀ b ∈ H, a * b = b * a)
    (hA : A ≤ G ⊔ H) {W C : Subgroup V} (htriv : ∀ y ∈ H, ∀ w ∈ W, y w = w) :
    fixMod A W C = fixMod (projSub G H A hcomm) W C := by
  ext w
  rw [mem_fixMod, mem_fixMod]
  constructor
  · rintro ⟨hw, h⟩
    refine ⟨hw, fun x hx => ?_⟩
    obtain ⟨-, y, hyH, hxy⟩ := mem_projSub.mp hx
    have e : (x * y) w = x w := by rw [MulAut.mul_apply, htriv y hyH w hw]
    have h' := h (x * y) hxy
    rwa [e] at h'
  · rintro ⟨hw, h⟩
    refine ⟨hw, fun a ha => ?_⟩
    obtain ⟨x, hxG, y, hyH, rfl⟩ := exists_decomp hcomm (hA ha)
    have e : (x * y) w = x w := by rw [MulAut.mul_apply, htriv y hyH w hw]
    rw [e]
    exact h x (mem_projSub.mpr ⟨hxG, y, hyH, ha⟩)

end Projection

section PairLemmas

variable {V : Type} [CommGroup V] {G₁ G₂ : Subgroup (MulAut V)} {W₁ W₂ C : Subgroup V}

theorem PairData.le₁ (P : PairData G₁ G₂ W₁ W₂ C) : C ≤ W₁ := by
  rw [← P.inf_eq]
  exact inf_le_left

theorem PairData.le₂ (P : PairData G₁ G₂ W₁ W₂ C) : C ≤ W₂ := by
  rw [← P.inf_eq]
  exact inf_le_right

theorem PairData.act_mem₁ (P : PairData G₁ G₂ W₁ W₂ C) {a : MulAut V} (ha : a ∈ G₁ ⊔ G₂)
    {w : V} (hw : w ∈ W₁) : a w ∈ W₁ := by
  obtain ⟨x, hx, y, hy, rfl⟩ := exists_decomp P.comm ha
  rw [MulAut.mul_apply, P.triv₁ y hy w hw]
  exact P.inv₁ x hx w hw

theorem PairData.act_mem₂ (P : PairData G₁ G₂ W₁ W₂ C) {a : MulAut V} (ha : a ∈ G₁ ⊔ G₂)
    {w : V} (hw : w ∈ W₂) : a w ∈ W₂ := by
  obtain ⟨x, hx, y, hy, rfl⟩ := exists_decomp P.comm ha
  rw [MulAut.mul_apply, P.triv₂ x hx (y w) (P.inv₂ y hy w hw)]
  exact P.inv₂ y hy w hw

theorem fixMod_le {B : Subgroup (MulAut V)} {W C : Subgroup V} : fixMod B W C ≤ W :=
  fun _ hw => (mem_fixMod.mp hw).1

theorem le_fixMod {B : Subgroup (MulAut V)} {W C : Subgroup V} (hCW : C ≤ W)
    (hfix : ∀ b ∈ B, ∀ c ∈ C, b c = c) : C ≤ fixMod B W C := fun c hc =>
  mem_fixMod.mpr ⟨hCW hc, fun b hb => by rw [hfix b hb c hc, mul_inv_cancel]; exact C.one_mem⟩

theorem inf_fixMod_eq (P : PairData G₁ G₂ W₁ W₂ C) {A : Subgroup (MulAut V)}
    (hAG : A ≤ G₁ ⊔ G₂) : fixMod A W₁ C ⊓ fixMod A W₂ C = C := by
  apply le_antisymm
  · rw [← P.inf_eq]
    exact inf_le_inf fixMod_le fixMod_le
  · exact le_inf (le_fixMod P.le₁ fun b hb c hc => P.fix_C b (hAG hb) c hc)
      (le_fixMod P.le₂ fun b hb c hc => P.fix_C b (hAG hb) c hc)

theorem fixV_le_sup_fixMod (P : PairData G₁ G₂ W₁ W₂ C) {A : Subgroup (MulAut V)}
    (hAG : A ≤ G₁ ⊔ G₂) : fixV A ≤ fixMod A W₁ C ⊔ fixMod A W₂ C := by
  intro v hv
  have hv' : v ∈ W₁ ⊔ W₂ := by
    rw [P.sup_eq_top]
    exact Subgroup.mem_top v
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Subgroup.mem_sup.mp hv'
  have key : ∀ a ∈ A, a w₁ * w₁⁻¹ ∈ C ∧ a w₂ * w₂⁻¹ ∈ C := by
    intro a ha
    have hfix : a (w₁ * w₂) = w₁ * w₂ := (mem_fixV.mp hv) a ha
    rw [map_mul] at hfix
    have m₁ : a w₁ * w₁⁻¹ ∈ W₁ := W₁.mul_mem (P.act_mem₁ (hAG ha) hw₁) (W₁.inv_mem hw₁)
    have m₂ : a w₂ * w₂⁻¹ ∈ W₂ := W₂.mul_mem (P.act_mem₂ (hAG ha) hw₂) (W₂.inv_mem hw₂)
    have e : a w₁ * w₁⁻¹ = (a w₂ * w₂⁻¹)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      calc a w₁ * w₁⁻¹ * (a w₂ * w₂⁻¹) = (a w₁ * a w₂) * (w₁ * w₂)⁻¹ := by
            rw [mul_inv_rev]
            ac_rfl
        _ = 1 := by rw [hfix, mul_inv_cancel]
    have mC : a w₁ * w₁⁻¹ ∈ C := by
      rw [← P.inf_eq]
      exact ⟨m₁, by rw [e]; exact W₂.inv_mem m₂⟩
    refine ⟨mC, ?_⟩
    have e' : a w₂ * w₂⁻¹ = (a w₁ * w₁⁻¹)⁻¹ := by rw [e, inv_inv]
    rw [e']
    exact C.inv_mem mC
  exact Subgroup.mul_mem_sup (mem_fixMod.mpr ⟨hw₁, fun a ha => (key a ha).1⟩)
    (mem_fixMod.mpr ⟨hw₂, fun a ha => (key a ha).2⟩)

theorem card_pieces [Finite V] (P : PairData G₁ G₂ W₁ W₂ C) (N₁ : NatCount G₁ W₁ C)
    (N₂ : NatCount G₂ W₂ C) {A : Subgroup (MulAut V)} (hAG : A ≤ G₁ ⊔ G₂)
    (hA2 : IsElemAbelian2 A) :
    ∃ a₁ a₂ : ℕ, 0 < a₁ ∧ 0 < a₂ ∧ Nat.card A ≤ a₁ * a₂ ∧
      a₁ * Nat.card (fixMod A W₁ C) ≤ Nat.card W₁ ∧
      a₂ * Nat.card (fixMod A W₂ C) ≤ Nat.card W₂ := by
  have hc' : ∀ b ∈ G₂, ∀ a ∈ G₁, b * a = a * b := fun b hb a ha => (P.comm a ha b hb).symm
  have hAG' : A ≤ G₂ ⊔ G₁ := hAG.trans (sup_comm G₁ G₂).le
  have hbot' : G₂ ⊓ G₁ = ⊥ := by
    rw [inf_comm]
    exact P.inf_eq_bot
  refine ⟨Nat.card (projSub G₁ G₂ A P.comm), Nat.card (projSub G₂ G₁ A hc'), Nat.card_pos,
    Nat.card_pos, card_le_projSub_mul P.comm hc' hAG, ?_, ?_⟩
  · have h := N₁ _ (projSub_le P.comm) (isElemAbelian2_projSub P.comm P.inf_eq_bot hA2)
    rwa [← fixMod_projSub (C := C) P.comm hAG P.triv₁] at h
  · have h := N₂ _ (projSub_le hc') (isElemAbelian2_projSub hc' hbot' hA2)
    rwa [← fixMod_projSub (C := C) hc' hAG' P.triv₂] at h

theorem card_chain {a a₁ a₂ f s c y₁ y₂ w₁ w₂ v : ℕ} (hc : 0 < c) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hv : v ≤ a * f) (ha : a ≤ a₁ * a₂) (hn₁ : a₁ * y₁ ≤ w₁) (hn₂ : a₂ * y₂ ≤ w₂)
    (h1 : s * c = y₁ * y₂) (h2 : v * c = w₁ * w₂) : s ≤ f := by
  refine Nat.le_of_mul_le_mul_left ?_ (Nat.mul_pos (Nat.mul_pos ha₁ ha₂) hc)
  calc a₁ * a₂ * c * s = a₁ * a₂ * (s * c) := by ring
    _ = (a₁ * y₁) * (a₂ * y₂) := by rw [h1]; ring
    _ ≤ w₁ * w₂ := Nat.mul_le_mul hn₁ hn₂
    _ = v * c := h2.symm
    _ ≤ (a * f) * c := Nat.mul_le_mul_right c hv
    _ ≤ (a₁ * a₂ * f) * c := Nat.mul_le_mul_right c (Nat.mul_le_mul_right f ha)
    _ = a₁ * a₂ * c * f := by ring

end PairLemmas

theorem fixMod_le_fixV {V : Type} [CommGroup V] [Finite V] {G₁ G₂ : Subgroup (MulAut V)}
    {W₁ W₂ C : Subgroup V} (P : PairData G₁ G₂ W₁ W₂ C) (N₁ : NatCount G₁ W₁ C)
    (N₂ : NatCount G₂ W₂ C) {A : Subgroup (MulAut V)} (hAG : A ≤ G₁ ⊔ G₂)
    (hA2 : IsElemAbelian2 A) (hA : Nat.card V ≤ Nat.card A * Nat.card (fixV A)) :
    fixMod A W₁ C ≤ fixV A := by
  obtain ⟨a₁, a₂, ha₁, ha₂, hAa, hn₁, hn₂⟩ := card_pieces P N₁ N₂ hAG hA2
  have hF := fixV_le_sup_fixMod P hAG
  have h1 := card_sup_mul_card_inf (fixMod A W₁ C) (fixMod A W₂ C)
  rw [inf_fixMod_eq P hAG] at h1
  have h2 := card_sup_mul_card_inf W₁ W₂
  rw [P.sup_eq_top, P.inf_eq, Subgroup.card_top] at h2
  have h3 := card_chain Nat.card_pos ha₁ ha₂ hA hAa hn₁ hn₂ h1 h2
  have hEq : fixV A = fixMod A W₁ C ⊔ fixMod A W₂ C := Subgroup.eq_of_le_of_card_ge hF h3
  rw [hEq]
  exact le_sup_left

theorem exists_fixMod_ne {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {Q : Subgroup (MulAut V)} (hQ : IsPGroup 2 Q) {W C : Subgroup V} (_hCW : C ≤ W)
    (hne : ∃ w ∈ W, w ∉ C) (hinv : ∀ q ∈ Q, ∀ w ∈ W, q w ∈ W)
    (hfix : ∀ q ∈ Q, ∀ c ∈ C, q c = c) :
    ∃ w ∈ W, w ∉ C ∧ ∀ q ∈ Q, q w * w⁻¹ ∈ C := by
  let instAct : MulAction ↥Q ↥W :=
    { smul := fun q w => ⟨q.1 w.1, hinv q.1 q.2 w.1 w.2⟩
      one_smul := fun _ => Subtype.ext rfl
      mul_smul := fun _ _ _ => Subtype.ext rfl }
  have instQuot : MulAction.QuotientAction ↥Q (C.subgroupOf W) :=
    ⟨fun q {a a'} h => by
      rw [Subgroup.mem_subgroupOf] at h ⊢
      change (a.1)⁻¹ * a'.1 ∈ C at h
      change (q.1 a.1)⁻¹ * q.1 a'.1 ∈ C
      have e : (q.1 a.1)⁻¹ * q.1 a'.1 = q.1 ((a.1)⁻¹ * a'.1) := by rw [map_mul, map_inv]
      rw [e, hfix q.1 q.2 _ h]
      exact h⟩
  have hW2 : IsPGroup 2 ↥W := (isPGroup_two_of_sq_eq_one hV).to_subgroup W
  obtain ⟨n, hn⟩ := hW2.index (C.subgroupOf W)
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.index_eq_one] at hn
    obtain ⟨w, hw, hwC⟩ := hne
    have hmem : (⟨w, hw⟩ : ↥W) ∈ C.subgroupOf W := by
      rw [hn]
      exact Subgroup.mem_top _
    exact hwC (Subgroup.mem_subgroupOf.mp hmem)
  have hdvd : 2 ∣ Nat.card (↥W ⧸ C.subgroupOf W) := by
    rw [← Subgroup.index_eq_card, hn]
    exact dvd_pow_self 2 hn0
  have hfp : (1 : ↥W ⧸ C.subgroupOf W) ∈ MulAction.fixedPoints ↥Q (↥W ⧸ C.subgroupOf W) := by
    rw [MulAction.mem_fixedPoints]
    intro q
    have h1 : q • (1 : ↥W) = 1 := Subtype.ext (map_one q.1)
    show q • (QuotientGroup.mk (1 : ↥W) : ↥W ⧸ C.subgroupOf W) = QuotientGroup.mk 1
    rw [MulAction.Quotient.smul_mk, h1]
  obtain ⟨b, hb, hb1⟩ := hQ.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (↥W ⧸ C.subgroupOf W) hdvd hfp
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective b
  have hwfix := MulAction.mem_fixedPoints.mp hb
  refine ⟨(w : V), w.2, fun hwC => hb1 ?_, fun q hq => ?_⟩
  · exact ((QuotientGroup.eq_one_iff w).mpr (Subgroup.mem_subgroupOf.mpr hwC)).symm
  · have h := hwfix ⟨q, hq⟩
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
    change (q (w : V))⁻¹ * (w : V) ∈ C at h
    have e : q (w : V) * (w : V)⁻¹ = ((q (w : V))⁻¹ * (w : V))⁻¹ := by
      rw [mul_inv_rev, inv_inv, mul_comm]
    rw [e]
    exact C.inv_mem h

theorem exists_fixed_vector {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {X G₁ G₂ L₁ L₂ Q : Subgroup (MulAut V)} {W₁ W₂ C : Subgroup V}
    (P : PairData G₁ G₂ W₁ W₂ C) (N₁ : NatCount G₁ W₁ C) (N₂ : NatCount G₂ W₂ C)
    (hX : ffJ X ≤ G₁ ⊔ G₂) (hL₂ : L₂ ≤ G₂)
    (hne : ∃ w ∈ W₁, w ∉ C) (hfree : ∀ w ∈ W₁, (∀ l ∈ L₁, l w * w⁻¹ ∈ C) → w ∈ C)
    (𝒜 : Set (Subgroup (MulAut V))) (hA : ∀ A ∈ 𝒜, IsFFStarOffender X A)
    (hQ2 : IsPGroup 2 Q) (hAQ : ∀ A ∈ 𝒜, A ≤ Q) (hQG : Q ≤ G₁ ⊔ G₂) :
    ∃ w ∈ W₁, w ∉ fixV L₁ ∧ w ∈ fixV L₂ ∧ ∀ A ∈ 𝒜, w ∈ fixV A := by
  obtain ⟨w, hw, hwC, hwQ⟩ := exists_fixMod_ne hV hQ2 P.le₁ hne
    (fun q hq w hw => P.act_mem₁ (hQG hq) hw) (fun q hq c hc => P.fix_C q (hQG hq) c hc)
  refine ⟨w, hw, fun hfixL => hwC ?_, mem_fixV.mpr fun l hl => P.triv₁ l (hL₂ hl) w hw, ?_⟩
  · refine hfree w hw fun l hl => ?_
    rw [(mem_fixV.mp hfixL) l hl, mul_inv_cancel]
    exact C.one_mem
  · intro A hAmem
    have hAoff := hA A hAmem
    have hAG : A ≤ G₁ ⊔ G₂ := (B6.le_ffJ hAoff).trans hX
    have hcard : Nat.card V ≤ Nat.card A * Nat.card (fixV A) := by
      have h := hAoff.card_le (bot_le : (⊥ : Subgroup (MulAut V)) ≤ A)
      rwa [B1.card_bot_mul_card_fixV] at h
    exact fixMod_le_fixV P N₁ N₂ hAG hAoff.2.2.1 hcard
      (mem_fixMod.mpr ⟨hw, fun a ha => hwQ a (hAQ A hAmem ha)⟩)

end R3c23

end CFSG.Quasithin
