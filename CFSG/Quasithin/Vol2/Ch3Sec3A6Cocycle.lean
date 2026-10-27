module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3328
public import CFSG.Quasithin.Vol2.Ch3Sec3A6Act

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

section Heart

variable (m : ℕ)

@[expose] def permWeightHom (σ : Equiv.Perm (Fin m)) : ↥(evenWeight m) →+ ↥(evenWeight m) where
  toFun := permWeight m σ
  map_zero' := rfl
  map_add' _ _ := rfl

theorem constWeight_le_comap (σ : Equiv.Perm (Fin m)) :
    constWeight m ≤ (constWeight m).comap (permWeightHom m σ) := by
  intro x hx
  show ∀ i j, (x : Fin m → ZMod 2) (σ⁻¹ i) = (x : Fin m → ZMod 2) (σ⁻¹ j)
  exact fun i j => hx _ _

@[expose] def heartAct (σ : Equiv.Perm (Fin m)) : AltHeart m →+ AltHeart m :=
  QuotientAddGroup.map _ _ (permWeightHom m σ) (constWeight_le_comap m σ)

theorem heartAct_mk (σ : Equiv.Perm (Fin m)) (x : ↥(evenWeight m)) :
    heartAct m σ (QuotientAddGroup.mk x) = QuotientAddGroup.mk (permWeight m σ x) := rfl

variable {m}

theorem heartAct_eq_of_equivariant {G : Type} [Group G] {L : Subgroup G}
    {α : ↥L →* alternatingGroup (Fin m)} {β : ↥(blockU L) →* Multiplicative (AltHeart m)}
    (hβe : ∀ (ℓ : ↥L) (u v : ↥(blockU L)), (v : G) = ℓ * u * ℓ⁻¹ →
      ∀ x : ↥(evenWeight m), (QuotientAddGroup.mk x : AltHeart m) = Multiplicative.toAdd (β u) →
        (QuotientAddGroup.mk (permWeight m (α ℓ : Equiv.Perm (Fin m)) x) : AltHeart m) =
          Multiplicative.toAdd (β v))
    (ℓ : ↥L) (u v : ↥(blockU L)) (h : (v : G) = ℓ * u * ℓ⁻¹) :
    Multiplicative.toAdd (β v) =
      heartAct m (α ℓ : Equiv.Perm (Fin m)) (Multiplicative.toAdd (β u)) := by
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (β u))
  rw [← hx, heartAct_mk]
  exact (hβe ℓ u v h x hx).symm

end Heart

namespace A6Coc

abbrev Γ : Type := ↥(alternatingGroup (Fin 6))

theorem aP_mem : aP ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup, aP, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_swap (show (0 : Fin 6) ≠ 1 by decide),
    Equiv.Perm.sign_swap (show (1 : Fin 6) ≠ 2 by decide)]
  decide

theorem bP_mem : bP ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup, bP, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (show (1 : Fin 6) ≠ 2 by decide),
    Equiv.Perm.sign_swap (show (2 : Fin 6) ≠ 3 by decide),
    Equiv.Perm.sign_swap (show (3 : Fin 6) ≠ 4 by decide),
    Equiv.Perm.sign_swap (show (4 : Fin 6) ≠ 5 by decide)]
  decide

@[expose] def aL : Γ := ⟨aP, aP_mem⟩

@[expose] def bL : Γ := ⟨bP, bP_mem⟩

@[expose] def step (da db : Vec4) (s : Γ × Vec4) (l : Bool) : Γ × Vec4 :=
  (s.1 * (if l then bL else aL), s.2 + act (s.1 : Equiv.Perm (Fin 6)) (if l then db else da))

@[expose] def wordVal (da db : Vec4) (w : List Bool) : Γ × Vec4 := w.foldl (step da db) (1, 0)

@[expose] def r₃ : List Bool := [false, false, false]

@[expose] def r₄ : List Bool := (List.replicate 4 [false, true]).flatten

@[expose] def y₀ : Vec4 := ![0, 0, 0, 1]

theorem rels_one : (wordVal 0 0 r₃).1 = 1 ∧ (wordVal 0 0 r₄).1 = 1 := by decide +kernel

theorem normCheck : ∀ x y : Vec4, (wordVal x y r₃).2 = 0 → ∃ w : Vec4, x = w - act aP w := by
  decide +kernel

theorem relCheck : ∀ y : Vec4, (wordVal 0 y r₄).2 = 0 →
    ∃ v : Vec4, act aP v = v ∧ (y = v - act bP v ∨ y = y₀ + (v - act bP v)) := by
  decide +kernel

@[expose] def decodeW : ℕ → ℕ → List Bool
  | 0, _ => []
  | f + 1, n => if n ≤ 1 then [] else decodeW f (n / 2) ++ [n % 2 == 1]

@[expose] def codes3 : List ℕ :=
  [ 0, 0, 0, 0, 0, 0, 0, 0, 2, 181, 436, 171, 0, 4, 0, 111, 218, 634, 0, 591, 207, 0, 119, 2455,
    0, 173, 301, 93, 0, 123, 0, 125, 189, 361, 110, 0, 0, 0, 4, 591, 173, 125, 0, 0, 0, 0, 0, 0,
    2, 0, 0, 175, 346, 250, 181, 0, 117, 0, 732, 1687, 436, 0, 421, 628, 0, 245, 171, 0, 107, 331,
    87, 0, 0, 2, 0, 207, 301, 189, 4, 0, 0, 117, 421, 107, 0, 0, 0, 0, 0, 0, 111, 175, 0, 0, 215,
    1957, 218, 346, 0, 122, 0, 630, 634, 250, 0, 466, 604, 0, 0, 181, 111, 0, 93, 361, 591, 0, 175,
    0, 628, 331, 207, 117, 0, 0, 122, 466, 0, 0, 0, 0, 0, 0, 119, 732, 215, 0, 0, 235, 2455, 1687,
    1957, 0, 3289, 0, 0, 436, 218, 119, 0, 110, 173, 0, 346, 732, 0, 87, 301, 421, 0, 215, 0, 604,
    93, 628, 122, 0, 0, 3289, 0, 0, 0, 0, 0, 0, 123, 245, 630, 235, 0, 0, 0, 171, 634, 2455, 123,
    0, 125, 0, 250, 1687, 245, 0, 189, 107, 0, 1957, 630, 0, 361, 331, 466, 0, 235, 0, 110, 87,
    604, 3289, 0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def word3 (i j k : Fin 6) : List Bool :=
  decodeW 12 (codes3.getD (36 * i.val + 6 * j.val + k.val) 0)

theorem word3_spec : ∀ i j k : Fin 6, i ≠ j → j ≠ k → i ≠ k →
    ((wordVal 0 0 (word3 i j k)).1 : Equiv.Perm (Fin 6)) = Equiv.swap i j * Equiv.swap j k := by
  decide +kernel

theorem fst_wordVal (da db da' db' : Vec4) (w : List Bool) :
    (wordVal da db w).1 = (wordVal da' db' w).1 := by
  unfold wordVal
  suffices h : ∀ s s' : Γ × Vec4, s.1 = s'.1 →
      (w.foldl (step da db) s).1 = (w.foldl (step da' db') s').1 from h _ _ rfl
  induction w with
  | nil => intro s s' h; exact h
  | cons l w ih =>
    intro s s' h
    simp only [List.foldl_cons]
    exact ih _ _ (by simp only [step, h])

theorem fst_wordVal_mem (da db : Vec4) (w : List Bool) :
    (wordVal da db w).1 ∈ Subgroup.closure ({aL, bL} : Set Γ) := by
  unfold wordVal
  suffices h : ∀ s : Γ × Vec4, s.1 ∈ Subgroup.closure ({aL, bL} : Set Γ) →
      (w.foldl (step da db) s).1 ∈ Subgroup.closure ({aL, bL} : Set Γ) from
    h _ (Subgroup.one_mem _)
  induction w with
  | nil => intro s h; exact h
  | cons l w ih =>
    intro s h
    simp only [List.foldl_cons]
    refine ih _ ?_
    simp only [step]
    refine Subgroup.mul_mem _ h (Subgroup.subset_closure ?_)
    cases l <;> simp

theorem closure_ab : Subgroup.closure ({aL, bL} : Set Γ) = ⊤ := by
  rw [eq_top_iff, ← alternatingGroup.closure_isThreeCycles_eq_top, Subgroup.closure_le]
  intro g hg
  have hg3 : (g : Equiv.Perm (Fin 6)).IsThreeCycle := hg
  obtain ⟨x, hx⟩ : (g : Equiv.Perm (Fin 6)).support.Nonempty := by
    rw [← Finset.card_pos, hg3.card_support]
    norm_num
  have hxg := hg3.eq_swap_mul_swap_iff_mem_support.mpr hx
  set p : Equiv.Perm (Fin 6) := (g : Equiv.Perm (Fin 6)) with hp
  have h1 : p x ≠ x := Equiv.Perm.mem_support.mp hx
  have h2 : p (p x) ≠ p x := fun h => h1 (p.injective h)
  have h3 : p (p x) ≠ x := by
    intro h
    have h33 : (p ^ 3) x = x := by
      rw [← hg3.orderOf, pow_orderOf_eq_one]
      rfl
    have e : (p ^ 3) x = p (p (p x)) := by
      simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply]
    rw [e, h] at h33
    exact h1 h33
  have hw := word3_spec x (p x) (p (p x)) h1.symm h2.symm h3.symm
  have hgw : g = (wordVal 0 0 (word3 x (p x) (p (p x)))).1 := by
    apply Subtype.ext
    rw [hw]
    exact hxg
  rw [SetLike.mem_coe, hgw]
  exact fst_wordVal_mem 0 0 _

@[expose] def IsCrossed (δ : Γ → Vec4) : Prop :=
  ∀ g h : Γ, δ (g * h) = δ g + act (g : Equiv.Perm (Fin 6)) (δ h)

@[expose] def IsInner (δ : Γ → Vec4) : Prop :=
  ∃ v : Vec4, ∀ g : Γ, δ g = v - act (g : Equiv.Perm (Fin 6)) v

variable {δ : Γ → Vec4}

theorem cocycle_one (hδ : IsCrossed δ) : δ 1 = 0 := by
  have h := hδ 1 1
  rw [one_mul] at h
  have h1 : act ((1 : Γ) : Equiv.Perm (Fin 6)) (δ 1) = δ 1 := act_one (δ 1)
  rw [h1] at h
  have : δ 1 + δ 1 = δ 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel this

theorem snd_wordVal (hδ : IsCrossed δ) (w : List Bool) :
    (wordVal (δ aL) (δ bL) w).2 = δ (wordVal (δ aL) (δ bL) w).1 := by
  unfold wordVal
  suffices h : ∀ s : Γ × Vec4, s.2 = δ s.1 →
      (w.foldl (step (δ aL) (δ bL)) s).2 = δ (w.foldl (step (δ aL) (δ bL)) s).1 from
    h _ (cocycle_one hδ).symm
  induction w with
  | nil => intro s h; exact h
  | cons l w ih =>
    intro s h
    simp only [List.foldl_cons]
    refine ih _ ?_
    simp only [step]
    rw [hδ, h]
    cases l <;> rfl

theorem inner_of_gens (hδ : IsCrossed δ) (v : Vec4)
    (ha : δ aL = v - act aP v) (hb : δ bL = v - act bP v) :
    ∀ g, δ g = v - act (g : Equiv.Perm (Fin 6)) v := by
  intro g
  let H : Subgroup Γ :=
    { carrier := {g | δ g = v - act (g : Equiv.Perm (Fin 6)) v}
      one_mem' := by
        show δ 1 = v - act ((1 : Γ) : Equiv.Perm (Fin 6)) v
        rw [cocycle_one hδ]
        show 0 = v - act 1 v
        rw [act_one, sub_self]
      mul_mem' := by
        intro x y hx hy
        show δ (x * y) = v - act ((x * y : Γ) : Equiv.Perm (Fin 6)) v
        rw [hδ, hx, hy]
        show v - act x v + act x (v - act y v) = v - act ((x : Equiv.Perm (Fin 6)) * y) v
        rw [act_sub, act_mul]
        abel
      inv_mem' := by
        intro x hx
        show δ x⁻¹ = v - act ((x⁻¹ : Γ) : Equiv.Perm (Fin 6)) v
        have h1 := hδ x⁻¹ x
        rw [inv_mul_cancel, cocycle_one hδ, hx, act_sub, ← act_mul] at h1
        have e : ((x⁻¹ : Γ) : Equiv.Perm (Fin 6)) * (x : Equiv.Perm (Fin 6)) = 1 := by
          rw [← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]
        rw [e, act_one] at h1
        have h2 : δ x⁻¹ = -(act ((x⁻¹ : Γ) : Equiv.Perm (Fin 6)) v - v) :=
          eq_neg_of_add_eq_zero_left h1.symm
        rw [h2]
        abel }
  have hle : Subgroup.closure ({aL, bL} : Set Γ) ≤ H := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  rw [closure_ab] at hle
  exact hle (Subgroup.mem_top g)

theorem isCrossed_sub {δ₁ δ₂ : Γ → Vec4} (h₁ : IsCrossed δ₁) (h₂ : IsCrossed δ₂) :
    IsCrossed fun g => δ₁ g - δ₂ g := by
  intro g h
  show δ₁ (g * h) - δ₂ (g * h) = δ₁ g - δ₂ g + act g (δ₁ h - δ₂ h)
  rw [h₁, h₂, act_sub]
  abel

theorem isCrossed_inner (w : Vec4) : IsCrossed fun g => w - act (g : Equiv.Perm (Fin 6)) w := by
  intro g h
  show w - act ((g * h : Γ) : Equiv.Perm (Fin 6)) w =
    w - act g w + act g (w - act (h : Equiv.Perm (Fin 6)) w)
  rw [Subgroup.coe_mul, act_mul, act_sub]
  abel

theorem normal_form (hδ : IsCrossed δ) :
    ∃ w v : Vec4, act aP v = v ∧ δ aL = w - act aP w ∧
      (δ bL - (w - act bP w) = v - act bP v ∨ δ bL - (w - act bP w) = y₀ + (v - act bP v)) := by
  have ha3 : (wordVal (δ aL) (δ bL) r₃).2 = 0 := by
    have h1 := snd_wordVal hδ r₃
    rw [fst_wordVal (δ aL) (δ bL) 0 0, rels_one.1, cocycle_one hδ] at h1
    exact h1
  obtain ⟨w, hw⟩ := normCheck _ _ ha3
  set δ' : Γ → Vec4 := fun g => δ g - (w - act (g : Equiv.Perm (Fin 6)) w) with hδ'def
  have hδ' : IsCrossed δ' := isCrossed_sub hδ (isCrossed_inner w)
  have hδ'a : δ' aL = 0 := by
    show δ aL - (w - act aP w) = 0
    rw [hw, sub_self]
  have hrel : (wordVal 0 (δ' bL) r₄).2 = 0 := by
    have h1 := snd_wordVal hδ' r₄
    rw [hδ'a] at h1
    rw [h1, fst_wordVal 0 (δ' bL) 0 0, rels_one.2]
    exact cocycle_one hδ'
  obtain ⟨v, hv, hb⟩ := relCheck (δ' bL) hrel
  exact ⟨w, v, hv, hw, hb⟩

theorem diff_inner {δ₁ δ₂ : Γ → Vec4} (hδ₁ : IsCrossed δ₁) (hδ₂ : IsCrossed δ₂)
    (h₁ : ¬ IsInner δ₁) (h₂ : ¬ IsInner δ₂) : IsInner fun g => δ₁ g - δ₂ g := by
  have key : ∀ δ : Γ → Vec4, IsCrossed δ → ¬ IsInner δ → ∃ w v : Vec4, act aP v = v ∧
      δ aL = w - act aP w ∧ δ bL - (w - act bP w) = y₀ + (v - act bP v) := by
    intro δ hδ hn
    obtain ⟨w, v, hv, ha, hb | hb⟩ := normal_form hδ
    · refine absurd ⟨w + v, inner_of_gens hδ (w + v) ?_ ?_⟩ hn
      · rw [ha, act_add, hv]
        abel
      · rw [act_add]
        rw [sub_eq_iff_eq_add] at hb
        rw [hb]
        abel
    · exact ⟨w, v, hv, ha, hb⟩
  obtain ⟨w₁, v₁, hv₁, ha₁, hb₁⟩ := key δ₁ hδ₁ h₁
  obtain ⟨w₂, v₂, hv₂, ha₂, hb₂⟩ := key δ₂ hδ₂ h₂
  refine ⟨(w₁ - w₂) + (v₁ - v₂),
    inner_of_gens (isCrossed_sub hδ₁ hδ₂) _ ?_ ?_⟩
  · show δ₁ aL - δ₂ aL = _
    rw [ha₁, ha₂, act_add, act_sub, act_sub, hv₁, hv₂]
    abel
  · show δ₁ bL - δ₂ bL = _
    rw [sub_eq_iff_eq_add] at hb₁ hb₂
    rw [hb₁, hb₂, act_add, act_sub, act_sub]
    abel

@[expose] def crdHom : (Fin 6 → ZMod 2) →+ Vec4 where
  toFun := crd
  map_zero' := crd_zero
  map_add' := crd_add

theorem constWeight_le_ker :
    constWeight 6 ≤ (crdHom.comp (evenWeight 6).subtype).ker := by
  intro x hx
  rw [AddMonoidHom.mem_ker]
  have e : ((x : ↥(evenWeight 6)) : Fin 6 → ZMod 2) = fun _ => (x : Fin 6 → ZMod 2) 0 :=
    funext fun i => hx i 0
  show crd (x : Fin 6 → ZMod 2) = 0
  rw [e]
  exact crd_const _

@[expose] def eps : AltHeart 6 →+ Vec4 :=
  QuotientAddGroup.lift (constWeight 6) (crdHom.comp (evenWeight 6).subtype) constWeight_le_ker

theorem eps_mk (x : ↥(evenWeight 6)) :
    eps (QuotientAddGroup.mk x) = crd (x : Fin 6 → ZMod 2) := rfl

theorem sum_eq_zero_of_mem (x : ↥(evenWeight 6)) : ∑ i, (x : Fin 6 → ZMod 2) i = 0 := by
  have := x.2
  simpa [evenWeight] using this

theorem sec_mem (v : Vec4) : sec v ∈ evenWeight 6 := by
  simp only [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply]
  exact sum_sec v

@[expose] def epsInv (v : Vec4) : AltHeart 6 := QuotientAddGroup.mk ⟨sec v, sec_mem v⟩

theorem eps_epsInv (v : Vec4) : eps (epsInv v) = v := crd_sec v

theorem const_aux : ∀ x : Fin 6 → ZMod 2, x 0 + x 1 + x 2 + x 3 + x 4 + x 5 = 0 → crd x = 0 →
    ∀ i j, x i = x j := by
  decide +kernel

theorem eps_injective : Function.Injective eps := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  rw [eps_mk] at hy
  rw [QuotientAddGroup.eq_zero_iff]
  have hs := sum_eq_zero_of_mem x
  rw [Fin.sum_univ_six] at hs
  exact const_aux _ hs hy

theorem card_vec4 : Nat.card Vec4 = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_altHeart : Nat.card (AltHeart 6) = 16 := by
  rw [Nat.card_congr (Equiv.ofBijective eps ⟨eps_injective, fun v => ⟨epsInv v, eps_epsInv v⟩⟩)]
  exact card_vec4

theorem eps_heartAct (σ : Equiv.Perm (Fin 6)) (y : AltHeart 6) :
    eps (heartAct 6 σ y) = act σ (eps y) := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  rw [heartAct_mk, eps_mk, eps_mk, act_crd σ _ (sum_eq_zero_of_mem x)]
  rfl

theorem a6_cocycle {δ₁ δ₂ : Γ → AltHeart 6}
    (hδ₁ : ∀ g h : Γ, δ₁ (g * h) = δ₁ g + heartAct 6 (g : Equiv.Perm (Fin 6)) (δ₁ h))
    (hδ₂ : ∀ g h : Γ, δ₂ (g * h) = δ₂ g + heartAct 6 (g : Equiv.Perm (Fin 6)) (δ₂ h))
    (h₁ : ¬ ∃ u, ∀ g : Γ, δ₁ g = u - heartAct 6 (g : Equiv.Perm (Fin 6)) u)
    (h₂ : ¬ ∃ u, ∀ g : Γ, δ₂ g = u - heartAct 6 (g : Equiv.Perm (Fin 6)) u) :
    ∃ u, ∀ g : Γ, δ₁ g - δ₂ g = u - heartAct 6 (g : Equiv.Perm (Fin 6)) u := by
  have hc : ∀ δ : Γ → AltHeart 6,
      (∀ g h : Γ, δ (g * h) = δ g + heartAct 6 (g : Equiv.Perm (Fin 6)) (δ h)) →
      IsCrossed fun g => eps (δ g) := by
    intro δ hδ g h
    show eps (δ (g * h)) = eps (δ g) + act g (eps (δ h))
    rw [hδ, map_add, eps_heartAct]
  have hi : ∀ δ : Γ → AltHeart 6,
      (¬ ∃ u, ∀ g : Γ, δ g = u - heartAct 6 (g : Equiv.Perm (Fin 6)) u) →
      ¬ IsInner fun g => eps (δ g) := by
    rintro δ hn ⟨v, hv⟩
    have hv' : ∀ g : Γ, eps (δ g) = v - act (g : Equiv.Perm (Fin 6)) v := hv
    refine hn ⟨epsInv v, fun g => eps_injective ?_⟩
    calc eps (δ g) = v - act (g : Equiv.Perm (Fin 6)) v := hv' g
      _ = eps (epsInv v) - act (g : Equiv.Perm (Fin 6)) (eps (epsInv v)) := by
        rw [eps_epsInv]
      _ = eps (epsInv v) - eps (heartAct 6 (g : Equiv.Perm (Fin 6)) (epsInv v)) := by
        rw [eps_heartAct]
      _ = eps (epsInv v - heartAct 6 (g : Equiv.Perm (Fin 6)) (epsInv v)) := (map_sub _ _ _).symm
  obtain ⟨v, hv⟩ := diff_inner (hc δ₁ hδ₁) (hc δ₂ hδ₂) (hi δ₁ h₁) (hi δ₂ h₂)
  have hv' : ∀ g : Γ, eps (δ₁ g) - eps (δ₂ g) = v - act (g : Equiv.Perm (Fin 6)) v := hv
  refine ⟨epsInv v, fun g => eps_injective ?_⟩
  calc eps (δ₁ g - δ₂ g) = eps (δ₁ g) - eps (δ₂ g) := map_sub _ _ _
    _ = v - act (g : Equiv.Perm (Fin 6)) v := hv' g
    _ = eps (epsInv v) - act (g : Equiv.Perm (Fin 6)) (eps (epsInv v)) := by rw [eps_epsInv]
    _ = eps (epsInv v) - eps (heartAct 6 (g : Equiv.Perm (Fin 6)) (epsInv v)) := by
      rw [eps_heartAct]
    _ = eps (epsInv v - heartAct 6 (g : Equiv.Perm (Fin 6)) (epsInv v)) := (map_sub _ _ _).symm

end A6Coc

namespace A6Block

variable {G : Type} [Group G]

theorem relIndex_le_two_of {H Q : Subgroup G}
    (h : ∀ x ∈ Q, ∀ y ∈ Q, x ∉ H → y ∉ H → x⁻¹ * y ∈ H) : H.relIndex Q ≤ 2 := by
  rw [Subgroup.relIndex, Subgroup.index]
  let f : ↥Q ⧸ H.subgroupOf Q → Prop :=
    Quotient.lift (s := QuotientGroup.leftRel (H.subgroupOf Q)) (fun q : ↥Q => (q : G) ∈ H) (by
      intro a b hab
      have hab' : (a : G)⁻¹ * b ∈ H := by
        have := QuotientGroup.leftRel_apply.mp hab
        rwa [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at this
      apply propext
      constructor
      · intro ha
        have := H.mul_mem ha hab'
        rwa [mul_inv_cancel_left] at this
      · intro hb
        have := H.mul_mem hb (H.inv_mem hab')
        rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at this)
  have hf : Function.Injective f := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    have hab : (a : G) ∈ H ↔ (b : G) ∈ H := Iff.of_eq hxy
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    by_cases ha : (a : G) ∈ H
    · exact H.mul_mem (H.inv_mem ha) (hab.mp ha)
    · exact h a a.2 b b.2 ha fun hb => ha (hab.mpr hb)
  calc Nat.card (↥Q ⧸ H.subgroupOf Q) ≤ Nat.card Prop := Nat.card_le_card_of_injective f hf
    _ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_prop]

theorem card_blockU_of_blockZ_eq_bot {L : Subgroup G} (hA : IsAltBlockType L 6)
    (hZ : blockZ L = ⊥) : Nat.card ↥(blockU L) = 16 := by
  obtain ⟨-, α, -, -, β, hβs, hβk, -⟩ := hA
  have hinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, hZ, Subgroup.bot_subgroupOf]
  rw [Nat.card_congr (Equiv.ofBijective β ⟨hinj, hβs⟩)]
  exact A6Coc.card_altHeart

theorem relIndex_le_two {L Q : Subgroup G} (hA : IsAltBlockType L 6)
    (hQL : Q ≤ Subgroup.normalizer (L : Set G))
    (hQU : ∀ q ∈ Q, ∀ ℓ ∈ L, ⁅q, ℓ⁆ ∈ blockU L)
    (hQQ : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ Subgroup.centralizer (L : Set G))
    (hOQ : pCoreOf 2 L ≤ Q) :
    (blockU L ⊔ Q ⊓ Subgroup.centralizer (L : Set G)).relIndex Q ≤ 2 := by
  obtain ⟨hL, α, hαs, hαk, β, hβs, hβk, hβe⟩ := hA
  have hUQ : blockU L ≤ Q := (C1.blockU_le_blockQ hL).trans hOQ
  have hLU : L ≤ Subgroup.normalizer (blockU L : Set G) := fun x hx =>
    C1.mem_normalizer_blockU (Subgroup.le_normalizer hx)
  have hQUn : Q ≤ Subgroup.normalizer (blockU L : Set G) := fun x hx =>
    C1.mem_normalizer_blockU (hQL hx)
  have hUab : ∀ a ∈ blockU L, ∀ b ∈ blockU L, a * b = b * a := by
    intro a ha b hb
    have h1 := hL.2.2.1.1 ha
    have h2 := hL.2.2.1.1 hb
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp h1).2 b
      (Subgroup.mem_inf.mp h2).1).symm
  have hβZ : ∀ u : ↥(blockU L), (u : G) ∈ blockZ L → β u = 1 := by
    intro u hu
    have : u ∈ β.ker := by rw [hβk]; exact Subgroup.mem_subgroupOf.mpr hu
    exact this
  have hβeq : ∀ x y : ↥(blockU L), (x : G) * (y : G)⁻¹ ∈ blockZ L → β x = β y := by
    intro x y hxy
    have h1 := hβZ (x * y⁻¹) hxy
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1
  let cU : ∀ c ∈ Q, ↥L → ↥(blockU L) := fun c hc ℓ => ⟨⁅c, (ℓ : G)⁆, hQU c hc ℓ ℓ.2⟩
  have hdep : ∀ c (hc : c ∈ Q) (ℓ ℓ' : ↥L), α ℓ = α ℓ' → β (cU c hc ℓ) = β (cU c hc ℓ') := by
    intro c hc ℓ ℓ' he
    have hk : ℓ'⁻¹ * ℓ ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
    rw [hαk, Lem3328.mem_pCore_iff] at hk
    have hz : ⁅c, ((ℓ'⁻¹ * ℓ : ↥L) : G)⁆ ∈ blockZ L :=
      ⟨hQU c hc _ (ℓ'⁻¹ * ℓ).2, hQQ c hc _ (hOQ hk)⟩
    have hcen : (ℓ' : G) * ⁅c, ((ℓ'⁻¹ * ℓ : ↥L) : G)⁆ = ⁅c, ((ℓ'⁻¹ * ℓ : ↥L) : G)⁆ * ℓ' :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 ℓ' ℓ'.2
    have e : cU c hc ℓ = cU c hc ℓ' * ⟨⁅c, ((ℓ'⁻¹ * ℓ : ↥L) : G)⁆, (Subgroup.mem_inf.mp hz).1⟩ := by
      apply Subtype.ext
      show ⁅c, (ℓ : G)⁆ = ⁅c, (ℓ' : G)⁆ * ⁅c, ((ℓ'⁻¹ * ℓ : ↥L) : G)⁆
      have e1 : ⁅c, (ℓ : G)⁆ = ⁅c, (ℓ' : G)⁆ *
          ((ℓ' : G) * ⁅c, ((ℓ'⁻¹ * ℓ : ↥L) : G)⁆ * (ℓ' : G)⁻¹) := by
        simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e1, hcen, mul_inv_cancel_right]
    rw [e, map_mul, hβZ ⟨_, (Subgroup.mem_inf.mp hz).1⟩ hz, mul_one]
  let δ : ∀ c ∈ Q, A6Coc.Γ → AltHeart 6 := fun c hc g =>
    Multiplicative.toAdd (β (cU c hc (Function.surjInv hαs g)))
  have hδα : ∀ c (hc : c ∈ Q) (ℓ : ↥L), δ c hc (α ℓ) = Multiplicative.toAdd (β (cU c hc ℓ)) := by
    intro c hc ℓ
    show Multiplicative.toAdd (β (cU c hc (Function.surjInv hαs (α ℓ)))) = _
    rw [hdep c hc _ ℓ (Function.surjInv_eq hαs (α ℓ))]
  have hδc : ∀ c (hc : c ∈ Q) (g h : A6Coc.Γ),
      δ c hc (g * h) = δ c hc g + heartAct 6 (g : Equiv.Perm (Fin 6)) (δ c hc h) := by
    intro c hc g h
    obtain ⟨ℓ₁, rfl⟩ := hαs g
    obtain ⟨ℓ₂, rfl⟩ := hαs h
    rw [← map_mul, hδα c hc, hδα c hc, hδα c hc]
    have hw : (ℓ₁ : G) * ⁅c, (ℓ₂ : G)⁆ * (ℓ₁ : G)⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.mp (hLU ℓ₁.2) _).mp (hQU c hc ℓ₂ ℓ₂.2)
    have e : cU c hc (ℓ₁ * ℓ₂) = cU c hc ℓ₁ * ⟨_, hw⟩ := by
      apply Subtype.ext
      show ⁅c, ((ℓ₁ * ℓ₂ : ↥L) : G)⁆ = ⁅c, (ℓ₁ : G)⁆ * ((ℓ₁ : G) * ⁅c, (ℓ₂ : G)⁆ * (ℓ₁ : G)⁻¹)
      simp only [commutatorElement_def, Subgroup.coe_mul]
      group
    rw [e, map_mul, toAdd_mul, heartAct_eq_of_equivariant hβe ℓ₁ (cU c hc ℓ₂) ⟨_, hw⟩ rfl]
  have hin : ∀ c (hc : c ∈ Q),
      (∃ u₀, ∀ g : A6Coc.Γ, δ c hc g = u₀ - heartAct 6 (g : Equiv.Perm (Fin 6)) u₀) →
      c ∈ blockU L ⊔ Q ⊓ Subgroup.centralizer (L : Set G) := by
    rintro c hc ⟨u₀, hu₀⟩
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd u₀)
    have hcen : (u : G)⁻¹ * c ∈ Subgroup.centralizer (L : Set G) := by
      refine Lem3328.mem_centralizer_of_commutator_mem_blockZ hL fun ℓ hℓ => ?_
      have hul : (ℓ : G) * (u : G)⁻¹ * ℓ⁻¹ ∈ blockU L :=
        (Subgroup.mem_normalizer_iff.mp (hLU hℓ) _).mp (Subgroup.inv_mem _ u.2)
      have hcu : (⁅(u : G), ℓ⁆ : G) ∈ blockU L := by
        have : ⁅(u : G), ℓ⁆ = (u : G) * ((ℓ : G) * (u : G)⁻¹ * ℓ⁻¹) := by
          rw [commutatorElement_def]; group
        rw [this]
        exact Subgroup.mul_mem _ u.2 hul
      have hβu : Multiplicative.toAdd (β ⟨⁅(u : G), ℓ⁆, hcu⟩) =
          u₀ - heartAct 6 (α ⟨ℓ, hℓ⟩ : Equiv.Perm (Fin 6)) u₀ := by
        have e : (⟨⁅(u : G), ℓ⁆, hcu⟩ : ↥(blockU L)) = u * ⟨_, hul⟩ :=
          Subtype.ext (by
            show ⁅(u : G), ℓ⁆ = (u : G) * ((ℓ : G) * (u : G)⁻¹ * ℓ⁻¹)
            rw [commutatorElement_def]; group)
        rw [e, map_mul, toAdd_mul, heartAct_eq_of_equivariant hβe ⟨ℓ, hℓ⟩ u⁻¹ ⟨_, hul⟩ rfl,
          map_inv, toAdd_inv, hu, toAdd_ofAdd, map_neg, sub_eq_add_neg]
      have hβc : Multiplicative.toAdd (β (cU c hc ⟨ℓ, hℓ⟩)) =
          u₀ - heartAct 6 (α ⟨ℓ, hℓ⟩ : Equiv.Perm (Fin 6)) u₀ := by
        rw [← hδα c hc]
        exact hu₀ _
      have hββ : β (cU c hc ⟨ℓ, hℓ⟩) = β ⟨⁅(u : G), ℓ⁆, hcu⟩ :=
        Multiplicative.toAdd.injective (hβc.trans hβu.symm)
      have hker : cU c hc ⟨ℓ, hℓ⟩ * (⟨⁅(u : G), ℓ⁆, hcu⟩ : ↥(blockU L))⁻¹ ∈ β.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hββ]
        exact mul_inv_cancel _
      rw [hβk, Subgroup.mem_subgroupOf] at hker
      have hz : ⁅c, ℓ⁆ * ⁅(u : G), ℓ⁆⁻¹ ∈ blockZ L := hker
      have hwU : ⁅c, ℓ⁆ * ((ℓ : G) * u * ℓ⁻¹) ∈ blockU L :=
        Subgroup.mul_mem _ (hQU c hc ℓ hℓ)
          ((Subgroup.mem_normalizer_iff.mp (hLU hℓ) _).mp u.2)
      have huw := hUab _ u.2 _ hwU
      have e : ⁅(u : G)⁻¹ * c, ℓ⁆ = ⁅c, ℓ⁆ * ⁅(u : G), ℓ⁆⁻¹ := by
        have e1 : ⁅(u : G)⁻¹ * c, ℓ⁆ = (u : G)⁻¹ * (⁅c, ℓ⁆ * ((ℓ : G) * u * ℓ⁻¹)) := by
          simp only [commutatorElement_def]; group
        have e2 : ⁅c, ℓ⁆ * ⁅(u : G), ℓ⁆⁻¹ = (⁅c, ℓ⁆ * ((ℓ : G) * u * ℓ⁻¹)) * (u : G)⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e1, e2]
        calc (u : G)⁻¹ * (⁅c, ℓ⁆ * ((ℓ : G) * u * ℓ⁻¹)) =
            (u : G)⁻¹ * ((⁅c, ℓ⁆ * ((ℓ : G) * u * ℓ⁻¹)) * u) * (u : G)⁻¹ := by group
          _ = (u : G)⁻¹ * ((u : G) * (⁅c, ℓ⁆ * ((ℓ : G) * u * ℓ⁻¹))) * (u : G)⁻¹ := by
            rw [huw]
          _ = _ := by group
      rw [e]
      exact hz
    have hmem : (u : G)⁻¹ * c ∈ Q ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨Q.mul_mem (Q.inv_mem (hUQ u.2)) hc, hcen⟩
    have e : c = (u : G) * ((u : G)⁻¹ * c) := by group
    rw [e]
    exact Subgroup.mul_mem_sup u.2 hmem
  have hdiff : ∀ x (hx : x ∈ Q) y (hy : y ∈ Q) (g : A6Coc.Γ),
      δ (x⁻¹ * y) (Q.mul_mem (Q.inv_mem hx) hy) g = δ y hy g - δ x hx g := by
    intro x hx y hy g
    obtain ⟨ℓ, rfl⟩ := hαs g
    rw [hδα (x⁻¹ * y) (Q.mul_mem (Q.inv_mem hx) hy), hδα y hy, hδα x hx]
    set w : ↥(blockU L) := cU y hy ℓ * (cU x hx ℓ)⁻¹ with hwdef
    have hw' : x⁻¹ * (w : G) * x⁻¹⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.mp (hQUn (Q.inv_mem hx)) _).mp w.2
    have e : cU (x⁻¹ * y) (Q.mul_mem (Q.inv_mem hx) hy) ℓ = ⟨_, hw'⟩ := by
      apply Subtype.ext
      show ⁅x⁻¹ * y, (ℓ : G)⁆ = x⁻¹ * (⁅y, (ℓ : G)⁆ * ⁅x, (ℓ : G)⁆⁻¹) * x⁻¹⁻¹
      simp only [commutatorElement_def]
      group
    have hz : x⁻¹ * (w : G) * x⁻¹⁻¹ * (w : G)⁻¹ ∈ blockZ L := by
      refine ⟨Subgroup.mul_mem _ hw' (Subgroup.inv_mem _ w.2), ?_⟩
      have := hQQ x⁻¹ (Q.inv_mem hx) w (hUQ w.2)
      rwa [commutatorElement_def] at this
    rw [e, hβeq ⟨_, hw'⟩ w hz, hwdef, map_mul, map_inv, toAdd_mul, toAdd_inv, sub_eq_add_neg]
  refine relIndex_le_two_of fun x hx y hy hxH hyH => ?_
  have hx' : ¬ ∃ u₀, ∀ g : A6Coc.Γ, δ x hx g = u₀ - heartAct 6 (g : Equiv.Perm (Fin 6)) u₀ :=
    fun h => hxH (hin x hx h)
  have hy' : ¬ ∃ u₀, ∀ g : A6Coc.Γ, δ y hy g = u₀ - heartAct 6 (g : Equiv.Perm (Fin 6)) u₀ :=
    fun h => hyH (hin y hy h)
  obtain ⟨u₀, hu₀⟩ := A6Coc.a6_cocycle (hδc y hy) (hδc x hx) hy' hx'
  exact hin (x⁻¹ * y) (Q.mul_mem (Q.inv_mem hx) hy)
    ⟨u₀, fun g => by rw [hdiff x hx y hy]; exact hu₀ g⟩

end A6Block

end CFSG.Quasithin.H13
