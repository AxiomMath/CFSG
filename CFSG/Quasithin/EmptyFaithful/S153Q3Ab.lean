module

public import CFSG.Quasithin.EmptyFaithful.S153Q3Aa

public section

namespace CFSG.Quasithin

namespace S153Q

namespace Q3A

open scoped Pointwise

section NoFinite

variable {W : Type} [CommGroup W] {z : MulAut W}

@[expose] def fixSub (x : MulAut W) : Subgroup W where
  carrier := {w | x w = w}
  one_mem' := map_one x
  mul_mem' := fun {a b} (ha : x a = a) (hb : x b = b) => by
    show x (a * b) = a * b
    rw [map_mul, ha, hb]
  inv_mem' := fun {a} (ha : x a = a) => by
    show x a⁻¹ = a⁻¹
    rw [map_inv, ha]

theorem x5_apply {x : MulAut W} (hx : x ^ 5 = 1) (w : W) : x (x (x (x (x w)))) = w := by
  have h := congrArg (fun g : MulAut W => g w) hx
  simpa [pow_succ, MulAut.mul_apply] using h

theorem iterate5_eq_id {x : MulAut W} (hx : x ^ 5 = 1) : (⇑x)^[5] = id := by
  funext w
  exact x5_apply hx w

theorem mem_smul_iff (g : MulAut W) (H : Subgroup W) (w : W) : w ∈ g • H ↔ g⁻¹ w ∈ H := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

theorem card_smul (g : MulAut W) (H : Subgroup W) : Nat.card ↥(g • H) = Nat.card ↥H := by
  rw [Subgroup.pointwise_smul_def]
  exact Subgroup.card_map_of_injective (fun a b (h : g • a = g • b) => g.injective h)

theorem apply_comm {g : MulAut W} (hg : g * z = z * g) (v : W) : g (z v) = z (g v) := by
  have := congrArg (fun k : MulAut W => k v) hg
  simpa only [MulAut.mul_apply] using this

theorem z_mem_fixSub {x : MulAut W} (hxz : x * z = z * x) {w : W} (hw : w ∈ fixSub x) :
    z w ∈ fixSub x := by
  show x (z w) = z w
  rw [apply_comm hxz, show x w = w from hw]

theorem iter_val {x : MulAut W} {H : Subgroup W} (hH : ∀ h ∈ H, x h ∈ H) (n : ℕ) (a : H) :
    (((fun h : H => (⟨x h, hH h h.2⟩ : H))^[n] a : H) : W) = (⇑x)^[n] (a : W) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]

end NoFinite

section Mod5

variable {W : Type} [CommGroup W] [Finite W] {z : MulAut W}

theorem card_modEq_fixed {α : Type*} [Finite α] (f : α → α) (hf : f^[5] = id) :
    Nat.card α ≡ Nat.card {a // f a = a} [MOD 5] := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have hp : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let g : Function.End α := f
  have h5 : g ^ 5 ^ 1 = (1 : Function.End α) := by
    rw [pow_one]
    funext a
    exact congrFun hf a
  have h := Equiv.Perm.card_fixedPoints_modEq (α := α) (f := g) (p := 5) (n := 1) h5
  have e : Nat.card {a // f a = a} = Nat.card ↑(Function.fixedPoints g) :=
    Nat.card_congr (Equiv.refl _)
  rw [e, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact h

theorem card_modEq_inf (x : MulAut W) (hx : x ^ 5 = 1) (H : Subgroup W) (hH : ∀ h ∈ H, x h ∈ H) :
    Nat.card ↥H ≡ Nat.card ↥(H ⊓ fixSub x) [MOD 5] := by
  let f : H → H := fun h => ⟨x h, hH h h.2⟩
  have hf : f^[5] = id := by
    funext a
    apply Subtype.ext
    rw [iter_val hH, iterate5_eq_id hx]
    rfl
  have h := card_modEq_fixed f hf
  have e : Nat.card {a : H // f a = a} = Nat.card ↥(H ⊓ fixSub x) :=
    Nat.card_congr
      { toFun := fun a => ⟨a.1.1, a.1.2, congrArg Subtype.val a.2⟩
        invFun := fun b => ⟨⟨b.1, b.2.1⟩, Subtype.ext b.2.2⟩
        left_inv := fun a => rfl
        right_inv := fun b => rfl }
  rwa [e] at h

theorem card_fixSub (hWc : Nat.card W = 2 ^ 6) {x : MulAut W} (hx : x ^ 5 = 1) (hx1 : x ≠ 1) :
    Nat.card ↥(fixSub x) = 4 := by
  have h := card_modEq_inf x hx ⊤ (fun _ _ => Subgroup.mem_top _)
  rw [top_inf_eq, Subgroup.card_top, hWc] at h
  have hd : Nat.card ↥(fixSub x) ∣ 2 ^ 6 := by
    have := Subgroup.card_subgroup_dvd_card (fixSub x)
    rwa [hWc] at this
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  rw [hk'] at h ⊢
  interval_cases k
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · rfl
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exfalso
    apply hx1
    have htop : fixSub x = ⊤ := by
      rw [← Subgroup.card_eq_iff_eq_top, hk', hWc]
    ext w
    have : w ∈ fixSub x := htop ▸ Subgroup.mem_top w
    exact this

theorem le_fixSub_of_inv {x : MulAut W} (hx : x ^ 5 = 1) {o : Subgroup W} (ho : Nat.card ↥o = 4)
    (hinv : ∀ w ∈ o, x w ∈ o) : o ≤ fixSub x := by
  have h := card_modEq_inf x hx o hinv
  have hd : Nat.card ↥(o ⊓ fixSub x) ∣ 4 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : o ⊓ fixSub x ≤ o)
    rwa [ho] at this
  have h4 : Nat.card ↥(o ⊓ fixSub x) = 4 := by
    rw [ho] at h
    have hle : Nat.card ↥(o ⊓ fixSub x) ≤ 4 := Nat.le_of_dvd (by norm_num) hd
    generalize Nat.card ↥(o ⊓ fixSub x) = n at h hd hle ⊢
    interval_cases n <;> first | rfl | (exfalso; revert h hd; decide)
  have heq : o ⊓ fixSub x = o :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [ho, h4])
  exact heq.symm.le.trans inf_le_right

theorem smul_eq_of_le {g : MulAut W} {H : Subgroup W} (h : ∀ w ∈ H, g w ∈ H) : g • H = H := by
  apply Subgroup.eq_of_le_of_card_ge
  · intro w hw
    obtain ⟨s, hs, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hw
    exact h s hs
  · rw [card_smul]

end Mod5

section Perfect

variable {W : Type} [CommGroup W] [Finite W] {z : MulAut W}

theorem orbit_choice (hz3 : z ^ 3 = 1) (hfpf : ∀ w : W, z w = w → w = 1) {o : Subgroup W}
    (ho : IsPt z o) {k : MulAut W} (hko : ∀ u ∈ o, k u ∈ o) {u : W} (hu : u ∈ o) (hu1 : u ≠ 1) :
    k u = u ∨ k u = z u ∨ k u = z (z u) := by
  rcases (mem_pt_iff hz3 hfpf ho hu hu1 (k u)).mp (hko u hu) with h1 | h1 | h1 | h1
  · exact absurd (k.injective (h1.trans (map_one k).symm)) hu1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h1)

theorem comm_on_pt (hz3 : z ^ 3 = 1) (hfpf : ∀ w : W, z w = w → w = 1) {o : Subgroup W}
    (ho : IsPt z o) {g h : MulAut W} (hg : g * z = z * g) (hh : h * z = z * h)
    (hgo : ∀ u ∈ o, g u ∈ o) (hho : ∀ u ∈ o, h u ∈ o) : ∀ u ∈ o, g (h u) = h (g u) := by
  intro u hu
  by_cases hu1 : u = 1
  · subst hu1
    simp
  · have hgz := apply_comm hg
    have hhz := apply_comm hh
    rcases orbit_choice hz3 hfpf ho hgo hu hu1 with h1 | h1 | h1 <;>
    rcases orbit_choice hz3 hfpf ho hho hu hu1 with h2 | h2 | h2 <;>
    simp only [h1, h2, hgz, hhz]

theorem exists_not_stab {Ah : Subgroup (MulAut W)} (hperf : Ah ≤ ⁅Ah, Ah⁆) (hzA : z ∈ Ah)
    (hcent : ∀ g ∈ Ah, g * z = z * g) (hz3 : z ^ 3 = 1) (hfpf : ∀ w : W, z w = w → w = 1)
    {o : Subgroup W} (ho : IsPt z o) : ∃ g ∈ Ah, ∃ u ∈ o, g u ∉ o := by
  by_contra hcon
  push Not at hcon
  let E : Subgroup (MulAut W) :=
    { carrier := {g | ∀ u ∈ o, g u = u}
      one_mem' := fun u _ => rfl
      mul_mem' := fun {a b} ha hb u hu => by
        show a (b u) = u
        rw [hb u hu, ha u hu]
      inv_mem' := fun {a} ha u hu => by
        show a⁻¹ u = u
        calc a⁻¹ u = a⁻¹ (a u) := by rw [ha u hu]
          _ = u := MulAut.inv_apply_self _ _ _ }
  have hle : ⁅Ah, Ah⁆ ≤ E := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    show ∀ u ∈ o, (g * h * g⁻¹ * h⁻¹) u = u
    intro u hu
    have hv : g⁻¹ (h⁻¹ u) ∈ o := hcon _ (Ah.inv_mem hg) _ (hcon _ (Ah.inv_mem hh) u hu)
    have hc := comm_on_pt hz3 hfpf ho (hcent g hg) (hcent h hh) (hcon g hg) (hcon h hh) _ hv
    rw [MulAut.apply_inv_self, MulAut.apply_inv_self] at hc
    simpa only [MulAut.mul_apply] using hc
  have hz : z ∈ E := hle (hperf hzA)
  obtain ⟨w, hw, hw1⟩ : ∃ w ∈ o, w ≠ 1 := by
    by_contra hcon2
    push Not at hcon2
    have hbot : o = ⊥ := (Subgroup.eq_bot_iff_forall o).mpr hcon2
    have h1 : Nat.card ↥o = 1 := by rw [hbot]; exact Subgroup.card_bot
    have := ho.1
    omega
  exact hw1 (hfpf w (hz w hw))

end Perfect

end Q3A

end S153Q

end CFSG.Quasithin
