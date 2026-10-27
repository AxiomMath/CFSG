module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21 Subgroup

variable {H : Type} [Group H] [Finite H]

theorem commute_of_mem_closure_comm {s : Set H} (hc : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x)
    {g h : H} (hg : g ∈ closure s) (hh : h ∈ closure s) : g * h = h * g := by
  letI : CommGroup (closure s) := closureCommGroupOfComm (fun x hx y hy _ => hc x hx y hy)
  have := mul_comm (⟨g, hg⟩ : closure s) ⟨h, hh⟩
  exact congrArg Subtype.val this

theorem pow_three_of_mem_closure_comm {s : Set H} (hc : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x)
    (h3 : ∀ x ∈ s, x ^ 3 = 1) {g : H} (hg : g ∈ closure s) : g ^ 3 = 1 := by
  refine closure_induction (p := fun g _ => g ^ 3 = 1) (fun x hx => h3 x hx) (one_pow 3)
    (fun x y hx hy h1 h2 => ?_) (fun x hx h1 => by rw [inv_pow, h1, inv_one]) hg
  have hcm : Commute x y := commute_of_mem_closure_comm hc hx hy
  rw [hcm.mul_pow, h1, h2, one_mul]

theorem isPGroup_three_closure_comm {s : Set H} (hc : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x)
    (h3 : ∀ x ∈ s, x ^ 3 = 1) : IsPGroup 3 (closure s) := fun g =>
  ⟨1, Subtype.ext (by simpa using pow_three_of_mem_closure_comm hc h3 g.2)⟩

theorem exists_isElemAb_of_card_le {s : Set H} (hc : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x)
    (h3 : ∀ x ∈ s, x ^ 3 = 1) {k : ℕ} (hk : 3 ^ k ≤ Nat.card (closure s)) :
    ∃ T : Subgroup H, T ≤ closure s ∧ IsElemAb 3 k T := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm⟩ := (isPGroup_three_closure_comm hc h3).exists_card_eq
  have hkm : k ≤ m := by
    rw [hm] at hk
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hk
  obtain ⟨T', hT'⟩ := Sylow.exists_subgroup_card_pow_prime (G := closure s) 3
    (n := k) (by rw [hm]; exact pow_dvd_pow 3 hkm)
  refine ⟨T'.map (closure s).subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · have hT : ∀ x ∈ T'.map (closure s).subtype, ∀ y ∈ T'.map (closure s).subtype,
        x * y = y * x := by
      rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩
      exact commute_of_mem_closure_comm hc x.2 y.2
    have hc3 : ∀ x ∈ T'.map (closure s).subtype, x ^ 3 = 1 := by
      rintro _ ⟨x, -, rfl⟩
      exact pow_three_of_mem_closure_comm hc h3 x.2
    exact
      { is_comm := ⟨fun a b => Subtype.ext (hT a a.2 b b.2)⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
          Subtype.ext (hc3 x x.2) }
  · rw [Subgroup.card_map_of_injective (closure s).subtype_injective, hT']

theorem three_mul_card_le {X Y : Subgroup H} (hY : IsPGroup 3 Y) (hXY : X < Y) :
    3 * Nat.card X ≤ Nat.card Y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX : IsPGroup 3 X := hY.to_le hXY.le
  obtain ⟨a, ha⟩ := hX.exists_card_eq
  obtain ⟨b, hb⟩ := hY.exists_card_eq
  have hne : Nat.card X ≠ Nat.card Y := fun h =>
    hXY.ne (Subgroup.eq_of_le_of_card_ge hXY.le h.ge)
  have hlt : a < b := by
    have hle : a ≤ b := by
      have := Subgroup.card_le_of_le hXY.le
      rw [ha, hb] at this
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
    rcases hle.lt_or_eq with h | h
    · exact h
    · exact absurd (by rw [ha, hb, h]) hne
  rw [ha, hb, ← pow_succ']
  exact Nat.pow_le_pow_right (by norm_num) hlt

theorem nine_le_card_closure_pair {x y : H} (hxy : x * y = y * x) (hx : orderOf x = 3)
    (hy3 : y ^ 3 = 1) (hy : y ∉ zpowers x) : 9 ≤ Nat.card (closure ({x, y} : Set H)) := by
  have hc : ∀ a ∈ ({x, y} : Set H), ∀ b ∈ ({x, y} : Set H), a * b = b * a := by
    rintro a (rfl | rfl) b (rfl | rfl) <;> first | rfl | exact hxy | exact hxy.symm
  have h3 : ∀ a ∈ ({x, y} : Set H), a ^ 3 = 1 := by
    rintro a (rfl | rfl)
    · rw [← hx]; exact pow_orderOf_eq_one a
    · exact hy3
  have hlt : zpowers x < closure ({x, y} : Set H) := by
    refine lt_of_le_of_ne ((zpowers_le).2 (subset_closure (by simp))) fun h => hy ?_
    rw [h]; exact subset_closure (by simp)
  have := three_mul_card_le (isPGroup_three_closure_comm hc h3) hlt
  rw [Nat.card_zpowers, hx] at this
  omega

theorem twentyseven_le_card_closure_triple {x y z : H} (hxy : x * y = y * x) (hxz : x * z = z * x)
    (hyz : y * z = z * y) (hx : orderOf x = 3) (hy3 : y ^ 3 = 1) (hz3 : z ^ 3 = 1)
    (hy : y ∉ zpowers x) (hz : z ∉ closure ({x, y} : Set H)) :
    27 ≤ Nat.card (closure ({x, y, z} : Set H)) := by
  have hc : ∀ a ∈ ({x, y, z} : Set H), ∀ b ∈ ({x, y, z} : Set H), a * b = b * a := by
    rintro a (rfl | rfl | rfl) b (rfl | rfl | rfl) <;>
      first
        | rfl
        | exact hxy
        | exact hxy.symm
        | exact hxz
        | exact hxz.symm
        | exact hyz
        | exact hyz.symm
  have h3 : ∀ a ∈ ({x, y, z} : Set H), a ^ 3 = 1 := by
    rintro a (rfl | rfl | rfl)
    · rw [← hx]; exact pow_orderOf_eq_one a
    · exact hy3
    · exact hz3
  have hlt : closure ({x, y} : Set H) < closure ({x, y, z} : Set H) := by
    refine lt_of_le_of_ne (closure_mono (by intro a ha; simp at ha ⊢; tauto)) fun h => hz ?_
    rw [h]; exact subset_closure (by simp)
  have := three_mul_card_le (isPGroup_three_closure_comm hc h3) hlt
  have h9 := nine_le_card_closure_pair hxy hx hy3 hy
  omega

theorem false_of_fixed_triple {β : MulAut H}
    (hno : ∀ T : Subgroup H, (∀ t ∈ T, β t = t) → ¬ IsElemAb 3 3 T) {x y z : H}
    (hxy : x * y = y * x) (hxz : x * z = z * x) (hyz : y * z = z * y) (hx : orderOf x = 3)
    (hy3 : y ^ 3 = 1) (hz3 : z ^ 3 = 1) (hy : y ∉ zpowers x)
    (hz : z ∉ closure ({x, y} : Set H)) (fx : β x = x) (fy : β y = y) (fz : β z = z) : False := by
  have hc : ∀ a ∈ ({x, y, z} : Set H), ∀ b ∈ ({x, y, z} : Set H), a * b = b * a := by
    rintro a (rfl | rfl | rfl) b (rfl | rfl | rfl) <;>
      first
        | rfl
        | exact hxy
        | exact hxy.symm
        | exact hxz
        | exact hxz.symm
        | exact hyz
        | exact hyz.symm
  have h3 : ∀ a ∈ ({x, y, z} : Set H), a ^ 3 = 1 := by
    rintro a (rfl | rfl | rfl)
    · rw [← hx]; exact pow_orderOf_eq_one a
    · exact hy3
    · exact hz3
  obtain ⟨T, hTle, hT⟩ := exists_isElemAb_of_card_le (k := 3) hc h3
    (by simpa using twentyseven_le_card_closure_triple hxy hxz hyz hx hy3 hz3 hy hz)
  refine hno T (fun t ht => ?_) hT
  have hfix : closure ({x, y, z} : Set H) ≤ β.toMonoidHom.eqLocus (MonoidHom.id H) := by
    rw [closure_le]
    rintro a (rfl | rfl | rfl)
    · exact fx
    · exact fy
    · exact fz
  exact hfix (hTle ht)

end CFSG.RankThree.PartTwo.Sec21.FF79
