module

public import CFSG.Quasithin.Vol2.Ch11SecU1L33A

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.L33

open CFSG.QuasithinUnique.Vol2Native.L239.L33Insp

@[expose] def delta (x : S3) : S3 := (x⁻¹).transpose

theorem card_subtype_mem_list {α : Type} [DecidableEq α] {l : List α} (h : l.Nodup) :
    Nat.card {a // a ∈ l} = l.length := by
  have e : {a // a ∈ l} ≃ ↥l.toFinset := Equiv.subtypeEquivRight fun a => by simp
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup h]

variable {G : Type} [Group G]

structure Model (L : Subgroup G) where
  f : S3 →* G
  f_inj : Function.Injective f
  mem_iff : ∀ g, g ∈ L ↔ ∃ x, f x = g
  t : G
  t_mul_t : t * t = 1
  t_not_mem : t ∉ L
  t_mul_f : ∀ x, t * f x = f (delta x) * t
  cover : ∀ g, ∃ x, g = f x ∨ g = f x * t

namespace Model

variable {L : Subgroup G} (M : Model L)

open Classical in
@[expose] noncomputable def code (g : G) : Code :=
  if g ∈ L then (rn (Function.invFun M.f g), false)
  else (rn (Function.invFun M.f (g * M.t)), true)

theorem f_mem (x : S3) : M.f x ∈ L := (M.mem_iff _).mpr ⟨x, rfl⟩

theorem f_mul_t_not_mem (x : S3) : M.f x * M.t ∉ L := fun h => M.t_not_mem (by
  have := L.mul_mem (L.inv_mem (M.f_mem x)) h
  simpa using this)

theorem code_f (x : S3) : M.code (M.f x) = (rn x, false) := by
  rw [code, ite_eq_left (M.f_mem x), Function.leftInverse_invFun M.f_inj x]

theorem code_f_mul_t (x : S3) : M.code (M.f x * M.t) = (rn x, true) := by
  rw [code, ite_eq_right (M.f_mul_t_not_mem x), mul_assoc, M.t_mul_t, mul_one,
    Function.leftInverse_invFun M.f_inj x]

theorem code_mul (g h : G) : M.code (g * h) = cmul (M.code g) (M.code h) := by
  obtain ⟨x, rfl | rfl⟩ := M.cover g <;> obtain ⟨y, rfl | rfl⟩ := M.cover h
  · rw [← map_mul, code_f, code_f, code_f, cmul, rn_mul]
    rfl
  · rw [← mul_assoc, ← map_mul, code_f_mul_t, code_f, code_f_mul_t, cmul, rn_mul]
    rfl
  · rw [mul_assoc, M.t_mul_f, ← mul_assoc, ← map_mul, code_f_mul_t, code_f_mul_t, code_f, cmul,
      rn_mul, delta, rn_inv_transpose]
    rfl
  · have h1 : M.f x * M.t * (M.f y * M.t) = M.f (x * delta y) := by
      calc M.f x * M.t * (M.f y * M.t) = M.f x * (M.t * M.f y) * M.t := by group
        _ = M.f x * (M.f (delta y) * M.t) * M.t := by rw [M.t_mul_f]
        _ = M.f x * M.f (delta y) * (M.t * M.t) := by group
        _ = M.f (x * delta y) := by rw [M.t_mul_t, mul_one, map_mul]
    rw [h1, code_f, code_f_mul_t, code_f_mul_t, cmul, rn_mul, delta, rn_inv_transpose]
    rfl

theorem code_inj : Function.Injective M.code := by
  intro g h hgh
  obtain ⟨x, rfl | rfl⟩ := M.cover g <;> obtain ⟨y, rfl | rfl⟩ := M.cover h
  · rw [code_f, code_f, Prod.mk.injEq] at hgh
    rw [rn_inj hgh.1]
  · rw [code_f, code_f_mul_t, Prod.mk.injEq] at hgh
    exact absurd hgh.2 Bool.false_ne_true
  · rw [code_f_mul_t, code_f, Prod.mk.injEq] at hgh
    exact absurd hgh.2 (by decide : true ≠ false)
  · rw [code_f_mul_t, code_f_mul_t, Prod.mk.injEq] at hgh
    rw [rn_inj hgh.1]

theorem code_one : M.code 1 = cone := by
  rw [← M.f.map_one, code_f, rn_one]
  rfl

theorem mem_iff_code (g : G) : g ∈ L ↔ (M.code g).2 = false := by
  obtain ⟨x, rfl | rfl⟩ := M.cover g
  · rw [code_f]
    exact ⟨fun _ => rfl, fun _ => M.f_mem x⟩
  · rw [code_f_mul_t]
    exact ⟨fun h => absurd h (M.f_mul_t_not_mem x), fun h => absurd h (by decide : true ≠ false)⟩

theorem exists_code {c : Code} (hc : c.1 ∈ nL) : ∃ g, M.code g = c := by
  obtain ⟨hlt, hdet⟩ := mem_nL.mp hc
  obtain ⟨n, ε⟩ := c
  cases ε
  · exact ⟨M.f (ofN n hdet), by rw [code_f, rn_ofN n hlt hdet]⟩
  · exact ⟨M.f (ofN n hdet) * M.t, by rw [code_f_mul_t, rn_ofN n hlt hdet]⟩

theorem code_t : M.code M.t = cdelta := by
  have h := M.code_f_mul_t 1
  rwa [map_one, one_mul, rn_one] at h

theorem commute_iff (g h : G) : g * h = h * g ↔ cmul (M.code g) (M.code h) =
    cmul (M.code h) (M.code g) := by
  rw [← code_mul, ← code_mul]
  exact ⟨fun e => by rw [e], fun e => M.code_inj e⟩

@[expose] noncomputable def sub (l : List Code) (h1 : cone ∈ l)
    (hmul : ∀ a ∈ l, ∀ b ∈ l, cmul a b ∈ l) (hinv : ∀ a ∈ l, ∃ b ∈ l, cmul a b = cone)
    (hval : ∀ a ∈ l, a.1 ∈ nL) : Subgroup G where
  carrier := {g | M.code g ∈ l}
  one_mem' := by
    show M.code 1 ∈ l
    rw [code_one]
    exact h1
  mul_mem' {a b} ha hb := by
    show M.code (a * b) ∈ l
    rw [code_mul]
    exact hmul _ ha _ hb
  inv_mem' {a} ha := by
    obtain ⟨b, hb, hab⟩ := hinv _ ha
    obtain ⟨h, hh⟩ := M.exists_code (hval b hb)
    have h1 : a * h = 1 := M.code_inj (by rw [code_mul, hh, code_one, hab])
    show M.code a⁻¹ ∈ l
    rw [inv_eq_of_mul_eq_one_right h1, hh]
    exact hb

theorem card_sub {l : List Code} {h1 hmul hinv hval} (hnd : l.Nodup) :
    Nat.card (M.sub l h1 hmul hinv hval) = l.length := by
  rw [← card_subtype_mem_list hnd]
  refine Nat.card_congr (Equiv.ofBijective (fun g => ⟨M.code g, g.2⟩) ⟨fun g h e => ?_, ?_⟩)
  · exact Subtype.ext (M.code_inj (congrArg Subtype.val e))
  · rintro ⟨c, hc⟩
    obtain ⟨g, hg⟩ := M.exists_code (hval c hc)
    exact ⟨⟨g, show M.code g ∈ l by rw [hg]; exact hc⟩, Subtype.ext hg⟩

end Model

end CFSG.Quasithin.Vol2.Ch11.SecU1.L33
