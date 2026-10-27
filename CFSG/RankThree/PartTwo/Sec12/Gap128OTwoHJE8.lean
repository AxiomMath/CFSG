module

public import CFSG.Sporadic.Bridge.J2Native

public section

namespace CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJ

open CFSG CFSG.Blueprint

abbrev E8 : Type := Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)

theorem e8_sq : ∀ a : E8, a ^ 2 = 1 := by decide

theorem card_e8 : Nat.card E8 = 8 := by
  rw [Nat.card_eq_fintype_card]
  rfl

theorem zmodTwo_cases : ∀ x : Multiplicative (ZMod 2), x = 1 ∨ x = Multiplicative.ofAdd 1 := by
  decide

theorem mem_zpowers_ofAdd_one (x : Multiplicative (ZMod 2)) :
    x ∈ Subgroup.zpowers (Multiplicative.ofAdd (1 : ZMod 2)) := by
  rcases zmodTwo_cases x with rfl | rfl
  · exact Subgroup.one_mem _
  · exact Subgroup.mem_zpowers _

theorem orderOf_ofAdd_one : orderOf (Multiplicative.ofAdd (1 : ZMod 2)) = 2 :=
  orderOf_eq_prime (by decide) (by decide)

noncomputable def zmodTwoHom {G : Type*} [Group G] {a : G} (ha : a ^ 2 = 1) :
    Multiplicative (ZMod 2) →* G :=
  monoidHomOfForallMemZpowers mem_zpowers_ofAdd_one
    (by rw [orderOf_ofAdd_one]; exact orderOf_dvd_of_pow_eq_one ha)

theorem zmodTwoHom_gen {G : Type*} [Group G] {a : G} (ha : a ^ 2 = 1) :
    zmodTwoHom ha (Multiplicative.ofAdd 1) = a :=
  monoidHomOfForallMemZpowers_apply_gen _ _

theorem zmodTwoHom_cases {G : Type*} [Group G] {a : G} (ha : a ^ 2 = 1)
    (x : Multiplicative (ZMod 2)) : zmodTwoHom ha x = 1 ∨ zmodTwoHom ha x = a := by
  rcases zmodTwo_cases x with rfl | rfl
  · exact Or.inl (map_one _)
  · exact Or.inr (zmodTwoHom_gen ha)

theorem commute_zmodTwoHom {G : Type*} [Group G] {a b : G} (ha : a ^ 2 = 1)
    (hab : Commute b a) (x : Multiplicative (ZMod 2)) : Commute b (zmodTwoHom ha x) := by
  rcases zmodTwoHom_cases ha x with h | h <;> rw [h]
  · exact Commute.one_right b
  · exact hab

theorem exists_injective_e8 {G : Type*} [Group G] {a b c : G} (ha : a ^ 2 = 1)
    (hb : b ^ 2 = 1) (hc : c ^ 2 = 1) (hab : a * b = b * a) (hac : a * c = c * a)
    (hbc : b * c = c * b) (h₁ : a ≠ 1) (h₂ : b ≠ 1) (h₃ : c ≠ 1) (h₄ : a * b ≠ 1)
    (h₅ : a * c ≠ 1) (h₆ : b * c ≠ 1) (h₇ : a * b * c ≠ 1) :
    ∃ ι : E8 →* G, Function.Injective ι := by
  have cbc : ∀ m n, Commute (zmodTwoHom hb m) (zmodTwoHom hc n) := fun m n => by
    rcases zmodTwoHom_cases hb m with h | h <;> rw [h]
    · exact Commute.one_left _
    · exact commute_zmodTwoHom hc hbc n
  let fbc := (zmodTwoHom hb).noncommCoprod (zmodTwoHom hc) cbc
  have cabc : ∀ m n, Commute (zmodTwoHom ha m) (fbc n) := fun m n => by
    rcases zmodTwoHom_cases ha m with h | h <;> rw [h]
    · exact Commute.one_left _
    · exact (commute_zmodTwoHom hb hab n.1).mul_right (commute_zmodTwoHom hc hac n.2)
  refine ⟨(zmodTwoHom ha).noncommCoprod fbc cabc, ?_⟩
  rw [injective_iff_map_eq_one]
  rintro ⟨x, y, z⟩ h
  simp only [fbc, MonoidHom.noncommCoprod_apply] at h
  rcases zmodTwo_cases x with rfl | rfl <;> rcases zmodTwo_cases y with rfl | rfl <;>
    rcases zmodTwo_cases z with rfl | rfl <;>
    simp only [map_one, zmodTwoHom_gen, one_mul, mul_one] at h
  · rfl
  · exact absurd h h₃
  · exact absurd h h₂
  · exact absurd h h₆
  · exact absurd h h₁
  · exact absurd h h₅
  · exact absurd h h₄
  · exact absurd (by rw [mul_assoc]; exact h) h₇

section Native

open CFSG.Sporadic.Bridge.J2

@[expose] def e8L₂ : List (List ℕ) := mulL mP2c mP2c

@[expose] def e8L₃ : List (List ℕ) := mulL (mulL mP2b mP2a) mP2b

theorem wfM_mP2 : wfM mP2a = true ∧ wfM mP2b = true ∧ wfM mP2c = true := by decide +kernel

theorem wfM_e8L₂ : wfM e8L₂ = true := wfM_mulL wfM_mP2.2.2

theorem wfM_e8L₃ : wfM e8L₃ = true := wfM_mulL (wfM_mulL wfM_mP2.2.1)

theorem e8L_sq : mulL mP2a mP2a = idL ∧ mulL e8L₂ e8L₂ = idL ∧ mulL e8L₃ e8L₃ = idL := by
  decide +kernel

theorem e8L_comm : mulL mP2a e8L₂ = mulL e8L₂ mP2a ∧ mulL mP2a e8L₃ = mulL e8L₃ mP2a ∧
    mulL e8L₂ e8L₃ = mulL e8L₃ e8L₂ := by
  decide +kernel

theorem e8L_ne :
    toM mP2a 0 0 ≠ (1 : Matrix (Fin 14) (Fin 14) (ZMod 5)) 0 0 ∧
    toM e8L₂ 0 1 ≠ (1 : Matrix (Fin 14) (Fin 14) (ZMod 5)) 0 1 ∧
    toM e8L₃ 0 0 ≠ (1 : Matrix (Fin 14) (Fin 14) (ZMod 5)) 0 0 ∧
    toM (mulL mP2a e8L₂) 0 0 ≠ (1 : Matrix (Fin 14) (Fin 14) (ZMod 5)) 0 0 ∧
    toM (mulL mP2a e8L₃) 0 0 ≠ (1 : Matrix (Fin 14) (Fin 14) (ZMod 5)) 0 0 ∧
    toM (mulL e8L₂ e8L₃) 0 0 ≠ (1 : Matrix (Fin 14) (Fin 14) (ZMod 5)) 0 0 ∧
    toM (mulL (mulL mP2a e8L₂) e8L₃) 0 1 ≠ (1 : Matrix (Fin 14) (Fin 14) (ZMod 5)) 0 1 := by
  decide +kernel

noncomputable def e8G₁ : GL (Fin 14) (ZMod 5) := CFSG.Sporadic.Bridge.wordProd natU wP2a

noncomputable def e8G₂ : GL (Fin 14) (ZMod 5) :=
  CFSG.Sporadic.Bridge.wordProd natU wP2c * CFSG.Sporadic.Bridge.wordProd natU wP2c

noncomputable def e8G₃ : GL (Fin 14) (ZMod 5) :=
  CFSG.Sporadic.Bridge.wordProd natU wP2b * CFSG.Sporadic.Bridge.wordProd natU wP2a *
    CFSG.Sporadic.Bridge.wordProd natU wP2b

theorem e8G₁_mem : e8G₁ ∈ seedGroup := natWord_mem _

theorem e8G₂_mem : e8G₂ ∈ seedGroup := mul_mem (natWord_mem _) (natWord_mem _)

theorem e8G₃_mem : e8G₃ ∈ seedGroup :=
  mul_mem (mul_mem (natWord_mem _) (natWord_mem _)) (natWord_mem _)

theorem val_e8G₁ : (e8G₁ : Matrix (Fin 14) (Fin 14) (ZMod 5)) = toM mP2a :=
  val_natWord lwordL_sylow.1

theorem val_e8G₂ : (e8G₂ : Matrix (Fin 14) (Fin 14) (ZMod 5)) = toM e8L₂ := by
  rw [e8G₂, Units.val_mul, val_natWord lwordL_sylow.2.2.1, e8L₂,
    toM_mulL wfM_mP2.2.2 wfM_mP2.2.2]

theorem val_e8G₃ : (e8G₃ : Matrix (Fin 14) (Fin 14) (ZMod 5)) = toM e8L₃ := by
  rw [e8G₃, Units.val_mul, Units.val_mul, val_natWord lwordL_sylow.1,
    val_natWord lwordL_sylow.2.1, e8L₃, toM_mulL (wfM_mulL wfM_mP2.2.1) wfM_mP2.2.1,
    toM_mulL wfM_mP2.2.1 wfM_mP2.1]

theorem gl_sq_of_val {x : GL (Fin 14) (ZMod 5)} {X : List (List ℕ)} (hX : wfM X = true)
    (hXX : mulL X X = idL) (hx : (x : Matrix (Fin 14) (Fin 14) (ZMod 5)) = toM X) :
    x ^ 2 = 1 :=
  Units.ext (by rw [pow_two, Units.val_mul, hx, ← toM_mulL hX hX, hXX, toM_idL, Units.val_one])

theorem coe_mem_seedMonoid {g : GL (Fin 14) (ZMod 5)} (hg : g ∈ seedGroup) :
    (g : Matrix (Fin 14) (Fin 14) (ZMod 5)) ∈
      NativeSporadic.seedMonoid 5 14 1 NativeSporadic.J2Seed1 NativeSporadic.J2Seed2 := by
  rw [seedMonoid_eq]
  have h1 : g ∈ Submonoid.closure ({uA, uB} : Set (GL (Fin 14) (ZMod 5))) := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hg
  have h2 := Submonoid.mem_map_of_mem (Units.coeHom (Matrix (Fin 14) (Fin 14) (ZMod 5))) h1
  rw [MonoidHom.map_mclosure, Set.image_pair] at h2
  exact h2

@[expose] noncomputable def seedUnit (g : GL (Fin 14) (ZMod 5)) (hg : g ∈ seedGroup)
    (h2 : g ^ 2 = 1) : NativeSporadic.J2 :=
  Units.ofPowEqOne (⟨(g : Matrix (Fin 14) (Fin 14) (ZMod 5)), coe_mem_seedMonoid hg⟩ :
    NativeSporadic.seedMonoid 5 14 1 NativeSporadic.J2Seed1 NativeSporadic.J2Seed2) 2
    (Subtype.ext (by simpa using congrArg Units.val h2)) two_ne_zero

@[expose] noncomputable def j2Val : NativeSporadic.J2 →* Matrix (Fin 14) (Fin 14) (ZMod 5) :=
  (NativeSporadic.seedMonoid 5 14 1 NativeSporadic.J2Seed1 NativeSporadic.J2Seed2).subtype.comp
    (Units.coeHom _)

theorem j2Val_injective : Function.Injective j2Val :=
  fun _ _ h => Units.ext (Subtype.ext h)

theorem exists_injective_e8_j2 : ∃ ι : E8 →* NativeSporadic.J2, Function.Injective ι := by
  have s₁ := gl_sq_of_val wfM_mP2.1 e8L_sq.1 val_e8G₁
  have s₂ := gl_sq_of_val wfM_e8L₂ e8L_sq.2.1 val_e8G₂
  have s₃ := gl_sq_of_val wfM_e8L₃ e8L_sq.2.2 val_e8G₃
  set a := seedUnit e8G₁ e8G₁_mem s₁ with ha
  set b := seedUnit e8G₂ e8G₂_mem s₂ with hb
  set c := seedUnit e8G₃ e8G₃_mem s₃ with hc
  have va : j2Val a = toM mP2a := val_e8G₁
  have vb : j2Val b = toM e8L₂ := val_e8G₂
  have vc : j2Val c = toM e8L₃ := val_e8G₃
  have sq : ∀ {x : NativeSporadic.J2} {X : List (List ℕ)}, wfM X = true → mulL X X = idL →
      j2Val x = toM X → x ^ 2 = 1 := fun hX hXX hx => j2Val_injective (by
    rw [map_pow, pow_two, hx, ← toM_mulL hX hX, hXX, toM_idL, map_one])
  have cm : ∀ {x y : NativeSporadic.J2} {X Y : List (List ℕ)}, wfM X = true → wfM Y = true →
      mulL X Y = mulL Y X → j2Val x = toM X → j2Val y = toM Y → x * y = y * x :=
    fun hX hY hXY hx hy => j2Val_injective (by
      rw [map_mul, map_mul, hx, hy, ← toM_mulL hX hY, ← toM_mulL hY hX, hXY])
  have ne : ∀ {x : NativeSporadic.J2} (i j : Fin 14),
      j2Val x i j ≠ (1 : Matrix (Fin 14) (Fin 14) (ZMod 5)) i j → x ≠ 1 := by
    rintro x i j h rfl
    rw [map_one] at h
    exact h rfl
  obtain ⟨n₁, n₂, n₃, n₄, n₅, n₆, n₇⟩ := e8L_ne
  refine exists_injective_e8 (sq wfM_mP2.1 e8L_sq.1 va) (sq wfM_e8L₂ e8L_sq.2.1 vb)
    (sq wfM_e8L₃ e8L_sq.2.2 vc) (cm wfM_mP2.1 wfM_e8L₂ e8L_comm.1 va vb)
    (cm wfM_mP2.1 wfM_e8L₃ e8L_comm.2.1 va vc) (cm wfM_e8L₂ wfM_e8L₃ e8L_comm.2.2 vb vc)
    (ne 0 0 (by rw [va]; exact n₁)) (ne 0 1 (by rw [vb]; exact n₂))
    (ne 0 0 (by rw [vc]; exact n₃))
    (ne 0 0 (by rw [map_mul, va, vb, ← toM_mulL wfM_mP2.1 wfM_e8L₂]; exact n₄))
    (ne 0 0 (by rw [map_mul, va, vc, ← toM_mulL wfM_mP2.1 wfM_e8L₃]; exact n₅))
    (ne 0 0 (by rw [map_mul, vb, vc, ← toM_mulL wfM_e8L₂ wfM_e8L₃]; exact n₆))
    (ne 0 1 (by
      rw [map_mul, map_mul, va, vb, vc, ← toM_mulL wfM_mP2.1 wfM_e8L₂,
        ← toM_mulL (wfM_mulL wfM_mP2.1) wfM_e8L₃]
      exact n₇))

end Native

theorem exists_injective_lift {L J A : Type*} [Group L] [Finite L] [Group J] [Group A]
    [Finite A] (π : L →* J) (hπ : Function.Surjective π) (hodd : ¬ 2 ∣ Nat.card π.ker)
    (hA : Nat.card A = 8) (ι : A →* J) (hι : Function.Injective ι) :
    ∃ ι' : A →* L, Function.Injective ι' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := ι.range.comap π with hM
  set f : M →* J := π.comp M.subtype with hf
  have hrange : f.range = ι.range := by
    apply le_antisymm
    · rintro _ ⟨m, rfl⟩
      exact m.2
    · intro y hy
      obtain ⟨x, rfl⟩ := hπ y
      exact ⟨⟨x, hy⟩, rfl⟩
  have : Finite ι.range := Finite.of_surjective _ ι.rangeRestrict_surjective
  have hιcard : Nat.card ι.range = 8 := by
    rw [← hA]
    exact (Nat.card_congr (MonoidHom.ofInjective hι).toEquiv).symm
  have h8 : 2 ^ 3 ∣ Nat.card M := by
    rw [← Subgroup.card_ker_mul_card_range f, hrange, hιcard]
    exact Dvd.intro_left _ rfl
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime 2 h8
  set g : P →* J := f.comp P.subtype with hg
  have hginj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxk : ((x : M) : L) ∈ π.ker := hx
    have h8 : ((x : M) : L) ^ (2 ^ 3) = 1 := by
      have h := congrArg (fun z : P => ((z : M) : L)) (hP ▸ pow_card_eq_one' (x := x))
      simpa using h
    have hk : ((x : M) : L) ^ Nat.card π.ker = 1 :=
      congrArg Subtype.val (pow_card_eq_one' (x := (⟨_, hxk⟩ : π.ker)))
    have hcop : Nat.Coprime (2 ^ 3) (Nat.card π.ker) :=
      Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
    have h1 := pow_gcd_eq_one.mpr ⟨h8, hk⟩
    rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at h1
    exact Subtype.ext (Subtype.ext h1)
  have hgrange : g.range = ι.range := by
    have hle : g.range ≤ ι.range := by
      rintro _ ⟨x, rfl⟩
      exact (x : M).2
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hιcard, show (8 : ℕ) = 2 ^ 3 by norm_num, ← hP]
    exact (Nat.card_congr (MonoidHom.ofInjective hginj).toEquiv).le
  let e : P ≃* A := (MonoidHom.ofInjective hginj).trans
    ((MulEquiv.subgroupCongr hgrange).trans (MonoidHom.ofInjective hι).symm)
  exact ⟨(M.subtype.comp P.subtype).comp e.symm.toMonoidHom,
    (Subtype.val_injective.comp Subtype.val_injective).comp e.symm.injective⟩

end CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJ
