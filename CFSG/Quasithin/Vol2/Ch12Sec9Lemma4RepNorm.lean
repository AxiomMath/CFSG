module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4RepStmt
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4RepCodeB
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatSix
public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsHat
public import CFSG.Quasithin.Vol2.Ch12Sec8OneNine

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin GL42

namespace L1294R

variable {G : Type} [Group G]

theorem conj_eq_of_sq_conj {h x : G} {m : ℕ} (hm : Odd m) (hh : h ^ m = 1)
    (hx : h * h * x * (h * h)⁻¹ = x) : h * x * h⁻¹ = x := by
  obtain ⟨j, rfl⟩ := hm
  have hc : Commute (h * h) x := mul_inv_eq_iff_eq_mul.mp hx
  have e : h⁻¹ = (h * h) ^ j := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, ← pow_mul, ← pow_succ', hh]
  have hc' : Commute h⁻¹ x := e ▸ hc.pow_left j
  have hc'' : Commute h x := by simpa using hc'.inv_left
  rw [hc''.eq, mul_inv_cancel_right]

theorem exists_fixed_ne_one [Finite G] {T DI : Subgroup G} (hT : IsPGroup 2 T)
    (hTN : T ≤ Subgroup.normalizer (DI : Set G)) (hDI : Nat.card DI = 4) :
    ∃ p ∈ DI, p ≠ 1 ∧ ∀ t ∈ T, t * p * t⁻¹ = p := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction ↥T ↥DI := MulAction.compHom ↥DI (Subgroup.inclusion hTN)
  have hmod := hT.card_modEq_card_fixedPoints ↥DI
  rw [hDI] at hmod
  have h1 : (1 : ↥DI) ∈ MulAction.fixedPoints ↥T ↥DI := fun t =>
    show (Subgroup.inclusion hTN t) • (1 : ↥DI) = 1 from smul_one _
  obtain ⟨q, hq, hq1⟩ : ∃ q ∈ MulAction.fixedPoints ↥T ↥DI, q ≠ 1 := by
    by_contra hne
    push Not at hne
    have e : MulAction.fixedPoints ↥T ↥DI = {1} := Set.eq_singleton_iff_unique_mem.2 ⟨h1, hne⟩
    rw [e, Nat.card_unique] at hmod
    exact absurd hmod (by decide)
  refine ⟨q, q.2, fun h => hq1 (Subtype.ext h), fun t ht => ?_⟩
  have := hq ⟨t, ht⟩
  exact congrArg Subtype.val this

theorem bits_eq_zero : ∀ n : Fin 16, n.val % 2 = 0 → n.val / 2 % 2 = 0 → n.val / 4 % 2 = 0 →
    n.val / 8 % 2 = 0 → n = 0 := by
  decide

theorem pair_eq_zero {x y : G} (hx : x ≠ 1) (hy : y ≠ 1) (hxy : x * y ≠ 1) {i j : ℕ} (hi : i < 2)
    (hj : j < 2) (h : x ^ i * y ^ j = 1) : i = 0 ∧ j = 0 := by
  obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
  · obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    · exact ⟨rfl, rfl⟩
    · simp only [pow_zero, pow_one, one_mul] at h
      exact absurd h hy
  · obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    · simp only [pow_zero, pow_one, mul_one] at h
      exact absurd h hx
    · simp only [pow_one] at h
      exact absurd h hxy

theorem frame_of {V₁ V₂ DI : Subgroup G} {z b p d : G} (hz : z ∈ V₁) (hz1 : z ≠ 1)
    (hb : b ∈ V₂) (hbV₁ : b ∉ V₁) (hzV₂ : z ∈ V₂) (hV₁z : ∀ v ∈ V₁, v = 1 ∨ v = z)
    (hp : p ∈ DI) (hp1 : p ≠ 1) (hd : d ∈ DI) (hd1 : d ≠ 1) (hdp : d ≠ p)
    (hcV : ∀ x ∈ V₂, ∀ y ∈ V₂, x * y = y * x) (hcD : ∀ x ∈ DI, ∀ y ∈ DI, x * y = y * x)
    (hcVD : ∀ x ∈ V₂, ∀ y ∈ DI, x * y = y * x) (hsV : ∀ x ∈ V₂, x ^ 2 = 1)
    (hsD : ∀ x ∈ DI, x ^ 2 = 1) (hVD : V₂ ⊓ DI = ⊥) : Frame z b p d := by
  have hmem : ∀ x ∈ ({z, b, p, d} : Set G), x ∈ V₂ ∨ x ∈ DI := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Or.inl hzV₂
    · exact Or.inl hb
    · exact Or.inr hp
    · exact Or.inr hd
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy
    rcases hmem x hx with hx | hx <;> rcases hmem y hy with hy | hy
    · exact hcV x hx y hy
    · exact hcVD x hx y hy
    · exact (hcVD y hy x hx).symm
    · exact hcD x hx y hy
  · intro x hx
    rcases hmem x hx with hx | hx
    · exact hsV x hx
    · exact hsD x hx
  · intro n hn
    have hsplit : coord z b p d n = (z ^ (n.val % 2) * b ^ (n.val / 2 % 2)) *
        (p ^ (n.val / 4 % 2) * d ^ (n.val / 8 % 2)) := by simp only [coord, mul_assoc]
    have hlo : z ^ (n.val % 2) * b ^ (n.val / 2 % 2) ∈ V₂ :=
      V₂.mul_mem (V₂.pow_mem hzV₂ _) (V₂.pow_mem hb _)
    have hhi : p ^ (n.val / 4 % 2) * d ^ (n.val / 8 % 2) ∈ DI :=
      DI.mul_mem (DI.pow_mem hp _) (DI.pow_mem hd _)
    rw [hsplit] at hn
    have hlo1 : z ^ (n.val % 2) * b ^ (n.val / 2 % 2) = 1 := by
      have h1 : z ^ (n.val % 2) * b ^ (n.val / 2 % 2) =
          (p ^ (n.val / 4 % 2) * d ^ (n.val / 8 % 2))⁻¹ := eq_inv_of_mul_eq_one_left hn
      have h2 : z ^ (n.val % 2) * b ^ (n.val / 2 % 2) ∈ V₂ ⊓ DI := ⟨hlo, h1 ▸ DI.inv_mem hhi⟩
      rw [hVD] at h2
      exact h2
    have hhi1 : p ^ (n.val / 4 % 2) * d ^ (n.val / 8 % 2) = 1 := by
      rw [hlo1, one_mul] at hn
      exact hn
    have hbz : b ≠ z := fun h => hbV₁ (h ▸ hz)
    have hbzi : z * b ≠ 1 := fun h => hbV₁ (by
      rw [show b = z⁻¹ from eq_inv_of_mul_eq_one_right h]
      exact V₁.inv_mem hz)
    have hpd : p * d ≠ 1 := fun h => hdp (by
      rw [show d = p⁻¹ from eq_inv_of_mul_eq_one_right h, ← mul_one p⁻¹, ← hsD p hp, pow_two,
        inv_mul_cancel_left])
    have hb1 : b ≠ 1 := fun h => hbV₁ (h ▸ V₁.one_mem)
    obtain ⟨e0, e1⟩ := pair_eq_zero hz1 hb1 hbzi (Nat.mod_lt _ two_pos) (Nat.mod_lt _ two_pos) hlo1
    obtain ⟨e2, e3⟩ := pair_eq_zero hp1 hd1 hpd (Nat.mod_lt _ two_pos) (Nat.mod_lt _ two_pos) hhi1
    exact bits_eq_zero n e0 e1 e2 e3

theorem exists_coord {V₂ DI : Subgroup G} {z b p d : G}
    (hV : ∀ v ∈ V₂, v = 1 ∨ v = z ∨ v = b ∨ v = z * b)
    (hD : ∀ w ∈ DI, w = 1 ∨ w = p ∨ w = d ∨ w = p * d)
    (hN : V₂ ≤ Subgroup.normalizer (DI : Set G)) {y : G} (hy : y ∈ V₂ ⊔ DI) :
    ∃ n : Fin 16, coord z b p d n = y := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right V₂ DI hN] at hy
  obtain ⟨v, hv, w, hw, rfl⟩ := hy
  rcases hV v hv with rfl | rfl | rfl | rfl <;> rcases hD w hw with rfl | rfl | rfl | rfl
  exacts [⟨0, by simp [coord]⟩, ⟨4, by simp [coord]⟩, ⟨8, by simp [coord]⟩,
    ⟨12, by simp [coord]⟩, ⟨1, by simp [coord]⟩, ⟨5, by simp [coord]⟩, ⟨9, by simp [coord]⟩,
    ⟨13, by simp [coord, mul_assoc]⟩, ⟨2, by simp [coord]⟩, ⟨6, by simp [coord]⟩,
    ⟨10, by simp [coord]⟩, ⟨14, by simp [coord, mul_assoc]⟩, ⟨3, by simp [coord]⟩,
    ⟨7, by simp [coord]⟩, ⟨11, by simp [coord]⟩, ⟨15, by simp [coord, mul_assoc]⟩]


theorem mem_v1s_of_xorF : ∀ n : Fin 16, (xorF 2 n).val / 2 % 2 = 0 → n ∈ v1s := by decide

theorem xorF_four_mem : ∀ m ∈ ([0, 1, 2, 3] : List (Fin 16)), xorF 4 m ∈ d2s := by decide

theorem xorF_eight_mem : ∀ m ∈ ([0, 1, 2, 3] : List (Fin 16)), xorF 8 m ∈ d3s := by decide

theorem exists_coord_V₂ {V₂ : Subgroup G} {z b p d : G}
    (hV : ∀ v ∈ V₂, v = 1 ∨ v = z ∨ v = b ∨ v = z * b) {u : G} (hu : u ∈ V₂) :
    ∃ m ∈ ([0, 1, 2, 3] : List (Fin 16)), coord z b p d m = u := by
  rcases hV u hu with rfl | rfl | rfl | rfl
  exacts [⟨0, by simp, by simp [coord]⟩, ⟨1, by simp, by simp [coord]⟩,
    ⟨2, by simp, by simp [coord]⟩, ⟨3, by simp, by simp [coord]⟩]

theorem exists_coord_DI {DI : Subgroup G} {z b p d : G}
    (hD : ∀ w ∈ DI, w = 1 ∨ w = p ∨ w = d ∨ w = p * d) {u : G} (hu : u ∈ DI) :
    ∃ m ∈ ([0, 4, 8, 12] : List (Fin 16)), coord z b p d m = u := by
  rcases hD u hu with rfl | rfl | rfl | rfl
  exacts [⟨0, by simp, by simp [coord]⟩, ⟨4, by simp, by simp [coord]⟩,
    ⟨8, by simp, by simp [coord]⟩, ⟨12, by simp, by simp [coord]⟩]

theorem mem_normalizer_V₂ [Finite G] {V₂ : Subgroup G} {z b x : G}
    (hV : ∀ v ∈ V₂, v = 1 ∨ v = z ∨ v = b ∨ v = z * b) (hxz : x * z * x⁻¹ = z)
    (hxb : x * b * x⁻¹ ∈ V₂) (hzV : z ∈ V₂) : x ∈ Subgroup.normalizer (V₂ : Set G) := by
  apply mem_normalizer_of_conj_mem_of_finite
  intro v hv
  rcases hV v hv with rfl | rfl | rfl | rfl
  · simp
  · rw [hxz]; exact hzV
  · exact hxb
  · have e : x * (z * b) * x⁻¹ = (x * z * x⁻¹) * (x * b * x⁻¹) := by group
    rw [e, hxz]
    exact V₂.mul_mem hzV hxb

theorem normalizes_V₂ [Finite G] (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (hDI : Case1294FiveDI) {T L V : Subgroup G} (hcx : Cx1291 G T L V 4) {V₁ V₂ K₁ : Subgroup G}
    (hs : Setting1282One G T L V 4 V₁ V₂) (hLK : lOne L V₁ ≤ K₁)
    (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)))
    (hK4 : Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)))
    (D : HatModelU (u128 V V₁))
    (h5 : G112Concl5 D.B (D.img (Subgroup.normalizer (V₁ : Set G))))
    (himg : (D.img K₁).relIndex (D.img (Subgroup.normalizer (V₁ : Set G))) ≤ 2)
    {a : G} (haV₂ : a ∈ V₂) (haV₁ : a ∉ V₁) (h : ↥(Subgroup.normalizer (u128 V V₁ : Set G)))
    (hhK : (h : G) ∈ K₁) (h3 : ∃ k : ℕ, orderOf (h : G) = 3 ^ k)
    (hfix : D.ρ h (D.π a) = D.π a) : (h : G) ∈ Subgroup.normalizer (V₂ : Set G) := by
  classical
  obtain ⟨DI, hDIZ, hDIc, hDI4, hDIV₁, hDI2, hTDI, hP⟩ :=
    hDI G T L V hcx V₁ V₂ K₁ hs hLK hK hK4 D h5 himg
  obtain ⟨hhDI, hhB⟩ := hP a haV₂ haV₁ h hhK h3 hfix
  set x : G := (h : G) with hxdef
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hs.v1.2.1
  have hV₂4 : Nat.card V₂ = 4 := by simpa using hs.v2.2.1
  obtain ⟨-, hsq, hab⟩ := hs.hyp.card_sq
  obtain ⟨z, hz, hz1, b, hb, hbV₁⟩ := L128P.exists_gens hV₁2 hV₂4
  obtain ⟨k, hk, hkz, hkb, hkV⟩ :=
    L128P.exists_rotation_mem h1222 hs.hyp hs.v1 hs.v2 hs.le hz hz1 hb hbV₁
  have hzV₂ : z ∈ V₂ := hs.le hz
  have hV₂V : V₂ ≤ V := hs.v2.1
  have hVU : ∀ v ∈ V, v ∈ u128 V V₁ := fun v hv => le_conjClosure V _ hv
  have hV₁z : ∀ v ∈ V₁, v = 1 ∨ v = z := fun v hv => by
    by_cases hv1 : v = 1
    · exact Or.inl hv1
    · exact Or.inr (SteinbergBS.eq_of_card_le_two hV₁2.le hv hz hv1 hz1)
  have hV₂e : ∀ v ∈ V₂, v = 1 ∨ v = z ∨ v = b ∨ v = z * b := fun v hv =>
    L128P.eq_of_mem_four hs.le hV₁2 hV₂4 hz hz1 hbV₁ hb hv
  have hVZ := lemma12_8_8_three h1222 h12213 hs
  have hZc : ∀ y ∈ zU128 V V₁, ∀ u ∈ u128 V V₁, u * y = y * u := fun y hy u hu =>
    Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hy).2 u hu
  have hZU : ∀ y ∈ zU128 V V₁, y ∈ u128 V V₁ := fun y hy => (Subgroup.mem_inf.1 hy).1
  have hT2 : IsPGroup 2 T := hcx.hyp.hyp.sylow.1
  obtain ⟨p, hp, hp1, hTp⟩ := exists_fixed_ne_one hT2 hTDI hDI4
  have hp2 : p ^ 2 = 1 := hDI2 p hp
  have hP2 : Nat.card (Subgroup.zpowers p) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hp2 hp1
  have hPle : Subgroup.zpowers p ≤ DI := (Subgroup.zpowers_le).2 hp
  obtain ⟨d, hd, hdP⟩ : ∃ d ∈ DI, d ∉ Subgroup.zpowers p := by
    by_contra hne
    push Not at hne
    have := Subgroup.card_le_of_le (show DI ≤ Subgroup.zpowers p from hne)
    rw [hDI4, hP2] at this
    norm_num at this
  have hd1 : d ≠ 1 := fun e => hdP (e ▸ (Subgroup.zpowers p).one_mem)
  have hdp : d ≠ p := fun e => hdP (e ▸ Subgroup.mem_zpowers p)
  have hDe : ∀ w ∈ DI, w = 1 ∨ w = p ∨ w = d ∨ w = p * d := fun w hw =>
    L128P.eq_of_mem_four hPle hP2 hDI4 (Subgroup.mem_zpowers p) hp1 hdP hd hw
  have hcV : ∀ u ∈ V₂, ∀ w ∈ V₂, u * w = w * u := fun u hu w hw => hab u (hV₂V hu) w (hV₂V hw)
  have hcD : ∀ u ∈ DI, ∀ w ∈ DI, u * w = w * u := fun u hu w hw =>
    (hZc w (hDIZ hw) u (hZU u (hDIZ hu)))
  have hcVD : ∀ u ∈ V₂, ∀ w ∈ DI, u * w = w * u := fun u hu w hw =>
    hZc w (hDIZ hw) u (hVU u (hV₂V hu))
  have hsV : ∀ u ∈ V₂, u ^ 2 = 1 := fun u hu => hsq u (hV₂V hu)
  have hVD : V₂ ⊓ DI = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have h1 : y ∈ V ⊓ zU128 V V₁ := ⟨hV₂V hy.1, hDIZ hy.2⟩
    rw [hVZ] at h1
    have h2 : y ∈ DI ⊓ V₁ := ⟨hy.2, h1⟩
    rw [hDIV₁] at h2
    exact h2
  have hF : Frame z b p d := frame_of hz hz1 hb hbV₁ hzV₂ hV₁z hp hp1 hd hd1 hdp hcV hcD hcVD hsV
    hDI2 hVD
  have hN : V₂ ≤ Subgroup.normalizer (DI : Set G) := fun u hu =>
    mem_normalizer_of_conj_mem_of_finite fun w hw => by
      rw [hcVD u hu w hw, mul_inv_cancel_right]
      exact hw
  have hcoord : ∀ y ∈ V₂ ⊔ DI, ∃ n : Fin 16, coord z b p d n = y := fun y hy =>
    exists_coord hV₂e hDe hN hy
  have hcancel : ∀ (t u v : G), t * u * t⁻¹ = t * v * t⁻¹ → u = v := fun t u v e =>
    mul_left_cancel (mul_right_cancel e)
  have hTc : ∀ t ∈ T, HasCode z b p d t idC ∨ HasCode z b p d t tau1 ∨
      HasCode z b p d t tau2 ∨ HasCode z b p d t tau12 := by
    intro t ht
    have htz : t * z * t⁻¹ = z := L1297.conj_eq_of_mem_normalizer hV₁2 hz (hs.v1.2.2 ht)
    have htb : t * b * t⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.1 (hs.v2.2.2 ht) b).1 hb
    have htbV₁ : t * b * t⁻¹ ∉ V₁ := fun hm =>
      hbV₁ ((Subgroup.mem_normalizer_iff.1 (hs.v1.2.2 ht) b).2 hm)
    have htd : t * d * t⁻¹ ∈ DI := (Subgroup.mem_normalizer_iff.1 (hTDI ht) d).1 hd
    have htp := hTp t ht
    have hb' : t * b * t⁻¹ = b ∨ t * b * t⁻¹ = z * b := by
      rcases hV₂e _ htb with e | e | e | e
      · exact absurd (e ▸ V₁.one_mem) htbV₁
      · exact absurd (e ▸ hz) htbV₁
      · exact Or.inl e
      · exact Or.inr e
    have hd' : t * d * t⁻¹ = d ∨ t * d * t⁻¹ = p * d := by
      rcases hDe _ htd with e | e | e | e
      · exact absurd (hcancel t d 1 (by rw [e]; group)) hd1
      · exact absurd (hcancel t d p (by rw [e, htp])) hdp
      · exact Or.inl e
      · exact Or.inr e
    rcases hb' with e1 | e1 <;> rcases hd' with e2 | e2
    · exact Or.inl ⟨by simp [idC, coord, htz], by simp [idC, coord, e1],
        by simp [idC, coord, htp], by simp [idC, coord, e2]⟩
    · exact Or.inr (Or.inr (Or.inl ⟨by simp [tau2, coord, htz], by simp [tau2, coord, e1],
        by simp [tau2, coord, htp], by simp [tau2, coord, e2]⟩))
    · exact Or.inr (Or.inl ⟨by simp [tau1, coord, htz], by simp [tau1, coord, e1],
        by simp [tau1, coord, htp], by simp [tau1, coord, e2]⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨by simp [tau12, coord, htz], by simp [tau12, coord, e1],
        by simp [tau12, coord, htp], by simp [tau12, coord, e2]⟩))
  have hkI : k ∈ i128 T L V V₁ := by
    rw [L128P.i128_eq_sup h1222 h12213 hs]
    exact Subgroup.mem_sup_left hk
  have hcen : ∀ c ∈ centerOf (i128 T L V V₁), ∀ y ∈ i128 T L V V₁, y * c * y⁻¹ = c :=
    fun c hc y hy => by
      rw [Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 y hy, mul_inv_cancel_right]
  have hV₁N : V₁ ≤ Subgroup.normalizer (centerOf (i128 T L V V₁) : Set G) := fun v hv =>
    mem_normalizer_of_conj_mem_of_finite fun c hc => by
      rw [hcen c hc v (le_conjClosure (u128 V V₁) _ (hVU v (hs.v1.1 hv)))]
      exact hc
  have hkDI : ∀ w ∈ DI, ∃ u ∈ V₂, k * w * k⁻¹ = w * u := by
    intro w hw
    have hw' := hDIc hw
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hV₁N] at hw'
    obtain ⟨c, hc, v, hv, rfl⟩ := hw'
    refine ⟨v⁻¹ * (k * v * k⁻¹), ?_, ?_⟩
    · have h1 := hkV v (hs.v1.1 hv)
      have e : v⁻¹ * (k * v * k⁻¹) = v⁻¹ * (k * v * k⁻¹ * v⁻¹) * v := by group
      rw [e]
      exact V₂.mul_mem (V₂.mul_mem (V₂.inv_mem (hs.le hv)) h1) (hs.le hv)
    · rw [show k * (c * v) * k⁻¹ = (k * c * k⁻¹) * (k * v * k⁻¹) by group, hcen c hc k hkI]
      group
  obtain ⟨u₁, hu₁, hkp⟩ := hkDI p hp
  obtain ⟨u₂, hu₂, hkd⟩ := hkDI d hd
  obtain ⟨m₁, hm₁, hcm₁⟩ := exists_coord_V₂ (p := p) (d := d) hV₂e hu₁
  obtain ⟨m₂, hm₂, hcm₂⟩ := exists_coord_V₂ (p := p) (d := d) hV₂e hu₂
  have hk : HasCode z b p d k (y2Code (xorF 4 m₁) (xorF 8 m₂)) := by
    refine ⟨by simp [y2Code, coord, hkz], by simp [y2Code, coord, hkb], ?_, ?_⟩
    · show k * p * k⁻¹ = coord z b p d (xorF 4 m₁)
      rw [← hF.coord_mul, coord_four_eq, hcm₁, hkp]
    · show k * d * k⁻¹ = coord z b p d (xorF 8 m₂)
      rw [← hF.coord_mul, coord_eight_eq, hcm₂, hkd]
  have hK₁N : K₁ ≤ Subgroup.normalizer (V₁ : Set G) := le_of_mem_cComp (show K₁ ∈ cComp _ from hK)
  have hxz : x * z * x⁻¹ = z := L1297.conj_eq_of_mem_normalizer hV₁2 hz (hK₁N hhK)
  have hxp : x * p * x⁻¹ ∈ DI := (Subgroup.mem_normalizer_iff.1 hhDI p).1 hp
  have hxd : x * d * x⁻¹ ∈ DI := (Subgroup.mem_normalizer_iff.1 hhDI d).1 hd
  have hxb : x * b * x⁻¹ ∈ V₂ ⊔ DI :=
    (Subgroup.mem_normalizer_iff.1 hhB b).1 (Subgroup.mem_sup_left hb)
  obtain ⟨n₁, hn₁⟩ := hcoord _ hxb
  obtain ⟨n₂, hn₂m, hn₂⟩ := exists_coord_DI (z := z) (b := b) hDe hxp
  obtain ⟨n₃, hn₃m, hn₃⟩ := exists_coord_DI (z := z) (b := b) hDe hxd
  have hxc : HasCode z b p d x (y1Code n₁ n₂ n₃) :=
    ⟨by simp [y1Code, coord, hxz], hn₁.symm, hn₂.symm, hn₃.symm⟩
  have hn₂0 : n₂ ≠ 0 := fun e => hp1 (hcancel x p 1 (by rw [← hn₂, e]; simp [coord]))
  have hn₃0 : n₃ ≠ 0 := fun e => hd1 (hcancel x d 1 (by rw [← hn₃, e]; simp [coord]))
  have hn₂d : n₂ ∈ dMasks := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn₂m
    rcases hn₂m with e | e | e | e
    · exact absurd e hn₂0
    all_goals simp [dMasks, e]
  have hn₃d : n₃ ∈ dMasks := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn₃m
    rcases hn₃m with e | e | e | e
    · exact absurd e hn₃0
    all_goals simp [dMasks, e]
  have hne : n₂ ≠ n₃ := fun e => hdp (hcancel x d p (by rw [← hn₃, ← hn₂, e]))
  have hbU : b ∈ u128 V V₁ := hVU b (hV₂V hb)
  have hzZ : z ∈ zU128 V V₁ := by
    have : z ∈ V ⊓ zU128 V V₁ := by rw [hVZ]; exact hz
    exact this.2
  have hπb : D.π b = D.π a := by
    rcases hV₂e a haV₂ with e | e | e | e
    · exact absurd (e ▸ V₁.one_mem) haV₁
    · exact absurd (e ▸ hz) haV₁
    · rw [e]
    · rw [e, D.π_mul z (hVU z (hV₂V hzV₂)) b hbU,
        (L128A.HatU.π_eq_zero_iff D (hVU z (hV₂V hzV₂))).2 hzZ, zero_add]
  have hxbU : x * b * x⁻¹ ∈ u128 V V₁ := (Subgroup.mem_normalizer_iff.1 h.2 b).1 hbU
  have hyZ : b⁻¹ * (x * b * x⁻¹) ∈ zU128 V V₁ := by
    have h1 : D.π (x * b * x⁻¹) = D.π b := by
      rw [← D.ρ_π h b hbU, hπb, hfix]
    exact (D.π_eq_iff b hbU _ hxbU).1 h1.symm
  have hlo : ∀ m : Fin 16, coord z b p d m ∈ zU128 V V₁ → m.val / 2 % 2 = 0 := by
    intro m hm
    have hsplit : coord z b p d m = (z ^ (m.val % 2) * b ^ (m.val / 2 % 2)) *
        (p ^ (m.val / 4 % 2) * d ^ (m.val / 8 % 2)) := by simp only [coord, mul_assoc]
    have hhi : p ^ (m.val / 4 % 2) * d ^ (m.val / 8 % 2) ∈ zU128 V V₁ :=
      hDIZ (DI.mul_mem (DI.pow_mem hp _) (DI.pow_mem hd _))
    have h1 : z ^ (m.val % 2) * b ^ (m.val / 2 % 2) ∈ zU128 V V₁ := by
      have := (zU128 V V₁).mul_mem hm ((zU128 V V₁).inv_mem hhi)
      rwa [hsplit, mul_inv_cancel_right] at this
    have h2 : z ^ (m.val % 2) * b ^ (m.val / 2 % 2) ∈ V₁ := by
      have h3 : z ^ (m.val % 2) * b ^ (m.val / 2 % 2) ∈ V ⊓ zU128 V V₁ :=
        ⟨V.mul_mem (V.pow_mem (hV₂V hzV₂) _) (V.pow_mem (hV₂V hb) _), h1⟩
      rwa [hVZ] at h3
    rcases Nat.mod_two_eq_zero_or_one (m.val / 2) with e | e
    · exact e
    · exfalso
      rw [e, pow_one] at h2
      apply hbV₁
      have := V₁.mul_mem (V₁.inv_mem (V₁.pow_mem hz (m.val % 2))) h2
      rwa [inv_mul_cancel_left] at this
  have hn₁v : n₁ ∈ v1s := by
    apply mem_v1s_of_xorF
    apply hlo
    rw [← hF.coord_mul, coord_two_eq, hn₁]
    have hbinv : b⁻¹ = b := by
      rw [inv_eq_iff_mul_eq_one, ← pow_two]
      exact hsV b hb
    rw [hbinv] at hyZ
    exact hyZ
  rcases shape_or_witness n₁ hn₁v n₂ hn₂d n₃ hn₃d hne with e | e | ⟨h₁, h₂⟩ | ⟨w, hw1, hw2⟩
  · exact mem_normalizer_V₂ hV₂e hxz (by rw [← hn₁, e, coord_two_eq]; exact hb) hzV₂
  · refine mem_normalizer_V₂ hV₂e hxz ?_ hzV₂
    rw [← hn₁, e]
    simpa [coord] using V₂.mul_mem hzV₂ hb
  · exact (false_of_good (q := (n₂, n₃)) hF hcx.hyp.hyp.sylow.2 hTc h₁ h₂
      (xorF_four_mem m₁ hm₁) (xorF_eight_mem m₂ hm₂) hxc hk).elim
  · exfalso
    obtain ⟨j, hj⟩ := h3
    have hxm : x ^ (3 ^ j) = 1 := by rw [← hj]; exact pow_orderOf_eq_one x
    have hodd : Odd (3 ^ j) := Odd.pow (by decide)
    have hxx := hxc.mul hF hxc
    have h1 : x * x * coord z b p d w * (x * x)⁻¹ = coord z b p d w := by
      rw [hxx.conj hF, hw1]
    have h2 := conj_eq_of_sq_conj hodd hxm h1
    rw [hxc.conj hF] at h2
    exact hw2 (hF.coord_injective h2)

end L1294R

end CFSG.Quasithin.H13
