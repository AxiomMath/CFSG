module
public import CFSG.LocalAnalysis.WeakClosure81.OddCentral.NoTranslations
public section
namespace CFSG.LocalAnalysis.WeakClosure81.OddCentral
open Subgroup

section
variable {G M : Type*} [Group G] [Finite G] [AddCommGroup M] [Finite M] [DistribMulAction G M]

theorem frame_induction {H : Subgroup G} (hHodd : Odd (Nat.card H)) {z₀ z₁ : G}
    (hH0 : ∀ h ∈ H, z₀ * h * z₀⁻¹ ∈ H) (hH1 : ∀ h ∈ H, z₁ * h * z₁⁻¹ ∈ H)
    (h0 : z₀ * z₀ = 1) (h1 : z₁ * z₁ = 1) (h01 : z₀ * z₁ = z₁ * z₀) (hn0 : z₀ ≠ 1)
    (hn1 : z₁ ≠ 1) (hn01 : z₀ ≠ z₁) {P : G → Prop} (hP1 : P 1)
    (hPmul : ∀ a b, P a → P b → P (a * b)) (hPinv : ∀ a, P a → P a⁻¹)
    (hPfix : ∀ h ∈ H, (z₀ * h * z₀⁻¹ = h ∨ z₁ * h * z₁⁻¹ = h ∨
      (z₀ * z₁) * h * (z₀ * z₁)⁻¹ = h) → P h) : ∀ h ∈ H, P h := by
  have hinv : ∀ {z : G}, z * z = 1 → z⁻¹ = z := fun h => inv_eq_of_mul_eq_one_right h
  have h2 : (z₀ * z₁) * (z₀ * z₁) = 1 := by
    rw [show z₀ * z₁ * (z₀ * z₁) = z₀ * (z₁ * z₀) * z₁ by group, ← h01,
      show z₀ * (z₀ * z₁) * z₁ = (z₀ * z₀) * (z₁ * z₁) by group, h0, h1, one_mul]
  have e1 : z₀ * (z₀ * z₁) = z₁ := by rw [← mul_assoc, h0, one_mul]
  have e2 : z₁ * (z₀ * z₁) = z₀ := by rw [← mul_assoc, ← h01, mul_assoc, h1, mul_one]
  have e3 : (z₀ * z₁) * z₀ = z₁ := by rw [mul_assoc, ← h01, ← mul_assoc, h0, one_mul]
  have e4 : (z₀ * z₁) * z₁ = z₀ := by rw [mul_assoc, h1, mul_one]
  have e5 : z₁ * z₀ = z₀ * z₁ := h01.symm
  let T₁ : Subgroup G :=
    { carrier := {1, z₀, z₁, z₀ * z₁}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
        rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
          simp [h0, h1, h2, e1, e2, e3, e4, e5]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
        rcases ha with rfl | rfl | rfl | rfl
        · simp
        · rw [hinv h0]; simp
        · rw [hinv h1]; simp
        · rw [hinv h2]; simp }
  have hT₁mem : ∀ u ∈ T₁, u = 1 ∨ u = z₀ ∨ u = z₁ ∨ u = z₀ * z₁ := fun u hu => hu
  have hT₁sq : ∀ u ∈ T₁, u * u = 1 := by
    intro u hu
    rcases hT₁mem u hu with rfl | rfl | rfl | rfl
    · simp
    · exact h0
    · exact h1
    · exact h2
  have hT₁comm : ∀ u ∈ T₁, ∀ v ∈ T₁, u * v = v * u := by
    intro u hu v hv
    have h1' := hT₁sq u hu
    have h2' := hT₁sq v hv
    have h3' := hT₁sq (u * v) (T₁.mul_mem hu hv)
    rw [← hinv h3', mul_inv_rev, hinv h1', hinv h2']
  have hz₀T : z₀ ∈ T₁ := by simp [T₁]
  have hz₁T : z₁ ∈ T₁ := by simp [T₁]
  letI iC : CommGroup T₁ :=
    { (inferInstance : Group T₁) with mul_comm := fun a b => Subtype.ext (hT₁comm a a.2 b b.2) }
  haveI : CFSG.IsElementaryAbelian 2 T₁ :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hT₁comm a a.2 b b.2)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
        Subtype.ext (by rw [sq]; simpa using hT₁sq g g.2) }
  haveI : Nontrivial T₁ := ⟨⟨⟨z₀, hz₀T⟩, 1, fun h => hn0 (congrArg Subtype.val h)⟩⟩
  have hT₁H : ∀ u ∈ T₁, ∀ h ∈ H, u * h * u⁻¹ ∈ H := by
    intro u hu h hh
    rcases hT₁mem u hu with rfl | rfl | rfl | rfl
    · simpa using hh
    · exact hH0 h hh
    · exact hH1 h hh
    · rw [show z₀ * z₁ * h * (z₀ * z₁)⁻¹ = z₀ * (z₁ * h * z₁⁻¹) * z₀⁻¹ by group]
      exact hH0 _ (hH1 h hh)
  have hT₁inv : ∀ u ∈ T₁, u⁻¹ = u := fun u hu => hinv (hT₁sq u hu)
  let α : T₁ →* MulAut H :=
    { toFun := fun u =>
        { toFun := fun h => ⟨(u : G) * h * (u : G)⁻¹, hT₁H u u.2 h h.2⟩
          invFun := fun h => ⟨(u : G)⁻¹ * h * u, by
            have := hT₁H u u.2 h h.2
            rw [hT₁inv u u.2] at this ⊢
            exact this⟩
          left_inv := fun h => Subtype.ext (by simp [mul_assoc])
          right_inv := fun h => Subtype.ext (by simp [mul_assoc])
          map_mul' := fun h h' => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
      map_one' := MulEquiv.ext fun h => Subtype.ext (by simp)
      map_mul' := fun a b => MulEquiv.ext fun h => Subtype.ext (by
        show (a : G) * b * h * ((a : G) * b)⁻¹ = (a : G) * ((b : G) * h * (b : G)⁻¹) * (a : G)⁻¹
        group) }
  have hα : ∀ (b : T₁) (x : H), ((α b x : H) : G) = (b : G) * x * (b : G)⁻¹ := fun _ _ => rfl
  have hgen := CFSG.SolvableSignalizer.iSup_fixedBySubgroup_index_eq_top 2 Nat.prime_two α
    (by rw [← even_iff_two_dvd, Nat.not_even_iff_odd]; exact hHodd)
  let X : Set H := {x | z₀ * (x : G) * z₀⁻¹ = x ∨ z₁ * (x : G) * z₁⁻¹ = x ∨
    (z₀ * z₁) * (x : G) * (z₀ * z₁)⁻¹ = x}
  have hcard : Nat.card T₁ ≠ 2 := by
    intro h2'
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : T₁)).mp h2'
    have f1 := hy ⟨z₀, hz₀T⟩ (fun h => hn0 (congrArg Subtype.val h))
    have f2 := hy ⟨z₁, hz₁T⟩ (fun h => hn1 (congrArg Subtype.val h))
    exact hn01 (congrArg Subtype.val (f1.trans f2.symm))
  have hle : (⊤ : Subgroup H) ≤ closure X := by
    rw [← hgen]
    refine iSup₂_le fun B hB x hx => ?_
    rw [CFSG.SolvableSignalizer.mem_fixedBySubgroup] at hx
    obtain ⟨b, hbB, hb1⟩ : ∃ b ∈ B, b ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hBbot : B = ⊥ := (Subgroup.eq_bot_iff_forall B).mpr hcon
      rw [hBbot, Subgroup.index_bot] at hB
      exact hcard hB
    have hfix : (b : G) * x * (b : G)⁻¹ = x := by rw [← hα]; exact congrArg Subtype.val (hx b hbB)
    apply Subgroup.subset_closure
    rcases hT₁mem b b.2 with h | h | h | h
    · exact absurd (Subtype.ext h) hb1
    · exact Or.inl (h ▸ hfix)
    · exact Or.inr (Or.inl (h ▸ hfix))
    · exact Or.inr (Or.inr (h ▸ hfix))
  intro h hh
  have hh' : (⟨h, hh⟩ : H) ∈ closure X := hle (mem_top _)
  refine Subgroup.closure_induction (p := fun (x : H) _ => P (x : G)) (fun x hx => hPfix x x.2 hx) hP1
    (fun x y _ _ hx hy => hPmul _ _ hx hy) (fun x _ hx => hPinv _ hx) hh'

theorem fix_of_inverted {Q₀ : Subgroup G} (hQ₀odd : Odd (Nat.card Q₀)) (hQ₀Z : Q₀ ≤ center G)
    {y v z : G} (hzy : z * y * z⁻¹ = y) (hzv : z * v * z⁻¹ = v⁻¹)
    (hδ : y * v * y⁻¹ * v⁻¹ ∈ Q₀) : y * v * y⁻¹ = v := by
  set δ := y * v * y⁻¹ * v⁻¹ with hδd
  have hc : ∀ g : G, g * δ = δ * g := fun g => Subgroup.mem_center_iff.mp (hQ₀Z hδ) g
  have hyv : y * v * y⁻¹ = δ * v := by rw [hδd]; group
  have e1 : y * v⁻¹ * y⁻¹ * v = δ⁻¹ := by
    rw [show y * v⁻¹ * y⁻¹ = (y * v * y⁻¹)⁻¹ by group, hyv, mul_inv_rev, mul_assoc,
      (Commute.inv_left (show Commute δ v from (hc v).symm)).eq, inv_mul_cancel_left]
  have e2 : z * δ * z⁻¹ = y * v⁻¹ * y⁻¹ * v := by
    rw [show z * δ * z⁻¹ = (z * y * z⁻¹) * (z * v * z⁻¹) * (z * y * z⁻¹)⁻¹ * (z * v * z⁻¹)⁻¹ by
      rw [hδd]; group, hzy, hzv, inv_inv]
  have e3 : z * δ * z⁻¹ = δ := by rw [hc z, mul_inv_cancel_right]
  have hδ1 : δ * δ = 1 := by
    have : δ = δ⁻¹ := by rw [← e1, ← e2, e3]
    calc δ * δ = δ * δ⁻¹ := by rw [← this]
      _ = 1 := mul_inv_cancel δ
  have := eq_one_of_mul_self hQ₀odd hδ hδ1
  rw [hyv, this, one_mul]

theorem conj_pow_mul_inv {y v : G} (hc : y * v * y⁻¹ * v⁻¹ ∈ center G) (n : ℕ) :
    y * v ^ n * y⁻¹ * (v ^ n)⁻¹ = (y * v * y⁻¹ * v⁻¹) ^ n := by
  set δ := y * v * y⁻¹ * v⁻¹ with hδd
  have hcomm : Commute δ v := (Subgroup.mem_center_iff.mp hc v).symm
  have hyv : y * v * y⁻¹ = δ * v := by rw [hδd]; group
  rw [← conj_pow, hyv, hcomm.mul_pow, mul_inv_cancel_right]

theorem exists_translations {R₁ Q Q₀ V : Subgroup G} [hRn : R₁.Normal]
    (hR₁odd : Odd (Nat.card R₁)) (hQodd : Odd (Nat.card Q)) (hQ₀Q : Q₀ ≤ Q)
    (hQ₀Z : Q₀ ≤ center G) (hRQ : ∀ y ∈ R₁, ∀ x ∈ Q, y * x * y⁻¹ * x⁻¹ ∈ Q₀)
    (hQV : ∀ x ∈ Q, ∃ q ∈ Q₀, ∃ v ∈ V, x = q * v) (hVQ : V ≤ Q)
    {Vi : Fin 3 → Subgroup G} (hViV : ∀ a, Vi a ≤ V)
    (hVgen : ∀ v ∈ V, ∃ v₀ ∈ Vi 0, ∃ v₁ ∈ Vi 1, ∃ v₂ ∈ Vi 2, v = v₀ * v₁ * v₂)
    {z : Fin 3 → G} {t : G} (hz : ∀ a, z a * z a = 1) (hz2 : z 2 = z 0 * z 1)
    (h01 : z 0 * z 1 = z 1 * z 0) (hn0 : z 0 ≠ 1) (hn1 : z 1 ≠ 1) (hn01 : z 0 ≠ z 1)
    (hzinv : ∀ a b, a ≠ b → ∀ v ∈ Vi b, z a * v * (z a)⁻¹ = v⁻¹)
    (ht : ∀ a, t * z a * t⁻¹ = z (a + 1)) (htV : ∀ a v, v ∈ Vi a ↔ t * v * t⁻¹ ∈ Vi (a + 1))
    (hmov : ∃ y ∈ R₁, ∃ x ∈ Q, y * x * y⁻¹ ≠ x) :
    ∃ y : Fin 3 → G, ∀ a, y a ∈ R₁ ∧ z a * y a * (z a)⁻¹ = y a ∧
      ∃ v ∈ Vi a, y a * v * (y a)⁻¹ ≠ v := by
  have hQ₀odd : Odd (Nat.card Q₀) := Odd.of_dvd_nat hQodd (Subgroup.card_dvd_of_le hQ₀Q)
  have hfixb : ∀ a b, a ≠ b → ∀ y ∈ R₁, z a * y * (z a)⁻¹ = y → ∀ v ∈ Vi b, y * v * y⁻¹ = v :=
    fun a b hab y hy hzy v hv => fix_of_inverted hQ₀odd hQ₀Z hzy (hzinv a b hab v hv)
      (hRQ y hy v (hVQ (hViV b hv)))
  let S : Fin 3 → Prop := fun a =>
    ∀ y ∈ R₁, z a * y * (z a)⁻¹ = y → ∀ v ∈ Vi a, y * v * y⁻¹ = v
  have hstep : ∀ a, S a → S (a + 1) := by
    intro a hSa y hy hzy v hv
    have hy' : t⁻¹ * y * t ∈ R₁ := by simpa using hRn.conj_mem y hy t⁻¹
    have hza : z a = t⁻¹ * z (a + 1) * t := by rw [← ht a]; group
    have hzy' : z a * (t⁻¹ * y * t) * (z a)⁻¹ = t⁻¹ * y * t := by
      rw [hza, show t⁻¹ * z (a + 1) * t * (t⁻¹ * y * t) * (t⁻¹ * z (a + 1) * t)⁻¹ =
        t⁻¹ * (z (a + 1) * y * (z (a + 1))⁻¹) * t by group, hzy]
    have hv' : t⁻¹ * v * t ∈ Vi a := (htV a _).mpr (by simpa [mul_assoc] using hv)
    have := hSa _ hy' hzy' _ hv'
    have e : t⁻¹ * (y * v * y⁻¹) * t = t⁻¹ * v * t := by rw [← this]; group
    simpa using e
  have hS : ∀ a, ∃ y ∈ R₁, z a * y * (z a)⁻¹ = y ∧ ∃ v ∈ Vi a, y * v * y⁻¹ ≠ v := by
    by_contra hcon
    push Not at hcon
    obtain ⟨a₀, ha₀⟩ := hcon
    have hall : ∀ a, S a := by
      have h1 := hstep a₀ ha₀
      have h2 := hstep _ h1
      intro a
      have key : ∀ a a₀ : Fin 3, a = a₀ ∨ a = a₀ + 1 ∨ a = a₀ + 1 + 1 := by decide
      rcases key a a₀ with rfl | rfl | rfl
      · exact ha₀
      · exact h1
      · exact h2
    obtain ⟨y, hy, x, hx, hyx⟩ := hmov
    refine hyx (frame_induction hR₁odd (fun h hh => hRn.conj_mem h hh _)
      (fun h hh => hRn.conj_mem h hh _) (hz 0) (hz 1) h01 hn0 hn1 hn01
      (P := fun y => ∀ x ∈ Q, y * x * y⁻¹ = x) (fun x _ => by group) ?_ ?_ ?_ y hy x hx)
    · intro a b ha hb x hx
      rw [show a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ by group, hb x hx, ha x hx]
    · intro a ha x hx
      have := ha x hx
      calc a⁻¹ * x * a⁻¹⁻¹ = a⁻¹ * (a * x * a⁻¹) * a := by rw [this]; group
        _ = x := by group
    · intro y hy hfix x hx
      obtain ⟨a, hza⟩ : ∃ a, z a * y * (z a)⁻¹ = y := by
        rcases hfix with h | h | h
        · exact ⟨0, h⟩
        · exact ⟨1, h⟩
        · exact ⟨2, by rw [hz2]; exact h⟩
      have hVi : ∀ b, ∀ v ∈ Vi b, y * v * y⁻¹ = v := by
        intro b v hv
        by_cases hab : a = b
        · subst hab; exact hall a y hy hza v hv
        · exact hfixb a b hab y hy hza v hv
      have hconj : ∀ u w : G, y * u * y⁻¹ = u → y * w * y⁻¹ = w → y * (u * w) * y⁻¹ = u * w :=
        fun u w hu hw => by
          rw [show y * (u * w) * y⁻¹ = (y * u * y⁻¹) * (y * w * y⁻¹) by group, hu, hw]
      obtain ⟨q, hq, v, hv, rfl⟩ := hQV x hx
      obtain ⟨v₀, h₀, v₁, h₁, v₂, h₂, rfl⟩ := hVgen v hv
      have hqf : y * q * y⁻¹ = q := by
        rw [Subgroup.mem_center_iff.mp (hQ₀Z hq) y, mul_inv_cancel_right]
      exact hconj _ _ hqf (hconj _ _ (hconj _ _ (hVi 0 v₀ h₀) (hVi 1 v₁ h₁)) (hVi 2 v₂ h₂))
  choose y hyR hyz hyv using hS
  exact ⟨y, fun a => ⟨hyR a, hyz a, hyv a⟩⟩

theorem centralizes_of_frame {r : ℕ} (hr : r.Prime) (hrM : ¬ r ∣ Nat.card M)
    (hModd : Odd (Nat.card M)) (hMnt : ∃ m : M, m ≠ 0)
    {R₁ Q Q₀ V Z : Subgroup G} [hRn : R₁.Normal] (hR₁odd : Odd (Nat.card R₁))
    (hQodd : Odd (Nat.card Q)) (hQab : ∀ x ∈ Q, ∀ x' ∈ Q, x * x' = x' * x) (hQ₀Q : Q₀ ≤ Q)
    (hQ₀Z : Q₀ ≤ center G) (hRQ : ∀ y ∈ R₁, ∀ x ∈ Q, y * x * y⁻¹ * x⁻¹ ∈ Q₀)
    (hQV : ∀ x ∈ Q, ∃ q ∈ Q₀, ∃ v ∈ V, x = q * v) (hVQ : V ≤ Q) (hVr : ∀ v ∈ V, v ^ r = 1)
    (hZQ₀ : Z ≤ Q₀) (hZr : Nat.card Z = r) (hZΩ : ∀ q ∈ Q₀, q ^ r = 1 → q ∈ Z)
    (hZM : ∀ ζ ∈ Z, ζ ≠ 1 → ∀ m : M, ζ • m = m → m = 0)
    {Vi : Fin 3 → Subgroup G} (hViV : ∀ a, Vi a ≤ V)
    (hVgen : ∀ v ∈ V, ∃ v₀ ∈ Vi 0, ∃ v₁ ∈ Vi 1, ∃ v₂ ∈ Vi 2, v = v₀ * v₁ * v₂)
    {z : Fin 3 → G} {t c : G} (hc : c * c = 1) (hz : ∀ a, z a * z a = 1)
    (hz2 : z 2 = z 0 * z 1) (hcz : ∀ a, c * z a = z a * c) (h01 : z 0 * z 1 = z 1 * z 0)
    (hn0 : z 0 ≠ 1) (hn1 : z 1 ≠ 1) (hn01 : z 0 ≠ z 1)
    (hcV : ∀ v ∈ V, c * v * c⁻¹ = v⁻¹) (hzV : ∀ a, ∀ v ∈ V, z a * v * (z a)⁻¹ ∈ V)
    (hzinv : ∀ a b, a ≠ b → ∀ v ∈ Vi b, z a * v * (z a)⁻¹ = v⁻¹)
    (hLA : ∀ m : M, ∀ a, c • m = m → z a • m = -m → m = 0)
    (ht : ∀ a, t * z a * t⁻¹ = z (a + 1)) (htV : ∀ a v, v ∈ Vi a ↔ t * v * t⁻¹ ∈ Vi (a + 1)) :
    ∀ y ∈ R₁, ∀ x ∈ Q, y * x * y⁻¹ = x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨y, hy⟩ := exists_translations hR₁odd hQodd hQ₀Q hQ₀Z hRQ hQV hVQ hViV hVgen hz hz2 h01
    hn0 hn1 hn01 hzinv ht htV hcon
  have hQ₀odd : Odd (Nat.card Q₀) := Odd.of_dvd_nat hQodd (Subgroup.card_dvd_of_le hQ₀Q)
  have hδZ : ∀ y ∈ R₁, ∀ v ∈ V, y * v * y⁻¹ * v⁻¹ ∈ Z := fun y hy v hv => by
    have h := hRQ y hy v (hVQ hv)
    refine hZΩ _ h ?_
    rw [← conj_pow_mul_inv (hQ₀Z h) r, hVr v hv]
    group
  exact false_of_moving_translations hr hrM hModd hMnt (V := V) (Z := Z) (Vi := Vi) (z := z)
    (y := y) (c := c) (fun v hv w hw => hQab v (hVQ hv) w (hVQ hw)) hVr
    (Odd.of_dvd_nat hQodd (Subgroup.card_dvd_of_le hVQ)) (hZQ₀.trans hQ₀Z) hZr hZM hViV hc hz
    hz2 hcz h01 hcV hzV hzinv hLA (fun a v hv => hδZ (y a) (hy a).1 v hv)
    (fun a v hv => by simpa using hδZ (y a)⁻¹ (inv_mem (hy a).1) v hv)
    (fun a b hab v hv => fix_of_inverted hQ₀odd hQ₀Z (hy a).2.1 (hzinv a b hab v hv)
      (hRQ _ (hy a).1 v (hVQ (hViV b hv))))
    (fun a ζ hζ => by rw [Subgroup.mem_center_iff.mp (hQ₀Z (hZQ₀ hζ)) (y a), mul_inv_cancel_right])
    (fun a => by
      obtain ⟨v, hv, hne⟩ := (hy a).2.2
      exact ⟨v, hv, hδZ _ (hy a).1 v (hViV a hv), fun h => hne (mul_inv_eq_one.mp h)⟩)

end

end CFSG.LocalAnalysis.WeakClosure81.OddCentral

