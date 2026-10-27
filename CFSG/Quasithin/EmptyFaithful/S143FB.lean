module

public import CFSG.Quasithin.Background.G2Omega4PlusQuot
public import CFSG.Quasithin.EmptyFaithful.S143EE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

section Klein

variable {K : Type*} [Group K]

def klein (hc : ∀ a b : K, a * b = b * a) (x₀ x₁ x₂ : K) (h012 : x₀ * x₁ * x₂ = 1)
    (h0 : x₀ * x₀ = 1) (h1 : x₁ * x₁ = 1) (h2 : x₂ * x₂ = 1) : Subgroup K where
  carrier := {y | y = 1 ∨ y = x₀ ∨ y = x₁ ∨ y = x₂}
  one_mem' := Or.inl rfl
  mul_mem' := by
    have e01 : x₀ * x₁ = x₂ := by
      have := eq_inv_of_mul_eq_one_left h012
      rwa [inv_eq_of_mul_eq_one_right h2] at this
    have e12 : x₁ * x₂ = x₀ := by
      have h : x₀ * (x₁ * x₂) = 1 := by rw [← mul_assoc]; exact h012
      have := eq_inv_of_mul_eq_one_right h
      rwa [inv_eq_of_mul_eq_one_right h0] at this
    have e02 : x₀ * x₂ = x₁ := by
      have := eq_mul_inv_of_mul_eq e12
      rw [inv_eq_of_mul_eq_one_right h2] at this
      exact this.symm
    have e10 : x₁ * x₀ = x₂ := (hc x₁ x₀).trans e01
    have e20 : x₂ * x₀ = x₁ := (hc x₂ x₀).trans e02
    have e21 : x₂ * x₁ = x₀ := (hc x₂ x₁).trans e12
    rintro a b (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl)
    all_goals simp [e01, e12, e02, e10, e20, e21, h0, h1, h2]
  inv_mem' := by
    rintro y (rfl | rfl | rfl | rfl)
    · exact Or.inl (inv_one)
    · exact Or.inr (Or.inl (inv_eq_of_mul_eq_one_right h0))
    · exact Or.inr (Or.inr (Or.inl (inv_eq_of_mul_eq_one_right h1)))
    · exact Or.inr (Or.inr (Or.inr (inv_eq_of_mul_eq_one_right h2)))

end Klein

section KleinSetting

variable {G : Type*} [Group G] {I S E : Subgroup G}

structure KData (Q : QuotSetting I S E) (g r : G) : Prop where
  g_mem : g ∈ I
  g3 : g * g * g ∈ S
  fix : ∀ s ∈ S, (g * s * g⁻¹)⁻¹ * s ∈ E → s ∈ E
  r_mem : r ∈ S
  r_sq : r * r = 1
  r_nE : r ∉ E
  norm : r * (g * r * g⁻¹) * (g * g * r * (g * g)⁻¹) ∈ E

namespace KData

variable {Q : QuotSetting I S E} {g r : G} [(E.subgroupOf S).Normal] (D : KData Q g r)

include D

noncomputable def x0 : SecQuot S E := secMk S E ⟨r, D.r_mem⟩

noncomputable def x1 : SecQuot S E := Q.convAct ⟨g, D.g_mem⟩ D.x0

noncomputable def x2 : SecQuot S E := Q.convAct ⟨g, D.g_mem⟩ D.x1

omit [(E.subgroupOf S).Normal] in
theorem g_conj_mem {s : G} (hs : s ∈ S) : g * s * g⁻¹ ∈ S := Q.nS g D.g_mem s hs

theorem x1_eq : D.x1 = secMk S E ⟨g * r * g⁻¹, D.g_conj_mem D.r_mem⟩ :=
  Q.convAct_mk ⟨g, D.g_mem⟩ ⟨r, D.r_mem⟩

theorem x2_eq : D.x2 = secMk S E ⟨g * g * r * (g * g)⁻¹,
    by have := D.g_conj_mem (D.g_conj_mem D.r_mem)
       have e : g * (g * r * g⁻¹) * g⁻¹ = g * g * r * (g * g)⁻¹ := by group
       rwa [e] at this⟩ := by
  unfold x2
  rw [x1_eq, Q.convAct_mk]
  congr 1
  apply Subtype.ext
  show g * (g * r * g⁻¹) * g⁻¹ = g * g * r * (g * g)⁻¹
  group

theorem conv_x2 : Q.convAct ⟨g, D.g_mem⟩ D.x2 = D.x0 := by
  have h3 : Q.convAct (⟨g, D.g_mem⟩ * ⟨g, D.g_mem⟩ * ⟨g, D.g_mem⟩) = 1 :=
    Q.convAct_ker _ D.g3
  have : Q.convAct ⟨g, D.g_mem⟩ D.x2 =
      Q.convAct (⟨g, D.g_mem⟩ * ⟨g, D.g_mem⟩ * ⟨g, D.g_mem⟩) D.x0 := by
    unfold x2 x1
    simp only [map_mul, MulAut.mul_apply]
  rw [this, h3]
  rfl

theorem prod : D.x0 * D.x1 * D.x2 = 1 := by
  rw [x1_eq, x2_eq, x0]
  rw [← map_mul, ← map_mul, secMk_eq_one_iff]
  exact D.norm

theorem fix_quot (y : SecQuot S E) (hy : Q.convAct ⟨g, D.g_mem⟩ y = y) : y = 1 := by
  obtain ⟨s, rfl⟩ := secMk_surjective (A := S) (B := E) y
  rw [Q.convAct_mk, secMk_eq_secMk_iff] at hy
  have h1 : (g * (s : G) * g⁻¹)⁻¹ * (s : G) ∈ E := hy
  exact secMk_eq_one_iff.mpr (D.fix s s.2 h1)

theorem x0_ne_one : D.x0 ≠ 1 := fun h => D.r_nE (secMk_eq_one_iff.mp h)

theorem x1_ne_one : D.x1 ≠ 1 := by
  intro h
  apply D.x0_ne_one
  have := congrArg (Q.convAct ⟨g, D.g_mem⟩).symm h
  simpa [x1] using this

theorem x2_ne_one : D.x2 ≠ 1 := by
  intro h
  apply D.x1_ne_one
  have := congrArg (Q.convAct ⟨g, D.g_mem⟩).symm h
  simpa [x2] using this

theorem x0_ne_x1 : D.x0 ≠ D.x1 := fun h => D.x0_ne_one (D.fix_quot _ h.symm)

theorem x1_ne_x2 : D.x1 ≠ D.x2 := by
  intro h
  apply D.x0_ne_x1
  exact (Q.convAct ⟨g, D.g_mem⟩).injective h

theorem x0_ne_x2 : D.x0 ≠ D.x2 := by
  intro h
  have h1 := D.prod
  rw [← h] at h1
  have h2 : D.x0 * D.x1 * D.x0 = D.x1 := by
    rw [Q.quot_comm D.x0 D.x1, mul_assoc, Q.quot_sq, mul_one]
  rw [h2] at h1
  exact D.x1_ne_one h1

noncomputable def kleinHat : Subgroup (SecQuot S E) :=
  klein Q.quot_comm D.x0 D.x1 D.x2 D.prod (Q.quot_sq _) (Q.quot_sq _) (Q.quot_sq _)

noncomputable def A : Subgroup G := preSub S E D.kleinHat

theorem mem_A_iff {x : G} : x ∈ D.A ↔ ∃ h : x ∈ S, secMk S E ⟨x, h⟩ ∈ D.kleinHat := mem_preSub

theorem E_le_A : E ≤ D.A := Q.S₂_le_preSub _

theorem A_le_S : D.A ≤ S := preSub_le _

theorem r_mem_A : r ∈ D.A := mem_preSub.2 ⟨D.r_mem, Or.inr (Or.inl rfl)⟩

theorem r1_mem_A : g * r * g⁻¹ ∈ D.A :=
  mem_preSub.2 ⟨D.g_conj_mem D.r_mem, Or.inr (Or.inr (Or.inl (by rw [x1_eq])))⟩

theorem r2_mem_A : g * g * r * (g * g)⁻¹ ∈ D.A := by
  refine mem_preSub.2 ⟨?_, Or.inr (Or.inr (Or.inr ?_))⟩
  · have := D.g_conj_mem (D.g_conj_mem D.r_mem)
    have e : g * (g * r * g⁻¹) * g⁻¹ = g * g * r * (g * g)⁻¹ := by group
    rwa [e] at this
  · rw [x2_eq]

theorem mem_A_cases {x : G} (hx : x ∈ D.A) :
    ∃ e ∈ E, x = e ∨ x = r * e ∨ x = g * r * g⁻¹ * e ∨ x = g * g * r * (g * g)⁻¹ * e := by
  obtain ⟨hxS, hk⟩ := D.mem_A_iff.mp hx
  rcases hk with h1 | h1 | h1 | h1
  · refine ⟨x, secMk_eq_one_iff.mp h1, Or.inl rfl⟩
  · have h2 : secMk S E ⟨x, hxS⟩ = secMk S E ⟨r, D.r_mem⟩ := h1
    rw [secMk_eq_secMk_iff] at h2
    refine ⟨r⁻¹ * x, ?_, Or.inr (Or.inl (by group))⟩
    have := E.inv_mem h2
    simpa using this
  · have h2 : secMk S E ⟨x, hxS⟩ = secMk S E ⟨g * r * g⁻¹, D.g_conj_mem D.r_mem⟩ := by
      rw [← x1_eq]; exact h1
    rw [secMk_eq_secMk_iff] at h2
    refine ⟨(g * r * g⁻¹)⁻¹ * x, ?_, Or.inr (Or.inr (Or.inl (by group)))⟩
    have := E.inv_mem h2
    simpa using this
  · have h2 : secMk S E ⟨x, hxS⟩ = secMk S E ⟨g * g * r * (g * g)⁻¹, by
        have := D.g_conj_mem (D.g_conj_mem D.r_mem)
        have e : g * (g * r * g⁻¹) * g⁻¹ = g * g * r * (g * g)⁻¹ := by group
        rwa [e] at this⟩ := by
      rw [← x2_eq]; exact h1
    rw [secMk_eq_secMk_iff] at h2
    refine ⟨(g * g * r * (g * g)⁻¹)⁻¹ * x, ?_, Or.inr (Or.inr (Or.inr (by group)))⟩
    have := E.inv_mem h2
    simpa using this

theorem sq_of_mem_A (hEc : ∀ e ∈ E, ∀ s ∈ S, e * s = s * e) (hE2 : ∀ e ∈ E, e * e = 1) {x : G}
    (hx : x ∈ D.A) : x * x = 1 := by
  obtain ⟨e, he, hcases⟩ := D.mem_A_cases hx
  have key : ∀ y : G, y ∈ S → y * y = 1 → (y * e) * (y * e) = 1 := by
    intro y hyS hy2
    calc y * e * (y * e) = y * (e * y) * e := by group
      _ = y * (y * e) * e := by rw [hEc e he y hyS]
      _ = (y * y) * (e * e) := by group
      _ = 1 := by rw [hy2, hE2 e he, mul_one]
  rcases hcases with rfl | rfl | rfl | rfl
  · exact hE2 _ he
  · exact key r D.r_mem D.r_sq
  · refine key _ (D.g_conj_mem D.r_mem) ?_
    calc g * r * g⁻¹ * (g * r * g⁻¹) = g * (r * r) * g⁻¹ := by group
      _ = 1 := by rw [D.r_sq]; group
  · refine key _ ?_ ?_
    · have := D.g_conj_mem (D.g_conj_mem D.r_mem)
      have e : g * (g * r * g⁻¹) * g⁻¹ = g * g * r * (g * g)⁻¹ := by group
      rwa [e] at this
    · have e : g * g * r * (g * g)⁻¹ * (g * g * r * (g * g)⁻¹) =
          (g * g) * (r * r) * (g * g)⁻¹ := by group
      rw [e, D.r_sq]
      group

theorem card_kleinHat : Nat.card ↥D.kleinHat = 4 := by
  have hset : (D.kleinHat : Set (SecQuot S E)) = {1, D.x0, D.x1, D.x2} := by
    ext y
    simp [kleinHat, klein]
  have h1 : Nat.card ↥D.kleinHat = (D.kleinHat : Set (SecQuot S E)).ncard :=
    Nat.card_coe_set_eq _
  rw [h1, hset]
  have n01 : D.x0 ≠ 1 := D.x0_ne_one
  have n11 : D.x1 ≠ 1 := D.x1_ne_one
  have n21 : D.x2 ≠ 1 := D.x2_ne_one
  rw [Set.ncard_insert_of_notMem (by simp [n01.symm, n11.symm, n21.symm]),
    Set.ncard_insert_of_notMem (by simp [D.x0_ne_x1, D.x0_ne_x2]),
    Set.ncard_insert_of_notMem (by simp [D.x1_ne_x2]), Set.ncard_singleton]

theorem mem_kleinHat_iff {y : SecQuot S E} :
    y ∈ D.kleinHat ↔ y = 1 ∨ y = D.x0 ∨ y = D.x1 ∨ y = D.x2 := Iff.rfl

theorem card_A (hE : Nat.card E = 4) : Nat.card D.A = 16 := by
  have h1 : Nat.card ↥((D.A.subgroupOf S).map (secMk S E)) *
      Nat.card ↥(D.A ⊓ (secMk S E).ker.map S.subtype) = Nat.card D.A :=
    card_map_mul_card_inf_ker D.A_le_S (secMk S E)
  have hker : (secMk S E).ker.map S.subtype = E := by
    show (QuotientGroup.mk' (E.subgroupOf S)).ker.map S.subtype = E
    rw [QuotientGroup.ker_mk', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr Q.S₂_le]
  have hcomap : D.A.subgroupOf S = D.kleinHat.comap (secMk S E) := map_subtype_subgroupOf' _
  rw [hker, hcomap, Subgroup.map_comap_eq_self_of_surjective secMk_surjective,
    inf_eq_right.mpr D.E_le_A, D.card_kleinHat, hE] at h1
  omega

structure UData (D : KData Q g r) (u : G) : Prop where
  u_mem : u ∈ I
  u_r : (u * r * u⁻¹)⁻¹ * r ∈ E
  u_g : u * g * u⁻¹ * g ∈ S
  gen : ∀ γ ∈ I, ∃ w : G, (w = 1 ∨ w = u ∨ w = g ∨ w = g * g ∨ w = u * g ∨ w = u * (g * g)) ∧
    γ * w⁻¹ ∈ S

variable {u : G} (U : UData D u)

include U

theorem act_x0 : Q.convAct ⟨u, U.u_mem⟩ D.x0 = D.x0 := by
  unfold KData.x0
  rw [Q.convAct_mk, secMk_eq_secMk_iff]
  exact U.u_r

theorem act_comm : Q.convAct ⟨u, U.u_mem⟩ * Q.convAct ⟨g, D.g_mem⟩ =
    (Q.convAct ⟨g, D.g_mem⟩)⁻¹ * Q.convAct ⟨u, U.u_mem⟩ := by
  have hab : Q.convAct ⟨u, U.u_mem⟩ * Q.convAct ⟨g, D.g_mem⟩ * (Q.convAct ⟨u, U.u_mem⟩)⁻¹ *
      Q.convAct ⟨g, D.g_mem⟩ = 1 := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
    exact Q.convAct_ker _ U.u_g
  exact mul_inv_eq_iff_eq_mul.mp (eq_inv_of_mul_eq_one_left hab)

theorem act_x1 : Q.convAct ⟨u, U.u_mem⟩ D.x1 = D.x2 := by
  have hbx2 : Q.convAct ⟨g, D.g_mem⟩ D.x2 = D.x0 := D.conv_x2
  have hbinv0 : (Q.convAct ⟨g, D.g_mem⟩)⁻¹ D.x0 = D.x2 := by rw [← hbx2]; simp
  calc Q.convAct ⟨u, U.u_mem⟩ D.x1
      = (Q.convAct ⟨u, U.u_mem⟩ * Q.convAct ⟨g, D.g_mem⟩) D.x0 := by
        rw [MulAut.mul_apply]; rfl
    _ = (Q.convAct ⟨g, D.g_mem⟩)⁻¹ (Q.convAct ⟨u, U.u_mem⟩ D.x0) := by
        rw [D.act_comm U, MulAut.mul_apply]
    _ = D.x2 := by rw [D.act_x0 U, hbinv0]

theorem act_x2 : Q.convAct ⟨u, U.u_mem⟩ D.x2 = D.x1 := by
  have hbinv2 : (Q.convAct ⟨g, D.g_mem⟩)⁻¹ D.x2 = D.x1 := by
    have : Q.convAct ⟨g, D.g_mem⟩ D.x1 = D.x2 := rfl
    rw [← this]; simp
  calc Q.convAct ⟨u, U.u_mem⟩ D.x2
      = (Q.convAct ⟨u, U.u_mem⟩ * Q.convAct ⟨g, D.g_mem⟩) D.x1 := by
        rw [MulAut.mul_apply]; rfl
    _ = (Q.convAct ⟨g, D.g_mem⟩)⁻¹ (Q.convAct ⟨u, U.u_mem⟩ D.x1) := by
        rw [D.act_comm U, MulAut.mul_apply]
    _ = D.x1 := by rw [D.act_x1 U, hbinv2]

omit [(E.subgroupOf S).Normal] in
theorem conj_r : (u * r * u⁻¹)⁻¹ * r ∈ E := U.u_r

theorem conj_r1 : (u * (g * r * g⁻¹) * u⁻¹)⁻¹ * (g * g * r * (g * g)⁻¹) ∈ E := by
  have h1 := D.act_x1 U
  rw [D.x1_eq, Q.convAct_mk, D.x2_eq, secMk_eq_secMk_iff] at h1
  exact h1

theorem convAct_kleinHat_le {γ : ↥I} {y : SecQuot S E} (hy : y ∈ D.kleinHat) :
    Q.convAct γ y ∈ D.kleinHat := by
  set γg : ↥I := ⟨g, D.g_mem⟩ with hγg
  set γu : ↥I := ⟨u, U.u_mem⟩ with hγu
  have hbx0 : Q.convAct γg D.x0 = D.x1 := rfl
  have hbx1 : Q.convAct γg D.x1 = D.x2 := rfl
  have hbx2 : Q.convAct γg D.x2 = D.x0 := D.conv_x2
  have hstab_a : ∀ z ∈ D.kleinHat, Q.convAct γu z ∈ D.kleinHat := by
    intro z hz
    rcases (D.mem_kleinHat_iff).mp hz with rfl | rfl | rfl | rfl
    · rw [map_one]; exact D.kleinHat.one_mem
    · rw [D.act_x0 U]; exact (D.mem_kleinHat_iff).mpr (Or.inr (Or.inl rfl))
    · rw [D.act_x1 U]; exact (D.mem_kleinHat_iff).mpr (Or.inr (Or.inr (Or.inr rfl)))
    · rw [D.act_x2 U]; exact (D.mem_kleinHat_iff).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hstab_b : ∀ z ∈ D.kleinHat, Q.convAct γg z ∈ D.kleinHat := by
    intro z hz
    rcases (D.mem_kleinHat_iff).mp hz with rfl | rfl | rfl | rfl
    · rw [map_one]; exact D.kleinHat.one_mem
    · rw [hbx0]; exact (D.mem_kleinHat_iff).mpr (Or.inr (Or.inr (Or.inl rfl)))
    · rw [hbx1]; exact (D.mem_kleinHat_iff).mpr (Or.inr (Or.inr (Or.inr rfl)))
    · rw [hbx2]; exact (D.mem_kleinHat_iff).mpr (Or.inr (Or.inl rfl))
  obtain ⟨w, hw, hwS⟩ := U.gen γ γ.2
  have key : ∀ w' : ↥I, ((γ : G) * (w' : G)⁻¹ ∈ S) → Q.convAct γ = Q.convAct w' := by
    intro w' hS
    have e : γ = ⟨(γ : G) * (w' : G)⁻¹, I.mul_mem γ.2 (I.inv_mem w'.2)⟩ * w' :=
      Subtype.ext (by simp)
    rw [e, map_mul, Q.convAct_ker ⟨(γ : G) * (w' : G)⁻¹, I.mul_mem γ.2 (I.inv_mem w'.2)⟩ hS,
      one_mul]
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [key 1 (by simpa using hwS), map_one]; exact hy
  · rw [key γu hwS]; exact hstab_a _ hy
  · rw [key γg hwS]; exact hstab_b _ hy
  · rw [key (γg * γg) (by simpa using hwS), map_mul, MulAut.mul_apply]
    exact hstab_b _ (hstab_b _ hy)
  · rw [key (γu * γg) (by simpa using hwS), map_mul, MulAut.mul_apply]
    exact hstab_a _ (hstab_b _ hy)
  · rw [key (γu * (γg * γg)) (by simpa using hwS), map_mul, map_mul, MulAut.mul_apply,
      MulAut.mul_apply]
    exact hstab_a _ (hstab_b _ (hstab_b _ hy))

theorem conj_mem_A {γ : G} (hγ : γ ∈ I) {x : G} (hx : x ∈ D.A) : γ * x * γ⁻¹ ∈ D.A := by
  obtain ⟨hxS, hk⟩ := D.mem_A_iff.mp hx
  refine D.mem_A_iff.mpr ⟨Q.nS γ hγ x hxS, ?_⟩
  have := D.convAct_kleinHat_le U (γ := ⟨γ, hγ⟩) hk
  rwa [Q.convAct_mk] at this

end KData

end KleinSetting

end S143

end CFSG.Quasithin
