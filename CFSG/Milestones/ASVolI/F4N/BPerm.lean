module

public import CFSG.Quasithin.Recognition.CertU33DcPG

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.CosetTable CFSG.Sporadic.Bridge

@[expose] def burnsideF4nB_R (l : List ℕ) (g : U33G) : Prop := RepL l (u33PresHom g)

@[expose] def burnsideF4nB_TL (i : ℕ) : List ℕ := u33TelTab.getD i []

@[expose] def burnsideF4nB_DL (j : ℕ) : List ℕ := u33DTab.getD j []

@[expose] def burnsideF4nB_DIL (j : ℕ) : List ℕ := u33DInvTab.getD j []

@[expose] def burnsideF4nB_GL (k : ℕ) : List ℕ := u33GenTab.getD k []

@[expose] def burnsideF4nB_GIL (k : ℕ) : List ℕ := u33GenInvTab.getD k []

abbrev burnsideF4nB_t (i : ℕ) : U33G := u33Tel u33GenPG i

abbrev burnsideF4nB_d (j : ℕ) : U33G := u33D u33GenPG j

theorem burnsideF4nB_R_mul {l m : List ℕ} {g h : U33G} (hg : burnsideF4nB_R l g)
    (hh : burnsideF4nB_R m h) : burnsideF4nB_R (compL l m) (g * h) := by
  unfold burnsideF4nB_R at *
  rw [map_mul]
  exact repL_mul hg hh

theorem burnsideF4nB_R_one : burnsideF4nB_R (List.range 28) 1 := by
  unfold burnsideF4nB_R
  rw [map_one]
  exact repL_one 28

theorem burnsideF4nB_R_t {i : ℕ} (hi : i < 32) :
    burnsideF4nB_R (burnsideF4nB_TL i) (burnsideF4nB_t i) := by
  unfold burnsideF4nB_R burnsideF4nB_TL burnsideF4nB_t
  rw [u33Tel_hom]
  exact u33_telTab_rep i hi

theorem burnsideF4nB_R_d {j : ℕ} (hj : j < 14) :
    burnsideF4nB_R (burnsideF4nB_DL j) (burnsideF4nB_d j) := by
  unfold burnsideF4nB_R burnsideF4nB_DL burnsideF4nB_d
  rw [u33D_hom]
  exact u33_dTab_rep j hj

theorem burnsideF4nB_R_dinv {j : ℕ} (hj : j < 14) :
    burnsideF4nB_R (burnsideF4nB_DIL j) (burnsideF4nB_d j)⁻¹ := by
  unfold burnsideF4nB_R burnsideF4nB_DIL burnsideF4nB_d
  rw [map_inv, u33D_hom]
  exact u33_dInvTab_rep j hj

theorem burnsideF4nB_R_gen {k : ℕ} (hk : k < 5) :
    burnsideF4nB_R (burnsideF4nB_GL k) (u33GenPG k) := by
  unfold burnsideF4nB_R burnsideF4nB_GL
  rw [u33PresHom_genPG]
  exact u33_genTab_rep k hk

theorem burnsideF4nB_R_geninv {k : ℕ} (hk : k < 5) :
    burnsideF4nB_R (burnsideF4nB_GIL k) (u33GenPG k)⁻¹ := by
  unfold burnsideF4nB_R burnsideF4nB_GIL
  rw [map_inv, u33PresHom_genPG]
  exact u33_genInvTab_rep k hk

theorem burnsideF4nB_R_eq
    {l l' : List ℕ} {g h : U33G} (hg : burnsideF4nB_R l g) (hh : burnsideF4nB_R l' h)
    (hl : l = l') : g = h := by
  subst hl
  exact u33PresHom_injective (eq_of_repL hg hh)

theorem burnsideF4nB_R_unique {l l' : List ℕ} {g h : U33G} (hg : burnsideF4nB_R l g)
    (hh : burnsideF4nB_R l' h) (he : g = h) : l = l' := by
  subst he
  exact repL_unique hg hh

theorem burnsideF4nB_K4_check : ∀ k < 32,
    compL (compL (burnsideF4nB_DL 1) (burnsideF4nB_TL k))
      (compL (burnsideF4nB_DL 1) (burnsideF4nB_TL k)) = List.range 28 ↔
      (k = 5 ∨ k = 18 ∨ k = 29 ∨ k = 30) := by
  decide +kernel

theorem burnsideF4nB_ab_check : ∀ g ∈ [0, 1, 2, 4],
    compL (burnsideF4nB_TL 9) (burnsideF4nB_GL g) = compL (burnsideF4nB_GL g) (burnsideF4nB_TL 9) := by
  decide +kernel

theorem burnsideF4nB_pow_check :
    burnsideF4nB_TL 9 = compL (burnsideF4nB_GL 0) (burnsideF4nB_GL 1) ∧
    burnsideF4nB_TL 26 = compL (burnsideF4nB_TL 9) (burnsideF4nB_TL 9) ∧
    burnsideF4nB_TL 6 = compL (burnsideF4nB_TL 9) (burnsideF4nB_TL 26) ∧
    burnsideF4nB_TL 0 = List.range 28 := by
  decide +kernel

theorem burnsideF4nB_conj_check :
    compL (compL (burnsideF4nB_GL 2) (burnsideF4nB_GL 0)) (burnsideF4nB_GIL 2) = burnsideF4nB_GL 1 ∧
    compL (compL (burnsideF4nB_GIL 2) (burnsideF4nB_GL 0)) (burnsideF4nB_GL 2) = burnsideF4nB_GL 1 ∧
    compL (compL (burnsideF4nB_GL 2) (burnsideF4nB_GL 1)) (burnsideF4nB_GIL 2) = burnsideF4nB_GL 0 ∧
    compL (compL (burnsideF4nB_GIL 2) (burnsideF4nB_GL 1)) (burnsideF4nB_GL 2) = burnsideF4nB_GL 0 ∧
    compL (compL (burnsideF4nB_GL 3) (burnsideF4nB_GL 0)) (burnsideF4nB_GIL 3) =
      compL (burnsideF4nB_GIL 0) (burnsideF4nB_GIL 1) ∧
    compL (compL (burnsideF4nB_GIL 3) (burnsideF4nB_GL 0)) (burnsideF4nB_GL 3) = burnsideF4nB_GL 1 ∧
    compL (compL (burnsideF4nB_GL 3) (burnsideF4nB_GL 1)) (burnsideF4nB_GIL 3) = burnsideF4nB_GL 0 ∧
    compL (compL (burnsideF4nB_GIL 3) (burnsideF4nB_GL 1)) (burnsideF4nB_GL 3) =
      compL (burnsideF4nB_GIL 0) (burnsideF4nB_GIL 1) := by
  decide +kernel

theorem burnsideF4nB_trans_check : ∀ k ∈ [5, 18, 29, 30], ∀ k' ∈ [5, 18, 29, 30],
    ∃ n ∈ [0, 9, 26, 6],
      compL (burnsideF4nB_TL n) (compL (burnsideF4nB_DL 1) (burnsideF4nB_TL k)) =
        compL (compL (burnsideF4nB_DL 1) (burnsideF4nB_TL k')) (burnsideF4nB_TL n) := by
  decide +kernel

@[expose] def burnsideF4nB_cosA : List (ℕ × ℕ) :=
  [(0, 0), (0, 9), (0, 1), (0, 6), (0, 3), (1, 0), (0, 4), (0, 16), (0, 26), (0, 2), (1, 3), (0, 17),
    (0, 8), (1, 6), (1, 9), (1, 1), (0, 19), (0, 22), (1, 8), (0, 7), (1, 2), (1, 17), (0, 11),
    (1, 26), (1, 16), (1, 4), (0, 12), (1, 7), (1, 11), (1, 22), (1, 19), (1, 12)]

@[expose] def burnsideF4nB_cosB : List (ℕ × ℕ) :=
  [(0, 0), (1, 0), (1, 23), (1, 21), (1, 9), (0, 8), (0, 6), (0, 23), (0, 21), (0, 9), (1, 20),
    (0, 18), (0, 24), (1, 11), (1, 5), (1, 8), (1, 6), (1, 18), (0, 20), (1, 26), (0, 11), (0, 5),
    (1, 24), (0, 25), (0, 31), (0, 7), (0, 26), (1, 31), (1, 7), (1, 12), (1, 25), (0, 12)]

theorem burnsideF4nB_cosA_check : ∀ m < 32, (burnsideF4nB_cosA.getD m (0, 0)).2 < 32 ∧
    ((burnsideF4nB_cosA.getD m (0, 0)).1 = 0 ∧
      compL (burnsideF4nB_TL m) (burnsideF4nB_DL 1) =
        compL (burnsideF4nB_DL 1) (burnsideF4nB_TL (burnsideF4nB_cosA.getD m (0, 0)).2) ∨
     (burnsideF4nB_cosA.getD m (0, 0)).1 = 1 ∧
      compL (burnsideF4nB_TL m) (burnsideF4nB_DL 1) =
        compL (compL (burnsideF4nB_TL 5) (burnsideF4nB_DL 1))
          (burnsideF4nB_TL (burnsideF4nB_cosA.getD m (0, 0)).2)) := by
  decide +kernel

theorem burnsideF4nB_cosB_check : ∀ m < 32, (burnsideF4nB_cosB.getD m (0, 0)).2 < 32 ∧
    ((burnsideF4nB_cosB.getD m (0, 0)).1 = 0 ∧
      compL (burnsideF4nB_TL m) (burnsideF4nB_DL 2) =
        compL (burnsideF4nB_DL 2) (burnsideF4nB_TL (burnsideF4nB_cosB.getD m (0, 0)).2) ∨
     (burnsideF4nB_cosB.getD m (0, 0)).1 = 1 ∧
      compL (burnsideF4nB_TL m) (burnsideF4nB_DL 2) =
        compL (compL (burnsideF4nB_TL 1) (burnsideF4nB_DL 2))
          (burnsideF4nB_TL (burnsideF4nB_cosB.getD m (0, 0)).2)) := by
  decide +kernel

theorem burnsideF4nB_sepA_check : ∀ i < 32,
    burnsideF4nB_TL i ≠ compL (burnsideF4nB_TL 5) (burnsideF4nB_DL 1) ∧
    burnsideF4nB_TL i ≠ compL (burnsideF4nB_DIL 1) (compL (burnsideF4nB_TL 5) (burnsideF4nB_DL 1)) := by
  decide +kernel

theorem burnsideF4nB_sepB_check : ∀ i < 32,
    burnsideF4nB_TL i ≠ compL (burnsideF4nB_TL 1) (burnsideF4nB_DL 2) ∧
    burnsideF4nB_TL i ≠ compL (burnsideF4nB_DIL 2) (compL (burnsideF4nB_TL 1) (burnsideF4nB_DL 2)) := by
  decide +kernel

theorem burnsideF4nB_K4
    {k : ℕ} (hk : k < 32) :
    burnsideF4nB_d 1 * burnsideF4nB_t k * (burnsideF4nB_d 1 * burnsideF4nB_t k) = 1 ↔
      (k = 5 ∨ k = 18 ∨ k = 29 ∨ k = 30) := by
  have hR := burnsideF4nB_R_mul
    (burnsideF4nB_R_mul (burnsideF4nB_R_d (j := 1) (by norm_num)) (burnsideF4nB_R_t hk))
    (burnsideF4nB_R_mul (burnsideF4nB_R_d (j := 1) (by norm_num)) (burnsideF4nB_R_t hk))
  rw [← burnsideF4nB_K4_check k hk]
  exact ⟨fun h => burnsideF4nB_R_unique hR burnsideF4nB_R_one h,
    fun h => burnsideF4nB_R_eq hR burnsideF4nB_R_one h⟩

theorem burnsideF4nB_ab_comm
    {g : ℕ} (hg : g ∈ [0, 1, 2, 4]) :
    burnsideF4nB_t 9 * u33GenPG g = u33GenPG g * burnsideF4nB_t 9 := by
  have hg5 : g < 5 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hg; omega
  exact burnsideF4nB_R_eq (burnsideF4nB_R_mul (burnsideF4nB_R_t (by norm_num)) (burnsideF4nB_R_gen hg5))
    (burnsideF4nB_R_mul (burnsideF4nB_R_gen hg5) (burnsideF4nB_R_t (by norm_num)))
    (burnsideF4nB_ab_check g hg)

theorem burnsideF4nB_pow :
    burnsideF4nB_t 9 = u33GenPG 0 * u33GenPG 1 ∧
    burnsideF4nB_t 26 = burnsideF4nB_t 9 * burnsideF4nB_t 9 ∧
    burnsideF4nB_t 6 = burnsideF4nB_t 9 * burnsideF4nB_t 26 ∧ burnsideF4nB_t 0 = 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := burnsideF4nB_pow_check
  refine ⟨burnsideF4nB_R_eq (burnsideF4nB_R_t (by norm_num))
      (burnsideF4nB_R_mul (burnsideF4nB_R_gen (by norm_num)) (burnsideF4nB_R_gen (by norm_num))) h1,
    burnsideF4nB_R_eq (burnsideF4nB_R_t (by norm_num))
      (burnsideF4nB_R_mul (burnsideF4nB_R_t (by norm_num)) (burnsideF4nB_R_t (by norm_num))) h2,
    burnsideF4nB_R_eq (burnsideF4nB_R_t (by norm_num))
      (burnsideF4nB_R_mul (burnsideF4nB_R_t (by norm_num)) (burnsideF4nB_R_t (by norm_num))) h3,
    burnsideF4nB_R_eq (burnsideF4nB_R_t (by norm_num)) burnsideF4nB_R_one h4⟩

@[expose] noncomputable def burnsideF4nB_Z : Subgroup U33G := Subgroup.zpowers (burnsideF4nB_t 9)

@[expose] noncomputable def burnsideF4nB_Q : Subgroup U33G :=
  Subgroup.closure {u33GenPG 0, u33GenPG 1}

theorem burnsideF4nB_Z_central
    {d g : U33G} (hd : d ∈ burnsideF4nB_Z) (hg : g ∈ u33Data.B) :
    g * d = d * g := by
  have hB : u33Data.B ≤ Subgroup.centralizer ({burnsideF4nB_t 9} : Set U33G) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    rintro h rfl
    rcases hx with rfl | rfl | rfl | rfl
    · exact burnsideF4nB_ab_comm (g := 0) (by simp)
    · exact burnsideF4nB_ab_comm (g := 1) (by simp)
    · exact burnsideF4nB_ab_comm (g := 2) (by simp)
    · exact burnsideF4nB_ab_comm (g := 4) (by simp)
  have h9 : burnsideF4nB_t 9 ∈ Subgroup.centralizer (u33Data.B : Set U33G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := Subgroup.mem_centralizer_iff.1 (hB hx) (burnsideF4nB_t 9) rfl
    exact this.symm
  have hZ : burnsideF4nB_Z ≤ Subgroup.centralizer (u33Data.B : Set U33G) :=
    (Subgroup.zpowers_le).2 h9
  exact Subgroup.mem_centralizer_iff.1 (hZ hd) g hg

theorem burnsideF4nB_mem_normalizer_closure {G : Type*} [Group G] {S : Set G} {g : G}
    (h1 : ∀ u ∈ S, g * u * g⁻¹ ∈ Subgroup.closure S)
    (h2 : ∀ u ∈ S, g⁻¹ * u * g ∈ Subgroup.closure S) :
    g ∈ Subgroup.normalizer (Subgroup.closure S : Set G) := by
  have key : ∀ k : G, (∀ u ∈ S, k * u * k⁻¹ ∈ Subgroup.closure S) →
      ∀ h ∈ Subgroup.closure S, k * h * k⁻¹ ∈ Subgroup.closure S := by
    intro k hk h hh
    have hle : (Subgroup.closure S).map (MulAut.conj k).toMonoidHom ≤ Subgroup.closure S := by
      rw [MonoidHom.map_closure]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨u, hu, rfl⟩
      exact hk u hu
    exact hle ⟨h, hh, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key g h1 h hh, fun hh => ?_⟩
  have h2' : ∀ u ∈ S, g⁻¹ * u * g⁻¹⁻¹ ∈ Subgroup.closure S := by
    intro u hu
    rw [inv_inv]
    exact h2 u hu
  have := key g⁻¹ h2' _ hh
  rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at this

theorem burnsideF4nB_Q_props :
    burnsideF4nB_Q ≤ u33Data.T ∧ IsPGroup 2 burnsideF4nB_Q ∧
      u33Data.A ≤ Subgroup.normalizer (burnsideF4nB_Q : Set U33G) ∧ burnsideF4nB_Z ≤ burnsideF4nB_Q := by
  have hQT : burnsideF4nB_Q ≤ u33Data.T := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x (rfl | rfl)
    · exact u33Data.a_mem_T
    · exact u33Data.b_mem_T
  have ha : u33GenPG 0 ∈ burnsideF4nB_Q := Subgroup.subset_closure (Or.inl rfl)
  have hb : u33GenPG 1 ∈ burnsideF4nB_Q := Subgroup.subset_closure (Or.inr rfl)
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := burnsideF4nB_conj_check
  have hab' : (u33GenPG 0)⁻¹ * (u33GenPG 1)⁻¹ ∈ burnsideF4nB_Q :=
    burnsideF4nB_Q.mul_mem (burnsideF4nB_Q.inv_mem ha) (burnsideF4nB_Q.inv_mem hb)
  have R := fun {k : ℕ} (hk : k < 5) => burnsideF4nB_R_gen hk
  have Ri := fun {k : ℕ} (hk : k < 5) => burnsideF4nB_R_geninv hk
  have hs : u33GenPG 2 ∈ Subgroup.normalizer (burnsideF4nB_Q : Set U33G) := by
    refine burnsideF4nB_mem_normalizer_closure ?_ ?_
    · rintro u (rfl | rfl)
      · rw [burnsideF4nB_R_eq (burnsideF4nB_R_mul (burnsideF4nB_R_mul (R (k := 2) (by norm_num))
          (R (k := 0) (by norm_num))) (Ri (k := 2) (by norm_num))) (R (k := 1) (by norm_num)) c1]
        exact hb
      · rw [burnsideF4nB_R_eq (burnsideF4nB_R_mul (burnsideF4nB_R_mul (R (k := 2) (by norm_num))
          (R (k := 1) (by norm_num))) (Ri (k := 2) (by norm_num))) (R (k := 0) (by norm_num)) c3]
        exact ha
    · rintro u (rfl | rfl)
      · rw [burnsideF4nB_R_eq (burnsideF4nB_R_mul (burnsideF4nB_R_mul (Ri (k := 2) (by norm_num))
          (R (k := 0) (by norm_num))) (R (k := 2) (by norm_num))) (R (k := 1) (by norm_num)) c2]
        exact hb
      · rw [burnsideF4nB_R_eq (burnsideF4nB_R_mul (burnsideF4nB_R_mul (Ri (k := 2) (by norm_num))
          (R (k := 1) (by norm_num))) (R (k := 2) (by norm_num))) (R (k := 0) (by norm_num)) c4]
        exact ha
  have hx : u33GenPG 3 ∈ Subgroup.normalizer (burnsideF4nB_Q : Set U33G) := by
    refine burnsideF4nB_mem_normalizer_closure ?_ ?_
    · rintro u (rfl | rfl)
      · rw [burnsideF4nB_R_eq (burnsideF4nB_R_mul (burnsideF4nB_R_mul (R (k := 3) (by norm_num))
          (R (k := 0) (by norm_num))) (Ri (k := 3) (by norm_num)))
          (burnsideF4nB_R_mul (Ri (k := 0) (by norm_num)) (Ri (k := 1) (by norm_num))) c5]
        exact hab'
      · rw [burnsideF4nB_R_eq (burnsideF4nB_R_mul (burnsideF4nB_R_mul (R (k := 3) (by norm_num))
          (R (k := 1) (by norm_num))) (Ri (k := 3) (by norm_num))) (R (k := 0) (by norm_num)) c7]
        exact ha
    · rintro u (rfl | rfl)
      · rw [burnsideF4nB_R_eq (burnsideF4nB_R_mul (burnsideF4nB_R_mul (Ri (k := 3) (by norm_num))
          (R (k := 0) (by norm_num))) (R (k := 3) (by norm_num))) (R (k := 1) (by norm_num)) c6]
        exact hb
      · rw [burnsideF4nB_R_eq (burnsideF4nB_R_mul (burnsideF4nB_R_mul (Ri (k := 3) (by norm_num))
          (R (k := 1) (by norm_num))) (R (k := 3) (by norm_num)))
          (burnsideF4nB_R_mul (Ri (k := 0) (by norm_num)) (Ri (k := 1) (by norm_num))) c8]
        exact hab'
  refine ⟨hQT, u33_syl.1.to_le hQT, ?_, ?_⟩
  · refine (Subgroup.closure_le _).2 ?_
    rintro g (rfl | rfl | rfl | rfl)
    · exact Subgroup.le_normalizer ha
    · exact Subgroup.le_normalizer hb
    · exact hs
    · exact hx
  · refine (Subgroup.zpowers_le).2 ?_
    rw [burnsideF4nB_pow.1]
    exact burnsideF4nB_Q.mul_mem ha hb

theorem burnsideF4nB_relIndex_three {G : Type*} [Group G] {T A : Subgroup G} {r₁ r₂ : G}
    (h1 : r₁ ∈ A) (h2 : r₂ ∈ A)
    (hcov : ∀ g ∈ A, g ∈ T ∨ r₁⁻¹ * g ∈ T ∨ r₂⁻¹ * g ∈ T) (hn1 : r₁ ∉ T) (hn2 : r₂ ∉ T)
    (hn12 : r₁⁻¹ * r₂ ∉ T) : T.relIndex A = 3 := by
  unfold Subgroup.relIndex
  rw [Subgroup.index_eq_card]
  let r : Fin 3 → ↥A := ![1, ⟨r₁, h1⟩, ⟨r₂, h2⟩]
  let f : Fin 3 → ↥A ⧸ T.subgroupOf A := fun i => (r i : ↥A ⧸ T.subgroupOf A)
  have hmem : ∀ x y : ↥A, (x : ↥A ⧸ T.subgroupOf A) = y ↔ ((x : G)⁻¹ * (y : G)) ∈ T := by
    intro x y
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    rfl
  have hn1' : r₁⁻¹ ∉ T := fun h => hn1 (by simpa using T.inv_mem h)
  have hn2' : r₂⁻¹ ∉ T := fun h => hn2 (by simpa using T.inv_mem h)
  have hn21 : r₂⁻¹ * r₁ ∉ T := fun h => hn12 (by simpa using T.inv_mem h)
  have hf : Function.Bijective f := by
    refine ⟨fun i j hij => ?_, fun q => ?_⟩
    · have h := (hmem _ _).1 hij
      fin_cases i <;> fin_cases j <;> simp_all [r]
    · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      rcases hcov g g.2 with h | h | h
      · exact ⟨0, (hmem _ _).2 (by simpa [r] using h)⟩
      · exact ⟨1, (hmem _ _).2 (by simpa [r] using h)⟩
      · exact ⟨2, (hmem _ _).2 (by simpa [r] using h)⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_fin]

theorem burnsideF4nB_mem_T
    {g : U33G} (hg : g ∈ u33Data.T) :
    ∃ i : ℕ, i < 32 ∧ burnsideF4nB_t i = g := by
  obtain ⟨i, hi⟩ := (u33Data.mem_T_iff g).1 hg
  exact ⟨i, i.2, hi⟩

theorem burnsideF4nB_t_mem
    {i : ℕ} (hi : i < 32) : burnsideF4nB_t i ∈ u33Data.T :=
  u33Data.Tel_mem_T ⟨i, hi⟩

theorem burnsideF4nB_not_mem_T
    {l : List ℕ} {g : U33G} (hg : burnsideF4nB_R l g)
    (hl : ∀ i < 32, burnsideF4nB_TL i ≠ l) : g ∉ u33Data.T := by
  intro h
  obtain ⟨i, hi, rfl⟩ := burnsideF4nB_mem_T h
  exact hl i hi (burnsideF4nB_R_unique (burnsideF4nB_R_t hi) hg rfl)

theorem burnsideF4nB_D_ja :
    u33Data.D u33Data.ja = burnsideF4nB_d 1 := by
  have h : u33Data.D u33Data.ja = u33D u33GenPG ((1 : Fin 14) : ℕ) := by
    rw [show u33Data.ja = 1 from rfl]; rfl
  rw [h]
  exact congrArg (u33D u33GenPG) (by decide)

theorem burnsideF4nB_D_jb :
    u33Data.D u33Data.jb = burnsideF4nB_d 2 := by
  have h : u33Data.D u33Data.jb = u33D u33GenPG ((2 : Fin 14) : ℕ) := by
    rw [show u33Data.jb = 2 from rfl]; rfl
  rw [h]
  exact congrArg (u33D u33GenPG) (by decide)

theorem burnsideF4nB_mem_A
    {g : U33G} (hg : g ∈ u33Data.A) (hgT : g ∉ u33Data.T) :
    ∃ i j : ℕ, i < 32 ∧ j < 32 ∧ g = burnsideF4nB_t i * burnsideF4nB_d 1 * burnsideF4nB_t j := by
  obtain ⟨k, hk, i₁, i₂, rfl⟩ := (u33Data.mem_A_iff g).1 hg
  rcases hk with rfl | rfl
  · exfalso
    apply hgT
    rw [u33Data.D_zero, mul_one]
    exact u33Data.T.mul_mem (u33Data.Tel_mem_T i₁) (u33Data.Tel_mem_T i₂)
  · exact ⟨i₁, i₂, i₁.2, i₂.2, by rw [burnsideF4nB_D_ja]; rfl⟩

theorem burnsideF4nB_mem_B
    {g : U33G} (hg : g ∈ u33Data.B) (hgT : g ∉ u33Data.T) :
    ∃ i j : ℕ, i < 32 ∧ j < 32 ∧ g = burnsideF4nB_t i * burnsideF4nB_d 2 * burnsideF4nB_t j := by
  obtain ⟨k, hk, i₁, i₂, rfl⟩ := (u33Data.mem_B_iff g).1 hg
  rcases hk with rfl | rfl
  · exfalso
    apply hgT
    rw [u33Data.D_zero, mul_one]
    exact u33Data.T.mul_mem (u33Data.Tel_mem_T i₁) (u33Data.Tel_mem_T i₂)
  · exact ⟨i₁, i₂, i₁.2, i₂.2, by rw [burnsideF4nB_D_jb]; rfl⟩

theorem burnsideF4nB_relIndex_A :
    u33Data.T.relIndex u33Data.A = 3 := by
  have hd : burnsideF4nB_d 1 ∈ u33Data.A := burnsideF4nB_D_ja ▸ u33Data.D_ja
  have ht5 : burnsideF4nB_t 5 ∈ u33Data.A := u33Data.T_le_A (burnsideF4nB_t_mem (by norm_num))
  refine burnsideF4nB_relIndex_three hd (u33Data.A.mul_mem ht5 hd) (fun g hg => ?_)
    (burnsideF4nB_D_ja ▸ u33Data.D_ja_notMem_T) ?_ ?_
  · by_cases hgT : g ∈ u33Data.T
    · exact Or.inl hgT
    right
    obtain ⟨i, j, hi, hj, rfl⟩ := burnsideF4nB_mem_A hg hgT
    obtain ⟨hn, hc⟩ := burnsideF4nB_cosA_check i hi
    set n := (burnsideF4nB_cosA.getD i (0, 0)).2
    rcases hc with ⟨-, hc⟩ | ⟨-, hc⟩
    · left
      have e : burnsideF4nB_t i * burnsideF4nB_d 1 = burnsideF4nB_d 1 * burnsideF4nB_t n :=
        burnsideF4nB_R_eq (burnsideF4nB_R_mul (burnsideF4nB_R_t hi) (burnsideF4nB_R_d (by norm_num)))
          (burnsideF4nB_R_mul (burnsideF4nB_R_d (by norm_num)) (burnsideF4nB_R_t hn)) hc
      rw [e, show (burnsideF4nB_d 1)⁻¹ * (burnsideF4nB_d 1 * burnsideF4nB_t n * burnsideF4nB_t j) =
        burnsideF4nB_t n * burnsideF4nB_t j by group]
      exact u33Data.T.mul_mem (burnsideF4nB_t_mem hn) (burnsideF4nB_t_mem hj)
    · right
      have e : burnsideF4nB_t i * burnsideF4nB_d 1 =
          burnsideF4nB_t 5 * burnsideF4nB_d 1 * burnsideF4nB_t n :=
        burnsideF4nB_R_eq (burnsideF4nB_R_mul (burnsideF4nB_R_t hi) (burnsideF4nB_R_d (by norm_num)))
          (burnsideF4nB_R_mul (burnsideF4nB_R_mul (burnsideF4nB_R_t (by norm_num))
            (burnsideF4nB_R_d (by norm_num))) (burnsideF4nB_R_t hn)) hc
      rw [e, show (burnsideF4nB_t 5 * burnsideF4nB_d 1)⁻¹ *
          (burnsideF4nB_t 5 * burnsideF4nB_d 1 * burnsideF4nB_t n * burnsideF4nB_t j) =
        burnsideF4nB_t n * burnsideF4nB_t j by group]
      exact u33Data.T.mul_mem (burnsideF4nB_t_mem hn) (burnsideF4nB_t_mem hj)
  · exact burnsideF4nB_not_mem_T (burnsideF4nB_R_mul (burnsideF4nB_R_t (by norm_num))
      (burnsideF4nB_R_d (by norm_num))) fun i hi => (burnsideF4nB_sepA_check i hi).1
  · exact burnsideF4nB_not_mem_T (burnsideF4nB_R_mul (burnsideF4nB_R_dinv (by norm_num))
      (burnsideF4nB_R_mul (burnsideF4nB_R_t (by norm_num)) (burnsideF4nB_R_d (by norm_num))))
      fun i hi => (burnsideF4nB_sepA_check i hi).2

theorem burnsideF4nB_relIndex_B :
    u33Data.T.relIndex u33Data.B = 3 := by
  have hd : burnsideF4nB_d 2 ∈ u33Data.B := burnsideF4nB_D_jb ▸ u33Data.D_jb
  have ht1 : burnsideF4nB_t 1 ∈ u33Data.B := u33Data.T_le_B (burnsideF4nB_t_mem (by norm_num))
  refine burnsideF4nB_relIndex_three hd (u33Data.B.mul_mem ht1 hd) (fun g hg => ?_)
    (burnsideF4nB_D_jb ▸ u33Data.D_jb_notMem_T) ?_ ?_
  · by_cases hgT : g ∈ u33Data.T
    · exact Or.inl hgT
    right
    obtain ⟨i, j, hi, hj, rfl⟩ := burnsideF4nB_mem_B hg hgT
    obtain ⟨hn, hc⟩ := burnsideF4nB_cosB_check i hi
    set n := (burnsideF4nB_cosB.getD i (0, 0)).2
    rcases hc with ⟨-, hc⟩ | ⟨-, hc⟩
    · left
      have e : burnsideF4nB_t i * burnsideF4nB_d 2 = burnsideF4nB_d 2 * burnsideF4nB_t n :=
        burnsideF4nB_R_eq (burnsideF4nB_R_mul (burnsideF4nB_R_t hi) (burnsideF4nB_R_d (by norm_num)))
          (burnsideF4nB_R_mul (burnsideF4nB_R_d (by norm_num)) (burnsideF4nB_R_t hn)) hc
      rw [e, show (burnsideF4nB_d 2)⁻¹ * (burnsideF4nB_d 2 * burnsideF4nB_t n * burnsideF4nB_t j) =
        burnsideF4nB_t n * burnsideF4nB_t j by group]
      exact u33Data.T.mul_mem (burnsideF4nB_t_mem hn) (burnsideF4nB_t_mem hj)
    · right
      have e : burnsideF4nB_t i * burnsideF4nB_d 2 =
          burnsideF4nB_t 1 * burnsideF4nB_d 2 * burnsideF4nB_t n :=
        burnsideF4nB_R_eq (burnsideF4nB_R_mul (burnsideF4nB_R_t hi) (burnsideF4nB_R_d (by norm_num)))
          (burnsideF4nB_R_mul (burnsideF4nB_R_mul (burnsideF4nB_R_t (by norm_num))
            (burnsideF4nB_R_d (by norm_num))) (burnsideF4nB_R_t hn)) hc
      rw [e, show (burnsideF4nB_t 1 * burnsideF4nB_d 2)⁻¹ *
          (burnsideF4nB_t 1 * burnsideF4nB_d 2 * burnsideF4nB_t n * burnsideF4nB_t j) =
        burnsideF4nB_t n * burnsideF4nB_t j by group]
      exact u33Data.T.mul_mem (burnsideF4nB_t_mem hn) (burnsideF4nB_t_mem hj)
  · exact burnsideF4nB_not_mem_T (burnsideF4nB_R_mul (burnsideF4nB_R_t (by norm_num))
      (burnsideF4nB_R_d (by norm_num))) fun i hi => (burnsideF4nB_sepB_check i hi).1
  · exact burnsideF4nB_not_mem_T (burnsideF4nB_R_mul (burnsideF4nB_R_dinv (by norm_num))
      (burnsideF4nB_R_mul (burnsideF4nB_R_t (by norm_num)) (burnsideF4nB_R_d (by norm_num))))
      fun i hi => (burnsideF4nB_sepB_check i hi).2

@[expose] def burnsideF4nB_invCoset (b₀ : U33G) :
    Set U33G :=
  {e | e * e = 1 ∧ b₀⁻¹ * e ∈ u33Data.T}

theorem burnsideF4nB_invCoset_d1 :
    burnsideF4nB_invCoset (burnsideF4nB_d 1) =
      (fun k : ℕ => burnsideF4nB_d 1 * burnsideF4nB_t k) '' {5, 18, 29, 30} := by
  ext β
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨k, hk, hke⟩ := burnsideF4nB_mem_T h2
    have hβ : β = burnsideF4nB_d 1 * burnsideF4nB_t k := by rw [hke]; group
    refine ⟨k, ?_, hβ.symm⟩
    rw [hβ] at h1
    have := (burnsideF4nB_K4 hk).1 h1
    simpa using this
  · rintro ⟨k, hk, rfl⟩
    have hk' : k = 5 ∨ k = 18 ∨ k = 29 ∨ k = 30 := by simpa using hk
    have hk32 : k < 32 := by omega
    refine ⟨(burnsideF4nB_K4 hk32).2 hk', ?_⟩
    rw [show (burnsideF4nB_d 1)⁻¹ * (burnsideF4nB_d 1 * burnsideF4nB_t k) = burnsideF4nB_t k by
      group]
    exact burnsideF4nB_t_mem hk32

theorem burnsideF4nB_invCoset_conj
    {i j : ℕ} (hi : i < 32) (hj : j < 32) :
    burnsideF4nB_invCoset (burnsideF4nB_t i * burnsideF4nB_d 1 * burnsideF4nB_t j) =
      (fun β => burnsideF4nB_t i * β * (burnsideF4nB_t i)⁻¹) ''
        burnsideF4nB_invCoset (burnsideF4nB_d 1) := by
  have hti := burnsideF4nB_t_mem hi
  have htj := burnsideF4nB_t_mem hj
  ext e
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(burnsideF4nB_t i)⁻¹ * e * burnsideF4nB_t i, ⟨?_, ?_⟩, by group⟩
    · rw [show (burnsideF4nB_t i)⁻¹ * e * burnsideF4nB_t i * ((burnsideF4nB_t i)⁻¹ * e *
          burnsideF4nB_t i) = (burnsideF4nB_t i)⁻¹ * (e * e) * burnsideF4nB_t i by group, h1]
      group
    · have := u33Data.T.mul_mem (u33Data.T.mul_mem htj h2) hti
      rwa [show burnsideF4nB_t j * ((burnsideF4nB_t i * burnsideF4nB_d 1 * burnsideF4nB_t j)⁻¹ * e) *
          burnsideF4nB_t i = (burnsideF4nB_d 1)⁻¹ * ((burnsideF4nB_t i)⁻¹ * e * burnsideF4nB_t i) by
        group] at this
  · rintro ⟨β, ⟨h1, h2⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [show burnsideF4nB_t i * β * (burnsideF4nB_t i)⁻¹ * (burnsideF4nB_t i * β *
          (burnsideF4nB_t i)⁻¹) = burnsideF4nB_t i * (β * β) * (burnsideF4nB_t i)⁻¹ by group, h1]
      group
    · have := u33Data.T.mul_mem (u33Data.T.mul_mem (u33Data.T.inv_mem htj) h2) (u33Data.T.inv_mem hti)
      rwa [show (burnsideF4nB_t j)⁻¹ * ((burnsideF4nB_d 1)⁻¹ * β) * (burnsideF4nB_t i)⁻¹ =
          (burnsideF4nB_t i * burnsideF4nB_d 1 * burnsideF4nB_t j)⁻¹ *
            (burnsideF4nB_t i * β * (burnsideF4nB_t i)⁻¹) by group] at this

theorem burnsideF4nB_ncard_inv
    {b₀ : U33G} (hb : b₀ ∈ u33Data.A) (hbT : b₀ ∉ u33Data.T) :
    (burnsideF4nB_invCoset b₀).ncard = 4 := by
  obtain ⟨i, j, hi, hj, rfl⟩ := burnsideF4nB_mem_A hb hbT
  have hinj : Set.InjOn (fun k : ℕ => burnsideF4nB_d 1 * burnsideF4nB_t k) {5, 18, 29, 30} := by
    intro k hk k' hk' h
    have hk32 : k < 32 := by simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk; omega
    have hk'32 : k' < 32 := by simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk'; omega
    have h' : burnsideF4nB_t k = burnsideF4nB_t k' := mul_left_cancel h
    have := u33_inj (a₁ := ⟨k, hk32⟩) (a₂ := ⟨k', hk'32⟩) h'
    exact congrArg Fin.val this
  rw [burnsideF4nB_invCoset_conj hi hj, Set.ncard_image_of_injective _ (fun x y h => by
    simpa using h), burnsideF4nB_invCoset_d1, hinj.ncard_image,
    show ({5, 18, 29, 30} : Set ℕ) = (({5, 18, 29, 30} : Finset ℕ) : Set ℕ) by simp,
    Set.ncard_coe_finset]
  rfl

theorem burnsideF4nB_t_mem_Z
    {n : ℕ} (hn : n ∈ [0, 9, 26, 6]) :
    burnsideF4nB_t n ∈ burnsideF4nB_Z := by
  obtain ⟨-, h26, h6, h0⟩ := burnsideF4nB_pow
  have h9 : burnsideF4nB_t 9 ∈ burnsideF4nB_Z := Subgroup.mem_zpowers _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl
  · rw [h0]; exact burnsideF4nB_Z.one_mem
  · exact h9
  · rw [h26]; exact burnsideF4nB_Z.mul_mem h9 h9
  · rw [h6, h26]; exact burnsideF4nB_Z.mul_mem h9 (burnsideF4nB_Z.mul_mem h9 h9)

theorem burnsideF4nB_trans_inv
    {b₀ : U33G} (hb : b₀ ∈ u33Data.A) (hbT : b₀ ∉ u33Data.T)
    {e e' : U33G} (he : e ∈ burnsideF4nB_invCoset b₀) (he' : e' ∈ burnsideF4nB_invCoset b₀) :
    ∃ d ∈ burnsideF4nB_Z, d * e * d⁻¹ = e' := by
  obtain ⟨i, j, hi, hj, rfl⟩ := burnsideF4nB_mem_A hb hbT
  rw [burnsideF4nB_invCoset_conj hi hj, burnsideF4nB_invCoset_d1] at he he'
  obtain ⟨_, ⟨k, hk, rfl⟩, rfl⟩ := he
  obtain ⟨_, ⟨k', hk', rfl⟩, rfl⟩ := he'
  have hkl : k ∈ [5, 18, 29, 30] := by simpa using hk
  have hkl' : k' ∈ [5, 18, 29, 30] := by simpa using hk'
  have hk32 : k < 32 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hkl; omega
  have hk'32 : k' < 32 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hkl'; omega
  obtain ⟨n, hn, hnc⟩ := burnsideF4nB_trans_check k hkl k' hkl'
  have hn32 : n < 32 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hn; omega
  have hcomm : burnsideF4nB_t n * (burnsideF4nB_d 1 * burnsideF4nB_t k) =
      burnsideF4nB_d 1 * burnsideF4nB_t k' * burnsideF4nB_t n :=
    burnsideF4nB_R_eq (burnsideF4nB_R_mul (burnsideF4nB_R_t hn32)
      (burnsideF4nB_R_mul (burnsideF4nB_R_d (by norm_num)) (burnsideF4nB_R_t hk32)))
      (burnsideF4nB_R_mul (burnsideF4nB_R_mul (burnsideF4nB_R_d (by norm_num))
        (burnsideF4nB_R_t hk'32)) (burnsideF4nB_R_t hn32)) hnc
  have hZ := burnsideF4nB_t_mem_Z hn
  have hc : burnsideF4nB_t i * burnsideF4nB_t n = burnsideF4nB_t n * burnsideF4nB_t i :=
    burnsideF4nB_Z_central hZ (u33Data.T_le_B (burnsideF4nB_t_mem hi))
  refine ⟨burnsideF4nB_t n, hZ, ?_⟩
  calc burnsideF4nB_t n * (burnsideF4nB_t i * (burnsideF4nB_d 1 * burnsideF4nB_t k) *
        (burnsideF4nB_t i)⁻¹) * (burnsideF4nB_t n)⁻¹
      = (burnsideF4nB_t n * burnsideF4nB_t i) * (burnsideF4nB_d 1 * burnsideF4nB_t k) *
          (burnsideF4nB_t n * burnsideF4nB_t i)⁻¹ := by group
    _ = burnsideF4nB_t i * (burnsideF4nB_t n * (burnsideF4nB_d 1 * burnsideF4nB_t k)) *
          (burnsideF4nB_t n)⁻¹ * (burnsideF4nB_t i)⁻¹ := by rw [← hc]; group
    _ = burnsideF4nB_t i * (burnsideF4nB_d 1 * burnsideF4nB_t k') * (burnsideF4nB_t i)⁻¹ := by
          rw [hcomm]; group

end CFSG.ASVolI
