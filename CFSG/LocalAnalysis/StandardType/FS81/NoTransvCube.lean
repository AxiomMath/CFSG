module

public import CFSG.LocalAnalysis.StandardType.FS81.NoTransvP1

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly
open scoped Matrix

variable {G : Type} [Group G]

theorem mul_pow_three_of_comm {x y z : G} (hyx : y * x = x * y * z) (hzx : Commute z x)
    (hzy : Commute z y) (hz3 : z ^ 3 = 1) : (x * y) ^ 3 = x ^ 3 * y ^ 3 := by
  have h2 : y * y * x = x * y * y * (z * z) := by
    calc y * y * x = y * (y * x) := by group
      _ = y * (x * y * z) := by rw [hyx]
      _ = (y * x) * y * z := by group
      _ = x * y * z * y * z := by rw [hyx]
      _ = x * y * (z * y) * z := by group
      _ = x * y * (y * z) * z := by rw [hzy.eq]
      _ = x * y * y * (z * z) := by group
  have h3 : z * z * y = y * (z * z) := ((hzy.mul_left hzy).eq)
  rw [pow_three', pow_three', pow_three']
  calc x * y * (x * y) * (x * y) = x * (y * x) * y * x * y := by group
    _ = x * (x * y * z) * y * x * y := by rw [hyx]
    _ = x * x * y * (z * y) * x * y := by group
    _ = x * x * y * (y * z) * x * y := by rw [hzy.eq]
    _ = x * x * y * y * (z * x) * y := by group
    _ = x * x * y * y * (x * z) * y := by rw [hzx.eq]
    _ = x * x * (y * y * x) * (z * y) := by group
    _ = x * x * (x * y * y * (z * z)) * (y * z) := by rw [h2, hzy.eq]
    _ = x * x * x * y * y * (z * z * y) * z := by group
    _ = x * x * x * y * y * (y * (z * z)) * z := by rw [h3]
    _ = x * x * x * (y * y * y) * (z * z * z) := by group
    _ = x * x * x * (y * y * y) := by rw [← pow_three' z, hz3, mul_one]

namespace Basis3

variable {k : ℕ}

theorem vec_neg' (B : Basis3 G k) (e : Coords k) : B.vec (-e) = (B.vec e)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← B.vec_add, add_neg_cancel, B.vec_zero]

theorem vec_smul' (B : Basis3 G k) (c : ZMod 3) (e : Coords k) :
    B.vec (c • e) = B.vec e ^ c.val := by
  rw [← B.vec_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]

theorem acts_vec' (B : Basis3 G k) {g : G} (hg : g ∈ Subgroup.normalizer (B.span : Set G))
    {M : Matrix (Fin k) (Fin k) (ZMod 3)} (h : B.Acts g M) (e : Coords k) :
    g * B.vec e * g⁻¹ = B.vec (M *ᵥ e) := by
  set φ := B.span.normalizerMonoidHom ⟨g, hg⟩ with hφ
  have hφg : ∀ y : ↥B.span, ((φ y : ↥B.span) : G) = g * y * g⁻¹ := fun y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
  have hM : B.matOf φ = M := B.matOf_eq_of_acts hφg h
  have h1 := B.coords_apply_vec φ e
  rw [hM] at h1
  calc g * B.vec e * g⁻¹ = ((φ ⟨B.vec e, B.vec_mem_span e⟩ : ↥B.span) : G) :=
        (hφg ⟨B.vec e, B.vec_mem_span e⟩).symm
    _ = B.vec (B.coords (φ ⟨B.vec e, B.vec_mem_span e⟩)) := (B.vec_coords _).symm
    _ = B.vec (M *ᵥ e) := by rw [h1]

theorem acts_spMat_one (B : Basis3 G k) {g : G} {s : Fin k → ZMod 3}
    (h : B.Acts g (spMat 1 s)) (j : Fin k) : g * B.b j * g⁻¹ = B.b j ^ (s j).val := by
  rw [h j, ← B.vec_smul_single]
  congr 1
  funext i
  by_cases hij : i = j
  · subst hij; simp [spMat_apply]
  · simp [spMat_apply, hij]

end Basis3

@[expose] def DiagSigns {n : ℕ} (B : Basis3 G (n + 1)) (E : Subgroup G) : Prop :=
  ∀ k l : Fin (n + 1), k ≠ 0 → l ≠ 0 → l ≠ k → ∃ d ∈ Subgroup.normalizer (E : Set G),
    ∃ s : Fin (n + 1) → ZMod 3, IsSign s ∧ s 0 = 1 ∧ B.Acts d (spMat 1 s) ∧ s l ≠ s k

@[expose] def CoordTrans {n : ℕ} (B : Basis3 G (n + 1)) (b₀ : G) (E : Subgroup G) : Prop :=
  ∃ i₀ : Fin (n + 1), i₀ ≠ 0 ∧ ∀ k : Fin (n + 1), k ≠ 0 →
    ∃ g ∈ Subgroup.normalizer (E : Set G), g * b₀ * g⁻¹ = b₀ ∧
      ∃ c : Coords (n + 1), g * B.b i₀ * g⁻¹ = B.vec c ∧ c k ≠ 0

namespace TransvP1

variable [Finite G] {b₀ : G} {K E P₁ : Subgroup G}

theorem exists_lift (h : TransvSetup b₀ K E) (hP : TransvP1 b₀ K E P₁) {d : G}
    (hd : d ∈ Subgroup.normalizer (E : Set G)) :
    ∃ d' ∈ Subgroup.normalizer (E : Set G), d' ∈ Subgroup.normalizer (P₁ : Set G) ∧
      ∀ y ∈ E, d' * y * d'⁻¹ = d * y * d⁻¹ := by
  obtain ⟨c, hc, hcd⟩ := h.exists_centralizer_mul_mem_normalizer hP.le hP.pgroup hP.card hP.surj'
    hd
  refine ⟨c * d, Subgroup.mul_mem _ (Subgroup.centralizer_le_normalizer _ hc) hd, hcd,
    fun y hy => ?_⟩
  have hdy : d * y * d⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hd y).mp hy
  rw [show c * d * y * (c * d)⁻¹ = c * (d * y * d⁻¹) * c⁻¹ by group,
    ← Subgroup.mem_centralizer_iff.mp hc _ hdy, mul_inv_cancel_right]

theorem cube_mul (h : TransvSetup b₀ K E) (hP : TransvP1 b₀ K E P₁) {n : ℕ}
    (B : Basis3 G (n + 1)) (hB : Adapted B b₀ K E) (hsc : SignChanges B.b b₀ E) {x y : G}
    (hx : x ∈ P₁) (hy : y ∈ P₁) : (x * y) ^ 3 = x ^ 3 * y ^ 3 := by
  have hz : y⁻¹ * x⁻¹ * y * x ∈ E ⊓ K := by
    have := hP.comm_mem_A h B hB hsc (P₁.inv_mem hy) (P₁.inv_mem hx)
    rwa [inv_inv, inv_inv] at this
  have hcomm : ∀ {u : G}, u ∈ P₁ → Commute (y⁻¹ * x⁻¹ * y * x) u := fun {u} hu =>
    (mul_inv_eq_iff_eq_mul.mp ((hP.le hu).2.1 _ hz)).symm
  exact mul_pow_three_of_comm (z := y⁻¹ * x⁻¹ * y * x) (by group) (hcomm hx) (hcomm hy)
    (h.elem.2 _ hz.1)

theorem cube_eq_of_tb_eq (h : TransvSetup b₀ K E) (hP : TransvP1 b₀ K E P₁) {n : ℕ}
    (B : Basis3 G (n + 1)) (hB : Adapted B b₀ K E) (hsc : SignChanges B.b b₀ E) {x y : G}
    (hx : x ∈ P₁) (hy : y ∈ P₁) (hxy : tb b₀ x = tb b₀ y) : x ^ 3 = y ^ 3 := by
  have he : x⁻¹ * y ∈ E := hP.mem_E h (P₁.mul_mem (P₁.inv_mem hx) hy) (by
    rw [tb_mul (hP.le (P₁.inv_mem hx)) (hP.le hy), tb_inv (hP.le hx), hxy, inv_mul_cancel])
  have := hP.cube_mul h B hB hsc hx (hP.E_le he)
  rw [mul_inv_cancel_left, h.elem.2 _ he, mul_one] at this
  exact this.symm

theorem cube_eq_single (h : TransvSetup b₀ K E) (hP : TransvP1 b₀ K E P₁) {n : ℕ}
    (B : Basis3 G (n + 1)) (hB : Adapted B b₀ K E) (hsc : SignChanges B.b b₀ E)
    (hdiag : DiagSigns B E) {k : Fin (n + 1)} (hk : k ≠ 0) {x : G} (hx : x ∈ P₁)
    (hxb : tb b₀ x = B.b k) : ∃ m : ZMod 3, x ^ 3 = B.vec (Pi.single k m) := by
  have hbE : ∀ i, B.b i ∈ E := fun i => hB.1 ▸ B.b_mem_span i
  have hxA := hP.cube_mem_A h B hB hsc hx
  have hxS : x ^ 3 ∈ B.span := hB.1 ▸ hxA.1
  set c := B.coords ⟨x ^ 3, hxS⟩ with hcdef
  have hc : B.vec c = x ^ 3 := B.vec_coords _
  have hc0 : c 0 = 0 :=
    B.coords_zero_of_mem hB.2.1 h.ord hB.2.2 (hB.1 ▸ h.disj) ⟨x ^ 3, hxS⟩ hxA.2
  refine ⟨c k, ?_⟩
  rw [← hc]
  congr 1
  funext l
  by_cases hlk : l = k
  · rw [hlk, Pi.single_eq_same]
  rw [Pi.single_apply, if_neg hlk]
  by_cases hl0 : l = 0
  · rw [hl0, hc0]
  obtain ⟨d, hdN, s, hs, hs0, hds, hslk⟩ := hdiag k l hk hl0 hlk
  obtain ⟨d', hd'N, hd'P, hd'⟩ := hP.exists_lift h hdN
  have hacts : B.Acts d' (spMat 1 s) := fun j => by rw [hd' _ (hbE j)]; exact hds j
  have hb : ∀ j, d' * B.b j * d'⁻¹ = B.b j ^ (s j).val := B.acts_spMat_one hacts
  have hd'b : d' * b₀ * d'⁻¹ = b₀ := by
    have := hb 0
    rwa [hs0, ZMod.val_one, pow_one, hB.2.1] at this
  have hdxP : d' * x * d'⁻¹ ∈ P₁ := (Subgroup.mem_normalizer_iff.mp hd'P x).mp hx
  have hcube : (d' * x * d'⁻¹) ^ 3 = B.vec (fun i => s i * c i) := by
    rw [conj_pow, ← hc, B.acts_vec' (by rw [hB.1]; exact hd'N) hacts, spMat_mulVec]
    rfl
  have htb : tb b₀ (d' * x * d'⁻¹) = B.b k ^ (s k).val := by rw [tb_conj hd'b, hxb, hb]
  have hcl : s l * c l = s k * c l := by
    rcases hs k with hsk | hsk
    · have h1 : (d' * x * d'⁻¹) ^ 3 = x ^ 3 := hP.cube_eq_of_tb_eq h B hB hsc hdxP hx (by
        rw [htb, hsk, ZMod.val_one, pow_one, hxb])
      have := congrFun (B.vec_injective (hcube.symm.trans (h1.trans hc.symm))) l
      rw [hsk, one_mul]
      exact this
    · have h1 : (d' * x * d'⁻¹) ^ 3 = x⁻¹ ^ 3 := hP.cube_eq_of_tb_eq h B hB hsc hdxP
        (P₁.inv_mem hx) (by
          rw [htb, tb_inv (hP.le hx), hxb]
          have h3 : B.b k ^ 3 = 1 := by rw [← B.ord k]; exact pow_orderOf_eq_one _
          have hv : (s k).val = 2 := by rw [hsk]; rfl
          rw [hv]
          exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h3))
      have h2 : x⁻¹ ^ 3 = B.vec (-c) := by rw [inv_pow, ← hc, B.vec_neg']
      have := congrFun (B.vec_injective (hcube.symm.trans (h1.trans h2))) l
      rw [Pi.neg_apply] at this
      rw [hsk]
      have key : ∀ a b : ZMod 3, b * a = -a → b * a = -1 * a := by decide
      exact key _ _ this
  have hne : s l - s k ≠ 0 := sub_ne_zero.mpr hslk
  have : (s l - s k) * c l = 0 := by rw [sub_mul, hcl, sub_self]
  exact (mul_eq_zero.mp this).resolve_left hne

theorem cube_eq_vec (h : TransvSetup b₀ K E) (hP : TransvP1 b₀ K E P₁) {n : ℕ}
    (B : Basis3 G (n + 1)) (hB : Adapted B b₀ K E) (hsc : SignChanges B.b b₀ E)
    {xk : Fin (n + 1) → G} (hxkP : ∀ k, k ≠ 0 → xk k ∈ P₁)
    (hxkb : ∀ k, k ≠ 0 → tb b₀ (xk k) = B.b k) {μ : Fin (n + 1) → ZMod 3}
    (hμ : ∀ k, k ≠ 0 → xk k ^ 3 = B.vec (Pi.single k (μ k))) :
    ∀ y ∈ P₁, ∀ e : Coords (n + 1), tb b₀ y = B.vec e → y ^ 3 = B.vec (fun m => μ m * e m) := by
  have hcoords : ∀ {y : G}, y ∈ P₁ → ∃ e : Coords (n + 1), tb b₀ y = B.vec e := fun hy =>
    let ⟨e, he⟩ := B.exists_vec_eq (hB.1 ▸ (tb_mem (hP.le hy)).1)
    ⟨e, he.symm⟩
  refine hP.forall_of_gen h B hB (p := fun y => ∀ e : Coords (n + 1), tb b₀ y = B.vec e →
      y ^ 3 = B.vec (fun m => μ m * e m)) ?_ ?_ ?_ ?_
  · intro y y' hy hy' h1 h2 e he
    obtain ⟨e₁, he₁⟩ := hcoords hy
    obtain ⟨e₂, he₂⟩ := hcoords hy'
    have hsum : e = e₁ + e₂ := B.vec_injective (by
      rw [← he, tb_mul (hP.le hy) (hP.le hy'), he₁, he₂, B.vec_add])
    rw [hP.cube_mul h B hB hsc hy hy', h1 e₁ he₁, h2 e₂ he₂, ← B.vec_add, hsum]
    congr 1
    funext m
    simp [mul_add]
  · intro y hy h1 e he
    have h2 : tb b₀ y = B.vec (-e) := by
      rw [B.vec_neg', ← he, tb_inv (hP.le hy), inv_inv]
    rw [inv_pow, h1 _ h2, ← B.vec_neg']
    congr 1
    funext m
    simp
  · intro y hy e he
    have hy1 : tb b₀ y = 1 := by
      have := hP.le (hP.E_le hy)
      exact (h.beta_eq_one_iff ⟨y, this⟩).mpr
        (Subgroup.mem_centralizer_iff.mpr fun z hz => h.comm hz hy) |> congrArg Subtype.val
    have he0 : e = 0 := B.vec_injective (by rw [← he, hy1, B.vec_zero])
    have hz : (fun m => μ m * e m) = 0 := funext fun m => by simp [he0]
    rw [h.elem.2 y hy, hz, B.vec_zero]
  · intro k hk
    refine ⟨xk k, hxkP k hk, hxkb k hk, fun e he => ?_⟩
    have he' : e = Pi.single k 1 := B.vec_injective (by rw [← he, hxkb k hk, B.vec_single])
    rw [hμ k hk, he']
    congr 1
    funext m
    by_cases hm : m = k
    · subst hm; simp
    · simp [hm]

theorem exists_cube_eq_pow (h : TransvSetup b₀ K E) (hP : TransvP1 b₀ K E P₁) {n : ℕ}
    (B : Basis3 G (n + 1)) (hB : Adapted B b₀ K E) (hsc : SignChanges B.b b₀ E)
    (hdiag : DiagSigns B E) (htr : CoordTrans B b₀ E) :
    ∃ μ : ℕ, ∀ y ∈ P₁, y ^ 3 = tb b₀ y ^ μ := by
  have hbE : ∀ i, B.b i ∈ E := fun i => hB.1 ▸ B.b_mem_span i
  have hbA : ∀ i : Fin (n + 1), i ≠ 0 → B.b i ∈ E ⊓ K := fun i hi => ⟨hbE i, hB.2.2 i hi⟩
  have hpre : ∀ k : Fin (n + 1), k ≠ 0 → ∃ x ∈ P₁, tb b₀ x = B.b k := fun k hk =>
    hP.surj _ (hbA k hk)
  choose! xk hxkP hxkb using hpre
  have hsingle : ∀ k : Fin (n + 1), k ≠ 0 → ∃ m : ZMod 3, xk k ^ 3 = B.vec (Pi.single k m) :=
    fun k hk => hP.cube_eq_single h B hB hsc hdiag hk (hxkP k hk) (hxkb k hk)
  choose! μ hμ using hsingle
  have hvec := hP.cube_eq_vec h B hB hsc hxkP hxkb hμ
  obtain ⟨i₀, hi₀, hmove⟩ := htr
  have hall : ∀ k : Fin (n + 1), k ≠ 0 → μ k = μ i₀ := by
    intro k hk
    obtain ⟨g, hgN, hgb, c, hgc, hck⟩ := hmove k hk
    obtain ⟨g', hg'N, hg'P, hg'⟩ := hP.exists_lift h hgN
    have hg'b : g' * b₀ * g'⁻¹ = b₀ := by rw [hg' _ h.b0_mem, hgb]
    have hyP : g' * xk i₀ * g'⁻¹ ∈ P₁ := (Subgroup.mem_normalizer_iff.mp hg'P _).mp (hxkP i₀ hi₀)
    have htb : tb b₀ (g' * xk i₀ * g'⁻¹) = B.vec c := by
      rw [tb_conj hg'b, hxkb i₀ hi₀, hg' _ (hbE i₀), hgc]
    have h1 := hvec _ hyP c htb
    have h2 : (g' * xk i₀ * g'⁻¹) ^ 3 = B.vec (μ i₀ • c) := by
      rw [conj_pow, hμ i₀ hi₀, show (Pi.single i₀ (μ i₀) : Coords (n + 1)) =
        μ i₀ • Pi.single i₀ 1 by rw [← Pi.single_smul]; simp, B.vec_smul', B.vec_single, ← conj_pow, hg' _ (hbE i₀), hgc,
        ← B.vec_smul']
    have := congrFun (B.vec_injective (h1.symm.trans h2)) k
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact mul_right_cancel₀ hck this
  refine ⟨(μ i₀).val, fun y hy => ?_⟩
  obtain ⟨e, he⟩ := B.exists_vec_eq (hB.1 ▸ (tb_mem (hP.le hy)).1)
  have he0 : e 0 = 0 := by
    have := B.coords_zero_of_mem hB.2.1 h.ord hB.2.2 (hB.1 ▸ h.disj)
      ⟨tb b₀ y, hB.1 ▸ (tb_mem (hP.le hy)).1⟩ (tb_mem (hP.le hy)).2
    rwa [show B.coords ⟨tb b₀ y, _⟩ = e from B.vec_injective (by rw [B.vec_coords, he])] at this
  rw [hvec y hy e he.symm, ← he, ← B.vec_smul']
  congr 1
  funext m
  by_cases hm : m = 0
  · subst hm; simp [he0]
  · simp [hall m hm]

end TransvP1

end CFSG.StandardType.FrameRoute.FS81

end
