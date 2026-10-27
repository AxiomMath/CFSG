module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3AutL3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC15TCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase9B

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

private theorem s1611e3_nine_isElemAbelian2_of_le {A B : Subgroup (MulAut W)}
    (hA : IsElemAbelian2 A) (hBA : B ≤ A) : IsElemAbelian2 B :=
  ⟨fun a ha b hb => hA.1 a (hBA ha) b (hBA hb), fun a ha => hA.2 a (hBA ha)⟩

private theorem s1611e3_nine_abs_map_conj_map_conj (A : Subgroup (MulAut W))
    (x y : MulAut W) :
    (A.map (MulAut.conj x).toMonoidHom).map (MulAut.conj y).toMonoidHom =
      A.map (MulAut.conj (y * x)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1

private theorem s1611e3_nine_abs_map_conj_one (A : Subgroup (MulAut W)) :
    A.map (MulAut.conj (1 : MulAut W)).toMonoidHom = A := by
  ext z
  simp [Subgroup.mem_map, MulAut.conj_apply]

private def s1611e3_nine_eqSub {W : Type*} [Group W] (f g : MulAut W) : Subgroup W where
  carrier := {v | f v = g v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, map_mul, ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [MulEquiv.map_inv, MulEquiv.map_inv, ha]

private theorem s1611e3_nine_eq_on_sup {A B : Subgroup W} {f g : MulAut W}
    (hA : ∀ a ∈ A, f a = g a) (hB : ∀ b ∈ B, f b = g b) :
    ∀ v ∈ A ⊔ B, f v = g v :=
  fun v hv => (sup_le hA hB : A ⊔ B ≤ s1611e3_nine_eqSub f g) hv

private theorem s1611e3_nine_aut_eq_of_eq_on_sup {A B : Subgroup W} (hsup : A ⊔ B = ⊤)
    {f g : MulAut W} (hA : ∀ a ∈ A, f a = g a) (hB : ∀ b ∈ B, f b = g b) :
    f = g :=
  MulEquiv.ext fun v => s1611e3_nine_eq_on_sup hA hB v (by rw [hsup]; trivial)

private theorem s1611e3_nine_map_commSub_eq {L : Subgroup (MulAut W)} {x : MulAut W}
    (hx : x ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    (commSub ⊤ L).map x.toMonoidHom = commSub ⊤ L := by
  have hx' : L.map (MulAut.conj x).toMonoidHom = L := by
    simpa using Subgroup.mem_normalizer_iff_map_conj_eq.mp hx
  rw [← s16c167_commSub_top_conj x L, hx']

theorem s1611e3_nine_abs_normalizes_conj {X L : Subgroup (MulAut W)} {g : MulAut W}
    (hg : s16n9b_case9Two X L g) :
    ∀ x ∈ X, x ∈ Subgroup.normalizer (L : Set (MulAut W)) →
      x ∈ Subgroup.normalizer
        ((L.map (MulAut.conj g).toMonoidHom : Subgroup (MulAut W)) : Set (MulAut W)) := by
  intro x hxX hxN
  have hxN' : L.map (MulAut.conj x).toMonoidHom = L := by
    simpa using Subgroup.mem_normalizer_iff_map_conj_eq.mp hxN
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  show (L.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x).toMonoidHom =
    L.map (MulAut.conj g).toMonoidHom
  have hconj := hg.conj (x * g) (X.mul_mem hxX hg.mem)
  rw [← s1611e3_nine_abs_map_conj_map_conj L g x] at hconj
  rcases hconj with h | h
  · exfalso
    have hxN'' : L.map (MulAut.conj x⁻¹).toMonoidHom = L := by
      have h2 := congrArg (fun A : Subgroup (MulAut W) =>
        A.map (MulAut.conj x⁻¹).toMonoidHom) hxN'
      rw [s1611e3_nine_abs_map_conj_map_conj, inv_mul_cancel,
        s1611e3_nine_abs_map_conj_one] at h2
      exact h2.symm
    have h3 : L.map (MulAut.conj g).toMonoidHom = L := by
      have h2 := congrArg (fun A : Subgroup (MulAut W) =>
        A.map (MulAut.conj x⁻¹).toMonoidHom) h
      rwa [s1611e3_nine_abs_map_conj_map_conj, inv_mul_cancel,
        s1611e3_nine_abs_map_conj_one, hxN''] at h2
    exact hg.ne h3
  · exact h

private theorem s1611e3_nine_card_le_two_mul_of_cover {F : Type*} [Group F] [Finite F]
    {H : Subgroup F} {t : F} (h : ∀ x : F, x ∈ H ∨ x * t ∈ H) :
    Nat.card F ≤ 2 * Nat.card H := by
  have hsub : (Set.univ : Set F) ⊆ (H : Set F) ∪ ((fun x => x * t⁻¹) '' (H : Set F)) := by
    intro x _
    rcases h x with hx | hx
    · exact Or.inl hx
    · exact Or.inr ⟨x * t, hx, by group⟩
  have h1 : (Set.univ : Set F).ncard ≤
      ((H : Set F) ∪ ((fun x => x * t⁻¹) '' (H : Set F))).ncard := Set.ncard_le_ncard hsub
  have h2 : ((H : Set F) ∪ ((fun x => x * t⁻¹) '' (H : Set F))).ncard ≤
      (H : Set F).ncard + ((fun x => x * t⁻¹) '' (H : Set F)).ncard := Set.ncard_union_le _ _
  have h3 : ((fun x => x * t⁻¹) '' (H : Set F)).ncard = (H : Set F).ncard :=
    Set.ncard_image_of_injective _ fun a b hab => mul_right_cancel hab
  have h4 : (H : Set F).ncard = Nat.card H := by
    simpa using (Nat.card_coe_set_eq (H : Set F)).symm
  have h5 : (Set.univ : Set F).ncard = Nat.card F := Set.ncard_univ F
  rw [h5] at h1
  rw [h3, h4] at h2
  omega

private theorem s1611e3_nine_exists_notMem_union {F : Type*} [Group F] {H K : Subgroup F}
    (hH : H ≠ ⊤) (hK : K ≠ ⊤) : ∃ x : F, x ∉ H ∧ x ∉ K := by
  by_contra h
  have h' : ∀ x : F, x ∈ H ∨ x ∈ K := by
    intro x
    by_contra hx
    push Not at hx
    exact h ⟨x, hx.1, hx.2⟩
  obtain ⟨x, hxH⟩ : ∃ x, x ∉ H := by
    by_contra hc
    push Not at hc
    exact hH (eq_top_iff.mpr fun x _ => hc x)
  obtain ⟨y, hyK⟩ : ∃ y, y ∉ K := by
    by_contra hc
    push Not at hc
    exact hK (eq_top_iff.mpr fun y _ => hc y)
  have hxK : x ∈ K := (h' x).resolve_left hxH
  have hyH : y ∈ H := (h' y).resolve_right hyK
  rcases h' (x * y) with hh | hh
  · exact hxH (by simpa [mul_assoc] using H.mul_mem hh (H.inv_mem hyH))
  · exact hyK (by simpa [mul_assoc] using K.mul_mem (K.inv_mem hxK) hh)

private theorem s1611e3_nine_abs_card_le_mul_four {L : Subgroup (MulAut W)} (hL3 : IsL3 ↥L 1)
    {E₀ : Subgroup (MulAut W)} (hab : IsElemAbelian2 E₀)
    (hE₀N : E₀ ≤ Subgroup.normalizer (L : Set (MulAut W))) :
    Nat.card ↥E₀ ≤
      Nat.card ↥(E₀ ⊓ Subgroup.centralizer (L : Set (MulAut W))) * 4 := by
  classical
  let f : E₀ →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hE₀N)
  have hker : f.ker = (E₀ ⊓ Subgroup.centralizer (L : Set (MulAut W))).subgroupOf E₀ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx
      refine ⟨x.2, ?_⟩
      have hxN : (Subgroup.inclusion hE₀N x : ↥(Subgroup.normalizer (L : Set (MulAut W)))) ∈
          MonoidHom.ker L.normalizerMonoidHom := hx
      rwa [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hxN
    · rintro ⟨-, hx⟩
      show L.normalizerMonoidHom (Subgroup.inclusion hE₀N x) = 1
      rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
      exact hx
  have hrange : Nat.card f.range ≤ 4 := by
    have hOpen : CFSG.Open.IsElemAbelian 2 f.range := by
      refine ⟨IsMulCommutative.of_comm (fun a b => ?_), fun y hy => ?_⟩
      · apply Subtype.ext
        obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
        obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 b.2
        have h1 : ((a : f.range) : MulAut ↥L) = f x := hx.symm
        have h2 : ((b : f.range) : MulAut ↥L) = f z := hz.symm
        have hxz : x * z = z * x := by
          apply Subtype.ext
          rw [Subgroup.coe_mul, Subgroup.coe_mul]
          exact hab.1 x x.2 z z.2
        rw [Subgroup.coe_mul, Subgroup.coe_mul, h1, h2, ← map_mul, ← map_mul, hxz]
      · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hy
        rw [← hx, ← map_pow]
        have hx2 : x ^ 2 = 1 := by
          apply Subtype.ext
          rw [Subgroup.coe_pow, Subgroup.coe_one]
          exact hab.2 x x.2
        rw [hx2, map_one]
    exact s1611e3_card_le_four_mulAut_l3 hL3 hOpen
  calc Nat.card ↥E₀ = Nat.card f.ker * Nat.card f.range :=
        (Subgroup.card_ker_mul_card_range f).symm
    _ = Nat.card ↥((E₀ ⊓ Subgroup.centralizer (L : Set (MulAut W))).subgroupOf E₀) *
          Nat.card f.range := by rw [hker]
    _ = Nat.card ↥(E₀ ⊓ Subgroup.centralizer (L : Set (MulAut W))) * Nat.card f.range := by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
    _ ≤ Nat.card ↥(E₀ ⊓ Subgroup.centralizer (L : Set (MulAut W))) * 4 :=
          Nat.mul_le_mul_left _ hrange

theorem s1611e3_nine_abs_card_normalizer_le_sixteen {X L : Subgroup (MulAut W)}
    {g : MulAut W} (hg : s16n9b_case9Two X L g) (hL3 : IsL3 ↥L 1)
    (hcard4 : ∀ E : Subgroup (MulAut W), E ≤ X → IsElemAbelian2 E →
      E ≤ Subgroup.normalizer (L : Set (MulAut W)) →
      E ≤ Subgroup.normalizer ((L.map (MulAut.conj g).toMonoidHom : Subgroup (MulAut W)) :
        Set (MulAut W)) →
      (∀ x ∈ E, ∀ a ∈ L, x * a = a * x) → Nat.card ↥E ≤ 4)
    {E₀ : Subgroup (MulAut W)} (hE₀X : E₀ ≤ X) (hab : IsElemAbelian2 E₀)
    (hE₀N : E₀ ≤ Subgroup.normalizer (L : Set (MulAut W))) :
    Nat.card ↥E₀ ≤ 16 := by
  have hNL' := s1611e3_nine_abs_normalizes_conj hg
  have hK : Nat.card ↥(E₀ ⊓ Subgroup.centralizer (L : Set (MulAut W))) ≤ 4 := by
    refine hcard4 _ (inf_le_left.trans hE₀X)
      (s1611e3_nine_isElemAbelian2_of_le hab inf_le_left) (inf_le_left.trans hE₀N) ?_ ?_
    · intro x hx
      exact hNL' x (hE₀X hx.1) (hE₀N hx.1)
    · intro x hx a ha
      exact (Subgroup.mem_centralizer_iff.mp hx.2 a ha).symm
  have h := s1611e3_nine_abs_card_le_mul_four hL3 hab hE₀N
  omega

theorem s1611e3_nine_abs_card_le_sixteen {X L : Subgroup (MulAut W)} {g : MulAut W}
    (hg : s16n9b_case9Two X L g) (hL3 : IsL3 ↥L 1)
    (hcard4 : ∀ E : Subgroup (MulAut W), E ≤ X → IsElemAbelian2 E →
      E ≤ Subgroup.normalizer (L : Set (MulAut W)) →
      E ≤ Subgroup.normalizer ((L.map (MulAut.conj g).toMonoidHom : Subgroup (MulAut W)) :
        Set (MulAut W)) →
      (∀ x ∈ E, ∀ a ∈ L, x * a = a * x) → Nat.card ↥E ≤ 4)
    (hfaith : ∀ x ∈ X, x * x = 1 → (∀ a ∈ L, x * a = a * x) →
      (∀ a ∈ L.map (MulAut.conj g).toMonoidHom, x * a = a * x) → x = 1)
    {E : Subgroup (MulAut W)} (hE : E ≤ X) (hab : IsElemAbelian2 E) :
    Nat.card ↥E ≤ 16 := by
  classical
  have hNL' := s1611e3_nine_abs_normalizes_conj hg
  set E₀ : Subgroup (MulAut W) := E ⊓ Subgroup.normalizer (L : Set (MulAut W)) with hE₀def
  have hE₀X : E₀ ≤ X := inf_le_left.trans hE
  have hab₀ : IsElemAbelian2 E₀ := s1611e3_nine_isElemAbelian2_of_le hab inf_le_left
  have hE₀N : E₀ ≤ Subgroup.normalizer (L : Set (MulAut W)) := inf_le_right
  by_cases hEN : E ≤ Subgroup.normalizer (L : Set (MulAut W))
  · have hE₀eq : E₀ = E := by rw [hE₀def]; exact inf_eq_left.mpr hEN
    have h16 := s1611e3_nine_abs_card_normalizer_le_sixteen hg hL3 hcard4 hE₀X hab₀ hE₀N
    rwa [hE₀eq] at h16
  · rw [SetLike.le_def] at hEN
    push Not at hEN
    obtain ⟨t, htE, htN⟩ := hEN
    have htL : L.map (MulAut.conj t).toMonoidHom =
        L.map (MulAut.conj g).toMonoidHom := by
      rcases hg.conj t (hE htE) with h | h
      · exact absurd (Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by simpa using h)) htN
      · exact h
    have hKbot : E₀ ⊓ Subgroup.centralizer (L : Set (MulAut W)) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      have hxE : x ∈ E := (hE₀def ▸ hx.1).1
      have hx2 : x * x = 1 := hab.2 x hxE
      have hxL : ∀ a ∈ L, x * a = a * x := fun a ha =>
        (Subgroup.mem_centralizer_iff.mp hx.2 a ha).symm
      have hxt : x * t = t * x := hab.1 x hxE t htE
      have hxL' : ∀ a ∈ L.map (MulAut.conj g).toMonoidHom, x * a = a * x := by
        intro a ha
        rw [← htL] at ha
        obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.1 ha
        have hxl : x * l = l * x := hxL l hl
        have hxt' : x * t⁻¹ = t⁻¹ * x := by
          have h2 : x * t⁻¹ * x⁻¹ = t⁻¹ := by
            have h1 : x * t * x⁻¹ = t := by rw [hxt]; group
            calc x * t⁻¹ * x⁻¹ = (x * t * x⁻¹)⁻¹ := by group
              _ = t⁻¹ := by rw [h1]
          exact mul_inv_eq_iff_eq_mul.mp h2
        calc x * (t * l * t⁻¹) = (x * t) * l * t⁻¹ := by group
          _ = (t * x) * l * t⁻¹ := by rw [hxt]
          _ = t * (x * l) * t⁻¹ := by group
          _ = t * (l * x) * t⁻¹ := by rw [hxl]
          _ = t * l * (x * t⁻¹) := by group
          _ = t * l * (t⁻¹ * x) := by rw [hxt']
          _ = (t * l * t⁻¹) * x := by group
      exact hfaith x (hE hxE) hx2 hxL hxL'
    have h4₀ : Nat.card ↥E₀ ≤ 4 := by
      have h := s1611e3_nine_abs_card_le_mul_four hL3 hab₀ hE₀N
      rw [hKbot, Subgroup.card_bot, one_mul] at h
      exact h
    have hcover : ∀ x : ↥E, x ∈ E₀.subgroupOf E ∨ x * ⟨t, htE⟩ ∈ E₀.subgroupOf E := by
      intro x
      by_cases hx₀ : (x : MulAut W) ∈ E₀
      · exact Or.inl hx₀
      · refine Or.inr ?_
        have hxN : (x : MulAut W) ∉ Subgroup.normalizer (L : Set (MulAut W)) := fun hxN' =>
          hx₀ ⟨x.2, hxN'⟩
        have hxL : L.map (MulAut.conj (x : MulAut W)).toMonoidHom =
            L.map (MulAut.conj g).toMonoidHom := by
          rcases hg.conj (x : MulAut W) (hE x.2) with h | h
          · exact absurd (Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by simpa using h)) hxN
          · exact h
        have hxt : (L.map (MulAut.conj t).toMonoidHom).map
            (MulAut.conj (x : MulAut W)).toMonoidHom = L := by
          rw [htL, ← hxL, s1611e3_nine_abs_map_conj_map_conj L (x : MulAut W) (x : MulAut W),
            show (x : MulAut W) * (x : MulAut W) = 1 from hab.2 x x.2,
            s1611e3_nine_abs_map_conj_one]
        have hnorm : (x : MulAut W) * t ∈ Subgroup.normalizer (L : Set (MulAut W)) := by
          rw [Subgroup.mem_normalizer_iff_map_conj_eq]
          show L.map (MulAut.conj ((x : MulAut W) * t)).toMonoidHom = L
          rw [← s1611e3_nine_abs_map_conj_map_conj L t (x : MulAut W)]
          exact hxt
        exact ⟨E.mul_mem x.2 htE, hnorm⟩
    have hcard_sub : Nat.card ↥(E₀.subgroupOf E) = Nat.card ↥E₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have h2 := s1611e3_nine_card_le_two_mul_of_cover hcover
    rw [hcard_sub] at h2
    omega

theorem s1611e3_nine_abs_five_le_rkIdx_of_swap {X L : Subgroup (MulAut W)} {g : MulAut W}
    (hg : s16n9b_case9Two X L g) (h9 : rk ↥(commSub ⊤ L) = 9)
    {E : Subgroup (MulAut W)} (hE : E ≤ X) (hab : IsElemAbelian2 E) {t : MulAut W}
    (htE : t ∈ E)
    (htL : L.map (MulAut.conj t).toMonoidHom = L.map (MulAut.conj g).toMonoidHom) :
    5 ≤ rkIdx (fixV E) := by
  have hdisj : commSub ⊤ L ⊓ (commSub ⊤ L).map t.toMonoidHom = ⊥ := by
    have h1 : (commSub ⊤ L).map t.toMonoidHom = (commSub ⊤ L).map g.toMonoidHom := by
      rw [← s16c167_commSub_top_conj t L, ← s16c167_commSub_top_conj g L]
      exact congrArg (fun A => commSub ⊤ A) htL
    rw [h1]
    exact hg.inf
  have hswap : rk ↥(commSub ⊤ L) ≤ rkIdx (fixV (Subgroup.zpowers t)) :=
    s16c15t_rk_le_rkIdx_of_swap hdisj rfl
  have hmono : fixV E ≤ fixV (Subgroup.zpowers t) := by
    intro v hv
    rw [mem_fixV] at hv ⊢
    intro x hx
    exact hv x (Subgroup.zpowers_le.mpr htE hx)
  have hanti := rkIdx_anti hmono
  omega

theorem s1611e3_nine_abs_five_le_rkIdx_of_stab {X L : Subgroup (MulAut W)} {g : MulAut W}
    (hg : s16n9b_case9Two X L g) (hW : ∀ w : W, w ^ 2 = 1)
    (hcard4 : ∀ E : Subgroup (MulAut W), E ≤ X → IsElemAbelian2 E →
      E ≤ Subgroup.normalizer (L : Set (MulAut W)) →
      E ≤ Subgroup.normalizer ((L.map (MulAut.conj g).toMonoidHom : Subgroup (MulAut W)) :
        Set (MulAut W)) →
      (∀ x ∈ E, ∀ a ∈ L, x * a = a * x) → Nat.card ↥E ≤ 4)
    (hcard4sym : ∀ E : Subgroup (MulAut W), E ≤ X → IsElemAbelian2 E →
      E ≤ Subgroup.normalizer (L : Set (MulAut W)) →
      (∀ x ∈ E, ∀ a ∈ L.map (MulAut.conj g).toMonoidHom, x * a = a * x) →
      Nat.card ↥E ≤ 4)
    (hloc0 : ∀ t ∈ X, t * t = 1 → (commSub ⊤ L).map t.toMonoidHom = commSub ⊤ L →
      commSub ⊤ L ≤ fixV (Subgroup.zpowers t) ∨
        3 ≤ E3.mQuot (commSub ⊤ L) (commSub ⊤ L ⊓ fixV (Subgroup.zpowers t)))
    (hloc1 : ∀ t ∈ X, t * t = 1 →
      ((commSub ⊤ L).map g.toMonoidHom).map t.toMonoidHom = (commSub ⊤ L).map g.toMonoidHom →
      (commSub ⊤ L).map g.toMonoidHom ≤ fixV (Subgroup.zpowers t) ∨
        3 ≤ E3.mQuot ((commSub ⊤ L).map g.toMonoidHom)
              (((commSub ⊤ L).map g.toMonoidHom) ⊓ fixV (Subgroup.zpowers t)))
    {E : Subgroup (MulAut W)} (hE : E ≤ X) (hab : IsElemAbelian2 E)
    (hstab : ∀ x ∈ E, x ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (h3 : 3 ≤ rk ↥E) :
    5 ≤ rkIdx (fixV E) := by
  classical
  have hNL' := s1611e3_nine_abs_normalizes_conj hg
  set W₀ : Subgroup W := commSub ⊤ L with hW₀def
  set W₁ : Subgroup W := (commSub ⊤ L).map g.toMonoidHom with hW₁def
  have hdisj : W₀ ⊓ W₁ = ⊥ := hg.inf
  have hsup : W₀ ⊔ W₁ = ⊤ := hg.sup
  set E₁ : Subgroup (MulAut W) := E ⊓ centSub W₀ with hE₁def
  set E₂ : Subgroup (MulAut W) := E ⊓ centSub W₁ with hE₂def
  have hE₁X : E₁ ≤ X := inf_le_left.trans hE
  have hE₂X : E₂ ≤ X := inf_le_left.trans hE
  have hab₁ : IsElemAbelian2 E₁ := s1611e3_nine_isElemAbelian2_of_le hab inf_le_left
  have hab₂ : IsElemAbelian2 E₂ := s1611e3_nine_isElemAbelian2_of_le hab inf_le_left
  have hE₁N : E₁ ≤ Subgroup.normalizer (L : Set (MulAut W)) := fun x hx =>
    hstab x (hE₁def ▸ hx).1
  have hE₂N : E₂ ≤ Subgroup.normalizer (L : Set (MulAut W)) := fun x hx =>
    hstab x (hE₂def ▸ hx).1
  have hcent₁ : ∀ x ∈ E₁, ∀ a ∈ L, x * a = a * x := by
    intro x hx a ha
    have hxE : x ∈ E := (hE₁def ▸ hx).1
    have hxc : x ∈ centSub W₀ := (hE₁def ▸ hx).2
    have hxfix : ∀ w ∈ W₀, x w = w := fun w hw => mem_centSub.1 hxc w hw
    have hxN : x ∈ Subgroup.normalizer (L : Set (MulAut W)) := hE₁N hx
    have hxW₀ : W₀.map x.toMonoidHom = W₀ := s1611e3_nine_map_commSub_eq hxN
    have hxW₁ : W₁.map x.toMonoidHom = W₁ := by
      rw [hW₁def, ← s16c167_commSub_top_conj g L]
      exact s1611e3_nine_map_commSub_eq (hNL' x (hE₁X hx) hxN)
    have haW₀ : W₀.map a.toMonoidHom = W₀ :=
      s1611e3_nine_map_commSub_eq (Subgroup.le_normalizer ha)
    have hafix : ∀ w ∈ W₁, a w = w := fun w hw => hg.fixA a ha w hw
    have hx2 : x * x = 1 := hab.2 x hxE
    have hxinv_eq : (x⁻¹ : MulAut W) = x := inv_eq_of_mul_eq_one_right hx2
    have hconj : x * a * x⁻¹ = a := by
      apply s1611e3_nine_aut_eq_of_eq_on_sup hsup
      · intro w hw
        have haW₀' : a w ∈ W₀ := by
          have := Subgroup.mem_map_of_mem a.toMonoidHom hw
          rwa [haW₀] at this
        show (x * a * x⁻¹) w = a w
        rw [MulAut.mul_apply, MulAut.mul_apply, hxinv_eq, hxfix w hw]
        exact hxfix (a w) haW₀'
      · intro w hw
        have hxw : x w ∈ W₁ := by
          have := Subgroup.mem_map_of_mem x.toMonoidHom hw
          rwa [hxW₁] at this
        have hafix' : a (x w) = x w := hafix _ hxw
        show (x * a * x⁻¹) w = a w
        rw [MulAut.mul_apply, MulAut.mul_apply, hxinv_eq, hafix', ← MulAut.mul_apply, hx2,
          MulAut.one_apply]
        exact (hafix w hw).symm
    calc x * a = x * a * x⁻¹ * x := by group
      _ = a * x := by rw [hconj]
  have hcent₂ : ∀ x ∈ E₂, ∀ a ∈ L.map (MulAut.conj g : MulAut W →* MulAut W), x * a = a * x := by
    intro x hx a ha
    have hxE : x ∈ E := (hE₂def ▸ hx).1
    have hxc : x ∈ centSub W₁ := (hE₂def ▸ hx).2
    have hxfix : ∀ w ∈ W₁, x w = w := fun w hw => mem_centSub.1 hxc w hw
    have hxN : x ∈ Subgroup.normalizer (L : Set (MulAut W)) := hE₂N hx
    have hxW₀ : W₀.map x.toMonoidHom = W₀ := s1611e3_nine_map_commSub_eq hxN
    have hxW₁ : W₁.map x.toMonoidHom = W₁ := by
      rw [hW₁def, ← s16c167_commSub_top_conj g L]
      exact s1611e3_nine_map_commSub_eq (hNL' x (hE₂X hx) hxN)
    have haW₁ : W₁.map a.toMonoidHom = W₁ := by
      rw [hW₁def, ← s16c167_commSub_top_conj g L]
      exact s1611e3_nine_map_commSub_eq (Subgroup.le_normalizer ha)
    have hafix : ∀ w ∈ W₀, a w = w := fun w hw => hg.fixB a ha w hw
    have hx2 : x * x = 1 := hab.2 x hxE
    have hxinv_eq : (x⁻¹ : MulAut W) = x := inv_eq_of_mul_eq_one_right hx2
    have hconj : x * a * x⁻¹ = a := by
      apply s1611e3_nine_aut_eq_of_eq_on_sup hsup
      · intro w hw
        have hxw : x w ∈ W₀ := by
          have := Subgroup.mem_map_of_mem x.toMonoidHom hw
          rwa [hxW₀] at this
        have hafix' : a (x w) = x w := hafix _ hxw
        show (x * a * x⁻¹) w = a w
        rw [MulAut.mul_apply, MulAut.mul_apply, hxinv_eq, hafix', ← MulAut.mul_apply, hx2,
          MulAut.one_apply]
        exact (hafix w hw).symm
      · intro w hw
        have haW₁' : a w ∈ W₁ := by
          have := Subgroup.mem_map_of_mem a.toMonoidHom hw
          rwa [haW₁] at this
        show (x * a * x⁻¹) w = a w
        rw [MulAut.mul_apply, MulAut.mul_apply, hxinv_eq, hxfix w hw]
        exact hxfix (a w) haW₁'
    calc x * a = x * a * x⁻¹ * x := by group
      _ = a * x := by rw [hconj]
  have h4₁ : Nat.card ↥E₁ ≤ 4 :=
    hcard4 E₁ hE₁X hab₁ hE₁N (fun x hx => hNL' x (hE₁X hx) (hE₁N hx)) hcent₁
  have h4₂ : Nat.card ↥E₂ ≤ 4 := hcard4sym E₂ hE₂X hab₂ hE₂N hcent₂
  have hcardE : 8 ≤ Nat.card ↥E := by
    have hP : IsPGroup 2 ↥E := isPGroup_two_of_sq_eq_one fun x => by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hab.2 (x : MulAut W) x.2
    have hpow := card_eq_two_pow_of_isPGroup hP
    have hle : 2 ^ 3 ≤ 2 ^ rk ↥E := Nat.pow_le_pow_right (by norm_num) h3
    omega
  have hproper₁ : E₁.subgroupOf E ≠ ⊤ := by
    intro h
    have hcard : Nat.card ↥(E₁.subgroupOf E) = Nat.card ↥E₁ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have := congrArg (fun S : Subgroup ↥E => Nat.card ↥S) h
    rw [hcard, Subgroup.card_top] at this
    omega
  have hproper₂ : E₂.subgroupOf E ≠ ⊤ := by
    intro h
    have hcard : Nat.card ↥(E₂.subgroupOf E) = Nat.card ↥E₂ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have := congrArg (fun S : Subgroup ↥E => Nat.card ↥S) h
    rw [hcard, Subgroup.card_top] at this
    omega
  obtain ⟨x, hx₁, hx₂⟩ := s1611e3_nine_exists_notMem_union hproper₁ hproper₂
  have hxE : (x : MulAut W) ∈ E := x.2
  have hx2 : (x : MulAut W) * (x : MulAut W) = 1 := hab.2 x x.2
  have hxX : (x : MulAut W) ∈ X := hE hxE
  have hxN : (x : MulAut W) ∈ Subgroup.normalizer (L : Set (MulAut W)) := hstab x x.2
  have hstab₀ : W₀.map (x : MulAut W).toMonoidHom = W₀ :=
    s1611e3_nine_map_commSub_eq hxN
  have hstab₁ : W₁.map (x : MulAut W).toMonoidHom = W₁ := by
    rw [hW₁def, ← s16c167_commSub_top_conj g L]
    exact s1611e3_nine_map_commSub_eq (hNL' (x : MulAut W) hxX hxN)
  have hnot₀ : ¬ W₀ ≤ fixV (Subgroup.zpowers (x : MulAut W)) := by
    intro hle
    apply hx₁
    rw [Subgroup.mem_subgroupOf]
    exact ⟨x.2, mem_centSub.2 fun w hw => mem_fixV.1 (hle hw) (x : MulAut W)
      (Subgroup.mem_zpowers _)⟩
  have hnot₁ : ¬ W₁ ≤ fixV (Subgroup.zpowers (x : MulAut W)) := by
    intro hle
    apply hx₂
    rw [Subgroup.mem_subgroupOf]
    exact ⟨x.2, mem_centSub.2 fun w hw => mem_fixV.1 (hle hw) (x : MulAut W)
      (Subgroup.mem_zpowers _)⟩
  have h3₀ : 3 ≤ E3.mQuot W₀ (W₀ ⊓ fixV (Subgroup.zpowers (x : MulAut W))) := by
    rcases hloc0 (x : MulAut W) hxX hx2 hstab₀ with h | h
    · exact absurd h hnot₀
    · exact h
  have h3₁ : 3 ≤ E3.mQuot W₁ (W₁ ⊓ fixV (Subgroup.zpowers (x : MulAut W))) := by
    rcases hloc1 (x : MulAut W) hxX hx2 hstab₁ with h | h
    · exact absurd h hnot₁
    · exact h
  have hsplit := s16c167_rkIdx_fixV_split hW (x : MulAut W) hdisj hsup hstab₀ hstab₁
  have hmono : fixV E ≤ fixV (Subgroup.zpowers (x : MulAut W)) := by
    intro v hv
    rw [mem_fixV] at hv ⊢
    intro y hy
    exact hv y (Subgroup.zpowers_le.mpr hxE hy)
  have hanti := rkIdx_anti hmono
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
