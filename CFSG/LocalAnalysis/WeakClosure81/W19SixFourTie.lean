module

public import CFSG.LocalAnalysis.WeakClosure81.W19ModE
public import CFSG.LocalAnalysis.WeakClosure81.W19SixFourCard

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup
open scoped Pointwise commutatorElement

theorem isElemAbelian_of_card_two {H : Type*} [Group H] {B : Subgroup H}
    (hB : Nat.card B = 2) : IsElemAbelian 2 B := by
  have hsq : ∀ x ∈ B, x ^ 2 = 1 := by
    intro x hx
    have hd : orderOf (⟨x, hx⟩ : ↥B) ∣ 2 := by
      have h0 := orderOf_dvd_natCard (⟨x, hx⟩ : ↥B)
      rwa [hB] at h0
    simpa using congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.1 hd)
  refine ⟨⟨⟨fun a b => ?_⟩⟩, hsq⟩
  apply Subtype.ext
  have ha := hsq a a.2
  have hb := hsq b b.2
  have hab := hsq (a * b) (B.mul_mem a.2 b.2)
  rw [pow_two] at ha hb hab
  have h1 : ((a : H) * b)⁻¹ = (a : H) * b := inv_eq_of_mul_eq_one_right hab
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb] at h1
  exact h1.symm

theorem eq_bot_or_eq_of_card_two {H : Type*} [Group H] [Finite H] {B B' : Subgroup H}
    (hB : Nat.card B = 2) (hle : B' ≤ B) : B' = ⊥ ∨ B' = B := by
  have hd : Nat.card B' ∣ 2 := hB ▸ Subgroup.card_dvd_of_le hle
  rcases (Nat.dvd_prime Nat.prime_two).1 hd with h1 | h2
  · exact Or.inl (Subgroup.eq_bot_of_card_eq B' h1)
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge hle (by rw [h2, hB]))

theorem mem_normalizer_of_cj_eq {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    {B : Subgroup (LGL 2 W)} {x : LGL 2 W} (h : cj x B = B) :
    x ∈ normalizer (B : Set (LGL 2 W)) := by
  have h4 : ∀ y, y ∈ B ↔ x⁻¹ * y * x ∈ B := fun y => by rw [← mem_cj, h]
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have h5 := h4 (x * y * x⁻¹)
  have e : x⁻¹ * (x * y * x⁻¹) * x = y := by group
  rw [e] at h5
  exact h5.symm

theorem commSpace_commSub_eq_bot_of_card_two {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    {B : Subgroup (LGL 2 W)} (hB : Nat.card B = 2) : commSpace B (commSub B) = ⊥ := by
  classical
  have hBne : B ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hB
    exact absurd hB (by norm_num)
  obtain ⟨⟨b, hbB⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hBne
  have hbb : b * b = 1 := by
    have hd : orderOf (⟨b, hbB⟩ : ↥B) ∣ 2 := by
      have h0 := orderOf_dvd_natCard (⟨b, hbB⟩ : ↥B)
      rwa [hB] at h0
    have h2 : (⟨b, hbB⟩ : ↥B) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 hd
    simpa [pow_two] using congrArg Subtype.val h2
  have huniq : ∀ x ∈ B, x = 1 ∨ x = b := by
    intro x hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · refine Or.inr ?_
      obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥B)).1 hB
      have e1 : (⟨x, hx⟩ : ↥B) = y := hy _ (fun h' => hx1 (congrArg Subtype.val h'))
      have e2 : (⟨b, hbB⟩ : ↥B) = y := hy _ hb1
      exact congrArg Subtype.val (e1.trans e2.symm)
  have h2 : ∀ x : W, x + x = 0 := fun x => by
    rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]
  have hfix : ∀ u ∈ commSub B, b u = u := by
    intro u hu
    refine Submodule.span_induction (p := fun u _ => b u = u) ?_ ?_ ?_ ?_ hu
    · rintro w ⟨a, ha, v, rfl⟩
      rcases huniq a ha with h1 | h1
      · rw [h1]
        simp
      · rw [h1]
        have hbbv : b (b v) = v := by
          have := congrArg (fun z : LGL 2 W => z v) hbb
          simpa using this
        have hx : (b v - v) + (b v - v) = 0 := h2 _
        have h6 : -(b v - v) = b v - v := neg_eq_of_add_eq_zero_left hx
        rw [map_sub, hbbv, ← h6]
        abel
    · exact map_zero b
    · intro x y _ _ hx hy
      rw [map_add, hx, hy]
    · intro c x _ hx
      rw [map_smul, hx]
  rw [eq_bot_iff, commSpace]
  refine Submodule.span_le.2 ?_
  rintro w ⟨k, hk, u, hu, rfl⟩
  rcases huniq k hk with h1 | h1
  · rw [h1]
    simp
  · rw [h1, hfix u hu]
    simp

section Group

variable {G : Type} [Group G] [Finite G]

theorem commutator_conjSubgroup {E : Subgroup G} {j : G} (hj : j ∈ normalizer (E : Set G))
    (B : Subgroup G) : ⁅E, conjSubgroup B j⁆ = conjSubgroup ⁅E, B⁆ j := by
  unfold conjSubgroup
  have hj' : j⁻¹ ∈ normalizer (E : Set G) := Subgroup.inv_mem _ hj
  have hE : E.map (MulAut.conj j⁻¹).toMonoidHom = E :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 hj'
  rw [Subgroup.map_commutator, hE]

theorem inf_centralizer_le_pCoreOf {J E : Subgroup G} (hJ : J ≤ normalizer (E : Set G))
    (hC : IsPGroup 2 ↥(J ⊓ centralizer (E : Set G))) :
    J ⊓ centralizer (E : Set G) ≤ pCoreOf 2 J := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ j ∈ J, ∀ h ∈ J ⊓ centralizer (E : Set G),
      j * h * j⁻¹ ∈ J ⊓ centralizer (E : Set G) := by
    intro j hj h hh
    refine Subgroup.mem_inf.2 ⟨J.mul_mem (J.mul_mem hj hh.1) (J.inv_mem hj), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have he' : j⁻¹ * e * j⁻¹⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.1 (hJ (J.inv_mem hj)) e).1 he
    have h1 := Subgroup.mem_centralizer_iff.1 hh.2 _ he'
    have h2 : e * (j * h * j⁻¹) = j * (j⁻¹ * e * j⁻¹⁻¹ * h) * j⁻¹ := by group
    have h3 : (j * h * j⁻¹) * e = j * (h * (j⁻¹ * e * j⁻¹⁻¹)) * j⁻¹ := by group
    rw [h2, h3, h1]
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ hC
  intro j hj
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key j hj h hh, fun hh => ?_⟩
  have := key j⁻¹ (J.inv_mem hj) _ hh
  simpa [mul_assoc] using this

end Group

variable {G : Type} [Group G] [Finite G]

structure TieData (J E A : Subgroup G) : Prop where
  elemAb : IsElemAbelian 2 E
  le_normalizer : J ≤ normalizer (E : Set G)
  isPGroup_cent : IsPGroup 2 ↥(J ⊓ centralizer (E : Set G))
  A_le : A ≤ J
  relIndex : (centralizer (E : Set G)).relIndex A = 2
  inf_pCore : A ⊓ pCoreOf 2 J ≤ centralizer (E : Set G)
  isPGroup_norm : IsPGroup 2 ↥(J ⊓ normalizer (A : Set G))
  ti : ∀ j ∈ J, ⁅E, A⁆ ⊓ ⁅E, conjSubgroup A j⁻¹⁆ ≠ ⊥ → j ∈ normalizer (A : Set G)

namespace TieData

variable {J E A : Subgroup G} (T : TieData J E A) (M : ModDataE J E)

include T

theorem card_img_A : Nat.card (M.img A) = 2 := by
  rw [M.card_img T.A_le]
  exact T.relIndex

theorem conjSubgroup_le {j : G} (hj : j ∈ J) : conjSubgroup A j⁻¹ ≤ J := by
  intro x hx
  rw [mem_conjSubgroup_iff] at hx
  have h1 : j * (j⁻¹ * x * j⁻¹⁻¹) * j⁻¹ ∈ J :=
    J.mul_mem (J.mul_mem hj (T.A_le hx)) (J.inv_mem hj)
  simpa [mul_assoc] using h1

theorem mem_orbit_iff {B : Subgroup (LGL 2 M.W)} :
    B ∈ {B | ∃ g ∈ M.img J, B = cj g (M.img A)} ↔
      ∃ j : ↥J, B = M.img (conjSubgroup A (j : G)⁻¹) := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨j, -, rfl⟩ := M.mem_img.1 hg
    exact ⟨j, M.img_conj T.A_le j⟩
  · rintro ⟨j, rfl⟩
    exact ⟨M.ρ j, M.mem_img.2 ⟨j, j.2, rfl⟩, (M.img_conj T.A_le j).symm⟩

theorem commSub_inf_eq_bot {j₁ j₂ : ↥J}
    (hne : M.img (conjSubgroup A (j₁ : G)⁻¹) ≠ M.img (conjSubgroup A (j₂ : G)⁻¹)) :
    commSub (M.img (conjSubgroup A (j₁ : G)⁻¹)) ⊓ commSub (M.img (conjSubgroup A (j₂ : G)⁻¹)) =
      ⊥ := by
  by_contra hcon
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 hcon
  obtain ⟨e, he, rfl⟩ := M.ι_surj w
  have he1 : e ≠ 1 := fun h => hw0 (by rw [h, M.ι_one])
  have h1 : e ∈ ⁅E, conjSubgroup A (j₁ : G)⁻¹⁆ :=
    (M.mem_commSub_img_iff (T.conjSubgroup_le j₁.2) he).1 hw.1
  have h2 : e ∈ ⁅E, conjSubgroup A (j₂ : G)⁻¹⁆ :=
    (M.mem_commSub_img_iff (T.conjSubgroup_le j₂.2) he).1 hw.2
  have hE₁ : (j₁ : G)⁻¹ ∈ normalizer (E : Set G) := T.le_normalizer (J.inv_mem j₁.2)
  have hE₂ : (j₂ : G)⁻¹ ∈ normalizer (E : Set G) := T.le_normalizer (J.inv_mem j₂.2)
  rw [commutator_conjSubgroup hE₁, mem_conjSubgroup_iff] at h1
  rw [commutator_conjSubgroup hE₂, mem_conjSubgroup_iff] at h2
  have hj : (j₂ : G)⁻¹ * (j₁ : G) ∈ J := J.mul_mem (J.inv_mem j₂.2) j₁.2
  have he' : (j₂ : G)⁻¹ * e * (j₂ : G) ≠ 1 := by
    intro h
    apply he1
    have h3 : (j₂ : G)⁻¹ * e * ((j₂ : G)⁻¹)⁻¹ = 1 := by simpa using h
    exact conj_eq_one_iff.1 h3
  have hmeet : ⁅E, A⁆ ⊓ ⁅E, conjSubgroup A ((j₂ : G)⁻¹ * (j₁ : G))⁻¹⁆ ≠ ⊥ := by
    intro hbot
    have hmem : (j₂ : G)⁻¹ * e * (j₂ : G) ∈
        ⁅E, A⁆ ⊓ ⁅E, conjSubgroup A ((j₂ : G)⁻¹ * (j₁ : G))⁻¹⁆ := by
      refine Subgroup.mem_inf.2 ⟨by simpa using h2, ?_⟩
      rw [commutator_conjSubgroup (T.le_normalizer (J.inv_mem hj)), mem_conjSubgroup_iff]
      have e2 : ((j₂ : G)⁻¹ * (j₁ : G))⁻¹ * ((j₂ : G)⁻¹ * e * (j₂ : G)) *
          ((j₂ : G)⁻¹ * (j₁ : G))⁻¹⁻¹ = (j₁ : G)⁻¹ * e * ((j₁ : G)⁻¹)⁻¹ := by group
      rw [e2]
      exact h1
    rw [hbot, Subgroup.mem_bot] at hmem
    exact he' hmem
  have hN := T.ti _ hj hmeet
  have hA : conjSubgroup A ((j₂ : G)⁻¹ * (j₁ : G)) = A := conjSubgroup_eq_iff_mem_normalizer.2 hN
  apply hne
  congr 1
  calc conjSubgroup A (j₁ : G)⁻¹
      = conjSubgroup (conjSubgroup A ((j₂ : G)⁻¹ * (j₁ : G))) (j₁ : G)⁻¹ := by rw [hA]
    _ = conjSubgroup A ((j₂ : G)⁻¹ * (j₁ : G) * (j₁ : G)⁻¹) := conjSubgroup_conjSubgroup _ _ _
    _ = conjSubgroup A (j₂ : G)⁻¹ := by rw [mul_inv_cancel_right]

theorem assumption131 :
    Assumption131 (M.img J) {B | ∃ g ∈ M.img J, B = cj g (M.img A)} commSub 1 := by
  classical
  set Γ : Set (Subgroup (LGL 2 M.W)) := {B | ∃ g ∈ M.img J, B = cj g (M.img A)} with hΓ
  have hcard : ∀ g : LGL 2 M.W, Nat.card (cj g (M.img A)) = 2 := fun g =>
    (card_cj (M.img A) g).trans (T.card_img_A M)
  have hle : ∀ B ∈ Γ, B ≤ M.img J := by
    rintro B ⟨g, hg, rfl⟩ x hx
    have hx : x ∈ cj g (M.img A) := hx
    rw [mem_cj] at hx
    have h1 : g⁻¹ * x * g ∈ M.img J := M.img_mono T.A_le hx
    have h2 : g * (g⁻¹ * x * g) * g⁻¹ ∈ M.img J :=
      (M.img J).mul_mem ((M.img J).mul_mem hg h1) ((M.img J).inv_mem hg)
    simpa [mul_assoc] using h2
  have hel : ∀ B ∈ Γ, IsElemAbelian 2 B := by
    rintro B ⟨g, hg, rfl⟩
    exact isElemAbelian_of_card_two (hcard g)
  have hinv : ∀ B ∈ Γ, ∀ g ∈ M.img J, cj g B ∈ Γ := by
    rintro B ⟨g', hg', rfl⟩ g hg
    exact ⟨g * g', (M.img J).mul_mem hg hg', (cj_mul g g' _).symm⟩
  have hne : ∀ B ∈ Γ, B ≠ ⊥ := by
    rintro B ⟨g, hg, rfl⟩ hbot
    have h2 := hcard g
    rw [hbot, Subgroup.card_bot] at h2
    exact absurd h2 (by norm_num)
  have hA₁inf : M.img A ⊓ pCoreOf 2 (M.img J) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxA, hxO⟩
    rw [← M.img_pCoreOf T.isPGroup_cent] at hxO
    obtain ⟨a, haA, rfl⟩ := M.mem_img.1 hxA
    obtain ⟨r, hrO, hra⟩ := M.mem_img.1 hxO
    have hc : M.ρ (a⁻¹ * r) = 1 := by rw [map_mul, map_inv, hra, inv_mul_cancel]
    have hcC : ((a⁻¹ * r : ↥J) : G) ∈ centralizer (E : Set G) := (M.ρ_eq_one_iff _).1 hc
    have hcO : ((a⁻¹ * r : ↥J) : G) ∈ pCoreOf 2 J :=
      inf_centralizer_le_pCoreOf T.le_normalizer T.isPGroup_cent ⟨(a⁻¹ * r).2, hcC⟩
    have haO : (a : G) ∈ pCoreOf 2 J := by
      have e : (a : G) = (r : G) * ((a⁻¹ * r : ↥J) : G)⁻¹ := by simp [mul_assoc]
      rw [e]
      exact Subgroup.mul_mem _ hrO (Subgroup.inv_mem _ hcO)
    have haC : (a : G) ∈ centralizer (E : Set G) := T.inf_pCore ⟨haA, haO⟩
    rw [(M.ρ_eq_one_iff a).2 haC]
    exact Subgroup.one_mem _
  have hinf : ∀ B ∈ Γ, B ⊓ pCoreOf 2 (M.img J) = ⊥ := by
    rintro B ⟨g, hg, rfl⟩
    rw [eq_bot_iff]
    rintro x ⟨hxB, hxO⟩
    have hxB : x ∈ cj g (M.img A) := hxB
    rw [mem_cj] at hxB
    have hn := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (M.img J) ((M.img J).inv_mem hg)
    have h1 : g⁻¹ * x * g⁻¹⁻¹ ∈ pCoreOf 2 (M.img J) :=
      (Subgroup.mem_normalizer_iff.1 hn x).1 hxO
    have h2 : g⁻¹ * x * g ∈ M.img A ⊓ pCoreOf 2 (M.img J) := ⟨hxB, by simpa using h1⟩
    rw [hA₁inf, Subgroup.mem_bot] at h2
    have h3 : x = 1 := by
      have h4 := congrArg (fun z => g * z * g⁻¹) h2
      simpa [mul_assoc] using h4
    rw [h3]
    exact Subgroup.one_mem _
  have hdisj : ∀ B ∈ Γ, ∀ B' ∈ Γ, B ≠ B' → commSub B ⊓ commSub B' = ⊥ := by
    intro B hB B' hB' hBB'
    obtain ⟨j₁, rfl⟩ := (T.mem_orbit_iff M).1 hB
    obtain ⟨j₂, rfl⟩ := (T.mem_orbit_iff M).1 hB'
    exact T.commSub_inf_eq_bot M hBB'
  have hnorm : ∀ B ∈ Γ, M.img J ⊓ normalizer (B : Set (LGL 2 M.W)) =
      stabilizerOf (M.img J) (commSub B) := by
    intro B hB
    ext x
    constructor
    · rintro ⟨hxG, hxN⟩
      refine ⟨hxG, ?_⟩
      have h1 : cj x B = B := cj_eq_of_mem_normalizer hxN
      have h2 := commSub_cj (A := B) x
      rw [h1] at h2
      exact h2.symm
    · rintro ⟨hxG, hxS⟩
      refine ⟨hxG, ?_⟩
      have hB' : cj x B ∈ Γ := hinv B hB x hxG
      have h2 : commSub (cj x B) = commSub B := by
        rw [commSub_cj]
        exact hxS
      by_contra hxN
      have hneq : B ≠ cj x B := fun h => hxN (mem_normalizer_of_cj_eq h.symm)
      have h3 := hdisj B hB (cj x B) hB' hneq
      rw [h2, inf_idem] at h3
      exact hne B hB ((commSub_eq_bot_iff B).1 h3)
  have hcond2 : ∀ B ∈ Γ, ∀ B' : Subgroup (LGL 2 M.W), B' ≤ B → mOf B B' ≤ 1 →
      commSpace B (fixSub B') ≤ commSub B := by
    rintro B ⟨g, hg, rfl⟩ B' hB' -
    rcases eq_bot_or_eq_of_card_two (hcard g) hB' with rfl | rfl
    · rw [fixSub_bot, commSpace_top_eq_commSub]
    · refine Submodule.span_le.2 ?_
      rintro w ⟨k, hk, u, hu, rfl⟩
      have h0 : k u = u := hu k hk
      simp [h0]
  exact
    { pos_i := Nat.one_pos
      le_G := hle
      isElemAb := hel
      invariant := hinv
      ne_bot := hne
      inf_pCore := hinf
      normalizer_eq := hnorm
      disjoint := hdisj
      cond2 := hcond2
      quadratic := fun B hB => by
        obtain ⟨g, hg, rfl⟩ := hB
        exact commSpace_commSub_eq_bot_of_card_two (hcard g)
      equivariant := fun B _ g _ => commSub_cj (A := B) g }

theorem isPGroup_inf_normalizer :
    IsPGroup 2 ↥(M.img J ⊓ normalizer ((M.img A : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W))) := by
  refine (M.isPGroup_img T.isPGroup_norm).to_le ?_
  rintro x ⟨hxG, hxN⟩
  obtain ⟨j, hjJ, rfl⟩ := M.mem_img.1 hxG
  have hcj : cj (M.ρ j) (M.img A) = M.img A := cj_eq_of_mem_normalizer hxN
  rw [M.img_conj T.A_le j] at hcj
  have hbot : commSub (M.img A) ≠ ⊥ := fun h =>
    (by
      have h0 : M.img A = ⊥ := (commSub_eq_bot_iff _).1 h
      have h1 := T.card_img_A M
      rw [h0, Subgroup.card_bot] at h1
      exact absurd h1 (by norm_num))
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 hbot
  obtain ⟨e, he, rfl⟩ := M.ι_surj w
  have he1 : e ≠ 1 := fun h => hw0 (by rw [h, M.ι_one])
  have h1 : e ∈ ⁅E, A⁆ := (M.mem_commSub_img_iff T.A_le he).1 hw
  have h2 : e ∈ ⁅E, conjSubgroup A (j : G)⁻¹⁆ := by
    refine (M.mem_commSub_img_iff (T.conjSubgroup_le j.2) he).1 ?_
    rw [hcj]
    exact hw
  have hmeet : ⁅E, A⁆ ⊓ ⁅E, conjSubgroup A (j : G)⁻¹⁆ ≠ ⊥ := fun hbot' => by
    have h3 : e ∈ ⁅E, A⁆ ⊓ ⁅E, conjSubgroup A (j : G)⁻¹⁆ := ⟨h1, h2⟩
    rw [hbot', Subgroup.mem_bot] at h3
    exact he1 h3
  have hjN := T.ti (j : G) j.2 hmeet
  exact M.mem_img.2 ⟨j, ⟨j.2, hjN⟩, rfl⟩

end TieData

theorem card_le_of_tie
    (h763 : ∀ (G' : Type) [Group G'] [Finite G'] (V' : Subgroup G'), SevenSixThreeAbelian V')
    {J E A : Subgroup G} (T : TieData J E A) {P : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hPJ : P ≤ J) (hPexp : ∀ x ∈ P, x ^ p = 1)
    (hAP : A ≤ normalizer ((P ⊔ pCoreOf 2 J : Subgroup G) : Set G)) : Nat.card P ≤ p := by
  classical
  obtain ⟨M⟩ := exists_modDataE T.elemAb T.le_normalizer
  have hO : pCoreOf 2 J ≤ J := CFSG.LieType.BorelTits.pCoreOf_le 2 J
  have hPC : P ⊓ centralizer (E : Set G) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxP, hxC⟩
    have hx2 : x ∈ J ⊓ centralizer (E : Set G) := ⟨hPJ hxP, hxC⟩
    obtain ⟨j, hj⟩ := T.isPGroup_cent ⟨x, hx2⟩
    have hj' : x ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    exact E1.mem_of_pow_mem_two_p (N := ⊥) hp hp2 (k := 1) (j := j)
      (by simpa using hPexp x hxP) (by simpa using hj')
  have hcard : Nat.card (M.img P) = Nat.card P := by
    rw [M.card_img hPJ, ← Subgroup.inf_relIndex_right, inf_comm, hPC, Subgroup.relIndex_bot_left]
  have hexp : ∀ x ∈ M.img P, x ^ p = 1 := by
    intro x hx
    obtain ⟨j, hjP, rfl⟩ := M.mem_img.1 hx
    rw [← map_pow]
    have h0 : j ^ p = 1 := Subtype.ext (by simpa using hPexp (j : G) hjP)
    rw [h0, map_one]
  have hAX : M.img A ≤
      normalizer ((M.img P ⊔ pCoreOf 2 (M.img J) : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W)) := by
    rw [← M.img_pCoreOf T.isPGroup_cent, ← M.img_sup hPJ hO]
    exact M.img_le_normalizer T.A_le (sup_le hPJ hO) hAP
  have h1 := card_le_of_assumption131 h763 (T.assumption131 M) (T.card_img_A M)
    (T.isPGroup_inf_normalizer M) hp hp2 (X₁ := M.img P) (M.img_mono hPJ) hexp hAX
  rwa [hcard] at h1

end CFSG.LocalAnalysis.WeakClosure81

end
