module

public import CFSG.Quasithin.Vol2.E2NineTIBender

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6
open scoped commutatorElement

namespace E2

theorem pair_trichotomy (hKG3 : KGBenderMax) {Y : Type} [Group Y] [Finite Y]
    {X L₁ L₂ S₁ S₂ : Subgroup Y} {n : ℕ} (hn2 : 2 ≤ n) (hB₁ : IsPSL 2 2 n ↥L₁ ∨ IsSz n ↥L₁)
    (hB₂ : IsPSL 2 2 n ↥L₂ ∨ IsSz n ↥L₂) (hc : ⁅L₁, L₂⁆ = ⊥) (hinf : L₁ ⊓ L₂ = ⊥)
    (hXN : X ≤ Subgroup.normalizer ((L₁ ⊔ L₂ : Subgroup Y) : Set Y))
    (horb : ∀ x ∈ X, cjSub x L₁ = L₁ ∨ cjSub x L₁ = L₂)
    (hS₁ : IsSylowTwoOf S₁ L₁) (hS₂ : IsSylowTwoOf S₂ L₂) (hP₁1 : S₁ ≠ ⊥) (hP₂1 : S₂ ≠ ⊥)
    (hS₁X : S₁ ≤ X) (hS₂X : S₂ ≤ X) :
    L₁ ≤ X ∨ X ≤ Subgroup.normalizer ((S₁ ⊔ S₂ : Subgroup Y) : Set Y) ∨
      (L₂ ≤ X ∧ X ≤ Subgroup.normalizer (S₁ : Set Y)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs₁ := isSimpleGroup_of_psl_or_sz hB₁
  have hs₂ := isSimpleGroup_of_psl_or_sz hB₂
  have hc' : ⁅L₂, L₁⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hc
  have hinf' : L₂ ⊓ L₁ = ⊥ := by rw [inf_comm]; exact hinf
  set D := X ⊓ (L₁ ⊔ L₂) with hD
  have hDN₁ : D ≤ Subgroup.normalizer (L₁ : Set Y) :=
    inf_le_right.trans (sup_le Subgroup.le_normalizer (le_normalizer_of_commutator_eq_bot hc'))
  have hDN₂ : D ≤ Subgroup.normalizer (L₂ : Set Y) :=
    inf_le_right.trans (sup_le (le_normalizer_of_commutator_eq_bot hc) Subgroup.le_normalizer)
  have hXD : X ≤ Subgroup.normalizer (D : Set Y) := fun x hx =>
    mem_normalizer_inf_of_mem (Subgroup.le_normalizer hx) (hXN hx)
  have hP₁D : S₁ ≤ D ⊓ L₁ := fun x hx =>
    ⟨⟨hS₁X hx, Subgroup.mem_sup_left (hS₁.1 hx)⟩, hS₁.1 hx⟩
  have hP₂D : S₂ ≤ D ⊓ L₂ := fun x hx =>
    ⟨⟨hS₂X hx, Subgroup.mem_sup_right (hS₂.1 hx)⟩, hS₂.1 hx⟩
  rcases hKG3 Y L₁ S₁ (L₁ ⊓ (D ⊔ L₂)) n hn2 hB₁ hS₁
      (fun x hx => ⟨hS₁.1 hx, Subgroup.mem_sup_left (hP₁D hx).1⟩) inf_le_left with hπ₁ | hπ₁
  swap
  · exact Or.inl ((le_of_le_sup_of_simple hc hDN₂ hs₁ hP₁D hP₁1
      (by rw [← hπ₁]; exact inf_le_right)).trans inf_le_left)
  rcases hKG3 Y L₂ S₂ (L₂ ⊓ (D ⊔ L₁)) n hn2 hB₂ hS₂
      (fun x hx => ⟨hS₂.1 hx, Subgroup.mem_sup_left (hP₂D hx).1⟩) inf_le_left with hπ₂ | hπ₂
  ·
    right; left
    set Q := S₁ ⊔ S₂ with hQ
    have hQ2 : IsPGroup 2 Q := IsPGroup.to_sup_of_normal_right' hS₁.2.1 hS₂.2.1 fun x hx =>
      mem_normalizer_of_forall_commute fun y hy =>
        commute_of_commutator_eq_bot hc (hS₁.1 hx) (hS₂.1 hy)
    have hQD : Q ≤ D := sup_le (fun x hx => (hP₁D hx).1) (fun x hx => (hP₂D hx).1)
    have hDQ : D ≤ Subgroup.normalizer (Q : Set Y) := by
      intro d hd
      obtain ⟨a, ha, b, hb, rfl⟩ :=
        exists_mul_of_mem_sup_of_le_normalizer (le_normalizer_of_commutator_eq_bot hc) hd.2
      have haπ : a ∈ L₁ ⊓ (D ⊔ L₂) := ⟨ha, by
        have := (D ⊔ L₂).mul_mem (Subgroup.mem_sup_left hd)
          (Subgroup.mem_sup_right (L₂.inv_mem hb))
        simpa using this⟩
      have hbπ : b ∈ L₂ ⊓ (D ⊔ L₁) := ⟨hb, by
        have := (D ⊔ L₁).mul_mem (Subgroup.mem_sup_right (L₁.inv_mem ha))
          (Subgroup.mem_sup_left hd)
        simpa using this⟩
      refine Subgroup.mul_mem _ (mem_normalizer_sup_of_mem (hπ₁ haπ) ?_)
        (mem_normalizer_sup_of_mem ?_ (hπ₂ hbπ))
      · exact mem_normalizer_of_forall_commute fun y hy =>
          commute_of_commutator_eq_bot hc ha (hS₂.1 hy)
      · exact mem_normalizer_of_forall_commute fun y hy =>
          (commute_of_commutator_eq_bot hc (hS₁.1 hy) hb).symm
    have hmax : ∀ R : Subgroup Y, Q ≤ R → R ≤ D → IsPGroup 2 R → R ≤ Q := by
      intro R hQR hRD hR2
      have h₁ := proj_le_of_isPGroup hc hinf (hRD.trans hDN₂) hR2 hS₁
        (fun x hx => ⟨hS₁.1 hx, Subgroup.mem_sup_left (hQR (Subgroup.mem_sup_left hx))⟩)
      have h₂ := proj_le_of_isPGroup hc' hinf' (hRD.trans hDN₁) hR2 hS₂
        (fun x hx => ⟨hS₂.1 hx, Subgroup.mem_sup_left (hQR (Subgroup.mem_sup_right hx))⟩)
      intro r hr
      obtain ⟨a, ha, b, hb, rfl⟩ :=
        exists_mul_of_mem_sup_of_le_normalizer (le_normalizer_of_commutator_eq_bot hc) (hRD hr).2
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (h₁ ⟨ha, ?_⟩))
        (Subgroup.mem_sup_right (h₂ ⟨hb, ?_⟩))
      · have := (R ⊔ L₂).mul_mem (Subgroup.mem_sup_left hr)
          (Subgroup.mem_sup_right (L₂.inv_mem hb))
        simpa using this
      · have := (R ⊔ L₁).mul_mem (Subgroup.mem_sup_right (L₁.inv_mem ha))
          (Subgroup.mem_sup_left hr)
        simpa using this
    intro x hx
    have hxD : cjSub x D = D := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hXD hx)
    have hcj : cjSub x Q ≤ D := by
      rw [← hxD]
      exact cjSub_mono hQD
    have h2 : IsPGroup 2 ↥(cjSub x Q ⊔ Q) :=
      IsPGroup.to_sup_of_normal_right' (hQ2.map _) hQ2 (hcj.trans hDQ)
    have hxQ : cjSub x Q ≤ Q := le_sup_left.trans (hmax _ le_sup_right (sup_le hcj hQD) h2)
    apply mem_normalizer_of_cjSub_eq
    exact Subgroup.eq_of_le_of_card_ge hxQ (by rw [card_cjSub])
  ·
    have hL₂D : L₂ ≤ D := le_of_le_sup_of_simple hc' hDN₁ hs₂ hP₂D hP₂1
      (by rw [← hπ₂]; exact inf_le_right)
    have hL₂X : L₂ ≤ X := hL₂D.trans inf_le_left
    by_cases hN₁ : X ≤ Subgroup.normalizer (L₁ : Set Y)
    swap
    · left
      obtain ⟨x, hx, hxN⟩ := Set.not_subset.mp hN₁
      rcases horb x hx with h1 | h1
      · exact absurd (mem_normalizer_of_cjSub_eq h1) hxN
      · have h2 : cjSub x⁻¹ L₂ = L₁ := by
          rw [← h1, cjSub_cjSub, inv_mul_cancel, cjSub_one]
        rw [← h2, ← cjSub_self_of_mem (X.inv_mem hx)]
        exact cjSub_mono hL₂X
    right; right
    refine ⟨hL₂X, fun x hx => ?_⟩
    have hxL : cjSub x L₁ = L₁ := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hN₁ hx)
    have hxX : cjSub x X = X := cjSub_self_of_mem hx
    have hcj : cjSub x S₁ ≤ L₁ ⊓ (D ⊔ L₂) := by
      intro y hy
      have hyL : y ∈ L₁ := by
        have := cjSub_mono hS₁.1 hy
        rwa [hxL] at this
      have hyX : y ∈ X := by
        have := cjSub_mono hS₁X hy
        rwa [hxX] at this
      exact ⟨hyL, Subgroup.mem_sup_left ⟨hyX, Subgroup.mem_sup_left hyL⟩⟩
    have h2 : IsPGroup 2 ↥(cjSub x S₁ ⊔ S₁) :=
      IsPGroup.to_sup_of_normal_right' (hS₁.2.1.map _) hS₁.2.1 (hcj.trans hπ₁)
    have hxP : cjSub x S₁ ≤ S₁ := le_sup_left.trans
      ((A4.isSylowTwoOf_iff_maximal.mp hS₁).2.2 _
        (sup_le (hcj.trans inf_le_left) hS₁.1) h2 le_sup_right)
    apply mem_normalizer_of_cjSub_eq
    exact Subgroup.eq_of_le_of_card_ge hxP (by rw [card_cjSub])

section Star

variable {G : Type} [Group G] [Finite G] {H T M V : Subgroup G}

theorem mem_kerIn_of_mem_solvableRadical {Y A : Subgroup G} (hYH : Y ≤ H)
    {L : Subgroup (StarQuot M H)} (hAL : star M H A ≤ L) (hLY : L ≤ star M H Y)
    (hs : IsSimpleGroup ↥L) (hnab : ∃ a b : ↥L, a * b ≠ b * a) {a : G} (haA : a ∈ A)
    (haR : a ∈ (CFSG.solvableRadical ↥Y).map Y.subtype) : a ∈ kerIn M H := by
  set R := (CFSG.solvableRadical ↥Y).map Y.subtype with hRdef
  have hRY : R ≤ Y := Subgroup.map_subtype_le _
  have hRH : R ≤ H := hRY.trans hYH
  have hYR : Y ≤ Subgroup.normalizer (R : Set G) := fun y hy =>
    le_normalizer_map_subtype (CFSG.solvableRadical ↥Y) hy
  have hRs : Group.IsSolvable ↥(star M H R) := by
    have h1 : Group.IsSolvable ↥(CFSG.solvableRadical ↥Y) := A3.solvableRadical_isSolvable
    have h2 : Group.IsSolvable ↥R := Group.isSolvable_of_surjective
      (f := (Subgroup.equivMapOfInjective _ _ Y.subtype_injective).toMonoidHom)
      (MulEquiv.surjective _)
    have h3 : Group.IsSolvable ↥(R.subgroupOf H) := Group.isSolvable_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe hRH).symm.toMonoidHom) (MulEquiv.surjective _)
    exact Group.isSolvable_of_surjective
      (f := (E2P.starMap M H).subgroupMap (R.subgroupOf H))
      ((E2P.starMap M H).subgroupMap_surjective _)
  have hLN : L ≤ Subgroup.normalizer (star M H R : Set (StarQuot M H)) := by
    intro x hx
    obtain ⟨⟨y, hyH⟩, hyY, rfl⟩ := hLY hx
    exact starMap_mem_normalizer hyH (hYR (Subgroup.mem_subgroupOf.mp hyY))
  have hRL : star M H R ⊓ L = ⊥ := by
    have hnorm : ((star M H R ⊓ L).subgroupOf L).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
      exact fun y hy => mem_normalizer_inf_of_mem (hLN hy) (Subgroup.le_normalizer hy)
    rcases hs.eq_bot_or_eq_top_of_normal ((star M H R ⊓ L).subgroupOf L) with h0 | h0
    · rw [Subgroup.subgroupOf_eq_bot] at h0
      exact eq_bot_iff.mpr fun x hx => (Subgroup.mem_bot).mpr
        ((Subgroup.disjoint_def.mp h0) hx hx.2)
    · exfalso
      rw [Subgroup.subgroupOf_eq_top] at h0
      have hLs : Group.IsSolvable ↥L := Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (h0.trans inf_le_left)) (Subgroup.inclusion_injective _)
      obtain ⟨a, b, hab⟩ := hnab
      exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr hLs a b)
  have h1 : E2P.starMap M H ⟨a, hRH haR⟩ ∈ star M H R ⊓ L :=
    ⟨starMap_mem_star (hRH haR) haR, hAL (starMap_mem_star (hRH haR) haA)⟩
  rw [hRL, Subgroup.mem_bot] at h1
  have h2 : (⟨a, hRH haR⟩ : ↥H) ∈ (E2P.starMap M H).ker := h1
  rw [E2P.ker_starMap, Subgroup.mem_subgroupOf] at h2
  exact h2

theorem card_star_le_card_barRad_of_inf {Y A : Subgroup G} (hYH : Y ≤ H) (hAY : A ≤ Y)
    (hA : ∀ a ∈ A, a ∈ (CFSG.solvableRadical ↥Y).map Y.subtype → a ∈ kerIn M H) :
    Nat.card (star M H A) ≤ Nat.card (E1.barRad ↥Y (A.subgroupOf Y)) := by
  classical
  set A' := A.subgroupOf Y with hA'
  let g₁ : ↥A' → ↥(E1.barRad ↥Y A') := fun a =>
    ⟨QuotientGroup.mk' (CFSG.solvableRadical ↥Y) a, ⟨a, a.2, rfl⟩⟩
  let g₂ : ↥A' → ↥(star M H A) := fun a =>
    ⟨E2P.starMap M H ⟨((a : ↥Y) : G), hYH (a : ↥Y).2⟩,
      starMap_mem_star (hYH (a : ↥Y).2) (Subgroup.mem_subgroupOf.mp a.2)⟩
  have hg₁ : Function.Surjective g₁ := by
    rintro ⟨_, a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  have hg₂ : Function.Surjective g₂ := by
    rintro ⟨_, ⟨x, hxH⟩, hxA, rfl⟩
    exact ⟨⟨⟨x, hAY (Subgroup.mem_subgroupOf.mp hxA)⟩,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hxA)⟩, rfl⟩
  have hcompat : ∀ a b : ↥A', g₁ a = g₁ b → g₂ a = g₂ b := by
    intro a b hab
    have h1 : QuotientGroup.mk' (CFSG.solvableRadical ↥Y) (a : ↥Y) =
        QuotientGroup.mk' (CFSG.solvableRadical ↥Y) (b : ↥Y) := congrArg Subtype.val hab
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
    have h2 : ((a : ↥Y) : G)⁻¹ * ((b : ↥Y) : G) ∈ kerIn M H := by
      refine hA _ ?_ ⟨(a : ↥Y)⁻¹ * (b : ↥Y), h1, rfl⟩
      exact A.mul_mem (A.inv_mem (Subgroup.mem_subgroupOf.mp a.2)) (Subgroup.mem_subgroupOf.mp b.2)
    apply Subtype.ext
    show QuotientGroup.mk' _ _ = QuotientGroup.mk' _ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simpa using h2
  let f : ↥(E1.barRad ↥Y A') → ↥(star M H A) := fun x => g₂ (hg₁ x).choose
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨a, rfl⟩ := hg₂ z
    exact ⟨g₁ a, hcompat _ _ (hg₁ (g₁ a)).choose_spec⟩
  exact Nat.card_le_card_of_surjective f hf

theorem le_solvableRadical_of_star_le {Y A : Subgroup G} (hmp : MinParabolic H T M) (hYH : Y ≤ H)
    (hAY : A ≤ Y) {U : Subgroup (StarQuot M H)} (hU2 : IsPGroup 2 U)
    (hYU : star M H Y ≤ Subgroup.normalizer (U : Set (StarQuot M H))) (hAU : star M H A ≤ U) :
    A ≤ (CFSG.solvableRadical ↥Y).map Y.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ψ : ↥Y →* StarQuot M H := (E2P.starMap M H).comp (Subgroup.inclusion hYH) with hψ
  set P : Subgroup ↥Y := U.comap ψ with hP
  have hPn : P.Normal := by
    refine ⟨fun p hp y => ?_⟩
    show ψ (y * p * y⁻¹) ∈ U
    rw [map_mul, map_mul, map_inv]
    have hyN : ψ y ∈ Subgroup.normalizer (U : Set (StarQuot M H)) :=
      hYU (starMap_mem_star (hYH y.2) y.2)
    exact (Subgroup.mem_normalizer_iff.mp hyN _).mp hp
  have hPs : Group.IsSolvable ↥P := by
    have hJs : Group.IsSolvable ↥(E2P.starMap M H).ker := E2P.isSolvable_ker_starMap hmp
    have hU : Group.IsSolvable ↥U := by
      have := hU2.isNilpotent
      infer_instance
    set g : ↥P →* ↥U := (ψ.comp P.subtype).codRestrict U (fun p => p.2) with hg
    let f : ↥(g.ker) →* ↥(E2P.starMap M H).ker :=
      { toFun := fun x => ⟨Subgroup.inclusion hYH ((x : ↥P) : ↥Y), by
          have hx : g x = 1 := x.2
          have := congrArg Subtype.val hx
          exact this⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hfinj : Function.Injective f := by
      intro a b hab
      have := congrArg (fun z : ↥(E2P.starMap M H).ker => ((z : ↥H) : G)) hab
      exact Subtype.ext (Subtype.ext (Subtype.ext this))
    have hker : Group.IsSolvable ↥(g.ker) :=
      Group.isSolvable_of_isSolvable_injective (f := f) hfinj
    exact Group.isSolvable_of_ker_le_range g.ker.subtype g (by rw [Subgroup.range_subtype])
  have hPR : P ≤ CFSG.solvableRadical ↥Y := A3.le_solvableRadical hPn hPs
  intro a ha
  refine ⟨⟨a, hAY ha⟩, hPR ?_, rfl⟩
  show ψ ⟨a, hAY ha⟩ ∈ U
  exact hAU (starMap_mem_star (hYH (hAY ha)) ha)

end Star

section Main

variable {G : Type} [Group G] [Finite G] {H T M V : Subgroup G}

theorem exists_mem_ne_one_ne {Y : Type*} [Group Y] [Finite Y] {K : Subgroup Y}
    (hK : 2 < Nat.card K) (v : Y) : ∃ w ∈ K, w ≠ 1 ∧ w ≠ v := by
  by_contra hne
  push Not at hne
  have hsub : (K : Set Y) ⊆ {1, v} := by
    intro w hw
    by_cases h1 : w = 1
    · exact Or.inl h1
    · exact Or.inr (hne w hw h1)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({1, v} : Set Y).ncard ≤ 2 :=
    (Set.ncard_insert_le 1 {v}).trans (by rw [Set.ncard_singleton])
  have h3 : Nat.card K = (K : Set Y).ncard := Nat.card_coe_set_eq (K : Set Y)
  omega

omit [Finite G] in
theorem not_eTwo_of_le_solvableRadical {K' A S : Subgroup G}
    (hA : A ≤ (CFSG.solvableRadical ↥K').map K'.subtype) :
    ¬ E1.ETwo ↥K' (S.subgroupOf K') (A.subgroupOf K') := by
  have hRad : E1.barRad ↥K' (A.subgroupOf K') = ⊥ := by
    unfold E1.barRad
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hA (Subgroup.mem_subgroupOf.mp hx)
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  rintro ⟨-, -, -, L, hL, -, hL'⟩
  rw [hRad] at hL'
  rcases hL' with h1 | ⟨h1, -⟩
  · rw [Subgroup.commutator_bot_right] at h1
    have := CFSG.LocalCores.isQuasisimple_nontrivial hL.1
    exact ((Subgroup.nontrivial_iff_ne_bot L).mp this) h1
  · exact h1 bot_le

theorem conjSub_eq_cjSub' {Y : Type} [Group Y] (g : Y) (X : Subgroup Y) :
    conjSub g X = cjSub g X := by
  ext x
  rw [mem_conjSub, mem_cjSub]

theorem le_nParam_of_pair_ti
    (hKG1' : KGBenderInnerTwo) (h : Hyp28 H T M V) (hTI : IsTISetIn V M)
    (hsq : SQTKGroup ↥(⊤ : Subgroup (StarQuot M H))) {K : Subgroup (StarQuot M H)}
    {t : StarQuot M H} (hP : PairCase ⊤ (star M H T) K t)
    (hHK : (⊤ : Subgroup (StarQuot M H)) = K ⊔ star M H T)
    (hM : star M H M = (star M H M ⊓ K) ⊔ cjSub t (star M H M ⊓ K) ⊔ star M H T)
    (hMK : star M H M ⊓ K =
      K ⊓ Subgroup.normalizer ((star M H T ⊓ K : Subgroup (StarQuot M H)) : Set _))
    {n : ℕ} (hn2 : 2 ≤ n) (hty : IsPSL 2 2 n ↥K ∨ IsSz n ↥K) :
    (n : ℕ∞) ≤ E1.nParam H := by
  have := E2P.finite_starQuot M H
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := h.minParabolic.isSylow.1
  have hY28 := h.star hsq
  have hmpY := E2P.minParabolic_star h.minParabolic
  have hJY : kerIn (star M H M) ⊤ = ⊥ := E2P.kerIn_star M H
  set Ts := star M H T with hTs
  set Ms := star M H M with hMs
  set L₂ := cjSub t K with hL₂
  have htT : t ∈ Ts := hP.mem
  have hty₂ : IsPSL 2 2 n ↥L₂ ∨ IsSz n ↥L₂ :=
    hty.imp (isPSL_of_mulEquiv (cjSubEquiv t K).symm) (isSz_of_mulEquiv' (cjSubEquiv t K).symm)
  have hBen₁ : IsBenderOf n ↥K := ⟨hn2, hty.elim Or.inl (fun h' => Or.inr (Or.inl h'))⟩
  have hc' : ⁅L₂, K⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hP.comm
  have hinf' : L₂ ⊓ K = ⊥ := by rw [inf_comm]; exact hP.inf
  obtain ⟨hO, hinv⟩ := hKG1' (StarQuot M H) ⊤ Ts Ms K t n hmpY hJY htT le_top hP.ne hP.norm
    hP.cent hP.inf hP.comm hHK.symm hn2 hty hM hMK
  have hS₁ : IsSylowTwoOf (Ts ⊓ K) K :=
    E2P.isSylowTwoOf_inf_of_subnormal hmpY.isSylow (subnormal_of_mem_cComp hP.comp)
  have hS₂ : IsSylowTwoOf (Ts ⊓ L₂) L₂ :=
    E2P.isSylowTwoOf_inf_of_subnormal hmpY.isSylow (subnormal_of_mem_cComp hP.comp')
  obtain ⟨kK, hBK⟩ := exists_fusionBenderBorel_of_psl_or_sz hn2 hty
  obtain ⟨kL, hBL⟩ := exists_fusionBenderBorel_of_psl_or_sz hn2 hty₂
  obtain ⟨hZ₁card, htrans₁⟩ := exists_conj_center_of_isBenderOf hBen₁ hS₁
  obtain ⟨hZ₂card, -⟩ := card_inf_centralizer_of_fusionBenderBorel hBL hS₂
  set Z₁ := Ts ⊓ K ⊓ Subgroup.centralizer ((Ts ⊓ K : Subgroup (StarQuot M H)) : Set _)
    with hZ₁
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  set E := tiClosure M V with hEdef
  have hEel := h.isElemAbelian_tiClosure hTI
  have hEO := h.tiClosure_le_pCoreOf
  have hET : E ≤ T := hEO.trans h.pCoreOf_M_le_T
  have hVE : V ≤ E := le_tiClosure
  have hEsel := isElemAbelian_star (M := M) (H := H) hEel
  have hEsD : star M H E ≤ K ⊔ L₂ :=
    ((star_mono hEO).trans (star_pCoreOf_le h.minParabolic)).trans hO
  have hEsT : star M H E ≤ Ts := star_mono hET
  have hEsN : Ms ≤ Subgroup.normalizer (star M H E : Set (StarQuot M H)) := by
    rintro _ ⟨⟨m, hmH⟩, hm, rfl⟩
    exact starMap_mem_normalizer hmH (le_normalizer_tiClosure (Subgroup.mem_subgroupOf.1 hm))
  have hEs1 : star M H E ≠ ⊥ := fun hb => hY28.ne_bot (le_bot_iff.mp (hb ▸ star_mono hVE))
  have hEc : ∀ e ∈ star M H E, ∀ x ∈ Ts ⊓ (K ⊔ L₂), e * x = x * e := fun e he x hx =>
    ((Subgroup.mem_centralizer_iff.mp (hinv e ⟨hEsT he, hEsD he⟩ (hEsel.2 e he))) x hx).symm
  obtain ⟨hE₁S, hE₁C, -⟩ := proj_le_inf_centralizer hP.comm hP.inf hEsD hEsel.2
    (fun e he x hx => hEc e he x ⟨hx.1, Subgroup.mem_sup_left hx.2⟩) hS₁
  have hEKZ : star M H E ⊓ K ≤ Z₁ := fun x hx =>
    ⟨hE₁S ⟨hx.2, Subgroup.mem_sup_left hx.1⟩, hE₁C ⟨hx.2, Subgroup.mem_sup_left hx.1⟩⟩
  have hKNL : K ≤ Subgroup.normalizer (L₂ : Set (StarQuot M H)) :=
    le_normalizer_of_commutator_eq_bot hP.comm
  have hcommK : ∀ b ∈ Ms ⊓ K, ∀ a ∈ K, ∀ c ∈ L₂,
      b * (a * c) * b⁻¹ * (a * c)⁻¹ = b * a * b⁻¹ * a⁻¹ := by
    intro b hb a ha c hc
    have hbc : b * c = c * b := commute_of_commutator_eq_bot hP.comm hb.2 hc
    have hcb : c * b⁻¹ = b⁻¹ * c := by
      calc c * b⁻¹ = b⁻¹ * (b * c) * b⁻¹ := by group
        _ = b⁻¹ * (c * b) * b⁻¹ := by rw [hbc]
        _ = b⁻¹ * c := by group
    calc b * (a * c) * b⁻¹ * (a * c)⁻¹ = b * a * (c * b⁻¹) * c⁻¹ * a⁻¹ := by group
      _ = b * a * (b⁻¹ * c) * c⁻¹ * a⁻¹ := by rw [hcb]
      _ = b * a * b⁻¹ * a⁻¹ := by group
  have hBE : ∀ b ∈ Ms ⊓ K, ∀ e ∈ star M H E, b * e * b⁻¹ * e⁻¹ ∈ star M H E ⊓ K := by
    intro b hb e he
    refine ⟨?_, ?_⟩
    · have h1 := (Subgroup.mem_normalizer_iff.mp (hEsN hb.1) e).mp he
      exact (star M H E).mul_mem h1 ((star M H E).inv_mem he)
    · obtain ⟨a, ha, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hKNL (hEsD he)
      rw [hcommK b hb a ha c hc]
      exact K.mul_mem (K.mul_mem (K.mul_mem hb.2 ha) (K.inv_mem hb.2)) (K.inv_mem ha)
  have hfix : ∀ z ∈ Z₁, (∀ b ∈ Ms ⊓ K, b * z * b⁻¹ = z) → z = 1 := by
    intro z hz hzb
    by_contra hz1
    obtain ⟨w, hw, hw1, hwz⟩ := exists_mem_ne_one_ne (K := Z₁) (by omega) z
    obtain ⟨m, hm, hmz⟩ := htrans₁ z hz w hw hz1 hw1
    have hmM : m ∈ Ms ⊓ K := hMK.symm ▸ hm
    have h1 := hzb m⁻¹ ⟨Ms.inv_mem hmM.1, K.inv_mem hmM.2⟩
    rw [inv_inv] at h1
    exact hwz (hmz.symm.trans h1)
  have hLt : cjSub t L₂ = K := by
    rcases hP.orbit (t * t) (Subgroup.mem_top _) with h1 | h1
    · rw [hL₂, cjSub_cjSub]
      exact h1
    · exfalso
      apply hP.ne
      have h3 := congrArg (cjSub t⁻¹) h1
      rw [cjSub_cjSub, cjSub_cjSub, inv_mul_cancel_left, inv_mul_cancel, cjSub_one] at h3
      exact h3
  have hEK1 : star M H E ⊓ K ≠ ⊥ := by
    intro hbot
    have hEL : star M H E ≤ L₂ := by
      intro e he
      obtain ⟨a, ha, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hKNL (hEsD he)
      have haZ : a ∈ Z₁ := by
        have haE : a ∈ K ⊓ (star M H E ⊔ L₂) := ⟨ha, by
          have := (star M H E ⊔ L₂).mul_mem (Subgroup.mem_sup_left he)
            (Subgroup.mem_sup_right (L₂.inv_mem hc))
          simpa using this⟩
        exact ⟨hE₁S haE, hE₁C haE⟩
      have ha1 : a = 1 := hfix a haZ fun b hb => by
        have h1 := hBE b hb _ he
        rw [hbot, Subgroup.mem_bot, hcommK b hb a ha c hc] at h1
        have : b * a * b⁻¹ = a := by
          calc b * a * b⁻¹ = b * a * b⁻¹ * a⁻¹ * a := by group
            _ = a := by rw [h1, one_mul]
        exact this
      rw [ha1, one_mul]
      exact hc
    have htE : cjSub t (star M H E) = star M H E :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hEsN (hmpY.le htT))
    have hEK : star M H E ≤ K := by
      rw [← htE, ← hLt]
      exact cjSub_mono hEL
    exact hEs1 (le_bot_iff.mp (by rw [← hP.inf]; exact le_inf hEK hEL))
  have hEKeq : star M H E ⊓ K = Z₁ := by
    refine le_antisymm hEKZ fun z hz => ?_
    obtain ⟨⟨e, he⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hEK1
    have he1' : e ≠ 1 := fun h' => he1 (Subtype.ext h')
    by_cases hz1 : z = 1
    · rw [hz1]; exact (star M H E ⊓ K).one_mem
    obtain ⟨m, hm, hmz⟩ := htrans₁ e (hEKZ he) z hz he1' hz1
    have hmM : m ∈ Ms ⊓ K := hMK.symm ▸ hm
    rw [← hmz]
    refine ⟨?_, K.mul_mem (K.mul_mem (K.inv_mem hmM.2) he.2) hmM.2⟩
    have := (Subgroup.mem_normalizer_iff.mp (hEsN (Ms.inv_mem hmM.1)) e).mp he.1
    simpa using this
  set F := E ⊓ (K.comap (E2P.starMap M H)).map H.subtype with hFdef
  have hFE : F ≤ E := inf_le_left
  have hFT : F ≤ T := hFE.trans hET
  have hFel : IsElemAbelian 2 F := by
    have := hEel.1
    exact ⟨⟨⟨fun a b => Subtype.ext (setLike_mul_comm (hFE a.2) (hFE b.2))⟩⟩,
      fun x hx => hEel.2 x (hFE hx)⟩
  have hFs : star M H F = Z₁ := by
    rw [← hEKeq]
    ext x
    constructor
    · rintro ⟨⟨f, hfH⟩, hf, rfl⟩
      have hf' : f ∈ F := Subgroup.mem_subgroupOf.mp hf
      refine ⟨starMap_mem_star hfH hf'.1, ?_⟩
      obtain ⟨y, hy, hyf⟩ := hf'.2
      have hy' : y = ⟨f, hfH⟩ := Subtype.ext hyf
      rw [← hy']
      exact hy
    · rintro ⟨⟨⟨e, heH⟩, he, rfl⟩, hK⟩
      exact ⟨⟨e, heH⟩, Subgroup.mem_subgroupOf.mpr
        ⟨Subgroup.mem_subgroupOf.mp he, ⟨⟨e, heH⟩, hK, rfl⟩⟩, rfl⟩
  have hFJ : ¬ F ≤ kerIn M H := by
    intro hle
    have h1 : star M H F = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨⟨f, hfH⟩, hf, rfl⟩
      rw [Subgroup.mem_bot]
      show QuotientGroup.mk' _ _ = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hle (Subgroup.mem_subgroupOf.mp hf)
    rw [hFs] at h1
    rw [h1, Subgroup.card_bot] at hZ₁card
    omega
  have hev : Even (2 ^ n) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have horbK : ∀ x : StarQuot M H, cjSub x K = K ∨ cjSub x K = L₂ :=
    fun x => hP.orbit x (Subgroup.mem_top x)
  have horbL : ∀ x : StarQuot M H, cjSub x L₂ = L₂ ∨ cjSub x L₂ = K := by
    intro x
    rcases horbK (x * t) with h1 | h1
    · right
      rw [hL₂, cjSub_cjSub]
      exact h1
    · left
      rw [hL₂, cjSub_cjSub]
      exact h1
  have hDN : (⊤ : Subgroup (StarQuot M H)) ≤
      Subgroup.normalizer ((K ⊔ L₂ : Subgroup (StarQuot M H)) : Set _) := hP.norm
  have hP₁1 : Ts ⊓ K ≠ ⊥ := by
    intro h0
    rw [hZ₁, h0, bot_inf_eq, Subgroup.card_bot] at hZ₁card
    omega
  have hP₂1 : Ts ⊓ L₂ ≠ ⊥ := by
    intro h0
    rw [h0, bot_inf_eq, Subgroup.card_bot] at hZ₂card
    omega
  refine le_nParam_of_forall_isE h.minParabolic hFT hFel hFJ ?_
  intro i _ hin g hg hAT K' hE'
  by_contra hK'M
  obtain ⟨hK'H, hτ, -, hEE⟩ := hE'
  set A := A1b.conjSub g F with hAdef
  have hAH : A ≤ H := hAT.trans hTH
  have hAel : IsElemAbelian 2 A := isElemAbelian_cjSub hFel
  set g' := E2P.starMap M H ⟨g, hg⟩ with hg'
  have hAs : star M H A = cjSub g' Z₁ := by
    rw [hAdef, a1bConjSub_eq, star_conjSub hg, hFs, conjSub_eq_cjSub']
  have hAsT : star M H A ≤ Ts := star_mono hAT
  have hAK' : A ≤ K' := fun a ha => (hτ (mem_tauOf_of_commutator_mem_kerIn h.minParabolic hAT
    (hAT ha) fun a' ha' => by
      have := hAel.1
      have hc : a * a' = a' * a := setLike_mul_comm ha ha'
      rw [commutatorElement_eq_one_iff_mul_comm.mpr hc]
      exact (kerIn M H).one_mem)).2
  have hK'Ms : ¬ star M H K' ≤ Ms := by
    intro hle
    apply hK'M
    intro k hk
    exact mem_of_starMap_mem_star (hK'H hk) (hle (starMap_mem_star (hK'H hk) hk))
  have hlt : 2 ^ i < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) hin
  have hcardA : Nat.card ↥(star M H A) = 2 ^ n := by rw [hAs, card_cjSub, hZ₁card]
  have key : ∀ L L' : Subgroup (StarQuot M H), (IsPSL 2 2 n ↥L ∨ IsSz n ↥L) →
      (IsPSL 2 2 n ↥L' ∨ IsSz n ↥L') → ⁅L, L'⁆ = ⊥ → L ⊓ L' = ⊥ →
      (⊤ : Subgroup (StarQuot M H)) ≤ Subgroup.normalizer ((L ⊔ L' : Subgroup _) : Set _) →
      (∀ x : StarQuot M H, cjSub x L = L ∨ cjSub x L = L') →
      (∀ x : StarQuot M H, cjSub x L' = L' ∨ cjSub x L' = L) →
      IsSylowTwoOf (Ts ⊓ L) L → IsSylowTwoOf (Ts ⊓ L') L' → Ts ⊓ L ≠ ⊥ → Ts ⊓ L' ≠ ⊥ →
      star M H A = Ts ⊓ L ⊓ Subgroup.centralizer ((Ts ⊓ L : Subgroup (StarQuot M H)) : Set _) →
      False := by
    intro L L' hB hB' hc hinfL hXN horb horb' hS hS' hP1 hP2 hAZ
    have hsL := isSimpleGroup_of_psl_or_sz hB
    have hsL' := isSimpleGroup_of_psl_or_sz hB'
    have hnabL := nonabelian_of_psl_or_sz (by omega) hB
    have hnabL' := nonabelian_of_psl_or_sz (by omega) hB'
    have hAL : star M H A ≤ L := hAZ ▸ (inf_le_left.trans inf_le_right)
    have hτK : ∀ (x : G) (hx : x ∈ T), (E2P.starMap M H ⟨x, hTH hx⟩ ∈ Ts ⊓ L ∨
        E2P.starMap M H ⟨x, hTH hx⟩ ∈ Ts ⊓ L') → x ∈ K' := by
      intro x hx hxU
      refine (hτ (mem_tauOf_of_commutator_mem_kerIn h.minParabolic hAT hx fun a ha => ?_)).2
      have haZ : E2P.starMap M H ⟨a, hAH ha⟩ ∈ Ts ⊓ L ⊓
          Subgroup.centralizer ((Ts ⊓ L : Subgroup (StarQuot M H)) : Set _) :=
        hAZ ▸ starMap_mem_star (hAH ha) ha
      refine commutator_mem_kerIn_of_commute (hTH hx) (hAH ha) ?_
      rcases hxU with hxL | hxL'
      · exact (Subgroup.mem_centralizer_iff.mp haZ.2) _ hxL
      · exact (commute_of_commutator_eq_bot hc haZ.1.2 hxL'.2).symm
    have hSK' : Ts ⊓ L ≤ star M H K' := by
      intro u hu
      obtain ⟨⟨x, hxH⟩, hx, rfl⟩ := hu.1
      exact starMap_mem_star hxH (hτK x (Subgroup.mem_subgroupOf.mp hx) (Or.inl hu))
    have hS'K' : Ts ⊓ L' ≤ star M H K' := by
      intro u hu
      obtain ⟨⟨x, hxH⟩, hx, rfl⟩ := hu.1
      exact starMap_mem_star hxH (hτK x (Subgroup.mem_subgroupOf.mp hx) (Or.inr hu))
    have hsolK' : E1.EOne ↥K' (A.subgroupOf K') → ∀ X : Subgroup (StarQuot M H),
        X ≤ star M H K' → IsSimpleGroup ↥X → (∃ a b : ↥X, a * b ≠ b * a) → False := by
      intro hE1 X hXK' hsX hnabX
      have hsol := E1.RootLift.isSolvable_of_eOne hE1
      have h4 : Group.IsSolvable ↥(K'.subgroupOf H) := Group.isSolvable_of_surjective
        (f := (Subgroup.subgroupOfEquivOfLe hK'H).symm.toMonoidHom) (MulEquiv.surjective _)
      have h5 : Group.IsSolvable ↥(star M H K') := Group.isSolvable_of_surjective
        (f := (E2P.starMap M H).subgroupMap (K'.subgroupOf H))
        ((E2P.starMap M H).subgroupMap_surjective _)
      have hsolX : Group.IsSolvable ↥X := Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion hXK') (Subgroup.inclusion_injective _)
      obtain ⟨a, b, hab⟩ := hnabX
      exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr hsolX a b)
    rcases pair_trichotomy kgBenderMax_holds hn2 hB hB' hc hinfL
        (fun x _ => hXN (Subgroup.mem_top x)) (fun x _ => horb x) hS hS' hP1 hP2 hSK' hS'K' with
      hLK' | hN | ⟨hL'K', hN⟩
    ·
      have hcardle := card_star_le_card_barRad_of_inf hK'H hAK' fun a ha haR =>
        mem_kerIn_of_mem_solvableRadical hK'H hAL hLK' hsL hnabL ha haR
      rw [hcardA] at hcardle
      rcases hEE with ⟨hE1, -⟩ | ⟨-, h3⟩
      · exact hsolK' hE1 L hLK' hsL hnabL
      · omega
    ·
      apply hK'Ms
      refine hN.trans fun x hx => ?_
      refine hmpY.le_of_lt (X := Subgroup.normalizer
        (((Ts ⊓ L) ⊔ (Ts ⊓ L') : Subgroup (StarQuot M H)) : Set _)) ?_ ?_ hx
      · intro y hy
        apply mem_normalizer_of_cjSub_eq
        have hyT : cjSub y Ts = Ts := cjSub_self_of_mem hy
        have e1 : ∀ X : Subgroup (StarQuot M H), cjSub y (Ts ⊓ X) = Ts ⊓ cjSub y X := by
          intro X
          have h1 : cjSub y (Ts ⊓ X) = cjSub y Ts ⊓ cjSub y X :=
            Subgroup.map_inf_eq _ _ _ (MulAut.conj y).injective
          rw [h1, hyT]
        have hinj : ∀ X Y : Subgroup (StarQuot M H), cjSub y X = cjSub y Y → X = Y := by
          intro X Y hXY
          have := congrArg (cjSub y⁻¹) hXY
          rwa [cjSub_cjSub, cjSub_cjSub, inv_mul_cancel, cjSub_one, cjSub_one] at this
        have hLL : L ≠ L' := by
          intro hLL'
          apply hP1
          rw [eq_bot_iff]
          intro x hx
          have : x ∈ L ⊓ L' := ⟨hx.2, hLL' ▸ hx.2⟩
          rwa [hinfL] at this
        rw [cjSub_sup, e1, e1]
        rcases horb y with h1 | h1 <;> rcases horb' y with h2 | h2
        · rw [h1, h2]
        · exact absurd (hinj _ _ (h1.trans h2.symm)) hLL
        · exact absurd (hinj _ _ (h1.trans h2.symm)) hLL
        · rw [h1, h2, sup_comm]
      · refine lt_of_le_of_ne le_top fun heq => ?_
        have hUN : (⊤ : Subgroup (StarQuot M H)) ≤ Subgroup.normalizer
            (((Ts ⊓ L) ⊔ (Ts ⊓ L') : Subgroup (StarQuot M H)) : Set _) := heq ▸ le_rfl
        have hU2 : IsPGroup 2 ↥((Ts ⊓ L) ⊔ (Ts ⊓ L')) :=
          IsPGroup.to_sup_of_normal_right' hS.2.1 hS'.2.1 fun x hx =>
            mem_normalizer_of_forall_commute fun y hy =>
              commute_of_commutator_eq_bot hc hx.2 hy.2
        have hUO := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_top hUN hU2
        have hU1 := le_bot_iff.mp (hUO.trans (hmpY.pCoreOf_le_kerIn.trans hJY.le))
        exact hP1 (le_bot_iff.mp (le_sup_left.trans hU1.le))
    ·
      have hAR := le_solvableRadical_of_star_le h.minParabolic hK'H hAK' hS.2.1 hN
        (hAZ ▸ inf_le_left)
      rcases hEE with ⟨hE1, -⟩ | ⟨hE2, -⟩
      · exact hsolK' hE1 L' hL'K' hsL' hnabL'
      · exact not_eTwo_of_le_solvableRadical hAR hE2
  have hS₁g := isSylowTwoOf_cjSub hS₁ g'
  have hZg := cjSub_inf_centralizer g' (Ts ⊓ K)
  rcases horbK g' with hgK | hgK
  · rw [hgK] at hS₁g
    have hle1 : star M H A ≤ Ts ⊓ K := le_inf hAsT (by
      rw [hAs, ← hgK]
      exact cjSub_mono (inf_le_left.trans inf_le_right))
    have hSeq := eq_of_inf_centralizer_le hev hBK hS₁ hS₁g (by rw [← hZg, ← hAs]; exact hle1)
    exact key K L₂ hty hty₂ hP.comm hP.inf hDN horbK horbL hS₁ hS₂ hP₁1 hP₂1
      (by rw [hAs, hZg, ← hSeq])
  · rw [hgK] at hS₁g
    have hle1 : star M H A ≤ Ts ⊓ L₂ := le_inf hAsT (by
      rw [hAs, ← hgK]
      exact cjSub_mono (inf_le_left.trans inf_le_right))
    have hSeq := eq_of_inf_centralizer_le hev hBL hS₂ hS₁g (by rw [← hZg, ← hAs]; exact hle1)
    exact key L₂ K hty₂ hty hc' hinf' (by rw [sup_comm]; exact hDN) horbL horbK hS₂ hS₁ hP₂1 hP₁1
      (by rw [hAs, hZg, ← hSeq])

end Main

end E2

end CFSG.Quasithin
