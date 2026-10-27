module

public import CFSG.Quasithin.H13.U3S1347Q
public import CFSG.Quasithin.H13.U3S1347S

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem card_mul_card_inf_le {X X' C : Subgroup G} (h : X' ≤ X) :
    Nat.card X' * Nat.card ↥(X ⊓ C) ≤ Nat.card X * Nat.card ↥(X' ⊓ C) := by
  have h1 := relIndex_mul_card C X'
  have h2 := relIndex_mul_card C X
  have h3 : C.relIndex X' ≤ C.relIndex X :=
    relIndex_le_of_le_right h index_ne_zero_of_finite
  rw [inf_comm C X'] at h1
  rw [inf_comm C X] at h2
  calc Nat.card X' * Nat.card ↥(X ⊓ C) =
        C.relIndex X' * Nat.card ↥(X' ⊓ C) * Nat.card ↥(X ⊓ C) := by rw [h1]
    _ ≤ C.relIndex X * Nat.card ↥(X' ⊓ C) * Nat.card ↥(X ⊓ C) := by gcongr
    _ = Nat.card X * Nat.card ↥(X' ⊓ C) := by rw [← h2]; ring

omit [Finite G] in
theorem mem_of_mem_map_subtype {X : Subgroup G} {K : Subgroup ↥X} {g : G}
    (hg : g ∈ K.map X.subtype) : ∃ hX : g ∈ X, (⟨g, hX⟩ : ↥X) ∈ K := by
  obtain ⟨w, hw, rfl⟩ := hg
  exact ⟨w.2, hw⟩

omit [Finite G] in
theorem card_inf_le_of_map {X C : Subgroup G} {Y : Type*} [Group Y] [Finite Y] (F : ↥X →* Y)
    (hF : Function.Surjective F) (P : Y → Prop) (hP : ∀ x : ↥X, (x : G) ∈ C → P (F x)) :
    Nat.card ↥(X ⊓ C) ≤ Nat.card ↥((F.ker.map X.subtype) ⊓ C) * Nat.card {y : Y // P y} ∧
      Nat.card X = Nat.card ↥(F.ker.map X.subtype) * Nat.card Y := by
  constructor
  · let F' : ↥((X ⊓ C).subgroupOf X) →* Y := F.comp ((X ⊓ C).subgroupOf X).subtype
    have hdom : Nat.card ↥((X ⊓ C).subgroupOf X) = Nat.card ↥(X ⊓ C) :=
      Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
    have hker : Nat.card F'.ker = Nat.card ↥((F.ker.map X.subtype) ⊓ C) :=
      Nat.card_congr
        { toFun := fun x => ⟨x.1.1.1, mem_inf.2
            ⟨⟨x.1.1, x.2, rfl⟩, (mem_inf.1 (mem_subgroupOf.1 x.1.2)).2⟩⟩
          invFun := fun z => ⟨⟨⟨z.1, (mem_of_mem_map_subtype (mem_inf.1 z.2).1).fst⟩,
            mem_subgroupOf.2 (mem_inf.2 ⟨(mem_of_mem_map_subtype (mem_inf.1 z.2).1).fst,
              (mem_inf.1 z.2).2⟩)⟩, (mem_of_mem_map_subtype (mem_inf.1 z.2).1).snd⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    have hrange : Nat.card F'.range ≤ Nat.card {y : Y // P y} := by
      refine Nat.card_le_card_of_injective (fun y => ⟨y.1, ?_⟩) fun a b hab => ?_
      · obtain ⟨x, hx⟩ := y.2
        rw [← hx]
        exact hP _ (mem_inf.1 (mem_subgroupOf.1 x.2)).2
      · exact Subtype.ext (congrArg (fun y : {y : Y // P y} => (y : Y)) hab)
    have hmul := card_eq_card_quotient_mul_card_subgroup F'.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange F').toEquiv] at hmul
    rw [← hdom, hmul, ← hker, mul_comm]
    exact Nat.mul_le_mul_left _ hrange
  · have hmul := card_eq_card_quotient_mul_card_subgroup F.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective F hF).toEquiv] at hmul
    rw [hmul, mul_comm, Nat.card_congr (equivMapOfInjective F.ker X.subtype
      X.subtype_injective).toEquiv]

omit [Finite G] in
theorem le_normalizer_of_comm {X I Y : Subgroup G} [IsMulCommutative ↥X] (hIX : I ≤ X)
    (hYX : Y ≤ X) : I ≤ normalizer (Y : Set G) := fun i hi => mem_normalizer_iff.2 fun n => by
  constructor
  · intro hn
    have hc : i * n = n * i :=
      congrArg Subtype.val (mul_comm (⟨i, hIX hi⟩ : ↥X) ⟨n, hYX hn⟩)
    rw [hc, mul_inv_cancel_right]
    exact hn
  · intro hn
    have hc : i * (i * n * i⁻¹) = i * n * i⁻¹ * i :=
      congrArg Subtype.val (mul_comm (⟨i, hIX hi⟩ : ↥X) ⟨_, hYX hn⟩)
    have e : i * n * i⁻¹ = n := by
      calc i * n * i⁻¹ = i⁻¹ * (i * (i * n * i⁻¹)) := by group
        _ = i⁻¹ * (i * n * i⁻¹ * i) := by rw [hc]
        _ = n := by group
    rw [← e]
    exact hn

omit [Finite G] in
theorem exists_ext_of_sup {X I Y : Subgroup G} [IsMulCommutative ↥X] (hIX : I ≤ X)
    (hYX : Y ≤ X) (hX : X ≤ I ⊔ Y) {W : Type*} [Group W] (F : ↥Y →* W)
    (hIY : ∀ y : ↥Y, (y : G) ∈ I → F y = 1) :
    ∃ F₀ : ↥X →* W, (∀ y : ↥Y, F₀ ⟨y, hYX y.2⟩ = F y) ∧ ∀ x : ↥X, (x : G) ∈ I → F₀ x = 1 := by
  set I' : Subgroup ↥X := I.subgroupOf X
  let j : ↥Y →* ↥X ⧸ I' := (QuotientGroup.mk' I').comp (inclusion hYX)
  have hYn : I ≤ normalizer (Y : Set G) := le_normalizer_of_comm hIX hYX
  have hj : Function.Surjective j := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hx : (x : G) ∈ Y ⊔ I := sup_comm I Y ▸ hX x.2
    obtain ⟨y, hy, i, hi, hyi⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hYn).1 hx
    refine ⟨⟨y, hy⟩, ?_⟩
    show QuotientGroup.mk (inclusion hYX ⟨y, hy⟩) = QuotientGroup.mk x
    rw [QuotientGroup.eq]
    show ((inclusion hYX ⟨y, hy⟩)⁻¹ * x : G) ∈ I
    have e : ((inclusion hYX ⟨y, hy⟩)⁻¹ * x : G) = i := by
      show y⁻¹ * (x : G) = i
      rw [hyi, inv_mul_cancel_left]
    rw [e]
    exact hi
  have hker : j.ker ≤ F.ker := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy ⊢
    have hy' : (inclusion hYX y : ↥X) ∈ I' := (QuotientGroup.eq_one_iff _).1 hy
    exact hIY y (mem_subgroupOf.1 hy')
  let Fb : ↥X ⧸ I' →* W := (QuotientGroup.lift j.ker F hker).comp
    (QuotientGroup.quotientKerEquivOfSurjective j hj).symm.toMonoidHom
  have hFb : ∀ y : ↥Y, Fb (j y) = F y := by
    intro y
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective j hj).symm (j y) =
        (y : ↥Y ⧸ j.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1, QuotientGroup.lift_mk]
  refine ⟨Fb.comp (QuotientGroup.mk' I'), fun y => ?_, fun x hx => ?_⟩
  · exact hFb y
  · have h1 : (QuotientGroup.mk' I') x = 1 := by
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 hx)
    rw [MonoidHom.comp_apply, h1, map_one]

omit [Finite G] in
theorem ext_conj {X I Y : Subgroup G} [IsMulCommutative ↥X] (hIX : I ≤ X) (hYX : Y ≤ X)
    (hX : X ≤ I ⊔ Y) {W : Type*} [Group W] {F : ↥Y →* W} {F₀ : ↥X →* W}
    (hF₀Y : ∀ y : ↥Y, F₀ ⟨y, hYX y.2⟩ = F y) (hF₀I : ∀ x : ↥X, (x : G) ∈ I → F₀ x = 1)
    {t : G} (htI : t ∈ normalizer (I : Set G)) (htY : t ∈ normalizer (Y : Set G))
    (s : MulAut W) (hFt : ∀ y : ↥Y, F (conjAct Y ⟨t, htY⟩ y) = s (F y))
    (x : ↥X) (hx : t * x * t⁻¹ ∈ X) : F₀ ⟨t * x * t⁻¹, hx⟩ = s (F₀ x) := by
  have hYn : I ≤ normalizer (Y : Set G) := le_normalizer_of_comm hIX hYX
  have hx' : (x : G) ∈ Y ⊔ I := sup_comm I Y ▸ hX x.2
  obtain ⟨y, hy, i, hi, hyi⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hYn).1 hx'
  have hti : t * i * t⁻¹ ∈ I := (mem_normalizer_iff.1 htI i).1 hi
  have hty : t * y * t⁻¹ ∈ Y := (mem_normalizer_iff.1 htY y).1 hy
  have e1 : (⟨t * x * t⁻¹, hx⟩ : ↥X) = ⟨t * y * t⁻¹, hYX hty⟩ * ⟨t * i * t⁻¹, hIX hti⟩ :=
    Subtype.ext (by
      show t * (x : G) * t⁻¹ = t * y * t⁻¹ * (t * i * t⁻¹)
      rw [hyi]
      group)
  have e2 : x = ⟨y, hYX hy⟩ * ⟨i, hIX hi⟩ := Subtype.ext hyi
  have e3 : F (conjAct Y ⟨t, htY⟩ ⟨y, hy⟩) = F ⟨t * y * t⁻¹, hty⟩ :=
    congrArg F (Subtype.ext (conjAct_val htY ⟨y, hy⟩))
  rw [e1, map_mul, hF₀I ⟨t * i * t⁻¹, hIX hti⟩ hti, mul_one, e2, map_mul,
    hF₀I ⟨i, hIX hi⟩ hi, mul_one]
  have h1 := hF₀Y ⟨t * y * t⁻¹, hty⟩
  have h2 := hF₀Y ⟨y, hy⟩
  rw [h1, h2, ← e3, hFt]

theorem chain_ineq {X I C : Subgroup G} (hIX : I ≤ X) (F : ↥X →* ↥W4)
    (hF : Function.Surjective F) (hIF : ∀ x : ↥X, (x : G) ∈ I → F x = 1)
    (hI : Nat.card I = 16) (P : ↥W4 → Prop) (hP : ∀ x : ↥X, (x : G) ∈ C → P (F x)) :
    256 * Nat.card ↥(X ⊓ C) ≤ Nat.card X * Nat.card ↥(I ⊓ C) * Nat.card {w // P w} := by
  obtain ⟨h1, h2⟩ := card_inf_le_of_map F hF P hP
  have hIN : I ≤ F.ker.map X.subtype := fun i hi => ⟨⟨i, hIX hi⟩, hIF _ hi, rfl⟩
  have h3 := card_mul_card_inf_le (C := C) hIN
  have hW : Nat.card ↥W4 = 16 := by
    have : Fintype.card {x : P6 // InW4 x} = 16 := by decide +kernel
    rw [← this, ← Nat.card_eq_fintype_card]
    rfl
  rw [hW] at h2
  rw [hI] at h3
  calc 256 * Nat.card ↥(X ⊓ C) ≤ 256 * (Nat.card ↥((F.ker.map X.subtype) ⊓ C) *
        Nat.card {w // P w}) := Nat.mul_le_mul_left _ h1
    _ = 16 * (16 * Nat.card ↥((F.ker.map X.subtype) ⊓ C)) * Nat.card {w // P w} := by ring
    _ ≤ 16 * (Nat.card ↥(F.ker.map X.subtype) * Nat.card ↥(I ⊓ C)) * Nat.card {w // P w} := by
        gcongr
    _ = Nat.card X * Nat.card ↥(I ⊓ C) * Nat.card {w // P w} := by rw [h2]; ring

theorem le_centralizer_of_A6 {H₀ T V₀ I A : Subgroup G} (hTH : T ≤ H₀)
    (hV₀ : IsElemAbelian 2 V₀) (hV₀T : V₀ ≤ T) (hIV : I ≤ V₀)
    (hH₀I : H₀ ≤ normalizer (I : Set G)) (hI16 : Nat.card I = 16)
    {ρ : ↥H₀ →* Perm (Fin 6)} {ψ : ↥I ≃* ↥W4}
    (hψ : ∀ (h : ↥H₀) (v : ↥I), ψ (conjAct I ⟨h, hH₀I h.2⟩ v) = act4 (ρ h) (ψ v))
    (hρT : ∀ t (ht : t ∈ T), InD6 (ρ ⟨t, hTH ht⟩))
    (hker : ∀ h : ↥H₀, ρ h = 1 ↔ (h : G) ∈ centralizer (V₀ : Set G))
    {F₀ : ↥V₀ →* ↥W4} (hF₀ : Function.Surjective F₀)
    (hIF : ∀ x : ↥V₀, (x : G) ∈ I → F₀ x = 1)
    (hF₀T : ∀ t (ht : t ∈ T) (x : ↥V₀) (hx : t * x * t⁻¹ ∈ V₀),
      F₀ ⟨t * x * t⁻¹, hx⟩ = act4 (S6Out.phiEquiv.symm (ρ ⟨t, hTH ht⟩)) (F₀ x))
    {j : ℕ} (hj : j ≤ 1) (hA : IsElemAbelianCorank T j A) :
    A ≤ centralizer (V₀ : Set G) := by
  by_contra hAC
  have hAH : A ≤ H₀ := hA.1.trans hTH
  set A' : Subgroup (Perm (Fin 6)) := (A.subgroupOf H₀).map ρ with hA'
  have hAD : ∀ a ∈ A', InD6 a := by
    rintro _ ⟨a, ha, rfl⟩
    exact hρT a (hA.1 (mem_subgroupOf.1 ha))
  have hA'ne : A' ≠ ⊥ := by
    intro hb
    apply hAC
    intro a ha
    have hm : ρ ⟨a, hAH ha⟩ ∈ A' := ⟨⟨a, hAH ha⟩, mem_subgroupOf.2 ha, rfl⟩
    rw [hb, mem_bot] at hm
    exact (hker _).1 hm
  have hA2 : ∀ a ∈ A', a * a = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul]
    have h2 := hA.2.1.2 _ (mem_subgroupOf.1 ha)
    have : a * a = 1 := Subtype.ext (by rw [← sq]; exact h2)
    rw [this, map_one]
  have hfix := S6Out.card_fix_mul_le hAD hA'ne hA2
  have hcardA : Nat.card A' = (A ⊓ centralizer (V₀ : Set G)).relIndex A := by
    have hk : ρ.ker = (centralizer (V₀ : Set G)).subgroupOf H₀ := by
      ext h
      rw [MonoidHom.mem_ker, mem_subgroupOf]
      exact hker h
    rw [hA', ← relIndex_ker, hk, relIndex_subgroupOf hAH, inf_relIndex_left]
  have hB := card_le_relIndex_mul_card_mul_two_pow hV₀ hV₀T hA
  have hf₁ : Nat.card ↥(I ⊓ centralizer (A : Set G)) ≤
      Nat.card {x : ↥W4 // ∀ a ∈ A', act4 a x = x} := by
    refine Nat.card_le_card_of_injective (fun v => ⟨ψ ⟨v, (mem_inf.1 v.2).1⟩, ?_⟩) ?_
    · rintro _ ⟨a, ha, rfl⟩
      rw [← hψ]
      congr 1
      apply Subtype.ext
      rw [conjAct_val]
      show (a : G) * v * (a : G)⁻¹ = v
      rw [mem_centralizer_iff.1 (mem_inf.1 v.2).2 a (mem_subgroupOf.1 ha), mul_inv_cancel_right]
    · intro v w hvw
      have h1 := ψ.injective (congrArg Subtype.val hvw)
      have h2 : (v : G) = w := congrArg (fun z : ↥I => (z : G)) h1
      exact Subtype.ext h2
  have hch := chain_ineq hIV F₀ hF₀ hIF hI16
    (fun w => ∀ a ∈ S6Out.phiEquiv.symm '' (A' : Set (Perm (Fin 6))), act4 a w = w)
    (fun x hx => by
      rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      have hax : (a : G) * x * (a : G)⁻¹ = x := by
        rw [mem_centralizer_iff.1 hx a (mem_subgroupOf.1 ha), mul_inv_cancel_right]
      have h1 := hF₀T a (hA.1 (mem_subgroupOf.1 ha)) x (by rw [hax]; exact x.2)
      have e : (⟨(a : G) * x * (a : G)⁻¹, by rw [hax]; exact x.2⟩ : ↥V₀) = x :=
        Subtype.ext hax
      rw [e] at h1
      exact h1.symm)
  have hc : 0 < Nat.card ↥(V₀ ⊓ centralizer (A : Set G)) := Nat.card_pos
  have h2j : 2 ^ j ≤ 2 := by
    calc 2 ^ j ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hj
      _ = 2 := by norm_num
  rw [← hcardA] at hB
  have key : 256 * Nat.card ↥(V₀ ⊓ centralizer (A : Set G)) ≤
      128 * Nat.card ↥(V₀ ⊓ centralizer (A : Set G)) := by
    calc 256 * Nat.card ↥(V₀ ⊓ centralizer (A : Set G)) ≤
          Nat.card V₀ * Nat.card ↥(I ⊓ centralizer (A : Set G)) *
            Nat.card {w : ↥W4 // ∀ a ∈ S6Out.phiEquiv.symm '' (A' : Set (Perm (Fin 6))),
              act4 a w = w} := hch
      _ ≤ (Nat.card A' * Nat.card ↥(V₀ ⊓ centralizer (A : Set G)) * 2) *
            Nat.card {x : ↥W4 // ∀ a ∈ A', act4 a x = x} *
            Nat.card {w : ↥W4 // ∀ a ∈ S6Out.phiEquiv.symm '' (A' : Set (Perm (Fin 6))),
              act4 a w = w} := by
        gcongr
        exact hB.trans (Nat.mul_le_mul_left _ h2j)
      _ = 2 * Nat.card ↥(V₀ ⊓ centralizer (A : Set G)) * (Nat.card A' *
            Nat.card {x : ↥W4 // ∀ a ∈ A', act4 a x = x} *
            Nat.card {w : ↥W4 // ∀ a ∈ S6Out.phiEquiv.symm '' (A' : Set (Perm (Fin 6))),
              act4 a w = w}) := by ring
      _ ≤ 2 * Nat.card ↥(V₀ ⊓ centralizer (A : Set G)) * 64 := Nat.mul_le_mul_left _ hfix
      _ = 128 * Nat.card ↥(V₀ ⊓ centralizer (A : Set G)) := by ring
  omega

theorem le_normalizer_thompsonJi_of {H T R : Subgroup G} (hRT : R ≤ T)
    (hR : H ≤ normalizer (R : Set G)) {i : ℕ}
    (hA : ∀ A, IsElemAbelianCorank T i A → A ≤ R) :
    H ≤ normalizer (thompsonJi T i : Set G) := by
  rcases lt_or_ge i (CFSG.Open.pRank 2 T) with hi | hi
  · have hJ : thompsonJi T i ≤ R := iSup₂_le fun A h => hA A h
    rw [thompsonJi_eq_of_le hi hJ hRT]
    exact hR.trans (normalizer_le_normalizer_thompsonJi151 R i)
  · have hb : thompsonJi T i = ⊥ := by
      refine le_bot_iff.mp (iSup₂_le fun A h => ?_)
      have h1 : Nat.card A * 2 ^ i ≤ 1 * 2 ^ i := by
        rw [h.2.2, one_mul]
        exact Nat.pow_le_pow_right (by norm_num) hi
      have h2 : Nat.card A ≤ 1 := Nat.le_of_mul_le_mul_right h1 (by positivity)
      exact (card_eq_one.mp (le_antisymm h2 Nat.card_pos)).le
    rw [hb, normalizer_eq_top_iff.mpr inferInstance]
    exact le_top

end CFSG.Quasithin.H13.U3
