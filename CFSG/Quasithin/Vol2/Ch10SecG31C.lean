module

public import CFSG.Quasithin.Vol2.Ch10SecG31B
public import CFSG.Quasithin.Background.G10FourGL

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.G31

open Module CFSG.GroupTheory.GLnTwoSplitting

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem mem_span_pair_two {x y w : W} :
    w ∈ Submodule.span (ZMod 2) {x, y} ↔ w = 0 ∨ w = x ∨ w = y ∨ w = x + y := by
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩
    rcases zmod_two_eq_zero_or_one a with rfl | rfl <;>
      rcases zmod_two_eq_zero_or_one b with rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, 0, by simp⟩
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
    · exact ⟨1, 1, by simp⟩

theorem transvection_congr {f f' : Dual (ZMod 2) W} {d d' : W} (hf : f = f') (hd : d = d')
    (h : f d = 0) (h' : f' d' = 0) :
    LinearEquiv.transvection h = LinearEquiv.transvection h' := by
  subst hf
  subst hd
  rfl

@[expose] def IsFull (Δ : Set W) (F : W → Submodule (ZMod 2) (Dual (ZMod 2) W))
    (P : Submodule (ZMod 2) W) : Prop :=
  ∀ v ∈ P, v ≠ 0 → v ∈ Δ ∧ C F v ⊓ P = Submodule.span (ZMod 2) {v}

@[expose] def grpPY (Δ : Set W) (F : W → Submodule (ZMod 2) (Dual (ZMod 2) W))
    (P : Submodule (ZMod 2) W) (y : W) : Subgroup (W ≃ₗ[ZMod 2] W) :=
  Subgroup.closure {t | ∃ v ∈ Δ, (v ∈ P ∨ v = y) ∧ ∃ ψ ∈ F v, ∃ h : ψ v = 0,
    t = LinearEquiv.transvection h}

theorem transvection_mem_grpPY {Δ : Set W} {F : W → Submodule (ZMod 2) (Dual (ZMod 2) W)}
    {P : Submodule (ZMod 2) W} {y v : W} (hv : v ∈ Δ) (hvP : v ∈ P ∨ v = y)
    {ψ : Dual (ZMod 2) W} (hψ : ψ ∈ F v) (h : ψ v = 0) :
    LinearEquiv.transvection h ∈ grpPY Δ F P y :=
  Subgroup.subset_closure ⟨v, hv, hvP, ψ, hψ, h, rfl⟩

variable [Finite W]

theorem invariant_closure {S : Set (W ≃ₗ[ZMod 2] W)} {U : Submodule (ZMod 2) W}
    (hS : ∀ t ∈ S, ∀ u ∈ U, t u ∈ U) : G11.Invariant (Subgroup.closure S) U := by
  intro k hk
  induction hk using Subgroup.closure_induction with
  | mem t ht => exact hS t ht
  | one => exact fun u hu => hu
  | mul a b _ _ ha hb => exact fun u hu => ha _ (hb u hu)
  | inv a _ ha =>
    intro u hu
    have hle : U.map (a : W →ₗ[ZMod 2] W) ≤ U := by
      rintro _ ⟨w, hw, rfl⟩
      exact ha w hw
    have heq : U.map (a : W →ₗ[ZMod 2] W) = U :=
      Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq a U)
    rw [← heq] at hu
    obtain ⟨w, hw, rfl⟩ := hu
    show a.symm (a w) ∈ U
    simpa using hw

theorem invariant_grpPY {Δ : Set W} {F : W → Submodule (ZMod 2) (Dual (ZMod 2) W)}
    {P : Submodule (ZMod 2) W} {y : W} :
    G11.Invariant (grpPY Δ F P y) (P ⊔ Submodule.span (ZMod 2) {y}) := by
  refine invariant_closure ?_
  rintro t ⟨v, -, hvP, ψ, -, h, rfl⟩ u hu
  rw [transvection_apply]
  refine Submodule.add_mem _ hu (Submodule.smul_mem _ _ ?_)
  rcases hvP with hvP | rfl
  · exact Submodule.mem_sup_left hvP
  · exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)

theorem map_eq_of_invariant {K : Subgroup (W ≃ₗ[ZMod 2] W)} {U : Submodule (ZMod 2) W}
    (hK : G11.Invariant K U) {k : W ≃ₗ[ZMod 2] W} (hk : k ∈ K) :
    U.map (k : W →ₗ[ZMod 2] W) = U := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ (LinearEquiv.finrank_map_eq k U)
  rintro _ ⟨w, hw, rfl⟩
  exact hK k hk w hw

namespace Hyp

variable {G : Subgroup (W ≃ₗ[ZMod 2] W)} {Δ : Set W}
  {F : W → Submodule (ZMod 2) (Dual (ZMod 2) W)}

omit [Finite W] in
theorem grpPY_le (hH : Hyp G Δ F) (P : Submodule (ZMod 2) W) (y : W) : grpPY Δ F P y ≤ G :=
  (Subgroup.closure_le G).2 (by rintro t ⟨v, hv, -, ψ, hψ, h, rfl⟩; exact hH.mem v hv ψ hψ h)

theorem isFull_span_pair (hH : Hyp G Δ F) {x y : W} (hx : x ∈ Δ) (hy : y ∈ Δ)
    (hyx : y ∉ C F x) : IsFull Δ F (Submodule.span (ZMod 2) {x, y}) := by
  have hxy : x ∉ C F y := hH.not_mem_C_comm hx hy hyx
  have hz : x + y ∈ Δ := hH.add_mem hx hy hyx
  have hxz : x ∉ C F (x + y) := hH.not_mem_C_add hx hy hyx
  have hzx : x + y ∉ C F x := fun h => hyx (by
    have := (C F x).sub_mem h (hH.self_mem_C hx)
    rwa [add_sub_cancel_left] at this)
  have hzy : x + y ∉ C F y := fun h => hxy (by
    have := (C F y).sub_mem h (hH.self_mem_C hy)
    rwa [add_sub_cancel_right] at this)
  have hyz : y ∉ C F (x + y) := fun h => hxz (by
    have := (C F (x + y)).sub_mem (hH.self_mem_C hz) h
    rwa [add_sub_cancel_right] at this)
  have key : ∀ v ∈ Δ, v ∈ Submodule.span (ZMod 2) {x, y} →
      (∀ w, (w = x ∨ w = y ∨ w = x + y) → w ≠ v → w ∉ C F v) →
      C F v ⊓ Submodule.span (ZMod 2) {x, y} = Submodule.span (ZMod 2) {v} := by
    intro v hv hvP hoth
    refine le_antisymm ?_ ?_
    · rintro w ⟨hwC, hwP⟩
      rcases mem_span_pair_two.1 hwP with h0 | hw
      · rw [h0]
        exact Submodule.zero_mem _
      · by_cases hwv : w = v
        · rw [hwv]
          exact Submodule.mem_span_singleton_self v
        · exact absurd hwC (hoth w hw hwv)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact ⟨hH.self_mem_C hv, hvP⟩
  intro v hvP hv0
  rcases mem_span_pair_two.1 hvP with h0 | h | h | h
  · exact absurd h0 hv0
  all_goals rw [h] at hvP ⊢
  · refine ⟨hx, key _ hx hvP fun w hw hne => ?_⟩
    rcases hw with h' | h' | h' <;> rw [h'] at hne ⊢
    · exact absurd rfl hne
    · exact hyx
    · exact hzx
  · refine ⟨hy, key _ hy hvP fun w hw hne => ?_⟩
    rcases hw with h' | h' | h' <;> rw [h'] at hne ⊢
    · exact hxy
    · exact absurd rfl hne
    · exact hzy
  · refine ⟨hz, key _ hz hvP fun w hw hne => ?_⟩
    rcases hw with h' | h' | h' <;> rw [h'] at hne ⊢
    · exact hxz
    · exact hyz
    · exact absurd rfl hne

omit [Finite W] in
theorem exists_apply_eq_of_isFull (hH : Hyp G Δ F) {P : Submodule (ZMod 2) W}
    (hP : IsFull Δ F P) {u q : W} (hu : u ∈ P) (hq : q ∈ P) (hu0 : u ≠ 0) (hq0 : q ≠ 0)
    (huq : u ≠ q) : u + q ∈ Δ ∧ u + q ∈ P ∧ ∃ ψ ∈ F (u + q), ∃ h : ψ (u + q) = 0,
      LinearEquiv.transvection h u = q := by
  have hv : u + q ∈ P := P.add_mem hu hq
  have hv0 : u + q ≠ 0 := fun h => huq (by rwa [two_add_eq_iff, zero_add] at h)
  obtain ⟨hvΔ, hvC⟩ := hP _ hv hv0
  have hun : u ∉ C F (u + q) := by
    intro h
    have hmem : u ∈ Submodule.span (ZMod 2) {u + q} := hvC ▸ ⟨h, hu⟩
    rcases mem_span_singleton_iff_two.1 hmem with h1 | h1
    · exact hu0 h1
    · exact hq0 (by simpa using h1.symm)
  obtain ⟨ψ, hψ, hψu⟩ := exists_eq_one_of_not_mem_C hun
  refine ⟨hvΔ, hv, ψ, hψ, hH.apply_self _ hvΔ ψ hψ, ?_⟩
  rw [transvection_apply, hψu, one_smul, ← add_assoc, two_add_self, zero_add]

omit [Finite W] in
theorem transvection_mem_grpPY_of_mem (hH : Hyp G Δ F) {P : Submodule (ZMod 2) W}
    (hP : IsFull Δ F P) {x : W} (hxP : x ∈ P) (hx0 : x ≠ 0) {φ : Dual (ZMod 2) W}
    (hφ : φ ∈ F x) (hφP : ∀ u ∈ P, φ u = 0) (y : W) {q : W} (hq : q ∈ P) :
    LinearEquiv.transvection (hφP q hq) ∈ grpPY Δ F P y := by
  have hx : x ∈ Δ := (hP x hxP hx0).1
  have hφx : φ x = 0 := hH.apply_self x hx φ hφ
  by_cases hq0 : q = 0
  · rw [transvection_congr rfl hq0 (hφP q hq) (by rw [map_zero]), transvection_eq_one]
    exact one_mem _
  by_cases hxq : x = q
  · rw [← transvection_congr rfl hxq hφx (hφP q hq)]
    exact transvection_mem_grpPY hx (Or.inl hxP) hφ hφx
  obtain ⟨hvΔ, hvP, ψ, hψ, h, hk⟩ := hH.exists_apply_eq_of_isFull hP hxP hq hx0 hq0 hxq
  have hk' : LinearEquiv.transvection h ∈ grpPY Δ F P y :=
    transvection_mem_grpPY hvΔ (Or.inl hvP) hψ h
  have hmem : LinearEquiv.transvection h * LinearEquiv.transvection hφx *
      (LinearEquiv.transvection h)⁻¹ ∈ grpPY Δ F P y :=
    mul_mem (mul_mem hk' (transvection_mem_grpPY hx (Or.inl hxP) hφ hφx)) (inv_mem hk')
  rw [mul_transvection_mul_inv _ hφx (transvection_comp_apply_eq_zero _ hφx)] at hmem
  have hf : φ ∘ₗ ((LinearEquiv.transvection h).symm : W →ₗ[ZMod 2] W) = φ := by
    ext w
    show φ ((LinearEquiv.transvection h).symm w) = φ w
    rw [show (LinearEquiv.transvection h).symm = LinearEquiv.transvection h from
      transvection_inv h, transvection_apply, map_add, map_smul, hφP _ hvP, smul_zero, add_zero]
  rwa [transvection_congr hf hk _ (hφP q hq)] at hmem

theorem isFull_sup (hH : Hyp G Δ F) {P : Submodule (ZMod 2) W} (hP : IsFull Δ F P)
    {x : W} (hxP : x ∈ P) (hx0 : x ≠ 0) {φ : Dual (ZMod 2) W} (hφ : φ ∈ F x)
    (hφP : ∀ u ∈ P, φ u = 0) {y : W} (hy : y ∈ Δ) (hφy : φ y = 1) :
    IsFull Δ F (P ⊔ Submodule.span (ZMod 2) {y}) := by
  set I := P ⊔ Submodule.span (ZMod 2) {y} with hI
  have hx : x ∈ Δ := (hP x hxP hx0).1
  have hφx : φ x = 0 := hH.apply_self x hx φ hφ
  have hyx : y ∉ C F x := fun h => by
    rw [mem_C.1 h φ hφ] at hφy
    exact zero_ne_one hφy
  obtain ⟨ψ₁, hψ₁, hψ₁x⟩ := exists_eq_one_of_not_mem_C (hH.not_mem_C_comm hx hy hyx)
  have hψ₁y : ψ₁ y = 0 := hH.apply_self y hy ψ₁ hψ₁
  have hk₁ : LinearEquiv.transvection hψ₁y ∈ grpPY Δ F P y :=
    transvection_mem_grpPY hy (Or.inr rfl) hψ₁ hψ₁y
  have hk₁x : LinearEquiv.transvection hψ₁y x = x + y := by
    rw [transvection_apply, hψ₁x, one_smul]
  have hxI : x ∈ I := Submodule.mem_sup_left hxP
  have hyI : y ∈ I := Submodule.mem_sup_right (Submodule.mem_span_singleton_self y)
  have hdec : ∀ w ∈ I, ∃ p ∈ P, ∃ c : ZMod 2, w = p + c • y := by
    intro w hw
    obtain ⟨p, hp, z, hz, rfl⟩ := Submodule.mem_sup.1 hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
    exact ⟨p, hp, c, rfl⟩
  have hφI : ∀ p ∈ P, ∀ c : ZMod 2, φ (p + c • y) = c := by
    intro p hp c
    rw [map_add, map_smul, hφP p hp, hφy, smul_eq_mul, mul_one, zero_add]
  have hirr : G11.IsIrr (grpPY Δ F P y) I := by
    refine ⟨invariant_grpPY, bot_lt_iff_ne_bot.2 fun h => hx0 ?_, ?_⟩
    · rw [h] at hxI
      exact (Submodule.mem_bot _).1 hxI
    intro J hJ _ hJI
    by_cases hJP : ∃ u ∈ J, u ∈ P ∧ u ≠ 0
    · right
      obtain ⟨u, huJ, huP, hu0⟩ := hJP
      have hPJ : P ≤ J := by
        intro q hq
        by_cases hq0 : q = 0
        · rw [hq0]
          exact J.zero_mem
        by_cases huq : u = q
        · rw [← huq]
          exact huJ
        obtain ⟨hvΔ, hvP, ψ, hψ, h, hk⟩ := hH.exists_apply_eq_of_isFull hP huP hq hu0 hq0 huq
        rw [← hk]
        exact hJ _ (transvection_mem_grpPY hvΔ (Or.inl hvP) hψ h) u huJ
      have hyJ : y ∈ J := by
        have h1 := hJ _ hk₁ x (hPJ hxP)
        rw [hk₁x] at h1
        have := J.sub_mem h1 (hPJ hxP)
        rwa [add_sub_cancel_left] at this
      exact le_antisymm hJI (sup_le hPJ ((Submodule.span_singleton_le_iff_mem _ _).2 hyJ))
    · left
      refine (Submodule.eq_bot_iff J).2 fun j hj => ?_
      by_contra hj0
      obtain ⟨p, hp, c, rfl⟩ := hdec j (hJI hj)
      have hc : c = 1 := by
        rcases zmod_two_eq_zero_or_one c with h0 | h1
        · exfalso
          rw [h0, zero_smul, add_zero] at hj hj0
          exact hJP ⟨p, hj, hp, hj0⟩
        · exact h1
      subst hc
      have h1 := hJ _ (transvection_mem_grpPY hx (Or.inl hxP) hφ hφx) _ hj
      rw [transvection_apply, hφI p hp 1] at h1
      have hxJ := J.sub_mem h1 hj
      rw [add_sub_cancel_left, one_smul] at hxJ
      exact hJP ⟨x, hxJ, hxP, hx0⟩
  have hα : φ.domRestrict I ≠ 0 := fun h => by
    have := LinearMap.congr_fun h ⟨y, hyI⟩
    rw [LinearMap.domRestrict_apply, LinearMap.zero_apply, hφy] at this
    exact one_ne_zero this
  have hAut : G11.AutAll (grpPY Δ F P y) I := by
    refine G11.autAll_of_fullTransvections _ I hirr (φ.domRestrict I) hα fun a ha => ?_
    obtain ⟨p, hp, c, hpc⟩ := hdec a a.2
    have hc : c = 0 := by
      have h0 : φ (a : W) = 0 := ha
      rwa [hpc, hφI p hp c] at h0
    have hap : (a : W) ∈ P := by
      rw [hpc, hc, zero_smul, add_zero]
      exact hp
    exact ⟨_, hH.transvection_mem_grpPY_of_mem hP hxP hx0 hφ hφP y hap, fun u => rfl⟩
  have hHG := hH.grpPY_le P y
  have hCx : C F x ⊓ I = Submodule.span (ZMod 2) {x} := by
    refine le_antisymm ?_ ?_
    · rintro u ⟨huC, huI⟩
      by_contra hu
      have hu' : (⟨u, huI⟩ : I) ∉ Submodule.span (ZMod 2) {(⟨x, hxI⟩ : I)} := by
        intro h
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h
        exact hu (Submodule.mem_span_singleton.2 ⟨c, congrArg Subtype.val hc⟩)
      obtain ⟨ψ', hψ'x, hψ'u⟩ := exists_dual_eq_one_of_notMem hu'
      have hψ'0 : ψ' ≠ 0 := fun h => by
        rw [h, LinearMap.zero_apply] at hψ'u
        exact zero_ne_one hψ'u
      obtain ⟨g, hgx, hg⟩ := exists_comp_eq_of_apply_eq_zero hα hψ'0
        (e₀ := ⟨x, hxI⟩) hφx (hψ'x _ (Submodule.mem_span_singleton_self _))
      obtain ⟨k, hk, hkg⟩ := hAut g
      have hkx : k x = x := by
        have := hkg ⟨x, hxI⟩
        rw [hgx] at this
        exact this
      have hφk := (hH.mem_F_map k (hHG hk) x hx φ).1 (by rw [hkx]; exact hφ)
      have h1 := mem_C.1 huC _ hφk
      have h2 := LinearMap.congr_fun hg ⟨u, huI⟩
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.domRestrict_apply,
        ← hkg ⟨u, huI⟩, hψ'u] at h2
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, h2] at h1
      exact one_ne_zero h1
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact ⟨hH.self_mem_C hx, hxI⟩
  intro v hvI hv0
  obtain ⟨f, d, hfd, hgxv⟩ := exists_transvection_apply_eq (a := (⟨x, hxI⟩ : I))
    (b := ⟨v, hvI⟩) (fun h => hx0 (congrArg Subtype.val h)) (fun h => hv0 (congrArg Subtype.val h))
  obtain ⟨k, hk, hkg⟩ := hAut (LinearEquiv.transvection hfd)
  have hkx : k x = v := by
    have := hkg ⟨x, hxI⟩
    rw [hgxv] at this
    exact this
  refine ⟨hkx ▸ hH.map_mem k (hHG hk) x hx, ?_⟩
  rw [← hkx, hH.C_map (hHG hk) hx, ← map_eq_of_invariant hirr.1 hk,
    ← Submodule.map_inf _ k.injective, hCx, Submodule.map_span, Set.image_singleton]
  rfl

end Hyp

end CFSG.Quasithin.G31
