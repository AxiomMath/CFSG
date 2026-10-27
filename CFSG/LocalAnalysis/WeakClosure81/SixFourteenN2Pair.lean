module

public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenN2F4Module

public noncomputable section
public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open CFSG.GroupTheory.GL52 (F4 F4poly F4root_ne_zero)

section LinearAlgebra

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem line_inf_eq_bot {L M : LineOf (K := K) (V := V)} (hLM : L ≠ M) :
    L.1 ⊓ M.1 = ⊥ := by
  by_contra hne
  have hLatom : IsAtom L.1 := Submodule.isAtom_iff_finrank_eq_one.mpr L.2
  have hMatom : IsAtom M.1 := Submodule.isAtom_iff_finrank_eq_one.mpr M.2
  have hL : L.1 ⊓ M.1 = L.1 := (hLatom.le_iff_eq hne).mp inf_le_left
  have hM : L.1 ⊓ M.1 = M.1 := (hMatom.le_iff_eq hne).mp inf_le_right
  apply hLM
  exact Subtype.ext (hL.symm.trans hM)

theorem line_sup_eq_top (hV : Module.finrank K V = 2)
    {L M : LineOf (K := K) (V := V)} (hLM : L ≠ M) :
    L.1 ⊔ M.1 = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  have hfr := Submodule.finrank_sup_add_finrank_inf_eq L.1 M.1
  rw [line_inf_eq_bot hLM, finrank_bot, add_zero, L.2, M.2] at hfr
  rw [hfr, hV]

theorem exists_injective_pair_scalar_of_le {G : Type*} [Group G]
    (hV : Module.finrank K V = 2) {L M : LineOf (K := K) (V := V)} (hLM : L ≠ M)
    (S : Subgroup G) (ρ : G →* (V ≃ₗ[K] V)) (hρ : Function.Injective ρ)
    (hL : ∀ g ∈ S, lineMap (ρ g) L = L) (hM : ∀ g ∈ S, lineMap (ρ g) M = M) :
    ∃ f : ↥S →* Kˣ × Kˣ, Function.Injective f ∧
      (∀ (g : ↥S) (x : V), x ∈ L.1 → ρ g.val x = ((f g).1 : K) • x) ∧
      (∀ (g : ↥S) (y : V), y ∈ M.1 → ρ g.val y = ((f g).2 : K) • y) := by
  classical
  obtain ⟨l, hl⟩ :=
    Module.finrank_pos_iff_exists_ne_zero.mp
      (by rw [L.2]; norm_num : 0 < Module.finrank K L.1)
  obtain ⟨m, hm⟩ :=
    Module.finrank_pos_iff_exists_ne_zero.mp
      (by rw [M.2]; norm_num : 0 < Module.finrank K M.1)
  let lV : V := (l : V)
  let mV : V := (m : V)
  have hlV : lV ≠ 0 := fun h => hl (Subtype.ext (show (l : V) = 0 from h))
  have hmV : mV ≠ 0 := fun h => hm (Subtype.ext (show (m : V) = 0 from h))
  have hspanL : L.1 = Submodule.span K {lV} :=
    eq_span_singleton_of_mem_of_finrank_eq_one L.2 (show lV ∈ L.1 from l.2) hlV
  have hspanM : M.1 = Submodule.span K {mV} :=
    eq_span_singleton_of_mem_of_finrank_eq_one M.2 (show mV ∈ M.1 from m.2) hmV
  have hsp : Submodule.span K {lV} ⊔ Submodule.span K {mV} = ⊤ := by
    rw [← hspanL, ← hspanM]
    exact line_sup_eq_top hV hLM
  have hmemL : ∀ g : ↥S, ρ g.val lV ∈ Submodule.span K {lV} := by
    intro g
    rw [← hspanL]
    have h := congrArg Subtype.val (hL g.val g.2)
    rw [← h]
    exact Submodule.mem_map_of_mem (f := (ρ g.val : V →ₗ[K] V))
      (show lV ∈ L.1 from l.2)
  have hmemM : ∀ g : ↥S, ρ g.val mV ∈ Submodule.span K {mV} := by
    intro g
    rw [← hspanM]
    have h := congrArg Subtype.val (hM g.val g.2)
    rw [← h]
    exact Submodule.mem_map_of_mem (f := (ρ g.val : V →ₗ[K] V))
      (show mV ∈ M.1 from m.2)
  let cL : ↥S → K := fun g =>
    (Submodule.mem_span_singleton.mp (hmemL g)).choose
  have hcL : ∀ g : ↥S, cL g • lV = ρ g.val lV := fun g =>
    (Submodule.mem_span_singleton.mp (hmemL g)).choose_spec
  let cM : ↥S → K := fun g =>
    (Submodule.mem_span_singleton.mp (hmemM g)).choose
  have hcM : ∀ g : ↥S, cM g • mV = ρ g.val mV := fun g =>
    (Submodule.mem_span_singleton.mp (hmemM g)).choose_spec
  have hcL_ne : ∀ g : ↥S, cL g ≠ 0 := by
    intro g hc
    have h0 : ρ g.val lV = 0 := by rw [← hcL g, hc, zero_smul]
    have h0' : ρ g.val lV = ρ g.val 0 := by simpa using h0
    exact hlV ((ρ g.val).injective h0')
  have hcM_ne : ∀ g : ↥S, cM g ≠ 0 := by
    intro g hc
    have h0 : ρ g.val mV = 0 := by rw [← hcM g, hc, zero_smul]
    have h0' : ρ g.val mV = ρ g.val 0 := by simpa using h0
    exact hmV ((ρ g.val).injective h0')
  have hsmulL : ∀ {c c' : K}, c • lV = c' • lV → c = c' := by
    intro c c' h
    have hsub : (c - c') • lV = 0 := by rw [sub_smul, h, sub_self]
    rcases smul_eq_zero.mp hsub with h0 | h0
    · exact sub_eq_zero.mp h0
    · exact absurd h0 hlV
  have hsmulM : ∀ {c c' : K}, c • mV = c' • mV → c = c' := by
    intro c c' h
    have hsub : (c - c') • mV = 0 := by rw [sub_smul, h, sub_self]
    rcases smul_eq_zero.mp hsub with h0 | h0
    · exact sub_eq_zero.mp h0
    · exact absurd h0 hmV
  have hcL_one : cL 1 = 1 := by
    apply hsmulL
    rw [hcL 1]
    simp
  have hcM_one : cM 1 = 1 := by
    apply hsmulM
    rw [hcM 1]
    simp
  have hcL_mul : ∀ g₁ g₂ : ↥S, cL (g₁ * g₂) = cL g₁ * cL g₂ := by
    intro g₁ g₂
    apply hsmulL
    calc cL (g₁ * g₂) • lV = ρ (g₁ * g₂).val lV := hcL (g₁ * g₂)
      _ = ρ g₁.val (ρ g₂.val lV) := by
            rw [Subgroup.coe_mul, map_mul]
            rfl
      _ = ρ g₁.val (cL g₂ • lV) := by rw [hcL g₂]
      _ = cL g₂ • ρ g₁.val lV := map_smul _ _ _
      _ = cL g₂ • (cL g₁ • lV) := by rw [hcL g₁]
      _ = (cL g₁ * cL g₂) • lV := by rw [mul_comm, mul_smul]
  have hcM_mul : ∀ g₁ g₂ : ↥S, cM (g₁ * g₂) = cM g₁ * cM g₂ := by
    intro g₁ g₂
    apply hsmulM
    calc cM (g₁ * g₂) • mV = ρ (g₁ * g₂).val mV := hcM (g₁ * g₂)
      _ = ρ g₁.val (ρ g₂.val mV) := by
            rw [Subgroup.coe_mul, map_mul]
            rfl
      _ = ρ g₁.val (cM g₂ • mV) := by rw [hcM g₂]
      _ = cM g₂ • ρ g₁.val mV := map_smul _ _ _
      _ = cM g₂ • (cM g₁ • mV) := by rw [hcM g₁]
      _ = (cM g₁ * cM g₂) • mV := by rw [mul_comm, mul_smul]
  let cLu : ↥S → Kˣ := fun g => Units.mk0 (cL g) (hcL_ne g)
  let cMu : ↥S → Kˣ := fun g => Units.mk0 (cM g) (hcM_ne g)
  let f : ↥S →* Kˣ × Kˣ :=
    { toFun := fun g => (cLu g, cMu g)
      map_one' := by
        apply Prod.ext
        · apply Units.ext
          simp [cLu, hcL_one]
        · apply Units.ext
          simp [cMu, hcM_one]
      map_mul' := by
        intro g₁ g₂
        apply Prod.ext
        · apply Units.ext
          simp [cLu, hcL_mul]
        · apply Units.ext
          simp [cMu, hcM_mul] }
  have hfinj : Function.Injective f := by
    intro g₁ g₂ hEq
    have hcLval : cL g₁ = cL g₂ := by
      have h := congrArg (fun p : Kˣ × Kˣ => (p.1 : K)) hEq
      simpa [f, cLu, Units.val_mk0] using h
    have hcMval : cM g₁ = cM g₂ := by
      have h := congrArg (fun p : Kˣ × Kˣ => (p.2 : K)) hEq
      simpa [f, cMu, Units.val_mk0] using h
    have heqρ : ρ g₁.val = ρ g₂.val := by
      apply LinearEquiv.ext
      intro v
      have hv : v ∈ Submodule.span K {lV} ⊔ Submodule.span K {mV} := by
        rw [hsp]; exact Submodule.mem_top
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
      obtain ⟨ca, hca⟩ := Submodule.mem_span_singleton.mp ha
      obtain ⟨cb, hcb⟩ := Submodule.mem_span_singleton.mp hb
      have h1l : ρ g₁.val lV = ρ g₂.val lV := by
        rw [← hcL g₁, ← hcL g₂, hcLval]
      have h1m : ρ g₁.val mV = ρ g₂.val mV := by
        rw [← hcM g₁, ← hcM g₂, hcMval]
      calc ρ g₁.val (a + b) = ρ g₁.val a + ρ g₁.val b := map_add _ _ _
        _ = ρ g₁.val (ca • lV) + ρ g₁.val (cb • mV) := by rw [hca, hcb]
        _ = ca • ρ g₁.val lV + cb • ρ g₁.val mV := by rw [map_smul, map_smul]
        _ = ca • ρ g₂.val lV + cb • ρ g₂.val mV := by rw [h1l, h1m]
        _ = ρ g₂.val (ca • lV) + ρ g₂.val (cb • mV) := by rw [map_smul, map_smul]
        _ = ρ g₂.val (a + b) := by rw [hca, hcb, map_add]
    exact Subtype.ext (hρ heqρ)
  refine ⟨f, hfinj, ?_, ?_⟩
  · intro g x hx
    have hx' : x ∈ Submodule.span K {lV} := by rwa [← hspanL]
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx'
    calc ρ g.val (a • lV) = a • ρ g.val lV := map_smul _ _ _
      _ = a • (cL g • lV) := by rw [hcL g]
      _ = cL g • (a • lV) := smul_comm a (cL g) lV
      _ = ((f g).1 : K) • (a • lV) := by simp [f, cLu, Units.val_mk0]
  · intro g y hy
    have hy' : y ∈ Submodule.span K {mV} := by rwa [← hspanM]
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy'
    calc ρ g.val (a • mV) = a • ρ g.val mV := map_smul _ _ _
      _ = a • (cM g • mV) := by rw [hcM g]
      _ = cM g • (a • mV) := smul_comm a (cM g) mV
      _ = ((f g).2 : K) • (a • mV) := by simp [f, cMu, Units.val_mk0]

theorem exists_smul_one_of_commute_swap {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hV : Module.finrank K V = 2)
    {L M : LineOf (K := K) (V := V)} (hLM : L ≠ M) {h g : V ≃ₗ[K] V}
    (hL : lineMap h L = L) (hM : lineMap h M = M)
    (gL : lineMap g L = M) (gM : lineMap g M = L) (hcomm : h * g = g * h) :
    ∃ c : K, ∀ v : V, (h : V → V) v = c • v := by
  classical
  obtain ⟨l, hl⟩ :=
    Module.finrank_pos_iff_exists_ne_zero.mp
      (by rw [L.2]; norm_num : 0 < Module.finrank K L.1)
  let lv : V := (l : V)
  have hlv : lv ≠ 0 := fun hh => hl (Subtype.ext hh)
  have hspanL : L.1 = Submodule.span K {lv} :=
    eq_span_singleton_of_mem_of_finrank_eq_one L.2 (show lv ∈ L.1 from l.2) hlv
  have hmapL : L.1.map (h : V →ₗ[K] V) = L.1 := by
    have hh := congrArg Subtype.val hL
    simpa [lineMap] using hh
  have hhl : (h : V → V) lv ∈ L.1 := by
    rw [← hmapL]
    exact Submodule.mem_map_of_mem (f := (h : V →ₗ[K] V)) (show lv ∈ L.1 from l.2)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (by rwa [hspanL] at hhl)
  have hha : (h : V → V) lv = a • lv := ha.symm
  have hmapG : L.1.map (g : V →ₗ[K] V) = M.1 := by
    have hh := congrArg Subtype.val gL
    simpa [lineMap] using hh
  have hmM : (g : V → V) lv ∈ M.1 := by
    rw [← hmapG]
    exact Submodule.mem_map_of_mem (f := (g : V →ₗ[K] V)) (show lv ∈ L.1 from l.2)
  have hm0 : (g : V → V) lv ≠ 0 := by
    intro hh
    apply hlv
    apply g.injective
    simpa using hh
  have hspanM : M.1 = Submodule.span K {(g : V → V) lv} :=
    eq_span_singleton_of_mem_of_finrank_eq_one M.2 hmM hm0
  have hhm : (h : V → V) ((g : V → V) lv) = a • ((g : V → V) lv) := by
    calc (h : V → V) ((g : V → V) lv) = (g : V → V) ((h : V → V) lv) := by
          have hh := congrArg (fun e : V ≃ₗ[K] V => (e : V → V) lv) hcomm
          simpa using hh
      _ = (g : V → V) (a • lv) := by rw [hha]
      _ = a • (g : V → V) lv := map_smul g a lv
  refine ⟨a, fun v => ?_⟩
  have hv : v ∈ L.1 ⊔ M.1 := by
    rw [line_sup_eq_top hV hLM]
    exact Submodule.mem_top
  rw [hspanL, hspanM] at hv
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨β, rfl⟩ := Submodule.mem_span_singleton.mp hy
  calc (h : V → V) (α • lv + β • ((g : V → V) lv))
      = α • ((h : V → V) lv) + β • ((h : V → V) ((g : V → V) lv)) := by
        rw [map_add, map_smul, map_smul]
    _ = α • (a • lv) + β • (a • ((g : V → V) lv)) := by rw [hha, hhm]
    _ = a • (α • lv) + a • (β • ((g : V → V) lv)) := by
        rw [smul_comm α a lv, smul_comm β a ((g : V → V) lv)]
    _ = a • (α • lv + β • ((g : V → V) lv)) := by rw [smul_add]

theorem lineMap_mul_apply {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (g₁ g₂ : V ≃ₗ[K] V) (L : LineOf (K := K) (V := V)) :
    lineMap (g₁ * g₂) L = lineMap g₁ (lineMap g₂ L) := by
  apply Subtype.ext
  rw [lineMap_apply, lineMap_apply, lineMap_apply]
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨g₂ w, ⟨w, hw, rfl⟩, rfl⟩
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, rfl⟩

theorem lineMap_one_apply {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (L : LineOf (K := K) (V := V)) :
    lineMap (1 : V ≃ₗ[K] V) L = L := by
  apply Subtype.ext
  rw [lineMap_apply]
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro hv
    exact ⟨v, hv, rfl⟩

end LinearAlgebra

section PairBranch

variable {W : Type*} [CommGroup W] [Finite W]

private theorem line_le_fixedSubmodule_of_map_eq {K V : Type*} [Field K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {g : V ≃ₗ[K] V} (hg2 : g * g = 1) {L : Submodule K V}
    (hL : Module.finrank K L = 1) (hmap : L.map (g : V →ₗ[K] V) = L) :
    L ≤ fixedSubmodule (g : V →ₗ[K] V) := by
  intro x hx
  rw [mem_fixedSubmodule]
  by_cases hx0 : x = 0
  · rw [hx0, map_zero]
  · have hgxL : g x ∈ L := by
      rw [← hmap]
      exact Submodule.mem_map_of_mem (f := (g : V →ₗ[K] V)) hx
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one (K := K) (V := ↥L) hL
      (x := ⟨x, hx⟩) (by simpa using hx0) ⟨g x, hgxL⟩
    have hgxl : g x = c • x := by
      have := congrArg Subtype.val hc
      simpa using this.symm
    have hg2x : g (g x) = x := by
      have h := congrArg (fun e : V ≃ₗ[K] V => e x) hg2
      simpa using h
    have hc2 : c ^ 2 = 1 := by
      have h1 : (c ^ 2) • x = x := by
        rw [pow_two, mul_smul]
        calc c • (c • x) = c • g x := by rw [← hgxl]
          _ = g (c • x) := (map_smul g c x).symm
          _ = g (g x) := by rw [← hgxl]
          _ = x := hg2x
      have hsub : (c ^ 2 - 1) • x = 0 := by rw [sub_smul, h1, one_smul, sub_self]
      rcases smul_eq_zero.mp hsub with h0 | h0
      · exact sub_eq_zero.mp h0
      · exact absurd h0 hx0
    calc (g : V → V) x = c • x := hgxl
      _ = x := by rw [eq_one_of_sq_eq_one hc2, one_smul]

theorem sixfourteen_n2_pair_orders {W : Type} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hx_ord3 : orderOf x = 3)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16)
    {G X H D : Subgroup (MulAut W)} {s : MulAut W} {Y : Subgroup W}
    (hH : H = G ⊓ Subgroup.centralizer (X : Set (MulAut W)))
    (hXG : X ≤ G) (hXnorm : ∀ g ∈ G, ∀ y ∈ X, g * y * g⁻¹ ∈ X)
    (hxgen : X = Subgroup.zpowers x)
    (hsG : s ∈ G) (hs_ord2 : orderOf s = 2)
    (hs_not_cent : s ∉ Subgroup.centralizer (X : Set (MulAut W)))
    (hirr : ∀ Z : Subgroup W, (∀ g ∈ G, ∀ z ∈ Z, g z ∈ Z) → Z = ⊥ ∨ Z = ⊤)
    (hD : D ≤ G) (hDCX : ∀ d ∈ D, ∀ y ∈ X, d * y = y * d)
    (hDs : ∀ d ∈ D, d * s = s * d)
    (hElem : CFSG.Quasithin.IsElemAbelian2 D) (hDcard : Nat.card D = 2)
    (hYD : Y ≤ fixV D)
    (hYinv : ∀ a ∈ X, ∀ y ∈ Y, a y ∈ Y) (hYcard : Nat.card Y = 4)
    (hcommH : ∀ h ∈ H, h * x = x * h)
    (hpair : letI := galoisModule hw2 x hx3 hfix;
      ∃ S : Set (LineOf (K := GaloisField 2 2) (V := Additive W)),
        S.ncard = 2 ∧ S.Nonempty ∧ S ≠ Set.univ ∧
        (∀ h : ↥H, S.image (fun L => lineMap (HLinHom hw2 x hx3 hfix H hcommH h) L) = S)) :
    letI := galoisModule hw2 x hx3 hfix
    Nat.card H = 18 ∧ ∃ (L M : LineOf (K := GaloisField 2 2) (V := Additive W))
      (H0 : Subgroup ↥H) (d : ↥H), L ≠ M ∧ (X.subgroupOf H) ≤ H0 ∧ H0.index = 2 ∧
      Nat.card H0 = 9 ∧ (∀ a ∈ H0, ∀ b ∈ H0, a * b = b * a) ∧
      (∀ h : ↥H, h ∈ H0 ↔ lineMap (HLinHom hw2 x hx3 hfix H hcommH h) L = L ∧
        lineMap (HLinHom hw2 x hx3 hfix H hcommH h) M = M) ∧
      (d : MulAut W) ∈ D ∧ d * d = 1 ∧ d ∉ H0 ∧
      (∀ b : ↥H, b ∈ H0 ∨ b * d⁻¹ ∈ H0) ∧
      lineMap (HLinHom hw2 x hx3 hfix H hcommH d) L = M ∧
      lineMap (HLinHom hw2 x hx3 hfix H hcommH d) M = L ∧
      fixedSubmodule (hGaloisLinearEquiv hw2 x hx3 hfix (d : MulAut W)
        (hcommH (d : MulAut W) d.2)).toLinearMap =
        YSubmodule hw2 x hx3 hfix (by rw [hxgen]; exact Subgroup.mem_zpowers x) hYinv := by
  letI := galoisModule hw2 x hx3 hfix
  obtain ⟨S, hScard, hSne, hSproper, hSinv⟩ := hpair
  obtain ⟨L, M, hLM, hSeq⟩ := Set.ncard_eq_two.mp hScard
  letI : MulAction ↥H (LineOf (K := GaloisField 2 2) (V := Additive W)) :=
  { smul := fun h L => lineMap (HLinHom hw2 x hx3 hfix H hcommH h) L
    one_smul := by
      intro K
      change lineMap (HLinHom hw2 x hx3 hfix H hcommH 1) K = K
      rw [map_one]
      ext v
      constructor
      · rintro ⟨w, hw, rfl⟩
        simpa using hw
      · intro hv
        exact ⟨v, hv, rfl⟩
    mul_smul := by
      intro h₁ h₂ K
      change lineMap (HLinHom hw2 x hx3 hfix H hcommH (h₁ * h₂)) K =
        lineMap (HLinHom hw2 x hx3 hfix H hcommH h₁)
          (lineMap (HLinHom hw2 x hx3 hfix H hcommH h₂) K)
      rw [map_mul]
      ext v
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨(HLinHom hw2 x hx3 hfix H hcommH h₂) w, ⟨w, hw, rfl⟩, rfl⟩
      · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
        exact ⟨u, hu, rfl⟩ }
  let H0 : Subgroup ↥H := MulAction.stabilizer ↥H L ⊓ MulAction.stabilizer ↥H M
  have hH0mem : ∀ h : ↥H, h ∈ H0 ↔ h • L = L ∧ h • M = M := by
    intro h
    simp [H0]
  have hsmul_def : ∀ (h : ↥H) (K : LineOf (K := GaloisField 2 2) (V := Additive W)),
      h • K = lineMap (HLinHom hw2 x hx3 hfix H hcommH h) K := fun h K => rfl
  have hmemS : ∀ (g : ↥H) (K : LineOf (K := GaloisField 2 2) (V := Additive W)),
      K ∈ S → g • K ∈ S := by
    intro g K hK
    have hmem : g • K ∈ S.image
        (fun L => lineMap (HLinHom hw2 x hx3 hfix H hcommH g) L) :=
      Set.mem_image_of_mem _ hK
    rwa [hSinv g] at hmem
  have hdich : ∀ g : ↥H, (g • L = L ∧ g • M = M) ∨ (g • L = M ∧ g • M = L) := by
    intro g
    have hL' : g • L ∈ S :=
      hmemS g L (by rw [hSeq]; exact Set.mem_insert_iff.mpr (Or.inl rfl))
    have hM' : g • M ∈ S :=
      hmemS g M (by rw [hSeq]; exact Set.mem_insert_iff.mpr (Or.inr rfl))
    rw [hSeq, Set.mem_insert_iff, Set.mem_singleton_iff] at hL' hM'
    rcases hL' with hL' | hL'
    · left
      refine ⟨hL', ?_⟩
      rcases hM' with hM' | hM'
      · exfalso
        have hEq : g • M = g • L := hM'.trans hL'.symm
        exact hLM (MulAction.injective g hEq).symm
      · exact hM'
    · right
      refine ⟨hL', ?_⟩
      rcases hM' with hM' | hM'
      · exact hM'
      · exfalso
        have hEq : g • M = g • L := hM'.trans hL'.symm
        exact hLM (MulAction.injective g hEq).symm
  have hxX : x ∈ X := by rw [hxgen]; exact Subgroup.mem_zpowers x
  have hXcard : Nat.card X = 3 := by rw [hxgen, Nat.card_zpowers, hx_ord3]
  have hXH : X ≤ H := by
    rw [hH]
    exact le_inf_centralizer_self hXG hXcard
  have hXsubcard : Nat.card (X.subgroupOf H) = 3 := by
    have h := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv
    rw [hXcard] at h
    exact h
  have hXleH0 : X.subgroupOf H ≤ H0 := by
    intro a ha
    rw [hH0mem]
    by_contra hcon
    have hswap : a • L = M ∧ a • M = L := by
      rcases hdich a with h | h
      · exact absurd h hcon
      · exact h
    have ha3 : a ^ 3 = 1 := by
      apply Subtype.ext
      have hmem : (a : MulAut W) ∈ X := ha
      have hdvd : orderOf (a : MulAut W) ∣ Nat.card X := Subgroup.orderOf_dvd_natCard X hmem
      rw [hXcard] at hdvd
      have h := orderOf_dvd_iff_pow_eq_one.mp hdvd
      simpa using h
    have hA2L : (a ^ 2) • L = L := by
      rw [pow_two, mul_smul, hswap.1, hswap.2]
    have hinvL : (a ^ 2)⁻¹ • L = L := by
      have h := inv_smul_smul (a ^ 2) L
      rwa [hA2L] at h
    have haeq : a = (a ^ 2)⁻¹ := by
      have h : a * a ^ 2 = 1 := by rw [← pow_succ', ha3]
      exact eq_inv_of_mul_eq_one_left h
    rw [haeq, hinvL] at hswap
    exact hLM hswap.1
  obtain ⟨d0, hd0D, hd0sq, hd0ne⟩ := exists_involution_of_card_two hDcard hElem
  have hd0H : d0 ∈ H := by
    rw [hH]
    refine Subgroup.mem_inf.mpr ⟨hD hd0D, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hDCX d0 hd0D y hy).symm
  let d : ↥H := ⟨d0, hd0H⟩
  have hd_d : d * d = 1 := by
    apply Subtype.ext
    simpa [d] using hd0sq
  have hd0comm : d0 * x = x * d0 := hcommH d0 hd0H
  have hKcard : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hVf : Module.finrank (GaloisField 2 2) (Additive W) = 2 :=
    finrank_galoisModule hw2 x hx3 hfix hW
  have hYsubcard : Nat.card (YSubmodule hw2 x hx3 hfix hxX hYinv) = 4 :=
    card_YSubmodule hw2 x hx3 hfix hxX hYinv hYcard
  have hfixsub : fixedSubmodule (hGaloisLinearEquiv hw2 x hx3 hfix d0 hd0comm).toLinearMap =
      YSubmodule hw2 x hx3 hfix hxX hYinv :=
    fixedSubmodule_eq_of_card_four hKcard hVf hYsubcard
      (hGaloisLinearEquiv hw2 x hx3 hfix d0 hd0comm)
      (YSubmodule_le_fixedSubmodule hw2 x hx3 hfix hxX hYinv hd0D hYD hd0comm)
      (hGaloisLinearEquiv_ne_one hw2 x hx3 hfix hd0comm hd0ne)
  have hdgal2 : hGaloisLinearEquiv hw2 x hx3 hfix d0 hd0comm *
      hGaloisLinearEquiv hw2 x hx3 hfix d0 hd0comm = 1 :=
    hGaloisLinearEquiv_mul_self hw2 x hx3 hfix H hcommH hd0H hd0sq
  have hdline : ∀ K : LineOf (K := GaloisField 2 2) (V := Additive W),
      d • K = K → K.1 ≤ YSubmodule hw2 x hx3 hfix hxX hYinv := by
    intro K hK
    have hmap : K.1.map ((hGaloisLinearEquiv hw2 x hx3 hfix d0 hd0comm) : Additive W →ₗ[GaloisField 2 2] Additive W) = K.1 := by
      have h := congrArg Subtype.val hK
      rw [hsmul_def d K] at h
      rw [HLinHom_apply] at h
      exact h
    have h := line_le_fixedSubmodule_of_map_eq hdgal2 K.2 hmap
    rwa [hfixsub] at h
  have hdswap : d • L = M ∧ d • M = L := by
    rcases hdich d with hfixx | hswap
    · exfalso
      have hLle : L.1 ≤ YSubmodule hw2 x hx3 hfix hxX hYinv := hdline L hfixx.1
      have hMle : M.1 ≤ YSubmodule hw2 x hx3 hfix hxX hYinv := hdline M hfixx.2
      have hYfin1 : Module.finrank (GaloisField 2 2) (YSubmodule hw2 x hx3 hfix hxX hYinv) = 1 :=
        finrank_eq_one_of_card_four hYsubcard
      have hLeq : L.1 = YSubmodule hw2 x hx3 hfix hxX hYinv :=
        Submodule.eq_of_le_of_finrank_le hLle (by rw [hYfin1, L.2])
      have hMeq : M.1 = YSubmodule hw2 x hx3 hfix hxX hYinv :=
        Submodule.eq_of_le_of_finrank_le hMle (by rw [hYfin1, M.2])
      exact hLM (Subtype.ext (hLeq.trans hMeq.symm))
    · exact hswap
  have hdinvL : d⁻¹ • L = M := by
    calc d⁻¹ • L = d⁻¹ • (d • M) := by rw [hdswap.2]
      _ = (d⁻¹ * d) • M := (mul_smul d⁻¹ d M).symm
      _ = M := by rw [inv_mul_cancel, one_smul]
  have hdinvM : d⁻¹ • M = L := by
    calc d⁻¹ • M = d⁻¹ • (d • L) := by rw [hdswap.1]
      _ = (d⁻¹ * d) • L := (mul_smul d⁻¹ d L).symm
      _ = L := by rw [inv_mul_cancel, one_smul]
  have hdnot : d ∉ H0 := by
    intro hdmem
    have hfixx : d • L = L ∧ d • M = M := (hH0mem d).mp hdmem
    have hLle : L.1 ≤ YSubmodule hw2 x hx3 hfix hxX hYinv := hdline L hfixx.1
    have hMle : M.1 ≤ YSubmodule hw2 x hx3 hfix hxX hYinv := hdline M hfixx.2
    have hYfin1 : Module.finrank (GaloisField 2 2) (YSubmodule hw2 x hx3 hfix hxX hYinv) = 1 :=
      finrank_eq_one_of_card_four hYsubcard
    have hLeq : L.1 = YSubmodule hw2 x hx3 hfix hxX hYinv :=
      Submodule.eq_of_le_of_finrank_le hLle (by rw [hYfin1, L.2])
    have hMeq : M.1 = YSubmodule hw2 x hx3 hfix hxX hYinv :=
      Submodule.eq_of_le_of_finrank_le hMle (by rw [hYfin1, M.2])
    exact hLM (Subtype.ext (hLeq.trans hMeq.symm))
  have hcover : ∀ b : ↥H, b ∈ H0 ∨ b * d⁻¹ ∈ H0 := by
    intro b
    by_cases hb : b ∈ H0
    · exact Or.inl hb
    · right
      rcases hdich b with hfixx | hswap
      · exact absurd ((hH0mem b).mpr hfixx) hb
      · rw [hH0mem]
        refine ⟨?_, ?_⟩
        · calc (b * d⁻¹) • L = b • (d⁻¹ • L) := mul_smul b d⁻¹ L
            _ = b • M := by rw [hdinvL]
            _ = L := hswap.2
        · calc (b * d⁻¹) • M = b • (d⁻¹ • M) := mul_smul b d⁻¹ M
            _ = b • L := by rw [hdinvM]
            _ = M := hswap.1
  have hindex : H0.index = 2 := by
    rw [Subgroup.index_eq_two_iff_exists_notMem_and]
    refine ⟨d⁻¹, ?_, fun b => ?_⟩
    · intro hmem
      exact hdnot (by simpa using H0.inv_mem hmem)
    · rcases hcover b with h | h
      · exact Or.inr h
      · exact Or.inl h
  have hcardHmul : Nat.card ↥H = Nat.card ↥H0 * 2 := by
    have h := Subgroup.card_mul_index (H := H0)
    rw [hindex] at h
    omega
  have hρinj : Function.Injective (HLinHom hw2 x hx3 hfix H hcommH) := by
    intro g₁ g₂ hEq
    let dd : ↥H := g₁ * g₂⁻¹
    have hmap : HLinHom hw2 x hx3 hfix H hcommH dd = 1 := by
      have hmul : HLinHom hw2 x hx3 hfix H hcommH (g₁ * g₂⁻¹) =
          HLinHom hw2 x hx3 hfix H hcommH g₁ *
            (HLinHom hw2 x hx3 hfix H hcommH g₂)⁻¹ := by
        rw [map_mul, map_inv]
      rw [hmul, hEq, mul_inv_cancel]
    have hlin : hGaloisLinearEquiv hw2 x hx3 hfix (dd : MulAut W) (hcommH dd dd.2) = 1 := by
      simpa [HLinHom_apply] using hmap
    have hdd1 : dd = 1 := by
      by_contra hne
      exact hGaloisLinearEquiv_ne_one hw2 x hx3 hfix (hcommH dd dd.2)
        (fun h => hne (Subtype.ext h)) hlin
    exact mul_inv_eq_one.mp (by simpa [dd] using hdd1)
  obtain ⟨f, hfinj, hfL, hfM⟩ :=
    exists_injective_pair_scalar_of_le (K := GaloisField 2 2) (V := Additive W)
      hVf hLM H0 (HLinHom hw2 x hx3 hfix H hcommH) hρinj
      (fun g hg => ((hH0mem g).mp hg).1) (fun g hg => ((hH0mem g).mp hg).2)
  have hunit : Nat.card ((GaloisField 2 2)ˣ) = 3 := by
    rw [Nat.card_units, hKcard]
  have hprod9 : Nat.card ((GaloisField 2 2)ˣ × (GaloisField 2 2)ˣ) = 9 := by
    rw [Nat.card_prod, hunit]
  have hrangecard : Nat.card ↥H0 = Nat.card f.range :=
    Nat.card_congr (Equiv.ofInjective f hfinj)
  have hdvd9 : Nat.card ↥H0 ∣ 9 := by
    rw [hrangecard]
    have h := f.range.card_subgroup_dvd_card
    rwa [hprod9] at h
  have h3dvd : 3 ∣ Nat.card ↥H0 := by
    have hsub : Nat.card ((X.subgroupOf H).subgroupOf H0) = Nat.card (X.subgroupOf H) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXleH0).toEquiv
    have hdvd := ((X.subgroupOf H).subgroupOf H0).card_subgroup_dvd_card
    rwa [hsub, hXsubcard] at hdvd
  have hH0comm' : ∀ a b : ↥H0, a * b = b * a := by
    intro a b
    apply hfinj
    rw [map_mul, map_mul, mul_comm]
  have hH0comm : ∀ a ∈ H0, ∀ b ∈ H0, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (hH0comm' ⟨a, ha⟩ ⟨b, hb⟩)
  have hH0card : Nat.card ↥H0 = 3 ∨ Nat.card ↥H0 = 9 := by
    obtain ⟨k, hk⟩ := h3dvd
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · rw [h0, mul_zero] at hk
        exact absurd hk (Nat.card_pos.ne')
      · exact hpos
    have hkdvd : k ∣ 3 := by
      have h9 := hdvd9
      rw [hk] at h9
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : (0 : ℕ) < 3) h9
    have hk13 : k = 1 ∨ k = 3 := (Nat.dvd_prime Nat.prime_three).mp hkdvd
    rcases hk13 with h1 | h3
    · left; omega
    · right; omega
  have hH0ne3 : Nat.card ↥H0 ≠ 3 := by
    intro hcard3
    have hH0eqX : H0 = X.subgroupOf H :=
      (Subgroup.eq_of_le_of_card_ge hXleH0 (by rw [hXsubcard, hcard3])).symm
    have hdH0comm : ∀ h ∈ H0, d * h = h * d := by
      intro h hh
      apply Subtype.ext
      have hhX : (h : MulAut W) ∈ X := by
        have hh' : h ∈ X.subgroupOf H := hH0eqX ▸ hh
        exact Subgroup.mem_subgroupOf.mp hh' 
      exact hDCX d0 hd0D (h : MulAut W) hhX
    have hHcomm : ∀ a b : ↥H, a * b = b * a := by
      intro a b
      have ha := hcover a
      have hb := hcover b
      rcases ha with ha | ha
      · rcases hb with hb | hb
        · exact hH0comm a ha b hb
        · set b0 : ↥H := b * d⁻¹ with hb0
          have hb0mem : b0 ∈ H0 := hb
          have hbeq : b = b0 * d := by
            rw [hb0]; group
          rw [hbeq]
          calc a * (b0 * d) = (a * b0) * d := by group
            _ = (b0 * a) * d := by rw [hH0comm a ha b0 hb0mem]
            _ = b0 * (a * d) := by group
            _ = b0 * (d * a) := by rw [hdH0comm a ha]
            _ = b0 * d * a := by group
      · rcases hb with hb | hb
        · set a0 : ↥H := a * d⁻¹ with ha0
          have ha0mem : a0 ∈ H0 := ha
          have haeq : a = a0 * d := by
            rw [ha0]; group
          rw [haeq]
          calc a0 * d * b = a0 * (d * b) := by group
            _ = a0 * (b * d) := by rw [hdH0comm b hb]
            _ = (a0 * b) * d := by group
            _ = (b * a0) * d := by rw [hH0comm a0 ha0mem b hb]
            _ = b * (a0 * d) := by group
        · set a0 : ↥H := a * d⁻¹ with ha0
          set b0 : ↥H := b * d⁻¹ with hb0
          have ha0mem : a0 ∈ H0 := ha
          have hb0mem : b0 ∈ H0 := hb
          have haeq : a = a0 * d := by rw [ha0]; group
          have hbeq : b = b0 * d := by rw [hb0]; group
          rw [haeq, hbeq]
          calc a0 * d * (b0 * d) = a0 * (d * b0) * d := by group
            _ = a0 * (b0 * d) * d := by rw [hdH0comm b0 hb0mem]
            _ = (a0 * b0) * (d * d) := by group
            _ = (a0 * b0) * 1 := by rw [hd_d]
            _ = a0 * b0 := by group
            _ = b0 * a0 := hH0comm a0 ha0mem b0 hb0mem
            _ = (b0 * a0) * 1 := by group
            _ = (b0 * a0) * (d * d) := by rw [hd_d]
            _ = b0 * (a0 * d) * d := by group
            _ = b0 * (d * a0) * d := by rw [hdH0comm a0 ha0mem]
            _ = b0 * d * (a0 * d) := by group
    have hs2 : s * s = 1 := by
      have h := pow_orderOf_eq_one s
      rw [hs_ord2] at h
      simpa [pow_two] using h
    have hGcent : ∀ g ∈ G, g * d0 = d0 * g := by
      intro g hg
      rcases cover_H_MulAut hXG hH hXnorm hxgen hx_ord3 hsG hs2 hs_not_cent g hg with hgH | hgH
      · have hcomm := hHcomm ⟨g, hgH⟩ d
        simpa [d] using congrArg Subtype.val hcomm
      · have hseq : g = s * (s⁻¹ * g) := by group
        have hsd : s * d0 = d0 * s := (hDs d0 hd0D).symm
        have hhcomm : (s⁻¹ * g) * d0 = d0 * (s⁻¹ * g) := by
          have hcomm := hHcomm ⟨s⁻¹ * g, hgH⟩ d
          simpa [d] using congrArg Subtype.val hcomm
        rw [hseq]
        calc s * (s⁻¹ * g) * d0 = s * ((s⁻¹ * g) * d0) := by group
          _ = s * (d0 * (s⁻¹ * g)) := by rw [hhcomm]
          _ = (s * d0) * (s⁻¹ * g) := by group
          _ = (d0 * s) * (s⁻¹ * g) := by rw [hsd]
          _ = d0 * (s * (s⁻¹ * g)) := by group
    have hfixVcases := fixV_eq_bot_or_top_of_central hirr hGcent
    have hYle : Y ≤ fixV (Subgroup.zpowers d0) := by
      intro y hy
      rw [mem_fixV]
      intro a ha
      have hzD : a ∈ D := Subgroup.zpowers_le.mpr hd0D ha
      exact apply_eq_self_of_le_fixV hYD hzD hy
    have hbot : fixV (Subgroup.zpowers d0) ≠ ⊥ := by
      intro h
      have hYbot : Y = ⊥ := by
        rw [← le_bot_iff]
        rwa [h] at hYle
      rw [hYbot] at hYcard
      simp at hYcard
    have htop : fixV (Subgroup.zpowers d0) ≠ ⊤ := by
      intro h
      apply hd0ne
      ext w
      have hw : w ∈ fixV (Subgroup.zpowers d0) := by rw [h]; exact Subgroup.mem_top w
      exact mem_fixV.mp hw d0 (Subgroup.mem_zpowers d0)
    rcases hfixVcases with h | h
    · exact hbot h
    · exact htop h
  have hH0nine : Nat.card ↥H0 = 9 := by
    rcases hH0card with h | h
    · exact absurd h hH0ne3
    · exact h
  refine ⟨?_, L, M, H0, d, hLM, hXleH0, hindex, hH0nine, hH0comm, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [hcardHmul, hH0nine]
  · intro h
    rw [hH0mem h]
    exact Iff.rfl
  · exact hd0D
  · exact hd_d
  · exact hdnot
  · exact hcover
  · exact (hsmul_def d L).symm.trans hdswap.1
  · exact (hsmul_def d M).symm.trans hdswap.2
  · exact hfixsub

end PairBranch

section HLinInjective

variable {W : Type*} [CommGroup W] [Finite W]

theorem hLinHom_injective {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (H : Subgroup (MulAut W))
    (hcommH : ∀ h ∈ H, h * x = x * h) :
    Function.Injective (HLinHom hw2 x hx3 hfix H hcommH) := by
  letI := galoisModule hw2 x hx3 hfix
  intro g₁ g₂ hEq
  let dd : ↥H := g₁ * g₂⁻¹
  have hmap : HLinHom hw2 x hx3 hfix H hcommH dd = 1 := by
    have hmul : HLinHom hw2 x hx3 hfix H hcommH (g₁ * g₂⁻¹) =
        HLinHom hw2 x hx3 hfix H hcommH g₁ *
          (HLinHom hw2 x hx3 hfix H hcommH g₂)⁻¹ := by
      rw [map_mul, map_inv]
    rw [hmul, hEq, mul_inv_cancel]
  have hlin : hGaloisLinearEquiv hw2 x hx3 hfix (dd : MulAut W) (hcommH dd dd.2) = 1 := by
    simpa [HLinHom_apply] using hmap
  have hdd1 : dd = 1 := by
    by_contra hne
    exact hGaloisLinearEquiv_ne_one hw2 x hx3 hfix (hcommH dd dd.2)
      (fun h => hne (Subtype.ext h)) hlin
  exact mul_inv_eq_one.mp (by simpa [dd] using hdd1)

end HLinInjective

section PairTorusAux

variable {W : Type*} [CommGroup W] [Finite W]

private theorem hgal_congr_eq (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) {h₁ h₂ : MulAut W} (he : h₁ = h₂)
    (hc₁ : h₁ * x = x * h₁) (hc₂ : h₂ * x = x * h₂) :
    hGaloisLinearEquiv hw2 x hx3 hfix h₁ hc₁ =
      hGaloisLinearEquiv hw2 x hx3 hfix h₂ hc₂ := by
  subst h₂
  exact congrArg (fun hc => hGaloisLinearEquiv hw2 x hx3 hfix h₁ hc)
    (Subsingleton.elim hc₁ hc₂)

private theorem pair_torus_theta_ne
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16)
    {H : Subgroup (MulAut W)} (hcommH : ∀ h ∈ H, h * x = x * h) :
    letI := galoisModule hw2 x hx3 hfix
    ∀ {L M : LineOf (K := GaloisField 2 2) (V := Additive W)} (hLM : L ≠ M)
      {H0 : Subgroup ↥H} {d : ↥H},
      (∀ h : ↥H, h ∈ H0 ↔ lineMap (HLinHom hw2 x hx3 hfix H hcommH h) L = L ∧
        lineMap (HLinHom hw2 x hx3 hfix H hcommH h) M = M) →
      Nat.card H0 = 9 →
      lineMap (HLinHom hw2 x hx3 hfix H hcommH d) L = M →
      lineMap (HLinHom hw2 x hx3 hfix H hcommH d) M = L →
      d * d = 1 →
      ¬ (∀ u ∈ H0, d * u * d⁻¹ = u) := by
  letI := galoisModule hw2 x hx3 hfix
  intro L M hLM H0 d hH0mem hH0card hdL hdM hd2 htheta
  let d0 : MulAut W := (d : MulAut W)
  have hd0H : d0 ∈ H := d.2
  have hd0comm : d0 * x = x * d0 := hcommH d0 hd0H
  let hgalD : Additive W ≃ₗ[GaloisField 2 2] Additive W :=
    hGaloisLinearEquiv hw2 x hx3 hfix d0 hd0comm
  have hgalD_L : lineMap hgalD L = M := by
    rw [show hgalD = HLinHom hw2 x hx3 hfix H hcommH d from by
      rw [HLinHom_apply]]
    exact hdL
  have hgalD_M : lineMap hgalD M = L := by
    rw [show hgalD = HLinHom hw2 x hx3 hfix H hcommH d from by
      rw [HLinHom_apply]]
    exact hdM
  let hgalH : ↥H0 → (Additive W ≃ₗ[GaloisField 2 2] Additive W) := fun h =>
    hGaloisLinearEquiv hw2 x hx3 hfix ((h : ↥H) : MulAut W) (hcommH _ (h : ↥H).2)
  have hgalH_L : ∀ h : ↥H0, lineMap (hgalH h) L = L := by
    intro h
    have hh := (hH0mem (h : ↥H)).mp h.2
    have h1 : lineMap (HLinHom hw2 x hx3 hfix H hcommH (h : ↥H)) L = L := hh.1
    rw [HLinHom_apply] at h1
    exact h1
  have hgalH_M : ∀ h : ↥H0, lineMap (hgalH h) M = M := by
    intro h
    have hh := (hH0mem (h : ↥H)).mp h.2
    have h1 : lineMap (HLinHom hw2 x hx3 hfix H hcommH (h : ↥H)) M = M := hh.2
    rw [HLinHom_apply] at h1
    exact h1
  have hcomm_lin : ∀ h : ↥H0, hgalH h * hgalD = hgalD * hgalH h := by
    intro h
    have hd0sq : d0 * d0 = 1 := by
      have := congrArg Subtype.val hd2
      simpa [d0] using this
    have hhcomm : ((h : ↥H) : MulAut W) * d0 = d0 * ((h : ↥H) : MulAut W) := by
      have hh := htheta (h : ↥H) h.2
      have hh' : d0 * ((h : ↥H) : MulAut W) * d0⁻¹ = ((h : ↥H) : MulAut W) :=
        congrArg Subtype.val hh
      have hd0inv : d0⁻¹ = d0 := inv_eq_of_mul_eq_one_right hd0sq
      calc ((h : ↥H) : MulAut W) * d0 = (d0 * ((h : ↥H) : MulAut W) * d0⁻¹) * d0 := by
            rw [hh']
        _ = (d0 * ((h : ↥H) : MulAut W) * d0) * d0 := by rw [hd0inv]
        _ = d0 * ((h : ↥H) : MulAut W) * (d0 * d0) := by group
        _ = d0 * ((h : ↥H) : MulAut W) := by rw [hd0sq, mul_one]
    have h1 : hgalH h * hgalD =
        hGaloisLinearEquiv hw2 x hx3 hfix
          (((h : ↥H) : MulAut W) * d0) (hcommH _ (H.mul_mem (h : ↥H).2 hd0H)) := by
      rw [hGaloisLinearEquiv_mul hw2 x hx3 hfix ((h : ↥H) : MulAut W) d0
        (hcommH _ (h : ↥H).2) hd0comm (hcommH _ (H.mul_mem (h : ↥H).2 hd0H))]
      exact (LinearEquiv.mul_eq_trans (hgalH h) hgalD).symm
    have h2 : hgalD * hgalH h =
        hGaloisLinearEquiv hw2 x hx3 hfix
          (d0 * ((h : ↥H) : MulAut W)) (hcommH _ (H.mul_mem hd0H (h : ↥H).2)) := by
      rw [hGaloisLinearEquiv_mul hw2 x hx3 hfix d0 ((h : ↥H) : MulAut W)
        hd0comm (hcommH _ (h : ↥H).2) (hcommH _ (H.mul_mem hd0H (h : ↥H).2))]
      exact (LinearEquiv.mul_eq_trans hgalD (hgalH h)).symm
    rw [h1, h2]
    exact hgal_congr_eq hw2 x hx3 hfix hhcomm _ _
  have hVf : Module.finrank (GaloisField 2 2) (Additive W) = 2 :=
    finrank_galoisModule hw2 x hx3 hfix hW
  have hscalar : ∀ h : ↥H0, ∃ c : GaloisField 2 2, ∀ v : Additive W,
      (hgalH h : Additive W → Additive W) v = c • v := by
    intro h
    exact exists_smul_one_of_commute_swap hVf hLM (hgalH_L h) (hgalH_M h)
      hgalD_L hgalD_M (hcomm_lin h)
  let c : ↥H0 → GaloisField 2 2 := fun h => Classical.choose (hscalar h)
  have hcspec : ∀ (h : ↥H0) (v : Additive W), (hgalH h) v = c h • v := fun h =>
    Classical.choose_spec (hscalar h)
  have hcne : ∀ h : ↥H0, c h ≠ 0 := by
    intro h hc0
    have hzero : ∀ v : Additive W, (hgalH h) v = 0 := by
      intro v
      rw [hcspec h v, hc0]
      simp
    obtain ⟨v, hv⟩ :=
      Module.finrank_pos_iff_exists_ne_zero.mp
        (by rw [hVf]; norm_num : 0 < Module.finrank (GaloisField 2 2) (Additive W))
    have h0 : (hgalH h) v = (hgalH h) 0 := by rw [hzero v, hzero 0]
    exact hv ((hgalH h).injective h0)
  let Ψ : ↥H0 → (GaloisField 2 2)ˣ := fun h => Units.mk0 (c h) (hcne h)
  have hΨinj : Function.Injective Ψ := by
    intro h₁ h₂ hEq
    have hc : c h₁ = c h₂ := by
      have := congrArg Units.val hEq
      simpa [Ψ] using this
    have hlin : hgalH h₁ = hgalH h₂ := by
      ext v
      rw [hcspec h₁ v, hcspec h₂ v, hc]
    apply Subtype.ext
    exact hLinHom_injective hw2 x hx3 hfix H hcommH (by
      rw [HLinHom_apply, HLinHom_apply]
      exact hlin)
  have hunit : Nat.card ((GaloisField 2 2)ˣ) = 3 := by
    have hK : Nat.card (GaloisField 2 2) = 4 := by
      rw [GaloisField.card 2 2 (by norm_num)]
      norm_num
    rw [Nat.card_units, hK]
  have hle : Nat.card ↥H0 ≤ 3 := by
    have h := Nat.card_le_card_of_injective Ψ hΨinj
    rwa [hunit] at h
  omega

end PairTorusAux

section PairTorus

variable {W : Type*} [CommGroup W] [Finite W]

theorem sixfourteen_n2_pair_torus {W : Type} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hx_ord3 : orderOf x = 3)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16)
    {G X H D : Subgroup (MulAut W)} {s : MulAut W} {Y : Subgroup W}
    (hH : H = G ⊓ Subgroup.centralizer (X : Set (MulAut W)))
    (hXG : X ≤ G) (hXnorm : ∀ g ∈ G, ∀ y ∈ X, g * y * g⁻¹ ∈ X)
    (hxgen : X = Subgroup.zpowers x)
    (hsG : s ∈ G) (hs_ord2 : orderOf s = 2)
    (hs_not_cent : s ∉ Subgroup.centralizer (X : Set (MulAut W)))
    (hirr : ∀ Z : Subgroup W, (∀ g ∈ G, ∀ z ∈ Z, g z ∈ Z) → Z = ⊥ ∨ Z = ⊤)
    (hD : D ≤ G) (hDCX : ∀ d ∈ D, ∀ y ∈ X, d * y = y * d)
    (hDs : ∀ d ∈ D, d * s = s * d)
    (hElem : CFSG.Quasithin.IsElemAbelian2 D) (hDcard : Nat.card D = 2)
    (hYD : Y ≤ fixV D)
    (hYinv : ∀ a ∈ X, ∀ y ∈ Y, a y ∈ Y) (hYcard : Nat.card Y = 4)
    (hcommH : ∀ h ∈ H, h * x = x * h)
    (hpair : letI := galoisModule hw2 x hx3 hfix;
      ∃ S : Set (LineOf (K := GaloisField 2 2) (V := Additive W)),
        S.ncard = 2 ∧ S.Nonempty ∧ S ≠ Set.univ ∧
        (∀ h : ↥H, S.image (fun L => lineMap (HLinHom hw2 x hx3 hfix H hcommH h) L) = S)) :
    letI := galoisModule hw2 x hx3 hfix
    ∃ (L M : LineOf (K := GaloisField 2 2) (V := Additive W)) (H0 : Subgroup ↥H)
      (v : ↥H0) (d : ↥H),
      L ≠ M ∧
      (X.subgroupOf H) ≤ H0 ∧
      ((X.subgroupOf H).subgroupOf H0) ⊔ Subgroup.zpowers v = ⊤ ∧
      ((X.subgroupOf H).subgroupOf H0) ⊓ Subgroup.zpowers v = ⊥ ∧
      Nat.card H0 = 9 ∧
      (∀ h : ↥H, h ∈ H0 ↔ lineMap (HLinHom hw2 x hx3 hfix H hcommH h) L = L ∧
        lineMap (HLinHom hw2 x hx3 hfix H hcommH h) M = M) ∧
      (∀ a ∈ H0, ∀ b ∈ H0, a * b = b * a) ∧
      v ∉ (X.subgroupOf H).subgroupOf H0 ∧ orderOf v = 3 ∧
      (d : MulAut W) ∈ D ∧ d * d = 1 ∧ d ∉ H0 ∧
      (∀ b : ↥H, b ∈ H0 ∨ b * d⁻¹ ∈ H0) ∧
      (d : MulAut W) * (((v : ↥H0) : ↥H) : MulAut W) * (d : MulAut W)⁻¹ =
        (((v ^ 2 : ↥H0) : ↥H) : MulAut W) ∧
      (∀ w : ↥H0, (d : MulAut W) * (((w : ↥H0) : ↥H) : MulAut W) * (d : MulAut W)⁻¹ =
        (((w ^ 2 : ↥H0) : ↥H) : MulAut W) → w ∈ Subgroup.zpowers v) ∧
      lineMap (HLinHom hw2 x hx3 hfix H hcommH d) L = M ∧
      lineMap (HLinHom hw2 x hx3 hfix H hcommH d) M = L := by
  letI := galoisModule hw2 x hx3 hfix
  obtain ⟨-, L, M, H0, d, hLM, hXleH0, hindex, hH0card, hH0comm, hH0mem, hdD, hd2, hdnot,
    hcover, hdL, hdM, hdfix⟩ :=
    sixfourteen_n2_pair_orders hw2 x hx3 hx_ord3 hfix hW hH hXG hXnorm hxgen hsG hs_ord2
      hs_not_cent hirr hD hDCX hDs hElem hDcard hYD hYinv hYcard hcommH hpair
  have hVf : Module.finrank (GaloisField 2 2) (Additive W) = 2 :=
    finrank_galoisModule hw2 x hx3 hfix hW
  obtain ⟨f, hfinj, hfL, hfM⟩ :=
    exists_injective_pair_scalar_of_le hVf hLM H0 (HLinHom hw2 x hx3 hfix H hcommH)
      (hLinHom_injective hw2 x hx3 hfix H hcommH)
      (fun g hg => ((hH0mem g).mp hg).1) (fun g hg => ((hH0mem g).mp hg).2)
  have hKcard : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hunit : Nat.card ((GaloisField 2 2)ˣ) = 3 := by
    rw [Nat.card_units, hKcard]
  have hexp3 : ∀ u : ↥H0, u ^ 3 = 1 := by
    intro u
    apply hfinj
    rw [map_pow, map_one]
    have h1 : (f u).1 ^ 3 = 1 := by
      have h := pow_card_eq_one' (G := (GaloisField 2 2)ˣ) (x := (f u).1)
      rwa [hunit] at h
    have h2 : (f u).2 ^ 3 = 1 := by
      have h := pow_card_eq_one' (G := (GaloisField 2 2)ˣ) (x := (f u).2)
      rwa [hunit] at h
    ext
    · simpa using congrArg Units.val h1
    · simpa using congrArg Units.val h2
  have hdinvL : lineMap (HLinHom hw2 x hx3 hfix H hcommH d⁻¹) L = M := by
    have hinj : Function.Injective (lineMap (HLinHom hw2 x hx3 hfix H hcommH d)) := by
      intro a b hab
      have h := congrArg (fun K => lineMap (HLinHom hw2 x hx3 hfix H hcommH d⁻¹) K) hab
      rw [← lineMap_mul_apply, ← lineMap_mul_apply] at h
      have hmul : HLinHom hw2 x hx3 hfix H hcommH d⁻¹ *
          HLinHom hw2 x hx3 hfix H hcommH d = 1 := by
        rw [← map_mul, inv_mul_cancel, map_one]
      rw [hmul, lineMap_one_apply, lineMap_one_apply] at h
      exact h
    have h1 : lineMap (HLinHom hw2 x hx3 hfix H hcommH d)
        (lineMap (HLinHom hw2 x hx3 hfix H hcommH d⁻¹) L) = L := by
      rw [← lineMap_mul_apply]
      have hmul : HLinHom hw2 x hx3 hfix H hcommH d *
          HLinHom hw2 x hx3 hfix H hcommH d⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel, map_one]
      rw [hmul, lineMap_one_apply]
    have h2 : lineMap (HLinHom hw2 x hx3 hfix H hcommH d) M = L := hdM
    exact hinj (h1.trans h2.symm)
  have hdinvM : lineMap (HLinHom hw2 x hx3 hfix H hcommH d⁻¹) M = L := by
    have hinj : Function.Injective (lineMap (HLinHom hw2 x hx3 hfix H hcommH d)) := by
      intro a b hab
      have h := congrArg (fun K => lineMap (HLinHom hw2 x hx3 hfix H hcommH d⁻¹) K) hab
      rw [← lineMap_mul_apply, ← lineMap_mul_apply] at h
      have hmul : HLinHom hw2 x hx3 hfix H hcommH d⁻¹ *
          HLinHom hw2 x hx3 hfix H hcommH d = 1 := by
        rw [← map_mul, inv_mul_cancel, map_one]
      rw [hmul, lineMap_one_apply, lineMap_one_apply] at h
      exact h
    have h1 : lineMap (HLinHom hw2 x hx3 hfix H hcommH d)
        (lineMap (HLinHom hw2 x hx3 hfix H hcommH d⁻¹) M) = M := by
      rw [← lineMap_mul_apply]
      have hmul : HLinHom hw2 x hx3 hfix H hcommH d *
          HLinHom hw2 x hx3 hfix H hcommH d⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel, map_one]
      rw [hmul, lineMap_one_apply]
    have h2 : lineMap (HLinHom hw2 x hx3 hfix H hcommH d) L = M := hdL
    exact hinj (h1.trans h2.symm)
  have hconj_mem : ∀ u : ↥H0, ∃ u' : ↥H0, (u' : ↥H) = d * (u : ↥H) * d⁻¹ := by
    intro u
    have huH : (((u : ↥H0) : ↥H) : MulAut W) ∈ H := (u : ↥H).2
    let w : ↥H := ⟨d * (u : ↥H) * d⁻¹,
      H.mul_mem (H.mul_mem d.2 huH) (H.inv_mem d.2)⟩
    have hwH0 : w ∈ H0 := by
      rw [hH0mem w]
      have hwlin : HLinHom hw2 x hx3 hfix H hcommH w =
          HLinHom hw2 x hx3 hfix H hcommH d *
            HLinHom hw2 x hx3 hfix H hcommH (u : ↥H) *
              HLinHom hw2 x hx3 hfix H hcommH d⁻¹ := by
        change HLinHom hw2 x hx3 hfix H hcommH (d * (u : ↥H) * d⁻¹) = _
        rw [map_mul, map_mul, map_inv]
      constructor
      · rw [hwlin, lineMap_mul_apply, lineMap_mul_apply, hdinvL]
        rw [((hH0mem (u : ↥H)).mp u.2).2, hdM]
      · rw [hwlin, lineMap_mul_apply, lineMap_mul_apply, hdinvM]
        rw [((hH0mem (u : ↥H)).mp u.2).1, hdL]
    exact ⟨⟨w, hwH0⟩, rfl⟩
  let θ : ↥H0 → ↥H0 := fun u => Classical.choose (hconj_mem u)
  have hθspec : ∀ u : ↥H0, (θ u : ↥H) = d * (u : ↥H) * d⁻¹ := fun u =>
    Classical.choose_spec (hconj_mem u)
  have hθmul : ∀ u v : ↥H0, θ (u * v) = θ u * θ v := by
    intro u v
    apply Subtype.ext
    rw [Subgroup.coe_mul, hθspec (u * v), hθspec u, hθspec v, Subgroup.coe_mul]
    group
  have hθone : θ 1 = 1 := by
    apply Subtype.ext
    rw [hθspec 1]
    simp
  have hθinv : ∀ u : ↥H0, θ u⁻¹ = (θ u)⁻¹ := by
    intro u
    apply Subtype.ext
    have h1 : (θ u⁻¹ : ↥H) = d * (((u⁻¹ : ↥H0) : ↥H)) * d⁻¹ := hθspec u⁻¹
    have h2 : (((θ u)⁻¹ : ↥H0) : ↥H) = ((d * ((u : ↥H0) : ↥H) * d⁻¹)⁻¹) := by
      rw [Subgroup.coe_inv, hθspec u]
    rw [h1, h2, Subgroup.coe_inv]
    group
  have hd0sq : (d : MulAut W) * (d : MulAut W) = 1 := by
    have := congrArg Subtype.val hd2
    simpa using this
  have hθinv2 : ∀ u : ↥H0, θ (θ u) = u := by
    intro u
    apply Subtype.ext
    rw [hθspec (θ u), hθspec u]
    have hdinv : (d : ↥H)⁻¹ = d := inv_eq_of_mul_eq_one_right hd2
    calc d * (d * (u : ↥H) * d⁻¹) * d⁻¹ = (d * d) * (u : ↥H) * (d⁻¹ * d⁻¹) := by group
      _ = (u : ↥H) := by rw [hd2, hdinv, hd2]; group
  have hH0comm' : ∀ a b : ↥H0, a * b = b * a := by
    intro a b
    apply Subtype.ext
    exact hH0comm (a : ↥H) a.2 (b : ↥H) b.2
  let U : Subgroup ↥H0 :=
  { carrier := {u | θ u = u ^ 2}
    one_mem' := by
      show θ 1 = 1 ^ 2
      rw [hθone, one_pow]
    mul_mem' := by
      intro u v hu hv
      show θ (u * v) = (u * v) ^ 2
      rw [hθmul, hu, hv]
      have hsq : u ^ 2 * v ^ 2 = (u * v) ^ 2 := by
        rw [pow_two, pow_two, pow_two]
        calc u * u * (v * v) = u * (u * v) * v := by group
          _ = u * (v * u) * v := by rw [hH0comm' u v]
          _ = u * v * (u * v) := by group
      exact hsq
    inv_mem' := by
      intro u hu
      show θ u⁻¹ = (u⁻¹) ^ 2
      rw [hθinv, hu]
      group }
  have htheta_ne : ¬ (∀ u ∈ H0, d * u * d⁻¹ = u) :=
    pair_torus_theta_ne hw2 x hx3 hfix hW hcommH hLM hH0mem hH0card hdL hdM hd2
  have hex : ∃ u : ↥H0, θ u ≠ u := by
    by_contra h
    push Not at h
    apply htheta_ne
    intro u hu
    have h1 : θ ⟨u, hu⟩ = ⟨u, hu⟩ := h ⟨u, hu⟩
    have h2 := congrArg Subtype.val h1
    rw [hθspec] at h2
    exact h2
  obtain ⟨u, hu_ne⟩ := hex
  let u0 : ↥H0 := u * (θ u)⁻¹
  have hu0U : u0 ∈ U := by
    show θ u0 = u0 ^ 2
    have h1 : θ u0 = u0⁻¹ := by
      have : u0 = u * (θ u)⁻¹ := rfl
      rw [this, hθmul, hθinv, hθinv2]
      group
    rw [h1]
    have h3 : u0 ^ 3 = 1 := hexp3 u0
    have hinv : u0⁻¹ = u0 ^ 2 := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_succ', h3]
    exact hinv
  have hu0ne : u0 ≠ 1 := by
    intro h
    apply hu_ne
    have hu : u = θ u := by
      calc u = (u * (θ u)⁻¹) * (θ u) := by group
        _ = 1 * (θ u) := by rw [← h]
        _ = θ u := one_mul _
    exact hu.symm
  have hUne : U ≠ ⊥ := by
    intro hbot
    have : u0 ∈ (⊥ : Subgroup ↥H0) := hbot ▸ hu0U
    exact hu0ne (Subgroup.mem_bot.mp this)
  let X0 : Subgroup ↥H0 := (X.subgroupOf H).subgroupOf H0
  have hXcard : Nat.card X = 3 := by rw [hxgen, Nat.card_zpowers, hx_ord3]
  have hXH : X ≤ H := by
    rw [hH]
    exact le_inf_centralizer_self hXG hXcard
  have hXsubcard : Nat.card (X.subgroupOf H) = 3 := by
    have h := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv
    rw [hXcard] at h
    exact h
  have hX0card : Nat.card X0 = 3 := by
    have h := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXleH0).toEquiv
    rw [hXsubcard] at h
    exact h
  have hX0U : X0 ⊓ U = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rcases Subgroup.mem_inf.mp hu with ⟨huX, huU⟩
    have hθu : θ u = u := by
      apply Subtype.ext
      rw [hθspec u]
      apply Subtype.ext
      have huX' : (((u : ↥H0) : ↥H) : MulAut W) ∈ X := huX
      have hcomm := hDCX (d : MulAut W) hdD (((u : ↥H0) : ↥H) : MulAut W) huX'
      have hdinv : (d : MulAut W)⁻¹ = (d : MulAut W) := inv_eq_of_mul_eq_one_right hd0sq
      calc ((d * (u : ↥H) * d⁻¹ : ↥H) : MulAut W)
          = (d : MulAut W) * (((u : ↥H0) : ↥H) : MulAut W) * (d : MulAut W)⁻¹ := rfl
        _ = (d : MulAut W) * (((u : ↥H0) : ↥H) : MulAut W) * (d : MulAut W) := by rw [hdinv]
        _ = (((u : ↥H0) : ↥H) : MulAut W) * (d : MulAut W) * (d : MulAut W) := by
              rw [hcomm]
        _ = (((u : ↥H0) : ↥H) : MulAut W) := by
              rw [mul_assoc, hd0sq, mul_one]
    have huU' : θ u = u ^ 2 := huU
    rw [hθu] at huU'
    have hone : u = 1 := by
      have h : u * u = u * 1 := by rw [mul_one, ← pow_two, ← huU']
      exact mul_left_cancel h
    rw [Subgroup.mem_bot]
    exact hone
  have hUcard : Nat.card ↥U = 3 := by
    have hdvd : Nat.card ↥U ∣ 9 := by
      have h := U.card_subgroup_dvd_card
      rwa [hH0card] at h
    have h9 : (9 : ℕ) = 3 ^ 2 := by norm_num
    rw [h9] at hdvd
    obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hkcases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hkcases with rfl | rfl | rfl
    · exfalso
      apply hUne
      rw [Subgroup.eq_bot_iff_card]
      simpa using hk
    · simpa using hk
    · exfalso
      have htop : U = ⊤ := by
        apply Subgroup.eq_top_of_card_eq
        rw [hk, hH0card]
        norm_num
      have hXle : X0 ≤ U := by rw [htop]; exact le_top
      have hinf : X0 ⊓ U = X0 := inf_eq_left.mpr hXle
      rw [hX0U] at hinf
      have hzero : X0 = ⊥ := hinf.symm
      rw [hzero, Subgroup.card_bot] at hX0card
      omega
  obtain ⟨v, hvU, hvne⟩ := (Subgroup.bot_or_exists_ne_one U).resolve_left hUne
  have hvord : orderOf v = 3 := by
    have hdvd : orderOf v ∣ Nat.card ↥U := Subgroup.orderOf_dvd_natCard U hvU
    rw [hUcard] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp (by simpa using hdvd) with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hvne
    · exact h3
  have hzp : Subgroup.zpowers v = U := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hvU)
    rw [hUcard, Nat.card_zpowers, hvord]
  have hdisj : Disjoint X0 U := by
    rw [disjoint_iff]
    exact hX0U
  have hcardmul : Nat.card X0 * Nat.card U = Nat.card ↥H0 := by
    rw [hX0card, hUcard, hH0card]
  have hsup : X0 ⊔ U = ⊤ :=
    (Subgroup.isComplement'_of_card_mul_and_disjoint hcardmul hdisj).sup_eq_top
  have hsupV : X0 ⊔ Subgroup.zpowers v = ⊤ := by rw [hzp]; exact hsup
  have hvnotX : v ∉ X0 := by
    intro hvX
    have hm : v ∈ X0 ⊓ U := Subgroup.mem_inf.mpr ⟨hvX, hvU⟩
    rw [hX0U] at hm
    exact hvne (Subgroup.mem_bot.mp hm)
  have hv2 : θ v = v ^ 2 := hvU
  have hdv : (d : MulAut W) * (((v : ↥H0) : ↥H) : MulAut W) * (d : MulAut W)⁻¹ =
      (((v ^ 2 : ↥H0) : ↥H) : MulAut W) := by
    have h := congrArg (fun z : ↥H => (z : MulAut W)) (hθspec v)
    rw [hv2] at h
    exact h.symm
  have hUchar : ∀ w : ↥H0, (d : MulAut W) * (((w : ↥H0) : ↥H) : MulAut W) * (d : MulAut W)⁻¹ =
      (((w ^ 2 : ↥H0) : ↥H) : MulAut W) → w ∈ Subgroup.zpowers v := by
    intro w hw
    have hwU : w ∈ U := by
      show θ w = w ^ 2
      apply Subtype.ext
      rw [hθspec w]
      apply Subtype.ext
      exact hw
    rw [hzp]
    exact hwU
  have hdisj : ((X.subgroupOf H).subgroupOf H0) ⊓ Subgroup.zpowers v = ⊥ := by
    rw [hzp]
    exact hX0U
  exact ⟨L, M, H0, v, d, hLM, hXleH0, hsupV, hdisj, hH0card, hH0mem, hH0comm, hvnotX, hvord,
    hdD, hd2, hdnot, hcover, hdv, hUchar, hdL, hdM⟩

end PairTorus

section XScalarPair

variable {W : Type*} [CommGroup W] [Finite W]

theorem sixfourteen_n2_pair_X_scalar {W : Type} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hx_ord3 : orderOf x = 3)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16)
    {G X H D : Subgroup (MulAut W)} {s : MulAut W} {Y : Subgroup W}
    (hH : H = G ⊓ Subgroup.centralizer (X : Set (MulAut W)))
    (hXG : X ≤ G) (hXnorm : ∀ g ∈ G, ∀ y ∈ X, g * y * g⁻¹ ∈ X)
    (hxgen : X = Subgroup.zpowers x)
    (hsG : s ∈ G) (hs_ord2 : orderOf s = 2)
    (hs_not_cent : s ∉ Subgroup.centralizer (X : Set (MulAut W)))
    (hirr : ∀ Z : Subgroup W, (∀ g ∈ G, ∀ z ∈ Z, g z ∈ Z) → Z = ⊥ ∨ Z = ⊤)
    (hD : D ≤ G) (hDCX : ∀ d ∈ D, ∀ y ∈ X, d * y = y * d)
    (hDs : ∀ d ∈ D, d * s = s * d)
    (hElem : CFSG.Quasithin.IsElemAbelian2 D) (hDcard : Nat.card D = 2)
    (hYD : Y ≤ fixV D)
    (hYinv : ∀ a ∈ X, ∀ y ∈ Y, a y ∈ Y) (hYcard : Nat.card Y = 4)
    (hcommH : ∀ h ∈ H, h * x = x * h)
    (hpair : letI := galoisModule hw2 x hx3 hfix;
      ∃ S : Set (LineOf (K := GaloisField 2 2) (V := Additive W)),
        S.ncard = 2 ∧ S.Nonempty ∧ S ≠ Set.univ ∧
        (∀ h : ↥H, S.image (fun L => lineMap (HLinHom hw2 x hx3 hfix H hcommH h) L) = S)) :
    letI := galoisModule hw2 x hx3 hfix
    ∃ (L M : LineOf (K := GaloisField 2 2) (V := Additive W)) (H0 : Subgroup ↥H) (d : ↥H),
      L ≠ M ∧ (X.subgroupOf H) ≤ H0 ∧ (d : MulAut W) ∈ D ∧ d * d = 1 ∧
      (∀ a : ↥H, a ∈ X.subgroupOf H → ∃ c : GaloisField 2 2, c ≠ 0 ∧
        ∀ v : Additive W,
          hGaloisLinearEquiv hw2 x hx3 hfix (a : MulAut W) (hcommH a a.2) v = c • v) := by
  letI := galoisModule hw2 x hx3 hfix
  obtain ⟨-, L, M, H0, d, hLM, hXleH0, hindex, hH0card, hH0comm, hH0mem, hdD, hd2, hdnot,
    hcover, hdL, hdM, hdfix⟩ :=
    sixfourteen_n2_pair_orders hw2 x hx3 hx_ord3 hfix hW hH hXG hXnorm hxgen hsG hs_ord2
      hs_not_cent hirr hD hDCX hDs hElem hDcard hYD hYinv hYcard hcommH hpair
  have hVf : Module.finrank (GaloisField 2 2) (Additive W) = 2 :=
    finrank_galoisModule hw2 x hx3 hfix hW
  have hd0sq : (d : MulAut W) * (d : MulAut W) = 1 := by
    have := congrArg Subtype.val hd2
    simpa using this
  have hgalD_L : lineMap (hGaloisLinearEquiv hw2 x hx3 hfix (d : MulAut W)
      (hcommH (d : MulAut W) d.2)) L = M := by
    rw [← HLinHom_apply]
    exact hdL
  have hgalD_M : lineMap (hGaloisLinearEquiv hw2 x hx3 hfix (d : MulAut W)
      (hcommH (d : MulAut W) d.2)) M = L := by
    rw [← HLinHom_apply]
    exact hdM
  refine ⟨L, M, H0, d, hLM, hXleH0, hdD, hd2, ?_⟩
  intro a ha
  have haH0 : a ∈ H0 := hXleH0 ha
  have hmem := (hH0mem a).mp haH0
  have hcomm_ad : (a : MulAut W) * (d : MulAut W) = (d : MulAut W) * (a : MulAut W) :=
    (hDCX (d : MulAut W) hdD (a : MulAut W) ha).symm
  have hgalA_L : lineMap (hGaloisLinearEquiv hw2 x hx3 hfix (a : MulAut W)
      (hcommH (a : MulAut W) a.2)) L = L := by
    rw [← HLinHom_apply]
    exact hmem.1
  have hgalA_M : lineMap (hGaloisLinearEquiv hw2 x hx3 hfix (a : MulAut W)
      (hcommH (a : MulAut W) a.2)) M = M := by
    rw [← HLinHom_apply]
    exact hmem.2
  have hcomm_lin : hGaloisLinearEquiv hw2 x hx3 hfix (a : MulAut W)
        (hcommH (a : MulAut W) a.2) *
      hGaloisLinearEquiv hw2 x hx3 hfix (d : MulAut W) (hcommH (d : MulAut W) d.2) =
      hGaloisLinearEquiv hw2 x hx3 hfix (d : MulAut W) (hcommH (d : MulAut W) d.2) *
        hGaloisLinearEquiv hw2 x hx3 hfix (a : MulAut W)
          (hcommH (a : MulAut W) a.2) := by
    have h1 : hGaloisLinearEquiv hw2 x hx3 hfix (a : MulAut W)
          (hcommH (a : MulAut W) a.2) *
        hGaloisLinearEquiv hw2 x hx3 hfix (d : MulAut W) (hcommH (d : MulAut W) d.2) =
        hGaloisLinearEquiv hw2 x hx3 hfix ((a : MulAut W) * (d : MulAut W))
          (hcommH _ (H.mul_mem a.2 d.2)) := by
      rw [hGaloisLinearEquiv_mul hw2 x hx3 hfix (a : MulAut W) (d : MulAut W)
        (hcommH (a : MulAut W) a.2) (hcommH (d : MulAut W) d.2)
        (hcommH _ (H.mul_mem a.2 d.2))]
      exact (LinearEquiv.mul_eq_trans _ _).symm
    have h2 : hGaloisLinearEquiv hw2 x hx3 hfix (d : MulAut W)
          (hcommH (d : MulAut W) d.2) *
        hGaloisLinearEquiv hw2 x hx3 hfix (a : MulAut W)
          (hcommH (a : MulAut W) a.2) =
        hGaloisLinearEquiv hw2 x hx3 hfix ((d : MulAut W) * (a : MulAut W))
          (hcommH _ (H.mul_mem d.2 a.2)) := by
      rw [hGaloisLinearEquiv_mul hw2 x hx3 hfix (d : MulAut W) (a : MulAut W)
        (hcommH (d : MulAut W) d.2) (hcommH (a : MulAut W) a.2)
        (hcommH _ (H.mul_mem d.2 a.2))]
      exact (LinearEquiv.mul_eq_trans _ _).symm
    rw [h1, h2]
    exact hgal_congr_eq hw2 x hx3 hfix hcomm_ad _ _
  obtain ⟨c, hc⟩ := exists_smul_one_of_commute_swap hVf hLM hgalA_L hgalA_M
    hgalD_L hgalD_M hcomm_lin
  refine ⟨c, ?_, hc⟩
  intro hc0
  have hzero : ∀ v : Additive W,
      hGaloisLinearEquiv hw2 x hx3 hfix (a : MulAut W) (hcommH (a : MulAut W) a.2) v = 0 := by
    intro v
    rw [hc v, hc0]
    simp
  obtain ⟨v, hv⟩ :=
    Module.finrank_pos_iff_exists_ne_zero.mp
      (by rw [hVf]; norm_num : 0 < Module.finrank (GaloisField 2 2) (Additive W))
  have h0 : hGaloisLinearEquiv hw2 x hx3 hfix (a : MulAut W) (hcommH (a : MulAut W) a.2) v =
      hGaloisLinearEquiv hw2 x hx3 hfix (a : MulAut W) (hcommH (a : MulAut W) a.2) 0 := by
    rw [hzero v, hzero 0]
  exact hv ((hGaloisLinearEquiv hw2 x hx3 hfix (a : MulAut W)
    (hcommH (a : MulAut W) a.2)).injective h0)

end XScalarPair

section UniqueOrderNine

variable {W : Type*} [CommGroup W] [Finite W]

private theorem eq_of_card_nine {H : Subgroup (MulAut W)} {H0 K : Subgroup ↥H} {d : ↥H}
    (hH0card : Nat.card H0 = 9) (hKcard : Nat.card K = 9)
    (hdnot : d ∉ H0) (hcover : ∀ b : ↥H, b ∈ H0 ∨ b * d⁻¹ ∈ H0) :
    K = H0 := by
  have hKle : K ≤ H0 := by
    by_contra hKle
    have hex : ∃ k0 : ↥H, k0 ∈ K ∧ k0 ∉ H0 := by
      by_contra h
      push Not at h
      exact hKle (fun x hx => h x hx)
    obtain ⟨k0, hk0K, hk0not⟩ := hex
    let k0' : ↥K := ⟨k0, hk0K⟩
    let K0 : Subgroup ↥K := (K ⊓ H0).subgroupOf K
    have hk0'not : k0'⁻¹ ∉ K0 := by
      intro hmem
      have hinv : (k0'⁻¹)⁻¹ ∈ K0 := K0.inv_mem hmem
      have hval : k0 ∈ K ⊓ H0 := hinv
      exact hk0not (Subgroup.mem_inf.mp hval).2
    have hright : ∀ b : ↥K, b * k0'⁻¹ ∈ K0 ∨ b ∈ K0 := by
      intro b
      by_cases hb : (b : ↥H) ∈ H0
      · right
        exact Subgroup.mem_inf.mpr ⟨b.2, hb⟩
      · left
        have hbcover : (b : ↥H) * d⁻¹ ∈ H0 := (hcover (b : ↥H)).resolve_left hb
        have hk0cover : k0 * d⁻¹ ∈ H0 := (hcover k0).resolve_left hk0not
        have hprod : ((b : ↥H) * d⁻¹) * (k0 * d⁻¹)⁻¹ ∈ H0 :=
          H0.mul_mem hbcover (H0.inv_mem hk0cover)
        have heq : ((b : ↥H) * k0⁻¹) = ((b : ↥H) * d⁻¹) * (k0 * d⁻¹)⁻¹ := by group
        have hKmem : (b : ↥H) * k0⁻¹ ∈ K := K.mul_mem b.2 (K.inv_mem hk0K)
        have hH0mem : (b : ↥H) * k0⁻¹ ∈ H0 := by
          rw [heq]
          exact hprod
        rw [Subgroup.mem_subgroupOf]
        show ((b * k0'⁻¹ : ↥K) : ↥H) ∈ K ⊓ H0
        rw [show ((b * k0'⁻¹ : ↥K) : ↥H) = (b : ↥H) * k0⁻¹ from rfl]
        exact Subgroup.mem_inf.mpr ⟨hKmem, hH0mem⟩
    have hidx : K0.index = 2 := by
      rw [Subgroup.index_eq_two_iff_exists_notMem_and]
      exact ⟨k0'⁻¹, hk0'not, fun b => hright b⟩
    have hcard := Subgroup.card_mul_index (H := K0)
    rw [hidx, hKcard] at hcard
    omega
  exact Subgroup.eq_of_le_of_card_ge hKle (by omega)

end UniqueOrderNine

section ZpowersThree

private theorem mem_zpowers_three {G : Type*} [Group G] {v : G} (hv : orderOf v = 3) :
    ∀ x ∈ Subgroup.zpowers v, x = 1 ∨ x = v ∨ x = v ^ 2 := by
  intro x hx
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hmod : v ^ a = v ^ (a % 3) := by
    have h := zpow_mod_orderOf v a
    rw [show (orderOf v : ℤ) = 3 by rw [hv]; norm_num] at h
    exact h.symm
  rw [hmod]
  have hlt : a % 3 < 3 := Int.emod_lt_of_pos a (by norm_num)
  have hge : 0 ≤ a % 3 := Int.emod_nonneg a (by norm_num)
  have hr : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
  rcases hr with h0 | h1 | h2
  · left; rw [h0]; simp
  · right; left; rw [h1, zpow_one]
  · right; right; rw [h2]
    norm_num

end ZpowersThree

section PairS3

variable {W : Type*} [CommGroup W] [Finite W]

theorem sixfourteen_n2_pair_S3 {W : Type} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hx_ord3 : orderOf x = 3)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16)
    {G X H D : Subgroup (MulAut W)} {s : MulAut W} {Y : Subgroup W}
    (hH : H = G ⊓ Subgroup.centralizer (X : Set (MulAut W)))
    (hXG : X ≤ G) (hXnorm : ∀ g ∈ G, ∀ y ∈ X, g * y * g⁻¹ ∈ X)
    (hxgen : X = Subgroup.zpowers x)
    (hsG : s ∈ G) (hs_ord2 : orderOf s = 2)
    (hs_not_cent : s ∉ Subgroup.centralizer (X : Set (MulAut W)))
    (hirr : ∀ Z : Subgroup W, (∀ g ∈ G, ∀ z ∈ Z, g z ∈ Z) → Z = ⊥ ∨ Z = ⊤)
    (hD : D ≤ G) (hDCX : ∀ d ∈ D, ∀ y ∈ X, d * y = y * d)
    (hDs : ∀ d ∈ D, d * s = s * d)
    (hElem : CFSG.Quasithin.IsElemAbelian2 D) (hDcard : Nat.card D = 2)
    (hYD : Y ≤ fixV D)
    (hYinv : ∀ a ∈ X, ∀ y ∈ Y, a y ∈ Y) (hYcard : Nat.card Y = 4)
    (hcommH : ∀ h ∈ H, h * x = x * h)
    (hpair : letI := galoisModule hw2 x hx3 hfix;
      ∃ S : Set (LineOf (K := GaloisField 2 2) (V := Additive W)),
        S.ncard = 2 ∧ S.Nonempty ∧ S ≠ Set.univ ∧
        (∀ h : ↥H, S.image (fun L => lineMap (HLinHom hw2 x hx3 hfix H hcommH h) L) = S)) :
    letI := galoisModule hw2 x hx3 hfix
    ∃ (L M : LineOf (K := GaloisField 2 2) (V := Additive W)) (H0 : Subgroup ↥H)
      (v : ↥H0) (d : ↥H) (s0 : MulAut W),
      L ≠ M ∧ (X.subgroupOf H) ≤ H0 ∧ Nat.card H0 = 9 ∧
      ((X.subgroupOf H).subgroupOf H0) ⊔ Subgroup.zpowers v = ⊤ ∧
      ((X.subgroupOf H).subgroupOf H0) ⊓ Subgroup.zpowers v = ⊥ ∧
      v ∉ (X.subgroupOf H).subgroupOf H0 ∧ orderOf v = 3 ∧
      (d : MulAut W) ∈ D ∧ d * d = 1 ∧ d ∉ H0 ∧
      (∀ b : ↥H, b ∈ H0 ∨ b * d⁻¹ ∈ H0) ∧
      (d : MulAut W) * (((v : ↥H0) : ↥H) : MulAut W) * (d : MulAut W)⁻¹ =
        (((v ^ 2 : ↥H0) : ↥H) : MulAut W) ∧
      (s0 = s ∨ s0 = s * (d : MulAut W)) ∧
      s0 ∈ G ∧ s0 * s0 = 1 ∧ s0 ∉ H ∧
      s0 * x * s0⁻¹ = x ^ 2 ∧
      s0 * (((v : ↥H0) : ↥H) : MulAut W) * s0⁻¹ = (((v : ↥H0) : ↥H) : MulAut W) ∧
      s0 * (d : MulAut W) * s0⁻¹ = (d : MulAut W) ∧
      (∀ h : MulAut W, h ∈ Subgroup.zpowers (((v : ↥H0) : ↥H) : MulAut W) ⊔
        Subgroup.zpowers (d : MulAut W) → s0 * h = h * s0) := by
  letI := galoisModule hw2 x hx3 hfix
  obtain ⟨L, M, H0, v, d, hLM, hXleH0, hsupV, hdisj, hH0card, hH0mem, hH0comm, hvnotX, hvord,
    hdD, hd2, hdnot, hcover, hdv, hUchar, hdL, hdM⟩ :=
    sixfourteen_n2_pair_torus hw2 x hx3 hx_ord3 hfix hW hH hXG hXnorm hxgen hsG hs_ord2
      hs_not_cent hirr hD hDCX hDs hElem hDcard hYD hYinv hYcard hcommH hpair
  let v0 : MulAut W := (((v : ↥H0) : ↥H) : MulAut W)
  let d0 : MulAut W := (d : MulAut W)
  have hxX : x ∈ X := by rw [hxgen]; exact Subgroup.mem_zpowers x
  have hs2 : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs_ord2] at h
    simpa [pow_two] using h
  have hd0sq : d0 * d0 = 1 := by
    have := congrArg Subtype.val hd2
    simpa [d0] using this
  have hs_not_H : s ∉ H := by
    intro hsH
    apply hs_not_cent
    rw [hH] at hsH
    exact (Subgroup.mem_inf.mp hsH).2
  have hHnorm : ∀ g ∈ G, ∀ h ∈ H, g * h * g⁻¹ ∈ H :=
    inf_centralizer_normal_in_G hH hXnorm
  let cs : ↥H →* ↥H :=
  { toFun := fun h => ⟨s * (h : MulAut W) * s⁻¹, hHnorm s hsG (h : MulAut W) h.2⟩
    map_one' := by
      apply Subtype.ext
      simp
    map_mul' := by
      intro a b
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      group }
  have hcs_inj : Function.Injective cs := by
    intro a b hab
    have h' : s * (a : MulAut W) * s⁻¹ = s * (b : MulAut W) * s⁻¹ := congrArg Subtype.val hab
    apply Subtype.ext
    have := congrArg (fun z => s⁻¹ * z * s) h'
    simpa [mul_assoc] using this
  let K : Subgroup ↥H := H0.map cs
  have hKcard : Nat.card K = 9 := by
    rw [Subgroup.card_map_of_injective hcs_inj, hH0card]
  have hK : K = H0 := eq_of_card_nine hH0card hKcard hdnot hcover
  have hcs_mem : ∀ h : ↥H, h ∈ H0 → cs h ∈ H0 := by
    intro h hh
    have : cs h ∈ K := Subgroup.mem_map_of_mem cs hh
    rwa [hK] at this
  let ψ : ↥H0 →* ↥H0 :=
  { toFun := fun u => ⟨cs (u : ↥H), hcs_mem (u : ↥H) u.2⟩
    map_one' := by
      apply Subtype.ext
      exact map_one cs
    map_mul' := by
      intro a b
      apply Subtype.ext
      exact map_mul cs (a : ↥H) (b : ↥H) }
  have hψspec : ∀ u : ↥H0, ((ψ u : ↥H0) : ↥H) = cs (u : ↥H) := fun u => rfl
  have hψinj : Function.Injective ψ := by
    intro a b hab
    apply Subtype.ext
    apply hcs_inj
    have h := congrArg (fun z : ↥H0 => (z : ↥H)) hab
    rwa [hψspec a, hψspec b] at h
  have hψv_ambient : (((ψ v : ↥H0) : ↥H) : MulAut W) = s * v0 * s⁻¹ := by
    rw [hψspec v]
    rfl
  have hsd : d0 * s = s * d0 := hDs d hdD
  have hsdinv : s⁻¹ * d0⁻¹ = d0⁻¹ * s⁻¹ := by
    calc s⁻¹ * d0⁻¹ = (d0 * s)⁻¹ := (mul_inv_rev d0 s).symm
      _ = (s * d0)⁻¹ := by rw [hsd]
      _ = d0⁻¹ * s⁻¹ := mul_inv_rev s d0
  have hdv0 : d0 * v0 * d0⁻¹ = v0 ^ 2 := by simpa [v0, d0, Subgroup.coe_pow] using hdv
  have hconj : d0 * (((ψ v : ↥H0) : ↥H) : MulAut W) * d0⁻¹ =
      ((((ψ v : ↥H0) ^ 2 : ↥H0) : ↥H) : MulAut W) := by
    have hψv2 : ((((ψ v : ↥H0) ^ 2 : ↥H0) : ↥H) : MulAut W) = (s * v0 * s⁻¹) ^ 2 := by
      rw [show ((((ψ v : ↥H0) ^ 2 : ↥H0) : ↥H) : MulAut W) =
          (((ψ v : ↥H0) : ↥H) : MulAut W) ^ 2 from by push_cast; rfl]
      exact congrArg (fun z : MulAut W => z ^ 2) hψv_ambient
    rw [hψv_ambient, hψv2, pow_two]
    calc d0 * (s * v0 * s⁻¹) * d0⁻¹ = (d0 * s) * v0 * (s⁻¹ * d0⁻¹) := by group
      _ = (s * d0) * v0 * (d0⁻¹ * s⁻¹) := by rw [hsd, hsdinv]
      _ = s * (d0 * v0 * d0⁻¹) * s⁻¹ := by group
      _ = s * v0 ^ 2 * s⁻¹ := by rw [hdv0]
      _ = s * (v0 * v0) * s⁻¹ := by rw [pow_two]
      _ = (s * v0 * s⁻¹) * (s * v0 * s⁻¹) := by group
  have hmemv : ψ v ∈ Subgroup.zpowers v := hUchar (ψ v) hconj
  have hvne : v ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hvord
    omega
  have hψv_ne : ψ v ≠ 1 := by
    intro h
    apply hvne
    apply hψinj
    rw [h, map_one]
  have hv0ord : orderOf v0 = 3 := by
    have h1 : orderOf v = orderOf (v : ↥H) := Subgroup.orderOf_mk (v : ↥H) v.2
    have h2 : orderOf (v : ↥H) = orderOf v0 :=
      Subgroup.orderOf_mk ((v : ↥H) : MulAut W) (v : ↥H).2
    rw [← h2, ← h1]
    exact hvord
  have hv03 : v0 ^ 3 = 1 := by
    have := pow_orderOf_eq_one v0
    rwa [hv0ord] at this
  have hsd_conj : s * d0 * s⁻¹ = d0 := by
    calc s * d0 * s⁻¹ = (s * d0) * s⁻¹ := by group
      _ = (d0 * s) * s⁻¹ := by rw [hsd.symm]
      _ = d0 := by group
  have hcomm_of_conj : ∀ (t : MulAut W), t * v0 * t⁻¹ = v0 → t * d0 * t⁻¹ = d0 →
      ∀ h : MulAut W, h ∈ Subgroup.zpowers v0 ⊔ Subgroup.zpowers d0 → t * h = h * t := by
    intro t hv hd h hh
    have hcent : Subgroup.zpowers v0 ⊔ Subgroup.zpowers d0 ≤
        Subgroup.centralizer ({t} : Set (MulAut W)) := by
      apply sup_le
      · apply Subgroup.zpowers_le.mpr
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        calc t * v0 = (t * v0 * t⁻¹) * t := by group
          _ = v0 * t := by rw [hv]
      · apply Subgroup.zpowers_le.mpr
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        calc t * d0 = (t * d0 * t⁻¹) * t := by group
          _ = d0 * t := by rw [hd]
    exact (Subgroup.mem_centralizer_iff.mp (hcent hh)) t (Set.mem_singleton t)
  have hψv_cases := mem_zpowers_three hvord (ψ v) hmemv
  rcases hψv_cases with h1 | h2 | h2
  · exact absurd h1 hψv_ne
  ·
    have hsv : s * v0 * s⁻¹ = v0 := by
      have h := hψspec v
      rw [h2] at h
      have h' : cs v = (v : ↥H) := h.symm
      have h'' : s * ((v : ↥H) : MulAut W) * s⁻¹ = ((v : ↥H) : MulAut W) := congrArg Subtype.val h'
      exact h''
    refine ⟨L, M, H0, v, d, s, hLM, hXleH0, hH0card, hsupV, hdisj, hvnotX, hvord, hdD, hd2,
      hdnot, hcover, hdv, Or.inl rfl, hsG, hs2, hs_not_H, ?_, hsv, hsd_conj, ?_⟩
    · have hne : s * x * s⁻¹ ≠ x := fun h =>
        hs_not_cent (mem_centralizer_of_conj_eq_self hxgen h)
      exact conj_eq_sq_of_zpowers_three_of_mem hxgen hx_ord3 (hXnorm s hsG x hxX) hne
    · exact hcomm_of_conj s hsv hsd_conj
  ·
    have hsv : s * v0 * s⁻¹ = v0 ^ 2 := by
      have h := hψspec v
      rw [h2] at h
      have h' : cs v = ((v ^ 2 : ↥H0) : ↥H) := h.symm
      have h'' : s * ((v : ↥H) : MulAut W) * s⁻¹ =
          (((v ^ 2 : ↥H0) : ↥H) : MulAut W) := congrArg Subtype.val h'
      rw [h''] 
      rfl
    have hvs0 : (s * d0) * v0 * (s * d0)⁻¹ = v0 := by
      calc (s * d0) * v0 * (s * d0)⁻¹ = s * (d0 * v0 * d0⁻¹) * s⁻¹ := by group
        _ = s * v0 ^ 2 * s⁻¹ := by rw [hdv0]
        _ = s * (v0 * v0) * s⁻¹ := by rw [pow_two]
        _ = (s * v0 * s⁻¹) * (s * v0 * s⁻¹) := by group
        _ = (v0 ^ 2) * (v0 ^ 2) := by rw [hsv]
        _ = (v0 ^ 2) ^ 2 := by group
        _ = v0 := by
            rw [show (v0 ^ 2) ^ 2 = v0 ^ 4 by group]
            rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_add, hv03, one_mul, pow_one]
    have hds0 : (s * d0) * d0 * (s * d0)⁻¹ = d0 := by
      calc (s * d0) * d0 * (s * d0)⁻¹ = s * d0 * (d0 * d0⁻¹) * s⁻¹ := by group
        _ = s * d0 * s⁻¹ := by rw [mul_inv_cancel, mul_one]
        _ = d0 := hsd_conj
    refine ⟨L, M, H0, v, d, s * d0, hLM, hXleH0, hH0card, hsupV, hdisj, hvnotX, hvord, hdD, hd2,
      hdnot, hcover, hdv, Or.inr rfl, ?_, ?_, ?_, ?_, hvs0, hds0, ?_⟩
    · exact G.mul_mem hsG (hD hdD)
    · calc (s * d0) * (s * d0) = s * (d0 * s) * d0 := by group
        _ = s * (s * d0) * d0 := by rw [hsd]
        _ = (s * s) * (d0 * d0) := by group
        _ = 1 := by rw [hs2, hd0sq, one_mul]
    · intro hmem
      apply hs_not_H
      have hd0H : d0 ∈ H := d.2
      have : s = (s * d0) * d0⁻¹ := by group
      rw [this]
      exact H.mul_mem hmem (H.inv_mem hd0H)
    · have hxd : d0 * x = x * d0 := hDCX d hdD x hxX
      have hsx : s * x * s⁻¹ = x ^ 2 := by
        have hne : s * x * s⁻¹ ≠ x := fun h =>
          hs_not_cent (mem_centralizer_of_conj_eq_self hxgen h)
        exact conj_eq_sq_of_zpowers_three_of_mem hxgen hx_ord3 (hXnorm s hsG x hxX) hne
      calc (s * d0) * x * (s * d0)⁻¹ = s * (d0 * x * d0⁻¹) * s⁻¹ := by group
        _ = s * x * s⁻¹ := by rw [show d0 * x * d0⁻¹ = x by
              rw [hxd]; group]
        _ = x ^ 2 := hsx
    · exact hcomm_of_conj (s * d0) hvs0 hds0

end PairS3

end CFSG.LocalAnalysis.WeakClosure81
