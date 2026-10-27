module

public import CFSG.RankThree.PartOne.S10.PlaneContract
import CFSG.RankThree.PartOne.S10.PlaneAuxiliary

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven

namespace PlaneSemidirect

@[expose] def restrictHom {G D : Type*} [Group G] [Group D] (φ : G →* MulAut D) (E : Subgroup D)
    (h : ∀ g : G, ∀ e ∈ E, φ g e ∈ E) : G →* MulAut E where
  toFun g :=
    { toFun := fun e => ⟨φ g e, h g e e.2⟩
      invFun := fun e => ⟨(φ g)⁻¹ e, by simpa [map_inv] using h g⁻¹ e e.2⟩
      left_inv := fun e => Subtype.ext (by simp)
      right_inv := fun e => Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  map_one' := MulEquiv.ext fun e => Subtype.ext (by simp)
  map_mul' := fun g g' => MulEquiv.ext fun e => Subtype.ext (by simp)

theorem restrictHom_apply {G D : Type*} [Group G] [Group D] (φ : G →* MulAut D) (E : Subgroup D)
    (h : ∀ g : G, ∀ e ∈ E, φ g e ∈ E) (g : G) (e : E) :
    ((restrictHom φ E h g e : E) : D) = φ g e := rfl

section Kernel

variable {B S : Type} [Group B] [Group S] [MulDistribMulAction B S]

theorem eq_bot_of_normal_isPGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [Finite B] [Finite S]
    (hB : IsPGroup p B) (hS : IsPGroup 2 S) (hfaith : ∀ c : B, (∀ s : S, c • s = s) → c = 1)
    (T : Subgroup (S ⋊[MulDistribMulAction.toMulAut B S] B)) [T.Normal] (hT : IsPGroup p T) :
    T = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := S ⋊[MulDistribMulAction.toMulAut B S] B with hK
  have hS2 : IsPGroup 2 (SemidirectProduct.inl : S →* K).range := by
    rintro ⟨_, ⟨s, rfl⟩⟩
    obtain ⟨k, hk⟩ := hS s
    exact ⟨k, Subtype.ext (by simp [← map_pow, hk])⟩
  have hnormS : (SemidirectProduct.inl : S →* K).range.Normal := by
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  have hdis : Disjoint T (SemidirectProduct.inl : S →* K).range :=
    IsPGroup.disjoint_of_ne p 2 hp2 T _ hT hS2
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hcomm : ∀ t : S, x * SemidirectProduct.inl t = SemidirectProduct.inl t * x := by
    intro t
    have h1 : x * SemidirectProduct.inl t * x⁻¹ * (SemidirectProduct.inl t)⁻¹ ∈ T := by
      have h2 := (inferInstance : T.Normal).conj_mem x⁻¹ (T.inv_mem hx) (SemidirectProduct.inl t)
      have h3 := T.mul_mem hx h2
      convert h3 using 1
      group
    have h2 : x * SemidirectProduct.inl t * x⁻¹ * (SemidirectProduct.inl t)⁻¹ ∈
        (SemidirectProduct.inl : S →* K).range := by
      refine (SemidirectProduct.inl : S →* K).range.mul_mem
        (hnormS.conj_mem _ ⟨t, rfl⟩ x) ((SemidirectProduct.inl : S →* K).range.inv_mem ⟨t, rfl⟩)
    have h3 : x * SemidirectProduct.inl t * x⁻¹ * (SemidirectProduct.inl t)⁻¹ = 1 := by
      have := hdis.le_bot ⟨h1, h2⟩
      rwa [Subgroup.mem_bot] at this
    calc x * SemidirectProduct.inl t
        = (x * SemidirectProduct.inl t * x⁻¹ * (SemidirectProduct.inl t)⁻¹) *
          SemidirectProduct.inl t * x := by group
      _ = SemidirectProduct.inl t * x := by rw [h3, one_mul]
  obtain ⟨s, c⟩ := x
  have hinner : ∀ t : S, c • t = s⁻¹ * t * s := by
    intro t
    have h := congrArg SemidirectProduct.left (hcomm t)
    simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
      map_one, MulAut.one_apply] at h
    calc c • t = s⁻¹ * (s * (c • t)) := by group
      _ = s⁻¹ * (t * s) := by rw [show s * (c • t) = t * s from h]
      _ = s⁻¹ * t * s := by group
  have hc1 : c = 1 := PlaneAux.eq_one_of_smul_eq_inner hp hp2 hB hS hfaith hinner
  subst hc1
  have hxs : (⟨s, 1⟩ : K) = SemidirectProduct.inl s := rfl
  have hmem : (⟨s, 1⟩ : K) ∈ T ⊓ (SemidirectProduct.inl : S →* K).range := ⟨hx, s, rfl⟩
  have := hdis.le_bot hmem
  rwa [Subgroup.mem_bot] at this

theorem conj_inr_inl (b : B) (s : S) :
    (SemidirectProduct.inr b : S ⋊[MulDistribMulAction.toMulAut B S] B) *
      SemidirectProduct.inl s * (SemidirectProduct.inr b)⁻¹ = SemidirectProduct.inl (b • s) := by
  have h := SemidirectProduct.inl_aut (φ := MulDistribMulAction.toMulAut B S) b s
  change (SemidirectProduct.inl (b • s) : S ⋊[MulDistribMulAction.toMulAut B S] B) = _ at h
  rw [h, map_inv]

theorem pow_smul_mem_of_smul_mem (c : B) {U : Subgroup S} (hcU : ∀ u ∈ U, c • u ∈ U) (n : ℕ)
    {u : S} (hu : u ∈ U) : (c ^ n) • u ∈ U := by
  induction n with
  | zero => simpa using hu
  | succ n ih => rw [pow_succ', mul_smul]; exact hcU _ ih

theorem zpowers_smul_mem_of_smul_mem [Finite B] (c : B) {U : Subgroup S}
    (hcU : ∀ u ∈ U, c • u ∈ U) {w : B} (hw : w ∈ Subgroup.zpowers c) {u : S} (hu : u ∈ U) :
    w • u ∈ U := by
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hw)
  exact pow_smul_mem_of_smul_mem c hcU n hu

end Kernel

section Rank

variable {B S D : Type} [Group B] [Group S] [Group D] [MulDistribMulAction B S]
  (β : (S ⋊[MulDistribMulAction.toMulAut B S] B) →* MulAut D)

theorem commute_inl_inr_of_fixed (d : D) (k : S ⋊[MulDistribMulAction.toMulAut B S] B)
    (h : β k d = d) :
    Commute (SemidirectProduct.inl d : D ⋊[β] (S ⋊[MulDistribMulAction.toMulAut B S] B))
      (SemidirectProduct.inr k) := by
  have h1 := SemidirectProduct.inl_aut (φ := β) k d
  rw [h, map_inv] at h1
  change _ * _ = _ * _
  calc SemidirectProduct.inl d * SemidirectProduct.inr k
      = (SemidirectProduct.inr k * SemidirectProduct.inl d * (SemidirectProduct.inr k)⁻¹) *
        SemidirectProduct.inr k := by rw [← h1]
    _ = SemidirectProduct.inr k * SemidirectProduct.inl d := by group

theorem commute_inr_inl_of_smul_eq (c : B) (u : S) (h : c • u = u) :
    Commute (SemidirectProduct.inr c : S ⋊[MulDistribMulAction.toMulAut B S] B)
      (SemidirectProduct.inl u) := by
  have h1 := SemidirectProduct.inl_aut (φ := MulDistribMulAction.toMulAut B S) c u
  change (SemidirectProduct.inl (c • u) : S ⋊[MulDistribMulAction.toMulAut B S] B) = _ at h1
  rw [h, map_inv] at h1
  change _ * _ = _ * _
  calc SemidirectProduct.inr c * SemidirectProduct.inl u
      = (SemidirectProduct.inr c * SemidirectProduct.inl u * (SemidirectProduct.inr c)⁻¹) *
        SemidirectProduct.inr c := by group
    _ = SemidirectProduct.inl u * SemidirectProduct.inr c := by rw [← h1]

theorem mem_normalizer_of_commutes {G : Type*} [Group G] {U : Subgroup G} {x : G}
    (h : ∀ u ∈ U, x * u = u * x) : x ∈ Subgroup.normalizer (U : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    have e : x * g * x⁻¹ = g := by
      calc x * g * x⁻¹ = g * x * x⁻¹ := by rw [h g hg]
        _ = g := by group
    rwa [e]
  · intro hg
    have h1 := h _ hg
    have e : x * g * x⁻¹ = g := by
      calc x * g * x⁻¹ = x⁻¹ * (x * (x * g * x⁻¹)) := by group
        _ = x⁻¹ * ((x * g * x⁻¹) * x) := by rw [h1]
        _ = g := by group
    rwa [e] at hg

theorem zpow_apply_eq_of_apply_eq {G D : Type*} [Group G] [Group D] (φ : G →* MulAut D) {g : G}
    {d : D} (h : φ g d = d) (m : ℤ) : φ (g ^ m) d = d := by
  have hmem : φ g ∈ MulAction.stabilizer (MulAut D) d := h
  rw [map_zpow]
  exact (MulAction.stabilizer (MulAut D) d).zpow_mem hmem m

theorem zpow_smul_eq_of_smul_eq (c : B) {u : S} (h : c • u = u) (m : ℤ) : (c ^ m) • u = u := by
  have hmem : c ∈ MulAction.stabilizer B u := h
  exact (MulAction.stabilizer B u).zpow_mem hmem m

theorem conj_inr_inr_inr_inl (g : B) (u : S) :
    (SemidirectProduct.inr (SemidirectProduct.inr g) :
        D ⋊[β] (S ⋊[MulDistribMulAction.toMulAut B S] B)) *
      SemidirectProduct.inr (SemidirectProduct.inl u) *
      (SemidirectProduct.inr (SemidirectProduct.inr g))⁻¹ =
    SemidirectProduct.inr (SemidirectProduct.inl (g • u)) := by
  have h := SemidirectProduct.inl_aut (φ := MulDistribMulAction.toMulAut B S) g u
  change (SemidirectProduct.inl (g • u) : S ⋊[MulDistribMulAction.toMulAut B S] B) = _ at h
  rw [h]
  simp only [map_mul, map_inv]

variable [Finite B] [Finite S] [Finite D]

theorem le_evenRank_of_fixed {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hS : IsPGroup 2 S) {s : S}
    (hs : s ≠ 1) {E : Subgroup D} (hE : IsElementaryAbelian p E)
    (hfix : ∀ e ∈ E, β (SemidirectProduct.inl s) e = e) {k : ℕ} (hk : Nat.card E = p ^ k) :
    k ≤ evenRank (D ⋊[β] (S ⋊[MulDistribMulAction.toMulAut B S] B)) := by
  have : Fact p.Prime := ⟨hp⟩
  have := hE
  let ι : S →* D ⋊[β] (S ⋊[MulDistribMulAction.toMulAut B S] B) :=
    SemidirectProduct.inr.comp SemidirectProduct.inl
  have hι : Function.Injective ι :=
    SemidirectProduct.inr_injective.comp SemidirectProduct.inl_injective
  refine PlaneAux.le_evenRank_of_hom_normalizes hp hp2 (A := E) (fun a b => ?_) (fun a => ?_) hk
    (SemidirectProduct.inl.comp E.subtype)
    (SemidirectProduct.inl_injective.comp E.subtype_injective)
    (U := (Subgroup.zpowers s).map ι) ?_ ?_ ?_
  · exact hE.is_comm.comm a b
  · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p E) a
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ hι, Subgroup.zpowers_eq_bot]
    exact hs
  · exact (hS.to_subgroup (Subgroup.zpowers s)).map ι
  · intro a
    refine mem_normalizer_of_commutes fun u hu => ?_
    obtain ⟨t, ht, rfl⟩ := hu
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    have hc : Commute (SemidirectProduct.inl (a : D) :
        D ⋊[β] (S ⋊[MulDistribMulAction.toMulAut B S] B)) (ι s) :=
      commute_inl_inr_of_fixed β a (SemidirectProduct.inl s) (hfix a a.2)
    rw [map_zpow]
    exact (hc.zpow_right m).eq

theorem succ_le_evenRank_of_normalizes {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hS : IsPGroup 2 S)
    {U : Subgroup S} (hU : U ≠ ⊥) {E : Subgroup D} (hE : IsElementaryAbelian p E)
    (hEU : ∀ u ∈ U, ∀ e ∈ E, β (SemidirectProduct.inl u) e = e) {c : B} (hc1 : c ≠ 1)
    (hcp : c ^ p = 1) (hcE : ∀ e ∈ E, β (SemidirectProduct.inr c) e = e)
    (hcU : ∀ u ∈ U, c • u ∈ U) {k : ℕ} (hk : Nat.card E = p ^ k) :
    k + 1 ≤ evenRank (D ⋊[β] (S ⋊[MulDistribMulAction.toMulAut B S] B)) := by
  have : Fact p.Prime := ⟨hp⟩
  have := hE
  let ι : S →* D ⋊[β] (S ⋊[MulDistribMulAction.toMulAut B S] B) :=
    SemidirectProduct.inr.comp SemidirectProduct.inl
  have hι : Function.Injective ι :=
    SemidirectProduct.inr_injective.comp SemidirectProduct.inl_injective
  let f₁ : E →* D ⋊[β] (S ⋊[MulDistribMulAction.toMulAut B S] B) :=
    SemidirectProduct.inl.comp E.subtype
  let f₂ : Subgroup.zpowers c →* D ⋊[β] (S ⋊[MulDistribMulAction.toMulAut B S] B) :=
    (SemidirectProduct.inr.comp (SemidirectProduct.inr.comp (MonoidHom.id B))).comp
      (Subgroup.zpowers c).subtype
  have hcomm : ∀ (e : E) (w : Subgroup.zpowers c), Commute (f₁ e) (f₂ w) := by
    intro e w
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp w.2
    have h1 : β (SemidirectProduct.inr ((w : B))) e = e := by
      have h2 := zpow_apply_eq_of_apply_eq β (hcE e e.2) m
      rw [← map_zpow, hm] at h2
      exact h2
    exact commute_inl_inr_of_fixed β e (SemidirectProduct.inr (w : B)) h1
  let f : (E × Subgroup.zpowers c) →* D ⋊[β] (S ⋊[MulDistribMulAction.toMulAut B S] B) :=
    f₁.noncommCoprod f₂ hcomm
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨e, w⟩ h
    have h' : (SemidirectProduct.inl (e : D) : D ⋊[β] (S ⋊[MulDistribMulAction.toMulAut B S] B)) *
        SemidirectProduct.inr (SemidirectProduct.inr (w : B)) = 1 := h
    have hl := congrArg SemidirectProduct.left h'
    have hr := congrArg SemidirectProduct.right h'
    simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, SemidirectProduct.left_inr, SemidirectProduct.right_inr,
      SemidirectProduct.one_left, SemidirectProduct.one_right, map_one, mul_one, one_mul] at hl hr
    have he : e = 1 := Subtype.ext hl
    have hw : w = 1 := Subtype.ext (SemidirectProduct.inr_injective (by
      rw [hr, Subgroup.coe_one, map_one]))
    rw [he, hw]
    rfl
  have hA : Nat.card (E × Subgroup.zpowers c) = p ^ (k + 1) := by
    rw [Nat.card_prod, hk, Nat.card_zpowers, orderOf_eq_prime hcp hc1, pow_succ]
  have hzcomm : ∀ w₁ w₂ : Subgroup.zpowers c, w₁ * w₂ = w₂ * w₁ := by
    intro w₁ w₂
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp w₁.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp w₂.2
    refine Subtype.ext ?_
    change (w₁ : B) * w₂ = w₂ * w₁
    rw [← hi, ← hj]
    exact (Commute.zpow_zpow_self c i j).eq
  refine PlaneAux.le_evenRank_of_hom_normalizes hp hp2 (A := E × Subgroup.zpowers c)
    (fun a b => Prod.ext (hE.is_comm.comm a.1 b.1) (hzcomm a.2 b.2)) (fun a => Prod.ext ?_ ?_) hA f
    hf (U := U.map ι) ?_ ?_ ?_
  · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p E) a.1
  · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp a.2.2
    refine Subtype.ext ?_
    change ((a.2 : B)) ^ p = 1
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hcp, one_zpow]
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ hι]
    exact hU
  · exact (hS.to_subgroup U).map ι
  · intro a
    have hmul : f a = f₁ a.1 * f₂ a.2 := MonoidHom.noncommCoprod_apply _ _ _ _
    have h1 : f₁ a.1 ∈ Subgroup.normalizer ((U.map ι : Subgroup _) : Set _) := by
      refine mem_normalizer_of_commutes fun u' hu' => ?_
      obtain ⟨u, hu, rfl⟩ := hu'
      exact (commute_inl_inr_of_fixed β a.1 (SemidirectProduct.inl u)
        (hEU u hu a.1 a.1.2)).eq
    have h2 : f₂ a.2 ∈ Subgroup.normalizer ((U.map ι : Subgroup _) : Set _) := by
      have hw := a.2.2
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨(a.2 : B) • u, zpowers_smul_mem_of_smul_mem c hcU hw hu,
          (conj_inr_inr_inr_inl β (a.2 : B) u).symm⟩
      · rintro ⟨u, hu, hux⟩
        refine ⟨(a.2 : B)⁻¹ • u, zpowers_smul_mem_of_smul_mem c hcU
          (Subgroup.inv_mem _ hw) hu, ?_⟩
        have h3 := conj_inr_inr_inr_inl β (a.2 : B)⁻¹ u
        have h4 : (SemidirectProduct.inr (SemidirectProduct.inl u) :
            D ⋊[β] (S ⋊[MulDistribMulAction.toMulAut B S] B)) =
            SemidirectProduct.inr (SemidirectProduct.inr (a.2 : B)) * x *
              (SemidirectProduct.inr (SemidirectProduct.inr (a.2 : B)))⁻¹ := hux
        have h6 : (SemidirectProduct.inr (SemidirectProduct.inl ((a.2 : B)⁻¹ • u)) :
            D ⋊[β] (S ⋊[MulDistribMulAction.toMulAut B S] B)) = x := by
          rw [← h3, map_inv, map_inv, h4]
          group
        exact h6
    rw [hmul]
    exact Subgroup.mul_mem _ h1 h2

theorem succ_le_evenRank_of_fixed {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hS : IsPGroup 2 S)
    {U : Subgroup S} (hU : U ≠ ⊥) {E : Subgroup D} (hE : IsElementaryAbelian p E)
    (hEU : ∀ u ∈ U, ∀ e ∈ E, β (SemidirectProduct.inl u) e = e) {c : B} (hc1 : c ≠ 1)
    (hcp : c ^ p = 1) (hcE : ∀ e ∈ E, β (SemidirectProduct.inr c) e = e)
    (hcU : ∀ u ∈ U, c • u = u) {k : ℕ} (hk : Nat.card E = p ^ k) :
    k + 1 ≤ evenRank (D ⋊[β] (S ⋊[MulDistribMulAction.toMulAut B S] B)) :=
  succ_le_evenRank_of_normalizes β hp hp2 hS hU hE hEU hc1 hcp hcE
    (fun u hu => by rw [hcU u hu]; exact hu) hk

end Rank


end PlaneSemidirect

end CFSG.RankThree.PartOne
