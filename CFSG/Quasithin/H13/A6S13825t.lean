module

public import CFSG.Quasithin.H13.A6S13825m
public import CFSG.Quasithin.EmptyFaithful.SzN2Lin

public section

namespace CFSG.Quasithin.H13.A6.L13825

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Quasithin.SBd8.Flag CFSG.QuasithinUnique

variable {Y : Type} [Group Y] {n : ℕ}

theorem exists_pow_mul_eq {K : Subgroup Y} {k t : Y} (hk : k ∈ K)
    (ht : t ∈ Subgroup.normalizer (K : Set Y)) (N : ℕ) :
    ∃ k' ∈ K, (k * t) ^ N = k' * t ^ N := by
  induction N with
  | zero => exact ⟨1, K.one_mem, by simp⟩
  | succ N ih =>
    obtain ⟨k', hk', h⟩ := ih
    have htN : t ^ N ∈ Subgroup.normalizer (K : Set Y) := Subgroup.pow_mem _ ht N
    refine ⟨k' * (t ^ N * k * (t ^ N)⁻¹), K.mul_mem hk'
      ((Subgroup.mem_normalizer_iff.mp htN k).mp hk), ?_⟩
    rw [pow_succ, h, pow_succ]
    group

theorem inf_centralizer_eq_bot [Finite Y] {H K T : Subgroup Y}
    (hKn : H ≤ Subgroup.normalizer (K : Set Y)) (hHKT : H ≤ K ⊔ T) (hTH : T ≤ H)
    (hT : IsPGroup 2 ↥T) (hZ : ∀ k ∈ K, (∀ k' ∈ K, k * k' = k' * k) → k = 1)
    (hO2 : ∀ Q : Subgroup Y, Q ≤ H → (Q.subgroupOf H).Normal → IsPGroup 2 ↥Q → Q = ⊥) :
    H ⊓ Subgroup.centralizer (K : Set Y) = ⊥ := by
  refine hO2 _ inf_le_left ⟨fun x hx h => ?_⟩ fun c => ?_
  · obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)
    rw [Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    refine Subgroup.mem_inf.mpr ⟨H.mul_mem (H.mul_mem h.2 hxH) (H.inv_mem h.2), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : (h : Y)⁻¹ * k * h ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (K : Set Y)).inv_mem (hKn h.2)) k).mp hk
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hxC _ hk'
    calc k * ((h : Y) * x * (h : Y)⁻¹)
        = (h : Y) * ((h : Y)⁻¹ * k * h * x) * (h : Y)⁻¹ := by group
      _ = (h : Y) * (x * ((h : Y)⁻¹ * k * h)) * (h : Y)⁻¹ := by rw [h1]
      _ = (h : Y) * x * (h : Y)⁻¹ * k := by group
  · obtain ⟨hcH, hcC⟩ := Subgroup.mem_inf.mp c.2
    obtain ⟨k, hk, t, ht, hc⟩ :=
      (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes (hTH.trans hKn)).mp (hHKT hcH)
    obtain ⟨m, hm⟩ := hT ⟨t, ht⟩
    have htm : t ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    obtain ⟨k', hk', hpow⟩ := exists_pow_mul_eq hk (hKn (hTH ht)) (2 ^ m)
    rw [htm, mul_one, ← hc] at hpow
    have hC' : (c : Y) ^ 2 ^ m ∈ Subgroup.centralizer (K : Set Y) :=
      Subgroup.pow_mem _ hcC _
    have h1 : (c : Y) ^ 2 ^ m = 1 := by
      rw [hpow] at hC' ⊢
      exact hZ k' hk' fun k'' hk'' => (Subgroup.mem_centralizer_iff.mp hC' k'' hk'').symm
    exact ⟨m, Subtype.ext (by simpa using h1)⟩

theorem exists_std_equiv [Finite Y] (hn : 1 ≤ n) {K T : Subgroup Y}
    (hTK : IsSylowTwoOf (T ⊓ K) K) (e₀ : ↥K ≃* SpecialLinearGroup (Fin n) (ZMod 2)) :
    ∃ e : ↥K ≃* SpecialLinearGroup (Fin n) (ZMod 2),
      ((T ⊓ K).subgroupOf K).map e.toMonoidHom = unitriangular n (ZMod 2) := by
  have hU₀ : IsSylowTwoOf (unitriangular n (ZMod 2)) ⊤ :=
    CFSG.Quasithin.SzN2.isSylowTwoOf_unitriangular hn
  have hU₁ : IsSylowTwoOf (((T ⊓ K).subgroupOf K).map e₀.toMonoidHom) ⊤ :=
    CFSG.Quasithin.isSylowTwoOf_top_map_of_surjective
      (CFSG.Quasithin.isSylowTwoOf_top_subgroupOf hTK) e₀.toMonoidHom e₀.surjective
  obtain ⟨g, -, hg⟩ := CFSG.Quasithin.B6.isSylowTwoOf_exists_conj hU₀ hU₁
  refine ⟨e₀.trans (MulAut.conj g⁻¹), ?_⟩
  have h1 : ((T ⊓ K).subgroupOf K).map (e₀.trans (MulAut.conj g⁻¹)).toMonoidHom =
      (((T ⊓ K).subgroupOf K).map e₀.toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [Subgroup.map_map]
    rfl
  rw [h1, hg]
  have h2 := CFSG.Quasithin.B6.conjSub_mul g⁻¹ g (unitriangular n (ZMod 2))
  rw [inv_mul_cancel, CFSG.Quasithin.B6.conjSub_one] at h2
  exact h2.symm

@[expose] def conjOn (K : Subgroup Y) {t : Y} (ht : t ∈ Subgroup.normalizer (K : Set Y)) :
    MulAut ↥K where
  toFun k := ⟨t * k * t⁻¹, (Subgroup.mem_normalizer_iff.mp ht k).mp k.2⟩
  invFun k := ⟨t⁻¹ * k * t, by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ht) k).mp k.2
    simpa using this⟩
  left_inv k := Subtype.ext (by dsimp; group)
  right_inv k := Subtype.ext (by dsimp; group)
  map_mul' a b := Subtype.ext (by dsimp; group)

theorem conjOn_coe (K : Subgroup Y) {t : Y} (ht : t ∈ Subgroup.normalizer (K : Set Y))
    (k : ↥K) : ((conjOn K ht k : ↥K) : Y) = t * k * t⁻¹ := rfl

@[expose] def alphaOf {K : Subgroup Y} (e : ↥K ≃* SpecialLinearGroup (Fin n) (ZMod 2)) {t : Y}
    (ht : t ∈ Subgroup.normalizer (K : Set Y)) : MulAut (SpecialLinearGroup (Fin n) (ZMod 2)) :=
  MulAut.congr e (conjOn K ht)

theorem alphaOf_apply {K : Subgroup Y} (e : ↥K ≃* SpecialLinearGroup (Fin n) (ZMod 2)) {t : Y}
    (ht : t ∈ Subgroup.normalizer (K : Set Y)) (k : ↥K) :
    alphaOf e ht (e k) = e (conjOn K ht k) := by
  rw [alphaOf, MulAut.congr_apply]
  simp

theorem map_alphaOf [Finite Y] {K A : Subgroup Y} (e : ↥K ≃* SpecialLinearGroup (Fin n) (ZMod 2))
    {t : Y} (ht : t ∈ Subgroup.normalizer (K : Set Y))
    (htA : t ∈ Subgroup.normalizer (A : Set Y)) :
    ((A.subgroupOf K).map e.toMonoidHom).map (alphaOf e ht).toMonoidHom =
      (A.subgroupOf K).map e.toMonoidHom := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨conjOn K ht a, ?_, (alphaOf_apply e ht a).symm⟩
    have ha' : (a : Y) ∈ A := Subgroup.mem_subgroupOf.mp ha
    show conjOn K ht a ∈ A.subgroupOf K
    rw [Subgroup.mem_subgroupOf, conjOn_coe]
    exact (Subgroup.mem_normalizer_iff.mp htA a).mp ha'
  · rw [Subgroup.card_map_of_injective (f := (alphaOf e ht).toMonoidHom) (alphaOf e ht).injective]

theorem alphaOf_ne_conj {H K : Subgroup Y} (e : ↥K ≃* SpecialLinearGroup (Fin n) (ZMod 2))
    {t : Y} (ht : t ∈ Subgroup.normalizer (K : Set Y)) (hKH : K ≤ H) (htH : t ∈ H)
    (htK : t ∉ K) (hC : H ⊓ Subgroup.centralizer (K : Set Y) = ⊥)
    (s : SpecialLinearGroup (Fin n) (ZMod 2)) : alphaOf e ht ≠ MulAut.conj s := by
  intro h
  set k : ↥K := e.symm s with hkdef
  have hks : e k = s := e.apply_symm_apply s
  have key : ∀ y : ↥K, t * (y : Y) * t⁻¹ = (k : Y) * y * (k : Y)⁻¹ := by
    intro y
    have h1 := congrArg (fun φ : MulAut (SpecialLinearGroup (Fin n) (ZMod 2)) => φ (e y)) h
    simp only [alphaOf_apply, MulAut.conj_apply] at h1
    rw [← hks, ← map_mul, ← map_inv, ← map_mul] at h1
    have h2 := congrArg Subtype.val (e.injective h1)
    simpa [conjOn_coe] using h2
  have hc : (k : Y)⁻¹ * t ∈ H ⊓ Subgroup.centralizer (K : Set Y) := by
    refine ⟨H.mul_mem (H.inv_mem (hKH k.2)) htH, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have h1 := key ⟨y, hy⟩
    calc y * ((k : Y)⁻¹ * t) = (k : Y)⁻¹ * ((k : Y) * y * (k : Y)⁻¹) * t := by group
      _ = (k : Y)⁻¹ * (t * y * t⁻¹) * t := by rw [h1]
      _ = (k : Y)⁻¹ * t * y := by group
  rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hc
  exact htK (hc ▸ k.2)

theorem revCuts_eq_of_conj [Finite Y] (hn : 3 ≤ n) {H K T B : Subgroup Y}
    (e : ↥K ≃* SpecialLinearGroup (Fin n) (ZMod 2)) (hKH : K ≤ H)
    (hKn : H ≤ Subgroup.normalizer (K : Set Y)) (hC : H ⊓ Subgroup.centralizer (K : Set Y) = ⊥)
    (hTH : T ≤ H) (he : ((T ⊓ K).subgroupOf K).map e.toMonoidHom = unitriangular n (ZMod 2))
    {t : Y} (htT : t ∈ T) (htK : t ∉ K) (htB : t ∈ Subgroup.normalizer (B : Set Y))
    {C : Set ℕ} (hCc : IsCuts n C)
    (hBC : (B.subgroupOf K).map e.toMonoidHom = flagStabilizer n (ZMod 2) C) :
    revCuts n C = C := by
  have ht : t ∈ Subgroup.normalizer (K : Set Y) := hKn (hTH htT)
  have htTK : t ∈ Subgroup.normalizer ((T ⊓ K : Subgroup Y) : Set Y) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer htT, ht⟩
  have hα : (unitriangular n (ZMod 2)).map (alphaOf e ht).toMonoidHom =
      unitriangular n (ZMod 2) := by
    rw [← he]
    exact map_alphaOf e ht htTK
  have hfix : (flagStabilizer n (ZMod 2) C).map (alphaOf e ht).toMonoidHom =
      flagStabilizer n (ZMod 2) C := by
    rw [← hBC]
    exact map_alphaOf e ht htB
  exact revCuts_eq_of_map_eq hn hα (alphaOf_ne_conj e ht hKH (hTH htT) htK hC) hCc hfix

end CFSG.Quasithin.H13.A6.L13825
