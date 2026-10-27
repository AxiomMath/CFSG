module

public import CFSG.Quasithin.H13.A5W1618c

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

local notation "StSL" => Assembly.LowTwoRank.StatedSL

section Frattini

variable {G : Type} [Group G] [Finite G]

theorem exists_normalizer_thompsonJ_gen {Y T W : Subgroup G} {J : Subgroup (MulAut ↥W)}
    (hTY : IsSylowTwoOf T Y) (hYW : Y ≤ Subgroup.normalizer (W : Set G))
    (hJT : autOn (thompsonJ T) W ≤ J)
    (hYJ : autOn Y W ≤ Subgroup.normalizer (J : Set (MulAut ↥W))) {x : MulAut ↥W}
    (hxY : x ∈ autOn Y W)
    (hxN : x ∈ Subgroup.normalizer ((autOn T W ⊓ J : Subgroup (MulAut ↥W)) : Set (MulAut ↥W))) :
    ∃ (y : G) (hy : y ∈ Y), y ∈ Subgroup.normalizer (thompsonJ T : Set G) ∧
      ∃ r ∈ autOn T W ⊓ J, conjAct W ⟨y, hYW hy⟩ = r * x := by
  set Q : Subgroup (MulAut ↥W) := autOn T W ⊓ J with hQ
  let pre : Subgroup (MulAut ↥W) → Subgroup G := fun Q' =>
    ((Q'.comap (conjAct W)).map (Subgroup.normalizer (W : Set G)).subtype) ⊓ Y
  have mem_pre : ∀ {Q' : Subgroup (MulAut ↥W)} {g : G},
      g ∈ pre Q' ↔ ∃ hg : g ∈ Y, conjAct W ⟨g, hYW hg⟩ ∈ Q' := by
    intro Q' g
    constructor
    · rintro ⟨⟨⟨y, hyN⟩, hy, rfl⟩, hg⟩
      exact ⟨hg, hy⟩
    · rintro ⟨hg, hq⟩
      exact ⟨⟨⟨g, hYW hg⟩, hq, rfl⟩, hg⟩
  set Yp := pre (Subgroup.normalizer (Q : Set (MulAut ↥W))) with hYp
  set X := pre Q with hX
  have hXY : X ≤ Yp := fun g hg => by
    obtain ⟨hg, hq⟩ := mem_pre.1 hg
    exact mem_pre.2 ⟨hg, Subgroup.le_normalizer hq⟩
  have hYX : Yp ≤ Subgroup.normalizer (X : Set G) := by
    have key : ∀ k ∈ Yp, ∀ g ∈ X, k * g * k⁻¹ ∈ X := by
      intro k hk g hg
      obtain ⟨hkY, hkq⟩ := mem_pre.1 hk
      obtain ⟨hgY, hgq⟩ := mem_pre.1 hg
      have hm : k * g * k⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem hkY hgY) (Y.inv_mem hkY)
      refine mem_pre.2 ⟨hm, ?_⟩
      rw [show (⟨k * g * k⁻¹, hYW hm⟩ : ↥(Subgroup.normalizer (W : Set G))) =
        ⟨k, hYW hkY⟩ * ⟨g, hYW hgY⟩ * (⟨k, hYW hkY⟩)⁻¹ from rfl, map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hkq _).mp hgq
    intro y hy
    refine B6.mem_normalizer_of_forall_mem (key y hy) fun g hg => ?_
    have := key y⁻¹ (Yp.inv_mem hy) g hg
    rwa [inv_inv] at this
  have hTYp : T ≤ Yp := by
    intro t ht
    have htY := hTY.1 ht
    refine mem_pre.2 ⟨htY, ?_⟩
    have hts : conjAct W ⟨t, hYW htY⟩ ∈ autOn T W :=
      Setup.mem_autOn_iff.2 ⟨⟨t, hYW htY⟩, ht, rfl⟩
    have htsY : conjAct W ⟨t, hYW htY⟩ ∈ autOn Y W :=
      Setup.mem_autOn_iff.2 ⟨⟨t, hYW htY⟩, htY, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro q
    rw [hQ, Subgroup.mem_inf, Subgroup.mem_inf,
      (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hts) q),
      (Subgroup.mem_normalizer_iff.mp (hYJ htsY) q)]
  have hTYp' : IsSylowTwoOf T Yp := B6.isSylowTwoOf_mono hTY hTYp inf_le_right
  have hJX : thompsonJ T ≤ X := by
    intro j hj
    have hjT : j ∈ T := B6.thompsonJ_le T hj
    have hjY := hTY.1 hjT
    refine mem_pre.2 ⟨hjY, ?_, ?_⟩
    · exact Setup.mem_autOn_iff.2 ⟨⟨j, hYW hjY⟩, hjT, rfl⟩
    · exact hJT (Setup.mem_autOn_iff.2 ⟨⟨j, hYW hjY⟩, hj, rfl⟩)
  have hTX : IsSylowTwoOf (T ⊓ X) X := B6.isSylowTwoOf_inf_normal hTYp' hXY hYX
  obtain ⟨⟨g, hgN⟩, hgY, rfl⟩ := Setup.mem_autOn_iff.1 hxY
  have hgYp : g ∈ Yp := mem_pre.2 ⟨hgY, hxN⟩
  obtain ⟨n, hnX, k, ⟨hkYp, hkN⟩, hgnk⟩ := exists_mul_normalizer_of_sylow hXY hYX hTX hgYp
  have hJ : thompsonJ (T ⊓ X) = thompsonJ T :=
    B6.thompsonJ_eq_of_le (le_inf (B6.thompsonJ_le T) hJX) inf_le_left
  have hkJ : k ∈ Subgroup.normalizer (thompsonJ T : Set G) := by
    rw [← hJ]
    exact normalizer_le_normalizer_thompsonJ _ hkN
  obtain ⟨hkY, -⟩ := mem_pre.1 hkYp
  obtain ⟨hnY, hnq⟩ := mem_pre.1 hnX
  refine ⟨k, hkY, hkJ, (conjAct W ⟨n, hYW hnY⟩)⁻¹, Q.inv_mem hnq, ?_⟩
  have e : (⟨k, hYW hkY⟩ : ↥(Subgroup.normalizer (W : Set G))) =
      (⟨n, hYW hnY⟩)⁻¹ * ⟨g, hgN⟩ := Subtype.ext (by
    show k = n⁻¹ * g
    rw [hgnk, inv_mul_cancel_left])
  rw [e, map_mul, map_inv]

end Frattini

section Powers

variable {Γ : Type*} [Group Γ]

theorem mul_pow_mul_inv_mem {Q : Subgroup Γ} {r x : Γ} (hr : r ∈ Q)
    (hx : x ∈ Subgroup.normalizer (Q : Set Γ)) (k : ℕ) : (r * x) ^ k * (x ^ k)⁻¹ ∈ Q := by
  induction k with
  | zero => simp [Q.one_mem]
  | succ k ih =>
    have hxk : x ^ k ∈ Subgroup.normalizer (Q : Set Γ) := Subgroup.pow_mem _ hx k
    have h1 : x ^ k * r * (x ^ k)⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hxk r).mp hr
    have e : (r * x) ^ (k + 1) * (x ^ (k + 1))⁻¹ =
        ((r * x) ^ k * (x ^ k)⁻¹) * (x ^ k * r * (x ^ k)⁻¹) := by
      rw [pow_succ, pow_succ]
      group
    rw [e]
    exact Q.mul_mem ih h1

theorem fix_pow_of_fix {V : Type*} [Group V] {Q : Subgroup (MulAut V)} {r x : MulAut V}
    (hr : r ∈ Q) (hx : x ∈ Subgroup.normalizer (Q : Set (MulAut V))) {u : V}
    (hQ : ∀ q ∈ Q, q u = u) {k : ℕ} (hk : ((r * x) ^ k) u = u) : (x ^ k) u = u := by
  have h1 := mul_pow_mul_inv_mem hr hx k
  have e : x ^ k = ((r * x) ^ k * (x ^ k)⁻¹)⁻¹ * (r * x) ^ k := by group
  rw [e, MulAut.mul_apply, hk, hQ _ (Q.inv_mem h1)]

end Powers

section Borel

variable {K : Type} [Field K] [CharP K 2]
variable {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)} {W C : Subgroup V}
  {π : ↥(StSL 2 K) →* ↥H}

theorem fix_of_fix_conj_borel (hπ : (FFModel.nat (StSL 2 K)).RealizesVia H W C π)
    (hC : ∀ g ∈ H, ∀ c ∈ C, g c = c) (hHp : ⁅H, H⁆ = H) {z : V}
    (hzW : ∀ g ∈ H, g z * z⁻¹ ∈ W) (s : Matrix.SpecialLinearGroup (Fin 2) K)
    (hU : ∀ x : K, ((π (slOf (s * unip x * s⁻¹)) : ↥H) : MulAut V) z = z) {μ : Kˣ}
    (hμ : (μ : K) ≠ 1) (hT : ((π (slOf (s * tor μ * s⁻¹)) : ↥H) : MulAut V) z = z) :
    ∀ g ∈ H, g z = z := by
  set p := ((π (slOf s⁻¹) : ↥H) : MulAut V) with hp
  have hpH : p ∈ H := (π (slOf s⁻¹)).2
  have hconj : ∀ t : Matrix.SpecialLinearGroup (Fin 2) K,
      ((π (slOf (s * t * s⁻¹)) : ↥H) : MulAut V) z = z →
        ((π (slOf t) : ↥H) : MulAut V) (p z) = p z := by
    intro t ht
    have e : slOf t * slOf s⁻¹ = slOf s⁻¹ * slOf (s * t * s⁻¹) := by
      rw [← map_mul, ← map_mul]
      congr 1
      group
    have e2 : ((π (slOf t * slOf s⁻¹) : ↥H) : MulAut V) z =
        ((π (slOf s⁻¹ * slOf (s * t * s⁻¹)) : ↥H) : MulAut V) z := by rw [e]
    rw [map_mul π, map_mul π, Subgroup.coe_mul, Subgroup.coe_mul, MulAut.mul_apply,
      MulAut.mul_apply] at e2
    rw [hp, e2, ht]
  have hzW' : ∀ g ∈ H, g (p z) * (p z)⁻¹ ∈ W := by
    intro g hg
    have e : g (p z) * (p z)⁻¹ = ((g * p) z * z⁻¹) * (p z * z⁻¹)⁻¹ := by
      rw [MulAut.mul_apply]
      group
    rw [e]
    exact W.mul_mem (hzW _ (H.mul_mem hg hpH)) (W.inv_mem (hzW _ hpH))
  have h1 := fix_of_fix_borel hπ hC hHp hzW' (fun x => hconj _ (hU x)) hμ (hconj _ hT)
  have hz : p z = z := by
    have := h1 _ (H.inv_mem hpH)
    rw [MulAut.inv_apply_self] at this
    exact this.symm
  intro g hg
  rw [← hz]
  exact h1 g hg

end Borel

section Sylow

theorem exists_conj_unitriangular {Γ : Type} [Group Γ] [Finite Γ] {N Q₁ : Subgroup Γ}
    {K : Type} [Field K] [Finite K] [CharP K 2] {π : ↥(StSL 2 K) →* ↥N}
    (hinj : Function.Injective π) (hsurj : Function.Surjective π) (hQ : IsSylowTwoOf Q₁ N) :
    ∃ s : Matrix.SpecialLinearGroup (Fin 2) K,
      (∀ x : K, ((π (slOf (s * unip x * s⁻¹)) : ↥N) : Γ) ∈ Q₁) ∧
      ∀ μ : Kˣ, ((π (slOf (s * tor μ * s⁻¹)) : ↥N) : Γ) ∈ Subgroup.normalizer (Q₁ : Set Γ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ψ : Matrix.SpecialLinearGroup (Fin 2) K →* ↥N := π.comp slOf with hψ
  have hψi : Function.Injective ψ := hinj.comp fun a b h =>
    Matrix.SpecialLinearGroup.toGL_injective (congrArg Subtype.val h)
  have hψs : Function.Surjective ψ := hsurj.comp slOf_surjective
  set P := (Q₁.subgroupOf N).comap ψ with hP
  have hPsyl : IsSylowTwoOf P ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact (hQ.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hQ.1).symm).comap_of_injective ψ hψi
    · show ¬ 2 ∣ P.relIndex ⊤
      rw [Subgroup.relIndex_top_right, hP, Subgroup.index_comap_of_surjective _ hψs]
      exact hQ.2.2
  have hU₀ : IsSylowTwoOf (unitriangular 2 K) ⊤ := SzN2.isSylowTwoOf_unitriangular (by norm_num)
  obtain ⟨s, -, hs⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj
    (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.1 hU₀)
    (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.1 hPsyl)
  have hmemP : ∀ y, y ∈ P → ((ψ y : ↥N) : Γ) ∈ Q₁ := fun y hy =>
    Subgroup.mem_subgroupOf.mp (Subgroup.mem_comap.mp hy)
  have hunip : ∀ x : K, unip x ∈ unitriangular 2 K := by
    intro x
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp_all [unip]
    · fin_cases i <;> simp [unip]
  have htor : ∀ μ : Kˣ, tor μ ∈ Subgroup.normalizer (unitriangular 2 K : Set _) := by
    intro μ
    rw [normalizer_unitriangular]
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [tor]
  refine ⟨s, fun x => ?_, fun μ => ?_⟩
  · apply hmemP
    rw [hs]
    have e : s⁻¹ * (s * unip x * s⁻¹) * s = unip x := by group
    rw [e]
    exact hunip x
  ·
    set t := s * tor μ * s⁻¹ with ht
    have htP : ∀ y, y ∈ P ↔ t * y * t⁻¹ ∈ P := by
      intro y
      rw [hs, hs]
      have e : s⁻¹ * (t * y * t⁻¹) * s = tor μ * (s⁻¹ * y * s) * (tor μ)⁻¹ := by
        rw [ht]
        group
      rw [e]
      exact Subgroup.mem_normalizer_iff.mp (htor μ) _
    have hQψ : ∀ q ∈ Q₁, ∃ y ∈ P, ((ψ y : ↥N) : Γ) = q := by
      intro q hq
      obtain ⟨y, hy⟩ := hψs ⟨q, hQ.1 hq⟩
      refine ⟨y, Subgroup.mem_comap.mpr (Subgroup.mem_subgroupOf.mpr ?_), ?_⟩
      · rw [hy]
        exact hq
      · rw [hy]
    have hψt : ((π (slOf t) : ↥N) : Γ) = ((ψ t : ↥N) : Γ) := rfl
    rw [hψt]
    refine B6.mem_normalizer_of_forall_mem (fun q hq => ?_) fun q hq => ?_
    · obtain ⟨y, hyP, rfl⟩ := hQψ q hq
      have h1 := hmemP _ ((htP y).mp hyP)
      simpa [map_mul, map_inv] using h1
    · obtain ⟨y, hyP, rfl⟩ := hQψ q hq
      have h2 : t⁻¹ * y * t⁻¹⁻¹ ∈ P := by
        rw [htP, show t * (t⁻¹ * y * t⁻¹⁻¹) * t⁻¹ = y by group]
        exact hyP
      have h1 := hmemP _ h2
      simpa [map_mul, map_inv] using h1

end Sylow

end CFSG.Quasithin.H13.A5
