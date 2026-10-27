module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitSpDim
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitSUMove

public section

namespace CFSG.StandardType

namespace OrdPNsGen

open Matrix Module SUTB NoOffOm CFSG.RankThree.PartOne.OddIso

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
  {B : (Fin d → K) →ₗ[K] (Fin d → K) →ₗ[K] K} {Γ : Subgroup (GL (Fin d) K)} {p : ℕ}
  {A : Subgroup (GL (Fin d) K)}

omit [Finite K] [CharP K 2] in
theorem nondegOn_orth' (hB : B.IsSymm) (hBsep : ∀ v, (∀ w, B v w = 0) → v = 0)
    {X : Submodule K (Fin d → K)} (hX : NondegOn B X) : NondegOn B (X.orthogonalBilin B) := by
  intro w hw hW
  have hall : ∀ v, B v w = 0 := by
    intro v
    obtain ⟨m, hm, t, ht, rfl⟩ := exists_add_orth hX v
    rw [map_add, LinearMap.add_apply, (Submodule.mem_orthogonalBilin.mp hw) m hm, hW t ht,
      add_zero]
  refine hBsep w fun v => ?_
  rw [← hB.eq v w, hall v, map_zero]

omit [Finite K] [CharP K 2] in
theorem restrictElt_isometry_of_on' (hB : B.IsSymm) {W : Submodule K (Fin d → K)}
    (hW : NondegOn B W) {c : Module.End K (Fin d → K)} (hc : ∀ w ∈ W, c w ∈ W)
    (hcB : ∀ v ∈ W, ∀ w ∈ W, B (c v) (c w) = B v w) (v w : Fin d → K) :
    B (restrictElt hW c hc v) (restrictElt hW c hc w) = B v w := by
  obtain ⟨m, hm, z, hz, rfl⟩ := exists_add_orth hW v
  obtain ⟨m', hm', z', hz', rfl⟩ := exists_add_orth hW w
  have hWo : ∀ a ∈ W, ∀ b ∈ W.orthogonalBilin B, B a b = 0 := fun a ha b hb =>
    (Submodule.mem_orthogonalBilin.mp hb) a ha
  have hoW : ∀ a ∈ W, ∀ b ∈ W.orthogonalBilin B, B b a = 0 := fun a ha b hb => by
    rw [← hB.eq a b, hWo a ha b hb, map_zero]
  simp only [map_add, LinearMap.add_apply, restrictElt_apply_of_mem hW hc hm,
    restrictElt_apply_of_mem hW hc hm', restrictElt_apply_of_mem_orth hW hc hz,
    restrictElt_apply_of_mem_orth hW hc hz']
  rw [hWo _ (hc m hm) z' hz', hoW _ (hc m' hm') z hz, hWo m hm z' hz', hoW m' hm' z hz,
    hcB m hm m' hm']

@[expose] def IsSympFamily (B : (Fin d → K) →ₗ[K] (Fin d → K) →ₗ[K] K) {k : ℕ}
    (F : Fin k ⊕ Fin k → Fin d → K) : Prop :=
  ∀ i j : Fin k, B (F (.inl i)) (F (.inl j)) = 0 ∧ B (F (.inr i)) (F (.inr j)) = 0 ∧
    B (F (.inl i)) (F (.inr j)) = (if i = j then 1 else 0) ∧
    B (F (.inr i)) (F (.inl j)) = (if i = j then 1 else 0)

omit [Finite K] [CharP K 2] in
theorem IsSympFamily.gram_eq {k : ℕ} {F F' : Fin k ⊕ Fin k → Fin d → K} (hF : IsSympFamily B F)
    (hF' : IsSympFamily B F') : ∀ x y, B (F x) (F y) = B (F' x) (F' y) := by
  rintro (i | i) (j | j)
  · rw [(hF i j).1, (hF' i j).1]
  · rw [(hF i j).2.2.1, (hF' i j).2.2.1]
  · rw [(hF i j).2.2.2, (hF' i j).2.2.2]
  · rw [(hF i j).2.1, (hF' i j).2.1]

omit [Finite K] [CharP K 2] in
theorem nondegOn_span_of_sympFamily {k : ℕ} {F : Fin k ⊕ Fin k → Fin d → K}
    (hF : IsSympFamily B F) : NondegOn B (Submodule.span K (Set.range F)) := by
  classical
  intro v hv hB0
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hv
  have hval : ∀ y, B (F y) (∑ x, c x • F x) = ∑ x, c x * B (F y) (F x) := by
    intro y
    rw [map_sum]
    simp [map_smul]
  have hc : ∀ x, c x = 0 := by
    rintro (i | i)
    · have h1 := hB0 (F (.inr i)) (Submodule.subset_span ⟨_, rfl⟩)
      rw [hval, Fintype.sum_sum_type] at h1
      simpa [(hF i _).2.1, (hF i _).2.2.2] using h1
    · have h1 := hB0 (F (.inl i)) (Submodule.subset_span ⟨_, rfl⟩)
      rw [hval, Fintype.sum_sum_type] at h1
      simpa [(hF i _).1, (hF i _).2.2.1] using h1
  simp [hc]

omit [Finite K] [CharP K 2] in
theorem exists_gl_of_pow (hp : 1 ≤ p) {z : Module.End K (Fin d → K)} (hzp : z ^ p = 1) :
    ∃ g : GL (Fin d) K, glin g = z := by
  set M := LinearMap.toMatrixAlgEquiv' z with hM
  have hMp : M ^ p = 1 := by rw [hM, ← map_pow, hzp, map_one]
  have hMM : M * M ^ (p - 1) = 1 := by rw [← pow_succ', Nat.sub_add_cancel hp, hMp]
  have hMM' : M ^ (p - 1) * M = 1 := by rw [← pow_succ, Nat.sub_add_cancel hp, hMp]
  refine ⟨⟨M, M ^ (p - 1), hMM, hMM'⟩, ?_⟩
  change Matrix.toLinAlgEquiv' M = z
  rw [hM, Matrix.toLinAlgEquiv'_toMatrixAlgEquiv']

theorem triv_orth_genPieceSpan (hA : GenMax B Γ p A) {S : Finset (GL (Fin d) K)}
    (hS : GenPieceSet B A S) (hterm : ∀ c ∈ A, (∀ v ∈ genPieceSpan S, glin c v = v) → c = 1)
    {a : GL (Fin d) K} (ha : a ∈ A) :
    ∀ w ∈ (genPieceSpan S).orthogonalBilin B, glin a w = w := by
  have hp1 : 1 ≤ p := hA.prime.one_lt.le
  have hX : NondegOn B (genPieceSpan S) := (hS.nondegOn_card hA).1
  have hW := nondegOn_orth' hA.symm hA.sep hX
  have hXA : ∀ b ∈ A, ∀ v ∈ genPieceSpan S, glin b v ∈ genPieceSpan S := by
    intro b hb v hv
    have hle : genPieceSpan S ≤ (genPieceSpan S).comap (glin b) := by
      refine iSup₂_le fun y hy u hu => ?_
      exact (le_iSup₂ (f := fun y (_ : y ∈ S) => grng y) y hy) (grng_inv hA (hS.mem y hy) hb u hu)
    exact hle hv
  have hWA : ∀ b ∈ A, ∀ w ∈ (genPieceSpan S).orthogonalBilin B, glin b w ∈
      (genPieceSpan S).orthogonalBilin B := fun b hb w hw =>
    orth_invariantH (hA.iso b hb) (hA.lin_pow hb) hp1 (hXA b hb) hw
  obtain ⟨g, hgA, hgW, hgW'⟩ := hA.exists_mem_restrict hW hWA ha
  have hg1 : g = 1 := by
    refine hterm g hgA fun v hv => hgW' v ?_
    refine Submodule.mem_orthogonalBilin.mpr fun w hw => ?_
    rw [← hA.symm.eq v w, (Submodule.mem_orthogonalBilin.mp hw) v hv, map_zero]
  intro w hw
  rw [← hgW w hw, hg1, glin_one]
  rfl

omit [Finite K] [CharP K 2] in
theorem isSympFamily_of_basis [CharP K 2] (hBalt : ∀ v, B v v = 0)
    {U : Submodule K (Fin d → K)} {m k : ℕ} {b : Basis (Fin m ⊕ Fin m) K U}
    (hb : CFSG.RankThree.PartOne.KCAlternating.IsSymplecticBasis (B.domRestrict₁₂ U U) b)
    {τ : Fin k → Fin m} (hτ : Function.Injective τ) :
    IsSympFamily B (fun x => (b (Sum.map τ τ x) : Fin d → K)) := by
  have halt : (B.domRestrict₁₂ U U).IsAlt := fun x => hBalt x
  intro i j
  have h1 := hb.1 (τ i) (τ j)
  have h2 := hb.2.1 (τ i) (τ j)
  have h3 := hb.2.2 (τ i) (τ j)
  have h4 := CFSG.RankThree.PartOne.KCAlternating.IsSymplecticBasis.apply_inr_inl halt hb (τ i) (τ j)
  simp only [LinearMap.domRestrict₁₂_apply, hτ.eq_iff, CharTwo.neg_eq] at h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

theorem finrank_orth_genPieceSpan_lt (hBalt : ∀ v, B v v = 0) (hA : GenMax B Γ p A)
    (hΓ : ∀ g : GL (Fin d) K, (∀ v w, B (glin g v) (glin g w) = B v w) → g ∈ Γ)
    {S : Finset (GL (Fin d) K)} (hS : GenPieceSet B A S)
    (hterm : ∀ c ∈ A, (∀ v ∈ genPieceSpan S, glin c v = v) → c = 1) {y₀ : GL (Fin d) K}
    (hy₀ : y₀ ∈ S) :
    finrank K ((genPieceSpan S).orthogonalBilin B) < finrank K (grng y₀) := by
  classical
  have hBs : B.IsSymm := hA.symm
  have hp := hA.prime
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hy₀A : y₀ ∈ A := hS.mem y₀ hy₀
  set X := genPieceSpan S with hXdef
  set W := X.orthogonalBilin B with hWdef
  set U₀ := grng y₀ with hU₀
  have hX : NondegOn B X := (hS.nondegOn_card hA).1
  have hW : NondegOn B W := nondegOn_orth' hBs hA.sep hX
  have hU₀nd : NondegOn B U₀ := nondegOn_grng hA hy₀A
  have hmpos : 0 < finrank K U₀ := by
    rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact grng_ne_bot (hS.ne_one y₀ hy₀)
  by_contra hlt
  push Not at hlt
  have hnd : ∀ {U : Submodule K (Fin d → K)}, NondegOn B U → (B.domRestrict₁₂ U U).Nondegenerate := by
    intro U hU
    refine ⟨fun x hx => Subtype.ext (hU x x.2 fun w hw => ?_), fun x hx =>
      Subtype.ext (hU x x.2 fun w hw => hx ⟨w, hw⟩)⟩
    have h1 := hx ⟨w, hw⟩
    rw [LinearMap.domRestrict₁₂_apply] at h1
    rw [← hBs.eq (x : Fin d → K) w, h1]
    rfl
  have halt : ∀ {U : Submodule K (Fin d → K)}, (B.domRestrict₁₂ U U).IsAlt := fun x => hBalt x
  obtain ⟨k, b₀, hk, hb₀⟩ :=
    CFSG.RankThree.PartOne.KCAlternating.exists_isSymplecticBasis (halt (U := U₀)) (hnd hU₀nd)
  obtain ⟨m, b₁, hm, hb₁⟩ :=
    CFSG.RankThree.PartOne.KCAlternating.exists_isSymplecticBasis (halt (U := W)) (hnd hW)
  have hkm : k ≤ m := by omega
  set F : Fin k ⊕ Fin k → Fin d → K := fun x => (b₀ (Sum.map id id x) : Fin d → K) with hF
  set F' : Fin k ⊕ Fin k → Fin d → K :=
    fun x => (b₁ (Sum.map (Fin.castLE hkm) (Fin.castLE hkm) x) : Fin d → K) with hF'
  have hFs : IsSympFamily B F := isSympFamily_of_basis hBalt hb₀ Function.injective_id
  have hF's : IsSympFamily B F' := isSympFamily_of_basis hBalt hb₁ (Fin.castLE_injective hkm)
  have hFx : ∀ x, F x = (b₀ x : Fin d → K) := fun x => by simp [hF, Sum.map_id_id]
  have hspanF : Submodule.span K (Set.range F) = U₀ := by
    have h1 : Set.range F = U₀.subtype '' Set.range b₀ := by
      ext v
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨b₀ x, ⟨x, rfl⟩, (hFx x).symm⟩
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, hFx x⟩
    rw [h1, ← Submodule.map_span, b₀.span_eq, Submodule.map_top, Submodule.range_subtype]
  set W' := Submodule.span K (Set.range F') with hW'
  have hW'W : W' ≤ W := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact (b₁ _).2)
  have hW'nd : NondegOn B W' := nondegOn_span_of_sympFamily hF's
  have hFnd : NondegOn B (Submodule.span K (Set.range F)) := by rw [hspanF]; exact hU₀nd
  have hG : ∀ i j, B (F i) (F j) = B (F' i) (F' j) := hFs.gram_eq hF's
  have hG' : ∀ i j, B (F' i) (F' j) = B (F i) (F j) := fun i j => (hG i j).symm
  obtain ⟨θ, hθ⟩ := exists_linearMap_of_gram hG hW'nd
  obtain ⟨θ', hθ'⟩ := exists_linearMap_of_gram hG' hFnd
  have hθθ' : ∀ v ∈ U₀, θ' (θ v) = v := by
    intro v hv
    rw [← hspanF] at hv
    have h1 : Set.EqOn (θ' ∘ₗ θ) (LinearMap.id : Module.End K (Fin d → K)) (Set.range F) := by
      rintro _ ⟨i, rfl⟩
      simp [hθ, hθ']
    exact LinearMap.eqOn_span' h1 hv
  have hθ'θ : ∀ v ∈ W', θ (θ' v) = v := by
    intro v hv
    have h1 : Set.EqOn (θ ∘ₗ θ') (LinearMap.id : Module.End K (Fin d → K)) (Set.range F') := by
      rintro _ ⟨i, rfl⟩
      simp [hθ, hθ']
    exact LinearMap.eqOn_span' h1 hv
  have hθ'mem : ∀ v ∈ W', θ' v ∈ U₀ := fun v hv => by
    rw [← hspanF]
    exact gram_map_mem hθ' hv
  have hθmem : ∀ v ∈ U₀, θ v ∈ W' := fun v hv => gram_map_mem hθ (by rw [hspanF]; exact hv)
  set c : Module.End K (Fin d → K) := θ ∘ₗ glin y₀ ∘ₗ θ' with hc
  have hcW' : ∀ w ∈ W', c w ∈ W' := fun w hw =>
    hθmem _ (grng_inv hA hy₀A hy₀A _ (hθ'mem w hw))
  have hcB : ∀ v ∈ W', ∀ w ∈ W', B (c v) (c w) = B v w := by
    intro v hv w hw
    simp only [hc, LinearMap.comp_apply]
    have hv' : glin y₀ (θ' v) ∈ Submodule.span K (Set.range F) := by
      rw [hspanF]; exact grng_inv hA hy₀A hy₀A _ (hθ'mem v hv)
    have hw' : glin y₀ (θ' w) ∈ Submodule.span K (Set.range F) := by
      rw [hspanF]; exact grng_inv hA hy₀A hy₀A _ (hθ'mem w hw)
    rw [gram_map_eq hG hθ hv' hw', hA.iso y₀ hy₀A, gram_map_eq hG' hθ' hv hw]
  have hcpow : ∀ k : ℕ, ∀ w ∈ W', (c ^ k) w = θ (glin (y₀ ^ k) (θ' w)) := by
    intro k
    induction k with
    | zero =>
      intro w hw
      rw [pow_zero, pow_zero, glin_one, Module.End.one_apply, Module.End.one_apply, hθ'θ w hw]
    | succ k ih =>
      intro w hw
      have hk : glin (y₀ ^ k) (θ' w) ∈ U₀ :=
        pow_mem_of_inv (grng_inv hA hy₀A hy₀A) k _ (hθ'mem w hw)
      rw [pow_succ', Module.End.mul_apply, ih w hw, hc, LinearMap.comp_apply, LinearMap.comp_apply,
        hθθ' _ hk, pow_succ', glin_mul, Module.End.mul_apply]
  obtain ⟨z, hz⟩ : ∃ z, z = restrictElt hW'nd c hcW' := ⟨_, rfl⟩
  have hzp : z ^ p = 1 := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨m', hm', t, ht, rfl⟩ := exists_add_orth hW'nd v
    rw [hz, restrictElt_pow_apply hW'nd hcW' p hm' ht, hcpow p m' hm', hA.pow y₀ hy₀A, glin_one,
      Module.End.one_apply, hθ'θ m' hm', Module.End.one_apply]
  have hziso : ∀ v w, B (z v) (z w) = B v w := by
    rw [hz]
    exact restrictElt_isometry_of_on' hBs hW'nd hcW' hcB
  obtain ⟨g, hg⟩ := exists_gl_of_pow hp1 hzp
  have hgΓ : g ∈ Γ := hΓ g (by rw [hg]; exact hziso)
  have hgp : g ^ p = 1 := glin_injective (by rw [glin_pow, hg, hzp, glin_one])
  have hcomm : ∀ a ∈ A, g * a = a * g := by
    intro a ha
    have htriv := triv_orth_genPieceSpan hA hS hterm ha
    have haW' : ∀ w ∈ W', glin a w ∈ W' := fun w hw => by rw [htriv w (hW'W hw)]; exact hw
    have haW'' : ∀ t ∈ W'.orthogonalBilin B, glin a t ∈ W'.orthogonalBilin B := fun t ht =>
      orth_invariantH (hA.iso a ha) (hA.lin_pow ha) hp1 haW' ht
    have hac : ∀ w ∈ W', glin a (c w) = c (glin a w) := fun w hw => by
      rw [htriv _ (hW'W (hcW' w hw)), htriv w (hW'W hw)]
    have h1 := restrictElt_comm hW'nd hcW' haW' haW'' hac
    apply glin_injective
    rw [glin_mul, glin_mul, hg, hz]
    exact h1.symm
  have hgA : g ∈ A := hA.max g hgΓ hgp hcomm
  have hg1 : g = 1 := by
    refine hterm g hgA fun v hv => ?_
    have hvo : v ∈ W'.orthogonalBilin B := by
      refine Submodule.mem_orthogonalBilin.mpr fun w hw => ?_
      rw [← hBs.eq v w, (Submodule.mem_orthogonalBilin.mp (hW'W hw)) v hv, map_zero]
    rw [hg, hz]
    exact restrictElt_apply_of_mem_orth hW'nd hcW' hvo
  have hkpos : 0 < k := by omega
  set i₀ : Fin k := ⟨0, hkpos⟩ with hi₀
  have hF'W' : F' (.inl i₀) ∈ W' := Submodule.subset_span ⟨_, rfl⟩
  have hz1 : z (F' (.inl i₀)) = F' (.inl i₀) := by rw [← hg, hg1, glin_one]; rfl
  have hz2 : z (F' (.inl i₀)) = θ (glin y₀ (F (.inl i₀))) := by
    rw [hz, restrictElt_apply_of_mem hW'nd hcW' hF'W', hc, LinearMap.comp_apply,
      LinearMap.comp_apply, hθ' (.inl i₀)]
  rw [hz2] at hz1
  have hFU : F (.inl i₀) ∈ U₀ := by rw [hFx]; exact (b₀ _).2
  have hyF : glin y₀ (F (.inl i₀)) = F (.inl i₀) := by
    have h1 := congrArg θ' hz1
    rwa [hθθ' _ (grng_inv hA hy₀A hy₀A _ hFU), hθ' (.inl i₀)] at h1
  have hF0 : F (.inl i₀) = 0 := eq_zero_of_mem_grng hA hy₀A hFU hyF
  have h1 := (hFs i₀ i₀).2.2.1
  rw [hF0, map_zero, LinearMap.zero_apply, ite_eq_left rfl] at h1
  exact zero_ne_one h1

end OrdPNsGen

end CFSG.StandardType
