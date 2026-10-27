module

public import CFSG.LocalAnalysis.StandardType.GGTBWNorm

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

theorem ggHL_descent {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs L : Subgroup G}
    {x : G} (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (hxB : x ∈ Bs)
    (hker : ∀ b : ↥Bs, ggGamma L hBsN b = 1 ↔ b ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs))
    {Λ : Type} {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    (φ : Λ → MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hxker : ∀ i, α i (ι (Additive.ofMul ⟨x, hxB⟩)) = 0)
    (ψ : Λ → MulAut ↥(ggGamma L hBsN).range)
    (hcompat : ∀ i (b : ↥Bs),
      ψ i ((ggGamma L hBsN).rangeRestrict b) = (ggGamma L hBsN).rangeRestrict (φ i b)) :
    ∃ (VA : Type) (_ : AddCommGroup VA) (_ : Module (ZMod p) VA)
      (ιA : Additive ↥(ggGamma L hBsN).range ≃+ VA) (q : V →ₗ[ZMod p] VA)
      (hA : Λ → VA) (αA : Λ → Module.Dual (ZMod p) VA),
      (∀ b : ↥Bs, q (ι (Additive.ofMul b)) =
        ιA (Additive.ofMul ((ggGamma L hBsN).rangeRestrict b))) ∧
      Function.Surjective q ∧
      LinearMap.ker q = Submodule.span (ZMod p) {ι (Additive.ofMul ⟨x, hxB⟩)} ∧
      (∀ i, q (h i) = hA i) ∧ (∀ i v, αA i (q v) = α i v) ∧
      (∀ i w, ggLin (p := p) ιA (ψ i) w = w - αA i w • hA i) := by
  let A : Subgroup (MulAut L) := (ggGamma L hBsN).range
  let γr : ↥Bs →* ↥A := (ggGamma L hBsN).rangeRestrict
  have hsurj : Function.Surjective γr := MonoidHom.rangeRestrict_surjective _
  let spanx : Submodule (ZMod p) V :=
    Submodule.span (ZMod p) {ι (Additive.ofMul (⟨x, hxB⟩ : ↥Bs))}
  let q : V →ₗ[ZMod p] V ⧸ spanx := Submodule.mkQ spanx
  have hwd : ∀ b b' : ↥Bs, γr b = γr b' →
      q (ι (Additive.ofMul b)) = q (ι (Additive.ofMul b')) := by
    intro b b' h
    have hgg : ggGamma L hBsN b = ggGamma L hBsN b' :=
      congrArg Subtype.val h
    have hmem : ggGamma L hBsN (b⁻¹ * b') = 1 := by
      rw [map_mul, map_inv, hgg, inv_mul_cancel]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ((hker (b⁻¹ * b')).mp hmem)
    have hb' : b' = b * (⟨x, hxB⟩ : ↥Bs) ^ k := by rw [hk]; group
    have hz : q (ι (Additive.ofMul ((⟨x, hxB⟩ : ↥Bs) ^ k))) = 0 := by
      have hspan_mem : ι (Additive.ofMul ((⟨x, hxB⟩ : ↥Bs) ^ k)) ∈ spanx := by
        rw [ofMul_zpow, map_zsmul, ← Int.cast_smul_eq_zsmul (ZMod p) k]
        exact Submodule.smul_mem spanx (k : ZMod p) (Submodule.mem_span_singleton_self _)
      have h0 : (Submodule.mkQ spanx) (ι (Additive.ofMul ((⟨x, hxB⟩ : ↥Bs) ^ k))) = 0 := by
        rw [Submodule.mkQ_apply]
        exact (Submodule.Quotient.mk_eq_zero (p := spanx)).mpr hspan_mem
      simpa only [q] using h0
    rw [hb']
    symm
    calc q (ι (Additive.ofMul (b * (⟨x, hxB⟩ : ↥Bs) ^ k)))
        = q (ι (Additive.ofMul b + Additive.ofMul ((⟨x, hxB⟩ : ↥Bs) ^ k))) := by
          rw [ofMul_mul]
      _ = q (ι (Additive.ofMul b) + ι (Additive.ofMul ((⟨x, hxB⟩ : ↥Bs) ^ k))) := by
          rw [map_add]
      _ = q (ι (Additive.ofMul b)) +
            q (ι (Additive.ofMul ((⟨x, hxB⟩ : ↥Bs) ^ k))) := by rw [map_add]
      _ = q (ι (Additive.ofMul b)) + 0 := by rw [hz]
      _ = q (ι (Additive.ofMul b)) := by rw [add_zero]
  have hspan : ∀ b : ↥Bs, q (ι (Additive.ofMul b)) = 0 →
      b ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs) := by
    intro b hb
    have hbspan : ι (Additive.ofMul b) ∈ spanx := by
      have hmem : ι (Additive.ofMul b) ∈ (Submodule.mkQ spanx).ker :=
        LinearMap.mem_ker.mpr (by simpa only [q] using hb)
      rwa [Submodule.ker_mkQ] at hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hbspan
    refine Subgroup.mem_zpowers_iff.mpr ⟨(c.val : ℤ), ?_⟩
    apply Additive.ofMul.injective
    apply ι.injective
    rw [ofMul_zpow, map_zsmul, ← Int.cast_smul_eq_zsmul (ZMod p) (c.val : ℤ), Int.cast_natCast,
      ZMod.natCast_zmod_val]
    exact hc
  let pick : ↥A → ↥Bs := fun a => Classical.choose (hsurj a)
  have hpick : ∀ a, γr (pick a) = a := fun a => Classical.choose_spec (hsurj a)
  let f : Additive ↥A →+ V ⧸ spanx :=
    { toFun := fun a => q (ι (Additive.ofMul (pick (Additive.toMul a))))
      map_zero' := by
        have h1 : γr (pick (Additive.toMul (0 : Additive ↥A))) = γr (1 : ↥Bs) := by
          rw [hpick, map_one]
          exact toMul_zero
        change q (ι (Additive.ofMul (pick (Additive.toMul (0 : Additive ↥A))))) = 0
        rw [hwd _ _ h1, ofMul_one, map_zero, map_zero]
      map_add' := fun a a' => by
        have h1 : γr (pick (Additive.toMul (a + a'))) =
            γr (pick (Additive.toMul a) * pick (Additive.toMul a')) := by
          rw [hpick, map_mul, hpick, hpick, toMul_add]
        change q (ι (Additive.ofMul (pick (Additive.toMul (a + a'))))) =
          q (ι (Additive.ofMul (pick (Additive.toMul a)))) +
            q (ι (Additive.ofMul (pick (Additive.toMul a'))))
        rw [hwd _ _ h1]
        simp only [ofMul_mul, map_add] }
  have hker_f : ∀ a : Additive ↥A, f a = 0 → a = 0 := by
    intro a ha
    have ha' : q (ι (Additive.ofMul (pick (Additive.toMul a)))) = 0 := ha
    have hb : (Submodule.mkQ spanx) (ι (Additive.ofMul (pick (Additive.toMul a)))) = 0 := by
      simpa only [q] using ha'
    have hgg : ggGamma L hBsN (pick (Additive.toMul a)) = 1 :=
      (hker _).mpr (hspan (pick (Additive.toMul a)) hb)
    have hto : Additive.toMul a = 1 := by
      rw [← hpick a]
      exact Subtype.ext hgg
    exact Additive.toMul.injective (by rw [hto]; rfl)
  have hinj : Function.Injective f := by
    intro a a' haa'
    have hzero : f (a - a') = 0 := by rw [map_sub, haa', sub_self]
    have hsub : a - a' = 0 := hker_f (a - a') hzero
    rwa [sub_eq_zero] at hsub
  have hsurj_f : Function.Surjective f := by
    intro w
    obtain ⟨v, hv⟩ := Submodule.mkQ_surjective spanx w
    obtain ⟨b, rfl⟩ := ι.surjective v
    obtain ⟨b0, rfl⟩ := Additive.ofMul.surjective b
    refine ⟨Additive.ofMul (γr b0), ?_⟩
    have h1 : γr (pick (Additive.toMul (Additive.ofMul (γr b0)))) = γr b0 := by
      rw [hpick, toMul_ofMul]
    rw [← hv]
    change q (ι (Additive.ofMul (pick (Additive.toMul (Additive.ofMul (γr b0)))))) =
      q (ι (Additive.ofMul b0))
    rw [hwd _ _ h1]
  let ιA : Additive ↥A ≃+ V ⧸ spanx := AddEquiv.ofBijective f ⟨hinj, hsurj_f⟩
  have hprop1 : ∀ b : ↥Bs, q (ι (Additive.ofMul b)) = ιA (Additive.ofMul (γr b)) := by
    intro b
    have h1 : γr (pick (Additive.toMul (Additive.ofMul (γr b)))) = γr b := by
      rw [hpick, toMul_ofMul]
    have hq : q (ι (Additive.ofMul (pick (Additive.toMul (Additive.ofMul (γr b)))))) =
        q (ι (Additive.ofMul b)) := hwd _ _ h1
    rw [show ιA (Additive.ofMul (γr b)) =
      f (Additive.ofMul (γr b)) from AddEquiv.ofBijective_apply f ⟨hinj, hsurj_f⟩ _]
    change q (ι (Additive.ofMul b)) =
      q (ι (Additive.ofMul (pick (Additive.toMul (Additive.ofMul (γr b))))))
    rw [hq]
  let hA : Λ → V ⧸ spanx := fun i => q (h i)
  have hle : ∀ i, spanx ≤ (α i).ker := by
    intro i
    change Submodule.span (ZMod p) {ι (Additive.ofMul (⟨x, hxB⟩ : ↥Bs))} ≤ (α i).ker
    rw [Submodule.span_le]
    rintro v rfl
    exact LinearMap.mem_ker.mpr (hxker i)
  let αA : Λ → Module.Dual (ZMod p) (V ⧸ spanx) :=
    fun i => Submodule.liftQ spanx (α i) (hle i)
  have hprop5 : ∀ i v, αA i (q v) = α i v := by
    intro i v
    dsimp only [αA]
    rw [Submodule.mkQ_apply, Submodule.liftQ_apply]
  have hcomm : ∀ i v, ggLin (p := p) ιA (ψ i) (q v) =
      q (ggLin (p := p) ι (φ i) v) := by
    intro i v
    obtain ⟨b, rfl⟩ := ι.surjective v
    obtain ⟨b0, rfl⟩ := Additive.ofMul.surjective b
    calc ggLin (p := p) ιA (ψ i) (q (ι (Additive.ofMul b0)))
        = ggLin (p := p) ιA (ψ i) (ιA (Additive.ofMul (γr b0))) := by rw [hprop1 b0]
      _ = ιA (Additive.ofMul (ψ i (γr b0))) := by rw [ggLin_apply_ofMul]
      _ = ιA (Additive.ofMul (γr (φ i b0))) := by rw [hcompat i b0]
      _ = q (ι (Additive.ofMul (φ i b0))) := by rw [hprop1 (φ i b0)]
      _ = q (ggLin (p := p) ι (φ i) (ι (Additive.ofMul b0))) := by rw [ggLin_apply_ofMul]
  refine ⟨V ⧸ spanx, inferInstance, inferInstance, ιA, q, hA, αA, hprop1, ?_, ?_, ?_, ?_, ?_⟩
  · exact Submodule.mkQ_surjective spanx
  · change LinearMap.ker (Submodule.mkQ spanx) = spanx
    exact Submodule.ker_mkQ spanx
  · intro i
    rfl
  · exact hprop5
  · intro i w
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective spanx w
    change ggLin (p := p) ιA (ψ i) (q v) = q v - αA i (q v) • hA i
    calc ggLin (p := p) ιA (ψ i) (q v)
        = q (ggLin (p := p) ι (φ i) v) := hcomm i v
      _ = q (v - α i v • h i) := by rw [hlin i v]
      _ = q v - α i v • q (h i) := by rw [map_sub, map_smul]
      _ = q v - αA i (q v) • q (h i) := by rw [hprop5 i v]
      _ = q v - αA i (q v) • hA i := rfl

end CFSG.StandardType
