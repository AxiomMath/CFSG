module

public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtSetting
import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
public import CFSG.LocalAnalysis.StandardType.ZS.ExcMatrices
public import CFSG.LocalAnalysis.StandardType.ZS.ImprimSystem

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

@[expose] def IsMonomialIn {ι : Type} (f : Module.Basis ι (ZMod p) U) (g : U ≃ₗ[ZMod p] U) :
    Prop :=
  ∀ i, ∃ j, ∃ x : ZMod p, g (f i) = x • f j

theorem IsMonomialIn.mul {ι : Type} {f : Module.Basis ι (ZMod p) U} {g h : U ≃ₗ[ZMod p] U}
    (hg : IsMonomialIn f g) (hh : IsMonomialIn f h) : IsMonomialIn f (g * h) := by
  intro i
  obtain ⟨j, y, hy⟩ := hh i
  obtain ⟨k, x, hx⟩ := hg j
  refine ⟨k, y * x, ?_⟩
  rw [LinearEquiv.mul_apply, hy, map_smul, hx, smul_smul]

theorem IsMonomialIn.inv {ι : Type} [Finite ι] {f : Module.Basis ι (ZMod p) U}
    {g : U ≃ₗ[ZMod p] U} (hg : IsMonomialIn f g) : IsMonomialIn f g⁻¹ := by
  classical
  choose τ x hx using hg
  have hx_ne_zero : ∀ i, x i ≠ 0 := by
    intro i hxi
    have h1 : g (f i) = 0 := by rw [hx i, hxi, zero_smul]
    have h2 : f i = 0 := g.injective (by simpa using h1)
    exact f.ne_zero i h2
  have hτ_inj : Function.Injective τ := by
    intro i i' hτ
    have hx_i := hx i
    have hx_i' := hx i'
    rw [← hτ] at hx_i'
    have h_prop : x i' • f i = x i • f i' := by
      apply g.injective
      simp only [map_smul, hx_i, hx_i', smul_smul]
      rw [mul_comm]
    exact f.linearIndependent.eq_of_smul_apply_eq_smul_apply
      (x i') (x i) i i' (hx_ne_zero i') h_prop
  have hτ_bij : Function.Bijective τ := (Finite.injective_iff_bijective).mp hτ_inj
  intro j
  obtain ⟨i, hi⟩ := hτ_bij.2 j
  refine ⟨i, (x i)⁻¹, ?_⟩
  have hx_i : g (f i) = x i • f j := by rw [hx i, hi]
  calc
    g⁻¹ (f j) = g⁻¹ ((x i)⁻¹ • g (f i)) := by
      rw [hx_i, inv_smul_smul₀ (hx_ne_zero i)]
    _ = (x i)⁻¹ • g⁻¹ (g (f i)) := by rw [map_smul]
    _ = (x i)⁻¹ • f i := by
      congr 1
      exact LinearEquiv.symm_apply_apply g (f i)

private theorem zsnb_all_monomial_of_refl_monomial {n : ℕ} {f : Module.Basis (Fin n) (ZMod p) U}
    {G : Subgroup (U ≃ₗ[ZMod p] U)} (hG : ReflGen p G)
    (hmono_ref : ∀ r ∈ G, IsRefl p r → IsMonomialIn f r) :
    ∀ g ∈ G, IsMonomialIn f g := by
  intro g hg
  rw [hG] at hg
  induction hg using Subgroup.closure_induction'' with
  | mem t ht => exact hmono_ref t ht.1 ht.2
  | inv_mem t ht =>
      rw [inv_eq_of_mul_eq_one_right ht.2.1]
      exact hmono_ref t ht.1 ht.2
  | one =>
      intro i
      exact ⟨i, 1, by simp⟩
  | mul x y _ _ ihx ihy => exact ihx.mul ihy

private theorem zsnb_imprimitive_of_monomial {n : ℕ} (hn : 2 ≤ n)
    {f : Module.Basis (Fin n) (ZMod p) U} {G : Subgroup (U ≃ₗ[ZMod p] U)}
    (hall : ∀ g ∈ G, IsMonomialIn f g) :
    Quasithin.SimsG4.IsImprimitiveOnV G := by
  set W : Fin n → Submodule (ZMod p) U := fun i => Submodule.span (ZMod p) {f i} with hW
  have hW_ne : ∀ i, W i ≠ ⊥ := by
    intro i
    simpa [hW, Submodule.span_singleton_eq_bot] using f.ne_zero i
  have hW_ind : iSupIndep W := by
    simpa only [hW] using f.linearIndependent.iSupIndep_span_singleton
  have hW_sup : (⨆ i, W i) = ⊤ := by
    simp only [hW]
    rw [Submodule.iSup_span, Set.iUnion_singleton_eq_range, f.span_eq]
  have hW_perm : ∀ g ∈ G, ∀ i, ∃ j, (W i).map (g : U →ₗ[ZMod p] U) = W j := by
    intro g hg i
    obtain ⟨j, x, hx⟩ := hall g hg i
    have hx_ne : x ≠ 0 := by
      intro hx0
      have h1 : g (f i) = 0 := by rw [hx, hx0, zero_smul]
      have h2 : f i = 0 := g.injective (by simpa using h1)
      exact f.ne_zero i h2
    refine ⟨j, ?_⟩
    calc
      (W i).map (g : U →ₗ[ZMod p] U)
          = (Submodule.span (ZMod p) {f i}).map (g : U →ₗ[ZMod p] U) := by simp only [hW]
      _ = Submodule.span (ZMod p) {g (f i)} := by
        rw [Submodule.map_span, Set.image_singleton]
        rfl
      _ = Submodule.span (ZMod p) {x • f j} := by rw [hx]
      _ = Submodule.span (ZMod p) {f j} :=
        Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hx_ne) (f j)
      _ = W j := by simp only [hW]
  exact ⟨n, W, by omega, hW_ne, hW_ind, hW_sup, hW_perm⟩

theorem exists_isRefl_not_isMonomialIn {n : ℕ} (hn : 2 ≤ n) (f : Module.Basis (Fin n) (ZMod p) U)
    {G : Subgroup (U ≃ₗ[ZMod p] U)} (hG : ReflGen p G)
    (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV G) :
    ∃ r ∈ G, IsRefl p r ∧ ¬ IsMonomialIn f r := by
  by_contra hcon
  have hmono_ref : ∀ r ∈ G, IsRefl p r → IsMonomialIn f r := by
    intro r hr href
    by_contra hnot
    exact hcon ⟨r, hr, href, hnot⟩
  exact hprim (zsnb_imprimitive_of_monomial hn (zsnb_all_monomial_of_refl_monomial hG hmono_ref))

namespace ImpExtSetting

variable [Module.Finite (ZMod p) U] {G H : Subgroup (U ≃ₗ[ZMod p] U)} {d : ℕ}

omit [Module.Finite (ZMod p) U] in
private theorem zsnb_apply_mem_of_movedSpace_le {W : Submodule (ZMod p) U}
    {t : U ≃ₗ[ZMod p] U} (h : HardMathSupport.Kantor79.movedSpace t ≤ W) {v : U}
    (hv : v ∈ W) : t v ∈ W := by
  have hmem : t v - v ∈ HardMathSupport.Kantor79.movedSpace t := by
    refine ⟨v, ?_⟩
    simp
  have heq : t v = v + (t v - v) := by abel
  rw [heq]
  exact W.add_mem hv (h hmem)

omit [Module.Finite (ZMod p) U] in
private theorem zsnb_map_le_of_movedSpace_le {W : Submodule (ZMod p) U}
    {t : U ≃ₗ[ZMod p] U} (h : HardMathSupport.Kantor79.movedSpace t ≤ W) :
    W.map (t : U →ₗ[ZMod p] U) ≤ W := by
  rintro w ⟨v, hv, rfl⟩
  exact zsnb_apply_mem_of_movedSpace_le h hv

omit [Module.Finite (ZMod p) U] in
private theorem zsnb_movedSpace_conj (g x : U ≃ₗ[ZMod p] U) :
    HardMathSupport.Kantor79.movedSpace (g * x * g⁻¹) =
      (HardMathSupport.Kantor79.movedSpace x).map (g : U →ₗ[ZMod p] U) := by
  ext y
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨x (g⁻¹ v) - g⁻¹ v, ⟨g⁻¹ v, by simp⟩, ?_⟩
    simp
  · rintro ⟨u, ⟨v, rfl⟩, rfl⟩
    refine ⟨g v, ?_⟩
    simp

omit [Module.Finite (ZMod p) U] in
private theorem zsnb_exists_refl_not_map (S : ImpExtSetting G H d) :
    ∃ s ∈ G, IsRefl p s ∧
      ¬ (HardMathSupport.Kantor79.commutatorSpace H).map (s : U →ₗ[ZMod p] U) ≤
        HardMathSupport.Kantor79.commutatorSpace H := by
  by_contra h
  have hmap : ∀ r ∈ G, IsRefl p r →
      (HardMathSupport.Kantor79.commutatorSpace H).map (r : U →ₗ[ZMod p] U) ≤
        HardMathSupport.Kantor79.commutatorSpace H := by
    intro r hr hrfl
    by_contra hnot
    exact h ⟨r, hr, hrfl, hnot⟩
  have hinv : ∀ g ∈ G, ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace H,
      g v ∈ HardMathSupport.Kantor79.commutatorSpace H := by
    intro g hg
    rw [S.reflGen] at hg
    induction hg using Subgroup.closure_induction'' with
    | mem t ht =>
        intro v hv
        exact hmap t ht.1 ht.2 (Submodule.mem_map_of_mem (f := (t : U →ₗ[ZMod p] U)) hv)
    | inv_mem t ht =>
        intro v hv
        rw [inv_eq_of_mul_eq_one_right ht.2.1]
        exact hmap t ht.1 ht.2 (Submodule.mem_map_of_mem (f := (t : U →ₗ[ZMod p] U)) hv)
    | one =>
        intro v hv
        simpa using hv
    | mul x y _ _ ihx ihy =>
        intro v hv
        exact ihx (y v) (ihy v hv)
  have hfin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H) =
      Module.finrank (ZMod p) U - 1 := S.splitSupport.2.1
  have h4 := S.four_le_finrank
  rcases S.absIrred.1 (HardMathSupport.Kantor79.commutatorSpace H) hinv with hbot | htop
  · rw [hbot, finrank_bot] at hfin
    omega
  · have : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H) =
        Module.finrank (ZMod p) U := by rw [htop, finrank_top]
    omega

omit [Module.Finite (ZMod p) U] in
private theorem zsnb_iSup_map_invariant {H : Subgroup (U ≃ₗ[ZMod p] U)}
    {W : Submodule (ZMod p) U} :
    ∀ k ∈ H, ∀ x ∈ (⨆ h : H, W.map (h : U →ₗ[ZMod p] U)), k x ∈
      (⨆ h : H, W.map (h : U →ₗ[ZMod p] U)) := by
  intro k hk x hx
  refine Submodule.iSup_induction
    (motive := fun z => k z ∈ (⨆ h : H, W.map (h : U →ₗ[ZMod p] U)))
    (fun h : H => W.map (h : U →ₗ[ZMod p] U)) hx ?_ ?_ ?_
  · rintro h y ⟨u, hu, rfl⟩
    exact Submodule.mem_iSup_of_mem (⟨k, hk⟩ * h)
      ⟨u, hu, by simp [Subgroup.coe_mul]⟩
  · simp
  · intro x y hx hy
    rw [map_add]
    exact add_mem hx hy

omit [Module.Finite (ZMod p) U] in
private theorem zsnb_iSup_map_le {H : Subgroup (U ≃ₗ[ZMod p] U)}
    {W V : Submodule (ZMod p) U} (hinv : ∀ k ∈ H, ∀ w ∈ W, k w ∈ V) :
    (⨆ h : H, W.map (h : U →ₗ[ZMod p] U)) ≤ V := by
  refine iSup_le (fun h : H => ?_)
  rintro y ⟨u, hu, rfl⟩
  exact hinv (h : U ≃ₗ[ZMod p] U) h.2 u hu

omit [Module.Finite (ZMod p) U] in
private theorem zsnb_iSup_map_ne_bot {H : Subgroup (U ≃ₗ[ZMod p] U)}
    {W : Submodule (ZMod p) U} (hW : W ≠ ⊥) :
    (⨆ h : H, W.map (h : U →ₗ[ZMod p] U)) ≠ ⊥ := by
  intro hbot
  have hle : W ≤ (⨆ h : H, W.map (h : U →ₗ[ZMod p] U)) := by
    have h1 := le_iSup (fun h : H => W.map (h : U →ₗ[ZMod p] U)) (1 : H)
    simpa using h1
  exact hW (le_bot_iff.mp (hbot ▸ hle))

omit [Module.Finite (ZMod p) U] in
private theorem zsnb_conj_le {f : Module.Basis (Fin 4) (ZMod p) U}
    (S : ImpExtSetting G H d) {s d₀ : U ≃ₗ[ZMod p] U}
    (hsG : s ∈ G) (hsRefl : IsRefl p s) (hsMono : IsMonomialIn f s)
    (hd0G : d₀ ∈ G) (hd0Refl : IsRefl p d₀) (hd0NonMono : ¬ IsMonomialIn f d₀)
    (hA : ∀ r, r ∈ G → IsRefl p r → ¬ IsMonomialIn f r →
      HardMathSupport.Kantor79.movedSpace r ≤ HardMathSupport.Kantor79.commutatorSpace H)
    (hH : ∀ h ∈ H, IsMonomialIn f h) (h : H) :
    ((HardMathSupport.Kantor79.movedSpace d₀).map (h : U →ₗ[ZMod p] U)).map
        (s : U →ₗ[ZMod p] U) ≤ HardMathSupport.Kantor79.commutatorSpace H := by
  have hgG : s * (h : U ≃ₗ[ZMod p] U) ∈ G := G.mul_mem hsG (S.H_le h.2)
  have hgMono : IsMonomialIn f (s * (h : U ≃ₗ[ZMod p] U)) :=
    IsMonomialIn.mul hsMono (hH (h : U ≃ₗ[ZMod p] U) h.2)
  have hconjG : (s * (h : U ≃ₗ[ZMod p] U)) * d₀ * (s * (h : U ≃ₗ[ZMod p] U))⁻¹ ∈ G :=
    G.mul_mem (G.mul_mem hgG hd0G) (G.inv_mem hgG)
  have hconjRefl : IsRefl p ((s * (h : U ≃ₗ[ZMod p] U)) * d₀ *
      (s * (h : U ≃ₗ[ZMod p] U))⁻¹) := IsRefl.conj hd0Refl (s * (h : U ≃ₗ[ZMod p] U))
  have hconjNonMono : ¬ IsMonomialIn f ((s * (h : U ≃ₗ[ZMod p] U)) * d₀ *
      (s * (h : U ≃ₗ[ZMod p] U))⁻¹) := by
    intro hmono
    have hginv : (s * (h : U ≃ₗ[ZMod p] U))⁻¹ = (h : U ≃ₗ[ZMod p] U)⁻¹ * s := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hsRefl.1]
    have hginvMono : IsMonomialIn f ((s * (h : U ≃ₗ[ZMod p] U))⁻¹) := by
      rw [hginv]
      exact IsMonomialIn.mul (IsMonomialIn.inv (hH (h : U ≃ₗ[ZMod p] U) h.2)) hsMono
    exact hd0NonMono (by
      have heq : d₀ = (s * (h : U ≃ₗ[ZMod p] U))⁻¹ * ((s * (h : U ≃ₗ[ZMod p] U)) * d₀ *
        (s * (h : U ≃ₗ[ZMod p] U))⁻¹) * (s * (h : U ≃ₗ[ZMod p] U)) := by group
      rw [heq]
      simpa [mul_assoc] using
        IsMonomialIn.mul hginvMono (IsMonomialIn.mul hmono hgMono))
  have hle := hA _ hconjG hconjRefl hconjNonMono
  rw [zsnb_movedSpace_conj] at hle
  rintro y ⟨w, ⟨u, hu, rfl⟩, rfl⟩
  exact hle ⟨u, hu, rfl⟩

omit [Module.Finite (ZMod p) U] in
private theorem zsnb_map_le_of_forall_conj {f : Module.Basis (Fin 4) (ZMod p) U}
    (S : ImpExtSetting G H d) {s d₀ : U ≃ₗ[ZMod p] U}
    (hsG : s ∈ G) (hsRefl : IsRefl p s) (hsMono : IsMonomialIn f s)
    (hd0G : d₀ ∈ G) (hd0Refl : IsRefl p d₀) (hd0NonMono : ¬ IsMonomialIn f d₀)
    (hA : ∀ r, r ∈ G → IsRefl p r → ¬ IsMonomialIn f r →
      HardMathSupport.Kantor79.movedSpace r ≤ HardMathSupport.Kantor79.commutatorSpace H)
    (hH : ∀ h ∈ H, IsMonomialIn f h) :
    (HardMathSupport.Kantor79.commutatorSpace H).map (s : U →ₗ[ZMod p] U) ≤
      HardMathSupport.Kantor79.commutatorSpace H := by
  have hd0le : HardMathSupport.Kantor79.movedSpace d₀ ≤
      HardMathSupport.Kantor79.commutatorSpace H := hA d₀ hd0G hd0Refl hd0NonMono
  set X : Submodule (ZMod p) U :=
    ⨆ h : H, (HardMathSupport.Kantor79.movedSpace d₀).map (h : U →ₗ[ZMod p] U) with hX
  have hXinv : ∀ k ∈ H, ∀ x ∈ X, k x ∈ X := by
    rw [hX]
    exact zsnb_iSup_map_invariant
  have hXle : X ≤ HardMathSupport.Kantor79.commutatorSpace H := by
    rw [hX]
    exact zsnb_iSup_map_le (fun k hk w hw => apply_mem_commutatorSpace hk (hd0le hw))
  have hXne : X ≠ ⊥ := by
    rw [hX]
    exact zsnb_iSup_map_ne_bot (by
      intro hb
      have := hd0Refl.2
      have hb' : LinearMap.range ((d₀ : U →ₗ[ZMod p] U) - LinearMap.id) = ⊥ := hb
      rw [hb', finrank_bot] at this
      exact Nat.zero_ne_one this)
  have hXeq : X = HardMathSupport.Kantor79.commutatorSpace H := by
    rcases S.splitSupport.2.2 X bot_le hXle hXinv with h | h
    · exact absurd h hXne
    · exact h
  have hXsle : X.map (s : U →ₗ[ZMod p] U) ≤
      HardMathSupport.Kantor79.commutatorSpace H := by
    rw [hX, Submodule.map_iSup]
    exact iSup_le (fun h : H =>
      zsnb_conj_le S hsG hsRefl hsMono hd0G hd0Refl hd0NonMono hA hH h)
  rwa [hXeq] at hXsle

omit [Module.Finite (ZMod p) U] in
theorem exists_isRefl_not_isMonomialIn_not_le (S : ImpExtSetting G H d)
    (f : Module.Basis (Fin 4) (ZMod p) U) (hH : ∀ h ∈ H, IsMonomialIn f h) :
    ∃ r ∈ G, IsRefl p r ∧ ¬ IsMonomialIn f r ∧
      ¬ HardMathSupport.Kantor79.movedSpace r ≤ HardMathSupport.Kantor79.commutatorSpace H := by
  by_contra hcon
  have hA : ∀ r, r ∈ G → IsRefl p r → ¬ IsMonomialIn f r →
      HardMathSupport.Kantor79.movedSpace r ≤ HardMathSupport.Kantor79.commutatorSpace H := by
    intro r hr hrfl hnr
    by_contra hle
    exact hcon ⟨r, hr, hrfl, hnr, hle⟩
  obtain ⟨s, hsG, hsRefl, hsNotMap⟩ := zsnb_exists_refl_not_map S
  have hsMono : IsMonomialIn f s := by
    by_contra hns
    exact hsNotMap (zsnb_map_le_of_movedSpace_le (hA s hsG hsRefl hns))
  obtain ⟨d₀, hd0G, hd0Refl, hd0NonMono⟩ :=
    exists_isRefl_not_isMonomialIn (n := 4) (by norm_num) f S.reflGen S.primitive
  exact hsNotMap (zsnb_map_le_of_forall_conj S hsG hsRefl hsMono hd0G hd0Refl hd0NonMono hA hH)

end ImpExtSetting

end CFSG.StandardType.ZS

end
