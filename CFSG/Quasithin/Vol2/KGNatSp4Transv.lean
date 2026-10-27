module

public import CFSG.Quasithin.Vol2.KGNatSp4Axis
public import CFSG.Quasithin.Vol2.KGNatSp4N13
public import CFSG.Quasithin.Vol2.Ch11SecCFacts4

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)

variable {K : Type} [Field K]

theorem exists_span_eq_range_sub4 [Finite K]
    (T : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K)) (hT1 : ∃ x, T x ≠ x)
    (hcard : Nat.card K ^ 3 ≤ Nat.card (LinearMap.ker (T - LinearMap.id))) :
    ∃ v : Fin 2 ⊕ Fin 2 → K, v ≠ 0 ∧ LinearMap.range (T - LinearMap.id) = K ∙ v := by
  set N := T - LinearMap.id with hN
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hV : Module.finrank K (Fin 2 ⊕ Fin 2 → K) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  have hk : 3 ≤ Module.finrank K (LinearMap.ker N) := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := ↥(LinearMap.ker N))] at hcard
    exact (Nat.pow_le_pow_iff_right hq).mp hcard
  have hk4 : Module.finrank K (LinearMap.ker N) ≠ 4 := by
    intro h4
    have htop : LinearMap.ker N = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [h4, hV])
    obtain ⟨x, hx⟩ := hT1
    apply hx
    have hxk : x ∈ LinearMap.ker N := htop ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, hN, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hxk
    exact hxk
  have hrn := LinearMap.finrank_range_add_finrank_ker N
  rw [hV] at hrn
  have hkle : Module.finrank K (LinearMap.ker N) ≤ 4 := by
    have := Submodule.finrank_le (LinearMap.ker N)
    rwa [hV] at this
  have hr : Module.finrank K (LinearMap.range N) = 1 := by omega
  have hne : LinearMap.range N ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hr
    exact zero_ne_one hr
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨v, hv0, (Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem v
    _).mpr hv) (by rw [finrank_span_singleton hv0, hr])).symm⟩

theorem fix_Usp_iff (x : Fin 2 ⊕ Fin 2 → K) :
    (∀ u ∈ Usp K, mat 2 K u *ᵥ x = x) ↔ x ∈ spLine K := by
  constructor
  · intro h
    have h1 := h _ (qSp_mem_Usp 1 0 0)
    have h2 := h _ (qSp_mem_Usp 0 0 1)
    have h3 := h _ (nSp_mem_Usp 1)
    rw [qSp_mulVec] at h1 h2
    rw [nSp_mulVec] at h3
    have a1 := congrFun h1 (.inl 0)
    have a2 := congrFun h2 (.inl 1)
    have a3 := congrFun h3 (.inl 0)
    simp [vec4] at a1 a2 a3
    exact ⟨a3, a1, a2⟩
  · intro hx u hu
    obtain ⟨x0, y0, z0, r, h⟩ := usp_mulVec hu
    obtain ⟨h1, h2, h3⟩ := hx
    rw [h, nSp_mulVec, qSp_mulVec]
    refine vec4_eq ?_ ?_ ?_ ?_ <;>
      simp [vec4_apply_inl0, vec4_apply_inl1, vec4_apply_inr0, vec4_apply_inr1, h1, h2, h3]

theorem mem_gmapSp_spLine_iff {g : StatedSp 2 K} {x : Fin 2 ⊕ Fin 2 → K} :
    x ∈ gmapSp g (spLine K) ↔ ∃ t : K, x = t • (mat 2 K g *ᵥ vec4 1 0 0 0) :=
  mem_gS1_iff g x

section Real

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥(StatedSp 2 K) →* ↥H} {f : W → (Fin 2 ⊕ Fin 2 → K)}

theorem fixedW_iff_sp (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f)
    {P : Subgroup (MulAut W)} {g : StatedSp 2 K}
    (hg : ∀ x : MulAut W, x ∈ P ↔ ∃ u ∈ Usp K, x = ((π (g * u * g⁻¹) : ↥H) : MulAut W))
    (w : W) : (∀ s ∈ P, s w * w⁻¹ ∈ Z) ↔ f w ∈ gmapSp g (spLine K) := by
  rw [mem_gmapSp, ← fix_Usp_iff]
  constructor
  · intro h u hu
    have h1 := h _ ((hg _).mpr ⟨u, hu, rfl⟩)
    rw [← hf.ker, hf.map_mul_inv, hf.act4, sub_eq_zero] at h1
    have h2 : mat 2 K g⁻¹ *ᵥ (mat 2 K (g * u * g⁻¹) *ᵥ f w) = mat 2 K g⁻¹ *ᵥ f w := by rw [h1]
    rw [conj_mulVec_sp] at h2
    exact h2
  · intro h s hs
    obtain ⟨u, hu, rfl⟩ := (hg s).mp hs
    rw [← hf.ker, hf.map_mul_inv, hf.act4, sub_eq_zero]
    have h1 := h u hu
    have h2 : mat 2 K g *ᵥ (mat 2 K u *ᵥ (mat 2 K g⁻¹ *ᵥ f w)) = f w := by
      rw [h1, mat_mulVec_inv]
    calc mat 2 K (g * u * g⁻¹) *ᵥ f w
        = mat 2 K g *ᵥ (mat 2 K g⁻¹ *ᵥ (mat 2 K (g * u * g⁻¹) *ᵥ f w)) := (mat_mulVec_inv g _).symm
      _ = f w := by rw [conj_mulVec_sp, h2]

end Real

theorem factTransvPointSp4_holds : Ch11.SecC.FactTransvPointSp4 := by
  intro F _ _ n hn hF W _ _ hW H π hπ S hS y hyN hyy hy1 hcard
  have : CharP F 2 := charP_two_of_card (by omega) hF
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usp hF (by omega) hf hS
  have hinj : ∀ a b : W, f a = f b → a = b := fun a b h =>
    mul_inv_eq_one.mp (Subgroup.mem_bot.mp ((hf.eq_iff a b).mp h))
  have hW4 : Nat.card W = Nat.card F ^ 4 := by
    rw [Nat.card_congr (Equiv.ofBijective f ⟨fun a b h => hinj a b h, hf.surj⟩), Nat.card_fun]
    simp
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hC3 : Nat.card F ^ 3 ≤ Nat.card {w : W // y w = w} := by
    have h1 : Nat.card F ^ 4 ≤ Nat.card F * Nat.card {w : W // y w = w} := by
      rw [← hW4, hF]
      exact hcard
    rw [pow_succ'] at h1
    exact Nat.le_of_mul_le_mul_left h1 (by omega)
  obtain ⟨L, hLf, -⟩ := exists_isometry_of_invol hf hyN hyy (by
    calc Nat.card W = Nat.card F ^ 4 := hW4
      _ < Nat.card F ^ 6 := Nat.pow_lt_pow_right hq (by norm_num)
      _ = (Nat.card F ^ 3) ^ 2 := by ring
      _ ≤ Nat.card {w : W // y w = w} ^ 2 := Nat.pow_le_pow_left hC3 2)
  have hT1 : ∃ x, L x ≠ x := by
    by_contra hcon
    push Not at hcon
    apply hy1
    ext w
    exact hinj _ _ ((hLf w).symm.trans (hcon (f w)))
  have hker : Nat.card F ^ 3 ≤ Nat.card (LinearMap.ker (L - LinearMap.id)) := by
    refine hC3.trans (le_of_eq (Nat.card_congr (Equiv.ofBijective
      (fun w : {w : W // y w = w} => (⟨f w, ?_⟩ : LinearMap.ker (L - LinearMap.id)))
      ⟨fun a b hab => Subtype.ext (hinj _ _ (congrArg Subtype.val hab)), fun x => ?_⟩)))
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, hLf, w.2, sub_self]
    · obtain ⟨x, hx⟩ := x
      obtain ⟨w, rfl⟩ := hf.surj x
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, hLf, sub_eq_zero] at hx
      exact ⟨⟨w, hinj _ _ hx⟩, rfl⟩
  obtain ⟨v, hv0, hrange⟩ := exists_span_eq_range_sub4 L hT1 hker
  obtain ⟨γ, hγ⟩ := exists_sp4_lin_eq _ v (v0_ne_zero g) hv0
  set h : MulAut W := ((π γ : ↥H) : MulAut W) with hhdef
  have hact : ∀ x, f (h x) = (linModelNat (StatedSp 2 F)).lin γ (f x) := hf.act γ
  have hlinj : ∀ a b, (linModelNat (StatedSp 2 F)).lin γ a =
      (linModelNat (StatedSp 2 F)).lin γ b → a = b := by
    intro a b hab
    obtain ⟨a', rfl⟩ := hf.surj a
    obtain ⟨b', rfl⟩ := hf.surj b
    rw [← hact, ← hact] at hab
    rw [h.injective (hinj _ _ hab)]
  have hfixS : ∀ x : W, (∀ s ∈ S, s x = x) ↔
      ∃ t : F, f x = t • (mat 2 F g *ᵥ vec4 1 0 0 0) := by
    intro x
    rw [← mem_gmapSp_spLine_iff, ← fixedW_iff_sp hf hg x]
    simp only [Subgroup.mem_bot, mul_inv_eq_one]
  have hsub : ∀ w' : W,
      (L - LinearMap.id : (Fin 2 ⊕ Fin 2 → F) →ₗ[F] (Fin 2 ⊕ Fin 2 → F)) (f w') =
        f (y w' * w'⁻¹) := by
    intro w'
    rw [LinearMap.sub_apply, LinearMap.id_apply, hLf, hf.map_mul_inv]
  refine ⟨h, (π γ).2, fun w => ⟨?_, fun hx => ?_⟩⟩
  · rintro ⟨w', rfl⟩
    rw [hfixS]
    have hmem : f (y w' * w'⁻¹) ∈ LinearMap.range (L - LinearMap.id) := ⟨f w', hsub w'⟩
    rw [hrange, Submodule.mem_span_singleton] at hmem
    obtain ⟨t, ht⟩ := hmem
    refine ⟨t, hlinj _ _ ?_⟩
    rw [← hact, MulAut.apply_inv_self, LinearMap.map_smul, hγ, ht]
  · obtain ⟨t, ht⟩ := (hfixS _).mp hx
    have hfw : f w = t • v := by
      rw [← MulAut.apply_inv_self W h w, hact, ht, LinearMap.map_smul, hγ]
    have hmem : f w ∈ LinearMap.range (L - LinearMap.id) := by
      rw [hrange, Submodule.mem_span_singleton]
      exact ⟨t, hfw.symm⟩
    obtain ⟨z, hz⟩ := hmem
    obtain ⟨w', rfl⟩ := hf.surj z
    exact ⟨w', hinj _ _ (by rw [← hsub, hz])⟩

end CFSG.Quasithin.Vol2.KGNat
