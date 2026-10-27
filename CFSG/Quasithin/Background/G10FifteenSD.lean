module

public import CFSG.Quasithin.Background.G10FifteenRing
public import CFSG.Quasithin.Background.G10Stmts

public section

namespace CFSG.Quasithin

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem selfDual_of_nondegOn {H : Subgroup (GLV V)} {B : LinearMap.BilinForm (ZMod 2) V}
    {I : Submodule (ZMod 2) V} (hrefl : B.IsRefl)
    (hiso : ∀ k ∈ H, ∀ v w, B (k v) (k w) = B v w) (hnd : NondegOn B I) : SelfDual H I := by
  refine ⟨B.restrict I, ⟨fun x hx => ?_, fun y hy => ?_⟩, fun k hk i j i' j' hi hj => ?_⟩
  · apply Subtype.ext
    exact hnd x x.2 fun w hw => hx ⟨w, hw⟩
  · apply Subtype.ext
    exact hnd y y.2 fun w hw => hrefl _ _ (hy ⟨w, hw⟩)
  · show B (i' : V) (j' : V) = B (i : V) (j : V)
    rw [← hi, ← hj]
    exact hiso k hk _ _

theorem selfDual_of_isDualOf_hiso {H : Subgroup (GLV V)} {I J : Submodule (ZMod 2) V}
    (hd : IsDualOf H I J) (h : HIso H I J) : SelfDual H I := by
  obtain ⟨β, hβ1, hβ2, hβ3⟩ := hd
  obtain ⟨φ, hφ⟩ := h
  refine ⟨β.comp φ.toLinearMap, ⟨fun x hx => ?_, fun y hy => ?_⟩, fun k hk i j i' j' hi hj => ?_⟩
  · have : φ x = 0 := hβ1 _ fun i => hx i
    exact φ.injective (by rw [this, map_zero])
  · apply hβ2
    intro j
    obtain ⟨i, rfl⟩ := φ.surjective j
    exact hy i
  · have h1 := hφ k hk i i' hi
    have h2 : (k : GLV V) ((φ i : ↥J) : V) = ((φ i' : ↥J) : V) := h1
    exact hβ3 k hk (φ i) (φ i') j j' h2 hj

theorem fixes_dual_of_fixes {H : Subgroup (GLV V)} {I J : Submodule (ZMod 2) V}
    (hI : Invariant H I) (hJ : Invariant H J) (hd : IsDualOf H I J) {k : GLV V} (hk : k ∈ H)
    (hki : ∀ i ∈ I, k i = i) : ∀ j ∈ J, k j = j := by
  obtain ⟨β, hβ1, -, hβ3⟩ := hd
  intro j hj
  have hkj : k j ∈ J := hJ k hk j hj
  have hkinv : ∀ i : ↥I, k⁻¹ (i : V) = i := fun i => by
    have h1 := hki i i.2
    calc k⁻¹ (i : V) = k.symm (k (i : V)) := by rw [h1]; rfl
      _ = i := LinearEquiv.symm_apply_apply k _
  have h0 : (⟨k j + j, J.add_mem hkj hj⟩ : ↥J) = 0 := by
    apply hβ1
    intro i
    have h1 := hβ3 k hk ⟨j, hj⟩ ⟨k j, hkj⟩ ⟨k⁻¹ (i : V), hI _ (H.inv_mem hk) _ i.2⟩ i rfl
      (LinearEquiv.apply_symm_apply k (i : V))
    have h2 : (⟨k⁻¹ (i : V), hI _ (H.inv_mem hk) _ i.2⟩ : ↥I) = i := Subtype.ext (hkinv i)
    rw [h2] at h1
    have h3 : (⟨k j + j, J.add_mem hkj hj⟩ : ↥J) = ⟨k j, hkj⟩ + ⟨j, hj⟩ := rfl
    rw [h3, map_add, LinearMap.add_apply, h1]
    exact CharTwo.add_self_eq_zero _
  have h4 : k j + j = 0 := congrArg Subtype.val h0
  have h5 : k j = -j := eq_neg_of_add_eq_zero_left h4
  have h6 : -j = j := neg_eq_of_add_eq_zero_left (add_self_eq_zero_of_zmod2 j)
  rw [h5, h6]

theorem IsDualOf.symm {H : Subgroup (GLV V)} {I J : Submodule (ZMod 2) V} (hd : IsDualOf H I J) :
    IsDualOf H J I := by
  obtain ⟨β, hβ1, hβ2, hβ3⟩ := hd
  exact ⟨β.flip, hβ2, hβ1, fun k hk i i' j j' hi hj => hβ3 k hk j j' i i' hj hi⟩

theorem centralizerOn_eq_of_isDualOf {H : Subgroup (GLV V)} {I J : Submodule (ZMod 2) V}
    (hI : Invariant H I) (hJ : Invariant H J) (hd : IsDualOf H I J) :
    centralizerOn H I = centralizerOn H J := by
  ext k
  constructor
  · rintro ⟨hk, hki⟩
    exact ⟨hk, fixes_dual_of_fixes hI hJ hd hk hki⟩
  · rintro ⟨hk, hkj⟩
    exact ⟨hk, fixes_dual_of_fixes hJ hI hd.symm hk hkj⟩

@[expose] def transvAut {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (φ : Module.Dual (ZMod 2) M) (v : M) (h : φ v = 0) : M ≃ₗ[ZMod 2] M where
  toFun u := u + φ u • v
  invFun u := u + φ u • v
  map_add' a b := by
    simp only [map_add, add_smul]
    abel
  map_smul' c a := by
    simp only [map_smul, smul_eq_mul, smul_add, RingHom.id_apply, mul_smul]
  left_inv u := by
    have h2 : φ u • v + φ u • v = 0 := by
      rw [← two_smul (ZMod 2) (φ u • v), show (2 : ZMod 2) = 0 from rfl, zero_smul]
    simp only [map_add, map_smul, h, smul_zero, add_zero]
    rw [add_assoc, h2, add_zero]
  right_inv u := by
    have h2 : φ u • v + φ u • v = 0 := by
      rw [← two_smul (ZMod 2) (φ u • v), show (2 : ZMod 2) = 0 from rfl, zero_smul]
    simp only [map_add, map_smul, h, smul_zero, add_zero]
    rw [add_assoc, h2, add_zero]

theorem transvAut_apply {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (φ : Module.Dual (ZMod 2) M) (v : M) (h : φ v = 0) (u : M) :
    transvAut φ v h u = u + φ u • v := rfl

theorem not_autAll_of_selfDual {H : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}
    (hI : 2 < Module.finrank (ZMod 2) I) (hsd : SelfDual H I) : ¬ AutAll H I := by
  intro hall
  obtain ⟨f, ⟨hfl, -⟩, hinv⟩ := hsd
  have hGL : ∀ g : ↥I ≃ₗ[ZMod 2] ↥I, ∀ i j : ↥I, f (g i) (g j) = f i j := by
    intro g i j
    obtain ⟨k, hk, hkg⟩ := hall g
    exact hinv k hk i j (g i) (g j) (hkg i) (hkg j)
  have hne : ∃ i j : ↥I, f i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hnt : Nontrivial ↥I := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
    obtain ⟨i, hi⟩ := exists_ne (0 : ↥I)
    exact hi (hfl i (hcon i))
  obtain ⟨i, j, hij⟩ := hne
  have hk : ∃ k : ↥I, k ∉ Submodule.span (ZMod 2) {i, j} := by
    by_contra hcon
    push Not at hcon
    have htop : Submodule.span (ZMod 2) {i, j} = ⊤ := eq_top_iff.2 fun x _ => hcon x
    have h1 : Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) {i, j}) ≤ 2 := by
      classical
      have := finrank_span_finset_le_card (R := ZMod 2) ({i, j} : Finset ↥I)
      simp only [Finset.coe_insert, Finset.coe_singleton] at this
      exact this.trans Finset.card_le_two
    rw [htop, finrank_top] at h1
    omega
  obtain ⟨k, hk⟩ := hk
  obtain ⟨φ, hφk, hφle⟩ := Submodule.exists_le_ker_of_notMem hk
  have hφi : φ i = 0 := hφle (Submodule.subset_span (Set.mem_insert _ _))
  have hφj : φ j = 0 :=
    hφle (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hφk1 : φ k = 1 := by
    have hc : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
    exact hc _ hφk
  have h1 := hGL (transvAut φ j hφj) i k
  rw [transvAut_apply, transvAut_apply, hφi, hφk1, zero_smul, add_zero, one_smul, map_add] at h1
  apply hij
  have := congrArg (fun z => z - f i k) h1
  simp only [sub_self] at this
  linear_combination this

theorem finite_dual [Finite V] (U : Submodule (ZMod 2) V) : Finite (↥U →ₗ[ZMod 2] ZMod 2) := by
  classical
  let b := Module.finBasis (ZMod 2) ↥U
  exact Finite.of_injective
    (fun f : ↥U →ₗ[ZMod 2] ZMod 2 => fun j : Fin (Module.finrank (ZMod 2) U) => f (b j))
    (fun f g hfg => b.ext fun j => congrFun hfg j)

theorem card_dual_le [Finite V] (U : Submodule (ZMod 2) V) :
    Nat.card (↥U →ₗ[ZMod 2] ZMod 2) ≤ 2 ^ Module.finrank (ZMod 2) U := by
  classical
  let b := Module.finBasis (ZMod 2) ↥U
  have hinj : Function.Injective
      (fun f : ↥U →ₗ[ZMod 2] ZMod 2 => fun j : Fin (Module.finrank (ZMod 2) U) => f (b j)) := by
    intro f g hfg
    exact b.ext fun j => congrFun hfg j
  have h1 := Nat.card_le_card_of_injective _ hinj
  have h2 : Nat.card (Fin (Module.finrank (ZMod 2) U) → ZMod 2) =
      2 ^ Module.finrank (ZMod 2) U := by
    rw [Nat.card_fun, Nat.card_zmod]
    simp
  rw [h2] at h1
  exact h1


theorem hiso_of_selfDual_isDual [Finite V] {H : Subgroup (GLV V)} {I J : Submodule (ZMod 2) V}
    (hI : Invariant H I) (hJ : Invariant H J) (hsd : SelfDual H I) (hd : IsDualOf H I J) :
    HIso H I J := by
  classical
  obtain ⟨f, hfnd, hfinv⟩ := hsd
  obtain ⟨β, hβ1, hβ2, hβ3⟩ := hd
  have hβinj : Function.Injective (fun j : ↥J => β j) := by
    intro j j' h
    have h0 : β (j + j') = 0 := by
      rw [β.map_add]
      ext i
      simp only [LinearMap.add_apply, LinearMap.zero_apply]
      rw [← congrArg (fun g : ↥I →ₗ[ZMod 2] ZMod 2 => g i) h]
      exact CharTwo.add_self_eq_zero _
    have := hβ1 (j + j') (fun i => by rw [h0]; rfl)
    have h3 : j = -j' := eq_neg_of_add_eq_zero_left this
    rw [h3]
    exact neg_eq_of_add_eq_zero_left (add_self_eq_zero_of_zmod2 j')
  have hβ2inj : Function.Injective (fun i : ↥I => β.flip i) := by
    intro i i' h
    have h0 : β.flip (i + i') = 0 := by
      rw [β.flip.map_add]
      ext a
      simp only [LinearMap.add_apply, LinearMap.zero_apply]
      rw [← congrArg (fun g : ↥J →ₗ[ZMod 2] ZMod 2 => g a) h]
      exact CharTwo.add_self_eq_zero _
    have := hβ2 (i + i') (fun j => by
      have := LinearMap.congr_fun h0 j
      simpa using this)
    have h3 : i = -i' := eq_neg_of_add_eq_zero_left this
    rw [h3]
    exact neg_eq_of_add_eq_zero_left (add_self_eq_zero_of_zmod2 i')
  have hcardI := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥I)
  have hcardJ := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥J)
  rw [Nat.card_zmod] at hcardI hcardJ
  have := finite_dual I
  have := finite_dual J
  have h1 : Nat.card ↥J ≤ Nat.card (↥I →ₗ[ZMod 2] ZMod 2) :=
    Nat.card_le_card_of_injective _ hβinj
  have h2 : Nat.card ↥I ≤ Nat.card (↥J →ₗ[ZMod 2] ZMod 2) :=
    Nat.card_le_card_of_injective _ hβ2inj
  have h3 := card_dual_le I
  have h4 := card_dual_le J
  have e1 : 2 ^ Module.finrank (ZMod 2) J ≤ 2 ^ Module.finrank (ZMod 2) I := by
    rw [← hcardJ]
    exact h1.trans h3
  have e2 : 2 ^ Module.finrank (ZMod 2) I ≤ 2 ^ Module.finrank (ZMod 2) J := by
    rw [← hcardI]
    exact h2.trans h4
  have hIJ : Module.finrank (ZMod 2) I = Module.finrank (ZMod 2) J :=
    le_antisymm ((Nat.pow_le_pow_iff_right Nat.one_lt_two).1 e2)
      ((Nat.pow_le_pow_iff_right Nat.one_lt_two).1 e1)
  have hle : Nat.card (↥I →ₗ[ZMod 2] ZMod 2) ≤ Nat.card ↥J := by
    rw [hcardJ, ← hIJ]
    exact h3
  have hbij : Function.Bijective (fun j : ↥J => β j) := hβinj.bijective_of_nat_card_le hle
  let e : ↥J ≃ₗ[ZMod 2] Module.Dual (ZMod 2) ↥I := LinearEquiv.ofBijective β hbij
  let Φ : ↥I ≃ₗ[ZMod 2] ↥J := (f.toDual hfnd).trans e.symm
  have hΦ : ∀ (i : ↥I) (i' : ↥I), β (Φ i) i' = f i i' := by
    intro i i'
    have := e.apply_symm_apply (f.toDual hfnd i)
    have h2 : β (Φ i) = f.toDual hfnd i := this
    rw [h2]
    rfl
  refine ⟨Φ, fun k hk i j hkij => ?_⟩
  have hkj : (k : GLV V) ((Φ i : ↥J) : V) ∈ J := hJ k hk _ (Φ i).2
  have key : (fun j : ↥J => β j) ⟨(k : GLV V) ((Φ i : ↥J) : V), hkj⟩ = (fun j : ↥J => β j) (Φ j) := by
    refine LinearMap.ext fun i' => ?_
    have hi₂ : (k : GLV V)⁻¹ (i' : V) ∈ I := hI _ (H.inv_mem hk) _ i'.2
    have h1 := hβ3 k hk (Φ i) ⟨(k : GLV V) ((Φ i : ↥J) : V), hkj⟩ ⟨(k : GLV V)⁻¹ (i' : V), hi₂⟩ i'
      rfl (LinearEquiv.apply_symm_apply (k : GLV V) (i' : V))
    have h2 := hfinv k hk i ⟨(k : GLV V)⁻¹ (i' : V), hi₂⟩ j i' hkij
      (LinearEquiv.apply_symm_apply (k : GLV V) (i' : V))
    show β ⟨(k : GLV V) ((Φ i : ↥J) : V), hkj⟩ i' = β (Φ j) i'
    rw [h1, hΦ, hΦ]
    exact h2.symm
  exact congrArg Subtype.val (hβinj key)

end G11

end CFSG.Quasithin
