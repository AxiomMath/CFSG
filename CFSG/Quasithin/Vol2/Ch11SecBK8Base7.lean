module

public import CFSG.Quasithin.Vol2.Ch11SecBK8Base4

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H
open scoped commutatorElement

variable {G : Type} [Group G] {W : Subgroup G} {hW : IsElemAbelian 2 W} {K : Type} [Field K]

@[expose] noncomputable def psi (Φ : IntMod W hW ≃* W6 K) : W6 K →* G where
  toFun v := (Φ.symm v).val
  map_one' := by rw [map_one]; rfl
  map_mul' a b := by rw [map_mul]; rfl

theorem psi_apply (Φ : IntMod W hW ≃* W6 K) (v : W6 K) : psi Φ v = (Φ.symm v).val := rfl

theorem psi_mem (Φ : IntMod W hW ≃* W6 K) (v : W6 K) : psi Φ v ∈ W := (Φ.symm v).val_mem

theorem psi_injective (Φ : IntMod W hW ≃* W6 K) : Function.Injective (psi Φ) :=
  fun _ _ h => Φ.symm.injective (IntMod.val_injective h)

theorem exists_psi_eq (Φ : IntMod W hW ≃* W6 K) {w : G} (hw : w ∈ W) : ∃ v, psi Φ v = w :=
  ⟨Φ (IntMod.mk hW ⟨w, hw⟩), by rw [psi_apply, MulEquiv.symm_apply_apply]; rfl⟩

@[expose] noncomputable def hat (Φ : IntMod W hW ≃* W6 K) (x : G)
    (hx : x ∈ Subgroup.normalizer (W : Set G)) : MulAut (W6 K) :=
  congrHom Φ (convI hW ⟨x, hx⟩)

theorem psi_hat (Φ : IntMod W hW ≃* W6 K) {x : G} (hx : x ∈ Subgroup.normalizer (W : Set G))
    (v : W6 K) : psi Φ (hat Φ x hx v) = x * psi Φ v * x⁻¹ := by
  rw [psi_apply, psi_apply, hat, congrHom_apply, MulEquiv.symm_apply_apply, convI_apply_val]

theorem hat_mul (Φ : IntMod W hW ≃* W6 K) {x y : G} (hx : x ∈ Subgroup.normalizer (W : Set G))
    (hy : y ∈ Subgroup.normalizer (W : Set G)) (hxy : x * y ∈ Subgroup.normalizer (W : Set G)) :
    hat Φ (x * y) hxy = hat Φ x hx * hat Φ y hy := by
  unfold hat
  rw [← map_mul, ← map_mul]
  rfl

theorem hat_inv (Φ : IntMod W hW ≃* W6 K) {x : G} (hx : x ∈ Subgroup.normalizer (W : Set G))
    (hxi : x⁻¹ ∈ Subgroup.normalizer (W : Set G)) : hat Φ x⁻¹ hxi = (hat Φ x hx)⁻¹ := by
  unfold hat
  rw [← map_inv, ← map_inv]
  rfl

theorem hat_pow (Φ : IntMod W hW ≃* W6 K) {x : G} (hx : x ∈ Subgroup.normalizer (W : Set G))
    (k : ℕ) (hxk : x ^ k ∈ Subgroup.normalizer (W : Set G)) :
    hat Φ (x ^ k) hxk = hat Φ x hx ^ k := by
  unfold hat
  rw [← map_pow, ← map_pow]
  rfl

theorem hat_eq_one_iff (Φ : IntMod W hW ≃* W6 K) {x : G}
    (hx : x ∈ Subgroup.normalizer (W : Set G)) :
    hat Φ x hx = 1 ↔ x ∈ Subgroup.centralizer (W : Set G) := by
  rw [← convI_eq_one_iff hW ⟨x, hx⟩, hat, ← map_one (congrHom Φ)]
  exact (congrHom_injective Φ).eq_iff

theorem mem_map_autI (Φ : IntMod W hW ≃* W6 K) {E : Subgroup G} {y : MulAut (W6 K)} :
    y ∈ (autI hW E).map (congrHom Φ) ↔
      ∃ (x : G) (hx : x ∈ Subgroup.normalizer (W : Set G)), x ∈ E ∧ hat Φ x hx = y := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨g, hgE, rfl⟩ := (mem_autI hW).mp hz
    exact ⟨g, g.2, hgE, rfl⟩
  · rintro ⟨x, hx, hxE, rfl⟩
    exact ⟨_, convI_mem_autI hW hxE hx, rfl⟩

theorem hat_mem_map_autI (Φ : IntMod W hW ≃* W6 K) {E : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (W : Set G)) (hxE : x ∈ E) :
    hat Φ x hx ∈ (autI hW E).map (congrHom Φ) :=
  (mem_map_autI Φ).mpr ⟨x, hx, hxE, rfl⟩

theorem hat_mem_normD (Φ : IntMod W hW ≃* W6 K) {L : Subgroup G}
    (hL : (autI hW L).map (congrHom Φ) = diagSL K) {x : G}
    (hx : x ∈ Subgroup.normalizer (W : Set G)) (hxL : x ∈ Subgroup.normalizer (L : Set G)) :
    hat Φ x hx ∈ normD K := by
  have hxi : x⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ hxL
  refine Subgroup.mem_normalizer_iff.mpr fun h => ?_
  rw [← SetLike.mem_coe, ← SetLike.mem_coe, ← hL, SetLike.mem_coe, SetLike.mem_coe,
    mem_map_autI, mem_map_autI]
  have hxi' : x⁻¹ ∈ Subgroup.normalizer (W : Set G) := Subgroup.inv_mem _ hx
  constructor
  · rintro ⟨l, hl, hlL, rfl⟩
    have hxl := Subgroup.mul_mem _ hx hl
    refine ⟨x * l * x⁻¹, Subgroup.mul_mem _ hxl hxi',
      (Subgroup.mem_normalizer_iff.mp hxL l).mp hlL, ?_⟩
    rw [hat_mul Φ hxl hxi', hat_mul Φ hx hl, hat_inv Φ hx]
  · rintro ⟨l, hl, hlL, hl'⟩
    have hxl := Subgroup.mul_mem _ hxi' hl
    have hxii : x⁻¹⁻¹ ∈ Subgroup.normalizer (W : Set G) := Subgroup.inv_mem _ hxi'
    refine ⟨x⁻¹ * l * x⁻¹⁻¹, Subgroup.mul_mem _ hxl hxii,
      (Subgroup.mem_normalizer_iff.mp hxi l).mp hlL, ?_⟩
    rw [hat_mul Φ hxl hxii, hat_mul Φ hxi' hl, hat_inv Φ hxi' hxii, hat_inv Φ hx hxi', hl']
    group

theorem map_autI_le_normD (Φ : IntMod W hW ≃* W6 K) {L E : Subgroup G}
    (hL : (autI hW L).map (congrHom Φ) = diagSL K)
    (hE : ∀ x ∈ E, x ∈ Subgroup.normalizer (W : Set G) → x ∈ Subgroup.normalizer (L : Set G)) :
    (autI hW E).map (congrHom Φ) ≤ normD K := by
  intro y hy
  obtain ⟨x, hx, hxE, rfl⟩ := (mem_map_autI Φ).mp hy
  exact hat_mem_normD Φ hL hx (hE x hxE hx)

theorem card_fix_hat (Φ : IntMod W hW ≃* W6 K) {x : G}
    (hx : x ∈ Subgroup.normalizer (W : Set G)) :
    Nat.card (FixW (hat Φ x hx)) = Nat.card ↥(W ⊓ Subgroup.centralizer ({x} : Set G)) := by
  have hiff : ∀ v : W6 K, hat Φ x hx v = v ↔ psi Φ v ∈ Subgroup.centralizer ({x} : Set G) := by
    intro v
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have := psi_hat Φ hx v
      rw [h] at this
      calc psi Φ v * x = x * psi Φ v * x⁻¹ * x := by rw [← this]
        _ = x * psi Φ v := by group
    · intro h
      apply psi_injective Φ
      rw [psi_hat, ← h]
      group
  refine Nat.card_congr
    { toFun := fun v => ⟨psi Φ (Multiplicative.ofAdd v.1),
        psi_mem Φ _, (hiff _).mp (congrArg Multiplicative.ofAdd v.2)⟩
      invFun := fun w => ⟨Multiplicative.toAdd (Classical.choose (exists_psi_eq Φ w.2.1)), by
        have h1 := Classical.choose_spec (exists_psi_eq Φ w.2.1)
        have hwC : (w : G) ∈ Subgroup.centralizer ({x} : Set G) := (Subgroup.mem_inf.mp w.2).2
        have h2 : hat Φ x hx (Classical.choose (exists_psi_eq Φ w.2.1)) =
            Classical.choose (exists_psi_eq Φ w.2.1) := (hiff _).mpr (by rw [h1]; exact hwC)
        exact congrArg Multiplicative.toAdd h2⟩
      left_inv := fun v => Subtype.ext (by
        have h1 := Classical.choose_spec (exists_psi_eq Φ (psi_mem Φ (Multiplicative.ofAdd v.1)))
        exact congrArg Multiplicative.toAdd (psi_injective Φ h1))
      right_inv := fun w => Subtype.ext (Classical.choose_spec (exists_psi_eq Φ w.2.1)) }

theorem card_W [Finite K] (Φ : IntMod W hW ≃* W6 K) : Nat.card ↥W = Nat.card K ^ 6 := by
  rw [← card_W6]
  exact Nat.card_congr Φ.toEquiv

theorem map_comap_psi (Φ : IntMod W hW ≃* W6 K) {U : Subgroup G} (hU : U ≤ W) :
    (U.comap (psi Φ)).map (psi Φ) = U := by
  refine le_antisymm (Subgroup.map_comap_le _ _) fun u hu => ?_
  obtain ⟨v, rfl⟩ := exists_psi_eq Φ (hU hu)
  exact ⟨v, hu, rfl⟩

theorem card_comap_psi (Φ : IntMod W hW ≃* W6 K) {U : Subgroup G} (hU : U ≤ W) :
    Nat.card ↥(U.comap (psi Φ)) = Nat.card ↥U := by
  conv_rhs => rw [← map_comap_psi Φ hU]
  exact (Subgroup.card_map_of_injective (psi_injective Φ)).symm

theorem comap_psi_inf_centralizer (Φ : IntMod W hW ≃* W6 K) {E : Subgroup G}
    (hE : E ≤ Subgroup.normalizer (W : Set G)) :
    (W ⊓ Subgroup.centralizer (E : Set G)).comap (psi Φ) =
      fixV ((autI hW E).map (congrHom Φ)) := by
  ext v
  rw [Subgroup.mem_comap, Subgroup.mem_inf, mem_fixV, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨-, h⟩ y hy
    obtain ⟨x, hx, hxE, rfl⟩ := (mem_map_autI Φ).mp hy
    apply psi_injective Φ
    rw [psi_hat, h x hxE]
    group
  · intro h
    refine ⟨psi_mem Φ v, fun x hxE => ?_⟩
    have h1 := h _ (hat_mem_map_autI Φ (hE hxE) hxE)
    have h2 := psi_hat Φ (hE hxE) v
    rw [h1] at h2
    calc x * psi Φ v = x * psi Φ v * x⁻¹ * x := by group
      _ = psi Φ v * x := by rw [← h2]

theorem commutator_eq_map (Φ : IntMod W hW ≃* W6 K) {S E : Subgroup G} (hS : S ≤ W)
    (hE : E ≤ Subgroup.normalizer (W : Set G)) :
    ⁅S, E⁆ = (commSub (S.comap (psi Φ)) ((autI hW E).map (congrHom Φ))).map (psi Φ) := by
  have hc := hW.1
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro s hs e he
    obtain ⟨v, rfl⟩ := exists_psi_eq Φ (hS hs)
    have hv : v⁻¹ ∈ S.comap (psi Φ) := Subgroup.inv_mem _ hs
    refine ⟨hat Φ e (hE he) v⁻¹ * v⁻¹⁻¹, Subgroup.subset_closure
      ⟨_, hat_mem_map_autI Φ (hE he) he, v⁻¹, hv, rfl⟩, ?_⟩
    rw [inv_inv, map_mul, psi_hat, map_inv, commutatorElement_def]
    calc e * (psi Φ v)⁻¹ * e⁻¹ * psi Φ v = (e * psi Φ v * e⁻¹)⁻¹ * psi Φ v := by group
      _ = psi Φ v * (e * psi Φ v * e⁻¹)⁻¹ := setLike_mul_comm (W.inv_mem
          (by rw [← psi_hat Φ (hE he)]; exact psi_mem Φ _)) (psi_mem Φ v)
      _ = psi Φ v * e * (psi Φ v)⁻¹ * e⁻¹ := by group
  · rw [Subgroup.map_le_iff_le_comap, commSub, Subgroup.closure_le]
    rintro _ ⟨y, hy, w, hw, rfl⟩
    obtain ⟨x, hx, hxE, rfl⟩ := (mem_map_autI Φ).mp hy
    rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, psi_hat, map_inv]
    have : x * psi Φ w * x⁻¹ * (psi Φ w)⁻¹ = ⁅x, psi Φ w⁆ := by rw [commutatorElement_def]
    rw [this, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hxE hw

theorem isPGroup_of_le (hW : IsElemAbelian 2 W) {U : Subgroup G} (hU : U ≤ W) :
    IsPGroup 2 ↥U := fun u =>
  ⟨1, Subtype.ext (by rw [pow_one]; exact hW.2 u (hU u.2))⟩

theorem two_pow_mQuot_mul_card [Finite G] [Finite K] (Φ : IntMod W hW ≃* W6 K) {n : ℕ}
    (hK : Nat.card K = 2 ^ n) {U : Subgroup G} (hU : U ≤ W) :
    2 ^ E3.mQuot W U * Nat.card ↥U = 2 ^ (6 * n) := by
  rw [← E3.card_eq_two_pow_mul (isPGroup_of_le hW le_rfl) hU, card_W Φ, hK, ← pow_mul,
    mul_comm]

theorem card_autI_eq_two_pow [Finite G] {E : Subgroup G} (hE : IsElemAbelian 2 E)
    (hEN : E ≤ Subgroup.normalizer (W : Set G)) :
    Nat.card ↥(autI hW E) = 2 ^ E3.mQuot E (E ⊓ Subgroup.centralizer (W : Set G)) := by
  rw [card_autI_eq hW hEN]
  exact E3.relIndex_eq_two_pow (fun e => ⟨1, Subtype.ext (by rw [pow_one]; exact hE.2 e e.2)⟩) _

theorem card_map_autI (Φ : IntMod W hW ≃* W6 K) (E : Subgroup G) :
    Nat.card ↥((autI hW E).map (congrHom Φ)) = Nat.card ↥(autI hW E) :=
  card_map_congrHom Φ _

end CFSG.Quasithin.Vol2.Ch11.SecB.K8
