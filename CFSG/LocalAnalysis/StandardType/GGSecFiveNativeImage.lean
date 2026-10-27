module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoord
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordFix
import CFSG.LocalAnalysis.StandardType.GGSecFiveNativeImageLin
import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxBasic
import CFSG.LocalAnalysis.StandardType.GGSecFiveBarBridge

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G] {p : ℕ}

private noncomputable def invMulAutHom {M : Type*} [Group M]
    (hcomm : ∀ a b : M, a * b = b * a) (ψ : MulAut M) : M →* M where
  toFun b := b⁻¹ * ψ b
  map_one' := by simp
  map_mul' a b := by
    show (a * b)⁻¹ * ψ (a * b) = a⁻¹ * ψ a * (b⁻¹ * ψ b)
    calc (a * b)⁻¹ * ψ (a * b)
        = (b⁻¹ * a⁻¹) * (ψ a * ψ b) := by rw [map_mul, mul_inv_rev]
      _ = (a⁻¹ * b⁻¹) * (ψ a * ψ b) := by rw [hcomm b⁻¹ a⁻¹]
      _ = a⁻¹ * (b⁻¹ * (ψ a * ψ b)) := by rw [mul_assoc]
      _ = a⁻¹ * ((b⁻¹ * ψ a) * ψ b) := by rw [← mul_assoc b⁻¹ (ψ a) (ψ b)]
      _ = a⁻¹ * ((ψ a * b⁻¹) * ψ b) := by rw [hcomm b⁻¹ (ψ a)]
      _ = a⁻¹ * (ψ a * (b⁻¹ * ψ b)) := by rw [mul_assoc (ψ a) (b⁻¹) (ψ b)]
      _ = a⁻¹ * ψ a * (b⁻¹ * ψ b) := by rw [← mul_assoc]

private theorem invMulAutHom_apply {M : Type*} [Group M]
    (hcomm : ∀ a b : M, a * b = b * a) (ψ : MulAut M) (b : M) :
    invMulAutHom hcomm ψ b = b⁻¹ * ψ b := rfl

private theorem invMulAutHom_range_ne_bot {M : Type*} [Group M]
    (hcomm : ∀ a b : M, a * b = b * a) {ψ : MulAut M} (hψ1 : ψ ≠ 1) :
    (invMulAutHom hcomm ψ).range ≠ ⊥ := by
  intro hbot
  apply hψ1
  refine MulEquiv.ext fun b => ?_
  have hb' : invMulAutHom hcomm ψ b = 1 := by
    have hmem : invMulAutHom hcomm ψ b ∈ (invMulAutHom hcomm ψ).range :=
      MonoidHom.mem_range.mpr ⟨b, rfl⟩
    simpa [hbot] using hmem
  rw [invMulAutHom_apply, inv_mul_eq_one] at hb'
  exact hb'.symm

private theorem invMulAutHom_ker_card {M : Type*} [Group M]
    (hcomm : ∀ a b : M, a * b = b * a) (ψ : MulAut M) :
    Nat.card (invMulAutHom hcomm ψ).ker = Nat.card {b : M // ψ b = b} := by
  apply Nat.card_congr
  refine Equiv.subtypeEquivRight ?_
  intro a
  rw [MonoidHom.mem_ker]
  show invMulAutHom hcomm ψ a = 1 ↔ ψ a = a
  rw [invMulAutHom_apply, inv_mul_eq_one]
  exact eq_comm

private theorem fixes_zpowers_of_fixes_generator {M : Type*} [Group M] {x : M} {ψ : MulAut M}
    (hψx : ψ x = x) : ∀ y ∈ Subgroup.zpowers x, ψ y = y := by
  intro y hy
  rcases Subgroup.mem_zpowers_iff.mp hy with ⟨k, hk⟩
  rw [← hk, map_zpow, hψx]

omit [Finite G] in
theorem ggIsTransvection_of_forall_mul_inv_mem_zpowers (hp : p.Prime) {Bs : Subgroup G}
    (hcomm : ∀ a b : ↥Bs, a * b = b * a) {x : G} (hx : x ∈ Bs) (hxp : orderOf x = p)
    {ψ : MulAut ↥Bs} (hψ1 : ψ ≠ 1) (hψx : ψ ⟨x, hx⟩ = ⟨x, hx⟩)
    (h : ∀ b : ↥Bs, ψ b * b⁻¹ ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs)) : GGIsTransvection p ψ := by
  let f := invMulAutHom hcomm ψ
  have hf_mem : ∀ b : ↥Bs, b⁻¹ * ψ b ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs) := by
    intro b
    rw [← hcomm (ψ b) b⁻¹]
    exact h b
  have hrange_le : f.range ≤ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs) := by
    rintro _ ⟨b, rfl⟩
    change b⁻¹ * ψ b ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs)
    exact hf_mem b
  have hcard_zpowers : Nat.card (Subgroup.zpowers (⟨x, hx⟩ : ↥Bs)) = p := by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hxp]
  have hrange_ne_bot : f.range ≠ ⊥ := by
    simpa [f] using invMulAutHom_range_ne_bot hcomm hψ1
  have hrange_card : Nat.card f.range = p := by
    have hdiv : Nat.card f.range ∣ p := by
      rw [← hcard_zpowers]
      exact Subgroup.card_dvd_of_le hrange_le
    have hne : Nat.card f.range ≠ 1 := fun h1 =>
      hrange_ne_bot ((Subgroup.card_eq_one).mp h1)
    rcases (Nat.dvd_prime hp).mp hdiv with h1 | hp_eq
    · exact absurd h1 hne
    · exact hp_eq
  have hker_card : Nat.card f.ker = Nat.card {b : ↥Bs // ψ b = b} := by
    simpa [f] using invMulAutHom_ker_card hcomm ψ
  have hmain := Subgroup.card_ker_mul_card_range f
  rw [hker_card, hrange_card] at hmain
  change Nat.card {b : ↥Bs // ψ b = b} * p = Nat.card ↥Bs ∧
    ∀ b : ↥Bs, ψ (b⁻¹ * ψ b) = b⁻¹ * ψ b
  refine ⟨hmain, ?_⟩
  have hfix := fixes_zpowers_of_fixes_generator hψx
  intro b
  exact hfix (b⁻¹ * ψ b) (hf_mem b)

omit [Finite G] in
theorem eq_one_of_forall_mul_inv_mem_zpowers (hp : p.Prime) {Bs : Subgroup G}
    (hcomm : ∀ a b : ↥Bs, a * b = b * a) (hNT : GGNoTransvection p Bs) {x : G} (hx : x ∈ Bs)
    (hxp : orderOf x = p) {ψ : MulAut ↥Bs} (hψ : ψ ∈ ggInduced ⊤ Bs)
    (hψx : ψ ⟨x, hx⟩ = ⟨x, hx⟩)
    (h : ∀ b : ↥Bs, ψ b * b⁻¹ ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs)) : ψ = 1 := by
  by_contra hψ1
  exact hNT ψ hψ (ggIsTransvection_of_forall_mul_inv_mem_zpowers hp hcomm hx hxp hψ1 hψx h)

private theorem signedPerm_coord {p n : ℕ} [Fact p.Prime]
    {s : (Fin n → ZMod p) ≃ₗ[ZMod p] (Fin n → ZMod p)}
    (σ : Equiv.Perm (Fin n)) (ε : Fin n → ZMod p)
    (hs : ∀ i, s (Pi.basisFun (ZMod p) (Fin n) i) =
      ε i • Pi.basisFun (ZMod p) (Fin n) (σ i))
    (v : Fin n → ZMod p) (j : Fin n) : s v (σ j) = ε j * v j := by
  have hv : v = ∑ i, v i • Pi.basisFun (ZMod p) (Fin n) i := by
    simpa [Pi.basisFun_repr] using ((Pi.basisFun (ZMod p) (Fin n)).sum_repr v).symm
  conv_lhs => rw [hv]
  rw [map_sum, Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply]
  rw [Finset.sum_eq_single j]
  · rw [hs j, Pi.smul_apply, Pi.basisFun_apply, Pi.single_eq_same]
    ring_nf
  · intro i _ hi
    have hne : σ i ≠ σ j := fun h => hi (σ.injective h)
    rw [hs i, Pi.smul_apply, Pi.basisFun_apply, Pi.single_eq_of_ne (Ne.symm hne)]
    simp
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

private theorem bCoordIota_pow {p n : ℕ} [Fact p.Prime] {G : Type} [Group G] {Bs : Subgroup G}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (g : ↥Bs) (c : ℕ) :
    bCoordIota eta (Additive.ofMul (g ^ c)) =
      (c : ZMod p) • bCoordIota eta (Additive.ofMul g) := by
  rw [ofMul_pow, map_nsmul, Nat.cast_smul_eq_nsmul]

private theorem bCoordIota_mem_span_of_mem_zpowers {p n : ℕ} [Fact p.Prime] {G : Type} [Group G]
    {Bs : Subgroup G} {x : G} (hx : x ∈ Bs)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {y : ↥Bs}
    (hy : y ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs)) :
    bCoordIota eta (Additive.ofMul y) ∈
      Submodule.span (ZMod p)
        ({bCoordIota eta (Additive.ofMul (⟨x, hx⟩ : ↥Bs))} : Set (Fin n → ZMod p)) := by
  rcases Subgroup.mem_zpowers_iff.mp hy with ⟨k, hk⟩
  rw [← hk, ofMul_zpow, map_zsmul]
  rw [← Int.cast_smul_eq_zsmul (R := ZMod p)]
  exact Submodule.smul_mem
    (Submodule.span (ZMod p)
      ({bCoordIota eta (Additive.ofMul (⟨x, hx⟩ : ↥Bs))} : Set (Fin n → ZMod p))) (k : ZMod p)
    (Submodule.mem_span_singleton_self _)

private theorem lin_sub_smul_mem_span {p n : ℕ} [Fact p.Prime] {G : Type} [Group G]
    {Bs : Subgroup G} {x : G} (hx : x ∈ Bs)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {φ a : MulAut ↥Bs} {c : ℕ}
    (hca : ∀ b : ↥Bs, φ b * (a b ^ c)⁻¹ ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs)) :
    ∀ v : Fin n → ZMod p,
      ggLin (p := p) (bCoordIota eta) φ v -
          (c : ZMod p) • ggLin (p := p) (bCoordIota eta) a v ∈
        Submodule.span (ZMod p)
          ({bCoordIota eta (Additive.ofMul (⟨x, hx⟩ : ↥Bs))} : Set (Fin n → ZMod p)) := by
  intro v
  let b : ↥Bs := Additive.toMul ((bCoordIota eta).symm v)
  have hb : bCoordIota eta (Additive.ofMul b) = v := by
    dsimp [b]
    simp
  rw [← hb]
  rw [ggLin_apply_ofMul (p := p) (bCoordIota eta) φ b,
    ggLin_apply_ofMul (p := p) (bCoordIota eta) a b,
    ← bCoordIota_pow eta (a b) c, ← map_sub]
  have hsub : Additive.ofMul (φ b) - Additive.ofMul ((a b) ^ c) =
      Additive.ofMul (φ b * ((a b) ^ c)⁻¹) := by
    rw [ofMul_mul, ofMul_inv, sub_eq_add_neg]
  rw [hsub]
  exact bCoordIota_mem_span_of_mem_zpowers hx eta (hca b)

private theorem mem_zpowers_of_supported {p n : ℕ} (hp : p.Prime)
    {u w : Fin n → Multiplicative (ZMod p)} (i0 : Fin n)
    (hu : ∀ i, i ≠ i0 → u i = 1) (hw : ∀ i, i ≠ i0 → w i = 1)
    (hui : u i0 ≠ 1) : w ∈ Subgroup.zpowers u := by
  have : Fact p.Prime := ⟨hp⟩
  have hA : (u i0).toAdd ≠ 0 := fun h => hui (toAdd_eq_zero.mp h)
  obtain ⟨c, hc⟩ : ∃ c : ℕ, (u i0) ^ c = w i0 := by
    refine ⟨(((w i0).toAdd / (u i0).toAdd).val), ?_⟩
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, nsmul_eq_mul, ZMod.natCast_zmod_val]
    exact div_mul_cancel₀ (w i0).toAdd hA
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨(c : ℤ), ?_⟩
  rw [zpow_natCast]
  funext i
  rw [Pi.pow_apply]
  by_cases hi : i = i0
  · subst hi; exact hc
  · rw [hu i hi, hw i hi, one_pow]

private theorem eta_ne_one_of_ne_one {p n : ℕ} {G : Type} [Group G] {Bs : Subgroup G}
    {x : G} (hx : x ∈ Bs) {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    (hx1 : x ≠ 1) : eta ⟨x, hx⟩ ≠ 1 := by
  intro h
  apply hx1
  have h' : (⟨x, hx⟩ : ↥Bs) = 1 := eta.injective (by simpa using h)
  simpa using congrArg Subtype.val h'

private theorem pow_eq_self_of_natCast_eq_one {M : Type*} [Group M] {p c : ℕ} (hp : p.Prime)
    {g : M} (hg : g ^ p = 1) (hc : (c : ZMod p) = 1) : g ^ c = g := by
  rw [pow_eq_pow_mod c hg]
  have hc1 : (c : ZMod p) = ((1 : ℕ) : ZMod p) := by simpa using hc
  have hmod : c % p = 1 := by
    have := (ZMod.natCast_eq_natCast_iff' c 1 p).mp hc1
    simpa [Nat.mod_eq_of_lt hp.one_lt] using this
  rw [hmod, pow_one]

private theorem pow_eq_inv_of_natCast_eq_neg_one {M : Type*} [Group M] {p c : ℕ} (hp : p.Prime)
    {g : M} (hg : g ^ p = 1) (hc : (c : ZMod p) = -1) : g ^ c = g⁻¹ := by
  rw [pow_eq_pow_mod c hg]
  have hmod : c % p = p - 1 := by
    have hval : ((-1 : ZMod p)).val = p - 1 := by
      cases p with
      | zero => exact (Nat.not_prime_zero hp).elim
      | succ n =>
        have h : (-1 : ZMod (n + 1)).val = n := ZMod.val_neg_one n
        simp
    rw [← ZMod.val_natCast, hc]
    exact hval
  rw [hmod]
  have h1 : g ^ (p - 1) * g = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hp.one_lt.le, hg]
  exact eq_inv_of_mul_eq_one_left h1

variable {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}

theorem dCoordinateBlock_le_bCoordinateBlock {n : ℕ} (i0 : Fin n) :
    dCoordinateBlock n p i0 ≤ bCoordinateBlock n p i0 := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro r (⟨a, b, hab, ha, hb, rfl⟩ | ⟨a, b, hab, ha, hb, rfl⟩)
  · exact Subgroup.subset_closure (Or.inr ⟨a, b, hab, ha, hb, rfl⟩)
  · have hsign : SpCoord.sgnAut a ∈ bCoordinateBlock n p i0 :=
      Subgroup.subset_closure (Or.inl ⟨a, ha, rfl⟩)
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hsign
      (Subgroup.subset_closure (Or.inr ⟨a, b, hab, ha, hb, rfl⟩))) (Subgroup.inv_mem _ hsign)

omit [Finite G] in
theorem ggIsReflection_congr_sgnAut [Fact p.Prime] (hp2 : p ≠ 2) {n : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (a : Fin n) :
    GGIsReflection p ((MulAut.congr eta).symm (SpCoord.sgnAut a)) := by
  set φ : MulAut ↥Bs := (MulAut.congr eta).symm (SpCoord.sgnAut a) with hφ
  have hcongr : MulAut.congr eta φ = SpCoord.sgnAut a := by
    rw [hφ]
    exact MulEquiv.apply_symm_apply (MulAut.congr eta) (SpCoord.sgnAut a)
  refine ⟨?_, ?_⟩
  · rw [hφ, ← map_pow, SpCoord.sgnAut_sq, map_one]
  · have h1 : Nat.card {b : ↥Bs // φ b = b} =
        Nat.card {f : Fin n → Multiplicative (ZMod p) // SpCoord.sgnAut a f = f} := by
      refine Nat.card_congr (Equiv.subtypeEquiv eta.toEquiv fun b => ?_)
      constructor
      · intro h
        have h2 : MulAut.congr eta φ (eta b) = eta b := by
          rw [MulAut.congr_apply]
          simpa using congrArg eta h
        rwa [hcongr] at h2
      · intro h
        apply eta.injective
        have h2 : MulAut.congr eta φ (eta b) = eta b := by rwa [hcongr]
        simpa [MulAut.congr_apply] using h2
    rw [h1, Nat.card_congr eta.toEquiv]
    exact SpCoord.card_fix_sgnAut (Fact.out : p.Prime) hp2 a

private theorem fix_eta_x_of_map_eq (hx : x ∈ Bs)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n : ℕ}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {H : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))}
    (hH : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = H) :
    ∀ u ∈ H, u (eta ⟨x, hx⟩) = eta ⟨x, hx⟩ := by
  intro u hu
  rw [← hH] at hu
  obtain ⟨a, ha, hEq⟩ := Subgroup.mem_map.mp hu
  have h1 : ((MulAut.congr eta).toMonoidHom a) (eta ⟨x, hx⟩) = eta ⟨x, hx⟩ := by
    change (eta.symm.trans (a.trans eta)) (eta ⟨x, hx⟩) = eta ⟨x, hx⟩
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      ggRM_AL_fixes_x (ggSecFiveRouteCfg'_of_routeCfg hR) hx a ha]
  rwa [hEq] at h1

private theorem eq_of_mul_inv_mem_zpowers_of_mem_ggInduced
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hx : x ∈ Bs)
    {φ a : MulAut ↥Bs} (hφ : φ ∈ ggInduced ⊤ Bs) (hfix : φ ⟨x, hx⟩ = ⟨x, hx⟩)
    (ha : a ∈ ggInduced ⊤ Bs) (hfix_a_x : a ⟨x, hx⟩ = ⟨x, hx⟩)
    (hca : ∀ b : ↥Bs, φ b * (a b)⁻¹ ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs)) : φ = a := by
  obtain ⟨hp, hBs, -, -, -⟩ := hR.1.1.tableB_facts
  have : Fact p.Prime := ⟨hp⟩
  have hx1 : x ≠ 1 := hR.1.1.1.2.2.2.2.2.2.1.2.2.1
  have hxp : orderOf x = p := orderOf_eq_prime (hBs.2 x hx) hx1
  have hcomm : ∀ a b : ↥Bs, a * b = b * a := fun a b => hBs.1.is_comm.comm a b
  have hNT : GGNoTransvection p Bs := hR.1.2.2.2.1
  have hinv_apply : a⁻¹ ⟨x, hx⟩ = ⟨x, hx⟩ := by
    rw [← hfix_a_x, MulAut.inv_apply_self, hfix_a_x]
  let ψ : MulAut ↥Bs := φ * a⁻¹
  have hψ_ind : ψ ∈ ggInduced ⊤ Bs :=
    mul_mem_ggInduced hφ (inv_mem_ggInduced ha)
  have hψx : ψ ⟨x, hx⟩ = ⟨x, hx⟩ := by
    change (φ * a⁻¹) ⟨x, hx⟩ = ⟨x, hx⟩
    rw [MulAut.mul_apply, hinv_apply, hfix]
  have hψ_mem : ∀ b : ↥Bs, ψ b * b⁻¹ ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs) := by
    intro b
    have hb := hca (a⁻¹ b)
    simpa [ψ, MulAut.mul_apply, MulAut.apply_inv_self] using hb
  have hψ1 := eq_one_of_forall_mul_inv_mem_zpowers hp hcomm hNT hx hxp hψ_ind hψx hψ_mem
  exact eq_of_mul_inv_eq_one hψ1

omit [Finite G] in
private theorem bCoord_eq_smul_basis_of_axis {n : ℕ} [Fact p.Prime]
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {i0 : Fin n} (hx : x ∈ Bs)
    (hxcoord : ∀ k, k ≠ i0 → eta ⟨x, hx⟩ k = 1) (heta_ne_one : eta ⟨x, hx⟩ ≠ 1) :
    ∃ t : ZMod p, t ≠ 0 ∧ eta ⟨x, hx⟩ i0 ≠ 1 ∧
      bCoordIota eta (Additive.ofMul (⟨x, hx⟩ : ↥Bs)) =
        t • Pi.basisFun (ZMod p) (Fin n) i0 := by
  let t : ZMod p := Multiplicative.toAdd (eta ⟨x, hx⟩ i0)
  have ht : t ≠ 0 := by
    intro ht0
    apply heta_ne_one
    funext k
    by_cases hk : k = i0
    · subst hk
      exact toAdd_eq_zero.mp (by simpa [t] using ht0)
    · simp [hxcoord k hk]
  have hui : eta ⟨x, hx⟩ i0 ≠ 1 := by
    intro h
    apply heta_ne_one
    funext k
    by_cases hk : k = i0
    · subst hk; exact h
    · exact hxcoord k hk
  refine ⟨t, ht, hui, ?_⟩
  funext k
  simp only [bCoordIota_apply_ofMul]
  by_cases hk : k = i0
  · subst hk
    simp [t, Pi.basisFun_apply, Pi.smul_apply]
  · rw [hxcoord k hk]
    simp [Pi.basisFun_apply, Pi.smul_apply, Pi.single_eq_of_ne hk]

omit [Finite G] in
private theorem signed_form_of_mem_bCoordinateBlock [Fact p.Prime]
    {n : ℕ} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {i0 : Fin n}
    (hx : x ∈ Bs) {a : MulAut ↥Bs}
    (hcongr : MulAut.congr eta a ∈ bCoordinateBlock n p i0)
    (hfix_a_x : a ⟨x, hx⟩ = ⟨x, hx⟩) {t : ZMod p} (ht : t ≠ 0)
    (hw : bCoordIota eta (Additive.ofMul (⟨x, hx⟩ : ↥Bs)) =
      t • Pi.basisFun (ZMod p) (Fin n) i0) :
    ∃ (σ : Equiv.Perm (Fin n)) (ε : Fin n → ZMod p),
      (∀ j, ε j = 1 ∨ ε j = -1) ∧ σ i0 = i0 ∧
        ∀ v j, ggLin (p := p) (bCoordIota eta) a v (σ j) = ε j * v j := by
  obtain ⟨σ, ε, hε, hσ⟩ := (congr_mem_bSignedFull_iff eta a).mp
    (bCoordinateBlock_le_bSignedFull i0 hcongr)
  have hσ_coord : ∀ v j, ggLin (p := p) (bCoordIota eta) a v (σ j) = ε j * v j :=
    signedPerm_coord σ ε hσ
  have hs_fix_w : ggLin (p := p) (bCoordIota eta) a
      (bCoordIota eta (Additive.ofMul (⟨x, hx⟩ : ↥Bs))) =
      bCoordIota eta (Additive.ofMul (⟨x, hx⟩ : ↥Bs)) :=
    (ggLin_fix_iff (p := p) (bCoordIota eta) a ⟨x, hx⟩).mp hfix_a_x
  have hw_e : ggLin (p := p) (bCoordIota eta) a (t • Pi.basisFun (ZMod p) (Fin n) i0) =
      t • Pi.basisFun (ZMod p) (Fin n) i0 := by
    rw [← hw]
    exact hs_fix_w
  have hs_e : ggLin (p := p) (bCoordIota eta) a (Pi.basisFun (ZMod p) (Fin n) i0) =
      Pi.basisFun (ZMod p) (Fin n) i0 := by
    have h := hw_e
    rw [map_smul] at h
    exact smul_right_injective (Fin n → ZMod p) ht h
  have hσ_i0 : σ i0 = i0 := by
    have hσ_e : ε i0 • Pi.basisFun (ZMod p) (Fin n) (σ i0) =
        Pi.basisFun (ZMod p) (Fin n) i0 := by
      rw [← hσ i0, hs_e]
    by_contra hne
    have h := congrFun hσ_e i0
    simp [Pi.basisFun_apply, Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hne)] at h
  exact ⟨σ, ε, hε, hσ_i0, hσ_coord⟩

omit [Finite G] in
private theorem mul_inv_mem_zpowers_of_congr_eq_negOff {n : ℕ} (hp : p.Prime)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {i0 : Fin n}
    (hx : x ∈ Bs) (hxcoord : ∀ k, k ≠ i0 → eta ⟨x, hx⟩ k = 1)
    (hui : eta ⟨x, hx⟩ i0 ≠ 1) {ν : MulAut ↥Bs}
    (hν_eq : MulAut.congr eta ν = negOff i0) :
    ∀ w : ↥Bs, (ν w) * w ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs) := by
  intro w
  have hsupp : ∀ k, k ≠ i0 → eta (ν w * w) k = 1 := by
    intro k hk
    rw [map_mul, Pi.mul_apply]
    have hν_apply : eta (ν w) k = (eta w k)⁻¹ := by
      have h1 : MulAut.congr eta ν (eta w) = eta (ν w) := by
        simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      rw [← h1, hν_eq, negOff_apply, if_neg hk]
    rw [hν_apply]
    simp
  have hmem : eta (ν w * w) ∈ Subgroup.zpowers (eta ⟨x, hx⟩) :=
    mem_zpowers_of_supported hp i0 hxcoord hsupp hui
  rw [Subgroup.mem_zpowers_iff] at hmem ⊢
  obtain ⟨k, hk⟩ := hmem
  refine ⟨k, ?_⟩
  apply eta.injective
  rw [map_zpow, hk]

omit [Finite G] in
private theorem mul_inv_mem_zpowers_of_neg_one {φ a ν : MulAut ↥Bs} {c : ℕ}
    (hx : x ∈ Bs) (hpow : ∀ g : ↥Bs, g ^ c = g⁻¹)
    (hca : ∀ b : ↥Bs, φ b * (a b ^ c)⁻¹ ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs))
    (hν : ∀ w : ↥Bs, ν w * w ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs)) :
    ∀ b : ↥Bs, φ b * ((ν * a) b)⁻¹ ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs) := by
  intro b
  have hAB : φ b * a b ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs) := by
    simpa [hpow (a b)] using hca b
  have hCB : ν (a b) * a b ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs) := hν (a b)
  have h1 : φ b * ((ν * a) b)⁻¹ = (φ b * a b) * (ν (a b) * a b)⁻¹ := by
    rw [MulAut.mul_apply]
    group
  rw [h1]
  exact Subgroup.mul_mem _ hAB (Subgroup.inv_mem _ hCB)

private theorem eq_negOff_mul_of_neg_one [Fact p.Prime]
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n : ℕ}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {i0 : Fin n} (hx : x ∈ Bs)
    (hxi0 : ∀ k, k ≠ i0 → eta ⟨x, hx⟩ k = 1) (hui : eta ⟨x, hx⟩ i0 ≠ 1)
    (hν : (MulAut.congr eta).symm (negOff i0) ∈ ggInduced ⊤ Bs)
    {φ a : MulAut ↥Bs} (hφ : φ ∈ ggInduced ⊤ Bs) (hfix : φ ⟨x, hx⟩ = ⟨x, hx⟩)
    (ha : a ∈ ggInduced ⊤ Bs) (hfix_a_x : a ⟨x, hx⟩ = ⟨x, hx⟩)
    {c : ℕ} (hcneg : (c : ZMod p) = -1)
    (hca : ∀ b : ↥Bs, φ b * (a b ^ c)⁻¹ ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs)) :
    φ = (MulAut.congr eta).symm (negOff i0) * a := by
  obtain ⟨hp, hBs, -, -, -⟩ := hR.1.1.tableB_facts
  let ν : MulAut ↥Bs := (MulAut.congr eta).symm (negOff i0)
  have hν_eq : MulAut.congr eta ν = negOff i0 :=
    MulEquiv.apply_symm_apply (MulAut.congr eta) (negOff i0)
  have hν_line := mul_inv_mem_zpowers_of_congr_eq_negOff hp hx hxi0 hui hν_eq
  have hpow : ∀ g : ↥Bs, g ^ c = g⁻¹ := fun g =>
    pow_eq_inv_of_natCast_eq_neg_one hp (Subtype.ext (hBs.2 g g.2)) hcneg
  have hca'' := mul_inv_mem_zpowers_of_neg_one hx hpow hca hν_line
  have hν_fix_eta : MulAut.congr eta ν (eta ⟨x, hx⟩) = eta ⟨x, hx⟩ := by
    rw [hν_eq]
    funext k
    by_cases hk : k = i0
    · subst hk
      simp [negOff_apply]
    · rw [negOff_apply, if_neg hk, hxi0 k hk]
      simp
  have hν_fix_x : ν ⟨x, hx⟩ = ⟨x, hx⟩ := by
    apply eta.injective
    simpa [MulAut.congr_apply] using hν_fix_eta
  have hνa_fix_x : (ν * a) ⟨x, hx⟩ = ⟨x, hx⟩ := by
    rw [MulAut.mul_apply, hfix_a_x, hν_fix_x]
  exact eq_of_mul_inv_mem_zpowers_of_mem_ggInduced hR hx hφ hfix (mul_mem_ggInduced hν ha)
    hνa_fix_x hca''

private theorem mem_of_neg_one [Fact p.Prime]
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n : ℕ}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {i0 : Fin n} (hx : x ∈ Bs)
    (hxi0 : ∀ k, k ≠ i0 → eta ⟨x, hx⟩ k = 1)
    (hui : eta ⟨x, hx⟩ i0 ≠ 1) {H : Subgroup (MulAut ↥Bs)}
    (hH : ∀ h ∈ H, h ∈ ggInduced ⊤ Bs)
    (hneg : (MulAut.congr eta).symm (negOff i0) ∈ H)
    {φ a : MulAut ↥Bs} (hφ : φ ∈ ggInduced ⊤ Bs)
    (hfix : φ ⟨x, hx⟩ = ⟨x, hx⟩) (hfix_a_x : a ⟨x, hx⟩ = ⟨x, hx⟩) (ha : a ∈ H)
    {c : ℕ} (hcneg : (c : ZMod p) = -1)
    (hca : ∀ b : ↥Bs, φ b * (a b ^ c)⁻¹ ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs)) :
    φ ∈ H := by
  rw [eq_negOff_mul_of_neg_one hR hx hxi0 hui (hH _ hneg) hφ hfix (hH a ha) hfix_a_x hcneg hca]
  exact Subgroup.mul_mem _ hneg ha

omit [Finite G] in
private theorem aCoord_eq_smul_one {n : ℕ} [Fact p.Prime]
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} (i0 : Fin n)
    (hx : x ∈ Bs) (hxconst : ∀ a b, eta ⟨x, hx⟩ a = eta ⟨x, hx⟩ b)
    (heta_ne_one : eta ⟨x, hx⟩ ≠ 1) :
    ∃ t : ZMod p, t ≠ 0 ∧
      bCoordIota eta (Additive.ofMul (⟨x, hx⟩ : ↥Bs)) = t • (1 : Fin n → ZMod p) := by
  let t : ZMod p := Multiplicative.toAdd (eta ⟨x, hx⟩ i0)
  have ht : t ≠ 0 := by
    intro ht0
    apply heta_ne_one
    funext k
    rw [hxconst k i0]
    exact toAdd_eq_zero.mp (by simpa [t] using ht0)
  refine ⟨t, ht, ?_⟩
  funext k
  simp only [bCoordIota_apply_ofMul]
  rw [hxconst k i0]
  simp [t, Pi.smul_apply]

omit [Finite G] in
private theorem signed_form_of_mem_aPermutationFull [Fact p.Prime] {n : ℕ}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    (hLA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    (hx : x ∈ Bs) {a : MulAut ↥Bs} (ha : a ∈ ggAutomizer L Bs)
    (hfix_a_x : a ⟨x, hx⟩ = ⟨x, hx⟩) {t : ZMod p} (ht : t ≠ 0)
    (hw : bCoordIota eta (Additive.ofMul (⟨x, hx⟩ : ↥Bs)) = t • (1 : Fin n → ZMod p)) :
    ∃ (σ : Equiv.Perm (Fin n)) (ε : Fin n → ZMod p),
      (∀ j, ε j = 1 ∨ ε j = -1) ∧ ∀ v j,
        ggLin (p := p) (bCoordIota eta) a v (σ j) = v j := by
  have hcongr : MulAut.congr eta a ∈ aPermutationFull n p := by
    rw [← hLA]
    exact Subgroup.mem_map_of_mem _ ha
  obtain ⟨σ, ε, hε, hσ⟩ := (congr_mem_bSignedFull_iff eta a).mp
    (aPermutationFull_le_bSignedFull hcongr)
  have hs_fix_w : ggLin (p := p) (bCoordIota eta) a
      (bCoordIota eta (Additive.ofMul (⟨x, hx⟩ : ↥Bs))) =
      bCoordIota eta (Additive.ofMul (⟨x, hx⟩ : ↥Bs)) :=
    (ggLin_fix_iff (p := p) (bCoordIota eta) a ⟨x, hx⟩).mp hfix_a_x
  have hw_e : ggLin (p := p) (bCoordIota eta) a (t • (1 : Fin n → ZMod p)) =
      t • (1 : Fin n → ZMod p) := by
    rw [← hw]
    exact hs_fix_w
  have hs_one : ggLin (p := p) (bCoordIota eta) a (1 : Fin n → ZMod p) = 1 := by
    have h := hw_e
    rw [map_smul] at h
    exact smul_right_injective (Fin n → ZMod p) ht h
  have hε_one : ∀ j, ε j = 1 := by
    intro j
    have h := signedPerm_coord σ ε hσ (1 : Fin n → ZMod p) j
    rw [hs_one] at h
    simpa using h.symm
  refine ⟨σ, ε, hε, ?_⟩
  intro v j
  rw [signedPerm_coord σ ε hσ v j, hε_one j, one_mul]

private theorem natCast_eq_one_or_neg_one_of_bCoordinateBlock
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n : ℕ} (hn : 4 ≤ n)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {i0 : Fin n} (hx : x ∈ Bs)
    (hxi0 : ∀ k, k ≠ i0 → eta ⟨x, hx⟩ k = 1)
    {φ a : MulAut ↥Bs} (hrefl : GGIsReflection p φ)
    (haB : MulAut.congr eta a ∈ bCoordinateBlock n p i0)
    {c : ℕ} (hca : ∀ b : ↥Bs, φ b * (a b ^ c)⁻¹ ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs)) :
    (c : ZMod p) = 1 ∨ (c : ZMod p) = -1 := by
  obtain ⟨hp, -, -, -, -⟩ := hR.1.1.tableB_facts
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    obtain ⟨-, hp2, -⟩ := (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
    exact hp2
  have hx1 : x ≠ 1 := hR.1.1.1.2.2.2.2.2.2.1.2.2.1
  let ι := bCoordIota eta
  let r := ggLin (p := p) ι φ
  have hr : GGLinRefl r := (ggIsReflection_iff_ggLinRefl hp2 ι φ).mp hrefl
  have ha_fix : MulAut.congr eta a (eta ⟨x, hx⟩) = eta ⟨x, hx⟩ :=
    (forall_bCoordinateBlock_fix_iff hp hp2 i0 (eta ⟨x, hx⟩)).mpr hxi0 _ haB
  have hfix_a_x : a ⟨x, hx⟩ = ⟨x, hx⟩ := by
    apply eta.injective
    simpa [MulAut.congr_apply] using ha_fix
  obtain ⟨t, ht, _, hw⟩ := bCoord_eq_smul_basis_of_axis hx hxi0
    (eta_ne_one_of_ne_one (eta := eta) hx hx1)
  obtain ⟨σ, ε, hε, hσ_i0, hσ_coord⟩ :=
    signed_form_of_mem_bCoordinateBlock hx haB hfix_a_x ht hw
  exact eq_one_or_eq_neg_one_of_linRefl_sub_smul_signedPerm (p := p) (n := n) hn (i0 := i0)
    hr σ ε hε hσ_i0 hσ_coord (c : ZMod p) _ (lin_sub_smul_mem_span hx hca)

theorem GGSecFiveRouteCfg.mem_of_native_of_mem_bCoordinateBlock
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n : ℕ} (hn : 4 ≤ n)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {i0 : Fin n} (hx : x ∈ Bs)
    (hxi0 : ∀ k, k ≠ i0 → eta ⟨x, hx⟩ k = 1) {H : Subgroup (MulAut ↥Bs)}
    (hH : ∀ h ∈ H, h ∈ ggInduced ⊤ Bs) (hneg : (MulAut.congr eta).symm (negOff i0) ∈ H)
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggInduced ⊤ Bs) (hrefl : GGIsReflection p φ)
    (hfix : φ ⟨x, hx⟩ = ⟨x, hx⟩) {c : ℕ} {a : MulAut ↥Bs} (ha : a ∈ H)
    (haB : MulAut.congr eta a ∈ bCoordinateBlock n p i0)
    (hca : ∀ b : ↥Bs, φ b * (a b ^ c)⁻¹ ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs)) :
    φ ∈ H := by
  obtain ⟨hp, hBs, -, -, -⟩ := hR.1.1.tableB_facts
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    obtain ⟨-, hp2, -⟩ := (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
    exact hp2
  have hx1 : x ≠ 1 := hR.1.1.1.2.2.2.2.2.2.1.2.2.1
  have ha_fix : MulAut.congr eta a (eta ⟨x, hx⟩) = eta ⟨x, hx⟩ :=
    (forall_bCoordinateBlock_fix_iff hp hp2 i0 (eta ⟨x, hx⟩)).mpr hxi0 _ haB
  have hfix_a_x : a ⟨x, hx⟩ = ⟨x, hx⟩ := by
    apply eta.injective
    simpa [MulAut.congr_apply] using ha_fix
  obtain ⟨_, _, hui, _⟩ := bCoord_eq_smul_basis_of_axis hx hxi0
    (eta_ne_one_of_ne_one (eta := eta) hx hx1)
  have hc_pm := natCast_eq_one_or_neg_one_of_bCoordinateBlock hR hn hx hxi0 hrefl haB hca
  rcases hc_pm with hc1 | hcneg
  · have hpow : ∀ g : ↥Bs, g ^ c = g := fun g =>
      pow_eq_self_of_natCast_eq_one hp (Subtype.ext (hBs.2 g g.2)) hc1
    have hca1 : ∀ b : ↥Bs, φ b * (a b)⁻¹ ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs) :=
      fun b => by simpa [hpow (a b)] using hca b
    rw [eq_of_mul_inv_mem_zpowers_of_mem_ggInduced hR hx hφ hfix
      (hH a ha) hfix_a_x hca1]
    exact ha
  · exact mem_of_neg_one hR hx hxi0 hui hH hneg hφ hfix hfix_a_x ha hcneg hca

theorem GGSecFiveRouteCfg.mem_ggAutomizer_of_native_bCoordinateBlock
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n : ℕ} (hn : 4 ≤ n)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {i0 : Fin n}
    (hLB : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    (hx : x ∈ Bs) {φ : MulAut ↥Bs} (hφ : φ ∈ ggInduced ⊤ Bs) (hrefl : GGIsReflection p φ)
    (hfix : φ ⟨x, hx⟩ = ⟨x, hx⟩) {c : ℕ} {a : MulAut ↥Bs} (ha : a ∈ ggAutomizer L Bs)
    (hca : ∀ b : ↥Bs, φ b * (a b ^ c)⁻¹ ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs)) :
    φ ∈ ggAutomizer L Bs := by
  obtain ⟨hp, -, -, -, -⟩ := hR.1.1.tableB_facts
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    obtain ⟨-, hp2, -⟩ := (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
    exact hp2
  have hfixB := fix_eta_x_of_map_eq hx hR hLB
  have hxi0 : ∀ k, k ≠ i0 → eta ⟨x, hx⟩ k = 1 :=
    (forall_bCoordinateBlock_fix_iff hp hp2 i0 (eta ⟨x, hx⟩)).mp hfixB
  have haB : MulAut.congr eta a ∈ bCoordinateBlock n p i0 := by
    rw [← hLB]
    exact Subgroup.mem_map_of_mem _ ha
  have hneg : (MulAut.congr eta).symm (negOff i0) ∈ ggAutomizer L Bs := by
    have hmem : negOff (p := p) i0 ∈
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom := by
      rw [hLB]
      exact negOff_mem_bCoordinateBlock (p := p) i0
    obtain ⟨a₀, ha₀, hEq⟩ := Subgroup.mem_map.mp hmem
    have hsymm : a₀ = (MulAut.congr eta).symm (negOff i0) := by
      apply (MulAut.congr eta).injective
      rw [MulEquiv.apply_symm_apply]
      exact hEq
    rw [← hsymm]
    exact ha₀
  exact GGSecFiveRouteCfg.mem_of_native_of_mem_bCoordinateBlock (H := ggAutomizer L Bs)
    hR hn hx hxi0 (fun _ hh => mem_ggInduced_top_of_mem_ggAutomizer hh) hneg
    hφ hrefl hfix ha haB hca

theorem GGSecFiveRouteCfg.mem_ggAutomizer_of_native_aPermutationFull
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n : ℕ} (hn : 5 ≤ n)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    (hLA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    (hx : x ∈ Bs) {φ : MulAut ↥Bs} (hφ : φ ∈ ggInduced ⊤ Bs) (hrefl : GGIsReflection p φ)
    (hfix : φ ⟨x, hx⟩ = ⟨x, hx⟩) {c : ℕ} {a : MulAut ↥Bs} (ha : a ∈ ggAutomizer L Bs)
    (hca : ∀ b : ↥Bs, φ b * (a b ^ c)⁻¹ ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs)) :
    φ ∈ ggAutomizer L Bs := by
  obtain ⟨hp, hBs, -, -, -⟩ := hR.1.1.tableB_facts
  have : Fact p.Prime := ⟨hp⟩
  have hx1 : x ≠ 1 := hR.1.1.1.2.2.2.2.2.2.1.2.2.1
  let ι := bCoordIota eta
  let r := ggLin (p := p) ι φ
  have hp2 : p ≠ 2 := by
    obtain ⟨-, hp2, -⟩ := (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
    exact hp2
  have hr : GGLinRefl r := (ggIsReflection_iff_ggLinRefl hp2 ι φ).mp hrefl
  have hfixA := fix_eta_x_of_map_eq hx hR hLA
  have hxconst : ∀ a b, eta ⟨x, hx⟩ a = eta ⟨x, hx⟩ b :=
    (forall_aPermutationFull_fix_iff (eta ⟨x, hx⟩)).mp hfixA
  have heta_ne_one := eta_ne_one_of_ne_one (eta := eta) hx hx1
  let i0 : Fin n := ⟨0, by omega⟩
  obtain ⟨t, ht, hw⟩ := aCoord_eq_smul_one i0 hx hxconst heta_ne_one
  have hfix_a_x := ggRM_AL_fixes_x (ggSecFiveRouteCfg'_of_routeCfg hR) hx a ha
  obtain ⟨σ, ε, hε, hσ_coord⟩ :=
    signed_form_of_mem_aPermutationFull hLA hx ha hfix_a_x ht hw
  have hc1 : (c : ZMod p) = 1 :=
    eq_one_of_linRefl_sub_smul_perm_mem_span (p := p) (n := n) hn hr σ hσ_coord
      (c : ZMod p) _ (lin_sub_smul_mem_span hx hca)
  have hpow : ∀ g : ↥Bs, g ^ c = g := fun g =>
    pow_eq_self_of_natCast_eq_one hp (Subtype.ext (hBs.2 g g.2)) hc1
  have hca1 : ∀ b : ↥Bs, φ b * (a b)⁻¹ ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs) :=
    fun b => by simpa [hpow (a b)] using hca b
  rw [eq_of_mul_inv_mem_zpowers_of_mem_ggInduced hR hx hφ hfix
    (mem_ggInduced_top_of_mem_ggAutomizer ha) hfix_a_x hca1]
  exact ha

private theorem sum_basisFun_eq_one {n : ℕ} :
    (∑ j, Pi.basisFun (ZMod p) (Fin n) j) = (1 : Fin n → ZMod p) := by
  funext k
  rw [Finset.sum_apply]
  simp [Pi.basisFun_apply, Pi.single_apply]

private theorem basisFun_of_perm_coord {n : ℕ} {f : (Fin n → ZMod p) → Fin n → ZMod p}
    {σ : Equiv.Perm (Fin n)} (hσ : ∀ v j, f v (σ j) = v j) (i : Fin n) :
    f (Pi.basisFun (ZMod p) (Fin n) i) = Pi.basisFun (ZMod p) (Fin n) (σ i) := by
  funext k
  obtain ⟨j, rfl⟩ := σ.surjective k
  rw [hσ, Pi.basisFun_apply, Pi.basisFun_apply, Pi.single_apply, Pi.single_apply]
  by_cases h : j = i
  · subst h
    simp
  · have h' : σ j ≠ σ i := fun hh => h (σ.injective hh)
    simp [h, h']

theorem GGSecFiveRouteCfg.exists_perm_of_native_aPermutationFull [Fact p.Prime]
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n : ℕ}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    (hLA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    (hx : x ∈ Bs) {φ : MulAut ↥Bs} {c : ℕ} {a : MulAut ↥Bs} (ha : a ∈ ggAutomizer L Bs)
    (hca : ∀ b : ↥Bs, φ b * (a b ^ c)⁻¹ ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs)) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, ∃ s : ZMod p,
      ggLin (p := p) (bCoordIota eta) φ (Pi.basisFun (ZMod p) (Fin n) i) =
        (c : ZMod p) • Pi.basisFun (ZMod p) (Fin n) (σ i) +
          s • ∑ j, Pi.basisFun (ZMod p) (Fin n) j := by
  rcases n with _ | m
  · exact ⟨1, fun i => Fin.elim0 i⟩
  have hx1 : x ≠ 1 := hR.1.1.1.2.2.2.2.2.2.1.2.2.1
  have hxconst : ∀ a b, eta ⟨x, hx⟩ a = eta ⟨x, hx⟩ b :=
    (forall_aPermutationFull_fix_iff (eta ⟨x, hx⟩)).mp (fix_eta_x_of_map_eq hx hR hLA)
  obtain ⟨t, ht, hw⟩ := aCoord_eq_smul_one ⟨0, Nat.succ_pos m⟩ hx hxconst
    (eta_ne_one_of_ne_one (eta := eta) hx hx1)
  obtain ⟨σ, -, -, hσ⟩ := signed_form_of_mem_aPermutationFull hLA hx ha
    (ggRM_AL_fixes_x (ggSecFiveRouteCfg'_of_routeCfg hR) hx a ha) ht hw
  refine ⟨σ, fun i => ?_⟩
  have hmem := lin_sub_smul_mem_span (eta := eta) hx hca
    (Pi.basisFun (ZMod p) (Fin (m + 1)) i)
  rw [hw, basisFun_of_perm_coord (f := ggLin (p := p) (bCoordIota eta) a) hσ i] at hmem
  obtain ⟨u, hu⟩ := (Submodule.mem_span_singleton (R := ZMod p)
    (y := t • (1 : Fin (m + 1) → ZMod p))).mp hmem
  refine ⟨u * t, ?_⟩
  rw [sum_basisFun_eq_one, mul_smul, hu]
  abel

end CFSG.StandardType

end
