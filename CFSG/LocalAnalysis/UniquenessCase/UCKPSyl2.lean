module

public import CFSG.LocalAnalysis.UniquenessCase.UCKPSyl1
public import CFSG.Quasithin.EmptyFaithful.SBdK36Abs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.GH74.Uniqueness.Bender CFSG.GH74.Uniqueness.Bender.Frame

theorem fix_of_mem_zpowers {G : Type*} [Group G] {q : ℕ} [Fact q.Prime] {β : MulAut G} {k : ℕ}
    (hβ : β ^ (q ^ k) = 1) {x : G} (hx : x ^ q = 1) (hβx : β x ∈ zpowers x) : β x = x := by
  obtain ⟨m, hm⟩ := mem_zpowers_iff.1 hβx
  have hpow : ∀ j : ℕ, (β ^ j) x = x ^ (m ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ β j, MulAut.mul_apply, ← hm, map_zpow, ih, ← _root_.zpow_mul, ← pow_succ]
  by_cases hx1 : x = 1
  · rw [hx1, map_one]
  have hord : orderOf x = q := orderOf_eq_prime hx hx1
  have h1 : x ^ (m ^ (q ^ k)) = x := by rw [← hpow, hβ, MulAut.one_apply]
  have h2 : x ^ (m ^ (q ^ k) - 1) = 1 := by rw [_root_.zpow_sub, h1, zpow_one, mul_inv_cancel]
  have h3 : ((orderOf x : ℕ) : ℤ) ∣ m ^ (q ^ k) - 1 := orderOf_dvd_iff_zpow_eq_one.2 h2
  rw [hord] at h3
  have h4 : (m : ZMod q) = 1 := by
    have h5 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).2 h3
    push_cast at h5
    rw [ZMod.pow_card_pow] at h5
    exact sub_eq_zero.1 h5
  have h6 : (q : ℤ) ∣ m - 1 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).1 (by push_cast; rw [h4, sub_self])
  have h7 : x ^ (m - 1) = 1 := orderOf_dvd_iff_zpow_eq_one.1 (by rw [hord]; exact h6)
  rw [← hm]
  calc x ^ m = x ^ (m - 1) * x := by rw [← _root_.zpow_add_one, sub_add_cancel]
    _ = x := by rw [h7, one_mul]

theorem map_mem_normalizer_iff {G : Type*} [Group G] {H : Subgroup G} {β : MulAut G}
    (hβ : ∀ x, β x ∈ H ↔ x ∈ H) (x : G) :
    β x ∈ normalizer (H : Set G) ↔ x ∈ normalizer (H : Set G) := by
  simp only [mem_normalizer_iff]
  constructor
  · intro h y
    rw [← hβ y, h (β y), ← map_inv, ← map_mul, ← map_mul, hβ]
  · intro h y
    obtain ⟨y', rfl⟩ : ∃ y', β y' = y := ⟨β⁻¹ y, MulAut.apply_inv_self G β y⟩
    rw [hβ y', h y', ← map_inv, ← map_mul, ← map_mul, hβ]

theorem inv_mul_mem_of_perm_three {G : Type*} [Group G] {F F₀ : Subgroup G}
    (π : F₀ →* Equiv.Perm (Fin 3)) (hπ : Function.Surjective π)
    (hker : π.ker = F.subgroupOf F₀) {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) {β : MulAut G}
    {k : ℕ} (hβ : β ^ (q ^ k) = 1) (hβF₀ : ∀ x, β x ∈ F₀ ↔ x ∈ F₀)
    (hβF : ∀ x, β x ∈ F ↔ x ∈ F) : ∀ w ∈ F₀, w⁻¹ * β w ∈ F := by
  let β₀ : MulAut F₀ :=
    { toFun := fun w => ⟨β w, (hβF₀ w).2 w.2⟩
      invFun := fun w => ⟨β⁻¹ (w : G), (hβF₀ _).1 (by rw [MulAut.apply_inv_self]; exact w.2)⟩
      left_inv := fun w => Subtype.ext (MulAut.inv_apply_self G β w)
      right_inv := fun w => Subtype.ext (MulAut.apply_inv_self G β w)
      map_mul' := fun w w' => Subtype.ext (map_mul β (w : G) (w' : G)) }
  have hβ₀ : ∀ w : F₀, ((β₀ w : F₀) : G) = β w := fun w => rfl
  have hK : π.ker.map (β₀ : F₀ →* F₀) = π.ker := by
    ext w
    rw [Subgroup.mem_map, hker, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Subgroup.mem_subgroupOf] at hy
      exact (hβF y).2 hy
    · intro hw
      refine ⟨β₀.symm w, ?_, β₀.apply_symm_apply w⟩
      rw [Subgroup.mem_subgroupOf]
      have h1 : ((β₀ (β₀.symm w) : F₀) : G) ∈ F := by rw [β₀.apply_symm_apply]; exact hw
      exact (hβF _).1 h1
  let e : F₀ ⧸ π.ker ≃* Equiv.Perm (Fin 3) := QuotientGroup.quotientKerEquivOfSurjective π hπ
  have he : ∀ w : F₀, e (QuotientGroup.mk w) = π w := fun w => rfl
  let σ : MulAut (Equiv.Perm (Fin 3)) :=
    e.symm.trans ((QuotientGroup.congr π.ker π.ker β₀ hK).trans e)
  have hσ : ∀ w : F₀, σ (π w) = π (β₀ w) := by
    intro w
    change e (QuotientGroup.congr π.ker π.ker β₀ hK (e.symm (π w))) = π (β₀ w)
    rw [← he w, MulEquiv.symm_apply_apply, QuotientGroup.congr_mk]
    rfl
  have hpow : ∀ m : ℕ, ∀ w : F₀, (σ ^ m) (π w) = π ((β₀ ^ m) w) := by
    intro m
    induction m with
    | zero => intro w; rfl
    | succ m ih =>
      intro w
      rw [pow_succ' σ m, MulAut.mul_apply, ih, hσ, pow_succ' β₀ m, MulAut.mul_apply]
  have hβ₀pow : ∀ m : ℕ, ∀ w : F₀, (((β₀ ^ m) w : F₀) : G) = (β ^ m) w := by
    intro m
    induction m with
    | zero => intro w; rfl
    | succ m ih =>
      intro w
      rw [pow_succ' β₀ m, MulAut.mul_apply, hβ₀, ih, pow_succ' β m, MulAut.mul_apply]
  have hσq : σ ^ (q ^ k) = 1 := by
    refine MulEquiv.ext fun τ => ?_
    obtain ⟨w, rfl⟩ := hπ τ
    have h1 : (β₀ ^ (q ^ k)) w = w := Subtype.ext (by rw [hβ₀pow, hβ, MulAut.one_apply])
    rw [hpow, h1, MulAut.one_apply]
  have hσ1 : σ = 1 := by
    have hcard : Nat.card (MulAut (Equiv.Perm (Fin 3))) = 6 := by
      rw [← Nat.card_congr CFSG.Quasithin.SBd.conjEquivPerm3.toEquiv, Nat.card_eq_fintype_card,
        Fintype.card_perm, Fintype.card_fin]
      rfl
    have h6 : Nat.Coprime q 6 := hq.coprime_iff_not_dvd.2 fun h => by
      rcases eq_two_or_three_of_dvd_six hq h with h | h <;> omega
    have h1 : Nat.Coprime (orderOf σ) 6 :=
      Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hσq) (Nat.Coprime.pow_left k h6)
    exact orderOf_eq_one_iff.1 (h1.eq_one_of_dvd (hcard ▸ orderOf_dvd_natCard σ))
  intro w hw
  have h1 : π (β₀ ⟨w, hw⟩) = π ⟨w, hw⟩ := by rw [← hσ, hσ1, MulAut.one_apply]
  have h2 : (⟨w, hw⟩ : F₀)⁻¹ * β₀ ⟨w, hw⟩ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
  rw [hker, Subgroup.mem_subgroupOf] at h2
  exact h2

theorem commute_map_of_inv_mul_mem {G : Type*} [Group G] {F : Subgroup G}
    (hcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) {β : MulAut G} {w x : G} (hw : w⁻¹ * β w ∈ F)
    (hx : β x ∈ F) (hwx : w * x = x * w) : w * β x = β x * w := by
  have hβw : β w = w * (w⁻¹ * β w) := (mul_inv_cancel_left w (β w)).symm
  have h1 : β w * β x = β x * β w := by rw [← map_mul, hwx, map_mul]
  rw [hβw] at h1
  have h2 := hcomm _ hw (β x) hx
  have h3 : w * β x * (w⁻¹ * β w) = β x * w * (w⁻¹ * β w) := by
    calc w * β x * (w⁻¹ * β w) = w * (β x * (w⁻¹ * β w)) := mul_assoc _ _ _
      _ = w * ((w⁻¹ * β w) * β x) := by rw [h2]
      _ = w * (w⁻¹ * β w) * β x := (mul_assoc _ _ _).symm
      _ = β x * (w * (w⁻¹ * β w)) := h1
      _ = β x * w * (w⁻¹ * β w) := (mul_assoc _ _ _).symm
  exact mul_right_cancel h3

theorem exists_three_dvd_mul_add_one {q : ℕ} (hq : q.Prime) (hq3 : 3 < q) :
    ∃ s, 3 ∣ q * s + 1 := by
  have h3 : q % 3 ≠ 0 := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 (Nat.dvd_of_mod_eq_zero h)
    omega
  rcases (by omega : q % 3 = 1 ∨ q % 3 = 2) with h | h
  · exact ⟨2, by omega⟩
  · exact ⟨1, by omega⟩

theorem exists_pow_eq_of_pow_eq_one {E : Type} [Field E] {m q : ℕ} [NeZero q]
    {z a : rootsOfUnity m E} (hz : orderOf z = q) (ha : a ^ q = 1) : ∃ i : ℕ, z ^ i = a := by
  have h1 : IsPrimitiveRoot (z : Eˣ) q :=
    IsPrimitiveRoot.iff_orderOf.2 (by rw [Subgroup.orderOf_coe, hz])
  obtain ⟨i, -, hi⟩ := h1.eq_pow_of_mem_rootsOfUnity (ξ := (a : Eˣ))
    (by rw [mem_rootsOfUnity, ← Subgroup.coe_pow, ha]; rfl)
  exact ⟨i, Subtype.ext (by rw [Subgroup.coe_pow]; exact hi)⟩

theorem prod_line_eq_one {G : Type*} [CommGroup G] (z : G) (k : Fin 3) :
    ∏ l, (if l = k then z ^ (-2 : ℤ) else z) = 1 := by
  fin_cases k <;> simp [Fin.prod_univ_three] <;> group

variable {n : ℕ} {E : Type} [Field E] {hU : UnitaryFieldData 2 n E}
  {v : Fin 3 → (Fin 3 → E)}

theorem pow_three_of_mem_normOneScalars {z : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)}
    (hz : z ∈ normOneScalars hU (gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) 3) : z ^ 3 = 1 := by
  obtain ⟨c, -, hc3, hzc⟩ := hz
  apply Subtype.ext
  rw [Subgroup.coe_pow, hzc, ← map_pow, hc3, map_one]
  rfl

theorem exists_frameEigHom_eq (hv : IsOrthonormalFrame hU v)
    (c : Fin 3 → rootsOfUnity (2 ^ n + 1) E) (hc : ∏ i, c i = 1) :
    ∃ d : frameTorusSU hU v, ∀ i, frameEigHom hv i d = c i := by
  have hcN : ∀ i, hU.norm ((c i : Eˣ) : E) = 1 := fun i => norm_coe_rootsOfUnity hU (c i)
  have hcp : ∏ i, ((c i : Eˣ) : E) = 1 := by
    have h2 := congrArg (fun x : rootsOfUnity (2 ^ n + 1) E => ((x : Eˣ) : E)) hc
    simpa only [SubmonoidClass.coe_finsetProd, Units.coe_prod, OneMemClass.coe_one,
      Units.val_one] using h2
  exact ⟨⟨frameDiagElt hv _ hcN hcp, frameDiagElt_mem_frameTorusSU hv _ hcN hcp⟩, fun i =>
    Subtype.ext (Units.ext (frameEig_eq hv (frameDiagElt_mulVec hv _ hcN hcp i)))⟩

theorem exists_frameMono_perm (hv : IsOrthonormalFrame hU v) (σ : Equiv.Perm (Fin 3)) :
    ∃ w : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E), w ∈ frameMonoSU hU v ∧
      ∀ l, lineIdx v ((((w : GL (Fin 3) E))⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) l =
        σ.symm l := by
  have hc : ∀ i : Fin 3, hU.norm ((fun _ => (1 : E)) i) = 1 := fun _ => by
    simp [UnitaryFieldData.norm]
  have hp : ∏ i : Fin 3, (fun _ => (1 : E)) i = 1 := by simp
  refine ⟨frameMonoElt hv σ (fun _ => 1) hc hp, frameMonoElt_mem_frameMonoSU hv σ _ hc hp,
    fun l => lineIdx_eq hv (c := ((fun _ => (1 : E)) (σ.symm l))⁻¹) ?_⟩
  apply inv_mulVec_eq (ne_zero_of_norm_eq_one (hc (σ.symm l)))
  rw [frameMonoElt_mulVec, Equiv.apply_symm_apply]

theorem exists_eig_mul_of_mk_eq (hv : IsOrthonormalFrame hU v) {d d' : frameTorusSU hU v}
    (h : (QuotientGroup.mk (d : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) :
      primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)) =
      QuotientGroup.mk (d' : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E))) :
    ∃ s, s ^ 3 = 1 ∧ ∀ l, frameEigHom hv l d' = frameEigHom hv l d * s := by
  have hz := QuotientGroup.eq.1 h
  have hzT := normOneScalars_le_frameTorusSU hU v 3 hz
  refine ⟨frameEigHom hv 0 ⟨_, hzT⟩, ?_, fun l => ?_⟩
  · rw [← map_pow]
    have h1 : (⟨_, hzT⟩ : frameTorusSU hU v) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact pow_three_of_mem_normOneScalars hz)
    rw [h1, map_one]
  · have hd' : d' = d * ⟨_, hzT⟩ := Subtype.ext (mul_inv_cancel_left _ _).symm
    exact (congrArg (frameEigHom hv l) hd').trans
      (by rw [map_mul, frameEigHom_eq_of_mem_normOneScalars hv (g := ⟨_, hzT⟩) hz l 0])

theorem exists_lift_pow_eq_one {q : ℕ} (hq : q.Prime) (hq3 : 3 < q)
    {t : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)} (ht : t ∈ frameTorus hU v)
    (htq : t ^ q = 1) :
    ∃ d ∈ frameTorusSU hU v, (QuotientGroup.mk d : primeFormP hU
      (1 : Matrix (Fin 3) (Fin 3) E)) = t ∧ d ^ q = 1 := by
  obtain ⟨d₀, hd₀, rfl⟩ := Subgroup.mem_map.1 ht
  obtain ⟨s, j, hj⟩ := exists_three_dvd_mul_add_one hq hq3
  have h1 : d₀ ^ q ∈ normOneScalars hU (gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) 3 := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact htq
  refine ⟨d₀ ^ (q * s + 1), pow_mem hd₀ _, ?_, ?_⟩
  · rw [QuotientGroup.mk_pow, pow_succ, pow_mul]
    change (QuotientGroup.mk' _ d₀ ^ q) ^ s * QuotientGroup.mk' _ d₀ = QuotientGroup.mk' _ d₀
    rw [htq, one_pow, one_mul]
  · rw [← pow_mul, hj, show 3 * j * q = q * 3 * j by ring, pow_mul, pow_mul,
      pow_three_of_mem_normOneScalars h1, one_pow]

theorem frameEig_eq_of_herm_ne_zero (hv : IsOrthonormalFrame hU v)
    {g d d' : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)} (hd : d ∈ frameTorusSU hU v)
    (hd' : d' ∈ frameTorusSU hU v) (hconj : g * d * g⁻¹ = d') {i j : Fin 3}
    (ha : herm hU (v j) (((g : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ v i) ≠ 0) :
    frameEig hU v ((d' : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) j =
      frameEig hU v ((d : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) i := by
  set gm : Matrix (Fin 3) (Fin 3) E := ((g : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) with hgm
  have hde : ((d' : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ (gm *ᵥ v i) =
      frameEig hU v ((d : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) i • (gm *ᵥ v i) := by
    rw [← hconj]
    change (gm * ((d : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *
      ((((g : GL (Fin 3) E))⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E)) *ᵥ (gm *ᵥ v i) = _
    rw [← mulVec_mulVec, ← mulVec_mulVec, mulVec_mulVec (v i)
      ((((g : GL (Fin 3) E))⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) gm, hgm, Units.inv_mul,
      one_mulVec, mulVec_frameEig hv hd i, mulVec_smul]
  have h1 := herm_mulVec_mulVec hU d'.2 (v j) (gm *ᵥ v i)
  rw [mulVec_frameEig hv hd' j, hde, herm_smul_left, herm_smul_right] at h1
  have hn := norm_frameEig hv hd' j
  set e := frameEig hU v ((d' : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) j
  set c := frameEig hU v ((d : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) i
  have h2 : (hU.bar e * c) * herm hU (v j) (gm *ᵥ v i) = 1 * herm hU (v j) (gm *ᵥ v i) := by
    rw [one_mul, mul_assoc]
    exact h1
  have h3 : hU.bar e * c = 1 := mul_right_cancel₀ ha h2
  have h4 : e * hU.bar e = 1 := hn
  calc e = e * (hU.bar e * c) := by rw [h3, mul_one]
    _ = (e * hU.bar e) * c := by rw [mul_assoc]
    _ = c := by rw [h4, one_mul]

theorem mem_frameTorus_of_commute (hv : IsOrthonormalFrame hU v) {d₀ : frameTorusSU hU v}
    (hreg : Function.Injective fun i => frameEigHom hv i d₀ ^ 3)
    {g : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)}
    (hg : g * QuotientGroup.mk (d₀ : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) =
      QuotientGroup.mk (d₀ : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) * g) :
    g ∈ frameTorus hU v := by
  classical
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  set y := g * (d₀ : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) * g⁻¹ with hy
  have hmk : (QuotientGroup.mk (d₀ : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) :
      primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)) = QuotientGroup.mk y := by
    rw [hy, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hg,
      mul_inv_cancel_right]
  have hyT : y ∈ frameTorusSU hU v := by
    have h1 := mul_mem d₀.2 (normOneScalars_le_frameTorusSU hU v 3 (QuotientGroup.eq.1 hmk))
    rwa [mul_inv_cancel_left] at h1
  obtain ⟨s, hs3, hs⟩ := exists_eig_mul_of_mk_eq hv (d := d₀) (d' := ⟨y, hyT⟩) hmk
  set gm : Matrix (Fin 3) (Fin 3) E := ((g : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E)
  have hsupp : ∀ i j, herm hU (v j) (gm *ᵥ v i) ≠ 0 → j = i := by
    intro i j ha
    have h2 : frameEigHom hv j ⟨y, hyT⟩ = frameEigHom hv i d₀ :=
      (frameEigHom_eq_iff hv).2 (frameEig_eq_of_herm_ne_zero hv d₀.2 hyT rfl ha)
    apply hreg
    change frameEigHom hv j d₀ ^ 3 = frameEigHom hv i d₀ ^ 3
    rw [← h2, hs, mul_pow, hs3, mul_one]
  have hdiag : ∀ i, gm *ᵥ v i = herm hU (v i) (gm *ᵥ v i) • v i := by
    intro i
    conv_lhs => rw [frame_expand hv (gm *ᵥ v i)]
    rw [Finset.sum_eq_single i]
    · intro j _ hj
      by_contra hne
      exact hj (hsupp i j fun h0 => hne (by rw [h0, zero_smul]))
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hgT : g ∈ frameTorusSU hU v := fun i => ⟨herm hU (v i) (gm *ᵥ v i), fun h0 =>
    mulVec_ne_zero (g : GL (Fin 3) E) (frame_ne_zero hv i) (by rw [hdiag i, h0, zero_smul]),
    hdiag i⟩
  exact Subgroup.mem_map_of_mem _ hgT

theorem conj_eq_of_invariant (hv : IsOrthonormalFrame hU v)
    {w : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)} (hwM : w ∈ frameMonoSU hU v)
    {σ : Equiv.Perm (Fin 3)}
    (hwl : ∀ l, lineIdx v ((((w : GL (Fin 3) E))⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) l =
      σ l) {ℓ : frameTorusSU hU v} (hsym : ∀ l, frameEigHom hv (σ l) ℓ = frameEigHom hv l ℓ) :
    w * (ℓ : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) * w⁻¹ = ℓ :=
  congrArg Subtype.val (frameTorusSU_ext hv (g := ⟨w * ℓ * w⁻¹, conj_mem_frameTorusSU hwM ℓ.2⟩)
    (h := ℓ) fun l => by rw [frameEigHom_conj hv hwM ℓ l, hwl, hsym])

theorem mem_zpowers_of_commute_swap (hv : IsOrthonormalFrame hU v) {q : ℕ} (hq : q.Prime)
    (hq3 : 3 < q) {z : rootsOfUnity (2 ^ n + 1) E} (hz : orderOf z = q) {i j k : Fin 3}
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) {ℓ : frameTorusSU hU v}
    (hℓ : ∀ l, frameEigHom hv l ℓ = if l = k then z ^ (-2 : ℤ) else z)
    {w : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)} (hwM : w ∈ frameMonoSU hU v)
    (hwl : ∀ l, lineIdx v ((((w : GL (Fin 3) E))⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) l =
      Equiv.swap i j l)
    {t : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)} (ht : t ∈ frameTorus hU v) (htq : t ^ q = 1)
    (hwt : (QuotientGroup.mk w : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)) * t =
      t * QuotientGroup.mk w) :
    t ∈ zpowers (QuotientGroup.mk (ℓ : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) :
      primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  obtain ⟨d, hdT, rfl, hdq⟩ := exists_lift_pow_eq_one hq hq3 ht htq
  set D : frameTorusSU hU v := ⟨d, hdT⟩ with hD
  have hY : ∀ l, frameEigHom hv l ⟨w * d * w⁻¹, conj_mem_frameTorusSU hwM hdT⟩ =
      frameEigHom hv (Equiv.swap i j l) D := fun l => by
    rw [← hwl l]
    exact frameEigHom_conj hv hwM D l
  have hmk : (QuotientGroup.mk (w * d * w⁻¹) : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)) =
      QuotientGroup.mk d := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hwt, mul_inv_cancel_right]
  obtain ⟨s, -, hs⟩ := exists_eig_mul_of_mk_eq hv
    (d := ⟨w * d * w⁻¹, conj_mem_frameTorusSU hwM hdT⟩) (d' := D) hmk
  have hs1 : s = 1 := by
    have h := hs k
    rw [hY, Equiv.swap_apply_of_ne_of_ne hki hkj] at h
    exact mul_eq_left.1 h.symm
  have hij' : frameEigHom hv i D = frameEigHom hv j D := by
    have h := hs i
    rwa [hY, Equiv.swap_apply_left, hs1, mul_one] at h
  have hDq : D ^ q = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hdq)
  obtain ⟨m, hm⟩ := exists_pow_eq_of_pow_eq_one hz (a := frameEigHom hv i D)
    (by rw [← map_pow, hDq, map_one])
  have hk : frameEigHom hv k D = (z ^ m * z ^ m)⁻¹ := by
    have h := prod_frameEigHom hv D
    rw [prod_fin3_eq (fun l => frameEigHom hv l D) hij hki hkj, ← hij', ← hm] at h
    exact eq_inv_of_mul_eq_one_right h
  have hDℓ : D = ℓ ^ m := frameTorusSU_ext hv fun l => by
    rw [map_pow, hℓ]
    rcases fin3_cover i j k hij hki hkj l with rfl | rfl | rfl
    · rw [if_neg hki.symm, hm]
    · rw [if_neg hkj.symm, ← hij', hm]
    · rw [if_pos rfl, hk]
      group
  rw [mem_zpowers_iff]
  refine ⟨m, ?_⟩
  rw [zpow_natCast, ← QuotientGroup.mk_pow, ← Subgroup.coe_pow, ← hDℓ]

theorem pow_three_eq_lines (hv : IsOrthonormalFrame hU v) {z : rootsOfUnity (2 ^ n + 1) E}
    {ℓ₁ ℓ₂ : frameTorusSU hU v}
    (hℓ₁ : ∀ l, frameEigHom hv l ℓ₁ = if l = 1 then z ^ (-2 : ℤ) else z)
    (hℓ₂ : ∀ l, frameEigHom hv l ℓ₂ = if l = 2 then z ^ (-2 : ℤ) else z)
    {d : frameTorusSU hU v} {a b : ℕ} (ha : frameEigHom hv 0 d = z ^ a)
    (hb : frameEigHom hv 1 d = z ^ b) :
    d ^ 3 = ℓ₂ ^ (2 * (a : ℤ) + b) * ℓ₁ ^ ((a : ℤ) - b) := by
  have h2 : frameEigHom hv 2 d = (z ^ a * z ^ b)⁻¹ := by
    have h := prod_frameEigHom hv d
    rw [Fin.prod_univ_three, ha, hb] at h
    exact eq_inv_of_mul_eq_one_right h
  refine frameTorusSU_ext hv fun l => ?_
  rw [map_pow, map_mul, map_zpow, map_zpow, hℓ₁, hℓ₂]
  fin_cases l
  · simp only [Fin.zero_eta, Fin.isValue, zero_ne_one, ↓reduceIte, Fin.reduceEq, ha]
    group
  · simp only [Fin.mk_one, Fin.isValue, ↓reduceIte, Fin.reduceEq, hb]
    group
  · simp only [Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte, h2]
    group

theorem fix_of_normalizes_frame (hU : UnitaryFieldData 2 n E) (hn : 2 ≤ n)
    {v : Fin 3 → (Fin 3 → E)} (hv : IsOrthonormalFrame hU v) {q : ℕ} (hq : q.Prime)
    (hq3 : 3 < q) (hqn : q ∣ 2 ^ n + 1)
    {T : Subgroup (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E))} (hTF : T ≤ frameTorus hU v)
    (hΩT : ∀ t ∈ frameTorus hU v, t ^ q = 1 → t ∈ T)
    {β : MulAut (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E))} {k : ℕ} (hβ : β ^ (q ^ k) = 1)
    (hβT : ∀ t ∈ T, β t ∈ T) : ∀ t ∈ T, t ^ q = 1 → β t = t := by
  classical
  haveI := hU.finite
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨-, -, hcomm, -, -, -, π, hπ, hker⟩ := frame_group_structure hU hn hv
  have hF₀N := frameMono_eq_normalizer hn hv
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := rootsOfUnity (2 ^ n + 1) E) q
    (by rw [card_rootsOfUnity_eq hU]; exact hqn)
  have hzq : z ^ q = 1 := hz ▸ pow_orderOf_eq_one z
  have h3 : z ^ 3 ≠ 1 := fun h => by
    have := Nat.le_of_dvd (by norm_num) (hz ▸ orderOf_dvd_of_pow_eq_one h)
    omega
  have h6 : z ^ 6 ≠ 1 := fun h => by
    rcases eq_two_or_three_of_dvd_six hq (hz ▸ orderOf_dvd_of_pow_eq_one h) with h | h <;> omega
  obtain ⟨x₀, hx₀⟩ := exists_frameEigHom_eq hv ![z, z⁻¹, 1] (by simp [Fin.prod_univ_three])
  have f01 : z ^ 3 ≠ z⁻¹ ^ 3 := fun h => h6 (by
    rw [show 6 = 3 + 3 from rfl, pow_add]
    nth_rw 2 [h]
    rw [inv_pow, mul_inv_cancel])
  have f02 : z ^ 3 ≠ 1 ^ 3 := by rwa [one_pow]
  have f12 : z⁻¹ ^ 3 ≠ 1 ^ 3 := by rwa [inv_pow, one_pow, inv_ne_one]
  have hreg : Function.Injective fun i => frameEigHom hv i x₀ ^ 3 := by
    intro a b hab
    have hab' : (![z, z⁻¹, 1] a) ^ 3 = (![z, z⁻¹, 1] b) ^ 3 := by simpa only [hx₀] using hab
    fin_cases a <;> fin_cases b
    all_goals first
      | rfl
      | exact absurd hab' f01 | exact absurd hab'.symm f01
      | exact absurd hab' f02 | exact absurd hab'.symm f02
      | exact absurd hab' f12 | exact absurd hab'.symm f12
  have hx₀1 : x₀ ^ q = 1 := frameTorusSU_ext hv fun l => by
    rw [map_pow, hx₀, map_one]
    fin_cases l
    · exact hzq
    · simp [inv_pow, hzq]
    · simp
  set x : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E) :=
    QuotientGroup.mk (x₀ : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) with hxdef
  have hxT : x ∈ T := hΩT _ (Subgroup.mem_map_of_mem _ x₀.2) (by
    rw [hxdef, ← QuotientGroup.mk_pow, ← Subgroup.coe_pow, hx₀1]
    rfl)
  have hβm : ∀ m : ℕ, ∀ t ∈ T, (β ^ m) t ∈ T := by
    intro m
    induction m with
    | zero => intro t ht; exact ht
    | succ m ih =>
      intro t ht
      rw [pow_succ' β m, MulAut.mul_apply]
      exact hβT _ (ih t ht)
  have hβinv : β⁻¹ = β ^ (q ^ k - 1) := inv_eq_of_mul_eq_one_right (by
    rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_pow _ _ hq.pos), hβ])
  have hTinv : ∀ t ∈ T, β⁻¹ t ∈ T := by rw [hβinv]; exact hβm _
  have key : ∀ γ : MulAut (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)),
      (∀ t ∈ T, γ⁻¹ t ∈ T) → ∀ y ∈ frameTorus hU v, γ y ∈ frameTorus hU v := by
    intro γ hγ y hy
    apply mem_frameTorus_of_commute hv hreg
    have h2 := hcomm y hy _ (hTF (hγ _ hxT))
    calc γ y * x = γ y * γ (γ⁻¹ x) := by rw [MulAut.apply_inv_self]
      _ = γ (y * γ⁻¹ x) := (map_mul γ _ _).symm
      _ = γ (γ⁻¹ x * y) := by rw [h2]
      _ = x * γ y := by rw [map_mul, MulAut.apply_inv_self]
  have hβF : ∀ y, β y ∈ frameTorus hU v ↔ y ∈ frameTorus hU v := fun y =>
    ⟨fun h => by
      have h1 := key β⁻¹ (by rw [inv_inv]; exact hβT) (β y) h
      rwa [MulAut.inv_apply_self] at h1,
     fun h => key β hTinv y h⟩
  have hβF₀ : ∀ y, β y ∈ frameMono hU v ↔ y ∈ frameMono hU v := fun y => by
    rw [hF₀N]
    exact map_mem_normalizer_iff hβF y
  have hq5 : 5 ≤ q := by
    rcases (by omega : q = 4 ∨ 5 ≤ q) with h | h
    · exact absurd (h ▸ hq) (by norm_num)
    · exact h
  have hS3 := inv_mul_mem_of_perm_three π hπ hker hq hq5 hβ hβF₀ hβF
  have hline : ∀ i j k : Fin 3, i ≠ j → k ≠ i → k ≠ j → ∀ ℓ : frameTorusSU hU v,
      (∀ l, frameEigHom hv l ℓ = if l = k then z ^ (-2 : ℤ) else z) →
      β (QuotientGroup.mk (ℓ : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E))) =
        QuotientGroup.mk (ℓ : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) := by
    intro i j k hij hki hkj ℓ hℓ
    obtain ⟨w, hwM, hwl⟩ := exists_frameMono_perm hv (Equiv.swap i j)
    rw [Equiv.symm_swap] at hwl
    have hsym : ∀ l, frameEigHom hv (Equiv.swap i j l) ℓ = frameEigHom hv l ℓ := by
      intro l
      rw [hℓ, hℓ]
      by_cases hl : l = k
      · rw [hl, Equiv.swap_apply_of_ne_of_ne hki hkj]
      · have hl' : Equiv.swap i j l ≠ k := fun h => hl (by
          rw [← Equiv.swap_apply_self i j l, h, Equiv.swap_apply_of_ne_of_ne hki hkj])
        rw [if_neg hl, if_neg hl']
    have hwℓ := conj_eq_of_invariant hv hwM hwl hsym
    have hcw : (QuotientGroup.mk w : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)) *
        QuotientGroup.mk (ℓ : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) =
        QuotientGroup.mk (ℓ : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) * QuotientGroup.mk w := by
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      calc w * (ℓ : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) =
            w * (ℓ : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) * w⁻¹ * w := by group
        _ = ℓ * w := by rw [hwℓ]
    have hℓ1 : ℓ ^ q = 1 := frameTorusSU_ext hv fun l => by
      rw [map_pow, hℓ, map_one]
      split_ifs
      · rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hzq,
          _root_.one_zpow]
      · exact hzq
    have hℓq : (QuotientGroup.mk (ℓ : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) :
        primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)) ^ q = 1 := by
      rw [← QuotientGroup.mk_pow, ← Subgroup.coe_pow, hℓ1]
      rfl
    have hℓF : (QuotientGroup.mk (ℓ : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) :
        primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)) ∈ frameTorus hU v :=
      Subgroup.mem_map_of_mem _ ℓ.2
    refine fix_of_mem_zpowers hβ hℓq (mem_zpowers_of_commute_swap hv hq hq3 hz hij hki hkj hℓ
      hwM hwl ((hβF _).2 hℓF) (by rw [← map_pow, hℓq, map_one]) ?_)
    exact commute_map_of_inv_mul_mem hcomm (hS3 _ (Subgroup.mem_map_of_mem _ hwM))
      ((hβF _).2 hℓF) hcw
  obtain ⟨ℓ₂, hℓ₂⟩ := exists_frameEigHom_eq hv _ (prod_line_eq_one z 2)
  obtain ⟨ℓ₁, hℓ₁⟩ := exists_frameEigHom_eq hv _ (prod_line_eq_one z 1)
  have hfix₂ := hline 0 1 2 (by decide) (by decide) (by decide) ℓ₂ hℓ₂
  have hfix₁ := hline 0 2 1 (by decide) (by decide) (by decide) ℓ₁ hℓ₁
  intro t htT htq
  obtain ⟨d, hdT, rfl, hdq⟩ := exists_lift_pow_eq_one hq hq3 (hTF htT) htq
  have hDq : (⟨d, hdT⟩ : frameTorusSU hU v) ^ q = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hdq)
  obtain ⟨a, ha⟩ := exists_pow_eq_of_pow_eq_one hz (a := frameEigHom hv 0 ⟨d, hdT⟩)
    (by rw [← map_pow, hDq, map_one])
  obtain ⟨b, hb⟩ := exists_pow_eq_of_pow_eq_one hz (a := frameEigHom hv 1 ⟨d, hdT⟩)
    (by rw [← map_pow, hDq, map_one])
  have hd3 := pow_three_eq_lines hv hℓ₁ hℓ₂ ha.symm hb.symm
  have ht3 : (QuotientGroup.mk d : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)) ^ 3 =
      (QuotientGroup.mk (ℓ₂ : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E))) ^ (2 * (a : ℤ) + b) *
      (QuotientGroup.mk (ℓ₁ : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E))) ^ ((a : ℤ) - b) := by
    have h1 := congrArg (fun y : frameTorusSU hU v => (QuotientGroup.mk
      (y : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) : primeFormP hU
        (1 : Matrix (Fin 3) (Fin 3) E))) hd3
    simpa only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_zpow, QuotientGroup.mk_pow,
      QuotientGroup.mk_mul, QuotientGroup.mk_zpow] using h1
  have hβt3 : β ((QuotientGroup.mk d : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)) ^ 3) =
      (QuotientGroup.mk d : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)) ^ 3 := by
    rw [ht3, map_mul, map_zpow, map_zpow, hfix₂, hfix₁]
  obtain ⟨s, u, hu⟩ := exists_three_dvd_mul_add_one hq hq3
  have htu : (QuotientGroup.mk d : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)) =
      ((QuotientGroup.mk d : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)) ^ 3) ^ u := by
    rw [← pow_mul, ← hu, pow_succ, pow_mul, htq, one_pow, one_mul]
  rw [htu, map_pow, hβt3]

end CFSG.LocalAnalysis.UniquenessCase.UCK
