module

public import CFSG.RankThree.PartTwo.Sec15.Item153Push2ProofTools
public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS CFSG.Semidihedral.Principal Equiv

variable {G : Type} [Group G] [Finite G]

section Action

variable (W K : Subgroup G)

abbrev nWK : Subgroup G := Subgroup.normalizer (W : Set G) ⊓ Subgroup.normalizer (K : Set G)

omit [Finite G] in
theorem mem_nWK {W K : Subgroup G} (hWK : W ≤ Subgroup.normalizer (K : Set G)) {w : G}
    (hw : w ∈ W) : w ∈ nWK W K :=
  ⟨Subgroup.le_normalizer hw, hWK hw⟩

@[expose] noncomputable def conjW : ↥(nWK W K) →* MulAut ↥W :=
  W.normalizerMonoidHom.comp (Subgroup.inclusion inf_le_left)

omit [Finite G] in
theorem conjW_apply (g : ↥(nWK W K)) (w : ↥W) :
    ((conjW W K g w : ↥W) : G) = (g : G) * w * (g : G)⁻¹ :=
  rfl

omit [Finite G] in
theorem conjW_mem (g : ↥(nWK W K)) (m : ↥W) (hm : m ∈ K.subgroupOf W) :
    conjW W K g m ∈ K.subgroupOf W := by
  rw [Subgroup.mem_subgroupOf] at hm ⊢
  rw [conjW_apply]
  exact (Subgroup.mem_normalizer_iff.mp g.2.2 _).mp hm

variable [(K.subgroupOf W).Normal]

@[expose] noncomputable def qAct : ↥(nWK W K) →* MulAut (↥W ⧸ K.subgroupOf W) :=
  CoprimeFixedPoint.quotientAction (conjW W K) (K.subgroupOf W) (conjW_mem W K)

omit [Finite G] in
theorem qAct_mk (g : ↥(nWK W K)) (w : ↥W) :
    qAct W K g (w : ↥W ⧸ K.subgroupOf W) = ((conjW W K g w : ↥W) : ↥W ⧸ K.subgroupOf W) :=
  rfl

omit [Finite G] in
theorem qAct_mem (hWK : W ≤ Subgroup.normalizer (K : Set G)) (w : G) (hw : w ∈ W) :
    qAct W K ⟨w, mem_nWK hWK hw⟩ = MulAut.conj (QuotientGroup.mk ⟨w, hw⟩) := by
  refine MulEquiv.ext fun q => ?_
  induction q using QuotientGroup.induction_on with
  | H z =>
    rw [qAct_mk, MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul]
    congr 1

end Action

section Perm

variable {W K : Subgroup G} [(K.subgroupOf W).Normal] {n : ℕ}
  (φ : ↥W ⧸ K.subgroupOf W ≃* alternatingGroup (Fin n))
  (autE : Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)))

@[expose] noncomputable def rho : ↥(nWK W K) →* Perm (Fin n) :=
  autE.symm.toMonoidHom.comp ((MulAut.congr φ).toMonoidHom.comp (qAct W K))

omit [Finite G] in
theorem rho_mem (hautE : ∀ σ, autE σ = MulAut.conjNormal σ)
    (hWK : W ≤ Subgroup.normalizer (K : Set G)) (w : G) (hw : w ∈ W) :
    rho φ autE ⟨w, mem_nWK hWK hw⟩ =
      ((φ (QuotientGroup.mk ⟨w, hw⟩) : alternatingGroup (Fin n)) : Perm (Fin n)) := by
  apply autE.injective
  rw [rho, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, hautE, MulAut.conjNormal_val,
    qAct_mem W K hWK w hw]
  refine MulEquiv.ext fun a => ?_
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

omit [Finite G] in
theorem rho_eq_one_iff (hautE : ∀ σ, autE σ = MulAut.conjNormal σ)
    (hWK : W ≤ Subgroup.normalizer (K : Set G)) (w : G) (hw : w ∈ W) :
    rho φ autE ⟨w, mem_nWK hWK hw⟩ = 1 ↔ w ∈ K := by
  rw [rho_mem φ autE hautE hWK w hw, OneMemClass.coe_eq_one, MulEquiv.map_eq_one_iff,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

omit [Finite G] in
theorem rho_mem_alternatingGroup (hautE : ∀ σ, autE σ = MulAut.conjNormal σ)
    (hWK : W ≤ Subgroup.normalizer (K : Set G)) (w : G) (hw : w ∈ W) :
    rho φ autE ⟨w, mem_nWK hWK hw⟩ ∈ alternatingGroup (Fin n) := by
  rw [rho_mem φ autE hautE hWK w hw]
  exact SetLike.coe_mem _

omit [Finite G] in
theorem exists_rho_eq (hautE : ∀ σ, autE σ = MulAut.conjNormal σ)
    (hWK : W ≤ Subgroup.normalizer (K : Set G)) {z : Perm (Fin n)}
    (hz : z ∈ alternatingGroup (Fin n)) :
    ∃ (w : G) (hw : w ∈ W), rho φ autE ⟨w, mem_nWK hWK hw⟩ = z := by
  obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (φ.symm ⟨z, hz⟩)
  refine ⟨w, w.2, ?_⟩
  rw [rho_mem φ autE hautE hWK _ w.2]
  have : (QuotientGroup.mk ⟨(w : G), w.2⟩ : ↥W ⧸ K.subgroupOf W) = φ.symm ⟨z, hz⟩ := hw
  rw [this, MulEquiv.apply_symm_apply]

end Perm

theorem exists_mem_inf_of_fixed {A W K : Subgroup G} (hAF : A ∈ partTwoF G)
    (hAW : A ≤ Subgroup.normalizer (W : Set G)) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hWK : W ≤ Subgroup.normalizer (K : Set G)) (hK : ¬ 3 ∣ Nat.card K) {y : G} (hy : y ∈ W)
    (hfix : ∀ a ∈ A, a * y * a⁻¹ * y⁻¹ ∈ K) (hy3 : y ^ 3 ∈ K) :
    ∃ a₀ ∈ A ⊓ W, a₀ * y⁻¹ ∈ K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set V := K ⊓ W with hVdef
  have hV3 : ¬ 3 ∣ Nat.card V := fun h => hK (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hWV : W ≤ Subgroup.normalizer (V : Set G) :=
    (le_inf hWK Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hAV : A ≤ Subgroup.normalizer (V : Set G) :=
    (le_inf hAK hAW).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hA3 : IsPGroup 3 ↥A := fun a => ⟨1, Subtype.ext (by simpa using hAF.1.2 a a.2)⟩
  let α : ↥A →* MulAut G := MulAut.conj.comp A.subtype
  obtain ⟨c, hcV, hcfix⟩ := (coprime_invariant_coset_fixed 3 hA3 α V hV3 y).1 (by
    intro a x hx
    change (a : G) * x * (a : G)⁻¹ * y⁻¹ ∈ V
    have h1 : (a : G) * (x * y⁻¹) * (a : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hAV a.2) _).mp hx
    have h2 : (a : G) * y * (a : G)⁻¹ * y⁻¹ ∈ V :=
      ⟨hfix a a.2, W.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAW a.2) y).mp hy) (W.inv_mem hy)⟩
    have e : (a : G) * x * (a : G)⁻¹ * y⁻¹ =
        ((a : G) * (x * y⁻¹) * (a : G)⁻¹) * ((a : G) * y * (a : G)⁻¹ * y⁻¹) := by group
    rw [e]
    exact V.mul_mem h1 h2)
  have hcA : ∀ a ∈ A, a * c * a⁻¹ = c := fun a ha => hcfix ⟨a, ha⟩
  have hcW : c ∈ W := by
    have e : c = (c * y⁻¹) * y := by group
    rw [e]
    exact W.mul_mem hcV.2 hy
  have hc3 : c ^ 3 ∈ V := by
    have h := Push153B.pow_mul_mem_of_mem hWV hcV hy 3
    have e : c * y⁻¹ * y = c := by group
    rw [e] at h
    have e2 : c ^ 3 = (c ^ 3 * (y ^ 3)⁻¹) * y ^ 3 := by group
    rw [e2]
    exact V.mul_mem h ⟨hy3, W.pow_mem hy 3⟩
  set m := Nat.card V with hm
  have hcm : (c ^ 3) ^ m = 1 := by
    have h : (⟨c ^ 3, hc3⟩ : ↥V) ^ m = 1 := pow_card_eq_one'
    have h' : ((⟨c ^ 3, hc3⟩ : ↥V) ^ m : ↥V).val = (1 : ↥V).val := congrArg Subtype.val h
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one] at h'
    exact h'
  have hm3 : m ^ 2 % 3 = 1 := by
    have h0 : m % 3 ≠ 0 := fun h0 => hV3 (Nat.dvd_of_mod_eq_zero h0)
    have h : m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases h with h | h <;> simp [Nat.pow_mod, h]
  obtain ⟨j, hj⟩ : ∃ j, m ^ 2 = 3 * j + 1 := ⟨m ^ 2 / 3, by omega⟩
  refine ⟨c ^ (3 * j + 1), ⟨?_, W.pow_mem hcW _⟩, ?_⟩
  · apply mem_of_mem_partTwoF hAF
    · rw [← pow_mul, show (3 * j + 1) * 3 = 3 * (m * m) by rw [← hj]; ring, pow_mul, pow_mul,
        hcm, one_pow]
    · intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff.mp hx]
      have h := congrArg (· ^ (3 * j + 1)) (hcA a ha)
      simp only [conj_pow] at h
      calc c ^ (3 * j + 1) * a = a * (a⁻¹ * c ^ (3 * j + 1) * a) := by group
        _ = a * c ^ (3 * j + 1) := by
          congr 1
          have h' := congrArg (fun z => a⁻¹ * z * a) h
          rw [← h']
          group
  · have e : c ^ (3 * j + 1) * y⁻¹ = (c ^ 3) ^ j * (c * y⁻¹) := by
      rw [← pow_mul, pow_succ]
      group
    rw [e]
    exact K.mul_mem (K.pow_mem hc3.1 j) hcV.1

section PermLift

variable {A W K : Subgroup G} [(K.subgroupOf W).Normal] {n : ℕ}
  (φ : ↥W ⧸ K.subgroupOf W ≃* alternatingGroup (Fin n))
  (autE : Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)))

theorem exists_mem_inf_rho_eq (hautE : ∀ σ, autE σ = MulAut.conjNormal σ)
    (hAF : A ∈ partTwoF G) (hAW : A ≤ Subgroup.normalizer (W : Set G))
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hWK : W ≤ Subgroup.normalizer (K : Set G))
    (hK : ¬ 3 ∣ Nat.card K) {z : Perm (Fin n)} (hz3 : z ^ 3 = 1)
    (hzA : ∀ (a : G) (ha : a ∈ A),
      rho φ autE ⟨a, hAW ha, hAK ha⟩ * z = z * rho φ autE ⟨a, hAW ha, hAK ha⟩) :
    ∃ (a₀ : G) (ha₀ : a₀ ∈ A ⊓ W), rho φ autE ⟨a₀, mem_nWK hWK ha₀.2⟩ = z := by
  have hzA_n : z ∈ alternatingGroup (Fin n) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    have h := congrArg Equiv.Perm.sign hz3
    rw [map_pow, map_one] at h
    rcases Int.units_eq_one_or (Equiv.Perm.sign z) with h1 | h1
    · exact h1
    · rw [h1] at h
      exact absurd h (by decide)
  obtain ⟨y, hy, hρy⟩ := exists_rho_eq φ autE hautE hWK hzA_n
  have hfix : ∀ a ∈ A, a * y * a⁻¹ * y⁻¹ ∈ K := by
    intro a ha
    have hmem : a * y * a⁻¹ * y⁻¹ ∈ W :=
      W.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAW ha) y).mp hy) (W.inv_mem hy)
    refine (rho_eq_one_iff φ autE hautE hWK _ hmem).mp ?_
    have e : (⟨a * y * a⁻¹ * y⁻¹, mem_nWK hWK hmem⟩ : ↥(nWK W K)) =
        ⟨a, hAW ha, hAK ha⟩ * ⟨y, mem_nWK hWK hy⟩ * ⟨a, hAW ha, hAK ha⟩⁻¹ *
          ⟨y, mem_nWK hWK hy⟩⁻¹ := Subtype.ext rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hρy, hzA a ha]
    group
  have hy3 : y ^ 3 ∈ K := by
    refine (rho_eq_one_iff φ autE hautE hWK _ (W.pow_mem hy 3)).mp ?_
    have e : (⟨y ^ 3, mem_nWK hWK (W.pow_mem hy 3)⟩ : ↥(nWK W K)) =
        ⟨y, mem_nWK hWK hy⟩ ^ 3 := Subtype.ext (by simp)
    rw [e, map_pow, hρy, hz3]
  obtain ⟨a₀, ha₀, hK₀⟩ := exists_mem_inf_of_fixed hAF hAW hAK hWK hK hy hfix hy3
  refine ⟨a₀, ha₀, ?_⟩
  have hmem : a₀ * y⁻¹ ∈ W := W.mul_mem ha₀.2 (W.inv_mem hy)
  have h1 := (rho_eq_one_iff φ autE hautE hWK _ hmem).mpr hK₀
  have e : (⟨a₀ * y⁻¹, mem_nWK hWK hmem⟩ : ↥(nWK W K)) =
      ⟨a₀, mem_nWK hWK ha₀.2⟩ * ⟨y, mem_nWK hWK hy⟩⁻¹ := Subtype.ext rfl
  rw [e, map_mul, map_inv, hρy, mul_inv_eq_one] at h1
  exact h1

end PermLift

theorem nonempty_quot_equiv_img148 {A M W : Subgroup G} [(ker148 A M).Normal]
    (hWM : W ≤ M) [((pPrimeCoreOf 3 M).subgroupOf W).Normal] :
    Nonempty (↥W ⧸ (pPrimeCoreOf 3 M).subgroupOf W ≃* ↥(img148 A M W)) := by
  let ψ : ↥W →* ↥(M ⊔ A) ⧸ ker148 A M :=
    (QuotientGroup.mk' (ker148 A M)).comp (Subgroup.inclusion (hWM.trans le_sup_left))
  have hrange : ψ.range = img148 A M W := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hker : ψ.ker = (pPrimeCoreOf 3 M).subgroupOf W := by
    ext w
    rw [MonoidHom.mem_ker]
    change QuotientGroup.mk' (ker148 A M)
      (Subgroup.inclusion (hWM.trans le_sup_left) w) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ker148, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange ψ).trans (MulEquiv.subgroupCongr hrange))⟩

end CFSG.RankThree.PartTwo.Sec15.Sylow155R
