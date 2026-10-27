module

public import CFSG.Walter.PSL2Facts.FieldAut
import CFSG.Walter.W67.Section4.Prop43cA
import CFSG.Walter.W67.Section4.Prop43ab
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourMapInjective
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2KleinFourSelfCentralizer
public import CFSG.Walter.Cited.PSL2Small
public import CFSG.Walter.W67.Interface
import CFSG.Walter.W67.Lemma21

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups Pointwise commutatorElement
open CFSG.GorensteinWalter

theorem psl2_mulAut_eq_conj_of_centralizes_sylow_two
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (h5 : 5 ≤ p) (h8 : p % 8 = 3 ∨ p % 8 = 5) (α : MulAut PSL(2, GaloisField p 1))
    (S : Sylow 2 PSL(2, GaloisField p 1))
    (hαS : ∀ x ∈ (S : Subgroup PSL(2, GaloisField p 1)), α x = x) :
    ∃ g ∈ (S : Subgroup PSL(2, GaloisField p 1)), α = MulAut.conj g := by
  classical
  set K := GaloisField p 1
  have hK : Nat.card K = p ^ 1 := GaloisField.card p 1 one_ne_zero
  have hK1 : Nat.card K = p := by rw [hK, pow_one]
  have hK' : IsOddPrimePower (Nat.card K) := isOddPrimePower_of_card hK hp one_pos
  have hcard : 3 < Nat.card K := by omega
  have h8' : p ^ 1 % 8 = 3 ∨ p ^ 1 % 8 = 5 := by rw [pow_one]; exact h8
  obtain ⟨V0, hV0, -⟩ := exists_kleinFour_fieldAut_fixed hp h8'
  have hScard : Nat.card (S : Subgroup PSL(2, K)) = 4 :=
    psl2_sylow_two_card_eq_four K hK hp one_pos h8' S
  let V0S : Sylow 2 PSL(2, K) :=
    Sylow.ofCard V0 (by rw [hV0.card_four, ← hScard, S.card_eq_multiplicity])
  have hV0S : (V0S : Subgroup PSL(2, K)) = V0 := Sylow.coe_ofCard _ _
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq PSL(2, K) S V0S
  have hmemV0 : ∀ v, v ∈ V0 → (MulAut.conj k)⁻¹ v ∈ (S : Subgroup PSL(2, K)) := by
    intro v hv
    have hv' : v ∈ ((k • S : Sylow 2 PSL(2, K)) : Subgroup PSL(2, K)) := by
      rw [hk, hV0S]
      exact hv
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hv'
    exact hv'
  set α' := MulAut.conj k * α * (MulAut.conj k)⁻¹ with hα'
  have hα'V : ∀ v ∈ V0, α' v = v := by
    intro v hv
    have h := hαS _ (hmemV0 v hv)
    change (MulAut.conj k) (α ((MulAut.conj k)⁻¹ v)) = v
    rw [h, ← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  obtain ⟨x, hx⟩ := pGammaL2ToMulAutPSL2_surjective K hK hK' hcard α'
  set g := x.left
  set σ := x.right
  have hσ : σ = 1 := (Suzuki.subsingleton_ringEquiv_of_card_prime K hK1).elim _ _
  have hα'g : α' = pgl2InnerAutPSL2 K hK' hcard g := by
    rw [← hx, ← SemidirectProduct.inl_left_mul_inr_right x, map_mul, pGammaL2ToMulAutPSL2_inl,
      pGammaL2ToMulAutPSL2_inr]
    change pgl2InnerAutPSL2 K hK' hcard g * psl2FieldAut K σ = _
    rw [hσ, map_one, mul_one]
  let toPGL : PSL(2, K) →* PGL2 K := Matrix.ProjectiveSpecialLinearGroup.toPGL
  have htoPGL : Function.Injective toPGL := fun _ _ h =>
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective h
  have hVP : IsKleinFour (V0.map toPGL) := isKleinFour_map_of_injective V0 hV0 toPGL htoPGL
  have hgC : g ∈ Subgroup.centralizer ((V0.map toPGL : Subgroup (PGL2 K)) : Set (PGL2 K)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    have h1 : pgl2InnerAutPSL2 K hK' hcard g v = v := by
      rw [← hα'g]
      exact hα'V v hv
    have h2 := toPGL_pgl2InnerAutPSL2_apply K hK' hcard g v
    rw [h1] at h2
    calc toPGL v * g = (g * toPGL v * g⁻¹) * g := by rw [← h2]
      _ = g * toPGL v := by group
  rw [pgl2_kleinFour_centralizer_eq_self K hK' _ hVP] at hgC
  obtain ⟨g0, hg0V, hg0⟩ := hgC
  have hα'2 : α' = MulAut.conj g0 := by
    rw [hα'g, ← hg0]
    exact pgl2InnerAutPSL2_toPGL K hK' hcard g0
  refine ⟨(MulAut.conj k)⁻¹ g0, hmemV0 g0 hg0V, ?_⟩
  have hα : α = (MulAut.conj k)⁻¹ * α' * MulAut.conj k := by rw [hα']; group
  rw [hα, hα'2]
  ext y
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, MulAut.conj_symm_apply]
  group

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_conj_eq_of_normalizes
    [Fact (Nat.Prime 5)] {Q V : Subgroup G}
    (e : Q ≃* PSL(2, GaloisField 5 1))
    (hVQ : V ≤ Q) (hV4 : Nat.card V = 4) {g : G} (hgN : g ∈ Subgroup.normalizer (Q : Set G))
    (hgV : g ∈ Subgroup.centralizer (V : Set G)) :
    ∃ v ∈ V, ∀ x ∈ Q, g * x * g⁻¹ = v * x * v⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgQ : ∀ x ∈ Q, g * x * g⁻¹ ∈ Q := fun x hx => (Subgroup.mem_normalizer_iff.mp hgN x).mp hx
  have hgQ' : ∀ x ∈ Q, g⁻¹ * x * g⁻¹⁻¹ ∈ Q := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) x).mp hx
  let β : Q ≃* Q :=
    { toFun := fun x => ⟨g * x * g⁻¹, hgQ x x.2⟩
      invFun := fun x => ⟨g⁻¹ * x * g⁻¹⁻¹, hgQ' x x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  let α : MulAut PSL(2, GaloisField 5 1) := (e.symm.trans β).trans e
  set V' : Subgroup PSL(2, GaloisField 5 1) := (V.subgroupOf Q).map e.toMonoidHom
  have hV'card : Nat.card V' = 4 := by
    rw [Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVQ).toEquiv, hV4]
  have hK5 : Nat.card (GaloisField 5 1) = 5 ^ 1 := GaloisField.card 5 1 one_ne_zero
  have hfac : (Nat.card PSL(2, GaloisField 5 1)).factorization 2 = 2 := by
    rw [psl2_card_formula _ (isOddPrimePower_of_card hK5 (by decide) one_pos), hK5,
      show (5 : ℕ) ^ 1 * ((5 ^ 1) ^ 2 - 1) / 2 = 2 ^ 2 * 15 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  let S : Sylow 2 PSL(2, GaloisField 5 1) := Sylow.ofCard V' (by rw [hV'card, hfac]; norm_num)
  have hS : (S : Subgroup PSL(2, GaloisField 5 1)) = V' := Sylow.coe_ofCard _ _
  have hαS : ∀ x ∈ (S : Subgroup PSL(2, GaloisField 5 1)), α x = x := by
    intro x hx
    rw [hS] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    change e (β (e.symm (e y))) = e y
    rw [e.symm_apply_apply]
    congr 1
    apply Subtype.ext
    change g * (y : G) * g⁻¹ = y
    rw [(Subgroup.mem_centralizer_iff.mp hgV (y : G) hy).symm, mul_inv_cancel_right]
  obtain ⟨g₀, hg₀S, hα⟩ := psl2_mulAut_eq_conj_of_centralizes_sylow_two (p := 5) (by decide)
    le_rfl (by norm_num) α S hαS
  rw [hS] at hg₀S
  obtain ⟨v₀, hv₀, rfl⟩ := hg₀S
  refine ⟨v₀, hv₀, fun x hx => ?_⟩
  have h1 := congrArg (fun φ : MulAut PSL(2, GaloisField 5 1) => e.symm (φ (e ⟨x, hx⟩))) hα
  simp only [α, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply, map_mul,
    map_inv] at h1
  have h3 : e.symm (e.toMonoidHom v₀) = v₀ := e.symm_apply_apply v₀
  rw [h3] at h1
  exact congrArg Subtype.val h1

namespace Std

variable (s : Std G)

theorem commutator_H_le_K :
    ⁅s.H, s.H⁆ ≤ s.K := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨j₁, hj₁, k₁, hk₁, e₁, he₁, rfl⟩ := s.fr.exists_decomp_H hx
  obtain ⟨j₂, hj₂, k₂, hk₂, e₂, he₂, rfl⟩ := s.fr.exists_decomp_H hy
  have hjc : ∀ j ∈ Subgroup.zpowers s.J, ∀ z ∈ s.H, j * z = z * j := by
    intro j hj z hz
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hj
    exact (Commute.zpow_left (Commute.symm (s.commute_J hz)) m).eq
  have hH : ∀ {k e}, k ∈ s.K → e ∈ s.fr.E → k * e ∈ s.H := fun hk he =>
    Subgroup.mul_mem _ (s.K_le_H hk) (s.fr.E_le_H he)
  have hEK : ∀ {e k}, e ∈ s.fr.E → k ∈ s.K → e * k * e⁻¹ ∈ s.K := fun he hk =>
    s.conj_mem_K (s.fr.E_le_H he) hk
  have h1 : ⁅j₁ * k₁ * e₁, j₂ * k₂ * e₂⁆ = ⁅k₁ * e₁, k₂ * e₂⁆ := by
    have c1 := hjc j₁ hj₁ _ (hH hk₂ he₂)
    have c2 := hjc j₂ hj₂ _ (hH hk₁ he₁)
    have c3 := hjc j₁ hj₁ _ (s.J_mem_H)
    rw [commutatorElement_def, commutatorElement_def]
    calc j₁ * k₁ * e₁ * (j₂ * k₂ * e₂) * (j₁ * k₁ * e₁)⁻¹ * (j₂ * k₂ * e₂)⁻¹
        = j₁ * (k₁ * e₁ * j₂) * (k₂ * e₂) * (k₁ * e₁)⁻¹ * j₁⁻¹ * (k₂ * e₂)⁻¹ * j₂⁻¹ := by group
      _ = j₁ * (j₂ * (k₁ * e₁)) * (k₂ * e₂) * (k₁ * e₁)⁻¹ * j₁⁻¹ * (k₂ * e₂)⁻¹ * j₂⁻¹ := by
          rw [show k₁ * e₁ * j₂ = j₂ * (k₁ * e₁) from c2.symm]
      _ = j₂ * (j₁ * ((k₁ * e₁) * (k₂ * e₂) * (k₁ * e₁)⁻¹)) * j₁⁻¹ * (k₂ * e₂)⁻¹ * j₂⁻¹ := by
          have : j₁ * j₂ = j₂ * j₁ := hjc j₁ hj₁ j₂
            (Subgroup.zpowers_le.mpr s.J_mem_H hj₂)
          calc j₁ * (j₂ * (k₁ * e₁)) * (k₂ * e₂) * (k₁ * e₁)⁻¹ * j₁⁻¹ * (k₂ * e₂)⁻¹ * j₂⁻¹
              = (j₁ * j₂) * ((k₁ * e₁) * (k₂ * e₂) * (k₁ * e₁)⁻¹) * j₁⁻¹ * (k₂ * e₂)⁻¹ *
                  j₂⁻¹ := by group
            _ = (j₂ * j₁) * ((k₁ * e₁) * (k₂ * e₂) * (k₁ * e₁)⁻¹) * j₁⁻¹ * (k₂ * e₂)⁻¹ *
                  j₂⁻¹ := by rw [this]
            _ = _ := by group
      _ = j₂ * (((k₁ * e₁) * (k₂ * e₂) * (k₁ * e₁)⁻¹) * j₁) * j₁⁻¹ * (k₂ * e₂)⁻¹ * j₂⁻¹ := by
          rw [hjc j₁ hj₁ _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hH hk₁ he₁) (hH hk₂ he₂))
            (Subgroup.inv_mem _ (hH hk₁ he₁)))]
      _ = j₂ * (((k₁ * e₁) * (k₂ * e₂) * (k₁ * e₁)⁻¹) * (k₂ * e₂)⁻¹) * j₂⁻¹ := by group
      _ = (((k₁ * e₁) * (k₂ * e₂) * (k₁ * e₁)⁻¹) * (k₂ * e₂)⁻¹) * j₂ * j₂⁻¹ := by
          rw [hjc j₂ hj₂ _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
            (hH hk₁ he₁) (hH hk₂ he₂)) (Subgroup.inv_mem _ (hH hk₁ he₁)))
            (Subgroup.inv_mem _ (hH hk₂ he₂)))]
      _ = k₁ * e₁ * (k₂ * e₂) * (k₁ * e₁)⁻¹ * (k₂ * e₂)⁻¹ := by group
  rw [h1, commutatorElement_def]
  have hee : e₁ * e₂ = e₂ * e₁ := s.E_comm he₁ he₂
  have e : k₁ * e₁ * (k₂ * e₂) * (k₁ * e₁)⁻¹ * (k₂ * e₂)⁻¹ =
      k₁ * (e₁ * k₂ * e₁⁻¹) * (e₁ * e₂ * e₁⁻¹ * e₂⁻¹) * (e₂ * k₁⁻¹ * e₂⁻¹) * k₂⁻¹ := by group
  rw [e, show e₁ * e₂ * e₁⁻¹ * e₂⁻¹ = 1 by rw [hee]; group, mul_one]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hk₁ (hEK he₁ hk₂))
    (hEK he₂ (Subgroup.inv_mem _ hk₁))) (Subgroup.inv_mem _ hk₂)

theorem odd_f (hp : s.p = 3) : Odd s.f := by
  have h8 := s.mod_eight
  rw [Hyp.q, hp] at h8
  by_contra hf
  obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.mp hf
  rw [hk, ← two_mul, pow_mul, Nat.pow_mod] at h8
  norm_num at h8

theorem not_five_dvd_card_K (hp : s.p = 3) : ¬ 5 ∣ Nat.card s.K := by
  have hK := PSL2Sub.card_eq s.iso s.odd_p s.f_pos
  rw [hK, hp]
  obtain ⟨k, hk⟩ := s.odd_f hp
  intro h5
  have h2 : 2 ∣ 3 ^ s.f * ((3 ^ s.f) ^ 2 - 1) := by
    have : Even ((3 ^ s.f) ^ 2 - 1) := by
      rw [Nat.even_sub (Nat.one_le_pow _ _ (by positivity))]
      simp [Nat.even_pow, show ¬ Even 3 by decide]
    exact (even_iff_two_dvd.mp this).mul_left _
  have h5' : 5 ∣ 3 ^ s.f * ((3 ^ s.f) ^ 2 - 1) :=
    h5.trans (Nat.div_dvd_of_dvd h2)
  rcases (Nat.Prime.dvd_mul (by norm_num)).mp h5' with h | h
  · exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) h) (by norm_num)
  · rw [← pow_mul, hk] at h
    have hmod : (3 : ℕ) ^ ((2 * k + 1) * 2) % 5 = 4 := by
      rw [show (2 * k + 1) * 2 = 2 * (2 * k) + 2 by ring, pow_add, pow_mul, pow_mul,
        Nat.mul_mod, Nat.pow_mod]
      norm_num
    have h1 : 1 ≤ (3 : ℕ) ^ ((2 * k + 1) * 2) := Nat.one_le_pow _ _ (by norm_num)
    omega

end Std

end CFSG.Walter.W67
