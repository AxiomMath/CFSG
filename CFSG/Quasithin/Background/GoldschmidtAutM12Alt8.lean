module

public import CFSG.Quasithin.Background.GoldschmidtAutM12DataS8
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.Quasithin.F6

open CFSG.Assembly CFSG.Assembly.LowTwoRank

namespace AutM12Recog

theorem eq_sylow_of_card_perm_eight {H : Subgroup (Equiv.Perm (Fin 8))} (hH : IsPGroup 2 H)
    (hc : Nat.card H = 2 ^ 7) : ∃ P : Sylow 2 (Equiv.Perm (Fin 8)), (P : Subgroup _) = H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hH.exists_le_sylow
  refine ⟨P, (Subgroup.eq_of_le_of_card_ge hP ?_).symm⟩
  obtain ⟨m, hm⟩ := P.isPGroup'.exists_card_eq
  have hdvd : Nat.card (P : Subgroup (Equiv.Perm (Fin 8))) ∣ Nat.card (Equiv.Perm (Fin 8)) :=
    Subgroup.card_subgroup_dvd_card _
  have h8 : Nat.card (Equiv.Perm (Fin 8)) = 2 ^ 7 * 315 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  rw [hm, h8] at hdvd
  have h2 : 2 ^ m ∣ 2 ^ 7 :=
    (Nat.Coprime.pow_left m (by norm_num : Nat.Coprime 2 315)).dvd_of_dvd_mul_right hdvd
  have hm7 : m ≤ 7 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h2
  rw [hc, hm]
  exact Nat.pow_le_pow_right (by norm_num) hm7

variable {D : Type} [Group D] [Finite D]

theorem eq_one_of_conjQuotHom_eq_one (hS : F618RecogSetting D) {x : D}
    (hx2 : ∃ j : ℕ, x ^ 2 ^ j = 1) (hx : conjQuotHom D x = 1) : x = 1 := by
  have := twoResidual_top_normal (D := D)
  have hxker : x ∈ (conjQuotHom D).ker := hx
  rw [ker_conjQuotHom hS] at hxker
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hxker
  obtain ⟨k, hk⟩ := hS.center ⟨z, hz⟩
  obtain ⟨j, hj⟩ := hx2
  have h3 : (z : D) ^ 3 ^ k = 1 := by
    have := congrArg (fun y : ↥(Subgroup.center ↥(twoResidual (⊤ : Subgroup D))) =>
      ((y : ↥(twoResidual (⊤ : Subgroup D))) : D)) hk
    simpa using this
  have h1 : orderOf ((z : ↥(twoResidual (⊤ : Subgroup D))) : D) ∣ 2 ^ j :=
    orderOf_dvd_of_pow_eq_one hj
  have h2 : orderOf ((z : ↥(twoResidual (⊤ : Subgroup D))) : D) ∣ 3 ^ k :=
    orderOf_dvd_of_pow_eq_one h3
  have hcop : Nat.Coprime (2 ^ j) (3 ^ k) :=
    Nat.Coprime.pow _ _ (by norm_num)
  have : orderOf ((z : ↥(twoResidual (⊤ : Subgroup D))) : D) = 1 :=
    Nat.eq_one_of_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h2)
  exact orderOf_eq_one_iff.mp this

theorem false_of_alt8 (hS : F618RecogSetting D) {T : Type} [Group T] (hT : TProps T)
    (S : Sylow 2 D) (eT : ↥(S : Subgroup D) ≃* T)
    (e : TwoResidualQuot D ≃* alternatingGroup (Fin 8)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ψ : MulAut (TwoResidualQuot D) ≃* Equiv.Perm (Fin 8) :=
    (MulAut.congr e).trans (MulEquiv.ofBijective
      (MulAut.conjNormal (H := alternatingGroup (Fin 8)))
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8 (by norm_num)
        (by norm_num))).symm
  let g : ↥(S : Subgroup D) →* Equiv.Perm (Fin 8) :=
    ψ.toMonoidHom.comp ((conjQuotHom D).comp (S : Subgroup D).subtype)
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : conjQuotHom D (x : D) = 1 := by
      have : ψ (conjQuotHom D (x : D)) = 1 := hx
      exact ψ.injective (by rw [this, map_one])
    have h2 : ∃ j : ℕ, (x : D) ^ 2 ^ j = 1 := by
      obtain ⟨j, hj⟩ := S.isPGroup' x
      exact ⟨j, by simpa using congrArg Subtype.val hj⟩
    exact Subtype.ext (eq_one_of_conjQuotHom_eq_one hS h2 hx')
  have hrange2 : IsPGroup 2 g.range :=
    S.isPGroup'.of_surjective g.rangeRestrict g.rangeRestrict_surjective
  have hrangec : Nat.card g.range = 2 ^ 7 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hg).toEquiv, Nat.card_congr eT.toEquiv, hT.card]
  obtain ⟨P, hP⟩ := eq_sylow_of_card_perm_eight hrange2 hrangec
  have h16 := Tab.S8Cert.hasTwoE16_perm8 P
  let φ : ↥(P : Subgroup (Equiv.Perm (Fin 8))) ≃* T :=
    ((MulEquiv.subgroupCongr hP).trans (MonoidHom.ofInjective hg).symm).trans eT
  exact hT.not_hasTwoE16 φ.toMonoidHom φ.injective h16

end AutM12Recog

end CFSG.Quasithin.F6
