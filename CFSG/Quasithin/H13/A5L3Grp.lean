module

public import CFSG.Quasithin.H13.A5Facts1321
public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationL32Proof
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328Iso

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.Quasithin.A10

@[expose] def sqC (c : ℕ) : ℕ := L32Tab.cmpN c c

@[expose] def pow16C (c : ℕ) : ℕ := sqC (sqC (sqC (sqC c)))

theorem Dc_inv_cent : ∀ d ∈ L32Tab.Dc, L32Tab.cmpN d d = L32Tab.idC → d ≠ L32Tab.idC →
    8 ≤ (L32Tab.Lc.filter (L32Tab.commB d)).length →
    ∀ x ∈ L32Tab.Dc, L32Tab.commB d x = true → pow16C x = L32Tab.idC := by
  decide +kernel

theorem code_pow16 (σ : Equiv.Perm (Omega (ZMod 7))) :
    L32Proof.code (σ ^ 16) = pow16C (L32Proof.code σ) := by
  have h16 : σ ^ 16 = (((σ ^ 2) ^ 2) ^ 2) ^ 2 := by rw [← pow_mul, ← pow_mul, ← pow_mul]
  rw [h16]
  simp only [pow_two]
  simp only [L32Proof.code_mul, pow16C, sqC]

theorem eq_bot_of_pow16 {X : Type*} [Group X] {Y : Subgroup X} (hY : Y = oTwoRes Y)
    (h16 : ∀ y ∈ Y, y ^ 16 = 1) : Y = ⊥ := by
  rw [hY, oTwoRes, eq_bot_iff, Subgroup.closure_le]
  rintro x ⟨hx, m, hm, hxm⟩
  have h1 : orderOf x ∣ Nat.gcd m 16 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hxm) (orderOf_dvd_of_pow_eq_one (h16 x hx))
  have h2 : Nat.gcd m 16 = 1 := by
    have : Nat.Coprime m 2 := Nat.coprime_two_right.mpr hm
    exact Nat.Coprime.pow_right 4 this
  rw [h2, Nat.dvd_one, orderOf_eq_one_iff] at h1
  exact h1

theorem card_sl3_two : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  rw [Nat.card_congr (MulEquiv.ofBijective _
    CFSG.LocalAnalysis.ComponentInitial.bijective_toGL_three_zmod_two).toEquiv,
    Matrix.card_GL_field, ZMod.card, Fin.prod_univ_three]
  norm_num

theorem card_sylow_two_of_card {X : Type*} [Group X] [Finite X] (hX : Nat.card X = 168)
    (S : Sylow 2 X) : Nat.card S = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp S.isPGroup')
  have hidx := (S : Subgroup X).card_mul_index
  rw [hk, hX] at hidx
  have hodd := S.not_dvd_index
  have hk8 : k < 8 := by
    by_contra h
    have : 2 ^ 8 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpos : 0 < (S : Subgroup X).index := Nat.pos_of_ne_zero (by
      intro h0; rw [h0] at hidx; omega)
    have : 2 ^ k ≤ 168 := by
      calc 2 ^ k ≤ 2 ^ k * (S : Subgroup X).index := Nat.le_mul_of_pos_right _ hpos
        _ = 168 := hidx
    omega
  rw [hk]
  interval_cases k <;> omega

theorem factL3Grp1321 : FactL3Grp1321 := by
  intro K _ _ hK ⟨F, _, _, hF2, π, hπ⟩ v hv1 hv2 ⟨S, hS⟩ Y hYc hY
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    isSimpleGroup_sl_zmodTwo (by norm_num)
  let ε : ↥(StatedSL 3 F) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    statedSLEquivZModTwo hF2
  have : IsSimpleGroup ↥(StatedSL 3 F) := ε.isSimpleGroup
  have hinj : Function.Injective π := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff π).1 h
    · exfalso
      obtain ⟨a, ha⟩ := exists_ne (1 : K)
      obtain ⟨g, rfl⟩ := hπ a
      exact ha (MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top g))
  let e0 : ↥(StatedSL 3 F) ≃* K := MulEquiv.ofBijective π ⟨hinj, hπ⟩
  let e₂ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq
      CFSG.LocalAnalysis.ComponentInitial.center_SL_three_zmod_two_eq_bot).trans
      QuotientGroup.quotientBot
  obtain ⟨θ⟩ := L32Proof.nonempty_equiv_coordinateG K ⟨e0.symm.trans (ε.trans e₂.symm)⟩
  have hcardK : Nat.card K = 168 := by
    rw [Nat.card_congr (e0.symm.trans ε).toEquiv, card_sl3_two]
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  let Ψ : MulAut K ≃* coordinateE (ZMod 7) :=
    (MulAut.congr θ).trans (coordinateConjugationEquiv (ZMod 7)).symm
  have hΨ : ∀ (α : MulAut K) (k : K), ((θ (α k) : coordinateG (ZMod 7)) :
      Equiv.Perm (Omega (ZMod 7))) = ((Ψ α : coordinateE (ZMod 7)) : Equiv.Perm (Omega (ZMod 7))) *
        ((θ k : coordinateG (ZMod 7)) : Equiv.Perm (Omega (ZMod 7))) *
          ((Ψ α : coordinateE (ZMod 7)) : Equiv.Perm (Omega (ZMod 7)))⁻¹ := by
    intro α k
    have h1 : coordinateConjugation (ZMod 7) (Ψ α) = MulAut.congr θ α :=
      (coordinateConjugationEquiv (ZMod 7)).apply_symm_apply (MulAut.congr θ α)
    rw [← coordinateConjugation_apply_coe, h1]
    show ((θ (α k) : coordinateG (ZMod 7)) : Equiv.Perm (Omega (ZMod 7))) =
      ((θ (α (θ.symm (θ k))) : coordinateG (ZMod 7)) : Equiv.Perm (Omega (ZMod 7)))
    rw [MulEquiv.symm_apply_apply]
  set d := L32Proof.code ((Ψ v : coordinateE (ZMod 7)) : Equiv.Perm (Omega (ZMod 7))) with hd
  have hdD : d ∈ L32Tab.Dc := L32Proof.coordinateE_code _ (Ψ v).2
  have hdd : L32Tab.cmpN d d = L32Tab.idC := by
    have h1 : ((Ψ v : coordinateE (ZMod 7)) : Equiv.Perm (Omega (ZMod 7))) *
        ((Ψ v : coordinateE (ZMod 7)) : Equiv.Perm (Omega (ZMod 7))) = 1 := by
      rw [← Subgroup.coe_mul, ← map_mul, hv2, map_one, Subgroup.coe_one]
    rw [hd, ← L32Proof.code_mul, h1, L32Proof.code_one]
  have hd1 : d ≠ L32Tab.idC := by
    intro h
    apply hv1
    have h1 : ((Ψ v : coordinateE (ZMod 7)) : Equiv.Perm (Omega (ZMod 7))) = 1 :=
      L32Proof.code_injective (h.trans L32Proof.code_one.symm)
    have h2 : Ψ v = 1 := Subtype.ext h1
    rw [← map_one Ψ] at h2
    exact Ψ.injective h2
  have hcomm : ∀ s : S, ((Ψ v : coordinateE (ZMod 7)) : Equiv.Perm (Omega (ZMod 7))) *
      ((θ (s : K) : coordinateG (ZMod 7)) : Equiv.Perm (Omega (ZMod 7))) =
        ((θ (s : K) : coordinateG (ZMod 7)) : Equiv.Perm (Omega (ZMod 7))) *
          ((Ψ v : coordinateE (ZMod 7)) : Equiv.Perm (Omega (ZMod 7))) := by
    intro s
    have h1 := hΨ v (s : K)
    rw [hS (s : K) s.2] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1.symm)
  have h8 : 8 ≤ (L32Tab.Lc.filter (L32Tab.commB d)).length := by
    let f : S → ℕ := fun s => L32Proof.code ((θ (s : K) : coordinateG (ZMod 7)) :
      Equiv.Perm (Omega (ZMod 7)))
    have hf_mem : ∀ s : S, f s ∈ L32Tab.Lc.filter (L32Tab.commB d) := by
      intro s
      rw [List.mem_filter]
      exact ⟨L32Proof.coordinateG_code _ (θ (s : K)).2, L32Proof.commB_code (hcomm s)⟩
    have hf_inj : Function.Injective f := by
      intro s s' h
      exact Subtype.ext (θ.injective (Subtype.ext (L32Proof.code_injective h)))
    have h1 : Nat.card S ≤ Nat.card ((L32Tab.Lc.filter (L32Tab.commB d)).toFinset) :=
      Nat.card_le_card_of_injective
        (fun s => ⟨f s, List.mem_toFinset.2 (hf_mem s)⟩)
        (fun s s' h => hf_inj (congrArg Subtype.val h))
    rw [Nat.card_eq_finsetCard, card_sylow_two_of_card hcardK S] at h1
    exact h1.trans (List.toFinset_card_le _)
  refine eq_bot_of_pow16 hY fun y hy => ?_
  have hyv : y * v = v * y := Subgroup.mem_centralizer_singleton_iff.mp (hYc hy)
  have hc : ((Ψ v : coordinateE (ZMod 7)) : Equiv.Perm (Omega (ZMod 7))) *
      ((Ψ y : coordinateE (ZMod 7)) : Equiv.Perm (Omega (ZMod 7))) =
        ((Ψ y : coordinateE (ZMod 7)) : Equiv.Perm (Omega (ZMod 7))) *
          ((Ψ v : coordinateE (ZMod 7)) : Equiv.Perm (Omega (ZMod 7))) := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hyv]
  have h16 := Dc_inv_cent d hdD hdd hd1 h8 _ (L32Proof.coordinateE_code _ (Ψ y).2)
    (L32Proof.commB_code hc)
  rw [← code_pow16, ← L32Proof.code_one] at h16
  have h1 := L32Proof.code_injective h16
  have h2 : Ψ (y ^ 16) = 1 := by
    rw [map_pow]
    exact Subtype.ext (by rw [Subgroup.coe_pow, h1, Subgroup.coe_one])
  rw [← map_one Ψ] at h2
  exact Ψ.injective h2

end CFSG.Quasithin.H13.A5
