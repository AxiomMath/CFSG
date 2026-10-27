module

public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUDvdLeaf
public import CFSG.LocalAnalysis.StandardType.GGK1ADvd
import all CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPSU

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.ClassicalPosition

section BlockField

theorem blockDegree_le_one_of_forall_mul_eq_smul {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] {S : Set (GL ι F)} {e : Matrix ι ι F}
    (h : ∀ s ∈ S, ∃ c : F, (s : Matrix ι ι F) * e = c • e) :
    blockDegree (Algebra.adjoin F (Units.val '' S)) e ≤ 1 := by
  have key : ∀ x : Matrix ι ι F, x ∈ Algebra.adjoin F (Units.val '' S) →
      ∃ c : F, x * e = c • e := by
    intro x hx
    refine Algebra.adjoin_induction
      (p := fun x _ => ∃ c : F, x * e = c • e) ?_ ?_ ?_ ?_ hx
    · rintro x ⟨s, hs, rfl⟩
      exact h s hs
    · intro r
      exact ⟨r, by rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]⟩
    · rintro x y hx hy ⟨c1, h1⟩ ⟨c2, h2⟩
      exact ⟨c1 + c2, by rw [add_mul, h1, h2, add_smul]⟩
    · rintro x y hx hy ⟨c1, h1⟩ ⟨c2, h2⟩
      exact ⟨c2 * c1, by rw [mul_assoc, h2, Matrix.mul_smul, h1, smul_smul]⟩
  have hle : (Subalgebra.toSubmodule (Algebra.adjoin F (Units.val '' S))).map
      (LinearMap.mulRight F e) ≤ Submodule.span F {e} := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨c, hc⟩ := key a ha
    rw [LinearMap.mulRight_apply]
    exact Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩
  unfold blockDegree
  refine (Submodule.finrank_mono hle).trans ?_
  by_cases he : e = 0
  · subst he
    rw [Submodule.span_zero_singleton, finrank_bot]
    exact Nat.zero_le 1
  · exact (finrank_span_singleton (K := F) he).le

theorem dvd_card_pow_blockDegree_of_pow_eq_one {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] [Finite F] [CharP F 2] {p : ℕ} (hp : p.Prime) {S : Set (GL ι F)}
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix ι ι F} (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    {t : Matrix ι ι F} (htA : t ∈ Algebra.adjoin F (Units.val '' S)) (htp : t ^ p = 1)
    (hte : t * e ≠ e) :
    p ∣ Nat.card F ^ blockDegree (Algebra.adjoin F (Units.val '' S)) e - 1 := by
  obtain ⟨K, instF, instA, instFin, π, _hsurj, hker, hdeg⟩ :=
    exists_blockField hS hodd he
  obtain ⟨t', ht⟩ : ∃ t' : Algebra.adjoin F (Units.val '' S),
      (t' : Matrix ι ι F) = t :=
    ⟨⟨t, htA⟩, rfl⟩
  have htp' : t' ^ p = 1 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, ht, htp, Subalgebra.coe_one]
  have hζp : π t' ^ p = 1 := by rw [← map_pow, htp', map_one]
  have hζne : π t' ≠ 1 := by
    intro h1
    have h2 : π (t' - 1) = 0 := by rw [map_sub, h1, map_one, sub_self]
    have h3 := (hker (t' - 1)).mp h2
    apply hte
    rw [Subalgebra.coe_sub, Subalgebra.coe_one, ht, sub_mul, one_mul, sub_eq_zero] at h3
    exact h3
  have hζ0 : π t' ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp.ne_zero] at hζp
    exact zero_ne_one hζp
  have : Fact p.Prime := ⟨hp⟩
  have hu_pow : (Units.mk0 (π t') hζ0) ^ p = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    exact hζp
  have hu_ne : Units.mk0 (π t') hζ0 ≠ 1 := by
    intro h
    apply hζne
    have h' := congrArg Units.val h
    rwa [Units.val_mk0, Units.val_one] at h'
  have hord : orderOf (Units.mk0 (π t') hζ0) = p := orderOf_eq_prime hu_pow hu_ne
  have hdvd : p ∣ Nat.card (Units K) := by
    have h := orderOf_dvd_natCard (Units.mk0 (π t') hζ0)
    rwa [hord] at h
  have : Module.Finite F K := Module.Finite.of_finite
  have hcard : Nat.card K =
      Nat.card F ^ blockDegree (Algebra.adjoin F (Units.val '' S)) e := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := K), hdeg]
  rw [Nat.card_units, hcard] at hdvd
  exact hdvd

end BlockField

section Lifts

theorem PSULiftHyp.exists_lam_mul_ne_of_two_le {X : Type} [Group X] [Finite X] {n g p : ℕ}
    {ψ : ↥(Unitary.SU (PSUσ g) n) →* X} {B : Subgroup X} (hH : PSULiftHyp n g ψ p B)
    (hpq : ¬ p ∣ 2 ^ (g + 1) + 1) {S : Set (GL (Fin n) (PSUF g))}
    {e : Matrix (Fin n) (Fin n) (PSUF g)} {D : Subgroup X} (hDB : D ≤ B)
    (hSD : ∀ s ∈ S, ∃ d ∈ D, IsGLLift (PSUj n g) ψ s d)
    (hd : 2 ≤ blockDegree (Algebra.adjoin (PSUF g) (Units.val '' S)) e) :
    ∃ (y : X) (hy : y ∈ D), ((hH.lam hpq ⟨y, hDB hy⟩ : GL (Fin n) (PSUF g)) :
      Matrix (Fin n) (Fin n) (PSUF g)) * e ≠ e := by
  by_contra hcon
  have hfix : ∀ (y : X) (hy : y ∈ D),
      ((hH.lam hpq ⟨y, hDB hy⟩ : GL (Fin n) (PSUF g)) :
        Matrix (Fin n) (Fin n) (PSUF g)) * e = e := by
    intro y hy
    by_contra h
    exact hcon ⟨y, hy, h⟩
  have hsmul : ∀ s ∈ S, ∃ c : PSUF g, (s : Matrix (Fin n) (Fin n) (PSUF g)) * e = c • e := by
    intro s hs
    obtain ⟨d, hdD, hl⟩ := hSD s hs
    have hl' : IsGLLift (PSUj n g) ψ (hH.lam hpq ⟨d, hDB hdD⟩ : GL (Fin n) (PSUF g)) d :=
      (hH.lam_spec hpq (hDB hdD)).2.1
    obtain ⟨c, hc⟩ := isGLLift_unique_PSU (card_PSUF g) n ψ hH.ker hl hl'
    refine ⟨c, ?_⟩
    have hs_eq : (s : Matrix (Fin n) (Fin n) (PSUF g)) =
        ((hH.lam hpq ⟨d, hDB hdD⟩ : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) *
          (((hH.lam hpq ⟨d, hDB hdD⟩ : GL (Fin n) (PSUF g))⁻¹ * s : GL (Fin n) (PSUF g)) :
            Matrix (Fin n) (Fin n) (PSUF g)) := by
      rw [← Units.val_mul, mul_inv_cancel_left]
    have hsc : Matrix.scalar (Fin n) c * e = c • e := by
      rw [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
    rw [hs_eq, Matrix.mul_assoc, hc, hsc, Matrix.mul_smul, hfix d hdD]
  have hle := blockDegree_le_one_of_forall_mul_eq_smul (S := S) (e := e) hsmul
  omega

end Lifts

section Assembly

theorem dvd_card_of_mulEquiv_quotient_center {G Q : Type} [Group G] [Group Q] {p : ℕ}
    (φ : G ⧸ Subgroup.center G ≃* Q) (hp : p ∣ Nat.card Q) : p ∣ Nat.card G := by
  rw [← Nat.card_congr φ.toEquiv] at hp
  exact hp.trans (Subgroup.card_quotient_dvd_card _)

private theorem charP_two_of_card_eq_pow_pow {K : Type} [Field K] [Finite K] {f d : ℕ}
    (hf : f ≠ 0) (hd : d ≠ 0) (hK : Nat.card K = (2 ^ f) ^ d) : CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  refine ringChar.of_eq (FiniteField.even_card_iff_char_two.mpr ?_)
  rw [← Nat.card_eq_fintype_card, hK]
  exact Nat.even_iff.mp (Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, hf⟩, hd⟩)

theorem dvd_card_J_PSU
    {X : Type} [Group X] [Finite X] {n p g : ℕ} {G₀ B D J L : Subgroup X} {x : X}
    {ψ : (ggU .PSU n (g + 1)).K →* X} (h : GGTCHyp .PSU n (g + 1) ψ p G₀ B D J L x)
    (hF : GGSixLSevenFieldExtCase J .PSU (g + 1)) (hp : ¬ p ∣ 2 ^ (g + 1) + 1) :
    p ∣ Nat.card J := by
  classical
  have hH := PSULiftHyp.of_ggTCHyp h
  have hJ : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (D : Set X)) := by
    rw [h.range]
    exact h.j_comp
  obtain ⟨S, ε, e, J', hS, hb, -, hJ'g, hJ'm⟩ := hH.exists_block h.d_le hJ
  have hd : 2 ≤ blockDegree (Algebra.adjoin (PSUF g) (Units.val '' S)) e := by
    by_cases hself : e = ε
    · exact hb.two_le_blockDegree_of_selfDual hH hself h.d_card h.j_cent hJ'g hJ'm hF
    · exact hb.two_le_blockDegree_of_dualPair hH hself h.d_card h.j_cent hJ'g hJ'm hF
  obtain ⟨y, hyD, hye⟩ := hH.exists_lam_mul_ne_of_two_le hp h.d_le
    (fun s hs => ((hS s).mp hs).2) hd
  have hspec := hH.lam_spec hp (h.d_le hyD)
  have hlamS : (hH.lam hp ⟨y, h.d_le hyD⟩ : GL (Fin n) (PSUF g)) ∈ S :=
    (hS _).mpr ⟨hspec.1.1, y, hyD, hspec.2.1⟩
  have hpow : ((hH.lam hp ⟨y, h.d_le hyD⟩ : GL (Fin n) (PSUF g)) :
      Matrix (Fin n) (Fin n) (PSUF g)) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hspec.2.2, Units.val_one]
  have hdvd := dvd_card_pow_blockDegree_of_pow_eq_one hH.prime (hb.S_comm hH) (hb.S_odd hH)
    hb.e_prim (Algebra.subset_adjoin ⟨_, hlamS, rfl⟩) hpow hye
  rw [card_PSUF] at hdvd
  generalize hdd : blockDegree (Algebra.adjoin (PSUF g) (Units.val '' S)) e = d at hd hdvd
  have hf0 : g + 1 ≠ 0 := by omega
  have hd0 : d ≠ 0 := by omega
  subst hJ'm
  rcases hb.cases with hself | ⟨-, hpair, hεeq⟩
  · rcases fePSU_selfDual_iso (card_PSUF g) n ψ hH.ker S (fun s hs => (hb.subE s hs).1)
      (hb.S_comm hH) (hb.S_odd hH) hb.eps_prim hJ'g hb.e_prim d hdd.symm hd hself with
      ⟨m, K, hKf, hKfin, hKcard, hm3, -, ⟨eiso⟩⟩ | ⟨K, hKf, hKfin, hKcard, ⟨eiso⟩⟩
    · have hq : (2 ^ (g + 1)) ^ d = 2 ^ ((g + 1) * d) := (pow_mul 2 (g + 1) d).symm
      rw [pow_right_comm, hq] at hdvd
      rw [hq] at hKcard eiso
      have : CharP K 2 := charP_two_of_card_eq_pow_pow (Nat.mul_ne_zero hf0 hd0) two_ne_zero hKcard
      exact dvd_card_of_mulEquiv_quotient_center eiso
        (prime_dvd_card_statedProj_statedSU hH.prime hH.ne_two (by omega) hKcard hdvd)
    · have : CharP K 2 := charP_two_of_card_eq_pow_pow hf0 hd0 hKcard
      refine dvd_card_of_mulEquiv_quotient_center eiso
        (prime_dvd_card_statedProj_statedSL hH.prime hH.ne_two le_rfl (CharP.cast_eq_zero K 2) ?_)
      rw [hKcard]
      rwa [pow_right_comm] at hdvd
  · obtain ⟨m, K, hKf, hKfin, hKcard, hm, ⟨eiso⟩⟩ := fePSU_dualPair_iso (card_PSUF g) n ψ
      hH.ker S (fun s hs => (hb.subE s hs).1) (hb.S_comm hH) (hb.S_odd hH) hb.eps_prim hJ'g
      hb.e_prim hb.ee d hdd.symm hd hpair hεeq
    have : CharP K 2 := charP_two_of_card_eq_pow_pow hf0 (Nat.mul_ne_zero two_ne_zero hd0) hKcard
    refine dvd_card_of_mulEquiv_quotient_center eiso
      (prime_dvd_card_statedProj_statedSL hH.prime hH.ne_two hm (CharP.cast_eq_zero K 2) ?_)
    have hpK : p ∣ Nat.card K - 1 := by
      rw [hKcard, pow_mul]
      exact hdvd
    exact hpK.trans (Nat.sub_one_dvd_pow_sub_one _ 2)

theorem false_of_not_dvd_PSU
    {X : Type} [Group X] [Finite X] {n f p : ℕ} {G₀ B D J L : Subgroup X} {x : X}
    {ψ : (ggU .PSU n f).K →* X} (h : GGTCHyp .PSU n f ψ p G₀ B D J L x)
    (hF : GGSixLSevenFieldExtCase J .PSU f) (hp : ¬ p ∣ 2 ^ f + 1) : False := by
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by have := h.adm.2.1; omega⟩
  exact false_of_not_dvd_PSU_of_hM2 h hF hp (dvd_card_J_PSU h hF hp)

theorem ggTCAt_PSU :
    GGTCAt .PSU := by
  intro X _ _ n f ψ p G₀ B D J L x h hF _
  by_cases hp : p ∣ 2 ^ f + 1
  · exact (false_of_dvd_PSU h hF hp).elim
  · exact (false_of_not_dvd_PSU h hF hp).elim

end Assembly

end CFSG.StandardType.TableCRes
