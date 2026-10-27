module

public import CFSG.LocalAnalysis.StandardType.GGL45TGLift
public import CFSG.LocalAnalysis.StandardType.GGL45TGSU
public import CFSG.LocalAnalysis.StandardType.GGL45TGSUFrame

public section

namespace CFSG.StandardType.GGL45TG

open CFSG CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.ComponentInitial Matrix
open GGL45TA (diagGL exists_frobPow_of_dvd)

variable {n d : ℕ} {k : Type} [Field k]

@[expose] noncomputable def suData (h : UnitaryFieldData 2 n k) (hd : 3 ≤ d) (hn : 2 ≤ n) :
    GData d k where
  H := LargeEvenSUGroup (Fin d) k (2 ^ n)
  A := SU.CU h d
  le_A g hg := (SU.mem_cu_iff h).mpr ⟨1, by rw [one_smul]; exact ((SU.mem_su_iff h).mp hg).1⟩
  perf := SU.commutator_su h hd hn
  cent := SU.mem_scalars_of_commute_su h hd
  det_one g hg := ((SU.mem_su_iff h).mp hg).2
  map_mem σ g hg := SU.map_mem_su h σ hg
  conj_mem x hx g hg := SU.conj_mem_su h hx hg
  scalar_mem c := SU.scalar_mem_cu h c
  map_memA σ x hx := SU.map_mem_cu h σ hx

theorem pow_card_eq_one_of_mem_field_su (h : UnitaryFieldData 2 n k)
    {f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) k (2 ^ n)))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) k (2 ^ n)))) :
    f ^ Nat.card (k ≃+* k) = 1 := by
  obtain ⟨σ, hσ⟩ := hf
  have hg := YS09Field.graph_pow (S := k ≃+* k) (LargeEvenSUGroup (Fin d) k (2 ^ n))
    (LargeEvenProjMk _) (fun τ g => Matrix.GeneralLinearGroup.map τ.toRingHom g)
    YS09Field.glMap_one YS09Field.glMap_mul (fun τ g => SU.map_mem_su h τ g.2)
    (fun τ g g' => ((g' : GL (Fin d) k) : Matrix (Fin d) (Fin d) k) =
      ((g : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).map τ.toRingHom)
    (fun τ g g' => by rw [Units.ext_iff, YS09Field.coe_glMap]) σ f hσ (Nat.card (k ≃+* k))
  rw [pow_card_eq_one'] at hg
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ x
  rw [MulAut.one_apply]
  exact hg y y (by ext i j; rfl)

private theorem dvd_Q₀_sub_one {p n : ℕ} (hp : p.Prime) (hpn : p ∣ n)
    (hq : (p : ℤ) ∣ 2 ^ n + 1) : (p : ℤ) ∣ ((2 ^ (2 * n / p) : ℕ) : ℤ) - 1 := by
  haveI := Fact.mk hp
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hq ⊢
  push_cast at hq ⊢
  obtain ⟨m, rfl⟩ := hpn
  have h2 : 2 * (p * m) / p = 2 * m := by rw [mul_left_comm, Nat.mul_div_cancel_left _ hp.pos]
  rw [h2]
  have h1 : ((2 : ZMod p) ^ m) ^ p = (2 : ZMod p) ^ m := ZMod.pow_card _
  rw [← pow_mul] at h1
  rw [mul_comm p m, h1] at hq
  have h3 : (2 : ZMod p) ^ m = -1 := eq_neg_of_add_eq_zero_left hq
  rw [mul_comm 2 m, pow_mul, h3]
  norm_num

private theorem inducedAut_eq_of_induces' {K : Type} [Group K] {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) {ψ : MulAut K} {φ : MulAut R}
    (h : LargeEvenInduces θ (fun k k' => k' = ψ k) φ) : φ = ggInducedAut θ ψ := by
  ext r
  obtain ⟨q, rfl⟩ := θ.surjective r
  induction q using QuotientGroup.induction_on with
  | H l =>
    rw [ggInducedAut_apply]
    exact h l (ψ l) rfl

theorem ggL45H4Raw_unitary [Finite k] (hn : 1 ≤ n) (hk : Nat.card k = (2 ^ n) ^ 2) (hd : 3 ≤ d)
    (hq : ¬(d = 3 ∧ 2 ^ n = 2)) {p : ℕ} (hp : p.Prime) (lab : LargeEvenLabel) :
    GGL45H4Raw p lab (LargeEvenProj (LargeEvenSUGroup (Fin d) k (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) k (2 ^ n)))
        (LargeEvenGUSet (Fin d) k (2 ^ n)))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) k (2 ^ n)))) := by
  have hu : UnitaryFieldData 2 n k := unitaryFieldData_of_card hn hk
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdq : (d, 2 ^ n) ≠ (3, 2) := fun h3 => hq ⟨congrArg Prod.fst h3, congrArg Prod.snd h3⟩
  exact ggL45H4Raw_of_aut hp
    (fun _ => CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU k 2 n hk d hd hdq)
    (ggL45NtAut_of_inputs hp (RecipeFieldSU.ggRawInnField_unitary hu hk hd hq hp.ne_one)
      (fun _ _ => InndiagSU.ggInndiagNormal_unitary hn hk hd hq)
      (RecipeFieldSU.ggRawPCyclic_unitary hu hk hd hq))

private theorem dvd_two_pow_div_add_one {p n : ℕ} (hp : p.Prime) (hpn : p ∣ n)
    (hq : (p : ℤ) ∣ 2 ^ n + 1) : (p : ℤ) ∣ 2 ^ (n / p) + 1 := by
  haveI := Fact.mk hp
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hq ⊢
  push_cast at hq ⊢
  obtain ⟨m, rfl⟩ := hpn
  rw [Nat.mul_div_cancel_left _ hp.pos]
  have h1 : ((2 : ZMod p) ^ m) ^ p = (2 : ZMod p) ^ m := ZMod.pow_card _
  rw [← pow_mul, mul_comm m p] at h1
  rw [h1] at hq
  exact hq

theorem ggL45TorusHRaw_unitary_case2
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (htag : lab.tag = .twA) (hrank : lab.rank + 1 = d) (hpd : p ∣ d)
    (hq : (p : ℤ) ∣ 2 ^ lab.n + 1) [Finite k] (hk : Nat.card k = (2 ^ lab.n) ^ 2) :
    GGL45TorusHRaw p lab (LargeEvenProj (LargeEvenSUGroup (Fin d) k (2 ^ lab.n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) k (2 ^ lab.n)))
        (LargeEvenGUSet (Fin d) k (2 ^ lab.n)))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) k (2 ^ lab.n)))) := by
  intro K _ _ θ hK hA2 ψ E hyp
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hd3 : 3 ≤ d := hp3.trans (Nat.le_of_dvd (by omega) hpd)
  have hd1 : 1 ≤ d := by omega
  have hn1 : 1 ≤ lab.n := by
    by_contra h0
    have h1 := Finite.one_lt_card (α := k)
    rw [hk, show lab.n = 0 by omega] at h1
    norm_num at h1
  have hu : UnitaryFieldData 2 lab.n k := unitaryFieldData_of_card hn1 hk
  have hk2 : Nat.card k = 2 ^ (2 * lab.n) := by rw [hk, ← pow_mul, mul_comm]
  obtain ⟨f, hf, u, hu', hford, hind⟩ := hyp.2.1
  have hψbar : ggInducedAut θ ψ = u * f * u⁻¹ := (inducedAut_eq_of_induces' θ hind).symm
  have hpn : p ∣ lab.n := by
    obtain ⟨hcard, -⟩ := card_ringAut_and_isCyclic Nat.prime_two k hk2
    have h1 := orderOf_dvd_of_pow_eq_one (pow_card_eq_one_of_mem_field_su hu hf)
    rw [hford, show Nat.card (k ≃+* k) = 2 * lab.n from hcard] at h1
    rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
    · exact absurd (Nat.le_of_dvd (by norm_num) h2) (by omega)
    · exact h2
  have hn3 : 3 ≤ lab.n := hp3.trans (Nat.le_of_dvd (by omega) hpn)
  have hn2 : 2 ≤ lab.n := by omega
  let D : GData d k := suData hu hd3 hn2
  have hdq : ¬(d = 3 ∧ 2 ^ lab.n = 2) := fun h => by
    have : 2 ^ 2 ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  have hH4 := ggL45H4Raw_unitary (k := k) hn1 hk hd3 hdq hp lab
  have hIeq := RecipeFieldSU.coe_recIU hu hk hd1
  rw [← hIeq] at hyp hH4 ⊢
  have hrig : ∀ σ : k ≃+* k, SemilinImpl (D := D) (LargeEvenProjMk D.H) 1 1 σ → σ = 1 := by
    intro σ hσ
    refine SU.eq_one_of_field_eq_one hu hd3 hn2 fun a b hab => ?_
    exact hσ a b (by rw [hab, one_mul, inv_one, mul_one])
  obtain ⟨σ, hσ, hσp, hσ1⟩ := exists_field_of_orderOf (D := D) hp hrig hf hford
  obtain ⟨τ, hτ, hτp, hτ1⟩ := exists_frobPow_of_dvd (k := k) hp hk2 (dvd_mul_of_dvd_right hpn 2)
    (by omega)
  haveI : IsCyclic (k ≃+* k) := (card_ringAut_and_isCyclic Nat.prime_two k hk2).2
  obtain ⟨j, hj, hσj⟩ := ggL45NtAutAsm_exists_pow_of_cyclic hp hσp hτp hσ1 hτ1
  obtain ⟨j', -, hjj'⟩ := Nat.exists_mul_mod_eq_one_of_coprime (k := p) (n := j)
    (hp.coprime_iff_not_dvd.mpr hj).symm hp.one_lt
  have hj' : ¬ p ∣ j' := by
    intro hdiv
    have h0 : j * j' % p = 0 := Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right hdiv j)
    omega
  have hσj' : σ ^ j' = τ := by
    rw [hσj, ← pow_mul, pow_eq_pow_mod _ hτp, hjj', pow_one]
  have hτ' : ∀ a, τ a = a ^ (2 ^ (lab.n / p)) ^ 2 := fun a => by
    rw [hτ a, Nat.mul_div_assoc 2 hpn, mul_comm 2 (lab.n / p), pow_mul]
  obtain ⟨π, hπs, hπker, hθ⟩ := SU.exists_cover_unitary hu hd3 hn2 hK θ
  obtain ⟨A, hAS, hA0⟩ := hu'
  have hAA : A ∈ D.A := SU.guSet_subset_cu hu hAS
  have hA : Implements (D := D) (LargeEvenProjMk D.H) u A := hA0
  obtain ⟨ũ, hũ⟩ := exists_implements_lift (D := D) hπs hπker hAA
  have hπR : Function.Surjective (LargeEvenProjMk D.H) := QuotientGroup.mk'_surjective _
  have hũbar : ggInducedAut θ ũ = u :=
    implements_injective_of_surj hπR hAA (implements_inducedAut hθ hũ) hA
  have hũI : GGL45InducesIn θ (RecipeFieldSU.recIU d hu hd1 : Set (MulAut _)) ũ :=
    (ggL45_inducesIn_iff θ _ ũ).mpr (by rw [hũbar, hIeq]; exact ⟨A, hAS, hA0⟩)
  have hyp₁ := ggL45TorusKGHyp_conj p lab (RecipeFieldSU.recIU d hu hd1) _ θ ũ hũI ψ E hyp
  have hψ₁bar : ggInducedAut θ (ũ⁻¹ * ψ * ũ) = f := by
    rw [map_mul, map_mul, map_inv, hũbar, hψbar]; group
  have hF : ∀ g ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) k (2 ^ lab.n))),
      ∀ m : ℕ, g ^ m ∈
        LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) k (2 ^ lab.n))) :=
    fun g hg m => YS09Field.matField_pow_closed _ (fun σ h hh => SU.map_mem_su hu σ hh) _ g hg m
  have hyp₂ := ggL45TorusKGHyp_pow hp hF hj' hyp₁
  have hψ₂R : SemilinImpl (D := D) (LargeEvenProjMk D.H)
      (ggInducedAut θ ((ũ⁻¹ * ψ * ũ) ^ j')) 1 τ := by
    rw [map_pow, hψ₁bar, ← hσj']
    exact hσ.pow j'
  have hψimpl : SemilinImpl (D := D) π ((ũ⁻¹ * ψ * ũ) ^ j') 1 τ :=
    semilinImpl_of_inducedAut hθ D.A.one_mem hψ₂R
  obtain ⟨h1, -, h3, h4, -, h6, h7, h8, h9, h10⟩ := id hyp₂
  have hEimpl : ∀ e ∈ E.map (MulAut.conj ũ⁻¹).toMonoidHom,
      ∃ x ∈ D.A, Implements (D := D) π e x := by
    intro e he
    have he' := (ggL45_inducesIn_iff θ _ e).mp (h6 e he)
    rw [hIeq] at he'
    obtain ⟨A', hA'S, hA'⟩ := he'
    have hA'A : A' ∈ D.A := SU.guSet_subset_cu hu hA'S
    exact ⟨A', hA'A, implements_of_inducedAut hθ hA'A hA'⟩
  have hsemi : ∀ γ : MulAut K, GGL45IsPElt p γ →
      ∃ g ∈ D.A, ∃ (σ' : k ≃+* k) (m : ℕ), σ' ^ p ^ m = 1 ∧ SemilinImpl (D := D) π γ g σ' := by
    rintro γ ⟨a, ha⟩
    have hγR : GGL45IsPElt p (ggInducedAut θ γ) := ⟨a, by rw [← map_pow, ha, map_one]⟩
    obtain ⟨g, hgA, σ', m, hσ', hg⟩ := SU.exists_semilin_of_pElt hu hd3 hn2 hp hp2 hγR
    exact ⟨g, hgA, σ', m, hσ', semilinImpl_of_inducedAut hθ hgA hg⟩
  have hpik : ∃ P : Subgroup (MulAut K), P ≤ E.map (MulAut.conj ũ⁻¹).toMonoidHom ∧
      Nat.card (E.map (MulAut.conj ũ⁻¹).toMonoidHom) ≤ p * Nat.card P ∧ ∀ e ∈ P,
      ∃ γ : MulAut K, GGL45IsPElt p γ ∧
        (∀ e' ∈ E.map (MulAut.conj ũ⁻¹).toMonoidHom, γ * e' = e' * γ) ∧
        e = γ * ((ũ⁻¹ * ψ * ũ) ^ j')⁻¹ * γ⁻¹ * (ũ⁻¹ * ψ * ũ) ^ j' := by
    obtain ⟨P, hPE, hPc, hP⟩ := h10
    refine ⟨P, hPE, hPc, fun e he => ?_⟩
    obtain ⟨γ, hγ1, hγ2, -, hγ4⟩ := hP e he
    exact ⟨γ, hγ1, hγ2, hγ4⟩
  have ha2 : d = 3 → p ∣ Nat.card (Subgroup.center K) := by
    intro hd
    have hp3' : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hd ▸ hpd)
    have hlab2 : GGLabelA2 lab := by
      unfold GGLabelA2
      refine ⟨by omega, by omega, Or.inr ⟨htag, ?_⟩⟩
      have h3' : ((3 : ℕ) : ℤ) ∣ ((2 ^ lab.n + 1 : ℕ) : ℤ) := by
        rw [hp3'] at hq
        push_cast
        simpa using hq
      exact Int.natCast_dvd_natCast.mp h3'
    exact hA2 hlab2 hp3'
  have hbig : p ^ (d / p) < Nat.card (E.map (MulAut.conj ũ⁻¹).toMonoidHom) := by
    by_contra hle
    push Not at hle
    exact SU.false_of_card_E_le hu hp hp2 hpd hd3 hq hτp hπs hπker
      (fun a b hab => hψimpl a b (by rw [hab, one_mul, inv_one, mul_one])) h4 h9 hle
  have hframe : ∀ L : Set (GL (Fin d) k), L.Finite → (∀ x ∈ L, ∀ y ∈ L, x * y = y * x) →
      (∀ x ∈ L, x ∈ D.A ∧ x ^ p = 1 ∧ Matrix.GeneralLinearGroup.map τ.toRingHom x = x) →
      ∃ P : GL (Fin d) k, Matrix.GeneralLinearGroup.map τ.toRingHom P = P ∧
        (∀ x ∈ L, ((P * x * P⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).IsDiag) ∧
        ∀ t : Fin d → kˣ, ∏ i, t i = 1 → (∀ i, GGL45IsPElt p (t i)) →
          P⁻¹ * diagGL d t * P ∈ D.H := by
    intro L hL hcomm hL'
    exact SU.exists_unitary_frame hu hp hp2 hpn (dvd_two_pow_div_add_one hp hpn hq) hτ' L hL hcomm
      (fun x hx => SU.unitary_of_mem_cu_of_pow hu hp hp2 hq (hL' x hx).1 (hL' x hx).2.1)
      (fun x hx => (hL' x hx).2.1) (fun x hx => (hL' x hx).2.2)
  let S : GSetting p (2 ^ (2 * lab.n / p)) d k D K ((ũ⁻¹ * ψ * ũ) ^ j')
      (E.map (MulAut.conj ũ⁻¹).toMonoidHom) :=
    { π := π
      surj := hπs
      ker_le := hπker
      τ := τ
      τ_apply := hτ
      hp := hp
      hp2 := hp2
      char_two := hu.charP
      card_k := by rw [← pow_mul, Nat.div_mul_cancel (dvd_mul_of_dvd_right hpn 2)]; exact hk2
      dvd_q₀ := dvd_Q₀_sub_one hp hpn hq
      dvd_d := hpd
      three_le := hd3
      ψ_impl := hψimpl
      E_impl := hEimpl
      semilin := hsemi
      ψ_pow := h1
      elem := h3
      card_E := h4
      comm := h7
      sat := h8
      big_E := hbig
      pik := hpik
      a2 := ha2
      frame := hframe }
  have h123 : GGL45TorusH123 p (RecipeFieldSU.recIU d hu hd1 : Set (MulAut _)) θ
      ((ũ⁻¹ * ψ * ũ) ^ j') (E.map (MulAut.conj ũ⁻¹).toMonoidHom) := by
    rw [hIeq]
    exact S.torusH123 (SU.guSet_subset_cu hu) hθ
  have hH₂ := ggL45TorusH_of_parts h123 (hH4 K θ hK _ _ hyp₂)
  have hH₁ := ggL45TorusH_pow hp hyp₁.1 hj' hH₂
  have hũinvI : GGL45InducesIn θ (RecipeFieldSU.recIU d hu hd1 : Set (MulAut _)) ũ⁻¹ :=
    (ggL45_inducesIn_iff θ _ ũ⁻¹).mpr (by
      rw [map_inv, hũbar]
      exact (RecipeFieldSU.recIU d hu hd1).inv_mem
        (by rw [← SetLike.mem_coe, hIeq]; exact ⟨A, hAS, hA0⟩))
  have hH := ggL45TorusH_conj p (RecipeFieldSU.recIU d hu hd1) θ ũ⁻¹ hũinvI _ _ hH₁
  have hψeq : ũ⁻¹⁻¹ * (ũ⁻¹ * ψ * ũ) * ũ⁻¹ = ψ := by group
  have hEeq : (E.map (MulAut.conj ũ⁻¹).toMonoidHom).map (MulAut.conj ũ⁻¹⁻¹).toMonoidHom = E := by
    rw [Subgroup.map_map]
    have hid : (MulAut.conj ũ⁻¹⁻¹).toMonoidHom.comp (MulAut.conj ũ⁻¹).toMonoidHom =
        MonoidHom.id _ := by
      ext e : 1
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply, inv_inv]
      group
    rw [hid, Subgroup.map_id]
  rw [hψeq, hEeq] at hH
  exact hH

theorem largeEvenLabelAll_torusHRaw_unitary_case2
    {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {lab : LargeEvenLabel} (htag : lab.tag = .twA) (hpd : p ∣ lab.rank + 1)
    (hq : (p : ℤ) ∣ 2 ^ lab.n + 1) : LargeEvenLabelAll lab (GGL45TorusHRaw p lab) := by
  obtain ⟨t, rank, n⟩ := lab
  dsimp only at htag hpd hq
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  exact recipeUnitary_and (fun k _ _ hk =>
    ggL45TorusHRaw_unitary_case2 hp hp2 (lab := ⟨.twA, rank, n⟩) rfl rfl hpd hq hk) hQ

theorem ggL45TorusHKnownFormsOn_famTypeACase2_unitary :
    GGL45TorusHKnownFormsOn fun p lab => GGL45FamTypeACase2 p lab ∧ lab.tag = .twA := by
  rintro p hp hp2 lab - - ⟨⟨⟨-, hpd⟩, hq⟩, htag⟩
  refine largeEvenLabelAll_torusHRaw_unitary_case2 hp hp2 htag hpd ?_
  have he : GGL45Eps lab = -1 := by simp [GGL45Eps, htag]
  rw [he] at hq
  simpa using hq

end CFSG.StandardType.GGL45TG
