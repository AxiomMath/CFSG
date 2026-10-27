module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenOrth
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyU

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

namespace CorFourTwoOpen

@[expose] def GGTorusSelfCentR (p : ℕ) {R : Type} [Group R] (Eh : Subgroup (MulAut R)) : Prop :=
  ∀ g : R, (∀ e ∈ Eh, e g = g) → g ^ p = 1 → MulAut.conj g ∈ Eh

@[expose] def GGNoInvariantLineSC (p : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ Eh : Subgroup (MulAut R), (Eh : Set (MulAut R)) ⊆ I → IsElemAbelian p Eh →
    p ^ 3 ≤ Nat.card Eh → GGTorusSelfCentR p Eh →
    ∀ Λ : Subgroup (MulAut R), Λ ≤ Eh → Nat.card Λ = p →
      ∃ w : R, MulAut.conj w ∈ Subgroup.normalizer (Eh : Set (MulAut R)) ∧
        ∃ e ∈ Λ, MulAut.conj w * e * (MulAut.conj w)⁻¹ ∉ Λ

section Coord

open UCoord

theorem exists_swap_move_line {d p : ℕ} (hp : p.Prime) (hd : 3 ≤ d) (hpd : ¬ p ∣ d)
    {f : ↥(sumZero d p)} (hf : f ≠ 1) :
    ∃ σ : Equiv.Perm (Fin d), ∀ n : ℕ, permAutV σ f ≠ f ^ n := by
  classical
  have := Fact.mk hp
  obtain ⟨i, j, hij⟩ : ∃ i j, crd f i ≠ crd f j := by
    by_contra h
    push Not at h
    apply hf
    have hd0 : (d : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact hpd
    have hsum := sum_crd f
    have hc : ∀ k, crd f k = crd f ⟨0, by omega⟩ := fun k => h k _
    rw [Finset.sum_congr rfl (fun k _ => hc k), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hsum
    have h0 : crd f ⟨0, by omega⟩ = 0 := (mul_eq_zero.mp hsum).resolve_left hd0
    exact ext_crd fun k => by rw [hc k, h0, crd_one]
  have hij' : i ≠ j := fun h => hij (h ▸ rfl)
  by_cases hk : ∃ k, k ≠ i ∧ k ≠ j ∧ crd f k ≠ 0
  · obtain ⟨k, hki, hkj, hk0⟩ := hk
    refine ⟨Equiv.swap i j, fun n hn => ?_⟩
    have h1 := congrArg (fun g => crd g k) hn
    have h2 := congrArg (fun g => crd g i) hn
    simp only [crd_permAutV, Equiv.swap_inv, crd_pow] at h1 h2
    rw [Equiv.swap_apply_of_ne_of_ne hki hkj] at h1
    rw [Equiv.swap_apply_left] at h2
    have hn1 : (n : ZMod p) = 1 := by
      have h3 : ((n : ZMod p) - 1) * crd f k = 0 := by linear_combination -h1
      exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hk0)
    rw [hn1, one_mul] at h2
    exact hij h2.symm
  · push Not at hk
    obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
    refine ⟨Equiv.swap i k, fun n hn => ?_⟩
    have h1 := congrArg (fun g => crd g k) hn
    simp only [crd_permAutV, Equiv.swap_inv, crd_pow, Equiv.swap_apply_right] at h1
    rw [hk k hki hkj, mul_zero] at h1
    have hsum := sum_crd f
    rw [Finset.sum_eq_single j (fun b _ hb => ?_) (by simp)] at hsum
    · exact hij (h1.trans hsum.symm)
    · by_cases hbi : b = i
      · rw [hbi]
        exact h1
      · exact hk b hbi hb

end Coord

section Config

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ggTorusSelfCentR_ggBeta {p : ℕ} (hp : p.Prime) {Bs L : Subgroup G} {R : Type} [Group R]
    (θ : L ⧸ Subgroup.center L ≃* R) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center L)) :
    GGTorusSelfCentR p (ggBeta L θ hBsN).range := by
  intro g hg hgp
  obtain ⟨l, rfl⟩ := ggQuotHom_surjective θ g
  have hcop : Nat.Coprime (Nat.card (Subgroup.center L)) p :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hZ)
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  set N := Nat.card (Subgroup.center L) with hN
  set l' : L := l ^ (N * u) with hl'
  have himg : ggQuotHom θ l' = ggQuotHom θ l := by
    rw [hl', map_pow, ← Nat.div_add_mod (N * u) p, hu, pow_add, pow_mul, hgp, one_pow, one_mul,
      pow_one]
  have hlpZ : l ^ p ∈ Subgroup.center L := by
    rw [← ker_ggQuotHom θ, MonoidHom.mem_ker, map_pow, hgp]
  have hl'p : l' ^ p = 1 := by
    have h1 : (⟨l ^ p, hlpZ⟩ : Subgroup.center L) ^ N = 1 := pow_card_eq_one'
    have h2 : (l ^ p) ^ N = 1 := by
      have := congrArg Subtype.val h1
      simpa using this
    rw [hl', ← pow_mul, mul_comm (N * u) p, ← mul_assoc, pow_mul, pow_mul, h2, one_pow]
  have hcopZ : Nat.Coprime p N := hcop.symm
  have hcomm : ∀ b ∈ Bs, (b : G) * (l' : G) = (l' : G) * b := by
    intro b hb
    have hfix := hg (ggBeta L θ hBsN ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩
    set m : L := L.normalizerMonoidHom ⟨b, hBsN hb⟩ l' with hm
    have hm' : ggQuotHom θ m = ggQuotHom θ l' := by
      have e1 : ggQuotHom θ m = ggBeta L θ hBsN ⟨b, hb⟩ (ggQuotHom θ l') := by
        rw [ggBeta_eq, ggQuotHom_apply, ggQuotHom_apply, ggLAut_apply]
      rw [e1, himg, hfix]
    have hz : m * l'⁻¹ ∈ Subgroup.center L := by
      rw [← ker_ggQuotHom θ, MonoidHom.mem_ker, map_mul, map_inv, hm', mul_inv_cancel]
    have hmp : m ^ p = 1 := by
      rw [hm, ← map_pow, hl'p, map_one]
    set z : Subgroup.center L := ⟨m * l'⁻¹, hz⟩ with hzdef
    have hzc : ∀ y : L, (z : L) * y = y * z := fun y => (Subgroup.mem_center_iff.mp hz y).symm
    have hzp : z ^ p = 1 := by
      apply Subtype.ext
      have e2 : m = (z : L) * l' := by rw [hzdef]; group
      have e3 : ((z : L) * l') ^ p = (z : L) ^ p * l' ^ p :=
        (Commute.mul_pow (hzc l') p)
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      calc (z : L) ^ p = (z : L) ^ p * l' ^ p := by rw [hl'p, mul_one]
        _ = ((z : L) * l') ^ p := e3.symm
        _ = m ^ p := by rw [← e2]
        _ = 1 := hmp
    have hz1 : orderOf z = 1 := Nat.eq_one_of_dvd_coprimes hcopZ (orderOf_dvd_of_pow_eq_one hzp)
      (orderOf_dvd_natCard z)
    rw [orderOf_eq_one_iff] at hz1
    have hml : m = l' := by
      have h1 : m * l'⁻¹ = 1 := by
        have := congrArg Subtype.val hz1
        simpa [hzdef] using this
      exact mul_inv_eq_one.mp h1
    have h2 : (b : G) * l' * b⁻¹ = l' := by
      have := congrArg Subtype.val hml
      rw [hm, normalizerMonoidHom_coe] at this
      exact this
    calc (b : G) * l' = (b : G) * l' * b⁻¹ * b := by group
      _ = l' * b := by rw [h2]
  have hl'C : (l' : G) ∈ Subgroup.centralizer (Bs : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun b hb => hcomm b hb
  have hl'pG : (l' : G) ^ p = 1 := by
    have := congrArg Subtype.val hl'p
    simpa using this
  have hl'B := hSC _ hl'C hl'pG
  refine ⟨⟨l', hl'B⟩, ?_⟩
  rw [ggBeta_eq, ggLAut_of_mem, himg]

theorem not_normalizer_le_of_noInvariantLineSC {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hC : GGConfig p B Bs x L D J) (hL : commutator L = ⊤)
    {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R) {I : Set (MulAut R)}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hZc : GGCenterCoprime p R) (hline : GGNoInvariantLineSC p R I)
    {E : Subgroup G} (hEBs : E ≤ Bs) (hxE : x ∈ E) (hE : Nat.card E = p ^ 2) :
    ¬ Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (E : Set G) := by
  intro hN
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := hC.2.1.1.trans hBsN
  obtain ⟨-, h3', -⟩ := card_range_ggBeta_bstar hC hL θ hBN hBsN
  have hSCB : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hC.2.1.2.2.2
  obtain ⟨hT, hBs, -⟩ := hC
  obtain ⟨-, -, -, -, -, hβ, hS, -⟩ := hT
  have hp : p.Prime := hβ.1
  have := Fact.mk hp
  have : Finite R := Finite.of_equiv _ θ.toEquiv
  set β := ggBeta L θ hBsN with hβdef
  have hEN : E ≤ Subgroup.normalizer (L : Set G) := hEBs.trans hBsN
  have hEA : IsElemAbelian p E := isElemAbelian_mono hBs.2.1 hEBs
  have hΛcard : Nat.card (ggBeta L θ hEN).range = p := by
    have h1 := card_range_ggBeta_mul_of hp hEA hxE hS.2.2.1 hS.2.2.2.1.1 hS.2.2.2.2 hL θ hEN
    rw [hE, pow_two] at h1
    exact Nat.eq_of_mul_eq_mul_right hp.pos h1
  have hΛE : (ggBeta L θ hEN).range ≤ β.range := range_ggBeta_le θ hEBs hEN hBsN
  have hle := Subgroup.card_le_of_le (range_ggBeta_le θ hBs.1 hBN hBsN)
  have hEhI : ((β.range : Subgroup (MulAut R)) : Set (MulAut R)) ⊆ I := by
    rintro _ ⟨c, rfl⟩
    exact ggBeta_mem L θ hBsN h3 c
  have hZ' : ¬ p ∣ Nat.card (Subgroup.center L) := by
    have h1 := hZc L (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hL
    rwa [ker_ggQuotHom] at h1
  obtain ⟨w, hw, e, he, hne⟩ := hline β.range hEhI (isElemAbelian_range_ggBeta θ hBs.2.1 hBsN)
    (h3'.trans hle) (ggTorusSelfCentR_ggBeta hp θ hBsN hSCB hZ') _ hΛE hΛcard
  obtain ⟨n, hnL, hnBs, hact⟩ := exists_normalizer_lift hp hBs.2.1 (hBs.1 hS.2.1) hS.2.2.1
    hS.2.2.2.1.1 hS.2.2.2.2 hL θ hBsN hZ' w hw
  apply hne
  rw [← hact e (hΛE he)]
  obtain ⟨⟨e₀, he₀⟩, rfl⟩ := he
  have h1 : n * e₀ * n⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp (hN hnBs) e₀).mp he₀
  refine ⟨⟨n * e₀ * n⁻¹, h1⟩, ?_⟩
  rw [ggBeta_eq, ggBeta_eq, ggLAut_conj]
  rfl

end Config

theorem ggLNoInvariantLineInputOn_of_labelsSC {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => GGCenterCoprime p R ∧ GGNoInvariantLineSC p R I) :
    GGLNoInvariantLineInputOn S := by
  intro G _ _ p B Bs x L D J hC hM E hEBs hxE hE
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBsN, h3⟩, hZc, hline⟩ := largeEvenRawDatum_exists hraw
  exact not_normalizer_le_of_noInvariantLineSC hC hL θ hBsN h3 hZc hline hEBs hxE hE

section Unitary

open UCoord

theorem ggNoInvariantLineSC_unitary {K : Type} [Field K] [Finite K] {n d p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2))
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d) :
    GGNoInvariantLineSC p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  intro Eh hEhI hEhA h3 hSC Λ hΛ hΛp
  have hZ := TableBUE.center_proj_eq_bot hK hd hdq
  have hinj := OrthRest.conj_injective hZ
  have := TableBSymp.finite_mulAut (R := LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
  have hIn : ∀ φ ∈ Eh, φ ∈ (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) →*
      MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))).range := fun φ hφ =>
    InndiagSU.ggOutdiagPrime_unitary hK hn hd hdq hp hpq hpd φ (hEhI hφ) (hEhA.2 φ hφ)
  set E := Eh.comap (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) →*
      MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))) with hE
  have hmap : E.map MulAut.conj = Eh := by
    rw [hE, Subgroup.map_comap_eq, inf_eq_right.mpr]
    exact hIn
  have hcardE : Nat.card E = Nat.card Eh := by
    rw [Nat.card_congr (E.equivMapOfInjective _ hinj).toEquiv, hmap]
  have hEe : IsElemAbelian p E := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hEhA a.2 b.2
    · rw [map_pow, map_one]
      exact hEhA.2 _ hx
  have hscE : ∀ g : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)),
      (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    refine hSC g (fun φ hφ => ?_) hgp
    obtain ⟨e, rfl⟩ := hIn φ hφ
    have he : e ∈ E := hφ
    rw [MulAut.conj_apply, ← hg e he, mul_inv_cancel_right]
  obtain ⟨τ, hτi, hτE, hperm, -⟩ := UModel.ggTorusPermEltSC_unitary hK hn (by omega) hp hp2 hpq
    hpd E hEe (hcardE ▸ h3) hscE
  obtain ⟨e₀, he₀Λ, he₀1⟩ : ∃ e ∈ Λ, e ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : Λ = ⊥ := (Subgroup.eq_bot_iff_forall Λ).mpr h
    rw [hbot, Subgroup.card_bot] at hΛp
    exact hp.one_lt.ne hΛp
  have hΛz : ∀ e ∈ Λ, ∃ m : ℕ, e₀ ^ m = e := by
    have hz : Subgroup.zpowers e₀ = Λ := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr he₀Λ) ?_
      rw [hΛp, Nat.card_zpowers]
      have h1 : orderOf e₀ ∣ p := hΛp ▸ Subgroup.orderOf_dvd_natCard Λ he₀Λ
      rcases (Nat.dvd_prime hp).mp h1 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) he₀1
      · exact h.ge
    intro e he
    rw [← hz] at he
    exact (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr he)
  obtain ⟨y₀, rfl⟩ := hIn e₀ (hΛ he₀Λ)
  have hy₀E : y₀ ∈ E := hΛ he₀Λ
  obtain ⟨f₀, rfl⟩ : y₀ ∈ τ.range := by
    rw [hτE]
    exact hy₀E
  have hf₀ : f₀ ≠ 1 := by
    rintro rfl
    exact he₀1 (by rw [map_one, map_one])
  obtain ⟨σ, hσ⟩ := exists_swap_move_line hp hd hpd hf₀
  obtain ⟨w, hw⟩ := hperm σ
  have hwN : MulAut.conj w ∈ Subgroup.normalizer
      (Eh : Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))) := by
    refine NbrLang.mem_normalizer_of_conj_mem fun b hb => ?_
    obtain ⟨y, rfl⟩ := hIn b hb
    have hyE : y ∈ E := hb
    obtain ⟨f, rfl⟩ : y ∈ τ.range := by
      rw [hτE]
      exact hyE
    rw [← map_inv, ← map_mul, ← map_mul, hw]
    show τ (permAutV σ f) ∈ E
    rw [← hτE]
    exact ⟨_, rfl⟩
  refine ⟨w, hwN, MulAut.conj (τ f₀), he₀Λ, fun hmem => ?_⟩
  obtain ⟨m, hm⟩ := hΛz _ hmem
  rw [← map_inv, ← map_mul, ← map_mul, hw, ← map_pow, ← map_pow] at hm
  exact hσ m (hτi (hinj hm)).symm


theorem recipeUnitary_noInvariantLineSC {d n p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    (hn : 1 ≤ n) (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2)) (hpd : ¬ p ∣ d) {Q : LargeEvenRawCont}
    (hQ : LargeEvenRecipeUnitary d (2 ^ n) Q) :
    LargeEvenRecipeUnitary d (2 ^ n) fun R _ I F =>
      Q R I F ∧ (GGCenterCoprime p R ∧ GGNoInvariantLineSC p R I) := by
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  exact ⟨ggCenterCoprime_of_centerPrime
      (StdSubRestU.ggCenterPrime_unitary hK hn hd hdq hp hp2 hpd),
    ggNoInvariantLineSC_unitary hK hn hd hdq hp hp2 hpq hpd⟩

end Unitary

end CorFourTwoOpen

open CorFourTwoOpen

section Labels


theorem largeEvenLabelAll_noInvariantLineSC_unitary {p : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : GGUnitaryCoprimeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGCenterCoprime p R ∧ GGNoInvariantLineSC p R I := by
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  rcases h with ⟨h, hpn, hpl⟩ | ⟨h, hl, hpn⟩
  · dsimp only at h hpn hpl
    subst h
    have hl2 : 2 ≤ l := hlab.2.1
    have hl2n : l = 2 → 2 ≤ n := hlab.2.2
    refine recipeUnitary_noInvariantLineSC hp hpn hn (by omega) ?_ hpl hQ
    intro heq
    simp only [Prod.mk.injEq] at heq
    have hn2 := hl2n (by omega)
    have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  · dsimp only at h hl hpn
    subst h hl
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_right (show ¬ (3 = 2) by decide), ite_eq_left (show (3 = 3) from rfl)] at hQ ⊢
    have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpn
    refine recipeUnitary_noInvariantLineSC hp hpn hn (by norm_num) (by simp)
      (fun h4 => hp2 ?_) hQ
    have h1 : p ∣ 2 ^ 2 := by norm_num; exact h4
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1)

theorem ggLNoInvariantLineInputOn_unitary :
    GGLNoInvariantLineInputOn GGUnitaryCoprimeLabel :=
  ggLNoInvariantLineInputOn_of_labelsSC fun _ _ hp hlab h =>
    largeEvenLabelAll_noInvariantLineSC_unitary hp hlab h

end Labels

end CFSG.StandardType

end
