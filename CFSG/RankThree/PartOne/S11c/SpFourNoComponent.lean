module

public import CFSG.RankThree.PartOne.KC.SymplecticFourInnerDefining
public import CFSG.RankThree.PartOne.S11c.ClassicalFiveFixed

public section

namespace CFSG.RankThree.PartOne.HNRed

open Matrix CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.PartOne.KCExpLog CFSG.RankThree.PartOne.KCSymplectic
open CFSG.RankThree.PartOne.KCSymplecticAdapted CFSG.RankThree.PartOne.KCSymplecticInner
open CFSG.RankThree.PartOne.KCSymplecticFour CFSG.RankThree.LocalRank
open CFSG.RankThree.PartOne.KCRegular
open CFSG.RankThree.Classical (siegelElt coe_siegelElt siegelElt_mem siegelRadicalSp
  pow_char_eq_one_of_mem_siegelRadicalSp conj_mem_siegelRadicalSp_of_proj_commute
  exists_eq_conj_of_forall_fix_projSiegel)

theorem noComponent_of_pointwise_centralizer {T : Type*} [Group T] [Finite T]
    (hinj : Function.Injective (MulAut.conj : T →* MulAut T)) {p : ℕ} (hp : p.Prime) {x : T}
    (U : Subgroup T) (hUC : U ≤ Subgroup.centralizer ({x} : Set T)) (hUp : ∀ z ∈ U, z ^ p = 1)
    (hUnorm : ∀ c ∈ Subgroup.centralizer ({x} : Set T), ∀ z ∈ U, c * z * c⁻¹ ∈ U)
    (hpt : ∀ α : MulAut T, (∀ z ∈ U, α z = z) → ∃ z ∈ U, α = MulAut.conj z) :
    ∀ L : Subgroup (Subgroup.centralizer ({x} : Set T)), ¬ CFSG.IsComponent L := by
  have : Fact p.Prime := ⟨hp⟩
  intro L
  refine CFSG.RankThree.CAInnerDefining.forall_not_isComponent_of_pow (p := p)
    (U.subgroupOf (Subgroup.centralizer ({x} : Set T))) ?_ ?_ ?_ L
  · exact ⟨fun n hn c => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact hUnorm c c.2 n hn⟩
  · intro y hy
    apply Subtype.ext
    simpa using hUp _ (Subgroup.mem_subgroupOf.mp hy)
  · intro g hg
    have hgU : ∀ z ∈ U, (g : T) * z * (g : T)⁻¹ = z := by
      intro z hz
      have h1 := hg ⟨z, hUC hz⟩ (Subgroup.mem_subgroupOf.mpr hz)
      have h2 : (g : T) * z = z * g := congrArg Subtype.val h1
      calc (g : T) * z * (g : T)⁻¹ = z * g * (g : T)⁻¹ := by rw [h2]
        _ = z := by group
    obtain ⟨w, hw, hgw⟩ := hpt (MulAut.conj (g : T))
      (fun z hz => by simpa [MulAut.conj_apply] using hgU z hz)
    have hgw' : (g : T) = w := hinj hgw
    apply Subtype.ext
    rw [Subgroup.coe_pow, hgw']
    exact hUp w hw

section Radical

variable {r : ℕ} {K : Type} [Field K]

theorem symplectic_noComponent_of_radical_data {p f : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hf : 1 ≤ f) (hr : 2 ≤ r) [Finite K] [CharP K p] (hK : Nat.card K = p ^ f)
    (u : StatedSp r K) (hup : u ^ p = 1) (N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
    (hN : ∀ g : StatedSp r K, g * u = u * g →
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * N =
        N * ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))
    (R : Subgroup (StatedSp r K)) (hRu : ∀ y ∈ R, y * u = u * y) (hRp : ∀ y ∈ R, y ^ p = 1)
    (hRnorm : ∀ g : StatedSp r K,
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * N =
        N * ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) →
        ∀ y ∈ R, g * y * g⁻¹ ∈ R)
    (hRpt : ∀ (A : gsp r K) (σ : K ≃+* K), (∀ y ∈ R, conjSp r K A (fieldSp r K σ y) = y) →
      ∃ y' ∈ R, conjAut r K A * fieldAut r K σ = MulAut.conj (proj r K y')) :
    ∀ L : Subgroup (Subgroup.centralizer ({proj r K u} : Set (StatedProj (StatedSp r K)))),
      ¬ CFSG.IsComponent L := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    exact (show 4 ≤ p by omega).trans (Nat.le_self_pow (by omega) p)
  have hinj := conj_injective_statedProj_statedSp (r := r) (K := K) hr h4
  refine noComponent_of_pointwise_centralizer hinj hp (U := R.map (proj r K)) ?_ ?_ ?_ ?_
  ·
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hRu y hy]
  ·
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, hRp y hy, map_one]
  ·
    intro c hc z hz
    obtain ⟨g, rfl⟩ := CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective c
    obtain ⟨y, hy, rfl⟩ := hz
    have hy' : proj r K g * proj r K u = proj r K u * proj r K g :=
      Subgroup.mem_centralizer_singleton_iff.1 hc
    have hconj : g * u * g⁻¹ = u :=
      CFSG.ComponentClassification.CatalogueBSymplecticTwo.eq_of_proj_eq_of_pow_eq_one (by omega)
        p (a := 1) (b := 1)
        (by rw [pow_one, conj_pow, hup, mul_one, mul_inv_cancel]) (by rw [pow_one, hup])
        (by rw [map_mul, map_mul, map_inv, hy', mul_inv_cancel_right])
    have hgu : g * u = u * g := by
      calc g * u = g * u * g⁻¹ * g := by group
        _ = u * g := by rw [hconj]
    refine ⟨g * y * g⁻¹, hRnorm g (hN g hgu) y hy, ?_⟩
    rw [map_mul, map_mul, map_inv]
  ·
    intro α hα
    have hodd : ringChar K ≠ 2 := by
      rw [ringChar.eq K p]
      exact hp2
    obtain ⟨A, σ, hαA⟩ :=
      CFSG.ComponentClassification.CatalogueBSymplecticRepresentation.automorphism_standard hodd
        hr α
    have hexact : ∀ y ∈ R, conjSp r K A (fieldSp r K σ y) = y := by
      intro y hy
      have hfix := hα _ ⟨y, hy, rfl⟩
      rw [hαA, MulAut.mul_apply, fieldAut_proj, conjAut_proj] at hfix
      exact CFSG.ComponentClassification.CatalogueBSymplecticTwo.eq_of_proj_eq_of_pow_eq_one
        (by omega) p (a := 1) (b := 1)
        (by rw [pow_one, ← map_pow, ← map_pow, hRp y hy, map_one, map_one])
        (by rw [pow_one, hRp y hy]) hfix
    obtain ⟨y', hy', hα'⟩ := hRpt A σ hexact
    exact ⟨_, ⟨y', hy', rfl⟩, by rw [hαA, hα']⟩

end Radical


section Cases

variable {K : Type} [Field K]

theorem symplectic_regular_noComponent {p f r : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hf : 1 ≤ f)
    (hr : 2 ≤ r) (h2rp : 2 * r ≤ p) [Finite K] (hK : Nat.card K = p ^ f)
    {N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hNJ : Nᵀ * formJ r K + formJ r K * N = 0) (hN0 : N ^ (2 * r) = 0)
    (hN1 : N ^ (2 * r - 1) ≠ 0) (u : StatedSp r K)
    (hu : ((u : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      expMat (2 * r) N) :
    ∀ L : Subgroup (Subgroup.centralizer ({proj r K u} : Set (StatedProj (StatedSp r K)))),
      ¬ CFSG.IsComponent L := by
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite K
  have : CharP K p :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  have hr1 : 1 ≤ r := by omega
  have hup : u ^ p = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
    show spMat u ^ p = 1
    have hu' : spMat u = expMat (2 * r) N := hu
    rw [hu']
    exact expMat_pow_char (finSumFinTwoMul r) (by omega) h2rp hN0
  refine symplectic_noComponent_of_radical_data hp hp3 hf hr hK u hup N ?_
    (unipCentralizer hN0 hN1 hr1) ?_ ?_ ?_ ?_
  · intro g hg
    exact (commute_of_mul_comm hr1 hN0 hu h2rp hg).eq
  · intro y hy
    exact mul_comm_of_mem_unipCentralizer hu h2rp hy
  · intro y hy
    exact pow_eq_one_of_mem_unipCentralizer h2rp hy
  · intro g hg y hy
    have h := mul_comm_of_commute_regular (show Commute (spMat g) N from hg) hy
    rw [h, mul_inv_cancel_right]
    exact hy
  · intro A σ hfix
    exact exists_conj_of_forall_fix_unipCentralizer hr h2rp hN0 hN1 hNJ A σ hfix

theorem symplectic_transvection_std_noComponent {p f : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) {c : K} (hc : c ≠ 0) (u : StatedSp 2 K)
    (hu : ((u : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      1 + Matrix.single (Sum.inl 0) (Sum.inr 0) c) :
    ∀ L : Subgroup (Subgroup.centralizer ({proj 2 K u} : Set (StatedProj (StatedSp 2 K)))),
      ¬ CFSG.IsComponent L := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero f hp.ne_zero)
  have := Fintype.ofFinite K
  have : CharP K p := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    have := Nat.le_of_dvd (by norm_num) ((CharP.cast_eq_zero_iff K p 2).mp h')
    omega
  have hu' : u = symplecticStdTransvection K c := by
    apply Subtype.ext
    apply Units.ext
    rw [hu, coe_symplecticStdTransvection]
  subst hu'
  have htv : symplecticFourTransvection K c ∈ radical K :=
    ⟨0, 0, c, by rw [coe_symplecticFourTransvection, uMat_zero_zero]⟩
  refine symplectic_noComponent_of_radical_data hp hp3 hf (le_refl 2) hK _ ?_
    (Matrix.single (Sum.inl 0) (Sum.inr 0) c) ?_ (radicalStd K) ?_ ?_ ?_ ?_
  · rw [symplecticStdTransvection, ← map_pow, pow_char_eq_one_of_mem_radical htv, map_one]
  · intro g hg
    have h1 := congrArg (fun z : StatedSp 2 K => ((z : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hg
    simp only [Subgroup.coe_mul, Units.val_mul, coe_symplecticStdTransvection] at h1
    rw [mul_add, add_mul, mul_one, one_mul] at h1
    exact add_left_cancel h1
  · rintro _ ⟨y₀, hy₀, rfl⟩
    change spEquiv K y₀ * spEquiv K (symplecticFourTransvection K c) =
      spEquiv K (symplecticFourTransvection K c) * spEquiv K y₀
    rw [← map_mul, ← map_mul, radical_comm_transvection hy₀ c]
  · rintro _ ⟨y₀, hy₀, rfl⟩
    change (spEquiv K y₀) ^ p = 1
    rw [← map_pow, pow_char_eq_one_of_mem_radical hy₀, map_one]
  · intro g hg y hy
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    set g₀ : symplecticFourS K := (spEquiv K).symm g with hg₀
    have hgρ : ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        coordAlg K ((g₀ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
      rw [← coe_coordGL, ← coe_spEquiv, hg₀, MulEquiv.apply_symm_apply]
    have hNρ : Matrix.single (Sum.inl 0) (Sum.inr 0) c =
        coordAlg K (c • symplecticFourE14 K) := by
      rw [map_smul, coordAlg_E14, Matrix.smul_single, smul_eq_mul, mul_one]
    rw [hgρ, hNρ, ← map_mul, ← map_mul] at hg
    have hg' := (coordAlg K).injective hg
    rw [Matrix.mul_smul, Matrix.smul_mul] at hg'
    have hcomm := smul_right_injective _ hc hg'
    refine ⟨g₀ * y₀ * g₀⁻¹, conj_mem_radical_of_commute hcomm hy₀, ?_⟩
    change spEquiv K (g₀ * y₀ * g₀⁻¹) = g * spEquiv K y₀ * g⁻¹
    rw [map_mul, map_mul, map_inv, hg₀, MulEquiv.apply_symm_apply]
  · intro A σ hex
    exact exists_eq_conj_of_forall_fix_radicalStd h2 A σ hex

end Cases


section SquareZero

variable {r : ℕ} {K : Type} [Field K]

theorem symplectic_square_zero_noComponent {p f : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (hr : 2 ≤ r) {D : Matrix (Fin r) (Fin r) K} (hDs : Dᵀ = D)
    (hD : IsUnit D) :
    ∀ L : Subgroup (Subgroup.centralizer
      ({proj r K (siegelElt hDs)} : Set (StatedProj (StatedSp r K)))), ¬ CFSG.IsComponent L := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero f hp.ne_zero)
  have := Fintype.ofFinite K
  have : CharP K p :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    exact (show 4 ≤ p by omega).trans (Nat.le_self_pow (by omega) p)
  have hinj := conj_injective_statedProj_statedSp (r := r) (K := K) hr h4
  set x := proj r K (siegelElt hDs) with hx
  set U := (siegelRadicalSp r K).map (proj r K) with hU
  have hUp : ∀ z ∈ U, z ^ p = 1 := by
    rintro _ ⟨w, hw, rfl⟩
    rw [← map_pow, pow_char_eq_one_of_mem_siegelRadicalSp hw, map_one]
  have hUcomm : ∀ z ∈ U, ∀ z' ∈ U, z * z' = z' * z := by
    rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩ _ ⟨_, ⟨v', rfl⟩, rfl⟩
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm v v']
  refine noComponent_of_pointwise_centralizer hinj hp (U := U) ?_ hUp ?_ ?_
  · exact fun z hz => Subgroup.mem_centralizer_singleton_iff.2
      (hUcomm z hz x ⟨_, siegelElt_mem hDs, rfl⟩)
  · intro c hc z hz
    obtain ⟨g, rfl⟩ := SymplecticHigher.proj_surjective c
    obtain ⟨w, hw, rfl⟩ := hz
    have hg : proj r K g * x = x * proj r K g := Subgroup.mem_centralizer_singleton_iff.1 hc
    refine ⟨g * w * g⁻¹, conj_mem_siegelRadicalSp_of_proj_commute (by omega) hDs hD hg hw, ?_⟩
    rw [map_mul, map_mul, map_inv]
  · exact fun α hα => exists_eq_conj_of_forall_fix_projSiegel hp2 hr α hα

end SquareZero

theorem noComponent_conj {T : Type*} [Group T] (s w : T)
    (h : ∀ L : Subgroup (Subgroup.centralizer ({w} : Set T)), ¬ CFSG.IsComponent L) :
    ∀ L : Subgroup (Subgroup.centralizer ({s * w * s⁻¹} : Set T)), ¬ CFSG.IsComponent L := by
  have hw : (MulAut.conj s⁻¹ : T ≃* T) (s * w * s⁻¹) = w := by
    rw [MulAut.conj_apply]
    group
  exact CFSG.RankThree.CAInnerDefining.forall_not_isComponent_centralizer_of_mulEquiv
    (MulAut.conj s⁻¹ : T ≃* T) (s * w * s⁻¹) (by rw [hw]; exact h)


theorem noComponent_of_unipotent {p f : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] [CharP K p] (hK : Nat.card K = p ^ f) (u : StatedSp 2 K)
    (hup : u ^ p = 1) (hu1 : u ≠ 1) :
    ∀ L : Subgroup (Subgroup.centralizer ({proj 2 K u} : Set (StatedProj (StatedSp 2 K)))),
      ¬ CFSG.IsComponent L := by
  have : Fact p.Prime := ⟨hp⟩
  have h2K : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    have := (CharP.cast_eq_zero_iff K p 2).mp h'
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hupm : spMat u ^ p = 1 := by
    have h := congrArg (fun g : StatedSp 2 K => spMat g) hup
    simpa [spMat, Subgroup.coe_pow, Units.val_pow_eq_pow_val] using h
  have hMp : (spMat u - 1) ^ p = 0 := by
    rw [sub_pow_char_of_commute p (Commute.one_right _), one_pow, hupm, sub_self]
  have hM4 : (spMat u - 1) ^ (2 * 2) = 0 := by
    rw [← card_fin_sum_fin 2]
    exact pow_card_eq_zero_of_isNilpotent ⟨p, hMp⟩
  have hdp : 2 * 2 ≤ p := by omega
  have hKc := not_cast_eq_zero_of_lt (K := K) (p := p) (r := 2) hdp
  have huJ : (spMat u)ᵀ * formJ 2 K * spMat u = formJ 2 K :=
    SymplecticTorusWeyl.mem_statedSp_iff.mp u.2
  set N := logMat (2 * 2) (spMat u) with hN
  have hNJ : Nᵀ * formJ 2 K + formJ 2 K * N = 0 :=
    logMat_skew (finSumFinTwoMul 2) (by omega) hdp (formJ_mul_neg 2 K) (neg_formJ_mul 2 K) hM4
      huJ
  have hN4 : N ^ (2 * 2) = 0 := logMat_pow_eq_zero (finSumFinTwoMul 2) hM4
  have hexp : spMat u = expMat (2 * 2) N :=
    (expMat_logMat (finSumFinTwoMul 2) (by omega) hKc hM4).symm
  have hNne : N ≠ 0 := by
    intro h0
    apply hu1
    apply Subtype.ext
    apply Units.ext
    show spMat u = 1
    rw [hexp, h0]
    simp [expMat, Finset.sum_range_succ]
  have hdim : Module.finrank K (Fin 2 ⊕ Fin 2 → K) = 4 := by simp
  have hf4 : (Matrix.toLin' N) ^ 4 = 0 := by
    rw [← Matrix.toLin'_pow]
    have : N ^ 4 = 0 := hN4
    rw [this, map_zero]
  have hfne : Matrix.toLin' N ≠ 0 := fun h => hNne ((Matrix.toLin'.map_eq_zero_iff).mp h)
  obtain ⟨c, hli, hc⟩ := KCNilpotent.exists_chain_four hdim (Matrix.toLin' N) hf4 hfne
  simp only [Matrix.toLin'_apply] at hc
  rcases hc with ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩
  ·
    have hN3c : (N ^ 3) *ᵥ c 3 = c 0 := by
      rw [pow_three, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h3, h2, h1]
    have hN1 : N ^ (2 * 2 - 1) ≠ 0 := by
      intro h
      have h' : N ^ 3 = 0 := h
      rw [h', Matrix.zero_mulVec] at hN3c
      exact hli.ne_zero 0 hN3c.symm
    exact symplectic_regular_noComponent hp hp3 hf (le_refl 2) hdp hK hNJ hN4 hN1 u hexp
  ·
    obtain ⟨A, γ, hγ, hA, hNA⟩ := exists_isometry_of_chain_transvection hNJ hli h0 h1 h2 h3
    have hsq : (γ • (Matrix.single (Sum.inl 0) (Sum.inr 0) (1 : K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) *
        (γ • (Matrix.single (Sum.inl 0) (Sum.inr 0) (1 : K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) = 0 := by
      simp
    obtain ⟨s, w, hsw, hw⟩ := exists_conj_of_isometry_mul_eq hexp hA hNA hsq
    have h' := noComponent_conj (proj 2 K s) (proj 2 K w)
      (symplectic_transvection_std_noComponent hp hp3 hf hK hγ w
        (hw.trans (by simp [Matrix.smul_single])))
    rwa [← map_inv, ← map_mul, ← map_mul, ← hsw] at h'
  ·
    obtain ⟨A, D, hA, hDs, hD, hNA⟩ := exists_isometry_of_chain_square_zero hNJ h2K hli h0 h1 h2 h3
    have hsq : (Matrix.fromBlocks 0 D 0 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        Matrix.fromBlocks 0 D 0 0 = 0 := by
      rw [Matrix.fromBlocks_multiply]
      simp
    obtain ⟨s, w, hsw, hw⟩ := exists_conj_of_isometry_mul_eq hexp hA hNA hsq
    have hws : w = siegelElt hDs := by
      apply SymplecticTorusWeyl.statedSp_ext
      rw [coe_siegelElt]
      show spMat w = _
      rw [hw]
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply]
    have hnc := symplectic_square_zero_noComponent hp hp3 hf hK (le_refl 2) hDs hD
    rw [← hws] at hnc
    have h' := noComponent_conj (proj 2 K s) (proj 2 K w) hnc
    rwa [← map_inv, ← map_mul, ← map_mul, ← hsw] at h'
  ·
    exact (not_chain_three_one_mat hNJ h2K hli h0 h1 h2 h3).elim


theorem oddSymplecticFourInnerDefiningFixedComponentFree_holds :
    OddSymplecticFourInnerDefiningFixedComponentFree := by
  intro ℓ f hℓ hℓ3 hf T _ hmod β hβ hβℓ
  obtain ⟨-, k, _, _, hk, ⟨e⟩⟩ := hmod
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hchar : CharP k ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ hf hk
  have h4 : 4 ≤ Nat.card k := by
    rw [hk]
    exact (show 4 ≤ ℓ by omega).trans (Nat.le_self_pow (by omega) ℓ)
  have hinjP := conj_injective_statedProj_statedSp (r := 2) (K := k) le_rfl h4
  obtain ⟨y, rfl⟩ := hβ
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, map_one, orderOf_one] at hβℓ
    exact hℓ.one_lt.ne hβℓ
  have hpow : (MulAut.conj y : MulAut T) ^ ℓ = 1 := by
    rw [← hβℓ]
    exact pow_orderOf_eq_one _
  have hxpow : (MulAut.conj (e y) : MulAut (StatedProj (StatedSp 2 k))) ^ ℓ = 1 := by
    have := congrArg (MulAut.congr e) hpow
    rwa [map_pow, CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, map_one] at this
  have hxℓ : e y ^ ℓ = 1 := by
    apply hinjP
    rw [map_pow, hxpow, map_one]
  have hx1 : e y ≠ 1 := fun h => hy1 (e.injective (h.trans (map_one e).symm))
  have hrange : e y ∈ (proj 2 k).range := by
    obtain ⟨g, hg⟩ := SymplecticHigher.proj_surjective (e y)
    exact ⟨g, hg⟩
  obtain ⟨u, hux, hup⟩ := exists_lift_pow_eq_one (proj 2 k) hℓ
    (by rw [SymplecticHigher.ker_proj]; exact not_dvd_card_scalars hℓ hf hk) hrange hxℓ
  have hu1 : u ≠ 1 := by
    rintro rfl
    apply hx1
    rw [← hux, map_one]
  have hnc := noComponent_of_unipotent hℓ hℓ3 hf hk u hup hu1
  rw [hux] at hnc
  have hnc' := CFSG.RankThree.CAInnerDefining.forall_not_isComponent_centralizer_of_mulEquiv e y
    hnc
  rw [CFSG.RankThree.CAInnerDefining.eqLocus_conj_eq_centralizer y]
  exact hnc'


end CFSG.RankThree.PartOne.HNRed
