module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResU5FiveHeis
public import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneUnitaryLabel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GUniGeom

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.FQ
  CFSG.LocalAnalysis.GLTheoremA.T156
open scoped commutatorElement

theorem exists_pow_five_of_pow_U5Five {K : Type} [Field K] [Finite K] {a : ℕ}
    (hK : Nat.card K = a ^ 5) (ha : a % 5 = 1) {s : Kˣ} (hs : s ^ (a - 1) = 1) :
    ∃ t : Kˣ, t ^ 5 = s := by
  classical
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  set Φ := (b + 1) ^ 4 + (b + 1) ^ 3 + (b + 1) ^ 2 + (b + 1) + 1 with hΦ
  have hb0 : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h0 | h0
    · subst h0
      have h1 : Nat.card K = 1 := by rw [hK]; norm_num
      have : Subsingleton K := (Nat.card_eq_one_iff_unique.mp h1).1
      exact absurd (Subsingleton.elim (1 : K) 0) one_ne_zero
    · exact h0
  have hfac : (b + 1) ^ 5 - 1 = b * Φ := by
    have e : (b + 1) ^ 5 = b * Φ + 1 := by rw [hΦ]; ring
    rw [e, Nat.add_sub_cancel]
  have h5Φ : 5 ∣ Φ := by
    apply Nat.dvd_of_mod_eq_zero
    rw [hΦ]
    simp [Nat.add_mod, Nat.pow_mod, ha]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = (b + 1) ^ 5 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]
  have hfin : IsOfFinOrder g := isOfFinOrder_of_finite g
  obtain ⟨e, he⟩ := (mem_powers_iff_mem_zpowers.mpr (hg s) : s ∈ Submonoid.powers g)
  have he' : g ^ e = s := he
  have hdvd : orderOf g ∣ e * b := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul, he']
    simpa using hs
  rw [hord, hfac, mul_comm e b] at hdvd
  have hΦe : Φ ∣ e := Nat.dvd_of_mul_dvd_mul_left hb0 hdvd
  obtain ⟨e', rfl⟩ := h5Φ.trans hΦe
  exact ⟨g ^ e', by rw [← pow_mul, mul_comm, he']⟩

theorem five_dvd_sub_U5Five {n : ℕ} (hpn : 5 ∣ 2 ^ n + 1) (h5n : 5 ∣ n) : 5 ∣ 2 ^ (n / 5) + 1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨m, rfl⟩ := h5n
  rw [Nat.mul_div_cancel_left m (by norm_num)]
  have h1 : ((2 ^ (5 * m) + 1 : ℕ) : ZMod 5) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpn
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast at h1 ⊢
  rw [pow_mul', ZMod.pow_card] at h1
  exact h1

section Field

variable {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem ggFixNoCompOn_u5Five (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) {σ : K ≃+* K}
    (hσ : Odd (orderOf σ)) (hσ5 : orderOf σ = 5) (hdq : ((5 : ℕ), 2 ^ (n / orderOf σ)) ≠ (3, 2))
    (h5 : 5 ∣ 2 ^ (n / orderOf σ) + 1)
    {f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 5) K (2 ^ n)))}
    (hf : Uni.Induced (2 ^ n) σ f) :
    GGFixNoCompOn (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 5) K (2 ^ n)))
        (LargeEvenGUSet (Fin 5) K (2 ^ n))) f
      (Uni.subfieldEquiv (by norm_num) hn hK hσ hdq hf).symm
      (ggRegSetU5Five (fixF σ) (n / orderOf σ)) := by
  classical
  intro φ hφI hφ φ₀ hφ₀X hres J
  obtain ⟨hjr, hj', hk⟩ := Uni.fixF_data hn hK σ hσ
  haveI : CharP (fixF σ) 2 := Uni.charP_fixF hn hK σ hσ
  obtain ⟨A, hAGU, hA⟩ := hφI
  obtain ⟨M, ⟨hMGU, hMreg⟩, hM⟩ := hφ₀X
  set ι : fixF σ →+* K := (fixF σ).subtype with hι
  set F₁ : GL (Fin 5) (fixF σ) →* GL (Fin 5) K := Matrix.GeneralLinearGroup.map ι with hF₁
  set Mt := F₁ M with hMt
  set e := Uni.subfieldEquiv (by norm_num) hn hK hσ hdq hf with he
  have hstep : ∀ B : GL (Fin 5) (fixF σ),
      B ∈ LargeEvenSUGroup (Fin 5) (fixF σ) (2 ^ (n / orderOf σ)) →
        ∃ z ∈ Subgroup.center (GL (Fin 5) K), A * F₁ B * A⁻¹ = Mt * F₁ B * Mt⁻¹ * z := by
    intro B hB
    set Bs : LargeEvenSUGroup (Fin 5) (fixF σ) (2 ^ (n / orderOf σ)) := ⟨B, hB⟩ with hBs
    have hg : Uni.subfieldHom hn hK σ hσ Bs ∈ ggFixDer f := by
      rw [← Uni.range_subfieldHom (by norm_num) hn hK hσ hdq hf]
      exact ⟨Bs, rfl⟩
    have hθ : e.symm ⟨_, hg⟩ = QuotientGroup.mk Bs := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      exact (Uni.coe_subfieldEquiv_mk (by norm_num) hn hK hσ hdq hf Bs).symm
    set B' : LargeEvenSUGroup (Fin 5) (fixF σ) (2 ^ (n / orderOf σ)) :=
      ⟨M * B * M⁻¹, Uni.conj_mem_su hMGU hB⟩ with hB'
    have h1 := hres _ hg
    rw [hθ] at h1
    have h2 : φ₀ (QuotientGroup.mk Bs) = QuotientGroup.mk B' := hM Bs B' rfl
    rw [h2] at h1
    have h3 : φ (Uni.subfieldHom hn hK σ hσ Bs) = Uni.subfieldHom hn hK σ hσ B' := by
      have h4 := congrArg Subtype.val ((MulEquiv.symm_apply_eq e).mp h1)
      exact h4.trans (Uni.coe_subfieldEquiv_mk (by norm_num) hn hK hσ hdq hf B')
    have hmem : A * F₁ B * A⁻¹ ∈ LargeEvenSUGroup (Fin 5) K (2 ^ n) :=
      Uni.conj_mem_su hAGU (Uni.subfieldInclusion hn hK σ hσ Bs).2
    have h4 : φ (Uni.subfieldHom hn hK σ hσ Bs) =
        LargeEvenProjMk (LargeEvenSUGroup (Fin 5) K (2 ^ n)) ⟨A * F₁ B * A⁻¹, hmem⟩ :=
      hA (Uni.subfieldInclusion hn hK σ hσ Bs) ⟨_, hmem⟩ rfl
    have h5' : LargeEvenProjMk (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 n K 5)
        ⟨A * F₁ B * A⁻¹, hmem⟩ = LargeEvenProjMk _ (Uni.subfieldInclusion hn hK σ hσ B') :=
      h4.symm.trans h3
    obtain ⟨c, hc⟩ := TableBUD.exists_scalar_of_mk_eq h5'
    have hc' : (A * F₁ B * A⁻¹)⁻¹ * (Mt * F₁ B * Mt⁻¹) =
        Matrix.GeneralLinearGroup.scalar (Fin 5) c := by
      rw [← hc]
      change _ = (A * F₁ B * A⁻¹)⁻¹ * F₁ (M * B * M⁻¹)
      rw [map_mul, map_mul, map_inv]
    refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 5) c⁻¹,
      Subgroup.mem_center_iff.mpr fun g => (TypeA.PGLTor.scalar_mul_comm c⁻¹ g).symm, ?_⟩
    rw [map_inv, ← hc']
    group
  set H1 : Subgroup (GL (Fin 5) K) :=
    (LargeEvenSUGroup (Fin 5) (fixF σ) (2 ^ (n / orderOf σ))).map F₁ with hH1def
  have hH1 : ⁅H1, H1⁆ = H1 := by
    rw [hH1def, ← Subgroup.map_commutator, Uni.commutator_su hk (by norm_num) hdq]
  have hcent : ∀ g ∈ H1, ⁅Mt⁻¹ * A, g⁆ ∈ Subgroup.center (GL (Fin 5) K) := by
    rintro _ ⟨B, hB, rfl⟩
    obtain ⟨z, hz, hzeq⟩ := hstep B hB
    have e1 : ⁅Mt⁻¹ * A, F₁ B⁆ = (F₁ B * Mt⁻¹) * z * (F₁ B * Mt⁻¹)⁻¹ :=
      calc ⁅Mt⁻¹ * A, F₁ B⁆ = Mt⁻¹ * (A * F₁ B * A⁻¹) * Mt * (F₁ B)⁻¹ := by
            rw [commutatorElement_def]
            group
        _ = Mt⁻¹ * (Mt * F₁ B * Mt⁻¹ * z) * Mt * (F₁ B)⁻¹ := by rw [hzeq]
        _ = (F₁ B * Mt⁻¹) * z * (F₁ B * Mt⁻¹)⁻¹ := by group
    rw [e1]
    exact (inferInstance : (Subgroup.center (GL (Fin 5) K)).Normal).conj_mem z hz _
  have hXs : Mt⁻¹ * A ∈ LargeEvenScalars (Fin 5) K :=
    Uni.mem_scalars_of_commute_su (k := fixF σ) (g := n / orderOf σ) hj' hk (by norm_num) ι
      fun x hx => LinearFieldFix.commute_of_commutator_mem_center hH1 hcent ⟨x, hx, rfl⟩
  obtain ⟨c, hc⟩ := hXs
  have hAeq : A = Mt * Matrix.GeneralLinearGroup.scalar (Fin 5) c := by
    have hc' : Matrix.GeneralLinearGroup.scalar (Fin 5) c = Mt⁻¹ * A := hc
    rw [hc', mul_inv_cancel_left]
  obtain ⟨⟨s, hs⟩, N, ζ, hζ1, hζ5, hMN⟩ := hMreg
  have hmapscal : ∀ u : (fixF σ)ˣ, F₁ (Matrix.GeneralLinearGroup.scalar (Fin 5) u) =
      Matrix.GeneralLinearGroup.scalar (Fin 5) (Units.map ι.toMonoidHom u) := by
    intro u
    apply Units.ext
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [hF₁, Matrix.scalar_apply]
    · simp [hF₁, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]
  have hMt5 : Mt ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin 5) (Units.map ι.toMonoidHom s) := by
    have hs' : Matrix.GeneralLinearGroup.scalar (Fin 5) s = M ^ 5 := hs
    rw [hMt, ← map_pow, ← hs', hmapscal]
  have hmK : n = n / orderOf σ * 5 := by rw [← hσ5]; exact hjr
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : Kˣ, t₀ ^ 5 = Units.map ι.toMonoidHom s := by
    refine exists_pow_five_of_pow_U5Five (a := (2 ^ (n / orderOf σ)) ^ 2) ?_ ?_ ?_
    · rw [hK, ← pow_mul, ← pow_mul, ← pow_mul]
      congr 1
      conv_lhs => rw [hmK]
      ring
    · have e1 : (2 ^ (n / orderOf σ)) ^ 2 - 1 =
          (2 ^ (n / orderOf σ) + 1) * (2 ^ (n / orderOf σ) - 1) := by
        have := Nat.sq_sub_sq (2 ^ (n / orderOf σ)) 1
        rwa [one_pow] at this
      have h1 : 5 ∣ (2 ^ (n / orderOf σ)) ^ 2 - 1 := e1 ▸ Dvd.dvd.mul_right h5 _
      have h2 : 1 ≤ (2 ^ (n / orderOf σ)) ^ 2 := Nat.one_le_pow _ _ (by positivity)
      omega
    · rw [← map_pow]
      have h1 : s ^ ((2 ^ (n / orderOf σ)) ^ 2 - 1) = 1 := by
        have h2 := pow_card_eq_one' (G := (fixF σ)ˣ) (x := s)
        rwa [Nat.card_units, hk] at h2
      rw [h1, map_one]
  have hA5 : A ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin 5) ((t₀ * c) ^ 5) := by
    rw [hAeq, ← TypeA.PGLTor.scalar_mul_comm c Mt, (TypeA.PGLTor.commute_scalar c Mt).mul_pow,
      hMt5, ← map_pow, ← map_mul, mul_pow, ht₀, mul_comm]
  have hcoe : ∀ Z : GL (Fin 5) (fixF σ),
      ((F₁ Z : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = (Z : Matrix (Fin 5) (Fin 5) _).map ι :=
    fun _ => rfl
  have hAmat : (A : Matrix (Fin 5) (Fin 5) K) = (c : K) • (Mt : Matrix (Fin 5) (Fin 5) K) := by
    rw [hAeq, ← TypeA.PGLTor.scalar_mul_comm c Mt, Units.val_mul,
      Matrix.GeneralLinearGroup.coe_scalar, TableBUD.scalar_mul_eq_smul]
  have hMNt : (Mt : Matrix (Fin 5) (Fin 5) K) * (F₁ N : GL (Fin 5) K) =
      ι ζ • (((F₁ N : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * Mt) := by
    rw [hMt, hcoe, hcoe, ← Matrix.map_mul, hMN,
      Matrix.map_smul _ _ (fun a => map_mul ι ζ a), Matrix.map_mul]
    rfl
  have hAN : (A : Matrix (Fin 5) (Fin 5) K) * (F₁ N : GL (Fin 5) K) =
      ι ζ • (((F₁ N : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * A) := by
    rw [hAmat, Matrix.smul_mul, hMNt, Matrix.mul_smul, smul_comm]
  have hζ1' : ι ζ ≠ 1 := fun h1 => hζ1 (ι.injective (h1.trans (map_one ι).symm))
  have hζ5' : ι ζ ^ 5 = 1 := by rw [← map_pow, hζ5, map_one]
  have hAnorm := TableBUE.gu_subset_normalizer (TableBU.unitaryFieldData_of_card hK hn) hAGU
  exact not_isComponentOf_ggFix_of_regular_U5Five hAnorm hA5 hζ1' hζ5' hAN hA J

end Field

section Datum

theorem ggFixDataKX_u5Five {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpn : 5 ∣ 2 ^ n + 1) (h5n : 5 ∣ n)
    {f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 5) K (2 ^ n)))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 5) K (2 ^ n))))
    (hord : orderOf f = 5) :
    GGFixDataKX 5 (fun k => k ∣ 5)
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 5) K (2 ^ n)))
        (LargeEvenGUSet (Fin 5) K (2 ^ n))) f := by
  obtain ⟨σ, hσf⟩ := Uni.exists_induced hf
  have hσ5 : orderOf σ = 5 := (Uni.orderOf_eq_of_induced (by norm_num) hn hK hσf).trans hord
  have hσ : Odd (orderOf σ) := by rw [hσ5]; decide
  obtain ⟨-, hj', hk⟩ := Uni.fixF_data hn hK σ hσ
  have hdq : ((5 : ℕ), 2 ^ (n / orderOf σ)) ≠ (3, 2) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  have h5 : 5 ∣ 2 ^ (n / orderOf σ) + 1 := by
    rw [hσ5]
    exact five_dvd_sub_U5Five hpn h5n
  haveI : CharP (fixF σ) 2 := Uni.charP_fixF hn hK σ hσ
  obtain ⟨hS, hna⟩ := Uni.simple_noncomm_proj hk (d := 5) (by norm_num) hdq
  exact ⟨_, inferInstance, _, ggRegSetU5Five (fixF σ) (n / orderOf σ),
    (Uni.subfieldEquiv (by norm_num) hn hK hσ hdq hσf).symm, hS, hna,
    Uni.ggFixGeom_unitary (by norm_num) hn hK hσ hdq hσf,
    TypeA.ggTorusLift_zero (two_dvd_card_statedProj_statedSU (d := 5) (f := n / orderOf σ)
      (K := fixF σ) (by norm_num)),
    ggTorusNoLineTwoKX_u5Five hk hj' h5, ggFixNoCompOn_u5Five hK hn hσ hσ5 hdq h5 hσf⟩

theorem largeEvenLabelAll_fixKX_u5Five {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .twA ∧ lab.rank = 4 ∧ 5 ∣ 2 ^ lab.n + 1 ∧ 5 ∣ lab.n) :
    LargeEvenLabelAll lab (GGRawFieldFixKX 5 (fun k => k ∣ 5)) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hpn, h5n⟩ := h
  dsimp only at ht hl hpn h5n
  subst ht hl
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, ← pow_mul])
  refine ⟨K, i1, i2, hK, hQ', ?_⟩
  intro _ _ f hf hord
  exact ggFixDataKX_u5Five hK hn hpn h5n hf hord

end Datum

end CFSG.StandardType

end
