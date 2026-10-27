module

public import CFSG.RankThree.PartOne.KF.R12Ctx
public import CFSG.RankThree.PartOne.KF.R12Unitary
public import CFSG.RankThree.PartOne.KF.HeartCtx
public import CFSG.RankThree.PartOne.KF.ToralQuotAut
public import CFSG.RankThree.PartOne.KF.SymCtxMatrix
public import CFSG.RankThree.PartOne.KF.R1Model
public import CFSG.RankThree.PartOne.KF.Reduction123
public import CFSG.RankThree.PartOne.KF.RowCore

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag

variable {G : Type} [Group G]

theorem exists_r12ctx [Finite G] {p : ℕ} {L A₀ F : Subgroup G} (h : Table123Core p L A₀ F)
    (hmodel : RowModel p L 12) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), (∃ ζ : Kˣ, IsPrimitiveRoot ζ 5) ∧
      Nonempty (HeartCtx K L F) := by
  classical
  obtain ⟨hp5, -, f, hf1, h5, h25, hmod⟩ := hmodel
  subst hp5
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hmod
  have hU : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf1, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨z, hz⟩ := exists_isPrimitiveRoot hU Nat.prime_five h5
  have hz0 : z ≠ 0 := hz.ne_zero (by norm_num)
  obtain ⟨ζ, hζ'⟩ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ 5 :=
    ⟨Units.mk0 z hz0, IsPrimitiveRoot.coe_units_iff.mp (by simpa using hz)⟩
  have hTM : torusSU 5 5 K ≤ unitarySU 2 f K 5 := torusSU_le_unitarySU hU h5
  have hdist : ∀ i j : Fin 5, i ≠ j → ∃ x ∈ torusSU 5 5 K, ent x i i ≠ ent x j j := fun i j hij =>
    torusSU_char_distinct hζ'.pow_eq_one
      (hζ'.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)) hij
  obtain ⟨SM⟩ := SymCtx.ofMatrixGroup (p := 5) (unitarySU 2 f K 5) hTM
    (fun σ => permGL_mem_unitarySU hU σ) hdist
  have hZT : scalarsU K f ≤ (torusSU 5 5 K).subgroupOf (unitarySU 2 f K 5) := by
    intro w hw
    have hw' : (w : GL (Fin 5) K) ∈ StatedScalars (Fin 5) K := Subgroup.mem_subgroupOf.mp hw
    obtain ⟨c, hc⟩ := hw'
    have hdet := ((mem_unitarySU_iff hU).mp w.2).1
    have hc5 : c ^ 5 = 1 := by
      rw [← hc] at hdet
      have h2 : ((Matrix.GeneralLinearGroup.scalar (Fin 5) c : GL (Fin 5) K) :
          Matrix (Fin 5) (Fin 5) K) = (c : K) • (1 : Matrix (Fin 5) (Fin 5) K) := by
        simp [Matrix.GeneralLinearGroup.scalar, Matrix.smul_one_eq_diagonal]
      rw [h2, det_smul_one_five] at hdet
      exact Units.ext (by simpa using hdet)
    have h1 : Matrix.GeneralLinearGroup.scalar (Fin 5) c = diagU (fun _ => c) := by
      apply Units.ext
      rw [diagU_val]
      simp [Matrix.GeneralLinearGroup.scalar]
    rw [Subgroup.mem_subgroupOf, ← hc, h1]
    exact mem_torusSU_iff.mpr ⟨fun _ => c, fun _ => hc5, by simp [Finset.prod_const, hc5], rfl⟩
  have hcardZ : Nat.card (scalarsU K f) = 5 := card_scalarsU hU h5 hz
  have hZV : ∀ d : torusVec 5 5 K, projU K f
      ((SM.tor d : (torusSU 5 5 K).subgroupOf (unitarySU 2 f K 5)) : ↥(unitarySU 2 f K 5)) = 1 ↔
      d ∈ scalarSub 5 5 K := fun d => by
    rw [← symCtx_scalars SM (scalarsU K f) scalarsU_le_center hZT hcardZ ⟨ζ, hζ'⟩ d, ← ker_projU,
      MonoidHom.mem_ker]
  have hker_le : (projU K f).ker ≤ (torusSU 5 5 K).subgroupOf (unitarySU 2 f K 5) := by
    rw [ker_projU]
    exact hZT
  obtain ⟨SH⟩ := heartCtx_of_symCtx (projU K f) projU_surjective SM hker_le hZV
  have hcop : Nat.Coprime 5 (Nat.card (Subgroup.center ↥L)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr h.center_pPrime
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀ : ↥L →* StatedProj (unitarySU 2 f K 5), IsCentralPQuot 5 ε₀ :=
    ⟨_, isCentralPQuot_center e hcop⟩
  have hTexp : ∀ t ∈ torusBar K f, t ^ 5 = 1 := by
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_pow]
    have : t ^ 5 = 1 := by
      apply Subtype.ext
      obtain ⟨d, hd1, -, hd⟩ := mem_torusSU_iff.mp (Subgroup.mem_subgroupOf.mp ht)
      rw [Subgroup.coe_pow, ← hd, diagU_pow, show d ^ 5 = 1 from funext hd1, diagU_one]
      rfl
    rw [this, map_one]
  have hTcomm : ∀ s ∈ torusBar K f, ∀ t ∈ torusBar K f, s * t = t * s := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    obtain ⟨d, -, -, hd⟩ := mem_torusSU_iff.mp (Subgroup.mem_subgroupOf.mp hs)
    obtain ⟨d', -, -, hd'⟩ := mem_torusSU_iff.mp (Subgroup.mem_subgroupOf.mp ht)
    show (s : GL (Fin 5) K) * t = t * s
    rw [← hd, ← hd', diagU_mul, diagU_mul, mul_comm]
  obtain ⟨S₀, hS₀L, hS₀ne, hS₀2, hAS₀, hS₀comm⟩ := h.A₀_invariant
  have hA₀pow : ∀ g ∈ A₀, g ^ 5 = 1 := fun g hg => by
    have := h.A₀_elem
    exact elemPow_eq_one_of_isElementaryAbelian g hg
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ↥(A₀.subgroupOf L) →* StatedProj (unitarySU 2 f K 5),
      ∀ x, ρ x = ε₀ (x : ↥L) := ⟨ε₀.comp (A₀.subgroupOf L).subtype, fun x => rfl⟩
  have hAinj : Function.Injective ρ := by
    intro x y hxy
    have hx5 : ((x : ↥L)) ^ 5 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hA₀pow _ (Subgroup.mem_subgroupOf.mp x.2))
    have hy5 : ((y : ↥L)) ^ 5 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hA₀pow _ (Subgroup.mem_subgroupOf.mp y.2))
    rw [hρ, hρ] at hxy
    exact Subtype.ext (hε₀.eq_of_map_eq hx5 hy5 hxy)
  have hAcard : Nat.card ρ.range = 25 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hAinj).toEquiv.symm,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.A₀_le).toEquiv, h.A₀_card]
    norm_num
  have hSb_ne : (S₀.subgroupOf L).map ε₀ ≠ ⊥ := by
    intro hbot
    apply hS₀ne
    have hcent : ∀ s ∈ S₀, ∀ a ∈ A₀, s * a = a * s := by
      intro s hs a ha
      have h1 : ε₀ ⟨s, hS₀L hs⟩ = 1 := by
        have : ε₀ ⟨s, hS₀L hs⟩ ∈ (S₀.subgroupOf L).map ε₀ :=
          ⟨⟨s, hS₀L hs⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
        rw [hbot] at this
        exact this
      have h3 := hε₀.central (show (⟨s, hS₀L hs⟩ : ↥L) ∈ ε₀.ker from h1)
      have := Subgroup.mem_center_iff.mp h3 ⟨a, h.A₀_le ha⟩
      exact (congrArg Subtype.val this).symm
    refine hS₀comm.trans (eq_bot_iff.mpr (Subgroup.commutator_le.mpr fun s hs a ha => ?_))
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hcent s hs a ha)
  have hSb2 : IsPGroup 2 ((S₀.subgroupOf L).map ε₀) := by
    intro x
    obtain ⟨y, hy, hyx⟩ := x.2
    obtain ⟨k, hk⟩ := hS₀2 ⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩
    refine ⟨k, Subtype.ext ?_⟩
    have hy' : y ^ (2 ^ k) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [Subgroup.coe_pow, ← hyx, ← map_pow, hy', map_one]
    rfl
  have hAS : ∀ a ∈ ρ.range, ∀ s ∈ (S₀.subgroupOf L).map ε₀,
      a * s * a⁻¹ ∈ (S₀.subgroupOf L).map ε₀ := by
    rintro _ ⟨a₀, rfl⟩ _ ⟨s₀, hs₀, rfl⟩
    refine ⟨(a₀ : ↥L) * s₀ * (a₀ : ↥L)⁻¹, Subgroup.mem_subgroupOf.mpr ?_,
      by rw [hρ, map_mul, map_mul, map_inv]⟩
    have ha₀ := Subgroup.mem_subgroupOf.mp a₀.2
    have hs₀' := Subgroup.mem_subgroupOf.mp hs₀
    exact (Subgroup.mem_normalizer_iff.mp (hAS₀ ha₀) _).mp hs₀'
  have hDiag : ∀ X : Subgroup (StatedProj (unitarySU 2 f K 5)), (∀ x ∈ X, x ^ 5 = 1) →
      (∀ x ∈ X, ∀ y ∈ X, x * y = y * x) →
      (∀ (a : G) (ha : a ∈ A₀),
        ε₀ (Subgroup.inclusion (h.A₀_le_F.trans h.F_le) ⟨a, ha⟩) ∈ X) →
      ∃ α : MulAut (StatedProj (unitarySU 2 f K 5)), ∀ x ∈ X, α x ∈ torusBar K f := by
    intro X hXe hXc hAX
    refine toral_conj_of_contains hU h5 h25 X ρ.range ((S₀.subgroupOf L).map ε₀) ?_ hAcard hXe
      hXc hSb_ne hSb2 hAS
    rintro _ ⟨y, rfl⟩
    rw [hρ]
    exact hAX (y : G) (Subgroup.mem_subgroupOf.mp y.2)
  obtain ⟨ε, hε, hFT₁, hFT₂⟩ := exists_toral_quot_aut ε₀ hε₀ hTexp hTcomm h.F_le h.A₀_le_F hDiag
    h.F_exp h.F_comm h.maximal
  have hVexp : ∀ d : Heart K, d ^ 5 = 1 := by
    intro d
    obtain ⟨d', rfl⟩ := heartMk_surjective d
    rw [← map_pow]
    have : d' ^ 5 = 1 := Subtype.ext (funext fun i => d'.2.1 i)
    rw [this, map_one]
  exact ⟨K, hKf, hKfin, ⟨ζ, hζ'⟩,
    WCtx.ofCentralQuot hVexp SH (MonoidHom.id (StatedProj (unitarySU 2 f K 5)))
      (SymCtx.isCentralPQuot_of_bijective _ Function.bijective_id 5) ε hε h.F_le h.F_exp hFT₁ hFT₂⟩

theorem kf123Row12 : KF123Row 12 := by
  intro G _ _ p L A₀ F h hmodel
  obtain ⟨K, hKf, hKfin, hζ, ⟨S⟩⟩ := exists_r12ctx h.toCore hmodel
  have hp5 : p = 5 := hmodel.1
  subst hp5
  exact S.rowData hζ hmodel

theorem kf123NTRow12 : KF123NTRow 12 := by
  intro G _ _ p L A₀ F h hmodel y hyL hyF
  obtain ⟨K, hKf, hKfin, hζ, ⟨S⟩⟩ := exists_r12ctx h.toCore hmodel
  have hp5 : p = 5 := hmodel.1
  subst hp5
  have hpowF : ∀ a : F, a ^ 5 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp h.F_elem.exponent_dvd_p
  exact S.not_isAutTransvection hζ (fun α hα ht => perm_five_aut_inner α hα ht) hpowF hyL hyF

end CFSG.RankThree.PartOne
