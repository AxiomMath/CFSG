module

public import CFSG.RankThree.PartOne.KF.R9Torus
public import CFSG.RankThree.PartOne.KF.U4Multiplier
public import CFSG.RankThree.PartOne.KF.RowCore
public import CFSG.RankThree.PartOne.KF.Reduction123

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.KFU

variable {G : Type} [Group G]

theorem perm_four_pow_prime_eq_one {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (π : Equiv.Perm (Fin 4)) (hπ : π ^ p = 1) : π = 1 := by
  have h1 : orderOf π ∣ p := orderOf_dvd_of_pow_eq_one hπ
  have h2 : orderOf π ∣ 24 := by
    have h24 : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm]
      simp [Nat.factorial]
    rw [← h24]
    exact orderOf_dvd_natCard π
  have hcop : Nat.Coprime p 24 := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => ?_
    have hle : p ≤ 24 := Nat.le_of_dvd (by norm_num) hd
    interval_cases p <;> first | omega | (norm_num at hp)
  have h3 : orderOf π ∣ Nat.gcd p 24 := Nat.dvd_gcd h1 h2
  rw [hcop] at h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

theorem exists_r9ctx_model [Finite G] (hZ : PSUFourEvenCenterTrivial) {p : ℕ}
    {L A₀ F : Subgroup G} (h : Table123Core p L A₀ F) (hmodel : RowModel p L 9) :
    ∃ (f : ℕ) (K : Type) (_ : Field K), 1 ≤ f ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 4 2 f ∧
        Nonempty (R9Ctx p L F f K) := by
  obtain ⟨f, hf1, hpq, hmod⟩ := hmodel
  have hmod0 := hmod
  have hp := h.prime
  have h5 := h.five_le
  have hf2 : 2 ≤ f := by
    by_contra hlt
    have hf1' : f = 1 := by omega
    subst hf1'
    have h3' : p ∣ 3 := by simpa using hpq
    have := Nat.le_of_dvd (by norm_num) h3'
    omega
  have hZL : Subgroup.center L = ⊥ := hZ L f hf2 h.quasisimple hmod
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hmod
  have hU : UnitaryFieldData 2 f K := ⟨Nat.prime_two, by omega, by rw [hK, ← pow_mul, mul_comm]⟩
  have hFexp : ∀ x ∈ F.subgroupOf L, x ^ p = 1 := by
    intro x hx
    have hxF : (x : G) ∈ F := Subgroup.mem_subgroupOf.mp hx
    apply Subtype.ext
    have := h.F_elem
    simpa using elemPow_eq_one_of_isElementaryAbelian (x : G) hxF
  have hFcomm : ∀ x ∈ F.subgroupOf L, ∀ y ∈ F.subgroupOf L, x * y = y * x := by
    intro x hx y hy
    apply Subtype.ext
    have hxF : (x : G) ∈ F := Subgroup.mem_subgroupOf.mp hx
    have hyF : (y : G) ∈ F := Subgroup.mem_subgroupOf.mp hy
    show (x : G) * (y : G) = (y : G) * (x : G)
    exact congrArg Subtype.val (h.F_elem.is_comm.comm ⟨(x : G), hxF⟩ ⟨(y : G), hyF⟩)
  obtain ⟨ψ, hψ⟩ := exists_diag_iso_le (K := K) (by omega) hK hp hpq hZL e (F.subgroupOf L)
    hFexp hFcomm
  let φ : unitarySU 2 f K 4 →* G := L.subtype.comp ψ.toMonoidHom
  let T₀ : Subgroup (unitarySU 2 f K 4) := (torusSU p 4 K).subgroupOf (unitarySU 2 f K 4)
  let Fm : Subgroup G := T₀.map φ
  have hFm_le : Fm ≤ L := by
    rintro _ ⟨g, -, rfl⟩
    exact (ψ g).2
  have hdiag : ∀ g : unitarySU 2 f K 4, g ∈ T₀ → ∃ d : Fin 4 → Kˣ, (∀ i, d i ^ p = 1) ∧
      ∏ i, d i = 1 ∧ diagU d = (g : GL (Fin 4) K) := fun g hg => mem_torusSU_iff.mp hg
  have hFm_comm : ∀ x ∈ Fm, ∀ y ∈ Fm, x * y = y * x := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨g', hg', rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    obtain ⟨d, -, -, hd⟩ := hdiag g hg
    obtain ⟨d', -, -, hd'⟩ := hdiag g' hg'
    show (g : GL (Fin 4) K) * g' = g' * g
    rw [← hd, ← hd', diagU_mul, diagU_mul, mul_comm]
  have hFm_exp : ∀ x ∈ Fm, x ^ p = 1 := by
    rintro _ ⟨g, hg, rfl⟩
    rw [← map_pow]
    have hgp : g ^ p = 1 := by
      apply Subtype.ext
      obtain ⟨d, hd1, -, hd⟩ := hdiag g hg
      rw [Subgroup.coe_pow, ← hd, diagU_pow, show d ^ p = 1 from funext hd1, diagU_one]
      rfl
    rw [hgp, map_one]
  have hFm_elem : IsElementaryAbelian p Fm := by
    have hc : IsMulCommutative Fm := ⟨⟨fun a b => Subtype.ext (hFm_comm _ a.2 _ b.2)⟩⟩
    have hexp : Monoid.exponent Fm ∣ p :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun g => Subtype.ext (hFm_exp _ g.2)
    exact ⟨hexp⟩
  have hFsub : F ≤ Fm := by
    intro x hx
    have hxL : x ∈ L := h.F_le hx
    have hxF' : (⟨x, hxL⟩ : L) ∈ F.subgroupOf L := Subgroup.mem_subgroupOf.mpr hx
    have hg := hψ (ψ.symm ⟨x, hxL⟩) (by rw [MulEquiv.apply_symm_apply]; exact hxF')
    refine ⟨ψ.symm ⟨x, hxL⟩, hg, ?_⟩
    show ((ψ (ψ.symm ⟨x, hxL⟩) : L) : G) = x
    rw [MulEquiv.apply_symm_apply]
  have hFm_cent : Fm ≤ Subgroup.centralizer (A₀ : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact hFm_comm a (hFsub (h.A₀_le_F ha)) x hx
  have hFm_eq : Fm = F := h.F_max Fm hFm_le hFm_elem hFm_cent hFsub
  refine ⟨f, K, hKf, hf1, hmod0, ⟨⟨hp, h5, hU, hf2, hpq, h.F_le, ψ, fun g => ?_⟩⟩⟩
  constructor
  · intro hgF
    exact hψ g (Subgroup.mem_subgroupOf.mpr hgF)
  · intro hg
    have : (ψ g : G) ∈ Fm := ⟨g, hg, rfl⟩
    rwa [hFm_eq] at this

theorem exists_r9ctx [Finite G] (hZ : PSUFourEvenCenterTrivial) {p : ℕ} {L A₀ F : Subgroup G}
    (h : Table123Core p L A₀ F) (hmodel : RowModel p L 9) :
    ∃ (f : ℕ) (K : Type) (_ : Field K), Nonempty (R9Ctx p L F f K) := by
  obtain ⟨f, K, hKf, -, -, hC⟩ := exists_r9ctx_model hZ h hmodel
  exact ⟨f, K, hKf, hC⟩

theorem kf123Row9_of_inputs (hZ : PSUFourEvenCenterTrivial) : KF123Row 9 := by
  intro G _ _ p L A₀ F h hmodel
  obtain ⟨f, K, hKf, ⟨C⟩⟩ := exists_r9ctx hZ h.toCore hmodel
  have hKfin : Finite K := C.hU.finite
  have hζ := C.exists_unit_root
  have hp2 : p ≠ 2 := by have := C.h5; omega
  have hp4 : ¬ p ∣ 4 := fun hd => by
    have := Nat.le_of_dvd (by norm_num) hd
    have := C.h5
    omega
  have S := C.toSymCtx
  exact ⟨hmodel, S.card_F (m := 3) rfl C.hp.pos hζ, ⟨S.weylEquiv C.hp hp2 hζ⟩,
    S.torusImage_eq_closure C.hp hp2 hζ,
    fun _ B hBF hB => S.torusIrreducible C.hp (by norm_num) hp4 B hBF hB,
    fun h11 => absurd h11 (by norm_num)⟩

theorem kf123NTRow9_of_inputs (hZ : PSUFourEvenCenterTrivial) : KF123NTRow 9 := by
  intro G _ _ p L A₀ F h hmodel y hyL hyF
  obtain ⟨f, K, hKf, ⟨C⟩⟩ := exists_r9ctx hZ h.toCore hmodel
  have hKfin : Finite K := C.hU.finite
  have hζ := C.exists_unit_root
  have hp2 : p ≠ 2 := by have := C.h5; omega
  have hpowF : ∀ a : F, a ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp h.F_elem.exponent_dvd_p
  exact C.toSymCtx.not_isAutTransvection C.hp hp2 (by norm_num)
    (fun π hπ => perm_four_pow_prime_eq_one C.hp C.h5 π hπ) hζ
    (fun α hα _ => perm_four_aut_inner α hα) hpowF hyL hyF

theorem kf123Row9_of_multipliers
    (hGA : CFSG.Open.GriessAllModelsStatement) : KF123Row 9 :=
  kf123Row9_of_inputs (psuFourEvenCenterTrivial_of_multipliers hGA)

theorem kf123NTRow9_of_multipliers
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    KF123NTRow 9 :=
  kf123NTRow9_of_inputs (psuFourEvenCenterTrivial_of_multipliers hGA)

end CFSG.RankThree.PartOne
