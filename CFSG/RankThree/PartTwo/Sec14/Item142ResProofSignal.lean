module

public import CFSG.RankThree.PartTwo.Sec14.Item143StepsProofLThree
import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
import CFSG.RankThree.PartTwo.Sec13.Item13K410

public section

namespace CFSG.RankThree.PartTwo.Sec14.Proof142Res

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec13 (IsLThreePi mem_centMod_of_mk_commute mul_mem_of_mem_centMod)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix (ProjGenLinGroup GeneralLinearGroup)

section Abelian

variable {X : Type*} [Group X] [Finite X]

theorem exists_signal_of_abelian {C A₀ : Subgroup X}
    (hcomm : ∀ x ∈ A₀, ∀ y ∈ A₀, x * y = y * x)
    (hnorm : C ≤ Subgroup.normalizer (A₀ : Set X)) (hcube : ∀ s ∈ C, s ^ 3 ∈ A₀) :
    ∃ W : Subgroup X, ¬ 3 ∣ Nat.card W ∧ C ≤ Subgroup.normalizer (W : Set X) ∧
      ∀ U : Subgroup X, U ≤ C → ¬ 3 ∣ Nat.card U → U ≤ W := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set m := ordCompl[3] (Nat.card A₀) with hm
  have hA₀0 : Nat.card A₀ ≠ 0 := Nat.card_pos.ne'
  have hm3 : Nat.Coprime 3 m := Nat.coprime_ordCompl Nat.prime_three hA₀0
  let W : Subgroup X :=
    { carrier := {x | x ∈ A₀ ∧ x ^ m = 1}
      mul_mem' := by
        rintro x y ⟨hx, hxm⟩ ⟨hy, hym⟩
        refine ⟨A₀.mul_mem hx hy, ?_⟩
        rw [(show Commute x y from hcomm x hx y hy).mul_pow, hxm, hym, one_mul]
      one_mem' := ⟨A₀.one_mem, one_pow m⟩
      inv_mem' := by
        rintro x ⟨hx, hxm⟩
        exact ⟨A₀.inv_mem hx, by rw [inv_pow, hxm, inv_one]⟩ }
  have hmemW : ∀ x : X, x ∈ W ↔ x ∈ A₀ ∧ x ^ m = 1 := fun x => Iff.rfl
  refine ⟨W, ?_, ?_, ?_⟩
  ·
    intro h3
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := W) 3 h3
    have hw' : orderOf (w : X) = 3 := by rw [Subgroup.orderOf_coe, hw]
    have hdvd : orderOf (w : X) ∣ m := orderOf_dvd_of_pow_eq_one ((hmemW _).mp w.2).2
    rw [hw'] at hdvd
    exact Nat.Prime.one_lt Nat.prime_three |>.ne' (Nat.Coprime.eq_one_of_dvd hm3 hdvd)
  ·
    intro c hc
    have hcA := hnorm hc
    rw [Subgroup.mem_normalizer_iff] at hcA ⊢
    intro x
    rw [hmemW, hmemW, ← hcA x]
    refine and_congr_right fun _ => ?_
    rw [conj_pow]
    constructor
    · intro h
      rw [h, mul_one, mul_inv_cancel]
    · intro h
      have h2 : x ^ m = c⁻¹ * (c * x ^ m * c⁻¹) * c := by group
      rw [h2, h, mul_one, inv_mul_cancel]
  ·
    intro U hUC hU3 u hu
    have hcop : Nat.Coprime 3 (orderOf u) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h =>
        hU3 (h.trans (Subgroup.orderOf_dvd_natCard U hu))
    have huA : u ∈ A₀ := by
      obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * 3 + b * (orderOf u : ℤ) = 1 := by
        obtain ⟨a, b, h⟩ := Nat.isCoprime_iff_coprime.mpr hcop
        exact ⟨a, b, by exact_mod_cast h⟩
      have e : u = (u ^ 3) ^ a * (u ^ orderOf u) ^ b := by
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add,
          show ((3 : ℕ) : ℤ) * a + (orderOf u : ℤ) * b = 1 by push_cast; linarith, zpow_one]
      rw [e, pow_orderOf_eq_one, one_zpow, mul_one]
      exact A₀.zpow_mem (hcube u (hUC hu)) a
    refine ⟨huA, orderOf_dvd_iff_pow_eq_one.mp ?_⟩
    have hdvd : orderOf u ∣ ordProj[3] (Nat.card A₀) * m := by
      rw [hm, Nat.ordProj_mul_ordCompl_eq_self]
      exact Subgroup.orderOf_dvd_natCard A₀ huA
    exact (Nat.Coprime.pow_right _ hcop.symm).dvd_of_dvd_mul_left hdvd

end Abelian

section Point

@[expose] def SignalPoint {X : Type*} [Group X] (b : X) : Prop :=
  ∃ W : Subgroup X, ¬ 3 ∣ Nat.card W ∧
    Subgroup.centralizer ({b} : Set X) ≤ Subgroup.normalizer (W : Set X) ∧
    ∀ U : Subgroup X, U ≤ Subgroup.centralizer ({b} : Set X) → ¬ 3 ∣ Nat.card U → U ≤ W

theorem signalAt_of_signalPoint {X : Type} [Group X] {b : X} (h : SignalPoint b)
    (E : Subgroup X) : SignalAt E b := by
  obtain ⟨W, hW3, hWN, hWle⟩ := h
  exact ⟨W, hW3, hWN, fun U hU hU3 _ => hWle U hU hU3⟩

theorem map_centralizer_singleton_mulEquiv {X Y : Type*} [Group X] [Group Y] (ψ : X ≃* Y)
    (b : X) :
    (Subgroup.centralizer ({b} : Set X)).map ψ.toMonoidHom =
      Subgroup.centralizer ({ψ b} : Set Y) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    change ψ x * ψ b = ψ b * ψ x
    rw [← map_mul, ← map_mul, hx]
  · intro hy
    refine ⟨ψ.symm y, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    apply ψ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy]

theorem signalPoint_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (ψ : X ≃* Y) {b : X}
    (h : SignalPoint (ψ b)) : SignalPoint b := by
  obtain ⟨W, hW3, hWN, hWle⟩ := h
  have hcen := map_centralizer_singleton_mulEquiv ψ b
  refine ⟨W.map ψ.symm.toMonoidHom, ?_, ?_, ?_⟩
  · rwa [Subgroup.card_map_of_injective ψ.symm.injective]
  · intro g hg
    have hψg : ψ g ∈ Subgroup.normalizer (W : Set Y) :=
      hWN (hcen ▸ Subgroup.mem_map_of_mem ψ.toMonoidHom hg)
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact ⟨ψ g, hψg, by simp⟩
  · intro U hU hU3
    have hUC : U.map ψ.toMonoidHom ≤ Subgroup.centralizer ({ψ b} : Set Y) :=
      hcen ▸ Subgroup.map_mono hU
    have hU3' : ¬ 3 ∣ Nat.card (U.map ψ.toMonoidHom) := by
      rwa [Subgroup.card_map_of_injective ψ.injective]
    intro u hu
    refine ⟨ψ u, hWle _ hUC hU3' ⟨u, hu, rfl⟩, by simp⟩

end Point

theorem exists_model_of_isLThreePi {X : Type} [Group X] (hX : IsLThreePi X) :
    ∃ (π : Bool) (p f : ℕ) (K : Type) (_ : Field K), PiField π p f K ∧ ModThree π (p ^ f) ∧
      Nonempty (X ≃* projImage (slPi π 3 (p ^ f) K)) := by
  obtain ⟨p, e, hp, he, hL⟩ := hX
  have hpp : p.Prime := hp.out
  rcases hL with ⟨hq3, ⟨φ⟩⟩ | ⟨hq3, ⟨φ⟩⟩
  · refine ⟨true, p, e, GaloisField p e, inferInstance, ⟨hpp, he, ?_⟩, hq3,
      ⟨φ.trans (MulEquiv.subgroupCongr (projSL_eq_projImage _ _))⟩⟩
    rw [GaloisField.card p e (by omega)]
    rfl
  · have hK : PiField false p e (GaloisField p (2 * e)) := ⟨hpp, he, by
      rw [GaloisField.card p (2 * e) (by omega)]
      change p ^ (2 * e) = (p ^ e) ^ 2
      rw [← pow_mul, mul_comm]⟩
    exact ⟨false, p, e, GaloisField p (2 * e), inferInstance, hK, hq3,
      ⟨φ.trans (MulEquiv.subgroupCongr (projSU_eq_projImage _ _))⟩⟩

section Lift

variable {K : Type} [Field K]

theorem det_scalar_units (c : Kˣ) :
    GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) = c ^ 3 :=
  Units.ext (by rw [GeneralLinearGroup.val_det_apply, det_scalar, Units.val_pow_eq_pow_val])

theorem pow_three_eq_one_of_conj_inv {g h : GL (Fin 3) K}
    (hdet : GeneralLinearGroup.det g = 1) (hg3 : g ^ 3 ∈ StatedScalars (Fin 3) K)
    (hconj : h * g * h⁻¹ * g ∈ StatedScalars (Fin 3) K) : g ^ 3 = 1 := by
  obtain ⟨μ, hμ⟩ := hg3
  obtain ⟨lam, hlam⟩ := hconj
  have hsc : ∀ (c : Kˣ) (A : GL (Fin 3) K),
      A * GeneralLinearGroup.scalar (Fin 3) c = GeneralLinearGroup.scalar (Fin 3) c * A :=
    fun c A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c A).eq
  have h1 : h * g * h⁻¹ = GeneralLinearGroup.scalar (Fin 3) lam * g⁻¹ := by
    rw [hlam]
    group
  have hlam3 : lam ^ 3 = 1 := by
    have := congrArg GeneralLinearGroup.det h1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hdet, det_scalar_units, mul_one,
      mul_inv_cancel, inv_one, mul_one] at this
    exact this.symm
  have hμ3 : μ ^ 3 = 1 := by
    have := congrArg GeneralLinearGroup.det hμ
    rwa [det_scalar_units, map_pow, hdet, one_pow] at this
  have hμinv : GeneralLinearGroup.scalar (Fin 3) μ = GeneralLinearGroup.scalar (Fin 3) μ⁻¹ := by
    have e1 : (h * g * h⁻¹) ^ 3 = GeneralLinearGroup.scalar (Fin 3) μ := by
      rw [conj_pow, ← hμ, hsc, mul_inv_cancel_right]
    have e2 : (GeneralLinearGroup.scalar (Fin 3) lam * g⁻¹) ^ 3 =
        GeneralLinearGroup.scalar (Fin 3) μ⁻¹ := by
      rw [(CFSG.ClassicalGroups.UnitaryFlag.commute_scalar lam g⁻¹).symm.mul_pow, ← map_pow,
        hlam3, map_one, one_mul, inv_pow, ← hμ, map_inv]
    rw [← e1, h1, e2]
  have hμ1 : μ = 1 := by
    have hμe := scalar_injective_three hμinv
    have hμμ : μ * μ = 1 := by
      calc μ * μ = μ * μ⁻¹ := by rw [← hμe]
        _ = 1 := mul_inv_cancel μ
    calc μ = μ ^ 3 := by rw [pow_three, hμμ, mul_one]
      _ = 1 := hμ3
  rw [← hμ, hμ1, map_one]

@[expose] noncomputable def centP (L : Subgroup (GL (Fin 3) K)) (y : GL (Fin 3) K) :
    Subgroup (projImage L) :=
  (Subgroup.centralizer ({ProjGenLinGroup.mk y} : Set (ProjGenLinGroup (Fin 3) K))).subgroupOf
    (projImage L)

theorem mem_centP_iff {L : Subgroup (GL (Fin 3) K)} {y : GL (Fin 3) K} {s : projImage L} :
    s ∈ centP L y ↔
      (s : ProjGenLinGroup (Fin 3) K) * ProjGenLinGroup.mk y =
        ProjGenLinGroup.mk y * (s : ProjGenLinGroup (Fin 3) K) := by
  rw [centP, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]

theorem exists_signal_centMod {π : Bool} {p f : ℕ} (hK : PiField π p f K) {y : GL (Fin 3) K}
    (hTcomm : ∀ a ∈ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer ({y} : Set (GL (Fin 3) K)),
      ∀ c ∈ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer ({y} : Set (GL (Fin 3) K)), a * c = c * a)
    (hMcube : ∀ m ∈ centMod (slPi π 3 (p ^ f) K) y,
      m ^ 3 ∈ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer ({y} : Set (GL (Fin 3) K))) :
    ∃ W : Subgroup (projImage (slPi π 3 (p ^ f) K)), ¬ 3 ∣ Nat.card W ∧
      centP (slPi π 3 (p ^ f) K) y ≤
        Subgroup.normalizer (W : Set (projImage (slPi π 3 (p ^ f) K))) ∧
      ∀ U : Subgroup (projImage (slPi π 3 (p ^ f) K)), U ≤ centP (slPi π 3 (p ^ f) K) y →
        ¬ 3 ∣ Nat.card U → U ≤ W := by
  have := hK.finite
  set T := slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer ({y} : Set (GL (Fin 3) K)) with hT
  set A₀ : Subgroup (projImage (slPi π 3 (p ^ f) K)) :=
    (T.subgroupOf (slPi π 3 (p ^ f) K)).map (projOf (slPi π 3 (p ^ f) K)) with hA₀
  have hmemA₀ : ∀ a : projImage (slPi π 3 (p ^ f) K), a ∈ A₀ ↔
      ∃ t ∈ T, ProjGenLinGroup.mk t = (a : ProjGenLinGroup (Fin 3) K) := by
    intro a
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, Subgroup.mem_subgroupOf.mp ht, rfl⟩
    · rintro ⟨t, ht, hta⟩
      exact ⟨⟨t, ht.1⟩, Subgroup.mem_subgroupOf.mpr ht, Subtype.ext hta⟩
  have hcomm : ∀ x ∈ A₀, ∀ x' ∈ A₀, x * x' = x' * x := by
    intro x hx x' hx'
    obtain ⟨t, ht, htx⟩ := (hmemA₀ x).mp hx
    obtain ⟨t', ht', htx'⟩ := (hmemA₀ x').mp hx'
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← htx, ← htx', ← map_mul, ← map_mul,
      hTcomm t ht t' ht']
  have hliftC : ∀ s ∈ centP (slPi π 3 (p ^ f) K) y,
      ∃ m ∈ centMod (slPi π 3 (p ^ f) K) y,
        ProjGenLinGroup.mk m = (s : ProjGenLinGroup (Fin 3) K) := by
    intro s hs
    obtain ⟨m, hmL, hms⟩ := Subgroup.mem_map.mp s.2
    refine ⟨m, mem_centMod_of_mk_commute hmL ?_, hms⟩
    rw [hms]
    exact (mem_centP_iff.mp hs).symm
  have hconjA : ∀ s ∈ centP (slPi π 3 (p ^ f) K) y, ∀ a ∈ A₀, s * a * s⁻¹ ∈ A₀ := by
    intro s hs a ha
    obtain ⟨m, hmM, hms⟩ := hliftC s hs
    obtain ⟨t, ht, hta⟩ := (hmemA₀ a).mp ha
    refine (hmemA₀ _).mpr ⟨m * t * m⁻¹, mul_mem_of_mem_centMod hmM ht, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv, hms,
      hta]
  have hnorm : centP (slPi π 3 (p ^ f) K) y ≤
      Subgroup.normalizer (A₀ : Set (projImage (slPi π 3 (p ^ f) K))) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro a
    refine ⟨fun ha => hconjA s hs a ha, fun ha => ?_⟩
    have := hconjA s⁻¹ (inv_mem hs) _ ha
    simpa [mul_assoc] using this
  have hcube : ∀ s ∈ centP (slPi π 3 (p ^ f) K) y, s ^ 3 ∈ A₀ := by
    intro s hs
    obtain ⟨m, hmM, hms⟩ := hliftC s hs
    refine (hmemA₀ _).mpr ⟨m ^ 3, hMcube m hmM, ?_⟩
    rw [Subgroup.coe_pow, map_pow, hms]
  have : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective (ProjGenLinGroup.mk : GL (Fin 3) K →* _) ProjGenLinGroup.mk_surjective
  exact exists_signal_of_abelian hcomm hnorm hcube

theorem signalPoint_of_type1 {π : Bool} {p f : ℕ} (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) {g : GL (Fin 3) K} (hgL : g ∈ slPi π 3 (p ^ f) K)
    (htype1 : Type123 π (p ^ f) K g 1) :
    SignalPoint (⟨ProjGenLinGroup.mk g, ⟨g, hgL, rfl⟩⟩ : projImage (slPi π 3 (p ^ f) K)) := by
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hgH : g ∈ glPi π 3 (p ^ f) K := slPi_le_glPi hπ hgL
  obtain ⟨τ', hτ', hτ'1, z₀, hz₀, k₀, hk₀, hD₀⟩ := htype1
  have hz₀S := mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz₀
  have hgZ : g ∉ zPi π 3 (p ^ f) K := by
    intro hgZ
    have hgS := mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hgZ
    have hS : k₀⁻¹ * (g * z₀) * k₀ ∈ StatedScalars (Fin 3) K := by
      rw [show k₀⁻¹ * (g * z₀) * k₀ = g * z₀ from by
        rw [mul_assoc, ← commute_of_mem_statedScalars (mul_mem hgS hz₀S) k₀,
          inv_mul_cancel_left]]
      exact mul_mem hgS hz₀S
    rw [hD₀] at hS
    obtain ⟨μ, hμ⟩ := hS
    have h2 : ((GeneralLinearGroup.scalar (Fin 3) μ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal ![τ', τ' ^ 2, 1] := by
      rw [hμ, coe_diagTau_eq_diagonal]
    have e0 := congrFun (congrFun h2 0) 0
    have e2 := congrFun (congrFun h2 2) 2
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Matrix.diagonal_apply_eq] at e0 e2
    change (μ : K) = τ' at e0
    change (μ : K) = 1 at e2
    exact hτ'1 (e0.symm.trans e2)
  have hg3Z : g ^ 3 ∈ zPi π 3 (p ^ f) K := by
    have e1 : (g * z₀) ^ 3 = 1 := by
      rw [show g * z₀ = k₀ * diagTau hτ' * k₀⁻¹ from by rw [← hD₀]; group, conj_pow,
        diagTau_pow_three hτ', mul_one, mul_inv_cancel]
    have e2 : (g * z₀) ^ 3 = g ^ 3 * z₀ ^ 3 :=
      (Commute.mul_pow (commute_of_mem_statedScalars hz₀S g) 3)
    have : g ^ 3 = (z₀ ^ 3)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← e2, e1]
    rw [this]
    exact inv_mem (pow_mem hz₀ 3)
  have htype1 : Type123 π (p ^ f) K g 1 := ⟨τ', hτ', hτ'1, z₀, hz₀, k₀, hk₀, hD₀⟩
  obtain ⟨y, ⟨z, hz, rfl⟩, hcase⟩ := rank3II_4_10_one hK hq hτ hτ1 hgH hgZ hg3Z
  rcases hcase with ⟨-, ⟨eT⟩, hrel⟩ | ⟨⟨k', hk', e, he, hD⟩, -, -⟩ | ⟨-, hirr, -⟩
  rotate_left
  ·
    exfalso
    have he3 : (e : K) ^ 3 = 1 := by
      rcases he with he | he <;> rw [he]
      · exact hτ
      · rw [← pow_mul, pow_mul', hτ, one_pow]
    have he1 : e ≠ 1 := by
      rintro rfl
      rw [Units.val_one] at he
      have hτ0 : τ ≠ 0 := by
        rintro rfl
        simp at hτ
      rcases he with he | he
      · exact hτ1 he.symm
      · apply hτ1
        calc τ = τ ^ 3 / τ ^ 2 := by field_simp
          _ = 1 := by rw [hτ, ← he, div_one]
    exact not_type123_one_two hK hq htype1 ⟨e, he3, he1, z, hz, k', hk', hD⟩
  ·
    exact absurd ⟨hgZ, hg3Z, hirr⟩ (not_type123_three_of_one hK hq htype1)
  have hTcomm : ∀ a ∈ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer ({g * z} : Set (GL (Fin 3) K)),
      ∀ c ∈ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer ({g * z} : Set (GL (Fin 3) K)),
        a * c = c * a := by
    intro a ha c hc
    have h1 : (⟨a, ha⟩ : ↥(slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {g * z})) * ⟨c, hc⟩ =
        ⟨c, hc⟩ * ⟨a, ha⟩ :=
      eT.injective (by rw [map_mul, map_mul, mul_comm])
    exact congrArg Subtype.val h1
  have hMcube : ∀ m ∈ centMod (slPi π 3 (p ^ f) K) (g * z),
      m ^ 3 ∈ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer ({g * z} : Set (GL (Fin 3) K)) := by
    intro m hm
    set T := slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer ({g * z} : Set (GL (Fin 3) K)) with hT
    set M := centMod (slPi π 3 (p ^ f) K) (g * z) with hM
    have hnormal : (T.subgroupOf M).Normal := ⟨fun t ht m' => by
      rw [Subgroup.mem_subgroupOf] at ht ⊢
      exact mul_mem_of_mem_centMod m'.2 ht⟩
    have hidx : (T.subgroupOf M).index = 3 := hrel
    have h1 := Subgroup.pow_index_mem (T.subgroupOf M) (⟨m, hm⟩ : M)
    rw [hidx, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hmkz : ProjGenLinGroup.mk z = 1 :=
    mk_eq_one_iff_mem_statedScalars.mpr (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz)
  have hC : Subgroup.centralizer
      ({(⟨ProjGenLinGroup.mk g, ⟨g, hgL, rfl⟩⟩ : projImage (slPi π 3 (p ^ f) K))} :
        Set (projImage (slPi π 3 (p ^ f) K))) =
      centP (slPi π 3 (p ^ f) K) (g * z) := by
    ext s
    rw [mem_centP_iff, map_mul, hmkz, mul_one, Subgroup.mem_centralizer_singleton_iff,
      Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_mul]
  obtain ⟨W, hW3, hWN, hWle⟩ := exists_signal_centMod hK hTcomm hMcube
  exact ⟨W, hW3, hC ▸ hWN, hC ▸ hWle⟩

theorem signalPoint_projImage {π : Bool} {p f : ℕ} (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) {b w : projImage (slPi π 3 (p ^ f) K)} (hb1 : b ≠ 1)
    (hb3 : b ^ 3 = 1) (hw : w * b * w⁻¹ = b⁻¹) : SignalPoint b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨g, hgL, hgb⟩ := Subgroup.mem_map.mp b.2
  obtain ⟨h, -, hhw⟩ := Subgroup.mem_map.mp w.2
  have hdet : GeneralLinearGroup.det g = 1 :=
    Units.ext (by rw [GeneralLinearGroup.val_det_apply]; exact ((mem_slPi_iff hπ).mp hgL).2)
  have hg3S : g ^ 3 ∈ StatedScalars (Fin 3) K := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_pow, hgb, ← Subgroup.coe_pow, hb3,
      Subgroup.coe_one]
  have hconj : h * g * h⁻¹ * g ∈ StatedScalars (Fin 3) K := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_mul, map_mul, map_mul, map_inv, hgb, hhw,
      ← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hw,
      inv_mul_cancel, Subgroup.coe_one]
  have hg3 : g ^ 3 = 1 := pow_three_eq_one_of_conj_inv hdet hg3S hconj
  have hgS : g ∉ StatedScalars (Fin 3) K := by
    intro hgS
    apply hb1
    apply Subtype.ext
    rw [← hgb, mk_eq_one_iff_mem_statedScalars.mpr hgS, Subgroup.coe_one]
  have hgZ : g ∉ zPi π 3 (p ^ f) K := by
    rw [zPi_eq hπ hq' hτ hτ1]
    exact fun h => hgS h.2
  have hg1 : g ≠ 1 := fun h1 => hgS (h1 ▸ one_mem _)
  have hord : orderOf g = 3 := orderOf_eq_prime hg3 hg1
  obtain ⟨k, hk, hkD⟩ := rank3II_4_10_three hK hq hτ hτ1 hgL hgZ hord
  have htype1 : Type123 π (p ^ f) K g 1 :=
    ⟨τ, hτ, hτ1, 1, one_mem _, k, hk, by rw [mul_one]; exact hkD⟩
  have hb : b = ⟨ProjGenLinGroup.mk g, ⟨g, hgL, rfl⟩⟩ := Subtype.ext hgb.symm
  rw [hb]
  exact signalPoint_of_type1 hK hq hgL htype1

end Lift

end CFSG.RankThree.PartTwo.Sec14.Proof142Res

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG.RankThree.PartTwo.Sec14.Proof142Res

theorem ks142SignalLThreePi : KS142SignalLThreePi := by
  intro X _ _ hX E hE _ htr b hbE hb1
  obtain ⟨π, p, f, K, _, hK, hq, ⟨ψ⟩⟩ := exists_model_of_isLThreePi hX
  obtain ⟨w, -, hw⟩ := htr b hbE hb1 b⁻¹ (E.inv_mem hbE) (inv_ne_one.mpr hb1)
  have hb3 : b ^ 3 = 1 := hE.2 b hbE
  refine signalAt_of_signalPoint (signalPoint_of_mulEquiv ψ ?_) E
  refine signalPoint_projImage hK hq (w := ψ w) ?_ ?_ ?_
  · exact fun h => hb1 (ψ.injective (h.trans ψ.map_one.symm))
  · rw [← map_pow, hb3, map_one]
  · rw [← map_inv, ← map_mul, ← map_mul, hw, map_inv]

end CFSG.RankThree.PartTwo.Sec14
