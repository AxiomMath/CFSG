module

public import CFSG.RankThree.PartTwo.Sec21.Notation
public import CFSG.RankThree.PartOne.KF.SymTorus
public import CFSG.RankThree.PartOne.KF.R9Perm
public import CFSG.RankThree.PartOne.KF.UnitaryModel

public section

namespace CFSG.RankThree.PartTwo.Sec21.U4OddLines

open CFSG CFSG.RankThree CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KFU (diagU diagU_val diagU_injective diagUHom torusVec torusSU
  mem_torusSU_iff symAct coe_symAct symAut symAut_apply symAut_injective movedSub permGL
  permGL_conj_diagU permGL_mem_unitarySU NormPerm normPerm_permGL exists_normPerm
  torus_char_distinct torusSU_le_unitarySU card_movedSub_swap involution_cases
  card_movedSub_ne_prime_of_double_swap exists_isPrimitiveRoot ent)

structure U4OddCtx (G : Type) [Group G] [Finite G] (L A : Subgroup G) (c : G) (f : ℕ)
    (K : Type) [Field K] where
  hU : UnitaryFieldData 2 f K
  hf2 : 2 ≤ f
  hpq : 3 ∣ 2 ^ f + 1
  hAe : CFSG.Assembly.IsElemAbelian 3 A
  hA81 : Nat.card A = 3 ^ 4
  hcA : c ∈ A
  hcL : c ∉ L
  hLc : L ≤ Subgroup.centralizer ({c} : Set G)
  hAL : Nat.card (A ⊓ L : Subgroup G) = 3 ^ 3
  ψ : unitarySU 2 f K 4 ≃* L
  hψ : ∀ g : unitarySU 2 f K 4, (ψ g : G) ∈ A ↔ (g : GL (Fin 4) K) ∈ torusSU 3 4 K

namespace U4OddCtx

variable {G : Type} [Group G] [Finite G] {L A : Subgroup G} {c : G} {f : ℕ} {K : Type}
  [Field K] (C : U4OddCtx G L A c f K)

@[expose] def phi : unitarySU 2 f K 4 →* G := L.subtype.comp C.ψ.toMonoidHom

theorem coe_phi (g : unitarySU 2 f K 4) : C.phi g = ((C.ψ g : L) : G) := rfl

theorem phi_injective : Function.Injective C.phi := fun _ _ hxy =>
  C.ψ.injective (Subtype.ext hxy)

theorem phi_mem_L (g : unitarySU 2 f K 4) : C.phi g ∈ L := (C.ψ g).2

@[expose] noncomputable def torU : torusVec 3 4 K →* unitarySU 2 f K 4 :=
  (diagUHom.comp (torusVec 3 4 K).subtype).codRestrict (unitarySU 2 f K 4) fun d =>
    torusSU_le_unitarySU C.hU C.hpq (mem_torusSU_iff.mpr ⟨d.1, d.2.1, d.2.2, rfl⟩)

theorem coe_torU (d : torusVec 3 4 K) :
    ((C.torU d : unitarySU 2 f K 4) : GL (Fin 4) K) = diagU (d : Fin 4 → Kˣ) := rfl

@[expose] noncomputable def theta : torusVec 3 4 K →* G := C.phi.comp C.torU

theorem theta_apply (d : torusVec 3 4 K) : C.theta d = C.phi (C.torU d) := rfl

theorem theta_mem_A (d : torusVec 3 4 K) : C.theta d ∈ A :=
  (C.hψ _).mpr (mem_torusSU_iff.mpr ⟨d.1, d.2.1, d.2.2, rfl⟩)

theorem theta_mem_L (d : torusVec 3 4 K) : C.theta d ∈ L := C.phi_mem_L _

theorem theta_injective : Function.Injective C.theta := by
  intro d e h
  have h1 := congrArg (fun x : unitarySU 2 f K 4 => (x : GL (Fin 4) K)) (C.phi_injective h)
  exact Subtype.ext (diagU_injective h1)

theorem exists_theta {x : G} (hxA : x ∈ A) (hxL : x ∈ L) : ∃ d, C.theta d = x := by
  set g := C.ψ.symm ⟨x, hxL⟩ with hg
  have hgx : C.phi g = x := by rw [coe_phi, hg, MulEquiv.apply_symm_apply]
  have hgT := (C.hψ g).mp (by rw [← coe_phi, hgx]; exact hxA)
  obtain ⟨d, hd1, hd2, hdg⟩ := mem_torusSU_iff.mp hgT
  refine ⟨⟨d, hd1, hd2⟩, ?_⟩
  rw [theta_apply, ← hgx]
  congr 1
  exact Subtype.ext hdg

include C in
theorem commA {a b : G} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a :=
  congrArg Subtype.val (C.hAe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

include C in
theorem comm_c {x : G} (hx : x ∈ L) : x * c = c * x :=
  Subgroup.mem_centralizer_singleton_iff.mp (C.hLc hx)

theorem decomp {a : G} (ha : a ∈ A) : ∃ (d : torusVec 3 4 K) (i : ℤ), a = C.theta d * c ^ i := by
  have hcomm : ∀ x ∈ A, ∀ i : ℤ, c ^ i * x = x * c ^ i := fun x hx i =>
    ((Commute.zpow_left (C.commA C.hcA hx) i)).eq
  let M : Subgroup G :=
    { carrier := {a | ∃ x ∈ A ⊓ L, ∃ i : ℤ, a = x * c ^ i}
      mul_mem' := by
        rintro _ _ ⟨x, hx, i, rfl⟩ ⟨y, hy, j, rfl⟩
        refine ⟨x * y, (A ⊓ L).mul_mem hx hy, i + j, ?_⟩
        rw [zpow_add]
        calc x * c ^ i * (y * c ^ j) = x * (c ^ i * y) * c ^ j := by group
          _ = x * (y * c ^ i) * c ^ j := by rw [hcomm y (Subgroup.mem_inf.mp hy).1 i]
          _ = x * y * (c ^ i * c ^ j) := by group
      one_mem' := ⟨1, (A ⊓ L).one_mem, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨x, hx, i, rfl⟩
        refine ⟨x⁻¹, (A ⊓ L).inv_mem hx, -i, ?_⟩
        rw [mul_inv_rev, ← zpow_neg, hcomm x⁻¹ (A.inv_mem (Subgroup.mem_inf.mp hx).1) (-i)] }
  have hLM : A ⊓ L ≤ M := fun x hx => ⟨x, hx, 0, by simp⟩
  have hcM : c ∈ M := ⟨1, (A ⊓ L).one_mem, 1, by simp⟩
  have hMA : M ≤ A := by
    rintro _ ⟨x, hx, i, rfl⟩
    exact A.mul_mem (Subgroup.mem_inf.mp hx).1 (A.zpow_mem C.hcA i)
  have hMeq : M = A := by
    apply Subgroup.eq_of_le_of_card_ge hMA
    have h1 : Nat.card (A ⊓ L : Subgroup G) ∣ Nat.card M := Subgroup.card_dvd_of_le hLM
    have h2 : Nat.card M ∣ Nat.card A := Subgroup.card_dvd_of_le hMA
    rw [C.hAL] at h1
    rw [C.hA81] at h2
    obtain ⟨k, hk, hMk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h2
    rw [hMk] at h1
    have hk3 : 3 ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h1
    rcases (by omega : k = 3 ∨ k = 4) with rfl | rfl
    · exfalso
      have hMeq' : A ⊓ L = M := Subgroup.eq_of_le_of_card_ge hLM (by rw [hMk, C.hAL])
      exact C.hcL (Subgroup.mem_inf.mp (hMeq' ▸ hcM)).2
    · rw [hMk, C.hA81]
  obtain ⟨x, hx, i, rfl⟩ : a ∈ M := hMeq ▸ ha
  obtain ⟨d, rfl⟩ := C.exists_theta (Subgroup.mem_inf.mp hx).1 (Subgroup.mem_inf.mp hx).2
  exact ⟨d, i, rfl⟩

include C in
theorem exists_unit_root : ∃ ζ : Kˣ, IsPrimitiveRoot ζ 3 := by
  obtain ⟨z, hz⟩ := exists_isPrimitiveRoot C.hU Nat.prime_three C.hpq
  have hz0 : z ≠ 0 := hz.ne_zero (by norm_num)
  exact ⟨Units.mk0 z hz0, IsPrimitiveRoot.coe_units_iff.mp (by simpa using hz)⟩

include C in
theorem hdist : ∀ i j : Fin 4, i ≠ j → ∃ x ∈ torusSU 3 4 K, ent x i i ≠ ent x j j := by
  obtain ⟨ζ, hζ⟩ := C.exists_unit_root
  intro i j hij
  exact torus_char_distinct hζ.pow_eq_one
    (hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)) i j hij

@[expose] noncomputable def permU : Equiv.Perm (Fin 4) →* unitarySU 2 f K 4 :=
  (permGL (n := 4) (K := K)).codRestrict _ fun σ => permGL_mem_unitarySU C.hU σ

theorem coe_permU (σ : Equiv.Perm (Fin 4)) :
    ((C.permU σ : unitarySU 2 f K 4) : GL (Fin 4) K) = permGL σ := rfl

theorem permU_conj_torU (σ : Equiv.Perm (Fin 4)) (d : torusVec 3 4 K) :
    C.permU σ * C.torU d * (C.permU σ)⁻¹ = C.torU (symAct 3 K σ d) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_permU, coe_torU]
  rw [permGL_conj_diagU]
  rfl

theorem conj_theta (σ : Equiv.Perm (Fin 4)) (d : torusVec 3 4 K) :
    C.phi (C.permU σ) * C.theta d * (C.phi (C.permU σ))⁻¹ = C.theta (symAct 3 K σ d) := by
  rw [theta_apply, theta_apply, ← C.permU_conj_torU, map_mul, map_mul, map_inv]

include C in
theorem conj_zpow_c {x : G} (hx : x ∈ L) (i : ℤ) : x * c ^ i * x⁻¹ = c ^ i := by
  rw [((Commute.zpow_right (show Commute x c from C.comm_c hx) i)).eq, mul_inv_cancel_right]

theorem conj_theta_zpow (σ : Equiv.Perm (Fin 4)) (d : torusVec 3 4 K) (i : ℤ) :
    C.phi (C.permU σ) * (C.theta d * c ^ i) * (C.phi (C.permU σ))⁻¹ =
      C.theta (symAct 3 K σ d) * c ^ i := by
  calc C.phi (C.permU σ) * (C.theta d * c ^ i) * (C.phi (C.permU σ))⁻¹ =
      (C.phi (C.permU σ) * C.theta d * (C.phi (C.permU σ))⁻¹) *
        (C.phi (C.permU σ) * c ^ i * (C.phi (C.permU σ))⁻¹) := by group
    _ = C.theta (symAct 3 K σ d) * c ^ i := by
      rw [C.conj_theta, C.conj_zpow_c (C.phi_mem_L (C.permU σ)) i]

theorem conj_mem_A (σ : Equiv.Perm (Fin 4)) {a : G} (ha : a ∈ A) :
    C.phi (C.permU σ) * a * (C.phi (C.permU σ))⁻¹ ∈ A := by
  obtain ⟨d, i, rfl⟩ := C.decomp ha
  rw [C.conj_theta_zpow]
  exact A.mul_mem (C.theta_mem_A _) (A.zpow_mem C.hcA i)

theorem phi_permU_mem_normalizer (σ : Equiv.Perm (Fin 4)) :
    C.phi (C.permU σ) ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨fun ha => C.conj_mem_A σ ha, fun ha => ?_⟩
  have h := C.conj_mem_A σ⁻¹ ha
  rw [map_inv, map_inv, inv_inv] at h
  convert h using 1
  group

@[expose] noncomputable def permN : Equiv.Perm (Fin 4) →* ↥(Subgroup.normalizer (A : Set G)) where
  toFun σ := ⟨C.phi (C.permU σ), C.phi_permU_mem_normalizer σ⟩
  map_one' := Subtype.ext (by simp)
  map_mul' σ τ := Subtype.ext (by simp [map_mul])

@[expose] noncomputable def actA : Equiv.Perm (Fin 4) →* MulAut A :=
  A.normalizerMonoidHom.comp C.permN

theorem actA_apply_coe (σ : Equiv.Perm (Fin 4)) (a : A) :
    ((C.actA σ a : A) : G) = C.phi (C.permU σ) * a * (C.phi (C.permU σ))⁻¹ := rfl

theorem actA_theta (σ : Equiv.Perm (Fin 4)) (d : torusVec 3 4 K) :
    C.actA σ ⟨C.theta d, C.theta_mem_A d⟩ =
      ⟨C.theta (symAct 3 K σ d), C.theta_mem_A _⟩ :=
  Subtype.ext (C.conj_theta σ d)

theorem actA_c (σ : Equiv.Perm (Fin 4)) : C.actA σ ⟨c, C.hcA⟩ = ⟨c, C.hcA⟩ := by
  apply Subtype.ext
  rw [actA_apply_coe]
  have := C.conj_zpow_c (C.phi_mem_L (C.permU σ)) 1
  simpa using this

theorem actA_mem_starOf (σ : Equiv.Perm (Fin 4)) : C.actA σ ∈ starOf A L :=
  ⟨C.permN σ, Subgroup.mem_subgroupOf.mpr (C.phi_mem_L _), rfl⟩

theorem ext_of_theta_c {φ₁ φ₂ : MulAut A}
    (hθ : ∀ d, φ₁ ⟨C.theta d, C.theta_mem_A d⟩ = φ₂ ⟨C.theta d, C.theta_mem_A d⟩)
    (hc : φ₁ ⟨c, C.hcA⟩ = φ₂ ⟨c, C.hcA⟩) : φ₁ = φ₂ := by
  apply MulEquiv.ext
  intro a
  obtain ⟨d, i, hdi⟩ := C.decomp a.2
  have ha : a = ⟨C.theta d, C.theta_mem_A d⟩ * (⟨c, C.hcA⟩ : A) ^ i :=
    Subtype.ext (by rw [hdi]; rfl)
  rw [ha, map_mul, map_mul, map_zpow, map_zpow, hθ, hc]

theorem starOf_eq_range : starOf A L = C.actA.range := by
  apply le_antisymm
  · rintro _ ⟨⟨w, hwN⟩, hwL, rfl⟩
    have hwL' : w ∈ L := Subgroup.mem_subgroupOf.mp hwL
    set g := C.ψ.symm ⟨w, hwL'⟩ with hg
    have hgw : C.phi g = w := by rw [coe_phi, hg, MulEquiv.apply_symm_apply]
    have key : ∀ g' : unitarySU 2 f K 4, C.phi g' ∈ Subgroup.normalizer (A : Set G) →
        ∀ x ∈ torusSU 3 4 K,
          (g' : GL (Fin 4) K) * x * (g' : GL (Fin 4) K)⁻¹ ∈ torusSU 3 4 K := by
      intro g' hg' x hx
      have hxU := torusSU_le_unitarySU C.hU C.hpq hx
      have h1 : C.phi g' * C.phi ⟨x, hxU⟩ * (C.phi g')⁻¹ ∈ A :=
        ((Subgroup.mem_normalizer_iff.mp hg') _).1 ((C.hψ ⟨x, hxU⟩).mpr hx)
      have h2 : C.phi g' * C.phi ⟨x, hxU⟩ * (C.phi g')⁻¹ = C.phi (g' * ⟨x, hxU⟩ * g'⁻¹) := by
        simp [map_mul, map_inv]
      rw [h2] at h1
      exact (C.hψ _).mp h1
    obtain ⟨τ, hτ⟩ := exists_normPerm C.hdist (key g (hgw ▸ hwN)) (by
      have h := key g⁻¹ (by rw [map_inv, hgw]; exact Subgroup.inv_mem _ hwN)
      simpa using h)
    refine ⟨τ, C.ext_of_theta_c (fun d => ?_) ?_⟩
    · rw [actA_theta]
      apply Subtype.ext
      show C.theta (symAct 3 K τ d) = w * C.theta d * w⁻¹
      have hT : (C.torU d : GL (Fin 4) K) ∈ torusSU 3 4 K :=
        mem_torusSU_iff.mpr ⟨d.1, d.2.1, d.2.2, rfl⟩
      have hconj : g * C.torU d * g⁻¹ = C.torU (symAct 3 K τ d) := by
        rw [← C.permU_conj_torU]
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_permU]
        exact hτ.conj_eq hT ((normPerm_permGL τ).1 _ hT)
          (fun m => (normPerm_permGL τ).ent_conj hT m)
      rw [← hgw, theta_apply, theta_apply, ← hconj, map_mul, map_mul, map_inv]
    · rw [actA_c]
      apply Subtype.ext
      show c = w * c * w⁻¹
      have := C.conj_zpow_c hwL' 1
      simp only [zpow_one] at this
      exact this.symm
  · rintro _ ⟨σ, rfl⟩
    exact C.actA_mem_starOf σ

@[expose] noncomputable def thetaA : torusVec 3 4 K →* A := C.theta.codRestrict A C.theta_mem_A

theorem coe_thetaA (d : torusVec 3 4 K) : ((C.thetaA d : A) : G) = C.theta d := rfl

theorem thetaA_injective : Function.Injective C.thetaA := by
  intro d e h
  have h' := congrArg (fun x : A => (x : G)) h
  simp only [coe_thetaA] at h'
  exact C.theta_injective h'

theorem actA_injective : Function.Injective C.actA := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  apply symAut_injective Nat.prime_three (by norm_num) C.exists_unit_root
  rw [map_one]
  apply MulEquiv.ext
  intro d
  rw [symAut_apply]
  apply C.theta_injective
  have h := C.actA_theta σ d
  rw [hσ] at h
  exact (congrArg Subtype.val h).symm

theorem commOf_actA (σ : Equiv.Perm (Fin 4)) :
    commOf (C.actA σ) = (movedSub 3 K σ).map C.thetaA := by
  rw [commOf, movedSub, MonoidHom.map_closure]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨a, rfl⟩
    obtain ⟨d, i, hdi⟩ := C.decomp a.2
    apply Subgroup.subset_closure
    refine ⟨symAct 3 K σ d * d⁻¹, ⟨d, rfl⟩, Subtype.ext ?_⟩
    rw [coe_thetaA, Subgroup.coe_mul, Subgroup.coe_inv, actA_apply_coe, hdi,
      C.conj_theta_zpow, map_mul, map_inv]
    have hc2 : c ^ i * ((C.theta d)⁻¹ * C.theta (symAct 3 K σ d)) =
        ((C.theta d)⁻¹ * C.theta (symAct 3 K σ d)) * c ^ i :=
      C.commA (A.zpow_mem C.hcA i) (A.mul_mem (A.inv_mem (C.theta_mem_A d)) (C.theta_mem_A _))
    calc C.theta (symAct 3 K σ d) * (C.theta d)⁻¹ =
        (C.theta d)⁻¹ * C.theta (symAct 3 K σ d) :=
          C.commA (C.theta_mem_A _) (A.inv_mem (C.theta_mem_A d))
      _ = (c ^ i)⁻¹ * (c ^ i * ((C.theta d)⁻¹ * C.theta (symAct 3 K σ d))) := by group
      _ = (c ^ i)⁻¹ * (((C.theta d)⁻¹ * C.theta (symAct 3 K σ d)) * c ^ i) := by rw [hc2]
      _ = (C.theta d * c ^ i)⁻¹ * (C.theta (symAct 3 K σ d) * c ^ i) := by group
  · rw [Subgroup.closure_le]
    rintro _ ⟨_, ⟨d, rfl⟩, rfl⟩
    apply Subgroup.subset_closure
    refine ⟨C.thetaA d, Subtype.ext ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_inv, actA_apply_coe, coe_thetaA, coe_thetaA, C.conj_theta,
      map_mul, map_inv]
    exact C.commA (A.inv_mem (C.theta_mem_A d)) (C.theta_mem_A _)

theorem card_commOf_actA (σ : Equiv.Perm (Fin 4)) :
    Nat.card (commOf (C.actA σ)) = Nat.card (movedSub 3 K σ) := by
  rw [C.commOf_actA, Subgroup.card_map_of_injective C.thetaA_injective]

theorem isReflectionOn_actA_iff [Finite K] (σ : Equiv.Perm (Fin 4)) :
    IsReflectionOn (C.actA σ) ↔ σ.IsSwap := by
  have hζ := C.exists_unit_root
  constructor
  · rintro ⟨hord, hcard⟩
    rw [orderOf_injective C.actA C.actA_injective σ] at hord
    have hσσ : σ * σ = 1 := by rw [← sq, ← hord, pow_orderOf_eq_one]
    have hσ1 : σ ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hord
      norm_num at hord
    rcases involution_cases σ hσσ hσ1 with ⟨a, b, hab, rfl⟩ | ⟨a, b, c', d, hab, hac, -, hbc, -,
      hcd, h1, h2, h3, h4⟩
    · exact ⟨a, b, hab, rfl⟩
    · exfalso
      rw [C.card_commOf_actA] at hcard
      exact card_movedSub_ne_prime_of_double_swap Nat.prime_three (by norm_num) hζ σ hab hac hbc
        hcd h1 h2 h3 h4 hcard
  · rintro ⟨a, b, hab, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [orderOf_injective C.actA C.actA_injective]
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine orderOf_eq_prime (by rw [pow_two, Equiv.swap_mul_self]) ?_
      intro h
      have := congrArg (fun σ : Equiv.Perm (Fin 4) => σ a) h
      simp [Equiv.swap_apply_left] at this
      exact hab this.symm
    · rw [C.card_commOf_actA]
      exact card_movedSub_swap Nat.prime_three (by norm_num) hζ hab

include C in
theorem starOf_eq_closure [Finite K] :
    starOf A L = Subgroup.closure ((starOf A L : Set (MulAut A)) ∩ {φ | IsReflectionOn φ}) := by
  apply le_antisymm
  · have h : starOf A L = Subgroup.closure (C.actA '' {σ | σ.IsSwap}) := by
      rw [C.starOf_eq_range, MonoidHom.range_eq_map, ← Equiv.Perm.closure_isSwap,
        MonoidHom.map_closure]
    calc starOf A L = Subgroup.closure (C.actA '' {σ | σ.IsSwap}) := h
      _ ≤ _ := by
        refine Subgroup.closure_mono ?_
        rintro _ ⟨σ, hσ, rfl⟩
        exact ⟨C.actA_mem_starOf σ, (C.isReflectionOn_actA_iff σ).mpr hσ⟩
  · rw [Subgroup.closure_le]
    exact Set.inter_subset_left

end U4OddCtx

end CFSG.RankThree.PartTwo.Sec21.U4OddLines
