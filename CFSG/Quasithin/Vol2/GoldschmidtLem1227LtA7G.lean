module

public import CFSG.Quasithin.Vol2.GoldschmidtLem1227LtA7
public import CFSG.Quasithin.Vol2.GoldschmidtLem1227LtBasic
public import CFSG.Quasithin.Vol2.GoldschmidtLem1227LtFinish
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13.Lem1227Eq
open CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Vol2Native.A312L.Seven
open Equiv

namespace Lem1227Lt

namespace A7

@[expose] def Qpres (σ : P7) : Prop := (σ 4 = 4 ∨ σ 4 = 5) ∧ (σ 5 = 4 ∨ σ 5 = 5)

theorem Qpres_mul {x y : P7} (hx : Qpres x) (hy : Qpres y) : Qpres (x * y) := by
  obtain ⟨a4, a5⟩ := hx
  obtain ⟨b4, b5⟩ := hy
  refine ⟨?_, ?_⟩
  · rcases b4 with h | h <;> simp [Perm.mul_apply, h] <;> tauto
  · rcases b5 with h | h <;> simp [Perm.mul_apply, h] <;> tauto

theorem Qpres_inv {x : P7} (hx : Qpres x) : Qpres x⁻¹ := by
  obtain ⟨h4, h5⟩ := hx
  rcases fix_or_swap h4 h5 with ⟨a, b⟩ | ⟨a, b⟩
  · obtain ⟨c, d⟩ := inv_fix a b
    exact ⟨Or.inl c, Or.inr d⟩
  · obtain ⟨c, d⟩ := inv_swap a b
    exact ⟨Or.inr c, Or.inl d⟩

theorem Qpres_conj {σ y : P7} (hσ : Qpres σ) (hσ' : Qpres σ⁻¹) :
    Qpres (σ * y * σ⁻¹) ↔ Qpres y := by
  constructor
  · intro h
    have := Qpres_mul (Qpres_mul hσ' h) (show Qpres σ⁻¹⁻¹ by rwa [inv_inv])
    simpa [mul_assoc] using this
  · intro h
    exact Qpres_mul (Qpres_mul hσ h) hσ'

section Family

variable {G : Type} [Group G] [Finite G] {T K Y H M₀ : Subgroup G}

theorem exists_phi_T7
    (h : LtHyp G T K Y) (ν : (↥Y ⧸ CFSG.pCore 2 ↥Y) →* ↥A7s) (hν : Function.Surjective ν) :
    ∃ φ : ↥Y →* ↥A7s, Function.Surjective φ ∧
      (∀ y : ↥Y, φ y = 1 ↔
        (QuotientGroup.mk y : ↥Y ⧸ CFSG.pCore 2 ↥Y) ∈ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)) ∧
      imgS T Y φ = T7 := by
  have hsimple : IsSimpleGroup ↥A7s := alternatingGroup.isSimpleGroup (by simp)
  have hX : ∃ a b : ↥A7s, a * b ≠ b * a :=
    nonabelian_of_card_not_prime (by rw [card_A7s]; norm_num)
  have hS : IsSylowTwoOf (imgS T Y (phiOf Y ν)) ⊤ := isSylow_imgS h _ (phi_surj hν)
  obtain ⟨ρ, hρ⟩ := exists_mulEquiv_map_eq_of_sylow (MulEquiv.refl ↥A7s) hS isSylowTwoOf_T7
  have hν' : Function.Surjective (ρ.toMonoidHom.comp ν) := ρ.surjective.comp hν
  refine ⟨phiOf Y (ρ.toMonoidHom.comp ν), phi_surj hν', phi_hkc h hX hν', ?_⟩
  rw [← hρ]
  simp only [imgS, Subgroup.map_map]
  rfl

theorem sign_conj (σ x : P7) : Perm.sign (σ * x * σ⁻¹) = Perm.sign x := by
  simp only [Perm.sign_mul, Perm.sign_inv]
  rw [mul_comm (Perm.sign σ) (Perm.sign x), mul_assoc, Int.units_mul_self, mul_one]

theorem normD7_of_map {σ : P7}
    (hT : T7.map (MulAut.conjNormal σ : MulAut ↥A7s).toMonoidHom = T7) :
    ∀ x, x ∈ D7 ↔ σ * x * σ⁻¹ ∈ D7 := by
  intro x
  have hD := D7_le_A7s
  have key : ∀ y : ↥A7s, y ∈ T7 ↔ (MulAut.conjNormal σ : MulAut ↥A7s) y ∈ T7 := by
    intro y
    constructor
    · intro hy
      rw [← hT]
      exact ⟨y, hy, rfl⟩
    · intro hy
      rw [← hT] at hy
      obtain ⟨y', hy', hyy⟩ := hy
      have : y' = y := (MulAut.conjNormal σ : MulAut ↥A7s).injective hyy
      rwa [← this]
  constructor
  · intro hx
    have hy : (⟨x, hD hx⟩ : ↥A7s) ∈ T7 := Subgroup.mem_subgroupOf.2 hx
    have h1 := Subgroup.mem_subgroupOf.1 ((key _).1 hy)
    simpa [MulAut.conjNormal_apply] using h1
  · intro hx
    have hxe : Perm.sign x = 1 := by
      have := Equiv.Perm.mem_alternatingGroup.mp (hD hx)
      rwa [sign_conj] at this
    have hy : (MulAut.conjNormal σ : MulAut ↥A7s) ⟨x, Equiv.Perm.mem_alternatingGroup.mpr hxe⟩ ∈
        T7 := by
      refine Subgroup.mem_subgroupOf.2 ?_
      simpa [MulAut.conjNormal_apply] using hx
    have := (key _).2 hy
    exact Subgroup.mem_subgroupOf.1 this

theorem exists_sigma (h : LtHyp G T K Y) (φ : ↥Y →* ↥A7s)
    (hφs : Function.Surjective φ)
    (hk : ∀ y : ↥Y, φ y = 1 ↔
      (QuotientGroup.mk y : ↥Y ⧸ CFSG.pCore 2 ↥Y) ∈ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y))
    (hS : imgS T Y φ = T7) (t : ↥T) :
    ∃ σ : P7, (∀ y : ↥Y, MulAut.conjNormal σ (φ y) = φ (conjY h t y)) ∧
      (∀ x, x ∈ D7 ↔ σ * x * σ⁻¹ ∈ D7) ∧
      (∀ b ∈ imgK K Y φ, σ * (b : P7) * σ⁻¹ ∈ (imgK K Y φ).map A7s.subtype) := by
  obtain ⟨α, hα, hαB, hαS⟩ := exists_act_T h φ hφs (hinv_of_hk h φ hk) t
  obtain ⟨σ, hσ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by norm_num) (by norm_num)).2 α
  subst hσ
  refine ⟨σ, hα, normD7_of_map (by rw [← hS]; exact hαS), fun b hb => ?_⟩
  have : MulAut.conjNormal σ b ∈ (imgK K Y φ).map (MulAut.conjNormal σ : MulAut ↥A7s).toMonoidHom :=
    ⟨b, hb, rfl⟩
  rw [hαB] at this
  exact ⟨_, this, by simp [MulAut.conjNormal_apply]⟩

theorem a7_l3
    (h : LtHyp G T K Y) (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hmin : MinParabolic H T M₀) (hker : KerChar M₀ H K)
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hlist : E22TwoAlt ↥(E2.star M₀ H K)
      (E2.IsDiagramNontrivial (E2.star M₀ H T) (E2.star M₀ H K) (E2.star M₀ H (T ⊓ K)))
      (8 < E2.autCard (E2.star M₀ H T) (E2.star M₀ H K))
      (E2.InducesOuter (E2.star M₀ H T) (E2.star M₀ H K)))
    (φ : ↥Y →* ↥A7s) (hφs : Function.Surjective φ)
    (hk : ∀ y : ↥Y, φ y = 1 ↔
      (QuotientGroup.mk y : ↥Y ⧸ CFSG.pCore 2 ↥Y) ∈ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y))
    (hS : imgS T Y φ = T7) {i : ℕ} (hi : i = 8 ∨ i = 9)
    (hBi : (imgK K Y φ).map A7s.subtype = Z i)
    (e : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃* ↥(Z i)) : False := by
  have hsl : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := slThree_isSimple
  set ψ := psi h φ with hψ
  set B := imgK K Y φ with hB
  have hrange : ψ.range = B := (imgK_eq_range h φ).symm
  have hmem : ∀ k : ↥K, ψ k ∈ B := fun k => by
    rw [← hrange]
    exact ⟨k, rfl⟩
  let eB : ↥B ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    ((B.equivMapOfInjective A7s.subtype A7s.subtype_injective).trans
      (MulEquiv.subgroupCongr hBi)).trans e.symm
  let ψ₃ : ↥K →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    eB.toMonoidHom.comp (ψ.codRestrict B hmem)
  have hψ₃ : Function.Surjective ψ₃ := by
    intro y
    obtain ⟨k, hk'⟩ : (eB.symm y : ↥A7s) ∈ ψ.range := by
      rw [hrange]
      exact (eB.symm y).2
    refine ⟨k, ?_⟩
    have : ψ.codRestrict B hmem k = eB.symm y := Subtype.ext hk'
    show eB (ψ.codRestrict B hmem k) = y
    rw [this, MulEquiv.apply_symm_apply]
  refine false_of_card_168 hKH hHK hmin hker hq h.hTK hlist slThree_nonabelian
    card_sl_three_zmod_two ψ₃ hψ₃ ?_
  intro t
  obtain ⟨σ, hσα, hσD, hσB⟩ := exists_sigma h φ hφs hk hS t
  have hσZ : σ ∈ Z i := sigma_mem_Z hi hBi hσD hσB
  rw [← hBi] at hσZ
  obtain ⟨b, hb, hbσ⟩ := hσZ
  obtain ⟨k, hkb⟩ : b ∈ ψ.range := by
    rw [hrange]
    exact hb
  refine ⟨k, fun x => ?_⟩
  have h1 : ψ (K.normalizerMonoidHom ⟨(t : G), h.hTK t.2⟩ x) = ψ (k * x * k⁻¹) := by
    rw [psi_conj h φ t (α := MulAut.conjNormal σ) hσα x, map_mul, map_mul, map_inv, hkb]
    apply Subtype.ext
    simp [MulAut.conjNormal_apply, ← hbσ]
    rfl
  show eB.toMonoidHom (ψ.codRestrict B hmem _) = eB.toMonoidHom (ψ.codRestrict B hmem _)
  congr 1
  exact Subtype.ext h1

@[expose] def Pstab : Subgroup ↥rng6 where
  carrier := {y | Qpres ((y : ↥A7s) : P7)}
  one_mem' := ⟨Or.inl rfl, Or.inr rfl⟩
  mul_mem' := fun hx hy => Qpres_mul hx hy
  inv_mem' := fun hx => Qpres_inv hx

theorem mem_Pstab {y : ↥rng6} : y ∈ Pstab ↔ Qpres ((y : ↥A7s) : P7) := Iff.rfl

theorem Pstab_ne_top :
    Pstab ≠ ⊤ := by
  intro htop
  let c : ↥A7s := ⟨perm7 [[3, 4, 5]], Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩
  have hc : c ∈ rng6 := (mem_rng6 c).2 (by decide +kernel)
  have : (⟨c, hc⟩ : ↥rng6) ∈ Pstab := htop ▸ Subgroup.mem_top _
  have h2 : Qpres (perm7 [[3, 4, 5]]) := this
  revert h2
  unfold Qpres
  decide +kernel

theorem Pstab_index :
    Pstab.index ≤ 15 := by
  have hD : D7 ≤ A7s := D7_le_A7s
  have hT7 : T7 ≤ rng6 := by
    intro x hx
    have hx' := Subgroup.mem_subgroupOf.1 hx
    exact (mem_rng6 x).2 (Qfix_of_mem_D7 hx').1
  have hle : T7.subgroupOf rng6 ≤ Pstab := by
    intro y hy
    have hy' := Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 hy)
    exact (Qfix_of_mem_D7 hy').2
  have hcardT : Nat.card (T7.subgroupOf rng6) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT7).toEquiv]
    rw [T7, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD).toEquiv]
    exact card_D7
  have h8 : 8 ∣ Nat.card Pstab := hcardT ▸ Subgroup.card_dvd_of_le hle
  have h3 : 3 ∣ Nat.card Pstab := by
    let c : ↥A7s := ⟨perm7 [[0, 1, 2]], Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩
    have hc : c ∈ rng6 := (mem_rng6 c).2 (by decide +kernel)
    have hcP : (⟨c, hc⟩ : ↥rng6) ∈ Pstab := by
      show Qpres (perm7 [[0, 1, 2]])
      unfold Qpres
      decide +kernel
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf (⟨⟨c, hc⟩, hcP⟩ : ↥Pstab) = 3 := by
      refine orderOf_eq_prime ?_ ?_
      · apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        show (perm7 [[0, 1, 2]]) ^ 3 = 1
        decide +kernel
      · intro h1
        have := congrArg (fun z : ↥Pstab => ((z : ↥rng6) : ↥A7s).1) h1
        revert this
        show perm7 [[0, 1, 2]] ≠ 1
        decide +kernel
    exact hord ▸ orderOf_dvd_natCard _
  have h24 : 24 ∣ Nat.card Pstab :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 8 3) h8 h3
  have hcard6 : Nat.card ↥rng6 = 360 := by
    rw [Nat.card_congr rng6Equiv.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    decide
  have hmul := Subgroup.card_mul_index Pstab
  rw [hcard6] at hmul
  have hpos : 0 < Nat.card Pstab := Nat.card_pos
  have h24' : 24 ≤ Nat.card Pstab := Nat.le_of_dvd hpos h24
  by_contra hcon
  push Not at hcon
  have : 24 * 16 ≤ Nat.card Pstab * Pstab.index := Nat.mul_le_mul h24' hcon
  omega

theorem a7_a6
    (h : LtHyp G T K Y) (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hmin : MinParabolic H T M₀)
    (hker : KerChar M₀ H K) (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hlist : E22TwoAlt ↥(E2.star M₀ H K)
      (E2.IsDiagramNontrivial (E2.star M₀ H T) (E2.star M₀ H K) (E2.star M₀ H (T ⊓ K)))
      (8 < E2.autCard (E2.star M₀ H T) (E2.star M₀ H K))
      (E2.InducesOuter (E2.star M₀ H T) (E2.star M₀ H K)))
    (φ : ↥Y →* ↥A7s) (hφs : Function.Surjective φ)
    (hk : ∀ y : ↥Y, φ y = 1 ↔
      (QuotientGroup.mk y : ↥Y ⧸ CFSG.pCore 2 ↥Y) ∈ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y))
    (hS : imgS T Y φ = T7) (hB6 : imgK K Y φ = rng6) : False := by
  set ψ := psi h φ with hψ
  have hrange : ψ.range = rng6 := (imgK_eq_range h φ).symm.trans hB6
  have hmem : ∀ k : ↥K, ψ k ∈ rng6 := fun k => by
    rw [← hrange]
    exact ⟨k, rfl⟩
  let ψ₆ : ↥K →* ↥(alternatingGroup (Fin 6)) :=
    rng6Equiv.toMonoidHom.comp (ψ.codRestrict rng6 hmem)
  have hψ₆ : Function.Surjective ψ₆ := by
    intro y
    obtain ⟨k, hk'⟩ : (rng6Equiv.symm y : ↥A7s) ∈ ψ.range := by
      rw [hrange]
      exact (rng6Equiv.symm y).2
    refine ⟨k, ?_⟩
    have : ψ.codRestrict rng6 hmem k = rng6Equiv.symm y := Subtype.ext hk'
    show rng6Equiv (ψ.codRestrict rng6 hmem k) = y
    rw [this, MulEquiv.apply_symm_apply]
  have hP : Pstab.map rng6Equiv.toMonoidHom ≠ ⊤ := by
    intro htop
    apply Pstab_ne_top
    have := congrArg (Subgroup.comap rng6Equiv.toMonoidHom) htop
    rwa [Subgroup.comap_map_eq_self_of_injective rng6Equiv.injective, Subgroup.comap_top] at this
  have hidx : (Pstab.map rng6Equiv.toMonoidHom).index ≤ 44 := by
    rw [Subgroup.index_map_of_bijective (f := rng6Equiv.toMonoidHom) rng6Equiv.bijective]
    exact Pstab_index.trans (by norm_num)
  refine false_of_card_360 hKH hHK hmin hker hq h.hTK hlist ψ₆ hψ₆ _ hP hidx ?_
  intro t x
  obtain ⟨σ, hσα, hσD, hσB⟩ := exists_sigma h φ hφs hk hS t
  obtain ⟨-, hQ, hQ'⟩ := norm_D7 hσD
  have hconj : ψ (K.normalizerMonoidHom ⟨(t : G), h.hTK t.2⟩ x) =
      MulAut.conjNormal σ (ψ x) := psi_conj h φ t (α := MulAut.conjNormal σ) hσα x
  have key : ∀ z : ↥K, ψ₆ z ∈ Pstab.map rng6Equiv.toMonoidHom ↔ Qpres ((ψ z : ↥A7s) : P7) := by
    intro z
    rw [show ψ₆ z = rng6Equiv ⟨ψ z, hmem z⟩ from rfl, Subgroup.mem_map_equiv,
      MulEquiv.symm_apply_apply]
    exact mem_Pstab
  rw [key, key, hconj]
  simp only [MulAut.conjNormal_apply]
  exact Qpres_conj ⟨hQ.2.1, hQ.2.2⟩ ⟨hQ'.2.1, hQ'.2.2⟩

theorem fam_a7
    (h : LtHyp G T K Y) (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hmin : MinParabolic H T M₀) (hker : KerChar M₀ H K)
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hlist : E22TwoAlt ↥(E2.star M₀ H K)
      (E2.IsDiagramNontrivial (E2.star M₀ H T) (E2.star M₀ H K) (E2.star M₀ H (T ⊓ K)))
      (8 < E2.autCard (E2.star M₀ H T) (E2.star M₀ H K))
      (E2.InducesOuter (E2.star M₀ H T) (E2.star M₀ H K)))
    (ν : (↥Y ⧸ CFSG.pCore 2 ↥Y) →* ↥A7s) (hν : Function.Surjective ν) :
    LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 2 2 2 ∧
      Nonempty ((↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) ≃*
        alternatingGroup (Fin 7)) := by
  have hsimple : IsSimpleGroup ↥A7s := alternatingGroup.isSimpleGroup (by simp)
  have hX : ∃ a b : ↥A7s, a * b ≠ b * a :=
    nonabelian_of_card_not_prime (by rw [card_A7s]; norm_num)
  obtain ⟨-, eQ, -⟩ := SteinbergBM.five_quasisimple_centerless_image h.hYq hX ν hν
  refine ⟨?_, ⟨eQ⟩⟩
  obtain ⟨φ, hφs, hk, hS⟩ := exists_phi_T7 h ν hν
  have hperf := imgK_perfect h φ
  have hbot := imgK_ne_bot h φ (fun y hy => (hk y).1 hy)
  have htop := imgK_ne_top h φ (fun y hy => (hk y).1 hy)
  have hN : T7 ≤ Subgroup.normalizer (imgK K Y φ : Set ↥A7s) := hS ▸ imgS_le_normalizer h φ
  rcases classify_B hperf hbot htop hN with hB5 | ⟨i, hi, hBi⟩ | hB6
  ·
    have hrange : (psi h φ).range = rng5 := (imgK_eq_range h φ).symm.trans hB5
    have hmem : ∀ k : ↥K, psi h φ k ∈ rng5 := fun k => by
      rw [← hrange]
      exact ⟨k, rfl⟩
    let ψ₅ : ↥K →* ↥(alternatingGroup (Fin 5)) :=
      rng5Equiv.toMonoidHom.comp ((psi h φ).codRestrict rng5 hmem)
    have hψ₅ : Function.Surjective ψ₅ := by
      intro y
      obtain ⟨k, hk'⟩ : (rng5Equiv.symm y : ↥A7s) ∈ (psi h φ).range := by
        rw [hrange]
        exact (rng5Equiv.symm y).2
      refine ⟨k, ?_⟩
      have : (psi h φ).codRestrict rng5 hmem k = rng5Equiv.symm y := Subtype.ext hk'
      show rng5Equiv ((psi h φ).codRestrict rng5 hmem k) = y
      rw [this, MulEquiv.apply_symm_apply]
    exact lieModel_of_surjective_alt5 hq ψ₅ hψ₅
  ·
    rcases hi with rfl | rfl
    · exact (a7_l3 h hKH hHK hmin hker hq hlist φ hφs hk hS (Or.inl rfl) hBi z8Equiv).elim
    · exact (a7_l3 h hKH hHK hmin hker hq hlist φ hφs hk hS (Or.inr rfl) hBi z9Equiv).elim
  ·
    exact (a7_a6 h hKH hHK hmin hker hq hlist φ hφs hk hS hB6).elim

end Family

end A7

end Lem1227Lt

end CFSG.Quasithin.H13
