module

public import CFSG.RankThree.PartOne.F106.NoQD32NADeg
public import CFSG.RankThree.PartOne.F106.NoQD32NADispLift
public import CFSG.RankThree.PartOne.F106.NoQD32NAL3U3Reg
public import CFSG.RankThree.PartOne.F106.NoQD32L3U3Count
public import CFSG.RankThree.PartOne.N143X.EvenSmall

public section

namespace CFSG.RankThree.PartOne.F106

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.N143X
  CFSG.RankThree.PartOne.F106.NAD
open scoped commutatorElement

section Gen

theorem na_deg_gen {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {q N : ℕ}
    (hq : q.Prime) (hNK : (N : K) ≠ 0) {P : Type} [Group P] (ρ : P →* GL ι K)
    (hρ : Function.Injective ρ) (hN : ∀ z ∈ center P, z ^ N = 1)
    (hcq : ∀ a b : P, ⁅a, b⁆ ^ q = 1) (hcl : ∀ a b c : P, ⁅⁅a, b⁆, c⁆ = 1)
    (h4 : q ^ 4 ≤ Nat.card (P ⧸ center P)) : 2 * q ≤ Fintype.card ι := by
  let ε : P ≃* ρ.range := MonoidHom.ofInjective hρ
  have hcl' : ∀ a ∈ ρ.range, ∀ b ∈ ρ.range, ∀ c ∈ ρ.range, ⁅⁅a, b⁆, c⁆ = 1 := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ _ ⟨c, rfl⟩
    rw [← map_commutatorElement, ← map_commutatorElement, hcl, map_one]
  have hcq' : ∀ a ∈ ρ.range, ∀ b ∈ ρ.range, ⁅a, b⁆ ^ q = 1 := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_commutatorElement, ← map_pow, hcq, map_one]
  have hN' : ∀ e ∈ Fz ρ.range, e ^ N = 1 := by
    intro e he
    obtain ⟨⟨p, rfl⟩, hcomm⟩ := mem_Fz.1 he
    have hp : p ∈ center P := by
      refine mem_center_iff.2 fun g => hρ ?_
      rw [map_mul, map_mul]
      exact hcomm (ρ g) ⟨g, rfl⟩
    rw [← map_pow, hN p hp, map_one]
  exact na_deg_of_classTwo ⟨hq, hN', hcq', hcl'⟩ hNK
    (by rw [← card_quotient_center_congr ε]; exact h4)

end Gen

section Class

variable {G : Type*} [Group G]

theorem commutator_mul_left_of_class_two (hcl : ∀ a b c : G, ⁅⁅a, b⁆, c⁆ = 1) (x y a : G) :
    ⁅x * y, a⁆ = ⁅x, a⁆ * ⁅y, a⁆ := by
  have e1 : ⁅x * y, a⁆ = x * ⁅y, a⁆ * x⁻¹ * ⁅x, a⁆ := by
    simp only [commutatorElement_def]
    group
  have e2 : x * ⁅y, a⁆ * x⁻¹ = ⁅y, a⁆ := by
    rw [← commutatorElement_eq_one_iff_mul_comm.1 (hcl y a x)]
    group
  have e3 : ⁅x, a⁆ * ⁅y, a⁆ = ⁅y, a⁆ * ⁅x, a⁆ :=
    commutatorElement_eq_one_iff_mul_comm.1 (hcl x a ⁅y, a⁆)
  rw [e1, e2, e3]

theorem commutator_pow_three_of_class_two (hcl : ∀ a b c : G, ⁅⁅a, b⁆, c⁆ = 1) (a b : G) :
    ⁅a, b⁆ ^ 3 = ⁅a ^ 3, b⁆ := by
  have h2 : ⁅a ^ 2, b⁆ = ⁅a, b⁆ ^ 2 := by
    rw [pow_two, commutator_mul_left_of_class_two hcl, pow_two]
  rw [pow_succ a 2, commutator_mul_left_of_class_two hcl, h2, ← pow_succ]

end Class

section Cover

variable {K : Type} [Field K] {P : Type} [Group P] (ρ : P →* GL (Fin 3) K)

theorem scalar_cube_eq_one (hdet : ∀ g, ((ρ g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1)
    {c : Kˣ} {z : P} (hz : ρ z = Matrix.GeneralLinearGroup.scalar (Fin 3) c) : c ^ 3 = 1 := by
  have := hdet z
  rw [hz] at this
  exact pow_eq_one_of_scalar_det this

variable {T : Type} [Group T] (f : P →* T)

theorem card_ker_le_three [Finite P] (hρ : Function.Injective ρ)
    (hdet : ∀ g, ((ρ g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hZ : ∀ z : P, f z = 1 → ∃ c : Kˣ, ρ z = Matrix.GeneralLinearGroup.scalar (Fin 3) c) :
    Nat.card f.ker ≤ 3 := by
  choose! c hc using hZ
  have hmem : ∀ z : f.ker, c z ∈ rootsOfUnity 3 K := fun z => by
    rw [mem_rootsOfUnity]
    exact scalar_cube_eq_one ρ hdet (hc z z.2)
  have hinj : Function.Injective (fun z : f.ker => (⟨c z, hmem z⟩ : rootsOfUnity 3 K)) := by
    intro z z' h
    have h1 : c z = c z' := congrArg Subtype.val h
    apply Subtype.ext
    apply hρ
    rw [hc z z.2, hc z' z'.2, h1]
  exact (Nat.card_le_card_of_injective _ hinj).trans (card_rootsOfUnity K 3)

theorem index_centralizer_le [Finite P] {x : P} (hx : ∀ h : P, f ⁅x, h⁆ = 1) :
    (Subgroup.centralizer ({x} : Set P)).index ≤ Nat.card f.ker := by
  set C := Subgroup.centralizer ({x} : Set P) with hC
  have hmem : ∀ h : P, ⁅h, x⁆ ∈ f.ker := fun h => by
    rw [MonoidHom.mem_ker, ← commutatorElement_inv, map_inv, hx h, inv_one]
  have hmul : ∀ h c : P, c ∈ C → ⁅h * c, x⁆ = ⁅h, x⁆ := by
    intro h c hc
    have hc1 : ⁅c, x⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2
      (mem_centralizer_iff.1 hc x rfl).symm
    have e : ⁅h * c, x⁆ = h * ⁅c, x⁆ * h⁻¹ * ⁅h, x⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e, hc1]
    group
  let Φ : P ⧸ C → f.ker := Quotient.lift (fun h : P => (⟨⁅h, x⁆, hmem h⟩ : f.ker))
    (fun h h' hh => by
      have hh' : h⁻¹ * h' ∈ C := QuotientGroup.leftRel_apply.1 hh
      apply Subtype.ext
      change ⁅h, x⁆ = ⁅h', x⁆
      have : h' = h * (h⁻¹ * h') := by group
      rw [this, hmul h _ hh'])
  have hΦ : Function.Injective Φ := by
    intro u v huv
    induction u using Quotient.inductionOn with | _ h => ?_
    induction v using Quotient.inductionOn with | _ h' => ?_
    have h1 : ⁅h, x⁆ = ⁅h', x⁆ := congrArg Subtype.val huv
    apply Quotient.sound
    refine QuotientGroup.leftRel_apply.2 ?_
    rw [hC, mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    simp only [commutatorElement_def] at h1
    have h2 : h * y * h⁻¹ = h' * y * h'⁻¹ := mul_right_cancel h1
    calc y * (h⁻¹ * h') = h⁻¹ * (h * y * h⁻¹) * h' := by group
      _ = h⁻¹ * (h' * y * h'⁻¹) * h' := by rw [h2]
      _ = h⁻¹ * h' * y := by group
  rw [Subgroup.index_eq_card]
  exact Nat.card_le_card_of_injective Φ hΦ

theorem centralizer_abelian [Finite P] (hρ : Function.Injective ρ)
    (hdet : ∀ g, ((ρ g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hZ : ∀ z : P, f z = 1 → ∃ c : Kˣ, ρ z = Matrix.GeneralLinearGroup.scalar (Fin 3) c) {x g : P}
    (hker : ⁅g, x⁆ ∈ f.ker) (hne : ⁅g, x⁆ ≠ 1) {a b : P}
    (ha : a ∈ Subgroup.centralizer ({x} : Set P)) (hb : b ∈ Subgroup.centralizer ({x} : Set P)) :
    a * b = b * a := by
  obtain ⟨c, hc⟩ := hZ _ hker
  have hc3 : c ^ 3 = 1 := scalar_cube_eq_one ρ hdet hc
  have hc1 : c ≠ 1 := by
    rintro rfl
    apply hne
    apply hρ
    rw [hc, map_one, map_one]
  have hgx : g * x = ⁅g, x⁆ * (x * g) := by
    simp only [commutatorElement_def]
    group
  have hxg : ((ρ g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((ρ x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (c : K) • (((ρ x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((ρ g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
    have h1 : ρ g * ρ x = Matrix.GeneralLinearGroup.scalar (Fin 3) c * (ρ x * ρ g) := by
      calc ρ g * ρ x = ρ (g * x) := (map_mul ρ g x).symm
        _ = ρ (⁅g, x⁆ * (x * g)) := by rw [hgx]
        _ = ρ ⁅g, x⁆ * (ρ x * ρ g) := by rw [map_mul, map_mul]
        _ = Matrix.GeneralLinearGroup.scalar (Fin 3) c * (ρ x * ρ g) := by rw [hc]
    have h2 := congrArg (fun u : GL (Fin 3) K => (u : Matrix (Fin 3) (Fin 3) K)) h1
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_eq_diagonal_mul] using h2
  refine commute_of_regular ρ hρ (ω := (c : K)) ?_ ?_ hxg ?_ ?_
  · rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
  · intro h
    exact hc1 (Units.ext h)
  · exact (mem_centralizer_iff.1 ha x rfl).symm
  · exact (mem_centralizer_iff.1 hb x rfl).symm

end Cover

section Final

variable {K : Type} [Field K] {P : Type} [Group P] [Finite P] {T : Type} [Group T]

theorem false_of_cover (hK : (3 : K) ≠ 0) (ρ : P →* GL (Fin 3) K) (hρ : Function.Injective ρ)
    (hdet : ∀ g, ((ρ g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1) (f : P →* T)
    (hZ : ∀ z : P, f z = 1 → ∃ c : Kˣ, ρ z = Matrix.GeneralLinearGroup.scalar (Fin 3) c)
    (hexp : ∀ x : P, f x ^ 3 = 1) (hcl : ∀ a b c : P, f ⁅⁅a, b⁆, c⁆ = 1)
    (hD : ∀ C : Subgroup P, (∀ a ∈ C, ∀ b ∈ C, a * b = b * a) → Nat.card (C.map f) ≤ 27)
    (h4 : 3 ^ 4 ≤ Nat.card (↥f.range ⧸ center ↥f.range)) : False := by
  have : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hrange3 : ∀ y : ↥f.range, y ^ 3 = 1 := by
    rintro ⟨_, p, rfl⟩
    exact Subtype.ext (hexp p)
  by_cases hB : ∃ x : P, (∀ h : P, f ⁅x, h⁆ = 1) ∧ ∃ g : P, ⁅x, g⁆ ≠ 1
  · obtain ⟨x, hxcl, g, hg⟩ := hB
    have hker : ∀ h : P, ⁅h, x⁆ ∈ f.ker := fun h => by
      rw [MonoidHom.mem_ker, ← commutatorElement_inv, map_inv, hxcl h, inv_one]
    have hne : ⁅g, x⁆ ≠ 1 := fun h => hg (by rw [← commutatorElement_inv, h, inv_one])
    set C := Subgroup.centralizer ({x} : Set P) with hC
    have hCab : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := fun a ha b hb =>
      centralizer_abelian ρ f hρ hdet hZ (hker g) hne ha hb
    have hidx : C.index ≤ 3 :=
      (index_centralizer_le f hxcl).trans (card_ker_le_three ρ f hρ hdet hZ)
    have hD27 := hD C hCab
    have hP : Nat.card f.ker * Nat.card f.range = Nat.card P := Subgroup.card_ker_mul_card_range f
    have hPC : Nat.card P = C.index * Nat.card C := by
      rw [Subgroup.index_eq_card]
      exact Subgroup.card_eq_card_quotient_mul_card_subgroup C
    have hCle : Nat.card C ≤ Nat.card f.ker * Nat.card (C.map f) := by
      have h1 := Subgroup.card_ker_mul_card_range (f.comp C.subtype)
      have h2 : (f.comp C.subtype).range = C.map f := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      have h3 : Nat.card (f.comp C.subtype).ker ≤ Nat.card f.ker :=
        Nat.card_le_card_of_injective (fun c => ⟨(c : C).1, c.2⟩) (by
          intro c c' h
          have h1 := congrArg (fun z : f.ker => (z : P)) h
          exact Subtype.ext (Subtype.ext h1))
      rw [h2] at h1
      calc Nat.card C = Nat.card (f.comp C.subtype).ker * Nat.card (C.map f) := h1.symm
        _ ≤ Nat.card f.ker * Nat.card (C.map f) := Nat.mul_le_mul_right _ h3
    have hkpos : 0 < Nat.card f.ker := Nat.card_pos
    have h81 : Nat.card f.range ≤ 81 := by
      have : Nat.card f.ker * Nat.card f.range ≤ Nat.card f.ker * 81 := by
        calc Nat.card f.ker * Nat.card f.range = Nat.card P := hP
          _ = C.index * Nat.card C := hPC
          _ ≤ 3 * (Nat.card f.ker * Nat.card (C.map f)) := Nat.mul_le_mul hidx hCle
          _ ≤ 3 * (Nat.card f.ker * 27) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hD27)
          _ = Nat.card f.ker * 81 := by ring
      exact Nat.le_of_mul_le_mul_left this hkpos
    have h5 := pow_five_dvd_card Nat.prime_three hrange3 h4
    have h6 : 3 ^ 5 ≤ Nat.card f.range := Nat.le_of_dvd Nat.card_pos h5
    have h7 : (3 : ℕ) ^ 5 = 243 := by norm_num
    rw [h7] at h6
    omega
  · push Not at hB
    have hcl2 : ∀ a b c : P, ⁅⁅a, b⁆, c⁆ = 1 := fun a b c => hB ⁅a, b⁆ (fun h => hcl a b h) c
    have hcen : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ center (GL (Fin 3) K) := by
      intro c
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨c, rfl⟩
    have hcq : ∀ a b : P, ⁅a, b⁆ ^ 3 = 1 := by
      intro a b
      rw [commutator_pow_three_of_class_two hcl2]
      obtain ⟨c, hc⟩ := hZ (a ^ 3) (by rw [map_pow]; exact hexp a)
      apply hρ
      rw [map_commutatorElement, hc, map_one]
      exact commutatorElement_eq_one_iff_mul_comm.2 (mem_center_iff.1 (hcen c) (ρ b)).symm
    have hN : ∀ z ∈ center P, z ^ 9 = 1 := by
      intro z _
      obtain ⟨c, hc⟩ := hZ (z ^ 3) (by rw [map_pow]; exact hexp z)
      have hc3 := scalar_cube_eq_one ρ hdet hc
      apply hρ
      rw [map_one, show z ^ 9 = (z ^ 3) ^ 3 by rw [← pow_mul], map_pow, hc, ← map_pow, hc3,
        map_one]
    have hNK : ((9 : ℕ) : K) ≠ 0 := by
      have : ((9 : ℕ) : K) = (3 : K) * 3 := by push_cast; norm_num
      rw [this]
      exact mul_ne_zero hK hK
    have h4' : 3 ^ 4 ≤ Nat.card (P ⧸ center P) :=
      h4.trans (card_quotient_center_le_of_surjective f.rangeRestrict f.rangeRestrict_surjective)
    have := na_deg_gen Nat.prime_three hNK ρ hρ hN hcq hcl2 h4'
    simp only [Fintype.card_fin] at this
    omega

end Final

section Model

theorem false_of_statedProj_three_nonab {K : Type} [Field K] [Finite K] (hqK : (3 : K) ≠ 0)
    (M : Subgroup (GL (Fin 3) K))
    (hdet : ∀ g ∈ M, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1)
    {T : Type} [Group T] (e : T ≃* StatedProj M) {Y : Subgroup T} (hexp : ∀ y ∈ Y, y ^ 3 = 1)
    (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅⁅a, b⁆, c⁆ = 1)
    (h4 : 3 ^ 4 ≤ Nat.card (↥Y ⧸ center ↥Y)) : False := by
  classical
  let N : Subgroup M := (StatedScalars (Fin 3) K).subgroupOf M
  let π : M →* T := e.symm.toMonoidHom.comp (QuotientGroup.mk' N)
  have hπ : Function.Surjective π := e.symm.surjective.comp (QuotientGroup.mk'_surjective N)
  have hπker : π.ker = N := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  let P : Subgroup M := Y.comap π
  let f : P →* T := π.comp P.subtype
  let ρ : P →* GL (Fin 3) K := M.subtype.comp P.subtype
  have hρ : Function.Injective ρ := M.subtype_injective.comp P.subtype_injective
  have hfrange : f.range = Y := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact Subgroup.map_comap_eq_self_of_surjective hπ Y
  have hfmem : ∀ p : P, f p ∈ Y := fun p => p.2
  have hexp' : ∀ x : P, f x ^ 3 = 1 := fun x => hexp (f x) (hfmem x)
  refine false_of_cover hqK ρ hρ (fun p => hdet p.1.1 p.1.2) f ?_ hexp' ?_ ?_ ?_
  · intro z hz
    have hzM : (z : M) ∈ π.ker := hz
    rw [hπker] at hzM
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hzM
    exact ⟨c, hc.symm⟩
  · intro a b c
    rw [map_commutatorElement, map_commutatorElement]
    exact hcl (f a) (hfmem a) (f b) (hfmem b) (f c) (hfmem c)
  · intro C hC
    have hDe : IsElementaryAbelian 3 (C.map f) :=
      { is_comm := ⟨fun a b => by
          obtain ⟨p, hp, hpa⟩ := a.2
          obtain ⟨r, hr, hrb⟩ := b.2
          apply Subtype.ext
          rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hpa, ← hrb, ← map_mul, ← map_mul, hC p hp r hr]⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun y => by
          obtain ⟨p, -, hpy⟩ := y.2
          apply Subtype.ext
          rw [Subgroup.coe_pow, Subgroup.coe_one, ← hpy]
          exact hexp' p }
    exact card_le_of_statedProj_three hqK M hdet e hDe
  · rw [card_quotient_center_congr (MulEquiv.subgroupCongr hfrange)]
    exact h4

theorem false_psl3_nonab {T : Type} [Group T] {f : ℕ} (hmod : StatedClassicalModel T .PSL 3 2 f)
    {Y : Subgroup T} (hexp : ∀ y ∈ Y, y ^ 3 = 1)
    (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅⁅a, b⁆, c⁆ = 1)
    (h4 : 3 ^ 4 ≤ Nat.card (↥Y ⧸ Subgroup.center ↥Y)) : False := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hqK : (3 : K) ≠ 0 := by
    simpa using natCast_ne_zero_of_card_two_pow hK Nat.prime_three (by norm_num)
  exact false_of_statedProj_three_nonab hqK (StatedSL 3 K)
    (fun g hg => det_eq_one_of_mem_statedSL' hg) e hexp hcl h4

theorem false_psu3_nonab {T : Type} [Group T] {f : ℕ} (hmod : StatedClassicalModel T .PSU 3 2 f)
    {Y : Subgroup T} (hexp : ∀ y ∈ Y, y ^ 3 = 1)
    (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅⁅a, b⁆, c⁆ = 1)
    (h4 : 3 ^ 4 ≤ Nat.card (↥Y ⧸ Subgroup.center ↥Y)) : False := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hqK : (3 : K) ≠ 0 := by
    simpa using natCast_ne_zero_of_card_two_pow (g := 2 * f)
      (by rw [hK, ← pow_mul, mul_comm]) Nat.prime_three (by norm_num)
  exact false_of_statedProj_three_nonab hqK (StatedSU 3 (2 ^ f) K)
    (fun g hg => det_eq_one_of_mem_statedSU' hg) e hexp hcl h4

end Model

end CFSG.RankThree.PartOne.F106
