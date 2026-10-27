module

public import CFSG.Quasithin.H13.U4ParOuter
public import CFSG.Quasithin.H13.U4ParYAmalgam
public import CFSG.Quasithin.H13.U4ParTorus

public section

namespace CFSG.Quasithin.H13.U4Par

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.BorelTits

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

omit h in
theorem exists_mul_eq_of_mem_sup_of_le_normalizer {Y : Type} [Group Y] {N H : Subgroup Y}
    (hH : H ≤ Subgroup.normalizer (N : Set Y)) {x : Y} (hx : x ∈ N ⊔ H) :
    ∃ n ∈ N, ∃ y ∈ H, n * y = x := by
  let X : Subgroup Y :=
    { carrier := {g | ∃ n ∈ N, ∃ y ∈ H, n * y = g}
      one_mem' := ⟨1, N.one_mem, 1, H.one_mem, mul_one 1⟩
      mul_mem' := by
        rintro _ _ ⟨n₁, hn₁, y₁, hy₁, rfl⟩ ⟨n₂, hn₂, y₂, hy₂, rfl⟩
        refine ⟨n₁ * (y₁ * n₂ * y₁⁻¹), N.mul_mem hn₁
          ((Subgroup.mem_normalizer_iff.mp (hH hy₁) n₂).mp hn₂), y₁ * y₂, H.mul_mem hy₁ hy₂, ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨n, hn, y, hy, rfl⟩
        refine ⟨y⁻¹ * n⁻¹ * y⁻¹⁻¹, (Subgroup.mem_normalizer_iff.mp (hH (H.inv_mem hy)) n⁻¹).mp
          (N.inv_mem hn), y⁻¹, H.inv_mem hy, ?_⟩
        group }
  exact (sup_le (fun n hn => ⟨n, hn, 1, H.one_mem, mul_one n⟩)
    (fun y hy => ⟨1, N.one_mem, y, hy, one_mul y⟩) : N ⊔ H ≤ X) hx

theorem frobElt_apply (g : hypSU h 2 0) (i j : Ix) :
    (((frobElt h g : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) i j =
      h.bar ((((g : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) i j) := by
  rw [coe_frobElt]
  rfl

theorem frobElt_mem_parP {g : hypSU h 2 0} (hg : g ∈ parP h) : frobElt h g ∈ parP h := by
  rw [mem_parP_iff] at hg ⊢
  intro a ha
  rw [frobElt_apply, hg a ha, map_zero]

theorem chi_frobElt (g : hypSU h 2 0) : chi h (frobElt h g) = h.bar (chi h g) :=
  frobElt_apply h g ie1 ie1

theorem frobElt_mem_parP2 {g : hypSU h 2 0} (hg : g ∈ parP2 h) : frobElt h g ∈ parP2 h := by
  rw [mem_parP2_iff] at hg ⊢
  obtain ⟨c1, c2, c3, c4⟩ := hg
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [frobElt_apply] <;> simp [c1, c2, c3, c4]

theorem rho2_frobElt (g : hypSU h 2 0) : rho2 h (frobElt h g) = (rho2 h g).map h.bar := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rho2, frobElt_apply]

theorem frobElt_mem_radQ {g : hypSU h 2 0} (hg : g ∈ radQ h) : frobElt h g ∈ radQ h := by
  obtain ⟨x, y, c, hc, hG⟩ := hg
  refine ⟨h.bar x, h.bar y, h.bar c, ?_, ?_⟩
  · unfold SAdm at hc ⊢
    have := congrArg h.bar hc
    simpa only [map_add, map_mul] using this
  · rw [coe_frobElt, hG]
    ext i j
    rcases ix_cases i with rfl | rfl | rfl | rfl <;>
      rcases ix_cases j with rfl | rfl | rfl | rfl <;>
      simp [map_apply, sMat_apply, one_apply, ie1, ie2, if1, if2, h.bar_bar]

theorem frobElt_mem_hypUnitriangular {g : hypSU h 2 0} (hg : g ∈ hypUnitriangular h 2 0) :
    frobElt h g ∈ hypUnitriangular h 2 0 := by
  obtain ⟨hbt, hdiag⟩ := mem_hypUnitriangular.mp hg
  refine mem_hypUnitriangular.mpr ⟨fun i j hij => ?_, fun a => ?_⟩
  · rw [frobElt_apply, hbt hij, map_zero]
  · rw [frobElt_apply, hdiag a, map_one]

theorem frobElt_levHom (A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField) :
    frobElt h (levHom h A) = levHom h A := by
  apply hypSU_ext h
  rw [coe_frobElt, coe_levHom]
  have hA := slMat_bar h A
  have e : ∀ a b : Fin 2, h.bar (slMat h A a b) = slMat h A a b := fun a b =>
    congrFun (congrFun hA a) b
  ext i j
  rw [map_apply, levMat_apply]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [e, ie1, ie2, if1, if2]

theorem frobElt_mul_inv_mem_radQ {ℓ : hypSU h 2 0} (hℓ : ℓ ∈ perfectCore (parP h)) :
    frobElt h ℓ * ℓ⁻¹ ∈ radQ h := by
  have hℓ' := parH_le_radQ_sup h (perfectCore_parP_le_parH h hℓ)
  have hN : (levHom h).range ≤ Subgroup.normalizer (radQ h : Set (hypSU h 2 0)) :=
    (levHom_le_parP h).trans (parP_le_normalizer_radQ h)
  obtain ⟨s, hs, l, ⟨A, rfl⟩, rfl⟩ := exists_mul_eq_of_mem_sup_of_le_normalizer hN hℓ'
  have hf : frobElt h (s * levHom h A) = frobElt h s * levHom h A := by
    rw [← frob_apply, map_mul, frob_apply, frob_apply, frobElt_levHom]
  rw [hf]
  have e : frobElt h s * levHom h A * (s * levHom h A)⁻¹ = frobElt h s * s⁻¹ := by group
  rw [e]
  exact (radQ h).mul_mem (frobElt_mem_radQ h hs) ((radQ h).inv_mem hs)

theorem pCoreOf_perfectCore_parP2_eq (hm : 2 ≤ m) :
    pCoreOf 2 (perfectCore (parP2 h)) = radQ2 h := by
  refine le_antisymm (pCoreOf_perfectCore_parP2_le_radQ2 h) ?_
  refine le_pCoreOf 2 (radQ2_le_perfectCore_parP2 h hm)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (radQ2_le_perfectCore_parP2 h hm)).mpr
      ((perfectCore_le _).trans (parP2_le_normalizer_radQ2 h)))
    ((pCoreOf_isPGroup 2 (parP2 h)).to_le (radQ2_le_pCoreOf_parP2 h))

theorem rho2_eq_one_of_mem_radQ2 {g : hypSU h 2 0} (hg : g ∈ radQ2 h) : rho2 h g = 1 := by
  obtain ⟨a1, a2, a3, a4, -⟩ := hg
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rho2, a1, a2, a3, a4]

@[expose] noncomputable def frobFix : Subgroup (hypSU h 2 0) where
  carrier := {g | frobElt h g = g}
  mul_mem' {a b} ha hb := by
    change frobElt h (a * b) = a * b
    rw [← frob_apply, map_mul, frob_apply, frob_apply]
    exact congrArg₂ (· * ·) ha hb
  one_mem' := by
    change frobElt h 1 = 1
    rw [← frob_apply, map_one]
  inv_mem' {a} ha := by
    change frobElt h a⁻¹ = a⁻¹
    rw [← frob_apply, map_inv, frob_apply]
    exact congrArg (·⁻¹) ha

theorem mem_frobFix {g : hypSU h 2 0} : g ∈ frobFix h ↔ frobElt h g = g := Iff.rfl

section Outer

variable {Ŷ : Type} [Group Ŷ] {ψ : hypSU h 2 0 →* Ŷ} {y₀ : Ŷ}
  (hact : ∀ g, y₀ * ψ g * y₀⁻¹ = ψ (frob h g))
include hact

theorem inv_conj_eq_frob (g : hypSU h 2 0) : y₀⁻¹ * ψ g * y₀ = ψ (frob h g) := by
  have e := hact (frob h g)
  rw [frob_apply, frob_apply, frobElt_frobElt, ← frob_apply] at e
  calc y₀⁻¹ * ψ g * y₀ = y₀⁻¹ * (y₀ * ψ (frob h g) * y₀⁻¹) * y₀ := by rw [e]
    _ = ψ (frob h g) := by group

theorem mem_normalizer_map_of_frob {X : Subgroup (hypSU h 2 0)}
    (hX : ∀ g ∈ X, frobElt h g ∈ X) :
    y₀ ∈ Subgroup.normalizer ((X.map ψ : Subgroup Ŷ) : Set Ŷ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨frob h g, hX g hg, (hact g).symm⟩
  · rintro ⟨g, hg, hgz⟩
    refine ⟨frob h g, hX g hg, ?_⟩
    rw [← inv_conj_eq_frob h hact, hgz]
    group

theorem map_inf_centralizer (hψ : Function.Injective ψ) (X : Subgroup (hypSU h 2 0)) :
    X.map ψ ⊓ Subgroup.centralizer ({y₀} : Set Ŷ) = (X ⊓ frobFix h).map ψ := by
  ext z
  constructor
  · rintro ⟨⟨g, hg, rfl⟩, hc⟩
    refine ⟨g, ⟨hg, ?_⟩, rfl⟩
    have e := Subgroup.mem_centralizer_iff.mp hc y₀ (Set.mem_singleton y₀)
    apply hψ
    calc ψ (frobElt h g) = y₀ * ψ g * y₀⁻¹ := by rw [← frob_apply, hact g]
      _ = ψ g * y₀ * y₀⁻¹ := by rw [e]
      _ = ψ g := by group
  · rintro ⟨g, ⟨hg, hf⟩, rfl⟩
    refine ⟨⟨g, hg, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have e := hact g
    rw [frob_apply, (mem_frobFix h).mp hf] at e
    calc y₀ * ψ g = y₀ * ψ g * y₀⁻¹ * y₀ := by group
      _ = ψ g * y₀ := by rw [e]

theorem pCoreOf_normalizer_parP (hm : 2 ≤ m) [Finite Ŷ] (hψ : Function.Injective ψ)
    (hidx : ψ.range.index = 2) (hy₀ : y₀ ∉ ψ.range) {M : Subgroup Ŷ}
    (hM : M = Subgroup.normalizer (((parP h).map ψ : Subgroup Ŷ) : Set Ŷ))
    (hMψ : M ⊓ ψ.range = (parP h).map ψ) :
    pCoreOf 2 M = (radQ h).map ψ := by
  classical
  have := h.finite
  have := finite_hypSU h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : ψ.range.Normal := Subgroup.normal_of_index_eq_two hidx
  have hPM : (parP h).map ψ ≤ M := hM ▸ Subgroup.le_normalizer
  have hy₀M : y₀ ∈ M := hM ▸ mem_normalizer_map_of_frob h hact fun g hg => frobElt_mem_parP h hg
  have hQcore : (radQ h).map ψ = pCoreOf 2 (perfectCore ((parP h).map ψ)) := by
    rw [← map_perfectCore, pCoreOf_map_of_inj hψ, pCoreOf_perfectCore_parP h hm]
  have hMQ : M ≤ Subgroup.normalizer (((radQ h).map ψ : Subgroup Ŷ) : Set Ŷ) := by
    rw [hQcore, hM]
    exact (normalizer_le_normalizer_perfectCore _).trans (normalizer_le_normalizer_pCoreOf 2 _)
  have hQM : (radQ h).map ψ ≤ M := (Subgroup.map_mono (radQ_le_parP h)).trans hPM
  refine le_antisymm ?_ (le_pCoreOf 2 hQM
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hQM).mpr hMQ) ((radQ_isPGroup h).map ψ))
  set R := pCoreOf 2 M with hR
  have hRM : R ≤ M := pCoreOf_le 2 M
  have hMR : M ≤ Subgroup.normalizer (R : Set Ŷ) := le_normalizer_pCoreOf 2 M
  have hR2 : IsPGroup 2 R := pCoreOf_isPGroup 2 M
  have hRY : R ⊓ ψ.range ≤ (radQ h).map ψ := by
    have hle : R ⊓ ψ.range ≤ (parP h).map ψ := by
      rw [← hMψ]
      exact inf_le_inf_right _ hRM
    have hXP : (R ⊓ ψ.range).comap ψ ≤ parP h := fun g hg =>
      (Subgroup.mem_map_iff_mem hψ).mp (hle hg)
    have hX2 : IsPGroup 2 ((R ⊓ ψ.range).comap ψ) :=
      (hR2.to_le inf_le_left).comap_of_injective ψ hψ
    have hXc := le_perfectCore_parP_of_isPGroup h hm hX2 hXP
    have hXn : perfectCore (parP h) ≤
        Subgroup.normalizer (((R ⊓ ψ.range).comap ψ : Subgroup _) : Set (hypSU h 2 0)) := by
      intro g hg
      have hgM : ψ g ∈ M := hPM ⟨g, perfectCore_le _ hg, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have h1 := Subgroup.mem_normalizer_iff.mp (hMR hgM) (ψ x)
      simp only [Subgroup.mem_comap, Subgroup.mem_inf, map_mul, map_inv]
      constructor
      · rintro ⟨hxR, -⟩
        exact ⟨h1.mp hxR, ⟨g * x * g⁻¹, by simp⟩⟩
      · rintro ⟨hxR, -⟩
        exact ⟨h1.mpr hxR, ⟨x, rfl⟩⟩
    have hXQ : (R ⊓ ψ.range).comap ψ ≤ radQ h := by
      rw [← pCoreOf_perfectCore_parP h hm]
      exact le_pCoreOf 2 hXc ((Subgroup.normal_subgroupOf_iff_le_normalizer hXc).mpr hXn) hX2
    intro z hz
    obtain ⟨g, hg⟩ := (Subgroup.mem_inf.mp hz).2
    refine ⟨g, hXQ ?_, hg⟩
    rw [Subgroup.mem_comap, hg]
    exact hz
  have hRY0 : R ≤ ψ.range := by
    intro w hw
    by_contra hwY
    have hy₀i : y₀⁻¹ ∉ ψ.range := fun h' => hy₀ (by simpa using ψ.range.inv_mem h')
    have hwy : w * y₀⁻¹ ∈ ψ.range :=
      (Subgroup.mul_mem_iff_of_index_two hidx).mpr (iff_of_false hwY hy₀i)
    obtain ⟨p, hpP, hp⟩ : w * y₀⁻¹ ∈ (parP h).map ψ := by
      rw [← hMψ]
      exact ⟨M.mul_mem (hRM hw) (M.inv_mem hy₀M), hwy⟩
    obtain ⟨a, ha, hμ⟩ := exists_torus_scalar h
    have htP := torElt_mem_parP h ha
    set t := torElt h ha with ht
    have htM : ψ t ∈ M := hPM ⟨t, htP, rfl⟩
    have hcR : w * ψ t * w⁻¹ * (ψ t)⁻¹ ∈ R := by
      have h1 : ψ t * w⁻¹ * (ψ t)⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.mp (hMR htM) w⁻¹).mp (R.inv_mem hw)
      have e : w * ψ t * w⁻¹ * (ψ t)⁻¹ = w * (ψ t * w⁻¹ * (ψ t)⁻¹) := by group
      rw [e]
      exact R.mul_mem hw h1
    have hw' : w = ψ p * y₀ := by rw [hp]; group
    have hcomp : w * ψ t * w⁻¹ * (ψ t)⁻¹ = ψ (p * frob h t * p⁻¹ * t⁻¹) := by
      rw [hw', map_mul, map_mul, map_mul, map_inv, map_inv, ← hact t]
      group
    have hcY : w * ψ t * w⁻¹ * (ψ t)⁻¹ ∈ ψ.range := by
      rw [hcomp]
      exact ⟨_, rfl⟩
    obtain ⟨g, hgQ, hg⟩ := hRY ⟨hcR, hcY⟩
    rw [hcomp] at hg
    have hgeq := hψ hg
    rw [hgeq] at hgQ
    have hchi := (chi_rho_of_mem_radQ h hgQ).1
    have hfP : frob h t ∈ parP h := frobElt_mem_parP h htP
    have hpi : p⁻¹ ∈ parP h := (parP h).inv_mem hpP
    have hti : t⁻¹ ∈ parP h := (parP h).inv_mem htP
    rw [chi_mul h hti, chi_mul h hpi, chi_mul h hfP, frob_apply, chi_frobElt] at hchi
    have hcp := chi_mul_inv h hpP
    have hct := chi_mul_inv h htP
    have hchit : chi h t = a := by
      simp [chi, ht, coe_torElt, torMat, torDiag]
    have hb : h.bar a = a⁻¹ := bar_eq_inv_of_bar_mul h ha
    have ha0 := ne_zero_of_bar_mul h ha
    rw [hchit] at hct hchi
    rw [hb] at hchi
    have hti' : chi h t⁻¹ = a⁻¹ := by
      field_simp at hct ⊢
      linear_combination hct
    rw [hti'] at hchi
    have hpi' : chi h p⁻¹ = (chi h p)⁻¹ := by
      have hp0 : chi h p ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hcp
        exact zero_ne_one hcp
      field_simp
      linear_combination hcp
    rw [hpi'] at hchi
    have hp0 : chi h p ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hcp
      exact zero_ne_one hcp
    have haa : a⁻¹ * a⁻¹ = 1 := by
      field_simp at hchi ⊢
      linear_combination hchi
    apply hμ
    rw [haa, map_one]
  exact (le_inf le_rfl hRY0).trans hRY

theorem pCoreOf_normalizer_parP2 (hm : 2 ≤ m) [Finite Ŷ] (hψ : Function.Injective ψ)
    (hidx : ψ.range.index = 2) (hy₀ : y₀ ∉ ψ.range) {M : Subgroup Ŷ}
    (hM : M = Subgroup.normalizer (((parP2 h).map ψ : Subgroup Ŷ) : Set Ŷ))
    (hMψ : M ⊓ ψ.range = (parP2 h).map ψ) :
    pCoreOf 2 M = (radQ2 h).map ψ := by
  classical
  have := h.finite
  have := finite_hypSU h
  have := h.charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : ψ.range.Normal := Subgroup.normal_of_index_eq_two hidx
  have hPM : (parP2 h).map ψ ≤ M := hM ▸ Subgroup.le_normalizer
  have hy₀M : y₀ ∈ M := hM ▸ mem_normalizer_map_of_frob h hact fun g hg => frobElt_mem_parP2 h hg
  have hQcore : (radQ2 h).map ψ = pCoreOf 2 (perfectCore ((parP2 h).map ψ)) := by
    rw [← map_perfectCore, pCoreOf_map_of_inj hψ, pCoreOf_perfectCore_parP2_eq h hm]
  have hMQ : M ≤ Subgroup.normalizer (((radQ2 h).map ψ : Subgroup Ŷ) : Set Ŷ) := by
    rw [hQcore, hM]
    exact (normalizer_le_normalizer_perfectCore _).trans (normalizer_le_normalizer_pCoreOf 2 _)
  have hQM : (radQ2 h).map ψ ≤ M := (Subgroup.map_mono (radQ2_le_parP2 h)).trans hPM
  have hQ2 : IsPGroup 2 (radQ2 h) := (pCoreOf_isPGroup 2 (parP2 h)).to_le (radQ2_le_pCoreOf_parP2 h)
  refine le_antisymm ?_ (le_pCoreOf 2 hQM
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hQM).mpr hMQ) (hQ2.map ψ))
  set R := pCoreOf 2 M with hR
  have hRM : R ≤ M := pCoreOf_le 2 M
  have hMR : M ≤ Subgroup.normalizer (R : Set Ŷ) := le_normalizer_pCoreOf 2 M
  have hR2 : IsPGroup 2 R := pCoreOf_isPGroup 2 M
  have hRY : R ⊓ ψ.range ≤ (radQ2 h).map ψ := by
    have hle : R ⊓ ψ.range ≤ (parP2 h).map ψ := by
      rw [← hMψ]
      exact inf_le_inf_right _ hRM
    have hXP : (R ⊓ ψ.range).comap ψ ≤ parP2 h := fun g hg =>
      (Subgroup.mem_map_iff_mem hψ).mp (hle hg)
    have hX2 : IsPGroup 2 ((R ⊓ ψ.range).comap ψ) :=
      (hR2.to_le inf_le_left).comap_of_injective ψ hψ
    have hXc := le_perfectCore_parP2_of_isPGroup h hm hX2 hXP
    have hXn : perfectCore (parP2 h) ≤
        Subgroup.normalizer (((R ⊓ ψ.range).comap ψ : Subgroup _) : Set (hypSU h 2 0)) := by
      intro g hg
      have hgM : ψ g ∈ M := hPM ⟨g, perfectCore_le _ hg, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have h1 := Subgroup.mem_normalizer_iff.mp (hMR hgM) (ψ x)
      simp only [Subgroup.mem_comap, Subgroup.mem_inf, map_mul, map_inv]
      constructor
      · rintro ⟨hxR, -⟩
        exact ⟨h1.mp hxR, ⟨g * x * g⁻¹, by simp⟩⟩
      · rintro ⟨hxR, -⟩
        exact ⟨h1.mpr hxR, ⟨x, rfl⟩⟩
    have hXQ : (R ⊓ ψ.range).comap ψ ≤ radQ2 h := by
      rw [← pCoreOf_perfectCore_parP2_eq h hm]
      exact le_pCoreOf 2 hXc ((Subgroup.normal_subgroupOf_iff_le_normalizer hXc).mpr hXn) hX2
    intro z hz
    obtain ⟨g, hg⟩ := (Subgroup.mem_inf.mp hz).2
    refine ⟨g, hXQ ?_, hg⟩
    rw [Subgroup.mem_comap, hg]
    exact hz
  have hRY0 : R ≤ ψ.range := by
    intro w hw
    by_contra hwY
    have hy₀i : y₀⁻¹ ∉ ψ.range := fun h' => hy₀ (by simpa using ψ.range.inv_mem h')
    have hwy : w * y₀⁻¹ ∈ ψ.range :=
      (Subgroup.mul_mem_iff_of_index_two hidx).mpr (iff_of_false hwY hy₀i)
    obtain ⟨p, hpP, hp⟩ : w * y₀⁻¹ ∈ (parP2 h).map ψ := by
      rw [← hMψ]
      exact ⟨M.mul_mem (hRM hw) (M.inv_mem hy₀M), hwy⟩
    obtain ⟨z, hz⟩ := h.exists_bar_ne
    set A₀ : Matrix.SpecialLinearGroup (Fin 2) K :=
      ⟨!![1 + z, 1; z, 1], by simp [det_fin_two_of]⟩ with hA₀
    set l := lev2Hom h A₀ with hl
    have hlP : l ∈ parP2 h := lev2Hom_le_parP2 h ⟨A₀, rfl⟩
    have hlM : ψ l ∈ M := hPM ⟨l, hlP, rfl⟩
    have hcR : w * ψ l * w⁻¹ * (ψ l)⁻¹ ∈ R := by
      have h1 : ψ l * w⁻¹ * (ψ l)⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.mp (hMR hlM) w⁻¹).mp (R.inv_mem hw)
      have e : w * ψ l * w⁻¹ * (ψ l)⁻¹ = w * (ψ l * w⁻¹ * (ψ l)⁻¹) := by group
      rw [e]
      exact R.mul_mem hw h1
    have hw' : w = ψ p * y₀ := by rw [hp]; group
    have hcomp : w * ψ l * w⁻¹ * (ψ l)⁻¹ = ψ (p * frob h l * p⁻¹ * l⁻¹) := by
      rw [hw', map_mul, map_mul, map_mul, map_inv, map_inv, ← hact l]
      group
    have hcY : w * ψ l * w⁻¹ * (ψ l)⁻¹ ∈ ψ.range := by
      rw [hcomp]
      exact ⟨_, rfl⟩
    obtain ⟨g, hgQ, hg⟩ := hRY ⟨hcR, hcY⟩
    rw [hcomp] at hg
    have hgeq := hψ hg
    rw [hgeq] at hgQ
    have hrho := rho2_eq_one_of_mem_radQ2 h hgQ
    have hfP : frob h l ∈ parP2 h := frobElt_mem_parP2 h hlP
    have hpi : p⁻¹ ∈ parP2 h := (parP2 h).inv_mem hpP
    have hli : l⁻¹ ∈ parP2 h := (parP2 h).inv_mem hlP
    rw [rho2_mul h hli, rho2_mul h hpi, rho2_mul h hfP, frob_apply, rho2_frobElt,
      rho2_lev2Hom] at hrho
    have hll : rho2 h l⁻¹ * rho2 h l = 1 := by
      rw [← rho2_mul h hlP, inv_mul_cancel, rho2_one]
    have hpp : rho2 h p⁻¹ * rho2 h p = 1 := by
      rw [← rho2_mul h hpP, inv_mul_cancel, rho2_one]
    have hX : rho2 h p * (A₀ : Matrix (Fin 2) (Fin 2) K).map h.bar * rho2 h p⁻¹ =
        (A₀ : Matrix (Fin 2) (Fin 2) K) := by
      have e1 : rho2 h l = (A₀ : Matrix (Fin 2) (Fin 2) K) := rho2_lev2Hom h A₀
      calc rho2 h p * (A₀ : Matrix (Fin 2) (Fin 2) K).map h.bar * rho2 h p⁻¹ =
            rho2 h p * (A₀ : Matrix (Fin 2) (Fin 2) K).map h.bar * rho2 h p⁻¹ *
              (rho2 h l⁻¹ * rho2 h l) := by rw [hll, Matrix.mul_one]
        _ = (rho2 h p * (A₀ : Matrix (Fin 2) (Fin 2) K).map h.bar * rho2 h p⁻¹ *
              rho2 h l⁻¹) * rho2 h l := by simp only [Matrix.mul_assoc]
        _ = (A₀ : Matrix (Fin 2) (Fin 2) K) := by rw [hrho, Matrix.one_mul, e1]
    have htr := congrArg Matrix.trace hX
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hpp, Matrix.mul_one] at htr
    simp [hA₀, Matrix.trace_fin_two, map_add, map_one] at htr
    apply hz
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination htr
  exact (le_inf le_rfl hRY0).trans hRY

omit hact in
theorem mem_normalizer_of_map_le {Y : Type} [Group Y] {C : Subgroup Y} [Finite C] {g : Y}
    (hle : C.map (MulAut.conj g : Y →* Y) ≤ C) : g ∈ Subgroup.normalizer (C : Set Y) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hinj : Function.Injective (MulAut.conj g : Y →* Y) := (MulAut.conj g).injective
  have : Finite ↥(C.map (MulAut.conj g : Y →* Y)) :=
    Finite.of_equiv _ (C.equivMapOfInjective _ hinj).toEquiv
  exact Subgroup.eq_of_le_of_card_ge hle (Subgroup.card_map_of_injective hinj).ge

theorem pCoreOf_perfectCore_sup_zpowers (hm : 2 ≤ m) [Finite Ŷ] (hψ : Function.Injective ψ)
    (hy2 : y₀ * y₀ = 1) :
    pCoreOf 2 ((perfectCore (parP h)).map ψ ⊔ Subgroup.zpowers y₀) =
      (radQ h).map ψ ⊔ Subgroup.zpowers y₀ := by
  classical
  have := h.finite
  have := finite_hypSU h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := (perfectCore (parP h)).map ψ ⊔ Subgroup.zpowers y₀ with hX
  set C := (radQ h).map ψ ⊔ Subgroup.zpowers y₀ with hC
  have hyi : y₀⁻¹ = y₀ := inv_eq_of_mul_eq_one_left hy2
  have hQc : radQ h ≤ perfectCore (parP h) := radQ_le_perfectCore h hm
  have hfc : ∀ g ∈ perfectCore (parP h), frobElt h g ∈ perfectCore (parP h) := fun g hg => by
    have e : frobElt h g = (frobElt h g * g⁻¹) * g := by group
    rw [e]
    exact (perfectCore (parP h)).mul_mem (hQc (frobElt_mul_inv_mem_radQ h hg)) hg
  have hyN : Subgroup.zpowers y₀ ≤
      Subgroup.normalizer (((perfectCore (parP h)).map ψ : Subgroup Ŷ) : Set Ŷ) :=
    (Subgroup.zpowers_le (H := Subgroup.normalizer _)).mpr (mem_normalizer_map_of_frob h hact hfc)
  have hyQ : Subgroup.zpowers y₀ ≤ Subgroup.normalizer (((radQ h).map ψ : Subgroup Ŷ) : Set Ŷ) :=
    (Subgroup.zpowers_le (H := Subgroup.normalizer _)).mpr
      (mem_normalizer_map_of_frob h hact fun g hg => frobElt_mem_radQ h hg)
  have hy2' : y₀ ^ 2 ^ 1 = 1 := by rw [pow_one, pow_two, hy2]
  have hC2 : IsPGroup 2 C :=
    IsPGroup.to_sup_of_normal_left' ((radQ_isPGroup h).map ψ) (isPGroup_zpowers_of_pow hy2') hyQ
  have hCX : C ≤ X := sup_le_sup_right (Subgroup.map_mono hQc) _
  have hQN : ∀ g ∈ (parP h).map ψ, g ∈ Subgroup.normalizer
      (((radQ h).map ψ : Subgroup Ŷ) : Set Ŷ) := fun g hg =>
    Subgroup.le_normalizer_map ψ (Subgroup.map_mono (parP_le_normalizer_radQ h) hg)
  have hXC : X ≤ Subgroup.normalizer (C : Set Ŷ) := by
    refine sup_le ?_ ?_
    · rintro _ ⟨l, hl, rfl⟩
      refine mem_normalizer_of_map_le ?_
      rw [hC, Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rw [Subgroup.mem_normalizer_iff_map_conj_eq.mp (hQN _ ⟨l, perfectCore_le _ hl, rfl⟩)]
        exact le_sup_left
      · rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
        have e : (MulAut.conj (ψ l) : Ŷ →* Ŷ) y₀ = y₀ * ψ (frobElt h l * l⁻¹) := by
          change ψ l * y₀ * (ψ l)⁻¹ = _
          have h1 : ψ (frobElt h l) = y₀ * ψ l * y₀ := by
            rw [← frob_apply, ← inv_conj_eq_frob h hact, hyi]
          rw [map_mul, map_inv, h1]
          calc ψ l * y₀ * (ψ l)⁻¹ = (y₀ * y₀) * ψ l * y₀ * (ψ l)⁻¹ := by rw [hy2, one_mul]
            _ = y₀ * (y₀ * ψ l * y₀ * (ψ l)⁻¹) := by group
        rw [e]
        exact C.mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers y₀))
          (Subgroup.mem_sup_left ⟨_, frobElt_mul_inv_mem_radQ h hl, rfl⟩)
    · rw [Subgroup.zpowers_le]
      refine mem_normalizer_of_map_le ?_
      rw [hC, Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rw [Subgroup.mem_normalizer_iff_map_conj_eq.mp (hyQ (Subgroup.mem_zpowers y₀))]
        exact le_sup_left
      · rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
        have e : (MulAut.conj y₀ : Ŷ →* Ŷ) y₀ = y₀ := by
          change y₀ * y₀ * y₀⁻¹ = y₀
          group
        rw [e]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y₀)
  refine le_antisymm ?_ (le_pCoreOf 2 hCX ((Subgroup.normal_subgroupOf_iff_le_normalizer hCX).mpr
    hXC) hC2)
  set R := pCoreOf 2 X with hR
  have hRX : R ≤ X := pCoreOf_le 2 X
  have hXR : X ≤ Subgroup.normalizer (R : Set Ŷ) := le_normalizer_pCoreOf 2 X
  have hCR : C ≤ R := le_pCoreOf 2 hCX ((Subgroup.normal_subgroupOf_iff_le_normalizer hCX).mpr
    hXC) hC2
  have hRP : R ⊓ (perfectCore (parP h)).map ψ ≤ (radQ h).map ψ := by
    have hPX : (perfectCore (parP h)).map ψ ≤ X := le_sup_left
    have h1 : R ⊓ (perfectCore (parP h)).map ψ ≤ pCoreOf 2 ((perfectCore (parP h)).map ψ) :=
      le_pCoreOf 2 inf_le_right ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr
        (le_inf (hPX.trans hXR) Subgroup.le_normalizer |>.trans
          Subgroup.inf_normalizer_le_normalizer_inf)) ((pCoreOf_isPGroup 2 X).to_le inf_le_left)
    rwa [pCoreOf_map_of_inj hψ, pCoreOf_perfectCore_parP h hm] at h1
  intro r hr
  obtain ⟨n, hn, y, hy, rfl⟩ := exists_mul_eq_of_mem_sup_of_le_normalizer hyN (hRX hr)
  have hyC : y ∈ C := Subgroup.mem_sup_right hy
  have hnR : n ∈ R := by
    have e : n = n * y * y⁻¹ := by group
    rw [e]
    exact R.mul_mem hr (R.inv_mem (hCR hyC))
  exact C.mul_mem (Subgroup.mem_sup_left (hRP ⟨hnR, hn⟩)) hyC

end Outer

end CFSG.Quasithin.H13.U4Par
