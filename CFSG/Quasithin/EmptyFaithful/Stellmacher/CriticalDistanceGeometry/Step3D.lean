module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Step3Chain

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 Equiv CFSG.Quasithin.EmptyFaithful.Stellmacher

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace Step3Ctx

variable {α β α' : Geo H M} (C : Step3Ctx H M S α β α')

include C

theorem commute_of_odd_order {γ : Geo H M} (hγ : vtype γ = false) {x : G}
    (hx : x ∈ Ctilde γ) {l : G} (hl : l ∈ stab γ) {m : ℕ} (hm : Odd m) (hlm : l ^ m = 1) :
    l * x * l⁻¹ * x⁻¹ = 1 := by
  have hLX := Zv_le_Vn_self C.hA γ
  have := (C.isSec_Vn γ).normal_subgroupOf
  rw [Ctilde, X1512.mem_fixSecIn hLX] at hx
  obtain ⟨hxV, hxc⟩ := hx
  have hlO : l ∈ oTwoRes (stab γ) := Subgroup.subset_closure ⟨hl, m, hm, hlm⟩
  set c := l * x * l⁻¹ * x⁻¹ with hc
  have hcZ : c ∈ Zv γ := hxc l hlO
  have hcen : ∀ k : ℕ, l * c ^ k * l⁻¹ = c ^ k := by
    intro k
    have hck : c ^ k ∈ Zv γ := Subgroup.pow_mem _ hcZ k
    have h := (Subgroup.mem_centralizer_iff.mp (C.Zv_le_center hγ hck).2 l hl)
    rw [h]; group
  have hconj : ∀ k : ℕ, l ^ k * x * (l ^ k)⁻¹ = c ^ k * x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : l ^ (k + 1) * x * (l ^ (k + 1))⁻¹ = l * (l ^ k * x * (l ^ k)⁻¹) * l⁻¹ := by
        rw [pow_succ']; group
      rw [e, ih]
      have e2 : l * (c ^ k * x) * l⁻¹ = (l * c ^ k * l⁻¹) * (l * x * l⁻¹) := by group
      rw [e2, hcen k]
      have e3 : l * x * l⁻¹ = c * x := by rw [hc]; group
      rw [e3, pow_succ]; group
  have h1 : c ^ m = 1 := by
    have := hconj m
    rw [hlm] at this
    simpa using this.symm
  have h2 : c ^ 2 = 1 := (C.isElemAbelian_Vn' γ).2 c (Zv_le_Vn_self C.hA γ hcZ)
  obtain ⟨j, rfl⟩ := hm
  rw [pow_succ, pow_mul, h2, one_pow, one_mul] at h1
  simpa [hc] using h1

theorem Ctilde_eq_centralizer {γ : Geo H M} (hγ : vtype γ = false) :
    Ctilde γ = Vn γ ⊓ Subgroup.centralizer (oTwoRes (stab γ) : Set G) := by
  have hLX := Zv_le_Vn_self C.hA γ
  have := (C.isSec_Vn γ).normal_subgroupOf
  apply le_antisymm
  · intro x hx
    refine ⟨fixSecIn_le_sec _ _ _ hx, ?_⟩
    have hle : oTwoRes (stab γ) ≤ Subgroup.centralizer ({x} : Set G) := by
      rw [oTwoRes, Subgroup.closure_le]
      rintro l ⟨hl, m, hm, hlm⟩
      have h := C.commute_of_odd_order hγ hx hl hm hlm
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      calc l * x = (l * x * l⁻¹ * x⁻¹) * (x * l) := by group
        _ = x * l := by rw [h, one_mul]
    show x ∈ Subgroup.centralizer _
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hl)
  · rintro x ⟨hxV, hxc⟩
    rw [Ctilde, X1512.mem_fixSecIn hLX]
    refine ⟨hxV, fun a ha => ?_⟩
    have := Subgroup.mem_centralizer_iff.mp hxc a ha
    rw [this]
    simp

theorem comm_Ctilde_oTwoRes {γ : Geo H M} (hγ : vtype γ = false) :
    ⁅Ctilde γ, oTwoRes (stab γ)⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  rw [C.Ctilde_eq_centralizer hγ]
  exact fun x hx => hx.2

theorem exists_smul_γ_δ_ε (P : CritPath α β α') {l : Geo H M} (hl : l ∈ nbrs α')
    (hlγ : l ≠ P.γ) :
    ∃ g : ↥(H ⊔ M), g • P.γ = P.γ ∧ g • P.δ = α' ∧ g • P.ε = l := by
  have hb := C.hb6
  obtain ⟨g0, hg0γ, hg0δ⟩ := C.exists_smul_γ_δ P
  have hγ' : P.γ ∈ nbrs α' := mem_nbrs_comm (P.γ_adj (by omega))
  have hl0 : g0 • P.ε ∈ nbrs α' := by
    have := (smul_mem_nbrs_iff g0 (l := P.δ) (δ := P.ε)).mpr
      (mem_nbrs_comm (P.ε_adj (by omega)))
    rwa [hg0δ] at this
  have hl0γ : g0 • P.ε ≠ P.γ := by
    intro h
    apply C.γ_ne_ε P
    have : g0 • P.ε = g0 • P.γ := h.trans hg0γ.symm
    exact (smul_left_cancel g0 this).symm
  by_cases hll : g0 • P.ε = l
  · exact ⟨g0, hg0γ, hg0δ, hll⟩
  · obtain ⟨z, hzZ, hzQ⟩ := IsConcreteLE.not_le_iff_exists.mp C.hc.not_le
    have hzα' : z ∈ stab α' := (Zv_le_stab_pair C.hA C.hc C.hcomm).2 hzZ
    have hzγ : z ∈ stab P.γ :=
      Zv_le_stab_of_dist_le_bMin C.hA (by rw [P.dist_start_γ (by omega)]; omega) hzZ
    let zz : ↥(H ⊔ M) := ⟨z, stab_le _ hzα'⟩
    have hzzγ : zz • P.γ = P.γ := smul_eq_of_mem_stab hzγ
    have hzzα' : zz • α' = α' := smul_eq_of_mem_stab hzα'
    have hz1 : zz • (g0 • P.ε) ∈ nbrs α' := smul_mem_nbrs hzα' hl0
    have hz2 : zz • (g0 • P.ε) ≠ P.γ := by
      intro h
      apply hl0γ
      exact smul_left_cancel zz (h.trans hzzγ.symm)
    have hz3 : zz • (g0 • P.ε) ≠ g0 • P.ε := by
      intro h
      exact hzQ (mem_Qv_of_fixes_two_nbrs C.hA C.vtype_alpha' hγ' hl0 hl0γ.symm hzα' hzγ
        (mem_stab_of_smul_eq h))
    have hn := eq_of_three_mem_nbrs C.hA C.vtype_alpha' hl0γ.symm hlγ.symm hll hγ' hl0 hl
    have hz4 : zz • (g0 • P.ε) = l := by
      have hm : zz • (g0 • P.ε) ∈ ({P.γ, g0 • P.ε, l} : Set (Geo H M)) := hn ▸ hz1
      rcases hm with h | h | h
      · exact absurd h hz2
      · exact absurd h hz3
      · exact h
    refine ⟨zz * g0, ?_, ?_, ?_⟩
    · rw [mul_smul, hg0γ, hzzγ]
    · rw [mul_smul, hg0δ, hzzα']
    · rw [mul_smul]; exact hz4

theorem Vn_inf_smul_ε (P : CritPath α β α') {g : ↥(H ⊔ M)} (hgγ : g • P.γ = P.γ) :
    Vn P.γ ⊓ Vn (g • P.ε) = conjSub (g : G) (Vn P.γ ⊓ Vn P.ε) := by
  rw [conjSub_inf, ← Vn_smul, ← Vn_smul, hgγ]

theorem Ctilde_le_Vn_inf (P : CritPath α β α') {l : Geo H M} (hl : l ∈ nbrs α')
    (hlγ : l ≠ P.γ) : Ctilde P.γ ≤ Vn P.γ ⊓ Vn l := by
  obtain ⟨g, hgγ, -, hgε⟩ := C.exists_smul_γ_δ_ε P hl hlγ
  rw [← hgε, C.Vn_inf_smul_ε P hgγ]
  have hN := C.Ctilde_normal P.γ (mem_stab_of_smul_eq hgγ)
  calc Ctilde P.γ = conjSub (g : G) (Ctilde P.γ) := (conjSub_eq_of_mem_normalizer hN).symm
    _ ≤ conjSub (g : G) (Vn P.γ ⊓ Vn P.ε) := conjSub_mono _ (C.Ctilde_le_inter P (C.vhatData P))

end Step3Ctx

end F53.Stellmacher

end CFSG.Quasithin
