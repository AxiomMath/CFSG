module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftOrigRank
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraBasic
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem517

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.LieType.BorelTits

theorem perm3_conj_gens : ∀ a b : Equiv.Perm (Fin 3),
    (a ≠ 1 ∧ a ^ 2 = 1 ∧ b ≠ 1 ∧ b ^ 2 = 1 ∧ a ≠ b) → ∃ y : Equiv.Perm (Fin 3),
      y * Equiv.swap 0 1 * y⁻¹ = a ∧ y * Equiv.swap 1 2 * y⁻¹ = b := by
  decide +kernel

theorem perm3_words_swap : ∀ x : Equiv.Perm (Fin 3), x = 1 ∨ x = Equiv.swap 0 1 ∨
    x = Equiv.swap 1 2 ∨ x = Equiv.swap 0 1 * Equiv.swap 1 2 ∨
    x = Equiv.swap 1 2 * Equiv.swap 0 1 ∨ x = Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 0 1 := by
  decide +kernel

theorem perm3_center : ∀ x : Equiv.Perm (Fin 3), x * Equiv.swap 0 1 = Equiv.swap 0 1 * x →
    x * Equiv.swap 1 2 = Equiv.swap 1 2 * x → x = 1 := by
  decide +kernel

theorem perm3_aut_inner (σ : Equiv.Perm (Fin 3) ≃* Equiv.Perm (Fin 3)) :
    ∃ y : Equiv.Perm (Fin 3), ∀ x, σ x = y * x * y⁻¹ := by
  have h01 : Equiv.swap (0 : Fin 3) 1 ≠ 1 := by decide
  have h12 : Equiv.swap (1 : Fin 3) 2 ≠ 1 := by decide
  have hne : Equiv.swap (0 : Fin 3) 1 ≠ Equiv.swap 1 2 := by decide
  have hsq : ∀ s : Equiv.Perm (Fin 3), s ^ 2 = 1 → σ s ^ 2 = 1 := fun s hs => by
    rw [← map_pow, hs, map_one]
  obtain ⟨y, hy1, hy2⟩ := perm3_conj_gens (σ (Equiv.swap 0 1)) (σ (Equiv.swap 1 2))
    ⟨fun h => h01 (σ.injective (h.trans (map_one σ).symm)), hsq _ (by decide),
      fun h => h12 (σ.injective (h.trans (map_one σ).symm)), hsq _ (by decide),
      fun h => hne (σ.injective h)⟩
  refine ⟨y, fun x => ?_⟩
  rcases perm3_words_swap x with rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · exact hy1.symm
  · exact hy2.symm
  · rw [map_mul, ← hy1, ← hy2]
    group
  · rw [map_mul, ← hy1, ← hy2]
    group
  · rw [map_mul, map_mul, ← hy1, ← hy2]
    group

theorem nonempty_autI_equiv_perm3 {G : Type} [Group G] [Finite G] {H T V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hred : IsTwoReducedIn H V) (hT : IsSylowTwoOf T H)
    (hOJ : twoResidual H ≤ thompsonJ H) {L₀ : Subgroup (MulAut (IntMod V hV))}
    (hJL : autI hV (thompsonJ H) = L₀) (hnat : ActsAsNaturalL2 L₀ (commV L₀)) :
    Nonempty (↥(autI hV H) ≃* Equiv.Perm (Fin 3)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  obtain ⟨e, -, -⟩ := hnat
  set e₀ : ↥L₀ ≃* Equiv.Perm (Fin 3) := e.trans Setup.Lift.sl2F2EquivPerm3 with he₀
  set A := autI hV H with hA
  have hJH : thompsonJ H ≤ H := thompsonJ_le_self H
  have hL₀A : L₀ ≤ A := hJL ▸ autI_mono hV hJH
  have hnorm : ∀ φ ∈ A, ∀ ψ ∈ L₀, φ * ψ * φ⁻¹ ∈ L₀ := by
    intro φ hφ ψ hψ
    rw [← hJL] at hψ ⊢
    obtain ⟨g, hgH, rfl⟩ := (mem_autI hV).1 hφ
    obtain ⟨x, hxJ, rfl⟩ := (mem_autI hV).1 hψ
    refine (mem_autI hV).2 ⟨g * x * g⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.mp
      (GammaExtra.normalizer_le_normalizer_thompsonJ H (Subgroup.le_normalizer hgH)) x).mp hxJ
  have hAT : ∀ φ ∈ A, ∃ ψ ∈ L₀, ∃ τ ∈ autI hV T, φ = ψ * τ := by
    intro φ hφ
    obtain ⟨g, hgH, rfl⟩ := (mem_autI hV).1 hφ
    have hg : (g : G) ∈ ((oTwoUpper H ⊔ T : Subgroup G) : Set G) := by
      rw [← eq_oTwoUpper_sup_of_isSylowTwoOf' hT]
      exact hgH
    rw [Subgroup.coe_mul_of_right_le_normalizer_left (oTwoUpper H) T
      (hT.1.trans (le_normalizer_oTwoUpper H))] at hg
    obtain ⟨k, hk, t, ht, hkt⟩ := hg
    have hkN : k ∈ Subgroup.normalizer (V : Set G) := hHN (oTwoUpper_le H hk)
    have htN : t ∈ Subgroup.normalizer (V : Set G) := hHN (hT.1 ht)
    have hkJ : k ∈ thompsonJ H := hOJ (by rw [twoResidual_eq_oTwoUpper']; exact hk)
    refine ⟨convI hV ⟨k, hkN⟩, hJL ▸ (mem_autI hV).2 ⟨⟨k, hkN⟩, hkJ, rfl⟩,
      convI hV ⟨t, htN⟩, (mem_autI hV).2 ⟨⟨t, htN⟩, ht, rfl⟩, ?_⟩
    rw [← map_mul]
    congr 1
    exact Subtype.ext hkt.symm
  have hcent : ∀ c ∈ A, (∀ ψ ∈ L₀, c * ψ = ψ * c) → c = 1 := by
    set C := A ⊓ Subgroup.centralizer (L₀ : Set (MulAut (IntMod V hV))) with hC
    have hCA : C ≤ A := inf_le_left
    have hZ : ∀ ψ ∈ L₀, (∀ ψ' ∈ L₀, ψ * ψ' = ψ' * ψ) → ψ = 1 := by
      intro ψ hψ hcomm
      have h1 : e₀ ⟨ψ, hψ⟩ = 1 := by
        refine perm3_center _ ?_ ?_
        · obtain ⟨s, hs⟩ := e₀.surjective (Equiv.swap 0 1)
          rw [← hs, ← map_mul, ← map_mul]
          congr 1
          exact Subtype.ext (hcomm s s.2)
        · obtain ⟨s, hs⟩ := e₀.surjective (Equiv.swap 1 2)
          rw [← hs, ← map_mul, ← map_mul]
          congr 1
          exact Subtype.ext (hcomm s s.2)
      have := congrArg Subtype.val ((map_eq_one_iff e₀ e₀.injective).mp h1)
      simpa using this
    have hC2 : IsPGroup 2 ↥C := by
      intro c
      obtain ⟨ψ, hψ, τ, hτ, hc⟩ := hAT c c.2.1
      obtain ⟨g, hgT, hg⟩ := (mem_autI hV).1 hτ
      obtain ⟨b, hb⟩ := hT.2.1 ⟨g, hgT⟩
      have hτb : τ ^ 2 ^ b = 1 := by
        rw [← hg, ← map_pow]
        have : g ^ 2 ^ b = 1 := Subtype.ext (by simpa using congrArg Subtype.val hb)
        rw [this, map_one]
      have hτN : τ ∈ Subgroup.normalizer (L₀ : Set (MulAut (IntMod V hV))) := by
        refine A4.mem_normalizer_of_conj_mem fun ψ' hψ' => ?_
        exact hnorm τ ((autI_mono hV hT.1) hτ) ψ' hψ'
      obtain ⟨ψ'', hψ'', he⟩ := pow_mem_mul_of_normalizes hψ hτN (2 ^ b)
      rw [hτb, mul_one, ← hc] at he
      refine ⟨b, Subtype.ext ?_⟩
      show (c : MulAut (IntMod V hV)) ^ 2 ^ b = 1
      rw [he]
      refine hZ ψ'' hψ'' fun ψ' hψ' => ?_
      rw [← he]
      have hcomm := Subgroup.mem_centralizer_iff.mp c.2.2 ψ' hψ'
      have : (c : MulAut (IntMod V hV)) ^ 2 ^ b ∈
          Subgroup.centralizer (L₀ : Set (MulAut (IntMod V hV))) := Subgroup.pow_mem _ c.2.2 _
      exact (Subgroup.mem_centralizer_iff.mp this ψ' hψ').symm
    have hCn : (C.subgroupOf A).Normal := by
      refine ⟨fun c hc a => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hc ⊢
      refine Subgroup.mem_inf.mpr ⟨(a * c * a⁻¹).2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro ψ hψ
      have hc2 := (Subgroup.mem_inf.mp hc).2
      have hψ' : (a : MulAut (IntMod V hV))⁻¹ * ψ * ((a : MulAut (IntMod V hV))⁻¹)⁻¹ ∈ L₀ :=
        hnorm _ (A.inv_mem a.2) ψ hψ
      have h1 := Subgroup.mem_centralizer_iff.mp hc2 _ hψ'
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at h1 ⊢
      calc ψ * ((a : MulAut (IntMod V hV)) * c * (a : MulAut (IntMod V hV))⁻¹) =
            (a : MulAut (IntMod V hV)) * (((a : MulAut (IntMod V hV))⁻¹ * ψ *
              (a : MulAut (IntMod V hV))) * c) * (a : MulAut (IntMod V hV))⁻¹ := by group
        _ = (a : MulAut (IntMod V hV)) * (c * ((a : MulAut (IntMod V hV))⁻¹ * ψ *
              (a : MulAut (IntMod V hV)))) * (a : MulAut (IntMod V hV))⁻¹ := by rw [h1]
        _ = (a : MulAut (IntMod V hV)) * c * (a : MulAut (IntMod V hV))⁻¹ * ψ := by group
    have hCbot := B2F.eq_bot_of_normal_isPGroup hV hred hCA hCn hC2
    intro c hc hcomm
    have hcC : c ∈ C := ⟨hc, Subgroup.mem_centralizer_iff.mpr fun ψ hψ => (hcomm ψ hψ).symm⟩
    rw [hCbot, Subgroup.mem_bot] at hcC
    exact hcC
  have hAL : A ≤ L₀ := by
    intro φ hφ
    let c : ↥L₀ ≃* ↥L₀ :=
      { toFun := fun ψ => ⟨φ * ψ * φ⁻¹, hnorm φ hφ ψ ψ.2⟩
        invFun := fun ψ => ⟨φ⁻¹ * ψ * φ⁻¹⁻¹, hnorm φ⁻¹ (A.inv_mem hφ) ψ ψ.2⟩
        left_inv := fun ψ => Subtype.ext (by simp [mul_assoc])
        right_inv := fun ψ => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun ψ ψ' => Subtype.ext (by simp [mul_assoc]) }
    obtain ⟨y, hy⟩ := perm3_aut_inner ((e₀.symm.trans c).trans e₀)
    set j : ↥L₀ := e₀.symm y with hj
    have hφj : φ * (j : MulAut (IntMod V hV))⁻¹ = 1 := by
      refine hcent _ (A.mul_mem hφ (A.inv_mem (hL₀A j.2))) fun ψ hψ => ?_
      have h1 := hy (e₀ (j⁻¹ * ⟨ψ, hψ⟩ * j))
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
      have h2 : c (j⁻¹ * ⟨ψ, hψ⟩ * j) = ⟨ψ, hψ⟩ := by
        apply e₀.injective
        rw [h1, map_mul, map_mul, map_inv, hj, MulEquiv.apply_symm_apply]
        group
      have h3 := congrArg Subtype.val h2
      simp only [c, MulEquiv.coe_mk, Equiv.coe_fn_mk, Subgroup.coe_mul, Subgroup.coe_inv] at h3
      calc φ * (j : MulAut (IntMod V hV))⁻¹ * ψ =
            (φ * ((j : MulAut (IntMod V hV))⁻¹ * ψ * j) * φ⁻¹) *
              (φ * (j : MulAut (IntMod V hV))⁻¹) := by group
        _ = ψ * (φ * (j : MulAut (IntMod V hV))⁻¹) := by rw [h3]
    have : φ = j := by
      have := congrArg (· * (j : MulAut (IntMod V hV))) hφj
      simpa using this
    rw [this]
    exact j.2
  have heq : A = L₀ := le_antisymm hAL hL₀A
  exact ⟨(MulEquiv.subgroupCongr heq).trans e₀⟩

end CFSG.Quasithin.H13.A5
