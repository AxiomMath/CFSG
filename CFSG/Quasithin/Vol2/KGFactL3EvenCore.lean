module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.H13.KGL3Even

variable {G : Type*} [Group G] {F : Type*} [Field F]

structure LinCoord (U P : Subgroup G) (F : Type*) [Field F] where
  ι : (Fin 2 → F) → G
  ι_add : ∀ c d, ι (c + d) = ι c * ι d
  ι_mem : ∀ c, ι c ∈ U
  ι_surj : ∀ u ∈ U, ∃ c, ι c = u
  ι_inj : Function.Injective ι
  lev : G → (Fin 2 → F) →ₗ[F] (Fin 2 → F)
  conj : ∀ g ∈ P, ∀ c, g * ι c * g⁻¹ = ι (lev g c)

namespace LinCoord

variable {U P : Subgroup G} (L : LinCoord U P F)

theorem ι_zero : L.ι 0 = 1 := by
  have h := L.ι_add 0 0
  rw [add_zero] at h
  exact left_eq_mul.mp h

theorem ι_neg (c : Fin 2 → F) : L.ι (-c) = (L.ι c)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← L.ι_add, neg_add_cancel, L.ι_zero]

theorem ι_sub (c d : Fin 2 → F) : L.ι (c - d) = L.ι c * (L.ι d)⁻¹ := by
  rw [sub_eq_add_neg, L.ι_add, L.ι_neg]

theorem lev_mul {g h : G} (hg : g ∈ P) (hh : h ∈ P) (c : Fin 2 → F) :
    L.lev (g * h) c = L.lev g (L.lev h c) := by
  apply L.ι_inj
  rw [← L.conj _ (P.mul_mem hg hh), ← L.conj _ hg, ← L.conj _ hh, mul_inv_rev]
  group

theorem lev_one (c : Fin 2 → F) : L.lev 1 c = c := by
  apply L.ι_inj
  rw [← L.conj _ P.one_mem]
  group

theorem lev_inv_lev {g : G} (hg : g ∈ P) (c : Fin 2 → F) : L.lev g⁻¹ (L.lev g c) = c := by
  rw [← L.lev_mul (P.inv_mem hg) hg, inv_mul_cancel, L.lev_one]

theorem lev_lev_inv {g : G} (hg : g ∈ P) (c : Fin 2 → F) : L.lev g (L.lev g⁻¹ c) = c := by
  rw [← L.lev_mul hg (P.inv_mem hg), mul_inv_cancel, L.lev_one]

include L in
theorem le_normalizer : P ≤ Subgroup.normalizer (U : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    obtain ⟨c, rfl⟩ := L.ι_surj u hu
    rw [L.conj g hg]
    exact L.ι_mem _
  · intro hu
    obtain ⟨c, hc⟩ := L.ι_surj _ hu
    have h := L.conj g⁻¹ (P.inv_mem hg) c
    rw [hc, inv_inv] at h
    have e : u = g⁻¹ * (g * u * g⁻¹) * g := by group
    rw [e, h]
    exact L.ι_mem _

theorem mem_centralizer {g : G} (hg : g ∈ P) (h : ∀ c, L.lev g c = c) :
    g ∈ Subgroup.centralizer (U : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  obtain ⟨c, rfl⟩ := L.ι_surj u hu
  have e := L.conj g hg c
  rw [h c] at e
  calc L.ι c * g = g * L.ι c * g⁻¹ * g := by rw [e]
    _ = g * L.ι c := by group

theorem commutator_eq {k : G} (hk : k ∈ P) (c : Fin 2 → F) :
    L.ι c * k * (L.ι c)⁻¹ * k⁻¹ = L.ι (c - L.lev k c) := by
  rw [L.ι_sub, ← L.conj k hk]
  group

@[expose] def commSpace (K : Subgroup G) : Submodule F (Fin 2 → F) :=
  ⨆ k : K, LinearMap.range (LinearMap.id - L.lev k)

theorem sub_mem_commSpace {K : Subgroup G} {k : G} (hk : k ∈ K) (c : Fin 2 → F) :
    c - L.lev k c ∈ L.commSpace K :=
  Submodule.mem_iSup_of_mem (⟨k, hk⟩ : K) ⟨c, rfl⟩

theorem lev_mem_commSpace {K : Subgroup G} {k : G} (hk : k ∈ K) {w : Fin 2 → F}
    (hw : w ∈ L.commSpace K) : L.lev k w ∈ L.commSpace K := by
  have h := L.sub_mem_commSpace hk w
  have e : L.lev k w = w - (w - L.lev k w) := by abel
  rw [e]
  exact Submodule.sub_mem _ hw h

theorem commSpace_mem {R₀ K : Subgroup G}
    (hcomm : ∀ c, ∀ k ∈ K, L.ι (c - L.lev k c) ∈ R₀) {w : Fin 2 → F}
    (hw : w ∈ L.commSpace K) : L.ι w ∈ R₀ := by
  refine Submodule.iSup_induction _ (motive := fun w => L.ι w ∈ R₀) hw ?_ ?_ ?_
  · rintro k x ⟨c, rfl⟩
    exact hcomm c k k.2
  · rw [L.ι_zero]
    exact R₀.one_mem
  · intro x y hx hy
    rw [L.ι_add]
    exact R₀.mul_mem hx hy

include L in
theorem eq_or_le_centralizer {R₀ K : Subgroup G} (hR : R₀ ≤ U) (hKP : K ≤ P)
    (hUK : U ≤ Subgroup.normalizer (K : Set G)) (hcore : U ⊓ K ≤ R₀) :
    R₀ = U ∨ ⁅⁅K, K⁆, ⁅K, K⁆⁆ ≤ Subgroup.centralizer (U : Set G) := by
  have hcomm : ∀ c, ∀ k ∈ K, L.ι (c - L.lev k c) ∈ R₀ := by
    intro c k hk
    rw [← L.commutator_eq (hKP hk)]
    refine hcore ⟨?_, ?_⟩
    · rw [L.commutator_eq (hKP hk)]
      exact L.ι_mem _
    · have h1 : L.ι c * k * (L.ι c)⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hUK (L.ι_mem c)) k).mp hk
      exact K.mul_mem h1 (K.inv_mem hk)
  by_cases hW : L.commSpace K = ⊤
  · left
    refine le_antisymm hR fun u hu => ?_
    obtain ⟨c, rfl⟩ := L.ι_surj u hu
    exact L.commSpace_mem hcomm (hW ▸ Submodule.mem_top)
  right
  have hrank : Module.finrank F (L.commSpace K) ≤ 1 := by
    have := Submodule.finrank_lt hW
    rw [Module.finrank_fin_fun] at this
    omega
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hrank
  have hscal : ∀ k ∈ K, ∃ μ : F, ∀ w ∈ L.commSpace K, L.lev k w = μ • w := by
    intro k hk
    obtain ⟨μ, hμ⟩ := hv ⟨L.lev k v, L.lev_mem_commSpace hk v.2⟩
    refine ⟨μ, fun w hw => ?_⟩
    obtain ⟨t, ht⟩ := hv ⟨w, hw⟩
    have hw' : w = t • (v : Fin 2 → F) := (congrArg Subtype.val ht).symm
    have hμ' : L.lev k v = μ • (v : Fin 2 → F) := by
      have := congrArg Subtype.val hμ
      exact this.symm
    rw [hw', map_smul, hμ', smul_comm]
  have hcommW : ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ w ∈ L.commSpace K,
      L.lev k₁ (L.lev k₂ w) = L.lev k₂ (L.lev k₁ w) := by
    intro k₁ hk₁ k₂ hk₂ w hw
    obtain ⟨μ₁, hμ₁⟩ := hscal k₁ hk₁
    obtain ⟨μ₂, hμ₂⟩ := hscal k₂ hk₂
    rw [hμ₂ w hw, map_smul, hμ₁ w hw, map_smul, hμ₂ w hw, smul_smul, smul_smul, mul_comm]
  let H₁ : Subgroup G :=
    { carrier := {x | x ∈ P ∧ ∀ w ∈ L.commSpace K, L.lev x w = w}
      one_mem' := ⟨P.one_mem, fun w _ => L.lev_one w⟩
      mul_mem' := by
        rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
        refine ⟨P.mul_mem hx hy, fun w hw => ?_⟩
        rw [L.lev_mul hx hy, hy' w hw, hx' w hw]
      inv_mem' := by
        rintro x ⟨hx, hx'⟩
        refine ⟨P.inv_mem hx, fun w hw => ?_⟩
        have := L.lev_inv_lev hx w
        rwa [hx' w hw] at this }
  have hK1 : ⁅K, K⁆ ≤ H₁ := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨P.mul_mem (P.mul_mem (P.mul_mem (hKP ha) (hKP hb)) (P.inv_mem (hKP ha)))
      (P.inv_mem (hKP hb)), fun w hw => ?_⟩
    have hPa := hKP ha
    have hPb := hKP hb
    have hw1 : L.lev b⁻¹ w ∈ L.commSpace K := L.lev_mem_commSpace (K.inv_mem hb) hw
    rw [commutatorElement_def, L.lev_mul (P.mul_mem (P.mul_mem hPa hPb) (P.inv_mem hPa))
      (P.inv_mem hPb), L.lev_mul (P.mul_mem hPa hPb) (P.inv_mem hPa), L.lev_mul hPa hPb,
      hcommW b hb a⁻¹ (K.inv_mem ha) _ hw1, L.lev_lev_inv hPb, L.lev_lev_inv hPa]
  have hKK : ⁅K, K⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem h₁ h₂) (K.inv_mem h₁)) (K.inv_mem h₂)
  have hcomm2 : ∀ a ∈ ⁅K, K⁆, ∀ b ∈ ⁅K, K⁆, ∀ c,
      L.lev a (L.lev b c) = L.lev b (L.lev a c) := by
    intro a ha b hb c
    have haK : a ∈ K := hKK ha
    have hbK : b ∈ K := hKK hb
    have hda := L.sub_mem_commSpace haK c
    have hdb := L.sub_mem_commSpace hbK c
    have ea := (hK1 ha).2 _ hdb
    have eb := (hK1 hb).2 _ hda
    rw [map_sub] at ea eb
    have e1 : L.lev a (L.lev b c) = L.lev a c - (c - L.lev b c) := by
      rw [← ea]; abel
    have e2 : L.lev b (L.lev a c) = L.lev b c - (c - L.lev a c) := by
      rw [← eb]; abel
    rw [e1, e2]
    abel
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hPa : a ∈ P := hKP (hKK ha)
  have hPb : b ∈ P := hKP (hKK hb)
  have ha' : a⁻¹ ∈ ⁅K, K⁆ := Subgroup.inv_mem _ ha
  have hb' : b⁻¹ ∈ ⁅K, K⁆ := Subgroup.inv_mem _ hb
  refine L.mem_centralizer (P.mul_mem (P.mul_mem (P.mul_mem hPa hPb) (P.inv_mem hPa))
    (P.inv_mem hPb)) fun c => ?_
  rw [commutatorElement_def, L.lev_mul (P.mul_mem (P.mul_mem hPa hPb) (P.inv_mem hPa))
    (P.inv_mem hPb), L.lev_mul (P.mul_mem hPa hPb) (P.inv_mem hPa), L.lev_mul hPa hPb,
    hcomm2 b hb a⁻¹ ha', L.lev_lev_inv hPa, L.lev_lev_inv hPb]

end LinCoord

end CFSG.Quasithin.H13.KGL3Even
