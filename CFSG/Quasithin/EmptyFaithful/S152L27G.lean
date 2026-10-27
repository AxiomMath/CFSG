module

public import CFSG.Quasithin.EmptyFaithful.S151Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G]

@[expose] def zsMod152 (ZS Z : Subgroup G) (hZ : Z ≤ ZS) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (ZS : Set G) ∧ ∀ s ∈ ZS, g * s * g⁻¹ * s⁻¹ ∈ Z}
  one_mem' := ⟨Subgroup.one_mem _, fun s _ => by simp⟩
  mul_mem' := by
    rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
    refine ⟨Subgroup.mul_mem _ hg hh, fun s hs => ?_⟩
    have hc := hh' s hs
    have hgc : g * (h * s * h⁻¹ * s⁻¹) * g⁻¹ ∈ Z := by
      have h1 := hg' _ (hZ hc)
      have e : g * (h * s * h⁻¹ * s⁻¹) * g⁻¹ =
          (g * (h * s * h⁻¹ * s⁻¹) * g⁻¹ * (h * s * h⁻¹ * s⁻¹)⁻¹) * (h * s * h⁻¹ * s⁻¹) := by
        group
      rw [e]
      exact Z.mul_mem h1 hc
    have e : g * h * s * (g * h)⁻¹ * s⁻¹ =
        (g * (h * s * h⁻¹ * s⁻¹) * g⁻¹) * (g * s * g⁻¹ * s⁻¹) := by group
    rw [e]
    exact Z.mul_mem hgc (hg' s hs)
  inv_mem' := by
    rintro g ⟨hg, hg'⟩
    have hgi : g⁻¹ ∈ Subgroup.normalizer (ZS : Set G) := Subgroup.inv_mem _ hg
    refine ⟨hgi, fun s hs => ?_⟩
    have hs' : g⁻¹ * s * g⁻¹⁻¹ ∈ ZS := (Subgroup.mem_normalizer_iff.mp hgi s).mp hs
    have h1 := hg' _ hs'
    have e : g⁻¹ * s * g⁻¹⁻¹ * s⁻¹ =
        (g * (g⁻¹ * s * g⁻¹⁻¹) * g⁻¹ * (g⁻¹ * s * g⁻¹⁻¹)⁻¹)⁻¹ := by group
    rw [e]
    exact Z.inv_mem h1

theorem centralizer_le_zsMod152 {ZS Z : Subgroup G} (hZ : Z ≤ ZS) :
    Subgroup.centralizer (ZS : Set G) ≤ zsMod152 ZS Z hZ := by
  intro g hg
  have hc : ∀ s ∈ ZS, g * s * g⁻¹ = s := fun s hs => by
    have := (Subgroup.mem_centralizer_iff.mp hg) s hs
    rw [← this]; group
  exact ⟨Subgroup.centralizer_le_normalizer _ hg, fun s hs => by rw [hc s hs]; simp⟩

variable [Finite G]

theorem le_zsMod_of_O2_le_centralizer152 {T P ZS Z : Subgroup G} (hZ : Z ≤ ZS)
    (hT : T ≤ zsMod152 ZS Z hZ) (hsyl : IsSylowTwoOf T P)
    (hO2 : oTwoUpper P ≤ Subgroup.centralizer (ZS : Set G)) : P ≤ zsMod152 ZS Z hZ := by
  rw [eq_oTwoUpper_sup_of_isSylowTwoOf hsyl]
  exact sup_le ((hO2.trans (centralizer_le_zsMod152 hZ))) hT

omit [Finite G] in
theorem oTwoUpper_le_centralizer_of_le152 {T P M Mc V : Subgroup G} (hT2 : IsPGroup 2 T) (hTM : T ≤ M)
    (hMV : M ≤ Subgroup.normalizer (V : Set G)) (hPM : P ≤ M) (hPMc : P ≤ Mc)
    (hinf : M ⊓ Mc ≤ (M ⊓ Subgroup.centralizer (V : Set G)) ⊔ T) :
    oTwoUpper P ≤ Subgroup.centralizer (V : Set G) := by
  have hTn : T ≤ Subgroup.normalizer ((M ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ t ∈ T, ∀ x ∈ M ⊓ Subgroup.centralizer (V : Set G),
        t * x * t⁻¹ ∈ M ⊓ Subgroup.centralizer (V : Set G) := by
      intro t ht x hx
      refine ⟨M.mul_mem (M.mul_mem (hTM ht) hx.1) (M.inv_mem (hTM ht)), ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro v hv
      have hv' : t⁻¹ * v * t⁻¹⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hMV (M.inv_mem (hTM ht))) v).mp hv
      have h1 := (Subgroup.mem_centralizer_iff.mp hx.2) _ hv'
      calc v * (t * x * t⁻¹) = t * ((t⁻¹ * v * t⁻¹⁻¹) * x) * t⁻¹ := by group
        _ = t * (x * (t⁻¹ * v * t⁻¹⁻¹)) * t⁻¹ := by rw [h1]
        _ = t * x * t⁻¹ * v := by group
    intro x
    refine ⟨key t ht x, fun hx => ?_⟩
    have := key t⁻¹ (T.inv_mem ht) _ hx
    simpa [mul_assoc] using this
  have hprod : (((M ⊓ Subgroup.centralizer (V : Set G)) ⊔ T : Subgroup G) : Set G) =
      ((M ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) * (T : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hTn
  refine oTwoUpper_le_of_pow_mem fun x hx => ?_
  have hx' : x ∈ ((M ⊓ Subgroup.centralizer (V : Set G)) ⊔ T : Subgroup G) :=
    hinf ⟨hPM hx, hPMc hx⟩
  have hx'' : x ∈ ((M ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) * (T : Set G) := by
    rw [← hprod]; exact hx'
  obtain ⟨n, hn, t, ht, hx0⟩ := Set.mem_mul.mp hx''
  subst hx0
  obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
  have hk' : t ^ 2 ^ k = 1 := by
    have := congrArg (fun z : T => (z : G)) hk
    simpa using this
  refine ⟨k, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hconj : ∀ m : ℕ, ∀ v ∈ V, (n * t) ^ m * v * ((n * t) ^ m)⁻¹ = t ^ m * v * (t ^ m)⁻¹ := by
    intro m
    induction m with
    | zero => intro v _; simp
    | succ m ih =>
      intro v hv
      have hvm : t ^ m * v * (t ^ m)⁻¹ ∈ V := by
        have hmem : t ^ m ∈ M := (M.pow_mem (hTM ht) m)
        exact (Subgroup.mem_normalizer_iff.mp (hMV hmem) v).mp hv
      have epow : ∀ a : G, a ^ (m + 1) * v * (a ^ (m + 1))⁻¹ =
          a * (a ^ m * v * (a ^ m)⁻¹) * a⁻¹ := by
        intro a; rw [pow_succ']; group
      rw [epow (n * t), epow t, ih v hv]
      have h1 := (Subgroup.mem_centralizer_iff.mp hn.2) _ hvm
      calc n * t * (t ^ m * v * (t ^ m)⁻¹) * (n * t)⁻¹
          = n * (t * (t ^ m * v * (t ^ m)⁻¹) * t⁻¹) * n⁻¹ := by group
        _ = t * (t ^ m * v * (t ^ m)⁻¹) * t⁻¹ := by
          have hw : t * (t ^ m * v * (t ^ m)⁻¹) * t⁻¹ ∈ V :=
            (Subgroup.mem_normalizer_iff.mp (hMV (hTM ht)) _).mp hvm
          have h2 := (Subgroup.mem_centralizer_iff.mp hn.2) _ hw
          rw [← h2]; group
  have h3 := hconj (2 ^ k) v hv
  rw [hk'] at h3
  have h4 : (n * t) ^ 2 ^ k * v = v * (n * t) ^ 2 ^ k := by
    have := congrArg (fun z => z * (n * t) ^ 2 ^ k) h3
    simpa [mul_assoc] using this
  exact h4.symm

theorem le_zsMod152 {T Mc M V ZS Z X : Subgroup G} (hZZS : Z ≤ ZS) (hZSV : ZS ≤ V)
    (hsyl : ∀ P : Subgroup G, T ≤ P → IsSylowTwoOf T P)
    (hTM : T ≤ M) (hMV : M ≤ Subgroup.normalizer (V : Set G))
    (hTX : T ≤ X) (hXMc : X ≤ Mc) (hNT : Subgroup.normalizer (T : Set G) ≤ M)
    (hinf : M ⊓ Mc ≤ (M ⊓ Subgroup.centralizer (V : Set G)) ⊔ T)
    (hTC : T ≤ zsMod152 ZS Z hZZS)
    (hH : ∀ P : Subgroup G, IsHStar T M P → oTwoUpper P ≤ Subgroup.centralizer (ZS : Set G))
    (hPar : ∀ P ∈ uFamHat X T, ¬ P ≤ M → IsHStar T M P) :
    X ≤ zsMod152 ZS Z hZZS := by
  have hT2 : IsPGroup 2 T := (hsyl T le_rfl).2.1
  have hP : ∀ P : Subgroup G, T ≤ P → P ≤ Mc → (P ≤ M ∨ IsHStar T M P) →
      P ≤ zsMod152 ZS Z hZZS := by
    intro P hTP hPMc hcase
    refine le_zsMod_of_O2_le_centralizer152 hZZS hTC (hsyl P hTP) ?_
    rcases hcase with hPM | hPH
    · exact (oTwoUpper_le_centralizer_of_le152 hT2 hTM hMV hPM hPMc hinf).trans
        (Subgroup.centralizer_le hZSV)
    · exact hH P hPH
  have hgen := le_uHat_sup_normalizer hTX
  refine hgen.trans (sup_le ?_ ?_)
  · refine iSup₂_le fun P hPmem => ?_
    have hPX : P ≤ X := hPmem.1.1
    have hTP : T ≤ P := hPmem.1.2.1.le
    by_cases hPM : P ≤ M
    · exact hP P hTP (hPX.trans hXMc) (Or.inl hPM)
    · exact hP P hTP (hPX.trans hXMc) (Or.inr (hPar P hPmem hPM))
  · exact hP _ (le_inf hTX Subgroup.le_normalizer) (inf_le_left.trans hXMc)
      (Or.inl (inf_le_right.trans hNT))

end CFSG.Quasithin
