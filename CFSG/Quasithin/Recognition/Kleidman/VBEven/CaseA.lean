module

public import CFSG.Quasithin.Recognition.SzVBA5Loc
public import CFSG.Quasithin.Recognition.SzVBEvenCtx

public section

namespace CFSG.Quasithin.Kleidman.VBEven

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SzVB

section Aux

variable {G : Type*} [Group G]

theorem eq_one_or_eq_of_mem_zpowers {z x : G} (hzz : z * z = 1) (hx : x ∈ Subgroup.zpowers z) :
    x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hk : 2 * (k / 2) + k % 2 = k := by omega
  have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hzz
  rw [← hk, zpow_add, zpow_mul, h2, one_zpow, one_mul]
  rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [h] <;> simp

theorem exists_conjHom {W P : Subgroup G} (hP : P ≤ Subgroup.normalizer (W : Set G)) {g : G}
    (hg : g ∈ P) : ∃ ψ : ↥W →* ↥W, ∀ x : ↥W, ((ψ x : ↥W) : G) = g * x * g⁻¹ := by
  have hmem : ∀ x : ↥W, g * (x : G) * g⁻¹ ∈ W := fun x =>
    (Subgroup.mem_normalizer_iff.mp (hP hg) _).mp x.2
  refine ⟨{ toFun := fun x => ⟨g * x * g⁻¹, hmem x⟩, map_one' := ?_, map_mul' := ?_ },
    fun x => rfl⟩
  · apply Subtype.ext
    simp
  · intro x y
    apply Subtype.ext
    simp [mul_assoc]

end Aux

section Perm

variable {G : Type*} [Group G] {P T V : Subgroup G} {z : G}

theorem T_smul_base (F : A5Facts P T V z) {x : ↥P} (hx : (x : G) ∈ T) :
    x • ConjSet.base P V = ConjSet.base P V :=
  Subtype.ext (OddAux.conjSub_eq_of_mem_normalizer' (F.l24.S_le_normalizer hx))

theorem T_smul_smul (F : A5Facts P T V z) {x : ↥P} (hx : (x : G) ∈ T) (U : ConjSet P V) :
    x • x • U = U := by
  have h := F.T_sq x hx
  rw [kerAct, MonoidHom.mem_ker] at h
  have h' : (x * x) • U = U := by
    have := congrArg (fun f : Equiv.Perm (ConjSet P V) => f U) h
    simpa using this
  rwa [mul_smul] at h'

theorem T_smul_comm (F : A5Facts P T V z) {x y : ↥P} (hx : (x : G) ∈ T) (hy : (y : G) ∈ T)
    (U : ConjSet P V) : x • y • U = y • x • U := by
  have hxy : ((x * y : ↥P) : G) ∈ T := T.mul_mem hx hy
  have h1 := T_smul_smul F hxy U
  rw [mul_smul, mul_smul] at h1
  have h2 : y • x • y • U = x • U := by
    have h4 : x • x • y • x • y • U = x • U := congrArg (x • ·) h1
    rwa [T_smul_smul F hx] at h4
  have h3 : y • y • x • y • U = y • x • U := congrArg (y • ·) h2
  rwa [T_smul_smul F hy] at h3

theorem T_fixed_all (F : A5Facts P T V z) {x : ↥P} (hx : (x : G) ∈ T) {U : ConjSet P V}
    (hU : U ≠ ConjSet.base P V) (hxU : x • U = U) (U' : ConjSet P V) : x • U' = U' := by
  by_cases h : U' = ConjSet.base P V
  · rw [h]
    exact T_smul_base F hx
  · obtain ⟨s, hs, hsU⟩ := F.l24.S_transitive U U' hU h
    have hsT : (s : G) ∈ T := hs
    rw [← hsU, T_smul_comm F hx hsT, hxU]

end Perm

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T V : Subgroup G} {z : G}

theorem caseA_witness (hC : GeoCtx G₀ G₁ G₂ T V z) (F : A5Facts G₂ T V z)
    (hTQ : T ≤ pCoreOf 2 G₁ ⊔ pCoreOf 2 G₂) (hA : ¬ A5FixedW G₂ V z) {w : G}
    (hw : w ∈ pCoreOf 2 G₁) (hw2 : w * w = 1) (hwQ : w ∉ pCoreOf 2 G₂) :
    ∃ a ∈ conjClosure V G₂, a ∈ secCentr (pCoreOf 2 G₁) V ∧ w * a * w⁻¹ * a⁻¹ ≠ 1 := by
  classical
  have _ := hTQ
  have _ := hw2
  have hO1T : pCoreOf 2 G₁ ≤ T := F7.isSylowTwoOf_pCoreOf_le hC.hyp.sylow₁
  have hTG : T ≤ G₂ := F.l24.S_le
  obtain ⟨t, htd, htU⟩ := exists_tDataG_mem F.klein
  have hwT : w ∈ T := hO1T hw
  let wP : ↥G₂ := ⟨w, hTG hwT⟩
  have hwP : (wP : G) ∈ T := hwT
  have : Fintype (ConjSet G₂ V) := Fintype.ofFinite _
  have hcard : Fintype.card (ConjSet G₂ V) = 5 := by
    rw [Fintype.card_eq_nat_card]
    exact F.l24.card_five
  obtain ⟨U₁, hU₁⟩ : ∃ U : ConjSet G₂ V, wP • U ≠ U := by
    by_contra hcon
    push Not at hcon
    apply hwQ
    refine F.ker_le wP ?_
    rw [kerAct, MonoidHom.mem_ker]
    ext U
    simpa using hcon U
  have hU₁0 : U₁ ≠ ConjSet.base G₂ V := fun h => hU₁ (by rw [h]; exact T_smul_base F hwP)
  obtain ⟨U₂, hU₂⟩ : ∃ U₂, U₂ = wP • U₁ := ⟨_, rfl⟩
  have hU₂1 : U₂ ≠ U₁ := fun h => hU₁ (hU₂ ▸ h)
  have hU₂0 : U₂ ≠ ConjSet.base G₂ V := by
    intro h
    apply hU₁0
    have h' : wP • U₁ = wP • ConjSet.base G₂ V := by
      rw [← hU₂, h, T_smul_base F hwP]
    exact MulAction.injective wP h'
  obtain ⟨U₃, hU₃⟩ : ∃ U : ConjSet G₂ V, U ∉ ({ConjSet.base G₂ V, U₁, U₂} : Finset _) := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset (ConjSet G₂ V)) ⊆ {ConjSet.base G₂ V, U₁, U₂} :=
      fun U _ => hcon U
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, hcard] at this
    have h3 := Finset.card_le_three (a := ConjSet.base G₂ V) (b := U₁) (c := U₂)
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hU₃
  obtain ⟨hU₃0, hU₃1, hU₃2⟩ := hU₃
  obtain ⟨U₄, hU₄⟩ : ∃ U₄, U₄ = wP • U₃ := ⟨_, rfl⟩
  have hU₄3 : U₄ ≠ U₃ := by
    intro h
    exact hU₁ (T_fixed_all F hwP hU₃0 (hU₄ ▸ h) U₁)
  have hU₄0 : U₄ ≠ ConjSet.base G₂ V := by
    intro h
    apply hU₃0
    have h' : wP • U₃ = wP • ConjSet.base G₂ V := by
      rw [← hU₄, h, T_smul_base F hwP]
    exact MulAction.injective wP h'
  have hU₄2 : U₄ ≠ U₂ := by
    intro h
    apply hU₃1
    have h' : wP • U₃ = wP • U₁ := by rw [← hU₄, ← hU₂, h]
    exact MulAction.injective wP h'
  have hU₄1 : U₄ ≠ U₁ := by
    intro h
    apply hU₃2
    have h' : wP • wP • U₃ = wP • U₁ := by rw [← hU₄, h]
    rw [T_smul_smul F hwP] at h'
    exact h'.trans hU₂.symm
  have hn1 : U₃ ∉ ({U₄} : Finset (ConjSet G₂ V)) := by simp [Ne.symm hU₄3]
  have hn2 : U₂ ∉ ({U₃, U₄} : Finset (ConjSet G₂ V)) := by
    simp [Ne.symm hU₃2, Ne.symm hU₄2]
  have hn3 : U₁ ∉ ({U₂, U₃, U₄} : Finset (ConjSet G₂ V)) := by
    simp [Ne.symm hU₂1, Ne.symm hU₃1, Ne.symm hU₄1]
  have hn4 : ConjSet.base G₂ V ∉ ({U₁, U₂, U₃, U₄} : Finset (ConjSet G₂ V)) := by
    simp [Ne.symm hU₁0, Ne.symm hU₂0, Ne.symm hU₃0, Ne.symm hU₄0]
  have hs : ({ConjSet.base G₂ V, U₁, U₂, U₃, U₄} : Finset (ConjSet G₂ V)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hcard, Finset.card_insert_of_notMem hn4, Finset.card_insert_of_notMem hn3,
      Finset.card_insert_of_notMem hn2, Finset.card_insert_of_notMem hn1, Finset.card_singleton]
  have hall : ∀ U : ConjSet G₂ V, U = ConjSet.base G₂ V ∨ U = U₁ ∨ U = U₂ ∨ U = U₃ ∨ U = U₄ := by
    intro U
    have : U ∈ ({ConjSet.base G₂ V, U₁, U₂, U₃, U₄} : Finset (ConjSet G₂ V)) := by
      rw [hs]; exact Finset.mem_univ U
    simpa using this
  have hcases : ∀ q : ↥G₂, (q : G) ∈ T →
      ((q • U₁ = U₁ ∧ q • U₃ = U₃) ∨ (q • U₁ = U₃ ∧ q • U₃ = U₁)) ∨
      ((q • U₁ = U₂ ∧ q • U₃ = U₄) ∨ (q • U₁ = U₄ ∧ q • U₃ = U₂)) := by
    intro q hq
    have hqU₀ : ∀ U : ConjSet G₂ V, q • U = ConjSet.base G₂ V → U = ConjSet.base G₂ V := by
      intro U h
      have h' : q • U = q • ConjSet.base G₂ V := by rw [h, T_smul_base F hq]
      exact MulAction.injective q h'
    rcases hall (q • U₁) with h | h | h | h | h
    · exact absurd (hqU₀ U₁ h) hU₁0
    · exact Or.inl (Or.inl ⟨h, T_fixed_all F hq hU₁0 h U₃⟩)
    · right
      left
      refine ⟨h, ?_⟩
      have hqw : ((q * wP : ↥G₂) : G) ∈ T := T.mul_mem hq hwP
      have hfix : (q * wP) • U₁ = U₁ := by
        rw [mul_smul, ← hU₂, ← h]
        exact T_smul_smul F hq U₁
      have hall' := T_fixed_all F hqw hU₁0 hfix U₃
      rw [mul_smul, ← hU₄] at hall'
      have h5 : q • q • U₄ = q • U₃ := congrArg (q • ·) hall'
      rw [T_smul_smul F hq] at h5
      exact h5.symm
    · left
      right
      refine ⟨h, ?_⟩
      rw [← h, T_smul_smul F hq]
    · right
      right
      refine ⟨h, ?_⟩
      have h1 : q • q • U₁ = q • U₄ := congrArg (q • ·) h
      rw [T_smul_smul F hq, hU₄, T_smul_comm F hq hwP] at h1
      have h2 : wP • U₁ = wP • wP • q • U₃ := congrArg (wP • ·) h1
      rw [T_smul_smul F hwP] at h2
      rw [hU₂, h2]
  have hzz : z * z = 1 := F.klein.z_mul_self
  have hVz : Subgroup.zpowers z ≤ V := Subgroup.zpowers_le.mpr F.klein.z_mem
  set W := conjClosure V G₂ with hW
  let : CommGroup ↥W := { (inferInstance : Group ↥W) with
    mul_comm := fun a b => Subtype.ext (F7.isElemAbelian_comm F.abel a.2 b.2) }
  let Zs : Subgroup ↥W := (Subgroup.zpowers z).comap W.subtype
  have hZs : ∀ x : ↥W, x ∈ Zs ↔ (x : G) ∈ Subgroup.zpowers z := fun x => Iff.rfl
  let τ : ConjSet G₂ V → ↥W := fun U => ⟨t U, htd.t_mem U⟩
  have hτ2 : ∀ U, τ U * τ U = 1 := fun U => Subtype.ext (htd.t_sq U)
  have hact : ∀ (q : ↥G₂) (ψ : ↥W →* ↥W), (∀ x : ↥W, ((ψ x : ↥W) : G) = q * x * q⁻¹) →
      ∀ U, ∃ ε ∈ Zs, ψ (τ U) = τ (q • U) * ε := by
    intro q ψ hψ U
    rcases htd.act q U with h | h
    · exact ⟨1, Zs.one_mem, Subtype.ext (by rw [hψ]; simpa using h)⟩
    · refine ⟨⟨z, htd.z_mem⟩, (hZs _).mpr (Subgroup.mem_zpowers z), Subtype.ext ?_⟩
      rw [hψ]
      simpa using h
  have hN : ∏ U, τ U ∈ Zs := by
    by_contra hnot
    apply hA
    unfold A5FixedW
    refine ⟨((∏ U, τ U : ↥W) : G), (∏ U, τ U : ↥W).2, hnot, fun g hg => ?_⟩
    obtain ⟨ψ, hψ⟩ := exists_conjHom (le_normalizer_conjClosure V G₂) hg
    choose ε hεZ hε using hact ⟨g, hg⟩ ψ hψ
    have h1 : ψ (∏ U, τ U) = (∏ U, τ U) * ∏ U, ε U := by
      rw [map_prod]
      simp_rw [hε]
      rw [Finset.prod_mul_distrib]
      congr 1
      exact Fintype.prod_equiv (MulAction.toPerm (⟨g, hg⟩ : ↥G₂)) _ _ (fun U => rfl)
    have h2 : ∏ U, ε U ∈ Zs := Subgroup.prod_mem _ (fun U _ => hεZ U)
    have h3 : ψ (∏ U, τ U) * (∏ U, τ U)⁻¹ = ∏ U, ε U := by
      rw [h1, mul_comm (∏ U, τ U), mul_inv_cancel_right]
    have h4 := congrArg (fun x : ↥W => (x : G)) h3
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hψ] at h4
    rw [h4]
    exact (hZs _).mp h2
  have hsum : ∏ U, τ U = τ (ConjSet.base G₂ V) * τ U₁ * τ U₂ * τ U₃ * τ U₄ := by
    rw [← hs, Finset.prod_insert hn4, Finset.prod_insert hn3, Finset.prod_insert hn2,
      Finset.prod_insert hn1, Finset.prod_singleton]
    ac_rfl
  rw [hsum] at hN
  set Ω0 : ConjSet G₂ V := ConjSet.base G₂ V with hΩ0
  have hainv : (τ U₁ * τ U₃)⁻¹ = τ U₁ * τ U₃ := inv_eq_of_mul_eq_one_right (by
    calc τ U₁ * τ U₃ * (τ U₁ * τ U₃) = (τ U₁ * τ U₁) * (τ U₃ * τ U₃) := by ac_rfl
      _ = 1 := by rw [hτ2, hτ2, one_mul])
  have hcomp1 : ∀ (q : ↥G₂) (ψ : ↥W →* ↥W), (∀ x : ↥W, ((ψ x : ↥W) : G) = q * x * q⁻¹) →
      ((q • U₁ = U₁ ∧ q • U₃ = U₃) ∨ (q • U₁ = U₃ ∧ q • U₃ = U₁)) →
      ψ (τ U₁ * τ U₃) * (τ U₁ * τ U₃)⁻¹ ∈ Zs := by
    intro q ψ hψ hcase
    obtain ⟨ε₁, hε₁, e₁⟩ := hact q ψ hψ U₁
    obtain ⟨ε₃, hε₃, e₃⟩ := hact q ψ hψ U₃
    rw [map_mul, e₁, e₃, hainv]
    rcases hcase with ⟨h1, h3⟩ | ⟨h1, h3⟩
    · rw [h1, h3]
      have : τ U₁ * ε₁ * (τ U₃ * ε₃) * (τ U₁ * τ U₃) =
          (τ U₁ * τ U₁) * (τ U₃ * τ U₃) * (ε₁ * ε₃) := by ac_rfl
      rw [this, hτ2, hτ2, one_mul, one_mul]
      exact Zs.mul_mem hε₁ hε₃
    · rw [h1, h3]
      have : τ U₃ * ε₁ * (τ U₁ * ε₃) * (τ U₁ * τ U₃) =
          (τ U₁ * τ U₁) * (τ U₃ * τ U₃) * (ε₁ * ε₃) := by ac_rfl
      rw [this, hτ2, hτ2, one_mul, one_mul]
      exact Zs.mul_mem hε₁ hε₃
  have hcomp2 : ∀ (q : ↥G₂) (ψ : ↥W →* ↥W), (∀ x : ↥W, ((ψ x : ↥W) : G) = q * x * q⁻¹) →
      ((q • U₁ = U₂ ∧ q • U₃ = U₄) ∨ (q • U₁ = U₄ ∧ q • U₃ = U₂)) →
      ∃ ε ∈ Zs, ψ (τ U₁ * τ U₃) * (τ U₁ * τ U₃)⁻¹ = τ Ω0 * ε := by
    intro q ψ hψ hcase
    obtain ⟨ε₁, hε₁, e₁⟩ := hact q ψ hψ U₁
    obtain ⟨ε₃, hε₃, e₃⟩ := hact q ψ hψ U₃
    rw [map_mul, e₁, e₃, hainv]
    refine ⟨ε₁ * ε₃ * (τ Ω0 * τ U₁ * τ U₂ * τ U₃ * τ U₄),
      Zs.mul_mem (Zs.mul_mem hε₁ hε₃) hN, ?_⟩
    have hrhs : τ Ω0 * (ε₁ * ε₃ * (τ Ω0 * τ U₁ * τ U₂ * τ U₃ * τ U₄)) =
        (τ Ω0 * τ Ω0) * ((ε₁ * ε₃) * (τ U₁ * τ U₂ * τ U₃ * τ U₄)) := by ac_rfl
    rw [hrhs, hτ2, one_mul]
    rcases hcase with ⟨h1, h3⟩ | ⟨h1, h3⟩
    · rw [h1, h3]
      ac_rfl
    · rw [h1, h3]
      ac_rfl
  have hVmem : ∀ x : ↥W, x ∈ Zs → (x : G) ∈ V := fun x hx => hVz ((hZs x).mp hx)
  have ht0 : t Ω0 ∈ V := (htU Ω0).1
  refine ⟨((τ U₁ * τ U₃ : ↥W) : G), (τ U₁ * τ U₃ : ↥W).2, ⟨?_, fun q hq => ?_⟩, ?_⟩
  · exact (Subgroup.centralizer_le_normalizer _)
      (Subgroup.mem_centralizer_iff.mpr fun h hh =>
        F7.isElemAbelian_comm F.abel (le_conjClosure V G₂ hh) (τ U₁ * τ U₃ : ↥W).2)
  · have hqT : q ∈ T := hO1T hq
    let qP : ↥G₂ := ⟨q, hTG hqT⟩
    obtain ⟨ψ, hψ⟩ := exists_conjHom (le_normalizer_conjClosure V G₂) qP.2
    have hu : q * ((τ U₁ * τ U₃ : ↥W) : G) * q⁻¹ * ((τ U₁ * τ U₃ : ↥W) : G)⁻¹ =
        ((ψ (τ U₁ * τ U₃) * (τ U₁ * τ U₃)⁻¹ : ↥W) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hψ]
      rfl
    rw [hu]
    rcases hcases qP hqT with hc | hc
    · exact hVmem _ (hcomp1 qP ψ hψ hc)
    · obtain ⟨ε, hε, e⟩ := hcomp2 qP ψ hψ hc
      rw [e, Subgroup.coe_mul]
      exact V.mul_mem ht0 (hVmem ε hε)
  · intro h1
    obtain ⟨ψ, hψ⟩ := exists_conjHom (le_normalizer_conjClosure V G₂) wP.2
    have hu : w * ((τ U₁ * τ U₃ : ↥W) : G) * w⁻¹ * ((τ U₁ * τ U₃ : ↥W) : G)⁻¹ =
        ((ψ (τ U₁ * τ U₃) * (τ U₁ * τ U₃)⁻¹ : ↥W) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hψ]
      rfl
    obtain ⟨ε, hε, e⟩ := hcomp2 wP ψ hψ (Or.inl ⟨hU₂.symm, hU₄.symm⟩)
    rw [hu, e] at h1
    have h2 : τ Ω0 * ε = 1 := Subtype.ext h1
    have h3 : τ Ω0 = ε⁻¹ := eq_inv_of_mul_eq_one_left h2
    have h4 : (t Ω0) ∈ Subgroup.zpowers z := (hZs (τ Ω0)).mp (h3 ▸ Zs.inv_mem hε)
    rcases eq_one_or_eq_of_mem_zpowers hzz h4 with h5 | h5
    · exact (htU Ω0).2.1 h5
    · exact (htU Ω0).2.2 h5

end CFSG.Quasithin.Kleidman.VBEven
