module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.AppendixH.H15.Vocab

public section

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Open

theorem mem_conjSubg_iff {X : Type*} [Group X] (g : X) (A : Subgroup X) (x : X) :
    x ∈ conjSubg g A ↔ g⁻¹ * x * g ∈ A := by
  rw [conjSubg, Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, hax⟩
    rw [← hax]
    change g⁻¹ * ((MulAut.conj g) a) * g ∈ A
    rw [MulAut.conj_apply]
    convert ha using 1
    group
  · intro h
    exact ⟨g⁻¹ * x * g, h, by
      change (MulAut.conj g) (g⁻¹ * x * g) = x
      rw [MulAut.conj_apply]
      group⟩

theorem conjSubg_mono {X : Type*} [Group X] (g : X) {A B : Subgroup X} (h : A ≤ B) :
    conjSubg g A ≤ conjSubg g B :=
  Subgroup.map_mono h

theorem conjSubg_inv_conjSubg {X : Type*} [Group X] (g : X) (A : Subgroup X) :
    conjSubg g⁻¹ (conjSubg g A) = A := by
  ext x
  rw [mem_conjSubg_iff, mem_conjSubg_iff]
  simp only [inv_inv]
  constructor
  · intro h
    convert h using 1
    group
  · intro h
    convert h using 1
    group

theorem pCoreOf_conjSubg (p : ℕ) {X : Type*} [Group X] (g : X) (H : Subgroup X) :
    pCoreOf p (conjSubg g H) = conjSubg g (pCoreOf p H) := by
  let φ : ↥H ≃* ↥(conjSubg g H) := MulEquiv.subgroupMap (MulAut.conj g) H
  calc pCoreOf p (conjSubg g H)
      = (pCore p ↥(conjSubg g H)).map (conjSubg g H).subtype := rfl
    _ = ((pCore p ↥H).map φ.toMonoidHom).map (conjSubg g H).subtype := by
          rw [← CFSG.pCore_map_iso p φ]
    _ = (pCore p ↥H).map ((conjSubg g H).subtype.comp φ.toMonoidHom) := by
          rw [Subgroup.map_map]
    _ = (pCore p ↥H).map ((MulAut.conj g).toMonoidHom.comp H.subtype) := rfl
    _ = ((pCore p ↥H).map H.subtype).map (MulAut.conj g).toMonoidHom := by
          rw [Subgroup.map_map]
    _ = conjSubg g (pCoreOf p H) := rfl

theorem perfectCore_conjSubg {X : Type*} [Group X] [Finite X] (g : X) (H : Subgroup X) :
    perfectCore (conjSubg g H) = conjSubg g (perfectCore H) := by
  rw [conjSubg, conjSubg, map_perfectCore]

theorem pCoreOf_le_subgroup (p : ℕ) {X : Type*} [Group X] (H : Subgroup X) : pCoreOf p H ≤ H :=
  Subgroup.map_subtype_le (pCore p ↥H)

theorem perfectCore_le_subgroup {X : Type*} [Group X] (H : Subgroup X) : perfectCore H ≤ H := by
  simpa [derivedSeriesOf_zero] using perfectCore_le_derivedSeriesOf H 0

theorem isO23_conjSubg {G N : Subgroup S24} (τ : S24) (h : IsO23 G N) :
    IsO23 (conjSubg τ G) (conjSubg τ N) := by
  unfold IsO23 at h ⊢
  refine ⟨conjSubg_mono τ h.1, ?_, ?_, ?_, ?_⟩
  · intro g hg n hn
    rw [mem_conjSubg_iff] at hg hn ⊢
    have hh := h.2.1 (τ⁻¹ * g * τ) hg (τ⁻¹ * n * τ) hn
    convert hh using 1
    group
  · rw [pCoreOf_conjSubg]
    exact conjSubg_mono τ h.2.2.1
  · intro n hn
    rw [mem_conjSubg_iff] at hn
    obtain ⟨k, hk⟩ := h.2.2.2.1 (τ⁻¹ * n * τ) hn
    refine ⟨k, ?_⟩
    rw [pCoreOf_conjSubg, mem_conjSubg_iff]
    have hpow : (τ⁻¹ * n * τ) ^ (3 ^ k) = τ⁻¹ * n ^ (3 ^ k) * τ := by
      rw [show τ⁻¹ * n * τ = MulAut.conj τ⁻¹ n by rw [MulAut.conj_apply, inv_inv],
        ← map_pow, MulAut.conj_apply, inv_inv]
    rw [← hpow]
    exact hk
  · intro N' hN'G hN'norm hN'core hN'pow
    let N'' : Subgroup S24 := conjSubg τ⁻¹ N'
    have hN''G : N'' ≤ G := by
      dsimp only [N'']
      calc conjSubg τ⁻¹ N' ≤ conjSubg τ⁻¹ (conjSubg τ G) := conjSubg_mono τ⁻¹ hN'G
        _ = G := conjSubg_inv_conjSubg τ G
    have hN''norm : ∀ g ∈ G, ∀ n ∈ N'', g * n * g⁻¹ ∈ N'' := by
      intro g hg n hn
      dsimp only [N''] at hn ⊢
      rw [mem_conjSubg_iff] at hn ⊢
      simp only [inv_inv] at hn ⊢
      have hg' : τ * g * τ⁻¹ ∈ conjSubg τ G := by
        rw [mem_conjSubg_iff]
        convert hg using 1
        group
      have hh := hN'norm (τ * g * τ⁻¹) hg' (τ * n * τ⁻¹) hn
      convert hh using 1
      group
    have hN''core : pCoreOf 2 G ≤ N'' := by
      dsimp only [N'']
      have hle : conjSubg τ (pCoreOf 2 G) ≤ N' := by
        rwa [← pCoreOf_conjSubg]
      calc pCoreOf 2 G = conjSubg τ⁻¹ (conjSubg τ (pCoreOf 2 G)) :=
            (conjSubg_inv_conjSubg τ (pCoreOf 2 G)).symm
        _ ≤ conjSubg τ⁻¹ N' := conjSubg_mono τ⁻¹ hle
    have hN''pow : ∀ n ∈ N'', ∃ k, n ^ (3 ^ k) ∈ pCoreOf 2 G := by
      intro n hn
      dsimp only [N''] at hn
      rw [mem_conjSubg_iff] at hn
      simp only [inv_inv] at hn
      obtain ⟨k, hk⟩ := hN'pow (τ * n * τ⁻¹) hn
      refine ⟨k, ?_⟩
      rw [pCoreOf_conjSubg, mem_conjSubg_iff] at hk
      have hpow : (τ * n * τ⁻¹) ^ (3 ^ k) = τ * n ^ (3 ^ k) * τ⁻¹ := by
        rw [show τ * n * τ⁻¹ = MulAut.conj τ n by rw [MulAut.conj_apply],
          ← map_pow, MulAut.conj_apply]
      rw [hpow] at hk
      convert hk using 1
      group
    have hN''le : N'' ≤ N := h.2.2.2.2 N'' hN''G hN''norm hN''core hN''pow
    have hconj : N' = conjSubg τ N'' := by
      dsimp only [N'']
      simpa using (conjSubg_inv_conjSubg τ⁻¹ N').symm
    calc N' = conjSubg τ N'' := hconj
      _ ≤ conjSubg τ N := conjSubg_mono τ hN''le

theorem MY_smul_of_mem {α : Type*} [MulAction S24 α] {Γ : Subgroup S24} {τ : S24} (hτ : τ ∈ Γ)
    (Y : α) : MY Γ (τ • Y) = conjSubg τ (MY Γ Y) := by
  have hΓ : conjSubg τ Γ = Γ := by
    ext x
    rw [mem_conjSubg_iff]
    constructor
    · intro hx
      have h2 : τ * (τ⁻¹ * x * τ) * τ⁻¹ ∈ Γ := Γ.mul_mem (Γ.mul_mem hτ hx) (Γ.inv_mem hτ)
      convert h2 using 1
      group
    · intro hx
      exact Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hτ) hx) hτ
  have hΓ' : Subgroup.map (MulAut.conj τ).toMonoidHom Γ = Γ := by
    simpa only [conjSubg] using hΓ
  unfold MY
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, conjSubg]
  rw [Subgroup.map_inf _ _ _ (MulAut.conj τ).injective, hΓ']

theorem KY_smul_of_mem {α : Type*} [MulAction S24 α] {Γ : Subgroup S24} {τ : S24} (hτ : τ ∈ Γ)
    (Y : α) : KY Γ (τ • Y) = conjSubg τ (KY Γ Y) := by
  unfold KY
  rw [MY_smul_of_mem hτ, pCoreOf_conjSubg]

theorem map_congrHom_rImg {V W : Type*} [CommGroup V] [CommGroup W] {Γ : Subgroup S24}
    (ρ : ↥Γ →* MulAut V) (ρ' : ↥Γ →* MulAut W) (e : V ≃* W) (τ : ↥Γ)
    (h : ∀ γ : ↥Γ, CFSG.Quasithin.H.congrHom e (ρ γ) = ρ' (τ⁻¹ * γ * τ)) {A : Subgroup S24}
    (hA : A ≤ Γ) :
    (rImg ρ A).map (CFSG.Quasithin.H.congrHom e) = rImg ρ' (conjSubg ((τ : S24)⁻¹) A) := by
  let c : ↥Γ →* ↥Γ :=
    { toFun := fun γ => ⟨(τ : S24)⁻¹ * (γ : S24) * (τ : S24),
        Γ.mul_mem (Γ.mul_mem (Γ.inv_mem τ.2) γ.2) τ.2⟩
      map_one' := by
        apply Subtype.ext
        change (τ : S24)⁻¹ * (1 : S24) * (τ : S24) = (1 : S24)
        group
      map_mul' := fun a b => by
        apply Subtype.ext
        change (τ : S24)⁻¹ * ((a : S24) * (b : S24)) * (τ : S24) =
          ((τ : S24)⁻¹ * (a : S24) * (τ : S24)) * ((τ : S24)⁻¹ * (b : S24) * (τ : S24))
        group }
  have hcomp : (CFSG.Quasithin.H.congrHom e).comp ρ = ρ'.comp c := by
    apply MonoidHom.ext
    intro γ
    exact h γ
  have hmap : (A.subgroupOf Γ).map c = (conjSubg ((τ : S24)⁻¹) A).subgroupOf Γ := by
    ext x
    rw [Subgroup.mem_map, Subgroup.mem_subgroupOf, mem_conjSubg_iff]
    simp only [inv_inv]
    constructor
    · rintro ⟨a, ha, rfl⟩
      have ha' : (a : S24) ∈ A := Subgroup.mem_subgroupOf.mp ha
      convert ha' using 1
      change (τ : S24) * ((τ : S24)⁻¹ * (a : S24) * (τ : S24)) * (τ : S24)⁻¹ = (a : S24)
      group
    · intro hx
      refine ⟨⟨(τ : S24) * (x : S24) * (τ : S24)⁻¹,
          Γ.mul_mem (Γ.mul_mem τ.2 x.2) (Γ.inv_mem τ.2)⟩, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mpr hx
      · apply Subtype.ext
        change (τ : S24)⁻¹ * ((τ : S24) * (x : S24) * (τ : S24)⁻¹) * (τ : S24) = (x : S24)
        group
  rw [rImg, rImg, Subgroup.map_map, hcomp, ← Subgroup.map_map, hmap]

theorem congrHom_twist {V W : Type*} [CommGroup V] [CommGroup W] {Γ : Subgroup S24}
    (ρ : ↥Γ →* MulAut V) (ρ' : ↥Γ →* MulAut W) (e : V ≃* W)
    (he : ∀ (γ : ↥Γ) (v : V), e (ρ γ v) = ρ' γ (e v)) (τ : ↥Γ) (γ : ↥Γ) :
    CFSG.Quasithin.H.congrHom ((ρ τ⁻¹ : MulAut V).trans e) (ρ γ) = ρ' (τ⁻¹ * γ * τ) := by
  apply MulEquiv.ext
  intro w
  rw [CFSG.Quasithin.H.congrHom_apply, MulEquiv.trans_apply, MulEquiv.symm_trans_apply]
  have hinner : (ρ τ⁻¹ : MulAut V) (ρ γ ((ρ τ⁻¹ : MulAut V).symm (e.symm w))) =
      ρ (τ⁻¹ * γ * τ) (e.symm w) := by
    rw [← MulAut.inv_def]
    rw [show (ρ τ⁻¹ : MulAut V)⁻¹ = ρ τ from by rw [← map_inv, inv_inv]]
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul]
  rw [hinner, he, MulEquiv.apply_symm_apply]

end CFSG.ASVolI.H16
