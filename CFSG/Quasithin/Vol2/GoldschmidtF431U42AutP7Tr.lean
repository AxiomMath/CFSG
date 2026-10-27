module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP6Syl

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431

section Generic

variable {G : Type} [Group G] {M₁ M₂ : Subgroup G} {P : Subgroup Ah} {M : Subgroup G}

@[expose] def cenHom0 (φ : ↥P ≃* ↥M) : ↥(P ⊓ Subgroup.centralizer ({fhatA} : Set Ah)) →* G :=
  M.subtype.comp (φ.toMonoidHom.comp (Subgroup.inclusion inf_le_left))

theorem cenHom0_mem (iso : AutIso M₁ M₂) (φ : ↥P ≃* ↥M)
    (hBP : Bh ≤ P) (hφ : ∀ b : Bh, ((φ (Subgroup.inclusion hBP b) : ↥M) : G) = iso.toG b)
    (p : ↥(P ⊓ Subgroup.centralizer ({fhatA} : Set Ah))) :
    cenHom0 φ p ∈ M ⊓ cenOf (iso.toG fhB) := by
  refine ⟨(φ ⟨p, p.2.1⟩).2, ?_⟩
  show _ ∈ Subgroup.centralizer ({iso.toG fhB} : Set G)
  rw [Subgroup.mem_centralizer_singleton_iff, ← hφ fhB]
  have h : (⟨p, p.2.1⟩ : ↥P) * Subgroup.inclusion hBP fhB =
      Subgroup.inclusion hBP fhB * ⟨p, p.2.1⟩ := by
    apply Subtype.ext
    have := Subgroup.mem_centralizer_singleton_iff.1 p.2.2
    simpa only [Subgroup.coe_mul, Subgroup.coe_inclusion, coe_fhB] using this
  have := congrArg (fun x : ↥P => ((φ x : ↥M) : G)) h
  simp only [map_mul, Subgroup.coe_mul] at this
  exact this

@[expose] def cenHom (iso : AutIso M₁ M₂) (φ : ↥P ≃* ↥M)
    (hBP : Bh ≤ P) (hφ : ∀ b : Bh, ((φ (Subgroup.inclusion hBP b) : ↥M) : G) = iso.toG b) :
    ↥(P ⊓ Subgroup.centralizer ({fhatA} : Set Ah)) →* ↥(M ⊓ cenOf (iso.toG fhB)) :=
  (cenHom0 φ).codRestrict _ (cenHom0_mem iso φ hBP hφ)

theorem cenHom_injective (iso : AutIso M₁ M₂) (φ : ↥P ≃* ↥M)
    (hBP : Bh ≤ P) (hφ : ∀ b : Bh, ((φ (Subgroup.inclusion hBP b) : ↥M) : G) = iso.toG b) :
    Function.Injective (cenHom iso φ hBP hφ) := by
  intro x y h
  have h1 : ((φ ⟨x, x.2.1⟩ : ↥M) : G) = ((φ ⟨y, y.2.1⟩ : ↥M) : G) :=
    congrArg (fun z : ↥(M ⊓ cenOf (iso.toG fhB)) => (z : G)) h
  have h2 := φ.injective (Subtype.ext h1)
  exact Subtype.ext (Subtype.mk.inj h2)

theorem cenHom_surjective (iso : AutIso M₁ M₂) (φ : ↥P ≃* ↥M)
    (hBP : Bh ≤ P) (hφ : ∀ b : Bh, ((φ (Subgroup.inclusion hBP b) : ↥M) : G) = iso.toG b) :
    Function.Surjective (cenHom iso φ hBP hφ) := by
  rintro ⟨g, hgM, hgC⟩
  set p : ↥P := φ.symm ⟨g, hgM⟩ with hp
  have hpg : ((φ p : ↥M) : G) = g := congrArg Subtype.val (φ.apply_symm_apply ⟨g, hgM⟩)
  have hgc := Subgroup.mem_centralizer_singleton_iff.1
    (show g ∈ Subgroup.centralizer ({iso.toG fhB} : Set G) from hgC)
  have hcomm : p * Subgroup.inclusion hBP fhB = Subgroup.inclusion hBP fhB * p := by
    apply φ.injective
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul, hpg, hφ fhB]
    exact hgc
  have hpD : (p : Ah) ∈ P ⊓ Subgroup.centralizer ({fhatA} : Set Ah) := by
    refine ⟨p.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have := congrArg (fun x : ↥P => (x : Ah)) hcomm
    simpa only [Subgroup.coe_mul, Subgroup.coe_inclusion, coe_fhB] using this
  refine ⟨⟨p, hpD⟩, Subtype.ext ?_⟩
  exact hpg

@[expose] noncomputable def cenEquiv (iso : AutIso M₁ M₂)
    (φ : ↥P ≃* ↥M) (hBP : Bh ≤ P)
    (hφ : ∀ b : Bh, ((φ (Subgroup.inclusion hBP b) : ↥M) : G) = iso.toG b) :
    ↥(P ⊓ Subgroup.centralizer ({fhatA} : Set Ah)) ≃* ↥(M ⊓ cenOf (iso.toG fhB)) :=
  MulEquiv.ofBijective (cenHom iso φ hBP hφ)
    ⟨cenHom_injective iso φ hBP hφ, cenHom_surjective iso φ hBP hφ⟩

theorem mem_pCoreOf_cen [Finite G] (iso : AutIso M₁ M₂)
    (φ : ↥P ≃* ↥M) (hBP : Bh ≤ P)
    (hφ : ∀ b : Bh, ((φ (Subgroup.inclusion hBP b) : ↥M) : G) = iso.toG b) [Finite Ah]
    {g : G} : g ∈ pCoreOf 2 (M ⊓ cenOf (iso.toG fhB)) ↔
      ∃ p : ↥P, (p : Ah) ∈ pCoreOf 2 (P ⊓ Subgroup.centralizer ({fhatA} : Set Ah)) ∧
        ((φ p : ↥M) : G) = g := by
  have hM : (CFSG.Open.pCore 2 ↥(P ⊓ Subgroup.centralizer ({fhatA} : Set Ah))).map
      (cenEquiv iso φ hBP hφ).toMonoidHom =
      CFSG.Open.pCore 2 ↥(M ⊓ cenOf (iso.toG fhB)) :=
    CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 (cenEquiv iso φ hBP hφ)
  constructor
  · intro hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hg
    rw [← hM] at hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    refine ⟨⟨y, y.2.1⟩, ?_, rfl⟩
    exact Subgroup.mem_map_of_mem _ hy
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨y, hy, hyp⟩ := Subgroup.mem_map.1 hp
    have hpe : (p : Ah) = (y : Ah) := hyp.symm
    refine Subgroup.mem_map.2 ⟨cenEquiv iso φ hBP hφ y, ?_, ?_⟩
    · rw [← hM]
      exact Subgroup.mem_map_of_mem _ hy
    · show ((φ ⟨y, y.2.1⟩ : ↥M) : G) = _
      have : (⟨y, y.2.1⟩ : ↥P) = p := Subtype.ext hpe.symm
      rw [this]

theorem pCoreOf_cen_eq_imgG [Finite G] [Finite Ah]
    (iso : AutIso M₁ M₂) (φ : ↥P ≃* ↥M) (hBP : Bh ≤ P)
    (hφ : ∀ b : Bh, ((φ (Subgroup.inclusion hBP b) : ↥M) : G) = iso.toG b)
    (hA : pCoreOf 2 (P ⊓ Subgroup.centralizer ({fhatA} : Set Ah)) ≤ Bh) :
    pCoreOf 2 (M ⊓ cenOf (iso.toG fhB)) =
      iso.imgG (pCoreOf 2 (P ⊓ Subgroup.centralizer ({fhatA} : Set Ah))) := by
  ext g
  rw [mem_pCoreOf_cen iso φ hBP hφ]
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine iso.mem_imgG.2 ⟨⟨p, hA hp⟩, hp, ?_⟩
    rw [← hφ]
    rfl
  · intro hg
    obtain ⟨b, hb, rfl⟩ := iso.mem_imgG.1 hg
    exact ⟨Subgroup.inclusion hBP b, hb, hφ b⟩

end Generic

end CFSG.Quasithin.H13.F431.U42Aut
