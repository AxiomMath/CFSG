module

public import CFSG.Quasithin.H13.GoldschmidtI51Corr
public import CFSG.Quasithin.H13.GoldschmidtI51Elem
public import CFSG.Quasithin.H13.Sp62DSystem

public section

namespace CFSG.Quasithin.H13.I51

open CFSG.Open

variable {G : Type} [Group G] {K : Type*} [Group K]

theorem mem_ker_iff_mem_pCoreOf {X : Subgroup G} (φ : ↥X →* K)
    (hker : φ.ker = CFSG.Open.pCore 2 ↥X) {n : G} (hn : n ∈ X) :
    (⟨n, hn⟩ : ↥X) ∈ φ.ker ↔ n ∈ pCoreOf 2 X := by
  rw [hker, mem_pCoreOf_iff]
  constructor
  · intro h; exact ⟨⟨n, hn⟩, h, rfl⟩
  · rintro ⟨y, hy, hyn⟩
    have : y = ⟨n, hn⟩ := Subtype.ext hyn
    rwa [← this]

theorem bridge_core {X P : Subgroup G} (φ : ↥X →* K) (hφ : Function.Surjective φ)
    (hker : φ.ker = CFSG.Open.pCore 2 ↥X) {A : Subgroup K}
    (hPA : (P.subgroupOf X).map φ = A)
    (hcore : ∀ n : K, (∀ g : K, g⁻¹ * n * g ∈ A) → n = 1) :
    ∀ n ∈ X, (∀ g ∈ X, g⁻¹ * n * g ∈ P) → n ∈ pCoreOf 2 X := by
  intro n hn h
  rw [← mem_ker_iff_mem_pCoreOf φ hker hn]
  exact transport_core φ hφ hPA hcore ⟨n, hn⟩ (fun g => by
    rw [Subgroup.mem_subgroupOf]; exact h g g.2)

theorem bridge_prod3 {X P R P' : Subgroup G} (φ : ↥X →* K)
    (hker : φ.ker = CFSG.Open.pCore 2 ↥X) {A B A' : Subgroup K}
    (hPA : (P.subgroupOf X).map φ = A) (hRB : (R.subgroupOf X).map φ = B)
    (hP'A' : (P'.subgroupOf X).map φ = A') (hkerP' : pCoreOf 2 X ≤ P')
    (h : ∀ g : K, ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ A', g = a * b * c) :
    ∀ g ∈ X, ∃ a ∈ P, ∃ b ∈ R, ∃ c ∈ P', g = a * b * c := by
  intro g hg
  have hk : φ.ker ≤ P'.subgroupOf X := by
    intro x hx
    rw [hker] at hx
    have : (x : G) ∈ pCoreOf 2 X := mem_pCoreOf_iff.2 ⟨x, hx, rfl⟩
    exact hkerP' this
  obtain ⟨a, ha, b, hb, c, hc, hgabc⟩ := transport_prod3 φ hPA hRB hP'A' hk h ⟨g, hg⟩
  refine ⟨a, ha, b, hb, c, hc, ?_⟩
  have := congrArg Subtype.val hgabc
  simpa using this

theorem bridge_prod2 {X P R : Subgroup G} (φ : ↥X →* K)
    (hker : φ.ker = CFSG.Open.pCore 2 ↥X) {A B : Subgroup K}
    (hPA : (P.subgroupOf X).map φ = A) (hRB : (R.subgroupOf X).map φ = B)
    (hkerR : pCoreOf 2 X ≤ R) (h : ∀ g : K, ∃ a ∈ A, ∃ b ∈ B, g = a * b) :
    ∀ g ∈ X, ∃ a ∈ P, ∃ b ∈ R, g = a * b := by
  intro g hg
  have hk : φ.ker ≤ R.subgroupOf X := by
    intro x hx
    rw [hker] at hx
    have : (x : G) ∈ pCoreOf 2 X := mem_pCoreOf_iff.2 ⟨x, hx, rfl⟩
    exact hkerR this
  obtain ⟨a, ha, b, hb, hgab⟩ := transport_prod2 φ hPA hRB hk h ⟨g, hg⟩
  refine ⟨a, ha, b, hb, ?_⟩
  have := congrArg Subtype.val hgab
  simpa using this

theorem bridge_index {X P : Subgroup G} (φ : ↥X →* K) (hφ : Function.Surjective φ)
    (hker : φ.ker = CFSG.Open.pCore 2 ↥X) {A : Subgroup K}
    (hPA : (P.subgroupOf X).map φ = A) (hkerP : pCoreOf 2 X ≤ P) :
    P.relIndex X = A.index := by
  have hk : φ.ker ≤ P.subgroupOf X := by
    intro x hx
    rw [hker] at hx
    have : (x : G) ∈ pCoreOf 2 X := mem_pCoreOf_iff.2 ⟨x, hx, rfl⟩
    exact hkerP this
  exact transport_index φ hφ hPA hk

theorem mem_ker_iff_mem_pCoreOf' {X : Subgroup G} (φ : ↥X →* K)
    (hker : φ.ker = CFSG.Open.pCore 2 ↥X) (x : ↥X) : x ∈ φ.ker ↔ (x : G) ∈ pCoreOf 2 X := by
  have := mem_ker_iff_mem_pCoreOf φ hker x.2
  simpa using this

theorem bridge_noNormal {X P M : Subgroup G} (φ : ↥X →* K)
    (hker : φ.ker = CFSG.Open.pCore 2 ↥X) {A : Subgroup K}
    (hPA : (P.subgroupOf X).map φ = A) (hcenter : ∀ n ∈ A, (∀ a ∈ A, a * n = n * a) → n = 1)
    (hMP : M ≤ P) (hnorm : ∀ a ∈ P, ∀ m ∈ M, a * m * a⁻¹ ∈ M)
    (hord : ∀ m₁ ∈ M, ∀ m₂ ∈ M, m₁ ∈ pCoreOf 2 X ∨ m₂ ∈ pCoreOf 2 X ∨
      m₁ * m₂⁻¹ ∈ pCoreOf 2 X) (hMX : M ≤ X) : M ≤ pCoreOf 2 X := by
  have := transport_noNormal φ (P := P.subgroupOf X) (M := M.subgroupOf X) hPA hcenter
    (fun x hx => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hMP hx)
    (fun a ha m hm => by
      rw [Subgroup.mem_subgroupOf] at ha hm ⊢
      exact hnorm a ha m hm)
    (fun m₁ hm₁ m₂ hm₂ => by
      rw [Subgroup.mem_subgroupOf] at hm₁ hm₂
      rw [mem_ker_iff_mem_pCoreOf' φ hker, mem_ker_iff_mem_pCoreOf' φ hker,
        mem_ker_iff_mem_pCoreOf' φ hker]
      simpa using hord m₁ hm₁ m₂ hm₂)
  intro m hm
  have := this (show (⟨m, hMX hm⟩ : ↥X) ∈ M.subgroupOf X from hm)
  exact (mem_ker_iff_mem_pCoreOf φ hker (hMX hm)).1 this

theorem relIndex_pCoreOf_eq_card {X T : Subgroup G} (hTX : T ≤ X) (φ : ↥X →* K)
    (hker : φ.ker = CFSG.Open.pCore 2 ↥X) {P₀ : Subgroup K}
    (hT : (T.subgroupOf X).map φ = P₀) : (pCoreOf 2 X).relIndex T = Nat.card P₀ := by
  have h1 := Subgroup.relIndex_ker (K := T.subgroupOf X) φ
  rw [hT, hker] at h1
  have h2 := Subgroup.relIndex_map_map_of_injective (f := X.subtype)
    (CFSG.Open.pCore 2 ↥X) (T.subgroupOf X) X.subtype_injective
  rw [CFSG.Quasithin.H13.A6.map_subtype_subgroupOf hTX] at h2
  exact h2.trans h1

end CFSG.Quasithin.H13.I51
