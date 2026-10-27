module

public import CFSG.Quasithin.Background.S1567Z4

public section

namespace CFSG.Quasithin.S153N

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

namespace BridgeC

section Preimage

variable {G : Type} [Group G] {Γ : Type*} [Group Γ]

@[expose] def preimagePCore (C : Subgroup G) (φ : ↥C →* Γ) : Subgroup G :=
  ((pCoreOf 2 φ.range).comap φ).map C.subtype

theorem mem_preimagePCore {C : Subgroup G} {φ : ↥C →* Γ} {x : G} :
    x ∈ preimagePCore C φ ↔ ∃ h : x ∈ C, φ ⟨x, h⟩ ∈ pCoreOf 2 φ.range := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c.2, hc⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

theorem preimagePCore_le {C : Subgroup G} {φ : ↥C →* Γ} : preimagePCore C φ ≤ C := by
  rintro _ ⟨c, -, rfl⟩
  exact c.2

theorem conj_mem_preimagePCore_of_mem {C : Subgroup G} (φ : ↥C →* Γ) {u d : G} (hu : u ∈ C)
    (hd : d ∈ preimagePCore C φ) : u * d * u⁻¹ ∈ preimagePCore C φ := by
  obtain ⟨hdC, hdP⟩ := mem_preimagePCore.mp hd
  have hmem : u * d * u⁻¹ ∈ C := C.mul_mem (C.mul_mem hu hdC) (C.inv_mem hu)
  refine mem_preimagePCore.mpr ⟨hmem, ?_⟩
  have hn := le_normalizer_pCoreOf 2 φ.range (⟨φ ⟨u, hu⟩, ⟨⟨u, hu⟩, rfl⟩⟩ : ↥φ.range).2
  have h1 := (Subgroup.mem_normalizer_iff.mp hn (φ ⟨d, hdC⟩)).mp hdP
  have e : φ ⟨u * d * u⁻¹, hmem⟩ = φ ⟨u, hu⟩ * φ ⟨d, hdC⟩ * (φ ⟨u, hu⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [e]
  exact h1

theorem le_preimagePCore {C K : Subgroup G} (φ : ↥C →* Γ) (hker : φ.ker = K.subgroupOf C)
    (hKC : K ≤ C) : K ≤ preimagePCore C φ := by
  intro κ hκ
  refine mem_preimagePCore.mpr ⟨hKC hκ, ?_⟩
  have h1 : (⟨κ, hKC hκ⟩ : ↥C) ∈ φ.ker := by
    rw [hker, Subgroup.mem_subgroupOf]
    exact hκ
  rw [MonoidHom.mem_ker.mp h1]
  exact Subgroup.one_mem _

variable [Finite G]

theorem exists_pow_eq_one_of_mem_pCoreOf_range {C : Subgroup G} (φ : ↥C →* Γ) {p : Γ}
    (hp : p ∈ pCoreOf 2 φ.range) : ∃ n : ℕ, p ^ 2 ^ n = 1 := by
  have : Finite ↥φ.range := Finite.of_surjective _ (MonoidHom.rangeRestrict_surjective φ)
  have h2 : IsPGroup 2 ↥(pCoreOf 2 φ.range) :=
    (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥φ.range) 2).map φ.range.subtype
  obtain ⟨n, hn⟩ := h2 ⟨p, hp⟩
  exact ⟨n, by simpa using congrArg Subtype.val hn⟩

theorem exists_pow_mem_of_mem_preimagePCore {C K : Subgroup G} (φ : ↥C →* Γ)
    (hker : φ.ker = K.subgroupOf C) {d : G} (hd : d ∈ preimagePCore C φ) :
    ∃ n : ℕ, d ^ 2 ^ n ∈ K := by
  obtain ⟨hdC, hdP⟩ := mem_preimagePCore.mp hd
  obtain ⟨n, hn⟩ := exists_pow_eq_one_of_mem_pCoreOf_range φ hdP
  refine ⟨n, ?_⟩
  have h1 : (⟨d, hdC⟩ : ↥C) ^ 2 ^ n ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact hn
  rw [hker, Subgroup.mem_subgroupOf] at h1
  exact h1

theorem conj_mem_preimagePCore {C K N : Subgroup G} (φ : ↥C →* Γ) (hker : φ.ker = K.subgroupOf C)
    (hNC : N ≤ Subgroup.normalizer (C : Set G)) (hNK : N ≤ Subgroup.normalizer (K : Set G)) {g d : G}
    (hg : g ∈ N) (hd : d ∈ preimagePCore C φ) : g * d * g⁻¹ ∈ preimagePCore C φ := by
  let Dg : Subgroup G := (preimagePCore C φ).comap (MulAut.conj g⁻¹).toMonoidHom
  have hDg : ∀ x : G, x ∈ Dg ↔ g⁻¹ * x * g ∈ preimagePCore C φ := fun x => by
    simp [Dg]
  let Ng : Subgroup Γ := (Dg.subgroupOf C).map φ
  have hNg : ∀ r : Γ, r ∈ Ng ↔ ∃ c : ↥C, g⁻¹ * (c : G) * g ∈ preimagePCore C φ ∧ φ c = r := by
    intro r
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, (hDg _).mp hc, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, (hDg _).mpr hc, rfl⟩
  have hgi : g⁻¹ ∈ Subgroup.normalizer (C : Set G) := (Subgroup.normalizer _).inv_mem (hNC hg)
  have hNg_le : Ng ≤ φ.range := by
    rintro _ ⟨c, -, rfl⟩
    exact ⟨c, rfl⟩
  have hNg_norm : (Ng.subgroupOf φ.range).Normal := by
    refine ⟨fun n hn r => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨c₁, hc₁, hn1⟩ := (hNg _).mp hn
    obtain ⟨c', hc'⟩ := MonoidHom.mem_range.mp r.2
    refine (hNg _).mpr ⟨c' * c₁ * c'⁻¹, ?_, ?_⟩
    · have hu : g⁻¹ * (c' : G) * g ∈ C := by
        have := (Subgroup.mem_normalizer_iff.mp hgi (c' : G)).mp c'.2
        simpa using this
      have h1 := conj_mem_preimagePCore_of_mem φ hu hc₁
      have e : g⁻¹ * ((c' * c₁ * c'⁻¹ : ↥C) : G) * g =
          (g⁻¹ * (c' : G) * g) * (g⁻¹ * (c₁ : G) * g) * (g⁻¹ * (c' : G) * g)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e]
      exact h1
    · rw [map_mul, map_mul, map_inv, hc', hn1]
      rfl
  have hNg_p : IsPGroup 2 ↥Ng := by
    intro n
    obtain ⟨c₁, hc₁, hn1⟩ := (hNg _).mp n.2
    obtain ⟨m, hm⟩ := exists_pow_mem_of_mem_preimagePCore φ hker hc₁
    refine ⟨m, Subtype.ext ?_⟩
    have e : (c₁ : G) ^ 2 ^ m = g * ((g⁻¹ * (c₁ : G) * g) ^ 2 ^ m) * g⁻¹ := by
      rw [show g⁻¹ * (c₁ : G) * g = g⁻¹ * (c₁ : G) * g⁻¹⁻¹ by rw [inv_inv], conj_pow]
      group
    have h1 : (c₁ : G) ^ 2 ^ m ∈ K := by
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hNK hg) _).mp hm
    have h2 : c₁ ^ 2 ^ m ∈ φ.ker := by
      rw [hker, Subgroup.mem_subgroupOf]
      exact h1
    have h3 : φ c₁ ^ 2 ^ m = 1 := by
      rw [← map_pow]
      exact MonoidHom.mem_ker.mp h2
    show (n : Γ) ^ 2 ^ m = 1
    rw [← hn1]
    exact h3
  have hNg_P : Ng ≤ pCoreOf 2 φ.range := le_pCoreOf 2 hNg_le hNg_norm hNg_p
  obtain ⟨hdC, -⟩ := mem_preimagePCore.mp hd
  have hmem : g * d * g⁻¹ ∈ C := by
    have := (Subgroup.mem_normalizer_iff.mp (hNC hg) d).mp hdC
    exact this
  refine mem_preimagePCore.mpr ⟨hmem, hNg_P ?_⟩
  refine (hNg _).mpr ⟨⟨g * d * g⁻¹, hmem⟩, ?_, rfl⟩
  have e : g⁻¹ * (g * d * g⁻¹) * g = d := by group
  show g⁻¹ * (g * d * g⁻¹) * g ∈ preimagePCore C φ
  rw [e]
  exact hd

theorem normalizer_le_normalizer_preimagePCore {C K N : Subgroup G} (φ : ↥C →* Γ)
    (hker : φ.ker = K.subgroupOf C) (hNC : N ≤ Subgroup.normalizer (C : Set G))
    (hNK : N ≤ Subgroup.normalizer (K : Set G)) :
    N ≤ Subgroup.normalizer (preimagePCore C φ : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro d
  refine ⟨fun hd => conj_mem_preimagePCore φ hker hNC hNK hg hd, fun hd => ?_⟩
  have := conj_mem_preimagePCore φ hker hNC hNK (N.inv_mem hg) hd
  simpa [mul_assoc] using this

end Preimage

end BridgeC

section O2

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t : G}

theorem bridgeC_o2 (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t) {W : Type} [CommGroup W]
    (φ : ↥(Subgroup.centralizer (E : Set G)) →* MulAut W)
    (hker : φ.ker = (S1567.K167 T M E).subgroupOf (Subgroup.centralizer (E : Set G)))
    (hH3 : ∀ D : Subgroup G, D ≤ Subgroup.centralizer (E : Set G) →
        Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (D : Set G) →
        S1567.K167 T M E ≤ D → (∀ d ∈ D, ∃ n : ℕ, d ^ 2 ^ n ∈ S1567.K167 T M E) →
          D ≤ S1567.K167 T M E) : pCoreOf 2 φ.range = ⊥ := by
  have _ := h113
  have _ := k
  have hKC : S1567.K167 T M E ≤ Subgroup.centralizer (E : Set G) := S1567.K167_le_centralizer
  have hD := hH3 (BridgeC.preimagePCore (Subgroup.centralizer (E : Set G)) φ) BridgeC.preimagePCore_le
    (BridgeC.normalizer_le_normalizer_preimagePCore φ hker (S1567.normalizer_le_normalizer_CE E)
      (S1567.normalizer_le_normalizer_K167 T M E))
    (BridgeC.le_preimagePCore φ hker hKC)
    (fun d hd => BridgeC.exists_pow_mem_of_mem_preimagePCore φ hker hd)
  rw [eq_bot_iff]
  intro p hp
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp (pCoreOf_le 2 φ.range hp)
  have hcD : (c : G) ∈ BridgeC.preimagePCore (Subgroup.centralizer (E : Set G)) φ :=
    BridgeC.mem_preimagePCore.mpr ⟨c.2, by simpa [hc] using hp⟩
  have h1 : c ∈ φ.ker := by
    rw [hker, Subgroup.mem_subgroupOf]
    exact hD hcD
  rw [Subgroup.mem_bot, ← hc]
  exact MonoidHom.mem_ker.mp h1

end O2

end CFSG.Quasithin.S153N
