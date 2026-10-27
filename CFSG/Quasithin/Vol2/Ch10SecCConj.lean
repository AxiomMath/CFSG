module

public import CFSG.Quasithin.Vol2.Ch10SecCGroup
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122APerfect
public import CFSG.Quasithin.Background.A3Structure316

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open

variable {G : Type*} [Group G]

theorem commutator_map_eq {X : Subgroup G} (e : G ≃* G) (hX : ⁅X, X⁆ = X) :
    ⁅X.map e.toMonoidHom, X.map e.toMonoidHom⁆ = X.map e.toMonoidHom := by
  rw [← Subgroup.map_commutator, hX]

theorem isSimpleGroup_quot_map {X : Subgroup G} (e : G ≃* G)
    (hX : IsSimpleGroup (↥X ⧸ CFSG.pCore 2 ↥X)) :
    IsSimpleGroup (↥(X.map e.toMonoidHom) ⧸ CFSG.pCore 2 ↥(X.map e.toMonoidHom)) := by
  let φ : ↥X ≃* ↥(X.map e.toMonoidHom) := X.equivMapOfInjective e.toMonoidHom e.injective
  have hφ : (CFSG.pCore 2 ↥X).map (φ : ↥X →* ↥(X.map e.toMonoidHom)) =
      CFSG.pCore 2 ↥(X.map e.toMonoidHom) := CFSG.pCore_map_iso 2 φ
  let ψ := QuotientGroup.congr (CFSG.pCore 2 ↥X) (CFSG.pCore 2 ↥(X.map e.toMonoidHom)) φ hφ
  exact @MulEquiv.isSimpleGroup _ _ _ _ hX ψ.symm

theorem relIndex_pCoreOf_map (X : Subgroup G) (e : G ≃* G) :
    (pCoreOf 2 (X.map e.toMonoidHom)).relIndex (X.map e.toMonoidHom) =
      (pCoreOf 2 X).relIndex X := by
  rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 e X,
    Subgroup.relIndex_map_map_of_injective _ _ e.injective]

theorem oPrimeResidualOf_le (p : ℕ) (X : Subgroup G) : oPrimeResidualOf p X ≤ X :=
  (Subgroup.closure_le X).mpr fun _ hx => hx.1

theorem oPrimeResidualOf_mono (p : ℕ) {X Y : Subgroup G} (h : X ≤ Y) :
    oPrimeResidualOf p X ≤ oPrimeResidualOf p Y :=
  Subgroup.closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

theorem oPrimeResidualOf_map (p : ℕ) (X : Subgroup G) (e : G ≃* G) :
    oPrimeResidualOf p (X.map e.toMonoidHom) = (oPrimeResidualOf p X).map e.toMonoidHom := by
  rw [oPrimeResidualOf, oPrimeResidualOf, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, k, hk⟩
    refine ⟨x, ⟨hx, k, ?_⟩, rfl⟩
    rwa [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq] at hk
  · rintro ⟨x, ⟨hx, k, hk⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, k, ?_⟩
    rwa [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]

variable [Finite G]

theorem oPrimeResidualOf_eq_self {p : ℕ} (hp : p.Prime) {L : Subgroup G} (hL : ⁅L, L⁆ = L)
    (hsimp : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L))
    (hdvd : p ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)) : oPrimeResidualOf p L = L := by
  have : Fact p.Prime := ⟨hp⟩
  have : Group.IsPerfect ↥L := isPerfect_of_commutator_eq hL
  have h2 : IsPGroup 2 ↥(CFSG.pCore 2 ↥L) := CFSG.pCore_isPGroup (p := 2) (G := ↥L)
  have : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal (p := 2) (G := ↥L)
  have htop := @CFSG.QuasithinUnique.Vol2Native.L122A.primeResidual_eq_top_of_perfect ↥L _ _ _ p hp
    (CFSG.pCore 2 ↥L) _ h2 hsimp hdvd
  rw [CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual_eq_closure] at htop
  apply le_antisymm (oPrimeResidualOf_le p L)
  intro x hx
  have hmem : (⟨x, hx⟩ : ↥L) ∈ Subgroup.closure {y : ↥L | ∃ k : ℕ, orderOf y = p ^ k} := by
    rw [htop]
    trivial
  have hmap := Subgroup.mem_map_of_mem L.subtype hmem
  rw [MonoidHom.map_closure] at hmap
  refine Subgroup.closure_mono ?_ hmap
  rintro _ ⟨y, ⟨k, hk⟩, rfl⟩
  exact ⟨y.2, k, by rwa [Subgroup.coe_subtype, Subgroup.orderOf_coe]⟩

end CFSG.Quasithin.Vol2.Ch10.SecC
