module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CC
public import CFSG.Quasithin.Vol2.Ch10SecA1012P5Fix
public import CFSG.Quasithin.Vol2.Ch10SecQ34B0
public import CFSG.Quasithin.Vol2.Ch10SecQ34LH
public import CFSG.Quasithin.Vol2.Ch10SecQ3CG
public import CFSG.Quasithin.Vol2.Ch10SecQ3CZA

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isSylowTwoOf_map_conj {S X : Subgroup G} (hS : IsSylowTwoOf S X) (g : G) :
    IsSylowTwoOf (S.map (MulAut.conj g).toMonoidHom) (X.map (MulAut.conj g).toMonoidHom) := by
  have hinj := (MulAut.conj g).injective
  refine ⟨Subgroup.map_mono hS.1,
    hS.2.1.of_equiv (S.equivMapOfInjective (MulAut.conj g).toMonoidHom hinj), ?_⟩
  have h := Subgroup.relIndex_map_map_of_injective S X (f := (MulAut.conj g).toMonoidHom) hinj
  rw [IsSylowTwoOf] at hS
  rw [show ((S.map (MulAut.conj g).toMonoidHom).subgroupOf
    (X.map (MulAut.conj g).toMonoidHom)).index = (S.subgroupOf X).index from h]
  exact hS.2.2

theorem centralizes_of_sylow {X S : Subgroup G} {F : Type} [Field F] [Finite F] {m : ℕ}
    (hF : Nat.card F = 2 ^ m)
    (he : Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* Matrix.SpecialLinearGroup (Fin 2) F))
    (hS : IsSylowTwoOf S X) {y : G} (hyN : y ∈ Subgroup.normalizer (X : Set G))
    (hyo : Odd (orderOf y)) (hyS : ∀ s ∈ S, y * s * y⁻¹ = s) : ∀ x ∈ X, y * x * y⁻¹ = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (S.subgroupOf X) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  have hidx : ¬ 2 ∣ (S.subgroupOf X).index := hS.2.2
  have h := factOddAutCentSylow_holds ↥X F m hF he (hP.toSylow hidx) (conjAct X ⟨y, hyN⟩)
    (SecA.odd_orderOf_conjAct hyN hyo) (fun s hs => Subtype.ext (by
      rw [SecA.coe_conjAct_apply']
      exact hyS s hs))
  intro x hx
  have h' := congrArg (fun φ : MulAut ↥X => ((φ ⟨x, hx⟩ : ↥X) : G)) h
  simp only [SecA.coe_conjAct_apply', MulAut.one_apply] at h'
  exact h'

theorem eq_one_of_centralizes {X : Subgroup G} {F : Type} [Field F] [Finite F] {m : ℕ}
    (hF : Nat.card F = 2 ^ m)
    (he : Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* Matrix.SpecialLinearGroup (Fin 2) F))
    {y : G} (hyX : y ∈ X) (hyo : Odd (orderOf y)) (hyC : ∀ x ∈ X, y * x * y⁻¹ = x) : y = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := he
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥X)
  have hc : e (π ⟨y, hyX⟩) ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨w, rfl⟩ := e.surjective z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X) w
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 2
    apply Subtype.ext
    have h := hyC x x.2
    simp only [Subgroup.coe_mul]
    calc (x : G) * y = y * x * y⁻¹ * y := by rw [h]
      _ = y * x := by group
  rw [center_sl2_eq_bot, Subgroup.mem_bot, ← map_one e, e.injective.eq_iff,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hc
  have hyO := (C10P34.mem_pCoreOf_iff hyX).mpr hc
  exact eq_one_of_mem_of_odd (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X) hyO hyo

variable {T L I H K : Subgroup G} {n k : ℕ} {b : G}
  {hel : IsElemAbelian 2 (VZ T H)} {I' : Finset (Subgroup (MulAut (IntMod (VZ T H) hel)))}
  {K₀ : Subgroup (MulAut (IntMod (VZ T H) hel))}

structure Ctx9 (c : Ctx T L I H K n k b hel I' K₀) (t : G) (L₁ : Subgroup G) : Prop where
  ht : t ∈ T
  htn : t ∉ Subgroup.normalizer (L : Set G)
  hL₁ : L₁ = L ∨ L₁ = CFSG.conjugate L t
  hbL₁ : b ∈ L₁
  hS₁L₁ : IsSylowTwoOf ⁅baum T, Subgroup.zpowers b⁆ L₁
  hS₁K : IsSylowTwoOf ⁅baum T, Subgroup.zpowers b⁆ K
  hL₁blk : IsShort2 L₁ ∧ IsLin2Type L₁ n ∧ blockZ L₁ = ⊥ ∧ blockQ L₁ = blockU L₁
  hKblk : IsShort2 K ∧ IsLin2Type K n ∧ blockZ K = ⊥ ∧ blockQ K = blockU K
  h1012 : Stmt10_1_2
  h1021 : Stmt10_2_1
  h39 : Vol2Native.A39ForSQTKCat
  hKF9 : FactTwoL2BlocksSL3

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
