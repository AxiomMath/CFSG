module

public import CFSG.Quasithin.H13.A6S13829d
public import CFSG.Quasithin.H13.A6S13832a
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Block
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5Fin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.Quasithin.Background.A3Structure312Facts
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.Quasithin.Background.F6Amalgams
public import CFSG.Quasithin.Background.F6SolvableQuotient
public import CFSG.Quasithin.EmptyFaithful.S1421L246
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S146C1
public import CFSG.Quasithin.EmptyFaithful.S146C2
public import CFSG.Quasithin.EmptyFaithful.S146G4
public import CFSG.Quasithin.EmptyFaithful.S146ThreeB
public import CFSG.Quasithin.EmptyFaithful.S151cCasei
public import CFSG.Quasithin.EmptyFaithful.S151cStmt
public import CFSG.Quasithin.EmptyFaithful.S152N11
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.H13.A5Quad
public import CFSG.Quasithin.H13.A5S1523
public import CFSG.Quasithin.H13.A5Sit15d
public import CFSG.Quasithin.H13.A6S13828b
public import CFSG.Quasithin.H13.A6S13833j
public import CFSG.Quasithin.H13.KGFactHatA6
public import CFSG.Quasithin.Vol2.Ch11SecAFacts
public import CFSG.Quasithin.Vol2.Ch11SecAVi2
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.Quasithin.Vol2.Ch12Sec2Action
public import CFSG.Quasithin.Vol2.Ch3Sec3StatementsB
public import CFSG.Quasithin.Vol2.Ch4Sec2Lem424N
public import CFSG.Sporadic.J4.QT2LocProof
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CPrime
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralAut
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase
public import Certificates.Kernel.J4Count.Prim

public section

namespace CFSG.Quasithin.H13.A6

open Matrix Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits

local notation "M4" => Matrix (Fin 4) (Fin 4) (ZMod 2)

theorem std_indep4 : ∀ x : Fin 4 → ZMod 2,
    x 0 • (Pi.single 0 1 : Fin 4 → ZMod 2) + x 1 • Pi.single 1 1 + x 2 • Pi.single 2 1 +
      x 3 • Pi.single 3 1 = 0 → x = 0 := by
  intro x hx
  funext i
  have := congrFun hx i
  fin_cases i <;> simpa using this

theorem exists_GL_e01 {a b : Fin 4 → ZMod 2} (hab : pl a b ≠ 0) :
    ∃ M : GL (Fin 4) (ZMod 2), (M : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Pi.single 0 1) = a ∧
      (M : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Pi.single 1 1) = b := by
  obtain ⟨ha, hb, hab'⟩ := (pl_ne_zero_iff a b).1 hab
  obtain ⟨c, d, hcd⟩ := exists_basis_of_pair ha hb hab'
  obtain ⟨M, h0, h1, -, -⟩ := exists_GL_map4 std_indep4 hcd
  exact ⟨M, h0, h1⟩

theorem exists_pl_ne_zero {a : Fin 4 → ZMod 2} (ha : a ≠ 0) : ∃ b, pl a b ≠ 0 := by
  obtain ⟨b, hb⟩ := exists_not_mem_list [0, a] (by simp)
  simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hb
  exact ⟨b, (pl_ne_zero_iff a b).2 ⟨ha, hb.1, Ne.symm hb.2⟩⟩

theorem GL_mulVec_inv (M : GL (Fin 4) (ZMod 2)) (v : Fin 4 → ZMod 2) :
    (M : M4) *ᵥ ((M⁻¹ : GL (Fin 4) (ZMod 2)) : M4) *ᵥ v = v := by
  rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

theorem GL_inv_mulVec (M : GL (Fin 4) (ZMod 2)) (v : Fin 4 → ZMod 2) :
    ((M⁻¹ : GL (Fin 4) (ZMod 2)) : M4) *ᵥ (M : M4) *ᵥ v = v := by
  rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

theorem wedge2_injective (M : GL (Fin 4) (ZMod 2)) :
    Function.Injective (wedge2 (M : Matrix (Fin 4) (Fin 4) (ZMod 2))).mulVec := by
  intro x y h
  have key : ∀ z, (wedge2 ((M⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))).mulVec
      ((wedge2 (M : Matrix (Fin 4) (Fin 4) (ZMod 2))).mulVec z) = z := fun z => by
    rw [wedge2_mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, wedge2_one,
      one_mulVec]
  rw [← key x, ← key y, h]

@[expose] def plHom (a : Fin 4 → ZMod 2) : (Fin 4 → ZMod 2) →+ (Fin 6 → ZMod 2) where
  toFun := pl a
  map_zero' := pl_zero_right a
  map_add' := pl_add_right a

theorem plHom_apply (a x : Fin 4 → ZMod 2) : plHom a x = pl a x := rfl

theorem neg_vec6 (ω : Fin 6 → ZMod 2) : -ω = ω := by
  funext i
  exact ZMod.neg_eq_self_mod_two (ω i)

@[expose] def plS (a b : Fin 4 → ZMod 2) : AddSubgroup (Fin 6 → ZMod 2) where
  carrier := {ω | ∃ x y, pl a x + pl b y = ω}
  add_mem' := by
    rintro _ _ ⟨x, y, rfl⟩ ⟨x', y', rfl⟩
    exact ⟨x + x', y + y', by rw [pl_add_right, pl_add_right]; abel⟩
  zero_mem' := ⟨0, 0, by rw [pl_zero_right, pl_zero_right, add_zero]⟩
  neg_mem' := by
    rintro _ ⟨x, y, rfl⟩
    exact ⟨x, y, (neg_vec6 _).symm⟩

theorem mem_plS {a b : Fin 4 → ZMod 2} {ω : Fin 6 → ZMod 2} :
    ω ∈ plS a b ↔ ∃ x y, pl a x + pl b y = ω := Iff.rfl

theorem pl_mem_plS_left (a b x : Fin 4 → ZMod 2) : pl a x ∈ plS a b :=
  mem_plS.2 ⟨x, 0, by rw [pl_zero_right, add_zero]⟩

theorem pl_mem_plS_right (a b y : Fin 4 → ZMod 2) : pl b y ∈ plS a b :=
  mem_plS.2 ⟨0, y, by rw [pl_zero_right, zero_add]⟩

theorem mem_plS_e01 (ω : Fin 6 → ZMod 2) :
    ω ∈ plS (Pi.single 0 1) (Pi.single 1 1) ↔ ω 5 = 0 := by
  rw [mem_plS]
  constructor
  · rintro ⟨x, y, rfl⟩
    simp [pl, wedgePair]
  · intro h
    refine ⟨![0, ω 0, ω 1, ω 2], ![0, 0, ω 3, ω 4], ?_⟩
    funext p
    fin_cases p <;> simp [pl, wedgePair, h]

theorem mem_plHom_e0 (ω : Fin 6 → ZMod 2) :
    ω ∈ (plHom (Pi.single 0 1)).range ↔ ω 3 = 0 ∧ ω 4 = 0 ∧ ω 5 = 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    simp [plHom_apply, pl, wedgePair]
  · rintro ⟨h3, h4, h5⟩
    refine ⟨![0, ω 0, ω 1, ω 2], ?_⟩
    funext p
    fin_cases p <;> simp [plHom_apply, pl, wedgePair, h3, h4, h5]

theorem card_plS_e01 : Nat.card ↥(plS (Pi.single 0 1) (Pi.single 1 1)) = 32 := by
  have e : Nat.card ↥(plS (Pi.single 0 1) (Pi.single 1 1)) =
      Nat.card {ω : Fin 6 → ZMod 2 // ω 5 = 0} :=
    Nat.card_congr (Equiv.subtypeEquivRight mem_plS_e01)
  rw [e, Nat.card_eq_fintype_card]
  decide

theorem card_plHom_e0 : Nat.card ↥(plHom (Pi.single 0 1)).range = 8 := by
  have e : Nat.card ↥(plHom (Pi.single 0 1)).range =
      Nat.card {ω : Fin 6 → ZMod 2 // ω 3 = 0 ∧ ω 4 = 0 ∧ ω 5 = 0} :=
    Nat.card_congr (Equiv.subtypeEquivRight mem_plHom_e0)
  rw [e, Nat.card_eq_fintype_card]
  decide

@[expose] def wedge2Hom (M : GL (Fin 4) (ZMod 2)) : (Fin 6 → ZMod 2) →+ (Fin 6 → ZMod 2) where
  toFun := (wedge2 (M : Matrix (Fin 4) (Fin 4) (ZMod 2))).mulVec
  map_zero' := mulVec_zero _
  map_add' := mulVec_add _

theorem plS_eq_map (M : GL (Fin 4) (ZMod 2)) :
    plS ((M : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Pi.single 0 1))
        ((M : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Pi.single 1 1)) =
      (plS (Pi.single 0 1) (Pi.single 1 1)).map (wedge2Hom M) := by
  ext ω
  rw [AddSubgroup.mem_map, mem_plS]
  constructor
  · rintro ⟨x, y, rfl⟩
    refine ⟨pl (Pi.single 0 1) (((M⁻¹ : GL (Fin 4) (ZMod 2)) : M4) *ᵥ x) +
      pl (Pi.single 1 1) (((M⁻¹ : GL (Fin 4) (ZMod 2)) : M4) *ᵥ y),
      mem_plS.2 ⟨_, _, rfl⟩, ?_⟩
    show (wedge2 (M : Matrix (Fin 4) (Fin 4) (ZMod 2))).mulVec _ = _
    rw [mulVec_add, wedge2_mulVec_pl, wedge2_mulVec_pl, GL_mulVec_inv, GL_mulVec_inv]
  · rintro ⟨ω', hω', rfl⟩
    obtain ⟨x, y, rfl⟩ := mem_plS.1 hω'
    refine ⟨(M : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec x,
      (M : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec y, ?_⟩
    show _ = (wedge2 (M : Matrix (Fin 4) (Fin 4) (ZMod 2))).mulVec _
    rw [mulVec_add, wedge2_mulVec_pl, wedge2_mulVec_pl]

theorem plHom_range_eq_map (M : GL (Fin 4) (ZMod 2)) :
    (plHom ((M : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Pi.single 0 1))).range =
      (plHom (Pi.single 0 1)).range.map (wedge2Hom M) := by
  ext ω
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨pl (Pi.single 0 1) (((M⁻¹ : GL (Fin 4) (ZMod 2)) : M4) *ᵥ x),
      ⟨_, rfl⟩, ?_⟩
    show (wedge2 (M : Matrix (Fin 4) (Fin 4) (ZMod 2))).mulVec _ = pl _ x
    rw [wedge2_mulVec_pl, GL_mulVec_inv]
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨(M : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec x, ?_⟩
    show pl _ _ = (wedge2 (M : Matrix (Fin 4) (Fin 4) (ZMod 2))).mulVec (pl _ x)
    rw [wedge2_mulVec_pl]

theorem card_plS {a b : Fin 4 → ZMod 2} (hab : pl a b ≠ 0) : Nat.card ↥(plS a b) = 32 := by
  obtain ⟨M, h0, h1⟩ := exists_GL_e01 hab
  rw [← h0, ← h1, plS_eq_map, AddSubgroup.card_map_of_injective (wedge2_injective M)]
  exact card_plS_e01

theorem card_plHom_range {a : Fin 4 → ZMod 2} (ha : a ≠ 0) : Nat.card ↥(plHom a).range = 8 := by
  obtain ⟨b, hb⟩ := exists_pl_ne_zero ha
  obtain ⟨M, h0, -⟩ := exists_GL_e01 hb
  rw [← h0, plHom_range_eq_map, AddSubgroup.card_map_of_injective (wedge2_injective M)]
  exact card_plHom_e0

theorem plS_add_right (a b : Fin 4 → ZMod 2) : plS a (a + b) = plS a b := by
  ext ω
  rw [mem_plS, mem_plS]
  constructor
  · rintro ⟨x, y, rfl⟩
    exact ⟨x + y, y, by rw [pl_add_left, pl_add_right]; abel⟩
  · rintro ⟨x, y, rfl⟩
    refine ⟨x + y, y, ?_⟩
    rw [pl_add_left, pl_add_right]
    have h2 : pl a y + pl a y = 0 := by
      funext i
      simp only [Pi.add_apply, Pi.zero_apply]
      generalize pl a y i = s
      revert s
      decide
    rw [show pl a x + pl a y + (pl a y + pl b y) = pl a x + pl b y + (pl a y + pl a y) by abel,
      h2, add_zero]

theorem pl_mem_plS_of_span {a b c : Fin 4 → ZMod 2} (hc : c = 0 ∨ c = a ∨ c = b ∨ c = a + b)
    (x : Fin 4 → ZMod 2) : pl c x ∈ plS a b := by
  rcases hc with h | h | h | h <;> rw [h]
  · rw [pl_zero_left]
    exact (plS a b).zero_mem
  · exact pl_mem_plS_left a b x
  · exact pl_mem_plS_right a b x
  · rw [pl_add_left]
    exact (plS a b).add_mem (pl_mem_plS_left a b x) (pl_mem_plS_right a b x)

theorem fix_e01_core : ∀ c d v : Fin 4 → ZMod 2,
    (cols4 (Pi.single 0 1) (Pi.single 1 1) c d * cols4 (Pi.single 0 1) (Pi.single 1 1) c d *
        cols4 (Pi.single 0 1) (Pi.single 1 1) c d = 1 ∧
      cols4 (Pi.single 0 1) (Pi.single 1 1) c d ≠ 1 ∧
      (cols4 (Pi.single 0 1) (Pi.single 1 1) c d).mulVec v = v) →
        v 2 = 0 ∧ v 3 = 0 := by
  decide +kernel

theorem eq_cols4_self (N : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    N = cols4 (N.mulVec (Pi.single 0 1)) (N.mulVec (Pi.single 1 1)) (N.mulVec (Pi.single 2 1))
      (N.mulVec (Pi.single 3 1)) := by
  ext i j
  fin_cases j <;> simp [cols4]

theorem fix_mem_span {w₁ w₂ : Fin 4 → ZMod 2} (hw : pl w₁ w₂ ≠ 0) {M : GL (Fin 4) (ZMod 2)}
    (h1 : (M : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec w₁ = w₁)
    (h2 : (M : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec w₂ = w₂) (h3 : M ^ 3 = 1) (hM : M ≠ 1)
    {v : Fin 4 → ZMod 2} (hv : (M : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v = v) :
    v = 0 ∨ v = w₁ ∨ v = w₂ ∨ v = w₁ + w₂ := by
  obtain ⟨P, hP0, hP1⟩ := exists_GL_e01 hw
  set N : GL (Fin 4) (ZMod 2) := P⁻¹ * M * P with hN
  have hNv : ∀ u, (N : M4) *ᵥ u = ((P⁻¹ : GL (Fin 4) (ZMod 2)) : M4) *ᵥ (M : M4) *ᵥ (P : M4) *ᵥ u :=
    fun u => by rw [hN, Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec]
  have hN0 : (N : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Pi.single 0 1) = Pi.single 0 1 := by
    rw [hNv, hP0, h1, ← hP0, GL_inv_mulVec]
  have hN1 : (N : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Pi.single 1 1) = Pi.single 1 1 := by
    rw [hNv, hP1, h2, ← hP1, GL_inv_mulVec]
  have hN3 : (N : Matrix (Fin 4) (Fin 4) (ZMod 2)) * N * N = 1 := by
    have : N ^ 3 = 1 := by
      have e : (P⁻¹ * M * P) ^ 3 = P⁻¹ * M ^ 3 * P := by
        rw [pow_three', pow_three']
        group
      rw [hN, e, h3, mul_one, inv_mul_cancel]
    rw [← Units.val_mul, ← Units.val_mul, ← pow_three', this, Units.val_one]
  have hN1' : (N : Matrix (Fin 4) (Fin 4) (ZMod 2)) ≠ 1 := by
    intro h
    apply hM
    have hN' : N = 1 := Units.ext h
    rw [hN] at hN'
    calc M = P * (P⁻¹ * M * P) * P⁻¹ := by group
      _ = 1 := by rw [hN', mul_one, mul_inv_cancel]
  set u := ((P⁻¹ : GL (Fin 4) (ZMod 2)) : M4) *ᵥ v with hu
  have hNu : (N : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec u = u := by
    rw [hNv, hu, GL_mulVec_inv, hv]
  have hc := eq_cols4_self (N : Matrix (Fin 4) (Fin 4) (ZMod 2))
  rw [hN0, hN1] at hc
  have key := fix_e01_core _ _ u ⟨hc ▸ hN3, hc ▸ hN1', by rw [← hc]; exact hNu⟩
  have hu' : u = u 0 • Pi.single 0 1 + u 1 • Pi.single 1 1 := by
    funext i
    fin_cases i <;> simp [key.1, key.2]
  have hv' : v = u 0 • w₁ + u 1 • w₂ := by
    have e1 : v = (P : M4) *ᵥ u := (GL_mulVec_inv P v).symm
    rw [e1]
    conv_lhs => rw [hu']
    rw [mulVec_add, mulVec_smul, mulVec_smul, hP0, hP1]
  rcases zmodTwo_cases (u 0) with h0 | h0 <;> rcases zmodTwo_cases (u 1) with h1' | h1' <;>
    simp [hv', h0, h1']

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
  [IsMulCommutative ↥(conjClosure V S.G1)]
  {ρ : ↥S.G1 →* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)}
  {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (Fin 4 → ZMod 2)}

theorem exists_gamma' (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1) (hρs : Function.Surjective ρ)
    (hβk : ∀ u : ↥(conjClosure S.V3 S.G1), β u = 1 ↔ (u : G) ∈ fsuV1 T V)
    (hβe : ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
      Multiplicative.toAdd (β v) =
        ((ρ h : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Multiplicative.toAdd (β u)))
    (hline : ∀ a b c : Fin 4 → ZMod 2, pl a b ≠ 0 → pl a c ≠ 0 →
      pl a b ≠ pl a c → S.Phi ρ β (pl a b) + S.Phi ρ β (pl a c) = S.Phi ρ β (pl a (b + c)))
    (hv0 : S.v04 ∉ conjClosure S.V3 S.G1) :
    ∃ γ : ↥(conjClosure V S.G1) →* Multiplicative (Fin 6 → ZMod 2),
      Function.Surjective γ ∧ (∀ v, γ v = 1 ↔ (v : G) ∈ conjClosure S.V3 S.G1) ∧
      (∀ (h : ↥S.G1) (u v : ↥(conjClosure V S.G1)), (v : G) = h * u * h⁻¹ →
        Multiplicative.toAdd (γ v) =
          (wedge2 ((ρ h : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :
            Matrix (Fin 4) (Fin 4) (ZMod 2))).mulVec (Multiplicative.toAdd (γ u))) ∧
      ∀ v, S.Theta ρ β hF (Multiplicative.toAdd (γ v)) = S.cls v := by
  set e : (Fin 6 → ZMod 2) ≃+ S.VUQ := AddEquiv.ofBijective (S.Theta ρ β hF)
    ⟨S.Theta_injective hF hρs hβk hβe hline hv0, S.Theta_surjective hF hβk hβe hline⟩ with he
  let γ : ↥(conjClosure V S.G1) →* Multiplicative (Fin 6 → ZMod 2) :=
    { toFun := fun v => Multiplicative.ofAdd (e.symm (S.cls v))
      map_one' := by
        rw [show S.cls 1 = 0 from (S.cls_eq_zero_iff 1).2 (conjClosure S.V3 S.G1).one_mem,
          map_zero, ofAdd_zero]
      map_mul' := fun v w => by rw [cls_mul, map_add, ofAdd_add] }
  have hγ : ∀ v, S.Theta ρ β hF (Multiplicative.toAdd (γ v)) = S.cls v := fun v => by
    show S.Theta ρ β hF (e.symm (S.cls v)) = S.cls v
    rw [show S.Theta ρ β hF (e.symm (S.cls v)) = e (e.symm (S.cls v)) from rfl,
      AddEquiv.apply_symm_apply]
  refine ⟨γ, fun x => ?_, fun v => ?_, fun h u v huv => ?_, hγ⟩
  · obtain ⟨q, hq⟩ := S.Theta_surjective hF hβk hβe hline (S.Theta ρ β hF (Multiplicative.toAdd x))
    induction hq' : S.Theta ρ β hF (Multiplicative.toAdd x) using Additive.rec with
    | _ q' =>
      induction q' using QuotientGroup.induction_on with
      | _ w =>
        refine ⟨w, ?_⟩
        apply Multiplicative.toAdd.injective
        apply S.Theta_injective hF hρs hβk hβe hline hv0
        rw [hγ]
        exact hq'.symm
  · constructor
    · intro h1
      have := hγ v
      rw [h1, toAdd_one, map_zero] at this
      exact (S.cls_eq_zero_iff v).1 this.symm
    · intro hv
      apply Multiplicative.toAdd.injective
      apply S.Theta_injective hF hρs hβk hβe hline hv0
      rw [hγ, toAdd_one, map_zero]
      exact (S.cls_eq_zero_iff v).2 hv
  · apply S.Theta_injective hF hρs hβk hβe hline hv0
    rw [hγ, S.Theta_equiv hF hρs hβk hβe hline, hγ, act_cls]
    congr 1
    exact Subtype.ext huv

end Setting4

end CFSG.Quasithin.H13.A6

