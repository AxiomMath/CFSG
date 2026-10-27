module

public import CFSG.LocalAnalysis.StandardType.GGOuterInvAtTwistedE6
public import CFSG.LocalAnalysis.StandardType.GGTwE6OuterGenInvol
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Aut
public import CFSG.LocalAnalysis.StandardType.GGRootCentKGStructE6Diag
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.E6Aux.Diag

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (IsElemAbelian)
open CFSG.HardMathSupport.Dickson.Sec6.I923 (e6Rho e6Phi e6Lam e6C e6Graph e6Phi_rho_mul
  e6Graph_conj_rootDiag)

theorem mem_of_commute_diag_graph {G M : Type*} [Group G] [CommGroup M] {N : Subgroup G}
    [N.Normal] (D : M →* G) (r : M → M) (γ : G) (hγ : ∀ b, γ * D b * γ⁻¹ = D (r b))
    (hr : ∀ b, D (r b * b) ∈ N) (h3 : ∀ b, D (b ^ 3) ∈ N) {i h : G} (hi : i ∈ N) (hh : h ∈ N)
    {a b : M} (hc : i * D b * (h * (D a * γ)) = h * (D a * γ) * (i * D b)) :
    i * D b ∈ N := by
  have e : ∀ {y : G}, y ∈ N → (y : G ⧸ N) = 1 := fun hy => (QuotientGroup.eq_one_iff _).2 hy
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, e hi, one_mul]
  have hc' := congrArg (QuotientGroup.mk : G → G ⧸ N) hc
  simp only [QuotientGroup.mk_mul, e hi, e hh, one_mul] at hc'
  have hab : ((D b : G) : G ⧸ N) * (D a : G) = ((D a : G) : G ⧸ N) * (D b : G) := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← map_mul D, ← map_mul D, mul_comm]
  have hPγ : ((D b : G) : G ⧸ N) * γ = (γ : G ⧸ N) * (D b : G) := by
    rw [← mul_assoc, hab, mul_assoc, mul_assoc] at hc'
    exact mul_left_cancel hc'
  have hP : ((D b : G) : G ⧸ N) = (D (r b) : G) := by
    refine mul_right_cancel (b := (γ : G ⧸ N)) ?_
    rw [hPγ, ← hγ b, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      inv_mul_cancel_right]
  have h2 : ((D b : G) : G ⧸ N) * (D b : G) = 1 := by
    calc ((D b : G) : G ⧸ N) * (D b : G) = ((D (r b) : G) : G ⧸ N) * (D b : G) := by rw [← hP]
      _ = 1 := by rw [← QuotientGroup.mk_mul, ← map_mul D]; exact e (hr b)
  have h3' : ((D b : G) : G ⧸ N) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, ← map_pow D]
    exact e (h3 b)
  calc ((D b : G) : G ⧸ N) = ((D b : G) : G ⧸ N) ^ 3 * (((D b : G) : G ⧸ N) * (D b : G))⁻¹ := by
        group
    _ = 1 := by rw [h3', h2, inv_one, mul_one]

section Torus

variable {K : Type} [Field K]

theorem mul_inv_mulSingle_e6Phi_mem (c : Fin Tag.E6.rank → Kˣ) :
    c * (Pi.mulSingle (0 : Fin Tag.E6.rank) (e6Phi K c))⁻¹ ∈
      TableB.torusSubgroup Tag.E6.cartan K := by
  set T := TableB.torusSubgroup Tag.E6.cartan K
  have key : (QuotientGroup.mk' T) = (QuotientGroup.mk' T).comp
      ((MonoidHom.mulSingle (fun _ : Fin Tag.E6.rank => Kˣ) 0).comp (e6Phi K)) := by
    refine MonoidHom.pi_ext fun j s => ?_
    have hφ : e6Phi K (Pi.mulSingle (M := fun _ => Kˣ) j s) = s ^ e6Lam j := by
      change ∏ i, (Pi.mulSingle (M := fun _ => Kˣ) j s i) ^ e6Lam i = _
      rw [Finset.prod_eq_single j]
      · simp
      · intro i _ hi
        simp [Pi.mulSingle_eq_of_ne hi]
      · simp
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.mulSingle_apply, hφ,
      QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem,
      div_eq_mul_inv]
    exact TableB.mulSingle_mul_inv_mem_torusE6 K j s
  have h := DFunLike.congr_fun key c
  rwa [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.mulSingle_apply,
    QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem,
    div_eq_mul_inv] at h

theorem e6Rho_mul_mem_torusSubgroup (b : Fin Tag.E6.rank → Kˣ) :
    e6Rho K b * b ∈ TableB.torusSubgroup Tag.E6.cartan K := by
  have h := mul_inv_mulSingle_e6Phi_mem (e6Rho K b * b)
  rw [e6Phi_rho_mul] at h
  have h3 : Pi.mulSingle (0 : Fin Tag.E6.rank) ((∏ k, b k ^ e6C k) ^ 3) ∈
      TableB.torusSubgroup Tag.E6.cartan K := by
    have := TableB.mulSingle_pow_mem_torusSubgroup (LargeEvenCartanE 6) K TableB.cartanE6_adj 0
      (∏ k, b k ^ e6C k)
    rw [zpow_natCast] at this
    exact this
  have := mul_mem h h3
  rwa [inv_mul_cancel_right] at this

theorem rootDiagUnit_mem_adjointGroup_of_mem_torusSubgroup
    {a : Fin Tag.E6.rank → Kˣ}
    (ha : a ∈ TableB.torusSubgroup Tag.E6.cartan K) :
    rootDiagUnit Tag.E6 a ∈ adjointGroup Tag.E6 K := by
  have hle : TableB.torusSubgroup Tag.E6.cartan K ≤
      (adjointGroup Tag.E6 K).comap (rootDiagUnitHom Tag.E6 K) := by
    rw [TableB.torusSubgroup, Subgroup.closure_le]
    rintro _ ⟨⟨i, t⟩, rfl⟩
    change rootDiagUnit Tag.E6 (fun j => t ^ Tag.E6.cartan i j) ∈ adjointGroup Tag.E6 K
    rw [← torusElt_eq_rootDiagUnit]
    exact torusElt_mem_adjointGroup i t
  exact hle ha

end Torus


section E6

variable {K : Type} [Field K]

theorem e6DiagHom_mem_inn_of_mem_torusSubgroup {b : Fin Tag.E6.rank → Kˣ}
    (hb : b ∈ TableB.torusSubgroup Tag.E6.cartan K) :
    AutSt.e6DiagHom K b ∈
      (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range :=
  ⟨_, (TableBExc.exactNormalAut_eq_conj_of_mem
    (rootDiagUnit_mem_adjointGroup_of_mem_torusSubgroup hb)).symm⟩

theorem e6Graph_conj_e6DiagHom (b : Fin Tag.E6.rank → Kˣ) :
    e6Graph K * AutSt.e6DiagHom K b * (e6Graph K)⁻¹ = AutSt.e6DiagHom K (e6Rho K b) := by
  have hD : ∀ c, AutSt.e6DiagHom K c = rootDiagAutHom .E6 K c := fun c =>
    (KGE6.rootDiagAutHom_eq_exactNormalAut c).symm
  rw [hD, hD]
  exact e6Graph_conj_rootDiag K b

theorem exactNormalAut_graph_eq_e6DiagHom_mul (a : Fin Tag.E6.rank → Kˣ) :
    exactNormalAut .E6 K a 1 1 = AutSt.e6DiagHom K a * e6Graph K := by
  have h := exactNormalAut_diag_mul (τ := .E6) (K := K) a 1 1 1
  rw [mul_one] at h
  exact h.symm

theorem e6_mem_inn_of_mem_innDiag_of_commute
    (g : adjointGroup .E6 K) (a : Fin Tag.E6.rank → Kˣ) {x : MulAut (adjointGroup .E6 K)}
    (hx : x ∈ (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range ⊔
      (AutSt.e6DiagHom K).range)
    (hxα : x * (MulAut.conj g * exactNormalAut .E6 K a 1 1) =
      (MulAut.conj g * exactNormalAut .E6 K a 1 1) * x) :
    x ∈ (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range := by
  have hN := AutSt.normal_range_conj (S := adjointGroup .E6 K)
  obtain ⟨_, ⟨c, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ := (Subgroup.mem_sup_of_normal_left (hs := hN)).mp hx
  rw [exactNormalAut_graph_eq_e6DiagHom_mul] at hxα
  exact mem_of_commute_diag_graph (AutSt.e6DiagHom K) (e6Rho K) (e6Graph K)
    e6Graph_conj_e6DiagHom
    (fun b => e6DiagHom_mem_inn_of_mem_torusSubgroup (e6Rho_mul_mem_torusSubgroup b))
    (fun b => e6DiagHom_mem_inn_of_mem_torusSubgroup (TableBExc.pow_three_mem_torusSubgroup_E6 b))
    ⟨c, rfl⟩ ⟨g, rfl⟩ hxα

end E6

section Twisted


theorem twistedE6_mem_inn_of_mem_innDiag_of_commute {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {α x : MulAut (twistedE6RootGroup K σ)} (hα2 : α * α = 1)
    (hαI : α ∉ twistedE6Inn K σ ⊔ twistedE6Diag K σ)
    (hx : x ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ) (hxα : x * α = α * x) :
    x ∈ twistedE6Inn K σ := by
  rw [← CFSG.HardMathSupport.Timmesfeld.CrossChar.range_twistedE6InndiagConj] at hαI hx
  exact TwE6OuterGen.mem_range_conj_of_commute_outer hf hK σ hσ (by rw [pow_two]; exact hα2)
    hαI hx hxα.symm

end Twisted

end CFSG.StandardType
