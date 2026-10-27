module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddL3AutClass
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IR
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IS

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.L3I

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
  Module CFSG.Quasithin.E2P.Asc80
open scoped MatrixGroups

variable {G : Type} [Group G]

theorem mem_of_congr_eq_conj {L : Subgroup G} [L.Normal]
    (hC : Subgroup.centralizer (L : Set G) = ⊥) {X : Type} [Group X] (ψ : ↥L ≃* X) {t : G}
    {g' : X} (h : MulAut.congr ψ (MulAut.conjNormal t) = MulAut.conj g') : t ∈ L := by
  set l₀ : ↥L := ψ.symm g' with hl₀
  have hσx : ∀ x : ↥L, MulAut.conjNormal t x = l₀ * x * l₀⁻¹ := by
    intro x
    have h1 : ψ (MulAut.conjNormal t x) = MulAut.congr ψ (MulAut.conjNormal t) (ψ x) := by
      simp [MulAut.congr_apply]
    rw [h, MulAut.conj_apply] at h1
    apply ψ.injective
    rw [h1, map_mul, map_mul, map_inv, hl₀, MulEquiv.apply_symm_apply]
  have hc : (l₀ : G)⁻¹ * t ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg Subtype.val (hσx ⟨x, hx⟩)
    rw [MulAut.conjNormal_apply] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    calc x * ((l₀ : G)⁻¹ * t) = (l₀ : G)⁻¹ * ((l₀ : G) * x * (l₀ : G)⁻¹) * t := by group
      _ = (l₀ : G)⁻¹ * (t * x * t⁻¹) * t := by rw [h1]
      _ = (l₀ : G)⁻¹ * t * x := by group
  rw [hC, Subgroup.mem_bot] at hc
  have ht : t = l₀ := by
    calc t = (l₀ : G) * ((l₀ : G)⁻¹ * t) := by group
      _ = l₀ := by rw [hc, mul_one]
  rw [ht]
  exact l₀.2

variable {p : ℕ} [Fact p.Prime]

theorem exists_graph_of_outer (hp2 : p ≠ 2) {L : Subgroup G} [L.Normal]
    (hC : Subgroup.centralizer (L : Set G) = ⊥) (e : ↥L ≃* PSL3 p) {b : G} (hbL : b ∉ L)
    (hb2 : orderOf b = 2) :
    ∃ A : GL (Fin 3) (ZMod p), (A : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ = A ∧
      MulAut.congr (e.trans (psl3EquivP p)) (MulAut.conjNormal b) =
        LinearFlag.conjAut 3 (ZMod p) A * LinearFlag.dualAut 3 (ZMod p) := by
  set ψ := e.trans (psl3EquivP p) with hψ
  set β := MulAut.congr ψ (MulAut.conjNormal b) with hβ
  have hbb : b ^ 2 = 1 := by rw [← hb2, pow_orderOf_eq_one]
  have hβ2 : β * β = 1 := by
    rw [hβ, ← map_mul, ← map_mul, ← pow_two, hbb, map_one, map_one]
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h1 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h1)
  rcases CFSG.QuasithinUnique.Ch1.classify_involution (Nat.card_zmod p) h2 β hβ2 with
    ⟨g, hg⟩ | ⟨A, hA, hβA⟩
  · exfalso
    apply hbL
    refine mem_of_congr_eq_conj hC ψ (g' := g⁻¹) ?_
    ext x
    rw [hg, MulAut.conj_apply, inv_inv]
  · exact ⟨A, hA, hβA⟩

theorem outer_pair_L3 (hp2 : p ≠ 2) {L : Subgroup G} [L.Normal]
    (hC : Subgroup.centralizer (L : Set G) = ⊥) (e : ↥L ≃* PSL3 p) {t₁ t₂ : G} (h₁ : t₁ ∉ L)
    (h₂ : t₂ ∉ L) (o₁ : orderOf t₁ = 2) (o₂ : orderOf t₂ = 2) (hc : t₁ * t₂ = t₂ * t₁) :
    t₁ * t₂ ∈ L := by
  obtain ⟨A₁, -, hA₁⟩ := exists_graph_of_outer hp2 hC e h₁ o₁
  obtain ⟨A₂, -, hA₂⟩ := exists_graph_of_outer hp2 hC e h₂ o₂
  set ψ := e.trans (psl3EquivP p) with hψ
  obtain ⟨-, -, -, -, hδc, -⟩ := standard_automorphism_transport (n := 3) (K := ZMod p)
  have hprod : MulAut.congr ψ (MulAut.conjNormal (t₁ * t₂)) =
      LinearFlag.conjAut 3 (ZMod p) (A₁ * GeneralLinearGroup.inverseTranspose A₂) := by
    rw [map_mul, map_mul, hA₁, hA₂, map_mul, ← hδc]
    group
  have hsq : (LinearFlag.conjAut 3 (ZMod p) (A₁ * GeneralLinearGroup.inverseTranspose A₂)) ^
      (2 ^ 1) = MulAut.conj 1 := by
    have htt : (t₁ * t₂) ^ 2 = 1 := by
      have h1 : t₁ ^ 2 = 1 := by rw [← o₁, pow_orderOf_eq_one]
      have h2' : t₂ ^ 2 = 1 := by rw [← o₂, pow_orderOf_eq_one]
      rw [(Commute.mul_pow hc 2), h1, h2', one_mul]
    rw [← hprod, ← map_pow, ← map_pow, pow_one, htt, map_one, map_one, map_one]
  obtain ⟨g', hg'⟩ := conjAut_inner_of_pow_inner _ hsq
  exact mem_of_congr_eq_conj hC ψ (hprod.trans hg')

end CFSG.Quasithin.Vol2.Ch11.SecU1.L3I
