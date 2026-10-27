module

public import CFSG.RankThree.PartOne.TCX.Ree.Regular
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.KLR.SectorOrder

public section

namespace CFSG.RankThree.PartOne.TCX.Ree

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.RF4
  CFSG.RankThree.PartOne.TCX
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Order

theorem orderOf_conj_theta {C : Type} [Group C] {τ : Tag} {L : Type} [Field L]
    {θ : C →* ModGL τ L} (hθ : Function.Injective θ) (g₀ : ModGL τ L) (c x : C) :
    orderOf (g₀⁻¹ * θ (c * x * c⁻¹) * g₀) = orderOf x := by
  have e1 : orderOf (g₀⁻¹ * θ (c * x * c⁻¹) * g₀) = orderOf (θ (c * x * c⁻¹)) := by
    have := orderOf_injective (MulAut.conj g₀⁻¹).toMonoidHom (MulAut.conj g₀⁻¹).injective
      (θ (c * x * c⁻¹))
    simpa [MulAut.conj_apply] using this
  have e2 : orderOf (θ (c * x * c⁻¹)) = orderOf (c * x * c⁻¹) := orderOf_injective θ hθ _
  have e3 : orderOf (c * x * c⁻¹) = orderOf x := by
    have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x
    simpa [MulAut.conj_apply] using this
  rw [e1, e2, e3]

end Order

section Def

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

@[expose] def SectorConclusion
    (p : ℕ) (α₀ : MulAut (ReeTag.F4.reeGamma K a)) (x : ReeTag.F4.reeGamma K a) : Prop :=
  SingleLayerData p α₀ (Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a))) ∨
    ((∀ y ∈ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)),
        ∀ z ∈ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)), y * z = z * y) ∧
      ∀ S : Subgroup (ReeTag.F4.reeGamma K a), S ≠ ⊥ → IsPGroup 2 ↥S →
        x ∈ Subgroup.normalizer (S : Set (ReeTag.F4.reeGamma K a)) → False)

end Def

section Sector

variable {K₀ K : Type} [Field K₀] [Finite K₀] [CharP K₀ ReeTag.F4.prime]
  [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a₀ a : ℕ} {L : Type} [Field L]
  [Algebra K₀ L] [Algebra K L] [CharP L 2] [IsAlgClosed L] [IsAlgClosure K L]
  [IsAlgClosure K₀ L] (D₀ : ReeFrameData K₀ L a₀) (D : ReeFrameData K L a)
  {α₀ : MulAut (ReeTag.F4.reeGamma K a)} {p : ℕ}

theorem ree_sector (hp : p.Prime) (hp5 : 5 ≤ p) (hK₀ : Nat.card K₀ = 2 ^ (2 * a₀ + 1))
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (hKK : 2 * a + 1 = p * (2 * a₀ + 1))
    (h : IsReeShintani p (thetaGamma L a) D₀.F D.F α₀) (w₀ : WeylGroup ReeTag.F4.tag)
    (E₀ : Subgroup (ModGL ReeTag.F4.tag L)) (hEH : E₀ ≤ torusGroup ReeTag.F4.tag L)
    (hEF : E₀ ≤ twistedFixed D₀.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w₀)) (m₀ : ℕ)
    (hE : Nat.card E₀ = m₀ ^ 2)
    (hpm : p ^ (Nat.card (ReeTag.F4.reeGamma K₀ a₀)).factorization p ∣ m₀ ^ 2)
    (hneg : NegAct (w₀ * ReeTag.F4.weylPerm w₀)) {x : ReeTag.F4.reeGamma K a}
    (hx : orderOf x = p) (hxα : α₀ x = x) : SectorConclusion p α₀ x := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 < p := by omega
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have ha : 1 ≤ a := by
    have h1 : 5 * 1 ≤ p * (2 * a₀ + 1) := Nat.mul_le_mul hp5 (by omega)
    omega
  obtain ⟨g₀, hg₀C, hFg₀, hconj⟩ := sector_hconj D₀ w₀ E₀ hEH hEF m₀ hE hp hpm
  set n₀ := canonicalRep (coxeterSystem ReeTag.F4.tag) L w₀ with hn₀
  have hn₀C : n₀ ∈ adjointGroup ReeTag.F4.tag L := canonicalRep_mem_adjointGroup _ L w₀
  have hfixx : Fext D₀.F (thetaGamma L a x) = thetaGamma L a x := by
    rw [← h.actor, hxα]
  obtain ⟨x₀, hx₀⟩ := D₀.exists_theta_of_fixed (thetaGamma_mem_adjointGroup L x) hfixx
  have hx₀ord : orderOf x₀ = p := by
    rw [← orderOf_injective (thetaGamma L a₀) (thetaGamma_injective L) x₀, hx₀,
      orderOf_injective (thetaGamma L a) h.inj x, hx]
  obtain ⟨c₀, hc₀⟩ := hconj x₀ hx₀ord
  have hfixc₀ : Fext D.F (thetaGamma L a₀ c₀) = thetaGamma L a₀ c₀ := by
    rw [h.iter, Fext_pow_eq_iterate D₀.F (thetaGamma_mem_adjointGroup L c₀)]
    exact Function.iterate_fixed (D₀.fext_theta c₀) p
  obtain ⟨c, hc⟩ := h.range _ (thetaGamma_mem_adjointGroup L c₀) hfixc₀
  have hcα : α₀ c = c := by
    apply h.inj
    rw [h.actor, hc, D₀.fext_theta]
  have hθ : thetaGamma L a (c * x * c⁻¹) = thetaGamma L a₀ (c₀ * x₀ * c₀⁻¹) := by
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hc, hx₀]
  obtain ⟨b, hb₀⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hc₀
  have hb : rootDiagUnit ReeTag.F4.tag b = g₀⁻¹ * thetaGamma L a (c * x * c⁻¹) * g₀ := by
    rw [← hb₀, hθ]
  by_cases hker : rootCharKernel b = ∅
  · right
    have hord : orderOf (rootDiagUnit ReeTag.F4.tag b) = p := by
      rw [hb, orderOf_conj_theta h.inj, hx]
    refine ⟨regular_comm hp hp3 hg₀C hord hb hker, fun S hS hS2 hxS => ?_⟩
    have hNC : nseqF n₀ D₀.F p ∈ adjointGroup ReeTag.F4.tag L := nseqF_mem hn₀C D₀.F p
    have hFg : Fext D.F g₀ = g₀ * nseqF n₀ D₀.F p := fext_lang_norm h.iter hg₀C hn₀C hFg₀
    have hNperm : PermAct (nseqF n₀ D₀.F p) (nseqW w₀ p) :=
      permAct_nseqF D₀.isFrob hn₀C (permAct_canonicalRep w₀) p
    have hneg' : NegAct (nseqW w₀ p * ReeTag.F4.weylPerm (nseqW w₀ p)) := by
      have e : nseqW w₀ p * ReeTag.F4.weylPerm (nseqW w₀ p) =
          (w₀ * ReeTag.F4.weylPerm w₀) ^ p := by
        obtain ⟨m, hm⟩ := id hpodd
        rw [hm]
        exact nseqW_mul_weylPerm w₀ m
      rw [e]
      exact negAct_pow_odd hneg hpodd
    exact regular_no_normalized D ha hK hp hp5 hg₀C hNC hFg hNperm hneg' hx hord hb hker hS hS2
      hxS
  · left
    exact ree_layer_case D₀ D hp hp5 hK₀ hK hKK h hg₀C hFg₀ hx hxα c hcα hb hker

theorem ree_sector_phi2 (hp : p.Prime) (hp5 : 5 ≤ p) (hK₀ : Nat.card K₀ = 2 ^ (2 * a₀ + 1))
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (hKK : 2 * a + 1 = p * (2 * a₀ + 1))
    (h : IsReeShintani p (thetaGamma L a) D₀.F D.F α₀) (hpq : p ∣ 2 ^ (2 * a₀ + 1) + 1)
    {x : ReeTag.F4.reeGamma K a} (hx : orderOf x = p) (hxα : α₀ x = x) :
    SectorConclusion p α₀ x := by
  obtain ⟨E, hEH, hEF, hE⟩ := torus_phi2 D₀.isFrob
  exact ree_sector D₀ D hp hp5 hK₀ hK hKK h wPhi2 E hEH hEF _ hE
    (pow_factorization_card_reeGamma_dvd_phi2 hK₀ hp (by omega) hpq) negAct_wPhi2 hx hxα

theorem ree_sector_phi4 (hp : p.Prime) (hp5 : 5 ≤ p) (hK₀ : Nat.card K₀ = 2 ^ (2 * a₀ + 1))
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (hKK : 2 * a + 1 = p * (2 * a₀ + 1))
    (h : IsReeShintani p (thetaGamma L a) D₀.F D.F α₀)
    (hpq : p ∣ (2 ^ (2 * a₀ + 1)) ^ 2 + 1) {x : ReeTag.F4.reeGamma K a} (hx : orderOf x = p)
    (hxα : α₀ x = x) : SectorConclusion p α₀ x := by
  rcases dvd_phi4_cases hp (by omega) hpq with ⟨hpp, -⟩ | ⟨hpm, -⟩
  · obtain ⟨E, hEH, hEF, hE⟩ := torus_phi4p D₀.isFrob
    exact ree_sector D₀ D hp hp5 hK₀ hK hKK h wPhi4p E hEH hEF _ hE
      (pow_factorization_card_reeGamma_dvd_phi4p hK₀ hp (by omega) hpp) negAct_wPhi4p hx hxα
  · obtain ⟨E, hEH, hEF, hE⟩ := torus_phi4m D₀.isFrob
    exact ree_sector D₀ D hp hp5 hK₀ hK hKK h wPhi4m E hEH hEF _ hE
      (pow_factorization_card_reeGamma_dvd_phi4m hK₀ hp (by omega) hpm) negAct_wPhi4m hx hxα

end Sector

end CFSG.RankThree.PartOne.TCX.Ree
