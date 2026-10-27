module

public import CFSG.LocalAnalysis.UniquenessCase.UCFrontExt
public import CFSG.LocalAnalysis.UniquenessCase.UC22K148Strip
import CFSG.LocalAnalysis.UniquenessCase.UC22K148Vocab
import CFSG.LocalAnalysis.UniquenessCase.UC22K148CaseA1
import CFSG.LocalAnalysis.UniquenessCase.UC22K148CaseA2
import CFSG.LocalAnalysis.UniquenessCase.UC22K148CaseA4
import CFSG.LocalAnalysis.UniquenessCase.UC22K148NoExc
import CFSG.LocalAnalysis.UniquenessCase.UC22K147L2Br
import CFSG.HardMathSupport.U4FF.SmallGL
import CFSG.Mathlib.GroupTheory.PermCommute
import TauCeti.GroupTheory.Perm.FinThree.Basic
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Basis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.Open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
open scoped Matrix

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

theorem natL2_one_of_faithful [Finite G] [Finite V] {H : Subgroup G}
    {N : Submodule (ZMod 2) V} (hN : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H N) (hrank : Module.finrank (ZMod 2) ↥N = 2)
    (hfaith : ∀ h ∈ H, (∀ n ∈ N, ρ h n = n) → h = 1) (hcard : Nat.card ↥H = 6) :
    NatL2 ρ H N ⊥ 1 := by
  have hGL : Nat.card (↥N ≃ₗ[ZMod 2] ↥N) = 6 := by
    rw [CFSG.HardMathSupport.U4FF.card_linearEquiv_eq_prod hrank, Fin.prod_univ_two]
    norm_num
  haveI : Finite (↥N ≃ₗ[ZMod 2] ↥N) := Nat.finite_of_card_ne_zero (by rw [hGL]; norm_num)
  have hinj : Function.Injective (resGL ρ H N hN) := fun x y hxy => by
    have h1 : (x : G)⁻¹ * y = 1 := hfaith _ (mul_mem (inv_mem x.2) y.2) fun n hn => by
      have h2 : ρ (x : G) n = ρ (y : G) n := congrArg (fun f => ((f ⟨n, hn⟩ : ↥N) : V)) hxy
      rw [glRep_mul_apply, ← h2, glRep_inv_apply]
    exact Subtype.ext (inv_mul_eq_one.1 h1)
  have hbij : Function.Bijective (resGL ρ H N hN) :=
    hinj.bijective_of_nat_card_le (by rw [hcard, hGL])
  let β : Module.Basis (Fin 2) (ZMod 2) ↥N := Module.finBasisOfFinrankEq (ZMod 2) ↥N hrank
  have hcoord : ∀ (f : ↥N ≃ₗ[ZMod 2] ↥N) (w : ↥N),
      (β.toGL f : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ β.equivFun w = β.equivFun (f w) := by
    intro f w
    have h1 : (Matrix.GeneralLinearGroup.toLin' β (β.toGL f)).toLinearEquiv w = f w := by
      rw [Module.Basis.toLin'_toGL]
      rfl
    rw [Matrix.GeneralLinearGroup.toLin'_apply] at h1
    apply β.equivFun.symm.injective
    rw [LinearEquiv.symm_apply_apply, Module.Basis.equivFun_symm_apply, ← h1,
      Fintype.linearCombination_apply]
    rfl
  have hSL : StatedSL 2 (ZMod 2) = ⊤ := by
    refine eq_top_iff.2 fun A _ => Subgroup.subset_closure ?_
    show (A : Matrix (Fin 2) (Fin 2) (ZMod 2)).det = 1
    have key : ∀ d : ZMod 2, d ≠ 0 → d = 1 := by decide
    exact key _ ((Matrix.isUnit_iff_isUnit_det _).1 A.isUnit).ne_zero
  let φG : ↥H ≃* ↥(StatedSL 2 (ZMod 2)) := ((MulEquiv.ofBijective _ hbij).trans β.toGL).trans
    (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hSL.symm))
  obtain ⟨Ψ, h0, hker, hsurj, hΨ⟩ := K147L2Br.exists_extend N β.equivFun.toAddEquiv
  refine ⟨ZMod 2, inferInstance, inferInstance, by rw [Nat.card_zmod, pow_one], hN,
    fun _ _ x hx => ?_, bot_le, φG, Ψ, h0, hker, hsurj, fun h x hx => ?_⟩
  · rw [(Submodule.mem_bot _).1 hx, map_zero]
    exact zero_mem _
  · have h1 : Ψ (ρ (h : G) x) = β.equivFun (resGL ρ H N hN h ⟨x, hx⟩) :=
      hΨ ⟨ρ h x, hN h h.2 x hx⟩
    have h2 : Ψ x = β.equivFun ⟨x, hx⟩ := hΨ ⟨x, hx⟩
    rw [h1, h2, ← hcoord]
    rfl

theorem commutator_eq_map_of_mulEquiv {P : Type*} [Group P] {H : Subgroup G} (e : ↥H ≃* P) :
    ⁅H, H⁆ = (commutator P).map (H.subtype.comp e.symm.toMonoidHom) := by
  rw [← Subgroup.map_map,
    TauCeti.Subgroup.map_commutator_eq_commutator (f := e.symm.toMonoidHom) e.symm.surjective,
    Subgroup.map_subtype_commutator]

theorem card_commutator_of_mulEquiv {P : Type*} [Group P] {H : Subgroup G} (e : ↥H ≃* P) :
    Nat.card ↥⁅H, H⁆ = Nat.card ↥(commutator P) := by
  rw [commutator_eq_map_of_mulEquiv e, Subgroup.card_map_of_injective]
  exact fun x y hxy => e.symm.injective (Subtype.ext hxy)

theorem mem_commutator_iff_of_mulEquiv {P : Type*} [Group P] {H : Subgroup G} (e : ↥H ≃* P)
    {x : G} (hx : x ∈ H) : x ∈ ⁅H, H⁆ ↔ e ⟨x, hx⟩ ∈ commutator P := by
  rw [commutator_eq_map_of_mulEquiv e, Subgroup.mem_map]
  constructor
  · rintro ⟨σ, hσ, hσx⟩
    have h1 : e.symm σ = ⟨x, hx⟩ := Subtype.ext hσx
    rwa [← h1, MulEquiv.apply_symm_apply]
  · intro h
    refine ⟨e ⟨x, hx⟩, h, ?_⟩
    show ((e.symm (e ⟨x, hx⟩) : ↥H) : G) = x
    rw [MulEquiv.symm_apply_apply]

theorem apply_eq_self_of_commute_of_faithful {H : Subgroup G} {N : Submodule (ZMod 2) V}
    (hNH : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H N) (hfaith : ∀ h ∈ H, (∀ n ∈ N, ρ h n = n) → h = 1)
    (hZ : Subgroup.center ↥H = ⊥) {c y : G} (hc : ∀ x ∈ H, c * x = x * c) (hy : y ∈ H)
    (hcy : ∀ n ∈ N, ρ c n = ρ y n) : ∀ n ∈ N, ρ c n = n := by
  have hyc : ∀ z ∈ H, y * z = z * y := fun z hz => by
    have h1 : (z * y)⁻¹ * (y * z) = 1 :=
      hfaith _ (mul_mem (inv_mem (mul_mem hz hy)) (mul_mem hy hz)) fun n hn => by
        rw [glRep_mul_apply, glRep_mul_apply ρ y z, ← hcy _ (hNH z hz n hn),
          ← glRep_mul_apply ρ c z, hc z hz, glRep_mul_apply ρ z c, hcy n hn,
          ← glRep_mul_apply ρ z y, glRep_inv_apply]
    exact (inv_mul_eq_one.1 h1).symm
  have h1 : (⟨y, hy⟩ : ↥H) ∈ Subgroup.center ↥H :=
    Subgroup.mem_center_iff.2 fun z => Subtype.ext (hyc z z.2).symm
  rw [hZ, Subgroup.mem_bot] at h1
  have hy1 : y = 1 := congrArg Subtype.val h1
  intro n hn
  rw [hcy n hn, hy1, map_one]
  rfl

theorem commOn_commOn_eq_of_isCompl {X : Subgroup G}
    (hc : IsCompl (commOn ρ X ⊤) (fixSub ρ X)) :
    commOn ρ X (commOn ρ X ⊤) = commOn ρ X ⊤ := by
  refine le_antisymm (commOn_mono_right le_top) (Submodule.span_le.2 ?_)
  rintro _ ⟨x, hx, v, -, rfl⟩
  have hv : v ∈ commOn ρ X ⊤ ⊔ fixSub ρ X := by
    rw [hc.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨n, hn, w, hw, rfl⟩ := Submodule.mem_sup.1 hv
  have h : ρ x (n + w) - (n + w) = ρ x n - n := by
    rw [map_add, mem_fixSub.1 hw x hx]
    abel
  rw [SetLike.mem_coe, h]
  exact sub_mem_commOn hx hn

private theorem perm_three_conj_eq_inv : ∀ σ τ : Equiv.Perm (Fin 3),
    Equiv.Perm.sign σ ≠ 1 → Equiv.Perm.sign τ = 1 → σ * τ * σ⁻¹ = τ⁻¹ := by
  decide

theorem factorData_of_mulEquiv_perm_three [Finite G] [Finite V] (hρ : Function.Injective ρ)
    (hH : hP ρ = ⊤) {H : Subgroup G} (hHN : H.Normal) (e : ↥H ≃* Equiv.Perm (Fin 3)) :
    (∀ c : G, (∀ x ∈ H, c * x = x * c) → ∀ n ∈ commOn ρ ⁅H, H⁆ ⊤, ρ c n = n) ∧
      (∀ h ∈ H, (∀ n ∈ commOn ρ ⁅H, H⁆ ⊤, ρ h n = n) → h = 1) ∧
      IsCompl (commOn ρ ⁅H, H⁆ ⊤) (fixSub ρ ⁅H, H⁆) ∧
      (∀ X : Subgroup G, CFSG.Open.IsElemAbelian 2 X → NoExcess ρ X (commOn ρ ⁅H, H⁆ ⊤)) ∧
      Shape148 ρ H (commOn ρ ⁅H, H⁆ ⊤) (fixSub ρ H) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmem : ∀ x (hx : x ∈ H), x ∈ ⁅H, H⁆ ↔ Equiv.Perm.sign (e ⟨x, hx⟩) = 1 := fun x hx => by
    rw [mem_commutator_iff_of_mulEquiv e hx,
      TauCeti.commutator_perm_fin_three_eq_alternatingGroup, Equiv.Perm.mem_alternatingGroup]
  have hQ3 : Nat.card ↥⁅H, H⁆ = 3 := by
    rw [card_commutator_of_mulEquiv e, TauCeti.commutator_perm_fin_three_eq_alternatingGroup,
      TauCeti.card_alternatingGroup_fin_three]
  have hQN : (⁅H, H⁆ : Subgroup G).Normal := by
    haveI := hHN
    infer_instance
  have hQH : ⁅H, H⁆ ≤ H := Subgroup.commutator_le_self H
  obtain ⟨Q, hQ⟩ : ∃ Q : Subgroup G, ⁅H, H⁆ = Q := ⟨_, rfl⟩
  rw [hQ] at hmem hQ3 hQN hQH ⊢
  have hH6 : Nat.card ↥H = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hnorm : ∀ g : G, g ∈ Subgroup.normalizer (Q : Set G) := fun g => by
    rw [Subgroup.normalizer_eq_top_iff.2 hQN]
    exact Subgroup.mem_top g
  have hinv : ∀ b ∈ H, b ∉ Q → ∀ x ∈ Q, b * x * b⁻¹ = x⁻¹ := fun b hb hbQ x hx => by
    have h1 := perm_three_conj_eq_inv (e ⟨b, hb⟩) (e ⟨x, hQH hx⟩)
      (fun h => hbQ ((hmem b hb).2 h)) ((hmem x (hQH hx)).1 hx)
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv] at h1
    exact congrArg Subtype.val (e.injective h1)
  have hZ : Subgroup.center ↥H = ⊥ := by
    refine eq_bot_iff.2 fun z hz => Subgroup.mem_bot.2 (e.injective ?_)
    rw [map_one]
    refine CFSG.perm_eq_one_of_forall_commute (by simp) fun τ => ?_
    obtain ⟨w, rfl⟩ := e.surjective τ
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz w]
  obtain ⟨b, hbH, hbQ⟩ : ∃ b ∈ H, b ∉ Q := SetLike.exists_of_lt (lt_of_le_of_ne hQH fun h => by
    rw [h] at hQ3
    omega)
  obtain ⟨x, hxQ, hx1⟩ := (Subgroup.bot_or_exists_ne_one Q).resolve_left fun h => by
    rw [h, Subgroup.card_bot] at hQ3
    omega
  have hbx : b * x ≠ x * b := fun h => by
    have h1 : x⁻¹ = x := by rw [← hinv b hbH hbQ x hxQ, h, mul_inv_cancel_right]
    have h2 : orderOf x ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact mul_eq_one_iff_eq_inv.2 h1.symm)
    have h3 : orderOf x ∣ 3 := hQ3 ▸ Subgroup.orderOf_dvd_natCard Q hxQ
    have h4 : orderOf x ∣ 1 := Nat.dvd_gcd h2 h3
    exact hx1 (orderOf_eq_one_iff.1 (Nat.dvd_one.1 h4))
  obtain ⟨A, hA, hQA⟩ : ∃ A ∈ calP ρ, ⁅Q, A⁆ ≠ ⊥ := by
    by_contra hne
    have hle : hP ρ ≤ Subgroup.centralizer (Q : Set G) := iSup₂_le fun A hA => by
      have h : ⁅Q, A⁆ = ⊥ := Classical.byContradiction fun h => hne ⟨A, hA, h⟩
      rwa [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    rw [hH] at hle
    exact hbx (Subgroup.mem_centralizer_iff.1 (hle (Subgroup.mem_top b)) x hxQ).symm
  obtain ⟨b', -, hX3, hXV, hXQ, -, -⟩ := exists_Q_of_moving hρ
    (IsPGroup.of_card (p := 3) (n := 1) (by rw [hQ3, pow_one])).isNilpotent
    (by rw [hQ3]; decide) (isElementaryAbelian_of_mem_calP hA) (fun a _ => hnorm a) hQA
    (isBestOffenderOn_of_mem_calP hρ hA)
  have hQV : Module.finrank (ZMod 2) ↥(commOn ρ Q ⊤) = 2 := by
    rw [← Subgroup.eq_of_le_of_card_ge hXQ (by rw [hQ3, hX3])]
    exact hXV
  have hcompl : IsCompl (commOn ρ Q ⊤) (fixSub ρ Q) :=
    isCompl_commOn_fixSub_of_odd (by rw [hQ3]; decide)
  have hNH : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H (commOn ρ Q ⊤) :=
    (invariant_commOn_top (A := H) fun g _ => hnorm g).2
  have hfaith : ∀ h ∈ H, (∀ n ∈ commOn ρ Q ⊤, ρ h n = n) → h = 1 := fun h hh hN => by
    by_cases hhQ : h ∈ Q
    · exact eq_one_of_fixes_commOn hρ hhQ
        (Odd.of_dvd_nat (by decide) (hQ3 ▸ Subgroup.orderOf_dvd_natCard Q hhQ)) hN
    · refine absurd (fun u hu => ?_)
        (not_forall_apply_eq_of_inverts hρ hQ3 (hinv h hh hhQ) Q.one_mem)
      rw [hN u hu, map_one]
      rfl
  have hF0 : ∀ c : G, (∀ x ∈ H, c * x = x * c) → ∀ n ∈ commOn ρ Q ⊤, ρ c n = n := by
    intro c hc
    obtain ⟨y, hy, hcy⟩ :=
      exists_eq_apply_of_card_three hρ hQ3 hQV (hinv b hbH hbQ) (hnorm b) (hnorm c)
    exact apply_eq_self_of_commute_of_faithful hNH hfaith hZ hc
      (sup_le hQH (Subgroup.zpowers_le.2 hbH) hy) hcy
  have hinf : commOn ρ Q ⊤ ⊓ fixSub ρ H = ⊥ := by
    refine eq_bot_iff.2 fun v hv => ?_
    have hv' : v ∈ commOn ρ Q ⊤ ⊓ fixSub ρ Q := Submodule.mem_inf.2
      ⟨(Submodule.mem_inf.1 hv).1,
        mem_fixSub.2 fun q hq => mem_fixSub.1 (Submodule.mem_inf.1 hv).2 q (hQH hq)⟩
    rwa [hcompl.inf_eq_bot] at hv'
  refine ⟨hF0, hfaith, hcompl, fun X hX => noExcess_of_finrank_two hQV hX
    (invariant_commOn_top (A := X) fun g _ => hnorm g).2, Or.inl ⟨1, le_rfl, ?_⟩⟩
  rw [hinf]
  exact natL2_one_of_faithful hNH hQV hfaith hH6

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
