module

public import CFSG.Quasithin.Vol2.Ch11SecAKM2
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA.C10KH

open CFSG.Open CFSG.Blueprint

theorem rho_eq_one_of_mem_nilpotent {K₀ W : Type*} [Group K₀] [Finite K₀] [Group W] [Finite W]
    (hperf : ⁅(⊤ : Subgroup K₀), (⊤ : Subgroup K₀)⁆ = ⊤) (ρ : K₀ →* MulAut W)
    {F : Subgroup (K₀ ⧸ CFSG.pCore 2 K₀)} (hFn : F.Normal) (hFnil : Group.IsNilpotent F)
    (hFq : ∀ q : ℕ, q.Prime → q ∣ Nat.card F → ¬ q ^ 2 ∣ Nat.card (MulAut W))
    {y : K₀} (hy : (y : K₀ ⧸ CFSG.pCore 2 K₀) ∈ F) (hodd : Odd (orderOf y)) : ρ y = 1 := by
  classical
  set O := CFSG.pCore 2 K₀ with hO
  have : Finite (MulAut W) := Finite.of_injective (fun a : MulAut W => a.toEquiv)
    (fun a b h => MulEquiv.ext fun x => congrArg (fun e : W ≃ W => e x) h)
  by_contra hne
  have hm1 : orderOf (ρ y) ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
  have : Fact p.Prime := ⟨hp⟩
  have hmy : orderOf (ρ y) ∣ orderOf y := orderOf_map_dvd ρ y
  have hpodd : Odd p := Odd.of_dvd_nat hodd (hpm.trans hmy)
  have hm0 : orderOf (ρ y) ≠ 0 := (orderOf_pos (ρ y)).ne'
  obtain ⟨z, hz⟩ : ∃ z, z = y ^ (orderOf (ρ y) / p) := ⟨_, rfl⟩
  have hρz : orderOf (ρ z) = p := by
    rw [hz, map_pow]
    exact orderOf_pow_orderOf_div hm0 hpm
  have hzF : (z : K₀ ⧸ O) ∈ F := by
    rw [hz, QuotientGroup.mk_pow]
    exact F.pow_mem hy _
  have hzodd : Odd (orderOf z) := by
    rw [hz]
    exact Odd.of_dvd_nat hodd (orderOf_pow_dvd _)
  have hpF : p ∣ Nat.card F := by
    have h1 : z ^ Nat.card F ∈ O := by
      have h0 : ((⟨(z : K₀ ⧸ O), hzF⟩ : F) ^ Nat.card F) = 1 := pow_card_eq_one'
      have h2 : ((z ^ Nat.card F : K₀) : K₀ ⧸ O) = 1 := by
        rw [QuotientGroup.mk_pow]
        exact congrArg Subtype.val h0
      exact (QuotientGroup.eq_one_iff _).mp h2
    have h3 : z ^ Nat.card F = 1 :=
      eq_one_of_isPGroup_of_odd CFSG.pCore_isPGroup h1
        (Odd.of_dvd_nat hzodd (orderOf_pow_dvd _))
    exact (hρz ▸ orderOf_map_dvd ρ z).trans (orderOf_dvd_of_pow_eq_one h3)
  have hpW := hFq p hp hpF
  have hMn : (ρ.ker ⊔ O).Normal := Subgroup.sup_normal _ _
  have hG : Nat.card (K₀ ⧸ (ρ.ker ⊔ O)) ∣ Nat.card (MulAut W) :=
    (Subgroup.index_dvd_of_le le_sup_left).trans
      ((Subgroup.index_ker ρ).symm ▸ Subgroup.card_subgroup_dvd_card _)
  have hpG : ¬ p ^ 2 ∣ Nat.card (K₀ ⧸ (ρ.ker ⊔ O)) := fun h => hpW (h.trans hG)
  have hperfG := perfect_quotient hperf (ρ.ker ⊔ O)
  have hzb1 : (z : K₀ ⧸ (ρ.ker ⊔ O)) ≠ 1 := by
    intro h
    have hzM : z ∈ ρ.ker ⊔ O := (QuotientGroup.eq_one_iff z).mp h
    have hmap : (ρ.ker ⊔ O).map ρ = O.map ρ := by
      rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff ρ.ker).mpr le_rfl, bot_sup_eq]
    have hz2 : ρ z ∈ O.map ρ := hmap ▸ Subgroup.mem_map_of_mem ρ hzM
    have h2 := eq_one_of_isPGroup_of_odd ((CFSG.pCore_isPGroup (p := 2) (G := K₀)).map ρ) hz2
      (by rw [hρz]; exact hpodd)
    rw [h2, orderOf_one] at hρz
    exact hp.one_lt.ne' hρz.symm
  have hzbp : (z : K₀ ⧸ (ρ.ker ⊔ O)) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    apply Subgroup.mem_sup_left
    rw [MonoidHom.mem_ker, map_pow, ← hρz, pow_orderOf_eq_one]
  have hzbo : orderOf (z : K₀ ⧸ (ρ.ker ⊔ O)) = p := orderOf_eq_prime hzbp hzb1
  let ψ : (K₀ ⧸ O) →* (K₀ ⧸ (ρ.ker ⊔ O)) :=
    QuotientGroup.map O (ρ.ker ⊔ O) (MonoidHom.id K₀) fun x hx => Subgroup.mem_sup_right hx
  have hψ : Function.Surjective ψ := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x => exact ⟨(x : K₀ ⧸ O), rfl⟩
  have hYn : (F.map ψ).Normal := hFn.map ψ hψ
  have hYnil : Group.IsNilpotent (F.map ψ) :=
    Group.nilpotent_of_surjective (ψ.subgroupMap F) (ψ.subgroupMap_surjective F)
  have hzbY : (z : K₀ ⧸ (ρ.ker ⊔ O)) ∈ F.map ψ := ⟨(z : K₀ ⧸ O), hzF, rfl⟩
  have hzbP : (z : K₀ ⧸ (ρ.ker ⊔ O)) ∈ CFSG.pCore p (K₀ ⧸ (ρ.ker ⊔ O)) := by
    have hpz : IsPGroup p (Subgroup.zpowers (⟨_, hzbY⟩ : F.map ψ)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hzbo, pow_one])
    obtain ⟨P, hP⟩ := hpz.exists_le_sylow
    exact Sylow.map_le_pCore hYn hYnil p P ⟨_, hP (Subgroup.mem_zpowers _), rfl⟩
  set P := CFSG.pCore p (K₀ ⧸ (ρ.ker ⊔ O)) with hPdef
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := p) (G := K₀ ⧸ (ρ.ker ⊔ O))).exists_card_eq
  have hk1 : k = 1 := by
    have hdvd : p ^ k ∣ Nat.card (K₀ ⧸ (ρ.ker ⊔ O)) := hk ▸ Subgroup.card_subgroup_dvd_card P
    have hk2 : k < 2 := by
      by_contra h
      exact hpG ((Nat.pow_dvd_pow p (by omega)).trans hdvd)
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      have : Subsingleton P := Nat.card_eq_one_iff_unique.mp hk |>.1
      exact hzb1 (congrArg Subtype.val (Subsingleton.elim (⟨_, hzbP⟩ : P) 1))
    omega
  have hPc : IsCyclic P := isCyclic_of_prime_card (by rw [hk, hk1, pow_one])
  have hzbZ : (z : K₀ ⧸ (ρ.ker ⊔ O)) ∈ Subgroup.center (K₀ ⧸ (ρ.ker ⊔ O)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := map_eq_one_of_perfect hperfG (MulAut.conjNormal (H := P))
      (fun a b => mulAut_comm_of_isCyclic _ _) g
    have h2 := congrArg (fun f : MulAut P => ((f ⟨_, hzbP⟩ : P) : K₀ ⧸ (ρ.ker ⊔ O))) h1
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
    calc g * (z : K₀ ⧸ (ρ.ker ⊔ O)) = g * (z : K₀ ⧸ (ρ.ker ⊔ O)) * g⁻¹ * g := by group
      _ = (z : K₀ ⧸ (ρ.ker ⊔ O)) * g := by rw [h2]
  have htr := map_eq_one_of_perfect hperfG (MonoidHom.transferCenterPow (K₀ ⧸ (ρ.ker ⊔ O)))
    (fun a b => Subtype.ext (Subgroup.mem_center_iff.mp
      (MonoidHom.transferCenterPow (K₀ ⧸ (ρ.ker ⊔ O)) b).2 _)) (z : K₀ ⧸ (ρ.ker ⊔ O))
  have h1 : (z : K₀ ⧸ (ρ.ker ⊔ O)) ^ (Subgroup.center (K₀ ⧸ (ρ.ker ⊔ O))).index = 1 := by
    have := congrArg Subtype.val htr
    rwa [MonoidHom.transferCenterPow_apply] at this
  have h2 : p ∣ (Subgroup.center (K₀ ⧸ (ρ.ker ⊔ O))).index :=
    hzbo ▸ orderOf_dvd_of_pow_eq_one h1
  have h3 : p ∣ Nat.card (Subgroup.center (K₀ ⧸ (ρ.ker ⊔ O))) := by
    have := orderOf_dvd_natCard (⟨_, hzbZ⟩ : Subgroup.center (K₀ ⧸ (ρ.ker ⊔ O)))
    rwa [Subgroup.orderOf_mk, hzbo] at this
  apply hpG
  rw [← (Subgroup.center (K₀ ⧸ (ρ.ker ⊔ O))).card_mul_index, sq]
  exact Nat.mul_dvd_mul h3 h2

theorem card_GL6 : Nat.card (Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) = 20158709760 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.SectionRank.Ccomm.card_GL_zmod, Fin.prod_univ_six]
  norm_num

theorem prime_dvd_GL6 {q : ℕ} (hq : q.Prime) (h : q ∣ 20158709760) :
    q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 31 := by
  have hmem : q ∈ Nat.primeFactorsList 20158709760 :=
    (Nat.mem_primeFactorsList (by norm_num)).mpr ⟨hq, h⟩
  simp only [Nat.primeFactorsList_ofNat, List.mem_cons, List.not_mem_nil, or_false] at hmem
  omega

theorem not_sq_dvd_GL6 {q : ℕ} (hq : q.Prime) (h5 : q % 5 = 1 ∨ q % 5 = 4 ∨ q = 5) :
    ¬ q ^ 2 ∣ 20158709760 := by
  intro h
  rcases prime_dvd_GL6 hq ((dvd_pow_self q two_ne_zero).trans h) with rfl | rfl | rfl | rfl | rfl
    <;> revert h h5 <;> decide

theorem not_isQuasisimple_of_gF {X : Type*} [Group X] [Finite X]
    (hgF : CFSG.generalizedFitting X = CFSG.fittingSubgroup X)
    (hne : CFSG.fittingSubgroup X ≠ ⊤) : ¬ CFSG.IsQuasisimple X := by
  intro hq
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq CFSG.fittingSubgroup_normal with h | h
  · exact hne h
  · apply hne
    have hc : Subgroup.centralizer (CFSG.generalizedFitting X : Set X) = ⊤ := by
      rw [hgF, eq_top_iff]
      intro g _
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_center_iff.mp (h hx) g).symm
    have := CFSG.centralizer_generalizedFitting_le X
    rw [hc, hgF] at this
    exact eq_top_iff.mpr this

theorem concl_c {K₀ W : Type} [Group K₀] [Finite K₀] [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W ≤ 2 ^ 6)
    (hperf : ⁅(⊤ : Subgroup K₀), (⊤ : Subgroup K₀)⁆ = ⊤) (ρ : K₀ →* MulAut W)
    (hX : A36Case4 (K₀ ⧸ CFSG.pCore 2 K₀) ∨
      ∃ p : ℕ, p.Prime ∧ (p % 5 = 1 ∨ p % 5 = 4) ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
        CFSG.generalizedFitting (K₀ ⧸ CFSG.pCore 2 K₀) =
          CFSG.fittingSubgroup (K₀ ⧸ CFSG.pCore 2 K₀) ∧
        IsElemAbelianOfRank p 2 ↥(CFSG.fittingSubgroup (K₀ ⧸ CFSG.pCore 2 K₀)) ∧
        NaturalSL2Action p (K₀ ⧸ CFSG.pCore 2 K₀) (CFSG.fittingSubgroup (K₀ ⧸ CFSG.pCore 2 K₀))) :
    ¬ CFSG.IsQuasisimple (K₀ ⧸ CFSG.pCore 2 K₀) ∧
      ∀ y : K₀, (QuotientGroup.mk y : K₀ ⧸ CFSG.pCore 2 K₀) ∈
        CFSG.fittingSubgroup (K₀ ⧸ CFSG.pCore 2 K₀) → Odd (orderOf y) → ρ y = 1 := by
  have hGL := card_mulAut_dvd hW hcard
  rw [card_GL6] at hGL
  obtain ⟨hgF, hne, hq5⟩ : CFSG.generalizedFitting (K₀ ⧸ CFSG.pCore 2 K₀) =
      CFSG.fittingSubgroup (K₀ ⧸ CFSG.pCore 2 K₀) ∧
      CFSG.fittingSubgroup (K₀ ⧸ CFSG.pCore 2 K₀) ≠ ⊤ ∧
      ∀ q : ℕ, q.Prime → q ∣ Nat.card (CFSG.fittingSubgroup (K₀ ⧸ CFSG.pCore 2 K₀)) →
        (q % 5 = 1 ∨ q % 5 = 4 ∨ q = 5) := by
    rcases hX with ⟨hgF, -, hsl, hpr⟩ | ⟨p, hp, h5, -, hgF, hel, hnat⟩
    · refine ⟨hgF, fun htop => ?_, fun q hq hdvd => (hpr q hq hdvd).1⟩
      have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      obtain ⟨e⟩ := (hsl : Nonempty (_ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)))
      have h1 : Nat.card ((K₀ ⧸ CFSG.pCore 2 K₀) ⧸
          CFSG.fittingSubgroup (K₀ ⧸ CFSG.pCore 2 K₀)) = 1 :=
        Subgroup.index_eq_one.mpr htop
      have h2 := CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two (ZMod 5)
      rw [← Nat.card_congr e.toEquiv, h1, Nat.card_zmod] at h2
      norm_num at h2
    · have : Fact p.Prime := ⟨hp⟩
      obtain ⟨eF⟩ := (hel : Nonempty (_ ≃* Multiplicative (Fin 2 → ZMod p)))
      obtain ⟨-, ψ, hψ, hker, -⟩ := hnat
      refine ⟨hgF, fun htop => ?_, fun q hq hdvd => ?_⟩
      · have hall : ∀ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod p), g = 1 := by
          intro g
          obtain ⟨x, rfl⟩ := hψ g
          have hx : x ∈ ψ.ker := by rw [hker, htop]; exact Subgroup.mem_top x
          exact hx
        have : Subsingleton (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
          ⟨fun a b => (hall a).trans (hall b).symm⟩
        have h2 := CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two (ZMod p)
        rw [Nat.card_unique, Nat.card_zmod] at h2
        have hp2 := hp.two_le
        have h4 : 4 ≤ p ^ 2 := by nlinarith
        have h3 : 2 * 3 ≤ p * (p ^ 2 - 1) := Nat.mul_le_mul hp2 (by omega)
        omega
      · have hcF : Nat.card (CFSG.fittingSubgroup (K₀ ⧸ CFSG.pCore 2 K₀)) = p ^ 2 := by
          rw [Nat.card_congr eF.toEquiv]
          simp [Nat.card_eq_fintype_card]
        rw [hcF] at hdvd
        have := (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hdvd)
        subst this
        tauto
  refine ⟨not_isQuasisimple_of_gF hgF hne, fun y hy hodd => ?_⟩
  exact rho_eq_one_of_mem_nilpotent hperf ρ CFSG.fittingSubgroup_normal inferInstance
    (fun q hq hdvd hq2 => not_sq_dvd_GL6 hq (hq5 q hq hdvd) (hq2.trans hGL)) hy hodd

end CFSG.Quasithin.Vol2.Ch11.SecA.C10KH
