module

public import CFSG.Quasithin.Background.FFC4Pair
public import CFSG.LinearAlgebra.SteinbergBQEvenSL2OddCyclic

public section

namespace CFSG.Quasithin

namespace B69

open CFSG.Assembly.LowTwoRank in
theorem nontrivial_statedSL_two {K : Type} [Field K] : Nontrivial ↥(StatedSL 2 K) := by
  have : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) K) := by
    refine ⟨⟨⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩, 1, fun h => ?_⟩⟩
    have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) K =>
      (g : Matrix (Fin 2) (Fin 2) K) 0 1) h
    simp at this
  exact (specialLinearGroupEquivStatedSL 2 K).injective.nontrivial

open CFSG.Assembly.LowTwoRank in
theorem noOddCoverSL2 (L H : Type) [Group L] [Group H] [Finite L] (hL : CFSG.Open.IsQuasisimple L)
    (f : L →* H) (hf : Function.Surjective f) (hodd : ∀ x ∈ f.ker, Odd (orderOf x))
    (hH : ∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (H ≃* ↥(StatedSL 2 K))) : Function.Injective f := by
  classical
  obtain ⟨n, K, hKf, hKfin, hK, ⟨e⟩⟩ := hH
  have : CharP K 2 := FFC.charP_two_of_card_pow hK
  have hperf : commutator L = ⊤ := hL.1
  have : Nontrivial ↥(StatedSL 2 K) := nontrivial_statedSL_two
  have hHnt : Nontrivial H := e.symm.injective.nontrivial
  rw [injective_iff_map_eq_one]
  intro x hx
  by_contra hx1
  have hne : f.ker ≠ ⊤ := by
    intro htop
    obtain ⟨a, b, hab⟩ := hHnt.exists_pair_ne
    obtain ⟨u, rfl⟩ := hf a
    obtain ⟨v, rfl⟩ := hf b
    apply hab
    have hu : u ∈ f.ker := by rw [htop]; trivial
    have hv : v ∈ f.ker := by rw [htop]; trivial
    rw [MonoidHom.mem_ker.mp hu, MonoidHom.mem_ker.mp hv]
  have hcent : f.ker ≤ Subgroup.center L :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hL f.ker hne
  have hxk : x ∈ f.ker := hx
  have hord1 : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.1 h)
  set p := (orderOf x).minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime hord1
  have hpx : p ∣ orderOf x := Nat.minFac_dvd _
  have hp2 : p ≠ 2 := by
    intro h2
    rw [h2] at hpx
    exact (Nat.not_even_iff_odd.2 (hodd x hxk)) (even_iff_two_dvd.2 hpx)
  have : Fact p.Prime := ⟨hp⟩
  have hne0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
  set z : L := x ^ (orderOf x / p) with hzdef
  have hzord : orderOf z = p := orderOf_pow_orderOf_div hne0 hpx
  have hzk : z ∈ f.ker := Subgroup.pow_mem _ hxk _
  have hzc : z ∈ Subgroup.center L := hcent hzk
  have hz1 : z ≠ 1 := fun h => hp.one_lt.ne' (by rw [← hzord, h, orderOf_one])
  have hzp : IsPGroup p (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzord, pow_one])
  obtain ⟨P, hzP⟩ := hzp.exists_le_sylow
  have hzP' : z ∈ (P : Subgroup L) := hzP (Subgroup.mem_zpowers z)
  let g : L →* Matrix.SpecialLinearGroup (Fin 2) K :=
    ((specialLinearGroupEquivStatedSL 2 K).symm.toMonoidHom).comp (e.toMonoidHom.comp f)
  have hginj : ∀ u : L, g u = 1 → f u = 1 := by
    intro u hu
    have h1 : e (f u) = 1 := (MulEquiv.map_eq_one_iff (specialLinearGroupEquivStatedSL 2 K).symm).1 hu
    exact (MulEquiv.map_eq_one_iff e).1 h1
  have hcyc : IsCyclic ↥((P : Subgroup L).map g) :=
    CFSG.LinearAlgebra.even_SL2_odd_prime_subgroups_cyclic hp2 _ (P.isPGroup'.map g)
  have hker : (g.subgroupMap (P : Subgroup L)).ker ≤ Subgroup.center ↥(P : Subgroup L) := by
    intro u hu
    rw [Subgroup.mem_center_iff]
    intro w
    have h1 : g (u : L) = 1 := by
      have := (MonoidHom.mem_ker).1 hu
      exact congrArg Subtype.val this
    have h2 : (u : L) ∈ Subgroup.center L := hcent (MonoidHom.mem_ker.2 (hginj _ h1))
    exact Subtype.ext ((Subgroup.mem_center_iff.1 h2) (w : L))
  have hPcomm : IsMulCommutative ↥(P : Subgroup L) :=
    MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center (g.subgroupMap (P : Subgroup L)) hker
  have hab : ∀ a b : ↥(P : Subgroup L), a * b = b * a := fun a b => hPcomm.is_comm.comm a b
  have hindex : Nat.Coprime p (P : Subgroup L).index :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 P.not_dvd_index
  have hbot : ((⊥ : Subgroup L).subgroupOf (P : Subgroup L)).Normal := by
    rw [Subgroup.bot_subgroupOf]
    infer_instance
  have hcomm : ⁅(P : Subgroup L), (P : Subgroup L)⁆ ≤ ⊥ := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have := hab ⟨a, ha⟩ ⟨b, hb⟩
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact congrArg Subtype.val this
  have hnot := generalized_thompson_transfer_one (G := L) (p := p) (H := (P : Subgroup L)) (K := ⊥)
    hindex ⟨bot_le, hbot⟩ hcomm hzP' (by simpa using hz1) ⟨1, by rw [pow_one, ← hzord, pow_orderOf_eq_one]⟩
    (fun m a _ => by
      have hzm : z ^ m ∈ Subgroup.center L := Subgroup.zpow_mem _ hzc m
      have h1 : a⁻¹ * z ^ m * a = z ^ m := by
        have := (Subgroup.mem_center_iff.1 hzm) a⁻¹
        rw [this, mul_assoc, inv_mul_cancel, mul_one]
      rw [h1, inv_mul_cancel]
      exact Subgroup.one_mem _)
  exact hnot (by rw [hperf]; trivial)

end B69

end CFSG.Quasithin
