module

public import CFSG.Quasithin.H13.A5S1521d

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.InternalSec
open scoped commutatorElement

section Gaschutz

variable {M : Type} [CommGroup M] [Finite M]

theorem map_eq_one_of_mem_commSubOf {K Pg : Subgroup (MulAut M)} (hodd : Odd (Pg.relIndex K))
    {Q : Type} [CommGroup Q] (hQ : ∀ q : Q, q ^ 2 = 1) (φ : M →* Q)
    (hφP : ∀ g ∈ Pg, ∀ m : M, φ (g m) = φ m) {z : M} (hz : ∀ k ∈ K, k z = z)
    (hzc : z ∈ commSubOf ⊤ K) : φ z = 1 := by
  classical
  set Qt := ↥K ⧸ Pg.subgroupOf K
  have : Fintype Qt := Fintype.ofFinite Qt
  let Φ : M →* Q :=
    { toFun := fun m => ∏ q : Qt, φ (((q.out : ↥K) : MulAut M)⁻¹ m)
      map_one' := by simp
      map_mul' := fun a c => by simp only [map_mul, Finset.prod_mul_distrib] }
  have hΦK : ∀ k ∈ K, ∀ m : M, Φ (k m) = Φ m := by
    intro k hk m
    let k' : ↥K := ⟨k, hk⟩
    show ∏ q : Qt, φ (((q.out : ↥K) : MulAut M)⁻¹ (k m)) =
      ∏ q : Qt, φ (((q.out : ↥K) : MulAut M)⁻¹ m)
    refine (Fintype.prod_equiv (MulAction.toPerm k') _ _ fun q => ?_).symm
    show φ (((q.out : ↥K) : MulAut M)⁻¹ m) = φ ((((k' • q).out : ↥K) : MulAut M)⁻¹ (k m))
    have hq : (QuotientGroup.mk (k' * q.out) : Qt) = k' • q := by
      conv_rhs => rw [← q.out_eq']
      rfl
    have hp : (k' * q.out)⁻¹ * (k' • q).out ∈ Pg.subgroupOf K := by
      rw [← QuotientGroup.eq, hq, QuotientGroup.out_eq']
    have e : (((k' • q).out : ↥K) : MulAut M)⁻¹ * k =
        (((k' * q.out)⁻¹ * (k' • q).out : ↥K) : MulAut M)⁻¹ *
          ((q.out : ↥K) : MulAut M)⁻¹ := by
      have hk' : ((k' : ↥K) : MulAut M) = k := rfl
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hk']
      group
    rw [← MulAut.mul_apply, e, MulAut.mul_apply,
      hφP _ (Pg.inv_mem (Subgroup.mem_subgroupOf.mp hp))]
  have hΦc : commSubOf ⊤ K ≤ Φ.ker := by
    rw [commSubOf, Subgroup.closure_le]
    rintro _ ⟨k, hk, m, -, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, hΦK k hk m]
    exact mul_inv_cancel _
  have h1 := hΦc hzc
  rw [MonoidHom.mem_ker] at h1
  have hzK : ∀ q : Qt, ((q.out : ↥K) : MulAut M)⁻¹ z = z := fun q =>
    hz _ (K.inv_mem (q.out).2)
  have h2 : Φ z = φ z ^ Fintype.card Qt := by
    show ∏ q : Qt, φ (((q.out : ↥K) : MulAut M)⁻¹ z) = _
    simp only [hzK, Finset.prod_const, Finset.card_univ]
  have hcard : Odd (Fintype.card Qt) := by
    rw [← Nat.card_eq_fintype_card]
    exact hodd
  obtain ⟨j, hj⟩ := hcard
  rw [h2, hj, pow_succ, pow_mul, hQ, one_pow, one_mul] at h1
  exact h1

end Gaschutz

section Six

variable {Y : Type} [Group Y] [Finite Y] {W : Type} [CommGroup W] [Finite W]

namespace Hyp1321

variable (P : Hyp1321 Y W)

omit [Finite Y] in
theorem commSubOf_L_eq_top (QL : HypL1 P) {S : Subgroup Y} (hS : IsSylowTwoOf S P.K)
    (hSL : S ≤ Subgroup.normalizer (QL.L : Set Y)) (hU : commSubOf ⊤ (P.K.map P.ρ) = ⊤)
    (hb1 : commSubOf ⊤ (QL.L.map P.ρ) ⊔ fixV (P.K.map P.ρ) = ⊤) :
    commSubOf ⊤ (QL.L.map P.ρ) = ⊤ := by
  set M0 := commSubOf ⊤ (QL.L.map P.ρ) with hM0
  have hdec : ∀ w : W, ∃ m ∈ M0, ∃ c ∈ fixV (P.K.map P.ρ), m * c = w := fun w =>
    Subgroup.mem_sup.mp (hb1 ▸ Subgroup.mem_top w)
  have hSP : S.map P.ρ ≤ centQuot M0 := by
    rintro _ ⟨s, hs, rfl⟩ w
    obtain ⟨m, hm, c, hc, rfl⟩ := hdec w
    have hcs : P.ρ s c = c := hc _ ⟨s, hS.1 hs, rfl⟩
    have hms : P.ρ s m ∈ M0 := by
      refine maps_commSubOf (fun k hk => ?_) (fun u _ => Subgroup.mem_top _) m hm
      obtain ⟨l, hl, rfl⟩ := hk
      exact ⟨s * l * s⁻¹, (Subgroup.mem_normalizer_iff.mp (hSL hs) l).mp hl, by
        rw [map_mul, map_mul, map_inv]⟩
    have e : P.ρ s (m * c) * (m * c)⁻¹ = P.ρ s m * m⁻¹ := by
      rw [map_mul, hcs]
      group
    rw [e]
    exact M0.mul_mem hms (M0.inv_mem hm)
  have hodd : Odd ((centQuot M0).relIndex (P.K.map P.ρ)) := by
    have h1 : (S.map P.ρ).relIndex (P.K.map P.ρ) = S.relIndex P.K :=
      Subgroup.relIndex_map_map_of_injective S P.K P.inj
    have h2 := Subgroup.relIndex_dvd_of_le_left (P.K.map P.ρ) hSP
    rw [h1] at h2
    have h3 : ¬ 2 ∣ S.relIndex P.K := hS.2.2
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h => h3 (h.trans h2))
  have hQ : ∀ q : W ⧸ M0, q ^ 2 = 1 := by
    intro q
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_pow, P.sq w, QuotientGroup.mk_one]
  have hφ : ∀ g ∈ centQuot M0, ∀ m : W,
      QuotientGroup.mk' M0 (g m) = QuotientGroup.mk' M0 m := by
    intro g hg m
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have h := M0.inv_mem (hg m)
    rwa [mul_inv_rev, inv_inv, mul_comm] at h
  have hC : fixV (P.K.map P.ρ) ≤ M0 := by
    intro z hz
    have h := map_eq_one_of_mem_commSubOf hodd hQ (QuotientGroup.mk' M0) hφ
      (fun k hk => hz k hk) (by rw [hU]; exact Subgroup.mem_top z)
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  exact (sup_eq_left.mpr hC).symm.trans hb1

end Hyp1321

end Six

end CFSG.Quasithin.H13.A5
