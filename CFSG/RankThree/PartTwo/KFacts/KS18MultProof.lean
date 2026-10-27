module

public import CFSG.RankThree.PartTwo.KFacts.KS14Mult
public import CFSG.RankThree.PartTwo.KFacts.KS14MultJ2
import CFSG.RankThree.CentralLift.EvenScalarCover
import CFSG.RankThree.CentralLift.ClassicalExactScalarCover
import CFSG.RankThree.PartOne.S15K.ProjSLBridge
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS14

open CFSG CFSG.Assembly.LowTwoRank CFSG.Assembly.RankThreeEven

theorem exists_le_center_not_dvd_pow_mem {X : Type*} [Group X] [Finite X] (Z : Subgroup X)
    (hZ : Z ≤ Subgroup.center X) {r : ℕ} (hr : r.Prime) :
    ∃ Q : Subgroup X, Q ≤ Z ∧ ¬ r ∣ Nat.card Q ∧ ∀ z ∈ Z, ∃ k : ℕ, z ^ (r ^ k) ∈ Q := by
  have : Fact r.Prime := ⟨hr⟩
  have hN : Nat.card Z ≠ 0 := Nat.card_pos.ne'
  set m := Nat.card Z / r ^ (Nat.card Z).factorization r with hm
  have hcop : Nat.Coprime r m := Nat.coprime_ordCompl hr hN
  let Q : Subgroup X :=
    { carrier := {z | z ∈ Z ∧ z ^ m = 1}
      mul_mem' := by
        rintro x y ⟨hx, hxm⟩ ⟨hy, hym⟩
        have hc : Commute x y := Subgroup.mem_center_iff.1 (hZ hy) x
        exact ⟨Z.mul_mem hx hy, by rw [hc.mul_pow, hxm, hym, one_mul]⟩
      one_mem' := ⟨Z.one_mem, one_pow m⟩
      inv_mem' := by
        rintro x ⟨hx, hxm⟩
        exact ⟨Z.inv_mem hx, by rw [inv_pow, hxm, inv_one]⟩ }
  have hmemQ : ∀ z, z ∈ Q ↔ z ∈ Z ∧ z ^ m = 1 := fun _ => Iff.rfl
  refine ⟨Q, fun z hz => ((hmemQ z).1 hz).1, fun hrQ => ?_, fun z hz => ?_⟩
  · obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Q) r hrQ
    have hord : orderOf (z : X) = r := by rw [Subgroup.orderOf_coe]; exact hz
    have hdvd : r ∣ m := hord ▸ orderOf_dvd_of_pow_eq_one ((hmemQ z).1 z.2).2
    exact hr.one_lt.ne' (hcop.eq_one_of_dvd hdvd)
  · refine ⟨(Nat.card Z).factorization r, (hmemQ _).2 ⟨Z.pow_mem hz _, ?_⟩⟩
    rw [← pow_mul, hm, Nat.ordProj_mul_ordCompl_eq_self]
    exact congrArg Subtype.val (pow_card_eq_one' (G := Z) (x := ⟨z, hz⟩))

theorem prime_dvd_of_forall_cover {X S : Type} [Group X] [Finite X] [Group S]
    (hX : Group.IsPerfect X) {Z : Subgroup X} [Z.Normal] (hZc : Z ≤ Subgroup.center X)
    (e : X ⧸ Z ≃* S) {r m : ℕ} (hr : r.Prime) (hrZ : r ∣ Nat.card Z)
    (hcov : ∀ (L : Type) [Group L] [Finite L] [Group.IsPerfect L] (η : L →* S),
      Function.Surjective η → η.ker ≤ Subgroup.center L → IsPGroup r η.ker →
      Nat.card η.ker ∣ m) :
    r ∣ m := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨Q, hQZ, hrQ, hQpow⟩ := exists_le_center_not_dvd_pow_mem Z hZc hr
  have hQn : Q.Normal := Subgroup.normal_of_le_center (hQZ.trans hZc)
  let η : X ⧸ Q →* S :=
    e.toMonoidHom.comp (QuotientGroup.map Q Z (MonoidHom.id X) fun x hx => hQZ hx)
  have hηmk : ∀ x : X, η (x : X ⧸ Q) = e (x : X ⧸ Z) := fun _ => rfl
  have hη : Function.Surjective η := by
    intro s
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e.symm s)
    exact ⟨(x : X ⧸ Q), by rw [hηmk, hx, MulEquiv.apply_symm_apply]⟩
  have hker : ∀ x : X, η (x : X ⧸ Q) = 1 ↔ x ∈ Z := by
    intro x
    rw [hηmk, ← map_one e, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hkerc : η.ker ≤ Subgroup.center (X ⧸ Q) := by
    intro g hg
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    have hx : x ∈ Subgroup.center X := hZc ((hker x).1 hg)
    rw [Subgroup.mem_center_iff]
    intro h
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective h
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 hx y]
  have hkerp : IsPGroup r η.ker := by
    rintro ⟨g, hg⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨k, hk⟩ := hQpow x ((hker x).1 hg)
    refine ⟨k, Subtype.ext ?_⟩
    change (x : X ⧸ Q) ^ (r ^ k) = 1
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 hk
  have hdvd := hcov (X ⧸ Q) η hη hkerc hkerp
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) r hrZ
  have hzord : orderOf (z : X) = r := by rw [Subgroup.orderOf_coe]; exact hz
  have hzQ : (z : X) ∉ Q := fun h => hrQ (hzord ▸ Subgroup.orderOf_dvd_natCard Q h)
  have hzker : ((z : X) : X ⧸ Q) ∈ η.ker := (hker z).2 z.2
  have hgord : orderOf ((z : X) : X ⧸ Q) = r := by
    refine orderOf_eq_prime ?_ fun h => hzQ ((QuotientGroup.eq_one_iff _).1 h)
    rw [← QuotientGroup.mk_pow, ← hzord, pow_orderOf_eq_one, QuotientGroup.mk_one]
  have hrker : r ∣ Nat.card η.ker := by
    have := orderOf_dvd_natCard (⟨((z : X) : X ⧸ Q), hzker⟩ : η.ker)
    rwa [Subgroup.orderOf_mk, hgord] at this
  exact hrker.trans hdvd

section Covers


theorem card_ker_dvd_gcd_projSL {p e : ℕ} [hp : Fact p.Prime] (he : 1 ≤ e) {r : ℕ}
    (hr : r.Prime) (hr3 : 3 < r) {L : Type} [Group L] [Finite L] [Group.IsPerfect L]
    (η : L →* projSL 3 (GaloisField p e)) (hη : Function.Surjective η)
    (hC : η.ker ≤ Subgroup.center L) (hCp : IsPGroup r η.ker) :
    Nat.card η.ker ∣ Nat.gcd 3 (p ^ e - 1) := by
  set E := CFSG.RankThree.PartOne.S15K.projSLEquivProjectiveSL 3 (GaloisField p e) with hE
  set η' := E.toMonoidHom.comp η with hη'
  have hker : η'.ker = η.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hη', MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, map_eq_one_iff _ E.injective]
  have hs : Function.Surjective η' := E.surjective.comp hη
  have hk : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  rw [← hker] at hC hCp ⊢
  rcases hp.out.eq_two_or_odd' with rfl | hodd
  · obtain ⟨⟨φ, hφ, -⟩, hall⟩ :=
      CFSG.RankThree.CentralLift.even_field_linear_perfect_central_large_prime_scalar_cover hr
        hr3 hk (by norm_num) η' hs hC hCp
    exact (hall φ hφ).2.2.2.2.2.2
  · obtain ⟨⟨φ, hφ, -⟩, hall⟩ :=
      CFSG.RankThree.CentralLift.odd_field_linear_perfect_central_large_prime_exact_scalar_cover_map
        hr hr3 hp.out hodd he hk (by norm_num) η' hs hC hCp
    exact (hall φ hφ).2.2.2.2.2.2

theorem card_ker_dvd_gcd_projSU {p e : ℕ} [hp : Fact p.Prime] (he : 1 ≤ e) {r : ℕ}
    (hr : r.Prime) (hr3 : 3 < r) {L : Type} [Group L] [Finite L] [Group.IsPerfect L]
    (η : L →* projSU 3 p e) (hη : Function.Surjective η)
    (hC : η.ker ≤ Subgroup.center L) (hCp : IsPGroup r η.ker) :
    Nat.card η.ker ∣ Nat.gcd 3 (p ^ e + 1) := by
  set E : projSU 3 p e ≃* StatedProj (StatedSU 3 (p ^ e) (GaloisField p (2 * e))) :=
    ((Census.statedProjEquivProjImage _).trans
      (MulEquiv.subgroupCongr (Census.projImage_statedSU 3 p e))).symm with hE
  set η' := E.toMonoidHom.comp η with hη'
  have hker : η'.ker = η.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hη', MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, map_eq_one_iff _ E.injective]
  have hs : Function.Surjective η' := E.surjective.comp hη
  have hK : Nat.card (GaloisField p (2 * e)) = p ^ (2 * e) := GaloisField.card p (2 * e) (by omega)
  rw [← hker] at hC hCp ⊢
  rcases hp.out.eq_two_or_odd' with rfl | hodd
  · have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 e (GaloisField 2 (2 * e)) :=
      ⟨Nat.prime_two, he, hK⟩
    obtain ⟨⟨φ, hφ, -⟩, hall⟩ :=
      CFSG.RankThree.CentralLift.even_field_unitary_perfect_central_large_prime_scalar_cover hr
        hr3 h le_rfl η' hs hC hCp
    exact (hall φ hφ).2.2.2.2.2.2
  · obtain ⟨⟨φ, -, -, -, -, -, ⟨ψ⟩⟩, hD⟩ :=
      CFSG.RankThree.CentralLift.unitary_exact_scalar_cover hr hr3 hp.out hodd he
        (K := GaloisField p (2 * e)) (by rw [hK, ← pow_mul, mul_comm]) le_rfl
        (Or.inr (Or.inr rfl)) η' hs hC hCp
    rw [Nat.card_congr ψ.toEquiv]
    exact (Subgroup.card_quotient_dvd_card _).trans hD

theorem ks18Mult_lThreePi (X : Type) [Group X] [Finite X] (Z : Subgroup X) [Z.Normal]
    (hX : Group.IsPerfect X) (hZc : Z ≤ Subgroup.center X) (hcop : Nat.Coprime 6 (Nat.card Z))
    (hS : Sec13.IsLThreePi (X ⧸ Z)) : Z = ⊥ := by
  obtain ⟨p, e, hp, he, hiso⟩ := hS
  refine Subgroup.eq_bot_of_card_eq _ (by_contra fun h1 => ?_)
  obtain ⟨r, hr, hrZ⟩ := Nat.exists_prime_and_dvd h1
  have hr6 : Nat.Coprime 6 r := Nat.Coprime.coprime_dvd_right hrZ hcop
  have hr3 : 3 < r := by
    have h2 : r ≠ 2 := by
      rintro rfl
      norm_num at hr6
    have h3 : r ≠ 3 := by
      rintro rfl
      norm_num at hr6
    have := hr.two_le
    omega
  have hr3' : r ∣ 3 := by
    rcases hiso with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
    · exact prime_dvd_of_forall_cover hX hZc φ hr hrZ fun L _ _ _ η hη hC hCp =>
        (card_ker_dvd_gcd_projSL he hr hr3 η hη hC hCp).trans (Nat.gcd_dvd_left _ _)
    · exact prime_dvd_of_forall_cover hX hZc φ hr hrZ fun L _ _ _ η hη hC hCp =>
        (card_ker_dvd_gcd_projSU he hr hr3 η hη hC hCp).trans (Nat.gcd_dvd_left _ _)
  have := Nat.le_of_dvd (by norm_num) hr3'
  omega

end Covers

theorem ks18Mult :
    KS18Mult := by
  intro X _ _ Z _ hX hZc hcop hS
  rcases hS with hL | hM12 | hJ | hA7 | hM22
  · exact ks18Mult_lThreePi X Z hX hZc hcop hL
  · exact ks18Mult_sporadic X Z hX hZc hcop (Or.inl hM12)
  · exact ks18Mult_j2 X Z hX hZc hcop hJ
  · exact ks18Mult_sporadic X Z hX hZc hcop (Or.inr (Or.inl hA7))
  · exact ks18Mult_sporadic X Z hX hZc hcop (Or.inr (Or.inr hM22))

end CFSG.RankThree.PartTwo.KFacts.KS14
