module

public import CFSG.Quasithin.Background.RonanD321End

public section

namespace CFSG.Quasithin.RonanD321

open CFSG.Quasithin CFSG.Quasithin.SmithD321 CFSG.Quasithin.SmithD39Two CFSG.Quasithin.Z391
  CFSG.Quasithin.SmithD391
  CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Pointwise

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

theorem cent_eq_bot_of_d321Three (hB : D321Base M Mp T L V t) (h3 : D321Three Mp L) :
    M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) = ⊥ := by
  set C := M ⊓ Subgroup.centralizer (Mp : Set (MulAut W))
  have hodd : ∀ x ∈ C, ∀ p : ℕ, p.Prime → p ≠ 2 → x ^ p = 1 → x = 1 := by
    intro x hx p hp hp2 hxp
    by_cases hpL : p ∣ Nat.card ↥L
    · exact hB.eq_one_of_pow_prime hp hp2 hpL hx hxp
    let _i := qAct hB.hD.hyp.Mp_normal
    obtain ⟨hxM, hxc⟩ := hx
    have hxcomm : ∀ m ∈ Mp, x * m = m * x := fun m hm =>
      ((Subgroup.mem_centralizer_iff.1 hxc) m hm).symm
    have hpow : ∀ q : W ⧸ modFix Mp (⊤ : Subgroup W), (⟨x, hxM⟩ : ↥M) ^ p • q = q := by
      intro q
      have h1 : (⟨x, hxM⟩ : ↥M) ^ p = 1 := Subtype.ext (by simpa using hxp)
      rw [h1, one_smul]
    have h1 := smul_eq_of_pElement hB h3 hp hp2 hpL hxM (fun l hl => hxcomm l (hB.L_le_Mp hl))
      (fun q _ => hpow q)
    have h3t := d321Three_conjAutSub (hB.hD.hyp.Mp_normal hB.t_mem) h3
    have hpLt : ¬ p ∣ Nat.card ↥(conjAutSub t L) := by
      have e : Nat.card ↥(conjAutSub t L) = Nat.card ↥L :=
        (Nat.card_congr (Subgroup.equivMapOfInjective L (MulAut.conj t).toMonoidHom
          (MulAut.conj t).injective).toEquiv).symm
      rwa [e]
    have h2 := smul_eq_of_pElement hB.swap h3t hp hp2 hpLt hxM
      (fun l hl => hxcomm l (hB.Lt_le_Mp hl)) (fun q _ => hpow q)
    apply hB.faithful hxM
    intro q
    have hq : q ∈ tilde Mp ⊤ (commV L) ⊔ (⟨t, hB.t_mem⟩ : ↥M) • tilde Mp ⊤ (commV L) :=
      hB.sup_tildeU ▸ Subgroup.mem_top q
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hq
    rw [hB.smul_tildeU] at hb
    rw [smul_mul', h1 a ha, h2 b hb]
  have h2 : IsPGroup 2 ↥C := by
    refine IsPGroup.of_card (n := (Nat.card ↥C).primeFactorsList.length)
      (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {d} hd hdC => ?_)
    by_contra hd2
    have : Fact d.Prime := ⟨hd⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' d hdC
    have hy1 : (y : MulAut W) ^ d = 1 := by
      have h1 := pow_orderOf_eq_one y
      rw [hy] at h1
      exact congrArg Subtype.val h1
    have hy2 : y = 1 := Subtype.ext (hodd _ y.2 d hd hd2 hy1)
    rw [hy2, orderOf_one] at hy
    exact hd.one_lt.ne hy
  have h := pCoreOf_two_cent_eq_bot hB.hD
  rwa [F6.pCoreOf_eq_self_of_isPGroup h2] at h

end CFSG.Quasithin.RonanD321
