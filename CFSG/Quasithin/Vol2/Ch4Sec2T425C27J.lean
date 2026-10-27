module

public import CFSG.Quasithin.Vol2.Ch4Sec2T425C27I
public import CFSG.RankThree.PartOne.KFCL.L4Block
public import CFSG.Quasithin.Vol2.Ch4Sec2T425C27F
public import CFSG.Quasithin.Vol2.Ch4Sec2T425C27G

public section

namespace CFSG.Quasithin.H13.Ch4.T425C27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SmithC27 CFSG.Quasithin.SBc17
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

theorem solvable_or_dvd_of_levi {F : Type} [Field F] [Finite F] [CharP F 2]
    (h4 : 4 ≤ Nat.card F) {Q : Type} [Group Q] [Finite Q] (ρ : Q →* GL (Fin 2) F)
    (hρ : ∀ x, ρ x = 1 → x ^ 2 = 1) (ι : SpecialLinearGroup (Fin 2) F →* Q)
    (hρι : ∀ A, ρ (ι A) = SpecialLinearGroup.toGL A) {X : Subgroup Q} (hX : X.Normal) :
    Group.IsSolvable X ∨ Nat.card (SpecialLinearGroup (Fin 2) F) ∣ Nat.card X := by
  have : IsSimpleGroup (SpecialLinearGroup (Fin 2) F) :=
    CFSG.RankThree.PartOne.KFCL.L4.sl2_isSimpleGroup h4
  set Y := X.map ρ with hY
  set N := Y.comap (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F)
  have hN : N.Normal := by
    refine ⟨fun B hB A => ?_⟩
    obtain ⟨x, hx, hxB⟩ := hB
    refine ⟨ι A * x * (ι A)⁻¹, hX.conj_mem x hx (ι A), ?_⟩
    rw [map_mul, map_mul, map_inv, hρι, hxB, map_mul, map_mul, map_inv]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
  · left
    have hYc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := by
      intro a ha b hb
      have hc : a * b * a⁻¹ * b⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem (Y.mul_mem ha hb) (Y.inv_mem ha))
        (Y.inv_mem hb)
      have hdet : ((a * b * a⁻¹ * b⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
        rw [← GeneralLinearGroup.val_det_apply, map_mul, map_mul, map_mul, map_inv, map_inv,
          mul_right_comm (GeneralLinearGroup.det a), mul_inv_cancel, one_mul, mul_inv_cancel,
          Units.val_one]
      let A : SpecialLinearGroup (Fin 2) F := ⟨_, hdet⟩
      have hA : A ∈ N := by
        show SpecialLinearGroup.toGL A ∈ Y
        convert hc using 1
        exact Units.ext rfl
      have hA1 : A = 1 := by
        rw [hbot] at hA
        exact Subgroup.mem_bot.mp hA
      have h1 : a * b * a⁻¹ * b⁻¹ = 1 := Units.ext (congrArg Subtype.val hA1)
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
      exact h1
    set f : ↥X →* ↥Y := (ρ.comp X.subtype).codRestrict Y fun x => ⟨x, x.2, rfl⟩
    have hYs : Group.IsSolvable ↥Y :=
      Group.isSolvable_of_comm fun a b => Subtype.ext (hYc _ a.2 _ b.2)
    refine isSolvable_of_ker f ?_
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 ↥f.ker := by
      intro z
      have hz1 : ρ ((z : ↥X) : Q) = 1 := congrArg Subtype.val z.2
      refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
      simpa using hρ _ hz1
    have : Group.IsNilpotent ↥f.ker := hp.isNilpotent
    infer_instance
  · right
    have hle : (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F).range ≤
        Y := by
      rintro _ ⟨A, rfl⟩
      have : A ∈ N := htop ▸ Subgroup.mem_top A
      exact this
    have h1 := Subgroup.card_dvd_of_le hle
    rw [← Nat.card_congr (MonoidHom.ofInjective SpecialLinearGroup.toGL_injective).toEquiv] at h1
    exact h1.trans (Subgroup.card_map_dvd X ρ)

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {H R M K J : Subgroup G} (c : Ctx H R M K J) (hC27 : ASC27Statement G)
include c hC27

theorem false_of_sl3q {F : Type} [Field F] [Fintype F] {n : ℕ} (hn : 2 ≤ n)
    (hF : Fintype.card F = 2 ^ n)
    (e₀ : ↥(autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) ≃*
      ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))
    (hmax : IsMaxParabolic2 (autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))
      (autOn (M ⊓ K) (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))) : False := by
  classical
  set V := omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) with hV
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) hF
  have hq4 : 4 ≤ Fintype.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h4 : 4 ≤ Nat.card F := by rwa [Nat.card_eq_fintype_card]
  let e : ↥(autOn K V) ≃* SpecialLinearGroup (Fin 3) F :=
    e₀.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm
  obtain ⟨g, d, hd1, hd3, hP⟩ := QP.exists_conj_stabilizer_of_mulEquiv (by norm_num) hmax e
  set φ : ↥(autOn K V) →* SpecialLinearGroup (Fin 3) F :=
    (MulAut.conj g⁻¹).toMonoidHom.comp e.toMonoidHom with hφdef
  have hφ : Function.Injective φ := (MulAut.conj g⁻¹).injective.comp e.injective
  have hPφ : ((autOn (M ⊓ K) V).subgroupOf (autOn K V)).map φ =
      stabilizer (flagSpace 3 F d) := by
    rw [hφdef, ← Subgroup.map_map, hP, Subgroup.map_map]
    have hid : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g : SpecialLinearGroup (Fin 3) F →*
        SpecialLinearGroup (Fin 3) F) = MonoidHom.id _ :=
      MonoidHom.ext fun x => by
        show (MulAut.conj g⁻¹) ((MulAut.conj g) x) = x
        rw [MulAut.conj_apply, MulAut.conj_apply]
        group
    rw [hid, Subgroup.map_id]
  have hJL : autOn J V ≤ autOn K V := autOn_mono' c.J_le_K
  set J' := ((autOn J V).subgroupOf (autOn K V)).map φ with hJ'
  have hJQ : J' ≤ stabilizer (flagSpace 3 F d) := by
    rw [← hPφ]
    exact Subgroup.map_mono fun x hx => autOn_mono' c.J_le hx
  have hQJ : stabilizer (flagSpace 3 F d) ≤
      Subgroup.normalizer (J' : Set (SpecialLinearGroup (Fin 3) F)) :=
    hPφ ▸ map_subgroupOf_le_normalizer c.autOn_le_normalizer φ hφ
  have hXn : (J'.subgroupOf (stabilizer (flagSpace 3 F d))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJQ).mpr hQJ
  have key : Group.IsSolvable ↥(J'.subgroupOf (stabilizer (flagSpace 3 F d))) ∨
      Nat.card (SpecialLinearGroup (Fin 2) F) ∣
        Nat.card ↥(J'.subgroupOf (stabilizer (flagSpace 3 F d))) := by
    obtain rfl | rfl : d = 1 ∨ d = 2 := by omega
    · exact solvable_or_dvd_of_levi h4 SL3.rhoOne (fun _ hx => SL3.sq_eq_one_of_rhoOne hx)
        SL3.iotaOne SL3.rhoOne_iotaOne hXn
    · exact solvable_or_dvd_of_levi h4 SL3.rhoTwo (fun _ hx => SL3.sq_eq_one_of_rhoTwo hx)
        SL3.iotaTwo SL3.rhoTwo_iotaTwo hXn
  let eJ : ↥(autOn J V) ≃* ↥(J'.subgroupOf (stabilizer (flagSpace 3 F d))) :=
    (subgroupOfMapEquiv hJL φ hφ).trans (Subgroup.subgroupOfEquivOfLe hJQ).symm
  rcases key with hs | hdvd
  · exact c.not_isSolvable_autOn hC27
      (Group.isSolvable_of_isSolvable_injective (f := eJ.toMonoidHom) eJ.injective)
  have h2q : 2 ∣ Fintype.card F := by
    rw [hF]
    exact dvd_pow_self 2 (by omega)
  set q := Fintype.card F with hq
  have hSL : q - 1 ∣ Nat.card (SpecialLinearGroup (Fin 2) F) := by
    rw [Matrix.card_SL_field 2, Fin.prod_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    have e1 : q ^ 2 - q = q * (q - 1) := by rw [Nat.mul_sub_one, sq]
    rw [e1, ← mul_assoc, Nat.mul_div_cancel _ (by omega : 0 < q - 1)]
    have h2 := Nat.sub_dvd_pow_sub_pow q 1 2
    rw [one_pow] at h2
    exact h2.mul_right q
  have hq1 : q - 1 ≠ 1 := by omega
  set p := (q - 1).minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime hq1
  have hp2 : p ≠ 2 := by
    intro h2
    have h1 : 2 ∣ q - 1 := h2 ▸ Nat.minFac_dvd (q - 1)
    omega
  have hpJ : p ∣ Nat.card J := (Nat.minFac_dvd _).trans (hSL.trans (hdvd.trans
    ((Nat.card_congr eJ.toEquiv).symm.dvd.trans c.card_autOn_dvd)))
  have hle := c.rank p hp hp2 hpJ
  have : Fact p.Prime := ⟨hp⟩
  have hs := c.star hC27
  let f : ↥K →* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 3 F) :=
    (QuotientGroup.mk' _).comp (e₀.toMonoidHom.comp (InternalSec.autOnHom hs.K_le_normalizer_V))
  have hf : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp
    (e₀.surjective.comp (InternalSec.autOnHom_surjective _))
  have hge := two_le_pRank_of_surjective f hf hp2
    (two_le_pRank_psl3 (by rw [Nat.card_eq_fintype_card]; exact Nat.minFac_dvd _))
  omega

end Ctx

end CFSG.Quasithin.H13.Ch4.T425C27
