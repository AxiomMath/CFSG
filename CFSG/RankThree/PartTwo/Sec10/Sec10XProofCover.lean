module

public import CFSG.RankThree.PartTwo.Sec10.Item1015Proof
public import CFSG.LieType.Steinberg.CentralExt.SL2CentrallyClosed

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)

namespace Sec10XProof

section Center

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
theorem mulAutQuotientHom_center_injective [Group.IsPerfect Q] :
    Function.Injective (mulAutQuotientHom (Subgroup.center Q)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro σ hσ
  rw [MonoidHom.mem_ker] at hσ
  rw [Subgroup.mem_bot]
  refine KFacts.eq_one_of_forall_mul_inv_mem_center fun s => ?_
  have h := congrArg (fun τ : MulAut (Q ⧸ Subgroup.center Q) => τ (s : Q ⧸ Subgroup.center Q)) hσ
  simp only [mulAutQuotientHom_mk, MulAut.one_apply] at h
  rw [QuotientGroup.eq] at h
  have := (Subgroup.center Q).inv_mem h
  simpa using this

omit [Finite Q] in
theorem listFacts_of_quotient_center {S : Type} [Group S] (hQ : CFSG.IsQuasisimple Q)
    (e : Q ⧸ Subgroup.center Q ≃* S)
    (hS : ∀ B : Subgroup (MulAut S), CFSG.Assembly.IsElemAbelian 3 B → Nat.card B ≤ 9)
    (h2 : 2 ∣ Nat.card S) (hcard : ¬ Nat.card S ∣ 58968) : Item1015Proof.ListFacts Q := by
  have : Group.IsPerfect Q := hQ.1
  refine ⟨Item1015Proof.card_le_nine_of_injective
    ((MulAut.congr e).toMonoidHom.comp (mulAutQuotientHom (Subgroup.center Q)))
    ((MulAut.congr e).injective.comp mulAutQuotientHom_center_injective) hS, ?_⟩
  intro M hMn hModd hdvd
  have hSQ : Nat.card S = (Subgroup.center Q).index := by
    rw [Subgroup.index, Nat.card_congr e.toEquiv]
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ hMn with rfl | hMZ
  · rw [Subgroup.card_top] at hModd
    have h2Q : 2 ∣ Nat.card Q := h2.trans (by rw [hSQ]; exact Subgroup.index_dvd_card _)
    exact (Nat.not_even_iff_odd.mpr hModd) (even_iff_two_dvd.mpr h2Q)
  · exact hcard (by rw [hSQ]; exact (Subgroup.index_dvd_of_le hMZ).trans hdvd)

theorem isPGroup_center_of_theta_eq_bot (hθ : aschbacherSolvableCore 3 Q = ⊥) :
    IsPGroup 3 (Subgroup.center Q) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, -, hmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := Q) Nat.prime_three
  rw [IsPGroup.iff_card]
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {r} hr hrdvd => ?_⟩
  by_contra hr3
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' r hrdvd
  have hzc : Subgroup.zpowers (z : Q) ≤ Subgroup.center Q :=
    Subgroup.zpowers_le.mpr z.2
  have hN : (Subgroup.zpowers (z : Q)).Normal := Subgroup.normal_of_le_center hzc
  have hS : Group.IsSolvable (Subgroup.zpowers (z : Q)) :=
    Group.isSolvable_of_comm fun x y => Subtype.ext (Subgroup.mem_center_iff.mp (hzc y.2) x)
  have hz3 : ¬ 3 ∣ Nat.card (Subgroup.zpowers (z : Q)) := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz]
    intro h3
    exact hr3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).mp h3).symm
  have hle := hmax _ hN hS hz3
  rw [hθ, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
  have h1 : z = 1 := Subtype.ext hle
  rw [h1, orderOf_one] at hz
  exact hr.one_lt.ne hz

theorem center_eq_bot_of_psl2_27
    [Group.IsPerfect Q] (hZ : IsPGroup 3 (Subgroup.center Q))
    (e : Q ⧸ Subgroup.center Q ≃* GorensteinWalter.PSL2 (GaloisField 3 3)) :
    Subgroup.center Q = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Nat.card (GaloisField 3 3) = 27 := by
    rw [GaloisField.card 3 3 (by norm_num)]
    norm_num
  set q : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 3 3) →*
      GorensteinWalter.PSL2 (GaloisField 3 3) :=
    QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 3 3)))
    with hqdef
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hqker : q.ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 3 3)) :=
    QuotientGroup.ker_mk' _
  obtain ⟨eM⟩ := CFSG.LieType.Steinberg.CentralExt.SL2Closed.sl2_hopfMultiplier_mulEquiv_ker
    (by rw [hK]; norm_num) (by rw [hK]; norm_num) q hq hqker.le
  have hM : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (GorensteinWalter.PSL2 (GaloisField 3 3))) ≤ 2 := by
    rw [Nat.card_congr eM.toEquiv,
      Nat.card_congr (MulEquiv.subgroupCongr hqker).toEquiv,
      Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity).toEquiv]
    have hroots : rootsOfUnity (max (Fintype.card (Fin 2)) 1) (GaloisField 3 3) =
        rootsOfUnity 2 (GaloisField 3 3) := by simp
    rw [hroots]
    exact card_rootsOfUnity (GaloisField 3 3) 2
  have : Finite (CFSG.RankThree.PerfectCover.hopfMultiplier
      (GorensteinWalter.PSL2 (GaloisField 3 3))) := Finite.of_equiv _ eM.symm.toEquiv
  set q' : Q →* GorensteinWalter.PSL2 (GaloisField 3 3) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q)) with hq'def
  have hq' : Function.Surjective q' := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker' : q'.ker = Subgroup.center Q := by
    ext x
    rw [MonoidHom.mem_ker, hq'def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hsurj := CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective q' hq' hker'.le
  have hle := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_congr (MulEquiv.subgroupCongr hker').toEquiv] at hle
  obtain ⟨k, hk⟩ := hZ.exists_card_eq
  have hk0 : k = 0 := by
    by_contra hk0
    have h3 : 3 ≤ 3 ^ k := Nat.le_self_pow hk0 3
    omega
  rw [hk0, pow_zero] at hk
  exact Subgroup.eq_bot_of_card_eq _ hk

end Center

section Radical

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem aschbacherSolvableCore_le_solvableRadical :
    aschbacherSolvableCore 3 Y ≤ solvableRadical Y :=
  Subgroup.map_subtype_le _

theorem solvableRadical_eq_comap_center
    (hY : CFSG.IsQuasisimple (Y ⧸ aschbacherSolvableCore 3 Y)) :
    solvableRadical Y = (Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y)).comap
      (QuotientGroup.mk' (aschbacherSolvableCore 3 Y)) := by
  set θ := aschbacherSolvableCore 3 Y with hθ
  set π := QuotientGroup.mk' θ with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective θ
  have hRn : (solvableRadical Y).Normal := ABGLocalTools.solvableRadical_normal
  have hRs : Group.IsSolvable (solvableRadical Y) := ABGLocalTools.solvableRadical_isSolvable
  apply le_antisymm
  · have hn : ((solvableRadical Y).map π).Normal := hRn.map π hπs
    have hs : Group.IsSolvable ((solvableRadical Y).map π) :=
      Group.isSolvable_of_surjective (π.subgroupMap_surjective (solvableRadical Y))
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hY hn with htop | hle
    · exfalso
      have : Group.IsSolvable (⊤ : Subgroup (Y ⧸ θ)) := htop ▸ hs
      exact Sec4.false_of_isQuasisimple_of_isSolvable hY
        (Group.isSolvable_of_surjective
          (f := (Subgroup.topEquiv : (⊤ : Subgroup (Y ⧸ θ)) ≃* Y ⧸ θ).toMonoidHom)
          Subgroup.topEquiv.surjective)
    · exact Subgroup.map_le_iff_le_comap.mp hle
  · set K := (Subgroup.center (Y ⧸ θ)).comap π with hK
    have hKn : K.Normal := Subgroup.Normal.comap inferInstance π
    have hθK : θ ≤ K := fun x hx => by
      change π x ∈ Subgroup.center (Y ⧸ θ)
      rw [hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
      exact Subgroup.one_mem _
    have hθs : Group.IsSolvable θ :=
      (solvable_prime_complement_core_characterization (H := Y) Nat.prime_three).1
    have hZs : Group.IsSolvable (Subgroup.center (Y ⧸ θ)) :=
      Group.isSolvable_of_comm fun x y => Subtype.ext (Subgroup.mem_center_iff.mp y.2 x)
    let g : K →* Subgroup.center (Y ⧸ θ) :=
      (π.comp K.subtype).codRestrict (Subgroup.center (Y ⧸ θ)) fun x => x.2
    have hKs : Group.IsSolvable K := by
      refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hθK) g ?_
      intro x hx
      have hx1 : π (x : Y) = 1 := congrArg Subtype.val hx
      have hxθ : (x : Y) ∈ θ := by
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
        exact hx1
      exact ⟨⟨x, hxθ⟩, rfl⟩
    exact le_sSup ⟨hKn, hKs⟩

theorem nonempty_quotient_center_mulEquiv
    (hY : CFSG.IsQuasisimple (Y ⧸ aschbacherSolvableCore 3 Y)) [(solvableRadical Y).Normal] :
    Nonempty ((Y ⧸ aschbacherSolvableCore 3 Y) ⧸ Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y)
      ≃* Y ⧸ solvableRadical Y) := by
  have hmap : (solvableRadical Y).map (QuotientGroup.mk' (aschbacherSolvableCore 3 Y)) =
      Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) := by
    rw [solvableRadical_eq_comap_center hY,
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hmap.symm).trans
    (QuotientGroup.quotientQuotientEquivQuotient _ _ aschbacherSolvableCore_le_solvableRadical)⟩

end Radical

section List

open CFSG.Blueprint


variable {Q : Type} [Group Q] [Finite Q]

theorem not_dvd_of_sixteen_dvd {n : ℕ} (h16 : 16 ∣ n) : ¬ n ∣ 58968 := fun h =>
  absurd (h16.trans h) (by norm_num)

theorem listFacts_of_quotient_list (hQ : CFSG.IsQuasisimple Q)
    (hlist : Nonempty (Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (Q ⧸ Subgroup.center Q ≃* NativeSporadic.M12) ∨
      Nonempty (Q ⧸ Subgroup.center Q ≃* NativeSporadic.J2) ∨
      Nonempty (Q ⧸ Subgroup.center Q ≃* NativeSporadic.M22) ∨
      ∃ (p e : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ e ∧ e ≤ 2 ∧
        Sec4.IsoLThreePi (Q ⧸ Subgroup.center Q) p e) :
    Item1015Proof.ListFacts Q := by
  rcases hlist with he | he | he | he | ⟨p, f, hpf, hp3, hf1, hf2, hL | hU⟩
  · obtain ⟨e⟩ := he
    have hcard : Nat.card (alternatingGroup (Fin 7)) = 2520 :=
      KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1
    exact listFacts_of_quotient_center hQ e Item1015Proof.card_le_nine_of_mulAut_alt7
      (by rw [hcard]; norm_num) (by rw [hcard]; norm_num)
  · obtain ⟨e⟩ := he
    exact listFacts_of_quotient_center hQ e Item1015Proof.card_le_nine_of_mulAut_M12
      (by rw [KFacts.KS14.card_nativeM12]; norm_num)
      (not_dvd_of_sixteen_dvd (by rw [KFacts.KS14.card_nativeM12]; norm_num))
  · obtain ⟨e⟩ := he
    have : Finite NativeSporadic.J2 := Finite.of_equiv _ e.toEquiv
    exact listFacts_of_quotient_center hQ e
      (Item1015Proof.card_le_nine_of_mulAut_J2 (MulEquiv.refl _))
      (by rw [KFacts.KS14.card_nativeJ2]; norm_num)
      (not_dvd_of_sixteen_dvd (by rw [KFacts.KS14.card_nativeJ2]; norm_num))
  · obtain ⟨e⟩ := he
    exact listFacts_of_quotient_center hQ e Item1015Proof.card_le_nine_of_mulAut_M22
      (by rw [KFacts.KS14.card_nativeM22]; norm_num)
      (not_dvd_of_sixteen_dvd (by rw [KFacts.KS14.card_nativeM22]; norm_num))
  · have hp : p.Prime := hpf.out
    have hpo : Odd p := hp.odd_of_ne_two (by omega)
    have hf3 : ¬ 3 ∣ f := by omega
    obtain ⟨-, ⟨e⟩⟩ := hL
    have h16 := Item1015Proof.sixteen_dvd_card_projSL (GaloisField p f)
      (by rw [GaloisField.card p f (by omega)]; exact hpo.pow)
    exact listFacts_of_quotient_center hQ e
      (Item1015Proof.card_le_nine_of_mulAut_projSL (by omega) hf1 hf3)
      ((show 2 ∣ 16 by norm_num).trans h16) (not_dvd_of_sixteen_dvd h16)
  · have hp : p.Prime := hpf.out
    have hpo : Odd p := hp.odd_of_ne_two (by omega)
    have hf3 : ¬ 3 ∣ f := by omega
    have hq : 2 < p ^ f := lt_of_lt_of_le (by omega) (Nat.le_self_pow (by omega) p)
    obtain ⟨-, ⟨e⟩⟩ := hU
    have h16 := Item1015Proof.sixteen_dvd_card_projSU p f hf1 hpo
    exact listFacts_of_quotient_center hQ e
      (Item1015Proof.card_le_nine_of_mulAut_projSU (by omega) hf1 hq hf3)
      ((show 2 ∣ 16 by norm_num).trans h16) (not_dvd_of_sixteen_dvd h16)

end List

end Sec10XProof

end CFSG.RankThree.PartTwo.Sec10
