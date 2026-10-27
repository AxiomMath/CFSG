module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LH1Gen424
public import CFSG.RankThree.PartTwo.Sec10.Item1015Proof
public import CFSG.RankThree.PartTwo.Sec8.Hering418L2

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem autRankLeTwo_of_cubeInner {S : Type} [Group S] (hZ : Subgroup.center S = ⊥)
    (hcube : CubeInner S)
    (hE : ∀ E : Subgroup S, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≤ 9) :
    AutRankLeTwo S := by
  intro B hB
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hc : x ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := congrArg (fun α : MulAut S => α g) hx
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc g * x = x * g * x⁻¹ * x := by rw [h]
        _ = x * g := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact hc
  have hBi : B ≤ (MulAut.conj : S →* MulAut S).range := fun b hb => hcube b (hB.2 b hb)
  have hmap : (B.comap (MulAut.conj : S →* MulAut S)).map (MulAut.conj : S →* MulAut S) = B :=
    Subgroup.map_comap_eq_self hBi
  have hcard : Nat.card (B.comap (MulAut.conj : S →* MulAut S)) = Nat.card B := by
    conv_rhs => rw [← hmap]
    rw [Subgroup.card_map_of_injective hinj]
  rw [← hcard]
  exact hE _ (isElemAbelian_comap _ hinj hB)

section CentSolv

variable {G : Type} [Group G] [Finite G]

theorem false_of_dvdK_of_centSolv {S : Type} [Group S]
    (hS : ∀ s : S, s ≠ 1 → Group.IsSolvable (Subgroup.centralizer ({s} : Set S)))
    {L : Subgroup G} (eL : L ⧸ Subgroup.center L ≃* S) {d : G}
    (hLd : ¬ L ≤ Subgroup.centralizer {d})
    {K : Subgroup ↥(L ⊓ Subgroup.centralizer {d})} (hK : IsComponent K)
    (hdK : d ∈ K.map (L ⊓ Subgroup.centralizer {d}).subtype) : False := by
  set K' := K.map (L ⊓ Subgroup.centralizer {d}).subtype with hK'
  have hK'M : K' ≤ L ⊓ Subgroup.centralizer {d} := Subgroup.map_subtype_le K
  have hK'L : K' ≤ L := hK'M.trans inf_le_left
  have hK'd : K' ≤ Subgroup.centralizer {d} := hK'M.trans inf_le_right
  have hdL : d ∈ L := hK'L hdK
  set π : ↥L →* S := eL.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L)) with hπ
  have hker : ∀ x : ↥L, π x = 1 ↔ x ∈ Subgroup.center ↥L := by
    intro x
    rw [hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_eq_one_iff _ eL.injective,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  set s := π ⟨d, hdL⟩ with hs
  have hs1 : s ≠ 1 := by
    intro h1
    have hZ := (hker _).mp h1
    apply hLd
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hZ ⟨y, hy⟩))
  set J : Subgroup ↥L := K'.subgroupOf L with hJ
  have hJs : J.map π ≤ Subgroup.centralizer ({s} : Set S) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hs, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hK'd hx))
  let eJ : ↥K ≃* ↥J := (K.equivMapOfInjective _ (Subgroup.subtype_injective _)).trans
    ((Subgroup.subgroupOfEquivOfLe hK'L).symm)
  have hJp : Group.IsPerfect ↥J := by
    haveI : Group.IsPerfect ↥K := hK.1.1
    exact Group.IsPerfect.ofSurjective (f := eJ.toMonoidHom) eJ.surjective
  have hJs' : ∀ x : ↥J, π (x : ↥L) ∈ Subgroup.centralizer ({s} : Set S) := fun x =>
    hJs ⟨x, x.2, rfl⟩
  let g : ↥J →* ↥(Subgroup.centralizer ({s} : Set S)) :=
    (π.comp J.subtype).codRestrict _ hJs'
  have hgker : ∀ x : ↥g.ker, ((x : ↥J) : ↥L) ∈ Subgroup.center ↥L := by
    intro x
    have h1 : g x = 1 := x.2
    have h2 : π ((x : ↥J) : ↥L) = 1 := congrArg Subtype.val h1
    exact (hker _).mp h2
  haveI : Group.IsSolvable ↥g.ker := isSolvable_of_comm fun a b => by
    apply Subtype.ext
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hgker b) _
  haveI : Group.IsSolvable ↥(Subgroup.centralizer ({s} : Set S)) := hS s hs1
  have hJsol : Group.IsSolvable ↥J :=
    solvable_of_ker_le_range g.ker.subtype g (by rw [Subgroup.range_subtype])
  haveI : Nontrivial ↥J := by
    haveI : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
    exact eJ.symm.toEquiv.nontrivial
  haveI := hJp
  exact Group.IsPerfect.not_isSolvable ↥J hJsol

end CentSolv

section Rows

theorem row427Cent_of_centSolv
    {S : Type} [Group S]
    (hS : ∀ s : S, s ≠ 1 → Group.IsSolvable (Subgroup.centralizer ({s} : Set S))) :
    Row427Cent S := by
  intro G _ _ hG A hA hEF hθ L hL ⟨eL⟩ d hdA _ hN hLd K hK hKt hCA
  rcases hKt with h5 | ⟨hdK, -⟩
  · obtain ⟨e5⟩ := h5
    exact false_of_cent_a5 hG hA hEF hL hdA hN hLd hK e5 hCA
  · exact false_of_dvdK_of_centSolv hS eL hLd hK hdK

theorem kH1_one_ge_five
    (p e : ℕ) [Fact p.Prime] (hp : 3 < p) (he : 1 ≤ e) :
    RowOf427 (projSL 2 (GaloisField p e)) := by
  intro S _ _ _ _ ⟨eS⟩
  have hK : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  have : Fact p.Prime := inferInstance
  let φ : S ≃* CFSG.GorensteinWalter.PSL2 (GaloisField p e) :=
    eS.trans (projSLEquivPSL (GaloisField p e))
  haveI : Finite (CFSG.GorensteinWalter.PSL2 (GaloisField p e)) := Finite.of_equiv S φ.toEquiv
  have hK3 : ringChar (GaloisField p e) ≠ 3 := by
    rw [ringChar.eq (GaloisField p e) p]
    omega
  have hK4 : 4 ≤ Nat.card (GaloisField p e) := by
    rw [hK]
    calc 4 ≤ p := by omega
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ e := Nat.pow_le_pow_right (by omega) he
  refine row427_of_cent (row427Cent_of_centSolv fun s hs => ?_) ?_
  ·
    set H := Subgroup.centralizer ({φ s} : Set (CFSG.GorensteinWalter.PSL2 (GaloisField p e)))
    have hZ : Subgroup.center H ≠ ⊥ := by
      intro h0
      have hmem : (⟨φ s, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ : H) ∈
          Subgroup.center H := by
        rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp y.2)
      rw [h0, Subgroup.mem_bot] at hmem
      have : φ s = 1 := congrArg Subtype.val hmem
      exact hs ((map_eq_one_iff φ φ.injective).mp this)
    have hHs := Item424Proof.isSolvable_of_center_ne_bot_psl2 hK H hZ
    have hmap : (Subgroup.centralizer ({s} : Set S)).map φ.toMonoidHom = H := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hx' : x * s = s * x := Subgroup.mem_centralizer_singleton_iff.mp hx
        refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        simp only [MulEquiv.coe_toMonoidHom]
        rw [← map_mul, ← map_mul, hx']
      · intro hy
        have hy' : y * φ s = φ s * y := Subgroup.mem_centralizer_singleton_iff.mp hy
        refine ⟨φ.symm y, Subgroup.mem_centralizer_singleton_iff.mpr ?_, by simp⟩
        apply φ.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy']
    let ψ : ↥(Subgroup.centralizer ({s} : Set S)) ≃* H :=
      ((Subgroup.centralizer ({s} : Set S)).equivMapOfInjective φ.toMonoidHom φ.injective).trans
        (MulEquiv.subgroupCongr hmap)
    exact solvable_of_surjective (f := ψ.symm.toMonoidHom) ψ.symm.surjective
  · exact AutRankLeTwo.of_mulEquiv φ (Hering418L2.card_le_nine_of_mulAut_PSL2 hK3 hK4)

theorem kH1_two_SU_five
    : RowOf427 (projSU 3 5 1) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hc := CFSG.RankThree.PartTwo.KFacts.KS14.card_projSU_three_mul_gcd 5 1 le_rfl
  norm_num at hc
  refine rowOf427_of_autRank ?_
    (Sec10.Item1015Proof.card_le_nine_of_mulAut_projSU (by norm_num) le_rfl (by norm_num)
      (by norm_num))
  have h : Nat.card (projSU 3 5 1) = 126000 := by omega
  rw [h]
  norm_num

theorem kH1_two_SL_five_two
    : RowOf427 (projSL 3 (GaloisField 5 2)) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hc := CFSG.RankThree.PartTwo.KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 5 2)
  rw [GaloisField.card 5 2 (by norm_num)] at hc
  norm_num at hc
  refine rowOf427_of_autRank ?_
    (Sec10.Item1015Proof.card_le_nine_of_mulAut_projSL (by norm_num) (by norm_num) (by norm_num))
  have h : Nat.card (projSL 3 (GaloisField 5 2)) = 50778000000 := by omega
  rw [h]
  norm_num

theorem cubeInner_adjointG2_prime
    {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hK : Nat.card K = p) : CubeInner ↥(adjointGroup .G2 K) := by
  intro τ hτ
  by_contra hout
  haveI : Fact p.Prime := ⟨hp⟩
  have : CharP K p := by
    have : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hK, pow_one])
  have hK3 : ringChar K ≠ 3 := by
    rw [ringChar.eq K p]
    omega
  have hK4 : 4 ≤ Nat.card K := by omega
  obtain ⟨σ, hσ, -⟩ := KFacts.g2_order_three_field_descent hK3 hK4 hτ hout
  haveI := Item49OddChar.subsingleton_ringAut_of_card_prime hp hK
  rw [Subsingleton.elim σ 1, orderOf_one] at hσ
  norm_num at hσ

theorem kH1_four_G2_five
    (q : TauCeti.PrimePower) (hqp : q.p = 5) (hqe : q.exponent = 1)
    (hq : (TauCeti.LieTypeIndex.G2 q).Valid) :
    RowOf427 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group := by
  obtain ⟨K, _, _, hKc, -, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hq
  have hK5 : Nat.card K = 5 := by
    rw [hKc, TauCeti.PrimePower.card_def, hqp, hqe, pow_one]
  have hK3 : ¬ 3 ∣ Nat.card K := by rw [hK5]; norm_num
  refine rowOf427_of_autRank ?_ (AutRankLeTwo.of_mulEquiv eK ?_)
  · rw [Nat.card_congr eK.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK5]
    norm_num [CFSG.Open.ordG2]
  · exact autRankLeTwo_of_cubeInner center_adjointGroup_eq_bot
      (cubeInner_adjointG2_prime (p := 5) (by norm_num) (by norm_num) hK5)
      (CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.rankLE2_three_adjointGroup_G2 K hK3)

end Rows

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
