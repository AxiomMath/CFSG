module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixFrameAux

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]

theorem e6QTwoSixFrameFullDiagonal (hK : Nat.card K = 4) {Bs L : Subgroup G} {x : G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤) (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 6)
    (hx : x ∈ Bs)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ) :
    Nat.card ↥(e6QTwoSixFrameAction hNL θ).ker = 3 ∧
      Nat.card ↥(e6QTwoSixFrameAction hNL θ).range = 3 ^ 5 ∧
        ∃ (Q : GL (Fin 6) K) (hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
            (RankThree.PartOne.KCUnitaryModel.idGram K 6)),
          ∀ σ : Fin 6 → Kˣ, σ (0 : Fin 6) = 1 → (∀ k, σ k ^ 3 = 1) →
            ∃ b : Bs, TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
              (e6QTwoSixFrameAction hNL θ b) σ := by
  let β := e6QTwoSixFrameAction hNL θ
  have hker_le : Nat.card ↥β.ker ≤ 3 :=
    e6QTwoSixFrameAction_card_ker_le hNL θ hperf hBs hx hBL
  have hrange_le : Nat.card ↥β.range ≤ 3 ^ 5 :=
    e6QTwoSixFrameAction_card_range_le hK hNL θ hBs hI
  have hprod : Nat.card ↥β.ker * Nat.card ↥β.range = 3 ^ 6 := by
    rw [← hcard]
    exact Subgroup.card_ker_mul_card_range β
  have hker3 : Nat.card ↥β.ker = 3 := by
    by_contra hne
    have hle : Nat.card ↥β.ker ≤ 2 := by omega
    have hb : Nat.card ↥β.ker * Nat.card ↥β.range ≤ 2 * 3 ^ 5 :=
      Nat.mul_le_mul hle hrange_le
    norm_num at hprod hb
    omega
  have hrange5 : Nat.card ↥β.range = 3 ^ 5 := by
    rw [hker3] at hprod
    rw [show (3 : ℕ) ^ 6 = 3 * 3 ^ 5 by norm_num] at hprod
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) hprod
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  obtain ⟨Q, hQ, hQfr⟩ := TableBUD.exists_frame_inndiag (h := USixTwo.fieldDataFour hK) hK'
    (by norm_num : 3 ≤ 6) (by norm_num : (6, 2 ^ 1) ≠ (3, 2))
    (by norm_num : ¬(6 = 3 ∧ 2 ^ 1 = 2)) (by norm_num : Nat.Prime 3)
    (by norm_num : 3 ∣ 2 ^ 1 + 1)
    (e6QTwoSixFrameAction_isElemAbelian_range hNL θ hBs)
    (e6QTwoSixFrameAction_range_le_inndiag hK hNL θ hI) (by rw [hrange5]; norm_num)
  have hQ' : ∀ e : β.range, ∃ σ : Fin 6 → Kˣ, σ (0 : Fin 6) = 1 ∧
      (∀ k, σ k ^ 3 = 1) ∧
      (∀ k, ((σ k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1) ∧
      TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ (e : MulAut _) σ :=
    fun e => hQfr e.1 e.2
  choose σ hσ0 hσ3 hσn hσfr using hQ'
  let f : β.range → (Fin 5 → Kˣ) := fun e i => σ e (Fin.succAbove 0 i)
  have hf_inj : Function.Injective f := by
    intro e e' he
    have hσeq : σ e = σ e' := by
      funext k
      by_cases hk : k = 0
      · rw [hk, hσ0 e, hσ0 e']
      · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq (x := k) (y := (0 : Fin 6)) hk
        exact congrFun he i
    have h1 : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ (e : MulAut _) (σ e) := hσfr e
    have h2 : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ (e' : MulAut _) (σ e) :=
      hσeq ▸ hσfr e'
    exact Subtype.ext (TableBUD.FrameAct.unique (h := USixTwo.fieldDataFour hK)
      (Q := Q) (hQ := hQ) (hσ := hσn e) h1 h2)
  have hcardf : Nat.card (Fin 5 → Kˣ) = 3 ^ 5 := by
    rw [Nat.card_pi]
    have hunits : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hunits]
  have hbij : Function.Bijective f :=
    hf_inj.bijective_of_nat_card_le (by rw [hcardf, hrange5])
  refine ⟨hker3, hrange5, Q, hQ, fun τ hτ0 hτ3 => ?_⟩
  obtain ⟨e, he⟩ := hbij.2 (fun i => τ (Fin.succAbove 0 i))
  have hτe : σ e = τ := by
    funext k
    by_cases hk : k = 0
    · rw [hk, hσ0 e, hτ0]
    · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq (x := k) (y := (0 : Fin 6)) hk
      exact congrFun he i
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp e.2
  refine ⟨b, ?_⟩
  rw [hb]
  exact hτe ▸ hσfr e

theorem e6QTwoSixFrameAction_mem_inn_of_mem_sup {Bs L : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    {b : Bs} (hb : (b : G) ∈ L ⊔ Subgroup.centralizer (L : Set G)) :
    e6QTwoSixFrameAction hNL θ b ∈
      (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →*
        MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))).range := by
  let C := Subgroup.centralizer (L : Set G)
  let N := Subgroup.normalizer (L : Set G)
  let cj : L →* MulAut L := MulAut.conj
  have hLCN : L ⊔ C ≤ N :=
    sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer (L : Set G))
  have hL : L.subgroupOf N ≤ Subgroup.comap (Subgroup.normalizerMonoidHom L) cj.range := by
    intro y hy
    rw [Subgroup.mem_subgroupOf] at hy
    rw [Subgroup.mem_comap]
    exact ⟨⟨(y : G), hy⟩, by
      ext w
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply]
      rfl⟩
  have hC : C.subgroupOf N ≤ Subgroup.comap (Subgroup.normalizerMonoidHom L) cj.range := by
    intro y hy
    rw [Subgroup.mem_subgroupOf] at hy
    rw [Subgroup.mem_comap]
    exact ⟨1, by
      ext w
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply, one_mul, inv_one,
        mul_one]
      have hcomm := Subgroup.mem_centralizer_iff.mp hy (w : G) w.2
      calc (w : G) = ((w : G) * (y : G)) * (y : G)⁻¹ := by group
        _ = ((y : G) * (w : G)) * (y : G)⁻¹ := by rw [hcomm]
        _ = (y : G) * (w : G) * (y : G)⁻¹ := by group⟩
  have hsup : (L ⊔ C).subgroupOf N ≤ Subgroup.comap (Subgroup.normalizerMonoidHom L) cj.range := by
    rw [Subgroup.subgroupOf_sup (le_sup_left.trans hLCN) (le_sup_right.trans hLCN)]
    exact sup_le hL hC
  have hbN : (⟨(b : G), hLCN hb⟩ : N) ∈ (L ⊔ C).subgroupOf N :=
    Subgroup.mem_subgroupOf.mpr hb
  have hmem := hsup hbN
  rw [Subgroup.mem_comap] at hmem
  obtain ⟨l, hl⟩ := hmem
  have hact : e6QTwoBstarConjAction hNL b = MulAut.conj l := by
    ext y
    rw [e6QTwoBstarConjAction_apply, MulAut.conj_apply]
    have h1 : (MulAut.conj l) y =
        Subgroup.normalizerMonoidHom L ⟨(b : G), hLCN hb⟩ y := by
      rw [hl]
    calc (b : G) * (y : G) * (b : G)⁻¹
        = ((Subgroup.normalizerMonoidHom L ⟨(b : G), hLCN hb⟩ y : L) : G) :=
          (Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨(b : G), hLCN hb⟩ y).symm
      _ = ((MulAut.conj l y : L) : G) := by rw [← h1]
      _ = (l : G) * (y : G) * (l : G)⁻¹ := by
            rw [MulAut.conj_apply]
            simp
  rw [e6QTwoSixFrameAction_eq hNL θ b, hact, e6QTwoQuotCenterAutHom_conj,
    ← e6QTwoMulAutConjCongr θ (QuotientGroup.mk' (Subgroup.center L) l)]
  exact ⟨θ (QuotientGroup.mk' (Subgroup.center L) l), rfl⟩

theorem e6QTwoSixFrameAction_mem_sup_of_mem_inn {Bs L : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    {b : Bs} (hb : e6QTwoSixFrameAction hNL θ b ∈
      (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →*
        MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))).range) :
    (b : G) ∈ L ⊔ Subgroup.centralizer (L : Set G) := by
  let C := Subgroup.centralizer (L : Set G)
  obtain ⟨r, hr⟩ := hb
  obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) (θ.symm r)
  have hθl : θ (QuotientGroup.mk' (Subgroup.center L) l) = r := by
    rw [hl, θ.apply_symm_apply]
  have hact : e6QTwoBstarConjAction hNL b = MulAut.conj l := by
    apply e6QTwoQuotCenterAutHom_injective hperf
    apply (MulAut.congr θ).injective
    calc (MulAut.congr θ) (e6QTwoQuotCenterAutHom L (e6QTwoBstarConjAction hNL b))
        = e6QTwoSixFrameAction hNL θ b := (e6QTwoSixFrameAction_eq hNL θ b).symm
      _ = MulAut.conj r := hr.symm
      _ = MulAut.conj (θ (QuotientGroup.mk' (Subgroup.center L) l)) := by rw [hθl]
      _ = (MulAut.congr θ) (MulAut.conj (QuotientGroup.mk' (Subgroup.center L) l)) :=
            e6QTwoMulAutConjCongr θ _
      _ = (MulAut.congr θ) (e6QTwoQuotCenterAutHom L (MulAut.conj l)) := by
            rw [e6QTwoQuotCenterAutHom_conj]
  have hcent : (l : G)⁻¹ * (b : G) ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hval : (b : G) * (y : G) * (b : G)⁻¹ = (l : G) * (y : G) * (l : G)⁻¹ := by
      have h1 := congrArg (fun φ : MulAut L => (((φ ⟨y, hy⟩ : L) : G))) hact
      simpa only [MulAut.conj_apply, e6QTwoBstarConjAction_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] using h1
    calc (y : G) * ((l : G)⁻¹ * (b : G))
        = (y : G) * (l : G)⁻¹ * (b : G) := by group
      _ = (l : G)⁻¹ * ((l : G) * (y : G) * (l : G)⁻¹) * (b : G) := by group
      _ = (l : G)⁻¹ * ((b : G) * (y : G) * (b : G)⁻¹) * (b : G) := by rw [← hval]
      _ = (l : G)⁻¹ * (b : G) * (y : G) := by group
      _ = ((l : G)⁻¹ * (b : G)) * (y : G) := by group
  have hb_eq : (b : G) = (l : G) * ((l : G)⁻¹ * (b : G)) := by group
  rw [hb_eq]
  exact Subgroup.mul_mem_sup l.2 hcent

theorem e6QTwoSixFrameInnerPartCard (hK : Nat.card K = 4) {Bs L : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hrange : Nat.card ↥(e6QTwoSixFrameAction hNL θ).range = 3 ^ 5)
    {Q : GL (Fin 6) K} (hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
      (RankThree.PartOne.KCUnitaryModel.idGram K 6))
    (hfull : ∀ σ : Fin 6 → Kˣ, σ (0 : Fin 6) = 1 → (∀ k, σ k ^ 3 = 1) →
      ∃ b : Bs, TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
        (e6QTwoSixFrameAction hNL θ b) σ) :
    Nat.card ↥((MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →*
        MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))).range ⊓
        (e6QTwoSixFrameAction hNL θ).range) = 3 ^ 4 := by
  let β := e6QTwoSixFrameAction hNL θ
  let Inn := (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →*
    MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))).range
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hcinj : Function.Injective
      (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →*
        MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) :=
    CFSG.StandardType.mulAut_conj_injective
      (TableBUE.center_proj_eq_bot hK' (by norm_num : 3 ≤ 6) (by norm_num : (6, 2 ^ 1) ≠ (3, 2)))
  have hTle : (e6QTwoFrameTorusHom hK Q hQ).range.map
      (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →*
        MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) ≤ Inn ⊓ β.range := by
    intro e he
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp he
    constructor
    · exact ⟨r, rfl⟩
    · obtain ⟨σ, rfl⟩ := hr
      have hσ3 : ∀ k, σ.1 k ^ 3 = 1 := fun k => USixTwo.cube_unit_eq_one hK (σ.1 k)
      let c : Kˣ := (σ.1 (0 : Fin 6))⁻¹
      have hc3 : c ^ 3 = 1 := USixTwo.cube_unit_eq_one hK c
      let τ : Fin 6 → Kˣ := fun k => c * σ.1 k
      have hτ0 : τ (0 : Fin 6) = 1 := by
        show c * σ.1 0 = 1
        exact inv_mul_cancel _
      have hτ3 : ∀ k, τ k ^ 3 = 1 := by
        intro k
        rw [show τ k = c * σ.1 k from rfl, mul_pow, hc3, hσ3 k, one_mul]
      have hτn : ∀ k, ((τ k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1 := by
        intro k
        rw [show 2 ^ 1 + 1 = 3 by norm_num, ← Units.val_pow_eq_pow_val, hτ3 k, Units.val_one]
      obtain ⟨b, hb⟩ := hfull τ hτ0 hτ3
      have hfr : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
          (MulAut.conj (e6QTwoFrameTorusHom hK Q hQ σ)) τ :=
        TableBUD.FrameAct.smul (e6QTwoFrameActFrameTorusHom hK Q hQ σ) c
      have hEq : β b = MulAut.conj (e6QTwoFrameTorusHom hK Q hQ σ) :=
        TableBUD.FrameAct.unique (h := USixTwo.fieldDataFour hK) (Q := Q) (hQ := hQ)
          (hσ := hτn) hb hfr
      rw [← hEq]
      exact ⟨b, rfl⟩
  have hlower : 3 ^ 4 ≤ Nat.card ↥(Inn ⊓ β.range) := by
    have hcard : Nat.card ↥((e6QTwoFrameTorusHom hK Q hQ).range.map
        (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →*
          MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))))) =
        Nat.card ↥(e6QTwoFrameTorusHom hK Q hQ).range :=
      Subgroup.card_map_of_injective (f := (MulAut.conj :
        LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →*
          MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))))) hcinj
    have hle := Subgroup.card_le_of_le hTle
    rwa [hcard, e6QTwoCardRangeFrameTorusHom hK Q hQ] at hle
  have hninner : ∃ e ∈ β.range, e ∉ Inn := by
    have hunits : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
    haveI : Fintype Kˣ := Fintype.ofFinite Kˣ
    haveI : Nontrivial Kˣ := (Fintype.one_lt_card_iff_nontrivial (α := Kˣ)).mp (by
      rw [← Nat.card_eq_fintype_card, hunits]; norm_num)
    obtain ⟨ω, hω1⟩ := exists_ne (1 : Kˣ)
    have hω3 : ω ^ 3 = 1 := USixTwo.cube_unit_eq_one hK ω
    let σ : Fin 6 → Kˣ := Function.update (fun _ : Fin 6 => (1 : Kˣ)) (1 : Fin 6) ω
    have hσ0 : σ (0 : Fin 6) = 1 := by
      show Function.update (fun _ : Fin 6 => (1 : Kˣ)) (1 : Fin 6) ω 0 = 1
      rw [Function.update_apply, if_neg (by decide : (0 : Fin 6) ≠ 1)]
    have hσ3 : ∀ k, σ k ^ 3 = 1 := by
      intro k
      by_cases hk : k = 1
      · rw [show σ k = ω from by
          show Function.update (fun _ : Fin 6 => (1 : Kˣ)) (1 : Fin 6) ω k = ω
          rw [Function.update_apply, if_pos hk]]
        exact hω3
      · rw [show σ k = 1 from by
          show Function.update (fun _ : Fin 6 => (1 : Kˣ)) (1 : Fin 6) ω k = 1
          rw [Function.update_apply, if_neg hk]]
        exact one_pow 3
    obtain ⟨b, hb⟩ := hfull σ hσ0 hσ3
    refine ⟨β b, ⟨b, rfl⟩, ?_⟩
    rintro ⟨r, hr⟩
    obtain ⟨v, hv⟩ := InndiagSU.frameMk_surjective (USixTwo.fieldDataFour hK) Q hQ r
    have hinner : InndiagSU.IsSemilin (InndiagSU.frameMk (USixTwo.fieldDataFour hK) Q hQ)
        (MulAut.conj r) v 1 := by
      intro u w huw
      rw [MulAut.conj_apply, ← hv, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [huw]
      simp
    have hdiag : InndiagSU.IsSemilin (InndiagSU.frameMk (USixTwo.fieldDataFour hK) Q hQ)
        (MulAut.conj r) (SectionRank.OddCover.diagHom 6 σ) 1 := by
      rw [hr]
      exact hb
    have hvu : (v : GL (Fin 6) K) ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
        (RankThree.PartOne.KCUnitaryModel.idGram K 6) :=
      TableBUE.unitarySU_le_primeFormUnitary (USixTwo.fieldDataFour hK) v.2
    have hσu : SectionRank.OddCover.diagHom 6 σ ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
        (RankThree.PartOne.KCUnitaryModel.idGram K 6) :=
      TableBUD.diagHom_mem_primeFormUnitary (USixTwo.fieldDataFour hK) (fun k => by
        rw [show 2 ^ 1 + 1 = 3 by norm_num, ← Units.val_pow_eq_pow_val, hσ3 k, Units.val_one])
    obtain ⟨c, hc⟩ := TableBUD.IsSemilin.eq_smul (h := USixTwo.fieldDataFour hK) hK'
      (by norm_num : 3 ≤ 6) (by norm_num : (6, 2 ^ 1) ≠ (3, 2))
      (by norm_num : Nat.Prime 3) (by norm_num : 3 ∣ 2 ^ 1 + 1) hQ hσu hvu hdiag hinner
    have hdetv : ((v : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 :=
      (CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff (USixTwo.fieldDataFour hK)).mp v.2 |>.1
    have hdetdiag : Matrix.GeneralLinearGroup.det (SectionRank.OddCover.diagHom 6 σ) =
        ∏ k, σ k := by
      ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, SectionRank.OddCover.det_diagHom,
        Units.coe_prod]
    have hdetv' : Matrix.GeneralLinearGroup.det (v : GL (Fin 6) K) = 1 := by
      ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, hdetv, Units.val_one]
    have hdetGL := congrArg (Matrix.GeneralLinearGroup.det) hc
    rw [hdetdiag, map_mul, Matrix.GeneralLinearGroup.det_scalar, hdetv', mul_one,
      Fintype.card_fin] at hdetGL
    have hc3 : c ^ 3 = 1 := USixTwo.cube_unit_eq_one hK c
    have hc6 : c ^ 6 = 1 := by rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, hc3, one_pow]
    have hprod1 : ∏ k, σ k = 1 := by
      rw [hdetGL, hc6]
    have hprod_eq : ∏ k, σ k = ω := by
      rw [Fintype.prod_eq_single 1]
      · rw [show σ 1 = ω from by
          show Function.update (fun _ : Fin 6 => (1 : Kˣ)) (1 : Fin 6) ω 1 = ω
          rw [Function.update_apply, if_pos rfl]]
      · intro k hk
        rw [show σ k = 1 from by
          show Function.update (fun _ : Fin 6 => (1 : Kˣ)) (1 : Fin 6) ω k = 1
          rw [Function.update_apply, if_neg hk]]
    rw [hprod_eq] at hprod1
    exact hω1 hprod1
  have hproper : Inn ⊓ β.range ≠ β.range := by
    intro heq
    obtain ⟨e, he, hne⟩ := hninner
    exact hne (heq.symm ▸ he).1
  have hdvd : Nat.card ↥(Inn ⊓ β.range) ∣ 3 ^ 5 := by
    have h := Subgroup.card_subgroup_dvd_card ((Inn ⊓ β.range).subgroupOf β.range)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right :
      Inn ⊓ β.range ≤ β.range)).toEquiv] at h
    rwa [show Nat.card ↥β.range = 3 ^ 5 from hrange] at h
  have hupper : Nat.card ↥(Inn ⊓ β.range) ≤ 3 ^ 4 := by
    obtain ⟨k, hk5, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hne5 : Nat.card ↥(Inn ⊓ β.range) ≠ 3 ^ 5 := by
      intro h5
      apply hproper
      exact Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h5, hrange])
    have hlt : Nat.card ↥(Inn ⊓ β.range) < 3 ^ 5 :=
      lt_of_le_of_ne (Nat.le_of_dvd (by norm_num) hdvd) hne5
    rw [hk] at hlt ⊢
    exact Nat.pow_le_pow_right (by norm_num) (by
      have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp hlt
      omega)
  exact le_antisymm hupper hlower


theorem e6QTwoSixCardInfSupCentralizer (hK : Nat.card K = 4) {Bs L : Subgroup G} {x : G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤) (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 6)
    (hx : x ∈ Bs)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ) :
    Nat.card ↥(Bs ⊓ (L ⊔ Subgroup.centralizer (L : Set G))) = 3 ^ 5 := by
  let β := e6QTwoSixFrameAction hNL θ
  let Inn := (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →*
    MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))).range
  obtain ⟨hker3, hrange5, Q, hQ, hfull⟩ :=
    e6QTwoSixFrameFullDiagonal hK θ hperf hBs hcard hx hBL hNL hI
  have hinner : Nat.card ↥(Inn ⊓ β.range) = 3 ^ 4 :=
    e6QTwoSixFrameInnerPartCard hK θ hNL hrange5 hQ hfull
  have hpre : (Bs ⊓ (L ⊔ Subgroup.centralizer (L : Set G))).subgroupOf Bs = Inn.comap β := by
    ext b
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_comap, MonoidHom.mem_range]
    constructor
    · rintro ⟨-, hb⟩
      exact e6QTwoSixFrameAction_mem_inn_of_mem_sup θ hNL hb
    · intro hb
      exact ⟨b.2, e6QTwoSixFrameAction_mem_sup_of_mem_inn θ hperf hNL hb⟩
  let β' : Bs →* β.range := β.codRestrict β.range (fun b => ⟨b, rfl⟩)
  have hβ'surj : Function.Surjective β' := by
    rintro ⟨e, he⟩
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp he
    exact ⟨b, Subtype.ext hb⟩
  let Isub : Subgroup β.range := Inn.subgroupOf β.range
  have hcomap : Isub.comap β' = Inn.comap β := by
    ext b
    change β b ∈ Inn ↔ β b ∈ Inn
    rfl
  have hinnerSub : Nat.card ↥Isub = 3 ^ 4 := by
    rw [show Isub = (Inn ⊓ β.range).subgroupOf β.range from
      (Subgroup.inf_subgroupOf_right Inn β.range).symm]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : Inn ⊓ β.range ≤ β.range)).toEquiv, hinner]
  have hcardpre : Nat.card ↥(Inn.comap β) =
      Nat.card ↥β.ker * Nat.card ↥Isub := by
    have h := CFSG.GroupTheory.card_comap_eq_card_ker_mul_card β' hβ'surj Isub
    have hker : β'.ker = β.ker :=
      MonoidHom.ker_codRestrict β β.range (fun b => by
        rw [MonoidHom.mem_range]
        exact ⟨b, rfl⟩)
    rw [hcomap, hker] at h
    exact h
  have hsubcard : Nat.card ↥(Bs ⊓ (L ⊔ Subgroup.centralizer (L : Set G))) =
      Nat.card ↥((Bs ⊓ (L ⊔ Subgroup.centralizer (L : Set G))).subgroupOf Bs) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : Bs ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) ≤ Bs)).toEquiv).symm
  rw [hsubcard, hpre, hcardpre, hker3, hinnerSub]
  norm_num
end CFSG.StandardType.E6QTwo

end
