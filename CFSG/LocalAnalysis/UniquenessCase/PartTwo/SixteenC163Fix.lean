module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Fix7
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165SevenA
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ya
import CFSG.Quasithin.Background.CommVBasics

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

namespace C163

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Matrix commutatorElement Pointwise

private theorem natTensor_bijective {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    (hL : Nat.card ↥L = 254016) (hT : NatTensor L (commSub ⊤ L) ⊥ 2 3) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 8 ∧
      ∃ π : (↥(StatedSL 2 K) × ↥(StatedSL 2 K)) →* ↥L, Function.Bijective π := by
  classical
  obtain ⟨K, _, _, hK, hReal⟩ := hT
  obtain ⟨π, hVia⟩ := hReal
  obtain ⟨hπsurj, -, -, -, -, -, -, -, -, -, -⟩ := hVia
  haveI : Fintype K := Fintype.ofFinite K
  have hK8 : Nat.card K = 8 := by rw [hK]; norm_num
  have hcardDom : Nat.card (FFModel.tensorNat 2 K).Gam = 254016 := by
    show Nat.card (↥(StatedSL 2 K) × ↥(StatedSL 2 K)) = 254016
    rw [Nat.card_prod, CFSG.Open.StatedAPI.card_statedSL_two, hK8]
    norm_num
  haveI : Finite (FFModel.tensorNat 2 K).Gam :=
    show Finite (↥(StatedSL 2 K) × ↥(StatedSL 2 K)) from inferInstance
  have hπbij : Function.Bijective π :=
    hπsurj.bijective_of_nat_card_le (by rw [hcardDom, hL])
  exact ⟨K, inferInstance, inferInstance, hK8, π, hπbij⟩

private theorem exists_orderOf_seven_fix_commSub {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} (hL : Nat.card ↥L = 254016)
    (hT : NatTensor L (commSub ⊤ L) ⊥ 2 3) {w : W} (hw : w ∈ commSub ⊤ L) :
    ∃ x ∈ L, orderOf x = 7 ∧ x w = w := by
  classical
  by_cases h1 : w = 1
  · rw [h1]
    haveI : Finite ↥L := Nat.finite_of_card_ne_zero (by rw [hL]; norm_num)
    haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 7 (by rw [hL]; norm_num)
    exact ⟨(x : MulAut W), x.2, by rw [Subgroup.orderOf_coe, hx], map_one (x : MulAut W)⟩
  · obtain ⟨K, _, _, hK, hReal⟩ := hT
    obtain ⟨π, hVia⟩ := hReal
    obtain ⟨hπsurj, -, -, hUinv, -, -, -, β, -, hβ1, hβint⟩ := hVia
    haveI : Fintype K := Fintype.ofFinite K
    have hK8 : Nat.card K = 8 := by rw [hK]; norm_num
    have hcardDom : Nat.card (FFModel.tensorNat 2 K).Gam = 254016 := by
      show Nat.card (↥(StatedSL 2 K) × ↥(StatedSL 2 K)) = 254016
      rw [Nat.card_prod, CFSG.Open.StatedAPI.card_statedSL_two, hK8]
      norm_num
    haveI : Finite (FFModel.tensorNat 2 K).Gam :=
      show Finite (↥(StatedSL 2 K) × ↥(StatedSL 2 K)) from inferInstance
    have hπbij : Function.Bijective π :=
      hπsurj.bijective_of_nat_card_le (by rw [hcardDom, hL])
    have hβinj : Function.Injective β := by
      intro a b hab
      have h1 : β (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
      have h2 : ((a * b⁻¹ : ↥(commSub ⊤ L)) : W) ∈ (⊥ : Subgroup W) :=
        (hβ1 (a * b⁻¹)).1 h1
      rw [Subgroup.mem_bot] at h2
      have h3 : a * b⁻¹ = 1 := Subtype.ext h2
      rwa [mul_inv_eq_one] at h3
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨w, hw⟩)
    let X : Matrix (Fin 2) (Fin 2) K :=
      Multiplicative.toAdd (m : (FFModel.tensorNat 2 K).Amb)
    have hX : X ≠ 0 := by
      intro hX0
      have hm1 : m = 1 := by
        apply Subtype.ext
        have h : Multiplicative.ofAdd X = (m : (FFModel.tensorNat 2 K).Amb) := rfl
        rw [← h, hX0]
        rfl
      have hβw1 : β ⟨w, hw⟩ = 1 := by
        rw [← hm, hm1]
        rfl
      exact h1 (Subgroup.mem_bot.mp ((hβ1 ⟨w, hw⟩).1 hβw1))
    obtain ⟨p, hp_ne, hp7, hpX⟩ := OmegaModel.exists_sl2_pair_fix (K := K) hK8 hX
    let s := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K
    let γ : (FFModel.tensorNat 2 K).Gam := (s p.1, s p.2)
    have hp17 : p.1 ^ 7 = 1 := by simpa using congrArg Prod.fst hp7
    have hp27 : p.2 ^ 7 = 1 := by simpa using congrArg Prod.snd hp7
    have hγne : γ ≠ 1 := by
      intro hγ
      apply hp_ne
      have hγ' : (s p.1, s p.2) = (1 : ↥(StatedSL 2 K) × ↥(StatedSL 2 K)) := hγ
      have h1 : s p.1 = 1 := by simpa using (Prod.ext_iff.mp hγ').1
      have h2 : s p.2 = 1 := by simpa using (Prod.ext_iff.mp hγ').2
      exact Prod.ext ((MulEquiv.map_eq_one_iff s).mp h1) ((MulEquiv.map_eq_one_iff s).mp h2)
    have hγ7 : γ ^ 7 = 1 := by
      apply Prod.ext
      · show (s p.1) ^ 7 = 1
        rw [← map_pow, hp17, map_one]
      · show (s p.2) ^ 7 = 1
        rw [← map_pow, hp27, map_one]
    haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    have hordγ : orderOf γ = 7 := orderOf_eq_prime hγ7 hγne
    have hcoe1 : ((γ.1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        (p.1 : Matrix (Fin 2) (Fin 2) K) :=
      CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe 2 K p.1
    have hcoe2 : ((γ.2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        (p.2 : Matrix (Fin 2) (Fin 2) K) :=
      CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe 2 K p.2
    have hact : (FFModel.tensorNat 2 K).act γ (m : (FFModel.tensorNat 2 K).Amb) =
        (m : (FFModel.tensorNat 2 K).Amb) := by
      change Multiplicative.ofAdd
          (((γ.1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * X *
            ((γ.2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ) = Multiplicative.ofAdd X
      rw [hcoe1, hcoe2, hpX]
    have hmemU : ((π γ : ↥L) : MulAut W) w ∈ commSub ⊤ L := hUinv (π γ) w hw
    have hmemsec : (FFModel.tensorNat 2 K).act γ (m : (FFModel.tensorNat 2 K).Amb) ∈
        (FFModel.tensorNat 2 K).sec := Subgroup.mem_top _
    have hβeq : β ⟨((π γ : ↥L) : MulAut W) w, hmemU⟩ = β ⟨w, hw⟩ := by
      rw [hβint γ ⟨w, hw⟩ m hmemU hmemsec hm.symm, hm.symm]
      congr 1
      apply Subtype.ext
      exact hact
    have hfix : ((π γ : ↥L) : MulAut W) w = w := congrArg Subtype.val (hβinj hβeq)
    have hordπ : orderOf (π γ) = 7 := by
      rw [orderOf_injective π hπbij.1 γ, hordγ]
    exact ⟨((π γ : ↥L) : MulAut W), (π γ).2, by rw [Subgroup.orderOf_coe, hordπ], hfix⟩

private theorem center_eq_bot_of_natTensor {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    (hL : Nat.card ↥L = 254016) (hT : NatTensor L (commSub ⊤ L) ⊥ 2 3) :
    Subgroup.center ↥L = ⊥ := by
  classical
  obtain ⟨K, _, _, hK8, π, hπbij⟩ := natTensor_bijective hL hT
  haveI : Fintype K := Fintype.ofFinite K
  let e : (↥(StatedSL 2 K) × ↥(StatedSL 2 K)) ≃* ↥L := MulEquiv.ofBijective π hπbij
  have hcenterDom : Subgroup.center (↥(StatedSL 2 K) × ↥(StatedSL 2 K)) = ⊥ := by
    rw [Subgroup.center_prod]
    have h1 : Subgroup.center ↥(StatedSL 2 K) = ⊥ :=
      CFSG.LocalAnalysis.UniquenessCase.UC22.P22y.center_eq_bot_of_isL2Ev
        (X := ↥(StatedSL 2 K)) (n := 3)
        ⟨K, inferInstance, inferInstance, by rw [hK8]; norm_num, ⟨MulEquiv.refl _⟩⟩
    rw [h1, Subgroup.bot_prod_bot]
  rw [show Subgroup.center ↥L =
      (Subgroup.center (↥(StatedSL 2 K) × ↥(StatedSL 2 K))).map e.toMonoidHom from
    (Subgroup.map_center_eq e).symm, hcenterDom, Subgroup.map_bot]

theorem exists_orderOf_seven_fix {W : Type} [CommGroup W] {A L : Subgroup (MulAut W)}
    (hgen : (⨆ X ∈ conjSubs A (commSub ⊤ L), X) = ⊤)
    (hcomm : ∀ g ∈ A, g ∉ normalizer (L : Set (MulAut W)) →
      commSub (commSub ⊤ L) (L.map (MulAut.conj g).toMonoidHom) = ⊥)
    (hL : Nat.card ↥L = 254016) (hT : NatTensor L (commSub ⊤ L) ⊥ 2 3) (w : W) :
    ∃ x ∈ L, orderOf x = 7 ∧ x w = w := by
  classical
  have hle : (⊤ : Subgroup W) ≤ commSub ⊤ L ⊔ fixV L := by
    refine le_trans (le_of_eq hgen.symm) ?_
    refine iSup_le fun X => iSup_le fun hX => ?_
    obtain ⟨g, hgA, rfl⟩ := hX
    intro x hx
    obtain ⟨u, hu, rfl⟩ := hx
    by_cases hgN : g ∈ normalizer (L : Set (MulAut W))
    · rw [← commV_eq_commSub] at hu ⊢
      exact Subgroup.mem_sup_left (commV_apply_mem_of_mem_normalizer hgN hu)
    · refine Subgroup.mem_sup_right ?_
      rw [mem_fixV]
      intro l hl
      have hgN' : g⁻¹ ∉ normalizer (L : Set (MulAut W)) := fun h => hgN (inv_mem_iff.mp h)
      have hfix : commSub ⊤ L ≤ fixV (L.map (MulAut.conj g⁻¹).toMonoidHom) :=
        commSub_eq_bot_iff.mp (hcomm g⁻¹ (A.inv_mem hgA) hgN')
      have hmem : g⁻¹ * l * g ∈ L.map (MulAut.conj g⁻¹).toMonoidHom := by
        refine ⟨l, hl, ?_⟩
        simp [MulAut.conj_apply]
      have h := (mem_fixV.mp (hfix hu)) (g⁻¹ * l * g) hmem
      have h2 : (g⁻¹ * l * g) u = g⁻¹ (l (g u)) := by
        rw [MulAut.mul_apply, MulAut.mul_apply]
      have h3 : g ((g⁻¹ * l * g) u) = g u := congrArg g h
      rw [h2, MulAut.apply_inv_self] at h3
      exact h3
  obtain ⟨w', hw'U, c, hc, hw⟩ := Subgroup.mem_sup.mp (hle (Subgroup.mem_top w))
  obtain ⟨x, hxL, hxord, hxfix⟩ := exists_orderOf_seven_fix_commSub hL hT hw'U
  refine ⟨x, hxL, hxord, ?_⟩
  rw [← hw, map_mul, hxfix, (mem_fixV.mp hc) x hxL, hw]

theorem exists_noncyclic_fix {W : Type} [CommGroup W] [Finite W] {A L : Subgroup (MulAut W)}
    {t : MulAut W} (hW : Conc4_136W A t L) (hLA : L ≤ A) (hL : Nat.card ↥L = 254016)
    (hT : NatTensor L (commSub ⊤ L) ⊥ 2 3) {φ : MulAut W} (hφ : φ ∈ A)
    (hφN : φ ∉ normalizer (L : Set (MulAut W))) (w : W) :
    ∃ E : Subgroup (MulAut W), E ≤ A ∧ IsPGroup 7 ↥E ∧ ¬ IsCyclic ↥E ∧ ∀ x ∈ E, x w = w := by
  classical
  have hgen : (⨆ X ∈ conjSubs A (commSub ⊤ L), X) = ⊤ := hW.1
  have hcomm : ∀ g ∈ A, g ∉ normalizer (L : Set (MulAut W)) →
      commSub (commSub ⊤ L) (L.map (MulAut.conj g).toMonoidHom) = ⊥ :=
    fun g hg hgN => (hW.2.1 g hg hgN).2
  obtain ⟨x, hxL, hxord, hxw⟩ := exists_orderOf_seven_fix hgen hcomm hL hT w
  obtain ⟨x', hx'L, hx'ord, hx'w⟩ := exists_orderOf_seven_fix hgen hcomm hL hT (φ⁻¹ w)
  let y : MulAut W := φ * x' * φ⁻¹
  have hyLmap : y ∈ L.map (MulAut.conj φ).toMonoidHom :=
    ⟨x', hx'L, by simp [y, MulAut.conj_apply]⟩
  have hyA : y ∈ A := A.mul_mem (A.mul_mem hφ (hLA hx'L)) (A.inv_mem hφ)
  have hyw : y w = w := by
    have h : x' (φ⁻¹ w) = φ⁻¹ w := hx'w
    simp only [y, MulAut.mul_apply, h, MulAut.apply_inv_self]
  have hx'ne : x' ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx'ord
    norm_num at hx'ord
  have hy7 : y ^ 7 = 1 := by
    have hx'7 : x' ^ 7 = 1 := by rw [← hx'ord]; exact pow_orderOf_eq_one x'
    rw [show y = MulAut.conj φ x' from rfl, ← map_pow, hx'7, map_one]
  have hbot : ⁅L, L.map (MulAut.conj φ).toMonoidHom⁆ = ⊥ := (hW.2.1 φ hφ hφN).1
  have hxy : Commute x y := by
    have hmem : ⁅x, y⁆ ∈ ⁅L, L.map (MulAut.conj φ).toMonoidHom⁆ :=
      Subgroup.commutator_mem_commutator hxL hyLmap
    rw [hbot, Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_commute.mp hmem
  have hy_not : y ∉ Subgroup.zpowers x := by
    intro hy
    have hyL : y ∈ L := (Subgroup.zpowers_le.2 hxL) hy
    have hycomm : ∀ l ∈ L, l * y = y * l := by
      intro l hl
      have hmem : ⁅l, y⁆ ∈ ⁅L, L.map (MulAut.conj φ).toMonoidHom⁆ :=
        Subgroup.commutator_mem_commutator hl hyLmap
      rw [hbot, Subgroup.mem_bot] at hmem
      exact commutatorElement_eq_one_iff_mul_comm.mp hmem
    have hycenter : (⟨y, hyL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      exact hycomm (l : MulAut W) l.2
    have hy1 : y = 1 := by
      have hcenter := center_eq_bot_of_natTensor hL hT
      rw [hcenter, Subgroup.mem_bot] at hycenter
      exact congrArg Subtype.val hycenter
    have hyne : y ≠ 1 := by
      intro hy1'
      apply hx'ne
      have h : φ * x' * φ⁻¹ = 1 := hy1'
      calc x' = φ⁻¹ * (φ * x' * φ⁻¹) * φ := by group
        _ = 1 := by rw [h]; group
    exact hyne hy1
  refine ⟨Subgroup.zpowers x ⊔ Subgroup.zpowers y, ?_, ?_, ?_, ?_⟩
  · refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]; exact hLA hxL
    · rw [Subgroup.zpowers_le]; exact hyA
  · exact Om8Seven.isPGroup_sup_zpowers (p := 7) (by rw [← hxord]; exact pow_orderOf_eq_one x)
      hy7 hxy
  · exact Om8Seven.not_isCyclic_sup_zpowers (p := 7) Nat.prime_seven hxord hy7 hxy hy_not
  · intro g hg
    have hstab : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ MulAction.stabilizer (MulAut W) w := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]
        show x • w = w
        exact hxw
      · rw [Subgroup.zpowers_le]
        show y • w = w
        exact hyw
    have hmem := hstab hg
    rw [MulAction.mem_stabilizer_iff] at hmem
    exact hmem

end C163

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
