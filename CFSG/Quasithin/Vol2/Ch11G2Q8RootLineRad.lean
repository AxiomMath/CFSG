module

public import CFSG.Quasithin.Vol2.Ch11G2Q8RadLift
public import CFSG.Quasithin.Vol2.Ch11G2Q8RootLine
public import CFSG.Quasithin.Vol2.Ch10SecABasicAut

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix
open scoped IsMulCommutative commutatorElement

theorem factG2RootLineRad_holds : FactG2RootLineRad := by
  intro G _ _ L V X T V₁ V₂ V₃ n hfl _ E hEX hEab hm
  obtain ⟨_, K, _, _, _, hK, π, f, hf, c₀, hc0, hc1, g, -, -, hV₂, -⟩ := exists_coord_flagG2 hfl
  have hn := hfl.two_le
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hLV := hfl.le_normalizer
  have h₂ : V₂ ≤ V := hfl.le₂₃.trans hfl.le₃
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsq : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hfl.elem.2 w w.2)
  have hEV : E ≤ Subgroup.normalizer (V : Set G) := hEX.trans inf_le_right
  have hZfix : ∀ h ∈ autOn L V, ∀ z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V,
      h z = z := by
    intro h hh z hz
    obtain ⟨y, hyL, hyV, rfl⟩ := SecA.mem_autOn_iff.mp hh
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hz
    apply Subtype.ext
    rw [SecA.conjV_apply_coe, hz y hyL, mul_inv_cancel_right]
  have hcomm : commV (autOn L V) = ⊤ := by
    rw [Ch10.SecA.commV_autOn_eq hLV, hfl.commutator_eq, Subgroup.subgroupOf_self]
  obtain ⟨CE, hCE⟩ : ∃ CE : Subgroup ↥V,
      CE = (V ⊓ Subgroup.centralizer (E : Set G)).subgroupOf V := ⟨_, rfl⟩
  have hmem_CE : ∀ w : ↥V, w ∈ CE ↔ ∀ e ∈ E, e * (w : G) = w * e := by
    intro w
    rw [hCE, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    exact ⟨fun h => h.2, fun h => ⟨w.2, h⟩⟩
  have hidx : CE.index = Nat.card K ^ 2 := by
    obtain ⟨N, hN⟩ := IsPGroup.iff_card.mp (show IsPGroup 2 ↥V from
      fun w => ⟨1, by rw [pow_one]; exact hsq w⟩)
    have hdvd : CE.index ∣ 2 ^ N := by
      rw [← hN]
      exact CE.index_dvd_card
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hm' : padicValNat 2 CE.index = 2 * n := by
      rw [hCE]
      exact hm
    rw [hk, padicValNat.prime_pow] at hm'
    rw [hk, hm', hK, ← pow_mul, mul_comm]
  have hZidx : ((Subgroup.centralizer (L : Set G)).subgroupOf V).index = Nat.card K ^ 6 := by
    have htop : hf.img ⊤ = ⊤ := by
      rw [eq_top_iff]
      intro x _
      obtain ⟨w, rfl⟩ := hf.surj x
      exact hf.mem_img.mpr ⟨w, Subgroup.mem_top w, rfl⟩
    have h1 := hf.card_img (U := ⊤)
    rw [Subgroup.relIndex_top_right, htop, AddSubgroup.card_top, card_Q] at h1
    exact h1.symm
  have hcardCE : Nat.card K ^ 4 ≤ Nat.card (hf.img CE) := by
    rw [hf.card_img]
    have h1 := Subgroup.relIndex_mul_index
      (inf_le_right : (Subgroup.centralizer (L : Set G)).subgroupOf V ⊓ CE ≤ CE)
    rw [Subgroup.inf_relIndex_right, hidx] at h1
    have h3 : ((Subgroup.centralizer (L : Set G)).subgroupOf V).index ≤
        ((Subgroup.centralizer (L : Set G)).subgroupOf V ⊓ CE).index :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        (Subgroup.index_dvd_of_le inf_le_left)
    rw [← h1, hZidx, show Nat.card K ^ 6 = Nat.card K ^ 4 * Nat.card K ^ 2 by
      rw [← pow_add]] at h3
    exact Nat.le_of_mul_le_mul_right h3 (by positivity)
  have key : ∀ e (he : e ∈ E), ∃ γ : ↥(cayleyGroup K), γ * γ = 1 ∧
      ∀ w, f (SecA.conjV V e (hEX he).2 w) = g2Act γ (f w) := by
    intro e he
    obtain ⟨c, γ, σ, hc, hcγ⟩ := exists_smul_frob_conjV hf hc0 hc1 hK hn hfl.normalizer_le
      (hEX he)
    have hfixE : ∀ w ∈ CE, SecA.conjV V e (hEX he).2 w = w := by
      intro w hw
      apply Subtype.ext
      rw [SecA.conjV_apply_coe, (hmem_CE w).mp hw e he, mul_inv_cancel_right]
    have hσ : ∀ θ, σ θ = θ := by
      by_contra hσ
      obtain ⟨θ, hθ⟩ := not_forall.mp hσ
      let Te : (Ix3 → K) →+ (Ix3 → K) :=
        { toFun := fun x => c • g2Act γ (frobQ σ x)
          map_zero' := by
            rw [show frobQ (σ : K →+* K) 0 = 0 from funext fun j => map_zero σ, map_zero,
              smul_zero]
          map_add' := fun x y => by
            rw [show frobQ (σ : K →+* K) (x + y) = frobQ σ x + frobQ σ y from
              funext fun j => map_add σ (x j) (y j), map_add, smul_add] }
      have hTe : ∀ (a : K) (x : Ix3 → K), Te (a • x) = (σ : K →+* K) a • Te x := by
        intro a x
        show c • g2Act γ (frobQ σ (a • x)) = (σ : K →+* K) a • (c • g2Act γ (frobQ σ x))
        rw [frobQ_smul, g2Act_smul, smul_comm]
      have h1 := card_fix_sq_le Te (σ : K →+* K) hθ hTe
      have h3 : Nat.card (hf.img CE) ≤ Nat.card {x : Ix3 → K // Te x = x} := by
        refine Nat.card_le_card_of_injective (fun x => ⟨x.1, ?_⟩) ?_
        · obtain ⟨w, hw, hwx⟩ := hf.mem_img.mp x.2
          show c • g2Act γ (frobQ σ x.1) = x.1
          rw [← hwx, ← hcγ, hfixE _ hw]
        · intro x x' h
          have h' := congrArg Subtype.val h
          exact Subtype.ext h'
      have h3' := hcardCE.trans h3
      rw [card_Q] at h1
      have h4 : Nat.card K ^ 4 * Nat.card K ^ 4 ≤ Nat.card K ^ 6 :=
        le_trans (Nat.mul_le_mul h3' h3') (by rw [← sq]; exact h1)
      rw [← pow_add] at h4
      have h5 : Nat.card K ^ 6 < Nat.card K ^ (4 + 4) := Nat.pow_lt_pow_right hq (by norm_num)
      omega
    have hfrob : ∀ x, frobQ (σ : K →+* K) x = x := fun x => funext fun j => hσ (x j)
    have hcγ' : ∀ w, f (SecA.conjV V e (hEX he).2 w) = c • g2Act γ (f w) := fun w => by
      rw [hcγ, hfrob]
    have hee : ∀ w, SecA.conjV V e (hEX he).2 (SecA.conjV V e (hEX he).2 w) = w := by
      intro w
      have he2 : e * e = 1 := by
        have := hEab.2 e he
        rwa [sq] at this
      apply Subtype.ext
      rw [SecA.conjV_apply_coe, SecA.conjV_apply_coe,
        show e * (e * (w : G) * e⁻¹) * e⁻¹ = (e * e) * w * (e * e)⁻¹ by group, he2]
      group
    have hγγ : ∀ x, g2Act (γ * γ) x = (c * c)⁻¹ • x := by
      intro x
      obtain ⟨w, rfl⟩ := hf.surj x
      have h1 := congrArg f (hee w)
      rw [hcγ', hcγ', g2Act_smul, smul_smul] at h1
      rw [g2Act_mul_apply]
      conv_rhs => rw [← h1]
      rw [smul_smul, inv_mul_cancel₀ (mul_ne_zero hc hc), one_smul]
    have hcc : (c * c)⁻¹ = 1 := scalar_eq_one hγγ
    have hc1' : c = 1 := by
      have h3 : c * c = 1 := by rw [← inv_inv (c * c), hcc, inv_one]
      have h4 : (c - 1) ^ 2 = 0 := by linear_combination h3 + (1 - c) * h2
      exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h4)
    refine ⟨γ, cayley_eq_one fun x => by rw [hγγ, hcc, one_smul], fun w => ?_⟩
    rw [hcγ', hc1', one_smul]
  choose γe hγe1 hγe using key
  have hfixCE : ∀ e (he : e ∈ E), ∀ y ∈ hf.img CE, g2Act (γe e he) y = y := by
    intro e he y hy
    obtain ⟨w, hw, rfl⟩ := hf.mem_img.mp hy
    rw [← hγe e he]
    congr 1
    apply Subtype.ext
    rw [SecA.conjV_apply_coe, (hmem_CE w).mp hw e he, mul_inv_cancel_right]
  have hlong : ∀ e (he : e ∈ E), γe e he ≠ 1 → ∃ x : ↥(cayleyGroup K),
      γe e he = x * tL 1 * x⁻¹ ∧ ∀ y, InC (g2Act x⁻¹ y) ↔ y ∈ hf.img CE := by
    intro e he hne
    have hfix : Nat.card K ^ 4 ≤ Nat.card (fixQ (γe e he)) := by
      refine hcardCE.trans (Nat.card_le_card_of_injective
        (fun y => ⟨y.1, mem_fixQ.mpr (hfixCE e he _ y.2)⟩) ?_)
      intro y y' h
      have h' := congrArg Subtype.val h
      exact Subtype.ext h'
    obtain ⟨x, hx⟩ := eq_conj_tL_of_fix (hγe1 e he) hne hfix
    have hmemC : ∀ y ∈ hf.img CE, InC (g2Act x⁻¹ y) := by
      intro y hy
      rw [← mem_fixQ_conj_tL, ← hx]
      exact mem_fixQ.mpr (hfixCE e he y hy)
    refine ⟨x, hx, fun y => ⟨fun hy => ?_, hmemC y⟩⟩
    let φ : hf.img CE → {y : Ix3 → K // InC (g2Act x⁻¹ y)} := fun y => ⟨y.1, hmemC _ y.2⟩
    have hinj : Function.Injective φ := by
      intro y y' h
      have h' := congrArg Subtype.val h
      exact Subtype.ext h'
    have hbij := (Nat.bijective_iff_injective_and_card φ).mpr ⟨hinj,
      le_antisymm (Nat.card_le_card_of_injective φ hinj) ((card_inC_le x).trans hcardCE)⟩
    obtain ⟨y', hy'⟩ := hbij.2 ⟨y, hy⟩
    have h1 : y'.1 = y := congrArg Subtype.val hy'
    rw [← h1]
    exact y'.2
  have hlift : ∀ e (he : e ∈ E), SecA.conjV V e (hEX he).2 =
      ((rhoG hc0 hc1 π (γe e he) : ↥(autOn L V)) : MulAut ↥V) := fun e he =>
    eq_rhoG_of_modZ hf hc0 hc1 hcomm (fun z hz h hh => hZfix h hh z hz)
      (fun h hh => conjV_mul_conjV_inv_mem (hfl.normalizer_le (hEX he)) (hEX he).2 hh)
      (hγe e he)
  obtain ⟨e₀, he₀, hne₀⟩ : ∃ e, ∃ he : e ∈ E, γe e he ≠ 1 := by
    by_contra hall
    have htop : CE = ⊤ := by
      rw [eq_top_iff]
      intro w _
      rw [hmem_CE]
      intro e he
      have h1 : γe e he = 1 := by
        by_contra h1
        exact hall ⟨e, he, h1⟩
      have h3 : SecA.conjV V e (hEX he).2 w = w := by
        rw [hlift e he, h1, map_one, Subgroup.coe_one, MulAut.one_apply]
      have h4 := congrArg Subtype.val h3
      rw [SecA.conjV_apply_coe] at h4
      calc e * (w : G) = e * w * e⁻¹ * e := by group
        _ = w * e := by rw [h4]
    have h1 : CE.index = 1 := by rw [htop, Subgroup.index_top]
    rw [hidx] at h1
    have : 1 < Nat.card K ^ 2 := Nat.one_lt_pow two_ne_zero hq
    omega
  obtain ⟨x₀, -, hx₀C⟩ := hlong e₀ he₀ hne₀
  have hroot : ∀ e (he : e ∈ E), ∃ s : K, γe e he = x₀ * tL s * x₀⁻¹ := by
    intro e he
    by_cases h1 : γe e he = 1
    · exact ⟨0, by rw [h1, tL_zero, mul_one, mul_inv_cancel]⟩
    obtain ⟨x, hx, hxC⟩ := hlong e he h1
    have hF : ∀ y, g2Act x⁻¹ y ∈ stdF K 2 ↔ g2Act x₀⁻¹ y ∈ stdF K 2 := by
      intro y
      rw [mem_F2_iff_polarQ, mem_F2_iff_polarQ]
      exact forall_congr' fun c => imp_congr_left ((hxC c).trans (hx₀C c).symm)
    have hst : x₀⁻¹ * x ∈ stabQ (stdF K 2) := by
      rw [mem_stabQ]
      intro w
      have h3 := hF (g2Act x w)
      rw [g2Act_inv_apply] at h3
      rw [g2Act_mul_apply]
      exact h3
    obtain ⟨s, hs⟩ := conj_tL_mem hst 1
    refine ⟨s, ?_⟩
    rw [hx]
    calc x * tL 1 * x⁻¹ = x₀ * ((x₀⁻¹ * x) * tL 1 * (x₀⁻¹ * x)⁻¹) * x₀⁻¹ := by group
      _ = x₀ * tL s * x₀⁻¹ := by rw [hs]
  choose sE hsE using hroot
  have hpsi : ∀ e (he : e ∈ E),
      SecA.conjV V e (hEX he).2 = psiG hc0 hc1 π x₀ (tL (sE e he)) := fun e he => by
    rw [hlift e he, hsE e he, psiG_apply]
  have hs₀ : sE e₀ he₀ ≠ 0 := by
    intro h0
    apply hne₀
    rw [hsE e₀ he₀, h0, tL_zero, mul_one, mul_inv_cancel]
  have hs1 : (1 : K) ≠ 0 := one_ne_zero
  have ha : ((Units.mk0 c₀ hc0 : Kˣ) : K) ≠ 1 := hc1
  obtain ⟨vt, hvt⟩ : ∃ vt : Subgroup ↥V,
      vt = (commHom (psiG hc0 hc1 π x₀ (tL 1))).range := ⟨_, rfl⟩
  have hEvt : commV (autOn E V) = vt := by
    apply le_antisymm
    · refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨φ, hφ, v, rfl⟩
      obtain ⟨e, he, heV, rfl⟩ := SecA.mem_autOn_iff.mp hφ
      rw [SetLike.mem_coe, hvt]
      by_cases h0 : sE e he = 0
      · have h3 : SecA.conjV V e heV v * v⁻¹ = 1 := by
          rw [hpsi e he, h0, tL_zero, map_one, MulAut.one_apply, mul_inv_cancel]
        rw [h3]
        exact Subgroup.one_mem _
      · have h3 : SecA.conjV V e heV v * v⁻¹ ∈
            (commHom (psiG hc0 hc1 π x₀ (tL (sE e he)))).range :=
          ⟨v, by rw [commHom_apply, hpsi e he]⟩
        exact vt_le hf hc0 hc1 x₀ hsq hZfix hs1 h0 ha h3
    · rw [hvt]
      intro w hw
      obtain ⟨v, rfl⟩ := vt_le hf hc0 hc1 x₀ hsq hZfix hs₀ hs1 ha hw
      refine Subgroup.subset_closure ⟨_, SecA.conjV_mem_autOn he₀ (hEX he₀).2, v, ?_⟩
      rw [hpsi e₀ he₀, commHom_apply]
  obtain ⟨l, hlL, hlV, hl⟩ := SecA.mem_autOn_iff.mp (rhoG hc0 hc1 π (g * x₀⁻¹)).2
  have hconj := subgroupOf_conjSubgroup_eq hf hc0 hc1 hV₂ hlV hl
  rw [show (g * x₀⁻¹)⁻¹ * g = x₀ by group] at hconj
  have hUV : conjSubgroup V₂ l ≤ V := conjSubgroup_le_of_le h₂ hlV
  have hLUV : LOf L (conjSubgroup V₂ l) ≤ Subgroup.normalizer (V : Set G) :=
    ((perfectCore_le _).trans inf_le_left).trans hLV
  have hLU : autOn (LOf L (conjSubgroup V₂ l)) V =
      (perfectCore (stabQ (stdF K 2))).map (psiG hc0 hc1 π x₀) := by
    rw [SecA.autOn_lOf hLV hUV, hconj]
    exact gammaW_two_eqG hf hc0 hc1 x₀
  have hR : (⁅conjSubgroup V₂ l, LOf L (conjSubgroup V₂ l)⁆).subgroupOf V = vt := by
    rw [← commS_autOn_eq hUV hLUV, hLU, hconj, hvt]
    exact commS_eq_vt hf hc0 hc1 x₀ hsq hZfix
  have hL : (⁅V, E⁆).subgroupOf V = vt := by
    rw [← Ch10.SecA.commV_autOn_eq hEV]
    exact hEvt
  refine ⟨l, hlL, ?_⟩
  have h1 := Subgroup.subgroupOf_inj.mp (hL.trans hR.symm)
  rwa [inf_of_le_left (commutator_le_of_le_of_normalizer le_rfl hEV),
    inf_of_le_left (commutator_le_of_le_of_normalizer hUV hLUV)] at h1

end CFSG.Quasithin.Vol2.Ch11.G2Q8
