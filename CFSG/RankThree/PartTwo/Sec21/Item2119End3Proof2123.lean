module

public import CFSG.RankThree.PartTwo.Sec21.Item2119EndProofDefs
import CFSG.RankThree.PartTwo.Sec21.Item2119EndProofTypeTwo
import CFSG.RankThree.PartTwo.Sec21.Item2119End3Proof2125Unique
import CFSG.RankThree.PartTwo.KFacts.KS222SL3Tools
import CFSG.RankThree.PartTwo.Sec19.Step1917EqProofJArith
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.RankThree.PartTwo.Sec6.Item68
public import CFSG.RankThree.PartTwo.Sec21.Item21Late2Proof2120
public import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec21

open Matrix CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.RankThree.PartTwo.Sec4 (diagUnits coe_diagUnits diagE)
open CFSG.Assembly.RankThreeEven (projImage projSL)

@[expose] def KF2123TypeTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (n : ℕ), 0 < n → Even n →
    Nonempty (lBar L ≃* projSL 3 (GaloisField 2 n)) → ∀ x : G, x ^ 3 = 1 →
      Sec4.InducesTypeOn L x 2 → ∀ d ∈ L, d ^ 3 = 1 → Sec4.InducesTypeOn L d 1 →
      x * d = d * x → d ∈ inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {x}) ∧
      IsQuasisimple (lBar (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {x}))) ∧
      Nat.card (lBar (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {x}))) =
        2 ^ n * (4 ^ n - 1)

namespace Item2119End3Proof

variable {G : Type} [Group G] [Finite G]

open Item2119EndProof

theorem inducesTypeOn_two_gen (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    {A E U₀ X : Subgroup G} {c d a : G} (hcA : c ∈ A) (hc1 : c ≠ 1) (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hcd : c ∉ Subgroup.zpowers d)
    (hcfgX : Config2119 G A E U₀ a X) (hdX : d ∈ X) (hdT : Sec4.InducesTypeOn X d 1)
    (haCD : a ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d) : Sec4.InducesTypeOn X c 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hpair, ⟨m, hm0, hmev, ⟨eX⟩⟩, hC, -, -⟩ := hcfgX
  have hm : 2 ≤ m := by
    obtain ⟨k, hk⟩ := hmev
    omega
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have haA : a ∈ A := hpair.mem_E.2 hpairs.1.1
  have ha1 : a ≠ 1 := hpairs.2.1
  have ha3 : orderOf a = 3 := orderOf_eq_prime (h3 a haA) ha1
  have hca : c ∉ Subgroup.zpowers a := fun h =>
    haCD (Subgroup.mem_sup_left (Item21Late2Proof.mem_zpowers_of_mem (h3 a haA) h hc1
      (Subgroup.mem_zpowers a)))
  have hda : d ∉ Subgroup.zpowers a := fun h =>
    haCD (Subgroup.mem_sup_right (Item21Late2Proof.mem_zpowers_of_mem (h3 a haA) h hd1
      (Subgroup.mem_zpowers a)))
  have hnotin : c ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers d := by
    intro h
    have hdc' : d ∉ Subgroup.zpowers c := fun h' => hcd
      (Item21Late2Proof.mem_zpowers_of_mem (h3 c hcA) h' hd1 (Subgroup.mem_zpowers c))
    have hB : Nat.card (Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup G) = 9 :=
      Item21LateProof.card_zpowers_sup_zpowers (hcomm c hcA d hdA) (h3 c hcA) (h3 d hdA) hc1 hdc'
    have hB' : Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers d : Subgroup G) = 9 :=
      Item21LateProof.card_zpowers_sup_zpowers (hcomm a haA d hdA) (h3 a haA) (h3 d hdA) ha1 hda
    have hle : Subgroup.zpowers c ⊔ Subgroup.zpowers d ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers d :=
      sup_le (Subgroup.zpowers_le.mpr h) le_sup_right
    have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hB, hB'])
    apply haCD
    rw [heq]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have hXa : X ∈ thetaComponentsAt 3 a := lZeroStarAt_subset A a hpairs.2.2.1
  have hG4 := hpair.standing.toTheoremFourHyp
  have hAL : A ≤ Subgroup.normalizer (X : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG4 hAe haA ha1 X hXa
  have hXs : X ∈ lStar A :=
    lZeroStar_subset_lStar A (lZeroStarAt_subset_lZeroStar A a hpairs.2.2.1)
  have hCA : A ⊓ Sec4.thetaQuotCentralizer X = Subgroup.zpowers a := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr
      ⟨haA, Sec6.mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hXa⟩) ?_
    rw [Nat.card_zpowers, ha3]
    exact Sec6.card_le_three_of_isCyclic (h66 G hpair.standing A hpair.mem_S X hXs)
      fun y hy => h3 y hy.1
  set T : Subgroup.normalizer (X : Set G) →* MulAut (lBar X) :=
    (Sec4.thetaQuotMulAut X).comp X.normalizerMonoidHom with hT
  have hTinner : ∀ (l₀ : G) (hl₀ : l₀ ∈ X) (z : lBar X),
      T ⟨l₀, Subgroup.le_normalizer hl₀⟩ z =
        ((⟨l₀, hl₀⟩ : X) : lBar X) * z * ((⟨l₀, hl₀⟩ : X) : lBar X)⁻¹ :=
    fun l₀ hl₀ z => Item21Late2Proof.thetaQuotMulAut_inner hl₀ _ z
  have htriv : ∀ (x : G) (hx : x ∈ A), (∀ z, T ⟨x, hAL hx⟩ z = z) → x ∈ Subgroup.zpowers a := by
    intro x hx h
    have hmem : x ∈ A ⊓ Sec4.thetaQuotCentralizer X :=
      ⟨hx, ⟨⟨x, hAL hx⟩, MonoidHom.mem_ker.mpr (MulEquiv.ext h), rfl⟩⟩
    rwa [hCA] at hmem
  obtain ⟨π, p, f, K, _, hPi, hmod, e, D, hD, hconj, -⟩ := hC
  have hcard := Sec13.card_projImage_slPi_mul_three hPi hmod
  rw [← Nat.card_congr e.toEquiv] at hcard
  obtain ⟨rfl, rfl, hfn⟩ := Sec19.Step1917EqProof.eq_two_of_card hPi.prime hPi.one_le
    (by omega) hmod hcard (Sec19.Step1917EqProof.card_kStar (by omega) (Or.inr ⟨eX⟩))
  subst hfn
  have h2 : (2 : K) = 0 := Item21Late2Proof.two_eq_zero_of_piField hPi
  have hq2 : 2 < 2 ^ f := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hm
  obtain ⟨τ₀, hτ₀, hτ₀1⟩ := Sec4.exists_tau hPi hmod
  set ψ : lBar X →* ProjGenLinGroup (Fin 3) K :=
    (projImage (Sec4.slPi true 3 (2 ^ f) K)).subtype.comp e.toMonoidHom with hψ
  have hψinj : Function.Injective ψ :=
    (projImage (Sec4.slPi true 3 (2 ^ f) K)).subtype_injective.comp e.injective
  have hψe : ∀ z, ψ z = (e z : ProjGenLinGroup (Fin 3) K) := fun z => rfl
  have hyA : ∀ (x : G) (hx : x ∈ A), ∃ y ∈ D, ∀ z,
      ψ (T ⟨x, hAL hx⟩ z) = ProjGenLinGroup.mk y * ψ z * (ProjGenLinGroup.mk y)⁻¹ := by
    intro x hx
    obtain ⟨y, hyD, hy⟩ := hconj _ (Sec4.mem_autThetaQuot_iff.mpr ⟨x, hAL hx, hx, rfl⟩)
    exact ⟨y, hyD, fun z => hy z⟩
  obtain ⟨g, -, hdiag, -⟩ := Sec4.isTypeC_conj_std hPi hmod hD
  have hsc : ∀ (Y : GL (Fin 3) K) (v : Kˣ), Y * GeneralLinearGroup.scalar (Fin 3) v =
      GeneralLinearGroup.scalar (Fin 3) v * Y := fun Y v => (SL3Lines.scalar_mul_comm v Y).symm
  have hscal : ∀ (x : G) (hx : x ∈ A) (y : GL (Fin 3) K) (l : Kˣ),
      (∀ z, ψ (T ⟨x, hAL hx⟩ z) = ProjGenLinGroup.mk y * ψ z * (ProjGenLinGroup.mk y)⁻¹) →
      g⁻¹ * y * g = GeneralLinearGroup.scalar (Fin 3) l → x ∈ Subgroup.zpowers a := by
    intro x hx y l hy hyl
    have hy1 : ProjGenLinGroup.mk y = 1 := by
      have e1 : y = GeneralLinearGroup.scalar (Fin 3) l := by
        calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
          _ = GeneralLinearGroup.scalar (Fin 3) l := by rw [hyl, hsc g l, mul_inv_cancel_right]
      rw [e1, ProjGenLinGroup.mk_scalar]
    refine htriv x hx fun z => hψinj ?_
    rw [hy, hy1, one_mul, inv_one, mul_one]
  have hroots : ∀ v : Kˣ, v ∈ rootsOfUnity 3 K → (v : K) ^ 3 = 1 := fun v hv => by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity 3 v).mp hv, Units.val_one]
  obtain ⟨yd, hydD, hyd⟩ := hyA d hdA
  obtain ⟨ld, sd, td, hsd, htd, hgd⟩ := hdiag yd hydD
  have hψd : ψ ((⟨d, hdX⟩ : X) : lBar X) = ProjGenLinGroup.mk yd := by
    refine Item21Late2Proof.coe_e_eq_mk_of_inner hPi hmod hq2 e _ yd fun z => ?_
    have h1 := hyd z
    rw [show T ⟨d, hAL hdA⟩ z = ((⟨d, hdX⟩ : X) : lBar X) * z * ((⟨d, hdX⟩ : X) : lBar X)⁻¹ from
      hTinner d hdX z] at h1
    exact h1
  obtain ⟨m₀, hm₀⟩ := Item21Late2Proof.exists_conj_inv_of_inducesTypeOn_one hm eX hdX hdT
  obtain ⟨r, -, hrm⟩ := (e m₀).2
  have hψm : ψ m₀ = ProjGenLinGroup.mk r := by
    rw [hψe]
    exact hrm.symm
  have hr1 : ProjGenLinGroup.mk (r * yd * r⁻¹) = ProjGenLinGroup.mk yd⁻¹ := by
    have h0 := congrArg ψ hm₀
    rw [map_mul, map_mul, map_inv, map_inv, hψd, hψm] at h0
    rw [map_mul, map_mul, map_inv, map_inv]
    exact h0
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hr1
  have hr3 : (g⁻¹ * r * g) * (g⁻¹ * yd * g) * (g⁻¹ * r * g)⁻¹ *
      GeneralLinearGroup.scalar (Fin 3) u = (g⁻¹ * yd * g)⁻¹ := by
    calc (g⁻¹ * r * g) * (g⁻¹ * yd * g) * (g⁻¹ * r * g)⁻¹ * GeneralLinearGroup.scalar (Fin 3) u
        = g⁻¹ * (r * yd * r⁻¹) * (g * GeneralLinearGroup.scalar (Fin 3) u) := by group
      _ = g⁻¹ * (r * yd * r⁻¹ * GeneralLinearGroup.scalar (Fin 3) u) * g := by
          rw [hsc g u]
          group
      _ = (g⁻¹ * yd * g)⁻¹ := by rw [hu]; group
  rw [hgd] at hr3
  have hsdtd : sd * td = 1 := by
    have hsd3 := hroots sd hsd
    have htd3 := hroots td htd
    rcases Item21Late2Proof.eq_of_conj_inv h2 hτ₀ hτ₀1 hsd3 htd3 hr3 with
      ⟨h1, h1'⟩ | ⟨h1, h1'⟩ | ⟨h1, h1'⟩
    · exact Units.ext (by rw [Units.val_mul, h1, h1', mul_one, Units.val_one])
    · exact Units.ext (by rw [Units.val_mul, h1, h1', ← pow_succ', hτ₀, Units.val_one])
    · exact Units.ext (by rw [Units.val_mul, h1, h1', ← pow_succ, hτ₀, Units.val_one])
  obtain ⟨yc, hycD, hyc⟩ := hyA c hcA
  obtain ⟨lc, sc, tc, hsc', htc, hgc⟩ := hdiag yc hycD
  have hsctc : sc * tc ≠ 1 := by
    intro hst
    have htc' : tc = sc⁻¹ := eq_inv_of_mul_eq_one_right hst
    have htd' : td = sd⁻¹ := eq_inv_of_mul_eq_one_right hsdtd
    by_cases hsc1 : sc = 1
    · exact hca (hscal c hcA yc lc hyc (by
        rw [hgc, htc', hsc1, inv_one, SL3Lines.diagUnits_one_one_one, mul_one]))
    by_cases hsd1 : sd = 1
    · exact hda (hscal d hdA yd ld hyd (by
        rw [hgd, htd', hsd1, inv_one, SL3Lines.diagUnits_one_one_one, mul_one]))
    have hk : sc * sd = 1 ∨ sc * sd * sd = 1 := by
      have hsc1' : (sc : K) ≠ 1 := fun h => hsc1 (Units.ext h)
      have hsd1' : (sd : K) ≠ 1 := fun h => hsd1 (Units.ext h)
      rcases Sec4.cube_root_cases hτ₀ hτ₀1 (hroots sc hsc') with h | h | h
      · exact absurd h hsc1'
      · rcases Sec4.cube_root_cases hτ₀ hτ₀1 (hroots sd hsd) with h' | h' | h'
        · exact absurd h' hsd1'
        · right
          exact Units.ext (by rw [Units.val_mul, Units.val_mul, h, h', ← pow_two, ← pow_succ,
            hτ₀, Units.val_one])
        · left
          exact Units.ext (by rw [Units.val_mul, h, h', ← pow_succ', hτ₀, Units.val_one])
      · rcases Sec4.cube_root_cases hτ₀ hτ₀1 (hroots sd hsd) with h' | h' | h'
        · exact absurd h' hsd1'
        · left
          exact Units.ext (by rw [Units.val_mul, h, h', ← pow_succ, hτ₀, Units.val_one])
        · right
          exact Units.ext (by
            rw [Units.val_mul, Units.val_mul, h, h', Units.val_one]
            linear_combination (τ₀ ^ 3 + 1) * hτ₀)
    have hTd : ∀ z, ψ (T ⟨d, hAL hdA⟩ z) =
        ProjGenLinGroup.mk yd * ψ z * (ProjGenLinGroup.mk yd)⁻¹ := hyd
    rcases hk with hk | hk
    ·
      have hxA : c * d ∈ A := A.mul_mem hcA hdA
      have hact : ∀ z, ψ (T ⟨c * d, hAL hxA⟩ z) =
          ProjGenLinGroup.mk (yc * yd) * ψ z * (ProjGenLinGroup.mk (yc * yd))⁻¹ := by
        intro z
        have e1 : T ⟨c * d, hAL hxA⟩ = T ⟨c, hAL hcA⟩ * T ⟨d, hAL hdA⟩ := by
          rw [← map_mul]
          rfl
        rw [e1, MulAut.mul_apply, hyc, hTd, map_mul]
        group
      have hgl : g⁻¹ * (yc * yd) * g = GeneralLinearGroup.scalar (Fin 3) (lc * ld) := by
        calc g⁻¹ * (yc * yd) * g = (g⁻¹ * yc * g) * (g⁻¹ * yd * g) := by group
          _ = GeneralLinearGroup.scalar (Fin 3) (lc * ld) * diagUnits 1 (sc * sd) (tc * td) := by
              rw [hgc, hgd, Sec4.scalar_diagUnits_mul]
          _ = GeneralLinearGroup.scalar (Fin 3) (lc * ld) := by
              rw [htc', htd', ← mul_inv, hk, inv_one, SL3Lines.diagUnits_one_one_one, mul_one]
      have hcda := hscal _ hxA _ _ hact hgl
      apply hnotin
      have e2 : c = (c * d) * d⁻¹ := by group
      rw [e2]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hcda)
        (Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers d)))
    ·
      have hxA : c * d * d ∈ A := A.mul_mem (A.mul_mem hcA hdA) hdA
      have hact : ∀ z, ψ (T ⟨c * d * d, hAL hxA⟩ z) =
          ProjGenLinGroup.mk (yc * yd * yd) * ψ z * (ProjGenLinGroup.mk (yc * yd * yd))⁻¹ := by
        intro z
        have e1 : T ⟨c * d * d, hAL hxA⟩ = T ⟨c, hAL hcA⟩ * T ⟨d, hAL hdA⟩ * T ⟨d, hAL hdA⟩ := by
          rw [← map_mul, ← map_mul]
          rfl
        rw [e1, MulAut.mul_apply, MulAut.mul_apply, hyc, hTd, hTd, map_mul, map_mul]
        group
      have hgl : g⁻¹ * (yc * yd * yd) * g =
          GeneralLinearGroup.scalar (Fin 3) (lc * ld * ld) := by
        calc g⁻¹ * (yc * yd * yd) * g = (g⁻¹ * yc * g) * (g⁻¹ * yd * g) * (g⁻¹ * yd * g) := by
              group
          _ = GeneralLinearGroup.scalar (Fin 3) (lc * ld * ld) *
                diagUnits 1 (sc * sd * sd) (tc * td * td) := by
              rw [hgc, hgd, Sec4.scalar_diagUnits_mul, Sec4.scalar_diagUnits_mul]
          _ = GeneralLinearGroup.scalar (Fin 3) (lc * ld * ld) := by
              rw [htc', htd', ← mul_inv, ← mul_inv, hk, inv_one, SL3Lines.diagUnits_one_one_one,
                mul_one]
      have hcda := hscal _ hxA _ _ hact hgl
      apply hnotin
      have e2 : c = (c * d * d) * (d⁻¹ * d⁻¹) := by group
      rw [e2]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hcda)
        (Subgroup.mem_sup_right (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers d))
          (Subgroup.inv_mem _ (Subgroup.mem_zpowers d))))
  have htype := type123_two_of_frame (q := 2 ^ f) hτ₀ hτ₀1 (hroots sc hsc') (hroots tc htc) hsctc
    hgc
  exact ⟨hAL hcA, true, 2, f, K, inferInstance, hPi, hmod, e, yc, Sec4.mem_glPi_true _ _, htype,
    fun z => hyc z⟩

theorem eq_of_two_pow_mul_eq {n m : ℕ} (h : 2 ^ n * (4 ^ n - 1) = 2 ^ m * (4 ^ m - 1)) :
    n = m := by
  have key : ∀ {n m : ℕ}, n < m → 2 ^ n * (4 ^ n - 1) < 2 ^ m * (4 ^ m - 1) := by
    intro n m hnm
    have h1 : 2 ^ n < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) hnm
    have h2 : 4 ^ n < 4 ^ m := Nat.pow_lt_pow_right (by norm_num) hnm
    have h3 : 1 ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num)
    have h4 : 4 ^ n - 1 < 4 ^ m - 1 := by omega
    exact Nat.mul_lt_mul'' h1 h4
  rcases lt_trichotomy n m with hnm | hnm | hnm
  · exact absurd h (key hnm).ne
  · exact hnm
  · exact absurd h (key hnm).ne'

end Item2119End3Proof

open Item2119End3Proof

theorem item2123Field_of (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h66 : Sec6.Item6_6)
    (hKF : KF2123TypeTwo) : Item2123Field := by
  intro G _ _ A E U c L d U₀ a X hE hcfgX hdX hdTX haCD hcTX
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcfg := hE.cfg
  have hpair := hcfg.pair
  obtain ⟨n, hn0, hne, ⟨eL⟩⟩ := hcfg.lthree
  obtain ⟨m, hm0, hme, ⟨eX⟩⟩ := hcfgX.lthree
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hpairs' := mem_lThreeStarPairs_iff.mp hcfgX.pair.mem_pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have haA : a ∈ A := hcfgX.pair.mem_E.2 hpairs'.1.1
  have ha1 : a ≠ 1 := hpairs'.2.1
  have hdA : d ∈ A := hE.mem_d.1
  have hdL : d ∈ L := hE.mem_d.2
  have hd1 := hE.ne_one_d
  have hd3 : d ^ 3 = 1 := h3 d hdA
  have had : a ∉ Subgroup.zpowers d := fun h => haCD (Subgroup.mem_sup_right h)
  have hda : d ∉ Subgroup.zpowers a := fun h => had
    (Item21Late2Proof.mem_zpowers_of_mem (h3 a haA) h hd1 (Subgroup.mem_zpowers a))
  have hcL : c ∉ L := (Item21Late2Proof.frame_of h45 h66 hcfg).1
  have hcd : c ∉ Subgroup.zpowers d := fun h => hcL ((Subgroup.zpowers_le.mpr hdL) h)
  have hcAD : c ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers d := by
    intro h
    have hdc' : d ∉ Subgroup.zpowers c := fun h' => hcd
      (Item21Late2Proof.mem_zpowers_of_mem (h3 c hcA) h' hd1 (Subgroup.mem_zpowers c))
    have hB : Nat.card (Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup G) = 9 :=
      Item21LateProof.card_zpowers_sup_zpowers (hcomm c hcA d hdA) (h3 c hcA) hd3 hc1 hdc'
    have hB' : Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers d : Subgroup G) = 9 :=
      Item21LateProof.card_zpowers_sup_zpowers (hcomm a haA d hdA) (h3 a haA) hd3 ha1 hda
    have hle : Subgroup.zpowers c ⊔ Subgroup.zpowers d ≤
        Subgroup.zpowers a ⊔ Subgroup.zpowers d :=
      sup_le (Subgroup.zpowers_le.mpr h) le_sup_right
    have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hB, hB'])
    apply haCD
    rw [heq]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have haTL : Sec4.InducesTypeOn L a 2 :=
    inducesTypeOn_two_gen h45 h66 haA ha1 hdA hd1 had hcfg hdL hE.type_d hcAD
  obtain ⟨hdI, hIq, hIcard⟩ :=
    hKF G L n hn0 hne ⟨eL⟩ a (h3 a haA) haTL d hdL hd3 hE.type_d (hcomm a haA d hdA)
  obtain ⟨hdJ, hJq, hJcard⟩ :=
    hKF G X m hm0 hme ⟨eX⟩ c (h3 c hcA) hcTX d hdX hd3 hdTX (hcomm c hcA d hdA)
  set I := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({a} : Set G)) with hIdef
  set J := inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({c} : Set G)) with hJdef
  have hG4 := hpair.standing.toTheoremFourHyp
  have hE27 : Late.IsE27 A := ⟨hAe, by rw [hcfg.card]; norm_num⟩
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c hpairs.2.2.1
  have hXa : X ∈ thetaComponentsAt 3 a := lZeroStarAt_subset A a hpairs'.2.2.1
  obtain ⟨K, hK, hIK⟩ := Sec14.exists_mem_thetaComponentsAt_le_residual h48
    (hG4.sectionFourHyp (Sec6.centralizer_ne_top_of_ne_one hG4 ha1)) hE27 hcA haA hc1 hLc hIq
  obtain ⟨K', hK', hJK'⟩ := Sec14.exists_mem_thetaComponentsAt_le_residual h48
    (hG4.sectionFourHyp (Sec6.centralizer_ne_top_of_ne_one hG4 hc1)) hE27 haA hcA ha1 hXa hJq
  have hZX : Subgroup.center (lBar X) = ⊥ :=
    center_eq_bot_of_mulEquiv' eX (Item21Early2Proof.center_projSL_three_eq_bot hm0 hme)
  have hZL : Subgroup.center (lBar L) = ⊥ :=
    center_eq_bot_of_mulEquiv' eL (Item21Early2Proof.center_projSL_three_eq_bot hn0 hne)
  have hKX : K = X := by
    by_contra hne'
    have h1 := le_thetaQuotCentralizer_of_ne hXa hK (Ne.symm hne')
    exact hd1 (eq_one_of_mem_thetaQuotCentralizer hZX hdX (h1 (hIK hdI)) hd3)
  have hK'L : K' = L := by
    by_contra hne'
    have h1 := le_thetaQuotCentralizer_of_ne hLc hK' (Ne.symm hne')
    exact hd1 (eq_one_of_mem_thetaQuotCentralizer hZL hdL (h1 (hJK' hdJ)) hd3)
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hXC : X ≤ Subgroup.centralizer ({a} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hXa
  have hIL : I ≤ L := (Sec6.inSubgroup_perfectResidual_le _).trans inf_le_left
  have hJX : J ≤ X := (Sec6.inSubgroup_perfectResidual_le _).trans inf_le_left
  have hIJ : I ≤ J := Sec6.le_inSubgroup_perfectResidual_of_isPerfect
    (Sec6.isPerfect_inSubgroup_perfectResidual _) (le_inf (hKX ▸ hIK) (hIL.trans hLC))
  have hJI : J ≤ I := Sec6.le_inSubgroup_perfectResidual_of_isPerfect
    (Sec6.isPerfect_inSubgroup_perfectResidual _) (le_inf (hK'L ▸ hJK') (hJX.trans hXC))
  have heq : I = J := le_antisymm hIJ hJI
  rw [heq, hJcard] at hIcard
  obtain rfl := eq_of_two_pow_mul_eq hIcard
  exact ⟨eX.trans eL.symm⟩



end CFSG.RankThree.PartTwo.Sec21
