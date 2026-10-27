module

public import CFSG.RankThree.PartTwo.Sec12.Item12Res3ProofM12
public import CFSG.RankThree.PartTwo.Sec12.Item12Res3ProofPGL
import CFSG.RankThree.PartTwo.Sec14.Item142ResProofCore
import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
import CFSG.RankThree.PartTwo.Sec10.HWNormalizes
import CFSG.RankThree.PartTwo.Sec12.Item128BarProofTools
import CFSG.RankThree.PartTwo.Sec13.Item137Tools

public section

namespace CFSG.RankThree.PartTwo.Sec12.Res3Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13 (omegaA lBarA)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem thetaBarAct_eq_one_of_le_centralizer {K : Subgroup G} {a : G}
    (hKa : K ≤ Subgroup.centralizer ({a} : Set G)) (haN : a ∈ Subgroup.normalizer (K : Set G)) :
    thetaBarAct K ⟨a, haN⟩ = 1 := by
  ext q
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 K) q
  rw [thetaBarAct_mk, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  change a * (l : G) * a⁻¹ = l
  rw [← (Subgroup.mem_centralizer_singleton_iff.mp (hKa l.2)), mul_inv_cancel_right]

theorem thetaBarAct_eq_one_of_mem_isPGroup {K : Subgroup G} {n : G}
    (hnN : n ∈ Subgroup.normalizer (K : Set G)) (hn3 : ¬ 3 ∣ orderOf n)
    {P : Subgroup (MulAut (K ⧸ aschbacherSolvableCore 3 K))} (hP : IsPGroup 3 P)
    (h : thetaBarAct K ⟨n, hnN⟩ ∈ P) : thetaBarAct K ⟨n, hnN⟩ = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨_, h⟩
  have h1 : thetaBarAct K ⟨n, hnN⟩ ^ 3 ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  have h2 : thetaBarAct K ⟨n, hnN⟩ ^ orderOf n = 1 := by
    rw [← map_pow]
    have : (⟨n, hnN⟩ : Subgroup.normalizer (K : Set G)) ^ orderOf n = 1 :=
      Subtype.ext (by simp [pow_orderOf_eq_one])
    rw [this, map_one]
  have hcop : Nat.Coprime (3 ^ k) (orderOf n) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hn3)
  exact (pow_eq_one_iff_of_coprime hcop).mp ⟨h1, h2⟩

theorem mem_of_pgl {A L : Subgroup G} {c : G} (h : Sec12StdBar G A c L) (hAE : A ∈ partTwoE G)
    (hSL : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L))
    {a : G} (ha : Subgroup.zpowers a ∈ omegaA A) (haB : a ∉ Sec4.thetaQuotCentralizer L)
    {K : Subgroup G} (hK : K ∈ lA422 A a) (hcK : c ∈ K) {x : G} (hxA : x ∈ A)
    (hx : Sec4.InducesTypeOn K x 3) : a ∈ L := by
  by_contra haL
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL := h.mem_thetaComponentsAt
  have hc1 := h.ne_one
  have hAF : A ∈ partTwoF G := h.partTwoF_eq ▸ hAE
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hAF.1
  have h27 : Nat.card A = 27 := hAE.2.1
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨haA, ha3', -⟩ := Sec13.zpowers_mem_omegaA_iff.mp ha
  have ha1 : a ≠ 1 := ne_one_of_card_zpowers_eq_three ha3'
  have ha3 : a ^ 3 = 1 := hAe.2 a haA
  have hc3 : c ^ 3 = 1 := hAe.2 c h.mem_A
  have hZ : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥ := by
    have : Group.IsPerfect (K ⧸ aschbacherSolvableCore 3 K) :=
      (Sec6.isQuasisimple_of_mem_thetaComponentsAt hK.1).1
    obtain ⟨-, π, p, f, 𝕂, _, hF, hq, e, -⟩ := hx
    have : Group.IsPerfect (Assembly.RankThreeEven.projImage (Sec4.slPi π 3 (p ^ f) 𝕂)) :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    rw [eq_bot_iff]
    intro l hl
    have hcen : e l ∈ Subgroup.center _ := by
      rw [Subgroup.mem_center_iff]
      intro m
      obtain ⟨l', rfl⟩ := e.surjective m
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hl l']
    rw [Sec4.center_projImage_eq_bot hF hq, Subgroup.mem_bot] at hcen
    exact Subgroup.mem_bot.mpr (e.injective (by rw [hcen, map_one]))
  have haK : a ∉ K := Proof128.not_mem_of_center_eq_bot hK.1 hZ ha3 ha1
  have hKa : K ≤ Subgroup.centralizer ({a} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hK.1
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hL
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := hK.2.1
  have haNK : a ∈ Subgroup.normalizer (K : Set G) := hAK haA
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := hAK hxA
  have hxc : x * c = c * x := hAc x hxA c h.mem_A
  have hxa : x * a = a * x := hAc x hxA a haA
  have hNK : ∀ n : G, n * a = a * n → n * c = c * n → n ∈ Subgroup.normalizer (K : Set G) :=
    fun n hna hnc => mem_normalizer_of_mem_centralizer hK.1 hcK hZ hc3 hc1
      (Subgroup.mem_centralizer_singleton_iff.mpr hna)
      (Subgroup.mem_centralizer_singleton_iff.mpr hnc)
  obtain ⟨tb, htbc, hP3, hcomm⟩ := exists_conj_inv_of_type3 hK.1 hcK hc3 hc1 hxc hxN hx
  have hc'3 : (⟨c, hcK⟩ : K) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
  have hCp : IsPGroup 3 (Subgroup.zpowers (⟨c, hcK⟩ : K)) :=
    KS128NotHJTC.isPGroup_zpowers_of_pow_three hc'3
  have htbN : tb ∈ Subgroup.normalizer (((Subgroup.zpowers (⟨c, hcK⟩ : K)).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 K)) :
        Subgroup (K ⧸ aschbacherSolvableCore 3 K)) : Set (K ⧸ aschbacherSolvableCore 3 K)) := by
    rw [MonoidHom.map_zpowers]
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← conj_zpow, htbc]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers _)) k
  rw [Sec13.normalizer_map_mk_eq hCp] at htbN
  obtain ⟨t₁, ht₁N, rfl⟩ := htbN
  have htc' : t₁ * ⟨c, hcK⟩ * t₁⁻¹ = (⟨c, hcK⟩ : K)⁻¹ := by
    apply CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three hCp
      ((Subgroup.mem_normalizer_iff.mp ht₁N _).mp (Subgroup.mem_zpowers _))
      (Subgroup.inv_mem _ (Subgroup.mem_zpowers _))
    rw [map_mul, map_mul, map_inv, map_inv]
    exact htbc
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 K) with hπ
  set t : G := (t₁ : G) with htdef
  have htK : t ∈ K := t₁.2
  have hta : t * a = a * t := Subgroup.mem_centralizer_singleton_iff.mp (hKa htK)
  have htc : t * c * t⁻¹ = c⁻¹ := by
    have := congrArg Subtype.val htc'
    simpa [htdef] using this
  have htN : t ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer htK
  have hπt : thetaBarAct K ⟨t, htN⟩ = MulAut.conj (π t₁) := thetaBarAct_of_mem htK
  generalize hσdef : thetaBarAct K ⟨x, hxN⟩ = σ at hP3 hcomm
  generalize hτdef : MulAut.conj (π t₁) * σ * (MulAut.conj (π t₁))⁻¹ = τσ at hP3 hcomm
  generalize hPdef : Subgroup.closure ({MulAut.conj (π ⟨c, hcK⟩), σ, τσ} :
    Set (MulAut (K ⧸ aschbacherSolvableCore 3 K))) = P at hP3
  have hcP : MulAut.conj (π ⟨c, hcK⟩) ∈ P := by
    rw [← hPdef]
    exact Subgroup.subset_closure (by simp)
  have hσP : σ ∈ P := by
    rw [← hPdef]
    exact Subgroup.subset_closure (by simp)
  have hτσP : τσ ∈ P := by
    rw [← hPdef]
    exact Subgroup.subset_closure (by simp)
  have hσa : thetaBarAct K ⟨a, haNK⟩ = 1 := thetaBarAct_eq_one_of_le_centralizer hKa haNK
  have hAP : ∀ g (hg : g ∈ A), thetaBarAct K ⟨g, hAK hg⟩ ∈ P := by
    have hac : a * c = c * a := hAc a haA c h.mem_A
    have haz : a ∉ Subgroup.zpowers c := fun h1 => haK (Subgroup.zpowers_le.mpr hcK h1)
    have h9 := card_zpowers_sup_eq_nine ha3 hc3 hc1 hac haz
    have hxac : x ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers c :=
      Sec14.Proof142Res.not_mem_sup_of_inducesTypeOn_three hK.1 hKa haNK hac hcK hx
    have hAeq : Subgroup.zpowers x ⊔ (Subgroup.zpowers a ⊔ Subgroup.zpowers c) = A :=
      eq_of_card_nine_lt h27 (sup_le (Subgroup.zpowers_le.mpr hxA)
        (sup_le (Subgroup.zpowers_le.mpr haA) (Subgroup.zpowers_le.mpr h.mem_A))) le_sup_right
        h9 (Subgroup.mem_sup_left (Subgroup.mem_zpowers x)) hxac
    have hle : A ≤ (P.comap (thetaBarAct K)).map (Subgroup.normalizer (K : Set G)).subtype := by
      rw [← hAeq]
      refine sup_le (Subgroup.zpowers_le.mpr ⟨⟨x, hxN⟩, ?_, rfl⟩)
        (sup_le (Subgroup.zpowers_le.mpr ⟨⟨a, haNK⟩, ?_, rfl⟩)
          (Subgroup.zpowers_le.mpr ⟨⟨c, Subgroup.le_normalizer hcK⟩, ?_, rfl⟩))
      · change thetaBarAct K ⟨x, hxN⟩ ∈ P
        rw [hσdef]
        exact hσP
      · change thetaBarAct K ⟨a, haNK⟩ ∈ P
        rw [hσa]
        exact one_mem P
      · change thetaBarAct K ⟨c, Subgroup.le_normalizer hcK⟩ ∈ P
        rw [thetaBarAct_of_mem hcK]
        exact hcP
    intro g hg
    obtain ⟨⟨g', hg'N⟩, hmem, rfl⟩ := hle hg
    exact hmem
  have hσx : ∀ g (hg : g ∈ A), thetaBarAct K ⟨g, hAK hg⟩ * σ = σ * thetaBarAct K ⟨g, hAK hg⟩ := by
    intro g hg
    have e1 : (⟨g, hAK hg⟩ : Subgroup.normalizer (K : Set G)) * ⟨x, hxN⟩ =
        ⟨x, hxN⟩ * ⟨g, hAK hg⟩ := Subtype.ext (hAc g hg x hxA)
    rw [← hσdef, ← map_mul, e1, map_mul]
  apply hcomm
  by_cases htL : t ∈ Subgroup.normalizer (L : Set G)
  ·
    have hAt := conj_mem_sup_theta_of_mem_normalizer h hAE hSL haA haB haL hta htc htL
    set θL : Subgroup G := inSubgroup (aschbacherSolvableCore 3) L with hθL
    have hAL : A ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_sec12StdBar h
    have hAθ : A ≤ Subgroup.normalizer (θL : Set G) := fun x hx =>
      Subgroup.mem_normalizer_fintype fun n hn => conj_mem_inSubgroup_theta (hAL hx) hn
    have hAθset : ((A ⊔ θL : Subgroup G) : Set G) = (A : Set G) * (θL : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right A θL hAθ
    have hmemX := hAt x hxA
    rw [← SetLike.mem_coe, hAθset] at hmemX
    obtain ⟨y, hyA, n, hn, hyn⟩ := hmemX
    have hyn : y * n = t * x * t⁻¹ := hyn
    have hnL : n ∈ L := Subgroup.map_subtype_le _ hn
    have hna : n * a = a * n := by
      have e : n = y⁻¹ * (t * x * t⁻¹) := by rw [← hyn]; group
      have hta' : Commute t a := hta
      have hc1' : Commute (t * x * t⁻¹) a :=
        (hta'.mul_left (show Commute x a from hxa)).mul_left hta'.inv_left
      have hc2 : Commute y a := hAc y hyA a haA
      rw [e]
      exact (hc2.inv_left.mul_left hc1').eq
    have hnc : n * c = c * n := Subgroup.mem_centralizer_singleton_iff.mp (hLc hnL)
    have hnN := hNK n hna hnc
    have hn3 := not_three_dvd_orderOf_of_mem_theta hn
    have eN : (⟨n, hnN⟩ : Subgroup.normalizer (K : Set G)) =
        (⟨y, hAK hyA⟩ : Subgroup.normalizer (K : Set G))⁻¹ *
          (⟨t, htN⟩ * ⟨x, hxN⟩ * ⟨t, htN⟩⁻¹) := by
      apply Subtype.ext
      change n = y⁻¹ * (t * x * t⁻¹)
      rw [← hyn]
      group
    have hact : thetaBarAct K ⟨n, hnN⟩ = (thetaBarAct K ⟨y, hAK hyA⟩)⁻¹ * τσ := by
      rw [eN, map_mul, map_inv, map_mul, map_mul, map_inv, hπt, hσdef, hτdef]
    have hmemP : thetaBarAct K ⟨n, hnN⟩ ∈ P := by
      rw [hact]
      exact mul_mem (inv_mem (hAP y hyA)) hτσP
    have h1 := thetaBarAct_eq_one_of_mem_isPGroup hnN hn3 hP3 hmemP
    rw [hact, inv_mul_eq_one] at h1
    rw [← h1]
    exact (hσx y hyA).symm
  ·
    set L' := L.map (MulAut.conj t).toMonoidHom with hL'def
    have hL' : L' ∈ thetaComponentsAt 3 c := by
      have h1 := KS128NotHJSL.map_conj_mem_thetaComponentsAt Nat.prime_three hL t
      rwa [htc, thetaComponentsAt_inv'] at h1
    have hne : L ≠ L' := by
      intro h1
      apply htL
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact h1.symm
    obtain ⟨i, hx₁⟩ := exists_zpow_mul_mem_inf h hAE hSL haA haL x hxA
    obtain ⟨x₁, hx₁, hx₁def⟩ : ∃ x₁, x₁ ∈ A ⊓ L ∧ x₁ = a ^ (-i) * x := ⟨_, hx₁, rfl⟩
    set y := t * x₁ * t⁻¹ with hydef
    have hyL' : y ∈ L' := ⟨x₁, hx₁.2, rfl⟩
    have hnθ := Sec10.commutator_mem_theta_of_ne hL hL' hne hx₁.2 hyL'
    have hx₁a : Commute x₁ a := hAc x₁ hx₁.1 a haA
    have hya : Commute y a := by
      have hta' : Commute t a := hta
      exact (hta'.mul_left hx₁a).mul_left hta'.inv_left
    have hna : x₁ * y * x₁⁻¹ * y⁻¹ * a = a * (x₁ * y * x₁⁻¹ * y⁻¹) :=
      (((hx₁a.mul_left hya).mul_left hx₁a.inv_left).mul_left hya.inv_left).eq
    have hnc : x₁ * y * x₁⁻¹ * y⁻¹ * c = c * (x₁ * y * x₁⁻¹ * y⁻¹) :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.map_subtype_le _ hnθ)
    have hnN := hNK _ hna hnc
    have hn3 := not_three_dvd_orderOf_of_mem_theta hnθ
    have hx₁N : x₁ ∈ Subgroup.normalizer (K : Set G) := hAK hx₁.1
    have hyN : y ∈ Subgroup.normalizer (K : Set G) := mul_mem (mul_mem htN hx₁N) (inv_mem htN)
    have hX : thetaBarAct K ⟨x₁, hx₁N⟩ = σ := by
      have e : (⟨x₁, hx₁N⟩ : Subgroup.normalizer (K : Set G)) = ⟨a, haNK⟩ ^ (-i) * ⟨x, hxN⟩ := by
        apply Subtype.ext
        change x₁ = _
        rw [hx₁def]
        simp
      rw [e, map_mul, map_zpow, hσa, one_zpow, one_mul, hσdef]
    have hY : thetaBarAct K ⟨y, hyN⟩ = τσ := by
      have e : (⟨y, hyN⟩ : Subgroup.normalizer (K : Set G)) =
          ⟨t, htN⟩ * ⟨x₁, hx₁N⟩ * ⟨t, htN⟩⁻¹ := Subtype.ext rfl
      rw [e, map_mul, map_mul, map_inv, hπt, hX, hτdef]
    have eN : (⟨x₁ * y * x₁⁻¹ * y⁻¹, hnN⟩ : Subgroup.normalizer (K : Set G)) =
        ⟨x₁, hx₁N⟩ * ⟨y, hyN⟩ * ⟨x₁, hx₁N⟩⁻¹ * ⟨y, hyN⟩⁻¹ := Subtype.ext rfl
    have hn' : thetaBarAct K ⟨x₁ * y * x₁⁻¹ * y⁻¹, hnN⟩ = σ * τσ * σ⁻¹ * τσ⁻¹ := by
      rw [eN, map_mul, map_mul, map_mul, map_inv, map_inv, hX, hY]
    have hmemP : thetaBarAct K ⟨x₁ * y * x₁⁻¹ * y⁻¹, hnN⟩ ∈ P := by
      rw [hn']
      exact mul_mem (mul_mem (mul_mem hσP hτσP) (inv_mem hσP)) (inv_mem hτσP)
    have h1 := thetaBarAct_eq_one_of_mem_isPGroup hnN hn3 hP3 hmemP
    rw [hn'] at h1
    have h2 := mul_inv_eq_one.mp h1
    calc σ * τσ = σ * τσ * σ⁻¹ * σ := by group
      _ = τσ * σ := by rw [h2]

end CFSG.RankThree.PartTwo.Sec12.Res3Proof
