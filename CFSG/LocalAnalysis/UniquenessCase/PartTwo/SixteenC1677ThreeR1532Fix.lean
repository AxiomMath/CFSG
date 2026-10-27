module

import CFSG.ClassicalGroups.SpecialLinear.VectorStabilizer
import CFSG.RankThree.S4Free.Stellmacher25
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165ExclCard
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165ExclDirect
public import CFSG.Quasithin.Background.A3Structure314Excl

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

open scoped Matrix commutatorElement

private theorem s168e3_no_fix_nat {n q p : ℕ} {K : Type} [Field K] [Finite K]
    (hq : Nat.card K = q) (hn : 2 ≤ n) (hp : p.Prime)
    (hnotdvd : ¬ p * (q ^ n - 1) ∣ Nat.card (Matrix.SpecialLinearGroup (Fin n) K))
    {a : Matrix.SpecialLinearGroup (Fin n) K} (ha : orderOf a = p) :
    ∀ v : Fin n → K, a • v = v → v = 0 := by
  intro v hv
  by_contra hv0
  have hz : Subgroup.zpowers a ≤
      MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin n) K) v := by
    rw [Subgroup.zpowers_le]
    exact MulAction.mem_stabilizer_iff.mpr hv
  have hdvd1 : p ∣ Nat.card ↥(Subgroup.zpowers a) := by
    rw [Nat.card_zpowers, ha]
  have hdvd2 : Nat.card ↥(Subgroup.zpowers a) ∣
      Nat.card ↥(MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin n) K) v) :=
    Subgroup.card_dvd_of_le hz
  have hI : (MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin n) K) v).index =
      q ^ n - 1 := by
    rw [CFSG.ClassicalGroups.SpecialLinear.index_stabilizer_eq hn hv0, hq]
  have hcard : Nat.card ↥(MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin n) K) v) *
      (q ^ n - 1) = Nat.card (Matrix.SpecialLinearGroup (Fin n) K) := by
    rw [← hI]
    exact Subgroup.card_mul_index _
  obtain ⟨m, hm⟩ := hdvd1
  obtain ⟨k, hk⟩ := hdvd2
  exact hnotdvd ⟨m * k, by rw [← hcard, hk, hm]; ring⟩

private theorem s168e3_normalizer_of_directProd {A : Type*} [Group A] {L K N : Subgroup A}
    (hdir : IsDirectProdOfConj L K N) : L ≤ Subgroup.normalizer (K : Set A) := by
  rw [← hdir.2.1]
  refine iSup_le fun X => iSup_le fun hX => ?_
  by_cases hXK : X = K
  · rw [hXK]
    exact Subgroup.le_normalizer
  · rw [Subgroup.le_normalizer_iff_commutator_le_right, Subgroup.commutator_comm]
    rw [hdir.2.2.1 K (s15_T7_mem_conjSet_self K N) X hX (Ne.symm hXK)]
    exact bot_le

private theorem s168e3_isSimpleGroup_of_isAlt5 {X : Type} [Group X] (h : UC22.IsAlt X 5) :
    IsSimpleGroup X := by
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  exact e.isSimpleGroup

private theorem s168e3_isSimpleGroup_of_isL3 {X : Type} [Group X] (h : IsL3 X 1) :
    IsSimpleGroup X :=
  (CFSG.LieType.Simplicity.fam_PSL_simplicity X 3 2 1
    (CFSG.Blueprint.LieModel.statedClassicalModel h (by decide))).2

private theorem s168e3_simple_normal_factor {G : Type*} [Group G]
    {K Y₁ Y₂ : Subgroup G} (hKs : IsSimpleGroup ↥K) (hKnorm : K.Normal)
    (hY1norm : Y₁.Normal) (hY2norm : Y₂.Normal) (hsup : Y₁ ⊔ Y₂ = ⊤)
    (hdisj : Y₁ ⊓ Y₂ = ⊥) (hcardnp : ¬ (Nat.card ↥K).Prime) :
    K ≤ Y₁ ∨ K ≤ Y₂ := by
  have hsimple := (Subgroup.isSimpleGroup_iff (H := K)).1 hKs
  have hnorm1 : ((K ⊓ Y₁).subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro h k hh hk
    exact ⟨K.mul_mem (K.mul_mem hk hh.1) (K.inv_mem hk), hY1norm.conj_mem h hh.2 k⟩
  have hnorm2 : ((K ⊓ Y₂).subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro h k hh hk
    exact ⟨K.mul_mem (K.mul_mem hk hh.1) (K.inv_mem hk), hY2norm.conj_mem h hh.2 k⟩
  rcases hsimple.2 (K ⊓ Y₁) inf_le_left hnorm1 with h1 | h1
  · rcases hsimple.2 (K ⊓ Y₂) inf_le_left hnorm2 with h2 | h2
    · exfalso
      have hcomm1 : ⁅K, Y₁⁆ = ⊥ := by
        rw [eq_bot_iff]
        exact (le_inf (Subgroup.commutator_le_left K Y₁)
          (Subgroup.commutator_le_right K Y₁)).trans (le_of_eq h1)
      have hcomm2 : ⁅K, Y₂⁆ = ⊥ := by
        rw [eq_bot_iff]
        exact (le_inf (Subgroup.commutator_le_left K Y₂)
          (Subgroup.commutator_le_right K Y₂)).trans (le_of_eq h2)
      have hcent : ∀ k ∈ K, ∀ y ∈ Y₁, k * y = y * k := by
        intro k hk y hy
        have h : ⁅k, y⁆ = 1 := by
          have hmem := Subgroup.commutator_le.mp (le_of_eq hcomm1) k hk y hy
          simpa using hmem
        exact commutatorElement_eq_one_iff_mul_comm.mp h
      have hcent2 : ∀ k ∈ K, ∀ y ∈ Y₂, k * y = y * k := by
        intro k hk y hy
        have h : ⁅k, y⁆ = 1 := by
          have hmem := Subgroup.commutator_le.mp (le_of_eq hcomm2) k hk y hy
          simpa using hmem
        exact commutatorElement_eq_one_iff_mul_comm.mp h
      have habel : ∀ a b : ↥K, a * b = b * a := by
        intro a b
        obtain ⟨y₁, hy₁, y₂, hy₂, hyb⟩ :=
          (Subgroup.mem_sup_of_normal_right (s := Y₁) (t := Y₂)).mp
            (by rw [hsup]; exact Subgroup.mem_top (b : G))
        apply Subtype.ext
        have hb : (b : G) = y₁ * y₂ := hyb.symm
        calc (a : G) * (b : G) = (a : G) * (y₁ * y₂) := by rw [hb]
          _ = ((a : G) * y₁) * y₂ := by group
          _ = (y₁ * (a : G)) * y₂ := by rw [hcent (a : G) a.2 y₁ hy₁]
          _ = y₁ * ((a : G) * y₂) := by group
          _ = y₁ * (y₂ * (a : G)) := by rw [hcent2 (a : G) a.2 y₂ hy₂]
          _ = (y₁ * y₂) * (a : G) := by group
          _ = (b : G) * (a : G) := by rw [← hb]
      have hcenter : Subgroup.center ↥K = ⊤ := by
        rw [eq_top_iff]
        intro x _
        rw [Subgroup.mem_center_iff]
        intro y
        exact (habel x y).symm
      letI : CommGroup ↥K := Group.commGroupOfCenterEqTop hcenter
      exact hcardnp ((CommGroup.is_simple_iff_prime_card).mp hKs)
    · exact Or.inr (by rw [← h2]; exact inf_le_right)
  · exact Or.inl (by rw [← h1]; exact inf_le_right)

private theorem s168e3_matrix_eq_zero_of_mul_eq_self {d : ℕ} {K : Type} [Field K]
    {A X : Matrix (Fin d) (Fin d) K} (h : ∀ v : Fin d → K, A.mulVec v = v → v = 0)
    (hX : A * X = X) : X = 0 := by
  ext i j
  have hcol : A.mulVec (fun k => X k j) = (fun k => X k j) := by
    ext i
    have := congrFun (congrFun hX i) j
    rwa [Matrix.mul_apply] at this
  exact congrFun (h (fun k => X k j) hcol) i

private theorem s168e3_no_fix_statedSL {n q p : ℕ} {K : Type} [Field K] [Finite K]
    (hq : Nat.card K = q) (hn : 2 ≤ n) (hp : p.Prime)
    (hnotdvd : ¬ p * (q ^ n - 1) ∣ Nat.card (Matrix.SpecialLinearGroup (Fin n) K))
    {a : ↥(StatedSL n K)} (ha : orderOf a = p) :
    ∀ v : Fin n → K, ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec v = v → v = 0 := by
  intro v hv
  let e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K
  let b : Matrix.SpecialLinearGroup (Fin n) K := e.symm a
  have hea : e b = a := by simp [b]
  have hb : orderOf b = p := by
    have h := MulEquiv.orderOf_eq e b
    rw [hea] at h
    rw [← h, ha]
  have hcoe : ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    have h := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe n K b
    rw [hea] at h
    exact h.symm
  have hv' : b • v = v := by
    rw [Matrix.SpecialLinearGroup.smul_def]
    change ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec v = v
    rw [hcoe]
    exact hv
  exact s168e3_no_fix_nat hq hn hp hnotdvd hb v hv'

private theorem s168e3_no_fix_statedSL_two_four {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) {a : ↥(StatedSL 2 K)} (ha : orderOf a = 5) :
    ∀ v : Fin 2 → K, ((a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec v = v → v = 0 := by
  refine s168e3_no_fix_statedSL (n := 2) (q := 4) (p := 5) hK (by norm_num) (by norm_num) ?_ ha
  intro hdvd
  have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = 60 := by
    rw [← CFSG.Open.StatedAPI.card_statedSL 2 K, CFSG.Open.StatedAPI.card_statedSL_two, hK]
    norm_num
  rw [hcard] at hdvd
  norm_num at hdvd

private theorem s168e3_no_fix_statedSL_three_two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {a : ↥(StatedSL 3 K)} (ha : orderOf a = 7) :
    ∀ v : Fin 3 → K, ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v = v → v = 0 := by
  refine s168e3_no_fix_statedSL (n := 3) (q := 2) (p := 7) hK (by norm_num) (by norm_num) ?_ ha
  intro hdvd
  have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) = 168 := by
    rw [← CFSG.Open.StatedAPI.card_statedSL 3 K, CFSG.Open.StatedAPI.card_statedSL_three, hK]
    norm_num
  rw [hcard] at hdvd
  norm_num at hdvd

section Generic

variable {W : Type} [CommGroup W]

private theorem s168e3_153_2_tensor_fix_of_model [Finite W]
    {A L K₀ : Subgroup (MulAut W)} {d p : ℕ} {K : Type} [Field K] [Finite K]
    (hdir : IsDirectProdOfConj L K₀ (A ⊓ Subgroup.normalizer (L : Set (MulAut W))))
    (h2 : (conjSet K₀ (A ⊓ Subgroup.normalizer (L : Set (MulAut W)))).ncard = 2)
    (hK0 : Nat.card ↥K₀ = Nat.card ↥(StatedSL d K))
    (hK0s : IsSimpleGroup ↥K₀)
    (hK0cardnp : ¬ (Nat.card ↥K₀).Prime)
    (hNoFix : ∀ c : ↥(StatedSL d K), orderOf c = p → ∀ v : Fin d → K,
      ((c : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).mulVec v = v → v = 0)
    (hReal : (FFModel.tensorNat d K).Realizes L (commSub ⊤ L) ⊥)
    {x : MulAut W} (hx : x ∈ K₀) (hxp : orderOf x = p) :
    ∀ w ∈ commSub ⊤ L, x w = w → w = 1 := by
  classical
  obtain ⟨π, hVia⟩ := hReal
  obtain ⟨hπsurj, -, -, hUinv, -, -, -, β, -, hβ1, hβint⟩ := hVia
  haveI : Finite (FFModel.tensorNat d K).Gam :=
    show Finite (↥(StatedSL d K) × ↥(StatedSL d K)) from inferInstance
  have hGamcard : Nat.card (FFModel.tensorNat d K).Gam = Nat.card ↥(StatedSL d K) ^ 2 := by
    show Nat.card (↥(StatedSL d K) × ↥(StatedSL d K)) = _
    rw [Nat.card_prod, sq]
  have hLcard : Nat.card ↥L = Nat.card ↥(StatedSL d K) ^ 2 := by
    rw [Om8Excl.card_eq_sq_of_ncard_two hdir h2, hK0]
  have hπbij : Function.Bijective π :=
    hπsurj.bijective_of_nat_card_le (by rw [hGamcard, hLcard])
  let πp : (↥(StatedSL d K) × ↥(StatedSL d K)) →* ↥L := π
  have hπpinj : Function.Injective πp := hπbij.1
  have hπpsurj : Function.Surjective πp := hπsurj
  have hβintP : ∀ (γ : ↥(StatedSL d K) × ↥(StatedSL d K)) (u : ↥(commSub ⊤ L))
      (m : ↥(FFModel.tensorNat d K).sec)
      (hu : ((πp γ : ↥L) : MulAut W) (u : W) ∈ commSub ⊤ L)
      (hm : (FFModel.tensorNat d K).act γ (m : (FFModel.tensorNat d K).Amb) ∈
        (FFModel.tensorNat d K).sec),
      β u = QuotientGroup.mk (s := (FFModel.tensorNat d K).ker.subgroupOf
        (FFModel.tensorNat d K).sec) m →
      β ⟨((πp γ : ↥L) : MulAut W) (u : W), hu⟩ = QuotientGroup.mk
        (s := (FFModel.tensorNat d K).ker.subgroupOf (FFModel.tensorNat d K).sec)
        ⟨(FFModel.tensorNat d K).act γ (m : (FFModel.tensorNat d K).Amb), hm⟩ := by
    intro γ u m hu hm h
    exact hβint γ u m hu hm h
  let inlR : Subgroup (↥(StatedSL d K) × ↥(StatedSL d K)) :=
    (MonoidHom.inl (↥(StatedSL d K)) (↥(StatedSL d K))).range
  let inrR : Subgroup (↥(StatedSL d K) × ↥(StatedSL d K)) :=
    (MonoidHom.inr (↥(StatedSL d K)) (↥(StatedSL d K))).range
  let Y₁ : Subgroup ↥L := inlR.map πp
  let Y₂ : Subgroup ↥L := inrR.map πp
  let K₀L : Subgroup ↥L := K₀.subgroupOf L
  have hK0L : K₀ ≤ L := hdir.1 K₀ (s15_T7_mem_conjSet_self K₀ _)
  have hInlN : inlR.Normal := by
    refine Subgroup.Normal.mk fun z hz g => ?_
    change z ∈ (MonoidHom.inl (↥(StatedSL d K)) (↥(StatedSL d K))).range at hz
    rw [MonoidHom.mem_range] at hz
    obtain ⟨c, rfl⟩ := hz
    exact ⟨g.1 * c * g.1⁻¹, by ext <;> simp [MonoidHom.inl_apply]⟩
  have hInrN : inrR.Normal := by
    refine Subgroup.Normal.mk fun z hz g => ?_
    change z ∈ (MonoidHom.inr (↥(StatedSL d K)) (↥(StatedSL d K))).range at hz
    rw [MonoidHom.mem_range] at hz
    obtain ⟨c, rfl⟩ := hz
    exact ⟨g.2 * c * g.2⁻¹, by ext <;> simp [MonoidHom.inr_apply]⟩
  have hY1norm : Y₁.Normal := Subgroup.Normal.map hInlN πp hπpsurj
  have hY2norm : Y₂.Normal := Subgroup.Normal.map hInrN πp hπpsurj
  have hK0normL : L ≤ Subgroup.normalizer (K₀ : Set (MulAut W)) :=
    s168e3_normalizer_of_directProd hdir
  have hK0Lnorm : K₀L.Normal := by
    rw [Subgroup.normal_subgroupOf_iff hK0L]
    intro h k hh hk
    exact ((Subgroup.mem_normalizer_iff.mp (hK0normL hk)) h).mp hh
  have hdisjR : inlR ⊓ inrR = ⊥ := by
    rw [eq_bot_iff]
    rintro ⟨u, v⟩ h
    change (u, v) ∈ (MonoidHom.inl (↥(StatedSL d K)) (↥(StatedSL d K))).range ⊓
      (MonoidHom.inr (↥(StatedSL d K)) (↥(StatedSL d K))).range at h
    rw [Subgroup.mem_inf, MonoidHom.mem_range, MonoidHom.mem_range] at h
    obtain ⟨⟨c, hc⟩, ⟨e, he⟩⟩ := h
    rw [MonoidHom.inl_apply] at hc
    rw [MonoidHom.inr_apply] at he
    rw [Subgroup.mem_bot]
    ext <;> simp_all
  have hdisj : Y₁ ⊓ Y₂ = ⊥ := by
    change (inlR.map πp) ⊓ (inrR.map πp) = ⊥
    rw [← Subgroup.map_inf_eq inlR inrR πp hπpinj, hdisjR, Subgroup.map_bot]
  have hsupR : inlR ⊔ inrR = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨a, b⟩ -
    have h1 : (MonoidHom.inl (↥(StatedSL d K)) (↥(StatedSL d K))) a ∈ inlR := ⟨a, rfl⟩
    have h2 : (MonoidHom.inr (↥(StatedSL d K)) (↥(StatedSL d K))) b ∈ inrR := ⟨b, rfl⟩
    have h : (MonoidHom.inl (↥(StatedSL d K)) (↥(StatedSL d K))) a *
        (MonoidHom.inr (↥(StatedSL d K)) (↥(StatedSL d K))) b = (a, b) := by
      ext <;> simp [MonoidHom.inl_apply, MonoidHom.inr_apply]
    rw [← h]
    haveI : inrR.Normal := hInrN
    exact (Subgroup.mem_sup_of_normal_right (s := inlR) (t := inrR)).mpr ⟨_, h1, _, h2, rfl⟩
  have hsup : Y₁ ⊔ Y₂ = ⊤ := by
    change (inlR.map πp) ⊔ (inrR.map πp) = ⊤
    rw [← Subgroup.map_sup, hsupR, Subgroup.map_top, MonoidHom.range_eq_top.mpr hπpsurj]
  have hK0Ls : IsSimpleGroup ↥K₀L := by
    haveI : IsSimpleGroup ↥K₀ := hK0s
    exact (Subgroup.subgroupOfEquivOfLe hK0L).isSimpleGroup
  have hK0Lcardnp : ¬ (Nat.card ↥K₀L).Prime := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK0L).toEquiv]
    exact hK0cardnp
  have hle := s168e3_simple_normal_factor hK0Ls hK0Lnorm hY1norm hY2norm hsup hdisj hK0Lcardnp
  have hβinj : Function.Injective β := by
    intro u v huv
    have h1 : β (u * v⁻¹) = 1 := by rw [map_mul, map_inv, huv, mul_inv_cancel]
    have h2 : ((u * v⁻¹ : ↥(commSub ⊤ L)) : W) ∈ (⊥ : Subgroup W) :=
      (hβ1 (u * v⁻¹)).1 h1
    rw [Subgroup.mem_bot] at h2
    have h3 : u * v⁻¹ = 1 := Subtype.ext h2
    rwa [mul_inv_eq_one] at h3
  intro w hw hxw
  rcases hle with hle | hle
  · have hxK0L : (⟨x, hK0L hx⟩ : ↥L) ∈ K₀L := Subgroup.mem_subgroupOf.mpr hx
    obtain ⟨γ, hγinl, hπγ⟩ := Subgroup.mem_map.mp (show (⟨x, hK0L hx⟩ : ↥L) ∈
      Subgroup.map πp inlR from hle hxK0L)
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp (show γ ∈
      (MonoidHom.inl (↥(StatedSL d K)) (↥(StatedSL d K))).range from hγinl)
    have hγeq : γ = (c, 1) := by rw [← hc, MonoidHom.inl_apply]
    have hπγcoe : ((πp γ : ↥L) : MulAut W) = x := by rw [hπγ]
    have horderγ : orderOf γ = p := by
      rw [← orderOf_injective πp hπpinj γ, ← Subgroup.orderOf_coe (πp γ), hπγcoe, hxp]
    have horderc : orderOf c = p := by
      have h2c : orderOf γ = orderOf c := by
        rw [hγeq]
        simp [Prod.orderOf]
      rwa [← h2c]
    have hmemU : ((πp γ : ↥L) : MulAut W) w ∈ commSub ⊤ L := hUinv (πp γ) w hw
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨w, hw⟩)
    have hmemsec : (FFModel.tensorNat d K).act γ (m : (FFModel.tensorNat d K).Amb) ∈
        (FFModel.tensorNat d K).sec := Subgroup.mem_top _
    have hβint' := hβintP γ ⟨w, hw⟩ m hmemU hmemsec hm.symm
    have hβeq : β ⟨((πp γ : ↥L) : MulAut W) w, hUinv (πp γ) w hw⟩ = β ⟨w, hw⟩ := by
      apply congrArg β
      apply Subtype.ext
      change ((πp γ : ↥L) : MulAut W) w = w
      rw [hπγcoe]
      exact hxw
    have hmk : QuotientGroup.mk
        (s := (FFModel.tensorNat d K).ker.subgroupOf (FFModel.tensorNat d K).sec)
        ⟨(FFModel.tensorNat d K).act γ (m : (FFModel.tensorNat d K).Amb), hmemsec⟩ =
        QuotientGroup.mk (s := (FFModel.tensorNat d K).ker.subgroupOf
          (FFModel.tensorNat d K).sec) m := by
      rw [← hβint', hβeq, hm.symm]
    have hm_eq : (⟨(FFModel.tensorNat d K).act γ (m : (FFModel.tensorNat d K).Amb),
        hmemsec⟩ : ↥(FFModel.tensorNat d K).sec) = m := by
      rw [← inv_mul_eq_one]
      have hmem := (QuotientGroup.eq).mp hmk
      have hker : (FFModel.tensorNat d K).ker = ⊥ := rfl
      rwa [hker, Subgroup.bot_subgroupOf, Subgroup.mem_bot] at hmem
    have hact : (FFModel.tensorNat d K).act γ (m : (FFModel.tensorNat d K).Amb) =
        (m : (FFModel.tensorNat d K).Amb) := congrArg Subtype.val hm_eq
    let X : Matrix (Fin d) (Fin d) K :=
      Multiplicative.toAdd (m : (FFModel.tensorNat d K).Amb)
    have hmat : ((γ.1 : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        X * ((γ.2 : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K)ᵀ =
        X := by
      have h : Multiplicative.ofAdd (((γ.1 : Matrix.GeneralLinearGroup (Fin d) K) :
          Matrix (Fin d) (Fin d) K) * X *
          ((γ.2 : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K)ᵀ) =
          Multiplicative.ofAdd X := by
        simpa [X, FFModel.tensorNat, tensorAct] using hact
      exact Multiplicative.ofAdd.injective h
    have hmatX : ((c : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        X = X := by
      rw [hγeq] at hmat
      simpa using hmat
    have hX0 : X = 0 :=
      s168e3_matrix_eq_zero_of_mul_eq_self (hNoFix c horderc) hmatX
    have hm1 : (m : (FFModel.tensorNat d K).Amb) = 1 := by
      have h : Multiplicative.ofAdd X = (1 : (FFModel.tensorNat d K).Amb) := by
        rw [hX0]
        rfl
      exact h
    have hmone : m = 1 := Subtype.ext hm1
    have hw1 : β ⟨w, hw⟩ = 1 := by rw [← hm, hmone]; rfl
    exact Subgroup.mem_bot.mp ((hβ1 ⟨w, hw⟩).1 hw1)
  · have hxK0L : (⟨x, hK0L hx⟩ : ↥L) ∈ K₀L := Subgroup.mem_subgroupOf.mpr hx
    obtain ⟨γ, hγinr, hπγ⟩ := Subgroup.mem_map.mp (show (⟨x, hK0L hx⟩ : ↥L) ∈
      Subgroup.map πp inrR from hle hxK0L)
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp (show γ ∈
      (MonoidHom.inr (↥(StatedSL d K)) (↥(StatedSL d K))).range from hγinr)
    have hγeq : γ = (1, c) := by rw [← hc, MonoidHom.inr_apply]
    have hπγcoe : ((πp γ : ↥L) : MulAut W) = x := by rw [hπγ]
    have horderγ : orderOf γ = p := by
      rw [← orderOf_injective πp hπpinj γ, ← Subgroup.orderOf_coe (πp γ), hπγcoe, hxp]
    have horderc : orderOf c = p := by
      have h2c : orderOf γ = orderOf c := by
        rw [hγeq]
        simp [Prod.orderOf]
      rwa [← h2c]
    have hmemU : ((πp γ : ↥L) : MulAut W) w ∈ commSub ⊤ L := hUinv (πp γ) w hw
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨w, hw⟩)
    have hmemsec : (FFModel.tensorNat d K).act γ (m : (FFModel.tensorNat d K).Amb) ∈
        (FFModel.tensorNat d K).sec := Subgroup.mem_top _
    have hβint' := hβintP γ ⟨w, hw⟩ m hmemU hmemsec hm.symm
    have hβeq : β ⟨((πp γ : ↥L) : MulAut W) w, hUinv (πp γ) w hw⟩ = β ⟨w, hw⟩ := by
      apply congrArg β
      apply Subtype.ext
      change ((πp γ : ↥L) : MulAut W) w = w
      rw [hπγcoe]
      exact hxw
    have hmk : QuotientGroup.mk
        (s := (FFModel.tensorNat d K).ker.subgroupOf (FFModel.tensorNat d K).sec)
        ⟨(FFModel.tensorNat d K).act γ (m : (FFModel.tensorNat d K).Amb), hmemsec⟩ =
        QuotientGroup.mk (s := (FFModel.tensorNat d K).ker.subgroupOf
          (FFModel.tensorNat d K).sec) m := by
      rw [← hβint', hβeq, hm.symm]
    have hm_eq : (⟨(FFModel.tensorNat d K).act γ (m : (FFModel.tensorNat d K).Amb),
        hmemsec⟩ : ↥(FFModel.tensorNat d K).sec) = m := by
      rw [← inv_mul_eq_one]
      have hmem := (QuotientGroup.eq).mp hmk
      have hker : (FFModel.tensorNat d K).ker = ⊥ := rfl
      rwa [hker, Subgroup.bot_subgroupOf, Subgroup.mem_bot] at hmem
    have hact : (FFModel.tensorNat d K).act γ (m : (FFModel.tensorNat d K).Amb) =
        (m : (FFModel.tensorNat d K).Amb) := congrArg Subtype.val hm_eq
    let X : Matrix (Fin d) (Fin d) K :=
      Multiplicative.toAdd (m : (FFModel.tensorNat d K).Amb)
    have hmat : ((γ.1 : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        X * ((γ.2 : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K)ᵀ =
        X := by
      have h : Multiplicative.ofAdd (((γ.1 : Matrix.GeneralLinearGroup (Fin d) K) :
          Matrix (Fin d) (Fin d) K) * X *
          ((γ.2 : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K)ᵀ) =
          Multiplicative.ofAdd X := by
        simpa [X, FFModel.tensorNat, tensorAct] using hact
      exact Multiplicative.ofAdd.injective h
    have hmatY : X * ((c : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K)ᵀ =
        X := by
      rw [hγeq] at hmat
      simpa using hmat
    have hmatT : ((c : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        Xᵀ = Xᵀ := by
      have := congrArg Matrix.transpose hmatY
      simpa using this
    have hX0 : Xᵀ = 0 :=
      s168e3_matrix_eq_zero_of_mul_eq_self (hNoFix c horderc) hmatT
    have hX0' : X = 0 := by
      have := congrArg Matrix.transpose hX0
      simpa using this
    have hm1 : (m : (FFModel.tensorNat d K).Amb) = 1 := by
      have h : Multiplicative.ofAdd X = (1 : (FFModel.tensorNat d K).Amb) := by
        rw [hX0']
        rfl
      exact h
    have hmone : m = 1 := Subtype.ext hm1
    have hw1 : β ⟨w, hw⟩ = 1 := by rw [← hm, hmone]; rfl
    exact Subgroup.mem_bot.mp ((hβ1 ⟨w, hw⟩).1 hw1)

theorem s168e3_153_2_tensor_fix [Finite W] {A L K₀ : Subgroup (MulAut W)}
    (hdir : IsDirectProdOfConj L K₀ (A ⊓ Subgroup.normalizer (L : Set (MulAut W))))
    (h2 : (conjSet K₀ (A ⊓ Subgroup.normalizer (L : Set (MulAut W)))).ncard = 2) {p : ℕ}
    (hT : (p = 5 ∧ NatTensor L (commSub ⊤ L) ⊥ 2 2) ∨ (p = 7 ∧ NatTensor L (commSub ⊤ L) ⊥ 3 1))
    (hK : (p = 5 ∧ UC22.IsAlt ↥K₀ 5) ∨ (p = 7 ∧ IsL3 ↥K₀ 1))
    {x : MulAut W} (hx : x ∈ K₀) (hxp : orderOf x = p) :
    ∀ w ∈ commSub ⊤ L, x w = w → w = 1 := by
  rcases hT with ⟨rfl, hT⟩ | ⟨rfl, hT⟩
  · rcases hK with ⟨-, hAlt⟩ | ⟨h75, -⟩
    · obtain ⟨K, _, _, hKcard, hReal⟩ := hT
      have hK4 : Nat.card K = 4 := by rw [hKcard]; norm_num
      have hK0 : Nat.card ↥K₀ = Nat.card ↥(StatedSL 2 K) := by
        rw [CFSG.Quasithin.A314.card_isAlt_five hAlt,
          CFSG.Open.StatedAPI.card_statedSL_two, hK4]
        norm_num
      have hK0s : IsSimpleGroup ↥K₀ := s168e3_isSimpleGroup_of_isAlt5 hAlt
      have hK0cardnp : ¬ (Nat.card ↥K₀).Prime := by
        rw [CFSG.Quasithin.A314.card_isAlt_five hAlt]; norm_num
      exact s168e3_153_2_tensor_fix_of_model hdir h2 hK0 hK0s hK0cardnp
        (fun c hc => s168e3_no_fix_statedSL_two_four (a := c) hK4 hc) hReal hx hxp
    · exact absurd h75 (by norm_num)
  · rcases hK with ⟨h57, -⟩ | ⟨-, hL3⟩
    · exact absurd h57 (by norm_num)
    · obtain ⟨K, _, _, hKcard, hReal⟩ := hT
      have hK2 : Nat.card K = 2 := by rw [hKcard]; norm_num
      have hK0 : Nat.card ↥K₀ = Nat.card ↥(StatedSL 3 K) := by
        rw [Om8Excl.card_isL3_one hL3, CFSG.Open.StatedAPI.card_statedSL_three, hK2]
        norm_num
      have hK0s : IsSimpleGroup ↥K₀ := s168e3_isSimpleGroup_of_isL3 hL3
      have hK0cardnp : ¬ (Nat.card ↥K₀).Prime := by
        rw [Om8Excl.card_isL3_one hL3]; norm_num
      exact s168e3_153_2_tensor_fix_of_model hdir h2 hK0 hK0s hK0cardnp
        (fun c hc => s168e3_no_fix_statedSL_three_two (a := c) hK2 hc) hReal hx hxp

theorem s168e3_153_2_count {W' : Type} [CommGroup W'] [Finite W] [Finite W']
    {ρ : W →* W'} (hρ : Function.Bijective ρ) {x : MulAut W} {x' : MulAut W'}
    (hρx : ∀ w : W, ρ (x w) = x' (ρ w)) (hfix : ∀ w : W, x w = w → w = 1)
    {K' : Subgroup (MulAut W')} (hx' : x' ∈ K')
    (hrk : rk ↥(commSub ⊤ K') < rk ↥(⊤ : Subgroup W)) : False := by
  have hfixV : fixV (Subgroup.zpowers x') = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro v hv
    obtain ⟨w, rfl⟩ := hρ.2 v
    have hvx : x' (ρ w) = ρ w := (mem_fixV.mp hv) x' (Subgroup.mem_zpowers x')
    have hxw : x w = w := hρ.1 (by rw [hρx]; exact hvx)
    rw [hfix w hxw, map_one]
  have hstab : x' ∈ stabSub (⊤ : Subgroup W') := fun _ => Iff.rfl
  have hsum := CFSG.RankThree.S4Free.Stell.rk_commSub_add_rk_inf_fixV (V := W') (g := x')
    (W := (⊤ : Subgroup W')) hstab
  rw [hfixV, top_inf_eq, rk_bot, add_zero] at hsum
  have hcard : Nat.card W = Nat.card W' := Nat.card_congr (Equiv.ofBijective ρ hρ)
  have hrktop : rk ↥(⊤ : Subgroup W') = rk ↥(⊤ : Subgroup W) := by
    rw [rk_top, rk_top]
    unfold rk
    rw [hcard]
  have hle : commSub ⊤ (Subgroup.zpowers x') ≤ commSub ⊤ K' :=
    commSub_mono le_rfl (Subgroup.zpowers_le.mpr hx')
  have hrkle : rk ↥(commSub ⊤ (Subgroup.zpowers x')) ≤ rk ↥(commSub ⊤ K') := rk_mono hle
  rw [hsum, hrktop] at hrkle
  exact absurd hrkle (not_le.mpr hrk)

end Generic

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
