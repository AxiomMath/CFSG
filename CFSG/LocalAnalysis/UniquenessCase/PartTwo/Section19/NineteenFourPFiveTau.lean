module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourPFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourOuterFactor
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mem_pCoreOf_sup_of_conj_trivial_19 {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) {x : G}
    (hxH : x ∈ L ⊔ K ⊔ D.T) (hxN : x ∈ normalizer ((L ⊔ K : Subgroup G) : Set G))
    (hx : UC6S846.rhoL (L ⊔ K) ⟨x, hxN⟩ = 1) : x ∈ pCoreOf 2 (L ⊔ K ⊔ D.T) := by
  classical
  have hTJ : D.T ≤ normalizer ((L ⊔ K : Subgroup G) : Set G) := by
    rw [← h.hLK]
    exact D.sylowM.le.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
      (S17.Lp_le_M D 5)).mp (s13_Lp_normal D.M 5))
  have hkerJ : ∀ y ∈ L ⊔ K, ∀ hy : y ∈ normalizer ((L ⊔ K : Subgroup G) : Set G),
      UC6S846.rhoL (L ⊔ K) ⟨y, hy⟩ = 1 → y ∈ pCoreOf 2 (L ⊔ K) := by
    intro y hyJ hy hρ
    have hyc : (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K))) ⟨y, hyJ⟩ ∈
        Subgroup.center (Bar2 (L ⊔ K)) := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(L ⊔ K)) w
      have hcomm : ⁅z, (⟨y, hyJ⟩ : ↥(L ⊔ K))⁆ ∈ CFSG.pCore 2 ↥(L ⊔ K) := by
        have h1 : ⁅(⟨y, hyJ⟩ : ↥(L ⊔ K)), z⁆ ∈ CFSG.pCore 2 ↥(L ⊔ K) := by
          have h2 : ⁅y, (z : G)⁆ ∈ pCoreOf 2 (L ⊔ K) :=
            (UC6S846.rhoL_fix_iff (L ⊔ K) ⟨y, hy⟩ z).mp (by rw [hρ]; rfl)
          rw [pCoreOf] at h2
          obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.mp h2
          have hce' : (⁅(⟨y, hyJ⟩ : ↥(L ⊔ K)), z⁆ : ↥(L ⊔ K)) = c := by
            refine Subtype.ext ?_
            rw [show (↑c : G) = y * (z : G) * y⁻¹ * (z : G)⁻¹ from hce]
            simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
          rw [hce']
          exact hc
        rw [← commutatorElement_inv]
        exact Subgroup.inv_mem _ h1
      exact (QuotientGroup.commute_mk_iff (N := CFSG.pCore 2 ↥(L ⊔ K))
        (a := z) (b := (⟨y, hyJ⟩ : ↥(L ⊔ K)))).mpr hcomm
    have hmem : (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K))) ⟨y, hyJ⟩ ∈
        (⊥ : Subgroup (Bar2 (L ⊔ K))) := by
      rw [← center_bar2_sup_eq_bot_19 h]
      exact hyc
    have hy1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K))) ⟨y, hyJ⟩ = 1 := by
      simpa using hmem
    have hker : (⟨y, hyJ⟩ : ↥(L ⊔ K)) ∈ (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K))).ker :=
      MonoidHom.mem_ker.mpr hy1
    rw [show (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K))).ker =
      (pCoreOf 2 (L ⊔ K)).subgroupOf (L ⊔ K) from by
        rw [QuotientGroup.ker_mk', CFSG.openPCoreOf_subgroupOf]] at hker
    exact Subgroup.mem_subgroupOf.mp hker
  exact UC6S846.mem_pCoreOf_sup_of_rhoL_eq_one D.sylowM.isPGroup hTJ hkerJ hxH hxN hx

theorem le_sup_of_centralizes_diag_19 {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) {s : G} (hsT : s ∈ D.T) (hs2 : s ^ 2 = 1)
    (hsL : s ∉ normalizer (L : Set G)) {x : G}
    (hxH : x ∈ E1.tauOf (L ⊔ K ⊔ D.T) (L ⊔ K ⊔ D.T) (Subgroup.zpowers s))
    (hxc : ∀ d ∈ (L ⊔ K) ⊓ E1.tauOf (L ⊔ K ⊔ D.T) (L ⊔ K ⊔ D.T) (Subgroup.zpowers s),
      ⁅x, d⁆ ∈ pCoreOf 2 (L ⊔ K ⊔ D.T)) :
    x ∈ pCoreOf 2 (L ⊔ K ⊔ D.T) ⊔ Subgroup.zpowers s := by
  classical
  obtain ⟨hxH', hxQ, hxs⟩ := E1.mem_tauOf.mp hxH
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hyp.hL.1.1
  have hKM : K ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hK.1
  have hHM : L ⊔ K ⊔ D.T ≤ D.M := sup_le (sup_le hLM hKM) D.sylowM.le
  have hxM : x ∈ D.M := hHM hxH'
  have hTJ : D.T ≤ normalizer ((L ⊔ K : Subgroup G) : Set G) := by
    rw [← h.hLK]
    exact D.sylowM.le.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
      (S17.Lp_le_M D 5)).mp (s13_Lp_normal D.M 5))
  have hJN : L ⊔ K ⊔ D.T ≤ normalizer ((L ⊔ K : Subgroup G) : Set G) :=
    sup_le le_normalizer hTJ
  have hxN : x ∈ normalizer ((L ⊔ K : Subgroup G) : Set G) := hJN hxH'
  have hsN : s ∈ normalizer ((L ⊔ K : Subgroup G) : Set G) := hJN (Subgroup.mem_sup_right hsT)
  have hs1 : s ≠ 1 := by
    intro h1
    exact hsL (h1 ▸ Subgroup.one_mem _)
  have hsord : orderOf s = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_iff_pow_eq_one.mpr hs2) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hs1
    · exact h1
  have hss : s * s = 1 := by simpa [pow_two] using hs2
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_left hss
  have hperm : PermutesPair D.M L K := permutesPair_of_ctx19_one h
  have hswap : L.map (MulAut.conj s).toMonoidHom = K ∧
      K.map (MulAut.conj s).toMonoidHom = L := by
    rcases hperm s (D.sylowM.le hsT) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1) hsL
    · exact ⟨h1, h2⟩
  have hLc : L ∈ calC D.M := h.hyp.hL.1
  have hKc : K ∈ calC D.M := h.hK
  have hne : L ≠ K := h.hne.symm
  have hKL : K ≤ normalizer (L : Set G) := calC_le_normalizer_of_ne hLc hKc hne
  have hLK : L ≤ normalizer (K : Set G) := calC_le_normalizer_of_ne hKc hLc hne.symm
  have hLJ : L ∈ calC (L ⊔ K) := by
    refine ⟨?_, hLc.2.1, hLc.2.2⟩
    have hnorm : (L.subgroupOf (L ⊔ K)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
        (sup_le Subgroup.le_normalizer hKL)
    exact CFSG.Open.IsSubnormal.step le_sup_left hnorm (CFSG.Open.IsSubnormal.refl _)
  have hKJ : K ∈ calC (L ⊔ K) := by
    refine ⟨?_, hKc.2.1, hKc.2.2⟩
    have hnorm : (K.subgroupOf (L ⊔ K)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).2
        (sup_le hLK Subgroup.le_normalizer)
    exact CFSG.Open.IsSubnormal.step le_sup_right hnorm (CFSG.Open.IsSubnormal.refl _)
  have hQL : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ K) :=
    CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 le_sup_left
      (sup_le le_normalizer hKL)
  have hQK : pCoreOf 2 K ≤ pCoreOf 2 (L ⊔ K) :=
    CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 le_sup_right
      (sup_le hLK le_normalizer)
  have hQJ : pCoreOf 2 (L ⊔ K) ≤ pCoreOf 2 (L ⊔ K ⊔ D.T) :=
    CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 le_sup_left
      (sup_le le_normalizer hTJ)
  have hQHnorm : ((pCoreOf 2 (L ⊔ K ⊔ D.T)).subgroupOf (L ⊔ K ⊔ D.T)).Normal := by
    rw [CFSG.openPCoreOf_subgroupOf]
    exact CFSG.pCore_normal
  have hQN : L ⊔ K ⊔ D.T ≤ normalizer (pCoreOf 2 (L ⊔ K ⊔ D.T) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (CFSG.LieType.BorelTits.pCoreOf_le 2 _)).mp hQHnorm
  have hLnorm : (L.subgroupOf (L ⊔ K)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
      (sup_le Subgroup.le_normalizer hKL)
  set f₁ : Subgroup (Bar2 (L ⊔ K)) := UC22.barImage (L ⊔ K) L with hf₁
  set f₂ : Subgroup (Bar2 (L ⊔ K)) := UC22.barImage (L ⊔ K) K with hf₂
  have hsup : f₁ ⊔ f₂ = ⊤ := barImage_sup_eq_top_19 L K
  have hcomm12 : ∀ a ∈ f₁, ∀ b ∈ f₂, a * b = b * a :=
    uc22p22l_barImage_commute hLJ hKJ hne
  have hn₁ : f₁.Normal := by
    have h1 := hLnorm.map (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K)))
      (QuotientGroup.mk'_surjective _)
    simpa only [hf₁, UC22.barImage] using h1
  have hdisj : f₁ ⊓ f₂ = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have hw1 : w ∈ f₁ := (Subgroup.mem_inf.mp hw).1
    have hw2 : w ∈ f₂ := (Subgroup.mem_inf.mp hw).2
    have hcent : w ∈ Subgroup.center (Bar2 (L ⊔ K)) := by
      rw [Subgroup.mem_center_iff]
      intro r
      have hr : r ∈ f₁ ⊔ f₂ := by rw [hsup]; exact Subgroup.mem_top r
      obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hr
      calc a * b * w = a * (b * w) := by group
        _ = a * (w * b) := by rw [hcomm12 w hw1 b hb]
        _ = (a * w) * b := by group
        _ = (w * a) * b := by rw [hcomm12 a ha w hw2]
        _ = w * (a * b) := by group
    have h1 : w ∈ (⊥ : Subgroup (Bar2 (L ⊔ K))) := by
      rw [← center_bar2_sup_eq_bot_19 h]
      exact hcent
    simpa using h1
  have hcancel : ∀ {a₁ b₁ a₂ b₂ : Bar2 (L ⊔ K)}, a₁ ∈ f₁ → a₂ ∈ f₂ → b₁ ∈ f₁ → b₂ ∈ f₂ →
      a₁ * a₂ = b₁ * b₂ → a₁ = b₁ := by
    intro a₁ b₁ a₂ b₂ ha₁ ha₂ hb₁ hb₂ heq
    have hmem : b₁⁻¹ * a₁ ∈ f₁ ⊓ f₂ := by
      refine Subgroup.mem_inf.mpr ⟨f₁.mul_mem (f₁.inv_mem hb₁) ha₁, ?_⟩
      have h2 : b₁⁻¹ * a₁ = b₂ * a₂⁻¹ := by
        calc b₁⁻¹ * a₁ = b₁⁻¹ * (a₁ * a₂) * a₂⁻¹ := by group
          _ = b₁⁻¹ * (b₁ * b₂) * a₂⁻¹ := by rw [heq]
          _ = b₂ * a₂⁻¹ := by group
      rw [h2]
      exact f₂.mul_mem hb₂ (f₂.inv_mem ha₂)
    rw [hdisj] at hmem
    have h3 : b₁⁻¹ * a₁ = 1 := by simpa using hmem
    calc a₁ = b₁ * (b₁⁻¹ * a₁) := by group
      _ = b₁ * 1 := by rw [h3]
      _ = b₁ := mul_one b₁
  have hnormalCase : ∀ y : G, y ∈ E1.tauOf (L ⊔ K ⊔ D.T) (L ⊔ K ⊔ D.T)
      (Subgroup.zpowers s) →
      (∀ d ∈ (L ⊔ K) ⊓ E1.tauOf (L ⊔ K ⊔ D.T) (L ⊔ K ⊔ D.T) (Subgroup.zpowers s),
        ⁅y, d⁆ ∈ pCoreOf 2 (L ⊔ K ⊔ D.T)) →
      y ∈ normalizer (L : Set G) → y ∈ pCoreOf 2 (L ⊔ K ⊔ D.T) := by
    intro y hyH hyc hyL
    obtain ⟨hyH', hyQ, hys⟩ := E1.mem_tauOf.mp hyH
    have hyM : y ∈ D.M := hHM hyH'
    have hyN : y ∈ normalizer ((L ⊔ K : Subgroup G) : Set G) := hJN hyH'
    have hyK : y ∈ normalizer (K : Set G) := mem_normalizer_right_19 h hyM hyL hne
    have hyl : ∀ l ∈ L, ⁅y, l⁆ ∈ pCoreOf 2 (L ⊔ K) := by
      intro l hl
      have hlsK : s * l * s⁻¹ ∈ K := by
        have h1 := Subgroup.mem_map_of_mem (MulAut.conj s).toMonoidHom hl
        rw [hswap.1] at h1
        simpa [MulAut.conj_apply] using h1
      have hylL : y * l * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hyL l).mp hl
      have hylsK : y * (s * l * s⁻¹) * y⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp hyK (s * l * s⁻¹)).mp hlsK
      have hlJ : l ∈ L ⊔ K := Subgroup.mem_sup_left hl
      have hlsJ : s * l * s⁻¹ ∈ L ⊔ K := Subgroup.mem_sup_right hlsK
      have hylJ : y * l * y⁻¹ ∈ L ⊔ K := Subgroup.mem_sup_left hylL
      have hylsJ : y * (s * l * s⁻¹) * y⁻¹ ∈ L ⊔ K := Subgroup.mem_sup_right hylsK
      have hdJ : l * (s * l * s⁻¹) ∈ L ⊔ K := (L ⊔ K).mul_mem hlJ hlsJ
      have hds : ⁅l * (s * l * s⁻¹), s⁆ ∈ pCoreOf 2 (L ⊔ K) := by
        have h1 : ⁅l, s * l * s⁻¹⁆ ∈ pCoreOf 2 L ⊓ pCoreOf 2 K :=
          (Subgroup.commutator_le.mp (calC_commutator_le_of_ne hLc hKc hne))
            l hl (s * l * s⁻¹) hlsK
        rw [show ⁅l * (s * l * s⁻¹), s⁆ = ⁅l, s * l * s⁻¹⁆ from by
          simp only [commutatorElement_def, mul_inv_rev, hsi, mul_assoc, hss,
            mul_one]]
        exact hQL h1.1
      have hdτ : l * (s * l * s⁻¹) ∈
          E1.tauOf (L ⊔ K ⊔ D.T) (L ⊔ K ⊔ D.T) (Subgroup.zpowers s) := by
        refine E1.mem_tauOf.mpr ⟨Subgroup.mem_sup_left hdJ, hQN (Subgroup.mem_sup_left hdJ), ?_⟩
        intro a ha
        rw [Subgroup.mem_zpowers_iff_of_orderOf_eq_two hsord] at ha
        rcases ha with rfl | rfl
        · simp
        · exact hQJ hds
      have h1 : ⁅y, l * (s * l * s⁻¹)⁆ ∈ pCoreOf 2 (L ⊔ K) := by
        have h1' : ⁅y, l * (s * l * s⁻¹)⁆ ∈ pCoreOf 2 (L ⊔ K ⊔ D.T) :=
          hyc _ (Subgroup.mem_inf.mpr ⟨hdJ, hdτ⟩)
        have hJ : ⁅y, l * (s * l * s⁻¹)⁆ ∈ L ⊔ K :=
          (L ⊔ K).mul_mem
            ((Subgroup.mem_normalizer_iff.mp hyN (l * (s * l * s⁻¹))).mp hdJ)
            ((L ⊔ K).inv_mem hdJ)
        exact CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 le_sup_left
          (Subgroup.mem_inf.mpr ⟨hJ, h1'⟩)
      have hfac : ⁅y, l * (s * l * s⁻¹)⁆ = ⁅y, l⁆ * (l * ⁅y, s * l * s⁻¹⁆ * l⁻¹) := by
        rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
        group
      have h2 : ⁅y, l⁆ * (l * ⁅y, s * l * s⁻¹⁆ * l⁻¹) ∈ pCoreOf 2 (L ⊔ K) := hfac ▸ h1
      have hAL : ⁅y, l⁆ ∈ L := L.mul_mem hylL (L.inv_mem hl)
      have hAJ : ⁅y, l⁆ ∈ L ⊔ K := Subgroup.mem_sup_left hAL
      have hylsK' : ⁅y, s * l * s⁻¹⁆ ∈ K := K.mul_mem hylsK (K.inv_mem hlsK)
      have hBK : l * ⁅y, s * l * s⁻¹⁆ * l⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hLK hl) ⁅y, s * l * s⁻¹⁆).mp hylsK'
      have hBJ : l * ⁅y, s * l * s⁻¹⁆ * l⁻¹ ∈ L ⊔ K := Subgroup.mem_sup_right hBK
      have hmk : (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K))) ⟨⁅y, l⁆, hAJ⟩ *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K)))
            ⟨l * ⁅y, s * l * s⁻¹⁆ * l⁻¹, hBJ⟩ = 1 := by
        rw [← map_mul]
        refine (QuotientGroup.eq_one_iff _).mpr ((CFSG.mem_openPCoreOf_iff _).mp ?_)
        have hcoe : ((⟨⁅y, l⁆, hAJ⟩ *
            ⟨l * ⁅y, s * l * s⁻¹⁆ * l⁻¹, hBJ⟩ : ↥(L ⊔ K)) : G) =
            ⁅y, l⁆ * (l * ⁅y, s * l * s⁻¹⁆ * l⁻¹) := rfl
        rw [hcoe]
        exact h2
      have hmk₁ : (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K))) ⟨⁅y, l⁆, hAJ⟩ ∈ f₁ :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hAL)
      have hmk₂ : (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K)))
          ⟨l * ⁅y, s * l * s⁻¹⁆ * l⁻¹, hBJ⟩ ∈ f₂ :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hBK)
      have hzero : (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K))) ⟨⁅y, l⁆, hAJ⟩ = 1 :=
        hcancel hmk₁ hmk₂ f₁.one_mem f₂.one_mem (by rw [mul_one]; exact hmk)
      have hker : (⟨⁅y, l⁆, hAJ⟩ : ↥(L ⊔ K)) ∈ CFSG.pCore 2 ↥(L ⊔ K) := by
        simpa only [QuotientGroup.ker_mk'] using (MonoidHom.mem_ker.mpr hzero)
      exact (CFSG.mem_openPCoreOf_iff _).mpr hker
    have hyk : ∀ k ∈ K, ⁅y, k⁆ ∈ pCoreOf 2 (L ⊔ K) := by
      intro k hk
      have hksL : s * k * s⁻¹ ∈ L := by
        have h1 := Subgroup.mem_map_of_mem (MulAut.conj s).toMonoidHom hk
        rw [hswap.2] at h1
        simpa [MulAut.conj_apply] using h1
      have hyl' : ⁅y, s * k * s⁻¹⁆ ∈ pCoreOf 2 (L ⊔ K) := hyl _ hksL
      have hyksK : y * k * y⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hyK k).mp hk
      have hykJ : y * k * y⁻¹ ∈ L ⊔ K := Subgroup.mem_sup_right hyksK
      have hkJ : k ∈ L ⊔ K := Subgroup.mem_sup_right hk
      have hksJ : s * k * s⁻¹ ∈ L ⊔ K := Subgroup.mem_sup_left hksL
      have hdJ : (s * k * s⁻¹) * k ∈ L ⊔ K := (L ⊔ K).mul_mem hksJ hkJ
      have hds : ⁅(s * k * s⁻¹) * k, s⁆ ∈ pCoreOf 2 (L ⊔ K) := by
        have h1 : ⁅s * k * s⁻¹, k⁆ ∈ pCoreOf 2 L ⊓ pCoreOf 2 K :=
          (Subgroup.commutator_le.mp (calC_commutator_le_of_ne hLc hKc hne))
            (s * k * s⁻¹) hksL k hk
        rw [show ⁅(s * k * s⁻¹) * k, s⁆ = ⁅s * k * s⁻¹, k⁆ from by
          simp only [commutatorElement_def, mul_inv_rev, hsi, mul_assoc, hss,
            mul_one]]
        exact hQL h1.1
      have hdτ : (s * k * s⁻¹) * k ∈
          E1.tauOf (L ⊔ K ⊔ D.T) (L ⊔ K ⊔ D.T) (Subgroup.zpowers s) := by
        refine E1.mem_tauOf.mpr ⟨Subgroup.mem_sup_left hdJ, hQN (Subgroup.mem_sup_left hdJ), ?_⟩
        intro a ha
        rw [Subgroup.mem_zpowers_iff_of_orderOf_eq_two hsord] at ha
        rcases ha with rfl | rfl
        · simp
        · exact hQJ hds
      have h1 : ⁅y, (s * k * s⁻¹) * k⁆ ∈ pCoreOf 2 (L ⊔ K) := by
        have h1' : ⁅y, (s * k * s⁻¹) * k⁆ ∈ pCoreOf 2 (L ⊔ K ⊔ D.T) :=
          hyc _ (Subgroup.mem_inf.mpr ⟨hdJ, hdτ⟩)
        have hJ : ⁅y, (s * k * s⁻¹) * k⁆ ∈ L ⊔ K :=
          (L ⊔ K).mul_mem
            ((Subgroup.mem_normalizer_iff.mp hyN ((s * k * s⁻¹) * k)).mp hdJ)
            ((L ⊔ K).inv_mem hdJ)
        exact CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 le_sup_left
          (Subgroup.mem_inf.mpr ⟨hJ, h1'⟩)
      have hfac : ⁅y, (s * k * s⁻¹) * k⁆ =
          ⁅y, s * k * s⁻¹⁆ * ((s * k * s⁻¹) * ⁅y, k⁆ * (s * k * s⁻¹)⁻¹) := by
        rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
        group
      have h2 : ⁅y, s * k * s⁻¹⁆ * ((s * k * s⁻¹) * ⁅y, k⁆ * (s * k * s⁻¹)⁻¹) ∈
          pCoreOf 2 (L ⊔ K) := hfac ▸ h1
      have hyAL : y * (s * k * s⁻¹) * y⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp hyL (s * k * s⁻¹)).mp hksL
      have hAL : ⁅y, s * k * s⁻¹⁆ ∈ L := L.mul_mem hyAL (L.inv_mem hksL)
      have hAJ : ⁅y, s * k * s⁻¹⁆ ∈ L ⊔ K := Subgroup.mem_sup_left hAL
      have hykK' : ⁅y, k⁆ ∈ K := K.mul_mem hyksK (K.inv_mem hk)
      have hykJ : ⁅y, k⁆ ∈ L ⊔ K := Subgroup.mem_sup_right hykK'
      have hBK : (s * k * s⁻¹) * ⁅y, k⁆ * (s * k * s⁻¹)⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hLK hksL) ⁅y, k⁆).mp hykK'
      have hBJ : (s * k * s⁻¹) * ⁅y, k⁆ * (s * k * s⁻¹)⁻¹ ∈ L ⊔ K :=
        Subgroup.mem_sup_right hBK
      have hmk : (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K))) ⟨⁅y, s * k * s⁻¹⁆, hAJ⟩ *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K)))
            ⟨(s * k * s⁻¹) * ⁅y, k⁆ * (s * k * s⁻¹)⁻¹, hBJ⟩ = 1 := by
        rw [← map_mul]
        refine (QuotientGroup.eq_one_iff _).mpr ((CFSG.mem_openPCoreOf_iff _).mp ?_)
        have hcoe : ((⟨⁅y, s * k * s⁻¹⁆, hAJ⟩ *
            ⟨(s * k * s⁻¹) * ⁅y, k⁆ * (s * k * s⁻¹)⁻¹, hBJ⟩ : ↥(L ⊔ K)) : G) =
            ⁅y, s * k * s⁻¹⁆ * ((s * k * s⁻¹) * ⁅y, k⁆ * (s * k * s⁻¹)⁻¹) := rfl
        rw [hcoe]
        exact h2
      have hmkA : (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K))) ⟨⁅y, s * k * s⁻¹⁆, hAJ⟩ = 1 := by
        refine (QuotientGroup.eq_one_iff _).mpr ((CFSG.mem_openPCoreOf_iff _).mp ?_)
        have hcoe : ((⟨⁅y, s * k * s⁻¹⁆, hAJ⟩ : ↥(L ⊔ K)) : G) = ⁅y, s * k * s⁻¹⁆ := rfl
        rw [hcoe]
        exact hyl'
      have hmkB : (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K)))
          ⟨(s * k * s⁻¹) * ⁅y, k⁆ * (s * k * s⁻¹)⁻¹, hBJ⟩ = 1 := by
        rw [hmkA, one_mul] at hmk
        exact hmk
      have hzero : (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K))) ⟨⁅y, k⁆, hykJ⟩ = 1 := by
        have hB : (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K)))
            ⟨(s * k * s⁻¹) * ⁅y, k⁆ * (s * k * s⁻¹)⁻¹, hBJ⟩ =
            (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K))) ⟨s * k * s⁻¹, hksJ⟩ *
            (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K))) ⟨⁅y, k⁆, hykJ⟩ *
            ((QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K))) ⟨s * k * s⁻¹, hksJ⟩)⁻¹ := by
          have huv : (⟨(s * k * s⁻¹) * ⁅y, k⁆ * (s * k * s⁻¹)⁻¹, hBJ⟩ : ↥(L ⊔ K)) =
              (⟨s * k * s⁻¹, hksJ⟩ : ↥(L ⊔ K)) * ⟨⁅y, k⁆, hykJ⟩ *
                (⟨s * k * s⁻¹, hksJ⟩ : ↥(L ⊔ K))⁻¹ :=
            Subtype.ext (by simp)
          rw [huv, map_mul, map_mul, map_inv]
        rw [hB] at hmkB
        calc (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K))) ⟨⁅y, k⁆, hykJ⟩ =
            ((QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K))) ⟨s * k * s⁻¹, hksJ⟩)⁻¹ *
              ((QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K))) ⟨s * k * s⁻¹, hksJ⟩ *
                (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K))) ⟨⁅y, k⁆, hykJ⟩ *
                ((QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K))) ⟨s * k * s⁻¹, hksJ⟩)⁻¹) *
              (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K))) ⟨s * k * s⁻¹, hksJ⟩ := by group
          _ = ((QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K))) ⟨s * k * s⁻¹, hksJ⟩)⁻¹ * 1 *
              (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K))) ⟨s * k * s⁻¹, hksJ⟩ := by rw [hmkB]
          _ = 1 := by group
      have hker : (⟨⁅y, k⁆, hykJ⟩ : ↥(L ⊔ K)) ∈ CFSG.pCore 2 ↥(L ⊔ K) := by
        simpa only [QuotientGroup.ker_mk'] using (MonoidHom.mem_ker.mpr hzero)
      exact (CFSG.mem_openPCoreOf_iff _).mpr hker
    have hρ : UC6S846.rhoL (L ⊔ K) ⟨y, hyN⟩ = 1 := by
      apply MulEquiv.ext
      intro r
      obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(L ⊔ K)) r
      change UC6S846.rhoL (L ⊔ K) ⟨y, hyN⟩ (QuotientGroup.mk z) = QuotientGroup.mk z
      rw [UC6S846.rhoL_mk]
      have hzmem : z ∈ (L.subgroupOf (L ⊔ K)) ⊔ (K.subgroupOf (L ⊔ K)) := by
        rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
        exact Subgroup.mem_top z
      obtain ⟨z₁, hz₁, z₂, hz₂, hz⟩ := Subgroup.mem_sup_of_normal_left.mp hzmem
      have hz₁L : (z₁ : G) ∈ L := Subgroup.mem_subgroupOf.mp hz₁
      have hz₂K : (z₂ : G) ∈ K := Subgroup.mem_subgroupOf.mp hz₂
      have hm₁ : (QuotientGroup.mk (s := CFSG.pCore 2 ↥(L ⊔ K))
          (Subgroup.normalizerMonoidHom (L ⊔ K) ⟨y, hyN⟩ z₁)) =
          QuotientGroup.mk (s := CFSG.pCore 2 ↥(L ⊔ K)) z₁ := by
        refine (QuotientGroup.eq_iff_div_mem).mpr ?_
        refine (CFSG.mem_openPCoreOf_iff _).mp ?_
        have hcoe : (((Subgroup.normalizerMonoidHom (L ⊔ K) ⟨y, hyN⟩ z₁) / z₁ :
            ↥(L ⊔ K)) : G) = ⁅y, (z₁ : G)⁆ := by
          simp only [Subgroup.normalizerMonoidHom_apply_apply_coe,
            Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def,
            div_eq_mul_inv]
        rw [hcoe]
        exact hyl (z₁ : G) hz₁L
      have hm₂ : (QuotientGroup.mk (s := CFSG.pCore 2 ↥(L ⊔ K))
          (Subgroup.normalizerMonoidHom (L ⊔ K) ⟨y, hyN⟩ z₂)) =
          QuotientGroup.mk (s := CFSG.pCore 2 ↥(L ⊔ K)) z₂ := by
        refine (QuotientGroup.eq_iff_div_mem).mpr ?_
        refine (CFSG.mem_openPCoreOf_iff _).mp ?_
        have hcoe : (((Subgroup.normalizerMonoidHom (L ⊔ K) ⟨y, hyN⟩ z₂) / z₂ :
            ↥(L ⊔ K)) : G) = ⁅y, (z₂ : G)⁆ := by
          simp only [Subgroup.normalizerMonoidHom_apply_apply_coe,
            Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def,
            div_eq_mul_inv]
        rw [hcoe]
        exact hyk (z₂ : G) hz₂K
      rw [← hz, map_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, hm₁, hm₂]
    exact mem_pCoreOf_sup_of_conj_trivial_19 h hyH' hyN hρ
  by_cases hxL : x ∈ normalizer (L : Set G)
  · exact Subgroup.mem_sup_left (hnormalCase x hxH hxc hxL)
  · rcases hperm x hxM with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1) hxL
    · have hxNL : x * s ∈ normalizer (L : Set G) := by
        rw [Subgroup.mem_normalizer_iff_map_conj_eq]
        change L.map (MulAut.conj (x * s)).toMonoidHom = L
        have hcomp : (MulAut.conj (x * s)).toMonoidHom =
            ((MulAut.conj x).toMonoidHom).comp ((MulAut.conj s).toMonoidHom) := by
          ext a
          show (x * s) * a * (x * s)⁻¹ = x * (s * a * s⁻¹) * x⁻¹
          group
        rw [hcomp, ← Subgroup.map_map, hswap.1, h2]
      have hsH'' : s ∈ E1.tauOf (L ⊔ K ⊔ D.T) (L ⊔ K ⊔ D.T) (Subgroup.zpowers s) := by
        refine E1.mem_tauOf.mpr ⟨Subgroup.mem_sup_right hsT, hQN (Subgroup.mem_sup_right hsT), ?_⟩
        intro a ha
        rw [Subgroup.mem_zpowers_iff_of_orderOf_eq_two hsord] at ha
        rcases ha with h1 | h2
        · rw [h1]; simp
        · rw [h2]; simp
      have hxsH'' : x * s ∈ E1.tauOf (L ⊔ K ⊔ D.T) (L ⊔ K ⊔ D.T) (Subgroup.zpowers s) :=
        (E1.tauOf (L ⊔ K ⊔ D.T) (L ⊔ K ⊔ D.T) (Subgroup.zpowers s)).mul_mem hxH hsH''
      have hDinv : ∀ d ∈ (L ⊔ K) ⊓ E1.tauOf (L ⊔ K ⊔ D.T) (L ⊔ K ⊔ D.T)
          (Subgroup.zpowers s), s * d * s⁻¹ ∈ (L ⊔ K) ⊓ E1.tauOf (L ⊔ K ⊔ D.T)
            (L ⊔ K ⊔ D.T) (Subgroup.zpowers s) := by
        intro d hd
        obtain ⟨hdJ, hdτ⟩ := Subgroup.mem_inf.mp hd
        have hdH := E1.tauOf_le (L ⊔ K ⊔ D.T) (L ⊔ K ⊔ D.T) (Subgroup.zpowers s) hdτ
        have hsH : s ∈ L ⊔ K ⊔ D.T := Subgroup.mem_sup_right hsT
        have hsdH : s * d * s⁻¹ ∈ L ⊔ K ⊔ D.T :=
          (L ⊔ K ⊔ D.T).mul_mem ((L ⊔ K ⊔ D.T).mul_mem hsH hdH)
            ((L ⊔ K ⊔ D.T).inv_mem hsH)
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · exact (Subgroup.mem_normalizer_iff.mp hsN d).mp hdJ
        · refine E1.mem_tauOf.mpr ⟨hsdH, hQN hsdH, ?_⟩
          intro a ha
          rw [Subgroup.mem_zpowers_iff_of_orderOf_eq_two hsord] at ha
          rcases ha with h1 | h2
          · rw [h1]; simp
          · rw [h2]
            have hds : ⁅d, s⁆ ∈ pCoreOf 2 (L ⊔ K ⊔ D.T) :=
              (E1.mem_tauOf.mp hdτ).2.2 s (Subgroup.mem_zpowers s)
            have hconj : s * ⁅d, s⁆ * s⁻¹ = ⁅s * d * s⁻¹, s⁆ := by
              rw [conjugate_commutatorElement]
              congr 2
              group
            rw [← hconj]
            exact (Subgroup.mem_normalizer_iff.mp (hQN hsH) ⁅d, s⁆).mp hds
      have hxcs : ∀ d ∈ (L ⊔ K) ⊓ E1.tauOf (L ⊔ K ⊔ D.T) (L ⊔ K ⊔ D.T) (Subgroup.zpowers s),
          ⁅x * s, d⁆ ∈ pCoreOf 2 (L ⊔ K ⊔ D.T) := by
        intro d hd
        have h1 := hxc (s * d * s⁻¹) (hDinv d hd)
        have hsd : ⁅s, d⁆ ∈ pCoreOf 2 (L ⊔ K ⊔ D.T) := by
          have hds : ⁅d, s⁆ ∈ pCoreOf 2 (L ⊔ K ⊔ D.T) :=
            (E1.mem_tauOf.mp (Subgroup.mem_inf.mp hd).2).2.2 s (Subgroup.mem_zpowers s)
          rw [← commutatorElement_inv]
          exact Subgroup.inv_mem _ hds
        rw [show ⁅x * s, d⁆ = ⁅x, s * d * s⁻¹⁆ * ⁅s, d⁆ from by
          rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
          group]
        exact (pCoreOf 2 (L ⊔ K ⊔ D.T)).mul_mem h1 hsd
      have hyQ : x * s ∈ pCoreOf 2 (L ⊔ K ⊔ D.T) := hnormalCase (x * s) hxsH'' hxcs hxNL
      have hxeq : x = (x * s) * s := by rw [mul_assoc, hss, mul_one]
      rw [hxeq]
      exact Subgroup.mul_mem_sup hyQ (Subgroup.mem_zpowers s)

theorem five_dvd_barImage_19 {D : Data G} {V₀ V : Subgroup G}
    {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) :
    5 ∣ Nat.card ↥(UC22.barImage (L ⊔ K) L) := by
  have hLc : L ∈ calC D.M := h.hyp.hL.1
  have hKc : K ∈ calC D.M := h.hK
  have hne : L ≠ K := h.hne.symm
  have hLJ : L ∈ calC (L ⊔ K) := by
    refine ⟨?_, hLc.2.1, hLc.2.2⟩
    have hKL : K ≤ normalizer (L : Set G) := calC_le_normalizer_of_ne hLc hKc hne
    have hnorm : (L.subgroupOf (L ⊔ K)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
        (sup_le Subgroup.le_normalizer hKL)
    exact CFSG.Open.IsSubnormal.step le_sup_left hnorm (CFSG.Open.IsSubnormal.refl _)
  have hf₁ : Nat.card ↥(UC22.barImage (L ⊔ K) L) = Nat.card (Bar2 L) := by
    obtain ⟨e⟩ := s13_bar_equiv hLJ
    exact (Nat.card_congr e.toEquiv).symm
  rw [hf₁]
  exact prime_dvd_bar2 Nat.prime_five (by norm_num) (h.p_eq ▸ h.hyp.hL.2)

theorem diag_barImage_mulEquiv_19 {D : Data G} {V₀ V : Subgroup G}
    {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) {s : G} (hsT : s ∈ D.T)
    (hs2 : s ^ 2 = 1) (hsL : s ∉ normalizer (L : Set G))
    (hsN : s ∈ normalizer ((L ⊔ K : Subgroup G) : Set G)) :
    Nonempty (↥(UC22.barImage (L ⊔ K) L) ≃*
      ↥(UC22.barImage (L ⊔ K) ((L ⊔ K) ⊓ E1.tauOf (L ⊔ K ⊔ D.T) (L ⊔ K ⊔ D.T)
        (Subgroup.zpowers s)))) := by
  classical
  have hLc : L ∈ calC D.M := h.hyp.hL.1
  have hKc : K ∈ calC D.M := h.hK
  have hne : L ≠ K := h.hne.symm
  have hKL : K ≤ normalizer (L : Set G) := calC_le_normalizer_of_ne hLc hKc hne
  have hLK : L ≤ normalizer (K : Set G) := calC_le_normalizer_of_ne hKc hLc hne.symm
  have hLJ : L ∈ calC (L ⊔ K) := by
    refine ⟨?_, hLc.2.1, hLc.2.2⟩
    have hnorm : (L.subgroupOf (L ⊔ K)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
        (sup_le Subgroup.le_normalizer hKL)
    exact CFSG.Open.IsSubnormal.step le_sup_left hnorm (CFSG.Open.IsSubnormal.refl _)
  have hKJ : K ∈ calC (L ⊔ K) := by
    refine ⟨?_, hKc.2.1, hKc.2.2⟩
    have hnorm : (K.subgroupOf (L ⊔ K)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).2
        (sup_le hLK Subgroup.le_normalizer)
    exact CFSG.Open.IsSubnormal.step le_sup_right hnorm (CFSG.Open.IsSubnormal.refl _)
  have hLnorm : (L.subgroupOf (L ⊔ K)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
      (sup_le Subgroup.le_normalizer hKL)
  have hTJ : D.T ≤ normalizer ((L ⊔ K : Subgroup G) : Set G) := by
    rw [← h.hLK]
    exact D.sylowM.le.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
      (S17.Lp_le_M D 5)).mp (s13_Lp_normal D.M 5))
  have hJN : L ⊔ K ⊔ D.T ≤ normalizer ((L ⊔ K : Subgroup G) : Set G) :=
    sup_le le_normalizer hTJ
  have hQnormI : ((pCoreOf 2 (L ⊔ K ⊔ D.T)).subgroupOf (L ⊔ K ⊔ D.T)).Normal := by
    rw [CFSG.openPCoreOf_subgroupOf]
    exact CFSG.pCore_normal
  have hQN : L ⊔ K ⊔ D.T ≤ normalizer (pCoreOf 2 (L ⊔ K ⊔ D.T) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (CFSG.LieType.BorelTits.pCoreOf_le 2 _)).mp hQnormI
  have hQJQ : pCoreOf 2 (L ⊔ K) ≤ pCoreOf 2 (L ⊔ K ⊔ D.T) :=
    CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 le_sup_left
      (sup_le le_normalizer (by
        rw [← h.hLK]
        exact D.sylowM.le.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
          (S17.Lp_le_M D 5)).mp (s13_Lp_normal D.M 5))))
  set f₁ : Subgroup (Bar2 (L ⊔ K)) := UC22.barImage (L ⊔ K) L with hf₁
  set f₂ : Subgroup (Bar2 (L ⊔ K)) := UC22.barImage (L ⊔ K) K with hf₂
  have hsup : f₁ ⊔ f₂ = ⊤ := barImage_sup_eq_top_19 L K
  have hcomm12 : ∀ a ∈ f₁, ∀ b ∈ f₂, a * b = b * a :=
    uc22p22l_barImage_commute hLJ hKJ hne
  have hn₁ : f₁.Normal := by
    have h1 := hLnorm.map (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K)))
      (QuotientGroup.mk'_surjective _)
    simpa only [hf₁, UC22.barImage] using h1
  have hdisj : f₁ ⊓ f₂ = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have hw1 : w ∈ f₁ := (Subgroup.mem_inf.mp hw).1
    have hw2 : w ∈ f₂ := (Subgroup.mem_inf.mp hw).2
    have hcent : w ∈ Subgroup.center (Bar2 (L ⊔ K)) := by
      rw [Subgroup.mem_center_iff]
      intro r
      have hr : r ∈ f₁ ⊔ f₂ := by rw [hsup]; exact Subgroup.mem_top r
      obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hr
      calc a * b * w = a * (b * w) := by group
        _ = a * (w * b) := by rw [hcomm12 w hw1 b hb]
        _ = (a * w) * b := by group
        _ = (w * a) * b := by rw [hcomm12 a ha w hw2]
        _ = w * (a * b) := by group
    have h1 : w ∈ (⊥ : Subgroup (Bar2 (L ⊔ K))) := by
      rw [← center_bar2_sup_eq_bot_19 h]
      exact hcent
    simpa using h1
  have hcancel : ∀ {a₁ b₁ a₂ b₂ : Bar2 (L ⊔ K)}, a₁ ∈ f₁ → a₂ ∈ f₂ → b₁ ∈ f₁ → b₂ ∈ f₂ →
      a₁ * a₂ = b₁ * b₂ → a₁ = b₁ := by
    intro a₁ b₁ a₂ b₂ ha₁ ha₂ hb₁ hb₂ heq
    have hmem : b₁⁻¹ * a₁ ∈ f₁ ⊓ f₂ := by
      refine Subgroup.mem_inf.mpr ⟨f₁.mul_mem (f₁.inv_mem hb₁) ha₁, ?_⟩
      have h2 : b₁⁻¹ * a₁ = b₂ * a₂⁻¹ := by
        calc b₁⁻¹ * a₁ = b₁⁻¹ * (a₁ * a₂) * a₂⁻¹ := by group
          _ = b₁⁻¹ * (b₁ * b₂) * a₂⁻¹ := by rw [heq]
          _ = b₂ * a₂⁻¹ := by group
      rw [h2]
      exact f₂.mul_mem hb₂ (f₂.inv_mem ha₂)
    rw [hdisj] at hmem
    have h3 : b₁⁻¹ * a₁ = 1 := by simpa using hmem
    calc a₁ = b₁ * (b₁⁻¹ * a₁) := by group
      _ = b₁ * 1 := by rw [h3]
      _ = b₁ := mul_one b₁
  let σ : MulAut (Bar2 (L ⊔ K)) := UC6S846.rhoL (L ⊔ K) ⟨s, hsN⟩
  have hσ_mk : ∀ z : ↥(L ⊔ K), σ (QuotientGroup.mk z) =
      QuotientGroup.mk (Subgroup.normalizerMonoidHom (L ⊔ K) ⟨s, hsN⟩ z) :=
    fun z => UC6S846.rhoL_mk (L ⊔ K) ⟨s, hsN⟩ z
  have hσ_mk' : ∀ z : ↥(L ⊔ K), σ (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K)) z) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K))
        (Subgroup.normalizerMonoidHom (L ⊔ K) ⟨s, hsN⟩ z) := fun z => hσ_mk z
  have hσ_invol : ∀ r : Bar2 (L ⊔ K), σ (σ r) = r := by
    intro r
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(L ⊔ K)) r
    rw [hσ_mk', hσ_mk']
    refine congrArg (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K))) (Subtype.ext ?_)
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe]
    have hss : s * s = 1 := by simpa [pow_two] using hs2
    have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_left hss
    have hcancel' : ∀ x : G, s * (s * x) = x := fun x => by
      rw [← mul_assoc, hss, one_mul]
    simp only [hsi, mul_assoc, hcancel', hss, mul_one]
  have hσ_f₁ : ∀ a ∈ f₁, σ a ∈ f₂ := by
    intro a ha
    rw [hf₁, UC22.barImage] at ha
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp ha
    rw [hσ_mk']
    have hlsK : s * (l : G) * s⁻¹ ∈ K := by
      have h1 := Subgroup.mem_map_of_mem (MulAut.conj s).toMonoidHom
        (Subgroup.mem_subgroupOf.mp hl)
      have hswap1 : L.map (MulAut.conj s).toMonoidHom = K := by
        rcases permutesPair_of_ctx19_one h s (D.sylowM.le hsT) with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact absurd (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1) (by
            intro hcontra
            exact hsL hcontra)
        · exact h1
      rw [hswap1] at h1
      simpa [MulAut.conj_apply] using h1
    have hcoe : ((Subgroup.normalizerMonoidHom (L ⊔ K) ⟨s, hsN⟩ l : ↥(L ⊔ K)) : G) =
        s * (l : G) * s⁻¹ := Subgroup.normalizerMonoidHom_apply_apply_coe (L ⊔ K) ⟨s, hsN⟩ l
    rw [hf₂, UC22.barImage]
    refine Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ?_)
    rw [hcoe]
    exact hlsK
  have hσ_f₂ : ∀ b ∈ f₂, σ b ∈ f₁ := by
    intro b hb
    rw [hf₂, UC22.barImage] at hb
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hb
    rw [hσ_mk']
    have hksL : s * (k : G) * s⁻¹ ∈ L := by
      have hswap2 : K.map (MulAut.conj s).toMonoidHom = L := by
        rcases permutesPair_of_ctx19_one h s (D.sylowM.le hsT) with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact absurd (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1) (by
            intro hcontra
            exact hsL hcontra)
        · exact h2
      have h1 := Subgroup.mem_map_of_mem (MulAut.conj s).toMonoidHom
        (Subgroup.mem_subgroupOf.mp hk)
      rw [hswap2] at h1
      simpa [MulAut.conj_apply] using h1
    have hcoe : ((Subgroup.normalizerMonoidHom (L ⊔ K) ⟨s, hsN⟩ k : ↥(L ⊔ K)) : G) =
        s * (k : G) * s⁻¹ := Subgroup.normalizerMonoidHom_apply_apply_coe (L ⊔ K) ⟨s, hsN⟩ k
    rw [hf₁, UC22.barImage]
    refine Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ?_)
    rw [hcoe]
    exact hksL
  have hdl_mem : ∀ l ∈ L, (l * (s * l * s⁻¹)) ∈ (L ⊔ K) ⊓ E1.tauOf (L ⊔ K ⊔ D.T)
      (L ⊔ K ⊔ D.T) (Subgroup.zpowers s) := by
    intro l hl
    have hlsK : s * l * s⁻¹ ∈ K := by
      have hswap1 : L.map (MulAut.conj s).toMonoidHom = K := by
        rcases permutesPair_of_ctx19_one h s (D.sylowM.le hsT) with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact absurd (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1) (by
            intro hcontra
            exact hsL hcontra)
        · exact h1
      have h1 := Subgroup.mem_map_of_mem (MulAut.conj s).toMonoidHom hl
      rw [hswap1] at h1
      simpa [MulAut.conj_apply] using h1
    have hdJ : l * (s * l * s⁻¹) ∈ L ⊔ K :=
      (L ⊔ K).mul_mem (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right hlsK)
    have hss : s * s = 1 := by simpa [pow_two] using hs2
    have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_left hss
    have hds : ⁅l * (s * l * s⁻¹), s⁆ ∈ pCoreOf 2 (L ⊔ K) := by
      have h1 : ⁅l, s * l * s⁻¹⁆ ∈ pCoreOf 2 L ⊓ pCoreOf 2 K :=
        (Subgroup.commutator_le.mp (calC_commutator_le_of_ne hLc hKc hne))
          l hl (s * l * s⁻¹) hlsK
      have h2 : ⁅l, s * l * s⁻¹⁆ ∈ pCoreOf 2 (L ⊔ K) :=
        CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 le_sup_left
          (sup_le Subgroup.le_normalizer hKL) h1.1
      rw [show ⁅l * (s * l * s⁻¹), s⁆ = ⁅l, s * l * s⁻¹⁆ from by
        simp only [commutatorElement_def, mul_inv_rev, hsi, mul_assoc, hss,
          mul_one]]
      exact h2
    have hdτ : l * (s * l * s⁻¹) ∈ E1.tauOf (L ⊔ K ⊔ D.T) (L ⊔ K ⊔ D.T)
        (Subgroup.zpowers s) := by
      refine E1.mem_tauOf.mpr ⟨Subgroup.mem_sup_left hdJ,
        hQN (Subgroup.mem_sup_left hdJ), ?_⟩
      intro a ha
      rw [Subgroup.mem_zpowers_iff_of_orderOf_eq_two (by
        rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_iff_pow_eq_one.mpr hs2) with h1 | h1
        · exact absurd (orderOf_eq_one_iff.mp h1) (by
            intro h0; exact hsL (h0 ▸ Subgroup.one_mem _))
        · exact h1)] at ha
      rcases ha with h1 | h2
      · rw [h1]; simp
      · rw [h2]
        exact hQJQ hds
    exact Subgroup.mem_inf.mpr ⟨hdJ, hdτ⟩
  let δ : ↥f₁ →* Bar2 (L ⊔ K) :=
    { toFun := fun x => (x : Bar2 (L ⊔ K)) * σ (x : Bar2 (L ⊔ K))
      map_one' := by simp
      map_mul' := by
        intro x y
        show ((x * y : ↥f₁) : Bar2 (L ⊔ K)) * σ ((x * y : ↥f₁) : Bar2 (L ⊔ K)) =
          ((x : Bar2 (L ⊔ K)) * σ (x : Bar2 (L ⊔ K))) *
            ((y : Bar2 (L ⊔ K)) * σ (y : Bar2 (L ⊔ K)))
        rw [Subgroup.coe_mul, map_mul]
        have hcomm : (y : Bar2 (L ⊔ K)) * σ (x : Bar2 (L ⊔ K)) =
            σ (x : Bar2 (L ⊔ K)) * (y : Bar2 (L ⊔ K)) :=
          hcomm12 y y.2 (σ (x : Bar2 (L ⊔ K))) (hσ_f₁ x x.2)
        calc (x : Bar2 (L ⊔ K)) * (y : Bar2 (L ⊔ K)) *
              (σ (x : Bar2 (L ⊔ K)) * σ (y : Bar2 (L ⊔ K)))
            = (x : Bar2 (L ⊔ K)) * ((y : Bar2 (L ⊔ K)) *
                σ (x : Bar2 (L ⊔ K))) * σ (y : Bar2 (L ⊔ K)) := by group
          _ = (x : Bar2 (L ⊔ K)) * (σ (x : Bar2 (L ⊔ K)) *
                (y : Bar2 (L ⊔ K))) * σ (y : Bar2 (L ⊔ K)) := by rw [hcomm]
          _ = ((x : Bar2 (L ⊔ K)) * σ (x : Bar2 (L ⊔ K))) *
                ((y : Bar2 (L ⊔ K)) * σ (y : Bar2 (L ⊔ K))) := by group }
  have hδ_inj : Function.Injective δ := by
    intro x y hxy
    exact Subtype.ext (hcancel x.2 (hσ_f₁ x x.2) y.2 (hσ_f₁ y y.2) hxy)
  have hδ_range : δ.range = UC22.barImage (L ⊔ K) ((L ⊔ K) ⊓ E1.tauOf (L ⊔ K ⊔ D.T)
      (L ⊔ K ⊔ D.T) (Subgroup.zpowers s)) := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      have hx : (x : Bar2 (L ⊔ K)) ∈ UC22.barImage (L ⊔ K) L := hf₁ ▸ x.2
      rw [UC22.barImage] at hx
      obtain ⟨l, hl, hlx⟩ := Subgroup.mem_map.mp hx
      have hd := hdl_mem (l : G) (Subgroup.mem_subgroupOf.mp hl)
      have hdJ : (l : G) * (s * (l : G) * s⁻¹) ∈ L ⊔ K := (Subgroup.mem_inf.mp hd).1
      rw [UC22.barImage]
      refine Subgroup.mem_map.mpr ⟨⟨(l : G) * (s * (l : G) * s⁻¹), hdJ⟩, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mpr hd
      · show (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K)))
            ⟨(l : G) * (s * (l : G) * s⁻¹), hdJ⟩ = δ x
        have hmeml : (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K))) l ∈ f₁ := by
          rw [hf₁]; exact Subgroup.mem_map_of_mem _ hl
        have hxeq : x = ⟨(QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K))) l, hmeml⟩ :=
          Subtype.ext hlx.symm
        rw [hxeq]
        rw [show δ ⟨(QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K))) l, hmeml⟩ =
            ((QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K))) l) *
              σ ((QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K))) l) from rfl, hσ_mk' l, ← map_mul]
        apply congrArg (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ K)))
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.normalizerMonoidHom_apply_apply_coe]
    · intro r hr
      rw [UC22.barImage] at hr
      obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hr
      have hdD : (d : G) ∈ (L ⊔ K) ⊓ E1.tauOf (L ⊔ K ⊔ D.T) (L ⊔ K ⊔ D.T)
          (Subgroup.zpowers s) := Subgroup.mem_subgroupOf.mp hd
      obtain ⟨hdJ, hdτ⟩ := Subgroup.mem_inf.mp hdD
      have hds : ⁅(d : G), s⁆ ∈ pCoreOf 2 (L ⊔ K) := by
        have h1 : ⁅(d : G), s⁆ ∈ pCoreOf 2 (L ⊔ K ⊔ D.T) :=
          (E1.mem_tauOf.mp hdτ).2.2 s (Subgroup.mem_zpowers s)
        have h2 : ⁅(d : G), s⁆ ∈ L ⊔ K := by
          rw [show ⁅(d : G), s⁆ = (d : G) * (s * (d : G)⁻¹ * s⁻¹) from by
            rw [commutatorElement_def]; group]
          exact (L ⊔ K).mul_mem hdJ
            ((Subgroup.mem_normalizer_iff.mp hsN ((d : G)⁻¹)).mp ((L ⊔ K).inv_mem hdJ))
        exact CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 le_sup_left
          (Subgroup.mem_inf.mpr ⟨h2, h1⟩)
      have hfixd : σ (QuotientGroup.mk d) = QuotientGroup.mk d := by
        rw [hσ_mk]
        refine (QuotientGroup.eq_iff_div_mem).mpr ?_
        refine (CFSG.mem_openPCoreOf_iff _).mp ?_
        have hcoe : (((Subgroup.normalizerMonoidHom (L ⊔ K) ⟨s, hsN⟩ d) / d : ↥(L ⊔ K)) : G) =
            ⁅s, (d : G)⁆ := by
          simp only [commutatorElement_def, div_eq_mul_inv]
          rfl
        rw [hcoe, ← commutatorElement_inv]
        exact Subgroup.inv_mem _ hds
      have hr' : (QuotientGroup.mk d) ∈ f₁ ⊔ f₂ := by rw [hsup]; exact Subgroup.mem_top _
      obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp hr'
      have hσa : σ a ∈ f₂ := hσ_f₁ a ha
      have hσb : σ b ∈ f₁ := hσ_f₂ b hb
      have hfixab : σ (a * b) = a * b := by rw [← hab] at hfixd; exact hfixd
      have h2 : σ a * σ b = a * b := by rw [map_mul] at hfixab; exact hfixab
      have heq : a * b = σ b * σ a := by
        rw [← h2, hcomm12 (σ b) hσb (σ a) hσa]
      have ha' : a = σ b := hcancel ha hb hσb hσa heq
      have hb' : b = σ a := by rw [← hσ_invol b, ha']
      refine ⟨⟨a, ha⟩, ?_⟩
      show δ ⟨a, ha⟩ = QuotientGroup.mk d
      show (a : Bar2 (L ⊔ K)) * σ a = QuotientGroup.mk d
      rw [← hb', ← hab]
  let δ' : ↥f₁ →* ↥(UC22.barImage (L ⊔ K) ((L ⊔ K) ⊓ E1.tauOf (L ⊔ K ⊔ D.T)
      (L ⊔ K ⊔ D.T) (Subgroup.zpowers s))) :=
    { toFun := fun x => ⟨δ x, by rw [← hδ_range]; exact ⟨x, rfl⟩⟩
      map_one' := Subtype.ext (map_one δ)
      map_mul' := fun x y => Subtype.ext (map_mul δ x y) }
  refine ⟨MulEquiv.ofBijective δ' ⟨?_, ?_⟩⟩
  · intro x y hxy
    exact hδ_inj (Subtype.ext_iff.mp hxy)
  · intro z
    have hz : (z : Bar2 (L ⊔ K)) ∈ δ.range := by rw [hδ_range]; exact z.2
    obtain ⟨x, hx⟩ := hz
    exact ⟨x, Subtype.ext hx⟩

theorem five_dvd_of_normal_tau_19 {D : Data G}
    {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K)
    (hLn : ¬ (L.subgroupOf D.M).Normal) {s : G} (hsT : s ∈ D.T) (hs2 : s ^ 2 = 1)
    (hsL : s ∉ normalizer (L : Set G)) {N : Subgroup G}
    (hNH : N ≤ E1.tauOf (L ⊔ K ⊔ D.T) (L ⊔ K ⊔ D.T) (Subgroup.zpowers s))
    (hHN : E1.tauOf (L ⊔ K ⊔ D.T) (L ⊔ K ⊔ D.T) (Subgroup.zpowers s) ≤
      normalizer (N : Set G))
    (hNQ : ¬ N ≤ pCoreOf 2 (L ⊔ K ⊔ D.T) ⊔ Subgroup.zpowers s) : 5 ∣ Nat.card N := by
  classical
  let J : Subgroup G := L ⊔ K
  let H : Subgroup G := L ⊔ K ⊔ D.T
  let Q : Subgroup G := pCoreOf 2 H
  let H'' : Subgroup G := E1.tauOf H H (Subgroup.zpowers s)
  let D' : Subgroup G := J ⊓ H''
  have hH''H : H'' ≤ H := E1.tauOf_le H H _
  have hTJ : D.T ≤ normalizer (J : Set G) := by
    rw [show J = L ⊔ K from rfl, ← h.hLK]
    exact D.sylowM.le.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
      (S17.Lp_le_M D 5)).mp (s13_Lp_normal D.M 5))
  have hJN : H ≤ normalizer (J : Set G) := sup_le le_normalizer hTJ
  have hsN : s ∈ normalizer (J : Set G) := hJN (Subgroup.mem_sup_right hsT)
  let φ : ↥H'' →* MulAut (Bar2 J) :=
    (UC6S846.rhoL J).comp (Subgroup.inclusion (hH''H.trans hJN))
  have hNnorm : (N.subgroupOf H'').Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hHN
  have hker_le : φ.ker ≤ Q.subgroupOf H'' := by
    intro x hx
    refine Subgroup.mem_subgroupOf.mpr ?_
    have hxH : (x : G) ∈ H := hH''H x.2
    have hx1 : UC6S846.rhoL J ⟨(x : G), hJN hxH⟩ = 1 := hx
    exact mem_pCoreOf_sup_of_conj_trivial_19 h hxH (hJN hxH) hx1
  have hQ2 : IsPGroup 2 (Q.subgroupOf H'') :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).comap_subtype
  have hPhiD : ∀ (d : ↥H'') (hd : d ∈ D'.subgroupOf H''),
      φ d = MulAut.conj (QuotientGroup.mk (⟨(d : G),
        (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hd)).1⟩ : ↥J)) := by
    intro d hd
    exact UC6S846.rhoL_inner J (d : G) (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hd)).1
  have hconj_inj : Function.Injective (MulAut.conj : Bar2 J →* MulAut (Bar2 J)) :=
    CFSG.mulAutConj_injective_of_center_eq_bot (center_bar2_sup_eq_bot_19 h)
  have hDbar_eq : (D'.subgroupOf H'').map φ =
      (UC22.barImage J D').map (MulAut.conj : Bar2 J →* MulAut (Bar2 J)) := by
    ext x
    constructor
    · rintro ⟨d, hd, rfl⟩
      have hdD : (d : G) ∈ D' := Subgroup.mem_subgroupOf.mp hd
      refine Subgroup.mem_map.mpr ⟨QuotientGroup.mk ⟨(d : G), (Subgroup.mem_inf.mp hdD).1⟩,
        ?_, (hPhiD d hd).symm⟩
      rw [UC22.barImage]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hdD)
    · rintro ⟨r, hr, rfl⟩
      rw [UC22.barImage] at hr
      obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hr
      have hjD : (j : G) ∈ D' := Subgroup.mem_subgroupOf.mp hj
      refine Subgroup.mem_map.mpr ⟨⟨(j : G), (Subgroup.mem_inf.mp hjD).2⟩, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mpr hjD
      · simpa using hPhiD ⟨(j : G), (Subgroup.mem_inf.mp hjD).2⟩
          (Subgroup.mem_subgroupOf.mpr hjD)
  have hLJ : L ∈ calC J := by
    refine ⟨?_, h.hyp.hL.1.2.1, h.hyp.hL.1.2.2⟩
    have hKL : K ≤ normalizer (L : Set G) :=
      calC_le_normalizer_of_ne h.hyp.hL.1 h.hK h.hne.symm
    have hnorm : (L.subgroupOf J).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
        (sup_le Subgroup.le_normalizer hKL)
    exact CFSG.Open.IsSubnormal.step le_sup_left hnorm (CFSG.Open.IsSubnormal.refl _)
  have hLsimple : IsSimpleGroup (Bar2 L) := by
    rcases h.shape with h2 | h3
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h2
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h3
  have hfs₁ : IsSimpleGroup ↥(UC22.barImage J L) := isSimpleGroup_barImage_19 hLJ hLsimple
  obtain ⟨eδ⟩ := diag_barImage_mulEquiv_19 h hsT hs2 hsL hsN
  have hDbar_simple : IsSimpleGroup ↥((D'.subgroupOf H'').map φ) := by
    rw [hDbar_eq]
    exact MulEquiv.isSimpleGroup
      (eδ.trans (Subgroup.equivMapOfInjective (UC22.barImage J D')
        (MulAut.conj : Bar2 J →* MulAut (Bar2 J)) hconj_inj)).symm
  have h5Dbar : 5 ∣ Nat.card ↥((D'.subgroupOf H'').map φ) := by
    rw [hDbar_eq]
    have hcard2 : Nat.card ↥((UC22.barImage J D').map
        (MulAut.conj : Bar2 J →* MulAut (Bar2 J))) = Nat.card ↥(UC22.barImage J D') :=
      (Nat.card_congr (Subgroup.equivMapOfInjective (UC22.barImage J D')
        (MulAut.conj : Bar2 J →* MulAut (Bar2 J)) hconj_inj).toEquiv).symm
    rw [hcard2, show Nat.card ↥(UC22.barImage J D') = Nat.card ↥(UC22.barImage J L) from
      (Nat.card_congr eδ.toEquiv).symm]
    exact five_dvd_barImage_19 h
  have hcard := Subgroup.card_ker_mul_card_range (φ.domRestrict (N.subgroupOf H''))
  rw [MonoidHom.ker_domRestrict, MonoidHom.domRestrict_range] at hcard
  have hcardN : Nat.card ↥(N.subgroupOf H'') = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv
  have hker2 : IsPGroup 2 (φ.ker.subgroupOf (N.subgroupOf H'')) :=
    (hQ2.comap_subtype (K := N.subgroupOf H'')).to_le
      (Subgroup.subgroupOf_mono (N.subgroupOf H'') hker_le)
  have h5ker : ¬ 5 ∣ Nat.card ↥(φ.ker.subgroupOf (N.subgroupOf H'')) := by
    obtain ⟨m, hm⟩ := hker2.exists_card_eq
    rw [hm]
    intro h5
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_five h5) (by norm_num)
  have hDbar_inv : ∀ x ∈ D'.subgroupOf H'', ∀ y : ↥H'',
      φ y * φ x * (φ y)⁻¹ ∈ (D'.subgroupOf H'').map φ := by
    intro x hx y
    refine Subgroup.mem_map.mpr ⟨y * x * y⁻¹, ?_, ?_⟩
    · have hxG : (x : G) ∈ D' := Subgroup.mem_subgroupOf.mp hx
      have hxJ : (x : G) ∈ J := (Subgroup.mem_inf.mp hxG).1
      have hxH'' : (x : G) ∈ H'' := (Subgroup.mem_inf.mp hxG).2
      refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
      · exact (Subgroup.mem_normalizer_iff.mp (hJN (hH''H y.2)) (x : G)).mp hxJ
      · exact H''.mul_mem (H''.mul_mem y.2 hxH'') (H''.inv_mem y.2)
    · rw [map_mul, map_mul, map_inv]
  have hNbar_inv : ∀ x ∈ N.subgroupOf H'', ∀ y : ↥H'',
      φ y * φ x * (φ y)⁻¹ ∈ (N.subgroupOf H'').map φ := by
    intro x hx y
    exact Subgroup.mem_map.mpr ⟨y * x * y⁻¹, hNnorm.conj_mem x hx y, by
      rw [map_mul, map_mul, map_inv]⟩
  by_cases hle : (D'.subgroupOf H'').map φ ≤ (N.subgroupOf H'').map φ
  · have h5 : 5 ∣ Nat.card ↥((N.subgroupOf H'').map φ) :=
      h5Dbar.trans (Subgroup.card_dvd_of_le hle)
    have h5N : 5 ∣ Nat.card ↥(N.subgroupOf H'') := by
      rw [← hcard]
      exact dvd_mul_of_dvd_right h5 _
    rw [← hcardN]
    exact h5N
  ·
    have hbot : (D'.subgroupOf H'').map φ ⊓ (N.subgroupOf H'').map φ = ⊥ := by
      have hEsub : ((D'.subgroupOf H'').map φ ⊓ (N.subgroupOf H'').map φ).subgroupOf
          ((D'.subgroupOf H'').map φ) |>.Normal := by
        refine Subgroup.Normal.mk ?_
        intro z hz y
        have hzE : (z : MulAut (Bar2 J)) ∈
            (D'.subgroupOf H'').map φ ⊓ (N.subgroupOf H'').map φ :=
          Subgroup.mem_subgroupOf.mp hz
        obtain ⟨n, hn, hzn⟩ := Subgroup.mem_map.mp (Subgroup.mem_inf.mp hzE).2
        obtain ⟨y', hy', hy'eq⟩ := Subgroup.mem_map.mp y.2
        refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
        · exact ((D'.subgroupOf H'').map φ).mul_mem
            (((D'.subgroupOf H'').map φ).mul_mem y.2 (Subgroup.mem_inf.mp hzE).1)
            (((D'.subgroupOf H'').map φ).inv_mem y.2)
        · change (y : MulAut (Bar2 J)) * (z : MulAut (Bar2 J)) * (y : MulAut (Bar2 J))⁻¹ ∈
            (N.subgroupOf H'').map φ
          rw [show (z : MulAut (Bar2 J)) = φ n from hzn.symm,
            show (y : MulAut (Bar2 J)) = φ y' from hy'eq.symm]
          exact hNbar_inv n hn y'
      rcases Subgroup.Normal.eq_bot_or_eq_top (((D'.subgroupOf H'').map φ ⊓
        (N.subgroupOf H'').map φ).subgroupOf ((D'.subgroupOf H'').map φ)) with hb | ht
      · rw [eq_bot_iff]
        intro x hx
        have hxD : x ∈ (D'.subgroupOf H'').map φ := (Subgroup.mem_inf.mp hx).1
        have hx' : (⟨x, hxD⟩ : ↥((D'.subgroupOf H'').map φ)) ∈
            ((D'.subgroupOf H'').map φ ⊓ (N.subgroupOf H'').map φ).subgroupOf
              ((D'.subgroupOf H'').map φ) := Subgroup.mem_subgroupOf.mpr hx
        rw [hb] at hx'
        have hx1 : (⟨x, hxD⟩ : ↥((D'.subgroupOf H'').map φ)) = 1 :=
          Subgroup.mem_bot.mp hx'
        exact Subgroup.mem_bot.mpr (Subtype.ext_iff.mp hx1)
      · exfalso
        apply hle
        intro x hx
        have hx' : (⟨x, hx⟩ : ↥((D'.subgroupOf H'').map φ)) ∈
            ((D'.subgroupOf H'').map φ ⊓ (N.subgroupOf H'').map φ).subgroupOf
              ((D'.subgroupOf H'').map φ) := by
          rw [ht]
          exact Subgroup.mem_top _
        have hxE : x ∈ (D'.subgroupOf H'').map φ ⊓ (N.subgroupOf H'').map φ :=
          Subgroup.mem_subgroupOf.mp hx'
        exact (Subgroup.mem_inf.mp hxE).2
    have hcomm : ∀ n ∈ N, ∀ d ∈ (L ⊔ K) ⊓ H'', ⁅n, d⁆ ∈ Q := by
      intro n hn d hd
      have hnH'' : n ∈ H'' := hNH hn
      have hdH'' : d ∈ H'' := (Subgroup.mem_inf.mp hd).2
      have hds : ⟨d, hdH''⟩ ∈ D'.subgroupOf H'' := Subgroup.mem_subgroupOf.mpr hd
      have hns : ⟨n, hnH''⟩ ∈ N.subgroupOf H'' := Subgroup.mem_subgroupOf.mpr hn
      have hcommφ : φ ⟨d, hdH''⟩ * φ ⟨n, hnH''⟩ = φ ⟨n, hnH''⟩ * φ ⟨d, hdH''⟩ := by
        have h1 : φ ⟨d, hdH''⟩ * φ ⟨n, hnH''⟩ * (φ ⟨d, hdH''⟩)⁻¹ * (φ ⟨n, hnH''⟩)⁻¹ ∈
            (N.subgroupOf H'').map φ :=
          Subgroup.mul_mem _ (hNbar_inv ⟨n, hnH''⟩ hns ⟨d, hdH''⟩)
            (Subgroup.inv_mem _ (Subgroup.mem_map_of_mem _ hns))
        have h2 : φ ⟨d, hdH''⟩ * φ ⟨n, hnH''⟩ * (φ ⟨d, hdH''⟩)⁻¹ * (φ ⟨n, hnH''⟩)⁻¹ ∈
            (D'.subgroupOf H'').map φ := by
          have hinv : φ ⟨n, hnH''⟩ * (φ ⟨d, hdH''⟩)⁻¹ * (φ ⟨n, hnH''⟩)⁻¹ ∈
              (D'.subgroupOf H'').map φ := by
            have h := hDbar_inv ⟨(d : G)⁻¹, H''.inv_mem hdH''⟩
              ((D'.subgroupOf H'').inv_mem hds) ⟨n, hnH''⟩
            have h' : φ ⟨(d : G)⁻¹, H''.inv_mem hdH''⟩ = (φ ⟨d, hdH''⟩)⁻¹ := by
              rw [← map_inv]
              rfl
            rwa [h'] at h
          rw [show φ ⟨d, hdH''⟩ * φ ⟨n, hnH''⟩ * (φ ⟨d, hdH''⟩)⁻¹ * (φ ⟨n, hnH''⟩)⁻¹ =
              φ ⟨d, hdH''⟩ * (φ ⟨n, hnH''⟩ * (φ ⟨d, hdH''⟩)⁻¹ * (φ ⟨n, hnH''⟩)⁻¹) from by
            group]
          exact Subgroup.mul_mem _ (Subgroup.mem_map_of_mem _ hds) hinv
        have hmem : φ ⟨d, hdH''⟩ * (φ ⟨n, hnH''⟩ * (φ ⟨d, hdH''⟩)⁻¹ *
            (φ ⟨n, hnH''⟩)⁻¹) ∈ (D'.subgroupOf H'').map φ ⊓ (N.subgroupOf H'').map φ := by
          refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
          · rw [show φ ⟨d, hdH''⟩ * (φ ⟨n, hnH''⟩ * (φ ⟨d, hdH''⟩)⁻¹ * (φ ⟨n, hnH''⟩)⁻¹) =
              φ ⟨d, hdH''⟩ * φ ⟨n, hnH''⟩ * (φ ⟨d, hdH''⟩)⁻¹ * (φ ⟨n, hnH''⟩)⁻¹ from by group]
            exact h2
          · rw [show φ ⟨d, hdH''⟩ * (φ ⟨n, hnH''⟩ * (φ ⟨d, hdH''⟩)⁻¹ * (φ ⟨n, hnH''⟩)⁻¹) =
              φ ⟨d, hdH''⟩ * φ ⟨n, hnH''⟩ * (φ ⟨d, hdH''⟩)⁻¹ * (φ ⟨n, hnH''⟩)⁻¹ from by group]
            exact h1
        rw [hbot] at hmem
        have hone : φ ⟨d, hdH''⟩ * (φ ⟨n, hnH''⟩ * (φ ⟨d, hdH''⟩)⁻¹ *
            (φ ⟨n, hnH''⟩)⁻¹) = 1 := by simpa using hmem
        have h3 : ⁅φ ⟨d, hdH''⟩, φ ⟨n, hnH''⟩⁆ = 1 := by
          rw [commutatorElement_def]
          rw [show φ ⟨d, hdH''⟩ * φ ⟨n, hnH''⟩ * (φ ⟨d, hdH''⟩)⁻¹ * (φ ⟨n, hnH''⟩)⁻¹ =
              φ ⟨d, hdH''⟩ * (φ ⟨n, hnH''⟩ * (φ ⟨d, hdH''⟩)⁻¹ * (φ ⟨n, hnH''⟩)⁻¹) from by
            group]
          exact hone
        exact (commutatorElement_eq_one_iff_mul_comm.mp h3)
      have hmemH'' : ⁅n, d⁆ ∈ H'' := by
        rw [commutatorElement_def]
        exact H''.mul_mem (H''.mul_mem (H''.mul_mem hnH'' hdH'') (H''.inv_mem hnH''))
          (H''.inv_mem hdH'')
      have hφ1 : φ ⟨⁅n, d⁆, hmemH''⟩ = 1 := by
        have he : (⟨⁅n, d⁆, hmemH''⟩ : ↥H'') =
            ⟨n, hnH''⟩ * ⟨d, hdH''⟩ * ⟨n, hnH''⟩⁻¹ * ⟨d, hdH''⟩⁻¹ := by
          apply Subtype.ext
          simp [commutatorElement_def]
        have h3 : φ ⟨⁅n, d⁆, hmemH''⟩ = ⁅φ ⟨n, hnH''⟩, φ ⟨d, hdH''⟩⁆ := by
          rw [he]
          simp only [map_mul, map_inv, commutatorElement_def]
        rw [h3, commutatorElement_eq_one_iff_mul_comm]
        exact hcommφ.symm
      exact Subgroup.mem_subgroupOf.mp (hker_le hφ1)
    have hall : ∀ n ∈ N, n ∈ Q ⊔ Subgroup.zpowers s :=
      fun n hn => le_sup_of_centralizes_diag_19 h hsT hs2 hsL (hNH hn) (hcomm n hn)
    exact absurd (fun n hn => hall n hn) hNQ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
