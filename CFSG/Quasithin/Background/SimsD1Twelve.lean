module

public import CFSG.Quasithin.Vol2.Ch3yB69
public import CFSG.Quasithin.Background.SimsD1Bridge

public section

namespace CFSG.Quasithin.SimsD1.Twelve

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {G₁ G₂ T V M₂ : Subgroup G}

omit [Finite G] in
theorem exists_mul_pow_eq {N : Subgroup G} {n s : G} (hn : n ∈ N)
    (hs : s ∈ Subgroup.normalizer (N : Set G)) (k : ℕ) :
    ∃ n' ∈ N, (n * s) ^ k = n' * s ^ k := by
  induction k with
  | zero => exact ⟨1, N.one_mem, by simp⟩
  | succ k ih =>
    obtain ⟨n', hn', h⟩ := ih
    have hsk : s ^ k ∈ Subgroup.normalizer (N : Set G) := Subgroup.pow_mem _ hs k
    have h1 : s ^ k * n * (s ^ k)⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp hsk n).mp hn
    refine ⟨n' * (s ^ k * n * (s ^ k)⁻¹), N.mul_mem hn' h1, ?_⟩
    rw [pow_succ, h]
    group

theorem isTwoReducedIn_of_minParabolic {H S M W : Subgroup G} (hmp : MinParabolic H S M)
    (hWH : W ≤ H) (hWE : IsElemAbelian 2 W) (hHW : H ≤ Subgroup.normalizer (W : Set G))
    (hQW : pCoreOf 2 H ≤ Subgroup.centralizer (W : Set G))
    (hCM : H ⊓ Subgroup.centralizer (W : Set G) ≤ M) : IsTwoReducedIn H W := by
  refine ⟨hWH, hHW, hWE, fun D hDH hDn hD2 => ?_⟩
  set C : Subgroup G := H ⊓ Subgroup.centralizer (W : Set G)
  have hCn : H ≤ Subgroup.normalizer (C : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hg, B6.le_normalizer_centralizer hHW hg⟩
  have hQC : pCoreOf 2 H ≤ C := le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 H) hQW
  have hDCH : D ⊔ C ≤ H := sup_le hDH inf_le_left
  have hDCn : H ≤ Subgroup.normalizer ((D ⊔ C : Subgroup G) : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_sup D C ⟨hDn hg, hCn hg⟩
  have hDC2 : ∀ x ∈ D ⊔ C, ∃ k : ℕ, x ^ 2 ^ k ∈ C := by
    intro x hx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right D C
      (fun d hd => hCn (hDH hd))] at hx
    obtain ⟨d, hd, c, hc, rfl⟩ := Set.mem_mul.mp hx
    obtain ⟨m, hm⟩ := hD2 d hd
    have hdC : d ^ 2 ^ m ∈ C := ⟨H.pow_mem (hDH hd) _, hm⟩
    have hc1 : d * c * d⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.mp (hCn (hDH hd)) c).mp hc
    obtain ⟨n', hn', hpow⟩ := exists_mul_pow_eq hc1 (hCn (hDH hd)) (2 ^ m)
    refine ⟨m, ?_⟩
    have e : d * c = (d * c * d⁻¹) * d := by group
    rw [e, hpow]
    exact C.mul_mem hn' hdC
  have hle : D ⊔ C ≤ C :=
    hmp.le_of_isTwoQuotient_of_pCoreOf_le hCn hQC hCM le_sup_right hDCH hDCn hDC2
  exact (le_sup_left.trans hle).trans inf_le_right

theorem one_le_qInt_of_b69One (hB : B69One) {H S M W : Subgroup G} (hmp : MinParabolic H S M)
    (hsq : IsSQTKSub H) (hred : IsTwoReducedIn H W) (hWE : IsElemAbelian 2 W)
    (hCM : H ⊓ Subgroup.centralizer (W : Set G) ≤ M) : (1 : WithTop ℚ) ≤ qInt H W hWE := by
  have hHW : H ≤ Subgroup.normalizer (W : Set G) := hred.2.1
  set X : Subgroup (MulAut ↥W) := autOn H W
  let φ : ↥H →* ↥X := ((conjAct W).comp (Subgroup.inclusion hHW)).codRestrict X
    fun g => AutOn.conjAct_mem_autOn (Subgroup.inclusion hHW g) g.2
  have hφ1 : ∀ g : ↥H, φ g = 1 ↔ (g : G) ∈ Subgroup.centralizer (W : Set G) := fun g =>
    Subtype.ext_iff.trans (AutOn.conjAct_eq_one_iff (Subgroup.inclusion hHW g))
  have hφsurj : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨n, hnH, rfl⟩ := AutOn.mem_autOn_iff.mp hx
    exact ⟨⟨n, hnH⟩, rfl⟩
  have hker : φ.ker ≤ M.subgroupOf H := fun g hg =>
    Subgroup.mem_subgroupOf.mpr (hCM ⟨g.2, (hφ1 g).mp (MonoidHom.mem_ker.mp hg)⟩)
  have hmpX := MinParabolic.map_of_surjective hmp.subgroupOf hφsurj hker
  have hO2 : pCoreOf 2 (⊤ : Subgroup ↥X) = ⊥ := by
    set Q : Subgroup ↥X := pCoreOf 2 (⊤ : Subgroup ↥X)
    have hQn : Q.Normal := Subgroup.normalizer_eq_top_iff.mp
      (top_le_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (⊤ : Subgroup ↥X)))
    have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (⊤ : Subgroup ↥X)
    have hDn : H ≤ Subgroup.normalizer (((Q.comap φ).map H.subtype : Subgroup G) : Set G) :=
      fun g hg => Subgroup.le_normalizer_map H.subtype ⟨⟨g, hg⟩, by
        rw [Subgroup.normalizer_eq_top_iff.mpr (hQn.comap φ)]
        exact Subgroup.mem_top _, rfl⟩
    have hDC : (Q.comap φ).map H.subtype ≤ Subgroup.centralizer (W : Set G) := by
      refine hred.2.2.2 _ (Subgroup.map_subtype_le _) hDn ?_
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨k, hk⟩ := hQ2 ⟨φ y, hy⟩
      refine ⟨k, ?_⟩
      have h1 : φ (y ^ 2 ^ k) = 1 := by
        rw [map_pow]
        exact congrArg Subtype.val hk
      exact (hφ1 _).mp h1
    refine eq_bot_iff.mpr fun q hq => ?_
    obtain ⟨y, rfl⟩ := hφsurj q
    exact Subgroup.mem_bot.mpr ((hφ1 y).mpr (hDC ⟨y, hq, rfl⟩))
  let _ : CommGroup ↥W := commGroupOfElemAbelian hWE
  have hsq' : ∀ v : ↥W, v ^ 2 = 1 := fun v => Subtype.ext (hWE.2 v v.2)
  have hnot : ¬ IsStrongFFModule X :=
    hB ↥W hsq' X _ _ ⟨↥H, inferInstance, inferInstance, hsq.2, hsq.1, φ, hφsurj⟩ hmpX hO2
  have key : ((1 : ℚ) : WithTop ℚ) ≤ kq X 2 := le_kq_iff.mpr fun A hA _ => by
    by_contra hlt
    exact hnot ((isStrongFFModule_iff hsq').mpr ⟨A, hA, not_le.mp hlt⟩)
  rw [WithTop.coe_one] at key
  exact key

theorem d12_finite (hB : B69One) (h : D11Hyp G₁ G₂ T V M₂)
    (hnff : ¬ IsFFInt G₁ V h.reduced.2.2.1) :
    (V ≤ pCoreOf 2 G₂ → IsElemAbelian 2 (conjClosure V G₂)) ∧
    (thompsonJ T = thompsonJ (pCoreOf 2 G₁) ∧
      thompsonJ (pCoreOf 2 G₁) = thompsonJ (pCoreOf 2 G₁ ⊔ pCoreOf 2 G₂)) ∧
    (¬ G₂ ≤ Subgroup.normalizer (T : Set G) ∧ ¬ thompsonJ (pCoreOf 2 G₁) ≤ pCoreOf 2 G₂) ∧
    IsMinParabolicOf G₂ G₂ ∧
    (∀ W : Subgroup G, W ≤ G₂ → ∀ hWE : IsElemAbelian 2 W,
      G₂ ≤ Subgroup.normalizer (W : Set G) → W ≤ pCoreOf 2 G₂ →
      pCoreOf 2 G₂ ≤ Subgroup.centralizer (W : Set G) →
      G₂ ⊓ Subgroup.centralizer (W : Set G) ≤ M₂ →
      IsTwoReducedIn G₂ W ∧
        (CFSG.SectionRank.IsSQTKCat ↥G₂ → (1 : WithTop ℚ) ≤ qInt G₂ W hWE)) := by
  have hmp : MinParabolic G₂ T M₂ := h.minParabolic hnff
  have hR₂T : pCoreOf 2 G₂ ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf h.sylow₂
  have hJ : thompsonJ (pCoreOf 2 G₁ ⊔ pCoreOf 2 G₂) = thompsonJ T :=
    B6.thompsonJ_eq_of_le ((h.thompsonJ_le hnff).trans le_sup_left)
      (sup_le h.pCoreOf_le_T hR₂T)
  refine ⟨fun hVR₂ => D15Proof.isElemAbelian_conjClosure h hnff hVR₂,
    ⟨h.thompsonJ_eq hnff, (h.thompsonJ_eq hnff).symm.trans hJ.symm⟩,
    ⟨hmp.not_normal, h.not_thompsonJ_le_pCoreOf hnff⟩, (minParabolic_iff.mp hmp).1, ?_⟩
  intro W hWG hWE hG₂W _ hRC hCM
  have hred : IsTwoReducedIn G₂ W := isTwoReducedIn_of_minParabolic hmp hWG hWE hG₂W hRC hCM
  exact ⟨hred, fun hcat =>
    one_le_qInt_of_b69One hB hmp (isSQTKSub_of_isSQTKCat hcat) hred hWE hCM⟩

end CFSG.Quasithin.SimsD1.Twelve
