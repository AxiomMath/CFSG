module

public import CFSG.Quasithin.Background.C48SporNat
public import CFSG.Quasithin.Background.C48PfA
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyOddClassical
public import CFSG.Quasithin.Background.C48SporPull

public section

namespace CFSG.Quasithin.C48Spor

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {H R M L V K : Subgroup G}

theorem M0R_le_normalizer_V (h : HypC28 H R M L V) :
    conjClosure L M ⊔ R ≤ Subgroup.normalizer (V : Set G) :=
  sup_le (M0_le_normalizer_V h) ((C48Pf.le_centralizer_V h).trans
    (Subgroup.centralizer_le_normalizer _))

@[expose] noncomputable def modO2EquivL (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K) :
    ModO2 (conjClosure L M) ≃* ModO2 (img (sporN H K) (conjClosure L M)) :=
  modO2Equiv (M0_le_sporX h h31) (isPGroup_ker_M0 h h31)

theorem mk_mem_inf_centralizer_iff (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K)
    (v : ↥V) :
    ((imgHom (N := sporN H K) (V_le_sporX h h31) v : ↥(img (sporN H K) V)) :
        ↥(sporX H K) ⧸ sporN H K) ∈
      img (sporN H K) V ⊓ Subgroup.centralizer
        (img (sporN H K) (conjClosure L M) : Set (↥(sporX H K) ⧸ sporN H K)) ↔
      (v : G) ∈ V ⊓ Subgroup.centralizer (conjClosure L M : Set G) := by
  rw [coe_imgHom, Subgroup.mem_inf, Subgroup.mem_inf,
    mk_mem_centralizer_iff h h31 (v := ⟨v, V_le_sporX h h31 v.2⟩) (V_le_K h h31 v.2)]
  exact ⟨fun hv => ⟨v.2, hv.2⟩, fun hv => ⟨mk_mem_img v.2, hv.2⟩⟩

theorem c48Case1_of_img (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K)
    (hL : L = conjClosure L M) {n : ℕ}
    (hn : IsPSL 2 2 n (ModO2 (img (sporN H K) (conjClosure L M))))
    (hmod : (∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
        IsNaturalSection (img (sporN H K) (conjClosure L M) ⊔ img (sporN H K) R)
          (img (sporN H K) V) (img (sporN H K) V ⊓ Subgroup.centralizer
            (img (sporN H K) (conjClosure L M) : Set (↥(sporX H K) ⧸ sporN H K)))
          ((img (sporN H K) R).subgroupOf
            (img (sporN H K) (conjClosure L M) ⊔ img (sporN H K) R)) (StatedSL 2 F)) ∨
      (n = 2 ∧ IsAltNaturalSection (img (sporN H K) (conjClosure L M) ⊔ img (sporN H K) R)
          (img (sporN H K) V) (img (sporN H K) V ⊓ Subgroup.centralizer
            (img (sporN H K) (conjClosure L M) : Set (↥(sporX H K) ⧸ sporN H K)))
          ((img (sporN H K) R).subgroupOf
            (img (sporN H K) (conjClosure L M) ⊔ img (sporN H K) R)) 5)) :
    C48Case1 H R M L V K := by
  have hL0 : L = conjClosure L M := hL
  have hA := M0R_le_sporX h h31
  have hV := V_le_sporX h h31
  rw [← img_sup (M0_le_sporX h h31) (R_le_sporX h h31)] at hmod
  refine ⟨n, ?_, ?_⟩
  · rw [hL0]
    exact Setup.Family.statedClassicalModel_of_mulEquiv (modO2EquivL h h31).symm hn
  · rcases hmod with ⟨F, hF, hFt, hcard, hnat⟩ | ⟨hn2, halt⟩
    · left
      refine ⟨F, hF, hFt, hcard, ?_⟩
      rw [hL0]
      exact isNaturalSection_of_img hA hV hnat (M0R_le_normalizer_V h) (comap_imgHom_R h h31)
        (mk_mem_inf_centralizer_iff h h31)
    · right; left
      refine ⟨hn2, ?_⟩
      rw [hL0]
      exact isAltNaturalSection_of_img hA hV halt (M0R_le_normalizer_V h) (comap_imgHom_R h h31)
        (mk_mem_inf_centralizer_iff h h31)

theorem mk_mem_bot_iff (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K)
    (hVK : V ⊓ Subgroup.centralizer (K : Set G) = ⊥) (v : ↥V) :
    ((imgHom (N := sporN H K) (V_le_sporX h h31) v : ↥(img (sporN H K) V)) :
        ↥(sporX H K) ⧸ sporN H K) ∈ (⊥ : Subgroup (↥(sporX H K) ⧸ sporN H K)) ↔
      (v : G) ∈ (⊥ : Subgroup G) := by
  rw [coe_imgHom, Subgroup.mem_bot, Subgroup.mem_bot, QuotientGroup.eq_one_iff, mem_sporN]
  constructor
  · intro hv
    have : (v : G) ∈ V ⊓ Subgroup.centralizer (K : Set G) := ⟨v.2, hv⟩
    rwa [hVK, Subgroup.mem_bot] at this
  · intro hv
    rw [hv]
    exact Subgroup.one_mem _

theorem c48Case2_of_img (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K)
    (hL : L = conjClosure L M)
    (hVK : V ⊓ Subgroup.centralizer (K : Set G) = ⊥)
    (h2 : C48Case2 ⊤ (img (sporN H K) R) (img (sporN H K) M)
      (img (sporN H K) (conjClosure L M)) (img (sporN H K) V) (img (sporN H K) K)) :
    C48Case2 H R M L V K := by
  have hL0 : L = conjClosure L M := hL
  have hA := M0R_le_sporX h h31
  have hV := V_le_sporX h h31
  obtain ⟨m, hm, hpsl, hmod⟩ := h2
  rw [← img_sup (M0_le_sporX h h31) (R_le_sporX h h31)] at hmod
  refine ⟨m, hm, ?_, ?_⟩
  · rw [hL0]
    exact Setup.Family.statedClassicalModel_of_mulEquiv (modO2EquivL h h31).symm hpsl
  · rcases hmod with ⟨k, hk, hs⟩ | ⟨hm4, halt⟩
    · left
      refine ⟨k, hk, ?_⟩
      rw [hL0]
      exact isSumOfNaturalModules_of_img hA hV hs (M0R_le_normalizer_V h) bot_le
        (comap_imgHom_R h h31) (mk_mem_bot_iff h h31 hVK)
    · right
      refine ⟨hm4, ?_⟩
      rw [hL0]
      exact isAltNaturalSection_of_img hA hV halt (M0R_le_normalizer_V h) (comap_imgHom_R h h31)
        (mk_mem_bot_iff h h31 hVK)

theorem sum_img (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K) (hL : L = conjClosure L M)
    {m k : ℕ} (hm : 2 ≤ m)
    (hs : IsSumOfNaturalModules (L ⊔ R) V ⊥ (R.subgroupOf (L ⊔ R)) (StatedSL m (ZMod 2))
      false k) :
    V ⊓ Subgroup.centralizer (K : Set G) = ⊥ ∧
      IsSumOfNaturalModules (img (sporN H K) (conjClosure L M) ⊔ img (sporN H K) R)
        (img (sporN H K) V) ⊥ ((img (sporN H K) R).subgroupOf
          (img (sporN H K) (conjClosure L M) ⊔ img (sporN H K) R)) (StatedSL m (ZMod 2))
        false k := by
  have hL0 : L = conjClosure L M := hL
  rw [hL0] at hs
  have hA := M0R_le_sporX h h31
  have hV := V_le_sporX h h31
  have hRL : R ≤ Subgroup.normalizer (conjClosure L M : Set G) :=
    h.le_M.trans (le_normalizer_conjClosure L M)
  have hcent := inf_centralizer_eq_bot_of_sum hm hRL hs
  have hVK : V ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
    rw [eq_bot_iff, ← hcent]
    exact inf_le_inf_left _ (Subgroup.centralizer_le h31.1)
  refine ⟨hVK, ?_⟩
  have hker : (imgHom (N := sporN H K) hA).ker ≤ R.subgroupOf (conjClosure L M ⊔ R) := by
    intro y hy
    rw [mem_ker_imgHom_iff] at hy
    exact mem_R_of_centralizer h h31 y.2 hy
  have hinj : Function.Injective (imgHom (N := sporN H K) hV) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro v hv
    rw [mem_ker_imgHom_iff] at hv
    have : (v : G) ∈ V ⊓ Subgroup.centralizer (K : Set G) := ⟨v.2, hv⟩
    rw [hVK, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).2 (Subtype.ext this)
  have := isSumOfNaturalModules_img hA hV hs hker hinj
  rwa [map_subgroupOf_imgHom hA le_sup_right, img_sup (M0_le_sporX h h31) (R_le_sporX h h31)]
    at this

end CFSG.Quasithin.C48Spor
