module

public import CFSG.Quasithin.Background.SmithC27AltK1Split
public import CFSG.Quasithin.Background.SmithC27K1Core
public import CFSG.Quasithin.Background.SmithC27AltSetup
public import CFSG.Quasithin.Background.SmithC27B51
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Block
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv Equiv.Perm C124 C124.YZ
open scoped Pointwise

section PermFacts

theorem eq_one_or_eq_swap_of_mem_swapGroupOf {Ω : Type*} [DecidableEq Ω] {a b : Ω} (hab : a ≠ b)
    (hz : swap a b * swap a b = 1) {g : Perm Ω} (hg : g ∈ swapGroupOf (swap a b) hz) :
    g = 1 ∨ g = swap a b := by
  have hg' : ∀ x, g x = x ∨ g x = swap a b x := mem_swapGroupOf.1 hg
  have hfix : ∀ x, x ≠ a → x ≠ b → g x = x := fun x hxa hxb => by
    rcases hg' x with h | h
    · exact h
    · rwa [swap_apply_of_ne_of_ne hxa hxb] at h
  rcases hg' a with ha | ha
  · left
    have hb : g b = b := by
      rcases hg' b with h | h
      · exact h
      · rw [swap_apply_right] at h
        exact absurd (g.injective (h.trans ha.symm)) (Ne.symm hab)
    ext x
    by_cases hxa : x = a
    · rw [hxa, ha, one_apply]
    by_cases hxb : x = b
    · rw [hxb, hb, one_apply]
    rw [hfix x hxa hxb, one_apply]
  · right
    rw [swap_apply_left] at ha
    have hb : g b = a := by
      rcases hg' b with h | h
      · exact absurd (g.injective (ha.trans h.symm)) hab
      · rwa [swap_apply_right] at h
    ext x
    by_cases hxa : x = a
    · rw [hxa, ha, swap_apply_left]
    by_cases hxb : x = b
    · rw [hxb, hb, swap_apply_right]
    rw [hfix x hxa hxb, swap_apply_of_ne_of_ne hxa hxb]

theorem exists_perm_of_ker_eq {Γ : Type*} [Group Γ] {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6)
    {α β : Γ →* alternatingGroup (Fin n)} (hα : Function.Surjective α)
    (hβ : Function.Surjective β) (hker : α.ker = β.ker) :
    ∃ π : Perm (Fin n), ∀ x, (α x : Perm (Fin n)) = π * (β x : Perm (Fin n)) * π⁻¹ := by
  let eα := QuotientGroup.quotientKerEquivOfSurjective α hα
  let eβ := QuotientGroup.quotientKerEquivOfSurjective β hβ
  let ψ : alternatingGroup (Fin n) ≃* alternatingGroup (Fin n) :=
    eβ.symm.trans ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans eα)
  have hψ : ∀ x, ψ (β x) = α x := by
    intro x
    have h1 : eβ.symm (β x) = QuotientGroup.mk x := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show eα ((QuotientGroup.quotientMulEquivOfEq hker.symm) (eβ.symm (β x))) = α x
    rw [h1]
    rfl
  obtain ⟨π, hπ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn
    hn6).2 ψ
  refine ⟨π, fun x => ?_⟩
  rw [← hψ x, ← hπ, MulAut.conjNormal_apply]

end PermFacts

section K1

variable {G : Type} [Group G] [Finite G] {H R M K : Subgroup G} {n k : ℕ} [NeZero n]

namespace AltCtx

theorem isPGroup_Vc (R K : Subgroup G) : IsPGroup 2 (Vc R K) :=
  (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (K ⊔ R)).to_le (A4.omegaOneCenterOf_le _)

variable (C : AltCtx H R M K n k)
include C

theorem blockU_eq (hK : IsShort2 K) : blockU K = ⁅Vc R K, K⁆ :=
  le_antisymm (L246C127.blockU_le_commutator_of_ne_bot hK C.starHyp.K_le_normalizer_V
    (isPGroup_Vc R K) (commutator_V_K_le_blockU C.hyp C.starHyp) C.starHyp.commutator_ne_bot)
    (commutator_V_K_le_blockU C.hyp C.starHyp)

theorem blockU_le_Vc (hK : IsShort2 K) : blockU K ≤ Vc R K := by
  rw [C.blockU_eq hK]
  exact commutator_V_K_le_V C.starHyp

theorem exists_commVEquiv (hK : IsShort2 K) :
    ∃ e : ↥(commV (starOf R K K)) ≃* ↥(blockU K),
      ∀ u, ((e u : ↥(blockU K)) : G) = IntMod.val (u : Wc R K) := by
  let f : ↥(commV (starOf R K K)) →* ↥(blockU K) :=
    { toFun := fun u => ⟨IntMod.val (u : Wc R K), by
        rw [C.blockU_eq hK]
        exact val_mem_commutator_of_mem_commV _ u.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl }
  have hinj : Function.Injective f := fun u v h =>
    Subtype.ext (IntMod.val_injective (congrArg (fun w : ↥(blockU K) => (w : G)) h))
  have hsurj : Function.Surjective f := fun w => by
    have hw : (w : G) ∈ ⁅Vc R K, K⁆ := C.blockU_eq hK ▸ w.2
    obtain ⟨u, hu, huw⟩ := exists_mem_commV_of_mem_commutator _ C.starHyp.K_le_normalizer_V hw
    exact ⟨⟨u, hu⟩, Subtype.ext huw⟩
  exact ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩, fun _ => rfl⟩

theorem exists_theta (hK : IsShort2 K)
    (hfix : ∀ u ∈ commV (starOf R K K), u ∈ fixV (starOf R K K) → u = 1) :
    ∃ θ : ↥(blockU K) ≃* ↥(G6.coreMod n),
      ∀ (g : ↥(autOn (K ⊔ R) (Vc R K))) (u : ↥(blockU K))
        (hgu : (((g : MulAut ↥(Vc R K)) ⟨u, C.blockU_le_Vc hK u.2⟩ : ↥(Vc R K)) : G) ∈
          blockU K),
        θ ⟨_, hgu⟩ = G6.coreAct n (C.ι g) (θ u) := by
  obtain ⟨e, he⟩ := C.exists_commVEquiv hK
  have hβinj : Function.Injective C.β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (hfix _ u.2 (C.β_ker u hu))
  let βe := MulEquiv.ofBijective C.β ⟨hβinj, C.β_surj⟩
  refine ⟨e.symm.trans βe, fun g u hgu => ?_⟩
  let g' : ↥(starOf R K (K ⊔ R)) := g
  set u' := e.symm u with hu'
  have hu'val : IntMod.val (u' : Wc R K) = u := by
    rw [← he u', hu', MulEquiv.apply_symm_apply]
  have hu'eq : (u' : Wc R K) = (⟨(u : G), C.blockU_le_Vc hK u.2⟩ : ↥(Vc R K)) :=
    IntMod.val_injective hu'val
  have hgval : IntMod.val ((g' : MulAut (Wc R K)) (u' : Wc R K)) =
      (((g : MulAut ↥(Vc R K)) ⟨u, C.blockU_le_Vc hK u.2⟩ : ↥(Vc R K)) : G) := by
    rw [hu'eq]
    rfl
  have hgu' : (g' : MulAut (Wc R K)) (u' : Wc R K) ∈ commV (starOf R K K) := by
    have hw : (((g : MulAut ↥(Vc R K)) ⟨u, C.blockU_le_Vc hK u.2⟩ : ↥(Vc R K)) : G) ∈
        ⁅Vc R K, K⁆ := C.blockU_eq hK ▸ hgu
    obtain ⟨w, hw, hwv⟩ := exists_mem_commV_of_mem_commutator _ C.starHyp.K_le_normalizer_V hw
    have : w = (g' : MulAut (Wc R K)) (u' : Wc R K) :=
      IntMod.val_injective (hwv.trans hgval.symm)
    rwa [← this]
  have h1 : e.symm ⟨_, hgu⟩ = ⟨_, hgu'⟩ := by
    apply e.injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [he]
    exact hgval.symm
  show βe (e.symm ⟨_, hgu⟩) = G6.coreAct n (C.ι g') (βe u')
  rw [h1]
  exact C.β_equiv g' u' hgu'

theorem blockZ_eq_bot (hK : IsShort2 K)
    (hfix : ∀ u ∈ commV (starOf R K K), u ∈ fixV (starOf R K K) → u = 1) : blockZ K = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hzU, hzC⟩
  have hz : z ∈ ⁅Vc R K, K⁆ := C.blockU_eq hK ▸ hzU
  obtain ⟨u, hu, huz⟩ := exists_mem_commV_of_mem_commutator _ C.starHyp.K_le_normalizer_V hz
  have hfixu : u ∈ fixV (starOf R K K) :=
    (mem_fixV_autI_iff _ C.starHyp.K_le_normalizer_V).2 (huz ▸ hzC)
  rw [Subgroup.mem_bot, ← huz, hfix u hu hfixu]
  rfl

theorem exists_rho (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥) :
    ∃ ρ : ↥K →* alternatingGroup (Fin n), Function.Surjective ρ ∧ ρ.ker = CFSG.pCore 2 ↥K ∧
      ∀ l : ↥K, (ρ l : Perm (Fin n)) = C.φ ⟨l, Subgroup.mem_sup_left l.2⟩ := by
  have hmem : ∀ l : ↥K, (C.φ.comp (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ R))) l ∈
      alternatingGroup (Fin n) := fun l => by
    have h := C.φ_mem_bar le_sup_left l.2
    rwa [show C.bar K = alternatingGroup (Fin n) from C.K_map] at h
  let ρ : ↥K →* alternatingGroup (Fin n) :=
    (C.φ.comp (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ R))).codRestrict _ hmem
  refine ⟨ρ, fun σ => ?_, ?_, fun l => rfl⟩
  · obtain ⟨y, hy, hyσ⟩ := C.exists_lift σ.2
    exact ⟨⟨y, hy⟩, Subtype.ext hyσ⟩
  · have hKC := C.starHyp.inf_centralizer_eq hZ
    ext l
    rw [MonoidHom.mem_ker, mem_pCore_iff_mem_pCoreOf, ← hKC]
    constructor
    · intro hl
      have h1 : C.φ ⟨l, Subgroup.mem_sup_left l.2⟩ = 1 := congrArg Subtype.val hl
      have h2 : starHom C.X_le_N ⟨l, Subgroup.mem_sup_left l.2⟩ = 1 :=
        C.inj (h1.trans (map_one C.ι).symm)
      have h3 : convI (isElemAbelian_omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))
          ⟨(l : G), C.X_le_N (Subgroup.mem_sup_left l.2)⟩ = 1 := congrArg Subtype.val h2
      exact ⟨l.2, (convI_eq_one_iff _ _).1 h3⟩
    · intro hl
      apply Subtype.ext
      show C.ι (starHom C.X_le_N ⟨l, Subgroup.mem_sup_left l.2⟩) = 1
      have h3 : starHom C.X_le_N ⟨l, Subgroup.mem_sup_left l.2⟩ = 1 :=
        Subtype.ext ((convI_eq_one_iff _ _).2 hl.2)
      rw [h3, map_one]

end AltCtx

namespace AltCtx

theorem zero_ne_one' (C : AltCtx H R M K n k) : (0 : Fin n) ≠ 1 :=
  fin_zero_ne_one (by rcases C.n57 with h | h <;> omega)

theorem exists_tau (C : AltCtx H R M K n 1) :
    ∃ τ : ↥(starOf R K (K ⊔ R)), C.ι τ = swap 0 1 ∧
      starOf R K (thompsonJ R) = Subgroup.zpowers (τ : MulAut (Wc R K)) := by
  have hsw : swap (0 : Fin n) 1 ∈ Bmap C.ι (starOf R K (thompsonJ R)) := by
    rw [C.J_map]
    exact C.swap_mem_std
  obtain ⟨τ, hτJ, hτ⟩ := mem_Bmap.1 hsw
  refine ⟨τ, hτ, le_antisymm ?_ ((Subgroup.zpowers_le).2 hτJ)⟩
  intro g hg
  have hgX : g ∈ starOf R K (K ⊔ R) := star_le ((thompsonJ_le R).trans le_sup_right) hg
  have h1 : C.ι ⟨g, hgX⟩ ∈ swapGroupOf (swap (0 : Fin n) 1) C.inv_sq := by
    have h := (mem_Bmap_iff_of_injective C.inj ⟨g, hgX⟩).2 hg
    rwa [C.J_map] at h
  rcases eq_one_or_eq_swap_of_mem_swapGroupOf C.zero_ne_one' C.inv_sq h1 with h2 | h2
  · have h3 : (⟨g, hgX⟩ : ↥(starOf R K (K ⊔ R))) = 1 := C.inj (h2.trans (map_one _).symm)
    rw [show g = 1 from congrArg Subtype.val h3]
    exact Subgroup.one_mem _
  · have h3 : (⟨g, hgX⟩ : ↥(starOf R K (K ⊔ R))) = τ := C.inj (h2.trans hτ.symm)
    rw [show g = τ from congrArg Subtype.val h3]
    exact Subgroup.mem_zpowers _

theorem bar_MK_k1 (C : AltCtx H R M K n 1) :
    C.bar (M ⊓ K) = alternatingGroup (Fin n) ⊓ Subgroup.centralizer {swap (0 : Fin n) 1} := by
  have h01 := C.zero_ne_one'
  have hstar : kJ {swap (0 : Fin n) 1} ≤ C.bar (M ⊓ K) := by
    rw [kJ_swap_eq_centralizer h01]
    exact C.star_alt_centralizer
  have h5 : 5 ≤ Fintype.card (Fin n) := by
    rw [Fintype.card_fin]
    rcases C.n57 with h | h <;> omega
  rcases kJ_swap_overgroups h5 ⟨0, 1, h01, rfl⟩ hstar C.MK_le_alt with h | h
  · rw [h, kJ_swap_eq_centralizer h01]
  · exact absurd h C.MK_ne_alt

theorem MK_commute_tau (C : AltCtx H R M K n 1) {τ : ↥(starOf R K (K ⊔ R))}
    (hτ : C.ι τ = swap 0 1) :
    ∀ g ∈ starOf R K (M ⊓ K), g * (τ : MulAut (Wc R K)) = (τ : MulAut (Wc R K)) * g := by
  intro g hg
  have hgX : g ∈ starOf R K (K ⊔ R) := star_le MK_le hg
  have h1 : C.ι ⟨g, hgX⟩ ∈ C.bar (M ⊓ K) := (mem_Bmap_iff_of_injective C.inj _).2 hg
  rw [C.bar_MK_k1] at h1
  have h2 : C.ι ⟨g, hgX⟩ * swap 0 1 = swap 0 1 * C.ι ⟨g, hgX⟩ :=
    Subgroup.mem_centralizer_singleton_iff.1 h1.2
  rw [← hτ, ← map_mul, ← map_mul] at h2
  exact congrArg Subtype.val (C.inj h2)

theorem three_of_k1 (C : AltCtx H R M K n 1) (hK : IsShort2 K) (htype : IsAltType K n)
    (hfix : ∀ u ∈ commV (starOf R K K), u ∈ fixV (starOf R K K) → u = 1) :
    C27Three H R M K (Vc R K) := by
  classical
  have hodd : Odd n := by rcases C.n57 with h | h <;> subst h <;> decide
  have h5 : 5 ≤ n := by rcases C.n57 with h | h <;> omega
  have h8 : n ≤ 8 := by rcases C.n57 with h | h <;> omega
  have h6 : n ≠ 6 := by rcases C.n57 with h | h <;> omega
  obtain ⟨α, hα⟩ := (isAltType_iff_exists_isAltBlockTypeWith hodd).1 htype
  have hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ :=
    center_quot_eq_bot_of_surj C.n57 α hα.1 hα.2.1
  obtain ⟨ρ, hρs, hρk, hρφ⟩ := C.exists_rho hZ
  obtain ⟨θ, hθ⟩ := C.exists_theta hK hfix
  have hθK : ∀ (l : ↥K) (u v : ↥(blockU K)), (v : G) = l * u * l⁻¹ →
      θ v = G6.coreAct n (ρ l) (θ u) := by
    intro l u v huv
    set g : ↥(autOn (K ⊔ R) (Vc R K)) := starHom C.X_le_N ⟨l, Subgroup.mem_sup_left l.2⟩
      with hg
    have hgval : (((g : MulAut ↥(Vc R K)) ⟨u, C.blockU_le_Vc hK u.2⟩ : ↥(Vc R K)) : G) =
        v := by
      rw [huv]
      exact convI_apply_val (isElemAbelian_omegaOneCenterOf _)
        ⟨(l : G), C.X_le_N (Subgroup.mem_sup_left l.2)⟩ (⟨u, C.blockU_le_Vc hK u.2⟩ : ↥(Vc R K))
    have hgu : (((g : MulAut ↥(Vc R K)) ⟨u, C.blockU_le_Vc hK u.2⟩ : ↥(Vc R K)) : G) ∈
        blockU K := hgval ▸ v.2
    have h1 := hθ g u hgu
    rw [show (⟨_, hgu⟩ : ↥(blockU K)) = v from Subtype.ext hgval] at h1
    rw [h1, hρφ l]
    rfl
  have hQU' : ∀ q ∈ pCoreOf 2 (K ⊔ R), ∀ u ∈ blockU K, q * u = u * q := by
    intro q hq u hu
    have hqC := pCoreOf_le_centralizer_omegaOneCenterOf (K ⊔ R) hq
    exact (Subgroup.mem_centralizer_iff.1 hqC u (C.blockU_le_Vc hK hu)).symm
  have hker : ∀ l : ↥K, ρ l = 1 → (l : G) ∈ blockQ K := by
    intro l hl
    have hl' : l ∈ ρ.ker := hl
    rw [hρk] at hl'
    exact (mem_pCore_iff_mem_pCoreOf l).1 hl'
  have hQU := pCoreOf_le_blockU_sup C.n57 hK le_sup_left C.hyp.sup_le_normalizer
    (C.blockZ_eq_bot hK hfix) hQU' ρ hρs hker θ hθK
  have hUn : K ⊔ R ≤ Subgroup.normalizer (blockU K : Set G) := fun g hg =>
    C1.mem_normalizer_blockU (C.hyp.sup_le_normalizer hg)
  obtain ⟨τ, hτ, hJ⟩ := C.exists_tau
  have hMK := C.MK_commute_tau hτ
  have hιK : ∀ σ ∈ alternatingGroup (Fin n), ∃ g : ↥(autOn (K ⊔ R) (Vc R K)),
      (g : MulAut ↥(Vc R K)) ∈ autOn K (Vc R K) ∧ C.ι g = σ := by
    intro σ hσ
    rw [← C.K_map] at hσ
    exact mem_Bmap.1 hσ
  obtain ⟨t, htR, htV, htτ, hR, hord⟩ := exists_eq_zpowers_of_k1 C.hyp rfl
    C.starHyp.pCore_eq_inf (C.blockU_le_Vc hK) hUn hQU hodd C.ι C.inj hιK θ hθ τ
    C.zero_ne_one' hτ hJ hMK
  obtain ⟨π, hπ⟩ := exists_perm_of_ker_eq h5 h6 hα.1 hρs (hα.2.1.trans hρk.symm)
  have htX : t ∈ K ⊔ R := Subgroup.mem_sup_right htR
  have hφt : C.φ ⟨t, htX⟩ = swap 0 1 := by
    rw [← hτ]
    show C.ι (starHom C.X_le_N ⟨t, htX⟩) = C.ι τ
    congr 1
    apply Subtype.ext
    exact htτ
  have hσ : (π * swap 0 1 * π⁻¹ : Perm (Fin n)).IsSwap :=
    ⟨π 0, π 1, π.injective.ne C.zero_ne_one', (swap_apply_apply π 0 1).symm⟩
  have hcompat : ∀ (k : G) (hk : k ∈ K) (hk' : t * k * t⁻¹ ∈ K),
      ((α ⟨t * k * t⁻¹, hk'⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) =
        (π * swap 0 1 * π⁻¹) * (α ⟨k, hk⟩ : Perm (Fin n)) * (π * swap 0 1 * π⁻¹)⁻¹ := by
    intro k hk hk'
    rw [hπ, hπ, hρφ, hρφ]
    have he : (⟨t * k * t⁻¹, Subgroup.mem_sup_left hk'⟩ : ↥(K ⊔ R)) =
        ⟨t, htX⟩ * ⟨k, Subgroup.mem_sup_left hk⟩ * ⟨t, htX⟩⁻¹ := Subtype.ext rfl
    rw [show (⟨t * k * t⁻¹, _⟩ : ↥(K ⊔ R)) = _ from he, map_mul, map_mul, map_inv, hφt]
    group
  have hMeq : autOn (M ⊓ K) (Vc R K) = autOn K (Vc R K) ⊓
      Subgroup.centralizer (autOn R (Vc R K) : Set (MulAut ↥(Vc R K))) := by
    rw [hR, htτ]
    apply le_antisymm
    · intro g hg
      refine Subgroup.mem_inf.2 ⟨autOn_mono' inf_le_right hg,
        Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      have hc : Commute g τ.1 := hMK g hg
      exact (hc.zpow_right j).eq.symm
    · rintro g ⟨hgK, hgC⟩
      have hgX : g ∈ starOf R K (K ⊔ R) := star_le le_sup_left hgK
      have hcomm := Subgroup.mem_centralizer_iff.1 hgC _ (Subgroup.mem_zpowers _)
      have h1 : C.ι ⟨g, hgX⟩ ∈ C.bar (M ⊓ K) := by
        rw [C.bar_MK_k1]
        refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · rw [← C.K_map]
          exact (mem_Bmap_iff_of_injective C.inj _).2 hgK
        · rw [Subgroup.mem_centralizer_singleton_iff, ← hτ, ← map_mul, ← map_mul]
          exact congrArg C.ι (Subtype.ext hcomm.symm)
      exact (mem_Bmap_iff_of_injective C.inj _).1 h1
  exact Or.inr (Or.inl ⟨⟨n, α, h5, h8, hK, hα, t, htR, htV, hR, hord, _, hσ, hcompat⟩, hMeq⟩)

end AltCtx

end K1

end CFSG.Quasithin.SmithC27
