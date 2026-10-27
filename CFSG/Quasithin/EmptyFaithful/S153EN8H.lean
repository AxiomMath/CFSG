module

public import CFSG.Quasithin.EmptyFaithful.S153EN8G
public import CFSG.Quasithin.EmptyFaithful.S153EN8A
public import CFSG.Quasithin.EmptyFaithful.S153EN8F

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153EN8

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {cx : Ctx15350 T Mc M V₁ V₂ t} {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y t₁ : G}

section JPart

variable (h113 : StageLemma14113) (c : Chain15359 cx N₁ N₂ g s y t₁) (B : BarModel cx)
  {d : G} (hdM : d ∈ M) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) (hbd : barM cx hdM ∈ B.L₂)

include B hdM hbd in
theorem d_mem_M₂ : d ∈ M ⊓ Subgroup.centralizer (V₁ : Set G) := (mem_M₂_iff B).2 ⟨hdM, hbd⟩

include c B hd3 hd1 hbd in
theorem exists_lift_J {ℓ : MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian)} (hℓ : ℓ ∈ B.L₁) :
    ∃ (x : G) (hx : x ∈ M), x ∈ Jgp M V₂ d ∧ barM cx hx = ℓ := by
  have hMN := cx.c.hyp.le_normalizer
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x₀, hx₀M, hx₀⟩ := exists_barM (B.hS.L₁_le hℓ)
  set Qg : Subgroup G := M ⊓ Subgroup.centralizer (VZ T M : Set G) with hQg
  have hQ2 : IsPGroup 2 Qg := isPGroup_Q c.toChain15358
  have hT2 : IsPGroup 2 T := cx.hF.sylow_H.2.1
  have hD3 : Nat.card (Subgroup.zpowers d) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hd3 hd1]
  have hDp : IsPGroup 3 (Subgroup.zpowers d) :=
    IsPGroup.of_card (p := 3) (n := 1) (by simpa using hD3)
  have hDQ : Subgroup.zpowers d ⊓ Qg = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx.1
    refine eq_one_of_cube_of_mem_T hT2 (Q_le_T c.toChain15358 hx.2) ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd3, one_zpow]
  have hQD : Subgroup.zpowers d ≤ Subgroup.normalizer (Qg : Set G) :=
    Subgroup.zpowers_le.2 (le_normalizer_Q hMN hdM)
  have hsyl : ¬ 3 ∣ (Subgroup.zpowers d).relIndex (Subgroup.zpowers d ⊔ Qg) := by
    have h1 := Subgroup.relIndex_mul_card (Subgroup.zpowers d) (Subgroup.zpowers d ⊔ Qg)
    have h2 := S153E59.card_sup_mul_card_inf_of_normalizes hQD
    rw [inf_eq_left.2 le_sup_left] at h1
    rw [hDQ, Subgroup.card_bot, mul_one, hD3] at h2
    obtain ⟨n, hn⟩ := hQ2.exists_card_eq
    rw [hn] at h2
    rw [h2] at h1
    have h3 : (Subgroup.zpowers d).relIndex (Subgroup.zpowers d ⊔ Qg) = 2 ^ n := by
      rw [hD3] at h1
      omega
    rw [h3]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have hx : ∀ δ ∈ Subgroup.zpowers d, x₀ * δ * x₀⁻¹ * δ⁻¹ ∈ Qg := by
    intro δ hδ
    have hδM2 : δ ∈ M ⊓ Subgroup.centralizer (V₁ : Set G) :=
      (Subgroup.zpowers_le.2 (d_mem_M₂ B hdM hbd)) hδ
    obtain ⟨hδM, hδb⟩ := (mem_M₂_iff B).1 hδM2
    exact commutator_mem_Q hx₀M hδM (by rw [hx₀]; exact B.hS.comm _ hℓ _ hδb)
  obtain ⟨q, hq, hqc⟩ := exists_mul_mem_centralizer hDp hDQ hQD hsyl hx
  have hqM : q ∈ M := hq.1
  have hxM : q⁻¹ * x₀ ∈ M := M.mul_mem (M.inv_mem hqM) hx₀M
  have hbar : barM cx hxM = ℓ := by
    rw [barM_mul (M.inv_mem hqM) hx₀M, barM_inv hqM, (barM_eq_one_iff hqM).2 hq.2, inv_one,
      one_mul, hx₀]
  refine ⟨q⁻¹ * x₀, hxM, ?_, hbar⟩
  rw [mem_Jgp]
  refine ⟨⟨hxM, ((mem_M₁_iff B).2 ⟨hxM, by rw [hbar]; exact hℓ⟩).2⟩, ?_⟩
  exact (Subgroup.mem_centralizer_iff.1 hqc d (Subgroup.mem_zpowers d)).symm

include h113 c B hdM hd3 hd1 hbd in
theorem inf_centralizer_Jgp :
    Jgp M V₂ d ⊓ Subgroup.centralizer (VZ T M : Set G) = V₁ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxJ, hxC⟩ := Subgroup.mem_inf.1 hx
    rw [mem_Jgp] at hxJ
    exact centralizer_Q_le_V₁ h113 c B hdM hd3 hd1 hbd ⟨hxJ.1.1, hxC⟩ hxJ.2
  · intro x hx
    have hV := cx.c.hyp.elemAbelian
    have hxV : x ∈ VZ T M := cx.c.decomp.le₁ hx
    have hxM : x ∈ M := (cx.c.hyp.VZ_le_T.trans (S153E.T_le_M cx)) hxV
    have hxC : x ∈ Subgroup.centralizer (VZ T M : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact B2F.isElemAbelian_comm hV hv hxV
    refine Subgroup.mem_inf.2 ⟨?_, hxC⟩
    rw [mem_Jgp]
    refine ⟨⟨hxM, ?_⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact B2F.isElemAbelian_comm hV (cx.c.decomp.le₂ hv) hxV
    · exact Subgroup.mem_centralizer_iff.1 (d_mem_M₂ B hdM hbd).2 x hx

include c B hd3 hd1 hbd in
theorem autI_Jgp : autI cx.c.hyp.elemAbelian (Jgp M V₂ d) = B.L₁ := by
  apply le_antisymm
  · intro φ hφ
    obtain ⟨x, hx, rfl⟩ := (mem_autI _).1 hφ
    have hxJ := (mem_Jgp.1 hx)
    obtain ⟨hxM, hbx⟩ := (mem_M₁_iff B).1 (show (x : G) ∈ M ⊓ Subgroup.centralizer (V₂ : Set G) from
      ⟨hxJ.1.1, hxJ.1.2⟩)
    exact hbx
  · intro ℓ hℓ
    obtain ⟨x, hxM, hxJ, hbar⟩ := exists_lift_J c B hdM hd3 hd1 hbd hℓ
    rw [← hbar]
    exact convI_mem_autI _ hxJ _

include h113 c B hdM hd3 hd1 hbd in
theorem card_Jgp : Nat.card (Jgp M V₂ d) = 24 := by
  have hV := cx.c.hyp.elemAbelian
  have hJN : Jgp M V₂ d ≤ Subgroup.normalizer (VZ T M : Set G) := fun x hx =>
    cx.c.hyp.le_normalizer ((mem_Jgp.1 hx).1.1)
  have h := card_autI_mul_card_inf hV hJN
  rw [autI_Jgp c B hdM hd3 hd1 hbd, inf_centralizer_Jgp h113 c B hdM hd3 hd1 hbd,
    B.hS.card_L₁, cx.c.decomp.card₁] at h
  omega

include B in
theorem mem_normalizer_V₁ {x : G} (hx : x ∈ M ⊓ Subgroup.centralizer (V₂ : Set G)) :
    x ∈ Subgroup.normalizer (V₁ : Set G) := by
  have hV := cx.c.hyp.elemAbelian
  obtain ⟨hxM, hbx⟩ := (mem_M₁_iff B).1 hx
  have hxN := cx.c.hyp.le_normalizer hxM
  rw [← B.hV₁]
  refine (mem_normalizer_map_inclMod_iff hV hxN (commV B.L₁)).2 ?_
  exact mem_stabSub_of_forall (fun u hu => commV_stable B.L₁ hbx hu)
    (fun u hu => commV_stable B.L₁ (B.L₁.inv_mem hbx) hu)

omit [Finite G] in
theorem autI_zpowers_eq' {V : Subgroup G} (hV : IsElemAbelian 2 V) {x : G}
    (hx : x ∈ Subgroup.normalizer (V : Set G)) :
    autI hV (Subgroup.zpowers x) = Subgroup.zpowers (convI hV ⟨x, hx⟩) := by
  ext φ
  rw [mem_autI hV]
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [← map_zpow]
    congr 1
    exact Subtype.ext hk
  · rintro hφ
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hφ
    refine ⟨⟨x ^ k, Subgroup.zpow_mem _ hx k⟩, Subgroup.zpow_mem_zpowers x k, ?_⟩
    rw [← map_zpow]
    rfl

include h113 c B hdM hd3 hd1 hbd in
theorem V₁_le_Jgp : V₁ ≤ Jgp M V₂ d := by
  have := (inf_centralizer_Jgp h113 c B hdM hd3 hd1 hbd).ge
  exact this.trans inf_le_left

include h113 c B hdM hd3 hd1 hbd in
theorem pCoreOf_Jgp : pCoreOf 2 (Jgp M V₂ d) = V₁ := by
  have hV := cx.c.hyp.elemAbelian
  have hJM : ∀ x ∈ Jgp M V₂ d, x ∈ M ⊓ Subgroup.centralizer (V₂ : Set G) := fun x hx =>
    ⟨(mem_Jgp.1 hx).1.1, (mem_Jgp.1 hx).1.2⟩
  apply le_antisymm
  · intro x hxO
    have hxJ : x ∈ Jgp M V₂ d := pCoreOf_le 2 _ hxO
    have hxM : x ∈ M := (mem_Jgp.1 hxJ).1.1
    set O := pCoreOf 2 (Jgp M V₂ d) with hO
    have hO2 : IsPGroup 2 O := pCoreOf_isPGroup 2 _
    have hS : autI hV O = ⊥ := by
      refine eq_bot_of_normal_pgroup B.hS.nat₁ ?_ ?_ ?_
      · rw [← autI_Jgp c B hdM hd3 hd1 hbd]
        exact autI_mono hV (pCoreOf_le 2 _)
      · intro ℓ hℓ ξ hξ
        obtain ⟨j, hjM, hjJ, hj⟩ := exists_lift_J c B hdM hd3 hd1 hbd hℓ
        obtain ⟨o, ho, rfl⟩ := (mem_autI hV).1 hξ
        have hjo : j * (o : G) * j⁻¹ ∈ O :=
          (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 (Jgp M V₂ d) hjJ) _).1 ho
        have hjN : j ∈ Subgroup.normalizer (VZ T M : Set G) := cx.c.hyp.le_normalizer hjM
        have h1 := convI_mem_autI hV hjo (cx.c.hyp.le_normalizer
          (M.mul_mem (M.mul_mem hjM (mem_Jgp.1 (pCoreOf_le 2 _ ho)).1.1) (M.inv_mem hjM)))
        have e : (⟨j * (o : G) * j⁻¹, cx.c.hyp.le_normalizer
            (M.mul_mem (M.mul_mem hjM (mem_Jgp.1 (pCoreOf_le 2 _ ho)).1.1) (M.inv_mem hjM))⟩ :
            Subgroup.normalizer (VZ T M : Set G)) = ⟨j, hjN⟩ * o * ⟨j, hjN⟩⁻¹ := Subtype.ext rfl
        rw [e, map_mul, map_mul, map_inv] at h1
        have hj' : convI hV ⟨j, hjN⟩ = ℓ := hj
        rwa [hj'] at h1
      · intro ξ
        obtain ⟨o, ho, hξ⟩ := (mem_autI hV).1 ξ.2
        obtain ⟨n, hn⟩ := hO2 ⟨(o : G), ho⟩
        refine ⟨n, ?_⟩
        have hn' : (o : G) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
        apply Subtype.ext
        show (ξ : MulAut (IntMod (VZ T M) hV)) ^ 2 ^ n = 1
        rw [← hξ, ← map_pow]
        have : o ^ 2 ^ n = 1 := Subtype.ext (by simpa using hn')
        rw [this, map_one]
    have h1 : convI hV ⟨x, cx.c.hyp.le_normalizer hxM⟩ ∈ autI hV O := convI_mem_autI hV hxO _
    rw [hS, Subgroup.mem_bot] at h1
    have h2 := (convI_eq_one_iff hV _).1 h1
    rw [← inf_centralizer_Jgp h113 c B hdM hd3 hd1 hbd]
    exact Subgroup.mem_inf.2 ⟨hxJ, h2⟩
  · exact le_pCoreOf_of_le_normalizer 2 (V₁_le_Jgp h113 c B hdM hd3 hd1 hbd)
      (fun x hx => mem_normalizer_V₁ B (hJM x hx))
      ((B2F.isPGroup_of_isElemAbelian hV).to_le cx.c.decomp.le₁)

end JPart

end S153EN8

end CFSG.Quasithin
