module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoBar2
public import CFSG.LocalAnalysis.WeakClosure81.FourteenFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem c23ne_bar2_of_calC {M V₀ V K : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMs : M ≤ stabTil V₀ V) (hKM : K ≤ M) (hK : CFSG.Open.IsQuasisimple (Bar2 K))
    (hKb : IsL3 ↥(barSub V₀ V hV K) 1) :
    IsL3 (Bar2 K) 1 ∧ K ⊓ F11.CTilde M V₀ V ≤ pCoreOf 2 K := by
  let ψ : ↥K →* MulAut (Vtil V₀ V hV) :=
    (actTil V₀ V hV).comp (Subgroup.inclusion (hKM.trans hMs))
  have hrange : ψ.range = barSub V₀ V hV K := by
    ext φ
    rw [MonoidHom.mem_range, mem_barSub]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨Subgroup.inclusion (hKM.trans hMs) k, k.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨(g : G), hg⟩, rfl⟩
  have hY : IsL3 ↥ψ.range 1 :=
    CFSG.Blueprint.LieModel.of_mulEquiv (MulEquiv.subgroupCongr hrange.symm) hKb
  obtain ⟨h1, h2⟩ := s16c7_quot_isL3 hY ψ.rangeRestrict (MonoidHom.rangeRestrict_surjective ψ) hK
  refine ⟨h1, ?_⟩
  rintro x ⟨hxK, hxc⟩
  have hx : (⟨x, hxK⟩ : ↥K) ∈ ψ.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker]
    change actTil V₀ V hV (Subgroup.inclusion (hKM.trans hMs) ⟨x, hxK⟩) = 1
    rw [actTil_eq_one_iff]
    intro v hv
    exact WeakClosure81.mem_cTilde_mul_inv hV (hMs.trans (stabTil_le_normalizer V₀ V)) hxc hv
  exact ⟨⟨x, hxK⟩, h2 hx, rfl⟩

private theorem c23ne_le_of_isSubnormal {A B : Subgroup G} (h : IsSubnormal A B) : A ≤ B := by
  induction h with
  | refl => exact le_rfl
  | step hHM _ _ ih => exact hHM.trans ih

theorem c23ne_centralizes_V₀ {K V₀ : Subgroup G} (hK : ⁅K, K⁆ = K) (hV₀ : IsElemAbelian 2 V₀)
    (hr : mSub V₀ ≤ 2) (hn : K ≤ normalizer (V₀ : Set G)) : K ≤ centralizer (V₀ : Set G) := by
  let ψ : ↥K →* MulAut ↥V₀ :=
    (Subgroup.normalizerMonoidHom V₀).comp (Subgroup.inclusion hn)
  have hcard : Nat.card ↥V₀ ≤ 4 := by
    rw [card_eq_two_pow_mSub (IsElemAbelian.isPGroup hV₀)]
    calc 2 ^ mSub V₀ ≤ 2 ^ 2 := pow_le_pow_right' (by norm_num) hr
      _ = 4 := by norm_num
  haveI : Group.IsSolvable (Equiv.Perm ↥V₀) := Equiv.Perm.isSolvable (α := ↥V₀) hcard
  haveI : Group.IsSolvable (MulAut ↥V₀) :=
    Group.isSolvable_of_isSolvable_injective (f := MulAut.toPerm ↥V₀)
      (fun _ _ h => MulEquiv.toEquiv_injective h)
  have hperfK : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 hK
  haveI : Group.IsPerfect (⊤ : Subgroup ↥K) := Group.IsPerfect.top_iff.2 hperfK
  have hperf : Group.IsPerfect ↥ψ.range := by
    have hmap := Group.IsPerfect.map (f := ψ) (H := ⊤)
    rw [Subgroup.map_top] at hmap
    exact hmap
  have hperf_eq : ⁅ψ.range, ψ.range⁆ = ψ.range := Subgroup.isPerfect_iff.1 hperf
  have hbot : ψ.range = ⊥ := by
    by_contra hne
    have hlt : ⁅ψ.range, ψ.range⁆ < ψ.range :=
      Group.IsSolvable.commutator_lt_of_ne_bot hne
    rw [hperf_eq] at hlt
    exact lt_irrefl _ hlt
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h1 : ψ ⟨k, hk⟩ = 1 := by
    have hmem : ψ ⟨k, hk⟩ ∈ ψ.range := (MonoidHom.mem_range).2 ⟨⟨k, hk⟩, rfl⟩
    rw [hbot] at hmem
    exact Subgroup.mem_bot.1 hmem
  have hfix : ψ ⟨k, hk⟩ ⟨v, hv⟩ = ⟨v, hv⟩ := by rw [h1]; rfl
  have hval : ((ψ ⟨k, hk⟩ ⟨v, hv⟩ : ↥V₀) : G) = k * v * k⁻¹ := by
    simpa [ψ, MonoidHom.comp_apply, Subgroup.coe_inclusion] using
      Subgroup.normalizerMonoidHom_apply_apply_coe V₀ (Subgroup.inclusion hn ⟨k, hk⟩) ⟨v, hv⟩
  have hkv : k * v * k⁻¹ = v :=
    hval.symm.trans (congrArg Subtype.val hfix)
  have hmul : k * v = v * k := by
    have h := congrArg (fun x : G => x * k) hkv
    simpa [mul_assoc] using h
  exact hmul.symm

theorem c23ne_ker_eq {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (hMs : M ≤ stabTil V₀ V)
    {K₁ K₂ : Subgroup G} (hK₁ : K₁ ∈ calC M) (hK₂ : K₂ ∈ calC M)
    (hn₁ : K₁ ≤ normalizer (K₂ : Set G)) (hn₂ : K₂ ≤ normalizer (K₁ : Set G))
    (hL₁ : IsL3 ↥(barSub V₀ V hV K₁) 1) (hL₂ : IsL3 ↥(barSub V₀ V hV K₂) 1)
    (hinf : barSub V₀ V hV K₁ ⊓ barSub V₀ V hV K₂ = ⊥) :
    F11.CTilde M V₀ V ⊓ (K₁ ⊔ K₂) = c23neQ2 K₁ K₂ ∧ IsPGroup 2 ↥(c23neQ2 K₁ K₂) := by
  have hK₁M : K₁ ≤ M := c23ne_le_of_isSubnormal hK₁.1
  have hK₂M : K₂ ≤ M := c23ne_le_of_isSubnormal hK₂.1
  have hSupM : K₁ ⊔ K₂ ≤ M := sup_le hK₁M hK₂M
  have hMn : M ≤ normalizer (V : Set G) := hMs.trans (stabTil_le_normalizer V₀ V)
  have hact : ∀ {K : Subgroup G} (hKM : K ≤ M) {k : G} (hk : k ∈ K),
      (actTil V₀ V hV ⟨k, hKM.trans hMs hk⟩ = 1) ↔ k ∈ F11.CTilde M V₀ V := by
    intro K hKM k hk
    rw [mem_cTilde_iff hV hMn]
    constructor
    · intro h
      exact ⟨hKM hk, ⟨hKM.trans hMs hk, h⟩⟩
    · rintro ⟨-, h, h1⟩
      have heq : (⟨k, h⟩ : stabTil V₀ V) = ⟨k, hKM.trans hMs hk⟩ := Subtype.ext rfl
      rwa [heq] at h1
  have hpCore : ∀ {K : Subgroup G}, K ≤ M → IsL3 ↥(barSub V₀ V hV K) 1 →
      pCoreOf 2 K ≤ F11.CTilde M V₀ V := by
    intro K hKM hKb
    let ψ : ↥K →* MulAut (Vtil V₀ V hV) :=
      (actTil V₀ V hV).comp (Subgroup.inclusion (hKM.trans hMs))
    have hrange : ψ.range = barSub V₀ V hV K := by
      ext φ
      rw [MonoidHom.mem_range, mem_barSub]
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨Subgroup.inclusion (hKM.trans hMs) k, k.2, rfl⟩
      · rintro ⟨g, hg, rfl⟩
        exact ⟨⟨(g : G), hg⟩, rfl⟩
    have hY : IsL3 ↥ψ.range 1 :=
      CFSG.Blueprint.LieModel.of_mulEquiv (MulEquiv.subgroupCongr hrange.symm) hKb
    have hs : IsSimpleGroup ↥ψ.range := isSimpleGroup_of_isL3 hY
    have hcard : Nat.card ↥ψ.range = 168 := card_eq_of_isL3 hY
    have hPbot : (CFSG.pCore 2 ↥K).map ψ.rangeRestrict = ⊥ := by
      by_contra hne
      haveI : ((CFSG.pCore 2 ↥K).map ψ.rangeRestrict).Normal :=
        Subgroup.Normal.map inferInstance ψ.rangeRestrict (MonoidHom.rangeRestrict_surjective ψ)
      have hNp : IsPGroup 2 ((CFSG.pCore 2 ↥K).map ψ.rangeRestrict) :=
        IsPGroup.map CFSG.pCore_isPGroup ψ.rangeRestrict
      have htop : (CFSG.pCore 2 ↥K).map ψ.rangeRestrict = ⊤ := by
        rcases hs.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥K).map ψ.rangeRestrict) with h | h
        · exact absurd h hne
        · exact h
      have hY2 : IsPGroup 2 ↥ψ.range := by
        have htop' : IsPGroup 2 (⊤ : Subgroup ↥ψ.range) := htop ▸ hNp
        exact htop'.of_equiv (Subgroup.topEquiv (G := ↥ψ.range))
      obtain ⟨n, hn⟩ := hY2.exists_card_eq
      rw [hcard] at hn
      have h3 : 3 ∣ 2 ^ n := ⟨56, by omega⟩
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
    have hker : CFSG.pCore 2 ↥K ≤ ψ.rangeRestrict.ker :=
      (Subgroup.map_eq_bot_iff (CFSG.pCore 2 ↥K)).1 hPbot
    intro x hx
    have hxK : x ∈ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K hx
    have hxP : (⟨x, hxK⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := by
      rcases hx with ⟨y, hy, hyx⟩
      rw [show (⟨x, hxK⟩ : ↥K) = y from Subtype.ext hyx.symm]
      exact hy
    have hxact : actTil V₀ V hV ⟨x, hKM.trans hMs hxK⟩ = 1 := by
      have h3 : ψ ⟨x, hxK⟩ = 1 := by
        have h2 := congrArg Subtype.val (hker hxP)
        simpa using h2
      change actTil V₀ V hV (Subgroup.inclusion (hKM.trans hMs) ⟨x, hxK⟩) = 1
      simpa [ψ, MonoidHom.comp_apply] using h3
    exact (hact hKM hxK).1 hxact
  constructor
  · refine le_antisymm ?_ ?_
    · intro x hx
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxZ, hxsup⟩ := hx
      have hmem : x ∈ (K₁ : Set G) * (K₂ : Set G) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right K₁ K₂ hn₁]
        exact hxsup
      obtain ⟨k₁, hk₁, k₂, hk₂, h₁₂⟩ := Set.mem_mul.mp hmem
      have hm₁ : actTil V₀ V hV ⟨k₁, hK₁M.trans hMs hk₁⟩ ∈ barSub V₀ V hV K₁ :=
        actTil_mem_barSub V₀ V hV hk₁ (hK₁M.trans hMs hk₁)
      have hm₂ : actTil V₀ V hV ⟨k₂, hK₂M.trans hMs hk₂⟩ ∈ barSub V₀ V hV K₂ :=
        actTil_mem_barSub V₀ V hV hk₂ (hK₂M.trans hMs hk₂)
      have hprod : actTil V₀ V hV ⟨k₁, hK₁M.trans hMs hk₁⟩ *
          actTil V₀ V hV ⟨k₂, hK₂M.trans hMs hk₂⟩ = 1 := by
        rw [← map_mul]
        have heq : (⟨k₁, hK₁M.trans hMs hk₁⟩ * ⟨k₂, hK₂M.trans hMs hk₂⟩ : stabTil V₀ V) =
            ⟨x, hSupM.trans hMs hxsup⟩ := by
          ext
          exact h₁₂
        rw [heq]
        exact (hact hSupM hxsup).2 hxZ
      have h1eq : actTil V₀ V hV ⟨k₁, hK₁M.trans hMs hk₁⟩ =
          (actTil V₀ V hV ⟨k₂, hK₂M.trans hMs hk₂⟩)⁻¹ :=
        mul_eq_one_iff_eq_inv.mp hprod
      have hk₁c : k₁ ∈ F11.CTilde M V₀ V := by
        have hmem1 : actTil V₀ V hV ⟨k₁, hK₁M.trans hMs hk₁⟩ ∈
            barSub V₀ V hV K₁ ⊓ barSub V₀ V hV K₂ :=
          ⟨hm₁, by rw [h1eq]; exact (barSub V₀ V hV K₂).inv_mem hm₂⟩
        rw [hinf] at hmem1
        exact (hact hK₁M hk₁).1 (Subgroup.mem_bot.1 hmem1)
      have hk₂c : k₂ ∈ F11.CTilde M V₀ V := by
        have h2eq : actTil V₀ V hV ⟨k₂, hK₂M.trans hMs hk₂⟩ =
            (actTil V₀ V hV ⟨k₁, hK₁M.trans hMs hk₁⟩)⁻¹ :=
          mul_eq_one_iff_eq_inv'.mp hprod
        have hmem2 : actTil V₀ V hV ⟨k₂, hK₂M.trans hMs hk₂⟩ ∈
            barSub V₀ V hV K₁ ⊓ barSub V₀ V hV K₂ :=
          ⟨by rw [h2eq]; exact (barSub V₀ V hV K₁).inv_mem hm₁, hm₂⟩
        rw [hinf] at hmem2
        exact (hact hK₂M hk₂).1 (Subgroup.mem_bot.1 hmem2)
      have hk₁Q : k₁ ∈ pCoreOf 2 K₁ :=
        (c23ne_bar2_of_calC hV hMs hK₁M hK₁.2.2 hL₁).2 ⟨hk₁, hk₁c⟩
      have hk₂Q : k₂ ∈ pCoreOf 2 K₂ :=
        (c23ne_bar2_of_calC hV hMs hK₂M hK₂.2.2 hL₂).2 ⟨hk₂, hk₂c⟩
      rw [← h₁₂]
      exact Subgroup.mul_mem_sup hk₁Q hk₂Q
    · intro x hx
      change x ∈ pCoreOf 2 K₁ ⊔ pCoreOf 2 K₂ at hx
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · exact (sup_le (hpCore hK₁M hL₁) (hpCore hK₂M hL₂)) hx
      · exact (sup_le ((CFSG.LieType.BorelTits.pCoreOf_le 2 K₁).trans le_sup_left)
          ((CFSG.LieType.BorelTits.pCoreOf_le 2 K₂).trans le_sup_right)) hx
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp1 : IsPGroup 2 (pCoreOf 2 K₁) :=
      CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K₁
    have hp2 : IsPGroup 2 (pCoreOf 2 K₂) :=
      CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K₂
    have hnorm : pCoreOf 2 K₂ ≤ Subgroup.normalizer (pCoreOf 2 K₁ : Set G) :=
      (CFSG.LieType.BorelTits.pCoreOf_le 2 K₂).trans (hn₂.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K₁))
    change IsPGroup 2 ↥(pCoreOf 2 K₁ ⊔ pCoreOf 2 K₂)
    exact IsPGroup.to_sup_of_normal_left' hp1 hp2 hnorm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
