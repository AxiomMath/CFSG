module

public import CFSG.LocalAnalysis.WeakClosure81.SixFiveH
public import CFSG.LocalAnalysis.WeakClosure81.SixFiveJ
import CFSG.CGT.T75N.BenderCenter
import CFSG.CGT.T75N.UnitaryTwoGen

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Hyp65

variable {n : ℕ} {M V₀ V : Subgroup G} {g : G}

private theorem s65_SixFiveK_mQuot {W V : Subgroup G} (hWV : W ≤ V)
    (hV : IsElemAbelian 2 V) : W.relIndex V = 2 ^ E3.mQuot V W := by
  have hdvd : W.relIndex V ∣ 2 ^ mSub V := by
    simpa only [card_eq_two_pow_mSub hV.isPGroup] using Subgroup.relIndex_dvd_card W V
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [ha, E3.mQuot, ha, padicValNat.prime_pow]

theorem conjV₀_le_K_iff (h : Hyp65 n M V₀ V g) :
    conjSubgroup V₀ g ≤ KOf M V g ↔ V₀ ≤ KOf M V g := by
  obtain ⟨l, hlL, hl⟩ := h.exists_conj
  have hV0l : conjSubgroup V₀ g = conjSubgroup V₀ l :=
    conjSubgroup_V₀_eq_of_conjSubgroup_eq h.normalizer_eq h.normalizer₀.ge hl
  have hlK : l ∈ normalizer (KOf M V g : Set G) := h.L_le_normalizer_K hlL
  have hKl : conjSubgroup (KOf M V g) l = KOf M V g :=
    conjSubgroup_eq_iff_mem_normalizer.2 hlK
  have hKli : conjSubgroup (KOf M V g) l⁻¹ = KOf M V g :=
    conjSubgroup_eq_iff_mem_normalizer.2 (inv_mem hlK)
  constructor
  · intro hle
    have hmono := conjSubgroup_mono hle l⁻¹
    rw [hV0l, conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one, hKli] at hmono
    exact hmono
  · intro hle
    rw [hV0l]
    simpa only [hKl] using conjSubgroup_mono hle l

theorem V_le_V₀_sup_U_of_le_K (h : Hyp65 n M V₀ V g) (hV : V ≤ V₀ ⊔ KOf M V g) :
    V ≤ V₀ ⊔ UOf M V g := by
  have hV₀norm : V₀ ≤ normalizer (KOf M V g : Set G) :=
    (h.le.trans le_sup_left).trans h.L_le_normalizer_K
  intro v hv
  have hvsup : v ∈ V₀ ⊔ KOf M V g := hV hv
  have hvsup' : v ∈ ((V₀ ⊔ KOf M V g : Subgroup G) : Set G) := hvsup
  rw [Subgroup.coe_mul_of_left_le_normalizer_right V₀ (KOf M V g) hV₀norm] at hvsup'
  have hvprod : v ∈ (V₀ : Set G) * (KOf M V g : Set G) := hvsup'
  obtain ⟨v₀, hv₀, k, hk, hvk⟩ := Set.mem_mul.1 hvprod
  have hkU : k ∈ UOf M V g := by
    have hkV : k ∈ V := by
      have hk_eq : k = v₀⁻¹ * v := by rw [← hvk]; group
      rw [hk_eq]
      exact V.mul_mem (V.inv_mem (h.le hv₀)) hv
    have hmem : k ∈ V ⊓ KOf M V g := ⟨hkV, hk⟩
    rwa [V_inf_K h] at hmem
  rw [← hvk]
  exact (V₀ ⊔ UOf M V g).mul_mem (Subgroup.mem_sup_left hv₀) (Subgroup.mem_sup_right hkU)

theorem V₀_inf_N (h : Hyp65 n M V₀ V g) : V₀ ⊓ NOf M V g = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxVg : x ∈ conjSubgroup V g :=
    (inf_le_left : BOf M V g ≤ conjSubgroup V g) hx.2.2
  have hmem : x ∈ V₀ ⊓ conjSubgroup V g := ⟨hx.1, hxVg⟩
  rw [V₀_inf_conjV h] at hmem
  exact hmem

theorem conjV₀_inf_N (h : Hyp65 n M V₀ V g) : conjSubgroup V₀ g ⊓ NOf M V g = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxV : x ∈ V := (inf_le_left : UOf M V g ≤ V) hx.2.1
  have hmem : x ∈ conjSubgroup V₀ g ⊓ V := ⟨hx.1, hxV⟩
  rw [conjV₀_inf_V h] at hmem
  exact hmem

theorem mSub_le_rMV (h : Hyp65 n M V₀ V g) : (mSub V₀ : ℕ∞) ≤ rMV M V := by
  unfold rMV
  refine le_iInf₂ fun W hW => ?_
  have hWV : W ≤ V := hW.1
  have hnc : ¬ centralizer (W : Set G) ≤ M := hW.2
  have hinf : V₀ ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    by_contra hx1
    have hcen : centralizer ({x} : Set G) ≤ M :=
      centralizer_le_M_of_mem_V₀ h.isTI h.normalizer₀ hx.1 hx1
    have hWle : centralizer (W : Set G) ≤ centralizer ({x} : Set G) := by
      refine Subgroup.centralizer_le ?_
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hx.2
    exact hnc (hWle.trans hcen)
  haveI : IsMulCommutative ↥V := h.elemAbelian.1
  haveI : (W.subgroupOf V).Normal := Subgroup.normal_of_isMulCommutative _
  let f : ↥V₀ → (↥V ⧸ (W.subgroupOf V)) :=
    fun v => QuotientGroup.mk (⟨(v : G), h.le v.2⟩ : ↥V)
  have hf : Function.Injective f := by
    intro a b hab
    have hmem : (⟨(a : G), h.le a.2⟩ : ↥V)⁻¹ * ⟨(b : G), h.le b.2⟩ ∈ W.subgroupOf V :=
      QuotientGroup.eq.1 hab
    have hW : (a : G)⁻¹ * (b : G) ∈ W := Subgroup.mem_subgroupOf.1 hmem
    have hV0 : (a : G)⁻¹ * (b : G) ∈ V₀ := V₀.mul_mem (V₀.inv_mem a.2) b.2
    have hbot : (a : G)⁻¹ * (b : G) ∈ (⊥ : Subgroup G) := by
      rw [← hinf]
      exact ⟨hV0, hW⟩
    have hone : (a : G)⁻¹ * (b : G) = 1 := Subgroup.mem_bot.1 hbot
    have habG : (a : G) = (b : G) := by
      have hh := congrArg (fun z => (a : G) * z) hone
      simpa [mul_assoc] using hh.symm
    exact Subtype.ext habG
  have hcard := Nat.card_le_card_of_injective f hf
  change Nat.card ↥V₀ ≤ W.relIndex V at hcard
  rw [s65_SixFiveK_mQuot hWV h.elemAbelian,
    card_eq_two_pow_mSub (h.elemAbelian.mono h.le).isPGroup] at hcard
  have hnat : mSub V₀ ≤ E3.mQuot V W :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hcard
  exact_mod_cast hnat

section Certified

theorem V_le_V₀_sup_K (h : Hyp65 n M V₀ V g) (hV₀K : ¬ V₀ ≤ KOf M V g) :
    V ≤ V₀ ⊔ KOf M V g := by
  haveI := h.K_normal
  let L := LOf V g
  let π : ↥L →* (↥L ⧸ (KOf M V g).subgroupOf L) :=
    QuotientGroup.mk' ((KOf M V g).subgroupOf L)
  let T : Subgroup (↥L ⧸ (KOf M V g).subgroupOf L) := imgK M V g V
  let T₀ : Subgroup (↥L ⧸ (KOf M V g).subgroupOf L) := imgK M V g V₀
  have hT₀T : T₀ ≤ T := by
    unfold T T₀ imgK
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono L h.le)
  obtain ⟨v₀, hv₀V₀, hv₀K⟩ := SetLike.not_le_iff_exists.1 hV₀K
  have hv₀L : v₀ ∈ L := (h.le.trans le_sup_left) hv₀V₀
  let v₀L : ↥L := ⟨v₀, hv₀L⟩
  let t₀ : ↥L ⧸ (KOf M V g).subgroupOf L := π v₀L
  have ht₀mem : t₀ ∈ T₀ := by
    unfold T₀ imgK t₀
    rw [Subgroup.mem_map]
    exact ⟨v₀L, (Subgroup.mem_subgroupOf).2 hv₀V₀, rfl⟩
  have ht₀1 : t₀ ≠ 1 := by
    intro h1
    exact hv₀K ((mk_eq_one_iff_mem_K M V g v₀L).1 h1)
  have hTle : T ≤ T₀ := by
    intro t ht
    by_cases ht1 : t = 1
    · rw [ht1]
      exact T₀.one_mem
    · obtain ⟨n, hn, hnt⟩ := h.quotPair.exists_normalizer_conj
        CFSG.CGT.T75N.benderCenterInput CFSG.CGT.T75N.unitaryTwoGenerationInput
        (T := T) (T₁ := imgK M V g (conjSubgroup V g)) (hT₀T ht₀mem) ht₀1 ht ht1
      obtain ⟨l, hlπ⟩ := QuotientGroup.mk'_surjective
        ((KOf M V g).subgroupOf L) n
      have hlnorm : π l ∈ Subgroup.normalizer (T : Set _) := by
        rw [hlπ]
        exact hn
      have hlM : (l : G) ∈ M := mem_M_of_image_mem_normalizer h hlnorm
      have hlnormV₀ : (l : G) ∈ Subgroup.normalizer (V₀ : Set G) := by
        rwa [← h.normalizer₀] at hlM
      have hlv₀ : (l : G) * v₀ * (l : G)⁻¹ ∈ V₀ :=
        (Subgroup.mem_normalizer_iff.1 hlnormV₀ v₀).1 hv₀V₀
      let y : ↥L := l * v₀L * l⁻¹
      have hyV₀ : (y : G) ∈ V₀ := by
        simpa only [y, Subgroup.coe_mul, Subgroup.coe_inv] using hlv₀
      have ht_eq : t = π y := by
        rw [← hnt]
        calc n * t₀ * n⁻¹ = π l * π v₀L * (π l)⁻¹ := by rw [← hlπ]
          _ = π (l * v₀L * l⁻¹) := by rw [map_mul, map_mul, map_inv]
          _ = π y := rfl
      rw [ht_eq]
      change π y ∈ imgK M V g V₀
      unfold imgK
      rw [Subgroup.mem_map]
      exact ⟨y, (Subgroup.mem_subgroupOf).2 hyV₀, rfl⟩
  intro v hv
  let vL : ↥L := ⟨v, (le_sup_left : V ≤ L) hv⟩
  have hmemT : π vL ∈ T := by
    unfold T imgK
    rw [Subgroup.mem_map]
    exact ⟨vL, hv, rfl⟩
  have hmemT₀ := hTle hmemT
  unfold T₀ imgK at hmemT₀
  rw [Subgroup.mem_map] at hmemT₀
  obtain ⟨y, hy, hyπ⟩ := hmemT₀
  have hyV₀ : (y : G) ∈ V₀ := (Subgroup.mem_subgroupOf).1 hy
  have hπinv : π (y⁻¹ * vL) = 1 := by
    rw [map_mul, map_inv, hyπ]
    group
  have hK : ((y⁻¹ * vL : ↥L) : G) ∈ KOf M V g :=
    (mk_eq_one_iff_mem_K M V g (y⁻¹ * vL)).1 hπinv
  have hK' : (y : G)⁻¹ * v ∈ KOf M V g := by
    simpa only [vL, Subgroup.coe_mul, Subgroup.coe_inv] using hK
  have hv_eq : v = (y : G) * ((y : G)⁻¹ * v) := by group
  rw [hv_eq]
  exact (V₀ ⊔ KOf M V g).mul_mem (Subgroup.mem_sup_left hyV₀) (Subgroup.mem_sup_right hK')

theorem conjV_le_conjV₀_sup_K (h : Hyp65 n M V₀ V g) (hV₀K : ¬ V₀ ≤ KOf M V g) :
    conjSubgroup V g ≤ conjSubgroup V₀ g ⊔ KOf M V g := by
  have hnot : ¬ conjSubgroup V₀ g ≤ KOf M V g :=
    fun hc => hV₀K ((conjV₀_le_K_iff h).1 hc)
  have hnot' : ¬ conjSubgroup V₀ g ≤ KOf (conjSubgroup M g) (conjSubgroup V g) g⁻¹ := by
    rwa [KOf_swap]
  have h := V_le_V₀_sup_K h.swap hnot'
  rwa [KOf_swap] at h

theorem LOf_le_normalizer_X (h : Hyp65 n M V₀ V g) (hV₀K : ¬ V₀ ≤ KOf M V g) :
    LOf V g ≤ normalizer ((V₀ ⊔ conjSubgroup V₀ g : Subgroup G) : Set G) := by
  let X : Subgroup G := V₀ ⊔ conjSubgroup V₀ g
  have hVU : V ≤ V₀ ⊔ UOf M V g :=
    V_le_V₀_sup_U_of_le_K h (V_le_V₀_sup_K h hV₀K)
  have hV₀norm : V₀ ≤ normalizer (X : Set G) :=
    (le_sup_left : V₀ ≤ X).trans Subgroup.le_normalizer
  have hV₀gnorm : conjSubgroup V₀ g ≤ normalizer (X : Set G) :=
    (le_sup_right : conjSubgroup V₀ g ≤ X).trans Subgroup.le_normalizer
  have hVcent : V ≤ centralizer (V₀ : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (h.elemAbelian.comm hv (h.le hw)).symm
  have hUnormV₀ : UOf M V g ≤ normalizer (V₀ : Set G) :=
    (inf_le_left : UOf M V g ≤ V).trans
      (hVcent.trans (Subgroup.centralizer_le_normalizer (V₀ : Set G)))
  have hUnormV₀g : UOf M V g ≤ normalizer (conjSubgroup V₀ g : Set G) := by
    rw [← conjSubgroup_normalizer V₀ g, ← h.normalizer₀]
    exact inf_le_right
  have hUnormX : UOf M V g ≤ normalizer (X : Set G) := by
    intro u hu
    exact CFSG.RankThree.GF2n.mem_normalizer_sup (hUnormV₀ hu) (hUnormV₀g hu)
  have hVnorm : V ≤ normalizer (X : Set G) :=
    hVU.trans (sup_le hV₀norm hUnormX)
  have hVgB : conjSubgroup V g ≤ conjSubgroup V₀ g ⊔ BOf M V g := by
    have hVgK : conjSubgroup V g ≤ conjSubgroup V₀ g ⊔
        KOf (conjSubgroup M g) (conjSubgroup V g) g⁻¹ := by
      rw [KOf_swap]
      exact conjV_le_conjV₀_sup_K h hV₀K
    have hh := V_le_V₀_sup_U_of_le_K h.swap hVgK
    rwa [UOf_swap] at hh
  have hBnormV₀ : BOf M V g ≤ normalizer (V₀ : Set G) := by
    rw [← h.normalizer₀]
    exact inf_le_right
  have hBcentV₀g : BOf M V g ≤ centralizer (conjSubgroup V₀ g : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (h.swap.elemAbelian.comm hb.1 (conjSubgroup_mono h.le g hx)).symm
  have hBnormV₀g : BOf M V g ≤ normalizer (conjSubgroup V₀ g : Set G) :=
    hBcentV₀g.trans (Subgroup.centralizer_le_normalizer (conjSubgroup V₀ g : Set G))
  have hBnormX : BOf M V g ≤ normalizer (X : Set G) := by
    intro b hb
    exact CFSG.RankThree.GF2n.mem_normalizer_sup (hBnormV₀ hb) (hBnormV₀g hb)
  have hVgnorm : conjSubgroup V g ≤ normalizer (X : Set G) :=
    hVgB.trans (sup_le hV₀gnorm hBnormX)
  exact sup_le hVnorm hVgnorm

theorem X_normal (h : Hyp65 n M V₀ V g) (hV₀K : ¬ V₀ ≤ KOf M V g) :
    ((V₀ ⊔ conjSubgroup V₀ g).subgroupOf (LOf V g)).Normal := by
  have hXL : V₀ ⊔ conjSubgroup V₀ g ≤ LOf V g :=
    sup_le (h.le.trans le_sup_left) ((conjSubgroup_mono h.le g).trans le_sup_right)
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hXL).2
    (LOf_le_normalizer_X h hV₀K)

theorem U_eq_Z0_sup_N (h : Hyp65 n M V₀ V g) (hV₀K : ¬ V₀ ≤ KOf M V g) :
    UOf M V g = Z0Of M V₀ g ⊔ NOf M V g := by
  apply le_antisymm
  · exact U_le_Z0_sup_N h h.genHyp h.exists_conj h.swapHyp
      (V_le_V₀_sup_U_of_le_K h (V_le_V₀_sup_K h hV₀K))
  · exact sup_le (Z0_le_U h) inf_le_left

theorem V_eq_V₀_sup_N (h : Hyp65 n M V₀ V g) (hV₀K : ¬ V₀ ≤ KOf M V g) :
    V = V₀ ⊔ NOf M V g := by
  apply le_antisymm
  · calc V ≤ V₀ ⊔ UOf M V g := V_le_V₀_sup_U_of_le_K h (V_le_V₀_sup_K h hV₀K)
      _ = V₀ ⊔ (Z0Of M V₀ g ⊔ NOf M V g) := by rw [U_eq_Z0_sup_N h hV₀K]
      _ ≤ V₀ ⊔ NOf M V g := by
          refine sup_le le_sup_left (sup_le ?_ le_sup_right)
          exact (inf_le_left : Z0Of M V₀ g ≤ V₀).trans le_sup_left
  · exact sup_le h.le ((inf_le_left : NOf M V g ≤ UOf M V g).trans
      (inf_le_left : UOf M V g ≤ V))

theorem conjV_eq_conjV₀_sup_N (h : Hyp65 n M V₀ V g) (hV₀K : ¬ V₀ ≤ KOf M V g) :
    conjSubgroup V g = conjSubgroup V₀ g ⊔ NOf M V g := by
  have hnot : ¬ conjSubgroup V₀ g ≤ KOf M V g :=
    fun hc => hV₀K ((conjV₀_le_K_iff h).1 hc)
  have hnot' : ¬ conjSubgroup V₀ g ≤ KOf (conjSubgroup M g) (conjSubgroup V g) g⁻¹ := by
    rwa [KOf_swap]
  have hh := V_eq_V₀_sup_N h.swap hnot'
  rwa [NOf_swap] at hh

theorem L_eq_X_sup_N (h : Hyp65 n M V₀ V g) (hV₀K : ¬ V₀ ≤ KOf M V g) :
    LOf V g = (V₀ ⊔ conjSubgroup V₀ g) ⊔ NOf M V g := by
  have hXL : V₀ ⊔ conjSubgroup V₀ g ≤ LOf V g :=
    sup_le (h.le.trans le_sup_left) ((conjSubgroup_mono h.le g).trans le_sup_right)
  have hNL : NOf M V g ≤ LOf V g :=
    ((inf_le_left : NOf M V g ≤ UOf M V g).trans
      (inf_le_left : UOf M V g ≤ V)).trans le_sup_left
  apply le_antisymm
  · rw [LOf]
    refine sup_le ?_ ?_
    · calc V = V₀ ⊔ NOf M V g := V_eq_V₀_sup_N h hV₀K
        _ ≤ (V₀ ⊔ conjSubgroup V₀ g) ⊔ NOf M V g := by
            refine sup_le ?_ le_sup_right
            exact (le_sup_left : V₀ ≤ V₀ ⊔ conjSubgroup V₀ g).trans le_sup_left
    · calc conjSubgroup V g = conjSubgroup V₀ g ⊔ NOf M V g :=
            conjV_eq_conjV₀_sup_N h hV₀K
        _ ≤ (V₀ ⊔ conjSubgroup V₀ g) ⊔ NOf M V g := by
            refine sup_le ?_ le_sup_right
            exact (le_sup_right : conjSubgroup V₀ g ≤ V₀ ⊔ conjSubgroup V₀ g).trans le_sup_left
  · exact sup_le hXL hNL

theorem rMV_le_mSub (h : Hyp65 n M V₀ V g) (hV₀K : ¬ V₀ ≤ KOf M V g) :
    rMV M V ≤ (mSub V₀ : ℕ∞) := by
  have hNV : NOf M V g ≤ V :=
    (inf_le_left : NOf M V g ≤ UOf M V g).trans (inf_le_left : UOf M V g ≤ V)
  have hcent : LOf V g ≤ centralizer (NOf M V g : Set G) :=
    Subgroup.le_centralizer_iff.2 (N_le_centralizer_L h)
  have hnc : ¬ centralizer (NOf M V g : Set G) ≤ M := by
    intro hle
    exact h.L_not_le_M (hcent.trans hle)
  have hrle : rMV M V ≤ (E3.mQuot V (NOf M V g) : ℕ∞) := by
    unfold rMV
    exact iInf₂_le (NOf M V g) ⟨hNV, hnc⟩
  have hVnormN : V₀ ≤ normalizer (NOf M V g : Set G) :=
    (h.le.trans (le_sup_left.trans hcent)).trans
      (Subgroup.centralizer_le_normalizer (NOf M V g : Set G))
  haveI : IsMulCommutative ↥V := h.elemAbelian.1
  haveI : ((NOf M V g).subgroupOf V).Normal := Subgroup.normal_of_isMulCommutative _
  let f : ↥V₀ → (↥V ⧸ ((NOf M V g).subgroupOf V)) :=
    fun v => QuotientGroup.mk (⟨(v : G), h.le v.2⟩ : ↥V)
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
    have hvsup : (v : G) ∈ V₀ ⊔ NOf M V g := by
      rw [← V_eq_V₀_sup_N h hV₀K]
      exact v.2
    have hvsup' : (v : G) ∈ ((V₀ ⊔ NOf M V g : Subgroup G) : Set G) := hvsup
    rw [Subgroup.coe_mul_of_left_le_normalizer_right V₀ (NOf M V g) hVnormN] at hvsup'
    have hvprod : (v : G) ∈ (V₀ : Set G) * (NOf M V g : Set G) := hvsup'
    obtain ⟨v₀, hv₀, n, hn, hvn⟩ := Set.mem_mul.1 hvprod
    refine ⟨⟨v₀, hv₀⟩, ?_⟩
    rw [QuotientGroup.eq]
    have hmem : (⟨(v₀ : G), h.le hv₀⟩ : ↥V)⁻¹ * v ∈ (NOf M V g).subgroupOf V := by
      rw [Subgroup.mem_subgroupOf]
      have hcalc : (v₀ : G)⁻¹ * (v : G) = n := by
        calc (v₀ : G)⁻¹ * (v : G) = (v₀ : G)⁻¹ * (v₀ * n) := by rw [hvn.symm]
          _ = n := by group
      have hmemN : (v₀ : G)⁻¹ * (v : G) ∈ NOf M V g := by
        rw [hcalc]
        exact hn
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk] using hmemN
    exact hmem
  have hcard := Nat.card_le_card_of_surjective f hsurj
  change (NOf M V g).relIndex V ≤ Nat.card ↥V₀ at hcard
  rw [s65_SixFiveK_mQuot hNV h.elemAbelian,
    card_eq_two_pow_mSub (h.elemAbelian.mono h.le).isPGroup] at hcard
  have hnat : E3.mQuot V (NOf M V g) ≤ mSub V₀ :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hcard
  calc rMV M V ≤ (E3.mQuot V (NOf M V g) : ℕ∞) := hrle
    _ ≤ (mSub V₀ : ℕ∞) := by exact_mod_cast hnat

theorem rMV_eq_mSub (h : Hyp65 n M V₀ V g) (hV₀K : ¬ V₀ ≤ KOf M V g) :
    rMV M V = (mSub V₀ : ℕ∞) := by
  exact le_antisymm (rMV_le_mSub h hV₀K) (mSub_le_rMV h)

theorem six_five_three (h : Hyp65 n M V₀ V g) :
    V₀ ≤ KOf M V g ∨
      (((V₀ ⊔ conjSubgroup V₀ g).subgroupOf (LOf V g)).Normal ∧
        LOf V g = (V₀ ⊔ conjSubgroup V₀ g) ⊔ NOf M V g ∧
        NOf M V g ≤ centralizer (LOf V g : Set G) ∧
        rMV M V = (mSub V₀ : ℕ∞)) := by
  by_cases hV₀K : V₀ ≤ KOf M V g
  · exact Or.inl hV₀K
  · exact Or.inr ⟨X_normal h hV₀K, L_eq_X_sup_N h hV₀K, N_le_centralizer_L h,
      rMV_eq_mSub h hV₀K⟩

end Certified

end Hyp65

end CFSG.LocalAnalysis.WeakClosure81
