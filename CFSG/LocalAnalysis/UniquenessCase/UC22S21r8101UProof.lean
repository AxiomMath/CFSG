module

public import CFSG.LocalAnalysis.UniquenessCase.GL3Excl.GL3ExclBasic
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101UIrr
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101UNorm
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101UInv
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101UFrat
import CFSG.LocalAnalysis.StronglyEmbedded.Normalizer
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4XD

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Matrix
open CFSG.RepresentationTheory (IsIrreducibleMatrixRep)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

namespace U4X

variable {D : Data G} {L K : Subgroup G} {n : ℕ}

theorem u81_normalizer_le
    (u : U4X D L K n) (hsp : IsStronglyPEmbedded n D.M) (hfour : 4 ≤ CFSG.Open.pRank n D.M)
    (h847 : F08.R847 D) (he : 3 < CFSG.Open.evenRank G) (h869 : F08.R869NS5 D)
    (hGL : GL3Excl.GL3Excl) {R B : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf (2 ^ n - 1) R D.M) (hBR : B ≤ R)
    (hRB : R ≤ centralizer (B : Set G)) (hBel : IsElemAbelian (2 ^ n - 1) B)
    (hΩ : ∀ x ∈ R, x ^ (2 ^ n - 1) = 1 → x ∈ B) (hr3 : CFSG.Open.pRank (2 ^ n - 1) D.M ≤ 3)
    (hC1 : CFSG.Open.pRank n (centralizer
      ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M))) ≤ 1)
    (hB0 : barImage D.M B ⊓ centralizer
      ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)) ≠ ⊥)
    (hdvd : ¬ n ∣ Nat.card (centralizer (B : Set G))) :
    normalizer (B : Set G) ≤ D.M := by
  by_contra hNM
  have hn : n.Prime := u.prime_n
  have hr := u.prime_r
  have hr2 := u.r_ne_two
  haveI : Fact n.Prime := ⟨hn⟩
  haveI : Fact (2 ^ n - 1).Prime := ⟨hr⟩
  haveI : NeZero (2 ^ n - 1) := ⟨hr.ne_zero⟩
  have hn2 : n ≠ 2 := by rcases u.hLS with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
  have hrp : 2 ^ n - 1 = 7 ∧ n = 3 ∨ 2 ^ n - 1 = 31 ∧ n = 5 := by
    rcases u.hLS with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Or.inl ⟨by norm_num, rfl⟩
    · exact Or.inr ⟨by norm_num, rfl⟩
  have hBM : B ≤ D.M := hBR.trans hR.le
  obtain ⟨b, hb⟩ := u.u81_exists_basis hr3 hR hBR hBel hΩ hB0
  have hCN : centralizer (B : Set G) ≤ normalizer (B : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hCM : centralizer (B : Set G) ≤ D.M :=
    (Subgroup.centralizer_le (Set.singleton_subset_iff.2 (hb.frame.mem 0))).trans
      ((CFSG.RankThree.PartOne.StrongP.centralizer_singleton_le_normalizer_zpowers _).trans
        (hb.normalizer_zpowers_le u hBM h847 he h869 0))
  obtain ⟨y, hyNM, hyo⟩ := u.u81_exists_mem_normalizer hsp hfour hR hBR hBel hΩ hC1
  have hY : IsStronglyPEmbedded n
      ((normalizer (B : Set G) ⊓ D.M).subgroupOf (normalizer (B : Set G))) := by
    refine hsp.subgroupOf hNM ?_
    have h := orderOf_dvd_natCard (⟨y, hyNM⟩ : ↥(normalizer (B : Set G) ⊓ D.M))
    rwa [Subgroup.orderOf_mk, hyo] at h
  have hkY : hb.frame.rho.ker ≤
      (normalizer (B : Set G) ⊓ D.M).subgroupOf (normalizer (B : Set G)) := by
    rw [hb.frame.ker_rho]
    exact fun m hm => Subgroup.mem_subgroupOf.2 ⟨m.2, hCM (Subgroup.mem_subgroupOf.1 hm)⟩
  have hpk : ¬ n ∣ Nat.card hb.frame.rho.ker := by
    rwa [hb.frame.ker_rho, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv]
  have hemb := u81_isStronglyPEmbedded_subgroupOf_range hY hb.frame.rho hkY hpk
  have hrH : ¬ (2 ^ n - 1) ∣ Nat.card
      (((normalizer (B : Set G) ⊓ D.M).subgroupOf (normalizer (B : Set G))).map
        hb.frame.rho) := by
    rw [← Subgroup.relIndex_ker]
    intro h
    obtain ⟨-, -, hidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1
      (hR.of_le (le_inf (hRB.trans hCN) hR.le) inf_le_right)
    refine hidx ?_
    rw [← Subgroup.relIndex_subgroupOf
      (inf_le_left : normalizer (B : Set G) ⊓ D.M ≤ normalizer (B : Set G))]
    refine h.trans (Subgroup.relIndex_dvd_of_le_left _ ?_)
    rw [hb.frame.ker_rho]
    exact fun m hm => Subgroup.mem_subgroupOf.2 (hRB (Subgroup.mem_subgroupOf.1 hm))
  have hmemY : ∀ {m : G} (h : m ∈ normalizer (B : Set G) ⊓ D.M),
      hb.frame.rho ⟨m, h.1⟩ ∈
        ((normalizer (B : Set G) ⊓ D.M).subgroupOf (normalizer (B : Set G))).map
          hb.frame.rho :=
    fun h => ⟨⟨_, h.1⟩, Subgroup.mem_subgroupOf.2 h, rfl⟩
  have hstab : ∀ g ∈ hb.frame.rho.range,
      (g : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ n - 1))) *ᵥ Pi.single 0 1 ∈
        Submodule.span (ZMod (2 ^ n - 1)) {(Pi.single 0 1 : Fin 3 → ZMod (2 ^ n - 1))} →
      g ∈ ((normalizer (B : Set G) ⊓ D.M).subgroupOf (normalizer (B : Set G))).map
        hb.frame.rho := by
    rintro _ ⟨m, rfl⟩ hm
    have h1 := hb.frame.conj_mem_zpowers_of_mulVec m 0 hm
    have hmN : (m : G) ∈ normalizer (zpowers (b 0) : Set G) :=
      Subgroup.mem_normalizer_fintype fun x hx => by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
        rw [← conj_zpow]
        exact zpow_mem h1 k
    exact hmemY ⟨m.2, hb.normalizer_zpowers_le u hBM h847 he h869 0 hmN⟩
  obtain ⟨t₁, ht₁, ht₁b⟩ := hb.exists_conj_zero u hBM
  obtain ⟨t₂, ht₂, ht₂b⟩ := hb.exists_conj_one u hBM
  have hd₁ : (hb.frame.rho ⟨t₁, ht₁.1⟩ : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ n - 1))) =
      Matrix.diagonal ![-1, 1, 1] := by
    rw [hb.frame.rho_eq_diagonal ⟨t₁, ht₁.1⟩ ht₁b]
    congr 1
    funext i
    fin_cases i <;> simp
  have hd₂ : (hb.frame.rho ⟨t₂, ht₂.1⟩ : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ n - 1))) =
      Matrix.diagonal ![1, -1, 1] := by
    rw [hb.frame.rho_eq_diagonal ⟨t₂, ht₂.1⟩ ht₂b]
    congr 1
    funext i
    fin_cases i <;> simp
  have hW : IsIrreducibleMatrixRep hb.frame.rho.range.subtype :=
    hb.frame.isIrreducible hr2 hd₁ hd₂ fun I hI hIu hle =>
      hNM (hle.trans (hb.normalizer_closure_le u hBM h847 he h869 hsp hfour hI hIu))
  obtain ⟨α, hα⟩ := hb.frame.exists_rho_eq_diagonal ⟨y, hyNM.1⟩ fun i =>
    hb.conj_mem_zpowers u hBM hyNM.2 hyNM.1 (by rw [hyo]; exact hn.odd_of_ne_two hn2) i
  have hyp : hb.frame.rho ⟨y, hyNM.1⟩ ^ n = 1 := by
    have h1 : (⟨y, hyNM.1⟩ : ↥(normalizer (B : Set G))) ^ n = 1 := by
      refine Subtype.ext ?_
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      have h := pow_orderOf_eq_one y
      rwa [hyo] at h
    rw [← map_pow, h1, map_one]
  by_cases hns : ∃ i j, α i ≠ α j
  · exact hGL (2 ^ n - 1) n hrp hb.frame.rho.range
      (((normalizer (B : Set G) ⊓ D.M).subgroupOf (normalizer (B : Set G))).map hb.frame.rho) hW
      (Subgroup.map_le_range _ _) hemb hrH hstab _ (hmemY ht₁) hd₁ _ (hmemY ht₂) hd₂ _
      (hmemY hyNM) hyp α hα hns
  push Not at hns
  have hcent : ∀ w : GL (Fin 3) (ZMod (2 ^ n - 1)),
      w * hb.frame.rho ⟨y, hyNM.1⟩ = hb.frame.rho ⟨y, hyNM.1⟩ * w := by
    intro w
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, hα,
      show Matrix.diagonal α = Matrix.scalar (Fin 3) (α 0) by
        rw [Matrix.scalar_apply]
        congr 1
        funext i
        exact hns i 0]
    exact (Matrix.scalar_commute (α 0) (fun r' => Commute.all _ _) _).eq.symm
  have hρy1 : hb.frame.rho ⟨y, hyNM.1⟩ ≠ 1 := by
    intro h1
    have h := orderOf_dvd_natCard
      (⟨y, (hb.frame.rho_eq_one_iff ⟨y, hyNM.1⟩).1 h1⟩ : ↥(centralizer (B : Set G)))
    rw [Subgroup.orderOf_mk, hyo] at h
    exact hdvd h
  obtain ⟨z, hz⟩ : ∃ z : ↥hb.frame.rho.range, (z : GL (Fin 3) (ZMod (2 ^ n - 1))) =
      hb.frame.rho ⟨y, hyNM.1⟩ := ⟨⟨_, ⟨⟨y, hyNM.1⟩, rfl⟩⟩, rfl⟩
  have hz1 : z ≠ 1 := fun h => hρy1 (by rw [← hz, h, Subgroup.coe_one])
  have hzp : z ^ n = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hz, hyp, Subgroup.coe_one])
  have hzY : z ∈ (((normalizer (B : Set G) ⊓ D.M).subgroupOf (normalizer (B : Set G))).map
      hb.frame.rho).subgroupOf hb.frame.rho.range :=
    Subgroup.mem_subgroupOf.2 (by rw [hz]; exact hmemY hyNM)
  have hCz := hemb.centralizer_le hz1 hzp hzY
  refine hNM fun m hm => ?_
  have hw : (⟨hb.frame.rho ⟨m, hm⟩, ⟨⟨m, hm⟩, rfl⟩⟩ : ↥hb.frame.rho.range) ∈
      (((normalizer (B : Set G) ⊓ D.M).subgroupOf (normalizer (B : Set G))).map
        hb.frame.rho).subgroupOf hb.frame.rho.range :=
    hCz (Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hz]
      exact hcent _)))
  obtain ⟨m', hm'Y, hm'⟩ := Subgroup.mem_subgroupOf.1 hw
  have hk : m'⁻¹ * ⟨m, hm⟩ ∈ hb.frame.rho.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hm']
    exact inv_mul_cancel _
  have hmY := Subgroup.mul_mem _ hm'Y (hkY hk)
  rw [mul_inv_cancel_left] at hmY
  exact (Subgroup.mem_subgroupOf.1 hmY).2

end U4X

end CFSG.LocalAnalysis.UniquenessCase.UC22
