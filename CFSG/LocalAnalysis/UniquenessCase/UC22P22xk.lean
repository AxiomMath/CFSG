module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22xj
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22t
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22xf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)
open CFSG.Open.StatedAPI

variable {G : Type} [Group G] [Finite G]

namespace P22x

theorem mem_normalizer_mbarImage (D : Data G) {x : G} (hxM : x ∈ D.M) :
    (QuotientGroup.mk ⟨x, hxM⟩ : MBar D.M D.U) ∈
      normalizer ((mbarImage D.M D.U (proofN D) : Subgroup (MBar D.M D.U)) : Set (MBar D.M D.U)) := by
  have h1 : (⟨x, hxM⟩ : ↥D.M) ∈
      normalizer (((proofN D).subgroupOf D.M : Subgroup ↥D.M) : Set ↥D.M) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    exact Subgroup.mem_normalizer_iff.1 (uc22p22t_M_le_normalizer_jOf D hxM) (h : G)
  exact Subgroup.le_normalizer_map (QuotientGroup.mk' (kerAct D.M D.U).normalCore)
    (Subgroup.mem_map_of_mem _ h1)

theorem card_dvd_proofN {D : Data G} {Y : Subgroup (MBar D.M D.U)}
    (hY : Y ≤ mbarImage D.M D.U (proofN D)) : Nat.card ↥Y ∣ Nat.card ↥(proofN D) := by
  have h1 : Nat.card ↥Y ∣ Nat.card ↥(mbarImage D.M D.U (proofN D)) := Subgroup.card_dvd_of_le hY
  have h2 : Nat.card ↥(mbarImage D.M D.U (proofN D)) ∣ Nat.card ↥((proofN D).subgroupOf D.M) :=
    Subgroup.card_map_dvd _ _
  have h3 : Nat.card ↥((proofN D).subgroupOf D.M) = Nat.card ↥(proofN D) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (uc22p22e_jOf_le_self D.M)).toEquiv
  exact h1.trans (h3 ▸ h2)

end P22x

open P22x

theorem uc22p22x_natpfact_of (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch)
    (h3 : S22_3_3 D Ch) (h51 : S22_5_1 D Ch) : NatPFact D Ch := by
  classical
  intro hH c p hp hpN x hxM hxp _hxJ hxE y hy
  obtain ⟨hpP, -⟩ := D.sig_prime p hp
  obtain ⟨m, Nb, hNb⟩ := h2 hH c
  obtain ⟨Umod, _, _, _, e, ρ, hc⟩ :=
    uc22br4_exists_conjModule D.M D.U (uc22p22xf_hV D) (uc22p22xf_hel D)
  have d := natDec_of_data D Ch h3 h51 hH c hNb e ρ hc
  have hV := uc22p22xf_hV D
  have hJM : jOf D.T ≤ D.M := (uc22p22e_jOf_le_self D.T).trans D.sylowM.le
  set Nbar : Subgroup (MBar D.M D.U) := mbarImage D.M D.U (proofN D) with hNbar
  set Q : Subgroup (MBar D.M D.U) := mbarImage D.M D.U (jOf D.T) with hQdef
  have hQN : Q ≤ Nbar := mbarImage_mono D.M D.U (uc22p22e_jOf_le D.sylowM)
  have hQ2 : IsPGroup 2 Q :=
    ((D.sylowM.isPGroup.to_le (uc22p22e_jOf_le_self D.T)).comap_subtype (K := D.M)).map _
  have himg : ∀ w ∈ natI ρ Nbar, (∀ a ∈ Q, ρ a w - w ∈ natC ρ Nbar) → ∀ a ∈ Q, ρ a w = w :=
    fun w hw hwC a ha => uc22p22xf_imgEI_of D Ch h2 h3 h51 hH c Umod e ρ hc w hw hwC a ha
  set xb : MBar D.M D.U := QuotientGroup.mk ⟨x, hxM⟩ with hxb
  have ht := mem_normalizer_mbarImage D hxM
  have hfix : ∀ v ∈ natI ρ Nbar ⊓ fixSub ρ Q, ρ xb v = v := by
    intro v hv
    have hvfix : v ∈ fixSub ρ Q := hv.2
    rw [hQdef, fixSub_mbarImage hV e ρ hc hJM] at hvfix
    have hz : iota e v ∈ centralizer ((jOf D.T : Subgroup G) : Set G) := mem_bsub.1 hvfix
    have hzE : iota e v ∈ proofE D :=
      uc22p22e_mem_omegaZJ'.2 ⟨uc22p22xf_UleT D (iota_mem e v),
        fun j hj => Subgroup.mem_centralizer_iff.1 hz j hj,
        (uc22p22xf_hel D).2 _ (iota_mem e v)⟩
    apply iota_injective e
    rw [hxb, iota_rho hV e ρ hc ⟨x, hxM⟩ v]
    exact hxE _ hzE
  obtain ⟨k, hk⟩ : ∃ k : ℕ, xb ^ (p ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hxp ⟨x, Subgroup.mem_zpowers x⟩
    refine ⟨k, ?_⟩
    have h1 : x ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have h2 : (⟨x, hxM⟩ : ↥D.M) ^ (p ^ k) = 1 := Subtype.ext (by simpa using h1)
    rw [hxb, ← QuotientGroup.mk_pow, h2]
    rfl
  have hpF : ∀ i, ¬ p ∣ Nat.card ↥(Nb i) := fun i hdvd =>
    hpN ⟨hpP, hdvd.trans (card_dvd_proofN (d.le i))⟩
  have hcomm := d.commute_of_fixed hQN hQ2 himg ht hfix hpP hpF hk
  have hyM : y ∈ D.M := hJM hy
  have hyb : (QuotientGroup.mk ⟨y, hyM⟩ : MBar D.M D.U) ∈ Nbar :=
    hQN (Subgroup.mem_map_of_mem _ (show (⟨y, hyM⟩ : ↥D.M) ∈ (jOf D.T).subgroupOf D.M from hy))
  have h4 := hcomm _ hyb
  rw [← hxb] at h4
  have hw : (QuotientGroup.mk (⟨x, hxM⟩ * ⟨y, hyM⟩ * ⟨x, hxM⟩⁻¹ * ⟨y, hyM⟩⁻¹ : ↥D.M) :
      MBar D.M D.U) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv]
    change xb * QuotientGroup.mk ⟨y, hyM⟩ * xb⁻¹ * (QuotientGroup.mk ⟨y, hyM⟩)⁻¹ = 1
    rw [h4]
    group
  have hker := (QuotientGroup.eq_one_iff _).1 hw
  have hker' : (⟨x, hxM⟩ * ⟨y, hyM⟩ * ⟨x, hxM⟩⁻¹ * ⟨y, hyM⟩⁻¹ : ↥D.M) ∈ kerAct D.M D.U :=
    Subgroup.normalCore_le _ hker
  exact hker'

end CFSG.LocalAnalysis.UniquenessCase.UC22
