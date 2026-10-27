module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCore
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock

public section

namespace CFSG.StandardType

namespace LayerPDiv

open CFSG.Assembly

theorem eq_bot_of_le_center {S : Type*} [Group S] [Finite S] {p : ℕ} [Fact p.Prime]
    (hperf : commutator S = ⊤) (P : Sylow p S) (hP : (P : Subgroup S) ≤ Subgroup.center S) :
    (P : Subgroup S) = ⊥ := by
  have hNC : Subgroup.normalizer ((P : Subgroup S) : Set S) ≤
      Subgroup.centralizer ((P : Subgroup S) : Set S) := fun n _ =>
    Subgroup.mem_centralizer_iff.mpr fun g hg => (Subgroup.mem_center_iff.mp (hP hg) n).symm
  have : IsMulCommutative (P : Subgroup S) :=
    ⟨⟨fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (hP b.2) a)⟩⟩
  have hcomp := MonoidHom.ker_transferSylow_isComplement' P hNC
  have hker : (MonoidHom.transferSylow P hNC).ker = ⊤ := by
    rw [eq_top_iff, ← hperf]
    exact Abelianization.commutator_subset_ker _
  rw [hker] at hcomp
  exact top_disjoint.mp hcomp.disjoint

theorem dvd_card_map_of_perfect {L G : Type*} [Group L] [Finite L] [Group G] (ψ : L →* G)
    (hker : ψ.ker ≤ Subgroup.center L) {S : Subgroup L} (hS : ⁅S, S⁆ = S) {p : ℕ}
    (hp : p.Prime) (hpS : p ∣ Nat.card S) : p ∣ Nat.card (S.map ψ) := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hnd
  obtain ⟨P⟩ : Nonempty (Sylow p S) := inferInstance
  have hperf : commutator S = ⊤ :=
    Group.isPerfect_def.mp (LayerFacts.ggIsPerfect_of_commutator_eq hS)
  have hPc : (P : Subgroup S) ≤ Subgroup.center S := by
    intro g hg
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨g, hg⟩
    have hgk : (g : L) ^ (p ^ k) = 1 := by
      simpa using congrArg (fun x : (P : Subgroup S) => ((x : S) : L)) hk
    have hmem : ψ (g : L) ∈ S.map ψ := Subgroup.mem_map_of_mem ψ g.2
    have h2 : orderOf (⟨ψ g, hmem⟩ : S.map ψ) ∣ Nat.card (S.map ψ) := orderOf_dvd_natCard _
    have h3 : orderOf (⟨ψ g, hmem⟩ : S.map ψ) ∣ p ^ k := by
      refine orderOf_dvd_of_pow_eq_one (Subtype.ext ?_)
      simp only [SubmonoidClass.mk_pow, OneMemClass.coe_one]
      rw [← map_pow, hgk, map_one]
    have hcop : (p ^ k).Coprime (Nat.card (S.map ψ)) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd)
    have h4 := Nat.eq_one_of_dvd_coprimes hcop h3 h2
    rw [orderOf_eq_one_iff] at h4
    have h5 : ψ (g : L) = 1 := by simpa using congrArg Subtype.val h4
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hker (MonoidHom.mem_ker.mpr h5)) y)
  have hdvd := P.dvd_card_of_dvd_card hpS
  rw [eq_bot_of_le_center hperf P hPc, Subgroup.card_bot] at hdvd
  exact hp.one_lt.ne' (Nat.dvd_one.mp hdvd)

theorem exists_eq_map_of_isComponentOf {L : Type*} [Group L] [Finite L] {G : Type*} [Group G]
    [Finite G] (ψ : L →* G) (hker : ψ.ker ≤ Subgroup.center L) {H : Subgroup G}
    {C₀ : Subgroup L} (hC₀H : C₀.map ψ ≤ H) (hnorm : ((C₀.map ψ).subgroupOf H).Normal)
    (hcomm : ⁅H, H⁆ ≤ C₀.map ψ) {β : Type*} (S : β → Subgroup L) (hSC : ∀ b, S b ≤ C₀)
    (hSn : ∀ b, ∀ c ∈ C₀, ∀ s ∈ S b, c * s * c⁻¹ ∈ S b) (hSq : ∀ b, CFSG.IsQuasisimple (S b))
    (hder : ∃ k, LayerFacts.ggDer C₀ k ≤ ⨆ b, S b) {K : Subgroup G}
    (hK : IsComponentOf K H) : ∃ b, K = (S b).map ψ := by
  have hcomp : ∀ b, IsComponentOf ((S b).map ψ) H := by
    intro b
    have hKq : CFSG.Assembly.IsQuasisimple ((S b).map ψ) := by
      refine (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
        (CFSG.LocalCores.isQuasisimple_map (hSq b) ψ fun hle => ?_)
      obtain ⟨a, a', haa⟩ := LayerFacts.exists_mul_ne_of_isQuasisimple (hSq b)
      exact haa (Subtype.ext (Subgroup.mem_center_iff.mp (hker (hle a.2)) a').symm)
    have hnormal : (((S b).map ψ).subgroupOf (C₀.map ψ)).Normal := by
      constructor
      intro x hx g
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      obtain ⟨s, hs, hsx⟩ := hx
      obtain ⟨c, hc, hcg⟩ := g.2
      refine ⟨c * s * c⁻¹, hSn b c hc s hs, ?_⟩
      simp only [map_mul, map_inv, hsx, hcg, Subgroup.coe_mul, Subgroup.coe_inv]
    exact ⟨(Subgroup.map_mono (hSC b)).trans hC₀H,
      IsSubnormal.step (Subgroup.map_mono (hSC b)) hnormal
        (IsSubnormal.step hC₀H hnorm (IsSubnormal.refl H)), hKq⟩
  obtain ⟨k, hk⟩ := hder
  have hKq := (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp
    hK.2.2
  have hKle : K ≤ (⨆ b, S b).map ψ :=
    calc K = LayerFacts.ggDer K (k + 1) :=
          (LayerFacts.ggDer_of_perfect (LayerFacts.ggCommutator_eq_of_isQuasisimple hKq) _).symm
      _ ≤ LayerFacts.ggDer H (k + 1) := LayerFacts.ggDer_mono hK.1 _
      _ = LayerFacts.ggDer ⁅H, H⁆ k := LayerFacts.ggDer_succ' H k
      _ ≤ LayerFacts.ggDer (C₀.map ψ) k := LayerFacts.ggDer_mono hcomm k
      _ = (LayerFacts.ggDer C₀ k).map ψ := (LayerFacts.map_ggDer ψ C₀ k).symm
      _ ≤ (⨆ b, S b).map ψ := Subgroup.map_mono hk
  by_contra hne
  have hc : ∀ b, (S b).map ψ ≤ Subgroup.centralizer (K : Set G) := by
    intro b
    rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hK (hcomp b) with h | h
    · exact absurd ⟨b, h⟩ hne
    · rw [Subgroup.commutator_comm] at h
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  have hKc : K ≤ Subgroup.centralizer (K : Set G) := by
    refine hKle.trans ?_
    rw [Subgroup.map_iSup]
    exact iSup_le hc
  obtain ⟨a, b, hab⟩ := LayerFacts.exists_mul_ne_of_isQuasisimple hKq
  exact hab (Subtype.ext (Subgroup.mem_centralizer_iff.mp (hKc b.2) a a.2))

theorem sq_sub_one_dvd_card_SL {D : Type*} [Field D] [Finite D] {d : ℕ} (hd : 2 ≤ d) :
    Nat.card D ^ 2 - 1 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin d) D) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by omega)]
  exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (Finset.mem_Icc.2 ⟨le_rfl, hd⟩)) _

theorem sq_sub_one_dvd_of_algebra {F D : Type*} [Field F] [Field D] [Algebra F D] [Finite D] :
    Nat.card F ^ 2 - 1 ∣ Nat.card D ^ 2 - 1 := by
  have : Finite F := Finite.of_injective _ (algebraMap F D).injective
  have : Module.Finite F D := inferInstance
  rw [Module.natCard_eq_pow_finrank (K := F) (V := D), ← pow_mul, mul_comm, pow_mul]
  simpa using Nat.sub_dvd_pow_sub_pow (Nat.card F ^ 2) 1 (Module.finrank F D)

theorem dvd_sq_sub_one {p q : ℕ} (h : p ∣ q - 1 ∨ p ∣ q + 1) : p ∣ q ^ 2 - 1 := by
  have e : q ^ 2 - 1 = (q + 1) * (q - 1) := by simpa using Nat.sq_sub_sq q 1
  rw [e]
  rcases h with h | h
  · exact h.mul_left _
  · exact h.mul_right _

end LayerPDiv

end CFSG.StandardType
