module

public import CFSG.Quasithin.EmptyFaithful.SzPS8Bender

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.GoldS146R CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SzPS8

section LiftSec

theorem commutator_self_of_simple {Γ : Type} [Group Γ] {K : Subgroup Γ} (hKs : IsSimpleGroup ↥K)
    (hKnc : ¬ IsMulCommutative ↥K) : ⁅K, K⁆ = K := by
  have h1 : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ := by
    rcases hKs.eq_bot_or_eq_top_of_normal ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ with h0 | h1
    · exfalso
      apply hKnc
      refine ⟨⟨fun a b => ?_⟩⟩
      have hle : (⊤ : Subgroup ↥K) ≤ Subgroup.centralizer ((⊤ : Subgroup ↥K) : Set ↥K) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp h0
      exact (Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_top a)) b
        (Subgroup.mem_top b)).symm
    · exact h1
  have := congrArg (Subgroup.map K.subtype) h1
  rwa [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype] at this

theorem exists_cComp_map_eq {Hg Γ : Type} [Group Hg] [Finite Hg] [Group Γ]
    (hspan : cCompSpan (⊤ : Subgroup Hg) = perfectCore (⊤ : Subgroup Hg))
    (ρ : Hg →* Γ) (hρ : Function.Surjective ρ)
    {K : Subgroup Γ} (hKn : K.Normal) (hKs : IsSimpleGroup ↥K) (hKnc : ¬ IsMulCommutative ↥K) :
    ∃ L ∈ cComp (⊤ : Subgroup Hg), L.map ρ = K := by
  classical
  have : Finite Γ := Finite.of_surjective ρ hρ
  by_contra hcon
  push Not at hcon
  set X : Subgroup Hg := K.comap ρ with hX
  have hXK : X.map ρ = K := Subgroup.map_comap_eq_self_of_surjective hρ K
  have hKperf : ⁅K, K⁆ = K := commutator_self_of_simple hKs hKnc
  have key : ∀ L ∈ cComp (⊤ : Subgroup Hg), L.map ρ ≤ Subgroup.centralizer (K : Set Γ) := by
    intro L hL
    set A : Subgroup Γ := L.map ρ with hA
    have hcomm : (⁅L, X⁆).map ρ = ⁅A, K⁆ := by rw [Subgroup.map_commutator, hXK]
    have hAK_le : ⁅A, K⁆ ≤ K := Subgroup.commutator_le_right A K
    have hKnormAK : K ≤ Subgroup.normalizer ((⁅A, K⁆ : Subgroup Γ) : Set Γ) :=
      le_sup_right.trans (A3.sup_le_normalizer_commutator A K)
    have hnorm : (⁅A, K⁆.subgroupOf K).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hAK_le).mpr hKnormAK
    have hAsub : IsSubnormal A ⊤ := A3.subnormal_top_map hρ (subnormal_of_mem_cComp hL)
    rcases hKs.eq_bot_or_eq_top_of_normal (⁅A, K⁆.subgroupOf K) with h0 | h1
    · have hbot : ⁅A, K⁆ = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have : (⟨x, hAK_le hx⟩ : ↥K) ∈ ⁅A, K⁆.subgroupOf K := hx
        rw [h0, Subgroup.mem_bot] at this
        simpa using congrArg Subtype.val this
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    · have hAKeq : ⁅A, K⁆ = K := by
        have := Subgroup.subgroupOf_eq_top.mp h1
        exact le_antisymm hAK_le this
      rcases cComp_commutator_dichotomy hL X with ⟨-, hsolv⟩ | hconj
      · exfalso
        have hs : Group.IsSolvable ↥K := by
          have hs' : Group.IsSolvable ↥((⁅L, X⁆).map ρ) :=
            haveI := hsolv
            Group.isSolvable_of_surjective (f := ρ.subgroupMap (⁅L, X⁆))
              (ρ.subgroupMap_surjective _)
          rw [hcomm, hAKeq] at hs'
          exact hs'
        exact hKnc ⟨⟨fun a b => (IsSimpleGroup.comm_iff_isSolvable.mpr hs) a b⟩⟩
      · have hAle : A ≤ K := by
          calc A ≤ conjClosure A K := by
                intro a ha
                exact Subgroup.subset_closure ⟨1, K.one_mem, a, ha, by simp⟩
            _ = ⁅A, K⁆ := by
                have := congrArg (Subgroup.map ρ) hconj
                rw [hcomm, A3.map_conjClosure, hXK] at this
                exact this.symm
            _ = K := hAKeq
        have hAsubK : IsSubnormal A K := A3.subnormal_of_le_of_le hAsub hAle le_top
        by_cases hAbot : A = ⊥
        · rw [hAbot]; exact bot_le
        · exfalso
          have : A = K := eq_of_isSubnormal_of_simple (A := K) hAsubK hAbot
          exact hcon L hL this
  have hall : K ≤ Subgroup.centralizer (K : Set Γ) := by
    have h1 : K ≤ perfectCore (⊤ : Subgroup Γ) := le_perfectCore_of_perfect le_top hKperf
    have h2 : (perfectCore (⊤ : Subgroup Hg)).map ρ = perfectCore (⊤ : Subgroup Γ) := by
      rw [map_perfectCore, Subgroup.map_top_of_surjective ρ hρ]
    rw [← h2, ← hspan] at h1
    unfold cCompSpan at h1
    rw [(Subgroup.gc_map_comap ρ).l_sSup] at h1
    exact h1.trans (iSup₂_le fun L hL => key L hL)
  refine hKnc ⟨⟨fun a b => ?_⟩⟩
  have := Subgroup.mem_centralizer_iff.mp (hall a.2) b b.2
  exact Subtype.ext this.symm

end LiftSec

section FixSec

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

theorem eq_bot_of_normal_fix (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M))
    {g : G} (hg : GoodElt128 T L g) (D : HatModel T M) {a : G} (haV : a ∈ VZ T M)
    (haZ : a ∉ quasithinOmegaOneCenter T)
    {N : Subgroup (D.V ≃ₗ[ZMod 2] D.V)}
    (hNn : ∀ γ ∈ D.img (mcOf T), ∀ n ∈ N, γ * n * γ⁻¹ ∈ N)
    (hfix : ∀ n ∈ N, n (D.π a) = D.π a) : N = ⊥ := by
  have hyp := h.lemma_12_8_12_three hU hg D haV haZ
  have hall : ∀ n ∈ N, ∀ v : D.V, n v = v := by
    intro n hn
    have hsub : Submodule.span (ZMod 2) (MulAction.orbit (D.img (mcOf T)) (D.π a)) ≤
        LinearMap.ker (n.toLinearMap - LinearMap.id) := by
      rw [Submodule.span_le]
      rintro _ ⟨γ, rfl⟩
      have hγn : (γ : D.V ≃ₗ[ZMod 2] D.V)⁻¹ * n * (γ : D.V ≃ₗ[ZMod 2] D.V) ∈ N := by
        have := hNn (γ : D.V ≃ₗ[ZMod 2] D.V)⁻¹ (Subgroup.inv_mem _ γ.2) n hn
        simpa [mul_assoc] using this
      have h1 := hfix _ hγn
      have h2 : (γ : D.V ≃ₗ[ZMod 2] D.V)⁻¹
          (n ((γ : D.V ≃ₗ[ZMod 2] D.V) (D.π a))) = D.π a := h1
      show n ((γ : D.V ≃ₗ[ZMod 2] D.V) (D.π a)) - (γ : D.V ≃ₗ[ZMod 2] D.V) (D.π a) = 0
      have h3 : n ((γ : D.V ≃ₗ[ZMod 2] D.V) (D.π a)) = (γ : D.V ≃ₗ[ZMod 2] D.V) (D.π a) := by
        have := congrArg (fun w => (γ : D.V ≃ₗ[ZMod 2] D.V) w) h2
        simpa using this
      rw [h3, sub_self]
    intro v
    have hv : v ∈ LinearMap.ker (n.toLinearMap - LinearMap.id) := by
      apply hsub
      rw [hyp.span_orbit]
      exact Submodule.mem_top
    have := LinearMap.mem_ker.mp hv
    simpa [sub_eq_zero] using this
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  ext v
  exact hall n hn v

end FixSec

section Glue

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

@[expose] noncomputable def rhoΓ (h : Hyp1281Two G T M (yOfL22 T M)) (D : HatModel T M) :
    ↥(mcOf T) →* ↥(D.img (mcOf T)) :=
  (S143V.rhoH h D).codRestrict (D.img (mcOf T)) (fun x => by
    rw [← S143V.range_rhoH h D]
    exact ⟨x, rfl⟩)

theorem rhoΓ_surjective (h : Hyp1281Two G T M (yOfL22 T M)) (D : HatModel T M) :
    Function.Surjective (rhoΓ h D) := by
  intro γ
  have : (γ : D.V ≃ₗ[ZMod 2] D.V) ∈ (S143V.rhoH h D).range := by
    rw [S143V.range_rhoH h D]
    exact γ.2
  obtain ⟨x, hx⟩ := this
  exact ⟨x, Subtype.ext hx⟩

theorem rhoΓ_eq_one_of_mem_pCoreOf (h : Hyp1281Two G T M (yOfL22 T M)) (D : HatModel T M)
    {x : ↥(mcOf T)} (hx : (x : G) ∈ pCoreOf 2 (mcOf T)) : rhoΓ h D x = 1 := by
  have h4 := Hyp1281Two.lemma_12_8_4_four h h.isHz_centralizer
  have hx' : (x : G) ∈ centralizerMod (quasithinOmegaOneCenter T) (mcOf T) (uOfL22 T M) :=
    h4.ge hx
  have hker : x ∈ (S143V.rhoH h D).ker :=
    (S143V.mem_ker_rhoH h D x).mpr ⟨x.2, normalizer_le_normalizer_centerOf _
      (h.g1_le_normalizer_uOfL22 x.2),
      fun u hu => h.omegaOneCenter_le_centerOf_uOfL22 (hx'.2.2 u hu)⟩
  apply Subtype.ext
  exact MonoidHom.mem_ker.mp hker

end Glue

section Glue2

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem false_of_good_lift
    (hyp : Hyp1421 G T M) (hnot : ¬ SixModels G) (hnab : ¬ IsMulCommutative ↥(uOfL22 T M))
    (h11 : StageLemma14111) (h113 : StageLemma14113)
    (hE22 : E2.E22StatementNoN) (hF : FieldOne1432) (D : HatModel T M)
    {Kd : Subgroup ↥(D.img (mcOf T))} (hKn : Kd.Normal) (hKnc : ¬ IsMulCommutative ↥Kd)
    {m : ℕ} (hm : 2 ≤ m) {L : Subgroup G} (hLH : L ≤ mcOf T) (hLc : L ∈ cComp (L ⊔ T))
    (hTN : T ≤ Subgroup.normalizer (L : Set G))
    (hLρ : (L.subgroupOf (mcOf T)).map (rhoΓ (hyp.hyp1281Two_of_inputs h11 h113) D) = Kd)
    (hsimp : IsSimpleGroup (KBar L)) (hBen : fusionIsBenderGroup (KBar L))
    (hcard : Nat.card (KBar L) = ordL2 m)
    (hB : L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ≤ M) : False := by
  classical
  have h1281 : Hyp1281Two G T M (yOfL22 T M) := hyp.hyp1281Two_of_inputs h11 h113
  obtain ⟨a, haV, haZ⟩ := h1281.exists_mem_VZ_not_mem
  obtain ⟨g, hg⟩ := h1281.exists_goodElt_L
  have hH : pCoreOf 2 (mcOf T) ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hyp.mc_max.1
  have hTH : T ≤ mcOf T := h1281.almostSpecialHyp_g1.T_le_H
  set ρ := rhoΓ h1281 D with hρ
  have hLTH : L ⊔ T ≤ mcOf T := sup_le hLH hTH
  have hsylH : IsSylowTwoOf T (mcOf T) := isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hTH
  have hInH : InH T (L ⊔ T) := by
    refine ⟨le_sup_right, ?_⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h1 : pCoreOf 2 (mcOf T) ≤ pCoreOf 2 (L ⊔ T) :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_two_le_of_isSylowTwoOf hsylH).trans le_sup_right)
        (hLTH.trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
    intro h0
    exact hH (le_bot_iff.mp (h0 ▸ h1))
  have hLM : ¬ L ≤ M := by
    intro hLM
    have hN := eq_bot_of_normal_fix h1281 hnab hg D haV haZ
      (N := Kd.map (D.img (mcOf T)).subtype)
      (fun γ hγ n hn => by
        obtain ⟨k, hk, rfl⟩ := hn
        exact ⟨(⟨γ, hγ⟩ : ↥(D.img (mcOf T))) * k * (⟨γ, hγ⟩ : ↥(D.img (mcOf T)))⁻¹,
          hKn.conj_mem k hk _, rfl⟩)
      (fun n hn => by
        obtain ⟨k, hk, rfl⟩ := hn
        rw [← hLρ] at hk
        obtain ⟨l, hl, rfl⟩ := hk
        exact S143V.rhoH_fix_of_mem_M h1281 hnab D haV haZ
          (hLM (Subgroup.mem_subgroupOf.mp hl)))
    apply hKnc
    have hKbot : Kd = ⊥ := by
      rw [eq_bot_iff]
      intro k hk
      have : (k : D.V ≃ₗ[ZMod 2] D.V) ∈ Kd.map (D.img (mcOf T)).subtype := ⟨k, hk, rfl⟩
      rw [hN, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      exact Subtype.ext this
    rw [hKbot]
    infer_instance
  have hHTM : IsHTM T M (L ⊔ T) := ⟨hInH, fun h => hLM (le_sup_left.trans h)⟩
  exact false_of_bender_borel hE22 hF hyp hnot hHTM hLc hTN hsimp hBen hm hcard hB

theorem false_of_normal_component
    (hyp : Hyp1421 G T M) (hnot : ¬ SixModels G) (hnab : ¬ IsMulCommutative ↥(uOfL22 T M))
    (h11 : StageLemma14111) (h113 : StageLemma14113) (h37 : A37ForSQTK) (h39 : A39ForSQTK)
    (hE22 : E2.E22StatementNoN) (hF : FieldOne1432) (D : HatModel T M)
    {Kd : Subgroup ↥(D.img (mcOf T))} (hKn : Kd.Normal) (hKs : IsSimpleGroup ↥Kd)
    (hKnc : ¬ IsMulCommutative ↥Kd) {m : ℕ} (hm : 2 ≤ m)
    (hKbar : ∀ L : Subgroup G, L ∈ cComp (mcOf T) → T ≤ Subgroup.normalizer (L : Set G) →
      (L.subgroupOf (mcOf T)).map (rhoΓ (hyp.hyp1281Two_of_inputs h11 h113) D) = Kd →
      IsSimpleGroup (KBar L) ∧ fusionIsBenderGroup (KBar L) ∧ Nat.card (KBar L) = ordL2 m ∧
        L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ≤ M) : False := by
  classical
  have h1281 : Hyp1281Two G T M (yOfL22 T M) := hyp.hyp1281Two_of_inputs h11 h113
  have hH : pCoreOf 2 (mcOf T) ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hyp.mc_max.1
  have hTH : T ≤ mcOf T := h1281.almostSpecialHyp_g1.T_le_H
  have hspanH : cCompSpan (mcOf T) = perfectCore (mcOf T) :=
    lemma_1_2_1_one hyp.qtke hyp.simple hyp.nonabelian h39 hH
  have hspanTop : cCompSpan (⊤ : Subgroup ↥(mcOf T)) = perfectCore (⊤ : Subgroup ↥(mcOf T)) := by
    apply Subgroup.map_injective (mcOf T).subtype_injective
    rw [← cCompSpan_eq_map_subtype, hspanH, map_perfectCore, Subgroup.map_top,
      Subgroup.range_subtype]
  set ρ := rhoΓ h1281 D with hρ
  obtain ⟨L', hL', hL'ρ⟩ := exists_cComp_map_eq hspanTop ρ (rhoΓ_surjective h1281 D) hKn hKs hKnc
  set L : Subgroup G := L'.map (mcOf T).subtype with hLdef
  have hL : L ∈ cComp (mcOf T) := map_subtype_mem_cComp hL'
  have hLsub : L.subgroupOf (mcOf T) = L' :=
    Subgroup.comap_map_eq_self_of_injective (mcOf T).subtype_injective L'
  have hLρ : (L.subgroupOf (mcOf T)).map ρ = Kd := by rw [hLsub]; exact hL'ρ
  have hLH : L ≤ mcOf T := le_of_mem_cComp hL
  have hTN : T ≤ Subgroup.normalizer (L : Set G) := by
    intro t ht
    by_contra htn
    set L₂ : Subgroup G := L.map (MulAut.conj t).toMonoidHom with hL₂def
    have hL₂ : L₂ ∈ cComp (mcOf T) := map_conj_mem_cComp hL (hTH ht)
    have hne : L ≠ L₂ := fun hLL => htn (A38.map_conj_eq_iff.mp hLL.symm)
    have hc2 := lemma_1_2_1_two hyp.qtke hyp.simple hyp.nonabelian h37 hH hL hL₂ hne
    have hcomm : ⁅L, L₂⁆ ≤ pCoreOf 2 (mcOf T) := hc2.1.trans hc2.2
    have hL₂H : L₂ ≤ mcOf T := le_of_mem_cComp hL₂
    set t' : ↥(mcOf T) := ⟨t, hTH ht⟩ with ht'
    have hL₂ρ : (L₂.subgroupOf (mcOf T)).map ρ = Kd := by
      apply le_antisymm
      · rintro _ ⟨y, hy, rfl⟩
        obtain ⟨l, hl, hly⟩ := hy
        have hlH : l ∈ mcOf T := hLH hl
        have hly' : t * l * t⁻¹ = (y : G) := by simpa [MulAut.conj_apply] using hly
        have hyeq : y = t' * ⟨l, hlH⟩ * t'⁻¹ := by
          apply Subtype.ext
          simp [ht', hly']
        have hρl : ρ ⟨l, hlH⟩ ∈ Kd := by
          have : ρ ⟨l, hlH⟩ ∈ (L.subgroupOf (mcOf T)).map ρ :=
            ⟨⟨l, hlH⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
          rwa [hLρ] at this
        rw [hyeq, map_mul, map_mul, map_inv]
        exact hKn.conj_mem _ hρl _
      · intro k hk
        have hk' : (ρ t')⁻¹ * k * (ρ t') ∈ Kd := by
          have := hKn.conj_mem k hk (ρ t')⁻¹
          simpa [mul_assoc] using this
        rw [← hLρ] at hk'
        obtain ⟨l, hl, hlk⟩ := hk'
        refine ⟨t' * l * t'⁻¹, ?_, ?_⟩
        · refine Subgroup.mem_subgroupOf.mpr ⟨(l : G), Subgroup.mem_subgroupOf.mp hl, ?_⟩
          simp [ht', MulAut.conj_apply]
        · rw [map_mul, map_mul, map_inv, hlk]
          group
    apply hKnc
    refine ⟨⟨fun k₁ k₂ => ?_⟩⟩
    have hk₁ : (k₁ : ↥(D.img (mcOf T))) ∈ (L.subgroupOf (mcOf T)).map ρ := by
      rw [hLρ]; exact k₁.2
    have hk₂ : (k₂ : ↥(D.img (mcOf T))) ∈ (L₂.subgroupOf (mcOf T)).map ρ := by
      rw [hL₂ρ]; exact k₂.2
    obtain ⟨a₁, ha₁, hρa₁⟩ := hk₁
    obtain ⟨a₂, ha₂, hρa₂⟩ := hk₂
    have hcg : (⁅a₁, a₂⁆ : ↥(mcOf T)) ∈ (pCoreOf 2 (mcOf T)).subgroupOf (mcOf T) := by
      refine Subgroup.mem_subgroupOf.mpr (hcomm ?_)
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp ha₁)
        (Subgroup.mem_subgroupOf.mp ha₂)
    have h1 : ρ ⁅a₁, a₂⁆ = 1 :=
      rhoΓ_eq_one_of_mem_pCoreOf h1281 D (Subgroup.mem_subgroupOf.mp hcg)
    simp only [commutatorElement_def, map_mul, map_inv, hρa₁, hρa₂] at h1
    apply Subtype.ext
    show (k₁ : ↥(D.img (mcOf T))) * (k₂ : ↥(D.img (mcOf T))) =
      (k₂ : ↥(D.img (mcOf T))) * (k₁ : ↥(D.img (mcOf T)))
    calc (k₁ : ↥(D.img (mcOf T))) * (k₂ : ↥(D.img (mcOf T))) =
        ((k₁ : ↥(D.img (mcOf T))) * (k₂ : ↥(D.img (mcOf T))) * (k₁ : ↥(D.img (mcOf T)))⁻¹ *
          (k₂ : ↥(D.img (mcOf T)))⁻¹) * ((k₂ : ↥(D.img (mcOf T))) * (k₁ : ↥(D.img (mcOf T)))) := by
          group
      _ = (k₂ : ↥(D.img (mcOf T))) * (k₁ : ↥(D.img (mcOf T))) := by rw [h1, one_mul]
  have hLTH : L ⊔ T ≤ mcOf T := sup_le hLH hTH
  have hLc : L ∈ cComp (L ⊔ T) := cComp_mem_of_le hL le_sup_left hLTH
  obtain ⟨hsimp, hBen, hcard, hB⟩ := hKbar L hL hTN hLρ
  exact false_of_good_lift hyp hnot hnab h11 h113 hE22 hF D hKn hKnc hm hLH hLc hTN hLρ hsimp
    hBen hcard hB

end Glue2

end SzPS8

end CFSG.Quasithin
