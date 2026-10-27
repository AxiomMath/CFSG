module

public import CFSG.Quasithin.Background.GoldschmidtS146RPair
public import CFSG.Quasithin.H13.L32NLem14324o

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.GoldS146R

namespace L14324

section Lift

theorem commutator_self_of_simple' {Γ : Type} [Group Γ] {K : Subgroup Γ}
    (hKs : IsSimpleGroup ↥K) (hKnc : ¬ IsMulCommutative ↥K) : ⁅K, K⁆ = K := by
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

theorem exists_cComp_map_eq' {Hg Γ : Type} [Group Hg] [Finite Hg] [Group Γ]
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
  have hKperf : ⁅K, K⁆ = K := commutator_self_of_simple' hKs hKnc
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

end Lift

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def rhoH {T V : Subgroup G} (D : HatModelU (fsuU T V)) :
    ↥(l32nH T V) →* ↥(D.img (l32nH T V)) :=
  (D.ρ.comp (Subgroup.inclusion (L14332.l32nH_le_normalizer_fsuU T V))).codRestrict
    (D.img (l32nH T V)) fun x => L128A.HatU.rho_mem_img D x.2 _

omit [Finite G] in
theorem coe_rhoH {T V : Subgroup G} (D : HatModelU (fsuU T V)) (x : ↥(l32nH T V)) :
    ((rhoH D x : ↥(D.img (l32nH T V))) : D.V ≃ₗ[ZMod 2] D.V) =
      D.ρ ⟨x, L14332.l32nH_le_normalizer_fsuU T V x.2⟩ := rfl

omit [Finite G] in
theorem rhoH_surjective {T V : Subgroup G} (D : HatModelU (fsuU T V)) :
    Function.Surjective (rhoH D) := by
  rintro ⟨γ, hγ⟩
  obtain ⟨h, hh, hhN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
  exact ⟨⟨h, hh⟩, rfl⟩

namespace Ctx5

variable {T L V V₂ : Subgroup G} {g a : G} {D : HatModelU (fsuU T V)}
  (C : Ctx5 G T L V V₂ g a D)
include C

theorem pCoreOf_ne : pCoreOf 2 (l32nH T V) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥(fsuV1 T V) := IsPGroup.of_card (n := 1) (by rw [C.card_V1]; norm_num)
  have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (Subgroup.le_normalizer : fsuV1 T V ≤ l32nH T V) le_rfl hp
  intro hbot
  rw [hbot, le_bot_iff] at hle
  have := C.card_V1
  rw [hle, Subgroup.card_bot] at this
  norm_num at this

theorem rho_eq_one_of_pCoreOf {x : G} (hx : x ∈ pCoreOf 2 (l32nH T V))
    (hxN : x ∈ Subgroup.normalizer (fsuU T V : Set G)) : D.ρ ⟨x, hxN⟩ = 1 := by
  rw [← C.q_tilde] at hx
  exact (L128A.HatU.rho_eq_one_iff D ⟨x, hxN⟩).mpr fun u hu => C.V1_le_zU (hx.2.2 u hu)

theorem exists_comp (h37 : A37ForSQTK) (h39 : A39ForSQTK)
    (M : S8Five.Model5 (D.img (l32nH T V))) :
    ∃ K ∈ cComp (l32nH T V), D.img K = M.A ∧
      l32nH T V ≤ Subgroup.normalizer (K : Set G) := by
  classical
  have hH := C.pCoreOf_ne
  have hspanH : cCompSpan (l32nH T V) = perfectCore (l32nH T V) :=
    lemma_1_2_1_one C.hyp.fsu.qtke C.hyp.fsu.simple C.hyp.fsu.nonabelian h39 hH
  have hspanTop : cCompSpan (⊤ : Subgroup ↥(l32nH T V)) =
      perfectCore (⊤ : Subgroup ↥(l32nH T V)) := by
    apply Subgroup.map_injective (l32nH T V).subtype_injective
    rw [← cCompSpan_eq_map_subtype, hspanH, map_perfectCore, Subgroup.map_top,
      Subgroup.range_subtype]
  have : IsSimpleGroup ↥M.A := M.isSimpleGroup_A
  set Kd : Subgroup ↥(D.img (l32nH T V)) := M.A.subgroupOf (D.img (l32nH T V)) with hKd
  have hKn : Kd.Normal := ⟨fun n hn γ => M.A_normal γ.2 hn⟩
  have hKs : IsSimpleGroup ↥Kd := (Subgroup.subgroupOfEquivOfLe M.A_le).isSimpleGroup
  have ha9A : M.ψ S8Five.a9 ∈ M.A :=
    ⟨S8Five.a9, Equiv.Perm.mem_alternatingGroup.mpr S8Five.e9_facts.2.2.2.1, rfl⟩
  have hn1A : M.ψ S8Five.n1 ∈ M.A :=
    ⟨S8Five.n1, Equiv.Perm.mem_alternatingGroup.mpr S8Five.e9_facts.2.2.2.2.2.1, rfl⟩
  have hnc : M.ψ S8Five.a9 * M.ψ S8Five.n1 ≠ M.ψ S8Five.n1 * M.ψ S8Five.a9 := by
    rw [← map_mul, ← map_mul]
    intro h
    exact absurd (M.ψ_injective h) (by decide)
  have hKnc : ¬ IsMulCommutative ↥Kd := by
    rintro ⟨⟨hc⟩⟩
    apply hnc
    have := hc ⟨⟨_, M.A_le ha9A⟩, ha9A⟩ ⟨⟨_, M.A_le hn1A⟩, hn1A⟩
    exact congrArg (fun x : ↥Kd => ((x : ↥(D.img (l32nH T V))) : D.V ≃ₗ[ZMod 2] D.V)) this
  obtain ⟨L', hL', hL'ρ⟩ := exists_cComp_map_eq' hspanTop (rhoH D) (rhoH_surjective D) hKn hKs
    hKnc
  set K : Subgroup G := L'.map (l32nH T V).subtype with hKdef
  have hK : K ∈ cComp (l32nH T V) := map_subtype_mem_cComp hL'
  have hKH : K ≤ l32nH T V := le_of_mem_cComp hK
  have hKimg : D.img K = M.A := by
    apply le_antisymm
    · intro γ hγ
      obtain ⟨k, hk, hkN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
      obtain ⟨k', hk', hkk'⟩ := hk
      have hmem : rhoH D k' ∈ Kd := hL'ρ ▸ ⟨k', hk', rfl⟩
      have e : D.ρ ⟨k, hkN⟩ =
          ((rhoH D k' : ↥(D.img (l32nH T V))) : D.V ≃ₗ[ZMod 2] D.V) := by
        rw [coe_rhoH]
        congr 2
        exact hkk'.symm
      rw [e]
      exact hmem
    · intro α hα
      have hmem : (⟨α, M.A_le hα⟩ : ↥(D.img (l32nH T V))) ∈ Kd := hα
      rw [← hL'ρ] at hmem
      obtain ⟨k', hk', hkk'⟩ := hmem
      refine (L128A.HatU.mem_img D).mpr ⟨k', ⟨k', hk', rfl⟩, H_N k'.2, ?_⟩
      have := congrArg Subtype.val hkk'
      rw [coe_rhoH] at this
      exact this
  refine ⟨K, hK, hKimg, fun h hh => ?_⟩
  by_contra hn
  set K₂ : Subgroup G := K.map (MulAut.conj h).toMonoidHom with hK₂def
  have hK₂ : K₂ ∈ cComp (l32nH T V) := map_conj_mem_cComp hK hh
  have hne : K ≠ K₂ := fun hKK => hn (A38.map_conj_eq_iff.mp hKK.symm)
  have hc2 := lemma_1_2_1_two C.hyp.fsu.qtke C.hyp.fsu.simple C.hyp.fsu.nonabelian h37 hH hK hK₂
    hne
  have hcomm : ⁅K, K₂⁆ ≤ pCoreOf 2 (l32nH T V) := hc2.1.trans hc2.2
  have hhN := H_N hh
  have hK₂img : ∀ β ∈ M.A, ∃ k ∈ K₂, ∃ hkN : k ∈ Subgroup.normalizer (fsuU T V : Set G),
      D.ρ ⟨k, hkN⟩ = β := by
    intro β hβ
    have hβ' : (D.ρ ⟨h, hhN⟩)⁻¹ * β * (D.ρ ⟨h, hhN⟩)⁻¹⁻¹ ∈ M.A :=
      M.A_normal (Subgroup.inv_mem _ (L128A.HatU.rho_mem_img D hh hhN)) hβ
    rw [← hKimg] at hβ'
    obtain ⟨k, hk, hkN, hke⟩ := (L128A.HatU.mem_img D).mp hβ'
    have hN' : h * k * h⁻¹ ∈ Subgroup.normalizer (fsuU T V : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hhN hkN) (Subgroup.inv_mem _ hhN)
    refine ⟨h * k * h⁻¹, ⟨k, hk, rfl⟩, hN', ?_⟩
    have e : D.ρ ⟨h * k * h⁻¹, hN'⟩ = D.ρ ⟨h, hhN⟩ * D.ρ ⟨k, hkN⟩ * (D.ρ ⟨h, hhN⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e, hke]
    group
  apply hnc
  have hα : M.ψ S8Five.a9 ∈ D.img K := hKimg ▸ ha9A
  obtain ⟨k₁, hk₁, hk₁N, hk₁e⟩ := (L128A.HatU.mem_img D).mp hα
  obtain ⟨k₂, hk₂, hk₂N, hk₂e⟩ := hK₂img _ hn1A
  have hck : k₁ * k₂ * k₁⁻¹ * k₂⁻¹ ∈ pCoreOf 2 (l32nH T V) := by
    apply hcomm
    have := Subgroup.commutator_mem_commutator hk₁ hk₂
    rwa [commutatorElement_def] at this
  have hN' : k₁ * k₂ * k₁⁻¹ * k₂⁻¹ ∈ Subgroup.normalizer (fsuU T V : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hk₁N hk₂N)
      (Subgroup.inv_mem _ hk₁N)) (Subgroup.inv_mem _ hk₂N)
  have h1 := C.rho_eq_one_of_pCoreOf hck hN'
  have e : D.ρ ⟨k₁ * k₂ * k₁⁻¹ * k₂⁻¹, hN'⟩ =
      D.ρ ⟨k₁, hk₁N⟩ * D.ρ ⟨k₂, hk₂N⟩ * (D.ρ ⟨k₁, hk₁N⟩)⁻¹ * (D.ρ ⟨k₂, hk₂N⟩)⁻¹ := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  rw [e, hk₁e, hk₂e] at h1
  calc M.ψ S8Five.a9 * M.ψ S8Five.n1 =
      (M.ψ S8Five.a9 * M.ψ S8Five.n1 * (M.ψ S8Five.a9)⁻¹ * (M.ψ S8Five.n1)⁻¹) *
        (M.ψ S8Five.n1 * M.ψ S8Five.a9) := by group
    _ = M.ψ S8Five.n1 * M.ψ S8Five.a9 := by rw [h1, one_mul]

end Ctx5

end L14324

end CFSG.Quasithin.H13
