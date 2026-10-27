module

public import CFSG.Quasithin.EmptyFaithful.SzPS8PLift
public import CFSG.Quasithin.EmptyFaithful.SzPS8S6Class
public import CFSG.Quasithin.EmptyFaithful.SzPS8Excl2Defs
public import CFSG.Quasithin.Background.P4InspSpEmbed

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.GoldS146R CFSG.LieType.BorelTits
open scoped MatrixGroups

namespace SzPS8

section Generic

variable {Γ : Type*} [Group Γ]

theorem le_of_normal_of_trivial_centralizer {K P : Subgroup Γ} [K.Normal] [P.Normal]
    (hKs : IsSimpleGroup ↥K) (hC : ∀ x : Γ, (∀ k ∈ K, x * k = k * x) → x = 1) (hP : P ≠ ⊥) :
    K ≤ P := by
  rcases hKs.eq_bot_or_eq_top_of_normal (P.subgroupOf K) with h0 | h1
  · exfalso
    apply hP
    rw [eq_bot_iff]
    intro p hp
    rw [Subgroup.mem_bot]
    refine hC p fun k hk => ?_
    have hK : p * k * p⁻¹ * k⁻¹ ∈ K :=
      K.mul_mem (Subgroup.Normal.conj_mem inferInstance k hk p) (K.inv_mem hk)
    have hPm : p * k * p⁻¹ * k⁻¹ ∈ P := by
      have := P.mul_mem hp (Subgroup.Normal.conj_mem inferInstance p⁻¹ (P.inv_mem hp) k)
      simpa [mul_assoc] using this
    have hmem : (⟨p * k * p⁻¹ * k⁻¹, hK⟩ : ↥K) ∈ P.subgroupOf K := hPm
    rw [h0, Subgroup.mem_bot] at hmem
    have h2 : p * k * p⁻¹ * k⁻¹ = 1 := congrArg Subtype.val hmem
    calc p * k = (p * k * p⁻¹ * k⁻¹) * (k * p) := by group
      _ = k * p := by rw [h2, one_mul]
  · exact Subgroup.subgroupOf_eq_top.mp h1

end Generic

section Six

open Equiv Equiv.Perm S6Class

@[expose] def cycThree : Perm (Fin 6) := [(0 : Fin 6), 1, 2].formPerm

theorem eq_one_of_comm_cycFive_cycThree :
    ∀ x : Perm (Fin 6), x * cycFive = cycFive * x → x * cycThree = cycThree * x → x = 1 := by
  decide +kernel

theorem eq_one_of_comm_cycFive_invZeroInf :
    ∀ x : Perm (Fin 6), x * cycFive = cycFive * x → x * invZeroInf = invZeroInf * x → x = 1 := by
  decide +kernel

theorem cycThree_mem_a5p : cycThree ∈ a5p := by
  rw [mem_a5p]
  exact ⟨by decide +kernel, by decide +kernel⟩

theorem cycFive_mem_a5p : cycFive ∈ a5p := mem_a5p.mpr ⟨cycFive_apply_five, sign_cycFive⟩

theorem cycFive_mem_psl25 : cycFive ∈ psl25 :=
  Subgroup.mem_inf.mpr ⟨cycFive_mem_pgl25, mem_alternatingGroup.mpr sign_cycFive⟩

theorem invZeroInf_mem_psl25 : invZeroInf ∈ psl25 :=
  Subgroup.mem_inf.mpr ⟨invZeroInf_mem_pgl25, mem_alternatingGroup.mpr (by decide +kernel)⟩

theorem centralizer_trivial_of_alt_five (S : Subgroup (Perm (Fin 6)))
    (e : ↥S ≃* ↥(alternatingGroup (Fin 5))) {x : Perm (Fin 6)} (hx : ∀ s ∈ S, x * s = s * x) :
    x = 1 := by
  have hcard5 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  have h60 : Nat.card ↥S = 60 := by rw [Nat.card_congr e.toEquiv, hcard5]
  have hS : ¬ Group.IsSolvable ↥S := by
    intro hs
    have : Group.IsSolvable ↥(alternatingGroup (Fin 5)) :=
      Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective
    have hs5 : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    have hcomm := IsSimpleGroup.comm_iff_isSolvable.mpr this
    have ha : Equiv.swap (0 : Fin 5) 1 * Equiv.swap 0 2 ∈ alternatingGroup (Fin 5) :=
      (Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide)
        (by decide)).mem_alternatingGroup
    have hb : Equiv.swap (0 : Fin 5) 1 * Equiv.swap 0 3 ∈ alternatingGroup (Fin 5) :=
      (Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide)
        (by decide)).mem_alternatingGroup
    have hne : (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 0 2) *
        (Equiv.swap 0 1 * Equiv.swap 0 3) ≠
        (Equiv.swap 0 1 * Equiv.swap 0 3) * (Equiv.swap 0 1 * Equiv.swap 0 2) := by decide
    exact hne (congrArg Subtype.val (hcomm ⟨_, ha⟩ ⟨_, hb⟩))
  obtain ⟨σ, hσ⟩ := exists_conj_mem_of_not_isSolvable S hS
  have hcard : Nat.card ↥(S.map (MulAut.conj σ).toMonoidHom) = 60 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj σ).injective, h60]
  have hy : ∀ n ∈ S.map (MulAut.conj σ).toMonoidHom,
      (σ * x * σ⁻¹) * n = n * (σ * x * σ⁻¹) := by
    rintro _ ⟨s, hs, rfl⟩
    have := hx s hs
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc σ * x * σ⁻¹ * (σ * s * σ⁻¹) = σ * (x * s) * σ⁻¹ := by group
      _ = σ * (s * x) * σ⁻¹ := by rw [this]
      _ = σ * s * σ⁻¹ * (σ * x * σ⁻¹) := by group
  have h1 : σ * x * σ⁻¹ = 1 := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
    rcases hσ with h | h | h | h | h | h
    · rw [h, card_alternatingGroup_six] at hcard
      omega
    · rw [h, card_top_six] at hcard
      omega
    · rw [h, card_s5p] at hcard
      omega
    · rw [h] at hy
      exact eq_one_of_comm_cycFive_cycThree _ (hy _ cycFive_mem_a5p) (hy _ cycThree_mem_a5p)
    · rw [h, card_pgl25] at hcard
      omega
    · rw [h] at hy
      exact eq_one_of_comm_cycFive_invZeroInf _ (hy _ cycFive_mem_psl25)
        (hy _ invZeroInf_mem_psl25)
  have h2 : x = σ⁻¹ * (σ * x * σ⁻¹) * σ := by group
  rw [h2, h1]
  group

end Six

section Hat

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem imgΓ_cZU_normal (h : Hyp1281Two G T M (yOfL22 T M)) (D : HatModel T M) :
    (imgΓ h D (cZU T M)).Normal :=
  Subgroup.Normal.map (cZU_normal_subgroupOf h) (rhoΓ h D) (rhoΓ_surjective h D)

theorem imgΓ_cZU_ne_bot (h : Hyp1281Two G T M (yOfL22 T M))
    (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) (D : HatModel T M) : imgΓ h D (cZU T M) ≠ ⊥ := by
  intro hbot
  apply img_cZU_ne_bot h hU D
  rw [← S143V.map_rhoH h D cZU_le]
  have e : ((cZU T M).subgroupOf (mcOf T)).map (S143V.rhoH h D) =
      (imgΓ h D (cZU T M)).map (D.img (mcOf T)).subtype := by
    unfold imgΓ
    rw [Subgroup.map_map]
    rfl
  rw [e, hbot, Subgroup.map_bot]

theorem false_of_normal_a5 (hyp : Hyp1421 G T M) (hnot : ¬ SixModels G)
    (hnab : ¬ IsMulCommutative ↥(uOfL22 T M)) (h11 : StageLemma14111) (h113 : StageLemma14113)
    (h35 : Lemma1435) (h37 : A37ForSQTK) (h39 : A39ForSQTK) (hE22 : E2.E22StatementNoN)
    (hF : FieldOne1432) (D : HatModel T M) {N : Subgroup ↥(D.img (mcOf T))} (hNn : N.Normal)
    (e5 : ↥N ≃* ↥(alternatingGroup (Fin 5)))
    (hC : ∀ x : ↥(D.img (mcOf T)), (∀ k ∈ N, x * k = k * x) → x = 1) : False := by
  have h1281 : Hyp1281Two G T M (yOfL22 T M) := hyp.hyp1281Two_of_inputs h11 h113
  have hs5 : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hKs : IsSimpleGroup ↥N := e5.isSimpleGroup
  have hKP : N ≤ imgΓ h1281 D (cZU T M) := by
    have := imgΓ_cZU_normal h1281 D
    have := hNn
    exact le_of_normal_of_trivial_centralizer hKs hC (imgΓ_cZU_ne_bot h1281 hnab D)
  obtain ⟨eS⟩ : Nonempty (SL(2, GaloisField 2 2) ≃* ↥(alternatingGroup (Fin 5))) := by
    obtain ⟨e⟩ := CFSG.Glauberman.Dickson.nonempty_psl2_galoisField_four_mulEquiv
    exact ⟨(CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 2)).symm.trans e⟩
  exact false_of_normal_sl2_four hyp hnot hnab h11 h113 h35 h37 h39 hE22 hF D hNn
    (e5.trans eS.symm) hKP

end Hat

theorem excl2NoNormalA5 (h11 : StageLemma14111) (h113 : StageLemma14113) (h35 : Lemma1435)
    (h37 : A37ForSQTK) (h39 : A39ForSQTK) (hE22 : E2.E22StatementNoN) (hF : FieldOne1432) :
    Excl2NoNormalA5 := by
  intro G _ _ T M hyp hnot hnab D hd ⟨N, hNn, ⟨e5⟩⟩
  classical
  have h1281 : Hyp1281Two G T M (yOfL22 T M) := hyp.hyp1281Two_of_inputs h11 h113
  obtain ⟨a, haV, haZ⟩ := h1281.exists_mem_VZ_not_mem
  obtain ⟨g, hg⟩ := h1281.exists_goodElt_L
  have h101 := h1281.lemma_12_8_12_three hnab hg D haV haZ
  have hsymp : G11.IsSymplectic D.B := ⟨D.B_isAlt, D.B_nondegenerate⟩
  have hΓsp : D.img (mcOf T) ≤ G11.spSub D.B := fun γ hγ x y => h101.isometry γ hγ x y
  obtain ⟨Mo⟩ := G11.P4InspSp.p4inspsp_exists_model hsymp hd
  obtain ⟨ρ, hinj, -, -, hrange⟩ := G11.P4InspSp.p4inspsp_exists_embedding hsymp hd Mo
  have hΓ : D.img (mcOf T) ≤ ρ.range := hΓsp.trans hrange
  set N' : Subgroup (G11.GLV D.V) := N.map (D.img (mcOf T)).subtype with hN'
  have hN'r : N' ≤ ρ.range := by
    rintro _ ⟨k, -, rfl⟩
    exact hΓ k.2
  set S : Subgroup (Equiv.Perm (Fin 6)) := N'.comap ρ with hS
  have hmap : S.map ρ = N' := Subgroup.map_comap_eq_self hN'r
  let eS : ↥S ≃* ↥N :=
    (Subgroup.equivMapOfInjective S ρ hinj).trans
      ((MulEquiv.subgroupCongr hmap).trans
        (Subgroup.equivMapOfInjective N (D.img (mcOf T)).subtype
          (D.img (mcOf T)).subtype_injective).symm)
  refine false_of_normal_a5 hyp hnot hnab h11 h113 h35 h37 h39 hE22 hF D hNn e5 ?_
  intro x hx
  obtain ⟨σ, hσ⟩ := hΓ x.2
  have hσc : ∀ s ∈ S, σ * s = s * σ := by
    intro s hs
    have hs' : ρ s ∈ N' := hs
    obtain ⟨k, hk, hkρ⟩ := hs'
    have h1 := hx k hk
    apply hinj
    rw [map_mul, map_mul, hσ, ← hkρ]
    exact congrArg Subtype.val h1
  have hσ1 : σ = 1 := centralizer_trivial_of_alt_five S (eS.trans e5) hσc
  apply Subtype.ext
  rw [← hσ, hσ1, map_one]
  rfl

end SzPS8

end CFSG.Quasithin
