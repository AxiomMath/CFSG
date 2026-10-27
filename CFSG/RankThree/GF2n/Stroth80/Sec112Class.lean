module

public import CFSG.RankThree.GF2n.Stroth80.Sec112Basic
import CFSG.RankThree.GF2n.Stroth80.Sec112Model
import CFSG.Timmesfeld.RootInvolutionConj
public import CFSG.Timmesfeld.Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.Timmesfeld (IsRootInvolutionSet)

private theorem ne_sq_of_orderOf_eq_four {Γ : Type*} [Group Γ] {D : Set Γ}
    (hD : IsRootInvolutionSet D) {d e : Γ} (hd : d ∈ D) (he : e ∈ D)
    (h4 : orderOf (d * e) = 4) : d ≠ (d * e) ^ 2 := by
  intro heq
  obtain ⟨-, -, -, hrel⟩ := CFSG.Timmesfeld.sq_mem_of_orderOf_eq_four hD hd he h4
  have hdd := hD.mul_self_eq_one hd
  have hee := hD.mul_self_eq_one he
  have h1 : e * d * e = 1 := by rw [hrel, ← heq, hdd]
  apply hD.ne_one hd
  calc d = (e * e) * d * (e * e) := by rw [hee, one_mul, mul_one]
    _ = e * (e * d * e) * e := by group
    _ = 1 := by rw [h1, mul_one, hee]

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem Ctx.exists_odd_partner_A2Set_inter [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    (hD : IsRootInvolutionSet (A2Set M Q Z ∩ (bar M Q (H0 M Z) : Set (Mbar M Q))))
    {a : Mbar M Q} (ha : a ∈ A2Set M Q Z ∩ (bar M Q (H0 M Z) : Set (Mbar M Q))) :
    ∃ c ∈ A2Set M Q Z ∩ (bar M Q (H0 M Z) : Set (Mbar M Q)),
      Odd (orderOf (a * c)) ∧ a * c ≠ 1 := by
  have : Finite (Mbar M Q) := inferInstanceAs (Finite (↥M ⧸ Q.subgroupOf M))
  have hO : a ∉ CFSG.Open.pCoreOf 2 (⊤ : Subgroup (Mbar M Q)) := by
    intro hmem
    have h1 := pCoreOf_le_pCore_of_subnormal (le_refl (⊤ : Subgroup (Mbar M Q)))
      Subgroup.le_normalizer Subgroup.normal_top hmem
    rw [hc.pCore_two_Mbar, Subgroup.mem_bot] at h1
    exact hD.ne_one ha h1
  obtain ⟨y, -, hodd, hne⟩ := CFSG.Timmesfeld.exists_odd_partner_of_not_mem_pCoreOf hD
    (fun _ _ => Subgroup.mem_top _) (fun y _ x hx => hc.conj_mem_A2Set_inter y hx) ha hO
  exact ⟨y * a * y⁻¹, hc.conj_mem_A2Set_inter y ha, hodd, hne⟩

theorem Ctx.ebarSqClosed [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    (hD : IsRootInvolutionSet (A2Set M Q Z ∩ (bar M Q (H0 M Z) : Set (Mbar M Q)))) :
    EbarSqClosedStatement M Q Z B := by
  intro e₁ he₁ e₂ he₂ h4
  have : Finite (Mbar M Q) := inferInstanceAs (Finite (↥M ⧸ Q.subgroupOf M))
  have hsub := hc.Ebar_subset_A2Set_inter
  obtain ⟨hsD, hc1, -, hrel⟩ :=
    CFSG.Timmesfeld.sq_mem_of_orderOf_eq_four hD (hsub he₁) (hsub he₂) h4
  have hmulD : e₁ * (e₁ * e₂) ^ 2 ∈ A2Set M Q Z ∩ (bar M Q (H0 M Z) : Set (Mbar M Q)) := by
    rw [← hrel]
    have h1 := hc.conj_mem_A2Set_inter e₂ (hsub he₁)
    rwa [hD.inv_eq (hsub he₂)] at h1
  obtain ⟨g, hg⟩ := CFSG.Timmesfeld.exists_conj_of_commuting_pair hD
    (fun g _ hx => hc.conj_mem_A2Set_inter g hx)
    (fun _ ha => hc.exists_odd_partner_A2Set_inter hD ha) (hsub he₁) hsD
    (ne_sq_of_orderOf_eq_four hD (hsub he₁) (hsub he₂) h4) hc1.eq hmulD
  rw [← hg]
  exact hc.Ebar_conj he₁ g

theorem Ctx.isRootInvolutionSet_Ebar [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    (hD : IsRootInvolutionSet (A2Set M Q Z ∩ (bar M Q (H0 M Z) : Set (Mbar M Q)))) :
    IsRootInvolutionSet (Ebar M Q Z B) :=
  ⟨fun d hd => hD.1 d (hc.Ebar_subset_A2Set_inter hd),
    fun d hd e he => hD.2.1 d (hc.Ebar_subset_A2Set_inter hd) e (hc.Ebar_subset_A2Set_inter he),
    fun d hd e he h4 => hc.ebarSqClosed hD d hd e he h4⟩

theorem Ctx.exists_odd_partner_Ebar [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    (hD : IsRootInvolutionSet (A2Set M Q Z ∩ (bar M Q (H0 M Z) : Set (Mbar M Q))))
    {e : Mbar M Q} (he : e ∈ Ebar M Q Z B) :
    ∃ y ∈ Xbar M Q Z B, Odd (orderOf (e * (y * e * y⁻¹))) ∧ e * (y * e * y⁻¹) ≠ 1 := by
  have : Finite (Mbar M Q) := inferInstanceAs (Finite (↥M ⧸ Q.subgroupOf M))
  have hE := hc.isRootInvolutionSet_Ebar hD
  have hO : e ∉ CFSG.Open.pCoreOf 2 (Xbar M Q Z B) := by
    intro hmem
    have h1 := pCoreOf_le_pCore_of_subnormal (le_refl (Xbar M Q Z B))
      Subgroup.le_normalizer hc.Xbar_normal hmem
    rw [hc.pCore_two_Mbar, Subgroup.mem_bot] at h1
    exact hE.ne_one he h1
  exact CFSG.Timmesfeld.exists_odd_partner_of_not_mem_pCoreOf hE
    (fun _ hx => Subgroup.subset_closure hx) (fun y _ x hx => hc.Ebar_conj hx y) he hO

private theorem Ctx.conj_of_orderOf_eq_four [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    (hD : IsRootInvolutionSet (A2Set M Q Z ∩ (bar M Q (H0 M Z) : Set (Mbar M Q))))
    {e f : Mbar M Q} (he : e ∈ Ebar M Q Z B) (hf : f ∈ Ebar M Q Z B)
    (h4 : orderOf (e * f) = 4) : ∃ x ∈ Xbar M Q Z B, x * e * x⁻¹ = f := by
  have : Finite (Mbar M Q) := inferInstanceAs (Finite (↥M ⧸ Q.subgroupOf M))
  have hE := hc.isRootInvolutionSet_Ebar hD
  have hEX : Ebar M Q Z B ⊆ Xbar M Q Z B := fun _ hx => Subgroup.subset_closure hx
  have hN : ∀ y ∈ Xbar M Q Z B, ∀ x ∈ Ebar M Q Z B, y * x * y⁻¹ ∈ Ebar M Q Z B :=
    fun y _ x hx => hc.Ebar_conj hx y
  have hodd : ∀ a ∈ Ebar M Q Z B, ∃ c ∈ Ebar M Q Z B, Odd (orderOf (a * c)) ∧ a * c ≠ 1 := by
    intro a ha
    obtain ⟨y, -, hy, hy1⟩ := hc.exists_odd_partner_Ebar hD ha
    exact ⟨y * a * y⁻¹, hc.Ebar_conj ha y, hy, hy1⟩
  obtain ⟨hs, hes, hfs, hrel⟩ := CFSG.Timmesfeld.sq_mem_of_orderOf_eq_four hE he hf h4
  have hinv : f * e = (e * f)⁻¹ := by rw [mul_inv_rev, hE.inv_eq he, hE.inv_eq hf]
  have hfe4 : orderOf (f * e) = 4 := by rw [hinv, orderOf_inv]; exact h4
  obtain ⟨-, -, -, hrel'⟩ := CFSG.Timmesfeld.sq_mem_of_orderOf_eq_four hE hf he hfe4
  have hsq : (f * e) ^ 2 = (e * f) ^ 2 := by
    have h44 : (e * f) ^ 4 = 1 := h4 ▸ pow_orderOf_eq_one (e * f)
    rw [hinv, inv_pow, inv_eq_iff_mul_eq_one, ← pow_add]
    exact h44
  have hesE : e * (e * f) ^ 2 ∈ Ebar M Q Z B := by
    rw [← hrel]
    have h1 := hc.Ebar_conj he f
    rwa [hE.inv_eq hf] at h1
  have hfsE : f * (e * f) ^ 2 ∈ Ebar M Q Z B := by
    rw [← hsq, ← hrel']
    have h1 := hc.Ebar_conj hf e
    rwa [hE.inv_eq he] at h1
  obtain ⟨y₁, hy₁, h₁⟩ := CFSG.Timmesfeld.exists_conj_of_commuting_pair_sub hE hEX hN hodd he hs
    (ne_sq_of_orderOf_eq_four hE he hf h4) hes.eq hesE
  obtain ⟨y₂, hy₂, h₂⟩ := CFSG.Timmesfeld.exists_conj_of_commuting_pair_sub hE hEX hN hodd hf hs
    (by rw [← hsq]; exact ne_sq_of_orderOf_eq_four hE hf he hfe4) hfs.eq hfsE
  refine ⟨y₂⁻¹ * y₁, (Xbar M Q Z B).mul_mem ((Xbar M Q Z B).inv_mem hy₂) hy₁, ?_⟩
  calc y₂⁻¹ * y₁ * e * (y₂⁻¹ * y₁)⁻¹ = y₂⁻¹ * (y₁ * e * y₁⁻¹) * y₂ := by group
    _ = y₂⁻¹ * (y₂ * f * y₂⁻¹) * y₂ := by rw [h₁, h₂]
    _ = f := by group

theorem Ctx.commute_of_not_conj [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    (hD : IsRootInvolutionSet (A2Set M Q Z ∩ (bar M Q (H0 M Z) : Set (Mbar M Q))))
    {e f : Mbar M Q} (he : e ∈ Ebar M Q Z B) (hf : f ∈ Ebar M Q Z B)
    (hef : ∀ x ∈ Xbar M Q Z B, x * e * x⁻¹ ≠ f) : e * f = f * e := by
  have : Finite (Mbar M Q) := inferInstanceAs (Finite (↥M ⧸ Q.subgroupOf M))
  have hE := hc.isRootInvolutionSet_Ebar hD
  have hEX : Ebar M Q Z B ⊆ Xbar M Q Z B := fun _ hx => Subgroup.subset_closure hx
  rcases hE.orderOf_mul he hf with h2 | h4 | hodd
  · have hsq : (e * f) ^ 2 = 1 := h2 ▸ pow_orderOf_eq_one (e * f)
    exact ((CFSG.Timmesfeld.commute_iff_mul_sq_eq_one (hE.mul_self_eq_one he)
      (hE.mul_self_eq_one hf)).mpr hsq).eq
  · obtain ⟨x, hx, hxe⟩ := hc.conj_of_orderOf_eq_four hD he hf h4
    exact absurd hxe (hef x hx)
  · obtain ⟨g, hg, hge⟩ := CFSG.Timmesfeld.exists_conj_of_odd_orderOf_mul
      (hE.mul_self_eq_one he) (hE.mul_self_eq_one hf) hodd
    have hgX : g ∈ Xbar M Q Z B := (Subgroup.closure_le _).mpr
      (Set.insert_subset_iff.mpr ⟨hEX he, Set.singleton_subset_iff.mpr (hEX hf)⟩) hg
    exact absurd hge (hef g hgX)

theorem Ctx.exists_conj_LB_lift [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {t : Mbar M Q}
    (ht : t ∈ Ebar M Q Z B) :
    ∃ m ∈ M, ∃ a : ↥M, (a : G) ∈ LB M Q (conjSubgroup m B) ∧ IsA2 Q Z (a : G) ∧
      (a : Mbar M Q) = t := by
  obtain ⟨⟨e, rfl, hA⟩, x, hx⟩ := ht
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  have hyM : (y : G)⁻¹ ∈ M := M.inv_mem y.2
  refine ⟨(y : G)⁻¹, hyM, e, ?_, hA, rfl⟩
  have h1 := (mk_mem_bar_iff_sec4 (le_sup_left : Q ≤ LB M Q B) (y * e * y⁻¹)).mp (by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv]
    exact hx)
  rw [hc.LB_conj hyM, mem_conjSubgroup, inv_inv]
  exact h1

end CFSG.RankThree.GF2n.Stroth80
