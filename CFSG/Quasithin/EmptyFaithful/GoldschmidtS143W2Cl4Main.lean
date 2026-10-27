module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Cl4Fus
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Cl4Syl
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Cl4Wr
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Cl4Cnt
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2LocJ
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2PcD

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.QuasithinUnique.Tight CFSG.QuasithinUnique.BenderBranch
  CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

namespace InspW2

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t d x : G}

theorem card_E0 (h : Ctx T M g A t d x) : Nat.card ↥(rOf T M ⊓ Gw d x) = 16 := by
  obtain ⟨φ⟩ := h.hR
  rw [Nat.card_congr φ.toEquiv, Nat.card_prod]
  have : Nat.card (Multiplicative (ZMod 4)) = 4 := by
    rw [Nat.card_eq_fintype_card]; decide
  rw [this]

theorem E0_comm (h : Ctx T M g A t d x) :
    ∀ a ∈ rOf T M ⊓ Gw d x, ∀ b ∈ rOf T M ⊓ Gw d x, a * b = b * a := by
  obtain ⟨eZ⟩ := h.hR
  intro a ha b hb
  have key : (⟨a, ha⟩ : ↥(rOf T M ⊓ Gw d x)) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ :=
    eZ.injective (by rw [map_mul, map_mul]; exact mul_comm _ _)
  exact congrArg Subtype.val key

theorem clause4_holds : Clause4 := by
  intro G _ _ T M g A t d x h L hL hmod
  have hf : LocalFacts T d x := ⟨wp0_of_ctx h, wp1_of_wp0 h (wp0_of_ctx h)⟩
  set S : Subgroup G := Tw T d x ⊓ L with hS
  set E : Subgroup G := rOf T M ⊓ Gw d x with hE
  have hS32 : Nat.card ↥S = 32 := card_Tw_inf_comp h hf hL hmod
  have hEL : E ≤ L := E0_le_comp h hf hL hmod
  have hES : E ≤ S := le_inf (E0_le_Tw h) hEL
  have hE16 : Nat.card ↥E = 16 := card_E0 h
  have hSL : S ≤ L := inf_le_right
  have hcardS : Nat.card ↥(S.subgroupOf L) = 32 := by
    rw [← hS32]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL).toEquiv
  obtain ⟨a, ha, b, hb, ha2, hb2, hab⟩ := exists_noncomm_invol hmod (S.subgroupOf L) hcardS
  have haS : (a : G) ∈ S := Subgroup.mem_subgroupOf.mp ha
  have hbS : (b : G) ∈ S := Subgroup.mem_subgroupOf.mp hb
  have ha2' : (a : G) * (a : G) = 1 := congrArg Subtype.val ha2
  have hb2' : (b : G) * (b : G) = 1 := congrArg Subtype.val hb2
  obtain ⟨u, huS, hu2, hnu⟩ : ∃ u ∈ S, u * u = 1 ∧ u ∉ E := by
    by_cases hae : (a : G) ∈ E
    · refine ⟨b, hbS, hb2', fun hbe => hab (Subtype.ext ?_)⟩
      exact E0_comm h _ hae _ hbe
    · exact ⟨a, haS, ha2', hae⟩
  have hu1 : u ≠ 1 := fun h1 => hnu (h1 ▸ E.one_mem)
  have huRQ : u ∈ rOf T M ⊔ qOf T := invol_mem_RQ h hf hL hmod huS hu2 hu1
  have hSeq : S = E ⊔ Subgroup.zpowers u :=
    eq_sup_zpowers_of_card hES huS hnu (by rw [hS32, hE16])
  have hSRQ : S ≤ rOf T M ⊔ qOf T := by
    rw [hSeq]
    exact sup_le (inf_le_left.trans le_sup_left) ((Subgroup.zpowers_le).mpr huRQ)
  have hwQ : wOfX d x ∈ qOf T := wOfX_mem_qOf h
  have hwL : wOfX d x ∉ L := by
    intro hwL
    have hzL : d * d ∈ L := hEL (z_mem_E0 h)
    obtain ⟨m, -, hm⟩ := R3c19.exists_conj_of_u33_subgroup hmod (d * d) hzL (wOfX d x) hwL
      h.z_sq h.z_ne h.w_sq h.w_ne
    exact h.hN1 m hm
  have hwS : wOfX d x ∉ S := fun hw => hwL (hSL hw)
  have hwc : ∀ s ∈ S, wOfX d x * s = s * wOfX d x := fun s hs =>
    (mem_Gw_iff.mp (hL.1 (hSL hs))).symm
  have hcard1 := card_zpowers_sup h.w_sq h.w_ne hwS hwc
  have hle : Subgroup.zpowers (wOfX d x) ⊔ S ≤ Tw T d x ⊓ (rOf T M ⊔ qOf T) := by
    refine sup_le ?_ (le_inf inf_le_left hSRQ)
    rw [Subgroup.zpowers_le]
    exact ⟨⟨h.w_mem_T, h.w_mem_Gw⟩, Subgroup.mem_sup_right hwQ⟩
  have heq := Subgroup.eq_of_le_of_card_ge hle (by
    rw [hcard1, hS32]; exact card_Tw_inf_RQ_le h)
  show Tw T d x ⊓ (rOf T M ⊔ qOf T) ≤ _
  rw [← heq]
  exact sup_le_sup_left hSL _

end InspW2

end S143

end CFSG.Quasithin
