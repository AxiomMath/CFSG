module

public import CFSG.Walter.Bender1970.S1.Burnside
import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Defs
public import Certificates.Data.A5

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter CFSG.SectionRank

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_zpowers_eq_bot_iff {t : G} {X : Subgroup G} :
    ⁅Subgroup.zpowers t, X⁆ = ⊥ ↔ ∀ x ∈ X, x * t = t * x := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.zpowers_le,
    Subgroup.mem_centralizer_iff]
  rfl

private theorem rank_eq_of_card_eq {T E R : Subgroup G} (hTp : IsPGroup 2 T)
    (hRE : R ≤ E) (hET : E ≤ T) (hE : CFSG.Open.IsElemAbelian 2 E)
    (hcardE : Nat.card E = 2 ^ CFSG.Open.pRank 2 T) (hcardR : Nat.card R * 2 = Nat.card E) :
    rank R = rank T - 1 := by
  have hp2 : Nat.Prime 2 := Nat.prime_two
  have hRp : IsPGroup 2 R := hTp.to_le (hRE.trans hET)
  rw [rank_eq_pRank_of_isPGroup hp2 hTp, rank_eq_pRank_of_isPGroup hp2 hRp]
  set r := CFSG.Open.pRank 2 T
  have hr : 1 ≤ r := by
    by_contra h0
    push Not at h0
    rw [Nat.lt_one_iff.mp h0, pow_zero] at hcardE
    have := Nat.card_pos (α := R)
    omega
  have hcardR' : Nat.card R = 2 ^ (r - 1) := by
    have h : 2 ^ r = 2 ^ (r - 1) * 2 := by rw [← pow_succ, Nat.sub_add_cancel hr]
    rw [hcardE, h] at hcardR
    exact Nat.eq_of_mul_eq_mul_right two_pos hcardR
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hRel : CFSG.Open.IsElemAbelian 2 R :=
    ⟨⟨⟨fun a b => Subtype.ext (hEc _ (hRE a.2) _ (hRE b.2))⟩⟩, fun x hx => hE.2 x (hRE hx)⟩
  refine le_antisymm ?_ (le_pRank one_lt_two le_rfl hRel hcardR')
  refine pRank_le one_lt_two fun F hFR _ => ?_
  rw [← hcardR']
  exact Subgroup.card_le_of_le hFR

theorem exists_rank_eq_commutator_ne_bot {T : Subgroup G} (hTp : IsPGroup 2 T)
    (hcommT : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) {t : G} (htT : t ∈ T) (ht : orderOf t = 2)
    {D : Subgroup G} (hTD : T ≤ Subgroup.normalizer (D : Set G)) (hDodd : Odd (Nat.card D))
    (htD : ⁅Subgroup.zpowers t, D⁆ ≠ ⊥) :
    ∃ R ≤ T, rank R = rank T - 1 ∧
      ⁅Subgroup.zpowers t, D ⊓ Subgroup.centralizer (R : Set G)⁆ ≠ ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E := omegaOneOfComm 2 T hcommT with hEdef
  have hET : E ≤ T := omegaOneOfComm_le T hcommT
  have htE : t ∈ E := ⟨htT, by rw [← ht, pow_orderOf_eq_one]⟩
  have hcardE : Nat.card E = 2 ^ CFSG.Open.pRank 2 T :=
    card_omegaOneOfComm Nat.prime_two T hcommT hTp
  have hEel : CFSG.Open.IsElemAbelian 2 E :=
    ⟨⟨⟨fun a b => Subtype.ext (hcommT _ (hET a.2) _ (hET b.2))⟩⟩, fun x hx => hx.2⟩
  have hEcomm := hEel.1
  have : IsElementaryAbelian 2 E :=
    { exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (hEel.2 x x.2) }
  have : Nontrivial E := by
    refine ⟨⟨⟨t, htE⟩, 1, fun h => ?_⟩⟩
    have h1 : t = 1 := congrArg Subtype.val h
    rw [h1, orderOf_one] at ht
    exact absurd ht (by norm_num)
  let _ : MulDistribMulAction E D :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer E D (hET.trans hTD)
  have hp : ¬ 2 ∣ Nat.card D := fun h => (Nat.not_even_iff_odd.mpr hDodd) (even_iff_two_dvd.mpr h)
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := 2) (A := E) (H := D) hp
  by_contra hcon
  push Not at hcon
  apply htD
  rw [commutator_zpowers_eq_bot_iff]
  set Ct : Subgroup D := (Subgroup.centralizer ({t} : Set G)).comap D.subtype
  have hle : ⨆ (B : Subgroup E) (_ : B.index = 2), CFSG.fixedPointSubgroup B D ≤ Ct := by
    refine iSup₂_le fun B hB => ?_
    set R : Subgroup G := B.map E.subtype
    have hRE : R ≤ E := Subgroup.map_subtype_le B
    have hcardR : Nat.card R * 2 = Nat.card E := by
      rw [Subgroup.card_map_of_injective E.subtype_injective, ← hB]
      exact B.card_mul_index
    have h := hcon R (hRE.trans hET) (rank_eq_of_card_eq hTp hRE hET hEel hcardE hcardR)
    rw [commutator_zpowers_eq_bot_iff] at h
    intro x hx
    refine Subgroup.mem_centralizer_singleton_iff.mpr (h x ⟨x.2, ?_⟩)
    show (x : G) ∈ Subgroup.centralizer (R : Set G)
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    have hbx := congrArg Subtype.val (hx ⟨b, hb⟩)
    change (b : G) * (x : G) * (b : G)⁻¹ = (x : G) at hbx
    calc (b : G) * (x : G) = (b : G) * (x : G) * (b : G)⁻¹ * (b : G) := by group
      _ = (x : G) * (b : G) := by rw [hbx]
  rw [hgen, top_le_iff] at hle
  intro x hx
  have hxC : (⟨x, hx⟩ : D) ∈ Ct := hle ▸ Subgroup.mem_top _
  exact Subgroup.mem_centralizer_singleton_iff.mp hxC

theorem bender1970_3_4 (T : Sylow 2 G) (hT : IsMulCommutative (T : Subgroup G)) {t : G}
    (htT : t ∈ (T : Subgroup G)) (ht : orderOf t = 2) {D : Subgroup G}
    (hTD : (T : Subgroup G) ≤ Subgroup.normalizer (D : Set G)) (hDodd : Odd (Nat.card D))
    (htD : ⁅Subgroup.zpowers t, D⁆ ≠ ⊥) :
    ∃ R ≤ (T : Subgroup G), rank R = rank (T : Subgroup G) - 1 ∧
      ⁅Subgroup.zpowers t, D ⊓ Subgroup.centralizer (R : Set G)⁆ ≠ ⊥ :=
  exists_rank_eq_commutator_ne_bot T.isPGroup'
    (fun x hx y hy => congrArg Subtype.val (hT.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)) htT ht hTD hDodd htD

end CFSG.Walter
