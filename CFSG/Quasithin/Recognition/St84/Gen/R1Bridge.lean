module

public import CFSG.Quasithin.Recognition.St84.Gen.S3Slice
public import CFSG.Quasithin.EmptyFaithful.SzSurvLocStmt
import CFSG.Quasithin.Recognition.St84.Gen.PerfectGen
import CFSG.Quasithin.Recognition.St84.AppTreeL2
import CFSG.Quasithin.EmptyFaithful.SBd5Dec
import CFSG.Quasithin.EmptyFaithful.S151S9UPerf
import CFSG.Quasithin.Vol2.Ch12Sec5Gam
import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Am
import CFSG.Quasithin.Background.F1VertexCore
import CFSG.GroupTheory.SylowInfNormal
public import CFSG.Quasithin.Recognition.GoldschmidtF112TitsBorel

public section

namespace CFSG.Quasithin.F112R

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

structure S3L2ZData {G : Type} [Group G] (L1 L2 S Z : Subgroup G) : Prop where
  card_Z : Nat.card Z = 2
  Z_cent_S : Z ≤ Subgroup.centralizer (S : Set G)
  Z_le : Z ≤ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)
  L2_cent : L2 ≤ Subgroup.centralizer (Z : Set G)
  V_le : conjClosure Z L1 ≤ pCoreOf 2 (L2 ⊔ bigB L1 L2 S)
  V_card : Nat.card ↥(conjClosure Z L1) = 4

@[expose] def ZDataS3L2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (n : ℕ),
    F112Hyp L1 L2 S → VS3 L1 → 4 ≤ n → IsL2Quot n (oTwoQuot ↥L2) →
      ∃ Z : Subgroup G, S3L2ZData L1 L2 S Z

@[expose] def ZDataS3L8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
    F112Hyp L1 L2 S → VS3 L1 → IsL2Quot 3 (oTwoQuot ↥L2) →
      ∃ Z : Subgroup G, S3L2ZData L1 L2 S Z ∧
        ∀ u ∈ S, u * u = 1 → (∀ s ∈ S, u * s = s * u) → u ∈ Z

variable {G : Type} [Group G] [Finite G] {L1 L2 S Z : Subgroup G} {n : ℕ}

private theorem sup_perfectCore_pCoreOf_eq {H : Subgroup G} {m : ℕ} (hm : 2 ≤ m)
    (h : IsL2Quot m (oTwoQuot ↥H)) : perfectCore H ⊔ pCoreOf 2 H = H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hperf : Group.IsPerfect (oTwoQuot ↥H) := isPerfect_of_isL2Quot hm h
  let π : ↥H →* oTwoQuot ↥H := QuotientGroup.mk' (CFSG.pCore 2 ↥H)
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hKtop : (perfectCore (⊤ : Subgroup ↥H)).map π = ⊤ := by
    rw [map_perfectCore]
    have htop : (⊤ : Subgroup ↥H).map π = ⊤ := by
      rw [Subgroup.map_top, MonoidHom.range_eq_top_of_surjective π hsurj]
    rw [htop]
    exact perfectCore_eq_self_of_perfect (Subgroup.commutator_eq_self (H := ⊤))
  have hsup : perfectCore (⊤ : Subgroup ↥H) ⊔ π.ker = ⊤ := by
    have h := Subgroup.comap_map_eq (f := π) (H := perfectCore (⊤ : Subgroup ↥H))
    rw [hKtop, Subgroup.comap_top] at h
    exact h.symm
  have hker : π.ker = CFSG.pCore 2 ↥H := QuotientGroup.ker_mk' _
  have hmap : (perfectCore (⊤ : Subgroup ↥H) ⊔ CFSG.pCore 2 ↥H).map H.subtype = H := by
    rw [hker] at hsup
    rw [hsup, Subgroup.map_top, Subgroup.range_subtype]
  rw [Subgroup.map_sup, map_perfectCore, Subgroup.map_top, Subgroup.range_subtype] at hmap
  simpa [pCoreOf] using hmap

private theorem oTwoQuot_perfectCore_mulEquiv {H : Subgroup G} {m : ℕ} (hm : 2 ≤ m)
    (h : IsL2Quot m (oTwoQuot ↥H)) :
    Nonempty (OTwoQuot (perfectCore H) ≃* OTwoQuot H) := by
  have hsup := sup_perfectCore_pCoreOf_eq hm h
  have hle : perfectCore H ≤ H := perfectCore_le H
  have hnorm : H ≤ Subgroup.normalizer (perfectCore H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp (perfectCore_normal H)
  exact St84.pCore_quotient_mulEquiv_of_sup_pCoreOf hle hnorm hsup

theorem isL2Quot_perfectCore (hn : 2 ≤ n) (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    IsL2Quot n (OTwoQuot (perfectCore L2)) := by
  obtain ⟨e⟩ := oTwoQuot_perfectCore_mulEquiv hn h2
  obtain ⟨e2⟩ := h2
  exact ⟨e.trans e2⟩

private theorem isSylowTwoOf_inf_perfectCore (hF : F112Hyp L1 L2 S) :
    IsSylowTwoOf (S ⊓ perfectCore L2) (perfectCore L2) := by
  have hK : perfectCore L2 ≤ L2 := perfectCore_le L2
  have hN : L2 ≤ Subgroup.normalizer (perfectCore L2 : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK).mp (perfectCore_normal L2)
  have h := CFSG.isSylowTwoOf_inf_of_normal (S := S ⊓ L2) (X := L2)
    (N := perfectCore L2) hF.1.h2.sylow hK hN
  have h' : perfectCore L2 ⊓ (S ⊓ L2) = S ⊓ perfectCore L2 := by
    rw [← inf_assoc, inf_comm (perfectCore L2) S, inf_assoc,
      inf_eq_left.mpr (perfectCore_le L2)]
  rwa [h'] at h

private theorem pCoreOf_L2_le_S (hF : F112Hyp L1 L2 S) : pCoreOf 2 L2 ≤ S :=
  (St84.pCoreOf_le_of_isSylowTwoOf hF.1.h2.sylow).trans inf_le_left

private theorem perfectCore_sup_S_eq (hF : F112Hyp L1 L2 S) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) : perfectCore L2 ⊔ S = L2 ⊔ S := by
  have hsup := sup_perfectCore_pCoreOf_eq hn h2
  have hO : pCoreOf 2 L2 ≤ S := pCoreOf_L2_le_S hF
  refine le_antisymm (sup_le ((perfectCore_le L2).trans le_sup_left) le_sup_right) ?_
  have h : L2 ⊔ S = perfectCore L2 ⊔ S := by
    calc L2 ⊔ S = (perfectCore L2 ⊔ pCoreOf 2 L2) ⊔ S := by rw [hsup]
      _ = perfectCore L2 ⊔ S := by rw [sup_assoc, sup_eq_right.mpr hO]
  rw [h]

private theorem isSylowTwoOf_S_bigB (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) :
    IsSylowTwoOf S (bigB L1 L2 S) := by
  have hB1 : borelOf L1 S = S ⊓ L1 := F112TitsSlice.borelOf_eq_vs3 hF.1.h1 h1
  have hbig : bigB L1 L2 S = borelOf L2 S ⊔ S := by
    change borelOf L1 S ⊔ borelOf L2 S ⊔ S = borelOf L2 S ⊔ S
    rw [hB1]
    calc (S ⊓ L1) ⊔ borelOf L2 S ⊔ S
        = (S ⊓ L1) ⊔ (borelOf L2 S ⊔ S) := by rw [sup_assoc]
      _ = borelOf L2 S ⊔ S := by
          rw [sup_eq_right.mpr (inf_le_left.trans le_sup_right)]
  have hS2syl : IsSylowTwoOf (S ⊓ L2) (borelOf L2 S) :=
    F7.isSylowTwoOf_mono_right hF.1.h2.sylow (F1.sylow_le_borelOf L2 S) (F1.borelOf_le L2 S)
  have hN : ¬ 2 ∣ (borelOf L2 S ⊓ S).relIndex (borelOf L2 S) := by
    have hle : S ⊓ L2 ≤ borelOf L2 S ⊓ S := le_inf (F1.sylow_le_borelOf L2 S) inf_le_left
    intro hd
    exact F7.isSylowTwoOf_odd_relIndex hS2syl
      (hd.trans (Subgroup.relIndex_dvd_of_le_left (borelOf L2 S) hle))
  have hSyl : IsSylowTwoOf S (borelOf L2 S ⊔ S) :=
    F112W.isSylowTwoOf_sup (N := borelOf L2 S) (B := S) (T := S)
      (F1.le_normalizer_borelOf hF.1.h2.normalizes)
      ⟨le_rfl, hF.1.h1.pgroup, by
        show ¬ 2 ∣ S.relIndex S
        rw [Subgroup.relIndex_self]
        norm_num⟩ hN
  rwa [hbig]

private theorem isSylowTwoOf_S_P1 (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) :
    IsSylowTwoOf S (L1 ⊔ bigB L1 L2 S) := by
  have hN : ¬ 2 ∣ (L1 ⊓ bigB L1 L2 S).relIndex L1 := by
    have hle : S ⊓ L1 ≤ L1 ⊓ bigB L1 L2 S :=
      le_inf inf_le_right (inf_le_left.trans le_sup_right)
    intro hd
    exact F7.isSylowTwoOf_odd_relIndex hF.1.h1.sylow
      (hd.trans (Subgroup.relIndex_dvd_of_le_left L1 hle))
  exact F112W.isSylowTwoOf_sup (N := L1) (B := bigB L1 L2 S) (T := S)
    (bigB_le_normalizer_of_hyp111 hF.1) (isSylowTwoOf_S_bigB hF h1) hN

private theorem pCoreOf_P1_le_S (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) :
    pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ S :=
  St84.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_S_P1 hF h1)

private theorem pCoreOf_L1'_eq (hF : F112Hyp L1 L2 S) :
    pCoreOf 2 (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) =
      pCoreOf 2 (L1 ⊔ bigB L1 L2 S) :=
  St84.pCoreOf_sup_pCoreOf le_sup_left
    (sup_le Subgroup.le_normalizer (bigB_le_normalizer_of_hyp111 hF.1))

private theorem P1_le_normalizer_L1' (hF : F112Hyp L1 L2 S) :
    L1 ⊔ bigB L1 L2 S ≤
      Subgroup.normalizer ((L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S) : Subgroup G) : Set G) :=
  (le_inf (sup_le Subgroup.le_normalizer (bigB_le_normalizer_of_hyp111 hF.1))
    (le_normalizer_pCoreOf (r := 2) (H := L1 ⊔ bigB L1 L2 S))).trans
    (Subgroup.inf_normalizer_le_normalizer_sup _ _)

private theorem S_le_normalizer_L1' (hF : F112Hyp L1 L2 S) :
    S ≤ Subgroup.normalizer ((L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S) : Subgroup G) : Set G) :=
  ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right).trans (P1_le_normalizer_L1' hF)

private theorem S_le_normalizer_perfectCore (hF : F112Hyp L1 L2 S) :
    S ≤ Subgroup.normalizer (perfectCore L2 : Set G) :=
  hF.1.h2.normalizes.trans (normalizer_le_normalizer_perfectCore L2)

private theorem isSylowTwoOf_inf_L1' (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) :
    IsSylowTwoOf (S ⊓ (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)))
      (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) := by
  have h := CFSG.isSylowTwoOf_inf_of_normal (S := S) (X := L1 ⊔ bigB L1 L2 S)
    (N := L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) (isSylowTwoOf_S_P1 hF h1)
    (sup_le le_sup_left (pCoreOf_le 2 (L1 ⊔ bigB L1 L2 S)))
    (P1_le_normalizer_L1' hF)
  simpa [inf_comm] using h

private theorem isSolvable_L1_sup_S (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) :
    Group.IsSolvable ↥(L1 ⊔ S) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsSolvable ↥L1 := H13.S125Gam.isSolvable_of_perm3 h1
  haveI : Group.IsSolvable ↥S := by
    haveI : Group.IsNilpotent ↥S := hF.1.h1.pgroup.isNilpotent
    infer_instance
  exact A3.isSolvable_sup_of_le_normalizer hF.1.h1.normalizes

private theorem oTwoQuot_L1'_mulEquiv (hF : F112Hyp L1 L2 S) :
    Nonempty (oTwoQuot ↥L1 ≃* oTwoQuot ↥(L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S))) := by
  have hle : L1 ≤ L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S) := le_sup_left
  have hnorm : (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ≤
      Subgroup.normalizer (L1 : Set G) :=
    (sup_le le_sup_left (pCoreOf_le 2 (L1 ⊔ bigB L1 L2 S))).trans
      (sup_le Subgroup.le_normalizer (bigB_le_normalizer_of_hyp111 hF.1))
  have hsup : L1 ⊔ pCoreOf 2 (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) =
      L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S) := by rw [pCoreOf_L1'_eq hF]
  exact St84.pCore_quotient_mulEquiv_of_sup_pCoreOf hle hnorm hsup

private theorem vs3_L1' (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) :
    VS3 (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) := by
  obtain ⟨e⟩ := oTwoQuot_L1'_mulEquiv hF
  obtain ⟨e1⟩ := h1
  exact ⟨e.symm.trans e1⟩

private theorem isL2Quot_one_L1' (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) :
    IsL2Quot 1 (oTwoQuot ↥(L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S))) := by
  have h1q : IsL2Quot 1 (oTwoQuot ↥L1) := isL2Quot_one_iff_perm3.mpr h1
  obtain ⟨e⟩ := oTwoQuot_L1'_mulEquiv hF
  obtain ⟨e1⟩ := h1q
  exact ⟨e.symm.trans e1⟩

private theorem isRankOneListed_L1' (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) :
    IsRankOneListed (oTwoQuot ↥(L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S))) := by
  obtain ⟨e⟩ := isL2Quot_one_L1' hF h1
  exact Or.inl ⟨1, le_rfl, ⟨e⟩⟩

private theorem isRankOneListed_perfectCore (hn : 2 ≤ n) (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    IsRankOneListed (OTwoQuot (perfectCore L2)) := by
  obtain ⟨e⟩ := isL2Quot_perfectCore hn h2
  exact Or.inl ⟨n, by omega, ⟨e⟩⟩

private theorem inf_S_L2_eq (hF : F112Hyp L1 L2 S) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    S ⊓ L2 = (S ⊓ perfectCore L2) ⊔ pCoreOf 2 L2 := by
  have hsup := sup_perfectCore_pCoreOf_eq hn h2
  have hO : pCoreOf 2 L2 ≤ S := pCoreOf_L2_le_S hF
  have hnorm : pCoreOf 2 L2 ≤ Subgroup.normalizer (perfectCore L2 : Set G) :=
    (pCoreOf_le 2 L2).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (perfectCore_le L2)).mp
        (perfectCore_normal L2))
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxS, hxL2⟩ := Subgroup.mem_inf.mp hx
    have hxmem : x ∈ perfectCore L2 ⊔ pCoreOf 2 L2 := by rw [hsup]; exact hxL2
    obtain ⟨k, hkK, o, hOo, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hnorm).mp hxmem
    have hk : k = (k * o) * o⁻¹ := by group
    have hkS : k ∈ S := by
      rw [hk]
      exact S.mul_mem hxS (S.inv_mem (hO hOo))
    exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hkS, hkK⟩) hOo
  · exact sup_le (le_inf inf_le_left (inf_le_right.trans (perfectCore_le L2)))
      (le_inf hO (pCoreOf_le 2 L2))

private theorem L2_eq_perfectCore_sup_inf (hF : F112Hyp L1 L2 S) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    L2 = perfectCore L2 ⊔ (S ⊓ L2) := by
  calc L2 = perfectCore L2 ⊔ pCoreOf 2 L2 := (sup_perfectCore_pCoreOf_eq hn h2).symm
    _ = (perfectCore L2 ⊔ (S ⊓ perfectCore L2)) ⊔ pCoreOf 2 L2 := by
        rw [show perfectCore L2 ⊔ (S ⊓ perfectCore L2) = perfectCore L2 from
          sup_eq_left.mpr inf_le_right]
    _ = perfectCore L2 ⊔ ((S ⊓ perfectCore L2) ⊔ pCoreOf 2 L2) := by rw [sup_assoc]
    _ = perfectCore L2 ⊔ (S ⊓ L2) := by rw [← inf_S_L2_eq hF hn h2]

private theorem borelOf_perfectCore_le (hF : F112Hyp L1 L2 S) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    borelOf (perfectCore L2) S ≤ borelOf L2 S := by
  intro x hx
  obtain ⟨hxK, hxN⟩ := Subgroup.mem_inf.mp hx
  refine Subgroup.mem_inf.mpr ⟨(perfectCore_le L2) hxK, ?_⟩
  rw [inf_S_L2_eq hF hn h2]
  refine (Subgroup.inf_normalizer_le_normalizer_sup (S ⊓ perfectCore L2) (pCoreOf 2 L2))
    (Subgroup.mem_inf.mpr ⟨hxN, ?_⟩)
  exact ((perfectCore_le L2).trans (le_normalizer_pCoreOf 2 L2)) hxK

private theorem borelOf_L2_le (hF : F112Hyp L1 L2 S) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    borelOf L2 S ≤ borelOf (perfectCore L2) S ⊔ S := by
  intro x hx
  obtain ⟨hxL2, hxN⟩ := Subgroup.mem_inf.mp hx
  have hsup := L2_eq_perfectCore_sup_inf hF hn h2
  have hnorm : S ⊓ L2 ≤ Subgroup.normalizer (perfectCore L2 : Set G) :=
    inf_le_right.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (perfectCore_le L2)).mp
        (perfectCore_normal L2))
  have hxmem : x ∈ perfectCore L2 ⊔ (S ⊓ L2) := by rw [← hsup]; exact hxL2
  obtain ⟨k, hkK, s, hsS, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hnorm).mp hxmem
  have hsS' : s ∈ S := hsS.1
  have hk_borel : k ∈ borelOf (perfectCore L2) S := by
    refine Subgroup.mem_inf.mpr ⟨hkK, ?_⟩
    have hk_norm_L2 : k ∈ Subgroup.normalizer (S ⊓ L2 : Subgroup G) := by
      have hsN : s ∈ Subgroup.normalizer (S ⊓ L2 : Subgroup G) := Subgroup.le_normalizer hsS
      have hmem : (k * s) * s⁻¹ ∈ Subgroup.normalizer (S ⊓ L2 : Subgroup G) :=
        Subgroup.mul_mem _ hxN (Subgroup.inv_mem _ hsN)
      have hk : k = (k * s) * s⁻¹ := by group
      rwa [hk]
    have hk_norm_K : k ∈ Subgroup.normalizer (perfectCore L2 : Set G) :=
      Subgroup.le_normalizer hkK
    have hEq : (S ⊓ L2) ⊓ perfectCore L2 = S ⊓ perfectCore L2 := by
      rw [inf_assoc, inf_comm (L2) (perfectCore L2), inf_eq_left.mpr (perfectCore_le L2)]
    rw [← hEq]
    exact (Subgroup.inf_normalizer_le_normalizer_inf (H := S ⊓ L2)
      (K := perfectCore L2)) (Subgroup.mem_inf.mpr ⟨hk_norm_L2, hk_norm_K⟩)
  exact (borelOf (perfectCore L2) S ⊔ S).mul_mem (Subgroup.mem_sup_left hk_borel)
    (Subgroup.mem_sup_right hsS')

private theorem borelOf_perfectCore_sup_S_eq (hF : F112Hyp L1 L2 S) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    borelOf (perfectCore L2) S ⊔ S = borelOf L2 S ⊔ S :=
  le_antisymm (sup_le_sup_right (borelOf_perfectCore_le hF hn h2) S)
    (sup_le (borelOf_L2_le hF hn h2) le_sup_right)

private theorem borelOf_L2_le_normalizer_L1' (hF : F112Hyp L1 L2 S) :
    borelOf L2 S ≤
      Subgroup.normalizer ((L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S) : Subgroup G) : Set G) :=
  F1.le_normalizer_sup hF.1.h1.borel_le
    (((le_sup_right : borelOf L2 S ≤ borelOf L1 S ⊔ borelOf L2 S).trans le_sup_left).trans
      ((le_sup_right : bigB L1 L2 S ≤ L1 ⊔ bigB L1 L2 S).trans
        (le_normalizer_pCoreOf 2 (L1 ⊔ bigB L1 L2 S))))

private theorem charTwo_L1' (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    CharTwo ((L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ⊔ S ⊔
      borelOf (perfectCore L2) S) := by
  have hQ : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ S := pCoreOf_P1_le_S hF h1
  have hL1'S : (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ⊔ S = L1 ⊔ S := by
    rw [sup_assoc, sup_eq_right.mpr hQ]
  have hBS : borelOf (perfectCore L2) S ⊔ S = borelOf L2 S ⊔ S :=
    borelOf_perfectCore_sup_S_eq hF hn h2
  have hS' : S ⊔ borelOf (perfectCore L2) S = S ⊔ borelOf L2 S := by
    rw [sup_comm, hBS, sup_comm]
  have hEq : (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ⊔ S ⊔
      borelOf (perfectCore L2) S = L1 ⊔ S ⊔ borelOf L2 S := by
    rw [hL1'S]
    calc L1 ⊔ S ⊔ borelOf (perfectCore L2) S
        = L1 ⊔ (S ⊔ borelOf (perfectCore L2) S) := by rw [sup_assoc]
      _ = L1 ⊔ (S ⊔ borelOf L2 S) := by rw [hS']
      _ = L1 ⊔ S ⊔ borelOf L2 S := by rw [sup_assoc]
  rw [hEq]
  exact hF.1.h1.charTwo

private theorem hyp111At_L1' (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    Hyp111At (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) (perfectCore L2) S where
  finite := hF.1.h1.finite
  pgroup := hF.1.h1.pgroup
  normalizes := S_le_normalizer_L1' hF
  sylow := isSylowTwoOf_inf_L1' hF h1
  listed := isRankOneListed_L1' hF h1
  borel_le := (borelOf_perfectCore_le hF hn h2).trans (borelOf_L2_le_normalizer_L1' hF)
  charTwo := charTwo_L1' hF h1 hn h2

private theorem borelOf_L1'_le_S (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    borelOf (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) S ≤ S := by
  rw [F112TitsSlice.borelOf_eq_vs3 (hyp111At_L1' hF h1 hn h2) (vs3_L1' hF h1)]
  exact inf_le_left

private theorem charTwo_K1 (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    CharTwo (perfectCore L2 ⊔ S ⊔
      borelOf (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) S) := by
  have hB1' : borelOf (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) S ≤ S :=
    borelOf_L1'_le_S hF h1 hn h2
  have hKS : perfectCore L2 ⊔ S = L2 ⊔ S := perfectCore_sup_S_eq hF hn h2
  have hB1 : borelOf L1 S ≤ S := by
    rw [F112TitsSlice.borelOf_eq_vs3 hF.1.h1 h1]
    exact inf_le_left
  have hEq : perfectCore L2 ⊔ S ⊔
      borelOf (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) S = L2 ⊔ S ⊔ borelOf L1 S := by
    rw [hKS]
    rw [sup_assoc, sup_eq_left.mpr hB1', sup_assoc, sup_eq_left.mpr hB1]
  rw [hEq]
  exact hF.1.h2.charTwo

private theorem hyp111At_K1 (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    Hyp111At (perfectCore L2) (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) S where
  finite := hF.1.h1.finite
  pgroup := hF.1.h1.pgroup
  normalizes := S_le_normalizer_perfectCore hF
  sylow := isSylowTwoOf_inf_perfectCore hF
  listed := isRankOneListed_perfectCore hn h2
  borel_le := (borelOf_L1'_le_S hF h1 hn h2).trans (S_le_normalizer_perfectCore hF)
  charTwo := charTwo_K1 hF h1 hn h2

private theorem sup_K1_L1'_S_eq (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    perfectCore L2 ⊔ (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ⊔ S = L1 ⊔ L2 ⊔ S := by
  have hKS : perfectCore L2 ⊔ S = L2 ⊔ S := perfectCore_sup_S_eq hF hn h2
  have hQ : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ S := pCoreOf_P1_le_S hF h1
  calc perfectCore L2 ⊔ (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ⊔ S
      = perfectCore L2 ⊔ (L1 ⊔ S) := by
          rw [sup_assoc, sup_assoc, sup_eq_right.mpr hQ]
    _ = L1 ⊔ (perfectCore L2 ⊔ S) := by ac_rfl
    _ = L1 ⊔ (L2 ⊔ S) := by rw [hKS]
    _ = L1 ⊔ L2 ⊔ S := by rw [sup_assoc]

private theorem hyp111_of_zData (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    Hyp111 (perfectCore L2) (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) S where
  h1 := hyp111At_K1 hF h1 hn h2
  h2 := hyp111At_L1' hF h1 hn h2
  o2 := by
    rw [sup_K1_L1'_S_eq hF h1 hn h2]
    exact hF.1.o2

private theorem isQuasithinSub_of_zData (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    IsQuasithinSub (perfectCore L2 ⊔ (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ⊔ S) := by
  rw [sup_K1_L1'_S_eq hF h1 hn h2]
  exact hF.2.1

private theorem mem_cComp_perfectCore (hF : F112Hyp L1 L2 S) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    perfectCore L2 ∈ cComp (perfectCore L2 ⊔ S) := by
  have hperf : ⁅perfectCore L2, perfectCore L2⁆ = perfectCore L2 := perfectCore_perfect L2
  have hne : perfectCore L2 ≠ ⊥ := by
    intro hbot
    have hsolv : Group.IsSolvable ↥(perfectCore L2) := by rw [hbot]; infer_instance
    exact not_isSolvable_of_isL2Quot hn (isL2Quot_perfectCore hn h2) hsolv
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hsimple : IsSimpleGroup (OTwoQuot (perfectCore L2)) := by
    obtain ⟨e⟩ := isL2Quot_perfectCore hn h2
    have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
    have h4 : 4 ≤ Nat.card (GaloisField 2 n) := by
      rw [hcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
    exact e.isSimpleGroup
  have hker : Group.IsSolvable ↥(QuotientGroup.mk' (CFSG.pCore 2 ↥(perfectCore L2))).ker := by
    rw [QuotientGroup.ker_mk']
    haveI : Group.IsNilpotent ↥(CFSG.pCore 2 ↥(perfectCore L2)) :=
      (CFSG.pCore_isPGroup (G := ↥(perfectCore L2)) (p := 2)).isNilpotent
    infer_instance
  have hmem : perfectCore L2 ∈ cComp (perfectCore L2) :=
    S151S9U.mem_cComp_self_of_simple_quotient
      (ψ := QuotientGroup.mk' (CFSG.pCore 2 ↥(perfectCore L2)))
      (QuotientGroup.mk'_surjective _) hne hperf hker
  exact SBd5.mem_cComp_sup' hmem (S_le_normalizer_perfectCore hF)

private theorem conjClosure_L1'_eq (hF : F112Hyp L1 L2 S) (h1 : VS3 L1)
    (hZ : S3L2ZData L1 L2 S Z) :
    conjClosure Z (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) = conjClosure Z L1 := by
  have hQ : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ S := pCoreOf_P1_le_S hF h1
  have hSZ : S ≤ Subgroup.centralizer (Z : Set G) := Subgroup.le_centralizer_iff.mp hZ.Z_cent_S
  have hnorm : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ Subgroup.normalizer (L1 : Set G) :=
    (pCoreOf_le 2 (L1 ⊔ bigB L1 L2 S)).trans
      (sup_le Subgroup.le_normalizer (bigB_le_normalizer_of_hyp111 hF.1))
  refine le_antisymm ?_ (conjClosure_mono le_rfl le_sup_left)
  refine conjClosure_le fun x hx z hz => ?_
  obtain ⟨l, hl, q, hq, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hnorm).mp hx
  have hqZ : q * z * q⁻¹ = z := by
    have hc : z * q = q * z := (Subgroup.mem_centralizer_iff.mp (hSZ (hQ hq)) z hz)
    rw [← hc]
    group
  have hconj : l * q * z * (l * q)⁻¹ = l * z * l⁻¹ := by
    rw [mul_inv_rev]
    calc l * q * z * (q⁻¹ * l⁻¹) = l * (q * z * q⁻¹) * l⁻¹ := by group
      _ = l * z * l⁻¹ := by rw [hqZ]
  rw [hconj]
  exact mem_conjClosure hl hz

private theorem Z_le_L1' (hF : F112Hyp L1 L2 S) (hZ : S3L2ZData L1 L2 S Z) :
    Z ≤ pCoreOf 2 (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) := by
  rw [pCoreOf_L1'_eq hF]
  exact hZ.Z_le

private theorem Z_cent_pCoreOf_L1' (hF : F112Hyp L1 L2 S) (h1 : VS3 L1)
    (hZ : S3L2ZData L1 L2 S Z) :
    Z ≤ Subgroup.centralizer
      (pCoreOf 2 (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) : Set G) := by
  rw [pCoreOf_L1'_eq hF]
  exact hZ.Z_cent_S.trans (Subgroup.centralizer_le (pCoreOf_P1_le_S hF h1))

private theorem Z_not_norm_L1' (hZ : S3L2ZData L1 L2 S Z) :
    ¬ (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ≤ Subgroup.normalizer (Z : Set G) := by
  intro hle
  have hL1N : L1 ≤ Subgroup.normalizer (Z : Set G) := le_sup_left.trans hle
  have hEq : conjClosure Z L1 = Z := by
    refine le_antisymm ?_ (le_conjClosure Z L1)
    exact conjClosure_le fun l hl z hz => (Subgroup.mem_normalizer_iff.mp (hL1N hl) z).mp hz
  have hcard := hZ.V_card
  rw [hEq, hZ.card_Z] at hcard
  omega

private theorem V_le_perfectCore (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) (hZ : S3L2ZData L1 L2 S Z) :
    conjClosure Z (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ≤
      pCoreOf 2 (perfectCore L2 ⊔ S) := by
  rw [conjClosure_L1'_eq hF h1 hZ]
  have hB1 : borelOf L1 S = S ⊓ L1 := F112TitsSlice.borelOf_eq_vs3 hF.1.h1 h1
  have hbig : bigB L1 L2 S = borelOf L2 S ⊔ S := by
    change borelOf L1 S ⊔ borelOf L2 S ⊔ S = borelOf L2 S ⊔ S
    rw [hB1]
    calc (S ⊓ L1) ⊔ borelOf L2 S ⊔ S
        = (S ⊓ L1) ⊔ (borelOf L2 S ⊔ S) := by rw [sup_assoc]
      _ = borelOf L2 S ⊔ S := by
          rw [sup_eq_right.mpr (inf_le_left.trans le_sup_right)]
  have hP2 : L2 ⊔ bigB L1 L2 S = L2 ⊔ S := by
    rw [hbig, ← sup_assoc, sup_eq_left.mpr (F1.borelOf_le L2 S)]
  have hKS : perfectCore L2 ⊔ S = L2 ⊔ S := perfectCore_sup_S_eq hF hn h2
  rw [hKS, ← hP2]
  exact hZ.V_le

theorem perfectCore_sup_bigB_eq
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    perfectCore L2 ⊔ bigB (perfectCore L2) (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) S =
      L2 ⊔ bigB L2 L1 S := by
  have hB1 : borelOf L1 S = S ⊓ L1 := F112TitsSlice.borelOf_eq_vs3 hF.1.h1 h1
  have hB1' : borelOf (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) S ≤ S :=
    borelOf_L1'_le_S hF h1 hn h2
  have hbig1 : bigB (perfectCore L2) (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) S =
      borelOf (perfectCore L2) S ⊔ S := by
    change borelOf (perfectCore L2) S ⊔
      borelOf (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) S ⊔ S =
        borelOf (perfectCore L2) S ⊔ S
    calc borelOf (perfectCore L2) S ⊔
          borelOf (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) S ⊔ S
        = borelOf (perfectCore L2) S ⊔
            (borelOf (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) S ⊔ S) := by rw [sup_assoc]
      _ = borelOf (perfectCore L2) S ⊔ S := by rw [sup_eq_right.mpr hB1']
  have hbig2 : bigB L2 L1 S = borelOf L2 S ⊔ S := by
    change borelOf L2 S ⊔ borelOf L1 S ⊔ S = borelOf L2 S ⊔ S
    rw [hB1]
    calc borelOf L2 S ⊔ (S ⊓ L1) ⊔ S
        = borelOf L2 S ⊔ ((S ⊓ L1) ⊔ S) := by rw [sup_assoc]
      _ = borelOf L2 S ⊔ S := by
          rw [show (S ⊓ L1) ⊔ S = S from sup_eq_right.mpr inf_le_left]
  have hKS : perfectCore L2 ⊔ S = L2 ⊔ S := perfectCore_sup_S_eq hF hn h2
  calc perfectCore L2 ⊔ bigB (perfectCore L2) (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) S
      = perfectCore L2 ⊔ (borelOf (perfectCore L2) S ⊔ S) := by rw [hbig1]
    _ = L2 ⊔ S := by
        rw [← sup_assoc, sup_eq_left.mpr (F1.borelOf_le (perfectCore L2) S), hKS]
    _ = L2 ⊔ (borelOf L2 S ⊔ S) := by
        rw [← sup_assoc, sup_eq_left.mpr (F1.borelOf_le L2 S)]
    _ = L2 ⊔ bigB L2 L1 S := by rw [← hbig2]

theorem sup_pCoreOf_sup_bigB_eq
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ⊔
        bigB (perfectCore L2) (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) S =
      L1 ⊔ bigB L2 L1 S := by
  have hB1 : borelOf L1 S = S ⊓ L1 := F112TitsSlice.borelOf_eq_vs3 hF.1.h1 h1
  have hB1' : borelOf (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) S ≤ S :=
    borelOf_L1'_le_S hF h1 hn h2
  have hQ : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ S := pCoreOf_P1_le_S hF h1
  have hbig1 : bigB (perfectCore L2) (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) S =
      borelOf (perfectCore L2) S ⊔ S := by
    change borelOf (perfectCore L2) S ⊔
      borelOf (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) S ⊔ S =
        borelOf (perfectCore L2) S ⊔ S
    calc borelOf (perfectCore L2) S ⊔
          borelOf (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) S ⊔ S
        = borelOf (perfectCore L2) S ⊔
            (borelOf (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) S ⊔ S) := by rw [sup_assoc]
      _ = borelOf (perfectCore L2) S ⊔ S := by rw [sup_eq_right.mpr hB1']
  have hbig2 : bigB L2 L1 S = borelOf L2 S ⊔ S := by
    change borelOf L2 S ⊔ borelOf L1 S ⊔ S = borelOf L2 S ⊔ S
    rw [hB1]
    calc borelOf L2 S ⊔ (S ⊓ L1) ⊔ S
        = borelOf L2 S ⊔ ((S ⊓ L1) ⊔ S) := by rw [sup_assoc]
      _ = borelOf L2 S ⊔ S := by
          rw [show (S ⊓ L1) ⊔ S = S from sup_eq_right.mpr inf_le_left]
  have hBS : borelOf (perfectCore L2) S ⊔ S = borelOf L2 S ⊔ S :=
    borelOf_perfectCore_sup_S_eq hF hn h2
  calc (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ⊔
        bigB (perfectCore L2) (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) S
      = (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ⊔
          (borelOf (perfectCore L2) S ⊔ S) := by rw [hbig1]
    _ = L1 ⊔ (pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ⊔
          (borelOf (perfectCore L2) S ⊔ S)) := by rw [sup_assoc]
    _ = L1 ⊔ (pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ⊔ (borelOf L2 S ⊔ S)) := by rw [hBS]
    _ = L1 ⊔ (borelOf L2 S ⊔ S) := by
        rw [show pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ⊔ (borelOf L2 S ⊔ S) =
          borelOf L2 S ⊔ S from sup_eq_right.mpr (hQ.trans le_sup_right)]
    _ = L1 ⊔ bigB L2 L1 S := by rw [← hbig2]

theorem r1SettingLegacyBare_of_zData
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) (hZ : S3L2ZData L1 L2 S Z) :
    R1SettingLegacyBare (perfectCore L2) (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) S Z := by
  have hQ : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ S := pCoreOf_P1_le_S hF h1
  have hL1'S : (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ⊔ S = L1 ⊔ S := by
    rw [sup_assoc, sup_eq_right.mpr hQ]
  have hB1' : borelOf (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) S ≤ S :=
    borelOf_L1'_le_S hF h1 hn h2
  refine ⟨hyp111_of_zData hF h1 hn h2, isQuasithinSub_of_zData hF h1 hn h2, ?_,
    mem_cComp_perfectCore hF hn h2, vs3_L1' hF h1, hL1'S.symm ▸ isSolvable_L1_sup_S hF h1,
    hZ.card_Z, Z_le_L1' hF hZ, Z_cent_pCoreOf_L1' hF h1 hZ, Z_not_norm_L1' hZ,
    hZ.Z_cent_S, (perfectCore_le L2).trans hZ.L2_cent, V_le_perfectCore hF h1 hn h2 hZ, ?_⟩
  · have h : S ⊔ borelOf (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) S = S :=
      sup_eq_left.mpr hB1'
    rw [h, Subgroup.subgroupOf_self]
    infer_instance
  · rw [conjClosure_L1'_eq hF h1 hZ]
    exact hZ.V_card

theorem idS3L8_of_zData (hR1b : F112R1bLocStatement) (hZ : ZDataS3L8) : IdS3L8 := by
  intro G _ _ L1 L2 S hF h1 h3
  obtain ⟨Z, hZD, hΩ⟩ := hZ G L1 L2 S hF h1 h3
  have hset := r1SettingLegacyBare_of_zData hF h1 (by norm_num : 2 ≤ 3) h3 hZD
  have hA := (hR1b G (perfectCore L2) (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) S Z hset
    (fun _ => hΩ) (isL2Quot_perfectCore (by norm_num : 2 ≤ 3) h3)).1
  rw [perfectCore_sup_bigB_eq hF h1 (by norm_num : 2 ≤ 3) h3,
    sup_pCoreOf_sup_bigB_eq hF h1 (by norm_num : 2 ≤ 3) h3] at hA
  exact hA

theorem noS3L2Big_of_zData (hR1c : F112R1cStatementLegacyBare) (hZ : ZDataS3L2) :
    NoS3L2Big := by
  intro G _ _ L1 L2 S n hF h1 h4 hn
  obtain ⟨Z, hZD⟩ := hZ G L1 L2 S n hF h1 h4 hn
  have hset := r1SettingLegacyBare_of_zData hF h1 (by omega : 2 ≤ n) hn hZD
  have hbender : ∃ m : ℕ, 2 ≤ m ∧ IsBenderQuot m (OTwoQuot (perfectCore L2)) :=
    ⟨n, by omega, Or.inl (isL2Quot_perfectCore (by omega) hn)⟩
  have hnot2 : ¬ IsL2Quot 2 (OTwoQuot (perfectCore L2)) := by
    intro h2'
    have := H13.eq_of_isL2Quot (a := 2) (b := n) (by norm_num) (by omega) h2'
      (isL2Quot_perfectCore (by omega) hn)
    omega
  have hnot3 : ¬ IsL2Quot 3 (OTwoQuot (perfectCore L2)) := by
    intro h3'
    have := H13.eq_of_isL2Quot (a := 3) (b := n) (by norm_num) (by omega) h3'
      (isL2Quot_perfectCore (by omega) hn)
    omega
  exact hR1c G (perfectCore L2) (L1 ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) S Z hset hbender
    hnot2 hnot3

end CFSG.Quasithin.F112R
