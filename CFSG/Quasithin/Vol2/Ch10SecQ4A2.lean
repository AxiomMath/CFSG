module

public import CFSG.Quasithin.Background.A3ComponentsCore
public import CFSG.Quasithin.Background.Ordering
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks

section

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C1 CFSG.QuasithinUnique.C5

variable {G : Type*} [Group G] [Finite G] {K J : Subgroup G}

omit [Finite G] in
theorem commutator_mem_blockQ_of_pCoreOf (hKJ : K ≤ J)
    (hQK : pCoreOf 2 J ≤ Subgroup.normalizer (K : Set G)) {q : G} (hq : q ∈ pCoreOf 2 J)
    {k : G} (hk : k ∈ K) : q * k * q⁻¹ * k⁻¹ ∈ blockQ K := by
  have hPnorm : J ≤ Subgroup.normalizer (pCoreOf 2 J : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 J
  have hP2 : IsPGroup 2 (pCoreOf 2 J) := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 J
  have h1 : q * k * q⁻¹ * k⁻¹ ∈ K :=
    K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hQK hq) k).mp hk) (K.inv_mem hk)
  have h2 : q * k * q⁻¹ * k⁻¹ ∈ pCoreOf 2 J := by
    have h3 : k * q⁻¹ * k⁻¹ ∈ pCoreOf 2 J :=
      (Subgroup.mem_normalizer_iff.mp (hPnorm (hKJ hk)) q⁻¹).mp (Subgroup.inv_mem _ hq)
    have e : q * k * q⁻¹ * k⁻¹ = q * (k * q⁻¹ * k⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hq h3
  have hKP : K ⊓ pCoreOf 2 J ≤ blockQ K := by
    refine le_pCoreOf_of_normalized inf_le_left ?_ (hP2.to_le inf_le_right)
    intro g hg
    exact mem_normalizer_inf (Subgroup.le_normalizer hg) (hPnorm (hKJ hg))
  exact hKP ⟨h1, h2⟩

theorem commutator_mem_blockU_of_pCoreOf (hK : IsShort2 K) (hKJ : K ≤ J)
    (hQK : pCoreOf 2 J ≤ Subgroup.normalizer (K : Set G)) {q : G} (hq : q ∈ pCoreOf 2 J)
    {k : G} (hk : k ∈ K) : q * k * q⁻¹ * k⁻¹ ∈ blockU K :=
  commutator_mem_blockU_of_mem_blockQ hK
    (fun _ hl => commutator_mem_blockQ_of_pCoreOf hKJ hQK hq hl) k hk

theorem commute_blockU_of_pCoreOf (hK : IsShort2 K) (hKJ : K ≤ J)
    (hQK : pCoreOf 2 J ≤ Subgroup.normalizer (K : Set G)) {q : G} (hq : q ∈ pCoreOf 2 J) :
    ∀ u ∈ blockU K, u * q = q * u := by
  have hP2 : IsPGroup 2 (pCoreOf 2 J) := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 J
  obtain ⟨n, hn⟩ := hP2 ⟨q, hq⟩
  refine commute_blockU_of_mem hK (hQK hq) ⟨n, by simpa using congrArg Subtype.val hn⟩
    (fun _ hl => commutator_mem_blockQ_of_pCoreOf hKJ hQK hq hl)

theorem blockU_inf_pCoreOf (hK : IsShort2 K) (hZ : blockZ K = ⊥) (hKJ : K ≤ J) :
    blockU K ⊓ pCoreOf 2 J = ⊥ ∨ blockU K ≤ pCoreOf 2 J := by
  have hPnorm : J ≤ Subgroup.normalizer (pCoreOf 2 J : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 J
  rcases hK.2.2.2.2.2 (blockU K ⊓ pCoreOf 2 J) (by rw [hZ]; exact bot_le) inf_le_left
      (fun g hg => mem_normalizer_inf (le_normalizer_blockU K hg) (hPnorm (hKJ hg))) with h | h
  · left
    rw [h, hZ]
  · right
    rw [← h]
    exact inf_le_right

end CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

end

end

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C1

variable {G : Type*} [Group G] {K J X : Subgroup G}

theorem conjClosure_perfect (hK : ⁅K, K⁆ = K) :
    ⁅conjClosure K J, conjClosure K J⁆ = conjClosure K J := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    exact (conjClosure K J).mul_mem ((conjClosure K J).mul_mem ((conjClosure K J).mul_mem ha hb)
      ((conjClosure K J).inv_mem ha)) ((conjClosure K J).inv_mem hb)
  · refine conjClosure_le fun j hj k hk => ?_
    have hmap : K.map (MulAut.conj j).toMonoidHom ≤ conjClosure K J := by
      rintro _ ⟨x, hx, rfl⟩
      exact mem_conjClosure hj hx
    have hmem : j * k * j⁻¹ ∈ K.map (MulAut.conj j).toMonoidHom := ⟨k, hk, by simp⟩
    rw [← hK, Subgroup.map_commutator] at hmem
    exact Subgroup.commutator_mono hmap hmap hmem

theorem conjClosure_le_self (hKJ : K ≤ J) : conjClosure K J ≤ J :=
  conjClosure_le fun _ hj _ hk => J.mul_mem (J.mul_mem hj (hKJ hk)) (J.inv_mem hj)

theorem conjClosure_eq_of_mem_cComp (hJ : J ∈ cComp X) (hKJ : K ≤ J) (hK : ⁅K, K⁆ = K)
    (hK1 : K ≠ ⊥) : conjClosure K J = J := by
  have hle := conjClosure_le_self (J := J) hKJ
  by_contra hne
  have hN1 : conjClosure K J ≠ ⊥ := fun h => hK1 (le_bot_iff.mp (h ▸ le_conjClosure K J))
  have hnorm : ((conjClosure K J).subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr (le_normalizer_conjClosure K J)
  exact not_subnormal_of_mem_cComp hJ (lt_of_le_of_ne hle hne) hN1 (conjClosure_perfect hK)
    (A3.subnormal_trans (A3.subnormal_of_normal hle hnorm) (subnormal_of_mem_cComp hJ))

variable [Finite G] (hK : IsShort2 K) (hKJ : K ≤ J)
  (hQK : pCoreOf 2 J ≤ Subgroup.normalizer (K : Set G))
include hK hKJ hQK

theorem commutator_mem_blockU_of_pCoreOf' {x : G} (hx : x ∈ pCoreOf 2 J) {k : G} (hk : k ∈ K) :
    k * x * k⁻¹ * x⁻¹ ∈ blockU K := by
  have := Subgroup.inv_mem _ (commutator_mem_blockU_of_pCoreOf hK hKJ hQK hx hk)
  convert this using 1
  group

variable (hUQ : blockU K ≤ pCoreOf 2 J)
include hUQ

omit [Finite G] hK hKJ hQK in
theorem conjClosure_le_pCoreOf : conjClosure (blockU K) J ≤ pCoreOf 2 J := by
  have hPnorm : J ≤ Subgroup.normalizer (pCoreOf 2 J : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 J
  exact conjClosure_le fun j hj u hu => (Subgroup.mem_normalizer_iff.mp (hPnorm hj) u).mp (hUQ hu)

omit hUQ in
theorem conjClosure_le_centralizer :
    conjClosure (blockU K) J ≤ Subgroup.centralizer (pCoreOf 2 J : Set G) := by
  have hPnorm : J ≤ Subgroup.normalizer (pCoreOf 2 J : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 J
  refine conjClosure_le fun j hj u hu => Subgroup.mem_centralizer_iff.mpr fun q hq => ?_
  have hq' : j⁻¹ * q * j⁻¹⁻¹ ∈ pCoreOf 2 J :=
    (Subgroup.mem_normalizer_iff.mp (hPnorm (J.inv_mem hj)) q).mp hq
  have hc := commute_blockU_of_pCoreOf hK hKJ hQK hq' u hu
  rw [inv_inv] at hc
  calc q * (j * u * j⁻¹) = j * ((j⁻¹ * q * j) * u) * j⁻¹ := by group
    _ = j * (u * (j⁻¹ * q * j)) * j⁻¹ := by rw [← hc]
    _ = j * u * j⁻¹ * q := by group

theorem commute_of_mem_conjClosure {a b : G} (ha : a ∈ conjClosure (blockU K) J)
    (hb : b ∈ conjClosure (blockU K) J) : a * b = b * a :=
  (Subgroup.mem_centralizer_iff.mp (conjClosure_le_centralizer hK hKJ hQK ha) b
    (conjClosure_le_pCoreOf hUQ hb)).symm

theorem isElemAbelian_conjClosure : IsElemAbelian 2 (conjClosure (blockU K) J) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (commute_of_mem_conjClosure hK hKJ hQK hUQ a.2 b.2)⟩⟩,
    fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, -, u, hu, rfl⟩ := hx
    have hu2 : u ^ 2 = 1 := hK.2.2.1.2 u hu
    calc (j * u * j⁻¹) ^ 2 = j * u ^ 2 * j⁻¹ := by rw [sq, sq]; group
      _ = 1 := by rw [hu2]; group
  | one => simp
  | mul a b ha hb iha ihb =>
    have hab := commute_of_mem_conjClosure hK hKJ hQK hUQ ha hb
    rw [(Commute.mul_pow hab 2), iha, ihb, one_mul]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

end CFSG.Quasithin.Vol2.Ch10.SecF.C10E4
