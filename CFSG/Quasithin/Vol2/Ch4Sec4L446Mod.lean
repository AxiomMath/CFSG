module

public import CFSG.Quasithin.Vol2.Ch4Sec4W446
public import CFSG.Quasithin.Vol2.Ch4Sec4L446Nat
public import CFSG.Quasithin.Background.InternalSecFFB
public import CFSG.Quasithin.H13.A7Nat1238NQBase

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4
open scoped IsMulCommutative Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_of_isSylowTwoOf_of_le_normalizer {S N : Subgroup G} (hS : IsSylowTwoOf S N)
    (hNS : N ≤ Subgroup.normalizer (S : Set G)) {x : G} (hx : x ∈ N) {e : ℕ}
    (he : x ^ 2 ^ e = 1) : x ∈ S := by
  have hP : IsPGroup 2 ↥(Subgroup.zpowers x) := by
    rintro ⟨y, hy⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨e, Subtype.ext ?_⟩
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, he, one_zpow]
  have hPN : Subgroup.zpowers x ≤ N := Subgroup.zpowers_le.mpr hx
  have hsup : IsPGroup 2 ↥(Subgroup.zpowers x ⊔ S) :=
    hP.to_sup_of_normal_right' hS.2.1 (hPN.trans hNS)
  have h := (isSylowTwoOf_iff_maximal.mp hS).2.2 _ (_root_.sup_le hPN hS.1) hsup le_sup_right
  exact h (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))

theorem mem_of_pow_two_pow_mem {K : Subgroup G} {x : G} {k : ℕ} (hk : x ^ 2 ^ k ∈ K)
    (h2 : ∀ m e : ℕ, Odd m → (x ^ m) ^ 2 ^ e = 1 → x ^ m ∈ K) : x ∈ K := by
  obtain ⟨e, m, hm, he⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  have hxm : x ^ m ∈ K := h2 m e hm (by rw [← pow_mul, mul_comm, ← he, pow_orderOf_eq_one])
  have hcop : Nat.Coprime m (2 ^ k) := Nat.Coprime.pow_right k (Odd.coprime_two_right hm)
  have hbez := Nat.gcd_eq_gcd_ab m (2 ^ k)
  rw [hcop, Nat.cast_one] at hbez
  have e1 : x = (x ^ m) ^ Nat.gcdA m (2 ^ k) * (x ^ 2 ^ k) ^ Nat.gcdB m (2 ^ k) := by
    rw [← zpow_natCast x m, ← zpow_natCast x (2 ^ k), ← zpow_mul, ← zpow_mul, ← zpow_add,
      ← hbez, zpow_one]
  rw [e1]
  exact K.mul_mem (K.zpow_mem hxm _) (K.zpow_mem hk _)

theorem le_of_perfect_of_pow_mem {L K : Subgroup G} (hL : ⁅L, L⁆ = L)
    (hLK : L ≤ Subgroup.normalizer (K : Set G)) (h : ∀ l ∈ L, ∃ k : ℕ, l ^ 2 ^ k ∈ K) :
    L ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hL
  have : (K.subgroupOf L).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hLK
  have h2 : IsPGroup 2 (↥L ⧸ K.subgroupOf L) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H l =>
      obtain ⟨k, hk⟩ := h l l.2
      exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hk⟩
  have htop : K.subgroupOf L = ⊤ := by
    apply QuotientGroup.subgroup_eq_top_of_subsingleton
    by_contra hns
    have : Nontrivial (↥L ⧸ K.subgroupOf L) := not_subsingleton_iff_nontrivial.mp hns
    exact Group.IsPerfect.not_isNilpotent (↥L ⧸ K.subgroupOf L) h2.isNilpotent
  intro l hl
  have : (⟨l, hl⟩ : ↥L) ∈ K.subgroupOf L := by
    rw [htop]
    exact Subgroup.mem_top _
  exact this

namespace Hyp4_2_1

variable {T M L : Subgroup G} (h : Hyp4_2_1 G T M L)
include h

theorem inf_centralizer_le_centralizerSection (hn : M ≤ Subgroup.normalizer (L : Set G))
    {V : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hVL : ⁅V, L⁆ ≠ ⊥) :
    (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ centralizerSection M L (pCoreOf 2 L) := by
  set A₀ := (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) with hA₀
  set KL := L ⊓ Subgroup.centralizer (V : Set G) with hKL
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := h.sup_le.trans hn
  have hAL : A₀ ≤ Subgroup.normalizer (L : Set G) := inf_le_left.trans hLTN
  have hLA : L ≤ Subgroup.normalizer (A₀ : Set G) := fun l hl =>
    mem_normalizer_inf (Subgroup.le_normalizer (Subgroup.mem_sup_left hl))
      (mem_normalizer_centralizer_of_mem_normalizer (hLV hl))
  have hLKL : L ≤ Subgroup.normalizer (KL : Set G) := fun l hl =>
    mem_normalizer_inf (Subgroup.le_normalizer hl)
      (mem_normalizer_centralizer_of_mem_normalizer (hLV hl))
  have hKLne : KL ≠ L := by
    intro he
    apply hVL
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (he ▸ inf_le_right)
  have h1 : ⁅A₀, L⁆ ≤ KL := le_inf (commutator_le_right_of_le_normalizer hAL)
    ((commutator_le_left_of_le_normalizer hLA).trans inf_le_right)
  have h2 : ⁅KL, L⁆ ≤ pCoreOf 2 L :=
    commutator_le_pCoreOf_of_normal h.quasisimple h.perfect inf_le_left hLKL hKLne
  have h3 : ⁅A₀, L⁆ ≤ pCoreOf 2 L := by
    rw [commutator_eq_commutator_commutator_of_perfect h.perfect hAL hLA]
    exact (Subgroup.commutator_mono h1 le_rfl).trans h2
  intro a ha
  refine mem_centralizerSection.mpr ⟨h.sup_le ha.1, hAL ha,
    normalizer_le_normalizer_pCoreOf 2 L (hAL ha), fun l hl => ?_⟩
  have hc : ⁅l, a⁆ ∈ ⁅A₀, L⁆ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hl ha
  exact h3 hc

theorem mem_pCoreOf_of_mem_centralizerSection (hn : M ≤ Subgroup.normalizer (L : Set G))
    {x : G} (hx : x ∈ L ⊔ T) (hxC : x ∈ centralizerSection M L (pCoreOf 2 L)) {e : ℕ}
    (he : x ^ 2 ^ e = 1) : x ∈ pCoreOf 2 (L ⊔ T) := by
  set C := centralizerSection M L (pCoreOf 2 L) with hC
  set N := (L ⊔ T) ⊓ C with hN
  have hTsyl : IsSylowTwoOf T (L ⊔ T) := isSylowTwoOf_of_le h.sylow le_sup_right
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (N : Set G) := fun g hg =>
    mem_normalizer_inf (Subgroup.le_normalizer hg)
      (le_normalizer_centralizerSection M L ⟨h.sup_le hg, (h.sup_le.trans hn) hg⟩)
  have hS : IsSylowTwoOf (T ⊓ N) N :=
    A4.isSylowTwoOf_inf_normal hTsyl inf_le_left hLTN
  have hTN : T ⊓ N = pCoreOf 2 (L ⊔ T) := by
    rw [h.pCoreOf_sup_eq hn, hN, ← inf_assoc, inf_eq_left.mpr (le_sup_right : T ≤ L ⊔ T)]
  rw [hTN] at hS
  exact mem_of_isSylowTwoOf_of_le_normalizer hS
    (inf_le_left.trans (le_normalizer_pCoreOf 2 (L ⊔ T))) ⟨hx, hxC⟩ he

theorem isTwoReducedIn_of_le_omegaOneCenter (hn : M ≤ Subgroup.normalizer (L : Set G))
    {V : Subgroup G} (hV : V ≤ quasithinOmegaOneCenter (pCoreOf 2 (L ⊔ T)))
    (hVN : L ⊔ T ≤ Subgroup.normalizer (V : Set G)) (hVL : ⁅V, L⁆ ≠ ⊥) :
    IsTwoReducedIn (L ⊔ T) V := by
  have hVO := fun v (hv : v ∈ V) => mem_quasithinOmegaOneCenter_iff.mp (hV hv)
  have hVLT : V ≤ L ⊔ T := fun v hv => pCoreOf_le 2 _ (hVO v hv).1
  have hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp (hVO b hb).2.1 a (hVO a ha).1
  have hVel : IsElemAbelian 2 V :=
    ⟨⟨⟨fun x y => Subtype.ext (hVcomm _ x.2 _ y.2)⟩⟩, fun v hv => (hVO v hv).2.2⟩
  have hO2C : pCoreOf 2 (L ⊔ T) ≤ Subgroup.centralizer (V : Set G) := fun q hq =>
    Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (Subgroup.mem_centralizer_iff.mp (hVO v hv).2.1 q hq).symm
  refine ⟨hVLT, hVN, hVel, fun D hDLT hDN hD2 => ?_⟩
  have hLD : L ≤ Subgroup.normalizer (D : Set G) := le_sup_left.trans hDN
  have hDL : D ≤ Subgroup.normalizer (L : Set G) := hDLT.trans (h.sup_le.trans hn)
  have hLC : L ≤ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) := fun l hl =>
    mem_normalizer_centralizer_of_mem_normalizer (hVN (Subgroup.mem_sup_left hl))
  have hDLc : ⁅D, L⁆ ≤ pCoreOf 2 L := by
    by_cases hcase : D ⊓ L = L
    · exfalso
      have hLD' : L ≤ D := hcase ▸ inf_le_left
      have hLV : L ≤ Subgroup.centralizer (V : Set G) :=
        le_of_perfect_of_pow_mem h.perfect hLC fun l hl => hD2 l (hLD' hl)
      apply hVL
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hLV
    · have h1 : ⁅D, L⁆ ≤ D ⊓ L :=
        le_inf (commutator_le_left_of_le_normalizer hLD) (commutator_le_right_of_le_normalizer hDL)
      have h2 : ⁅D ⊓ L, L⁆ ≤ pCoreOf 2 L :=
        commutator_le_pCoreOf_of_normal h.quasisimple h.perfect inf_le_right
          (fun l hl => mem_normalizer_inf (hLD hl) (Subgroup.le_normalizer hl)) hcase
      rw [commutator_eq_commutator_commutator_of_perfect h.perfect hDL hLD]
      exact (Subgroup.commutator_mono h1 le_rfl).trans h2
  have hDC : D ≤ centralizerSection M L (pCoreOf 2 L) := fun d hd =>
    mem_centralizerSection.mpr ⟨h.sup_le (hDLT hd), hDL hd,
      normalizer_le_normalizer_pCoreOf 2 L (hDL hd), fun l hl => hDLc (by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator hl hd)⟩
  intro d hd
  obtain ⟨k, hk⟩ := hD2 d hd
  exact mem_of_pow_two_pow_mem hk fun m e _ hme =>
    hO2C (h.mem_pCoreOf_of_mem_centralizerSection hn (hDLT (D.pow_mem hd m))
      (hDC (D.pow_mem hd m)) hme)

theorem le_commutator_reducedAggregate (hn : M ≤ Subgroup.normalizer (L : Set G))
    {V : Subgroup G} (hV : V ≤ quasithinOmegaOneCenter (pCoreOf 2 (L ⊔ T)))
    (hVN : L ⊔ T ≤ Subgroup.normalizer (V : Set G)) (hVeq : V = ⁅V, L⁆) (hV1 : V ≠ ⊥) :
    V ≤ ⁅reducedAggregate (L ⊔ T), L⁆ := by
  have hVL : ⁅V, L⁆ ≠ ⊥ := hVeq ▸ hV1
  have hred := h.isTwoReducedIn_of_le_omegaOneCenter hn hV hVN hVL
  calc V = ⁅V, L⁆ := hVeq
    _ ≤ ⁅reducedAggregate (L ⊔ T), L⁆ :=
      Subgroup.commutator_mono (A7.le_reducedAggregate_of_isTwoReducedIn hred) le_rfl

theorem isFFModule_of_le (hn : M ≤ Subgroup.normalizer (L : Set G)) {V W : Subgroup G}
    [IsMulCommutative ↥W] [IsMulCommutative ↥V] (hW2 : ∀ w ∈ W, w ^ 2 = 1) (hVW : V ≤ W)
    (hWR : W ≤ reducedAggregate (L ⊔ T)) (hVN : L ⊔ T ≤ Subgroup.normalizer (V : Set G))
    (hVL : ⁅V, L⁆ ≠ ⊥) (hFF : IsFFModule (autOn (L ⊔ T) W)) :
    IsFFModule (autOn (L ⊔ T) V) := by
  have hW2' : ∀ w : ↥W, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hW2 _ w.2)
  obtain ⟨A, hA⟩ := ((B1_4_5 hW2' (autOn (L ⊔ T) W)).out 1 2).1 hFF
  have hRred : IsTwoReducedIn (L ⊔ T) (reducedAggregate (L ⊔ T)) := by
    refine isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 ⟨Subgroup.map_subtype_le _, ?_⟩
    have hsub : (reducedAggregate (L ⊔ T)).subgroupOf (L ⊔ T) =
        primeReducedAggregate (↥(L ⊔ T)) 2 :=
      Subgroup.comap_map_eq_self_of_injective (L ⊔ T).subtype_injective _
    rw [hsub]
    exact isPrimeReduced_primeReducedAggregate 2
  have hO2W : pCoreOf 2 (L ⊔ T) ≤ Subgroup.centralizer (W : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le hWR)
    refine hRred.2.2.2 _ (pCoreOf_le 2 _) (le_normalizer_pCoreOf 2 _) fun d hd => ?_
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (L ⊔ T) ⟨d, hd⟩
    refine ⟨k, ?_⟩
    have hk' : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [hk']
    exact Subgroup.one_mem _
  refine InternalSec.isFFModule_autOn_of_offender hW2 hVW hVN hA fun hAc => hA.2.1 ?_
  rw [eq_bot_iff]
  intro a ha
  obtain ⟨g, hgLT, rfl⟩ := Setup.mem_autOn_iff.mp (hA.1 ha)
  have hgV : (g : G) ∈ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 := hAc ha ⟨v, hVW hv⟩ hv
    have h2 := congrArg Subtype.val h1
    rw [Setup.coe_conjAct_apply] at h2
    calc v * g = ((g : G) * v * (g : G)⁻¹) * g := by rw [h2]
      _ = g * v := by group
  have hgC := h.inf_centralizer_le_centralizerSection hn (le_sup_left.trans hVN) hVL
    ⟨hgLT, hgV⟩
  have hg2 : (g : G) ^ 2 ^ 1 ∈ Subgroup.centralizer (W : Set G) := by
    have hsq : (conjAct W g) ^ 2 = 1 := hA.2.2.1.2 _ ha
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have h1 := congrArg (fun φ : MulAut ↥W => ((φ ⟨w, hw⟩ : ↥W) : G)) hsq
    simp only [pow_two, MulAut.mul_apply, MulAut.one_apply] at h1
    rw [Setup.coe_conjAct_apply, Setup.coe_conjAct_apply] at h1
    have e : ((g : G) ^ 2 ^ 1) * w * ((g : G) ^ 2 ^ 1)⁻¹ = w := by
      have e2 : ((g : G) ^ 2 ^ 1) * w * ((g : G) ^ 2 ^ 1)⁻¹ =
          g * (g * w * (g : G)⁻¹) * (g : G)⁻¹ := by
        rw [pow_one, sq]
        group
      rw [e2]
      exact h1
    calc w * (g : G) ^ 2 ^ 1 = ((g : G) ^ 2 ^ 1 * w * ((g : G) ^ 2 ^ 1)⁻¹) * (g : G) ^ 2 ^ 1 := by
          rw [e]
      _ = (g : G) ^ 2 ^ 1 * w := by group
  have hgW : (g : G) ∈ Subgroup.centralizer (W : Set G) :=
    mem_of_pow_two_pow_mem hg2 fun m e _ hme =>
      hO2W (h.mem_pCoreOf_of_mem_centralizerSection hn ((L ⊔ T).pow_mem hgLT m)
        (Subgroup.pow_mem _ hgC m) hme)
  rw [InternalSec.conjAct_eq_one_of_mem_centralizer g hgW]
  exact Subgroup.one_mem _

end Hyp4_2_1

omit [Finite G] in
theorem eq_of_irreducible_quot {L V W : Subgroup G} (hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hVeq : V = ⁅V, L⁆) (hWV : W ≤ V)
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) (hWeq : W = ⁅W, L⁆) (hW1 : W ≠ ⊥)
    (hirr : ∀ X : Subgroup G, V ⊓ Subgroup.centralizer (L : Set G) ≤ X → X ≤ V →
      L ≤ Subgroup.normalizer (X : Set G) →
        X = V ⊓ Subgroup.centralizer (L : Set G) ∨ X = V) : W = V := by
  set C := V ⊓ Subgroup.centralizer (L : Set G) with hC
  have hLC : L ≤ Subgroup.normalizer (C : Set G) := fun l hl =>
    mem_normalizer_inf (hLV hl)
      (mem_normalizer_centralizer_of_mem_normalizer (Subgroup.le_normalizer hl))
  rcases hirr (W ⊔ C) le_sup_right (_root_.sup_le hWV inf_le_left)
      (le_normalizer_sup_of_le hLW hLC) with h1 | h2
  · exfalso
    apply hW1
    have hWC : W ≤ C := h1 ▸ le_sup_left
    rw [hWeq, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hWC.trans inf_le_right
  · refine le_antisymm hWV ?_
    have h3 : ⁅V, L⁆ = ⁅W ⊔ C, L⁆ := by rw [h2]
    have h4 : ⁅W ⊔ C, L⁆ ≤ W := by
      rw [Subgroup.commutator_le]
      intro x hx l hl
      obtain ⟨w, hw, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_comm hVcomm hWV inf_le_left hx
      have hcl : c * l = l * c := (Subgroup.mem_centralizer_iff.mp hc.2 l hl).symm
      have e : ⁅w * c, l⁆ = ⁅w, l⁆ := by
        simp only [commutatorElement_def]
        calc w * c * l * (w * c)⁻¹ * l⁻¹ = w * (c * l) * c⁻¹ * w⁻¹ * l⁻¹ := by group
          _ = w * (l * c) * c⁻¹ * w⁻¹ * l⁻¹ := by rw [hcl]
          _ = w * l * w⁻¹ * l⁻¹ := by group
      rw [e]
      have := Subgroup.commutator_mem_commutator hw hl
      rw [← hWeq] at this
      exact this
    calc V = ⁅V, L⁆ := hVeq
      _ = ⁅W ⊔ C, L⁆ := h3
      _ ≤ W := h4

theorem lemma446Mod_holds : Lemma446Mod := by
  intro G _ _ T M L VB hs hnab hK hT hM hTM hL hLf hLM hq hn hVB1 hVB2 hVB3 hVB0 hC hIrr
  have h : Hyp4_2_1 G T M L := ⟨hs, hnab, hK, hT, hM, hTM, hL, hLf, hLM, hq⟩
  set R := reducedAggregate (L ⊔ T) with hR
  set V := ⁅R, L⁆ with hV
  have hRred : IsTwoReducedIn (L ⊔ T) R := by
    refine isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 ⟨Subgroup.map_subtype_le _, ?_⟩
    have hsub : R.subgroupOf (L ⊔ T) = primeReducedAggregate (↥(L ⊔ T)) 2 :=
      Subgroup.comap_map_eq_self_of_injective (L ⊔ T).subtype_injective _
    rw [hsub]
    exact isPrimeReduced_primeReducedAggregate 2
  have hLR : L ≤ Subgroup.normalizer (R : Set G) := le_sup_left.trans hRred.2.1
  have hRL : R ≤ Subgroup.normalizer (L : Set G) := hRred.1.trans (h.sup_le.trans hn)
  have hVR : V ≤ R := commutator_le_left_of_le_normalizer hLR
  have hRel : IsElemAbelian 2 R := hRred.2.2.1
  have hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hRel.1.1.1 ⟨a, hVR ha⟩ ⟨b, hVR hb⟩)
  have hV2 : ∀ v ∈ V, v ^ 2 = 1 := fun v hv => hRel.2 v (hVR hv)
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := fun l hl =>
    mem_normalizer_commutator (hLR hl) (Subgroup.le_normalizer hl)
  have hVeq : V = ⁅V, L⁆ := commutator_eq_commutator_commutator_of_perfect h.perfect hRL hLR
  have hVBV : VB ≤ V := h.le_commutator_reducedAggregate hn hVB1 hVB2 hVB3 hVB0
  have hLVB : L ≤ Subgroup.normalizer (VB : Set G) := le_sup_left.trans hVB2
  have hVBL : ⁅VB, L⁆ ≠ ⊥ := hVB3 ▸ hVB0
  have hVBc : IsMulCommutative ↥VB :=
    ⟨⟨fun x y => Subtype.ext (hVcomm _ (hVBV x.2) _ (hVBV y.2))⟩⟩
  have heq := fun hc => eq_of_irreducible_quot hVcomm hLV hVeq hVBV hLVB hVB3 hVB0 (hIrr hc)
  obtain ⟨hMN, htype, ⟨hcomm, hFF⟩, hL3, hL4, hA6, hU3⟩ := hC
  refine ⟨hMN, htype, ⟨hVBc, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact h.isFFModule_of_le hn hV2 hVBV hVR hVB2 hVBL hFF
  · intro h3
    exact isNaturalSumUnder_of_le (by norm_num) (hL3 h3) hVcomm hVBV hLVB hVB0
  · intro h4
    rcases hL4 h4 with hnat | hext
    · exact Or.inl (isNaturalSumUnder_of_le (by norm_num) hnat hVcomm hVBV hLVB hVB0)
    · right
      rw [heq (Or.inr (Or.inr ⟨h4, hext⟩))]
      exact hext
  · intro h6
    rw [heq (Or.inl h6)]
    exact hA6 h6
  · intro hu
    rw [heq (Or.inr (Or.inl hu))]
    exact hU3 hu

end CFSG.Quasithin.H13.Ch4
