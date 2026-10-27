module

public import CFSG.RankThree.PartTwo.Sec17.Item1726Proof
public import CFSG.RankThree.PartTwo.Sec17.Item1721StepsProof1724
import CFSG.LocalAnalysis.RankTwoShapes.FixedPointFreeThree
public import CFSG.RankThree.PartTwo.Sec17.Item1724Two
public import CFSG.RankThree.PartTwo.Sec17.Item17ParaTools
public import CFSG.RankThree.PartTwo.Sec17.Item17TailEnd
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late

theorem item1724Three_of_item1724N (h1724 : Item1724N) : Item1724Three :=
  fun G _ _ A c L Y₀ Y₁ S p P w Q h => (h1724 G A c L Y₀ Y₁ S p P w Q h).2

namespace Proof1724N

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ Y₁ S : Subgroup G}
  {p : ℕ} {P : Subgroup G} {w : G} {Q : Subgroup G}

theorem inf_centralizer_c_eq_bot (h : Sec17W G A c L Y₀ Y₁ S p P w Q)
    (h3 : Q ⊓ Subgroup.normalizer (Y₀ : Set G) = ⊥) :
    Q ⊓ Subgroup.centralizer ({c} : Set G) = ⊥ := by
  rw [eq_bot_iff, ← h3]
  refine inf_le_inf_left Q (le_trans ?_ h.normalizer_c_le)
  have hC : Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) =
      Subgroup.centralizer ({c} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [← hC]
  exact Subgroup.centralizer_le_normalizer _

theorem card_omegaOneZ (h1725 : Item1725) {s : G} (h : Sec17S G A c L Y₀ Y₁ S p P w Q s)
    (hQc : Q ⊓ Subgroup.centralizer ({c} : Set G) = ⊥) :
    Nat.card (omegaOneZ p Q ⊓ Y₁ : Subgroup G) = p ^ 2 ∧ Nat.card (omegaOneZ p Q) = p ^ 6 := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  set Z := omegaOneZ p Q with hZdef
  have hZQ : Z ≤ Q := omegaOneZ_le p Q
  have hZe : CFSG.Assembly.IsElemAbelian p Z := isElemAbelian_omegaOneZ p Q
  have hNZ := normalizer_le_normalizer_omegaOneZ p Q
  have hZ1 : Z ≠ ⊥ := omegaOneZ_ne_bot h.isPGroup_Q h.Q_ne_bot
  have hwN : Subgroup.zpowers w ⊔ A ≤ Subgroup.normalizer (Z : Set G) :=
    (sup_le (Subgroup.zpowers_le.mpr h.w_normalizes_Q) h.le_normalizer_Q).trans hNZ
  have hZinv : Z ∈ invariantPiSubgroups Q (Subgroup.zpowers w ⊔ A) (piOf p) :=
    ⟨hZQ, fun q hq => h.isPiSubgroup_Q q (hq.trans (Subgroup.card_dvd_of_le hZQ)), hwN⟩
  obtain ⟨-, -, hX3⟩ := h1725 G A c L Y₀ Y₁ S p P w Q h.toSec17WQ Z hZinv
  have hcard3 : Nat.card Z = Nat.card (Z ⊓ Y₁ : Subgroup G) ^ 3 := by
    rw [← yI_one Y₁ w]
    exact hX3 hZe.1
  set Z₁ := Z ⊓ Y₁ with hZ₁def
  have hZ₁1 : Z₁ ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot, one_pow] at hcard3
    exact hZ1 (Subgroup.card_eq_one.mp hcard3)
  have hZ₁e : CFSG.Assembly.IsElemAbelian p Z₁ := isElemAbelian_of_le hZe inf_le_left
  have hAY : A ≤ Subgroup.normalizer (Y₁ : Set G) := h.mem_y1Star.prop.1.1.1.2
  have hcZ₁ : c ∈ Subgroup.normalizer (Z₁ : Set G) :=
    le_normalizer_inf (Subgroup.zpowers_le.mpr (hNZ (h.le_normalizer_Q h.c_mem)))
      (Subgroup.zpowers_le.mpr (hAY h.c_mem)) (Subgroup.mem_zpowers c)
  have hsZ₁ : s ∈ Subgroup.normalizer (Z₁ : Set G) :=
    le_normalizer_inf (Subgroup.zpowers_le.mpr (hNZ h.s_normalizes_Q))
      (Subgroup.zpowers_le.mpr h.s_normalizes_y1) (Subgroup.mem_zpowers s)
  have hfix : Z₁ ⊓ Subgroup.centralizer ({c} : Set G) = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_right _ (inf_le_left.trans hZQ)).trans hQc.le)
  have hne := card_ne_of_inverts hZ₁e hZ₁1 h.c_pow_three hcZ₁ hfix hsZ₁ h.s_inverts_c
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (h.isPGroup_Q.to_le (inf_le_left.trans hZQ) :
    IsPGroup p Z₁)
  have hk2 : k = 2 := by
    rcases k with _ | _ | _ | k
    · exfalso
      rw [pow_zero] at hk
      exact hZ₁1 (Subgroup.card_eq_one.mp hk)
    · exfalso
      rw [zero_add, pow_one] at hk
      exact hne hk
    · rfl
    · exfalso
      obtain ⟨E', hE'⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥Z₁) p (n := 3)
        (by rw [hk]; exact pow_dvd_pow p (by omega))
      refine h.not_card_cube (E := E'.map Z₁.subtype)
        ((Subgroup.map_subtype_le E').trans inf_le_right)
        (isElemAbelian_of_le hZ₁e (Subgroup.map_subtype_le E')) ?_
      rw [Subgroup.card_map_of_injective Z₁.subtype_injective, hE']
  refine ⟨by rw [hk, hk2], ?_⟩
  rw [hcard3, hk, hk2, ← pow_mul]

theorem mem_omegaOneZ_of_pow_eq_one (h1725 : Item1725) {s : G}
    (h : Sec17S G A c L Y₀ Y₁ S p P w Q s) (hQc : Q ⊓ Subgroup.centralizer ({c} : Set G) = ⊥)
    {x : G} (hxQ : x ∈ Q) (hxY : x ∈ Y₁) (hxp : x ^ p = 1) : x ∈ omegaOneZ p Q ⊓ Y₁ := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  obtain ⟨h2, -⟩ := card_omegaOneZ h1725 h hQc
  set Z₁ := omegaOneZ p Q ⊓ Y₁ with hZ₁def
  by_contra hx
  have hx1 : x ≠ 1 := fun h1 => hx (h1 ▸ one_mem _)
  have hord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hZ₁e : CFSG.Assembly.IsElemAbelian p Z₁ :=
    isElemAbelian_of_le (isElemAbelian_omegaOneZ p Q) inf_le_left
  have hxc : ∀ e ∈ Z₁, e * x = x * e := fun e he =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp he).1.2.1 x hxQ).symm
  have hsupe := isElemAbelian_sup_zpowers hZ₁e hxp hxc
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (Z₁ : Set G) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_fintype fun e he => ?_)
    rw [← hxc e he, mul_inv_cancel_right]
    exact he
  have hcard : Nat.card (Z₁ ⊔ Subgroup.zpowers x : Subgroup G) = p ^ 3 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hxN
      (disjoint_iff.mpr (inf_zpowers_eq_bot_of_prime h.p_prime hord hx)), h2, Nat.card_zpowers,
      hord]
    ring
  exact h.not_card_cube (sup_le inf_le_right (Subgroup.zpowers_le.mpr hxY)) hsupe hcard

theorem le_omegaOneZ_of_invariant (h1725 : Item1725) {s : G}
    (h : Sec17S G A c L Y₀ Y₁ S p P w Q s) (hQc : Q ⊓ Subgroup.centralizer ({c} : Set G) = ⊥)
    {X : Subgroup G} (hXQ : X ≤ Q)
    (hXN : Subgroup.zpowers w ⊔ A ≤ Subgroup.normalizer (X : Set G))
    (hXp : ∀ x ∈ X, x ^ p = 1) : X ≤ omegaOneZ p Q := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  set Z := omegaOneZ p Q with hZdef
  have hXinv : X ∈ invariantPiSubgroups Q (Subgroup.zpowers w ⊔ A) (piOf p) :=
    ⟨hXQ, fun q hq => h.isPiSubgroup_Q q (hq.trans (Subgroup.card_dvd_of_le hXQ)), hXN⟩
  obtain ⟨hXeq, hXi, -⟩ := h1725 G A c L Y₀ Y₁ S p P w Q h.toSec17WQ X hXinv
  have hNZ := normalizer_le_normalizer_omegaOneZ p Q
  have hwZ : w ∈ Subgroup.normalizer (Z : Set G) := hNZ h.w_normalizes_Q
  have hX1 : X ⊓ yI Y₁ w 1 ≤ Z := by
    rw [yI_one]
    intro x hx
    exact (mem_omegaOneZ_of_pow_eq_one h1725 h hQc (hXQ hx.1) hx.2 (hXp x hx.1)).1
  have hX3 : X ⊓ yI Y₁ w 3 ≤ Z := by
    have h1 := hXi 1 le_rfl (by norm_num)
    have h3 : X ⊓ yI Y₁ w 3 = (X ⊓ yI Y₁ w 1).map (MulAut.conj w⁻¹).toMonoidHom := by
      rw [h1, pow_one, map_conj_map_conj, inv_mul_cancel, map_conj_one]
    rw [h3, ← Late.map_conj_eq_of_mem_normalizer (inv_mem hwZ)]
    exact Subgroup.map_mono hX1
  have hX2 : X ⊓ yI Y₁ w 2 ≤ Z := by
    rw [hXi 2 (by norm_num) (by norm_num),
      ← Late.map_conj_eq_of_mem_normalizer (pow_mem hwZ 2)]
    exact Subgroup.map_mono hX3
  rw [hXeq]
  exact sup_le (sup_le hX1 hX2) hX3

theorem omegaOneZTwo_le (h1725 : Item1725) {s : G} (h : Sec17S G A c L Y₀ Y₁ S p P w Q s)
    (hQc : Q ⊓ Subgroup.centralizer ({c} : Set G) = ⊥) (hp : Odd p) :
    omegaOneZTwo p hp Q ≤ omegaOneZ p Q := by
  set I := omegaOneZTwo p hp Q with hIdef
  have hIQ : I ≤ Q := fun x hx => hx.1
  have hNI : Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (I : Set G) := by
    intro n hn
    have hCn : n ∈ Subgroup.normalizer
        ((Subgroup.centralizer (Q : Set G) : Subgroup G) : Set G) := by
      refine mem_normalizer_of_map_conj_eq' ?_
      rw [map_conj_centralizer, Late.map_conj_eq_of_mem_normalizer hn]
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨hxQ, hxp, hxc⟩ := hx
    refine ⟨(Subgroup.mem_normalizer_iff.mp hn x).mp hxQ, by rw [conj_pow, hxp, mul_one,
      mul_inv_cancel], fun g hg => ?_⟩
    have hg' : n⁻¹ * g * n⁻¹⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (inv_mem hn) g).mp hg
    have h1 := hxc _ hg'
    have e : n * x * n⁻¹ * g * (n * x * n⁻¹)⁻¹ * g⁻¹ =
        n * (x * (n⁻¹ * g * n⁻¹⁻¹) * x⁻¹ * (n⁻¹ * g * n⁻¹⁻¹)⁻¹) * n⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp hCn _).mp h1
  exact le_omegaOneZ_of_invariant h1725 h hQc hIQ
    ((sup_le (Subgroup.zpowers_le.mpr h.w_normalizes_Q) h.le_normalizer_Q).trans hNI)
    (fun x hx => hx.2.1)

theorem commutator_mem_centralizer_Q (h : Sec17W G A c L Y₀ Y₁ S p P w Q)
    (hQc : Q ⊓ Subgroup.centralizer ({c} : Set G) = ⊥) {x g : G} (hx : x ∈ Q) (hg : g ∈ Q) :
    x * g * x⁻¹ * g⁻¹ ∈ Subgroup.centralizer (Q : Set G) := by
  have hcQ : c ∈ Subgroup.normalizer (Q : Set G) := h.le_normalizer_Q h.c_mem
  set α : MulAut ↥Q := Q.normalizerMonoidHom ⟨c, hcQ⟩ with hα
  have hαapp : ∀ y : ↥Q, ((α y : ↥Q) : G) = c * y * c⁻¹ := fun y => rfl
  have hα3 : α ^ 3 = 1 := by
    rw [hα, ← map_pow]
    have h1 : (⟨c, hcQ⟩ : Subgroup.normalizer (Q : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using h.c_pow_three)
    rw [h1, map_one]
  have hfpf : ∀ y : ↥Q, α y = y → y = 1 := by
    intro y hy
    have hyc : (y : G) ∈ Q ⊓ Subgroup.centralizer ({c} : Set G) := by
      refine ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have h1 : c * (y : G) * c⁻¹ = y := by rw [← hαapp, hy]
      calc (y : G) * c = (c * (y : G) * c⁻¹) * c := by rw [h1]
        _ = c * y := by group
    rw [hQc] at hyc
    exact Subtype.ext ((Subgroup.mem_bot.mp hyc).trans rfl)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hcomm := (CFSG.RankTwoShapes.fpfThree_commutatorElement_central α hα3 hfpf ⟨x, hx⟩
    ⟨g, hg⟩ ⟨y, hy⟩).eq
  have h2 := congrArg Subtype.val hcomm
  simp only [Subgroup.coe_mul, commutatorElement_def, Subgroup.coe_inv] at h2
  exact h2.symm

theorem item1728Z_at {s d r : G} (h : Sec17Data G A c L Y₀ Y₁ S p P w Q s d r)
    (hQc : Q ⊓ Subgroup.centralizer ({c} : Set G) = ⊥)
    (hQd : Q ⊓ Subgroup.centralizer ({d} : Set G) = ⊥) (h6 : Nat.card (omegaOneZ p Q) = p ^ 6) :
    omegaOneZ p Q = (omegaOneZ p Q ⊓ Subgroup.centralizer {c * d}) ⊔
        (omegaOneZ p Q ⊓ Subgroup.centralizer {c * d⁻¹}) ∧
      (omegaOneZ p Q ⊓ Subgroup.centralizer {c * d}) ⊓
          (omegaOneZ p Q ⊓ Subgroup.centralizer {c * d⁻¹}) = ⊥ ∧
      Nat.card ↥(omegaOneZ p Q ⊓ Subgroup.centralizer {c * d}) = p ^ 3 := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  set Z := omegaOneZ p Q with hZdef
  have hZab : IsMulCommutative Z := (isElemAbelian_omegaOneZ p Q).1
  have hZQ : Z ≤ Q := omegaOneZ_le p Q
  have hNZ : Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (Z : Set G) :=
    normalizer_le_normalizer_omegaOneZ p Q
  have hcA : c ∈ A := h.c_mem
  have hdA : d ∈ A := h.d_mem.1
  have hcd : c * d = d * c := h.commute_of_mem hcA hdA
  have hd3 : d ^ 3 = 1 := h.isE27.1.2 d hdA
  have hfc : Z ⊓ Subgroup.centralizer ({c} : Set G) = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_right _ hZQ).trans hQc.le)
  have hfd : Z ⊓ Subgroup.centralizer ({d} : Set G) = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_right _ hZQ).trans hQd.le)
  obtain ⟨hZeq, hdisj⟩ := eq_sup_inf_centralizer_mul hZab h.coprime_omegaOneZ hcd h.c_pow_three
    hd3 (hNZ (h.le_normalizer_Q hcA)) (hNZ (h.le_normalizer_Q hdA)) hfc hfd
  refine ⟨hZeq, hdisj, ?_⟩
  obtain ⟨hrc', hrd⟩ := h.r_commute_c_and_inverts_d
  have hrc : r * c * r⁻¹ = c := by rw [← hrc', mul_inv_cancel_right]
  have hrZ : r ∈ Subgroup.normalizer (Z : Set G) := hNZ h.r_normalizes_Q
  have hswap : (Z ⊓ Subgroup.centralizer ({c * d} : Set G)).map (MulAut.conj r).toMonoidHom =
      Z ⊓ Subgroup.centralizer ({c * d⁻¹} : Set G) := by
    rw [map_conj_inf_centralizer hrZ (c * d)]
    congr 3
    calc r * (c * d) * r⁻¹ = (r * c * r⁻¹) * (r * d * r⁻¹) := by group
      _ = c * d⁻¹ := by rw [hrc, hrd]
  have hcard₂ : Nat.card (Z ⊓ Subgroup.centralizer ({c * d⁻¹} : Set G) : Subgroup G) =
      Nat.card (Z ⊓ Subgroup.centralizer ({c * d} : Set G) : Subgroup G) := by
    rw [← hswap, Subgroup.card_map_of_injective (MulAut.conj r).injective]
  have hnorm : Z ⊓ Subgroup.centralizer ({c * d⁻¹} : Set G) ≤
      Subgroup.normalizer ((Z ⊓ Subgroup.centralizer ({c * d} : Set G) : Subgroup G) : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      have hc : t * y = y * t :=
        congrArg Subtype.val (hZab.is_comm.comm ⟨t, ht.1⟩ ⟨y, hy.1⟩)
      have e : y * t * y⁻¹ = t := by rw [← hc, mul_inv_cancel_right]
      rw [e]
      exact ht
    · intro ht
      have hyt : y * t * y⁻¹ ∈ Z := ht.1
      have htZ : t ∈ Z := by
        have := Z.mul_mem (Z.mul_mem (Z.inv_mem hy.1) hyt) hy.1
        simpa [mul_assoc] using this
      have hc : t * y = y * t :=
        congrArg Subtype.val (hZab.is_comm.comm ⟨t, htZ⟩ ⟨y, hy.1⟩)
      have e : y * t * y⁻¹ = t := by rw [← hc, mul_inv_cancel_right]
      rw [e] at ht
      exact ht
  have hcardZ : Nat.card Z =
      Nat.card (Z ⊓ Subgroup.centralizer ({c * d} : Set G) : Subgroup G) ^ 2 := by
    conv_lhs => rw [hZeq]
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm
      (disjoint_iff.mpr hdisj), hcard₂, sq]
  rw [hcardZ, show p ^ 6 = (p ^ 3) ^ 2 by ring] at h6
  exact Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) h6

end Proof1724N

theorem item1726_ofN (h1724 : Item1724Three) (h1725 : Item1725) : Item1726 := by
  intro G _ _ A c L Y₀ Y₁ S p P w Q s h
  have : Fact p.Prime := ⟨h.p_prime⟩
  have hp : Odd p := h.p_prime.odd_of_ne_two (by have := h.three_lt_p; omega)
  have hQc := Proof1724N.inf_centralizer_c_eq_bot h.toSec17W
    (h1724 G A c L Y₀ Y₁ S p P w Q h.toSec17W)
  obtain ⟨-, hcard⟩ := Proof1724N.card_omegaOneZ h1725 h hQc
  refine ⟨?_, isElemAbelian_omegaOneZ p Q, hcard⟩
  have hI := Proof1724N.omegaOneZTwo_le h1725 h hQc hp
  apply le_antisymm
  · intro z hz
    exact Subgroup.subset_closure ⟨hz.1, hz.2.2⟩
  · rw [omegaOneAt, Subgroup.closure_le]
    rintro x ⟨hxQ, hxp⟩
    exact hI ⟨hxQ, hxp, fun g hg =>
      Proof1724N.commutator_mem_centralizer_Q h.toSec17W hQc hxQ hg⟩

theorem rank3II_17_28Z_ofN (h1724 : Item1724Three) (h1726 : Item1726) (h1727 : Item1727) :
    Item1728Z := fun G _ _ A c L Y₀ Y₁ S p P w Q s d r h =>
  Proof1724N.item1728Z_at h
    (Proof1724N.inf_centralizer_c_eq_bot h.toSec17W (h1724 G A c L Y₀ Y₁ S p P w Q h.toSec17W))
    (h1727 G A c L Y₀ Y₁ S p P w Q s d r h) (h1726 G A c L Y₀ Y₁ S p P w Q s h.toSec17S).2.2

end CFSG.RankThree.PartTwo.Sec17
