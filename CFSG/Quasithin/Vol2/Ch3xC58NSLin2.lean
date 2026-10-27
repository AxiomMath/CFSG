module

public import CFSG.Quasithin.Vol2.Ch3xC58NSPair
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245Natural
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245NaturalLin2

public section

namespace CFSG.Quasithin.C58NS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C5 Subgroup
open CFSG.QuasithinUnique.Setup.Campbell
open scoped commutatorElement MatrixGroups LinearAlgebra.Projectivization

variable {G : Type} [Group G] [Finite G]

theorem lin2_comm_of_mem_blockZ {L T : Subgroup G} (hL : IsShort2 L) {n : ℕ} (hn : 1 ≤ n)
    (hlin : IsLin2Type L n) (hT : IsSylowTwoOf T L) {t : G} (ht : t ∈ T) (htQ : t ∉ blockQ L)
    {u : G} (hu : u ∈ blockU L) (hz : t * u * t⁻¹ * u⁻¹ ∈ blockZ L) : u * t = t * u := by
  classical
  obtain ⟨F, hFfield, hFfin, hcard, α, hαs, hαk, β, hβs, hβk, hβe⟩ := hlin
  have hq : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hcard
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn hq
  have hUab : ∀ a ∈ blockU L, ∀ b ∈ blockU L, a * b = b * a := (C1.elemAb2_blockU hL).1
  have hLN : L ≤ normalizer (blockU L : Set G) := C1.le_normalizer_blockU L
  let conjL : ↥L →* MulAut ↥(blockU L) :=
    (blockU L).normalizerMonoidHom.comp (Subgroup.inclusion hLN)
  have hconjL : ∀ (l : L) (v : blockU L), ((conjL l v : blockU L) : G) = l * v * l⁻¹ :=
    fun l v => rfl
  have hkerle : α.ker ≤ conjL.ker := by
    intro l hl
    rw [MonoidHom.mem_ker]
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    rw [hconjL, MulAut.one_apply]
    have hlQ : (l : G) ∈ blockQ L := (C56.mem_blockQ_iff l).mpr (hαk ▸ hl)
    have := C1.blockU_comm hL v v.2 l hlQ
    rw [Subgroup.coe_inv, mul_inv_eq_iff_eq_mul]
    exact this.symm
  let act : Matrix.SpecialLinearGroup (Fin 2) F →* MulAut ↥(blockU L) :=
    MonoidHom.liftOfRightInverse α (Function.surjInv hαs) (Function.rightInverse_surjInv hαs)
      ⟨conjL, hkerle⟩
  have hact : ∀ l : L, act (α l) = conjL l := fun l =>
    MonoidHom.liftOfRightInverse_comp_apply α (Function.surjInv hαs)
      (Function.rightInverse_surjInv hαs) ⟨conjL, hkerle⟩ l
  have hactc : ∀ (l : L) (v : blockU L), ((act (α l) v : blockU L) : G) = l * v * l⁻¹ := by
    intro l v
    rw [hact, hconjL]
  let hCG : CommGroup ↥(blockU L) :=
    { (inferInstance : Group ↥(blockU L)) with
      mul_comm := fun a b => Subtype.ext (hUab _ a.2 _ b.2) }
  have hIs : IsNatPlane act β := by
    refine ⟨?_, hβs, ?_, ?_⟩
    · intro e
      apply Subtype.ext
      have := C1.blockU_sq hL e e.2
      simpa [pow_two] using this
    · intro g e
      obtain ⟨l, rfl⟩ := hαs g
      rw [hact]
      apply Multiplicative.toAdd.injective
      rw [toAdd_ofAdd, Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec]
      exact hβe l e (conjL l e) (hconjL l e)
    · intro g e he
      obtain ⟨l, rfl⟩ := hαs g
      rw [hact]
      have heZ : (e : G) ∈ blockZ L := by
        have : e ∈ (blockZ L).subgroupOf (blockU L) := hβk ▸ he
        exact this
      apply Subtype.ext
      rw [hconjL]
      have := Subgroup.mem_centralizer_iff.mp heZ.2 (l : G) l.2
      rw [Subgroup.coe_inv, mul_inv_eq_iff_eq_mul]
      exact this
  have hEL : commSub act Set.univ ⊤ = ⊤ := by
    rw [eq_top_iff]
    intro e _
    have hUK : blockU L ≤ (commSub act Set.univ ⊤).map (blockU L).subtype := by
      refine (C1.commutator_blockU hL).symm.le.trans ?_
      rw [Subgroup.commutator_le]
      intro v hv l hl
      have hgen : act (α ⟨l, hl⟩) ⟨v, hv⟩ * (⟨v, hv⟩ : blockU L)⁻¹ ∈ commSub act Set.univ ⊤ :=
        Subgroup.subset_closure ⟨α ⟨l, hl⟩, Set.mem_univ _, ⟨v, hv⟩, Subgroup.mem_top _, rfl⟩
      refine ⟨(act (α ⟨l, hl⟩) ⟨v, hv⟩ * (⟨v, hv⟩ : blockU L)⁻¹)⁻¹, inv_mem hgen, ?_⟩
      show (((act (α ⟨l, hl⟩) ⟨v, hv⟩ * (⟨v, hv⟩ : blockU L)⁻¹)⁻¹ : blockU L) : G) = ⁅v, l⁆
      rw [commutatorElement_def]
      simp [hactc]
      group
    obtain ⟨k, hk, hke⟩ := hUK e.2
    have : k = e := Subtype.ext hke
    rwa [this] at hk
  obtain ⟨-, hpall⟩ := saturated_natural_plane_root_fixed_space (k := F) (E := ↥(blockU L)) hn hq
    hIs hEL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨p, -, hT2⟩ := C56.lin2_exists_point hn hT hq α hαs hαk
  have htL : t ∈ L := hT.le ht
  have hα1 : α ⟨t, htL⟩ ≠ 1 := fun h => htQ ((C56.mem_blockQ_iff ⟨t, htL⟩).mpr
    (hαk ▸ MonoidHom.mem_ker.mpr h))
  have hαp : α ⟨t, htL⟩ ∈ rootGrp p := (hT2 _).mpr ht
  obtain ⟨-, -, -, hts, -, -⟩ := hpall p
  have hrk := (hts _ hαp hα1).2.2.2
  have hmemU : t * u * t⁻¹ * u⁻¹ ∈ blockU L := hz.1
  have hrange : (⟨t * u * t⁻¹ * u⁻¹, hmemU⟩ : blockU L) ∈ (actDiff act (α ⟨t, htL⟩)).range := by
    refine ⟨⟨u, hu⟩, ?_⟩
    apply Subtype.ext
    rw [actDiff_apply]
    show ((act (α ⟨t, htL⟩) ⟨u, hu⟩ : blockU L) : G) * (u : G)⁻¹ = _
    rw [hactc]
    rfl
  have hker : (⟨t * u * t⁻¹ * u⁻¹, hmemU⟩ : blockU L) ∈ β.ker := by
    rw [hβk]
    exact Subgroup.mem_subgroupOf.mpr hz
  have h0 : (⟨t * u * t⁻¹ * u⁻¹, hmemU⟩ : blockU L) ∈
      (actDiff act (α ⟨t, htL⟩)).range ⊓ β.ker := ⟨hrange, hker⟩
  rw [hrk] at h0
  have h1 : t * u * t⁻¹ * u⁻¹ = 1 := congrArg Subtype.val (Subgroup.mem_bot.mp h0)
  have h2 : t * u * t⁻¹ = u := by
    calc t * u * t⁻¹ = t * u * t⁻¹ * u⁻¹ * u := by group
      _ = u := by rw [h1, one_mul]
  calc u * t = t * u * t⁻¹ * t := by rw [h2]
    _ = t * u := by group

theorem rank1_of_lin2 {K S : Subgroup G} (hK : IsShort2 K) {n : ℕ} (hn : 1 < n)
    (hlin : IsLin2Type K n) (hS2 : IsPGroup 2 S) (hSN : S ≤ normalizer (K : Set G))
    (hsyl : IsSylowTwoOf S (K ⊔ S)) (hc542 : S ≤ (S ⊓ K) ⊔ pCoreOf 2 (K ⊔ S)) :
    Rank1 S (S ⊓ centralizer (blockU K : Set G)) (blockU K)
        (blockU K ⊓ centralizer ((S ⊓ K : Subgroup G) : Set G)) (2 ^ n) ∧
      K ≤ normalizer ((S ⊓ centralizer (blockU K : Set G) : Subgroup G) : Set G) ∧
      blockU K ≤ S ∧
      (∀ y ∈ S, y ∉ S ⊓ centralizer (blockU K : Set G) → ∀ u ∈ blockU K,
        y * u * y⁻¹ * u⁻¹ ∈ blockZ K →
          u ∈ blockU K ⊓ centralizer ((S ⊓ K : Subgroup G) : Set G)) ∧
      ∀ y ∈ normalizer (S : Set G),
        ¬ conjSubgroup (blockU K) y ≤ S ⊓ centralizer (blockU K : Set G) →
        ¬ conjSubgroup (blockU K) y⁻¹ ≤ S ⊓ centralizer (blockU K : Set G) →
        ∃ k ∈ K, K ≤ conjSubgroup (blockU K) y ⊔ conjSubgroup (conjSubgroup (blockU K) y) k := by
  set U := blockU K with hUdef
  have hSU : S ≤ normalizer (U : Set G) := fun g hg => C1.mem_normalizer_blockU (hSN hg)
  set X := K ⊔ S with hXdef
  have hKX : K ≤ X := le_sup_left
  have hSX : S ≤ X := le_sup_right
  have hXN : X ≤ normalizer (K : Set G) := sup_le Subgroup.le_normalizer hSN
  have hXU : X ≤ normalizer (U : Set G) := sup_le (C1.le_normalizer_blockU K) hSU
  have hQX : S ⊓ centralizer (U : Set G) = pCoreOf 2 X :=
    C56.baum_inf_centralizer_eq hK hS2 hSN hsyl
  have hUK : U ≤ K := (C1.blockU_le_blockQ hK).trans (C1.blockQ_le K)
  have hUS : U ≤ S := hsyl.le_of_normalizes (hUK.trans hKX) hXU (C1.isPGroup_blockU hK)
  have hXQ : X ≤ normalizer ((pCoreOf 2 X : Subgroup G) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X
  set Q := S ⊓ centralizer (U : Set G) with hQdef
  have hKQ : K ≤ normalizer (Q : Set G) := by rw [hQX]; exact hKX.trans hXQ
  have hQ2 : IsPGroup 2 Q := hS2.to_le inf_le_left
  have hQS : Q ≤ S := inf_le_left
  have hUQ : U ≤ Q := le_inf hUS (fun u hu => Subgroup.mem_centralizer_iff.mpr fun v hv =>
    (C1.elemAb2_blockU hK).1 v hv u hu)
  have hTsyl : IsSylowTwoOf (S ⊓ K) K :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal hsyl hKX
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hXN).isSubnormal
  set T := S ⊓ K with hTdef
  obtain ⟨hR1, hR2', hR3, hR4, hR5, k, hkK, hkgen⟩ :=
    C56.lin2_module_facts hK (by omega) hlin hTsyl
  have hQT : blockQ K ≤ T := hTsyl.le_of_normalizes (C1.blockQ_le K) (C1.le_normalizer_blockQ K)
    (C1.blockQ_isPGroup K)
  have hTS : T ≤ S := inf_le_left
  have hSTQ : S = T ⊔ Q := by
    refine le_antisymm ?_ (sup_le hTS hQS)
    have := hc542
    rwa [← hQX] at this
  have hTK : T ≤ K := inf_le_right
  have hTQ : T ≤ normalizer (Q : Set G) := fun t ht => by
    rw [hQX]; exact hXQ (hKX (hTK ht))
  have hdecomp : ∀ y ∈ S, ∃ t ∈ T, ∃ c ∈ Q, y = t * c := fun y hy =>
    C5.mem_sup_of_le_normalizer hTQ (hSTQ ▸ hy)
  have hQcomm : ∀ c ∈ Q, ∀ u ∈ U, u * c = c * u := fun c hc u hu =>
    Subgroup.mem_centralizer_iff.mp hc.2 u hu
  have hQTeq : Q ⊓ T = blockQ K := by
    refine le_antisymm (fun g hg => ?_) (fun g hg => ⟨⟨hQT.trans hTS hg, ?_⟩, hQT hg⟩)
    · have : g ∈ K ⊓ centralizer (U : Set G) := ⟨hTK hg.2, hg.1.2⟩
      rwa [hR1] at this
    · have : g ∈ K ⊓ centralizer (U : Set G) := by rw [hR1]; exact hg
      exact this.2
  have hidxQ : Q.relIndex S = 2 ^ n := by
    rw [hSTQ, C5.relIndex_sup_eq_of_le_normalizer hTQ, ← Subgroup.inf_relIndex_right Q T, hQTeq]
    exact hR2'
  have hnotQ : ∀ t ∈ T, ∀ c ∈ Q, t * c ∉ Q → t ∉ blockQ K := by
    intro t ht c hc hnq htq
    apply hnq
    have : t ∈ Q := by
      have h1 : t ∈ K ⊓ centralizer (U : Set G) := by rw [hR1]; exact htq
      exact ⟨hTS ht, h1.2⟩
    exact mul_mem this hc
  have hcent : ∀ y ∈ S, y ∉ Q → ∀ u ∈ U, (u ∈ (U ⊓ centralizer (T : Set G)) ↔ u * y = y * u) := by
    intro y hy hyQ u hu
    obtain ⟨t, ht, c, hc, rfl⟩ := hdecomp y hy
    have htq := hnotQ t ht c hc hyQ
    have hcu := hQcomm c hc u hu
    have h5 := hR5 t ht htq u hu
    constructor
    · intro hW
      have : u * t = t * u := h5.mpr hW.2
      calc u * (t * c) = (u * t) * c := by group
        _ = (t * u) * c := by rw [this]
        _ = t * (u * c) := by group
        _ = t * (c * u) := by rw [hcu]
        _ = (t * c) * u := by group
    · intro h
      refine ⟨hu, h5.mp ?_⟩
      have h6 : u * t * c = t * u * c := by
        calc u * t * c = u * (t * c) := by group
          _ = (t * c) * u := h
          _ = t * (c * u) := by group
          _ = t * (u * c) := by rw [hcu]
          _ = t * u * c := by group
      exact mul_right_cancel h6
  have hcomm : ⁅U, S⁆ = U ⊓ centralizer (T : Set G) := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro u hu b hb
      obtain ⟨t, ht, c, hc, rfl⟩ := hdecomp b hb
      have hcu' : c * u⁻¹ = u⁻¹ * c := (hQcomm c hc u⁻¹ (inv_mem hu)).symm
      have e : ⁅u, t * c⁆ = ⁅u, t⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        calc u * (t * c) * u⁻¹ * (t * c)⁻¹ = u * t * (c * u⁻¹) * c⁻¹ * t⁻¹ := by group
          _ = u * t * (u⁻¹ * c) * c⁻¹ * t⁻¹ := by rw [hcu']
          _ = u * t * u⁻¹ * t⁻¹ := by group
      rw [e, ← hR4]
      exact Subgroup.commutator_mem_commutator hu ht
    · rw [← hR4]
      exact Subgroup.commutator_mono le_rfl hTS
  have hR1struct : C5.Rank1 S Q U (U ⊓ centralizer (T : Set G)) (2 ^ n) :=
    { U_le_Q := hUQ
      Q_le_B := hQS
      B_le_normQ := fun _ hb => C5.mem_normalizer_inf (Subgroup.le_normalizer hb)
        (C5.mem_normalizer_centralizer (hSU hb))
      B_le_normU := hSU
      Q_eq := rfl
      W_le_U := inf_le_left
      idx_Q := hidxQ
      idx_W := hR3
      q_ne_zero := by positivity
      cent_y := hcent
      comm_UB := hcomm
      U_comm := (C1.elemAb2_blockU hK).1 }
  have hmod : ∀ y ∈ S, y ∉ Q → ∀ u ∈ U, y * u * y⁻¹ * u⁻¹ ∈ blockZ K →
      u ∈ U ⊓ centralizer (T : Set G) := by
    intro y hy hyQ u hu hz
    obtain ⟨t, ht, c, hc, rfl⟩ := hdecomp y hy
    have htq := hnotQ t ht c hc hyQ
    have hcu := hQcomm c hc u hu
    have e : t * c * u * (t * c)⁻¹ * u⁻¹ = t * u * t⁻¹ * u⁻¹ := by
      calc t * c * u * (t * c)⁻¹ * u⁻¹ = t * (c * u) * c⁻¹ * t⁻¹ * u⁻¹ := by group
        _ = t * (u * c) * c⁻¹ * t⁻¹ * u⁻¹ := by rw [hcu]
        _ = t * u * t⁻¹ * u⁻¹ := by group
    rw [e] at hz
    have h1 := lin2_comm_of_mem_blockZ hK (by omega) hlin hTsyl ht htq hu hz
    exact ⟨hu, (hR5 t ht htq u hu).mp h1⟩
  have hgen : ∀ y ∈ normalizer (S : Set G), ¬ conjSubgroup U y ≤ Q → ¬ conjSubgroup U y⁻¹ ≤ Q →
      ∃ k' ∈ K, K ≤ conjSubgroup U y ⊔ conjSubgroup (conjSubgroup U y) k' := by
    intro y hy _ hy2
    refine ⟨k, hkK, ?_⟩
    have hSeq : conjSubgroup U y ⊔ Q = S := hR1struct.sup_Q_conj hy hy2
    set Ut := conjSubgroup U y with hUt
    set Λ := Ut ⊔ conjSubgroup Ut k with hΛ
    have hcQ : k ∈ normalizer (Q : Set G) := hKQ hkK
    have hTΛ : T ≤ Λ ⊔ Q := by
      calc T ≤ S := hTS
        _ = Ut ⊔ Q := hSeq.symm
        _ ≤ Λ ⊔ Q := sup_le_sup_right le_sup_left Q
    have hTkΛ : conjSubgroup T k ≤ Λ ⊔ Q := by
      calc conjSubgroup T k ≤ conjSubgroup S k := C5.conjSubgroup_mono hTS k
        _ = conjSubgroup (Ut ⊔ Q) k := by rw [hSeq]
        _ = conjSubgroup Ut k ⊔ conjSubgroup Q k := C5.conjSubgroup_sup _ _ _
        _ = conjSubgroup Ut k ⊔ Q := by rw [C5.conjSubgroup_eq_self hcQ]
        _ ≤ Λ ⊔ Q := sup_le_sup_right le_sup_right Q
    have hKΛQ : K ≤ Λ ⊔ Q := hkgen.trans (sup_le hTΛ hTkΛ)
    have hQUt : Q ≤ normalizer (Ut : Set G) := fun g hg =>
      hR1struct.B_le_normU_conj hy (hQS hg)
    have hQΛ : Q ≤ normalizer (Λ : Set G) := by
      intro g hg
      have h2 : g ∈ normalizer ((conjSubgroup Ut k : Subgroup G) : Set G) := by
        have := C5.conjSubgroup_mono hQUt k
        rw [C5.conjSubgroup_eq_self hcQ, C5.conjSubgroup_normalizer] at this
        exact this hg
      exact C1.mem_normalizer_sup (hQUt hg) h2
    exact C56.le_of_le_sup_isPGroup hK hQ2 hQΛ hKΛQ
  exact ⟨hR1struct, hKQ, hUS, hmod, hgen⟩

theorem pairDataZ_of_lin2 {K S : Subgroup G} (hK : IsShort2 K) {n : ℕ} (hn : 1 < n)
    (hlin : IsLin2Type K n) (hS2 : IsPGroup 2 S) (hSN : S ≤ normalizer (K : Set G))
    (hsyl : IsSylowTwoOf S (K ⊔ S)) (hc542 : S ≤ (S ⊓ K) ⊔ pCoreOf 2 (K ⊔ S)) {x : G}
    (hx : x ∈ normalizer (S : Set G))
    (hxU : ¬ conjSubgroup (blockU K) x ≤ centralizer (blockU K : Set G)) :
    PairDataZ S (S ⊓ centralizer (blockU K : Set G)) (blockU K)
      (blockU K ⊓ centralizer ((S ⊓ K : Subgroup G) : Set G))
      ((S ⊓ centralizer (blockU K : Set G)) ⊓ centralizer (K : Set G)) x (2 ^ n) := by
  obtain ⟨hR, hKQ, hUS, hmod, hgen⟩ := rank1_of_lin2 hK hn hlin hS2 hSN hsyl hc542
  set U := blockU K with hUdef
  set Q := S ⊓ centralizer (U : Set G) with hQdef
  have hx1 : ¬ conjSubgroup U x ≤ Q := fun h => hxU (h.trans inf_le_right)
  have hx2 : ¬ conjSubgroup U x⁻¹ ≤ Q := by
    intro h
    apply hxU
    have h1 := C5.conjSubgroup_mono (h.trans inf_le_right) x
    rw [C5.conjSubgroup_inv_conjSubgroup, C5.conjSubgroup_centralizer] at h1
    rw [le_centralizer_iff] at h1
    exact h1
  have hUK : U ≤ K := (C1.blockU_le_blockQ hK).trans (C1.blockQ_le K)
  obtain ⟨hQeq, hDle⟩ := hR.Q_eq_sup_centralizer hx hx1 hUK hKQ
    (by rw [C56.relIndex_blockZ_isLin2Type hlin]) (hgen x hx hx1 hx2)
  set D := Q ⊓ centralizer (K : Set G) with hDdef
  have hq2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine
    { rank1 := hR
      hq := hq2
      hU2 := C1.blockU_sq hK
      hx := hx
      hx1 := hx1
      hx2 := hx2
      hQ := hQeq
      hDU := fun u hu d hd => Subgroup.mem_centralizer_iff.mp hd.2 u (hUK hu)
      hDUx := fun u hu d hd => by
        have hdQx : d ∈ conjSubgroup Q x := hDle hd
        rw [hR.conj_Q_eq hx] at hdQx
        exact Subgroup.mem_centralizer_iff.mp hdQx.2 u hu
      hZW := fun u hu => ⟨hu.1, Subgroup.mem_centralizer_iff.mpr fun t ht =>
        (Subgroup.mem_centralizer_iff.mp hu.2.2 t
          ((inf_le_right : (S ⊓ K : Subgroup G) ≤ K) ht))⟩
      cent_mod := fun y hy hyQ u hu hz => hmod y hy hyQ u hu
        ⟨hz.1, Subgroup.mem_centralizer_iff.mpr fun k hk =>
          Subgroup.mem_centralizer_iff.mp hz.2.2 k hk⟩ }

end CFSG.Quasithin.C58NS
