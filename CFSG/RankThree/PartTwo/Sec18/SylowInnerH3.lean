module

public import CFSG.RankThree.PartTwo.Sec18.SylowLcExists
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.GroupTheory.WielandtProductBasic
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
import CFSG.RankThree.PartTwo.Sec18.Claim184LcProof
import CFSG.RankThree.PartTwo.Sec18.SylowFusion
import CFSG.RankThree.PartTwo.Sec19.Step1914MoreSProofCore

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {c : G}

namespace SylowInner

theorem sup_inf_le_inf_sup {P Q M : Subgroup G} (hQM : Q ≤ M)
    (hPQ : ((P ⊔ Q : Subgroup G) : Set G) = (P : Set G) * (Q : Set G)) :
    (P ⊔ Q) ⊓ M ≤ P ⊓ M ⊔ Q := by
  intro x hx
  have hxM : x ∈ M := hx.2
  have hx' : x ∈ ((P ⊔ Q : Subgroup G) : Set G) := hx.1
  rw [hPQ] at hx'
  obtain ⟨p, hp, q, hq, rfl⟩ := hx'
  have hpM : p ∈ M := by
    have := M.mul_mem hxM (M.inv_mem (hQM hq))
    rwa [mul_inv_cancel_right] at this
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hp, hpM⟩) (Subgroup.mem_sup_right hq)

theorem centralizer_le_normalizer_zpowers (c : G) :
    Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  intro x hx
  apply CFSG.GroupTheory.WielandtProduct.mem_normalizer_of_forall_conj_mem
  intro z hz
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  rw [(Commute.zpow_right (show Commute x c from Subgroup.mem_centralizer_singleton_iff.mp hx)
    i).eq, mul_inv_cancel_right]
  exact Subgroup.zpow_mem_zpowers c i

theorem commutator_mem_pCoreOf_of_relIndex_eq_two {H M : Subgroup G} {s x : G}
    (hS : CFSG.Open.pCoreOf 2 (H ⊓ M) = Subgroup.zpowers s ⊔ CFSG.Open.pCoreOf 2 H)
    (hidx : (CFSG.Open.pCoreOf 2 H).relIndex (CFSG.Open.pCoreOf 2 (H ⊓ M)) = 2)
    (hxH : x ∈ H) (hxM : x ∈ M) : x * s * x⁻¹ * s⁻¹ ∈ CFSG.Open.pCoreOf 2 H := by
  set S := CFSG.Open.pCoreOf 2 (H ⊓ M) with hSdef
  set O := CFSG.Open.pCoreOf 2 H with hOdef
  have hsS : s ∈ S := by
    rw [hS]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers s)
  have hxS : x ∈ Subgroup.normalizer (S : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H ⊓ M) ⟨hxH, hxM⟩
  have hxO : x ∈ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hxH
  have haS : x * s * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hxS s).mp hsS
  have hidx' : (O.subgroupOf S).index = 2 := hidx
  have key := Subgroup.mul_mem_iff_of_index_two hidx' (a := (⟨x * s * x⁻¹, haS⟩ : S))
    (b := (⟨s, hsS⟩ : S)⁻¹)
  simp only [Subgroup.mem_subgroupOf] at key
  refine key.mpr ?_
  show x * s * x⁻¹ ∈ O ↔ s⁻¹ ∈ O
  rw [O.inv_mem_iff]
  exact (Subgroup.mem_normalizer_iff.mp hxO s).symm

theorem map_perfectResidual_inf_centralizer_eq (hH : Sec18H G A M H c) :
    ((inSubgroup perfectResidual (inSubgroup perfectResidual H ⊓
        Subgroup.centralizer ({c} : Set G))).subgroupOf H).map
        (QuotientGroup.mk' (CFSG.pCore 2 H)) =
      (perfectResidual H).map (QuotientGroup.mk' (CFSG.pCore 2 H)) ∧
    CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual (inSubgroup perfectResidual H ⊓
        Subgroup.centralizer ({c} : Set G))) ≤ CFSG.Open.pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : H →* H ⧸ CFSG.pCore 2 H := QuotientGroup.mk' (CFSG.pCore 2 H) with hπ
  set L := inSubgroup perfectResidual H with hLdef
  set Lb := (perfectResidual H).map π with hLbdef
  set C := Subgroup.centralizer ({c} : Set G) with hCdef
  have hLH : L ≤ H := Subgroup.map_subtype_le _
  have hLbn : Lb.Normal := by
    have hc := CFSG.perfect_residual_characterization (G := H)
    have : (perfectResidual H).Characteristic := hc.2.1
    exact (inferInstance : (perfectResidual H).Normal).map π (QuotientGroup.mk'_surjective _)
  have hLO : CFSG.Open.pCoreOf 2 L ≤ CFSG.Open.pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLH)
      ((le_normalizer_inSubgroup_perfectResidual H).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  have hLimg : (L.subgroupOf H).map π = Lb := by
    have : L.subgroupOf H = perfectResidual H :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    rw [this]
  set L₀ := inSubgroup perfectResidual (L ⊓ C) with hL₀def
  have hL₀L : L₀ ≤ L := (Subgroup.map_subtype_le _).trans inf_le_left
  have hL₀H : L₀ ≤ H := hL₀L.trans hLH
  have hLL₀ : L ≤ L₀ ⊔ CFSG.Open.pCoreOf 2 L := (le_sup_and_inf_le_of_sec18H hH).1
  have hL₀img : (L₀.subgroupOf H).map π = Lb := by
    apply le_antisymm
    · rw [← hLimg]
      exact Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr (hL₀L hx)
    · have hOH : CFSG.Open.pCoreOf 2 L ≤ H := (CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLH
      have hker : ((CFSG.Open.pCoreOf 2 L).subgroupOf H).map π = ⊥ := by
        rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk']
        intro x hx
        rw [mem_pCore_iff_mem_pCoreOf]
        exact hLO (Subgroup.mem_subgroupOf.mp hx)
      rw [← hLimg]
      calc (L.subgroupOf H).map π ≤ ((L₀ ⊔ CFSG.Open.pCoreOf 2 L).subgroupOf H).map π :=
            Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr (hLL₀ hx)
        _ = (L₀.subgroupOf H).map π := by
            rw [Subgroup.subgroupOf_sup hL₀H hOH, Subgroup.map_sup, hker, sup_bot_eq]
  exact ⟨hL₀img, Claim184LcProof.pCoreOf_le_of_map_eq hL₀H hL₀img⟩

theorem sup_mem_scriptH_of_ne_top {A M K T : Subgroup G} (h : Sec18Std G A M)
    (hY : K ⊔ A ⊔ T ≠ ⊤) (hK : ⁅K, K⁆ = K)
    (hKq : CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K)) (hT2 : IsPGroup 2 T) (hTM : T ≤ M)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hAT : A ≤ Subgroup.normalizer (T : Set G))
    (hYT : (K ⊔ A ⊔ T) ⊓ M ≤ Subgroup.normalizer (T : Set G))
    (hTO : ¬ T ≤ CFSG.Open.pCoreOf 2 (K ⊔ A ⊔ T)) :
    K ⊔ A ⊔ T ∈ scriptH A M ∧ inSubgroup perfectResidual (K ⊔ A ⊔ T) = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA := isE27_of_mem_partTwoE h.mem_partTwoE
  set Y := K ⊔ A ⊔ T with hYdef
  have hKY : K ≤ Y := le_sup_left.trans le_sup_left
  have hAY : A ≤ Y := le_sup_right.trans le_sup_left
  have hTY : T ≤ Y := le_sup_right
  have hYK : Y ≤ Subgroup.normalizer (K : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer hAK) hTK
  have hKn : (K.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKY).mpr hYK
  have hATs := isSolvable_sup_of_le_normalizer hA.1.1 hT2 hAT
  have hsupY : K ⊔ (A ⊔ T) = Y := by rw [hYdef, sup_assoc]
  have hq : Group.IsSolvable (Y ⧸ K.subgroupOf Y) :=
    isSolvable_quotient_of_sup_eq hKY (sup_le hAY hTY) hYK hsupY hATs
  have hres : inSubgroup perfectResidual Y = K :=
    le_antisymm (inSubgroup_perfectResidual_le_of_isSolvable hKY hq)
      (le_inSubgroup_perfectResidual hK hKY)
  have hTO' : T ≤ CFSG.Open.pCoreOf 2 (Y ⊓ M) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (le_inf hTY hTM) hYT hT2
  refine ⟨⟨hY, ?_, ?_, ?_⟩, hres⟩
  · rw [hres]
    apply le_antisymm
    · exact sup_le_sup_left hTO' _
    · exact sup_le (sup_le hKY hAY)
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left)
  · rw [hres]
    exact mem_oTwoComponentsIn_of_quasisimple hKY hKn.isSubnormal hK hKq
  · intro heq
    exact hTO (heq ▸ hTO')


theorem exists_mem_scriptH_lc (h1812 : Item181_2) (h184 : Item184_1) (h182 : Item182Alt1C)
    (h1842 : Item184_2) (hH : Sec18H G A M H c) :
    ∃ s ∈ Subgroup.centralizer (A : Set G),
      lc H c ⊔ A ⊔ (Subgroup.zpowers s ⊔ CFSG.Open.pCoreOf 2 (lc H c)) ∈ scriptH A M ∧
      inSubgroup perfectResidual
        (lc H c ⊔ A ⊔ (Subgroup.zpowers s ⊔ CFSG.Open.pCoreOf 2 (lc H c))) = lc H c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hH.toSec18Std
  have hHs := hH.mem_scriptH
  have hA := isE27_of_mem_partTwoE h.mem_partTwoE
  have hH₀ := (mem_scriptH_iff_mem_scriptH₀.mp hHs).1
  have hAH := le_of_mem_scriptH₀ hH₀
  have hAM := sec18Std_le h
  obtain ⟨s, ⟨hsS, hsA, hgf, hsH, -⟩, hS, hidx⟩ := h1812 G A M h H hHs
  refine ⟨s, hsA, ?_⟩
  have hout : Sec4.InducesOuterTheta s (inSubgroup perfectResidual H) :=
    hgf.inducesOuterTheta _ (by decide)
  obtain ⟨hcA, -⟩ := mem_and_commutator_mem_of_sec18H hH
  have hc1 : c ≠ 1 := by
    intro h1
    have := orderOf_eq_three_of_sec18H h184 hH
    rw [h1, orderOf_one] at this
    norm_num at this
  obtain ⟨hLcK, hLc_eq⟩ := SylowLc.lc_mem_oTwoComponentsIn h1812 h184 h182 hH
  set L := inSubgroup perfectResidual H with hLdef
  set C := Subgroup.centralizer ({c} : Set G) with hCdef
  set Lc := lc H c with hLcdef
  set O := CFSG.Open.pCoreOf 2 Lc with hOdef
  set L₀ := inSubgroup perfectResidual (L ⊓ C) with hL₀def
  set T := Subgroup.zpowers s ⊔ O with hTdef
  have hLH : L ≤ H := Subgroup.map_subtype_le _
  have hAC : A ≤ C := fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨c, hcA⟩))
  have hsC : s ∈ C :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hsA c hcA).symm
  have hCN : C ≤ Subgroup.normalizer (Lc : Set G) :=
    (centralizer_le_normalizer_zpowers c).trans (normalizer_zpowers_le_normalizer_lc h1842 hH)
  have hLcC : Lc ≤ C := SylowFusion.lc_le_centralizer H c
  have hLcp : ⁅Lc, Lc⁆ = Lc := commutator_inSubgroup_perfectResidual _
  have hNO : Subgroup.normalizer (Lc : Set G) ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Lc
  have hOLc : O ≤ Lc := CFSG.LieType.BorelTits.pCoreOf_le 2 Lc
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Lc
  have hsN : s ∈ Subgroup.normalizer (Lc : Set G) := hCN hsC
  have hsO : s ∈ Subgroup.normalizer (O : Set G) := hNO hsN
  have hAN : A ≤ Subgroup.normalizer (Lc : Set G) := hAC.trans hCN
  have hT2 : IsPGroup 2 T :=
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (H ⊓ M)).to_le
      (Subgroup.zpowers_le.mpr hsS)).to_sup_of_normal_right' hO2 (Subgroup.zpowers_le.mpr hsO)
  have hOM : O ≤ M := by
    have hθ := Sec19.Step1914MoreSProof.theta_le_gamma hA hAN
    intro x hx
    refine h.mem_scriptM.2 (hθ ⟨⟨x, hOLc hx⟩, ?_, rfl⟩)
    exact (solvable_prime_complement_core_characterization (H := Lc) Nat.prime_three).2.2.2.2.2.2
      2 Nat.prime_two (by norm_num) ((mem_pCore_iff_mem_pCoreOf (⟨x, hOLc hx⟩ : Lc)).mpr hx)
  have hsM : s ∈ M := ((CFSG.LieType.BorelTits.pCoreOf_le 2 (H ⊓ M)) hsS).2
  have hTM : T ≤ M := sup_le (Subgroup.zpowers_le.mpr hsM) hOM
  have hTN : T ≤ Subgroup.normalizer (Lc : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hsN) (hOLc.trans Subgroup.le_normalizer)
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := fun a ha =>
    Subgroup.inf_normalizer_le_normalizer_sup _ _
      ⟨centralizer_le_normalizer_zpowers s (Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hsA a ha)), hNO (hAN ha)⟩
  have hNT : ∀ x ∈ Subgroup.normalizer (O : Set G), x * s * x⁻¹ * s⁻¹ ∈ O →
      x ∈ Subgroup.normalizer (T : Set G) := by
    intro x hxO hxs
    apply CFSG.GroupTheory.WielandtProduct.mem_normalizer_of_forall_conj_mem
    intro t ht
    have hmap : T.map (MulAut.conj x).toMonoidHom ≤ T := by
      rw [hTdef, Subgroup.map_sup, MonoidHom.map_zpowers, map_conj_eq_of_mem_normalizer hxO]
      refine sup_le ?_ le_sup_right
      rw [Subgroup.zpowers_le]
      have e : (MulAut.conj x).toMonoidHom s = x * s * x⁻¹ * s⁻¹ * s := by simp
      rw [e]
      exact T.mul_mem (Subgroup.mem_sup_right hxs) (Subgroup.mem_sup_left (Subgroup.mem_zpowers s))
    exact hmap ⟨t, ht, by simp⟩
  have hL₀LC : L₀ ≤ L ⊓ C := Subgroup.map_subtype_le _
  have hL₀H : L₀ ≤ H := hL₀LC.trans (inf_le_left.trans hLH)
  have hL₀Lc : L₀ ≤ Lc := le_sup_left.trans hLc_eq.ge
  have hL₀N : L₀ ≤ Subgroup.normalizer (O : Set G) :=
    hL₀Lc.trans (Subgroup.le_normalizer.trans hNO)
  have hHCN : H ⊓ C ≤ Subgroup.normalizer (L₀ : Set G) := by
    refine le_trans ?_
      (CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
        (L ⊓ C))
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_inSubgroup_perfectResidual H hx.1, Subgroup.le_normalizer hx.2⟩
  have hsL₀ : s ∈ Subgroup.normalizer (L₀ : Set G) := hHCN ⟨hsH, hsC⟩
  have hL₀O : CFSG.Open.pCoreOf 2 L₀ ≤ O := by
    have hker : (O.subgroupOf Lc).map (QuotientGroup.mk' (CFSG.pCore 2 Lc)) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      intro x hx
      rw [mem_pCore_iff_mem_pCoreOf]
      exact Subgroup.mem_subgroupOf.mp hx
    have himg : (L₀.subgroupOf Lc).map (QuotientGroup.mk' (CFSG.pCore 2 Lc)) = ⊤ := by
      refine eq_top_iff.mpr ?_
      calc (⊤ : Subgroup (Lc ⧸ CFSG.pCore 2 Lc))
          = (⊤ : Subgroup Lc).map (QuotientGroup.mk' (CFSG.pCore 2 Lc)) :=
            (Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)).symm
        _ ≤ ((L₀ ⊔ O).subgroupOf Lc).map (QuotientGroup.mk' (CFSG.pCore 2 Lc)) :=
            Subgroup.map_mono fun x _ => Subgroup.mem_subgroupOf.mpr (hLc_eq.le x.2)
        _ = (L₀.subgroupOf Lc).map (QuotientGroup.mk' (CFSG.pCore 2 Lc)) := by
            rw [Subgroup.subgroupOf_sup hL₀Lc hOLc, Subgroup.map_sup, hker, sup_bot_eq]
    exact Claim184LcProof.pCoreOf_le_of_map_eq hL₀Lc himg
  have hL₀s : ∀ l ∈ L₀, l ∈ M → l * s * l⁻¹ * s⁻¹ ∈ O := by
    intro l hl hlM
    have h1 : l * s * l⁻¹ * s⁻¹ ∈ CFSG.Open.pCoreOf 2 H :=
      commutator_mem_pCoreOf_of_relIndex_eq_two hS hidx (hL₀H hl) hlM
    have h2 : l * s * l⁻¹ * s⁻¹ ∈ L₀ := by
      have : s * l⁻¹ * s⁻¹ ∈ L₀ := (Subgroup.mem_normalizer_iff.mp hsL₀ _).mp (L₀.inv_mem hl)
      have e : l * s * l⁻¹ * s⁻¹ = l * (s * l⁻¹ * s⁻¹) := by group
      rw [e]
      exact L₀.mul_mem hl this
    have h3 : L₀ ⊓ CFSG.Open.pCoreOf 2 H ≤ CFSG.Open.pCoreOf 2 L₀ :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
        (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx,
          CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hL₀H hx)⟩)
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_right)
    exact hL₀O (h3 ⟨h2, h1⟩)
  have hON : O ≤ Subgroup.normalizer (T : Set G) := by
    intro o ho
    refine hNT o (Subgroup.le_normalizer ho) ?_
    have : s * o⁻¹ * s⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp hsO _).mp (O.inv_mem ho)
    have e : o * s * o⁻¹ * s⁻¹ = o * (s * o⁻¹ * s⁻¹) := by group
    rw [e]
    exact O.mul_mem ho this
  have hLcMN : Lc ⊓ M ≤ Subgroup.normalizer (T : Set G) := by
    have hle : (L₀ ⊔ O) ⊓ M ≤ L₀ ⊓ M ⊔ O :=
      sup_inf_le_inf_sup hOM (Subgroup.coe_mul_of_left_le_normalizer_right L₀ O hL₀N)
    exact (inf_le_inf_right M hLc_eq.le).trans (hle.trans
      (sup_le (fun l hl => hNT l (hL₀N hl.1) (hL₀s l hl.1 hl.2)) hON))
  set Y := Lc ⊔ A ⊔ T with hYdef
  have hYMN : Y ⊓ M ≤ Subgroup.normalizer (T : Set G) := by
    have hY : Y = Lc ⊔ (A ⊔ T) := by rw [hYdef, sup_assoc]
    have hle : (Lc ⊔ (A ⊔ T)) ⊓ M ≤ Lc ⊓ M ⊔ (A ⊔ T) :=
      sup_inf_le_inf_sup (sup_le hAM hTM)
        (Subgroup.coe_mul_of_right_le_normalizer_left Lc (A ⊔ T) (sup_le hAN hTN))
    rw [hY]
    exact hle.trans (sup_le hLcMN (sup_le hAT Subgroup.le_normalizer))
  have hsY : s ∉ CFSG.Open.pCoreOf 2 Y := by
    intro hsY
    set Y₀ := L₀ ⊔ A ⊔ Subgroup.zpowers s with hY₀def
    have hY₀Y : Y₀ ≤ Y :=
      sup_le (sup_le (hL₀Lc.trans (le_sup_left.trans le_sup_left))
        (le_sup_right.trans le_sup_left)) ((le_sup_left : Subgroup.zpowers s ≤ T).trans le_sup_right)
    have hY₀N : Y₀ ≤ Subgroup.normalizer (L₀ : Set G) :=
      sup_le (sup_le Subgroup.le_normalizer fun a ha => hHCN ⟨hAH ha, hAC ha⟩)
        (Subgroup.zpowers_le.mpr hsL₀)
    obtain ⟨hL₀img, hL₀OH⟩ := map_perfectResidual_inf_centralizer_eq hH
    refine Claim184LcProof.not_mem_pCoreOf_of_inducesOuterTheta hsH (le_sup_left.trans le_sup_left)
      hY₀N hL₀img hL₀OH hout ?_
    have hle : CFSG.Open.pCoreOf 2 Y ⊓ Y₀ ≤ CFSG.Open.pCoreOf 2 Y₀ :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
        (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y (hY₀Y hx), Subgroup.le_normalizer hx⟩)
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y).to_le inf_le_left)
    exact hle ⟨hsY, Subgroup.mem_sup_right (Subgroup.mem_zpowers s)⟩
  have hYC : Y ≤ C :=
    sup_le (sup_le hLcC hAC) (sup_le (Subgroup.zpowers_le.mpr hsC) (hOLc.trans hLcC))
  have hYtop : Y ≠ ⊤ := fun htop =>
    Claim184LcProof.centralizer_ne_top h hc1 (top_le_iff.mp (htop.symm.le.trans hYC))
  exact sup_mem_scriptH_of_ne_top h hYtop hLcp (isQuasisimple_of_mem_oTwoComponentsIn hLcK) hT2 hTM
    hAN hTN hAT hYMN fun hle => hsY (hle (Subgroup.mem_sup_left (Subgroup.mem_zpowers s)))

end SylowInner

end CFSG.RankThree.PartTwo.Sec18
