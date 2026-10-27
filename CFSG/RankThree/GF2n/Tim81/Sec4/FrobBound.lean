module

public import CFSG.RankThree.GF2n.Tim81.Sec4.KElem
public import CFSG.RankThree.GF2n.Tim78S48PhaseGen
public import CFSG.GroupTheory.SteinbergCBFTFactorization
public import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.ReductionFixed

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V H : Subgroup G}

namespace RootHyp

private theorem V_le_centralizer_sup_Pc_kOf (M V H : Subgroup G) :
    V ≤ Subgroup.centralizer ((Pc M V ⊔ kOf V H : Subgroup G) : Set G) := by
  have hPC : Pc M V ≤ Subgroup.centralizer (V : Set G) := inf_le_right
  have hKC : kOf V H ≤ Subgroup.centralizer (V : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact Subgroup.mem_centralizer_iff.mp (mem_kOf_iff.mp hk).2 v (le_xOf_self V H hv)
  have hsup : Pc M V ⊔ kOf V H ≤ Subgroup.centralizer (V : Set G) := sup_le hPC hKC
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact (Subgroup.mem_centralizer_iff.mp (hsup hx) v hv).symm

private noncomputable def conjHK (V H : Subgroup G) : ↥H →* MulAut ↥(kOf V H) :=
  (Subgroup.normalizerMonoidHom (H := kOf V H)).comp
    (Subgroup.inclusion (le_normalizer_kOf V H))

private theorem conjHK_apply_coe (h : ↥H) (k : ↥(kOf V H)) :
    ((conjHK V H h k : ↥(kOf V H)) : G) = (h : G) * k * (h : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe (kOf V H)
    (Subgroup.inclusion (le_normalizer_kOf V H) h) k

private theorem conjHK_eq_one_of_mem {hcomm : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H,
    x * y = y * x} {z : ↥H} (hz : z ∈ (kOf V H).subgroupOf H) :
    conjHK V H z = 1 := by
  ext k
  rw [conjHK_apply_coe]
  simp only [MulAut.one_apply, Subgroup.coe_subtype]
  have hzK : (z : G) ∈ kOf V H := Subgroup.mem_subgroupOf.mp hz
  have hzk : (z : G) * (k : G) = (k : G) * (z : G) :=
    hcomm (z : G) hzK (k : G) k.2
  rw [hzk]
  group

private noncomputable def conjK (hcomm : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x) :
    HBar V H →* MulAut ↥(kOf V H) :=
  QuotientGroup.lift ((kOf V H).subgroupOf H) (conjHK V H)
    fun _ hz => MonoidHom.mem_ker.mpr (conjHK_eq_one_of_mem (hcomm := hcomm) hz)

private theorem conjK_apply (hcomm : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x)
    (z : ↥H) (k : ↥(kOf V H)) :
    conjK hcomm (piK V H z) k = conjHK V H z k :=
  congrArg (fun f : MulAut ↥(kOf V H) => f k)
    (QuotientGroup.lift_mk' ((kOf V H).subgroupOf H) (φ := conjHK V H)
      (fun _ hz => MonoidHom.mem_ker.mpr (conjHK_eq_one_of_mem (hcomm := hcomm) hz)) z)

private theorem conjK_apply_coe (hcomm : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x)
    (z : ↥H) (k : ↥(kOf V H)) :
    ((conjK hcomm (piK V H z) k : ↥(kOf V H)) : G) = (z : G) * k * (z : G)⁻¹ := by
  rw [conjK_apply, conjHK_apply_coe]

private theorem not_le_normalizer_inf (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hab : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x) :
    ¬ M ≤ Subgroup.normalizer (Pc M V ⊓ kOf V H : Set G) := by
  intro hMN
  have hY_le_M : Pc M V ⊓ kOf V H ≤ M := inf_le_left.trans h.toHyp.Pc_le_M
  have hY_comm : IsMulCommutative ↥(Pc M V ⊓ kOf V H) :=
    ⟨⟨fun a b => Subtype.ext
      (hab a ((inf_le_right : Pc M V ⊓ kOf V H ≤ kOf V H) a.2)
        b ((inf_le_right : Pc M V ⊓ kOf V H ≤ kOf V H) b.2))⟩⟩
  have hVlt := lt_Pc_inf_kOf h hPH hVH hnM hK
  have hY_le_V : Pc M V ⊓ kOf V H ≤ V :=
    h.maxAb.le_of_ge ⟨hY_le_M, hMN, hY_comm⟩ hVlt.le
  exact (not_le_of_gt hVlt) hY_le_V

private theorem comap_normalizer_imgK_le_normalizer_inf (h : RootHyp M V)
    (hPH : Pc M V ≤ H) :
    (Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H))).comap (piK V H) ≤
      (Subgroup.normalizer (Pc M V ⊓ kOf V H : Set G)).comap H.subtype := by
  intro n hn
  have hnbar : piK V H n ∈ Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H)) := hn
  have hcomap : (Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H))).comap (piK V H) =
      Subgroup.normalizer (((Pc M V).subgroupOf H ⊔ (kOf V H).subgroupOf H :
        Subgroup ↥H) : Set ↥H) := by
    rw [imgK, Subgroup.comap_normalizer_eq_of_le_range
      (Subgroup.map_le_range (piK V H) ((Pc M V).subgroupOf H))]
    rw [Subgroup.comap_map_eq (piK V H) ((Pc M V).subgroupOf H)]
    have hker : (piK V H).ker = (kOf V H).subgroupOf H := by
      simpa [piK] using (QuotientGroup.ker_mk' ((kOf V H).subgroupOf H))
    rw [hker]
  have hnN : n ∈ Subgroup.normalizer
      (((Pc M V).subgroupOf H ⊔ (kOf V H).subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    rw [← hcomap]
    exact hnbar
  have hnN_G : (n : G) ∈ Subgroup.normalizer
      (((Pc M V).subgroupOf H ⊔ (kOf V H).subgroupOf H : Subgroup ↥H).map
        H.subtype : Set G) :=
    Subgroup.le_normalizer_map H.subtype ⟨n, hnN, rfl⟩
  have hmap : (((Pc M V).subgroupOf H ⊔ (kOf V H).subgroupOf H : Subgroup ↥H).map
      H.subtype) = Pc M V ⊔ kOf V H := by
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hPH,
      Subgroup.map_subgroupOf_eq_of_le (kOf_le V H)]
  rw [hmap] at hnN_G
  have hV_eq : V = Tim79a.xOf V H ⊓ Subgroup.centralizer
      ((Pc M V ⊔ kOf V H : Subgroup G) : Set G) := by
    refine le_antisymm (le_inf (le_xOf_self V H) (V_le_centralizer_sup_Pc_kOf M V H)) ?_
    intro x hx
    have hxP : x ∈ Subgroup.centralizer (Pc M V : Set G) :=
      Subgroup.centralizer_le (fun x hx => Subgroup.mem_sup_left hx) hx.2
    rwa [h.toHyp.centralizer_Pc] at hxP
  have hnW : (n : G) ∈ Subgroup.normalizer (Tim79a.xOf V H : Set G) :=
    Tim79a.H_le_normalizer_xOf V H n.2
  have hnV : (n : G) ∈ Subgroup.normalizer (V : Set G) := by
    rw [hV_eq]
    exact mem_normalizer_inf hnW (mem_normalizer_centralizer hnN_G)
  have hnM : (n : G) ∈ M := by
    rw [← h.toHyp.normalizer_eq]
    exact hnV
  have hnP : (n : G) ∈ Subgroup.normalizer (Pc M V : Set G) :=
    h.toHyp.le_normalizer_Pc hnM
  have hnK : (n : G) ∈ Subgroup.normalizer (kOf V H : Set G) :=
    le_normalizer_kOf V H n.2
  exact Subgroup.mem_comap.mpr (mem_normalizer_inf hnP hnK)


private abbrev kInf (M V H : Subgroup G) : Subgroup G :=
  Pc M V ⊓ kOf V H

private abbrev kInfK (M V H : Subgroup G) : Subgroup ↥(kOf V H) :=
  (kInf M V H).subgroupOf (kOf V H)

private abbrev kNbar (M V H : Subgroup G) : Subgroup (HBar V H) :=
  Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H))

private theorem exists_conj_kInf (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hab : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x) :
    ∃ g ∈ M, conjSubgroup g (kInf M V H) ≠ kInf M V H ∧
      conjSubgroup g (kInf M V H) ≤ Pc M V ∧ ¬ conjSubgroup g (kInf M V H) ≤ kOf V H := by
  classical
  have hnot := not_le_normalizer_inf h hPH hVH hnM hK hab
  obtain ⟨g, hgM, hgN⟩ := SetLike.not_le_iff_exists.mp hnot
  have hne : conjSubgroup g (kInf M V H) ≠ kInf M V H :=
    fun heq => hgN (conjSubgroup_eq_self_iff.mp heq)
  have hgP : conjSubgroup g (Pc M V) = Pc M V :=
    conjSubgroup_eq_self_iff.mpr (h.toHyp.le_normalizer_Pc hgM)
  have hX_le_P : conjSubgroup g (kInf M V H) ≤ Pc M V := by
    calc conjSubgroup g (kInf M V H) ≤ conjSubgroup g (Pc M V) :=
          Subgroup.map_mono inf_le_left
      _ = Pc M V := hgP
  have hX_not_le_K : ¬ conjSubgroup g (kInf M V H) ≤ kOf V H := by
    intro hXK
    have hX_le_Y : conjSubgroup g (kInf M V H) ≤ kInf M V H := le_inf hX_le_P hXK
    have hcard : Nat.card ↥(conjSubgroup g (kInf M V H)) = Nat.card ↥(kInf M V H) :=
      card_conjSubgroup g (kInf M V H)
    exact hne (Subgroup.eq_of_le_of_card_ge hX_le_Y (by rw [hcard]))
  exact ⟨g, hgM, hne, hX_le_P, hX_not_le_K⟩

private theorem map_conjK_kInfK_le (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hab : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x)
    {n : HBar V H} (hn : n ∈ kNbar M V H) :
    (kInfK M V H).map (conjK hab n).toMonoidHom ≤ kInfK M V H := by
  intro z hz
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
  obtain ⟨h0, hh0⟩ := piK_surjective V H n
  have hh0N : h0 ∈ (kNbar M V H).comap (piK V H) := by
    rw [Subgroup.mem_comap]
    simpa [hh0] using hn
  have hh0Y : (h0 : G) ∈ Subgroup.normalizer (kInf M V H : Set G) :=
    comap_normalizer_imgK_le_normalizer_inf h hPH hh0N
  have hwY : (w : G) ∈ kInf M V H := Subgroup.mem_subgroupOf.mp hw
  have hconj : (h0 : G) * (w : G) * (h0 : G)⁻¹ ∈ kInf M V H :=
    (Subgroup.mem_normalizer_iff.mp hh0Y (w : G)).mp hwY
  have hval : (((conjK hab n) w : ↥(kOf V H)) : G) =
      (h0 : G) * (w : G) * (h0 : G)⁻¹ := by
    rw [← hh0]
    exact conjK_apply_coe hab h0 w
  have hmemK : (((conjK hab n) w : ↥(kOf V H)) : G) ∈ kInf M V H := by
    rw [hval]
    exact hconj
  exact Subgroup.mem_subgroupOf.mpr hmemK

private theorem map_conjK_kInfK_eq (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hab : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x)
    {n : HBar V H} (hn : n ∈ kNbar M V H) :
    (kInfK M V H).map (conjK hab n).toMonoidHom = kInfK M V H := by
  refine Subgroup.eq_of_le_of_card_ge (map_conjK_kInfK_le h hPH hab hn) ?_
  rw [Subgroup.card_map_of_injective (conjK hab n).injective]

private noncomputable def conjY (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hab : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x) :
    ↥(kNbar M V H) →* MulAut ↥(kInfK M V H) where
  toFun n := CFSG.AGLEmbedding.TrialityTwo.restrictAut (conjK hab (n : HBar V H))
    (kInfK M V H) (map_conjK_kInfK_eq h hPH hab n.2)
  map_one' := by
    ext y
    rw [CFSG.AGLEmbedding.TrialityTwo.restrictAut_apply]
    rw [show ((1 : ↥(kNbar M V H)) : HBar V H) = 1 from rfl, map_one]
    rfl
  map_mul' n1 n2 := by
    ext y
    simp only [CFSG.AGLEmbedding.TrialityTwo.restrictAut_apply]
    rw [MulAut.mul_apply]
    simp only [CFSG.AGLEmbedding.TrialityTwo.restrictAut_apply]
    rw [show ((n1 * n2 : ↥(kNbar M V H)) : HBar V H) =
      (n1 : HBar V H) * (n2 : HBar V H) from rfl, map_mul]
    rfl


theorem card_imgK_mul_card_inf {X : Subgroup G} (hXH : X ≤ H) :
    Nat.card ↥(imgK V H X) * Nat.card ↥(X ⊓ kOf V H) = Nat.card ↥X := by
  have hS : (X.subgroupOf H).map (piK V H) = imgK V H X := rfl
  have hker : X.subgroupOf H ⊓ (piK V H).ker = (X ⊓ kOf V H).subgroupOf H := by
    have hKker : (piK V H).ker = (kOf V H).subgroupOf H := by
      simpa [piK] using (QuotientGroup.ker_mk' ((kOf V H).subgroupOf H))
    rw [hKker]
    ext x
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_inf, and_assoc]
  have h1 := CFSG.GroupTheory.FT63ChII.card_eq_card_map_mul_card_inf (piK V H)
    (X.subgroupOf H)
  rw [hS, inf_comm (piK V H).ker (X.subgroupOf H), hker] at h1
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left.trans hXH : X ⊓ kOf V H ≤ H)).toEquiv] at h1
  exact h1.symm


private theorem conjY_apply_coe (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hab : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x)
    (a : ↥(kNbar M V H)) (y : ↥(kInfK M V H)) :
    ((((conjY h hPH hVH hH hnM hK hab) a y : ↥(kInfK M V H)) : ↥(kOf V H)) : G) =
      (((conjK hab (a : HBar V H) y.1 : ↥(kOf V H)) : G)) := by
  simp only [conjY]
  have h := CFSG.AGLEmbedding.TrialityTwo.restrictAut_apply (conjK hab (a : HBar V H))
    (kInfK M V H) (map_conjK_kInfK_eq h hPH hab a.2) y
  exact congrArg (fun z : ↥(kOf V H) => (z : G)) h

private theorem subgroupOf_inf_le_fixedSub_map (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hab : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x)
    {X : Subgroup G} (hXcomm : IsMulCommutative ↥X) :
    ((kInf M V H ⊓ X).subgroupOf (kOf V H)) ≤
      (fixedSub (conjY h hPH hVH hH hnM hK hab)
        ((imgK V H X).subgroupOf (kNbar M V H))).map
        (kInfK M V H).subtype := by
  intro x hx
  have hxY : (x : G) ∈ kInf M V H := (Subgroup.mem_subgroupOf.mp hx).1
  have hxX : (x : G) ∈ X := (Subgroup.mem_subgroupOf.mp hx).2
  refine Subgroup.mem_map.mpr ⟨⟨x, Subgroup.mem_subgroupOf.mpr hxY⟩, ?_, rfl⟩
  rw [mem_fixedSub]
  intro a ha
  have ha' : a.1 ∈ imgK V H X := Subgroup.mem_subgroupOf.mp ha
  apply Subtype.ext
  apply Subtype.ext
  rw [conjY_apply_coe]
  obtain ⟨z, hzX, hza⟩ := Subgroup.mem_map.mp ha'
  rw [← hza]
  rw [conjK_apply_coe]
  have hcomm : (z : G) * (x : G) = (x : G) * (z : G) :=
    congrArg Subtype.val (hXcomm.is_comm.comm ⟨z, hzX⟩ ⟨x, hxX⟩)
  rw [hcomm]
  group


private theorem fixedSub_conjY_eq (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hab : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x) :
    fixedSub (conjY h hPH hVH hH hnM hK hab)
        ((imgK V H (Pc M V)).subgroupOf (kNbar M V H)) =
      (V.subgroupOf (kOf V H)).subgroupOf (kInfK M V H) := by
  ext y
  rw [mem_fixedSub]
  constructor
  · intro hy
    have hcent : (y : G) ∈ Subgroup.centralizer (Pc M V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have hpImg : piK V H ⟨p, hPH hp⟩ ∈ imgK V H (Pc M V) :=
        Subgroup.mem_map.mpr ⟨⟨p, hPH hp⟩, Subgroup.mem_subgroupOf.mpr hp, rfl⟩
      have hpN : piK V H ⟨p, hPH hp⟩ ∈ kNbar M V H :=
        (imgK_mono (le_refl (Pc M V))).trans Subgroup.le_normalizer hpImg
      have hpL : (⟨piK V H ⟨p, hPH hp⟩, hpN⟩ : ↥(kNbar M V H)) ∈
          (imgK V H (Pc M V)).subgroupOf (kNbar M V H) :=
        Subgroup.mem_subgroupOf.mpr hpImg
      have hfix := hy ⟨piK V H ⟨p, hPH hp⟩, hpN⟩ hpL
      have hcoe := congrArg (fun z : ↥(kInfK M V H) =>
        ((((z : ↥(kOf V H)) : G)))) hfix
      rw [conjY_apply_coe] at hcoe
      rw [conjK_apply_coe] at hcoe
      calc p * (y : G) = p * (y : G) * p⁻¹ * p := by group
        _ = (y : G) * p := by rw [hcoe]
    have hCV : Subgroup.centralizer (Pc M V : Set G) ≤ V :=
      le_of_eq h.toHyp.centralizer_Pc
    have hyV : (y : G) ∈ V := hCV hcent
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hyV)
  · intro hy
    intro a ha
    have ha' : a.1 ∈ imgK V H (Pc M V) := Subgroup.mem_subgroupOf.mp ha
    obtain ⟨p, hpP, hpa⟩ := Subgroup.mem_map.mp ha'
    have hyV : (y : G) ∈ V :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hy)
    apply Subtype.ext
    apply Subtype.ext
    rw [conjY_apply_coe]
    rw [← hpa]
    rw [conjK_apply_coe]
    have hpy : (p : G) * (y : G) = (y : G) * (p : G) :=
      (Subgroup.mem_centralizer_iff.mp
        ((inf_le_right : Pc M V ≤ Subgroup.centralizer (V : Set G)) hpP)
        (y : G) hyV).symm
    rw [hpy]
    group


private theorem card_le_mul_fixedSub (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hab : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x)
    {X : Subgroup G} (hX_le_P : X ≤ Pc M V) (hXcomm : IsMulCommutative ↥X)
    (hXcard : Nat.card ↥X = Nat.card ↥(kInf M V H)) :
    Nat.card ↥(kInfK M V H) ≤ Nat.card (imgK V H X) * Nat.card ↥(fixedSub
      (conjY h hPH hVH hH hnM hK hab) ((imgK V H X).subgroupOf (kNbar M V H))) := by
  have hcardX := card_imgK_mul_card_inf (V := V) (H := H) (X := X) (hX_le_P.trans hPH)
  have hcontain := subgroupOf_inf_le_fixedSub_map h hPH hVH hH hnM hK hab hXcomm
  have hle_fixed : Nat.card ↥(kInf M V H ⊓ X) ≤
      Nat.card ↥(fixedSub (conjY h hPH hVH hH hnM hK hab)
        ((imgK V H X).subgroupOf (kNbar M V H))) := by
    have h1 : Nat.card ↥((kInf M V H ⊓ X).subgroupOf (kOf V H)) =
        Nat.card ↥(kInf M V H ⊓ X) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left.trans (inf_le_right : kInf M V H ≤ kOf V H))).toEquiv
    have h2 : Nat.card ↥((fixedSub (conjY h hPH hVH hH hnM hK hab)
          ((imgK V H X).subgroupOf (kNbar M V H))).map (kInfK M V H).subtype) =
        Nat.card ↥(fixedSub (conjY h hPH hVH hH hnM hK hab)
          ((imgK V H X).subgroupOf (kNbar M V H))) :=
      Subgroup.card_map_of_injective (kInfK M V H).subtype_injective
    rw [← h1, ← h2]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hcontain)
  have hcardX' : Nat.card (imgK V H X) * Nat.card ↥(kInf M V H ⊓ X) =
      Nat.card ↥X := by
    have hEq : kInf M V H ⊓ X = X ⊓ kOf V H := by
      rw [kInf, inf_assoc, inf_comm (kOf V H) X, ← inf_assoc,
        inf_eq_right.mpr hX_le_P]
    rw [hEq]
    exact hcardX
  calc Nat.card ↥(kInfK M V H)
      = Nat.card ↥(kInf M V H) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (inf_le_right : kInf M V H ≤ kOf V H)).toEquiv
    _ = Nat.card ↥X := hXcard.symm
    _ = Nat.card (imgK V H X) * Nat.card ↥(kInf M V H ⊓ X) := hcardX'.symm
    _ ≤ Nat.card (imgK V H X) * Nat.card ↥(fixedSub (conjY h hPH hVH hH hnM hK hab)
          ((imgK V H X).subgroupOf (kNbar M V H))) :=
        Nat.mul_le_mul_left _ hle_fixed

private theorem exists_X_bound (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hab : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x) :
    ∃ X : Subgroup G, X ≤ Pc M V ∧ imgK V H X ≠ ⊥ ∧
      Nat.card ↥(kInfK M V H) ≤ Nat.card (imgK V H X) *
        Nat.card ↥(fixedSub (conjY h hPH hVH hH hnM hK hab)
          ((imgK V H X).subgroupOf (kNbar M V H))) := by
  classical
  obtain ⟨g, hgM, hne, hX_le_P, hX_not_le_K⟩ :=
    exists_conj_kInf h hPH hVH hnM hK hab
  let X : Subgroup G := conjSubgroup g (kInf M V H)
  have hXcomm : IsMulCommutative ↥X := by
    letI : IsMulCommutative ↥(kInf M V H) :=
      ⟨⟨fun a b => Subtype.ext
        (hab a ((inf_le_right : kInf M V H ≤ kOf V H) a.2)
          b ((inf_le_right : kInf M V H ≤ kOf V H) b.2))⟩⟩
    exact Subgroup.map_isMulCommutative (kInf M V H) (MulAut.conj g).toMonoidHom
  have hXcard : Nat.card ↥X = Nat.card ↥(kInf M V H) :=
    card_conjSubgroup g (kInf M V H)
  have hA_bound := card_le_mul_fixedSub h hPH hVH hH hnM hK hab hX_le_P hXcomm hXcard
  have hA_ne : imgK V H X ≠ ⊥ := by
    intro hbot
    apply hX_not_le_K
    intro x hx
    have hxX : x ∈ X := by simpa [X] using hx
    have hxH : x ∈ H := (hX_le_P.trans hPH) hxX
    have hker : (piK V H).ker = (kOf V H).subgroupOf H := by
      simpa [piK] using (QuotientGroup.ker_mk' ((kOf V H).subgroupOf H))
    have hbot' : (X.subgroupOf H).map (piK V H) = ⊥ := hbot
    have hle : X.subgroupOf H ≤ (piK V H).ker := (Subgroup.map_eq_bot_iff _).mp hbot'
    rw [hker] at hle
    have hxH' : (⟨x, hxH⟩ : ↥H) ∈ X.subgroupOf H :=
      Subgroup.mem_subgroupOf.mpr hxX
    exact Subgroup.mem_subgroupOf.mp (hle hxH')
  exact ⟨X, hX_le_P, hA_ne, hA_bound⟩

private theorem frobenius_fixedSub_bound_data (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hab : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x)
    {X : Subgroup G} (hX_le_P : X ≤ Pc M V) (hA_ne : imgK V H X ≠ ⊥)
    (hA_bound : Nat.card ↥(kInfK M V H) ≤ Nat.card (imgK V H X) *
      Nat.card ↥(fixedSub (conjY h hPH hVH hH hnM hK hab)
        ((imgK V H X).subgroupOf (kNbar M V H)))) :
    ∃ AΓ : Subgroup ↥(kNbar M V H),
      AΓ ≤ (imgK V H (Pc M V)).subgroupOf (kNbar M V H) ∧ AΓ ≠ ⊥ ∧
      Nat.card ↥(kInfK M V H) ≤
        Nat.card ↥AΓ * Nat.card ↥(fixedSub (conjY h hPH hVH hH hnM hK hab) AΓ) := by
  let AΓ : Subgroup ↥(kNbar M V H) := (imgK V H X).subgroupOf (kNbar M V H)
  have hA_le_N : imgK V H X ≤ kNbar M V H :=
    (imgK_mono hX_le_P).trans (Subgroup.le_normalizer)
  have hAΓcard : Nat.card ↥AΓ = Nat.card (imgK V H X) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA_le_N).toEquiv
  have hAΓ_le : AΓ ≤ (imgK V H (Pc M V)).subgroupOf (kNbar M V H) := by
    intro a ha
    exact Subgroup.mem_subgroupOf.mpr ((imgK_mono hX_le_P) (Subgroup.mem_subgroupOf.mp ha))
  have hAΓ_ne : AΓ ≠ ⊥ := by
    intro hbot
    have hAΓ_eq : AΓ = (imgK V H X).subgroupOf (kNbar M V H) := rfl
    have hbot' : (imgK V H X).subgroupOf (kNbar M V H) =
        (⊥ : Subgroup (HBar V H)).subgroupOf (kNbar M V H) := by
      rw [← hAΓ_eq, hbot]
      simp
    have hinf : imgK V H X ⊓ kNbar M V H = ⊥ := by
      simpa using (Subgroup.subgroupOf_inj.mp hbot')
    have hEq : imgK V H X ⊓ kNbar M V H = imgK V H X :=
      inf_eq_left.mpr hA_le_N
    rw [hEq] at hinf
    exact hA_ne hinf
  have hAΓ_bound : Nat.card ↥(kInfK M V H) ≤
      Nat.card ↥AΓ * Nat.card ↥(fixedSub (conjY h hPH hVH hH hnM hK hab) AΓ) := by
    rw [hAΓcard]
    exact hA_bound
  exact ⟨AΓ, hAΓ_le, hAΓ_ne, hAΓ_bound⟩

private theorem frobenius_apply_aux (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hab : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x)
    {R : Subgroup (HBar V H)}
    (hRN : R ≤ Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H)))
    (hRcard : Nat.card R = Nat.card (imgK V H (Pc M V)) - 1)
    (hRc : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a)
    (hfrob : ∀ r ∈ R, r ≠ 1 → ∀ x ∈ imgK V H (Pc M V), r * x * r⁻¹ = x → x = 1)
    {X : Subgroup G} (hX_le_P : X ≤ Pc M V) (hA_ne : imgK V H X ≠ ⊥)
    (hA_bound : Nat.card ↥(kInfK M V H) ≤ Nat.card (imgK V H X) *
      Nat.card ↥(fixedSub (conjY h hPH hVH hH hnM hK hab)
        ((imgK V H X).subgroupOf (kNbar M V H)))) :
    ∃ (RΓ AΓ : Subgroup ↥(kNbar M V H)),
      Nat.card ↥((imgK V H (Pc M V)).subgroupOf (kNbar M V H)) =
        Nat.card (imgK V H (Pc M V)) ∧
      Nat.card ↥RΓ =
        Nat.card ↥((imgK V H (Pc M V)).subgroupOf (kNbar M V H)) - 1 ∧
      RΓ ≤ Subgroup.normalizer
        (((imgK V H (Pc M V)).subgroupOf (kNbar M V H)) : Set ↥(kNbar M V H)) ∧
      (∀ r ∈ RΓ, r ≠ 1 → ∀ x ∈ (imgK V H (Pc M V)).subgroupOf (kNbar M V H),
        r * x * r⁻¹ = x → x = 1) ∧
      (∀ a ∈ RΓ, ∀ b ∈ RΓ, a * b = b * a) ∧
      AΓ ≤ (imgK V H (Pc M V)).subgroupOf (kNbar M V H) ∧ AΓ ≠ ⊥ ∧
      Nat.card ↥(kInfK M V H) ≤
        Nat.card ↥AΓ * Nat.card ↥(fixedSub (conjY h hPH hVH hH hnM hK hab) AΓ) := by
  let LΓ : Subgroup ↥(kNbar M V H) := (imgK V H (Pc M V)).subgroupOf (kNbar M V H)
  let RΓ : Subgroup ↥(kNbar M V H) := R.subgroupOf (kNbar M V H)
  have hL_le_N : imgK V H (Pc M V) ≤ kNbar M V H := Subgroup.le_normalizer
  have hLΓcard : Nat.card ↥LΓ = Nat.card (imgK V H (Pc M V)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL_le_N).toEquiv
  have hRΓcard : Nat.card ↥RΓ = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRN).toEquiv
  have hKcardΓ : Nat.card ↥RΓ = Nat.card ↥LΓ - 1 := by
    rw [hRΓcard, hLΓcard, hRcard]
  have hKLΓ : RΓ ≤ Subgroup.normalizer (LΓ : Set ↥(kNbar M V H)) := by
    have hN_eq : (Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H))).subgroupOf
        (kNbar M V H) = Subgroup.normalizer (LΓ : Set ↥(kNbar M V H)) := by
      rw [show LΓ = (imgK V H (Pc M V)).subgroupOf (kNbar M V H) from rfl]
      exact Subgroup.subgroupOf_normalizer_eq hL_le_N
    intro r hr
    rw [← hN_eq]
    exact Subgroup.mem_subgroupOf.mpr (hRN (Subgroup.mem_subgroupOf.mp hr))
  have hfrobΓ : ∀ r ∈ RΓ, r ≠ 1 → ∀ x ∈ LΓ, r * x * r⁻¹ = x → x = 1 := by
    intro r hr hr1 x hx hconj
    have hrR : r.1 ∈ R := Subgroup.mem_subgroupOf.mp hr
    have hr1' : r.1 ≠ 1 := fun h1 => hr1 (Subtype.ext h1)
    have hxL : x.1 ∈ imgK V H (Pc M V) := Subgroup.mem_subgroupOf.mp hx
    have hconj' : r.1 * x.1 * r.1⁻¹ = x.1 := congrArg Subtype.val hconj
    exact Subtype.ext (hfrob r.1 hrR hr1' x.1 hxL hconj')
  have hKcΓ : ∀ a ∈ RΓ, ∀ b ∈ RΓ, a * b = b * a := by
    intro a ha b hb
    exact Subtype.ext (hRc a.1 (Subgroup.mem_subgroupOf.mp ha)
      b.1 (Subgroup.mem_subgroupOf.mp hb))
  obtain ⟨AΓ, hAΓ_le, hAΓ_ne, hAΓ_bound⟩ :=
    frobenius_fixedSub_bound_data h hPH hVH hH hnM hK hab hX_le_P hA_ne hA_bound
  exact ⟨RΓ, AΓ, hLΓcard, hKcardΓ, hKLΓ, hfrobΓ, hKcΓ, hAΓ_le, hAΓ_ne, hAΓ_bound⟩

private theorem frobenius_apply (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hab : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x)
    {R : Subgroup (HBar V H)}
    (hRN : R ≤ Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H)))
    (hRcard : Nat.card R = Nat.card (imgK V H (Pc M V)) - 1)
    (hRc : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a)
    (hfrob : ∀ r ∈ R, r ≠ 1 → ∀ x ∈ imgK V H (Pc M V), r * x * r⁻¹ = x → x = 1)
    {X : Subgroup G} (hX_le_P : X ≤ Pc M V) (hA_ne : imgK V H X ≠ ⊥)
    (hA_bound : Nat.card ↥(kInfK M V H) ≤ Nat.card (imgK V H X) *
      Nat.card ↥(fixedSub (conjY h hPH hVH hH hnM hK hab)
        ((imgK V H X).subgroupOf (kNbar M V H))))
    (hYK_elem : Assembly.IsElemAbelian 2 (kInfK M V H)) {nL : ℕ}
    (hnL : Nat.card (imgK V H (Pc M V)) = 2 ^ nL) :
    Nat.card ↥(kInfK M V H) ≤ Nat.card (imgK V H (Pc M V)) *
      Nat.card ↥(fixedSub (conjY h hPH hVH hH hnM hK hab)
        ((imgK V H (Pc M V)).subgroupOf (kNbar M V H))) := by
  obtain ⟨RΓ, AΓ, hLΓcard, hKcardΓ, hKLΓ, hfrobΓ, hKcΓ, hAΓ_le, hAΓ_ne,
    hAΓ_bound⟩ :=
    frobenius_apply_aux h hPH hVH hH hnM hK hab hRN hRcard hRc hfrob hX_le_P hA_ne hA_bound
  have key := tim78_2_4_acting (conjY h hPH hVH hH hnM hK hab)
    (fun a b => hYK_elem.1.is_comm.comm a b)
      (fun a => Subtype.ext (by simpa [pow_two] using hYK_elem.2 a.1 a.2))
    (L := (imgK V H (Pc M V)).subgroupOf (kNbar M V H)) (K := RΓ) (n := nL)
    (by rw [hLΓcard, hnL]) hKcardΓ hKLΓ hfrobΓ hKcΓ
    ⟨AΓ, hAΓ_le, hAΓ_ne, hAΓ_bound⟩
  rw [hLΓcard] at key
  exact key


private theorem frobenius_key (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hab : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x)
    {R : Subgroup (HBar V H)}
    (hRN : R ≤ Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H)))
    (hRcard : Nat.card R = Nat.card (imgK V H (Pc M V)) - 1)
    (hRc : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a)
    (hfrob : ∀ r ∈ R, r ≠ 1 → ∀ x ∈ imgK V H (Pc M V), r * x * r⁻¹ = x → x = 1) :
    Nat.card ↥(kInfK M V H) ≤ Nat.card (imgK V H (Pc M V)) *
      Nat.card ↥(fixedSub (conjY h hPH hVH hH hnM hK hab)
        ((imgK V H (Pc M V)).subgroupOf (kNbar M V H))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨X, hX_le_P, hA_ne, hA_bound⟩ := exists_X_bound h hPH hVH hH hnM hK hab
  have hK_elem : Assembly.IsElemAbelian 2 (kOf V H) :=
    isElemAbelian_kOf h hPH hH hnM hK hab
  have hYK_elem : Assembly.IsElemAbelian 2 (kInfK M V H) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hK_elem.1.is_comm.comm a.1 b.1)⟩⟩, ?_⟩
    intro a ha
    apply Subtype.ext
    simpa [pow_two] using hK_elem.2 a.1 a.2
  have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  have hP2H : IsPGroup 2 ((Pc M V).subgroupOf H) := hP2.comap_subtype
  have hL2 : IsPGroup 2 (imgK V H (Pc M V)) := hP2H.map (piK V H)
  obtain ⟨nL, hnL⟩ := hL2.exists_card_eq
  exact frobenius_apply h hPH hVH hH hnM hK hab hRN hRcard hRc hfrob
    hX_le_P hA_ne hA_bound hYK_elem hnL

theorem card_Pc_inf_kOf_le (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hab : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x)
    {R : Subgroup (HBar V H)}
    (hRN : R ≤ Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H)))
    (hRcard : Nat.card R = Nat.card (imgK V H (Pc M V)) - 1)
    (hRc : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a)
    (hfrob : ∀ r ∈ R, r ≠ 1 → ∀ x ∈ imgK V H (Pc M V), r * x * r⁻¹ = x → x = 1) :
    Nat.card ↥(Pc M V ⊓ kOf V H) ≤ Nat.card (imgK V H (Pc M V)) * Nat.card V := by
  have key := frobenius_key h hPH hVH hH hnM hK hab hRN hRcard hRc hfrob
  have hV_le_kInf : V ≤ kInf M V H := le_inf h.toHyp.le_Pc (le_kOf h hPH hVH)
  have hVK_inf : V.subgroupOf (kOf V H) ≤ kInfK M V H := by
    intro v hv
    exact Subgroup.mem_subgroupOf.mpr (hV_le_kInf (Subgroup.mem_subgroupOf.mp hv))
  have hfix : Nat.card ↥(fixedSub (conjY h hPH hVH hH hnM hK hab)
        ((imgK V H (Pc M V)).subgroupOf (kNbar M V H))) = Nat.card V := by
    rw [fixedSub_conjY_eq h hPH hVH hH hnM hK hab]
    exact Nat.card_congr ((Subgroup.subgroupOfEquivOfLe hVK_inf).trans
      (Subgroup.subgroupOfEquivOfLe (hV_le_kInf.trans
        (inf_le_right : kInf M V H ≤ kOf V H)))).toEquiv
  rw [hfix] at key
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (inf_le_right : kInf M V H ≤ kOf V H)).toEquiv] at key
  exact key
end RootHyp

end CFSG.RankThree.GF2n.Tim81
