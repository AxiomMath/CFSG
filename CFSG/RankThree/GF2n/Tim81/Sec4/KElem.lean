module

public import CFSG.RankThree.GF2n.Tim81.TIQuotient
public import CFSG.RankThree.GF2n.Tim81.Sec4.Inputs

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V H : Subgroup G}

theorem kOf_le_centralizer_V (V H : Subgroup G) :
    kOf V H ≤ Subgroup.centralizer (V : Set G) := by
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact Subgroup.mem_centralizer_iff.mp (mem_kOf_iff.mp hk).2 v (le_xOf_self V H hv)

namespace RootHyp

theorem kOf_le_M (h : RootHyp M V) : kOf V H ≤ M := by
  obtain ⟨⟨v, hvV⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.toHyp.ne_bot
  have hv1' : v ≠ 1 := fun h1 => hv1 (Subtype.ext h1)
  intro k hk
  have hkv : k * v = v * k :=
    (Subgroup.mem_centralizer_iff.mp ((mem_kOf_iff.mp hk).2) v
      (le_xOf_self V H hvV)).symm
  exact h.toHyp.centralizer_le_M hvV hv1'
    (Subgroup.mem_centralizer_singleton_iff.mpr hkv)

theorem le_kOf (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) : V ≤ kOf V H :=
  (le_xOf_self V H).trans (xOf_le_kOf h hPH hVH)

theorem conjSubgroup_ne_self (h : RootHyp M V) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M) :
    conjSubgroup h₀ V ≠ V := by
  intro hV
  have hhM : h₀ ∈ M := by
    rw [← h.toHyp.normalizer_eq]
    exact conjSubgroup_eq_self_iff.mp hV
  have hPh : conjSubgroup h₀ (Pc M V) = Pc M V :=
    conjSubgroup_eq_self_iff.mpr (h.toHyp.le_normalizer_Pc hhM)
  apply hnM
  rw [hH, hPh, sup_idem]
  exact h.toHyp.Pc_le_M

theorem inf_conj_Pc_eq_bot (h : RootHyp M V) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M) :
    V ⊓ conjSubgroup h₀ (Pc M V) = ⊥ := by
  by_contra hne
  exact conjSubgroup_ne_self h hH hnM (conj_eq_of_inf_conj_Pc_ne_bot h hne)

theorem conjSubgroup_inf_Pc_eq_bot (h : RootHyp M V) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M) :
    conjSubgroup h₀ V ⊓ Pc M V = ⊥ := by
  by_contra hne
  have hne' : V ⊓ conjSubgroup h₀⁻¹ (Pc M V) ≠ ⊥ := by
    intro hbot
    apply hne
    have h := congrArg (conjSubgroup h₀) hbot
    rw [conjSubgroup_inf, conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at h
    rw [h, conjSubgroup_eq_bot_iff.mpr rfl]
  have hV := conj_eq_of_inf_conj_Pc_ne_bot h (g := h₀⁻¹) hne'
  apply conjSubgroup_ne_self h hH hnM
  have h1 : conjSubgroup h₀ (conjSubgroup h₀⁻¹ V) = conjSubgroup h₀ V := by rw [hV]
  rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at h1
  exact h1.symm

private def kPart (P K : Subgroup G) : Subgroup G :=
  inSubgroup frattini (P ⊓ K)

theorem isPGroup_kOf_of_factorization (h : RootHyp M V) {h₀ : G}
    (hK : KFactorization M V H h₀) :
    IsPGroup 2 (kOf V H) := by
  have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  have hP2h : IsPGroup 2 (conjSubgroup h₀ (Pc M V)) :=
    hP2.map (MulAut.conj h₀).toMonoidHom
  have hA2 : IsPGroup 2 ↥(Pc M V ⊓ kOf V H) :=
    hP2.to_le (inf_le_left : Pc M V ⊓ kOf V H ≤ Pc M V)
  have hB2 : IsPGroup 2 ↥(conjSubgroup h₀ (Pc M V) ⊓ kOf V H) :=
    hP2h.to_le (inf_le_left : conjSubgroup h₀ (Pc M V) ⊓ kOf V H ≤ conjSubgroup h₀ (Pc M V))
  have hnorm : conjSubgroup h₀ (Pc M V) ⊓ kOf V H ≤
      Subgroup.normalizer ((Pc M V ⊓ kOf V H : Subgroup G) : Set G) := by
    refine Subgroup.le_normalizer_iff_commutator_le_right.mpr ?_
    refine Subgroup.commutator_le.mpr ?_
    intro b hb a ha
    have hbK : b ∈ kOf V H :=
      (inf_le_right : conjSubgroup h₀ (Pc M V) ⊓ kOf V H ≤ kOf V H) hb
    have hbNP : b ∈ Subgroup.normalizer (Pc M V : Set G) :=
      h.toHyp.le_normalizer_Pc (kOf_le_M h hbK)
    have hbaP : b * a * b⁻¹ ∈ Pc M V :=
      (Subgroup.mem_normalizer_iff.mp hbNP a).mp
        ((inf_le_left : Pc M V ⊓ kOf V H ≤ Pc M V) ha)
    have haK : a ∈ kOf V H :=
      (inf_le_right : Pc M V ⊓ kOf V H ≤ kOf V H) ha
    have hbaK : b * a * b⁻¹ ∈ kOf V H :=
      (kOf V H).mul_mem ((kOf V H).mul_mem hbK haK) ((kOf V H).inv_mem hbK)
    change b * a * b⁻¹ * a⁻¹ ∈ Pc M V ⊓ kOf V H
    exact Subgroup.mem_inf.mpr
      ⟨(Pc M V).mul_mem hbaP ((Pc M V).inv_mem ((inf_le_left : Pc M V ⊓ kOf V H ≤
        Pc M V) ha)), (kOf V H).mul_mem hbaK ((kOf V H).inv_mem haK)⟩
  rw [hK]
  exact IsPGroup.to_sup_of_normal_left' hA2 hB2 hnorm

private theorem exists_mul_of_mem_sup_of_le {K S T : Subgroup G}
    (hcomm : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) (hST : S ⊔ T ≤ K) {x : G}
    (hx : x ∈ S ⊔ T) : ∃ a ∈ S, ∃ b ∈ T, a * b = x := by
  haveI : IsMulCommutative ↥K := ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩
  letI : CommGroup ↥K := IsMulCommutative.instCommGroup
  have hS : S ≤ K := le_sup_left.trans hST
  have hT : T ≤ K := le_sup_right.trans hST
  have hxK : x ∈ K := hST hx
  have hmem : (⟨x, hxK⟩ : ↥K) ∈ S.subgroupOf K ⊔ T.subgroupOf K := by
    rw [← Subgroup.subgroupOf_sup hS hT]
    exact Subgroup.mem_subgroupOf.mpr hx
  obtain ⟨a, ha, b, hb, hab⟩ :=
    (Subgroup.mem_sup (s := S.subgroupOf K) (t := T.subgroupOf K)).mp hmem
  exact ⟨(a : G), Subgroup.mem_subgroupOf.mp ha, (b : G), Subgroup.mem_subgroupOf.mp hb,
    congrArg Subtype.val hab⟩

private theorem frattini_kOf_eq_sup (h : RootHyp M V) {h₀ : G}
    (hK : KFactorization M V H h₀)
    (hab : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x) :
    inSubgroup frattini (kOf V H) =
      kPart (Pc M V) (kOf V H) ⊔ kPart (conjSubgroup h₀ (Pc M V)) (kOf V H) := by
  have hK2 : IsPGroup 2 (kOf V H) := isPGroup_kOf_of_factorization h hK
  have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  have hP2h : IsPGroup 2 (conjSubgroup h₀ (Pc M V)) :=
    hP2.map (MulAut.conj h₀).toMonoidHom
  have hA2 : IsPGroup 2 ↥(Pc M V ⊓ kOf V H) :=
    hP2.to_le (inf_le_left : Pc M V ⊓ kOf V H ≤ Pc M V)
  have hB2 : IsPGroup 2 ↥(conjSubgroup h₀ (Pc M V) ⊓ kOf V H) :=
    hP2h.to_le (inf_le_left : conjSubgroup h₀ (Pc M V) ⊓ kOf V H ≤ conjSubgroup h₀ (Pc M V))
  have hcommK : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x := hab
  haveI : IsMulCommutative ↥(kOf V H) :=
    ⟨⟨fun x y => Subtype.ext (hab x x.2 y y.2)⟩⟩
  letI : CommGroup ↥(kOf V H) := IsMulCommutative.instCommGroup
  have hST : (Pc M V ⊓ kOf V H) ⊔ (conjSubgroup h₀ (Pc M V) ⊓ kOf V H) ≤ kOf V H := by
    rw [← hK]
  have hPhi_le : inSubgroup frattini (kOf V H) ≤
      kPart (Pc M V) (kOf V H) ⊔ kPart (conjSubgroup h₀ (Pc M V)) (kOf V H) := by
    refine inSubgroup_frattini_le_of_sq hK2 ?_ ?_
    · intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ :=
        exists_mul_of_mem_sup_of_le (K := kOf V H) hcommK hST (by rw [← hK]; exact hx)
      have haK : a ∈ kOf V H := (inf_le_right : Pc M V ⊓ kOf V H ≤ kOf V H) ha
      have hbK : b ∈ kOf V H :=
        (inf_le_right : conjSubgroup h₀ (Pc M V) ⊓ kOf V H ≤ kOf V H) hb
      have hsq : (a * b) ^ 2 = a ^ 2 * b ^ 2 :=
        congrArg Subtype.val (mul_pow (⟨a, haK⟩ : ↥(kOf V H)) ⟨b, hbK⟩ 2)
      rw [hsq]
      exact Subgroup.mul_mem _
        (Subgroup.mem_sup_left (sq_mem_inSubgroup_frattini hA2 ha))
        (Subgroup.mem_sup_right (sq_mem_inSubgroup_frattini hB2 hb))
    · intro x hx y hy
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hab x hx y hy)]
      exact Subgroup.one_mem _
  have hA_le : kPart (Pc M V) (kOf V H) ≤ inSubgroup frattini (kOf V H) :=
    inSubgroup_frattini_mono hK2 (inf_le_right : Pc M V ⊓ kOf V H ≤ kOf V H)
  have hB_le : kPart (conjSubgroup h₀ (Pc M V)) (kOf V H) ≤
      inSubgroup frattini (kOf V H) :=
    inSubgroup_frattini_mono hK2
      (inf_le_right : conjSubgroup h₀ (Pc M V) ⊓ kOf V H ≤ kOf V H)
  exact le_antisymm hPhi_le (sup_le hA_le hB_le)

private theorem kPart_le_V (h : RootHyp M V) :
    kPart (Pc M V) (kOf V H) ≤ V := by
  have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  exact (inSubgroup_frattini_mono hP2
    (inf_le_left : Pc M V ⊓ kOf V H ≤ Pc M V)).trans h.toHyp.frattini_Pc_le

private theorem kPart_conj_le (h : RootHyp M V) {h₀ : G}
    (hab : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x) :
    kPart (conjSubgroup h₀ (Pc M V)) (kOf V H) ≤ conjSubgroup h₀ V := by
  have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  have hP2h : IsPGroup 2 (conjSubgroup h₀ (Pc M V)) :=
    hP2.map (MulAut.conj h₀).toMonoidHom
  have hB2 : IsPGroup 2 ↥(conjSubgroup h₀ (Pc M V) ⊓ kOf V H) :=
    hP2h.to_le (inf_le_left : conjSubgroup h₀ (Pc M V) ⊓ kOf V H ≤ conjSubgroup h₀ (Pc M V))
  refine inSubgroup_frattini_le_of_sq hB2 ?_ ?_
  · intro x hx
    refine mem_conjSubgroup.mpr ?_
    have hxP : h₀⁻¹ * x * h₀ ∈ Pc M V :=
      mem_conjSubgroup.mp ((inf_le_left : conjSubgroup h₀ (Pc M V) ⊓ kOf V H ≤
        conjSubgroup h₀ (Pc M V)) hx)
    rw [show h₀⁻¹ * x ^ 2 * h₀ = (h₀⁻¹ * x * h₀) ^ 2 by rw [pow_two, pow_two]; group]
    exact h.toHyp.frattini_Pc_le (sq_mem_inSubgroup_frattini hP2 hxP)
  · intro x hx y hy
    rw [commutatorElement_eq_one_iff_mul_comm.mpr
      (hab x ((inf_le_right : conjSubgroup h₀ (Pc M V) ⊓ kOf V H ≤ kOf V H) hx)
        y ((inf_le_right : conjSubgroup h₀ (Pc M V) ⊓ kOf V H ≤ kOf V H) hy))]
    exact Subgroup.one_mem _

private theorem kPart_conj_inf_Pc_eq_bot (h : RootHyp M V) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hab : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x) :
    kPart (conjSubgroup h₀ (Pc M V)) (kOf V H) ⊓ Pc M V = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx1 : x ∈ conjSubgroup h₀ V :=
    kPart_conj_le h hab ((inf_le_left : kPart (conjSubgroup h₀ (Pc M V)) (kOf V H) ⊓ Pc M V ≤
      kPart (conjSubgroup h₀ (Pc M V)) (kOf V H)) hx)
  have hx2 : x ∈ Pc M V :=
    (inf_le_right : kPart (conjSubgroup h₀ (Pc M V)) (kOf V H) ⊓ Pc M V ≤ Pc M V) hx
  have hmem : x ∈ conjSubgroup h₀ V ⊓ Pc M V := Subgroup.mem_inf.mpr ⟨hx1, hx2⟩
  rwa [conjSubgroup_inf_Pc_eq_bot h hH hnM] at hmem

private theorem sup_inf_Pc_le (h : RootHyp M V) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hab : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x) :
    (kPart (Pc M V) (kOf V H) ⊔ kPart (conjSubgroup h₀ (Pc M V)) (kOf V H)) ⊓ Pc M V ≤
      kPart (Pc M V) (kOf V H) := by
  haveI : IsMulCommutative ↥(kOf V H) :=
    ⟨⟨fun x y => Subtype.ext (hab x x.2 y y.2)⟩⟩
  letI : CommGroup ↥(kOf V H) := IsMulCommutative.instCommGroup
  have hA_le_K : kPart (Pc M V) (kOf V H) ≤ kOf V H :=
    (Subgroup.map_subtype_le (frattini ↥(Pc M V ⊓ kOf V H))).trans inf_le_right
  have hB_le_K : kPart (conjSubgroup h₀ (Pc M V)) (kOf V H) ≤ kOf V H :=
    (Subgroup.map_subtype_le (frattini ↥(conjSubgroup h₀ (Pc M V) ⊓ kOf V H))).trans inf_le_right
  intro x hx
  obtain ⟨hxAB, hxP⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    exists_mul_of_mem_sup_of_le (K := kOf V H) hab (sup_le hA_le_K hB_le_K) hxAB
  have haP : a ∈ Pc M V := h.toHyp.le_Pc (kPart_le_V h ha)
  have hbP : b ∈ Pc M V := by
    have hmem : a⁻¹ * (a * b) ∈ Pc M V :=
      (Pc M V).mul_mem ((Pc M V).inv_mem haP) hxP
    simpa using hmem
  have hbBot : b = 1 := by
    have hmem : b ∈ kPart (conjSubgroup h₀ (Pc M V)) (kOf V H) ⊓ Pc M V :=
      Subgroup.mem_inf.mpr ⟨hb, hbP⟩
    rw [kPart_conj_inf_Pc_eq_bot h hH hnM hab] at hmem
    exact Subgroup.mem_bot.mp hmem
  simpa [hbBot] using ha

private theorem commutator_kPart_conj_le_V (h : RootHyp M V) (hPH : Pc M V ≤ H)
    {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hab : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x) :
    ⁅Pc M V, kPart (conjSubgroup h₀ (Pc M V)) (kOf V H)⁆ ≤ V := by
  have hB_le_Phi : kPart (conjSubgroup h₀ (Pc M V)) (kOf V H) ≤
      inSubgroup frattini (kOf V H) := by
    rw [frattini_kOf_eq_sup h hK hab]
    exact le_sup_right
  have hPhi_normal : H ≤ Subgroup.normalizer (inSubgroup frattini (kOf V H) : Set G) :=
    fun g hg => mem_normalizer_inSubgroup_frattini (le_normalizer_kOf V H hg)
  have h1 : ⁅Pc M V, kPart (conjSubgroup h₀ (Pc M V)) (kOf V H)⁆ ≤
      inSubgroup frattini (kOf V H) := by
    have hPnorm : Pc M V ≤ Subgroup.normalizer (inSubgroup frattini (kOf V H) : Set G) :=
      hPH.trans hPhi_normal
    have hcomm := Subgroup.le_normalizer_iff_commutator_le_left.mp hPnorm
    rw [Subgroup.commutator_comm] at hcomm
    exact (Subgroup.commutator_mono le_rfl hB_le_Phi).trans hcomm
  have h2 : ⁅Pc M V, kPart (conjSubgroup h₀ (Pc M V)) (kOf V H)⁆ ≤ Pc M V := by
    have hB_le_M : kPart (conjSubgroup h₀ (Pc M V)) (kOf V H) ≤ M :=
      (Subgroup.map_subtype_le
        (frattini ↥(conjSubgroup h₀ (Pc M V) ⊓ kOf V H))).trans
        (inf_le_right.trans (kOf_le_M h))
    have hBnorm : kPart (conjSubgroup h₀ (Pc M V)) (kOf V H) ≤
        Subgroup.normalizer (Pc M V : Set G) :=
      hB_le_M.trans h.toHyp.le_normalizer_Pc
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp hBnorm
  have h3 : ⁅Pc M V, kPart (conjSubgroup h₀ (Pc M V)) (kOf V H)⁆ ≤
      kPart (Pc M V) (kOf V H) := by
    refine (le_inf h1 h2).trans ?_
    rw [frattini_kOf_eq_sup h hK hab]
    exact sup_inf_Pc_le h hH hnM hab
  exact h3.trans (kPart_le_V h)

private theorem kPart_conj_eq_bot (h : RootHyp M V) (hPH : Pc M V ≤ H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hab : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x) :
    kPart (conjSubgroup h₀ (Pc M V)) (kOf V H) = ⊥ := by
  have hB_le_M : kPart (conjSubgroup h₀ (Pc M V)) (kOf V H) ≤ M :=
    (Subgroup.map_subtype_le
      (frattini ↥(conjSubgroup h₀ (Pc M V) ⊓ kOf V H))).trans
      (inf_le_right.trans (kOf_le_M h))
  have hB_le_CV : kPart (conjSubgroup h₀ (Pc M V)) (kOf V H) ≤
      Subgroup.centralizer (V : Set G) :=
    (Subgroup.map_subtype_le
      (frattini ↥(conjSubgroup h₀ (Pc M V) ⊓ kOf V H))).trans
      (inf_le_right.trans (kOf_le_centralizer_V V H))
  have hB_le_Q : kPart (conjSubgroup h₀ (Pc M V)) (kOf V H) ≤
      inSubgroup (pCore 2) M :=
    h.toHyp.le_pCore_of_commutator_le hB_le_M hB_le_CV
      (commutator_kPart_conj_le_V h hPH hH hnM hK hab)
  have hB_le_P : kPart (conjSubgroup h₀ (Pc M V)) (kOf V H) ≤ Pc M V :=
    le_inf hB_le_Q hB_le_CV
  rw [eq_bot_iff]
  intro x hx
  have hmem : x ∈ kPart (conjSubgroup h₀ (Pc M V)) (kOf V H) ⊓ Pc M V :=
    Subgroup.mem_inf.mpr ⟨hx, hB_le_P hx⟩
  rwa [kPart_conj_inf_Pc_eq_bot h hH hnM hab] at hmem

private theorem frattini_kOf_eq_bot (h : RootHyp M V) (hPH : Pc M V ≤ H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hab : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x) :
    inSubgroup frattini (kOf V H) = ⊥ := by
  have hBbot := kPart_conj_eq_bot h hPH hH hnM hK hab
  have hPhi_le_V : inSubgroup frattini (kOf V H) ≤ V := by
    rw [frattini_kOf_eq_sup h hK hab, hBbot, sup_bot_eq]
    exact kPart_le_V h
  have hPhi_normal : H ≤ Subgroup.normalizer (inSubgroup frattini (kOf V H) : Set G) :=
    fun g hg => mem_normalizer_inSubgroup_frattini (le_normalizer_kOf V H hg)
  obtain ⟨x, hxH, hxM⟩ := SetLike.not_le_iff_exists.mp hnM
  have hTI : V ⊓ conjSubgroup x V = ⊥ := by
    rcases h.toHyp.ti x with hbot | heq
    · exact hbot
    · exfalso
      have hne : V ⊓ conjSubgroup x V ≠ ⊥ := by rw [heq]; exact h.toHyp.ne_bot
      have hxN : x ∈ Subgroup.normalizer (V : Set G) :=
        conjSubgroup_eq_self_iff.mp (conjSubgroup_eq_of_isTI h.toHyp.ti hne)
      exact hxM (h.toHyp.normalizer_eq ▸ hxN)
  have hPhi_le_conj : inSubgroup frattini (kOf V H) ≤ conjSubgroup x V := by
    have hxN : x ∈ Subgroup.normalizer (inSubgroup frattini (kOf V H) : Set G) := hPhi_normal hxH
    have heq : conjSubgroup x (inSubgroup frattini (kOf V H)) = inSubgroup frattini (kOf V H) :=
      conjSubgroup_eq_self_iff.mpr hxN
    calc inSubgroup frattini (kOf V H)
        = conjSubgroup x (inSubgroup frattini (kOf V H)) := heq.symm
      _ ≤ conjSubgroup x V := Subgroup.map_mono hPhi_le_V
  rw [eq_bot_iff]
  intro y hy
  have hmem : y ∈ V ⊓ conjSubgroup x V :=
    Subgroup.mem_inf.mpr ⟨hPhi_le_V hy, hPhi_le_conj hy⟩
  rwa [hTI] at hmem

theorem isElemAbelian_kOf (h : RootHyp M V) (hPH : Pc M V ≤ H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hab : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x) :
    Assembly.IsElemAbelian 2 (kOf V H) := by
  have hK2 : IsPGroup 2 (kOf V H) := isPGroup_kOf_of_factorization h hK
  have hPhi_bot := frattini_kOf_eq_bot h hPH hH hnM hK hab
  refine ⟨⟨⟨fun a b => Subtype.ext (hab a a.2 b b.2)⟩⟩, ?_⟩
  intro x hx
  have hx2 : x ^ 2 ∈ inSubgroup frattini (kOf V H) := sq_mem_inSubgroup_frattini hK2 hx
  rw [hPhi_bot] at hx2
  exact Subgroup.mem_bot.mp hx2

theorem lt_Pc_inf_kOf (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀) :
    V < Pc M V ⊓ kOf V H := by
  have hV_le : V ≤ Pc M V ⊓ kOf V H := le_inf h.toHyp.le_Pc (le_kOf h hPH hVH)
  refine lt_of_le_of_ne hV_le ?_
  intro heq
  have hPK : Pc M V ⊓ kOf V H = V := heq.symm
  have hB0_le_P : conjSubgroup h₀ (Pc M V) ⊓ kOf V H ≤ Pc M V := by
    have hB0_le_M : conjSubgroup h₀ (Pc M V) ⊓ kOf V H ≤ M :=
      inf_le_right.trans (kOf_le_M h)
    have hB0_le_CV : conjSubgroup h₀ (Pc M V) ⊓ kOf V H ≤
        Subgroup.centralizer (V : Set G) :=
      inf_le_right.trans (kOf_le_centralizer_V V H)
    have hB0_commP : ⁅Pc M V, conjSubgroup h₀ (Pc M V) ⊓ kOf V H⁆ ≤ V := by
      have h1 : ⁅Pc M V, conjSubgroup h₀ (Pc M V) ⊓ kOf V H⁆ ≤ Pc M V := by
        have hB0norm : conjSubgroup h₀ (Pc M V) ⊓ kOf V H ≤
            Subgroup.normalizer (Pc M V : Set G) :=
          (inf_le_right.trans (kOf_le_M h) : conjSubgroup h₀ (Pc M V) ⊓ kOf V H ≤ M).trans
            h.toHyp.le_normalizer_Pc
        rw [Subgroup.commutator_comm]
        exact Subgroup.le_normalizer_iff_commutator_le_right.mp hB0norm
      have h2 : ⁅Pc M V, conjSubgroup h₀ (Pc M V) ⊓ kOf V H⁆ ≤ kOf V H := by
        have hPnorm : Pc M V ≤ Subgroup.normalizer (kOf V H : Set G) :=
          hPH.trans (le_normalizer_kOf V H)
        have h := Subgroup.le_normalizer_iff_commutator_le_left.mp hPnorm
        rw [Subgroup.commutator_comm] at h
        exact (Subgroup.commutator_mono (le_refl (Pc M V)) inf_le_right).trans h
      have h3 := le_inf h1 h2
      rwa [hPK] at h3
    have hB0_le_Q := h.toHyp.le_pCore_of_commutator_le hB0_le_M hB0_le_CV hB0_commP
    exact le_inf hB0_le_Q hB0_le_CV
  have hK_le_P : kOf V H ≤ Pc M V := by
    rw [hK]
    exact sup_le inf_le_left hB0_le_P
  have hK_eq_V : kOf V H = V := by
    rw [inf_eq_right.mpr hK_le_P] at hPK
    exact hPK
  apply hnM
  intro x hx
  have hxN : x ∈ Subgroup.normalizer (kOf V H : Set G) := le_normalizer_kOf V H hx
  rw [hK_eq_V, h.toHyp.normalizer_eq] at hxN
  exact hxN

end RootHyp

end CFSG.RankThree.GF2n.Tim81
