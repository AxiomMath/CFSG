module

public import CFSG.RankThree.GF2n.Tim77.Assembly
public import CFSG.RankThree.GF2n.Tim77.QuotPipe
public import CFSG.RankThree.GF2n.Tim77.Sec41Gen
public import CFSG.RankThree.GF2n.Tim77.Sec32d
public import CFSG.RankThree.GF2n.Tim77Prop24TwoD

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

abbrev sec415N (A Abar : Subgroup G) : Subgroup ↥(Subgroup.normalClosure (A : Set G)) :=
  (Sec415N0 A Abar).subgroupOf (Subgroup.normalClosure (A : Set G))

abbrev sec415D (A Abar : Subgroup G) : Set ↥(Subgroup.normalClosure (A : Set G)) :=
  {t | (t : G) ∈ Sec415E A Abar}

theorem sec415_memE_iff {A Abar : Subgroup G} {t : G} :
    t ∈ Sec415E A Abar ↔ ∃ g : G, ∃ a ∈ A, a ∉ Section3.A0 A Abar ∧ t = g * a * g⁻¹ :=
  Iff.rfl

theorem sec415_memE_top {A Abar : Subgroup G} {t : G} :
    t ∈ Sec415E A Abar ↔ t ∈ sec41g_D (⊤ : Subgroup G) A (Section3.A0 A Abar) := by
  rw [sec41g_mem_D]
  constructor
  · intro ht
    obtain ⟨g, a, ha, ha0, rfl⟩ := sec415_memE_iff.mp ht
    exact ⟨g, Subgroup.mem_top _, a, ha, ha0, rfl⟩
  · rintro ⟨g, -, a, ha, ha0, rfl⟩
    exact sec415_memE_iff.mpr ⟨g, a, ha, ha0, rfl⟩

theorem sec415_conj_mem {A Abar : Subgroup G} {g t : G} (ht : t ∈ Sec415E A Abar) :
    g * t * g⁻¹ ∈ Sec415E A Abar := by
  obtain ⟨h, a, ha, ha0, rfl⟩ := sec415_memE_iff.mp ht
  exact sec415_memE_iff.mpr ⟨g * h, a, ha, ha0, by group⟩

theorem sec415_mem_of_mem_A {A Abar : Subgroup G} {b : G} (hb : b ∈ A)
    (hb0 : b ∉ Section3.A0 A Abar) : b ∈ Sec415E A Abar :=
  sec415_memE_iff.mpr ⟨1, b, hb, hb0, by simp⟩

theorem sec415_mem_normalClosure {A Abar : Subgroup G} {t : G} (ht : t ∈ Sec415E A Abar) :
    t ∈ Subgroup.normalClosure (A : Set G) := by
  obtain ⟨g, a, ha, -, rfl⟩ := sec415_memE_iff.mp ht
  exact Subgroup.Normal.conj_mem inferInstance a (Subgroup.subset_normalClosure ha) g

theorem sec415_conjSubgroup_le {K N : Subgroup G} [N.Normal] (hK : K ≤ N) (g : G) :
    conjSubgroup g K ≤ N := by
  intro x hx
  rw [mem_conjSubgroup] at hx
  have h := Subgroup.Normal.conj_mem inferInstance _ (hK hx) g
  rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h

theorem sec415_elemAbelian_subgroupOf {H K : Subgroup G} (hH : IsElemAbelian 2 H) :
    IsElemAbelian 2 (H.subgroupOf K) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
  · simp only [Subgroup.coe_mul]
    exact sec32d_comm_of_isElemAbelian hH (Subgroup.mem_subgroupOf.mp a.2)
      (Subgroup.mem_subgroupOf.mp b.2)
  · simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact hH.2 _ (Subgroup.mem_subgroupOf.mp hx)

theorem sec415_normalClosure_le_closure [Finite G] {A Abar S₀ B : Subgroup G}
    (h : Sec3Ctx A Abar S₀ B) :
    Subgroup.normalClosure (A : Set G) ≤ Subgroup.closure (Sec415E A Abar) := by
  have hnorm : (Subgroup.closure (Sec415E A Abar)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    induction hn using Subgroup.closure_induction with
    | mem x hx => exact Subgroup.subset_closure (sec415_conj_mem hx)
    | one => simp
    | mul x y _ _ hx hy =>
      rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group]
      exact mul_mem hx hy
    | inv x _ hx =>
      rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
      exact inv_mem hx
  haveI := hnorm
  have hA0A : Section3.A0 A Abar ≤ A := by
    rw [h.a0_eq]
    exact inf_le_left
  refine Subgroup.normalClosure_le_normal ?_
  intro a ha
  by_cases ha0 : a ∈ Section3.A0 A Abar
  · obtain ⟨a₁, ha₁A, ha₁0⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hA0A h.a0_ne)
    have e : a = a₁⁻¹ * (a₁ * a) := by group
    rw [e]
    have h1 : a₁⁻¹ ∈ Sec415E A Abar := by
      refine sec415_mem_of_mem_A (inv_mem ha₁A) fun hi => ha₁0 ?_
      simpa using inv_mem hi
    have h2 : a₁ * a ∈ Sec415E A Abar := by
      refine sec415_mem_of_mem_A (mul_mem ha₁A ha) fun hi => ha₁0 ?_
      simpa using mul_mem hi (inv_mem ha0)
    exact mul_mem (Subgroup.subset_closure h1) (Subgroup.subset_closure h2)
  · exact Subgroup.subset_closure (sec415_mem_of_mem_A ha ha0)

theorem sec415_gen [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B)
    (y : ↥(Subgroup.normalClosure (A : Set G))) :
    y ∈ Subgroup.closure (sec415D A Abar ∪ (sec415N A Abar : Set ↥(Subgroup.normalClosure
      (A : Set G)))) := by
  have hE : Subgroup.closure (Sec415E A Abar) ≤
      (Subgroup.closure (sec415D A Abar ∪ (sec415N A Abar : Set ↥(Subgroup.normalClosure
        (A : Set G))))).map (Subgroup.normalClosure (A : Set G)).subtype := by
    rw [Subgroup.closure_le]
    intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, sec415_mem_normalClosure hx⟩,
      Subgroup.subset_closure (Or.inl hx), rfl⟩
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp (hE (sec415_normalClosure_le_closure h y.2))
  have hzy' : z = y := Subtype.ext hzy
  rw [← hzy']
  exact hz

theorem sec415_sec42 [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B)
    [(Sec415N0 A Abar).Normal] (hN0el : IsElemAbelian 2 (Sec415N0 A Abar))
    (hinf : A ⊓ Sec415N0 A Abar = Section3.A0 A Abar)
    (hcls : ∃ e₀ ∈ Sec415E A Abar, ∀ e ∈ Sec415E A Abar,
      ∃ y ∈ Subgroup.normalClosure (A : Set G), e = y * e₀ * y⁻¹)
    (hO2 : ⁅pCore 2 ↥(Subgroup.normalClosure (A : Set G)), ⊤⁆ ≤ sec415N A Abar) :
    Sec42Data ↥(Subgroup.normalClosure (A : Set G)) (sec415N A Abar) (sec415D A Abar) := by
  have hA : IsElemAbelian 2 A := h.hyp.elemAbelian
  have hAW : A ≤ Subgroup.normalClosure (A : Set G) := Subgroup.le_normalClosure
  have hAN : ∀ y ∈ (⊤ : Subgroup G), conjSubgroup y (Section3.A0 A Abar) ≤ Sec415N0 A Abar :=
    fun y _ => le_iSup (fun g : G => conjSubgroup g (Section3.A0 A Abar)) y
  have hNc : ∀ x ∈ Sec415N0 A Abar, ∀ w ∈ Sec415N0 A Abar, x * w = w * x :=
    fun x hx w hw => sec32d_comm_of_isElemAbelian hN0el hx hw
  refine
    { sq := fun n hn => (sec415_elemAbelian_subgroupOf hN0el).2 n hn
      disj := ?_
      invol := ?_
      ord := ?_
      conjD := ?_
      gen := fun y => sec415_gen h y
      cent := ?_
      single := ?_
      O2 := fun z hz g => hO2 (Subgroup.commutator_mem_commutator hz (Subgroup.mem_top g)) }
  ·
    intro t ht htN
    have ht' : (t : G) ∈ Sec415E A Abar := ht
    obtain ⟨g, a, ha, ha0, hta⟩ := sec415_memE_iff.mp ht'
    have htN0 : (t : G) ∈ Sec415N0 A Abar := Subgroup.mem_subgroupOf.mp htN
    have h1 := Subgroup.Normal.conj_mem inferInstance (t : G) htN0 g⁻¹
    have e : g⁻¹ * (t : G) * g⁻¹⁻¹ = a := by
      rw [hta]
      group
    rw [e] at h1
    have hmem : a ∈ A ⊓ Sec415N0 A Abar := Subgroup.mem_inf.mpr ⟨ha, h1⟩
    rw [hinf] at hmem
    exact ha0 hmem
  ·
    intro t ht
    have ht' : (t : G) ∈ Sec415E A Abar := ht
    obtain ⟨g, a, ha, -, hta⟩ := sec415_memE_iff.mp ht'
    apply Subtype.ext
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [hta, sq]
    exact sec41g_conj_sq (sec41g_invol hA ha)
  ·
    intro t ht t' ht'
    have ht1 : (t : G) ∈ Sec415E A Abar := ht
    have ht2 : (t' : G) ∈ Sec415E A Abar := ht'
    have e : orderOf (t * t') = orderOf ((t : G) * (t' : G)) := by
      rw [← Subgroup.coe_mul, Subgroup.orderOf_coe]
    rw [e]
    rcases sec41g_order h hAN hNc (sec415_memE_top.mp ht1) (sec415_memE_top.mp ht2) with h2 | ho
    · exact Or.inl (dvd_of_eq h2)
    · exact Or.inr ho
  ·
    intro g t ht
    have ht1 : (t : G) ∈ Sec415E A Abar := ht
    have e : ((g * t * g⁻¹ : ↥(Subgroup.normalClosure (A : Set G))) : G) =
        (g : G) * (t : G) * (g : G)⁻¹ := by
      simp
    show ((g * t * g⁻¹ : ↥(Subgroup.normalClosure (A : Set G))) : G) ∈ Sec415E A Abar
    rw [e]
    exact sec415_conj_mem ht1
  ·
    intro t ht x hx y hy hxt hyt
    have ht1 : (t : G) ∈ Sec415E A Abar := ht
    have hx1 : (x : G) ∈ Sec415E A Abar := hx
    have hy1 : (y : G) ∈ Sec415E A Abar := hy
    have hxt' : (x : G) * (t : G) = (t : G) * (x : G) := congrArg Subtype.val hxt.eq
    have hyt' : (y : G) * (t : G) = (t : G) * (y : G) := congrArg Subtype.val hyt.eq
    have hc := sec41g_comm_gen h hAN hNc (sec415_memE_top.mp ht1) (sec415_memE_top.mp hx1) hxt'
      (sec415_memE_top.mp hy1) hyt'
    show x * y = y * x
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact hc
  ·
    obtain ⟨e₀, he₀, hcl⟩ := hcls
    have he₀W : e₀ ∈ Subgroup.normalClosure (A : Set G) := sec415_mem_normalClosure he₀
    refine ⟨⟨e₀, he₀W⟩, he₀, fun d hd => ?_⟩
    have hd1 : (d : G) ∈ Sec415E A Abar := hd
    obtain ⟨y, hy, hdy⟩ := hcl (d : G) hd1
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hdy

theorem sec415_not_solvable {A Abar : Subgroup G} {b : G} [(Sec415N0 A Abar).Normal]
    (hN0el : IsElemAbelian 2 (Sec415N0 A Abar))
    (hKW : A ⊔ Abar ⊔ conjSubgroup b Abar ≤ Subgroup.normalClosure (A : Set G))
    (hK : ¬ Group.IsSolvable ↥(A ⊔ Abar ⊔ conjSubgroup b Abar)) :
    ¬ Group.IsSolvable (↥(Subgroup.normalClosure (A : Set G)) ⧸ sec415N A Abar) := by
  intro hsol
  apply hK
  haveI : IsMulCommutative ↥(sec415N A Abar) := (sec415_elemAbelian_subgroupOf hN0el).1
  haveI hWs : Group.IsSolvable ↥(Subgroup.normalClosure (A : Set G)) :=
    (Group.isSolvable_iff_subgroup_quotient (sec415N A Abar)).mpr ⟨inferInstance, hsol⟩
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.subgroupOfEquivOfLe hKW).symm.toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hKW).symm.injective

theorem sec415_of
    (h415a : Tim77Sec415aStatement) (h415b : Tim77Sec415bStatement)
    (h415c : Tim77Sec415cStatement) (h43 : Tim77Sec43Statement) (h44 : Tim77Sec44Statement)
    (h35 : Tim77Sec35Statement) : Tim77Sec415Statement := by
  unfold Tim77Sec415Statement
  intro G _ _ A Abar S₀ B hctx hq hH
  obtain ⟨hN0n, hN0el, hinf, -⟩ := h415a G A Abar S₀ B hctx hq hH
  obtain ⟨hcls, -, -, -⟩ := h415b G A Abar S₀ B hctx hq hH
  have hO2 : ⁅pCore 2 ↥(Subgroup.normalClosure (A : Set G)), ⊤⁆ ≤ sec415N A Abar :=
    h415c G A Abar S₀ B hctx hq hH
  haveI := hN0n
  have hAW : A ≤ Subgroup.normalClosure (A : Set G) := Subgroup.le_normalClosure
  obtain ⟨g₀, hg₀⟩ := hctx.exists_abar_eq
  have hAbarW : Abar ≤ Subgroup.normalClosure (A : Set G) := by
    rw [hg₀]
    exact sec415_conjSubgroup_le hAW g₀
  obtain ⟨b, -, -, hK⟩ := sec45_of h43 h44 h35 hctx hq
  have hKW : A ⊔ Abar ⊔ conjSubgroup b Abar ≤ Subgroup.normalClosure (A : Set G) :=
    sup_le (sup_le hAW hAbarW) (sec415_conjSubgroup_le hAbarW b)
  have hns := sec415_not_solvable hN0el hKW hK
  obtain ⟨-, hBen⟩ := qp_main (sec415_sec42 hctx hN0el hinf hcls hO2) hns
  have hA0A : Section3.A0 A Abar ≤ A := by
    rw [hctx.a0_eq]
    exact inf_le_left
  have hrel : (Section3.A0 A Abar).relIndex A = 2 := by
    rw [← hctx.setup.relIndex_Lb]
    exact hq
  have hcard : Nat.card A = 2 * Nat.card (Section3.A0 A Abar) := by
    have h1 := Subgroup.relIndex_mul_card (H := Section3.A0 A Abar) (K := A)
    rw [inf_of_le_left hA0A, hrel] at h1
    exact h1.symm
  have hAN0W : A ⊓ Sec415N0 A Abar ≤ Subgroup.normalClosure (A : Set G) :=
    inf_le_left.trans hAW
  have hNA : A ⊓ Subgroup.map (Subgroup.normalClosure (A : Set G)).subtype (sec415N A Abar) =
      Section3.A0 A Abar := by
    unfold sec415N
    rw [Subgroup.subgroupOf_map_subtype, ← hinf, ← inf_assoc, inf_eq_left.mpr hAN0W]
  unfold Cor2Alt3
  refine ⟨sec415N A Abar, inferInstance, sec415_elemAbelian_subgroupOf hN0el, ?_,
    Subgroup.center _, le_rfl, inferInstance, sec32d_beta_of_bender hBen⟩
  rw [hNA, hcard]

end CFSG.RankThree.GF2n.Tim77
