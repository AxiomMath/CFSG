module

public import CFSG.Timmesfeld.Bridge.Asc72XQuot

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.OddTransp
open scoped commutatorElement

variable {G : Type} [Group G] {D : Set G}

theorem mem_normalizer_map_pCore {z g : G} (hg : g ∈ localGroup D z) :
    g ∈ Subgroup.normalizer
      (((CFSG.pCore 2 (localGroup D z)).map (localGroup D z).subtype : Subgroup G) : Set G) := by
  have hnorm := CFSG.pCore_normal (p := 2) (G := localGroup D z)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨x', hx', rfl⟩
    exact ⟨⟨g, hg⟩ * x' * ⟨g, hg⟩⁻¹, hnorm.conj_mem x' hx' _, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    refine ⟨⟨g, hg⟩⁻¹ * y * ⟨g, hg⟩⁻¹⁻¹, hnorm.conj_mem y hy _, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at hyx ⊢
    rw [hyx]
    group

theorem exists_sylow_localGroup [Finite G] (hD : IsOddTransp D) {z u v d : G}
    (hu : u ∈ centSet D z) (hv : v ∈ centSet D z) (hd : d ∈ centSet D z) (huv : Commute u v)
    (hud : Commute u d) (hvd : Commute v d) :
    ∃ S₀ : Sylow 2 G, u ∈ S₀ ∧ v ∈ S₀ ∧ d ∈ S₀ ∧
      (CFSG.pCore 2 (localGroup D z)).map (localGroup D z).subtype ≤ S₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpair : ({u, v, d} : Set G).Pairwise Commute := by
    have h1 := huv; have h2 := hud; have h3 := hvd
    have h1' := huv.symm; have h2' := hud.symm; have h3' := hvd.symm
    intro s hs t ht _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;>
      first | exact Commute.refl _ | assumption
  have hA : IsPGroup 2 (Subgroup.closure ({u, v, d} : Set G)) := by
    refine isPGroup_closure_of_pairwise hpair ?_
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · exact hD.mul_self_eq_one hu.1
    · exact hD.mul_self_eq_one hv.1
    · exact hD.mul_self_eq_one hd.1
  have hQ : IsPGroup 2 ((CFSG.pCore 2 (localGroup D z)).map (localGroup D z).subtype) :=
    CFSG.pCore_isPGroup.map _
  have hle : Subgroup.closure ({u, v, d} : Set G) ≤ Subgroup.normalizer
      (((CFSG.pCore 2 (localGroup D z)).map (localGroup D z).subtype : Subgroup G) : Set G) := by
    rw [Subgroup.closure_le]
    rintro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · exact mem_normalizer_map_pCore (mem_localGroup_of_mem hu)
    · exact mem_normalizer_map_pCore (mem_localGroup_of_mem hv)
    · exact mem_normalizer_map_pCore (mem_localGroup_of_mem hd)
  obtain ⟨S₀, hS₀⟩ := (IsPGroup.to_sup_of_normal_right' hA hQ hle).exists_le_sylow
  refine ⟨S₀, hS₀ (Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))),
    hS₀ (Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))),
    hS₀ (Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))),
    le_sup_right.trans hS₀⟩

theorem false_of_pCore_not_commute [Finite G] (hS : Setup G D) (hdisc : Disconnected D)
    (hnorm : ∀ K : Subgroup G, K.Normal → K = ⊥ ∨ commutator G ≤ K) (hnsq : ¬ MeetsSq D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (hord : orderOf (u * v * w) = 2 * n) (huw : ¬ Reach D u w) {z : G}
    (hzdef : (u * v * w) ^ n = z) {q : localGroup D z} (hq : q ∈ CFSG.pCore 2 (localGroup D z))
    (hqu : ¬ Commute (q : G) u) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := hS.oddT
  have hN := hS.normal
  have hu := htri.1
  have hv := htri.2.1
  have hw := htri.2.2.1
  have hne := htri.2.2.2.1
  have huv := htri.2.2.2.2.1
  obtain ⟨hzz, hz1, hzu, hzv, hzw, hdD⟩ := htri.third_kind hD hN hn hord
  have hzD : z ∉ D := hzdef ▸ thirdKind_z_not_mem hS htri hn hord huw
  obtain ⟨huC, hvC, hwC, hdC⟩ := thirdKind_mem_centSet hS htri hn hord
  rw [hzdef] at hzz hz1 hzu hzv hzw hdD huC hvC hwC hdC
  set d := u * v * z with hddef
  have hdab : Commute d u ∧ Commute d v :=
    (hD.commute_mul_iff hu hv hdD hne huv).mp ((Commute.refl (u * v)).mul_left (hzu.mul_right hzv))
  obtain ⟨S₀, huS, hvS, hdS, hQS⟩ :=
    exists_sylow_localGroup hD huC hvC hdC huv hdab.1.symm hdab.2.symm
  have hu₀ : u ∈ D ∩ (S₀ : Set G) := ⟨hu, huS⟩
  have hv₀ : v ∈ D ∩ (S₀ : Set G) := ⟨hv, hvS⟩
  have hd₀ : d ∈ D ∩ (S₀ : Set G) := ⟨hdD, hdS⟩
  have hLcomm : ∀ s ∈ D ∩ (S₀ : Set G), ∀ t ∈ D ∩ (S₀ : Set G), Commute s t :=
    fun s hs t ht => hD.commute_of_isPGroup S₀.isPGroup' hs.1 ht.1 hs.2 ht.2
  have hzabd : z = u * v * d := by
    rw [hddef, ← mul_assoc, IsTriangle.uv_mul_self hD htri, one_mul]
  have hLz : ∀ s ∈ D ∩ (S₀ : Set G), Commute s z := fun s hs => by
    rw [hzabd]
    exact ((hLcomm s hs u hu₀).mul_right (hLcomm s hs v hv₀)).mul_right (hLcomm s hs d hd₀)
  have hLx : ∀ s ∈ D ∩ (S₀ : Set G), ¬ Commute s w := fun s hs hsw =>
    huw (reach_trans (reach_of_commute hu hs.1 (hLcomm u hu₀ s hs))
      (reach_of_commute hs.1 hw hsw))
  obtain ⟨hSX, hmemX⟩ := setup_classIn hS hw Set.inter_subset_left hLx
  set X := Subgroup.closure (insert w (D ∩ (S₀ : Set G))) with hXdef
  have hwX : w ∈ X := Subgroup.subset_closure (Set.mem_insert w _)
  have hLX : ∀ s ∈ D ∩ (S₀ : Set G), s ∈ X := fun s hs =>
    Subgroup.subset_closure (Set.mem_insert_of_mem w hs)
  set EX := classIn X ⟨w, hwX⟩ with hEXdef
  have hEXD : ∀ k ∈ EX, (k : G) ∈ D := by
    intro k hk
    obtain ⟨c, rfl⟩ := isConj_iff.mp hk
    exact hS.conj_mem (c : G) hw
  set u' : X := ⟨u, hLX u hu₀⟩ with hu'def
  set v' : X := ⟨v, hLX v hv₀⟩ with hv'def
  set w' : X := ⟨w, hwX⟩ with hw'def
  have hu'E : u' ∈ EX := hmemX u hu₀
  have hv'E : v' ∈ EX := hmemX v hv₀
  have hw'E : w' ∈ EX := IsConj.refl _
  have hd'E : (⟨d, hLX d hd₀⟩ : X) ∈ EX := hmemX d hd₀
  have hdiscX : Disconnected EX := by
    refine ⟨u', hu'E, w', hw'E, fun h => huw ?_⟩
    exact reach_of_reach_subgroup X (reach_mono (fun k hk => hEXD k hk) h)
  have hzX : z ∈ X := by
    rw [hzabd]
    exact X.mul_mem (X.mul_mem (hLX u hu₀) (hLX v hv₀)) (hLX d hd₀)
  have hzcomm : ∀ g ∈ X, Commute g z := by
    intro g hg
    have hle : X ≤ Subgroup.centralizer {z} := by
      rw [hXdef, Subgroup.closure_le]
      rintro y (rfl | hy)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hzw.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hLz y hy).eq
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)
  set z' : X := ⟨z, hzX⟩ with hz'def
  have hz'c : z' ∈ Subgroup.center X := Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (hzcomm g g.2).eq
  have hz'z' : z' * z' = 1 := Subtype.ext hzz
  have hz'1 : z' ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hz'E : z' ∉ EX := fun h => hzD (hEXD z' h)
  have : (Subgroup.zpowers z').Normal := Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hz'c)
  have huvz : u' * v' * z' ∈ EX := hd'E
  have hnpc := CentralQuot.noPerfectCentralExt hz'c hz'z' hSX hz'E hdiscX hu'E hv'E
    (fun h => hne (congrArg Subtype.val h)) (commute_coe_iff.mp huv) huvz
  have hXH : X ≤ localGroup D z := by
    rw [hXdef, Subgroup.closure_le]
    rintro y (rfl | hy)
    · exact mem_localGroup_of_mem hwC
    · exact mem_localGroup_of_mem ⟨hy.1, hLz y hy⟩
  set e : G := (q : G) * u * (q : G)⁻¹ with hedef
  have hqS : (q : G) ∈ S₀ := hQS ⟨q, hq, rfl⟩
  have he : e ∈ D := hS.conj_mem _ hu
  have he₀ : e ∈ D ∩ (S₀ : Set G) :=
    ⟨he, S₀.mul_mem (S₀.mul_mem hqS huS) (S₀.inv_mem hqS)⟩
  have hcae : Commute u e := hLcomm u hu₀ e he₀
  have hae : u ≠ e := by
    intro h
    apply hqu
    show (q : G) * u = u * q
    calc (q : G) * u = (q : G) * u * (q : G)⁻¹ * q := by group
      _ = u * q := by rw [← hedef, ← h]
  set e' : X := ⟨e, hLX e he₀⟩ with he'def
  have he'E : e' ∈ EX := hmemX e he₀
  have he'a : e' * u'⁻¹ ∈ CFSG.pCore 2 X := by
    set QH : Subgroup G := (CFSG.pCore 2 (localGroup D z)).map (localGroup D z).subtype
    have hQHn : (QH.comap X.subtype).Normal := by
      refine ⟨fun y hy g => ?_⟩
      have hg := mem_normalizer_map_pCore (D := D) (hXH g.2)
      exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy
    have hQHp : IsPGroup 2 (QH.comap X.subtype) := by
      rintro ⟨y, ⟨y', hy', hyy'⟩⟩
      obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := localGroup D z) ⟨y', hy'⟩
      refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      have h1 := congrArg (fun x => ((x : CFSG.pCore 2 (localGroup D z)) :
        localGroup D z)) hk
      have h2 := congrArg Subtype.val h1
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h2
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, Subgroup.coe_subtype] at hyy' ⊢
      rw [← hyy']
      exact h2
    have hle : QH.comap X.subtype ≤ CFSG.pCore 2 X := le_sSup ⟨hQHn, hQHp⟩
    set u'' : localGroup D z := ⟨u, mem_localGroup_of_mem huC⟩ with hu''def
    refine hle ⟨q * (u'' * q⁻¹ * u''⁻¹), (CFSG.pCore 2 (localGroup D z)).mul_mem hq
        ((CFSG.pCore_normal (p := 2) (G := localGroup D z)).conj_mem _
          ((CFSG.pCore 2 (localGroup D z)).inv_mem hq) _), ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, he'def, hu'def, hedef,
      hu''def]
    group
  have haeD : u * e ∉ D := fun h => hnsq ⟨u, hu, e, he, hae, hcae, h⟩
  obtain ⟨y, hy, hay, htri₂, m, hm, hm1, hord₂⟩ :=
    exists_thirdKind hS hdisc hnorm hu he hae hcae haeD
  obtain ⟨-, -, hta, hte, -, haet⟩ := htri₂.third_kind hD hN hm hord₂
  have hP' : IsPGroup 2 ((S₀ : Subgroup G).subgroupOf X) := S₀.isPGroup'.comap_subtype
  obtain ⟨T, hT⟩ := hP'.exists_le_sylow
  have hLT : ∀ s (hs : s ∈ D ∩ (S₀ : Set G)), (⟨s, hLX s hs⟩ : X) ∈ T := fun s hs =>
    hT (Subgroup.mem_subgroupOf.mpr hs.2)
  have hz'T : z' ∈ T := hT (Subgroup.mem_subgroupOf.mpr (show z ∈ (S₀ : Subgroup G) by
    rw [hzabd]; exact S₀.mul_mem (S₀.mul_mem huS hvS) hdS))
  have hpair₂ : ({u, e, u * e * (u * e * y) ^ m} : Set G).Pairwise Commute := by
    have h1 := hcae; have h1' := hcae.symm
    have h2 : Commute u (u * e * (u * e * y) ^ m) :=
      ((Commute.refl u).mul_right hcae).mul_right hta.symm
    have h2' := h2.symm
    have h3 : Commute e (u * e * (u * e * y) ^ m) :=
      (hcae.symm.mul_right (Commute.refl e)).mul_right hte.symm
    have h3' := h3.symm
    intro s hs t ht _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;>
      first | exact Commute.refl _ | assumption
  have hP₂ : IsPGroup 2 (Subgroup.closure ({u, e, u * e * (u * e * y) ^ m} : Set G)) := by
    refine isPGroup_closure_of_pairwise hpair₂ ?_
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · exact hD.mul_self_eq_one hu
    · exact hD.mul_self_eq_one he
    · exact hD.mul_self_eq_one haet
  have hgen₂ : ∀ r ∈ ({u, e, u * e * (u * e * y) ^ m} : Set G), Commute r u ∧ Commute r e := by
    intro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with hr | hr | hr <;> rw [hr]
    · exact ⟨Commute.refl u, hcae⟩
    · exact ⟨hcae.symm, Commute.refl e⟩
    · exact ⟨(((Commute.refl u).mul_right hcae).mul_right hta.symm).symm,
        ((hcae.symm.mul_right (Commute.refl e)).mul_right hte.symm).symm⟩
  have hPC : ∀ p ∈ Subgroup.closure ({u, e, u * e * (u * e * y) ^ m} : Set G),
      Commute p u ∧ Commute p e := by
    intro p hp
    constructor
    · exact commute_of_mem_closure (S := {u, e, u * e * (u * e * y) ^ m}) (T := {u})
        (fun r hr k hk => by
          rw [Set.mem_singleton_iff] at hk; rw [hk]; exact (hgen₂ r hr).1) hp
        (Subgroup.subset_closure rfl)
    · exact commute_of_mem_closure (S := {u, e, u * e * (u * e * y) ^ m}) (T := {e})
        (fun r hr k hk => by
          rw [Set.mem_singleton_iff] at hk; rw [hk]; exact (hgen₂ r hr).2) hp
        (Subgroup.subset_closure rfl)
  have hL : ∀ s ∈ D ∩ (S₀ : Set G), Commute s u ∧ Commute s e :=
    fun s hs => ⟨hLcomm s hs u hu₀, hLcomm s hs e he₀⟩
  obtain ⟨g, hga, hge, hgP⟩ := exists_conj_mem_of_isPGroup hN S₀ hL hP₂ hPC
  set y₂ := g * y * g⁻¹ with hy₂def
  have hga' : g * u * g⁻¹ = u := by rw [hga.eq, mul_inv_cancel_right]
  have hge' : g * e * g⁻¹ = e := by rw [hge.eq, mul_inv_cancel_right]
  have hconj_aey : g * (u * e * y) * g⁻¹ = u * e * y₂ := by
    calc g * (u * e * y) * g⁻¹ = g * u * g⁻¹ * (g * e * g⁻¹) * (g * y * g⁻¹) := by group
      _ = u * e * y₂ := by rw [hga', hge']
  have hconj_back : ∀ r : G, g⁻¹ * (g * r * g⁻¹) * g⁻¹⁻¹ = r := fun r => by group
  have htri₃ : IsTriangle D u y₂ e := by
    refine ⟨hu, he, hS.conj_mem g hy, hae, hcae, fun h => ?_, fun h => ?_⟩
    · apply htri₂.2.2.2.2.2.1
      have h1 := (Commute.conj_iff g⁻¹).mpr h
      rwa [← hga', hconj_back, hconj_back] at h1
    · apply htri₂.2.2.2.2.2.2
      have h1 := (Commute.conj_iff g⁻¹).mpr h
      rwa [← hge', hconj_back, hconj_back] at h1
  have hord₃ : orderOf (u * e * y₂) = 2 * m := by
    rw [← hconj_aey, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hord₂]
  have hay₂ : ¬ Reach D u y₂ := by
    intro h
    apply hay
    have h1 := reach_conj hN g⁻¹ h
    rwa [← hga', hconj_back, hconj_back] at h1
  have ht₂ : (u * e * y₂) ^ m = g * (u * e * y) ^ m * g⁻¹ := by rw [← hconj_aey, conj_pow]
  have haet₂ : u * e * (u * e * y₂) ^ m ∈ D ∩ (S₀ : Set G) := by
    have h1 := hgP _ (Subgroup.subset_closure (by simp)) haet
    have e1 : g * (u * e * (u * e * y) ^ m) * g⁻¹ = u * e * (u * e * y₂) ^ m := by
      rw [ht₂]
      calc g * (u * e * (u * e * y) ^ m) * g⁻¹ =
          g * u * g⁻¹ * (g * e * g⁻¹) * (g * (u * e * y) ^ m * g⁻¹) := by group
        _ = u * e * (g * (u * e * y) ^ m * g⁻¹) := by rw [hga', hge']
    rwa [e1] at h1
  set t₂ := (u * e * y₂) ^ m with ht₂def
  obtain ⟨-, -, -, hte₂, -, -⟩ := htri₃.third_kind hD hN hm hord₃
  have haet₂X : u * e * t₂ ∈ X := hLX _ haet₂
  have hKH : ThirdKindHyp X EX T u' w' v' n := by
    refine ⟨hSX, ⟨hu'E, hv'E, hw'E, fun h => hne (congrArg Subtype.val h),
      commute_coe_iff.mp huv, fun h => htri.2.2.2.2.2.1 (commute_coe_iff.mpr h),
      fun h => htri.2.2.2.2.2.2 (commute_coe_iff.mpr h)⟩, hn, hn1, ?_, hLT u hu₀, hLT v hv₀,
      ?_, ?_, hnpc⟩
    · rw [← Subgroup.orderOf_coe]
      exact hord
    · have h1 : (u' * v' * w') ^ n = z' := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hzdef)
      rw [h1]
      exact hz'T
    · rw [eq_top_iff, ← Subgroup.closure_closure_coe_preimage (k := insert w (D ∩ (S₀ : Set G)))]
      refine Subgroup.closure_mono ?_
      rintro ⟨r, hr⟩ (hr' | hr')
      · left
        exact Subtype.ext hr'
      · right
        exact ⟨hmemX r hr', hLT r hr'⟩
  obtain ⟨-, hmain⟩ := hKH.main
  obtain ⟨⟨u₁, w₁⟩, ⟨hu₁, hw₁, heq'⟩, -⟩ := hmain u' ⟨hu'E, hLT u hu₀⟩ ⟨u * e * t₂, haet₂X⟩
    ⟨hmemX _ haet₂, hLT _ haet₂⟩ e' he'E he'a
  have hwc := Subgroup.mem_center_iff.mp hw₁.2
  set T₂ : X := u' * ⟨u * e * t₂, haet₂X⟩ * e' with hT₂def
  have hT₂ : (T₂ : G) = t₂ := by
    show u * (u * e * t₂) * e = t₂
    rw [show u * (u * e * t₂) * e = u * u * e * (t₂ * e) by group, hte₂.eq,
      hD.mul_self_eq_one hu, one_mul, ← mul_assoc, hD.mul_self_eq_one he, one_mul]
  have heq : t₂ = (u₁ : G) * (w₁ : G) := by
    rw [← hT₂, heq']
    rfl
  have hut : Commute (u₁ : G) t₂ := by
    have hu'eq : u₁ = T₂ * w₁⁻¹ := eq_mul_inv_of_mul_eq heq'.symm
    have h1 : Commute u₁ T₂ := by
      rw [hu'eq]
      exact (Commute.refl _).mul_left
        (Subgroup.mem_center_iff.mp ((Subgroup.center X).inv_mem hw₁.2) _).symm
    rw [← hT₂]
    exact commute_coe_iff.mpr h1
  have hwa : Commute (w₁ : G) u := commute_coe_iff.mpr (hwc u').symm
  have hwx : Commute (w₁ : G) w := commute_coe_iff.mpr (hwc w').symm
  exact false_of_eq_mul hS htri₃ hm hord₃ hay₂ hw huw (hEXD u₁ hu₁) hut heq hwa hwx

end CFSG.Timmesfeld.Bridge.Asc72
