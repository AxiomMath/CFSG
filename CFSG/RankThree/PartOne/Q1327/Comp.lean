module

public import CFSG.RankThree.PartOne.Q1327.Frame
public import CFSG.RankThree.PartOne.Q1327.ThetaM
public import CFSG.RankThree.PartOne.Q1327.ThetaLemmas
public import CFSG.RankThree.PartOne.Q1327.BridgeConn
public import CFSG.RankThree.PartOne.Q1327.Lines

public section

namespace CFSG.RankThree.PartOne.Q1327

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K1320
  CFSG.RankThree.PartOne.K1327
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
  {f r : ℕ} {R : Subgroup G} {s s' zs : MulAut E}

@[expose] def clsOf (p : ℕ) (E : Subgroup G) (a : MulAut E) : Set (MulAut E) :=
  {t | ∃ g ∈ reflectionGroup p E, g * a * g⁻¹ = t}

omit [Finite G] in
theorem mem_clsOf_self (p : ℕ) (E : Subgroup G) (a : MulAut E) : a ∈ clsOf p E a :=
  ⟨1, Subgroup.one_mem _, by simp⟩

omit [Finite G] in
theorem clsOf_trans {a t : MulAut E} (h1 : t ∈ clsOf p E a) {t' : MulAut E} (h2 : t' ∈ clsOf p E t) :
    t' ∈ clsOf p E a := by
  obtain ⟨g, hg, rfl⟩ := h1
  obtain ⟨g', hg', rfl⟩ := h2
  refine ⟨g' * g, Subgroup.mul_mem _ hg' hg, ?_⟩
  group

theorem E_le_centralizer_R (H : Hyp G p A c L E f r R s s' zs) :
    E ≤ Subgroup.centralizer (R : Set G) := fun e he =>
  Subgroup.mem_centralizer_iff.mpr fun x hx => H.hRE x hx e he

theorem centralizer_R_ne_top (H : Hyp G p A c L E f r R s s' zs) :
    Subgroup.centralizer (R : Set G) ≠ ⊤ := by
  have h := H.h12
  have : IsSimpleGroup G := h.setup.1
  have hR : R ≠ ⊥ := by
    intro h0
    have := H.hRcard
    rw [h0, Subgroup.card_bot] at this
    exact H.hr.one_lt.ne this
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hR
  have hx1' : x ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
  intro htop
  apply EmbeddingFixedResidual.centralizer_ne_top_of_simple h.setup.2.1 hx1'
  rw [eq_top_iff, ← htop]
  exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hx)

theorem class_facts (H : Hyp G p A c L E f r R s s' zs) {a : MulAut E} (ha : a = s ∨ a = s')
    {t : MulAut E} (ht : t ∈ clsOf p E a) :
    t ∈ reflectionSet p E ∧ KFAt p E f t ∧
      R ≤ Subgroup.centralizer (kZero p E t : Set G) ∧
      kZero p E t ≤ Subgroup.centralizer (R : Set G) := by
  obtain ⟨g, hgX, rfl⟩ := ht
  obtain ⟨y, hy, hyg⟩ := Sec1322.exists_lift (Sec1322.reflectionGroup_le E hgX)
  have haS : a ∈ reflectionSet p E ∧ KFAt p E f a ∧
      R ≤ Subgroup.centralizer (kZero p E a : Set G) := by
    rcases ha with rfl | rfl
    · exact ⟨H.hs, H.hKs, H.hRs⟩
    · exact ⟨H.hs', H.hKs', H.hRs'⟩
  rw [← hyg]
  have hRy : conjBy y R = R := H.hRnorm y hy (by rw [hyg]; exact hgX)
  have hRt : R ≤ Subgroup.centralizer (kZero p E (conjAut E y hy * a * (conjAut E y hy)⁻¹) :
      Set G) := by
    rw [kZero_conj p a hy, Equivariance.centralizer_conjBy]
    have := Subgroup.map_mono (f := (MulAut.conj y).toMonoidHom) haS.2.2
    rw [← hRy]
    exact this
  exact ⟨conj_mem_reflectionSet H.h12.prime haS.1 hy, haS.2.1.conj hy, hRt,
    le_centralizer_symm hRt⟩

theorem exists_J_of_class (hS : SchreierFor InCatalog) (H : Hyp G p A c L E f r R s s' zs)
    {a : MulAut E} (ha : a = s ∨ a = s') {t : MulAut E} (ht : t ∈ clsOf p E a) :
    ∃ J ∈ thetaComponents p ↥(Subgroup.centralizer (R : Set G)),
      (kZero p E t).subgroupOf (Subgroup.centralizer (R : Set G)) ≤ J := by
  have h := H.h12
  have hp := h.prime
  obtain ⟨-, hKt, -, hKtM⟩ := class_facts H ha ht
  have hq : CFSG.IsQuasisimple ↥(kZero p E t) := (KFAt.toLiftAt hKt).1
  have hMne := centralizer_R_ne_top H
  have hKM : ∀ H' : Subgroup G, H' ≤ Subgroup.centralizer (R : Set G) → CFSG.IsKGroup ↥H' :=
    fun H' hH' => h.setup.2.2.1 H' (ne_top_of_le_ne_top hMne hH')
  have hD : autFixedInG E t ≤ Subgroup.centralizer (R : Set G) :=
    (Subgroup.map_subtype_le _).trans (E_le_centralizer_R H)
  have hDel : IsElementaryAbelian p ↥(autFixedInG E t) :=
    isElementaryAbelian_of_le' h.E_elem (Subgroup.map_subtype_le _)
  exact exists_thetaComponent_ge hp h.three_lt hS hKM h.evenRank_eq.le
    (Nat.card ↥(autFixedInG E t)) (autFixedInG E t) hD rfl hDel (kZero p E t)
    (le_inf hKtM (kZero_le_centralizer_fixed p E t))
    (kZero_mem_thetaComponents_inf hp hq hKtM)

theorem J_eq_of_noncommute (H : Hyp G p A c L E f r R s s' zs) {a : MulAut E}
    (ha : a = s ∨ a = s') {t t' : MulAut E} (ht : t ∈ clsOf p E a) (ht' : t' ∈ clsOf p E a)
    (hnc : t * t' ≠ t' * t)
    {J J' : Subgroup ↥(Subgroup.centralizer (R : Set G))}
    (hJ : J ∈ thetaComponents p ↥(Subgroup.centralizer (R : Set G)))
    (hJ' : J' ∈ thetaComponents p ↥(Subgroup.centralizer (R : Set G)))
    (hKJ : (kZero p E t).subgroupOf (Subgroup.centralizer (R : Set G)) ≤ J)
    (hKJ' : (kZero p E t').subgroupOf (Subgroup.centralizer (R : Set G)) ≤ J') : J = J' := by
  by_contra hne
  have h := H.h12
  have hp := h.prime
  obtain ⟨-, hKt, -, hKtM⟩ := class_facts H ha ht
  obtain ⟨-, hKt', -, hKtM'⟩ := class_facts H ha ht'
  obtain ⟨-, -, -, -, k, hk, hkK, hkt⟩ := hKt
  obtain ⟨-, -, -, -, k', hk', hkK', hkt'⟩ := hKt'
  set I₁ : Subgroup G := J.map (Subgroup.centralizer (R : Set G)).subtype with hI₁
  set I₂ : Subgroup G := J'.map (Subgroup.centralizer (R : Set G)).subtype with hI₂
  have hI₁M : I₁ ≤ Subgroup.centralizer (R : Set G) := Subgroup.map_subtype_le _
  have hI₂M : I₂ ≤ Subgroup.centralizer (R : Set G) := Subgroup.map_subtype_le _
  have h1 : I₁.subgroupOf (Subgroup.centralizer (R : Set G)) = J :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.centralizer (R : Set G)).subtype_injective _
  have h2 : I₂.subgroupOf (Subgroup.centralizer (R : Set G)) = J' :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.centralizer (R : Set G)).subtype_injective _
  have hk₁ : k ∈ I₁ := ⟨⟨k, hKtM hkK⟩,
    hKJ (show (⟨k, hKtM hkK⟩ : ↥(Subgroup.centralizer (R : Set G))) ∈
      (kZero p E t).subgroupOf (Subgroup.centralizer (R : Set G)) from
      Subgroup.mem_subgroupOf.mpr hkK), rfl⟩
  have hk₂ : k' ∈ I₂ := ⟨⟨k', hKtM' hkK'⟩,
    hKJ' (show (⟨k', hKtM' hkK'⟩ : ↥(Subgroup.centralizer (R : Set G))) ∈
      (kZero p E t').subgroupOf (Subgroup.centralizer (R : Set G)) from
      Subgroup.mem_subgroupOf.mpr hkK'), rfl⟩
  have hcomm := commute_of_distinct_components_M hp h.E_elem (E_le_centralizer_R H)
    (I₁ := I₁) (I₂ := I₂) (by rw [h1]; exact hJ) (by rw [h2]; exact hJ')
    (by rw [h1, h2]; exact hne) hI₁M hI₂M hk₁ hk₂ hk hk'
  rw [hkt, hkt'] at hcomm
  exact hnc hcomm

theorem eq_one_of_mem_zpowers_fixed {c z : G} (hp : p.Prime) (hc : orderOf c = p)
    (hz : z ∈ Subgroup.zpowers c) {S : Subgroup G} (hzS : z ∈ S) (hcS : c ∉ S) : z = 1 := by
  by_contra hz1
  have h1 : orderOf z ∣ p := by
    have := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers c) hz
    rwa [Nat.card_zpowers, hc] at this
  have h2 : orderOf z = p := by
    rcases (Nat.dvd_prime hp).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hz1
    · exact h
  have h3 : Subgroup.zpowers z = Subgroup.zpowers c :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hz)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hc, h2])
  apply hcS
  have : c ∈ Subgroup.zpowers z := by rw [h3]; exact Subgroup.mem_zpowers c
  exact (Subgroup.zpowers_le.2 hzS) this

omit [Finite G] in
theorem subgroupOf_ne_bot_perfect {K M : Subgroup G} (hKM : K ≤ M) (hq : CFSG.IsQuasisimple ↥K) :
    K.subgroupOf M ≠ ⊥ ∧ Group.IsPerfect ↥(K.subgroupOf M) := by
  have e := Subgroup.subgroupOfEquivOfLe hKM
  have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have hnt : Nontrivial ↥(K.subgroupOf M) := e.toEquiv.nontrivial
  refine ⟨(Subgroup.nontrivial_iff_ne_bot _).1 hnt, ?_⟩
  have : Group.IsPerfect ↥K := hq.1
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

structure JcData (p : ℕ) (E : Subgroup G) (c : G) (R : Subgroup G) (s : MulAut E)
    (Jc : Subgroup G) : Prop where
  le_M : Jc ≤ Subgroup.centralizer (R : Set G)
  mem : Jc.subgroupOf (Subgroup.centralizer (R : Set G)) ∈
    thetaComponents p ↥(Subgroup.centralizer (R : Set G))
  K_le : ∀ t ∈ clsOf p E s, kZero p E t ≤ Jc
  E_le : E ≤ Jc
  moves : ∃ t ∈ clsOf p E s, c ∉ autFixedInG E t
  fixed_trivial : ∀ z ∈ E, (∀ t ∈ clsOf p E s, z ∈ autFixedInG E t) → z = 1

theorem exists_Jc (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (H : Hyp G p A c L E f r R s s' zs) :
    ∃ Jc : Subgroup G, JcData p E c R s Jc := by
  have h := H.h12
  have hp := h.prime
  have hp2 : p ≠ 2 := by have := Sec12Three.five_le h; omega
  have hcard : Nat.card E = p ^ 3 := by rw [H.hEA]; exact h.A_card
  have hcE : c ∈ E := h.A_le_E h.c_mem
  obtain ⟨eX⟩ := H.hweyl
  obtain ⟨Bd⟩ := exists_bridge h H.hF13 hcard eX
  obtain ⟨a, a', b, g₀, ha, ha', hb, haL, ha'L, hbL, hss, hcomm, hne, hab4, ⟨h₁, hh₁X, hh₁⟩,
    hucen, hfixu, hfixc, hg₀X, hg₀, hza, hzb, hzab, hzba⟩ := refData hGA H
  have haS : a = s ∨ a = s' := by
    rcases hss with ⟨h1, -⟩ | ⟨-, h1⟩
    · exact Or.inl h1.symm
    · exact Or.inr h1.symm
  have ha'cls : a' ∈ clsOf p E a := ⟨h₁, hh₁X, hh₁⟩
  have hscls : s ∈ clsOf p E a := by
    rcases hss with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h1]; exact mem_clsOf_self p E a
    · rw [h1]; exact ha'cls
  have hacls : a ∈ clsOf p E s := by
    rcases hss with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [← h1]; exact mem_clsOf_self p E s
    · refine ⟨h₁⁻¹, Subgroup.inv_mem _ hh₁X, ?_⟩
      rw [h1, ← hh₁]
      group
  have hcls : ∀ t ∈ clsOf p E s, t ∈ clsOf p E a := fun t ht => clsOf_trans hscls ht
  have hcls' : ∀ t ∈ clsOf p E a, t ∈ clsOf p E s := fun t ht => clsOf_trans hacls ht
  have hMne := centralizer_R_ne_top H
  obtain ⟨J₀, hJ₀, hKJ₀⟩ := exists_J_of_class hS H haS (mem_clsOf_self p E a)
  have hall : ∀ t ∈ clsOf p E a,
      (kZero p E t).subgroupOf (Subgroup.centralizer (R : Set G)) ≤ J₀ := by
    intro t ht
    obtain ⟨J_t, hJt, hKJt⟩ := exists_J_of_class hS H haS ht
    have hJeq : J_t = J₀ := by
      rcases bridge_conn Bd h hcard ha hb H.hzs hab4 (H.hzc a haL) (H.hzc b hbL) hza hzb hzab hzba
          ⟨g₀, hg₀X, hg₀⟩ ht with h1 | h1 | ⟨u, hu, hau, htu⟩
      ·
        subst h1
        obtain ⟨-, hKt, -, hKtM⟩ := class_facts H haS ht
        obtain ⟨hP0, hPperf⟩ := subgroupOf_ne_bot_perfect hKtM (KFAt.toLiftAt hKt).1
        exact theta_component_eq_of_perfect_le hp hJt hJ₀ hP0 hPperf hKJt hKJ₀
      · exact (J_eq_of_noncommute H haS (mem_clsOf_self p E a) ht h1 hJ₀ hJt hKJ₀ hKJt).symm
      · obtain ⟨J_u, hJu, hKJu⟩ := exists_J_of_class hS H haS hu
        have e1 := J_eq_of_noncommute H haS (mem_clsOf_self p E a) hu hau hJ₀ hJu hKJ₀ hKJu
        have e2 := J_eq_of_noncommute H haS ht hu htu hJt hJu hKJt hKJu
        rw [e2, ← e1]
    exact hJeq ▸ hKJt
  refine ⟨J₀.map (Subgroup.centralizer (R : Set G)).subtype, ?_⟩
  have hKle : ∀ t ∈ clsOf p E a, kZero p E t ≤ J₀.map (Subgroup.centralizer (R : Set G)).subtype := by
    intro t ht x hx
    obtain ⟨-, -, -, hKtM⟩ := class_facts H haS ht
    exact ⟨⟨x, hKtM hx⟩, hall t ht (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hd := RefFacts.ElemData.of_isElementaryAbelian hp hp2 h.E_elem
  have hlines : ∀ t ∈ clsOf p E a,
      autMovedInG E t ≤ J₀.map (Subgroup.centralizer (R : Set G)).subtype := by
    intro t ht
    obtain ⟨-, hKt, -, -⟩ := class_facts H haS ht
    exact hKt.2.2.2.1.trans (hKle t ht)
  have hg₀W : g₀ ∈ torusWeyl E := Sec1322.reflectionGroup_le E hg₀X
  have ht3 : g₀ * a * g₀⁻¹ ∈ clsOf p E a := ⟨g₀, hg₀X, rfl⟩
  have ht4 : g₀ * a' * g₀⁻¹ ∈ clsOf p E a :=
    ⟨g₀ * h₁, Subgroup.mul_mem _ hg₀X hh₁X, by rw [← hh₁]; group⟩
  have hEle : E ≤ J₀.map (Subgroup.centralizer (R : Set G)).subtype :=
    E_le_of_lines hd hcE (RefFacts.mul_self_eq_one ha.1) (RefFacts.mul_self_eq_one ha'.1) hcomm
      (hucen b hbL) (hfixc b hbL hcE) hfixu hg₀W hg₀ H.hmov
      (hlines a (mem_clsOf_self p E a)) (hlines a' ha'cls) (hlines _ ht3) (hlines _ ht4)
  have hmoves : ∃ t ∈ clsOf p E s, c ∉ autFixedInG E t := by
    rcases exists_moves_c hd hcE h.c_ne_one hb.1 (hfixc b hbL hcE) hfixu hg₀W hg₀ H.hmov with h1 | h1
    · exact ⟨_, hcls' _ ht3, h1⟩
    · exact ⟨_, hcls' _ ht4, h1⟩
  refine ⟨Subgroup.map_subtype_le _, ?_, fun t ht => hKle t (hcls t ht), hEle, hmoves, ?_⟩
  · have : (J₀.map (Subgroup.centralizer (R : Set G)).subtype).subgroupOf
        (Subgroup.centralizer (R : Set G)) = J₀ :=
      Subgroup.comap_map_eq_self_of_injective (Subgroup.centralizer (R : Set G)).subtype_injective _
    rw [this]
    exact hJ₀
  ·
    intro z hzE hzfix
    have hza : z ∈ autFixedInG E a := hzfix a hacls
    have hza' : z ∈ autFixedInG E a' := hzfix a' (hcls' a' ha'cls)
    have hzu : z ∈ autFixedInG E (a * a') := by
      obtain ⟨m, hm, hmz⟩ := hza
      obtain ⟨m', hm', hmz'⟩ := hza'
      have e1 : m = ⟨z, hzE⟩ := Subtype.ext hmz
      have e2 : m' = ⟨z, hzE⟩ := Subtype.ext hmz'
      rw [e1] at hm
      rw [e2] at hm'
      refine ⟨⟨z, hzE⟩, ?_, rfl⟩
      show a (a' ⟨z, hzE⟩) = ⟨z, hzE⟩
      have h1 : a ⟨z, hzE⟩ = ⟨z, hzE⟩ := hm
      have h2 : a' ⟨z, hzE⟩ = ⟨z, hzE⟩ := hm'
      rw [h2, h1]
    rw [hfixu] at hzu
    obtain ⟨t₁, ht₁, hct₁⟩ := hmoves
    exact eq_one_of_mem_zpowers_fixed hp (Sec12Three.orderOf_c h) hzu (hzfix t₁ ht₁) hct₁

end CFSG.RankThree.PartOne.Q1327
