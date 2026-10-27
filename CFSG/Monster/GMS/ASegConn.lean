module

public import CFSG.Monster.GMS.ASegConnLocal
public import CFSG.Monster.GMS.FinalStep
public import CFSG.Monster.GMS.TwoAGraph

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace ASegConn

section Stabilizer

variable {G : Type*} [Group G]

@[expose] def baseVertex (a : G) : ConjVert a := ⟨a, IsConj.refl a⟩

@[expose] def smulHom (a g : G) : twoAGraph a →g twoAGraph a where
  toFun x := g • x
  map_rel' h := twoAGraph_adj_smul g h

theorem reachable_smul {a : G} (g : G) {u v : ConjVert a} (h : (twoAGraph a).Reachable u v) :
    (twoAGraph a).Reachable (g • u) (g • v) :=
  h.map (smulHom a g)

@[expose] def InComp (a x : G) : Prop :=
  ∃ hx : IsConj a x, (twoAGraph a).Reachable (baseVertex a) ⟨x, hx⟩

theorem inComp_self (a : G) : InComp a a :=
  ⟨IsConj.refl a, SimpleGraph.Reachable.refl _⟩

theorem InComp.of_reachable {a x y : G} (hx : InComp a x) (hy : IsConj a y)
    (h : ∀ hx' : IsConj a x, (twoAGraph a).Reachable ⟨x, hx'⟩ ⟨y, hy⟩) : InComp a y := by
  obtain ⟨hx', r⟩ := hx
  exact ⟨hy, r.trans (h hx')⟩

theorem InComp.of_adj {a x y : G} (hx : InComp a x) (hy : IsConj a y) (hne : x ≠ y)
    (hxy : IsConj a (x * y)) : InComp a y :=
  hx.of_reachable hy fun _ =>
    SimpleGraph.Adj.reachable ⟨fun e => hne (congrArg Subtype.val e), hxy⟩

@[expose] def compStab (a : G) : Subgroup G where
  carrier := {g | (twoAGraph a).Reachable (baseVertex a) (g • baseVertex a)}
  one_mem' := by
    show (twoAGraph a).Reachable _ ((1 : G) • _)
    rw [one_smul]
  mul_mem' := by
    intro g h hg hh
    show (twoAGraph a).Reachable _ ((g * h) • _)
    rw [mul_smul]
    exact hg.trans (reachable_smul g hh)
  inv_mem' := by
    intro g hg
    show (twoAGraph a).Reachable _ (g⁻¹ • _)
    have h := reachable_smul g⁻¹ hg
    rw [inv_smul_smul] at h
    exact h.symm

theorem mem_compStab_of_inComp {a x : G} (hx : InComp a x) (g : G)
    (hgx : InComp a (g * x * g⁻¹)) : g ∈ compStab a := by
  obtain ⟨hx', r₁⟩ := hx
  obtain ⟨hgx', r₂⟩ := hgx
  have r₃ := reachable_smul g r₁
  exact r₂.trans r₃.symm

theorem preconnected_of_compStab_eq_top {a : G} (h : compStab a = ⊤) :
    (twoAGraph a).Preconnected := by
  have hall : ∀ x : ConjVert a, (twoAGraph a).Reachable (baseVertex a) x := by
    rintro ⟨x, hx⟩
    obtain ⟨g, hg⟩ := isConj_iff.mp hx
    have hgK : g ∈ compStab a := h ▸ Subgroup.mem_top g
    have e : g • baseVertex a = ⟨x, hx⟩ := Subtype.ext hg
    rw [← e]
    exact hgK
  exact fun u v => (hall u).symm.trans (hall v)

end Stabilizer

section Sylow

variable {G : Type*} [Group G] [Finite G]

theorem exists_conj_mem_sylow_of_le {K : Subgroup G} (S : Sylow 2 G) (hSK : (S : Subgroup G) ≤ K)
    {t : G} (htK : t ∈ K) (ht : orderOf t = 2) : ∃ k ∈ K, k * t * k⁻¹ ∈ (S : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set t' : K := ⟨t, htK⟩ with ht'def
  have ht' : orderOf t' = 2 := by rw [ht'def, Subgroup.orderOf_mk]; exact ht
  have hp : IsPGroup 2 (Subgroup.zpowers t') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht', pow_one])
  obtain ⟨R, hR⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K R (S.subtype hSK)
  refine ⟨g, g.2, ?_⟩
  have hmem : (MulAut.conj g) t' ∈ ((S.subtype hSK : Sylow 2 K) : Subgroup K) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hR (Subgroup.mem_zpowers _))
  rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hmem
  simpa [ht'def] using hmem

end Sylow

end ASegConn

section Main

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

theorem twoAGraph_preconnected_of
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (h87 : ∀ z : G, IsConj z₀ z → ∀ x y : G, ∀ (hx : IsConj a x) (hy : IsConj a y),
      x ∈ leechQ z → y ∈ leechQ z → (twoAGraph a).Reachable ⟨x, hx⟩ ⟨y, hy⟩) :
    (twoAGraph a).Preconnected := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, z, u, h⟩ := exists_twoClasses I.sls I.tableV I.leech hG
  have hz : IsConj z₀ z := h.isConj_z
  have hzG : GMSLeechCentralizer z := hG.2.of_isConj hz
  have hz2 : orderOf z = 2 := hzG.1
  have haQ : a ∈ leechQ z := h.mem_leechQ_z
  have haP : ASegConn.InComp a a := ASegConn.inComp_self a
  have hadj : ∀ x y : G, IsConj a x → IsConj a y → ASegConn.InComp a x → x ≠ y →
      IsConj a (x * y) → ASegConn.InComp a y :=
    fun x y _ hy hx hne hxy => hx.of_adj hy hne hxy
  have hQ : ∀ w : G, IsConj z₀ w → ∀ x y : G, IsConj a x → IsConj a y → x ∈ leechQ w →
      y ∈ leechQ w → ASegConn.InComp a x → ASegConn.InComp a y :=
    fun w hw x y hx hy hxQ hyQ hxc => hxc.of_reachable hy fun hx' => h87 w hw x y hx' hy hxQ hyQ
  have hvert : ∀ x : G, ASegConn.InComp a x →
      Subgroup.centralizer ({x} : Set G) ≤ ASegConn.compStab a := by
    intro x hx g hg
    refine ASegConn.mem_compStab_of_inComp hx g ?_
    have : g * x * g⁻¹ = x := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp hg]
      group
    rw [this]
    exact hx
  have hB : ∀ s : G, IsConj z₀ s → (∃ x : G, IsConj a x ∧ x ∈ leechQ s ∧ ASegConn.InComp a x) →
      Subgroup.centralizer ({s} : Set G) ≤ ASegConn.compStab a := by
    rintro s hs ⟨x, hx, hxQ, hxc⟩ g hg
    exact ASegConn.mem_compStab_of_inComp hxc g
      (hQ s hs x _ hx (isConj_conj hx g) hxQ (conj_mem_leechQ hg hxQ) hxc)
  have hCz : Subgroup.centralizer ({z} : Set G) ≤ ASegConn.compStab a :=
    hB z hz ⟨a, IsConj.refl a, haQ, haP⟩
  have hinv : ∀ s ∈ Subgroup.centralizer ({z} : Set G), orderOf s = 2 →
      Subgroup.centralizer ({s} : Set G) ≤ ASegConn.compStab a := by
    intro s hsC hs2
    rcases s31_five I.sls I.tableV I.leech hG I.leechInv hs2 with hA | hB'
    · exact hvert s (ASegConn.mem_of_isConj_mem_centralizer (ASegConn.InComp a) hadj hQ I hG hz
        (IsConj.refl a) haQ haP hA hsC)
    · exact hB s hB' (ASegConn.exists_mem_leechQ_of_isConj (ASegConn.InComp a) hadj hQ I hG hz
        (IsConj.refl a) haQ haP hB' hsC)
  obtain ⟨S, hS⟩ := hzG.exists_sylow_center
  have hzmem : z ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype := by
    rw [hS]
    exact Subgroup.mem_zpowers z
  obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hzmem
  have hzS : z ∈ (S : Subgroup G) := hwz ▸ w.2
  have hzc : ∀ s ∈ (S : Subgroup G), z * s = s * z := by
    intro s hs
    have h' := congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨s, hs⟩)
    rw [← hwz]
    simpa using h'.symm
  have huniq : ∀ x ∈ (S : Subgroup G), orderOf x = 2 → (∀ s ∈ (S : Subgroup G), x * s = s * x) →
      x = z := by
    intro x hx hx2 hxc
    have hxz : x ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype := by
      refine Subgroup.mem_map.mpr ⟨⟨x, hx⟩, Subgroup.mem_center_iff.mpr fun g => ?_, rfl⟩
      apply Subtype.ext
      simpa using (hxc g g.2).symm
    rw [hS, mem_zpowers_iff_of_orderOf_two hz2] at hxz
    rcases hxz with rfl | rfl
    · simp at hx2
    · rfl
  have hSC : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzc s hs).symm
  have hSK : (S : Subgroup G) ≤ ASegConn.compStab a := hSC.trans hCz
  have hC : ∀ t ∈ ASegConn.compStab a, orderOf t = 2 →
      Subgroup.centralizer ({t} : Set G) ≤ ASegConn.compStab a := by
    intro t htK ht2
    obtain ⟨k, hkK, hks⟩ := ASegConn.exists_conj_mem_sylow_of_le S hSK htK ht2
    have hs2 : orderOf (k * t * k⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact ht2
    have := centralizer_conj_le (hinv _ (hSC hks) hs2) ((ASegConn.compStab a).inv_mem hkK)
    simpa [mul_assoc] using this
  have hKtop : ASegConn.compStab a = ⊤ := by
    by_contra hne
    have hSE := CFSG.Monster.B.Recog.isStronglyEmbeddedOrder_of_centralizer_le_of_unique hne hC S
      hSK hzS hz2 hzc huniq
    exact hG.not_isConj (isConj_of_isStronglyEmbeddedOrder hSE S hSK hG.1.1 hG.2.1)
  exact ASegConn.preconnected_of_compStab_eq_top hKtop

end Main

end CFSG.Monster.GMS
