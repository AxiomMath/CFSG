module

public import CFSG.Quasithin.Recognition.St84.SetupOf

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86 CFSG.Quasithin.F6.GoldAmL3T

open scoped Pointwise

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Setup

variable (X : Setup Γ G)

theorem arcStab_le_Gi_of_between {m r k : ℤ} (hmk : m ≤ k) (hkr : k ≤ r) :
    X.arcStab m r ≤ X.Gi k := by
  have h := X.arcStab_anti (m := m) (m' := k) (r := r) (r' := k) hmk hkr
  rwa [X.arcStab_self k] at h

theorem arcStab_le_Gi_left {m r : ℤ} (hmr : m < r) : X.arcStab m r ≤ X.Gi m :=
  X.arcStab_le_Gi_of_between le_rfl hmr.le

theorem arcStab_le_Gi_right {m r : ℤ} (hmr : m < r) : X.arcStab m r ≤ X.Gi r :=
  X.arcStab_le_Gi_of_between hmr.le le_rfl

theorem arcStab_le_Gi_left_succ {m r : ℤ} (hmr : m < r) :
    X.arcStab m r ≤ X.Gi (m + 1) :=
  X.arcStab_le_Gi_of_between (by omega) (by omega)

theorem arcStab_le_Gi_right_pred {m r : ℤ} (hmr : m < r) :
    X.arcStab m r ≤ X.Gi (r - 1) :=
  X.arcStab_le_Gi_of_between (by omega) (by omega)

theorem edgeSylow_right_eq (r : ℤ) :
    X.edgeSylow (r - 1) = pCoreOf 2 (X.Gi (r - 1) ⊓ X.Gi r) := by
  unfold Setup.edgeSylow
  rw [show r - 1 + 1 = r by omega]

theorem isSylowTwoOf_edgeSylow_right (r : ℤ) :
    IsSylowTwoOf (pCoreOf 2 (X.Gi (r - 1) ⊓ X.Gi r)) (X.Gi (r - 1) ⊓ X.Gi r) := by
  rw [← X.edgeSylow_right_eq r]
  have hr : r - 1 + 1 = r := by omega
  simpa only [hr] using X.isSylowTwoOf_edgeSylow (r - 1)

theorem Q_le_edgeSylow_right (r : ℤ) :
    X.Q r ≤ pCoreOf 2 (X.Gi (r - 1) ⊓ X.Gi r) := by
  rw [← X.edgeSylow_right_eq r]
  have hr : r - 1 + 1 = r := by omega
  simpa only [hr] using X.Q_le_edgeSylow (r - 1)

theorem Q_le_edgeSylow_left (m : ℤ) : X.Q m ≤ X.edgeSylow m := by
  rw [X.edgeSylow_eq_vertexSylow m]
  exact pCoreOf_le_vertexSylowMap X.hyp (X.hyp.isLocL2_oTwoPrime (X.vert m)) (X.vert (m + 1))

theorem edgeSylow_transitive_right (r : ℤ) :
    ∀ a b : V, Γ.Adj (X.vert r) a → a ≠ X.vert (r - 1) →
      Γ.Adj (X.vert r) b → b ≠ X.vert (r - 1) →
      ∃ s ∈ pCoreOf 2 (X.Gi (r - 1) ⊓ X.Gi r), s • a = b := by
  have hr : r - 1 + 1 = r := by omega
  have h := X.edgeSylow_transitive (r - 1)
  rw [X.edgeSylow_right_eq r] at h
  intro a b ha hab hb hbb
  have ha' : Γ.Adj (X.vert ((r - 1) + 1)) a := by rwa [hr]
  have hb' : Γ.Adj (X.vert ((r - 1) + 1)) b := by rwa [hr]
  exact h a b ha' hab hb' hbb

theorem edgeSylow_transitive_left (m : ℤ) :
    ∀ a b : V, Γ.Adj (X.vert m) a → a ≠ X.vert (m + 1) →
      Γ.Adj (X.vert m) b → b ≠ X.vert (m + 1) →
      ∃ s ∈ X.edgeSylow m, s • a = b := by
  intro a b ha hab hb hbb
  rw [X.edgeSylow_eq_vertexSylow m]
  exact CFSG.Quasithin.St84.edgeSylow_transitive X.hyp (X.hyp.isLocL2_oTwoPrime (X.vert m))
    (X.adj m) ha hb hab hbb

theorem Q_fixes_neighbors_vert (i : ℤ) :
    ∀ a : V, Γ.Adj (X.vert i) a → ∀ q ∈ X.Q i, q • a = a :=
  (X.hyp.isLocL2_oTwoPrime (X.vert i)).Q_fixes_neighbors X.hyp.adj_smul
    (X.hyp.finite_stab (X.vert i)) (X.hyp.valency (X.vert i)).2 (X.hyp.valency (X.vert i)).1

theorem exists_conj_mem_Q_right (r : ℤ) {x y : G}
    (hxS : x ∈ pCoreOf 2 (X.Gi (r - 1) ⊓ X.Gi r))
    (hyS : y ∈ pCoreOf 2 (X.Gi (r - 1) ⊓ X.Gi r))
    (hxQ : x ∉ X.Q r) (hyQ : y ∉ X.Q r) :
    ∃ k ∈ X.K ⊓ X.L r, k * x * k⁻¹ * y⁻¹ ∈ X.Q r := by
  have hr : r - 1 + 1 = r := by omega
  have hxS' : x ∈ X.edgeSylow (r - 1) := by rwa [X.edgeSylow_right_eq r]
  have hyS' : y ∈ X.edgeSylow (r - 1) := by rwa [X.edgeSylow_right_eq r]
  have h := X.exists_conj_mem_pCoreOf (r - 1) (x := x) (y := y) hxS' hyS'
    (by simpa only [hr] using hxQ) (by simpa only [hr] using hyQ)
  simpa only [hr] using h

theorem exists_conj_mem_Q_left (m : ℤ) {x y : G} (hxS : x ∈ X.edgeSylow m)
    (hyS : y ∈ X.edgeSylow m) (hxQ : x ∉ X.Q m) (hyQ : y ∉ X.Q m) :
    ∃ k ∈ X.K ⊓ X.L m, k * x * k⁻¹ * y⁻¹ ∈ X.Q m := by
  classical
  obtain ⟨S, K', hSmap, hKmap, hKS, hsup⟩ := X.exists_torusSylow m
  obtain ⟨x', hx', hx'eq⟩ := Subgroup.mem_map.mp (by rw [hSmap]; exact hxS)
  obtain ⟨y', hy', hy'eq⟩ := Subgroup.mem_map.mp (by rw [hSmap]; exact hyS)
  have hxQ' : (x' : G) ∉ X.Q m := by
    intro h
    exact hxQ (hx'eq ▸ h)
  have hyQ' : (y' : G) ∉ X.Q m := by
    intro h
    exact hyQ (hy'eq ▸ h)
  have hN : IsLocL2 Γ G (X.vert m) (X.n m) (X.L m) := X.hyp.isLocL2_oTwoPrime (X.vert m)
  have htrans := hN.torus_transitive_on_sylow X.hyp.adj_smul
    (X.hyp.finite_stab (X.vert m)) (X.hyp.valency (X.vert m)).2
    (X.hyp.valency (X.vert m)).1 S K' hKS hsup hx' hy' hxQ' hyQ'
  obtain ⟨k, hkQ⟩ := htrans
  refine ⟨(k : X.L m), ?_, ?_⟩
  · have : ((k : X.L m) : G) ∈ K'.map (X.L m).subtype := Subgroup.mem_map_of_mem _ k.2
    rwa [hKmap] at this
  · have hmem : (k * x' * k⁻¹ * (y')⁻¹) ∈ (X.Q m).subgroupOf (X.L m) := hkQ
    rw [Subgroup.mem_subgroupOf] at hmem
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hmem
    rw [show (x' : G) = x from hx'eq, show (y' : G) = y from hy'eq] at hmem
    exact hmem

abbrev RightTransAt (m r : ℤ) : Prop :=
  ∀ a b : V, Γ.Adj (X.vert r) a → a ≠ X.vert (r - 1) → Γ.Adj (X.vert r) b → b ≠ X.vert (r - 1) →
    ∃ g ∈ X.arcStab m r, g • a = b

abbrev LeftTransAt (m r : ℤ) : Prop :=
  ∀ a b : V, Γ.Adj (X.vert m) a → a ≠ X.vert (m + 1) → Γ.Adj (X.vert m) b → b ≠ X.vert (m + 1) →
    ∃ g ∈ X.arcStab m r, g • a = b

theorem pCoreOf_arcStab_le_Q_right (m r : ℤ) (hmr : m < r) (hsing : ¬ X.RightTransAt m r) :
    pCoreOf 2 (X.arcStab m r) ≤ X.Q r := by
  classical
  by_contra hPQ
  obtain ⟨x, hxP, hxQ⟩ := Set.not_subset.mp hPQ
  have hPle : pCoreOf 2 (X.arcStab m r) ≤ X.arcStab m r :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 (X.arcStab m r)
  have hPH : pCoreOf 2 (X.arcStab m r) ≤ X.Gi (r - 1) ⊓ X.Gi r :=
    le_inf (hPle.trans (X.arcStab_le_Gi_right_pred hmr))
      (hPle.trans (X.arcStab_le_Gi_right hmr))
  haveI : Finite ↥(X.Gi (r - 1) ⊓ X.Gi r) :=
    finite_of_le_stabilizer X.hyp (H := X.Gi (r - 1) ⊓ X.Gi r) inf_le_left
  have hSylow : IsSylowTwoOf (pCoreOf 2 (X.Gi (r - 1) ⊓ X.Gi r))
      (X.Gi (r - 1) ⊓ X.Gi r) :=
    X.isSylowTwoOf_edgeSylow_right r
  have hSn : ((pCoreOf 2 (X.Gi (r - 1) ⊓ X.Gi r)).subgroupOf
      (X.Gi (r - 1) ⊓ X.Gi r)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi (r - 1) ⊓ X.Gi r))
  have hPS : pCoreOf 2 (X.arcStab m r) ≤ pCoreOf 2 (X.Gi (r - 1) ⊓ X.Gi r) :=
    le_of_normal_isSylowTwoOf hSylow hSn hPH (pCoreOf_isPGroup' (X.arcStab m r))
  have hxS : x ∈ pCoreOf 2 (X.Gi (r - 1) ⊓ X.Gi r) := hPS hxP
  have hQS : X.Q r ≤ pCoreOf 2 (X.Gi (r - 1) ⊓ X.Gi r) := X.Q_le_edgeSylow_right r
  have hKnorm : X.K ≤ Subgroup.normalizer (pCoreOf 2 (X.arcStab m r) : Set G) :=
    (X.K_le_GT.trans (X.GT_le_arcStab m r)).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.arcStab m r))
  have hsup_le : pCoreOf 2 (X.arcStab m r) ⊔ X.Q r ≤
      pCoreOf 2 (X.Gi (r - 1) ⊓ X.Gi r) :=
    sup_le hPS hQS
  have hS_le_sup : pCoreOf 2 (X.Gi (r - 1) ⊓ X.Gi r) ≤
      pCoreOf 2 (X.arcStab m r) ⊔ X.Q r := by
    intro y hyS
    by_cases hyQ : y ∈ X.Q r
    · exact Subgroup.mem_sup_right hyQ
    · obtain ⟨k, hkK, hkq⟩ := X.exists_conj_mem_Q_right r hxS hyS hxQ hyQ
      have hkinv : k⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 (X.arcStab m r) : Set G) :=
        inv_mem (hKnorm hkK.1)
      have hzP : k * x * k⁻¹ ∈ pCoreOf 2 (X.arcStab m r) := by
        have hz := (Subgroup.mem_normalizer_iff''.mp hkinv x).mp hxP
        simpa only [inv_inv] using hz
      have hmem : y ∈ pCoreOf 2 (X.arcStab m r) ⊔ X.Q r := by
        have h := (pCoreOf 2 (X.arcStab m r) ⊔ X.Q r).mul_mem
          ((pCoreOf 2 (X.arcStab m r) ⊔ X.Q r).inv_mem (Subgroup.mem_sup_right hkq))
          (Subgroup.mem_sup_left hzP)
        rwa [show (k * x * k⁻¹ * y⁻¹)⁻¹ * (k * x * k⁻¹) = y by group] at h
      exact hmem
  have hsup_eq : pCoreOf 2 (X.arcStab m r) ⊔ X.Q r =
      pCoreOf 2 (X.Gi (r - 1) ⊓ X.Gi r) :=
    le_antisymm hsup_le hS_le_sup
  have hPtrans : ∀ a b : V, Γ.Adj (X.vert r) a → a ≠ X.vert (r - 1) →
      Γ.Adj (X.vert r) b → b ≠ X.vert (r - 1) →
      ∃ p ∈ pCoreOf 2 (X.arcStab m r), p • a = b := by
    intro a b ha hab hb hbb
    obtain ⟨s, hsS, hsb⟩ := X.edgeSylow_transitive_right r a b ha hab hb hbb
    have hPnormQ : pCoreOf 2 (X.arcStab m r) ≤ Subgroup.normalizer (X.Q r : Set G) :=
      hPle.trans ((X.arcStab_le_Gi_right hmr).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi r)))
    have hcoe : (↑(pCoreOf 2 (X.arcStab m r) ⊔ X.Q r) : Set G) =
        ↑(pCoreOf 2 (X.arcStab m r)) * ↑(X.Q r) :=
      Subgroup.coe_mul_of_left_le_normalizer_right
        (pCoreOf 2 (X.arcStab m r)) (X.Q r) hPnormQ
    have hs : s ∈ (↑(pCoreOf 2 (X.arcStab m r)) * ↑(X.Q r) : Set G) := by
      rw [← hcoe, hsup_eq]
      exact hsS
    obtain ⟨p, hpP, q, hqQ, hpq⟩ := hs
    have hpq' : p * q = s := hpq
    refine ⟨p, hpP, ?_⟩
    calc p • a = p • (q • a) := by rw [X.Q_fixes_neighbors_vert r a ha q hqQ]
      _ = (p * q) • a := (mul_smul p q a).symm
      _ = s • a := by rw [hpq']
      _ = b := hsb
  exact hsing (fun a b ha hab hb hbb => by
    obtain ⟨p, hpP, hpa⟩ := hPtrans a b ha hab hb hbb
    exact ⟨p, hPle hpP, hpa⟩)

theorem pCoreOf_arcStab_fixes_right (m r : ℤ) (hmr : m < r)
    (hsing : ¬ X.RightTransAt m r) :
    ∀ a, Γ.Adj (X.vert r) a → ∀ g ∈ pCoreOf 2 (X.arcStab m r), g • a = a := by
  intro a ha g hg
  exact X.Q_fixes_neighbors_vert r a ha g (X.pCoreOf_arcStab_le_Q_right m r hmr hsing hg)

theorem pCoreOf_arcStab_le_Q_left (m r : ℤ) (hmr : m < r) (hsing : ¬ X.LeftTransAt m r) :
    pCoreOf 2 (X.arcStab m r) ≤ X.Q m := by
  classical
  by_contra hPQ
  obtain ⟨x, hxP, hxQ⟩ := Set.not_subset.mp hPQ
  have hPle : pCoreOf 2 (X.arcStab m r) ≤ X.arcStab m r :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 (X.arcStab m r)
  have hPH : pCoreOf 2 (X.arcStab m r) ≤ X.Gi m ⊓ X.Gi (m + 1) :=
    le_inf (hPle.trans (X.arcStab_le_Gi_left hmr))
      (hPle.trans (X.arcStab_le_Gi_left_succ hmr))
  haveI : Finite ↥(X.Gi m ⊓ X.Gi (m + 1)) :=
    finite_of_le_stabilizer X.hyp (H := X.Gi m ⊓ X.Gi (m + 1)) inf_le_left
  have hSylow : IsSylowTwoOf (X.edgeSylow m) (X.Gi m ⊓ X.Gi (m + 1)) :=
    X.isSylowTwoOf_edgeSylow m
  have hSn : ((X.edgeSylow m).subgroupOf (X.Gi m ⊓ X.Gi (m + 1))).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi m ⊓ X.Gi (m + 1)))
  have hPS : pCoreOf 2 (X.arcStab m r) ≤ X.edgeSylow m :=
    le_of_normal_isSylowTwoOf hSylow hSn hPH (pCoreOf_isPGroup' (X.arcStab m r))
  have hxS : x ∈ X.edgeSylow m := hPS hxP
  have hQS : X.Q m ≤ X.edgeSylow m := X.Q_le_edgeSylow_left m
  have hKnorm : X.K ≤ Subgroup.normalizer (pCoreOf 2 (X.arcStab m r) : Set G) :=
    (X.K_le_GT.trans (X.GT_le_arcStab m r)).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.arcStab m r))
  have hsup_le : pCoreOf 2 (X.arcStab m r) ⊔ X.Q m ≤ X.edgeSylow m :=
    sup_le hPS hQS
  have hS_le_sup : X.edgeSylow m ≤ pCoreOf 2 (X.arcStab m r) ⊔ X.Q m := by
    intro y hyS
    by_cases hyQ : y ∈ X.Q m
    · exact Subgroup.mem_sup_right hyQ
    · obtain ⟨k, hkK, hkq⟩ := X.exists_conj_mem_Q_left m hxS hyS hxQ hyQ
      have hkinv : k⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 (X.arcStab m r) : Set G) :=
        inv_mem (hKnorm hkK.1)
      have hzP : k * x * k⁻¹ ∈ pCoreOf 2 (X.arcStab m r) := by
        have hz := (Subgroup.mem_normalizer_iff''.mp hkinv x).mp hxP
        simpa only [inv_inv] using hz
      have hmem : y ∈ pCoreOf 2 (X.arcStab m r) ⊔ X.Q m := by
        have h := (pCoreOf 2 (X.arcStab m r) ⊔ X.Q m).mul_mem
          ((pCoreOf 2 (X.arcStab m r) ⊔ X.Q m).inv_mem (Subgroup.mem_sup_right hkq))
          (Subgroup.mem_sup_left hzP)
        rwa [show (k * x * k⁻¹ * y⁻¹)⁻¹ * (k * x * k⁻¹) = y by group] at h
      exact hmem
  have hsup_eq : pCoreOf 2 (X.arcStab m r) ⊔ X.Q m = X.edgeSylow m :=
    le_antisymm hsup_le hS_le_sup
  have hPtrans : ∀ a b : V, Γ.Adj (X.vert m) a → a ≠ X.vert (m + 1) →
      Γ.Adj (X.vert m) b → b ≠ X.vert (m + 1) →
      ∃ p ∈ pCoreOf 2 (X.arcStab m r), p • a = b := by
    intro a b ha hab hb hbb
    obtain ⟨s, hsS, hsb⟩ := X.edgeSylow_transitive_left m a b ha hab hb hbb
    have hPnormQ : pCoreOf 2 (X.arcStab m r) ≤ Subgroup.normalizer (X.Q m : Set G) :=
      hPle.trans ((X.arcStab_le_Gi_left hmr).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi m)))
    have hcoe : (↑(pCoreOf 2 (X.arcStab m r) ⊔ X.Q m) : Set G) =
        ↑(pCoreOf 2 (X.arcStab m r)) * ↑(X.Q m) :=
      Subgroup.coe_mul_of_left_le_normalizer_right
        (pCoreOf 2 (X.arcStab m r)) (X.Q m) hPnormQ
    have hs : s ∈ (↑(pCoreOf 2 (X.arcStab m r)) * ↑(X.Q m) : Set G) := by
      rw [← hcoe, hsup_eq]
      exact hsS
    obtain ⟨p, hpP, q, hqQ, hpq⟩ := hs
    have hpq' : p * q = s := hpq
    refine ⟨p, hpP, ?_⟩
    calc p • a = p • (q • a) := by rw [X.Q_fixes_neighbors_vert m a ha q hqQ]
      _ = (p * q) • a := (mul_smul p q a).symm
      _ = s • a := by rw [hpq']
      _ = b := hsb
  exact hsing (fun a b ha hab hb hbb => by
    obtain ⟨p, hpP, hpa⟩ := hPtrans a b ha hab hb hbb
    exact ⟨p, hPle hpP, hpa⟩)

theorem pCoreOf_arcStab_fixes_left (m r : ℤ) (hmr : m < r)
    (hsing : ¬ X.LeftTransAt m r) :
    ∀ a, Γ.Adj (X.vert m) a → ∀ g ∈ pCoreOf 2 (X.arcStab m r), g • a = a := by
  intro a ha g hg
  exact X.Q_fixes_neighbors_vert m a ha g (X.pCoreOf_arcStab_le_Q_left m r hmr hsing hg)

end Setup

end CFSG.Quasithin.St84
