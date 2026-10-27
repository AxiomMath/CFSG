module

public import CFSG.Quasithin.Background.SmithC27RJ

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {H R M K V : Subgroup G}

theorem commutator_mem_pCoreOf_of_normalizer (hs : StarHyp R K V) {c n : G}
    (hc : c ∈ (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G))
    (hcR : c ∈ Subgroup.normalizer (R : Set G)) (hn : n ∈ K ⊔ R)
    (hnR : n ∈ Subgroup.normalizer (R : Set G)) : c * n * c⁻¹ * n⁻¹ ∈ pCoreOf 2 (K ⊔ R) := by
  have hDK : (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G) ⊓ K ≤ oTwoZIn K := fun x hx =>
    hs.inf_centralizer_le ⟨hx.2, hx.1.2⟩
  have hck := commutator_mem_pCoreOf_of_inf_le hs.quasi le_sup_left hs.le_normalizer inf_le_left
    hs.le_normalizer_centralizer hDK c hc
  obtain ⟨k, hk, r, hr, rfl⟩ := hs.mem_sup.1 hn
  have hQX : K ⊔ R ≤ Subgroup.normalizer (pCoreOf 2 (K ⊔ R) : Set G) :=
    le_normalizer_pCoreOf 2 _
  have hkX : k ∈ K ⊔ R := Subgroup.mem_sup_left hk
  have hcr : c * r * c⁻¹ * r⁻¹ ∈ pCoreOf 2 (K ⊔ R) := by
    rw [hs.pCore_eq_inf]
    refine ⟨R.mul_mem ((Subgroup.mem_normalizer_iff.1 hcR r).1 hr) (R.inv_mem hr), ?_⟩
    have hrC : r * c⁻¹ * r⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
      C124.conj_mem_centralizer_of_le hs.R_le_normalizer_V hr
        (Subgroup.inv_mem _ hc.2)
    have e : c * r * c⁻¹ * r⁻¹ = c * (r * c⁻¹ * r⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hc.2 hrC
  have e : c * (k * r) * c⁻¹ * (k * r)⁻¹ =
      (c * k * c⁻¹ * k⁻¹) * (k * (c * r * c⁻¹ * r⁻¹) * k⁻¹) := by group
  rw [e]
  refine Subgroup.mul_mem _ (hs.pCore_K_le_pCore (hck k hk)) ?_
  exact (Subgroup.mem_normalizer_iff.1 (hQX hkX) _).1 hcr

theorem autOn_inf_normalizer_R (hs : StarHyp R K V) :
    autOn ((K ⊔ R) ⊓ Subgroup.normalizer (R : Set G)) V =
      autOn (K ⊔ R) V ⊓ Subgroup.normalizer (autOn R V : Set (MulAut ↥V)) := by
  refine le_antisymm (le_inf (autOn_mono' inf_le_left) (autOn_le_normalizer_autOn inf_le_right))
    ?_
  have hRC : IsSylowTwoOf (R ⊓ Subgroup.centralizer (V : Set G))
      ((K ⊔ R) ⊓ Subgroup.centralizer (V : Set G)) := by
    rw [← hs.pCore_eq_inf]
    exact hs.centralizer_isSylow
  exact autOn_inf_normalizer_le hs.le_normalizer_V le_sup_right hs.pgroup hRC

theorem pCore_autOn_inf_normalizer_R (hR : IsTwoRadicalIn (K ⊔ R) R) (hs : StarHyp R K V) :
    pCoreOf 2 (autOn (K ⊔ R) V ⊓ Subgroup.normalizer (autOn R V : Set (MulAut ↥V))) =
      autOn R V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← autOn_inf_normalizer_R hs]
  set Y : Subgroup G := (K ⊔ R) ⊓ Subgroup.normalizer (R : Set G) with hY
  set A := pCoreOf 2 (autOn Y V) with hA
  set N := Subgroup.normalizer (V : Set G) with hN
  set Phat : Subgroup G := ((A.comap (conjAct V)).map N.subtype) ⊓ Y with hPhat
  have hRY : R ≤ Y := le_inf le_sup_right Subgroup.le_normalizer
  refine le_antisymm ?_ (le_pCoreOf_of_le_normalizer 2 (autOn_mono' hRY)
    (autOn_le_normalizer_autOn inf_le_right) (isPGroup_autOn hs.pgroup))
  have hmem : ∀ {x : G}, x ∈ Phat ↔ x ∈ Y ∧ ∃ hx : x ∈ N, conjAct V ⟨x, hx⟩ ∈ A := by
    intro x
    constructor
    · rintro ⟨⟨n, hn, rfl⟩, hx⟩
      exact ⟨hx, n.2, hn⟩
    · rintro ⟨hx, hxN, hxA⟩
      exact ⟨⟨⟨x, hxN⟩, hxA, rfl⟩, hx⟩
  have hPY : Phat ≤ Y := inf_le_right
  have hYN : Y ≤ N := inf_le_left.trans hs.le_normalizer_V
  have hPN : Phat ≤ N := hPY.trans hYN
  have hYnorm : Y ≤ Subgroup.normalizer (Phat : Set G) := by
    intro y hy
    have hyN : y ∈ N := hYN hy
    have hyA : conjAct V ⟨y, hyN⟩ ∈ Subgroup.normalizer (A : Set (MulAut ↥V)) := by
      have h1 : conjAct V ⟨y, hyN⟩ ∈ Subgroup.normalizer (autOn Y V : Set (MulAut ↥V)) :=
        autOn_le_normalizer_autOn (Y := Y) (L := Y) Subgroup.le_normalizer
          (mem_autOn_iff'.2 ⟨_, hy, rfl⟩)
      exact normalizer_le_normalizer_pCoreOf 2 _ h1
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨hxY, hxN, hxA⟩ := hmem.1 hx
    refine hmem.2 ⟨Y.mul_mem (Y.mul_mem hy hxY) (Y.inv_mem hy),
      N.mul_mem (N.mul_mem hyN hxN) (N.inv_mem hyN), ?_⟩
    have e : (⟨y * x * y⁻¹, N.mul_mem (N.mul_mem hyN hxN) (N.inv_mem hyN)⟩ : ↥N) =
        ⟨y, hyN⟩ * ⟨x, hxN⟩ * ⟨y, hyN⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 hyA _).1 hxA
  have hQY : pCoreOf 2 (K ⊔ R) ≤ Y := hs.core.trans hRY
  have hQP : pCoreOf 2 (K ⊔ R) ≤ Phat := by
    intro x hx
    refine hmem.2 ⟨hQY hx, hYN (hQY hx), ?_⟩
    rw [(conjAct_eq_one_iff' _).2 (hs.pCore_le_centralizer hx)]
    exact A.one_mem
  obtain ⟨T₀, hT₀, -⟩ := A4.exists_isSylowTwoOf_ge (bot_le : (⊥ : Subgroup G) ≤ Phat)
    (IsPGroup.of_card (n := 0) (by simp))
  have hQT : pCoreOf 2 (K ⊔ R) ≤ T₀ := by
    have h1 : pCoreOf 2 (K ⊔ R) ≤ pCoreOf 2 Phat :=
      le_pCoreOf_of_le_normalizer 2 hQP
        ((hPY.trans inf_le_left).trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
    exact h1.trans (B6.pCoreOf_two_le_of_isSylowTwoOf hT₀)
  have hT₀C : IsSylowTwoOf (T₀ ⊓ Subgroup.centralizer (V : Set G))
      (Phat ⊓ Subgroup.centralizer (V : Set G)) := by
    have := A4.isSylowTwoOf_inf_normal hT₀ inf_le_left (le_normalizer_inf_centralizer' hPN)
    rwa [← inf_assoc, inf_eq_left.2 hT₀.1] at this
  have hsylstar : IsSylowTwoOf (autOn T₀ V) (autOn Phat V) :=
    (isSylowTwoOf_iff_autOn hPN hT₀.1 hT₀.2.1 hT₀C).1 hT₀
  have hPhatA : autOn Phat V = A := by
    apply le_antisymm
    · intro φ hφ
      obtain ⟨n, hn, rfl⟩ := mem_autOn_iff'.1 hφ
      obtain ⟨-, hnN, hnA⟩ := hmem.1 hn
      exact hnA
    · intro φ hφ
      have hφY : φ ∈ autOn Y V := pCoreOf_le 2 _ hφ
      obtain ⟨n, hn, rfl⟩ := mem_autOn_iff'.1 hφY
      exact mem_autOn_iff'.2 ⟨n, hmem.2 ⟨hn, n.2, hφ⟩, rfl⟩
  have hT₀A : autOn T₀ V = A := by
    rw [← hPhatA]
    refine le_antisymm (autOn_mono' hT₀.1) ?_
    have hA2 : IsPGroup 2 ↥(autOn Phat V) := by
      rw [hPhatA]
      exact pCoreOf_isPGroup 2 _
    obtain ⟨k, hk⟩ := hA2.index ((autOn T₀ V).subgroupOf (autOn Phat V))
    have hk0 : k = 0 := by
      by_contra hk0
      exact hsylstar.2.2 (hk ▸ dvd_pow_self 2 hk0)
    rw [hk0, pow_zero, Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top] at hk
    exact hk
  have hT₀n : Phat ≤ Subgroup.normalizer (T₀ : Set G) := by
    intro x hx
    obtain ⟨hxY, hxN, hxA⟩ := hmem.1 hx
    have hxT : conjAct V ⟨x, hxN⟩ ∈ autOn T₀ V := by
      rw [hT₀A]
      exact hxA
    obtain ⟨t, ht, hte⟩ := mem_autOn_iff'.1 hxT
    have htY : (t : G) ∈ Y := hPY (hT₀.1 ht)
    have hcY : (t : G)⁻¹ * x ∈ Y := Y.mul_mem (Y.inv_mem htY) hxY
    have hcC : (t : G)⁻¹ * x ∈ Subgroup.centralizer (V : Set G) := by
      have h2 : conjAct V (t⁻¹ * ⟨x, hxN⟩) = 1 := by rw [map_mul, map_inv, hte, inv_mul_cancel]
      exact (conjAct_eq_one_iff' _).1 h2
    have hzT : (t : G)⁻¹ * x ∈ Subgroup.normalizer (T₀ : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun s hs' => ?_
      have hsY : s ∈ Y := hPY (hT₀.1 hs')
      have hc := commutator_mem_pCoreOf_of_normalizer hs ⟨hcY.1, hcC⟩ hcY.2 hsY.1 hsY.2
      have e : ((t : G)⁻¹ * x) * s * ((t : G)⁻¹ * x)⁻¹ =
          (((t : G)⁻¹ * x) * s * ((t : G)⁻¹ * x)⁻¹ * s⁻¹) * s := by group
      rw [e]
      exact T₀.mul_mem (hQT hc) hs'
    have e : x = (t : G) * ((t : G)⁻¹ * x) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer ht) hzT
  have hT₀O : T₀ ≤ pCoreOf 2 Phat := le_pCoreOf_of_le_normalizer 2 hT₀.1 hT₀n hT₀.2.1
  have hOO : pCoreOf 2 Phat ≤ pCoreOf 2 Y :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans hPY)
      (hYnorm.trans (normalizer_le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  have hYR : pCoreOf 2 Y = R := hR.2.2.symm
  rw [← hT₀A]
  exact autOn_mono' ((hT₀O.trans hOO).trans hYR.le)

theorem le_autOn_R_of_le_normalizer (hR : IsTwoRadicalIn (K ⊔ R) R) (hs : StarHyp R K V)
    {Y : Subgroup (MulAut ↥V)} (hYX : Y ≤ autOn (K ⊔ R) V) (hY : IsPGroup 2 Y)
    (hN : autOn (K ⊔ R) V ⊓ Subgroup.normalizer (autOn R V : Set (MulAut ↥V)) ≤
      Subgroup.normalizer (Y : Set (MulAut ↥V))) : Y ≤ autOn R V := by
  by_cases hbot : autOn R V = ⊥
  · have hXY : autOn (K ⊔ R) V ≤ Subgroup.normalizer (Y : Set (MulAut ↥V)) := by
      intro x hx
      refine hN ⟨hx, ?_⟩
      rw [hbot]
      exact Subgroup.mem_normalizer_iff.2 fun g => by simp
    have h1 : Y ≤ pCoreOf 2 (autOn (K ⊔ R) V) := le_pCoreOf_of_le_normalizer 2 hYX hXY hY
    rw [hs.pCore_eq_bot] at h1
    exact h1.trans bot_le
  · exact le_of_isSignalizer_of_isTwoRadicalIn
      ⟨autOn_mono' le_sup_right, hbot, (pCore_autOn_inf_normalizer_R hR hs).symm⟩ ⟨hYX, hY, hN⟩

theorem autOn_K_inf_normalizer_R_le (h : Hyp27 H R M K) (hs : StarHyp R K V) :
    autOn K V ⊓ Subgroup.normalizer (autOn R V : Set (MulAut ↥V)) ≤ autOn (M ⊓ K) V := by
  rw [hs.autOn_inf_M h.R_le_M]
  refine fun x hx => ⟨?_, hx.1⟩
  have hx' : x ∈ autOn ((K ⊔ R) ⊓ Subgroup.normalizer (R : Set G)) V := by
    rw [autOn_inf_normalizer_R hs]
    exact ⟨autOn_mono' le_sup_left hx.1, hx.2⟩
  exact autOn_mono' (le_inf (sup_inf_normalizer_R_le h) inf_le_left) hx'

theorem not_isBorelIn_MK (h : Hyp27 H R M K) (hs : StarHyp R K V)
    (hnS : ¬ IsSylowTwoOf R (K ⊔ R)) : ¬ IsBorelIn (autOn K V) (autOn (M ⊓ K) V) := by
  rintro ⟨S', hS', hB⟩
  apply hnS
  refine isSylowTwoOf_R_of_sylow_le hs hS' ?_
  have h1 : S' ≤ pCoreOf 2 (autOn (M ⊓ K) V) := by
    rw [hB]
    exact le_pCoreOf_of_le_normalizer 2 (le_inf hS'.1 Subgroup.le_normalizer) inf_le_right
      hS'.2.1
  exact h1.trans (pCore_MK_star_le_R_star h hs)

theorem isParabolic2_MK_of_sylow (h : Hyp27 H R M K) (hs : StarHyp R K V)
    {T' : Subgroup (MulAut ↥V)} (hT' : IsSylowTwoOf T' (autOn (K ⊔ R) V))
    (hT'R : T' ≤ Subgroup.normalizer (autOn R V : Set (MulAut ↥V)))
    (hself : ∀ S : Subgroup (MulAut ↥V), IsSylowTwoOf S (autOn K V) →
      autOn K V ⊓ Subgroup.normalizer (S : Set (MulAut ↥V)) ≤ S) :
    IsParabolic2 (autOn K V) (autOn (M ⊓ K) V) := by
  have hS : IsSylowTwoOf (T' ⊓ autOn K V) (autOn K V) :=
    A4.isSylowTwoOf_inf_normal hT' (autOn_mono' le_sup_left) hs.normalizes
  refine ⟨autOn_mono' inf_le_right, T' ⊓ autOn K V, hS, (hself _ hS).trans ?_⟩
  exact (le_inf inf_le_right (inf_le_left.trans hT'R)).trans (autOn_K_inf_normalizer_R_le h hs)

end CFSG.Quasithin.SmithC27
