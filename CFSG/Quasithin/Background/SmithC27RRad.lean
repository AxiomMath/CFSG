module

public import CFSG.Quasithin.Background.SmithC27Frattini

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {H R M K V : Subgroup G}

theorem pCore_K_eq_inf (hs : StarHyp R K V) :
    R ⊓ K ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · have e : R ⊓ K ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 (K ⊔ R) ⊓ K := by
      rw [hs.pCore_eq_inf, inf_right_comm]
    rw [e]
    exact le_pCoreOf_of_le_normalizer 2 inf_le_right
      (fun k hk => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hk), Subgroup.le_normalizer hk⟩)
      ((pCoreOf_isPGroup 2 _).to_le inf_le_left)
  · exact le_inf (le_inf (hs.pCore_K_le_pCore.trans hs.core) (pCoreOf_le 2 K))
      hs.pCore_K_le_centralizer

theorem pCore_K_le_D (hs : StarHyp R K V) : pCoreOf 2 K ≤ R ⊓ K :=
  (pCore_K_eq_inf hs).symm.le.trans inf_le_left

theorem inf_centralizer_K_isSylow (hs : StarHyp R K V) :
    IsSylowTwoOf (pCoreOf 2 K) (K ⊓ Subgroup.centralizer (V : Set G)) := by
  have hN : K ⊓ Subgroup.centralizer (V : Set G) ≤
      (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G) := inf_le_inf_right _ le_sup_left
  have hn : (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G) ≤
      Subgroup.normalizer ((K ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
    fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hs.le_normalizer hx.1, A4.mem_normalizer_centralizer (hs.le_normalizer_V hx.1)⟩
  have h1 := A4.isSylowTwoOf_inf_normal hs.centralizer_isSylow hN hn
  have e : pCoreOf 2 (K ⊔ R) ⊓ (K ⊓ Subgroup.centralizer (V : Set G)) = pCoreOf 2 K := by
    rw [← pCore_K_eq_inf hs, hs.pCore_eq_inf]
    ext x
    simp only [Subgroup.mem_inf]
    tauto
  rwa [e] at h1

theorem pCore_autOn_le (hs : StarHyp R K V) {P : Subgroup G} (hPK : P ≤ K)
    (hO : pCoreOf 2 K ≤ P) : pCoreOf 2 (autOn P V) ≤ autOn (pCoreOf 2 P) V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := pCoreOf 2 (autOn P V) with hA
  set N := Subgroup.normalizer (V : Set G) with hN
  set Phat : Subgroup G := ((A.comap (conjAct V)).map N.subtype) ⊓ P with hPhat
  have hmem : ∀ {x : G}, x ∈ Phat ↔ x ∈ P ∧ ∃ hx : x ∈ N, conjAct V ⟨x, hx⟩ ∈ A := by
    intro x
    constructor
    · rintro ⟨⟨n, hn, rfl⟩, hx⟩
      exact ⟨hx, n.2, hn⟩
    · rintro ⟨hx, hxN, hxA⟩
      exact ⟨⟨⟨x, hxN⟩, hxA, rfl⟩, hx⟩
  have hPN : P ≤ N := hPK.trans hs.K_le_normalizer_V
  have hPhP : Phat ≤ P := inf_le_right
  have hPhN : Phat ≤ N := hPhP.trans hPN
  have hPnorm : P ≤ Subgroup.normalizer (Phat : Set G) := by
    intro y hy
    have hyN : y ∈ N := hPN hy
    have hyA : conjAct V ⟨y, hyN⟩ ∈ Subgroup.normalizer (A : Set (MulAut ↥V)) :=
      le_normalizer_pCoreOf 2 _ (mem_autOn_iff'.2 ⟨_, hy, rfl⟩)
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨hxP, hxN, hxA⟩ := hmem.1 hx
    refine hmem.2 ⟨P.mul_mem (P.mul_mem hy hxP) (P.inv_mem hy),
      N.mul_mem (N.mul_mem hyN hxN) (N.inv_mem hyN), ?_⟩
    have e : (⟨y * x * y⁻¹, N.mul_mem (N.mul_mem hyN hxN) (N.inv_mem hyN)⟩ : ↥N) =
        ⟨y, hyN⟩ * ⟨x, hxN⟩ * ⟨y, hyN⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 hyA _).1 hxA
  have hOPh : pCoreOf 2 K ≤ Phat := by
    intro x hx
    have hxK : x ∈ K := pCoreOf_le 2 K hx
    refine hmem.2 ⟨hO hx, hs.K_le_normalizer_V hxK, ?_⟩
    rw [(conjAct_eq_one_iff' _).2 (hs.pCore_K_le_centralizer hx)]
    exact A.one_mem
  obtain ⟨T₀, hT₀, -⟩ := A4.exists_isSylowTwoOf_ge (bot_le : (⊥ : Subgroup G) ≤ Phat)
    (IsPGroup.of_card (n := 0) (by simp))
  have hOT : pCoreOf 2 K ≤ T₀ := by
    have h1 : pCoreOf 2 K ≤ pCoreOf 2 Phat :=
      le_pCoreOf_of_le_normalizer 2 hOPh ((hPhP.trans hPK).trans (le_normalizer_pCoreOf 2 K))
        (pCoreOf_isPGroup 2 K)
    exact h1.trans (B6.pCoreOf_two_le_of_isSylowTwoOf hT₀)
  have hT₀C : IsSylowTwoOf (T₀ ⊓ Subgroup.centralizer (V : Set G))
      (Phat ⊓ Subgroup.centralizer (V : Set G)) := by
    have := A4.isSylowTwoOf_inf_normal hT₀ inf_le_left (le_normalizer_inf_centralizer' hPhN)
    rwa [← inf_assoc, inf_eq_left.2 hT₀.1] at this
  have hsylstar : IsSylowTwoOf (autOn T₀ V) (autOn Phat V) :=
    (isSylowTwoOf_iff_autOn hPhN hT₀.1 hT₀.2.1 hT₀C).1 hT₀
  have hPhatA : autOn Phat V = A := by
    apply le_antisymm
    · intro φ hφ
      obtain ⟨n, hn, rfl⟩ := mem_autOn_iff'.1 hφ
      obtain ⟨-, hnN, hnA⟩ := hmem.1 hn
      exact hnA
    · intro φ hφ
      have hφP : φ ∈ autOn P V := pCoreOf_le 2 _ hφ
      obtain ⟨n, hn, rfl⟩ := mem_autOn_iff'.1 hφP
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
    obtain ⟨hxP, hxN, hxA⟩ := hmem.1 hx
    have hxT : conjAct V ⟨x, hxN⟩ ∈ autOn T₀ V := by
      rw [hT₀A]
      exact hxA
    obtain ⟨t, ht, hte⟩ := mem_autOn_iff'.1 hxT
    have hz : (t : G)⁻¹ * x ∈ oTwoZIn K := by
      refine hs.inf_centralizer_le ⟨K.mul_mem (K.inv_mem (hPK (hPhP (hT₀.1 ht)))) (hPK hxP), ?_⟩
      have h2 : conjAct V (t⁻¹ * ⟨x, hxN⟩) = 1 := by rw [map_mul, map_inv, hte, inv_mul_cancel]
      exact (conjAct_eq_one_iff' _).1 h2
    have hzT : (t : G)⁻¹ * x ∈ Subgroup.normalizer (T₀ : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun s hs' => ?_
      have hc := commutator_mem_pCore_of_mem_oTwoZIn hz (hPK (hPhP (hT₀.1 hs')))
      have e : ((t : G)⁻¹ * x) * s * ((t : G)⁻¹ * x)⁻¹ =
          (((t : G)⁻¹ * x) * s * ((t : G)⁻¹ * x)⁻¹ * s⁻¹) * s := by group
      rw [e]
      exact T₀.mul_mem (hOT hc) hs'
    have e : x = (t : G) * ((t : G)⁻¹ * x) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer ht) hzT
  have hT₀O : T₀ ≤ pCoreOf 2 Phat := le_pCoreOf_of_le_normalizer 2 hT₀.1 hT₀n hT₀.2.1
  have hOO : pCoreOf 2 Phat ≤ pCoreOf 2 P :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans hPhP)
      (hPnorm.trans (normalizer_le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  rw [← hT₀A]
  exact autOn_mono' (hT₀O.trans hOO)

omit [Finite G] in
theorem mem_normalizer_normalizer {D : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (D : Set G)) :
    n ∈ Subgroup.normalizer ((Subgroup.normalizer (D : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro m
  refine ⟨fun hm => Subgroup.mul_mem _ (Subgroup.mul_mem _ hn hm) (Subgroup.inv_mem _ hn),
    fun hm => ?_⟩
  have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hn) hm) hn
  simpa [mul_assoc] using this

theorem pCore_inf_normalizer_D (h : Hyp27 H R M K) :
    pCoreOf 2 (K ⊓ Subgroup.normalizer ((R ⊓ K : Subgroup G) : Set G)) = R ⊓ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup G := K ⊓ Subgroup.normalizer ((R ⊓ K : Subgroup G) : Set G) with hP
  apply le_antisymm
  · refine le_inf ?_ ((pCoreOf_le 2 P).trans inf_le_left)
    refine le_of_isSignalizer_of_isTwoRadicalIn h.isTwoRadicalIn_sup
      ⟨(pCoreOf_le 2 P).trans (inf_le_left.trans le_sup_left), pCoreOf_isPGroup 2 P, ?_⟩
    intro n hn
    have hnK : n ∈ Subgroup.normalizer (K : Set G) := h.sup_le_normalizer hn.1
    have hnD : n ∈ Subgroup.normalizer ((R ⊓ K : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hn.2, hnK⟩
    have hnP : n ∈ Subgroup.normalizer (P : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hnK, mem_normalizer_normalizer hnD⟩
    exact normalizer_le_normalizer_pCoreOf 2 P hnP
  · exact le_pCoreOf_of_le_normalizer 2 (le_inf inf_le_right Subgroup.le_normalizer)
      inf_le_right (h.isPGroup.to_le inf_le_left)

theorem autOn_inf_normalizer_D (hs : StarHyp R K V) :
    autOn (K ⊓ Subgroup.normalizer ((R ⊓ K : Subgroup G) : Set G)) V =
      autOn K V ⊓ Subgroup.normalizer (autOn (R ⊓ K) V : Set (MulAut ↥V)) := by
  refine le_antisymm (le_inf (autOn_mono' inf_le_left) (autOn_le_normalizer_autOn inf_le_right))
    ?_
  have hsyl : IsSylowTwoOf ((R ⊓ K) ⊓ Subgroup.centralizer (V : Set G))
      (K ⊓ Subgroup.centralizer (V : Set G)) := by
    rw [pCore_K_eq_inf hs]
    exact inf_centralizer_K_isSylow hs
  exact autOn_inf_normalizer_le hs.K_le_normalizer_V inf_le_right
    (hs.pgroup.to_le inf_le_left) hsyl

theorem pCore_autOn_inf_normalizer_D (h : Hyp27 H R M K) (hs : StarHyp R K V) :
    pCoreOf 2 (autOn K V ⊓ Subgroup.normalizer (autOn (R ⊓ K) V : Set (MulAut ↥V))) =
      autOn (R ⊓ K) V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← autOn_inf_normalizer_D hs]
  have hDP : R ⊓ K ≤ K ⊓ Subgroup.normalizer ((R ⊓ K : Subgroup G) : Set G) :=
    le_inf inf_le_right Subgroup.le_normalizer
  apply le_antisymm
  · have h1 := pCore_autOn_le hs (P := K ⊓ Subgroup.normalizer ((R ⊓ K : Subgroup G) : Set G))
      inf_le_left ((pCore_K_le_D hs).trans hDP)
    rwa [pCore_inf_normalizer_D h] at h1
  · exact le_pCoreOf_of_le_normalizer 2 (autOn_mono' hDP)
      (autOn_le_normalizer_autOn inf_le_right)
      (isPGroup_autOn (h.isPGroup.to_le inf_le_left))

end CFSG.Quasithin.SmithC27
