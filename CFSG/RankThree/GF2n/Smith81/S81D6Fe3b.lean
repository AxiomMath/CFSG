module

public import CFSG.RankThree.GF2n.Smith81.S81D6Basic
public import CFSG.RankThree.GF2n.Smith81.S81E7Roots

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CFSG.RankThree.GF2n.Smith81.E7Model CFSG.LieType.Steinberg.Minuscule
  CFSG.Blueprint.Chevalley

variable {K : Type} [Field K]

private theorem fe3b_height_le_of_perp {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β)
    (h0 : β node1 = 0) :
    CFSG.Blueprint.Chevalley.height (τ := .E7) β ≤
      CFSG.Blueprint.Chevalley.height (τ := .E7) theta4 := by
  revert h0
  refine (forall_isRoot_iff (fun β : Fin (Tag.rank .E7) → ℤ => β node1 = 0 →
    CFSG.Blueprint.Chevalley.height (τ := .E7) β ≤
      CFSG.Blueprint.Chevalley.height (τ := .E7) theta4)).2 ?_ β hβ
  decide +kernel

private theorem fe3b_height_theta4 : CFSG.Blueprint.Chevalley.height (τ := .E7) theta4 = 9 := by
  decide +kernel

theorem not_isRoot_add_theta4 {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) (h0 : γ ∈ Perp)
    (hpos : 0 < CFSG.Blueprint.Chevalley.height (τ := .E7) γ) :
    ¬ IsRoot .E7 (γ + theta4) ∧ γ + theta4 ≠ 0 := by
  have hγ0 : γ node1 = 0 := (perp_iff.1 h0).2
  have hsum : CFSG.Blueprint.Chevalley.height (τ := .E7) (γ + theta4)
      = CFSG.Blueprint.Chevalley.height (τ := .E7) γ
        + CFSG.Blueprint.Chevalley.height (τ := .E7) theta4 := by
    simp [CFSG.Blueprint.Chevalley.height, Finset.sum_add_distrib]
  have h4 := fe3b_height_theta4
  have hpe : (γ + theta4) node1 = 0 := by
    have h4n : theta4 node1 = 0 := by decide
    rw [Pi.add_apply, hγ0, h4n, add_zero]
  constructor
  · intro hroot
    have hle := fe3b_height_le_of_perp hroot hpe
    omega
  · intro h00
    have h0' : CFSG.Blueprint.Chevalley.height (τ := .E7) (γ + theta4) = 0 := by
      rw [h00]
      simp [CFSG.Blueprint.Chevalley.height]
    omega

theorem UL_le_E [CharP K 2] : UL K ≤ EGrp K := by
  rw [UL, Subgroup.closure_le]
  rintro g ⟨β, -, -, -, c, rfl⟩
  exact e7Data_valid.xu_mem K β c

theorem UL_comm_xu_theta4 [CharP K 2] {u : (Module.End K (V K))ˣ} (hu : u ∈ UL K) (d : K) :
    u * e7Data_valid.xu K theta4 d = e7Data_valid.xu K theta4 d * u := by
  have key : UL K ≤ Subgroup.centralizer {e7Data_valid.xu K theta4 d} := by
    rw [UL, Subgroup.closure_le]
    rintro g ⟨β, hβ, hzero, hpos, c, rfl⟩
    refine Subgroup.mem_centralizer_iff.2 ?_
    rintro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    obtain ⟨hnot, hne⟩ := not_isRoot_add_theta4 hβ ⟨hβ, hzero⟩ hpos
    have hcomm := (e7Data_valid.commutator_xm K hβ isRoot_theta4 hne).2 hnot c d
    rw [commutatorElement_eq_one_iff_mul_comm] at hcomm
    exact (congrArg Subtype.val hcomm).symm
  exact (Subgroup.mem_centralizer_iff.1 (key hu) _ (Set.mem_singleton _)).symm

@[expose] def BorL (K : Type) [Field K] : Subgroup ↥(e7Data_valid.minGroup K) :=
  Tor K ⊔ (UL K).comap (e7Data_valid.minGroup K).subtype

private theorem fe3b_tor_conj_mem_UL_end {t : ↥(e7Data_valid.minGroup K)} (ht : t ∈ Tor K) :
    ∀ g ∈ UL K, (t : (Module.End K (V K))ˣ) * g * (t : (Module.End K (V K))ˣ)⁻¹ ∈ UL K := by
  intro g hg
  have key : UL K ≤ (UL K).comap (MulAut.conj (t : (Module.End K (V K))ˣ)).toMonoidHom := by
    rw [UL, Subgroup.closure_le]
    rintro g' ⟨β, hβ, hzero, hpos, c, rfl⟩
    obtain ⟨s, -, hs⟩ := tor_conj_xm ht hβ
    have hc : (t : (Module.End K (V K))ˣ) * e7Data_valid.xu K β c *
        (t : (Module.End K (V K))ˣ)⁻¹ = e7Data_valid.xu K β (s * c) :=
      congrArg Subtype.val (hs c)
    have hmem : e7Data_valid.xu K β (s * c) ∈ UL K :=
      Subgroup.subset_closure ⟨β, hβ, hzero, hpos, s * c, rfl⟩
    show (t : (Module.End K (V K))ˣ) * e7Data_valid.xu K β c *
        (t : (Module.End K (V K))ˣ)⁻¹ ∈ UL K
    rw [hc]
    exact hmem
  exact key hg

private theorem fe3b_tor_conj_mem_comap {t : ↥(e7Data_valid.minGroup K)} (ht : t ∈ Tor K)
    {h : ↥(e7Data_valid.minGroup K)} (hh : h ∈ (UL K).comap (e7Data_valid.minGroup K).subtype) :
    t * h * t⁻¹ ∈ (UL K).comap (e7Data_valid.minGroup K).subtype :=
  fe3b_tor_conj_mem_UL_end ht _ (Subgroup.mem_comap.1 hh)

private theorem fe3b_tor_mem_normalizer {t : ↥(e7Data_valid.minGroup K)} (ht : t ∈ Tor K) :
    t ∈ Subgroup.normalizer ((UL K).comap (e7Data_valid.minGroup K).subtype) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact fun hh => fe3b_tor_conj_mem_comap ht hh
  · intro hh
    have := fe3b_tor_conj_mem_comap (inv_mem ht) hh
    simpa [mul_assoc] using this

theorem mem_BorL_iff [CharP K 2] {b : ↥(e7Data_valid.minGroup K)} :
    b ∈ BorL K ↔
      ∃ u ∈ (UL K).comap (e7Data_valid.minGroup K).subtype, ∃ t ∈ Tor K, b = u * t := by
  have hle : Tor K ≤ Subgroup.normalizer ((UL K).comap (e7Data_valid.minGroup K).subtype) :=
    fun t ht => fe3b_tor_mem_normalizer ht
  rw [BorL, sup_comm, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hle,
    Set.mem_mul]
  exact ⟨fun ⟨u, hu, t, ht, h⟩ => ⟨u, hu, t, ht, h.symm⟩,
    fun ⟨u, hu, t, ht, h⟩ => ⟨u, hu, t, ht, h.symm⟩⟩

theorem borL_conj_xm_theta4 [CharP K 2] {b : ↥(e7Data_valid.minGroup K)} (hb : b ∈ BorL K)
    (c : K) :
    ∃ c' : K, b * e7Data_valid.xm K theta4 c * b⁻¹ = e7Data_valid.xm K theta4 c' ∧
      (c ≠ 0 → c' ≠ 0) := by
  obtain ⟨u, hu, t, htor, rfl⟩ := (mem_BorL_iff).1 hb
  obtain ⟨s, hs, hts⟩ := tor_conj_xm htor isRoot_theta4
  refine ⟨s * c, ?_, fun hc => mul_ne_zero hs hc⟩
  have hcomm : u * e7Data_valid.xm K theta4 (s * c) = e7Data_valid.xm K theta4 (s * c) * u :=
    Subtype.ext (UL_comm_xu_theta4 (Subgroup.mem_comap.1 hu) (s * c))
  calc u * t * e7Data_valid.xm K theta4 c * (u * t)⁻¹
      = u * (t * e7Data_valid.xm K theta4 c * t⁻¹) * u⁻¹ := by group
    _ = u * e7Data_valid.xm K theta4 (s * c) * u⁻¹ := by rw [hts c]
    _ = e7Data_valid.xm K theta4 (s * c) := by
        rw [mul_inv_eq_iff_eq_mul]
        exact hcomm

theorem tor_conj_xm_theta4 {t : ↥(e7Data_valid.minGroup K)} (htor : t ∈ Tor K) :
    ∃ s : K, s ≠ 0 ∧ ∀ c : K,
      t * e7Data_valid.xm K theta4 c * t⁻¹ = e7Data_valid.xm K theta4 (s * c) :=
  tor_conj_xm htor isRoot_theta4

theorem nW_conj_xm_theta4 (w : W7 K) (c : K) :
    ∃ (γ' : Fin (Tag.rank .E7) → ℤ) (c' : K), IsRoot .E7 γ' ∧
      nW K w * e7Data_valid.xm K theta4 c * (nW K w)⁻¹ = e7Data_valid.xm K γ' c' ∧
      (c ≠ 0 → c' ≠ 0) := by
  have hθ : theta4 ∈ (e7Datum K).roots :=
    (e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 K).2 isRoot_theta4
  have hact : ((e7Datum K).rootGroup theta4).map (MulAut.conj (nW K w)).toMonoidHom
      = _ := CFSG.LieType.Steinberg.actsAs_nrep (e7Datum_isCTGroupDatum K) w theta4 hθ
  have hmem : nW K w * e7Data_valid.xm K theta4 c * (nW K w)⁻¹ ∈
      ((e7Datum K).rootGroup theta4).map (MulAut.conj (nW K w)).toMonoidHom :=
    Subgroup.mem_map_of_mem (MulAut.conj (nW K w)).toMonoidHom
      (e7Data_valid.xm_mem_rootGroup K theta4 c)
  rw [hact] at hmem
  obtain ⟨c', hc'⟩ := (e7Data_valid.mem_rootGroup K).1 hmem
  have hγ' := (e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 K).1
    (CFSG.LieType.CurtisTits.weylAction_mem_roots hθ w)
  refine ⟨_, c', hγ', hc'.symm, fun hc hc0 => hc ?_⟩
  subst hc0
  rw [e7Data_valid.xm_zero] at hc'
  have h1 : e7Data_valid.xm K theta4 c = 1 := by
    calc e7Data_valid.xm K theta4 c
        = (nW K w)⁻¹ * (nW K w * e7Data_valid.xm K theta4 c * (nW K w)⁻¹) * nW K w := by group
      _ = (nW K w)⁻¹ * 1 * nW K w := by rw [← hc']
      _ = 1 := by group
  exact e7Data_valid.xm_injective K isRoot_theta4 (h1.trans (e7Data_valid.xm_zero K theta4).symm)

end CFSG.RankThree.GF2n.Smith81.D6Spin
