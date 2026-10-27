module

public import CFSG.Quasithin.EmptyFaithful.S143Q8Aux
public import CFSG.Quasithin.EmptyFaithful.S143Setting
public import CFSG.Quasithin.Vol2.Ch12Sec8Four

public section

namespace CFSG.Quasithin

namespace S143

variable {G : Type*} [Group G] {U : Subgroup G}

theorem Q8SqData.nonempty_of_isQ8Sq {P : Type*} [Group P] (h : IsQ8Sq P) :
    Nonempty (Q8SqData P) := by
  obtain ⟨hcard, A, B, ⟨hcomm, hsup⟩, ⟨eA⟩, ⟨eB⟩⟩ := h
  exact ⟨⟨A, B, hcomm, hsup, eA, eB, hcard⟩⟩

theorem mem_centerOf_iff_mem_center {x : G} :
    x ∈ centerOf U ↔ ∃ hx : x ∈ U, (⟨x, hx⟩ : ↥U) ∈ Subgroup.center ↥U := by
  constructor
  · rintro ⟨hxU, hxc⟩
    exact ⟨hxU, Subgroup.mem_center_iff.mpr fun g =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hxc g g.2)⟩
  · rintro ⟨hxU, hxc⟩
    exact ⟨hxU, Subgroup.mem_centralizer_iff.mpr fun g hg =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hxc ⟨g, hg⟩)⟩

theorem centerOf_eq_map_center_subtype (U : Subgroup G) :
    centerOf U = (Subgroup.center ↥U).map U.subtype := by
  ext x
  rw [mem_centerOf_iff_mem_center, Subgroup.mem_map]
  constructor
  · rintro ⟨hx, hc⟩
    exact ⟨⟨x, hx⟩, hc, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩

theorem isQ8Sq_card_centerOf (h : IsQ8Sq ↥U) : Nat.card ↥(centerOf U) = 2 := by
  obtain ⟨d⟩ := Q8SqData.nonempty_of_isQ8Sq h
  rw [centerOf_eq_map_center_subtype, Subgroup.card_subtype]
  exact d.card_center

theorem isQ8Sq_comm_mem_centerOf (h : IsQ8Sq ↥U) :
    ∀ x ∈ U, ∀ y ∈ U, x * y * x⁻¹ * y⁻¹ ∈ centerOf U := by
  intro x hx y hy
  obtain ⟨d⟩ := Q8SqData.nonempty_of_isQ8Sq h
  exact mem_centerOf_iff_mem_center.mpr
    ⟨U.mul_mem (U.mul_mem (U.mul_mem hx hy) (U.inv_mem hx)) (U.inv_mem hy),
      d.commutator_mem_center ⟨x, hx⟩ ⟨y, hy⟩⟩

theorem isQ8Sq_exists_inner (h : IsQ8Sq ↥U) :
    ∀ q ∈ Subgroup.normalizer (U : Set G), (∀ u ∈ U, q * u * q⁻¹ * u⁻¹ ∈ centerOf U) →
      ∃ w ∈ U, ∀ u ∈ U, q * u * q⁻¹ = w * u * w⁻¹ := by
  intro q hq hcomm
  obtain ⟨d⟩ := Q8SqData.nonempty_of_isQ8Sq h
  have hqU : ∀ u ∈ U, q * u * q⁻¹ ∈ U := fun u hu => (Subgroup.mem_normalizer_iff.mp hq u).mp hu
  let φ : ↥U →* ↥U :=
    { toFun := fun u => ⟨q * u * q⁻¹, hqU u u.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hφ : ∀ u : ↥U, φ u * u⁻¹ ∈ Subgroup.center ↥U := fun u => by
    obtain ⟨_, hz⟩ := mem_centerOf_iff_mem_center.mp (hcomm u u.2)
    exact hz
  obtain ⟨w, hw⟩ := exists_inner_of_gens d.card d.card_center d.commutator_mem_center d.gens
    d.closure_gens φ hφ
  exact ⟨w, w.2, fun u hu => congrArg Subtype.val (hw ⟨u, hu⟩)⟩

theorem isQ8Sq_card_centralizer (h : IsQ8Sq ↥U) :
    ∀ v ∈ U, v ∉ centerOf U →
      Nat.card ↥(U ⊓ Subgroup.centralizer ({v} : Set G)) = 16 := by
  intro v hv hvc
  obtain ⟨d⟩ := Q8SqData.nonempty_of_isQ8Sq h
  have hvZ : (⟨v, hv⟩ : ↥U) ∉ Subgroup.center ↥U := fun hz => hvc (mem_centerOf_iff_mem_center.mpr ⟨hv, hz⟩)
  have heq : U ⊓ Subgroup.centralizer ({v} : Set G) =
      (Subgroup.centralizer ({⟨v, hv⟩} : Set ↥U)).map U.subtype := by
    ext x
    rw [Subgroup.mem_inf, Subgroup.mem_map]
    constructor
    · rintro ⟨hxU, hx⟩
      refine ⟨⟨x, hxU⟩, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hx)
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)
  rw [heq, Subgroup.card_subtype]
  exact card_centralizer_of_not_mem_center d.card d.card_center d.commutator_mem_center hvZ

end S143

open CFSG.Open CFSG.LieType.BorelTits in
theorem lemma_14_3_19_one {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G}
    (c : S143.Counter T M g) : S143.Concl19a T M := by
  have h := c.h1281
  have hNH : Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) = mcOf T :=
    le_antisymm (normalizer_le_centralizer_of_card_two h.card_omegaOneCenter)
      (Subgroup.centralizer_le_normalizer _)
  have hH : IsHz T M (yOfL22 T M) (mcOf T) := hNH ▸ h.isHz_normalizer
  have hA := h.almostSpecialHyp hH
  have h4 : centralizerMod (quasithinOmegaOneCenter T) (mcOf T) (uOfL22 T M) =
      pCoreOf 2 (mcOf T) := h.lemma_12_8_4_four hH
  have hcc := hA.conjClosure_le_N
  have hU := hA.G22_one.2
  have hUQ : ∀ u ∈ uOfL22 T M, u ∈ pCoreOf 2 (mcOf T) := fun u hu => by
    have hQ : tmk (quasithinOmegaOneCenter T) ⟨u, hcc hu⟩ ∈
        tildeOf (quasithinOmegaOneCenter T) (pCoreOf 2 (mcOf T)) :=
      omegaOneCenterOf_le _ ((secImg_le_iff.1 hU) ⟨u, hcc hu⟩ hu)
    exact (secMk_mem_secImg_iff hA.V₁_le_pCoreOf).1 hQ
  have hUH : ∀ u ∈ uOfL22 T M, u ∈ mcOf T := fun u hu => pCoreOf_le 2 _ (hUQ u hu)
  have hZU : ∀ z ∈ quasithinOmegaOneCenter T, z ∈ centerOf (uOfL22 T M) := fun z hz =>
    ⟨le_conjClosure _ _ (le_conjClosure _ _ hz), Subgroup.mem_centralizer_iff.mpr fun u hu =>
      ((Subgroup.mem_centralizer_iff.mp (hUH u hu)) z hz).symm⟩
  refine ⟨le_antisymm (fun q hq => ?_) (sup_le (fun u hu => hUQ u hu) inf_le_left)⟩
  have hqH : q ∈ mcOf T := pCoreOf_le 2 _ hq
  have hqN : q ∈ Subgroup.normalizer (uOfL22 T M : Set G) := le_normalizer_conjClosure _ _ hqH
  have hqM : q ∈ centralizerMod (quasithinOmegaOneCenter T) (mcOf T) (uOfL22 T M) := by
    rw [h4]
    exact hq
  have hqC : ∀ u ∈ uOfL22 T M, q * u * q⁻¹ * u⁻¹ ∈ centerOf (uOfL22 T M) := fun u hu =>
    hZU _ ((mem_centralizerMod.mp hqM).2.2 u hu)
  obtain ⟨w, hwU, hw⟩ := S143.isQ8Sq_exists_inner c.c15.q8sq q hqN hqC
  have hdQ : w⁻¹ * q ∈ pCoreOf 2 (mcOf T) :=
    (pCoreOf 2 (mcOf T)).mul_mem ((pCoreOf 2 (mcOf T)).inv_mem (hUQ w hwU)) hq
  have hdC : w⁻¹ * q ∈ Subgroup.centralizer (uOfL22 T M : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h1 : q * u * q⁻¹ = w * u * w⁻¹ := hw u hu
    calc u * (w⁻¹ * q) = w⁻¹ * (w * u * w⁻¹) * q := by group
      _ = w⁻¹ * (q * u * q⁻¹) * q := by rw [h1]
      _ = w⁻¹ * q * u := by group
  have hmem : w * (w⁻¹ * q) ∈ uOfL22 T M ⊔ S143.dOf T M :=
    Subgroup.mul_mem_sup hwU ⟨hdQ, hdC⟩
  simpa using hmem

end CFSG.Quasithin
