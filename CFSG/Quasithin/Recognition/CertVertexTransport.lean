module

public import CFSG.Quasithin.EmptyFaithful.S1422LocTitsDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Hypotheses

public noncomputable section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

section Fwd

variable {G G' : Type*} [Group G] [Group G'] {H : Subgroup G} {H' : Subgroup G'}

open Classical in
@[expose] def vFwd (φ : ↥H ≃* ↥H') (x : G) : G' :=
  if hx : x ∈ H then ((φ ⟨x, hx⟩ : ↥H') : G') else 1

variable (φ : ↥H ≃* ↥H')

theorem vFwd_of_mem {x : G} (hx : x ∈ H) : vFwd φ x = ((φ ⟨x, hx⟩ : ↥H') : G') := by
  simp only [vFwd, hx, dite_true]

theorem vFwd_mem {x : G} (hx : x ∈ H) : vFwd φ x ∈ H' := by
  rw [vFwd_of_mem φ hx]
  exact (φ ⟨x, hx⟩).2

theorem vFwd_mul {x y : G} (hx : x ∈ H) (hy : y ∈ H) : vFwd φ (x * y) = vFwd φ x * vFwd φ y := by
  rw [vFwd_of_mem φ (H.mul_mem hx hy), vFwd_of_mem φ hx, vFwd_of_mem φ hy]
  exact congrArg (fun z : ↥H' => (z : G')) (φ.map_mul ⟨x, hx⟩ ⟨y, hy⟩)

theorem vFwd_one : vFwd φ (1 : G) = 1 := by
  rw [vFwd_of_mem φ H.one_mem]
  exact congrArg (fun z : ↥H' => (z : G')) (φ.map_one)

theorem vFwd_inv {x : G} (hx : x ∈ H) : vFwd φ x⁻¹ = (vFwd φ x)⁻¹ := by
  rw [vFwd_of_mem φ (H.inv_mem hx), vFwd_of_mem φ hx]
  exact congrArg (fun z : ↥H' => (z : G')) (φ.map_inv ⟨x, hx⟩)

theorem vFwd_comm {x y : G} (hx : x ∈ H) (hy : y ∈ H) :
    vFwd φ (x * y * x⁻¹ * y⁻¹) = vFwd φ x * vFwd φ y * (vFwd φ x)⁻¹ * (vFwd φ y)⁻¹ := by
  rw [vFwd_mul φ (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy),
    vFwd_mul φ (H.mul_mem hx hy) (H.inv_mem hx), vFwd_mul φ hx hy, vFwd_inv φ hx, vFwd_inv φ hy]

theorem vFwd_inj {x y : G} (hx : x ∈ H) (hy : y ∈ H) (h : vFwd φ x = vFwd φ y) : x = y := by
  rw [vFwd_of_mem φ hx, vFwd_of_mem φ hy] at h
  have := φ.injective (Subtype.ext h)
  exact congrArg (fun z : ↥H => (z : G)) this

theorem vFwd_surj {y : G'} (hy : y ∈ H') : ∃ x ∈ H, vFwd φ x = y := by
  refine ⟨((φ.symm ⟨y, hy⟩ : ↥H) : G), (φ.symm ⟨y, hy⟩).2, ?_⟩
  rw [vFwd_of_mem φ (φ.symm ⟨y, hy⟩).2]
  simp

theorem vFwd_symm {x : G} (hx : x ∈ H) : vFwd φ.symm (vFwd φ x) = x := by
  have hm : vFwd φ x ∈ H' := vFwd_mem φ hx
  rw [vFwd_of_mem φ.symm hm]
  have : (⟨vFwd φ x, hm⟩ : ↥H') = φ ⟨x, hx⟩ := Subtype.ext (vFwd_of_mem φ hx)
  rw [this, MulEquiv.symm_apply_apply]

end Fwd

section Pull

variable {G G' : Type*} [Group G] [Group G'] {H : Subgroup G} {H' : Subgroup G'}
  (φ : ↥H ≃* ↥H')

theorem vFwd_pow {x : G} (hx : x ∈ H) (n : ℕ) : vFwd φ (x ^ n) = (vFwd φ x) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, vFwd_one]
  | succ n ih => rw [pow_succ, pow_succ, vFwd_mul φ (H.pow_mem hx n) hx, ih]

@[expose] def vPull (K' : Subgroup G') : Subgroup G where
  carrier := {x | x ∈ H ∧ vFwd φ x ∈ K'}
  mul_mem' := fun {a b} ha hb =>
    ⟨H.mul_mem ha.1 hb.1, by rw [vFwd_mul φ ha.1 hb.1]; exact K'.mul_mem ha.2 hb.2⟩
  one_mem' := ⟨H.one_mem, by rw [vFwd_one]; exact K'.one_mem⟩
  inv_mem' := fun {a} ha =>
    ⟨H.inv_mem ha.1, by rw [vFwd_inv φ ha.1]; exact K'.inv_mem ha.2⟩

theorem vPull_le {K' : Subgroup G'} : vPull φ K' ≤ H := fun _ hx => hx.1

theorem mem_pCoreOf_iff {x : G} :
    x ∈ pCoreOf 2 H ↔ ∃ hx : x ∈ H, (⟨x, hx⟩ : ↥H) ∈ Open.pCore 2 ↥H := by
  unfold pCoreOf
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨⟨x, hx⟩, hy, rfl⟩

theorem vFwd_pCoreOf {x : G} (hx : x ∈ H) : x ∈ pCoreOf 2 H ↔ vFwd φ x ∈ pCoreOf 2 H' := by
  have e := map_pCore_mulEquiv 2 φ
  rw [mem_pCoreOf_iff, mem_pCoreOf_iff]
  have hm := vFwd_mem φ hx
  have hφ : (⟨vFwd φ x, hm⟩ : ↥H') = φ ⟨x, hx⟩ := Subtype.ext (vFwd_of_mem φ hx)
  constructor
  · rintro ⟨_, h⟩
    refine ⟨hm, ?_⟩
    rw [hφ, ← e]
    exact Subgroup.mem_map_of_mem _ h
  · rintro ⟨_, h⟩
    refine ⟨hx, ?_⟩
    rw [hφ, ← e, Subgroup.mem_map_equiv] at h
    simpa using h

theorem exists_pCore_preimage {y : G'} (hy : y ∈ pCoreOf 2 H') :
    ∃ x ∈ pCoreOf 2 H, vFwd φ x = y := by
  obtain ⟨x, hxH, rfl⟩ := vFwd_surj φ (pCoreOf_le 2 H' hy)
  exact ⟨x, (vFwd_pCoreOf φ hxH).2 hy, rfl⟩

theorem vFwd_Z {L2 : Subgroup G} {L2' : Subgroup G'}
    (hT : ((H ⊓ L2).subgroupOf H).map φ.toMonoidHom = (H' ⊓ L2').subgroupOf H') {x : G}
    (hx : x ∈ H) :
    x ∈ quasithinOmegaOneCenter (H ⊓ L2) ↔ vFwd φ x ∈ quasithinOmegaOneCenter (H' ⊓ L2') := by
  rw [mem_quasithinOmegaOneCenter_iff, mem_quasithinOmegaOneCenter_iff]
  have hmemT : ∀ {y : G}, y ∈ H → (y ∈ H ⊓ L2 ↔ vFwd φ y ∈ H' ⊓ L2') := by
    intro y hy
    have h1 : y ∈ H ⊓ L2 ↔ (⟨y, hy⟩ : ↥H) ∈ (H ⊓ L2).subgroupOf H := Iff.rfl
    have h2 : vFwd φ y ∈ H' ⊓ L2' ↔
        (⟨vFwd φ y, vFwd_mem φ hy⟩ : ↥H') ∈ (H' ⊓ L2').subgroupOf H' := Iff.rfl
    rw [h1, h2, ← hT]
    have hφ : (⟨vFwd φ y, vFwd_mem φ hy⟩ : ↥H') = φ ⟨y, hy⟩ := Subtype.ext (vFwd_of_mem φ hy)
    rw [hφ, Subgroup.mem_map_equiv]
    simp
  refine and_congr (hmemT hx) (and_congr ?_ ?_)
  · simp only [Subgroup.mem_centralizer_iff]
    constructor
    · intro hc t' ht'
      obtain ⟨t, htH, rfl⟩ := vFwd_surj φ (Subgroup.mem_inf.1 ht').1
      have htT : t ∈ H ⊓ L2 := (hmemT htH).2 ht'
      have := hc t htT
      rw [← vFwd_mul φ htH hx, ← vFwd_mul φ hx htH, this]
    · intro hc t ht
      have htH : t ∈ H := (Subgroup.mem_inf.1 ht).1
      have := hc (vFwd φ t) ((hmemT htH).1 ht)
      rw [← vFwd_mul φ htH hx, ← vFwd_mul φ hx htH] at this
      exact vFwd_inj φ (H.mul_mem htH hx) (H.mul_mem hx htH) this
  · constructor
    · intro h2
      rw [← vFwd_pow φ hx, h2, vFwd_one]
    · intro h2
      rw [← vFwd_pow φ hx] at h2
      exact vFwd_inj φ (H.pow_mem hx 2) H.one_mem (h2.trans (vFwd_one φ).symm)

theorem card_eq_of_iff {K : Subgroup G} {K' : Subgroup G'} (hK : K ≤ H) (hK' : K' ≤ H')
    (hiff : ∀ x ∈ H, x ∈ K ↔ vFwd φ x ∈ K') : Nat.card K = Nat.card K' := by
  refine Nat.card_eq_of_bijective (fun x => ⟨vFwd φ x, (hiff x (hK x.2)).1 x.2⟩) ⟨?_, ?_⟩
  · intro x y hxy
    have := congrArg Subtype.val hxy
    exact Subtype.ext (vFwd_inj φ (hK x.2) (hK y.2) this)
  · rintro ⟨y, hy⟩
    obtain ⟨x, hxH, rfl⟩ := vFwd_surj φ (hK' hy)
    exact ⟨⟨x, (hiff x hxH).2 hy⟩, rfl⟩

end Pull

theorem TitsLikeVertexFacts.of_vertexEquiv {G G' : Type*} [Group G] [Group G']
    {H L2 : Subgroup G} {H' L2' : Subgroup G'} (φ : ↥H ≃* ↥H')
    (hT : ((H ⊓ L2).subgroupOf H).map φ.toMonoidHom = (H' ⊓ L2').subgroupOf H')
    (h : TitsLikeVertexFacts H' L2') : TitsLikeVertexFacts H L2 := by
  obtain ⟨E', F', cA, cB, cC, cD, cE1, cE2, cG, cH, cQ, cI1, cI2, cJ⟩ := h
  have hPH : ∀ {x : G}, x ∈ pCoreOf 2 H → x ∈ H := fun hx => pCoreOf_le 2 H hx
  have hPf : ∀ {x : G}, x ∈ H → (x ∈ pCoreOf 2 H ↔ vFwd φ x ∈ pCoreOf 2 H') :=
    fun hx => vFwd_pCoreOf φ hx
  have hZ : ∀ {x : G}, x ∈ H → (x ∈ quasithinOmegaOneCenter (H ⊓ L2) ↔
      vFwd φ x ∈ quasithinOmegaOneCenter (H' ⊓ L2')) := fun hx => vFwd_Z φ hT hx
  have hE'P : ∀ {y : G'}, y ∈ E' → y ∈ pCoreOf 2 H' := fun {y} hy => ((cA y).1 hy).1
  have hF'P : ∀ {y : G'}, y ∈ F' → y ∈ pCoreOf 2 H' := fun {y} hy => ((cB y).1 hy).1
  have hE'H : ∀ {y : G'}, y ∈ E' → y ∈ H' := fun hy => pCoreOf_le 2 H' (hE'P hy)
  have hF'H : ∀ {y : G'}, y ∈ F' → y ∈ H' := fun hy => pCoreOf_le 2 H' (hF'P hy)
  have hP'pre : ∀ {y : G'}, y ∈ pCoreOf 2 H' → ∃ x ∈ pCoreOf 2 H, vFwd φ x = y :=
    fun hy => exists_pCore_preimage φ hy
  have hcommH : ∀ {x y : G}, x ∈ H → y ∈ H → x * y * x⁻¹ * y⁻¹ ∈ H := fun hx hy =>
    H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)
  refine ⟨vPull φ E', vPull φ F', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    constructor
    · rintro ⟨hxH, hxE⟩
      obtain ⟨hxP', hcomm⟩ := (cA _).1 hxE
      refine ⟨(hPf hxH).2 hxP', fun y hy => ?_⟩
      have hyH := hPH hy
      have := hcomm _ ((hPf hyH).1 hy)
      rw [← vFwd_comm φ hxH hyH] at this
      exact (hZ (hcommH hxH hyH)).2 this
    · rintro ⟨hxP, hy⟩
      have hxH := hPH hxP
      refine ⟨hxH, (cA _).2 ⟨(hPf hxH).1 hxP, fun y' hy' => ?_⟩⟩
      obtain ⟨y, hyP, rfl⟩ := hP'pre hy'
      have hyH := hPH hyP
      have := (hZ (hcommH hxH hyH)).1 (hy y hyP)
      rwa [vFwd_comm φ hxH hyH] at this
  · intro x
    constructor
    · rintro ⟨hxH, hxF⟩
      obtain ⟨hxP', hcomm⟩ := (cB _).1 hxF
      refine ⟨(hPf hxH).2 hxP', fun e he => ?_⟩
      have := hcomm _ he.2
      rw [← vFwd_mul φ hxH he.1, ← vFwd_mul φ he.1 hxH] at this
      exact vFwd_inj φ (H.mul_mem hxH he.1) (H.mul_mem he.1 hxH) this
    · rintro ⟨hxP, hc⟩
      have hxH := hPH hxP
      refine ⟨hxH, (cB _).2 ⟨(hPf hxH).1 hxP, fun e' he' => ?_⟩⟩
      obtain ⟨e, heH, rfl⟩ := vFwd_surj φ (hE'H he')
      have := hc e ⟨heH, he'⟩
      rw [← vFwd_mul φ hxH heH, ← vFwd_mul φ heH hxH, this]
  · rintro e ⟨heH, heE⟩
    have := cC _ heE
    rw [← vFwd_mul φ heH heH, ← vFwd_one φ] at this
    exact vFwd_inj φ (H.mul_mem heH heH) H.one_mem this
  · rintro e ⟨heH, heE⟩ e' ⟨he'H, he'E⟩
    have := cD _ heE _ he'E
    rw [← vFwd_mul φ heH he'H, ← vFwd_mul φ he'H heH] at this
    exact vFwd_inj φ (H.mul_mem heH he'H) (H.mul_mem he'H heH) this
  · rw [card_eq_of_iff φ (pCoreOf_le 2 H) (pCoreOf_le 2 H') (fun x hx => hPf hx), cE1]
    congr 1
    exact (card_eq_of_iff φ (vPull_le φ) (fun y hy => hF'H hy)
      (fun x hx => ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩)).symm
  · have h1 := card_eq_of_iff φ (vPull_le φ) (fun y hy => hF'H hy)
      (K := vPull φ F') (K' := F') (fun x hx => ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩)
    have h2 := card_eq_of_iff φ (vPull_le φ) (fun y hy => hE'H hy)
      (K := vPull φ E') (K' := E') (fun x hx => ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩)
    rw [h1, h2]
    exact cE2
  · rintro x ⟨hxH, hxE⟩ hy
    refine (hZ hxH).2 (cG _ hxE (fun y' hy' => ?_))
    obtain ⟨y, hyP, rfl⟩ := hP'pre hy'
    have hyH := hPH hyP
    have := hy y hyP
    rw [← vFwd_mul φ hxH hyH, ← vFwd_mul φ hyH hxH, this]
  · intro x hx y hy
    have hxH := hPH hx
    have hyH := hPH hy
    refine ⟨hcommH hxH hyH, ?_⟩
    rw [vFwd_comm φ hxH hyH]
    exact cH _ ((hPf hxH).1 hx) _ ((hPf hyH).1 hy)
  · intro Q hEQ hQP hHQ
    have hQH : ∀ {x : G}, x ∈ Q → x ∈ H := fun hx => hPH (hQP hx)
    have hQfwd : ∀ {x : G}, x ∈ H → (vFwd φ x ∈ vPull φ.symm Q ↔ x ∈ Q) := fun {x} hx => by
      constructor
      · intro h
        have := h.2
        rwa [vFwd_symm φ hx] at this
      · intro h
        exact ⟨vFwd_mem φ hx, by rw [vFwd_symm φ hx]; exact h⟩
    have hE'Q' : E' ≤ vPull φ.symm Q := fun y hy => by
      obtain ⟨x, hxH, rfl⟩ := vFwd_surj φ (hE'H hy)
      exact (hQfwd hxH).2 (hEQ ⟨hxH, hy⟩)
    have hQ'P' : vPull φ.symm Q ≤ pCoreOf 2 H' := fun y hy => by
      obtain ⟨x, hxH, rfl⟩ := vFwd_surj φ hy.1
      exact (hPf hxH).1 (hQP ((hQfwd hxH).1 hy))
    have hHQ' : H' ≤ Subgroup.normalizer ((vPull φ.symm Q : Subgroup G') : Set G') := by
      intro h' hh'
      obtain ⟨h, hhH, rfl⟩ := vFwd_surj φ hh'
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have hnorm := Subgroup.mem_normalizer_iff.1 (hHQ hhH)
      constructor
      · intro hy
        obtain ⟨x, hxH, rfl⟩ := vFwd_surj φ hy.1
        have hxQ := (hQfwd hxH).1 hy
        have h1 := (hnorm x).1 hxQ
        have hmH : h * x * h⁻¹ ∈ H := H.mul_mem (H.mul_mem hhH hxH) (H.inv_mem hhH)
        have := (hQfwd hmH).2 h1
        rwa [vFwd_mul φ (H.mul_mem hhH hxH) (H.inv_mem hhH), vFwd_mul φ hhH hxH,
          vFwd_inv φ hhH] at this
      · intro hy
        have hyH' : y ∈ H' := by
          have h1 := H'.mul_mem (H'.mul_mem (H'.inv_mem (vFwd_mem φ hhH)) hy.1) (vFwd_mem φ hhH)
          simpa [mul_assoc] using h1
        obtain ⟨x, hxH, rfl⟩ := vFwd_surj φ hyH'
        have hmH : h * x * h⁻¹ ∈ H := H.mul_mem (H.mul_mem hhH hxH) (H.inv_mem hhH)
        rw [← vFwd_inv φ hhH, ← vFwd_mul φ hhH hxH,
          ← vFwd_mul φ (H.mul_mem hhH hxH) (H.inv_mem hhH)] at hy
        exact (hQfwd hxH).2 ((hnorm x).2 ((hQfwd hmH).1 hy))
    rcases cQ _ hE'Q' hQ'P' hHQ' with hA | hB
    · left
      intro x hxQ hc
      have hxH := hQH hxQ
      refine ⟨hxH, hA _ ((hQfwd hxH).2 hxQ) (fun w' hw' => ?_)⟩
      obtain ⟨w, hwH, rfl⟩ := vFwd_surj φ hw'.1
      have hwQ := (hQfwd hwH).1 hw'
      have := (hZ (hcommH hxH hwH)).1 (hc w hwQ)
      rwa [vFwd_comm φ hxH hwH] at this
    · right
      intro x hxQ hx2
      have hxH := hQH hxQ
      refine ⟨hxH, hB _ ((hQfwd hxH).2 hxQ) ?_⟩
      rw [← vFwd_mul φ hxH hxH, hx2, vFwd_one]
  · obtain ⟨j', hj'P, hj'F, hj'2⟩ := cI1
    obtain ⟨j, hjP, rfl⟩ := hP'pre hj'P
    have hjH := hPH hjP
    refine ⟨j, hjP, fun h => hj'F h.2, ?_⟩
    rw [← vFwd_mul φ hjH hjH, ← vFwd_one φ] at hj'2
    exact vFwd_inj φ (H.mul_mem hjH hjH) H.one_mem hj'2
  · intro j hjP hjF hj2 k hkP hkF hk2
    have hjH := hPH hjP
    have hkH := hPH hkP
    obtain ⟨h', hh'H', hh'⟩ := cI2 (vFwd φ j) ((hPf hjH).1 hjP) (fun h => hjF ⟨hjH, h⟩)
      (by rw [← vFwd_mul φ hjH hjH, hj2, vFwd_one])
      (vFwd φ k) ((hPf hkH).1 hkP) (fun h => hkF ⟨hkH, h⟩)
      (by rw [← vFwd_mul φ hkH hkH, hk2, vFwd_one])
    obtain ⟨h, hhH, rfl⟩ := vFwd_surj φ hh'H'
    refine ⟨h, hhH, vFwd_inj φ (H.mul_mem (H.mul_mem hhH hjH) (H.inv_mem hhH)) hkH ?_⟩
    rw [vFwd_mul φ (H.mul_mem hhH hjH) (H.inv_mem hhH), vFwd_mul φ hhH hjH, vFwd_inv φ hhH]
    exact hh'
  · obtain ⟨c', hc'H', hc'5, hc'⟩ := cJ
    obtain ⟨c, hcH, rfl⟩ := vFwd_surj φ hc'H'
    refine ⟨c, hcH, ?_, fun x hxP hxF h => ?_⟩
    · rw [← vFwd_pow φ hcH, ← vFwd_one φ] at hc'5
      exact vFwd_inj φ (H.pow_mem hcH 5) H.one_mem hc'5
    · have hxH := hPH hxP
      refine hc' (vFwd φ x) ((hPf hxH).1 hxP) (fun hh => hxF ⟨hxH, hh⟩) ?_
      have := h.2
      rwa [vFwd_comm φ hcH hxH] at this

theorem map_inf_subgroupOf_eq {G G' : Type*} [Group G] [Group G'] {H L2 : Subgroup G}
    {H' L2' : Subgroup G'} (φ : ↥H ≃* ↥H')
    (hT : ∀ x : ↥H, (x : G) ∈ L2 ↔ ((φ x : ↥H') : G') ∈ L2') :
    ((H ⊓ L2).subgroupOf H).map φ.toMonoidHom = (H' ⊓ L2').subgroupOf H' := by
  ext y
  rw [Subgroup.mem_map_equiv]
  have h1 : φ.symm y ∈ (H ⊓ L2).subgroupOf H ↔ ((φ.symm y : ↥H) : G) ∈ L2 :=
    ⟨fun h => (Subgroup.mem_inf.1 h).2, fun h => Subgroup.mem_inf.2 ⟨(φ.symm y).2, h⟩⟩
  have h2 : y ∈ (H' ⊓ L2').subgroupOf H' ↔ (y : G') ∈ L2' :=
    ⟨fun h => (Subgroup.mem_inf.1 h).2, fun h => Subgroup.mem_inf.2 ⟨y.2, h⟩⟩
  rw [h1, h2, hT (φ.symm y), MulEquiv.apply_symm_apply]

theorem TitsLikeVertexFacts.of_vertexEquiv' {G G' : Type*} [Group G] [Group G']
    {H L2 : Subgroup G} {H' L2' : Subgroup G'} (φ : ↥H ≃* ↥H')
    (hT : ∀ x : ↥H, (x : G) ∈ L2 ↔ ((φ x : ↥H') : G') ∈ L2')
    (h : TitsLikeVertexFacts H' L2') : TitsLikeVertexFacts H L2 :=
  TitsLikeVertexFacts.of_vertexEquiv φ (map_inf_subgroupOf_eq φ hT) h

end CFSG.Quasithin
