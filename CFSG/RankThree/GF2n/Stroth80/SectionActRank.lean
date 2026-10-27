module

public import CFSG.RankThree.GF2n.Stroth80.Conclusion

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Matrix
open scoped commutatorElement

private theorem eq_of_mulVec_eq {ι K : Type} [Fintype ι] [Semiring K] {M N : Matrix ι ι K}
    (h : ∀ w : ι → K, M *ᵥ w = N *ᵥ w) : M = N :=
  Matrix.mulVec_injective (funext h)

private theorem commutatorElement_eq_mul_inv_conj {G : Type} [Group G] (g s : G) :
    ⁅g, s⁆ = g * (s * g * s⁻¹)⁻¹ := by
  rw [commutatorElement_def]
  group

private theorem one_sub_mulVec_mem_range {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (A : Matrix ι ι K) (B : ℤ → Matrix ι ι K) (h0 : B 0 = 1)
    (hs : ∀ k : ℤ, B (k + 1) = B k * A) (hc : ∀ k : ℤ, B k * A = A * B k) (k : ℤ) :
    ∀ w : ι → K, (1 - B k) *ᵥ w ∈ LinearMap.range (Matrix.mulVecLin (A - 1)) := by
  have hcw : ∀ (M : Matrix ι ι K), M * A = A * M → ∀ w : ι → K,
      M *ᵥ (A *ᵥ w) = A *ᵥ (M *ᵥ w) := by
    intro M hM w
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]
  induction k with
  | zero =>
    intro w
    rw [h0, sub_self, Matrix.zero_mulVec]
    exact Submodule.zero_mem _
  | succ i ih =>
    intro w
    have e1 : (1 - B ((i : ℤ) + 1)) *ᵥ w = w - B i *ᵥ (A *ᵥ w) := by
      rw [hs, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
    have e2 : (1 - B i) *ᵥ w - (A - 1) *ᵥ (B i *ᵥ w) = w - A *ᵥ (B i *ᵥ w) := by
      simp only [Matrix.sub_mulVec, Matrix.one_mulVec]
      abel
    have key : w - B i *ᵥ (A *ᵥ w) = (1 - B i) *ᵥ w - (A - 1) *ᵥ (B i *ᵥ w) := by
      rw [e2, hcw (B i) (hc i) w]
    rw [e1, key]
    exact Submodule.sub_mem _ (ih w) (LinearMap.mem_range_self (Matrix.mulVecLin (A - 1)) _)
  | pred i ih =>
    intro w
    have hj := hs (-(i : ℤ) - 1)
    rw [show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring] at hj
    have h1 : (1 - B (-(i : ℤ) - 1) * A) *ᵥ w ∈ LinearMap.range (Matrix.mulVecLin (A - 1)) := by
      rw [← hj]
      exact ih w
    have key : (1 - B (-(i : ℤ) - 1)) *ᵥ w =
        (1 - B (-(i : ℤ) - 1) * A) *ᵥ w + (A - 1) *ᵥ (B (-(i : ℤ) - 1) *ᵥ w) := by
      simp only [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
      rw [hcw (B (-(i : ℤ) - 1)) (hc (-(i : ℤ) - 1)) w]
      abel
    rw [key]
    exact Submodule.add_mem _ h1 (LinearMap.mem_range_self (Matrix.mulVecLin (A - 1)) _)

theorem card_comm_zpowers_sup_of_sectionAct {G : Type} [Group G] {ι : Type} [Fintype ι]
    [DecidableEq ι] {K : Type} [Field K] [Finite K] {S V Z : Subgroup G} {φ : S →* GL ι K}
    {act : GL ι K → Matrix ι ι K} (hact : SectionAct K S V Z φ act) (hZV : Z ≤ V) (x : S) :
    Nat.card ↥(⁅V, Subgroup.zpowers (x : G)⁆ ⊔ Z) =
      Nat.card Z * Nat.card K ^ (act (φ x) - 1).rank := by
  obtain ⟨hnorm, hN, ψ, hψ⟩ := hact
  obtain ⟨piV, hpiV⟩ : ∃ f : V →* Multiplicative (ι → K),
      ∀ v : V, f v = ψ (QuotientGroup.mk v) :=
    ⟨ψ.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf V)), fun v => rfl⟩
  obtain ⟨R, hRdef⟩ : ∃ R : Submodule K (ι → K),
      R = LinearMap.range (Matrix.mulVecLin (act (φ x) - 1)) := ⟨_, rfl⟩
  have hnormV : ∀ (s : S) (v : V), (s : G) * (v : G) * (s : G)⁻¹ ∈ V := fun s v =>
    (Subgroup.mem_normalizer_iff.mp (hnorm s.2) (v : G)).mp v.2
  have hconj : ∀ (s : S) (v w : V), (w : G) = (s : G) * (v : G) * (s : G)⁻¹ →
      Multiplicative.toAdd (piV w) = act (φ s) *ᵥ Multiplicative.toAdd (piV v) := by
    intro s v w hw
    rw [hpiV, hpiV]
    exact hψ s v w hw
  have hsurj : ∀ u : ι → K, ∃ v : V, Multiplicative.toAdd (piV v) = u := by
    intro u
    obtain ⟨q, hq⟩ := ψ.surjective (Multiplicative.ofAdd u)
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨v, by simp [hpiV, hq]⟩
  have hker : ∀ v : V, piV v = 1 ↔ (v : G) ∈ Z := by
    intro v
    rw [hpiV, ψ.map_eq_one_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hcomm_mem : ∀ (s : S) (v : V), ⁅(v : G), (s : G)⁆ ∈ V := by
    intro s v
    rw [commutatorElement_eq_mul_inv_conj]
    exact V.mul_mem v.2 (V.inv_mem (hnormV s v))
  have hcomm_val : ∀ (s : S) (v c : V), (c : G) = ⁅(v : G), (s : G)⁆ →
      Multiplicative.toAdd (piV c) = (1 - act (φ s)) *ᵥ Multiplicative.toAdd (piV v) := by
    intro s v c hc
    have hsplit : c = v * (⟨(s : G) * (v : G) * (s : G)⁻¹, hnormV s v⟩ : V)⁻¹ := by
      apply Subtype.ext
      rw [hc, Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_eq_mul_inv_conj]
    rw [hsplit, map_mul, map_inv, toAdd_mul, toAdd_inv,
      hconj s v ⟨(s : G) * (v : G) * (s : G)⁻¹, hnormV s v⟩ rfl, Matrix.sub_mulVec,
      Matrix.one_mulVec, sub_eq_add_neg]
  have hH : ∀ s t : S, act (φ (s * t)) = act (φ s) * act (φ t) := by
    intro s t
    apply eq_of_mulVec_eq
    intro w
    obtain ⟨v, hv⟩ := hsurj w
    obtain ⟨v1, hv1e⟩ : ∃ v1 : V, (v1 : G) = (t : G) * (v : G) * (t : G)⁻¹ :=
      ⟨⟨_, hnormV t v⟩, rfl⟩
    obtain ⟨v2, hv2e⟩ : ∃ v2 : V, (v2 : G) = (s : G) * (v1 : G) * (s : G)⁻¹ :=
      ⟨⟨_, hnormV s v1⟩, rfl⟩
    have hv1 := hconj t v v1 hv1e
    have hv2 := hconj s v1 v2 hv2e
    have hv3 := hconj (s * t) v v2 (by
      rw [hv2e, hv1e]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group)
    rw [← hv, ← Matrix.mulVec_mulVec, ← hv3, hv2, hv1]
  have hone : act (φ 1) = 1 := by
    apply eq_of_mulVec_eq
    intro w
    obtain ⟨v, hv⟩ := hsurj w
    have h1 := hconj 1 v v (by simp)
    rw [Matrix.one_mulVec, ← hv, ← h1]
  have hBzero : act (φ (x ^ (0 : ℤ))) = 1 := by
    rw [zpow_zero, hone]
  have hBsucc : ∀ k : ℤ, act (φ (x ^ (k + 1))) = act (φ (x ^ k)) * act (φ x) := by
    intro k
    rw [_root_.zpow_add_one, hH]
  have hcomm_zpow : ∀ k : ℤ, act (φ (x ^ k)) * act (φ x) = act (φ x) * act (φ (x ^ k)) := by
    intro k
    rw [← hH, ← hH, ((Commute.refl x).zpow_left k).eq]
  have hD : ∀ (k : ℤ) (w : ι → K), (1 - act (φ (x ^ k))) *ᵥ w ∈ R := by
    intro k w
    rw [hRdef]
    exact one_sub_mulVec_mem_range (act (φ x)) (fun j => act (φ (x ^ j))) hBzero hBsucc
      hcomm_zpow k w
  obtain ⟨W, hWdef⟩ : ∃ W : Subgroup G, ∀ g : G,
      g ∈ W ↔ ∃ hg : g ∈ V, Multiplicative.toAdd (piV ⟨g, hg⟩) ∈ R :=
    ⟨{ carrier := {g : G | ∃ hg : g ∈ V, Multiplicative.toAdd (piV ⟨g, hg⟩) ∈ R}
       mul_mem' := by
         intro a b ha hb
         obtain ⟨ha', hpa⟩ := ha
         obtain ⟨hb', hpb⟩ := hb
         show ∃ hg : a * b ∈ V, Multiplicative.toAdd (piV ⟨a * b, hg⟩) ∈ R
         refine ⟨V.mul_mem ha' hb', ?_⟩
         have e : piV ⟨a * b, V.mul_mem ha' hb'⟩ = piV ⟨a, ha'⟩ * piV ⟨b, hb'⟩ :=
           map_mul piV ⟨a, ha'⟩ ⟨b, hb'⟩
         rw [e, toAdd_mul]
         exact R.add_mem hpa hpb
       one_mem' := by
         show ∃ hg : (1 : G) ∈ V, Multiplicative.toAdd (piV ⟨1, hg⟩) ∈ R
         refine ⟨V.one_mem, ?_⟩
         have e : piV ⟨1, V.one_mem⟩ = 1 := map_one piV
         rw [e, toAdd_one]
         exact R.zero_mem
       inv_mem' := by
         intro a ha
         obtain ⟨ha', hpa⟩ := ha
         show ∃ hg : a⁻¹ ∈ V, Multiplicative.toAdd (piV ⟨a⁻¹, hg⟩) ∈ R
         refine ⟨V.inv_mem ha', ?_⟩
         have e : piV ⟨a⁻¹, V.inv_mem ha'⟩ = (piV ⟨a, ha'⟩)⁻¹ := map_inv piV ⟨a, ha'⟩
         rw [e, toAdd_inv]
         exact R.neg_mem hpa }, fun g => Iff.rfl⟩
  have hgen : ⁅V, Subgroup.zpowers (x : G)⁆ ≤ W := by
    rw [Subgroup.commutator_le]
    intro g hg y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hk : (x : G) ^ k = ((x ^ k : S) : G) := by simp
    rw [hk]
    refine (hWdef _).mpr ⟨hcomm_mem (x ^ k) ⟨g, hg⟩, ?_⟩
    rw [hcomm_val (x ^ k) ⟨g, hg⟩ ⟨⁅g, ((x ^ k : S) : G)⁆, hcomm_mem (x ^ k) ⟨g, hg⟩⟩ rfl]
    exact hD k _
  have hZW : Z ≤ W := by
    intro z hz
    refine (hWdef z).mpr ⟨hZV hz, ?_⟩
    have e : piV ⟨z, hZV hz⟩ = 1 := (hker ⟨z, hZV hz⟩).mpr hz
    rw [e, toAdd_one]
    exact R.zero_mem
  obtain ⟨Hs, hHs⟩ : ∃ Hs : Subgroup G, Hs = ⁅V, Subgroup.zpowers (x : G)⁆ ⊔ Z := ⟨_, rfl⟩
  have hHsW : Hs ≤ W := by
    rw [hHs]
    exact sup_le hgen hZW
  have hZH : Z ≤ Hs := by
    rw [hHs]
    exact le_sup_right
  have hHsV : ∀ h : Hs, (h : G) ∈ V := fun h => by
    obtain ⟨hV, -⟩ := (hWdef (h : G)).mp (hHsW h.2)
    exact hV
  have hWH : ∀ h : Hs, Multiplicative.toAdd (piV ⟨(h : G), hHsV h⟩) ∈ R := fun h => by
    obtain ⟨hV, hR'⟩ := (hWdef (h : G)).mp (hHsW h.2)
    exact hR'
  obtain ⟨g, hgev⟩ : ∃ g : Hs →* Multiplicative (ι → K),
      ∀ h : Hs, g h = piV ⟨(h : G), hHsV h⟩ :=
    ⟨{ toFun := fun h => piV ⟨(h : G), hHsV h⟩
       map_one' := by
         show piV ⟨((1 : Hs) : G), hHsV 1⟩ = 1
         exact (hker _).mpr (by simp)
       map_mul' := fun a b => by
         show piV ⟨((a * b : Hs) : G), hHsV (a * b)⟩ =
           piV ⟨(a : G), hHsV a⟩ * piV ⟨(b : G), hHsV b⟩
         exact map_mul piV ⟨(a : G), hHsV a⟩ ⟨(b : G), hHsV b⟩ }, fun h => rfl⟩
  have hgker : g.ker = Z.subgroupOf Hs := by
    ext h
    rw [MonoidHom.mem_ker, hgev, Subgroup.mem_subgroupOf]
    exact hker ⟨(h : G), hHsV h⟩
  have hcard_ker : Nat.card g.ker = Nat.card Z := by
    rw [hgker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZH).toEquiv
  have hrange : Nat.card g.range = Nat.card R := by
    apply Nat.card_congr
    refine Equiv.subtypeEquiv Multiplicative.toAdd ?_
    intro m
    show m ∈ g.range ↔ Multiplicative.toAdd m ∈ R
    constructor
    · rw [MonoidHom.mem_range]
      rintro ⟨h, rfl⟩
      rw [hgev]
      exact hWH h
    · intro hm
      rw [hRdef] at hm
      obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hm
      rw [Matrix.mulVecLin_apply] at hc
      obtain ⟨v, hv⟩ := hsurj (-c)
      have hmemH : ⁅(v : G), (x : G)⁆ ∈ Hs := by
        rw [hHs]
        exact Subgroup.mem_sup_left
          (Subgroup.commutator_mem_commutator v.2 (Subgroup.mem_zpowers _))
      have e : g ⟨⁅(v : G), (x : G)⁆, hmemH⟩ = piV ⟨⁅(v : G), (x : G)⁆, hcomm_mem x v⟩ :=
        hgev _
      rw [MonoidHom.mem_range]
      refine ⟨⟨⁅(v : G), (x : G)⁆, hmemH⟩, ?_⟩
      rw [e]
      apply Multiplicative.toAdd.injective
      rw [hcomm_val x v ⟨⁅(v : G), (x : G)⁆, hcomm_mem x v⟩ rfl, hv, Matrix.mulVec_neg, ← hc]
      simp only [Matrix.sub_mulVec, Matrix.one_mulVec, neg_sub]
  have hcard : Nat.card Hs = Nat.card Z * Nat.card R := by
    rw [← Subgroup.card_mul_index g.ker, hcard_ker, Subgroup.index_ker, hrange]
  rw [← hHs, hcard]
  congr 1
  rw [hRdef]
  exact Module.natCard_eq_pow_finrank

theorem rank_inv_transpose_sub_one {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (A : GL ι K) :
    (((A⁻¹ : GL ι K) : Matrix ι ι K)ᵀ - 1).rank = ((A : Matrix ι ι K) - 1).rank := by
  have htr : ((A⁻¹ : GL ι K) : Matrix ι ι K)ᵀ - 1 =
      (((A⁻¹ : GL ι K) : Matrix ι ι K) - 1)ᵀ := by
    rw [Matrix.transpose_sub, Matrix.transpose_one]
  have hu : IsUnit ((A⁻¹ : GL ι K) : Matrix ι ι K).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)
  have hneg : IsUnit (-1 : Matrix ι ι K).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp isUnit_one.neg
  have hsplit : ((A⁻¹ : GL ι K) : Matrix ι ι K) - 1 =
      (-1 : Matrix ι ι K) * (((A⁻¹ : GL ι K) : Matrix ι ι K) * ((A : Matrix ι ι K) - 1)) := by
    rw [mul_sub, Units.inv_mul, mul_one, neg_one_mul, neg_sub]
  rw [htr, Matrix.rank_transpose, hsplit, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hneg,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hu]

end CFSG.RankThree.GF2n.Stroth80
