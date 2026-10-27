module

public import CFSG.Quasithin.EmptyFaithful.S14612DA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

section D3Facts

open DihedralGroup in
private theorem d3_order_three (d : DihedralGroup 3) (h3 : d ^ 3 = 1) (h1 : d ≠ 1) :
    d = r 1 ∨ d = r 2 := by
  revert d; decide

open DihedralGroup in
private theorem d3_order_two (d : DihedralGroup 3) (h2 : d * d = 1) (h1 : d ≠ 1) :
    d = sr 0 ∨ d = sr 1 ∨ d = sr 2 := by
  revert d; decide

open DihedralGroup in
private theorem d3_center (d : DihedralGroup 3) (h : ∀ e : DihedralGroup 3, d * e = e * d) :
    d = 1 := by
  revert d; decide

open DihedralGroup in
private theorem d3_closure : Subgroup.closure ({r 1, sr 0} : Set (DihedralGroup 3)) = ⊤ := by
  rw [eq_top_iff]
  intro d hd
  clear hd
  rcases d with i | i
  · have : (r i : DihedralGroup 3) = (r 1) ^ i.val := by
      revert i; decide
    rw [this]
    exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _
  · have : (sr i : DihedralGroup 3) = sr 0 * (r 1) ^ i.val := by
      revert i; decide
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)

end D3Facts

section CenMod

variable {G : Type} [Group G]

def cenModAt (Q : Subgroup G) (g : G) : Subgroup G where
  carrier := {y | y ∈ Subgroup.normalizer (Q : Set G) ∧ g * y * g⁻¹ * y⁻¹ ∈ Q}
  one_mem' := ⟨Subgroup.one_mem _, by simp⟩
  mul_mem' := by
    rintro y z ⟨hyN, hy⟩ ⟨hzN, hz⟩
    refine ⟨Subgroup.mul_mem _ hyN hzN, ?_⟩
    have e : g * (y * z) * g⁻¹ * (y * z)⁻¹ =
        (g * y * g⁻¹ * y⁻¹) * (y * (g * z * g⁻¹ * z⁻¹) * y⁻¹) := by group
    rw [e]
    exact Q.mul_mem hy ((Subgroup.mem_normalizer_iff.mp hyN _).mp hz)
  inv_mem' := by
    rintro y ⟨hyN, hy⟩
    refine ⟨Subgroup.inv_mem _ hyN, ?_⟩
    have e : g * y⁻¹ * g⁻¹ * y⁻¹⁻¹ = y⁻¹ * (g * y * g⁻¹ * y⁻¹)⁻¹ * y⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyN) _).mp (Q.inv_mem hy)

theorem card_quotient_le_of_fiber {X β : Type*} [Group X] [Finite β] (K : Subgroup X) (F : X → β)
    (hF : ∀ x y, F x = F y → x⁻¹ * y ∈ K) : Nat.card (X ⧸ K) ≤ Nat.card β := by
  classical
  let ψ : β → X ⧸ K := fun b => ((Function.invFun F b : X) : X ⧸ K)
  have hsurj : Function.Surjective ψ := by
    intro c
    induction c using QuotientGroup.induction_on with
    | H x =>
      refine ⟨F x, ?_⟩
      exact QuotientGroup.eq.mpr (hF _ _ (Function.invFun_eq (f := F) ⟨x, rfl⟩))
  exact Nat.card_le_card_of_surjective ψ hsurj

end CenMod

section Index6

variable {G : Type} [Group G]

open DihedralGroup in
theorem relIndex_centralizerMod_le_six {N' H₁ Q : Subgroup G}
    (hN₁ : N' ≤ Subgroup.normalizer (H₁ : Set G)) (hNQ : N' ≤ Subgroup.normalizer (Q : Set G))
    (hH₁Q : H₁ ≤ Subgroup.normalizer (Q : Set G))
    (φ : ↥H₁ →* DihedralGroup 3) (hφs : Function.Surjective φ)
    (hker : ∀ y : ↥H₁, φ y = 1 ↔ (y : G) ∈ Q) :
    (centralizerMod Q N' H₁).relIndex N' ≤ 6 := by
  classical
  obtain ⟨a, ha⟩ := hφs (r 1)
  obtain ⟨s, hs⟩ := hφs (sr 0)
  have hcj : ∀ x ∈ N', ∀ y ∈ H₁, x * y * x⁻¹ ∈ H₁ := fun x hx y hy =>
    (Subgroup.mem_normalizer_iff.mp (hN₁ hx) y).mp hy
  have hcjQ : ∀ x ∈ N', ∀ q : G, q ∈ Q ↔ x * q * x⁻¹ ∈ Q := fun x hx q =>
    Subgroup.mem_normalizer_iff.mp (hNQ hx) q
  have ha3 : (a : G) ^ 3 ∈ Q := by
    have : φ (a ^ 3) = 1 := by rw [map_pow, ha]; decide
    exact (hker _).mp this
  have hs2 : (s : G) * s ∈ Q := by
    have : φ (s * s) = 1 := by rw [map_mul, hs]; decide
    exact (hker _).mp this
  have haQ : (a : G) ∉ Q := fun h => by
    have := (hker a).mpr h
    rw [ha] at this
    exact absurd this (by decide)
  have hsQ : (s : G) ∉ Q := fun h => by
    have := (hker s).mpr h
    rw [hs] at this
    exact absurd this (by decide)
  let cj : ↥N' → ↥H₁ → ↥H₁ := fun x y => ⟨(x : G) * y * (x : G)⁻¹, hcj x x.2 y y.2⟩
  let f : ↥N' → DihedralGroup 3 × DihedralGroup 3 := fun x => (φ (cj x a), φ (cj x s))
  let Sfin : Finset (DihedralGroup 3 × DihedralGroup 3) :=
    ({r 1, r 2} : Finset (DihedralGroup 3)) ×ˢ ({sr 0, sr 1, sr 2} : Finset (DihedralGroup 3))
  have hfS : ∀ x, f x ∈ Sfin := by
    intro x
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · have h3 : φ (cj x a) ^ 3 = 1 := by
        rw [← map_pow, hker]
        have e : (((cj x a) ^ 3 : ↥H₁) : G) = (x : G) * (a : G) ^ 3 * (x : G)⁻¹ := by
          simp [cj, conj_pow]
        rw [e]
        exact (hcjQ x x.2 _).mp ha3
      have h1 : φ (cj x a) ≠ 1 := fun h => haQ ((hcjQ x x.2 (a : G)).mpr ((hker _).mp h))
      show φ (cj x a) ∈ ({r 1, r 2} : Finset (DihedralGroup 3))
      rcases d3_order_three _ h3 h1 with h | h <;> simp [h]
    · have h2 : φ (cj x s) * φ (cj x s) = 1 := by
        rw [← map_mul, hker]
        have e : ((cj x s * cj x s : ↥H₁) : G) = (x : G) * ((s : G) * s) * (x : G)⁻¹ := by
          simp only [cj, Subgroup.coe_mul]; group
        rw [e]
        exact (hcjQ x x.2 _).mp hs2
      have h1 : φ (cj x s) ≠ 1 := fun h => hsQ ((hcjQ x x.2 (s : G)).mpr ((hker _).mp h))
      show φ (cj x s) ∈ ({sr 0, sr 1, sr 2} : Finset (DihedralGroup 3))
      rcases d3_order_two _ h2 h1 with h | h | h <;> simp [h]
  have hfib : ∀ x y : ↥N', f x = f y → ((x⁻¹ * y : ↥N') : G) ∈ centralizerMod Q N' H₁ := by
    intro x y hxy
    have hxy1 : φ (cj x a) = φ (cj y a) := congrArg Prod.fst hxy
    have hxy2 : φ (cj x s) = φ (cj y s) := congrArg Prod.snd hxy
    set g : G := ((x⁻¹ * y : ↥N') : G) with hg
    have hgN : g ∈ N' := (x⁻¹ * y).2
    have hgQ : g ∈ Subgroup.normalizer (Q : Set G) := hNQ hgN
    have key : ∀ u : ↥H₁, φ (cj x u) = φ (cj y u) → (u : G) ∈ cenModAt Q g := by
      intro u hu
      refine ⟨hH₁Q u.2, ?_⟩
      have h1 : (((cj x u)⁻¹ * cj y u : ↥H₁) : G) ∈ Q :=
        (hker _).mp (by rw [map_mul, map_inv, hu, inv_mul_cancel])
      have h2 : (u : G)⁻¹ * g * u * g⁻¹ ∈ Q := by
        have h3 := (hcjQ ((x : G)⁻¹) (N'.inv_mem x.2) _).mp h1
        have e : (x : G)⁻¹ * (((cj x u)⁻¹ * cj y u : ↥H₁) : G) * (x : G)⁻¹⁻¹ =
            (u : G)⁻¹ * g * u * g⁻¹ := by
          simp only [cj, hg, Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rw [e] at h3
        exact h3
      have h4 := (Subgroup.mem_normalizer_iff.mp (hH₁Q u.2) _).mp h2
      have e : (u : G) * ((u : G)⁻¹ * g * u * g⁻¹) * (u : G)⁻¹ = g * (u : G) * g⁻¹ * (u : G)⁻¹ := by group
      rw [e] at h4
      exact h4
    have hQc : ∀ q ∈ Q, q ∈ cenModAt Q g := fun q hq =>
      ⟨Subgroup.le_normalizer hq, Q.mul_mem ((hcjQ g hgN q).mp hq) (Q.inv_mem hq)⟩
    have hall : ∀ u : ↥H₁, (u : G) ∈ cenModAt Q g := by
      intro u
      let A : Subgroup ↥H₁ := Subgroup.closure ({a, s} : Set ↥H₁)
      have hmap : A.map φ = ⊤ := by
        rw [MonoidHom.map_closure]
        have : φ '' ({a, s} : Set ↥H₁) = {r 1, sr 0} := by
          rw [Set.image_pair, ha, hs]
        rw [this]
        exact d3_closure
      have hu : φ u ∈ A.map φ := by rw [hmap]; trivial
      obtain ⟨w, hwA, hwu⟩ := Subgroup.mem_map.mp hu
      have hw : (w : G) ∈ cenModAt Q g := by
        refine Subgroup.closure_induction (p := fun (w : ↥H₁) _ => (w : G) ∈ cenModAt Q g) ?_ ?_ ?_ ?_ hwA
        · intro z hz
          rcases hz with h | h
          · rw [h]; exact key a hxy1
          · rw [h]; exact key s hxy2
        · exact (cenModAt Q g).one_mem
        · intro z z' _ _ hz hz'
          exact (cenModAt Q g).mul_mem hz hz'
        · intro z _ hz
          exact (cenModAt Q g).inv_mem hz
      have hq : ((w⁻¹ * u : ↥H₁) : G) ∈ Q := (hker _).mp (by rw [map_mul, map_inv, hwu, inv_mul_cancel])
      have e : (u : G) = (w : G) * ((w⁻¹ * u : ↥H₁) : G) := by simp
      rw [e]
      exact (cenModAt Q g).mul_mem hw (hQc _ hq)
    exact ⟨hgN, hgQ, fun u hu => (hall ⟨u, hu⟩).2⟩
  have hcard := card_quotient_le_of_fiber ((centralizerMod Q N' H₁).subgroupOf N')
    (fun x => (⟨f x, hfS x⟩ : ↥Sfin)) (fun x y hxy =>
      Subgroup.mem_subgroupOf.mpr (hfib x y (congrArg Subtype.val hxy)))
  calc (centralizerMod Q N' H₁).relIndex N'
      = Nat.card (↥N' ⧸ (centralizerMod Q N' H₁).subgroupOf N') := rfl
    _ ≤ Nat.card ↥Sfin := hcard
    _ = 6 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      decide

end Index6

section P3

variable {G : Type} [Group G] {T M H : Subgroup G} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDecP.exists_phi (h : IsDecP T M H 3 H₀ H₁ H₂ t) :
    ∃ φ : ↥H₁ →* DihedralGroup 3, Function.Surjective φ ∧
      ∀ y : ↥H₁, φ y = 1 ↔ (y : G) ∈ pCoreOf 2 H := by
  obtain ⟨hQn, ⟨e⟩⟩ := h.dihedral₁
  let φ : ↥H₁ →* DihedralGroup 3 :=
    e.toMonoidHom.comp (QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf H₁))
  refine ⟨φ, e.surjective.comp (QuotientGroup.mk'_surjective _), fun x => ?_⟩
  show e (QuotientGroup.mk x) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

end P3

section P3b

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {H₀ H₁ H₂ : Subgroup G} {t : G}

omit [Finite G] in
theorem IsDecP.exists_rotation (h : IsDecP T M H 3 H₀ H₁ H₂ t) :
    ∃ a ∈ H₁, a ∉ pCoreOf 2 H ∧ a ^ 3 ∈ pCoreOf 2 H := by
  obtain ⟨φ, hφs, hker⟩ := h.exists_phi
  obtain ⟨a, ha⟩ := hφs (DihedralGroup.r 1)
  refine ⟨a, a.2, fun hQ => ?_, ?_⟩
  · have := (hker a).mpr hQ
    rw [ha] at this
    exact absurd this (by decide)
  · have : φ (a ^ 3) = 1 := by rw [map_pow, ha]; decide
    exact (hker _).mp this

theorem IsDecP.pq_le (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ 3)
    (h : IsDecP T M H 3 H₀ H₁ H₂ t) : PQ ≤ H₀ := by
  obtain ⟨a, haH₁, haQ, ha3⟩ := h.exists_rotation
  have hTH : T ≤ H := hred.isHTM.1.1
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have haH : a ∈ H := h.le (h.le₁ haH₁)
  have haPT : a ∈ PQ ⊔ T := by rw [← hred.eq]; exact haH
  obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_sup_two hT2 (hTH.trans hred.normal) haPT
  have hQPQ : pCoreOf 2 H ≤ PQ := hred.lt.le
  have h3 : a ^ 3 ∈ PQ := hQPQ ha3
  have haPQ : a ∈ PQ := by
    have hcop : IsCoprime ((2 ^ k : ℕ) : ℤ) ((3 : ℕ) : ℤ) := by
      rw [Nat.isCoprime_iff_coprime]
      exact Nat.Coprime.pow_left k (by norm_num)
    obtain ⟨u, v, huv⟩ := hcop.symm
    have e : a = (a ^ 3) ^ u * (a ^ 2 ^ k) ^ v := by
      have huv' : ((3 : ℕ) : ℤ) * u + ((2 ^ k : ℕ) : ℤ) * v = 1 := by linarith [huv]
      have h1 : (a ^ 3) ^ u * (a ^ 2 ^ k) ^ v = a ^ (((3 : ℕ) : ℤ) * u + ((2 ^ k : ℕ) : ℤ) * v) := by
        rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
      rw [h1, huv', zpow_one]
    rw [e]
    exact PQ.mul_mem (PQ.zpow_mem h3 u) (PQ.zpow_mem hk v)
  have hHN : H ≤ Subgroup.normalizer ((H₀ ⊓ PQ : Subgroup G) : Set G) :=
    fun x hx => Subgroup.inf_normalizer_le_normalizer_inf ⟨h.normal hx, hred.normal hx⟩
  rcases hred.minimal (H₀ ⊓ PQ) (le_inf (h.Q₁.trans h.le₁) hQPQ) inf_le_right hHN with hN | hN
  · exfalso
    apply haQ
    rw [← hN]
    exact ⟨h.le₁ haH₁, haPQ⟩
  · exact inf_eq_right.mp hN

end P3b

section P3c

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {H₀ H₁ H₂ : Subgroup G} {t : G}

omit [Finite G] in
theorem IsDecP.mem_of_centralizes (h : IsDecP T M H 3 H₀ H₁ H₂ t) {y : G} (hy : y ∈ H₀)
    (hyc : ∀ u ∈ H₀, y * u * y⁻¹ * u⁻¹ ∈ pCoreOf 2 H) : y ∈ H₂ := by
  obtain ⟨φ, hφs, hker⟩ := h.exists_phi
  have hmul : (↑(H₁ ⊔ H₂) : Set G) = ↑H₁ * ↑H₂ :=
    Subgroup.coe_mul_of_left_le_normalizer_right H₁ H₂ h.H₁_le_normalizer_H₂
  have hy' : y ∈ (↑(H₁ ⊔ H₂) : Set G) := by
    rw [← h.sup]
    exact hy
  rw [hmul] at hy'
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := hy'
  have hQN : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hy₁H : y₁ ∈ H := h.le (h.le₁ hy₁)
  have hcen : ∀ u : ↥H₁, φ ⟨y₁, hy₁⟩ * φ u = φ u * φ ⟨y₁, hy₁⟩ := by
    intro u
    have hu0 : (u : G) ∈ H₀ := h.le₁ u.2
    have h1 := hyc _ hu0
    have hc : (u : G) * y₂ * (u : G)⁻¹ * y₂⁻¹ ∈ pCoreOf 2 H :=
      h.comm (Subgroup.commutator_mem_commutator u.2 hy₂)
    have hc' : y₂ * (u : G) * y₂⁻¹ * (u : G)⁻¹ ∈ pCoreOf 2 H := by
      have := (pCoreOf 2 H).inv_mem hc
      have e : ((u : G) * y₂ * (u : G)⁻¹ * y₂⁻¹)⁻¹ = y₂ * (u : G) * y₂⁻¹ * (u : G)⁻¹ := by group
      rwa [e] at this
    have h2 : y₁ * (u : G) * y₁⁻¹ * (u : G)⁻¹ ∈ pCoreOf 2 H := by
      have h3 := (Subgroup.mem_normalizer_iff.mp (hQN hy₁H) _).mp hc'
      have e : y₁ * y₂ * (u : G) * (y₁ * y₂)⁻¹ * (u : G)⁻¹ =
          (y₁ * (y₂ * (u : G) * y₂⁻¹ * (u : G)⁻¹) * y₁⁻¹) * (y₁ * (u : G) * y₁⁻¹ * (u : G)⁻¹) := by
        group
      rw [e] at h1
      have := (pCoreOf 2 H).mul_mem ((pCoreOf 2 H).inv_mem h3) h1
      simpa [mul_assoc] using this
    have h4 : φ (⟨y₁, hy₁⟩ * u * ⟨y₁, hy₁⟩⁻¹ * u⁻¹) = 1 := (hker _).mpr h2
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h4
    exact (commutatorElement_eq_one_iff_mul_comm).mp h4
  have h5 : φ ⟨y₁, hy₁⟩ = 1 := d3_center _ (fun e => by
    obtain ⟨u, rfl⟩ := hφs e
    exact hcen u)
  have hy₁Q : y₁ ∈ pCoreOf 2 H := (hker _).mp h5
  exact H₂.mul_mem (h.Q₂ hy₁Q) hy₂

theorem IsDecP.centralizerMod_le (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ 3) (h : IsDecP T M H 3 H₀ H₁ H₂ t) :
    centralizerMod (pCoreOf 2 H) H H₀ ≤ pCoreOf 2 H := by
  have hTH : T ≤ H := hred.isHTM.1.1
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  set K := centralizerMod (pCoreOf 2 H) H H₀ with hKdef
  have hKPQ : ∀ y ∈ K, y ∈ PQ → y ∈ pCoreOf 2 H := by
    intro y hyK hyPQ
    have hyH₀ : y ∈ H₀ := h.pq_le S hred hyPQ
    have hyc : ∀ u ∈ H₀, y * u * y⁻¹ * u⁻¹ ∈ pCoreOf 2 H := hyK.2.2
    have h2 : y ∈ H₂ := h.mem_of_centralizes hyH₀ hyc
    have h1 : y ∈ H₁ := h.swap.mem_of_centralizes hyH₀ hyc
    have : y ∈ H₁ ⊓ H₂ := ⟨h1, h2⟩
    rwa [h.inf] at this
  have hKH : K ≤ H := centralizerMod_le_left _ _ _
  have hHN : H ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_centralizerMod (le_normalizer_pCoreOf 2 H) Subgroup.le_normalizer h.normal
  have hKn : (K.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hHN
  have hK2 : IsPGroup 2 ↥K := by
    intro k
    have hkH : (k : G) ∈ H := hKH k.2
    have hkPT : (k : G) ∈ PQ ⊔ T := by
      rw [← hred.eq]
      exact hkH
    obtain ⟨n, hn⟩ := exists_pow_mem_of_mem_sup_two hT2 (hTH.trans hred.normal) hkPT
    have hnK : (k : G) ^ 2 ^ n ∈ K := K.pow_mem k.2 _
    have hnQ : (k : G) ^ 2 ^ n ∈ pCoreOf 2 H := hKPQ _ hnK hn
    obtain ⟨j, hj⟩ := pCoreOf_isPGroup 2 H ⟨_, hnQ⟩
    refine ⟨n + j, Subtype.ext ?_⟩
    have := congrArg Subtype.val hj
    simpa [pow_add, pow_mul] using this
  exact le_pCoreOf 2 hKH hKn hK2

end P3c

section P3d

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDecP.card_H₀ (h : IsDecP T M H 3 H₀ H₁ H₂ t) :
    Nat.card H₀ = 36 * Nat.card (pCoreOf 2 H) := by
  have h1 := h.card_H₁_gen (by norm_num : (3 : ℕ) ≠ 0)
  have h2 := h.swap.card_H₁_gen (by norm_num : (3 : ℕ) ≠ 0)
  have hprod := QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer h.H₁_le_normalizer_H₂
  rw [← h.sup, h.inf, h1, h2] at hprod
  have hpos : 0 < Nat.card (pCoreOf 2 H) := Nat.card_pos
  have : Nat.card H₀ * Nat.card (pCoreOf 2 H) = 36 * Nat.card (pCoreOf 2 H) * Nat.card (pCoreOf 2 H) := by
    rw [hprod]; ring
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem IsDecP.inf_normalizer_le (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ 3) (h : IsDecP T M H 3 H₀ H₁ H₂ t) :
    T ⊓ Subgroup.normalizer (H₁ : Set G) ≤ H₀ := by
  set Q := pCoreOf 2 H with hQ
  set T₀ := T ⊓ Subgroup.normalizer (H₁ : Set G) with hT₀
  have hTH : T ≤ H := hred.isHTM.1.1
  have hT₀H₂ : T₀ ≤ Subgroup.normalizer (H₂ : Set G) := by
    rw [hT₀, ← h.inf_normalizer_swap_eq]
    exact inf_le_right
  set N' := H₀ ⊔ T₀ with hN'
  have hH₀N' : H₀ ≤ N' := le_sup_left
  have hN'H : N' ≤ H := sup_le h.le (inf_le_left.trans hTH)
  have hN'₁ : N' ≤ Subgroup.normalizer (H₁ : Set G) :=
    sup_le h.H₀_le_normalizer_H₁ inf_le_right
  have hN'₂ : N' ≤ Subgroup.normalizer (H₂ : Set G) :=
    sup_le h.H₀_le_normalizer_H₂ hT₀H₂
  have hN'Q : N' ≤ Subgroup.normalizer (Q : Set G) := hN'H.trans (le_normalizer_pCoreOf 2 H)
  have hH₁Q : H₁ ≤ Subgroup.normalizer (Q : Set G) :=
    (h.le₁.trans h.le).trans (le_normalizer_pCoreOf 2 H)
  have hH₂Q : H₂ ≤ Subgroup.normalizer (Q : Set G) :=
    (h.le₂.trans h.le).trans (le_normalizer_pCoreOf 2 H)
  obtain ⟨φ₁, hs₁, hk₁⟩ := h.exists_phi
  obtain ⟨φ₂, hs₂, hk₂⟩ := h.swap.exists_phi
  have hi₁ := relIndex_centralizerMod_le_six hN'₁ hN'Q hH₁Q φ₁ hs₁ hk₁
  have hi₂ := relIndex_centralizerMod_le_six hN'₂ hN'Q hH₂Q φ₂ hs₂ hk₂
  have hKQ : centralizerMod Q N' H₁ ⊓ centralizerMod Q N' H₂ ≤ Q := by
    intro x hx
    refine h.centralizerMod_le S hred ⟨hN'H hx.1.1, hx.1.2.1, fun u hu => ?_⟩
    have hle : H₁ ⊔ H₂ ≤ cenModAt Q x :=
      sup_le (fun y hy => ⟨hH₁Q hy, hx.1.2.2 y hy⟩) (fun y hy => ⟨hH₂Q hy, hx.2.2.2 y hy⟩)
    have hu' : u ∈ H₁ ⊔ H₂ := by
      rw [← h.sup]
      exact hu
    exact (hle hu').2
  have hfin : (centralizerMod Q N' H₁ ⊓ centralizerMod Q N' H₂).relIndex N' ≤ 36 :=
    Subgroup.relIndex_inf_le.trans (Nat.mul_le_mul hi₁ hi₂)
  have hQN' : Q ≤ N' := (h.Q₁.trans h.le₁).trans hH₀N'
  have hQrel : Q.relIndex N' ≤ 36 :=
    (Subgroup.relIndex_le_of_le_left hKQ Subgroup.index_ne_zero_of_finite).trans hfin
  have hmul := Subgroup.relIndex_mul_card Q N'
  rw [inf_eq_left.mpr hQN'] at hmul
  have hcard : Nat.card N' ≤ Nat.card H₀ := by
    rw [← hmul, h.card_H₀]
    exact Nat.mul_le_mul_right _ hQrel
  have hEq : H₀ = N' := Subgroup.eq_of_le_of_card_ge hH₀N' hcard
  exact le_sup_right.trans hEq.ge

theorem IsDecP.relIndex_eq_two_of_p_three (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ 3) (h : IsDecP T M H 3 H₀ H₁ H₂ t) : H₀.relIndex H = 2 := by
  have hT₀ := h.inf_normalizer_le S hred
  have hTH : T ≤ H := hred.isHTM.1.1
  have hT₀eq : T ⊓ H₀ = T ⊓ Subgroup.normalizer (H₁ : Set G) :=
    le_antisymm h.inf_le_inf_normalizer (le_inf inf_le_left hT₀)
  have h1 := Subgroup.relIndex_mul_card (T ⊓ Subgroup.normalizer (H₁ : Set G)) T
  rw [inf_eq_left.mpr (inf_le_left : T ⊓ Subgroup.normalizer (H₁ : Set G) ≤ T), h.indexT] at h1
  have h2 := Subgroup.relIndex_mul_card H₀ H
  rw [inf_eq_left.mpr h.le] at h2
  have h3 := QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer (hTH.trans h.normal)
  rw [sup_comm, ← h.eq, hT₀eq] at h3
  have hpos : 0 < Nat.card (T ⊓ Subgroup.normalizer (H₁ : Set G) : Subgroup G) := Nat.card_pos
  have hpos₀ : 0 < Nat.card H₀ := Nat.card_pos
  have h4 : Nat.card H * Nat.card (T ⊓ Subgroup.normalizer (H₁ : Set G) : Subgroup G) =
      2 * Nat.card H₀ * Nat.card (T ⊓ Subgroup.normalizer (H₁ : Set G) : Subgroup G) := by
    rw [h3, ← h1]; ring
  have h5 : Nat.card H = 2 * Nat.card H₀ := Nat.eq_of_mul_eq_mul_right hpos h4
  rw [← h2] at h5
  exact Nat.eq_of_mul_eq_mul_right hpos₀ h5

end P3d

end CFSG.Quasithin
