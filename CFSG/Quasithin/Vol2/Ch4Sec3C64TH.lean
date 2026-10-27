module

public import CFSG.Quasithin.Vol2.Ch4Sec3C64Coord
public import CFSG.Quasithin.Vol2.Ch4Sec3A7Perm

public section

namespace CFSG.Quasithin.H13.Ch4.C64

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {α : ↥L →* alternatingGroup (Fin 7)}
  {β : ↥(blockU L) →* Multiplicative (AltHeart 7)}

omit [Finite G] in
theorem crd_eq_pair {u : ↥(blockU L)} {a b : Fin 7}
    (hu : Multiplicative.toAdd (β u) = (QuotientAddGroup.mk (A7.pairVec a b) : AltHeart 7)) :
    crd β u = Pi.single a 1 + Pi.single b 1 := by
  simp only [crd, hu, heartEquiv_symm_mk, A7.coe_pairVec]

theorem A7Blk.isCoordAct_of_conjAct (h : A7Blk L α β) (r : ↥(Subgroup.normalizer (L : Set G)))
    {σ : Perm (Fin 7)}
    (hσ : ∀ k : ↥L, ((α ((conjAct L r) k) : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
      σ * (α k : Perm (Fin 7)) * σ⁻¹) :
    H13.A7.IsCoordAct h.psi (r : G) σ := by
  refine h.isCoordAct_of_normalizes r.2 fun k k' hk' => ?_
  have e : k' = (conjAct L r) k := Subtype.ext (by
    rw [hk']
    exact (Subgroup.normalizerMonoidHom_apply_apply_coe L
      (Subgroup.inclusion le_rfl r) k).symm)
  rw [e]
  exact hσ k

theorem A7Blk.isCoordAct_one_or_swap (h : A7Blk L α β) {R : Subgroup G} {a b : Fin 7}
    (hRN : R ≤ Subgroup.normalizer (L : Set G))
    (hR1 : ∀ r : ↥(Subgroup.normalizer (L : Set G)), (r : G) ∈ R →
      (∀ k : ↥L, α ((conjAct L r) k) = α k) ∨
        ∀ k : ↥L, ((α ((conjAct L r) k) : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
          swap a b * (α k : Perm (Fin 7)) * (swap a b)⁻¹)
    {r : G} (hr : r ∈ R) :
    H13.A7.IsCoordAct h.psi r 1 ∨ H13.A7.IsCoordAct h.psi r (swap a b) := by
  rcases hR1 ⟨r, hRN hr⟩ hr with h1 | h1
  · left
    refine h.isCoordAct_of_conjAct ⟨r, hRN hr⟩ fun k => ?_
    rw [h1 k, one_mul, inv_one, mul_one]
  · right
    exact h.isCoordAct_of_conjAct ⟨r, hRN hr⟩ h1

theorem add_permAct7_swap (v : Fin 7 → ZMod 2) {a b : Fin 7} (hab : a ≠ b) :
    v + SteinbergCB.permAct7 (swap a b) v = (v a + v b) • (Pi.single a 1 + Pi.single b 1) := by
  funext i
  simp only [Pi.add_apply, SteinbergCB.permAct7_apply, swap_inv, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply]
  by_cases hia : i = a
  · subst hia
    simp [swap_apply_left, hab]
  · by_cases hib : i = b
    · subst hib
      simp [swap_apply_right, Ne.symm hab, add_comm]
    · rw [swap_apply_of_ne_of_ne hia hib]
      simp only [hia, hib, ite_false, add_zero, mul_zero]
      exact CharTwo.add_self_eq_zero (v i)

omit [Finite G] in
theorem crd_inv (v : ↥(blockU L)) : crd β v⁻¹ = crd β v := by
  have h1 : crd β v⁻¹ + crd β v = 0 := by
    rw [← crd_mul, inv_mul_cancel, crd_one]
  have h2 : crd β v + crd β v = 0 := by
    funext i
    exact CharTwo.add_self_eq_zero _
  calc crd β v⁻¹ = crd β v⁻¹ + (crd β v + crd β v) := by rw [h2, add_zero]
    _ = (crd β v⁻¹ + crd β v) + crd β v := by abel
    _ = crd β v := by rw [h1, zero_add]

theorem A7Blk.comm_mem_pair (h : A7Blk L α β) {R : Subgroup G} {a b : Fin 7} (hab : a ≠ b)
    (hRN : R ≤ Subgroup.normalizer (L : Set G))
    (hR1 : ∀ r : ↥(Subgroup.normalizer (L : Set G)), (r : G) ∈ R →
      (∀ k : ↥L, α ((conjAct L r) k) = α k) ∨
        ∀ k : ↥L, ((α ((conjAct L r) k) : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
          swap a b * (α k : Perm (Fin 7)) * (swap a b)⁻¹)
    {u : ↥(blockU L)}
    (hu : Multiplicative.toAdd (β u) = (QuotientAddGroup.mk (A7.pairVec a b) : AltHeart 7))
    {r : G} (hr : r ∈ R) (v w : ↥(blockU L)) (hw : (w : G) = r * v * r⁻¹) :
    v⁻¹ * w = 1 ∨ v⁻¹ * w = u := by
  have hcu := crd_eq_pair hu
  rcases h.isCoordAct_one_or_swap hRN hR1 hr with h1 | h1
  · left
    have h2 := h1 v w hw
    rw [h.vec_psi, h.vec_psi, SteinbergCB.permAct7_one] at h2
    apply h.crd_injective
    rw [crd_mul, crd_inv, h2, crd_one]
    funext i
    exact CharTwo.add_self_eq_zero _
  · have h2 := h1 v w hw
    rw [h.vec_psi, h.vec_psi] at h2
    have h3 : crd β (v⁻¹ * w) = (crd β v a + crd β v b) • (Pi.single a 1 + Pi.single b 1) := by
      rw [crd_mul, crd_inv, h2, add_permAct7_swap _ hab]
    rcases (show ∀ s : ZMod 2, s = 0 ∨ s = 1 by decide) (crd β v a + crd β v b) with h4 | h4
    · left
      apply h.crd_injective
      rw [h3, h4, zero_smul, crd_one]
    · right
      apply h.crd_injective
      rw [h3, h4, one_smul, hcu]

theorem A7Blk.le_centralizer_of_normalizes (h : A7Blk L α β) {R TH : Subgroup G} {a b : Fin 7}
    (hab : a ≠ b) (hRN : R ≤ Subgroup.normalizer (L : Set G))
    (hR1 : ∀ r : ↥(Subgroup.normalizer (L : Set G)), (r : G) ∈ R →
      (∀ k : ↥L, α ((conjAct L r) k) = α k) ∨
        ∀ k : ↥L, ((α ((conjAct L r) k) : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
          swap a b * (α k : Perm (Fin 7)) * (swap a b)⁻¹)
    (hR2 : ∃ r : ↥(Subgroup.normalizer (L : Set G)), (r : G) ∈ R ∧
      ∀ k : ↥L, ((α ((conjAct L r) k) : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
        swap a b * (α k : Perm (Fin 7)) * (swap a b)⁻¹)
    (hTL : TH ≤ Subgroup.normalizer (L : Set G)) (hTR : TH ≤ Subgroup.normalizer (R : Set G))
    {u : ↥(blockU L)}
    (hu : Multiplicative.toAdd (β u) = (QuotientAddGroup.mk (A7.pairVec a b) : AltHeart 7)) :
    TH ≤ Subgroup.centralizer ({(u : G)} : Set G) := by
  classical
  have hcu := crd_eq_pair hu
  obtain ⟨r₀, hr₀R, hr₀⟩ := hR2
  have hr₀act := h.isCoordAct_of_conjAct r₀ hr₀
  obtain ⟨c, hca, hcb⟩ : ∃ c : Fin 7, c ≠ a ∧ c ≠ b := by
    by_contra hne
    push Not at hne
    have h1 : ∀ c : Fin 7, c = a ∨ c = b := fun c => by
      by_cases hc : c = a
      · exact Or.inl hc
      · exact Or.inr (hne c hc)
    have h2 : (Finset.univ : Finset (Fin 7)) ⊆ {a, b} := fun c _ => by
      rcases h1 c with rfl | rfl <;> simp
    have h3 := Finset.card_le_card h2
    rw [Finset.card_univ, Fintype.card_fin] at h3
    have h4 := Finset.card_le_two (a := a) (b := b)
    omega
  obtain ⟨v, hv⟩ := exists_crd_eq h (SteinbergCB.pair_mem_evenWeight a c)
  have hr₀U : (r₀ : G) ∈ Subgroup.normalizer (blockU L : Set G) :=
    C1.mem_normalizer_blockU r₀.2
  let w₀ : ↥(blockU L) := ⟨r₀ * v * (r₀ : G)⁻¹, (Subgroup.mem_normalizer_iff.1 hr₀U v).1 v.2⟩
  have hw₀ : v⁻¹ * w₀ = u := by
    have h2 := hr₀act v w₀ rfl
    rw [h.vec_psi, h.vec_psi] at h2
    apply h.crd_injective
    rw [crd_mul, crd_inv, h2, add_permAct7_swap _ hab, hv, hcu]
    simp only [Pi.add_apply, Pi.single_apply, Ne.symm hca, Ne.symm hcb, Ne.symm hab,
      ite_true, ite_false, add_zero, one_smul]
  intro t ht
  rw [Subgroup.mem_centralizer_singleton_iff]
  have htU : t ∈ Subgroup.normalizer (blockU L : Set G) := C1.mem_normalizer_blockU (hTL ht)
  let v' : ↥(blockU L) := ⟨t * v * t⁻¹, (Subgroup.mem_normalizer_iff.1 htU v).1 v.2⟩
  let w' : ↥(blockU L) := ⟨t * w₀ * t⁻¹, (Subgroup.mem_normalizer_iff.1 htU w₀).1 w₀.2⟩
  have hr' : t * r₀ * t⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.1 (hTR ht) r₀).1 hr₀R
  have hw' : (w' : G) = (t * r₀ * t⁻¹) * v' * (t * r₀ * t⁻¹)⁻¹ := by
    show t * (r₀ * v * (r₀ : G)⁻¹) * t⁻¹ = (t * r₀ * t⁻¹) * (t * v * t⁻¹) * (t * r₀ * t⁻¹)⁻¹
    group
  have hconj : ((v'⁻¹ * w' : ↥(blockU L)) : G) = t * u * t⁻¹ := by
    rw [← hw₀]
    show (t * v * t⁻¹)⁻¹ * (t * (r₀ * v * (r₀ : G)⁻¹) * t⁻¹) =
      t * ((v : G)⁻¹ * (r₀ * v * (r₀ : G)⁻¹)) * t⁻¹
    group
  have hu1 : u ≠ 1 := by
    intro h1
    have h2 := congrFun hcu a
    rw [h1, crd_one] at h2
    simp [hab] at h2
  rcases h.comm_mem_pair hab hRN hR1 hu hr' v' w' hw' with h1 | h1
  · exfalso
    rw [h1] at hconj
    apply hu1
    apply Subtype.ext
    have h2 : (t * u * t⁻¹ : G) = 1 := hconj.symm
    calc (u : G) = t⁻¹ * (t * u * t⁻¹) * t := by group
      _ = 1 := by rw [h2]; group
  · rw [h1] at hconj
    calc t * u = (t * u * t⁻¹) * t := by group
      _ = u * t := by rw [← hconj]

end CFSG.Quasithin.H13.Ch4.C64
