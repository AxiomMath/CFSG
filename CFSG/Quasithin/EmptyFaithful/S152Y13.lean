module

public import CFSG.Quasithin.EmptyFaithful.S152Y10
public import CFSG.Quasithin.EmptyFaithful.S152Y12
public import CFSG.Quasithin.EmptyFaithful.S152Y05

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S152Y

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Wc (T Mc M : Subgroup G) : Subgroup G :=
  conjClosure (rcOf Mc M) (y0Of T Mc M ⊔ T)

@[expose] noncomputable def Ls (T Mc M : Subgroup G) : Subgroup (OTwoQuot M) :=
  imageOTwoQuot M (Wc T Mc M)

theorem yOf_eq_oTwoUpper_Wc (T Mc M : Subgroup G) : yOf152 T Mc M = oTwoUpper (Wc T Mc M) := rfl

namespace Data

variable {T Mc M : Subgroup G} (h : Data T Mc M)

include h

theorem Wc_le_M : Wc T Mc M ≤ M :=
  conjClosure_le fun _ hg _ hz =>
    M.mul_mem (M.mul_mem (sup_le (y0Of_le T Mc M) h.T_le hg) (h.rc_le_M hz))
      (M.inv_mem (sup_le (y0Of_le T Mc M) h.T_le hg))

theorem Ys_eq_oTwoUpper_Ls : Ys T Mc M = oTwoUpper (Ls T Mc M) := by
  unfold Ys Ls
  rw [yOf_eq_oTwoUpper_Wc, imageOTwoQuot_oTwoUpper h.Wc_le_M]

theorem Ys_le_Ls : Ys T Mc M ≤ Ls T Mc M := by
  rw [Ys_eq_oTwoUpper_Ls h]
  exact oTwoUpper_le _

theorem Ls_le_normalizer_Ys :
    Ls T Mc M ≤ Subgroup.normalizer (Ys T Mc M : Set (OTwoQuot M)) := by
  rw [Ys_eq_oTwoUpper_Ls h]
  exact le_normalizer_oTwoUpper _

theorem Ys_le_Y0s : Ys T Mc M ≤ Y0s T Mc M :=
  imageOTwoQuot_mono h.yOf_le_y0Of

theorem Wc_induction {P : OTwoQuot M → Prop} (h1 : P 1) (hmul : ∀ a b, P a → P b → P (a * b))
    (hinv : ∀ a, P a → P a⁻¹)
    (hgen : ∀ g ∈ y0Of T Mc M ⊔ T, ∀ z ∈ rcOf Mc M, ∀ hxM : g * z * g⁻¹ ∈ M,
      P (QuotientGroup.mk ⟨g * z * g⁻¹, hxM⟩)) :
    ∀ x ∈ Wc T Mc M, ∀ hxM : x ∈ M, P (QuotientGroup.mk ⟨x, hxM⟩) := by
  have key : ∀ x ∈ Wc T Mc M, ∃ hxM : x ∈ M, P (QuotientGroup.mk ⟨x, hxM⟩) := by
    intro x hx
    unfold Wc conjClosure at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨g, hg, z, hz, rfl⟩ := hx
      have hgM : g ∈ M := sup_le (y0Of_le T Mc M) h.T_le hg
      have hxM : g * z * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hgM (h.rc_le_M hz)) (M.inv_mem hgM)
      exact ⟨hxM, hgen g hg z hz hxM⟩
    | one =>
      refine ⟨M.one_mem, ?_⟩
      have : (⟨1, M.one_mem⟩ : ↥M) = 1 := rfl
      rw [this, QuotientGroup.mk_one]
      exact h1
    | mul x y _ _ ihx ihy =>
      obtain ⟨hxM, hx'⟩ := ihx
      obtain ⟨hyM, hy'⟩ := ihy
      refine ⟨M.mul_mem hxM hyM, ?_⟩
      have : (⟨x * y, M.mul_mem hxM hyM⟩ : ↥M) = ⟨x, hxM⟩ * ⟨y, hyM⟩ := rfl
      rw [this, QuotientGroup.mk_mul]
      exact hmul _ _ hx' hy'
    | inv x _ ihx =>
      obtain ⟨hxM, hx'⟩ := ihx
      refine ⟨M.inv_mem hxM, ?_⟩
      have : (⟨x⁻¹, M.inv_mem hxM⟩ : ↥M) = (⟨x, hxM⟩ : ↥M)⁻¹ := rfl
      rw [this, QuotientGroup.mk_inv]
      exact hinv _ hx'
  intro x hx hxM
  obtain ⟨hxM', hP⟩ := key x hx
  exact hP

theorem Ls_le_closure : Ls T Mc M ≤
    Subgroup.closure {x : OTwoQuot M | x ∈ Ls T Mc M ∧ ∃ m : ℕ, x ^ 2 ^ m = 1} := by
  intro u hu
  obtain ⟨x, hxM, hxW, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
  refine Wc_induction h (P := fun u => u ∈
    Subgroup.closure {x : OTwoQuot M | x ∈ Ls T Mc M ∧ ∃ m : ℕ, x ^ 2 ^ m = 1})
    (Subgroup.one_mem _) (fun a b ha hb => Subgroup.mul_mem _ ha hb)
    (fun a ha => Subgroup.inv_mem _ ha) ?_ x hxW hxM
  intro g hg z hz hxM
  apply Subgroup.subset_closure
  have hgW : g * z * g⁻¹ ∈ Wc T Mc M :=
    Subgroup.subset_closure ⟨g, hg, z, hz, rfl⟩
  refine ⟨mem_imageOTwoQuot_iff.mpr ⟨_, hxM, hgW, rfl⟩, ?_⟩
  obtain ⟨k, hk⟩ := rc_isPGroup Mc M ⟨z, hz⟩
  refine ⟨k, ?_⟩
  have hzk : z ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  rw [← QuotientGroup.mk_pow]
  have : (⟨g * z * g⁻¹, hxM⟩ : ↥M) ^ 2 ^ k = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [conj_pow, hzk]
    group
  rw [this]
  exact QuotientGroup.mk_one _

theorem K_central : ∀ k ∈ Ys T Mc M ⊓ (piStar h).ker, ∀ x ∈ Ls T Mc M, x * k = k * x := by
  intro k hk x hx
  obtain ⟨x', hxM, hxW, rfl⟩ := mem_imageOTwoQuot_iff.mp hx
  refine Wc_induction h (P := fun u => u * k = k * u) (by simp)
    (fun a b ha hb => by rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc])
    (fun a ha => (Commute.inv_left (show Commute a k from ha)).eq) ?_ x' hxW hxM
  intro g hg z hz hxM
  have hgM : g ∈ M := sup_le (y0Of_le T Mc M) h.T_le hg
  have hzM : z ∈ M := h.rc_le_M hz
  set gs : OTwoQuot M := QuotientGroup.mk ⟨g, hgM⟩ with hgs
  set zs : OTwoQuot M := QuotientGroup.mk ⟨z, hzM⟩ with hzs
  have hx : (QuotientGroup.mk ⟨g * z * g⁻¹, hxM⟩ : OTwoQuot M) = gs * zs * gs⁻¹ := by
    rw [hgs, hzs, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rfl
  have hgsN : gs ∈ Subgroup.normalizer (Ys T Mc M : Set (OTwoQuot M)) :=
    imageOTwoQuot_le_normalizer (M := M) (y0Of_sup_T_le_normalizer_yOf T Mc M)
      (mem_imageOTwoQuot_iff.mpr ⟨g, hgM, hg, rfl⟩)
  have hk' : gs⁻¹ * k * gs ∈ Ys T Mc M ⊓ (piStar h).ker := by
    refine ⟨?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgsN) k).mp hk.1
      simpa using this
    · refine MonoidHom.mem_ker.mpr ?_
      rw [map_mul, map_mul, MonoidHom.mem_ker.mp hk.2, mul_one, map_inv, inv_mul_cancel]
  have hk'' : gs⁻¹ * k * gs ∈ Y0s T Mc M ⊓ (piStar h).ker := ⟨Ys_le_Y0s h hk'.1, hk'.2⟩
  have hzsR : zs ∈ Rcs Mc M := mem_imageOTwoQuot_iff.mpr ⟨z, hzM, hz, rfl⟩
  have hc := Rcs_centralizes h zs hzsR _ hk''
  rw [hx]
  calc gs * zs * gs⁻¹ * k = gs * (zs * (gs⁻¹ * k * gs)) * gs⁻¹ := by group
    _ = gs * ((gs⁻¹ * k * gs) * zs) * gs⁻¹ := by rw [hc]
    _ = k * (gs * zs * gs⁻¹) := by group

theorem piStar_mem_of_mem_Ys {u : OTwoQuot M} (hu : u ∈ Ys T Mc M) :
    piStar h u ∈ oTwoUpper (mBar0 T Mc M) := by
  rw [← map_Y0s h]
  exact Subgroup.mem_map_of_mem _ (Ys_le_Y0s h hu)

theorem Ys_odd (hE : Odd (Nat.card (oTwoUpper (mBar0 T Mc M)))) :
    Odd (Nat.card (Ys T Mc M)) := by
  by_contra hne
  have h2 : 2 ∣ Nat.card (Ys T Mc M) := by
    rcases Nat.even_or_odd (Nat.card (Ys T Mc M)) with he | ho
    · exact even_iff_two_dvd.mp he
    · exact absurd ho hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Ys T Mc M) 2 h2
  have hu2 : orderOf (u : OTwoQuot M) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
  have hsq : (u : OTwoQuot M) ^ 2 = 1 := by
    have := pow_orderOf_eq_one (u : OTwoQuot M)
    rwa [hu2] at this
  have hπu : piStar h u ∈ oTwoUpper (mBar0 T Mc M) := piStar_mem_of_mem_Ys h u.2
  have hπ2 : (⟨piStar h u, hπu⟩ : ↥(oTwoUpper (mBar0 T Mc M))) ^ 2 = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow, hsq, map_one]
  have : Finite ↥(oTwoUpper (mBar0 T Mc M)) :=
    Nat.finite_of_card_ne_zero (fun h0 => by rw [h0] at hE; exact Nat.not_odd_zero hE)
  have h1 := eq_one_of_sq_eq_one_of_odd_card hE hπ2
  have hπ1 : piStar h u = 1 := congrArg Subtype.val h1
  have hmem : (u : OTwoQuot M) ∈ Ys T Mc M ⊓ (piStar h).ker := ⟨u.2, hπ1⟩
  have hodd := Ys_inf_ker_odd h _ hmem
  rw [hu2] at hodd
  exact absurd hodd (by decide)

theorem K_eq_bot_of_abelian (hE : Odd (Nat.card (oTwoUpper (mBar0 T Mc M))))
    (hab : ∀ a ∈ Ys T Mc M, ∀ b ∈ Ys T Mc M, a * b = b * a) :
    Ys T Mc M ⊓ (piStar h).ker = ⊥ :=
  eq_bot_of_central_of_abelian (L := Ls T Mc M) (Y := Ys T Mc M)
    (Ys_le_Ls h) (Ls_le_normalizer_Ys h) (Ys_eq_oTwoUpper_Ls h) (Ys_odd h hE)
    (Ls_le_closure h) hab inf_le_left (K_central h)

theorem K_le_commutator (hE : Odd (Nat.card (oTwoUpper (mBar0 T Mc M)))) :
    Ys T Mc M ⊓ (piStar h).ker ≤ ⁅Ys T Mc M, Ys T Mc M⁆ :=
  le_commutator_of_central (L := Ls T Mc M) (Y := Ys T Mc M)
    (Ys_le_Ls h) (Ls_le_normalizer_Ys h) (Ys_eq_oTwoUpper_Ls h) (Ys_odd h hE)
    (Ls_le_closure h) inf_le_left (K_central h)

theorem commutator_le_K (hEab : ∀ a ∈ oTwoUpper (mBar0 T Mc M), ∀ b ∈ oTwoUpper (mBar0 T Mc M),
    a * b = b * a) : ⁅Ys T Mc M, Ys T Mc M⁆ ≤ Ys T Mc M ⊓ (piStar h).ker := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  refine ⟨(Ys T Mc M).mul_mem ((Ys T Mc M).mul_mem ((Ys T Mc M).mul_mem ha hb)
    ((Ys T Mc M).inv_mem ha)) ((Ys T Mc M).inv_mem hb), ?_⟩
  refine MonoidHom.mem_ker.mpr ?_
  have hcomm := hEab _ (piStar_mem_of_mem_Ys h ha) _ (piStar_mem_of_mem_Ys h hb)
  have : piStar h ⁅a, b⁆ = ⁅piStar h a, piStar h b⁆ := map_commutatorElement _ _ _
  rw [this]
  exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm

end Data

end S152Y

end CFSG.Quasithin
