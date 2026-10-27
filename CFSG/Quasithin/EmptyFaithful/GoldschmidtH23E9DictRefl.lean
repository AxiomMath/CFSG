module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9ModVE
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9ModOdd
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23Six5BHelp
public import CFSG.Quasithin.EmptyFaithful.S151bRank
public import CFSG.Quasithin.EmptyFaithful.T1515A
public import CFSG.Quasithin.EmptyFaithful.T1515C6Gl

public section

namespace CFSG.Quasithin.E9

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

structure ReflData (T Mc M : Subgroup G) {hVe : IsElemAbelian 2 (V154 T Mc M)}
    (d : Six5Data T M (V154 T Mc M) hVe) (x₁ x₂ : MulAut (IntMod (V154 T Mc M) hVe)) : Prop where
  x₁_mem : x₁ ∈ d.S.A₁ ⊓ autI hVe T
  x₂_mem : x₂ ∈ d.S.A₂ ⊓ autI hVe T
  x₁_two : orderOf x₁ = 2
  x₂_two : orderOf x₂ = 2
  closure_eq : autI hVe T ⊓ (d.S.A₁ ⊔ d.S.A₂) = Subgroup.closure {x₁, x₂}
  jbar : autI hVe (thompsonJi T 1) = Subgroup.closure {x₁, x₂}
  vE : vE1516 T Mc M = (d.S.vEMod x₁ x₂).map (valHomI hVe)

theorem twoPart_eq_of_card' {Y : Type*} [Group Y] {X : Subgroup Y} {k m : ℕ} (hm : ¬ 2 ∣ m)
    (h : Nat.card X = 2 ^ k * m) : twoPart X = 2 ^ k := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero 2)
  unfold twoPart
  rw [h, Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hm]
  simp

omit [Finite G] in
theorem le_normalizer_of_commute {L R : Subgroup G} (hc : ∀ x ∈ L, ∀ y ∈ R, x * y = y * x) :
    R ≤ Subgroup.normalizer (L : Set G) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hc' : ∀ a ∈ L, b * a * b⁻¹ = a := fun a ha => by
    rw [← hc a ha b hb]
    group
  constructor
  · intro hh
    rw [hc' h hh]
    exact hh
  · intro hh
    have e : b⁻¹ * (b * h * b⁻¹) * b = b * h * b⁻¹ := by
      have h1 := hc _ hh b⁻¹ (R.inv_mem hb)
      calc b⁻¹ * (b * h * b⁻¹) * b = ((b * h * b⁻¹) * b⁻¹) * b := by rw [h1]
        _ = b * h * b⁻¹ := by group
    have h2 : h = b * h * b⁻¹ := by
      calc h = b⁻¹ * (b * h * b⁻¹) * b := by group
        _ = b * h * b⁻¹ := e
    rw [h2]
    exact hh

section Reflections

variable {X : Type*} [Group X] [Finite X]

theorem exists_involution_of_sylow {Tb A₀ A : Subgroup X} {m : ℕ} (hm : ¬ 2 ∣ m)
    (hS : IsSylowTwoOf (Tb ⊓ A₀) A₀) (hAA₀ : A ≤ A₀) (hn : A₀ ≤ Subgroup.normalizer (A : Set X))
    (hcard : Nat.card A = 2 * m) : ∃ x ∈ A ⊓ Tb, orderOf x = 2 := by
  have h1 : IsSylowTwoOf ((Tb ⊓ A₀) ⊓ A) A := A4.isSylowTwoOf_inf_normal hS hAA₀ hn
  have h2 : (Tb ⊓ A₀) ⊓ A = Tb ⊓ A := by
    rw [inf_assoc, inf_eq_right.mpr hAA₀]
  rw [h2] at h1
  have h3 : twoPart A = 2 := by
    have := twoPart_eq_of_card' (X := A) (k := 1) hm (by rw [hcard]; ring)
    simpa using this
  have h4 : Nat.card ↥(Tb ⊓ A) = 2 := by rw [h1.card_eq, h3]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Tb ⊓ A)) 2 (by rw [h4])
  exact ⟨(x : X), ⟨x.2.2, x.2.1⟩, (Subgroup.orderOf_coe x).trans hx⟩

end Reflections

variable {T Mc M : Subgroup G} {hVe : IsElemAbelian 2 (V154 T Mc M)}
  (d : Six5Data T M (V154 T Mc M) hVe)

theorem exists_reflData (h5 : Ce15Six T Mc M 5) (h113 : Lemma15113Four T Mc M) :
    ∃ x₁ x₂ : MulAut (IntMod (V154 T Mc M) hVe), ReflData T Mc M d x₁ x₂ := by
  have hA0M : d.S.A₁ ⊔ d.S.A₂ ≤ autI hVe M := by
    rw [d.hsup]
    exact Jhat_le _
  have hnormA : autI hVe M ≤ Subgroup.normalizer ((d.S.A₁ ⊔ d.S.A₂ : Subgroup _) : Set _) := by
    intro g hg
    exact Subgroup.mem_normalizer_fintype fun n hn => d.hnorm g hg n hn
  have hTb : IsSylowTwoOf (autI hVe T) (autI hVe M) := isSylowTwoOf_autOn' d.hsyl d.hMN
  have hS0 : IsSylowTwoOf (autI hVe T ⊓ (d.S.A₁ ⊔ d.S.A₂)) (d.S.A₁ ⊔ d.S.A₂) :=
    A4.isSylowTwoOf_inf_normal hTb hA0M hnormA
  have hcard₁ : Nat.card d.S.A₁ = 2 * 5 := by
    rw [Nat.card_congr d.S.e₁.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
  have hcard₂ : Nat.card d.S.A₂ = 2 * 5 := by
    rw [Nat.card_congr d.S.e₂.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
  have hn₁ : d.S.A₁ ⊔ d.S.A₂ ≤ Subgroup.normalizer (d.S.A₁ : Set _) :=
    sup_le Subgroup.le_normalizer (le_normalizer_of_commute d.S.comm)
  have hn₂ : d.S.A₁ ⊔ d.S.A₂ ≤ Subgroup.normalizer (d.S.A₂ : Set _) :=
    sup_le (le_normalizer_of_commute fun x hx y hy => (d.S.comm y hy x hx).symm)
      Subgroup.le_normalizer
  obtain ⟨x₁, hx₁, hx₁2⟩ := exists_involution_of_sylow (m := 5) (by norm_num) hS0 le_sup_left
    hn₁ hcard₁
  obtain ⟨x₂, hx₂, hx₂2⟩ := exists_involution_of_sylow (m := 5) (by norm_num) hS0 le_sup_right
    hn₂ hcard₂
  have hA0card : Nat.card (d.S.A₁ ⊔ d.S.A₂ : Subgroup _) = 2 ^ 2 * 25 := by
    have h := (card_sup_mul_card_inf_of_commute151b d.S.A₁ d.S.A₂ d.S.comm).1
    rw [d.S.inf, Subgroup.card_bot, mul_one, hcard₁, hcard₂] at h
    rw [h]
    norm_num
  have hPcard : Nat.card ↥(autI hVe T ⊓ (d.S.A₁ ⊔ d.S.A₂)) = 4 := by
    rw [hS0.card_eq, twoPart_eq_of_card' (k := 2) (m := 25) (by norm_num) hA0card]
    norm_num
  have hcl : autI hVe T ⊓ (d.S.A₁ ⊔ d.S.A₂) = Subgroup.closure {x₁, x₂} := by
    have hle : Subgroup.closure ({x₁, x₂} : Set (MulAut (IntMod (V154 T Mc M) hVe))) ≤
        autI hVe T ⊓ (d.S.A₁ ⊔ d.S.A₂) := by
      rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      · exact ⟨hx₁.2, Subgroup.mem_sup_left hx₁.1⟩
      · exact ⟨hx₂.2, Subgroup.mem_sup_right hx₂.1⟩
    have hc : Nat.card (Subgroup.closure ({x₁, x₂} :
        Set (MulAut (IntMod (V154 T Mc M) hVe)))) = 4 := by
      have hcomm : ∀ a ∈ Subgroup.zpowers x₁, ∀ b ∈ Subgroup.zpowers x₂, a * b = b * a := by
        intro a ha b hb
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        have h1 : ∀ n : ℤ, x₂ ^ n ∈ d.S.A₂ := fun n => d.S.A₂.zpow_mem hx₂.1 n
        have h2 : ∀ m : ℤ, x₁ ^ m ∈ d.S.A₁ := fun m => d.S.A₁.zpow_mem hx₁.1 m
        exact d.S.comm _ (h2 m) _ (h1 n)
      have h := (card_sup_mul_card_inf_of_commute151b (Subgroup.zpowers x₁) (Subgroup.zpowers x₂)
        hcomm).1
      have hinf : Subgroup.zpowers x₁ ⊓ Subgroup.zpowers x₂ = ⊥ := by
        rw [eq_bot_iff]
        intro y hy
        have hy1 : y ∈ d.S.A₁ := (Subgroup.zpowers_le.mpr hx₁.1) hy.1
        have hy2 : y ∈ d.S.A₂ := (Subgroup.zpowers_le.mpr hx₂.1) hy.2
        have : y ∈ d.S.A₁ ⊓ d.S.A₂ := ⟨hy1, hy2⟩
        rw [d.S.inf] at this
        exact this
      rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hx₁2, hx₂2] at h
      have hclo : Subgroup.closure ({x₁, x₂} : Set (MulAut (IntMod (V154 T Mc M) hVe))) =
          Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ := by
        apply le_antisymm
        · rw [Subgroup.closure_le]
          rintro y (rfl | rfl)
          · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
          · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
        · exact sup_le (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
            (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
      rw [hclo]
      omega
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hPcard, hc])).symm
  have hJbar : autI hVe (thompsonJi T 1) = autI hVe T ⊓ (d.S.A₁ ⊔ d.S.A₂) := by
    rcases h113 with ⟨h1, -⟩ | ⟨h3, -⟩
    · have hm : mBar0 T Mc M = d.S.A₁ ⊔ d.S.A₂ := (JhatOn_eq hVe).trans d.hsup.symm
      rw [hm] at h1
      exact h1
    · exfalso
      have h4 := h3.1
      have h6 := h5.card_eq
      omega
  refine ⟨x₁, x₂, ⟨hx₁, hx₂, hx₁2, hx₂2, hcl, hJbar.trans hcl, ?_⟩⟩
  have hJT : thompsonJi T 1 ≤ T := iSup₂_le fun _ hA => hA.1
  have hJN : thompsonJi T 1 ≤ Subgroup.normalizer (V154 T Mc M : Set G) := hJT.trans d.hTN
  have hfix : fixV (autI hVe (thompsonJi T 1)) = d.S.vEMod x₁ x₂ := by
    rw [hJbar.trans hcl]
    exact d.S.fixV_closure_pair hx₁.1 hx₂.1
  ext g
  constructor
  · rintro ⟨hgV, hgC⟩
    let w : IntMod (V154 T Mc M) hVe := IntMod.mk hVe ⟨g, hgV⟩
    have hw : w ∈ fixV (autI hVe (thompsonJi T 1)) := by
      rw [mem_fixV]
      intro φ hφ
      obtain ⟨j, hj, rfl⟩ := (mem_autI hVe).1 hφ
      apply IntMod.val_injective
      rw [← conj_val j.2]
      have := Subgroup.mem_centralizer_iff.mp hgC j hj
      show (j : G) * g * (j : G)⁻¹ = g
      rw [this]
      group
    rw [hfix] at hw
    exact Subgroup.mem_map.2 ⟨w, hw, rfl⟩
  · intro hg
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hg
    rw [← hfix] at hw
    refine ⟨IntMod.val_mem w, Subgroup.mem_centralizer_iff.mpr fun j hj => ?_⟩
    have h1 : convI hVe ⟨j, hJN hj⟩ w = w :=
      mem_fixV.mp hw _ (convI_mem_autI hVe hj (hJN hj))
    have h2 := conj_val (hV := hVe) (hJN hj) w
    rw [h1] at h2
    show j * IntMod.val w = IntMod.val w * j
    calc j * IntMod.val w = (j * IntMod.val w * j⁻¹) * j := by group
      _ = IntMod.val w * j := by rw [h2]

variable {d}

theorem ReflData.z₁_eq {x₁ x₂ : MulAut (IntMod (V154 T Mc M) hVe)} (r : ReflData T Mc M d x₁ x₂)
    {Z₁ V₁ : Subgroup G} (hZ : Z₁ = vE1516 T Mc M ⊓ V₁) (hV : V₁ = d.V₁) :
    Z₁ = (d.S.W₁ ⊓ fixV (Subgroup.zpowers x₁)).map (valHomI hVe) := by
  rw [hZ, hV, r.vE]
  unfold Six5Data.V₁
  rw [← Subgroup.map_inf _ _ _ (IntMod.val_injective (hV := hVe)), d.S.vEMod_inf_W₁]

theorem ReflData.z₂_eq {x₁ x₂ : MulAut (IntMod (V154 T Mc M) hVe)} (r : ReflData T Mc M d x₁ x₂)
    {Z₂ V₂ : Subgroup G} (hZ : Z₂ = vE1516 T Mc M ⊓ V₂) (hV : V₂ = d.V₂) :
    Z₂ = (d.S.W₂ ⊓ fixV (Subgroup.zpowers x₂)).map (valHomI hVe) := by
  rw [hZ, hV, r.vE]
  unfold Six5Data.V₂
  rw [← Subgroup.map_inf _ _ _ (IntMod.val_injective (hV := hVe)), d.S.vEMod_inf_W₂]

theorem ReflData.card_z₁ {x₁ x₂ : MulAut (IntMod (V154 T Mc M) hVe)}
    (r : ReflData T Mc M d x₁ x₂) :
    Nat.card ((d.S.W₁ ⊓ fixV (Subgroup.zpowers x₁)).map (valHomI hVe)) = 4 := by
  rw [Subgroup.card_map_of_injective (IntMod.val_injective (hV := hVe))]
  exact d.S.card_fix_reflection₁ (fun w => IntMod.sq_eq_one w) d.hcard r.x₁_mem.1 r.x₁_two

end CFSG.Quasithin.E9
