module

public import CFSG.Quasithin.EmptyFaithful.S146zUC2Model

public section

namespace CFSG.Quasithin.S146zU.UC2

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Commutator

variable {V : Type} [CommGroup V]

theorem range_commHom_le (x : MulAut V) : (commHom x).range ≤ commV (Subgroup.zpowers x) := by
  rintro _ ⟨v, rfl⟩
  exact Subgroup.subset_closure ⟨x, Subgroup.mem_zpowers x, v, rfl⟩

theorem card_sup_le_mul {G : Type} [CommGroup G] [Finite G] (A B : Subgroup G) :
    Nat.card ↥(A ⊔ B) ≤ Nat.card ↥A * Nat.card ↥B := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_surjective
    (fun p : ↥A × ↥B => (⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem_sup p.1.2 p.2.2⟩ : ↥(A ⊔ B))) ?_
  rintro ⟨x, hx⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hx
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩

theorem range_commHom_mul_le (u v : MulAut V) :
    (commHom (u * v)).range ≤ (commHom v).range.map u.toMonoidHom ⊔ (commHom u).range := by
  rintro _ ⟨w, rfl⟩
  have h : commHom (u * v) w = u (commHom v w) * commHom u w := by
    simp only [commHom_apply, MulAut.mul_apply, map_mul, map_inv]
    group
  rw [h]
  exact Subgroup.mul_mem_sup ⟨commHom v w, ⟨w, rfl⟩, rfl⟩ ⟨w, rfl⟩

theorem card_range_commHom_mul [Finite V] (u v : MulAut V) :
    Nat.card ↥(commHom (u * v)).range ≤
      Nat.card ↥(commHom u).range * Nat.card ↥(commHom v).range := by
  refine (Subgroup.card_le_of_le (range_commHom_mul_le u v)).trans ?_
  refine (card_sup_le_mul _ _).trans ?_
  rw [mul_comm]
  exact Nat.mul_le_mul_left _ (Subgroup.card_map_of_injective u.injective).le

theorem range_commHom_conj_le (k x : MulAut V) :
    (commHom (k * x * k⁻¹)).range ≤ (commHom x).range.map k.toMonoidHom := by
  rintro _ ⟨w, rfl⟩
  refine ⟨commHom x (k⁻¹ w), ⟨k⁻¹ w, rfl⟩, ?_⟩
  simp only [commHom_apply, MulAut.mul_apply, map_mul, map_inv, MulEquiv.coe_toMonoidHom]
  simp

theorem card_range_commHom_conj [Finite V] (k x : MulAut V) :
    Nat.card ↥(commHom (k * x * k⁻¹)).range ≤ Nat.card ↥(commHom x).range :=
  (Subgroup.card_le_of_le (range_commHom_conj_le k x)).trans
    (Subgroup.card_map_of_injective k.injective).le

theorem range_commHom_inv_le (x : MulAut V) :
    (commHom x⁻¹).range ≤ (commHom x).range.map x⁻¹.toMonoidHom := by
  rintro _ ⟨w, rfl⟩
  refine ⟨commHom x w⁻¹, ⟨w⁻¹, rfl⟩, ?_⟩
  simp only [commHom_apply, map_mul, map_inv, MulEquiv.coe_toMonoidHom]
  simp

theorem card_range_commHom_inv [Finite V] (x : MulAut V) :
    Nat.card ↥(commHom x⁻¹).range ≤ Nat.card ↥(commHom x).range :=
  (Subgroup.card_le_of_le (range_commHom_inv_le x)).trans
    (Subgroup.card_map_of_injective x⁻¹.injective).le

end Commutator

section Bound

variable {V : Type} [CommGroup V] {K₁ K₂ : Type} [Field K₁] [Field K₂] {L₁ L₂ : Subgroup (MulAut V)}
  {C : Subgroup V} {Φ : ↥(StatedSL 2 K₁) × ↥(StatedSL 2 K₂) →* MulAut V}
  {Θ : V →* Multiplicative (Fin 2 → K₁) × Multiplicative (Fin 2 → K₂)}

theorem sixteen_le_of_mul {c f r : ℕ} (hc : 0 < c) (hf : f ≤ 4096) (h : c * 65536 ≤ c * f * r) :
    16 ≤ r := by
  by_contra hr
  have hr' : r ≤ 15 := by omega
  have h1 : c * f * r ≤ c * 4096 * 15 := Nat.mul_le_mul (Nat.mul_le_mul_left c hf) hr'
  nlinarith

theorem IsPairModel.card_range_commHom_ge [Finite V] [Finite K₁] [Finite K₂]
    (hM : IsPairModel L₁ L₂ C Φ Θ) (hK₁ : Nat.card K₁ = 16) (hK₂ : Nat.card K₂ = 16)
    {g : ↥(StatedSL 2 K₁) × ↥(StatedSL 2 K₂)} (hg : g ≠ 1) :
    16 ≤ Nat.card ↥(commHom (Φ g)).range := by
  have hV := hM.card_V
  rw [hK₁, hK₂] at hV
  have hV' := card_eq_card_ker_mul_card_range (commHom (Φ g))
  have hker : Nat.card ↥(commHom (Φ g)).ker ≤ Nat.card ↥C *
      (Nat.card ↥(fixNat (Subgroup.zpowers g.1)) * Nat.card ↥(fixNat (Subgroup.zpowers g.2))) := by
    have h := hM.card_fixV_le (Subgroup.zpowers g)
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h
    rw [ker_commHom]
    exact h
  have hcpos : 0 < Nat.card ↥C := Nat.card_pos
  have hF₂ : ∀ {K : Type} [Field K] [Finite K], Nat.card K = 16 →
      ∀ B : Subgroup ↥(StatedSL 2 K), Nat.card ↥(fixNat B) ≤ 256 := by
    intro K _ _ hK B
    have := Subgroup.card_le_card_group (fixNat B)
    rw [card_multiplicative_fin_two_fun, hK] at this
    simpa using this
  have hmul : Nat.card V = Nat.card ↥C * 65536 := by
    rw [hV]
    ring
  by_cases h1 : g.1 = 1
  · have h2 : g.2 ≠ 1 := fun h2 => hg (Prod.ext h1 h2)
    have hb : Subgroup.zpowers g.2 ≠ ⊥ := fun hb => h2 (Subgroup.zpowers_eq_bot.mp hb)
    have hf₂ : Nat.card ↥(fixNat (Subgroup.zpowers g.2)) ≤ 16 := by
      have := card_fixNat_le_of_ne_bot hb
      rwa [hK₂] at this
    have hf₁ := hF₂ hK₁ (Subgroup.zpowers g.1)
    refine sixteen_le_of_mul hcpos (f := Nat.card ↥(fixNat (Subgroup.zpowers g.1)) *
      Nat.card ↥(fixNat (Subgroup.zpowers g.2))) ?_ ?_
    · calc Nat.card ↥(fixNat (Subgroup.zpowers g.1)) * Nat.card ↥(fixNat (Subgroup.zpowers g.2))
          ≤ 256 * 16 := Nat.mul_le_mul hf₁ hf₂
        _ = 4096 := by norm_num
    · rw [← hmul, hV']
      calc Nat.card ↥(commHom (Φ g)).ker * Nat.card ↥(commHom (Φ g)).range
          ≤ (Nat.card ↥C * (Nat.card ↥(fixNat (Subgroup.zpowers g.1)) *
            Nat.card ↥(fixNat (Subgroup.zpowers g.2)))) * Nat.card ↥(commHom (Φ g)).range :=
            Nat.mul_le_mul_right _ hker
        _ = _ := by ring
  · have hb : Subgroup.zpowers g.1 ≠ ⊥ := fun hb => h1 (Subgroup.zpowers_eq_bot.mp hb)
    have hf₁ : Nat.card ↥(fixNat (Subgroup.zpowers g.1)) ≤ 16 := by
      have := card_fixNat_le_of_ne_bot hb
      rwa [hK₁] at this
    have hf₂ := hF₂ hK₂ (Subgroup.zpowers g.2)
    refine sixteen_le_of_mul hcpos (f := Nat.card ↥(fixNat (Subgroup.zpowers g.1)) *
      Nat.card ↥(fixNat (Subgroup.zpowers g.2))) ?_ ?_
    · calc Nat.card ↥(fixNat (Subgroup.zpowers g.1)) * Nat.card ↥(fixNat (Subgroup.zpowers g.2))
          ≤ 16 * 256 := Nat.mul_le_mul hf₁ hf₂
        _ = 4096 := by norm_num
    · rw [← hmul, hV']
      calc Nat.card ↥(commHom (Φ g)).ker * Nat.card ↥(commHom (Φ g)).range
          ≤ (Nat.card ↥C * (Nat.card ↥(fixNat (Subgroup.zpowers g.1)) *
            Nat.card ↥(fixNat (Subgroup.zpowers g.2)))) * Nat.card ↥(commHom (Φ g)).range :=
            Nat.mul_le_mul_right _ hker
        _ = _ := by ring

theorem IsPairModel.card_range_commHom_ge_of_mem [Finite V] [Finite K₁] [Finite K₂]
    (hM : IsPairModel L₁ L₂ C Φ Θ) (hK₁ : Nat.card K₁ = 16) (hK₂ : Nat.card K₂ = 16)
    {l : MulAut V} (hl : l ∈ L₁ ⊔ L₂) (hl1 : l ≠ 1) : 16 ≤ Nat.card ↥(commHom l).range := by
  obtain ⟨g, rfl⟩ := (hM.mem_iff l).mp hl
  refine hM.card_range_commHom_ge hK₁ hK₂ (fun h => hl1 ?_)
  rw [h, map_one]

theorem IsPairModel.card_range_commHom_ge_four [Finite V] [Finite K₁] [Finite K₂]
    (hM : IsPairModel L₁ L₂ C Φ Θ) (hK₁ : Nat.card K₁ = 16) (hK₂ : Nat.card K₂ = 16)
    {Γ : Subgroup (MulAut V)} (hn : ∀ x ∈ Γ, ∀ l ∈ L₁ ⊔ L₂, x * l * x⁻¹ ∈ L₁ ⊔ L₂)
    (hcen : ∀ x ∈ Γ, (∀ l ∈ L₁ ⊔ L₂, x * l = l * x) → x = 1)
    {x : MulAut V} (hx : x ∈ Γ) (hx1 : x ≠ 1) : 4 ≤ Nat.card ↥(commHom x).range := by
  by_contra hlt
  have h3 : Nat.card ↥(commHom x).range ≤ 3 := by omega
  apply hx1
  refine hcen x hx (fun k hk => ?_)
  set c : MulAut V := x⁻¹ * (k * x * k⁻¹) with hc
  have hcL : c ∈ L₁ ⊔ L₂ := by
    have h1 : x⁻¹ * k * (x⁻¹)⁻¹ ∈ L₁ ⊔ L₂ := hn x⁻¹ (Γ.inv_mem hx) k hk
    have h2 : c = (x⁻¹ * k * (x⁻¹)⁻¹) * k⁻¹ := by
      rw [hc]
      group
    rw [h2]
    exact Subgroup.mul_mem _ h1 ((L₁ ⊔ L₂).inv_mem hk)
  have hcard : Nat.card ↥(commHom c).range ≤ 9 := by
    calc Nat.card ↥(commHom c).range
        ≤ Nat.card ↥(commHom x⁻¹).range * Nat.card ↥(commHom (k * x * k⁻¹)).range :=
          card_range_commHom_mul _ _
      _ ≤ 3 * 3 := Nat.mul_le_mul ((card_range_commHom_inv x).trans h3)
          ((card_range_commHom_conj k x).trans h3)
      _ = 9 := by norm_num
  have hc1 : c = 1 := by
    by_contra hne
    have := hM.card_range_commHom_ge_of_mem hK₁ hK₂ hcL hne
    omega
  have h4 : k * x * k⁻¹ = x := by
    have : x⁻¹ * (k * x * k⁻¹) = 1 := hc1
    exact (mul_eq_one_iff_eq_inv.mp this ▸ (inv_inv x).symm).symm
  calc x * k = (k * x * k⁻¹) * k := by rw [h4]
    _ = k * x := by group

end Bound

section Headline

variable {V : Type} [CommGroup V] [Finite V]

theorem nt_of_twoNat {Γ L₁ L₂ : Subgroup (MulAut V)} {τ : MulAut V} (h : S153M.TwoNat L₁ L₂ τ)
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (hL₁ : Nat.card ↥L₁ = 4080)
    (hL₂ : Nat.card ↥L₂ = 4080) (hn : ∀ x ∈ Γ, ∀ l ∈ L₁ ⊔ L₂, x * l * x⁻¹ ∈ L₁ ⊔ L₂)
    (hcen : ∀ x ∈ Γ, (∀ l ∈ L₁ ⊔ L₂, x * l = l * x) → x = 1) {x : MulAut V} (hx : x ∈ Γ)
    (hx1 : x ≠ 1) : 4 ≤ Nat.card ↥(commV (Subgroup.zpowers x)) := by
  obtain ⟨K₁, K₂, _, _, _, _, Φ, Θ, hK₁, hK₂, hM⟩ := exists_pairModel h hcomm hL₁ hL₂
  exact (hM.card_range_commHom_ge_four hK₁ hK₂ hn hcen hx hx1).trans
    (Subgroup.card_le_of_le (range_commHom_le x))

end Headline

end CFSG.Quasithin.S146zU.UC2
