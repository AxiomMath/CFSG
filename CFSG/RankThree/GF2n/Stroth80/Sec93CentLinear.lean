module

public import CFSG.CGT.Timmesfeld75.ListWCAlt
public import CFSG.CGT.Timmesfeld75.ListWCAlt9
public import CFSG.RankThree.GF2n.Stroth80.Sec93CentConj
public import CFSG.RankThree.GF2n.Stroth80.Sec93TransvCentralizer

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

theorem centralizer_le_of_psl {G : Type} [Group G] {m : ℕ} (hm : 3 ≤ m) {K : Type} [Field K]
    [Finite K] [CharP K 2] (e : G ≃* StatedProj (StatedSL m K)) {T : Subgroup G} (hT : IsWC T)
    (hT1 : T ≠ ⊥) {x : G} (hx : x ∈ Subgroup.centralizer (T : Set G)) : x ∈ T := by
  have hcomm : ∀ t ∈ T, e x * e t = e t * e x := fun t ht => by
    rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.1 hx t ht).symm]
  have hy : ∀ y ∈ T.map e.toMonoidHom, e x * y = y * e x := by
    rintro _ ⟨t, ht, rfl⟩
    exact hcomm t ht
  obtain ⟨-, hid, -⟩ := lin_wc hm e hT hT1
  have hmem : e x ∈ T.map e.toMonoidHom := by
    rcases hid with ⟨c, hc, hTc⟩ | ⟨a, ha, hTa⟩
    · rw [hTc] at hy ⊢
      exact mem_transvImage_center_of_centralizes (by omega) hc hy
    · rw [hTa] at hy ⊢
      exact mem_transvImage_axis_of_centralizes (by omega) ha hy
  obtain ⟨t, ht, hte⟩ := hmem
  have : t = x := e.injective hte
  rwa [← this]

theorem centralizer_le_of_alt_eight {G : Type} [Group G]
    (e : G ≃* alternatingGroup (Fin 8)) {T : Subgroup G} (hT : IsWC T) (hT1 : T ≠ ⊥) {x : G}
    (hx : x ∈ Subgroup.centralizer (T : Set G)) : x ∈ T := by
  obtain ⟨e'⟩ := nonempty_mulEquiv_psl_of_alt_eight e
  exact centralizer_le_of_psl (m := 4) (by norm_num) e' hT hT1 hx

theorem mem_of_mul_self_eq_one_alt67 {G : Type} [Group G] [Finite G] {k : ℕ} (hk6 : 6 ≤ k)
    (hk7 : k ≤ 7) (e : G ≃* alternatingGroup (Fin k)) {T : Subgroup G} (hT : IsElemAbelian 2 T)
    (h4 : 4 ≤ Nat.card T) {x : G} (hx : x ∈ Subgroup.centralizer (T : Set G))
    (hx2 : x * x = 1) : x ∈ T := by
  by_contra hxT
  obtain ⟨E, hTE, hE⟩ := exists_isElemAbelian_gt hT hx hx2 hxT
  obtain ⟨m, hm, hcard⟩ := exists_card_alt_eq_eight_mul hk6 hk7
  obtain ⟨hσ4, hσ2⟩ := altFourCycle_pow hk6 hk7
  have hlt : Nat.card T < Nat.card E := Subgroup.card_lt_of_lt hTE
  have h4E : 4 ≤ Nat.card E := h4.trans hlt.le
  have := card_eq_four_of_two_part_eight hm (by rw [Nat.card_congr e.toEquiv, hcard])
    (e.symm (altFourCycle k hk6)) (by rw [← map_pow, hσ4, map_one]) (fun h => hσ2 ?_) hE h4E
  · omega
  · rw [← map_pow] at h
    exact e.symm.injective (h.trans (map_one _).symm)

theorem mem_of_mul_self_eq_one_alt_nine {G : Type} [Group G]
    (e : G ≃* alternatingGroup (Fin 9)) {T : Subgroup G} (hT : IsWC T) (hT1 : T ≠ ⊥) {x : G}
    (hx : x ∈ Subgroup.centralizer (T : Set G)) (hx2 : x * x = 1) : x ∈ T := by
  suffices key : ∀ T₁ : Subgroup (alternatingGroup (Fin 9)), IsWC T₁ → T₁ ≠ ⊥ →
      ∀ x₁ ∈ Subgroup.centralizer (T₁ : Set (alternatingGroup (Fin 9))), x₁ * x₁ = 1 →
        x₁ ∈ T₁ by
    have h := key (T.map e.toMonoidHom) (hT.map_mulEquiv e)
      (fun h => hT1 ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h)) (e x) (by
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨t, ht, rfl⟩
        show e t * e x = e x * e t
        rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hx t ht]) (by
        rw [← map_mul, hx2, map_one])
    obtain ⟨t, ht, hte⟩ := h
    have : t = x := e.injective hte
    rwa [← this]
  intro T₁ hT₁ hT₁1 x₁ hx₁ hx₁2
  have hx₁2' : x₁ ^ 2 = 1 := by rw [pow_two]; exact hx₁2
  have hc : ∀ a ∈ T₁, ∀ b ∈ Subgroup.zpowers x₁, a * b = b * a := by
    intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    have : Commute a x₁ := Subgroup.mem_centralizer_iff.1 hx₁ a ha
    exact (this.zpow_right n).eq
  have hE : IsElemAbelian 2 (T₁ ⊔ Subgroup.zpowers x₁) :=
    IsElemAbelian.sup_of_commute hT₁.1 (isElemAbelian_zpowers hx₁2') hc
  obtain ⟨p, hp⟩ := exists_fixed_point_of_isPGroup_nine (isPGroup_two_of_isElemAbelian hE)
  have : MulAction.IsPretransitive (alternatingGroup (Fin 9)) (Fin 9) :=
    alternatingGroup.isPretransitive_of_three_le_card (Fin 9) (by simp)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 9)) p 0
  have hgp : (g : Equiv.Perm (Fin 9)) p = 0 := hg
  have hfix : ∀ t ∈ conjSubgroup g (T₁ ⊔ Subgroup.zpowers x₁),
      (t : Equiv.Perm (Fin 9)) 0 = 0 := by
    intro t ht
    rw [mem_conjSubgroup] at ht
    have h1 := hp _ ht
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply, hgp] at h1
    rw [Equiv.Perm.inv_eq_iff_eq, hgp] at h1
    exact h1
  have hT₂ : IsWC (conjSubgroup g T₁) := hT₁.conj g
  have hT₂1 : conjSubgroup g T₁ ≠ ⊥ := fun h => hT₁1 (by
    rw [← conjSubgroup_inj (g := g), h]
    exact (Subgroup.map_bot _).symm)
  have hTE : T₁ ≤ T₁ ⊔ Subgroup.zpowers x₁ := le_sup_left
  have hle : conjSubgroup g T₁ ≤ alt8to9.range := fun t ht =>
    mem_range_alt8to9 (hfix t (Subgroup.map_mono hTE ht))
  have hxE : x₁ ∈ T₁ ⊔ Subgroup.zpowers x₁ := Subgroup.mem_sup_right (Subgroup.mem_zpowers x₁)
  have hx₂E : g * x₁ * g⁻¹ ∈ conjSubgroup g (T₁ ⊔ Subgroup.zpowers x₁) := by
    rw [mem_conjSubgroup]
    simpa [mul_assoc] using hxE
  obtain ⟨x₃, hx₃⟩ := mem_range_alt8to9 (hfix _ hx₂E)
  have hT₃ := hT₂.comap_of_injective alt8to9_injective hle
  have hmap : ((conjSubgroup g T₁).comap alt8to9).map alt8to9 = conjSubgroup g T₁ :=
    Subgroup.map_comap_eq_self hle
  have hT₃1 : (conjSubgroup g T₁).comap alt8to9 ≠ ⊥ := fun h =>
    hT₂1 (by rw [← hmap, h, Subgroup.map_bot])
  have hx₃c : x₃ ∈ Subgroup.centralizer (((conjSubgroup g T₁).comap alt8to9 :
      Subgroup (alternatingGroup (Fin 8))) : Set (alternatingGroup (Fin 8))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply alt8to9_injective
    rw [map_mul, map_mul, hx₃]
    have hy' : alt8to9 y ∈ conjSubgroup g T₁ := hy
    rw [mem_conjSubgroup] at hy'
    have hxc := Subgroup.mem_centralizer_iff.1 hx₁ _ hy'
    calc alt8to9 y * (g * x₁ * g⁻¹)
        = g * ((g⁻¹ * alt8to9 y * g) * x₁) * g⁻¹ := by group
      _ = g * (x₁ * (g⁻¹ * alt8to9 y * g)) * g⁻¹ := by rw [hxc]
      _ = (g * x₁ * g⁻¹) * alt8to9 y := by group
  have hx₃T : x₃ ∈ (conjSubgroup g T₁).comap alt8to9 :=
    centralizer_le_of_alt_eight (MulEquiv.refl _) hT₃ hT₃1 hx₃c
  have hx₂T : g * x₁ * g⁻¹ ∈ conjSubgroup g T₁ := by
    rw [← hx₃]
    exact hx₃T
  rw [mem_conjSubgroup] at hx₂T
  simpa [mul_assoc] using hx₂T

end CFSG.RankThree.GF2n.Stroth80
