module

public import CFSG.RankThree.PartOne.S12.Sec1510Fit
public import CFSG.RankThree.PartOne.S12.Sec15Frattini
public import CFSG.RankThree.PartOne.S12.Sec159Hom

public section

namespace CFSG.RankThree.PartOne

open CFSG

namespace Sec1510

variable {H : Type} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]

theorem Y_le_gen {V Lh E P N₀ : Subgroup H} [V.Normal] {e : H}
    (hVp : ¬ p ∣ Nat.card ↥V)
    (hLlayer : Lh.map (QuotientGroup.mk' V) = layer (H ⧸ V))
    (hA : ∀ M : Subgroup (H ⧸ V), M.Normal → Group.IsNilpotent ↥M → ¬ p ∣ Nat.card ↥M → M = ⊥)
    (heE : e ∈ E) (he1 : e ≠ 1) (hecent : ∀ h : H, h * e = e * h)
    (hEexp : ∀ x ∈ E, x ^ p = 1)
    (hPsyl : IsSylowOf p P ⊤) (hEP : E ≤ P) (hPΩ : omegaOne p P = E)
    (hPc : ∀ x ∈ P, ∀ y ∈ E, x * y = y * x)
    (hPN : P ≤ N₀) (hVN : V ≤ N₀) (hWN : Subgroup.normalizer (E : Set H) ≤ N₀)
    (hND : ¬ IsCyclic ↥(E ⊓ (Subgroup.centralizer
        ((Lh.map (QuotientGroup.mk' V) : Subgroup (H ⧸ V)) : Set (H ⧸ V))).comap
        (QuotientGroup.mk' V)) →
      Subgroup.normalizer ((E ⊓ (Subgroup.centralizer
        ((Lh.map (QuotientGroup.mk' V) : Subgroup (H ⧸ V)) : Set (H ⧸ V))).comap
        (QuotientGroup.mk' V) : Subgroup H) : Set H) ≤ N₀)
    (hInn : ∀ x ∈ E, ∃ l ∈ E ⊓ Lh, ∃ c ∈ E ⊓ Subgroup.centralizer (Lh : Set H), x = l * c)
    {y : H} (hy : ∀ l ∈ Lh, y * l * y⁻¹ * l⁻¹ ∈ V) : y ∈ N₀ := by
  classical
  have hπ : Function.Surjective (QuotientGroup.mk' V) := QuotientGroup.mk'_surjective V
  have hYbn : (Subgroup.centralizer (layer (H ⧸ V) : Set (H ⧸ V))).Normal := centralizer_layer_normal
  obtain ⟨Qb, hQbY, hQbN, hQbp, hQbC, hQbZ⟩ := fitting_layer_centralizer p hA
  rw [← hLlayer] at hYbn hQbY hQbN hQbC
  set π := QuotientGroup.mk' V with hπdef
  set Yb := Subgroup.centralizer ((Lh.map π : Subgroup (H ⧸ V)) : Set (H ⧸ V)) with hYbdef
  set Y := Yb.comap π with hY
  set Qt := Qb.comap π with hQt
  have hYn : Y.Normal := hYbn.comap π
  have hπV : ∀ v ∈ V, π v = 1 := fun v hv => (QuotientGroup.eq_one_iff v).2 hv
  have hyY : y ∈ Y := by
    show π y ∈ Yb
    rw [hYbdef, Subgroup.mem_centralizer_iff]
    rintro _ ⟨l, hl, rfl⟩
    have h1 := hπV _ (hy l hl)
    have h2 : π (y * l * y⁻¹ * l⁻¹) = π y * π l * (π y)⁻¹ * (π l)⁻¹ := by simp
    rw [h2] at h1
    have h3 : π y * π l = π l * π y := by
      have := congrArg (fun z => z * π l * π y) h1
      simpa [mul_assoc] using this
    exact h3.symm
  have hQtY : Qt ≤ Y := fun x hx => hQbY hx
  have hQtN : ∀ g ∈ Y, g ∈ Subgroup.normalizer (Qt : Set H) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hg' : g⁻¹ ∈ Y := Y.inv_mem hg
    constructor
    · intro hh
      show π (g * h * g⁻¹) ∈ Qb
      rw [map_mul, map_mul]
      exact hQbN (π g) hg (π h) hh
    · intro hh
      have : π (g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹) ∈ Qb := by
        rw [map_mul, map_mul]
        exact hQbN (π g⁻¹) hg' _ hh
      have e1 : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
      rw [e1] at this
      exact this
  have hPsyl' : CFSG.ABGLocalTools.IsSylowOf p P ⊤ := CFSG.ABGLocalTools.isSylowOf_iff.2 hPsyl
  have hYnorm : (⊤ : Subgroup H) ≤ Subgroup.normalizer (Y : Set H) := by
    intro g _
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨fun hx => hYn.conj_mem x hx g, fun hx => by
      simpa [mul_assoc] using hYn.conj_mem _ hx g⁻¹⟩
  have hPY : CFSG.ABGLocalTools.IsSylowOf p (P ⊓ Y) Y :=
    hPsyl'.inf_of_le_normalizer le_top hYnorm
  have hQsyl0 : CFSG.ABGLocalTools.IsSylowOf p ((P ⊓ Y) ⊓ Qt) Qt :=
    hPY.inf_of_le_normalizer hQtY (fun g hg => hQtN g hg)
  have hPYQ : (P ⊓ Y) ⊓ Qt = P ⊓ Qt := by
    ext x; simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hQtY h.2⟩, h.2⟩⟩
  rw [hPYQ] at hQsyl0
  set Q := P ⊓ Qt with hQ
  have hQeq : Qt = V ⊔ Q := by
    have := Sec15Frattini.comap_eq_sup_of_sylow π hπ hQbp hQsyl0
    rwa [QuotientGroup.ker_mk'] at this
  have hQP : Q ≤ P := inf_le_left
  have hQtN₀ : Qt ≤ N₀ := by
    rw [hQeq]; exact sup_le hVN (hQP.trans hPN)
  have hΩQ : omegaOne p Q ≤ E := by
    rw [← hPΩ]
    exact Subgroup.closure_mono fun x ⟨hx, hx1⟩ => ⟨hQP hx, hx1⟩
  set R := omegaOne p Q with hR
  have hB1 : ∀ x ∈ E, π x ∈ Yb → x ∈ R := by
    intro x hxE hxY
    have hmem : π x ∈ Qb := by
      refine hQbC (π x) hxY ?_
      intro q hq
      obtain ⟨h, rfl⟩ := hπ q
      have hh : h ∈ Qt := hq
      rw [hQeq] at hh
      obtain ⟨v, hv, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hh
      have hcomm := hPc w hw.1 x hxE
      simp only [map_mul, hπV v hv, one_mul]
      rw [← map_mul, ← map_mul, hcomm]
    exact Subgroup.subset_closure ⟨⟨hEP hxE, hmem⟩, hEexp x hxE⟩
  have hRY : R = E ⊓ Y := by
    apply le_antisymm
    · refine le_inf hΩQ fun x hx => ?_
      have hxQ : x ∈ Q := (Subgroup.closure_le Q).2 (fun z hz => hz.1) hx
      have hxQ' : x ∈ P ⊓ Qt := hQ ▸ hxQ
      exact hQtY hxQ'.2
    · exact fun x hx => hB1 x hx.1 hx.2
  by_cases hcyc : IsCyclic ↥R
  ·
    have hπe : π e ∈ Yb := by
      rw [hYbdef, Subgroup.mem_centralizer_iff]
      intro z _
      obtain ⟨h, rfl⟩ := hπ z
      rw [← map_mul, ← map_mul, hecent h]
    have heR : e ∈ R := hB1 e heE hπe
    have hordE : orderOf e = p := orderOf_eq_prime (hEexp e heE) he1
    have hdvd : Nat.card ↥R ∣ p := by
      obtain ⟨g, hg⟩ := hcyc.exists_generator
      have hord : orderOf g = Nat.card ↥R := orderOf_eq_card_of_forall_mem_zpowers hg
      rw [← hord]
      exact orderOf_dvd_of_pow_eq_one (Subtype.ext (hEexp g (hΩQ g.2)))
    have hpR : p ∣ Nat.card ↥R := by
      have := orderOf_dvd_natCard (⟨e, heR⟩ : ↥R)
      rwa [Subgroup.orderOf_mk, hordE] at this
    have hcardR : Nat.card ↥R = p := Nat.dvd_antisymm hdvd hpR
    have hzR : Subgroup.zpowers e = R :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 heR)
        (by rw [hcardR, Nat.card_zpowers, hordE])
    have hEY : ∀ x ∈ E, π x ∈ Yb → x ∈ Subgroup.zpowers e := fun x hx hxY => hzR ▸ hB1 x hx hxY
    have hB4 : ∀ r ∈ E, y * r * y⁻¹ ∈ V ⊔ E := by
      intro r hr
      obtain ⟨l, hl, c, hc, rfl⟩ := hInn r hr
      have hcY : π c ∈ Yb := by
        rw [hYbdef, Subgroup.mem_centralizer_iff]
        rintro _ ⟨l', hl', rfl⟩
        have := Subgroup.mem_centralizer_iff.1 hc.2 l' hl'
        rw [← map_mul, ← map_mul, this]
      have hcz : c ∈ Subgroup.zpowers e := hEY c hc.1 hcY
      have hccent : y * c = c * y := by
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hcz
        exact (Commute.zpow_right (hecent y : Commute y e) j).eq
      have hv : y * l * y⁻¹ * l⁻¹ ∈ V := hy l hl.2
      have : y * (l * c) * y⁻¹ = (y * l * y⁻¹ * l⁻¹) * (l * c) := by
        calc y * (l * c) * y⁻¹ = (y * l * y⁻¹) * (y * c * y⁻¹) := by group
          _ = (y * l * y⁻¹) * c := by rw [hccent]; group
          _ = (y * l * y⁻¹ * l⁻¹) * (l * c) := by group
      rw [this]
      exact (V ⊔ E).mul_mem (Subgroup.mem_sup_left hv)
        (Subgroup.mem_sup_right (E.mul_mem hl.1 hc.1))
    have hEp : IsPGroup p ↥E := hPsyl.2.1.to_le hEP
    have hEsyl : CFSG.ABGLocalTools.IsSylowOf p E (V ⊔ E) :=
      Sec15Frattini.isSylowOf_sup_of_coprime hEp hVp
    obtain ⟨k, hk, hkn⟩ := Sec15Frattini.exists_mem_normalizer_of_normal hEsyl hB4
    have h3 := N₀.mul_mem (hVN hk) (hWN hkn)
    simpa using h3
  ·
    obtain ⟨k, hk, hkn⟩ := Sec15Frattini.exists_mem_normalizer_of_isSylowOf hQsyl0 (hQtN y hyY)
    have h1 : Subgroup.normalizer (R : Set H) ≤ N₀ := by
      rw [hRY]
      exact hND (hRY ▸ hcyc)
    have h2 : k⁻¹ * y ∈ Subgroup.normalizer ((omegaOne p Q : Subgroup H) : Set H) :=
      Sec159Cfg.normalizer_le_normalizer_omegaOne hkn
    have h3 := N₀.mul_mem (hQtN₀ hk) (h1 h2)
    simpa using h3

end Sec1510

end CFSG.RankThree.PartOne
