module

public import CFSG.Quasithin.Vol2.Ch12Sec2Indec
public import CFSG.Quasithin.Vol2.Ch12Sec2Models
public import CFSG.LieType.SteinbergBREvenSymplecticThreeRank

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative Pointwise

section Natural

theorem mulVec_tGL_eq_self {K : Type} [Field K] [CharP K 2] {w : Fin 2 → K}
    (h : ((CFSG.LieType.SteinbergBR.EvenSp.tGL (K := K) : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K).mulVec w = w) : w = 0 := by
  change (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) K).mulVec w = w at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  have hw0 : w 0 = 0 := by linear_combination h1
  funext i
  fin_cases i
  · simpa using hw0
  · simp only [Fin.mk_one, Pi.zero_apply]
    rw [h0, hw0]

variable {V : Type*} [CommGroup V]

theorem exists_pow_three_fixedPointFree_of_binaryNaturalSL {H : Subgroup (MulAut V)} {a : ℕ}
    (h : BinaryNaturalSL H ⊤ ⊥ 2 a) : ∃ x ∈ H, x ^ 3 = 1 ∧ ∀ v : V, x v = v → v = 1 := by
  obtain ⟨K, _, _, hK, π, -, -, -, -, -, -, -, β, -, hβ1, hβeq⟩ := h
  have : CharP K 2 := CFSG.SectionRank.charP_two_of_card hK
  have hmem : CFSG.LieType.SteinbergBR.EvenSp.tGL (K := K) ∈ StatedSL 2 K :=
    Subgroup.subset_closure CFSG.LieType.SteinbergBR.EvenSp.det_tGL
  set g : ↥(StatedSL 2 K) := ⟨_, hmem⟩ with hg
  refine ⟨(π g : MulAut V), (π g).2, ?_, fun v hv => ?_⟩
  · have hg3 : g ^ 3 = 1 := Subtype.ext CFSG.LieType.SteinbergBR.EvenSp.tGL_pow_three
    have h3 : π g ^ 3 = 1 := (map_pow π g 3).symm.trans ((congrArg π hg3).trans (map_one π))
    rw [← Subgroup.coe_pow, h3, Subgroup.coe_one]
  · obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨v, trivial⟩)
    have key := hβeq g ⟨v, trivial⟩ m trivial (Subgroup.mem_top _) hm.symm
    simp only [hv] at key
    rw [← hm, QuotientGroup.eq, Subgroup.mem_subgroupOf] at key
    have h1 : m⁻¹ * ⟨(FFModel.nat (StatedSL 2 K)).act g m.1, Subgroup.mem_top _⟩ = 1 :=
      Subtype.ext (Subgroup.mem_bot.mp key)
    rw [inv_mul_eq_one] at h1
    have h2 : (FFModel.nat (StatedSL 2 K)).act g m.1 = m.1 := (congrArg Subtype.val h1).symm
    have h3 : ((CFSG.LieType.SteinbergBR.EvenSp.tGL (K := K) : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd m.1) = Multiplicative.toAdd m.1 :=
      congrArg Multiplicative.toAdd h2
    have hm1 : m = 1 := Subtype.ext (Multiplicative.toAdd.injective (mulVec_tGL_eq_self h3))
    have : β ⟨v, trivial⟩ = 1 := by rw [← hm, hm1]; rfl
    exact (hβ1 _).mp this

end Natural

section Alternating

theorem exists_two_fixed_of_pow_three {σ : Equiv.Perm (Fin 5)} (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1) :
    ∃ d e : Fin 5, d ≠ e ∧ σ d = d ∧ σ e = e := by
  have hdvd : ∀ m ∈ σ.cycleType, m ∣ 3 := fun m hm =>
    (Equiv.Perm.dvd_of_mem_cycleType hm).trans (orderOf_dvd_of_pow_eq_one h3)
  have hm3 : ∀ m ∈ σ.cycleType, m = 3 := fun m hm => by
    have h2 := Equiv.Perm.two_le_of_mem_cycleType hm
    have h3' := Nat.le_of_dvd (by norm_num) (hdvd m hm)
    interval_cases m
    · exact absurd (hdvd 2 hm) (by decide)
    · rfl
  have hsum := Equiv.Perm.sum_cycleType σ
  have hcard : σ.support.card ≤ 5 := by simpa using Finset.card_le_univ σ.support
  have hk := Multiset.eq_replicate_card.mpr hm3
  rw [hk, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hk0 : σ.cycleType.card ≠ 0 := by
    intro h0
    rw [Multiset.card_eq_zero, Equiv.Perm.cycleType_eq_zero] at h0
    exact h1 h0
  have hsupp : σ.support.card = 3 := by omega
  have hcompl : (σ.supportᶜ).card = 2 := by rw [Finset.card_compl, hsupp]; simp
  obtain ⟨d, e, hde, hdeq⟩ := Finset.card_eq_two.mp hcompl
  have hd : d ∈ σ.supportᶜ := by rw [hdeq]; simp
  have he : e ∈ σ.supportᶜ := by rw [hdeq]; simp
  exact ⟨d, e, hde, Equiv.Perm.notMem_support.mp (Finset.mem_compl.mp hd),
    Equiv.Perm.notMem_support.mp (Finset.mem_compl.mp he)⟩

abbrev pairVec (d e : Fin 5) : G6.PermMod 5 :=
  Multiplicative.ofAdd (Pi.single d (1 : ZMod 2) + Pi.single e 1)

theorem pairVec_mem_coreMod (d e : Fin 5) : pairVec d e ∈ G6.coreMod 5 := by
  rw [G6.mem_coreMod]
  simp only [pairVec, toAdd_ofAdd, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single',
    Finset.mem_univ, ite_true]
  decide

theorem pairVec_ne_one {d e : Fin 5} (hde : d ≠ e) : pairVec d e ≠ 1 := by
  intro h
  have := congrFun (congrArg Multiplicative.toAdd h) d
  simp [pairVec, hde.symm] at this

theorem mk_pairVec_ne_one {d e : Fin 5} (hde : d ≠ e) :
    (QuotientGroup.mk ⟨pairVec d e, pairVec_mem_coreMod d e⟩ :
      ↥(FFModel.altDn 5).sec ⧸ (FFModel.altDn 5).ker.subgroupOf (FFModel.altDn 5).sec) ≠ 1 := by
  intro h
  have := (QuotientGroup.eq_one_iff _).mp h
  rw [Subgroup.mem_subgroupOf] at this
  exact pairVec_ne_one hde (eq_one_of_mem_zpowers_allOnes (by decide) this.1 this.2)

variable {V : Type*} [CommGroup V]

theorem exists_ne_one_of_alternatingNatural_five {H : Subgroup (MulAut V)}
    (h : AlternatingNatural H ⊤ ⊥ 5) : ∃ v : V, v ≠ 1 := by
  obtain ⟨π, -, -, -, -, -, -, -, β, hβs, -, -⟩ := h
  obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨pairVec 0 1, pairVec_mem_coreMod 0 1⟩)
  refine ⟨(u : V), fun hu1 => mk_pairVec_ne_one (d := 0) (e := 1) (by decide) ?_⟩
  rw [← hu, show u = 1 from Subtype.ext hu1, map_one]

theorem exists_fixed_of_alternatingNatural_five {H : Subgroup (MulAut V)}
    (h : AlternatingNatural H ⊤ ⊥ 5) {x : MulAut V} (hx : x ∈ H) (h3 : x ^ 3 = 1)
    (h1 : x ≠ 1) : ∃ v : V, v ≠ 1 ∧ x v = v := by
  obtain ⟨π, hπ, -, -, -, -, -, -, β, hβs, hβ1, hβeq⟩ := h
  have hs5 : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup (FFModel.altDn 5).Gam := hs5
  have hinj : Function.Injective π := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with hk | hk
    · exact (MonoidHom.ker_eq_bot_iff π).mp hk
    · exfalso
      obtain ⟨σ, hσ⟩ := hπ ⟨x, hx⟩
      have h1' : π σ = 1 := (MonoidHom.mem_ker).mp (hk ▸ Subgroup.mem_top σ)
      rw [h1'] at hσ
      exact h1 (congrArg Subtype.val hσ).symm
  obtain ⟨σ, hσ⟩ := hπ ⟨x, hx⟩
  have hσ3 : σ ^ 3 = 1 := by
    apply hinj
    have hx3 : π σ ^ 3 = 1 := by
      rw [hσ]
      exact Subtype.ext (by simpa using h3)
    rw [map_pow, hx3, map_one]
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [map_one] at hσ
    exact h1 (congrArg Subtype.val hσ).symm
  let σ' : ↥(alternatingGroup (Fin 5)) := σ
  have hσ'3 : σ' ^ 3 = 1 := hσ3
  have hσ'1 : σ' ≠ 1 := hσ1
  obtain ⟨d, e, hde, hd, he⟩ := exists_two_fixed_of_pow_three (σ := (σ' : Equiv.Perm (Fin 5)))
    (by rw [← Subgroup.coe_pow, hσ'3]; rfl) (fun h => hσ'1 (Subtype.ext h))
  have hyσ : G6.permAct 5 (σ' : Equiv.Perm (Fin 5)) (pairVec d e) = pairVec d e := by
    apply Multiplicative.toAdd.injective
    funext i
    rw [G6.permAct_apply]
    simp only [pairVec, toAdd_ofAdd, Pi.add_apply, Pi.single_apply, Equiv.Perm.inv_eq_iff_eq, hd,
      he]
  obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨pairVec d e, pairVec_mem_coreMod d e⟩)
  refine ⟨(u : V), fun hu1 => mk_pairVec_ne_one hde ?_, ?_⟩
  · rw [← hu, show u = 1 from Subtype.ext hu1, map_one]
  · have key := hβeq σ u ⟨pairVec d e, pairVec_mem_coreMod d e⟩ trivial
      (G6.permAct_mem_coreMod _ (pairVec_mem_coreMod d e)) hu
    have hact : (FFModel.altDn 5).act σ
        ((⟨pairVec d e, pairVec_mem_coreMod d e⟩ : ↥(FFModel.altDn 5).sec) :
          (FFModel.altDn 5).Amb) = pairVec d e := hyσ
    simp only [hact] at key
    rw [← hu] at key
    have h2 := (hβ1 (⟨((π σ : ↥H) : MulAut V) u, trivial⟩ * u⁻¹)).mp
      (by rw [map_mul, map_inv, key, mul_inv_cancel])
    rw [Subgroup.mem_bot] at h2
    have h3 : ((π σ : ↥H) : MulAut V) u = u := by
      have := congrArg (· * (u : V)) h2
      simpa using this
    rw [hσ] at h3
    exact h3

end Alternating

theorem naturalSL24NotA5Sum : NaturalSL24NotA5Sum := by
  intro G _ _ L V _ hLV hnat hirr hA5
  have hfixA5 : ∀ (W : Subgroup G) [IsMulCommutative ↥W], L ≤ Subgroup.normalizer (W : Set G) →
      AlternatingNatural (V := ↥W) (autOn L W) ⊤ ⊥ 5 →
        (Subgroup.centralizer (L : Set G)).subgroupOf W = ⊥ := fun W _ hLW halt =>
    (fixV_autOn_eq hLW).symm.trans
      (fixV_eq_bot_of_alternatingNatural ⟨2, by norm_num⟩ (by norm_num) halt)
  have hnt : ∀ (W : Subgroup G) [IsMulCommutative ↥W],
      AlternatingNatural (V := ↥W) (autOn L W) ⊤ ⊥ 5 → W ≠ ⊥ := fun W _ halt hW => by
    obtain ⟨w, hw⟩ := exists_ne_one_of_alternatingNatural_five halt
    apply hw
    have h1 : (w : G) ∈ W := w.2
    have h2 := hW.le h1
    rw [Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  rcases hA5 with ⟨-, _, halt⟩ | ⟨W₁, W₂, ⟨hLW₁, _, halt₁⟩, ⟨hLW₂, _, halt₂⟩, hW, hWV⟩
  ·
    rw [hfixA5 V hLV halt] at hnat
    obtain ⟨x, hxH, hx3, hfree⟩ := exists_pow_three_fixedPointFree_of_binaryNaturalSL hnat
    obtain ⟨w, hw⟩ := exists_ne_one_of_alternatingNatural_five halt
    have hx1 : x ≠ 1 := fun h => hw (hfree w (by rw [h]; rfl))
    obtain ⟨v, hv1, hvx⟩ := exists_fixed_of_alternatingNatural_five halt hxH hx3 hx1
    exact hv1 (hfree v hvx)
  ·
    have hW₁V : W₁ ≤ V := by rw [← hWV]; exact le_sup_left
    have hW₂V : W₂ ≤ V := by rw [← hWV]; exact le_sup_right
    have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
      congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥V) ⟨y, hy⟩)
    have hfix₁ : ∀ w ∈ W₁, w ∈ Subgroup.centralizer (L : Set G) → w = 1 := fun w hw hwC => by
      have : (⟨w, hw⟩ : ↥W₁) ∈ (Subgroup.centralizer (L : Set G)).subgroupOf W₁ := hwC
      rw [hfixA5 W₁ hLW₁ halt₁, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    have hCV : V ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
      have hset : ((W₁ ⊔ W₂ : Subgroup G) : Set G) = (W₁ : Set G) * (W₂ : Set G) :=
        Subgroup.coe_mul_of_left_le_normalizer_right W₁ W₂
          (le_normalizer_of_le_of_commute hVc hW₁V hW₂V)
      rw [eq_bot_iff]
      rintro v ⟨hvV, hvC⟩
      rw [← hWV] at hvV
      have hv' : v ∈ (W₁ : Set G) * (W₂ : Set G) := hset ▸ hvV
      obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := hv'
      have hw₁C : w₁ ∈ Subgroup.centralizer (L : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        have hc1 : l * w₁ * l⁻¹ ∈ W₁ := (Subgroup.mem_normalizer_iff.mp (hLW₁ hl) w₁).mp hw₁
        have hc2 : l * w₂ * l⁻¹ ∈ W₂ := (Subgroup.mem_normalizer_iff.mp (hLW₂ hl) w₂).mp hw₂
        have hlv : l * (w₁ * w₂) = w₁ * w₂ * l :=
          Subgroup.mem_centralizer_iff.mp hvC l hl
        have hab : (l * w₁ * l⁻¹) * (l * w₂ * l⁻¹) = w₁ * w₂ := by
          calc (l * w₁ * l⁻¹) * (l * w₂ * l⁻¹) = l * (w₁ * w₂) * l⁻¹ := by group
            _ = w₁ * w₂ * l * l⁻¹ := by rw [hlv]
            _ = w₁ * w₂ := by group
        have hkey : (l * w₁ * l⁻¹) * w₁⁻¹ = w₂ * (l * w₂ * l⁻¹)⁻¹ := by
          have ha : l * w₁ * l⁻¹ = w₁ * (w₂ * (l * w₂ * l⁻¹)⁻¹) := by
            calc l * w₁ * l⁻¹ = (l * w₁ * l⁻¹) * (l * w₂ * l⁻¹) * (l * w₂ * l⁻¹)⁻¹ := by group
              _ = w₁ * w₂ * (l * w₂ * l⁻¹)⁻¹ := by rw [hab]
              _ = w₁ * (w₂ * (l * w₂ * l⁻¹)⁻¹) := by group
          have hx : w₂ * (l * w₂ * l⁻¹)⁻¹ ∈ V := hW₂V (W₂.mul_mem hw₂ (W₂.inv_mem hc2))
          rw [ha, hVc w₁ (hW₁V hw₁) _ hx]
          group
        have hmem : (l * w₁ * l⁻¹) * w₁⁻¹ ∈ W₁ ⊓ W₂ :=
          ⟨W₁.mul_mem hc1 (W₁.inv_mem hw₁), by rw [hkey]; exact W₂.mul_mem hw₂ (W₂.inv_mem hc2)⟩
        rw [hW, Subgroup.mem_bot, mul_inv_eq_one] at hmem
        calc l * w₁ = l * w₁ * l⁻¹ * l := by group
          _ = w₁ * l := by rw [hmem]
      have hw₂C : w₂ ∈ Subgroup.centralizer (L : Set G) := by
        have := (Subgroup.centralizer (L : Set G)).mul_mem
          ((Subgroup.centralizer (L : Set G)).inv_mem hw₁C) hvC
        simpa using this
      show w₁ * w₂ ∈ ⊥
      rw [hfix₁ w₁ hw₁ hw₁C, one_mul]
      have hW₂fix : (⟨w₂, hw₂⟩ : ↥W₂) ∈ (Subgroup.centralizer (L : Set G)).subgroupOf W₂ := hw₂C
      rw [hfixA5 W₂ hLW₂ halt₂, Subgroup.mem_bot] at hW₂fix
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val hW₂fix)
    rcases hirr W₁ (by rw [hCV]; exact bot_le) hW₁V hLW₁ with h | h
    · exact hnt W₁ halt₁ (h.trans hCV)
    · apply hnt W₂ halt₂
      rw [eq_bot_iff, ← hW]
      exact le_inf (hW₂V.trans h.ge) le_rfl

end CFSG.Quasithin.H13
