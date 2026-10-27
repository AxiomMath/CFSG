module

public import CFSG.RankThree.Co2.CentA
public import CFSG.RankThree.Co2.W0Cert
public import CFSG.RankThree.Co2.Lemma210

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.Co2

open CFSG.Monster CFSG.Monster.B.Co2 CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Census CFSG.Monster.B.TwoA.Co2Inv

theorem w0GenWords_letters : ∀ k < w0GenWords.size, ∀ l ∈ w0GenWords[k]!, l < 42 := by
  decide +kernel

theorem mem_W0_iff_crMat {y : Cr} :
    y ∈ subW w0GenWords ↔ crMat y ∈ matGrp w0GenWords :=
  mem_subW_iff_crMat w0GenWords_letters

theorem inA_iff_clsA {x : Matrix (Fin 22) (Fin 22) (ZMod 2)} : InA x ↔ ClsA x := by
  simp [InA, ClsA]

theorem inB_iff_clsB {x : Matrix (Fin 22) (Fin 22) (ZMod 2)} : InB x ↔ ClsB x := by
  simp [InB, ClsB]

theorem typeBA_iff_matTypeBA {y : Cr} :
    TypeBA y ↔ MatTypeBA (crMat y) := by
  rw [typeBA_iff, MatTypeBA, inA_iff_clsA, inB_iff_clsB]

theorem card_W0 : Nat.card (subW w0GenWords) = 16 := by
  rw [card_subW_eq_matGrp w0GenWords_letters]
  exact w0Facts_cert.card

theorem W0_le_W : subW w0GenWords ≤ subW wWords := fun _ hy =>
  mem_W_iff_crMat.2 (w0Facts_cert.le (mem_W0_iff_crMat.1 hy))

theorem mem_W0_cases {y : Cr} (hy : y ∈ subW w0GenWords) : y = 1 ∨ TypeBA y := by
  by_cases h1 : y = 1
  · exact Or.inl h1
  refine Or.inr (typeBA_iff_matTypeBA.2
    (w0Facts_cert.typeBA_of_mem _ (mem_W0_iff_crMat.1 hy) fun e => h1 (crMat_injective ?_)))
  rw [e, map_one]

theorem mem_W0_of_typeBA {y : Cr} (hy : y ∈ subW wWords) (ht : TypeBA y) :
    y ∈ subW w0GenWords :=
  mem_W0_iff_crMat.2
    (w0Facts_cert.mem_of_typeBA _ (mem_W_iff_crMat.1 hy) (typeBA_iff_matTypeBA.1 ht))

theorem card_P1_inf_centralizer :
    Nat.card (subW pWords1 ⊓ Subgroup.centralizer (subW wWords : Set Cr) : Subgroup Cr) ≤
      2048 := by
  refine le_trans ?_ (wFacts_cert.cent card_matP1_le)
  refine Nat.card_le_card_of_injective
    (fun y => ⟨crMat y.1, mem_P1_iff_crMat.1 (Subgroup.mem_inf.1 y.2).1, ?_⟩) ?_
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := exists_of_mem_matW hw
    rw [← map_mul, ← map_mul,
      Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 y.2).2 v hv]
  · intro y z e
    exact Subtype.ext (crMat_injective (congrArg Subtype.val e))

theorem odd_elt_facts {p : ℕ}
    {m : Matrix (Fin 22) (Fin 22) (ZMod 2)} (hm : m ∈ Cm) (hp : m ^ p = 1)
    (ha : m * repMat 1 = repMat 1 * m) (hw : ∃ w ∈ matGrp wGenWords, w * m ≠ m * w) :
    ∃ x : Cr, x ^ p = 1 ∧ x * rep 1 = rep 1 * x ∧ ∃ v ∈ subW wWords, v * x ≠ x * v := by
  obtain ⟨x, rfl⟩ := MonoidHom.mem_mrange.1 (Cm_le_mrange hm)
  have h1 : crMat (rep 1) = repMat 1 := crMat_rep (by norm_num)
  obtain ⟨w, hw, hne⟩ := hw
  obtain ⟨v, hv, rfl⟩ := exists_of_mem_matW hw
  refine ⟨x, crMat_injective ?_, crMat_injective ?_, v, hv, fun e => hne ?_⟩
  · rw [map_pow, hp, map_one]
  · rw [map_mul, map_mul, h1, ha]
  · rw [← map_mul, ← map_mul, e]

theorem x3_facts :
    ∃ x : Cr, x ^ 3 = 1 ∧ x * rep 1 = rep 1 * x ∧ ∃ v ∈ subW wWords, v * x ≠ x * v := by
  obtain ⟨m, hm, hp, ha, hw⟩ := wFacts_cert.odd3
  exact odd_elt_facts hm hp ha hw

theorem x7_facts :
    ∃ x : Cr, x ^ 7 = 1 ∧ x * rep 1 = rep 1 * x ∧ ∃ v ∈ subW wWords, v * x ≠ x * v := by
  obtain ⟨m, hm, hp, ha, hw⟩ := wFacts_cert.odd7
  exact odd_elt_facts hm hp ha hw

theorem isPGroup_of_not_mem {Q : Type*} [Group Q] [Finite Q] {N : Subgroup Q} [N.Normal]
    (hQ : Nat.card Q = 2752512) {x y : Q} (hx : x ^ 3 = 1) (hxN : x ∉ N) (hy : y ^ 7 = 1)
    (hyN : y ∉ N) : IsPGroup 2 N := by
  have hdvd : ∀ {p : ℕ}, p.Prime → ∀ {g : Q}, g ^ p = 1 → g ∉ N → p ∣ Nat.card (Q ⧸ N) := by
    intro p hp g hg hgN
    have : Fact p.Prime := ⟨hp⟩
    have ho : orderOf (QuotientGroup.mk g : Q ⧸ N) = p := by
      apply orderOf_eq_prime
      · rw [← QuotientGroup.mk_pow, hg, QuotientGroup.mk_one]
      · rw [Ne, QuotientGroup.eq_one_iff]
        exact hgN
    rw [← ho]
    exact orderOf_dvd_natCard _
  have h21 : 21 ∣ Nat.card (Q ⧸ N) := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num)
    (hdvd (by norm_num) hx hxN) (hdvd (by norm_num) hy hyN)
  obtain ⟨m, hm⟩ := h21
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  rw [hQ, hm] at hcard
  have e : m * Nat.card N = 2 ^ 17 :=
    Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 21) (by rw [← mul_assoc, ← hcard]; norm_num)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro_left m e)
  exact IsPGroup.of_card hk

namespace Co2CentHyp

variable {G : Type} [Group G] (h : Co2CentHyp G)

abbrev W0G : Subgroup G := h.liftG (subW w0GenWords)

theorem W0G_le_WG : h.W0G ≤ h.WG := by
  intro x hx
  obtain ⟨hxH, hxS⟩ := h.mem_liftG.1 hx
  exact h.mem_liftG.2 ⟨hxH, W0_le_W hxS⟩

theorem W0G_le_X0G : h.W0G ≤ h.X0G := h.W0G_le_WG.trans h.WG_le_X0G

theorem W0G_le_IG : h.W0G ≤ h.IG := fun _ hx => (Subgroup.mem_inf.1 (h.W0G_le_X0G hx)).2

theorem W0G_le_S0G : h.W0G ≤ h.S0G := h.W0G_le_WG.trans h.WG_le_S0G

theorem card_W0G : Nat.card h.W0G = 16 := by rw [card_liftG, card_W0]

theorem mem_W0G_iff {x : G} (hx : x ∈ h.X0G) :
    x ∈ h.W0G ↔ x = 1 ∨ (IsConj h.aG x ∧ IsConj h.z (x * h.aG)) := by
  constructor
  · intro hxW
    obtain ⟨hxH, hxS⟩ := h.mem_liftG.1 hxW
    rcases mem_W0_cases hxS with e | e
    · left
      have : (⟨x, hxH⟩ : h.H) = 1 := (MulEquiv.map_eq_one_iff h.φ).1 e
      exact congrArg Subtype.val this
    · exact Or.inr ((h.typeBAG_iff hx).2 e)
  · rintro (rfl | hBA)
    · exact h.W0G.one_mem
    · have hW : x ∈ h.WG := (h.mem_WG_iff hx).2 (Or.inr (Or.inr (Or.inr hBA)))
      obtain ⟨hxH, hxS⟩ := h.mem_liftG.1 hW
      exact h.mem_liftG.2 ⟨hxH, mem_W0_of_typeBA hxS ((h.typeBAG_iff hx).1 hBA)⟩

theorem mem_W0G_or_mul {x : G} (hx : x ∈ h.WG) : x ∈ h.W0G ∨ x * h.aG ∈ h.W0G := by
  have hxX := h.WG_le_X0G hx
  rcases (h.mem_WG_iff hxX).1 hx with rfl | rfl | (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact Or.inl h.W0G.one_mem
  · right
    rw [h.aG_mul_self]
    exact h.W0G.one_mem
  · right
    have hxaX : x * h.aG ∈ h.X0G := h.WG_le_X0G (h.WG.mul_mem hx h.aG_mem_WG)
    refine (h.mem_W0G_iff hxaX).2 (Or.inr ⟨h2, ?_⟩)
    rw [mul_assoc, h.aG_mul_self, mul_one]
    exact h1
  · exact Or.inl ((h.mem_W0G_iff hxX).2 (Or.inr ⟨h1, h2⟩))

theorem typeBA_conj {i : G} (hi : i ∈ h.IG) {x : G}
    (hx : IsConj h.aG x ∧ IsConj h.z (x * h.aG)) :
    IsConj h.aG (i * x * i⁻¹) ∧ IsConj h.z (i * x * i⁻¹ * h.aG) := by
  have hia : i * h.aG * i⁻¹ = h.aG := by
    rw [Subgroup.mem_centralizer_singleton_iff.1 hi, mul_inv_cancel_right]
  have e : i * x * i⁻¹ * h.aG = i * (x * h.aG) * i⁻¹ := by
    calc i * x * i⁻¹ * h.aG = i * x * i⁻¹ * (i * h.aG * i⁻¹) := by rw [hia]
      _ = i * (x * h.aG) * i⁻¹ := by group
  rw [e, isConj_conj_right, isConj_conj_right]
  exact hx

theorem conj_mem_W0G {i : G} (hi : i ∈ h.IG) {w : G} (hw : w ∈ h.W0G)
    (hiw : i * w * i⁻¹ ∈ h.X0G) : i * w * i⁻¹ ∈ h.W0G := by
  rcases (h.mem_W0G_iff (h.W0G_le_X0G hw)).1 hw with rfl | hBA
  · simp only [mul_one, mul_inv_cancel]
    exact h.W0G.one_mem
  · exact (h.mem_W0G_iff hiw).2 (Or.inr (h.typeBA_conj hi hBA))

theorem NWG_le_normalizer_W0G : h.NWG ≤ Subgroup.normalizer (h.W0G : Set G) := by
  have := h.finite
  intro n hn
  obtain ⟨hnI, hnN⟩ := Subgroup.mem_inf.1 hn
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  have hnxW : n * x * n⁻¹ ∈ h.WG := (Subgroup.mem_normalizer_iff.1 hnN x).1 (h.W0G_le_WG hx)
  exact h.conj_mem_W0G hnI hx (h.WG_le_X0G hnxW)

theorem normalizer_W0G_le_NWG :
    h.IG ⊓ Subgroup.normalizer (h.W0G : Set G) ≤ h.NWG := by
  have := h.finite
  intro n hn
  obtain ⟨hnI, hnN⟩ := Subgroup.mem_inf.1 hn
  have hna : n * h.aG * n⁻¹ = h.aG := by
    rw [Subgroup.mem_centralizer_singleton_iff.1 hnI, mul_inv_cancel_right]
  refine Subgroup.mem_inf.2 ⟨hnI, Subgroup.mem_normalizer_fintype fun x hx => ?_⟩
  rcases h.mem_W0G_or_mul hx with hx0 | hx0
  · exact h.W0G_le_WG ((Subgroup.mem_normalizer_iff.1 hnN x).1 hx0)
  · have h1 := (Subgroup.mem_normalizer_iff.1 hnN _).1 hx0
    have e : n * (x * h.aG) * n⁻¹ * h.aG = n * x * n⁻¹ := by
      calc n * (x * h.aG) * n⁻¹ * h.aG = n * (x * h.aG) * n⁻¹ * (n * h.aG * n⁻¹) := by
            rw [hna]
        _ = n * x * (h.aG * h.aG) * n⁻¹ := by group
        _ = n * x * n⁻¹ := by rw [h.aG_mul_self, mul_one]
    rw [← e]
    exact h.WG.mul_mem (h.W0G_le_WG h1) h.aG_mem_WG

theorem exists_NWG_conj {w : G} (hw : w ∈ h.W0G) (hw1 : w ≠ 1) :
    ∃ n ∈ h.NWG, n * (h.z * h.aG) * n⁻¹ = w := by
  rcases (h.mem_W0G_iff (h.W0G_le_X0G hw)).1 hw with e | ⟨hBa, hBz⟩
  · exact absurd e hw1
  have hwa : w * h.aG ∈ h.WG := h.WG.mul_mem (h.W0G_le_WG hw) h.aG_mem_WG
  have ha : IsConj h.aG (w * h.aG * h.aG) := by
    rw [mul_assoc, h.aG_mul_self, mul_one]
    exact hBa
  obtain ⟨n, hn, hnz⟩ := h.exists_normalizer_conj_z hwa (h.WG_le_X0G hwa) hBz ha
  refine ⟨n, hn, ?_⟩
  have hna : n * h.aG * n⁻¹ = h.aG := by
    rw [Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hn).1, mul_inv_cancel_right]
  calc n * (h.z * h.aG) * n⁻¹ = (n * h.z * n⁻¹) * (n * h.aG * n⁻¹) := by group
    _ = w := by rw [hnz, hna, mul_assoc, h.aG_mul_self, mul_one]

abbrev CWG : Subgroup G := h.X0G ⊓ Subgroup.centralizer (h.WG : Set G)

theorem mem_CWG_of_centralizes {x : G} (hxI : x ∈ h.IG) (hx : ∀ w ∈ h.W0G, w * x = x * w) :
    x ∈ h.CWG := by
  have hxa : h.aG * x = x * h.aG := (Subgroup.mem_centralizer_singleton_iff.1 hxI).symm
  have hW : ∀ w ∈ h.WG, w * x = x * w := by
    intro w hw
    rcases h.mem_W0G_or_mul hw with hw0 | hw0
    · exact hx w hw0
    · have h1 := hx _ hw0
      calc w * x = w * h.aG * h.aG * x := by rw [mul_assoc w, h.aG_mul_self, mul_one]
        _ = w * h.aG * x * h.aG := by rw [mul_assoc (w * h.aG), hxa, ← mul_assoc]
        _ = x * (w * h.aG) * h.aG := by rw [h1]
        _ = x * w := by rw [mul_assoc, mul_assoc, h.aG_mul_self, mul_one]
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨?_, hxI⟩, Subgroup.mem_centralizer_iff.2 hW⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (hW _ h.z_mem_WG).symm

theorem CWG_normal : (h.CWG.subgroupOf h.X0G).Normal := by
  constructor
  intro c hc g
  rw [Subgroup.mem_subgroupOf] at hc ⊢
  obtain ⟨hcX, hcC⟩ := Subgroup.mem_inf.1 hc
  show (g : G) * c * (g : G)⁻¹ ∈ h.CWG
  refine Subgroup.mem_inf.2 ⟨h.X0G.mul_mem (h.X0G.mul_mem g.2 hcX) (h.X0G.inv_mem g.2), ?_⟩
  have hgN := h.X0G_le_normalizer g.2
  rw [Subgroup.mem_centralizer_iff] at hcC ⊢
  intro k hk
  have hk' : (g : G)⁻¹ * k * g ∈ h.WG := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hgN) k).1 hk
    rwa [inv_inv] at this
  have e := hcC _ hk'
  calc k * ((g : G) * c * (g : G)⁻¹) = g * (((g : G)⁻¹ * k * g) * c) * (g : G)⁻¹ := by group
    _ = g * (c * ((g : G)⁻¹ * k * g)) * (g : G)⁻¹ := by rw [e]
    _ = (g : G) * c * (g : G)⁻¹ * k := by group

theorem φ_symm_mem_X0G {x : Cr} (hx : x * rep 1 = rep 1 * x) :
    ((h.φ.symm x : h.H) : G) ∈ h.X0G := by
  rw [h.X0G_eq]
  exact h.φ_symm_mem_liftG (Subgroup.mem_centralizer_singleton_iff.2 hx)

theorem φ_symm_not_mem_CWG {x : Cr} (hx : ∃ v ∈ subW wWords, v * x ≠ x * v) :
    ((h.φ.symm x : h.H) : G) ∉ h.CWG := by
  intro hC
  obtain ⟨v, hv, hvx⟩ := hx
  have hvG : ((h.φ.symm v : h.H) : G) ∈ h.WG := h.φ_symm_mem_liftG hv
  have hc := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hC).2 _ hvG
  have := (h.commute_iff (h.φ.symm v) x).1 hc
  rw [MulEquiv.apply_symm_apply] at this
  exact hvx this

theorem φ_symm_pow {x : Cr} {k : ℕ} (hx : x ^ k = 1) : ((h.φ.symm x : h.H) : G) ^ k = 1 := by
  rw [← Subgroup.coe_pow, ← map_pow, hx, map_one, Subgroup.coe_one]

theorem isPGroup_CWG : IsPGroup 2 h.CWG := by
  have := h.finite
  have := h.CWG_normal
  obtain ⟨_, h3p, h3c, h3w⟩ := x3_facts
  obtain ⟨_, h7p, h7c, h7w⟩ := x7_facts
  have hP := isPGroup_of_not_mem (N := h.CWG.subgroupOf h.X0G) h.card_X0G
    (x := ⟨_, h.φ_symm_mem_X0G h3c⟩) (y := ⟨_, h.φ_symm_mem_X0G h7c⟩)
    (Subtype.ext (by rw [Subgroup.coe_pow]; exact h.φ_symm_pow h3p))
    (fun hm => h.φ_symm_not_mem_CWG h3w hm)
    (Subtype.ext (by rw [Subgroup.coe_pow]; exact h.φ_symm_pow h7p))
    (fun hm => h.φ_symm_not_mem_CWG h7w hm)
  exact hP.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_left)

theorem CWG_le_S0G : h.CWG ≤ h.S0G := by
  have := h.finite
  have := h.CWG_normal
  have hS : Nat.card (h.S0G.subgroupOf h.X0G) = 2 ^ (Nat.card h.X0G).factorization 2 := by
    rw [card_subgroupOf_eq h.S0G_le_X0G, h.card_S0G, h.card_X0G,
      factorization_two_eq (by norm_num : 2752512 = 2 ^ 17 * 21) (by decide)]
    norm_num
  have hP : IsPGroup 2 (h.CWG.subgroupOf h.X0G) :=
    h.isPGroup_CWG.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_left).symm
  have hle := hP.le_sylow_of_normal (Sylow.ofCard _ hS)
  intro x hx
  have hxX : x ∈ h.X0G := (Subgroup.mem_inf.1 hx).1
  have hmem := hle (show (⟨x, hxX⟩ : h.X0G) ∈ h.CWG.subgroupOf h.X0G from hx)
  rw [Sylow.coe_ofCard, Subgroup.mem_subgroupOf] at hmem
  exact hmem

theorem card_CWG_le : Nat.card h.CWG ≤ 2048 := by
  have := h.finite
  have hle : h.CWG ≤
      h.liftG (subW pWords1 ⊓ Subgroup.centralizer (subW wWords : Set Cr)) := by
    intro x hx
    obtain ⟨hxH, hxP⟩ := h.mem_liftG.1 (h.CWG_le_S0G hx)
    refine h.mem_liftG.2 ⟨hxH, Subgroup.mem_inf.2 ⟨hxP, ?_⟩⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hvG : ((h.φ.symm v : h.H) : G) ∈ h.WG := h.φ_symm_mem_liftG hv
    have hc := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).2 _ hvG
    exact ((h.commute_iff ⟨x, hxH⟩ v).1 hc.symm).symm
  calc Nat.card h.CWG ≤
        Nat.card (h.liftG (subW pWords1 ⊓ Subgroup.centralizer (subW wWords : Set Cr))) :=
        Subgroup.card_le_of_le hle
    _ ≤ 2048 := by
      rw [card_liftG]
      exact card_P1_inf_centralizer

theorem exists_conj_JG_le_IG : ∃ g : G, ∀ y ∈ h.JG, g⁻¹ * y * g ∈ h.IG := by
  obtain ⟨x, hx, hc⟩ := w0Facts_cert.ja
  obtain ⟨j, hj, rfl⟩ := matGrp_le_map jWords_lt42 hx
  have hcj : IsConj (rep 1) j := (isConj_iff_crConj (by norm_num)).2 hc
  have hcG : IsConj h.aG ((h.φ.symm j : h.H) : G) := by
    obtain ⟨c, hc'⟩ := isConj_iff.1 hcj
    refine isConj_iff.2 ⟨((h.φ.symm c : h.H) : G), ?_⟩
    have := congrArg (fun t : Cr => ((h.φ.symm t : h.H) : G)) hc'
    simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] using this
  obtain ⟨g, hg⟩ := isConj_iff.1 hcG
  refine ⟨g, fun y hy => ?_⟩
  have hyj : y * ((h.φ.symm j : h.H) : G) = ((h.φ.symm j : h.H) : G) * y :=
    h.elemTwo_JG.2 _ hy _ (h.φ_symm_mem_JG hj)
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc g⁻¹ * y * g * h.aG = g⁻¹ * (y * (g * h.aG * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * h.aG * g⁻¹) * y) * g := by rw [hg, hyj]
    _ = h.aG * (g⁻¹ * y * g) := by group

theorem eq_bot_of_normal_odd_IG (N : Subgroup h.IG) (hN : N.Normal)
    (hodd : Odd (Nat.card N)) : N = ⊥ := by
  have := h.finite
  obtain ⟨g, hg⟩ := h.exists_conj_JG_le_IG
  set Y : Subgroup G := (N.map h.IG.subtype).map (MulAut.conj g).toMonoidHom with hY
  have hYodd : Odd (Nat.card Y) := by
    rw [hY, Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective, Subgroup.card_map_of_injective h.IG.subtype_injective]
    exact hodd
  have hJY : h.JG ≤ Subgroup.normalizer (Y : Set G) := by
    intro y hy
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨_, ⟨n, hn, rfl⟩, rfl⟩ := hx
    have hi := hg y hy
    have hmem : (⟨g⁻¹ * y * g, hi⟩ : h.IG) * n * (⟨g⁻¹ * y * g, hi⟩ : h.IG)⁻¹ ∈ N :=
      hN.conj_mem n hn _
    refine ⟨_, ⟨_, hmem, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype,
      Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hYb := h.eq_bot_of_odd_normalized hYodd hJY
  rw [hY, Subgroup.map_eq_bot_iff_of_injective (f := (MulAut.conj g).toMonoidHom) _
    (MulAut.conj g).injective,
    Subgroup.map_eq_bot_iff_of_injective _ h.IG.subtype_injective] at hYb
  exact hYb

abbrev VI : Subgroup h.IG := h.W0G.subgroupOf h.IG

@[expose] def SI : Sylow 2 h.IG :=
  haveI := h.finite
  Sylow.ofCard (h.S0G.subgroupOf h.IG) h.card_sylow_I

theorem coe_SI : (h.SI : Subgroup h.IG) = h.S0G.subgroupOf h.IG := by
  have := h.finite
  exact Sylow.coe_ofCard _ _

theorem VI_le_SI : h.VI ≤ h.SI := by
  rw [coe_SI]
  intro x hx
  exact Subgroup.mem_subgroupOf.2 (h.W0G_le_S0G (Subgroup.mem_subgroupOf.1 hx))

theorem VI_comm : ∀ a ∈ h.VI, ∀ b ∈ h.VI, a * b = b * a := fun _ ha _ hb =>
  Subtype.ext (h.WG_comm (h.W0G_le_WG (Subgroup.mem_subgroupOf.1 ha))
    (h.W0G_le_WG (Subgroup.mem_subgroupOf.1 hb)))

theorem VI_sq : ∀ v ∈ h.VI, v * v = 1 := fun _ hv =>
  Subtype.ext (h.WG_sq (h.W0G_le_WG (Subgroup.mem_subgroupOf.1 hv)))

theorem card_VI : Nat.card h.VI = 16 := by
  rw [card_subgroupOf_eq h.W0G_le_IG, h.card_W0G]

theorem VI_closed : ∀ a ∈ h.VI, ∀ g : h.IG, g⁻¹ * a * g ∈ (h.SI : Subgroup h.IG) →
    g⁻¹ * a * g ∈ h.VI := by
  intro a ha g hg
  rw [coe_SI, Subgroup.mem_subgroupOf] at hg
  rw [Subgroup.mem_subgroupOf] at ha ⊢
  have hgI : (g : G)⁻¹ ∈ h.IG := h.IG.inv_mem g.2
  have e : ((g⁻¹ * a * g : h.IG) : G) = (g : G)⁻¹ * a * ((g : G)⁻¹)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
  rw [e] at hg ⊢
  exact h.conj_mem_W0G hgI ha (h.S0G_le_X0G hg)

theorem VI_oddCore : ∀ N : Subgroup h.IG, N.Normal → Odd (Nat.card N) → N = ⊥ :=
  h.eq_bot_of_normal_odd_IG

theorem map_centralizer_VI_le :
    (Subgroup.centralizer (h.VI : Set h.IG)).map h.IG.subtype ≤ h.CWG := by
  rintro _ ⟨c, hc, rfl⟩
  refine h.mem_CWG_of_centralizes c.2 fun w hw => ?_
  have hwI := h.W0G_le_IG hw
  have := Subgroup.mem_centralizer_iff.1 hc ⟨w, hwI⟩ (Subgroup.mem_subgroupOf.2 hw)
  exact congrArg Subtype.val this

theorem VI_centralizer_isPGroup : IsPGroup 2 (Subgroup.centralizer (h.VI : Set h.IG)) :=
  (h.isPGroup_CWG.to_le h.map_centralizer_VI_le).of_equiv
    (Subgroup.equivMapOfInjective _ _ h.IG.subtype_injective).symm

theorem VI_trans : ∀ v ∈ h.VI, ∀ w ∈ h.VI, v ≠ 1 → w ≠ 1 →
    ∃ n ∈ Subgroup.normalizer (h.VI : Set h.IG), n * v * n⁻¹ = w := by
  intro v hv w hw hv1 hw1
  rw [Subgroup.mem_subgroupOf] at hv hw
  have hv1' : (v : G) ≠ 1 := fun e => hv1 (Subtype.ext e)
  have hw1' : (w : G) ≠ 1 := fun e => hw1 (Subtype.ext e)
  obtain ⟨nv, hnv, hnvz⟩ := h.exists_NWG_conj hv hv1'
  obtain ⟨nw, hnw, hnwz⟩ := h.exists_NWG_conj hw hw1'
  have hn : nw * nv⁻¹ ∈ h.NWG := h.NWG.mul_mem hnw (h.NWG.inv_mem hnv)
  have hnI : nw * nv⁻¹ ∈ h.IG := (Subgroup.mem_inf.1 hn).1
  have hnN := h.NWG_le_normalizer_W0G hn
  refine ⟨⟨nw * nv⁻¹, hnI⟩, ?_, Subtype.ext ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.1 hnN x
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hnwz, ← hnvz]
    group

theorem NWG_subgroupOf_le :
    h.NWG.subgroupOf h.IG ≤ Subgroup.normalizer (h.VI : Set h.IG) := by
  intro n hn
  rw [Subgroup.mem_subgroupOf] at hn
  have hnN := h.NWG_le_normalizer_W0G hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  exact Subgroup.mem_normalizer_iff.1 hnN x

theorem VI_card_le :
    20160 * Nat.card (Subgroup.centralizer (h.VI : Set h.IG)) ≤
      Nat.card (Subgroup.normalizer (h.VI : Set h.IG)) := by
  have := h.finite
  have hC : Nat.card (Subgroup.centralizer (h.VI : Set h.IG)) ≤ 2048 := by
    rw [← Subgroup.card_map_of_injective h.IG.subtype_injective]
    exact (Subgroup.card_le_of_le h.map_centralizer_VI_le).trans h.card_CWG_le
  have hN : 41287680 ≤ Nat.card (Subgroup.normalizer (h.VI : Set h.IG)) := by
    rw [← h.card_normalizer_WG, ← card_subgroupOf_eq (inf_le_left : h.NWG ≤ h.IG)]
    exact Subgroup.card_le_of_le h.NWG_subgroupOf_le
  omega

theorem factorization_card_IG : (Nat.card h.IG).factorization 2 = 17 := by
  have h1 := h.card_sylow_I
  have hS0I : h.S0G ≤ h.IG := fun x hx => (Subgroup.mem_inf.1 (h.S0G_le_X0G hx)).2
  rw [card_subgroupOf_eq hS0I, h.card_S0G, show (131072 : ℕ) = 2 ^ 17 by norm_num] at h1
  exact (Nat.pow_right_injective le_rfl h1).symm

theorem card_normalizer_VI :
    Nat.card (Subgroup.normalizer (h.VI : Set h.IG)) = 41287680 := by
  have := h.finite
  rw [← h.card_normalizer_WG]
  refine le_antisymm ?_ ?_
  · rw [← Subgroup.card_map_of_injective h.IG.subtype_injective]
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨n, hn, rfl⟩
    refine h.normalizer_W0G_le_NWG (Subgroup.mem_inf.2 ⟨n.2, ?_⟩)
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have hxI := h.W0G_le_IG hx
    have := (Subgroup.mem_normalizer_iff.1 hn ⟨x, hxI⟩).1 (Subgroup.mem_subgroupOf.2 hx)
    exact Subgroup.mem_subgroupOf.1 this
  · rw [← card_subgroupOf_eq (inf_le_left : h.NWG ≤ h.IG)]
    exact Subgroup.card_le_of_le h.NWG_subgroupOf_le

end Co2CentHyp

end CFSG.RankThree.Co2
