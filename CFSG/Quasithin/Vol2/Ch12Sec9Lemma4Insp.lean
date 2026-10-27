module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4Tools
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4Sp
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4O6
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4Seven
public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4SL2
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4Q

public section

namespace CFSG.Quasithin.H13

namespace L1294I

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

theorem mem_of_relIndex_le_two_of_odd {G : Type*} [Group G] [Finite G] {Γ O : Subgroup G}
    (hidx : Γ.relIndex O ≤ 2) {x : G} (hxO : x ∈ O) {m : ℕ} (hx : x ^ (2 * m + 1) = 1) :
    x ∈ Γ := by
  have hsq : ∀ y ∈ O, y ^ 2 ∈ Γ := by
    intro y hy
    have h0 : (Γ.subgroupOf O).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hle : (Γ.subgroupOf O).index ≤ 2 := hidx
    rcases (by omega : (Γ.subgroupOf O).index = 1 ∨ (Γ.subgroupOf O).index = 2) with h1 | h2
    · have hmem : (⟨y ^ 2, O.pow_mem hy 2⟩ : O) ∈ Γ.subgroupOf O := by
        rw [Subgroup.index_eq_one.1 h1]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.1 hmem
    · have h4 := Subgroup.sq_mem_of_index_two h2 (⟨y, hy⟩ : O)
      rw [Subgroup.mem_subgroupOf] at h4
      simpa using h4
  have e : x = (x ^ (m + 1)) ^ 2 := by
    rw [← pow_mul, show (m + 1) * 2 = 2 * m + 1 + 1 by ring, pow_succ, hx, one_mul]
  rw [e]
  exact hsq _ (O.pow_mem hxO _)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem finite_glv : Finite (V ≃ₗ[ZMod 2] V) :=
  Finite.of_injective (fun f : V ≃ₗ[ZMod 2] V => (f : V → V)) DFunLike.coe_injective

omit [Finite V] in
theorem normal_subgroupOf {N Γ : Subgroup (V ≃ₗ[ZMod 2] V)} (hNΓ : N ≤ Γ)
    (hΓN : Γ ≤ Subgroup.normalizer (N : Set (V ≃ₗ[ZMod 2] V))) : (N.subgroupOf Γ).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer hNΓ).2 hΓN

omit [Finite V] in
theorem subgroupOf_ne_bot {N Γ : Subgroup (V ≃ₗ[ZMod 2] V)} (hNΓ : N ≤ Γ) (hne : N ≠ ⊥) :
    N.subgroupOf Γ ≠ ⊥ := fun h => hne (by
  rw [eq_bot_iff]
  intro x hx
  have : (⟨x, hNΓ hx⟩ : Γ) ∈ N.subgroupOf Γ := Subgroup.mem_subgroupOf.2 hx
  rw [h, Subgroup.mem_bot] at this
  exact (Subgroup.mem_bot).2 (congrArg Subtype.val this))

omit [Finite V] in
theorem card_subgroupOf {N Γ : Subgroup (V ≃ₗ[ZMod 2] V)} (hNΓ : N ≤ Γ) :
    Nat.card (N.subgroupOf Γ) = Nat.card N :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNΓ).toEquiv

omit [Finite V] in
theorem eq_of_le_of_normal3 {N Γ : Subgroup (V ≃ₗ[ZMod 2] V)} (hNΓ : N ≤ Γ)
    (h3 : L1294Q.Normal3 N) {F : Subgroup ↥Γ} (hFn : F.Normal) (hFN : F ≤ N.subgroupOf Γ)
    (hF3 : 3 < Nat.card F) : Nat.card N = Nat.card F := by
  have hM : F.map Γ.subtype = N := by
    refine h3 _ ?_ ?_ ?_
    · rintro _ ⟨f, hf, rfl⟩
      exact Subgroup.mem_subgroupOf.1 (hFN hf)
    · rintro n hn _ ⟨f, hf, rfl⟩
      exact ⟨⟨n, hNΓ hn⟩ * f * ⟨n, hNΓ hn⟩⁻¹, hFn.conj_mem f hf _, rfl⟩
    · rwa [Subgroup.card_map_of_injective Γ.subtype_injective]
  rw [← hM, Subgroup.card_map_of_injective Γ.subtype_injective]


section Cases

variable {B : LinearMap.BilinForm (ZMod 2) V} {Γ X : Subgroup (V ≃ₗ[ZMod 2] V)}

omit [Finite V] in
theorem card_of_concl1 (h : G112Concl1 Γ) : Nat.card Γ = 6 := by
  obtain ⟨-, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
  rfl

theorem no7_of_concl2 {v₁ : V} {W : Submodule (ZMod 2) V} {X₀ : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hG : G111Hyp B Γ v₁ W X X₀) (h : G112Concl2 Γ) :
    ∀ g ∈ Γ, g ^ 7 = 1 → g = 1 := fun g hg h7 =>
  L1294S.eq_one_of_pow_seven hG.alt hG.nondegenerate h.1 (hG.isometry g hg) h7

omit [Finite V] in
theorem card_dvd_of_concl3 (h : G112Concl3 Γ) : Nat.card Γ ∣ 432 := by
  obtain ⟨-, P, -, -, hP, -, hidx, -⟩ := h
  have h1 := P.card_mul_index
  rw [hP] at h1
  rw [← h1]
  exact Nat.mul_dvd_mul_left 27 hidx

omit [Finite V] in
theorem fstar_of_concl4 (h : G112Concl4 Γ) :
    IsSimpleGroup ↥(genFittingFStar ↥Γ) ∧ Nat.card (genFittingFStar ↥Γ) = 2520 := by
  obtain ⟨-, φ, -, -⟩ := h
  have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
  refine ⟨φ.isSimpleGroup, ?_⟩
  rw [Nat.card_congr φ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  rfl

theorem no7_of_concl7 (h : G112Concl7 Γ X) : ∀ g ∈ Γ, g ^ 7 = 1 → g = 1 := by
  have := finite_glv (V := V)
  obtain ⟨-, ⟨φ⟩, -⟩ := h
  obtain ⟨eA⟩ := nonempty_sl2_four_mulEquiv
  intro g hg h7
  have := eq_one_of_pow_seven_prod (G := ↥Γ) eA φ (g := ⟨g, hg⟩)
    (Subtype.ext (by simpa using h7))
  exact congrArg Subtype.val this

omit [Finite V] in
theorem card_of_concl9 (h : G112Concl9 Γ) : Nat.card Γ = 720 ∨ Nat.card Γ = 360 := by
  obtain ⟨-, h | h⟩ := h <;> obtain ⟨e⟩ := h
  · left
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_perm, Nat.card_perm, Nat.card_fin,
      Nat.card_fin]
    rfl
  · right
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_perm, nat_card_alternatingGroup,
      Nat.card_fin, Nat.card_fin]
    rfl

omit [Finite V] in
theorem fstar_of_concl11 (h : G112Concl11 Γ) :
    IsSimpleGroup ↥(genFittingFStar ↥Γ) ∧ Nat.card (genFittingFStar ↥Γ) = 504 := by
  obtain ⟨-, ⟨φ⟩⟩ := h
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 3)) :=
    CFSG.ComponentClassification.Asc75T4.isSimpleGroup_sl2 (by norm_num)
  refine ⟨φ.isSimpleGroup, ?_⟩
  let := Fintype.ofFinite (GaloisField 2 3)
  have hK : Fintype.card (GaloisField 2 3) = 8 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 3 (by norm_num)]
    norm_num
  rw [Nat.card_congr φ.toEquiv, Matrix.card_SL_field, hK, Fin.prod_univ_two]
  norm_num

theorem no7_of_concl12 (h : G112Concl12 Γ X) : ∀ g ∈ Γ, g ^ 7 = 1 → g = 1 := by
  have := finite_glv (V := V)
  obtain ⟨-, x, L, -, hLΓ, hF, hinf, hc, -, ⟨φ, -, -⟩, -⟩ := h
  set Lx := L.map (MulAut.conj x).toMonoidHom with hLx
  have hLxΓ : Lx ≤ Γ := by
    intro y hy
    have : y ∈ (genFittingFStar ↥Γ).map Γ.subtype := by rw [hF]; exact Subgroup.mem_sup_right hy
    obtain ⟨z, -, rfl⟩ := this
    exact z.2
  have eLx : ↥Lx ≃* alternatingGroup (Fin 5) :=
    (L.equivMapOfInjective _ (MulAut.conj x).injective).symm.trans φ
  intro g hg h7
  exact eq_one_of_pow_seven_sup hLΓ hLxΓ hF hc hinf φ eLx hg h7

end Cases

section Inspect

variable {B : LinearMap.BilinForm (ZMod 2) V} {Γ X X₀ : Subgroup (V ≃ₗ[ZMod 2] V)} {v₁ : V}
  {W : Submodule (ZMod 2) V}

theorem false_of_list2 (hG111 : G111Hyp B Γ v₁ W X X₀) (hfix : G11.G112ConclusionFix B Γ X)
    {N : Subgroup (V ≃ₗ[ZMod 2] V)} (hNΓ : N ≤ Γ)
    (hΓN : Γ ≤ Subgroup.normalizer (N : Set (V ≃ₗ[ZMod 2] V))) (hne : N ≠ ⊥)
    (hbig : 2661120 < Nat.card N) (h7 : 7 ∣ Nat.card N) (h3 : L1294Q.Normal3 N) : False := by
  classical
  have := finite_glv (V := V)
  have hle : Nat.card N ≤ Nat.card Γ := Subgroup.card_le_of_le hNΓ
  have hF : ∀ (_ : IsSimpleGroup ↥(genFittingFStar ↥Γ)), 3 < Nat.card (genFittingFStar ↥Γ) →
      Nat.card N = Nat.card (genFittingFStar ↥Γ) := fun hS h3F =>
    eq_of_le_of_normal3 hNΓ h3 (A7Mod.genFittingFStar_normal' _)
      (L1294F.genFittingFStar_le_of_normal hS (normal_subgroupOf hNΓ hΓN)
        (subgroupOf_ne_bot hNΓ hne)) h3F
  rcases hfix with ((h1 | h2 | h3' | h4 | h5 | h6 | h7' | h8 | h9 | h10 | h11 | h12 | h13) |
    h8S | h6U)
  · rw [card_of_concl1 h1] at hle
    omega
  · exact not_seven_dvd hNΓ (no7_of_concl2 hG111 h2) h7
  · have := Nat.le_of_dvd (by norm_num) (card_dvd_of_concl3 h3')
    omega
  · obtain ⟨hS, hc⟩ := fstar_of_concl4 h4
    have := hF hS (by rw [hc]; norm_num)
    omega
  · obtain ⟨Ω, -, -, -, hΓc⟩ := L1294O.exists_simple_le hG111.nondegenerate h5
    omega
  · rw [h6.2] at hle
    omega
  · exact not_seven_dvd hNΓ (no7_of_concl7 h7') h7
  · obtain ⟨-, ⟨e⟩, -⟩ := h8
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin,
      show Nat.factorial 7 = 5040 from rfl] at hle
    omega
  · rcases card_of_concl9 h9 with h | h <;> omega
  · rw [h10.2.1] at hle
    omega
  · obtain ⟨hS, hc⟩ := fstar_of_concl11 h11
    have := hF hS (by rw [hc]; norm_num)
    omega
  · exact not_seven_dvd hNΓ (no7_of_concl12 h12) h7
  · rw [h13.2] at hle
    omega
  · obtain ⟨-, ⟨e⟩, -⟩ := h8S
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin,
      show Nat.factorial 8 = 40320 from rfl] at hle
    omega
  · rw [h6U.2] at hle
    omega

theorem of_list3 {Q : Type} [Group Q] (hSeven : G112ConclSeven) (hG111 : G111Hyp B Γ v₁ W X X₀)
    (hsqtk : IsQuotientOfSQTKTauCeti ↥Γ) (hfix : G11.G112ConclusionFix B Γ X)
    {N : Subgroup (V ≃ₗ[ZMod 2] V)} (hNΓ : N ≤ Γ)
    (hΓN : Γ ≤ Subgroup.normalizer (N : Set (V ≃ₗ[ZMod 2] V))) (hne : N ≠ ⊥)
    (hcls : (Nonempty (Q ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∧ Nat.card N = 20160 ∧
        L1294Q.Normal3 N) ∨
      ((Nat.card N = 2520 ∨ Nat.card N = 7560 ∨ 2661120 < Nat.card N) ∧ L1294Q.Normal3 N) ∨
      Nat.card N ∣ 16464)
    {S L : Subgroup (V ≃ₗ[ZMod 2] V)} (hS : QuasithinUnique.IsSylowTwoOf S Γ) (hLN : L ≤ N)
    (hSL : S ≤ Subgroup.normalizer (L : Set (V ≃ₗ[ZMod 2] V))) {k : ℕ}
    (hL : Nat.card L = 2 ^ k * 21) :
    G112Concl4 Γ ∨ (G112Concl5 B Γ ∧
      Nonempty (Q ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∧ N.relIndex Γ ≤ 2) := by
  classical
  have := finite_glv (V := V)
  have hle : Nat.card N ≤ Nat.card Γ := Subgroup.card_le_of_le hNΓ
  have hdvdΓ : Nat.card N ∣ Nat.card Γ := Subgroup.card_dvd_of_le hNΓ
  have h7 : 7 ∣ Nat.card N := (seven_dvd_of_card hL).trans (Subgroup.card_dvd_of_le hLN)
  have h7Γ : 7 ∣ Nat.card Γ := h7.trans hdvdΓ
  have hN' := normal_subgroupOf hNΓ hΓN
  have hN'1 := subgroupOf_ne_bot hNΓ hne
  have hN'c := card_subgroupOf hNΓ
  obtain ⟨g, hgN, hg7, hg1⟩ := exists_pow_seven h7
  have h16464 : ∀ (_ : Nat.card N ∣ 16464), Nat.card N ≤ 16464 := fun h =>
    Nat.le_of_dvd (by norm_num) h
  obtain ⟨h6s, h6Us, h13s⟩ := hSeven V B Γ v₁ W X X₀ hG111 hsqtk (N.subgroupOf Γ) hN'
    (by rw [hN'c]; exact h7)
  rcases hfix with ((h1 | h2 | h3' | h4 | h5 | h6 | h7' | h8 | h9 | h10 | h11 | h12 | h13) |
    h8S | h6U)
  · rw [card_of_concl1 h1] at h7Γ
    exact absurd h7Γ (by decide)
  · exact absurd h7 (not_seven_dvd hNΓ (no7_of_concl2 hG111 h2))
  · exact absurd (h7Γ.trans (card_dvd_of_concl3 h3')) (by decide)
  · exact Or.inl h4
  ·
    obtain ⟨Ω, hΩΓ, hΩs, hΩc, hΓc⟩ := L1294O.exists_simple_le hG111.nondegenerate h5
    have hΩidx : Ω.relIndex Γ ≤ 2 := by
      have h1 := (Ω.subgroupOf Γ).card_mul_index
      rw [card_subgroupOf hΩΓ, hΩc] at h1
      change Ω.relIndex Γ ≤ 2
      unfold Subgroup.relIndex
      omega
    have hgΩ : g ∈ Ω := mem_of_relIndex_le_two_of_odd hΩidx (hNΓ hgN) (m := 3) hg7
    have hΩN : Ω ≤ N := by
      have hn : ((N ⊓ Ω).subgroupOf Ω).Normal := ⟨fun x hx w => by
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        refine ⟨?_, Ω.mul_mem (Ω.mul_mem w.2 hx.2) (Ω.inv_mem w.2)⟩
        exact (Subgroup.mem_normalizer_iff.1 (hΓN (hΩΓ w.2)) _).1 hx.1⟩
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ Ω).subgroupOf Ω) with h | h
      · exfalso
        have : (⟨g, hgΩ⟩ : Ω) ∈ (N ⊓ Ω).subgroupOf Ω := Subgroup.mem_subgroupOf.2 ⟨hgN, hgΩ⟩
        rw [h, Subgroup.mem_bot] at this
        exact hg1 (congrArg Subtype.val this)
      · intro x hx
        have : (⟨x, hx⟩ : Ω) ∈ (N ⊓ Ω).subgroupOf Ω := by rw [h]; exact Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf.1 this).1
    have hge : 20160 ≤ Nat.card N := hΩc ▸ Subgroup.card_le_of_le hΩN
    rcases hcls with ⟨hQ4, hc, -⟩ | ⟨hc | hc | hc, -⟩ | hc
    · refine Or.inr ⟨h5, hQ4, ?_⟩
      have h1 := (N.subgroupOf Γ).card_mul_index
      rw [hN'c, hc] at h1
      change (N.subgroupOf Γ).index ≤ 2
      omega
    · omega
    · omega
    · omega
    · have := h16464 hc
      omega
  ·
    have hge := h6s h6
    rw [hN'c, h6.2] at hge
    rw [h6.2] at hdvdΓ hle
    rcases hcls with ⟨-, hc, -⟩ | ⟨hc | hc | hc, -⟩ | hc
    · omega
    · rw [hc] at hdvdΓ
      exact absurd hdvdΓ (by decide)
    · rw [hc] at hdvdΓ
      exact absurd hdvdΓ (by decide)
    · omega
    · have := Nat.le_of_dvd (by norm_num) (Nat.dvd_gcd hc hdvdΓ)
      norm_num at this
      omega
  · exact absurd h7 (not_seven_dvd hNΓ (no7_of_concl7 h7'))
  · obtain ⟨-, ⟨e⟩, -⟩ := h8
    exact (false_of_perm_iso (Or.inl rfl) e hS (hLN.trans hNΓ) hSL hL).elim
  · rcases card_of_concl9 h9 with h | h <;> rw [h] at h7Γ <;> exact absurd h7Γ (by decide)
  · rw [h10.2.1] at h7Γ
    exact absurd h7Γ (by decide)
  ·
    obtain ⟨hS, hc⟩ := fstar_of_concl11 h11
    have hFN := L1294F.genFittingFStar_le_of_normal hS hN' hN'1
    have h504 : 504 ∣ Nat.card N := by
      rw [← hc, ← hN'c]
      exact Subgroup.card_dvd_of_le hFN
    rcases hcls with ⟨-, hc', h3⟩ | ⟨hc', h3⟩ | hcN
    · have := eq_of_le_of_normal3 hNΓ h3 (A7Mod.genFittingFStar_normal' _) hFN
        (by rw [hc]; norm_num)
      omega
    · have := eq_of_le_of_normal3 hNΓ h3 (A7Mod.genFittingFStar_normal' _) hFN
        (by rw [hc]; norm_num)
      omega
    · exact absurd (h504.trans hcN) (by decide)
  · exact absurd h7 (not_seven_dvd hNΓ (no7_of_concl12 h12))
  ·
    have h11 := h13s h13
    rw [hN'c] at h11
    rw [h13.2] at hle
    rcases hcls with ⟨-, hc, -⟩ | ⟨hc | hc | hc, -⟩ | hc
    · rw [hc] at h11
      exact absurd h11 (by decide)
    · rw [hc] at h11
      exact absurd h11 (by decide)
    · rw [hc] at h11
      exact absurd h11 (by decide)
    · omega
    · exact absurd (h11.trans hc) (by decide)
  · obtain ⟨-, ⟨e⟩, -⟩ := h8S
    exact (false_of_perm_iso (Or.inr rfl) e hS (hLN.trans hNΓ) hSL hL).elim
  ·
    have hge := h6Us h6U
    rw [hN'c, h6U.2] at hge
    rw [h6U.2] at hdvdΓ hle
    rcases hcls with ⟨-, hc, -⟩ | ⟨hc | hc | hc, -⟩ | hc
    · omega
    · rw [hc] at hdvdΓ
      exact absurd hdvdΓ (by decide)
    · omega
    · omega
    · have := Nat.le_of_dvd (by norm_num) (Nat.dvd_gcd hc hdvdΓ)
      norm_num at this
      omega

end Inspect

end L1294I

end CFSG.Quasithin.H13
