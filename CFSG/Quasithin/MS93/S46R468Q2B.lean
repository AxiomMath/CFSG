module

public import CFSG.Quasithin.MS93.S46R468N1
public import CFSG.Quasithin.MS93.S46R468B3

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement

section General

variable {𝔾 : Type*} [Group 𝔾]

theorem eq_of_card_two {P : Subgroup 𝔾} (hP : Nat.card P = 2) {a b : 𝔾} (ha : a ∈ P)
    (hb : b ∈ P) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : P)).mp hP
  have h1 : (⟨a, ha⟩ : P) = y := hy _ fun h => ha1 (congrArg Subtype.val h)
  have h2 : (⟨b, hb⟩ : P) = y := hy _ fun h => hb1 (congrArg Subtype.val h)
  exact congrArg Subtype.val (h1.trans h2.symm)

theorem exists_ne_one_of_card_two {P : Subgroup 𝔾} (hP : Nat.card P = 2) :
    ∃ a ∈ P, a ≠ 1 := by
  by_contra h
  push Not at h
  have : P = ⊥ := (Subgroup.eq_bot_iff_forall P).mpr h
  rw [this, Subgroup.card_bot] at hP
  omega

theorem eq_of_card_two_of_mem {P Q : Subgroup 𝔾} (hP : Nat.card P = 2) (hQ : Nat.card Q = 2)
    {a : 𝔾} (haP : a ∈ P) (haQ : a ∈ Q) (ha1 : a ≠ 1) : P = Q := by
  have : Finite ↥Q := Nat.finite_of_card_ne_zero (by rw [hQ]; norm_num)
  refine Subgroup.eq_of_le_of_card_ge (fun b hb => ?_) (by rw [hP, hQ])
  by_cases hb1 : b = 1
  · rw [hb1]; exact Q.one_mem
  · rw [eq_of_card_two hP hb haP hb1 ha1]; exact haQ

theorem eq_or_eq_or_eq_of_card_four {H P₁ P₂ P₃ P : Subgroup 𝔾} (hH : Nat.card H = 4)
    (hc : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (h₁ : P₁ ≤ H) (h₂ : P₂ ≤ H) (h₃ : P₃ ≤ H)
    (hP : P ≤ H) (c₁ : Nat.card P₁ = 2) (c₂ : Nat.card P₂ = 2) (c₃ : Nat.card P₃ = 2)
    (cP : Nat.card P = 2) (n₁₂ : P₁ ≠ P₂) (n₁₃ : P₁ ≠ P₃) (n₂₃ : P₂ ≠ P₃) :
    P = P₁ ∨ P = P₂ ∨ P = P₃ := by
  have : Finite ↥H := Nat.finite_of_card_ne_zero (by rw [hH]; norm_num)
  have hsup : P₁ ⊔ P₂ = H := by
    have hle : P₁ ⊔ P₂ ≤ H := sup_le h₁ h₂
    have : Finite ↥(P₁ ⊔ P₂) := Finite.of_injective _ (Subgroup.inclusion_injective hle)
    have hdvd : Nat.card ↥(P₁ ⊔ P₂) ∣ 4 := hH ▸ Subgroup.card_dvd_of_le hle
    have hge : 2 ≤ Nat.card ↥(P₁ ⊔ P₂) := c₁ ▸ Subgroup.card_le_of_le le_sup_left
    have hne : Nat.card ↥(P₁ ⊔ P₂) ≠ 2 := fun h => n₁₂ (by
      have e1 : P₁ = P₁ ⊔ P₂ := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h, c₁])
      have e2 : P₂ = P₁ ⊔ P₂ := Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [h, c₂])
      rw [e1, ← e2])
    have h4 : Nat.card ↥(P₁ ⊔ P₂) = 4 := by
      have hpos : 0 < Nat.card ↥(P₁ ⊔ P₂) := by omega
      have := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases h : Nat.card ↥(P₁ ⊔ P₂) <;> first | rfl | omega
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [h4, hH])
  have hn : P₁ ≤ Subgroup.normalizer (P₂ : Set 𝔾) := fun a ha =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun b hb =>
      hc b (h₂ hb) a (h₁ ha))
  have hdec : ∀ g ∈ H, ∃ a ∈ P₁, ∃ b ∈ P₂, g = a * b := by
    intro g hg
    rw [← hsup] at hg
    have := (Subgroup.coe_mul_of_left_le_normalizer_right P₁ P₂ hn) ▸ (SetLike.mem_coe.mpr hg)
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp this
    exact ⟨a, ha, b, hb, rfl⟩
  obtain ⟨p₁, hp₁, hp₁1⟩ := exists_ne_one_of_card_two c₁
  obtain ⟨p₂, hp₂, hp₂1⟩ := exists_ne_one_of_card_two c₂
  have key : ∀ {Q : Subgroup 𝔾}, Q ≤ H → Nat.card Q = 2 → Q ≠ P₁ → Q ≠ P₂ →
      ∀ q ∈ Q, q ≠ 1 → q = p₁ * p₂ := by
    intro Q hQ cQ nQ₁ nQ₂ q hq hq1
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec q (hQ hq)
    by_cases ha1 : a = 1
    · rw [ha1, one_mul] at hq hq1
      exact absurd (eq_of_card_two_of_mem cQ c₂ hq hb hq1) nQ₂
    by_cases hb1 : b = 1
    · rw [hb1, mul_one] at hq hq1
      exact absurd (eq_of_card_two_of_mem cQ c₁ hq ha hq1) nQ₁
    rw [eq_of_card_two c₁ ha hp₁ ha1 hp₁1, eq_of_card_two c₂ hb hp₂ hb1 hp₂1]
  by_contra hne
  push Not at hne
  obtain ⟨p₃, hp₃, hp₃1⟩ := exists_ne_one_of_card_two c₃
  obtain ⟨p, hp, hp1⟩ := exists_ne_one_of_card_two cP
  have e₃ := key h₃ c₃ (Ne.symm n₁₃) (Ne.symm n₂₃) p₃ hp₃ hp₃1
  have e := key hP cP hne.1 hne.2.1 p hp hp1
  exact hne.2.2 (eq_of_card_two_of_mem cP c₃ hp (e ▸ e₃ ▸ hp₃) hp1)

theorem exists_mul_of_mem_sup_of_commute' {A B : Subgroup 𝔾}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : 𝔾} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have hn : A ≤ Subgroup.normalizer (B : Set 𝔾) := fun a ha =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun b hb =>
      (hAB a ha b hb).symm)
  have := (Subgroup.coe_mul_of_left_le_normalizer_right A B hn) ▸ (SetLike.mem_coe.mpr hx)
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp this
  exact ⟨a, ha, b, hb, rfl⟩

end General

section Amalgam

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem uloc_le_usup_sup_usup (h464 : I464) (h465 : I465) (c : Hyp46 M T L φ)
    {x ℓ m : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxℓ : (puAmalgam c.pu.le).treeGraph.Adj x ℓ) (hxm : (puAmalgam c.pu.le).treeGraph.Adj x m)
    (hne : Usup (puAmalgam c.pu.le) x ℓ ≠ Usup _ x m) :
    Uloc c.pu.le L x ≤ Usup (puAmalgam c.pu.le) x ℓ ⊔ Usup _ x m := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have h464' := h464 G M T L F φ c
  have hsq : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam c.pu.le) δ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    (h465 G M T L F φ c δ ρ hδ hδρ).1
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc c.pu c.via hx
  have hm₁ := mem_usup_iff c.pu c.via h464' hsq hx hxℓ hψ
  have hm₂ := mem_usup_iff c.pu c.via h464' hsq hx hxm hψ
  set W₁ := fixN (natImage ψ (Qv (puAmalgam c.pu.le) ℓ)) with hW₁
  set W₂ := fixN (natImage ψ (Qv (puAmalgam c.pu.le) m)) with hW₂
  have hne' : W₁ ≠ W₂ := fun heq => hne ((S45.eq_iff_of_natVec_iff hψ
    (usup_le_uloc' c.pu hfull hx hxℓ) (usup_le_uloc' c.pu hfull hx hxm) hm₁ hm₂).mpr heq)
  have hd₁ : Module.finrank F W₁ = 2 := (I466b.fixN_natImage_qv c.pu c.via h464' hsq hx hxℓ hψ).1
  have hd₂ : Module.finrank F W₂ = 2 := (I466b.fixN_natImage_qv c.pu c.via h464' hsq hx hxm hψ).1
  have hi := S45.finrank_inf_eq_one hd₁ hd₂ hne'
  have htop : W₁ ⊔ W₂ = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq W₁ W₂
    rw [hd₁, hd₂, hi] at h1
    have h2 : Module.finrank F (Fin 3 → F) = 3 := Module.finrank_fin_fun F
    omega
  intro u hu
  have hmem : natVec hψ ⟨u, hu⟩ ∈ W₁ ⊔ W₂ := by rw [htop]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨ua, rfl⟩ := natVec_surjective hψ a
  obtain ⟨ub, rfl⟩ := natVec_surjective hψ b
  have he : (⟨u, hu⟩ : ↥(Uloc c.pu.le L x)) = ua * ub :=
    natVec_injective hψ (by rw [natVec_mul, hab])
  have hu' : u = (ua : (puAmalgam c.pu.le).Universal) * ub := congrArg Subtype.val he
  rw [hu']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ((hm₁ ua).mpr ha))
    (Subgroup.mem_sup_right ((hm₂ ub).mpr hb))

theorem commute_of_mem_zm (c : Hyp46 M T L φ) {x : Vtx (puAmalgam c.pu.le)}
    (hx : IsMVtx (puAmalgam c.pu.le) x) {a b : (puAmalgam c.pu.le).Universal}
    (ha : a ∈ ZM (puAmalgam c.pu.le) x) (hb : b ∈ ZM (puAmalgam c.pu.le) x) : a * b = b * a :=
  (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ c.pu.hyp20 hx ha) b
    (zm_le_qv_self _ hx c.pu.critDist_pos hb)).symm

theorem mem_ptQ_of_mem_normalizer_usup (h464 : I464) (h465 : I465) (c : Hyp46 M T L φ)
    {x ℓ n : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxℓ : (puAmalgam c.pu.le).treeGraph.Adj x ℓ) (hxn : (puAmalgam c.pu.le).treeGraph.Adj x n)
    (hne : Usup (puAmalgam c.pu.le) x ℓ ≠ Usup _ x n) {y : (puAmalgam c.pu.le).Universal}
    (hyℓ : y ∈ Qv (puAmalgam c.pu.le) ℓ)
    (hyn : y ∈ Subgroup.normalizer (Usup (puAmalgam c.pu.le) x n : Set _)) :
    y ∈ ptQ (puAmalgam c.pu.le) x (Usup _ x ℓ ⊓ Usup _ x n) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have h464' := h464 G M T L F φ c
  have hys : y ∈ stab (puAmalgam c.pu.le) x := qv_le_stab_of_adj _ hxℓ.symm hyℓ
  have hcℓ : ∀ p ∈ Usup (puAmalgam c.pu.le) x ℓ, y * p = p * y := fun p hp =>
    Subgroup.mem_centralizer_iff.mp (zh_le_centralizer _ ℓ (h464' x ℓ hx hxℓ hp)) y hyℓ
  have hUZ : ∀ {k : Vtx (puAmalgam c.pu.le)}, (puAmalgam c.pu.le).treeGraph.Adj x k →
      Usup (puAmalgam c.pu.le) x k ≤ ZM _ x := fun {k} hxk =>
    (h464' x k hx hxk).trans (zh_le_zm _ hxk)
  refine ⟨hys, Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr
    fun p hp => (hcℓ p hp.1).symm), fun z hz => ?_⟩
  obtain ⟨u, hu, ζ, hζ, rfl⟩ := I466b.exists_uloc_mul_zloc c.pu hfull hx hz
  have hζy : y * ζ = ζ * y :=
    Subgroup.mem_centralizer_iff.mp (zloc_le_centralizer_stab c.pu hfull hx hζ) y hys
  have e1 : ⁅u * ζ, y⁆ = ⁅u, y⁆ := by
    simp only [commutatorElement_def]
    calc u * ζ * y * (u * ζ)⁻¹ * y⁻¹ = u * (ζ * y) * ζ⁻¹ * u⁻¹ * y⁻¹ := by group
      _ = u * (y * ζ) * ζ⁻¹ * u⁻¹ * y⁻¹ := by rw [hζy]
      _ = u * y * u⁻¹ * y⁻¹ := by group
  rw [e1]
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute'
    (fun a ha b hb => commute_of_mem_zm c hx (hUZ hxn ha) (hUZ hxℓ hb))
    (uloc_le_usup_sup_usup h464 h465 c hx hxn hxℓ (Ne.symm hne) hu)
  have e2 : ⁅a * b, y⁆ = ⁅a, y⁆ := by
    simp only [commutatorElement_def]
    calc a * b * y * (a * b)⁻¹ * y⁻¹ = a * (b * y) * b⁻¹ * a⁻¹ * y⁻¹ := by group
      _ = a * (y * b) * b⁻¹ * a⁻¹ * y⁻¹ := by rw [hcℓ b hb]
      _ = a * y * a⁻¹ * y⁻¹ := by group
  rw [e2]
  refine ⟨?_, ?_⟩
  · have hza : a ∈ Zv (puAmalgam c.pu.le) x := by
      rw [zv_of_isMVtx _ hx]; exact hUZ hxn ha
    exact Subgroup.commutator_mem_commutator hza hyℓ
  · have hya : y * a * y⁻¹ ∈ Usup (puAmalgam c.pu.le) x n :=
      (Subgroup.mem_normalizer_iff.mp hyn a).mp ha
    have e3 : ⁅a, y⁆ = a * (y * a * y⁻¹)⁻¹ := by rw [commutatorElement_def]; group
    rw [e3]
    exact Subgroup.mul_mem _ ha (Subgroup.inv_mem _ hya)

theorem usup_smul_ne (h464 : I464) (h465 : I465) (c : Hyp46 M T L φ)
    {x ℓ m : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxℓ : (puAmalgam c.pu.le).treeGraph.Adj x ℓ) (hxm : (puAmalgam c.pu.le).treeGraph.Adj x m)
    (hne : Usup (puAmalgam c.pu.le) x ℓ ≠ Usup _ x m) {R : Subgroup (puAmalgam c.pu.le).Universal}
    (hR : IsPtOn (puAmalgam c.pu.le) x ℓ R) (hRP : R ≠ Usup (puAmalgam c.pu.le) x ℓ ⊓ Usup _ x m)
    {y : (puAmalgam c.pu.le).Universal} (hyℓ : y ∈ Qv (puAmalgam c.pu.le) ℓ)
    (hyR : y ∈ ptQ (puAmalgam c.pu.le) x R) (hyx : y ∉ Qv (puAmalgam c.pu.le) x) :
    Usup (puAmalgam c.pu.le) x (y • m) ≠ Usup _ x m := by
  intro he
  have hys : y ∈ stab (puAmalgam c.pu.le) x := qv_le_stab_of_adj _ hxℓ.symm hyℓ
  have hyx' : y • x = x := MulAction.mem_stabilizer_iff.mp hys
  have hconj : (Usup (puAmalgam c.pu.le) x m).map (MulAut.conj y).toMonoidHom = Usup _ x m := by
    rw [← usup_smul, hyx']; exact he
  have hyn : y ∈ Subgroup.normalizer (Usup (puAmalgam c.pu.le) x m : Set _) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [← hconj]
      exact ⟨h, hh, rfl⟩
    · intro hh
      rw [← hconj] at hh
      obtain ⟨h', hh', he'⟩ := hh
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_left_inj,
        mul_right_inj] at he'
      rwa [← he']
  have hP := mem_ptQ_of_mem_normalizer_usup h464 h465 c hx hxℓ hxm hne hyℓ hyn
  have hPpt : IsPtOn (puAmalgam c.pu.le) x ℓ (Usup _ x ℓ ⊓ Usup _ x m) :=
    ⟨m, hxm, Ne.symm hne, rfl⟩
  exact hyx (ptQ_inf_ptQ_le_qv h464 h465 c hx hxℓ hPpt hR (Ne.symm hRP) ⟨hP, hyR⟩)

theorem exists_mem_qv_inf_ptQ (h464 : I464) (h465 : I465) (h466a : I466a) (c : Hyp46 M T L φ)
    {x ℓ : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxℓ : (puAmalgam c.pu.le).treeGraph.Adj x ℓ) {P : Subgroup (puAmalgam c.pu.le).Universal}
    (hP : IsPtOn (puAmalgam c.pu.le) x ℓ P) :
    ∃ y ∈ Qv (puAmalgam c.pu.le) ℓ ⊓ ptQ _ x P, y ∉ Qv (puAmalgam c.pu.le) x := by
  by_contra h
  push Not at h
  have h1 := relIndex_qv_inf_ptQ h464 h465 h466a c hx hxℓ hP
  rw [Subgroup.relIndex_eq_one.mpr fun y hy => h y hy] at h1
  have := Fintype.one_lt_card (α := F)
  omega

theorem exists_three_isPtOn (h464 : I464) (h465 : I465) (c : Hyp46 M T L φ)
    {x ℓ : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxℓ : (puAmalgam c.pu.le).treeGraph.Adj x ℓ) :
    ∃ P₁ P₂ P₃ : Subgroup (puAmalgam c.pu.le).Universal, IsPtOn (puAmalgam c.pu.le) x ℓ P₁ ∧
      IsPtOn (puAmalgam c.pu.le) x ℓ P₂ ∧ IsPtOn (puAmalgam c.pu.le) x ℓ P₃ ∧
      P₁ ≠ P₂ ∧ P₁ ≠ P₃ ∧ P₂ ≠ P₃ := by
  have h464' := h464 G M T L F φ c
  have hsq : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam c.pu.le) δ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    (h465 G M T L F φ c δ ρ hδ hδρ).1
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc c.pu c.via hx
  set W := fixN (natImage ψ (Qv (puAmalgam c.pu.le) ℓ)) with hWdef
  have hW2 : Module.finrank F W = 2 := (I466b.fixN_natImage_qv c.pu c.via h464' hsq hx hxℓ hψ).1
  have hWne : W ≠ ⊥ := fun h => by rw [h, finrank_bot] at hW2; omega
  obtain ⟨v₁, hv₁W, hv₁⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
  have hlt : F ∙ v₁ < W := by
    refine lt_of_le_of_ne ((Submodule.span_singleton_le_iff_mem _ _).mpr hv₁W) fun he => ?_
    have h1 := finrank_span_singleton (K := F) hv₁
    rw [he, hW2] at h1
    omega
  obtain ⟨v₂, hv₂W, hv₂⟩ := IsConcreteLE.exists_of_lt hlt
  have hv₂0 : v₂ ≠ 0 := fun h => hv₂ (h ▸ Submodule.zero_mem _)
  have hv₃ : v₁ + v₂ ≠ 0 := fun h => hv₂ (Submodule.mem_span_singleton.mpr
    ⟨-1, by rw [neg_one_smul]; exact neg_eq_of_add_eq_zero_right h⟩)
  have hv₂₁ : v₁ ∉ F ∙ v₂ := fun h => by
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
    have ha0 : a ≠ 0 := by rintro rfl; rw [zero_smul] at ha; exact hv₁ ha.symm
    exact hv₂ (Submodule.mem_span_singleton.mpr
      ⟨a⁻¹, by rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]⟩)
  have hv₃₁ : v₁ ∉ F ∙ (v₁ + v₂) := fun h => by
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
    have ha0 : a ≠ 0 := by rintro rfl; rw [zero_smul] at ha; exact hv₁ ha.symm
    have e : a • v₂ = (1 - a) • v₁ := by
      calc a • v₂ = (a • v₁ + a • v₂) - a • v₁ := by abel
        _ = v₁ - a • v₁ := by rw [← smul_add, ha]
        _ = (1 - a) • v₁ := by rw [sub_smul, one_smul]
    exact hv₂ (Submodule.mem_span_singleton.mpr
      ⟨a⁻¹ * (1 - a), by rw [mul_smul, ← e, smul_smul, inv_mul_cancel₀ ha0, one_smul]⟩)
  have hv₃₂ : v₂ ∉ F ∙ (v₁ + v₂) := fun h => by
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
    by_cases ha1 : a = 1
    · rw [ha1, one_smul, add_eq_right] at ha
      exact hv₁ ha
    · have h1a : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
      have e : a • v₁ = (1 - a) • v₂ := by
        calc a • v₁ = (a • v₁ + a • v₂) - a • v₂ := by abel
          _ = v₂ - a • v₂ := by rw [← smul_add, ha]
          _ = (1 - a) • v₂ := by rw [sub_smul, one_smul]
      exact hv₂ (Submodule.mem_span_singleton.mpr
        ⟨(1 - a)⁻¹ * a, by rw [mul_smul, e, smul_smul, inv_mul_cancel₀ h1a, one_smul]⟩)
  obtain ⟨P₁, h₁, -, hP₁⟩ := exists_isPtOn_span h464 h465 c hx hxℓ hψs hψ hv₁W hv₁
  obtain ⟨P₂, h₂, -, hP₂⟩ := exists_isPtOn_span h464 h465 c hx hxℓ hψs hψ hv₂W hv₂0
  obtain ⟨P₃, h₃, -, hP₃⟩ :=
    exists_isPtOn_span h464 h465 c hx hxℓ hψs hψ (W.add_mem hv₁W hv₂W) hv₃
  obtain ⟨u₁, hu₁⟩ := natVec_surjective hψ v₁
  obtain ⟨u₂, hu₂⟩ := natVec_surjective hψ v₂
  have hu₁P₁ : (u₁ : (puAmalgam c.pu.le).Universal) ∈ P₁ :=
    (hP₁ u₁).mpr (by rw [hu₁]; exact Submodule.mem_span_singleton_self v₁)
  have hu₂P₂ : (u₂ : (puAmalgam c.pu.le).Universal) ∈ P₂ :=
    (hP₂ u₂).mpr (by rw [hu₂]; exact Submodule.mem_span_singleton_self v₂)
  refine ⟨P₁, P₂, P₃, h₁, h₂, h₃, fun he => ?_, fun he => ?_, fun he => ?_⟩
  · rw [he] at hu₁P₁; exact hv₂₁ (by rw [← hu₁]; exact (hP₂ u₁).mp hu₁P₁)
  · rw [he] at hu₁P₁
    have h := (hP₃ u₁).mp hu₁P₁
    rw [hu₁] at h
    exact hv₃₁ h
  · rw [he] at hu₂P₂
    have h := (hP₃ u₂).mp hu₂P₂
    rw [hu₂] at h
    exact hv₃₂ h

theorem eq_of_isPtOn_three (h464 : I464) (h465 : I465) (c : Hyp46 M T L φ)
    (hq : Fintype.card F = 2) {x ℓ : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxℓ : (puAmalgam c.pu.le).treeGraph.Adj x ℓ)
    {P₁ P₂ P₃ P : Subgroup (puAmalgam c.pu.le).Universal}
    (h₁ : IsPtOn (puAmalgam c.pu.le) x ℓ P₁) (h₂ : IsPtOn (puAmalgam c.pu.le) x ℓ P₂)
    (h₃ : IsPtOn (puAmalgam c.pu.le) x ℓ P₃) (hP : IsPtOn (puAmalgam c.pu.le) x ℓ P)
    (n₁₂ : P₁ ≠ P₂) (n₁₃ : P₁ ≠ P₃) (n₂₃ : P₂ ≠ P₃) : P = P₁ ∨ P = P₂ ∨ P = P₃ := by
  have h464' := h464 G M T L F φ c
  have hc4 : Nat.card ↥(Usup (puAmalgam c.pu.le) x ℓ) = 4 := by
    rw [(h465 G M T L F φ c x ℓ hx hxℓ).1, hq]; norm_num
  have hle : ∀ {Q}, IsPtOn (puAmalgam c.pu.le) x ℓ Q → Q ≤ Usup (puAmalgam c.pu.le) x ℓ :=
    fun {Q} ⟨_, _, _, hQ⟩ => hQ ▸ inf_le_left
  have hcard : ∀ {Q}, IsPtOn (puAmalgam c.pu.le) x ℓ Q → Nat.card ↥Q = 2 := fun {Q} hQ => by
    rw [card_of_isPtOn h464 h465 c hx hxℓ hQ, hq]
  have hUZ : Usup (puAmalgam c.pu.le) x ℓ ≤ ZM _ x := (h464' x ℓ hx hxℓ).trans (zh_le_zm _ hxℓ)
  exact eq_or_eq_or_eq_of_card_four hc4
    (fun a ha b hb => commute_of_mem_zm c hx (hUZ ha) (hUZ hb)) (hle h₁) (hle h₂) (hle h₃)
    (hle hP) (hcard h₁) (hcard h₂) (hcard h₃) (hcard hP) n₁₂ n₁₃ n₂₃

end Amalgam

end CFSG.Quasithin.MS93.S46R
