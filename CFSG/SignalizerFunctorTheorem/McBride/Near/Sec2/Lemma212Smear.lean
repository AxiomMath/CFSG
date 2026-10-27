module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma212Setup

public section

open CFSG.Open
open scoped Pointwise

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma212

variable {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} {A B G : Subgroup Γ}

namespace GoodB

variable (H : Hyp p A G) (hB : GoodB A B G)

include H hB

theorem orbit_data {J : Subgroup Γ} (hJ : J ∈ lcal G) :
    ∃ (S₁ : Set (Subgroup Γ)) (_ : IsDirectProduct S₁ (orbitClosure J A)),
      S₁ ⊆ lcal G ∧ J ∈ S₁ ∧
      (∀ K ∈ S₁, ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom) ∧
      smear J B = orbitClosure J A ⊓ Subgroup.centralizer (B : Set Γ) ∧
      projIn S₁ J (smear J B) = J ∧ smear J B ⊓ sSup (S₁ \ {J}) = ⊥ := by
  have hG₁ := isDirectProduct_orbit (J := J) H.near.admits hJ
  have hAS : ∀ b ∈ B, ∀ K ∈ {K | ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom},
      K.map (MulAut.conj b).toMonoidHom ∈
        {K | ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom} := by
    rintro b hb _ ⟨a, ha, rfl⟩
    exact ⟨b * a, mul_mem (hB.le hb) ha, Thm210.map_conj_map_conj J a b⟩
  have hJ₁ : J ∈ {K | ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom} :=
    ⟨1, one_mem A, (Thm210.map_conj_one J).symm⟩
  have htr : ∀ K ∈ {K | ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom},
      ∃ b ∈ B, K = J.map (MulAut.conj b).toMonoidHom := by
    rintro _ ⟨a, ha, rfl⟩
    exact hB.trans J hJ a ha
  have hsm : smear J B = orbitClosure J A ⊓ Subgroup.centralizer (B : Set Γ) :=
    smear_eq_centralizer_of_transitive hG₁ hAS hJ₁ htr
  have hproj := projIn_centralizer_eq hG₁ hAS hJ₁
  have hbot := inf_centralizer_inf_sSup_eq_bot_of_transitive hG₁ hAS hJ₁ htr
  refine ⟨_, hG₁, ?_, hJ₁, fun K hK => hK, hsm, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact H.A_perm_lcal ha hJ
  · rw [hsm, hproj]
    refine le_antisymm inf_le_left fun x hx => Subgroup.mem_inf.mpr ⟨hx, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (Subgroup.mem_centralizer_iff.mp (hB.free J hJ hb) x hx).symm
  · rw [hsm]
    exact hbot

theorem smear_eq {J : Subgroup Γ} (hJ : J ∈ lcal G) :
    smear J B = orbitClosure J A ⊓ Subgroup.centralizer (B : Set Γ) := by
  obtain ⟨-, -, -, -, -, hsm, -, -⟩ := orbit_data H hB hJ
  exact hsm

theorem smear_le {J : Subgroup Γ} (hJ : J ∈ lcal G) :
    smear J B ≤ kOf G ⊓ Subgroup.centralizer (B : Set Γ) := by
  rw [smear_eq H hB hJ]
  exact inf_le_inf_right _ (orbitClosure_le_of_normalizer (H.hK.le hJ) H.A_le_normalizer)

theorem projIn_smear {J : Subgroup Γ} (hJ : J ∈ lcal G) : projIn (lcal G) J (smear J B) = J := by
  obtain ⟨S₁, hG₁, hS₁, hJ₁, -, -, hproj, -⟩ := orbit_data H hB hJ
  have hG := H.hK
  refine le_antisymm (projIn_le J _) fun x hx => ?_
  have hx' : x ∈ projIn S₁ J (smear J B) := by
    rw [hproj]
    exact hx
  obtain ⟨y, hyD, rfl⟩ := (hG₁.mem_projIn_iff hJ₁).mp hx'
  exact (hG.mem_projIn_iff hJ).mpr ⟨⟨y, Thm210.le_of_subset hG hG₁ hS₁ y.2⟩, hyD,
    (Thm210.coord_eq_of_subset hG hG₁ hS₁ hJ₁ y.2).symm⟩

theorem smear_inf_sSup {J : Subgroup Γ} (hJ : J ∈ lcal G) :
    smear J B ⊓ sSup (lcal G \ {J}) = ⊥ := by
  obtain ⟨S₁, hG₁, hS₁, hJ₁, -, hsm, -, hbot⟩ := orbit_data H hB hJ
  have hG := H.hK
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hyD, hyS⟩ := Subgroup.mem_inf.mp hy
  have hyG₁ : y ∈ orbitClosure J A := (Subgroup.mem_inf.mp (hsm ▸ hyD)).1
  have hy1 : hG.coord hJ ⟨y, Thm210.le_of_subset hG hG₁ hS₁ hyG₁⟩ = 1 :=
    (hG.coord_eq_one_iff hJ _).mpr hyS
  have hy2 : hG₁.coord hJ₁ ⟨y, hyG₁⟩ = 1 := by
    apply Subtype.ext
    rw [Thm210.coord_eq_of_subset hG hG₁ hS₁ hJ₁ hyG₁, hy1]
  have hy3 : y ∈ sSup (S₁ \ {J}) := (hG₁.coord_eq_one_iff hJ₁ _).mp hy2
  have : y ∈ smear J B ⊓ sSup (S₁ \ {J}) := Subgroup.mem_inf.mpr ⟨hyD, hy3⟩
  rwa [hbot] at this

theorem smear_le_sSup {J J' : Subgroup Γ} (hJ : J ∈ lcal G)
    (hne : ∀ a ∈ A, J' ≠ J.map (MulAut.conj a).toMonoidHom) :
    smear J B ≤ sSup (lcal G \ {J'}) := by
  obtain ⟨S₁, hG₁, hS₁, hJ₁, hS₁orb, hsm, -, -⟩ := orbit_data H hB hJ
  rw [hsm]
  refine inf_le_left.trans ?_
  rw [← hG₁.sSup_eq]
  refine sSup_le_sSup fun K hK => ⟨hS₁ hK, fun hKJ' => ?_⟩
  obtain ⟨a, ha, rfl⟩ := hS₁orb K hK
  exact hne a ha (Set.mem_singleton_iff.mp hKJ').symm

omit hB in
theorem mem_orbitClosure_of_coord {J : Subgroup Γ} {x : Γ} (hx : x ∈ kOf G)
    (h : ∀ (J' : Subgroup Γ) (hJ' : J' ∈ lcal G),
      (∀ a ∈ A, J' ≠ J.map (MulAut.conj a).toMonoidHom) →
        ((H.hK.coord hJ' ⟨x, hx⟩ : J') : Γ) = 1) :
    x ∈ orbitClosure J A := by
  classical
  have hK := H.hK
  let T : Subgroup Γ → Subgroup Γ := fun J' =>
    if ∃ a ∈ A, J' = J.map (MulAut.conj a).toMonoidHom then J' else ⊥
  have T_pos : ∀ J', (∃ a ∈ A, J' = J.map (MulAut.conj a).toMonoidHom) → T J' = J' :=
    fun J' hc => ite_eq_left hc
  have T_neg : ∀ J', ¬ (∃ a ∈ A, J' = J.map (MulAut.conj a).toMonoidHom) → T J' = ⊥ :=
    fun J' hc => ite_eq_right hc
  have hT : ∀ J' ∈ lcal G, T J' ≤ J' := by
    intro J' _
    by_cases hc : ∃ a ∈ A, J' = J.map (MulAut.conj a).toMonoidHom
    · rw [T_pos J' hc]
    · rw [T_neg J' hc]
      exact bot_le
  have hmem := (Thm210.mem_sSup_image_iff hK hT (x := x)).mpr
    ⟨hx, fun J' hJ' => by
      by_cases hc : ∃ a ∈ A, J' = J.map (MulAut.conj a).toMonoidHom
      · rw [T_pos J' hc]
        exact (hK.coord hJ' ⟨x, hx⟩).2
      · have hne : ∀ a ∈ A, J' ≠ J.map (MulAut.conj a).toMonoidHom := by
          intro a ha hJ'a
          exact hc ⟨a, ha, hJ'a⟩
        rw [T_neg J' hc, Subgroup.mem_bot]
        exact h J' hJ' hne⟩
  refine (sSup_le ?_ : sSup {K | ∃ J' ∈ lcal G, K = T J'} ≤ orbitClosure J A) hmem
  rintro K ⟨J', hJ', rfl⟩
  by_cases hc : ∃ a ∈ A, J' = J.map (MulAut.conj a).toMonoidHom
  · rw [T_pos J' hc]
    obtain ⟨a, ha, rfl⟩ := hc
    exact map_conj_le_orbitClosure J ha
  · rw [T_neg J' hc]
    exact bot_le

theorem exists_mulEquiv_smear {J : Subgroup Γ} (hJ : J ∈ lcal G) :
    Nonempty (↥(smear J B) ≃* ↥J) := by
  have hG := H.hK
  have hle : smear J B ≤ kOf G := (smear_le H hB hJ).trans inf_le_left
  let ψ : ↥(smear J B) →* ↥J := (hG.coord hJ).comp (Subgroup.inclusion hle)
  refine ⟨MulEquiv.ofBijective ψ ⟨?_, ?_⟩⟩
  · rw [injective_iff_map_eq_one]
    intro y hy
    have h1 : (y : Γ) ∈ sSup (lcal G \ {J}) := (hG.coord_eq_one_iff hJ _).mp hy
    have h2 : (y : Γ) ∈ smear J B ⊓ sSup (lcal G \ {J}) := Subgroup.mem_inf.mpr ⟨y.2, h1⟩
    rw [smear_inf_sSup H hB hJ, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  · intro z
    have hz : (z : Γ) ∈ projIn (lcal G) J (smear J B) := by
      rw [projIn_smear H hB hJ]
      exact z.2
    obtain ⟨y, hy, hyz⟩ := (hG.mem_projIn_iff hJ).mp hz
    exact ⟨⟨y, hy⟩, Subtype.ext hyz⟩

theorem isSimpleGroup_smear {J : Subgroup Γ} (hJ : J ∈ lcal G) : IsSimpleGroup ↥(smear J B) := by
  obtain ⟨e⟩ := exists_mulEquiv_smear H hB hJ
  have : IsSimpleGroup ↥J := (mem_lcal_iff.mp hJ).2.2.1
  exact e.isSimpleGroup

theorem not_isSolvable_smear {J : Subgroup Γ} (hJ : J ∈ lcal G) :
    ¬ Group.IsSolvable ↥(smear J B) := by
  obtain ⟨e⟩ := exists_mulEquiv_smear H hB hJ
  intro hs
  exact not_isSolvable_of_mem_lcal hJ
    (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)

theorem smear_map_conj_of_mem {J : Subgroup Γ} (hJ : J ∈ lcal G) {a : Γ} (ha : a ∈ A) :
    smear (J.map (MulAut.conj a).toMonoidHom) B = smear J B := by
  rw [smear_eq H hB (H.A_perm_lcal ha hJ), smear_eq H hB hJ, orbitClosure_map_conj_of_mem J ha]

end GoodB

end CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma212
