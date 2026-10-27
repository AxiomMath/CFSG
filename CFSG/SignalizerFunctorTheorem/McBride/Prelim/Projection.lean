module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.DirectProduct

public section

namespace CFSG.SignalizerFunctorTheorem.McBride

variable {G : Type*} [Group G]

private theorem map_conj_one (J : Subgroup G) : J.map (MulAut.conj (1 : G)).toMonoidHom = J := by
  ext x
  simp

private theorem map_conj_map_conj (J : Subgroup G) (a b : G) :
    (J.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      J.map (MulAut.conj (b * a)).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨j, hj, by simp [mul_assoc]⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨_, ⟨j, hj, rfl⟩, by simp [mul_assoc]⟩

private theorem map_conj_inv_map_conj (J : Subgroup G) (a : G) :
    (J.map (MulAut.conj a).toMonoidHom).map (MulAut.conj a⁻¹).toMonoidHom = J := by
  rw [map_conj_map_conj, inv_mul_cancel, map_conj_one]

private theorem map_conj_map_conj_inv (J : Subgroup G) (a : G) :
    (J.map (MulAut.conj a⁻¹).toMonoidHom).map (MulAut.conj a).toMonoidHom = J := by
  simpa using map_conj_inv_map_conj J a⁻¹

private theorem mem_normalizer_of_map_conj_eq {J : Subgroup G} {a b : G}
    (h : J.map (MulAut.conj a).toMonoidHom = J.map (MulAut.conj b).toMonoidHom) :
    b⁻¹ * a ∈ Subgroup.normalizer (J : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have h1 := map_conj_map_conj J a b⁻¹
  rw [h, map_conj_inv_map_conj] at h1
  exact h1.symm

private theorem exists_equivariant_fn {A J : Subgroup G} {x : G} (hxJ : x ∈ J)
    (hx : x ∈ Subgroup.centralizer ((A ⊓ Subgroup.normalizer (J : Set G) : Subgroup G) : Set G)) :
    ∃ f : Subgroup G → G, (∀ K, f K ∈ K) ∧ f J = x ∧
      (∀ c ∈ A, ∀ K, f (K.map (MulAut.conj c).toMonoidHom) = c * f K * c⁻¹) ∧
      ∀ K, f K = 1 ∨ ∃ a ∈ A, f K = a * x * a⁻¹ := by
  classical
  have key : ∀ a ∈ A, ∀ b ∈ A,
      J.map (MulAut.conj a).toMonoidHom = J.map (MulAut.conj b).toMonoidHom →
        a * x * a⁻¹ = b * x * b⁻¹ := by
    intro a ha b hb hab
    have hmem : b⁻¹ * a ∈ A ⊓ Subgroup.normalizer (J : Set G) :=
      Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hb) ha, mem_normalizer_of_map_conj_eq hab⟩
    have hc := Subgroup.mem_centralizer_iff.mp hx (b⁻¹ * a) hmem
    calc a * x * a⁻¹ = b * (b⁻¹ * a * x) * a⁻¹ := by group
      _ = b * (x * (b⁻¹ * a)) * a⁻¹ := by rw [hc]
      _ = b * x * b⁻¹ := by group
  let f : Subgroup G → G := fun K =>
    if h : ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom then h.choose * x * h.choose⁻¹ else 1
  have f_orbit : ∀ a ∈ A, f (J.map (MulAut.conj a).toMonoidHom) = a * x * a⁻¹ := by
    intro a ha
    have h : ∃ b ∈ A, J.map (MulAut.conj a).toMonoidHom = J.map (MulAut.conj b).toMonoidHom :=
      ⟨a, ha, rfl⟩
    simp only [f, dite_eq_left h]
    exact key _ h.choose_spec.1 a ha h.choose_spec.2.symm
  have f_not : ∀ K, (¬ ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom) → f K = 1 := by
    intro K hK
    simp only [f, dite_eq_right hK]
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro K
    by_cases h : ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom
    · obtain ⟨a, ha, rfl⟩ := h
      rw [f_orbit a ha]
      exact ⟨x, hxJ, rfl⟩
    · rw [f_not K h]
      exact one_mem K
  · have := f_orbit 1 (one_mem A)
    rwa [map_conj_one, one_mul, inv_one, mul_one] at this
  · intro c hc K
    by_cases h : ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom
    · obtain ⟨a, ha, rfl⟩ := h
      rw [map_conj_map_conj, f_orbit a ha, f_orbit (c * a) (mul_mem hc ha)]
      group
    · have h' : ¬ ∃ a ∈ A,
          K.map (MulAut.conj c).toMonoidHom = J.map (MulAut.conj a).toMonoidHom := by
        rintro ⟨b, hb, hKb⟩
        refine h ⟨c⁻¹ * b, mul_mem (inv_mem hc) hb, ?_⟩
        rw [← map_conj_map_conj, ← hKb, map_conj_inv_map_conj]
      rw [f_not K h, f_not _ h']
      group
  · intro K
    by_cases h : ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom
    · obtain ⟨a, ha, rfl⟩ := h
      exact Or.inr ⟨a, ha, f_orbit a ha⟩
    · exact Or.inl (f_not K h)

private theorem exists_coord_eq [Finite G] {S : Set (Subgroup G)} {L A : Subgroup G}
    (hL : IsDirectProduct S L)
    (hA : ∀ a ∈ A, ∀ J ∈ S, J.map (MulAut.conj a).toMonoidHom ∈ S) {J : Subgroup G} (hJ : J ∈ S)
    {x : G} (hxJ : x ∈ J)
    (hx : x ∈ Subgroup.centralizer ((A ⊓ Subgroup.normalizer (J : Set G) : Subgroup G) : Set G)) :
    ∃ y : L, (y : G) ∈ Subgroup.centralizer (A : Set G) ∧ ((hL.coord hJ y : J) : G) = x ∧
      ∀ M : Subgroup G, (∀ a ∈ A, a * x * a⁻¹ ∈ M) → (y : G) ∈ M := by
  obtain ⟨f, hfK, hfJ, hfc, hfv⟩ := exists_equivariant_fn hxJ hx
  let z : (K : S) → (K : Subgroup G) := fun K => ⟨f K, hfK K⟩
  let y : L := hL.equiv z
  have hcoord : ∀ (K : Subgroup G) (hK : K ∈ S), ((hL.coord hK y : K) : G) = f K :=
    fun K hK => congrArg Subtype.val (hL.coord_equiv hK z)
  refine ⟨y, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have hc' := hA c hc
    have hy : (⟨c * (y : G) * c⁻¹, hL.conj_mem hc' y.2⟩ : L) = y := by
      refine hL.ext_coord fun K hK => Subtype.ext ?_
      have hK₀ : K.map (MulAut.conj c⁻¹).toMonoidHom ∈ S := hA c⁻¹ (inv_mem hc) K hK
      have hK₀c := map_conj_map_conj_inv K c
      have h1 := hL.coord_conj hc' hK₀ y.2
      have h2 := hL.coord_val_congr hK (hc' _ hK₀) hK₀c.symm
        ⟨c * (y : G) * c⁻¹, hL.conj_mem hc' y.2⟩
      rw [h2, h1, hcoord _ hK₀, hcoord K hK, ← hfc c hc, hK₀c]
    have h : c * (y : G) * c⁻¹ = y := congrArg Subtype.val hy
    calc c * (y : G) = c * (y : G) * c⁻¹ * c := by group
      _ = (y : G) * c := by rw [h]
  · rw [hcoord J hJ, hfJ]
  · intro M hM
    refine hL.equiv_mem z fun K => ?_
    rcases hfv K with h | ⟨a, ha, h⟩
    · show f K ∈ M
      rw [h]
      exact one_mem M
    · show f K ∈ M
      rw [h]
      exact hM a ha

private theorem exists_coord_eq_of_free [Finite G] {S : Set (Subgroup G)} {L A : Subgroup G}
    (hL : IsDirectProduct S L)
    (hA : ∀ a ∈ A, ∀ J ∈ S, J.map (MulAut.conj a).toMonoidHom ∈ S)
    (hfree : ∀ a ∈ A, a ≠ 1 → ∀ J ∈ S, J.map (MulAut.conj a).toMonoidHom ≠ J)
    {K : Subgroup G} (hK : K ∈ S) {x : G} (hxK : x ∈ K) :
    ∃ y : L, (y : G) ∈ Subgroup.centralizer (A : Set G) ∧ ((hL.coord hK y : K) : G) = x ∧
      ∀ M : Subgroup G, (∀ a ∈ A, a * x * a⁻¹ ∈ M) → (y : G) ∈ M := by
  refine exists_coord_eq hL hA hK hxK ?_
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  obtain ⟨hnA, hnN⟩ := Subgroup.mem_inf.mp hn
  by_cases h1 : n = 1
  · subst h1
    simp
  · exact absurd (Subgroup.mem_normalizer_iff_map_conj_eq.mp hnN) (hfree n hnA h1 K hK)

theorem projIn_centralizer_eq [Finite G] {S : Set (Subgroup G)} {L A : Subgroup G}
    (hL : IsDirectProduct S L)
    (hA : ∀ a ∈ A, ∀ J ∈ S, J.map (MulAut.conj a).toMonoidHom ∈ S) {J : Subgroup G} (hJ : J ∈ S) :
    projIn S J (L ⊓ Subgroup.centralizer (A : Set G)) =
      J ⊓ Subgroup.centralizer ((A ⊓ Subgroup.normalizer (J : Set G) : Subgroup G) : Set G) := by
  ext x
  rw [hL.mem_projIn_iff hJ, Subgroup.mem_inf]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(hL.coord hJ y).2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    obtain ⟨hnA, hnN⟩ := Subgroup.mem_inf.mp hn
    have hyc := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2 n hnA
    have hn' := hA n hnA
    have hJn : J.map (MulAut.conj n).toMonoidHom = J :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hnN
    have hyy : (⟨n * (y : G) * n⁻¹, hL.conj_mem hn' y.2⟩ : L) = y :=
      Subtype.ext (show n * (y : G) * n⁻¹ = y by rw [hyc]; group)
    have h1 := hL.coord_conj hn' hJ y.2
    have h2 := hL.coord_val_congr (hn' J hJ) hJ hJn ⟨n * (y : G) * n⁻¹, hL.conj_mem hn' y.2⟩
    have h3 := h2.symm.trans h1
    rw [hyy] at h3
    calc n * ((hL.coord hJ y : J) : G)
        = n * ((hL.coord hJ y : J) : G) * n⁻¹ * n := by group
      _ = ((hL.coord hJ y : J) : G) * n := by rw [← h3]
  · rintro ⟨hxJ, hx⟩
    obtain ⟨y, hyC, hyx, -⟩ := exists_coord_eq hL hA hJ hxJ hx
    exact ⟨y, Subgroup.mem_inf.mpr ⟨y.2, hyC⟩, hyx⟩

theorem smear_eq_centralizer_of_transitive [Finite G] {S : Set (Subgroup G)} {L A : Subgroup G}
    (hL : IsDirectProduct S L)
    (hA : ∀ a ∈ A, ∀ J ∈ S, J.map (MulAut.conj a).toMonoidHom ∈ S) {J : Subgroup G} (hJ : J ∈ S)
    (htrans : ∀ K ∈ S, ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom) :
    smear J A = L ⊓ Subgroup.centralizer (A : Set G) := by
  have hoc : orbitClosure J A = L := by
    refine le_antisymm (orbitClosure_le fun a ha => hL.le (hA a ha J hJ)) ?_
    rw [← hL.sSup_eq]
    refine sSup_le fun K hK => ?_
    obtain ⟨a, ha, rfl⟩ := htrans K hK
    exact map_conj_le_orbitClosure J ha
  rw [smear, hoc]

theorem inf_centralizer_inf_sSup_eq_bot_of_transitive [Finite G] {S : Set (Subgroup G)}
    {L A : Subgroup G} (hL : IsDirectProduct S L)
    (hA : ∀ a ∈ A, ∀ J ∈ S, J.map (MulAut.conj a).toMonoidHom ∈ S) {J : Subgroup G} (hJ : J ∈ S)
    (htrans : ∀ K ∈ S, ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom) :
    L ⊓ Subgroup.centralizer (A : Set G) ⊓ sSup (S \ {J}) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf, Subgroup.mem_inf] at hx
  obtain ⟨⟨hxL, hxC⟩, hxS⟩ := hx
  have hy1 : hL.coord hJ ⟨x, hxL⟩ = 1 := (hL.coord_eq_one_iff hJ ⟨x, hxL⟩).mpr hxS
  have hy : (⟨x, hxL⟩ : L) = 1 := by
    refine hL.ext_coord fun K hK => ?_
    obtain ⟨a, ha, rfl⟩ := htrans K hK
    rw [map_one]
    refine Subtype.ext ?_
    have hax : a * x * a⁻¹ = x := by
      rw [Subgroup.mem_centralizer_iff.mp hxC a ha]
      group
    have h1 := hL.coord_conj (hA a ha) hJ hxL
    have hya : (⟨a * x * a⁻¹, hL.conj_mem (hA a ha) hxL⟩ : L) = ⟨x, hxL⟩ := Subtype.ext hax
    rw [hya, hy1] at h1
    simpa using h1
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hy)

theorem le_projIn_of_smear_le [Finite G] {S : Set (Subgroup G)} {L A W T : Subgroup G}
    (hL : IsDirectProduct S L)
    (hA : ∀ a ∈ A, ∀ J ∈ S, J.map (MulAut.conj a).toMonoidHom ∈ S)
    (hfree : ∀ a ∈ A, a ≠ 1 → ∀ J ∈ S, J.map (MulAut.conj a).toMonoidHom ≠ J)
    (_hW : W ≤ L ⊓ Subgroup.centralizer (A : Set G)) {K : Subgroup G} (hK : K ∈ S) (hTK : T ≤ K)
    (hT : smear T A ≤ W) : T ≤ projIn S K W := by
  intro t ht
  obtain ⟨y, hyC, hyt, hyM⟩ := exists_coord_eq_of_free hL hA hfree hK (hTK ht)
  have hyo : (y : G) ∈ orbitClosure T A :=
    hyM _ fun a ha => map_conj_le_orbitClosure T ha ⟨t, ht, rfl⟩
  have hyW : (y : G) ∈ W := hT (show (y : G) ∈ smear T A from Subgroup.mem_inf.mpr ⟨hyo, hyC⟩)
  exact (hL.mem_projIn_iff hK).mpr ⟨y, hyW, hyt⟩

theorem center_centralizer_eq [Finite G] {S : Set (Subgroup G)} {L A : Subgroup G}
    (hL : IsDirectProduct S L)
    (hA : ∀ a ∈ A, ∀ J ∈ S, J.map (MulAut.conj a).toMonoidHom ∈ S)
    (hfree : ∀ a ∈ A, a ≠ 1 → ∀ J ∈ S, J.map (MulAut.conj a).toMonoidHom ≠ J) :
    (L ⊓ Subgroup.centralizer (A : Set G)) ⊓
        Subgroup.centralizer ((L ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) =
      (L ⊓ Subgroup.centralizer (L : Set G)) ⊓ Subgroup.centralizer (A : Set G) := by
  ext z
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_inf]
  constructor
  · rintro ⟨⟨hzL, hzA⟩, hzC⟩
    refine ⟨⟨hzL, ?_⟩, hzA⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hcomm : (⟨w, hw⟩ : L) * ⟨z, hzL⟩ = ⟨z, hzL⟩ * ⟨w, hw⟩ := by
      refine hL.ext_coord fun K hK => ?_
      rw [map_mul, map_mul]
      obtain ⟨y, hyC, hyw, -⟩ :=
        exists_coord_eq_of_free hL hA hfree hK (hL.coord hK ⟨w, hw⟩).2
      have hyw' : hL.coord hK y = hL.coord hK ⟨w, hw⟩ := Subtype.ext hyw
      have hyz : y * ⟨z, hzL⟩ = ⟨z, hzL⟩ * y :=
        Subtype.ext (Subgroup.mem_centralizer_iff.mp hzC y (Subgroup.mem_inf.mpr ⟨y.2, hyC⟩))
      have h := congrArg (hL.coord hK) hyz
      rw [map_mul, map_mul, hyw'] at h
      exact h
    exact congrArg Subtype.val hcomm
  · rintro ⟨⟨hzL, hzCL⟩, hzA⟩
    refine ⟨⟨hzL, hzA⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subgroup.mem_centralizer_iff.mp hzCL h (Subgroup.mem_inf.mp hh).1

end CFSG.SignalizerFunctorTheorem.McBride
