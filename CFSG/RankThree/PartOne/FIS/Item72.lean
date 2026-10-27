module

public import CFSG.RankThree.PartOne.FIS.WRelation

public section

namespace CFSG.RankThree.PartOne.FIS

open CFSG.LocalAnalysis.GorensteinLyons (IsThreeTranspositions)
open CFSG.RankThree.PartTwo.Sec7

variable {G : Type*} [Group G] {D : Set G}

theorem ncard_centralizerIn_eq (hD : IsThreeTranspositions D)
    (htr : ∀ d ∈ D, ∀ e ∈ D, ∃ g : G, g * d * g⁻¹ = e) {x y : G} (hx : x ∈ D) (hy : y ∈ D) :
    (centralizerIn D x).ncard = (centralizerIn D y).ncard := by
  obtain ⟨g, rfl⟩ := htr x hx y hy
  have himg : centralizerIn D (g * x * g⁻¹) = (fun z => g * z * g⁻¹) '' centralizerIn D x := by
    ext z
    rw [mem_centralizerIn_conj hD]
    constructor
    · intro h
      exact ⟨g⁻¹ * z * g, h, by group⟩
    · rintro ⟨w, hw, rfl⟩
      simpa [mul_assoc] using hw
  rw [himg, Set.ncard_image_of_injective]
  intro a b h
  exact mul_left_cancel (mul_right_cancel h)

@[expose] def PairwiseComm (D : Set G) (x : G) : Prop :=
  ∀ e ∈ localSet D x, ∀ f ∈ localSet D x, e * f = f * e

theorem pairwiseComm_of_conj (hD : IsThreeTranspositions D)
    (htr : ∀ d ∈ D, ∀ e ∈ D, ∃ g : G, g * d * g⁻¹ = e) {d : G} (hd : d ∈ D)
    (h : PairwiseComm D d) {x : G} (hx : x ∈ D) : PairwiseComm D x := by
  obtain ⟨g, rfl⟩ := htr d hd x hx
  intro e he f hf
  have he' := (mem_localSet_conj hD g d e).1 he
  have hf' := (mem_localSet_conj hD g d f).1 hf
  have h1 := h _ he' _ hf'
  have := (conj_comm_iff g⁻¹ e f).1 (by simpa using h1)
  exact this

theorem mem_vSet_of_pairwiseComm [Finite G] (hD : IsThreeTranspositions D)
    (htr : ∀ d ∈ D, ∀ e ∈ D, ∃ g : G, g * d * g⁻¹ = e) {x y : G} (hx : x ∈ D)
    (hy : y ∈ localSet D x) (hc : PairwiseComm D x) : y ∈ vSet D x := by
  have hsub : centralizerIn D x ⊆ centralizerIn D y := by
    rintro z ⟨hz, hzx⟩
    refine ⟨hz, ?_⟩
    by_cases hzx' : z = x
    · rw [hzx']
      exact hy.2.1.symm
    · exact hc z ⟨hz, hzx, hzx'⟩ y hy
  have hle : (centralizerIn D y).ncard ≤ (centralizerIn D x).ncard :=
    (ncard_centralizerIn_eq hD htr hy.1 hx).le
  exact ⟨hy.1, (Set.eq_of_subset_of_ncard_le hsub hle).symm⟩

section Part3

variable [Finite G]

theorem mk_eq_of_comm (hD : IsThreeTranspositions D)
    (htr : ∀ d ∈ D, ∀ e ∈ D, ∃ g : G, g * d * g⁻¹ = e)
    (hc : ∀ x ∈ D, PairwiseComm D x) {x y : G} (hx : x ∈ D) (hy : y ∈ D) (hxy : x * y = y * x) :
    QuotientGroup.mk' (CFSG.pCore 2 G) x = QuotientGroup.mk' (CFSG.pCore 2 G) y := by
  by_cases hne : y = x
  · rw [hne]
  have hloc : y ∈ localSet D x := ⟨hy, hxy.symm, hne⟩
  have hv := mem_vSet_of_pairwiseComm hD htr hx hloc (hc x hx)
  rw [vSet_eq_conjOrbit hD htr hx] at hv
  obtain ⟨m, hm, rfl⟩ := hv
  have hm1 : QuotientGroup.mk' (CFSG.pCore 2 G) m = 1 := (QuotientGroup.eq_one_iff m).2 hm
  rw [map_mul, map_mul, map_inv, hm1, one_mul, inv_one, mul_one]

theorem item72_part3 (hD : IsThreeTranspositions D)
    (htr : ∀ d ∈ D, ∀ e ∈ D, ∃ g : G, g * d * g⁻¹ = e) {d : G} (hd : d ∈ D)
    (h2 : IsPGroup 2 (Subgroup.closure (localSet D d))) :
    (CFSG.pCore 3 (G ⧸ CFSG.pCore 2 G)).comap (QuotientGroup.mk' (CFSG.pCore 2 G)) ⊔
      Subgroup.zpowers d = ⊤ := by
  set N := CFSG.pCore 2 G with hN
  set π := QuotientGroup.mk' N with hπ
  have hcd : PairwiseComm D d := by
    intro e he f hf
    by_contra hef
    have h3 := tt_cube hD he.1 hf.1 hef
    have hmem : e * f ∈ Subgroup.closure (localSet D d) :=
      mul_mem (Subgroup.subset_closure he) (Subgroup.subset_closure hf)
    have h1 : e * f = 1 := eq_one_of_mem_pGroup h2 (by norm_num : Nat.Coprime 3 2) hmem h3
    have : f = e := by
      rw [← tt_inv_eq hD he.1]
      exact eq_inv_of_mul_eq_one_right h1
    exact hef (by rw [this])
  have hc : ∀ x ∈ D, PairwiseComm D x := fun x hx => pairwiseComm_of_conj hD htr hd hcd hx
  by_cases hdN : d ∈ N
  · have hDN : ∀ x ∈ D, x ∈ N := by
      intro x hx
      obtain ⟨g, rfl⟩ := htr d hd x hx
      exact Subgroup.Normal.conj_mem inferInstance d hdN g
    have hNtop : N = ⊤ := by
      rw [eq_top_iff, ← tt_closure_eq hD, Subgroup.closure_le]
      exact hDN
    rw [eq_top_iff]
    intro g _
    refine Subgroup.mem_sup_left ?_
    rw [Subgroup.mem_comap]
    have : g ∈ N := by rw [hNtop]; trivial
    rw [show π g = 1 from (QuotientGroup.eq_one_iff g).2 this]
    exact one_mem _
  have hxN : ∀ x ∈ D, x ∉ N := by
    intro x hx hxN'
    obtain ⟨g, hg⟩ := htr d hd x hx
    apply hdN
    have := Subgroup.Normal.conj_mem inferInstance x hxN' g⁻¹
    rwa [← hg, show g⁻¹ * (g * d * g⁻¹) * g⁻¹⁻¹ = d by group] at this
  let E : Set (G ⧸ N) := π '' D
  have hP : IsPGroup 3 (Subgroup.closure {z : G ⧸ N | ∃ a ∈ E, ∃ b ∈ E, z = a * b}) := by
    refine isPGroup_three_closure_mul E ?_ ?_ ?_ ?_ ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩ g
      obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
      exact ⟨g' * x * g'⁻¹, tt_conj_mem hD hx g', by simp [hπ]⟩
    · rw [← MonoidHom.map_closure, tt_closure_eq hD]
      exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, tt_mul_self hD hx, map_one]
    · rintro _ ⟨x, hx, rfl⟩ h
      exact hxN x hx ((QuotientGroup.eq_one_iff x).1 h)
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hab
      by_cases hxy : x * y = y * x
      · exact mk_eq_of_comm hD htr hc hx hy hxy
      · have h3 := tt_cube hD hx hy hxy
        refine WidthOne.eq_of_comm_of_cube ?_ ?_ hab ?_
        · rw [← map_mul, tt_mul_self hD hx, map_one]
        · rw [← map_mul, tt_mul_self hD hy, map_one]
        · rw [← map_mul, ← map_pow, h3, map_one]
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      by_cases hxy : x * y = y * x
      · rw [mk_eq_of_comm hD htr hc hx hy hxy, ← map_mul, tt_mul_self hD hy, map_one, one_pow]
      · rw [← map_mul, ← map_pow, tt_cube hD hx hy hxy, map_one]
  have hnorm : (Subgroup.closure {z : G ⧸ N | ∃ a ∈ E, ∃ b ∈ E, z = a * b}).Normal := by
    refine ⟨fun n hn g => ?_⟩
    induction hn using Subgroup.closure_induction with
    | mem s hs =>
      obtain ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩ := hs
      obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
      refine Subgroup.subset_closure ⟨π (g' * x * g'⁻¹), ⟨_, tt_conj_mem hD hx g', rfl⟩,
        π (g' * y * g'⁻¹), ⟨_, tt_conj_mem hD hy g', rfl⟩, ?_⟩
      simp [hπ]
    | one => simp
    | mul a b _ _ iha ihb =>
      rw [show g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) by group]
      exact mul_mem iha ihb
    | inv a _ iha =>
      rw [show g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ by group]
      exact inv_mem iha
  have hle : Subgroup.closure {z : G ⧸ N | ∃ a ∈ E, ∃ b ∈ E, z = a * b} ≤
      CFSG.pCore 3 (G ⧸ N) := le_sSup ⟨hnorm, hP⟩
  rw [eq_top_iff, ← tt_closure_eq hD, Subgroup.closure_le]
  intro x hx
  have hxd : x * d ∈ (CFSG.pCore 3 (G ⧸ N)).comap π := by
    rw [Subgroup.mem_comap]
    apply hle
    refine Subgroup.subset_closure ⟨π x, ⟨x, hx, rfl⟩, π d, ⟨d, hd, rfl⟩, ?_⟩
    simp [hπ]
  have := mul_mem (Subgroup.mem_sup_left hxd)
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers d) :
      d ∈ (CFSG.pCore 3 (G ⧸ N)).comap π ⊔ Subgroup.zpowers d)
  rwa [mul_assoc, tt_mul_self hD hd, mul_one] at this

end Part3

theorem inFischer42 : Item72 := fun _ _ _ _ hD htr _ hd =>
  ⟨vSet_eq_conjOrbit hD htr hd, wSet_eq_conjOrbit hD hd, item72_part3 hD htr hd⟩

theorem item72_proved : Item72 := inFischer42

end CFSG.RankThree.PartOne.FIS
