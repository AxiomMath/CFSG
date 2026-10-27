module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.FinalAuxComp

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Sec6S33

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

omit [Finite G] in
theorem eq_bot_of_conj_mem_of_isSolvable {J N : Subgroup G} (hJs : IsSimpleGroup ↥J)
    (hJnc : ¬ IsMulCommutative ↥J) (hNJ : N ≤ J) (hconj : ∀ c ∈ J, ∀ z ∈ N, c * z * c⁻¹ ∈ N)
    (hN : Group.IsSolvable ↥N) : N = ⊥ := by
  have hnorm : (N.subgroupOf J).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hconj g g.2 n hn
  rcases hnorm.eq_bot_or_eq_top with h1 | h1
  · rw [← Subgroup.map_subgroupOf_eq_of_le hNJ, h1, Subgroup.map_bot]
  · exfalso
    have hJN : J ≤ N := by
      intro x hx
      have : (⟨x, hx⟩ : ↥J) ∈ N.subgroupOf J := h1 ▸ Subgroup.mem_top _
      exact this
    have hJsol : Group.IsSolvable ↥J :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hJN)
    exact hJnc (isMulCommutative_iff.mpr fun a b => IsSimpleGroup.comm_iff_isSolvable.mpr hJsol a b)

omit [Finite G] in
theorem conj_mem_sSup {T : Set (Subgroup G)} {c : G}
    (hc : ∀ J ∈ T, c ∈ Subgroup.normalizer (J : Set G)) {l : G} (hl : l ∈ sSup T) :
    c * l * c⁻¹ ∈ sSup T := by
  have : sSup T ≤ (sSup T).comap (MulAut.conj c).toMonoidHom := by
    refine sSup_le fun J hJ x hx => ?_
    exact le_sSup hJ ((Subgroup.mem_normalizer_iff.mp (hc J hJ) x).mp hx)
  exact this hl

omit [Finite G] in
theorem centralizes_of_proj {S : Set (Subgroup G)} {L : Subgroup G} (hL : IsDirectProduct S L)
    {M : Subgroup G} {c : G} (hc : ∀ J ∈ S, c ∈ Subgroup.normalizer (J : Set G))
    (hcM : c ∈ Subgroup.centralizer (M : Set G)) (hproj : ∀ J ∈ S, J ≤ projIn S J M) :
    c ∈ Subgroup.centralizer (L : Set G) := by
  have h1 : L ≤ Subgroup.centralizer ({c} : Set G) := by
    rw [← hL.sSup_eq]
    refine sSup_le fun J hJ j hj => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hjp := hproj J hJ hj
    rw [projIn, mem_proj_iff (hL.commute_sSup_diff hJ)] at hjp
    obtain ⟨-, l, hl, hjl⟩ := hjp
    have hcomm : c * (j * l) = (j * l) * c := (Subgroup.mem_centralizer_iff.mp hcM _ hjl).symm
    have hj' : c * j * c⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hc J hJ) j).mp hj
    have hl' : c * l * c⁻¹ ∈ sSup (S \ {J}) := conj_mem_sSup (fun J' hJ' => hc J' hJ'.1) hl
    have heq : (c * j * c⁻¹) * (c * l * c⁻¹) = j * l := by
      calc (c * j * c⁻¹) * (c * l * c⁻¹) = c * (j * l) * c⁻¹ := by group
        _ = j * l := by rw [hcomm]; group
    have hmem1 : j⁻¹ * (c * j * c⁻¹) ∈ J := mul_mem (inv_mem hj) hj'
    have hmem2 : j⁻¹ * (c * j * c⁻¹) = l * (c * l * c⁻¹)⁻¹ := by
      calc j⁻¹ * (c * j * c⁻¹) = j⁻¹ * ((c * j * c⁻¹) * (c * l * c⁻¹)) * (c * l * c⁻¹)⁻¹ := by
            group
        _ = l * (c * l * c⁻¹)⁻¹ := by rw [heq]; group
    have hmem3 : j⁻¹ * (c * j * c⁻¹) ∈ sSup (S \ {J}) := by
      rw [hmem2]
      exact mul_mem hl (inv_mem hl')
    have hbot := (hL.isDirectPair hJ).inf_eq_bot
    have : j⁻¹ * (c * j * c⁻¹) ∈ J ⊓ sSup (S \ {J}) := ⟨hmem1, hmem3⟩
    rw [hbot, Subgroup.mem_bot] at this
    have h2 : c * j * c⁻¹ = j := by
      have := congrArg (fun y => j * y) this
      simpa using this
    have h3 := congrArg (· * c) h2
    simp only [mul_assoc, inv_mul_cancel, mul_one] at h3
    exact h3.symm
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact Subgroup.mem_centralizer_singleton_iff.mp (h1 hk)

theorem eq_bot_of_forall_projIn {S : Set (Subgroup G)} {L Y : Subgroup G}
    (hL : IsDirectProduct S L) (hYL : Y ≤ L) (h : ∀ J ∈ S, projIn S J Y = ⊥) : Y = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  have hinj := Thm210.projInHom_injective_pi hL hYL
  have key : ∀ (N : Subgroup G) (hN : N = ⊥) (x : ↥N), (x : G) = 1 := by
    intro N hN x
    subst hN
    exact Subgroup.mem_bot.mp x.2
  have h1 : (MonoidHom.pi (fun J : S => Thm210.projInHom hL J.2 hYL) : ↥Y →*
      ((J : S) → ↥(projIn S J.1 Y))) ⟨y, hy⟩ = 1 := by
    funext J
    apply Subtype.ext
    exact key _ (h J.1 J.2) _
  have h2 := hinj (h1.trans (map_one _).symm)
  have : y = 1 := congrArg Subtype.val h2
  rw [this]
  exact one_mem _

section Main

variable (h : Counterexample p A θ)

include h

theorem sup_zpowers_eq_of_mem {B : Subgroup G} (hB : B ∈ signalizerFunctorEk p 2 A) {e e' : G}
    (he : e ∈ B) (he1 : e ≠ 1) (he' : e' ∈ B) (hne : e' ∉ Subgroup.zpowers e) :
    Subgroup.zpowers e ⊔ Subgroup.zpowers e' = B := by
  have heA : e ∈ A := hB.1 he
  have he'A : e' ∈ A := hB.1 he'
  have he'1 : e' ≠ 1 := fun h1 => hne (h1 ▸ one_mem _)
  have hne' : Subgroup.zpowers e ≠ Subgroup.zpowers e' := fun heq =>
    hne (heq ▸ Subgroup.mem_zpowers e')
  have hsup := sup_mem_E2_of_ne h (zpowers_mem_E1 h heA he1) (zpowers_mem_E1 h he'A he'1) hne'
  exact Subgroup.eq_of_le_of_card_ge
    (sup_le (Subgroup.zpowers_le.mpr he) (Subgroup.zpowers_le.mpr he')) (by rw [hB.2, hsup.2])

theorem kOf_thetaOf_mono
    {B B' : Subgroup G} (hB : B ∈ rSet p A θ) (hB' : B' ∈ rSet p A θ)
    (hle : B ≤ B') : kOf (thetaOf θ B') ≤ kOf (thetaOf θ B) := by
  obtain ⟨hB1, hBA, hBns⟩ := h.mem_rSet_iff.mp hB
  obtain ⟨hB'1, hB'A, hB'ns⟩ := h.mem_rSet_iff.mp hB'
  rw [← h.perfRes_thetaOf_eq_kOf hB'1 hB'A hB'ns, ← h.perfRes_thetaOf_eq_kOf hB1 hBA hBns]
  exact perfRes_mono (thetaOf_anti hle)

theorem le_projIn_kOf
    {B : Subgroup G} (hB : B ∈ rSetN p A θ 2) {e e' : G} (he : e ∈ B)
    (he1 : e ≠ 1) (he' : e' ∈ B) (hne : e' ∉ Subgroup.zpowers e) {J : Subgroup G}
    (hJ : J ∈ lcal (θ e)) :
    J ≤ projIn (lcal (θ e)) J (kOf (thetaOf θ B)) := by
  have hθ := h.hyp.nearFunctor
  obtain ⟨hB1, hBA, hBns, hBcard⟩ := h.mem_rSetN_iff.mp hB
  have hBE : B ∈ signalizerFunctorEk p 2 A := ⟨hBA, hBcard⟩
  have heA : e ∈ A := hBA he
  have he'A : e' ∈ A := hBA he'
  have he'1 : e' ≠ 1 := fun h1 => hne (h1 ▸ one_mem _)
  have hen := NT.of_mem_rSetN_two h hB he he1
  have hBeq := sup_zpowers_eq_of_mem h hBE he he1 he' hne
  have hL := hen.isDirectProduct h
  have hA' : ∀ g ∈ Subgroup.zpowers e', ∀ J' ∈ lcal (θ e),
      J'.map (MulAut.conj g).toMonoidHom ∈ lcal (θ e) := fun g hg J' hJ' =>
    hen.conj_mem_lcal h (Subgroup.zpowers_le.mpr he'A hg) hJ'
  have hP : kOf (θ e) ⊓ Subgroup.centralizer ((Subgroup.zpowers e' : Subgroup G) : Set G) ≤
      kOf (thetaOf θ B) := by
    have := kOf_apply_inf_centralizer_le hθ heA he1 he'A he'1
    rw [hBeq] at this
    rwa [centralizer_zpowers_eq_singleton]
  have hprojP : J ≤ projIn (lcal (θ e)) J
      (kOf (θ e) ⊓ Subgroup.centralizer ((Subgroup.zpowers e' : Subgroup G) : Set G)) := by
    rw [projIn_centralizer_eq hL hA' hJ]
    by_cases hN : e' ∈ Subgroup.normalizer (J : Set G)
    · have hF : e' ∈ FN A θ e := by
        rw [hen.FN_eq h hJ]
        exact ⟨he'A, hN⟩
      have hc : e' ∈ Subgroup.centralizer (J : Set G) := by
        by_contra hc
        have := hen.isSolvable_of_mem_FN h hF hJ hc
        rw [hBeq] at this
        exact hBns this
      have hz : Subgroup.zpowers e' ≤ Subgroup.centralizer (J : Set G) :=
        Subgroup.zpowers_le.mpr hc
      refine le_inf le_rfl fun x hx => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact (Subgroup.mem_centralizer_iff.mp (hz hg.1) x hx).symm
    · have hbot : Subgroup.normalizer (J : Set G) ⊓ Subgroup.zpowers e' = ⊥ :=
        CFSG.SignalizerFunctorTheorem.inf_eq_bot_of_not_le h.hyp.prime
          ((zpowers_mem_E1 h he'A he'1).2.trans (pow_one p))
          (fun hle => hN (hle (Subgroup.mem_zpowers e')))
      have hbot' : Subgroup.zpowers e' ⊓ Subgroup.normalizer (J : Set G) = ⊥ := by
        rw [inf_comm]
        exact hbot
      rw [hbot']
      have htop : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
        Subgroup.centralizer_eq_top_iff_subset.mpr fun y hy => by
          rw [SetLike.mem_coe, Subgroup.mem_bot] at hy
          rw [hy]
          exact one_mem _
      rw [htop, inf_top_eq]
  exact hprojP.trans (Thm210.projIn_mono J hP)

theorem inf_centralizer_inf_kOf_eq_bot
    {B : Subgroup G} (hB : B ∈ rSetN p A θ 2)
    {X : Subgroup G} (hX : X ∈ assoc p A θ) (hXs : Group.IsSolvable ↥X)
    (hXK : kOf (thetaOf θ B) ≤ Subgroup.normalizer (X : Set G)) {e : G} (he : e ∈ B)
    (he1 : e ≠ 1) : X ⊓ Subgroup.centralizer ({e} : Set G) = ⊥ := by
  have hθ := h.hyp.nearFunctor
  obtain ⟨hB1, hBA, hBns, hBcard⟩ := h.mem_rSetN_iff.mp hB
  have hBE : B ∈ signalizerFunctorEk p 2 A := ⟨hBA, hBcard⟩
  have heA : e ∈ A := hBA he
  have hen := NT.of_mem_rSetN_two h hB he he1
  obtain ⟨e', he', hne⟩ := exists_mem_not_mem_zpowers h hBE heA
  have hL := hen.isDirectProduct h
  set K := kOf (thetaOf θ B) with hKdef
  set Ke := kOf (θ e) with hKe
  set Z := X ⊓ Subgroup.centralizer ({e} : Set G) with hZ
  have hKBe : K ≤ Ke := by
    have hBR := hB.1
    have hzR := hen.zpowers_mem_rSet h
    have := kOf_thetaOf_mono h hzR hBR (Subgroup.zpowers_le.mpr he)
    rwa [hθ.isFunctor.thetaOf_zpowers heA he1] at this
  have hKc : K ≤ Subgroup.centralizer ({e} : Set G) := by
    intro k hk
    have hkB := kOf_le _ hk
    have := hθ.isFunctor.thetaOf_le_centralizer hBA hkB
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr he) this
  have hKnZ : ∀ k ∈ K, ∀ z ∈ Z, k * z * k⁻¹ ∈ Z := by
    intro k hk z hz
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hXK hk) z).mp hz.1, ?_⟩
    have hkc := Subgroup.mem_centralizer_singleton_iff.mp (hKc hk)
    have hzc := Subgroup.mem_centralizer_singleton_iff.mp hz.2
    have hke' : k⁻¹ * e = e * k⁻¹ := by
      have := congrArg (fun y => k⁻¹ * y * k⁻¹) hkc
      simp only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] at this
      exact this.symm
    show k * z * k⁻¹ ∈ Subgroup.centralizer ({e} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc k * z * k⁻¹ * e = k * z * (k⁻¹ * e) := by group
      _ = k * z * (e * k⁻¹) := by rw [hke']
      _ = k * (z * e) * k⁻¹ := by group
      _ = k * (e * z) * k⁻¹ := by rw [hzc]
      _ = (k * e) * z * k⁻¹ := by group
      _ = (e * k) * z * k⁻¹ := by rw [hkc]
      _ = e * (k * z * k⁻¹) := by group
  have hZH : Z ≤ θ e := fun z hz => hX.2.2.1 e heA he1 ⟨hz.1, hz.2⟩
  have hKeN : θ e ≤ Subgroup.normalizer (Ke : Set G) := Nonsolv.le_normalizer_kOf (θ e)
  have hY : ∀ k ∈ K, ∀ y ∈ Z ⊓ Ke, k * y * k⁻¹ ∈ Z ⊓ Ke := by
    intro k hk y hy
    refine ⟨hKnZ k hk y hy.1, ?_⟩
    have hkH : k ∈ θ e := kOf_le _ (hKBe hk)
    exact (Subgroup.mem_normalizer_iff.mp (hKeN hkH) y).mp hy.2
  have hYsol : Group.IsSolvable ↥(Z ⊓ Ke) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective
      ((inf_le_left : Z ⊓ Ke ≤ Z).trans (inf_le_left : Z ≤ X)))
  have hYbot : Z ⊓ Ke = ⊥ := by
    refine eq_bot_of_forall_projIn hL inf_le_right fun J hJ => ?_
    have hproj := le_projIn_kOf h hB he he1 he' hne hJ
    obtain ⟨-, -, hJs, hJnc⟩ := mem_lcal_iff.mp hJ
    refine eq_bot_of_conj_mem_of_isSolvable hJs hJnc (projIn_le J _) ?_
      (Thm210.isSolvable_projIn hL hJ inf_le_right hYsol)
    intro c hc z hz
    exact Thm210.projIn_conj_mem hL hJ hY c (hproj hc) z hz
  rw [eq_bot_iff]
  intro z hz
  have hzH : z ∈ θ e := hZH hz
  have hzK : z ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h1 : z * k * z⁻¹ * k⁻¹ ∈ Z ⊓ Ke := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have h2 := hKnZ k hk z⁻¹ (inv_mem hz)
        have e1 : z * k * z⁻¹ * k⁻¹ = z * (k * z⁻¹ * k⁻¹) := by group
        rw [e1]
        exact mul_mem hz h2
      · have hkKe : k ∈ Ke := hKBe hk
        have := (Subgroup.mem_normalizer_iff.mp (hKeN hzH) k).mp hkKe
        exact mul_mem this (inv_mem hkKe)
    rw [hYbot, Subgroup.mem_bot] at h1
    have h3 : z * k = k * z := by
      have := h1
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
      exact this
    exact h3.symm
  have hz1 : z ∈ Subgroup.centralizer (Ke : Set G) :=
    centralizes_of_proj hL (fun J hJ => hen.normalizes_lcal h hzH J hJ) hzK
      (fun J hJ => le_projIn_kOf h hB he he1 he' hne hJ)
  have hbot : θ e ⊓ Subgroup.centralizer (Ke : Set G) = ⊥ :=
    centralizer_kOf_eq_bot (hen.sol_eq_bot h)
  have : z ∈ θ e ⊓ Subgroup.centralizer (Ke : Set G) := ⟨hzH, hz1⟩
  rw [hbot] at this
  exact this

theorem eq_bot_of_rSetN_two
    {B : Subgroup G} (hB : B ∈ rSetN p A θ 2) {X : Subgroup G}
    (hX : X ∈ assoc p A θ) (hXs : Group.IsSolvable ↥X)
    (hXK : kOf (thetaOf θ B) ≤ Subgroup.normalizer (X : Set G)) : X = ⊥ := by
  obtain ⟨hB1, hBA, hBns, hBcard⟩ := h.mem_rSetN_iff.mp hB
  have hBE : B ∈ signalizerFunctorEk p 2 A := ⟨hBA, hBcard⟩
  have hrank : p ^ 2 ≤ Nat.card B := hBcard.ge
  have hBX : B ≤ Subgroup.normalizer (X : Set G) := hBA.trans hX.1
  have hgen := iSup_centralizer_nonidentity h.hyp.prime (isElemAbelian_of_le h hBA) hrank hBX
    hX.2.1
  rw [eq_bot_iff, ← hgen]
  exact iSup_le fun e => iSup_le fun he => iSup_le fun he1 =>
    (inf_centralizer_inf_kOf_eq_bot h hB hX hXs hXK he he1).le

theorem eq_bot_of_rSet
    {B : Subgroup G} (hB : B ∈ rSet p A θ) {X : Subgroup G}
    (hX : X ∈ assoc p A θ) (hXs : Group.IsSolvable ↥X)
    (hXK : kOf (thetaOf θ B) ≤ Subgroup.normalizer (X : Set G)) : X = ⊥ := by
  rcases h.card_of_mem_rSet hB with hc | hc
  · obtain ⟨B', hB', hBB'⟩ := h.exists_rSetN_two_ge hB
    exact eq_bot_of_rSetN_two h hB' hX hXs ((kOf_thetaOf_mono h hB hB'.1 hBB').trans hXK)
  · exact eq_bot_of_rSetN_two h ⟨hB, hc⟩ hX hXs hXK

end Main

end Sec6S33

end CFSG.SignalizerFunctorTheorem.McBride.Near
