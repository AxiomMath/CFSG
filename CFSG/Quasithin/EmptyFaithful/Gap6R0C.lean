module

public import CFSG.Quasithin.Background.B1Solvable
public import CFSG.GroupTheory.BaerSuzuki

public section

namespace CFSG.Quasithin

namespace Gap6

open CFSG.Open CFSG.LieType.BorelTits

section Six

variable {Y : Type*} [Group Y]

theorem exists_zpowers_cube_of_card_six [Finite Y] (h6 : Nat.card Y = 6) :
    ∃ x : Y, (Subgroup.zpowers x).Normal ∧ (Subgroup.zpowers x).index = 2 ∧
      ∀ y, y ∈ Subgroup.zpowers x ↔ y ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Y) 3
    (show 3 ∣ Nat.card Y by rw [h6]; norm_num)
  have hcard : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hx]
  have hindex : (Subgroup.zpowers x).index = 2 := by
    have := Subgroup.index_mul_card (H := Subgroup.zpowers x)
    rw [hcard, h6] at this
    omega
  have hnorm : (Subgroup.zpowers x).Normal := Subgroup.normal_of_index_eq_two hindex
  refine ⟨x, hnorm, hindex, fun y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
  · have h1 := pow_card_eq_one' (G := ↥(Subgroup.zpowers x)) (x := ⟨y, hy⟩)
    rw [hcard] at h1
    exact congrArg Subtype.val h1
  · have h2 : y ^ 2 ∈ Subgroup.zpowers x := by
      have := Subgroup.pow_index_mem (Subgroup.zpowers x) y
      rwa [hindex] at this
    have e : y = (y ^ 2) ^ 2 := by
      calc y = y ^ 3 * y := by rw [hy, one_mul]
        _ = (y ^ 2) ^ 2 := by group
    rw [e]
    exact Subgroup.pow_mem _ h2 2

theorem commute_of_cube_card_six [Finite Y] (h6 : Nat.card Y = 6) {u v : Y} (hu : u ^ 3 = 1)
    (hv : v ^ 3 = 1) : u * v = v * u := by
  obtain ⟨x, -, -, hx⟩ := exists_zpowers_cube_of_card_six h6
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ((hx u).2 hu)
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp ((hx v).2 hv)
  exact ((Commute.refl x).zpow_zpow i j).eq

theorem cube_of_involutions_card_six [Finite Y] (h6 : Nat.card Y = 6) {u v : Y} (hu1 : u ≠ 1)
    (hv1 : v ≠ 1) (hu : u * u = 1) (hv : v * v = 1) : (u * v) ^ 3 = 1 := by
  obtain ⟨x, hxn, hxi, hx⟩ := exists_zpowers_cube_of_card_six h6
  have hnotin : ∀ y : Y, y ≠ 1 → y * y = 1 → y ∉ Subgroup.zpowers x := by
    intro y hy1 hyy hmem
    have h3 := (hx y).1 hmem
    apply hy1
    have e : y = y ^ 3 * (y * y)⁻¹ := by group
    rw [h3, hyy] at e
    simpa using e
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.mp hxi
  have hua : u * a ∈ Subgroup.zpowers x := by
    rcases ha u with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd h1 (hnotin u hu1 hu)
  have hva : v * a ∈ Subgroup.zpowers x := by
    rcases ha v with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd h1 (hnotin v hv1 hv)
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have h2 : a⁻¹ * v ∈ Subgroup.zpowers x := by
    have := Subgroup.inv_mem _ hva
    rwa [mul_inv_rev, hvinv] at this
  have h3 : u * v ∈ Subgroup.zpowers x := by
    have : u * v = (u * a) * (a⁻¹ * v) := by group
    rw [this]
    exact Subgroup.mul_mem _ hua h2
  exact (hx _).1 h3

end Six

section Blocks

variable {W : Type*} [CommGroup W] [Finite W]

theorem exists_blocks (hW : ∀ w : W, w ^ 2 = 1) {X₀ : Subgroup (MulAut W)}
    (hsolv : Group.IsSolvable ↥X₀) (hO2 : pCoreOf 2 X₀ = ⊥) :
    ∃ 𝓗 : Finset (Subgroup (MulAut W)),
      IsTransvectionBlocks (Subgroup.closure (transvectionsIn X₀)) 𝓗 := by
  have hJX := B1.closure_transvectionsIn_le X₀
  have hsolvJ : Group.IsSolvable ↥(Subgroup.closure (transvectionsIn X₀)) :=
    B1.solvable_of_le hJX hsolv
  have hOJ := B1.normal_two_subgroups_trivial_of_normal hJX
    (fun x hx j hj => B1.closure_transvectionsIn_normal x hx j hj)
    (normal_two_subgroups_trivial_of_pCoreOf_eq_bot hO2)
  have hcl : Subgroup.closure (transvectionsIn (Subgroup.closure (transvectionsIn X₀))) =
      Subgroup.closure (transvectionsIn X₀) := by
    apply le_antisymm
    · exact (Subgroup.closure_le _).2 fun t ht => ht.1
    · exact Subgroup.closure_mono fun t ht => ⟨Subgroup.subset_closure ht, ht.2⟩
  exact transvection_structure hW hsolvJ hOJ hcl

variable {Y : Subgroup (MulAut W)} {𝓗 : Finset (Subgroup (MulAut W))}

omit [Finite W] in
theorem block_of_prod (hb : IsTransvectionBlocks Y 𝓗) (hW : ∀ w : W, w ^ 2 = 1) {s s' : MulAut W}
    (hs : s ∈ transvectionsIn Y) (hs' : s' ∈ transvectionsIn Y) (h3 : (s * s') ^ 3 = 1) :
    ∃ K ∈ 𝓗, s * s' ∈ K := by
  obtain ⟨K₁, hK₁, hsK₁⟩ := hb.cover s hs
  obtain ⟨K₂, hK₂, hsK₂⟩ := hb.cover s' hs'
  by_cases hK : K₁ = K₂
  · subst hK
    exact ⟨K₁, hK₁, K₁.mul_mem hsK₁ hsK₂⟩
  · have hc : s * s' = s' * s := hb.comm K₁ hK₁ K₂ hK₂ hK s hsK₁ s' hsK₂
    obtain ⟨hs1, w, hw⟩ := hs.2
    obtain ⟨hs1', w', hw'⟩ := hs'.2
    have hss := B1.tv_sq hW hw hs1
    have hss' := B1.tv_sq hW hw' hs1'
    have h2 : (s * s') ^ 2 = 1 := by
      calc (s * s') ^ 2 = s * s' * (s * s') := sq _
        _ = s * (s' * s) * s' := by group
        _ = s * (s * s') * s' := by rw [hc]
        _ = (s * s) * (s' * s') := by group
        _ = 1 := by rw [hss, hss', one_mul]
    have h1 : s * s' = 1 := by
      calc s * s' = (s * s') ^ 3 * ((s * s') ^ 2)⁻¹ := by group
        _ = 1 := by rw [h3, h2]; simp
    exact ⟨K₁, hK₁, h1 ▸ K₁.one_mem⟩

theorem commute_of_cube (hb : IsTransvectionBlocks Y 𝓗) {K K' : Subgroup (MulAut W)} (hK : K ∈ 𝓗)
    (hK' : K' ∈ 𝓗) {u u' : MulAut W} (hu : u ∈ K) (hu' : u' ∈ K') (h3 : u ^ 3 = 1)
    (h3' : u' ^ 3 = 1) : u * u' = u' * u := by
  by_cases hKK : K = K'
  · subst hKK
    have h6 := hb.card_eq K hK
    have := commute_of_cube_card_six h6 (u := ⟨u, hu⟩) (v := ⟨u', hu'⟩)
      (Subtype.ext (by simpa using h3)) (Subtype.ext (by simpa using h3'))
    exact congrArg Subtype.val this
  · exact hb.comm K hK K' hK' hKK u hu u' hu'

theorem cube_of_involutions (hb : IsTransvectionBlocks Y 𝓗) {K : Subgroup (MulAut W)} (hK : K ∈ 𝓗)
    {u v : MulAut W} (hu : u ∈ K) (hv : v ∈ K) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (hu2 : u * u = 1)
    (hv2 : v * v = 1) : (u * v) ^ 3 = 1 := by
  have h6 := hb.card_eq K hK
  have := cube_of_involutions_card_six h6 (u := ⟨u, hu⟩) (v := ⟨v, hv⟩)
    (fun h => hu1 (congrArg Subtype.val h)) (fun h => hv1 (congrArg Subtype.val h))
    (Subtype.ext (by simpa using hu2)) (Subtype.ext (by simpa using hv2))
  simpa using congrArg Subtype.val this

end Blocks

section Closure

theorem isPGroup_closure_of_pairwise_commute {G' : Type*} [Group G'] {p : ℕ} {S : Set G'}
    (hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hp : ∀ x ∈ S, x ^ p = 1) :
    IsPGroup p ↥(Subgroup.closure S) := by
  have hSc : S ⊆ Subgroup.centralizer S := by
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    exact hS y hy x hx
  have hcl : Subgroup.closure S ≤ Subgroup.centralizer S :=
    (Subgroup.closure_le_centralizer_centralizer S).trans (Subgroup.centralizer_le hSc)
  have hcomm : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x := by
    intro x hx y hy
    have h1 : ∀ s ∈ S, s * y = y * s := fun s hs =>
      (Subgroup.mem_centralizer_iff.mp (hcl hy) s hs)
    have h2 : Subgroup.closure S ≤ Subgroup.centralizer {y} := by
      rw [Subgroup.closure_le]
      intro s hs
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact h1 s hs
    exact Subgroup.mem_centralizer_singleton_iff.mp (h2 hx)
  have hpow : ∀ x ∈ Subgroup.closure S, x ^ p = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hp x hx
    | one => simp
    | mul x y hxm hym hx hy =>
      rw [Commute.mul_pow (show Commute x y from hcomm x hxm y hym), hx, hy, one_mul]
    | inv x hxm hx => rw [inv_pow, hx, inv_one]
  intro g
  exact ⟨1, Subtype.ext (by simpa using hpow g g.2)⟩

end Closure

section Claim

variable {Γ : Type*} [Group Γ]

theorem claim_A2_abstract {W₀ WC : Type*} [CommGroup W₀] [Finite W₀] [CommGroup WC] [Finite WC]
    (hW₀ : ∀ w : W₀, w ^ 2 = 1) (ρ₀ : Γ →* MulAut W₀) (ρC : Γ →* MulAut WC)
    (hsolv : Group.IsSolvable Γ) (hO₀ : pCoreOf 2 ρ₀.range = ⊥)
    (hOC : CFSG.pCore 2 ↥ρC.range = ⊥)
    {J : Subgroup Γ} (hJn : J.Normal) (hfaith : ∀ j ∈ J, ρ₀ j = 1 → j = 1)
    (hF : ∀ N : Subgroup Γ, N ≤ J → N.Normal → IsPGroup 3 ↥N → N ≤ ρC.ker)
    {t : Γ} (htJ : t ∈ J) (ht2 : t ^ 2 = 1) (htv : ∃ w : W₀, IsTransvectionWith (ρ₀ t) w) :
    ρC t = 1 := by
  classical
  by_cases ht1 : t = 1
  · rw [ht1, map_one]
  obtain ⟨w, hw⟩ := htv
  have ht₀ne : ρ₀ t ≠ 1 := fun h => ht1 (hfaith t htJ h)
  have hsolv₀ : Group.IsSolvable ↥ρ₀.range := Group.isSolvable_of_surjective ρ₀.rangeRestrict_surjective
  obtain ⟨𝓗, hb⟩ := exists_blocks hW₀ hsolv₀ hO₀
  set Y₀ : Subgroup (MulAut W₀) := Subgroup.closure (transvectionsIn ρ₀.range) with hY₀
  have hTrans : ∀ g : Γ, ρ₀ (g * t * g⁻¹) ∈ transvectionsIn Y₀ := by
    intro g
    have h1 : IsTransvection (ρ₀ (g * t * g⁻¹)) := by
      rw [map_mul, map_mul, map_inv]
      exact B1.isTransvection_conj ⟨ht₀ne, w, hw⟩ (ρ₀ g)
    exact ⟨Subgroup.subset_closure ⟨⟨_, rfl⟩, h1⟩, h1⟩
  have hts : ρ₀ t * ρ₀ t = 1 := B1.tv_sq hW₀ hw ht₀ne
  have hconj_sq : ∀ g : Γ, ρ₀ (g * t * g⁻¹) * ρ₀ (g * t * g⁻¹) = 1 := by
    intro g
    obtain ⟨hne, w', hw'⟩ := (hTrans g).2
    exact B1.tv_sq hW₀ hw' hne
  have hconj_ne : ∀ g : Γ, ρ₀ (g * t * g⁻¹) ≠ 1 := fun g => (hTrans g).2.1
  have hcore : ∀ g : Γ, ρC t * ρC (g * t * g⁻¹) = ρC (g * t * g⁻¹) * ρC t := by
    intro g
    set t' : Γ := g * t * g⁻¹ with ht'
    have ht'J : t' ∈ J := hJn.conj_mem t htJ g
    have hT0 : ρ₀ t ∈ transvectionsIn Y₀ := by
      have := hTrans 1
      simpa using this
    obtain ⟨K₁, hK₁, hsK₁⟩ := hb.cover _ hT0
    obtain ⟨K₂, hK₂, hsK₂⟩ := hb.cover _ (hTrans g)
    by_cases hK : K₁ = K₂
    · subst hK
      have hcube : (ρ₀ t * ρ₀ t') ^ 3 = 1 :=
        cube_of_involutions hb hK₁ hsK₁ hsK₂ ht₀ne (hconj_ne g) hts (hconj_sq g)
      set a : Γ := t * t' with ha
      have haJ : a ∈ J := J.mul_mem htJ ht'J
      have ha3 : a ^ 3 = 1 := by
        refine hfaith _ (J.pow_mem haJ 3) ?_
        rw [map_pow, ha, map_mul]
        exact hcube
      have hcube_conj : ∀ h : Γ, ρ₀ (h * a * h⁻¹) ^ 3 = 1 := by
        intro h
        rw [← map_pow, conj_pow, ha3]
        simp
      have hblock : ∀ h : Γ, ∃ K ∈ 𝓗, ρ₀ (h * a * h⁻¹) ∈ K := by
        intro h
        have e : h * a * h⁻¹ = (h * t * h⁻¹) * ((h * g) * t * (h * g)⁻¹) := by
          simp only [ha, ht', mul_inv_rev]; group
        have hc3 : (ρ₀ (h * t * h⁻¹) * ρ₀ ((h * g) * t * (h * g)⁻¹)) ^ 3 = 1 := by
          rw [← map_mul, ← e]
          exact hcube_conj h
        obtain ⟨K, hK, hmem⟩ := block_of_prod hb hW₀ (hTrans h) (hTrans (h * g)) hc3
        exact ⟨K, hK, by rw [e, map_mul]; exact hmem⟩
      have hgen_comm : ∀ h k : Γ,
          (h * a * h⁻¹) * (k * a * k⁻¹) = (k * a * k⁻¹) * (h * a * h⁻¹) := by
        intro h k
        obtain ⟨Kh, hKh, hmh⟩ := hblock h
        obtain ⟨Kk, hKk, hmk⟩ := hblock k
        have hc : ρ₀ (h * a * h⁻¹) * ρ₀ (k * a * k⁻¹) = ρ₀ (k * a * k⁻¹) * ρ₀ (h * a * h⁻¹) :=
          commute_of_cube hb hKh hKk hmh hmk (hcube_conj h) (hcube_conj k)
        have hJh : h * a * h⁻¹ ∈ J := hJn.conj_mem a haJ h
        have hJk : k * a * k⁻¹ ∈ J := hJn.conj_mem a haJ k
        have h5 : (h * a * h⁻¹) * (k * a * k⁻¹) * ((k * a * k⁻¹) * (h * a * h⁻¹))⁻¹ = 1 := by
          refine hfaith _ (J.mul_mem (J.mul_mem hJh hJk) (J.inv_mem (J.mul_mem hJk hJh))) ?_
          have h6 : ρ₀ ((h * a * h⁻¹) * (k * a * k⁻¹) * ((k * a * k⁻¹) * (h * a * h⁻¹))⁻¹) =
              ρ₀ (h * a * h⁻¹) * ρ₀ (k * a * k⁻¹) *
                (ρ₀ (k * a * k⁻¹) * ρ₀ (h * a * h⁻¹))⁻¹ := by
            simp only [map_mul, map_inv]
          rw [h6, hc, mul_inv_cancel]
        exact mul_inv_eq_one.mp h5
      have hS : ∀ x ∈ Group.conjugatesOfSet ({a} : Set Γ), ∀ y ∈ Group.conjugatesOfSet ({a} : Set Γ),
          x * y = y * x := by
        intro x hx y hy
        obtain ⟨_, hx', hxc⟩ := Group.mem_conjugatesOfSet_iff.mp hx
        obtain ⟨_, hy', hyc⟩ := Group.mem_conjugatesOfSet_iff.mp hy
        rw [Set.mem_singleton_iff] at hx' hy'
        subst hx'
        subst hy'
        obtain ⟨h, rfl⟩ := isConj_iff.mp hxc
        obtain ⟨k, rfl⟩ := isConj_iff.mp hyc
        exact hgen_comm h k
      have hcube : ∀ x ∈ Group.conjugatesOfSet ({a} : Set Γ), x ^ 3 = 1 := by
        intro x hx
        obtain ⟨_, hx', hxc⟩ := Group.mem_conjugatesOfSet_iff.mp hx
        rw [Set.mem_singleton_iff] at hx'
        subst hx'
        obtain ⟨h, rfl⟩ := isConj_iff.mp hxc
        rw [conj_pow, ha3]
        simp
      have hN3 : IsPGroup 3 ↥(Subgroup.normalClosure ({a} : Set Γ)) :=
        isPGroup_closure_of_pairwise_commute hS hcube
      have hNJ : Subgroup.normalClosure ({a} : Set Γ) ≤ J :=
        Subgroup.normalClosure_le_normal (by simpa using haJ)
      have hNker := hF _ hNJ inferInstance hN3
      have haN : a ∈ Subgroup.normalClosure ({a} : Set Γ) := Subgroup.subset_normalClosure rfl
      have h1 : ρC a = 1 := hNker haN
      rw [ha, map_mul] at h1
      exact h1.trans (mul_eq_one_comm.mp h1).symm
    · have hc : ρ₀ t * ρ₀ t' = ρ₀ t' * ρ₀ t := hb.comm K₁ hK₁ K₂ hK₂ hK _ hsK₁ _ hsK₂
      have h5 : t * t' * (t' * t)⁻¹ = 1 := by
        refine hfaith _ (J.mul_mem (J.mul_mem htJ ht'J) (J.inv_mem (J.mul_mem ht'J htJ))) ?_
        have h6 : ρ₀ (t * t' * (t' * t)⁻¹) = ρ₀ t * ρ₀ t' * (ρ₀ t' * ρ₀ t)⁻¹ := by
          simp only [map_mul, map_inv]
        rw [h6, hc, mul_inv_cancel]
      rw [← map_mul, ← map_mul, mul_inv_eq_one.mp h5]
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let x : ↥ρC.range := ⟨ρC t, t, rfl⟩
  have hx1 : x ≠ 1 := fun h => hne (congrArg Subtype.val h)
  have hx2 : x ^ 2 = 1 := by
    apply Subtype.ext
    show ρC t ^ 2 = 1
    rw [← map_pow, ht2, map_one]
  have hmem : x ∈ CFSG.pCore 2 ↥ρC.range := by
    rw [CFSG.BaerSuzuki.baer_suzuki_iff]
    intro y
    obtain ⟨g, hg⟩ := y.2
    have hv : ((y * x * y⁻¹ : ↥ρC.range) : MulAut WC) = ρC (g * t * g⁻¹) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      simp only [map_mul, map_inv, hg]
      rfl
    have hxy : x * (y * x * y⁻¹) = (y * x * y⁻¹) * x := by
      apply Subtype.ext
      show (x : MulAut WC) * ((y * x * y⁻¹ : ↥ρC.range) : MulAut WC) =
        ((y * x * y⁻¹ : ↥ρC.range) : MulAut WC) * (x : MulAut WC)
      rw [hv]
      exact hcore g
    have hy2 : (y * x * y⁻¹) ^ 2 = 1 := by rw [conj_pow, hx2]; simp
    refine isPGroup_closure_of_pairwise_commute ?_ ?_
    · intro a ha b hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · rfl
      · rw [Set.mem_singleton_iff] at hb
        rw [hb]; exact hxy
      · rw [Set.mem_singleton_iff] at ha
        rw [ha]; exact hxy.symm
      · rw [Set.mem_singleton_iff] at ha hb
        rw [ha, hb]
    · intro a ha
      rcases ha with rfl | ha
      · exact hx2
      · rw [Set.mem_singleton_iff] at ha
        rw [ha]; exact hy2
  rw [hOC] at hmem
  exact hx1 (Subgroup.mem_bot.mp hmem)

end Claim

end Gap6

end CFSG.Quasithin
