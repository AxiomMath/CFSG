module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBTrans

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {T : Type} [CommGroup T] [Finite T]

private theorem s16n9b_rk_add_one_le_of_lt {V : Type*} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {H K : Subgroup V} (h : H < K) : rk ↥H + 1 ≤ rk ↥K := by
  have hle : rk ↥H ≤ rk ↥K := rk_mono h.le
  have hne : rk ↥H ≠ rk ↥K := by
    intro heq
    exact h.ne (eq_of_le_of_rk_le hV h.le (le_of_eq heq.symm))
  omega

private theorem s16n9b_fix_mul_of_fix_mul {A B : Subgroup T} (hd : Disjoint A B) {φ : MulAut T}
    (hA : A.map φ.toMonoidHom = A) (hB : B.map φ.toMonoidHom = B) {y z : T}
    (hy : y ∈ A) (hz : z ∈ B) (hfix : φ (y * z) = y * z) : φ y = y ∧ φ z = z := by
  have hyφ : φ y ∈ A := by
    have h : φ y ∈ A.map φ.toMonoidHom := Subgroup.mem_map.2 ⟨y, hy, rfl⟩
    rwa [hA] at h
  have hzφ : φ z ∈ B := by
    have h : φ z ∈ B.map φ.toMonoidHom := Subgroup.mem_map.2 ⟨z, hz, rfl⟩
    rwa [hB] at h
  rw [map_mul] at hfix
  have hkey : (φ y)⁻¹ * y = φ z * z⁻¹ := by
    rw [eq_inv_mul_of_mul_eq hfix]
    group
  have hmemB : (φ y)⁻¹ * y ∈ B := by
    rw [hkey]
    exact B.mul_mem hzφ (B.inv_mem hz)
  have hmem : (φ y)⁻¹ * y ∈ A ⊓ B := ⟨A.mul_mem (A.inv_mem hyφ) hy, hmemB⟩
  rw [hd.eq_bot, Subgroup.mem_bot] at hmem
  have hy' : φ y = y := inv_mul_eq_one.1 hmem
  refine ⟨hy', ?_⟩
  have hz' : φ z * z⁻¹ = 1 := by
    rw [← hkey, hy']
    exact inv_mul_cancel y
  exact mul_inv_eq_one.1 hz'

private theorem s16n9b_fixV_inf_sup_le {A B : Subgroup T} (hd : Disjoint A B) {φ : MulAut T}
    (hA : A.map φ.toMonoidHom = A) (hB : B.map φ.toMonoidHom = B) :
    fixV (Subgroup.zpowers φ) ⊓ (A ⊔ B) ≤
      (fixV (Subgroup.zpowers φ) ⊓ A) ⊔ (fixV (Subgroup.zpowers φ) ⊓ B) := by
  intro w hw
  obtain ⟨hwC, hwAB⟩ := hw
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hwAB
  obtain ⟨hyfix, hzfix⟩ :=
    s16n9b_fix_mul_of_fix_mul hd hA hB hy hz (mem_fixV_zpowers_iff_apply.mp hwC)
  exact Subgroup.mul_mem_sup ⟨mem_fixV_zpowers_iff_apply.mpr hyfix, hy⟩
    ⟨mem_fixV_zpowers_iff_apply.mpr hzfix, hz⟩

private theorem s16n9b_mem_biSup_of_mem {ι : Type*} {Y : ι → Subgroup T} {S : Set ι} {j : ι}
    (hj : j ∈ S) {x : T} (hx : x ∈ Y j) : x ∈ ⨆ j ∈ S, Y j :=
  (le_iSup₂ (f := fun j (_ : j ∈ S) => Y j) j hj) hx

private theorem s16n9b_mul_mem_biSup {ι : Type*} {Y : ι → Subgroup T} {S : Set ι} {i j k : ι}
    (hi : i ∈ S) (hj : j ∈ S) (hk : k ∈ S) {x y z : T} (hx : x ∈ Y i) (hy : y ∈ Y j)
    (hz : z ∈ Y k) : x * y * z ∈ ⨆ j ∈ S, Y j :=
  Subgroup.mul_mem _
    (Subgroup.mul_mem _ (s16n9b_mem_biSup_of_mem hi hx) (s16n9b_mem_biSup_of_mem hj hy))
    (s16n9b_mem_biSup_of_mem hk hz)

private theorem s16n9b_eq_one_of_mem_biSup {ι : Type*} {Y : ι → Subgroup T} (hind : iSupIndep Y)
    {i : ι} {S : Set ι} (hi : i ∉ S) {x : T} (hxi : x ∈ Y i) (hxS : x ∈ ⨆ j ∈ S, Y j) :
    x = 1 := by
  have hmem : x ∈ Y i ⊓ (⨆ j ∈ S, Y j) := ⟨hxi, hxS⟩
  rw [(hind.disjoint_biSup (x := i) (y := S) hi).eq_bot, Subgroup.mem_bot] at hmem
  exact hmem

theorem s16n9b_case4_rank_supp {φ : MulAut T} {W Q : Subgroup T}
    (hW : W.map φ.toMonoidHom ≤ W) (hQ : Q ≤ fixV (Subgroup.zpowers φ)) (hWQ : W ⊔ Q = ⊤)
    (U : Subgroup T) : s16n9bCommOn U φ ≤ W := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨u, hu, rfl⟩
  have hu' : u ∈ W ⊔ Q := by rw [hWQ]; exact Subgroup.mem_top u
  obtain ⟨w, hw, q, hq, hwq⟩ := Subgroup.mem_sup.1 hu'
  have hφq : φ q = q := mem_fixV_zpowers_iff_apply.mp (hQ hq)
  have hφw : φ w ∈ W := hW (Subgroup.mem_map.2 ⟨w, hw, rfl⟩)
  have heq : φ u * u⁻¹ = φ w * w⁻¹ := by
    rw [← hwq, map_mul, hφq, mul_inv_rev]
    group
  rw [heq]
  exact W.mul_mem hφw (W.inv_mem hw)

theorem s16n9b_case4_rank_count (hT : ∀ t : T, t ^ 2 = 1) {φ : MulAut T} {W : Subgroup T}
    (hW : W.map φ.toMonoidHom ≤ W) {U : Subgroup T}
    (h : rkIdx U + rk ↥(fixV (Subgroup.zpowers φ) ⊓ W) < rk ↥W) :
    ∃ z ∈ s16n9bCommOn U φ, z ≠ 1 ∧ z ∈ W := by
  by_contra hcon
  push Not at hcon
  have h1 : U ⊓ W ≤ fixV (Subgroup.zpowers φ) := by
    intro u hu
    obtain ⟨huU, huW⟩ := hu
    have hzW : φ u * u⁻¹ ∈ W :=
      W.mul_mem (hW (Subgroup.mem_map.2 ⟨u, huW, rfl⟩)) (W.inv_mem huW)
    have hzS : φ u * u⁻¹ ∈ s16n9bCommOn U φ :=
      Subgroup.subset_closure ⟨u, huU, rfl⟩
    have hz1 : φ u * u⁻¹ = 1 := by
      by_contra hne
      exact (hcon _ hzS hne) hzW
    exact mem_fixV_zpowers_iff_apply.mpr (mul_inv_eq_one.1 hz1)
  have hle : rk ↥(U ⊓ W) ≤ rk ↥(fixV (Subgroup.zpowers φ) ⊓ W) :=
    rk_mono (le_inf h1 inf_le_right)
  have hsup := rk_sup_add_rk_inf U W
  have htop : rk ↥(U ⊔ W) ≤ rk T := by
    have h' := rk_mono (le_top : U ⊔ W ≤ ⊤)
    rwa [rk_top] at h'
  have hadd := rk_add_rkIdx U
  omega

theorem s16n9b_case4_rank_swap (hT : ∀ t : T, t ^ 2 = 1) {Ya Yb : Subgroup T}
    (hd : Disjoint Ya Yb) {d k : ℕ} (hrka : rk ↥Ya = d) (hrkb : rk ↥Yb = d) (hk : k < d)
    {φ : MulAut T} (hφa : Ya.map φ.toMonoidHom = Yb) (hφb : Yb.map φ.toMonoidHom = Ya)
    {U : Subgroup T} (hU : rkIdx U ≤ k) :
    ∃ z ∈ s16n9bCommOn U φ, z ≠ 1 ∧ z ∈ Ya ⊔ Yb := by
  have hW : (Ya ⊔ Yb).map φ.toMonoidHom ≤ Ya ⊔ Yb := by
    rw [Subgroup.map_sup Ya Yb φ.toMonoidHom, hφa, hφb]
    exact le_of_eq (sup_comm Yb Ya)
  have hYbC : fixV (Subgroup.zpowers φ) ⊓ Yb = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    obtain ⟨hyC, hyB⟩ := hy
    have hyfix : φ y = y := mem_fixV_zpowers_iff_apply.mp hyC
    have hyA : y ∈ Ya := by
      have h : φ y ∈ Yb.map φ.toMonoidHom := Subgroup.mem_map.2 ⟨y, hyB, rfl⟩
      rw [hφb] at h
      rwa [hyfix] at h
    have hyAB : y ∈ Ya ⊓ Yb := ⟨hyA, hyB⟩
    rw [hd.eq_bot, Subgroup.mem_bot] at hyAB
    exact hyAB
  have hinf : (fixV (Subgroup.zpowers φ) ⊓ (Ya ⊔ Yb)) ⊓ Yb = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨⟨hxC, -⟩, hxB⟩ := hx
    have hxCB : x ∈ fixV (Subgroup.zpowers φ) ⊓ Yb := ⟨hxC, hxB⟩
    rw [hYbC, Subgroup.mem_bot] at hxCB
    exact hxCB
  have hrkW : rk ↥(Ya ⊔ Yb) = 2 * d := by
    have h := rk_sup_add_rk_inf Ya Yb
    rw [hd.eq_bot, rk_bot] at h
    omega
  have hCrank : rk ↥(fixV (Subgroup.zpowers φ) ⊓ (Ya ⊔ Yb)) ≤ d := by
    have h1 := rk_sup_add_rk_inf (fixV (Subgroup.zpowers φ) ⊓ (Ya ⊔ Yb)) Yb
    rw [hinf, rk_bot] at h1
    have h2 : rk ↥((fixV (Subgroup.zpowers φ) ⊓ (Ya ⊔ Yb)) ⊔ Yb) ≤ rk ↥(Ya ⊔ Yb) :=
      rk_mono (sup_le inf_le_right le_sup_right)
    omega
  have h : rkIdx U + rk ↥(fixV (Subgroup.zpowers φ) ⊓ (Ya ⊔ Yb)) < rk ↥(Ya ⊔ Yb) := by
    omega
  exact s16n9b_case4_rank_count hT hW h

theorem s16n9b_case4_rank_id (hT : ∀ t : T, t ^ 2 = 1) {ι : Type} [Fintype ι]
    {Y : ι → Subgroup T} (hind : iSupIndep Y) (hsup : ⨆ i, Y i = ⊤) {k : ℕ} (hk : k ≤ 1)
    {φ : MulAut T} (hφ : ∀ i, (Y i).map φ.toMonoidHom = Y i) {U : Subgroup T}
    (hU : rkIdx U ≤ k) (hUφ : ¬ U ≤ fixV (Subgroup.zpowers φ)) :
    ∃ a b : ι, ∃ z ∈ s16n9bCommOn U φ, z ≠ 1 ∧ z ∈ Y a ⊔ Y b := by
  classical
  set C := fixV (Subgroup.zpowers φ) with hC
  by_cases htwo : ∃ a b : ι, a ≠ b ∧ ¬ Y a ≤ C ∧ ¬ Y b ≤ C
  · obtain ⟨a, b, hab, ha, hb⟩ := htwo
    have hdab : Disjoint (Y a) (Y b) := hind.pairwiseDisjoint hab
    have hW : (Y a ⊔ Y b).map φ.toMonoidHom ≤ Y a ⊔ Y b := by
      rw [Subgroup.map_sup (Y a) (Y b) φ.toMonoidHom, hφ a, hφ b]
    have hrkW : rk ↥(Y a ⊔ Y b) = rk ↥(Y a) + rk ↥(Y b) := by
      have h := rk_sup_add_rk_inf (Y a) (Y b)
      rw [hdab.eq_bot, rk_bot] at h
      omega
    have hle : C ⊓ (Y a ⊔ Y b) ≤ (C ⊓ Y a) ⊔ (C ⊓ Y b) :=
      s16n9b_fixV_inf_sup_le hdab (hφ a) (hφ b)
    have hrkC : rk ↥(C ⊓ (Y a ⊔ Y b)) ≤ rk ↥(C ⊓ Y a) + rk ↥(C ⊓ Y b) := by
      have h1 := rk_mono hle
      have h2 := rk_sup_add_rk_inf (C ⊓ Y a) (C ⊓ Y b)
      omega
    have hlt_a : C ⊓ Y a < Y a :=
      lt_of_le_of_ne inf_le_right (fun h => ha (inf_eq_right.1 h))
    have hlt_b : C ⊓ Y b < Y b :=
      lt_of_le_of_ne inf_le_right (fun h => hb (inf_eq_right.1 h))
    have h1a : rk ↥(C ⊓ Y a) + 1 ≤ rk ↥(Y a) := s16n9b_rk_add_one_le_of_lt hT hlt_a
    have h1b : rk ↥(C ⊓ Y b) + 1 ≤ rk ↥(Y b) := s16n9b_rk_add_one_le_of_lt hT hlt_b
    have h : rkIdx U + rk ↥(C ⊓ (Y a ⊔ Y b)) < rk ↥(Y a ⊔ Y b) := by
      omega
    obtain ⟨z, hzS, hz1, hzW⟩ := s16n9b_case4_rank_count hT hW h
    exact ⟨a, b, z, hzS, hz1, hzW⟩
  · have hpair : ∀ a b : ι, a ≠ b → Y a ≤ C ∨ Y b ≤ C := by
      intro a b hab
      by_contra h
      push Not at h
      exact htwo ⟨a, b, hab, h.1, h.2⟩
    by_cases hone : ∀ i, Y i ≤ C
    · exfalso
      have htop : (⊤ : Subgroup T) ≤ C := by
        rw [← hsup]
        exact iSup_le hone
      exact hUφ fun u _ => htop (Subgroup.mem_top u)
    · push Not at hone
      obtain ⟨a, ha⟩ := hone
      have hQ : (⨆ i : {i : ι // i ≠ a}, Y i.1) ≤ C :=
        iSup_le fun i => (hpair a i.1 (Ne.symm i.2)).resolve_left ha
      have hsplit : (⨆ i, Y i) = Y a ⊔ ⨆ i : {i : ι // i ≠ a}, Y i.1 := by
        apply le_antisymm
        · refine iSup_le fun i => ?_
          by_cases hi : i = a
          · subst hi; exact le_sup_left
          · exact le_sup_of_le_right
              (le_iSup (fun i : {i : ι // i ≠ a} => Y i.1) ⟨i, hi⟩)
        · refine sup_le ?_ ?_
          · exact le_iSup Y a
          · exact iSup_le fun i => le_iSup Y i.1
      have hWQ : Y a ⊔ (⨆ i : {i : ι // i ≠ a}, Y i.1) = ⊤ := by
        rw [← hsplit]; exact hsup
      have hW : (Y a).map φ.toMonoidHom ≤ Y a := le_of_eq (hφ a)
      have hle : s16n9bCommOn U φ ≤ Y a :=
        s16n9b_case4_rank_supp hW hQ hWQ U
      obtain ⟨z, hzS, hz1⟩ := s16n9b_exists_commOn hUφ
      exact ⟨a, a, z, hzS, hz1, Subgroup.mem_sup_left (hle hzS)⟩

theorem s16n9b_case4_rank_moved (hT : ∀ t : T, t ^ 2 = 1) {ι : Type} [Fintype ι]
    {Y : ι → Subgroup T} (hind : iSupIndep Y) (hinj : Function.Injective Y) {d : ℕ}
    (hrk : ∀ i, rk ↥(Y i) = d) {φ : MulAut T}
    (hperm : ∀ i, ∃ j, (Y i).map φ.toMonoidHom = Y j)
    (hC : rkIdx (fixV (Subgroup.zpowers φ)) < 2 * d) :
    (∀ i, (Y i).map φ.toMonoidHom = Y i) ∨
      ∃ a b : ι, a ≠ b ∧ (Y a).map φ.toMonoidHom = Y b ∧ (Y b).map φ.toMonoidHom = Y a ∧
        ∀ i, i ≠ a → i ≠ b → (Y i).map φ.toMonoidHom = Y i := by
  classical
  choose σ hσ using hperm
  have hσinj : Function.Injective σ := by
    intro i j hij
    apply hinj
    exact Subgroup.map_injective φ.injective (by rw [hσ i, hσ j, hij])
  have key : ∀ a a' : ι, a ≠ a' → σ a ≠ a → σ a' ≠ a' → σ a = a' ∧ σ a' = a := by
    intro a a' han ha ha'
    by_contra hnot
    have hσaa' : σ a ≠ σ a' := fun h => han (hσinj h)
    have hinf : fixV (Subgroup.zpowers φ) ⊓ (Y a ⊔ Y a') = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro w hw
      obtain ⟨hwC, hwAB⟩ := hw
      obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hwAB
      have hfix : φ y * φ z = y * z := by
        have h := mem_fixV_zpowers_iff_apply.mp hwC
        rwa [map_mul] at h
      have hyφ : φ y ∈ Y (σ a) := by
        have h : φ y ∈ (Y a).map φ.toMonoidHom := Subgroup.mem_map.2 ⟨y, hy, rfl⟩
        rwa [hσ a] at h
      have hzφ : φ z ∈ Y (σ a') := by
        have h : φ z ∈ (Y a').map φ.toMonoidHom := Subgroup.mem_map.2 ⟨z, hz, rfl⟩
        rwa [hσ a'] at h
      have hyz : y * z = 1 := by
        by_cases h1 : σ a = a'
        ·
          have h2 : σ a' ≠ a := fun h => hnot ⟨h1, h⟩
          have haS : a ∈ ({j : ι | j ≠ σ a'} : Set ι) := Ne.symm h2
          have ha'S : a' ∈ ({j : ι | j ≠ σ a'} : Set ι) := Ne.symm ha'
          have hσaS : σ a ∈ ({j : ι | j ≠ σ a'} : Set ι) := hσaa'
          have hφz_eq : φ z = y * z * (φ y)⁻¹ := by
            rw [eq_inv_mul_of_mul_eq hfix]
            exact mul_comm _ _
          have hφzS : φ z ∈ ⨆ j ∈ ({j : ι | j ≠ σ a'} : Set ι), Y j := by
            rw [hφz_eq]
            exact s16n9b_mul_mem_biSup haS ha'S hσaS hy hz ((Y (σ a)).inv_mem hyφ)
          have hφz1 : φ z = 1 :=
            s16n9b_eq_one_of_mem_biSup hind (i := σ a')
              (S := {j : ι | j ≠ σ a'}) (by simp) hzφ hφzS
          have hz1 : z = 1 := φ.injective (by rw [hφz1, map_one])
          have hφy : φ y = y := by simpa [hz1, hφz1] using hfix
          have hmem : φ y ∈ Y a ⊓ Y (σ a) := ⟨by rw [hφy]; exact hy, hyφ⟩
          have hd' : Disjoint (Y a) (Y (σ a)) := hind.pairwiseDisjoint (Ne.symm ha)
          rw [hd'.eq_bot, Subgroup.mem_bot] at hmem
          have hy1 : y = 1 := φ.injective (by rw [hmem, map_one])
          rw [hy1, hz1, mul_one]
        ·
          have haS : a ∈ ({j : ι | j ≠ σ a} : Set ι) := Ne.symm ha
          have ha'S : a' ∈ ({j : ι | j ≠ σ a} : Set ι) := Ne.symm h1
          have hσa'S : σ a' ∈ ({j : ι | j ≠ σ a} : Set ι) := Ne.symm hσaa'
          have hφy_eq : φ y = y * z * (φ z)⁻¹ := eq_mul_inv_of_mul_eq hfix
          have hφyS : φ y ∈ ⨆ j ∈ ({j : ι | j ≠ σ a} : Set ι), Y j := by
            rw [hφy_eq]
            exact s16n9b_mul_mem_biSup haS ha'S hσa'S hy hz ((Y (σ a')).inv_mem hzφ)
          have hφy1 : φ y = 1 :=
            s16n9b_eq_one_of_mem_biSup hind (i := σ a)
              (S := {j : ι | j ≠ σ a}) (by simp) hyφ hφyS
          have hy1 : y = 1 := φ.injective (by rw [hφy1, map_one])
          have hφz : φ z = z := by simpa [hy1, hφy1] using hfix
          have hmem : φ z ∈ Y a' ⊓ Y (σ a') := ⟨by rw [hφz]; exact hz, hzφ⟩
          have hd' : Disjoint (Y a') (Y (σ a')) :=
            hind.pairwiseDisjoint (Ne.symm ha')
          rw [hd'.eq_bot, Subgroup.mem_bot] at hmem
          have hz1 : z = 1 := φ.injective (by rw [hmem, map_one])
          rw [hy1, hz1, mul_one]
      exact hyz
    have hdab : Disjoint (Y a) (Y a') := hind.pairwiseDisjoint han
    have hrkW : rk ↥(Y a ⊔ Y a') = rk ↥(Y a) + rk ↥(Y a') := by
      have h := rk_sup_add_rk_inf (Y a) (Y a')
      rw [hdab.eq_bot, rk_bot] at h
      omega
    have hsup := rk_sup_add_rk_inf (fixV (Subgroup.zpowers φ)) (Y a ⊔ Y a')
    rw [hinf, rk_bot] at hsup
    have htop : rk ↥(fixV (Subgroup.zpowers φ) ⊔ (Y a ⊔ Y a')) ≤ rk T := by
      have h' := rk_mono (le_top : fixV (Subgroup.zpowers φ) ⊔ (Y a ⊔ Y a') ≤ ⊤)
      rwa [rk_top] at h'
    have hadd := rk_add_rkIdx (fixV (Subgroup.zpowers φ))
    have hra := hrk a
    have hrb := hrk a'
    omega
  by_cases hmoved : ∃ i, σ i ≠ i
  · obtain ⟨a, ha⟩ := hmoved
    have hσa_moved : σ (σ a) ≠ σ a := fun h => ha (hσinj h)
    obtain ⟨-, hσa⟩ := key a (σ a) (Ne.symm ha) ha hσa_moved
    refine Or.inr ⟨a, σ a, Ne.symm ha, hσ a, ?_, ?_⟩
    · rw [hσ (σ a), hσa]
    · intro i hia hib
      have hσi : σ i = i := by
        by_contra hne
        exact hib (key a i (Ne.symm hia) ha hne).1.symm
      rw [hσ i, hσi]
  · refine Or.inl fun i => ?_
    have hσi : σ i = i := by
      by_contra hne
      exact hmoved ⟨i, hne⟩
    rw [hσ i, hσi]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
