module

public import CFSG.Quasithin.Background.HatA6NormPts

public section

namespace CFSG.Quasithin.HatA6

open CFSG.CharacterTheory.SteinbergBY
open CFSG.Quasithin.H13.Orbit

variable {W : Type} [CommGroup W] [Finite W] {K : Subgroup (MulAut W)} {z : ↥K} {f : W}

theorem Setup.exists_mem_image_eq (S : Setup W K z f) {P₁ P₂ P₃ Q₁ Q₂ Q₃ : Set W}
    (hP₁ : P₁ ∈ points (z : MulAut W) (orbitIn K f))
    (hP₂ : P₂ ∈ points (z : MulAut W) (orbitIn K f))
    (hP₃ : P₃ ∈ points (z : MulAut W) (orbitIn K f))
    (hQ₁ : Q₁ ∈ points (z : MulAut W) (orbitIn K f))
    (hQ₂ : Q₂ ∈ points (z : MulAut W) (orbitIn K f))
    (hQ₃ : Q₃ ∈ points (z : MulAut W) (orbitIn K f))
    (hP₁₂ : P₁ ≠ P₂) (hP₁₃ : P₁ ≠ P₃) (hP₂₃ : P₂ ≠ P₃)
    (hQ₁₂ : Q₁ ≠ Q₂) (hQ₁₃ : Q₁ ≠ Q₃) (hQ₂₃ : Q₂ ≠ Q₃) :
    ∃ k ∈ K, ⇑k '' P₁ = Q₁ ∧ ⇑k '' P₂ = Q₂ ∧ ⇑k '' P₃ = Q₃ := by
  classical
  let O : Set W := orbitIn K f
  let zW : MulAut W := (z : MulAut W)
  let α := ↥(points zW O)
  have h3 : zW ^ 3 = 1 := S.pow_three
  let ρ : ↥K →* Equiv.Perm α :=
    (pointPerm h3).comp (Subgroup.inclusion S.le_semiStab)
  have : Fintype α := Fintype.ofFinite α
  have : DecidableEq α := Classical.decEq α
  have hα6 : Nat.card α = 6 := S.card_points
  have hρ_apply (k : ↥K) (P : α) :
      (((ρ k) P : α) : Set W) = ⇑(k : MulAut W) '' (P : Set W) := by
    change ((((pointPerm h3) (Subgroup.inclusion S.le_semiStab k)) P : α) : Set W) =
      ⇑(k : MulAut W) '' (P : Set W)
    rw [coe_pointPerm_apply, Subgroup.coe_inclusion]
  have hρ_pt_val (k : ↥K) {w : W} (hw : w ∈ O) :
      (((ρ k) ⟨pt zW w, ⟨w, hw, rfl⟩⟩ : α) : Set W) = pt zW ((k : MulAut W) w) := by
    obtain ⟨y, _, hy⟩ := ((ρ k) ⟨pt zW w, ⟨w, hw, rfl⟩⟩).2
    have hmem : (k : MulAut W) w ∈
        (((ρ k) ⟨pt zW w, ⟨w, hw, rfl⟩⟩ : α) : Set W) := by
      rw [hρ_apply]
      exact ⟨w, by simp [pt], rfl⟩
    rw [← hy] at hmem
    have hpt : pt zW ((k : MulAut W) w) = pt zW y := (pt_eq_pt_iff h3).mpr hmem
    exact hy.symm.trans hpt.symm
  have hρtrans : ∀ P Q : α, ∃ k : ↥K, (ρ k) P = Q := by
    intro P Q
    have hP2 : (P : Set W) ∈ pt zW '' O := P.2
    have hQ2 : (Q : Set W) ∈ pt zW '' O := Q.2
    obtain ⟨w, hwO, hwP⟩ := (Set.mem_image (pt zW) O (P : Set W)).mp hP2
    obtain ⟨w', hw'O, hw'Q⟩ := (Set.mem_image (pt zW) O (Q : Set W)).mp hQ2
    have hwO' : w ∈ O := hwO
    have hw'O' : w' ∈ O := hw'O
    obtain ⟨k₁, hk₁K, hk₁⟩ := hwO
    obtain ⟨k₂, hk₂K, hk₂⟩ := hw'O
    refine ⟨⟨k₂ * k₁⁻¹, K.mul_mem hk₂K (K.inv_mem hk₁K)⟩, ?_⟩
    have hP : P = ⟨pt zW w, ⟨w, hwO', rfl⟩⟩ := Subtype.ext hwP.symm
    have hQ : Q = ⟨pt zW w', ⟨w', hw'O', rfl⟩⟩ := Subtype.ext hw'Q.symm
    rw [hP, hQ]
    apply Subtype.ext
    have hkw : ((⟨k₂ * k₁⁻¹, K.mul_mem hk₂K (K.inv_mem hk₁K)⟩ : ↥K) : MulAut W) w = w' := by
      change (k₂ * k₁⁻¹ : MulAut W) w = w'
      rw [MulAut.mul_apply, ← hk₁, MulAut.inv_apply_self, hk₂]
    rw [hρ_pt_val (k := ⟨k₂ * k₁⁻¹, K.mul_mem hk₂K (K.inv_mem hk₁K)⟩) hwO', hkw]
  have hρne : ρ ≠ 1 := by
    intro h
    have : Nontrivial α := by
      rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card, hα6]
      norm_num
    obtain ⟨P, Q, hPQ⟩ := exists_pair_ne α
    obtain ⟨k, hk⟩ := hρtrans P Q
    have hfix : (ρ k) P = P := by rw [h]; rfl
    exact hPQ (hfix.symm.trans hk)
  have hρz : ρ z = 1 := by
    have hzsem : (⟨zW, S.le_semiStab z.2⟩ : ↥(semiStab zW O)) ∈ (pointPerm h3).ker := by
      have hmem : (⟨zW, S.le_semiStab z.2⟩ : ↥(semiStab zW O)) ∈
          (Subgroup.zpowers zW).subgroupOf (semiStab zW O) :=
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers zW)
      exact zpowers_le_ker_pointPerm (O := O) h3 hmem
    change (pointPerm h3) (Subgroup.inclusion S.le_semiStab z) = 1
    rw [show Subgroup.inclusion S.le_semiStab z = ⟨zW, S.le_semiStab z.2⟩ from
      Subtype.ext (Subgroup.coe_inclusion S.le_semiStab z)]
    exact hzsem
  have hcenter_le : Subgroup.center ↥K ≤ ρ.ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    have hkz : k ∈ Subgroup.zpowers z := S.center_eq ▸ hk
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hkz
    calc ρ k = ρ (z ^ n) := by rw [← hn]
      _ = (ρ z) ^ n := map_zpow ρ z n
      _ = 1 := by rw [hρz]; simp
  have hker_le_center : ρ.ker ≤ Subgroup.center ↥K := by
    let N : Subgroup ↥K := ρ.ker
    let C : Subgroup ↥K := Subgroup.center ↥K
    let π : ↥K →* ↥K ⧸ C := QuotientGroup.mk' C
    let M : Subgroup (↥K ⧸ C) := N.map π
    have hMN : M.Normal :=
      Subgroup.Normal.map (MonoidHom.normal_ker ρ) π (QuotientGroup.mk'_surjective C)
    have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    let e : ↥K ⧸ C ≃* alternatingGroup (Fin 6) := S.quot.some
    have hMe : (M.map e.toMonoidHom).Normal :=
      Subgroup.Normal.map hMN e.toMonoidHom e.surjective
    have : (M.map e.toMonoidHom).Normal := hMe
    rcases Subgroup.Normal.eq_bot_or_eq_top (M.map e.toMonoidHom) with hbot | htop
    · have hMbot : M = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective (H := M) e.injective).mp hbot
      intro n hn
      have h1 : π n ∈ M := ⟨n, hn, rfl⟩
      rw [hMbot, Subgroup.mem_bot] at h1
      have h2 : n ∈ π.ker := MonoidHom.mem_ker.mpr h1
      simpa [π, C, QuotientGroup.ker_mk'] using h2
    · have hMtop : M = ⊤ := by
        refine Subgroup.map_injective (f := e.toMonoidHom) e.injective ?_
        rw [htop, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
      have hsup : C ⊔ N = ⊤ := by
        have h : Subgroup.comap (QuotientGroup.mk' C) M = C ⊔ N :=
          QuotientGroup.comap_map_mk' C N
        rw [hMtop, Subgroup.comap_top] at h
        exact h.symm
      have hNtop : N = ⊤ := (sup_eq_right.mpr hcenter_le).symm.trans hsup
      exfalso
      exact hρne (MonoidHom.ker_eq_top_iff.mp hNtop)
  have hker : ρ.ker = Subgroup.center ↥K := le_antisymm hker_le_center hcenter_le
  have hKcard : Nat.card ↥K = 1080 := (quasisimple_card S.perf S.card_center S.quot.some).2
  have hrange_card : Nat.card ρ.range = 360 := by
    have h := Subgroup.card_ker_mul_card_range ρ
    rw [hker, S.card_center, hKcard] at h
    omega
  have hperm_card : Nat.card (Equiv.Perm α) = 720 := by
    rw [Nat.card_perm, hα6]
    norm_num
  have hidx : ρ.range.index = 2 := by
    have h := Subgroup.index_mul_card ρ.range
    rw [hperm_card, hrange_card] at h
    omega
  have hrange_eq : ρ.range = alternatingGroup α :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hidx
  have h4alt : MulAction.IsMultiplyPretransitive (alternatingGroup α) α 4 := by
    have h := alternatingGroup.isMultiplyPretransitive (α := α)
    rw [hα6] at h
    simpa using h
  have h3trans : MulAction.IsMultiplyPretransitive ρ.range α 3 := by
    rw [hrange_eq]
    let : MulAction.IsMultiplyPretransitive (alternatingGroup α) α 4 := h4alt
    exact MulAction.isMultiplyPretransitive_of_le (n := 4) (by norm_num) (by omega)
  let x : Fin 3 ↪ α := ⟨![⟨P₁, hP₁⟩, ⟨P₂, hP₂⟩, ⟨P₃, hP₃⟩], by
    intro i j hij
    fin_cases i
    · fin_cases j
      · rfl
      · exact absurd (congrArg Subtype.val hij) hP₁₂
      · exact absurd (congrArg Subtype.val hij) hP₁₃
    · fin_cases j
      · exact absurd (congrArg Subtype.val hij) (Ne.symm hP₁₂)
      · rfl
      · exact absurd (congrArg Subtype.val hij) hP₂₃
    · fin_cases j
      · exact absurd (congrArg Subtype.val hij) (Ne.symm hP₁₃)
      · exact absurd (congrArg Subtype.val hij) (Ne.symm hP₂₃)
      · rfl⟩
  let y : Fin 3 ↪ α := ⟨![⟨Q₁, hQ₁⟩, ⟨Q₂, hQ₂⟩, ⟨Q₃, hQ₃⟩], by
    intro i j hij
    fin_cases i
    · fin_cases j
      · rfl
      · exact absurd (congrArg Subtype.val hij) hQ₁₂
      · exact absurd (congrArg Subtype.val hij) hQ₁₃
    · fin_cases j
      · exact absurd (congrArg Subtype.val hij) (Ne.symm hQ₁₂)
      · rfl
      · exact absurd (congrArg Subtype.val hij) hQ₂₃
    · fin_cases j
      · exact absurd (congrArg Subtype.val hij) (Ne.symm hQ₁₃)
      · exact absurd (congrArg Subtype.val hij) (Ne.symm hQ₂₃)
      · rfl⟩
  obtain ⟨σ, hσ⟩ := (MulAction.isMultiplyPretransitive_iff.mp h3trans) x y
  have hσrange : (σ : Equiv.Perm α) ∈ ρ.range := σ.2
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hσrange
  have key {i : Fin 3} : (ρ k) (x i) = y i := by
    have h0 := congrArg (fun e : Fin 3 ↪ α => (e i : α)) hσ
    rw [hk]
    exact h0
  have himg : ∀ i : Fin 3, ⇑(k : MulAut W) '' (x i : Set W) = y i := by
    intro i
    have hval : ((((pointPerm h3) (Subgroup.inclusion S.le_semiStab k)) (x i) : α) : Set W) =
        (y i : Set W) := by
      simpa only [ρ, MonoidHom.comp_apply] using congrArg Subtype.val (key (i := i))
    rw [coe_pointPerm_apply, Subgroup.coe_inclusion] at hval
    exact hval
  exact ⟨(k : MulAut W), k.2, himg 0, himg 1, himg 2⟩

theorem Setup.not_collinear (S : Setup W K z f) {u v w : W} (hu : u ∈ orbitIn K f)
    (hv : v ∈ orbitIn K f) (hw : w ∈ orbitIn K f)
    (huv : pt (z : MulAut W) u ≠ pt (z : MulAut W) v)
    (huw : pt (z : MulAut W) u ≠ pt (z : MulAut W) w)
    (hvw : pt (z : MulAut W) v ≠ pt (z : MulAut W) w) (a b : FieldFour) :
    u ≠ fsmul (z : MulAut W) a v * fsmul (z : MulAut W) b w := by
  classical
  intro hcol
  let zW : MulAut W := (z : MulAut W)
  let O : Set W := orbitIn K f
  have hzz : ∀ y : W, zW (zW y) = y * zW y := S.zz
  let L : Set W := Set.range (fun p : FieldFour × FieldFour =>
    fsmul zW p.1 v * fsmul zW p.2 w)
  have hLv : ∀ c : FieldFour, fsmul zW c v ∈ L := fun c =>
    ⟨(c, 0), by simp [fsmul_zero]⟩
  have hLw : ∀ c : FieldFour, fsmul zW c w ∈ L := fun c =>
    ⟨(0, c), by simp [fsmul_zero]⟩
  have hLfsmul : ∀ c : FieldFour, ∀ y : W, y ∈ L → fsmul zW c y ∈ L := by
    rintro c _ ⟨⟨c₀, c₁⟩, rfl⟩
    refine ⟨(c * c₀, c * c₁), ?_⟩
    calc fsmul zW (c * c₀) v * fsmul zW (c * c₁) w
        = fsmul zW c (fsmul zW c₀ v) * fsmul zW c (fsmul zW c₁ w) := by
          rw [fsmul_mul S.sq hzz, fsmul_mul S.sq hzz]
      _ = fsmul zW c (fsmul zW c₀ v * fsmul zW c₁ w) :=
          (fsmul_mul_right zW c (fsmul zW c₀ v) (fsmul zW c₁ w)).symm
  have hptv : pt zW v ⊆ L := by
    intro y hy
    obtain ⟨c, -, rfl⟩ := exists_fsmul_of_mem_pt hzz hy
    exact hLv c
  have hptw : pt zW w ⊆ L := by
    intro y hy
    obtain ⟨c, -, rfl⟩ := exists_fsmul_of_mem_pt hzz hy
    exact hLw c
  have hpt_of_mem_L : ∀ y : W, y ∈ L → pt zW y ⊆ L := by
    intro y hy x hx
    obtain ⟨c, -, rfl⟩ := exists_fsmul_of_mem_pt hzz hx
    exact hLfsmul c y hy
  have hOsub : O ⊆ L := by
    intro x hxO
    by_cases hxv : pt zW x = pt zW v
    · exact hptv (hxv ▸ by simp [pt])
    by_cases hxw : pt zW x = pt zW w
    · exact hptw (hxw ▸ by simp [pt])
    obtain ⟨k, hkK, hkv, hkw, hku⟩ :=
      Setup.exists_mem_image_eq S
        ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩ ⟨u, hu, rfl⟩
        ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩ ⟨x, hxO, rfl⟩
        hvw (Ne.symm huv) (Ne.symm huw) hvw (Ne.symm hxv) (Ne.symm hxw)
    have hkcomm : ∀ y : W, k (zW y) = zW (k y) := fun y =>
      congrArg (fun e : MulAut W => e y) (S.commute_z hkK)
    have hkvm : k v ∈ pt zW v := by
      rw [← hkv]
      exact ⟨v, by simp [pt], rfl⟩
    have hkwm : k w ∈ pt zW w := by
      rw [← hkw]
      exact ⟨w, by simp [pt], rfl⟩
    have hkum : k u ∈ pt zW x := by
      rw [← hku]
      exact ⟨u, by simp [pt], rfl⟩
    obtain ⟨c, -, hc⟩ := exists_fsmul_of_mem_pt hzz hkvm
    obtain ⟨c', -, hc'⟩ := exists_fsmul_of_mem_pt hzz hkwm
    have hku_eq : k u = fsmul zW a (k v) * fsmul zW b (k w) := by
      rw [hcol, map_mul, map_fsmul hkcomm, map_fsmul hkcomm]
    have hkuL : k u ∈ L := by
      rw [hku_eq, hc, hc']
      refine ⟨(a * c, b * c'), ?_⟩
      change fsmul zW (a * c) v * fsmul zW (b * c') w =
        fsmul zW a (fsmul zW c v) * fsmul zW b (fsmul zW c' w)
      rw [fsmul_mul S.sq hzz, fsmul_mul S.sq hzz]
    have hptx : pt zW (k u) = pt zW x := (pt_eq_pt_iff S.pow_three).mpr hkum
    have hxpt : x ∈ pt zW (k u) := by
      rw [hptx]
      simp [pt]
    exact hpt_of_mem_L (k u) hkuL hxpt
  have hO_le_L : Nat.card O ≤ Nat.card L := Nat.card_mono (Set.finite_range _) hOsub
  have hL_le : Nat.card L ≤ 16 := by
    have h := Finite.card_range_le (fun p : FieldFour × FieldFour =>
      fsmul zW p.1 v * fsmul zW p.2 w)
    calc Nat.card L ≤ Nat.card (FieldFour × FieldFour) := h
      _ = 16 := by norm_num [Nat.card_prod, FieldFour.natCard_eq, FieldFour.card_eq]
  have hOcard : Nat.card O = 18 := S.card_orbit
  rw [hOcard] at hO_le_L
  omega

end CFSG.Quasithin.HatA6

end
