module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3Blk

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

private lemma s16h_map_conj_mul {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {a b : MulAut W} :
    H.map (MulAut.conj (a * b)).toMonoidHom =
      (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  have hhom : (MulAut.conj (a * b)).toMonoidHom =
      ((MulAut.conj a).toMonoidHom).comp ((MulAut.conj b).toMonoidHom) := by
    rw [map_mul]
    rfl
  rw [Subgroup.map_map, ← hhom]

private lemma s16h_conj_comp_conj_inv {W : Type} [CommGroup W] (x : MulAut W) :
    ((MulAut.conj x⁻¹).toMonoidHom).comp ((MulAut.conj x).toMonoidHom) =
      MonoidHom.id (MulAut W) := by
  have h1 : (MulAut.conj x⁻¹ * MulAut.conj x).toMonoidHom =
      ((MulAut.conj x⁻¹).toMonoidHom).comp ((MulAut.conj x).toMonoidHom) := rfl
  rw [← h1, ← map_mul, inv_mul_cancel, map_one]
  exact MulEquiv.toMonoidHom_refl

private lemma s16h_map_conj_one {W : Type} [CommGroup W] (H : Subgroup (MulAut W)) :
    H.map (MulAut.conj (1 : MulAut W)).toMonoidHom = H := by
  have h1 : MulAut.conj (1 : MulAut W) = (1 : MulAut (MulAut W)) := map_one _
  rw [h1]
  change H.map (MonoidHom.id (MulAut W)) = H
  rw [Subgroup.map_id]

private lemma s16h_stabSub_commSub_of_comm {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {y : MulAut W} (hy : ∀ l ∈ H, y * l = l * y) :
    y ∈ stabSub (commSub (⊤ : Subgroup W) H) := by
  rw [mem_stabSub]
  intro c
  constructor
  · intro hc
    have hy' : ∀ l ∈ H, y⁻¹ * l * (y⁻¹)⁻¹ ∈ H := by
      intro l hl
      have h : y⁻¹ * l * (y⁻¹)⁻¹ = l := by
        rw [inv_inv]
        calc y⁻¹ * l * y = y⁻¹ * (y * l) := by rw [hy l hl]; group
          _ = l := by group
      rw [h]; exact hl
    have := commSub_top_stable151b (X := H) (g := y⁻¹) hy' (y c) hc
    simpa [MulAut.inv_apply_self] using this
  · intro hc
    have hy' : ∀ l ∈ H, y * l * y⁻¹ ∈ H := by
      intro l hl
      have h : y * l * y⁻¹ = l := by rw [hy l hl]; group
      rw [h]; exact hl
    exact commSub_top_stable151b (X := H) (g := y) hy' c hc

private lemma s16h_comm_of_fix_stab {W : Type} [CommGroup W] {U U₂ : Subgroup W}
    (hsup : U ⊔ U₂ = ⊤) {a b : MulAut W} (haU : ∀ u ∈ U, a u ∈ U)
    (haU₂ : ∀ u ∈ U₂, a u = u) (hbU : ∀ u ∈ U, b u = u) (hbU₂ : ∀ u ∈ U₂, b u ∈ U₂) :
    a * b = b * a := by
  ext w
  have hw : w ∈ U ⊔ U₂ := by rw [hsup]; exact Subgroup.mem_top w
  obtain ⟨u, hu, v, hv, rfl⟩ := Subgroup.mem_sup.mp hw
  simp only [MulAut.mul_apply, map_mul]
  rw [hbU u hu, haU₂ v hv, haU₂ _ (hbU₂ v hv), hbU _ (haU u hu)]

private lemma s16h_subgroupOf_sup_normal {W : Type} [CommGroup W] {A J J₂ : Subgroup (MulAut W)}
    (hJ : ∀ b ∈ A, J.map (MulAut.conj b).toMonoidHom ≤ J ⊔ J₂)
    (hJ₂ : ∀ b ∈ A, J₂.map (MulAut.conj b).toMonoidHom ≤ J ⊔ J₂) :
    ((J ⊔ J₂).subgroupOf A).Normal := by
  have hmap : ∀ b ∈ A, (J ⊔ J₂).map (MulAut.conj b).toMonoidHom ≤ J ⊔ J₂ := by
    intro b hbA
    rw [Subgroup.map_sup]
    exact sup_le (hJ b hbA) (hJ₂ b hbA)
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hgA : (g : MulAut W) ∈ A := g.2
  have := hmap (g : MulAut W) hgA
    (Subgroup.mem_map_of_mem (MulAut.conj (g : MulAut W)).toMonoidHom hn)
  simpa using this

theorem s16h_z3_not_isPGroup_of_O2 {W : Type} [CommGroup W] [Finite W]
    {A L L₂ : Subgroup (MulAut W)} {x : MulAut W} (hB : s16h_Z3Blocks A L L₂ x)
    (hO2 : ∀ P : Subgroup (MulAut W), P ≤ A → (P.subgroupOf A).Normal → IsPGroup 2 P → P = ⊥)
    {J : Subgroup (MulAut W)} (hJA : J ≤ A) (hJ1 : J ≠ ⊥)
    (hJU₂ : J ≤ centSub (commSub (⊤ : Subgroup W) L₂))
    (hJL : ∀ y ∈ J, ∀ l ∈ L, y * l = l * y)
    (hJn : ∀ b ∈ A, L.map (MulAut.conj b).toMonoidHom = L → ∀ y ∈ J, b * y * b⁻¹ ∈ J) :
    ¬ IsPGroup 2 J := by
  intro hJp
  let U := commSub (⊤ : Subgroup W) L
  let U₂ := commSub (⊤ : Subgroup W) L₂
  let J₂ := J.map (MulAut.conj x).toMonoidHom
  have hxL : L.map (MulAut.conj x).toMonoidHom = L₂ := hB.eq.symm
  have hxinvL : L₂.map (MulAut.conj x⁻¹).toMonoidHom = L := by
    rw [← hxL, Subgroup.map_map, s16h_conj_comp_conj_inv x, Subgroup.map_id]
  have hfix₂ : ∀ b ∈ A, L.map (MulAut.conj b).toMonoidHom = L →
      L₂.map (MulAut.conj b).toMonoidHom = L₂ := by
    intro b hbA hbL
    rcases hB.perm b hbA with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2
    · exact absurd (h1.symm.trans hbL) hB.ne
  have hswap₂ : ∀ b ∈ A, L.map (MulAut.conj b).toMonoidHom = L₂ →
      L₂.map (MulAut.conj b).toMonoidHom = L := by
    intro b hbA hbL₂
    rcases hB.perm b hbA with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd (h1.symm.trans hbL₂) (Ne.symm hB.ne)
    · exact h2
  have hconjA₀ : ∀ b ∈ A, L.map (MulAut.conj b).toMonoidHom = L →
      L.map (MulAut.conj (x⁻¹ * b * x)).toMonoidHom = L := by
    intro b hbA hbL
    have hbL₂ : L₂.map (MulAut.conj b).toMonoidHom = L₂ := hfix₂ b hbA hbL
    rw [s16h_map_conj_mul (H := L) (a := x⁻¹ * b) (b := x),
      s16h_map_conj_mul (H := L.map (MulAut.conj x).toMonoidHom) (a := x⁻¹) (b := b),
      hxL, hbL₂, hxinvL]
  have hxinv_fix : ∀ g ∈ A, L.map (MulAut.conj g).toMonoidHom = L₂ →
      L.map (MulAut.conj (x⁻¹ * g)).toMonoidHom = L := by
    intro g hgA hgL₂
    rw [s16h_map_conj_mul (H := L) (a := x⁻¹) (b := g), hgL₂, hxinvL]
  have hgx_fix : ∀ g ∈ A, L.map (MulAut.conj g).toMonoidHom = L₂ →
      L.map (MulAut.conj (g * x)).toMonoidHom = L := by
    intro g hgA hgL₂
    rw [s16h_map_conj_mul (H := L) (a := g) (b := x), hxL]
    exact hswap₂ g hgA hgL₂
  have hJ₂_le_A : J₂ ≤ A := by
    have hAconj : A.map (MulAut.conj x).toMonoidHom ≤ A := by
      rintro z ⟨a, ha, rfl⟩
      change x * a * x⁻¹ ∈ A
      exact A.mul_mem (A.mul_mem hB.mem ha) (A.inv_mem hB.mem)
    exact (Subgroup.map_mono hJA).trans hAconj
  have hJU : ∀ y ∈ J, y ∈ stabSub U :=
    fun y hy => s16h_stabSub_commSub_of_comm (H := L) (hJL y hy)
  have hJU₂fix : ∀ y ∈ J, ∀ u ∈ U₂, y u = u :=
    fun y hy u hu => mem_centSub.mp (hJU₂ hy) u hu
  have hJ₂_comm_L₂ : ∀ z ∈ J₂, ∀ l₂ ∈ L₂, z * l₂ = l₂ * z := by
    intro z hz l₂ hl₂
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    have hl₂' : l₂ ∈ L.map (MulAut.conj x).toMonoidHom := by rwa [hxL]
    obtain ⟨l, hl, hl_eq⟩ := Subgroup.mem_map.mp hl₂'
    have hconj : ∀ a : MulAut W, (MulAut.conj x).toMonoidHom a = x * a * x⁻¹ :=
      fun a => MulAut.conj_apply x a
    have hyl : y * l * y⁻¹ = l := by rw [hJL y hy l hl]; group
    have hconj' : ((MulAut.conj x).toMonoidHom y) * ((MulAut.conj x).toMonoidHom l) *
        ((MulAut.conj x).toMonoidHom y)⁻¹ = l₂ := by
      calc ((MulAut.conj x).toMonoidHom y) * ((MulAut.conj x).toMonoidHom l) *
            ((MulAut.conj x).toMonoidHom y)⁻¹
          = x * (y * l * y⁻¹) * x⁻¹ := by rw [hconj y, hconj l]; group
        _ = x * l * x⁻¹ := by rw [hyl]
        _ = l₂ := by rw [← hconj l]; exact hl_eq
    have hconj_eq : ((MulAut.conj x).toMonoidHom y) * l₂ *
        ((MulAut.conj x).toMonoidHom y)⁻¹ = l₂ := by
      simpa only [hl_eq] using hconj'
    calc ((MulAut.conj x).toMonoidHom y) * l₂
        = ((MulAut.conj x).toMonoidHom y) * l₂ * ((MulAut.conj x).toMonoidHom y)⁻¹ *
            ((MulAut.conj x).toMonoidHom y) := by group
      _ = l₂ * ((MulAut.conj x).toMonoidHom y) := by rw [hconj_eq]
  have hJ₂_stabU₂ : J₂ ≤ stabSub U₂ :=
    fun z hz => s16h_stabSub_commSub_of_comm (H := L₂) (hJ₂_comm_L₂ z hz)
  have hJ₂_fixU : ∀ z ∈ J₂, ∀ u ∈ U, z u = u := by
    intro z hz u hu
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    have hconj : ∀ a : MulAut W, (MulAut.conj x).toMonoidHom a = x * a * x⁻¹ :=
      fun a => MulAut.conj_apply x a
    have hxinv : x⁻¹ u ∈ U₂ :=
      (hB.swap' (x⁻¹ u)).mpr (by simpa [MulAut.apply_inv_self] using hu)
    have hfix := mem_centSub.mp (hJU₂ hy) (x⁻¹ u) hxinv
    show ((MulAut.conj x).toMonoidHom y) u = u
    rw [hconj y]
    simp only [MulAut.mul_apply]
    rw [hfix]
    exact MulAut.apply_inv_self W x u
  have hcomm : ∀ y ∈ J, ∀ z ∈ J₂, y * z = z * y := by
    intro y hy z hz
    refine s16h_comm_of_fix_stab (U := U) (U₂ := U₂) hB.sup ?_ ?_ ?_ ?_
    · intro u hu
      exact (mem_stabSub.mp (hJU y hy) u).2 hu
    · intro u hu
      exact hJU₂fix y hy u hu
    · intro u hu
      exact hJ₂_fixU z hz u hu
    · intro u hu
      exact (mem_stabSub.mp (hJ₂_stabU₂ hz) u).2 hu
  have hJnorm : J ≤ Subgroup.normalizer (J₂ : Set (MulAut W)) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply le_antisymm
    · rintro z ⟨w, hw, rfl⟩
      change y * w * y⁻¹ ∈ J₂
      have h : y * w * y⁻¹ = w := by rw [hcomm y hy w hw]; group
      rw [h]
      exact hw
    · intro z hz
      have hh : y * z * y⁻¹ = z := by rw [hcomm y hy z hz]; group
      have hz' : y⁻¹ * z * y ∈ J₂ := by
        have h : y⁻¹ * z * y = z := by
          conv_lhs => rw [← hh]
          group
        rwa [h]
      have hmap : (MulAut.conj y).toMonoidHom (y⁻¹ * z * y) = z := by
        change y * (y⁻¹ * z * y) * y⁻¹ = z
        group
      rw [← hmap]
      exact Subgroup.mem_map_of_mem _ hz'
  have hJ₂p : IsPGroup 2 J₂ := hJp.map (MulAut.conj x).toMonoidHom
  have hNp : IsPGroup 2 ↥(J ⊔ J₂) := IsPGroup.to_sup_of_normal_right' hJp hJ₂p hJnorm
  have hNleA : J ⊔ J₂ ≤ A := sup_le hJA hJ₂_le_A
  have hJconj : ∀ b ∈ A, J.map (MulAut.conj b).toMonoidHom ≤ J ⊔ J₂ := by
    intro b hbA
    by_cases hbL : L.map (MulAut.conj b).toMonoidHom = L
    · refine le_trans ?_ le_sup_left
      intro w hw
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hw
      exact hJn b hbA hbL y hy
    · have hbL₂ : L.map (MulAut.conj b).toMonoidHom = L₂ := by
        rcases hB.perm b hbA with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact absurd h1 hbL
        · exact h1
      refine le_trans ?_ le_sup_right
      intro w hw
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hw
      let a := x⁻¹ * b
      have haA : a ∈ A := A.mul_mem (A.inv_mem hB.mem) hbA
      have haL : L.map (MulAut.conj a).toMonoidHom = L := by
        simpa only [a] using hxinv_fix b hbA hbL₂
      have hay : a * y * a⁻¹ ∈ J := hJn a haA haL y hy
      have hba : b = x * a := by simp only [a]; group
      have heq : (MulAut.conj b).toMonoidHom y =
          (MulAut.conj x).toMonoidHom (a * y * a⁻¹) := by
        change b * y * b⁻¹ = x * (a * y * a⁻¹) * x⁻¹
        rw [hba]; group
      rw [heq]
      exact Subgroup.mem_map_of_mem _ hay
  have hJ₂conj : ∀ b ∈ A, J₂.map (MulAut.conj b).toMonoidHom ≤ J ⊔ J₂ := by
    intro b hbA
    by_cases hbL : L.map (MulAut.conj b).toMonoidHom = L
    · refine le_trans ?_ le_sup_right
      intro w hw
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hw
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
      let c := x⁻¹ * b * x
      have hcA : c ∈ A := A.mul_mem (A.mul_mem (A.inv_mem hB.mem) hbA) hB.mem
      have hcL : L.map (MulAut.conj c).toMonoidHom = L := by
        simpa only [c] using hconjA₀ b hbA hbL
      have hcy : c * y * c⁻¹ ∈ J := hJn c hcA hcL y hy
      have hbc : b = x * c * x⁻¹ := by simp only [c]; group
      have heq : (MulAut.conj b).toMonoidHom ((MulAut.conj x).toMonoidHom y) =
          (MulAut.conj x).toMonoidHom (c * y * c⁻¹) := by
        change b * (x * y * x⁻¹) * b⁻¹ = x * (c * y * c⁻¹) * x⁻¹
        rw [hbc]; group
      rw [heq]
      exact Subgroup.mem_map_of_mem _ hcy
    · have hbL₂ : L.map (MulAut.conj b).toMonoidHom = L₂ := by
        rcases hB.perm b hbA with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact absurd h1 hbL
        · exact h1
      refine le_trans ?_ le_sup_left
      intro w hw
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hw
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
      have hbxA : b * x ∈ A := A.mul_mem hbA hB.mem
      have hbxL : L.map (MulAut.conj (b * x)).toMonoidHom = L := hgx_fix b hbA hbL₂
      have hbxy : (b * x) * y * (b * x)⁻¹ ∈ J := hJn (b * x) hbxA hbxL y hy
      have heq : (MulAut.conj b).toMonoidHom ((MulAut.conj x).toMonoidHom y) =
          (b * x) * y * (b * x)⁻¹ := by
        change b * (x * y * x⁻¹) * b⁻¹ = (b * x) * y * (b * x)⁻¹
        group
      rw [heq]
      exact hbxy
  have hNnormal : ((J ⊔ J₂).subgroupOf A).Normal :=
    s16h_subgroupOf_sup_normal hJconj hJ₂conj
  have hNbot : J ⊔ J₂ = ⊥ := hO2 (J ⊔ J₂) hNleA hNnormal hNp
  have hJbot : J = ⊥ := by
    have hle : J ≤ (⊥ : Subgroup (MulAut W)) := by rw [← hNbot]; exact le_sup_left
    exact le_antisymm hle bot_le
  exact hJ1 hJbot

theorem s16h_z3_exists_J {W : Type} [CommGroup W] [Finite W] {A L L₂ : Subgroup (MulAut W)}
    {x : MulAut W} (hB : s16h_Z3Blocks A L L₂ x)
    (hO2 : ∀ P : Subgroup (MulAut W), P ≤ A → (P.subgroupOf A).Normal → IsPGroup 2 P → P = ⊥)
    {j : MulAut W} (hjA : j ∈ A) (hj2 : j ^ 2 = 1) (hj1 : j ≠ 1)
    (hjU₂ : j ∈ centSub (commSub (⊤ : Subgroup W) L₂)) (hjL : ∀ l ∈ L, j * l = l * j) :
    ∃ J : Subgroup (MulAut W), J ≤ A ∧ J ≤ centSub (commSub (⊤ : Subgroup W) L₂) ∧
      (∀ y ∈ J, ∀ l ∈ L, y * l = l * y) ∧
      (∀ b ∈ A, L.map (MulAut.conj b).toMonoidHom = L → ∀ y ∈ J, b * y * b⁻¹ ∈ J) ∧
      (∃ Y : Set (MulAut W), (∀ g ∈ Y, g ^ 2 = 1) ∧ J = closure Y) ∧ ¬ IsPGroup 2 J := by
  let Y : Set (MulAut W) :=
    {y | ∃ b ∈ A, L.map (MulAut.conj b).toMonoidHom = L ∧ y = b * j * b⁻¹}
  let J : Subgroup (MulAut W) := Subgroup.closure Y
  have hjY : j ∈ Y := ⟨1, A.one_mem, s16h_map_conj_one L, by simp⟩
  have hjJ : j ∈ J := Subgroup.subset_closure hjY
  have hJ1 : J ≠ ⊥ := by
    intro hbot
    have : j ∈ (⊥ : Subgroup (MulAut W)) := hbot ▸ hjJ
    exact hj1 (by simpa using this)
  have hJA : J ≤ A := by
    refine (Subgroup.closure_le A).2 ?_
    rintro y ⟨b, hbA, -, rfl⟩
    exact A.mul_mem (A.mul_mem hbA hjA) (A.inv_mem hbA)
  have hJU₂ : J ≤ centSub (commSub (⊤ : Subgroup W) L₂) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro y ⟨b, hbA, hbL, rfl⟩
    change b * j * b⁻¹ ∈ centSub (commSub (⊤ : Subgroup W) L₂)
    rw [mem_centSub]
    intro u hu
    have hbstab := (hB.stab b hbA hbL).2
    have hbu : b⁻¹ u ∈ commSub (⊤ : Subgroup W) L₂ :=
      (mem_stabSub.mp hbstab (b⁻¹ u)).1 (by simpa [MulAut.apply_inv_self] using hu)
    have hfix := mem_centSub.mp hjU₂ (b⁻¹ u) hbu
    show (b * j * b⁻¹) u = u
    simp only [MulAut.mul_apply]
    rw [hfix]
    exact MulAut.apply_inv_self W b u
  have hJL : ∀ y ∈ J, ∀ l ∈ L, y * l = l * y := by
    intro y hy l hl
    have hYcent : Y ⊆ Subgroup.centralizer ({l} : Set (MulAut W)) := by
      rintro y ⟨b, hbA, hbL, rfl⟩
      refine Subgroup.mem_centralizer_iff.2 ?_
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      have hl' : l ∈ L.map (MulAut.conj b).toMonoidHom := by rwa [hbL]
      obtain ⟨c, hc, hceq⟩ := Subgroup.mem_map.mp hl'
      have hcl : b⁻¹ * l * b = c := by
        have h1 : (MulAut.conj b) (b⁻¹ * l * b) = l := by
          change b * (b⁻¹ * l * b) * b⁻¹ = l
          group
        have h2 : (MulAut.conj b) c = l := hceq
        exact (MulAut.conj b).injective (h1.trans h2.symm)
      have hbc : b⁻¹ * l * b ∈ L := hcl ▸ hc
      calc l * (b * j * b⁻¹) = b * ((b⁻¹ * l * b) * j) * b⁻¹ := by group
        _ = b * (j * (b⁻¹ * l * b)) * b⁻¹ := by rw [hjL (b⁻¹ * l * b) hbc]
        _ = (b * j * b⁻¹) * l := by group
    have hyc : y ∈ Subgroup.centralizer ({l} : Set (MulAut W)) :=
      (Subgroup.closure_le (Subgroup.centralizer ({l} : Set (MulAut W)))).2 hYcent hy
    exact (Subgroup.mem_centralizer_iff.mp hyc l (by simp)).symm
  have hJn : ∀ b ∈ A, L.map (MulAut.conj b).toMonoidHom = L → ∀ y ∈ J, b * y * b⁻¹ ∈ J := by
    intro b hbA hbL y hy
    have hYmap : ∀ z ∈ Y, b * z * b⁻¹ ∈ Y := by
      rintro z ⟨c, hcA, hcL, rfl⟩
      refine ⟨b * c, A.mul_mem hbA hcA, ?_, ?_⟩
      · rw [s16h_map_conj_mul (H := L) (a := b) (b := c), hcL, hbL]
      · change b * (c * j * c⁻¹) * b⁻¹ = (b * c) * j * (b * c)⁻¹
        group
    have hle : J.map (MulAut.conj b).toMonoidHom ≤ J := by
      change (Subgroup.closure Y).map (MulAut.conj b).toMonoidHom ≤ Subgroup.closure Y
      rw [MonoidHom.map_closure]
      refine (Subgroup.closure_le _).2 ?_
      rintro w ⟨z, hz, rfl⟩
      exact Subgroup.subset_closure (hYmap z hz)
    have hthis := hle (Subgroup.mem_map_of_mem (MulAut.conj b).toMonoidHom hy)
    exact hthis
  have hgen2 : ∀ g ∈ Y, g ^ 2 = 1 := by
    rintro y ⟨b, hbA, hbL, rfl⟩
    calc (b * j * b⁻¹) ^ 2 = b * j ^ 2 * b⁻¹ := by rw [pow_two, pow_two]; group
      _ = 1 := by rw [hj2]; group
  exact ⟨J, hJA, hJU₂, hJL, hJn, ⟨Y, hgen2, rfl⟩,
    s16h_z3_not_isPGroup_of_O2 hB hO2 hJA hJ1 hJU₂ hJL hJn⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
