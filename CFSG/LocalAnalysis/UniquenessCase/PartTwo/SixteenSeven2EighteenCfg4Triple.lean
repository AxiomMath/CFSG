module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg4Frame
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W]

private def bigCent (A : Set (Subgroup W)) : Subgroup (MulAut W) :=
  sInf (centSub '' A)

private theorem mem_bigCent {A : Set (Subgroup W)} {x : MulAut W} :
    x ∈ bigCent A ↔ ∀ Y ∈ A, x ∈ centSub Y := by
  rw [bigCent, Subgroup.mem_sInf]
  constructor
  · intro h Y hY
    exact h (centSub Y) (Set.mem_image_of_mem centSub hY)
  · rintro h p ⟨Y, hY, rfl⟩
    exact h Y hY

private theorem mem_centSub_map_conj_iff (g : MulAut W) (Y : Subgroup W) (x : MulAut W) :
    x ∈ centSub (Y.map g.toMonoidHom) ↔ (MulAut.conj g).symm x ∈ centSub Y := by
  rw [← s16c167_cfg4_centSub_conj g Y, Subgroup.mem_map_equiv]

private theorem bigCent_conj (g : MulAut W) (A : Set (Subgroup W)) :
    (bigCent A).map (MulAut.conj g).toMonoidHom
      = bigCent (A.image fun Y => Y.map g.toMonoidHom) := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [mem_bigCent] at hy
    rw [mem_bigCent]
    intro Z hZ
    obtain ⟨Y, hY, rfl⟩ := hZ
    rw [← hyx, mem_centSub_map_conj_iff]
    have hgy : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    simpa [hgy] using hy Y hY
  · intro hx
    rw [mem_bigCent] at hx
    rw [Subgroup.mem_map]
    refine ⟨(MulAut.conj g).symm x, ?_, MulEquiv.apply_symm_apply (MulAut.conj g) x⟩
    rw [mem_bigCent]
    intro Y hY
    have h := hx (Y.map g.toMonoidHom) ⟨Y, hY, rfl⟩
    rwa [mem_centSub_map_conj_iff] at h

theorem s16c167_cfg4_faithful {X L : Subgroup (MulAut W)} {Z : Subgroup W}
    (F : Cfg4Setting X L Z) {x : MulAut W} (hx : ∀ Y ∈ conjSubs X Z, x ∈ centSub Y) : x = 1 := by
  have hle : sSup (conjSubs X Z) ≤ fixV (Subgroup.zpowers x) := by
    refine sSup_le fun Y hY => ?_
    intro y hy
    rw [mem_fixV_zpowers_iff_apply]
    exact (mem_centSub.mp (hx Y hY)) y hy
  rw [F.sup_eq] at hle
  ext w
  have hw : w ∈ fixV (Subgroup.zpowers x) := hle trivial
  simpa using (mem_fixV_zpowers_iff_apply.mp hw)

private theorem map_conj_inv_cancel (g : MulAut W) (Y : Subgroup W) :
    (Y.map (g⁻¹).toMonoidHom).map g.toMonoidHom = Y := by
  rw [Subgroup.map_map]
  have h : g.toMonoidHom.comp (g⁻¹).toMonoidHom = MonoidHom.id W := by
    ext x
    simp
  rw [h, Subgroup.map_id]

private theorem image_sdiff_singleton {X : Subgroup (MulAut W)} {Z Y : Subgroup W} {g : MulAut W}
    (hg : g ∈ X) :
    ((conjSubs X Z \ {Y}).image fun Y' => Y'.map g.toMonoidHom)
      = conjSubs X Z \ {Y.map g.toMonoidHom} := by
  ext Z'
  constructor
  · rintro ⟨Y', hmem, rfl⟩
    refine ⟨s16c167_cfg4_map_mem hg hmem.1, fun h => hmem.2 ?_⟩
    exact Subgroup.map_injective (f := g.toMonoidHom) g.injective h
  · rintro ⟨hZ', hne⟩
    refine ⟨Z'.map (g⁻¹).toMonoidHom,
      ⟨s16c167_cfg4_map_mem (inv_mem hg) hZ', ?_⟩, map_conj_inv_cancel g Z'⟩
    intro h
    rw [Set.mem_singleton_iff] at h
    apply hne
    simp only [Set.mem_singleton_iff]
    calc Z' = (Z'.map (g⁻¹).toMonoidHom).map g.toMonoidHom :=
          (map_conj_inv_cancel g Z').symm
      _ = Y.map g.toMonoidHom := by rw [h]

private def kern (L X : Subgroup (MulAut W)) (Z : Subgroup W) (Y : Subgroup W) :
    Subgroup (MulAut W) :=
  L ⊓ bigCent (conjSubs X Z \ {Y})

private theorem map_kern {X L : Subgroup (MulAut W)} {Z : Subgroup W} (F : Cfg4Setting X L Z)
    {g : MulAut W} (hg : g ∈ X) (Y : Subgroup W) :
    (kern L X Z Y).map (MulAut.conj g).toMonoidHom = kern L X Z (Y.map g.toMonoidHom) := by
  unfold kern
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, F.norm g hg, bigCent_conj,
    image_sdiff_singleton hg]

private theorem kern_inf_centSub {X L : Subgroup (MulAut W)} {Z : Subgroup W}
    (F : Cfg4Setting X L Z) {Y : Subgroup W} (hY : Y ∈ conjSubs X Z) :
    kern L X Z Y ⊓ centSub Y = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  refine s16c167_cfg4_faithful F fun Y' hY' => ?_
  by_cases h : Y' = Y
  · rw [h]; exact hx.2
  · exact (mem_bigCent.mp hx.1.2) Y' ⟨hY', h⟩

private theorem kern_le_centSub {X L : Subgroup (MulAut W)} {Z : Subgroup W}
    {Y Y' : Subgroup W} (hY' : Y' ∈ conjSubs X Z \ {Y}) :
    kern L X Z Y ≤ centSub Y' := by
  intro x hx
  exact (mem_bigCent.mp hx.2) Y' hY'

theorem s16c167_cfg4_triple {X L : Subgroup (MulAut W)} {Z : Subgroup W} (F : Cfg4Setting X L Z)
    {Y₁ Y₂ Y₃ : Subgroup W} (h₁ : Y₁ ∈ conjSubs X Z) (h₂ : Y₂ ∈ conjSubs X Z)
    (h₃ : Y₃ ∈ conjSubs X Z) (h12 : Y₁ ≠ Y₂) (h13 : Y₁ ≠ Y₃) (h23 : Y₂ ≠ Y₃) :
    L ⊓ centSub Y₁ ⊓ centSub Y₂ ⊓ centSub Y₃ = ⊥ := by
  by_contra hne
  have hsub : ({Y₁, Y₂, Y₃} : Set (Subgroup W)) ⊆ conjSubs X Z := by
    intro Y hY
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hY
    rcases hY with rfl | rfl | rfl
    · exact h₁
    · exact h₂
    · exact h₃
  have hncard3 : ({Y₁, Y₂, Y₃} : Set (Subgroup W)).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨Y₁, Y₂, Y₃, h12, h13, h23, rfl⟩
  have hdiff : (conjSubs X Z \ ({Y₁, Y₂, Y₃} : Set (Subgroup W))).ncard = 1 := by
    rw [Set.ncard_sdiff hsub, F.ncard_eq, hncard3]
  obtain ⟨Y₄, hY₄eq⟩ := Set.ncard_eq_one.mp hdiff
  have hY₄mem : Y₄ ∈ conjSubs X Z := by
    have h : Y₄ ∈ ({Y₄} : Set (Subgroup W)) := by simp
    rw [← hY₄eq] at h
    exact h.1
  have hY₄not : Y₄ ∉ ({Y₁, Y₂, Y₃} : Set (Subgroup W)) := by
    have h : Y₄ ∈ ({Y₄} : Set (Subgroup W)) := by simp
    rw [← hY₄eq] at h
    exact h.2
  have hY₄ne₁ : Y₄ ≠ Y₁ := fun h => hY₄not (by simp [h])
  have hY₄ne₂ : Y₄ ≠ Y₂ := fun h => hY₄not (by simp [h])
  have hY₄ne₃ : Y₄ ≠ Y₃ := fun h => hY₄not (by simp [h])
  have hunion : conjSubs X Z = ({Y₁, Y₂, Y₃} : Set (Subgroup W)) ∪ {Y₄} := by
    rw [← hY₄eq]
    exact (Set.union_sdiff_cancel hsub).symm
  have hS : conjSubs X Z = ({Y₁, Y₂, Y₃, Y₄} : Set (Subgroup W)) := by
    rw [hunion]
    ext Y
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hsdiff4 : conjSubs X Z \ {Y₄} = ({Y₁, Y₂, Y₃} : Set (Subgroup W)) := by
    rw [hS]
    ext Y
    constructor
    · intro hY
      have h1 : Y ∈ ({Y₁, Y₂, Y₃, Y₄} : Set (Subgroup W)) := hY.1
      have h2 : Y ≠ Y₄ := fun h => hY.2 (by simp [h])
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 ⊢
      tauto
    · intro hY
      refine ⟨?_, ?_⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hY ⊢
        tauto
      · intro hmem
        rw [Set.mem_singleton_iff] at hmem
        exact hY₄not (hmem ▸ hY)
  have hbigC : bigCent (conjSubs X Z \ {Y₄}) = centSub Y₁ ⊓ centSub Y₂ ⊓ centSub Y₃ := by
    rw [hsdiff4]
    ext x
    rw [mem_bigCent, Subgroup.mem_inf, Subgroup.mem_inf]
    constructor
    · intro h
      exact ⟨⟨h Y₁ (by simp), h Y₂ (by simp)⟩, h Y₃ (by simp)⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩ Y hY
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hY
      rcases hY with rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
  have hkern₄ : kern L X Z Y₄ = L ⊓ centSub Y₁ ⊓ centSub Y₂ ⊓ centSub Y₃ := by
    unfold kern
    rw [hbigC]
    ac_rfl
  have hA₄ne : kern L X Z Y₄ ≠ ⊥ := by
    rw [hkern₄]
    exact hne
  obtain ⟨g₁, hg₁X, hg₁⟩ := s16c167_cfg4_transitive hY₄mem h₁
  obtain ⟨g₂, hg₂X, hg₂⟩ := s16c167_cfg4_transitive hY₄mem h₂
  obtain ⟨g₃, hg₃X, hg₃⟩ := s16c167_cfg4_transitive hY₄mem h₃
  have hcard₁ : Nat.card ↥(kern L X Z Y₁) = Nat.card ↥(kern L X Z Y₄) := by
    have h : kern L X Z Y₁ = (kern L X Z Y₄).map (MulAut.conj g₁).toMonoidHom := by
      rw [← hg₁]
      exact (map_kern F hg₁X Y₄).symm
    rw [h]
    exact Subgroup.card_map_of_injective (f := (MulAut.conj g₁).toMonoidHom)
      (MulAut.conj g₁).injective
  have hcard₂ : Nat.card ↥(kern L X Z Y₂) = Nat.card ↥(kern L X Z Y₄) := by
    have h : kern L X Z Y₂ = (kern L X Z Y₄).map (MulAut.conj g₂).toMonoidHom := by
      rw [← hg₂]
      exact (map_kern F hg₂X Y₄).symm
    rw [h]
    exact Subgroup.card_map_of_injective (f := (MulAut.conj g₂).toMonoidHom)
      (MulAut.conj g₂).injective
  have hcard₃ : Nat.card ↥(kern L X Z Y₃) = Nat.card ↥(kern L X Z Y₄) := by
    have h : kern L X Z Y₃ = (kern L X Z Y₄).map (MulAut.conj g₃).toMonoidHom := by
      rw [← hg₃]
      exact (map_kern F hg₃X Y₄).symm
    rw [h]
    exact Subgroup.card_map_of_injective (f := (MulAut.conj g₃).toMonoidHom)
      (MulAut.conj g₃).injective
  have hcardL : Nat.card ↥L = 27 := by
    obtain ⟨e⟩ := F.elem
    rw [Nat.card_congr e.toEquiv,
      (Nat.card_congr (Multiplicative.ofAdd (α := Fin 3 → ZMod 3))).symm,
      Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    norm_num
  have hcommL : ∀ a b : MulAut W, a ∈ L → b ∈ L → a * b = b * a := by
    intro a b ha hb
    obtain ⟨e⟩ := F.elem
    have h : e (⟨a, ha⟩ * ⟨b, hb⟩) = e (⟨b, hb⟩ * ⟨a, ha⟩) := by
      rw [map_mul, map_mul]
      exact mul_comm _ _
    exact Subtype.ext_iff.mp (e.injective h)
  have hnorm : ∀ {A B : Subgroup (MulAut W)}, A ≤ L → B ≤ L →
      B ≤ Subgroup.normalizer (A : Set (MulAut W)) := by
    intro A B hA hB
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer (A : Set (MulAut W)))
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact hcommL a b (hA ha) (hB hb)
  have hle₁₂ : kern L X Z Y₁ ≤ centSub Y₂ := kern_le_centSub (Y := Y₁) ⟨h₂, h12.symm⟩
  have hle₁₃ : kern L X Z Y₁ ≤ centSub Y₃ := kern_le_centSub (Y := Y₁) ⟨h₃, h13.symm⟩
  have hle₁₄ : kern L X Z Y₁ ≤ centSub Y₄ := kern_le_centSub (Y := Y₁) ⟨hY₄mem, hY₄ne₁⟩
  have hle₂₁ : kern L X Z Y₂ ≤ centSub Y₁ := kern_le_centSub (Y := Y₂) ⟨h₁, h12⟩
  have hle₂₃ : kern L X Z Y₂ ≤ centSub Y₃ := kern_le_centSub (Y := Y₂) ⟨h₃, h23.symm⟩
  have hle₂₄ : kern L X Z Y₂ ≤ centSub Y₄ := kern_le_centSub (Y := Y₂) ⟨hY₄mem, hY₄ne₂⟩
  have hle₃₁ : kern L X Z Y₃ ≤ centSub Y₁ := kern_le_centSub (Y := Y₃) ⟨h₁, h13⟩
  have hle₃₂ : kern L X Z Y₃ ≤ centSub Y₂ := kern_le_centSub (Y := Y₃) ⟨h₂, h23⟩
  have hle₃₄ : kern L X Z Y₃ ≤ centSub Y₄ := kern_le_centSub (Y := Y₃) ⟨hY₄mem, hY₄ne₃⟩
  have hd₁₂ : Disjoint (kern L X Z Y₁) (kern L X Z Y₂) := by
    rw [disjoint_iff, eq_bot_iff]
    calc kern L X Z Y₁ ⊓ kern L X Z Y₂ ≤ kern L X Z Y₁ ⊓ centSub Y₁ :=
          inf_le_inf_left _ hle₂₁
      _ = ⊥ := kern_inf_centSub F h₁
  have hd₁₂₃ : Disjoint (kern L X Z Y₁ ⊔ kern L X Z Y₂) (kern L X Z Y₃) := by
    rw [disjoint_iff, eq_bot_iff]
    calc (kern L X Z Y₁ ⊔ kern L X Z Y₂) ⊓ kern L X Z Y₃
        ≤ centSub Y₃ ⊓ kern L X Z Y₃ := inf_le_inf_right _ (sup_le hle₁₃ hle₂₃)
      _ = ⊥ := by rw [inf_comm]; exact kern_inf_centSub F h₃
  have hd₁₂₃₄ : Disjoint (kern L X Z Y₁ ⊔ kern L X Z Y₂ ⊔ kern L X Z Y₃)
      (kern L X Z Y₄) := by
    rw [disjoint_iff, eq_bot_iff]
    calc (kern L X Z Y₁ ⊔ kern L X Z Y₂ ⊔ kern L X Z Y₃) ⊓ kern L X Z Y₄
        ≤ centSub Y₄ ⊓ kern L X Z Y₄ :=
          inf_le_inf_right _ (sup_le (sup_le hle₁₄ hle₂₄) hle₃₄)
      _ = ⊥ := by rw [inf_comm]; exact kern_inf_centSub F hY₄mem
  have hc₁₂ := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (kern L X Z Y₁) (kern L X Z Y₂) (hnorm inf_le_left inf_le_left) hd₁₂
  have hc₁₂₃ := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (kern L X Z Y₁ ⊔ kern L X Z Y₂) (kern L X Z Y₃)
    (hnorm (sup_le inf_le_left inf_le_left) inf_le_left) hd₁₂₃
  have hc₁₂₃₄ := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (kern L X Z Y₁ ⊔ kern L X Z Y₂ ⊔ kern L X Z Y₃) (kern L X Z Y₄)
    (hnorm (sup_le (sup_le inf_le_left inf_le_left) inf_le_left) inf_le_left) hd₁₂₃₄
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Nat.card ↥(kern L X Z Y₄) = m := ⟨_, rfl⟩
  have hcard₁' : Nat.card ↥(kern L X Z Y₁) = m := hcard₁.trans hm
  have hcard₂' : Nat.card ↥(kern L X Z Y₂) = m := hcard₂.trans hm
  have hcard₃' : Nat.card ↥(kern L X Z Y₃) = m := hcard₃.trans hm
  have hjoin : Nat.card ↥(kern L X Z Y₁ ⊔ kern L X Z Y₂ ⊔ kern L X Z Y₃ ⊔ kern L X Z Y₄)
      = m * m * m * m := by
    rw [hc₁₂₃₄, hc₁₂₃, hc₁₂, hcard₁', hcard₂', hcard₃', hm]
  have hleJoin : Nat.card ↥(kern L X Z Y₁ ⊔ kern L X Z Y₂ ⊔ kern L X Z Y₃ ⊔ kern L X Z Y₄)
      ≤ 27 := by
    have hdvd : Nat.card ↥(kern L X Z Y₁ ⊔ kern L X Z Y₂ ⊔ kern L X Z Y₃ ⊔ kern L X Z Y₄) ∣ 27 := by
      have h := Subgroup.card_dvd_of_le (H := kern L X Z Y₁ ⊔ kern L X Z Y₂ ⊔ kern L X Z Y₃ ⊔
        kern L X Z Y₄) (sup_le (sup_le (sup_le inf_le_left inf_le_left) inf_le_left) inf_le_left)
      rwa [hcardL] at h
    exact Nat.le_of_dvd (by norm_num) hdvd
  have hle : m * m * m * m ≤ 27 := hjoin ▸ hleJoin
  have hm3 : 3 ≤ m := by
    have hdvd : Nat.card ↥(kern L X Z Y₄) ∣ 27 := by
      have h := Subgroup.card_dvd_of_le (H := kern L X Z Y₄) inf_le_left
      rwa [hcardL] at h
    have hne1 : Nat.card ↥(kern L X Z Y₄) ≠ 1 := fun h1 =>
      hA₄ne (Subgroup.eq_bot_of_card_eq (H := kern L X Z Y₄) h1)
    have hdvd3 : Nat.card ↥(kern L X Z Y₄) ∣ 3 ^ 3 := by
      rwa [show (3 : ℕ) ^ 3 = 27 by norm_num]
    obtain ⟨k, _, hdk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd3
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hne1 (by simpa using hdk)
    rw [← hm, hdk]
    have hk1 : 1 ≤ k := by omega
    calc (3 : ℕ) = 3 ^ 1 := (pow_one 3).symm
      _ ≤ 3 ^ k := pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 3) hk1
  have h81 : 81 ≤ m * m * m * m := by
    have h : (3 : ℕ) * 3 * 3 * 3 ≤ m * m * m * m :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hm3 hm3) hm3) hm3
    norm_num at h
    exact h
  have : (81 : ℕ) ≤ 27 := le_trans h81 hle
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
