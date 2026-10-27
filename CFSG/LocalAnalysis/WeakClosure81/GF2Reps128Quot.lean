module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsMain
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem iSup_conjSet_eq_biSup_conj (L Y : Subgroup (MulAut W)) :
    (⨆ X ∈ conjSet L Y, X) = ⨆ φ ∈ Y, L.map (MulAut.conj φ).toMonoidHom := by
  apply le_antisymm
  · refine iSup₂_le fun X hX => ?_
    obtain ⟨n, hn, rfl⟩ := hX
    exact le_iSup₂_of_le n hn le_rfl
  · refine iSup₂_le fun φ hφ => ?_
    exact le_iSup₂_of_le (L.map (MulAut.conj φ).toMonoidHom) ⟨φ, hφ, rfl⟩ le_rfl

omit [Finite W] in
theorem conj_mem_biSup_conj {Y L : Subgroup (MulAut W)} {y : MulAut W} (hy : y ∈ Y)
    {h : MulAut W} (hh : h ∈ ⨆ φ ∈ Y, L.map (MulAut.conj φ).toMonoidHom) :
    y * h * y⁻¹ ∈ ⨆ φ ∈ Y, L.map (MulAut.conj φ).toMonoidHom := by
  have hle : (⨆ φ ∈ Y, L.map (MulAut.conj φ).toMonoidHom).map (MulAut.conj y).toMonoidHom ≤
      ⨆ φ ∈ Y, L.map (MulAut.conj φ).toMonoidHom := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun φ => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hφ => ?_
    refine le_iSup₂_of_le (y * φ) (Y.mul_mem hy hφ) ?_
    rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    refine ⟨l, hl, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hmem := hle (Subgroup.mem_map_of_mem (MulAut.conj y).toMonoidHom hh)
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hmem

omit [Finite W] in
theorem h_facts {Y L H : Subgroup (MulAut W)} (hL : IsComponentOf L Y)
    (hH : H = ⨆ X ∈ conjSet L Y, X) :
    H = ⨆ φ ∈ Y, L.map (MulAut.conj φ).toMonoidHom ∧ L ≤ H ∧ H ≤ Y ∧
      (∀ y ∈ Y, ∀ h ∈ H, y * h * y⁻¹ ∈ H) ∧ (H.subgroupOf Y).Normal ∧ H ≠ ⊥ := by
  have h1 : H = ⨆ φ ∈ Y, L.map (MulAut.conj φ).toMonoidHom := by
    rw [hH, iSup_conjSet_eq_biSup_conj]
  have hLH : L ≤ H := le_of_eq_biSup_conj h1
  have hHY : H ≤ Y :=
    biSup_conj_le_of_normal h1 (fun y hy m hm => Y.mul_mem (Y.mul_mem hy hm) (Y.inv_mem hy)) hL.1
  have hn : ∀ y ∈ Y, ∀ h ∈ H, y * h * y⁻¹ ∈ H := by
    intro y hy h hh
    rw [h1] at hh ⊢
    exact conj_mem_biSup_conj hy hh
  have hnorm : (H.subgroupOf Y).Normal := by
    constructor
    intro n hn' g
    rw [Subgroup.mem_subgroupOf] at hn' ⊢
    simpa using hn g g.2 n hn'
  have hLne : L ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot L).mp (CFSG.LocalCores.isQuasisimple_nontrivial
      (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hL.2.2))
  exact ⟨h1, hLH, hHY, hn, hnorm, fun h => hLne (eq_bot_iff.mpr (h ▸ hLH))⟩

theorem commV_eq_top (hW : ∀ w : W, w ^ 2 = 1) {Y L H : Subgroup (MulAut W)}
    (hO : ∀ P : Subgroup (MulAut W), P ≤ Y → (P.subgroupOf Y).Normal → IsPGroup 2 P → P = ⊥)
    (hB : IsBasicModule Y) (hL : IsComponentOf L Y) (hH : H = ⨆ X ∈ conjSet L Y, X) :
    commV H = ⊤ := by
  obtain ⟨h1, -, hHY, -, hnorm, hne⟩ := h_facts hL hH
  have htop : (⨆ I ∈ irrSet H, I) = ⊤ :=
    ((w4Lem12_5_holds W hW Y hO hB H hne hHY hnorm).2 L hL h1).1.1
  rw [eq_top_iff, ← htop]
  refine iSup₂_le fun I hI => ?_
  have hI' : commSub I H = I := hI.1
  rw [← hI', commV_eq_commSub]
  exact commSub_mono le_top le_rfl

omit [Finite W] in
theorem le_stabSub_fixV {Y H : Subgroup (MulAut W)} (hn : ∀ y ∈ Y, ∀ h ∈ H, y * h * y⁻¹ ∈ H) :
    Y ≤ stabSub (fixV H) := by
  intro y hy u
  refine ⟨fun hu => ?_, fun hu => stableUnder_fixV hn y hy u hu⟩
  have h := stableUnder_fixV hn y⁻¹ (Y.inv_mem hy) (y u) hu
  simpa using h

omit [Finite W] in
theorem conj_mem_centQuot {C : Subgroup W} {g k : MulAut W} (hg : ∀ c ∈ C, g c ∈ C)
    (hk : k ∈ centQuot C) : g * k * g⁻¹ ∈ centQuot C := by
  rw [mem_centQuot] at hk ⊢
  intro v
  have h := hg _ (hk (g⁻¹ v))
  have he : g (k (g⁻¹ v) * (g⁻¹ v)⁻¹) = (g * k * g⁻¹) v * v⁻¹ := by
    simp only [map_mul, map_inv, MulAut.mul_apply, MulAut.apply_inv_self]
  rwa [he] at h

theorem eq_one_of_mem_fixV_quot (hW : ∀ w : W, w ^ 2 = 1) {Y L H : Subgroup (MulAut W)}
    (hO : ∀ P : Subgroup (MulAut W), P ≤ Y → (P.subgroupOf Y).Normal → IsPGroup 2 P → P = ⊥)
    (hB : IsBasicModule Y) (hL : IsComponentOf L Y) (hH : H = ⨆ X ∈ conjSet L Y, X)
    {y : MulAut W} (hy : y ∈ Y) (hyq : ∀ w : W, y w * w⁻¹ ∈ fixV H) : y = 1 := by
  obtain ⟨-, -, hHY, hn, -, -⟩ := h_facts hL hH
  set C := fixV H with hC
  have hCY : StableUnder Y C := stableUnder_fixV hn
  have hHC : ∀ h ∈ H, ∀ c ∈ C, h c = c := fun h hh c hc => hc h hh
  set S : Subgroup (MulAut W) := H ⊓ centQuot C with hS
  have hSY : S ≤ Y := inf_le_left.trans hHY
  have hSn : (S.subgroupOf Y).Normal := by
    constructor
    intro s hs g
    rw [Subgroup.mem_subgroupOf] at hs ⊢
    obtain ⟨hsH, hsC⟩ := hs
    exact ⟨hn g g.2 s hsH, conj_mem_centQuot (fun c hc => hCY g g.2 c hc) hsC⟩
  have hS2 : IsPGroup 2 S := by
    intro s
    have hsH : (s : MulAut W) ∈ H := s.2.1
    have hsC : ∀ v, (s : MulAut W) v * v⁻¹ ∈ C := mem_centQuot.mp s.2.2
    have key : (s : MulAut W) * (s : MulAut W) = 1 := by
      refine MulEquiv.ext fun v => ?_
      have hc : (s : MulAut W) v * v⁻¹ ∈ C := hsC v
      have hsv : (s : MulAut W) v = ((s : MulAut W) v * v⁻¹) * v := by
        rw [inv_mul_cancel_right]
      have hsc := hHC _ hsH _ hc
      have hcc : ((s : MulAut W) v * v⁻¹) * ((s : MulAut W) v * v⁻¹) = 1 := by
        have := hW ((s : MulAut W) v * v⁻¹)
        rwa [pow_two] at this
      rw [MulAut.mul_apply, MulAut.one_apply]
      conv_lhs => rw [hsv, map_mul, hsc]
      calc (s : MulAut W) v * v⁻¹ * (s : MulAut W) v
          = (s : MulAut W) v * v⁻¹ * (((s : MulAut W) v * v⁻¹) * v) := by
            rw [inv_mul_cancel_right]
        _ = ((s : MulAut W) v * v⁻¹) * ((s : MulAut W) v * v⁻¹) * v := (mul_assoc _ _ _).symm
        _ = v := by rw [hcc, one_mul]
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, pow_two, Subgroup.coe_mul, Subgroup.coe_one]
    exact key
  have hS1 : S = ⊥ := hO S hSY hSn hS2
  have hyC : y ∈ centQuot C := by rw [mem_centQuot]; exact hyq
  have hyc : ∀ h ∈ H, y * h = h * y := by
    intro h hh
    have hcH : y * h * y⁻¹ * h⁻¹ ∈ H := H.mul_mem (hn y hy h hh) (H.inv_mem hh)
    have hcC : y * h * y⁻¹ * h⁻¹ ∈ centQuot C := by
      have h1 : h * y⁻¹ * h⁻¹ ∈ centQuot C :=
        conj_mem_centQuot (fun c hc => by rw [hHC h hh c hc]; exact hc) (Subgroup.inv_mem _ hyC)
      have h2 := Subgroup.mul_mem _ hyC h1
      simpa only [mul_assoc] using h2
    have hmem : y * h * y⁻¹ * h⁻¹ ∈ S := ⟨hcH, hcC⟩
    rw [hS1, Subgroup.mem_bot] at hmem
    calc y * h = y * h * y⁻¹ * h⁻¹ * (h * y) := by group
      _ = h * y := by rw [hmem, one_mul]
  have hfix : ∀ v ∈ commV H, y v = v := by
    intro v hv
    refine Subgroup.closure_induction (p := fun v _ => y v = v) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨h, hh, w, rfl⟩
      have hc : y w * w⁻¹ ∈ C := hyq w
      have hyw : y w = (y w * w⁻¹) * w := by simp
      have hyh : y (h w) = h (y w) := by
        rw [← MulAut.mul_apply, hyc h hh, MulAut.mul_apply]
      rw [map_mul, map_inv, hyh]
      conv_lhs => rw [hyw]
      rw [map_mul, hHC h hh _ hc, mul_inv, mul_comm (y w * w⁻¹) (h w), mul_assoc,
        ← mul_assoc (y w * w⁻¹), mul_inv_cancel, one_mul]
    · simp
    · intro a b _ _ ha hb
      rw [map_mul, ha, hb]
    · intro a _ ha
      rw [map_inv, ha]
  have htop := commV_eq_top hW hO hB hL hH
  refine MulEquiv.ext fun w => ?_
  have := hfix w (by rw [htop]; trivial)
  simpa using this

theorem zpow_apply_eq_self {M : Type*} [Group M] {f : MulAut M} {x : M} (h : f x = x) :
    ∀ k : ℤ, (f ^ k) x = x := by
  have hpos : ∀ n : ℕ, (f ^ n) x = x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, MulAut.mul_apply, h, ih]
  intro k
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · simpa using hpos n
  · rw [zpow_neg, zpow_natCast]
    calc (f ^ n)⁻¹ x = (f ^ n)⁻¹ ((f ^ n) x) := by rw [hpos n]
      _ = x := by simp

end CFSG.LocalAnalysis.WeakClosure81
