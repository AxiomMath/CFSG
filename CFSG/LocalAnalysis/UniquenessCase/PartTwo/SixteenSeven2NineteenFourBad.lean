module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2NineteenFourIdx

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

private theorem s16c167_four_map_eq_iff_mem_stabSub {Y : Subgroup W} {g : MulAut W} :
    Y.map g.toMonoidHom = Y ↔ g ∈ stabSub Y := by
  constructor
  · intro h
    rw [mem_stabSub]
    intro u
    constructor
    · intro hu
      have hmem : g u ∈ Y.map g.toMonoidHom := by rw [h]; exact hu
      obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.mp hmem
      rwa [g.injective hvu] at hv
    · intro hu
      have hmem : g u ∈ Y.map g.toMonoidHom := Subgroup.mem_map_of_mem g.toMonoidHom hu
      rwa [h] at hmem
  · intro hg
    ext u
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (mem_stabSub.mp hg v).mpr hv
    · intro hu
      refine ⟨g⁻¹ u, ?_, ?_⟩
      · exact (mem_stabSub.mp hg (g⁻¹ u)).mp (by simpa using hu)
      · simp

private theorem s16c167_four_map_eq_map_iff {Y : Subgroup W} {g g' : MulAut W} :
    Y.map g.toMonoidHom = Y.map g'.toMonoidHom ↔ (g⁻¹ * g') ∈ stabSub Y := by
  constructor
  · intro h
    have h2 : (Y.map g.toMonoidHom).map g⁻¹.toMonoidHom =
        (Y.map g'.toMonoidHom).map g⁻¹.toMonoidHom := by rw [h]
    rw [Subgroup.map_map, Subgroup.map_map] at h2
    change Y.map (g⁻¹ * g).toMonoidHom = Y.map (g⁻¹ * g').toMonoidHom at h2
    rw [inv_mul_cancel] at h2
    rw [show ((1 : MulAut W).toMonoidHom) = MonoidHom.id W from rfl, Subgroup.map_id] at h2
    exact (s16c167_four_map_eq_iff_mem_stabSub).mp h2.symm
  · intro hst
    have h2 : Y.map (g⁻¹ * g').toMonoidHom = Y :=
      (s16c167_four_map_eq_iff_mem_stabSub).mpr hst
    have h3 : (Y.map (g⁻¹ * g').toMonoidHom).map g.toMonoidHom = Y.map g.toMonoidHom := by
      rw [h2]
    rw [Subgroup.map_map] at h3
    change Y.map (g * (g⁻¹ * g')).toMonoidHom = Y.map g.toMonoidHom at h3
    rw [← mul_assoc, mul_inv_cancel, one_mul] at h3
    exact h3.symm

private theorem s16c167_four_exists_fixed {E : Subgroup (MulAut W)} {𝒴 : Set (Subgroup W)}
    (F : Four19 E 𝒴) {Y : Subgroup W} (hY : Y ∈ 𝒴) :
    ∃ w₀ ∈ Y, w₀ ≠ 1 ∧ ∀ g ∈ E ⊓ stabSub Y, g w₀ = w₀ := by
  classical
  let X : Subgroup (MulAut W) := E ⊓ stabSub Y
  have hX2 : IsPGroup 2 ↥X := by
    refine isPGroup_two_of_sq_eq_one (fun x : ↥X => ?_)
    apply Subtype.ext
    simpa [pow_two] using F.sq_E x.1 x.2.1
  let act : MulAction ↥X ↥Y :=
    { smul := fun g y => ⟨g.1 (y : W), (mem_stabSub.mp g.2.2 (y : W)).mpr y.2⟩
      one_smul := fun y => by
        apply Subtype.ext
        change (1 : MulAut W) (y : W) = (y : W)
        rw [MulAut.one_apply]
      mul_smul := fun g h y => by
        apply Subtype.ext
        change ((g : MulAut W) * (h : MulAut W)) (y : W) =
          (g : MulAut W) ((h : MulAut W) (y : W))
        rw [MulAut.mul_apply] }
  letI : MulAction ↥X ↥Y := act
  have hcard : Nat.card ↥Y = 4 := by
    rw [card_eq_two_pow F.sq Y, F.rk_eq Y hY]
    norm_num
  have hdvd : 2 ∣ Nat.card ↥Y := by rw [hcard]; norm_num
  obtain ⟨b, hb, hbne⟩ :=
    hX2.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := ↥Y) hdvd
      (a := (1 : ↥Y)) (by
        rw [MulAction.mem_fixedPoints]
        intro g
        apply Subtype.ext
        change (g : MulAut W) (1 : W) = (1 : W)
        rw [map_one])
  refine ⟨(b : W), b.2, ?_, ?_⟩
  · intro hb1
    exact hbne (Subtype.ext hb1).symm
  · intro g hg
    have hfix : (⟨g, hg⟩ : ↥X) • b = b := (MulAction.mem_fixedPoints.mp hb) ⟨g, hg⟩
    exact congrArg Subtype.val hfix

private theorem s16c167_four_smul_smul_eq {g f : MulAut W} {v : W} (hcomm : g * f = f * g)
    (hgv : g v = v) : g (f v) = f v := by
  rw [← MulAut.mul_apply, hcomm, MulAut.mul_apply, hgv]

private theorem s16c167_four_disjoint_sup {S : Set (Subgroup W)} (hind : sSupIndep S)
    {A B C D : Subgroup W} (hA : A ∈ S) (hB : B ∈ S) (hC : C ∈ S) (hD : D ∈ S)
    (hAB : B ≠ A) (hAC : C ≠ A) (hAD : D ≠ A) (hBC : C ≠ B) (hBD : D ≠ B) :
    (A ⊔ B) ⊓ (C ⊔ D) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzAB, hzCD⟩ := Subgroup.mem_inf.mp hz
  obtain ⟨a, ha, b, hb, habz⟩ := Subgroup.mem_sup.mp hzAB
  rw [← habz] at hzCD ⊢
  have hBs : B ∈ S \ {A} := ⟨hB, by simpa using hAB⟩
  have hCs : C ∈ S \ {A} := ⟨hC, by simpa using hAC⟩
  have hDs : D ∈ S \ {A} := ⟨hD, by simpa using hAD⟩
  have hleA : C ⊔ D ≤ sSup (S \ {A}) := sup_le (le_sSup hCs) (le_sSup hDs)
  have hzAs : a * b ∈ sSup (S \ {A}) := hleA hzCD
  have hbA : b ∈ sSup (S \ {A}) := le_sSup hBs hb
  have haA : a ∈ sSup (S \ {A}) := by
    have h : a = (a * b) * b⁻¹ := by group
    rw [h]
    exact (sSup (S \ {A})).mul_mem hzAs ((sSup (S \ {A})).inv_mem hbA)
  have ha1 : a = 1 := by
    have hmem : a ∈ A ⊓ sSup (S \ {A}) := ⟨ha, haA⟩
    rw [(hind hA).eq_bot] at hmem
    exact Subgroup.mem_bot.mp hmem
  rw [ha1, one_mul]
  have hCsB : C ∈ S \ {B} := ⟨hC, by simpa using hBC⟩
  have hDsB : D ∈ S \ {B} := ⟨hD, by simpa using hBD⟩
  have hleB : C ⊔ D ≤ sSup (S \ {B}) := sup_le (le_sSup hCsB) (le_sSup hDsB)
  have hbCD : b ∈ C ⊔ D := by simpa [ha1] using hzCD
  have hbB : b ∈ sSup (S \ {B}) := hleB hbCD
  have hmem : b ∈ B ⊓ sSup (S \ {B}) := ⟨hb, hbB⟩
  rw [(hind hB).eq_bot] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem s16c167_four_bad_stab {E : Subgroup (MulAut W)} {𝒴 : Set (Subgroup W)}
    (F : Four19 E 𝒴) {Y : Subgroup W} (hY : Y ∈ 𝒴) {H : Subgroup (MulAut W)} (hHE : H ≤ E)
    (hH : E3.mQuot E H = 1) (hYH : E ⊓ stabSub Y ≤ H) : fixV H ≠ fixV E := by
  classical
  have hHneE : H ≠ E := by
    intro hHE'
    have h0 : E3.mQuot E H = 0 := by rw [hHE', E3.mQuot_self]
    rw [h0] at hH
    exact zero_ne_one hH
  obtain ⟨e, heE, heH⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hHE hHneE)
  have heK : e ∉ E ⊓ stabSub Y := fun h => heH (hYH h)
  obtain ⟨w₀, hw₀Y, hw₀ne, hw₀fix⟩ := s16c167_four_exists_fixed F hY
  by_cases hHK : H = E ⊓ stabSub Y
  · have hw₀H : w₀ ∈ fixV H := by
      rw [hHK, mem_fixV]
      exact hw₀fix
    have hw₀notE : w₀ ∉ fixV E := by
      rw [mem_fixV]
      intro hfix
      have hew : e w₀ = w₀ := hfix e heE
      have hstab : e ∉ stabSub Y := fun hs => heK (Subgroup.mem_inf.mpr ⟨heE, hs⟩)
      have hmapne : Y.map e.toMonoidHom ≠ Y :=
        fun h => hstab ((s16c167_four_map_eq_iff_mem_stabSub).mp h)
      have hmapmem : Y.map e.toMonoidHom ∈ 𝒴 := F.perm e heE Y hY
      have hdisj := s16c167_cfg4_inf_eq_bot F.indep hY hmapmem hmapne.symm
      have hw₀im : w₀ ∈ Y.map e.toMonoidHom := Subgroup.mem_map.mpr ⟨w₀, hw₀Y, hew⟩
      have hmem : w₀ ∈ Y ⊓ Y.map e.toMonoidHom := ⟨hw₀Y, hw₀im⟩
      rw [hdisj] at hmem
      exact hw₀ne (Subgroup.mem_bot.mp hmem)
    exact fun heq => hw₀notE (heq ▸ hw₀H)
  · have hKleH : E ⊓ stabSub Y ≤ H := hYH
    have hKneH : E ⊓ stabSub Y ≠ H := fun h => hHK h.symm
    have hH2 : IsPGroup 2 ↥H := isPGroup_two_of_sq_eq_one (fun x : ↥H => by
      apply Subtype.ext
      simpa [pow_two] using F.sq_E x.1 (hHE x.2))
    have hmHK : E3.mQuot H (E ⊓ stabSub Y) = 1 := by
      have hadd := E3.mQuot_add (V := E) (U := E ⊓ stabSub Y) (U' := H) hKleH hHE
      rw [hH] at hadd
      have hle : E3.mQuot H (E ⊓ stabSub Y) ≤ 1 := by
        have := s16c167_four_index_stab F hY
        rw [hadd] at this
        omega
      have hne : E3.mQuot H (E ⊓ stabSub Y) ≠ 0 := fun h0 =>
        hKneH ((E3.mQuot_eq_zero_iff hH2 hKleH).mp h0)
      omega
    have hrel : (E ⊓ stabSub Y).relIndex H = 2 := by
      rw [E3.relIndex_eq_two_pow hH2 (E ⊓ stabSub Y), hmHK, pow_one]
    have hsub : ((E ⊓ stabSub Y).subgroupOf H).index = 2 := hrel
    obtain ⟨a, ha, haall⟩ := Subgroup.index_eq_two_iff_exists_notMem_and'.mp hsub
    let f : MulAut W := a.1
    have hfH : f ∈ H := a.2
    have hfE : f ∈ E := hHE hfH
    have hfK : f ∉ E ⊓ stabSub Y := by
      intro hf
      exact ha (Subgroup.mem_subgroupOf.mpr hf)
    have hf2 : f * f = 1 := F.sq_E f hfE
    have hefK : e * f ∉ E ⊓ stabSub Y := by
      intro hef
      apply heH
      have hefH : e * f ∈ H := hYH hef
      have hmem : (e * f) * f ∈ H := H.mul_mem hefH hfH
      rwa [mul_assoc, hf2, mul_one] at hmem
    let w : W := w₀ * f w₀
    have hfixK : ∀ g ∈ E ⊓ stabSub Y, g w = w := by
      intro g hg
      obtain ⟨hgE, _⟩ := Subgroup.mem_inf.mp hg
      have hgw₀ : g w₀ = w₀ := hw₀fix g hg
      have hgfw : g (f w₀) = f w₀ :=
        s16c167_four_smul_smul_eq (F.comm g hgE f hfE) hgw₀
      calc g w = g (w₀ * f w₀) := rfl
        _ = g w₀ * g (f w₀) := by rw [map_mul]
        _ = w₀ * f w₀ := by rw [hgw₀, hgfw]
        _ = w := rfl
    have hfw : f w = w := by
      have hffw : f (f w₀) = w₀ := by
        have h1 : f (f w₀) = (f * f) w₀ := by rw [MulAut.mul_apply]
        rw [h1, hf2, MulAut.one_apply]
      calc f w = f (w₀ * f w₀) := rfl
        _ = f w₀ * f (f w₀) := by rw [map_mul]
        _ = f w₀ * w₀ := by rw [hffw]
        _ = w := mul_comm _ _
    have hwfixH : w ∈ fixV H := by
      rw [mem_fixV]
      intro h hh
      rcases haall ⟨h, hh⟩ with hfhK | hhK
      · have hfhK' : f * h ∈ E ⊓ stabSub Y := by
          rw [Subgroup.mem_subgroupOf] at hfhK
          simpa [f] using hfhK
        have hh_eq : f * (f * h) = h := by rw [← mul_assoc, hf2, one_mul]
        rw [← hh_eq, MulAut.mul_apply, hfixK (f * h) hfhK', hfw]
      · have hhK' : h ∈ E ⊓ stabSub Y := by
          rw [Subgroup.mem_subgroupOf] at hhK
          simpa [f] using hhK
        exact hfixK h hhK'
    have hwnotE : w ∉ fixV E := by
      rw [mem_fixV]
      intro hfix
      have hew : e w = w := hfix e heE
      have hfYmem : Y.map f.toMonoidHom ∈ 𝒴 := F.perm f hfE Y hY
      have heYmem : Y.map e.toMonoidHom ∈ 𝒴 := F.perm e heE Y hY
      have hefYmem : Y.map (e * f).toMonoidHom ∈ 𝒴 :=
        F.perm (e * f) (E.mul_mem heE hfE) Y hY
      have hfYne : Y.map f.toMonoidHom ≠ Y := fun h =>
        hfK (Subgroup.mem_inf.mpr ⟨hfE, (s16c167_four_map_eq_iff_mem_stabSub).mp h⟩)
      have heYne : Y.map e.toMonoidHom ≠ Y := fun h =>
        heK (Subgroup.mem_inf.mpr ⟨heE, (s16c167_four_map_eq_iff_mem_stabSub).mp h⟩)
      have hefYne : Y.map (e * f).toMonoidHom ≠ Y := fun h =>
        hefK (Subgroup.mem_inf.mpr ⟨E.mul_mem heE hfE,
          (s16c167_four_map_eq_iff_mem_stabSub).mp h⟩)
      have heYne_fY : Y.map e.toMonoidHom ≠ Y.map f.toMonoidHom := by
        intro h
        have hst : e⁻¹ * f ∈ stabSub Y := (s16c167_four_map_eq_map_iff).mp h
        have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right
          (by simpa [pow_two] using F.sq_E e heE)
        rw [heinv] at hst
        exact hefK (Subgroup.mem_inf.mpr ⟨E.mul_mem heE hfE, hst⟩)
      have hefYne_fY : Y.map (e * f).toMonoidHom ≠ Y.map f.toMonoidHom := by
        intro h
        have hst : (e * f)⁻¹ * f ∈ stabSub Y := (s16c167_four_map_eq_map_iff).mp h
        have hefinv : (e * f)⁻¹ = e * f := by
          apply inv_eq_of_mul_eq_one_right
          simpa [pow_two] using F.sq_E (e * f) (E.mul_mem heE hfE)
        have hsimp : (e * f)⁻¹ * f = e := by rw [hefinv, mul_assoc, hf2, mul_one]
        rw [hsimp] at hst
        exact heK (Subgroup.mem_inf.mpr ⟨heE, hst⟩)
      have hdisj := s16c167_four_disjoint_sup F.indep hY hfYmem heYmem hefYmem
        hfYne heYne hefYne heYne_fY hefYne_fY
      have hwAB : w ∈ Y ⊔ Y.map f.toMonoidHom :=
        Subgroup.mem_sup.mpr ⟨w₀, hw₀Y, f w₀,
          Subgroup.mem_map.mpr ⟨w₀, hw₀Y, rfl⟩, rfl⟩
      have hwCD : w ∈ Y.map e.toMonoidHom ⊔ Y.map (e * f).toMonoidHom := by
        refine Subgroup.mem_sup.mpr ⟨e w₀, Subgroup.mem_map.mpr ⟨w₀, hw₀Y, rfl⟩,
          (e * f) w₀, Subgroup.mem_map.mpr ⟨w₀, hw₀Y, rfl⟩, ?_⟩
        rw [MulAut.mul_apply, ← map_mul]
        exact hew
      have hw1 : w = 1 := by
        have hmem : w ∈ (Y ⊔ Y.map f.toMonoidHom) ⊓
            (Y.map e.toMonoidHom ⊔ Y.map (e * f).toMonoidHom) := ⟨hwAB, hwCD⟩
        rw [hdisj] at hmem
        exact Subgroup.mem_bot.mp hmem
      have h1 : w₀ = (f w₀)⁻¹ := eq_inv_of_mul_eq_one_left (by simpa [w] using hw1)
      have h2 : (f w₀)⁻¹ = f w₀ := by
        apply inv_eq_of_mul_eq_one_right
        simpa [pow_two] using F.sq (f w₀)
      have hw₀_fY : w₀ ∈ Y.map f.toMonoidHom :=
        Subgroup.mem_map.mpr ⟨w₀, hw₀Y, (h1.trans h2).symm⟩
      have hmem : w₀ ∈ Y ⊓ Y.map f.toMonoidHom := ⟨hw₀Y, hw₀_fY⟩
      rw [s16c167_cfg4_inf_eq_bot F.indep hY hfYmem hfYne.symm] at hmem
      exact hw₀ne (Subgroup.mem_bot.mp hmem)
    exact fun heq => hwnotE (heq ▸ hwfixH)

theorem s16c167_four_bad_cent {E : Subgroup (MulAut W)} {𝒴 : Set (Subgroup W)}
    (F : Four19 E 𝒴) {Y : Subgroup W} (hY : Y ∈ 𝒴) (hne : E ⊓ centSub Y ≠ E ⊓ stabSub Y)
    (hidx : E3.mQuot E (E ⊓ stabSub Y) ≤ 1) {H : Subgroup (MulAut W)} (hHE : H ≤ E)
    (hH : E3.mQuot E H = 1) (hcut : H ⊓ (E ⊓ stabSub Y) = E ⊓ centSub Y) :
    fixV H ≠ fixV E := by
  classical
  have hE2 : IsPGroup 2 ↥E := isPGroup_two_of_sq_eq_one (fun x : ↥E => by
    apply Subtype.ext
    simpa [pow_two] using F.sq_E x.1 x.2)
  have hKleE : E ⊓ stabSub Y ≤ E := inf_le_left
  have hNleK : E ⊓ centSub Y ≤ E ⊓ stabSub Y := inf_le_inf_left E (centSub_le_stabSub Y)
  have hNKne : E ⊓ centSub Y ≠ E ⊓ stabSub Y := hne
  obtain ⟨e₁, he₁K, he₁N⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hNleK hNKne)
  have he₁E : e₁ ∈ E := (Subgroup.mem_inf.mp he₁K).1
  have he₁ncent : e₁ ∉ centSub Y := fun hc =>
    he₁N (Subgroup.mem_inf.mpr ⟨he₁E, hc⟩)
  rw [mem_centSub] at he₁ncent
  obtain ⟨w₀, hw₀⟩ := not_forall.mp he₁ncent
  rw [not_imp] at hw₀
  obtain ⟨hw₀Y, hw₀moved⟩ := hw₀
  by_cases hKE : E ⊓ stabSub Y = E
  · have hH_N : H = E ⊓ centSub Y := by
      have h1 : E ⊓ stabSub Y = E := hKE
      rw [h1, inf_eq_left.mpr hHE] at hcut
      exact hcut
    have hw₀H : w₀ ∈ fixV H := by
      rw [hH_N, mem_fixV]
      intro h hh
      exact (mem_centSub.mp (Subgroup.mem_inf.mp hh).2) w₀ hw₀Y
    have hw₀notE : w₀ ∉ fixV E := by
      rw [mem_fixV]
      intro hfix
      exact hw₀moved (hfix e₁ he₁E)
    exact fun heq => hw₀notE (heq ▸ hw₀H)
  · have hmEK : E3.mQuot E (E ⊓ stabSub Y) = 1 := by
      have hpos : 0 < E3.mQuot E (E ⊓ stabSub Y) := by
        by_contra h
        exact hKE ((E3.mQuot_eq_zero_iff hE2 hKleE).mp (Nat.eq_zero_of_not_pos h))
      omega
    have hHneK : H ≠ E ⊓ stabSub Y := by
      intro hHK
      apply hNKne
      rw [← hcut, hHK, inf_idem]
    have hHnleK : ¬ H ≤ E ⊓ stabSub Y := by
      intro hHK
      have hadd := E3.mQuot_add (V := E) (U := H) (U' := E ⊓ stabSub Y) hHK hKleE
      rw [hH, hmEK] at hadd
      have hK2 : IsPGroup 2 ↥(E ⊓ stabSub Y) := isPGroup_two_of_sq_eq_one
        (fun x : ↥(E ⊓ stabSub Y) => by
          apply Subtype.ext
          simpa [pow_two] using F.sq_E x.1 x.2.1)
      have hmKH : E3.mQuot (E ⊓ stabSub Y) H = 0 := by omega
      exact hHneK ((E3.mQuot_eq_zero_iff hK2 hHK).mp hmKH)
    obtain ⟨f, hfH, hfK⟩ := Set.not_subset.mp hHnleK
    have hfE : f ∈ E := hHE hfH
    have hf2 : f * f = 1 := F.sq_E f hfE
    have hEdecomp : ∀ b ∈ E, f * b ∈ E ⊓ stabSub Y ∨ b ∈ E ⊓ stabSub Y := by
      intro b hbE
      have hKidx : (E ⊓ stabSub Y).relIndex E = 2 := by
        rw [E3.relIndex_eq_two_pow hE2 (E ⊓ stabSub Y), hmEK, pow_one]
      have hsub : ((E ⊓ stabSub Y).subgroupOf E).index = 2 := hKidx
      obtain ⟨a, ha, haall⟩ := Subgroup.index_eq_two_iff_exists_notMem_and'.mp hsub
      have haE : a.1 ∈ E := a.2
      have haf : a.1 * f ∈ E ⊓ stabSub Y := by
        rcases haall ⟨f, hfE⟩ with h | h
        · rw [Subgroup.mem_subgroupOf] at h
          exact h
        · have hfK' : f ∈ E ⊓ stabSub Y := by rwa [Subgroup.mem_subgroupOf] at h
          exact absurd hfK' hfK
      have hb'E : (a.1 * f) * b ∈ E := E.mul_mem (E.mul_mem haE hfE) hbE
      have hb' : a.1 * ((a.1 * f) * b) ∈ E ⊓ stabSub Y ∨
          ((a.1 * f) * b) ∈ E ⊓ stabSub Y := haall ⟨(a.1 * f) * b, hb'E⟩
      rcases hb' with h | h
      · left
        have heq : a.1 * ((a.1 * f) * b) = f * b := by
          calc a.1 * ((a.1 * f) * b) = (a.1 * a.1) * (f * b) := by ac_rfl
            _ = f * b := by rw [F.sq_E a.1 haE, one_mul]
        rwa [heq] at h
      · right
        have heq : b = (a.1 * f)⁻¹ * ((a.1 * f) * b) := by group
        rw [heq]
        exact (E ⊓ stabSub Y).mul_mem ((E ⊓ stabSub Y).inv_mem haf) h
    let w : W := w₀ * f w₀
    have hfixN : ∀ g ∈ E ⊓ centSub Y, g w = w := by
      intro g hg
      obtain ⟨hgE, hgcent⟩ := Subgroup.mem_inf.mp hg
      have hgw₀ : g w₀ = w₀ := (mem_centSub.mp hgcent) w₀ hw₀Y
      have hgfw : g (f w₀) = f w₀ :=
        s16c167_four_smul_smul_eq (F.comm g hgE f hfE) hgw₀
      calc g w = g (w₀ * f w₀) := rfl
        _ = g w₀ * g (f w₀) := by rw [map_mul]
        _ = w₀ * f w₀ := by rw [hgw₀, hgfw]
        _ = w := rfl
    have hfw : f w = w := by
      have hffw : f (f w₀) = w₀ := by
        have h1 : f (f w₀) = (f * f) w₀ := by rw [MulAut.mul_apply]
        rw [h1, hf2, MulAut.one_apply]
      calc f w = f (w₀ * f w₀) := rfl
        _ = f w₀ * f (f w₀) := by rw [map_mul]
        _ = f w₀ * w₀ := by rw [hffw]
        _ = w := mul_comm _ _
    have hwfixH : w ∈ fixV H := by
      rw [mem_fixV]
      intro h hh
      rcases hEdecomp h (hHE hh) with hfhK | hhK
      · have hfhN : f * h ∈ E ⊓ centSub Y := by
          have hmem : f * h ∈ H ⊓ (E ⊓ stabSub Y) := ⟨H.mul_mem hfH hh, hfhK⟩
          rwa [hcut] at hmem
        have hh_eq : f * (f * h) = h := by rw [← mul_assoc, hf2, one_mul]
        rw [← hh_eq, MulAut.mul_apply, hfixN (f * h) hfhN, hfw]
      · have hhN : h ∈ E ⊓ centSub Y := by
          have hmem : h ∈ H ⊓ (E ⊓ stabSub Y) := ⟨hh, hhK⟩
          rwa [hcut] at hmem
        exact hfixN h hhN
    have hwnotE : w ∉ fixV E := by
      rw [mem_fixV]
      intro hfix
      have hew : e₁ w = w := hfix e₁ he₁E
      have he₁fw : e₁ (f w₀) = f (e₁ w₀) := by
        have h1 : e₁ (f w₀) = (e₁ * f) w₀ := by rw [MulAut.mul_apply]
        rw [h1, F.comm e₁ he₁E f hfE, ← MulAut.mul_apply]
      have h1 : e₁ w = e₁ w₀ * f (e₁ w₀) := by
        calc e₁ w = e₁ (w₀ * f w₀) := rfl
          _ = e₁ w₀ * e₁ (f w₀) := by rw [map_mul]
          _ = e₁ w₀ * f (e₁ w₀) := by rw [he₁fw]
      have hew' : e₁ w₀ * f (e₁ w₀) = w₀ * f w₀ := by
        rw [← h1, hew]
      let u : W := w₀ * (e₁ w₀)⁻¹
      have huY : u ∈ Y := by
        have he₁w₀Y : e₁ w₀ ∈ Y :=
          (mem_stabSub.mp (Subgroup.mem_inf.mp he₁K).2 w₀).mpr hw₀Y
        exact Y.mul_mem hw₀Y (Y.inv_mem he₁w₀Y)
      have hu_ne : u ≠ 1 := by
        intro hu1
        apply hw₀moved
        have h : w₀ = e₁ w₀ := mul_inv_eq_one.mp (by simpa [u] using hu1)
        exact h.symm
      have hfu : f u = f w₀ * (f (e₁ w₀))⁻¹ := by
        show f (w₀ * (e₁ w₀)⁻¹) = f w₀ * (f (e₁ w₀))⁻¹
        rw [map_mul, map_inv]
      have hu_mul : u * f u = 1 := by
        have h2 : w₀ * (e₁ w₀)⁻¹ * (f w₀ * (f (e₁ w₀))⁻¹)
            = (w₀ * f w₀) * ((e₁ w₀) * f (e₁ w₀))⁻¹ := by
          rw [mul_inv_rev]; ac_rfl
        have huu : u * f u = w₀ * (e₁ w₀)⁻¹ * (f w₀ * (f (e₁ w₀))⁻¹) := by
          rw [hfu]
        rw [huu, h2, hew', mul_inv_cancel]
      have hfu_eq : f u = u := by
        have h : u⁻¹ = f u := inv_eq_of_mul_eq_one_right hu_mul
        have hu_inv : u⁻¹ = u := by
          apply inv_eq_of_mul_eq_one_right
          simpa [pow_two] using F.sq u
        rw [hu_inv] at h
        exact h.symm
      have hu_fY : u ∈ Y.map f.toMonoidHom := Subgroup.mem_map.mpr ⟨u, huY, hfu_eq⟩
      have hfYne : Y.map f.toMonoidHom ≠ Y := fun h =>
        hfK (Subgroup.mem_inf.mpr ⟨hfE, (s16c167_four_map_eq_iff_mem_stabSub).mp h⟩)
      have hfYmem : Y.map f.toMonoidHom ∈ 𝒴 := F.perm f hfE Y hY
      have hmem : u ∈ Y ⊓ Y.map f.toMonoidHom := ⟨huY, hu_fY⟩
      rw [s16c167_cfg4_inf_eq_bot F.indep hY hfYmem hfYne.symm] at hmem
      exact hu_ne (Subgroup.mem_bot.mp hmem)
    exact fun heq => hwnotE (heq ▸ hwfixH)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
