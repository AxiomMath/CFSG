module

public import CFSG.Quasithin.MS93.S59Base

public noncomputable section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Pointwise

namespace S59

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem commutator_le_of_elt_baseA (h : PUHyp M T L) {P Z₀ : Subgroup (puAmalgam h.le).Universal}
    (hPst : P ≤ stab _ (baseA (puAmalgam h.le))) (hZst : Z₀ ≤ stab _ (baseA (puAmalgam h.le)))
    (hPn : puTrans h.le L (baseA _) ≤ Subgroup.normalizer (P : Set (puAmalgam h.le).Universal))
    (hZn : puTrans h.le L (baseA _) ≤ Subgroup.normalizer (Z₀ : Set (puAmalgam h.le).Universal))
    {y : (puAmalgam h.le).Universal} (hy : y ∈ stab _ (baseA (puAmalgam h.le)))
    (hy2 : ∃ e : ℕ, y ^ 2 ^ e = 1) (hyQ : y ∉ Qv _ (baseA (puAmalgam h.le)))
    (hyZ : y ∈ Subgroup.normalizer (Z₀ : Set (puAmalgam h.le).Universal))
    (hyP : ∀ w ∈ P, y * w * y⁻¹ * w⁻¹ ∈ Z₀) :
    ⁅P, puTrans h.le L (baseA _)⁆ ≤ Z₀ := by
  have hLα : puTrans h.le L (baseA _) = imM h.le L := S5B.puTrans_L_baseA h
  have hQα : Qv _ (baseA (puAmalgam h.le)) = imM h.le (pCoreOf 2 M) :=
    puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le
  have hstM : stab _ (baseA (puAmalgam h.le)) = (puAmalgam h.le).ofA.range := by
    rw [puAmalgam.stab_baseA, imM, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]
  have hPP := S5B.imM_preM h.le hPst
  have hZZ := S5B.imM_preM h.le hZst
  have hPn₀ : L ≤ Subgroup.normalizer (S5B.preM h.le P : Set G) :=
    S5B.le_normalizer_preM h.le h.L_le (hLα ▸ hPn)
  have hZn₀ : L ≤ Subgroup.normalizer (S5B.preM h.le Z₀ : Set G) :=
    S5B.le_normalizer_preM h.le h.L_le (hLα ▸ hZn)
  have hyst := hy
  rw [hstM] at hy
  obtain ⟨y₀, rfl⟩ := hy
  have hyZ₀ : (y₀ : G) ∈ Subgroup.normalizer (S5B.preM h.le Z₀ : Set G) := by
    have hle : imM h.le (Subgroup.zpowers (y₀ : G)) ≤
        Subgroup.normalizer (Z₀ : Set (puAmalgam h.le).Universal) := by
      rintro _ ⟨m, hm, rfl⟩
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_subgroupOf.1 hm)
      have : m = y₀ ^ n := Subtype.ext (by simpa using hn.symm)
      rw [this, map_zpow]
      exact zpow_mem hyZ n
    have hzM : Subgroup.zpowers (y₀ : G) ≤ M := (Subgroup.zpowers_le).2 y₀.2
    exact S5B.le_normalizer_preM h.le hzM hle (Subgroup.mem_zpowers _)
  have hcore := S5B.commutator_le_of_two_elt h (W := S5B.preM h.le P)
    (Z := S5B.preM h.le Z₀) hPn₀ hZn₀ y₀.2 ?_ ?_ hyZ₀ ?_
  · have := (S5B.commutator_imM_le_iff h.le (S5B.preM_le h.le _) h.L_le).2 hcore
    rwa [hPP, ← hLα, hZZ] at this
  · obtain ⟨e, he⟩ := hy2
    refine ⟨e, ?_⟩
    have he' : (puAmalgam h.le).ofA (y₀ ^ 2 ^ e) = (puAmalgam h.le).ofA 1 := by
      rw [map_pow, map_one, he]
    have := (puAmalgam h.le).ofA_injective he'
    simpa using congrArg Subtype.val this
  · intro hO
    apply hyQ
    rw [hQα]
    exact ⟨y₀, Subgroup.mem_subgroupOf.2 hO, rfl⟩
  · rintro _ ⟨m, hm, rfl⟩
    have h2 : (puAmalgam h.le).ofA (y₀ * m * y₀⁻¹ * m⁻¹) ∈ Z₀ := by
      simpa [map_mul, map_inv] using hyP _ hm
    have hgoal := (S5B.mem_preM h.le (y₀ * m * y₀⁻¹ * m⁻¹)).2 h2
    simpa using hgoal

theorem commutator_le_xm_baseA (h : PUHyp M T L) {P : Subgroup (puAmalgam h.le).Universal}
    (hPst : P ≤ stab _ (baseA (puAmalgam h.le)))
    (hPn : puTrans h.le L (baseA _) ≤ Subgroup.normalizer (P : Set (puAmalgam h.le).Universal))
    {y : (puAmalgam h.le).Universal} (hy : y ∈ stab _ (baseA (puAmalgam h.le)))
    (hy2 : ∃ e : ℕ, y ^ 2 ^ e = 1) (hyQ : y ∉ Qv _ (baseA (puAmalgam h.le)))
    (hyP : ∀ w ∈ P, y * w * y⁻¹ * w⁻¹ ∈ XM _ (baseA (puAmalgam h.le))) :
    ⁅P, puTrans h.le L (baseA _)⁆ ≤ XM _ (baseA (puAmalgam h.le)) :=
  commutator_le_of_elt_baseA h hPst ((xm_le_qv _ _).trans (qv_le_stab _ _)) hPn
    ((puTrans_le_stab h.le L _).trans (stab_le_normalizer_xm _ _)) hy hy2 hyQ
    (stab_le_normalizer_xm _ _ hy) hyP

theorem commutator_le_uSub_of_elt_baseA (h : PUHyp M T L) (h32 : ⁅Xq M, L⁆ ≤ Uq M T L)
    {P : Subgroup (puAmalgam h.le).Universal} (hPst : P ≤ stab _ (baseA (puAmalgam h.le)))
    (hPn : puTrans h.le L (baseA _) ≤ Subgroup.normalizer (P : Set (puAmalgam h.le).Universal))
    {y : (puAmalgam h.le).Universal} (hy : y ∈ stab _ (baseA (puAmalgam h.le)))
    (hy2 : ∃ e : ℕ, y ^ 2 ^ e = 1) (hyQ : y ∉ Qv _ (baseA (puAmalgam h.le)))
    (hyP : ∀ w ∈ P, y * w * y⁻¹ * w⁻¹ ∈ XM _ (baseA (puAmalgam h.le))) :
    ⁅P, puTrans h.le L (baseA _)⁆ ≤ S5.uSub h.le L (baseA _) := by
  have hXU : ⁅XM _ (baseA (puAmalgam h.le)), puTrans h.le L (baseA _)⁆ ≤
      S5.uSub h.le L (baseA _) := by
    rw [S5B.xm_baseA_eq h, S5B.puTrans_L_baseA h, S5B.uSub_baseA h]
    exact (S5B.commutator_imM_le_iff h.le (Xq_le M) h.L_le).2 h32
  have hLst := puTrans_le_stab h.le L (baseA (puAmalgam h.le))
  have hUn := stab_le_normalizer_uSub h (L := L) (baseA (puAmalgam h.le))
  have hperf : ⁅puTrans h.le L (baseA (puAmalgam h.le)), puTrans h.le L (baseA _)⁆ =
      puTrans h.le L (baseA _) := by
    rw [S5B.puTrans_L_baseA h, ← imM_commutator h.le h.L_le h.L_le, h.perfect]
  exact S5B.commutator_le_of_perfect hperf (hPst.trans hUn) (hLst.trans hUn)
    (commutator_le_xm_baseA h hPst hPn hy hy2 hyQ hyP) hXU

theorem commutator_le_of_elt (h : PUHyp M T L) {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    {P Z₀ : Subgroup (puAmalgam h.le).Universal} (hPst : P ≤ stab _ δ) (hZst : Z₀ ≤ stab _ δ)
    (hPn : puTrans h.le L δ ≤ Subgroup.normalizer (P : Set (puAmalgam h.le).Universal))
    (hZn : puTrans h.le L δ ≤ Subgroup.normalizer (Z₀ : Set (puAmalgam h.le).Universal))
    {y : (puAmalgam h.le).Universal} (hy : y ∈ stab _ δ) (hy2 : ∃ e : ℕ, y ^ 2 ^ e = 1)
    (hyQ : y ∉ Qv _ δ) (hyZ : y ∈ Subgroup.normalizer (Z₀ : Set (puAmalgam h.le).Universal))
    (hyP : ∀ w ∈ P, y * w * y⁻¹ * w⁻¹ ∈ Z₀) :
    ⁅P, puTrans h.le L δ⁆ ≤ Z₀ := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hδ
  have hLg := puTrans_smul (hTM := h.le) hLn g (baseA _)
  have hQg := qv_smul (puAmalgam h.le) g (baseA _)
  have hSg := stab_smul (puAmalgam h.le) g (baseA _)
  set P' := P.map (MulAut.conj g⁻¹).toMonoidHom with hP'
  set Z' := Z₀.map (MulAut.conj g⁻¹).toMonoidHom with hZ'
  have hPP' : P = P'.map (MulAut.conj g).toMonoidHom := by rw [hP', map_conj_map_conj_inv]
  have hZZ' : Z₀ = Z'.map (MulAut.conj g).toMonoidHom := by rw [hZ', map_conj_map_conj_inv]
  rw [hPP'] at hPst hPn hyP ⊢
  rw [hZZ'] at hZst hZn hyZ hyP ⊢
  rw [hSg, map_conj_le_map_conj_iff] at hPst hZst
  rw [hLg, normalizer_map_conj, map_conj_le_map_conj_iff] at hPn hZn
  rw [hSg] at hy
  obtain ⟨y', hy', rfl⟩ := hy
  rw [hQg] at hyQ
  have hyQ' : y' ∉ Qv _ (baseA (puAmalgam h.le)) := fun hm => hyQ ⟨y', hm, rfl⟩
  have hy2' : ∃ e : ℕ, y' ^ 2 ^ e = 1 := by
    obtain ⟨e, he⟩ := hy2
    refine ⟨e, (MulAut.conj g).injective ?_⟩
    rw [map_pow, map_one]
    exact he
  have hyZ' : y' ∈ Subgroup.normalizer (Z' : Set (puAmalgam h.le).Universal) := by
    rw [normalizer_map_conj] at hyZ
    obtain ⟨z, hz, hze⟩ := hyZ
    have : z = y' := (MulAut.conj g).injective hze
    rw [← this]
    exact hz
  have hyP' : ∀ w ∈ P', y' * w * y'⁻¹ * w⁻¹ ∈ Z' := by
    intro w hw
    have h1 := hyP _ ⟨w, hw, rfl⟩
    obtain ⟨x, hx, hxe⟩ := h1
    have : x = y' * w * y'⁻¹ * w⁻¹ := (MulAut.conj g).injective (by
      rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul] at hxe
      simpa using hxe)
    rw [← this]
    exact hx
  have key := commutator_le_of_elt_baseA h hPst hZst hPn hZn hy' hy2' hyQ' hyZ' hyP'
  rw [hLg, ← Subgroup.map_commutator]
  exact Subgroup.map_mono key

theorem commutator_le_uSub_of_elt (h : PUHyp M T L) (h32 : ⁅Xq M, L⁆ ≤ Uq M T L)
    {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) {P : Subgroup (puAmalgam h.le).Universal}
    (hPst : P ≤ stab _ δ)
    (hPn : puTrans h.le L δ ≤ Subgroup.normalizer (P : Set (puAmalgam h.le).Universal))
    {y : (puAmalgam h.le).Universal} (hy : y ∈ stab _ δ) (hy2 : ∃ e : ℕ, y ^ 2 ^ e = 1)
    (hyQ : y ∉ Qv _ δ) (hyP : ∀ w ∈ P, y * w * y⁻¹ * w⁻¹ ∈ XM _ δ) :
    ⁅P, puTrans h.le L δ⁆ ≤ S5.uSub h.le L δ := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hδ
  have hLg := puTrans_smul (hTM := h.le) hLn g (baseA _)
  have hXg := xm_smul (puAmalgam h.le) g (baseA _)
  have hUg := S5B.uSub_smul h.le hLn g (baseA (puAmalgam h.le))
  have hQg := qv_smul (puAmalgam h.le) g (baseA _)
  have hSg := stab_smul (puAmalgam h.le) g (baseA _)
  set P' := P.map (MulAut.conj g⁻¹).toMonoidHom with hP'
  have hPP' : P = P'.map (MulAut.conj g).toMonoidHom := by rw [hP', map_conj_map_conj_inv]
  rw [hPP'] at hPst hPn hyP ⊢
  rw [hSg, map_conj_le_map_conj_iff] at hPst
  rw [hLg, normalizer_map_conj, map_conj_le_map_conj_iff] at hPn
  rw [hSg] at hy
  obtain ⟨y', hy', rfl⟩ := hy
  rw [hQg] at hyQ
  have hyQ' : y' ∉ Qv _ (baseA (puAmalgam h.le)) := fun hm => hyQ ⟨y', hm, rfl⟩
  have hy2' : ∃ e : ℕ, y' ^ 2 ^ e = 1 := by
    obtain ⟨e, he⟩ := hy2
    refine ⟨e, (MulAut.conj g).injective ?_⟩
    rw [map_pow, map_one]
    exact he
  have hyP' : ∀ w ∈ P', y' * w * y'⁻¹ * w⁻¹ ∈ XM _ (baseA (puAmalgam h.le)) := by
    intro w hw
    have h1 := hyP _ ⟨w, hw, rfl⟩
    rw [hXg] at h1
    obtain ⟨x, hx, hxe⟩ := h1
    have : x = y' * w * y'⁻¹ * w⁻¹ := (MulAut.conj g).injective (by
      rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul] at hxe
      simpa using hxe)
    rw [← this]
    exact hx
  have key := commutator_le_uSub_of_elt_baseA h h32 hPst hPn hy' hy2' hyQ' hyP'
  rw [hLg, hUg, ← Subgroup.map_commutator]
  exact Subgroup.map_mono key

theorem inf_le_bSub_of_elt (h : PUHyp M T L) (h32 : ⁅Xq M, L⁆ ≤ Uq M T L)
    {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) {P : Subgroup (puAmalgam h.le).Universal}
    (hPst : P ≤ stab _ δ)
    (hPn : puTrans h.le L δ ≤ Subgroup.normalizer (P : Set (puAmalgam h.le).Universal))
    {y : (puAmalgam h.le).Universal} (hy : y ∈ stab _ δ) (hy2 : ∃ e : ℕ, y ^ 2 ^ e = 1)
    (hyQ : y ∉ Qv _ δ) (hyP : ∀ w ∈ P, y * w * y⁻¹ * w⁻¹ ∈ XM _ δ) :
    P ⊓ Vv _ δ ≤ S5.bSub h.le L δ := by
  have hc := commutator_le_uSub_of_elt h h32 hδ hPst hPn hy hy2 hyQ hyP
  have hUZ : S5.uSub h.le L δ ≤ ZM _ δ :=
    commutator_le_left_of_le_normalizer ((puTrans_le_stab h.le L δ).trans
      (stab_le_normalizer_zm _ _))
  rintro v ⟨hvP, hvV⟩
  refine Subgroup.subset_closure ⟨hvV, fun l hl => ?_⟩
  exact hUZ (hc (Subgroup.commutator_mem_commutator hvP hl))

end S59

end CFSG.Quasithin.MS93
