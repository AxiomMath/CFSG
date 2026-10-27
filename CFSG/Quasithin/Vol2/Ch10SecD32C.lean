module

public import CFSG.Quasithin.Background.E3Lower

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Quasithin.E3

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_of_fusionIsTI {U : Subgroup G} (hTI : fusionIsTI U) {x u : G}
    (hu : u ∈ U) (hu1 : u ≠ 1) (hxu : x * u * x⁻¹ ∈ U) :
    x ∈ Subgroup.normalizer (U : Set G) := by
  by_contra hx
  have hne : U.map (MulAut.conj x).toMonoidHom ≠ U := by
    intro heq
    apply hx
    have h1 : conjSubgroup U x⁻¹ = U := by
      rw [conjSubgroup, inv_inv]
      exact heq
    have h2 := (Subgroup.normalizer (U : Set G)).inv_mem
      (conjSubgroup_eq_iff_mem_normalizer.mp h1)
    rwa [inv_inv] at h2
  have h3 : x * u * x⁻¹ ∈ U ⊓ U.map (MulAut.conj x).toMonoidHom := ⟨hxu, u, hu, rfl⟩
  rw [hTI x hne, Subgroup.mem_bot] at h3
  apply hu1
  calc u = x⁻¹ * (x * u * x⁻¹) * x := by group
    _ = 1 := by rw [h3]; group

omit [Finite G] in
theorem mQuot_bot_le_rParam {V : Subgroup G} (hTI : fusionIsTI V) :
    ((mQuot V ⊥ : ℕ) : ℕ∞) ≤ rParam V := by
  refine le_iInf₂ fun U hU => ?_
  obtain ⟨hUV, hC⟩ := hU
  rcases eq_or_ne U ⊥ with hU1 | hU1
  · subst hU1
    exact le_rfl
  · exfalso
    apply hC
    obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hU1
    have hu1' : u ≠ 1 := fun h' => hu1 (Subtype.ext h')
    intro x hx
    refine mem_normalizer_of_fusionIsTI hTI (hUV hu) hu1' ?_
    have hxu : x * u = u * x := ((Subgroup.mem_centralizer_iff.mp hx) u hu).symm
    rw [hxu, mul_inv_cancel_right]
    exact hUV hu

theorem exists_isWOffenderAt {T V : Subgroup G} (hV : IsElemAbelian 2 V) (hT : HypE322 T V)
    {k : ℕ} (hk : wParam T V = k) : ∃ g : G, IsWOffenderAt T V g := by
  have hk1 : ¬ wClos V k T ≤ T ⊓ Subgroup.centralizer (V : Set G) := by
    intro hle
    have : ((k + 1 : ℕ) : ℕ∞) ≤ wParam T V := by
      refine le_iInf₂ fun j hj => ?_
      have h1 : (k : ℕ∞) ≤ j := hk ▸ iInf₂_le j hj
      have h2 : j ≠ k := fun hjk => hj (hjk ▸ hle)
      have h1' : k ≤ j := Nat.cast_le.mp h1
      exact Nat.cast_le.mpr (by omega)
    rw [hk] at this
    exact absurd (Nat.cast_le.mp this) (by omega)
  obtain ⟨A, hA, hAC⟩ : ∃ A ∈ gammaSet V k T, ¬ A ≤ Subgroup.centralizer (V : Set G) := by
    by_contra hcon
    exact hk1 (iSup₂_le fun A hA => le_inf hA.1 (not_not.mp fun h => hcon ⟨A, hA, h⟩))
  obtain ⟨hAT, g, hAg, hAk⟩ := hA
  have hAB : A ≤ conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) :=
    le_inf hAg (hAT.trans hT.normal)
  have hBk : mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) ≤ k :=
    hAk ▸ mQuot_mono hAB
  have hBk' :
      mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) = k := by
    by_contra hne
    have hlt := lt_of_le_of_ne hBk hne
    apply hAC
    refine hAB.trans ?_
    have hTN : IsSylowIn 2 T (Subgroup.normalizer (V : Set G)) :=
      B6.isSylowTwoOf_mono hT.sylow hT.normal le_top
    have hB2 : IsPGroup 2 ↥(conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) :=
      (isPGroup_conjSubgroup (B2F.isPGroup_of_isElemAbelian hV) g).to_le inf_le_left
    obtain ⟨n, hn, hle⟩ := exists_le_conj_of_isSylowIn hTN inf_le_right hB2
    have h1 : conjSubgroup (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) n⁻¹ ≤ T := by
      have := conjSubgroup_mono_left n⁻¹ hle
      rwa [conjSubgroup_conj_inv] at this
    have hmem : conjSubgroup (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) n⁻¹ ∈
        gammaSet V (mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)))
          T := by
      refine ⟨h1, g * n⁻¹, ?_, ?_⟩
      · rw [← conjSubgroup_conjSubgroup]
        exact conjSubgroup_mono_left n⁻¹ inf_le_left
      · rw [← conjSubgroup_conjSubgroup, mQuot_conjSubgroup]
    have h2 : conjSubgroup (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) n⁻¹ ≤
        Subgroup.centralizer (V : Set G) :=
      ((le_wClos hmem).trans (wClos_le_of_lt_wParam (by rw [hk]; exact_mod_cast hlt))).trans
        inf_le_right
    have hnV : conjSubgroup V n = V := conjSubgroup_eq_iff_mem_normalizer.2 hn
    have h3 := conjSubgroup_mono_left n h2
    rwa [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one, conjSubgroup_centralizer,
      hnV] at h3
  refine ⟨g, fun hbot => hAC (hAg.trans ?_), by rw [hk, hBk']⟩
  exact le_centralizer_iff_comm.mp (commutator_eq_bot_iff_le_centralizer'.mp hbot)

theorem inf_centralizer_eq_bot_of_fusionIsTI {T V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hT : HypE322 T V) (h24 : HypE324 T V hV) (hTI : fusionIsTI V) {k : ℕ} (hk : wParam T V = k)
    {g : G} (hg : IsWOffenderAt T V g) :
    conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) ⊓ Subgroup.centralizer (V : Set G) = ⊥ := by
  set A := conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) with hA
  have h1 := e3_28_two_left hV hT h24 hg
  rw [hk, rk_autI_eq_mQuot hV inf_le_right] at h1
  have h2 := (mQuot_bot_le_rParam hTI).trans h1
  have h2' : mQuot V ⊥ ≤ k + mQuot A (A ⊓ Subgroup.centralizer (V : Set G)) := by
    exact_mod_cast h2
  have hAk : mQuot (conjSubgroup V g) A = k := by
    have := hg.2
    rw [hk] at this
    exact_mod_cast this.symm
  have h3 : mQuot (conjSubgroup V g) ⊥ = mQuot V ⊥ := by
    have := mQuot_conjSubgroup V ⊥ g
    rwa [conjSubgroup_bot] at this
  have h4 := mQuot_add (bot_le : (⊥ : Subgroup G) ≤ A) (inf_le_left : A ≤ conjSubgroup V g)
  have h5 := mQuot_add (bot_le : (⊥ : Subgroup G) ≤ A ⊓ Subgroup.centralizer (V : Set G))
    (inf_le_left : A ⊓ Subgroup.centralizer (V : Set G) ≤ A)
  have h0 : mQuot (A ⊓ Subgroup.centralizer (V : Set G)) ⊥ = 0 := by omega
  have hp : IsPGroup 2 ↥(A ⊓ Subgroup.centralizer (V : Set G)) :=
    (isPGroup_conjSubgroup (B2F.isPGroup_of_isElemAbelian hV) g).to_le
      (inf_le_left.trans inf_le_left)
  exact ((mQuot_eq_zero_iff hp bot_le).mp h0).symm

omit [Finite G] in
theorem inf_conjSubgroup_eq_bot {V : Subgroup G} (hTI : fusionIsTI V) {g : G}
    (hne : V ≠ conjSubgroup V g) : V ⊓ conjSubgroup V g = ⊥ :=
  hTI g⁻¹ (Ne.symm hne)

omit [Finite G] in
theorem mem_normalizer_conjSubgroup {V : Subgroup G} (hTI : fusionIsTI V) {g b v : G}
    (hb : b ∈ conjSubgroup V g) (hb1 : b ≠ 1) (hvb : v * b = b * v) :
    v ∈ Subgroup.normalizer (conjSubgroup V g : Set G) := by
  rw [mem_conjSubgroup_iff] at hb
  have hu1 : g * b * g⁻¹ ≠ 1 := fun h' => hb1 (by
    calc b = g⁻¹ * (g * b * g⁻¹) * g := by group
      _ = 1 := by rw [h']; group)
  have h1 : (g * v * g⁻¹) * (g * b * g⁻¹) * (g * v * g⁻¹)⁻¹ ∈ V := by
    have e : (g * v * g⁻¹) * (g * b * g⁻¹) * (g * v * g⁻¹)⁻¹ = g * b * g⁻¹ := by
      calc (g * v * g⁻¹) * (g * b * g⁻¹) * (g * v * g⁻¹)⁻¹ = g * (v * b) * v⁻¹ * g⁻¹ := by
            group
        _ = g * (b * v) * v⁻¹ * g⁻¹ := by rw [hvb]
        _ = g * b * g⁻¹ := by group
    rw [e]
    exact hb
  rw [← conjSubgroup_normalizer, mem_conjSubgroup_iff]
  exact mem_normalizer_of_fusionIsTI hTI hb hu1 h1

end CFSG.Quasithin.Vol2.Ch10.SecD
