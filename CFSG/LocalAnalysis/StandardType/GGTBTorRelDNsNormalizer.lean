module

public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenDefs
public import CFSG.ClassicalGroups.Orthogonal.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType

namespace RelDNs

open Module QuadraticMap CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.ClassicalGroups.Orthogonal

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p k : ℕ} {U : Fin k → Submodule F V}
  {e : Fin k → ↥(orthDerived Q)} {E : Subgroup ↥(orthDerived Q)} {u : Fin k → V} {c t : F}

private theorem frame_u_ne_zero (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    u a ≠ 0 := by
  intro h0
  have h1 := hF.quad_eq a
  rw [h0, map_zero] at h1
  exact hF.c_ne_zero h1.symm

private theorem frame_u_linearIndependent (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (a : Fin k) : LinearIndependent F ![u a, (e a : V ≃ₗ[F] V) (u a)] := by
  rw [LinearIndependent.pair_iff]
  intro x y hxy
  have hxyV : x • u a + y • (e a : V ≃ₗ[F] V) (u a) = 0 := hxy
  have htc : t * c ≠ 0 := mul_ne_zero hF.t_ne_zero hF.c_ne_zero
  have hpolar := congrArg (fun z => polar Q (u a) z) hxyV
  rw [polar_zero_right, polar_add_right, polar_smul_right, polar_smul_right,
    hF.polar_eq a, polar_self_eq_two_mul, hF.quad_eq a, CharTwo.two_eq_zero,
    zero_mul, smul_zero, zero_add, smul_eq_mul, mul_eq_zero] at hpolar
  have hy : y = 0 := (hpolar.resolve_right htc)
  subst hy
  simp only [zero_smul, add_zero] at hxyV
  exact ⟨(smul_eq_zero.mp hxyV).resolve_right (frame_u_ne_zero hF a), rfl⟩

private theorem frame_span (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    Submodule.span F ({u a, (e a : V ≃ₗ[F] V) (u a)} : Set V) = U a := by
  have hli := frame_u_linearIndependent hF a
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · refine Submodule.span_le.mpr ?_
    intro x hx
    rcases hx with rfl | rfl
    · exact hF.mem a
    · exact (hF.toIsPlaneFrame.maps_to a) _ (hF.mem a)
  · rw [show ({u a, (e a : V ≃ₗ[F] V) (u a)} : Set V) =
        Set.range ![u a, (e a : V ≃ₗ[F] V) (u a)] by
      ext x
      simp [or_comm]]
    rw [finrank_span_eq_card hli, Fintype.card_fin]
    exact (hF.toIsPlaneFrame.toIsPlaneSystem.finrank_eq a).symm

private theorem rot_apply_add_self (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (a : Fin k) {x : V} (hx : x ∈ U a) :
    (e a : V ≃ₗ[F] V) ((e a : V ≃ₗ[F] V) x) + t • (e a : V ≃ₗ[F] V) x + x = 0 := by
  let A : Module.End F V :=
    (e a : V ≃ₗ[F] V) * (e a : V ≃ₗ[F] V) + t • (e a : V ≃ₗ[F] V) + 1
  have hAu : A (u a) = 0 := by
    dsimp [A]
    rw [hF.rot a]
    calc t • (e a : V ≃ₗ[F] V) (u a) + u a + t • (e a : V ≃ₗ[F] V) (u a) + u a
        = (t • (e a : V ≃ₗ[F] V) (u a) + t • (e a : V ≃ₗ[F] V) (u a)) +
            (u a + u a) := by abel
      _ = 0 := by
          rw [← two_smul F (t • (e a : V ≃ₗ[F] V) (u a)), ← two_smul F (u a),
            CharTwo.two_eq_zero, zero_smul, zero_smul, add_zero]
  have hAeu : A ((e a : V ≃ₗ[F] V) (u a)) = 0 := by
    have h := congrArg (fun z => (e a : V ≃ₗ[F] V) z) hAu
    simpa [A, map_add, map_smul, add_assoc] using h
  have hAall : ∀ y ∈ U a, A y = 0 := by
    intro y hy
    rw [← frame_span hF a] at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        rcases hy with rfl | rfl
        · exact hAu
        · exact hAeu
    | zero => simp
    | add y z hy hz ihy ihz => rw [map_add, ihy, ihz, add_zero]
    | smul b y hy ihy => rw [map_smul, ihy, smul_zero]
  exact hAall x hx

private theorem plane_anisotropic (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (a : Fin k) {x : ↥(U a)} (hx : Q (x : V) = 0) : x = 0 := by
  by_contra hx0
  apply hF.toIsPlaneFrame.not_isPlusType a
  refine ⟨Submodule.span F ({x} : Set ↥(U a)), ?_, ?_⟩
  · rw [finrank_span_singleton hx0, hF.toIsPlaneFrame.toIsPlaneSystem.finrank_eq a]
  · intro y hy
    rw [Submodule.mem_span_singleton] at hy
    obtain ⟨b, rfl⟩ := hy
    change Q (b • (x : V)) = 0
    rw [map_smul_eq_sq, hx, mul_zero]

private theorem fixedSpace_conj {g f : V ≃ₗ[F] V} :
    fixedSpace (g * f * g⁻¹) = (fixedSpace f).map (g : V →ₗ[F] V) := by
  ext x
  simp only [mem_fixedSpace, Submodule.mem_map, LinearEquiv.coe_coe]
  constructor
  · intro hx
    refine ⟨g.symm x, ?_, by simp⟩
    have hx' : g (f (g.symm x)) = x := by
      simpa [LinearEquiv.mul_apply] using hx
    have := congrArg (fun z => g.symm z) hx'
    simpa using this
  · rintro ⟨y, hy, rfl⟩
    simp [hy]

private theorem fixedSpace_inf_sup_eq_bot {A B F0 : Submodule F V} {d : V ≃ₗ[F] V}
    (hAB : Disjoint A B) (hFA : F0 ⊓ A = ⊥) (hFB : F0 ⊓ B = ⊥)
    (hdA : ∀ x ∈ A, d x ∈ A) (hdB : ∀ x ∈ B, d x ∈ B)
    (hfreeA : ∀ x ∈ A, d x = x → x = 0) (hfreeB : ∀ x ∈ B, d x = x → x = 0)
    (hfix : F0 ≤ fixedSpace d) : F0 ⊓ (A ⊔ B) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨hxF, hxAB⟩ := hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hxAB
  have hdx : d (a + b) = a + b := mem_fixedSpace.mp (hfix hxF)
  have hsum : d a + d b = a + b := by simpa [map_add] using hdx
  have hzero : (d a - a) + (d b - b) = 0 := by
    have h : (d a - a) + (d b - b) = (d a + d b) - (a + b) := by abel
    rw [h, hsum, sub_self]
  have hdaA : d a - a ∈ A := A.sub_mem (hdA a ha) ha
  have hdbB : d b - b ∈ B := B.sub_mem (hdB b hb) hb
  have hdaB : d a - a ∈ B := by
    have h : d a - a = -(d b - b) := by
      rw [eq_neg_iff_add_eq_zero]
      exact hzero
    rw [h]
    exact B.neg_mem hdbB
  have hda0 : d a - a = 0 := by
    have hmem : d a - a ∈ A ⊓ B := ⟨hdaA, hdaB⟩
    rwa [hAB.eq_bot] at hmem
  have hdbA : d b - b ∈ A := by
    have h : d b - b = -(d a - a) := by
      rw [eq_neg_iff_add_eq_zero]
      rw [add_comm]
      exact hzero
    rw [h, hda0, neg_zero]
    exact Submodule.zero_mem _
  have hdb0 : d b - b = 0 := by
    have hmem : d b - b ∈ A ⊓ B := ⟨hdbA, hdbB⟩
    rwa [hAB.eq_bot] at hmem
  have ha0 : a = 0 := hfreeA a ha (sub_eq_zero.mp hda0)
  have hb0 : b = 0 := hfreeB b hb (sub_eq_zero.mp hdb0)
  rw [ha0, hb0, add_zero]

private theorem fixedSpace_disjoint_iSup (hF : IsPlaneSystem Q U) {d : V ≃ₗ[F] V}
    {s : Finset (Fin k)} (hmaps : ∀ j, ∀ x ∈ U j, d x ∈ U j)
    (hfree : ∀ j ∈ s, ∀ x ∈ U j, d x = x → x = 0) :
    Disjoint (fixedSpace d) (⨆ j ∈ s, U j) := by
  induction s using Finset.induction_on with
  | empty =>
      have hbot : (⨆ j ∈ (∅ : Finset (Fin k)), U j) = ⊥ := by simp
      rw [hbot]
      exact disjoint_bot_right
  | insert a s ha ih =>
      rw [Finset.iSup_insert]
      have hFA : Disjoint (fixedSpace d) (U a) := by
        rw [disjoint_iff_inf_le]
        intro x hx
        obtain ⟨hxF, hxA⟩ := hx
        have hdx : d x = x := mem_fixedSpace.mp hxF
        have hx0 : x = 0 := hfree a (Finset.mem_insert_self a s) x hxA hdx
        rw [hx0]
        exact Submodule.zero_mem _
      have hFB : Disjoint (fixedSpace d) (⨆ j ∈ s, U j) :=
        ih (fun j hj => hfree j (Finset.mem_insert_of_mem hj))
      have hAB : Disjoint (U a) (⨆ j ∈ s, U j) := hF.disjoint_biSup ha
      have hfreeB : ∀ x ∈ (⨆ j ∈ s, U j), d x = x → x = 0 := by
        intro x hx hdx
        have hxF : x ∈ fixedSpace d := mem_fixedSpace.mpr hdx
        have hxbot : x ∈ fixedSpace d ⊓ (⨆ j ∈ s, U j) := ⟨hxF, hx⟩
        rw [hFB.eq_bot] at hxbot
        simpa using hxbot
      have hdB : ∀ x ∈ (⨆ j ∈ s, U j), d x ∈ (⨆ j ∈ s, U j) := by
        have hmap : (⨆ j ∈ s, U j).map (d : V →ₗ[F] V) ≤ (⨆ j ∈ s, U j) := by
          rw [Submodule.map_iSup]
          refine iSup_le ?_
          intro j
          rw [Submodule.map_iSup]
          refine iSup_le ?_
          intro hj
          intro x hx
          rw [Submodule.mem_map] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          exact Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hj (hmaps j y hy))
        intro x hx
        have hxmap : d x ∈ (⨆ j ∈ s, U j).map (d : V →ₗ[F] V) := by
          rw [Submodule.mem_map]
          exact ⟨x, hx, rfl⟩
        exact hmap hxmap
      rw [disjoint_iff_inf_le]
      rw [fixedSpace_inf_sup_eq_bot hAB hFA.eq_bot hFB.eq_bot
        (fun x hx => hmaps a x hx) hdB
        (fun x hx => hfree a (Finset.mem_insert_self a s) x hx) hfreeB
        (le_refl _)]

private theorem exists_unique_plane_of_fixedSpace
    (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (hp : p.Prime) (hk : 0 < k)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {d : ↥(orthDerived Q)} (hd : d ∈ E) (hd1 : d ≠ 1)
    (hfix : Module.finrank F (fixedSpace (d : V ≃ₗ[F] V)) =
      Module.finrank F V - 2) :
    ∃ b : Fin k,
      (¬ ∀ x ∈ U b, (d : V ≃ₗ[F] V) x = x) ∧
      (∀ j, j ≠ b → ∀ x ∈ U j, (d : V ≃ₗ[F] V) x = x) ∧
      fixedSpace (d : V ≃ₗ[F] V) = polarPerp Q (U b) := by
  classical
  have hsys := hF.toIsPlaneFrame.toIsPlaneSystem
  let S : Finset (Fin k) :=
    Finset.univ.filter fun j => ¬ ∀ x ∈ U j, (d : V ≃ₗ[F] V) x = x
  let T : Finset (Fin k) := Finset.univ \ S
  let W : Submodule F V := polarPerp Q (⨆ j, U j)
  let Vsub : Submodule F V := ⨆ j ∈ T, U j
  have hS_mem : ∀ j, j ∈ S ↔ ¬ ∀ x ∈ U j, (d : V ≃ₗ[F] V) x = x := by
    intro j; simp [S]
  have hT_mem : ∀ j, j ∈ T ↔ j ∉ S := by
    intro j; simp [T]
  have hT_fix : ∀ j ∈ T, ∀ x ∈ U j, (d : V ≃ₗ[F] V) x = x := by
    intro j hj
    have hjn : j ∉ S := (hT_mem j).mp hj
    by_contra h
    exact hjn ((hS_mem j).mpr h)
  have hS_free : ∀ j ∈ S, ∀ x ∈ U j, (d : V ≃ₗ[F] V) x = x → x = 0 := by
    intro j hj x hx
    have hn := (hS_mem j).mp hj
    exact (hF.toIsPlaneFrame.apply_eq_or_eq_zero hp hd j).resolve_left hn x hx
  have pow_maps : ∀ (j : Fin k) (m : ℕ) (x : V), x ∈ U j →
      ((e j : V ≃ₗ[F] V) ^ m) x ∈ U j := by
    intro j m
    induction m with
    | zero => intro x hx; simpa using hx
    | succ m ih =>
        intro x hx
        rw [pow_succ', LinearEquiv.mul_apply]
        exact hF.toIsPlaneFrame.maps_to j _ (ih x hx)
  have hd_maps : ∀ j, ∀ x ∈ U j, (d : V ≃ₗ[F] V) x ∈ U j := by
    intro j x hx
    obtain ⟨m, hm⟩ := hF.toIsPlaneFrame.exists_pow_apply_eq hd j
    rw [hm x hx]
    exact pow_maps j m x hx
  have hW_fix : W ≤ fixedSpace (d : V ≃ₗ[F] V) := by
    intro x hx
    exact mem_fixedSpace.mpr (hF.toIsPlaneFrame.apply_eq_of_mem_polarPerp_iSup hd hx)
  have hsub_fix : Vsub ≤ fixedSpace (d : V ≃ₗ[F] V) := by
    refine iSup₂_le ?_
    intro j hj x hx
    exact mem_fixedSpace.mpr (hT_fix j hj x hx)
  have hA_le : Vsub ⊔ W ≤ fixedSpace (d : V ≃ₗ[F] V) :=
    sup_le hsub_fix hW_fix
  have hdisj : Disjoint Vsub W := by
    refine hsys.isCompl_iSup.disjoint.mono_left ?_
    exact iSup₂_le fun j _ => le_iSup U j
  have hfin_sub : Module.finrank F ↥Vsub = 2 * T.card :=
    hsys.finrank_biSup T
  have hsup_univ : (⨆ j ∈ (Finset.univ : Finset (Fin k)), U j) =
      (⨆ j : Fin k, U j : Submodule F V) := by simp
  have hfin_W : Module.finrank F W = Module.finrank F V - 2 * k := by
    calc Module.finrank F W
        = Module.finrank F V - Module.finrank F (⨆ j : Fin k, U j : Submodule F V) := by
          rw [show W = polarPerp Q (⨆ j, U j) from rfl, finrank_polarPerp hQ]
      _ = Module.finrank F V -
          Module.finrank F (⨆ j ∈ (Finset.univ : Finset (Fin k)), U j : Submodule F V) := by
          rw [hsup_univ]
      _ = Module.finrank F V - 2 * k := by
          rw [hsys.finrank_biSup Finset.univ]; simp
  have hfin_A : Module.finrank F ↥(Vsub ⊔ W) =
      2 * T.card + (Module.finrank F V - 2 * k) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq Vsub W
    rw [hdisj.eq_bot, finrank_bot, add_zero] at h
    rw [h, hfin_sub, hfin_W]
  let UsumS : Submodule F V := ⨆ j ∈ S, U j
  have hUsumS_fin : Module.finrank F ↥UsumS = 2 * S.card := hsys.finrank_biSup S
  have hdisjS : Disjoint (fixedSpace (d : V ≃ₗ[F] V)) UsumS :=
    fixedSpace_disjoint_iSup hsys hd_maps hS_free
  have h2k : 2 * k ≤ Module.finrank F V := by
    calc 2 * k = 2 * (Finset.univ : Finset (Fin k)).card := by simp
      _ = Module.finrank F (⨆ j ∈ (Finset.univ : Finset (Fin k)), U j : Submodule F V) :=
          (hsys.finrank_biSup Finset.univ).symm
      _ = Module.finrank F (⨆ j : Fin k, U j : Submodule F V) := by rw [hsup_univ]
      _ ≤ Module.finrank F V := Submodule.finrank_le _
  have hSle : S.card ≤ 1 := by
    have h := Submodule.finrank_add_finrank_le_of_disjoint hdisjS
    rw [hUsumS_fin, hfix] at h
    omega
  have hSnonempty : S.Nonempty := by
    by_contra h
    have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hTuniv : T = Finset.univ := by
      ext j; simp [T, hSempty]
    have htop : Vsub ⊔ W = ⊤ := by
      have hsub : (⨆ j ∈ (Finset.univ : Finset (Fin k)), U j) = ⨆ j, U j := by simp
      dsimp only [Vsub]
      rw [hTuniv, hsub]
      exact hsys.isCompl_iSup.sup_eq_top
    have hfix_all : fixedSpace (d : V ≃ₗ[F] V) = ⊤ :=
      eq_top_iff.mpr (by simpa [htop] using hA_le)
    have hd_eq_one : d = 1 := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      have hx : x ∈ fixedSpace (d : V ≃ₗ[F] V) := by
        rw [hfix_all]; exact Submodule.mem_top
      simpa using mem_fixedSpace.mp hx
    exact hd1 hd_eq_one
  have hScard : S.card = 1 := le_antisymm hSle (Finset.card_pos.mpr hSnonempty)
  obtain ⟨b, hbS⟩ := hSnonempty
  obtain ⟨b', hb'⟩ := Finset.card_eq_one.mp hScard
  have hbb' : b = b' := by
    have : b ∈ ({b'} : Finset (Fin k)) := by rw [← hb']; exact hbS
    simpa using this
  subst hbb'
  have hSsing : S = {b} := hb'
  have hbnontriv : ¬ ∀ x ∈ U b, (d : V ≃ₗ[F] V) x = x :=
    (hS_mem b).mp (by rw [hSsing]; simp)
  have hbother : ∀ j, j ≠ b → ∀ x ∈ U j, (d : V ≃ₗ[F] V) x = x := by
    intro j hj x hx
    have hjn : j ∉ S := by rw [hSsing]; simp [hj]
    exact hT_fix j ((hT_mem j).mpr hjn) x hx
  refine ⟨b, hbnontriv, hbother, ?_⟩
  have hTerase : T = Finset.univ.erase b := by
    ext j
    simp [T, hSsing, Finset.mem_erase, eq_comm]
  have hsub_perp : Vsub ≤ polarPerp Q (U b) := by
    refine iSup₂_le ?_
    intro j hj x hx
    rw [mem_polarPerp_iff]
    intro y hy
    rw [hTerase] at hj
    have hjb : j ≠ b := (Finset.mem_erase.mp hj).1
    exact hF.toIsPlaneFrame.toIsPlaneSystem.perp b j (fun h => hjb h.symm) y hy x hx
  have hW_perp : W ≤ polarPerp Q (U b) := by
    intro x hx
    rw [mem_polarPerp_iff]
    intro y hy
    exact mem_polarPerp_iff.mp hx y (le_iSup U b hy)
  have hA_perp : Vsub ⊔ W ≤ polarPerp Q (U b) :=
    sup_le hsub_perp hW_perp
  have hTcard : T.card = k - 1 := by
    have hTS : T.card + S.card = k := by
      have := Finset.card_sdiff_add_card_eq_card (s := S) (t := Finset.univ)
        (Finset.subset_univ S)
      simpa [T, Finset.card_univ, Fintype.card_fin] using this
    have hS1 : S.card = 1 := by rw [hSsing]; simp
    omega
  have hA_fin : Module.finrank F ↥(Vsub ⊔ W) =
      Module.finrank F (polarPerp Q (U b)) := by
    rw [hfin_A, hTcard, finrank_polarPerp hQ,
      hF.toIsPlaneFrame.toIsPlaneSystem.finrank_eq b]
    omega
  have hA_eq : Vsub ⊔ W = polarPerp Q (U b) :=
    Submodule.eq_of_le_of_finrank_eq hA_perp hA_fin
  have hperp_le : polarPerp Q (U b) ≤ fixedSpace (d : V ≃ₗ[F] V) := by
    rw [← hA_eq]; exact hA_le
  refine (Submodule.eq_of_le_of_finrank_eq hperp_le ?_).symm
  rw [finrank_polarPerp hQ, hF.toIsPlaneFrame.toIsPlaneSystem.finrank_eq b, hfix]

theorem conj_e_of_mem_normalizer {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type}
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {k : ℕ} {U : Fin k → Submodule F V} {e : Fin k → ↥(CFSG.RankThree.Classical2.orthDerived Q)}
    {E : Subgroup ↥(CFSG.RankThree.Classical2.orthDerived Q)} {u : Fin k → V} {c t : F}
    (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    {g : ↥(CFSG.RankThree.Classical2.orthDerived Q)}
    (hg : g ∈ Subgroup.normalizer (E : Set ↥(CFSG.RankThree.Classical2.orthDerived Q))) :
    ∃ (π : Equiv.Perm (Fin k)) (ε : Fin k → ℤ),
      (∀ a, ε a = 1 ∨ ε a = -1) ∧ ∀ a, g * e a * g⁻¹ = e (π a) ^ ε a := by
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (V ≃ₗ[F] V) :=
    Finite.of_injective (fun e : V ≃ₗ[F] V => (e : V → V))
      fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  haveI : Finite ↥(orthDerived Q) := Subtype.finite
  by_cases hk0 : k = 0
  · subst hk0
    refine ⟨Equiv.refl (Fin 0), fun a => Fin.elim0 a, ?_, ?_⟩
    · intro a; exact Fin.elim0 a
    · intro a; exact Fin.elim0 a
  let gL : V ≃ₗ[F] V := (g : V ≃ₗ[F] V)
  let eL : Fin k → V ≃ₗ[F] V := fun a => (e a : V ≃ₗ[F] V)
  let d : Fin k → ↥(orthDerived Q) := fun a => g * e a * g⁻¹
  have memO : ∀ x : ↥(orthDerived Q),
      (x : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    intro x
    let O : Subgroup (V ≃ₗ[F] V) := TauCeti.QuadraticMap.orthogonalGroup Q
    have hle : ⁅O, O⁆ ≤ O := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      exact O.mul_mem (O.mul_mem (O.mul_mem ha hb) (O.inv_mem ha)) (O.inv_mem hb)
    exact hle x.2
  have hgO : gL ∈ TauCeti.QuadraticMap.orthogonalGroup Q := memO g
  have hd_mem : ∀ a, d a ∈ E := by
    intro a
    exact (Subgroup.mem_normalizer_iff.mp hg (e a)).mp (hF.toIsPlaneFrame.mem a)
  have hd_ne_one : ∀ a, d a ≠ 1 := by
    intro a h1
    have h2 : e a = 1 := by
      have := congrArg (fun z => g⁻¹ * z * g) h1
      simpa [d, mul_assoc] using this
    have hp1 : p = 1 := by
      rw [← hF.toIsPlaneFrame.orderOf_eq a, h2, orderOf_one]
    exact hp.ne_one hp1
  have hfixConj : ∀ a, fixedSpace (d a : V ≃ₗ[F] V) =
      (fixedSpace (e a : V ≃ₗ[F] V)).map (gL : V →ₗ[F] V) := by
    intro a
    have hcoe : (d a : V ≃ₗ[F] V) = gL * (e a : V ≃ₗ[F] V) * gL⁻¹ := by
      simp [d, gL]
    rw [hcoe]
    exact fixedSpace_conj
  have hfixdim : ∀ a, Module.finrank F (fixedSpace (d a : V ≃ₗ[F] V)) =
      Module.finrank F V - 2 := by
    intro a
    rw [hfixConj a, LinearEquiv.finrank_map_eq,
      hF.toIsPlaneFrame.fixedSpace_eq_polarPerp a, finrank_polarPerp hQ,
      hF.toIsPlaneFrame.toIsPlaneSystem.finrank_eq a]
  have hex_b : ∀ a, ∃ b : Fin k,
      (¬ ∀ x ∈ U b, (d a : V ≃ₗ[F] V) x = x) ∧
      (∀ j, j ≠ b → ∀ x ∈ U j, (d a : V ≃ₗ[F] V) x = x) ∧
      fixedSpace (d a : V ≃ₗ[F] V) = polarPerp Q (U b) :=
    fun a => exists_unique_plane_of_fixedSpace hF hp (Nat.pos_of_ne_zero hk0) hQ (hd_mem a) (hd_ne_one a) (hfixdim a)
  choose b hb using hex_b
  let W : Submodule F V := polarPerp Q (⨆ j, U j)
  have hglobal {u v : V ≃ₗ[F] V}
      (hU : ∀ j, ∀ x ∈ U j, u x = v x) (hW : ∀ x ∈ W, u x = v x) : u = v := by
    have h1 : u⁻¹ * v = 1 := by
      refine hF.toIsPlaneFrame.toIsPlaneSystem.eq_one_of_apply_eq ?_ ?_
      · intro j x hx
        rw [LinearEquiv.mul_apply, ← hU j x hx]
        exact u.symm_apply_apply x
      · intro x hx
        rw [LinearEquiv.mul_apply, ← hW x hx]
        exact u.symm_apply_apply x
    exact inv_mul_eq_one.mp h1
  have hsingle : ∀ a, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ d a = e (b a) ^ ε := by
    intro a
    let bb : Fin k := b a
    let cEnd : Module.End F ↥(U bb) :=
      (((e bb : V ≃ₗ[F] V) : V →ₗ[F] V)).restrict (p := U bb) (q := U bb)
        (hF.toIsPlaneFrame.maps_to bb)
    obtain ⟨n, hn⟩ := hF.toIsPlaneFrame.exists_pow_apply_eq (hd_mem a) bb
    let dE : Module.End F ↥(U bb) := cEnd ^ n
    let cInv : Module.End F ↥(U bb) := cEnd + t • 1
    have hc_pow_apply : ∀ (m : ℕ) (y : ↥(U bb)),
        (((cEnd ^ m) y : ↥(U bb)) : V) = ((e bb : V ≃ₗ[F] V) ^ m) (y : V) := by
      intro m
      induction m with
      | zero => intro y; simp
      | succ m ih =>
          intro y
          rw [pow_succ', Module.End.mul_apply, pow_succ', LinearEquiv.mul_apply]
          show (e bb : V ≃ₗ[F] V) (((cEnd ^ m) y : ↥(U bb)) : V) =
            (e bb : V ≃ₗ[F] V) (((e bb : V ≃ₗ[F] V) ^ m) (y : V))
          rw [ih y]
    have hdE_apply : ∀ y : ↥(U bb),
        ((dE y : ↥(U bb)) : V) = (d a : V ≃ₗ[F] V) (y : V) := by
      intro y
      calc ((dE y : ↥(U bb)) : V) = (((cEnd ^ n) y : ↥(U bb)) : V) := rfl
        _ = ((e bb : V ≃ₗ[F] V) ^ n) (y : V) := hc_pow_apply n y
        _ = (d a : V ≃ₗ[F] V) (y : V) := (hn (y : V) y.2).symm
    have hc_rot : cEnd * cEnd + t • cEnd + 1 = 0 := by
      ext y
      simpa [cEnd, Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
        Module.End.one_apply] using rot_apply_add_self hF bb y.2
    have hnegEnd : -(1 : Module.End F ↥(U bb)) = 1 := by
      have h2 : (2 : F) • (1 : Module.End F ↥(U bb)) = 0 := by
        rw [CharTwo.two_eq_zero, zero_smul]
      rw [two_smul] at h2
      exact neg_eq_of_add_eq_zero_right h2
    have hrel : cEnd * cEnd + t • cEnd = 1 := by
      have h := eq_neg_of_add_eq_zero_right hc_rot
      have h' : -(1 : Module.End F ↥(U bb)) = cEnd * cEnd + t • cEnd := by
        rw [h, neg_neg]
      rw [hnegEnd] at h'
      exact h'.symm
    have hc_mul_cInv : cEnd * cInv = 1 := by
      calc cEnd * cInv = cEnd * (cEnd + t • 1) := rfl
        _ = cEnd * cEnd + t • cEnd := by
            rw [mul_add, Algebra.mul_smul_comm, mul_one]
        _ = 1 := hrel
    have hc_cInv_apply : ∀ y, cEnd (cInv y) = y := by
      intro y
      rw [← Module.End.mul_apply, hc_mul_cInv, Module.End.one_apply]
    have hc_add_cInv : cEnd + cInv = t • 1 := by
      dsimp [cInv]
      rw [← add_assoc, ← two_smul F cEnd, CharTwo.two_eq_zero, zero_smul, zero_add]
    have hcInv_add_c_apply : ∀ y, cInv y + cEnd y = t • y := by
      have hsum : cInv + cEnd = t • 1 := by rw [add_comm, hc_add_cInv]
      intro y
      have := congrArg (fun f : Module.End F ↥(U bb) => f y) hsum
      simpa using this
    have hc_dE_apply : ∀ y, cEnd (dE y) = dE (cEnd y) := by
      intro y
      dsimp [dE]
      rw [← Module.End.mul_apply, ← Module.End.mul_apply]
      have hcomm : cEnd * cEnd ^ n = cEnd ^ n * cEnd := by
        rw [← pow_succ', ← pow_succ, Nat.add_comm]
      rw [hcomm]
    have hcInv_dE_apply : ∀ y, cInv (dE y) = dE (cInv y) := by
      intro y
      calc cInv (dE y) = cEnd (dE y) + t • dE y := by simp [cInv]
        _ = dE (cEnd y) + dE (t • y) := by rw [hc_dE_apply, map_smul]
        _ = dE (cEnd y + t • y) := by rw [map_add]
        _ = dE (cInv y) := by simp [cInv]
    have hFix_d_eq : fixedSpace (d a : V ≃ₗ[F] V) = polarPerp Q (U bb) := (hb a).2.2
    have hmap_perp : (polarPerp Q (U a)).map (gL : V →ₗ[F] V) = polarPerp Q (U bb) := by
      rw [← hF.toIsPlaneFrame.fixedSpace_eq_polarPerp a, ← hfixConj a, hFix_d_eq]
    have hdouble : U bb = polarPerp Q (polarPerp Q (U bb)) := by
      simpa [polarPerp] using
        (LinearMap.BilinForm.orthogonal_orthogonal hQ (isRefl_polarBilin Q) (U bb)).symm
    have hgUa : (U a).map (gL : V →ₗ[F] V) = U bb := by
      refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
      · intro x hx
        rw [Submodule.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        rw [hdouble, mem_polarPerp_iff]
        intro z hz
        have hzmap : z ∈ (polarPerp Q (U a)).map (gL : V →ₗ[F] V) := by
          rw [hmap_perp]; exact hz
        rw [Submodule.mem_map] at hzmap
        obtain ⟨w, hw, rfl⟩ := hzmap
        change polar Q (gL w) (gL y) = 0
        rw [polar_map_of_mem hgO w y, polar_comm Q w y]
        exact mem_polarPerp_iff.mp hw y hy
      · rw [LinearEquiv.finrank_map_eq, hF.toIsPlaneFrame.toIsPlaneSystem.finrank_eq a,
          hF.toIsPlaneFrame.toIsPlaneSystem.finrank_eq bb]
    have hrot_d : ∀ y ∈ U bb,
        (d a : V ≃ₗ[F] V) ((d a : V ≃ₗ[F] V) y) + t • (d a : V ≃ₗ[F] V) y + y = 0 := by
      intro y hy
      have hy' : y ∈ (U a).map (gL : V →ₗ[F] V) := by rw [hgUa]; exact hy
      rw [Submodule.mem_map] at hy'
      obtain ⟨x, hx, rfl⟩ := hy'
      have hd_apply : ∀ z : V,
          (d a : V ≃ₗ[F] V) (gL z) = gL ((e a : V ≃ₗ[F] V) z) := by
        intro z
        simp [d, gL, mul_assoc]
      have hd1 : (d a : V ≃ₗ[F] V) ((d a : V ≃ₗ[F] V) (gL x)) =
          gL ((e a : V ≃ₗ[F] V) ((e a : V ≃ₗ[F] V) x)) := by
        rw [hd_apply x]
        exact hd_apply ((e a : V ≃ₗ[F] V) x)
      have hd2 : (d a : V ≃ₗ[F] V) (gL x) = gL ((e a : V ≃ₗ[F] V) x) := hd_apply x
      change (d a : V ≃ₗ[F] V) ((d a : V ≃ₗ[F] V) (gL x)) +
        t • (d a : V ≃ₗ[F] V) (gL x) + gL x = 0
      rw [hd1, hd2]
      calc gL ((e a : V ≃ₗ[F] V) ((e a : V ≃ₗ[F] V) x)) +
            t • gL ((e a : V ≃ₗ[F] V) x) + gL x
          = gL ((e a : V ≃ₗ[F] V) ((e a : V ≃ₗ[F] V) x) +
              t • (e a : V ≃ₗ[F] V) x + x) := by
            rw [map_add, map_add, map_smul]
        _ = 0 := by rw [rot_apply_add_self hF a hx, map_zero]
    have hdE_rot : ∀ y : ↥(U bb), dE (dE y) + t • dE y + y = 0 := by
      intro y
      apply Subtype.ext
      change ((dE (dE y) : ↥(U bb)) : V) + t • ((dE y : ↥(U bb)) : V) + (y : V) = 0
      rw [hdE_apply (dE y), hdE_apply y]
      exact hrot_d (y : V) y.2
    have hnegVec : ∀ z : ↥(U bb), -z = z := by
      intro z
      have h2 : (2 : F) • z = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
      rw [two_smul] at h2
      exact neg_eq_of_add_eq_zero_right h2
    let A : Module.End F ↥(U bb) := dE + cEnd
    let B : Module.End F ↥(U bb) := dE + cInv
    have hAB : ∀ y : ↥(U bb), A (B y) = 0 := by
      intro y
      calc A (B y) = dE (dE y) + dE (cInv y) + cEnd (dE y) + cEnd (cInv y) := by
            simp only [A, B, LinearMap.add_apply, map_add]
            abel
        _ = dE (dE y) + dE (cInv y) + dE (cEnd y) + y := by
            rw [hc_dE_apply y, hc_cInv_apply y]
        _ = dE (dE y) + (dE (cInv y) + dE (cEnd y)) + y := by abel
        _ = dE (dE y) + dE (cInv y + cEnd y) + y := by rw [← map_add]
        _ = dE (dE y) + dE (t • y) + y := by rw [hcInv_add_c_apply y]
        _ = dE (dE y) + t • dE y + y := by
            rw [show dE (t • y) = t • dE y from map_smul dE t y]
        _ = 0 := hdE_rot y
    have hAcomm_c : ∀ y : ↥(U bb), A (cEnd y) = cEnd (A y) := by
      intro y
      calc A (cEnd y) = dE (cEnd y) + cEnd (cEnd y) := by simp [A]
        _ = cEnd (dE y) + cEnd (cEnd y) := by rw [← hc_dE_apply y]
        _ = cEnd (dE y + cEnd y) := by rw [map_add]
        _ = cEnd (A y) := by simp [A]
    have hA_or_B : A = 0 ∨ B = 0 := by
      by_cases hA0 : A = 0
      · exact Or.inl hA0
      · right
        by_contra hB0
        let K : Submodule F ↥(U bb) := LinearMap.ker A
        have hKbot : K ≠ ⊥ := by
          intro hbot
          apply hB0
          apply LinearMap.ext
          intro y
          have hBy : B y = 0 := by
            have hAy : A (B y) = 0 := hAB y
            have hmem : B y ∈ K := hAy
            rw [hbot] at hmem
            simpa using hmem
          exact hBy
        have hKtop : K ≠ ⊤ := by
          intro htop
          apply hA0
          apply LinearMap.ext
          intro y
          have hy : y ∈ K := by rw [htop]; exact Submodule.mem_top
          exact hy
        have hKpos : 1 ≤ Module.finrank F K := by
          obtain ⟨x, hxK, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hKbot
          have hspanle : Submodule.span F {x} ≤ K := by
            rw [Submodule.span_le]
            intro y hy
            rw [Set.mem_singleton_iff] at hy
            subst hy
            exact hxK
          calc 1 = Module.finrank F (Submodule.span F {x}) :=
                (finrank_span_singleton hx0).symm
            _ ≤ Module.finrank F K := Submodule.finrank_mono hspanle
        have hKlt : Module.finrank F K < 2 := by
          have := Submodule.finrank_lt hKtop
          rwa [hF.toIsPlaneFrame.toIsPlaneSystem.finrank_eq bb] at this
        have hKfin : Module.finrank F K = 1 := by omega
        obtain ⟨x, hxK, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hKbot
        have hspanK : Submodule.span F {x} = K := by
          refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
          · rw [Submodule.span_le]
            intro y hy
            rw [Set.mem_singleton_iff] at hy
            subst hy
            exact hxK
          · rw [finrank_span_singleton hx0, hKfin]
        have hKspan : K = Submodule.span F {x} := hspanK.symm
        have hAx : A x = 0 := hxK
        have hcxK : cEnd x ∈ K := by
          change A (cEnd x) = 0
          rw [hAcomm_c x, hAx, map_zero]
        rw [hKspan] at hcxK
        obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp hcxK
        have hQx : Q (x : V) ≠ 0 := fun h => hx0 (plane_anisotropic hF bb h)
        have hiso : Q ((cEnd x : ↥(U bb)) : V) = Q (x : V) := by
          have hcx : ((cEnd x : ↥(U bb)) : V) = (e bb : V ≃ₗ[F] V) (x : V) := rfl
          rw [hcx, map_of_mem (memO (e bb))]
        have hlamQ : lam ^ 2 * Q (x : V) = Q (x : V) := by
          have h := congrArg (fun z : ↥(U bb) => Q (z : V)) hlam
          simpa [Submodule.coe_smul, map_smul_eq_sq, hiso] using h
        have hsq : lam ^ 2 = 1 := by
          have h2 : lam ^ 2 * Q (x : V) = 1 * Q (x : V) := by simpa using hlamQ
          exact mul_right_cancel₀ hQx h2
        have hlam1 : lam = 1 := by
          rcases (sq_eq_one_iff.mp hsq) with h | h
          · exact h
          · rwa [CharTwo.neg_eq] at h
        have hcx : cEnd x = x := by rw [← hlam, hlam1, one_smul]
        have hcxV : (e bb : V ≃ₗ[F] V) (x : V) = (x : V) := by
          simpa [cEnd] using congrArg (fun z : ↥(U bb) => (z : V)) hcx
        have hxV : (x : V) = 0 :=
          hF.toIsPlaneFrame.eq_zero_of_apply_eq bb (x : V) x.2 hcxV
        exact hx0 (Subtype.ext hxV)
    rcases hA_or_B with hA0 | hB0
    · have hdE_eq_c : dE = cEnd := by
        apply LinearMap.ext
        intro y
        have h0 : dE y + cEnd y = 0 := by
          have := congrArg (fun f : Module.End F ↥(U bb) => f y) hA0
          simpa [A] using this
        rw [add_comm] at h0
        have hneg : dE y = -(cEnd y) := eq_neg_of_add_eq_zero_right h0
        rw [hneg, hnegVec]
      have hUeq : ∀ j, ∀ x ∈ U j, (d a : V ≃ₗ[F] V) x = (e bb : V ≃ₗ[F] V) x := by
        intro j x hx
        by_cases hjb : j = bb
        · subst hjb
          have hd := hdE_apply ⟨x, hx⟩
          calc (d a : V ≃ₗ[F] V) x = ((dE ⟨x, hx⟩ : ↥(U bb)) : V) := hd.symm
            _ = ((cEnd ⟨x, hx⟩ : ↥(U bb)) : V) := by rw [hdE_eq_c]
            _ = (e bb : V ≃ₗ[F] V) x := rfl
        · have hdj := (hb a).2.1 j hjb x hx
          have hej : (e bb : V ≃ₗ[F] V) x = x := by
            have hxperp : x ∈ polarPerp Q (U bb) := mem_polarPerp_iff.mpr fun y hy => by
              rw [polar_comm]
              exact hF.toIsPlaneFrame.toIsPlaneSystem.perp j bb hjb x hx y hy
            exact hF.toIsPlaneFrame.apply_of_perp bb x hxperp
          rw [hdj, hej]
      have hWeq : ∀ x ∈ W, (d a : V ≃ₗ[F] V) x = (e bb : V ≃ₗ[F] V) x := by
        intro x hx
        have hdx := hF.toIsPlaneFrame.apply_eq_of_mem_polarPerp_iSup (hd_mem a) hx
        have hex := hF.toIsPlaneFrame.apply_eq_of_mem_polarPerp_iSup
          (hF.toIsPlaneFrame.mem bb) hx
        rw [hdx, hex]
      have hlin := hglobal hUeq hWeq
      refine ⟨1, Or.inl rfl, ?_⟩
      rw [zpow_one]
      exact Subtype.ext hlin
    · have hdE_eq_cInv : dE = cInv := by
        apply LinearMap.ext
        intro y
        have h0 : dE y + cInv y = 0 := by
          have := congrArg (fun f : Module.End F ↥(U bb) => f y) hB0
          simpa [B] using this
        rw [add_comm] at h0
        have hneg : dE y = -(cInv y) := eq_neg_of_add_eq_zero_right h0
        rw [hneg, hnegVec]
      have hebinv_apply : ∀ x : ↥(U bb),
          (e bb : V ≃ₗ[F] V)⁻¹ (x : V) = (cInv x : V) := by
        intro x
        have h := hc_cInv_apply x
        have hV : (e bb : V ≃ₗ[F] V) ((cInv x : ↥(U bb)) : V) = (x : V) := by
          simpa [cEnd] using congrArg (fun z : ↥(U bb) => (z : V)) h
        have hinv := congrArg (fun z => (e bb : V ≃ₗ[F] V)⁻¹ z) hV
        simpa using hinv.symm
      have hUeq : ∀ j, ∀ x ∈ U j,
          (d a : V ≃ₗ[F] V) x = ((e bb : V ≃ₗ[F] V)⁻¹) x := by
        intro j x hx
        by_cases hjb : j = bb
        · subst hjb
          have hd := hdE_apply ⟨x, hx⟩
          have hinv := hebinv_apply ⟨x, hx⟩
          calc (d a : V ≃ₗ[F] V) x = ((dE ⟨x, hx⟩ : ↥(U bb)) : V) := hd.symm
            _ = ((cInv ⟨x, hx⟩ : ↥(U bb)) : V) := by rw [hdE_eq_cInv]
            _ = ((e bb : V ≃ₗ[F] V)⁻¹) x := hinv.symm
        · have hdj := (hb a).2.1 j hjb x hx
          have hej : ((e bb : V ≃ₗ[F] V)⁻¹) x = x := by
            have hxperp : x ∈ polarPerp Q (U bb) := mem_polarPerp_iff.mpr fun y hy => by
              rw [polar_comm]
              exact hF.toIsPlaneFrame.toIsPlaneSystem.perp j bb hjb x hx y hy
            have hfix := hF.toIsPlaneFrame.apply_of_perp bb x hxperp
            have := congrArg (fun z => (e bb : V ≃ₗ[F] V)⁻¹ z) hfix
            simpa using this.symm
          rw [hdj, hej]
      have hWeq : ∀ x ∈ W, (d a : V ≃ₗ[F] V) x = ((e bb : V ≃ₗ[F] V)⁻¹) x := by
        intro x hx
        have hdx := hF.toIsPlaneFrame.apply_eq_of_mem_polarPerp_iSup (hd_mem a) hx
        have hex := hF.toIsPlaneFrame.apply_eq_of_mem_polarPerp_iSup
          (hF.toIsPlaneFrame.mem bb) hx
        have hinvx : ((e bb : V ≃ₗ[F] V)⁻¹) x = x := by
          have := congrArg (fun z => (e bb : V ≃ₗ[F] V)⁻¹ z) hex
          simpa using this.symm
        rw [hdx, hinvx]
      have hlin := hglobal hUeq hWeq
      refine ⟨-1, Or.inr rfl, ?_⟩
      rw [zpow_neg_one]
      exact Subtype.ext hlin
  choose ε hε using hsingle
  have hb_inj : Function.Injective b := by
    intro a a' hbb
    by_contra hne
    have hconj' := (hε a').2
    have hb_zp : e (b a) ∈ Subgroup.zpowers (g * e a' * g⁻¹) := by
      rcases (hε a').1 with h | h
      · have hconj1 : g * e a' * g⁻¹ = e (b a) := by
          simpa [h, hbb] using hconj'
        rw [← hconj1]
        exact Subgroup.mem_zpowers _
      · have hconj1 : g * e a' * g⁻¹ = (e (b a))⁻¹ := by
          simpa [h, hbb] using hconj'
        have hinv : (g * e a' * g⁻¹)⁻¹ = e (b a) := by
          rw [hconj1]; simp
        rw [← hinv]
        exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
    have hd_zp : g * e a * g⁻¹ ∈ Subgroup.zpowers (g * e a' * g⁻¹) := by
      change d a ∈ Subgroup.zpowers (g * e a' * g⁻¹)
      rw [(hε a).2]
      exact Subgroup.zpow_mem (K := Subgroup.zpowers (g * e a' * g⁻¹)) hb_zp (ε a)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hd_zp
    have hea_zp : e a ∈ Subgroup.zpowers (e a') := by
      refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
      have hthis := congrArg (fun z => g⁻¹ * z * g) hm
      rw [conj_zpow] at hthis
      simpa [mul_assoc] using hthis
    have hle : Subgroup.zpowers (e a) ≤ Subgroup.zpowers (e a') :=
      Subgroup.zpowers_le.mpr hea_zp
    have hcard : Nat.card (Subgroup.zpowers (e a')) ≤ Nat.card (Subgroup.zpowers (e a)) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, hF.toIsPlaneFrame.orderOf_eq a,
        hF.toIsPlaneFrame.orderOf_eq a']
    have heq : Subgroup.zpowers (e a) = Subgroup.zpowers (e a') :=
      Subgroup.eq_of_le_of_card_ge hle hcard
    have hea'_zp : e a' ∈ Subgroup.zpowers (e a) := by
      rw [heq]; exact Subgroup.mem_zpowers (e a')
    have hfixu : (e a : V ≃ₗ[F] V) (u a) = u a :=
      hF.toIsPlaneFrame.apply_eq_of_mem_zpowers hp (hF.toIsPlaneFrame.mem a) hea'_zp a hne
        (u a) (hF.mem a)
    have hu0 : u a = 0 :=
      hF.toIsPlaneFrame.eq_zero_of_apply_eq a (u a) (hF.mem a) hfixu
    have hc0 : c = 0 := by
      have h := hF.quad_eq a
      rw [hu0, map_zero] at h
      exact h.symm
    exact hF.c_ne_zero hc0
  let π : Equiv.Perm (Fin k) := Equiv.ofBijective b (Finite.injective_iff_bijective.mp hb_inj)
  refine ⟨π, ε, fun a => (hε a).1, ?_⟩
  intro a
  show g * e a * g⁻¹ = e (π a) ^ ε a
  have hπa : π a = b a := rfl
  rw [hπa]
  exact (hε a).2

end RelDNs

end CFSG.StandardType

end
