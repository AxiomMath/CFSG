module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18Common
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18Family
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18Case2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18Diagonal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18Assembly
public import CFSG.Quasithin.SteinbergCGPlanePairLocal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Config

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise


private theorem realizesVia_of_secIsoOn {W : Type} [CommGroup W]
    {X : Subgroup (MulAut W)} {D : FFModel} {π : D.Gam →* ↥X} {I J : Subgroup W}
    (h : D.RealizesVia X I ⊥ π) (hsec : SecIsoOn X I ⊥ J ⊥) :
    D.RealizesVia X J ⊥ π := by
  obtain ⟨-, -, hXI, -, hXJ, -, β, hβJ, hβk, hβs, hβe⟩ := hsec
  let βJ : ↥I →* ↥J := β.codRestrict J hβJ
  have hinj : Function.Injective βJ := by
    intro a b hab
    have h1 : βJ (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : β (a * b⁻¹) = 1 := congrArg Subtype.val h1
    have h3 : ((a * b⁻¹ : ↥I) : W) ∈ (⊥ : Subgroup W) := by
      have hb : β (a * b⁻¹) ∈ (⊥ : Subgroup W) := by
        rw [h2]
        exact Subgroup.mem_bot.mpr rfl
      exact (hβk (a * b⁻¹)).mp hb
    have h4 : (a * b⁻¹ : ↥I) = 1 := Subtype.ext (Subgroup.mem_bot.mp h3)
    exact mul_inv_eq_one.mp h4
  have hsurj : Function.Surjective βJ := by
    intro b
    obtain ⟨a, ha⟩ := hβs (b : W) b.2
    exact ⟨a, Subtype.ext (mul_inv_eq_one.mp (Subgroup.mem_bot.mp ha))⟩
  let e : ↥I ≃* ↥J := MulEquiv.ofBijective βJ ⟨hinj, hsurj⟩
  let f : ↥J ≃* ↥I := e.symm
  have hβe' : ∀ (x : ↥X) (a : ↥I),
      β (⟨(x : MulAut W) (a : W), hXI x x.2 (a : W) a.2⟩ : ↥I) =
        (x : MulAut W) (β a) := by
    intro x a
    have hzero := hβe x x.2 a ⟨(x : MulAut W) (a : W), hXI x x.2 (a : W) a.2⟩ rfl
    exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hzero)
  have hf : ∀ (x : ↥X) (u : ↥J),
      ((f ⟨(x : MulAut W) (u : W), hXJ x x.2 (u : W) u.2⟩ : ↥I) : W) =
        (x : MulAut W) ((f u : ↥I) : W) := by
    intro x u
    have hβfu : β (f u) = (u : W) := by
      have h1 : βJ (f u) = u := by
        rw [show f u = e.symm u from rfl]
        exact e.apply_symm_apply u
      exact congrArg Subtype.val h1
    have hval : f ⟨(x : MulAut W) (u : W), hXJ x x.2 (u : W) u.2⟩ =
        ⟨(x : MulAut W) ((f u : ↥I) : W), hXI x x.2 ((f u : ↥I) : W) (f u).2⟩ := by
      apply e.injective
      rw [e.apply_symm_apply]
      apply Subtype.ext
      symm
      calc ((βJ ⟨(x : MulAut W) ((f u : ↥I) : W),
              hXI x x.2 ((f u : ↥I) : W) (f u).2⟩ : ↥J) : W)
          = β ⟨(x : MulAut W) ((f u : ↥I) : W),
              hXI x x.2 ((f u : ↥I) : W) (f u).2⟩ := rfl
        _ = (x : MulAut W) (β (f u)) := hβe' x (f u)
        _ = (x : MulAut W) ((u : ↥J) : W) := by rw [hβfu]
    rw [hval]
  exact Thm14_5.realizesVia_transfer h (MonoidHom.id ↥X) Function.surjective_id
    (fun x u hu => hXJ x x.2 u hu) f hf

private theorem realizesVia_conj {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {D : FFModel} {I : Subgroup W} {π : D.Gam →* ↥L} (h : D.RealizesVia L I ⊥ π)
    {g : MulAut W} (hgL : L.map (MulAut.conj g).toMonoidHom = L) :
    ∃ π' : D.Gam →* ↥L, D.RealizesVia L (I.map g.toMonoidHom) ⊥ π' := by
  have hLI : ∀ x : ↥L, ∀ u ∈ I, (x : MulAut W) u ∈ I := h.2.2.2.1
  have hginvL : L.map (MulAut.conj g⁻¹).toMonoidHom = L := by
    have hgN : g ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hgL
    have hginvN : g⁻¹ ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
      (Subgroup.normalizer (L : Set (MulAut W))).inv_mem hgN
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hginvN
  let ρ : ↥L →* ↥L :=
    { toFun := fun x => ⟨g * (x : MulAut W) * g⁻¹, by
        have hx : g * (x : MulAut W) * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom :=
          Subgroup.mem_map.mpr ⟨(x : MulAut W), x.2, rfl⟩
        rwa [hgL] at hx⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp [mul_assoc] }
  have hρsurj : Function.Surjective ρ := by
    intro y
    have hy : (y : MulAut W) ∈ L.map (MulAut.conj g).toMonoidHom := by
      rw [hgL]; exact y.2
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let eI : ↥I ≃* ↥(I.map g.toMonoidHom) := I.equivMapOfInjective g.toMonoidHom g.injective
  let f : ↥(I.map g.toMonoidHom) ≃* ↥I := eI.symm
  have heI : ∀ v : ↥I, ((eI v : ↥(I.map g.toMonoidHom)) : W) = g (v : W) := fun v => rfl
  have hU' : ∀ x : ↥L, ∀ u ∈ I.map g.toMonoidHom, (x : MulAut W) u ∈ I.map g.toMonoidHom := by
    intro x u hu
    obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.mp hu
    have hxL : g⁻¹ * (x : MulAut W) * g ∈ L := by
      have hx : g⁻¹ * (x : MulAut W) * g ∈ L.map (MulAut.conj g⁻¹).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨(x : MulAut W), x.2, rfl⟩
      rwa [hginvL] at hx
    refine Subgroup.mem_map.mpr ⟨(g⁻¹ * (x : MulAut W) * g) v,
      hLI ⟨g⁻¹ * (x : MulAut W) * g, hxL⟩ v hv, ?_⟩
    rw [← hvu]
    simp [MulAut.mul_apply]
  have hf : ∀ (x : ↥L) (u : ↥(I.map g.toMonoidHom)),
      ((f ⟨(ρ x : MulAut W) (u : W), hU' (ρ x) u u.2⟩ : ↥I) : W) =
        (x : MulAut W) ((f u : ↥I) : W) := by
    intro x u
    apply g.injective
    have h1 : g (((f ⟨(ρ x : MulAut W) (u : W), hU' (ρ x) u u.2⟩ : ↥I) : W)) =
        (ρ x : MulAut W) (u : W) := by
      have := congrArg Subtype.val
        (eI.apply_symm_apply ⟨(ρ x : MulAut W) (u : W), hU' (ρ x) u u.2⟩)
      rw [heI] at this
      exact this
    have h2 : g ((x : MulAut W) ((f u : ↥I) : W)) = (ρ x : MulAut W) (u : W) := by
      have hgfu : g (((f u : ↥I) : W)) = (u : W) := by
        have := congrArg Subtype.val (eI.apply_symm_apply u)
        rw [heI] at this
        exact this
      calc g ((x : MulAut W) ((f u : ↥I) : W))
          = ((g * (x : MulAut W)) ((f u : ↥I) : W)) := rfl
        _ = (((g * (x : MulAut W) * g⁻¹) * g) ((f u : ↥I) : W)) := by group
        _ = (g * (x : MulAut W) * g⁻¹) (g ((f u : ↥I) : W)) := rfl
        _ = (ρ x : MulAut W) (u : W) := by rw [hgfu]; rfl
    rw [h1, h2]
  exact ⟨ρ.comp π, Thm14_5.realizesVia_transfer h ρ hρsurj hU' f hf⟩

private theorem aParam_autSub_top {W : Type} [CommGroup W] (Y : Subgroup (MulAut W)) :
    E3.aParam (autSub Y (⊤ : Subgroup W)) = E3.aParam Y := by
  rw [CFSG.Quasithin.H13.autSub_top_eq_map]
  exact CFSG.Quasithin.H.aParam_map_congrHom _ Y

private theorem center_eq_bot_of_isSimpleGroup {X : Type} [Group X] [IsSimpleGroup X]
    (hq : IsSimpleGroup (X ⧸ Subgroup.center X)) : Subgroup.center X = ⊥ := by
  rcases (inferInstance : (Subgroup.center X).Normal).eq_bot_or_eq_top with hZ | hZ
  · exact hZ
  · exfalso
    haveI hq' : Nontrivial (X ⧸ Subgroup.center X) := hq.toNontrivial
    haveI : Subsingleton (X ⧸ Subgroup.center X) := by
      refine ⟨fun a b => ?_⟩
      induction a using QuotientGroup.induction_on with
      | H a =>
        induction b using QuotientGroup.induction_on with
        | H b =>
          rw [QuotientGroup.eq]
          rw [hZ]
          exact Subgroup.mem_top _
    obtain ⟨a, b, hab⟩ := exists_pair_ne (X ⧸ Subgroup.center X)
    exact hab (Subsingleton.elim a b)



private theorem secIsoOn_refl_of_stable {W : Type} [CommGroup W]
    {X : Subgroup (MulAut W)} {I : Subgroup W} (hXI : StableUnder X I) :
    SecIsoOn X I ⊥ I ⊥ := by
  refine ⟨bot_le, bot_le, hXI, fun x hx u hu => by simpa using hu, hXI,
    fun x hx u hu => by simpa using hu, I.subtype, ?_, ?_, ?_, ?_⟩
  · intro a; exact a.2
  · intro a; exact Iff.rfl
  · intro b hb
    exact ⟨⟨b, hb⟩, by rw [Subgroup.mem_bot]; simp⟩
  · intro x hx a a' haa'
    show ((a' : ↥I) : W) * (x ((a : ↥I) : W))⁻¹ = 1
    rw [haa', mul_inv_cancel]

private theorem natSUn_of_secIsoOn {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {I J : Subgroup W} {n : ℕ} (h : NatSUn L I ⊥ 4 n) (hsec : SecIsoOn L I ⊥ J ⊥) :
    NatSUn L J ⊥ 4 n := by
  obtain ⟨K, hKf, hKfin, hcard, π, hπ⟩ := h
  exact ⟨K, hKf, hKfin, hcard, π, realizesVia_of_secIsoOn hπ hsec⟩

private theorem natOmegaMinus_of_secIsoOn {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} {I J : Subgroup W} {n : ℕ}
    (h : NatOmegaMinus L I ⊥ 6 n) (hsec : SecIsoOn L I ⊥ J ⊥) :
    NatOmegaMinus L J ⊥ 6 n := by
  obtain ⟨h6, K, hKf, hKfin, b, c, hcard, hq, π, hπ⟩ := h
  exact ⟨h6, K, hKf, hKfin, b, c, hcard, hq, π, realizesVia_of_secIsoOn hπ hsec⟩

private theorem natSUn_conj {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {I : Subgroup W} {n : ℕ} (h : NatSUn L I ⊥ 4 n) {g : MulAut W}
    (hgL : L.map (MulAut.conj g).toMonoidHom = L) :
    NatSUn L (I.map g.toMonoidHom) ⊥ 4 n := by
  obtain ⟨K, hKf, hKfin, hcard, π, hπ⟩ := h
  obtain ⟨π', hπ'⟩ := realizesVia_conj hπ hgL
  exact ⟨K, hKf, hKfin, hcard, π', hπ'⟩

private theorem natOmegaMinus_conj {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {I : Subgroup W} {n : ℕ} (h : NatOmegaMinus L I ⊥ 6 n) {g : MulAut W}
    (hgL : L.map (MulAut.conj g).toMonoidHom = L) :
    NatOmegaMinus L (I.map g.toMonoidHom) ⊥ 6 n := by
  obtain ⟨h6, K, hKf, hKfin, b, c, hcard, hq, π, hπ⟩ := h
  obtain ⟨π', hπ'⟩ := realizesVia_conj hπ hgL
  exact ⟨h6, K, hKf, hKfin, b, c, hcard, hq, π', hπ'⟩

private theorem natSUn_of_mem_irrSet {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y L : Subgroup (MulAut W)} (hO2 : O2Trivial Y)
    (hB : IsBasicModule Y) (hL : IsComponentOf L Y)
    (hfixH : fixV (⨆ X' ∈ conjSet L Y, X') = ⊥)
    (hsum0 : IsDirSumOver (conjSet L Y) (fun X' => commV (autQuot X' ⊥))) {I : Subgroup W}
    (hI : I ∈ irrSet L) {n : ℕ} (hNat : NatSUn L I ⊥ 4 n) {J : Subgroup W}
    (hJ : J ∈ irrSet L) : NatSUn L J ⊥ 4 n := by
  have hsum : IsDirSumOver (conjSet L Y) commV := Thm14_5.isDirSumOver_commV_of_autQuot_bot hsum0
  have hinf : commV L ⊓ fixV L = ⊥ := commV_inf_fixV_eq_bot_of_isDirSumOver hL hfixH hsum0
  have hJfix : J ⊓ fixV L = ⊥ := by
    rw [eq_bot_iff, ← hinf]
    exact inf_le_inf_right _ (le_commV_of_mem_irrSet hJ)
  obtain ⟨g, hg, hsecg⟩ :=
    exists_secIsoOn_of_mem_irrSet_of_basic hW hO2 hB hL hfixH hsum hI hJ
  have hgL : L.map (MulAut.conj g).toMonoidHom = L :=
    Thm14_5.map_conj_eq_of_secIsoOn hL.1 hsum hI hJ hJfix hg hsecg
  exact natSUn_of_secIsoOn (natSUn_conj hNat hgL) hsecg

private theorem natOmegaMinus_of_mem_irrSet {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y L : Subgroup (MulAut W)} (hO2 : O2Trivial Y)
    (hB : IsBasicModule Y) (hL : IsComponentOf L Y)
    (hfixH : fixV (⨆ X' ∈ conjSet L Y, X') = ⊥)
    (hsum0 : IsDirSumOver (conjSet L Y) (fun X' => commV (autQuot X' ⊥))) {I : Subgroup W}
    (hI : I ∈ irrSet L) {n : ℕ} (hNat : NatOmegaMinus L I ⊥ 6 n) {J : Subgroup W}
    (hJ : J ∈ irrSet L) : NatOmegaMinus L J ⊥ 6 n := by
  have hsum : IsDirSumOver (conjSet L Y) commV := Thm14_5.isDirSumOver_commV_of_autQuot_bot hsum0
  have hinf : commV L ⊓ fixV L = ⊥ := commV_inf_fixV_eq_bot_of_isDirSumOver hL hfixH hsum0
  have hJfix : J ⊓ fixV L = ⊥ := by
    rw [eq_bot_iff, ← hinf]
    exact inf_le_inf_right _ (le_commV_of_mem_irrSet hJ)
  obtain ⟨g, hg, hsecg⟩ :=
    exists_secIsoOn_of_mem_irrSet_of_basic hW hO2 hB hL hfixH hsum hI hJ
  have hgL : L.map (MulAut.conj g).toMonoidHom = L :=
    Thm14_5.map_conj_eq_of_secIsoOn hL.1 hsum hI hJ hJfix hg hsecg
  exact natOmegaMinus_of_secIsoOn (natOmegaMinus_conj hNat hgL) hsecg

private theorem natOmegaMinus_to_autSub {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {J : Subgroup W} {n : ℕ} (hLJ : L ≤ stabSub J) (hfaith : L ⊓ centSub J = ⊥)
    (h : NatOmegaMinus L J ⊥ 6 n) : NatOmegaMinus (autSub L J) ⊤ ⊥ 6 n := by
  exact Thm14_5.natOmegaMinus_transfer h (autSubEquivOfFaithful hLJ hfaith)
    (autSubEquivOfFaithful hLJ hfaith).surjective (fun _ _ _ => Subgroup.mem_top _)
    (Subgroup.topEquiv (G := J)) (fun x u => rfl)

private theorem mul_mParam_le_of_rk {mN m D C k : ℕ} (hD : 0 < D)
    (hrk : k * D ≤ C) (hmul : mN * C ≤ m * D) : k * mN ≤ m := by
  have h1 : mN * (k * D) ≤ mN * C := Nat.mul_le_mul_left _ hrk
  have h2 : mN * (k * D) ≤ m * D := h1.trans hmul
  have h2' : mN * k * D ≤ m * D := by
    calc mN * k * D = mN * (k * D) := by ring
      _ ≤ m * D := h2
  calc k * mN = mN * k := by ring
    _ ≤ m := Nat.le_of_mul_le_mul_right h2' hD

private theorem two_mul_rk_le_of_second {W : Type} [CommGroup W] [Finite W]
    {s : Set (Subgroup W)} (hs : sSupIndep s) {I J : Subgroup W}
    (hIs : I ∈ s) (hJs : J ∈ s) (hJI : J ≠ I) (hrk : rk ↥J = rk ↥I) :
    2 * rk ↥I ≤ rk ↥(sSup s) := by
  have hJnot : J ∈ s \ {I} :=
    ⟨hJs, by simpa [Set.mem_singleton_iff] using hJI⟩
  have hdisj : Disjoint I J := (hs hIs).mono_right (le_sSup hJnot)
  have hIJ : I ⊓ J = ⊥ := disjoint_iff.mp hdisj
  have hrank := rk_sup_add_rk_inf I J
  rw [hIJ, rk_bot, hrk] at hrank
  have hle : rk ↥(I ⊔ J) ≤ rk ↥(sSup s) :=
    rk_mono (sup_le (le_sSup hIs) (le_sSup hJs))
  omega

private theorem three_mul_rk_le_of_third {W : Type} [CommGroup W] [Finite W]
    {s : Set (Subgroup W)} (hs : sSupIndep s) {I J K : Subgroup W}
    (hIs : I ∈ s) (hJs : J ∈ s) (hKs : K ∈ s) (hJI : J ≠ I) (hKI : K ≠ I)
    (hKJ : K ≠ J) (hrkJ : rk ↥J = rk ↥I) (hrkK : rk ↥K = rk ↥I) :
    3 * rk ↥I ≤ rk ↥(sSup s) := by
  have hJnot : J ∈ s \ {I} :=
    ⟨hJs, by simpa [Set.mem_singleton_iff] using hJI⟩
  have hdisjIJ : Disjoint I J := (hs hIs).mono_right (le_sSup hJnot)
  have hIJ : I ⊓ J = ⊥ := disjoint_iff.mp hdisjIJ
  have hKdisj : Disjoint K (sSup (s \ {K})) := hs hKs
  have hJK : J ∈ s \ {K} :=
    ⟨hJs, by simpa [Set.mem_singleton_iff] using hKJ.symm⟩
  have hIK : I ∈ s \ {K} :=
    ⟨hIs, by simpa [Set.mem_singleton_iff] using hKI.symm⟩
  have hIJle : I ⊔ J ≤ sSup (s \ {K}) :=
    sup_le (le_sSup hIK) (le_sSup hJK)
  have hIJK : (I ⊔ J) ⊓ K = ⊥ := by
    rw [inf_comm]
    exact disjoint_iff.mp (hKdisj.mono_right hIJle)
  have hrank1 := rk_sup_add_rk_inf I J
  rw [hIJ, rk_bot, hrkJ] at hrank1
  have hrank2 := rk_sup_add_rk_inf (I ⊔ J) K
  rw [hIJK, rk_bot, hrkK] at hrank2
  have hle : rk ↥((I ⊔ J) ⊔ K) ≤ rk ↥(sSup s) :=
    rk_mono (sup_le (sup_le (le_sSup hIs) (le_sSup hJs)) (le_sSup hKs))
  omega

private theorem four_mul_rk_le_of_fourth {W : Type} [CommGroup W] [Finite W]
    {s : Set (Subgroup W)} (hs : sSupIndep s) {I J K M : Subgroup W}
    (hIs : I ∈ s) (hJs : J ∈ s) (hKs : K ∈ s) (hMs : M ∈ s)
    (hJI : J ≠ I) (hKI : K ≠ I) (hKJ : K ≠ J) (hMI : M ≠ I) (hMJ : M ≠ J)
    (hMK : M ≠ K) (hrkJ : rk ↥J = rk ↥I) (hrkK : rk ↥K = rk ↥I)
    (hrkM : rk ↥M = rk ↥I) : 4 * rk ↥I ≤ rk ↥(sSup s) := by
  have hJnot : J ∈ s \ {I} :=
    ⟨hJs, by simpa [Set.mem_singleton_iff] using hJI⟩
  have hdisjIJ : Disjoint I J := (hs hIs).mono_right (le_sSup hJnot)
  have hIJ : I ⊓ J = ⊥ := disjoint_iff.mp hdisjIJ
  have hKdisj : Disjoint K (sSup (s \ {K})) := hs hKs
  have hJK : J ∈ s \ {K} :=
    ⟨hJs, by simpa [Set.mem_singleton_iff] using hKJ.symm⟩
  have hIK : I ∈ s \ {K} :=
    ⟨hIs, by simpa [Set.mem_singleton_iff] using hKI.symm⟩
  have hIJle : I ⊔ J ≤ sSup (s \ {K}) := sup_le (le_sSup hIK) (le_sSup hJK)
  have hIJK : (I ⊔ J) ⊓ K = ⊥ := by
    rw [inf_comm]
    exact disjoint_iff.mp (hKdisj.mono_right hIJle)
  have hMdisj : Disjoint M (sSup (s \ {M})) := hs hMs
  have hJI' : J ∈ s \ {M} :=
    ⟨hJs, by simpa [Set.mem_singleton_iff] using hMJ.symm⟩
  have hKI' : K ∈ s \ {M} :=
    ⟨hKs, by simpa [Set.mem_singleton_iff] using hMK.symm⟩
  have hII' : I ∈ s \ {M} :=
    ⟨hIs, by simpa [Set.mem_singleton_iff] using hMI.symm⟩
  have hIJKle : (I ⊔ J) ⊔ K ≤ sSup (s \ {M}) :=
    sup_le (sup_le (le_sSup hII') (le_sSup hJI')) (le_sSup hKI')
  have hIJKM : ((I ⊔ J) ⊔ K) ⊓ M = ⊥ := by
    rw [inf_comm]
    exact disjoint_iff.mp (hMdisj.mono_right hIJKle)
  have hrank1 := rk_sup_add_rk_inf I J
  rw [hIJ, rk_bot, hrkJ] at hrank1
  have hrank2 := rk_sup_add_rk_inf (I ⊔ J) K
  rw [hIJK, rk_bot, hrkK] at hrank2
  have hrank3 := rk_sup_add_rk_inf ((I ⊔ J) ⊔ K) M
  rw [hIJKM, rk_bot, hrkM] at hrank3
  have hle : rk ↥(((I ⊔ J) ⊔ K) ⊔ M) ≤ rk ↥(sSup s) :=
    rk_mono (sup_le (sup_le (sup_le (le_sSup hIs) (le_sSup hJs)) (le_sSup hKs))
      (le_sSup hMs))
  omega

private theorem sumOfNat_three {W : Type} [CommGroup W]
    {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop} {H : Subgroup (MulAut W)}
    {I J K : Subgroup W} (hI : N H I ⊥) (hJ : N H J ⊥) (hK : N H K ⊥)
    (hind : iSupIndep ![I, J, K]) (htop : (⨆ i, ![I, J, K] i) = ⊤) :
    SumOfNat N H ⊤ ⊥ 3 := by
  refine ⟨![I, J, K], fun i => bot_le, ?_, ?_, ?_⟩
  · intro i
    have hd : Disjoint (![I, J, K] i) (⨆ (j : Fin 3) (_ : j ≠ i), ![I, J, K] j) := by
      simpa using hind i
    rw [bot_sup_eq]
    exact le_of_eq (disjoint_iff.mp hd)
  · simpa using htop
  · intro i
    fin_cases i
    · simpa using hI
    · simpa using hJ
    · simpa using hK

theorem concl146_of_caseI_U4
    (hb : W4Lem4_17U4U5N) (hMod : K146ModU4) (hA : K146Om6mA) (hIso : K146NatIsoU4)
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L : Subgroup (MulAut W)} {n : ℕ} (hO2 : O2Trivial Y)
    (hB : IsBasicModule Y) (hL : IsComponentOf L Y)
    (hX : L = ⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom) (hU4 : IsU4 ↥L n)
    (hn : 1 < n) (hfix : fixV L = ⊥) (hm : 3 < E3.mParam Y)
    (hle : E3.mParam Y ≤ max (bParam L Y) n + 2) : Sec18Concl Y L L n := by
  haveI hLsimple : IsSimpleGroup ↥L :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU4
  have hZ : Subgroup.center ↥L = ⊥ := center_eq_bot_of_isSimpleGroup hL.2.2.2
  have hoddZ : Odd (Nat.card ↥(Subgroup.center ↥L)) := by
    rw [hZ, Subgroup.card_bot]
    exact ⟨0, by simp⟩
  have hLn : (L.subgroupOf Y).Normal :=
    (Thm14_5.iSup_map_conj_eq_self_iff hL.1).mp hX.symm
  have hb3n : bParam L Y ≤ 3 * n := by
    refine bParam_le_of_normalCase hW hL hLn hfix hZ (B := 3 * n) ?_
    intro T _ _ hcomp hsyl hfixT _ hTN
    exact hb W hW (L ⊔ T) L T n le_sup_left le_sup_right rfl hcomp hsyl hfixT hoddZ hTN hn
      (Or.inl hU4)
  have hmle : E3.mParam Y ≤ 3 * n + 2 := by
    have hmax : max (bParam L Y) n ≤ 3 * n := max_le hb3n (by omega)
    omega
  have hdeg : 6 * n ≤ dMinDeg ↥L :=
    (dMinDeg_lower_bounds (L := ↥L) (n := n)).2.2.2.2.1 hU4 hn
  have hd : E3.mParam Y < dMinDeg ↥L := by
    have h3 : 3 * n + 2 < 6 * n := by omega
    omega
  have hnL2 : ∀ e : ℕ, ¬ IsL2 ↥L e :=
    fun e => not_isL2_of_shape (L := ↥L) (n := n) (e := e)
      (Or.inr (Or.inr (Or.inr (Or.inl hU4))))
  obtain ⟨hsum0, I, hI, hIm⟩ :=
    case2_of_fix_of_lt_dMinDeg hW hO2 hB hL hX hfix hd hnL2
  obtain ⟨hSN, hnorm, hirr, hrk, hmul, hmN⟩ := setup_of_case2 hW hL hX hfix hsum0 hI hIm
  have hLI : L ≤ stabSub I := Thm14_5.le_stabSub_of_mem_irrSet hI
  have hfixH : fixV (⨆ X' ∈ conjSet L Y, X') = ⊥ := by
    rw [WeakClosure81.iSup_conjSet_eq_biSup_conj, ← hX]
    exact hfix
  have hfixI : I ⊓ fixV L = ⊥ := by
    have hsum := Thm14_5.isDirSumOver_commV_of_autQuot_bot hsum0
    have hinf : commV L ⊓ fixV L = ⊥ := commV_inf_fixV_eq_bot_of_isDirSumOver hL hfixH hsum0
    rw [eq_bot_iff, ← hinf]
    exact inf_le_inf_right _ (le_commV_of_mem_irrSet hI)
  have hLI_faith : L ⊓ centSub I = ⊥ :=
    inf_centSub_eq_bot_of_isSimpleGroup hLsimple hLI
      (Thm14_5.not_le_centSub_of_mem_irrSet hI hfixI)
  have hU4S : IsU4 ↥(autSub L I) n :=
    lieModel_autSub hL hX hfix hsum0 hLsimple hI hU4
  have hleN : E3.mParam (autSub Y I) ≤ 3 * n + 2 := le_trans hmN hmle
  have hsum : IsDirSumOver (conjSet L Y) commV :=
    Thm14_5.isDirSumOver_commV_of_autQuot_bot hsum0
  have hcommTop : commV L = ⊤ := by
    have h := commV_sup_fixV_eq_top_of_basic hW hO2 hB hL
    rw [hfix, sup_bot_eq] at h
    exact h
  have hinf : commV L ⊓ fixV L = ⊥ :=
    commV_inf_fixV_eq_bot_of_isDirSumOver hL hfixH hsum0
  obtain ⟨s, hIs, hsL, hsind, hspan⟩ :=
    exists_sSupIndep_irrSet_of_basic hW hO2 hB hL hfixH hsum hI
  have hspanTop : sSup s = ⊤ := hspan.trans hcommTop
  have hDpos : 0 < rk ↥I := by
    rw [Nat.pos_iff_ne_zero, Ne, rk_eq_zero_iff hW]
    exact WeakClosure81.ne_bot_of_mem_irrSet hI
  have hrkJ : ∀ J ∈ irrSet L, rk ↥J = rk ↥I :=
    fun J hJ => rk_eq_of_mem_irrSet_of_basic hW hO2 hB hL hfixH hsum hI hJ
  have h2m_of : ∀ J ∈ s, J ≠ I → 2 * E3.mParam (autSub Y I) ≤ E3.mParam Y := by
    intro J hJs hJI
    have hrk : 2 * rk ↥I ≤ rk ↥(commV L) := by
      rw [← hspan]
      exact two_mul_rk_le_of_second hsind hIs hJs hJI (hrkJ J (hsL hJs))
    exact mul_mParam_le_of_rk hDpos hrk hmul
  have h3m_of : ∀ J ∈ s, J ≠ I → ∀ K ∈ s, K ≠ I → K ≠ J →
      3 * E3.mParam (autSub Y I) ≤ E3.mParam Y := by
    intro J hJs hJI K hKs hKI hKJ
    have hrk : 3 * rk ↥I ≤ rk ↥(commV L) := by
      rw [← hspan]
      exact three_mul_rk_le_of_third hsind hIs hJs hKs hJI hKI hKJ
        (hrkJ J (hsL hJs)) (hrkJ K (hsL hKs))
    exact mul_mParam_le_of_rk hDpos hrk hmul
  have h4m_of : ∀ J ∈ s, J ≠ I → ∀ K ∈ s, K ≠ I → K ≠ J → ∀ M ∈ s, M ≠ I → M ≠ J →
      M ≠ K → 4 * E3.mParam (autSub Y I) ≤ E3.mParam Y := by
    intro J hJs hJI K hKs hKI hKJ M hMs hMI hMJ hMK
    have hrk : 4 * rk ↥I ≤ rk ↥(commV L) := by
      rw [← hspan]
      exact four_mul_rk_le_of_fourth hsind hIs hJs hKs hMs hJI hKI hKJ hMI hMJ hMK
        (hrkJ J (hsL hJs)) (hrkJ K (hsL hKs)) (hrkJ M (hsL hMs))
    exact mul_mParam_le_of_rk hDpos hrk hmul
  rcases hMod ↥I (fun u => Subtype.ext (hW u)) (autSub Y I) (autSub L I) n
      hSN hnorm hU4S hn hirr hleN with
    ⟨hSUn, hNatSUn, h2n⟩ | ⟨hOmg, hNatOmg, hnle⟩ | ⟨hn2, h2mN, haN⟩
  ·
    have hNatSUnI : NatSUn L I ⊥ 4 n := by
      obtain ⟨K, hKf, hKfin, hcard, hreal⟩ := hNatSUn
      have hreal' : (FFModel.nat (StatedSU 4 (2 ^ n) K)).Realizes (autSub L I) ⊤
          ((⊥ : Subgroup W).subgroupOf I) := by
        rwa [Subgroup.bot_subgroupOf]
      exact ⟨K, hKf, hKfin, hcard,
        FFModel.Realizes.of_autSub hLI (B5.Ln.stabSub_bot_le L) bot_le hLI_faith hreal'⟩
    have hIsSUnL : IsSUn ↥L 4 n := by
      obtain ⟨K, hKf, hKfin, hcard, ⟨eS⟩⟩ := hSUn
      exact ⟨K, hKf, hKfin, hcard,
        ⟨(autSubEquivOfFaithful hLI hLI_faith).trans eS⟩⟩
    by_cases hsingle : s ⊆ {I}
    ·
      have hs_eq : s = {I} :=
        Set.Subset.antisymm hsingle (Set.singleton_subset_iff.mpr hIs)
      have hcommI : commV L = I := by
        rw [← hspan, hs_eq, sSup_singleton]
      have hItop : I = ⊤ := hcommI.symm.trans hcommTop
      have hNatTop : NatSUn L ⊤ ⊥ 4 n := by
        rw [← hItop]
        exact hNatSUnI
      refine Or.inr (Or.inr (Or.inl ⟨hIsSUnL, ?_⟩))
      simpa [hfix] using hNatTop
    ·
      obtain ⟨J, hJs, hJnot⟩ := Set.not_subset.mp hsingle
      have hJI : J ≠ I := by
        intro h
        exact hJnot (by simpa [h] using Set.mem_singleton I)
      have hJirr : J ∈ irrSet L := hsL hJs
      have h2D : 2 * rk ↥I ≤ rk ↥(sSup s) :=
        two_mul_rk_le_of_second hsind hIs hJs hJI (hrkJ J hJirr)
      have h2D' : 2 * rk ↥I ≤ rk ↥(commV L) := by
        rw [← hspan]
        exact h2D
      have hmN2 : 2 * E3.mParam (autSub Y I) ≤ E3.mParam Y := by
        have h1 := Nat.mul_le_mul_left (E3.mParam (autSub Y I)) h2D'
        have h2 : E3.mParam (autSub Y I) * (2 * rk ↥I) ≤ E3.mParam Y * rk ↥I :=
          h1.trans hmul
        have h2' : E3.mParam (autSub Y I) * 2 * rk ↥I ≤ E3.mParam Y * rk ↥I := by
          calc E3.mParam (autSub Y I) * 2 * rk ↥I
              = E3.mParam (autSub Y I) * (2 * rk ↥I) := by ring
            _ ≤ E3.mParam Y * rk ↥I := h2
        have h3 := Nat.le_of_mul_le_mul_right h2' hDpos
        omega
      have hn2' : n = 2 := by
        have h4 : 4 * n ≤ E3.mParam Y := by omega
        omega
      have hnot3 : ∀ K ∈ s, K ≠ I → K ≠ J → False := by
        intro K hKs hKI hKJ
        have h3D : 3 * rk ↥I ≤ rk ↥(sSup s) :=
          three_mul_rk_le_of_third hsind hIs hJs hKs hJI hKI hKJ
            (hrkJ J hJirr) (hrkJ K (hsL hKs))
        have h3D' : 3 * rk ↥I ≤ rk ↥(commV L) := by
          rw [← hspan]
          exact h3D
        have h3m : 3 * E3.mParam (autSub Y I) ≤ E3.mParam Y := by
          have h1 := Nat.mul_le_mul_left (E3.mParam (autSub Y I)) h3D'
          have h2 : E3.mParam (autSub Y I) * (3 * rk ↥I) ≤ E3.mParam Y * rk ↥I :=
            h1.trans hmul
          have h2' : E3.mParam (autSub Y I) * 3 * rk ↥I ≤ E3.mParam Y * rk ↥I := by
            calc E3.mParam (autSub Y I) * 3 * rk ↥I
                = E3.mParam (autSub Y I) * (3 * rk ↥I) := by ring
              _ ≤ E3.mParam Y * rk ↥I := h2
          have h3 := Nat.le_of_mul_le_mul_right h2' hDpos
          omega
        have h8 : E3.mParam Y ≤ 8 := by
          rw [hn2'] at hmle
          norm_num at hmle
          exact hmle
        have : 3 * 4 ≤ E3.mParam Y := by
          have h4 : 4 ≤ E3.mParam (autSub Y I) := by
            rw [hn2'] at h2n
            omega
          omega
        omega
      have hs_eq : s = {I, J} := by
        apply Set.Subset.antisymm
        · intro K hKs
          by_contra hK
          have hKI : K ≠ I := fun h => hK (by simp [h])
          have hKJ : K ≠ J := fun h => hK (by simp [h])
          exact hnot3 K hKs hKI hKJ
        · intro K hK
          rcases hK with rfl | rfl
          · exact hIs
          · exact hJs
      have hIJinf : I ⊓ J = ⊥ := by
        have hJnot' : J ∈ s \ {I} :=
          ⟨hJs, by simpa [Set.mem_singleton_iff] using hJI⟩
        exact disjoint_iff.mp ((hsind hIs).mono_right (le_sSup hJnot'))
      have hIJtop : I ⊔ J = ⊤ := by
        have h := hspanTop
        rw [hs_eq] at h
        simpa [sSup_pair] using h
      have hNatSUnJ : NatSUn L J ⊥ 4 n :=
        natSUn_of_mem_irrSet hW hO2 hB hL hfixH hsum0 hI hNatSUnI hJirr
      have hsecIJ : SecIsoOn L I ⊥ J ⊥ :=
        hIso W hW L n I J hU4 hn (Or.inl ⟨hNatSUnI, hNatSUnJ⟩)
      obtain ⟨K, hKf, hKfin, hcard, π, hπ⟩ := hNatSUnI
      have hπJ : (FFModel.nat (StatedSU 4 (2 ^ n) K)).RealizesVia L J ⊥ π :=
        realizesVia_of_secIsoOn hπ hsecIJ
      have hsumNat : SumOfNatVia (FFModel.nat (StatedSU 4 (2 ^ n) K)) L ⊤ ⊥ 2 π :=
        sumOfNatVia_of_secIsoOn hπ ![I, J] (fun i => by
          fin_cases i
          · simpa using secIsoOn_refl_of_stable (stableUnder_of_mem_irrSet hI)
          · simpa using hsecIJ)
          (CFSG.Quasithin.SteinbergCG.iSupIndep_fin_two (f := ![I, J])
            (by simpa [Matrix.cons_val_zero, Matrix.cons_val_one] using
              disjoint_iff.mpr hIJinf))
          (by rw [iSup_fin_two_eq]; exact hIJtop)
      have h8d : n = 2 ∧ IsSUn ↥L 4 n ∧
          ∃ (K : Type) (_ : Field K) (_ : Finite K)
            (π : ↥(StatedSU 4 (2 ^ n) K) →* ↥L),
            Nat.card K = (2 ^ n) ^ 2 ∧
              SumOfNatVia (FFModel.nat (StatedSU 4 (2 ^ n) K)) L ⊤ ⊥ 2 π :=
        ⟨hn2', hIsSUnL, K, hKf, hKfin, π, hcard, hsumNat⟩
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inl (Or.inr <| Or.inr <| Or.inr h8d)
  ·
    have hNatOmgI : NatOmegaMinus L I ⊥ 6 n := by
      obtain ⟨h6, K, hKf, hKfin, b, c, hcard, hq, hreal⟩ := hNatOmg
      have hreal' : (FFModel.nat (StatedOmega (StatedQuadMinus 3 K b c))).Realizes
          (autSub L I) ⊤ ((⊥ : Subgroup W).subgroupOf I) := by
        rwa [Subgroup.bot_subgroupOf]
      exact ⟨h6, K, hKf, hKfin, b, c, hcard, hq,
        FFModel.Realizes.of_autSub hLI (B5.Ln.stabSub_bot_le L) bot_le hLI_faith hreal'⟩
    have hOmgL : IsOmegaMinus ↥L 6 n := by
      obtain ⟨h6, K, hKf, hKfin, b, c, hcard, hq, ⟨e'⟩⟩ := hOmg
      exact ⟨h6, K, hKf, hKfin, b, c, hcard, hq,
        ⟨(autSubEquivOfFaithful hLI hLI_faith).trans e'⟩⟩
    have hNatAutSub : ∀ J ∈ irrSet L, NatOmegaMinus (autSub L J) ⊤ ⊥ 6 n := by
      intro J hJ
      have hNatJ : NatOmegaMinus L J ⊥ 6 n :=
        natOmegaMinus_of_mem_irrSet hW hO2 hB hL hfixH hsum0 hI hNatOmgI hJ
      have hLJ : L ≤ stabSub J := Thm14_5.le_stabSub_of_mem_irrSet hJ
      have hJfix : J ⊓ fixV L = ⊥ := by
        rw [eq_bot_iff, ← hinf]
        exact inf_le_inf_right _ (le_commV_of_mem_irrSet hJ)
      have hfaithJ : L ⊓ centSub J = ⊥ :=
        inf_centSub_eq_bot_of_isSimpleGroup hLsimple hLJ
          (Thm14_5.not_le_centSub_of_mem_irrSet hJ hJfix)
      exact natOmegaMinus_to_autSub hLJ hfaithJ hNatJ
    have hhom : ∀ J ∈ irrSet L, SecIsoOn L I ⊥ J ⊥ := by
      intro J hJ
      have hNatJ : NatOmegaMinus L J ⊥ 6 n :=
        natOmegaMinus_of_mem_irrSet hW hO2 hB hL hfixH hsum0 hI hNatOmgI hJ
      exact hIso W hW L n I J hU4 hn (Or.inr ⟨hNatOmgI, hNatJ⟩)
    have haJ : ∀ J ∈ irrSet L, E3.aParam (autSub Y J) ≤ 2 * n + 1 ∧
        (Odd n → E3.aParam (autSub Y J) ≤ 2 * n) := by
      intro J hJ
      have hSNJ : autSub L J ≤ autSub Y J := autSub_mono hL.1 J
      have hnormJ : ((autSub L J).subgroupOf (autSub Y J)).Normal :=
        Thm14_5.normal_autSub_of_normalizes (fun y hy hyJ =>
          Thm14_5.mem_normalizer_of_mem_stabSub hsum hJ hy hyJ)
      exact hA ↥J (fun u => Subtype.ext (hW u)) (autSub Y J) (autSub L J) n
        hSNJ hnormJ hn (hNatAutSub J hJ)
    have hb2n1 : bParam L Y ≤ 2 * n + 1 :=
      bParam_le_of_homogeneous hW hL.1 hLn hLsimple hfix hcommTop hI hhom
        (B := 2 * n + 1) (fun J hJ => (haJ J hJ).1)
    have hmB1 : E3.mParam Y ≤ 2 * n + 3 := by
      have hmax : max (bParam L Y) n ≤ 2 * n + 1 := max_le hb2n1 (by omega)
      omega
    by_cases hsingle : s ⊆ {I}
    ·
      have hs_eq : s = {I} :=
        Set.Subset.antisymm hsingle (Set.singleton_subset_iff.mpr hIs)
      have hcommI : commV L = I := by
        rw [← hspan, hs_eq, sSup_singleton]
      have hItop : I = ⊤ := hcommI.symm.trans hcommTop
      have hNatTop : NatOmegaMinus L ⊤ ⊥ 6 n := by
        rw [← hItop]
        exact hNatOmgI
      have h4 : IsOmegaMinus ↥L 6 n ∧ NatOmegaMinus L ⊤ (fixV L) 6 n :=
        ⟨hOmgL, by simpa [hfix] using hNatTop⟩
      exact Or.inr <| Or.inr <| Or.inr <| Or.inl h4
    ·
      obtain ⟨J, hJs, hJnot⟩ := Set.not_subset.mp hsingle
      have hJI : J ≠ I := by
        intro h
        exact hJnot (by simpa [h] using Set.mem_singleton I)
      have hJirr : J ∈ irrSet L := hsL hJs
      by_cases hsingle2 : s ⊆ {I, J}
      ·
        have hs_eq : s = {I, J} :=
          Set.Subset.antisymm hsingle2 (by
            intro M hM
            rcases hM with rfl | rfl
            · exact hIs
            · exact hJs)
        have hIJinf : I ⊓ J = ⊥ := by
          have hJnot' : J ∈ s \ {I} :=
            ⟨hJs, by simpa [Set.mem_singleton_iff] using hJI⟩
          exact disjoint_iff.mp ((hsind hIs).mono_right (le_sSup hJnot'))
        have hIJtop : I ⊔ J = ⊤ := by
          have h := hspanTop
          rw [hs_eq] at h
          simpa [sSup_pair] using h
        have hNatJ : NatOmegaMinus L J ⊥ 6 n :=
          natOmegaMinus_of_mem_irrSet hW hO2 hB hL hfixH hsum0 hI hNatOmgI hJirr
        have hsecIJ : SecIsoOn L I ⊥ J ⊥ :=
          hIso W hW L n I J hU4 hn (Or.inr ⟨hNatOmgI, hNatJ⟩)
        obtain ⟨h6, K, hKf, hKfin, b, c, hcard, hq, π, hπ⟩ := hNatOmgI
        have hsumNat : SumOfNatVia (FFModel.nat (StatedOmega (StatedQuadMinus 3 K b c)))
            L ⊤ ⊥ 2 π :=
          sumOfNatVia_of_secIsoOn hπ ![I, J] (fun i => by
            fin_cases i
            · simpa using secIsoOn_refl_of_stable (stableUnder_of_mem_irrSet hI)
            · simpa using hsecIJ)
            (CFSG.Quasithin.SteinbergCG.iSupIndep_fin_two (f := ![I, J])
            (by simpa [Matrix.cons_val_zero, Matrix.cons_val_one] using
              disjoint_iff.mpr hIJinf))
          (by rw [iSup_fin_two_eq]; exact hIJtop)
        have h8b : IsOmegaMinus ↥L 6 n ∧
            ∃ (K : Type) (_ : Field K) (_ : Finite K) (b c : K)
              (π : ↥(StatedOmega (StatedQuadMinus 3 K b c)) →* ↥L),
              Nat.card K = 2 ^ n ∧ (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
                SumOfNatVia (FFModel.nat (StatedOmega (StatedQuadMinus 3 K b c)))
                  L ⊤ ⊥ 2 π :=
          ⟨hOmgL, K, hKf, hKfin, b, c, π, hcard, hq, hsumNat⟩
        exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inl (Or.inr (Or.inl h8b))
      ·
        obtain ⟨K, hKs, hKnot⟩ := Set.not_subset.mp hsingle2
        have hKI : K ≠ I := by
          intro h
          exact hKnot (by simp [h])
        have hKJ : K ≠ J := by
          intro h
          exact hKnot (by simp [h])
        have h3m : 3 * E3.mParam (autSub Y I) ≤ E3.mParam Y :=
          h3m_of J hJs hJI K hKs hKI hKJ
        by_cases hodd : Odd n
        · exfalso
          have hb2n : bParam L Y ≤ 2 * n :=
            bParam_le_of_homogeneous hW hL.1 hLn hLsimple hfix hcommTop hI hhom
              (B := 2 * n) (fun J hJ => (haJ J hJ).2 hodd)
          have hmB2 : E3.mParam Y ≤ 2 * n + 2 := by
            have hmax : max (bParam L Y) n ≤ 2 * n := max_le hb2n (by omega)
            omega
          obtain ⟨k, hk⟩ := hodd
          omega
        ·
          have hn3 : n ≤ 3 := by omega
          have hn2' : n = 2 := by
            obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.1 hodd
            omega
          have hnle2 : 2 ≤ E3.mParam (autSub Y I) := by
            simpa [hn2'] using hnle
          have hmB1' : E3.mParam Y ≤ 7 := by
            simpa [hn2'] using hmB1
          have hnot4 : ∀ M ∈ s, M ≠ I → M ≠ J → M ≠ K → False := by
            intro M hMs hMI hMJ hMK
            have h4m : 4 * E3.mParam (autSub Y I) ≤ E3.mParam Y :=
              h4m_of J hJs hJI K hKs hKI hKJ M hMs hMI hMJ hMK
            omega
          have hs_eq3 : s = {I, J, K} := by
            apply Set.Subset.antisymm
            · intro M hMs
              by_contra hM
              have hMI : M ≠ I := fun h => hM (by simp [h])
              have hMJ : M ≠ J := fun h => hM (by simp [h])
              have hMK : M ≠ K := fun h => hM (by simp [h])
              exact hnot4 M hMs hMI hMJ hMK
            · intro M hM
              rcases hM with rfl | rfl | rfl
              · exact hIs
              · exact hJs
              · exact hKs
          have hdisjI : Disjoint I (J ⊔ K) :=
            (hsind hIs).mono_right (sup_le
              (le_sSup (show J ∈ s \ {I} from
                ⟨hJs, by simpa [Set.mem_singleton_iff] using hJI⟩))
              (le_sSup (show K ∈ s \ {I} from
                ⟨hKs, by simpa [Set.mem_singleton_iff] using hKI⟩)))
          have hdisjJ : Disjoint J (I ⊔ K) :=
            (hsind hJs).mono_right (sup_le
              (le_sSup (show I ∈ s \ {J} from
                ⟨hIs, by simpa [Set.mem_singleton_iff] using hJI.symm⟩))
              (le_sSup (show K ∈ s \ {J} from
                ⟨hKs, by simpa [Set.mem_singleton_iff] using hKJ⟩)))
          have hdisjK : Disjoint K (I ⊔ J) :=
            (hsind hKs).mono_right (sup_le
              (le_sSup (show I ∈ s \ {K} from
                ⟨hIs, by simpa [Set.mem_singleton_iff] using hKI.symm⟩))
              (le_sSup (show J ∈ s \ {K} from
                ⟨hJs, by simpa [Set.mem_singleton_iff] using hKJ.symm⟩)))
          have hind : iSupIndep ![I, J, K] := by
            rw [iSupIndep_fin_three]
            refine ⟨?_, ?_, ?_⟩
            · simpa using hdisjI
            · simpa [sup_comm] using hdisjJ
            · simpa [sup_comm] using hdisjK
          have htop3 : I ⊔ J ⊔ K = ⊤ := by
            have h := hspanTop
            rw [hs_eq3] at h
            simpa [sSup_insert, sSup_pair, sup_assoc] using h
          have htop : (⨆ i, ![I, J, K] i) = ⊤ := by
            rw [iSup_fin_three]
            exact htop3
          have hNatI : NatOmegaMinus L I ⊥ 6 2 := by simpa [hn2'] using hNatOmgI
          have hNatJ : NatOmegaMinus L J ⊥ 6 2 := by
            simpa [hn2'] using
              (natOmegaMinus_of_mem_irrSet hW hO2 hB hL hfixH hsum0 hI hNatOmgI hJirr)
          have hNatK : NatOmegaMinus L K ⊥ 6 2 := by
            simpa [hn2'] using
              (natOmegaMinus_of_mem_irrSet hW hO2 hB hL hfixH hsum0 hI hNatOmgI
                (hsL hKs))
          have hsum3 : SumOfNat (fun H U Z => NatOmegaMinus H U Z 6 2) L ⊤ ⊥ 3 :=
            sumOfNat_three hNatI hNatJ hNatK hind htop
          have h9 : IsOmegaMinus ↥L 6 2 ∧
              SumOfNat (fun H U Z => NatOmegaMinus H U Z 6 2) L ⊤ ⊥ 3 :=
            ⟨by simpa [hn2'] using hOmgL, hsum3⟩
          exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
            Or.inr <| Or.inl (Or.inl h9)

  ·
    exfalso
    by_cases hsingle : s ⊆ {I}
    ·
      have hs_eq : s = {I} :=
        Set.Subset.antisymm hsingle (Set.singleton_subset_iff.mpr hIs)
      have hcommI : commV L = I := by
        rw [← hspan, hs_eq, sSup_singleton]
      have hItop : I = ⊤ := hcommI.symm.trans hcommTop
      have haY : E3.aParam Y + 2 < E3.mParam Y := by
        have h1 : E3.aParam (autSub Y I) + 2 < E3.mParam (autSub Y I) := haN
        rw [hItop, aParam_autSub_top] at h1
        have h2 : E3.mParam (autSub Y ⊤) ≤ E3.mParam Y := by
          rwa [hItop] at hmN
        exact lt_of_lt_of_le h1 h2
      have hb_le_a : bParam L Y ≤ E3.aParam Y := bParam_le_aParam
      have hm_bound : E3.mParam Y ≤ max (E3.aParam Y) 2 + 2 := by
        have hmax : max (bParam L Y) n ≤ max (E3.aParam Y) 2 := by
          rw [hn2]
          exact max_le (hb_le_a.trans (le_max_left _ _)) (le_max_right _ _)
        omega
      have hm5 : 5 ≤ E3.mParam Y := by
        have h2mN' : 3 * 2 + 2 < 2 * E3.mParam (autSub Y I) := by
          simpa [hn2] using h2mN
        omega
      by_cases ha2 : 2 ≤ E3.aParam Y
      · have hmax : max (E3.aParam Y) 2 = E3.aParam Y := max_eq_left ha2
        omega
      · have hmax : max (E3.aParam Y) 2 = 2 := max_eq_right (by omega)
        omega
    ·
      obtain ⟨J, hJs, hJnot⟩ := Set.not_subset.mp hsingle
      have hJI : J ≠ I := by
        intro h
        exact hJnot (by simpa [h] using Set.mem_singleton I)
      have h2m : 2 * E3.mParam (autSub Y I) ≤ E3.mParam Y :=
        h2m_of J hJs hJI
      have hmN5 : 5 ≤ E3.mParam (autSub Y I) := by
        have h2mN' : 3 * 2 + 2 < 2 * E3.mParam (autSub Y I) := by
          simpa [hn2] using h2mN
        omega
      have hm8 : E3.mParam Y ≤ 8 := by
        rw [hn2] at hmle
        norm_num at hmle
        exact hmle
      omega



theorem false_of_caseI_U54
    (hb : W4Lem4_17U4U5N) (hMod : K146ModU54)
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L : Subgroup (MulAut W)} (hO2 : O2Trivial Y)
    (hB : IsBasicModule Y) (hL : IsComponentOf L Y)
    (hX : L = ⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom) (hU5 : LieModel ↥L .PSU 5 2 2)
    (hfix : fixV L = ⊥) (hm : 3 < E3.mParam Y)
    (hle : E3.mParam Y ≤ max (bParam L Y) 2 + 2) : False := by
  haveI hLsimple : IsSimpleGroup ↥L :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU5
  have hZ : Subgroup.center ↥L = ⊥ := center_eq_bot_of_isSimpleGroup hL.2.2.2
  have hoddZ : Odd (Nat.card ↥(Subgroup.center ↥L)) := by
    rw [hZ, Subgroup.card_bot]
    exact ⟨0, by simp⟩
  have hLn : (L.subgroupOf Y).Normal :=
    (Thm14_5.iSup_map_conj_eq_self_iff hL.1).mp hX.symm
  have hb6 : bParam L Y ≤ 3 * 2 := by
    refine bParam_le_of_normalCase hW hL hLn hfix hZ (B := 3 * 2) ?_
    intro T _ _ hcomp hsyl hfixT _ hTN
    exact hb W hW (L ⊔ T) L T 2 le_sup_left le_sup_right rfl hcomp hsyl hfixT hoddZ hTN
      (by norm_num) (Or.inr hU5)
  have hm8 : E3.mParam Y ≤ 8 := by
    have hmax : max (bParam L Y) 2 ≤ 6 := max_le hb6 (by norm_num)
    omega
  have hdeg : 20 ≤ dMinDeg ↥L :=
    (dMinDeg_lower_bounds (L := ↥L) (n := 2)).2.2.2.2.2 hU5
  have hd : E3.mParam Y < dMinDeg ↥L := by omega
  have hnL2 : ∀ e : ℕ, ¬ IsL2 ↥L e :=
    fun e => not_isL2_of_shape (L := ↥L) (n := 2) (e := e)
      (Or.inr (Or.inr (Or.inr (Or.inr hU5))))
  obtain ⟨hsum0, I, hI, hIm⟩ :=
    case2_of_fix_of_lt_dMinDeg hW hO2 hB hL hX hfix hd hnL2
  obtain ⟨hSN, hnorm, hirr, hrk, hmul, hmN⟩ := setup_of_case2 hW hL hX hfix hsum0 hI hIm
  have hLie : LieModel ↥(autSub L I) .PSU 5 2 2 :=
    lieModel_autSub hL hX hfix hsum0 hLsimple hI hU5
  have h9 : 8 < E3.mParam (autSub Y I) :=
    hMod ↥I (fun u => Subtype.ext (hW u)) (autSub Y I) (autSub L I) hSN hnorm hLie hirr
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
