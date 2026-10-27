module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentySwap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyNineFrame
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyNineNorm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyNineOdd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyNineFix
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s16c167_mkTil_bot_injective {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    Function.Injective (mkTil (⊥ : Subgroup G) V hV) := by
  intro x y hxy
  exact IntMod.val_injective
    (mul_inv_eq_one.1 (Subgroup.mem_bot.1 ((mkTil_eq_iff ⊥ V hV x y).1 hxy)))

private theorem s16c167_imgTil_inj' {V U U' : Subgroup G} (hV : IsElemAbelian 2 V)
    (hU : U ≤ V) (hU' : U' ≤ V) (h : imgTil (⊥ : Subgroup G) V hV U =
      imgTil (⊥ : Subgroup G) V hV U') : U = U' := by
  have hmkTil_inj : Function.Injective (mkTil (⊥ : Subgroup G) V hV) :=
    s16c167_mkTil_bot_injective hV
  have hmain : (intSub V hV U).map (mkTil (⊥ : Subgroup G) V hV) =
      (intSub V hV U').map (mkTil (⊥ : Subgroup G) V hV) := h
  have h1 : intSub V hV U = intSub V hV U' := by
    have hc := congrArg (Subgroup.comap (mkTil (⊥ : Subgroup G) V hV)) hmain
    rw [Subgroup.comap_map_eq_self_of_injective hmkTil_inj,
      Subgroup.comap_map_eq_self_of_injective hmkTil_inj] at hc
    exact hc
  have h2 : (U.subgroupOf V).map V.subtype = (U'.subgroupOf V).map V.subtype := by
    simpa only [intSub] using congrArg (Subgroup.map V.subtype) h1
  rwa [Subgroup.map_subgroupOf_eq_of_le hU, Subgroup.map_subgroupOf_eq_of_le hU'] at h2

private theorem s16c167_isIrr_action_nontrivial' {W : Type*} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} {V : Subgroup W}
    (hV : XMod.IsIrr ↥L V) (hc : Nat.card ↥V = 8) :
    ∃ x ∈ L, ∃ v ∈ V, x v ≠ v := by
  by_contra hcon
  have htriv : ∀ x ∈ L, ∀ v ∈ V, x v = v := by
    intro x hx v hv
    by_contra hne
    exact hcon ⟨x, hx, v, hv, hne⟩
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥V) 2 (by rw [hc]; norm_num)
  let J : Subgroup W := Subgroup.zpowers (x₀ : W)
  have hxV : (x₀ : W) ∈ V := x₀.2
  have hJV : J ≤ V := Subgroup.zpowers_le.mpr hxV
  have hJcard : Nat.card J = 2 := by
    change Nat.card (Subgroup.zpowers (x₀ : W)) = 2
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx₀]
  have hJinv : XMod.IsInv ↥L J := by
    intro a l hl
    have hlV : l ∈ V := hJV hl
    have hfix : (a : MulAut W) l = l := htriv a a.2 l hlV
    show (a : MulAut W) l ∈ J
    rw [hfix]; exact hl
  have hJbot : J ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hJcard
    omega
  have hJtop : J ≠ V := by
    intro h
    rw [h, hc] at hJcard
    omega
  rcases hV.2.2 J hJinv bot_le hJV with h | h
  · exact hJbot h
  · exact hJtop h

private theorem s16c167_fixV_barSub {V B' : Subgroup G} (hV : IsElemAbelian 2 V)
    (hB' : B' ≤ stabTil (⊥ : Subgroup G) V) :
    fixV (barSub (⊥ : Subgroup G) V hV B') =
      imgTil (⊥ : Subgroup G) V hV (V ⊓ centralizer (B' : Set G)) := by
  ext q
  constructor
  · intro hq
    obtain ⟨x, rfl⟩ := mkTil_surjective (⊥ : Subgroup G) V hV q
    rw [mem_imgTil]
    refine ⟨x, ⟨x.val_mem, ?_⟩, rfl⟩
    intro b hb
    have hbs : b ∈ stabTil (⊥ : Subgroup G) V := hB' hb
    have hmem : actTil (⊥ : Subgroup G) V hV ⟨b, hbs⟩ ∈ barSub (⊥ : Subgroup G) V hV B' :=
      actTil_mem_barSub (⊥ : Subgroup G) V hV hb hbs
    have h1 : actTil (⊥ : Subgroup G) V hV ⟨b, hbs⟩ (mkTil (⊥ : Subgroup G) V hV x) =
        mkTil (⊥ : Subgroup G) V hV x := (mem_fixV.1 hq) _ hmem
    rw [actTil_mk] at h1
    have h2 : actStab (⊥ : Subgroup G) V hV ⟨b, hbs⟩ x = x :=
      s16c167_mkTil_bot_injective hV h1
    have h3 := congrArg IntMod.val h2
    rw [actStab_apply_val] at h3
    exact mul_inv_eq_iff_eq_mul.1 h3
  · rintro ⟨x, ⟨hxV, hxC⟩, rfl⟩
    rw [mem_fixV]
    intro φ hφ
    obtain ⟨b, hb, hbφ⟩ := (mem_barSub (⊥ : Subgroup G) V hV B' φ).1 hφ
    rw [← hbφ, actTil_mk]
    congr 1
    apply IntMod.val_injective
    rw [actStab_apply_val]
    have h1 : (b : G) * x.val = x.val * (b : G) := hxC (b : G) hb
    rw [mul_inv_eq_iff_eq_mul.2 h1]

private theorem s16c167_mem_conjSubs_map {W : Type} [CommGroup W]
    {X : Subgroup (MulAut W)} {U : Subgroup W} {Y : Subgroup W}
    (hY : Y ∈ conjSubs X U) {φ : MulAut W} (hφ : φ ∈ X) :
    Y.map φ.toMonoidHom ∈ conjSubs X U := by
  obtain ⟨ψ, hψ, rfl⟩ := hY
  refine ⟨φ * ψ, X.mul_mem hφ hψ, ?_⟩
  rw [Subgroup.map_map]
  rfl

private theorem s16c167_lBar_le_stabSub_wTil {V L : Subgroup G} (hV : IsElemAbelian 2 V) :
    lBar (⊥ : Subgroup G) V hV L ≤ stabSub (wTil (⊥ : Subgroup G) V hV L) := by
  have hmap : ∀ y ∈ lBar (⊥ : Subgroup G) V hV L,
      ∀ w ∈ wTil (⊥ : Subgroup G) V hV L, y w ∈ wTil (⊥ : Subgroup G) V hV L := by
    intro y hy w hw
    have h := s15_Infra_commSub_top_map_conj (lBar (⊥ : Subgroup G) V hV L) y
    have hX : (lBar (⊥ : Subgroup G) V hV L).map (MulAut.conj y).toMonoidHom =
        lBar (⊥ : Subgroup G) V hV L := by
      ext z
      constructor
      · rintro ⟨z₀, hz₀, rfl⟩
        exact (lBar (⊥ : Subgroup G) V hV L).mul_mem
          ((lBar (⊥ : Subgroup G) V hV L).mul_mem hy hz₀)
          ((lBar (⊥ : Subgroup G) V hV L).inv_mem hy)
      · intro hz
        exact ⟨y⁻¹ * z * y, (lBar (⊥ : Subgroup G) V hV L).mul_mem
          ((lBar (⊥ : Subgroup G) V hV L).mul_mem
            ((lBar (⊥ : Subgroup G) V hV L).inv_mem hy) hz) hy,
          by simp [MulAut.conj_apply, mul_assoc]⟩
    rw [hX] at h
    change y w ∈ commSub ⊤ (lBar (⊥ : Subgroup G) V hV L)
    rw [h]
    exact ⟨w, hw, rfl⟩
  intro x hx
  rw [mem_stabSub]
  intro u
  exact ⟨fun hu => by
    have h1 := hmap x⁻¹ ((lBar (⊥ : Subgroup G) V hV L).inv_mem hx) (x u) hu
    rwa [mulAut_inv_apply_apply] at h1, hmap x hx u⟩

private theorem s16c167_lBar_inf_centSub_wTil_eq_bot {V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hLbar : IsPSL 3 2 1 ↥(lBar (⊥ : Subgroup G) V hV L))
    (hJ : NatSum3 (lBar (⊥ : Subgroup G) V hV L) (wTil (⊥ : Subgroup G) V hV L)) :
    lBar (⊥ : Subgroup G) V hV L ⊓ centSub (wTil (⊥ : Subgroup G) V hV L) = ⊥ := by
  rw [eq_bot_iff]
  intro l hl
  obtain ⟨hlL, hlC⟩ := Subgroup.mem_inf.1 hl
  obtain ⟨I₀, I₁, I₂, hi₀, -, -, hc₀, -, -, h01, h012, hsum⟩ := hJ
  have hI₀W : I₀ ≤ wTil (⊥ : Subgroup G) V hV L := by
    rw [← hsum]
    exact le_trans le_sup_left le_sup_left
  have hinv : ∀ x ∈ lBar (⊥ : Subgroup G) V hV L, ∀ v ∈ I₀, x v ∈ I₀ :=
    fun x hx v hv => hi₀.1 ⟨x, hx⟩ v hv
  have hnt : ∃ x ∈ lBar (⊥ : Subgroup G) V hV L, ∃ v ∈ I₀, x v ≠ v :=
    s16c167_isIrr_action_nontrivial' hi₀ hc₀
  have hfix : ∀ v ∈ I₀, l v = v := fun v hv => hlC v (hI₀W hv)
  exact Subgroup.mem_bot.2 (rank3_inj hLbar hinv hnt l hlL hfix)

theorem s16c167_twenty_nine_swap (D : Data G) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hC : Counterex16 D ⊥ V L hV) {A : Subgroup G} {g : G} {Δ : Set (Subgroup G)}
    (hA : Choice1613 D ⊥ V hV L A) (hAel : IsElemAbelian 2 A)
    (hΔ : Concl1617 D ⊥ V hV L A g Δ) (h9 : Case168_9 D ⊥ V hV L) :
    ∃ (I₀ I₁ : Subgroup G) (a : G), Swap20 A V I₀ I₁ a ∧
      (∀ B' : Subgroup G, B' ≤ A → (∀ b ∈ B', conjSubgroup I₀ b = I₀) →
        8 ≤ Nat.card ↥(I₀ ⊓ centralizer (B' : Set G))) := by
  classical
  have hM : D.M ≤ normalizer (V : Set G) := hC.setting.hyp16.hyp125.normalizer_eq.ge
  have hAM : A ≤ D.M := hA.1.1.trans D.sylowM.le
  have hAst : A ≤ stabTil (⊥ : Subgroup G) V :=
    fun x hx => s16c167_mem_stabTil_bot (hM (hAM hx))
  have hW2 : ∀ w : Vtil (⊥ : Subgroup G) V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one ⊥ V hV
  have hLbar : IsPSL 3 2 1 ↥(lBar (⊥ : Subgroup G) V hV L) := s16c167_isPSL_of_isL3 h9.2.1
  have hJ : NatSum3 (lBar (⊥ : Subgroup G) V hV L) (wTil (⊥ : Subgroup G) V hV L) :=
    s16c167_natSum3_of_sumOfNat h9.2.2.2.1
  obtain ⟨Z, hZle, hZcard, hZcent, hZnorm, hZL, hZJ, hZf, hN⟩ :=
    s16c167_case9_frame D hC hΔ h9
  have hMbarNorm : Mbar D.M (⊥ : Subgroup G) V hV ≤
      normalizer (oddBar D.M (⊥ : Subgroup G) V hV :
        Set (MulAut (Vtil (⊥ : Subgroup G) V hV))) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (relPPrimeCore_le _)).1
      (relPPrimeCore_normal Nat.prime_two _)
  have hnotstab : ¬ barSub (⊥ : Subgroup G) V hV A ≤
      stabSub (wTil (⊥ : Subgroup G) V hV L) := by
    rcases hA.2 with hc | ⟨-, hc⟩
    · intro hle
      apply hc
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨b, hbA, rfl⟩ := (mem_barSub (⊥ : Subgroup G) V hV A x).1 hx
      have hb2 : b ^ 2 = 1 := by
        apply Subtype.ext
        exact hAel.2 (b : G) hbA
      have hx2 : (actTil (⊥ : Subgroup G) V hV b) ^ (2 ^ 1) = 1 := by
        rw [show (2 : ℕ) ^ 1 = 2 by norm_num, ← map_pow, hb2, map_one]
      have hxMbar : actTil (⊥ : Subgroup G) V hV b ∈ Mbar D.M (⊥ : Subgroup G) V hV :=
        actTil_mem_barSub (⊥ : Subgroup G) V hV (hAM hbA) b.2
      have hxWtil : (wTil (⊥ : Subgroup G) V hV L).map
          (actTil (⊥ : Subgroup G) V hV b).toMonoidHom =
          wTil (⊥ : Subgroup G) V hV L := by
        have h1 : actTil (⊥ : Subgroup G) V hV b ∈
            stabSub (wTil (⊥ : Subgroup G) V hV L) :=
          hle (actTil_mem_barSub (⊥ : Subgroup G) V hV hbA b.2)
        rw [mem_stabSub] at h1
        ext u
        rw [Subgroup.mem_map]
        constructor
        · rintro ⟨v, hv, hvu⟩
          rw [← hvu]
          exact (h1 v).2 hv
        · intro hu
          refine ⟨(actTil (⊥ : Subgroup G) V hV b)⁻¹ u, ?_, ?_⟩
          · refine (h1 ((actTil (⊥ : Subgroup G) V hV b)⁻¹ u)).1 ?_
            rw [mulAut_apply_inv_apply]
            exact hu
          · exact mulAut_apply_inv_apply _ _
      have hxZ : Z.map (MulAut.conj (actTil (⊥ : Subgroup G) V hV b)).toMonoidHom = Z :=
        hZnorm _ hxMbar
      have hxL : (lBar (⊥ : Subgroup G) V hV L).map
          (MulAut.conj (actTil (⊥ : Subgroup G) V hV b)).toMonoidHom =
          lBar (⊥ : Subgroup G) V hV L :=
        hN _ hxMbar hxWtil
      have hZc := (s16c167_natSum3_normalizer_two hW2 hLbar hJ hZcard hZL hZJ hZf
        hx2 hxZ hxL hxWtil).2
      have hZodd : Odd (Nat.card ↥Z) := by rw [hZcard]; norm_num
      have hZn : ∀ z ∈ oddBar D.M (⊥ : Subgroup G) V hV, ∀ z' ∈ Z,
          z * z' * z⁻¹ ∈ Z := by
        intro z hz z' hz'
        have hzMbar : z ∈ Mbar D.M (⊥ : Subgroup G) V hV := relPPrimeCore_le _ hz
        have h1 := hZnorm z hzMbar
        have hmem : MulAut.conj z z' ∈ Z.map (MulAut.conj z).toMonoidHom :=
          Subgroup.mem_map_of_mem _ hz'
        rwa [h1] at hmem
      have hxO : ∀ z ∈ oddBar D.M (⊥ : Subgroup G) V hV,
          actTil (⊥ : Subgroup G) V hV b * z * (actTil (⊥ : Subgroup G) V hV b)⁻¹ ∈
            oddBar D.M (⊥ : Subgroup G) V hV := by
        intro z hz
        have h1 : actTil (⊥ : Subgroup G) V hV b ∈
            normalizer (oddBar D.M (⊥ : Subgroup G) V hV :
              Set (MulAut (Vtil (⊥ : Subgroup G) V hV))) := hMbarNorm hxMbar
        exact (Subgroup.mem_normalizer_iff.1 h1 z).1 hz
      have hcentO := s16c167_odd_centralizes hZle hZodd hZn hZcent hx2 hxO hZc
      exact hcentO y hy
    · exact hc
  obtain ⟨φ, hφmem, hφnot⟩ : ∃ φ ∈ barSub (⊥ : Subgroup G) V hV A,
      φ ∉ stabSub (wTil (⊥ : Subgroup G) V hV L) := by
    by_contra h
    exact hnotstab fun x hx => by
      by_contra hx2
      exact h ⟨x, hx, hx2⟩
  have hφmap : (wTil (⊥ : Subgroup G) V hV L).map φ.toMonoidHom ≠
      wTil (⊥ : Subgroup G) V hV L := by
    intro h
    apply hφnot
    rw [mem_stabSub]
    intro u
    constructor
    · intro hu
      have h1 : φ u ∈ (wTil (⊥ : Subgroup G) V hV L).map φ.toMonoidHom := by rw [h]; exact hu
      obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.1 h1
      have h2 : v = u := φ.injective hvu
      rwa [h2] at hv
    · intro hu
      have h1 : φ u ∈ (wTil (⊥ : Subgroup G) V hV L).map φ.toMonoidHom :=
        Subgroup.mem_map_of_mem _ hu
      rwa [h] at h1
  obtain ⟨b, hbA, hbφ⟩ := (mem_barSub (⊥ : Subgroup G) V hV A φ).1 hφmem
  have hΔeq : Δ = wConj D.M (⊥ : Subgroup G) V hV L := hΔ.2.2.2.2.2.2 (Or.inl h9)
  have hΔn : Δ.ncard = 2 := hΔ.1
  have hΔV : ∀ I ∈ Δ, I ≤ V := hΔ.2.1
  have hΔind : sSupIndep Δ := hΔ.2.2.1
  have hΔsup : sSup Δ = V := hΔ.2.2.2.1
  have hWmem : wSub (⊥ : Subgroup G) V hV L ∈ Δ := by
    rw [hΔeq]
    exact ⟨1, D.M.one_mem, by rw [conjSubgroup_one]⟩
  have hWleV : wSub (⊥ : Subgroup G) V hV L ≤ V := hΔV _ hWmem
  have hWtil_eq : imgTil (⊥ : Subgroup G) V hV (wSub (⊥ : Subgroup G) V hV L) =
      wTil (⊥ : Subgroup G) V hV L := by
    unfold wSub
    exact imgTil_preTil (⊥ : Subgroup G) V hV (wTil (⊥ : Subgroup G) V hV L)
  obtain ⟨I₁, hΔpair, hI₁ne⟩ : ∃ I₁ : Subgroup G,
      Δ = {wSub (⊥ : Subgroup G) V hV L, I₁} ∧ I₁ ≠ wSub (⊥ : Subgroup G) V hV L := by
    obtain ⟨a₁, b₁, hab, hΔab⟩ := Set.ncard_eq_two.1 hΔn
    have hWab : wSub (⊥ : Subgroup G) V hV L = a₁ ∨ wSub (⊥ : Subgroup G) V hV L = b₁ := by
      have hmem : wSub (⊥ : Subgroup G) V hV L ∈ ({a₁, b₁} : Set (Subgroup G)) := by
        rw [← hΔab]; exact hWmem
      simpa using hmem
    rcases hWab with h | h
    · exact ⟨b₁, by rw [h]; exact hΔab, fun hba => hab (h.symm.trans hba.symm)⟩
    · exact ⟨a₁, by rw [h, Set.pair_comm]; exact hΔab, by rw [h]; exact hab⟩
  have hI₁mem : I₁ ∈ Δ := by rw [hΔpair]; exact Set.mem_insert_iff.2 (Or.inr rfl)
  have hI₁leV : I₁ ≤ V := hΔV _ hI₁mem
  have hcj : imgTil (⊥ : Subgroup G) V hV '' Δ =
      conjSubs (Mbar D.M (⊥ : Subgroup G) V hV) (wTil (⊥ : Subgroup G) V hV L) := by
    rw [hΔeq]
    exact s16c167_imgTil_wConj hV hM L
  have hconjSubs_eq : conjSubs (Mbar D.M (⊥ : Subgroup G) V hV)
      (wTil (⊥ : Subgroup G) V hV L) =
      {wTil (⊥ : Subgroup G) V hV L, imgTil (⊥ : Subgroup G) V hV I₁} := by
    rw [← hcj, hΔpair, Set.image_pair, hWtil_eq]
  have hWtil_ne_I₁ : wTil (⊥ : Subgroup G) V hV L ≠ imgTil (⊥ : Subgroup G) V hV I₁ := by
    intro h
    apply hI₁ne
    apply s16c167_imgTil_inj' hV hI₁leV hWleV
    rw [hWtil_eq, ← h]
  have hWtil_mem_conjSubs : wTil (⊥ : Subgroup G) V hV L ∈
      conjSubs (Mbar D.M (⊥ : Subgroup G) V hV) (wTil (⊥ : Subgroup G) V hV L) :=
    ⟨1, (Mbar D.M (⊥ : Subgroup G) V hV).one_mem, by ext; simp⟩
  have hmem_conjSubs : ∀ x : G, ∀ hx : x ∈ A,
      (wTil (⊥ : Subgroup G) V hV L).map
        (actTil (⊥ : Subgroup G) V hV ⟨x, hAst hx⟩).toMonoidHom ∈
      conjSubs (Mbar D.M (⊥ : Subgroup G) V hV) (wTil (⊥ : Subgroup G) V hV L) := by
    intro x hx
    exact s16c167_mem_conjSubs_map hWtil_mem_conjSubs
      (actTil_mem_barSub (⊥ : Subgroup G) V hV (hAM hx) (hAst hx))
  have hmem_conjSubs_I₁ : ∀ x : G, ∀ hx : x ∈ A,
      (imgTil (⊥ : Subgroup G) V hV I₁).map
        (actTil (⊥ : Subgroup G) V hV ⟨x, hAst hx⟩).toMonoidHom ∈
      conjSubs (Mbar D.M (⊥ : Subgroup G) V hV) (wTil (⊥ : Subgroup G) V hV L) := by
    intro x hx
    refine s16c167_mem_conjSubs_map ?_
      (actTil_mem_barSub (⊥ : Subgroup G) V hV (hAM hx) (hAst hx))
    rw [← hcj]
    exact Set.mem_image_of_mem _ hI₁mem
  have hdich : ∀ x : G, ∀ hx : x ∈ A,
      ((wTil (⊥ : Subgroup G) V hV L).map
          (actTil (⊥ : Subgroup G) V hV ⟨x, hAst hx⟩).toMonoidHom =
        wTil (⊥ : Subgroup G) V hV L ∧
       (imgTil (⊥ : Subgroup G) V hV I₁).map
          (actTil (⊥ : Subgroup G) V hV ⟨x, hAst hx⟩).toMonoidHom =
        imgTil (⊥ : Subgroup G) V hV I₁) ∨
      ((wTil (⊥ : Subgroup G) V hV L).map
          (actTil (⊥ : Subgroup G) V hV ⟨x, hAst hx⟩).toMonoidHom =
        imgTil (⊥ : Subgroup G) V hV I₁ ∧
       (imgTil (⊥ : Subgroup G) V hV I₁).map
          (actTil (⊥ : Subgroup G) V hV ⟨x, hAst hx⟩).toMonoidHom =
        wTil (⊥ : Subgroup G) V hV L) := by
    intro x hx
    have h1 := hmem_conjSubs x hx
    have h2 := hmem_conjSubs_I₁ x hx
    rw [hconjSubs_eq] at h1 h2
    have hinj : Function.Injective (fun Y : Subgroup (Vtil (⊥ : Subgroup G) V hV) =>
        Y.map (actTil (⊥ : Subgroup G) V hV ⟨x, hAst hx⟩).toMonoidHom) :=
      Subgroup.map_injective (actTil (⊥ : Subgroup G) V hV ⟨x, hAst hx⟩).injective
    rcases h1 with h1 | h1
    · left
      refine ⟨h1, ?_⟩
      rcases h2 with h2 | h2
      · exact absurd (hinj (h2.trans h1.symm)) (Ne.symm hWtil_ne_I₁)
      · exact h2
    · right
      refine ⟨h1, ?_⟩
      rcases h2 with h2 | h2
      · exact h2
      · exact absurd (hinj (h2.trans h1.symm)) (Ne.symm hWtil_ne_I₁)
  have hacts : ∀ x ∈ A,
      (conjSubgroup (wSub (⊥ : Subgroup G) V hV L) x = wSub (⊥ : Subgroup G) V hV L ∧
        conjSubgroup I₁ x = I₁) ∨
      (conjSubgroup (wSub (⊥ : Subgroup G) V hV L) x = I₁ ∧
        conjSubgroup I₁ x = wSub (⊥ : Subgroup G) V hV L) := by
    intro x hx
    have hc0 : imgTil (⊥ : Subgroup G) V hV
        (conjSubgroup (wSub (⊥ : Subgroup G) V hV L) x) =
        (imgTil (⊥ : Subgroup G) V hV (wSub (⊥ : Subgroup G) V hV L)).map
          (actTil (⊥ : Subgroup G) V hV ⟨x, hAst hx⟩).toMonoidHom :=
      s16c167_imgTil_conjSubgroup hV (hAst hx) (hAel.2 x hx) _
    have hc1 : imgTil (⊥ : Subgroup G) V hV (conjSubgroup I₁ x) =
        (imgTil (⊥ : Subgroup G) V hV I₁).map
          (actTil (⊥ : Subgroup G) V hV ⟨x, hAst hx⟩).toMonoidHom :=
      s16c167_imgTil_conjSubgroup hV (hAst hx) (hAel.2 x hx) _
    have hxV : conjSubgroup V x = V := conjSubgroup_eq_iff_mem_normalizer.2 (hM (hAM hx))
    have hle0 : conjSubgroup (wSub (⊥ : Subgroup G) V hV L) x ≤ V :=
      (E3.conjSubgroup_mono_left x hWleV).trans (le_of_eq hxV)
    have hle1 : conjSubgroup I₁ x ≤ V :=
      (E3.conjSubgroup_mono_left x hI₁leV).trans (le_of_eq hxV)
    rcases hdich x hx with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · left
      refine ⟨?_, ?_⟩
      · apply s16c167_imgTil_inj' hV hle0 hWleV
        rw [hc0, hWtil_eq, h0]
      · apply s16c167_imgTil_inj' hV hle1 hI₁leV
        rw [hc1, h1]
    · right
      refine ⟨?_, ?_⟩
      · apply s16c167_imgTil_inj' hV hle0 hI₁leV
        rw [hc0, hWtil_eq, h0]
      · apply s16c167_imgTil_inj' hV hle1 hWleV
        rw [hc1, h1, hWtil_eq]
  have hφeq' : actTil (⊥ : Subgroup G) V hV ⟨(b : G), hAst hbA⟩ = φ := by
    rw [show (⟨(b : G), hAst hbA⟩ : stabTil (⊥ : Subgroup G) V) = b from Subtype.ext rfl]
    exact hbφ
  have hswapWtil : (wTil (⊥ : Subgroup G) V hV L).map φ.toMonoidHom =
      imgTil (⊥ : Subgroup G) V hV I₁ := by
    have hmem := hmem_conjSubs (b : G) hbA
    rw [hφeq', hconjSubs_eq] at hmem
    rcases hmem with h | h
    · exact absurd h hφmap
    · exact h
  have hswap : conjSubgroup (wSub (⊥ : Subgroup G) V hV L) (b : G) = I₁ := by
    refine s16c167_imgTil_inj' hV ?_ hI₁leV ?_
    · have hbV : conjSubgroup V (b : G) = V :=
        conjSubgroup_eq_iff_mem_normalizer.2 (hM (hAM hbA))
      exact (E3.conjSubgroup_mono_left (b : G) hWleV).trans (le_of_eq hbV)
    · rw [s16c167_imgTil_conjSubgroup hV (hAst hbA) (hAel.2 (b : G) hbA) _,
        hWtil_eq, hφeq', hswapWtil]
  refine ⟨wSub (⊥ : Subgroup G) V hV L, I₁, (b : G), ?_, ?_⟩
  · refine ⟨hWleV, hI₁leV, ?_, ?_, ?_, hbA, ?_, hacts⟩
    · intro hbot
      have h1 : wTil (⊥ : Subgroup G) V hV L = ⊥ := by
        rw [← hWtil_eq, hbot]
        unfold imgTil intSub
        rw [Subgroup.bot_subgroupOf]
        exact Subgroup.map_bot (f := mkTil (⊥ : Subgroup G) V hV)
      have h2 : rk ↥(wTil (⊥ : Subgroup G) V hV L) = 9 := s16c167_rk_natSum3 hJ
      rw [h1, rk_bot] at h2
      exact absurd h2 (by norm_num)
    · have hind : sSupIndep ({wSub (⊥ : Subgroup G) V hV L, I₁} : Set (Subgroup G)) := by
        rw [← hΔpair]; exact hΔind
      have hdisj := (sSupIndep_pair (fun h => hI₁ne h.symm)).1 hind
      exact disjoint_iff.1 hdisj
    · have hsup := hΔsup
      rw [hΔpair, sSup_pair] at hsup
      exact hsup
    · exact hswap
  · intro B' hB'A hB'fix
    have hB'stab : B' ≤ stabTil (⊥ : Subgroup G) V :=
      fun x hx => s16c167_mem_stabTil_bot (hM (hAM (hB'A hx)))
    let Wt : Subgroup (Vtil (⊥ : Subgroup G) V hV) := wTil (⊥ : Subgroup G) V hV L
    let Lb : Subgroup (MulAut (Vtil (⊥ : Subgroup G) V hV)) := lBar (⊥ : Subgroup G) V hV L
    let Xb : Subgroup (MulAut (Vtil (⊥ : Subgroup G) V hV)) := barSub (⊥ : Subgroup G) V hV B'
    let ρ : ↥(stabSub Wt) →* MulAut Wt := resHom Wt
    let A' : Subgroup (MulAut Wt) := autSub Xb Wt
    let Q : Subgroup (MulAut (Vtil (⊥ : Subgroup G) V hV)) :=
      Lb ⊓ (A'.comap ρ).map (stabSub Wt).subtype
    have hLbStab : Lb ≤ stabSub Wt := s16c167_lBar_le_stabSub_wTil hV
    have hLbCent : Lb ⊓ centSub Wt = ⊥ := s16c167_lBar_inf_centSub_wTil_eq_bot hV hLbar hJ
    have hXbWt : ∀ φ ∈ Xb, Wt.map φ.toMonoidHom = Wt := by
      intro φ hφ
      obtain ⟨bb, hbbB, hbbφ⟩ := (mem_barSub (⊥ : Subgroup G) V hV B' φ).1 hφ
      have hbbA : (bb : G) ∈ A := hB'A hbbB
      have hbb2 : (bb : G) ^ 2 = 1 := hAel.2 (bb : G) hbbA
      have h1 : imgTil (⊥ : Subgroup G) V hV
          (conjSubgroup (wSub (⊥ : Subgroup G) V hV L) (bb : G)) =
          (imgTil (⊥ : Subgroup G) V hV (wSub (⊥ : Subgroup G) V hV L)).map
            (actTil (⊥ : Subgroup G) V hV bb).toMonoidHom :=
        s16c167_imgTil_conjSubgroup hV bb.2 hbb2 _
      rw [hB'fix (bb : G) hbbB, hWtil_eq] at h1
      rw [← hbbφ]
      exact h1.symm
    have hXbStab : Xb ≤ stabSub Wt := by
      intro φ hφ
      rw [mem_stabSub]
      intro u
      have h := hXbWt φ hφ
      constructor
      · intro hu
        have h1 : φ u ∈ Wt.map φ.toMonoidHom := by rw [h]; exact hu
        obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.1 h1
        have h3 : v = u := φ.injective hvu
        rwa [h3] at hv
      · intro hu
        have h1 : φ u ∈ Wt.map φ.toMonoidHom := Subgroup.mem_map_of_mem _ hu
        rwa [h] at h1
    have hXbp : IsPGroup 2 ↥Xb := by
      let incl : ↥B' →* ↥(stabTil (⊥ : Subgroup G) V) :=
        { toFun := fun b => ⟨(b : G), hB'stab b.2⟩
          map_one' := Subtype.ext rfl
          map_mul' := fun _ _ => Subtype.ext rfl }
      let f : ↥B' →* MulAut (Vtil (⊥ : Subgroup G) V hV) :=
        (actTil (⊥ : Subgroup G) V hV).comp incl
      have hB'p : IsPGroup 2 ↥B' :=
        B2F.isPGroup_of_isElemAbelian (B2F.isElemAbelian_mono hB'A hAel)
      have hrange : (⊤ : Subgroup ↥B').map f = Xb := by
        ext φ
        constructor
        · rintro ⟨b, -, rfl⟩
          exact actTil_mem_barSub (⊥ : Subgroup G) V hV b.2 (hB'stab b.2)
        · intro hφ
          obtain ⟨gg, hgB, hgφ⟩ := (mem_barSub (⊥ : Subgroup G) V hV B' φ).1 hφ
          refine ⟨⟨(gg : G), hgB⟩, Subgroup.mem_top _, ?_⟩
          show f ⟨(gg : G), hgB⟩ = φ
          rw [← hgφ]
          rfl
      rw [← hrange]
      exact IsPGroup.map (H := ⊤) (hB'p.of_equiv Subgroup.topEquiv.symm) f
    have hA'p : IsPGroup 2 ↥A' := by
      have h1 : IsPGroup 2 ↥(Xb.subgroupOf (stabSub Wt)) := by
        rw [← Subgroup.comap_subtype Xb (stabSub Wt)]
        exact hXbp.comap_of_injective (stabSub Wt).subtype Subtype.coe_injective
      have h2 : IsPGroup 2 ↥((Xb.subgroupOf (stabSub Wt)).map ρ) := IsPGroup.map h1 ρ
      show IsPGroup 2 ↥((Xb.subgroupOf (stabSub Wt)).map (resHom Wt))
      exact h2
    have hQp : IsPGroup 2 ↥Q := by
      rw [isPGroup_iff_pow_pow_eq_one]
      intro q
      have hqL : (q : MulAut (Vtil (⊥ : Subgroup G) V hV)) ∈ Lb := q.2.1
      have hqcomap : (q : MulAut (Vtil (⊥ : Subgroup G) V hV)) ∈
          (A'.comap ρ).map (stabSub Wt).subtype := q.2.2
      obtain ⟨gg, hgA', hgq⟩ := Subgroup.mem_map.1 hqcomap
      obtain ⟨n, hn⟩ := (isPGroup_iff_pow_pow_eq_one.1 hA'p) ⟨ρ gg, hgA'⟩
      have hn' : (ρ gg) ^ (2 ^ n) = 1 := congrArg Subtype.val hn
      refine ⟨n, Subtype.ext ?_⟩
      have hcent : (q : MulAut (Vtil (⊥ : Subgroup G) V hV)) ^ (2 ^ n) ∈ centSub Wt := by
        rw [mem_centSub]
        intro u hu
        have h1 : resHom Wt (gg ^ (2 ^ n)) = 1 := by rw [map_pow, hn']
        have h2 : (resHom Wt (gg ^ (2 ^ n))) ⟨u, hu⟩ = ⟨u, hu⟩ := by rw [h1]; rfl
        have h3 := resHom_apply Wt (gg ^ (2 ^ n)) ⟨u, hu⟩
        rw [h2] at h3
        have h4 : (gg ^ (2 ^ n) : MulAut (Vtil (⊥ : Subgroup G) V hV)) u = u := h3.symm
        rw [← hgq]
        exact h4
      have hmem : (q : MulAut (Vtil (⊥ : Subgroup G) V hV)) ^ (2 ^ n) ∈ Lb ⊓ centSub Wt :=
        ⟨Lb.pow_mem hqL _, hcent⟩
      rw [hLbCent, Subgroup.mem_bot] at hmem
      exact hmem
    have hbar_exists : ∀ φ ∈ Xb, ∃ l ∈ Lb, ∀ w ∈ Wt, φ w = l w := by
      intro φ hφ
      obtain ⟨bb, hbbB, hbbφ⟩ := (mem_barSub (⊥ : Subgroup G) V hV B' φ).1 hφ
      have hbbA : (bb : G) ∈ A := hB'A hbbB
      have hbb2 : bb ^ 2 = 1 := by
        apply Subtype.ext
        exact hAel.2 (bb : G) hbbA
      have hφ2 : φ ^ (2 ^ 1) = 1 := by
        rw [show (2 : ℕ) ^ 1 = 2 by norm_num, ← hbbφ, ← map_pow, hbb2, map_one]
      have hφMbar : φ ∈ Mbar D.M (⊥ : Subgroup G) V hV := by
        rw [← hbbφ]
        exact actTil_mem_barSub (⊥ : Subgroup G) V hV (hAM hbbA) bb.2
      have hφZ : Z.map (MulAut.conj φ).toMonoidHom = Z := hZnorm φ hφMbar
      have hφL : Lb.map (MulAut.conj φ).toMonoidHom = Lb := hN φ hφMbar (hXbWt φ hφ)
      exact (s16c167_natSum3_normalizer_two hW2 hLbar hJ hZcard hZL hZJ hZf
        hφ2 hφZ hφL (hXbWt φ hφ)).1
    have hfixQ : Wt ⊓ fixV Q = Wt ⊓ fixV Xb := by
      ext u
      rw [Subgroup.mem_inf, Subgroup.mem_inf, mem_fixV, mem_fixV]
      constructor
      · rintro ⟨huW, huQ⟩
        refine ⟨huW, ?_⟩
        intro φ hφ
        obtain ⟨l, hlL, hlw⟩ := hbar_exists φ hφ
        have hlA' : ρ ⟨l, hLbStab hlL⟩ ∈ A' := by
          have h1 : ρ ⟨l, hLbStab hlL⟩ = ρ ⟨φ, hXbStab hφ⟩ := by
            ext u
            rw [resHom_apply, resHom_apply]
            exact (hlw (u : Vtil (⊥ : Subgroup G) V hV) u.2).symm
          rw [h1]
          show ρ ⟨φ, hXbStab hφ⟩ ∈ (Xb.subgroupOf (stabSub Wt)).map ρ
          exact Subgroup.mem_map.2 ⟨⟨φ, hXbStab hφ⟩, hφ, rfl⟩
        have hlQ : l ∈ Q :=
          ⟨hlL, Subgroup.mem_map.2 ⟨⟨l, hLbStab hlL⟩, hlA', rfl⟩⟩
        have h1 := huQ l hlQ
        rw [← hlw u huW] at h1
        exact h1
      · rintro ⟨huW, huX⟩
        refine ⟨huW, ?_⟩
        intro q hq
        have hqL : (q : MulAut (Vtil (⊥ : Subgroup G) V hV)) ∈ Lb := hq.1
        have hqcomap : (q : MulAut (Vtil (⊥ : Subgroup G) V hV)) ∈
            (A'.comap ρ).map (stabSub Wt).subtype := hq.2
        obtain ⟨gg, hgA', hgq⟩ := Subgroup.mem_map.1 hqcomap
        have hgA'' : ρ gg ∈ (Xb.subgroupOf (stabSub Wt)).map ρ := by
          show ρ gg ∈ A'
          exact hgA'
        obtain ⟨g₀, hg₀mem, hg₀eq⟩ := Subgroup.mem_map.1 hgA''
        have hφX : (g₀ : MulAut (Vtil (⊥ : Subgroup G) V hV)) ∈ Xb :=
          Subgroup.mem_subgroupOf.1 hg₀mem
        have hgu : (g₀ : MulAut (Vtil (⊥ : Subgroup G) V hV)) u = u := huX _ hφX
        have hqgu : (q : MulAut (Vtil (⊥ : Subgroup G) V hV)) u =
            (g₀ : MulAut (Vtil (⊥ : Subgroup G) V hV)) u := by
          have h1 : (ρ gg : MulAut Wt) ⟨u, huW⟩ = (ρ g₀ : MulAut Wt) ⟨u, huW⟩ := by
            rw [hg₀eq]
          have h2 := resHom_apply Wt gg ⟨u, huW⟩
          have h3 := resHom_apply Wt g₀ ⟨u, huW⟩
          rw [← hgq]
          have h4 : ((ρ gg) ⟨u, huW⟩ : Vtil (⊥ : Subgroup G) V hV) =
              ((ρ g₀) ⟨u, huW⟩ : Vtil (⊥ : Subgroup G) V hV) := congrArg Subtype.val h1
          exact h2.symm.trans (h4.trans h3)
        rw [hqgu, hgu]
    have h3 : 3 ≤ rk ↥(Wt ⊓ fixV Q) := s16c167_natSum3_fix_ge hJ inf_le_left hQp
    rw [hfixQ] at h3
    have hfixXb : fixV Xb = imgTil (⊥ : Subgroup G) V hV (V ⊓ centralizer (B' : Set G)) :=
      s16c167_fixV_barSub hV hB'stab
    rw [hfixXb] at h3
    have hWt_eq_img : Wt = imgTil (⊥ : Subgroup G) V hV (wSub (⊥ : Subgroup G) V hV L) :=
      hWtil_eq.symm
    rw [hWt_eq_img, ← s16c167_imgTil_inf_bot hV] at h3
    have hsub : wSub (⊥ : Subgroup G) V hV L ⊓ (V ⊓ centralizer (B' : Set G)) =
        wSub (⊥ : Subgroup G) V hV L ⊓ centralizer (B' : Set G) := by
      rw [← inf_assoc, inf_eq_left.2 hWleV]
    rw [hsub, s16c167_rk_imgTil hV (le_trans inf_le_left hWleV)] at h3
    have hNpos : Nat.card ↥(wSub (⊥ : Subgroup G) V hV L ⊓ centralizer (B' : Set G)) ≠ 0 :=
      Nat.card_pos.ne'
    have h8 : 8 ∣ Nat.card ↥(wSub (⊥ : Subgroup G) V hV L ⊓ centralizer (B' : Set G)) := by
      have h := (padicValNat_dvd_iff_le (p := 2) (n := 3) hNpos).2 h3
      simpa using h
    exact Nat.le_of_dvd Nat.card_pos h8

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
