module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3A5Inv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3A5Fix3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3A5Triv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3A5Single
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3ThCount

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

open scoped Pointwise

variable {W : Type} [CommGroup W]

private lemma s1611e3_smul_eq_map (x : MulAut W) (I : Subgroup W) :
    x • I = I.map x.toMonoidHom := by
  have hf : MulDistribMulAction.toMonoidEnd _ _ x = x.toMonoidHom := by
    ext y
    rfl
  rw [Subgroup.pointwise_smul_def, hf]

private lemma s1611e3_map_one (I : Subgroup W) :
    I.map (1 : MulAut W).toMonoidHom = I := by
  have h : (1 : MulAut W).toMonoidHom = MonoidHom.id W := MonoidHom.ext fun _ => rfl
  rw [h, Subgroup.map_id]

private lemma s1611e3_map_mul_map (a b : MulAut W) (I : Subgroup W) :
    (I.map a.toMonoidHom).map b.toMonoidHom = I.map (b * a).toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

private lemma s1611e3_map_inv (I : Subgroup W) (x : MulAut W)
    (h : I.map x.toMonoidHom = I) : I.map x⁻¹.toMonoidHom = I := by
  have h1 : (I.map x.toMonoidHom).map x⁻¹.toMonoidHom = I.map x⁻¹.toMonoidHom := by rw [h]
  rw [s1611e3_map_mul_map x x⁻¹ I, inv_mul_cancel, s1611e3_map_one] at h1
  exact h1.symm

private theorem s1611e3_isPGroup_two_of_elemAbelian2 {A : Subgroup (MulAut W)}
    (h : IsElemAbelian2 A) : IsPGroup 2 ↥A := by
  intro x
  refine ⟨1, Subtype.ext ?_⟩
  simpa using h.2 (x : MulAut W) x.2

private theorem s1611e3_card_natural [Finite W] {L : Subgroup (MulAut W)} {J : Subgroup W}
    (hJ : AlternatingNatural L J ⊥ 5) : Nat.card ↥J = 16 := by
  obtain ⟨π, hπ⟩ := hJ
  obtain ⟨f, hfs, hfk, -⟩ := CFSG.Quasithin.FFC.RealizesVia.secMap
    (D := FFModel.altDn 5) CFSG.Quasithin.FFC.altDn_ker_five hπ
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hfk u).1 hu))
  have hcard : Nat.card ↥J = Nat.card ↥(FFModel.altDn 5).sec :=
    Nat.card_congr (Equiv.ofBijective f ⟨hinj, hfs⟩)
  rw [hcard]
  exact CFSG.Quasithin.FFC.card_coreMod_five

private theorem s1611e3_natural_conj {L L' : Subgroup (MulAut W)} {N : Subgroup W}
    {x : MulAut W} (hx : L.map (MulAut.conj x).toMonoidHom = L')
    (hN : AlternatingNatural L N ⊥ 5) :
    AlternatingNatural L' (N.map x.toMonoidHom) ⊥ 5 := by
  obtain ⟨π, hπ⟩ := hN
  have hmem_inv : ∀ g : MulAut W, g ∈ L' → x⁻¹ * g * x ∈ L := by
    intro g hg
    have hg' : g ∈ L.map (MulAut.conj x).toMonoidHom := hx ▸ hg
    obtain ⟨l, hl, hl_eq⟩ := Subgroup.mem_map.1 hg'
    have hle : x⁻¹ * g * x = l := by
      have h2 : (MulAut.conj x) l = g := hl_eq
      rw [← h2, MulAut.conj_apply]
      group
    rw [hle]
    exact hl
  have hmem : ∀ l : MulAut W, l ∈ L → x * l * x⁻¹ ∈ L' := by
    intro l hl
    have h1 : x * l * x⁻¹ ∈ L.map (MulAut.conj x).toMonoidHom := by
      have h2 := Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom hl
      simpa [MulAut.conj_apply] using h2
    rwa [hx] at h1
  let e : ↥L' ≃* ↥L :=
    { toFun := fun g => ⟨x⁻¹ * (g : MulAut W) * x, hmem_inv g g.2⟩
      invFun := fun l => ⟨x * (l : MulAut W) * x⁻¹, hmem l l.2⟩
      left_inv := fun g => Subtype.ext (by group)
      right_inv := fun l => Subtype.ext (by group)
      map_mul' := fun g h => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have he : ∀ (g : ↥L') (w : W),
      x.toMonoidHom ((e g : MulAut W) w) = (g : MulAut W) (x.toMonoidHom w) := by
    intro g w
    show x ((x⁻¹ * (g : MulAut W) * x) w) = (g : MulAut W) (x w)
    simp only [MulAut.mul_apply, MulAut.apply_inv_self]
  refine ⟨e.symm.toMonoidHom.comp π, ?_⟩
  have h := CFSG.Quasithin.FFC.RealizesVia.transport x.toMonoidHom x.injective e he hπ
  simpa using h

theorem s1611e3_a5_local {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L L' Z T : Subgroup (MulAut W)} {U U' : Subgroup W}
    (hL : IsAlt ↥L 5) (hL' : IsAlt ↥L' 5) (hUU' : U ⊓ U' = ⊥) (hsup : U ⊔ U' = ⊤)
    (hsum : SumOfNat (fun H V Z => AlternatingNatural H V Z 5) L U ⊥ 2)
    (hsum' : SumOfNat (fun H V Z => AlternatingNatural H V Z 5) L' U' ⊥ 2)
    (hcomm : ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (hfixU : ∀ b ∈ L', ∀ w ∈ U, b w = w) (hfixU' : ∀ a ∈ L, ∀ w ∈ U', a w = w)
    (hZ : Nat.card ↥Z = 3) (hZL : ∀ z ∈ Z, ∀ l ∈ L, z * l = l * z)
    (hZL' : ∀ z ∈ Z, ∀ l ∈ L', z * l = l * z)
    (hZU : ∀ z ∈ Z, ∀ w ∈ U, z w ∈ U) (hZU' : ∀ z ∈ Z, ∀ w ∈ U', z w ∈ U')
    (hZf : ∀ z ∈ Z, z ≠ 1 → ∃ w ∈ U, z w ≠ w) (hZf' : ∀ z ∈ Z, z ≠ 1 → ∃ w ∈ U', z w ≠ w)
    (hT2 : IsPGroup 2 ↥T)
    (hT : ∀ x ∈ T,
      (L.map (MulAut.conj x).toMonoidHom = L ∧ L'.map (MulAut.conj x).toMonoidHom = L' ∧
        U.map x.toMonoidHom = U ∧ U'.map x.toMonoidHom = U') ∨
      (L.map (MulAut.conj x).toMonoidHom = L' ∧ L'.map (MulAut.conj x).toMonoidHom = L ∧
        U.map x.toMonoidHom = U' ∧ U'.map x.toMonoidHom = U))
    (hTZ : ∀ x ∈ T, Z.map (MulAut.conj x).toMonoidHom = Z) :
    ∃ I : Subgroup W, (∀ x ∈ T, I.map x.toMonoidHom = I) ∧
      (∀ w ∈ I, w ≠ 1 → ∃ y ∈ L ⊔ L', orderOf y = 3 ∧ y w = w) ∧
      ∀ E : Subgroup (MulAut W), E ≤ T → IsElemAbelian2 E → E ≠ ⊥ →
        ∃ B ≤ E, E3.mQuot E B = 1 ∧ ∃ u : W, (∀ b ∈ B, b u = u) ∧ (∃ e ∈ E, e u ≠ u) ∧
          ∀ e ∈ E, e u * u⁻¹ ∈ I := by
  classical
  have hZbot : Z ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hZ
    norm_num at hZ
  obtain ⟨z0, hz0ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZbot
  have hz0 : (z0 : MulAut W) ∈ Z := z0.2
  have hz0' : (z0 : MulAut W) ≠ 1 := fun h => hz0ne (Subtype.ext h)
  have hUne : U ≠ ⊥ := by
    intro hbot
    obtain ⟨w, hwU, hzw⟩ := hZf (z0 : MulAut W) hz0 hz0'
    rw [hbot, Subgroup.mem_bot] at hwU
    rw [hwU, map_one] at hzw
    exact hzw rfl
  have hUU'ne : U ≠ U' := by
    intro h
    have h1 : U ⊓ U' = U := by rw [h, inf_idem]
    rw [hUU'] at h1
    exact hUne h1.symm
  set T₀ : Subgroup (MulAut W) := T ⊓ MulAction.stabilizer (MulAut W) U with hT₀def
  have hmemT₀ : ∀ x : MulAut W, x ∈ T → U.map x.toMonoidHom = U → x ∈ T₀ := by
    intro x hxT hxU
    rw [hT₀def, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, s1611e3_smul_eq_map]
    exact ⟨hxT, hxU⟩
  have hT₀mem : ∀ x ∈ T₀, x ∈ T ∧ U.map x.toMonoidHom = U := by
    intro x hx
    rw [hT₀def, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, s1611e3_smul_eq_map] at hx
    exact hx
  have hfix_of_mem : ∀ x ∈ T₀, L.map (MulAut.conj x).toMonoidHom = L ∧
      L'.map (MulAut.conj x).toMonoidHom = L' ∧
      U.map x.toMonoidHom = U ∧ U'.map x.toMonoidHom = U' := by
    intro x hx
    obtain ⟨hxT, hxU⟩ := hT₀mem x hx
    rcases hT x hxT with hf | hs
    · exact hf
    · exact absurd (hxU.symm.trans hs.2.2.1) hUU'ne
  have hT₀T : T₀ ≤ T := fun x hx => (hT₀mem x hx).1
  have hT₀P : IsPGroup 2 ↥T₀ := hT2.to_le hT₀T
  have hconjT₀ : ∀ x ∈ T₀, ∀ t ∈ T, t⁻¹ * x * t ∈ T₀ := by
    intro x hx t ht
    obtain ⟨hxT, hxU⟩ := hT₀mem x hx
    have hxfix := hfix_of_mem x hx
    have hcomp : U.map (t⁻¹ * x * t).toMonoidHom =
        ((U.map t.toMonoidHom).map x.toMonoidHom).map t⁻¹.toMonoidHom := by
      rw [s1611e3_map_mul_map t x U, s1611e3_map_mul_map (x * t) t⁻¹ U]
      congr 1
    have hUmap : U.map (t⁻¹ * x * t).toMonoidHom = U := by
      rw [hcomp]
      rcases hT t ht with hf | hs
      · rw [hf.2.2.1, hxfix.2.2.1, s1611e3_map_inv U t hf.2.2.1]
      · have h2 : U'.map t⁻¹.toMonoidHom = U := by
          rw [← hs.2.2.1, s1611e3_map_mul_map t t⁻¹ U, inv_mul_cancel, s1611e3_map_one]
        rw [hs.2.2.1, hxfix.2.2.2, h2]
    exact hmemT₀ (t⁻¹ * x * t) (T.mul_mem (T.mul_mem (T.inv_mem ht) hxT) ht) hUmap
  obtain ⟨N₁, hN₁U, hN₁nat, hN₁inv⟩ :=
    s1611e3_a5_inv (L := L) (Z := Z) (U := U) hW hL hsum hZ hZL hZU hZf hT₀P
      (fun x hx => (hfix_of_mem x hx).1) (fun x hx => (hfix_of_mem x hx).2.2.1)
  have hN₁'ex : ∃ N₁' : Subgroup W, N₁' ≤ U' ∧ AlternatingNatural L' N₁' ⊥ 5 ∧
      (∀ x ∈ T₀, N₁'.map x.toMonoidHom = N₁') ∧
      (∀ t ∈ T, U.map t.toMonoidHom = U' → N₁.map t.toMonoidHom = N₁') ∧
      (∀ t ∈ T, U.map t.toMonoidHom = U' → N₁'.map t.toMonoidHom = N₁) := by
    by_cases hS : ∃ s ∈ T, U.map s.toMonoidHom = U'
    · obtain ⟨s, hsT, hsU⟩ := hS
      have hs_swap : L.map (MulAut.conj s).toMonoidHom = L' ∧
          L'.map (MulAut.conj s).toMonoidHom = L ∧
          U.map s.toMonoidHom = U' ∧ U'.map s.toMonoidHom = U := by
        rcases hT s hsT with hf | hs
        · exact absurd (hf.2.2.1.symm.trans hsU) hUU'ne
        · exact hs
      have hsi : U'.map s⁻¹.toMonoidHom = U := by
        rw [← hs_swap.2.2.1, s1611e3_map_mul_map s s⁻¹ U, inv_mul_cancel, s1611e3_map_one]
      refine ⟨N₁.map s.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
      · rw [← hs_swap.2.2.1]
        exact Subgroup.map_mono hN₁U
      · exact s1611e3_natural_conj hs_swap.1 hN₁nat
      · intro x hx
        have hxT : x ∈ T := hT₀T hx
        have hxs : s⁻¹ * x * s ∈ T₀ := hconjT₀ x hx s hsT
        have h1 : N₁.map (s⁻¹ * x * s).toMonoidHom = N₁ := hN₁inv _ hxs
        calc (N₁.map s.toMonoidHom).map x.toMonoidHom
            = N₁.map (x * s).toMonoidHom := s1611e3_map_mul_map s x N₁
          _ = N₁.map (s * (s⁻¹ * x * s)).toMonoidHom := by
                congr 1
                group
          _ = (N₁.map (s⁻¹ * x * s).toMonoidHom).map s.toMonoidHom :=
                (s1611e3_map_mul_map (s⁻¹ * x * s) s N₁).symm
          _ = N₁.map s.toMonoidHom := by rw [h1]
      · intro t htT htU
        have hst : s⁻¹ * t ∈ T₀ := by
          have hstU : U.map (s⁻¹ * t).toMonoidHom = U := by
            have hcomp : U.map (s⁻¹ * t).toMonoidHom = (U.map t.toMonoidHom).map s⁻¹.toMonoidHom :=
              (s1611e3_map_mul_map t s⁻¹ U).symm
            rw [hcomp, htU, hsi]
          exact hmemT₀ (s⁻¹ * t) (T.mul_mem (T.inv_mem hsT) htT) hstU
        calc N₁.map t.toMonoidHom
            = N₁.map (s * (s⁻¹ * t)).toMonoidHom := by congr 1; group
          _ = (N₁.map (s⁻¹ * t).toMonoidHom).map s.toMonoidHom :=
                (s1611e3_map_mul_map (s⁻¹ * t) s N₁).symm
          _ = N₁.map s.toMonoidHom := by rw [hN₁inv _ hst]
      · intro t htT htU
        have ht_swap : U'.map t.toMonoidHom = U := by
          rcases hT t htT with hf | hs
          · exact absurd (hf.2.2.1.symm.trans htU) hUU'ne
          · exact hs.2.2.2
        have hts : t * s ∈ T₀ := by
          have htsU : U.map (t * s).toMonoidHom = U := by
            rw [← s1611e3_map_mul_map s t U, hs_swap.2.2.1, ht_swap]
          exact hmemT₀ (t * s) (T.mul_mem htT hsT) htsU
        calc (N₁.map s.toMonoidHom).map t.toMonoidHom
            = N₁.map (t * s).toMonoidHom := s1611e3_map_mul_map s t N₁
          _ = N₁ := hN₁inv _ hts
    · have hfix' : ∀ x ∈ T, L.map (MulAut.conj x).toMonoidHom = L ∧
          L'.map (MulAut.conj x).toMonoidHom = L' ∧
          U.map x.toMonoidHom = U ∧ U'.map x.toMonoidHom = U' := by
        intro x hxT
        rcases hT x hxT with hf | hs
        · exact hf
        · exact absurd ⟨x, hxT, hs.2.2.1⟩ hS
      obtain ⟨N₁', hN₁'U', hN₁'nat, hN₁'inv⟩ :=
        s1611e3_a5_inv (L := L') (Z := Z) (U := U') hW hL' hsum' hZ hZL' hZU' hZf' hT2
          (fun x hx => (hfix' x hx).2.1) (fun x hx => (hfix' x hx).2.2.2)
      refine ⟨N₁', hN₁'U', hN₁'nat, ?_, ?_, ?_⟩
      · intro x hx
        exact hN₁'inv x (hT₀T hx)
      · intro t htT htU
        exact absurd ⟨t, htT, htU⟩ hS
      · intro t htT htU
        exact absurd ⟨t, htT, htU⟩ hS
  obtain ⟨N₁', hN₁'U', hN₁'nat, hN₁'inv, hN₁'indep, hN₁'swap⟩ := hN₁'ex
  let I : Subgroup W := N₁ ⊔ N₁'
  have hN₁I : N₁ ≤ I := le_sup_left
  have hN₁'I : N₁' ≤ I := le_sup_right
  have hIinv : ∀ x ∈ T, I.map x.toMonoidHom = I := by
    intro x hxT
    rcases hT x hxT with hf | hs
    · have hxT₀ : x ∈ T₀ := hmemT₀ x hxT hf.2.2.1
      rw [show I = N₁ ⊔ N₁' from rfl, Subgroup.map_sup, hN₁inv x hxT₀, hN₁'inv x hxT₀]
    · rw [show I = N₁ ⊔ N₁' from rfl, Subgroup.map_sup,
        hN₁'indep x hxT hs.2.2.1, hN₁'swap x hxT hs.2.2.1, sup_comm]
  have hLinfL' : L ⊓ L' = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxL, hxL'⟩ := Subgroup.mem_inf.1 hx
    apply MulEquiv.ext
    intro w
    have hw : w ∈ U ⊔ U' := by rw [hsup]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hw
    rw [MulAut.one_apply, map_mul, hfixU x hxL' a ha, hfixU' x hxL b hb]
  have hprop1 : ∀ w ∈ I, w ≠ 1 → ∃ y ∈ L ⊔ L', orderOf y = 3 ∧ y w = w := by
    intro w hwI hwne
    rw [show I = N₁ ⊔ N₁' from rfl] at hwI
    obtain ⟨n, hnN₁, n', hn'N₁', rfl⟩ := Subgroup.mem_sup.1 hwI
    obtain ⟨ℓ, hℓL, hℓn, hℓord, hℓone⟩ :
        ∃ ℓ ∈ L, ℓ n = n ∧ (n ≠ 1 → orderOf ℓ = 3) ∧ (n = 1 → ℓ = 1) := by
      by_cases hn : n = 1
      · exact ⟨1, L.one_mem, by rw [hn, map_one], fun h => (h hn).elim, fun _ => rfl⟩
      · obtain ⟨ℓ, hℓL, hℓord, hℓfix⟩ := s1611e3_a5_fix_three hL hN₁nat n hnN₁ hn
        exact ⟨ℓ, hℓL, hℓfix, fun _ => hℓord, fun h => absurd h hn⟩
    obtain ⟨ℓ', hℓ'L', hℓ'n', hℓ'ord, hℓ'one⟩ :
        ∃ ℓ' ∈ L', ℓ' n' = n' ∧ (n' ≠ 1 → orderOf ℓ' = 3) ∧ (n' = 1 → ℓ' = 1) := by
      by_cases hn : n' = 1
      · exact ⟨1, L'.one_mem, by rw [hn, map_one], fun h => (h hn).elim, fun _ => rfl⟩
      · obtain ⟨ℓ', hℓ'L', hℓ'ord, hℓ'fix⟩ := s1611e3_a5_fix_three hL' hN₁'nat n' hn'N₁' hn
        exact ⟨ℓ', hℓ'L', hℓ'fix, fun _ => hℓ'ord, fun h => absurd h hn⟩
    have hℓn' : ℓ n' = n' := hfixU' ℓ hℓL n' (hN₁'U' hn'N₁')
    have hℓ'n : ℓ' n = n := hfixU ℓ' hℓ'L' n (hN₁U hnN₁)
    refine ⟨ℓ * ℓ', (L ⊔ L').mul_mem (Subgroup.mem_sup_left hℓL)
      (Subgroup.mem_sup_right hℓ'L'), ?_, ?_⟩
    · have hℓ3 : ℓ ^ 3 = 1 := by
        by_cases hn : n = 1
        · rw [hℓone hn]; simp
        · rw [← hℓord hn]; exact pow_orderOf_eq_one ℓ
      have hℓ'3 : ℓ' ^ 3 = 1 := by
        by_cases hn : n' = 1
        · rw [hℓ'one hn]; simp
        · rw [← hℓ'ord hn]; exact pow_orderOf_eq_one ℓ'
      have hy3 : (ℓ * ℓ') ^ 3 = 1 := by
        rw [Commute.mul_pow (show Commute ℓ ℓ' from hcomm ℓ hℓL ℓ' hℓ'L') 3,
          hℓ3, hℓ'3, one_mul]
      have hy1 : ℓ * ℓ' ≠ 1 := by
        intro hy
        have hsome : n ≠ 1 ∨ n' ≠ 1 := by
          by_contra h
          rw [not_or] at h
          exact hwne (by rw [not_not.mp h.1, not_not.mp h.2, mul_one])
        rcases hsome with hn | hn'
        · have hℓ1 : ℓ ≠ 1 := by
            intro h
            rw [h, orderOf_one] at hℓord
            exact absurd (hℓord hn) (by norm_num)
          have hℓinv : ℓ = ℓ'⁻¹ := mul_eq_one_iff_eq_inv.1 hy
          have hmem : ℓ ∈ L ⊓ L' :=
            Subgroup.mem_inf.2 ⟨hℓL, by rw [hℓinv]; exact L'.inv_mem hℓ'L'⟩
          rw [hLinfL', Subgroup.mem_bot] at hmem
          exact hℓ1 hmem
        · have hℓ'1 : ℓ' ≠ 1 := by
            intro h
            rw [h, orderOf_one] at hℓ'ord
            exact absurd (hℓ'ord hn') (by norm_num)
          have hℓ'inv : ℓ' = ℓ⁻¹ := eq_inv_of_mul_eq_one_right hy
          have hmem : ℓ' ∈ L ⊓ L' :=
            Subgroup.mem_inf.2 ⟨by rw [hℓ'inv]; exact L.inv_mem hℓL, hℓ'L'⟩
          rw [hLinfL', Subgroup.mem_bot] at hmem
          exact hℓ'1 hmem
      exact orderOf_eq_prime hy3 hy1
    · show (ℓ * ℓ') (n * n') = n * n'
      rw [MulAut.mul_apply, map_mul, hℓ'n, hℓ'n', map_mul, hℓn, hℓn']
  refine ⟨I, hIinv, hprop1, ?_⟩
  intro E hET hEel hEne
  set E₀ : Subgroup (MulAut W) := E ⊓ T₀ with hE₀def
  by_cases hEeq : E = E₀
  ·
    have hET₀ : E ≤ T₀ := by
      intro x hx
      have hx' : x ∈ E₀ := hEeq ▸ hx
      have hx'' : x ∈ E ⊓ T₀ := hE₀def ▸ hx'
      exact (Subgroup.mem_inf.1 hx'').2
    by_cases htriv₁ : ∀ e ∈ E, ∀ j ∈ N₁, e j = j
    · by_cases htriv₂ : ∀ e ∈ E, ∀ j ∈ N₁', e j = j
      ·
        have htriv₁e : ∀ e ∈ E,
            ((∀ z ∈ Z, e * z = z * e) → ∀ u ∈ U, e u = u) ∧
            ((∀ z ∈ Z, e * z * e⁻¹ ∈ Z) → ∀ u ∈ U, e u * u⁻¹ ∈ N₁) := by
          intro e he
          exact s1611e3_a5_triv (L := L) (Z := Z) (U := U) (J := N₁) (e := e)
            hW hL hsum hZ hZL hZU hZf hN₁U hN₁nat
            (hfix_of_mem e (hET₀ he)).1 (hfix_of_mem e (hET₀ he)).2.2.1 (htriv₁ e he)
        have htriv₂e : ∀ e ∈ E,
            ((∀ z ∈ Z, e * z = z * e) → ∀ u ∈ U', e u = u) ∧
            ((∀ z ∈ Z, e * z * e⁻¹ ∈ Z) → ∀ u ∈ U', e u * u⁻¹ ∈ N₁') := by
          intro e he
          exact s1611e3_a5_triv (L := L') (Z := Z) (U := U') (J := N₁') (e := e)
            hW hL' hsum' hZ hZL' hZU' hZf' hN₁'U' hN₁'nat
            (hfix_of_mem e (hET₀ he)).2.1 (hfix_of_mem e (hET₀ he)).2.2.2 (htriv₂ e he)
        have hnormZ : ∀ e ∈ E, ∀ z ∈ Z, e * z * e⁻¹ ∈ Z := by
          intro e he z hz
          have h := hTZ e (hET he)
          have hzmap : (MulAut.conj e) z ∈ Z.map (MulAut.conj e).toMonoidHom :=
            Subgroup.mem_map_of_mem _ hz
          rw [h] at hzmap
          simpa [MulAut.conj_apply] using hzmap
        have hIu : ∀ e ∈ E, ∀ u : W, e u * u⁻¹ ∈ I := by
          intro e he u
          have hu : u ∈ U ⊔ U' := by rw [hsup]; trivial
          obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hu
          have h1 : e a * a⁻¹ ∈ N₁ := (htriv₁e e he).2 (hnormZ e he) a ha
          have h2 : e b * b⁻¹ ∈ N₁' := (htriv₂e e he).2 (hnormZ e he) b hb
          have heq : e (a * b) * (a * b)⁻¹ = (e a * a⁻¹) * (e b * b⁻¹) := by
            rw [map_mul, mul_inv_rev]
            ac_rfl
          rw [heq]
          exact I.mul_mem (hN₁I h1) (hN₁'I h2)
        have hker : ∀ e ∈ E, (∀ z ∈ Z, e * z = z * e) → e = 1 := by
          intro e he hcen
          have hU : ∀ u ∈ U, e u = u := (htriv₁e e he).1 hcen
          have hU' : ∀ u ∈ U', e u = u := (htriv₂e e he).1 hcen
          apply MulEquiv.ext
          intro w
          have hw : w ∈ U ⊔ U' := by rw [hsup]; trivial
          obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hw
          rw [map_mul, hU a ha, hU' b hb, MulAut.one_apply]
        have hE₀el : IsElemAbelian2 E₀ := by
          refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
          · have ha' : a ∈ E ∧ a ∈ T₀ := by
              have h : a ∈ E ⊓ T₀ := hE₀def ▸ ha
              exact Subgroup.mem_inf.1 h
            have hb' : b ∈ E ∧ b ∈ T₀ := by
              have h : b ∈ E ⊓ T₀ := hE₀def ▸ hb
              exact Subgroup.mem_inf.1 h
            exact hEel.1 a ha'.1 b hb'.1
          · have ha' : a ∈ E ∧ a ∈ T₀ := by
              have h : a ∈ E ⊓ T₀ := hE₀def ▸ ha
              exact Subgroup.mem_inf.1 h
            exact hEel.2 a ha'.1
        have hE₂p : IsPGroup 2 ↥E := s1611e3_isPGroup_two_of_elemAbelian2 hEel
        have hE₀p : IsPGroup 2 ↥E₀ := s1611e3_isPGroup_two_of_elemAbelian2 hE₀el
        have hE₀N : ∀ x ∈ E₀, N₁.map x.toMonoidHom = N₁ := by
          intro x hx
          have hx' : x ∈ E ∧ x ∈ T₀ := by
            have h : x ∈ E ⊓ T₀ := hE₀def ▸ hx
            exact Subgroup.mem_inf.1 h
          exact hN₁inv x hx'.2
        have hz0gen : Subgroup.zpowers (z0 : MulAut W) = Z := by
          have hord : orderOf (z0 : MulAut W) = 3 := by
            have hdvd : orderOf (z0 : MulAut W) ∣ 3 := by
              rw [← hZ]; exact Subgroup.orderOf_dvd_natCard Z hz0
            rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
            · exact absurd (orderOf_eq_one_iff.1 h) hz0'
            · exact h
          refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le_of_mem hz0) ?_
          simp [Nat.card_zpowers, hord, hZ]
        have hfmem : ∀ e : ↥E, (e : MulAut W) * z0 * (e : MulAut W)⁻¹ ∈ Z := by
          intro e
          have h := hTZ (e : MulAut W) (hET e.2)
          have hzmap : (MulAut.conj (e : MulAut W)) z0 ∈
              Z.map (MulAut.conj (e : MulAut W)).toMonoidHom :=
            Subgroup.mem_map_of_mem _ hz0
          rw [h] at hzmap
          simpa [MulAut.conj_apply] using hzmap
        let f : ↥E → ↥Z := fun e => ⟨(e : MulAut W) * z0 * (e : MulAut W)⁻¹, hfmem e⟩
        have hfinj : Function.Injective f := by
          intro e1 e2 heq
          have h1 : (e1 : MulAut W) * z0 * (e1 : MulAut W)⁻¹ =
              (e2 : MulAut W) * z0 * (e2 : MulAut W)⁻¹ := congrArg Subtype.val heq
          have h2 : (e2 : MulAut W)⁻¹ * ((e1 : MulAut W) * z0 * (e1 : MulAut W)⁻¹) *
              (e2 : MulAut W) = z0 := by
            rw [h1]
            group
          let c : MulAut W := (e2 : MulAut W)⁻¹ * (e1 : MulAut W)
          have hc : c * z0 = z0 * c := by
            have h3 : c * z0 * c⁻¹ = z0 := by
              show ((e2 : MulAut W)⁻¹ * (e1 : MulAut W)) * z0 *
                ((e2 : MulAut W)⁻¹ * (e1 : MulAut W))⁻¹ = z0
              rw [mul_inv_rev, inv_inv]
              simpa only [mul_assoc] using h2
            calc c * z0 = c * z0 * c⁻¹ * c := by group
              _ = z0 * c := by rw [h3]
          have hccen : ∀ z ∈ Z, c * z = z * c := by
            intro z hz
            have hz' : z ∈ Subgroup.zpowers (z0 : MulAut W) := by
              rw [hz0gen]
              exact hz
            obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz'
            have hk' : (z0 : MulAut W) ^ k = z := hk
            rw [← hk']
            exact (Commute.zpow_right (show Commute c (z0 : MulAut W) from hc) k)
          have hcE : c ∈ E := E.mul_mem (E.inv_mem e2.2) e1.2
          have hc1 : c = 1 := hker c hcE hccen
          exact Subtype.ext (show (e1 : MulAut W) = (e2 : MulAut W) from by
            have h := congrArg (fun x : MulAut W => (e2 : MulAut W) * x) hc1
            simp only [mul_one] at h
            rw [show c = (e2 : MulAut W)⁻¹ * (e1 : MulAut W) from rfl] at h
            rw [← h]
            group)
        have hle : Nat.card ↥E ≤ Nat.card ↥Z := Nat.card_le_card_of_injective f hfinj
        have hcardE : Nat.card ↥E = 2 := by
          obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hE₂p
          have hkpos : 0 < k := by
            rcases Nat.eq_zero_or_pos k with h | h
            · subst h
              rw [pow_zero] at hk
              exact absurd (Subgroup.eq_bot_of_card_eq E hk) hEne
            · exact h
          have hk3 : 2 ^ k ≤ 3 := by
            rw [← hk]
            exact hle.trans (le_of_eq hZ)
          have hklt : k < 2 := by
            by_contra h
            have hk2 : 2 ≤ k := by omega
            have h4 : 4 ≤ 2 ^ k := by
              calc 4 = 2 ^ 2 := by norm_num
                _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hk2
            omega
          have hk1 : k = 1 := by omega
          rw [hk, hk1, pow_one]
        have hmq : E3.mQuot E ⊥ = 1 := by
          unfold E3.mQuot
          rw [Subgroup.relIndex_bot_left, hcardE]
          exact padicValNat_self
        obtain ⟨e₁, he₁E, he₁ne⟩ : ∃ e : MulAut W, e ∈ E ∧ e ≠ 1 := by
          obtain ⟨e, hene⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hEne
          exact ⟨e, e.2, fun h => hene (Subtype.ext h)⟩
        obtain ⟨u, hu⟩ : ∃ u : W, e₁ u ≠ u := by
          by_contra h
          apply he₁ne
          apply MulEquiv.ext
          intro w
          by_contra hne
          exact h ⟨w, hne⟩
        refine ⟨⊥, bot_le, hmq, u, ?_, ⟨e₁, he₁E, hu⟩, ?_⟩
        · intro b hb
          rw [Subgroup.mem_bot] at hb
          rw [hb]
          rfl
        · intro e he
          exact hIu e he u
      ·
        have hE1 : ∃ e ∈ E, ∃ j ∈ N₁', e j ≠ j := by
          by_contra h
          apply htriv₂
          intro e he j hj
          by_contra hne
          exact h ⟨e, he, j, hj, hne⟩
        obtain ⟨B, hBE, hmq, u, huN₁', hufix, e0, he0E, he0u⟩ :=
          s1611e3_a5_single (L := L') (J := N₁') (E := E) hW hL' hN₁'nat hEel
            (fun e he => (hfix_of_mem e (hET₀ he)).2.1)
            (fun e he => hN₁'inv e (hET₀ he)) hE1
        refine ⟨B, hBE, hmq, u, hufix, ⟨e0, he0E, he0u⟩, ?_⟩
        intro e he
        have hmem : e u ∈ N₁' := by
          have h := hN₁'inv e (hET₀ he)
          exact h ▸ Subgroup.mem_map_of_mem e.toMonoidHom huN₁'
        exact hN₁'I (N₁'.mul_mem hmem (N₁'.inv_mem huN₁'))
    ·
      have hE1 : ∃ e ∈ E, ∃ j ∈ N₁, e j ≠ j := by
        by_contra h
        apply htriv₁
        intro e he j hj
        by_contra hne
        exact h ⟨e, he, j, hj, hne⟩
      obtain ⟨B, hBE, hmq, u, huN₁, hufix, e0, he0E, he0u⟩ :=
        s1611e3_a5_single (L := L) (J := N₁) (E := E) hW hL hN₁nat hEel
          (fun e he => (hfix_of_mem e (hET₀ he)).1)
          (fun e he => hN₁inv e (hET₀ he)) hE1
      refine ⟨B, hBE, hmq, u, hufix, ⟨e0, he0E, he0u⟩, ?_⟩
      intro e he
      have hmem : e u ∈ N₁ := by
        have h := hN₁inv e (hET₀ he)
        exact h ▸ Subgroup.mem_map_of_mem e.toMonoidHom huN₁
      exact hN₁I (N₁.mul_mem hmem (N₁.inv_mem huN₁))
  ·
    have hnotle : ¬ E ≤ T₀ := by
      intro hle
      have heq : E = E₀ := by
        apply le_antisymm
        · intro x hx
          rw [hE₀def]
          exact Subgroup.mem_inf.2 ⟨hx, hle hx⟩
        · rw [hE₀def]
          exact inf_le_left
      exact hEeq heq
    obtain ⟨t, htE, htT₀⟩ : ∃ t ∈ E, t ∉ T₀ := by
      by_contra h
      apply hnotle
      intro x hx
      by_contra hxT₀
      exact h ⟨x, hx, hxT₀⟩
    have htT : t ∈ T := hET htE
    have ht_swap : L.map (MulAut.conj t).toMonoidHom = L' ∧
        L'.map (MulAut.conj t).toMonoidHom = L ∧
        U.map t.toMonoidHom = U' ∧ U'.map t.toMonoidHom = U := by
      rcases hT t htT with hf | hs
      · exact absurd (hmemT₀ t htT hf.2.2.1) htT₀
      · exact hs
    have htE₀ : t ∉ E₀ := by
      intro h
      have h' : t ∈ E ⊓ T₀ := hE₀def ▸ h
      exact htT₀ (Subgroup.mem_inf.1 h').2
    have hrel : E₀.relIndex E = 2 := by
      refine Subgroup.relIndex_eq_two_iff_exists_notMem_and.2 ⟨t, htE, htE₀, fun b hb => ?_⟩
      by_cases hbT₀ : b ∈ T₀
      · right
        rw [hE₀def]
        exact Subgroup.mem_inf.2 ⟨hb, hbT₀⟩
      · left
        have hb_swap' : U'.map b.toMonoidHom = U := by
          rcases hT b (hET hb) with hf | hs
          · exact absurd (hmemT₀ b (hET hb) hf.2.2.1) hbT₀
          · exact hs.2.2.2
        rw [hE₀def]
        refine Subgroup.mem_inf.2 ⟨E.mul_mem hb htE, ?_⟩
        have hcomp : U.map (b * t).toMonoidHom = (U.map t.toMonoidHom).map b.toMonoidHom :=
          (s1611e3_map_mul_map t b U).symm
        refine hmemT₀ (b * t) (T.mul_mem (hET hb) htT) ?_
        rw [hcomp, ht_swap.2.2.1, hb_swap']
    have hmq : E3.mQuot E E₀ = 1 := by
      unfold E3.mQuot
      rw [hrel]
      exact padicValNat_self
    have hE₀el : IsElemAbelian2 E₀ := by
      refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
      · have ha' : a ∈ E ∧ a ∈ T₀ := by
          have h : a ∈ E ⊓ T₀ := hE₀def ▸ ha
          exact Subgroup.mem_inf.1 h
        have hb' : b ∈ E ∧ b ∈ T₀ := by
          have h : b ∈ E ⊓ T₀ := hE₀def ▸ hb
          exact Subgroup.mem_inf.1 h
        exact hEel.1 a ha'.1 b hb'.1
      · have ha' : a ∈ E ∧ a ∈ T₀ := by
          have h : a ∈ E ⊓ T₀ := hE₀def ▸ ha
          exact Subgroup.mem_inf.1 h
        exact hEel.2 a ha'.1
    have hE₀p : IsPGroup 2 ↥E₀ := s1611e3_isPGroup_two_of_elemAbelian2 hE₀el
    have hE₀N : ∀ x ∈ E₀, N₁.map x.toMonoidHom = N₁ := by
      intro x hx
      have hx' : x ∈ E ∧ x ∈ T₀ := by
        have h : x ∈ E ⊓ T₀ := hE₀def ▸ hx
        exact Subgroup.mem_inf.1 h
      exact hN₁inv x hx'.2
    have hN₁card : 2 ∣ Nat.card ↥N₁ := by
      rw [s1611e3_card_natural hN₁nat]
      norm_num
    have hE₀Nmem : ∀ g ∈ E₀, ∀ u ∈ N₁, g u ∈ N₁ := by
      intro g hg u hu
      have h := hE₀N g hg
      exact h ▸ Subgroup.mem_map_of_mem g.toMonoidHom hu
    obtain ⟨u, huN₁, hu1, hufix⟩ :=
      CFSG.LocalAnalysis.EvenBN.Tits.N.exists_ne_one_fixed E₀ hE₀p N₁ hE₀Nmem hN₁card
    refine ⟨E₀, inf_le_left, hmq, u, hufix, ⟨t, htE, ?_⟩, ?_⟩
    · intro htu
      have htuU' : t u ∈ U' := by
        have h1 : t u ∈ N₁.map t.toMonoidHom := Subgroup.mem_map_of_mem t.toMonoidHom huN₁
        have h2 : N₁.map t.toMonoidHom ≤ U.map t.toMonoidHom := Subgroup.map_mono hN₁U
        exact ht_swap.2.2.1 ▸ h2 h1
      have hmem : u ∈ U ⊓ U' := ⟨hN₁U huN₁, htu ▸ htuU'⟩
      rw [hUU'] at hmem
      exact hu1 (Subgroup.mem_bot.1 hmem)
    · intro e he
      by_cases heT₀ : e ∈ T₀
      · have hefix : e u = u := hufix e (Subgroup.mem_inf.2 ⟨he, heT₀⟩)
        rw [hefix, mul_inv_cancel]
        exact I.one_mem
      · have he_swap : L.map (MulAut.conj e).toMonoidHom = L' ∧
            L'.map (MulAut.conj e).toMonoidHom = L ∧
            U.map e.toMonoidHom = U' ∧ U'.map e.toMonoidHom = U := by
          rcases hT e (hET he) with hf | hs
          · exact absurd (hmemT₀ e (hET he) hf.2.2.1) heT₀
          · exact hs
        have hste : t⁻¹ * e ∈ T₀ := by
          have hcomp : U.map (t⁻¹ * e).toMonoidHom = (U.map e.toMonoidHom).map t⁻¹.toMonoidHom :=
            (s1611e3_map_mul_map e t⁻¹ U).symm
          have ht2 : U'.map t⁻¹.toMonoidHom = U := by
            rw [← ht_swap.2.2.1, s1611e3_map_mul_map t t⁻¹ U, inv_mul_cancel, s1611e3_map_one]
          refine hmemT₀ (t⁻¹ * e) (T.mul_mem (T.inv_mem htT) (hET he)) ?_
          rw [hcomp, he_swap.2.2.1, ht2]
        have hsteE₀ : t⁻¹ * e ∈ E₀ := by
          rw [hE₀def]
          exact Subgroup.mem_inf.2 ⟨E.mul_mem (E.inv_mem htE) he, hste⟩
        have hfixste : (t⁻¹ * e) u = u := hufix _ hsteE₀
        have htuN₁' : t u ∈ N₁' :=
          hN₁'indep t htT ht_swap.2.2.1 ▸ Subgroup.mem_map_of_mem t.toMonoidHom huN₁
        have heu : e u = t u := by
          have hsplit : e = t * (t⁻¹ * e) := by group
          rw [hsplit, MulAut.mul_apply, hfixste]
        rw [heu]
        exact I.mul_mem (hN₁'I htuN₁') (I.inv_mem (hN₁I huN₁))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
