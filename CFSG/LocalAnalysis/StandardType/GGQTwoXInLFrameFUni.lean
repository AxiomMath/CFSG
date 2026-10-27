module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFUni3

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.SemisimpleCentralizers.Held CFSG.SectionRank.OddCover
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {R : Type} [Group R] [Finite R]

private lemma eq_erase_of_ne_univ {α : Type*} [Fintype α] [DecidableEq α] {I : Finset α}
    (hproper : I ≠ Finset.univ) (hcard : (Finset.univ \ I).card ≤ 1) :
    ∃ i₀, I = Finset.univ.erase i₀ := by
  have hne : (Finset.univ \ I).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hsub
    exact hproper (Finset.Subset.antisymm (Finset.subset_univ I) hsub)
  obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp
    (le_antisymm hcard (Finset.card_pos.mpr hne))
  refine ⟨i₀, ?_⟩
  rw [← Finset.sdiff_singleton_eq_erase, ← hi₀]
  exact (Finset.sdiff_sdiff_eq_self (Finset.subset_univ I)).symm

private lemma three_dvd_card {H X : Type} [Group H] [Group X] {ψ : H →* X} {J : Subgroup X}
    {K : Subgroup H} (hJ : J = Subgroup.map ψ K)
    (hu : ∃ u : H, u ∈ K ∧ u ^ 3 = 1 ∧ u ≠ 1) (hψ : Function.Injective ψ) :
    3 ∣ Nat.card J := by
  obtain ⟨u, huK, hu3, hu1⟩ := hu
  have hgJ : ψ u ∈ J := by
    rw [hJ]
    exact Subgroup.mem_map.mpr ⟨u, huK, rfl⟩
  have hg3 : (ψ u) ^ 3 = 1 := by rw [← map_pow, hu3, map_one]
  have hg1 : ψ u ≠ 1 := by
    intro h
    exact hu1 (hψ (by rw [map_one]; exact h))
  have horder : orderOf (ψ u) = 3 :=
    orderOf_eq_prime (p := 3) (hp := ⟨Nat.prime_three⟩) hg3 hg1
  have := Subgroup.orderOf_dvd_natCard J hgJ
  rwa [horder] at this

theorem exists_frameSign_of_uFrame {E : Subgroup R} {x : R} {L D J : Subgroup R}
    (hC : GGQTwoFRCfg E x L D J) {n : ℕ} {M : Type} [Field M] [Finite M] (hM : Nat.card M = 4)
    {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} (hτ2 : ∀ y, τ y = y ^ 2)
    {ρ : ↥(heldGU n M τ hτ) →* R} (hU : GGQTwoUFrame ρ E x L) (hn : 6 ≤ n)
    (ι : Additive ↥E ≃+ (Fin n → ZMod 3)) {c : M} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hι : ∀ (A : ↥(heldGU n M τ hτ)) (he : ρ A ∈ E),
      (∀ i j, i ≠ j → ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i j = 0) →
      ∀ i, ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i =
        c ^ (ι (Additive.ofMul ⟨ρ A, he⟩) i).val) :
    ∃ (i₀ : Fin n) (α : MulAut R),
      (∀ (e : R) (he : e ∈ E), e ∈ D ↔
        ∃ a b : ZMod 3, ι (Additive.ofMul ⟨e, he⟩) = fun i => a + if i = i₀ then b else 0) ∧
      3 ∣ Nat.card J ∧ (∀ e ∈ E, α e ∈ E) ∧
      (∀ (e : R) (he : e ∈ E) (hae : α e ∈ E), ι (Additive.ofMul ⟨α e, hae⟩) =
        fun i => (if i = i₀ then -1 else 1) * ι (Additive.ofMul ⟨e, he⟩) i) ∧
      ∀ j ∈ J, α j = j  := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨hEelem, hEcard, hEsq, hxE, hxne, hxL, hLcomp, hEnorm, hEL, hDE, hDcard, hxD,
    hJcomp, hEJ⟩ := hC
  obtain ⟨cU, hcU, hcU3, hcU1⟩ := FrameSign.exists_cU hc3 hc1
  have hinj : ∀ a b : ZMod 3, (cU : M) ^ a.val = (cU : M) ^ b.val → a = b :=
    FrameSign.pow_val_injective hcU3 hcU1
  have hUF : UnitaryFieldData 2 1 M :=
    ⟨Nat.prime_two, le_rfl, by rw [hM]; norm_num⟩
  obtain ⟨hSU, hle, hψinj, hker, hψrange⟩ := FrameSign.exists_psi_setup hτ2 m hU
  let ψ : ↥(unitarySU 2 1 M (m + 1)) →* R := ρ.comp (Subgroup.inclusion hle)
  have hD9 : Nat.card ↥D = 9 := by rw [hDcard]; norm_num
  have hδ : ∀ e ∈ (D : Set R), (e, diagHom (m + 1) (FrameSign.delta cU E ι e)) ∈
      SUTorus.suPairs ψ := by
    intro e heD
    exact FrameSign.mem_suPairs (hM := hM) (hτ2 := hτ2) (hU := hU) (hSU := hSU)
      (hle := hle) (c := c) (cU := cU) hcU hι (D := D) hDE heD
  obtain ⟨i, hJI⟩ := SUTorus.exists_le_map_blockSU (f := 1) (m := m) (G := R)
    (ψ := ψ) (S := (D : Set R)) (δ := FrameSign.delta cU E ι) (J := J) hUF
    Nat.prime_three (by norm_num) hker hδ (by rw [hψrange]; exact hJcomp)
  let I : Finset (Fin (m + 1)) :=
    LinTorus.diagClass (D : Set R) (FrameSign.delta cU E ι) i
  have hJI' : J ≤ Subgroup.map ψ (TableBUE.blockSU (K := M) (n := 1) I) := hJI
  have hcoord : ∀ (e : R) (he : e ∈ E) (heD : e ∈ D) {j k : Fin (m + 1)},
      j ∈ I → k ∈ I → ι (Additive.ofMul ⟨e, he⟩) j = ι (Additive.ofMul ⟨e, he⟩) k := by
    intro e he heD j k hj hk
    exact FrameSign.coord_const hinj he heD hj hk
  have hblock : ∀ (v : Fin (m + 1) → ZMod 3), (∀ j ∈ I, ∀ k ∈ I, v j = v k) →
      ∀ u : ↥(unitarySU 2 1 M (m + 1)), u ∈ TableBUE.blockSU (K := M) (n := 1) I →
      ρ (FrameSign.dg hM hτ2 cU v) * ψ u = ψ u * ρ (FrameSign.dg hM hτ2 cU v) := by
    intro v hv u hu
    exact FrameSign.block_comm hM hτ2 hv hu
  have hdmem : ∀ (v : Fin (m + 1) → ZMod 3), (∀ j ∈ I, ∀ k ∈ I, v j = v k) →
      ρ (FrameSign.dg hM hτ2 cU v) ∈ D := by
    intro v hv
    exact FrameSign.dg_mem_D (hM := hM) (hτ2 := hτ2) (hU := hU) (hle := hle)
      hJI' hEJ hv
  have hproper : I ≠ Finset.univ := by
    intro hIuniv
    exact FrameSign.ne_univ_of_const hDE hD9 (ι := ι) (I := I) (i := i)
      (fun e heD j hj => hcoord e (hDE heD) heD hj
        (LinTorus.self_mem_diagClass (D : Set R) (FrameSign.delta cU E ι) i)) hIuniv
  have hcompl : (Finset.univ \ I).card ≤ 1 :=
    FrameSign.compl_le_one (hM := hM) (hτ2 := hτ2) (cU := cU) (ρ := ρ) (D := D) (I := I)
      (i := i) (LinTorus.self_mem_diagClass (D : Set R) (FrameSign.delta cU E ι) i)
      hdmem hU.1 (FrameSign.dg_injective hM hτ2 hinj) hD9
  obtain ⟨i₀, hIeq⟩ := eq_erase_of_ne_univ hproper hcompl
  have hImem : ∀ j : Fin (m + 1), j ∈ I ↔ j ≠ i₀ := by
    intro j
    rw [hIeq, Finset.mem_erase]
    exact ⟨fun h => h.1, fun h => ⟨h, Finset.mem_univ j⟩⟩
  have hIcard : I.card = m := by
    rw [hIeq, Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ,
      Fintype.card_fin]
    omega
  have hKqmap : CFSG.Assembly.IsQuasisimple
      ↥(Subgroup.map ψ (TableBUE.blockSU (K := M) (n := 1) I)) :=
    FrameSign.isQuasisimple_map_blockSU (hM := hM) (ψ := ψ) hUF hker (I := I)
      (by omega) (by
        intro h
        have h1 : I.card = 3 := by simpa using congrArg Prod.fst h
        omega)
  have hKleH : Subgroup.map ψ (TableBUE.blockSU (K := M) (n := 1) I) ≤
      ψ.range ⊓ Subgroup.centralizer (D : Set R) :=
    FrameSign.map_blockSU_le_centralizer (hM := hM) (hτ2 := hτ2) (hU := hU)
      (hle := hle) (c := c) hcU hι hDE hcoord hblock
  have hJeq : J = Subgroup.map ψ (TableBUE.blockSU (K := M) (n := 1) I) :=
    LinTypeAk.eq_of_isComponentOf_of_le (by rw [hψrange]; exact hJcomp) hJI' hKleH hKqmap
  obtain ⟨u, huB, hu3, hu1⟩ :=
    FrameSign.exists_order_three_block (hM := hM) (cU := cU) (c := c) hcU hcU3 hc1
      (I := I) (by omega)
  have h3dvd : 3 ∣ Nat.card J :=
    three_dvd_card hJeq ⟨u, huB, hu3, hu1⟩ hψinj
  obtain ⟨α, hEα, hsign, hfix⟩ :=
    FrameSign.exists_alpha_fixes (hM := hM) (hτ2 := hτ2) (hU := hU) (hle := hle)
      (c := c) hcU hcU3 hcU1 hinj hι hJeq hImem
  have hDdesc : ∀ (e : R) (he : e ∈ E), e ∈ D ↔ ∃ a b : ZMod 3,
      ι (Additive.ofMul ⟨e, he⟩) = fun i => a + if i = i₀ then b else 0 :=
    FrameSign.D_description (hM := hM) (hτ2 := hτ2) (cU := cU) (hU := hU) (c := c)
      hcU hι (i := i) (LinTorus.self_mem_diagClass (D : Set R)
        (FrameSign.delta cU E ι) i) hImem hcoord hdmem
  exact ⟨i₀, α, hDdesc, h3dvd, hEα, hsign, hfix⟩

theorem ggQTwoFRFrame_of_uFrame {E : Subgroup R} {x : R} {L D J : Subgroup R}
    (hC : GGQTwoFRCfg E x L D J) {n : ℕ} {M : Type} [Field M] [Finite M] (hM : Nat.card M = 4)
    {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} (hτ2 : ∀ y, τ y = y ^ 2)
    {ρ : ↥(heldGU n M τ hτ) →* R} (hU : GGQTwoUFrame ρ E x L) : GGQTwoFRFrame E x L D J := by
  obtain ⟨hn, hx, ι, c, hc3, hc1, hx1, haut, hι⟩ :=
    QTwoFrameTorus.frame_exists_frameIota hC hM hτ2 hU
  obtain ⟨i₀, α, hD, h3, hE, hsign, hfix⟩ :=
    exists_frameSign_of_uFrame hC hM hτ2 hU hn ι hc3 hc1 hι
  exact ⟨n, hn, hx, ι, i₀, α, hx1, haut, hD, h3, hE, hsign, hfix⟩

end CFSG.StandardType

end
