module

public import CFSG.Quasithin.Vol2.Ch3B513NC3C
public import CFSG.Quasithin.Background.FFC5T2

public section

namespace CFSG.Quasithin.B513N

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.JonesParshall Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {W : Type} [CommGroup W]

omit [CommGroup W] in
theorem transvection_mulVec_single {K : Type} [Field K] (k j : Fin 3) (hkj : k ≠ j) (c : K) :
    transvection k j c *ᵥ Pi.single j 1 = Pi.single j 1 + Pi.single k c := by
  funext r
  fin_cases k <;> fin_cases j <;> fin_cases r <;>
    simp_all [transvection, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.one_apply,
      Matrix.single_apply]

@[expose] noncomputable def trv {K : Type} [Field K] (k j : Fin 3) (hkj : k ≠ j) (c : K) :
    ↥(StatedSL 3 K) :=
  ⟨⟨transvection k j c, transvection k j (-c),
      by rw [transvection_mul_transvection_same k j hkj, add_neg_cancel, transvection_zero],
      by rw [transvection_mul_transvection_same k j hkj, neg_add_cancel, transvection_zero]⟩,
    Subgroup.subset_closure
      (show (transvection k j c).det = 1 from det_transvection_of_ne k j hkj c)⟩

theorem sup_commOf_eq_of_nat3 {L : Subgroup (MulAut W)} {I C : Subgroup W} {K : Type} [Field K]
    {π : ↥(StatedSL 3 K) →* ↥L} (hr : (FFModel.nat (StatedSL 3 K)).RealizesVia L I C π) :
    XMod.commOf ↥L I ⊔ C = I := by
  have hinv : ∀ h : ↥L, ∀ u ∈ I, (h : MulAut W) u ∈ I := hr.2.2.2.1
  have hCI : C ≤ I := hr.2.1
  apply le_antisymm
  · refine sup_le ?_ hCI
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨a, l, hl, rfl⟩
    exact I.mul_mem (hinv a l hl) (I.inv_mem hl)
  obtain ⟨β₀, hβs₀, hβk₀, hβe₀⟩ := FFModel.RealizesVia.coord rfl rfl hr
  let β : ↥I →* Multiplicative (Fin 3 → K) := β₀
  have hβs : Function.Surjective β := hβs₀
  have hβk : ∀ u : ↥I, β u = 1 ↔ (u : W) ∈ C := hβk₀
  have hβe : ∀ (γ : ↥(StatedSL 3 K)) (u : ↥I) (hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ I),
      β ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩ =
        Multiplicative.ofAdd (((γ : Matrix.GeneralLinearGroup (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) *ᵥ Multiplicative.toAdd (β u)) := hβe₀
  let S : Subgroup (Multiplicative (Fin 3 → K)) := ((XMod.commOf ↥L I).subgroupOf I).map β
  have hsingle : ∀ (k : Fin 3) (c : K), Multiplicative.ofAdd (Pi.single k c) ∈ S := by
    intro k c
    have hkj : k ≠ k + 1 := by fin_cases k <;> decide
    obtain ⟨i, hi⟩ := hβs (Multiplicative.ofAdd (Pi.single (k + 1) 1))
    have hmem : ((π (trv k (k + 1) hkj c) : ↥L) : MulAut W) (i : W) ∈ I :=
      hinv _ (i : W) i.2
    refine ⟨⟨_, I.mul_mem hmem (I.inv_mem i.2)⟩, ?_, ?_⟩
    · show _ ∈ XMod.commOf ↥L I
      exact Subgroup.subset_closure ⟨π (trv k (k + 1) hkj c), (i : W), i.2, rfl⟩
    · have e : (⟨_, I.mul_mem hmem (I.inv_mem i.2)⟩ : ↥I) = ⟨_, hmem⟩ * i⁻¹ := rfl
      rw [e, map_mul, map_inv, hβe, hi]
      apply Multiplicative.toAdd.injective
      simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd]
      show transvection k (k + 1) c *ᵥ Pi.single (k + 1) 1 + -Pi.single (k + 1) 1 = _
      rw [transvection_mulVec_single k (k + 1) hkj c]
      abel
  have htop : S = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv : v = ∏ k : Fin 3, Multiplicative.ofAdd (Pi.single k (Multiplicative.toAdd v k)) := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_prod]
      simp only [toAdd_ofAdd]
      ext r
      simp
    rw [hv]
    exact Subgroup.prod_mem _ fun k _ => hsingle k _
  intro u hu
  have hu' : β ⟨u, hu⟩ ∈ S := by rw [htop]; trivial
  obtain ⟨x, hx, hxu⟩ := hu'
  have hC' : ((x⁻¹ * ⟨u, hu⟩ : ↥I) : W) ∈ C := by
    rw [← hβk, map_mul, map_inv, hxu, inv_mul_cancel]
  have e : u = (x : W) * ((x⁻¹ * ⟨u, hu⟩ : ↥I) : W) := by
    show u = (x : W) * ((x : W)⁻¹ * u)
    group
  rw [e]
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.1 hx) hC'

theorem commOf_inv {L : Subgroup (MulAut W)} {I : Subgroup W}
    (hinv : ∀ h : ↥L, ∀ u ∈ I, (h : MulAut W) u ∈ I) :
    ∀ h : ↥L, ∀ x ∈ XMod.commOf ↥L I, (h : MulAut W) x ∈ XMod.commOf ↥L I := by
  intro h x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, l, hl, rfl⟩ := hy
    have e : (h : MulAut W) ((a : MulAut W) l * l⁻¹) =
        ((h * a * h⁻¹ : ↥L) : MulAut W) ((h : MulAut W) l) * ((h : MulAut W) l)⁻¹ := by
      simp [MulAut.mul_apply]
    show (h : MulAut W) ((a : MulAut W) l * l⁻¹) ∈ _
    rw [e]
    exact Subgroup.subset_closure ⟨h * a * h⁻¹, (h : MulAut W) l, hinv h l hl, rfl⟩
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact Subgroup.mul_mem _ ha hb
  | inv a _ ha => rw [map_inv]; exact Subgroup.inv_mem _ ha

theorem commOf_commOf_eq {L : Subgroup (MulAut W)} {I C : Subgroup W} (hC : C ≤ fixV L)
    (hinv : ∀ h : ↥L, ∀ u ∈ I, (h : MulAut W) u ∈ I) (hsup : XMod.commOf ↥L I ⊔ C = I) :
    XMod.commOf ↥L (XMod.commOf ↥L I) = XMod.commOf ↥L I := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨a, l, hl, rfl⟩
    exact Subgroup.mul_mem _ (commOf_inv hinv a l hl) (Subgroup.inv_mem _ hl)
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨a, l, hl, rfl⟩
    have hl' : l ∈ XMod.commOf ↥L I ⊔ C := by rw [hsup]; exact hl
    obtain ⟨j, hj, c, hc, rfl⟩ := Subgroup.mem_sup.1 hl'
    have e : (a • (j * c)) * (j * c)⁻¹ = (a • j) * j⁻¹ := by
      show (a : MulAut W) (j * c) * (j * c)⁻¹ = (a : MulAut W) j * j⁻¹
      rw [map_mul, hC hc _ a.2]
      group
    rw [e]
    exact Subgroup.subset_closure ⟨a, j, hj, rfl⟩

variable [Finite W]

theorem hasGood_of_two_nat (hW : ∀ w : W, w ^ 2 = 1) {G L D : Subgroup (MulAut W)}
    (hD : IsFFStarMin G D) (hDL : D ≤ L) {Wi C : Subgroup W} (hC : C ≤ fixV L)
    (hsupW : Wi ⊔ fixV L = ⊤) {n : ℕ} (hn : 1 < n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n)
    (hds : DirectSumOfCopies L Wi C (FFModel.nat (StatedSL 3 K)) 2) : HasGood G := by
  obtain ⟨I, π, hCI, hind, hsupI, hreal⟩ := hds
  have hinvI : ∀ k, ∀ h : ↥L, ∀ u ∈ I k, (h : MulAut W) u ∈ I k := fun k => (hreal k).2.2.2.1
  set J : Fin 2 → Subgroup W := fun k => XMod.commOf ↥L (I k) with hJdef
  have hJsup : ∀ k, J k ⊔ C = I k := fun k => sup_commOf_eq_of_nat3 (hreal k)
  have hJinv : ∀ k, ∀ h : ↥L, ∀ u ∈ J k, (h : MulAut W) u ∈ J k := fun k =>
    commOf_inv (hinvI k)
  have hJcomm : ∀ k, XMod.commOf ↥L (J k) = J k := fun k =>
    commOf_commOf_eq hC (hinvI k) (hJsup k)
  have hJC : ∀ k, C ⊓ J k = ⊥ := fun k =>
    eq_bot_of_sl3_cover hW (fun x hx v hv => hJinv k ⟨x, hx⟩ v hv) (hJcomm k)
      (inf_le_left.trans hC) inf_le_right hn hK
      ⟨π, FFC.realizesVia_restrict (hreal k) (hJsup k) (hJinv k)⟩
  have hrealJ : ∀ k, (FFModel.nat (StatedSL 3 K)).RealizesVia L (J k) ⊥ π := fun k => by
    have := FFC.realizesVia_restrict (hreal k) (hJsup k) (hJinv k)
    rwa [hJC k] at this
  have hI01 : I 0 ⊓ I 1 ≤ C := by
    have h0 := hind 0
    have hiSup : (⨆ (j : Fin 2) (_ : j ≠ 0), I j) = I 1 := by
      apply le_antisymm
      · refine iSup₂_le fun j hj => ?_
        have : j = 1 := by fin_cases j <;> simp_all
        rw [this]
      · exact le_iSup₂_of_le (f := fun (j : Fin 2) (_ : j ≠ 0) => I j) 1 (by decide) le_rfl
    rw [hiSup] at h0
    rw [← h0]
    exact inf_le_inf_left _ le_sup_right
  have hJ01 : J 0 ⊓ J 1 = ⊥ := by
    rw [eq_bot_iff, ← hJC 0]
    intro x hx
    have hxI : x ∈ I 0 ⊓ I 1 := ⟨(hJsup 0) ▸ Subgroup.mem_sup_left hx.1,
      (hJsup 1) ▸ Subgroup.mem_sup_left hx.2⟩
    exact ⟨hI01 hxI, hx.1⟩
  have hU : commV L = J 0 ⊔ J 1 := by
    apply le_antisymm
    · refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨g, hg, v, rfl⟩
      have hv : v ∈ Wi ⊔ fixV L := by rw [hsupW]; trivial
      obtain ⟨w, hw, f, hf, rfl⟩ := Subgroup.mem_sup.1 hv
      have hI2 : (⨆ i, I i) = I 0 ⊔ I 1 := by
        apply le_antisymm (iSup_le fun i => ?_) (sup_le (le_iSup I 0) (le_iSup I 1))
        fin_cases i
        · exact le_sup_left
        · exact le_sup_right
      rw [← hsupI, hI2] at hw
      obtain ⟨c, hc, i01, hi01, rfl⟩ := Subgroup.mem_sup.1 hw
      obtain ⟨i0, hi0, i1, hi1, rfl⟩ := Subgroup.mem_sup.1 hi01
      have e : g (c * (i0 * i1) * f) * (c * (i0 * i1) * f)⁻¹ =
          (g i0 * i0⁻¹) * (g i1 * i1⁻¹) := by
        rw [map_mul, map_mul, map_mul, hC hc g hg, hf g hg]
        calc c * (g i0 * g i1) * f * (c * (i0 * i1) * f)⁻¹
            = (g i0 * i0⁻¹) * (g i1 * i1⁻¹) * (c * c⁻¹) * (f * f⁻¹) := by
              simp only [_root_.mul_inv_rev]
              ac_rfl
          _ = (g i0 * i0⁻¹) * (g i1 * i1⁻¹) := by rw [mul_inv_cancel, mul_inv_cancel, mul_one,
              mul_one]
      rw [e]
      exact Subgroup.mul_mem_sup (Subgroup.subset_closure ⟨⟨g, hg⟩, i0, hi0, rfl⟩)
        (Subgroup.subset_closure ⟨⟨g, hg⟩, i1, hi1, rfl⟩)
    · refine sup_le ?_ ?_ <;>
      · refine (Subgroup.closure_le _).2 ?_
        rintro _ ⟨a, l, hl, rfl⟩
        exact Subgroup.subset_closure ⟨a, a.2, l, rfl⟩
  obtain ⟨d₀, hd₀, hd₀1⟩ : ∃ x ∈ D, x ≠ 1 := by
    by_contra h
    push Not at h
    exact hD.1.2.1 (eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 (h x hx))
  obtain ⟨γ, hγ⟩ := (hrealJ 0).1 ⟨d₀, hDL hd₀⟩
  have hγ1 : γ ≠ 1 := by
    rintro rfl
    apply hd₀1
    have := congrArg Subtype.val hγ
    rw [map_one] at this
    exact this.symm
  have hγD : ((π γ : ↥L) : MulAut W) ∈ D := by rw [hγ]; exact hd₀
  have hinvD : ∀ k, ∀ x ∈ D, ∀ u ∈ J k, x u ∈ J k := fun k x hx u hu =>
    hJinv k ⟨x, hDL hx⟩ u hu
  have hF : Nat.card ↥(fixV D ⊓ commV L) ≤ Nat.card K ^ 2 * Nat.card K ^ 2 := by
    rw [hU]
    calc Nat.card ↥(fixV D ⊓ (J 0 ⊔ J 1))
        ≤ Nat.card ↥((fixV D ⊓ J 0) ⊔ (fixV D ⊓ J 1)) :=
          Subgroup.card_le_of_le (fixV_inf_sup_le hJ01 (hinvD 0) (hinvD 1))
      _ ≤ Nat.card ↥(fixV D ⊓ J 0) * Nat.card ↥(fixV D ⊓ J 1) := card_sup_le _ _
      _ ≤ Nat.card K ^ 2 * Nat.card K ^ 2 :=
          Nat.mul_le_mul (card_fixV_inf_le_of_nat (hrealJ 0) hγ1 hγD)
            (card_fixV_inf_le_of_nat (hrealJ 1) hγ1 hγD)
  have hJcard : ∀ k, Nat.card (J k) = Nat.card K ^ 3 := fun k => by
    rw [card_commV_of_nat (hrealJ k), Subgroup.card_bot, one_mul]
  have hUcard : Nat.card (commV L) = Nat.card K ^ 3 * Nat.card K ^ 3 := by
    rw [hU, card_sup_of_inf_eq_bot hJ01, hJcard, hJcard]
  have hDK : Nat.card K ^ 2 ≤ Nat.card D := by
    have h1 := Subgroup.relIndex_mul_card (fixV D) (commV L)
    have h2 := (relIndex_fixV_le_index D (commV L)).trans (index_fixV_le_card hD.1)
    have hpos : 0 < Nat.card K ^ 2 * Nat.card K ^ 2 :=
      Nat.mul_pos (pow_pos Nat.card_pos _) (pow_pos Nat.card_pos _)
    have h4 : Nat.card K ^ 3 * Nat.card K ^ 3 ≤
        (fixV D).relIndex (commV L) * (Nat.card K ^ 2 * Nat.card K ^ 2) := by
      rw [← hUcard, ← h1]
      exact Nat.mul_le_mul_left _ hF
    have h5 : Nat.card K ^ 2 * (Nat.card K ^ 2 * Nat.card K ^ 2) ≤
        (fixV D).relIndex (commV L) * (Nat.card K ^ 2 * Nat.card K ^ 2) := by
      calc Nat.card K ^ 2 * (Nat.card K ^ 2 * Nat.card K ^ 2)
          = Nat.card K ^ 3 * Nat.card K ^ 3 := by ring
        _ ≤ _ := h4
    exact (Nat.le_of_mul_le_mul_right h5 hpos).trans h2
  refine hasGood_of_offender_le hW hD (commV_mono hDL) ?_
  calc Nat.card ↥(fixV D ⊓ commV L) ≤ Nat.card K ^ 2 * Nat.card K ^ 2 := hF
    _ = (Nat.card K ^ 2) ^ 2 := by ring
    _ ≤ Nat.card D ^ 2 := Nat.pow_le_pow_left hDK 2

end CFSG.Quasithin.B513N
