module

public import CFSG.Quasithin.Vol2.Ch3B513NC1ii
public import CFSG.Quasithin.H13.VolII16SL3

public section

namespace CFSG.Quasithin.B513N

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.JonesParshall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {W : Type} [CommGroup W] [Finite W]

theorem hasGood_of_nat_cent_of (hW : ∀ w : W, w ^ 2 = 1) {G L D : Subgroup (MulAut W)}
    (hD : IsFFStarMin G D) (hDL : D ≤ L) {d : ℕ} {K : Type} [Field K] [Finite K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin d) K)} {Z : Subgroup W}
    {π : (FFModel.nat Γ).Gam →* ↥L} (hr : (FFModel.nat Γ).RealizesVia L (commV L) Z π)
    (hd : 1 ≤ d) (hbound : Nat.card Z * Nat.card K ^ (d - 1) ≤ Nat.card K ^ 2) : HasGood G := by
  obtain ⟨d₀, hd₀, hd₀1⟩ : ∃ x ∈ D, x ≠ 1 := by
    by_contra h
    push Not at h
    exact hD.1.2.1 (eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 (h x hx))
  obtain ⟨β, hβs, hβk, hβe⟩ := FFModel.RealizesVia.coord rfl rfl hr
  obtain ⟨γ, hγ⟩ := hr.1 ⟨d₀, hDL hd₀⟩
  have hγ1 : γ ≠ 1 := by
    rintro rfl
    apply hd₀1
    have := congrArg Subtype.val hγ
    rw [map_one] at this
    exact this.symm
  set F : Subgroup W := fixV D ⊓ commV L with hF
  have hFU : F ≤ commV L := inf_le_right
  have hFcard : Nat.card F ≤ Nat.card Z * Nat.card K ^ (d - 1) := by
    let g : ↥F →* Multiplicative (Fin d → K) := β.comp (Subgroup.inclusion hFU)
    have hker : Nat.card g.ker ≤ Nat.card Z := by
      refine Nat.card_le_card_of_injective (fun x => ⟨(x.1 : W), (hβk _).1 x.2⟩) ?_
      intro x y hxy
      have h1 : ((x : ↥F) : W) = ((y : ↥F) : W) := congrArg (fun t : ↥Z => (t : W)) hxy
      exact Subtype.ext (Subtype.ext h1)
    have hrange : Nat.card g.range ≤ Nat.card K ^ (d - 1) := by
      refine le_trans ?_ (card_fix_natAct_le Γ hγ1)
      refine Nat.card_le_card_of_injective (fun y => ⟨(y : Multiplicative (Fin d → K)), ?_⟩) ?_
      · obtain ⟨x, hx⟩ := y.2
        rw [← hx]
        have hfix : d₀ (x : W) = x := x.2.1 d₀ hd₀
        have hu : ((π γ : ↥L) : MulAut W) ((x : W)) ∈ commV L := by
          rw [show ((π γ : ↥L) : MulAut W) = d₀ from congrArg Subtype.val hγ, hfix]
          exact hFU x.2
        have h1 := hβe γ ⟨x, hFU x.2⟩ hu
        have h2 : (⟨((π γ : ↥L) : MulAut W) (x : W), hu⟩ : ↥(commV L)) = ⟨x, hFU x.2⟩ := by
          apply Subtype.ext
          show ((π γ : ↥L) : MulAut W) (x : W) = x
          rw [show ((π γ : ↥L) : MulAut W) = d₀ from congrArg Subtype.val hγ, hfix]
        rw [h2] at h1
        exact h1.symm
      · intro y z hyz
        have h1 : (y : Multiplicative (Fin d → K)) = z :=
          congrArg (fun t : {x : Multiplicative (Fin d → K) // natAct Γ γ x = x} => t.1) hyz
        exact Subtype.ext h1
    calc Nat.card F = Nat.card g.ker * Nat.card g.range := (Subgroup.card_ker_mul_card_range g).symm
      _ ≤ Nat.card Z * Nat.card K ^ (d - 1) := Nat.mul_le_mul hker hrange
  have hUcard : Nat.card (commV L) = Nat.card Z * Nat.card K ^ d := card_commV_of_nat hr
  have hDK : Nat.card K ≤ Nat.card D := by
    have h1 : (fixV D).relIndex (commV L) * Nat.card F = Nat.card (commV L) :=
      Subgroup.relIndex_mul_card (fixV D) (commV L)
    have h2 : (fixV D).relIndex (commV L) ≤ (fixV D).index := relIndex_fixV_le_index D (commV L)
    have h3 : (fixV D).index ≤ Nat.card D := index_fixV_le_card hD.1
    have hZpos : 0 < Nat.card Z := Nat.card_pos
    have hKpos : 0 < Nat.card K := Nat.card_pos
    have h4 : Nat.card Z * Nat.card K ^ d ≤
        (fixV D).relIndex (commV L) * (Nat.card Z * Nat.card K ^ (d - 1)) := by
      rw [← hUcard, ← h1]
      exact Nat.mul_le_mul_left _ hFcard
    have hdk : Nat.card K ^ d = Nat.card K * Nat.card K ^ (d - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hdk] at h4
    have h5 : Nat.card K ≤ (fixV D).relIndex (commV L) := by
      have hpos : 0 < Nat.card Z * Nat.card K ^ (d - 1) := Nat.mul_pos hZpos (pow_pos hKpos _)
      have : Nat.card K * (Nat.card Z * Nat.card K ^ (d - 1)) ≤
          (fixV D).relIndex (commV L) * (Nat.card Z * Nat.card K ^ (d - 1)) := by
        calc Nat.card K * (Nat.card Z * Nat.card K ^ (d - 1))
            = Nat.card Z * (Nat.card K * Nat.card K ^ (d - 1)) := by ring
          _ ≤ _ := h4
      exact Nat.le_of_mul_le_mul_right this hpos
    exact h5.trans (h2.trans h3)
  refine hasGood_of_offender_le hW hD (commV_mono hDL) ?_
  calc Nat.card F ≤ Nat.card Z * Nat.card K ^ (d - 1) := hFcard
    _ ≤ Nat.card K ^ 2 := hbound
    _ ≤ Nat.card D ^ 2 := Nat.pow_le_pow_left hDK 2

omit [Finite W] in
theorem commOf_commV_eq {L : Subgroup (MulAut W)} {Wi C : Subgroup W} (hC : C ≤ fixV L)
    (hWi : Wi = commV L ⊔ C) (hsup : Wi ⊔ fixV L = ⊤) :
    XMod.commOf ↥L (commV L) = commV L := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨a, l, hl, rfl⟩
    exact Subgroup.subset_closure ⟨a, a.2, l, rfl⟩
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨g, hg, v, rfl⟩
    have hv : v ∈ Wi ⊔ fixV L := by rw [hsup]; trivial
    obtain ⟨w, hw, f, hf, rfl⟩ := Subgroup.mem_sup.1 hv
    rw [hWi] at hw
    obtain ⟨u, hu, c, hc, rfl⟩ := Subgroup.mem_sup.1 hw
    have e : g (u * c * f) * (u * c * f)⁻¹ = g u * u⁻¹ := by
      rw [map_mul, map_mul, hC hc g hg, hf g hg]
      group
    rw [e]
    exact Subgroup.subset_closure ⟨⟨g, hg⟩, u, hu, rfl⟩

theorem card_le_of_sl2_cover (hexp : ∀ w : W, w ^ 2 = 1) (L : Subgroup (MulAut W))
    (U : Subgroup W) (hinv : ∀ x ∈ L, ∀ v ∈ U, x v ∈ U) (hcomm : XMod.commOf ↥L U = U)
    {Z : Subgroup W} (hZ : Z ≤ fixV L) (hZU : Z ≤ U) {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ n) (hreal : (FFModel.nat (StatedSL 2 K)).Realizes L U Z) :
    Nat.card Z ≤ 2 ^ n := by
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card]; exact hK
  have : CharP K 2 := charP_of_card_eq_prime_pow hF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  obtain ⟨π, hπ⟩ := hreal
  obtain ⟨β, hβs, hβk, hβe⟩ := FFModel.RealizesVia.coord rfl rfl hπ
  have hcard := card_le_pow_finrank_H1_dual (Γ := ↥(StatedSL 2 K)) hexp L U Z
    hZU (fun z hz x hx => hZ hz x hx) hinv hcomm π hπ.1 (SLCover.natRepQ 2 K) β
    hβs hβk (fun γ v hv => hβe γ v hv)
  rwa [finrank_H1_SL2' hF (by omega) (SLCover.binaryNaturalSL_dual 2 K)] at hcard

theorem eq_bot_of_sl3_cover (hexp : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    {U Z : Subgroup W} (hinv : ∀ x ∈ L, ∀ v ∈ U, x v ∈ U) (hcomm : XMod.commOf ↥L U = U)
    (hZ : Z ≤ fixV L) (hZU : Z ≤ U) {n : ℕ} (hn : 1 < n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) (hreal : (FFModel.nat (StatedSL 3 K)).Realizes L U Z) : Z = ⊥ := by
  have h := H13.VolI.sl3_cover hn hK (H13.VolI.sq_eq_one_of_subgroup hexp)
    (H13.VolI.subgroupOf_le_fixV_resHom_range hinv hZ) (H13.VolI.commV_resHom_range hinv hcomm)
    (H13.VolI.realizes_resHom_range hinv _ hreal)
  rw [eq_bot_iff]
  intro z hz
  have hz' : (⟨z, hZU hz⟩ : ↥U) ∈ Z.subgroupOf U := Subgroup.mem_subgroupOf.2 hz
  rw [h, Subgroup.mem_bot] at hz'
  exact Subgroup.mem_bot.2 (congrArg Subtype.val hz')

end CFSG.Quasithin.B513N
