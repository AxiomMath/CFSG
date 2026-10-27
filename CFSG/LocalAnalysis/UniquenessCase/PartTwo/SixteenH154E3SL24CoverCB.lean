module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24CoverCA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24CoverCBA
public import CFSG.CharacterTheory.Wreathed.PrimewisePerfectLift
public import CFSG.Quasithin.Background.F918H3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_sl24_cover_natNorm (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    {π : ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K) →* ↥L}
    {β : ↥(commSub ⊤ L) →* StdMod (Fin 2) K}
    (hπs : Function.Surjective π) (hβs : Function.Surjective β)
    (hβk : ∀ u : ↥(commSub ⊤ L), β u = 1 ↔ (u : W) ∈ commSub ⊤ L ⊓ fixV L)
    (hβe : ∀ (γ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K)) (u : ↥(commSub ⊤ L))
      (hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ commSub ⊤ L),
      β ⟨_, hu⟩ = natAct (CFSG.Assembly.LowTwoRank.StatedSL 2 K) γ (β u))
    {n : MulAut W} (hn : n ∈ Subgroup.normalizer (L : Set (MulAut W))) (hn2 : n ^ 2 = 1)
    (hnU : ∃ u ∈ commSub ⊤ L, n u ≠ u)
    (hnU' : ∀ u : ↥(commSub ⊤ L), n (u : W) ∈ commSub ⊤ L) :
    ∃ s : MulAut (StdMod (Fin 2) K),
      s ∈ natNorm (CFSG.Assembly.LowTwoRank.StatedSL 2 K) ∧ s ^ 2 = 1 ∧ s ≠ 1 ∧
      (∀ u : ↥(commSub ⊤ L), β ⟨n (u : W), hnU' u⟩ = s (β u)) := by
  classical
  let U : Subgroup W := commSub ⊤ L
  let Z : Subgroup W := commSub ⊤ L ⊓ fixV L
  have hUdef : U = commSub ⊤ L := rfl
  have hZdef : Z = commSub ⊤ L ⊓ fixV L := rfl
  have huU : ∀ u : ↥U, (u : W) ∈ commSub ⊤ L := fun u => hUdef ▸ u.2
  have hUmem : ∀ u : ↥U, (u : W) ∈ U := fun u => u.2
  have hLstab : ∀ l : ↥L, ∀ u : ↥U, ((l : MulAut W) (u : W)) ∈ U := by
    intro l u
    exact (mem_stabSub.mp (s16h_sl24_commSub_stab (L := L)
      (Subgroup.le_normalizer l.2)) (u : W)).mpr u.2
  have hnU'U : ∀ u : ↥U, n (u : W) ∈ U := by
    intro u
    change n (u : W) ∈ commSub ⊤ L
    exact hnU' ⟨u.1, huU u⟩
  have hnZ : ∀ z : ↥Z, n (z : W) ∈ Z := by
    intro z
    change n (z : W) ∈ commSub ⊤ L ⊓ fixV L
    exact (mem_stabSub.mp (s16h_sl24_le_stabSub_Z (L := L) hn) (z : W)).mpr z.2
  have hUmap : U.map (n : W →* W) = U := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨u, hu, rfl⟩
      exact hnU'U ⟨u, hu⟩
    · intro x hx
      refine ⟨n x, hnU'U ⟨x, hx⟩, ?_⟩
      have hnnu : n (n x) = x := by
        have h := congrArg (fun f : MulAut W => f x) hn2
        simpa [pow_two, MulAut.mul_apply] using h
      exact hnnu
  let nUe : ↥U ≃* ↥U :=
    (MulEquiv.subgroupMap n U).trans (MulEquiv.subgroupCongr hUmap)
  have hnUe_apply : ∀ u : ↥U, ((nUe u : ↥U) : W) = n (u : W) := by
    intro u
    rfl
  have hZmap_le : (Z.subgroupOf U).map (nUe : ↥U →* ↥U) ≤ Z.subgroupOf U := by
    rintro x ⟨z, hz, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr (hnZ ⟨z.1, Subgroup.mem_subgroupOf.mp hz⟩)
  have hZmap : (Z.subgroupOf U).map (nUe : ↥U →* ↥U) = Z.subgroupOf U := by
    refine Subgroup.eq_of_le_of_card_ge hZmap_le ?_
    rw [Subgroup.card_map_of_injective nUe.injective]
  let t : (↥U ⧸ Z.subgroupOf U) ≃* (↥U ⧸ Z.subgroupOf U) :=
    QuotientGroup.congr (Z.subgroupOf U) (Z.subgroupOf U) nUe hZmap
  have hker : β.ker = Z.subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hZdef]
    exact hβk ⟨u.1, huU u⟩
  let e0 : (↥U ⧸ β.ker) ≃* StdMod (Fin 2) K :=
    QuotientGroup.quotientKerEquivOfSurjective β hβs
  let e : (↥U ⧸ Z.subgroupOf U) ≃* StdMod (Fin 2) K :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans e0
  let s : MulAut (StdMod (Fin 2) K) := e.symm.trans (t.trans e)
  have he_mk : ∀ u : ↥U, e (QuotientGroup.mk u) = β u := by
    intro u
    change e0 (QuotientGroup.quotientMulEquivOfEq hker.symm (QuotientGroup.mk u)) = β u
    rw [QuotientGroup.quotientMulEquivOfEq_mk]
    change QuotientGroup.kerLift β (QuotientGroup.mk u) = β u
    exact QuotientGroup.kerLift_mk (φ := β) u
  have ht_mk : ∀ u : ↥U, t (QuotientGroup.mk u) = QuotientGroup.mk (nUe u) := by
    intro u
    exact QuotientGroup.congr_mk (Z.subgroupOf U) (Z.subgroupOf U) nUe hZmap u
  have hsβ : ∀ u : ↥U, β ⟨n (u : W), hnU' ⟨u.1, huU u⟩⟩ = s (β u) := by
    intro u
    have hsymm : e.symm (β u) = QuotientGroup.mk u := by
      rw [← he_mk u, MulEquiv.symm_apply_apply]
    change β ⟨n (u : W), hnU' ⟨u.1, huU u⟩⟩ = e (t (e.symm (β u)))
    rw [hsymm, ht_mk]
    rw [he_mk (nUe u)]
    exact congrArg β (Subtype.ext (hnUe_apply u).symm)
  have hsβ' : ∀ u : ↥(commSub ⊤ L), β ⟨n (u : W), hnU' u⟩ = s (β u) := by
    intro u
    exact hsβ ⟨u, by rw [hUdef]; exact u.2⟩
  have hs2 : s ^ 2 = 1 := by
    apply MulEquiv.ext
    intro y
    obtain ⟨u, rfl⟩ := hβs y
    rw [pow_two, MulAut.mul_apply]
    rw [← hsβ u, ← hsβ ⟨n (u : W), hnU'U u⟩]
    have hnu : n (n (u : W)) = (u : W) := by
      have h := congrArg (fun f : MulAut W => f (u : W)) hn2
      simpa [pow_two, MulAut.mul_apply] using h
    simpa only [MulAut.one_apply] using congrArg β (Subtype.ext hnu)
  refine ⟨s, ?_, hs2, ?_, ?_⟩
  ·
    have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_left hs2
    have hconj : ∀ a ∈ natImage (CFSG.Assembly.LowTwoRank.StatedSL 2 K),
        s * a * s⁻¹ ∈ natImage (CFSG.Assembly.LowTwoRank.StatedSL 2 K) := by
      intro a ha
      obtain ⟨γ, rfl⟩ := ha
      have hmemL : n * (π γ : MulAut W) * n⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp hn (π γ : MulAut W)).mp (π γ).2
      obtain ⟨γ', hγ'⟩ := hπs ⟨n * (π γ : MulAut W) * n⁻¹, hmemL⟩
      refine ⟨γ', ?_⟩
      apply MulEquiv.ext
      intro y
      obtain ⟨u, rfl⟩ := hβs y
      simp only [MulAut.mul_apply, natAut_apply]
      symm
      have hnule : ((π γ' : ↥L) : MulAut W) = n * (π γ : MulAut W) * n⁻¹ :=
        congrArg (fun x : ↥L => (x : MulAut W)) hγ'
      have hnu : n (n (u : W)) = (u : W) := by
        have h := congrArg (fun f : MulAut W => f (u : W)) hn2
        simpa [pow_two, MulAut.mul_apply] using h
      have hLnu : ((π γ : ↥L) : MulAut W) (n (u : W)) ∈ commSub ⊤ L :=
        hLstab (π γ) ⟨n (u : W), hnU'U u⟩
      have hLnnu : n (((π γ : ↥L) : MulAut W) (n (u : W))) ∈ commSub ⊤ L :=
        hnU' ⟨_, hLnu⟩
      calc s (natAct (CFSG.Assembly.LowTwoRank.StatedSL 2 K) γ (s⁻¹ (β u)))
          = s (natAct (CFSG.Assembly.LowTwoRank.StatedSL 2 K) γ (s (β u))) := by
              rw [hsinv]
        _ = s (natAct (CFSG.Assembly.LowTwoRank.StatedSL 2 K) γ
              (β ⟨n (u : W), hnU' u⟩)) := by rw [← hsβ' u]
        _ = s (β ⟨((π γ : ↥L) : MulAut W) (n (u : W)), hLnu⟩) := by
              rw [← hβe γ ⟨n (u : W), hnU' u⟩ hLnu]
        _ = β ⟨n (((π γ : ↥L) : MulAut W) (n (u : W))), hLnnu⟩ := by
              rw [← hsβ' ⟨_, hLnu⟩]
        _ = β ⟨((π γ' : ↥L) : MulAut W) (u : W), hLstab (π γ') ⟨u, huU u⟩⟩ := by
              congr 1
              apply Subtype.ext
              show n (((π γ : ↥L) : MulAut W) (n (u : W))) =
                ((π γ' : ↥L) : MulAut W) (u : W)
              rw [hnule]
              simp only [MulAut.mul_apply]
              have hninv : n⁻¹ = n :=
                inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hn2)
              rw [hninv]
        _ = natAct (CFSG.Assembly.LowTwoRank.StatedSL 2 K) γ' (β u) := by
              rw [hβe γ' u (hLstab (π γ') ⟨u, huU u⟩)]
    rw [natNorm, Subgroup.mem_normalizer_iff_map_conj_eq]
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact hconj a ha
    · intro hb
      refine ⟨s * b * s⁻¹, hconj b hb, ?_⟩
      show s * (s * b * s⁻¹) * s⁻¹ = b
      rw [hsinv]
      calc s * (s * b * s) * s = (s * s) * b * (s * s) := by group
        _ = b := by simp only [← pow_two, hs2, one_mul, mul_one]
  ·
    intro hs1
    have hntriv : ∀ u : ↥(commSub ⊤ L), n (u : W) * (u : W)⁻¹ ∈
        commSub ⊤ L ⊓ fixV L := by
      intro u
      let uU : ↥U := ⟨u, by rw [hUdef]; exact u.2⟩
      have h1 : β (⟨n (u : W), hnU' u⟩ * ⟨(u : W), u.2⟩⁻¹) = 1 := by
        rw [map_mul, map_inv, hsβ' u, hs1]
        simp
      exact (hβk _).mp h1
    obtain ⟨u, hu, hnu⟩ := hnU
    exact hnu (s16h_sl24_triv_of_triv_quot hK hπs hβs hβk hβe hn hn2 hnU' hntriv ⟨u, hu⟩)
  ·
    intro u
    exact hsβ ⟨u, huU ⟨u, by rw [hUdef]; exact u.2⟩⟩
theorem s16h_sl24_cover_transfer (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    {π : ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K) →* ↥L}
    {β : ↥(commSub ⊤ L) →* StdMod (Fin 2) K}
    (hπs : Function.Surjective π) (hβs : Function.Surjective β)
    (hβk : ∀ u : ↥(commSub ⊤ L), β u = 1 ↔ (u : W) ∈ commSub ⊤ L ⊓ fixV L)
    (hβe : ∀ (γ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K)) (u : ↥(commSub ⊤ L))
      (hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ commSub ⊤ L),
      β ⟨_, hu⟩ = natAct (CFSG.Assembly.LowTwoRank.StatedSL 2 K) γ (β u))
    {n : MulAut W} (hn : n ∈ Subgroup.normalizer (L : Set (MulAut W))) (hn2 : n ^ 2 = 1)
    (hnU : ∃ u ∈ commSub ⊤ L, n u ≠ u) :
    ∃ s : MulAut (StdMod (Fin 2) K),
      s ∈ natNorm (CFSG.Assembly.LowTwoRank.StatedSL 2 K) ∧ s ^ 2 = 1 ∧ s ≠ 1 ∧
      rkIdx (fixV (Subgroup.zpowers s)) ≤ rkIdx (fixV (Subgroup.zpowers n)) := by
  have hnstab : n ∈ stabSub (commSub ⊤ L) :=
    mem_stabSub_commSub (mem_stabSub.mpr fun u => Iff.rfl) hn
  have hnU' : ∀ u : ↥(commSub ⊤ L), n (u : W) ∈ commSub ⊤ L :=
    fun u => (mem_stabSub.mp hnstab (u : W)).2 u.2
  obtain ⟨s, hsN, hs2, hs1, hβe'⟩ :=
    s16h_sl24_cover_natNorm hW hK hπs hβs hβk hβe hn hn2 hnU hnU'
  exact ⟨s, hsN, hs2, hs1, s16h_sl24_cover_rank_le hβs hnU' hβe'⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
