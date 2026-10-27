module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Quot
public import CFSG.Quasithin.Background.HStandard
public import CFSG.RankThree.GF2n.Stroth80.ClassicalQuasisimple
public import CFSG.Quasithin.MS93.SkTypes
public import CFSG.Quasithin.Background.B1Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W]

theorem s16h_sl24_commSub_stab {L : Subgroup (MulAut W)} {g : MulAut W}
    (hg : g ∈ normalizer (L : Set (MulAut W))) : g ∈ stabSub (commSub ⊤ L) := by
  rw [mem_stabSub]
  have hnorm : ∀ x ∈ L, g * x * g⁻¹ ∈ L :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  have hgNinv : g⁻¹ ∈ normalizer (L : Set (MulAut W)) :=
    (normalizer (L : Set (MulAut W))).inv_mem hg
  have hnorminv : ∀ x ∈ L, g⁻¹ * x * (g⁻¹)⁻¹ ∈ L :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp hgNinv x).mp hx
  intro u
  constructor
  · intro hu
    have hmem : g⁻¹ (g u) ∈ commSub (⊤ : Subgroup W) L :=
      commSub_top_stable151b hnorminv (g u) hu
    simpa using hmem
  · intro hu
    exact commSub_top_stable151b hnorm u hu

theorem s16h_sl24_le_stabSub_Z {L : Subgroup (MulAut W)} :
    normalizer (L : Set (MulAut W)) ≤ stabSub (commSub ⊤ L ⊓ fixV L) := by
  intro x hx
  have hxnorm : ∀ l ∈ L, x * l * x⁻¹ ∈ L := fun l hl =>
    (Subgroup.mem_normalizer_iff.mp hx l).mp hl
  have hxinvnorm : ∀ l ∈ L, x⁻¹ * l * (x⁻¹)⁻¹ ∈ L := fun l hl =>
    (Subgroup.mem_normalizer_iff.mp ((normalizer (L : Set (MulAut W))).inv_mem hx) l).mp hl
  have hxZ : ∀ u ∈ commSub ⊤ L ⊓ fixV L, x u ∈ commSub ⊤ L ⊓ fixV L := by
    intro u hu
    rw [Subgroup.mem_inf] at hu ⊢
    refine ⟨commSub_top_stable151b hxnorm u hu.1, ?_⟩
    intro l hl
    calc l (x u) = x ((x⁻¹ * l * x) u) := by simp [MulAut.mul_apply]
      _ = x u := by rw [mem_fixV.mp hu.2 (x⁻¹ * l * x) (by simpa using hxinvnorm l hl)]
  have hxinvZ : ∀ u ∈ commSub ⊤ L ⊓ fixV L, x⁻¹ u ∈ commSub ⊤ L ⊓ fixV L := by
    intro u hu
    rw [Subgroup.mem_inf] at hu ⊢
    refine ⟨commSub_top_stable151b hxinvnorm u hu.1, ?_⟩
    intro l hl
    calc l (x⁻¹ u) = x⁻¹ ((x * l * x⁻¹) u) := by simp [MulAut.mul_apply]
      _ = x⁻¹ u := by rw [mem_fixV.mp hu.2 (x * l * x⁻¹) (hxnorm l hl)]
  rw [mem_stabSub]
  intro u
  exact ⟨fun hu => by have := hxinvZ (x u) hu; simpa using this, hxZ u⟩

theorem s16h_sl24_triv_of_triv_quot [Finite W] {L : Subgroup (MulAut W)}
    {K : Type} [Field K] [Finite K]
    {π : ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K) →* ↥L}
    {β : ↥(commSub ⊤ L) →* StdMod (Fin 2) K}
    (hK : Nat.card K = 4)
    (hπs : Function.Surjective π) (hβs : Function.Surjective β)
    (hβk : ∀ u : ↥(commSub ⊤ L), β u = 1 ↔ (u : W) ∈ commSub ⊤ L ⊓ fixV L)
    (hβe : ∀ (γ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K)) (u : ↥(commSub ⊤ L))
      (hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ commSub ⊤ L),
      β ⟨_, hu⟩ = natAct (CFSG.Assembly.LowTwoRank.StatedSL 2 K) γ (β u))
    {n : MulAut W} (hn : n ∈ Subgroup.normalizer (L : Set (MulAut W))) (hn2 : n ^ 2 = 1)
    (hnU' : ∀ u : ↥(commSub ⊤ L), n (u : W) ∈ commSub ⊤ L)
    (hntriv : ∀ u : ↥(commSub ⊤ L), n (u : W) * (u : W)⁻¹ ∈ commSub ⊤ L ⊓ fixV L) :
    ∀ u : ↥(commSub ⊤ L), n (u : W) = u := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  have h4K : 4 ≤ Nat.card K := by omega
  have hQSL : CFSG.IsQuasisimple ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K) :=
    CFSG.RankThree.GF2n.Stroth80.statedSL_quasisimple_of_card 2 K le_rfl h4K
  have hMcard : Nat.card (StdMod (Fin 2) K) = 16 := by
    have hc : Fintype.card K = 4 := by rw [Fintype.card_eq_nat_card, hK]
    simp [StdMod, Nat.card_fun, hc]
  have hUcard : 1 < Nat.card ↥(commSub ⊤ L) := by
    have hle := Nat.card_le_card_of_surjective β hβs
    omega
  have hUnt : Nontrivial ↥(commSub ⊤ L) :=
    (Finite.one_lt_card_iff_nontrivial (α := ↥(commSub ⊤ L))).mp hUcard
  have hLne : L ≠ ⊥ := by
    intro hbot
    have hUbot : commSub ⊤ L = ⊥ := by
      rw [hbot]
      exact commSub_eq_bot_iff.mpr (by rw [B1.fixV_bot])
    exact (Subgroup.nontrivial_iff_ne_bot (commSub ⊤ L)).mp hUnt hUbot
  haveI : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).mpr hLne
  have hkerne : π.ker ≠ ⊤ := by
    intro htop
    apply hLne
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨γ, hγ⟩ := hπs ⟨x, hx⟩
    have hmem : γ ∈ π.ker := by rw [htop]; exact Subgroup.mem_top γ
    have hx1 : π γ = 1 := MonoidHom.mem_ker.mp hmem
    simpa using hγ.symm.trans hx1
  have hkerle : π.ker ≤ Subgroup.center ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K) :=
    CFSG.Quasithin.MS93.le_center_of_isQuasisimple hQSL hkerne
  have hQL : CFSG.IsQuasisimple ↥L :=
    CFSG.LocalCores.isQuasisimple_of_surjective hQSL π hπs hkerle
  have hQL' : CFSG.Open.IsQuasisimple ↥L :=
    ⟨hQL.1.commutator_eq_top, hQL.2.1⟩
  have hcomp : IsComponentOf L (Subgroup.normalizer (L : Set (MulAut W))) :=
    ⟨Subgroup.le_normalizer,
      IsSubnormal.step (M := Subgroup.normalizer (L : Set (MulAut W)))
        Subgroup.le_normalizer inferInstance (IsSubnormal.refl _), hQL'⟩
  intro u
  exact s16h_H5_triv_of_triv_quot hcomp hn (fun w hw => hntriv ⟨w, hw⟩) u u.2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
