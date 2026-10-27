module

public import CFSG.LocalAnalysis.StandardType.GGD5Defs
public import CFSG.LocalAnalysis.StandardType.GGXInLSCLift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

private theorem lup10sc_card_comap_eq_card_mul_card_ker {A B : Type} [Group A] [Finite A]
    [Group B] (π : A →* B) (hπ : Function.Surjective π) (E : Subgroup B) :
    Nat.card (E.comap π) = Nat.card E * Nat.card π.ker := by
  let N : Subgroup A := E.comap π
  let Z : Subgroup A := π.ker
  have hZN : Z ≤ N := by
    intro z hz
    exact Subgroup.mem_comap.mpr (by rw [MonoidHom.mem_ker.mp hz]; exact E.one_mem)
  let f : N →* E :=
    { toFun := fun x => ⟨π x, x.2⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp }
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := hπ y.1
    refine ⟨⟨x, ?_⟩, ?_⟩
    · rw [Subgroup.mem_comap]
      rw [hx]
      exact y.2
    · ext
      exact hx
  have hker : f.ker = Z.subgroupOf N := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf]
      have hx' : f x = 1 := MonoidHom.mem_ker.mp hx
      have hv : π (x : A) = 1 := by
        have := congrArg Subtype.val hx'
        simpa [f] using this
      exact MonoidHom.mem_ker.mpr hv
    · intro hx
      rw [MonoidHom.mem_ker]
      ext
      exact Subgroup.mem_subgroupOf.mp hx
  have hmap : Subgroup.map N.subtype (Z.subgroupOf N) = Z := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hZN]
  have hcardZ : Nat.card (Z.subgroupOf N) = Nat.card Z := by
    rw [← Subgroup.card_map_of_injective (K := Z.subgroupOf N) N.subtype_injective, hmap]
  calc
    Nat.card N = Nat.card f.ker * Nat.card E :=
      (Subgroup.card_ker_mul_card_of_surjective (f := f) hf).symm
    _ = Nat.card (Z.subgroupOf N) * Nat.card E := by rw [hker]
    _ = Nat.card Z * Nat.card E := by rw [hcardZ]
    _ = Nat.card E * Nat.card Z := Nat.mul_comm _ _

private theorem lup10sc_coprime_center {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {J : Subgroup G}
    (h : Nat.Coprime p (Nat.card (Subgroup.center (↥J ⧸ LargeEvenPPrimeCore p ↥J)))) :
    Nat.Coprime p (Nat.card (Subgroup.center ↥J)) := by
  classical
  let O : Subgroup ↥J := LargeEvenPPrimeCore p ↥J
  let π : ↥J →* (↥J ⧸ O) := QuotientGroup.mk' O
  let C : Subgroup (↥J ⧸ O) := Subgroup.center (↥J ⧸ O)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective O
  have hker : π.ker = O := QuotientGroup.ker_mk' O
  have hmap : Subgroup.map π (Subgroup.center ↥J) ≤ C :=
    Subgroup.map_center_le_center hπ
  have hle : Subgroup.center ↥J ≤ C.comap π := by
    intro z hz
    exact hmap ⟨z, hz, rfl⟩
  have hcopC : Nat.Coprime p (Nat.card ↥C) := h
  have hcopO : Nat.Coprime p (Nat.card ↥O) := by
    dsimp [O]
    exact CFSG.pPrimeCore_coprime_card (p := p) (G := ↥J)
  have hcopComap : Nat.Coprime p (Nat.card ↥(C.comap π)) := by
    rw [lup10sc_card_comap_eq_card_mul_card_ker π hπ C, hker]
    exact Nat.Coprime.mul_right hcopC hcopO
  exact hcopComap.of_dvd_right (Subgroup.card_dvd_of_le hle)

private theorem lup10sc_card_sup_mul_card_inf {G : Type} [Group G] [Finite G]
    {A B : Subgroup G} (h : A ≤ Subgroup.normalizer (B : Set G)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  set N := Subgroup.normalizer (B : Set G) with hN
  have hB : B ≤ N := Subgroup.le_normalizer
  have hAB : A ⊔ B ≤ N := sup_le h hB
  have h1 := Subgroup.relIndex_sup_right (H := A.subgroupOf N) (K := B.subgroupOf N)
  have h2 := Subgroup.relIndex_mul_card (H := B.subgroupOf N)
    (K := A.subgroupOf N ⊔ B.subgroupOf N)
  have h3 := Subgroup.relIndex_mul_card (H := B.subgroupOf N) (K := A.subgroupOf N)
  rw [inf_eq_left.2 le_sup_right, h1] at h2
  have eA : Nat.card ↥(A.subgroupOf N) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv
  have eB : Nat.card ↥(B.subgroupOf N) = Nat.card ↥B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv
  have eAB : Nat.card ↥(A.subgroupOf N ⊔ B.subgroupOf N) = Nat.card ↥(A ⊔ B) := by
    rw [← Subgroup.subgroupOf_sup h hB]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv
  have eI : Nat.card ↥(B.subgroupOf N ⊓ A.subgroupOf N) = Nat.card ↥(A ⊓ B) := by
    have : B.subgroupOf N ⊓ A.subgroupOf N = (A ⊓ B).subgroupOf N := by
      ext x
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
      exact and_comm
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans h)).toEquiv
  rw [eAB, eB] at h2
  rw [eI, eA] at h3
  rw [← h2, ← h3]
  ring

theorem lup10d_sc_lift {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3) (hI1 : GGQTwoI1 Bs D J)
    {y : G} {K : Subgroup G} (M : GGQTwoAmbModel p Bs x y L (L ⊔ K))
    (hcard5 : Nat.card Bs = p ^ 5)
    (hLab : lup10d_LabelData p Bs x L J M) : lup10d_SCData Bs J := by
  unfold lup10d_LabelData at hLab
  have hcfg : GGConfig p B Bs x L D J := hS.1.1
  have hBs : GGBstar p B Bs := hcfg.2.1
  have hStdPre : LargeEvenStdSubPre p B x L D J := hcfg.2.2.1
  have hcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (hBs.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hexp : ∀ a ∈ Bs, a ^ p = 1 := hBs.2.1.2
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hBs.2.2.2
  have hinner : ∀ b ∈ Bs, ∃ j ∈ J, ∀ k ∈ J, b * k * b⁻¹ = j * k * j⁻¹ := hLab.2.2.2
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hS.1.2.2.1.1
  have hEJ : Bs ≤ Subgroup.normalizer (J : Set G) :=
    GGDichotomy.le_normalizer_stdSub hcomm hBs.1 hStdPre hN
  have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥J)) :=
    lup10sc_coprime_center hLab.2.1
  obtain ⟨hsup, hinf⟩ := GGXInL.sc_lift Bs J hcomm hexp hEJ hcop hinner hSC
  have hDc : D ≤ Subgroup.centralizer (J : Set G) := by
    rw [hStdPre.2.2.2.2.2.2]
    exact inf_le_right
  have hBD : Bs ⊓ Subgroup.centralizer (J : Set G) = D := by
    apply le_antisymm
    · intro b hb
      exact hI1 b hb.1 fun j hj => (Subgroup.mem_centralizer_iff.mp hb.2 j hj).symm
    · intro d hd
      exact ⟨hStdPre.1.trans hBs.1 hd, hDc hd⟩
  have hBcard : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = 9 := by
    rw [hBD, hStdPre.2.2.1, hp]
    norm_num
  unfold lup10d_SCData
  refine ⟨hsup, hinf, ?_⟩
  let A : Subgroup G := Bs ⊓ J
  let B : Subgroup G := Bs ⊓ Subgroup.centralizer (J : Set G)
  have hnorm : A ≤ Subgroup.normalizer (B : Set G) := by
    refine (show A ≤ Subgroup.centralizer (B : Set G) from ?_).trans
      (Subgroup.centralizer_le_normalizer (B : Set G))
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hcomm b hb.1 a ha.1
  have hformula := lup10sc_card_sup_mul_card_inf (A := A) (B := B) hnorm
  rw [show A ⊔ B = Bs from hsup, show A ⊓ B = ⊥ from hinf, Subgroup.card_bot,
    mul_one] at hformula
  have h243 : Nat.card Bs = 243 := by
    rw [hcard5, hp]
    norm_num
  have hBcard' : Nat.card ↥B = 9 := hBcard
  rw [h243, hBcard'] at hformula
  have hA27 : Nat.card ↥A = 27 := by omega
  exact hA27


end CFSG.StandardType

end
