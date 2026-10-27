module

public import CFSG.RankThree.GF2n.Tim81.Sec6.Stmts
public import CFSG.RankThree.GF2n.Tim81.FStarSimple
public import CFSG.RankThree.GF2n.Tim81.Recog.L2Gen
public import CFSG.Timmesfeld.Transvection.Subgroup
public import CFSG.Timmesfeld.Transvection.SpCount
public import CFSG.Timmesfeld.Transvection.TriangleAb

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Quasithin
open CFSG.Quasithin.JonesParshall CFSG.QuasithinUnique.Setup.X7 CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld CFSG.Timmesfeld.Transvection
open CFSG.Timmesfeld.ARS (conjSub Commuting commuting_iff_commutator_eq_bot IsRootClass
  restrict Opposite Special)
open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G}


private theorem conjSubgroup_inv_mem_of_mapsTo {Γ : Set (Subgroup G)} {g : G}
    (h : ∀ B ∈ Γ, conjSubgroup g B ∈ Γ) :
    ∀ B ∈ Γ, conjSubgroup g⁻¹ B ∈ Γ := by
  intro B hB
  have hfin : Γ.Finite := Set.toFinite Γ
  have hsub : conjSubgroup g '' Γ ⊆ Γ := by
    rintro _ ⟨C, hC, rfl⟩
    exact h C hC
  have himg : conjSubgroup g '' Γ = Γ := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ hfin
    rw [Set.ncard_image_of_injective _ (fun C C' hCC' => by
      have h1 := congrArg (conjSubgroup g⁻¹) hCC'
      calc C = conjSubgroup g⁻¹ (conjSubgroup g C) := by
            rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
        _ = conjSubgroup g⁻¹ (conjSubgroup g C') := h1
        _ = C' := by rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one])]
  obtain ⟨C, hC, hCB⟩ := himg ▸ hB
  have hCinv : conjSubgroup g⁻¹ B = C := by
    rw [← hCB, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  rwa [hCinv]

private theorem conjSubgroup_iSup_eq_of_mapsTo {Γ : Set (Subgroup G)} {g : G}
    (h : ∀ B ∈ Γ, conjSubgroup g B ∈ Γ) :
    conjSubgroup g (⨆ A ∈ Γ, A) = ⨆ A ∈ Γ, A :=
  Transvection.conjSub_iSup_eq h (conjSubgroup_inv_mem_of_mapsTo h)

private theorem conjSubgroup_mem_iSup₂ {Γ : Set (Subgroup G)}
    (hVM : V ≤ M)
    (hMΓ : ∀ m ∈ M, ∀ B ∈ Γ, conjSubgroup m B ∈ Γ)
    (htr : ∀ A ∈ Γ, ∃ g : G, A = conjSubgroup g V ∧ ∀ B ∈ Γ, conjSubgroup g B ∈ Γ) :
    ∀ l ∈ (⨆ A ∈ Γ, A), ∀ B ∈ Γ, conjSubgroup l B ∈ Γ := by
  let H : Subgroup G :=
    { carrier := {g | ∀ B ∈ Γ, conjSubgroup g B ∈ Γ}
      one_mem' := by
        intro B hB
        rw [conjSubgroup_one]
        exact hB
      mul_mem' := by
        intro g h hg hh B hB
        rw [conjSubgroup_mul]
        exact hg _ (hh B hB)
      inv_mem' := by
        intro g hg
        exact conjSubgroup_inv_mem_of_mapsTo hg }
  have hVH : V ≤ H := fun v hv B hB => hMΓ v (hVM hv) B hB
  have hAH : ∀ A ∈ Γ, A ≤ H := by
    intro A hA
    obtain ⟨g, hAeq, hgΓ⟩ := htr A hA
    have hgH : g ∈ H := hgΓ
    intro a ha
    have hv : g⁻¹ * a * g ∈ V := by
      rw [← mem_conjSubgroup, ← hAeq]
      exact ha
    have haeq : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
    rw [← haeq]
    exact H.mul_mem (H.mul_mem hgH (hVH hv)) (H.inv_mem hgH)
  have hLH : (⨆ A ∈ Γ, A) ≤ H := iSup₂_le hAH
  exact fun l hl B hB => hLH hl B hB


private theorem center_map_le_V
    (hS : Sec6Hyp M V) {Γ : Set (Subgroup G)} {L : Subgroup G}
    (hL : L = ⨆ A ∈ Γ, A) (hVΓ : V ∈ Γ)
    (hMΓ : ∀ m ∈ M, ∀ B ∈ Γ, conjSubgroup m B ∈ Γ) :
    (Subgroup.center ↥L).map L.subtype ≤ V := by
  have hR := hS.sec5.toRootHyp
  have hHyp := hR.toHyp
  let Z : Subgroup G := (Subgroup.center ↥L).map L.subtype
  have hΓL : ∀ B ∈ Γ, B ≤ L := by
    intro B hB
    rw [hL]
    exact le_iSup₂ (f := fun A (_ : A ∈ Γ) => A) B hB
  have hVL : V ≤ L := hΓL V hVΓ
  have hZeq : Z = L ⊓ Subgroup.centralizer (L : Set G) := by
    ext z
    rw [Subgroup.mem_inf]
    exact CFSG.LocalCores.mem_map_center_iff L
  have hZleC : Z ≤ Subgroup.centralizer (V : Set G) :=
    hZeq.le.trans (inf_le_right.trans (Subgroup.centralizer_le hVL))
  have hZleM : Z ≤ M := by
    obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hHyp.ne_bot
    have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
    refine hZleC.trans ?_
    exact (Subgroup.centralizer_le (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hv)).trans (hHyp.centralizer_le_M hv hv1')
  have hZabel : IsMulCommutative Z :=
    Subgroup.map_isMulCommutative (f := L.subtype) (H := Subgroup.center ↥L)
  have hML : M ≤ Subgroup.normalizer (L : Set G) := by
    intro m hm
    have h := conjSubgroup_iSup_eq_of_mapsTo (Γ := Γ) (g := m)
      (fun B hB => hMΓ m hm B hB)
    rw [← hL] at h
    exact conjSubgroup_eq_self_iff.mp h
  have hZnormalM : M ≤ Subgroup.normalizer (Z : Set G) := by
    intro m hm
    have hmL : conjSubgroup m L = L := by
      have h := conjSubgroup_iSup_eq_of_mapsTo (Γ := Γ) (g := m)
        (fun B hB => hMΓ m hm B hB)
      rwa [← hL] at h
    apply conjSubgroup_eq_self_iff.mp
    rw [hZeq, conjSubgroup_inf, ← centralizer_conjSubgroup_eq, hmL]
  have hVV : Commuting V V := fun a ha b hb =>
    (commute_iff_eq a b).mpr
      (congrArg Subtype.val (hHyp.maxAb.prop.2.2.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
  have hZZ : Commuting Z Z := fun a ha b hb =>
    (commute_iff_eq a b).mpr
      (congrArg Subtype.val (hZabel.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
  have hcommVZ : Commuting V Z := fun v hv z hz =>
    (commute_iff_eq v z).mpr (Subgroup.mem_centralizer_iff.mp (hZleC hz) v hv)
  have hcommZV : Commuting Z V := hcommVZ.symm
  have hcommS : Commuting (V ⊔ Z) (V ⊔ Z) :=
    (hVV.sup_left hcommZV).sup_right (hcommVZ.sup_left hZZ)
  have habelS : IsMulCommutative ↥(V ⊔ Z) :=
    ⟨⟨fun x y => Subtype.ext (hcommS x x.2 y y.2).eq⟩⟩
  have hMVZ : M ≤ Subgroup.normalizer ((V ⊔ Z : Subgroup G) : Set G) := by
    intro m hm
    exact Subgroup.inf_normalizer_le_normalizer_sup V Z
      ⟨hHyp.le_normalizer hm, hZnormalM hm⟩
  have hZV : Z ≤ V := by
    have h := hHyp.maxAb.le_of_ge
      ⟨sup_le hHyp.le_M hZleM, hMVZ, habelS⟩ (le_sup_left : V ≤ V ⊔ Z)
    exact le_sup_right.trans h
  simpa [Z] using hZV

private theorem center_map_eq_bot
    (hS : Sec6Hyp M V) {Γ : Set (Subgroup G)} {L : Subgroup G}
    (hL : L = ⨆ A ∈ Γ, A) (hVΓ : V ∈ Γ)
    (hMΓ : ∀ m ∈ M, ∀ B ∈ Γ, conjSubgroup m B ∈ Γ)
    (htr : ∀ A ∈ Γ, ∃ g : G, A = conjSubgroup g V ∧ ∀ B ∈ Γ, conjSubgroup g B ∈ Γ)
    (hSigΓ : sigmaSet M V ⊆ Γ) :
    (Subgroup.center ↥L).map L.subtype = ⊥ := by
  have hR := hS.sec5.toRootHyp
  let Z : Subgroup G := (Subgroup.center ↥L).map L.subtype
  have hΓL : ∀ B ∈ Γ, B ≤ L := by
    intro B hB
    rw [hL]
    exact le_iSup₂ (f := fun A (_ : A ∈ Γ) => A) B hB
  have hZeq : Z = L ⊓ Subgroup.centralizer (L : Set G) := by
    ext z
    rw [Subgroup.mem_inf]
    exact CFSG.LocalCores.mem_map_center_iff L
  have hZV : Z ≤ V := center_map_le_V hS hL hVΓ hMΓ
  have hZleA : ∀ A ∈ Γ, Z ≤ A := by
    intro A hA
    obtain ⟨g, hAeq, hgΓ⟩ := htr A hA
    have hgL : conjSubgroup g L = L := by
      have h := conjSubgroup_iSup_eq_of_mapsTo (Γ := Γ) (g := g) hgΓ
      rwa [← hL] at h
    have hgZ : conjSubgroup g Z = Z := by
      rw [hZeq, conjSubgroup_inf, ← centralizer_conjSubgroup_eq, hgL]
    have hle : conjSubgroup g Z ≤ conjSubgroup g V := Subgroup.map_mono hZV
    rwa [hgZ, ← hAeq] at hle
  obtain ⟨U, hU⟩ := hS.ne
  have hUne : U ≠ V := ne_of_mem_sigmaSet hR hU
  have hUΓ : U ∈ Γ := hSigΓ hU
  have hZI : Z ≤ V ⊓ U := le_inf hZV (hZleA U hUΓ)
  obtain ⟨g, hUg, -⟩ := hU
  have hne : conjSubgroup g V ≠ V := by rwa [← hUg]
  have hTI : V ⊓ U = ⊥ := by
    rw [hUg]
    exact inf_conjSubgroup_eq_bot_of_isTI hR.toHyp.ti hne
  have hZbot : Z = ⊥ := le_bot_iff.mp (hZI.trans (le_of_eq hTI))
  simpa [Z] using hZbot

private theorem P_preserves_gamma2
    (hS : Sec6Hyp M V) {Γ Γ₂ : Set (Subgroup G)} {L : Subgroup G}
    (hΓ₂ : Γ₂ = {B | B ∈ Γ ∧ ¬ ∃ g ∈ L, B = conjSubgroup g V})
    (hL : L = ⨆ A ∈ Γ, A)
    (hMΓ : ∀ m ∈ M, ∀ B ∈ Γ, conjSubgroup m B ∈ Γ) :
    ∀ p ∈ Pc M V, ∀ B ∈ Γ₂, conjSubgroup p B ∈ Γ₂ := by
  intro p hp B hB₂
  rw [hΓ₂] at hB₂
  have hpM : p ∈ M := hS.sec5.toRootHyp.toHyp.Pc_le_M hp
  have hpC : ∀ v ∈ V, p * v = v * p := fun v hv =>
    (Subgroup.mem_centralizer_iff.mp hp.2 v hv).symm
  have hpV : conjSubgroup p V = V := by
    ext v
    rw [mem_conjSubgroup]
    constructor
    · intro hv
      have hw : p * (p⁻¹ * v * p) = (p⁻¹ * v * p) * p := hpC (p⁻¹ * v * p) hv
      have hv' : v = p⁻¹ * v * p := by
        calc v = p * (p⁻¹ * v * p) * p⁻¹ := by group
          _ = (p⁻¹ * v * p) * p * p⁻¹ := by rw [hw]
          _ = p⁻¹ * v * p := by group
      rw [hv']
      exact hv
    · intro hv
      have h : p⁻¹ * v * p = v := by
        calc p⁻¹ * v * p = p⁻¹ * (p * v) := by
              rw [hpC v hv]
              group
          _ = v := by group
      rw [h]
      exact hv
  have hpL : conjSubgroup p L = L := by
    have h := conjSubgroup_iSup_eq_of_mapsTo (Γ := Γ) (g := p)
      (fun C hC => hMΓ p hpM C hC)
    rwa [← hL] at h
  have hpInvV : conjSubgroup p⁻¹ V = V := by
    have h := congrArg (conjSubgroup p⁻¹) hpV
    rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one] at h
    exact h.symm
  have hpInvL : conjSubgroup p⁻¹ L = L := by
    have h := congrArg (conjSubgroup p⁻¹) hpL
    rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one] at h
    exact h.symm
  rw [hΓ₂]
  refine ⟨hMΓ p hpM B hB₂.1, ?_⟩
  rintro ⟨h, hhL, hheq⟩
  apply hB₂.2
  have hhL' : p⁻¹ * h * p ∈ L := by
    have hmem : p⁻¹ * h * p ∈ conjSubgroup p⁻¹ L := by
      rw [mem_conjSubgroup]
      have h1 : p⁻¹⁻¹ * (p⁻¹ * h * p) * p⁻¹ = h := by group
      rwa [h1]
    rwa [hpInvL] at hmem
  refine ⟨p⁻¹ * h * p, hhL', ?_⟩
  calc B = conjSubgroup p⁻¹ (conjSubgroup p B) := by
        rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
    _ = conjSubgroup p⁻¹ (conjSubgroup h V) := by rw [hheq]
    _ = conjSubgroup (p⁻¹ * h) V := (conjSubgroup_mul p⁻¹ h V).symm
    _ = conjSubgroup ((p⁻¹ * h * p) * p⁻¹) V := by congr 1; group
    _ = conjSubgroup (p⁻¹ * h * p) (conjSubgroup p⁻¹ V) :=
        (conjSubgroup_mul (p⁻¹ * h * p) p⁻¹ V)
    _ = conjSubgroup (p⁻¹ * h * p) V := by rw [hpInvV]

private theorem gamma2_contradiction
    (hS : Sec6Hyp M V) (h60 : Sec6.Stmt60 M V)
    {Γ Γ₁ Γ₂ : Set (Subgroup G)} {L : Subgroup G}
    (hΓ₁ : Γ₁ = {B | B ∈ Γ ∧ ∃ g ∈ L, B = conjSubgroup g V})
    (hΓ₂ : Γ₂ = {B | B ∈ Γ ∧ ¬ ∃ g ∈ L, B = conjSubgroup g V})
    (hL : L = ⨆ A ∈ Γ, A) (hVΓ : V ∈ Γ)
    (hGam2Sig : Γ₂ ⊆ sigmaSet M V)
    (hPΓ₂ : ∀ p ∈ Pc M V, ∀ B ∈ Γ₂, conjSubgroup p B ∈ Γ₂)
    (hcomm₁₂ : ∀ A ∈ Γ₁, ∀ B ∈ Γ₂, Commuting A B)
    (hcenter : Subgroup.center ↥L = ⊥) :
    ∀ B ∈ Γ, ∃ g ∈ L, B = conjSubgroup g V := by
  have hR := hS.sec5.toRootHyp
  have hΓL : ∀ B ∈ Γ, B ≤ L := by
    intro B hB
    rw [hL]
    exact le_iSup₂ (f := fun A (_ : A ∈ Γ) => A) B hB
  by_contra hclass
  push Not at hclass
  obtain ⟨B₀, hB₀Γ, hB₀not⟩ := hclass
  have hB₀₂ : B₀ ∈ Γ₂ := by
    rw [hΓ₂]
    exact ⟨hB₀Γ, fun ⟨g, hg, hEq⟩ => hB₀not g hg hEq⟩
  have hB0sig : B₀ ∈ sigmaSet M V := hGam2Sig hB₀₂
  have hVleSupΓ₂ : V ≤ ⨆ B ∈ Γ₂, B := by
    refine (h60.2.2 B₀ hB0sig).trans ?_
    rw [Subgroup.commutator_le]
    intro p hp b hb
    have hpb : p * b * p⁻¹ ∈ conjSubgroup p B₀ := by
      rw [mem_conjSubgroup]
      have h1 : p⁻¹ * (p * b * p⁻¹) * p = b := by group
      rwa [h1]
    have hmem₁ : p * b * p⁻¹ ∈ ⨆ B ∈ Γ₂, B :=
      le_iSup₂ (f := fun B (_ : B ∈ Γ₂) => B) (conjSubgroup p B₀)
        (hPΓ₂ p hp B₀ hB₀₂) hpb
    have hmem₂ : b⁻¹ ∈ ⨆ B ∈ Γ₂, B :=
      le_iSup₂ (f := fun B (_ : B ∈ Γ₂) => B) B₀ hB₀₂ (B₀.inv_mem hb)
    exact Subgroup.mul_mem _ hmem₁ hmem₂
  have hΓ₂C : ∀ B ∈ Γ₂, B ≤ Subgroup.centralizer (V : Set G) := fun B hB =>
    (hS.sec5.le_M_of_mem_sigmaSet (hGam2Sig hB)).2
  have hL_le_CV : L ≤ Subgroup.centralizer (V : Set G) := by
    rw [hL]
    refine iSup₂_le fun A hA => ?_
    by_cases hA₁ : A ∈ Γ₁
    · rw [Subgroup.le_centralizer_iff]
      refine hVleSupΓ₂.trans ?_
      refine iSup₂_le fun B hB => ?_
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (hcomm₁₂ A hA₁ B hB a ha b hb).eq
    · refine hΓ₂C A ?_
      rw [hΓ₂]
      exact ⟨hA, fun h => hA₁ (by rw [hΓ₁]; exact ⟨hA, h⟩)⟩
  have hVleCL : V ≤ Subgroup.centralizer (L : Set G) :=
    (Subgroup.le_centralizer_iff).mpr hL_le_CV
  have hVZ : V ≤ (Subgroup.center ↥L).map L.subtype := by
    have hZeq : (Subgroup.center ↥L).map L.subtype =
        L ⊓ Subgroup.centralizer (L : Set G) := by
      ext z
      rw [Subgroup.mem_inf]
      exact CFSG.LocalCores.mem_map_center_iff L
    rw [hZeq]
    exact le_inf (hΓL V hVΓ) hVleCL
  have hVbot : V = ⊥ := by
    have hle : V ≤ (⊥ : Subgroup G) := by
      simpa [hcenter, Subgroup.map_bot] using hVZ
    exact le_bot_iff.mp hle
  exact hR.toHyp.ne_bot hVbot

private theorem exists_conjSub_eq_of_mem_sigmaSet
    (hS : Sec6Hyp M V) (h60 : Sec6.Stmt60 M V)
    {Γ : Set (Subgroup G)} {L : Subgroup G}
    (hL : L = ⨆ A ∈ Γ, A) (hVΓ : V ∈ Γ)
    (hpair : ∀ A ∈ Γ, ∀ B ∈ Γ, A ≠ B → ⁅A, B⁆ = ⊥ ∨ IsL2Gen A B)
    (hcomm : ∀ B ∈ Γ, B ≠ V → ⁅V, B⁆ = ⊥ → B ∈ sigmaSet M V)
    (hMΓ : ∀ m ∈ M, ∀ B ∈ Γ, conjSubgroup m B ∈ Γ)
    (hcenter : Subgroup.center ↥L = ⊥) :
    ∀ B ∈ Γ, ∃ g ∈ L, B = conjSubgroup g V := by
  have hΓL : ∀ B ∈ Γ, B ≤ L := by
    intro B hB
    rw [hL]
    exact le_iSup₂ (f := fun A (_ : A ∈ Γ) => A) B hB
  let Γ₁ : Set (Subgroup G) := {B | B ∈ Γ ∧ ∃ g ∈ L, B = conjSubgroup g V}
  let Γ₂ : Set (Subgroup G) := {B | B ∈ Γ ∧ ¬ ∃ g ∈ L, B = conjSubgroup g V}
  have hΓ₁ : Γ₁ = {B | B ∈ Γ ∧ ∃ g ∈ L, B = conjSubgroup g V} := rfl
  have hΓ₂ : Γ₂ = {B | B ∈ Γ ∧ ¬ ∃ g ∈ L, B = conjSubgroup g V} := rfl
  have hVΓ₁ : V ∈ Γ₁ := ⟨hVΓ, 1, L.one_mem, (conjSubgroup_one V).symm⟩
  have hcomm₁₂ : ∀ A ∈ Γ₁, ∀ B ∈ Γ₂, Commuting A B := by
    rintro A ⟨hAΓ, g, hgL, hAeq⟩ B ⟨hBΓ, hBnot⟩
    by_cases hAB : A = B
    · subst hAB
      exact absurd ⟨g, hgL, hAeq⟩ hBnot
    · rcases hpair A hAΓ B hBΓ hAB with hc | hL2
      · exact commuting_iff_commutator_eq_bot.mpr hc
      · obtain ⟨x, hx, hxB⟩ := hL2.exists_conj
        refine absurd ?_ hBnot
        refine ⟨x * g, L.mul_mem ?_ hgL, ?_⟩
        · exact (sup_le (hΓL A hAΓ) (hΓL B hBΓ)) hx
        · rw [hxB, hAeq, conjSubgroup_mul]
  have hGam2Sig : Γ₂ ⊆ sigmaSet M V := by
    rintro B ⟨hBΓ, hBnot⟩
    have hBne : B ≠ V := by
      intro hBV
      exact hBnot ⟨1, L.one_mem, by rw [hBV, conjSubgroup_one]⟩
    have hVB : Commuting V B := hcomm₁₂ V hVΓ₁ B ⟨hBΓ, hBnot⟩
    exact hcomm B hBΓ hBne (commuting_iff_commutator_eq_bot.mp hVB)
  have hPΓ₂ := P_preserves_gamma2 hS (Γ₂ := Γ₂) hΓ₂ hL hMΓ
  exact gamma2_contradiction hS h60 hΓ₁ hΓ₂ hL hVΓ hGam2Sig hPΓ₂ hcomm₁₂ hcenter

private theorem same_commuting_set_conj
    {Γ : Set (Subgroup G)} {L : Subgroup G} {A B : Subgroup G} {g : G}
    (hΓL : ∀ C ∈ Γ, C ≤ L) (hAL : A ≤ L) (hBL : B ≤ L) (hAeq : A = conjSubgroup g V)
    (hgΓ : ∀ C ∈ Γ, conjSubgroup g C ∈ Γ)
    (hsame : ∀ C ∈ restrict Γ L,
      Commuting (A.subgroupOf L) C ↔ Commuting (B.subgroupOf L) C) :
    ∀ D ∈ Γ, Commuting V D ↔ Commuting (conjSubgroup g⁻¹ B) D := by
  intro D hD
  have hCΓ : conjSubgroup g D ∈ Γ := hgΓ D hD
  have hCmem : (conjSubgroup g D).subgroupOf L ∈ restrict Γ L :=
    CFSG.Timmesfeld.Transvection.SubgroupForm.subgroupOf_mem hCΓ (hΓL _ hCΓ)
  have hCD : Commuting A (conjSubgroup g D) ↔
      Commuting B (conjSubgroup g D) := by
    have h := hsame ((conjSubgroup g D).subgroupOf L) hCmem
    change Commuting (A.subgroupOf L) ((conjSubgroup g D).subgroupOf L) ↔
      Commuting (B.subgroupOf L) ((conjSubgroup g D).subgroupOf L) at h
    have h1 : Commuting (A.subgroupOf L) ((conjSubgroup g D).subgroupOf L) ↔
        Commuting A (conjSubgroup g D) := by
      rw [CFSG.Timmesfeld.ARS.Restrict.commuting_subgroupOf_iff,
        inf_of_le_left hAL, inf_of_le_left (hΓL _ hCΓ)]
    have h2 : Commuting (B.subgroupOf L) ((conjSubgroup g D).subgroupOf L) ↔
        Commuting B (conjSubgroup g D) := by
      rw [CFSG.Timmesfeld.ARS.Restrict.commuting_subgroupOf_iff,
        inf_of_le_left hBL, inf_of_le_left (hΓL _ hCΓ)]
    exact h1.symm.trans (h.trans h2)
  have hconj : Commuting (conjSubgroup g⁻¹ A)
      (conjSubgroup g⁻¹ (conjSubgroup g D)) ↔
      Commuting (conjSubgroup g⁻¹ B) (conjSubgroup g⁻¹ (conjSubgroup g D)) := by
    have hA : conjSubgroup g (conjSubgroup g⁻¹ A) = A := by
      rw [← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]
    have hB : conjSubgroup g (conjSubgroup g⁻¹ B) = B := by
      rw [← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]
    have hC : conjSubgroup g (conjSubgroup g⁻¹ (conjSubgroup g D)) =
        conjSubgroup g D := by
      rw [← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]
    constructor
    · intro h
      have h' : Commuting A (conjSubgroup g D) := by
        have hg := h.conjSub g
        change Commuting (conjSubgroup g (conjSubgroup g⁻¹ A))
          (conjSubgroup g (conjSubgroup g⁻¹ (conjSubgroup g D))) at hg
        rwa [hA, hC] at hg
      exact (hCD.mp h').conjSub g⁻¹
    · intro h
      have h' : Commuting B (conjSubgroup g D) := by
        have hg := h.conjSub g
        change Commuting (conjSubgroup g (conjSubgroup g⁻¹ B))
          (conjSubgroup g (conjSubgroup g⁻¹ (conjSubgroup g D))) at hg
        rwa [hB, hC] at hg
      exact (hCD.mpr h').conjSub g⁻¹
  have hD' : conjSubgroup g⁻¹ (conjSubgroup g D) = D := by
    rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  have hVA : conjSubgroup g⁻¹ A = V := by
    rw [hAeq, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  rwa [hVA, hD'] at hconj

private theorem pointsDetermined_restrict
    (hS : Sec6Hyp M V) (h60 : Sec6.Stmt60 M V)
    {Γ : Set (Subgroup G)} {L : Subgroup G}
    (hL : L = ⨆ A ∈ Γ, A) (hSigΓ : sigmaSet M V ⊆ Γ)
    (hcomm : ∀ B ∈ Γ, B ≠ V → ⁅V, B⁆ = ⊥ → B ∈ sigmaSet M V)
    (htr : ∀ A ∈ Γ, ∃ g : G, A = conjSubgroup g V ∧ ∀ B ∈ Γ, conjSubgroup g B ∈ Γ)
    (hRoot : IsRootClass (restrict Γ L)) :
    PointsDetermined (restrict Γ L) := by
  have hΓL : ∀ B ∈ Γ, B ≤ L := by
    intro B hB
    rw [hL]
    exact le_iSup₂ (f := fun A (_ : A ∈ Γ) => A) B hB
  intro A' hA' B' hB' hsame
  obtain ⟨A, ⟨hAΓ, hAL⟩, rfl⟩ := hA'
  obtain ⟨B, ⟨hBΓ, hBL⟩, rfl⟩ := hB'
  have hA'R : A.subgroupOf L ∈ restrict Γ L :=
    CFSG.Timmesfeld.Transvection.SubgroupForm.subgroupOf_mem hAΓ hAL
  have hAcomm : Commuting (A.subgroupOf L) (A.subgroupOf L) := hRoot.commuting_self hA'R
  have hBA : Commuting (B.subgroupOf L) (A.subgroupOf L) :=
    (hsame (A.subgroupOf L) hA'R).mp hAcomm
  have hAB' : Commuting (A.subgroupOf L) (B.subgroupOf L) := hBA.symm
  have hAB : Commuting A B := by
    rw [CFSG.Timmesfeld.ARS.Restrict.commuting_subgroupOf_iff,
      inf_of_le_left hAL, inf_of_le_left hBL] at hAB'
    exact hAB'
  obtain ⟨g, hAeq, hgΓ⟩ := htr A hAΓ
  let B₁ : Subgroup G := conjSubgroup g⁻¹ B
  have hB₁Γ : B₁ ∈ Γ := conjSubgroup_inv_mem_of_mapsTo hgΓ B hBΓ
  have hVA : conjSubgroup g⁻¹ A = V := by
    rw [hAeq, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  have hcommVB₁ : Commuting V B₁ := by
    have h := hAB.conjSub g⁻¹
    change Commuting (conjSubgroup g⁻¹ A) (conjSubgroup g⁻¹ B) at h
    rwa [hVA] at h
  have hsameV : ∀ D ∈ Γ, Commuting V D ↔ Commuting B₁ D := by
    have h := same_commuting_set_conj hΓL hAL hBL hAeq hgΓ hsame
    simpa [B₁] using h
  have hB₁eq : B₁ = V := by
    by_contra hB₁ne
    have hB₁sig : B₁ ∈ sigmaSet M V :=
      hcomm B₁ hB₁Γ hB₁ne (commuting_iff_commutator_eq_bot.mp hcommVB₁)
    obtain ⟨U', hU'sig, hL2⟩ := h60.1 B₁ hB₁sig
    have hU'Γ : U' ∈ Γ := hSigΓ hU'sig
    have hVU' : Commuting V U' := fun v hv u hu =>
      (commute_iff_eq v u).mpr
        (Subgroup.mem_centralizer_iff.mp
          ((hS.sec5.le_M_of_mem_sigmaSet hU'sig).2 hu) v hv)
    have hB₁U' : Commuting B₁ U' := (hsameV U' hU'Γ).mp hVU'
    exact hL2.not_commuting hB₁U'
  have hBAeq : B = A := by
    calc B = conjSubgroup g (conjSubgroup g⁻¹ B) := by
          rw [← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]
      _ = conjSubgroup g B₁ := rfl
      _ = conjSubgroup g V := by rw [hB₁eq]
      _ = A := hAeq.symm
  exact (CFSG.Timmesfeld.ARS.subgroupOf_inj_of_le hAL hBL).mpr hBAeq.symm

private theorem conj_map_injective
    {f n : ℕ} {Φ : ↥(StatedSp n (GaloisField 2 f)) →* G} (hΦinj : Function.Injective Φ)
    (x : ↥(StatedSp n (GaloisField 2 f))) :
    Function.Injective (fun Y : Subgroup ↥(StatedSp n (GaloisField 2 f)) =>
      (conjSub Y x).map Φ) := by
  intro Y Y' h
  have h' := h
  change (Y.map (MulAut.conj x).toMonoidHom).map Φ =
    (Y'.map (MulAut.conj x).toMonoidHom).map Φ at h'
  have h'' := Subgroup.map_injective (f := Φ) hΦinj h'
  exact Subgroup.map_injective (f := (MulAut.conj x).toMonoidHom)
    (MulAut.conj x).injective h''

private theorem sp_image_eq
    {f n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 f)) →* G} (hΦinj : Function.Injective Φ)
    {T : Subgroup ↥(StatedSp n (GaloisField 2 f))}
    {x : ↥(StatedSp n (GaloisField 2 f))} {V : Subgroup G}
    (hx : V = (conjSub T x).map Φ)
    {Γ : Set (Subgroup G)}
    (hmem : ∀ X : Subgroup G, X ∈ Γ ↔ ∃ g, X = (conjSub T g).map Φ) :
    (fun Y : Subgroup ↥(StatedSp n (GaloisField 2 f)) => (conjSub Y x).map Φ) ''
        {Y | (∃ g, Y = conjSub T g) ∧ Y ≠ T ∧ Commuting T Y} =
      {B : Subgroup G | B ∈ Γ ∧ B ≠ V ∧ Commuting V B} := by
  let ψ : Subgroup ↥(StatedSp n (GaloisField 2 f)) → Subgroup G :=
    fun Y => (conjSub Y x).map Φ
  let S1 : Set (Subgroup ↥(StatedSp n (GaloisField 2 f))) :=
    {Y | (∃ g, Y = conjSub T g) ∧ Y ≠ T ∧ Commuting T Y}
  let S2 : Set (Subgroup G) := {B | B ∈ Γ ∧ B ≠ V ∧ Commuting V B}
  have hψinjY : Function.Injective ψ := conj_map_injective hΦinj x
  change ψ '' S1 = S2
  ext B
  constructor
  · rintro ⟨Y, hY, rfl⟩
    obtain ⟨⟨g, hYg⟩, hYT, hTY⟩ := hY
    have hψ : ψ Y = (conjSub T (x * g)).map Φ := by
      calc ψ Y = (conjSub (conjSub T g) x).map Φ := by rw [hYg]
        _ = (conjSub T (x * g)).map Φ := by rw [← CFSG.Timmesfeld.ARS.conjSub_mul]
    refine ⟨(hmem (ψ Y)).mpr ⟨x * g, hψ⟩, ?_, ?_⟩
    · intro hψV
      have hψT : ψ Y = ψ T := by
        rw [hψV]
        exact hx
      exact hYT (hψinjY hψT)
    · have hconj : Commuting (conjSub T x) (conjSub Y x) := hTY.conjSub x
      have hmap : Commuting ((conjSub T x).map Φ) ((conjSub Y x).map Φ) := by
        intro a ha b hb
        obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
        obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
        exact (hconj a' ha' b' hb').map Φ
      change Commuting V (ψ Y)
      rw [hx]
      exact hmap
  · intro hB
    obtain ⟨hBΓ, hBne, hVB⟩ := hB
    obtain ⟨g, hBg⟩ := (hmem B).mp hBΓ
    have hψ : ψ (conjSub T (x⁻¹ * g)) = B := by
      calc ψ (conjSub T (x⁻¹ * g))
          = (conjSub (conjSub T (x⁻¹ * g)) x).map Φ := rfl
        _ = (conjSub T (x * (x⁻¹ * g))).map Φ := by
              rw [← CFSG.Timmesfeld.ARS.conjSub_mul]
        _ = (conjSub T g).map Φ := by
              rw [show x * (x⁻¹ * g) = g by group]
        _ = B := hBg.symm
    refine ⟨conjSub T (x⁻¹ * g), ⟨⟨x⁻¹ * g, rfl⟩, ?_, ?_⟩, hψ⟩
    · intro hYT
      apply hBne
      rw [← hψ, hYT]
      exact hx.symm
    · have hmapcomm : Commuting ((conjSub T x).map Φ)
          ((conjSub (conjSub T (x⁻¹ * g)) x).map Φ) := by
        change Commuting ((conjSub T x).map Φ) (ψ (conjSub T (x⁻¹ * g)))
        rw [← hx, hψ]
        exact hVB
      have hconj : Commuting (conjSub T x) (conjSub (conjSub T (x⁻¹ * g)) x) := by
        intro a ha b hb
        have hc : Commute (Φ a) (Φ b) :=
          hmapcomm (Φ a) (Subgroup.mem_map_of_mem Φ ha) (Φ b)
            (Subgroup.mem_map_of_mem Φ hb)
        apply (commute_iff_eq a b).mpr
        apply hΦinj
        rw [map_mul, map_mul]
        exact (commute_iff_eq (Φ a) (Φ b)).mp hc
      have h := hconj.conjSub x⁻¹
      change Commuting (conjSub (conjSub T x) x⁻¹)
        (conjSub (conjSub (conjSub T (x⁻¹ * g)) x) x⁻¹) at h
      rw [← CFSG.Timmesfeld.ARS.conjSub_mul, ← CFSG.Timmesfeld.ARS.conjSub_mul,
        inv_mul_cancel] at h
      simpa using h

private theorem card_sp_conj_commuting_eq
    {f n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 f)) →* G} (hΦinj : Function.Injective Φ)
    {T : Subgroup ↥(StatedSp n (GaloisField 2 f))}
    {x : ↥(StatedSp n (GaloisField 2 f))} {V : Subgroup G}
    (hx : V = (conjSub T x).map Φ)
    {Γ : Set (Subgroup G)}
    (hmem : ∀ X : Subgroup G, X ∈ Γ ↔ ∃ g, X = (conjSub T g).map Φ) :
    Nat.card {Y : Subgroup ↥(StatedSp n (GaloisField 2 f)) //
      (∃ g, Y = conjSub T g) ∧ Y ≠ T ∧ Commuting T Y} =
    Nat.card {B : Subgroup G // B ∈ Γ ∧ B ≠ V ∧ Commuting V B} := by
  let ψ : Subgroup ↥(StatedSp n (GaloisField 2 f)) → Subgroup G :=
    fun Y => (conjSub Y x).map Φ
  have hψinj : Function.Injective ψ := conj_map_injective hΦinj x
  have himage := sp_image_eq hΦinj hx hmem
  have hcard : Nat.card {Y : Subgroup ↥(StatedSp n (GaloisField 2 f)) //
      (∃ g, Y = conjSub T g) ∧ Y ≠ T ∧ Commuting T Y} =
      Nat.card {B : Subgroup G // B ∈ Γ ∧ B ≠ V ∧ Commuting V B} := by
    change Nat.card ↥{Y : Subgroup ↥(StatedSp n (GaloisField 2 f)) |
        (∃ g, Y = conjSub T g) ∧ Y ≠ T ∧ Commuting T Y} =
      Nat.card ↥{B : Subgroup G | B ∈ Γ ∧ B ≠ V ∧ Commuting V B}
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    rw [← himage, Set.ncard_image_of_injective _ hψinj]
  exact hcard

private theorem restrict_conj_ne_mul
    (hS : Sec6Hyp M V) {Γ : Set (Subgroup G)} {L : Subgroup G}
    (hL : L = ⨆ A ∈ Γ, A) (hVΓ : V ∈ Γ) (hΓ : Γ ⊆ omegaSet V)
    (hclass : ∀ B ∈ Γ, ∃ g ∈ L, B = conjSubgroup g V)
    (hconjL : ∀ l ∈ L, ∀ B ∈ Γ, conjSubgroup l B ∈ Γ) :
    (∃ A₀ : Subgroup ↥L, restrict Γ L = Set.range (conjSub A₀)) ∧
      (∀ X ∈ restrict Γ L, X ≠ ⊥) ∧
      (∀ X ∈ restrict Γ L, ∀ x ∈ X, x * x = 1) := by
  have hR := hS.sec5.toRootHyp
  have hΓL : ∀ B ∈ Γ, B ≤ L := by
    intro B hB
    rw [hL]
    exact le_iSup₂ (f := fun A (_ : A ∈ Γ) => A) B hB
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨V.subgroupOf L, ?_⟩
    ext X
    constructor
    · intro hX
      obtain ⟨B, ⟨hBΓ, hBL⟩, rfl⟩ := hX
      obtain ⟨g, hgL, hBg⟩ := hclass B hBΓ
      refine ⟨⟨g, hgL⟩, ?_⟩
      rw [show conjSub (V.subgroupOf L) (⟨g, hgL⟩ : ↥L) =
          (conjSubgroup g V).subgroupOf L from
        CFSG.Timmesfeld.ARS.map_conj_subgroupOf_mk hgL]
      rw [hBg]
    · rintro ⟨x, rfl⟩
      have hmem := hconjL x x.2 V hVΓ
      rw [show conjSub (V.subgroupOf L) x = (conjSubgroup (x : G) V).subgroupOf L from
        CFSG.Timmesfeld.ARS.map_conj_subgroupOf_mk (H := V) (L := L) (x := (x : G)) x.2]
      exact CFSG.Timmesfeld.Transvection.SubgroupForm.subgroupOf_mem hmem
        (hΓL _ hmem)
  · rintro X ⟨B, ⟨hBΓ, hBL⟩, rfl⟩ hbot
    have hBbot : B = ⊥ := (Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le hBL
    have hBne : B ≠ ⊥ := by
      obtain ⟨g, -, hBg⟩ := Tim79a.mem_omegaOf.mp (hΓ hBΓ)
      intro hconj
      apply hR.toHyp.ne_bot
      have hconj' : conjSubgroup g V = ⊥ := by rwa [← hBg]
      have h := congrArg (conjSubgroup g⁻¹) hconj'
      rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one] at h
      have hbot' : conjSubgroup g⁻¹ (⊥ : Subgroup G) = ⊥ := Subgroup.map_bot _
      rwa [hbot'] at h
    exact hBne hBbot
  · rintro X ⟨B, ⟨hBΓ, hBL⟩, rfl⟩ x hx
    have hxB : (x : G) ∈ B := Subgroup.mem_subgroupOf.mp hx
    obtain ⟨g, -, hBg⟩ := Tim79a.mem_omegaOf.mp (hΓ hBΓ)
    have hxB' : (x : G) ∈ conjSubgroup g V := by rwa [hBg] at hxB
    have hB_elem : Assembly.IsElemAbelian 2 (conjSubgroup g V) := by
      change Assembly.IsElemAbelian 2 (V.map (MulAut.conj g).toMonoidHom)
      exact CFSG.Open.IsElemAbelian.map hR.toHyp.elem (MulAut.conj g).toMonoidHom
    exact Subtype.ext (by
      simpa [pow_two] using hB_elem.2 (x : G) hxB')

private theorem restrict_rel_gen
    {Γ : Set (Subgroup G)} {L : Subgroup G}
    (hL : L = ⨆ A ∈ Γ, A)
    (hpair : ∀ A ∈ Γ, ∀ B ∈ Γ, A ≠ B → ⁅A, B⁆ = ⊥ ∨ IsL2Gen A B) :
    (∀ A ∈ restrict Γ L, ∀ B ∈ restrict Γ L, A ≠ B →
      Commuting A B ∨ Opposite A B ∨ Special (restrict Γ L) A B) ∧
      (⨆ X ∈ restrict Γ L, X) = ⊤ := by
  have hΓL : ∀ B ∈ Γ, B ≤ L := by
    intro B hB
    rw [hL]
    exact le_iSup₂ (f := fun A (_ : A ∈ Γ) => A) B hB
  refine ⟨?_, ?_⟩
  · rintro A ⟨A₀, ⟨hA₀Γ, hA₀L⟩, rfl⟩ B ⟨B₀, ⟨hB₀Γ, hB₀L⟩, rfl⟩ hne
    have hne₀ : A₀ ≠ B₀ := by
      intro h
      exact hne (by rw [h])
    rcases hpair A₀ hA₀Γ B₀ hB₀Γ hne₀ with hc | hL2
    · left
      rw [CFSG.Timmesfeld.ARS.Restrict.commuting_subgroupOf_iff,
        inf_of_le_left hA₀L, inf_of_le_left hB₀L]
      exact commuting_iff_commutator_eq_bot.mpr hc
    · right; left
      exact (hL2.subgroupOf hA₀L hB₀L).opposite
  · apply Subgroup.map_injective (f := L.subtype) L.subtype_injective
    have hmap : (⨆ X ∈ restrict Γ L, X).map L.subtype =
        ⨆ X ∈ restrict Γ L, X.map L.subtype := by
      rw [Subgroup.map_iSup]
      simp only [Subgroup.map_iSup]
    have hle : (⨆ X ∈ restrict Γ L, X.map L.subtype) ≤ ⨆ B ∈ Γ, B := by
      refine iSup₂_le fun X hX => ?_
      obtain ⟨B, ⟨hBΓ, hBL⟩, rfl⟩ := hX
      rw [Subgroup.map_subgroupOf_eq_of_le hBL]
      exact le_iSup₂ (f := fun B (_ : B ∈ Γ) => B) B hBΓ
    have hge : (⨆ B ∈ Γ, B) ≤ ⨆ X ∈ restrict Γ L, X.map L.subtype := by
      refine iSup₂_le fun B hB => ?_
      have hX : B.subgroupOf L ∈ restrict Γ L :=
        CFSG.Timmesfeld.Transvection.SubgroupForm.subgroupOf_mem hB (hΓL B hB)
      rw [← Subgroup.map_subgroupOf_eq_of_le (hΓL B hB)]
      exact le_iSup₂ (f := fun X (_ : X ∈ restrict Γ L) => X.map L.subtype)
        (B.subgroupOf L) hX
    calc (⨆ X ∈ restrict Γ L, X).map L.subtype = ⨆ X ∈ restrict Γ L, X.map L.subtype := hmap
      _ = ⨆ B ∈ Γ, B := le_antisymm hle hge
      _ = L := Eq.symm hL
      _ = (⊤ : Subgroup ↥L).map L.subtype := by
        rw [Subgroup.map_top, Subgroup.range_subtype]

private theorem isRootClass_restrict
    (hS : Sec6Hyp M V) {Γ : Set (Subgroup G)} {L : Subgroup G}
    (hL : L = ⨆ A ∈ Γ, A) (hVΓ : V ∈ Γ) (hΓ : Γ ⊆ omegaSet V)
    (hclass : ∀ B ∈ Γ, ∃ g ∈ L, B = conjSubgroup g V)
    (hconjL : ∀ l ∈ L, ∀ B ∈ Γ, conjSubgroup l B ∈ Γ)
    (hpair : ∀ A ∈ Γ, ∀ B ∈ Γ, A ≠ B → ⁅A, B⁆ = ⊥ ∨ IsL2Gen A B) :
    IsRootClass (restrict Γ L) := by
  obtain ⟨h1, h2, h3⟩ := restrict_conj_ne_mul hS hL hVΓ hΓ hclass hconjL
  obtain ⟨h4, h5⟩ := restrict_rel_gen hL hpair
  exact { conj_class := h1, ne_bot := h2, mul_self := h3, rel := h4, gen := h5 }

private theorem noSpecial_restrict
    {Γ : Set (Subgroup G)} {L : Subgroup G}
    (hRoot : IsRootClass (restrict Γ L))
    (hpair : ∀ A ∈ Γ, ∀ B ∈ Γ, A ≠ B → ⁅A, B⁆ = ⊥ ∨ IsL2Gen A B) :
    ∀ A ∈ restrict Γ L, ∀ B ∈ restrict Γ L, ¬ Special (restrict Γ L) A B := by
  rintro A hA' B hB' hspec
  obtain ⟨A₀, ⟨hA₀Γ, hA₀L⟩, rfl⟩ := hA'
  obtain ⟨B₀, ⟨hB₀Γ, hB₀L⟩, rfl⟩ := hB'
  have hA'R : A₀.subgroupOf L ∈ restrict Γ L :=
    CFSG.Timmesfeld.Transvection.SubgroupForm.subgroupOf_mem hA₀Γ hA₀L
  have hA₀B₀ : A₀ ≠ B₀ := by
    intro h
    subst h
    exact hRoot.ne_bot _ hspec.1
      (commuting_iff_commutator_eq_bot.mp (hRoot.commuting_self hA'R))
  have hcommΓ : ⁅A₀, B₀⁆ ∈ Γ := by
    have hmem := CFSG.Timmesfeld.Transvection.SubgroupForm.map_subtype_mem hspec.1
    rwa [CFSG.Timmesfeld.ARS.Restrict.commutator_subgroupOf hA₀L hB₀L,
      Subgroup.map_subgroupOf_eq_of_le
        (Subgroup.commutator_le_of_le hA₀L hB₀L)] at hmem
  have hcommA : Commuting ⁅A₀, B₀⁆ A₀ := by
    have h := hspec.2.1
    rw [CFSG.Timmesfeld.ARS.Restrict.commutator_subgroupOf hA₀L hB₀L,
      CFSG.Timmesfeld.ARS.Restrict.commuting_subgroupOf_iff,
      inf_of_le_left (Subgroup.commutator_le_of_le hA₀L hB₀L),
      inf_of_le_left hA₀L] at h
    exact h
  have hcommB : Commuting ⁅A₀, B₀⁆ B₀ := by
    have h := hspec.2.2
    rw [CFSG.Timmesfeld.ARS.Restrict.commutator_subgroupOf hA₀L hB₀L,
      CFSG.Timmesfeld.ARS.Restrict.commuting_subgroupOf_iff,
      inf_of_le_left (Subgroup.commutator_le_of_le hA₀L hB₀L),
      inf_of_le_left hB₀L] at h
    exact h
  rcases hpair A₀ hA₀Γ B₀ hB₀Γ hA₀B₀ with hc | hL2
  · have hbot : ⁅A₀, B₀⁆ = ⊥ := hc
    have hsub : ⁅A₀.subgroupOf L, B₀.subgroupOf L⁆ = ⊥ := by
      rw [CFSG.Timmesfeld.ARS.Restrict.commutator_subgroupOf hA₀L hB₀L, hbot]
      simp
    exact hRoot.ne_bot _ hspec.1 hsub
  · exact hL2.not_special Γ ⟨hcommΓ, hcommA, hcommB⟩

private theorem rank_restrict
    (hS : Sec6Hyp M V) {Γ : Set (Subgroup G)} {L : Subgroup G}
    (hL : L = ⨆ A ∈ Γ, A) (hVΓ : V ∈ Γ) (hSigΓ : sigmaSet M V ⊆ Γ) :
    ∃ A ∈ restrict Γ L, ∃ B ∈ restrict Γ L, A ≠ B ∧ Commuting A B := by
  have hR := hS.sec5.toRootHyp
  have hΓL : ∀ B ∈ Γ, B ≤ L := by
    intro B hB
    rw [hL]
    exact le_iSup₂ (f := fun A (_ : A ∈ Γ) => A) B hB
  obtain ⟨U, hU⟩ := hS.ne
  have hUΓ : U ∈ Γ := hSigΓ hU
  refine ⟨V.subgroupOf L,
    CFSG.Timmesfeld.Transvection.SubgroupForm.subgroupOf_mem hVΓ (hΓL V hVΓ),
    U.subgroupOf L,
    CFSG.Timmesfeld.Transvection.SubgroupForm.subgroupOf_mem hUΓ (hΓL U hUΓ), ?_, ?_⟩
  · intro h
    have hVU : V = U :=
      (CFSG.Timmesfeld.ARS.subgroupOf_inj_of_le (hΓL V hVΓ) (hΓL U hUΓ)).mp h
    exact ne_of_mem_sigmaSet hR hU hVU.symm
  · rw [CFSG.Timmesfeld.ARS.Restrict.commuting_subgroupOf_iff,
      inf_of_le_left (hΓL V hVΓ), inf_of_le_left (hΓL U hUΓ)]
    exact fun v hv u hu =>
      (commute_iff_eq v u).mpr
        (Subgroup.mem_centralizer_iff.mp ((hS.sec5.le_M_of_mem_sigmaSet hU).2 hu) v hv)

private theorem small_restrict
    (hS : Sec6Hyp M V) {Γ : Set (Subgroup G)} {L : Subgroup G}
    (hΓ : Γ ⊆ omegaSet V) :
    (∃ A ∈ restrict Γ L, Nat.card A = 2) →
      IsSimpleGroup (commutator ↥L) ∧ ThickLines (restrict Γ L) := by
  have h4 := hS.sec5.toRootHyp.four_le_card
  rintro ⟨A, hA_R, hA2⟩
  obtain ⟨B, ⟨hBΓ, hBL⟩, rfl⟩ := hA_R
  obtain ⟨g, -, hBg⟩ := Tim79a.mem_omegaOf.mp (hΓ hBΓ)
  have hcardB : Nat.card (B.subgroupOf L) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv
  have hcardV : Nat.card B = Nat.card V := by
    rw [hBg]
    exact card_conjSubgroup g V
  have h2 : Nat.card (B.subgroupOf L) = 2 := hA2
  omega

private theorem sp_branch_false
    (hS : Sec6Hyp M V) (h60 : Sec6.Stmt60 M V)
    {Γ : Set (Subgroup G)} (hVΓ : V ∈ Γ)
    (hSigΓ : sigmaSet M V ⊆ Γ)
    (hcomm : ∀ B ∈ Γ, B ≠ V → ⁅V, B⁆ = ⊥ → B ∈ sigmaSet M V)
    {f : ℕ} (hf1 : 1 ≤ f) (hcardV : Nat.card V = 2 ^ f)
    {n : ℕ} (hn : 2 ≤ n)
    {Φ : ↥(StatedSp n (GaloisField 2 f)) →* G} (hΦinj : Function.Injective Φ)
    (hmem : ∀ X : Subgroup G, X ∈ Γ ↔
      ∃ g, X = (conjSub ((Symplectic.rootDatum n (GaloisField 2 f)).rootGroup
        (Pi.single (⟨n - 1, by omega⟩ : Fin n) 1)) g).map Φ) :
    False := by
  have hR := hS.sec5.toRootHyp
  let K := GaloisField 2 f
  let T : Subgroup ↥(StatedSp n K) :=
    (Symplectic.rootDatum n K).rootGroup (Pi.single (⟨n - 1, by omega⟩ : Fin n) 1)
  obtain ⟨x, hxV⟩ := (hmem V).mp hVΓ
  have hcardEq := card_sp_conj_commuting_eq (f := f) (n := n) hΦinj hxV hmem
  have hcardSig : Nat.card {B : Subgroup G // B ∈ Γ ∧ B ≠ V ∧ Commuting V B} =
      Nat.card (sigmaSet M V) := by
    have hset : {B : Subgroup G | B ∈ Γ ∧ B ≠ V ∧ Commuting V B} =
        sigmaSet M V := by
      ext B
      constructor
      · rintro ⟨hBΓ, hBne, hVB⟩
        exact hcomm B hBΓ hBne (commuting_iff_commutator_eq_bot.mp hVB)
      · intro hBsig
        refine ⟨hSigΓ hBsig, ne_of_mem_sigmaSet hR hBsig, ?_⟩
        intro v hv u hu
        exact (commute_iff_eq v u).mpr
          (Subgroup.mem_centralizer_iff.mp
            ((hS.sec5.le_M_of_mem_sigmaSet hBsig).2 hu) v hv)
    change Nat.card ↥{B : Subgroup G | B ∈ Γ ∧ B ≠ V ∧ Commuting V B} =
      Nat.card ↥(sigmaSet M V)
    rw [hset]
  have hKcard : Nat.card K = 2 ^ f := GaloisField.card 2 f (by omega)
  have hdvdK : Nat.card K ^ 2 ∣
      Nat.card {Y : Subgroup ↥(StatedSp n K) //
        (∃ g, Y = conjSub T g) ∧ Y ≠ T ∧ Commuting T Y} := by
    rw [hKcard, ← hcardV, hcardEq, hcardSig]
    exact h60.2.1
  exact (CFSG.Timmesfeld.Transvection.ModelRank.not_sq_dvd_card_commuting_conjSub_rootGroup_sp
    hn (K := K)) hdvdK

theorem Sec6Hyp.recog (hS : Sec6Hyp M V) (h60 : Sec6.Stmt60 M V)
    (hT : Timmesfeld.Transvection.SubgroupTransvectionStatement) {Γ : Set (Subgroup G)}
    (hΓ : Γ ⊆ omegaSet V) (hVΓ : V ∈ Γ) (hSigΓ : sigmaSet M V ⊆ Γ)
    (hpair : ∀ A ∈ Γ, ∀ B ∈ Γ, A ≠ B → ⁅A, B⁆ = ⊥ ∨ IsL2Gen A B)
    (hcomm : ∀ B ∈ Γ, B ≠ V → ⁅V, B⁆ = ⊥ → B ∈ sigmaSet M V)
    (hM : ∀ m ∈ M, ∀ B ∈ Γ, conjSubgroup m B ∈ Γ)
    (htr : ∀ A ∈ Γ, ∃ g : G, A = conjSubgroup g V ∧ ∀ B ∈ Γ, conjSubgroup g B ∈ Γ) :
    ∃ f : ℕ, ∃ hf : 2 ≤ f, Nat.card V = 2 ^ f ∧ ∃ m : ℕ, ∃ hm : 4 ≤ m,
      ∃ Φ : ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m) →* G,
        Φ.ker = Subgroup.center _ ∧ Φ.range = (⨆ A ∈ Γ, A) ∧ ∀ X : Subgroup G, X ∈ Γ ↔
          ∃ x, X = (conjSub ((Unitary.rootDatum
            (card_galoisField_two_mul (Nat.le_trans (Nat.le_add_left 1 1) hf))
            m).rootGroup
            (unitaryLongRoot m (Nat.le_trans (Nat.le_add_left 2 2) hm))) x).map Φ := by
  have hR := hS.sec5.toRootHyp
  have h4 := hR.four_le_card
  let L : Subgroup G := ⨆ A ∈ Γ, A
  have hΓL : ∀ B ∈ Γ, B ≤ L := by
    intro B hB
    exact le_iSup₂ (f := fun A (_ : A ∈ Γ) => A) B hB
  have hconjL : ∀ l ∈ L, ∀ B ∈ Γ, conjSubgroup l B ∈ Γ :=
    conjSubgroup_mem_iSup₂ hR.toHyp.le_M hM htr
  have hZL := center_map_eq_bot hS (L := L) rfl hVΓ hM htr hSigΓ
  have hcenter : Subgroup.center ↥L = ⊥ := by
    apply Subgroup.map_injective (f := L.subtype) L.subtype_injective
    rw [hZL, Subgroup.map_bot]
  have hclass := exists_conjSub_eq_of_mem_sigmaSet hS h60 (L := L) rfl hVΓ
    hpair hcomm hM hcenter
  let R : Set (Subgroup ↥L) := restrict Γ L
  have hRoot : IsRootClass R := isRootClass_restrict hS rfl hVΓ hΓ hclass hconjL hpair
  have hNoSpecial : ∀ A ∈ R, ∀ B ∈ R, ¬ Special R A B := noSpecial_restrict hRoot hpair
  have hcls : IsTransvectionClass R := ⟨hRoot, hNoSpecial⟩
  have hpoints := pointsDetermined_restrict hS h60 (L := L) rfl hSigΓ hcomm htr hRoot
  have hrank : ∃ A ∈ R, ∃ B ∈ R, A ≠ B ∧ Commuting A B :=
    rank_restrict hS rfl hVΓ hSigΓ
  have hsmall : (∃ A ∈ R, Nat.card A = 2) →
      IsSimpleGroup (commutator ↥L) ∧ ThickLines R := small_restrict hS hΓ
  have hTrans : TransvectionHyp ↥L R :=
    { finite := inferInstance
      cls := hcls
      points := hpoints
      center := hcenter
      rank := hrank
      small := hsmall }
  obtain ⟨f, hf1, hcard, hcon⟩ := hT G L Γ (fun X hX => hΓL X hX) hTrans
  have hcardV : Nat.card V = 2 ^ f := hcard V hVΓ
  have hf2 : 2 ≤ f := by
    have h4' : 4 ≤ 2 ^ f := by rw [← hcardV]; exact h4
    by_contra h
    interval_cases f <;> norm_num at h4'
  rcases hcon with ⟨n, hn, Φ, hΦinj, -, hmem⟩ | ⟨m, hm, Φ, hker, hrange, hmem⟩
  · exact (sp_branch_false hS h60 hVΓ hSigΓ hcomm hf1 hcardV hn hΦinj hmem).elim
  · refine ⟨f, hf2, hcardV, m, hm, Φ, hker, ?_, ?_⟩
    · simpa [L] using hrange
    · intro X
      exact hmem X

theorem Sec6Hyp.unitaryConclusion_of_omega (hS : Sec6Hyp M V) (h60 : Sec6.Stmt60 M V)
    (hT : Timmesfeld.Transvection.SubgroupTransvectionStatement)
    (hF : Subgroup.normalClosure (V : Set G) = generalizedFitting G)
    (hpair : ∀ A ∈ omegaSet V, ∀ B ∈ omegaSet V, A ≠ B → ⁅A, B⁆ = ⊥ ∨ IsL2Gen A B)
    (hcomm : ∀ B ∈ omegaSet V, B ≠ V → ⁅V, B⁆ = ⊥ → B ∈ sigmaSet M V) :
    UnitaryConclusion V := by
  have hVΓ : V ∈ omegaSet V := ⟨1, Subgroup.mem_top 1, (conjSubgroup_one V).symm⟩
  have hSigΓ : sigmaSet M V ⊆ omegaSet V := by
    rintro U ⟨g, rfl, -⟩
    exact ⟨g, Subgroup.mem_top g, rfl⟩
  have hM : ∀ m ∈ M, ∀ B ∈ omegaSet V, conjSubgroup m B ∈ omegaSet V := by
    intro m hm B hB
    exact Tim79a.conjSubgroup_mem_omegaOf_of_mem hB (Subgroup.mem_top m)
  have htr : ∀ A ∈ omegaSet V,
      ∃ g : G, A = conjSubgroup g V ∧ ∀ B ∈ omegaSet V, conjSubgroup g B ∈ omegaSet V := by
    rintro A ⟨g, -, hA⟩
    exact ⟨g, hA, fun B hB =>
      Tim79a.conjSubgroup_mem_omegaOf_of_mem hB (Subgroup.mem_top g)⟩
  obtain ⟨f, hf, hcardV, m, hm, Φ, hker, hrange, hmem⟩ :=
    Sec6Hyp.recog hS h60 hT (subset_rfl) hVΓ hSigΓ hpair hcomm hM htr
  refine ⟨f, hf, hcardV, hF, m, hm, Φ, ?_, hker, ?_⟩
  · rw [hrange, Quasithin.MS93.normalClosure_eq_iSup_map_conj]
    apply le_antisymm
    · refine iSup₂_le fun A hA => ?_
      obtain ⟨g, -, hA⟩ := hA
      rw [hA]
      exact le_iSup (fun g => V.map (MulAut.conj g).toMonoidHom) g
    · refine iSup_le fun g => ?_
      exact le_iSup₂ (f := fun A (_ : A ∈ omegaSet V) => A) (conjSubgroup g V)
        ⟨g, Subgroup.mem_top g, rfl⟩
  · intro X
    have hX : (∃ g, X = conjSubgroup g V) ↔ X ∈ omegaSet V := by
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨g, Subgroup.mem_top g, rfl⟩
      · rintro ⟨g, -, hg⟩
        exact ⟨g, hg⟩
    exact hX.trans (hmem X)

private theorem V_inf_generalizedFitting_ne_bot
    (hS : Sec6Hyp M V) :
    V ⊓ generalizedFitting G ≠ ⊥ := by
  have hR := hS.sec5.toRootHyp
  have h4 := hR.four_le_card
  have hFnormal : (generalizedFitting G).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := G)).2
  obtain ⟨T, hTM, hQT⟩ := hR.toHyp.exists_sylow_le_M
  obtain ⟨X, hXcomp⟩ := hR.toHyp.exists_isComponent h4
  have hXleF : X ≤ generalizedFitting G :=
    (CFSG.LocalCores.component_le_layer hXcomp).trans le_sup_right
  have hTX : (T : Subgroup G) ⊓ X ≠ ⊥ :=
    hR.toHyp.sylow_inf_component_ne_bot h4 T hXcomp
  have hTF : (T : Subgroup G) ⊓ generalizedFitting G ≠ ⊥ := by
    intro hbot
    refine hTX (le_bot_iff.mp ?_)
    exact (le_inf inf_le_left (inf_le_right.trans hXleF)).trans (le_of_eq hbot)
  have hSne : (generalizedFitting G).subgroupOf (T : Subgroup G) ≠ ⊥ := by
    intro hbot
    apply hTF
    rw [Subgroup.subgroupOf_eq_bot] at hbot
    rw [inf_comm]
    exact disjoint_iff.mp hbot
  haveI : Group.IsNilpotent ↥(T : Subgroup G) := T.isPGroup'.isNilpotent
  obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal (G := ↥(T : Subgroup G)) hSne)
  have hyF : ((y : ↥(T : Subgroup G)) : G) ∈ generalizedFitting G :=
    Subgroup.mem_subgroupOf.mp y.2.1
  have hyT : ((y : ↥(T : Subgroup G)) : G) ∈ (T : Subgroup G) :=
    (y : ↥(T : Subgroup G)).2
  have hyC : ((y : ↥(T : Subgroup G)) : G) ∈
      Subgroup.centralizer ((T : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val
      (Subgroup.mem_center_iff.mp y.2.2 ⟨t, ht⟩)
  have hyV : ((y : ↥(T : Subgroup G)) : G) ∈ V :=
    hR.toHyp.center_sylow_le hTM T.isPGroup' hQT ⟨hyT, hyC⟩
  intro hbot
  have hmem : ((y : ↥(T : Subgroup G)) : G) ∈ V ⊓ generalizedFitting G :=
    Subgroup.mem_inf.mpr ⟨hyV, hyF⟩
  rw [hbot] at hmem
  apply hy1
  exact Subtype.ext (Subtype.ext (Subgroup.mem_bot.mp hmem))

private theorem V_le_generalizedFitting
    (hS : Sec6Hyp M V) (h60 : Sec6.Stmt60 M V) :
    V ≤ generalizedFitting G := by
  have hR := hS.sec5.toRootHyp
  have h4 := hR.four_le_card
  have hFnormal : (generalizedFitting G).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := G)).2
  have hVF : V ⊓ generalizedFitting G ≠ ⊥ := V_inf_generalizedFitting_ne_bot hS
  obtain ⟨U, hUsig⟩ := hS.ne
  obtain ⟨U', hU'sig, hL2⟩ := h60.1 U hUsig
  have hU4 : 4 ≤ Nat.card U := by
    obtain ⟨g, rfl, -⟩ := hUsig
    rw [card_conjSubgroup g V]
    exact h4
  have hUinfF : U ⊓ generalizedFitting G ≠ ⊥ := by
    obtain ⟨g, hUg, -⟩ := hUsig
    have hconjF : conjSubgroup g (generalizedFitting G) = generalizedFitting G := by
      apply conjSubgroup_eq_self_iff.mpr
      rw [Subgroup.normalizer_eq_top_iff.mpr hFnormal]
      exact Subgroup.mem_top g
    have hconj : conjSubgroup g (V ⊓ generalizedFitting G) ≠ ⊥ := by
      intro hbot
      apply hVF
      have h := congrArg (conjSubgroup g⁻¹) hbot
      rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one] at h
      have hmap : CGT.Timmesfeld75.conjSubgroup g⁻¹ (⊥ : Subgroup G) = ⊥ :=
        Subgroup.map_bot _
      rwa [hmap] at h
    rw [conjSubgroup_inf, hconjF, ← hUg] at hconj
    exact hconj
  let H : Subgroup G := U ⊔ U'
  haveI : IsSimpleGroup ↥H := hL2.isSimpleGroup hU4
  have hHF : H ⊓ generalizedFitting G ≠ ⊥ := by
    intro hbot
    apply hUinfF
    refine le_bot_iff.mp ?_
    exact (le_inf (inf_le_left.trans le_sup_left) inf_le_right).trans (le_of_eq hbot)
  have hNne : (generalizedFitting G).subgroupOf H ≠ ⊥ := by
    intro hbot
    apply hHF
    rw [Subgroup.subgroupOf_eq_bot] at hbot
    rw [inf_comm]
    exact disjoint_iff.mp hbot
  have hNtop : (generalizedFitting G).subgroupOf H = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((generalizedFitting G).subgroupOf H) with h | h
    · exact absurd h hNne
    · exact h
  have hHleF : H ≤ generalizedFitting G := by
    intro x hx
    have hmem : (⟨x, hx⟩ : ↥H) ∈ (generalizedFitting G).subgroupOf H := by
      rw [hNtop]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hmem
  have hUleF : U ≤ generalizedFitting G := le_sup_left.trans hHleF
  refine (h60.2.2 U hUsig).trans ?_
  rw [Subgroup.commutator_le]
  intro p hp u hu
  exact (generalizedFitting G).mul_mem
    (hFnormal.conj_mem u (hUleF hu) p) ((generalizedFitting G).inv_mem (hUleF hu))

theorem Sec6Hyp.normalClosure_eq (hS : Sec6Hyp M V) (h60 : Sec6.Stmt60 M V) :
    Subgroup.normalClosure (V : Set G) = generalizedFitting G := by
  have hR := hS.sec5.toRootHyp
  have h4 := hR.four_le_card
  have hsimple := hR.toHyp.isSimpleGroup_generalizedFitting h4
  let F := generalizedFitting G
  have hFnormal : F.Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := G)).2
  haveI : IsSimpleGroup ↥F := hsimple.1
  haveI : F.Normal := hFnormal
  have hVF : V ≤ F := V_le_generalizedFitting hS h60
  have hNleF : Subgroup.normalClosure (V : Set G) ≤ F :=
    Subgroup.normalClosure_le_normal (fun v hv => hVF hv)
  have hNne : Subgroup.normalClosure (V : Set G) ≠ ⊥ := by
    intro hbot
    have hVle : V ≤ Subgroup.normalClosure (V : Set G) := Subgroup.subset_normalClosure
    exact hR.toHyp.ne_bot (le_bot_iff.mp (hVle.trans (le_of_eq hbot)))
  haveI : ((Subgroup.normalClosure (V : Set G)).subgroupOf F).Normal :=
    Subgroup.Normal.subgroupOf
      (inferInstance : (Subgroup.normalClosure (V : Set G)).Normal) F
  have hNsubne : (Subgroup.normalClosure (V : Set G)).subgroupOf F ≠ ⊥ := by
    intro hbot
    have hVle : V ≤ Subgroup.normalClosure (V : Set G) := Subgroup.subset_normalClosure
    have hVinf : V ≤ Subgroup.normalClosure (V : Set G) ⊓ F := le_inf hVle hVF
    have hVbot : V = ⊥ := le_bot_iff.mp
      (hVinf.trans (le_of_eq (disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp hbot))))
    exact hR.toHyp.ne_bot hVbot
  have hNtop : (Subgroup.normalClosure (V : Set G)).subgroupOf F = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((Subgroup.normalClosure (V : Set G)).subgroupOf F) with h | h
    · exact absurd h hNsubne
    · exact h
  have hFleN : F ≤ Subgroup.normalClosure (V : Set G) := by
    intro x hx
    have hmem : (⟨x, hx⟩ : ↥F) ∈
        (Subgroup.normalClosure (V : Set G)).subgroupOf F := by
      rw [hNtop]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hmem
  exact le_antisymm hNleF hFleN
end CFSG.RankThree.GF2n.Tim81
