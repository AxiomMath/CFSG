module

public import CFSG.Quasithin.EmptyFaithful.SBc9AvgCocycle
public import CFSG.Quasithin.EmptyFaithful.SBc9AvgCoinv
public import CFSG.Quasithin.EmptyFaithful.SBc7Hyp
public import CFSG.Quasithin.EmptyFaithful.SBd5Perf

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SBc9

section Short

variable {G : Type} [Group G] {L : Subgroup G}

theorem blockU_facts (hshort : IsShort2 L) :
    blockU L ≤ pCoreOf 2 L ∧ (∀ x ∈ blockU L, ∀ y ∈ blockU L, x * y = y * x) ∧
      ∀ x ∈ blockU L, x * x = 1 := by
  obtain ⟨-, -, ⟨hU, hsq⟩, -, -⟩ := hshort
  refine ⟨fun x hx => (hU hx).1, fun x hx y hy => ?_, fun x hx => by rw [← sq]; exact hsq x hx⟩
  exact (Subgroup.mem_centralizer_iff.mp (hU hx).2 y (hU hy).1).symm

end Short

section Perfect

theorem centralizes_of_perfect {G : Type} [Group G] {L Z : Subgroup G} {d : G}
    (hL : ⁅L, L⁆ = L) (hZc : ∀ z ∈ Z, ∀ l ∈ L, l * z * l⁻¹ = z)
    (hZ : ∀ z ∈ Z, ∀ z' ∈ Z, z * z' = z' * z)
    (hd : ∀ l ∈ L, l * d * l⁻¹ * d⁻¹ ∈ Z) : d ∈ Subgroup.centralizer (L : Set G) := by
  have hmul : ∀ x ∈ L, ∀ y ∈ L, (x * y) * d * (x * y)⁻¹ * d⁻¹ =
      (y * d * y⁻¹ * d⁻¹) * (x * d * x⁻¹ * d⁻¹) := by
    intro x hx y hy
    have h1 : x * (y * d * y⁻¹ * d⁻¹) * x⁻¹ = y * d * y⁻¹ * d⁻¹ := hZc _ (hd y hy) x hx
    calc (x * y) * d * (x * y)⁻¹ * d⁻¹
        = x * (y * d * y⁻¹ * d⁻¹) * x⁻¹ * (x * d * x⁻¹ * d⁻¹) := by group
      _ = (y * d * y⁻¹ * d⁻¹) * (x * d * x⁻¹ * d⁻¹) := by rw [h1]
  have hinv : ∀ x ∈ L, x⁻¹ * d * x⁻¹⁻¹ * d⁻¹ = (x * d * x⁻¹ * d⁻¹)⁻¹ := by
    intro x hx
    have h := hmul x hx x⁻¹ (L.inv_mem hx)
    have h' : (x⁻¹ * d * x⁻¹⁻¹ * d⁻¹) * (x * d * x⁻¹ * d⁻¹) = 1 := by
      rw [← h]
      group
    exact eq_inv_of_mul_eq_one_left h'
  have hcomm : ∀ a ∈ L, ∀ b ∈ L, (a * b * a⁻¹ * b⁻¹) * d * (a * b * a⁻¹ * b⁻¹)⁻¹ * d⁻¹ = 1 := by
    intro a ha b hb
    have hu := hd a ha
    have hv := hd b hb
    have e1 := hmul a ha (b * (a⁻¹ * b⁻¹)) (L.mul_mem hb (L.mul_mem (L.inv_mem ha) (L.inv_mem hb)))
    have e2 := hmul b hb (a⁻¹ * b⁻¹) (L.mul_mem (L.inv_mem ha) (L.inv_mem hb))
    have e3 := hmul a⁻¹ (L.inv_mem ha) b⁻¹ (L.inv_mem hb)
    have hba : a * b * a⁻¹ * b⁻¹ = a * (b * (a⁻¹ * b⁻¹)) := by group
    rw [hba, e1, e2, e3, hinv a ha, hinv b hb]
    set u := a * d * a⁻¹ * d⁻¹ with hudef
    set v := b * d * b⁻¹ * d⁻¹ with hvdef
    have huv : u * v = v * u := hZ u hu v hv
    calc v⁻¹ * u⁻¹ * v * u = (u * v)⁻¹ * (v * u) := by group
      _ = 1 := by rw [← huv, inv_mul_cancel]
  have hLc : L ≤ Subgroup.centralizer ({d} : Set G) := by
    calc L = ⁅L, L⁆ := hL.symm
      _ ≤ Subgroup.centralizer ({d} : Set G) := by
        rw [Subgroup.commutator_le]
        intro a ha b hb
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx, commutatorElement_def]
        have h1 : (a * b * a⁻¹ * b⁻¹) * d * (a * b * a⁻¹ * b⁻¹)⁻¹ = d :=
          mul_inv_eq_one.mp (hcomm a ha b hb)
        exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact (Subgroup.mem_centralizer_iff.mp (hLc hl) d (Set.mem_singleton d)).symm

end Perfect

section Main

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem cover_of_centralizer_le (c : Ctx15331 T Mc M V₁ V₂ Yp I L t) (hshort : IsShort2 L)
    (hCZ : ∀ q ∈ blockU L, q ∈ Subgroup.centralizer (Yp : Set G) → q ∈ blockZ L)
    {d : G} (hdY : d ∈ Subgroup.centralizer (Yp : Set G))
    (hdQ : d ∈ Subgroup.centralizer (blockU L : Set G))
    (hcomm : ⁅L, Subgroup.zpowers d⁆ ≤ centerOf (blockU L)) :
    d ∈ Subgroup.centralizer (L : Set G) := by
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t := c.toCtx15328.toCtx15327.toCtx15325L
  have hF : Facts15325 T Mc M V₁ V₂ Yp I := c25.facts
  have hsyl : IsSylowTwoOf (Sgp153 T V₁) I := hF.sylow
  have hLc : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ c25.conc.1
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hIL : I ≤ Subgroup.normalizer (L : Set G) := c.c27.normal
  have hYL : Yp ≤ L := c.c27.Yp_le
  have hSM : Sgp153 T V₁ ≤ M := inf_le_right.trans c.c29.norm_le
  have hLperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hLc
  obtain ⟨hQP, hQc, -⟩ := blockU_facts hshort
  have hLQ : L ≤ Subgroup.normalizer (blockU L : Set G) :=
    Subgroup.normalizer_commutator_ge_right (pCoreOf 2 L) L
  have hW2 : IsPGroup 2 ↥(blockU L) := (pCoreOf_isPGroup 2 L).to_le hQP
  have hQsyl : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L := B6.isSylowTwoOf_inf_normal hsyl hLI hIL
  have hodd : ¬ 2 ∣ (M ⊓ L).relIndex L := fun h2 =>
    hQsyl.2.2 (h2.trans (Subgroup.relIndex_dvd_of_le_left L (inf_le_inf_right L hSM)))
  have hZQ : blockZ L ≤ blockU L := inf_le_left
  have hZc : ∀ z ∈ blockZ L, ∀ l ∈ L, l * z * l⁻¹ = z := fun z hz l hl => by
    have h := Subgroup.mem_centralizer_iff.mp hz.2 l hl
    calc l * z * l⁻¹ = (z * l) * l⁻¹ := by rw [h]
      _ = z := by group
  have hLZ : ∀ l ∈ L, ∀ z ∈ blockZ L, l * z * l⁻¹ ∈ blockZ L := fun l hl z hz => by
    rw [hZc z hz l hl]
    exact hz
  have hdW : ∀ w ∈ blockU L, d * w * d⁻¹ = w := fun w hw => by
    have h := Subgroup.mem_centralizer_iff.mp hdQ w hw
    calc d * w * d⁻¹ = (w * d) * d⁻¹ := by rw [h]
      _ = w := by group
  have hd : ∀ l ∈ L, l * d * l⁻¹ * d⁻¹ ∈ blockU L := fun l hl => by
    have h := hcomm (Subgroup.commutator_mem_commutator hl (Subgroup.mem_zpowers d))
    rw [commutatorElement_def] at h
    exact h.1
  have hMIYp : M ⊓ I ≤ Subgroup.normalizer (Yp : Set G) := by
    rw [← hF.norm_eq]
    exact inf_le_right
  have hP : ∀ p ∈ M ⊓ L, p * d * p⁻¹ * d⁻¹ ∈ blockZ L := by
    intro p hp
    have hpI : p ∈ M ⊓ I := ⟨hp.1, hLI hp.2⟩
    have hδC : p * d * p⁻¹ * d⁻¹ ∈ Subgroup.centralizer (Yp : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy2 : p⁻¹ * y * p ∈ Yp := by
        have := (Subgroup.mem_normalizer_iff.mp (hMIYp ((M ⊓ I).inv_mem hpI)) y).mp hy
        simpa using this
      have hdy : y * d = d * y := Subgroup.mem_centralizer_iff.mp hdY y hy
      have hdy2 : (p⁻¹ * y * p) * d = d * (p⁻¹ * y * p) :=
        Subgroup.mem_centralizer_iff.mp hdY _ hy2
      calc y * (p * d * p⁻¹ * d⁻¹)
          = p * ((p⁻¹ * y * p) * d) * p⁻¹ * d⁻¹ := by group
        _ = p * (d * (p⁻¹ * y * p)) * p⁻¹ * d⁻¹ := by rw [hdy2]
        _ = p * d * p⁻¹ * (y * d⁻¹) := by group
        _ = p * d * p⁻¹ * (d⁻¹ * y) := by
          have : y * d⁻¹ = d⁻¹ * y := by
            have h1 : d⁻¹ * (y * d) * d⁻¹ = d⁻¹ * (d * y) * d⁻¹ := by rw [hdy]
            exact (by simpa [mul_assoc] using h1 : d⁻¹ * y = y * d⁻¹).symm
          rw [this]
        _ = (p * d * p⁻¹ * d⁻¹) * y := by group
    exact hCZ _ (hd p hp.2) hδC
  obtain ⟨m, hmQ, hm⟩ := exists_mul_mod_of_cocycle hLQ hQc hW2 hZQ hLZ hodd hdW hd hP
  have hdm : d * m⁻¹ ∈ Subgroup.centralizer (L : Set G) :=
    centralizes_of_perfect hLperf hZc (fun z hz z' hz' => hQc z (hZQ hz) z' (hZQ hz')) hm
  have hmC : m ∈ Subgroup.centralizer (Yp : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyd : y * d = d * y := Subgroup.mem_centralizer_iff.mp hdY y hy
    have h1 : y * (d * m⁻¹) = (d * m⁻¹) * y := Subgroup.mem_centralizer_iff.mp hdm y (hYL hy)
    have h2 : y * m⁻¹ * y⁻¹ = m⁻¹ := by
      have h3 : y * (d * m⁻¹) * y⁻¹ = (y * d * y⁻¹) * (y * m⁻¹ * y⁻¹) := by group
      have h4 : y * d * y⁻¹ = d := by
        calc y * d * y⁻¹ = (d * y) * y⁻¹ := by rw [hyd]
          _ = d := by group
      have h5 : y * (d * m⁻¹) * y⁻¹ = d * m⁻¹ := by
        calc y * (d * m⁻¹) * y⁻¹ = ((d * m⁻¹) * y) * y⁻¹ := by rw [h1]
          _ = d * m⁻¹ := by group
      rw [h3, h4] at h5
      exact mul_left_cancel h5
    have h6 : y * m * y⁻¹ = m := by
      have := congrArg Inv.inv h2
      simpa [mul_assoc] using this
    calc y * m = (y * m * y⁻¹) * y := by group
      _ = m * y := by rw [h6]
  have hmZ : m ∈ blockZ L := hCZ m hmQ hmC
  have := (Subgroup.centralizer (L : Set G)).mul_mem hdm hmZ.2
  rwa [inv_mul_cancel_right] at this

theorem blockU_le_Yp_of_cover (c : Ctx15331 T Mc M V₁ V₂ Yp I L t) (hshort : IsShort2 L)
    (hQ : ∀ q ∈ blockU L, ∃ r ∈ ⁅blockU L, Yp⁆, r⁻¹ * q ∈ blockZ L) : blockU L ≤ Yp := by
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t := c.toCtx15328.toCtx15327.toCtx15325L
  have hF : Facts15325 T Mc M V₁ V₂ Yp I := c25.facts
  have hsyl : IsSylowTwoOf (Sgp153 T V₁) I := hF.sylow
  have hLc : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ c25.conc.1
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hIL : I ≤ Subgroup.normalizer (L : Set G) := c.c27.normal
  have hYL : Yp ≤ L := c.c27.Yp_le
  have hSM : Sgp153 T V₁ ≤ M := inf_le_right.trans c.c29.norm_le
  obtain ⟨hQP, hQc, hQ2⟩ := blockU_facts hshort
  have hLQ : L ≤ Subgroup.normalizer (blockU L : Set G) :=
    Subgroup.normalizer_commutator_ge_right (pCoreOf 2 L) L
  have hQsyl : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L := B6.isSylowTwoOf_inf_normal hsyl hLI hIL
  have hodd : ¬ 2 ∣ (M ⊓ L).relIndex L := fun h2 =>
    hQsyl.2.2 (h2.trans (Subgroup.relIndex_dvd_of_le_left L (inf_le_inf_right L hSM)))
  have hMIYp : M ⊓ I ≤ Subgroup.normalizer (Yp : Set G) := by
    rw [← hF.norm_eq]
    exact inf_le_right
  have hQY : blockU L ≤ Subgroup.normalizer (Yp : Set G) :=
    (SBc7.blockU_le_Sgp c.toCtx15330).trans (SBc7.Sgp_le_normalizer_Yp c.toCtx15330)
  have hRQ : ⁅blockU L, Yp⁆ ≤ blockU L :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hYL.trans hLQ)
  have hRY : ⁅blockU L, Yp⁆ ≤ Yp := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hQY
  have hPR : ∀ p ∈ M ⊓ L, ∀ r ∈ ⁅blockU L, Yp⁆, p * r * p⁻¹ ∈ ⁅blockU L, Yp⁆ := by
    intro p hp r hr
    have hpI : p ∈ M ⊓ I := ⟨hp.1, hLI hp.2⟩
    exact (Subgroup.mem_normalizer_iff.mp
      (SBd5.mem_normalizer_commutator_of (hLQ hp.2) (hMIYp hpI)) r).mp hr
  have hQPR : ⁅blockU L, M ⊓ L⁆ ≤ ⁅blockU L, Yp⁆ := by
    rw [Subgroup.commutator_le]
    intro q hq p hp
    obtain ⟨r, hrR, hz⟩ := hQ q hq
    have hzp : (r⁻¹ * q) * p = p * (r⁻¹ * q) := (Subgroup.mem_centralizer_iff.mp hz.2 p hp.2).symm
    have e : ⁅q, p⁆ = r * (p * r⁻¹ * p⁻¹) := by
      rw [commutatorElement_def]
      calc q * p * q⁻¹ * p⁻¹ = r * ((r⁻¹ * q) * p) * q⁻¹ * p⁻¹ := by group
        _ = r * (p * (r⁻¹ * q)) * q⁻¹ * p⁻¹ := by rw [hzp]
        _ = r * (p * r⁻¹ * p⁻¹) := by group
    rw [e]
    exact (⁅blockU L, Yp⁆).mul_mem hrR (hPR p hp r⁻¹ ((⁅blockU L, Yp⁆).inv_mem hrR))
  have hZR : blockZ L ≤ ⁅blockU L, Yp⁆ :=
    (inf_centralizer_le_commutator_of_odd_index hLQ hQc hQ2 inf_le_right hodd
      (C1.commutator_blockU hshort) : blockZ L ≤ ⁅blockU L, M ⊓ L⁆).trans hQPR
  intro q hq
  obtain ⟨r, hrR, hz⟩ := hQ q hq
  have e : q = r * (r⁻¹ * q) := by group
  rw [e]
  exact Yp.mul_mem (hRY hrR) (hRY (hZR hz))

end Main

end SBc9

end CFSG.Quasithin
