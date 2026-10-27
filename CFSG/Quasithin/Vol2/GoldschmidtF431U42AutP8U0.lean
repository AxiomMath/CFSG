module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8Q2
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8Q3

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431

structure QData {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}
    (c : AutCtx G M₁ M₂ z) where
  Q : Subgroup ↥(cenOf (c.iso.toG fhB))
  normal : Q.Normal
  index_eq : Q.index = 8
  eq_closure : Q = Subgroup.closure {x : ↥(cenOf (c.iso.toG fhB)) | Odd (orderOf x)}
  equiv : ↥Q ≃* alternatingGroup (Fin 6)

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

section Basic

variable (c : AutCtx G M₁ M₂ z) {R : Subgroup G}

theorem exists_QData
    (h : F55Ctx c R) : Nonempty (QData c) := by
  obtain ⟨ρ, hρ, hρ2⟩ := exists_rho c h
  obtain ⟨Q, hQn, hQi, hQR, hQc⟩ := exists_Q c h (⟨hρ, hρ2⟩ : RhoCtx c R ρ)
  have := hQn
  rcases Q_recog c h hQi hQR hQc with he | he
  · obtain ⟨e⟩ := he
    exact (Q_not_L32 c h hQi hQc e).elim
  · obtain ⟨e⟩ := he
    exact ⟨⟨Q, hQn, hQi, hQc, e⟩⟩

theorem card_Alt1h : Nat.card ↥Alt1h = 12 := by
  apply le_antisymm
  · have := card_le_length_of_reps Alt1h (F := Alt1L) (fun g hg => hg)
    rwa [Alt1_check.2.2.2.1] at this
  · have := length_le_card_of_nodup Alt1h (L := Alt1L) Alt1_check.2.2.1 (fun l hl => by
      obtain ⟨g, hg, hrep⟩ := exists_elt_Alt1 hl
      exact ⟨g, hg, hrep⟩)
    rwa [Alt1_check.2.2.2.1] at this

theorem card_B1G : Nat.card ↥(B1G c) = 12 := by
  rw [B1G, Subgroup.card_map_of_injective c.iso.toG1_injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Alt1h_le_C1.trans inf_le_left)).toEquiv]
  exact card_Alt1h

theorem B1G_le_oddCl : B1G c ≤ oddCl (cenOf (c.iso.toG fhB)) := by
  rw [B1G_eq_oddCl c]
  exact oddCl_mono (E1G_le_cen c)

theorem oddCl_conj_cen {n y : G} (hn : n ∈ cenOf (c.iso.toG fhB))
    (hy : y ∈ oddCl (cenOf (c.iso.toG fhB))) : n * y * n⁻¹ ∈ oddCl (cenOf (c.iso.toG fhB)) :=
  oddCl_conj (fun _ hx => (cenOf (c.iso.toG fhB)).mul_mem
    ((cenOf (c.iso.toG fhB)).mul_mem hn hx) ((cenOf (c.iso.toG fhB)).inv_mem hn)) hy

end Basic

namespace QData

variable {c : AutCtx G M₁ M₂ z} (qd : QData c)

include qd

theorem card_Q : Nat.card ↥qd.Q = 360 := by
  rw [Nat.card_congr qd.equiv.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem oddCl_eq :
    oddCl (cenOf (c.iso.toG fhB)) = qd.Q.map (cenOf (c.iso.toG fhB)).subtype := by
  apply le_antisymm
  · intro y hy
    obtain ⟨hy', hq⟩ := oddCl_subtype hy
    exact ⟨⟨y, hy'⟩, by rw [qd.eq_closure]; exact hq, rfl⟩
  · rintro _ ⟨q, hq, rfl⟩
    rw [qd.eq_closure] at hq
    induction hq using Subgroup.closure_induction with
    | mem x hx =>
      refine Subgroup.subset_closure ⟨x.2, ?_⟩
      show Odd (orderOf ((x : ↥(cenOf (c.iso.toG fhB))) : G))
      rw [Subgroup.orderOf_coe]
      exact hx
    | one => exact (oddCl _).one_mem
    | mul x y _ _ hx hy => exact (oddCl _).mul_mem hx hy
    | inv x _ hx => exact (oddCl _).inv_mem hx

theorem card_oddCl : Nat.card ↥(oddCl (cenOf (c.iso.toG fhB))) = 360 := by
  rw [qd.oddCl_eq, Subgroup.card_map_of_injective (cenOf (c.iso.toG fhB)).subtype_injective]
  exact qd.card_Q

theorem mem_oddCl_iff (g : G) :
    g ∈ oddCl (cenOf (c.iso.toG fhB)) ↔
      ∃ q : ↥qd.Q, (((q : ↥(cenOf (c.iso.toG fhB))) : G)) = g := by
  rw [qd.oddCl_eq, Subgroup.mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨⟨q, hq⟩, rfl⟩
  · rintro ⟨q, rfl⟩
    exact ⟨q, q.2, rfl⟩

theorem center_trivial {y : G} (hy : y ∈ oddCl (cenOf (c.iso.toG fhB)))
    (hcen : ∀ q ∈ oddCl (cenOf (c.iso.toG fhB)), y * q = q * y) : y = 1 := by
  obtain ⟨q₀, rfl⟩ := (qd.mem_oddCl_iff y).1 hy
  have hz : qd.equiv q₀ ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨q, rfl⟩ := qd.equiv.surjective w
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    exact (hcen _ ((qd.mem_oddCl_iff _).2 ⟨q, rfl⟩)).symm
  rw [CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.center_eq_bot,
    Subgroup.mem_bot] at hz
  have : q₀ = 1 := qd.equiv.injective (hz.trans (map_one qd.equiv).symm)
  rw [this]
  rfl

end QData

end CFSG.Quasithin.H13.F431.U42Aut
