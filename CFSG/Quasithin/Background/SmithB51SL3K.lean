module

public import CFSG.Quasithin.Background.SmithB51SL3J

public section

namespace CFSG.Quasithin

namespace B5

open CFSG.Assembly.LowTwoRank

section SplitData

variable {V : Type} [CommGroup V] {G L : Subgroup (MulAut V)}

structure SL3Split (G L : Subgroup (MulAut V)) : Type 1 where
  A : Subgroup (MulAut V)
  I : Subgroup V
  K : Type
  [instField : Field K]
  [instFinite : Finite K]
  n : ℕ
  hK : Nat.card K = 2 ^ n
  hmin : IsFFStarMin G A
  hAL : A ≤ L
  hquad : IsQuadratic A
  hIU : I ≤ commV L
  hLI : L ≤ stabSub I
  e₁ : NatSec L I ⊥ K
  e₂ : NatSec L (commV L) I K
  hπ : e₂.π = e₁.π
  hpre : e₁.pre A = axisSub (stdAxis K)
  hcardA : Nat.card A = Nat.card K ^ 2
  σ : Multiplicative (Fin 3 → K) →* ↥(commV L)
  hσf : ∀ s, e₂.f (σ s) = s
  hσe : ∀ (γ : ↥(StatedSL 3 K)) (s : Multiplicative (Fin 3 → K)),
    ((e₁.π γ : ↥L) : MulAut V) (σ s) = σ (natAct (StatedSL 3 K) γ s)

attribute [instance] SL3Split.instField SL3Split.instFinite

theorem le_stabSub_commV_self' : L ≤ stabSub (commV L) :=
  le_stabSub_commV (fun _ hg _ hl => L.mul_mem (L.mul_mem hg hl) (L.inv_mem hg))
    (fun _ hg => L.inv_mem hg)

theorem exists_sl3Split [Finite V] (hA21 : AsA21SQTKSection) (hB42 : AsB42) (hA36 : AsA36NoOddCover)
    (hIH : B51Part1Below (Nat.card V)) (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L)
    (hU : commV L ∉ IrrPlus L ⊤) {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (eL : ↥L ≃* ↥(StatedSL 3 K)) : Nonempty (SL3Split G L) := by
  obtain ⟨s⟩ := exists_sl3Std hA21 hB42 hA36 hIH hV h hU hK eL
  have : CharP s.K 2 := charP_two_of_card_eq s.hK
  have hq : 2 ∣ Nat.card s.K := by
    rw [s.hK]
    rcases Nat.eq_zero_or_pos s.n with h0 | h0
    · have : (1 : ℕ) < Nat.card s.K := Finite.one_lt_card
      rw [s.hK, h0] at this
      norm_num at this
    · exact dvd_pow_self 2 h0.ne'
  have hpre₂ : s.e₂.pre s.A = axisSub (stdAxis s.K) := by
    rw [← s.hpre]
    unfold NatSec.pre
    rw [s.hπ]
  obtain ⟨σ, hσf, hσe⟩ := exists_equivariant_section hV s.hIU le_stabSub_commV_self' s.hLI s.e₁
    s.e₂ s.hπ s.hAL s.hquad hpre₂ s.hlift hq
  refine ⟨⟨s.A, s.I, s.K, s.n, s.hK, s.hmin, s.hAL, s.hquad, s.hIU, s.hLI, s.e₁, s.e₂, s.hπ,
    s.hpre, s.hcardA, σ, hσf, fun γ x => ?_⟩⟩
  rw [← s.hπ]
  exact hσe γ x

variable (s : SL3Split G L)

@[expose] def SL3Split.I' : Subgroup V := s.σ.range.map (commV L).subtype

theorem SL3Split.mem_I' {x : V} : x ∈ s.I' ↔ ∃ y, ((s.σ y : ↥(commV L)) : V) = x := by
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨_, ⟨y, rfl⟩, rfl⟩

theorem SL3Split.I'_le : s.I' ≤ commV L := by
  rintro _ ⟨_, -, rfl⟩
  exact Subtype.coe_prop _

theorem SL3Split.inf_eq_bot : s.I' ⊓ s.I = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, hxI⟩
  obtain ⟨y, rfl⟩ := (s.mem_I').1 hx
  have h1 : s.e₂.f (s.σ y) = 1 := (s.e₂.hfk _).2 hxI
  rw [s.hσf] at h1
  rw [h1, map_one, Subgroup.coe_one]
  exact Subgroup.one_mem _

theorem SL3Split.sup_eq : s.I' ⊔ s.I = commV L := by
  refine le_antisymm (sup_le s.I'_le s.hIU) fun u hu => ?_
  set y := s.σ (s.e₂.f ⟨u, hu⟩) with hy
  have hyI : ((y : ↥(commV L)) : V)⁻¹ * u ∈ s.I := by
    have hmem : ((y : ↥(commV L)) : V)⁻¹ * u ∈ commV L :=
      (commV L).mul_mem ((commV L).inv_mem y.2) hu
    rw [← s.e₂.hfk ⟨_, hmem⟩]
    have e1 : (⟨_, hmem⟩ : ↥(commV L)) = y⁻¹ * ⟨u, hu⟩ := rfl
    rw [e1, map_mul, map_inv, hy, s.hσf, inv_mul_cancel]
  have : u = (y : V) * ((y : V)⁻¹ * u) := by group
  rw [this]
  exact Subgroup.mul_mem_sup ((s.mem_I').2 ⟨_, rfl⟩) hyI

theorem SL3Split.hLI' : L ≤ stabSub s.I' := by
  intro l hl
  have key : ∀ l ∈ L, ∀ x ∈ s.I', l x ∈ s.I' := by
    intro l hl x hx
    obtain ⟨y, rfl⟩ := (s.mem_I').1 hx
    obtain ⟨γ, hγ⟩ := s.e₁.hπ.2 ⟨l, hl⟩
    have h1 := s.hσe γ y
    rw [hγ] at h1
    exact (s.mem_I').2 ⟨_, h1.symm⟩
  exact mem_stabSub_of_inv (key l hl) (key l⁻¹ (L.inv_mem hl))

@[expose] noncomputable def SL3Split.e₁' : NatSec L s.I' ⊥ s.K :=
  (s.e₂.restrict s.I'_le s.sup_eq).ofEq s.inf_eq_bot

theorem SL3Split.e₁'_π : s.e₁'.π = s.e₁.π := by
  rw [← s.hπ]
  exact MonoidHom.ext fun γ => NatSec.ofEq_π _ _ γ

end SplitData

end B5

end CFSG.Quasithin
