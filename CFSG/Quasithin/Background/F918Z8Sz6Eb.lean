module

public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

theorem BinaryNaturalSL.exists_natEquiv {V : Type*} [CommGroup V] {L : Subgroup (MulAut V)}
    {d a : ℕ} (h : BinaryNaturalSL L ⊤ ⊥ d a) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ a ∧
      ∃ e : V ≃* Multiplicative (Fin d → K), ∀ g : ↥(StatedSL d K), ∃ l ∈ L, ∀ r : V,
        e (l r) = natAct (StatedSL d K) g (e r) := by
  obtain ⟨K, hK, hfin, hcard, π, hπ⟩ := h
  refine ⟨K, hK, hfin, hcard, ?_⟩
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := hπ
  obtain ⟨β, hβs, hβk, hβe⟩ : ∃ β : ↥(⊤ : Subgroup V) →*
      (↥(⊤ : Subgroup (Multiplicative (Fin d → K))) ⧸
        (⊥ : Subgroup (Multiplicative (Fin d → K))).subgroupOf ⊤),
      Function.Surjective β ∧ (∀ u : ↥(⊤ : Subgroup V), β u = 1 ↔ (u : V) ∈ (⊥ : Subgroup V)) ∧
      ∀ (g : ↥(StatedSL d K)) (u : ↥(⊤ : Subgroup V))
        (m : ↥(⊤ : Subgroup (Multiplicative (Fin d → K)))),
        β u = QuotientGroup.mk m →
          β ⟨((π g : ↥L) : MulAut V) (u : V), Subgroup.mem_top _⟩ =
            QuotientGroup.mk ⟨natAct (StatedSL d K) g (m : Multiplicative (Fin d → K)),
              Subgroup.mem_top _⟩ :=
    ⟨β, hβs, hβk, fun g u m hm => hβe g u m (Subgroup.mem_top _) (Subgroup.mem_top _) hm⟩
  let q : (↥(⊤ : Subgroup (Multiplicative (Fin d → K))) ⧸
      (⊥ : Subgroup (Multiplicative (Fin d → K))).subgroupOf ⊤) →* Multiplicative (Fin d → K) :=
    QuotientGroup.lift _ (Subgroup.subtype _) (by
      intro x hx
      have hx' : (x : Multiplicative (Fin d → K)) ∈ (⊥ : Subgroup (Multiplicative (Fin d → K))) :=
        hx
      exact Subgroup.mem_bot.mp hx')
  have hq1 : ∀ x, q x = 1 → x = 1 := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H m =>
      intro hm
      have hm' : (m : Multiplicative (Fin d → K)) = 1 := hm
      have : m = 1 := Subtype.ext hm'
      rw [this]
      exact QuotientGroup.mk_one _
  let e₀ : V →* Multiplicative (Fin d → K) :=
    { toFun := fun r => q (β ⟨r, Subgroup.mem_top r⟩)
      map_one' := by
        have : (⟨1, Subgroup.mem_top 1⟩ : ↥(⊤ : Subgroup V)) = 1 := rfl
        rw [this, map_one, map_one]
      map_mul' := fun r s => by
        have : (⟨r * s, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup V)) =
            ⟨r, Subgroup.mem_top r⟩ * ⟨s, Subgroup.mem_top s⟩ := rfl
        rw [this, map_mul, map_mul] }
  have he₀ : ∀ r, e₀ r = q (β ⟨r, Subgroup.mem_top r⟩) := fun r => rfl
  have hinj : Function.Injective e₀ := by
    rw [injective_iff_map_eq_one]
    intro r hr
    have h1 : β ⟨r, Subgroup.mem_top r⟩ = 1 := hq1 _ hr
    have h2 := (hβk ⟨r, Subgroup.mem_top r⟩).mp h1
    exact Subgroup.mem_bot.mp h2
  have hsurj : Function.Surjective e₀ := by
    intro v
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨v, Subgroup.mem_top v⟩)
    refine ⟨(u : V), ?_⟩
    rw [he₀]
    have : (⟨(u : V), Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup V)) = u := rfl
    rw [this, hu]
    rfl
  refine ⟨MulEquiv.ofBijective e₀ ⟨hinj, hsurj⟩, fun g => ⟨(π g : MulAut V), (π g).2, fun r => ?_⟩⟩
  show e₀ ((π g : MulAut V) r) = natAct (StatedSL d K) g (e₀ r)
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨r, Subgroup.mem_top r⟩)
  have h1 := hβe g ⟨r, Subgroup.mem_top r⟩ m hm.symm
  rw [he₀, he₀, h1, ← hm]
  rfl

end CFSG.Quasithin
