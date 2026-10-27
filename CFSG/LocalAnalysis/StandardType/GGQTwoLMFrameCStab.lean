module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrameCBase
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrameCCard
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrameCSplit
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrameCNorm
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrameCAut

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord

variable {G : Type} [Group G] [Finite G] {B Bs L : Subgroup G} {x : G} {m : ℕ}
  {V VT : Type} [Group V] [Group VT]

theorem qTwoLMFrameC_stab_form (F : QTwoFrame m V VT Bs L x) (hG : GGThmIHyp 3 B x L)
    (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1) (h3 : ¬ 3 ∣ m)
    (hVT : IsAugModel m VT F.permVT) :
    ∀ a : MulAut ↥Bs, a ∈ ggInduced ⊤ Bs → a ⟨x, F.hx⟩ = ⟨x, F.hx⟩ →
      ∃ (π : Equiv.Perm (Fin m)) (ε : Bool), ∀ v : VT,
        ((a ⟨((F.thetaT v : ↥(Bs ⊓ L)) : G), (F.thetaT v).2.1⟩ : ↥Bs) : G) =
          ((F.thetaT (if ε then (F.permVT π v)⁻¹ else F.permVT π v) : ↥(Bs ⊓ L)) : G) := by
  intro a ha hax
  simp only [ggInduced] at ha
  obtain ⟨g, -, hgBs, hga⟩ := ha
  have hm4 : 4 ≤ m := qTwoLMFrameC_four_le hL
  have hgx_eq : g * x * g⁻¹ = x := by
    have h := hga ⟨x, F.hx⟩
    have hxval : ((a ⟨x, F.hx⟩ : ↥Bs) : G) = x := by
      simpa using congrArg Subtype.val hax
    rw [hxval] at h
    simpa using h.symm
  have hgx : g ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    rwa [mul_inv_eq_iff_eq_mul] at hgx_eq
  have hgL : g ∈ Subgroup.normalizer (L : Set G) :=
    qTwoLMFrameC_normalizer_of_centralizer F hG (by omega) hVT g hgx
  obtain ⟨π, hcase⟩ := qTwoLMFrameC_aut_form hm4 h3 hVT
    (qTwoLMFrameC_actVT_normalizes F hgBs hgL)
  rcases hcase with hcase | hcase
  · refine ⟨π, false, fun v => ?_⟩
    have hspec := qTwoLMFrameC_actVT_spec F hgBs hgL v
    rw [hcase v] at hspec
    rw [hga ⟨((F.thetaT v : ↥(Bs ⊓ L)) : G), (F.thetaT v).2.1⟩, ← hspec]
    simp
  · refine ⟨π, true, fun v => ?_⟩
    have hspec := qTwoLMFrameC_actVT_spec F hgBs hgL v
    rw [hcase v] at hspec
    rw [hga ⟨((F.thetaT v : ↥(Bs ⊓ L)) : G), (F.thetaT v).2.1⟩, ← hspec]
    simp

theorem qTwoLMFrameC_stab_card_of_form (F : QTwoFrame m V VT Bs L x) (hxL : x ∉ L)
    (hV : IsAugModel m V F.permV) (hVT : IsAugModel m VT F.permVT)
    (hform : ∀ a : MulAut ↥Bs, a ∈ ggInduced ⊤ Bs → a ⟨x, F.hx⟩ = ⟨x, F.hx⟩ →
      ∃ (π : Equiv.Perm (Fin m)) (ε : Bool), ∀ v : VT,
        ((a ⟨((F.thetaT v : ↥(Bs ⊓ L)) : G), (F.thetaT v).2.1⟩ : ↥Bs) : G) =
          ((F.thetaT (if ε then (F.permVT π v)⁻¹ else F.permVT π v) : ↥(Bs ⊓ L)) : G)) :
    Nat.card {a : MulAut ↥Bs // a ∈ ggInduced ⊤ Bs ∧ a ⟨x, F.hx⟩ = ⟨x, F.hx⟩} ≤
      2 * m.factorial := by
  let Stab : Type := {a : MulAut ↥Bs // a ∈ ggInduced ⊤ Bs ∧ a ⟨x, F.hx⟩ = ⟨x, F.hx⟩}
  change Nat.card Stab ≤ 2 * m.factorial
  have hform' : ∀ a : Stab, ∃ (π : Equiv.Perm (Fin m)) (ε : Bool), ∀ v : VT,
      ((a.1 ⟨((F.thetaT v : ↥(Bs ⊓ L)) : G), (F.thetaT v).2.1⟩ : ↥Bs) : G) =
        ((F.thetaT (if ε then (F.permVT π v)⁻¹ else F.permVT π v) : ↥(Bs ⊓ L)) : G) :=
    fun a => hform a.1 a.2.1 a.2.2
  choose π ε hπε using hform'
  have hinj : Function.Injective (fun a : Stab => (π a, ε a)) := by
    rintro ⟨a, ha1, ha2⟩ ⟨a', ha1', ha2'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hπ, hε⟩ := h
    have hT : ∀ (t : G) (ht : t ∈ Bs ⊓ L), a ⟨t, ht.1⟩ = a' ⟨t, ht.1⟩ := by
      intro t ht
      obtain ⟨v, hv⟩ := F.thetaT.surjective ⟨t, ht⟩
      have hv' : t = ((F.thetaT v : ↥(Bs ⊓ L)) : G) := (congrArg Subtype.val hv).symm
      have hinput : (⟨t, ht.1⟩ : ↥Bs) =
          ⟨((F.thetaT v : ↥(Bs ⊓ L)) : G), (F.thetaT v).2.1⟩ := Subtype.ext hv'
      rw [hinput]
      apply Subtype.ext
      rw [hπε ⟨a, ha1, ha2⟩ v, hπε ⟨a', ha1', ha2'⟩ v, hπ, hε]
    have hx' : a ⟨x, F.hx⟩ = a' ⟨x, F.hx⟩ := by rw [ha2, ha2']
    refine Subtype.ext ?_
    ext b
    obtain ⟨t, ht, k, hbk⟩ := qTwoLMFrameC_split F hxL hV hVT (b : G) b.2
    have hb : b = ⟨t, ht.1⟩ * ⟨x, F.hx⟩ ^ k := by
      apply Subtype.ext
      simpa using hbk
    simp only [hb, map_mul, map_pow, hT t ht, hx']
  calc
    Nat.card Stab ≤ Nat.card (Equiv.Perm (Fin m) × Bool) :=
      Nat.card_le_card_of_injective (fun a : Stab => (π a, ε a)) hinj
    _ = m.factorial * 2 := by
      rw [Nat.card_prod, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin,
        Nat.card_eq_fintype_card, Fintype.card_bool]
    _ = 2 * m.factorial := mul_comm _ _

end CFSG.StandardType.QTwo

end
