module

public import CFSG.Quasithin.Background.B5Sec
public import CFSG.Quasithin.Background.B5Statement

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped commutatorElement

namespace B5

section Transport

variable {V : Type} [CommGroup V] {W U : Subgroup V} {L : Subgroup (MulAut V)}
  (hUW : U ≤ W) (hLW : L ≤ stabSub W) (hLU : L ≤ stabSub U) (hfaith : L ⊓ centSec W U = ⊥)

include hUW hLW hLU hfaith

theorem realizes_of_autSec {D : FFModel}
    (h : D.Realizes (autSec L W U) (⊤ : Subgroup (Sec W U)) ⊥) : D.Realizes L W U := by
  obtain ⟨π', hπ'⟩ := h
  exact ⟨_, realizesVia_of_autSec hUW hLW hLU hfaith hπ'⟩

theorem binaryNaturalSL_of_autSec {d a : ℕ}
    (h : BinaryNaturalSL (autSec L W U) (⊤ : Subgroup (Sec W U)) ⊥ d a) : BinaryNaturalSL L W U d a := by
  obtain ⟨K, hK, hf, hc, hr⟩ := h
  exact ⟨K, hK, hf, hc, realizes_of_autSec hUW hLW hLU hfaith hr⟩

theorem binaryNaturalSp4_of_autSec {a : ℕ}
    (h : BinaryNaturalSp4 (autSec L W U) (⊤ : Subgroup (Sec W U)) ⊥ a) : BinaryNaturalSp4 L W U a := by
  obtain ⟨K, hK, hf, hc, hr⟩ := h
  exact ⟨K, hK, hf, hc, realizes_of_autSec hUW hLW hLU hfaith hr⟩

theorem g2Natural_of_autSec {a : ℕ}
    (h : G2Natural (autSec L W U) (⊤ : Subgroup (Sec W U)) ⊥ a) : G2Natural L W U a := by
  obtain ⟨K, hK, hf, hc, hr⟩ := h
  exact ⟨K, hK, hf, hc, realizes_of_autSec hUW hLW hLU hfaith hr⟩

theorem g2NaturalDerived_of_autSec {a : ℕ}
    (h : G2NaturalDerived (autSec L W U) (⊤ : Subgroup (Sec W U)) ⊥ a) : G2NaturalDerived L W U a := by
  obtain ⟨K, hK, hf, hc, hr⟩ := h
  exact ⟨K, hK, hf, hc, realizes_of_autSec hUW hLW hLU hfaith hr⟩

theorem alternatingNatural_of_autSec {n : ℕ}
    (h : AlternatingNatural (autSec L W U) (⊤ : Subgroup (Sec W U)) ⊥ n) : AlternatingNatural L W U n :=
  realizes_of_autSec hUW hLW hLU hfaith h

theorem symmetricNatural_of_autSec {n : ℕ}
    (h : SymmetricNatural (autSec L W U) (⊤ : Subgroup (Sec W U)) ⊥ n) : SymmetricNatural L W U n :=
  realizes_of_autSec hUW hLW hLU hfaith h

theorem a7Four_of_autSec (h : A7Four (autSec L W U) (⊤ : Subgroup (Sec W U)) ⊥) : A7Four L W U := by
  obtain ⟨α, hr⟩ := h
  exact ⟨α, realizes_of_autSec hUW hLW hLU hfaith hr⟩

theorem tripleA6Six_of_autSec (h : TripleA6Six (autSec L W U) (⊤ : Subgroup (Sec W U)) ⊥) :
    TripleA6Six L W U := by
  obtain ⟨K, hK, hf, Γ₀, h1, h2, h3, h4, hr⟩ := h
  exact ⟨K, hK, hf, Γ₀, h1, h2, h3, h4, realizes_of_autSec hUW hLW hLU hfaith hr⟩

theorem slExteriorTwo_of_autSec {d : ℕ}
    (h : SLExteriorTwo (autSec L W U) (⊤ : Subgroup (Sec W U)) ⊥ d) : SLExteriorTwo L W U d :=
  realizes_of_autSec hUW hLW hLU hfaith h

theorem b42ModulePair_of_autSec
    (h : B42ModulePair (autSec L W U) (⊤ : Subgroup (Sec W U)) ⊥) : B42ModulePair L W U := by
  rcases h with ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl ⟨n, binaryNaturalSL_of_autSec hUW hLW hLU hfaith h⟩
  · exact Or.inr (Or.inl ⟨n, binaryNaturalSL_of_autSec hUW hLW hLU hfaith h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨n, binaryNaturalSp4_of_autSec hUW hLW hLU hfaith h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, g2Natural_of_autSec hUW hLW hLU hfaith h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (g2NaturalDerived_of_autSec hUW hLW hLU hfaith h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (alternatingNatural_of_autSec hUW hLW hLU hfaith h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (alternatingNatural_of_autSec hUW hLW hLU hfaith h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (alternatingNatural_of_autSec hUW hLW hLU hfaith h))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (a7Four_of_autSec hUW hLW hLU hfaith h)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (tripleA6Six_of_autSec hUW hLW hLU hfaith h))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (binaryNaturalSL_of_autSec hUW hLW hLU hfaith h)))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (binaryNaturalSL_of_autSec hUW hLW hLU hfaith h))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (slExteriorTwo_of_autSec hUW hLW hLU hfaith h)))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (slExteriorTwo_of_autSec hUW hLW hLU hfaith h)))))))))))))

end Transport

section Derived

variable {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)} {U Z : Subgroup V}

theorem commutator_le_self {Ω : Type*} [Group Ω] (H : Subgroup Ω) : ⁅H, H⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

theorem alternatingNatural_derived {n : ℕ} (hn : 5 ≤ n) (h : SymmetricNatural H U Z n) :
    AlternatingNatural ⁅H, H⁆ U Z n := by
  obtain ⟨π, hπ⟩ := h
  set ψ : Equiv.Perm (Fin n) →* MulAut V := H.subtype.comp π with hψ
  have hA : alternatingGroup (Fin n) = commutator (Equiv.Perm (Fin n)) :=
    (alternatingGroup.commutator_perm_eq (by simpa using hn)).symm
  have hrange : ψ.range = H := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact (π g).2
    · intro hx
      obtain ⟨g, hg⟩ := hπ.1 ⟨x, hx⟩
      exact ⟨g, congrArg Subtype.val hg⟩
  have hmap : (alternatingGroup (Fin n)).map ψ = ⁅H, H⁆ := by
    rw [hA, commutator, Subgroup.map_commutator, ← MonoidHom.range_eq_map, hrange]
  let π' : ↥(alternatingGroup (Fin n)) →* ↥⁅H, H⁆ :=
    (ψ.comp (alternatingGroup (Fin n)).subtype).codRestrict ⁅H, H⁆
      (fun x => hmap ▸ Subgroup.mem_map_of_mem ψ x.2)
  obtain ⟨-, hZU, hkerle, hUinv, hZinv, hsec, hkerinv, β, hβs, hβk, hβe⟩ := hπ
  refine ⟨π', ?_, hZU, hkerle, ?_, ?_, ?_, ?_, β, hβs, hβk, ?_⟩
  · intro y
    have hy : (y : MulAut V) ∈ (alternatingGroup (Fin n)).map ψ := by rw [hmap]; exact y.2
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  · intro g u hu
    exact hUinv ⟨(g : MulAut V), commutator_le_self H g.2⟩ u hu
  · intro g z hz
    exact hZinv ⟨(g : MulAut V), commutator_le_self H g.2⟩ z hz
  · intro (γ : ↥(alternatingGroup (Fin n))) m hm
    exact hsec (γ : Equiv.Perm (Fin n)) m hm
  · intro (γ : ↥(alternatingGroup (Fin n))) m hm
    exact hkerinv (γ : Equiv.Perm (Fin n)) m hm
  · intro (γ : ↥(alternatingGroup (Fin n))) u m hu hm hum
    exact hβe (γ : Equiv.Perm (Fin n)) u m hu hm hum


theorem g2NaturalDerived_of_g2Natural {a : ℕ} (h : G2Natural H U Z a) :
    G2NaturalDerived ⁅H, H⁆ U Z a := by
  obtain ⟨K, hK, hf, hc, π0, hπ⟩ := h
  refine ⟨K, hK, hf, hc, ?_⟩
  let Γ : Subgroup (quasithinZorn K ≃ₗ[K] quasithinZorn K) := quasithinG2 K
  let ψ : ↥Γ →* MulAut V := H.subtype.comp π0
  have hrange : ψ.range = H := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact (π0 g).2
    · intro hx
      obtain ⟨g, hg⟩ := hπ.1 ⟨x, hx⟩
      exact ⟨g, congrArg Subtype.val hg⟩
  have hmap : (commutator ↥Γ).map ψ = ⁅H, H⁆ := by
    rw [commutator, Subgroup.map_commutator, ← MonoidHom.range_eq_map, hrange]
  have hle : ⁅Γ, Γ⁆ ≤ Γ := commutator_le_self Γ
  let incl : ↥⁅Γ, Γ⁆ →* ↥Γ := Subgroup.inclusion hle
  have hincl : ∀ x : ↥⁅Γ, Γ⁆, incl x ∈ commutator ↥Γ := by
    intro x
    have hx : ((x : ↥⁅Γ, Γ⁆) : quasithinZorn K ≃ₗ[K] quasithinZorn K) ∈
        (commutator ↥Γ).map Γ.subtype := by
      rw [Subgroup.map_subtype_commutator]; exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    have : incl x = y := Subtype.ext hyx.symm
    rw [this]; exact hy
  let π' : ↥⁅Γ, Γ⁆ →* ↥⁅H, H⁆ :=
    (ψ.comp incl).codRestrict ⁅H, H⁆ (fun x => hmap ▸ Subgroup.mem_map_of_mem ψ (hincl x))
  obtain ⟨-, hZU, hkerle, hUinv, hZinv, hsec, hkerinv, β, hβs, hβk, hβe⟩ := hπ
  refine ⟨π', ?_, hZU, hkerle, ?_, ?_, ?_, ?_, β, hβs, hβk, ?_⟩
  · intro y
    have hy : (y : MulAut V) ∈ (commutator ↥Γ).map ψ := by rw [hmap]; exact y.2
    obtain ⟨c, hc, hcy⟩ := hy
    have hcmem : ((c : ↥Γ) : quasithinZorn K ≃ₗ[K] quasithinZorn K) ∈ ⁅Γ, Γ⁆ := by
      rw [← Subgroup.map_subtype_commutator]; exact ⟨c, hc, rfl⟩
    exact ⟨⟨c, hcmem⟩, Subtype.ext hcy⟩
  · intro g u hu
    exact hUinv ⟨(g : MulAut V), commutator_le_self H g.2⟩ u hu
  · intro g z hz
    exact hZinv ⟨(g : MulAut V), commutator_le_self H g.2⟩ z hz
  · intro γ m hm
    exact hsec (incl γ) m hm
  · intro γ m hm
    exact hkerinv (incl γ) m hm
  · intro γ u m hu hm hum
    exact hβe (incl γ) u m hu hm hum

end Derived

end B5

end CFSG.Quasithin
