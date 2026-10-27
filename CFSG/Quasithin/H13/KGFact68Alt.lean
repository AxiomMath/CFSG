module

public import CFSG.Quasithin.H13.KGFact68AltBase
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115AltSix
public import CFSG.Permutation.AlternatingAutomorphism.Conjugation
public import Certificates.Certificate7131
public import Certificates.Certificate7132

public section

namespace CFSG.Quasithin.H13.KG68

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv Equiv.Perm
open scoped Pointwise

theorem exists_eq_of_injective {α β : Type} [Finite α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) {s : Finset β} (hs : ∀ x, f x ∈ s) (hcard : s.card ≤ Nat.card α)
    {b : β} (hb : b ∈ s) : ∃ x, f x = b := by
  by_contra hne
  push Not at hne
  have h1 : Nat.card α ≤ (s.erase b).card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_le_card_of_injective (fun x => ⟨f x, Finset.mem_erase.mpr ⟨hne x, hs x⟩⟩)
      fun x y hxy => hf (congrArg Subtype.val hxy)
  have h2 := Finset.card_erase_lt_of_mem hb
  omega

section Core

variable {Y : Type} [Group Y] [Finite Y] {L A R : Subgroup Y} {z : Y} {G : Type} [Group G]

theorem not_e68Hyp_core (h : E6.E68Hyp L A R z) (φ : (↥L ⧸ Subgroup.center ↥L) ≃* G)
    (hZ : Odd (Nat.card (Subgroup.center ↥L))) {c d y : G} {pc pd : ↥L}
    (hpc : pc ∈ ((sylowIn h : Sylow 2 ↥L) : Subgroup ↥L))
    (hpd : pd ∈ ((sylowIn h : Sylow 2 ↥L) : Subgroup ↥L))
    (hc : φ (pc : ↥L ⧸ Subgroup.center ↥L) = c) (hd : φ (pd : ↥L ⧸ Subgroup.center ↥L) = d)
    {Tu Tv : MulAut G}
    (hAut : ∀ β : MulAut G, β c = c → β d = d → β = 1 ∨ β = Tu ∨ β = Tv ∨ β = Tu * Tv)
    (hy : y * y = 1) (hvy : Tv y = y) (huy : Tu y ≠ y) (hv : Tv ≠ 1) : False := by
  classical
  set Z := Subgroup.center ↥L with hZdef
  have hperf : commutator ↥L = ⊤ := Group.isPerfect_def.mp h.quasisimple.1
  let ind : MulAut ↥L → MulAut G := fun α => MulAut.congr φ (quotAut Z α)
  have hind_inj : Function.Injective ind := by
    intro α β hαβ
    have h1 : quotAut Z α = quotAut Z β := (MulAut.congr φ).injective hαβ
    have h2 : quotAut Z (α * β⁻¹) = 1 := by
      rw [quotAut_mul, h1, ← quotAut_mul, mul_inv_cancel, quotAut_one]
    exact mul_inv_eq_one.mp (eq_one_of_quotAut_eq_one le_rfl hperf h2)
  have hind_apply : ∀ (α : MulAut ↥L) (x : ↥L),
      ind α (φ (x : ↥L ⧸ Z)) = φ ((α x : ↥L) : ↥L ⧸ Z) := by
    intro α x
    show φ (quotAut Z α (φ.symm (φ (x : ↥L ⧸ Z)))) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hind_one : ind 1 = 1 := by
    show MulAut.congr φ (quotAut Z 1) = 1
    rw [quotAut_one, map_one]
  have hmem : ∀ a (ha : a ∈ A),
      ind (conjOn L a (leN h ha)) ∈ ({1, Tu, Tv, Tu * Tv} : Finset (MulAut G)) := by
    intro a ha
    have h1 : ind (conjOn L a (leN h ha)) c = c := by
      rw [← hc, hind_apply, conjOn_fix_of_hyp h ha hpc]
    have h2 : ind (conjOn L a (leN h ha)) d = d := by
      rw [← hd, hind_apply, conjOn_fix_of_hyp h ha hpd]
    rcases hAut _ h1 h2 with e | e | e | e <;> simp [e]
  have hcard : ({1, Tu, Tv, Tu * Tv} : Finset (MulAut G)).card ≤
      Nat.card (actHom L A (leN h)).range :=
    Finset.card_le_four.trans (h.four_le.trans (relIndex_eq_card_range L A (leN h)).le)
  let F : ↥(actHom L A (leN h)).range → MulAut G := fun α => ind α
  have hF : Function.Injective F := fun α β hαβ => Subtype.ext (hind_inj hαβ)
  have hFs : ∀ α, F α ∈ ({1, Tu, Tv, Tu * Tv} : Finset (MulAut G)) := by
    rintro ⟨α, a, rfl⟩
    exact hmem a a.2
  obtain ⟨⟨α₁, a₁, rfl⟩, he₁⟩ := exists_eq_of_injective hF hFs hcard (b := Tv) (by simp)
  obtain ⟨⟨α₂, a₂, rfl⟩, he₂⟩ := exists_eq_of_injective hF hFs hcard (b := Tu) (by simp)
  have he₁' : ind (conjOn L a₁ (leN h a₁.2)) = Tv := he₁
  have he₂' : ind (conjOn L a₂ (leN h a₂.2)) = Tu := he₂
  have hna₁ : (a₁ : Y) ∉ Subgroup.centralizer (L : Set Y) := by
    intro hc1
    apply hv
    rw [← he₁', (conjOn_eq_one_iff L (leN h a₁.2)).mpr hc1, hind_one]
  have hpowZ : ∀ ζ ∈ Z, ζ ^ Nat.card ↥Z = 1 := by
    intro ζ hζ
    have h1 : ((⟨ζ, hζ⟩ : ↥Z) ^ Nat.card ↥Z : ↥Z) = 1 := pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    rw [SubmonoidClass.coe_pow] at h2
    exact h2
  obtain ⟨k, hk⟩ := hZ
  have hodd1 : ∀ ζ ∈ Z, ζ * ζ = 1 → ζ = 1 := by
    intro ζ hζ hζ2
    have h1 := hpowZ ζ hζ
    rw [hk, pow_succ, pow_mul, sq, hζ2, one_pow, one_mul] at h1
    exact h1
  obtain ⟨q, hq⟩ := φ.surjective y
  obtain ⟨y₁, rfl⟩ := QuotientGroup.mk_surjective q
  have hy₁ : y₁ * y₁ ∈ Z := by
    rw [← QuotientGroup.eq_one_iff]
    apply φ.injective
    rw [QuotientGroup.mk_mul, map_mul, hq, hy, map_one]
  set y₀ := y₁ ^ Nat.card ↥Z with hy₀def
  have hy₀2 : y₀ * y₀ = 1 := by
    rw [hy₀def, ← (Commute.refl y₁).mul_pow]
    exact hpowZ _ hy₁
  have hy₀ : φ (y₀ : ↥L ⧸ Z) = y := by
    rw [hy₀def, QuotientGroup.mk_pow, map_pow, hq, hk, pow_succ, pow_mul, sq, hy, one_pow,
      one_mul]
  have hcomm₁ : (y₀ : Y) * a₁ = a₁ * y₀ := by
    set w := conjOn L a₁ (leN h a₁.2) y₀ with hw
    have hw1 : (w : ↥L ⧸ Z) = (y₀ : ↥L ⧸ Z) := by
      apply φ.injective
      rw [hw, ← hind_apply, he₁', hy₀, hvy]
    have hζ : y₀⁻¹ * w ∈ Z := QuotientGroup.eq.mp hw1.symm
    have hww : w * w = 1 := by rw [hw, ← map_mul, hy₀2, map_one]
    have hζ2 : (y₀⁻¹ * w) * (y₀⁻¹ * w) = 1 := by
      have hcent := Subgroup.mem_center_iff.mp hζ y₀
      calc (y₀⁻¹ * w) * (y₀⁻¹ * w) = y₀⁻¹ * (y₀ * (y₀⁻¹ * w)) * (y₀⁻¹ * w) := by group
        _ = y₀⁻¹ * ((y₀⁻¹ * w) * y₀) * (y₀⁻¹ * w) := by rw [hcent]
        _ = (y₀ * y₀)⁻¹ * (w * w) := by group
        _ = 1 := by rw [hww, hy₀2, inv_one, mul_one]
    have hwy : w = y₀ := (inv_mul_eq_one.mp (hodd1 _ hζ hζ2)).symm
    have h1 : (a₁ : Y) * y₀ * (a₁ : Y)⁻¹ = y₀ := by
      rw [← conjOn_coe L (a₁ : Y) (leN h a₁.2), ← hw, hwy]
    calc (y₀ : Y) * a₁ = ((a₁ : Y) * y₀ * (a₁ : Y)⁻¹) * a₁ := by rw [h1]
      _ = a₁ * y₀ := by group
  have hcA := h.centralizes a₁ a₁.2 hna₁ y₀ y₀.2 hcomm₁
    ⟨1, by simpa [sq] using congrArg Subtype.val hy₀2⟩
  have hc2 := Subgroup.mem_centralizer_iff.mp hcA a₂ a₂.2
  have h2 : conjOn L a₂ (leN h a₂.2) y₀ = y₀ := by
    apply Subtype.ext
    rw [conjOn_coe, hc2, mul_inv_cancel_right]
  apply huy
  rw [← he₂', ← hy₀, hind_apply, h2]

theorem not_e68Hyp_of_sylow [Finite G] (h : E6.E68Hyp L A R z)
    (φ : (↥L ⧸ Subgroup.center ↥L) ≃* G) (hZ : Odd (Nat.card (Subgroup.center ↥L)))
    (P₀ : Sylow 2 G) {c d y : G} (hc : c ∈ P₀) (hd : d ∈ P₀) {Tu Tv : MulAut G}
    (hAut : ∀ β : MulAut G, β c = c → β d = d → β = 1 ∨ β = Tu ∨ β = Tv ∨ β = Tu * Tv)
    (hy : y * y = 1) (hvy : Tv y = y) (huy : Tu y ≠ y) (hv : Tv ≠ 1) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : ↥L →* G := φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hf : Function.Surjective f := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G ((sylowIn h).mapSurjective hf) P₀
  have key : ∀ x ∈ P₀, ∃ p ∈ ((sylowIn h : Sylow 2 ↥L) : Subgroup ↥L), g * f p * g⁻¹ = x := by
    intro x hx
    have hx' : x ∈ MulAut.conj g • ((sylowIn h).mapSurjective hf : Subgroup G) := by
      rw [← Sylow.coe_subgroup_smul, hg]
      exact hx
    obtain ⟨s, hs, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hx'
    rw [Sylow.coe_mapSurjective, Subgroup.mem_map] at hs
    obtain ⟨p, hp, rfl⟩ := hs
    exact ⟨p, hp, rfl⟩
  obtain ⟨pc, hpc, hpc'⟩ := key c hc
  obtain ⟨pd, hpd, hpd'⟩ := key d hd
  exact not_e68Hyp_core h (φ.trans (MulAut.conj g)) hZ hpc hpd hpc' hpd' hAut hy hvy huy hv

end Core

private def alt6y : alternatingGroup (Fin 6) :=
  ⟨swap 0 1 * swap 4 5, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private def alt6t : alternatingGroup (Fin 6) :=
  ⟨swap 3 4 * swap 4 5, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private def alt7y : alternatingGroup (Fin 7) :=
  ⟨swap 0 1 * swap 4 5, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private def alt7t : alternatingGroup (Fin 7) :=
  ⟨swap 3 4 * swap 4 5, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

theorem alt6_aut_fix
    (β : MulAut (alternatingGroup (Fin 6)))
    (hc : β alt6c = alt6c) (hd : β alt6d = alt6d) :
    β = 1 ∨ β = MulAut.conjNormal (swap 0 2 * swap 1 3) ∨ β = MulAut.conjNormal (swap 4 5) ∨
      β = MulAut.conjNormal (swap 0 2 * swap 1 3) * MulAut.conjNormal (swap 4 5) := by
  obtain ⟨σ, b, rfl⟩ := Ch1.AltSix.autOf_surjective β
  have hc' := congrArg Subtype.val hc
  have hd' := congrArg Subtype.val hd
  rw [Ch1.AltSix.autOf_apply] at hc' hd'
  obtain ⟨rfl, hσ⟩ := Certificates.certificate7131 σ b hc' hd'
  have e : ∀ τ : Perm (Fin 6), Ch1.AltSix.autOf τ false = MulAut.conjNormal τ := fun _ => rfl
  rw [e]
  rcases hσ with rfl | rfl | rfl | rfl
  · exact Or.inl (map_one _)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (map_mul _ _ _)))

theorem alt7_aut_fix (β : MulAut (alternatingGroup (Fin 7)))
    (hc : β alt7c = alt7c) (hd : β alt7d = alt7d) :
    β = 1 ∨ β = MulAut.conjNormal (swap 0 2 * swap 1 3) ∨ β = MulAut.conjNormal (swap 4 5) ∨
      β = MulAut.conjNormal (swap 0 2 * swap 1 3) * MulAut.conjNormal (swap 4 5) := by
  obtain ⟨σ, hσ⟩ := CFSG.AlternatingAutomorphism.exists_perm_conj_of_degree_eq_five_or_seven_le
    (n := 7) (Or.inr le_rfl) β
  have hβ : β = MulAut.conjNormal σ :=
    MulEquiv.ext fun g => Subtype.ext (by rw [hσ g, MulAut.conjNormal_apply])
  have hcomm : ∀ x : alternatingGroup (Fin 7), β x = x → σ * (x : Perm (Fin 7)) = x * σ := by
    intro x hx
    have h1 := hσ x
    rw [hx] at h1
    calc σ * (x : Perm (Fin 7)) = (σ * x * σ⁻¹) * σ := by group
      _ = x * σ := by rw [← h1]
  rw [hβ]
  rcases Certificates.certificate7132 σ (hcomm _ hc) (hcomm _ hd) with rfl | rfl | rfl | rfl
  · exact Or.inl (map_one _)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (map_mul _ _ _)))

section Final

variable {Y : Type} [Group Y] [Finite Y] {L A R : Subgroup Y} {z : Y}

theorem not_e68Hyp_of_alt6
    (h : E6.E68Hyp L A R z)
    (φ : (↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin 6))
    (hZ : Odd (Nat.card (Subgroup.center ↥L))) : False := by
  have hc : alt6c ∈ alt6Sylow := by
    have := alt6c_mem
    rw [← alt6Sylow_coe] at this
    exact this
  have hd : alt6d ∈ alt6Sylow := by
    have := alt6d_mem
    rw [← alt6Sylow_coe] at this
    exact this
  refine not_e68Hyp_of_sylow h φ hZ alt6Sylow hc hd alt6_aut_fix (y := alt6y) ?_ ?_ ?_ ?_
  · exact Subtype.ext (by decide)
  · exact Subtype.ext (by rw [MulAut.conjNormal_apply]; decide)
  · intro e
    have e' := congrArg Subtype.val e
    rw [MulAut.conjNormal_apply] at e'
    revert e'
    decide
  · intro e
    have e' := congrArg (fun β : MulAut (alternatingGroup (Fin 6)) =>
      ((β alt6t : alternatingGroup (Fin 6)) : Perm (Fin 6))) e
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at e'
    revert e'
    decide

theorem not_e68Hyp_of_alt7 (h : E6.E68Hyp L A R z)
    (φ : (↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin 7))
    (hZ : Odd (Nat.card (Subgroup.center ↥L))) : False := by
  have hc : alt7c ∈ alt7Sylow := by
    have := alt7c_mem
    rw [← alt7Sylow_coe] at this
    exact this
  have hd : alt7d ∈ alt7Sylow := by
    have := alt7d_mem
    rw [← alt7Sylow_coe] at this
    exact this
  refine not_e68Hyp_of_sylow h φ hZ alt7Sylow hc hd alt7_aut_fix (y := alt7y) ?_ ?_ ?_ ?_
  · exact Subtype.ext (by decide)
  · exact Subtype.ext (by rw [MulAut.conjNormal_apply]; decide)
  · intro e
    have e' := congrArg Subtype.val e
    rw [MulAut.conjNormal_apply] at e'
    revert e'
    decide
  · intro e
    have e' := congrArg (fun β : MulAut (alternatingGroup (Fin 7)) =>
      ((β alt7t : alternatingGroup (Fin 7)) : Perm (Fin 7))) e
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at e'
    revert e'
    decide

end Final

theorem e68ComponentFactsAlt_holds :
    E6.E68ComponentFactsAlt := by
  intro Y _ _ L A R z hcase h
  exfalso
  have hodd : ∀ {n : ℕ}, n = 1 ∨ n = 3 → Odd n := by
    rintro n (rfl | rfl) <;> decide
  rcases hcase with ⟨φ, σ, hZ, -, -⟩ | ⟨φ, σ, hZ, -, -⟩
  · exact not_e68Hyp_of_alt6 h φ (hodd hZ)
  · exact not_e68Hyp_of_alt7 h φ (hodd hZ)

end CFSG.Quasithin.H13.KG68
