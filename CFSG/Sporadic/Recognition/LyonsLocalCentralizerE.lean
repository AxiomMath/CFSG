module

public import CFSG.Sporadic.Recognition.LyonsLocalPerfect
public import CFSG.Sporadic.Recognition.LyonsLocalPreim
public import CFSG.Sporadic.Recognition.LyonsLocalA5

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup

@[expose] def QE {G : Type*} [Group G] (a b : G) : Subgroup G := centralizer ({a, b} : Set G)

theorem mem_QE {G : Type*} [Group G] {a b g : G} :
    g ∈ QE a b ↔ a * g = g * a ∧ b * g = g * b := by
  simp [QE, mem_centralizer_iff]

structure ThreeCoreE {G : Type*} [Group G] (a b : G) (R : Subgroup G) : Prop where
  le : R ≤ QE a b
  normal : ∀ g ∈ QE a b, ∀ r ∈ R, g * r * g⁻¹ ∈ R
  isPGroup : IsPGroup 3 R
  card : Nat.card ↥R = 729
  max : ∀ J : Subgroup G, J ≤ QE a b → (∀ g ∈ QE a b, ∀ j ∈ J, g * j * g⁻¹ ∈ J) →
    IsPGroup 3 J → J ≤ R
  left_mem : a ∈ R
  right_mem : b ∈ R

section Main

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

namespace LyData

theorem QE_eq_preimQ (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    QE (x₁ : G) (x₂ : G) = preimQ (x₁ : G) (centralizer ({D.x₂Q S} : Set (CentQuot (x₁ : G)))) := by
  ext g
  rw [mem_QE, mem_preimQ]
  constructor
  · rintro ⟨h1, h2⟩
    have hc : g ∈ centralizer ({(x₁ : G)} : Set G) := mem_centralizer_singleton_iff.2 h1.symm
    refine ⟨hc, ?_⟩
    rw [mem_centralizer_singleton_iff]
    change QuotientGroup.mk (⟨g, hc⟩ : ↥(centralizer ({(x₁ : G)} : Set G))) * D.x₂Q S =
      D.x₂Q S * QuotientGroup.mk (⟨g, hc⟩ : ↥(centralizer ({(x₁ : G)} : Set G)))
    rw [LyData.x₂Q, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    exact h2.symm
  · rintro ⟨hc, hK⟩
    have h := mem_centralizer_singleton_iff.1 hK
    have := D.commute_of_mk_commute S (m := ⟨g, hc⟩) h
    exact ⟨(mem_centralizer_singleton_iff.1 hc).symm, this.symm⟩

end LyData

end Main

@[expose] def SL5 {G : Type} [Group G] {t : G}
    (ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)) : Subgroup G :=
  (IsCover11.A5sub ρ).map (centralizer ({t} : Set G)).subtype

section SL5

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

namespace LyData

omit [Finite G] in
theorem card_SL5 (D : LyData G t ρ) : Nat.card ↥(SL5 ρ) = 120 := by
  rw [SL5, Subgroup.card_map_of_injective (centralizer ({t} : Set G)).subtype_injective]
  exact D.cover.card_A5sub

omit [Finite G] in
theorem SL5_le_QE (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    SL5 ρ ≤ QE (x₁ : G) (x₂ : G) := by
  rintro _ ⟨a, ha, rfl⟩
  rw [mem_QE]
  have ha' : ρ a ∈ A5p := ha
  have h1 : a * x₁ = x₁ * a :=
    D.cover.commute_of_rho_commute_pow_three S.pow₁ (by rw [S.rho₁]; exact A5p_comm_x1p ha')
  have h2 : a * x₂ = x₂ * a :=
    D.cover.commute_of_rho_commute_pow_three S.pow₂ (by rw [S.rho₂]; exact A5p_comm_x2p ha')
  have h1' := congrArg Subtype.val h1
  have h2' := congrArg Subtype.val h2
  exact ⟨h1'.symm, h2'.symm⟩

omit [Finite G] in
theorem SL5_eq_bot_of_odd (D : LyData G t ρ) {J : Subgroup G} (hJ : J ≤ SL5 ρ)
    (hn : ∀ g ∈ SL5 ρ, ∀ j ∈ J, g * j * g⁻¹ ∈ J) (hodd : Odd (Nat.card ↥J)) : J = ⊥ := by
  have hJH : J ≤ centralizer ({t} : Set G) := hJ.trans (map_subtype_le _)
  have hmap : (J.comap (centralizer ({t} : Set G)).subtype).map
      (centralizer ({t} : Set G)).subtype = J :=
    Subgroup.map_comap_eq_self (by rw [range_subtype]; exact hJH)
  have hle : J.comap (centralizer ({t} : Set G)).subtype ≤ IsCover11.A5sub ρ := by
    intro j hj
    obtain ⟨a, ha, haj⟩ := hJ hj
    have : a = j := Subtype.ext haj
    rw [← this]; exact ha
  have hnorm : ∀ g ∈ IsCover11.A5sub ρ, ∀ j ∈ J.comap (centralizer ({t} : Set G)).subtype,
      g * j * g⁻¹ ∈ J.comap (centralizer ({t} : Set G)).subtype := by
    intro g hg j hj
    have := hn (g : G) ⟨g, hg, rfl⟩ (j : G) hj
    exact this
  have hodd' : Odd (Nat.card ↥(J.comap (centralizer ({t} : Set G)).subtype)) := by
    rw [← Subgroup.card_map_of_injective (centralizer ({t} : Set G)).subtype_injective, hmap]
    exact hodd
  have hbot := D.cover.eq_bot_of_odd_normal hle hnorm hodd'
  rw [← hmap, hbot, Subgroup.map_bot]

theorem inf_SL5_eq_bot (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) {R : Subgroup G}
    (hR : ThreeCoreE (x₁ : G) (x₂ : G) R) : R ⊓ SL5 ρ = ⊥ := by
  have hSQ := D.SL5_le_QE S
  apply D.SL5_eq_bot_of_odd inf_le_right
  · intro g hg j hj
    refine ⟨hR.normal g (hSQ hg) j hj.1, ?_⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hj.2) (Subgroup.inv_mem _ hg)
  · have hp : IsPGroup 3 ↥(R ⊓ SL5 ρ) := hR.isPGroup.to_le inf_le_left
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hp
    rw [hk]
    exact Odd.pow (by decide)

end LyData

end SL5

section CertSmall

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

namespace LyData

theorem card_QE (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    Nat.card ↥(QE (x₁ : G) (x₂ : G)) = 87480 := by
  obtain ⟨e⟩ := D.centQuot_mcl S.pow₁ S.rho₁
  have hy3 := D.orderOf_x₂Q S
  have hc := card_centralizer_eq_of_five_dvd e hy3 (D.five_dvd_card_centralizer_x₂Q S)
  rw [D.QE_eq_preimQ S, card_preimQ, orderOf_x₁ S, hc]

theorem QE_eq_mul_SL5 (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) {R : Subgroup G}
    (hR : ThreeCoreE (x₁ : G) (x₂ : G) R) :
    ∀ q ∈ QE (x₁ : G) (x₂ : G), ∃ r ∈ R, ∃ s ∈ SL5 ρ, q = r * s := by
  have hSQ := D.SL5_le_QE S
  have hinter : R ⊓ SL5 ρ = ⊥ := D.inf_SL5_eq_bot S hR
  let f : ↥R × ↥(SL5 ρ) → ↥(QE (x₁ : G) (x₂ : G)) := fun p =>
    ⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem _ (hR.le p.1.2) (hSQ p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨r, hr⟩, ⟨s, hs⟩⟩ ⟨⟨r', hr'⟩, ⟨s', hs'⟩⟩ h
    have h1 : r * s = r' * s' := congrArg Subtype.val h
    have h2 : r'⁻¹ * r ∈ R ⊓ SL5 ρ := by
      refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hr') hr, ?_⟩
      have : r'⁻¹ * r = s' * s⁻¹ := by
        calc r'⁻¹ * r = r'⁻¹ * (r * s) * s⁻¹ := by group
          _ = r'⁻¹ * (r' * s') * s⁻¹ := by rw [h1]
          _ = s' * s⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ hs' (Subgroup.inv_mem _ hs)
    rw [hinter, Subgroup.mem_bot] at h2
    have hrr : r = r' := (inv_mul_eq_one.1 h2).symm
    subst hrr
    have hss : s = s' := mul_left_cancel h1
    subst hss
    rfl
  have hcard : Nat.card ↥(QE (x₁ : G) (x₂ : G)) ≤ Nat.card (↥R × ↥(SL5 ρ)) := by
    rw [Nat.card_prod, hR.card, D.card_SL5, D.card_QE S]
  have hbij := hf.bijective_of_nat_card_le hcard
  intro q hq
  obtain ⟨⟨r, s⟩, hrs⟩ := hbij.2 ⟨q, hq⟩
  exact ⟨r, r.2, s, s.2, (congrArg Subtype.val hrs).symm⟩

end LyData

end CertSmall

section CertFull

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

namespace LyData

theorem exists_threeCoreE (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    ∃ R : Subgroup G, ThreeCoreE (x₁ : G) (x₂ : G) R := by
  obtain ⟨e⟩ := D.centQuot_mcl S.pow₁ S.rho₁
  have hy3 := D.orderOf_x₂Q S
  have hc := card_centralizer_eq_of_five_dvd e hy3 (D.five_dvd_card_centralizer_x₂Q S)
  obtain ⟨Rs, hRs⟩ := exists_threeCore e hy3 hc
  have hQ := D.QE_eq_preimQ S
  have hcard : Nat.card ↥(preimQ (x₁ : G) Rs) = 729 := by
    rw [card_preimQ, orderOf_x₁ S, hRs.card]
  refine ⟨preimQ (x₁ : G) Rs, ?_, ?_, ?_, hcard, ?_, x_mem_preimQ _, ?_⟩
  · rw [hQ]; exact preimQ_mono hRs.le_cent
  · intro g hg r hr
    rw [hQ] at hg
    obtain ⟨hgc, hgK⟩ := mem_preimQ.1 hg
    obtain ⟨hrc, hrK⟩ := mem_preimQ.1 hr
    have hmc : g * r * g⁻¹ ∈ centralizer ({(x₁ : G)} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hgc hrc) (Subgroup.inv_mem _ hgc)
    refine mem_preimQ.2 ⟨hmc, ?_⟩
    have : (⟨g * r * g⁻¹, hmc⟩ : ↥(centralizer ({(x₁ : G)} : Set G))) =
        ⟨g, hgc⟩ * ⟨r, hrc⟩ * ⟨g, hgc⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]
    exact hRs.normal _ hgK _ hrK
  · exact IsPGroup.of_card (n := 6) (by rw [hcard]; norm_num)
  · intro J hJQ hJn hJ3
    rw [hQ] at hJQ hJn
    have hJc : J ≤ centralizer ({(x₁ : G)} : Set G) := hJQ.trans (preimQ_le_centralizer _)
    rw [le_preimQ_iff hJc]
    refine hRs.max _ ?_ (imQ_normalized hJn) (imQ_isPGroup hJc hJ3)
    rw [← le_preimQ_iff hJc]
    exact hJQ
  · refine mem_preimQ.2 ⟨mem_centralizer_singleton_iff.2 (D.comm₂₁ S), ?_⟩
    have hy : D.x₂Q S ∈ Rs := by
      have h1 : D.x₂Q S ∈ zpowers (D.x₂Q S) := mem_zpowers _
      rw [← hRs.comm] at h1
      exact commutator_le_of_le (le_refl Rs) (le_refl Rs) h1
    exact hy

end LyData

end CertFull

end CFSG.Sporadic.Recognition.LyonsSims
