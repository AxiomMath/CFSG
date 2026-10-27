module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.L74.Center
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.RegFam.Sylow

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace L74

variable {G : Type*} [Group G] [Finite G]

theorem dvd_card_of_isRegFam {A H N : Subgroup G} {Ω : Set (Subgroup G)}
    (hΩ : IsRegFam A H Ω N) {r : ℕ} (hr : r.Prime) (hdvd : r ∣ Nat.card H) {L : Subgroup G}
    (hL : L ∈ Ω) : r ∣ Nat.card L := by
  have hm : ∀ L' ∈ Ω, Nat.card L' = Nat.card L := by
    intro L' hL'
    obtain ⟨x, -, rfl⟩ := hΩ.transitive L hL L' hL'
    exact Subgroup.card_map_of_injective (MulAut.conj x).injective
  rw [hΩ.card_eq_pow hm] at hdvd
  exact hr.dvd_of_dvd_pow hdvd

theorem inf_ne_bot_of_isRegFam {A H N P : Subgroup G} {Ω : Set (Subgroup G)}
    (hΩ : IsRegFam A H Ω N) {r : ℕ} (hr : r.Prime) (hPH : P ≤ H) (hP : IsPGroup r P)
    (hidx : Nat.Coprime (P.relIndex H) r) (hdvd : r ∣ Nat.card H) {L : Subgroup G}
    (hL : L ∈ Ω) : P ⊓ L ≠ ⊥ := by
  intro hbot
  have hcop := (IsDirectProduct.sylow_decomp hΩ.isDirectProduct hr hPH hP hidx).2 L hL
  rw [hbot, Subgroup.relIndex_bot_left] at hcop
  exact hr.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop.symm (dvd_card_of_isRegFam hΩ hr hdvd hL))

theorem zOf_ne_bot_of_isPGroup {r : ℕ} (hr : r.Prime) {X : Subgroup G} (hX : IsPGroup r X)
    (hX1 : X ≠ ⊥) : zOf X ≠ ⊥ := by
  have : Fact r.Prime := ⟨hr⟩
  have : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot X).mpr hX1
  have := hX.center_nontrivial
  intro hbot
  have h1 : Subgroup.center X = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp hbot
  exact (Subgroup.nontrivial_iff_ne_bot _).mp this h1

theorem inf_ne_bot_and_isDirectProduct_zOf {A H N S : Subgroup G} {Ω : Set (Subgroup G)} {r : ℕ}
    {a : G} (hr : r.Prime) (hΩ : IsRegFam A H Ω N) (hHa : H ≤ Subgroup.centralizer {a})
    (hPH : S ⊓ Subgroup.centralizer {a} ≤ H) (hP : IsPGroup r ↥(S ⊓ Subgroup.centralizer {a}))
    (hidx : Nat.Coprime ((S ⊓ Subgroup.centralizer {a}).relIndex H) r)
    (hAP : A ≤ Subgroup.normalizer ((S ⊓ Subgroup.centralizer {a} : Subgroup G) : Set G))
    (hdvd : r ∣ Nat.card H)
    (hZ : zOf (S ⊓ Subgroup.centralizer {a}) = zOf S ⊓ Subgroup.centralizer {a}) :
    (∀ L ∈ Ω, zOf S ⊓ L ≠ ⊥) ∧
      IsDirectProduct {Y | ∃ L ∈ Ω, Y = zOf S ⊓ L} (zOf S ⊓ H) := by
  set P : Subgroup G := S ⊓ Subgroup.centralizer {a} with hPdef
  have hne : ∀ L ∈ Ω, P ⊓ L ≠ ⊥ := fun L hL => inf_ne_bot_of_isRegFam hΩ hr hPH hP hidx hdvd hL
  have hfam := hΩ.inf_family hr hPH hP hidx hAP hne
  have hdpP := hfam.isDirectProduct
  have hdpZ := isDirectProduct_zOf hdpP
  have hkey : ∀ L ∈ Ω, zOf S ⊓ L = zOf (P ⊓ L) := by
    intro L hL
    refine le_antisymm (fun z hz => ?_) (fun w hw => ?_)
    · obtain ⟨hzZ, hzL⟩ := Subgroup.mem_inf.mp hz
      have hzS : z ∈ S := zOf_le S hzZ
      have hzP : z ∈ P := Subgroup.mem_inf.mpr ⟨hzS, hHa (hΩ.isDirectProduct.le hL hzL)⟩
      exact mem_zOf_iff.mpr ⟨Subgroup.mem_inf.mpr ⟨hzP, hzL⟩, fun v hv =>
        (mem_zOf_iff.mp hzZ).2 v (Subgroup.mem_inf.mp hv).1.1⟩
    · have hwP : w ∈ zOf P :=
        zOf_le_zOf_of_mem hdpP (show P ⊓ L ∈ {Y | ∃ L ∈ Ω, Y = P ⊓ L} from ⟨L, hL, rfl⟩) hw
      rw [hZ] at hwP
      exact Subgroup.mem_inf.mpr ⟨hwP.1, (Subgroup.mem_inf.mp (zOf_le _ hw)).2⟩
  refine ⟨fun L hL => ?_, ?_⟩
  · rw [hkey L hL]
    exact zOf_ne_bot_of_isPGroup hr (hP.to_inf_left) (hne L hL)
  · have hH : zOf S ⊓ H = zOf P := by
      rw [hZ]
      refine le_antisymm (le_inf inf_le_left (fun x hx => hHa hx.2)) (fun x hx => ?_)
      exact Subgroup.mem_inf.mpr ⟨hx.1, hPH (Subgroup.mem_inf.mpr ⟨zOf_le S hx.1, hx.2⟩)⟩
    have hset : {Y | ∃ L ∈ Ω, Y = zOf S ⊓ L} =
        {Y | ∃ X ∈ {Y | ∃ L ∈ Ω, Y = P ⊓ L}, Y = zOf X} := by
      ext Y
      constructor
      · rintro ⟨L, hL, rfl⟩
        exact ⟨P ⊓ L, ⟨L, hL, rfl⟩, hkey L hL⟩
      · rintro ⟨_, ⟨L, hL, rfl⟩, rfl⟩
        exact ⟨L, hL, (hkey L hL).symm⟩
    rw [hset, hH]
    exact hdpZ

end L74

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
