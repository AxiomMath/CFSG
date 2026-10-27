module

public import CFSG.Quasithin.Background.FFC7D

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.B5
open scoped commutatorElement

@[expose] def B510SumNat : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (H K : Subgroup (MulAut W)), K ≤ H →
    (∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) →
    (∃ (m : ℕ) (K' : Type) (_ : Field K') (_ : Finite K'), Odd m ∧ Nat.card K' = 2 ^ m ∧
      DirectSumOfCopies K ⊤ ⊥ (FFModel.nat (Assembly.LowTwoRank.StatedSL 3 K')) 2) →
    ∀ A : Subgroup (MulAut W), IsFFStarOffender H A → A ≤ K

namespace B510

section SumNat

variable {V : Type} [CommGroup V]

theorem realizesVia_comap' {L : Subgroup (MulAut V)} {W : Subgroup V} (hst : L ≤ stabSub W)
    (hf : ∀ g ∈ L, (∀ v ∈ W, g v = v) → g = 1) {D : FFModel} {U Z : Subgroup V}
    {π : D.Gam →* ↥L} (hUW : U ≤ W) (h : D.RealizesVia L U Z π) :
    D.RealizesVia (autSub L W) (U.comap W.subtype) (Z.comap W.subtype)
      ((resEquiv hst hf).toMonoidHom.comp π) := by
  obtain ⟨hsurj, hZU, hkersec, hHU, hHZ, hsec, hker, β, hβs, hβk, hβe⟩ := h
  let iso : ↥(U.comap W.subtype) ≃* ↥U := Subgroup.subgroupOfEquivOfLe hUW
  have hiso : ∀ u : ↥(U.comap W.subtype), ((iso u : ↥U) : V) = ((u : ↥W) : V) := fun u => rfl
  refine ⟨(resEquiv hst hf).surjective.comp hsurj, Subgroup.comap_mono hZU, hkersec, ?_, ?_, hsec,
    hker, β.comp iso.toMonoidHom, hβs.comp iso.surjective, ?_, ?_⟩
  · intro h' u hu
    obtain ⟨g, rfl⟩ := (resEquiv hst hf).surjective h'
    exact hHU g (u : ↥W) hu
  · intro h' z hz
    obtain ⟨g, rfl⟩ := (resEquiv hst hf).surjective h'
    exact hHZ g (z : ↥W) hz
  · intro u
    show β (iso u) = 1 ↔ _
    rw [hβk]
    exact Iff.rfl
  · intro γ u m hu hm hbu
    have hu' : ((π γ : ↥L) : MulAut V) (((iso u : ↥U) : V)) ∈ U := hu
    exact hβe γ (iso u) m hu' hm hbu

theorem directSum_comap {L : Subgroup (MulAut V)} {W : Subgroup V} (hst : L ≤ stabSub W)
    (hf : ∀ g ∈ L, (∀ v ∈ W, g v = v) → g = 1) {D : FFModel} {k : ℕ}
    (hd : DirectSumOfCopies L W ⊥ D k) :
    DirectSumOfCopies (autSub L W) (⊤ : Subgroup ↥W) ⊥ D k := by
  obtain ⟨I, π, hZ, hind, hsup, hreal⟩ := hd
  have hι := W.subtype_injective
  have hIW : ∀ i, I i ≤ W := fun i => by
    rw [← hsup]
    exact (le_iSup I i).trans le_sup_right
  have hmapI : ∀ i, ((I i).comap W.subtype).map W.subtype = I i := fun i => by
    rw [Subgroup.map_comap_eq, Subgroup.range_subtype]
    exact inf_eq_right.2 (hIW i)
  have hbot : (⊥ : Subgroup V).comap W.subtype = ⊥ := by
    rw [MonoidHom.comap_bot, Subgroup.ker_subtype]
  refine ⟨fun i => (I i).comap W.subtype, (resEquiv hst hf).toMonoidHom.comp π, fun i => bot_le,
    fun i => ?_, ?_, fun i => ?_⟩
  · apply Subgroup.map_injective hι
    have h1 : ((⊥ : Subgroup ↥W) ⊔ ⨆ (j : Fin k) (_ : j ≠ i), (I j).comap W.subtype).map W.subtype =
        ⊥ ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j := by
      rw [Subgroup.map_sup, Subgroup.map_bot, Subgroup.map_iSup]
      congr 1
      refine iSup_congr fun j => ?_
      rw [Subgroup.map_iSup]
      refine iSup_congr fun _ => ?_
      exact hmapI j
    rw [Subgroup.map_inf _ _ W.subtype hι, hmapI i, h1, hind i, Subgroup.map_bot]
  · apply Subgroup.map_injective hι
    have h1 : ((⊥ : Subgroup ↥W) ⊔ ⨆ i, (I i).comap W.subtype).map W.subtype = ⊥ ⊔ ⨆ i, I i := by
      rw [Subgroup.map_sup, Subgroup.map_bot, Subgroup.map_iSup]
      congr 1
      exact iSup_congr fun j => hmapI j
    rw [h1, hsup, Subgroup.map_top, Subgroup.range_subtype]
  · have := realizesVia_comap' hst hf (hIW i) (hreal i)
    rwa [hbot] at this

end SumNat

section Offenders

variable {V : Type} [CommGroup V] [Finite V]

theorem offenders_of_sumNat (hP4 : AsB15Part4) (hSum : B510SumNat) {G L : Subgroup (MulAut V)}
    (hc : B56Counterex G) (hL : CFSG.Open.IsComponentOf L G)
    (h3 : ∃ (m : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Odd m ∧ Nat.card K = 2 ^ m ∧
      DirectSumOfCopies L (commV L) ⊥ (FFModel.nat (Assembly.LowTwoRank.StatedSL 3 K)) 2) :
    B510Offenders G L := by
  intro D hD d hd
  have hV := hc.hV
  have hJ : G = ffJ G := hc.hyp.2.1
  have hnG : G ≤ Subgroup.normalizer (L : Set (MulAut V)) := B55.normalizes_comp hP4 hV hJ hL
  have hn : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L := fun g hg l hl =>
    B19Aux.conj_mem_of_le_normalizer hnG hg hl
  have hGst : G ≤ stabSub (commV L) := le_stabSub_commV hn
  have hLU : L ≤ stabSub (commV L) := hL.1.trans hGst
  obtain ⟨m, K', hK', hfin, hodd, hcard, hds⟩ := h3
  have hfaith : ∀ g ∈ L, (∀ w ∈ commV L, g w = w) → g = 1 := by
    obtain ⟨I, π, hZ, hind, hsup, hreal⟩ := hds
    have hI0 : I 0 ≤ commV L := by
      rw [← hsup]
      exact (le_iSup I 0).trans le_sup_right
    intro g hg hgW
    exact faithful_of_binaryNatural (U := I 0) (Z := ⊥) (d := 3) (n := m)
      ⟨K', hK', hfin, hcard, π, hreal 0⟩ g hg (fun u hu => hgW u (hI0 hu))
  by_cases hDW : D ≤ centSub (commV L)
  · exact ⟨1, L.one_mem, fun w hw => by simpa using hDW hd w hw⟩
  · have hDinv : ∀ a ∈ D, ∀ w ∈ commV L, a w ∈ commV L := fun a ha w hw =>
      (hGst (hD.1 ha) w).2 hw
    have hoff : IsFFStarOffender (autSub G (commV L)) (autSub D (commV L)) :=
      B1Red.isFFStarOffender_autSub hD hDinv hDW
    have hKH : autSub L (commV L) ≤ autSub G (commV L) := autSub_mono hL.1 _
    have hnorm : ∀ h ∈ autSub G (commV L), ∀ k ∈ autSub L (commV L),
        h * k * h⁻¹ ∈ autSub L (commV L) := fun h hh k hk => autSub_conj_mem hn hh hk
    have hdsM : ∃ (m : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Odd m ∧ Nat.card K = 2 ^ m ∧
        DirectSumOfCopies (autSub L (commV L)) ⊤ ⊥
          (FFModel.nat (Assembly.LowTwoRank.StatedSL 3 K)) 2 :=
      ⟨m, K', hK', hfin, hodd, hcard, directSum_comap hLU hfaith hds⟩
    have hle := hSum ↥(commV L) (autSub G (commV L)) (autSub L (commV L)) hKH hnorm hdsM _ hoff
    have hdst : d ∈ stabSub (commV L) := hGst (hD.1 hd)
    have hmem : resHom (commV L) ⟨d, hdst⟩ ∈ autSub D (commV L) :=
      mem_autSub.2 ⟨⟨d, hdst⟩, hd, rfl⟩
    obtain ⟨g', hg'L, hg'r⟩ := mem_autSub.1 (hle hmem)
    refine ⟨(g' : MulAut V), hg'L, fun w hw => ?_⟩
    have := congrArg (fun φ : MulAut ↥(commV L) => ((φ ⟨w, hw⟩ : ↥(commV L)) : V)) hg'r
    exact this.symm

end Offenders

end B510

end FFC

end CFSG.Quasithin
