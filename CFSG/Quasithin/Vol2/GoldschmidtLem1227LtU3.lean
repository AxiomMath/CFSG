module

public import CFSG.Quasithin.Vol2.GoldschmidtLem1227LtVac
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverCertU33
public import CFSG.Quasithin.Vol2.GoldschmidtLem1227Eq

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13.Lem1227Eq
open CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
open CFSG.QuasithinUnique.Bridge.Over.CertU33 CFSG.QuasithinUnique.Unc25K1.Six
open Equiv

namespace Lem1227Lt

namespace U3

abbrev A33 : Subgroup (Perm (Fin 28)) := CFSG.GH74.KGroups.U33.QP.originalSubgroup

theorem solvable_of_overgroup
    (Y : Subgroup ↥A33) (hDY : D.subgroupOf A33 ≤ Y) (hY : Y ≠ ⊤) :
    Group.IsSolvable ↥Y := by
  have hc := cert_check
  have hcl := cert.closedOK_of_check hc
  have hsz := cert.sizesOK_of_check hc
  let Y' : Subgroup (Perm (Fin 28)) := Y.map A33.subtype
  have hTY' : Subgroup.closure {g | g ∈ cert.tGens} ≤ Y' := by
    intro t ht
    have ht' : t ∈ D := ht
    let x : ↥A33 := ⟨t, D_le ht'⟩
    have hx : x ∈ D.subgroupOf A33 := Subgroup.mem_subgroupOf.2 ht'
    exact ⟨x, hDY hx, rfl⟩
  have hY'A : Y' ≤ A33 := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hY'M : Y' ≤ Subgroup.closure {g | g ∈ cert.mGens} := closure_mGens ▸ hY'A
  obtain ⟨L, hL, hYL⟩ := cert.overgroups (rawIsEnc 28) hc Y' hTY' hY'M
  have hLcard : Nat.card (Subgroup.closure {g | g ∈ L}) ∈ cert.sizes :=
    cert.card_member (rawIsEnc 28) hcl hsz L hL
  have hYcard : Nat.card Y = Nat.card (Subgroup.closure {g | g ∈ L}) := by
    rw [← hYL]
    exact (Subgroup.card_map_of_injective A33.subtype_injective).symm
  have hAcard : Nat.card A33 = 6048 := by
    have := cert.card_m (rawIsEnc 28) hcl hsz
    have h2 : Subgroup.closure {g | g ∈ cert.mGens} = A33 := closure_mGens
    rw [h2] at this
    exact this
  have hne : Nat.card Y ≠ 6048 := fun h' =>
    hY (Subgroup.eq_top_of_card_eq Y (h'.trans hAcard.symm))
  have hmem : Nat.card (Subgroup.closure {g | g ∈ L}) = 32 ∨
      Nat.card (Subgroup.closure {g | g ∈ L}) = 96 ∨
      Nat.card (Subgroup.closure {g | g ∈ L}) = 6048 := by
    have : Nat.card (Subgroup.closure {g | g ∈ L}) ∈ ([32, 96, 96, 6048] : List ℕ) := hLcard
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    omega
  rw [← hYcard] at hmem
  rcases hmem with h32 | h96 | h6048
  · exact isSolvable_of_card_pq Nat.prime_two Nat.prime_three (by norm_num) (a := 5) (b := 0)
      (by rw [h32]; norm_num)
  · exact isSolvable_of_card_pq Nat.prime_two Nat.prime_three (by norm_num) (a := 5) (b := 1)
      (by rw [h96]; norm_num)
  · exact absurd h6048 hne

theorem solvOver
    {X : Type} [Group X]
    (hX : LieModel X .PSU 3 3 1) (S M : Subgroup X) (hS : IsSylowTwoOf S ⊤) (hSM : S ≤ M)
    (hM : M ≠ ⊤) : Group.IsSolvable ↥M := by
  obtain ⟨e⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel hX
  have hS' : IsSylowTwoOf (S.map e.toMonoidHom) ⊤ := isSylowTwoOf_top_map e hS
  obtain ⟨ρ, hρ⟩ := exists_mulEquiv_map_eq_of_sylow (MulEquiv.refl _) hS' isSylow_D
  let ε : X ≃* ↥A33 := e.trans ρ
  have hSD : S.map ε.toMonoidHom = D.subgroupOf A33 := by
    rw [← hρ, Subgroup.map_map]
    rfl
  have h1 : D.subgroupOf A33 ≤ M.map ε.toMonoidHom :=
    hSD ▸ Subgroup.map_mono hSM
  have h2 : M.map ε.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hM
    have := congrArg (Subgroup.comap ε.toMonoidHom) htop
    rwa [Subgroup.comap_map_eq_self_of_injective ε.injective, Subgroup.comap_top] at this
  have h3 := solvable_of_overgroup _ h1 h2
  exact Group.isSolvable_of_isSolvable_injective
    (f := (M.equivMapOfInjective ε.toMonoidHom ε.injective).toMonoidHom)
    (M.equivMapOfInjective ε.toMonoidHom ε.injective).injective

end U3

section Families

variable {G : Type} [Group G] [Finite G] {T K Y : Subgroup G}

theorem false_of_u33
    (h : LtHyp G T K Y)
    (hLie : LieModel (↥Y ⧸ CFSG.pCore 2 ↥Y) .PSU 3 3 1) : False := by
  obtain ⟨hc, hZ⟩ := card_center_of_lieModel_psu h.hYq hLie
  have hsimple : IsSimpleGroup (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
    have : IsSimpleGroup ((↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)) :=
      h.hYq.2.1
    have e : (↥Y ⧸ CFSG.pCore 2 ↥Y) ≃*
        ((↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)) :=
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
    exact e.isSimpleGroup
  have hX : ∃ a b : (↥Y ⧸ CFSG.pCore 2 ↥Y), a * b ≠ b * a :=
    Seven.nonabelian_of_card_not_prime (by rw [hc]; norm_num)
  exact false_of_nu_vac h hX (MonoidHom.id _) Function.surjective_id
    fun S M hS hSM hM => U3.solvOver hLie S M hS hSM hM

end Families

end Lem1227Lt

end CFSG.Quasithin.H13
