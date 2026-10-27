module

public import CFSG.Quasithin.Background.D2Basic
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

private instance s16h_e3_CycThreeCentAAAA_mulAutAction (Ω : Type*) [Group Ω] :
    MulAction (MulAut Ω) (Subgroup Ω) where
  smul e X := X.map e.toMonoidHom
  one_smul X := by
    change X.map (1 : MulAut Ω).toMonoidHom = X
    rw [show (1 : MulAut Ω).toMonoidHom = MonoidHom.id Ω from
      MonoidHom.ext fun x => rfl]
    exact Subgroup.map_id X
  mul_smul e₁ e₂ X := by
    change X.map (e₁ * e₂).toMonoidHom = (X.map e₂.toMonoidHom).map e₁.toMonoidHom
    rw [Subgroup.map_map]
    congr 1

private instance s16h_e3_CycThreeCentAAAA_restrictAction
    {Ω : Type*} [Group Ω] {E : Subgroup (MulAut Ω)} : MulAction ↥E (Subgroup Ω) where
  smul g X := X.map (g : MulAut Ω).toMonoidHom
  one_smul X := by
    change X.map ((1 : ↥E) : MulAut Ω).toMonoidHom = X
    rw [show ((1 : ↥E) : MulAut Ω) = 1 from rfl]
    rw [show (1 : MulAut Ω).toMonoidHom = MonoidHom.id Ω from
      MonoidHom.ext fun x => rfl]
    exact Subgroup.map_id X
  mul_smul g h X := by
    change X.map ((g * h : ↥E) : MulAut Ω).toMonoidHom =
      (X.map (h : MulAut Ω).toMonoidHom).map (g : MulAut Ω).toMonoidHom
    rw [Subgroup.map_map]
    congr 1

private theorem s16h_e3_CycThreeCentAAAA_mem_stabSub_iff_map_eq
    {Ω : Type*} [CommGroup Ω] (e : MulAut Ω) (X : Subgroup Ω) :
    e ∈ stabSub X ↔ X.map e.toMonoidHom = X := by
  constructor
  · intro h
    rw [mem_stabSub] at h
    refine le_antisymm ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap]
      intro u hu
      exact (h u).2 hu
    · intro u hu
      refine Subgroup.mem_map.mpr ⟨e⁻¹ u, (h (e⁻¹ u)).1 (by simpa using hu), ?_⟩
      simp
  · intro h
    rw [mem_stabSub]
    intro u
    constructor
    · intro hu
      rw [← h] at hu
      rw [Subgroup.mem_map] at hu
      obtain ⟨x, hx, hxe⟩ := hu
      have : x = u := e.injective hxe
      rwa [this] at hx
    · intro hu
      rw [← h]
      exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩

private def s16h_e3_CycThreeCentAAAA_fixSub {Ω : Type*} [Group Ω]
    (k : MulAut Ω) : Subgroup Ω where
  carrier := {u | k u = u}
  one_mem' := map_one k
  mul_mem' := by
    intro a b ha hb
    show k (a * b) = a * b
    rw [map_mul, ha, hb]
  inv_mem' := by
    intro a ha
    show k a⁻¹ = a⁻¹
    rw [map_inv, ha]

private theorem s16h_e3_CycThreeCentAAAA_eq_three_of_dvd_27 {d : ℕ}
    (hdvd : d ∣ 27) (h2 : 2 ≤ d) (h3 : d ≤ 3) : d = 3 := by
  interval_cases d
  · norm_num at hdvd
  · rfl

private theorem s16h_e3_CycThreeCentAAAA_inf_card_ge_three
    {G : Type*} [Group G] {E A B : Subgroup G} (hE27 : Nat.card ↥E = 27)
    (hAE : A ≤ E) (hBE : B ≤ E)
    (hA9 : 9 ≤ Nat.card ↥A) (hB9 : 9 ≤ Nat.card ↥B) :
    3 ≤ Nat.card ↥(A ⊓ B) := by
  have hprodA : A.relIndex E * Nat.card ↥A = 27 := by
    have h := Subgroup.relIndex_mul_card A E
    rw [inf_eq_left.mpr hAE, hE27] at h
    exact h
  have hAid : A.relIndex E ≤ 3 := by
    by_contra h
    have h4 : 4 ≤ A.relIndex E := by omega
    have h36 : 36 ≤ A.relIndex E * Nat.card ↥A := by
      calc 36 = 4 * 9 := by norm_num
        _ ≤ A.relIndex E * Nat.card ↥A := Nat.mul_le_mul h4 hA9
    omega
  have hprodB : B.relIndex E * Nat.card ↥B = 27 := by
    have h := Subgroup.relIndex_mul_card B E
    rw [inf_eq_left.mpr hBE, hE27] at h
    exact h
  have hBid : B.relIndex E ≤ 3 := by
    by_contra h
    have h4 : 4 ≤ B.relIndex E := by omega
    have h36 : 36 ≤ B.relIndex E * Nat.card ↥B := by
      calc 36 = 4 * 9 := by norm_num
        _ ≤ B.relIndex E * Nat.card ↥B := Nat.mul_le_mul h4 hB9
    omega
  have hinfid : (A ⊓ B).relIndex E ≤ 9 := by
    calc (A ⊓ B).relIndex E
        ≤ A.relIndex E * B.relIndex E := Subgroup.relIndex_inf_le
      _ ≤ 3 * 3 := Nat.mul_le_mul hAid hBid
      _ = 9 := by norm_num
  have hABE : A ⊓ B ≤ E := le_trans inf_le_left hAE
  have hprodAB : (A ⊓ B).relIndex E * Nat.card ↥(A ⊓ B) = 27 := by
    have h := Subgroup.relIndex_mul_card (A ⊓ B) E
    rw [inf_eq_left.mpr hABE, hE27] at h
    exact h
  by_contra h
  have h2 : Nat.card ↥(A ⊓ B) ≤ 2 := by omega
  have hle : (A ⊓ B).relIndex E * Nat.card ↥(A ⊓ B) ≤ 9 * 2 :=
    Nat.mul_le_mul hinfid h2
  omega

theorem s16h_e3_three_summands_fixed_pair {Ω : Type} [CommGroup Ω] [Finite Ω]
    {E : Subgroup (MulAut Ω)} (hE : IsElemAbelian 3 E) (hEcard : Nat.card ↥E = 3 ^ 3)
    {𝒲 : Set (Subgroup Ω)} (hcard : 𝒲.ncard = 3) (hsup : (⨆ X ∈ 𝒲, X) = ⊤)
    (hperm : ∀ e ∈ E, ∀ X ∈ 𝒲, X.map e.toMonoidHom ∈ 𝒲)
    (hrank : ∀ X ∈ 𝒲, ∀ B : Subgroup (MulAut Ω), B ≤ E → B ≤ stabSub X →
      Nat.card ↥B ≤ 3 * Nat.card ↥(B ⊓ centSub X))
    {X Y : Subgroup Ω} (hX : X ∈ 𝒲) (hY : Y ∈ 𝒲) :
    ∃ e ∈ E, e ≠ 1 ∧ e ∈ centSub X ∧ e ∈ centSub Y := by
  haveI hEcomm : IsMulCommutative ↥E := hE.1
  have hWfin : 𝒲.Finite := Set.finite_of_ncard_ne_zero (by rw [hcard]; norm_num)
  have hstab_eq : ∀ Z : Subgroup Ω,
      MulAction.stabilizer ↥E Z = (E ⊓ stabSub Z).subgroupOf E := by
    intro Z
    ext e
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      s16h_e3_CycThreeCentAAAA_mem_stabSub_iff_map_eq]
    exact ⟨fun h => ⟨e.2, h⟩, fun h => h.2⟩
  have hsubOrbit : ∀ Z ∈ 𝒲, MulAction.orbit ↥E Z ⊆ 𝒲 := by
    intro Z hZ W hW
    rw [MulAction.mem_orbit_iff] at hW
    obtain ⟨g, rfl⟩ := hW
    exact hperm (g : MulAut Ω) g.2 Z hZ
  have horbit_le : ∀ Z ∈ 𝒲, (MulAction.orbit ↥E Z).ncard ≤ 3 := by
    intro Z hZ
    calc (MulAction.orbit ↥E Z).ncard ≤ 𝒲.ncard :=
          Set.ncard_le_ncard (hsubOrbit Z hZ) hWfin
      _ = 3 := hcard
  have hstab : ∀ Z ∈ 𝒲, E ≤ stabSub Z := by
    intro Z hZ
    by_contra hnot
    obtain ⟨e, heE, heNot⟩ : ∃ e : MulAut Ω, e ∈ E ∧ e ∉ stabSub Z := by
      by_contra h
      exact hnot fun e he => by
        by_contra hmem
        exact h ⟨e, he, hmem⟩
    have heZ : e • Z ≠ Z := by
      intro hh
      exact heNot ((s16h_e3_CycThreeCentAAAA_mem_stabSub_iff_map_eq e Z).mpr hh)
    have hSE : E ⊓ stabSub Z ≤ E := inf_le_left
    have hprod : (E ⊓ stabSub Z).relIndex E * Nat.card ↥(E ⊓ stabSub Z) = 27 := by
      have h := Subgroup.relIndex_mul_card (E ⊓ stabSub Z) E
      rw [inf_eq_left.mpr hSE, hEcard] at h
      norm_num at h
      exact h
    have hrelStab : (E ⊓ stabSub Z).relIndex E = (MulAction.orbit ↥E Z).ncard := by
      rw [Subgroup.relIndex, ← hstab_eq Z]
      exact MulAction.index_stabilizer ↥E Z
    have h2orb : 2 ≤ (MulAction.orbit ↥E Z).ncard := by
      have hne' : Z ≠ e • Z := fun hh => heZ hh.symm
      have hsub : ({Z, e • Z} : Set (Subgroup Ω)) ⊆ MulAction.orbit ↥E Z := by
        intro W hW
        rcases hW with h | h
        · rw [h]; exact MulAction.mem_orbit_self Z
        · rw [h]; exact MulAction.mem_orbit_iff.mpr ⟨⟨e, heE⟩, rfl⟩
      calc 2 = ({Z, e • Z} : Set (Subgroup Ω)).ncard := (Set.ncard_pair hne').symm
        _ ≤ (MulAction.orbit ↥E Z).ncard :=
            Set.ncard_le_ncard hsub (hWfin.subset (hsubOrbit Z hZ))
    have hdiv : (MulAction.orbit ↥E Z).ncard ∣ 27 := by
      rw [← hrelStab]
      exact ⟨Nat.card ↥(E ⊓ stabSub Z), hprod.symm⟩
    have horbit3 : (MulAction.orbit ↥E Z).ncard = 3 :=
      s16h_e3_CycThreeCentAAAA_eq_three_of_dvd_27 hdiv h2orb (horbit_le Z hZ)
    have horbit_eq : MulAction.orbit ↥E Z = 𝒲 :=
      Set.eq_of_subset_of_ncard_le (hsubOrbit Z hZ) (by rw [hcard, horbit3]) hWfin
    have hcardS : Nat.card ↥(E ⊓ stabSub Z) = 9 := by
      rw [hrelStab, horbit3] at hprod
      omega
    have hk3 : 3 ≤ Nat.card ↥((E ⊓ stabSub Z) ⊓ centSub Z) := by
      have h := hrank Z hZ (E ⊓ stabSub Z) inf_le_left inf_le_right
      rw [hcardS] at h
      have h' : 3 * 3 ≤ 3 * Nat.card ↥((E ⊓ stabSub Z) ⊓ centSub Z) := by simpa using h
      exact Nat.le_of_mul_le_mul_left h' (by norm_num)
    obtain ⟨k, hkS, hk1⟩ :
        ∃ k : MulAut Ω, k ∈ (E ⊓ stabSub Z) ⊓ centSub Z ∧ k ≠ 1 := by
      rcases Subgroup.bot_or_exists_ne_one ((E ⊓ stabSub Z) ⊓ centSub Z) with hbot | h
      · exfalso
        rw [hbot, Subgroup.card_bot] at hk3
        omega
      · exact h
    have hkE : k ∈ E := hkS.1.1
    have hkZ : k ∈ centSub Z := hkS.2
    have hkcent : ∀ W ∈ 𝒲, k ∈ centSub W := by
      intro W hW
      have hWorb : W ∈ MulAction.orbit ↥E Z := by rw [horbit_eq]; exact hW
      rw [MulAction.mem_orbit_iff] at hWorb
      obtain ⟨g, hg⟩ := hWorb
      rw [mem_centSub]
      intro u hu
      rw [← hg] at hu
      change u ∈ Z.map (g : MulAut Ω).toMonoidHom at hu
      rw [Subgroup.mem_map] at hu
      obtain ⟨x, hx, hxu⟩ := hu
      rw [← hxu]
      have hcomm : k * (g : MulAut Ω) = (g : MulAut Ω) * k := by
        have hEq : (⟨k, hkE⟩ : ↥E) * g = g * ⟨k, hkE⟩ := mul_comm' _ _
        have := congrArg (Subtype.val) hEq
        simpa only [Subgroup.coe_mul, Subtype.coe_mk] using this
      calc k ((g : MulAut Ω) x) = (k * (g : MulAut Ω)) x := rfl
        _ = ((g : MulAut Ω) * k) x := by rw [hcomm]
        _ = (g : MulAut Ω) (k x) := rfl
        _ = (g : MulAut Ω) x := by rw [(mem_centSub.mp hkZ) x hx]
    have hleFix : (⨆ W ∈ 𝒲, W) ≤ s16h_e3_CycThreeCentAAAA_fixSub k := by
      refine iSup_le fun W => iSup_le fun hW => ?_
      intro u hu
      exact (mem_centSub.mp (hkcent W hW)) u hu
    have hkD : k ∈ centSub (⨆ W ∈ 𝒲, W) := by
      rw [mem_centSub]
      intro u hu
      exact hleFix hu
    have hktop : k ∈ centSub (⊤ : Subgroup Ω) := by
      rw [hsup] at hkD
      exact hkD
    rw [mem_centSub] at hktop
    exact hk1 (MulEquiv.ext fun u => hktop u trivial)
  have hXstab : E ≤ stabSub X := hstab X hX
  have hYstab : E ≤ stabSub Y := hstab Y hY
  have hA9 : 9 ≤ Nat.card ↥(E ⊓ centSub X) := by
    have h := hrank X hX E le_rfl hXstab
    rw [hEcard] at h
    have h' : 3 * 9 ≤ 3 * Nat.card ↥(E ⊓ centSub X) := by simpa using h
    exact Nat.le_of_mul_le_mul_left h' (by norm_num)
  have hB9 : 9 ≤ Nat.card ↥(E ⊓ centSub Y) := by
    have h := hrank Y hY E le_rfl hYstab
    rw [hEcard] at h
    have h' : 3 * 9 ≤ 3 * Nat.card ↥(E ⊓ centSub Y) := by simpa using h
    exact Nat.le_of_mul_le_mul_left h' (by norm_num)
  have hAB3 : 3 ≤ Nat.card ↥((E ⊓ centSub X) ⊓ (E ⊓ centSub Y)) :=
    s16h_e3_CycThreeCentAAAA_inf_card_ge_three (G := MulAut Ω) (E := E)
      (A := E ⊓ centSub X) (B := E ⊓ centSub Y)
      (by rw [hEcard]; norm_num) inf_le_left inf_le_left hA9 hB9
  have hABne : (E ⊓ centSub X) ⊓ (E ⊓ centSub Y) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hAB3
    omega
  rcases Subgroup.bot_or_exists_ne_one ((E ⊓ centSub X) ⊓ (E ⊓ centSub Y)) with
    hbot | ⟨e, heAB, he1⟩
  · exact absurd hbot hABne
  · refine ⟨e, ?_, he1, ?_, ?_⟩
    · exact (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp heAB).1).1
    · exact (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp heAB).1).2
    · exact (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp heAB).2).2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
