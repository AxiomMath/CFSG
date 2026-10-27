module

public import CFSG.Quasithin.EmptyFaithful.SBc2SzLift
public import CFSG.Quasithin.Background.A3Structure312Embed

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SBc2

section General

variable {G : Type} [Group G] [Finite G]

theorem le_of_normal_sylow {P H Q : Subgroup G} (hP : IsSylowTwoOf P H)
    (hN : H ≤ Subgroup.normalizer (P : Set G)) (hQH : Q ≤ H) (hQ : IsPGroup 2 Q) : Q ≤ P := by
  obtain ⟨R, hR, hQR⟩ := A4.exists_isSylowTwoOf_ge hQH hQ
  obtain ⟨h, hh, hconj⟩ := A4.exists_conj_of_isSylowTwoOf hP hR
  intro q hq
  have h1 := (hconj q).mp (hQR hq)
  have h2 := (Subgroup.mem_normalizer_iff.mp (hN hh) _).mp h1
  have e : h * (h⁻¹ * q * h) * h⁻¹ = q := by group
  rw [e] at h2
  exact h2

theorem sup_le_normalizer_of_solv {A L P : Subgroup G} (hP : IsSylowTwoOf P L)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hA : Group.IsSolvable ↥A) (hPA : P ≤ A)
    (hsolv : ∀ H : Subgroup G, H ≤ L → Group.IsSolvable ↥H → P ≤ H →
      H ≤ Subgroup.normalizer (P : Set G)) : A ≤ Subgroup.normalizer (P : Set G) := by
  have hPL := hP.1
  set H : Subgroup G := A ⊓ L with hH
  have hHL : H ≤ L := inf_le_right
  have hHA : H ≤ A := inf_le_left
  have hPH : P ≤ H := le_inf hPA hPL
  have hHsolv : Group.IsSolvable ↥H :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hHA).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hHA).surjective
  have hHN : H ≤ Subgroup.normalizer (P : Set G) := hsolv H hHL hHsolv hPH
  have hPH' : IsSylowTwoOf P H := A4.isSylowTwoOf_mono hP hPH hHL
  intro a ha
  refine A4.mem_normalizer_of_conj_mem fun p hp => ?_
  set Q : Subgroup G := P.map (MulAut.conj a).toMonoidHom with hQ
  have hQH : Q ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨A.mul_mem (A.mul_mem ha (hPA hx)) (A.inv_mem ha),
      (Subgroup.mem_normalizer_iff.mp (hAL ha) x).mp (hPL hx)⟩
  have hQ2 : IsPGroup 2 Q := hP.2.1.map _
  exact le_of_normal_sylow hPH' hHN hQH hQ2 ⟨p, hp, rfl⟩

theorem charTwo_borel {L P : Subgroup G} (hP : IsSylowTwoOf P L) (hSz : SzLift L P) :
    CharTwo (L ⊓ Subgroup.normalizer (P : Set G)) := by
  set B : Subgroup G := L ⊓ Subgroup.normalizer (P : Set G) with hB
  have hPB : IsSylowTwoOf P B :=
    A4.isSylowTwoOf_mono hP (le_inf hP.1 Subgroup.le_normalizer) inf_le_left
  have hp : pCoreOf 2 B = P := by
    refine le_antisymm (QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hPB) ?_
    exact le_pCoreOf_of_le_normalizer 2 hPB.1 inf_le_right hP.2.1
  intro b hb
  rw [hp] at hb ⊢
  obtain ⟨hbB, hbC⟩ := hb
  refine hSz.cent b hbB.1 fun p hp' => ?_
  have h := Subgroup.mem_centralizer_iff.mp hbC p hp'
  have e : b * p * b⁻¹ * p⁻¹ = 1 := by
    rw [← h]
    group
  rw [e]
  exact Subgroup.one_mem _

end General

section Prod

variable {G : Type} [Group G] [Finite G] {L L' : Subgroup G}

theorem le_normalizer_of_commutator_le (hc : ⁅L, L'⁆ ≤ pCoreOf 2 L ⊓ pCoreOf 2 L') :
    L ≤ Subgroup.normalizer (L' : Set G) ∧ L' ≤ Subgroup.normalizer (L : Set G) := by
  constructor
  · intro l hl
    refine A4.mem_normalizer_of_conj_mem fun x hx => ?_
    have h1 : ⁅l, x⁆ ∈ pCoreOf 2 L' := (hc (Subgroup.commutator_mem_commutator hl hx)).2
    have e : l * x * l⁻¹ = ⁅l, x⁆ * x := by simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact L'.mul_mem (pCoreOf_le 2 L' h1) hx
  · intro x hx
    refine A4.mem_normalizer_of_conj_mem fun l hl => ?_
    have h1 : ⁅l, x⁆ ∈ pCoreOf 2 L := (hc (Subgroup.commutator_mem_commutator hl hx)).1
    have h2 : ⁅l, x⁆⁻¹ ∈ pCoreOf 2 L := (pCoreOf 2 L).inv_mem h1
    have e : x * l * x⁻¹ = ⁅l, x⁆⁻¹ * l := by simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact L.mul_mem (pCoreOf_le 2 L h2) hl

omit [Finite G] in
theorem exists_mul_of_mem_sup_of_le_normalizer {A B : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right A B hAB] at hx
  exact hx

theorem sylow_inf_left (hc : ⁅L, L'⁆ ≤ pCoreOf 2 L ⊓ pCoreOf 2 L') {P : Subgroup G}
    (hP : IsSylowTwoOf P (L ⊔ L')) : IsSylowTwoOf (P ⊓ L) L :=
  A4.isSylowTwoOf_inf_normal hP le_sup_left
    (sup_le Subgroup.le_normalizer (le_normalizer_of_commutator_le hc).2)

theorem sylow_inf_right (hc : ⁅L, L'⁆ ≤ pCoreOf 2 L ⊓ pCoreOf 2 L') {P : Subgroup G}
    (hP : IsSylowTwoOf P (L ⊔ L')) : IsSylowTwoOf (P ⊓ L') L' :=
  A4.isSylowTwoOf_inf_normal hP le_sup_right
    (sup_le (le_normalizer_of_commutator_le hc).1 Subgroup.le_normalizer)

theorem exists_mul_of_sylow (hc : ⁅L, L'⁆ ≤ pCoreOf 2 L ⊓ pCoreOf 2 L') {P : Subgroup G}
    (hP : IsSylowTwoOf P (L ⊔ L')) {p : G} (hp : p ∈ P) :
    ∃ p₁ ∈ P ⊓ L, ∃ p₂ ∈ P ⊓ L', p₁ * p₂ = p := by
  have hLN := le_normalizer_of_commutator_le hc
  have h1 : p ∈ (P ⊓ L) ⊔ L' :=
    A312.inf_sup_le_of_sylow (sylow_inf_left hc hP) hP.2.1 hLN.1 ⟨hp, hP.1 hp⟩
  obtain ⟨p₁, hp₁, l', hl', hpl⟩ := exists_mul_of_mem_sup_of_le_normalizer
    (inf_le_right.trans hLN.1) h1
  refine ⟨p₁, hp₁, l', ⟨?_, hl'⟩, hpl⟩
  have e : l' = p₁⁻¹ * p := by rw [← hpl]; group
  rw [e]
  exact P.mul_mem (P.inv_mem hp₁.1) hp

theorem mem_normalizer_of_sylow (hc : ⁅L, L'⁆ ≤ pCoreOf 2 L ⊓ pCoreOf 2 L') {P : Subgroup G}
    (hP : IsSylowTwoOf P (L ⊔ L')) {x : G} (h1 : x ∈ Subgroup.normalizer ((P ⊓ L : Subgroup G) : Set G))
    (h2 : x ∈ Subgroup.normalizer ((P ⊓ L' : Subgroup G) : Set G)) :
    x ∈ Subgroup.normalizer (P : Set G) := by
  refine A4.mem_normalizer_of_conj_mem fun p hp => ?_
  obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := exists_mul_of_sylow hc hP hp
  have e : x * (p₁ * p₂) * x⁻¹ = (x * p₁ * x⁻¹) * (x * p₂ * x⁻¹) := by group
  rw [e]
  exact P.mul_mem ((Subgroup.mem_normalizer_iff.mp h1 p₁).mp hp₁).1
    ((Subgroup.mem_normalizer_iff.mp h2 p₂).mp hp₂).1

theorem mem_normalizer_of_left (hc : ⁅L, L'⁆ ≤ pCoreOf 2 L ⊓ pCoreOf 2 L') {P : Subgroup G}
    (hP : IsSylowTwoOf P (L ⊔ L')) {l : G} (hl : l ∈ L)
    (h1 : l ∈ Subgroup.normalizer ((P ⊓ L : Subgroup G) : Set G)) :
    l ∈ Subgroup.normalizer (P : Set G) := by
  have hLN := le_normalizer_of_commutator_le hc
  have hP' : IsSylowTwoOf (P ⊓ L') L' := sylow_inf_right hc hP
  refine mem_normalizer_of_sylow hc hP h1 ?_
  refine A4.mem_normalizer_of_conj_mem fun p hp => ?_
  have hcom : ⁅l, p⁆ ∈ pCoreOf 2 L' := (hc (Subgroup.commutator_mem_commutator hl hp.2)).2
  have hcP : ⁅l, p⁆ ∈ P ⊓ L' :=
    QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hP' hcom
  have e : l * p * l⁻¹ = ⁅l, p⁆ * p := by simp [commutatorElement_def, mul_assoc]
  rw [e]
  exact (P ⊓ L').mul_mem hcP hp

theorem mem_normalizer_of_right (hc : ⁅L, L'⁆ ≤ pCoreOf 2 L ⊓ pCoreOf 2 L') {P : Subgroup G}
    (hP : IsSylowTwoOf P (L ⊔ L')) {l : G} (hl : l ∈ L')
    (h1 : l ∈ Subgroup.normalizer ((P ⊓ L' : Subgroup G) : Set G)) :
    l ∈ Subgroup.normalizer (P : Set G) := by
  have hc' : ⁅L', L⁆ ≤ pCoreOf 2 L' ⊓ pCoreOf 2 L := by
    rw [Subgroup.commutator_comm, inf_comm]
    exact hc
  have hP' : IsSylowTwoOf P (L' ⊔ L) := by rw [sup_comm]; exact hP
  exact mem_normalizer_of_left hc' hP' hl h1

theorem prod_sup_le_normalizer (hc : ⁅L, L'⁆ ≤ pCoreOf 2 L ⊓ pCoreOf 2 L') {P A : Subgroup G}
    (hP : IsSylowTwoOf P (L ⊔ L')) (hSz : SzLift L (P ⊓ L)) (hSz' : SzLift L' (P ⊓ L'))
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hAL' : A ≤ Subgroup.normalizer (L' : Set G))
    (hA : Group.IsSolvable ↥A) (hPA : P ≤ A) : A ≤ Subgroup.normalizer (P : Set G) := by
  have h1 : A ≤ Subgroup.normalizer ((P ⊓ L : Subgroup G) : Set G) :=
    sup_le_normalizer_of_solv (sylow_inf_left hc hP) hAL hA (inf_le_left.trans hPA) hSz.solv
  have h2 : A ≤ Subgroup.normalizer ((P ⊓ L' : Subgroup G) : Set G) :=
    sup_le_normalizer_of_solv (sylow_inf_right hc hP) hAL' hA (inf_le_left.trans hPA) hSz'.solv
  exact fun a ha => mem_normalizer_of_sylow hc hP (h1 ha) (h2 ha)

theorem inf_normalizer_le_borel (hc : ⁅L, L'⁆ ≤ pCoreOf 2 L ⊓ pCoreOf 2 L') {P : Subgroup G}
    (hP : IsSylowTwoOf P (L ⊔ L')) :
    L ⊓ Subgroup.normalizer ((P ⊓ L : Subgroup G) : Set G) ≤
      (L ⊔ L') ⊓ Subgroup.normalizer (P : Set G) :=
  fun _ hl => ⟨Subgroup.mem_sup_left hl.1, mem_normalizer_of_left hc hP hl.1 hl.2⟩

theorem inf_normalizer_le_borel' (hc : ⁅L, L'⁆ ≤ pCoreOf 2 L ⊓ pCoreOf 2 L') {P : Subgroup G}
    (hP : IsSylowTwoOf P (L ⊔ L')) :
    L' ⊓ Subgroup.normalizer ((P ⊓ L' : Subgroup G) : Set G) ≤
      (L ⊔ L') ⊓ Subgroup.normalizer (P : Set G) :=
  fun _ hl => ⟨Subgroup.mem_sup_right hl.1, mem_normalizer_of_right hc hP hl.1 hl.2⟩

theorem prod_maximal (hc : ⁅L, L'⁆ ≤ pCoreOf 2 L ⊓ pCoreOf 2 L') {P : Subgroup G}
    (hP : IsSylowTwoOf P (L ⊔ L')) (hSz : SzLift L (P ⊓ L)) (hSz' : SzLift L' (P ⊓ L'))
    {s : G} (hLL' : L' = L.map (MulAut.conj s).toMonoidHom) {X : Subgroup G} (hX : X ≤ L ⊔ L')
    (hs : s ∈ Subgroup.normalizer (X : Set G))
    (hBX : (L ⊔ L') ⊓ Subgroup.normalizer (P : Set G) ≤ X) (hne : X ≠ L ⊔ L') :
    X = (L ⊔ L') ⊓ Subgroup.normalizer (P : Set G) := by
  have hLN := le_normalizer_of_commutator_le hc
  have hL₀L : L ⊔ L' ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hLN.2
  have hL₀L' : L ⊔ L' ≤ Subgroup.normalizer (L' : Set G) := sup_le hLN.1 Subgroup.le_normalizer
  have hP₁ := sylow_inf_left hc hP
  have hP₂ := sylow_inf_right hc hP
  have hs' : s⁻¹ ∈ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normalizer (X : Set G)).inv_mem hs
  have hXL : X ⊓ L = L ⊓ Subgroup.normalizer ((P ⊓ L : Subgroup G) : Set G) := by
    rcases hSz.maximal (X ⊓ L) inf_le_right
        (le_inf (fun l hl => hBX (inf_normalizer_le_borel hc hP hl)) fun l hl => hl.1) with h | h
    · exact h
    · exfalso
      have hLX : L ≤ X := inf_eq_right.mp h
      apply hne
      refine le_antisymm hX (sup_le hLX ?_)
      rw [hLL']
      rintro _ ⟨l, hl, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hs l).mp (hLX hl)
  have hXL' : X ⊓ L' = L' ⊓ Subgroup.normalizer ((P ⊓ L' : Subgroup G) : Set G) := by
    rcases hSz'.maximal (X ⊓ L') inf_le_right
        (le_inf (fun l hl => hBX (inf_normalizer_le_borel' hc hP hl)) fun l hl => hl.1) with h | h
    · exact h
    · exfalso
      have hL'X : L' ≤ X := inf_eq_right.mp h
      apply hne
      have hLX : L ≤ X := by
        intro l hl
        have hmem : s * l * s⁻¹ ∈ L' := by
          rw [hLL']
          exact ⟨l, hl, rfl⟩
        have := (Subgroup.mem_normalizer_iff.mp hs' _).mp (hL'X hmem)
        simpa [mul_assoc] using this
      exact le_antisymm hX (sup_le hLX hL'X)
  refine le_antisymm (fun x hx => ⟨hX hx, ?_⟩) hBX
  have hxN : x ∈ Subgroup.normalizer (X : Set G) := Subgroup.le_normalizer hx
  have key : ∀ (K : Subgroup G) (hKN : x ∈ Subgroup.normalizer (K : Set G)) (Pk : Subgroup G),
      IsSylowTwoOf Pk K → (X ⊓ K = K ⊓ Subgroup.normalizer (Pk : Set G)) →
      x ∈ Subgroup.normalizer (Pk : Set G) := by
    intro K hKN Pk hPk hXK
    have hPkB : IsSylowTwoOf Pk (K ⊓ Subgroup.normalizer (Pk : Set G)) :=
      A4.isSylowTwoOf_mono hPk (le_inf hPk.1 Subgroup.le_normalizer) inf_le_left
    refine A4.mem_normalizer_of_conj_mem fun p hp => ?_
    set Q : Subgroup G := Pk.map (MulAut.conj x).toMonoidHom with hQ
    have hQB : Q ≤ K ⊓ Subgroup.normalizer (Pk : Set G) := by
      rw [← hXK]
      rintro _ ⟨y, hy, rfl⟩
      have hyB : y ∈ X ⊓ K := by
        rw [hXK]
        exact ⟨hPk.1 hy, Subgroup.le_normalizer hy⟩
      exact ⟨X.mul_mem (X.mul_mem hx hyB.1) (X.inv_mem hx),
        (Subgroup.mem_normalizer_iff.mp hKN y).mp hyB.2⟩
    exact le_of_normal_sylow hPkB inf_le_right hQB (hPk.2.1.map _) ⟨p, hp, rfl⟩
  have h1 : x ∈ Subgroup.normalizer ((P ⊓ L : Subgroup G) : Set G) :=
    key L (hL₀L (hX hx)) _ hP₁ hXL
  have h2 : x ∈ Subgroup.normalizer ((P ⊓ L' : Subgroup G) : Set G) :=
    key L' (hL₀L' (hX hx)) _ hP₂ hXL'
  exact mem_normalizer_of_sylow hc hP h1 h2

omit [Finite G] in
theorem left_part (hc : ⁅L, L'⁆ ≤ pCoreOf 2 L ⊓ pCoreOf 2 L') {P : Subgroup G}
    (hSz : SzLift L (P ⊓ L)) (hZ : centerOf L = pCoreOf 2 L) {l l' : G} (hl : l ∈ L)
    (hl' : l' ∈ L') (hb : ∀ p ∈ P, p * (l * l') = (l * l') * p) : l ∈ P ⊓ L := by
  refine hSz.cent l hl fun p hp => ?_
  have hc' : ⁅L', L⁆ ≤ pCoreOf 2 L' ⊓ pCoreOf 2 L := by
    rw [Subgroup.commutator_comm, inf_comm]
    exact hc
  obtain ⟨c, hcdef⟩ : ∃ c, c = l' * p * l'⁻¹ * p⁻¹ := ⟨_, rfl⟩
  have hcz : c ∈ centerOf L := by
    rw [hZ, hcdef]
    exact (hc' (Subgroup.commutator_mem_commutator hl' hp.2)).2
  have hlc : l * c = c * l := Subgroup.mem_centralizer_iff.mp hcz.2 l hl
  have hbp : (l * l') * p * (l * l')⁻¹ = p := by
    have := hb p hp.1
    calc (l * l') * p * (l * l')⁻¹ = (p * (l * l')) * (l * l')⁻¹ := by rw [this]
      _ = p := by group
  have h2 : l * (c * p) * l⁻¹ = p := by
    have : (l * l') * p * (l * l')⁻¹ = l * (c * p) * l⁻¹ := by rw [hcdef]; group
    rw [← this]
    exact hbp
  have h1 : c * (l * p * l⁻¹) = p := by
    calc c * (l * p * l⁻¹) = (c * l) * p * l⁻¹ := by group
      _ = (l * c) * p * l⁻¹ := by rw [hlc]
      _ = l * (c * p) * l⁻¹ := by group
      _ = p := h2
  have e : l * p * l⁻¹ * p⁻¹ = c⁻¹ := by
    have h3 : l * p * l⁻¹ = c⁻¹ * p := by
      calc l * p * l⁻¹ = c⁻¹ * (c * (l * p * l⁻¹)) := by group
        _ = c⁻¹ * p := by rw [h1]
    rw [h3]
    group
  rw [e]
  exact (centerOf L).inv_mem hcz

theorem prod_charTwo (hc : ⁅L, L'⁆ ≤ pCoreOf 2 L ⊓ pCoreOf 2 L') {P : Subgroup G}
    (hP : IsSylowTwoOf P (L ⊔ L')) (hSz : SzLift L (P ⊓ L)) (hSz' : SzLift L' (P ⊓ L'))
    (hZ : centerOf L = pCoreOf 2 L) (hZ' : centerOf L' = pCoreOf 2 L') :
    CharTwo ((L ⊔ L') ⊓ Subgroup.normalizer (P : Set G)) := by
  have hLN := le_normalizer_of_commutator_le hc
  set B : Subgroup G := (L ⊔ L') ⊓ Subgroup.normalizer (P : Set G) with hB
  have hPB : IsSylowTwoOf P B :=
    A4.isSylowTwoOf_mono hP (le_inf hP.1 Subgroup.le_normalizer) inf_le_left
  have hp : pCoreOf 2 B = P := by
    refine le_antisymm (QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hPB) ?_
    exact le_pCoreOf_of_le_normalizer 2 hPB.1 inf_le_right hP.2.1
  intro b hb
  rw [hp] at hb ⊢
  obtain ⟨hbB, hbC⟩ := hb
  have hbc : ∀ p ∈ P, p * b = b * p := fun p hp' => Subgroup.mem_centralizer_iff.mp hbC p hp'
  obtain ⟨l, hl, l', hl', rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hLN.1 hbB.1
  have h1 : l ∈ P ⊓ L := left_part hc hSz hZ hl hl' hbc
  have hl₂ : l'⁻¹ * l * l' ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (hLN.2 (L'.inv_mem hl')) l).mp hl
    simpa [mul_assoc] using this
  have hc' : ⁅L', L⁆ ≤ pCoreOf 2 L' ⊓ pCoreOf 2 L := by
    rw [Subgroup.commutator_comm, inf_comm]
    exact hc
  have hbc' : ∀ p ∈ P, p * (l' * (l'⁻¹ * l * l')) = (l' * (l'⁻¹ * l * l')) * p := by
    intro p hp'
    have e : l' * (l'⁻¹ * l * l') = l * l' := by group
    rw [e]
    exact hbc p hp'
  have hP' : IsSylowTwoOf P (L' ⊔ L) := by rw [sup_comm]; exact hP
  have hSz'' : SzLift L' (P ⊓ L') := hSz'
  have h2 : l' ∈ P ⊓ L' := left_part hc' hSz'' hZ' hl' hl₂ hbc'
  exact P.mul_mem h1.1 h2.1

end Prod

end SBc2

end CFSG.Quasithin
