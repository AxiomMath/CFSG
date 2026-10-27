module

public import CFSG.Quasithin.EmptyFaithful.S143KC
public import CFSG.Quasithin.EmptyFaithful.S143GD

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

open A6Model

section Generic

variable {G : Type*} [Group G]

theorem mm_I4 (M : Mat4) : mm M I4 = M := by
  obtain ⟨r0, r1, r2, r3⟩ := M
  show (⟨vm r0 I4, vm r1 I4, vm r2 I4, vm r3 I4⟩ : Mat4) = ⟨r0, r1, r2, r3⟩
  rw [vm_I4, vm_I4, vm_I4, vm_I4]

theorem mm_assoc (A B C : Mat4) : mm (mm A B) C = mm A (mm B C) := by
  show (⟨vm (vm A.r0 B) C, vm (vm A.r1 B) C, vm (vm A.r2 B) C, vm (vm A.r3 B) C⟩ : Mat4) =
    ⟨vm A.r0 (mm B C), vm A.r1 (mm B C), vm A.r2 (mm B C), vm A.r3 (mm B C)⟩
  rw [vm_vm, vm_vm, vm_vm, vm_vm]

theorem centralizer_conj_mem {A : Subgroup G} {γ c : G}
    (hγ : γ ∈ Subgroup.normalizer (A : Set G)) (hc : c ∈ Subgroup.centralizer (A : Set G)) :
    γ * c * γ⁻¹ ∈ Subgroup.centralizer (A : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hγ' : γ⁻¹ ∈ Subgroup.normalizer (A : Set G) := (Subgroup.normalizer _).inv_mem hγ
  have h1 : γ⁻¹ * a * γ⁻¹⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hγ' a).mp ha
  have h2 := Subgroup.mem_centralizer_iff.mp hc _ h1
  calc a * (γ * c * γ⁻¹) = γ * ((γ⁻¹ * a * γ⁻¹⁻¹) * c) * γ⁻¹ := by group
    _ = γ * (c * (γ⁻¹ * a * γ⁻¹⁻¹)) * γ⁻¹ := by rw [h2]
    _ = γ * c * γ⁻¹ * a := by group

variable {A : Subgroup G} {e0 e1 e2 e3 : G} (hB : IsBasis A e0 e1 e2 e3)

include hB

theorem A6Model.IsBasis.cmat_eq_iff_mem_centralizer {γ γ' : G}
    (hγ : γ ∈ Subgroup.normalizer (A : Set G)) (hγ' : γ' ∈ Subgroup.normalizer (A : Set G)) :
    cmat e0 e1 e2 e3 γ = cmat e0 e1 e2 e3 γ' ↔ γ⁻¹ * γ' ∈ Subgroup.centralizer (A : Set G) := by
  rw [hB.cmat_eq_iff hγ hγ', Subgroup.mem_centralizer_iff]
  constructor
  · intro h a ha
    have h1 := h a ha
    calc a * (γ⁻¹ * γ') = γ⁻¹ * (γ * a * γ⁻¹) * γ' := by group
      _ = γ⁻¹ * (γ' * a * γ'⁻¹) * γ' := by rw [h1]
      _ = γ⁻¹ * γ' * a := by group
  · intro h a ha
    have h1 := h a ha
    calc γ * a * γ⁻¹ = γ * (γ⁻¹ * γ' * a * (γ⁻¹ * γ')⁻¹) * γ⁻¹ := by
          rw [← h1]; group
      _ = γ' * a * γ'⁻¹ := by group

theorem A6Model.IsBasis.cmat_eq_one_iff_mem_centralizer {γ : G}
    (hγ : γ ∈ Subgroup.normalizer (A : Set G)) :
    cmat e0 e1 e2 e3 γ = I4 ↔ γ ∈ Subgroup.centralizer (A : Set G) := by
  rw [hB.cmat_eq_one_iff hγ, Subgroup.mem_centralizer_iff]
  constructor
  · intro h a ha
    have h1 := h a ha
    calc a * γ = (γ * a * γ⁻¹) * γ := by rw [h1]
      _ = γ * a := by group
  · intro h a ha
    have h1 := h a ha
    calc γ * a * γ⁻¹ = (a * γ) * γ⁻¹ := by rw [h1]
      _ = a := by group

end Generic

section Hyp

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)
  {r : G} (hrW : r ∈ Hyp1281Two.wOfU T M) (hrV : r ∉ VZ T M) (hr2 : r * r = 1)

include c hrW hrV hr2

theorem Counter.exists_not_comm_of_fpf {w : G} (hw : w ∈ iTwo T M)
    (hfpf : ∀ ρ ∈ rOf T M, w * ρ * w⁻¹ = ρ → ρ = 1) :
    ∃ ρ' ∈ rOf T M, w * ρ' * w⁻¹ * ρ'⁻¹ ∉ c.Ac hrW hrV hr2 := by
  by_contra hall
  push Not at hall
  obtain ⟨ρ₀, hρ₀R, hρ₀A⟩ : ∃ ρ₀ ∈ rOf T M, ρ₀ ∉ c.Ac hrW hrV hr2 := by
    by_contra hh
    push Not at hh
    have h1 : Nat.card (rOf T M) ≤ Nat.card (c.Ac hrW hrV hr2) :=
      Subgroup.card_le_of_le fun x hx => hh x hx
    rw [card_rOf c, c.card_Ac hrW hrV hr2] at h1
    omega
  have hRiTwo : rOf T M ≤ iTwo T M := pCoreOf_le 2 (iTwo T M)
  have hcomm : ∀ a ∈ c.Ac hrW hrV hr2, ∀ b ∈ c.Ac hrW hrV hr2, a * b = b * a := fun a ha b hb =>
    mul_comm_of_sq_eq_one (fun y hy => c.sq_Ac hrW hrV hr2 hy) ha hb
  have ha₀ : ρ₀⁻¹ * (w * ρ₀ * w⁻¹) ∈ c.Ac hrW hrV hr2 := by
    have h1 := c.Ac_conj_mem hrW hrV hr2 ((iTwo T M).inv_mem (hRiTwo hρ₀R)) (hall ρ₀ hρ₀R)
    have e : ρ₀⁻¹ * (w * ρ₀ * w⁻¹ * ρ₀⁻¹) * ρ₀⁻¹⁻¹ = ρ₀⁻¹ * (w * ρ₀ * w⁻¹) := by group
    rwa [e] at h1
  let _ : CommGroup ↥(c.Ac hrW hrV hr2) :=
    { (inferInstance : Group ↥(c.Ac hrW hrV hr2)) with
      mul_comm := fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2) }
  let φ : ↥(c.Ac hrW hrV hr2) →* ↥(c.Ac hrW hrV hr2) :=
    MonoidHom.mk' (fun b => ⟨w * (b : G) * w⁻¹, c.Ac_conj_mem hrW hrV hr2 hw b.2⟩)
      (fun b b' => Subtype.ext (by simp [mul_assoc]))
  let F : ↥(c.Ac hrW hrV hr2) →* ↥(c.Ac hrW hrV hr2) :=
    MonoidHom.mk' (fun b => b * (φ b)⁻¹) (fun b b' => by
      rw [map_mul, mul_inv]; ac_rfl)
  have hF : Function.Injective F := by
    rw [injective_iff_map_eq_one]
    intro b hb
    have h1 : b * (φ b)⁻¹ = 1 := hb
    have h2 : (b : G) = w * (b : G) * w⁻¹ := congrArg Subtype.val (mul_inv_eq_one.mp h1)
    exact Subtype.ext (hfpf _ (c.Ac_le_rOf hrW hrV hr2 b.2) h2.symm)
  obtain ⟨b, hb⟩ := Finite.injective_iff_surjective.mp hF ⟨ρ₀⁻¹ * (w * ρ₀ * w⁻¹), ha₀⟩
  have hb' : (b : G) * (w * (b : G) * w⁻¹)⁻¹ = ρ₀⁻¹ * (w * ρ₀ * w⁻¹) := congrArg Subtype.val hb
  have hfix : w * (ρ₀ * (b : G)) * w⁻¹ = ρ₀ * (b : G) := by
    calc w * (ρ₀ * (b : G)) * w⁻¹ = (w * ρ₀ * w⁻¹) * (w * (b : G) * w⁻¹) := by group
      _ = ρ₀ * ((ρ₀⁻¹ * (w * ρ₀ * w⁻¹)) * (w * (b : G) * w⁻¹)) := by group
      _ = ρ₀ * ((b : G) * (w * (b : G) * w⁻¹)⁻¹ * (w * (b : G) * w⁻¹)) := by rw [hb']
      _ = ρ₀ * (b : G) := by group
  have h0 := hfpf _ ((rOf T M).mul_mem hρ₀R (c.Ac_le_rOf hrW hrV hr2 b.2)) hfix
  apply hρ₀A
  have : ρ₀ = (b : G)⁻¹ := eq_inv_of_mul_eq_one_left h0
  rw [this]
  exact (c.Ac hrW hrV hr2).inv_mem b.2

theorem Counter.rOf_le_normalizer_Ac :
    rOf T M ≤ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) := fun _ hγ =>
  c.iTwo_le_normalizer_Ac hrW hrV hr2 (pCoreOf_le 2 (iTwo T M) hγ)

variable {c hrW hrV hr2}

variable {x z a r1 : G} (hS : Setup c hrW hrV hr2 x z a r1) {t : G} (htT : t ∈ T)
  (htRQ : t ∉ rOf T M ⊔ qOf T)

include hS htT htRQ

theorem Setup.exists_RHyp :
    ∃ R1 R2 : Mat4, IsRMat R1 ∧ IsRMat R2 ∧ RHypM R1 R2 ∧
      ∀ P, P ∈ [I4, R1, R2, mm R1 R2] ↔ ∃ ρ' ∈ rOf T M, cmat z a r r1 ρ' = P := by
  have hB := hS.basis
  have hRN := c.rOf_le_normalizer_Ac hrW hrV hr2
  have hcomm : ∀ a ∈ c.Ac hrW hrV hr2, ∀ b ∈ c.Ac hrW hrV hr2, a * b = b * a := hB.comm
  have hRC : Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) ⊓ rOf T M = c.Ac hrW hrV hr2 :=
    c.centralizer_inf_rOf_Ac hrW hrV hr2 htT htRQ
  have hAR := c.Ac_le_rOf hrW hrV hr2
  have hEq : ∀ s ∈ rOf T M, ∀ s' ∈ rOf T M,
      cmat z a r r1 s = cmat z a r r1 s' ↔ s⁻¹ * s' ∈ c.Ac hrW hrV hr2 := by
    intro s hs s' hs'
    rw [hB.cmat_eq_iff_mem_centralizer (hRN hs) (hRN hs')]
    have hw : s⁻¹ * s' ∈ rOf T M := (rOf T M).mul_mem ((rOf T M).inv_mem hs) hs'
    constructor
    · intro h
      have : s⁻¹ * s' ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) ⊓ rOf T M := ⟨h, hw⟩
      rwa [hRC] at this
    · intro h
      exact Subgroup.mem_centralizer_iff.mpr fun a ha => hcomm a ha _ h
  have hcard := ncard_image_mul_card hAR (cmat z a r r1) hEq
  rw [c.card_Ac hrW hrV hr2, card_rOf c] at hcard
  have hX : ((cmat z a r r1) '' (rOf T M : Set G)).ncard = 4 := by omega
  set X := (cmat z a r r1) '' (rOf T M : Set G) with hXdef
  have hI4 : I4 ∈ X := ⟨1, (rOf T M).one_mem, hB.cmat_one⟩
  obtain ⟨R1, hR1X, hR1⟩ : ∃ R1 ∈ X, R1 ≠ I4 := by
    by_contra hh
    push Not at hh
    have h1 : X ⊆ {I4} := fun P hP => hh P hP
    have h2 := Set.ncard_le_ncard h1 (Set.finite_singleton _)
    rw [Set.ncard_singleton] at h2
    omega
  obtain ⟨R2, hR2X, hR2, hR21⟩ : ∃ R2 ∈ X, R2 ≠ I4 ∧ R2 ≠ R1 := by
    by_contra hh
    push Not at hh
    have h1 : X ⊆ {I4, R1} := fun P hP => by
      by_cases h : P = I4
      · exact Or.inl h
      · exact Or.inr (hh P hP h)
    have h2 := Set.ncard_le_ncard h1 (Set.toFinite _)
    have h3 : ({I4, R1} : Set Mat4).ncard ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)
    omega
  obtain ⟨r', hr'R, hr'⟩ := hR1X
  obtain ⟨r'', hr''R, hr''⟩ := hR2X
  have hm1 : IsRMat R1 := hr' ▸ hS.isRMat_cmat htT htRQ hr'R
  have hm2 : IsRMat R2 := hr'' ▸ hS.isRMat_cmat htT htRQ hr''R
  have hd := IsRMat.mm_distinct hm1 hm2 hR1 hR2 (fun h => hR21 h.symm)
  have hprod : mm R1 R2 = cmat z a r r1 (r'' * r') := by
    rw [← hr', ← hr'']
    exact (hB.cmat_mul (hRN hr''R) (hRN hr'R)).symm
  have hnd : [I4, R1, R2, mm R1 R2].Nodup := by
    refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr
      ⟨?_, List.nodup_singleton _⟩⟩⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hR1.symm, hR2.symm, hd.1.symm⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun h => hR21 h.symm, hd.2.1.symm⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact hd.2.2.symm
  have hsub : (↑([I4, R1, R2, mm R1 R2].toFinset) : Set Mat4) ⊆ X := by
    intro P hP
    have hP' : P ∈ [I4, R1, R2, mm R1 R2] := List.mem_toFinset.mp (Finset.mem_coe.mp hP)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hP'
    rcases hP' with rfl | rfl | rfl | rfl
    · exact hI4
    · exact ⟨r', hr'R, hr'⟩
    · exact ⟨r'', hr''R, hr''⟩
    · exact ⟨r'' * r', (rOf T M).mul_mem hr''R hr'R, hprod.symm⟩
  have hcardS : (↑([I4, R1, R2, mm R1 R2].toFinset) : Set Mat4).ncard = 4 := by
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]; rfl
  have hEqX := Set.eq_of_subset_of_ncard_le hsub (by rw [hcardS, hX]) (Set.toFinite _)
  have hset : ∀ P, P ∈ [I4, R1, R2, mm R1 R2] ↔ P ∈ X := by
    intro P
    have := Set.ext_iff.mp hEqX P
    simpa using this
  refine ⟨R1, R2, hm1, hm2, ⟨hR1, hR2, fun h => hR21 h.symm, ?_, ?_⟩, ?_⟩
  · intro P hP
    obtain ⟨ρ', hρ'R, hρ'⟩ := (hset P).mp hP
    have hxρ : x * ρ' * x⁻¹ ∈ rOf T M :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (iTwo T M) hS.x_iTwo) ρ').mp hρ'R
    refine ⟨cmat z a r r1 (x * ρ' * x⁻¹), (hset _).mpr ⟨_, hxρ, rfl⟩, ?_⟩
    rw [← hρ', ← hS.cmat_x, ← hB.cmat_mul (c.iTwo_le_normalizer_Ac hrW hrV hr2 hS.x_iTwo) (hRN hρ'R),
      ← hB.cmat_mul (hRN hxρ) (c.iTwo_le_normalizer_Ac hrW hrV hr2 hS.x_iTwo)]
    congr 1
    group
  · obtain ⟨ρ', hρ'R, hnot⟩ := c.exists_not_comm_of_fpf hrW hrV hr2
      (w := x⁻¹) ((iTwo T M).inv_mem hS.x_iTwo) (fun ρ hρ h => by
        apply hS.x_fpf ρ hρ
        have h' : x⁻¹ * ρ * x = ρ := by simpa using h
        calc x * ρ * x⁻¹ = x * (x⁻¹ * ρ * x) * x⁻¹ := by rw [h']
          _ = ρ := by group)
    refine ⟨cmat z a r r1 ρ', (hset _).mpr ⟨ρ', hρ'R, rfl⟩, fun h => hnot ?_⟩
    have hxN := c.iTwo_le_normalizer_Ac hrW hrV hr2 hS.x_iTwo
    rw [← hS.cmat_x, ← hB.cmat_mul hxN (hRN hρ'R), ← hB.cmat_mul (hRN hρ'R) hxN,
      hB.cmat_eq_iff_mem_centralizer (Subgroup.mul_mem _ hxN (hRN hρ'R))
        (Subgroup.mul_mem _ (hRN hρ'R) hxN)] at h
    have h1 := centralizer_conj_mem (hRN hρ'R) h
    have e : ρ' * ((x * ρ')⁻¹ * (ρ' * x)) * ρ'⁻¹ = x⁻¹ * ρ' * x⁻¹⁻¹ * ρ'⁻¹ := by group
    rw [e] at h1
    have hq : x⁻¹ * ρ' * x⁻¹⁻¹ * ρ'⁻¹ ∈ rOf T M := by
      have hxinv : x⁻¹ ∈ Subgroup.normalizer (rOf T M : Set G) :=
        (Subgroup.normalizer _).inv_mem (le_normalizer_pCoreOf 2 (iTwo T M) hS.x_iTwo)
      exact (rOf T M).mul_mem ((Subgroup.mem_normalizer_iff.mp hxinv ρ').mp hρ'R |> fun h' => by
        simpa using h') ((rOf T M).inv_mem hρ'R)
    have : x⁻¹ * ρ' * x⁻¹⁻¹ * ρ'⁻¹ ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) ⊓ rOf T M :=
      ⟨h1, hq⟩
    rwa [hRC] at this
  · intro P
    rw [hset P]
    constructor
    · rintro ⟨ρ', hρ', rfl⟩; exact ⟨ρ', hρ', rfl⟩
    · rintro ⟨ρ', hρ', rfl⟩; exact ⟨ρ', hρ', rfl⟩

end Hyp

end S143

end CFSG.Quasithin
