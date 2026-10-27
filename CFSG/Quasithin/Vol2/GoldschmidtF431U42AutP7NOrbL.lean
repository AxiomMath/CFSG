module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7NSpan
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7Gen
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7NOrb
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP6Norm

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

@[expose] def NormL (u : PL) (gens Kl : List PL) : Prop :=
  ∀ a ∈ gens, comp u a ∈ Kl.map fun a' => comp a' u

instance (u : PL) (gens Kl : List PL) : Decidable (NormL u gens Kl) :=
  inferInstanceAs (Decidable (∀ a ∈ gens, comp u a ∈ Kl.map fun a' => comp a' u))

theorem mem_normalizer_of_normL {Kl gens : List PL}
    {h1 : idL ∈ Kl} {hmul : ∀ a ∈ Kl, ∀ b ∈ Kl, comp a b ∈ Kl} (hT : ∀ l ∈ Kl, l ∈ Thl)
    (hgens : ∀ g ∈ gens, g ∈ Kl) (hspan : ∀ l ∈ Kl, l ∈ spanL gens) {u : Ah} {ul : PL}
    (hu : RepL ul (u : P45)) (hn : NormL ul gens Kl) :
    u ∈ Subgroup.normalizer (listSub Kl h1 hmul : Set Ah) := by
  set K := listSub Kl h1 hmul with hK
  set S : Set Ah := {x | ∃ g ∈ gens, RepL g (x : P45)} with hS
  let C : Subgroup Ah := K.comap (MulAut.conj u).toMonoidHom
  have hCmem : ∀ x, x ∈ C ↔ u * x * u⁻¹ ∈ K := fun x => Iff.rfl
  have hSC : S ⊆ C := by
    rintro x ⟨g, hg, hrep⟩
    rw [SetLike.mem_coe, hCmem]
    obtain ⟨l', hl', hl'eq⟩ := List.mem_map.1 (hn g hg)
    obtain ⟨a', -, hra'⟩ := exists_That_of_mem_Thl (hT l' hl')
    have hua : u * x = a' * u := by
      apply Subtype.ext
      exact eq_of_repL (l := comp ul g) (repL_mul hu hrep) (by
        rw [← hl'eq]
        exact repL_mul hra' hu)
    have : u * x * u⁻¹ = a' := by rw [hua]; group
    rw [this]
    exact ⟨l', hl', hra'⟩
  have hclos := (Subgroup.closure_le (K := C)).2 hSC
  refine normalizer_of_conj_le fun a ha => ?_
  obtain ⟨l, hl, hra⟩ := ha
  obtain ⟨x, hx, hrepx⟩ := spanL_rep (S := S) (fun g hg => by
    obtain ⟨y, hy1, hy⟩ := exists_That_of_mem_Thl (hT g (hgens g hg))
    exact ⟨y, ⟨g, hg, hy⟩, hy⟩) l (hspan l hl)
  have hxa : x = a := Subtype.ext (eq_of_repL hrepx hra)
  rw [← hxa]
  exact hclos hx

@[expose] def CLof (P Q : List ℕ → PL) (Kl : List PL) (w : List ℕ) : List PL :=
  Kl.map fun a => comp (comp (P w) a) (Q w)

section Conj

variable {Kl : List PL} {h1 : idL ∈ Kl}
  {hmul : ∀ a ∈ Kl, ∀ b ∈ Kl, comp a b ∈ Kl} (hT : ∀ l ∈ Kl, l ∈ Thl)
  {P Q : List ℕ → PL} {w : List ℕ} (hP : P w = evalAL w) (hQ : Q w = evalAL (invAL w))

include hT hP hQ

theorem mem_conjSub_iff_CL {x : Ah} :
    x ∈ B6.conjSub (aW w) (listSub Kl h1 hmul) ↔ ∃ l ∈ CLof P Q Kl w, RepL l (x : P45) := by
  rw [B6.mem_conjSub]
  constructor
  · rintro ⟨l₀, hl₀, hrep⟩
    refine ⟨comp (comp (P w) l₀) (Q w), List.mem_map.2 ⟨l₀, hl₀, rfl⟩, ?_⟩
    have hx : x = aW w * ((aW w)⁻¹ * x * aW w) * (aW w)⁻¹ := by group
    rw [hx]
    rw [hP, hQ]
    exact repL_mul (repL_mul (repL_aW w) hrep) (repL_aW_inv w)
  · rintro ⟨l, hl, hrep⟩
    obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.1 hl
    obtain ⟨y, -, hy⟩ := exists_That_of_mem_Thl (hT l₀ hl₀)
    refine ⟨l₀, hl₀, ?_⟩
    have hxy : x = aW w * y * (aW w)⁻¹ := by
      apply Subtype.ext
      apply eq_of_repL hrep
      rw [hP, hQ]
      exact repL_mul (repL_mul (repL_aW w) hy) (repL_aW_inv w)
    have : (aW w)⁻¹ * x * aW w = y := by rw [hxy]; group
    rw [this]
    exact hy

theorem exists_elt_of_mem_CL {l : PL} (hl : l ∈ CLof P Q Kl w) :
    ∃ x ∈ B6.conjSub (aW w) (listSub Kl h1 hmul), RepL l (x : P45) := by
  obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.1 hl
  obtain ⟨y, -, hy⟩ := exists_That_of_mem_Thl (hT l₀ hl₀)
  refine ⟨aW w * y * (aW w)⁻¹, ?_, ?_⟩
  · rw [B6.mem_conjSub]
    have : (aW w)⁻¹ * (aW w * y * (aW w)⁻¹) * aW w = y := by group
    rw [this]
    exact ⟨l₀, hl₀, hy⟩
  · rw [hP, hQ]
    exact repL_mul (repL_mul (repL_aW w) hy) (repL_aW_inv w)

end Conj

theorem aW_nil : aW [] = 1 := by
  apply Subtype.ext
  apply eq_of_repL (repL_aW [])
  have : evalAL [] = idL := by decide +kernel
  rw [this]
  exact repL_one 45

theorem card_norm_of_lists
    {Kl : List PL} {h1 : idL ∈ Kl}
    {hmul : ∀ a ∈ Kl, ∀ b ∈ Kl, comp a b ∈ Kl} (hT : ∀ l ∈ Kl, l ∈ Thl) (gi : List ℕ)
    (hgi : ∀ i ∈ gi, i < Kl.length)
    (hspan : ∀ l ∈ Kl, l ∈ spanL (gi.map fun i => Kl.getD i []))
    {H : Subgroup Ah} {Γ : Set Ah} (hΓ : Subgroup.closure Γ = H) (gl : List (PL × PL))
    (hgl : ∀ s ∈ Γ, ∃ p ∈ gl, RepL p.1 (s : P45) ∧ RepL p.2 ((s⁻¹ : Ah) : P45))
    (ws : List (List ℕ)) (hnd : ws.Nodup) (P Q : List ℕ → PL)
    (hP : ∀ w ∈ ws, P w = evalAL w) (hQ : ∀ w ∈ ws, Q w = evalAL (invAL w))
    (CL : List ℕ → List PL) (hCL : ∀ w ∈ ws, CL w = CLof P Q Kl w)
    (hws : ∀ w ∈ ws, aW w ∈ H) (hid : ([] : List ℕ) ∈ ws)
    (hdist : ∀ w ∈ ws, ∀ w' ∈ ws, w ≠ w' → ∃ l ∈ CL w, l ∉ CL w')
    (T : List ℕ → PL × PL → List ℕ)
    (hclos : ∀ w ∈ ws, ∀ p ∈ gl, T w p ∈ ws ∧
      ∀ i ∈ gi, comp (comp p.1 ((CL w).getD i [])) p.2 ∈ CL (T w p)) :
    Nat.card ↥(H ⊓ Subgroup.normalizer (listSub Kl h1 hmul : Set Ah)) * ws.length =
      Nat.card ↥H := by
  set K := listSub Kl h1 hmul with hK
  have hdist' : ∀ w ∈ ws, ∀ w' ∈ ws, w ≠ w' →
      ∃ l ∈ CLof P Q Kl w, l ∉ CLof P Q Kl w' := by
    intro w hw w' hw' hne
    rw [← hCL w hw, ← hCL w' hw']
    exact hdist w hw w' hw' hne
  have hinj : ∀ w ∈ ws, ∀ w' ∈ ws, B6.conjSub (aW w) K = B6.conjSub (aW w') K → w = w' := by
    intro w hw w' hw' heq
    by_contra hne
    obtain ⟨l, hl, hl'⟩ := hdist' w hw w' hw' hne
    obtain ⟨x, hx, hrep⟩ := exists_elt_of_mem_CL (h1 := h1) (hmul := hmul) hT (hP w hw) (hQ w hw) hl
    rw [heq, mem_conjSub_iff_CL (h1 := h1) (hmul := hmul) hT (hP w' hw') (hQ w' hw')] at hx
    obtain ⟨l', hl'', hrep'⟩ := hx
    exact hl' (repL_unique hrep hrep' ▸ hl'')
  have hnd' : (ws.map fun w => B6.conjSub (aW w) K).Nodup := hnd.map_on hinj
  have h := card_normalizer_mul_of_closed_class (Γ := Γ) hΓ (K := K)
    (cl := ws.map fun w => B6.conjSub (aW w) K) hnd' ?_ ?_ ?_
  · rwa [List.length_map] at h
  · intro C hC
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hC
    exact ⟨aW w, hws w hw, rfl⟩
  · exact List.mem_map.2 ⟨[], hid, by rw [aW_nil, B6.conjSub_one]⟩
  · intro C hC s hs
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hC
    obtain ⟨p, hp, hps, hpsi⟩ := hgl s hs
    obtain ⟨hw'mem, hn⟩ := hclos w hw p hp
    set w' := T w p with hw'
    refine List.mem_map.2 ⟨w', hw'mem, ?_⟩
    have hgenK : ∀ i ∈ gi, ∃ y ∈ K, RepL (Kl.getD i []) (y : P45) := by
      intro i hi
      have hl : Kl.getD i [] ∈ Kl := by
        rw [List.getD_eq_getElem _ _ (hgi i hi)]
        exact List.getElem_mem _
      obtain ⟨y, -, hy⟩ := exists_That_of_mem_Thl (hT _ hl)
      exact ⟨y, ⟨_, hl, hy⟩, hy⟩
    set u : Ah := s * aW w with hu
    let Sg : Subgroup Ah := (B6.conjSub (aW w') K).comap (MulAut.conj u).toMonoidHom
    have hSg : ∀ y, y ∈ Sg ↔ u * y * u⁻¹ ∈ B6.conjSub (aW w') K := fun y => Iff.rfl
    have hgens : ∀ i ∈ gi, ∀ y : Ah, RepL (Kl.getD i []) (y : P45) → y ∈ Sg := by
      intro i hi y hy
      rw [hSg, mem_conjSub_iff_CL (h1 := h1) (hmul := hmul) hT (hP w' hw'mem) (hQ w' hw'mem)]
      rw [← hCL w' hw'mem]
      refine ⟨comp (comp p.1 ((CL w).getD i [])) p.2, hn i hi, ?_⟩
      have hCLi : (CL w).getD i [] = comp (comp (P w) (Kl.getD i [])) (Q w) := by
        rw [hCL w hw, CLof]
        have hi' := hgi i hi
        rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map,
          List.getD_eq_getElem _ _ hi']
      rw [hCLi, hP w hw, hQ w hw]
      have heq : u * y * u⁻¹ = s * (aW w * y * (aW w)⁻¹) * s⁻¹ := by rw [hu]; group
      rw [heq]
      exact repL_mul (repL_mul hps (repL_mul (repL_mul (repL_aW w) hy) (repL_aW_inv w))) hpsi
    have hKSg : K ≤ Sg := by
      intro a ha
      obtain ⟨l, hl, hra⟩ := ha
      obtain ⟨x, hx, hrepx⟩ := spanL_rep (S := {y : Ah | ∃ i ∈ gi, RepL (Kl.getD i []) (y : P45)})
        (fun g hg => by
          obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
          obtain ⟨y, -, hy⟩ := hgenK i hi
          exact ⟨y, ⟨i, hi, hy⟩, hy⟩) l (hspan l hl)
      have hxa : x = a := Subtype.ext (eq_of_repL hrepx hra)
      have hcl : Subgroup.closure {y : Ah | ∃ i ∈ gi, RepL (Kl.getD i []) (y : P45)} ≤ Sg := by
        rw [Subgroup.closure_le]
        rintro y ⟨i, hi, hy⟩
        exact hgens i hi y hy
      rw [← hxa]
      exact hcl hx
    have hle : B6.conjSub s (B6.conjSub (aW w) K) ≤ B6.conjSub (aW w') K := by
      intro x hx
      rw [B6.mem_conjSub, B6.mem_conjSub] at hx
      have hy : (aW w)⁻¹ * (s⁻¹ * x * s) * aW w ∈ K := by
        have : (aW w)⁻¹ * (s⁻¹ * x * s) * aW w = (aW w)⁻¹ * s⁻¹ * x * s * aW w := by group
        rw [this]
        exact hx
      have := hKSg hy
      rw [hSg] at this
      have e : u * ((aW w)⁻¹ * (s⁻¹ * x * s) * aW w) * u⁻¹ = x := by rw [hu]; group
      rwa [e] at this
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [conjSub_card, conjSub_card, conjSub_card]

end CFSG.Quasithin.H13.F431.U42Aut
