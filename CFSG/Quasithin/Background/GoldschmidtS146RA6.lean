module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelA6
import all CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelA6Enc
public import CFSG.Quasithin.Background.GoldschmidtS146RLat

public section

namespace CFSG.Quasithin.GoldS146R

open CFSG.QuasithinUnique.Borel252.A6 CFSG.QuasithinUnique CFSG.Quasithin CFSG.Open

def fpR (r : R6) : ℕ :=
  (if r.a = 0 then 1 else 0) + (if r.b = 1 then 1 else 0) + (if r.c = 2 then 1 else 0) +
    (if r.d = 3 then 1 else 0) + (if r.e = 4 then 1 else 0) + (if r.f = 5 then 1 else 0)

theorem fpR_Sa : ∀ r ∈ saL, r * r * r = 1 → r ≠ 1 → fpR r = 3 := by decide +kernel

theorem fpR_Sb : ∀ r ∈ sbL, r * r * r = 1 → r ≠ 1 → fpR r = 0 := by decide +kernel

def fpP (x : P6) : ℕ := (Finset.univ.filter fun i : Fin 6 => x i = i).card

theorem fpP_eq (x : P6) : fpP x = fpR (R6.enc x) := by
  have h : fpP x = ∑ i : Fin 6, (if x i = i then 1 else 0) := Finset.card_filter _ _
  rw [h, Fin.sum_univ_six]
  rfl

theorem fpP_conj (k x : P6) : fpP (k * x * k⁻¹) = fpP x := by
  unfold fpP
  refine Finset.card_bij (fun i _ => (k⁻¹ : P6) i) ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨-, hi⟩ := hi
    have h1 : k (x (k⁻¹ i)) = i := by simpa [Equiv.Perm.mul_apply] using hi
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have := congrArg (k⁻¹ : P6) h1
    simpa using this
  · intro a _ b _ hab
    exact Equiv.injective (k⁻¹ : P6) hab
  · intro j hj
    rw [Finset.mem_filter] at hj
    obtain ⟨-, hj⟩ := hj
    refine ⟨k j, ?_, by simp⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    simp [Equiv.Perm.mul_apply, hj]

theorem enc_cube {x : P6} (h3 : x ^ 3 = 1) : R6.enc x * R6.enc x * R6.enc x = 1 := by
  have : x * x * x = 1 := by
    have h' : x ^ 3 = x * x * x := by rw [pow_succ, pow_two]
    rw [← h']
    exact h3
  rw [← R6.enc_mul, ← R6.enc_mul, this, R6.enc_one]

theorem fpP_of_mem_Sa {x : P6} (hx : x ∈ Sa) (h3 : x ^ 3 = 1) (h1 : x ≠ 1) : fpP x = 3 := by
  rw [fpP_eq]
  refine fpR_Sa _ ((mem_Sa x).mp hx) (enc_cube h3) fun h => h1 ?_
  exact R6.enc_inj (h.trans R6.enc_one.symm)

theorem fpP_of_mem_Sb {x : P6} (hx : x ∈ Sb) (h3 : x ^ 3 = 1) (h1 : x ≠ 1) : fpP x = 0 := by
  rw [fpP_eq]
  refine fpR_Sb _ ((mem_Sb x).mp hx) (enc_cube h3) fun h => h1 ?_
  exact R6.enc_inj (h.trans R6.enc_one.symm)

theorem card_Sa' : Nat.card Sa = 24 := by
  obtain ⟨-, hs, -, -, hsn, -, -, -, -, -⟩ := sizes_ok
  rw [card_of_list R6.enc_inj Sa saL hsn mem_Sa (fun r hr => (sound_Sa r hr).imp fun x hx => hx.2)]
  exact hs

theorem card_Sb' : Nat.card Sb = 24 := by
  obtain ⟨-, -, hs, -, -, hsn, -, -, -, -⟩ := sizes_ok
  rw [card_of_list R6.enc_inj Sb sbL hsn mem_Sb (fun r hr => (sound_Sb r hr).imp fun x hx => hx.2)]
  exact hs

section Six

abbrev U6' : Subgroup M6 := D0.subgroupOf A6s

theorem card_U6' : Nat.card U6' = 8 := by
  rw [card_sub D0_le_A6, card_D0]

theorem sylow_U6' : IsSylowTwoOf U6' ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h8 : Nat.card U6' = 2 ^ 3 := by rw [card_U6']; norm_num
  refine ⟨le_top, IsPGroup.of_card h8, ?_⟩
  rw [show (U6'.subgroupOf ⊤).index = U6'.index from Subgroup.relIndex_top_right U6']
  have h := Subgroup.card_mul_index U6'
  rw [h8, card_A6] at h
  omega

theorem six_cases' (W : Subgroup M6) (hW : U6' ≤ W) (hWt : W ≠ ⊤) :
    W = U6' ∨ (W.map A6s.subtype = Sa ∧ Nat.card W = 24) ∨
      (W.map A6s.subtype = Sb ∧ Nat.card W = 24) := by
  have hD : D0 ≤ W.map A6s.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le D0_le_A6]
    exact Subgroup.map_mono hW
  have hA : W.map A6s.subtype ≤ A6s := Subgroup.map_subtype_le W
  have hcard : Nat.card (W.map A6s.subtype) = Nat.card W :=
    Subgroup.card_map_of_injective A6s.subtype_injective
  rcases six_overgroups _ hD hA with h | h | h | h
  · left
    apply Subgroup.map_injective A6s.subtype_injective
    rw [h, Subgroup.map_subgroupOf_eq_of_le D0_le_A6]
  · right; left
    exact ⟨h, by rw [← hcard, h, card_Sa']⟩
  · right; right
    exact ⟨h, by rw [← hcard, h, card_Sb']⟩
  · exfalso
    apply hWt
    apply Subgroup.map_injective A6s.subtype_injective
    rw [h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

end Six

section Transport

variable {A B : Type} [Group A] [Group B]

theorem isSylowTwoOf_subgroupOf_top' [Finite A] {S H : Subgroup A} (h : IsSylowTwoOf S H) :
    IsSylowTwoOf (S.subgroupOf H) ⊤ := by
  refine ⟨le_top, h.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe h.1).symm, ?_⟩
  show ¬ 2 ∣ (S.subgroupOf H).relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  exact h.2.2

theorem isSylowTwoOf_map_equiv' [Finite A] [Finite B] (e : A ≃* B) {S : Subgroup A}
    (h : IsSylowTwoOf S ⊤) : IsSylowTwoOf (S.map e.toMonoidHom) ⊤ := by
  refine ⟨le_top, h.2.1.map _, ?_⟩
  show ¬ 2 ∣ (S.map e.toMonoidHom).relIndex ⊤
  rw [Subgroup.relIndex_top_right, Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective]
  have h1 : ¬ 2 ∣ S.relIndex ⊤ := h.2.2
  rwa [Subgroup.relIndex_top_right] at h1

end Transport

section Swap

variable {Y : Type} [Group Y] [Finite Y]

theorem a6_swap {X U P : Subgroup Y} (hA6 : IsAlt 6 ↥X) (hU : IsSylowTwoOf U X) (hPX : P ≤ X)
    (hPne : P ≠ X) (hPmax : ∀ Q : Subgroup Y, Q ≤ X → Q ≠ X → P ≤ Q → Q = P) (hUP : U ≤ P)
    {τ : Y} (hτX : τ ∈ Subgroup.normalizer (X : Set Y))
    (hτU : τ ∈ Subgroup.normalizer (U : Set Y)) (hτP : τ ∉ Subgroup.normalizer (P : Set Y)) :
    ∃ x ∈ X, x ^ 3 = 1 ∧ x ≠ 1 ∧ ∀ k ∈ X, k * x * k⁻¹ ≠ τ * x * τ⁻¹ := by
  obtain ⟨e₀⟩ := hA6
  have hU₁ : IsSylowTwoOf (U.subgroupOf X) ⊤ := isSylowTwoOf_subgroupOf_top' hU
  have hU₂ := isSylowTwoOf_map_equiv' e₀ hU₁
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf_top hU₂ sylow_U6'
  let e : ↥X ≃* M6 := e₀.trans (MulAut.conj g)
  have heU : (U.subgroupOf X).map e.toMonoidHom = U6' := by
    rw [hg, Subgroup.map_map]
    rfl
  have hUX : U ≤ X := hU.1
  let Q₀ : Subgroup Y := P.map (MulAut.conj τ).toMonoidHom
  have hQX : Q₀ ≤ X := by
    rintro _ ⟨z, hz, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hτX z).mp (hPX hz)
  have hUQ : U ≤ Q₀ := by
    intro u hu
    have hinv : τ⁻¹ ∈ Subgroup.normalizer (U : Set Y) :=
      (Subgroup.normalizer (U : Set Y)).inv_mem hτU
    have h1 : τ⁻¹ * u * τ⁻¹⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hinv u).mp hu
    refine ⟨τ⁻¹ * u * τ⁻¹⁻¹, hUP h1, ?_⟩
    show (MulAut.conj τ) (τ⁻¹ * u * τ⁻¹⁻¹) = u
    rw [MulAut.conj_apply]
    group
  have hQP : Q₀ ≠ P := fun h => hτP (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
  have hcardQ : Nat.card ↥Q₀ = Nat.card ↥P :=
    Subgroup.card_map_of_injective (MulAut.conj τ).injective
  have hQtop : Q₀ ≠ X := by
    intro h
    apply hPne
    refine Subgroup.eq_of_le_of_card_ge hPX ?_
    rw [← h, hcardQ]
  have hUP₁ : U.subgroupOf X ≤ P.subgroupOf X := fun x hx => hUP hx
  have hUQ₁ : U.subgroupOf X ≤ Q₀.subgroupOf X := fun x hx => hUQ hx
  have hP₁top : P.subgroupOf X ≠ ⊤ := by
    intro h
    apply hPne
    refine le_antisymm hPX (fun x hx => ?_)
    have : (⟨x, hx⟩ : ↥X) ∈ P.subgroupOf X := by rw [h]; trivial
    exact this
  have hQ₁top : Q₀.subgroupOf X ≠ ⊤ := by
    intro h
    apply hQtop
    refine le_antisymm hQX (fun x hx => ?_)
    have : (⟨x, hx⟩ : ↥X) ∈ Q₀.subgroupOf X := by rw [h]; trivial
    exact this
  have hmaptop : ∀ W : Subgroup ↥X, W ≠ ⊤ → W.map e.toMonoidHom ≠ ⊤ := by
    intro W hW h
    apply hW
    have h1 := Subgroup.comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective W
    rw [h, Subgroup.comap_top] at h1
    exact h1.symm
  have hWP : U6' ≤ (P.subgroupOf X).map e.toMonoidHom := by
    rw [← heU]
    exact Subgroup.map_mono hUP₁
  have hWQ : U6' ≤ (Q₀.subgroupOf X).map e.toMonoidHom := by
    rw [← heU]
    exact Subgroup.map_mono hUQ₁
  have hcP := six_cases' _ hWP (hmaptop _ hP₁top)
  have hcQ := six_cases' _ hWQ (hmaptop _ hQ₁top)
  have hXcard : Nat.card ↥X = 360 := (Nat.card_congr e.toEquiv).trans card_A6
  have hUcard : Nat.card ↥U = 8 := by
    have h1 : Nat.card ↥(U.subgroupOf X) = Nat.card ↥U :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUX).toEquiv
    have h2 : Nat.card ↥((U.subgroupOf X).map e.toMonoidHom) = Nat.card ↥(U.subgroupOf X) :=
      Subgroup.card_map_of_injective e.injective
    rw [← h1, ← h2, heU, card_U6']
  have hPnotD : (P.subgroupOf X).map e.toMonoidHom ≠ U6' := by
    intro hD
    have hP₁U : P.subgroupOf X = U.subgroupOf X := by
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      rw [hD, heU]
    have hPU : P ≤ U := fun z hz => by
      have : (⟨z, hPX hz⟩ : ↥X) ∈ P.subgroupOf X := hz
      rw [hP₁U] at this
      exact this
    let Z₁ : Subgroup ↥X := (Sa.subgroupOf A6s).map e.symm.toMonoidHom
    let Z : Subgroup Y := Z₁.map X.subtype
    have hZ₁card : Nat.card ↥Z₁ = 24 := by
      rw [Subgroup.card_map_of_injective e.symm.injective, card_sub Sa_le_A6, card_Sa']
    have hZcard : Nat.card ↥Z = 24 := by
      rw [Subgroup.card_map_of_injective X.subtype_injective]
      exact hZ₁card
    have hZX : Z ≤ X := Subgroup.map_subtype_le _
    have hZne : Z ≠ X := by
      intro h
      have : Nat.card ↥Z = Nat.card ↥X := by rw [h]
      omega
    have hUZ : U ≤ Z := by
      intro u hu
      have hw : (⟨u, hUX hu⟩ : ↥X) ∈ U.subgroupOf X := hu
      have hew : e ⟨u, hUX hu⟩ ∈ U6' := by
        rw [← heU]
        exact Subgroup.mem_map_of_mem _ hw
      have hSa6 : e ⟨u, hUX hu⟩ ∈ Sa.subgroupOf A6s := by
        have : U6' ≤ Sa.subgroupOf A6s := fun a ha => D0_le_Sa ha
        exact this hew
      exact ⟨⟨u, hUX hu⟩, ⟨e ⟨u, hUX hu⟩, hSa6, by simp⟩, rfl⟩
    have hZP : Z = P := hPmax Z hZX hZne (hPU.trans hUZ)
    have hPcard : Nat.card ↥P ≤ Nat.card ↥U := Subgroup.card_le_of_le hPU
    rw [← hZP, hZcard] at hPcard
    omega
  have hcardmap : ∀ W : Subgroup ↥X, Nat.card ↥(W.map e.toMonoidHom) = Nat.card ↥W :=
    fun W => Subgroup.card_map_of_injective e.injective
  have hPcard : Nat.card ↥(P.subgroupOf X) = Nat.card ↥P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPX).toEquiv
  have hQcard : Nat.card ↥(Q₀.subgroupOf X) = Nat.card ↥Q₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQX).toEquiv
  have hP24 : Nat.card ↥P = 24 := by
    rcases hcP with h | ⟨-, h⟩ | ⟨-, h⟩
    · exact absurd h hPnotD
    · rw [← hPcard, ← hcardmap]; exact h
    · rw [← hPcard, ← hcardmap]; exact h
  have hQnotD : (Q₀.subgroupOf X).map e.toMonoidHom ≠ U6' := by
    intro hD
    have : Nat.card ↥(Q₀.subgroupOf X) = 8 := by
      rw [← hcardmap, hD, card_U6']
    rw [hQcard, hcardQ, hP24] at this
    omega
  set IP : Subgroup P6 := ((P.subgroupOf X).map e.toMonoidHom).map A6s.subtype with hIP
  set IQ : Subgroup P6 := ((Q₀.subgroupOf X).map e.toMonoidHom).map A6s.subtype with hIQ
  have hIP' : IP = Sa ∨ IP = Sb := by
    rcases hcP with h | ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h hPnotD
    · exact Or.inl h
    · exact Or.inr h
  have hIQ' : IQ = Sa ∨ IQ = Sb := by
    rcases hcQ with h | ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h hQnotD
    · exact Or.inl h
    · exact Or.inr h
  have hIPQ : IP ≠ IQ := by
    intro h
    apply hQP
    have h1 : (P.subgroupOf X).map e.toMonoidHom = (Q₀.subgroupOf X).map e.toMonoidHom :=
      Subgroup.map_injective A6s.subtype_injective h
    have h2 : P.subgroupOf X = Q₀.subgroupOf X := Subgroup.map_injective (f := e.toMonoidHom)
      e.injective h1
    have h3 : (P.subgroupOf X).map X.subtype = (Q₀.subgroupOf X).map X.subtype := by rw [h2]
    rw [Subgroup.map_subgroupOf_eq_of_le hPX, Subgroup.map_subgroupOf_eq_of_le hQX] at h3
    exact h3.symm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨gP, hgP⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) 3 (by rw [hP24]; norm_num)
  have hxP : (gP : Y) ∈ P := gP.2
  have hx3 : (gP : Y) ^ 3 = 1 := by
    have h1 : gP ^ 3 = 1 := by
      rw [← hgP]
      exact pow_orderOf_eq_one gP
    exact congrArg Subtype.val h1
  have hx1 : (gP : Y) ≠ 1 := by
    intro h
    have : gP = 1 := Subtype.ext h
    rw [this, orderOf_one] at hgP
    omega
  refine ⟨(gP : Y), hPX hxP, hx3, hx1, fun k hk hkx => ?_⟩
  have hyQ : τ * (gP : Y) * τ⁻¹ ∈ Q₀ := ⟨(gP : Y), hxP, by simp [MulAut.conj_apply]⟩
  have hyX : τ * (gP : Y) * τ⁻¹ ∈ X := hQX hyQ
  have hy3 : (τ * (gP : Y) * τ⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hx3]
    group
  have hy1 : τ * (gP : Y) * τ⁻¹ ≠ 1 := by
    intro h
    apply hx1
    calc (gP : Y) = τ⁻¹ * (τ * (gP : Y) * τ⁻¹) * τ := by group
      _ = 1 := by rw [h]; group
  have key3 : ∀ z : ↥X, (z : Y) ^ 3 = 1 → ((e z : M6) : P6) ^ 3 = 1 := by
    intro z hz
    have h1 : z ^ 3 = 1 := Subtype.ext (by simpa using hz)
    have h2 : (e z) ^ 3 = 1 := by rw [← map_pow, h1, map_one]
    have h3 := congrArg Subtype.val h2
    simpa using h3
  have key1 : ∀ z : ↥X, (z : Y) ≠ 1 → ((e z : M6) : P6) ≠ 1 := by
    intro z hz h
    apply hz
    have h1 : e z = 1 := Subtype.ext h
    have h2 : z = 1 := e.injective (by rw [h1, map_one])
    rw [h2]
    rfl
  let xX : ↥X := ⟨(gP : Y), hPX hxP⟩
  let yX : ↥X := ⟨τ * (gP : Y) * τ⁻¹, hyX⟩
  let kX : ↥X := ⟨k, hk⟩
  have hconj : kX * xX * kX⁻¹ = yX := Subtype.ext (by simpa using hkx)
  have hxXP : xX ∈ P.subgroupOf X := hxP
  have hyXQ : yX ∈ Q₀.subgroupOf X := hyQ
  have hb : ((e kX : M6) : P6) * ((e xX : M6) : P6) * ((e kX : M6) : P6)⁻¹ =
      ((e yX : M6) : P6) := by
    have := congrArg (fun z : ↥X => ((e z : M6) : P6)) hconj
    simpa [map_mul, map_inv] using this
  have hfp : fpP ((e yX : M6) : P6) = fpP ((e xX : M6) : P6) := by
    rw [← hb]
    exact fpP_conj _ _
  have ha_mem : ((e xX : M6) : P6) ∈ IP := ⟨e xX, ⟨xX, hxXP, rfl⟩, rfl⟩
  have hb_mem : ((e yX : M6) : P6) ∈ IQ := ⟨e yX, ⟨yX, hyXQ, rfl⟩, rfl⟩
  have ha3 : ((e xX : M6) : P6) ^ 3 = 1 := key3 xX hx3
  have ha1 : ((e xX : M6) : P6) ≠ 1 := key1 xX hx1
  have hb3 : ((e yX : M6) : P6) ^ 3 = 1 := key3 yX hy3
  have hb1 : ((e yX : M6) : P6) ≠ 1 := key1 yX hy1
  rcases hIP' with hP | hP <;> rcases hIQ' with hQ | hQ
  · exact hIPQ (hP.trans hQ.symm)
  · have h1 := fpP_of_mem_Sa (hP ▸ ha_mem) ha3 ha1
    have h2 := fpP_of_mem_Sb (hQ ▸ hb_mem) hb3 hb1
    omega
  · have h1 := fpP_of_mem_Sb (hP ▸ ha_mem) ha3 ha1
    have h2 := fpP_of_mem_Sa (hQ ▸ hb_mem) hb3 hb1
    omega
  · exact hIPQ (hP.trans hQ.symm)

end Swap

end CFSG.Quasithin.GoldS146R
