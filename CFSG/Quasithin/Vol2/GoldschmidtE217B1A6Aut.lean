module

public import Certificates.Certificate4217
public import CFSG.GH74.KGroups.A6
public import CFSG.GH74.KGroups.Generic2
public import CFSG.GH74.AS16.E2.OuterModel
public import CFSG.Quasithin.Vol2.GoldschmidtE217L2Dih

public section

namespace CFSG.Quasithin

open CFSG.GH74.KGroups CFSG.GH74.AS16.E2 CFSG.Quasithin.E217A6 E217R3

namespace E217R4

theorem a6Check_sound {LP LA : List (Equiv.Perm (Fin 10))} (h : a6Check LP LA = true) :
    sList.Nodup ∧ sList.length = 8 ∧
    (∀ x ∈ sList, x ∈ LP ∧ x⁻¹ ∈ sList ∧ ∀ y ∈ sList, x * y ∈ sList) ∧
    (∀ g ∈ LP, (∀ s ∈ sList, g * s * g⁻¹ ∈ sList) → g ∈ sList) ∧
    z0 ∈ sList ∧ z0 * z0 = 1 ∧
    p1List.Nodup ∧ p1List.length = 24 ∧
    (∀ x ∈ p1List, x ∈ LP ∧ x⁻¹ ∈ p1List ∧ ∀ y ∈ p1List, x * y ∈ p1List) ∧
    (∀ s ∈ sList, s ∈ p1List) ∧ (∀ x ∈ LP, x ∈ LA) ∧
    (∀ a ∈ LA, a * a = 1 → (∀ s ∈ sList, a * s = s * a) → a = 1 ∨ a = z0 ∨
      ∀ b ∈ LA, (∀ s ∈ sList, b * s * b⁻¹ ∈ sList) → a * b = b * a →
        ∀ p ∈ p1List, b * p * b⁻¹ ∈ p1List) ∧
    (∀ u ∈ LP, u * u = 1 → u ≠ 1 → ∃ g ∈ LP, (u * (g * u * g⁻¹)) ^ 5 = 1 ∧
      (u * (g * u * g⁻¹)) ^ 3 ≠ 1) := by
  simp only [a6Check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  refine ⟨h1, h2, fun x hx => ?_, fun g hg hs => ?_, h5, h6, h7, h8, fun x hx => ?_, h10, h11,
    fun a ha ha2 hac => ?_, fun u hu hu2 hu1 => ?_⟩
  · obtain ⟨⟨a, b⟩, c⟩ := h3 x hx
    exact ⟨a, b, c⟩
  · rcases h4 g hg with h | h
    · exact absurd hs h
    · exact h
  · obtain ⟨⟨a, b⟩, c⟩ := h9 x hx
    exact ⟨a, b, c⟩
  · rcases h12 a ha with ((h | h) | h) | h
    · exact absurd ⟨ha2, hac⟩ h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr fun b hb hn hc => ?_)
      rcases h b hb with (h' | h') | h'
      · exact absurd hn h'
      · exact absurd hc h'
      · exact h'
  · rcases h13 u hu with h | ⟨g, hg, h5, h3⟩
    · exact absurd ⟨hu2, hu1⟩ h
    · exact ⟨g, hg, h5, h3⟩

theorem a6_check_ok :
    a6Check (elemsT A6.QP) (elemsT A6.QA) = true :=
  Certificates.certificate4217

@[expose] def listSubgroup10 (l : List (Equiv.Perm (Fin 10))) (hne : 0 < l.length)
    (hcl : ∀ x ∈ l, x⁻¹ ∈ l ∧ ∀ y ∈ l, x * y ∈ l) : Subgroup (Equiv.Perm (Fin 10)) where
  carrier := {x | x ∈ l}
  mul_mem' := fun {x y} hx hy => (hcl x hx).2 y hy
  one_mem' := by
    obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos hne
    simpa using (hcl x hx).2 x⁻¹ (hcl x hx).1
  inv_mem' := fun {x} hx => (hcl x hx).1

theorem mem_listSubgroup10 {l : List (Equiv.Perm (Fin 10))} {hne : 0 < l.length}
    {hcl : ∀ x ∈ l, x⁻¹ ∈ l ∧ ∀ y ∈ l, x * y ∈ l} {x : Equiv.Perm (Fin 10)} :
    x ∈ listSubgroup10 l hne hcl ↔ x ∈ l := Iff.rfl

theorem card_listSubgroup10 {l : List (Equiv.Perm (Fin 10))} {hne : 0 < l.length}
    {hcl : ∀ x ∈ l, x⁻¹ ∈ l ∧ ∀ y ∈ l, x * y ∈ l} (hnd : l.Nodup) :
    Nat.card (listSubgroup10 l hne hcl) = l.length := by
  have h1 : ((listSubgroup10 l hne hcl : Subgroup (Equiv.Perm (Fin 10))) :
      Set (Equiv.Perm (Fin 10))) = ↑l.toFinset := by
    ext x
    simp [mem_listSubgroup10]
  show Nat.card ((listSubgroup10 l hne hcl : Subgroup (Equiv.Perm (Fin 10))) :
    Set (Equiv.Perm (Fin 10))) = l.length
  rw [h1, Nat.card_coe_set_eq, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]

theorem a6_table
    {K : Type} [Group K] (hK : Nonempty (K ≃* alternatingGroup (Fin 6)))
    (S : Subgroup K) (hS : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index) :
    ∃ P₁ : Subgroup K, S ≤ P₁ ∧ Nat.card P₁ = 24 ∧
      (∀ g : K, (∀ s ∈ S, g * s * g⁻¹ ∈ S) → g ∈ S) ∧
      (∀ α : MulAut K, α ^ 2 = 1 → (∀ s ∈ S, α s = s) →
        (∃ z ∈ S, z * z = 1 ∧ α = MulAut.conj z) ∨
        ∀ β : MulAut K, (∀ s ∈ S, β s ∈ S) → β * α = α * β → ∀ p ∈ P₁, β p ∈ P₁) ∧
      ∀ u : K, u * u = 1 → u ≠ 1 → ¬ OddCube u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e0⟩ := A6.equiv_of_alt6 hK
  have hQ := A6.QP_ok
  have hA := A6.QA_ok
  obtain ⟨M, hMP, hMA⟩ := A6.autModel e0
  obtain ⟨hs_nd, hs_len, hs_cl, hs_norm, hz0, hz02, hp_nd, hp_len, hp_cl, hsp, hPA, htable,
    hodd⟩ := a6Check_sound a6_check_ok
  have : Finite K := Finite.of_equiv _ e0.symm.toEquiv
  let S0 := listSubgroup10 sList (by rw [hs_len]; norm_num)
    (fun x hx => ⟨(hs_cl x hx).2.1, (hs_cl x hx).2.2⟩)
  let P1 := listSubgroup10 p1List (by rw [hp_len]; norm_num)
    (fun x hx => ⟨(hp_cl x hx).2.1, (hp_cl x hx).2.2⟩)
  have hmemP : ∀ y ∈ elemsT A6.QP, y ∈ M.P := fun y hy => by
    rw [hMP]
    exact (mem_elemsT A6.QP hQ y).1 hy
  have hmemA : ∀ y ∈ M.A, y ∈ elemsT A6.QA := fun y hy => by
    rw [hMA] at hy
    exact (mem_elemsT A6.QA hA y).2 hy
  have hSP : S0 ≤ M.P := fun x hx => hmemP x (hs_cl x hx).1
  have hcardS : Nat.card S0 = 2 ^ 3 := by
    rw [card_listSubgroup10 hs_nd, hs_len]
    norm_num
  have hcardK : Nat.card K = 2 ^ 3 * 45 := by
    rw [Nat.card_congr e0.toEquiv, card_group A6.QP hQ, A6.QP_valid.2]
    norm_num
  obtain ⟨e', he'⟩ := exists_iso_of_sylow M.P M.e S0 hSP hcardS hcardK (by decide)
    (hS.toSylow hSi)
  have he'S : ∀ k : K, k ∈ S ↔ ((e' k : M.P) : Equiv.Perm (Fin 10)) ∈ sList := fun k =>
    show k ∈ S ↔ ((e' k : M.P) : Equiv.Perm (Fin 10)) ∈ S0 by simpa using he' k
  have hsurj : ∀ y ∈ M.P, ∃ k : K, ((e' k : M.P) : Equiv.Perm (Fin 10)) = y := fun y hy =>
    ⟨e'.symm ⟨y, hy⟩, by simp⟩
  have hLP : ∀ k : K, ((e' k : M.P) : Equiv.Perm (Fin 10)) ∈ elemsT A6.QP := fun k => by
    rw [mem_elemsT A6.QP hQ, ← hMP]
    exact (e' k).2
  let M' := AM.twist M e'
  have hspec : ∀ (φ : MulAut K) (x : K), ((e' (φ x) : M.P) : Equiv.Perm (Fin 10)) =
      ((M'.Φ φ : M.A) : Equiv.Perm (Fin 10)) * ((e' x : M.P) : Equiv.Perm (Fin 10)) *
        ((M'.Φ φ : M.A) : Equiv.Perm (Fin 10))⁻¹ := fun φ x => M'.spec φ x
  have hLA : ∀ φ : MulAut K, ((M'.Φ φ : M.A) : Equiv.Perm (Fin 10)) ∈ elemsT A6.QA :=
    fun φ => hmemA _ (M'.Φ φ).2
  have hcoe : ∀ x y : K, ((e' (x * y) : M.P) : Equiv.Perm (Fin 10)) =
      ((e' x : M.P) : Equiv.Perm (Fin 10)) * ((e' y : M.P) : Equiv.Perm (Fin 10)) :=
    fun x y => by rw [map_mul, Subgroup.coe_mul]
  have hcoe1 : ((e' 1 : M.P) : Equiv.Perm (Fin 10)) = 1 := by rw [map_one, Subgroup.coe_one]
  have hcoeinv : ∀ x : K, ((e' x⁻¹ : M.P) : Equiv.Perm (Fin 10)) =
      ((e' x : M.P) : Equiv.Perm (Fin 10))⁻¹ := fun x => by rw [map_inv, Subgroup.coe_inv]
  have hcoepow : ∀ (x : K) (n : ℕ), ((e' (x ^ n) : M.P) : Equiv.Perm (Fin 10)) =
      ((e' x : M.P) : Equiv.Perm (Fin 10)) ^ n := fun x n => by
    rw [map_pow, Subgroup.coe_pow]
  have hinj : ∀ x y : K, ((e' x : M.P) : Equiv.Perm (Fin 10)) =
      ((e' y : M.P) : Equiv.Perm (Fin 10)) → x = y := fun x y h =>
    e'.injective (Subtype.ext h)
  let P₁ : Subgroup K := P1.comap (M.P.subtype.comp e'.toMonoidHom)
  have hP₁ : ∀ k : K, k ∈ P₁ ↔ ((e' k : M.P) : Equiv.Perm (Fin 10)) ∈ p1List := fun k => Iff.rfl
  refine ⟨P₁, fun k hk => (hP₁ k).2 (hsp _ ((he'S k).1 hk)), ?_, ?_, ?_, ?_⟩
  · have hle : P1 ≤ (M.P.subtype.comp e'.toMonoidHom).range := fun y hy => by
      obtain ⟨k, hk⟩ := hsurj y (hmemP y (hp_cl y hy).1)
      exact ⟨k, hk⟩
    have hinj' : Function.Injective (M.P.subtype.comp e'.toMonoidHom) :=
      Subtype.val_injective.comp e'.injective
    rw [← Subgroup.card_map_of_injective hinj', Subgroup.map_comap_eq, inf_eq_right.2 hle,
      card_listSubgroup10 hp_nd, hp_len]
  · intro g hg
    refine (he'S g).2 (hs_norm _ (hLP g) fun s0 hs0 => ?_)
    obtain ⟨k, hk⟩ := hsurj s0 (hSP hs0)
    have hkS : k ∈ S := (he'S k).2 (hk ▸ hs0)
    have := (he'S _).1 (hg k hkS)
    rwa [hcoe, hcoe, hcoeinv, hk] at this
  · intro α hα2 hαS
    set ψ : Equiv.Perm (Fin 10) := ((M'.Φ α : M.A) : Equiv.Perm (Fin 10)) with hψ
    have hαx : ∀ x : K, ((e' (α x) : M.P) : Equiv.Perm (Fin 10)) =
        ψ * ((e' x : M.P) : Equiv.Perm (Fin 10)) * ψ⁻¹ := hspec α
    have hψ2 : ψ * ψ = 1 := by
      have : M'.Φ (α ^ 2) = 1 := by rw [hα2, map_one]
      rw [pow_two, map_mul] at this
      exact congrArg Subtype.val this
    have hψc : ∀ s ∈ sList, ψ * s = s * ψ := by
      intro s hs
      obtain ⟨k, hk⟩ := hsurj s (hSP hs)
      have hkS : k ∈ S := (he'S k).2 (hk ▸ hs)
      have h1 := hαx k
      rw [hαS k hkS, hk] at h1
      calc ψ * s = (ψ * s * ψ⁻¹) * ψ := by group
        _ = s * ψ := by rw [← h1]
    rcases htable ψ (hLA α) hψ2 hψc with h1 | h1 | h1
    · left
      refine ⟨1, one_mem S, mul_one 1, ?_⟩
      ext x
      apply hinj
      rw [hαx x, h1, MulAut.conj_apply, hcoe, hcoe, hcoeinv, hcoe1]
    · left
      have hz0P : z0 ∈ M.P := hmemP z0 (hs_cl z0 hz0).1
      obtain ⟨z, hz⟩ := hsurj z0 hz0P
      have hzS : z ∈ S := (he'S z).2 (hz ▸ hz0)
      refine ⟨z, hzS, hinj _ _ (by rw [hcoe, hz, hz02, hcoe1]), ?_⟩
      ext x
      apply hinj
      rw [hαx x, h1, MulAut.conj_apply, hcoe, hcoe, hcoeinv, hz]
    · right
      intro β hβS hcomm p hp
      have hbn : ∀ s ∈ sList, ((M'.Φ β : M.A) : Equiv.Perm (Fin 10)) * s *
          ((M'.Φ β : M.A) : Equiv.Perm (Fin 10))⁻¹ ∈ sList := by
        intro s hs
        obtain ⟨k, hk⟩ := hsurj s (hSP hs)
        have hkS : k ∈ S := (he'S k).2 (hk ▸ hs)
        have := (he'S _).1 (hβS k hkS)
        rwa [hspec β k, hk] at this
      have hbc : ψ * ((M'.Φ β : M.A) : Equiv.Perm (Fin 10)) =
          ((M'.Φ β : M.A) : Equiv.Perm (Fin 10)) * ψ := by
        have : M'.Φ (α * β) = M'.Φ (β * α) := by rw [← hcomm]
        rw [map_mul, map_mul] at this
        exact congrArg Subtype.val this
      have := h1 _ (hLA β) hbn hbc _ ((hP₁ p).1 hp)
      exact (hP₁ _).2 (by rwa [hspec β p])
  · intro u hu2 hu1 hO
    obtain ⟨g, hgP, h5, h3⟩ := hodd _ (hLP u) (by rw [← hcoe, hu2, hcoe1])
      (fun h => hu1 (hinj _ _ (by rw [h, hcoe1])))
    obtain ⟨k, hk⟩ := hsurj g (hmemP g hgP)
    have hconj : ((e' (u * (k * u * k⁻¹)) : M.P) : Equiv.Perm (Fin 10)) =
        ((e' u : M.P) : Equiv.Perm (Fin 10)) * (g * ((e' u : M.P) : Equiv.Perm (Fin 10)) *
          g⁻¹) := by
      rw [hcoe, hcoe, hcoe, hcoeinv, hk]
    have h53 := hO k 5 (by decide) (hinj _ _ (by rw [hcoepow, hconj, h5, hcoe1]))
    apply h3
    rw [← hconj, ← hcoepow, h53, hcoe1]

end E217R4

end CFSG.Quasithin
