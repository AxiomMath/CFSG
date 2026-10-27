module

public import CFSG.Quasithin.Vol2.Ch10SecV1SE

public noncomputable section

namespace CFSG.Quasithin.Vol2.Ch10.V1C.A319

open CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {H : Type} [Group H] {L : Subgroup H} {K : Type} [Field K]

@[expose] def invSubs (L V : Subgroup H) (N : ℕ) : Set (Subgroup H) :=
  {J | J ≤ V ∧ L ≤ Subgroup.normalizer (J : Set H) ∧ Nat.card J = N}

theorem map_conj_mem {V : Subgroup H} {N : ℕ} {g : H}
    (hgV : g ∈ Subgroup.normalizer (V : Set H)) (hgL : g ∈ Subgroup.normalizer (L : Set H))
    {J : Subgroup H} (hJ : J ∈ invSubs L V N) :
    J.map (MulAut.conj g).toMonoidHom ∈ invSubs L V N := by
  obtain ⟨hJV, hLJ, hcard⟩ := hJ
  refine ⟨?_, le_normalizer_of_conj_mem fun l hl x hx => ?_, ?_⟩
  · rintro _ ⟨j, hj, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hgV j).mp (hJV hj)
  · obtain ⟨j, hj, rfl⟩ := hx
    have hl' : g⁻¹ * l * g ∈ L := NatCoord.conj_mem hgL ⟨l, hl⟩
    refine ⟨(g⁻¹ * l * g) * j * (g⁻¹ * l * g)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hLJ hl') j).mp hj, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]

theorem map_conj_map_conj (J : Subgroup H) (g g' : H) :
    (J.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g').toMonoidHom =
      J.map (MulAut.conj (g' * g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem map_conj_one (J : Subgroup H) : J.map (MulAut.conj (1 : H)).toMonoidHom = J := by
  ext x
  simp

@[expose] def conjPerm {V : Subgroup H} (N : ℕ) {h : H} (hhV : h ∈ Subgroup.normalizer (V : Set H))
    (hhL : h ∈ Subgroup.normalizer (L : Set H)) : Equiv.Perm ↥(invSubs L V N) where
  toFun J := ⟨_, map_conj_mem hhV hhL J.2⟩
  invFun J := ⟨_, map_conj_mem (Subgroup.inv_mem _ hhV) (Subgroup.inv_mem _ hhL) J.2⟩
  left_inv J := Subtype.ext (by
    show (J.1.map _).map _ = J.1
    rw [map_conj_map_conj, inv_mul_cancel, map_conj_one])
  right_inv J := Subtype.ext (by
    show (J.1.map _).map _ = J.1
    rw [map_conj_map_conj, mul_inv_cancel, map_conj_one])

theorem conjPerm_pow {V : Subgroup H} (N : ℕ) {h : H} (hhV : h ∈ Subgroup.normalizer (V : Set H))
    (hhL : h ∈ Subgroup.normalizer (L : Set H)) (n : ℕ) (J : ↥(invSubs L V N)) :
    (((conjPerm N hhV hhL) ^ n) J).1 = J.1.map (MulAut.conj (h ^ n)).toMonoidHom := by
  induction n with
  | zero => simp only [pow_zero, Equiv.Perm.one_apply, map_conj_one]
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    show ((((conjPerm N hhV hhL) ^ n) J).1).map _ = _
    rw [ih, map_conj_map_conj, ← pow_succ']

namespace SumTwo

variable {φ : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(StatedSL 3 K)} {V W₀ W₁ : Subgroup H}

theorem graph_ne (S : SumTwo φ V W₀ W₁) (a : K) : S.graph a ≠ W₁ := by
  intro h
  obtain ⟨w, hw⟩ : ∃ w : ↥W₀, w ≠ 1 := by
    refine ⟨S.c₀.θ.symm (Multiplicative.ofAdd (Pi.single 0 1)), fun h1 => ?_⟩
    have h2 := congrArg (fun x => Multiplicative.toAdd (S.c₀.θ x)) h1
    simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd, map_one, toAdd_one] at h2
    simpa using congrFun h2 0
  have hm : S.grHom a w ∈ W₁ := h.le ⟨w, rfl⟩
  have hw1 : (w : H) ∈ W₁ := by
    have e : (w : H) = S.grHom a w * (S.gr a w : H)⁻¹ := by
      show (w : H) = (w : H) * S.gr a w * (S.gr a w : H)⁻¹
      group
    rw [e]
    exact W₁.mul_mem hm (W₁.inv_mem (S.gr a w).2)
  exact hw (Subtype.ext (S.eq_one_of_mem w.2 hw1))

theorem graph_injective (S : SumTwo φ V W₀ W₁) : Function.Injective S.graph := by
  intro a b hab
  set w := S.c₀.θ.symm (Multiplicative.ofAdd (Pi.single 0 1)) with hw
  have hm : (w : H) * S.gr a w ∈ S.graph b := hab ▸ ⟨w, rfl⟩
  have h1 := congrArg (fun x => Multiplicative.toAdd (S.c₁.θ x))
    (Subtype.ext (S.eq_gr_of_mem w (S.gr a w).2 hm) : S.gr a w = S.gr b w)
  simp only [gr_apply, toAdd_ofAdd, hw, MulEquiv.apply_symm_apply] at h1
  simpa using congrFun h1 0

theorem card_invSubs [Finite H] [Finite K] (S : SumTwo φ V W₀ W₁) :
    Nat.card ↥(invSubs L V (Nat.card W₀)) = Nat.card K + 1 := by
  let f : Option K → ↥(invSubs L V (Nat.card W₀)) := fun o => match o with
    | none => ⟨W₁, S.le₁, S.c₁.le_normalizer, S.card_eq.symm⟩
    | some a => ⟨S.graph a, S.graph_le a, S.le_normalizer_graph a, S.card_graph a⟩
  have hf : Function.Bijective f := by
    refine ⟨fun o o' h => ?_, fun J => ?_⟩
    · have h' := congrArg Subtype.val h
      rcases o with _ | a <;> rcases o' with _ | b
      · rfl
      · exact ((S.graph_ne b) h'.symm).elim
      · exact ((S.graph_ne a) h').elim
      · exact congrArg some (S.graph_injective h')
    · rcases S.eq_or_eq_graph J.2.1 J.2.2.1 J.2.2.2 with h | ⟨a, ha⟩
      · exact ⟨none, Subtype.ext h.symm⟩
      · exact ⟨some a, Subtype.ext ha.symm⟩
  have := Fintype.ofFinite K
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_option,
    Nat.card_eq_fintype_card]

end SumTwo

end CFSG.Quasithin.Vol2.Ch10.V1C.A319
