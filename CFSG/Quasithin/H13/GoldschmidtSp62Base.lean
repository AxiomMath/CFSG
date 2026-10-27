module

public import CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two

public section

namespace CFSG.Quasithin.H13.U3

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U

theorem mem_closure_of_mem_table (l : List (List ℕ × List ℕ)) (h : l.all pairCheck = true) (n : ℕ)
    (hok : closureOK (l.map Prod.fst) (closureT (l.map Prod.fst)) n = true) {c : List ℕ}
    (hc : c ∈ closureT (l.map Prod.fst)) {u : H6} (hu : mat6 u = dec6 c) :
    u ∈ Subgroup.closure (genSet l h) := by
  simp only [closureOK, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨-, hclosed⟩, -⟩, -⟩ := hok
  have himg : mat6 '' (Subgroup.closure (genSet l h) : Set H6) =
      {y | ∃ t < (closureT (l.map Prod.fst)).size,
        dec6 ((closureT (l.map Prod.fst)).getD t []) = y} :=
    image_closure_eq dec6 one6 mul6 (l.map Prod.fst) mat6 dec6_one6 dec6_mul6
      (genSet l h) (image_genSet l h) _ hclosed
  obtain ⟨t, ht, rfl⟩ := Array.mem_iff_getElem.mp hc
  have hmem : mat6 u ∈ {y | ∃ t < (closureT (l.map Prod.fst)).size,
      dec6 ((closureT (l.map Prod.fst)).getD t []) = y} := by
    refine ⟨t, ht, ?_⟩
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ht, Option.getD_some, hu]
  rw [← himg] at hmem
  obtain ⟨g, hg, hgu⟩ := hmem
  rw [mat6_injective hgu] at hg
  exact hg

theorem card_centralizer_conj {H : Type*} [Group H] (t g : H) :
    Nat.card (Subgroup.centralizer ({g * t * g⁻¹} : Set H)) =
      Nat.card (Subgroup.centralizer ({t} : Set H)) := by
  have h : (Subgroup.centralizer ({t} : Set H)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({g * t * g⁻¹} : Set H) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      calc g * y * g⁻¹ * (g * t * g⁻¹) = g * (y * t) * g⁻¹ := by group
        _ = g * (t * y) * g⁻¹ := by rw [hy]
        _ = g * t * g⁻¹ * (g * y * g⁻¹) := by group
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, by group⟩
      calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [hx]
        _ = t * (g⁻¹ * x * g) := by group
  rw [← h]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem centralizer_tH_eq (i : Fin 4) :
    Subgroup.centralizer ({tH i} : Set H6) = XH i := by
  refine (Subgroup.eq_of_le_of_card_ge (XH_le_centralizer i) ?_).symm
  have h := CFSG.RankThree.PartTwo.Census.Carrier.G2Three.card_centralizer_mul_le (orbElt i)
    (orbElt_injective i) (orbElt_conj i)
  have hcard : orbSize i * Nat.card (XH i) = Nat.card H6 := by
    rw [card_XH, card_H6]
    fin_cases i <;> rfl
  have ho : 0 < orbSize i := by
    fin_cases i <;> decide
  rw [← hcard, mul_comm (orbSize i)] at h
  exact Nat.le_of_mul_le_mul_right h ho

theorem exists_eq_of_isConj {H : Type*} [Group H] [Finite H] {t : H} {n : ℕ} (f : Fin n → H)
    (hf : Function.Injective f) (hft : ∀ k, ∃ g, f k = g * t * g⁻¹)
    (hcard : Nat.card (Subgroup.centralizer ({t} : Set H)) * n = Nat.card H) {x : H}
    (hx : IsConj t x) : ∃ k, f k = x := by
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer (ConjAct H) t)
  rw [MulAction.index_stabilizer, ← Subgroup.nat_card_centralizer_nat_card_stabilizer,
    Nat.card_congr (ConjAct.toConjAct (G := H)).toEquiv.symm] at h1
  have hn : (MulAction.orbit (ConjAct H) t).ncard = n := by
    have hpos : 0 < Nat.card (Subgroup.centralizer ({t} : Set H)) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans hcard.symm)
  have hmem : ∀ k, f k ∈ MulAction.orbit (ConjAct H) t := fun k => by
    obtain ⟨g, hg⟩ := hft k
    exact ⟨ConjAct.toConjAct g, by
      change ConjAct.toConjAct g • t = f k
      rw [ConjAct.toConjAct_smul, hg]⟩
  have hsub : Set.range f ⊆ MulAction.orbit (ConjAct H) t := Set.range_subset_iff.mpr hmem
  have hr : (Set.range f).ncard = n := by
    rw [Set.ncard_range_of_injective hf, Nat.card_fin]
  have heq : Set.range f = MulAction.orbit (ConjAct H) t :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hn, hr]) (Set.toFinite _)
  have hxo : x ∈ MulAction.orbit (ConjAct H) t := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hx
    exact ⟨ConjAct.toConjAct c, by
      change ConjAct.toConjAct c • t = x
      rw [ConjAct.toConjAct_smul, hc]⟩
  rw [← heq] at hxo
  exact hxo

theorem exists_orbElt_of_isConj {x : H6} (hx : IsConj (tH 0) x) :
    ∃ k, orbElt 0 k = x := by
  refine exists_eq_of_isConj (orbElt 0) (orbElt_injective 0) (orbElt_conj 0) ?_ hx
  rw [centralizer_tH_eq, card_XH]
  have : Nat.card H6 = 1451520 := card_H6
  rw [this]
  rfl

theorem exists_sylow_le_of_dvd {K : Subgroup H6} (hK : 512 ∣ Nat.card K) :
    ∃ P : Sylow 2 H6, (P : Subgroup H6) ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥K) 2 (n := 9) (by simpa using hK)
  have hP : Nat.card (Q.map K.subtype) = 2 ^ 9 := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, hQ]
  have hP2 : IsPGroup 2 (Q.map K.subtype) := IsPGroup.of_card hP
  have hidx : ¬ 2 ∣ (Q.map K.subtype).index := by
    have h := Subgroup.card_mul_index (Q.map K.subtype)
    rw [hP, card_H6] at h
    have : (Q.map K.subtype).index = 2835 := by omega
    rw [this]
    decide
  exact ⟨hP2.toSylow hidx, Subgroup.map_subtype_le Q⟩

theorem card_centralizer_map_equiv {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y) (d : X) :
    Nat.card (Subgroup.centralizer ({φ d} : Set Y)) =
      Nat.card (Subgroup.centralizer ({d} : Set X)) := by
  have h : (Subgroup.centralizer ({d} : Set X)).map φ.toMonoidHom =
      Subgroup.centralizer ({φ d} : Set Y) := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← map_mul, ← map_mul, hx]
    · intro hy
      refine ⟨φ.symm y, ?_, by simp⟩
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy]
  rw [← h]
  exact Subgroup.card_map_of_injective φ.injective

theorem exists_sylow_le_centralizer_of_equiv {X Y : Type*} [Group X] [Group Y] [Finite Y]
    (φ : X ≃* Y) {c : X}
    (h : ∃ P : Sylow 2 Y, (P : Subgroup Y) ≤ Subgroup.centralizer ({φ c} : Set Y)) :
    ∃ P : Sylow 2 X, (P : Subgroup X) ≤ Subgroup.centralizer ({c} : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := h
  refine ⟨P.mapSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hP hp)
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply φ.injective
  simpa [map_mul] using h1

end CFSG.Quasithin.H13.U3
