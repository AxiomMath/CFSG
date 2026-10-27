module

public import CFSG.Quasithin.Background.Ordering
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.LieType.BorelTits.Basic
public import CFSG.GroupTheory.SolvableHallNodes

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

theorem coe_sup_of_mul_comm {A B : Subgroup G}
    (h : (B : Set G) * (A : Set G) = (A : Set G) * (B : Set G)) :
    ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * (B : Set G) := by
  let S : Subgroup G :=
    { carrier := (A : Set G) * (B : Set G)
      mul_mem' := fun {x y} hx hy => by
        obtain ⟨a, ha, b, hb, rfl⟩ := hx
        obtain ⟨a', ha', b', hb', rfl⟩ := hy
        have hba : b * a' ∈ (A : Set G) * (B : Set G) := h ▸ Set.mul_mem_mul hb ha'
        obtain ⟨a'', ha'', b'', hb'', he⟩ := hba
        have he' : a'' * b'' = b * a' := he
        refine ⟨a * a'', A.mul_mem ha ha'', b'' * b', B.mul_mem hb'' hb', ?_⟩
        calc a * a'' * (b'' * b') = a * (a'' * b'') * b' := by group
          _ = a * b * (a' * b') := by rw [he']; group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, mul_one 1⟩
      inv_mem' := fun {x} hx => by
        obtain ⟨a, ha, b, hb, rfl⟩ := hx
        have h1 : b⁻¹ * a⁻¹ ∈ (A : Set G) * (B : Set G) :=
          h ▸ Set.mul_mem_mul (B.inv_mem hb) (A.inv_mem ha)
        rw [mul_inv_rev]
        exact h1 }
  apply le_antisymm
  · have hAS : A ≤ S := fun a ha => ⟨a, ha, 1, B.one_mem, mul_one a⟩
    have hBS : B ≤ S := fun b hb => ⟨1, A.one_mem, b, hb, one_mul b⟩
    exact fun x hx => sup_le hAS hBS hx
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    exact Subgroup.mul_mem_sup ha hb

theorem commutator_sup_le_sup {Y Z N : Subgroup G}
    (hY : Y ≤ Subgroup.normalizer (N : Set G)) (hZ : Z ≤ Subgroup.normalizer (N : Set G)) :
    ⁅Y ⊔ N, Z⁆ ≤ ⁅Y, Z⁆ ⊔ N := by
  rw [Subgroup.commutator_le]
  intro w hw z hz
  have hw' : w ∈ (Y : Set G) * (N : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right Y N hY]
    exact hw
  obtain ⟨y, hy, c, hc, rfl⟩ := hw'
  have hcz : ⁅c, z⁆ ∈ N := by
    rw [commutatorElement_def]
    have : z * c⁻¹ * z⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hZ hz) _).mp (inv_mem hc)
    simpa [mul_assoc] using N.mul_mem hc this
  have hycz : y * ⁅c, z⁆ * y⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hY hy) _).mp hcz
  rw [show ⁅y * c, z⁆ = (y * ⁅c, z⁆ * y⁻¹) * ⁅y, z⁆ by simp only [commutatorElement_def]; group]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hycz)
    (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hy hz))

theorem commutator_sup_sup_le {H N : Subgroup G}
    (hH : H ≤ Subgroup.normalizer (N : Set G)) : ⁅H ⊔ N, H ⊔ N⁆ ≤ ⁅H, H⁆ ⊔ N := by
  have hHN : H ⊔ N ≤ Subgroup.normalizer (N : Set G) := sup_le hH Subgroup.le_normalizer
  calc ⁅H ⊔ N, H ⊔ N⁆ ≤ ⁅H, H ⊔ N⁆ ⊔ N := commutator_sup_le_sup hH hHN
    _ ≤ (⁅H, H⁆ ⊔ N) ⊔ N := by
        refine sup_le_sup_right ?_ N
        rw [Subgroup.commutator_comm H (H ⊔ N)]
        exact commutator_sup_le_sup hH hH
    _ = ⁅H, H⁆ ⊔ N := by rw [sup_assoc, sup_idem]

theorem le_normalizer_of_commutator_le_self {X B : Subgroup G} (h : ⁅X, B⁆ ≤ X) :
    B ≤ Subgroup.normalizer (X : Set G) := by
  have key : ∀ b ∈ B, ∀ x ∈ X, b * x * b⁻¹ ∈ X := by
    intro b hb x hx
    have h1 : ⁅x, b⁆ ∈ X := h (Subgroup.commutator_mem_commutator hx hb)
    have h2 : b * x * b⁻¹ = ⁅x, b⁆⁻¹ * x := by
      rw [commutatorElement_def]
      group
    rw [h2]
    exact X.mul_mem (X.inv_mem h1) hx
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key b hb x, fun hx => ?_⟩
  have h3 := key b⁻¹ (B.inv_mem hb) _ hx
  have h4 : b⁻¹ * (b * x * b⁻¹) * b⁻¹⁻¹ = x := by group
  rw [h4] at h3
  exact h3

theorem conjClosure_perfect {L T : Subgroup G} (hL : ⁅L, L⁆ = L) :
    ⁅conjClosure L T, conjClosure L T⁆ = conjClosure L T := by
  refine le_antisymm (A3.commutator_self_le _) (conjClosure_le fun t ht l hl => ?_)
  have hKC : L.map (MulAut.conj t).toMonoidHom ≤ conjClosure L T := by
    rintro _ ⟨l', hl', rfl⟩
    exact mem_conjClosure ht hl'
  have hKp : ⁅L.map (MulAut.conj t).toMonoidHom, L.map (MulAut.conj t).toMonoidHom⁆ =
      L.map (MulAut.conj t).toMonoidHom := by
    rw [← Subgroup.map_commutator, hL]
  have hmem : t * l * t⁻¹ ∈ L.map (MulAut.conj t).toMonoidHom := ⟨l, hl, rfl⟩
  rw [← hKp] at hmem
  exact Subgroup.commutator_mono hKC hKC hmem

theorem inf_eq_bot_of_isPGroup_two_of_odd [Finite G] {Q K : Subgroup G} (hQ : IsPGroup 2 ↥Q)
    (hK : Odd (Nat.card K)) : Q ⊓ K = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hQ
  refine disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard ?_)
  rw [hk]
  exact Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hK)

theorem exists_mul_mem_normalizer [Finite G] {Q B : Subgroup G} (hQ : IsPGroup 2 ↥Q)
    (hB : Odd (Nat.card B)) (hBQ : B ≤ Subgroup.normalizer (Q : Set G)) {m : G}
    (hmQ : m ∈ Subgroup.normalizer (Q : Set G))
    (hmB : B.map (MulAut.conj m).toMonoidHom ≤ B ⊔ Q) :
    ∃ q ∈ Q, q * m ∈ Subgroup.normalizer (B : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardBm : Nat.card (B.map (MulAut.conj m).toMonoidHom) = Nat.card B :=
    Subgroup.card_map_of_injective (MulAut.conj m).injective
  have hQB : Q ⊓ B = ⊥ := inf_eq_bot_of_isPGroup_two_of_odd hQ hB
  have hQBm : Q ⊓ B.map (MulAut.conj m).toMonoidHom = ⊥ :=
    inf_eq_bot_of_isPGroup_two_of_odd hQ (hcardBm ▸ hB)
  have hQU : Q ≤ B ⊔ Q := le_sup_right
  have hBU : B ≤ B ⊔ Q := le_sup_left
  have hUQ : B ⊔ Q ≤ Subgroup.normalizer (Q : Set G) := sup_le hBQ Subgroup.le_normalizer
  have hBmQ : B.map (MulAut.conj m).toMonoidHom ≤ Subgroup.normalizer (Q : Set G) :=
    hmB.trans hUQ
  have hU1 : ((B ⊔ Q : Subgroup G) : Set G) = (Q : Set G) * (B : Set G) := by
    rw [sup_comm]
    exact Subgroup.coe_mul_of_right_le_normalizer_left Q B hBQ
  have hQm : Q.map (MulAut.conj m).toMonoidHom = Q :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 hmQ
  have hUm : (B ⊔ Q).map (MulAut.conj m).toMonoidHom = B.map (MulAut.conj m).toMonoidHom ⊔ Q := by
    rw [Subgroup.map_sup, hQm]
  have hUm' : (B ⊔ Q).map (MulAut.conj m).toMonoidHom = B ⊔ Q := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [hUm]
      exact sup_le hmB hQU
    · exact (Subgroup.card_map_of_injective (MulAut.conj m).injective).ge
  have hU2 : ((B ⊔ Q : Subgroup G) : Set G) =
      (Q : Set G) * (B.map (MulAut.conj m).toMonoidHom : Set G) := by
    rw [← hUm', hUm, sup_comm]
    exact Subgroup.coe_mul_of_right_le_normalizer_left Q _ hBmQ
  have hNn : (Q.subgroupOf (B ⊔ Q)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQU).2 hUQ
  have hNsolv : Group.IsSolvable ↥(Q.subgroupOf (B ⊔ Q)) := by
    have h2 : IsPGroup 2 ↥(Q.subgroupOf (B ⊔ Q)) :=
      hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQU).symm
    have := h2.isNilpotent
    infer_instance
  have hmul : ∀ S : Subgroup G, S ≤ B ⊔ Q →
      ((B ⊔ Q : Subgroup G) : Set G) = (Q : Set G) * (S : Set G) →
      ((Q.subgroupOf (B ⊔ Q) : Subgroup ↥(B ⊔ Q)) : Set ↥(B ⊔ Q)) *
        ((S.subgroupOf (B ⊔ Q) : Subgroup ↥(B ⊔ Q)) : Set ↥(B ⊔ Q)) = Set.univ := by
    intro S hSU hUS
    refine Set.eq_univ_of_forall fun u => ?_
    have hu : (u : G) ∈ (Q : Set G) * (S : Set G) := hUS ▸ u.2
    obtain ⟨q, hq, s, hs, he⟩ := hu
    exact ⟨⟨q, hQU hq⟩, hq, ⟨s, hSU hs⟩, hs, Subtype.ext he⟩
  have hinf : ∀ S : Subgroup G, Q ⊓ S = ⊥ →
      Q.subgroupOf (B ⊔ Q) ⊓ S.subgroupOf (B ⊔ Q) = ⊥ := by
    intro S hS
    rw [eq_bot_iff]
    intro u hu
    have h1 : (u : G) ∈ Q ⊓ S := ⟨hu.1, hu.2⟩
    rw [hS] at h1
    exact (Subgroup.mem_bot).2 (Subtype.ext ((Subgroup.mem_bot).1 h1))
  have hNH := hmul B hBU hU1
  have hNK := hmul _ hmB hU2
  have hNH' := hinf B hQB
  have hNK' := hinf _ hQBm
  have hcompl : Subgroup.IsComplement' (Q.subgroupOf (B ⊔ Q)) (B.subgroupOf (B ⊔ Q)) :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.2 hNH') hNH
  have hcopN : Nat.Coprime (Nat.card (Q.subgroupOf (B ⊔ Q))) (Q.subgroupOf (B ⊔ Q)).index := by
    rw [hcompl.symm.index_eq_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQU).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBU).toEquiv]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hQ
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hB)
  obtain ⟨n, hn, hKn⟩ := CFSG.SolvableHall.solvable_normal_hall_complement_conjugacy
    (Q.subgroupOf (B ⊔ Q)) hNsolv hcopN hNH hNK hNH' hNK'
  have hcomm : (B ⊔ Q).subtype.comp (MulAut.conj n⁻¹).toMonoidHom =
      (MulAut.conj ((n : G)⁻¹)).toMonoidHom.comp (B ⊔ Q).subtype := by
    ext x
    simp
  have hBmq : B.map (MulAut.conj m).toMonoidHom = B.map (MulAut.conj ((n : G)⁻¹)).toMonoidHom := by
    have h1 := congrArg (Subgroup.map (B ⊔ Q).subtype) hKn
    rw [Subgroup.map_subgroupOf_eq_of_le hmB, Subgroup.map_map, hcomm, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hBU] at h1
    exact h1
  refine ⟨(n : G), hn, ?_⟩
  have hconj : (MulAut.conj ((n : G) * m)).toMonoidHom =
      (MulAut.conj (n : G)).toMonoidHom.comp (MulAut.conj m).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hid : (MulAut.conj (n : G)).toMonoidHom.comp (MulAut.conj ((n : G)⁻¹)).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have key : B.map (MulAut.conj ((n : G) * m)).toMonoidHom = B := by
    rw [hconj, ← Subgroup.map_map, hBmq, Subgroup.map_map, hid, Subgroup.map_id]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.2 key

theorem le_inf_centralizer_sup [Finite G] {X Q B : Subgroup G} (hQ : IsPGroup 2 ↥Q)
    (hB : Odd (Nat.card B)) (hQX : Q ≤ X) (hXQ : X ≤ Subgroup.normalizer (Q : Set G))
    (hBQ : B ≤ Subgroup.normalizer (Q : Set G)) (hXB : ⁅X, B⁆ ≤ Q) :
    X ≤ (X ⊓ Subgroup.centralizer (B : Set G)) ⊔ Q := by
  intro m hm
  have hmB : B.map (MulAut.conj m).toMonoidHom ≤ B ⊔ Q := by
    rintro _ ⟨b, hb, rfl⟩
    have h1 : ⁅m, b⁆ ∈ Q := hXB (Subgroup.commutator_mem_commutator hm hb)
    have h2 : (MulAut.conj m).toMonoidHom b = ⁅m, b⁆ * b := by
      simp [MulAut.conj_apply, commutatorElement_def]
    rw [h2]
    exact (B ⊔ Q).mul_mem (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left hb)
  obtain ⟨q, hq, hqm⟩ := exists_mul_mem_normalizer hQ hB hBQ (hXQ hm) hmB
  have hqmX : q * m ∈ X := X.mul_mem (hQX hq) hm
  have hQB : Q ⊓ B = ⊥ := inf_eq_bot_of_isPGroup_two_of_odd hQ hB
  have hqmC : q * m ∈ Subgroup.centralizer (B : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h1 : ⁅q * m, b⁆ ∈ Q := hXB (Subgroup.commutator_mem_commutator hqmX hb)
    have h2 : ⁅q * m, b⁆ ∈ B := by
      rw [commutatorElement_def]
      exact B.mul_mem ((Subgroup.mem_normalizer_iff.1 hqm b).1 hb) (B.inv_mem hb)
    have h3 : ⁅q * m, b⁆ = 1 := by
      have h4 : ⁅q * m, b⁆ ∈ Q ⊓ B := ⟨h1, h2⟩
      rw [hQB] at h4
      exact h4
    rw [commutatorElement_eq_one_iff_mul_comm] at h3
    exact h3.symm
  have hm' : m = q⁻¹ * (q * m) := by group
  rw [hm']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Q.inv_mem hq))
    (Subgroup.mem_sup_left ⟨hqmX, hqmC⟩)

theorem eq_perfectCore_sup [Finite G] {X Q B : Subgroup G} (hQ : IsPGroup 2 ↥Q)
    (hB : Odd (Nat.card B)) (hQX : Q ≤ X) (hXQ : X ≤ Subgroup.normalizer (Q : Set G))
    (hBQ : B ≤ Subgroup.normalizer (Q : Set G)) (hXB : ⁅X, B⁆ ≤ Q) (hX : ⁅X, X⁆ = X) :
    X = perfectCore (X ⊓ Subgroup.centralizer (B : Set G)) ⊔ Q := by
  set C := X ⊓ Subgroup.centralizer (B : Set G) with hC
  have key : ∀ n, X ≤ derivedSeriesOf C n ⊔ Q := by
    intro n
    induction n with
    | zero => exact le_inf_centralizer_sup hQ hB hQX hXQ hBQ hXB
    | succ n ih =>
      have hDn : derivedSeriesOf C n ≤ Subgroup.normalizer (Q : Set G) :=
        ((derivedSeriesOf_le C n).trans inf_le_left).trans hXQ
      calc X = ⁅X, X⁆ := hX.symm
        _ ≤ ⁅derivedSeriesOf C n ⊔ Q, derivedSeriesOf C n ⊔ Q⁆ := Subgroup.commutator_mono ih ih
        _ ≤ ⁅derivedSeriesOf C n, derivedSeriesOf C n⁆ ⊔ Q := commutator_sup_sup_le hDn
        _ = derivedSeriesOf C (n + 1) ⊔ Q := by rw [derivedSeriesOf_succ]
  obtain ⟨n, hn⟩ := exists_perfectCore_eq C
  refine le_antisymm ?_ (sup_le ((perfectCore_le C).trans inf_le_left) hQX)
  rw [hn n le_rfl]
  exact key n

end CFSG.Quasithin.H13
