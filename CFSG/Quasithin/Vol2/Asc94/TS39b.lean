module

public import CFSG.Quasithin.Vol2.Asc94.TS39a

public section

namespace CFSG.Quasithin.A94

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G] {z : G}

structure Frame1 (G : Type) [Group G] (z : G) extends Frame0 G z where
  U2 : Subgroup G
  Q : Subgroup G
  TQ : Set G
  Q_eq : Q = pCoreOf 2 (Cz z)
  U2_normal : ∀ h ∈ Cz z, ∀ u ∈ U2, h⁻¹ * u * h ∈ U2
  U2_trans : ∀ x ∈ U2, x ≠ 1 → x ≠ z → ∀ y ∈ U2, y ≠ 1 → y ≠ z → ∃ h ∈ Cz z, y = h⁻¹ * x * h
  Q_inv : ∀ q ∈ Q, q * q = 1 → q ≠ 1 → q = z ∨ (q ∈ U ∧ q ≠ z) ∨ (q ∈ U2 ∧ q ≠ z) ∨ q ∈ TQ
  TQ_sq : ∀ t ∈ TQ, t * t = 1
  TQ_card : ∀ t ∈ TQ, Nat.card ↥(Cz z ⊓ Cz t) = 2 ^ 9
  TQ_der : ∀ t ∈ TQ, ⁅⁅Cz z ⊓ Cz t, Cz z ⊓ Cz t⁆, ⁅Cz z ⊓ Cz t, Cz z ⊓ Cz t⁆⁆ =
    Subgroup.zpowers z

@[expose] def InZG (z x : G) : Prop := ∃ g : G, x = g⁻¹ * z * g

theorem eq_one_or_of_mem_zpowers {x w : G} (hx : orderOf x = 2) (hw : w ∈ Subgroup.zpowers x) :
    w = 1 ∨ w = x := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  have h1 : x ^ (n % (2 : ℤ)) = x ^ n := by
    have := zpow_mod_orderOf x n
    rwa [hx] at this
  rw [← h1]
  have : n % (2 : ℤ) = 0 ∨ n % (2 : ℤ) = 1 := by omega
  rcases this with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]

theorem conj_mem_derived2 {S : Subgroup G} {x w : G} (hx : x ∈ Subgroup.normalizer (S : Set G))
    (hw : w ∈ ⁅⁅S, S⁆, ⁅S, S⁆⁆) : x * w * x⁻¹ ∈ ⁅⁅S, S⁆, ⁅S, S⁆⁆ := by
  have hS : S.map (MulAut.conj x).toMonoidHom = S := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 hx s).1 hs
    · intro hy
      refine ⟨x⁻¹ * y * x, ?_, ?_⟩
      · refine (Subgroup.mem_normalizer_iff.1 hx (x⁻¹ * y * x)).2 ?_
        rw [show x * (x⁻¹ * y * x) * x⁻¹ = y by group]
        exact hy
      · show x * (x⁻¹ * y * x) * x⁻¹ = y
        group
  have hmap : (⁅⁅S, S⁆, ⁅S, S⁆⁆).map (MulAut.conj x).toMonoidHom = ⁅⁅S, S⁆, ⁅S, S⁆⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_commutator, hS]
  rw [← hmap]
  exact ⟨w, hw, rfl⟩

theorem Frame1.normalizer_S_le_H (F : Frame1 G z) {t : G} (ht : t ∈ F.TQ) :
    ∀ x ∈ Subgroup.normalizer ((Cz z ⊓ Cz t : Subgroup G) : Set G), x ∈ Cz z := by
  intro x hx
  have hz1 : z ≠ 1 := F.toFrame0.z_ne_one
  have hz : z ∈ ⁅⁅Cz z ⊓ Cz t, Cz z ⊓ Cz t⁆, ⁅Cz z ⊓ Cz t, Cz z ⊓ Cz t⁆⁆ := by
    rw [F.TQ_der t ht]
    exact Subgroup.mem_zpowers z
  have hmem : x * z * x⁻¹ ∈ Subgroup.zpowers z := by
    rw [← F.TQ_der t ht]
    exact conj_mem_derived2 hx hz
  rcases eq_one_or_of_mem_zpowers F.ord hmem with h | h
  · exfalso
    apply hz1
    have : z = x⁻¹ * (x * z * x⁻¹) * x := by group
    rw [this, h]
    group
  · rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * z = (x * z * x⁻¹) * x := by group
      _ = z * x := by rw [h]

theorem Frame1.isPGroup_S (F : Frame1 G z) {t : G} (ht : t ∈ F.TQ) :
    IsPGroup 2 ↥(Cz z ⊓ Cz t) :=
  IsPGroup.of_card (F.TQ_card t ht)

theorem Frame1.S_maximal (F : Frame1 G z) {t : G} (ht : t ∈ F.TQ) :
    ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ Cz t → (Cz z ⊓ Cz t) ≤ Q → Q = Cz z ⊓ Cz t :=
  Gen.maximal_pSubgroup_of_normalizer_le (p := 2) (P := Cz z ⊓ Cz t) (C := Cz z ⊓ Cz t)
    (K := Cz t) (F.isPGroup_S ht) le_rfl inf_le_right
    (fun _ _ hQ hPQ => le_antisymm hQ hPQ)
    (fun n hnK hnN => Subgroup.mem_inf.2 ⟨F.normalizer_S_le_H ht n hnN, hnK⟩)

theorem s39_4 (F : Frame1 G z) : ∀ t ∈ F.TQ, ∀ g : G, g⁻¹ * z * g ≠ t := by
  intro t ht g hg
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K : Subgroup G := Cz t with hK
  set S : Subgroup G := Cz z ⊓ Cz t with hS
  have hSK : S ≤ K := inf_le_right
  have hSsub : Nat.card (S.subgroupOf K) = 2 ^ 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv]
    exact F.TQ_card t ht
  let SS : Sylow 2 ↥K :=
    { toSubgroup := S.subgroupOf K
      isPGroup' := IsPGroup.of_card hSsub
      is_maximal' := by
        intro Q hQ hSQ
        have h1 : IsPGroup 2 ↥(Q.map K.subtype) := hQ.map K.subtype
        have h2 : S ≤ Q.map K.subtype := by
          intro y hy
          exact ⟨⟨y, hSK hy⟩, hSQ (by simpa [Subgroup.mem_subgroupOf] using hy), rfl⟩
        have h3 : Q.map K.subtype ≤ K := by
          rintro _ ⟨q, -, rfl⟩
          exact q.2
        have h4 := F.S_maximal ht _ h1 h3 h2
        calc Q = (Q.map K.subtype).comap K.subtype :=
              (Subgroup.comap_map_eq_self_of_injective K.subtype_injective Q).symm
          _ = (Q.map K.subtype).subgroupOf K := rfl
          _ = S.subgroupOf K := by rw [h4] }
  set T' : Subgroup G := F.T.map (MulAut.conj g⁻¹).toMonoidHom with hT'
  have hT'K : T' ≤ K := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hK, Subgroup.mem_centralizer_singleton_iff, ← hg]
    have hxz := F.z_comm_T hx
    show g⁻¹ * x * g⁻¹⁻¹ * (g⁻¹ * z * g) = g⁻¹ * z * g * (g⁻¹ * x * g⁻¹⁻¹)
    calc g⁻¹ * x * g⁻¹⁻¹ * (g⁻¹ * z * g) = g⁻¹ * (x * z) * g := by group
      _ = g⁻¹ * (z * x) * g := by rw [← hxz]
      _ = g⁻¹ * z * g * (g⁻¹ * x * g⁻¹⁻¹) := by group
  have hinj : Function.Injective (MulAut.conj g⁻¹).toMonoidHom := fun a b h =>
    (MulAut.conj g⁻¹).injective h
  have hT'card : Nat.card T' = 2 ^ 10 := by
    rw [hT', Subgroup.card_map_of_injective hinj, F.card_T]
    norm_num
  have hT'sub : Nat.card (T'.subgroupOf K) = 2 ^ 10 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT'K).toEquiv, hT'card]
  obtain ⟨P, hP⟩ := (IsPGroup.of_card hT'sub : IsPGroup 2 ↥(T'.subgroupOf K)).exists_le_sylow
  have hle : Nat.card (T'.subgroupOf K) ≤ Nat.card (P : Subgroup ↥K) :=
    Subgroup.card_le_of_le hP
  have hPS : Nat.card (P : Subgroup ↥K) = Nat.card (SS : Subgroup ↥K) := by
    rw [Sylow.card_eq_multiplicity P, Sylow.card_eq_multiplicity SS]
  have hSS : Nat.card (SS : Subgroup ↥K) = 2 ^ 9 := hSsub
  rw [hPS, hSS, hT'sub] at hle
  omega

theorem s39_5 (F : Frame1 G z)
    (hnw : ∃ g : G, g⁻¹ * z * g ∈ pCoreOf 2 (Cz z) ∧ g⁻¹ * z * g ≠ z) :
    (∀ u ∈ F.U, u ≠ 1 → InZG z u) ∨ (∀ u ∈ F.U2, u ≠ 1 → InZG z u) := by
  obtain ⟨g, hgQ, hgz⟩ := hnw
  have hz1 : z ≠ 1 := F.toFrame0.z_ne_one
  have hq1 : g⁻¹ * z * g ≠ 1 := by
    intro h
    apply hz1
    have : z = g * (g⁻¹ * z * g) * g⁻¹ := by group
    rw [this, h]
    group
  have hq2 : g⁻¹ * z * g * (g⁻¹ * z * g) = 1 := by
    have hz2 : z * z = 1 := by
      have h := pow_orderOf_eq_one z
      rw [F.ord, sq] at h
      exact h
    calc g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [hz2]; group
  have hQ : g⁻¹ * z * g ∈ F.Q := by rw [F.Q_eq]; exact hgQ
  rcases F.Q_inv _ hQ hq2 hq1 with h | ⟨hU, hne⟩ | ⟨hU2, hne⟩ | hT
  · exact absurd h hgz
  · left
    intro u hu hu1
    by_cases huz : u = z
    · exact ⟨1, by simp [huz]⟩
    · obtain ⟨h, hh, huh⟩ := F.U_trans _ hU hq1 hne u hu hu1 huz
      exact ⟨g * h, by rw [huh]; group⟩
  · right
    intro u hu hu1
    by_cases huz : u = z
    · exact ⟨1, by simp [huz]⟩
    · obtain ⟨h, hh, huh⟩ := F.U2_trans _ hU2 hq1 hne u hu hu1 huz
      exact ⟨g * h, by rw [huh]; group⟩
  · exact absurd rfl (s39_4 F _ hT g)

end CFSG.Quasithin.A94
