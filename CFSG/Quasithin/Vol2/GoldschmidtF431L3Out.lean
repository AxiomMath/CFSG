module

public import CFSG.Quasithin.Vol2.GoldschmidtF431L3Base
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.Quasithin.H13.F431.L3

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

variable {G : Type} [Group G]

theorem maximal_two_of_char [Finite G] {S M H Z' : Subgroup G} (hSM : IsSylowTwoOf S M)
    (hZS : Z' ≤ S) (hw : ∃ w ∈ Z', w ≠ 1)
    (hchar : ∀ n ∈ H, n ∈ Subgroup.normalizer (S : Set G) → ∀ x ∈ Z', n * x * n⁻¹ ∈ Z')
    (hZ : ∀ w ∈ Z', w ≠ 1 → ∀ y ∈ H, y * w = w * y → y ∈ M) :
    ∀ P : Subgroup G, IsPGroup 2 P → S ≤ P → P ≤ H → P = S := by
  intro P hP hSP hPH
  by_contra hne
  obtain ⟨n, hnP, hnN, hnS⟩ := exists_mem_normalizer_not_mem_of_isPGroup hP hSP (Ne.symm hne)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup G := S ⊔ Subgroup.zpowers n with hN
  have hNP : N ≤ P := sup_le hSP (Subgroup.zpowers_le.2 hnP)
  have hNp : IsPGroup 2 N := hP.to_le hNP
  have hNnorm : N ≤ Subgroup.normalizer (S : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 hnN)
  have hnN' : n ∈ N := Subgroup.mem_sup_right (Subgroup.mem_zpowers n)
  have hSN : S ≤ N := le_sup_left
  have : Group.IsNilpotent N := hNp.isNilpotent
  set Z0 : Subgroup N := Z'.subgroupOf N with hZ0
  have hZ0n : Z0.Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hx' : (x : G) ∈ Z' := Subgroup.mem_subgroupOf.mp hx
    have hgH : (g : G) ∈ H := hPH (hNP g.2)
    have hgn : (g : G) ∈ Subgroup.normalizer (S : Set G) := hNnorm g.2
    exact Subgroup.mem_subgroupOf.mpr (hchar _ hgH hgn _ hx')
  obtain ⟨w0, hw0S, hw01⟩ := hw
  have hZ0ne : Z0 ≠ ⊥ := by
    intro h
    have hmem : (⟨w0, hSN (hZS hw0S)⟩ : N) ∈ Z0 := Subgroup.mem_subgroupOf.mpr hw0S
    rw [h, Subgroup.mem_bot] at hmem
    exact hw01 (congrArg Subtype.val hmem)
  have hinf := Group.IsNilpotent.inf_center_ne_bot_of_normal hZ0ne
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hinf
  have haC : (a : N) ∈ Subgroup.center N := a.2.2
  have haZ : ((a : N) : G) ∈ Z' := Subgroup.mem_subgroupOf.mp (a.2.1 : (a : N) ∈ Z0)
  have ha1 : ((a : N) : G) ≠ 1 := by
    intro h
    apply ha
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hcent : ∀ x ∈ N, x * ((a : N) : G) = ((a : N) : G) * x := fun x hx => by
    have := Subgroup.mem_center_iff.mp haC ⟨x, hx⟩
    exact congrArg Subtype.val this
  have hNM : N ≤ M := fun x hx => hZ _ haZ ha1 x (hPH (hNP hx)) (hcent x hx)
  have hNeq := eq_of_isSylowTwoOf_of_isPGroup hSM hSN hNM hNp
  exact hnS (hNeq ▸ hnN')

theorem isSylowTwoOf_of_max [Finite G] {S H : Subgroup G} (hSH : S ≤ H) (hp : IsPGroup 2 S)
    (hmax : ∀ P : Subgroup G, IsPGroup 2 P → S ≤ P → P ≤ H → P = S) : IsSylowTwoOf S H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := (hp.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm).exists_le_sylow
  have hPp : IsPGroup 2 ((Q : Subgroup H).map H.subtype) := Q.isPGroup'.map _
  have hSP : S ≤ (Q : Subgroup H).map H.subtype := fun x hx =>
    ⟨⟨x, hSH hx⟩, hQ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hPH : (Q : Subgroup H).map H.subtype ≤ H := Subgroup.map_subtype_le _
  have hPS := hmax _ hPp hSP hPH
  refine ⟨hSH, hp, ?_⟩
  have : S.subgroupOf H = (Q : Subgroup H) := by
    ext x
    constructor
    · intro hx; exact hQ hx
    · intro hx
      have : (x : G) ∈ (Q : Subgroup H).map H.subtype := ⟨x, hx, rfl⟩
      rw [hPS] at this
      exact Subgroup.mem_subgroupOf.mpr this
  rw [this]
  exact Q.not_dvd_index

structure L3OutDatum (M₁ M₂ : Subgroup G) where
  S : Subgroup G
  T : Subgroup G
  B : Subgroup G
  f : G
  S_eq : S = pCoreOf 2 (M₁ ⊓ M₂)
  S_le_T : S ≤ T
  T_le : T ≤ M₁ ⊓ M₂
  T_pgroup : IsPGroup 2 T
  T_index : ¬ 2 ∣ T.relIndex M₁
  B_le : B ≤ M₁ ⊓ M₂
  trans : ∀ x ∈ centerOf S, x ≠ 1 → ∀ y ∈ centerOf S, y ≠ 1 → ∃ b ∈ B, b * x * b⁻¹ = y
  cent : ∀ x ∈ centerOf S, x ≠ 1 → ∀ y ∈ M₁, y * x = x * y → y ∈ M₂
  ZT : ∀ w ∈ centerOf T, w ∈ centerOf S
  invS : ∀ x ∈ S, x * x = 1 → x ≠ 1 → ∃ m : G, (m ∈ M₁ ∨ m ∈ M₂) ∧ m * x * m⁻¹ ∈ centerOf S
  f_mem : f ∈ T
  f_not : f ∉ S
  f_sq : f * f = 1
  T_comm : ∀ x ∈ T, ∀ y ∈ T, x * y * x⁻¹ * y⁻¹ ∈ S
  T_cyc : ∀ x ∈ T, ∀ y ∈ T, x ∉ S → y ∉ S → x * x ∈ S → y * y ∈ S → x⁻¹ * y ∈ S
  Tf_sylow : IsSylowTwoOf (T ⊓ Subgroup.centralizer {f}) (M₁ ⊓ M₂ ⊓ Subgroup.centralizer {f})
  Zf_ne : centerOf (T ⊓ Subgroup.centralizer {f}) ⊓
    ⁅T ⊓ Subgroup.centralizer {f}, T ⊓ Subgroup.centralizer {f}⁆ ≠ ⊥
  Zf_le : centerOf (T ⊓ Subgroup.centralizer {f}) ⊓
    ⁅T ⊓ Subgroup.centralizer {f}, T ⊓ Subgroup.centralizer {f}⁆ ≤ centerOf S
  Tf_lt : Nat.card ↥(T ⊓ Subgroup.centralizer {f}) < Nat.card S

theorem commutator_eq_top_of_simple {G : Type} [Group G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) : commutator G = ⊤ := by
  rcases (Subgroup.commutator_normal (⊤ : Subgroup G) (⊤ : Subgroup G)).eq_bot_or_eq_top with h | h
  · obtain ⟨a, b, hab⟩ := hnab
    exact (hab ((isMulCommutative_iff.mp ((commutator_eq_bot_iff G).mp h)) a b)).elim
  · exact h

namespace L3OutDatum

section Out

variable {M₁ M₂ : Subgroup G} (O : L3OutDatum M₁ M₂)

theorem S_le_H : O.S ≤ M₁ ⊓ M₂ := by
  rw [O.S_eq]; exact LieType.BorelTits.pCoreOf_le 2 _

theorem S_pgroup [Finite G] : IsPGroup 2 O.S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [O.S_eq]; exact LieType.BorelTits.pCoreOf_isPGroup 2 _

theorem H_le_normalizer_S : M₁ ⊓ M₂ ≤ Subgroup.normalizer (O.S : Set G) := by
  rw [O.S_eq]; exact LieType.BorelTits.le_normalizer_pCoreOf 2 _

theorem mem_centerOf {X : Subgroup G} {x : G} :
    x ∈ centerOf X ↔ x ∈ X ∧ ∀ s ∈ X, s * x = x * s := by
  unfold centerOf
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  rfl

theorem centZ {z : G} (hz : z ∈ centerOf O.S) (hz1 : z ≠ 1)
    (hC : Subgroup.centralizer ({z} : Set G) ≤ M₁) :
    ∀ x ∈ centerOf O.S, x ≠ 1 → ∀ y : G, y * x = x * y → y ∈ M₁ ⊓ M₂ := by
  intro x hx hx1 y hy
  obtain ⟨b, hb, hbz⟩ := O.trans z hz hz1 x hx hx1
  have hbH : b ∈ M₁ ⊓ M₂ := O.B_le hb
  have h1 : b⁻¹ * y * b ∈ M₁ := by
    apply hC
    rw [Subgroup.mem_centralizer_singleton_iff]
    have : y * (b * z * b⁻¹) = (b * z * b⁻¹) * y := by rw [hbz]; exact hy
    calc b⁻¹ * y * b * z = b⁻¹ * (y * (b * z * b⁻¹)) * b := by group
      _ = b⁻¹ * ((b * z * b⁻¹) * y) * b := by rw [this]
      _ = z * (b⁻¹ * y * b) := by group
  have h2 : y ∈ M₁ := by
    have := M₁.mul_mem (M₁.mul_mem hbH.1 h1) (M₁.inv_mem hbH.1)
    simpa [mul_assoc] using this
  exact ⟨h2, O.cent x hx hx1 y h2 hy⟩

end Out

end L3OutDatum

namespace L3OutDatum

section Main

variable {M₁ M₂ : Subgroup G} (O : L3OutDatum M₁ M₂)

theorem false_of_simple [Finite G] [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) {z : G}
    (hz : z ∈ centerOf O.S) (hz1 : z ≠ 1) (hC : Subgroup.centralizer ({z} : Set G) ≤ M₁) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcentG := O.centZ hz hz1 hC
  have hT1 : O.T ≤ M₁ := O.T_le.trans inf_le_left
  have hzT : z ∈ O.T := O.S_le_T ((mem_centerOf.mp hz).1)
  have hTw : ∃ w ∈ centerOf O.T, w ≠ 1 := by
    have hnt : Nontrivial O.T := ⟨⟨⟨z, hzT⟩, 1, fun h => hz1 (congrArg Subtype.val h)⟩⟩
    have := O.T_pgroup.center_nontrivial
    obtain ⟨w0, hw0⟩ := exists_ne (1 : Subgroup.center O.T)
    refine ⟨((w0 : O.T) : G), mem_centerOf.mpr ⟨(w0 : O.T).2, fun s hs => ?_⟩, ?_⟩
    · have := Subgroup.mem_center_iff.mp w0.2 ⟨s, hs⟩
      exact congrArg Subtype.val this
    · intro h
      apply hw0
      apply Subtype.ext
      apply Subtype.ext
      exact h
  have hTsyl : IsSylowTwoOf O.T ⊤ :=
    isSylowTwoOf_top_of_centralizer_le ⟨hT1, O.T_pgroup, O.T_index⟩ hTw (fun w hw hw1 y hy =>
      (hcentG w (O.ZT w hw) hw1 y (Subgroup.mem_centralizer_singleton_iff.mp hy)).1)
  have hconj : ∀ x ∈ O.S, x * x = 1 → x ≠ 1 → ∃ g : G, g * z * g⁻¹ = x := by
    intro x hx hx2 hx1
    obtain ⟨m, -, hmz⟩ := O.invS x hx hx2 hx1
    have hmx1 : m * x * m⁻¹ ≠ 1 := by
      intro h; apply hx1
      have := congrArg (fun y => m⁻¹ * y * m) h
      simpa [mul_assoc] using this
    obtain ⟨b, -, hbz⟩ := O.trans z hz hz1 _ hmz hmx1
    refine ⟨m⁻¹ * b, ?_⟩
    calc m⁻¹ * b * z * (m⁻¹ * b)⁻¹ = m⁻¹ * (b * z * b⁻¹) * m := by group
      _ = m⁻¹ * (m * x * m⁻¹) * m := by rw [hbz]
      _ = x := by group
  have hTf_le : O.T ⊓ Subgroup.centralizer ({O.f} : Set G) ≤ Subgroup.centralizer ({O.f} : Set G) :=
    inf_le_right
  have hZfS : centerOf (O.T ⊓ Subgroup.centralizer ({O.f} : Set G)) ⊓
      ⁅O.T ⊓ Subgroup.centralizer ({O.f} : Set G), O.T ⊓ Subgroup.centralizer ({O.f} : Set G)⁆ ≤
      O.T ⊓ Subgroup.centralizer ({O.f} : Set G) := inf_le_left.trans inf_le_left
  have hZfw : ∃ w ∈ centerOf (O.T ⊓ Subgroup.centralizer ({O.f} : Set G)) ⊓
      ⁅O.T ⊓ Subgroup.centralizer ({O.f} : Set G), O.T ⊓ Subgroup.centralizer ({O.f} : Set G)⁆,
      w ≠ 1 := by
    obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp O.Zf_ne
    refine ⟨(a : G), a.2, fun h => ha (Subtype.ext h)⟩
  have hchar : ∀ n ∈ Subgroup.centralizer ({O.f} : Set G),
      n ∈ Subgroup.normalizer ((O.T ⊓ Subgroup.centralizer ({O.f} : Set G) : Subgroup G) : Set G) →
      ∀ x ∈ centerOf (O.T ⊓ Subgroup.centralizer ({O.f} : Set G)) ⊓
        ⁅O.T ⊓ Subgroup.centralizer ({O.f} : Set G), O.T ⊓ Subgroup.centralizer ({O.f} : Set G)⁆,
        n * x * n⁻¹ ∈ centerOf (O.T ⊓ Subgroup.centralizer ({O.f} : Set G)) ⊓
        ⁅O.T ⊓ Subgroup.centralizer ({O.f} : Set G),
          O.T ⊓ Subgroup.centralizer ({O.f} : Set G)⁆ := by
    intro n _ hn x hx
    have hcn := conjSub_eq_of_mem_normalizer hn
    have e : conjSub n (centerOf (O.T ⊓ Subgroup.centralizer ({O.f} : Set G)) ⊓
        ⁅O.T ⊓ Subgroup.centralizer ({O.f} : Set G),
          O.T ⊓ Subgroup.centralizer ({O.f} : Set G)⁆) =
        centerOf (O.T ⊓ Subgroup.centralizer ({O.f} : Set G)) ⊓
        ⁅O.T ⊓ Subgroup.centralizer ({O.f} : Set G),
          O.T ⊓ Subgroup.centralizer ({O.f} : Set G)⁆ := by
      rw [conjSub_inf, ← centerOf_conjSub, ← conjSub_commutator, hcn]
    rw [← e]
    exact mul_mem_conjSub hx
  have hmax := maximal_two_of_char (S := O.T ⊓ Subgroup.centralizer ({O.f} : Set G))
    (M := M₁ ⊓ M₂ ⊓ Subgroup.centralizer ({O.f} : Set G))
    (H := Subgroup.centralizer ({O.f} : Set G)) (Z' := centerOf (O.T ⊓ Subgroup.centralizer
      ({O.f} : Set G)) ⊓ ⁅O.T ⊓ Subgroup.centralizer ({O.f} : Set G),
        O.T ⊓ Subgroup.centralizer ({O.f} : Set G)⁆)
    O.Tf_sylow hZfS hZfw hchar (fun w hw hw1 y hy hyw => ⟨hcentG w (O.Zf_le hw) hw1 y hyw, hy⟩)
  have hTfSyl : IsSylowTwoOf (O.T ⊓ Subgroup.centralizer ({O.f} : Set G))
      (Subgroup.centralizer ({O.f} : Set G)) :=
    isSylowTwoOf_of_max hTf_le (O.T_pgroup.to_le inf_le_left) hmax
  have hf1 : O.f ≠ 1 := fun h => O.f_not (h ▸ O.S.one_mem)
  have hfG : ∀ g : G, g⁻¹ * O.f * g ∉ O.S := by
    intro g hg
    have hj2 : g⁻¹ * O.f * g * (g⁻¹ * O.f * g) = 1 := by
      calc g⁻¹ * O.f * g * (g⁻¹ * O.f * g) = g⁻¹ * (O.f * O.f) * g := by group
        _ = 1 := by rw [O.f_sq]; group
    obtain ⟨h, hh⟩ := hconj _ hg hj2 (conj_ne_one' hf1)
    have hfeq : O.f = (g * h) * z * (g * h)⁻¹ := by
      calc O.f = g * (g⁻¹ * O.f * g) * g⁻¹ := by group
        _ = g * (h * z * h⁻¹) * g⁻¹ := by rw [hh]
        _ = (g * h) * z * (g * h)⁻¹ := by group
    have hPp : IsPGroup 2 (conjSub (g * h) O.S) := F7.isPGroup_conjSub O.S_pgroup
    have hPH : conjSub (g * h) O.S ≤ Subgroup.centralizer ({O.f} : Set G) := by
      intro p hp
      rw [mem_conjSub] at hp
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hc := (mem_centerOf.mp hz).2 _ hp
      calc p * O.f = (g * h) * (((g * h)⁻¹ * p * (g * h)) * z) * (g * h)⁻¹ := by rw [hfeq]; group
        _ = (g * h) * (z * ((g * h)⁻¹ * p * (g * h))) * (g * h)⁻¹ := by rw [hc]
        _ = O.f * p := by rw [hfeq]; group
    obtain ⟨x, -, hPx⟩ := F7.isSylowTwoOf_exists_conj_le hTfSyl hPH hPp
    have h1 : Nat.card (conjSub (g * h) O.S) ≤ Nat.card (conjSub x
        (O.T ⊓ Subgroup.centralizer ({O.f} : Set G))) := Subgroup.card_le_of_le hPx
    rw [card_conjSub, card_conjSub] at h1
    exact absurd O.Tf_lt (not_lt.mpr h1)
  have hT2 : Nat.Coprime 2 O.T.index := by
    have h := hTsyl.2.2
    have h' : ¬ 2 ∣ O.T.index := by
      rw [← Subgroup.relIndex_top_right]; exact h
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h'
  have hTnorm : O.T ≤ Subgroup.normalizer (O.S : Set G) := O.T_le.trans O.H_le_normalizer_S
  have hnotcomm : O.f ∉ commutator G := by
    refine generalized_thompson_transfer_two (H := O.T) (K := O.S) hT2
      ⟨O.S_le_T, Subgroup.normal_subgroupOf_of_le_normalizer hTnorm⟩ ?_ O.f_mem O.f_not
      (orderOf_eq_prime (by rw [pow_two]; exact O.f_sq) hf1) ?_
    · exact Subgroup.commutator_le.mpr (fun x hx y hy => O.T_comm x hx y hy)
    · intro a ha
      exact O.T_cyc _ O.f_mem _ ha O.f_not (hfG a) (by rw [O.f_sq]; exact O.S.one_mem)
        (by
          have : a⁻¹ * O.f * a * (a⁻¹ * O.f * a) = 1 := by
            calc a⁻¹ * O.f * a * (a⁻¹ * O.f * a) = a⁻¹ * (O.f * O.f) * a := by group
              _ = 1 := by rw [O.f_sq]; group
          rw [this]; exact O.S.one_mem)
  exact hnotcomm (by rw [commutator_eq_top_of_simple hnab]; trivial)

end Main

end L3OutDatum


end CFSG.Quasithin.H13.F431.L3
