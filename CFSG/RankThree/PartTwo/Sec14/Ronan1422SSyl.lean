module

public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SRK
public import CFSG.RankThree.PartTwo.Sec11.Item116H3Rank
public import CFSG.RankThree.PartTwo.Sec4.LThreePiAct
public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SDefs

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

namespace Pt

theorem pow_three_of_mem (h : Pt A c L) {x : G} (hx : x ∈ A) : x ^ 3 = 1 :=
  h.std.mem_partTwoF.1.2 x hx

theorem comm_of_mem (h : Pt A c L) {a b : G} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a :=
  congrArg Subtype.val (h.std.mem_partTwoF.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem three_dvd_card_L (h : Pt A c L) : 3 ∣ Nat.card L :=
  Proof1413Res3.three_dvd_card_of_card_inf h.card_B

theorem normalizer_zpowers_le (h : Pt A c L) :
    Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  intro w hw
  have hwc : w * c * w⁻¹ ∈ Subgroup.zpowers c :=
    (Subgroup.mem_normalizer_iff.mp hw c).mp (Subgroup.mem_zpowers c)
  have hmem := Sec11.map_conj_mem_thetaComponentsAt (h.pow_three_of_mem h.mem_A) h.std.mem_lA.1 hwc
  have hdvd : 3 ∣ Nat.card (L.map (MulAut.conj w).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj w).injective]
    exact h.three_dvd_card_L
  exact CFSG.RankThree.PartTwo.Sec14.mem_normalizer_of_map_conj_eq
    ((h.std.chosen136.2 c h.std.zpowers_mem_omegaA L h.std.mem_lA).2 _ hmem hdvd)

theorem mem_A_of_centralizes (h : Pt A c L) {z : G} (hzA : ∀ a ∈ A, a * z = z * a)
    (hz3 : z ^ 3 = 1) : z ∈ A := by
  refine Sec4.mem_of_maximal_of_commute ⟨h.std.mem_partTwoF.1, fun B hB hAB => ?_⟩ hz3 hzA
  exact (h.std.mem_partTwoF.2.1 B hB hAB).le

end Pt

theorem mem_sup_of_forall_commute {H K : Subgroup G} (hc : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x)
    {z : G} : z ∈ H ⊔ K ↔ ∃ x ∈ H, ∃ y ∈ K, x * y = z := by
  refine ⟨fun hz => ?_, fun ⟨x, hx, y, hy, e⟩ => by
    rw [← e]; exact mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hy)⟩
  let S : Subgroup G :=
    { carrier := {z | ∃ x ∈ H, ∃ y ∈ K, x * y = z}
      mul_mem' := by
        rintro _ _ ⟨x₁, hx₁, y₁, hy₁, rfl⟩ ⟨x₂, hx₂, y₂, hy₂, rfl⟩
        refine ⟨x₁ * x₂, H.mul_mem hx₁ hx₂, y₁ * y₂, K.mul_mem hy₁ hy₂, ?_⟩
        calc x₁ * x₂ * (y₁ * y₂) = x₁ * (x₂ * y₁) * y₂ := by group
          _ = x₁ * (y₁ * x₂) * y₂ := by rw [hc x₂ hx₂ y₁ hy₁]
          _ = x₁ * y₁ * (x₂ * y₂) := by group
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨x, hx, y, hy, rfl⟩
        refine ⟨x⁻¹, H.inv_mem hx, y⁻¹, K.inv_mem hy, ?_⟩
        have h' := congrArg (fun t => t⁻¹) (hc x hx y hy)
        simp only [mul_inv_rev] at h' ⊢
        exact h'.symm }
  obtain ⟨x, hx, y, hy, e⟩ := (sup_le (fun x hx => ⟨x, hx, 1, K.one_mem, mul_one x⟩)
    (fun y hy => ⟨1, H.one_mem, y, hy, one_mul y⟩) : H ⊔ K ≤ S) hz
  exact ⟨x, hx, y, hy, e⟩

omit [Finite G] in
theorem mul_inv_eq_inv_mul_of_mul_eq {a b : G} (h : a * b = b * a) : a * b⁻¹ = b⁻¹ * a := by
  calc a * b⁻¹ = b⁻¹ * (b * a) * b⁻¹ := by group
    _ = b⁻¹ * (a * b) * b⁻¹ := by rw [h]
    _ = b⁻¹ * a := by group

omit [Finite G] in
theorem conj_eq_of_pow_prime_pow {c g : G} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) {k : ℕ}
    (hgk : g ^ 3 ^ k = 1) (hgc : g * c * g⁻¹ ∈ Subgroup.zpowers c) : g * c * g⁻¹ = c := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hcyc : ∀ t ∈ Subgroup.zpowers c, t = 1 ∨ t = c ∨ t = c⁻¹ := by
    intro t ht
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    have hm := zpow_mod_orderOf c m
    rw [hord, Nat.cast_ofNat] at hm
    have h2 : c ^ (2 : ℤ) = c⁻¹ := by
      have : c ^ (2 : ℤ) = c ^ 2 := by norm_cast
      rw [this]
      exact (inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hc3)).symm
    have h3 : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases h3 with h3 | h3 | h3
    · left
      rw [h3, zpow_zero] at hm
      exact hm.symm
    · right; left
      rw [h3, zpow_one] at hm
      exact hm.symm
    · right; right
      rw [h3, h2] at hm
      exact hm.symm
  have hd1 : g * c * g⁻¹ ≠ 1 := fun h1 => hc1 (by
    have := congrArg (fun t => g⁻¹ * t * g) h1
    simpa [mul_assoc] using this)
  rcases hcyc _ hgc with h1 | h1 | h1
  · exact absurd h1 hd1
  · exact h1
  · exfalso
    have hsq : g ^ 2 * c * (g ^ 2)⁻¹ = c := by
      calc g ^ 2 * c * (g ^ 2)⁻¹ = g * (g * c * g⁻¹) * g⁻¹ := by
              rw [sq, mul_inv_rev]; group
        _ = g * c⁻¹ * g⁻¹ := by rw [h1]
        _ = (g * c * g⁻¹)⁻¹ := by group
        _ = c := by rw [h1, inv_inv]
    have hodd : ∀ n : ℕ, g ^ (2 * n + 1) * c * (g ^ (2 * n + 1))⁻¹ = c⁻¹ := by
      intro n
      induction n with
      | zero => simpa using h1
      | succ n ih =>
        calc g ^ (2 * (n + 1) + 1) * c * (g ^ (2 * (n + 1) + 1))⁻¹
            = g ^ 2 * (g ^ (2 * n + 1) * c * (g ^ (2 * n + 1))⁻¹) * (g ^ 2)⁻¹ := by
              rw [show 2 * (n + 1) + 1 = 2 + (2 * n + 1) by ring, pow_add]; group
          _ = g ^ 2 * c⁻¹ * (g ^ 2)⁻¹ := by rw [ih]
          _ = (g ^ 2 * c * (g ^ 2)⁻¹)⁻¹ := by group
          _ = c⁻¹ := by rw [hsq]
    obtain ⟨n, hn⟩ : Odd (3 ^ k) := Odd.pow ⟨1, rfl⟩
    have h4 := hodd n
    rw [← hn, hgk, one_mul, inv_one, mul_one] at h4
    have hcc : c * c = 1 := by
      have := congrArg (fun t => c * t) h4
      simpa using this
    have h5 : c ^ 3 = c := by rw [pow_three, hcc, mul_one]
    exact hc1 (by rw [← h5]; exact hc3)

theorem exists_mem_normalizer_not_mem {p : ℕ} [Fact p.Prime] {Q A : Subgroup G}
    (hQ : IsPGroup p Q) (hAQ : A ≤ Q) (hne : A ≠ Q) :
    ∃ x ∈ Q, x ∈ Subgroup.normalizer (A : Set G) ∧ x ∉ A := by
  haveI : Group.IsNilpotent Q := hQ.isNilpotent
  have hsub : A.subgroupOf Q < ⊤ := lt_top_iff_ne_top.mpr fun htop =>
    hne (le_antisymm hAQ (Subgroup.subgroupOf_eq_top.mp htop))
  have hnc : NormalizerCondition Q := Group.normalizerCondition_of_isNilpotent
  obtain ⟨x0, hx0N, hx0A⟩ := SetLike.exists_of_lt (hnc _ hsub)
  refine ⟨(x0 : G), x0.2, ?_, fun hx => hx0A (Subgroup.mem_subgroupOf.mpr hx)⟩
  rw [Subgroup.mem_normalizer_iff]
  intro g
  by_cases hgQ : g ∈ Q
  · have h1 := Subgroup.mem_normalizer_iff.mp hx0N ⟨g, hgQ⟩
    simpa [Subgroup.mem_subgroupOf] using h1
  · constructor
    · intro hgA
      exact absurd (hAQ hgA) hgQ
    · intro hxg
      exfalso
      apply hgQ
      have e : g = (x0 : G)⁻¹ * ((x0 : G) * g * (x0 : G)⁻¹) * (x0 : G) := by group
      rw [e]
      exact Q.mul_mem (Q.mul_mem (Q.inv_mem x0.2) (hAQ hxg)) x0.2

theorem map_conj_mul_map (X : Subgroup G) (a b : G) :
    X.map (MulAut.conj (a * b)).toMonoidHom =
      (X.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev]
  group

omit [Finite G] in
theorem map_conj_map_conj_inv (X : Subgroup G) (a : G) :
    (X.map (MulAut.conj a).toMonoidHom).map (MulAut.conj a⁻¹).toMonoidHom = X := by
  rw [Subgroup.map_map]
  have h1 : (MulAut.conj a⁻¹).toMonoidHom.comp (MulAut.conj a).toMonoidHom = MonoidHom.id G := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.id_apply,
      MulAut.conj_apply, inv_inv]
    group
  rw [h1, Subgroup.map_id]

omit [Finite G] in
theorem eq_or_eq_of_pair_mem {α : Type*} {S : Set α} {P Q R Y Z : α} (hS : S = {P, Q})
    (hR : R ∈ S) (hY : Y ∈ S) (hZ : Z ∈ S) (hZR : Z ≠ R) : Y = R ∨ Y = Z := by
  subst hS
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hR hY hZ
  rcases hR with rfl | rfl
  · rcases hZ with rfl | rfl
    · exact absurd rfl hZR
    · rcases hY with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
  · rcases hZ with rfl | rfl
    · rcases hY with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl rfl
    · exact absurd rfl hZR

theorem maxInvariant_map_mem {H : Type} [Group H] (σ : H ≃* H) {B : Subgroup H}
    (hB : B.map σ.toMonoidHom = B) {X : Subgroup H}
    (hX : X ∈ maxInvariantPiSubgroups ⊤ B (piOf 2)) :
    X.map σ.toMonoidHom ∈ maxInvariantPiSubgroups ⊤ B (piOf 2) := by
  have himg := CFSG.RankThree.PartTwo.Sec4.Sporadic.image_maxInvariantPiSubgroups σ ⊤ B (piOf 2)
  rw [Subgroup.map_top_of_surjective _ σ.surjective, hB] at himg
  rw [← himg]
  exact ⟨X, hX, rfl⟩

omit [Finite G] in
theorem map_subtype_map_aut {X : Subgroup L} {σ : MulAut L} {u : G}
    (hσ : ∀ x : L, ((σ x : L) : G) = u * x * u⁻¹) :
    (X.map σ.toMonoidHom).map L.subtype = (X.map L.subtype).map (MulAut.conj u).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  exact hσ x

omit [Finite G] in
theorem map_subtype_conj_subgroupOf {X : Subgroup G} (hX : X ≤ L) (l : L) :
    ((X.subgroupOf L).map (MulAut.conj l).toMonoidHom).map L.subtype =
      X.map (MulAut.conj (l : G)).toMonoidHom := by
  rw [Subgroup.map_map]
  have hcomp : L.subtype.comp (MulAut.conj l).toMonoidHom =
      (MulAut.conj (l : G)).toMonoidHom.comp L.subtype := by
    ext x
    rfl
  rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hX]

theorem map_normalizerMonoidHom_subgroupOf {B : Subgroup G} (hBL : B ≤ L) {u : G}
    (hu : u ∈ Subgroup.normalizer (L : Set G)) (hB : B.map (MulAut.conj u).toMonoidHom = B) :
    (B.subgroupOf L).map (L.normalizerMonoidHom ⟨u, hu⟩).toMonoidHom = B.subgroupOf L := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨l, hl, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    have hmem : u * (l : G) * u⁻¹ ∈ B.map (MulAut.conj u).toMonoidHom :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mp hl)
    rw [hB] at hmem
    exact hmem
  · have hcard : Nat.card ((B.subgroupOf L).map (L.normalizerMonoidHom ⟨u, hu⟩).toMonoidHom) =
        Nat.card (B.subgroupOf L) :=
      Subgroup.card_map_of_injective (L.normalizerMonoidHom ⟨u, hu⟩).injective
    exact hcard.symm.le

namespace Pt

theorem comm_subgroupOf (h : Pt A c L) {b b' : L} (hb : b ∈ (A ⊓ L).subgroupOf L)
    (hb' : b' ∈ (A ⊓ L).subgroupOf L) : b * b' = b' * b :=
  Subtype.ext (h.comm_of_mem (Subgroup.mem_subgroupOf.mp hb).1 (Subgroup.mem_subgroupOf.mp hb').1)

theorem map_A_eq (h : Pt A c L) {u : G}
    (hcu : Subgroup.zpowers (u * c * u⁻¹) = Subgroup.zpowers c)
    (hB : (A ⊓ L).map (MulAut.conj u).toMonoidHom = A ⊓ L) :
    A.map (MulAut.conj u).toMonoidHom = A := by
  have hz : (Subgroup.zpowers c).map (MulAut.conj u).toMonoidHom = Subgroup.zpowers c := by
    rw [MonoidHom.map_zpowers]
    exact hcu
  calc A.map (MulAut.conj u).toMonoidHom
      = (Subgroup.zpowers c ⊔ (A ⊓ L)).map (MulAut.conj u).toMonoidHom := by rw [← h.eq_sup]
    _ = (Subgroup.zpowers c).map (MulAut.conj u).toMonoidHom ⊔
          (A ⊓ L).map (MulAut.conj u).toMonoidHom := Subgroup.map_sup _ _ _
    _ = Subgroup.zpowers c ⊔ (A ⊓ L) := by rw [hz, hB]
    _ = A := h.eq_sup.symm

end Pt

section KP4Cert


namespace Pt

theorem fix_of_pow (h : Pt A c L) {x : G} (hxL : x ∈ Subgroup.normalizer (L : Set G))
    {k : ℕ} (hxk : x ^ 3 ^ k = 1) (hxB : x ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G)) :
    ∀ b ∈ A ⊓ L, x * b * x⁻¹ = b := by
  set α : MulAut L := L.normalizerMonoidHom ⟨x, hxL⟩ with hα
  have hcoe : ∀ l : L, ((α l : L) : G) = x * l * x⁻¹ := fun l => rfl
  set BL : Subgroup L := (A ⊓ L).subgroupOf L with hBL
  have hBα : BL.map α.toMonoidHom = BL := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨l, hl, rfl⟩
      show α l ∈ BL
      rw [hBL, Subgroup.mem_subgroupOf, hcoe]
      exact (Subgroup.mem_normalizer_iff.mp hxB _).mp (Subgroup.mem_subgroupOf.mp hl)
    · have hcard : Nat.card (BL.map α.toMonoidHom) = Nat.card BL :=
        Subgroup.card_map_of_injective α.injective
      exact hcard.symm.le
  have hfix8 : ∀ b ∈ BL, (α ^ 8) b = b := fun b hb =>
    KFacts.KP4.m22_aut_pow_eight h.m22 h.card_B_L hBα hb
  have hαpow : α ^ 3 ^ k = 1 := by
    have h1 : (⟨x, hxL⟩ : Subgroup.normalizer (L : Set G)) ^ 3 ^ k = 1 :=
      Subtype.ext (by simpa using hxk)
    rw [hα, ← map_pow, h1, map_one]
  have hm_dvd : orderOf α ∣ 3 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hαpow
  have hfix : ∀ b ∈ BL, α b = b := by
    rcases Nat.lt_or_ge 1 (orderOf α) with hm | hm
    · have hcop : Nat.Coprime 8 (orderOf α) :=
        Nat.Coprime.coprime_dvd_right hm_dvd (Nat.Coprime.pow_right k (by norm_num))
      obtain ⟨t, -, ht⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hm
      have hαt : (α ^ 8) ^ t = α := by
        rw [← pow_mul, ← pow_mod_orderOf α (8 * t), ht, pow_one]
      intro b hb
      have hit : ∀ s : ℕ, ((α ^ 8) ^ s) b = b := by
        intro s
        induction s with
        | zero => rfl
        | succ s ih => rw [pow_succ, MulAut.mul_apply, hfix8 b hb, ih]
      rw [← hαt]
      exact hit t
    · intro b _
      have hpos : 0 < orderOf α := by
        rcases Nat.eq_zero_or_pos (orderOf α) with h0 | h0
        · rw [h0, zero_dvd_iff] at hm_dvd
          exact absurd hm_dvd (pow_ne_zero _ (by norm_num))
        · exact h0
      have h1 : α = 1 := orderOf_eq_one_iff.mp (by omega)
      rw [h1, MulAut.one_apply]
  intro b hb
  have hbBL : (⟨b, (Subgroup.mem_inf.mp hb).2⟩ : L) ∈ BL := Subgroup.mem_subgroupOf.mpr hb
  have := congrArg Subtype.val (hfix _ hbBL)
  rw [hcoe] at this
  exact this

theorem exists_factor (h : Pt A c L) {x : G} (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hxB : ∀ b ∈ A ⊓ L, x * b = b * x) :
    ∃ b ∈ A ⊓ L, ∀ l ∈ L, (b⁻¹ * x) * l = l * (b⁻¹ * x) := by
  set α : MulAut L := L.normalizerMonoidHom ⟨x, hxL⟩ with hα
  have hcoe : ∀ l : L, ((α l : L) : G) = x * l * x⁻¹ := fun l => rfl
  have hfix : ∀ b ∈ (A ⊓ L).subgroupOf L, α b = b := by
    intro b hb
    apply Subtype.ext
    rw [hcoe]
    have hb' := Subgroup.mem_subgroupOf.mp hb
    rw [hxB _ hb', mul_inv_cancel_right]
  obtain ⟨c', hc', hαc⟩ := KFacts.KP4.m22_aut_fix_eq_conj h.m22 h.card_B_L hfix
  refine ⟨(c' : G), Subgroup.mem_subgroupOf.mp hc', fun l hl => ?_⟩
  have hl' : α ⟨l, hl⟩ = MulAut.conj c' ⟨l, hl⟩ := by rw [hαc]
  have heq : x * l * x⁻¹ = (c' : G) * l * (c' : G)⁻¹ := by
    have := congrArg Subtype.val hl'
    rw [hcoe] at this
    simpa using this
  calc ((c' : G)⁻¹ * x) * l = (c' : G)⁻¹ * (x * l * x⁻¹) * x := by group
    _ = (c' : G)⁻¹ * ((c' : G) * l * (c' : G)⁻¹) * x := by rw [heq]
    _ = l * ((c' : G)⁻¹ * x) := by group

theorem center_eq_bot (h : Pt A c L) : Subgroup.center L = ⊥ := by
  obtain ⟨e⟩ := h.m22
  haveI : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M22 :=
    CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
  haveI : IsSimpleGroup L := e.isSimpleGroup
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center L) with hbot | htop
  · exact hbot
  · exfalso
    have hC : (⊤ : Subgroup L) ≤
        Subgroup.centralizer (((A ⊓ L).subgroupOf L : Subgroup L) : Set L) := by
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro b _
      have hx : x ∈ Subgroup.center L := by rw [htop]; exact Subgroup.mem_top x
      exact Subgroup.mem_center_iff.mp hx b
    rw [KFacts.KP4.m22_centralizer_eq h.m22 h.card_B_L] at hC
    have hBtop : (A ⊓ L).subgroupOf L = ⊤ := top_le_iff.mp hC
    have hcard : Nat.card L = 443520 := by
      rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Mathieu.card_M22]
    have h9 := h.card_B_L
    rw [hBtop, Subgroup.card_top, hcard] at h9
    norm_num at h9

theorem mem_zpowers_of_centralizes (h : Pt A c L) {z : G} (hzA : ∀ a ∈ A, a * z = z * a)
    (hzL : ∀ l ∈ L, z * l = l * z) (hz3 : z ^ 3 = 1) : z ∈ Subgroup.zpowers c := by
  have hzA' : z ∈ A := h.mem_A_of_centralizes hzA hz3
  have hsup : z ∈ Subgroup.zpowers c ⊔ (A ⊓ L) := by rw [← h.eq_sup]; exact hzA'
  have hzc : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ A ⊓ L, x * y = y * x := fun x hx y hy =>
    h.comm_of_mem (Subgroup.zpowers_le.mpr h.mem_A hx) hy.1
  obtain ⟨y, hy, e, he, hye⟩ := (mem_sup_of_forall_commute hzc).mp hsup
  have hcL : ∀ x ∈ Subgroup.zpowers c, ∀ l ∈ L, x * l = l * x := by
    intro x hx l hl
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hcl : Commute c l := (Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hl)).symm
    exact (hcl.zpow_left m).eq
  have hecent : ∀ l ∈ L, e * l = l * e := by
    intro l hl
    have h1 := hzL l hl
    rw [← hye] at h1
    have h2 := hcL y⁻¹ (Subgroup.inv_mem _ hy) l hl
    calc e * l = y⁻¹ * ((y * e) * l) := by group
      _ = y⁻¹ * (l * (y * e)) := by rw [h1]
      _ = (y⁻¹ * l) * (y * e) := by group
      _ = l * (y⁻¹ * (y * e)) := by rw [h2, mul_assoc]
      _ = l * e := by group
  have he1 : e = 1 := by
    have hcent : (⟨e, he.2⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      simpa using (hecent (g : G) g.2).symm
    rw [h.center_eq_bot, Subgroup.mem_bot] at hcent
    simpa using congrArg Subtype.val hcent
  rw [← hye, he1, mul_one]
  exact hy

theorem cube_mem_zpowers (h : Pt A c L) {y : G} (hyA : ∀ a ∈ A, a * y = y * a)
    (hy9 : y ^ 9 = 1) : y ^ 3 ∈ Subgroup.zpowers c := by
  have hyc : y * c = c * y := (hyA c h.mem_A).symm
  have hyN : y ∈ Subgroup.normalizer (L : Set G) :=
    h.cent_le (Subgroup.mem_centralizer_singleton_iff.mpr hyc)
  obtain ⟨b, hb, hz⟩ := h.exists_factor hyN (fun b hb => (hyA b hb.1).symm)
  obtain ⟨z, hzdef⟩ : ∃ z : G, z = b⁻¹ * y := ⟨_, rfl⟩
  have hbA : ∀ a ∈ A, a * b = b * a := fun a ha => h.comm_of_mem ha hb.1
  have hzL : ∀ l ∈ L, z * l = l * z := fun l hl => by rw [hzdef]; exact hz l hl
  have hcz : ∀ a ∈ A, a * z = z * a := by
    intro a ha
    rw [hzdef]
    calc a * (b⁻¹ * y) = (a * b⁻¹) * y := by simp only [mul_assoc]
      _ = (b⁻¹ * a) * y := by rw [mul_inv_eq_inv_mul_of_mul_eq (hbA a ha)]
      _ = b⁻¹ * (a * y) := by simp only [mul_assoc]
      _ = b⁻¹ * (y * a) := by rw [hyA a ha]
      _ = (b⁻¹ * y) * a := by simp only [mul_assoc]
  have hby : Commute b y := hyA b hb.1
  have hb3 : b ^ 3 = 1 := h.pow_three_of_mem hb.1
  have hb9 : b ^ 9 = 1 := by
    rw [show (9 : ℕ) = 3 * 3 from rfl, pow_mul, hb3, one_pow]
  have hyz : y = b * z := by rw [hzdef]; group
  have hbz : Commute b z := hcz b hb.1
  have hy3 : y ^ 3 = z ^ 3 := by
    rw [hyz, hbz.mul_pow 3, hb3, one_mul]
  have hz9 : z ^ 9 = 1 := by
    have hc : Commute b⁻¹ y := hby.inv_left
    rw [hzdef, hc.mul_pow 9, hy9, mul_one, inv_pow, hb9, inv_one]
  have hw3 : (z ^ 3) ^ 3 = 1 := by
    rw [← pow_mul]
    exact hz9
  have hwA : ∀ a ∈ A, a * z ^ 3 = z ^ 3 * a := fun a ha =>
    ((show Commute a z from hcz a ha).pow_right 3).eq
  have hwL : ∀ l ∈ L, z ^ 3 * l = l * z ^ 3 := fun l hl =>
    ((show Commute z l from hzL l hl).pow_left 3).eq
  rw [hy3]
  exact h.mem_zpowers_of_centralizes hwA hwL hw3

theorem eq_of_isPGroup_three (h : Pt A c L) {Q : Subgroup G} (hQ : IsPGroup 3 Q) (hAQ : A ≤ Q)
    (hQN : Q ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) : Q = A := by
  by_contra hne
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc3 : c ^ 3 = 1 := h.pow_three_of_mem h.mem_A
  have hcard : Nat.card (Subgroup.zpowers c) = 3 :=
    (zpowers_mem_omegaA_iff.mp h.std.zpowers_mem_omegaA).2.1
  have hordc : orderOf c = 3 := by rw [← Nat.card_zpowers]; exact hcard
  have hc1 : c ≠ 1 := by
    intro hc
    rw [hc, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hcard
    norm_num at hcard
  obtain ⟨x, hxQ, hxN, hxA⟩ := exists_mem_normalizer_not_mem hQ hAQ (Ne.symm hne)
  obtain ⟨k, hxk⟩ : ∃ k : ℕ, x ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hQ ⟨x, hxQ⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hxcN : x ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := hQN hxQ
  have hxc : x * c * x⁻¹ = c :=
    conj_eq_of_pow_prime_pow hc3 hc1 hxk
      ((Subgroup.mem_normalizer_iff.mp hxcN c).mp (Subgroup.mem_zpowers c))
  have hxL : x ∈ Subgroup.normalizer (L : Set G) := h.normalizer_zpowers_le hxcN
  have hxB : x ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    simp only [SetLike.mem_coe, Subgroup.mem_inf]
    exact and_congr (Subgroup.mem_normalizer_iff.mp hxN g) (Subgroup.mem_normalizer_iff.mp hxL g)
  have hxBc : ∀ b ∈ A ⊓ L, x * b = b * x := fun b hb =>
    mul_inv_eq_iff_eq_mul.mp (h.fix_of_pow hxL hxk hxB b hb)
  have hxA' : ∀ a ∈ A, x * a = a * x := by
    have hle : A ≤ Subgroup.centralizer ({x} : Set G) := by
      rw [h.eq_sup]
      refine sup_le (Subgroup.zpowers_le.mpr ?_) ?_
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hxc).symm
      · intro b hb
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hxBc b hb).symm
    intro a ha
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle ha)).symm
  obtain ⟨b, hbB, hzL⟩ := h.exists_factor hxL hxBc
  obtain ⟨z, hzdef⟩ : ∃ z : G, z = b⁻¹ * x := ⟨_, rfl⟩
  have hzA : ∀ a ∈ A, a * z = z * a := by
    intro a ha
    rw [hzdef]
    calc a * (b⁻¹ * x) = (a * b⁻¹) * x := by simp only [mul_assoc]
      _ = (b⁻¹ * a) * x := by rw [mul_inv_eq_inv_mul_of_mul_eq (h.comm_of_mem ha hbB.1)]
      _ = b⁻¹ * (a * x) := by simp only [mul_assoc]
      _ = b⁻¹ * (x * a) := by rw [← hxA' a ha]
      _ = (b⁻¹ * x) * a := by simp only [mul_assoc]
  have hzQ : z ∈ Q := by
    rw [hzdef]
    exact Q.mul_mem (Q.inv_mem (hAQ hbB.1)) hxQ
  have hzA_not : z ∉ A := by
    intro hzmem
    apply hxA
    have := A.mul_mem hbB.1 hzmem
    rwa [hzdef, mul_inv_cancel_left] at this
  have hz3 : z ^ 3 ≠ 1 := fun h1 => hzA_not (h.mem_A_of_centralizes hzA h1)
  obtain ⟨j, hj⟩ := hQ ⟨z, hzQ⟩
  have hzj : z ^ 3 ^ j = 1 := by simpa using congrArg Subtype.val hj
  obtain ⟨i, -, hi⟩ :=
    (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_iff_pow_eq_one.mpr hzj)
  have hi2 : 2 ≤ i := by
    by_contra hlt
    have hlt' : i < 2 := by omega
    have hdvd : orderOf z ∣ 3 := by
      rw [hi]
      interval_cases i <;> simp
    exact hz3 (orderOf_dvd_iff_pow_eq_one.mp hdvd)
  obtain ⟨y, hydef⟩ : ∃ y : G, y = z ^ 3 ^ (i - 2) := ⟨_, rfl⟩
  have hzord : z ^ 3 ^ i = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hi] at this
  have hy9 : y ^ 9 = 1 := by
    have e9 : 3 ^ (i - 2) * 9 = 3 ^ i := by
      rw [show (9 : ℕ) = 3 ^ 2 from rfl, ← pow_add]
      congr 1
      omega
    rw [hydef, ← pow_mul, e9, hzord]
  have hy3 : y ^ 3 ≠ 1 := by
    intro h1
    have e3 : 3 ^ (i - 2) * 3 = 3 ^ (i - 1) := by
      rw [← pow_succ]
      congr 1
      omega
    have h2 : z ^ 3 ^ (i - 1) = 1 := by
      rw [← e3, pow_mul, ← hydef]
      exact h1
    have h3 : orderOf z ∣ 3 ^ (i - 1) := orderOf_dvd_iff_pow_eq_one.mpr h2
    rw [hi, Nat.pow_dvd_pow_iff_le_right (by norm_num)] at h3
    omega
  have hyA : ∀ a ∈ A, a * y = y * a := by
    intro a ha
    rw [hydef]
    exact ((show Commute a z from hzA a ha).pow_right _).eq
  have hy3mem : y ^ 3 ∈ Subgroup.zpowers c := h.cube_mem_zpowers hyA hy9
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hy3mem
  obtain ⟨d, hdB, hd1⟩ : ∃ d ∈ A ⊓ L, d ≠ 1 := by
    have hnt : Nontrivial (A ⊓ L : Subgroup G) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [h.card_B]; norm_num)
    obtain ⟨d, hd⟩ := exists_ne (1 : (A ⊓ L : Subgroup G))
    exact ⟨d, d.2, fun h1 => hd (Subtype.ext h1)⟩
  have hd3 : d ^ 3 = 1 := h.pow_three_of_mem hdB.1
  obtain ⟨w, hwN, -, hwc⟩ := h.transv d hdB
  have hwinv : w⁻¹ ∈ Subgroup.normalizer (A : Set G) := Subgroup.inv_mem _ hwN
  have hconj : ∀ a ∈ A, w⁻¹ * a * w ∈ A := fun a ha => by
    have := (Subgroup.mem_normalizer_iff.mp hwinv a).mp ha
    rwa [inv_inv] at this
  have conj3 : ∀ (t : G) (n : ℕ), (w * t * w⁻¹) ^ n = w * t ^ n * w⁻¹ := by
    intro t n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ih, pow_succ]; group
  have conjZ : ∀ (t : G) (n : ℤ), (w * t * w⁻¹) ^ n = w * t ^ n * w⁻¹ := by
    intro t n
    have := map_zpow (MulAut.conj w) t n
    simpa [MulAut.conj_apply] using this.symm
  obtain ⟨y', hy'def⟩ : ∃ y' : G, y' = w * y * w⁻¹ := ⟨_, rfl⟩
  have hy'A : ∀ a ∈ A, a * y' = y' * a := by
    intro a ha
    rw [hy'def]
    calc a * (w * y * w⁻¹) = w * ((w⁻¹ * a * w) * y) * w⁻¹ := by group
      _ = w * (y * (w⁻¹ * a * w)) * w⁻¹ := by rw [hyA _ (hconj a ha)]
      _ = (w * y * w⁻¹) * a := by group
  have hy'9 : y' ^ 9 = 1 := by
    rw [hy'def, conj3, hy9, mul_one, mul_inv_cancel]
  have hy'3 : y' ^ 3 = (c * d) ^ m := by
    rw [hy'def, conj3, ← hwc, conjZ, hm]
  have hy'3ne : y' ^ 3 ≠ 1 := by
    intro h1
    apply hy3
    rw [hy'def, conj3] at h1
    calc y ^ 3 = w⁻¹ * (w * y ^ 3 * w⁻¹) * w := by group
      _ = w⁻¹ * 1 * w := by rw [h1]
      _ = 1 := by group
  have hy'3mem : y' ^ 3 ∈ Subgroup.zpowers c := h.cube_mem_zpowers hy'A hy'9
  have ht3 : (y' ^ 3) ^ 3 = 1 := by
    rw [← pow_mul]
    exact hy'9
  have hsemi : SemiconjBy w c (c * d) := mul_inv_eq_iff_eq_mul.mp hwc
  have hcdcard : Nat.card (Subgroup.zpowers (c * d)) = 3 := by
    rw [Nat.card_zpowers, ← SemiconjBy.orderOf_eq w hsemi]
    exact hordc
  have hzp1 : Subgroup.zpowers (y' ^ 3) = Subgroup.zpowers c := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy'3mem)
    rw [hcard, Nat.card_zpowers, orderOf_eq_prime ht3 hy'3ne]
  have hzp2 : Subgroup.zpowers (y' ^ 3) = Subgroup.zpowers (c * d) := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact Subgroup.zpowers_le.mpr (by
        rw [hy'3]; exact (Subgroup.zpowers (c * d)).zpow_mem (Subgroup.mem_zpowers _) m)
    · rw [hcdcard, Nat.card_zpowers, orderOf_eq_prime ht3 hy'3ne]
  have hcd_mem : c * d ∈ Subgroup.zpowers c := by
    rw [← hzp1, hzp2]
    exact Subgroup.mem_zpowers _
  have hdc : d ∈ Subgroup.zpowers c := by
    have := (Subgroup.zpowers c).mul_mem ((Subgroup.zpowers c).inv_mem (Subgroup.mem_zpowers c))
      hcd_mem
    simpa using this
  have hdord : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have hzpd : Subgroup.zpowers d = Subgroup.zpowers c := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdc)
    rw [hcard, Nat.card_zpowers, hdord]
  have hcL : c ∈ L := by
    have hc' : c ∈ Subgroup.zpowers d := by
      rw [hzpd]
      exact Subgroup.mem_zpowers c
    exact (Subgroup.zpowers_le.mpr hdB.2) hc'
  exact h.not_mem hcL

theorem maxInv_pair (h : Pt A c L) : ∃ P Q : Subgroup L,
    maxInvariantPiSubgroups ⊤ ((A ⊓ L).subgroupOf L) (piOf 2) = {P, Q} := by
  obtain ⟨a, b, -, -, -, -, hpair⟩ := KFacts.KP4.m22_maxInvariant_eq_pair h.m22 h.card_B_L
  exact ⟨_, _, (KFacts.KP4.m22_maxInvariant_threePrime_eq_two h.m22 h.card_B_L).symm.trans hpair⟩

theorem inf_centralizer_L (h : Pt A c L) {R : Subgroup G}
    (hR : R ∈ scriptQPiStar A (lB A) L (piOf 2)) :
    R.subgroupOf L ⊓ Subgroup.centralizer (((A ⊓ L).subgroupOf L : Subgroup L) : Set L) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxR, hxC⟩
  have hxG : (x : G) ∈ R := Subgroup.mem_subgroupOf.mp hxR
  have hcomm : (x : G) ∈ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have := Subgroup.mem_centralizer_iff.mp hxC ⟨b, (Subgroup.mem_inf.mp hb).2⟩
      (Subgroup.mem_subgroupOf.mpr hb)
    exact congrArg Subtype.val this
  have h1 : (x : G) ∈ R ⊓ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) := ⟨hxG, hcomm⟩
  rw [(h.R_kp4 hR).2.2.2, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact Subtype.ext h1

theorem eq_one_of_mem_normalizer (h : Pt A c L) {R : Subgroup G}
    (hR : R ∈ scriptQPiStar A (lB A) L (piOf 2)) {x : L} (hxR : x ∈ R.subgroupOf L)
    (hxN : x ∈ Subgroup.normalizer (((A ⊓ L).subgroupOf L : Subgroup L) : Set L)) : x = 1 := by
  obtain ⟨hRL, -, hAR, -⟩ := h.R_facts hR
  have hBR : (A ⊓ L).subgroupOf L ≤
      Subgroup.normalizer ((R.subgroupOf L : Subgroup L) : Set L) :=
    le_normalizer_subgroupOf hRL hAR
  have hxC : x ∈ Subgroup.centralizer (((A ⊓ L).subgroupOf L : Subgroup L) : Set L) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hcB : x * b * x⁻¹ * b⁻¹ ∈ (A ⊓ L).subgroupOf L :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp hxN b).mp hb) (inv_mem hb)
    have hcR : x * b * x⁻¹ * b⁻¹ ∈ R.subgroupOf L := by
      have h2 : b * x⁻¹ * b⁻¹ ∈ R.subgroupOf L :=
        (Subgroup.mem_normalizer_iff.mp (hBR hb) x⁻¹).mp (inv_mem hxR)
      have h3 := mul_mem hxR h2
      simpa only [mul_assoc] using h3
    have hcC : x * b * x⁻¹ * b⁻¹ ∈
        Subgroup.centralizer (((A ⊓ L).subgroupOf L : Subgroup L) : Set L) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b' hb'
      exact h.comm_subgroupOf hb' hcB
    have hc1 : x * b * x⁻¹ * b⁻¹ = 1 := by
      have h4 := h.inf_centralizer_L hR
      rw [eq_bot_iff] at h4
      exact Subgroup.mem_bot.mp (h4 ⟨hcR, hcC⟩)
    have hxb : x * b = b * x := by
      calc x * b = (x * b * x⁻¹ * b⁻¹) * (b * x) := by group
        _ = b * x := by rw [hc1, one_mul]
    exact hxb.symm
  have h5 := h.inf_centralizer_L hR
  rw [eq_bot_iff] at h5
  exact Subgroup.mem_bot.mp (h5 ⟨hxR, hxC⟩)

theorem exists_moves (h : Pt A c L) (hA6 : KF1422AutA6) {R : Subgroup G}
    (hR : R ∈ scriptQPiStar A (lB A) L (piOf 2)) :
    ∃ n ∈ Subgroup.normalizer (((A ⊓ L).subgroupOf L : Subgroup L) : Set L),
      (R.subgroupOf L).map (MulAut.conj n).toMonoidHom ≠ R.subgroupOf L := by
  by_contra hcon
  have hnorm : ∀ n ∈ Subgroup.normalizer (((A ⊓ L).subgroupOf L : Subgroup L) : Set L),
      (R.subgroupOf L).map (MulAut.conj n).toMonoidHom = R.subgroupOf L := fun n hn => by
    by_contra hne
    exact hcon ⟨n, hn, hne⟩
  have hR' : R.subgroupOf L ∈ maxInvariantPiSubgroups ⊤ ((A ⊓ L).subgroupOf L) (piOf 2) :=
    h.mem_maxInvariant hR
  have hNbNr : Subgroup.normalizer (((A ⊓ L).subgroupOf L : Subgroup L) : Set L) ≤
      Subgroup.normalizer ((R.subgroupOf L : Subgroup L) : Set L) := fun n hn =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hnorm n hn)
  obtain ⟨-, ⟨q⟩⟩ := KFacts.KP4.m22_normalizer_quotient h.m22 h.card_B_L hR'
  let f : Subgroup.normalizer ((R.subgroupOf L : Subgroup L) : Set L) →* alternatingGroup (Fin 6) :=
    q.toMonoidHom.comp (QuotientGroup.mk' ((R.subgroupOf L).subgroupOf
      (Subgroup.normalizer ((R.subgroupOf L : Subgroup L) : Set L))))
  have hf_ker : ∀ x : Subgroup.normalizer ((R.subgroupOf L : Subgroup L) : Set L),
      f x = 1 ↔ (x : L) ∈ R.subgroupOf L := by
    intro x
    show q (QuotientGroup.mk' _ x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
  have hφinj : Function.Injective (f.comp (Subgroup.inclusion hNbNr)) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxR : (x : L) ∈ R.subgroupOf L := (hf_ker _).mp hx
    have hx1 : (x : L) = 1 := h.eq_one_of_mem_normalizer hR hxR x.2
    exact Subtype.ext hx1
  have hcardN : Nat.card (Subgroup.normalizer (((A ⊓ L).subgroupOf L : Subgroup L) : Set L)) = 72 :=
    KFacts.KP4.m22_card_normalizer h.m22 h.card_B_L
  have hBle : (A ⊓ L).subgroupOf L ≤
      Subgroup.normalizer (((A ⊓ L).subgroupOf L : Subgroup L) : Set L) := Subgroup.le_normalizer
  have hBLn : Nat.card (((A ⊓ L).subgroupOf L).subgroupOf
      (Subgroup.normalizer (((A ⊓ L).subgroupOf L : Subgroup L) : Set L))) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBle).toEquiv, h.card_B_L]
  have hconj : ∀ (m s : Subgroup.normalizer (((A ⊓ L).subgroupOf L : Subgroup L) : Set L)),
      s ∈ ((A ⊓ L).subgroupOf L).subgroupOf
        (Subgroup.normalizer (((A ⊓ L).subgroupOf L : Subgroup L) : Set L)) →
      m * s * m⁻¹ ∈ ((A ⊓ L).subgroupOf L).subgroupOf
        (Subgroup.normalizer (((A ⊓ L).subgroupOf L : Subgroup L) : Set L)) := by
    intro m s hs
    have hsBL : (s : L) ∈ (A ⊓ L).subgroupOf L := Subgroup.mem_subgroupOf.mp hs
    rw [Subgroup.mem_subgroupOf]
    have := (Subgroup.mem_normalizer_iff.mp m.2 (s : L)).mp hsBL
    simpa using this
  have hTf : Nat.card ((((A ⊓ L).subgroupOf L).subgroupOf
      (Subgroup.normalizer (((A ⊓ L).subgroupOf L : Subgroup L) : Set L))).map
        (f.comp (Subgroup.inclusion hNbNr))) = 9 := by
    rw [Subgroup.card_map_of_injective hφinj, hBLn]
  have hNTf : (⊤ : Subgroup (Subgroup.normalizer
      (((A ⊓ L).subgroupOf L : Subgroup L) : Set L))).map (f.comp (Subgroup.inclusion hNbNr)) ≤
      Subgroup.normalizer (((((A ⊓ L).subgroupOf L).subgroupOf
        (Subgroup.normalizer (((A ⊓ L).subgroupOf L : Subgroup L) : Set L))).map
          (f.comp (Subgroup.inclusion hNbNr)) : Subgroup (alternatingGroup (Fin 6))) :
            Set (alternatingGroup (Fin 6))) := by
    rintro _ ⟨m, -, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨m * s * m⁻¹, hconj m s hs, ?_⟩
      simp only [map_mul, map_inv]
    · rintro ⟨s, hs, hst⟩
      refine ⟨m⁻¹ * s * m, ?_, ?_⟩
      · have := hconj m⁻¹ s hs
        rwa [inv_inv] at this
      · rw [map_mul, map_mul, map_inv, hst]
        group
  have h36 := hA6.2.2.1 _ hTf
  have hle := Subgroup.card_le_of_le hNTf
  rw [Subgroup.card_map_of_injective hφinj, Subgroup.card_top, hcardN, h36] at hle
  norm_num at hle

theorem exists_conj_eq (h : Pt A c L) {g : G} (hgL : g ∈ Subgroup.normalizer (L : Set G)) :
    ∃ l ∈ L, ((A ⊓ L).map (MulAut.conj g).toMonoidHom).map (MulAut.conj l).toMonoidHom =
      A ⊓ L := by
  have hBL : A ⊓ L ≤ L := inf_le_right
  have hBgL : (A ⊓ L).map (MulAut.conj g).toMonoidHom ≤ L := by
    rintro _ ⟨b, hb, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hgL b).mp hb.2
  have hBgcard : Nat.card ((A ⊓ L).map (MulAut.conj g).toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, h.card_B]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := h.m22
  have hfac : (Nat.card L).factorization 3 = 2 := by
    rw [Nat.card_congr e.toEquiv, CFSG.RankThree.Asc83Table.M22.factorization_card]
  have hP : Nat.card ((A ⊓ L).subgroupOf L) = 3 ^ (Nat.card L).factorization 3 := by
    rw [h.card_B_L, hfac]
    norm_num
  have hBg9 : Nat.card (((A ⊓ L).map (MulAut.conj g).toMonoidHom).subgroupOf L) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBgL).toEquiv, hBgcard]
  have hBgp : IsPGroup 3 (((A ⊓ L).map (MulAut.conj g).toMonoidHom).subgroupOf L) := by
    apply IsPGroup.of_card (n := 2)
    rw [hBg9]
    norm_num
  obtain ⟨l, hl⟩ := CFSG.RankThree.Asc83Table.exists_map_conj_le hP hBgp
  have hlc : ((((A ⊓ L).map (MulAut.conj g).toMonoidHom).subgroupOf L).map
      (MulAut.conj l).toMonoidHom) = (A ⊓ L).subgroupOf L := by
    apply Subgroup.eq_of_le_of_card_ge hl
    rw [Subgroup.card_map_of_injective (MulAut.conj l).injective, hBg9, h.card_B_L]
  refine ⟨(l : G), l.2, ?_⟩
  have := congrArg (Subgroup.map L.subtype) hlc
  rw [map_subtype_conj_subgroupOf hBgL, Subgroup.map_subgroupOf_eq_of_le hBL] at this
  exact this

theorem exists_inverting (hA6 : KF1422AutA6) (h : Pt A c L) {R : Subgroup G}
    (hR : R ∈ scriptQPiStar A (lB A) L (piOf 2)) {g : G} (hg : g * c * g⁻¹ = c⁻¹) :
    ∃ u ∈ Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (R : Set G),
      u * c * u⁻¹ = c⁻¹ := by
  obtain ⟨hRL, -, -, -⟩ := h.R_facts hR
  have hgc : g ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    show Subgroup.zpowers (g * c * g⁻¹) = Subgroup.zpowers c
    rw [hg, Subgroup.zpowers_inv]
  have hgL : g ∈ Subgroup.normalizer (L : Set G) := h.normalizer_zpowers_le hgc
  obtain ⟨l, hlL, hlB⟩ := h.exists_conj_eq hgL
  have hlN : (l : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hlL
  have hu₁L : (l : G) * g ∈ Subgroup.normalizer (L : Set G) := mul_mem hlN hgL
  have hlc : Commute c (l : G) :=
    (Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hlL)).symm
  have hu₁c : (l : G) * g * c * ((l : G) * g)⁻¹ = c⁻¹ := by
    calc (l : G) * g * c * ((l : G) * g)⁻¹ = (l : G) * (g * c * g⁻¹) * (l : G)⁻¹ := by group
      _ = (l : G) * c⁻¹ * (l : G)⁻¹ := by rw [hg]
      _ = c⁻¹ := by rw [← (hlc.inv_left).eq, mul_inv_cancel_right]
  have hu₁B : (A ⊓ L).map (MulAut.conj ((l : G) * g)).toMonoidHom = A ⊓ L := by
    rw [map_conj_mul_map, hlB]
  have hu₁A : A.map (MulAut.conj ((l : G) * g)).toMonoidHom = A :=
    h.map_A_eq (by rw [hu₁c, Subgroup.zpowers_inv]) hu₁B
  have hu₁N : (l : G) * g ∈ Subgroup.normalizer (A : Set G) :=
    CFSG.RankThree.PartTwo.Sec14.mem_normalizer_of_map_conj_eq hu₁A
  have hBu₁ : ((A ⊓ L).subgroupOf L).map
      (L.normalizerMonoidHom ⟨(l : G) * g, hu₁L⟩).toMonoidHom = (A ⊓ L).subgroupOf L :=
    map_normalizerMonoidHom_subgroupOf inf_le_right hu₁L hu₁B
  have hRσ := maxInvariant_map_mem (L.normalizerMonoidHom ⟨(l : G) * g, hu₁L⟩) hBu₁
    (h.mem_maxInvariant hR)
  obtain ⟨n, hnN, hnne⟩ := h.exists_moves hA6 hR
  have hBn : ((A ⊓ L).subgroupOf L).map (MulAut.conj n).toMonoidHom = (A ⊓ L).subgroupOf L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hnN
  have hRn := maxInvariant_map_mem (MulAut.conj n) hBn (h.mem_maxInvariant hR)
  obtain ⟨P, Q, hPQ⟩ := h.maxInv_pair
  rcases eq_or_eq_of_pair_mem hPQ (h.mem_maxInvariant hR) hRσ hRn hnne with hY | hY
  ·
    have hRu : R.map (MulAut.conj ((l : G) * g)).toMonoidHom = R := by
      have := congrArg (Subgroup.map L.subtype) hY
      rw [map_subtype_map_aut (σ := L.normalizerMonoidHom ⟨(l : G) * g, hu₁L⟩)
        (u := (l : G) * g) (fun x => rfl), Subgroup.map_subgroupOf_eq_of_le hRL] at this
      exact this
    exact ⟨(l : G) * g, Subgroup.mem_inf.mpr
      ⟨hu₁N, CFSG.RankThree.PartTwo.Sec14.mem_normalizer_of_map_conj_eq hRu⟩, hu₁c⟩
  ·
    have hRu : R.map (MulAut.conj ((l : G) * g)).toMonoidHom =
        R.map (MulAut.conj (n : G)).toMonoidHom := by
      have := congrArg (Subgroup.map L.subtype) hY
      rw [map_subtype_map_aut (σ := L.normalizerMonoidHom ⟨(l : G) * g, hu₁L⟩)
        (u := (l : G) * g) (fun x => rfl),
        map_subtype_map_aut (σ := MulAut.conj n) (u := (n : G)) (fun x => rfl),
        Subgroup.map_subgroupOf_eq_of_le hRL] at this
      exact this
    have hBn' : (A ⊓ L).map (MulAut.conj (n : G)).toMonoidHom = A ⊓ L := by
      have := congrArg (Subgroup.map L.subtype) hBn
      rw [map_subtype_conj_subgroupOf inf_le_right, Subgroup.map_subgroupOf_eq_of_le inf_le_right]
        at this
      exact this
    have hnc : Commute c (n : G) :=
      (Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer n.2)).symm
    have hncc : (n : G) * c * (n : G)⁻¹ = c := by
      rw [← hnc.eq, mul_inv_cancel_right]
    have hnA : (n : G) ∈ Subgroup.normalizer (A : Set G) :=
      CFSG.RankThree.PartTwo.Sec14.mem_normalizer_of_map_conj_eq
        (h.map_A_eq (by rw [hncc]) hBn')
    refine ⟨(n : G)⁻¹ * ((l : G) * g), Subgroup.mem_inf.mpr
      ⟨mul_mem (inv_mem hnA) hu₁N, ?_⟩, ?_⟩
    · apply CFSG.RankThree.PartTwo.Sec14.mem_normalizer_of_map_conj_eq
      rw [map_conj_mul_map, hRu, map_conj_map_conj_inv]
    · calc (n : G)⁻¹ * ((l : G) * g) * c * ((n : G)⁻¹ * ((l : G) * g))⁻¹
          = (n : G)⁻¹ * (((l : G) * g) * c * ((l : G) * g)⁻¹) * (n : G) := by group
        _ = (n : G)⁻¹ * c⁻¹ * (n : G) := by rw [hu₁c]
        _ = c⁻¹ := by
          calc (n : G)⁻¹ * c⁻¹ * (n : G) = (n : G)⁻¹ * (c⁻¹ * (n : G)) := by group
            _ = (n : G)⁻¹ * ((n : G) * c⁻¹) := by rw [(hnc.inv_left).eq]
            _ = c⁻¹ := by group

end Pt

end KP4Cert

end CFSG.RankThree.PartTwo.Sec14.Ronan1422S
