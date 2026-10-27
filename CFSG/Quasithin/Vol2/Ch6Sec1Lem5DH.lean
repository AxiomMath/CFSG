module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftOrigRank
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5CentA

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits

theorem sq_or_cube_sl22 : ∀ g : SL22, g ^ 2 = 1 ∨ g ^ 3 = 1 := by decide

theorem exists_conj_mul_sl22 : ∀ x : SL22, x ≠ 1 → x ^ 2 = 1 →
    ∃ g : SL22, g * x * g⁻¹ * x ≠ 1 ∧ (g * x * g⁻¹ * x) ^ 3 = 1 := by decide

theorem eq_bot_of_normal_sl22 {N : Subgroup SL22} (hN : N.Normal) (h2 : IsPGroup 2 N) :
    N = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  have hx2 : x ^ 2 = 1 := by
    rcases sq_or_cube_sl22 x with h | h
    · exact h
    · obtain ⟨k, hk⟩ := h2 ⟨x, hx⟩
      have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have h1 := orderOf_dvd_of_pow_eq_one h
      have h2' := orderOf_dvd_of_pow_eq_one hk'
      have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
      exact absurd (orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.coprime_dvd_left h1 hcop) h2')) hx1
  obtain ⟨g, hg1, hg3⟩ := exists_conj_mul_sl22 x hx1 hx2
  have hmem : g * x * g⁻¹ * x ∈ N := N.mul_mem (hN.conj_mem x hx g) hx
  obtain ⟨k, hk⟩ := h2 ⟨_, hmem⟩
  have hk' : (g * x * g⁻¹ * x) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 := orderOf_dvd_of_pow_eq_one hg3
  have h2' := orderOf_dvd_of_pow_eq_one hk'
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  exact hg1 (orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
    (Nat.Coprime.coprime_dvd_left h1 hcop) h2'))

theorem eq_top_sl22 {A : Subgroup SL22} {a b : SL22} (ha : a ∈ A) (ha1 : a ≠ 1)
    (ha2 : a ^ 2 = 1) (hb : b ∈ A) (hb1 : b ≠ 1) (hb3 : b ^ 3 = 1) : A = ⊤ := by
  have h2 : orderOf a = 2 := orderOf_eq_prime ha2 ha1
  have h3 : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hd2 : 2 ∣ Nat.card A := by
    have := orderOf_dvd_natCard (⟨a, ha⟩ : A)
    rwa [Subgroup.orderOf_mk, h2] at this
  have hd3 : 3 ∣ Nat.card A := by
    have := orderOf_dvd_natCard (⟨b, hb⟩ : A)
    rwa [Subgroup.orderOf_mk, h3] at this
  have hd6 : 6 ∣ Nat.card A := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) hd2 hd3
  have hle : Nat.card A ≤ 6 := by
    rw [← card_sl22]
    exact Subgroup.card_le_card_group A
  apply Subgroup.eq_top_of_card_eq
  rw [card_sl22]
  have hpos : 0 < Nat.card A := Nat.card_pos
  obtain ⟨m, hm⟩ := hd6
  rcases m with _ | _ | m
  · omega
  · omega
  · omega

theorem eq_one_of_comm_inv_sl22 : ∀ v r : SL22, v ^ 3 = 1 → r ≠ 1 → r ^ 2 = 1 →
    v * r = r * v → v = 1 := by decide

theorem eq_bot_of_normal_sl22_sq {N : Subgroup (SL22 × SL22)} (hN : N.Normal)
    (h2 : IsPGroup 2 N) : N = ⊥ := by
  have h1 : N.map (MonoidHom.fst SL22 SL22) = ⊥ :=
    eq_bot_of_normal_sl22 (hN.map _ fun u => ⟨(u, 1), rfl⟩) (h2.map _)
  have h2' : N.map (MonoidHom.snd SL22 SL22) = ⊥ :=
    eq_bot_of_normal_sl22 (hN.map _ fun v => ⟨(1, v), rfl⟩) (h2.map _)
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have e1 : x.1 = 1 := by
    have : x.1 ∈ N.map (MonoidHom.fst SL22 SL22) := ⟨x, hx, rfl⟩
    rwa [h1, Subgroup.mem_bot] at this
  have e2 : x.2 = 1 := by
    have : x.2 ∈ N.map (MonoidHom.snd SL22 SL22) := ⟨x, hx, rfl⟩
    rwa [h2', Subgroup.mem_bot] at this
  exact Prod.ext e1 e2

theorem eq_top_sl22_sq {Y : Subgroup (SL22 × SL22)} (h1 : ∀ u : SL22, (u, 1) ∈ Y)
    (h2 : ∀ v : SL22, (1, v) ∈ Y) : Y = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨u, v⟩ -
  have e : ((u, v) : SL22 × SL22) = (u, 1) * (1, v) := Prod.ext (by simp) (by simp)
  rw [e]
  exact Y.mul_mem (h1 u) (h2 v)

theorem eq_top_sl22_sq_of {Y : Subgroup (SL22 × SL22)} {g r₁ v r₂ : SL22} (hg1 : g ≠ 1)
    (hg3 : g ^ 3 = 1) (hr₁1 : r₁ ≠ 1) (hr₁2 : r₁ ^ 2 = 1) (hv1 : v ≠ 1) (hv3 : v ^ 3 = 1)
    (hr₂1 : r₂ ≠ 1) (hr₂2 : r₂ ^ 2 = 1) (hg : (g, 1) ∈ Y) (hr₁ : (r₁, 1) ∈ Y)
    (hv : (1, v) ∈ Y) (hr₂ : (1, r₂) ∈ Y) : Y = ⊤ := by
  have e1 : Y.comap (MonoidHom.inl SL22 SL22) = ⊤ :=
    eq_top_sl22 (a := r₁) (b := g) hr₁ hr₁1 hr₁2 hg hg1 hg3
  have e2 : Y.comap (MonoidHom.inr SL22 SL22) = ⊤ :=
    eq_top_sl22 (a := r₂) (b := v) hr₂ hr₂1 hr₂2 hv hv1 hv3
  refine eq_top_sl22_sq (fun u => ?_) (fun w => ?_)
  · have : u ∈ Y.comap (MonoidHom.inl SL22 SL22) := by rw [e1]; exact Subgroup.mem_top u
    exact this
  · have : w ∈ Y.comap (MonoidHom.inr SL22 SL22) := by rw [e2]; exact Subgroup.mem_top w
    exact this


variable {G : Type} [Group G] [Finite G]

theorem nonempty_oTwoQuot_ch615 {P : Type*} [Group P] [Finite P] (ρ : P →* SL22)
    (hρs : Function.Surjective ρ) (hker : IsPGroup 2 ρ.ker) :
    Nonempty (oTwoQuot P ≃* Equiv.Perm (Fin 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk : ρ.ker = CFSG.Open.pCore 2 P := by
    apply le_antisymm
    · exact CFSG.LieType.BorelTits.le_pCore (r := 2) ρ.normal_ker hker
    · have h1 := CFSG.LieType.BorelTits.map_pCore_le (r := 2) ρ hρs
      have h2 : CFSG.Open.pCore 2 SL22 = ⊥ := eq_bot_of_normal_sl22
        (CFSG.LieType.BorelTits.pCore_normal (r := 2) (G := SL22))
        (CFSG.LieType.BorelTits.pCore_isPGroup (r := 2) (G := SL22))
      rw [h2, le_bot_iff, Subgroup.map_eq_bot_iff] at h1
      exact h1
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective ρ hρs).trans
      CFSG.QuasithinUnique.Setup.Lift.sl2F2EquivPerm3)⟩

theorem relIndex_sup_eq_relIndex_inf_ch615 {N B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (N : Set G)) : B.relIndex (N ⊔ B) = (N ⊓ B).relIndex N := by
  have h1 : (B ⊓ N).relIndex B * B.relIndex (N ⊔ B) = (B ⊓ N).relIndex (N ⊔ B) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left le_sup_right
  have h2 : (B ⊓ N).relIndex N * N.relIndex (N ⊔ B) = (B ⊓ N).relIndex (N ⊔ B) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right le_sup_left
  have h3 : N.relIndex (N ⊔ B) = (B ⊓ N).relIndex B := by
    rw [sup_comm, A4.relIndex_sup_eq_of_le_normalizer' hB]
    exact (Subgroup.inf_relIndex_left B N).symm
  have h4 : 0 < (B ⊓ N).relIndex B :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := ((B ⊓ N).subgroupOf B)))
  have h5 : B.relIndex (N ⊔ B) = (B ⊓ N).relIndex N := by
    refine Nat.eq_of_mul_eq_mul_left h4 ?_
    rw [h1, ← h2, h3, mul_comm]
  rw [h5, inf_comm]

theorem isSylowTwoOf_sup_ch615 {K B S : Subgroup G} (hBS : B ≤ S) (hS2 : IsPGroup 2 S)
    (hSK : S ≤ Subgroup.normalizer (K : Set G)) (hB : IsSylowTwoOf B (K ⊔ B)) :
    IsSylowTwoOf S (K ⊔ S) := by
  refine ⟨le_sup_right, hS2, ?_⟩
  show ¬ 2 ∣ S.relIndex (K ⊔ S)
  rw [relIndex_sup_eq_relIndex_inf_ch615 hSK]
  have h2 : ¬ 2 ∣ B.relIndex (K ⊔ B) := hB.2.2
  rw [relIndex_sup_eq_relIndex_inf_ch615 (hBS.trans hSK)] at h2
  have h3 : (K ⊓ B).relIndex (K ⊓ S) * (K ⊓ S).relIndex K = (K ⊓ B).relIndex K :=
    Subgroup.relIndex_mul_relIndex _ _ _ (inf_le_inf_left K hBS) inf_le_left
  intro hd
  exact h2 (h3 ▸ Dvd.dvd.mul_left hd _)

theorem charTwo_of_le_ch615 {Y P : Subgroup G} (hYP : Y ≤ P) (hP : CharTwo P)
    (hR : pCoreOf 2 P ≤ Y) : CharTwo Y := CFSG.QuasithinUnique.CharTwo.of_pCoreOf_le hP hYP hR

end CFSG.Quasithin.H13
