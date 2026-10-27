module

public import CFSG.Quasithin.Background.A1aFStar
public import CFSG.Quasithin.H13.A5Facts1321

public section

namespace CFSG.Quasithin.H13.KGLie

open CFSG.Open CFSG.Quasithin Subgroup

variable {V : Type} [CommGroup V]

@[expose] def commHom (v : MulAut V) : V →* V where
  toFun w := v w * w⁻¹
  map_one' := by simp
  map_mul' x y := by
    rw [map_mul, mul_inv, mul_mul_mul_comm]

theorem mem_ker_commHom {v : MulAut V} {w : V} : w ∈ (commHom v).ker ↔ v w = w := by
  rw [MonoidHom.mem_ker]
  show v w * w⁻¹ = 1 ↔ v w = w
  exact mul_inv_eq_one

theorem fixV_zpowers_eq_ker (v : MulAut V) : fixV (zpowers v) = (commHom v).ker := by
  ext w
  rw [mem_ker_commHom]
  constructor
  · intro h
    exact h v (mem_zpowers v)
  · intro h x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    have hk : ∀ n : ℕ, (v ^ n) w = w := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ', MulAut.mul_apply, ih, h]
    rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
    · rw [zpow_natCast]
      exact hk n
    · rw [zpow_neg, zpow_natCast]
      conv_lhs => rw [← hk n]
      exact MulAut.inv_apply_self _ _ _

variable [Finite V]

theorem index_le_four_of_rkIdx (hV2 : ∀ w : V, w ^ 2 = 1) {C : Subgroup V} (h : rkIdx C ≤ 2) :
    C.index ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 V := fun w => ⟨1, by rw [pow_one]; exact hV2 w⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hdvd : C.index ∣ 2 ^ k := hk ▸ C.index_dvd_card
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  unfold rkIdx at h
  rw [hj, padicValNat.prime_pow] at h
  rw [hj]
  calc 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h
    _ = 4 := by norm_num

theorem comm_of_scalar {L : Subgroup (MulAut V)} (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup V) ⊤)
    {v : MulAut V} (hvL : ∀ l ∈ L, v⁻¹ * l * v ∈ L) (hrk : (commHom v).ker.index ≤ 4)
    (hV : 16 < Nat.card V) {s : MulAut V} (hsL : ∀ l ∈ L, s * l = l * s) : v * s = s * v := by
  set y := v * s * v⁻¹ * s⁻¹ with hy
  have hyL : ∀ l ∈ L, y * l = l * y := by
    intro l hl
    have h1 : s⁻¹ * l = l * s⁻¹ := by
      have := hsL l hl
      calc s⁻¹ * l = s⁻¹ * (l * s) * s⁻¹ := by group
        _ = s⁻¹ * (s * l) * s⁻¹ := by rw [this]
        _ = l * s⁻¹ := by group
    have h2 : s * (v⁻¹ * l * v) = (v⁻¹ * l * v) * s := hsL _ (hvL l hl)
    calc y * l = v * s * v⁻¹ * (s⁻¹ * l) := by rw [hy]; group
      _ = v * s * v⁻¹ * (l * s⁻¹) := by rw [h1]
      _ = v * (s * (v⁻¹ * l * v)) * v⁻¹ * s⁻¹ := by group
      _ = v * ((v⁻¹ * l * v) * s) * v⁻¹ * s⁻¹ := by rw [h2]
      _ = l * y := by rw [hy]; group
  have hinv : XMod.IsInv ↥L (commHom y).ker := by
    intro a x hx
    rw [mem_ker_commHom] at hx ⊢
    show y ((a : MulAut V) x) = (a : MulAut V) x
    have := congrArg (fun f : MulAut V => f x) (hyL a a.2)
    simp only [MulAut.mul_apply] at this
    rw [this, hx]
  rcases hirr.2 _ hinv bot_le le_top with hbot | htop
  · exfalso
    have hle : (commHom v).ker ⊓ ((commHom v).ker.map s.toMonoidHom) ≤ (commHom y).ker := by
      intro w hw
      obtain ⟨hw1, hw2⟩ := mem_inf.1 hw
      obtain ⟨w', hw', rfl⟩ := mem_map.1 hw2
      rw [mem_ker_commHom] at hw1 hw'
      rw [mem_ker_commHom]
      have e1 : (v⁻¹ : MulAut V) w' = w' := by
        calc (v⁻¹ : MulAut V) w' = v⁻¹ (v w') := by rw [hw']
          _ = w' := MulAut.inv_apply_self _ v w'
      show (v * s * v⁻¹ * s⁻¹ : MulAut V) (s w') = s w'
      simp only [MulAut.mul_apply, MulAut.inv_apply_self, e1]
      exact hw1
    have hidx : ((commHom v).ker.map s.toMonoidHom).index = (commHom v).ker.index :=
      Subgroup.index_map_of_bijective s.bijective _
    have h1 : ((commHom v).ker ⊓ ((commHom v).ker.map s.toMonoidHom)).index ≤
        (commHom v).ker.index * ((commHom v).ker.map s.toMonoidHom).index :=
      Subgroup.index_inf_le
    have h2 := Subgroup.index_antitone hle
    rw [hbot, Subgroup.index_bot] at h2
    rw [hidx] at h1
    have : (commHom v).ker.index * (commHom v).ker.index ≤ 16 :=
      (Nat.mul_le_mul hrk hrk).trans (by norm_num)
    omega
  · have hy1 : y = 1 := by
      ext w
      have : w ∈ (commHom y).ker := by rw [htop]; trivial
      rw [mem_ker_commHom] at this
      exact this
    calc v * s = y * (s * v) := by rw [hy]; group
      _ = s * v := by rw [hy1, one_mul]

theorem false_of_scalars {L : Subgroup (MulAut V)} (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup V) ⊤)
    {v : MulAut V} (hv1 : v ≠ 1) (hvL : ∀ l ∈ L, v⁻¹ * l * v ∈ L)
    (hrk : (commHom v).ker.index ≤ 4) (hV : 16 < Nat.card V) {ι : Type} [Finite ι]
    (hι : 7 ≤ Nat.card ι) (m : ι → MulAut V) (hmL : ∀ i, ∀ l ∈ L, m i * l = l * m i)
    (hinj : ∀ u : V, u ≠ 1 → Function.Injective fun i => m i u) : False := by
  classical
  have hcomm : ∀ i, v * m i = m i * v := fun i => comm_of_scalar hirr hvL hrk hV (hmL i)
  obtain ⟨w, hw⟩ : ∃ w : V, v w ≠ w := by
    by_contra h
    push Not at h
    exact hv1 (MulEquiv.ext h)
  set u := v w * w⁻¹ with hu
  have hu1 : u ≠ 1 := fun h => hw (mul_inv_eq_one.1 h)
  have hmem : ∀ i, m i u ∈ (commHom v).range := by
    intro i
    refine ⟨m i w, ?_⟩
    have h1 := congrArg (fun f : MulAut V => f w) (hcomm i)
    simp only [MulAut.mul_apply] at h1
    show v (m i w) * (m i w)⁻¹ = m i u
    rw [hu, map_mul, map_inv, h1]
  have hne : ∀ i, m i u ≠ 1 := fun i h => hu1 ((map_eq_one_iff _ (m i).injective).1 h)
  have hcard : Nat.card ι + 1 ≤ Nat.card (commHom v).range := by
    have hinj' : Function.Injective (fun c : Option ι => match c with
        | none => (⟨1, one_mem _⟩ : ↥(commHom v).range)
        | some i => ⟨m i u, hmem i⟩) := by
      rintro (_ | i) (_ | i') h
      · rfl
      · exfalso
        exact hne i' (congrArg Subtype.val h).symm
      · exfalso
        exact hne i (congrArg Subtype.val h)
      · congr 1
        exact hinj u hu1 (congrArg Subtype.val h)
    have := Nat.card_le_card_of_injective _ hinj'
    rw [Nat.card_congr (Equiv.optionEquivSumPUnit ι), Nat.card_sum] at this
    have hp : Nat.card PUnit.{1} = 1 := Nat.card_unique
    omega
  have hrange : Nat.card (commHom v).range = (commHom v).ker.index :=
    (Subgroup.index_ker (commHom v)).symm
  omega

theorem false_of_cond_scalars (hV2 : ∀ w : V, w ^ 2 = 1) {G L : Subgroup (MulAut V)}
    {v : MulAut V} (hB4 : B4Hyp G L) (hc : A5.Cond1321 G L v) {ι : Type} [Finite ι]
    (hι : 7 ≤ Nat.card ι) (m : ι → MulAut V) (hmL : ∀ i, ∀ l ∈ L, m i * l = l * m i)
    (hinj : ∀ u : V, u ≠ 1 → Function.Injective fun i => m i u) (hV : 16 < Nat.card V) :
    False := by
  have hvL : ∀ l ∈ L, v⁻¹ * l * v ∈ L := by
    intro l hl
    have hvN : v⁻¹ ∈ normalizer (L : Set (MulAut V)) := by
      rw [hB4.2.1]
      exact le_normalizer_quasithinGenFitting G (G.inv_mem hc.mem)
    have := (mem_normalizer_iff.1 hvN l).1 hl
    simpa using this
  have hrk : (commHom v).ker.index ≤ 4 := by
    rw [← fixV_zpowers_eq_ker]
    exact index_le_four_of_rkIdx hV2 hc.rank
  exact false_of_scalars hB4.2.2.2 hc.ne_one hvL hrk hV hι m hmL hinj

end CFSG.Quasithin.H13.KGLie
