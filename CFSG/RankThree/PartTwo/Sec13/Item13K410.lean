module

public import CFSG.RankThree.PartTwo.Sec13.Item13Inputs
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseIc
import CFSG.RankThree.PartTwo.Sec10.HWNormalizes

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Matrix
open CFSG.Assembly.RankThreeEven (projImage)

section Semidirect

variable {M : Type*} [Group M] {T : Subgroup M} {w : M}

theorem exists_mul_pow_of_mem_sup (hw3 : w ^ 3 = 1) (hwT : ∀ t ∈ T, w * t * w⁻¹ ∈ T)
    {x : M} (hx : x ∈ T ⊔ Subgroup.zpowers w) : ∃ t ∈ T, ∃ m < 3, x = t * w ^ m := by
  have hwTk : ∀ k : ℕ, ∀ t ∈ T, w ^ k * t * (w ^ k)⁻¹ ∈ T := by
    intro k
    induction k with
    | zero => intro t ht; simpa using ht
    | succ k ih =>
      intro t ht
      have := hwT _ (ih t ht)
      rw [pow_succ']
      simpa [mul_assoc] using this
  have hinv : ∀ k : ℕ, (w ^ k)⁻¹ = w ^ (2 * k) := fun k => by
    rw [inv_eq_iff_mul_eq_one, ← pow_add, show k + 2 * k = 3 * k by ring, pow_mul, hw3, one_pow]
  let S : Subgroup M :=
    { carrier := {x | ∃ t ∈ T, ∃ m : ℕ, x = t * w ^ m}
      mul_mem' := by
        rintro _ _ ⟨t, ht, m, rfl⟩ ⟨t', ht', m', rfl⟩
        refine ⟨t * (w ^ m * t' * (w ^ m)⁻¹), T.mul_mem ht (hwTk m t' ht'), m + m', ?_⟩
        rw [pow_add]
        group
      one_mem' := ⟨1, T.one_mem, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨t, ht, m, rfl⟩
        refine ⟨w ^ (2 * m) * t⁻¹ * (w ^ (2 * m))⁻¹, hwTk _ _ (T.inv_mem ht), 2 * m, ?_⟩
        rw [_root_.mul_inv_rev, hinv]
        group }
  have hle : T ⊔ Subgroup.zpowers w ≤ S := sup_le (fun t ht => ⟨t, ht, 0, by simp⟩)
    (Subgroup.zpowers_le.mpr ⟨1, T.one_mem, 1, by simp⟩)
  obtain ⟨t, ht, m, rfl⟩ := hle hx
  refine ⟨t, ht, m % 3, Nat.mod_lt _ (by norm_num), ?_⟩
  conv_lhs => rw [← Nat.div_add_mod m 3, pow_add, pow_mul, hw3, one_pow, one_mul]

theorem pow_three_mem_of_mem_sup (hw3 : w ^ 3 = 1) (hwT : ∀ t ∈ T, w * t * w⁻¹ ∈ T)
    {x : M} (hx : x ∈ T ⊔ Subgroup.zpowers w) : x ^ 3 ∈ T := by
  obtain ⟨t, ht, m, -, rfl⟩ := exists_mul_pow_of_mem_sup hw3 hwT hx
  have hwTk : ∀ k : ℕ, ∀ t ∈ T, w ^ k * t * (w ^ k)⁻¹ ∈ T := by
    intro k
    induction k with
    | zero => intro t ht; simpa using ht
    | succ k ih =>
      intro t ht
      have := hwT _ (ih t ht)
      rw [pow_succ']
      simpa [mul_assoc] using this
  have e : (t * w ^ m) ^ 3 = t * (w ^ m * t * (w ^ m)⁻¹) * (w ^ (2 * m) * t * (w ^ (2 * m))⁻¹) *
      (w ^ 3) ^ m := by
    rw [← pow_mul, show 3 * m = m + m + m by ring, pow_add, pow_add,
      show 2 * m = m + m by ring, pow_add, pow_three]
    group
  rw [e, hw3, one_pow, mul_one]
  exact T.mul_mem (T.mul_mem ht (hwTk m t ht)) (hwTk (2 * m) t ht)

end Semidirect

section Torus

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem card_slPi_inf_center (hK : PiField π p f K) (hq : ModThree π (p ^ f)) :
    Nat.card (slPi π 3 (p ^ f) K ⊓ Subgroup.center (GL (Fin 3) K) : Subgroup _) = 3 := by
  have := hK.finite
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  apply le_antisymm
  · have hex : ∀ z : (slPi π 3 (p ^ f) K ⊓ Subgroup.center (GL (Fin 3) K) : Subgroup _),
        ∃ k : Fin 3, ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          τ ^ (k : ℕ) • (1 : Matrix (Fin 3) (Fin 3) K) := fun z =>
      exists_tau_pow_of_mem_center hK hq hτ hτ1 z.2.1 fun x _ =>
        (Subgroup.mem_center_iff.mp z.2.2 x).symm
    choose k hk using hex
    refine (Nat.card_le_card_of_injective k fun z z' hzz' => ?_).trans (by rw [Nat.card_fin])
    exact Subtype.ext (Units.ext (by rw [hk z, hk z', hzz']))
  · set τu : Kˣ := Units.mk0 τ hτ0
    have hτu3 : (τu : K) ^ 3 = 1 := hτ
    have hmem : GeneralLinearGroup.scalar (Fin 3) τu ∈
        slPi π 3 (p ^ f) K ⊓ Subgroup.center (GL (Fin 3) K) := by
      refine ⟨scalar_mem_slPi_of_cube hK hq hτu3, ?_⟩
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨τu, rfl⟩
    have hord : orderOf (GeneralLinearGroup.scalar (Fin 3) τu) = 3 := by
      rw [orderOf_injective _ scalar_injective_three]
      rcases Nat.prime_three.eq_one_or_self_of_dvd _
        (orderOf_dvd_of_pow_eq_one (Units.ext (by
          rw [Units.val_pow_eq_pow_val, hτu3, Units.val_one]) : τu ^ 3 = 1)) with h | h
      · exact absurd (Units.ext_iff.mp (orderOf_eq_one_iff.mp h)) hτ1
      · exact h
    have := Subgroup.card_le_of_le (Subgroup.zpowers_le.mpr hmem)
    rwa [Nat.card_zpowers, hord] at this

theorem torus_card (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f) {N : ℕ}
    (hN : N = qSubPi π ((p ^ f) ^ 3) / qSubPi π (p ^ f)) :
    ∃ n : ℕ, N = 3 * n ∧ n % 3 = 1 ∧ 7 ≤ n := by
  have h0 := qSubPi_ne_zero hK hq
  rw [qSubPi_cube_eq hq, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero h0)] at hN
  refine ⟨3 * (p ^ f / 3) ^ 2 + 3 * (p ^ f / 3) + 1, hN, by omega, ?_⟩
  have : 1 ≤ p ^ f / 3 := by omega
  nlinarith

theorem mul_mem_of_mem_centMod {L : Subgroup (GL (Fin 3) K)} {y g t : GL (Fin 3) K}
    (hg : g ∈ centMod L y) (ht : t ∈ L ⊓ Subgroup.centralizer ({y} : Set (GL (Fin 3) K))) :
    g * t * g⁻¹ ∈ L ⊓ Subgroup.centralizer ({y} : Set (GL (Fin 3) K)) := by
  obtain ⟨hgL, z, hz, hgy⟩ := mem_centMod_iff_scalar.mp hg
  refine Subgroup.mem_inf.mpr ⟨L.mul_mem (L.mul_mem hgL ht.1) (L.inv_mem hgL), ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hzc : ∀ x : GL (Fin 3) K, x * z = z * x := fun x => commute_of_mem_statedScalars hz x
  have hzc' : ∀ x : GL (Fin 3) K, x * z⁻¹ = z⁻¹ * x := fun x => by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, hzc x, inv_mul_cancel_left]
  have hty : t * y = y * t := Subgroup.mem_centralizer_singleton_iff.mp ht.2
  have hy : y = z⁻¹ * (g * y * g⁻¹) := by rw [hgy]; group
  calc g * t * g⁻¹ * y = g * t * g⁻¹ * (z⁻¹ * (g * y * g⁻¹)) := by rw [← hy]
    _ = z⁻¹ * (g * t * g⁻¹) * (g * y * g⁻¹) := by
        rw [← mul_assoc, hzc' (g * t * g⁻¹)]
    _ = z⁻¹ * (g * (t * y) * g⁻¹) := by group
    _ = z⁻¹ * (g * (y * t) * g⁻¹) := by rw [hty]
    _ = z⁻¹ * (g * y * g⁻¹) * (g * t * g⁻¹) := by group
    _ = y * (g * t * g⁻¹) := by rw [← hy]

theorem false_of_inverts_torus (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    {y : GL (Fin 3) K}
    (hcyc : IsCyclic ↥(slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y}))
    (hcard : Nat.card ↥(slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y}) =
      qSubPi π ((p ^ f) ^ 3) / qSubPi π (p ^ f))
    {w : GL (Fin 3) K} (hw3 : orderOf w = 3)
    (hcent : centMod (slPi π 3 (p ^ f) K) y =
      (slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y}) ⊔ Subgroup.zpowers w)
    (hcard3 : Nat.card ↥(slPi π 3 (p ^ f) K ⊓
      Subgroup.centralizer ({y, w} : Set (GL (Fin 3) K))) = 3)
    {l : GL (Fin 3) K} (hlc : l ∈ centMod (slPi π 3 (p ^ f) K) y)
    (hl1 : ProjGenLinGroup.mk l ≠ 1) (hl3 : ProjGenLinGroup.mk l ^ 3 = 1)
    (β : projImage (slPi π 3 (p ^ f) K) →* projImage (slPi π 3 (p ^ f) K))
    (hβinj : Function.Injective β)
    (hβC : ∀ s : projImage (slPi π 3 (p ^ f) K),
      ProjGenLinGroup.mk y * (s : ProjGenLinGroup (Fin 3) K) = s * ProjGenLinGroup.mk y →
        ProjGenLinGroup.mk y * (β s : ProjGenLinGroup (Fin 3) K) = β s * ProjGenLinGroup.mk y)
    (hβl : β ⟨ProjGenLinGroup.mk l, ⟨l, hlc.1, rfl⟩⟩ =
      (⟨ProjGenLinGroup.mk l, ⟨l, hlc.1, rfl⟩⟩ : projImage (slPi π 3 (p ^ f) K))⁻¹) :
    False := by
  have := hK.finite
  set T := slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer ({y} : Set (GL (Fin 3) K)) with hT
  have hw3' : w ^ 3 = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw3] at this
  have hwc : w ∈ centMod (slPi π 3 (p ^ f) K) y :=
    hcent ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
  have hwT : ∀ t ∈ T, w * t * w⁻¹ ∈ T := fun t ht => mul_mem_of_mem_centMod hwc ht
  let mkT : T →* projImage (slPi π 3 (p ^ f) K) :=
    (ProjGenLinGroup.mk.comp T.subtype).codRestrict (projImage (slPi π 3 (p ^ f) K)) fun t =>
    ⟨t, t.2.1, rfl⟩
  set Tbar := mkT.range with hTbar
  have hmkT : ∀ t : T, ((mkT t : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk t :=
    fun t => rfl
  have hkerEq : mkT.ker = (Subgroup.center (GL (Fin 3) K)).subgroupOf T := by
    ext t
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact ProjGenLinGroup.mk_eq_one.mp (congrArg Subtype.val h)
    · intro h
      exact Subtype.ext (ProjGenLinGroup.mk_eq_one.mpr h)
  have hker : Nat.card mkT.ker = 3 := by
    have hZT : Subgroup.center (GL (Fin 3) K) ⊓ T =
        slPi π 3 (p ^ f) K ⊓ Subgroup.center (GL (Fin 3) K) := by
      ext z
      constructor
      · rintro ⟨hz, hzT⟩
        exact ⟨hzT.1, hz⟩
      · rintro ⟨hzP, hz⟩
        exact ⟨hz, hzP, Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_center_iff.mp hz y).symm⟩
    rw [hkerEq, ← Subgroup.inf_subgroupOf_right,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, hZT]
    exact card_slPi_inf_center hK hq
  obtain ⟨n, hTn, hn3, hn7⟩ := torus_card hK hq hq2 hcard
  have hTbarcard : Nat.card Tbar = n := by
    have h1 := Subgroup.card_mul_index mkT.ker
    rw [Subgroup.index_ker, hker, hTn] at h1
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h1
  have hcop : Nat.Coprime 3 n := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    omega
  set Cent := (Subgroup.centralizer ({ProjGenLinGroup.mk y} :
    Set (ProjGenLinGroup (Fin 3) K))).subgroupOf (projImage (slPi π 3 (p ^ f) K)) with hCent
  have hmemCent : ∀ s : projImage (slPi π 3 (p ^ f) K), s ∈ Cent ↔
      ProjGenLinGroup.mk y * (s : ProjGenLinGroup (Fin 3) K) = s * ProjGenLinGroup.mk y := by
    intro s
    rw [hCent, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    exact eq_comm
  have hTC : Tbar ≤ Cent := by
    rintro _ ⟨t, rfl⟩
    rw [hmemCent, hmkT, ← map_mul, ← map_mul,
      (Subgroup.mem_centralizer_singleton_iff.mp t.2.2).symm]
  have hmkcomm : ∀ g : GL (Fin 3) K, ProjGenLinGroup.mk y * ProjGenLinGroup.mk g =
      ProjGenLinGroup.mk g * ProjGenLinGroup.mk y →
        g * y * g⁻¹ * y⁻¹ ∈ StatedScalars (Fin 3) K := by
    intro g h1
    have h2 : ProjGenLinGroup.mk (g * y * g⁻¹ * y⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
      group
    have h3 := ProjGenLinGroup.mk_eq_one.mp h2
    rwa [Matrix.GeneralLinearGroup.center_eq_range_scalar] at h3
  have hcentMod : ∀ g ∈ slPi π 3 (p ^ f) K, ProjGenLinGroup.mk y * ProjGenLinGroup.mk g =
      ProjGenLinGroup.mk g * ProjGenLinGroup.mk y → g ∈ centMod (slPi π 3 (p ^ f) K) y :=
    fun g hg h1 =>
    mem_centMod_iff_scalar.mpr ⟨hg, g * y * g⁻¹ * y⁻¹, hmkcomm g h1, by group⟩
  have hC3 : ∀ s ∈ Cent, s ^ 3 ∈ Tbar := by
    intro s hs
    obtain ⟨_, ⟨g, hg, rfl⟩⟩ := s
    have hgc := hcentMod g hg ((hmemCent _).mp hs)
    have hg3 := pow_three_mem_of_mem_sup hw3' hwT (hcent ▸ hgc)
    exact ⟨⟨g ^ 3, hg3⟩, Subtype.ext (by simp [hmkT])⟩
  have hchar : ∀ s : projImage (slPi π 3 (p ^ f) K), s ∈ Tbar ↔ s ∈ Cent ∧ s ^ n = 1 := by
    intro s
    constructor
    · intro hs
      refine ⟨hTC hs, ?_⟩
      have := pow_card_eq_one' (G := Tbar) (x := ⟨s, hs⟩)
      rw [hTbarcard] at this
      exact congrArg Subtype.val this
    · rintro ⟨hs, hsn⟩
      obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * 3 + v * n = 1 := by
        have := Nat.isCoprime_iff_coprime.mpr hcop
        obtain ⟨u, v, h⟩ := this
        exact ⟨u, v, by exact_mod_cast h⟩
      have e : s = (s ^ 3) ^ u * (s ^ n) ^ v := by
        rw [← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul,
          ← _root_.zpow_add, show ((3 : ℕ) : ℤ) * u + (n : ℤ) * v = 1 by push_cast; linarith,
          zpow_one]
      rw [e, hsn, _root_.one_zpow, mul_one]
      exact Tbar.zpow_mem (hC3 s hs) u
  set lbar : projImage (slPi π 3 (p ^ f) K) := ⟨ProjGenLinGroup.mk l, ⟨l, hlc.1, rfl⟩⟩ with hlbar
  have hlC : lbar ∈ Cent := by
    rw [hmemCent]
    obtain ⟨-, z, hz, hly⟩ := mem_centMod_iff_scalar.mp hlc
    have h1 : ProjGenLinGroup.mk l * ProjGenLinGroup.mk y * (ProjGenLinGroup.mk l)⁻¹ =
        ProjGenLinGroup.mk y := by
      rw [← map_inv, ← map_mul, ← map_mul, hly, map_mul]
      have : ProjGenLinGroup.mk z = 1 := ProjGenLinGroup.mk_eq_one.mpr (by
        rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
        exact hz)
      rw [this, one_mul]
    change ProjGenLinGroup.mk y * ProjGenLinGroup.mk l = ProjGenLinGroup.mk l * ProjGenLinGroup.mk y
    calc ProjGenLinGroup.mk y * ProjGenLinGroup.mk l =
        ProjGenLinGroup.mk l * ProjGenLinGroup.mk y * (ProjGenLinGroup.mk l)⁻¹ *
          ProjGenLinGroup.mk l := by rw [h1]
      _ = _ := by group
  have hβT : ∀ s ∈ Tbar, β s ∈ Tbar := by
    intro s hs
    obtain ⟨hsC, hsn⟩ := (hchar s).mp hs
    refine (hchar _).mpr ⟨(hmemCent _).mpr (hβC s ((hmemCent s).mp hsC)), ?_⟩
    rw [← map_pow, hsn, map_one]
  have hconjT : ∀ g ∈ Cent, ∀ s ∈ Tbar, g * s * g⁻¹ ∈ Tbar := by
    intro g hg s hs
    obtain ⟨hsC, hsn⟩ := (hchar s).mp hs
    refine (hchar _).mpr ⟨Cent.mul_mem (Cent.mul_mem hg hsC) (Cent.inv_mem hg), ?_⟩
    rw [conj_pow, hsn, mul_one, mul_inv_cancel]
  have hTbarcyc : IsCyclic Tbar := isCyclic_of_surjective mkT.rangeRestrict
    mkT.rangeRestrict_surjective
  obtain ⟨g₀, hg₀⟩ := hTbarcyc.exists_generator
  have hpow : ∀ x ∈ Tbar, ∃ k : ℤ, x = (g₀ : projImage (slPi π 3 (p ^ f) K)) ^ k := fun x hx => by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg₀ ⟨x, hx⟩)
    exact ⟨k, by simpa using (congrArg Subtype.val hk).symm⟩
  obtain ⟨b, hb⟩ := hpow _ (hβT _ g₀.2)
  obtain ⟨d₁, hd₁⟩ := hpow _ (hconjT _ hlC _ g₀.2)
  obtain ⟨d₂, hd₂⟩ := hpow _ (hconjT _ (Cent.inv_mem hlC) _ g₀.2)
  have hβl' : β lbar = lbar⁻¹ := hβl
  rw [inv_inv] at hd₂
  set g := (g₀ : projImage (slPi π 3 (p ^ f) K)) with hg
  have key : β (g ^ d₁) = β (g ^ d₂) := by
    calc β (g ^ d₁) = β (lbar * g * lbar⁻¹) := by rw [hd₁]
      _ = lbar⁻¹ * β g * lbar := by rw [map_mul, map_mul, map_inv, hβl', inv_inv]
      _ = lbar⁻¹ * g ^ b * lbar := by rw [hb]
      _ = (lbar⁻¹ * g * lbar) ^ b := by
          rw [show lbar⁻¹ * g * lbar = lbar⁻¹ * g * lbar⁻¹⁻¹ by rw [inv_inv], conj_zpow, inv_inv]
      _ = (g ^ d₂) ^ b := by rw [hd₂]
      _ = (g ^ b) ^ d₂ := by rw [← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]
      _ = β g ^ d₂ := by rw [hb]
      _ = β (g ^ d₂) := (map_zpow β g d₂).symm
  have hcomm₀ : lbar * g * lbar⁻¹ = lbar⁻¹ * g * lbar := by rw [hd₁, hd₂, hβinj key]
  have hl3' : lbar ^ 3 = 1 := Subtype.ext hl3
  have hlg : lbar * g = g * lbar := by
    have h2 : lbar ^ 2 * g * (lbar ^ 2)⁻¹ = g := by
      calc lbar ^ 2 * g * (lbar ^ 2)⁻¹ = lbar * (lbar * g * lbar⁻¹) * lbar⁻¹ := by
            rw [sq, _root_.mul_inv_rev]; group
        _ = lbar * (lbar⁻¹ * g * lbar) * lbar⁻¹ := by rw [hcomm₀]
        _ = g := by group
    have e : lbar = (lbar ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hl3', one_mul, pow_one]
    have h3 : lbar ^ 2 * g = g * lbar ^ 2 := by
      calc lbar ^ 2 * g = lbar ^ 2 * g * (lbar ^ 2)⁻¹ * lbar ^ 2 := by group
        _ = g * lbar ^ 2 := by rw [h2]
    rw [e]
    exact ((Commute.pow_left h3 2)).eq
  have hlT : ∀ x ∈ Tbar, lbar * x = x * lbar := by
    intro x hx
    obtain ⟨k, rfl⟩ := hpow x hx
    exact (Commute.zpow_right hlg k).eq
  obtain ⟨t₀, ht₀, m, hm3, hlm⟩ := exists_mul_pow_of_mem_sup hw3' hwT (hcent ▸ hlc)
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hlm
    have hlTbar : lbar ∈ Tbar := ⟨⟨l, hlm ▸ ht₀⟩, Subtype.ext rfl⟩
    obtain ⟨-, hln⟩ := (hchar lbar).mp hlTbar
    have hord : orderOf lbar ∣ 1 := by
      rw [← Nat.Coprime.gcd_eq_one hcop]
      exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hl3') (orderOf_dvd_of_pow_eq_one hln)
    apply hl1
    have := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hord)
    exact congrArg Subtype.val this
  have hTcomm : ∀ a b : T, a * b = b * a := fun a b => by
    have := hcyc
    exact (IsCyclic.commGroup (α := T)).mul_comm a b
  have hcen : ∀ t ∈ T, l * t * l⁻¹ * t⁻¹ ∈ Subgroup.center (GL (Fin 3) K) := by
    intro t ht
    have h1 := hlT _ ⟨⟨t, ht⟩, rfl⟩
    have h2 : ProjGenLinGroup.mk l * ProjGenLinGroup.mk t =
        ProjGenLinGroup.mk t * ProjGenLinGroup.mk l := congrArg Subtype.val h1
    refine ProjGenLinGroup.mk_eq_one.mp ?_
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h2]
    group
  have hcen' : ∀ x : GL (Fin 3) K, x ∈ Subgroup.center (GL (Fin 3) K) →
      ∀ z : GL (Fin 3) K, x * z = z * x := fun x hx z =>
    (Subgroup.mem_center_iff.mp hx z).symm
  let φ : T →* T :=
    { toFun := fun t => ⟨l * t * l⁻¹ * (t : GL (Fin 3) K)⁻¹,
        T.mul_mem (mul_mem_of_mem_centMod hlc t.2) (T.inv_mem t.2)⟩
      map_one' := by ext; simp
      map_mul' := fun s t => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        have ht := hcen' _ (hcen t t.2)
        have e1 : l * ((s : GL (Fin 3) K) * t) * l⁻¹ * ((s : GL (Fin 3) K) * t)⁻¹ =
            (l * s * l⁻¹ * (s : GL (Fin 3) K)⁻¹) *
              ((s : GL (Fin 3) K) * (l * t * l⁻¹ * (t : GL (Fin 3) K)⁻¹) *
                (s : GL (Fin 3) K)⁻¹) := by
          group
        rw [e1, ← ht (s : GL (Fin 3) K), mul_inv_cancel_right] }
  have hrange : Nat.card φ.range ≤ 3 := by
    calc Nat.card φ.range ≤ Nat.card ((Subgroup.center (GL (Fin 3) K)).subgroupOf T) :=
          Subgroup.card_le_of_le fun x hx => by
            obtain ⟨t, rfl⟩ := hx
            exact Subgroup.mem_subgroupOf.mpr (hcen t t.2)
      _ = Nat.card mkT.ker := by rw [hkerEq]
      _ = 3 := hker
  have hkerφ : Nat.card φ.ker ≤ 3 := by
    refine (Nat.card_le_card_of_injective (fun t => (⟨t.1, t.1.2.1, ?_⟩ :
      (slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer ({y, w} : Set (GL (Fin 3) K)) : Subgroup _)))
      ?_).trans_eq hcard3
    · have htl : l * t.1 * l⁻¹ * (t.1 : GL (Fin 3) K)⁻¹ = 1 :=
        congrArg Subtype.val (MonoidHom.mem_ker.mp t.2)
      have htl' : (t.1 : GL (Fin 3) K) * l = l * t.1 := by
        calc (t.1 : GL (Fin 3) K) * l =
            (l * t.1 * l⁻¹ * (t.1 : GL (Fin 3) K)⁻¹)⁻¹ * (l * t.1) := by group
          _ = l * t.1 := by rw [htl, inv_one, one_mul]
      have ht₀t : (t.1 : GL (Fin 3) K) * t₀ = t₀ * t.1 :=
        congrArg Subtype.val (hTcomm t.1 ⟨t₀, ht₀⟩)
      have htwm : (t.1 : GL (Fin 3) K) * w ^ m = w ^ m * t.1 := by
        have h1 : t₀ * ((t.1 : GL (Fin 3) K) * w ^ m) = t₀ * (w ^ m * t.1) := by
          calc t₀ * ((t.1 : GL (Fin 3) K) * w ^ m) = (t₀ * t.1) * w ^ m := by group
            _ = (t.1 * t₀) * w ^ m := by rw [ht₀t]
            _ = t.1 * l := by rw [hlm]; group
            _ = l * t.1 := htl'
            _ = t₀ * (w ^ m * t.1) := by rw [hlm]; group
        exact mul_left_cancel h1
      have htw : (t.1 : GL (Fin 3) K) * w = w * t.1 := by
        interval_cases m
        · exact absurd rfl hm0
        · simpa using htwm
        · have e : w = (w ^ 2) ^ 2 := by
            rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hw3', one_mul, pow_one]
          rw [e]
          exact ((Commute.pow_right htwm 2)).eq
      change (t.1 : GL (Fin 3) K) ∈ Subgroup.centralizer ({y, w} : Set (GL (Fin 3) K))
      rw [Subgroup.mem_centralizer_iff]
      rintro z (rfl | rfl)
      · exact (Subgroup.mem_centralizer_singleton_iff.mp t.1.2.2).symm
      · exact htw.symm
    · intro a b hab
      have h1 : ((a : T) : GL (Fin 3) K) = ((b : T) : GL (Fin 3) K) :=
        congrArg (fun z : (slPi π 3 (p ^ f) K ⊓
          Subgroup.centralizer ({y, w} : Set (GL (Fin 3) K)) : Subgroup _) =>
            (z : GL (Fin 3) K)) hab
      exact Subtype.ext (Subtype.ext h1)
  have hTle : Nat.card T ≤ 9 := by
    have h1 := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker] at h1
    rw [← h1]
    calc Nat.card φ.ker * Nat.card φ.range ≤ 3 * 3 := Nat.mul_le_mul hkerφ hrange
      _ = 9 := by norm_num
  omega

theorem not_irreducible_of_commute_type2 (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {x y : GL (Fin 3) K} (hx : Type123 π (p ^ f) K x 2)
    (hyx : y * x * y⁻¹ * x⁻¹ ∈ StatedScalars (Fin 3) K) :
    ¬ ∀ W : Submodule K (Fin 3 → K), (∀ v ∈ W, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) →
      W = ⊥ ∨ W = ⊤ := by
  intro hirr
  obtain ⟨e, he3, he1, z, hz, g, hg, hD⟩ := hx
  have hτ1 : (e : K) ≠ 1 := fun h => he1 (Units.ext h)
  obtain ⟨ζ, hζ⟩ := hyx
  have hzs : z ∈ StatedScalars (Fin 3) K := mem_statedScalars_of_mem_zPi hK hq he3 hτ1 hz
  set x' := x * z with hx'
  have hx'2 : Type123 π (p ^ f) K x' 2 :=
    ⟨e, he3, he1, 1, one_mem _, g, hg, by rw [mul_one]; exact hD⟩
  have hyx' : y * x' * y⁻¹ = x' * GeneralLinearGroup.scalar (Fin 3) ζ := by
    have h1 : y * x * y⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * x := by
      rw [hζ]; group
    have hzc := commute_of_mem_statedScalars hzs
    have hζc := fun g : GL (Fin 3) K => commute_of_mem_statedScalars
      (⟨ζ, rfl⟩ : GeneralLinearGroup.scalar (Fin 3) ζ ∈ StatedScalars (Fin 3) K) g
    calc y * x' * y⁻¹ = y * x * (z * y⁻¹) := by rw [hx']; group
      _ = y * x * (y⁻¹ * z) := by rw [← hzc y⁻¹]
      _ = y * x * y⁻¹ * z := by group
      _ = GeneralLinearGroup.scalar (Fin 3) ζ * x * z := by rw [h1]
      _ = GeneralLinearGroup.scalar (Fin 3) ζ * (x * z) := by group
      _ = x' * GeneralLinearGroup.scalar (Fin 3) ζ := (hζc (x * z)).symm
  have htr := trace_inv_conj y⁻¹ x'
  rw [inv_inv, hyx', trace_mul_scalar] at htr
  have hne := trace_ne_zero_of_type2 hK hq hx'2
  have hζ1 : (ζ : K) = 1 := by
    have := mul_right_cancel₀ hne (htr.trans (one_mul _).symm)
    exact this
  have hζ1' : ζ = 1 := Units.ext hζ1
  rw [hζ1', map_one, mul_one] at hyx'
  have hcomm : y * x' = x' * y := by
    calc y * x' = y * x' * y⁻¹ * y := by group
      _ = x' * y := by rw [hyx']
  set M := ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hM
  have hMD : M * diagonal ![(e : K), 1, 1] = diagonal ![(e : K), 1, 1] * M := by
    rw [hM, ← coe_diagE, ← hD, ← Units.val_mul, ← Units.val_mul]
    congr 1
    calc g⁻¹ * y * g * (g⁻¹ * x' * g) = g⁻¹ * (y * x') * g := by group
      _ = g⁻¹ * (x' * y) * g := by rw [hcomm]
      _ = g⁻¹ * x' * g * (g⁻¹ * y * g) := by group
  have hdi : ∀ i : Fin 3, i ≠ 0 → (![(e : K), 1, 1] : Fin 3 → K) i = 1 := by
    intro i hi
    fin_cases i <;> simp_all
  have hcol : ∀ i : Fin 3, i ≠ 0 → M i 0 = 0 := by
    intro i hi
    have h1 := congrFun (congrFun hMD i) 0
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
    rw [hdi i hi, one_mul, Matrix.cons_val_zero] at h1
    have : M i 0 * ((e : K) - 1) = 0 := by linear_combination h1
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hτ1)
  have hMe : M *ᵥ (Pi.single 0 1 : Fin 3 → K) = M 0 0 • (Pi.single 0 1 : Fin 3 → K) := by
    ext i
    rw [Matrix.mulVec_single_one, Pi.smul_apply, smul_eq_mul]
    fin_cases i
    · simp
    · simp [hcol 1 (by decide)]
    · simp [hcol 2 (by decide)]
  set v : Fin 3 → K := (g : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 0 1 with hv
  have hv0 : v ≠ 0 := by
    intro h0
    have := congrArg (fun w => ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w) h0
    simp only [hv, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec, Matrix.mulVec_zero] at this
    have := congrFun this 0
    simp at this
  have hyv : (y : Matrix (Fin 3) (Fin 3) K) *ᵥ v = M 0 0 • v := by
    have h1 : (y : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K) =
        (g : Matrix (Fin 3) (Fin 3) K) * M := by
      rw [hM, ← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    rw [hv, Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec, hMe, Matrix.mulVec_smul]
  rcases hirr (K ∙ v) (fun w hw => by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [Matrix.mulVec_smul, hyv, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)) with h | h
  · exact hv0 ((Submodule.span_singleton_eq_bot).mp h)
  · have := finrank_span_singleton (K := K) hv0
    rw [h, finrank_top, Module.finrank_fin_fun] at this
    omega

theorem eq_one_of_conj_eq_self (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    {u : ProjGenLinGroup (Fin 3) K}
    (h : ∀ s ∈ projImage (slPi π 3 (p ^ f) K), u * s * u⁻¹ = s) : u = 1 := by
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective u
  have hg := mem_statedScalars_of_commute_mk hK hq hq2 (g := g) fun s hs => by
    have := h _ ⟨s, hs, rfl⟩
    calc ProjGenLinGroup.mk g * ProjGenLinGroup.mk s =
        ProjGenLinGroup.mk g * ProjGenLinGroup.mk s * (ProjGenLinGroup.mk g)⁻¹ *
          ProjGenLinGroup.mk g := by group
      _ = ProjGenLinGroup.mk s * ProjGenLinGroup.mk g := by rw [this]
  exact ProjGenLinGroup.mk_eq_one.mpr (by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact hg)

theorem mem_centMod_of_mk_commute {y g : GL (Fin 3) K} (hg : g ∈ slPi π 3 (p ^ f) K)
    (h : ProjGenLinGroup.mk y * ProjGenLinGroup.mk g =
      ProjGenLinGroup.mk g * ProjGenLinGroup.mk y) :
    g ∈ centMod (slPi π 3 (p ^ f) K) y := by
  refine mem_centMod_iff_scalar.mpr ⟨hg, g * y * g⁻¹ * y⁻¹, ?_, by group⟩
  have h2 : ProjGenLinGroup.mk (g * y * g⁻¹ * y⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h]
    group
  have h3 := ProjGenLinGroup.mk_eq_one.mp h2
  rwa [Matrix.GeneralLinearGroup.center_eq_range_scalar] at h3

theorem exists_irreducible_structure (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {a y : GL (Fin 3) K} (haH : a ∈ glPi π 3 (p ^ f) K) (haZ : a ∉ zPi π 3 (p ^ f) K)
    (ha3 : a ^ 3 ∈ zPi π 3 (p ^ f) K)
    (hinner : ¬ ∃ l ∈ slPi π 3 (p ^ f) K, ∀ m ∈ slPi π 3 (p ^ f) K, a * m * a⁻¹ = l * m * l⁻¹)
    (hy3 : Type123 π (p ^ f) K y 3) (hya : y * a * y⁻¹ * a⁻¹ ∈ StatedScalars (Fin 3) K) :
    ∃ y' : GL (Fin 3) K, (∃ z ∈ zPi π 3 (p ^ f) K, y' = a * z) ∧
      IsCyclic ↥(slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y'}) ∧
      Nat.card ↥(slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y'}) =
        qSubPi π ((p ^ f) ^ 3) / qSubPi π (p ^ f) ∧
      ∃ w ∈ slPi π 3 (p ^ f) K, orderOf w = 3 ∧
        centMod (slPi π 3 (p ^ f) K) y' =
          (slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y'}) ⊔ Subgroup.zpowers w ∧
        Nat.card ↥(slPi π 3 (p ^ f) K ⊓
          Subgroup.centralizer ({y', w} : Set (GL (Fin 3) K))) = 3 := by
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have ha : Type123 π (p ^ f) K a 3 := by
    rcases type123_exhaust hK hq haH haZ ha3 with h1 | h2 | h3
    · exact absurd (exists_inner_of_type1 hK hq haH h1) hinner
    · exact absurd hy3.2.2 (not_irreducible_of_commute_type2 hK hq h2 hya)
    · exact h3
  obtain ⟨y', ⟨z, hz, rfl⟩, h⟩ := rank3II_4_10_one hK hq hτ hτ1 haH haZ ha3
  rcases h with ⟨⟨g, hg, hD⟩, -, -⟩ | ⟨⟨g, hg, e, he, hD⟩, -, -⟩ |
      ⟨-, -, -, hcyc, hcard, w, hw, hw3, -, hcent, hcard3⟩
  · exact absurd ha (not_type123_three_of_one hK hq ⟨τ, hτ, hτ1, z, hz, g, hg, hD⟩)
  · have he3 : (e : K) ^ 3 = 1 := by
      rcases he with he | he <;> rw [he]
      · exact hτ
      · rw [← pow_mul, pow_mul', hτ, one_pow]
    have he1 : e ≠ 1 := by
      rintro rfl
      rw [Units.val_one] at he
      rcases he with he | he
      · exact hτ1 he.symm
      · apply hτ1
        calc τ = τ ^ 3 / τ ^ 2 := by
              have : τ ≠ 0 := by rintro rfl; simp at hτ
              field_simp
          _ = 1 := by rw [hτ, ← he, div_one]
    exact absurd ha (not_type123_three_of_two hK hq ⟨e, he3, he1, z, hz, g, hg, hD⟩)
  · exact ⟨a * z, ⟨z, hz, rfl⟩, hcyc, hcard, w, hw, hw3, hcent, hcard3⟩

end Torus

section Elem

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem card_zpowers_sup_zpowers_eq_nine (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (h27 : Nat.card A = 27) {c d : G} (hc : c ∈ A) (hd : d ∈ A) (hd1 : d ≠ 1)
    (hcd : c ∉ Subgroup.zpowers d) :
    Nat.card (Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup G) = 9 := by
  have hcomm : c * d = d * c := congrArg Subtype.val (hA.1.is_comm.comm ⟨c, hc⟩ ⟨d, hd⟩)
  have hle : Nat.card (Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup G) ≤ 9 := by
    rw [← Sec4.closure_pair_eq]
    exact Sec10.card_closure_pair_le hcomm (hA.2 c hc) (hA.2 d hd)
  have hd3 : Nat.card (Subgroup.zpowers d) = 3 := by
    rw [Nat.card_zpowers]
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one (hA.2 d hd)) with
      h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hd1
    · exact h
  have hlt : Subgroup.zpowers d < Subgroup.zpowers c ⊔ Subgroup.zpowers d :=
    lt_of_le_of_ne le_sup_right fun h => hcd (h ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
  have hgt := Subgroup.card_lt_of_lt hlt
  have hdvd : Nat.card (Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup G) ∣ 3 ^ 3 := by
    rw [show 3 ^ 3 = 27 by norm_num, ← h27]
    exact Subgroup.card_dvd_of_le (sup_le (Subgroup.zpowers_le.mpr hc) (Subgroup.zpowers_le.mpr hd))
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  rw [hk'] at hle hgt ⊢
  rw [hd3] at hgt
  interval_cases k <;> simp_all

theorem sup_zpowers_eq_of_card (h27 : Nat.card A = 27) {U : Subgroup G} (hUA : U ≤ A)
    (hU9 : Nat.card U = 9) {x : G} (hxA : x ∈ A) (hxU : x ∉ U) :
    U ⊔ Subgroup.zpowers x = A := by
  have hle : U ⊔ Subgroup.zpowers x ≤ A := sup_le hUA (Subgroup.zpowers_le.mpr hxA)
  have hlt : U < U ⊔ Subgroup.zpowers x :=
    lt_of_le_of_ne le_sup_left fun h => hxU (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  have hgt := Subgroup.card_lt_of_lt hlt
  have hdvd : Nat.card (U ⊔ Subgroup.zpowers x : Subgroup G) ∣ 3 ^ 3 := by
    rw [show 3 ^ 3 = 27 by norm_num, ← h27]
    exact Subgroup.card_dvd_of_le hle
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  rw [hU9, hk'] at hgt
  have hk3 : k = 3 := by interval_cases k <;> simp_all
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [h27, hk', hk3]; norm_num)

end Elem

section Main

variable {G : Type} [Group G] [Finite G]

theorem false_of_inverts {A L : Subgroup G} {c : G} (hL : L ∈ thetaComponentsAt 3 c)
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) (h27 : Nat.card A = 27) (hcA : c ∈ A) (hc1 : c ≠ 1)
    (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (hsc : Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers c : Set G))
    {x : G} (hxA : x ∈ A) (hx : Sec4.InducesTypeOn L x 3) {d a t : G}
    (hAL : A ⊓ L = Subgroup.zpowers d) (hd1 : d ≠ 1) (haA : a ∈ A)
    (hanot : a ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d)
    (htN : t ∈ Subgroup.normalizer (L : Set G)) (hta : t * a * t⁻¹ = a)
    (htd : t * d * t⁻¹ = d⁻¹) : False := by
  obtain ⟨hxN, π, p, f, K, _, hK, hq, e, y, hyH, hy3, hact⟩ := hx
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hqs := Sec6.isQuasisimple_of_mem_thetaComponentsAt hL
  have hLq : Group.IsPerfect (L ⧸ aschbacherSolvableCore 3 L) := hqs.1
  have : IsSimpleGroup ((L ⧸ aschbacherSolvableCore 3 L) ⧸
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) := hqs.2.1
  have hLnt : Nontrivial (L ⧸ aschbacherSolvableCore 3 L) :=
    (QuotientGroup.mk_surjective (s := Subgroup.center (L ⧸ aschbacherSolvableCore 3 L))).nontrivial
  have hq2 : 2 < p ^ f := by
    by_contra h2
    have hp := hK.prime
    have hf := hK.one_le
    have h2' : p ^ f = 2 := by
      have : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) _)
      omega
    cases π
    · have := isSolvable_projImage_slPi_two hK h2'
      have : Group.IsSolvable (L ⧸ aschbacherSolvableCore 3 L) :=
        Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
      exact Group.IsPerfect.not_isSolvable _ this
    · change p ^ f % 3 = 1 at hq
      omega
  have hfaith : ∀ u : ProjGenLinGroup (Fin 3) K,
      (∀ s ∈ projImage (slPi π 3 (p ^ f) K), u * s * u⁻¹ = s) → u = 1 :=
    fun u h => eq_one_of_conj_eq_self hK hq hq2 h
  let B : Subgroup.normalizer (L : Set G) →* MulAut (projImage (slPi π 3 (p ^ f) K)) :=
    (MulAut.congr e).toMonoidHom.comp ((Sec4.thetaQuotMulAut L).comp L.normalizerMonoidHom)
  have hBapply : ∀ (g : Subgroup.normalizer (L : Set G)) (s : projImage (slPi π 3 (p ^ f) K)),
      B g s = e (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom g) (e.symm s)) := fun g s => rfl
  have hBx : ∀ s : projImage (slPi π 3 (p ^ f) K),
      ((B ⟨x, hxN⟩ s : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk y * s * (ProjGenLinGroup.mk y)⁻¹ := fun s => by
    rw [hBapply, hact, MulEquiv.apply_symm_apply]
  have hBl : ∀ (l : G) (hl : l ∈ L) (s : projImage (slPi π 3 (p ^ f) K)),
      B ⟨l, Subgroup.le_normalizer hl⟩ s =
        e ((⟨l, hl⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) * s *
          (e ((⟨l, hl⟩ : L) : L ⧸ aschbacherSolvableCore 3 L))⁻¹ := by
    intro l hl s
    rw [hBapply]
    obtain ⟨z, rfl⟩ := e.surjective s
    rw [MulEquiv.symm_apply_apply]
    induction z using QuotientGroup.induction_on with
    | H m =>
      rw [Sec4.thetaQuotMulAut_mk, ← map_inv, ← map_mul, ← map_mul]
      congr 1
  have hγ : ∀ (b : G) (hb : b ∈ Subgroup.normalizer (L : Set G)),
      b ∈ Sec4.thetaQuotCentralizer L ↔
        Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨b, hb⟩) = 1 := by
    intro b hb
    constructor
    · rintro ⟨y', hy', rfl⟩
      exact hy'
    · intro h
      exact ⟨⟨b, hb⟩, h, rfl⟩
  have hsc' := sectionCentralizer_eq_inf hAN
  rw [hsc] at hsc'
  have hBker : ∀ b (hb : b ∈ A), B ⟨b, hAN hb⟩ = 1 → b ∈ Subgroup.zpowers c := by
    intro b hb h
    have h1 : Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨b, hAN hb⟩) = 1 :=
      (MulAut.congr e).injective (by rw [map_one]; exact h)
    have h2 : b ∈ ((A ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) : Set G) :=
      ⟨hb, (hγ b (hAN hb)).mpr h1⟩
    rw [← hsc'] at h2
    exact h2
  have hBc : B ⟨c, hAN hcA⟩ = 1 := by
    have h1 : c ∈ ((A ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) : Set G) := by
      rw [← hsc']
      exact Subgroup.mem_zpowers c
    change (MulAut.congr e) (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨c, hAN hcA⟩)) = 1
    rw [(hγ c (hAN hcA)).mp h1.2, map_one]
  have hθ3 : ∀ (l : G) (hl : l ∈ L), l ^ 3 = 1 →
      ((⟨l, hl⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) = 1 → l = 1 := by
    intro l hl hl3 h
    rw [QuotientGroup.eq_one_iff] at h
    have h3 := (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).2.2.1
    have hord : orderOf (⟨⟨l, hl⟩, h⟩ : aschbacherSolvableCore 3 L) ∣ 1 := by
      rw [← (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3]
      refine Nat.dvd_gcd ?_ (orderOf_dvd_natCard _)
      exact orderOf_dvd_of_pow_eq_one (Subtype.ext (Subtype.ext (by simpa using hl3)))
    have := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hord)
    exact congrArg (fun z : aschbacherSolvableCore 3 L => ((z : L) : G)) this
  have hcL : c ∉ L := by
    intro hcL
    apply hc1
    refine hθ3 c hcL (hAe.2 c hcA) ?_
    have hcen : ((⟨c, hcL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) ∈
        Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
      rw [Subgroup.mem_center_iff]
      intro z
      induction z using QuotientGroup.induction_on with
      | H m =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp
          (Sec6.le_centralizer_of_mem_thetaComponentsAt hL m.2))
    have h1 : e ((⟨c, hcL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) ∈
        Subgroup.center (projImage (slPi π 3 (p ^ f) K)) := by
      rw [Subgroup.mem_center_iff]
      intro s
      obtain ⟨z, rfl⟩ := e.surjective s
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hcen z]
    rw [center_projImage_slPi hK hq hq2, Subgroup.mem_bot] at h1
    exact (map_eq_one_iff _ e.injective).mp h1
  have hdAL : d ∈ A ⊓ L := hAL ▸ Subgroup.mem_zpowers d
  have hdA : d ∈ A := hdAL.1
  have hdL : d ∈ L := hdAL.2
  set dq : L ⧸ aschbacherSolvableCore 3 L := ((⟨d, hdL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L)
    with hdq
  set dbar : projImage (slPi π 3 (p ^ f) K) := e dq with hdbar
  have hdbar1 : dbar ≠ 1 := fun h =>
    hd1 (hθ3 d hdL (hAe.2 d hdA) ((map_eq_one_iff _ e.injective).mp h))
  have hdbar3 : dbar ^ 3 = 1 := by
    rw [hdbar, ← map_pow, hdq, ← QuotientGroup.mk_pow]
    have : (⟨d, hdL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hAe.2 d hdA)
    rw [this, QuotientGroup.mk_one, map_one]
  let Sin : Subgroup G :=
    { carrier := {b | ∃ hb : b ∈ Subgroup.normalizer (L : Set G),
        ∃ s₀ : projImage (slPi π 3 (p ^ f) K), ∀ s, B ⟨b, hb⟩ s = s₀ * s * s₀⁻¹}
      mul_mem' := by
        rintro b b' ⟨hb, s₀, hs₀⟩ ⟨hb', s₀', hs₀'⟩
        refine ⟨Subgroup.mul_mem _ hb hb', s₀ * s₀', fun s => ?_⟩
        have : (⟨b * b', Subgroup.mul_mem _ hb hb'⟩ : Subgroup.normalizer (L : Set G)) =
            ⟨b, hb⟩ * ⟨b', hb'⟩ := rfl
        rw [this, map_mul, MulAut.mul_apply, hs₀', hs₀]
        group
      one_mem' := ⟨Subgroup.one_mem _, 1, fun s => by
        have : (⟨1, Subgroup.one_mem _⟩ : Subgroup.normalizer (L : Set G)) = 1 := rfl
        rw [this, map_one]
        simp⟩
      inv_mem' := by
        rintro b ⟨hb, s₀, hs₀⟩
        refine ⟨Subgroup.inv_mem _ hb, s₀⁻¹, fun s => ?_⟩
        have : (⟨b⁻¹, Subgroup.inv_mem _ hb⟩ : Subgroup.normalizer (L : Set G)) =
            (⟨b, hb⟩ : Subgroup.normalizer (L : Set G))⁻¹ := rfl
        rw [this, map_inv]
        apply (B ⟨b, hb⟩).injective
        rw [MulAut.apply_inv_self, hs₀]
        group }
  have hcSin : c ∈ Sin := ⟨hAN hcA, 1, fun s => by rw [hBc]; simp⟩
  have hdSin : d ∈ Sin := ⟨hAN hdA, dbar, fun s => hBl d hdL s⟩
  have hxSin : x ∉ Sin := by
    rintro ⟨hb, s₀, hs₀⟩
    have hu : (s₀ : ProjGenLinGroup (Fin 3) K)⁻¹ * ProjGenLinGroup.mk y = 1 := by
      refine hfaith _ fun s hs => ?_
      have h1 := hBx ⟨s, hs⟩
      have h2 := congrArg Subtype.val (hs₀ ⟨s, hs⟩)
      rw [show (⟨x, hb⟩ : Subgroup.normalizer (L : Set G)) = ⟨x, hxN⟩ from rfl] at h2
      rw [h1] at h2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
      calc (s₀ : ProjGenLinGroup (Fin 3) K)⁻¹ * ProjGenLinGroup.mk y * s *
          ((s₀ : ProjGenLinGroup (Fin 3) K)⁻¹ * ProjGenLinGroup.mk y)⁻¹ =
          (s₀ : ProjGenLinGroup (Fin 3) K)⁻¹ * (ProjGenLinGroup.mk y * s *
            (ProjGenLinGroup.mk y)⁻¹) * s₀ := by group
        _ = s := by rw [h2]; group
    have hys : ProjGenLinGroup.mk y = s₀ := by
      rw [← mul_inv_cancel_left (s₀ : ProjGenLinGroup (Fin 3) K) (ProjGenLinGroup.mk y), hu,
        mul_one]
    obtain ⟨l₀, hl₀, hl₀s⟩ := s₀.2
    apply not_inner_of_type3 hK hq hyH hy3
    refine ⟨l₀, hl₀, fun m hm => ?_⟩
    obtain ⟨u, hu'⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp (hl₀s.trans hys.symm)
    rw [← hu']
    have := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u m).eq
    calc l₀ * GeneralLinearGroup.scalar (Fin 3) u * m *
          (l₀ * GeneralLinearGroup.scalar (Fin 3) u)⁻¹ =
        l₀ * (GeneralLinearGroup.scalar (Fin 3) u * m) *
          (GeneralLinearGroup.scalar (Fin 3) u)⁻¹ * l₀⁻¹ := by group
      _ = l₀ * (m * GeneralLinearGroup.scalar (Fin 3) u) *
          (GeneralLinearGroup.scalar (Fin 3) u)⁻¹ * l₀⁻¹ := by rw [this]
      _ = l₀ * m * l₀⁻¹ := by group
  have hcd : c ∉ Subgroup.zpowers d := fun h =>
    hcL (Subgroup.zpowers_le.mpr hdL h)
  have h9 := card_zpowers_sup_zpowers_eq_nine hAe h27 hcA hdA hd1 hcd
  have hcdA : Subgroup.zpowers c ⊔ Subgroup.zpowers d ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr hcA) (Subgroup.zpowers_le.mpr hdA)
  have hcdSin : Subgroup.zpowers c ⊔ Subgroup.zpowers d ≤ Sin :=
    sup_le (Subgroup.zpowers_le.mpr hcSin) (Subgroup.zpowers_le.mpr hdSin)
  have hxcd : x ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d := fun h => hxSin (hcdSin h)
  have hAx := sup_zpowers_eq_of_card h27 hcdA h9 hxA hxcd
  have hAa := sup_zpowers_eq_of_card h27 hcdA h9 haA hanot
  have hPglPi : projImage (slPi π 3 (p ^ f) K) ≤ projImage (glPi π 3 (p ^ f) K) :=
    Subgroup.map_mono (slPi_le_glPi hπ)
  let Spgl : Subgroup G :=
    { carrier := {b | ∃ hb : b ∈ Subgroup.normalizer (L : Set G),
        ∃ u ∈ projImage (glPi π 3 (p ^ f) K), ∀ s : projImage (slPi π 3 (p ^ f) K),
          ((B ⟨b, hb⟩ s : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
            u * s * u⁻¹}
      mul_mem' := by
        rintro b b' ⟨hb, u, hu, hs⟩ ⟨hb', u', hu', hs'⟩
        refine ⟨Subgroup.mul_mem _ hb hb', u * u', Subgroup.mul_mem _ hu hu', fun s => ?_⟩
        have : (⟨b * b', Subgroup.mul_mem _ hb hb'⟩ : Subgroup.normalizer (L : Set G)) =
            ⟨b, hb⟩ * ⟨b', hb'⟩ := rfl
        rw [this, map_mul, MulAut.mul_apply, hs, hs']
        group
      one_mem' := ⟨Subgroup.one_mem _, 1, Subgroup.one_mem _, fun s => by
        have : (⟨1, Subgroup.one_mem _⟩ : Subgroup.normalizer (L : Set G)) = 1 := rfl
        rw [this, map_one]
        simp⟩
      inv_mem' := by
        rintro b ⟨hb, u, hu, hs⟩
        refine ⟨Subgroup.inv_mem _ hb, u⁻¹, Subgroup.inv_mem _ hu, fun s => ?_⟩
        have : (⟨b⁻¹, Subgroup.inv_mem _ hb⟩ : Subgroup.normalizer (L : Set G)) =
            (⟨b, hb⟩ : Subgroup.normalizer (L : Set G))⁻¹ := rfl
        rw [this, map_inv]
        have h1 := hs ((B ⟨b, hb⟩)⁻¹ s)
        rw [MulAut.apply_inv_self] at h1
        rw [h1]
        group }
  have hcS : c ∈ Spgl := ⟨hAN hcA, 1, Subgroup.one_mem _, fun s => by rw [hBc]; simp⟩
  have hdS : d ∈ Spgl := ⟨hAN hdA, dbar, hPglPi dbar.2, fun s => by
    rw [hBl d hdL s]
    rfl⟩
  have hxS : x ∈ Spgl := ⟨hxN, ProjGenLinGroup.mk y, ⟨y, hyH, rfl⟩, hBx⟩
  have hAS : A ≤ Spgl := by
    rw [← hAx]
    exact sup_le (sup_le (Subgroup.zpowers_le.mpr hcS) (Subgroup.zpowers_le.mpr hdS))
      (Subgroup.zpowers_le.mpr hxS)
  obtain ⟨haN, abar, ⟨a', ha'H, rfl⟩, hBa⟩ := hAS haA
  have hdet : ∀ u u' : ProjGenLinGroup (Fin 3) K,
      (∀ s ∈ projImage (slPi π 3 (p ^ f) K), u * s * u⁻¹ = u' * s * u'⁻¹) → u = u' := by
    intro u u' h
    have := hfaith (u'⁻¹ * u) fun s hs => by
      calc u'⁻¹ * u * s * (u'⁻¹ * u)⁻¹ = u'⁻¹ * (u * s * u⁻¹) * u' := by group
        _ = s := by rw [h s hs]; group
    rw [← mul_inv_cancel_left u' u, this, mul_one]
  have hBcomm : ∀ (g g' : G) (hg : g ∈ Subgroup.normalizer (L : Set G))
      (hg' : g' ∈ Subgroup.normalizer (L : Set G)), g * g' = g' * g →
      B ⟨g, hg⟩ * B ⟨g', hg'⟩ = B ⟨g', hg'⟩ * B ⟨g, hg⟩ := by
    intro g g' hg hg' h
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext h
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hNa : (⟨a, haN⟩ : Subgroup.normalizer (L : Set G)) = ⟨a, hAN haA⟩ := rfl
  have ha'Z : a' ∉ zPi π 3 (p ^ f) K := by
    intro hz
    obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
    have hs := mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz
    have h1 : ProjGenLinGroup.mk a' = 1 := ProjGenLinGroup.mk_eq_one.mpr (by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact hs)
    apply hanot
    refine Subgroup.mem_sup_left (hBker a haA ?_)
    ext s
    have := hBa s
    rw [h1] at this
    simp only [one_mul, inv_one, mul_one] at this
    exact this
  have ha'3 : a' ^ 3 ∈ zPi π 3 (p ^ f) K := by
    obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
    rw [zPi_eq hπ (fun h => by subst h; exact hq) hτ hτ1]
    refine ⟨Subgroup.pow_mem _ ha'H 3, ?_⟩
    have h1 : ProjGenLinGroup.mk a' ^ 3 = 1 := by
      refine hfaith _ fun s hs => ?_
      have h3 : (B ⟨a, haN⟩) ^ 3 = 1 := by
        rw [← map_pow]
        have : (⟨a, haN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
          Subtype.ext (by simpa using hAe.2 a haA)
        rw [this, map_one]
      have h4 := congrArg (fun σ : MulAut (projImage (slPi π 3 (p ^ f) K)) =>
        ((σ ⟨s, hs⟩ : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K)) h3
      simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] at h4
      rw [hBa, hBa, hBa] at h4
      generalize ProjGenLinGroup.mk a' = u at h4 ⊢
      calc u ^ 3 * s * (u ^ 3)⁻¹ = u * (u * (u * s * u⁻¹) * u⁻¹) * u⁻¹ := by
            rw [pow_three, _root_.mul_inv_rev, _root_.mul_inv_rev]
            simp only [mul_assoc]
        _ = s := h4
    have h2 := ProjGenLinGroup.mk_eq_one.mp (by rw [map_pow]; exact h1)
    rwa [Matrix.GeneralLinearGroup.center_eq_range_scalar] at h2
  have hinner : ¬ ∃ l ∈ slPi π 3 (p ^ f) K, ∀ m ∈ slPi π 3 (p ^ f) K,
      a' * m * a'⁻¹ = l * m * l⁻¹ := by
    rintro ⟨l₀, hl₀, hl₀m⟩
    have haSin : a ∈ Sin := ⟨haN, ⟨ProjGenLinGroup.mk l₀, ⟨l₀, hl₀, rfl⟩⟩, fun s => by
      apply Subtype.ext
      rw [hBa]
      obtain ⟨m, hm, hms⟩ := s.2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hms, ← map_inv, ← map_mul, ← map_mul, hl₀m m hm, map_mul, map_mul, map_inv]⟩
    have hASin : A ≤ Sin := by
      rw [← hAa]
      exact sup_le hcdSin (Subgroup.zpowers_le.mpr haSin)
    exact hxSin (hASin hxA)
  have hya : y * a' * y⁻¹ * a'⁻¹ ∈ StatedScalars (Fin 3) K := by
    have hxa := hBcomm x a hxN haN (hcomm x hxA a haA)
    have h1 : ProjGenLinGroup.mk y * ProjGenLinGroup.mk a' =
        ProjGenLinGroup.mk a' * ProjGenLinGroup.mk y := by
      refine hdet _ _ fun s hs => ?_
      have h2 := congrArg (fun σ : MulAut (projImage (slPi π 3 (p ^ f) K)) =>
        ((σ ⟨s, hs⟩ : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K)) hxa
      simp only [MulAut.mul_apply] at h2
      rw [hBx, hBa, hBa, hBx] at h2
      calc ProjGenLinGroup.mk y * ProjGenLinGroup.mk a' * s *
          (ProjGenLinGroup.mk y * ProjGenLinGroup.mk a')⁻¹ =
          ProjGenLinGroup.mk y * (ProjGenLinGroup.mk a' * s * (ProjGenLinGroup.mk a')⁻¹) *
            (ProjGenLinGroup.mk y)⁻¹ := by group
        _ = ProjGenLinGroup.mk a' * (ProjGenLinGroup.mk y * s * (ProjGenLinGroup.mk y)⁻¹) *
            (ProjGenLinGroup.mk a')⁻¹ := h2
        _ = _ := by group
    have h2 : ProjGenLinGroup.mk (y * a' * y⁻¹ * a'⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
      group
    have h3 := ProjGenLinGroup.mk_eq_one.mp h2
    rwa [Matrix.GeneralLinearGroup.center_eq_range_scalar] at h3
  obtain ⟨y', ⟨z, hz, rfl⟩, hcyc, hcard, w, hw, hw3, hcent, hcard3⟩ :=
    exists_irreducible_structure hK hq ha'H ha'Z ha'3 hinner hy3 hya
  have hmkz : ProjGenLinGroup.mk z = 1 := by
    obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
    refine ProjGenLinGroup.mk_eq_one.mpr ?_
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz
  have hmky : ProjGenLinGroup.mk (a' * z) = ProjGenLinGroup.mk a' := by
    rw [map_mul, hmkz, mul_one]
  obtain ⟨l, hlL, hld⟩ := dbar.2
  have hBd' : ∀ s : projImage (slPi π 3 (p ^ f) K),
      ((B ⟨d, hAN hdA⟩ s : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        dbar * s * (dbar : ProjGenLinGroup (Fin 3) K)⁻¹ := fun s => by
    rw [show (⟨d, hAN hdA⟩ : Subgroup.normalizer (L : Set G)) =
      ⟨d, Subgroup.le_normalizer hdL⟩ from rfl, hBl d hdL s]
    rfl
  have hlc : l ∈ centMod (slPi π 3 (p ^ f) K) (a' * z) := by
    refine mem_centMod_of_mk_commute hlL ?_
    rw [hmky, hld]
    have hda := hBcomm d a (hAN hdA) haN (hcomm d hdA a haA)
    refine (hdet _ _ fun s hs => ?_).symm
    have h2 := congrArg (fun σ : MulAut (projImage (slPi π 3 (p ^ f) K)) =>
      ((σ ⟨s, hs⟩ : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K)) hda
    simp only [MulAut.mul_apply] at h2
    rw [hBd', hBa, hBa, hBd'] at h2
    calc (dbar : ProjGenLinGroup (Fin 3) K) * ProjGenLinGroup.mk a' * s *
        ((dbar : ProjGenLinGroup (Fin 3) K) * ProjGenLinGroup.mk a')⁻¹ =
        (dbar : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk a' * s *
          (ProjGenLinGroup.mk a')⁻¹) * (dbar : ProjGenLinGroup (Fin 3) K)⁻¹ := by group
      _ = ProjGenLinGroup.mk a' * ((dbar : ProjGenLinGroup (Fin 3) K) * s *
          (dbar : ProjGenLinGroup (Fin 3) K)⁻¹) * (ProjGenLinGroup.mk a')⁻¹ := h2
      _ = _ := by group
  have hl1 : ProjGenLinGroup.mk l ≠ 1 := by
    rw [hld]
    exact fun h => hdbar1 (Subtype.ext h)
  have hl3 : ProjGenLinGroup.mk l ^ 3 = 1 := by
    rw [hld]
    exact congrArg Subtype.val hdbar3
  have hβC : ∀ s : projImage (slPi π 3 (p ^ f) K),
      ProjGenLinGroup.mk (a' * z) * (s : ProjGenLinGroup (Fin 3) K) =
        s * ProjGenLinGroup.mk (a' * z) →
      ProjGenLinGroup.mk (a' * z) * (B ⟨t, htN⟩ s : ProjGenLinGroup (Fin 3) K) =
        B ⟨t, htN⟩ s * ProjGenLinGroup.mk (a' * z) := by
    intro s hs
    rw [hmky] at hs ⊢
    have hta' := hBcomm t a htN haN (by
      calc t * a = t * a * t⁻¹ * t := by group
        _ = a * t := by rw [hta])
    have hsa : B ⟨a, haN⟩ s = s := by
      apply Subtype.ext
      rw [hBa, hs, mul_inv_cancel_right]
    have h1 : B ⟨t, htN⟩ s = B ⟨a, haN⟩ (B ⟨t, htN⟩ s) := by
      conv_lhs => rw [← hsa]
      rw [← MulAut.mul_apply, hta', MulAut.mul_apply]
    have h2 := congrArg Subtype.val h1
    rw [hBa] at h2
    calc ProjGenLinGroup.mk a' * ((B ⟨t, htN⟩ s : projImage (slPi π 3 (p ^ f) K)) :
        ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk a' * (B ⟨t, htN⟩ s : ProjGenLinGroup (Fin 3) K) *
          (ProjGenLinGroup.mk a')⁻¹ * ProjGenLinGroup.mk a' := by group
      _ = _ := by rw [← h2]
  have hβl : B ⟨t, htN⟩ ⟨ProjGenLinGroup.mk l, ⟨l, hlc.1, rfl⟩⟩ =
      (⟨ProjGenLinGroup.mk l, ⟨l, hlc.1, rfl⟩⟩ : projImage (slPi π 3 (p ^ f) K))⁻¹ := by
    have hl' : (⟨ProjGenLinGroup.mk l, ⟨l, hlc.1, rfl⟩⟩ : projImage (slPi π 3 (p ^ f) K)) =
        dbar := Subtype.ext hld
    rw [hl', hBapply, hdbar, MulEquiv.symm_apply_apply, hdq, Sec4.thetaQuotMulAut_mk, ← map_inv,
      ← QuotientGroup.mk_inv]
    congr 2
    exact Subtype.ext htd
  exact false_of_inverts_torus hK hq hq2 hcyc hcard hw3 hcent hcard3 hlc hl1 hl3
    (B ⟨t, htN⟩).toMonoidHom (B ⟨t, htN⟩).injective hβC hβl

theorem k410NotInverted : K410NotInverted := by
  intro G _ _ A c L hL hAe h27 hcA hc1 hAN hsc _ hx d a t hAL hd1 haA hanot htN _ hta htd
  obtain ⟨x, hxA, hx⟩ := hx
  exact false_of_inverts hL hAe h27 hcA hc1 hAN hsc hxA hx hAL hd1 haA hanot htN hta htd

end Main

end CFSG.RankThree.PartTwo.Sec13
