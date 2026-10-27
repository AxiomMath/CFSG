module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGOneFiveRank

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

section Transvection

theorem mem_centralizer_or_ggIsTransvection {p : ℕ} (hp : p.Prime) {B Bs : Subgroup G}
    (hBBs : B ≤ Bs) (hBs : IsElemAbelian p Bs) (hcard : Nat.card Bs ≤ p * Nat.card B) {u : G}
    (hu : u ∈ Subgroup.normalizer (Bs : Set G)) (huB : u ∈ Subgroup.centralizer (B : Set G))
    {k : ℕ} (huk : u ^ p ^ k = 1) :
    u ∈ Subgroup.centralizer (Bs : Set G) ∨ GGIsTransvection p (ggConjAut Bs hu) := by
  have : Fact p.Prime := ⟨hp⟩
  have hcomm : ∀ a b : ↥Bs, a * b = b * a := fun a b => hBs.1.is_comm.comm a b
  let f : ↥Bs →* ↥Bs :=
    { toFun := fun b => b⁻¹ * ggConjAut Bs hu b
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul, mul_inv_rev]
        calc b⁻¹ * a⁻¹ * (ggConjAut Bs hu a * ggConjAut Bs hu b)
            = b⁻¹ * (a⁻¹ * ggConjAut Bs hu a) * ggConjAut Bs hu b := by group
          _ = (a⁻¹ * ggConjAut Bs hu a) * b⁻¹ * ggConjAut Bs hu b := by rw [hcomm b⁻¹]
          _ = a⁻¹ * ggConjAut Bs hu a * (b⁻¹ * ggConjAut Bs hu b) := by group }
  have hf : ∀ b, f b = b⁻¹ * ggConjAut Bs hu b := fun _ => rfl
  have hfix : ∀ b, f b = 1 ↔ ggConjAut Bs hu b = b := fun b => by
    rw [hf, inv_mul_eq_one, eq_comm]
  by_cases hK : f.ker = ⊤
  · left
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h1 : f ⟨b, hb⟩ = 1 := by
      rw [← MonoidHom.mem_ker, hK]
      exact Subgroup.mem_top _
    rw [hfix] at h1
    have h2 := congrArg Subtype.val h1
    rw [ggConjAut_apply] at h2
    calc b * u = u * b * u⁻¹ * u := by rw [h2]
      _ = u * b := by group
  right
  have hfixK : Nat.card {b : ↥Bs // ggConjAut Bs hu b = b} = Nat.card f.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight fun b => (hfix b).symm.trans MonoidHom.mem_ker.symm)
  have hpg : IsPGroup p ↥Bs := fun b => ⟨1, Subtype.ext (by simpa using hBs.2 b b.2)⟩
  obtain ⟨n, hn⟩ := hpg.exists_card_eq
  have hBK : B.subgroupOf Bs ≤ f.ker := by
    intro b hb
    rw [MonoidHom.mem_ker, hfix]
    apply Subtype.ext
    rw [ggConjAut_apply]
    have hc := Subgroup.mem_centralizer_iff.mp huB b (Subgroup.mem_subgroupOf.mp hb)
    rw [← hc]
    group
  have hBcard : Nat.card B ≤ Nat.card f.ker := by
    have h1 : Nat.card (B.subgroupOf Bs) = Nat.card B :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBBs).toEquiv
    rw [← h1]
    exact Subgroup.card_le_of_le hBK
  have hindex : f.ker.index = p := by
    have hidx : f.ker.index ∣ p ^ n := hn ▸ f.ker.index_dvd_card
    obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow hp).mp hidx
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hK (Subgroup.index_eq_one.mp (by simpa using ha))
    have hle : f.ker.index ≤ p := by
      have hm := f.ker.card_mul_index
      have hpos : 0 < Nat.card f.ker := Nat.card_pos
      by_contra hlt'
      have hlt := not_le.mp hlt'
      have h3 : Nat.card f.ker * p < Nat.card ↥Bs := hm ▸ Nat.mul_lt_mul_of_pos_left hlt hpos
      have h2 : p * Nat.card B ≤ Nat.card f.ker * p := by
        rw [mul_comm]
        exact Nat.mul_le_mul_right p hBcard
      exact absurd (hcard.trans h2) (not_le.mpr h3)
    have hge : p ≤ f.ker.index := by
      rw [ha]
      exact Nat.le_self_pow ha0 p
    omega
  have hKp : Nat.card f.ker * p = Nat.card ↥Bs := by
    rw [← hindex]
    exact f.ker.card_mul_index
  refine ⟨by rw [hfixK]; exact hKp, ?_⟩
  have hrange : Nat.card f.range = p := by
    have h1 := Subgroup.card_ker_mul_card_range f
    rw [← hKp] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  intro b
  rw [← hf, ← hfix]
  by_contra hne
  set r := f b with hr
  have hr1 : r ≠ 1 := by
    intro h1
    apply hne
    rw [h1, map_one]
  have hrp : r ^ p = 1 := Subtype.ext (by simpa using hBs.2 r r.2)
  have hor : orderOf r = p := orderOf_eq_prime hrp hr1
  have hzr : Subgroup.zpowers r = f.range := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact ⟨b, rfl⟩
    · rw [hrange, Nat.card_zpowers, hor]
  obtain ⟨i, hi⟩ : ∃ i : ℤ, r ^ i = f r := by
    rw [← Subgroup.mem_zpowers_iff, hzr]
    exact ⟨r, rfl⟩
  have hφr : ggConjAut Bs hu r = r ^ (1 + i) := by
    rw [zpow_add, zpow_one, hi, hf, mul_inv_cancel_left]
  have hpow : ∀ m : ℕ, (ggConjAut Bs hu ^ m) r = r ^ ((1 + i) ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ' (ggConjAut Bs hu) m, MulAut.mul_apply, ih, map_zpow, hφr, ← zpow_mul,
        pow_succ' (1 + i) m]
  have hid : (ggConjAut Bs hu ^ p ^ k) r = r := by
    apply Subtype.ext
    rw [ggConjAut_pow_apply, huk]
    simp
  rw [hpow] at hid
  have hdvd : (p : ℤ) ∣ (1 + i) ^ p ^ k - 1 := by
    have h1 := orderOf_dvd_iff_zpow_eq_one.mpr
      (show r ^ ((1 + i) ^ p ^ k - 1) = 1 by rw [zpow_sub_one, hid, mul_inv_cancel])
    rwa [hor] at h1
  have hz : ((1 + i : ℤ) : ZMod p) = 1 := by
    have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd
    push_cast at h1
    rw [ZMod.pow_card_pow] at h1
    push_cast
    exact sub_eq_zero.mp h1
  have hi0 : (p : ℤ) ∣ i := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hz
    simpa using hz
  have hri : r ^ i = 1 := by
    rw [← orderOf_dvd_iff_zpow_eq_one, hor]
    exact hi0
  apply hne
  rw [← hi, hri]

end Transvection

section OmegaOne

theorem mem_of_noTransvection {p : ℕ} (hp : p.Prime) {B Bs : Subgroup G} (hBs : GGBstar p B Bs)
    (hNT : GGNoTransvection p Bs) {P : Subgroup G} (hPC : P ≤ Subgroup.centralizer (B : Set G))
    (hPp : IsPGroup p P) (hBsP : Bs ≤ P) {g : G} (hgP : g ∈ P) (hg : g ^ p = 1) : g ∈ Bs := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hBBs, hel, hcard, hΩ⟩ := hBs
  have hN : ∀ u ∈ P, u ∈ Subgroup.normalizer (Bs : Set G) →
      u ∈ Subgroup.centralizer (Bs : Set G) := by
    intro u huP huN
    obtain ⟨k, hk⟩ := hPp ⟨u, huP⟩
    have huk : u ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    rcases mem_centralizer_or_ggIsTransvection hp hBBs hel hcard huN (hPC huP) huk with h | h
    · exact h
    · exact absurd h (hNT _ (ggConjAut_mem_ggInduced (Subgroup.mem_top u) huN))
  have hBsC : Bs ≤ P ⊓ Subgroup.centralizer (Bs : Set G) := by
    refine le_inf hBsP fun b hb => Subgroup.mem_centralizer_iff.mpr fun c hc => ?_
    exact congrArg Subtype.val (hel.1.is_comm.comm (⟨c, hc⟩ : ↥Bs) ⟨b, hb⟩)
  have hCP : P ⊓ Subgroup.centralizer (Bs : Set G) = P := by
    by_contra hne
    obtain ⟨v, hvP, hvN, hvC⟩ :=
      exists_mem_normalizer_not_mem hPp (lt_of_le_of_ne inf_le_left hne)
    apply hvC
    refine ⟨hvP, hN v hvP ?_⟩
    have hle : Bs.map (MulAut.conj v).toMonoidHom ≤ Bs := by
      rintro _ ⟨b, hb, rfl⟩
      have hbC : v * b * v⁻¹ ∈ P ⊓ Subgroup.centralizer (Bs : Set G) :=
        (Subgroup.mem_normalizer_iff.mp hvN b).mp (hBsC hb)
      show v * b * v⁻¹ ∈ Bs
      refine hΩ _ hbC.2 ?_
      rw [conj_pow, hel.2 b hb, mul_one, mul_inv_cancel]
    exact mem_normalizer_iff_map_conj.mpr (Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj v).injective).ge)
  have hgC : g ∈ P ⊓ Subgroup.centralizer (Bs : Set G) := by
    rw [hCP]
    exact hgP
  exact hΩ g hgC.2 hg

end OmegaOne

theorem ggOmegaOneInput_of_noTransvection (hc₃ : GGNoTransvectionInput) : GGOmegaOneInput := by
  intro G _ _ p B Bs x L D J hcfg hOp hInn P hPC hPp hBsP g hgP hg
  exact mem_of_noTransvection hcfg.1.2.2.2.2.2.1.1 hcfg.2.1
    (hc₃ G p B Bs x L D J hcfg hOp hInn) hPC hPp hBsP hgP hg

end CFSG.StandardType
