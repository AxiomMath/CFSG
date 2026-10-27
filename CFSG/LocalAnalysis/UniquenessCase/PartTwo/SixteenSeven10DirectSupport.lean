module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase4Ker
public import CFSG.Sporadic.Schreier.RuElemAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

open scoped Pointwise

section Family

variable {T : Type} [CommGroup T]

structure SymSumFamily (X : Subgroup (MulAut T)) {ι : Type} [Fintype ι] (Y : ι → Subgroup T)
    (r d : ℕ) : Prop where
  indep : iSupIndep Y
  inj : Function.Injective Y
  sup : ⨆ i, Y i = ⊤
  card : Fintype.card ι = r + 1
  rank : ∀ i, rk ↥(Y i) = d
  perm : ∀ g ∈ X, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j
  surj : ∀ π : Equiv.Perm ι, ∃ g ∈ X, ∀ i, (Y i).map g.toMonoidHom = Y (π i)

theorem s16c1610_symSumFamily_of_symSumOfConj [Finite T] {X : Subgroup (MulAut T)} {r d : ℕ}
    (hS : SymSumOfConj X (⊤ : Subgroup T) r d) :
    ∃ (ι : Type) (_ : Fintype ι) (Y : ι → Subgroup T), SymSumFamily X Y r d := by
  obtain ⟨ι, hι, Y, hind, hinj, hsup, hcard, hrk, hperm, hsurj⟩ := s16n9b_case4_data hS
  exact ⟨ι, hι, Y, ⟨hind, hinj, hsup, hcard, hrk, hperm, hsurj⟩⟩

end Family

section Generic

variable {T : Type} [CommGroup T] [Finite T]

private theorem finite_mulAut : Finite (MulAut T) := by
  classical
  exact Finite.of_injective (fun f : MulAut T => (f : T → T))
    (fun f g h => MulEquiv.ext (congrFun h))

theorem s16c1610_inf_centSub_eq_bot {B : Subgroup (MulAut T)} {Ut Y : Subgroup T}
    (hA3 : ∀ b ∈ B, b ≠ 1 → fixV (Subgroup.zpowers b) ≤ Ut) (hY : ¬ Y ≤ Ut) :
    B ⊓ centSub Y = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro b ⟨hbB, hbc⟩
  by_contra hb1
  refine hY (le_trans (fun y hy => ?_) (hA3 b hbB hb1))
  exact mem_fixV_zpowers_iff_apply.mpr (mem_centSub.mp hbc y hy)

theorem s16c1610_inf_ne_bot_of_rkIdx_lt (hT : ∀ t : T, t ^ 2 = 1) {Y Ut : Subgroup T}
    (h : rkIdx Ut < rk ↥Y) : Y ⊓ Ut ≠ ⊥ := by
  intro hbot
  have h1 : rk ↥(Y ⊔ Ut) + rk ↥(Y ⊓ Ut) = rk ↥Y + rk ↥Ut := rk_sup_add_rk_inf Y Ut
  have h2 : rk ↥(Y ⊔ Ut) ≤ rk ↥Ut + rkIdx Ut := by
    calc rk ↥(Y ⊔ Ut) ≤ rk (⊤ : Subgroup T) := rk_mono le_top
      _ = rk T := rk_top
      _ = rk ↥Ut + rkIdx Ut := (rk_add_rkIdx Ut).symm
  have h3 : rkIdx Ut < rk ↥Y := h
  rw [hbot, rk_bot] at h1
  omega

theorem s16c1610_ut_eq_top_of_card_le_two (hT : ∀ t : T, t ^ 2 = 1) {B : Subgroup (MulAut T)}
    {Ut : Subgroup T} (hB1 : B ≠ ⊥) (hB2 : IsElemAbelian2 B) (hcard : Nat.card B ≤ 2)
    (hA4 : ∀ b ∈ B, b ≠ 1 → ∀ w, w ∈ Ut ↔ w * (b w)⁻¹ ∈ fixV B) : Ut = ⊤ := by
  classical
  haveI : Finite (MulAut T) := finite_mulAut
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB1
  let b : MulAut T := (a : MulAut T)
  have hbB : b ∈ B := a.2
  have hb1 : b ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hb2 : b ^ 2 = 1 := hB2.2 b hbB
  have hbz : Subgroup.zpowers b = B := by
    have hzle : Subgroup.zpowers b ≤ B := Subgroup.zpowers_le.mpr hbB
    have hzcard : Nat.card ↥(Subgroup.zpowers b) = 2 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hb2 hb1]
    have hdvd : 2 ∣ Nat.card B := hzcard ▸ Subgroup.card_dvd_of_le hzle
    have hBcard : Nat.card B = 2 := by
      obtain ⟨k, hk⟩ := hdvd
      have hpos : 0 < Nat.card B := Nat.card_pos
      omega
    exact Subgroup.eq_of_le_of_card_ge hzle (by omega)
  have hclass : ∀ b' ∈ B, b' = 1 ∨ b' = b := by
    intro b' hb'B
    have hmem : b' ∈ Subgroup.zpowers b := by rw [hbz]; exact hb'B
    rw [mem_zpowers_iff_mem_range_orderOf, orderOf_eq_prime hb2 hb1] at hmem
    rw [Finset.mem_image] at hmem
    obtain ⟨n, hn, hnb⟩ := hmem
    subst hnb
    rw [Finset.mem_range] at hn
    interval_cases n <;> simp
  have hfixw : ∀ w : T, w * (b w)⁻¹ ∈ fixV B := by
    intro w
    rw [mem_fixV]
    intro b' hb'B
    rcases hclass b' hb'B with rfl | rfl
    · simp
    · have hbb : b (b w) = w := by
        have h1 : b * b = 1 := by simpa [pow_two] using hb2
        calc b (b w) = (b * b) w := (MulAut.mul_apply T b b w).symm
          _ = (1 : MulAut T) w := by rw [h1]
          _ = w := rfl
      have hbw : (b w)⁻¹ = b w := by
        have h1 : b w * b w = 1 := by simpa [pow_two] using hT (b w)
        exact (mul_eq_one_iff_eq_inv.mp h1).symm
      have hw : w⁻¹ = w := by
        have h1 : w * w = 1 := by simpa [pow_two] using hT w
        exact (mul_eq_one_iff_eq_inv.mp h1).symm
      calc b (w * (b w)⁻¹) = b w * b ((b w)⁻¹) := by rw [map_mul]
        _ = b w * (b (b w))⁻¹ := by rw [map_inv]
        _ = b w * w⁻¹ := by rw [hbb]
        _ = b w * w := by rw [hw]
        _ = w * b w := by rw [mul_comm]
        _ = w * (b w)⁻¹ := by rw [hbw]
  rw [eq_top_iff]
  intro w _
  exact (hA4 b hbB hb1 w).mpr (hfixw w)

theorem s16c1610_rk_fixV_le_of_invariant (hT : ∀ t : T, t ^ 2 = 1) {B : Subgroup (MulAut T)}
    {S S' : Subgroup T} (hd : Disjoint S S') (hsup : S ⊔ S' = ⊤)
    (hS : ∀ b ∈ B, ∀ s ∈ S, b s ∈ S) (hS' : ∀ b ∈ B, ∀ s ∈ S', b s ∈ S') :
    rk ↥(fixV B) ≤ rk ↥(S ⊓ fixV B) + rk ↥(S' ⊓ fixV B) := by
  have hle : fixV B ≤ (S ⊓ fixV B) ⊔ (S' ⊓ fixV B) := by
    intro w hw
    obtain ⟨s, hs, s', hs', hss'⟩ :=
      Subgroup.mem_sup.mp (by rw [hsup]; exact Subgroup.mem_top w)
    have hsfix : s ∈ fixV B := by
      rw [mem_fixV]
      intro b hb
      have heq : b s * b s' = s * s' := by rw [← map_mul, hss', hw b hb]
      have hmem : s⁻¹ * b s ∈ S ⊓ S' := by
        refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hs) (hS b hb s hs), ?_⟩
        have h1 : s⁻¹ * b s = s' * (b s')⁻¹ := by
          rw [mul_comm s' ((b s')⁻¹), inv_mul_eq_inv_mul_iff_mul_eq_mul, heq, mul_comm]
        rw [h1]
        exact Subgroup.mul_mem _ hs' (Subgroup.inv_mem _ (hS' b hb s' hs'))
      have hbot : s⁻¹ * b s = 1 := Subgroup.mem_bot.mp (hd.le_bot hmem)
      calc b s = s * (s⁻¹ * b s) := by group
        _ = s * 1 := by rw [hbot]
        _ = s := mul_one s
    have hs'fix : s' ∈ fixV B := by
      rw [mem_fixV]
      intro b hb
      have heq : b s * b s' = s * s' := by rw [← map_mul, hss', hw b hb]
      have hmem : s' * (b s')⁻¹ ∈ S ⊓ S' := by
        refine ⟨?_, Subgroup.mul_mem _ hs' (Subgroup.inv_mem _ (hS' b hb s' hs'))⟩
        have h1 : s⁻¹ * b s = s' * (b s')⁻¹ := by
          rw [mul_comm s' ((b s')⁻¹), inv_mul_eq_inv_mul_iff_mul_eq_mul, heq, mul_comm]
        rw [← h1]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hs) (hS b hb s hs)
      have hbot : s' * (b s')⁻¹ = 1 := Subgroup.mem_bot.mp (hd.le_bot hmem)
      calc b s' = (s' * (b s')⁻¹)⁻¹ * s' := by group
        _ = 1⁻¹ * s' := by rw [hbot]
        _ = s' := by simp
    exact Subgroup.mem_sup.mpr ⟨s, ⟨hs, hsfix⟩, s', ⟨hs', hs'fix⟩, hss'⟩
  have h2 : rk ↥((S ⊓ fixV B) ⊔ (S' ⊓ fixV B)) + rk ↥((S ⊓ fixV B) ⊓ (S' ⊓ fixV B))
      = rk ↥(S ⊓ fixV B) + rk ↥(S' ⊓ fixV B) := rk_sup_add_rk_inf _ _
  have h3 : rk ↥((S ⊓ fixV B) ⊔ (S' ⊓ fixV B)) ≤
      rk ↥(S ⊓ fixV B) + rk ↥(S' ⊓ fixV B) := by omega
  exact (rk_mono hle).trans h3

theorem s16c1610_card_le_two_of_rk_two (hT : ∀ t : T, t ^ 2 = 1) {B : Subgroup (MulAut T)}
    (hB2 : ∀ b ∈ B, b ^ 2 = 1) {Y : Subgroup T} (hY : rk ↥Y = 2) (hBY : B ≤ stabSub Y)
    (hker : B ⊓ centSub Y = ⊥) : Nat.card B ≤ 2 := by
  classical
  haveI : Finite (MulAut ↥Y) :=
    Finite.of_injective (fun f : MulAut ↥Y => (f : ↥Y → ↥Y))
      (fun f g h => MulEquiv.ext (congrFun h))
  have hMA : Nat.card (MulAut ↥Y) = 6 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [CFSG.Sporadic.RuSchreier.ru_card_mulAut_elementary
      (fun a b : ↥Y => Subtype.ext (mul_comm (a : T) (b : T)))
      (fun a : ↥Y => Subtype.ext (by simpa using hT (a : T))) (n := 2)
      (by rw [card_eq_two_pow hT Y, hY])]
    simp [Fin.prod_univ_succ]
  have hdvd : Nat.card ↥(autSub B Y) ∣ 6 := by
    simpa [hMA] using Subgroup.card_subgroup_dvd_card (autSub B Y)
  have hsq : ∀ φ : ↥(autSub B Y), φ ^ 2 = 1 := by
    intro φ
    obtain ⟨g, hgB, hgφ⟩ := mem_autSub.mp φ.2
    apply Subtype.ext
    change ((φ : MulAut ↥Y)) ^ 2 = 1
    rw [← hgφ, ← map_pow, show g ^ 2 = 1 from Subtype.ext (hB2 (g : MulAut T) hgB), map_one]
  have hisP : IsPGroup 2 ↥(autSub B Y) := isPGroup_two_of_sq_eq_one hsq
  have hpow : Nat.card ↥(autSub B Y) = 2 ^ rk ↥(autSub B Y) :=
    card_eq_two_pow_of_isPGroup hisP
  have hdvd_pow : 2 ^ rk ↥(autSub B Y) ∣ 6 := hpow ▸ hdvd
  have hrk_le : rk ↥(autSub B Y) ≤ 1 := by
    by_contra hcon
    have h2 : 2 ≤ rk ↥(autSub B Y) := by omega
    exact absurd ((pow_dvd_pow 2 h2).trans hdvd_pow) (by norm_num)
  have hle2 : Nat.card ↥(autSub B Y) ≤ 2 := by
    rw [hpow]
    calc 2 ^ rk ↥(autSub B Y) ≤ 2 ^ 1 := pow_le_pow_right' (by norm_num) hrk_le
      _ = 2 := by norm_num
  have hcent : Nat.card ↥(B ⊓ centSub Y) = 1 := by rw [hker, Subgroup.card_bot]
  have hcardB : Nat.card B = Nat.card ↥(autSub B Y) := by
    rw [← card_autSub_mul hBY, hcent, mul_one]
  rw [hcardB]
  exact hle2

theorem s16c1610_card_le_two_mul_stab {B : Subgroup (MulAut T)} {Y Y' : Subgroup T}
    (horb : ∀ b ∈ B, Y.map b.toMonoidHom = Y ∨ Y.map b.toMonoidHom = Y') :
    Nat.card B ≤ 2 * Nat.card ↥(B ⊓ stabSub Y) := by
  have hsmul : ∀ b : MulAut T, b • Y = Y.map b.toMonoidHom := by
    intro b
    rw [Subgroup.pointwise_smul_def]
    have h : MulDistribMulAction.toMonoidEnd (MulAut T) T b = b.toMonoidHom :=
      MonoidHom.ext (fun x => rfl)
    rw [h]
  have hstab : ∀ b : MulAut T, b ∈ stabSub Y ↔ b • Y = Y := by
    intro b
    rw [hsmul b]
    constructor
    · intro hb
      apply le_antisymm
      · rintro y hy
        obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
        rw [← hxy]
        exact (mem_stabSub.mp hb x).mpr hx
      · intro y hy
        refine Subgroup.mem_map.mpr ⟨b.symm y, ?_, b.apply_symm_apply y⟩
        exact (mem_stabSub.mp (Subgroup.inv_mem _ hb) y).mpr hy
    · intro hb
      rw [mem_stabSub]
      intro u
      constructor
      · intro hu
        have h : b.toMonoidHom u ∈ Y.map b.toMonoidHom := hb.symm ▸ hu
        obtain ⟨x, hx, hxu⟩ := Subgroup.mem_map.mp h
        rwa [b.injective hxu] at hx
      · intro hu
        have h : b.toMonoidHom u ∈ Y.map b.toMonoidHom := Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
        rwa [hb] at h
  have hstab_eq : MulAction.stabilizer (MulAut T) Y = stabSub Y := by
    ext b
    rw [MulAction.mem_stabilizer_iff]
    exact (hstab b).symm
  have hstab_stab : (B ⊓ stabSub Y).subgroupOf B = MulAction.stabilizer B Y := by
    rw [← MulAction.stabilizer_subgroupOf B Y, hstab_eq]
    ext x
    simp [Subgroup.mem_subgroupOf, x.2]
  have hcardstab : Nat.card (MulAction.stabilizer B Y) = Nat.card ↥(B ⊓ stabSub Y) := by
    rw [← hstab_stab]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have horb_bound : (MulAction.orbit B Y).ncard ≤ 2 := by
    have hsub : MulAction.orbit B Y ⊆ ({Y, Y'} : Set (Subgroup T)) := by
      rintro Z ⟨b, rfl⟩
      change (b : MulAut T) • Y ∈ ({Y, Y'} : Set (Subgroup T))
      rw [hsmul (b : MulAut T)]
      rcases horb (b : MulAut T) b.2 with h | h
      · exact Or.inl h
      · exact Or.inr h
    have hpair : ({Y, Y'} : Set (Subgroup T)).ncard ≤ 2 := by
      calc ({Y, Y'} : Set (Subgroup T)).ncard
          = (insert Y ({Y'} : Set (Subgroup T))).ncard := rfl
        _ ≤ ({Y'} : Set (Subgroup T)).ncard + 1 := Set.ncard_insert_le Y {Y'}
        _ = 2 := by simp
    exact (Set.ncard_le_ncard hsub).trans hpair
  have hidx : (MulAction.stabilizer B Y).index ≤ 2 := by
    rw [MulAction.index_stabilizer]
    exact horb_bound
  have hmul : (MulAction.stabilizer B Y).index * Nat.card (MulAction.stabilizer B Y) =
      Nat.card B := Subgroup.index_mul_card _
  calc Nat.card B
      = (MulAction.stabilizer B Y).index * Nat.card (MulAction.stabilizer B Y) := hmul.symm
    _ = (MulAction.stabilizer B Y).index * Nat.card ↥(B ⊓ stabSub Y) := by rw [hcardstab]
    _ ≤ 2 * Nat.card ↥(B ⊓ stabSub Y) := Nat.mul_le_mul_right _ hidx

theorem s16c1610_orbit_pair {ι : Type} {Y : ι → Subgroup T} (hind : iSupIndep Y)
    {B : Subgroup (MulAut T)} (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hperm : ∀ b ∈ B, ∀ i, ∃ j, (Y i).map b.toMonoidHom = Y j) {i j : ι} (hij : i ≠ j)
    {b : MulAut T} (hb : b ∈ B) (hbij : (Y i).map b.toMonoidHom = Y j) {u : T} (hu : u ∈ Y i)
    (hu1 : u ≠ 1) (hfix : u * b u ∈ fixV B) :
    ∀ b' ∈ B, (Y i).map b'.toMonoidHom = Y i ∨ (Y i).map b'.toMonoidHom = Y j := by
  intro b' hb'
  obtain ⟨i', hi'⟩ := hperm b' hb' i
  obtain ⟨i'', hi''⟩ := hperm b hb i'
  suffices h : Y i' = Y i ∨ Y i' = Y j by
    rcases h with h | h
    · exact Or.inl (hi'.trans h)
    · exact Or.inr (hi'.trans h)
  by_contra hcon
  rw [not_or] at hcon
  have hi'i : i' ≠ i := fun h => hcon.1 (by rw [h])
  have hi'j : i' ≠ j := fun h => hcon.2 (by rw [h])
  have hxu : b' u ∈ Y i' := hi' ▸ Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
  have hyu : b (b' u) ∈ Y i'' := hi'' ▸ Subgroup.mem_map.mpr ⟨b' u, hxu, rfl⟩
  have hcomm' : b' (b u) = b (b' u) := by
    have h := congrArg (fun f : MulAut T => f u) (hBc b' hb' b hb)
    simpa using h
  have hfix' : b' (u * b u) = u * b u := hfix b' hb'
  have hxy : u * b u = b' u * b (b' u) := by
    rw [← hfix', map_mul, hcomm']
  have hbu : b u ∈ Y j := hbij ▸ Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
  have hWi : Y i ≤ ⨆ k ∈ ({i, j} : Set ι), Y k :=
    le_iSup₂ (f := fun k (_ : k ∈ ({i, j} : Set ι)) => Y k) i (by simp)
  have hWj : Y j ≤ ⨆ k ∈ ({i, j} : Set ι), Y k :=
    le_iSup₂ (f := fun k (_ : k ∈ ({i, j} : Set ι)) => Y k) j (by simp)
  have huv : u * b u ∈ ⨆ k ∈ ({i, j} : Set ι), Y k :=
    Subgroup.mul_mem _ (hWi hu) (hWj hbu)
  have hd1 : Disjoint (Y i') (⨆ k ∈ ({i, j} : Set ι), Y k) :=
    hind.disjoint_biSup (by simp [hi'i, hi'j])
  by_cases hcase : i'' = i ∨ i'' = j
  · have hy : b (b' u) ∈ ⨆ k ∈ ({i, j} : Set ι), Y k := by
      rcases hcase with h | h
      · exact hWi (h ▸ hyu)
      · exact hWj (h ▸ hyu)
    have hx : b' u ∈ ⨆ k ∈ ({i, j} : Set ι), Y k := by
      have heq : b' u = (u * b u) * (b (b' u))⁻¹ := by
        rw [hxy]
        group
      rw [heq]
      exact Subgroup.mul_mem _ huv (Subgroup.inv_mem _ hy)
    have hx1 : b' u = 1 := Subgroup.mem_bot.mp (hd1.le_bot ⟨hxu, hx⟩)
    exact hu1 (b'.injective (by rw [hx1, map_one]))
  · have hii'' : i'' ≠ i := (not_or.mp hcase).1
    have hji'' : i'' ≠ j := (not_or.mp hcase).2
    have hst : Disjoint ({i, j} : Set ι) ({i', i''} : Set ι) := by
      rw [Set.disjoint_left]
      rintro k hk hk'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk hk'
      rcases hk with rfl | rfl
      · rcases hk' with h | h
        · exact hi'i h.symm
        · exact hii'' h.symm
      · rcases hk' with h | h
        · exact hi'j h.symm
        · exact hji'' h.symm
    have hd2 : Disjoint (⨆ k ∈ ({i, j} : Set ι), Y k) (⨆ k ∈ ({i', i''} : Set ι), Y k) :=
      hind.disjoint_biSup_biSup' (s := ({i, j} : Set ι)) (t := ({i', i''} : Set ι)) hst
        ((Set.finite_singleton j).insert i)
    have hW'i : Y i' ≤ ⨆ k ∈ ({i', i''} : Set ι), Y k :=
      le_iSup₂ (f := fun k (_ : k ∈ ({i', i''} : Set ι)) => Y k) i' (by simp)
    have hW'' : Y i'' ≤ ⨆ k ∈ ({i', i''} : Set ι), Y k :=
      le_iSup₂ (f := fun k (_ : k ∈ ({i', i''} : Set ι)) => Y k) i'' (by simp)
    have hxysup : b' u * b (b' u) ∈ ⨆ k ∈ ({i', i''} : Set ι), Y k :=
      Subgroup.mul_mem _ (hW'i hxu) (hW'' hyu)
    have h1 : b' u * b (b' u) = 1 :=
      Subgroup.mem_bot.mp (hd2.le_bot ⟨hxy ▸ huv, hxysup⟩)
    have hu_eq : u = (b u)⁻¹ := mul_eq_one_iff_eq_inv.mp (hxy.trans h1)
    have hubot : u ∈ (⊥ : Subgroup T) := by
      refine (hind.pairwiseDisjoint hij).le_bot ⟨hu, ?_⟩
      rw [hu_eq]
      exact Subgroup.inv_mem _ hbu
    exact hu1 (Subgroup.mem_bot.mp hubot)

end Generic

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
