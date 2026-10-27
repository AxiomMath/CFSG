module

public import CFSG.Quasithin.EmptyFaithful.S151S1

public section

namespace CFSG.Quasithin.S151S6

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem comm_eq_one_of_central_ext {H : Type*} [Group H] [Finite H] {K B' : Subgroup H}
    (hK : K ≤ Subgroup.center H) (hK2 : IsPGroup 2 ↥K) (hB : ¬ 2 ∣ B'.index) {z : H}
    (hz : ∀ x ∈ B', x * z = z * x) {l : H} (hl : l * z * l⁻¹ * z⁻¹ ∈ K) : l * z = z * l := by
  have hcen : ∀ k ∈ K, ∀ g : H, g * k = k * g := fun k hk g =>
    Subgroup.mem_center_iff.mp (hK hk) g
  have hmul : ∀ a b : H, b * z * b⁻¹ * z⁻¹ ∈ K →
      a * b * z * (a * b)⁻¹ * z⁻¹ = (b * z * b⁻¹ * z⁻¹) * (a * z * a⁻¹ * z⁻¹) := by
    intro a b hb
    have h1 := hcen _ hb a
    calc a * b * z * (a * b)⁻¹ * z⁻¹ = (a * (b * z * b⁻¹ * z⁻¹)) * (z * a⁻¹ * z⁻¹) := by group
      _ = ((b * z * b⁻¹ * z⁻¹) * a) * (z * a⁻¹ * z⁻¹) := by rw [h1]
      _ = (b * z * b⁻¹ * z⁻¹) * (a * z * a⁻¹ * z⁻¹) := by group
  have hinv : ∀ a : H, a * z * a⁻¹ * z⁻¹ ∈ K → a⁻¹ * z * a⁻¹⁻¹ * z⁻¹ ∈ K := by
    intro a ha
    have hk : z * a * z⁻¹ * a⁻¹ ∈ K := by
      have h2 : (a * z * a⁻¹ * z⁻¹)⁻¹ ∈ K := K.inv_mem ha
      have h3 : (a * z * a⁻¹ * z⁻¹)⁻¹ = z * a * z⁻¹ * a⁻¹ := by group
      rwa [h3] at h2
    have h4 := hcen _ hk a⁻¹
    have h5 : a⁻¹ * z * a⁻¹⁻¹ * z⁻¹ = z * a * z⁻¹ * a⁻¹ := by
      calc a⁻¹ * z * a⁻¹⁻¹ * z⁻¹ = (a⁻¹ * (z * a * z⁻¹ * a⁻¹)) * a := by group
        _ = ((z * a * z⁻¹ * a⁻¹) * a⁻¹) * a := by rw [h4]
        _ = z * a * z⁻¹ * a⁻¹ := by group
    rw [h5]
    exact hk
  let P : Subgroup H :=
    { carrier := {a | a * z * a⁻¹ * z⁻¹ ∈ K}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        show a * b * z * (a * b)⁻¹ * z⁻¹ ∈ K
        rw [hmul a b hb]
        exact K.mul_mem hb ha
      inv_mem' := fun {a} ha => hinv a ha }
  have hmemP : ∀ a : H, a ∈ P ↔ a * z * a⁻¹ * z⁻¹ ∈ K := fun a => Iff.rfl
  let lam : ↥P →* ↥K :=
    MonoidHom.mk' (fun a => ⟨(a : H) * z * (a : H)⁻¹ * z⁻¹, (hmemP _).mp a.2⟩) (by
      intro a b
      apply Subtype.ext
      show ((a : H) * (b : H)) * z * ((a : H) * (b : H))⁻¹ * z⁻¹ =
        ((a : H) * z * (a : H)⁻¹ * z⁻¹) * ((b : H) * z * (b : H)⁻¹ * z⁻¹)
      rw [hmul (a : H) (b : H) ((hmemP _).mp b.2)]
      exact hcen _ ((hmemP _).mp a.2) _)
  have hBP : B' ≤ P := fun x hx => by
    rw [hmemP, hz x hx]
    simp
  have hker : B'.subgroupOf P ≤ lam.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    show (x : H) * z * (x : H)⁻¹ * z⁻¹ = 1
    have hx' : (x : H) ∈ B' := hx
    rw [hz _ hx']
    group
  have hdvd : lam.ker.index ∣ B'.index :=
    (Subgroup.index_dvd_of_le hker).trans (Subgroup.relIndex_dvd_index_of_le hBP)
  have hodd : ¬ 2 ∣ lam.ker.index := fun h => hB (h.trans hdvd)
  have hcard : Nat.card lam.range = 1 := by
    have hpg : IsPGroup 2 ↥lam.range := hK2.to_subgroup _
    rcases hpg.card_eq_or_dvd with h | h
    · exact h
    · exfalso
      apply hodd
      rw [Subgroup.index_ker]
      exact h
  have hrange : lam.range = ⊥ := Subgroup.card_eq_one.mp hcard
  have hl1 : lam ⟨l, (hmemP l).mpr hl⟩ = 1 := by
    have h1 : lam ⟨l, (hmemP l).mpr hl⟩ ∈ lam.range := MonoidHom.mem_range.mpr ⟨_, rfl⟩
    rw [hrange] at h1
    exact Subgroup.mem_bot.mp h1
  have hl2 : l * z * l⁻¹ * z⁻¹ = 1 := congrArg Subtype.val hl1
  calc l * z = (l * z * l⁻¹ * z⁻¹) * (z * l) := by group
    _ = z * l := by rw [hl2, one_mul]

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem autFixOn_of_central_quotient {L B Kg : Subgroup G} {Q : Type} [Group Q]
    (hperf : Group.IsPerfect ↥L) (hBL : B ≤ L) (π : ↥L →* Q) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center ↥L) (hKg : π.ker = Kg.subgroupOf L)
    (hKgN : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (Kg : Set G))
    (hfix : ∀ φ : Q →* Q, (∀ q, φ (φ q) = q) → (∀ x ∈ (B.subgroupOf L).map π, φ x = x) →
      ∃ c ∈ centerOf ((B.subgroupOf L).map π), ∀ q, φ q = c * q * c⁻¹) :
    AutFixOn L B := by
  intro z hzN hz2 hzB
  have hmem : ∀ l : ↥L, z * (l : G) * z⁻¹ ∈ L := fun l =>
    (Subgroup.mem_normalizer_iff.mp hzN l).mp l.2
  let φL : ↥L →* ↥L := MonoidHom.mk' (fun l => ⟨z * (l : G) * z⁻¹, hmem l⟩) (by
    intro a b
    apply Subtype.ext
    show z * ((a : G) * (b : G)) * z⁻¹ = (z * (a : G) * z⁻¹) * (z * (b : G) * z⁻¹)
    group)
  have hφφ : ∀ l, φL (φL l) = l := by
    intro l
    apply Subtype.ext
    show z * (z * (l : G) * z⁻¹) * z⁻¹ = l
    have hzz : z * z = 1 := by rw [← pow_two]; exact hz2
    calc z * (z * (l : G) * z⁻¹) * z⁻¹ = (z * z) * (l : G) * (z * z)⁻¹ := by group
      _ = l := by rw [hzz]; group
  have hKinv : ∀ l : ↥L, π l = 1 → π (φL l) = 1 := by
    intro l hl
    have hl' : (l : G) ∈ Kg := by
      have h0 : l ∈ π.ker := hl
      rw [hKg] at h0
      exact h0
    have hz' : z ∈ Subgroup.normalizer (Kg : Set G) := hKgN hzN
    have h1 : z * (l : G) * z⁻¹ ∈ Kg := (Subgroup.mem_normalizer_iff.mp hz' l).mp hl'
    have h2 : φL l ∈ π.ker := by
      rw [hKg]
      exact h1
    exact h2
  have hle : π.ker ≤ (π.comp φL).ker := fun l hl => by
    rw [MonoidHom.mem_ker] at hl ⊢
    exact hKinv l hl
  let φb : Q →* Q := MonoidHom.liftOfSurjective π hπ ⟨π.comp φL, hle⟩
  have hφb : ∀ l, φb (π l) = π (φL l) := fun l => by
    simp [φb]
  have hφbb : ∀ q, φb (φb q) = q := by
    intro q
    obtain ⟨l, rfl⟩ := hπ q
    rw [hφb, hφb, hφφ]
  have hφbP : ∀ x ∈ (B.subgroupOf L).map π, φb x = x := by
    rintro x ⟨b, hb, rfl⟩
    rw [hφb]
    congr 1
    apply Subtype.ext
    show z * (b : G) * z⁻¹ = b
    have hbB : (b : G) ∈ B := hb
    rw [hzB _ hbB]
    group
  obtain ⟨c, hc, hcq⟩ := hfix φb hφbb hφbP
  obtain ⟨b', hb', hb'c⟩ := hc.1
  have hκmem : ∀ l : ↥L, (b' * l * b'⁻¹)⁻¹ * φL l ∈ π.ker := by
    intro l
    have h1 : π (φL l) = c * π l * c⁻¹ := by rw [← hφb, hcq]
    have h2 : π (b' * l * b'⁻¹) = c * π l * c⁻¹ := by rw [map_mul, map_mul, map_inv, hb'c]
    rw [MonoidHom.mem_ker, map_mul, map_inv, h2, h1]
    group
  let κ : ↥L →* ↥L := MonoidHom.mk' (fun l => (b' * l * b'⁻¹)⁻¹ * φL l) (by
    intro a b
    have hca : (b' * a * b'⁻¹)⁻¹ * φL a ∈ Subgroup.center ↥L := hker (hκmem a)
    have h1 := Subgroup.mem_center_iff.mp hca (b' * b * b'⁻¹)⁻¹
    calc (b' * (a * b) * b'⁻¹)⁻¹ * φL (a * b)
        = (b' * b * b'⁻¹)⁻¹ * ((b' * a * b'⁻¹)⁻¹ * φL a) * φL b := by rw [map_mul]; group
      _ = ((b' * a * b'⁻¹)⁻¹ * φL a) * (b' * b * b'⁻¹)⁻¹ * φL b := by rw [h1]
      _ = ((b' * a * b'⁻¹)⁻¹ * φL a) * ((b' * b * b'⁻¹)⁻¹ * φL b) := by group)
  have hκ1 : ∀ l, κ l = 1 := by
    have hcomm : commutator ↥L ≤ κ.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      have hκa : κ a ∈ Subgroup.center ↥L := hker (hκmem a)
      exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hκa (κ b)).symm
    rw [hperf.commutator_eq_top, top_le_iff] at hcomm
    intro l
    have : l ∈ κ.ker := by rw [hcomm]; exact Subgroup.mem_top l
    exact this
  have hmain : ∀ l ∈ L, z * l * z⁻¹ = (b' : G) * l * (b' : G)⁻¹ := by
    intro l hl
    have h2 : (b' * ⟨l, hl⟩ * b'⁻¹)⁻¹ * φL ⟨l, hl⟩ = 1 := hκ1 ⟨l, hl⟩
    have h3 := congrArg Subtype.val h2
    have h4 : ((b' : G) * l * (b' : G)⁻¹)⁻¹ * (z * l * z⁻¹) = 1 := h3
    exact (inv_mul_eq_one.mp h4).symm
  refine ⟨(b' : G), ⟨hb', Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩, hmain⟩
  have hzx : z * x * z⁻¹ = x := by
    rw [hzB x hx]
    group
  have h1 := hmain x (hBL hx)
  have h2 : (b' : G) * x * (b' : G)⁻¹ = x := h1.symm.trans hzx
  have h3 : (b' : G) * x = x * (b' : G) := mul_inv_eq_iff_eq_mul.mp h2
  exact h3.symm

theorem isMax_comap_of_surjective {H Q : Type*} [Group H] [Group Q] (π : H →* Q)
    (hπ : Function.Surjective π) {D : Subgroup Q} (h : IsMaxSubgroupIn ⊤ D) :
    IsMaxSubgroupIn ⊤ (D.comap π) := by
  refine ⟨?_, fun K hK _ => ?_⟩
  · rw [lt_top_iff_ne_top]
    intro htop
    have hD : D = ⊤ := by
      rw [eq_top_iff]
      intro q _
      obtain ⟨x, rfl⟩ := hπ q
      have hx : x ∈ D.comap π := by rw [htop]; exact Subgroup.mem_top x
      exact hx
    exact h.1.ne hD
  · have hDK : D < K.map π := by
      refine lt_of_le_of_ne ?_ ?_
      · rw [← Subgroup.map_comap_eq_self_of_surjective hπ D]
        exact Subgroup.map_mono hK.le
      · intro hEq
        have hle : K ≤ D.comap π := by
          intro x hx
          have hx' : π x ∈ K.map π := ⟨x, hx, rfl⟩
          rw [← hEq] at hx'
          exact hx'
        exact absurd hK (not_lt_of_ge hle)
    have htop : K.map π = ⊤ := h.2 _ hDK le_top
    rw [eq_top_iff]
    intro x _
    have hx : π x ∈ K.map π := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨k, hk, hkx⟩ := hx
    have hker : k⁻¹ * x ∈ D.comap π := by
      show π (k⁻¹ * x) ∈ D
      rw [map_mul, map_inv, hkx, inv_mul_cancel]
      exact D.one_mem
    have hxk : x = k * (k⁻¹ * x) := by group
    rw [hxk]
    exact K.mul_mem hk (hK.le hker)

omit [Finite G] in
theorem isMaxSubgroupIn_of_subgroupOf {L C : Subgroup G} (hCL : C ≤ L)
    (h : IsMaxSubgroupIn (⊤ : Subgroup ↥L) (C.subgroupOf L)) : IsMaxSubgroupIn L C := by
  refine ⟨lt_of_le_of_ne hCL ?_, fun K hK hKL => ?_⟩
  · intro hCeq
    apply h.1.ne
    rw [hCeq]
    exact Subgroup.subgroupOf_self L
  · have hlt : C.subgroupOf L < K.subgroupOf L := by
      refine lt_of_le_of_ne (Subgroup.comap_mono hK.le) ?_
      intro hEq
      apply hK.ne
      rw [← Subgroup.map_subgroupOf_eq_of_le hCL, ← Subgroup.map_subgroupOf_eq_of_le hKL, hEq]
    have htop := h.2 _ hlt le_top
    apply le_antisymm hKL
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥L) ∈ K.subgroupOf L := by rw [htop]; exact Subgroup.mem_top _
    exact hx'

theorem centralizer_max_of_central_quotient {L B : Subgroup G} {Q : Type} [Group Q]
    (hBL : IsSylowTwoOf B L) (π : ↥L →* Q) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center ↥L) (hK2 : IsPGroup 2 ↥π.ker)
    (hne : ¬ L ≤ Subgroup.centralizer (centerOf B : Set G))
    (hmaxW : ∀ W : Subgroup Q, W ≤ centerOf ((B.subgroupOf L).map π) → W ≠ ⊥ →
      IsMaxSubgroupIn ⊤ (Subgroup.centralizer (W : Set Q))) :
    IsMaxSubgroupIn L (L ⊓ Subgroup.centralizer (centerOf B : Set G)) := by
  set B' : Subgroup ↥L := B.subgroupOf L with hB'def
  set P : Subgroup Q := B'.map π with hPdef
  have hodd : ¬ 2 ∣ B'.index := hBL.2.2
  have hZ' : ∀ x : ↥L, x ∈ centerOf B' ↔ (x : G) ∈ centerOf B := by
    intro x
    constructor
    · rintro ⟨hx1, hx2⟩
      refine ⟨hx1, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      have hy' : (⟨y, hBL.1 hy⟩ : ↥L) ∈ B' := hy
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hx2 _ hy')
    · rintro ⟨hx1, hx2⟩
      refine ⟨hx1, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx2 (y : G) hy)
  have hC' : ∀ x : ↥L, x ∈ Subgroup.centralizer (centerOf B' : Set ↥L) ↔
      (x : G) ∈ Subgroup.centralizer (centerOf B : Set G) := by
    intro x
    constructor
    · intro hx
      refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
      have hwL : w ∈ L := hBL.1 hw.1
      have hw' : (⟨w, hwL⟩ : ↥L) ∈ centerOf B' := (hZ' _).mpr hw
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hx _ hw')
    · intro hx
      refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx (w : G) ((hZ' w).mp hw))
  have hsub : (L ⊓ Subgroup.centralizer (centerOf B : Set G)).subgroupOf L =
      Subgroup.centralizer (centerOf B' : Set ↥L) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, hC' x]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  have hZP : ∀ z ∈ centerOf B', π z ∈ centerOf P := by
    intro z hz
    refine ⟨Subgroup.mem_map_of_mem π hz.1, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    obtain ⟨b, hb, rfl⟩ := hy
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hz.2 b hb]
  have hz0 : ∃ z₀ ∈ centerOf B', π z₀ ≠ 1 := by
    by_contra hcon0
    have hcon : ∀ z ∈ centerOf B', π z = 1 := fun z hz => by
      by_contra hne1
      exact hcon0 ⟨z, hz, hne1⟩
    apply hne
    intro x hx
    refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
    have hwL : w ∈ L := hBL.1 hw.1
    have hw' : (⟨w, hwL⟩ : ↥L) ∈ centerOf B' := (hZ' _).mpr hw
    have hker1 : (⟨w, hwL⟩ : ↥L) ∈ π.ker := hcon _ hw'
    have hcentral : (⟨w, hwL⟩ : ↥L) ∈ Subgroup.center ↥L := hker hker1
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hcentral ⟨x, hx⟩).symm
  obtain ⟨z₀, hz₀, hπz₀⟩ := hz0
  set W : Subgroup Q := (centerOf B').map π with hWdef
  have hWle : W ≤ centerOf P := by
    rintro _ ⟨z, hz, rfl⟩
    exact hZP z hz
  have hWne : W ≠ ⊥ := by
    intro hW
    have h1 : π z₀ ∈ W := ⟨z₀, hz₀, rfl⟩
    rw [hW] at h1
    exact hπz₀ (Subgroup.mem_bot.mp h1)
  have hCeq : Subgroup.centralizer (centerOf B' : Set ↥L) =
      (Subgroup.centralizer (W : Set Q)).comap π := by
    ext h
    rw [Subgroup.mem_comap]
    constructor
    · intro hh
      refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
      obtain ⟨w, hw, rfl⟩ := hv
      have h1 := Subgroup.mem_centralizer_iff.mp hh w hw
      rw [← map_mul, ← map_mul, h1]
    · intro hh
      refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
      have h1 := Subgroup.mem_centralizer_iff.mp hh (π w) ⟨w, hw, rfl⟩
      have hl : h * w * h⁻¹ * w⁻¹ ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
        rw [← h1]
        group
      have hz : ∀ x ∈ B', x * w = w * x := fun x hx => Subgroup.mem_centralizer_iff.mp hw.2 x hx
      exact (comm_eq_one_of_central_ext hker hK2 hodd hz hl).symm
  have hmaxC : IsMaxSubgroupIn ⊤ (Subgroup.centralizer (centerOf B' : Set ↥L)) := by
    rw [hCeq]
    exact isMax_comap_of_surjective π hπ (hmaxW W hWle hWne)
  apply isMaxSubgroupIn_of_subgroupOf inf_le_left
  rw [hsub]
  exact hmaxC

end CFSG.Quasithin.S151S6
