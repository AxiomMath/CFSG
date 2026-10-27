module

public import CFSG.Quasithin.Background.Asc81cTenFourA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

variable {W : Type} [CommGroup W]

private theorem s168e3_cyc_mem_fixV_zpowers {y : MulAut W} {w : W}
    (h : y w = w) : w ∈ fixV (Subgroup.zpowers y) := by
  rw [mem_fixV]
  intro g hg
  have hle : Subgroup.zpowers y ≤ MulAction.stabilizer (MulAut W) w := by
    rw [Subgroup.zpowers_le]
    exact (MulAction.mem_stabilizer_iff).mpr (by rw [MulAut.smul_def]; exact h)
  have := (MulAction.mem_stabilizer_iff).mp (hle hg)
  rwa [MulAut.smul_def] at this

private theorem s168e3_cyc_fixV_zpowers_mem {a b : MulAut W}
    (hcomm : a * b = b * a) (n : ℤ) {w : W} (hw : w ∈ fixV (Subgroup.zpowers b)) :
    (a ^ n) w ∈ fixV (Subgroup.zpowers b) := by
  have hc : Commute a b := hcomm
  rw [mem_fixV] at hw ⊢
  intro z hz
  rw [Subgroup.mem_zpowers_iff] at hz
  obtain ⟨m, rfl⟩ := hz
  have hcab : Commute (a ^ n) (b ^ m) := (hc.zpow_left n).zpow_right m
  calc (b ^ m) ((a ^ n) w) = ((b ^ m) * (a ^ n)) w := (MulAut.mul_apply ..).symm
    _ = ((a ^ n) * (b ^ m)) w := by rw [hcab.eq.symm]
    _ = (a ^ n) ((b ^ m) w) := MulAut.mul_apply ..
    _ = (a ^ n) w := by rw [hw (b ^ m) (Subgroup.mem_zpowers_iff.mpr ⟨m, rfl⟩)]

private theorem s168e3_cyc_commSub_zpowers_mem {a b : MulAut W}
    (hcomm : a * b = b * a) (n : ℤ) {u : W} (hu : u ∈ commSub ⊤ (Subgroup.zpowers b)) :
    (a ^ n) u ∈ commSub ⊤ (Subgroup.zpowers b) := by
  have hc : Commute a b := hcomm
  have hcn : MulAut.conj (a ^ n) b = b := by
    rw [MulAut.conj_apply, (hc.zpow_left n).eq, mul_assoc, mul_inv_cancel, mul_one]
  have hmap : (Subgroup.zpowers b).map (MulAut.conj (a ^ n)).toMonoidHom = Subgroup.zpowers b := by
    rw [MonoidHom.map_zpowers]
    exact congrArg Subgroup.zpowers hcn
  have hEq : (commSub ⊤ (Subgroup.zpowers b)).map (a ^ n).toMonoidHom =
      commSub ⊤ (Subgroup.zpowers b) := by
    rw [← CFSG.Quasithin.Asc81c.commSub_map_conj, hmap]
  have hmem : (a ^ n) u ∈ (commSub ⊤ (Subgroup.zpowers b)).map (a ^ n).toMonoidHom :=
    ⟨u, hu, rfl⟩
  rwa [hEq] at hmem

private lemma s168e3_cyc3_x_stable_fixV {x y : MulAut W} (hxy : x * y = y * x) :
    ∀ z ∈ fixV (Subgroup.zpowers y), x z ∈ fixV (Subgroup.zpowers y) := by
  intro z hz
  rw [mem_fixV] at hz ⊢
  intro m hm
  have hmx : Commute m x := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
    exact (show Commute y x from hxy.symm).zpow_left k
  calc m (x z) = (m * x) z := by rw [← MulAut.mul_apply]
    _ = (x * m) z := by rw [hmx.eq]
    _ = x (m z) := by rw [MulAut.mul_apply]
    _ = x z := by rw [hz m hm]

private lemma s168e3_cyc3_x_stable_commSub {x y : MulAut W} (hxy : x * y = y * x) :
    ∀ z ∈ commSub ⊤ (Subgroup.zpowers y), x z ∈ commSub ⊤ (Subgroup.zpowers y) := by
  have hmapY : (Subgroup.zpowers y).map (MulAut.conj x).toMonoidHom = Subgroup.zpowers y := by
    rw [MonoidHom.map_zpowers]
    congr 1
    change (MulAut.conj x) y = y
    rw [MulAut.conj_apply, hxy]
    group
  have h := CFSG.Quasithin.Asc81c.commSub_map_conj (Subgroup.zpowers y) x
  rw [hmapY] at h
  intro z hz
  rw [h]
  exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩

private lemma s168e3_cyc3_block_sub [Finite W] {x : MulAut W} {Z U : Subgroup W}
    (hUZ : U ≤ Z) (hxU : ∀ z ∈ U, x z ∈ U) (hfpf : ∀ w : W, x w = w → w = 1)
    (hZ : Nat.card ↥Z = 4) : U = ⊥ ∨ U = Z := by
  have hdvd : Nat.card ↥U ∣ 4 := by
    have h := Subgroup.card_dvd_of_le hUZ
    rwa [hZ] at h
  have hpos : 0 < Nat.card ↥U := Nat.card_pos
  have hle : Nat.card ↥U ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hne2 : Nat.card ↥U ≠ 2 := by
    intro h2
    obtain ⟨u, hu_ne, hu_uniq⟩ := (Nat.card_eq_two_iff' (1 : ↥U)).mp h2
    have hxu : x (u : W) ∈ U := hxU _ u.2
    have hxne : (⟨x (u : W), hxu⟩ : ↥U) ≠ 1 := by
      intro h
      have h1 : x (u : W) = 1 := congrArg Subtype.val h
      have h2' : (u : W) = 1 := x.injective (by rw [h1, map_one])
      exact hu_ne (Subtype.ext h2')
    have heq : (⟨x (u : W), hxu⟩ : ↥U) = u := hu_uniq _ hxne
    have hfix : x (u : W) = (u : W) := congrArg Subtype.val heq
    exact hu_ne (Subtype.ext (hfpf (u : W) hfix))
  have hdvd' : Nat.card ↥U ∣ 2 ^ 2 := by
    rw [show 2 ^ 2 = 4 by norm_num]
    exact hdvd
  have hmem : Nat.card ↥U = 1 ∨ Nat.card ↥U = 4 := by
    obtain ⟨k, _, hkU⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd'
    have hk012 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk012 with rfl | rfl | rfl
    · exact Or.inl (by rw [hkU]; norm_num)
    · exact absurd (by rw [hkU]; norm_num : Nat.card ↥U = 2) hne2
    · exact Or.inr (by rw [hkU]; norm_num)
  rcases hmem with h1 | h4
  · exact Or.inl (Subgroup.card_eq_one.mp h1)
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge hUZ (by rw [h4, hZ]))

private lemma s168e3_cyc3_pow_three_apply {ξ : MulAut W} (hξ : ξ ^ 3 = 1) (z : W) :
    ξ (ξ (ξ z)) = z := by
  have h : (ξ ^ 3) z = ξ (ξ (ξ z)) := by simp [pow_succ, MulAut.mul_apply, pow_two]
  rw [← h, hξ, MulAut.one_apply]

private lemma s168e3_cyc3_orbit_exhaust {Z : Subgroup W} (hZ : Nat.card ↥Z = 4) {ξ : MulAut W}
    (hξ : ξ ^ 3 = 1) (hξZ : ∀ z ∈ Z, ξ z ∈ Z) (hfix : ∀ z ∈ Z, ξ z = z → z = 1)
    {z₀ : W} (hz₀ : z₀ ∈ Z) (hz₀1 : z₀ ≠ 1) :
    ∀ z ∈ Z, z = 1 ∨ z = z₀ ∨ z = ξ z₀ ∨ z = ξ (ξ z₀) := by
  have hz₁Z : ξ z₀ ∈ Z := hξZ z₀ hz₀
  have hz₂Z : ξ (ξ z₀) ∈ Z := hξZ (ξ z₀) hz₁Z
  have h1z₀ : (1 : W) ≠ z₀ := fun h => hz₀1 h.symm
  have h1z₁ : (1 : W) ≠ ξ z₀ := by
    intro h
    exact hz₀1 (ξ.injective (by rw [h.symm, map_one]))
  have h1z₂ : (1 : W) ≠ ξ (ξ z₀) := by
    intro h
    have h2 : ξ z₀ = 1 := ξ.injective (by rw [h.symm, map_one])
    exact hz₀1 (ξ.injective (by rw [h2, map_one]))
  have hz₀z₁ : z₀ ≠ ξ z₀ := fun h => hz₀1 (hfix z₀ hz₀ h.symm)
  have hz₀z₂ : z₀ ≠ ξ (ξ z₀) := by
    intro h
    have h3 : ξ (ξ (ξ z₀)) = ξ z₀ := (congrArg ξ h).symm
    rw [s168e3_cyc3_pow_three_apply hξ z₀] at h3
    exact hz₀z₁ h3
  have hz₁z₂ : ξ z₀ ≠ ξ (ξ z₀) := fun h => hz₀z₁ (ξ.injective h)
  have hnot1 : (1 : W) ∉ ({z₀, ξ z₀, ξ (ξ z₀)} : Set W) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h1z₀, h1z₁, h1z₂⟩
  have hnot2 : z₀ ∉ ({ξ z₀, ξ (ξ z₀)} : Set W) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hz₀z₁, hz₀z₂⟩
  have hnot3 : ξ z₀ ∉ ({ξ (ξ z₀)} : Set W) := by
    simpa using hz₁z₂
  have hS : ({1, z₀, ξ z₀, ξ (ξ z₀)} : Set W).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (s := ({z₀, ξ z₀, ξ (ξ z₀)} : Set W)) hnot1,
      Set.ncard_insert_of_notMem (s := ({ξ z₀, ξ (ξ z₀)} : Set W)) hnot2,
      Set.ncard_insert_of_notMem (s := ({ξ (ξ z₀)} : Set W)) hnot3, Set.ncard_singleton]
  have hZc : (Z : Set W).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hZ
  intro z hz
  by_contra hmem
  have hz4 : z ∉ ({1, z₀, ξ z₀, ξ (ξ z₀)} : Set W) := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  have hins : (insert z ({1, z₀, ξ z₀, ξ (ξ z₀)} : Set W)).ncard = 5 := by
    rw [Set.ncard_insert_of_notMem hz4, hS]
  have hsub : insert z ({1, z₀, ξ z₀, ξ (ξ z₀)} : Set W) ⊆ (Z : Set W) := by
    intro v hv
    rw [Set.mem_insert_iff] at hv
    rcases hv with rfl | hv
    · exact hz
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact Z.one_mem
      · exact hz₀
      · exact hz₁Z
      · exact hz₂Z
  haveI : Finite (Z : Set W) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_coe_set_eq, hZc]; decide)
  have hle := Set.ncard_le_ncard hsub
  rw [hins, hZc] at hle
  omega

private lemma s168e3_cyc3_pow_eq_of_reg {Z : Subgroup W} (hZ : Nat.card ↥Z = 4)
    {ξ : MulAut W} (hξ : ξ ^ 3 = 1) (hξZ : ∀ z ∈ Z, ξ z ∈ Z)
    (hfix : ∀ z ∈ Z, ξ z = z → z = 1)
    {z z' : W} (hz : z ∈ Z) (hz1 : z ≠ 1) (hz' : z' ∈ Z) (hz'1 : z' ≠ 1) :
    ∃ a : ℕ, a < 3 ∧ (ξ ^ a) z = z' := by
  have hex := s168e3_cyc3_orbit_exhaust hZ hξ hξZ hfix hz hz1
  rcases hex z' hz' with h | h | h | h
  · exact absurd h hz'1
  · exact ⟨0, by norm_num, by rw [h, pow_zero, MulAut.one_apply]⟩
  · exact ⟨1, by norm_num, by rw [h, pow_one]⟩
  · refine ⟨2, by norm_num, ?_⟩
    rw [h, pow_two, MulAut.mul_apply]

private lemma s168e3_cyc3_pow_fix {Z : Subgroup W} {y : MulAut W} (hy : ∀ z ∈ Z, y z = z) :
    ∀ n : ℕ, ∀ z ∈ Z, (y ^ n) z = z := by
  intro n
  induction n with
  | zero => intro z _; rw [pow_zero, MulAut.one_apply]
  | succ n ih =>
      intro z hz
      rw [pow_succ, MulAut.mul_apply, ih (y z) (by rw [hy z hz]; exact hz), hy z hz]

private lemma s168e3_cyc3_shift [Finite W] {A : Subgroup (MulAut W)} {x g y : MulAut W}
    {Z Z₁ Z₂ : Subgroup W} (hgA : g ∈ A) (hyA : y ∈ A) (hordy : orderOf y = 3)
    (hxZ' : ∀ z ∈ Z.map g.toMonoidHom, x z ∈ Z.map g.toMonoidHom)
    (hfixZy : ∀ z ∈ Z, y z = z)
    (hZcard : Nat.card ↥Z = 4) (hZ₁card : Nat.card ↥Z₁ = 4) (hZ₂card : Nat.card ↥Z₂ = 4)
    (hxZ₁ : ∀ z ∈ Z₁, x z ∈ Z₁) (hxZ₂ : ∀ z ∈ Z₂, x z ∈ Z₂)
    (hfpf : ∀ w : W, x w = w → w = 1)
    (hne₁ : Z.map g.toMonoidHom ≠ Z₁) (hne₂ : Z.map g.toMonoidHom ≠ Z₂) :
    (Z.map g.toMonoidHom) ⊓ Z₁ = ⊥ ∧ (Z.map g.toMonoidHom) ⊓ Z₂ = ⊥ ∧
    Nat.card ↥(Z.map g.toMonoidHom) = 4 ∧ (g * y * g⁻¹) ∈ A ∧
    orderOf (g * y * g⁻¹) = 3 ∧ (∀ z ∈ Z.map g.toMonoidHom, (g * y * g⁻¹) z = z) := by
  have hZ'card : Nat.card ↥(Z.map g.toMonoidHom) = 4 := by
    rw [Subgroup.card_map_of_injective (K := Z) (f := g.toMonoidHom)
      (fun a b h => g.injective h), hZcard]
  have hZ'₁ : Z.map g.toMonoidHom ⊓ Z₁ = ⊥ := by
    have h := s168e3_cyc3_block_sub (Z := Z₁) (U := Z.map g.toMonoidHom ⊓ Z₁) inf_le_right
      (fun u hu => ⟨hxZ' u hu.1, hxZ₁ u hu.2⟩) hfpf hZ₁card
    rcases h with h | h
    · exact h
    · exfalso
      exact hne₁ (Subgroup.eq_of_le_of_card_ge (by rw [← h]; exact inf_le_left)
        (by rw [hZ'card, hZ₁card])).symm
  have hZ'₂ : Z.map g.toMonoidHom ⊓ Z₂ = ⊥ := by
    have h := s168e3_cyc3_block_sub (Z := Z₂) (U := Z.map g.toMonoidHom ⊓ Z₂) inf_le_right
      (fun u hu => ⟨hxZ' u hu.1, hxZ₂ u hu.2⟩) hfpf hZ₂card
    rcases h with h | h
    · exact h
    · exfalso
      exact hne₂ (Subgroup.eq_of_le_of_card_ge (by rw [← h]; exact inf_le_left)
        (by rw [hZ'card, hZ₂card])).symm
  have hhA : g * y * g⁻¹ ∈ A := A.mul_mem (A.mul_mem hgA hyA) (A.inv_mem hgA)
  have hord : orderOf (g * y * g⁻¹) = 3 := by
    rw [show g * y * g⁻¹ = MulAut.conj g y from (MulAut.conj_apply g y).symm]
    exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y).trans hordy
  have hfix : ∀ z ∈ Z.map g.toMonoidHom, (g * y * g⁻¹) z = z := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hz
    simp only [MulEquiv.coe_toMonoidHom, MulAut.mul_apply, MulAut.inv_apply_self, hfixZy u hu]
  exact ⟨hZ'₁, hZ'₂, hZ'card, hhA, hord, hfix⟩

private lemma s168e3_cyc_map_x_stable [Finite W] {A L : Subgroup (MulAut W)} {x g : MulAut W}
    {Z : Subgroup W} (hgA : g ∈ A) (hLn : ∀ a ∈ A, L.map (MulAut.conj a).toMonoidHom = L)
    (hLx : L = Subgroup.zpowers x) (hZpow : ∀ n : ℤ, ∀ z ∈ Z, (x ^ n) z ∈ Z) :
    ∀ z ∈ Z.map g.toMonoidHom, x z ∈ Z.map g.toMonoidHom := by
  intro z hz
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hz
  have hxL : x ∈ L := by rw [hLx]; exact Subgroup.mem_zpowers x
  have hgx : g⁻¹ * x * g ∈ L := by
    have h := Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hxL
    rwa [hLn g⁻¹ (A.inv_mem hgA)] at h
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (by rwa [hLx] at hgx)
  refine Subgroup.mem_map.mpr ⟨(x ^ n) u, hZpow n u hu, ?_⟩
  change g ((x ^ n) u) = x (g u)
  rw [hn]
  simp only [MulAut.mul_apply, MulAut.apply_inv_self]

theorem s168e3_cyc3_fix [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {A E L : Subgroup (MulAut W)}
    {x y₁ y₂ : MulAut W} {Z₁ Z₂ : Subgroup W} (hEA : E ≤ A)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE3 : ∀ a ∈ E, a ^ 3 = 1) (hxE : x ∈ E)
    (hy₁E : y₁ ∈ E) (hy₂E : y₂ ∈ E) (hy₁ : y₁ ≠ 1) (hy₂ : y₂ ≠ 1)
    (hLx : L = Subgroup.zpowers x) (hLn : ∀ g ∈ A, L.map (MulAut.conj g).toMonoidHom = L)
    (hfpf : ∀ w : W, x w = w → w = 1)
    (hfix₁ : fixV (Subgroup.zpowers y₁) = Z₁) (hfix₂ : fixV (Subgroup.zpowers y₂) = Z₂)
    (hcom₁ : commSub ⊤ (Subgroup.zpowers y₁) = Z₂) (hcom₂ : commSub ⊤ (Subgroup.zpowers y₂) = Z₁)
    (hZ₁ : Nat.card ↥Z₁ = 4) (hZ₂ : Nat.card ↥Z₂ = 4) (hZ : Z₁ ⊓ Z₂ = ⊥) (hZtop : Z₁ ⊔ Z₂ = ⊤)
    (hnp : ¬ ∀ g ∈ A, (Z₁.map g.toMonoidHom = Z₁ ∧ Z₂.map g.toMonoidHom = Z₂) ∨
      (Z₁.map g.toMonoidHom = Z₂ ∧ Z₂.map g.toMonoidHom = Z₁)) :
    ∀ w : W, w ≠ 1 → ∃ b ∈ A, orderOf b = 3 ∧ b w = w := by
  classical
  have hx3 : x ^ 3 = 1 := hE3 x hxE
  have hy₁3 : y₁ ^ 3 = 1 := hE3 y₁ hy₁E
  have hy₂3 : y₂ ^ 3 = 1 := hE3 y₂ hy₂E
  have hy₁A : y₁ ∈ A := hEA hy₁E
  have hy₂A : y₂ ∈ A := hEA hy₂E
  have hordy₁ : orderOf y₁ = 3 := by
    have hdvd : orderOf y₁ ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hy₁3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hy₁
    · exact h
  have hordy₂ : orderOf y₂ = 3 := by
    have hdvd : orderOf y₂ ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hy₂3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hy₂
    · exact h
  have hy₁fix₁ : ∀ z ∈ Z₁, y₁ z = z := by
    intro z hz
    have hz' : z ∈ fixV (Subgroup.zpowers y₁) := by rwa [hfix₁]
    rw [mem_fixV] at hz'
    exact hz' y₁ (Subgroup.mem_zpowers y₁)
  have hy₂fix₂ : ∀ z ∈ Z₂, y₂ z = z := by
    intro z hz
    have hz' : z ∈ fixV (Subgroup.zpowers y₂) := by rwa [hfix₂]
    rw [mem_fixV] at hz'
    exact hz' y₂ (Subgroup.mem_zpowers y₂)
  have hy₂Z₁ : ∀ z ∈ Z₁, y₂ z ∈ Z₁ := by
    intro z hz
    have hz' : z ∈ commSub ⊤ (Subgroup.zpowers y₂) := by rwa [hcom₂]
    have h := CFSG.Quasithin.Asc81c.commSub_stable' (Subgroup.mem_zpowers y₂) hz'
    rwa [hcom₂] at h
  have hy₁Z₂ : ∀ z ∈ Z₂, y₁ z ∈ Z₂ := by
    intro z hz
    have hz' : z ∈ commSub ⊤ (Subgroup.zpowers y₁) := by rwa [hcom₁]
    have h := CFSG.Quasithin.Asc81c.commSub_stable' (Subgroup.mem_zpowers y₁) hz'
    rwa [hcom₁] at h
  have hy₂fixZ₁ : ∀ z ∈ Z₁, y₂ z = z → z = 1 := by
    intro z hz hzy
    have hz₂ : z ∈ Z₂ := by
      rw [← hfix₂]
      exact s168e3_cyc_mem_fixV_zpowers hzy
    have hmem : z ∈ Z₁ ⊓ Z₂ := ⟨hz, hz₂⟩
    rwa [hZ, Subgroup.mem_bot] at hmem
  have hy₁fixZ₂ : ∀ z ∈ Z₂, y₁ z = z → z = 1 := by
    intro z hz hzy
    have hz₁ : z ∈ Z₁ := by
      rw [← hfix₁]
      exact s168e3_cyc_mem_fixV_zpowers hzy
    have hmem : z ∈ Z₁ ⊓ Z₂ := ⟨hz₁, hz⟩
    rwa [hZ, Subgroup.mem_bot] at hmem
  have hxZ₁ : ∀ z ∈ Z₁, x z ∈ Z₁ := by
    intro z hz
    have hz' : z ∈ fixV (Subgroup.zpowers y₁) := by rwa [hfix₁]
    have h := s168e3_cyc3_x_stable_fixV (hEc x hxE y₁ hy₁E) z hz'
    rwa [hfix₁] at h
  have hxZ₂ : ∀ z ∈ Z₂, x z ∈ Z₂ := by
    intro z hz
    have hz' : z ∈ fixV (Subgroup.zpowers y₂) := by rwa [hfix₂]
    have h := s168e3_cyc3_x_stable_fixV (hEc x hxE y₂ hy₂E) z hz'
    rwa [hfix₂] at h
  have hZ₁ne : Z₁ ≠ ⊥ := by
    intro h
    have hcard : Nat.card ↥Z₁ = 1 := by rw [h, Subgroup.card_bot]
    omega
  have hZne : Z₁ ≠ Z₂ := by
    intro h
    have hbot : Z₁ ⊓ Z₂ = Z₁ := inf_eq_left.mpr (le_of_eq h)
    rw [hZ] at hbot
    exact hZ₁ne hbot.symm
  have hnp' : ∃ g, g ∈ A ∧
      ¬ ((Z₁.map g.toMonoidHom = Z₁ ∧ Z₂.map g.toMonoidHom = Z₂) ∨
         (Z₁.map g.toMonoidHom = Z₂ ∧ Z₂.map g.toMonoidHom = Z₁)) := by
    by_contra h
    apply hnp
    intro g hgA
    by_contra hP
    exact h ⟨g, hgA, hP⟩
  obtain ⟨g, hgA, hgP⟩ := hnp'
  have hmapne : Z₁.map g.toMonoidHom ≠ Z₂.map g.toMonoidHom := by
    intro h
    exact hZne ((Subgroup.map_injective (f := g.toMonoidHom)
      (fun a b hab => g.injective hab)).eq_iff.mp h)
  have hbranch : (Z₁.map g.toMonoidHom ≠ Z₁ ∧ Z₁.map g.toMonoidHom ≠ Z₂) ∨
      (Z₂.map g.toMonoidHom ≠ Z₁ ∧ Z₂.map g.toMonoidHom ≠ Z₂) := by
    by_cases h11 : Z₁.map g.toMonoidHom = Z₁
    · by_cases h22 : Z₂.map g.toMonoidHom = Z₂
      · exact absurd (Or.inl ⟨h11, h22⟩) hgP
      · by_cases h21 : Z₂.map g.toMonoidHom = Z₁
        · exact absurd (h11.trans h21.symm) hmapne
        · exact Or.inr ⟨h21, h22⟩
    · by_cases h12 : Z₁.map g.toMonoidHom = Z₂
      · by_cases h21 : Z₂.map g.toMonoidHom = Z₁
        · exact absurd (Or.inr ⟨h12, h21⟩) hgP
        · by_cases h22 : Z₂.map g.toMonoidHom = Z₂
          · exact absurd (h12.trans h22.symm) hmapne
          · exact Or.inr ⟨h21, h22⟩
      · exact Or.inl ⟨h11, h12⟩
  have houtside : ∀ (Z' : Subgroup W) (h : MulAut W), h ∈ A → orderOf h = 3 →
      (∀ z ∈ Z', h z = z) → Z' ⊓ Z₁ = ⊥ → Z' ⊓ Z₂ = ⊥ → Nat.card ↥Z' = 4 →
      ∀ w : W, w ≠ 1 → ∃ b ∈ A, orderOf b = 3 ∧ b w = w := by
    intro Z' h hhA hordh hfixh hZ'₁ hZ'₂ hZ'card w hw1
    by_cases hwZ₁ : w ∈ Z₁
    · exact ⟨y₁, hy₁A, hordy₁, hy₁fix₁ w hwZ₁⟩
    by_cases hwZ₂ : w ∈ Z₂
    · exact ⟨y₂, hy₂A, hordy₂, hy₂fix₂ w hwZ₂⟩
    have hwtop : w ∈ Z₁ ⊔ Z₂ := by rw [hZtop]; exact Subgroup.mem_top w
    obtain ⟨a₁, ha₁, a₂, ha₂, ha₁a₂⟩ := Subgroup.mem_sup.mp hwtop
    have ha₁ne : a₁ ≠ 1 := by
      intro h1
      exact hwZ₂ (by rw [← ha₁a₂, h1, one_mul]; exact ha₂)
    have ha₂ne : a₂ ≠ 1 := by
      intro h2
      exact hwZ₁ (by rw [← ha₁a₂, h2, mul_one]; exact ha₁)
    haveI : Nontrivial ↥Z' := (Finite.one_lt_card_iff_nontrivial).mp (by rw [hZ'card]; norm_num)
    obtain ⟨z'₀, hz'₀ne⟩ := exists_ne (1 : ↥Z')
    have hz'Z' : (z'₀ : W) ∈ Z' := z'₀.2
    have hz'ne : (z'₀ : W) ≠ 1 := fun hh => hz'₀ne (Subtype.ext hh)
    have hz'top : (z'₀ : W) ∈ Z₁ ⊔ Z₂ := by rw [hZtop]; exact Subgroup.mem_top _
    obtain ⟨c₁, hc₁, c₂, hc₂, hc₁c₂⟩ := Subgroup.mem_sup.mp hz'top
    have hc₁ne : c₁ ≠ 1 := by
      intro h1
      have hmem : (z'₀ : W) ∈ Z' ⊓ Z₂ :=
        ⟨hz'Z', by rw [← hc₁c₂, h1, one_mul]; exact hc₂⟩
      rw [hZ'₂, Subgroup.mem_bot] at hmem
      exact hz'ne hmem
    have hc₂ne : c₂ ≠ 1 := by
      intro h2
      have hmem : (z'₀ : W) ∈ Z' ⊓ Z₁ :=
        ⟨hz'Z', by rw [← hc₁c₂, h2, mul_one]; exact hc₁⟩
      rw [hZ'₁, Subgroup.mem_bot] at hmem
      exact hz'ne hmem
    obtain ⟨a, ha3, haeq⟩ := s168e3_cyc3_pow_eq_of_reg hZ₁
      (by rw [← hordy₂]; exact pow_orderOf_eq_one y₂) hy₂Z₁ hy₂fixZ₁ hc₁ hc₁ne ha₁ ha₁ne
    obtain ⟨b, hb3, hbeq⟩ := s168e3_cyc3_pow_eq_of_reg hZ₂
      (by rw [← hordy₁]; exact pow_orderOf_eq_one y₁) hy₁Z₂ hy₁fixZ₂ hc₂ hc₂ne ha₂ ha₂ne
    let e : MulAut W := y₂ ^ a * y₁ ^ b
    have heA : e ∈ A := A.mul_mem (A.pow_mem hy₂A a) (A.pow_mem hy₁A b)
    have hpowfix₁ : ∀ z ∈ Z₁, (y₁ ^ b) z = z := s168e3_cyc3_pow_fix hy₁fix₁ b
    have hpowfix₂ : ∀ z ∈ Z₂, (y₂ ^ a) z = z := s168e3_cyc3_pow_fix hy₂fix₂ a
    have hez' : e (z'₀ : W) = w := by
      calc e (z'₀ : W) = (y₂ ^ a) ((y₁ ^ b) (z'₀ : W)) := by
              rw [show e = y₂ ^ a * y₁ ^ b from rfl, MulAut.mul_apply]
        _ = (y₂ ^ a) ((y₁ ^ b) c₁ * (y₁ ^ b) c₂) := by rw [← hc₁c₂, map_mul]
        _ = (y₂ ^ a) (c₁ * a₂) := by rw [hpowfix₁ c₁ hc₁, hbeq]
        _ = (y₂ ^ a) c₁ * (y₂ ^ a) a₂ := map_mul _ _ _
        _ = a₁ * a₂ := by rw [haeq, hpowfix₂ a₂ ha₂]
        _ = w := ha₁a₂
    refine ⟨e * h * e⁻¹, A.mul_mem (A.mul_mem heA hhA) (A.inv_mem heA), ?_, ?_⟩
    · rw [show e * h * e⁻¹ = MulAut.conj e h from (MulAut.conj_apply e h).symm]
      exact (orderOf_injective (MulAut.conj e).toMonoidHom
        (MulAut.conj e).injective h).trans hordh
    · calc (e * h * e⁻¹) w = e (h (e⁻¹ (e (z'₀ : W)))) := by
              rw [← hez']; simp only [MulAut.mul_apply]
        _ = e (h (z'₀ : W)) := by rw [MulAut.inv_apply_self]
        _ = e (z'₀ : W) := by rw [hfixh _ hz'Z']
        _ = w := hez'
  rcases hbranch with ⟨hne₁, hne₂⟩ | ⟨hne₁, hne₂⟩
  · have hZpow : ∀ n : ℤ, ∀ z ∈ Z₁, (x ^ n) z ∈ Z₁ := by
      intro n z hz
      have hz' : z ∈ fixV (Subgroup.zpowers y₁) := by rwa [hfix₁]
      have h := s168e3_cyc_fixV_zpowers_mem (hEc x hxE y₁ hy₁E) n hz'
      rwa [hfix₁] at h
    have hxZ' : ∀ z ∈ Z₁.map g.toMonoidHom, x z ∈ Z₁.map g.toMonoidHom :=
      s168e3_cyc_map_x_stable hgA hLn hLx hZpow
    obtain ⟨hZ'₁, hZ'₂, hZ'card, hhA, hordh, hfixh⟩ :=
      s168e3_cyc3_shift (Z := Z₁) (Z₁ := Z₁) (Z₂ := Z₂) (g := g) (y := y₁)
        hgA hy₁A hordy₁ hxZ' hy₁fix₁ hZ₁ hZ₁ hZ₂ hxZ₁ hxZ₂ hfpf hne₁ hne₂
    exact houtside (Z₁.map g.toMonoidHom) (g * y₁ * g⁻¹) hhA hordh hfixh hZ'₁ hZ'₂ hZ'card
  · have hZpow : ∀ n : ℤ, ∀ z ∈ Z₂, (x ^ n) z ∈ Z₂ := by
      intro n z hz
      have hz' : z ∈ fixV (Subgroup.zpowers y₂) := by rwa [hfix₂]
      have h := s168e3_cyc_fixV_zpowers_mem (hEc x hxE y₂ hy₂E) n hz'
      rwa [hfix₂] at h
    have hxZ' : ∀ z ∈ Z₂.map g.toMonoidHom, x z ∈ Z₂.map g.toMonoidHom :=
      s168e3_cyc_map_x_stable hgA hLn hLx hZpow
    obtain ⟨hZ'₁, hZ'₂, hZ'card, hhA, hordh, hfixh⟩ :=
      s168e3_cyc3_shift (Z := Z₂) (Z₁ := Z₁) (Z₂ := Z₂) (g := g) (y := y₂)
        hgA hy₂A hordy₂ hxZ' hy₂fix₂ hZ₂ hZ₁ hZ₂ hxZ₁ hxZ₂ hfpf hne₁ hne₂
    exact houtside (Z₂.map g.toMonoidHom) (g * y₂ * g⁻¹) hhA hordh hfixh hZ'₁ hZ'₂ hZ'card

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
