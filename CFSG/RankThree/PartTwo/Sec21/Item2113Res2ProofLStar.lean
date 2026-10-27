module

public import CFSG.RankThree.PartTwo.Sec21.Item2113ProofLinear
public import CFSG.RankThree.PartTwo.Sec21.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2113Res2Proof

open Subgroup
open CFSG.RankThree.PartTwo.Sec21.Item2113Proof (card_subgroup_cases eq_zpowers_of_card_three
  card_zpowers_three mem_zpowers_three sq_eq_inv zpowers_inf_eq_bot fixSub mem_fixSub
  fixSub_eq_closure eq_one_of_inv_eq sup_zpowers_eq_top)

section Delta

variable {A : Type*} [CommGroup A]

@[expose] def deltaHom (σ : MulAut A) : A →* A where
  toFun x := x⁻¹ * σ x
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, mul_inv]
    ac_rfl

theorem deltaHom_apply (σ : MulAut A) (x : A) : deltaHom σ x = x⁻¹ * σ x :=
  rfl

theorem apply_eq_mul_deltaHom (σ : MulAut A) (x : A) : σ x = x * deltaHom σ x := by
  rw [deltaHom_apply, mul_inv_cancel_left]

theorem deltaHom_eq_one_iff {σ : MulAut A} {x : A} : deltaHom σ x = 1 ↔ σ x = x := by
  rw [deltaHom_apply, inv_mul_eq_one, eq_comm]

theorem commOf_eq_range (σ : MulAut A) : commOf σ = (deltaHom σ).range := by
  have h : (Set.range fun a : A => a⁻¹ * σ a) = ((deltaHom σ).range : Set A) := by
    rw [MonoidHom.coe_range]
    rfl
  rw [commOf, h, Subgroup.closure_eq]

theorem deltaHom_comm {σ z : MulAut A} (h : z * σ = σ * z) (x : A) :
    deltaHom σ (z x) = z (deltaHom σ x) := by
  have h' : σ (z x) = z (σ x) := by
    have := congrArg (fun φ : MulAut A => φ x) h
    simpa only [MulAut.mul_apply] using this.symm
  rw [deltaHom_apply, deltaHom_apply, h', map_mul, map_inv]

theorem deltaHom_cube (h3 : ∀ x : A, x ^ 3 = 1) {σ : MulAut A} (hσ : σ ^ 3 = 1) (x : A) :
    deltaHom σ (deltaHom σ (deltaHom σ x)) = 1 := by
  set u := deltaHom σ x with hu
  set v := deltaHom σ u with hv
  set w := deltaHom σ v with hw
  have e1 : σ x = x * u := apply_eq_mul_deltaHom σ x
  have e2 : σ u = u * v := apply_eq_mul_deltaHom σ u
  have e3 : σ v = v * w := apply_eq_mul_deltaHom σ v
  have h : (σ ^ 3) x = x * w := by
    rw [pow_three, MulAut.mul_apply, MulAut.mul_apply]
    simp only [map_mul, e1, e2, e3]
    have hu3 : u * u * u = 1 := by rw [← h3 u, pow_three']
    have hv3 : v * v * v = 1 := by rw [← h3 v, pow_three']
    calc x * u * (u * v) * (u * v * (v * w)) = x * w * (u * u * u) * (v * v * v) := by ac_rfl
      _ = x * w := by rw [hu3, hv3, mul_one, mul_one]
  rw [hσ, MulAut.one_apply] at h
  exact (mul_eq_left.mp h.symm)

theorem deltaHom_eq_one_of_mem (h3 : ∀ x : A, x ^ 3 = 1) {σ : MulAut A} (hσ : σ ^ 3 = 1)
    {d : A} (hd1 : d ≠ 1) (hm : deltaHom σ d ∈ zpowers d) : deltaHom σ d = 1 := by
  have hc := deltaHom_cube h3 hσ d
  rcases (mem_zpowers_three h3).mp hm with h | h | h
  · exact h
  · rw [h, h, h] at hc
    exact absurd hc hd1
  · exfalso
    have h2 : deltaHom σ (d ^ 2) = d := by
      rw [map_pow, h, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, h3, one_mul, pow_one]
    rw [h, h2, h] at hc
    have : d = 1 := by
      have h' : (d ^ 2) ^ 2 = d := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, h3, one_mul, pow_one]
      rw [← h', hc, one_pow]
    exact hd1 this

end Delta

section Transvection

variable {A : Type*} [CommGroup A] [Finite A]

theorem not_mem_zpowers_of_mem (h3 : ∀ x : A, x ^ 3 = 1) {B : Subgroup A} {c d : A}
    (hcB : c ∉ B) (hdB : d ∈ B) (hd1 : d ≠ 1) : d ∉ zpowers c := by
  intro h
  have hc1 : c ≠ 1 := fun h1 => hcB (h1 ▸ one_mem B)
  have heq := eq_zpowers_of_card_three h3 (card_zpowers_three h3 hc1) h hd1
  exact hcB ((zpowers_le.mpr hdB) (heq ▸ mem_zpowers c))

theorem card_le_nine (h27 : Nat.card A = 27) {B : Subgroup A} {c : A} (hcB : c ∉ B) :
    Nat.card B ≤ 9 := by
  have hne : Nat.card B ≠ 27 := by
    intro h
    exact hcB ((eq_top_of_card_eq B (by rw [h, h27])) ▸ mem_top c)
  rcases card_subgroup_cases h27 B with h | h | h | h <;> omega

omit [Finite A] in
theorem eq_one_of_forall_fix {σ : MulAut A} (h : ∀ x, σ x = x) : σ = 1 := by
  ext x
  exact h x

theorem exists_transvection_of_cube (h3 : ∀ x : A, x ^ 3 = 1) (h27 : Nat.card A = 27)
    {B : Subgroup A} {c : A} (hc1 : c ≠ 1) (hcB : c ∉ B) {σ : MulAut A} (hσc : σ c = c)
    (hσB : ∀ x, x⁻¹ * σ x ∈ B) (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) :
    ∃ d : A, d ≠ 1 ∧ d ∈ B ∧ σ d = d ∧ commOf σ = zpowers d := by
  set δ := deltaHom σ with hδ
  have hR : δ.range ≤ B := by
    rintro _ ⟨x, rfl⟩
    exact hσB x
  have hcK : c ∈ δ.ker := MonoidHom.mem_ker.mpr (deltaHom_eq_one_iff.mpr hσc)
  have hcard : Nat.card δ.ker * Nat.card δ.range = 27 := h27 ▸ Subgroup.card_ker_mul_card_range δ
  have hK3 : 3 ≤ Nat.card δ.ker := by
    rw [← card_zpowers_three h3 hc1]
    exact card_le_of_le (zpowers_le.mpr hcK)
  have hB9 := card_le_nine h27 hcB
  have hR1 : Nat.card δ.range ≠ 1 := by
    intro h
    apply hσ1
    apply eq_one_of_forall_fix
    intro x
    have hx : δ x ∈ δ.range := ⟨x, rfl⟩
    rw [(card_eq_one.mp h), mem_bot] at hx
    exact deltaHom_eq_one_iff.mp hx
  have hR9 : Nat.card δ.range ≠ 9 := by
    intro h9
    rw [h9] at hcard
    have hK : Nat.card δ.ker = 3 := by omega
    have hKc : δ.ker = zpowers c := eq_zpowers_of_card_three h3 hK hcK hc1
    have hRB : δ.range = B := eq_of_le_of_card_ge hR (by omega)
    have hBK : B ≤ δ.ker := by
      intro b hb
      rw [← hRB] at hb
      obtain ⟨x, rfl⟩ := hb
      have h1 : δ (δ x) ∈ δ.ker := MonoidHom.mem_ker.mpr (deltaHom_cube h3 hσ3 x)
      rw [hKc] at h1
      have h2 : δ (δ x) ∈ B := hR ⟨_, rfl⟩
      have hbot := zpowers_inf_eq_bot h3 hcB
      have hmem : δ (δ x) ∈ zpowers c ⊓ B := ⟨h1, h2⟩
      rw [hbot, mem_bot] at hmem
      exact MonoidHom.mem_ker.mpr hmem
    have := card_le_of_le hBK
    rw [← hRB] at this
    omega
  have hR3 : Nat.card δ.range = 3 := by
    rcases card_subgroup_cases h27 δ.range with h | h | h | h
    · exact absurd h hR1
    · exact h
    · exact absurd h hR9
    · rw [h] at hcard
      omega
  have hne : δ.range ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hR3
    omega
  obtain ⟨d, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp hne)
  have hRd : δ.range = zpowers (d : A) :=
    eq_zpowers_of_card_three h3 hR3 d.2 (fun h => hd1 (Subtype.ext h))
  have hd1' : (d : A) ≠ 1 := fun h => hd1 (Subtype.ext h)
  have hδd : δ d = 1 := deltaHom_eq_one_of_mem h3 hσ3 hd1' (hRd ▸ ⟨(d : A), rfl⟩)
  exact ⟨d, hd1', hR d.2, deltaHom_eq_one_iff.mp hδd, (commOf_eq_range σ).trans hRd⟩

omit [Finite A] in
theorem isTransvectionOn_of_eq_zpowers (h3 : ∀ x : A, x ^ 3 = 1) {σ : MulAut A} {d : A}
    (hd1 : d ≠ 1) (hσd : σ d = d) (h : commOf σ = zpowers d) : IsTransvectionOn σ := by
  refine ⟨by rw [h, card_zpowers_three h3 hd1], ?_⟩
  rw [h, zpowers_le]
  exact (mem_fixedSubgroupOf σ d).mpr hσd

theorem card_eq_nine_and_inv_of_comm (h3 : ∀ x : A, x ^ 3 = 1) (h27 : Nat.card A = 27)
    {B : Subgroup A} {c : A} (hc1 : c ≠ 1) (hcB : c ∉ B) {σ : MulAut A} (hσc : σ c = c)
    (hσ1 : σ ≠ 1) {d : A} (hd1 : d ≠ 1) (hdB : d ∈ B) (hσd : σ d = d)
    (hcomm : commOf σ = zpowers d) {z : MulAut A} (hzc : z c = c)
    (hzB : ∀ x, x⁻¹ * z x ∈ B) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) (hzσ : z * σ = σ * z) :
    Nat.card B = 9 ∧ ∀ b ∈ B, z b = b⁻¹ := by
  set δ := deltaHom σ with hδ
  have hδR : ∀ x, δ x ∈ zpowers d := fun x => by
    rw [← hcomm, commOf_eq_range]
    exact ⟨x, rfl⟩
  have hzz : ∀ x, z (z x) = x := fun x => by
    have := congrArg (fun φ : MulAut A => φ x) hz2
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using this
  have hdc : d ∉ zpowers c := not_mem_zpowers_of_mem h3 hcB hdB hd1
  have hσpd : ∀ y ∈ zpowers d, σ y = y := by
    intro y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    rw [map_zpow, hσd]
  have hzd_mem : z d ∈ zpowers d := by
    have hdR : d ∈ δ.range := by
      rw [← commOf_eq_range, hcomm]
      exact mem_zpowers d
    obtain ⟨x, hx⟩ := hdR
    have : z d = δ (z x) := by rw [← hx, deltaHom_comm hzσ]
    rw [this]
    exact hδR (z x)
  have hzBB : ∀ b ∈ B, z b ∈ B := fun b hb => by
    have h := B.mul_mem hb (hzB b)
    rwa [mul_inv_cancel_left] at h
  have hzd_ne : z d ≠ d := by
    intro hzd
    obtain ⟨hF, -⟩ := fixSub_eq_closure h3 h27 hc1 hdc hzc hzd hz1
    have hσF : ∀ f ∈ fixSub z, σ f = f := by
      intro f hf
      rw [hF] at hf
      have hle : closure ({c, d} : Set A) ≤ fixSub σ := by
        rw [closure_le]
        rintro x (rfl | rfl)
        · exact hσc
        · exact hσd
      exact hle hf
    apply hσ1
    apply eq_one_of_forall_fix
    intro a
    set f := (a * z a) ^ 2 with hf
    set i := (a * (z a)⁻¹) ^ 2 with hi
    have hfi : f * i = a := by
      rw [hf, hi, ← mul_pow]
      have : a * z a * (a * (z a)⁻¹) = a * a := by
        rw [mul_mul_mul_comm, mul_inv_cancel, mul_one]
      rw [this, ← pow_two, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, h3, one_mul,
        pow_one]
    have hzf : z f = f := by
      rw [hf, map_pow, map_mul, hzz, mul_comm]
    have hzi : z i = i⁻¹ := by
      rw [hi, map_pow, map_mul, map_inv, hzz, ← inv_pow, mul_inv, inv_inv, mul_comm]
    have hσi : σ i = i := by
      have hzδ : z (δ i) = (δ i)⁻¹ := by
        rw [← deltaHom_comm hzσ, hzi, map_inv]
      have hfixδ : z (δ i) = δ i := by
        obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hδR i)
        rw [← hk, map_zpow, hzd]
      have h1 : δ i = 1 := eq_one_of_inv_eq h3 (hzδ.symm.trans hfixδ)
      exact deltaHom_eq_one_iff.mp h1
    rw [← hfi, map_mul, hσF f hzf, hσi]
  have hzd : z d = d⁻¹ := by
    rcases (mem_zpowers_three h3).mp hzd_mem with h | h | h
    · exfalso
      apply hd1
      have := congrArg z h
      rwa [hzz, map_one] at this
    · exact absurd h hzd_ne
    · rw [h, sq_eq_inv h3]
  have hdF : d ∉ fixSub z := by
    intro h
    exact hzd_ne h
  have hFB : ∀ g ∈ B, z g = g → g = 1 := by
    intro g hgB hzg
    by_contra hg1
    have hgc : g ∉ zpowers c := not_mem_zpowers_of_mem h3 hcB hgB hg1
    obtain ⟨hF, hF9⟩ := fixSub_eq_closure h3 h27 hc1 hgc hzc hzg hz1
    have hσg : σ g = g := by
      have hzδ : z (δ g) = δ g := by rw [← deltaHom_comm hzσ, hzg]
      have hmem : δ g ∈ zpowers d ⊓ fixSub z := ⟨hδR g, hzδ⟩
      have hdF' : d ∉ closure ({c, g} : Set A) := hF ▸ hdF
      rw [hF, zpowers_inf_eq_bot h3 hdF', mem_bot] at hmem
      exact deltaHom_eq_one_iff.mp hmem
    apply hσ1
    apply eq_one_of_forall_fix
    intro x
    have hdF' : d ∉ closure ({c, g} : Set A) := hF ▸ hdF
    have htop := sup_zpowers_eq_top h27 hF9 hdF'
    have hle : closure ({c, g} : Set A) ⊔ zpowers d ≤ fixSub σ := by
      refine sup_le ?_ ?_
      · rw [closure_le]
        rintro y (rfl | rfl)
        · exact hσc
        · exact hσg
      · intro y hy
        exact hσpd y hy
    exact hle (htop ▸ mem_top x)
  have hinv : ∀ b ∈ B, z b = b⁻¹ := by
    intro b hb
    have h1 : b * z b ∈ B := B.mul_mem hb (hzBB b hb)
    have h2 : z (b * z b) = b * z b := by rw [map_mul, hzz, mul_comm]
    have h3' := hFB _ h1 h2
    exact eq_inv_of_mul_eq_one_right h3'
  refine ⟨?_, hinv⟩
  have hB9 := card_le_nine h27 hcB
  have hBd : 3 ≤ Nat.card B := by
    rw [← card_zpowers_three h3 hd1]
    exact card_le_of_le (zpowers_le.mpr hdB)
  have hne3 : Nat.card B ≠ 3 := by
    intro h
    have hBeq : B = zpowers d := eq_zpowers_of_card_three h3 h hdB hd1
    obtain ⟨e, he⟩ : ∃ e, σ e ≠ e := by
      by_contra hcon
      exact hσ1 (eq_one_of_forall_fix fun x => not_not.mp fun h => hcon ⟨x, h⟩)
    have hy : e⁻¹ * z e ∈ zpowers d := hBeq ▸ hzB e
    have hze : z e = e * (e⁻¹ * z e) := by rw [mul_inv_cancel_left]
    have hδze : δ (z e) = δ e := by
      rw [hze, map_mul, deltaHom_eq_one_iff.mpr (hσpd _ hy), mul_one]
    have hδe : z (δ e) = (δ e)⁻¹ := hinv _ (hBeq ▸ hδR e)
    rw [← deltaHom_comm hzσ, hδze] at hδe
    have h1 : δ e = 1 := eq_one_of_inv_eq h3 hδe.symm
    exact he (deltaHom_eq_one_iff.mp h1)
  rcases card_subgroup_cases h27 B with h | h | h | h <;> omega

end Transvection

section Group

variable {G : Type} [Group G]

theorem coe_inv_mul_apply_mem {A L : Subgroup G} (hAL : A ≤ normalizer (L : Set G))
    {σ : MulAut A} (hσ : σ ∈ starOf A L) (a : A) : ((a⁻¹ * σ a : A) : G) ∈ L := by
  obtain ⟨w, hwL, rfl⟩ := hσ
  have hwL' : (w : G) ∈ L := Subgroup.mem_subgroupOf.mp hwL
  have haN : ((a : G))⁻¹ ∈ normalizer (L : Set G) := hAL (A.inv_mem a.2)
  have h1 : (a : G)⁻¹ * w * ((a : G)⁻¹)⁻¹ ∈ L := (mem_normalizer_iff.mp haN w).mp hwL'
  rw [inv_inv] at h1
  have heq : ((a⁻¹ * A.normalizerMonoidHom w a : A) : G) =
      ((a : G)⁻¹ * w * a) * (w : G)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inv]
    group
  rw [heq]
  exact L.mul_mem h1 (L.inv_mem hwL')

theorem apply_eq_of_mem_starOf {A L : Subgroup G} {c : G} (hcA : c ∈ A)
    (hLc : L ≤ centralizer ({c} : Set G)) {σ : MulAut A} (hσ : σ ∈ starOf A L) :
    σ ⟨c, hcA⟩ = ⟨c, hcA⟩ := by
  obtain ⟨w, hwL, rfl⟩ := hσ
  apply Subtype.ext
  have hwc : (w : G) * c = c * w :=
    mem_centralizer_singleton_iff.mp (hLc (Subgroup.mem_subgroupOf.mp hwL))
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hwc, mul_inv_cancel_right]

theorem exists_three_element [Finite G] {A L : Subgroup G} {σ : MulAut A} (hσ : σ ∈ starOf A L)
    (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) :
    ∃ u : normalizer (A : Set G), (u : G) ∈ L ∧ (∃ k : ℕ, (u : G) ^ (3 ^ k) = 1) ∧
      A.normalizerMonoidHom u ∈ starOf A L ∧ (A.normalizerMonoidHom u) ^ 3 = 1 ∧
      A.normalizerMonoidHom u ≠ 1 := by
  obtain ⟨w, hwL, rfl⟩ := hσ
  have hwL' : (w : G) ∈ L := Subgroup.mem_subgroupOf.mp hwL
  obtain ⟨k, m, hm3, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos w).ne' 3
    (by norm_num)
  refine ⟨w ^ m, ?_, ⟨k, ?_⟩, ⟨w ^ m, ?_, rfl⟩, ?_, ?_⟩
  · rw [Subgroup.coe_pow]
    exact pow_mem hwL' m
  · rw [Subgroup.coe_pow, ← pow_mul, mul_comm, ← hord]
    exact congrArg Subtype.val (pow_orderOf_eq_one w)
  · exact pow_mem (show w ∈ L.subgroupOf (normalizer (A : Set G)) from hwL) m
  · rw [map_pow, ← pow_mul, mul_comm, pow_mul, hσ3, one_pow]
  · rw [map_pow]
    intro h
    have hσo : orderOf (A.normalizerMonoidHom w) = 3 := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact orderOf_eq_prime hσ3 hσ1
    exact hm3 (hσo ▸ orderOf_dvd_of_pow_eq_one h)

theorem exists_cube_of_mulEquiv {A : Type*} [Group A] {S : Subgroup (MulAut A)} {H : Type*}
    [Group H] (e : S ≃* H) {s : H} (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) :
    ∃ σ ∈ S, σ ^ 3 = 1 ∧ σ ≠ 1 := by
  refine ⟨(e.symm s : MulAut A), (e.symm s).2, ?_, ?_⟩
  · rw [← Subgroup.coe_pow, ← map_pow, hs3, map_one, Subgroup.coe_one]
  · intro h
    apply hs1
    have h' : e.symm s = 1 := Subtype.ext h
    rw [← map_one e.symm] at h'
    exact e.symm.injective h'

theorem exists_central_of_mulEquiv {A : Type*} [Group A] {S : Subgroup (MulAut A)} {H : Type*}
    [Group H] (e : S ≃* H) {z : H} (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1)
    (hzc : ∀ h : H, z * h = h * z) :
    ∃ ζ ∈ S, ζ ^ 2 = 1 ∧ ζ ≠ 1 ∧ ∀ τ ∈ S, ζ * τ = τ * ζ := by
  refine ⟨(e.symm z : MulAut A), (e.symm z).2, ?_, ?_, ?_⟩
  · rw [← Subgroup.coe_pow, ← map_pow, hz2, map_one, Subgroup.coe_one]
  · intro h
    apply hz1
    have h' : e.symm z = 1 := Subtype.ext h
    rw [← map_one e.symm] at h'
    exact e.symm.injective h'
  · intro τ hτ
    have h1 : e.symm z * ⟨τ, hτ⟩ = ⟨τ, hτ⟩ * e.symm z := by
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hzc]
    exact congrArg Subtype.val h1

theorem dihedral_six_central :
    ∀ h : DihedralGroup 6, DihedralGroup.r 3 * h = h * DihedralGroup.r 3 := by
  decide

theorem gl_two_three_central : ∀ h : GL (Fin 2) (ZMod 3), (-1) * h = h * (-1) := fun h => by
  simp

theorem dihedral_six_data : (DihedralGroup.r 2 : DihedralGroup 6) ^ 3 = 1 ∧
    (DihedralGroup.r 2 : DihedralGroup 6) ≠ 1 ∧ (DihedralGroup.r 3 : DihedralGroup 6) ^ 2 = 1 ∧
    (DihedralGroup.r 3 : DihedralGroup 6) ≠ 1 ∧
    DihedralGroup.r 3 * DihedralGroup.r 2 =
      (DihedralGroup.r 2 : DihedralGroup 6) * DihedralGroup.r 3 := by
  decide

@[expose] def glTransvection : GL (Fin 2) (ZMod 3) :=
  ⟨!![1, 1; 0, 1], !![1, 2; 0, 1], by decide, by decide⟩

theorem gl_two_three_data : glTransvection ^ 3 = 1 ∧ glTransvection ≠ 1 ∧
    (-1 : GL (Fin 2) (ZMod 3)) ^ 2 = 1 ∧ (-1 : GL (Fin 2) (ZMod 3)) ≠ 1 ∧
    (-1 : GL (Fin 2) (ZMod 3)) * glTransvection = glTransvection * -1 := by
  refine ⟨?_, ?_, by simp, ?_, by simp⟩
  · apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_one, glTransvection]
    decide
  · intro h
    have := congrArg (fun u : GL (Fin 2) (ZMod 3) => (u : Matrix (Fin 2) (Fin 2) (ZMod 3))) h
    simp only [glTransvection, Units.val_one] at this
    revert this
    decide
  · intro h
    have := congrArg (fun u : GL (Fin 2) (ZMod 3) => (u : Matrix (Fin 2) (Fin 2) (ZMod 3))) h
    simp only [Units.val_neg, Units.val_one] at this
    revert this
    decide

theorem perm_three_data : (finRotate 3) ^ 3 = 1 ∧ finRotate 3 ≠ 1 := by
  decide

end Group

end CFSG.RankThree.PartTwo.Sec21.Item2113Res2Proof
