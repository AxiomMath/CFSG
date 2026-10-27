module

public import CFSG.RankThree.PartOne.Q1327.Comp

public section

namespace CFSG.RankThree.PartOne.Q1327

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K1320
  CFSG.RankThree.PartOne.K1327
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] {p : ℕ} {E : Subgroup G}

theorem mul_pow_eq_one_of_same_moved (hd : RefFacts.ElemData p E) {t t' : MulAut E}
    (ht : IsAutReflection p E t) (ht' : IsAutReflection p E t')
    (hl : autMoved E t = autMoved E t') : (t * t') ^ p = 1 := by
  set φ := t * t' with hφ
  have hinv : ∀ y ∈ autMoved E t, t y = y⁻¹ ∧ t' y = y⁻¹ := fun y hy =>
    ⟨RefFacts.t_apply_inv_of_mem_autMoved hd ht hy,
      RefFacts.t_apply_inv_of_mem_autMoved hd ht' (hl ▸ hy)⟩
  have hφfix : ∀ y ∈ autMoved E t, φ y = y := by
    intro y hy
    obtain ⟨h1, h2⟩ := hinv y hy
    show t (t' y) = y
    rw [h2, map_inv, h1, inv_inv]
  have hν : ∀ e : E, φ e * e⁻¹ ∈ autMoved E t := by
    intro e
    have hlam : t' e * e⁻¹ ∈ autMoved E t := hl ▸ (mem_autMoved_iff' hd.comm t').2 ⟨e, rfl⟩
    have hmu : t e * e⁻¹ ∈ autMoved E t := (mem_autMoved_iff' hd.comm t).2 ⟨e, rfl⟩
    have h1 : t (t' e * e⁻¹) = (t' e * e⁻¹)⁻¹ := (hinv _ hlam).1
    have h2 : φ e * e⁻¹ = (t' e * e⁻¹)⁻¹ * (t e * e⁻¹) := by
      show t (t' e) * e⁻¹ = _
      have h3 : t (t' e) = t ((t' e * e⁻¹) * e) := by group
      rw [h3, map_mul, h1]
      group
    rw [h2]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hlam) hmu
  have hind : ∀ k : ℕ, ∀ e : E, (φ ^ k) e = e * (φ e * e⁻¹) ^ k := by
    intro k
    induction k with
    | zero => intro e; simp
    | succ k ih =>
      intro e
      have ih' := ih e
      obtain ⟨ν, hνdef⟩ : ∃ ν, ν = φ e * e⁻¹ := ⟨_, rfl⟩
      rw [← hνdef] at ih' ⊢
      have hφe : φ e = e * ν := by
        calc φ e = ν * e := by rw [hνdef]; group
          _ = e * ν := hd.comm ν e
      have hfixν : φ ν = ν := by rw [hνdef]; exact hφfix _ (hν e)
      rw [pow_succ', MulAut.mul_apply, ih', map_mul, map_pow, hfixν, hφe, mul_assoc, ← pow_succ']
  refine MulEquiv.ext fun e => ?_
  rw [hind p e, hd.pow, mul_one]
  rfl

theorem autMovedInG_le_of_move [Finite G] (hd : RefFacts.ElemData p E) {t : MulAut E}
    (ht : IsAutReflection p E t) {k : G} (hk : k ∈ Subgroup.normalizer (E : Set G))
    (hkt : E.normalizerMonoidHom ⟨k, hk⟩ = t) {B : Subgroup G} (hBE : B ≤ E)
    (hinv : ∀ b ∈ B, k * b * k⁻¹ ∈ B) {b : G} (hbB : b ∈ B) (hb : b ∉ autFixedInG E t) :
    autMovedInG E t ≤ B := by
  set B' : Subgroup ↥E := B.subgroupOf E with hB'
  have hb' : (⟨b, hBE hbB⟩ : ↥E) ∈ B' := Subgroup.mem_subgroupOf.mpr hbB
  have htb : ((t ⟨b, hBE hbB⟩ : ↥E) : G) = k * b * k⁻¹ := by
    rw [← hkt, Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hmem : t ⟨b, hBE hbB⟩ ∈ B' := Subgroup.mem_subgroupOf.mpr (by rw [htb]; exact hinv b hbB)
  have hne : t ⟨b, hBE hbB⟩ ≠ ⟨b, hBE hbB⟩ := fun h1 => hb ⟨⟨b, hBE hbB⟩, h1, rfl⟩
  have hle := RefFacts.autMoved_le_of_move hd ht hb' hmem hne
  refine (Subgroup.map_mono hle).trans ?_
  rintro _ ⟨y, hy, rfl⟩
  exact Subgroup.mem_subgroupOf.mp hy

theorem propagate [Finite G] (hd : RefFacts.ElemData p E) (hX : Nat.card (reflectionGroup p E) = 48)
    (hp5 : 5 ≤ p) {t x : MulAut E} (ht : IsAutReflection p E t) (hx : IsAutReflection p E x)
    (htX : t ∈ reflectionGroup p E) (hxX : x ∈ reflectionGroup p E) {kx : G}
    (hkx : kx ∈ Subgroup.normalizer (E : Set G)) (hkxx : E.normalizerMonoidHom ⟨kx, hkx⟩ = x)
    {B : Subgroup G} (hBE : B ≤ E) (hinv : ∀ b ∈ B, kx * b * kx⁻¹ ∈ B)
    (hl : autMovedInG E t ≤ B) (hnc : x * t ≠ t * x) : autMovedInG E x ≤ B := by
  by_contra hxB
  have hfixB : ∀ b ∈ B, b ∈ autFixedInG E x := by
    intro b hb
    by_contra hnb
    exact hxB (autMovedInG_le_of_move hd hx hkx hkxx hBE hinv hb hnb)
  have hfixl : ∀ y ∈ autMoved E t, x y = y := by
    intro y hy
    have : (y : G) ∈ autFixedInG E x := hfixB _ (hl ⟨y, hy, rfl⟩)
    obtain ⟨m, hm, hmy⟩ := this
    have : m = y := Subtype.ext hmy
    rw [← this]
    exact hm
  have hmoved : autMoved E (x * t * x⁻¹) = autMoved E t := by
    rw [Equivariance.autMoved_conj]
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      have : x y = y := hfixl y hy
      show x y ∈ autMoved E t
      rw [this]
      exact hy
    · intro hz
      exact ⟨z, hz, hfixl z hz⟩
  have hrefl' : IsAutReflection p E (x * t * x⁻¹) := isAutReflection_conj x t ht
  have hpow := mul_pow_eq_one_of_same_moved hd ht hrefl' hmoved.symm
  have hmemX : t * (x * t * x⁻¹) ∈ reflectionGroup p E :=
    mul_mem htX (mul_mem (mul_mem hxX htX) (inv_mem hxX))
  have hord : orderOf (t * (x * t * x⁻¹)) ∣ p := orderOf_dvd_of_pow_eq_one hpow
  have hord48 : orderOf (t * (x * t * x⁻¹)) ∣ 48 := by
    have := Subgroup.orderOf_dvd_natCard (reflectionGroup p E) hmemX
    rwa [hX] at this
  have hp : p.Prime := hd.prime
  have hcop : Nat.Coprime p 48 := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hdvd => ?_
    have h48 : (48 : ℕ) = 2 ^ 4 * 3 := by norm_num
    rw [h48] at hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h2 | h3
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
      omega
    · have := Nat.le_of_dvd (by norm_num) h3
      omega
  have h1 : orderOf (t * (x * t * x⁻¹)) = 1 :=
    Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd hord hord48)
  have htt : t * t = 1 := RefFacts.mul_self_eq_one ht
  have hxx : x * x = 1 := RefFacts.mul_self_eq_one hx
  have h2 : t * (x * t * x⁻¹) = 1 := orderOf_eq_one_iff.mp h1
  apply hnc
  have h3 : x * t * x⁻¹ = t := by
    have := eq_inv_of_mul_eq_one_right h2
    rw [this]
    exact inv_eq_of_mul_eq_one_right htt
  calc x * t = (x * t * x⁻¹) * x := by group
    _ = t * x := by rw [h3]

theorem card_reflectionGroup_eq
    (eX : reflectionGroup p E ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) :
    Nat.card (reflectionGroup p E) = 48 := by
  rw [Nat.card_congr eX.toEquiv, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_perm]
  simp [Fintype.card_multiplicative, ZMod.card, Nat.factorial]

section Main

variable [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {f r : ℕ} {R : Subgroup G}
  {s s' zs : MulAut E}

theorem Jc_irreducible (hGA : CFSG.Open.GriessAllModelsStatement)
    (H : Hyp G p A c L E f r R s s' zs) {Jc : Subgroup G} (hJ : JcData p E c R s Jc) :
    ∀ B : Subgroup G, B ≤ E → torusInvariant E Jc B → B = ⊥ ∨ B = E := by
  intro B hBE hBinv
  by_cases hB1 : B = ⊥
  · exact Or.inl hB1
  right
  have h := H.h12
  have hp := h.prime
  have hp5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have hcard : Nat.card E = p ^ 3 := by rw [H.hEA]; exact h.A_card
  have hcE : c ∈ E := h.A_le_E h.c_mem
  have hd := RefFacts.ElemData.of_isElementaryAbelian hp hp2 h.E_elem
  obtain ⟨eX⟩ := H.hweyl
  obtain ⟨Bd⟩ := exists_bridge h H.hF13 hcard eX
  have hX := card_reflectionGroup_eq eX
  obtain ⟨a, a', b, g₀, ha, ha', hb, haL, ha'L, hbL, hss, hcomm, hne, hab4, ⟨h₁, hh₁X, hh₁⟩,
    hucen, hfixu, hfixc, hg₀X, hg₀, hza, hzb, hzab, hzba⟩ := refData hGA H
  have haS : a = s ∨ a = s' := by
    rcases hss with ⟨h1, -⟩ | ⟨-, h1⟩
    · exact Or.inl h1.symm
    · exact Or.inr h1.symm
  have ha'cls : a' ∈ clsOf p E a := ⟨h₁, hh₁X, hh₁⟩
  have hscls : s ∈ clsOf p E a := by
    rcases hss with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h1]; exact mem_clsOf_self p E a
    · rw [h1]; exact ha'cls
  have hacls : a ∈ clsOf p E s := by
    rcases hss with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [← h1]; exact mem_clsOf_self p E s
    · refine ⟨h₁⁻¹, Subgroup.inv_mem _ hh₁X, ?_⟩
      rw [h1, ← hh₁]
      group
  have hcls : ∀ t ∈ clsOf p E s, t ∈ clsOf p E a := fun t ht => clsOf_trans hscls ht
  have hcls' : ∀ t ∈ clsOf p E a, t ∈ clsOf p E s := fun t ht => clsOf_trans hacls ht
  have hlift : ∀ t ∈ clsOf p E a, ∃ (k : G) (hk : k ∈ Subgroup.normalizer (E : Set G)),
      k ∈ Jc ∧ E.normalizerMonoidHom ⟨k, hk⟩ = t := by
    intro t ht
    obtain ⟨-, hKt, -, -⟩ := class_facts H haS ht
    obtain ⟨-, -, -, -, k, hk, hkK, hkt⟩ := hKt
    exact ⟨k, hk, hJ.K_le t (hcls' t ht) hkK, hkt⟩
  have hinvt : ∀ t ∈ clsOf p E a, ∀ (k : G) (hk : k ∈ Subgroup.normalizer (E : Set G)),
      k ∈ Jc → ∀ b ∈ B, k * b * k⁻¹ ∈ B := by
    intro t ht k hk hkJ b hb
    exact hBinv k (Subgroup.mem_inf.mpr ⟨hkJ, hk⟩) b hb
  have hrefl : ∀ t ∈ clsOf p E a, IsAutReflection p E t ∧ t ∈ reflectionGroup p E := by
    intro t ht
    obtain ⟨hts, -, -, -⟩ := class_facts H haS ht
    exact ⟨hts.1, Subgroup.subset_closure hts⟩
  obtain ⟨b₀, hb₀B, hb₀1⟩ : ∃ b₀ ∈ B, b₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hB1 (eq_bot_iff.mpr fun x hx => (Subgroup.mem_bot).mpr (hcon x hx))
  obtain ⟨t₁, ht₁, hmov⟩ : ∃ t ∈ clsOf p E s, b₀ ∉ autFixedInG E t := by
    by_contra hall
    push Not at hall
    exact hb₀1 (hJ.fixed_trivial b₀ (hBE hb₀B) hall)
  have ht₁a := hcls t₁ ht₁
  obtain ⟨k₁, hk₁, hk₁J, hk₁t⟩ := hlift t₁ ht₁a
  have hl₁ : autMovedInG E t₁ ≤ B :=
    autMovedInG_le_of_move hd (hrefl t₁ ht₁a).1 hk₁ hk₁t hBE (hinvt t₁ ht₁a k₁ hk₁ hk₁J) hb₀B hmov
  have hprop : ∀ t ∈ clsOf p E a, ∀ x ∈ clsOf p E a, autMovedInG E t ≤ B → x * t ≠ t * x →
      autMovedInG E x ≤ B := by
    intro t ht x hx hlt hnc
    obtain ⟨kx, hkx, hkxJ, hkxx⟩ := hlift x hx
    exact propagate hd hX hp5 (hrefl t ht).1 (hrefl x hx).1 (hrefl t ht).2 (hrefl x hx).2 hkx hkxx
      hBE (hinvt x hx kx hkx hkxJ) hlt hnc
  have hconn : ∀ x ∈ clsOf p E a, x = a ∨ a * x ≠ x * a ∨
      ∃ u, u ∈ clsOf p E a ∧ a * u ≠ u * a ∧ x * u ≠ u * x := by
    intro x hx
    rcases bridge_conn Bd h hcard ha hb H.hzs hab4 (H.hzc a haL) (H.hzc b hbL) hza hzb hzab hzba
        ⟨g₀, hg₀X, hg₀⟩ hx with h1 | h1 | ⟨u, hu, hau, hxu⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr ⟨u, hu, hau, hxu⟩)
  have hla : autMovedInG E a ≤ B := by
    rcases hconn t₁ ht₁a with h1 | h1 | ⟨u, hu, hau, htu⟩
    · rw [← h1]; exact hl₁
    · exact hprop t₁ ht₁a a (mem_clsOf_self p E a) hl₁ h1
    · have hlu := hprop t₁ ht₁a u hu hl₁ (Ne.symm htu)
      exact hprop u hu a (mem_clsOf_self p E a) hlu hau
  have hlines : ∀ y ∈ clsOf p E a, autMovedInG E y ≤ B := by
    intro y hy
    rcases hconn y hy with h1 | h1 | ⟨u, hu, hau, hyu⟩
    · rw [h1]; exact hla
    · exact hprop a (mem_clsOf_self p E a) y hy hla (Ne.symm h1)
    · have hlu := hprop a (mem_clsOf_self p E a) u hu hla (Ne.symm hau)
      exact hprop u hu y hy hlu hyu
  have hg₀W : g₀ ∈ torusWeyl E := Sec1322.reflectionGroup_le E hg₀X
  have ht3 : g₀ * a * g₀⁻¹ ∈ clsOf p E a := ⟨g₀, hg₀X, rfl⟩
  have ht4 : g₀ * a' * g₀⁻¹ ∈ clsOf p E a :=
    ⟨g₀ * h₁, Subgroup.mul_mem _ hg₀X hh₁X, by rw [← hh₁]; group⟩
  have hEB : E ≤ B :=
    E_le_of_lines hd hcE (RefFacts.mul_self_eq_one ha.1) (RefFacts.mul_self_eq_one ha'.1) hcomm
      (hucen b hbL) (hfixc b hbL hcE) hfixu hg₀W hg₀ H.hmov (hlines a (mem_clsOf_self p E a))
      (hlines a' ha'cls) (hlines _ ht3) (hlines _ ht4)
  exact le_antisymm hEB hBE |>.symm

end Main

end CFSG.RankThree.PartOne.Q1327
