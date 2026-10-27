module

public import CFSG.Quasithin.H13.A6S1372L76Og2
public import CFSG.Quasithin.H13.A6S1372L76Oe2
public import CFSG.Quasithin.H13.A6S1372L76Og1

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative Matrix

namespace A6L76Og

theorem eq_of_odd_of_mem_fixV {W : Type*} [CommGroup W] (h2 : ∀ w : W, w * w = 1)
    {Y : Subgroup (MulAut W)} {y : MulAut W} (hy : y ∈ Y) (hodd : Odd (orderOf y)) {w : W}
    (hw : y w * w⁻¹ ∈ fixV Y) : y w = w := by
  obtain ⟨c, hc⟩ : ∃ c, c = y w * w⁻¹ := ⟨_, rfl⟩
  have hyc : y c = c := by rw [hc]; exact hw y hy
  have hyw : y w = c * w := by rw [hc, inv_mul_cancel_right]
  have hpow : ∀ j : ℕ, (y ^ j) w = c ^ j * w := by
    intro j
    induction j with
    | zero => rw [pow_zero, pow_zero, one_mul, MulAut.one_apply]
    | succ j ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hyc, hyw, pow_succ, mul_assoc]
  have h1 := hpow (orderOf y)
  rw [pow_orderOf_eq_one, MulAut.one_apply] at h1
  have hc1 : c ^ orderOf y = 1 := by
    have h3 : c ^ orderOf y * w = 1 * w := by rw [one_mul]; exact h1.symm
    exact mul_right_cancel h3
  obtain ⟨t, ht⟩ := hodd
  have hcc : c ^ orderOf y = c := by rw [ht, pow_succ, pow_mul, sq, h2 c, one_pow, one_mul]
  rw [hyw, ← hcc, hc1, one_mul]

theorem exists_odd_lift {A B : Type*} [Group A] [Group B] [Finite A] (φ : A →* B) (a : A)
    (hodd : Odd (orderOf (φ a))) : ∃ a' : A, Odd (orderOf a') ∧ φ a' = φ a := by
  obtain ⟨e, m', hm', hm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos a).ne'
  have hcop : Nat.Coprime (2 ^ e) (orderOf (φ a)) := (Nat.coprime_two_left.2 hodd).pow_left e
  by_cases ho : orderOf (φ a) = 1
  · refine ⟨1, by rw [orderOf_one]; exact odd_one, ?_⟩
    rw [map_one, (orderOf_eq_one_iff.1 ho)]
  · obtain ⟨r, -, hr⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by
      obtain ⟨t, ht⟩ := hodd
      omega)
    refine ⟨a ^ (2 ^ e * r), ?_, ?_⟩
    · have h1 : (a ^ (2 ^ e * r)) ^ m' = 1 := by
        rw [← pow_mul, show 2 ^ e * r * m' = (2 ^ e * m') * r by ring, pow_mul, ← hm,
          pow_orderOf_eq_one, one_pow]
      exact Odd.of_dvd_nat hm' (orderOf_dvd_of_pow_eq_one h1)
    · rw [map_pow, ← pow_mod_orderOf, hr, pow_one]

theorem exists_pow_three_lift {A B : Type*} [Group A] [Group B] (φ : A →* B) (x : A)
    (h3 : φ x ^ 3 = 1) {j : ℕ} (hj : (x ^ 3) ^ (2 ^ j) = 1) :
    ∃ N : ℕ, (x ^ N) ^ 3 = 1 ∧ φ (x ^ N) = φ x := by
  have hcop : Nat.Coprime (2 ^ j) 3 :=
    (Nat.coprime_two_left.2 (by decide : Odd 3)).pow_left j
  obtain ⟨r, -, hr⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by norm_num)
  refine ⟨2 ^ j * r, ?_, ?_⟩
  · rw [← pow_mul, show 2 ^ j * r * 3 = 3 * 2 ^ j * r by ring, pow_mul, pow_mul, hj, one_pow]
  · rw [map_pow, ← Nat.div_add_mod (2 ^ j * r) 3, hr, pow_add, pow_mul, h3, one_pow, one_mul,
      pow_one]

theorem exists_levi {W : Type*} [CommGroup W] {Y : Subgroup (MulAut W)}
    (hY : Group.IsPerfect ↥Y) {F : Type} [Field F] [Finite F] {n : ℕ} (hn2 : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) {π : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) →* ↥Y}
    (hπ : (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 F)).RealizesVia Y (commV Y)
      (fixV Y ⊓ commV Y) π)
    {a : MulAut W} (haY : ∀ y ∈ Y, a * y * a⁻¹ ∈ Y)
    {P : Subgroup (MulAut W)} (hP2 : IsPGroup 2 ↥P)
    (hPodd : Odd (P.subgroupOf Y).index) {v₂ : W} (hPv : ∀ p ∈ P, p v₂ = v₂)
    (hPa : ∀ p ∈ P, p (a v₂) = a v₂ ∨ p (a v₂) = v₂ * a v₂) (hv : v₂ ∉ fixV Y) :
    ∃ ι : Matrix.SpecialLinearGroup (Fin 2) F →* ↥Y, Function.Injective ι ∧
      ∀ A, ((ι A : ↥Y) : MulAut W) v₂ * v₂⁻¹ ∈ fixV Y ∧
        ((ι A : ↥Y) : MulAut W) (a v₂) * (a v₂)⁻¹ ∈ fixV Y := by
  obtain ⟨g, hfix⟩ := exists_fix_line hY hn2 hF hπ haY hP2 hPodd hPv hPa hv
  have hinj : Function.Injective π :=
    FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ
  let cg : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) →*
      ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) :=
    { toFun := fun x => g⁻¹ * x * g
      map_one' := by group
      map_mul' := fun x y => by group }
  have hcg : Function.Injective cg := fun x y h => by
    have h1 : g⁻¹ * x * g = g⁻¹ * y * g := h
    simpa using h1
  let e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F
  refine ⟨π.comp (cg.comp (e.toMonoidHom.comp leviHom)),
    hinj.comp (hcg.comp (e.injective.comp leviHom_injective)), fun A => ?_⟩
  refine hfix (g⁻¹ * e (leviHom A) * g) fun x hx1 hx2 => ?_
  rw [show g * (g⁻¹ * e (leviHom A) * g) * g⁻¹ = e (leviHom A) by group]
  apply Multiplicative.toAdd.injective
  rw [A6L76Of.natHom_apply]
  exact leviMat_mulVec hx1 hx2

theorem false_of_sl2_image {K Kt : Type*} [Group K] [Finite K] [Group Kt] {F : Type} [Field F]
    [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F) {κ : K →* Kt} (hκs : Function.Surjective κ)
    {ι : Matrix.SpecialLinearGroup (Fin 2) F →* Kt} (hι : Function.Injective ι)
    {Y₀ X : Subgroup K} (hgen : ∀ k, Odd (orderOf k) → κ k ∈ ι.range → k ∈ Y₀)
    (hκY : ∀ k ∈ Y₀, κ k ∈ ι.range) (hXn : ∀ y ∈ Y₀, ∀ x ∈ X, y * x * y⁻¹ ∈ X)
    (h48 : ∀ k ∈ Y₀, k ^ 48 ∈ X) (hκ2 : ∀ k, κ k = 1 → ∃ j : ℕ, k ^ (2 ^ j) = 1)
    (h3 : (∀ x ∈ X, orderOf x ≠ 3) ∨ (∀ x₁ ∈ X, ∀ x₂ ∈ X, orderOf x₁ = 3 → orderOf x₂ = 3 →
      ∃ j : ℕ, (x₁ * x₂) ^ (3 * 2 ^ j) = 1)) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsimple := isSimpleGroup_sl2 (F := F) h4
  set A₀ : Matrix.SpecialLinearGroup (Fin 2) F := ⟨sl2A, det_sl2A⟩ with hA₀
  have hA₀3 : A₀ ^ 3 = 1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_pow]
    exact pow_three_of_trace_one det_sl2A trace_sl2A)
  have hA₀1 : A₀ ≠ 1 := by
    intro h
    have h1 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) F =>
      (M : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp [hA₀, sl2A] at h1
  have hA₀o : orderOf A₀ = 3 := orderOf_eq_prime hA₀3 hA₀1
  have hN₀ : Subgroup.normalClosure {A : Matrix.SpecialLinearGroup (Fin 2) F |
      Odd (orderOf A)} = ⊤ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure
        {A : Matrix.SpecialLinearGroup (Fin 2) F | Odd (orderOf A)}) with h | h
    · exfalso
      have hA : A₀ ∈ Subgroup.normalClosure {A : Matrix.SpecialLinearGroup (Fin 2) F |
          Odd (orderOf A)} := Subgroup.subset_normalClosure (show Odd (orderOf A₀) by
            rw [hA₀o]
            decide)
      rw [h, Subgroup.mem_bot] at hA
      exact hA₀1 hA
    · exact h
  have hsurj : ∀ A, ∃ k ∈ Y₀, κ k = ι A := by
    have hle : Subgroup.normalClosure {A : Matrix.SpecialLinearGroup (Fin 2) F |
        Odd (orderOf A)} ≤ (Y₀.map κ).comap ι := by
      show Subgroup.closure (Group.conjugatesOfSet {A : Matrix.SpecialLinearGroup (Fin 2) F |
        Odd (orderOf A)}) ≤ _
      refine (Subgroup.closure_le _).2 fun A hA => ?_
      obtain ⟨B, hB, hAB⟩ := Group.mem_conjugatesOfSet_iff.1 hA
      have hoddA : Odd (orderOf A) := by
        rw [← hAB.orderOf_eq]
        exact hB
      have hoddι : Odd (orderOf (ι A)) := by rwa [orderOf_injective ι hι]
      obtain ⟨k, hk⟩ := hκs (ι A)
      obtain ⟨k', hk', hk'κ⟩ := exists_odd_lift κ k (by rwa [hk])
      exact ⟨k', hgen k' hk' (by rw [hk'κ, hk]; exact ⟨A, rfl⟩), by rw [hk'κ, hk]⟩
    intro A
    obtain ⟨k, hk, hkA⟩ := hle (by rw [hN₀]; exact Subgroup.mem_top A)
    exact ⟨k, hk, hkA⟩
  set XS : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) := (X.map κ).comap ι with hXS
  have hXSn : XS.Normal := by
    refine ⟨fun A hA B => ?_⟩
    obtain ⟨x, hx, hxA⟩ := hA
    obtain ⟨y, hy, hyB⟩ := hsurj B
    refine ⟨y * x * y⁻¹, hXn y hy x hx, ?_⟩
    rw [map_mul, map_mul, map_inv, hxA, hyB, map_mul, map_mul, map_inv]
  obtain ⟨c, hc0, hc1⟩ : ∃ c : F, c ≠ 0 ∧ c ≠ 1 := by
    have : Fintype F := Fintype.ofFinite F
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := fun c _ => by
      by_cases h : c = 0
      · simp [h]
      · simp [hcon c h]
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h2
    have h3 : ({0, 1} : Finset F).card ≤ 2 := Finset.card_le_two
    omega
  set B₀ : Matrix.SpecialLinearGroup (Fin 2) F := ⟨sl2B c, det_sl2B c⟩ with hB₀
  have hB₀3 : B₀ ^ 3 = 1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_pow]
    exact pow_three_of_trace_one (det_sl2B c) (trace_sl2B c))
  have hB₀1 : B₀ ≠ 1 := by
    intro h
    have h1 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) F =>
      (M : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simp [hB₀, sl2B] at h1
  have hAB : ∀ m : ℕ, ι ((A₀ * B₀) ^ (3 * 2 ^ m)) ≠ 1 := by
    intro m h
    rw [← map_one ι] at h
    have h1 : ((A₀ * B₀ : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) ^ (3 * 2 ^ m) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_pow, hι h]
      rfl
    have h2 := trace_of_pow_eq_one _ (A₀ * B₀).2 h1
    have h3 := trace_sl2A_mul_sl2B_ne hc0 hc1
    rcases h2 with h2 | h2
    · exact h3.1 h2
    · exact h3.2 h2
  rcases hsimple.eq_bot_or_eq_top_of_normal XS with hbot | htop
  ·
    obtain ⟨y, hy, hyC⟩ := hsurj (A₀ * B₀)
    have h1 : κ (y ^ 48) = 1 := by
      obtain ⟨A, hA⟩ := hκY _ (Y₀.pow_mem hy 48)
      have hA' : A ∈ XS := ⟨_, h48 y hy, hA.symm⟩
      rw [hbot, Subgroup.mem_bot] at hA'
      rw [← hA, hA', map_one]
    obtain ⟨j, hj⟩ := hκ2 _ h1
    apply hAB (j + 4)
    rw [map_pow, ← hyC, ← map_pow, show 3 * 2 ^ (j + 4) = 48 * 2 ^ j by ring, pow_mul, hj,
      map_one]
  ·
    have hlift3 : ∀ A : Matrix.SpecialLinearGroup (Fin 2) F, A ^ 3 = 1 → A ≠ 1 →
        ∃ x ∈ X, orderOf x = 3 ∧ κ x = ι A := by
      intro A hA3 hA1
      have hA : A ∈ XS := by rw [htop]; exact Subgroup.mem_top A
      obtain ⟨x, hx, hxA⟩ := hA
      have h1 : κ (x ^ 3) = 1 := by rw [map_pow, hxA, ← map_pow, hA3, map_one]
      obtain ⟨j, hj⟩ := hκ2 _ h1
      obtain ⟨N, hN3, hNκ⟩ := exists_pow_three_lift κ x (by rw [hxA, ← map_pow, hA3,
        map_one]) hj
      refine ⟨x ^ N, X.pow_mem hx N, orderOf_eq_prime hN3 fun h => hA1 (hι ?_), hNκ.trans hxA⟩
      rw [← hNκ.trans hxA, h, map_one, map_one]
    obtain ⟨xA, hxA, hxAo, hxAκ⟩ := hlift3 A₀ hA₀3 hA₀1
    obtain ⟨xB, hxB, hxBo, hxBκ⟩ := hlift3 B₀ hB₀3 hB₀1
    rcases h3 with h3 | h3
    · exact h3 xA hxA hxAo
    · obtain ⟨j, hj⟩ := h3 xA hxA xB hxB hxAo hxBo
      apply hAB j
      rw [map_pow, map_mul, ← hxAκ, ← hxBκ, ← map_mul, ← map_pow, hj, map_one]

end A6L76Og

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

theorem secMk_V3_mem {H : Subgroup G} (hH : H ∈ S.Hz)
    [IsMulCommutative ↥(conjClosure S.V3 H)] {g : ↥(Subgroup.normalizer (V : Set G))}
    (hgX : (g : G) ∈ S.X1375) (hg : S.frame.ρ g = swap 0 1 * swap 1 2)
    {Q : Subgroup (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))}
    (h1 : InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
      ⟨S.v2, S.v2_mem_UH H⟩ ∈ Q)
    (h2 : A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 hH)
      ⟨g, X1375_le_H hH hgX⟩ (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
        ⟨S.v2, S.v2_mem_UH H⟩) ∈ Q) :
    ∀ u (hu : u ∈ S.V3), InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
      ⟨u, le_conjClosure _ _ hu⟩ ∈ Q := by
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHV := S.le_normalizer_UV1 hH
  have hv2U := S.v2_mem_UH H
  have hgv : (g : G) * S.v2 * (g : G)⁻¹ ∈ S.V3 := by
    refine S.mem_pre.2 ⟨S.conj_v2_mem_V g, ?_⟩
    show InW3 ((S.frame.ψ ⟨_, S.conj_v2_mem_V g⟩ : ↥W4) : P6)
    rw [S.psi_conj_v2, hg]
    exact A6L76G.w4_facts.2.2.2.2.2.1
  have hmul : ∀ (u w : G) (hu : u ∈ conjClosure S.V3 H) (hw : w ∈ conjClosure S.V3 H),
      InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
        ⟨u * w, (conjClosure S.V3 H).mul_mem hu hw⟩ =
      InternalSec.secMk _ ⟨u, hu⟩ * InternalSec.secMk _ ⟨w, hw⟩ := by
    intro u w hu hw
    rw [← map_mul]
    rfl
  have hgvU : (g : G) * S.v2 * (g : G)⁻¹ ∈ conjClosure S.V3 H := le_conjClosure _ _ hgv
  have hfix1 : InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
      ⟨_, hgvU⟩ ∈ Q := by
    have e : InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) ⟨_, hgvU⟩ =
        A6Mod.secAct hHU hHV ⟨g, X1375_le_H hH hgX⟩ (InternalSec.secMk _ ⟨S.v2, hv2U⟩) := by
      rw [A6Mod.secAct_secMk]
      congr 1
    rw [e]
    exact h2
  have hg2U : ((g ^ 2 : ↥(Subgroup.normalizer (V : Set G))) : G) * S.v2 *
      ((g ^ 2 : ↥(Subgroup.normalizer (V : Set G))) : G)⁻¹ ∈ conjClosure S.V3 H := by
    rw [← S.v2_mul_conj hg]
    exact (conjClosure S.V3 H).mul_mem hv2U hgvU
  have hfix2 : InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
      ⟨_, hg2U⟩ ∈ Q := by
    have e : (⟨_, hg2U⟩ : ↥(conjClosure S.V3 H)) = ⟨S.v2, hv2U⟩ * ⟨_, hgvU⟩ :=
      Subtype.ext (S.v2_mul_conj hg).symm
    rw [e, map_mul]
    exact Subgroup.mul_mem _ h1 hfix1
  intro u hu
  have huU : u ∈ conjClosure S.V3 H := le_conjClosure _ _ hu
  have hinv : ∀ (w : G) (hw : w ∈ conjClosure S.V3 H), u * w ∈ fsuV1 T V →
      InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) ⟨w, hw⟩ ∈ Q →
      InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) ⟨u, huU⟩ ∈ Q := by
    intro w hw huw hwf
    have h1 : InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
        ⟨u * w, (conjClosure S.V3 H).mul_mem huU hw⟩ = 1 :=
      (A6Mod.secMk_eq_one_iff _).2 huw
    rw [hmul u w huU hw] at h1
    rw [eq_inv_of_mul_eq_one_left h1]
    exact Subgroup.inv_mem _ hwf
  rcases S.mem_V3_cases hg hu with h | h | h | h
  · have h1 : InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
        ⟨u, huU⟩ = 1 := (A6Mod.secMk_eq_one_iff _).2 h
    rw [h1]
    exact Subgroup.one_mem _
  · exact hinv _ hv2U h h1
  · exact hinv _ hgvU h hfix1
  · exact hinv _ hg2U h hfix2

theorem fix_V3_of_odd {H : Subgroup G} (hH : H ∈ S.Hz)
    (hab : IsElemAbelian 2 (conjClosure S.V3 H)) [IsMulCommutative ↥(conjClosure S.V3 H)]
    {K : Subgroup G} {g : ↥(Subgroup.normalizer (V : Set G))} (hgX : (g : G) ∈ S.X1375)
    (hg : S.frame.ρ g = swap 0 1 * swap 1 2)
    {y : MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))}
    (hy : y ∈ autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) (hodd : Odd (orderOf y))
    (h1 : y (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
        ⟨S.v2, S.v2_mem_UH H⟩) *
      (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
        ⟨S.v2, S.v2_mem_UH H⟩)⁻¹ ∈ fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
    (h2 : y (A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 hH)
        ⟨g, X1375_le_H hH hgX⟩ (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
          ⟨S.v2, S.v2_mem_UH H⟩)) *
      (A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 hH)
        ⟨g, X1375_le_H hH hgX⟩ (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
          ⟨S.v2, S.v2_mem_UH H⟩))⁻¹ ∈ fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) :
    ∀ u (hu : u ∈ S.V3), y (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
      ⟨u, le_conjClosure _ _ hu⟩) = InternalSec.secMk _ ⟨u, le_conjClosure _ _ hu⟩ := by
  intro u hu
  let C := fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
  let Q : Subgroup (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) :=
    { carrier := {w | y w * w⁻¹ ∈ C}
      mul_mem' := fun {w w'} hw hw' => by
        have e : y (w * w') * (w * w')⁻¹ = (y w * w⁻¹) * (y w' * w'⁻¹) := by
          rw [map_mul, mul_inv_rev]
          ac_rfl
        show y (w * w') * (w * w')⁻¹ ∈ C
        rw [e]
        exact Subgroup.mul_mem _ hw hw'
      one_mem' := by
        show y 1 * 1⁻¹ ∈ C
        rw [map_one, inv_one, mul_one]
        exact Subgroup.one_mem _
      inv_mem' := fun {w} hw => by
        have e : y w⁻¹ * w⁻¹⁻¹ = (y w * w⁻¹)⁻¹ := by
          rw [map_inv, inv_inv, mul_inv_rev, inv_inv]
          ac_rfl
        show y w⁻¹ * w⁻¹⁻¹ ∈ C
        rw [e]
        exact Subgroup.inv_mem _ hw }
  exact A6L76Og.eq_of_odd_of_mem_fixV (sec_mul_self hab) hy hodd
    (secMk_V3_mem hH hgX hg (Q := Q) h1 h2 u hu)

theorem conj_mem_V3_of_fix {H : Subgroup G} (hH : H ∈ S.Hz)
    [IsMulCommutative ↥(conjClosure S.V3 H)] {h : G} (hh : h ∈ H)
    (hfix : ∀ u (hu : u ∈ S.V3), A6Mod.secAct (le_normalizer_conjClosure S.V3 H)
      (S.le_normalizer_UV1 hH) ⟨h, hh⟩ (InternalSec.secMk
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) ⟨u, le_conjClosure _ _ hu⟩) =
      InternalSec.secMk _ ⟨u, le_conjClosure _ _ hu⟩) :
    ∀ u ∈ S.V3, h * u * h⁻¹ ∈ S.V3 := by
  intro u hu
  have h3 := hfix u hu
  rw [A6Mod.secAct_secMk] at h3
  have h5 : InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
      (Setup.rho (conjClosure S.V3 H) H (le_normalizer_conjClosure S.V3 H) ⟨h, hh⟩
        ⟨u, le_conjClosure _ _ hu⟩ * (⟨u, le_conjClosure _ _ hu⟩ : ↥(conjClosure S.V3 H))⁻¹) =
      1 := by
    rw [map_mul, map_inv, h3, mul_inv_cancel]
  rw [A6Mod.secMk_eq_one_iff, Subgroup.coe_mul, Setup.rho_apply_coe, Subgroup.coe_inv] at h5
  have h6 : h * u * h⁻¹ = (h * u * h⁻¹ * u⁻¹) * u := by group
  rw [h6]
  exact S.V3.mul_mem ((S.V1_le_V2.trans S.V2_le_V3) h5) hu

theorem false_of_levi (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) (h1337 : Stmt13_3_7) (hNS : ¬ LieModel G .PSp 3 2 1)
    {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
    [IsMulCommutative ↥(conjClosure S.V3 H)] {K : Subgroup G} (hK : K ∈ cComp H)
    {g₀ : ↥(Subgroup.normalizer (V : Set G))} (hgX : (g₀ : G) ∈ S.X1375)
    (hg : S.frame.ρ g₀ = swap 0 1 * swap 1 2) {F : Type} [Field F] [Finite F] [CharP F 2]
    (h4 : 4 ≤ Nat.card F)
    {ι : Matrix.SpecialLinearGroup (Fin 2) F →* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))} (hιinj : Function.Injective ι)
    (hιfix : ∀ A, ((ι A : ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) : MulAut _)
        (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) ⟨S.v2, S.v2_mem_UH H⟩) *
        (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
          ⟨S.v2, S.v2_mem_UH H⟩)⁻¹ ∈ fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ∧
      ((ι A : ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) : MulAut _)
        (A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 hH)
          ⟨g₀, X1375_le_H hH hgX⟩ (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
            ⟨S.v2, S.v2_mem_UH H⟩)) *
        (A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 hH)
          ⟨g₀, X1375_le_H hH hgX⟩ (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
            ⟨S.v2, S.v2_mem_UH H⟩))⁻¹ ∈ fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
              ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHV := S.le_normalizer_UV1 hH
  have hKH : K ≤ H := le_of_mem_cComp hK
  let κ : ↥K →* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) :=
    ((A6Mod.secAct hHU hHV).comp (Subgroup.inclusion hKH)).codRestrict _
      fun k => (A6Mod.mem_autSec_iff hHU hHV hKH).2 ⟨_, k.2, rfl⟩
  have hκ : ∀ k : ↥K, ((κ k : ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) : MulAut _) =
      A6Mod.secAct hHU hHV ⟨k, hKH k.2⟩ := fun k => rfl
  have hκs : Function.Surjective κ := by
    rintro ⟨ψ, hψ⟩
    obtain ⟨f, hfK, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHV hKH).1 hψ
    exact ⟨⟨f, hfK⟩, rfl⟩
  have hκ2 : ∀ k : ↥K, κ k = 1 → ∃ j : ℕ, k ^ (2 ^ j) = 1 := by
    intro k hk
    have h1 : A6Mod.secAct hHU hHV ⟨k, hKH k.2⟩ = 1 := by
      rw [← hκ]
      exact congrArg Subtype.val hk
    have h2 := (S.mem_QH_iff_tilde hNS h13315 h1356two hH (hKH k.2)).2
      ((A6Mod.secAct_eq_one_iff hHU hHV _).1 h1)
    obtain ⟨j, hj⟩ := (pCoreOf_isPGroup 2 H) ⟨_, h2⟩
    exact ⟨j, Subtype.ext (by simpa using congrArg Subtype.val hj)⟩
  set Y₀ : Subgroup ↥K := Subgroup.closure {k | Odd (orderOf k) ∧ κ k ∈ ι.range} with hY₀
  have hgenV3 : ∀ k : ↥K, Odd (orderOf k) → κ k ∈ ι.range →
      ∀ u ∈ S.V3, (k : G) * u * (k : G)⁻¹ ∈ S.V3 := by
    intro k hk hkι
    obtain ⟨A, hA⟩ := hkι
    obtain ⟨h1, h2⟩ := hιfix A
    rw [hA] at h1 h2
    have hfix := S.fix_V3_of_odd hH hab hgX hg (κ k).2
      (Odd.of_dvd_nat hk (by rw [Subgroup.orderOf_coe]; exact orderOf_map_dvd κ k)) h1 h2
    exact S.conj_mem_V3_of_fix hH (hKH k.2) fun u hu => by rw [← hκ]; exact hfix u hu
  have hY₀N : ∀ k ∈ Y₀, (k : G) ∈ Subgroup.normalizer (S.V3 : Set G) := by
    have hle : Y₀ ≤ (Subgroup.normalizer (S.V3 : Set G)).comap K.subtype := by
      rw [hY₀, Subgroup.closure_le]
      rintro k ⟨hk, hkι⟩
      show (k : G) ∈ Subgroup.normalizer (S.V3 : Set G)
      rw [Subgroup.mem_normalizer_iff]
      intro u
      refine ⟨hgenV3 k hk hkι u, fun hu' => ?_⟩
      have hk' : Odd (orderOf k⁻¹) := by rwa [orderOf_inv]
      have hkι' : κ k⁻¹ ∈ ι.range := by
        rw [map_inv]
        exact ι.range.inv_mem hkι
      have h1 := hgenV3 k⁻¹ hk' hkι' _ hu'
      have e : ((k⁻¹ : ↥K) : G) * ((k : G) * u * (k : G)⁻¹) * ((k⁻¹ : ↥K) : G)⁻¹ = u := by
        simp only [InvMemClass.coe_inv, inv_inv]
        group
      rwa [e] at h1
    exact fun k hk => hle hk
  have hY₀NV : ∀ k ∈ Y₀, (k : G) ∈ Subgroup.normalizer (V : Set G) :=
    fun k hk => S.G1_inf_G3_le h13315 ⟨hH.2.1 (hKH k.2), hY₀N k hk⟩
  set X : Subgroup ↥K := Y₀ ⊓ (Subgroup.centralizer (V : Set G)).comap K.subtype with hX
  refine A6L76Og.false_of_sl2_image h4 hκs hιinj (Y₀ := Y₀) (X := X)
    (fun k hk hkι => Subgroup.subset_closure ⟨hk, hkι⟩) (fun k hk => ?_) (fun y hy x hx => ?_)
    (fun k hk => ?_) hκ2 ?_
  ·
    have hle : Y₀ ≤ ι.range.comap κ := by
      rw [hY₀, Subgroup.closure_le]
      rintro k ⟨-, hk⟩
      exact hk
    exact hle hk
  ·
    refine ⟨Y₀.mul_mem (Y₀.mul_mem hy hx.1) (Y₀.inv_mem hy), ?_⟩
    show ((y * x * y⁻¹ : ↥K) : G) ∈ Subgroup.centralizer (V : Set G)
    have hyV := hY₀NV y hy
    have hxV : ((x : ↥K) : G) ∈ Subgroup.centralizer (V : Set G) := hx.2
    rw [Subgroup.mem_centralizer_iff] at hxV ⊢
    intro v hv
    have hv' : ((y : ↥K) : G)⁻¹ * v * ((y : ↥K) : G)⁻¹⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyV) v).mp hv
    have h1 := hxV _ hv'
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, inv_inv] at h1 ⊢
    calc v * ((y : G) * (x : G) * (y : G)⁻¹)
        = (y : G) * ((y : G)⁻¹ * v * (y : G) * (x : G)) * (y : G)⁻¹ := by group
      _ = (y : G) * ((x : G) * ((y : G)⁻¹ * v * (y : G))) * (y : G)⁻¹ := by rw [h1]
      _ = (y : G) * (x : G) * (y : G)⁻¹ * v := by group
  ·
    refine ⟨Y₀.pow_mem hk 48, ?_⟩
    show ((k ^ 48 : ↥K) : G) ∈ Subgroup.centralizer (V : Set G)
    have hz : (k : G) * S.z * (k : G)⁻¹ = S.z := by
      have h1 : (k : G) ∈ S.G1 := hH.2.1 (hKH k.2)
      rw [Setting4.G1, Subgroup.mem_centralizer_singleton_iff] at h1
      rw [h1, mul_inv_cancel_right]
    have hmem : S.frame.ρ ⟨(k : G), hY₀NV k hk⟩ ∈ A6L76F.stabE := S.fix_e0123 _ hz
    have h := orderOf_dvd_natCard (⟨_, hmem⟩ : ↥A6L76F.stabE)
    rw [A6L76F.card_stabE] at h
    have h2 := orderOf_dvd_iff_pow_eq_one.1 h
    have h3 : S.frame.ρ (⟨(k : G), hY₀NV k hk⟩ ^ 48) = 1 := by
      rw [map_pow]
      simpa using congrArg Subtype.val h2
    have h4 := (S.rho_eq_one_iff _).1 h3
    simpa using h4
  ·
    rcases h1337 G T L V S.h13 S.irr S.a6 with h3 | ⟨hhat, -, hl0⟩
    · left
      intro x hx hxo
      apply h3
      have h1 := Subgroup.orderOf_dvd_natCard _ (show ((x : ↥K) : G) ∈
        Subgroup.centralizer (V : Set G) from hx.2)
      rwa [Subgroup.orderOf_coe, hxo] at h1
    · right
      intro x₁ hx₁ x₂ hx₂ ho₁ ho₂
      have hmemL : ∀ x ∈ X, orderOf x = 3 → ((x : ↥K) : G) ∈ l0 L := by
        intro x hx hxo
        rw [hl0]
        exact Subgroup.subset_closure ⟨hx.2, by rw [Subgroup.orderOf_coe]; exact hxo⟩
      have hp : ((x₁ : ↥K) : G) * ((x₂ : ↥K) : G) ∈ o2Z L :=
        oTwoRes_le _ ((l0 L).mul_mem (hmemL x₁ hx₁ ho₁) (hmemL x₂ hx₂ ho₂))
      obtain ⟨j, hj⟩ := (pCoreOf_isPGroup 2 L) ⟨_, cube_mem_of_o2Z hhat hp⟩
      exact ⟨j, Subtype.ext (by rw [pow_mul]; simpa using hj)⟩

theorem false_of_natSL3_ge_two (h139 : Stmt13_3_9)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
    (h1337 : Stmt13_3_7) (hNS : ¬ LieModel G .PSp 3 2 1) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hab : IsElemAbelian 2 (conjClosure S.V3 H)) [IsMulCommutative ↥(conjClosure S.V3 H)]
    {K : Subgroup G} (hK : K ∈ cComp H) {n : ℕ} (hn2 : 2 ≤ n)
    (hSL : BinaryNaturalSL (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 3 n) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := id hSL
  have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hF
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  obtain ⟨g₀, hgX, hg⟩ := S.exists_X1375_c012
  obtain ⟨a, P, v₂, rfl, -, rfl, haY, -, hP2, hPodd, hPv, hPa, -, hv⟩ :=
    S.exists_odd_config_of hH hK rfl h139 h37 h38 h13315 hgX hg
  obtain ⟨ι, hιinj, hιfix⟩ := A6L76Og.exists_levi (S.isPerfect_tilde hH hK) hn2 hF hπ haY
    hP2 hPodd hPv hPa hv
  exact S.false_of_levi h13315 h1356two h1337 hNS hH hab hK hgX hg h4 hιinj hιfix

end Setting4

end CFSG.Quasithin.H13.A6
