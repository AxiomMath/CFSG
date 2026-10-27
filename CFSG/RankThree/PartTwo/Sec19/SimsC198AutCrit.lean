module

public import CFSG.RankThree.PartTwo.Sec19.SimsC198Type
public import CFSG.RankThree.PartTwo.Sec19.SimsC198Coprime
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsC198

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Aux

variable {S : Type} [Group S] [Finite S]

private theorem exists_mul_of_mem_sup {A B : Subgroup S} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {x : S} (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hc).2
  have hx' : x ∈ ((A ⊔ B : Subgroup S) : Set S) := hx
  rw [hset] at hx'
  exact Set.mem_mul.mp hx'

private theorem isElemAbelian_sup {A B : Subgroup S} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hB : CFSG.Open.IsElemAbelian 3 B) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    CFSG.Open.IsElemAbelian 3 (A ⊔ B : Subgroup S) := by
  have hAA : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    congrArg Subtype.val (isMulCommutative_iff.mp hA.1 ⟨a, ha⟩ ⟨a', ha'⟩)
  have hBB : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b := fun b hb b' hb' =>
    congrArg Subtype.val (isMulCommutative_iff.mp hB.1 ⟨b, hb⟩ ⟨b', hb'⟩)
  refine ⟨isMulCommutative_iff.mpr fun x y => ?_, fun x hx => ?_⟩
  · obtain ⟨a, ha, b, hb, hx⟩ := exists_mul_of_mem_sup hc x.2
    obtain ⟨a', ha', b', hb', hy⟩ := exists_mul_of_mem_sup hc y.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy]
    have h1 : Commute a (a' * b') :=
      Commute.mul_right (hAA a ha a' ha') (hc a ha b' hb')
    have h2 : Commute b (a' * b') :=
      Commute.mul_right (hc a' ha' b hb).symm (hBB b hb b' hb')
    exact Commute.mul_left h1 h2
  · obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hc hx
    have hab : Commute a b := hc a ha b hb
    rw [hab.mul_pow, hA.2 a ha, hB.2 b hb, one_mul]

private theorem isPGroup_of_isElemAbelian {A : Subgroup S} (hA : CFSG.Open.IsElemAbelian 3 A) :
    IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hA.2 x x.2)⟩

private theorem isPGroup_sup {A B : Subgroup S} (hA : IsPGroup 3 A) (hB : IsPGroup 3 B)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : IsPGroup 3 (A ⊔ B : Subgroup S) := by
  intro x
  obtain ⟨a, ha, b, hb, hx⟩ := exists_mul_of_mem_sup hc x.2
  obtain ⟨m, hm⟩ := hA ⟨a, ha⟩
  obtain ⟨n, hn⟩ := hB ⟨b, hb⟩
  have hm' : a ^ 3 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hn' : b ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have ha' : a ^ 3 ^ (m + n) = 1 := by rw [pow_add, pow_mul, hm', one_pow]
  have hb' : b ^ 3 ^ (m + n) = 1 := by rw [pow_add, pow_mul', hn', one_pow]
  have hab : Commute a b := hc a ha b hb
  refine ⟨m + n, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, Subgroup.coe_one, ← hx, hab.mul_pow, ha', hb', one_mul]

private theorem isElemAbelian_of_le {E F : Subgroup S} (hEF : E ≤ F)
    (hF : CFSG.Open.IsElemAbelian 3 F) : CFSG.Open.IsElemAbelian 3 E := by
  have hFF : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (isMulCommutative_iff.mp hF.1 ⟨x, hx⟩ ⟨y, hy⟩)
  exact ⟨isMulCommutative_iff.mpr fun a b => Subtype.ext (hFF a (hEF a.2) b (hEF b.2)),
    fun x hx => hF.2 x (hEF hx)⟩

end Aux

section Datum

variable {S : Type} [Group S] [Finite S] {c : S} {L : Subgroup S} {𝒟 : Subgroup (MulAut S)}

theorem AutDatum.exists_fixed_elemAbelian (h : AutDatum S c L 𝒟) :
    ∃ B : Subgroup S, B ≤ fixIn 𝒟 L ∧ CFSG.Open.IsElemAbelian 3 B ∧ Nat.card B = 9 := by
  obtain ⟨Bt, hBt, hBt9⟩ := IsType198.exists_elemAbelian h.quasisimple h.type
  have hp : IsPGroup 3 Bt := IsPGroup.of_card (n := 2) (by rw [hBt9]; norm_num)
  obtain ⟨P, hPle, -, ⟨e⟩⟩ := h.exists_lift Bt hp
  refine ⟨P, hPle, ⟨isMulCommutative_iff.mpr fun a b => e.injective ?_, fun x hx => ?_⟩, ?_⟩
  · rw [map_mul, map_mul]
    exact isMulCommutative_iff.mp hBt.1 _ _
  · have h1 : (e ⟨x, hx⟩) ^ 3 = 1 := Subtype.ext (by simpa using hBt.2 _ (e ⟨x, hx⟩).2)
    have h2 : (⟨x, hx⟩ : P) ^ 3 = 1 := e.injective (by rw [map_pow, h1, map_one])
    simpa using congrArg Subtype.val h2
  · rw [Nat.card_congr e.toEquiv]
    exact hBt9

theorem AutDatum.exists_fixed_pGroup (h : AutDatum S c L 𝒟) :
    ∃ P : Subgroup S, P ≤ fixIn 𝒟 L ∧ IsPGroup 3 P ∧ 27 ≤ Nat.card P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 3 (L ⧸ aschbacherSolvableCore 3 L)) := inferInstance
  have h27 : 3 ^ 3 ∣ Nat.card (Q : Subgroup (L ⧸ aschbacherSolvableCore 3 L)) :=
    Q.pow_dvd_card_of_pow_dvd_card (by simpa using IsType198.twentySeven_dvd h.quasisimple h.type)
  have hQ27 : 27 ≤ Nat.card (Q : Subgroup (L ⧸ aschbacherSolvableCore 3 L)) :=
    Nat.le_of_dvd Nat.card_pos (by simpa using h27)
  obtain ⟨P, hPle, hP, ⟨e⟩⟩ := h.exists_lift (Q : Subgroup (L ⧸ aschbacherSolvableCore 3 L))
    Q.isPGroup'
  exact ⟨P, hPle, hP, by rw [Nat.card_congr e.toEquiv]; exact hQ27⟩

theorem AutDatum.fixIn_eq (h : AutDatum S c L 𝒟) (hθ : aschbacherSolvableCore 3 L = ⊥) :
    fixIn 𝒟 L = L := by
  refine le_antisymm (fixIn_le 𝒟 L) fun x hx => ?_
  obtain ⟨l, hl, hlt⟩ := h.surj_fixIn ((⟨x, hx⟩ : L) : L ⧸ aschbacherSolvableCore 3 L)
  have hmem : l⁻¹ * (⟨x, hx⟩ : L) ∈ aschbacherSolvableCore 3 L := QuotientGroup.eq.mp hlt
  rw [hθ, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  rwa [hmem] at hl

theorem AutDatum.apply_eq (h : AutDatum S c L 𝒟) (hZ : Subgroup.center S = ⊥) {φ : MulAut S}
    (hφ : φ ∈ 𝒟) : φ c = c := by
  apply CoprimeAux.conj_injective_of_center_eq_bot hZ
  apply MulEquiv.ext
  intro y
  obtain ⟨x, rfl⟩ := φ.surjective y
  have h1 := congrArg (fun ψ : MulAut S => ψ x) (h.comm φ hφ _ h.conj_mem)
  simpa [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv] using h1

theorem AutDatum.center_eq_bot [IsSimpleGroup S] (h : AutDatum S c L 𝒟) :
    Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with hbot | htop
  · exact hbot
  · exfalso
    have hcen : ∀ x y : S, x * y = y * x := fun x y => by
      have hx : x ∈ Subgroup.center S := by rw [htop]; trivial
      exact (Subgroup.mem_center_iff.mp hx y).symm
    have hTcomm : ∀ a b : L ⧸ aschbacherSolvableCore 3 L, a * b = b * a := by
      intro a b
      obtain ⟨a₀, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b₀, rfl⟩ := QuotientGroup.mk_surjective b
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      exact congrArg _ (Subtype.ext (hcen a₀ b₀))
    have hcenT : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊤ := by
      rw [eq_top_iff]
      intro a _
      rw [Subgroup.mem_center_iff]
      intro g
      exact hTcomm g a
    have h3 := IsType198.card_center h.quasisimple h.type
    have h7 := IsType198.le_card h.quasisimple h.type
    rw [hcenT, Subgroup.card_top] at h3
    omega

end Datum

section Inner

variable {S : Type} [Group S] [Finite S] {c : S} {L : Subgroup S} {𝒟 : Subgroup (MulAut S)}

private theorem card_mul_nine_le [IsSimpleGroup S] (h : AutDatum S c L 𝒟)
    (hinn : 𝒟 ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner S) {A : Subgroup S}
    (hA : A ≤ fixIn 𝒟 L) :
    Nat.card A * 9 ≤ 3 * Nat.card (A ⊔ 𝒟.comap (MulAut.conj : S →* MulAut S) : Subgroup S) := by
  have hZ := h.center_eq_bot
  have hDS9 : Nat.card (𝒟.comap (MulAut.conj : S →* MulAut S)) = 9 :=
    (card_comap_conj hZ hinn).trans h.card
  have hcomm : ∀ a ∈ A, ∀ d ∈ 𝒟.comap (MulAut.conj : S →* MulAut S), a * d = d * a :=
    fun a ha d hd =>
      Subgroup.mem_centralizer_iff.mp (comap_conj_le_centralizer 𝒟 L hd) a (hA ha)
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A _ hcomm).1
  have hinf : Nat.card (A ⊓ 𝒟.comap (MulAut.conj : S →* MulAut S) : Subgroup S) ≤ 3 :=
    calc Nat.card (A ⊓ 𝒟.comap (MulAut.conj : S →* MulAut S) : Subgroup S)
        ≤ Nat.card (𝒟.comap (MulAut.conj : S →* MulAut S) ⊓ L : Subgroup S) :=
          Subgroup.card_le_of_le fun x hx => ⟨hx.2, fixIn_le 𝒟 L (hA hx.1)⟩
      _ ≤ Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) := h.card_comap_inf_le hZ
      _ = 3 := IsType198.card_center h.quasisimple h.type
  rw [hDS9] at hprod
  calc Nat.card A * 9 = Nat.card (A ⊔ 𝒟.comap (MulAut.conj : S →* MulAut S) : Subgroup S) *
        Nat.card (A ⊓ 𝒟.comap (MulAut.conj : S →* MulAut S) : Subgroup S) := hprod.symm
    _ ≤ Nat.card (A ⊔ 𝒟.comap (MulAut.conj : S →* MulAut S) : Subgroup S) * 3 :=
      Nat.mul_le_mul_left _ hinf
    _ = 3 * Nat.card (A ⊔ 𝒟.comap (MulAut.conj : S →* MulAut S) : Subgroup S) := mul_comm _ _

theorem AutDatum.exists_elemAbelian_27 [IsSimpleGroup S] (h : AutDatum S c L 𝒟)
    (hinn : 𝒟 ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner S) :
    ∃ E : Subgroup S, CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 27 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨B, hBle, hBel, hB9⟩ := h.exists_fixed_elemAbelian
  have hZ := h.center_eq_bot
  have hDSel : CFSG.Open.IsElemAbelian 3 (𝒟.comap (MulAut.conj : S →* MulAut S)) :=
    isElemAbelian_comap_conj hZ h.comm h.pow_three
  have hcomm : ∀ a ∈ B, ∀ d ∈ 𝒟.comap (MulAut.conj : S →* MulAut S), a * d = d * a :=
    fun a ha d hd =>
      Subgroup.mem_centralizer_iff.mp (comap_conj_le_centralizer 𝒟 L hd) a (hBle ha)
  have hEel := isElemAbelian_sup hBel hDSel hcomm
  have h27 : 27 ≤ Nat.card (B ⊔ 𝒟.comap (MulAut.conj : S →* MulAut S) : Subgroup S) := by
    have := card_mul_nine_le h hinn hBle
    rw [hB9] at this
    omega
  obtain ⟨n, hn⟩ := (isPGroup_of_isElemAbelian hEel).exists_card_eq
  have hn3 : 3 ≤ n := by
    by_contra hlt
    have : 3 ^ n ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime
    (G := (B ⊔ 𝒟.comap (MulAut.conj : S →* MulAut S) : Subgroup S)) 3 (n := 3)
    (by rw [hn]; exact pow_dvd_pow 3 hn3)
  refine ⟨K.map (B ⊔ 𝒟.comap (MulAut.conj : S →* MulAut S) : Subgroup S).subtype,
    isElemAbelian_of_le (Subgroup.map_subtype_le K) hEel, ?_⟩
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hK]
  norm_num

theorem AutDatum.exists_central_nine [IsSimpleGroup S] (h : AutDatum S c L 𝒟)
    (hinn : 𝒟 ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner S) :
    ∃ P D' : Subgroup S, IsPGroup 3 P ∧ 81 ≤ Nat.card P ∧ D' ≤ P ∧ CFSG.Open.IsElemAbelian 3 D' ∧
      Nat.card D' = 9 ∧ ∀ x ∈ D', ∀ y ∈ P, x * y = y * x := by
  obtain ⟨P₀, hP₀le, hP₀, hP₀27⟩ := h.exists_fixed_pGroup
  have hZ := h.center_eq_bot
  have hDSel : CFSG.Open.IsElemAbelian 3 (𝒟.comap (MulAut.conj : S →* MulAut S)) :=
    isElemAbelian_comap_conj hZ h.comm h.pow_three
  have hDS9 : Nat.card (𝒟.comap (MulAut.conj : S →* MulAut S)) = 9 :=
    (card_comap_conj hZ hinn).trans h.card
  have hcomm : ∀ a ∈ P₀, ∀ d ∈ 𝒟.comap (MulAut.conj : S →* MulAut S), a * d = d * a :=
    fun a ha d hd =>
      Subgroup.mem_centralizer_iff.mp (comap_conj_le_centralizer 𝒟 L hd) a (hP₀le ha)
  have hDSc : ∀ d ∈ 𝒟.comap (MulAut.conj : S →* MulAut S),
      ∀ d' ∈ 𝒟.comap (MulAut.conj : S →* MulAut S), d * d' = d' * d := fun d hd d' hd' =>
    congrArg Subtype.val (isMulCommutative_iff.mp hDSel.1 ⟨d, hd⟩ ⟨d', hd'⟩)
  refine ⟨P₀ ⊔ 𝒟.comap (MulAut.conj : S →* MulAut S), 𝒟.comap (MulAut.conj : S →* MulAut S),
    isPGroup_sup hP₀ (isPGroup_of_isElemAbelian hDSel) hcomm, ?_, le_sup_right, hDSel, hDS9, ?_⟩
  · have := card_mul_nine_le h hinn hP₀le
    omega
  · intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hcomm hy
    exact Commute.mul_right (hcomm a ha x hx).symm (hDSc x hx b hb)

theorem outerAutDatum_of_elemAbelian [IsSimpleGroup S]
    (hr : ∀ E : Subgroup S, CFSG.Open.IsElemAbelian 3 E → Nat.card E ≤ 9) : OuterAutDatum S := by
  intro c L 𝒟 h
  by_contra hne
  push Not at hne
  obtain ⟨E, hE, hE27⟩ := h.exists_elemAbelian_27 fun φ hφ => hne φ hφ
  have := hr E hE
  omega

theorem noAutDatum_of_out_card [IsSimpleGroup S]
    (hout : ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S))
    (h81 : ¬ 81 ∣ Nat.card S) : NoAutDatum S := by
  intro c L 𝒟 h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, D', hP, hP81, -, -, -, -⟩ :=
    h.exists_central_nine (le_inner_of_not_dvd h.pow_three hout)
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hn4 : 4 ≤ n := by
    by_contra hlt
    have : 3 ^ n ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  apply h81
  have h1 : 3 ^ 4 ∣ Nat.card P := by rw [hn]; exact pow_dvd_pow 3 hn4
  simpa using h1.trans (Subgroup.card_subgroup_dvd_card P)

theorem noAutDatum_of_out_sylow [IsSimpleGroup S]
    (hout : ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S))
    (h243 : ¬ 243 ∣ Nat.card S)
    (hZ : ∀ P D' : Subgroup S, IsPGroup 3 P → Nat.card P = 81 → D' ≤ P →
      CFSG.Open.IsElemAbelian 3 D' → (∀ x ∈ D', ∀ y ∈ P, x * y = y * x) → Nat.card D' ≤ 3) :
    NoAutDatum S := by
  intro c L 𝒟 h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, D', hP, hP81, hD'P, hD'el, hD'9, hD'c⟩ :=
    h.exists_central_nine (le_inner_of_not_dvd h.pow_three hout)
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hn4 : 4 ≤ n := by
    by_contra hlt
    have : 3 ^ n ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hn4' : n = 4 := by
    by_contra hne
    apply h243
    have h1 : 3 ^ 5 ∣ Nat.card P := by rw [hn]; exact pow_dvd_pow 3 (by omega)
    simpa using h1.trans (Subgroup.card_subgroup_dvd_card P)
  have hP81' : Nat.card P = 81 := by rw [hn, hn4']; norm_num
  have := hZ P D' hP hP81' hD'P hD'el hD'c
  omega

end Inner

end CFSG.RankThree.PartTwo.Sec19.SimsC198
