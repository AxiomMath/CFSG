module

public import CFSG.RankThree.PartOne.S12.Sec1511Y4
public import CFSG.RankThree.PartOne.AUTSL.Narrow
public import CFSG.RankThree.PartOne.S12.Sec1511Y3
public import CFSG.RankThree.PartOne.S12.Sec15BorelTits

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.ABGLocalTools StrongP

namespace Sec1511

section Core

variable {X : Type} [Group X] [Finite X]

theorem y4_coreE
    (hBTE : AUTSL.KF1511BTE)
    {t : Assembly.LowTwoRank.StatedLieTag} {n f : ℕ} (hmodel : Blueprint.LieModel X t n 2 f)
    (ht : (t = .PSL ∧ n = 4) ∨ (t = .PSp ∧ n = 3) ∨ (t = .POmegaMinus ∧ n = 4))
    {Q : Type} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q) (ρ : Q →* MulAut X)
    {S B E : Subgroup X} (hS1 : S ≠ ⊥) (hS2 : IsPGroup 2 ↥S)
    (hSρ : ∀ q, S.map (ρ q).toMonoidHom = S)
    (hmax : ∀ U : Subgroup X, IsPGroup 2 ↥U → (∀ q, U.map (ρ q).toMonoidHom = U) →
      B ≤ Subgroup.normalizer (U : Set X) → U ≤ S)
    (hEel : IsElementaryAbelian 5 ↥E) (hE125 : Nat.card ↥E = 125) (hBE : B ≤ E)
    (hB25 : Nat.card ↥B = 25)
    (hBS : B ≤ Subgroup.normalizer (S : Set X))
    {α : MulAut X} (hαS : S.map α.toMonoidHom = S) (hαB : B.map α.toMonoidHom = B)
    (hα3 : ∀ b ∈ B, (α ^ 3) b = b) (hα1 : ∃ b ∈ B, α b ≠ b)
    (hBQ : ∀ q, ∀ b ∈ B, b⁻¹ * ρ q b ∈ S) :
    E ≤ Subgroup.normalizer (S : Set X) ∧ ∀ q, ∀ e ∈ E, e⁻¹ * ρ q e ∈ S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJρ : ∀ q, (Subgroup.normalizer (S : Set X)).map (ρ q).toMonoidHom =
      Subgroup.normalizer (S : Set X) := fun q => by
    rw [Subgroup.map_equiv_normalizer_eq, hSρ q]
  have hcore : Open.pCoreOf 2 (Subgroup.normalizer (S : Set X)) = S := by
    apply le_antisymm
    · apply hmax _ (LieType.BorelTits.pCoreOf_isPGroup 2 _)
      · intro q
        have h1 := LieType.BorelTits.pCoreOf_map_mulEquiv 2 (ρ q) (Subgroup.normalizer (S : Set X))
        rw [hJρ q] at h1
        exact h1.symm
      · exact hBS.trans (LieType.BorelTits.le_normalizer_pCoreOf 2 _)
    · exact LieType.BorelTits.le_pCoreOf_normalizer 2 S hS2
  have htT : t ≠ .Tits := by
    rcases ht with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide
  obtain ⟨hJtop, S₀, hS₀, -⟩ := borelTits_normalizer_parabolic Nat.prime_two hmodel hS1 hS2 hcore
  exact hBTE X t n f hmodel ht S hS1 hS2 hcore hJtop ⟨S₀, hS₀ htT⟩ E hEel hE125 B hBE hBS hB25 α hαS
    hαB hα3 hα1 Q ρ hQ hSρ hBQ

end Core

section GLevel

variable {G : Type} [Group G] [Finite G]

theorem lemmaY4E
    (hBTE : AUTSL.KF1511BTE)
    {E I N Y' P R O : Subgroup G} (hNI : N = Subgroup.normalizer (I : Set G))
    (hS : Setting 5 E N) (hY1 : Y1Out 5 E N Y' P) (hY2 : Y2Out 5 N Y' P (P ⊓ E) O)
    (hY3 : Y3Out N R (P ⊓ E) O) (hEI : E ≤ I) (hE125 : Nat.card ↥E = 125)
    (hR2 : IsPGroup 2 ↥R) (hRn : ∀ y ∈ Y', ∀ r ∈ R, y * r * y⁻¹ ∈ R)
    (hNR : Subgroup.normalizer (R : Set G) ≤ Y')
    (hchar : ∀ y ∈ Y', (∀ r ∈ R, y * r = r * y) → y ∈ R)
    (hBN : Subgroup.normalizer ((P ⊓ E : Subgroup G) : Set G) ≤ N)
    {t : Assembly.LowTwoRank.StatedLieTag} {n f : ℕ} (hmodel : Blueprint.LieModel ↥I t n 2 f)
    (ht : (t = .PSL ∧ n = 4) ∨ (t = .PSp ∧ n = 3) ∨ (t = .POmegaMinus ∧ n = 4)) :
    False := by
  classical
  subst hNI
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set B : Subgroup G := P ⊓ E with hB
  have hBI : B ≤ I := inf_le_right.trans hEI
  have hBP : B ≤ P := inf_le_left
  have hPY : P ≤ Y' := hY1.syl.1
  have hBY : B ≤ Y' := hBP.trans hPY
  have hRN : R ≤ Subgroup.normalizer (I : Set G) := hY3.RN
  have hIN : I ≤ Subgroup.normalizer (I : Set G) := Subgroup.le_normalizer
  have hNormR : ∀ y ∈ Y', y ∈ Subgroup.normalizer (R : Set G) := fun y hy => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨fun hx => hRn y hy x hx, fun hx => by
      have := hRn y⁻¹ (Y'.inv_mem hy) _ hx
      simpa [mul_assoc] using this⟩
  obtain ⟨g, hgY, hgB, hg3, hg1⟩ := hY2.three
  have hgI : g ∈ Subgroup.normalizer (I : Set G) := hBN hgB
  let ρ : ↥R →* MulAut ↥I := I.normalizerMonoidHom.comp (Subgroup.inclusion hRN)
  have hρ : ∀ (r : ↥R) (x : ↥I), ((ρ r x : ↥I) : G) = (r : G) * x * (r : G)⁻¹ := fun r x => rfl
  let α : MulAut ↥I := I.normalizerMonoidHom ⟨g, hgI⟩
  have hα : ∀ x : ↥I, ((α x : ↥I) : G) = g * x * g⁻¹ := fun x => rfl
  let S : Subgroup ↥I := (R ⊓ I).subgroupOf I
  let BX : Subgroup ↥I := B.subgroupOf I
  have hxS : ∀ x : ↥I, x ∈ S ↔ (x : G) ∈ R := fun x => by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
  have hxB : ∀ x : ↥I, x ∈ BX ↔ (x : G) ∈ B := fun x => Subgroup.mem_subgroupOf
  have hS1 : S ≠ ⊥ := by
    intro hbot
    have hBR : ∀ b ∈ B, b ∈ R := by
      intro b hb
      refine hchar b (hBY hb) fun r hr => ?_
      have hbI : b ∈ I := hBI hb
      have hbinv : b⁻¹ ∈ I := I.inv_mem hbI
      have h1 : r * b⁻¹ * r⁻¹ ∈ I := (Subgroup.mem_normalizer_iff.1 (hRN hr) b⁻¹).1 hbinv
      have hcI : b * r * b⁻¹ * r⁻¹ ∈ I := by
        have : b * r * b⁻¹ * r⁻¹ = b * (r * b⁻¹ * r⁻¹) := by group
        rw [this]
        exact I.mul_mem hbI h1
      have hcR : b * r * b⁻¹ * r⁻¹ ∈ R := R.mul_mem (hRn b (hBY hb) r hr) (R.inv_mem hr)
      have hmem : (⟨b * r * b⁻¹ * r⁻¹, hcI⟩ : ↥I) ∈ S := (hxS _).2 hcR
      rw [hbot, Subgroup.mem_bot] at hmem
      have h2 : b * r * b⁻¹ * r⁻¹ = 1 := congrArg Subtype.val hmem
      calc b * r = b * r * b⁻¹ * r⁻¹ * (r * b) := by group
        _ = r * b := by rw [h2, one_mul]
    have h2 : IsPGroup 2 ↥B := hR2.to_le (fun b hb => hBR b hb)
    exact not_five_dvd_card_of_isPGroup_two h2 (by rw [hY2.card]; norm_num)
  have hS2 : IsPGroup 2 ↥S := (hR2.to_le (inf_le_left : R ⊓ I ≤ R)).comap_subtype
  have hSρ : ∀ q, S.map (ρ q).toMonoidHom = S := fun q => by
    refine map_eq_of_forall_iff fun x => ?_
    rw [hxS, hxS, hρ]
    exact Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer q.2) (x : G)
  have hmax : ∀ U : Subgroup ↥I, IsPGroup 2 ↥U → (∀ q, U.map (ρ q).toMonoidHom = U) →
      BX ≤ Subgroup.normalizer (U : Set ↥I) → U ≤ S := by
    intro U hU2 hUρ hBU
    set UG : Subgroup G := U.map I.subtype with hUG
    have hUG2 : IsPGroup 2 ↥UG := hU2.map I.subtype
    have hRU : R ≤ Subgroup.normalizer (UG : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      rintro r hr _ ⟨u, hu, rfl⟩
      have h1 : ρ ⟨r, hr⟩ u ∈ U := by
        rw [← hUρ ⟨r, hr⟩]
        exact ⟨u, hu, rfl⟩
      exact ⟨ρ ⟨r, hr⟩ u, h1, hρ ⟨r, hr⟩ u⟩
    have hRsup : IsPGroup 2 ↥(R ⊔ UG) := hR2.to_sup_of_normal_right' hUG2 hRU
    have hBUG : B ≤ Subgroup.normalizer (UG : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      rintro b hb _ ⟨u, hu, rfl⟩
      have hbI : b ∈ I := hBI hb
      have h1 := (Subgroup.mem_normalizer_iff.1 (hBU ((hxB ⟨b, hbI⟩).2 hb)) u).1 hu
      exact ⟨_, h1, rfl⟩
    have hBsup : B ≤ Subgroup.normalizer ((R ⊔ UG : Subgroup G) : Set G) := fun b hb =>
      Subgroup.inf_normalizer_le_normalizer_sup R UG ⟨hNormR b (hBY hb), hBUG hb⟩
    have hEq : R ⊔ UG = R := hY3.maximal _ hRsup le_sup_left hBsup
    have hUGR : UG ≤ R := le_sup_right.trans hEq.le
    intro u hu
    exact (hxS u).2 (hUGR ⟨u, hu, rfl⟩)
  have hBX25 : Nat.card ↥BX = 25 := by
    rw [← hY2.card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBI).toEquiv
  have hBXS : BX ≤ Subgroup.normalizer (S : Set ↥I) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hxS, hxS]
    exact Subgroup.mem_normalizer_iff.1 (hNormR (x : G) (hBY ((hxB x).1 hx))) (y : G)
  have hαS : S.map α.toMonoidHom = S := by
    refine map_eq_of_forall_iff fun y => ?_
    rw [hxS, hxS, hα]
    exact Subgroup.mem_normalizer_iff.1 (hNormR g hgY) (y : G)
  have hαB : BX.map α.toMonoidHom = BX := by
    refine map_eq_of_forall_iff fun y => ?_
    rw [hxB, hxB, hα]
    exact Subgroup.mem_normalizer_iff.1 hgB (y : G)
  have hα3pow : ∀ x : ↥I, (((α ^ 3) x : ↥I) : G) = g ^ 3 * x * (g ^ 3)⁻¹ := by
    intro x
    have : α ^ 3 = I.normalizerMonoidHom ((⟨g, hgI⟩ : ↥(Subgroup.normalizer (I : Set G))) ^ 3) := by
      show (I.normalizerMonoidHom ⟨g, hgI⟩) ^ 3 = _
      rw [map_pow]
    rw [this]
    rfl
  have hα3 : ∀ b ∈ BX, (α ^ 3) b = b := by
    intro b hb
    apply Subtype.ext
    rw [hα3pow]
    have := Subgroup.mem_centralizer_iff.1 hg3 (b : G) ((hxB b).1 hb)
    rw [← this]
    group
  have hα1 : ∃ b ∈ BX, α b ≠ b := by
    have h1 := hg1
    rw [Subgroup.mem_centralizer_iff] at h1
    push Not at h1
    obtain ⟨b, hb, hne⟩ := h1
    refine ⟨⟨b, hBI hb⟩, (hxB _).2 hb, fun h => hne ?_⟩
    have h2 : g * b * g⁻¹ = b := by
      have := congrArg Subtype.val h
      rw [hα] at this
      exact this
    calc b * g = g * b * g⁻¹ * g := by rw [h2]
      _ = g * b := by group
  have hBQ : ∀ q : ↥R, ∀ b ∈ BX, b⁻¹ * ρ q b ∈ S := by
    intro q b hb
    rw [hxS]
    have hbY : (b : G) ∈ Y' := hBY ((hxB b).1 hb)
    have h1 := hRn (b : G)⁻¹ (Y'.inv_mem hbY) (q : G) q.2
    have : (((b⁻¹ * ρ q b : ↥I)) : G) = (b : G)⁻¹ * (q : G) * (b : G)⁻¹⁻¹ * (q : G)⁻¹ := by
      rw [Subgroup.coe_mul, InvMemClass.coe_inv, hρ]
      group
    rw [this]
    exact R.mul_mem h1 (R.inv_mem q.2)
  have hEel : IsElementaryAbelian 5 ↥E := hS.Eel
  let EX : Subgroup ↥I := E.subgroupOf I
  have hEXel : IsElementaryAbelian 5 ↥EX := by
    have := hEel
    exact IsElementaryAbelian.subgroupOf hEI
  have hEX125 : Nat.card ↥EX = 125 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEI).toEquiv]
    exact hE125
  have hBEX : BX ≤ EX := fun x hx =>
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.1 ((hxB x).1 hx)).2
  obtain ⟨-, hEQ⟩ := y4_coreE (X := ↥I) hBTE hmodel ht hR2 ρ hS1 hS2 hSρ hmax hEXel hEX125 hBEX
    hBX25 hBXS hαS hαB hα3 hα1 hBQ
  have hEY : E ≤ Y' := by
    intro e he
    have heI : e ∈ I := hEI he
    have hconj : ∀ r ∈ R, e⁻¹ * r * e⁻¹⁻¹ ∈ R := by
      intro r hr
      have h1 := hEQ ⟨r, hr⟩ ⟨e, heI⟩ (Subgroup.mem_subgroupOf.2 he)
      have h2 : (((⟨e, heI⟩ : ↥I)⁻¹ * ρ ⟨r, hr⟩ ⟨e, heI⟩ : ↥I) : G) ∈ R := (hxS _).1 h1
      rw [Subgroup.coe_mul, hρ] at h2
      have h3 : e⁻¹ * r * e * r⁻¹ ∈ R := by
        have : e⁻¹ * r * e * r⁻¹ =
            ((((⟨e, heI⟩ : ↥I)⁻¹ : ↥I)) : G) * (r * e * r⁻¹) := by
          simp [mul_assoc]
        rw [this]
        exact h2
      have h4 := R.mul_mem h3 hr
      simpa [mul_assoc] using h4
    have hd : e⁻¹ ∈ Subgroup.normalizer (R : Set G) := mem_normalizer_of_conj_le hconj
    have := (Subgroup.normalizer (R : Set G)).inv_mem hd
    simpa using hNR this
  have hE53 : Nat.card ↥E = 5 ^ 3 := by rw [hE125]; norm_num
  have hEdvd : 5 ^ 3 ∣ Nat.card ↥Y' := by
    have := Subgroup.card_dvd_of_le hEY
    rwa [hE53] at this
  have hPcard : Nat.card ↥P = 25 := by rw [hY2.PB]; exact hY2.card
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf 5 P Y' := CFSG.ABGLocalTools.isSylowOf_iff.2 hY1.syl
  have h1 := hPsyl.card_eq
  have h2 : 3 ≤ (Nat.card ↥Y').factorization 5 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_five Nat.card_pos.ne').1 hEdvd
  have h3 : 5 ^ 3 ≤ Nat.card ↥P := by
    rw [h1]
    exact Nat.pow_le_pow_right (by norm_num) h2
  rw [hPcard] at h3
  norm_num at h3

end GLevel

end Sec1511

end CFSG.RankThree.PartOne
