module

public import CFSG.RankThree.PartTwo.Sec12.Item125Lcbar
import CFSG.RankThree.PartTwo.KFacts.KS12Moves
import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.RankThree.PartTwo.Sec12.Item123Inputs

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open scoped Pointwise

structure Sec12StdBar (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G)
    (L : Subgroup G) : Prop extends PartTwoStanding G where
  partTwoF_eq : partTwoF G = partTwoE G
  isE27 : Late.IsE27 A
  mem_A : c ∈ A
  ne_one : c ≠ 1
  mem_thetaComponentsAt : L ∈ thetaComponentsAt 3 c
  mem_L : c ∈ L
  card_B : Nat.card (A ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 9
  sup_eq : (A ⊓ Sec4.thetaQuotCentralizer L) ⊔ (A ⊓ L) = A
  exists_sylow : ∃ P : Subgroup G, IsSylowOf 3 P
      (Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)) ∧
    ¬ A ⊓ Sec4.thetaQuotCentralizer L ≤ (Subgroup.center P).map P.subtype

section Theta

variable {G : Type} [Group G] [Finite G]

theorem conj_mem_inSubgroup_theta {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) {t : G}
    (ht : t ∈ inSubgroup (aschbacherSolvableCore 3) L) :
    g * t * g⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  obtain ⟨t', ht', rfl⟩ := ht
  set σ := L.normalizerMonoidHom ⟨g, hg⟩
  have h := Sec4.map_aschbacherSolvableCore σ
  have hmem : σ t' ∈ aschbacherSolvableCore 3 L := h ▸ ⟨t', ht', rfl⟩
  exact ⟨σ t', hmem, rfl⟩

theorem conj_mem_thetaQuotCentralizer {L : Subgroup G} {g x : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (hx : x ∈ Sec4.thetaQuotCentralizer L) :
    g * x * g⁻¹ ∈ Sec4.thetaQuotCentralizer L := by
  obtain ⟨hxN, hxl⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp hx
  refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨?_, fun l hl => ?_⟩
  · exact mul_mem (mul_mem hg hxN) (inv_mem hg)
  · have hl' : g⁻¹ * l * g ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) l).mp hl
      simpa using this
    have h1 := conj_mem_inSubgroup_theta hg (hxl _ hl')
    have e : g * ((g⁻¹ * l * g)⁻¹ * (x * (g⁻¹ * l * g) * x⁻¹)) * g⁻¹ =
        l⁻¹ * (g * x * g⁻¹ * l * (g * x * g⁻¹)⁻¹) := by group
    rwa [e] at h1

theorem inf_inSubgroup_theta_eq_bot {L A : Subgroup G} (hA : IsPGroup 3 A) :
    A ⊓ inSubgroup (aschbacherSolvableCore 3) L = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA
  have hcard : Nat.card (inSubgroup (aschbacherSolvableCore 3) L) =
      Nat.card (aschbacherSolvableCore 3 L) :=
    Subgroup.card_map_of_injective L.subtype_injective
  refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
  rw [hk, hcard]
  exact Nat.Coprime.pow_left k
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr three_not_dvd_card_aschbacherSolvableCore)

theorem commute_of_mem_thetaQuotCentralizer {L A : Subgroup G} (hA : IsPGroup 3 A)
    {g b : G} (hgL : g ∈ L) (hgA : g ∈ Subgroup.normalizer (A : Set G)) (hbA : b ∈ A)
    (hb : b ∈ Sec4.thetaQuotCentralizer L) : g * b = b * g := by
  have h1 : (g⁻¹)⁻¹ * (b * g⁻¹ * b⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) L :=
    (Sec6.mem_thetaQuotCentralizer_iff.mp hb).2 _ (L.inv_mem hgL)
  have h2 : (g⁻¹)⁻¹ * (b * g⁻¹ * b⁻¹) ∈ A := by
    rw [inv_inv, ← mul_assoc, ← mul_assoc]
    exact A.mul_mem ((Subgroup.mem_normalizer_iff.mp hgA b).mp hbA) (A.inv_mem hbA)
  have h3 : (g⁻¹)⁻¹ * (b * g⁻¹ * b⁻¹) ∈ (⊥ : Subgroup G) := by
    rw [← inf_inSubgroup_theta_eq_bot hA (L := L)]
    exact ⟨h2, h1⟩
  rw [Subgroup.mem_bot, inv_inv] at h3
  calc g * b = (g * (b * g⁻¹ * b⁻¹)) * (b * g) := by group
    _ = b * g := by rw [h3, one_mul]

theorem mem_thetaQuotCentralizer_of_central {L : Subgroup G} {c : G} (hcL : c ∈ L)
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) : c ∈ Sec4.thetaQuotCentralizer L := by
  refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨Subgroup.le_normalizer hcL, fun l hl => ?_⟩
  have hcl : c * l = l * c := (Subgroup.mem_centralizer_singleton_iff.mp (hLc hl)).symm
  rw [hcl, mul_inv_cancel_right, inv_mul_cancel]
  exact Subgroup.one_mem _

theorem mem_normalizer_inf_thetaQuotCentralizer {A L : Subgroup G} {g : G}
    (hgA : g ∈ Subgroup.normalizer (A : Set G)) (hgL : g ∈ Subgroup.normalizer (L : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) : Set G) :=
  Subgroup.mem_normalizer_fintype fun x hx =>
    ⟨(Subgroup.mem_normalizer_iff.mp hgA x).mp hx.1, conj_mem_thetaQuotCentralizer hgL hx.2⟩

end Theta

section Bar

variable {G : Type} [Group G] [Finite G]

theorem autIn_le_transvectionGroup_bar {A L P : Subgroup G} {c : G} (hA : Late.IsE27 A)
    (hcA : c ∈ A) (hc1 : c ≠ 1) (hcL : c ∈ L) (hLc : L ≤ Subgroup.centralizer ({c} : Set G))
    (hB9 : Nat.card (A ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 9)
    (hsup : (A ⊓ Sec4.thetaQuotCentralizer L) ⊔ (A ⊓ L) = A)
    (hAL : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hPH : P ≤ Subgroup.normalizer (A : Set G) ⊓
      Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hP3 : IsPGroup 3 P) (hPL : P ≤ Subgroup.normalizer (L : Set G)) :
    Sec4.autIn P A ≤ transvectionGroup A ⟨c, hcA⟩ := by
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hexpA : ∀ x ∈ A, x ^ 3 = 1 := hA.1.2
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hexpA c hcA) hc1
  have hcB : c ∈ A ⊓ Sec4.thetaQuotCentralizer L :=
    ⟨hcA, mem_thetaQuotCentralizer_of_central hcL hLc⟩
  have hcAL : c ∈ A ⊓ L := ⟨hcA, hcL⟩
  intro σ hσ
  obtain ⟨g, hN, hgP, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
  obtain ⟨k, hk⟩ := hP3 ⟨g, hgP⟩
  have hg : g ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hgc : g * c * g⁻¹ ∈ Subgroup.zpowers c :=
    (Subgroup.mem_normalizer_iff.mp (hPH hgP).2 c).mp (Subgroup.mem_zpowers c)
  have hgc' := commute_of_conj_mem_zpowers hc3 hgc hg
  have hgA := (hPH hgP).1
  have hgL := hPL hgP
  have hgB := mem_normalizer_inf_thetaQuotCentralizer hgA hgL
  have hgAL : g ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp hgA y,
      Subgroup.mem_normalizer_iff.mp hgL y]
  have hB := conj_mul_inv_mem_zpowers (D := A ⊓ Sec4.thetaQuotCentralizer L)
    (fun x hx y hy => hcommA x hx.1 y hy.1) (fun x hx => hexpA x hx.1) hB9 hcB hc1 hgB hgc' hg
  have hAL' := conj_mul_inv_mem_zpowers (D := A ⊓ L) (fun x hx y hy => hcommA x hx.1 y hy.1)
    (fun x hx => hexpA x hx.1) hAL hcAL hc1 hgAL hgc' hg
  refine ⟨Subtype.ext ?_, fun x => ?_⟩
  · rw [Sec4.normalizerMonoidHom_apply_coe]
    change g * c * g⁻¹ = c
    rw [hgc', mul_inv_cancel_right]
  · rw [mem_zpowers_subtype_iff, Subgroup.coe_mul, Sec4.normalizerMonoidHom_apply_coe,
      Subgroup.coe_inv]
    have hBN : A ⊓ Sec4.thetaQuotCentralizer L ≤
        Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) := fun b hb => by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        rw [hcommA b hb.1 y hy.1, mul_inv_cancel_right]
        exact hy
      · intro hy
        have hyA : y ∈ A := by
          have := A.mul_mem (A.mul_mem (A.inv_mem hb.1) hy.1) hb.1
          simpa [mul_assoc] using this
        rwa [hcommA b hb.1 y hyA, mul_inv_cancel_right] at hy
    have hx : (x : G) ∈ ((A ⊓ Sec4.thetaQuotCentralizer L ⊔ A ⊓ L : Subgroup G) : Set G) := by
      rw [hsup]
      exact x.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hBN] at hx
    obtain ⟨b, hb, y, hy, hxy⟩ := hx
    rw [← hxy]
    have hgy : g * y * g⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hgA y).mp hy.1
    have h1 : b⁻¹ * (g * y * g⁻¹) = (g * y * g⁻¹) * b⁻¹ :=
      hcommA _ (A.inv_mem hb.1) _ hgy
    have h2 : b⁻¹ * y⁻¹ = y⁻¹ * b⁻¹ := hcommA _ (A.inv_mem hb.1) _ (A.inv_mem hy.1)
    have e : g * (b * y) * g⁻¹ * (b * y)⁻¹ =
        (g * b * g⁻¹) * ((g * y * g⁻¹) * (y⁻¹ * b⁻¹)) := by group
    have e' : (g * y * g⁻¹) * (y⁻¹ * b⁻¹) = b⁻¹ * ((g * y * g⁻¹) * y⁻¹) := by
      rw [← h2, ← mul_assoc, ← h1, mul_assoc]
    rw [e, e', ← mul_assoc]
    exact Subgroup.mul_mem _ (hB b hb) (hAL' y hy)

theorem nine_le_card_autIn_bar {A L : Subgroup G} {c : G} (hA : Late.IsE27 A) (hcA : c ∈ A)
    {P : Subgroup G} (hP : IsSylowOf 3 P (Subgroup.normalizer (A : Set G) ⊓
      Subgroup.normalizer (Subgroup.zpowers c : Set G)))
    (hPB : ¬ A ⊓ Sec4.thetaQuotCentralizer L ≤ (Subgroup.center P).map P.subtype)
    (hPAL : ∃ g ∈ P ⊓ L, ∃ y ∈ A ⊓ L, g * y * g⁻¹ ≠ y) :
    9 ≤ Nat.card (Sec4.autIn P A) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hexpA : ∀ x ∈ A, x ^ 3 = 1 := hA.1.2
  have hA3 : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hexpA x x.2)⟩
  have hPW : P ≤ Subgroup.normalizer (A : Set G) := hP.le.trans inf_le_left
  have hAWH : A ≤ Subgroup.normalizer (A : Set G) ⊓
      Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    refine fun x hx => Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer hx, ?_⟩
    exact mem_normalizer_zpowers_of_commute (hcommA x hx c hcA)
  have hPA : P ⊔ A = P := hP.eq_of_le le_sup_left (sup_le hP.le hAWH)
    (hP.isPGroup.to_sup_of_normal_right' hA3 hPW)
  have hAP : A ≤ P := hPA ▸ le_sup_right
  obtain ⟨b, hb₀, hbZ⟩ := Set.not_subset.mp hPB
  have hb := Subgroup.mem_inf.mp hb₀
  have hbP : b ∈ P := hAP hb.1
  have hbZ' : (⟨b, hbP⟩ : P) ∉ Subgroup.center P := fun hc => hbZ ⟨_, hc, rfl⟩
  rw [Subgroup.mem_center_iff] at hbZ'
  push Not at hbZ'
  obtain ⟨g₂, hg₂⟩ := hbZ'
  have hg₂b : (g₂ : G) * b * (g₂ : G)⁻¹ ≠ b := by
    intro he
    apply hg₂
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    calc (g₂ : G) * b = ((g₂ : G) * b * (g₂ : G)⁻¹) * g₂ := by group
      _ = b * g₂ := by rw [he]
  obtain ⟨g₁, ⟨hg₁P, hg₁L⟩, y, hy, hg₁y⟩ := hPAL
  set τ₁ := A.normalizerMonoidHom ⟨g₁, hPW hg₁P⟩ with hτ₁
  set τ₂ := A.normalizerMonoidHom ⟨g₂, hPW g₂.2⟩ with hτ₂
  have hτ₁S : τ₁ ∈ Sec4.autIn P A := Sec4.mem_autIn_iff.mpr ⟨g₁, _, hg₁P, rfl⟩
  have hτ₂S : τ₂ ∈ Sec4.autIn P A := Sec4.mem_autIn_iff.mpr ⟨g₂, _, g₂.2, rfl⟩
  have hτ₁1 : τ₁ ≠ 1 := by
    intro h1
    apply hg₁y
    have := congrArg (fun σ : MulAut A => ((σ ⟨y, hy.1⟩ : A) : G)) h1
    simpa [hτ₁, Sec4.normalizerMonoidHom_apply_coe] using this
  have hτ₁B : ∀ n : ℤ, (τ₁ ^ n) ⟨b, hb.1⟩ = ⟨b, hb.1⟩ := by
    have hfix : τ₁ ⟨b, hb.1⟩ = ⟨b, hb.1⟩ := by
      apply Subtype.ext
      rw [Sec4.normalizerMonoidHom_apply_coe]
      have hcomm : g₁ * b = b * g₁ :=
        commute_of_mem_thetaQuotCentralizer hA3 hg₁L (hPW hg₁P) hb.1 hb.2
      rw [hcomm, mul_inv_cancel_right]
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ n ih => rw [zpow_add_one, MulAut.mul_apply, hfix, ih]
    | pred n ih =>
      rw [zpow_sub_one, MulAut.mul_apply]
      have : τ₁⁻¹ ⟨b, hb.1⟩ = ⟨b, hb.1⟩ := by
        conv_lhs => rw [← hfix]
        exact MulEquiv.symm_apply_apply _ _
      rw [this, ih]
  have hτ₂B : τ₂ ⟨b, hb.1⟩ ≠ ⟨b, hb.1⟩ := by
    intro he
    apply hg₂b
    have := congrArg Subtype.val he
    simpa [hτ₂, Sec4.normalizerMonoidHom_apply_coe] using this
  have hS3 : IsPGroup 3 (Sec4.autIn P A) := by
    have h1 : IsPGroup 3 ((P ⊓ Subgroup.normalizer (A : Set G)).subgroupOf
        (Subgroup.normalizer (A : Set G))) :=
      (hP.isPGroup.to_le inf_le_left).comap_subtype
    exact h1.map _
  set S := Sec4.autIn P A
  set K := (Subgroup.zpowers τ₁).subgroupOf S
  have hKS : Subgroup.zpowers τ₁ ≤ S := Subgroup.zpowers_le.mpr hτ₁S
  have hKne : K ≠ ⊤ := by
    intro htop
    have : (⟨τ₂, hτ₂S⟩ : S) ∈ K := htop ▸ Subgroup.mem_top _
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp this)
    have hn' : τ₁ ^ n = τ₂ := hn
    apply hτ₂B
    rw [← hn']
    exact hτ₁B n
  have hcardK : Nat.card K = orderOf τ₁ := by
    rw [← Nat.card_zpowers]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKS).toEquiv
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hS3
  have hord3 : 3 ≤ orderOf τ₁ := by
    obtain ⟨j, hj⟩ := (hS3 ⟨τ₁, hτ₁S⟩)
    have hdvd : orderOf τ₁ ∣ 3 ^ j := by
      rw [← Subgroup.orderOf_mk τ₁ hτ₁S]
      exact orderOf_dvd_of_pow_eq_one hj
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    rcases i with _ | i
    · exact absurd (orderOf_eq_one_iff.mp (by simpa using hi)) hτ₁1
    · rw [hi, pow_succ]
      exact Nat.le_mul_of_pos_left 3 (by positivity)
  have hidx : 3 ≤ K.index := by
    have hdvd : K.index ∣ 3 ^ a := ha ▸ K.index_dvd_card
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    rcases i with _ | i
    · exact absurd (Subgroup.index_eq_one.mp (by simpa using hi)) hKne
    · rw [hi, pow_succ]
      exact Nat.le_mul_of_pos_left 3 (by positivity)
  calc 9 = 3 * 3 := by norm_num
    _ ≤ Nat.card K * K.index := Nat.mul_le_mul (hcardK ▸ hord3) hidx
    _ = Nat.card S := K.card_mul_index

theorem exists_fixed_mem_coset {D N : Subgroup G} (hD : IsPGroup 3 D) (hN : ¬ 3 ∣ Nat.card N)
    (y : G) (hinv : ∀ d ∈ D, ∀ n ∈ N, ∃ n' ∈ N, d * (y * n) * d⁻¹ = y * n') :
    ∃ n ∈ N, ∀ d ∈ D, d * (y * n) * d⁻¹ = y * n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set α : D →* MulAut G := MulAut.conj.comp D.subtype with hα
  set S : Set G := y • (N : Set G) with hS
  have hSinv : ∀ a : D, ∀ x ∈ S, α a x ∈ S := by
    rintro a _ ⟨n, hn, rfl⟩
    obtain ⟨n', hn', he⟩ := hinv a a.2 n hn
    refine ⟨n', hn', ?_⟩
    change y * n' = (a : G) * (y * n) * (a : G)⁻¹
    rw [he]
  have hcard : ¬ 3 ∣ Nat.card S := by
    rw [hS, Set.natCard_smul_set]
    exact hN
  obtain ⟨x, hxS, hx⟩ := CFSG.Semidihedral.Principal.CoprimeFixedPoint.exists_fixed_of_invariant
    3 hD α S hSinv hcard
  obtain ⟨n, hn, rfl⟩ := hxS
  exact ⟨n, hn, fun d hd => hx ⟨d, hd⟩⟩

omit [Finite G] in
theorem conj_pow_ne_of_conj_ne {x t : G} {j : ℕ} (hx : x ^ 3 ^ j = 1) (hxt : x * t * x⁻¹ ≠ t)
    {m : ℕ} (hm : ¬ 3 ∣ m) : x ^ m * t * (x ^ m)⁻¹ ≠ t := by
  intro he
  apply hxt
  have hcm : Commute (x ^ m) t := by
    change x ^ m * t = t * x ^ m
    calc x ^ m * t = (x ^ m * t * (x ^ m)⁻¹) * x ^ m := by group
      _ = t * x ^ m := by rw [he]
  rcases Nat.eq_zero_or_pos j with hj | hj
  · rw [hj, pow_zero, pow_one] at hx
    rw [hx]
    group
  have hcop : Nat.Coprime m (3 ^ j) :=
    Nat.Coprime.pow_right j ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm).symm
  have h1 : 1 < 3 ^ j := Nat.one_lt_pow (by omega) (by norm_num)
  obtain ⟨r, -, hr⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
  have hxr : (x ^ m) ^ r = x := by
    rw [← pow_mul, pow_eq_pow_mod (m * r) hx, hr, pow_one]
  have hc : Commute x t := hxr ▸ hcm.pow_left r
  change x * t * x⁻¹ = t
  rw [hc.eq, mul_inv_cancel_right]

theorem exists_threePart (x : G) :
    ∃ k m : ℕ, ¬ 3 ∣ m ∧ (x ^ m) ^ 3 ^ k = 1 ∧ orderOf x = 3 ^ k * m := by
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' 3 (by norm_num)
  refine ⟨k, m, hm, ?_, hn⟩
  rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]

theorem exists_moves_centralizing {A L : Subgroup G} (hA3 : IsPGroup 3 A)
    (hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {x t : G} (hxL : x ∈ L)
    (hxT : x ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G))
    (hx3 : IsPGroup 3 (Subgroup.zpowers x)) (ht : t ∈ A ⊓ L) (hxt : x * t * x⁻¹ ≠ t) :
    ∃ x' ∈ L, x' ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) ∧
      IsPGroup 3 (Subgroup.zpowers x') ∧ x' * t * x'⁻¹ ≠ t ∧
      ∀ b ∈ A ⊓ Sec4.thetaQuotCentralizer L, x' * b = b * x' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set T := A ⊓ L with hT
  set D := A ⊓ Sec4.thetaQuotCentralizer L with hD
  set N₀ := (Subgroup.normalizer (T : Set G) ⊓ L) ⊓ inSubgroup (aschbacherSolvableCore 3) L
    with hN₀
  have hD3 : IsPGroup 3 D := hA3.to_le inf_le_left
  have hN₀3 : ¬ 3 ∣ Nat.card N₀ := by
    intro h3
    apply three_not_dvd_card_aschbacherSolvableCore (G := L)
    have h1 : Nat.card N₀ ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) L) :=
      Subgroup.card_dvd_of_le inf_le_right
    rw [show Nat.card (inSubgroup (aschbacherSolvableCore 3) L) =
      Nat.card (aschbacherSolvableCore 3 L) from
        Subgroup.card_map_of_injective L.subtype_injective] at h1
    exact h3.trans h1
  have hDT : ∀ d ∈ D, d ∈ Subgroup.normalizer (T : Set G) := fun d hd =>
    Subgroup.mem_normalizer_fintype fun a ha => by
      rw [hcommA d hd.1 a ha.1, mul_inv_cancel_right]
      exact ha
  have hDL : ∀ d ∈ D, d ∈ Subgroup.normalizer (L : Set G) := fun d hd =>
    thetaQuotCentralizer_le_normalizer' L hd.2
  obtain ⟨n₀, hn₀, hfix⟩ := exists_fixed_mem_coset hD3 hN₀3 x fun d hd n hn => by
    refine ⟨x⁻¹ * (d * x * d⁻¹) * (d * n * d⁻¹), ?_, by group⟩
    have h1 : x⁻¹ * (d * x * d⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) L :=
      (Sec6.mem_thetaQuotCentralizer_iff.mp hd.2).2 x hxL
    have hdx : d * x * d⁻¹ ∈ Subgroup.normalizer (T : Set G) :=
      mul_mem (mul_mem (hDT d hd) hxT) (inv_mem (hDT d hd))
    have hdxL : d * x * d⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hDL d hd) x).mp hxL
    have hdn : d * n * d⁻¹ ∈ N₀ := by
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _
        (Subgroup.mul_mem _ (hDT d hd) (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hn).1).1)
          (Subgroup.inv_mem _ (hDT d hd)),
        (Subgroup.mem_normalizer_iff.mp (hDL d hd) n).mp
          (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hn).1).2⟩,
        conj_mem_inSubgroup_theta (hDL d hd) (Subgroup.mem_inf.mp hn).2⟩
    have hxinv : x⁻¹ * (d * x * d⁻¹) ∈ N₀ :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _
        (Subgroup.inv_mem _ hxT) hdx, L.mul_mem (L.inv_mem hxL) hdxL⟩, h1⟩
    exact N₀.mul_mem hxinv hdn
  set x₁ := x * n₀ with hx₁
  have hn₀' := Subgroup.mem_inf.mp hn₀
  have hn₀'' := Subgroup.mem_inf.mp hn₀'.1
  have hx₁L : x₁ ∈ L := L.mul_mem hxL hn₀''.2
  have hx₁T : x₁ ∈ Subgroup.normalizer (T : Set G) := Subgroup.mul_mem _ hxT hn₀''.1
  have hn₀T : ∀ a ∈ T, n₀ * a * n₀⁻¹ = a := by
    intro a ha
    have h1 : n₀ * a * n₀⁻¹ * a⁻¹ ∈ T :=
      T.mul_mem ((Subgroup.mem_normalizer_iff.mp hn₀''.1 a).mp ha) (T.inv_mem ha)
    have h2 : n₀ * a * n₀⁻¹ * a⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
      have h3 := conj_mem_inSubgroup_theta (Subgroup.le_normalizer ha.2)
        (Subgroup.inv_mem _ hn₀'.2)
      have e : n₀ * a * n₀⁻¹ * a⁻¹ = n₀ * (a * n₀⁻¹ * a⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hn₀'.2 h3
    have h4 : n₀ * a * n₀⁻¹ * a⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← inf_inSubgroup_theta_eq_bot (hA3.to_le inf_le_left) (L := L)]
      exact ⟨h1, h2⟩
    rw [Subgroup.mem_bot] at h4
    calc n₀ * a * n₀⁻¹ = (n₀ * a * n₀⁻¹ * a⁻¹) * a := by group
      _ = a := by rw [h4, one_mul]
  have hx₁act : ∀ k : ℕ, ∀ a ∈ T, x₁ ^ k * a * (x₁ ^ k)⁻¹ = x ^ k * a * (x ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro a _; simp
    | succ k ih =>
      intro a ha
      have hk : x ^ k * a * (x ^ k)⁻¹ ∈ T :=
        (Subgroup.mem_normalizer_iff.mp (pow_mem hxT k) a).mp ha
      calc x₁ ^ (k + 1) * a * (x₁ ^ (k + 1))⁻¹ = x₁ * (x₁ ^ k * a * (x₁ ^ k)⁻¹) * x₁⁻¹ := by
            rw [pow_succ']; group
        _ = x₁ * (x ^ k * a * (x ^ k)⁻¹) * x₁⁻¹ := by rw [ih a ha]
        _ = x * (n₀ * (x ^ k * a * (x ^ k)⁻¹) * n₀⁻¹) * x⁻¹ := by rw [hx₁]; group
        _ = x * (x ^ k * a * (x ^ k)⁻¹) * x⁻¹ := by rw [hn₀T _ hk]
        _ = x ^ (k + 1) * a * (x ^ (k + 1))⁻¹ := by rw [pow_succ']; group
  obtain ⟨k, m, hm, hx₂3, -⟩ := exists_threePart x₁
  obtain ⟨j, hj⟩ := hx3 ⟨x, Subgroup.mem_zpowers x⟩
  have hxj : x ^ 3 ^ j = 1 := by simpa using congrArg Subtype.val hj
  refine ⟨x₁ ^ m, L.pow_mem hx₁L m, pow_mem hx₁T m, fun g => ⟨k, ?_⟩, ?_, fun b hb => ?_⟩
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp g.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hi, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
      zpow_natCast, hx₂3, _root_.one_zpow]
    rfl
  · rw [hx₁act m t ht]
    exact conj_pow_ne_of_conj_ne hxj hxt hm
  · have hb' := hfix b hb
    have hcomm : Commute x₁ b := by
      change x₁ * b = b * x₁
      calc x₁ * b = (b * x₁ * b⁻¹) * b := by rw [hx₁, hb']
        _ = b * x₁ := by group
    exact (hcomm.pow_left m).eq

theorem card_inf_le_card_center_of_le_thetaQuotCentralizer {L B : Subgroup G}
    (hB3 : IsPGroup 3 B) (hBL : B ≤ Sec4.thetaQuotCentralizer L) :
    Nat.card (B ⊓ L : Subgroup G) ≤
      Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) := by
  set S : Subgroup L := (B ⊓ L).subgroupOf L with hS
  have hScard : Nat.card S = Nat.card (B ⊓ L : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hS3 : IsPGroup 3 S := by
    have h1 : IsPGroup 3 (B ⊓ L : Subgroup G) := hB3.to_le inf_le_left
    exact h1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L)
  have hmap : S.map π ≤ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 L) q
    have hxB : (x : G) ∈ B := (Subgroup.mem_subgroupOf.mp hx).1
    obtain ⟨t, ht, hte⟩ := (Sec6.mem_thetaQuotCentralizer_iff.mp (hBL hxB)).2 l l.2
    have h1 : l⁻¹ * (x * l * x⁻¹) ∈ aschbacherSolvableCore 3 L := by
      have : t = l⁻¹ * (x * l * x⁻¹) := Subtype.ext hte
      rw [← this]
      exact ht
    have h2 : π (x * l * x⁻¹) = π l := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq.mpr h1).symm
    rw [map_mul, map_mul, map_inv] at h2
    calc π l * π x = (π x * π l * (π x)⁻¹) * π x := by rw [h2]
      _ = π x * π l := by group
  have hinj : Set.InjOn π (S : Set L) := injOn_mk_of_isPGroup Nat.prime_three hS3
  have hcard : Nat.card (S.map π) = Nat.card S := by
    change Nat.card (↑(S.map π) : Set (L ⧸ aschbacherSolvableCore 3 L)) = Nat.card (S : Set L)
    rw [Subgroup.coe_map, Nat.card_image_of_injOn hinj]
  rw [← hScard, ← hcard]
  exact Subgroup.card_le_of_le hmap

theorem card_inf_eq_nine_bar {A L : Subgroup G} {c : G} (hA : Late.IsE27 A) (hcA : c ∈ A)
    (hc1 : c ≠ 1) (hcL : c ∈ L) (hLc : L ≤ Subgroup.centralizer ({c} : Set G))
    (hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3)
    (hB9 : Nat.card (A ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 9)
    (hsup : (A ⊓ Sec4.thetaQuotCentralizer L) ⊔ (A ⊓ L) = A) :
    Nat.card (A ⊓ L : Subgroup G) = 9 := by
  have hB3 : IsPGroup 3 (A ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) := fun x =>
    ⟨1, Subtype.ext (by simpa using hA.1.2 x x.2.1)⟩
  have hBL := card_inf_le_card_center_of_le_thetaQuotCentralizer hB3 inf_le_right (L := L)
  rw [hZ] at hBL
  have hA27 : Nat.card A = 27 := hA.2
  have hdvd : Nat.card (A ⊓ L : Subgroup G) ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hA27]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hA.1.2 c hcA) hc1
  have hcT : c ∈ A ⊓ L := ⟨hcA, hcL⟩
  have hcB : c ∈ A ⊓ Sec4.thetaQuotCentralizer L :=
    ⟨hcA, mem_thetaQuotCentralizer_of_central hcL hLc⟩
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases k
  · exfalso
    rw [pow_zero] at hk
    have h1 := (Subgroup.card_eq_one).mp hk
    rw [h1] at hcT
    exact hc1 hcT
  · exfalso
    have hTc : A ⊓ L = Subgroup.zpowers c := by
      refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcT) ?_).symm
      rw [hk, Nat.card_zpowers, hc3, pow_one]
    have hTB : A ⊓ L ≤ A ⊓ Sec4.thetaQuotCentralizer L := by
      rw [hTc]
      exact Subgroup.zpowers_le.mpr hcB
    have hAB : A ⊓ Sec4.thetaQuotCentralizer L = A :=
      (sup_eq_left.mpr hTB).symm.trans hsup
    rw [hAB, hA27] at hB9
    norm_num at hB9
  · rw [hk]
    norm_num
  · exfalso
    have hAL : A ⊓ L = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk, hA27]; norm_num)
    have hBL' : A ⊓ Sec4.thetaQuotCentralizer L ⊓ L = A ⊓ Sec4.thetaQuotCentralizer L := by
      refine inf_eq_left.mpr (le_trans inf_le_left ?_)
      rw [← hAL]
      exact inf_le_right
    rw [hBL', hB9] at hBL
    norm_num at hBL

theorem exists_mem_inf_moves_bar {A L : Subgroup G} {c : G} (hA : Late.IsE27 A) (hcA : c ∈ A)
    (hc1 : c ≠ 1) (hL : L ∈ thetaComponentsAt 3 c) (hcL : c ∈ L)
    (hsup : (A ⊓ Sec4.thetaQuotCentralizer L) ⊔ (A ⊓ L) = A)
    (hAL : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3)
    (hmoves : ∀ T : Subgroup (L ⧸ aschbacherSolvableCore 3 L),
      CFSG.Assembly.IsElemAbelian 3 T → Nat.card T = 9 → Subgroup.center _ ≤ T →
        ∃ x ∈ Subgroup.normalizer (T : Set _), IsPGroup 3 (Subgroup.zpowers x) ∧
          ∃ t ∈ T, x * t * x⁻¹ ≠ t)
    {P : Subgroup G} (hP : IsSylowOf 3 P
      (Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)))
    (hPL : P ≤ Subgroup.normalizer (L : Set G)) :
    ∃ g ∈ P ⊓ L, ∃ y ∈ A ⊓ L, g * y * g⁻¹ ≠ y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hexpA : ∀ x ∈ A, x ^ 3 = 1 := hA.1.2
  have hA3 : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hexpA x x.2)⟩
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hL
  set N := aschbacherSolvableCore 3 L with hNdef
  have hN3 : ¬ 3 ∣ Nat.card N := three_not_dvd_card_aschbacherSolvableCore
  set π := QuotientGroup.mk' N with hπ
  set T : Subgroup L := (A ⊓ L).subgroupOf L with hTdef
  have hT9 : Nat.card T = 9 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).trans hAL
  have hT3 : IsPGroup 3 T := IsPGroup.of_card (n := 2) (by rw [hT9]; norm_num)
  set Tb : Subgroup (L ⧸ N) := T.map π with hTbdef
  have hinjT := injOn_mk_of_coprime N hN3 hT3
  have hTb9 : Nat.card Tb = 9 := by
    rw [← hT9]
    change Nat.card (↑(T.map π) : Set (L ⧸ N)) = Nat.card (T : Set L)
    rw [Subgroup.coe_map, Nat.card_image_of_injOn hinjT]
  have hTbe : CFSG.Assembly.IsElemAbelian 3 Tb := by
    refine ⟨⟨⟨fun u v => ?_⟩⟩, ?_⟩
    · obtain ⟨u', hu', hu⟩ := Subgroup.mem_map.mp u.2
      obtain ⟨v', hv', hv⟩ := Subgroup.mem_map.mp v.2
      apply Subtype.ext
      change (u : L ⧸ N) * v = v * u
      rw [← hu, ← hv, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hcommA _ (Subgroup.mem_subgroupOf.mp hu').1 _
        (Subgroup.mem_subgroupOf.mp hv').1)
    · rintro _ ⟨u, hu, rfl⟩
      rw [← map_pow]
      have : u ^ 3 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow]
        exact hexpA _ (Subgroup.mem_subgroupOf.mp hu).1)
      rw [this, map_one]
  set c' : L := ⟨c, hcL⟩ with hc'
  have hc'T : c' ∈ T := Subgroup.mem_subgroupOf.mpr ⟨hcA, hcL⟩
  have hc'Z : c' ∈ Subgroup.center L := Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hLc g.2))
  have hπcZ : π c' ∈ Subgroup.center (L ⧸ N) :=
    Subgroup.map_center_le_center (QuotientGroup.mk'_surjective _) ⟨c', hc'Z, rfl⟩
  have hc'3 : orderOf c' = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime (hexpA c hcA) hc1
  have hπc1 : π c' ≠ 1 := by
    intro h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    apply hN3
    have h' := orderOf_dvd_natCard (⟨c', h1⟩ : N)
    rwa [Subgroup.orderOf_mk, hc'3] at h'
  have hZT : Subgroup.center (L ⧸ N) ≤ Tb := by
    have hle : Subgroup.zpowers (π c') ≤ Subgroup.center (L ⧸ N) :=
      Subgroup.zpowers_le.mpr hπcZ
    have hπc3 : orderOf (π c') = 3 := by
      refine orderOf_eq_prime ?_ hπc1
      have hc'p : c' ^ 3 = 1 := by rw [← hc'3]; exact pow_orderOf_eq_one c'
      rw [← map_pow, hc'p, map_one]
    have heq : Subgroup.zpowers (π c') = Subgroup.center (L ⧸ N) :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hZ, Nat.card_zpowers, hπc3])
    rw [← heq]
    exact Subgroup.zpowers_le.mpr ⟨c', hc'T, rfl⟩
  obtain ⟨xb, hxN, hx3, tb, htb, hmove⟩ := hmoves Tb hTbe hTb9 hZT
  obtain ⟨t, htT, rfl⟩ := htb
  obtain ⟨x, hxT, hx3', hxt⟩ := exists_isPGroup_normalizer_moves N hN3 hT3 hx3 hxN hmove
  have hxL : (x : G) ∈ L := x.2
  have hxAL : (x : G) ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    have hyT : (⟨y, hy.2⟩ : L) ∈ T := Subgroup.mem_subgroupOf.mpr hy
    have h1 := (Subgroup.mem_normalizer_iff.mp hxT _).mp hyT
    exact Subgroup.mem_subgroupOf.mp h1
  have hxG3 : IsPGroup 3 (Subgroup.zpowers (x : G)) := by
    have h := hx3'.map L.subtype
    rwa [MonoidHom.map_zpowers] at h
  have htG : (t : G) ∈ A ⊓ L := Subgroup.mem_subgroupOf.mp htT
  have hxtG : (x : G) * t * (x : G)⁻¹ ≠ t := fun he => hxt (Subtype.ext (by simpa using he))
  obtain ⟨x₂, hx₂L, hx₂T, hx₂3, hx₂t, hx₂B⟩ :=
    exists_moves_centralizing hA3 hcommA hxL hxAL hxG3 htG hxtG
  have hx₂A : x₂ ∈ Subgroup.normalizer (A : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    have hBN : A ⊓ Sec4.thetaQuotCentralizer L ≤
        Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) := fun b hb => by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        rw [hcommA b hb.1 y hy.1, mul_inv_cancel_right]
        exact hy
      · intro hy
        have hyA : y ∈ A := by
          have := A.mul_mem (A.mul_mem (A.inv_mem hb.1) hy.1) hb.1
          simpa [mul_assoc] using this
        rwa [hcommA b hb.1 y hyA, mul_inv_cancel_right] at hy
    have ha' : a ∈ ((A ⊓ Sec4.thetaQuotCentralizer L ⊔ A ⊓ L : Subgroup G) : Set G) := by
      rw [hsup]
      exact ha
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hBN] at ha'
    obtain ⟨b, hb, y, hy, rfl⟩ := ha'
    have e : x₂ * (b * y) * x₂⁻¹ = (x₂ * b * x₂⁻¹) * (x₂ * y * x₂⁻¹) := by group
    rw [e, hx₂B b hb, mul_inv_cancel_right]
    exact A.mul_mem hb.1 ((Subgroup.mem_normalizer_iff.mp hx₂T y).mp hy).1
  set W := Subgroup.normalizer (A : Set G) with hW
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  set Y := P ⊔ (L ⊓ W) with hY
  have hLC : L ⊓ W ≤ W ⊓ H := fun y hy => ⟨hy.2, mem_normalizer_zpowers_of_commute
    (Subgroup.mem_centralizer_singleton_iff.mp (hLc hy.1))⟩
  have hYWH : Y ≤ W ⊓ H := sup_le hP.le hLC
  have hYL : Y ≤ Subgroup.normalizer (L : Set G) :=
    sup_le hPL (inf_le_left.trans Subgroup.le_normalizer)
  have hPY : IsSylowOf 3 P Y := hP.of_le le_sup_left hYWH
  have hxY : x₂ ∈ Y := le_sup_right (a := P) ⟨hx₂L, hx₂A⟩
  obtain ⟨Q, hQ⟩ := hPY
  have hxp : IsPGroup 3 ((Subgroup.zpowers x₂).subgroupOf Y) := hx₂3.comap_subtype
  obtain ⟨Q', hQ'⟩ := hxp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y Q' Q
  have hxQ' : (⟨x₂, hxY⟩ : Y) ∈ (Q' : Subgroup Y) :=
    hQ' (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers _))
  have hgx : g * ⟨x₂, hxY⟩ * g⁻¹ ∈ (Q : Subgroup Y) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simpa [MulAut.smul_def, mul_assoc] using hxQ'
  have hgxP : (g : G) * x₂ * (g : G)⁻¹ ∈ P := hQ ▸ ⟨_, hgx, rfl⟩
  have hgL : (g : G) ∈ Subgroup.normalizer (L : Set G) := hYL g.2
  have hgA : (g : G) ∈ W := (hYWH g.2).1
  refine ⟨(g : G) * x₂ * (g : G)⁻¹, ⟨hgxP, (Subgroup.mem_normalizer_iff.mp hgL _).mp hx₂L⟩,
    (g : G) * t * (g : G)⁻¹, ⟨(Subgroup.mem_normalizer_iff.mp hgA _).mp htG.1,
      (Subgroup.mem_normalizer_iff.mp hgL _).mp htG.2⟩, fun he => hx₂t ?_⟩
  have := congrArg (fun z => (g : G)⁻¹ * z * g) he
  simpa [mul_assoc] using this

end Bar

section Main

variable {G : Type} [Group G] [Finite G]

theorem autIn_eq_transvectionGroup_bar (h45 : Sec4.Item4_5) {A L : Subgroup G} {c : G}
    (h : Sec12StdBar G A c L)
    (hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3)
    (hmoves : ∀ T : Subgroup (L ⧸ aschbacherSolvableCore 3 L),
      CFSG.Assembly.IsElemAbelian 3 T → Nat.card T = 9 → Subgroup.center _ ≤ T →
        ∃ x ∈ Subgroup.normalizer (T : Set _), IsPGroup 3 (Subgroup.zpowers x) ∧
          ∃ t ∈ T, x * t * x⁻¹ ≠ t)
    {P : Subgroup G} (hP : IsSylowOf 3 P (Subgroup.normalizer (A : Set G) ⊓
      Subgroup.normalizer (Subgroup.zpowers c : Set G)))
    (hPB : ¬ A ⊓ Sec4.thetaQuotCentralizer L ≤ (Subgroup.center P).map P.subtype) :
    Sec4.autIn P A = transvectionGroup A ⟨c, h.mem_A⟩ ∧ Nat.card (Sec4.autIn P A) = 9 := by
  have hexpA : ∀ x ∈ A, x ^ 3 = 1 := h.isE27.1.2
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hexpA c h.mem_A) h.ne_one
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hcB : c ∈ A ⊓ Sec4.thetaQuotCentralizer L :=
    ⟨h.mem_A, mem_thetaQuotCentralizer_of_central h.mem_L hLc⟩
  have hAL := card_inf_eq_nine_bar h.isE27 h.mem_A h.ne_one h.mem_L hLc hZ h.card_B h.sup_eq
  have hPL : P ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp hc3 h.mem_thetaComponentsAt
      hP.isPGroup (hP.le.trans inf_le_right)
  obtain ⟨b₀, hb₀, hb₀c⟩ := exists_mem_not_mem_zpowers h.card_B hc3
  obtain ⟨y₀, hy₀, hy₀c⟩ := exists_mem_not_mem_zpowers hAL hc3
  have hB := closure_pair_eq_of_card_nine (fun x hx => hexpA x (Subgroup.mem_inf.mp hx).1)
    h.card_B hcB h.ne_one hb₀ hb₀c
  have hAL' := closure_pair_eq_of_card_nine (fun x hx => hexpA x (Subgroup.mem_inf.mp hx).1) hAL
    ⟨h.mem_A, h.mem_L⟩ h.ne_one hy₀ hy₀c
  have hgen : Subgroup.closure ({c, b₀, y₀} : Set G) = A := by
    rw [← h.sup_eq, ← hB, ← hAL', ← Subgroup.closure_union]
    congr 1
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    tauto
  have hle := autIn_le_transvectionGroup_bar h.isE27 h.mem_A h.ne_one h.mem_L hLc h.card_B
    h.sup_eq hAL hP.le hP.isPGroup hPL
  have hT := card_transvectionGroup_le h.mem_A hb₀.1 hy₀.1 hgen hc3
  have h9 := nine_le_card_autIn_bar h.isE27 h.mem_A hP hPB
    (exists_mem_inf_moves_bar h.isE27 h.mem_A h.ne_one h.mem_thetaComponentsAt h.mem_L h.sup_eq
      hAL hZ hmoves hP hPL)
  exact ⟨Subgroup.eq_of_le_of_card_ge hle (hT.trans h9),
    le_antisymm ((Subgroup.card_le_of_le hle).trans hT) h9⟩

theorem normalizer_le_of_sec12StdBar (h45 : Sec4.Item4_5) {A L : Subgroup G} {c : G}
    (h : Sec12StdBar G A c L)
    (hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3)
    (hmoves : ∀ T : Subgroup (L ⧸ aschbacherSolvableCore 3 L),
      CFSG.Assembly.IsElemAbelian 3 T → Nat.card T = 9 → Subgroup.center _ ≤ T →
        ∃ x ∈ Subgroup.normalizer (T : Set _), IsPGroup 3 (Subgroup.zpowers x) ∧
          ∃ t ∈ T, x * t * x⁻¹ ≠ t) :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  obtain ⟨P, hP, hPB⟩ := h.exists_sylow
  obtain ⟨hPaut, hP9⟩ := autIn_eq_transvectionGroup_bar h45 h hZ hmoves hP hPB
  have hA27 : Nat.card A = 3 ^ 3 := by rw [h.isE27.2]; norm_num
  obtain ⟨V, _, _, hV, ⟨f⟩⟩ := exists_coords_module h.isE27.1 hA27
  exact normalizer_le_of_autIn_eq h.mem_A h.ne_one hP hPaut hP9 hV f

theorem normalizer_le_of_sec12StdBar_A6 (h45 : Sec4.Item4_5) {A L : Subgroup G} {c : G}
    (h : Sec12StdBar G A c L)
    (hL : Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6))) :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
  normalizer_le_of_sec12StdBar h45 h hL.1 fun T _ hT9 _ =>
    KFacts.exists_normalizer_moves_of_isTripleCover_alt
      (isQuasisimple_thetaQuot_of_mem h.mem_thetaComponentsAt) (Or.inl hL) T hT9

theorem normalizer_le_of_sec12StdBar_of_list (h45 : Sec4.Item4_5)
    (hK : KFacts.KS12NormalizerMoves) {A L : Subgroup G} {c : G} (h : Sec12StdBar G A c L)
    (hL : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22) :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  have hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3 := by
    rcases hL with hSL | hA6 | hA7 | hM22
    · exact card_center_eq_three_of_isSLThreePi hSL
    · exact hA6.1
    · exact hA7.1
    · exact hM22.1
  exact normalizer_le_of_sec12StdBar h45 h hZ fun T hT hT9 hZT =>
    hK _ (isQuasisimple_thetaQuot_of_mem h.mem_thetaComponentsAt) hL T hT hT9 hZT

end Main

end CFSG.RankThree.PartTwo.Sec12
