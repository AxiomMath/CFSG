module

public import CFSG.RankThree.PartTwo.Sec14.Ronan1411L37Bridge
import CFSG.RankThree.PartTwo.Sec14.Ronan1411L37Mat
import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJInner
import CFSG.LargeExtraspecial.S8DimB
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration
public import CFSG.RankThree.PartTwo.Sec4.LThreePiProjInner

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1411L37

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
  CFSG.RankThree.LocalRank
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix (ProjGenLinGroup)


variable {M : Type} [Group M] [Finite M] {Ybar Abar Xbar Rbar : Subgroup M} {abar : M}

theorem exists_pgl_model [Fact (Nat.Prime 7)] [hXn : Xbar.Normal]
    (hset : HJCoreSetting Ybar Abar Xbar Rbar abar)
    (hX : ∃ _ : Fact (Nat.Prime 7),
      Nonempty (↥Xbar ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1))) :
    ∃ e : ↥Xbar ≃* projImage (slPi true 3 (7 ^ 1) (GaloisField 7 1)),
      ∀ a ∈ Abar, ∃ y, IsPGLAtP e a y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨h7, -, hs, ⟨e⟩⟩ := exists_model hX
  have hK : PiField true 7 1 (GaloisField 7 1) :=
    ⟨Fact.out, le_rfl, by rw [GaloisField.card 7 1 (by norm_num)]; rfl⟩
  have hq : ModThree true (7 ^ 1) := by
    change 7 ^ 1 % 3 = 1
    norm_num
  haveI : Group.IsPerfect ↥Xbar := hset.perfect
  haveI := isPerfect_projImage_of_equiv e
  have hna : ∃ a b : ↥Xbar, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have htop : commutator ↥Xbar = ⊤ := Group.IsPerfect.commutator_eq_top
    have hbot : commutator ↥Xbar = ⊥ := by
      rw [commutator_def, eq_bot_iff]
      refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
      rw [Subgroup.mem_bot]
      exact commutatorElement_eq_one_iff_mul_comm.2 (h g₁ g₂)
    obtain ⟨g, hg⟩ := exists_ne (1 : ↥Xbar)
    have : g ∈ (⊥ : Subgroup ↥Xbar) := hbot ▸ htop ▸ Subgroup.mem_top g
    exact hg (Subgroup.mem_bot.1 this)
  obtain ⟨hLq, -⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hna
  have hθ := aschbacherSolvableCore_eq_bot_proj hK hq hLq e
  refine ⟨e, fun a ha => ?_⟩
  have hx3 : (⟨a, mem_normalizer_of_normal a⟩ : Subgroup.normalizer (Xbar : Set M)) ^ 3 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hset.isElemAbelian.2 a ha)
  rcases pslAct_pgl_or_field hK (by norm_num) hθ e _ hx3 with ⟨y, hy, hys⟩ |
    ⟨-, f₀, hf, -⟩
  · exact ⟨y, hy, hys⟩
  · omega

theorem false_of_not_inner (hset : HJCoreSetting Ybar Abar Xbar Rbar abar)
    (hX : ∃ _ : Fact (Nat.Prime 7),
      Nonempty (↥Xbar ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)))
    {b : M} (hbA : b ∈ Abar) (hbX : b ∈ Xbar) (hb1 : b ≠ 1)
    (hout : ∃ a₀ ∈ Abar, a₀ ∉ Xbar ⊔ Subgroup.centralizer (Xbar : Set M))
    {S T : Subgroup M} (hS : Maximal (Wales1411W.InvTwo Abar Ybar) S)
    (hT : Maximal (Wales1411W.InvTwo Abar Ybar) T) (hST : S ⊔ T = Ybar)
    (hsupp : ∀ e ∈ Abar, ¬ Ybar ≤ Subgroup.centralizer ({e} : Set M) →
      S ⊓ Subgroup.centralizer ({e} : Set M) = ⊥ ∨ T ⊓ Subgroup.centralizer ({e} : Set M) = ⊥) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hXn := Wales1411W.HJInner.normal_X hset
  obtain ⟨h7, -⟩ := id hX
  obtain ⟨e, hpgl⟩ := exists_pgl_model hset hX
  have hK : PiField true 7 1 (GaloisField 7 1) :=
    ⟨Fact.out, le_rfl, by rw [GaloisField.card 7 1 (by norm_num)]; rfl⟩
  have hq : ModThree true (7 ^ 1) := by
    change 7 ^ 1 % 3 = 1
    norm_num
  haveI : Group.IsPerfect ↥Xbar := hset.perfect
  haveI := isPerfect_projImage_of_equiv e
  have h2 : (2 : GaloisField 7 1) ≠ 0 := by
    have : CharP (GaloisField 7 1) 7 := inferInstance
    intro h
    have := (CharP.cast_eq_zero_iff (GaloisField 7 1) 7 2).mp (by exact_mod_cast h)
    omega
  have hLC := inf_centralizer_eq_bot_proj hK hq e
  have hAc : ∀ x ∈ Abar, ∀ y ∈ Abar, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hset.isElemAbelian.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hA3 : ∀ x ∈ Abar, x ^ 3 = 1 := hset.isElemAbelian.2
  obtain ⟨a₀, ha₀A, ha₀⟩ := hout
  have hbo : orderOf b = 3 := orderOf_eq_prime (hA3 b hbA) hb1
  have hzb : ∀ g ∈ Subgroup.zpowers b, g ≠ 1 → b ∈ Subgroup.zpowers g := by
    intro g hg hg1
    have hle : Subgroup.zpowers g ≤ Subgroup.zpowers b := Subgroup.zpowers_le.mpr hg
    have hgo : orderOf g = 3 := orderOf_eq_prime (by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hA3 b hbA, one_zpow])
      hg1
    have heq : Subgroup.zpowers g = Subgroup.zpowers b :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hgo, hbo])
    rw [heq]
    exact Subgroup.mem_zpowers b
  have hP1 : ∀ W : Subgroup M, W ≤ Xbar → IsPGroup 2 W →
      Abar ≤ Subgroup.normalizer (W : Set M) → W ≠ ⊥ →
      W ⊓ Subgroup.centralizer ({b} : Set M) ≠ ⊥ := by
    intro W hWX hW2 hAW hW1 hWb
    obtain ⟨Ω, hΩ⟩ : ∃ Ω : Subgroup M, ∀ x, x ∈ Ω ↔
        x ∈ W ∧ x ∈ Subgroup.centralizer (W : Set M) ∧ x ^ 2 = 1 :=
      ⟨{ carrier := {x | x ∈ W ∧ x ∈ Subgroup.centralizer (W : Set M) ∧ x ^ 2 = 1}
         mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, mul_mem hx.2.1 hy.2.1, by
           have hxy : Commute x y := (Subgroup.mem_centralizer_iff.mp hx.2.1 y hy.1).symm
           rw [hxy.mul_pow, hx.2.2, hy.2.2, one_mul]⟩
         one_mem' := ⟨one_mem _, one_mem _, one_pow _⟩
         inv_mem' := fun {x} hx => ⟨inv_mem hx.1, inv_mem hx.2.1, by
           rw [inv_pow, hx.2.2, inv_one]⟩ },
        fun x => Iff.rfl⟩
    have hΩW : Ω ≤ W := fun x hx => ((hΩ x).mp hx).1
    have hΩc : ∀ x ∈ Ω, ∀ y ∈ Ω, x * y = y * x := fun x hx y hy =>
      (Subgroup.mem_centralizer_iff.mp ((hΩ x).mp hx).2.1 y ((hΩ y).mp hy).1).symm
    have hAΩ : Abar ≤ Subgroup.normalizer (Ω : Set M) := by
      intro ε hε
      have hεW := hAW hε
      refine Subgroup.mem_normalizer_fintype fun x hx => ?_
      obtain ⟨hxW, hxC, hx2⟩ := (hΩ x).mp hx
      refine (hΩ _).mpr ⟨(Subgroup.mem_normalizer_iff.mp hεW x).mp hxW, ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro w hw
        have hw' : ε⁻¹ * w * ε ∈ W := by
          have := (Subgroup.mem_normalizer_iff.mp (inv_mem hεW) w).mp hw
          simpa using this
        have hc := Subgroup.mem_centralizer_iff.mp hxC _ hw'
        calc w * (ε * x * ε⁻¹) = ε * ((ε⁻¹ * w * ε) * x) * ε⁻¹ := by group
          _ = ε * (x * (ε⁻¹ * w * ε)) * ε⁻¹ := by rw [hc]
          _ = ε * x * ε⁻¹ * w := by group
      · rw [show (ε * x * ε⁻¹) ^ 2 = ε * x ^ 2 * ε⁻¹ by rw [sq, sq]; group, hx2, mul_one,
          mul_inv_cancel]
    have hΩ1 : Ω ≠ ⊥ := by
      haveI : Nontrivial ↥W := by
        rw [Subgroup.nontrivial_iff_ne_bot]
        exact hW1
      have hZ := hW2.center_nontrivial
      have hZ2 : IsPGroup 2 (Subgroup.center ↥W) := hW2.to_subgroup _
      obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥W)) 2
        (by
          rcases hZ2.card_eq_or_dvd with h | h
          · exfalso
            rw [Nat.card_eq_one_iff_unique] at h
            obtain ⟨u, v, huv⟩ := exists_pair_ne ↥(Subgroup.center ↥W)
            exact huv (h.1.elim u v)
          · exact h)
      intro hbot
      have hcM : ((c : ↥W) : M) ∈ Ω := by
        refine (hΩ _).mpr ⟨(c : ↥W).2, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_, ?_⟩
        · have := Subgroup.mem_center_iff.mp c.2 ⟨w, hw⟩
          show w * ((c : ↥W) : M) = ((c : ↥W) : M) * w
          exact congrArg Subtype.val this
        · rw [← Subgroup.coe_pow, ← Subgroup.coe_pow, ← hc, pow_orderOf_eq_one, Subgroup.coe_one,
            Subgroup.coe_one]
      rw [hbot] at hcM
      have hc1 : c = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        exact Subgroup.mem_bot.mp hcM
      rw [hc1, orderOf_one] at hc
      norm_num at hc
    have ha₀1 : a₀ ≠ 1 := fun h => ha₀ (h ▸ one_mem _)
    have ha₀o : orderOf a₀ = 3 := orderOf_eq_prime (hA3 a₀ ha₀A) ha₀1
    have hb₀X : Subgroup.zpowers b ≤ Xbar ⊔ Subgroup.centralizer (Xbar : Set M) :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left hbX)
    have hinf : Subgroup.zpowers b ⊓ Subgroup.zpowers a₀ = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      rw [Subgroup.mem_bot]
      by_contra hg1
      obtain ⟨hgb, hga⟩ := Subgroup.mem_inf.mp hg
      have hga₀ : Subgroup.zpowers g = Subgroup.zpowers a₀ := by
        have hle : Subgroup.zpowers g ≤ Subgroup.zpowers a₀ := Subgroup.zpowers_le.mpr hga
        have hgo : orderOf g = 3 := orderOf_eq_prime (by
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hga
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hA3 a₀ ha₀A,
            one_zpow]) hg1
        exact Subgroup.eq_of_le_of_card_ge hle (by
          rw [Nat.card_zpowers, Nat.card_zpowers, hgo, ha₀o])
      apply ha₀
      have : a₀ ∈ Subgroup.zpowers g := hga₀ ▸ Subgroup.mem_zpowers a₀
      exact Subgroup.zpowers_le.mpr (hb₀X hgb) this
    set F := Subgroup.zpowers b ⊔ Subgroup.zpowers a₀ with hF
    have hab₀ : a₀ * b = b * a₀ := hAc a₀ ha₀A b hbA
    have hnorm : Subgroup.zpowers a₀ ≤
        Subgroup.normalizer ((Subgroup.zpowers b : Subgroup M) : Set M) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.mem_normalizer_fintype fun z hz => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      rw [(Commute.zpow_right (show Commute a₀ b from hab₀) k).eq, mul_inv_cancel_right]
      exact Subgroup.zpow_mem_zpowers b k
    have hF9 : Nat.card F = 3 ^ 2 := by
      have h := CFSG.LargeExtraspecial.S8.card_sup_mul_card_inf_of_le_normalizer' hnorm
      rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hbo, ha₀o] at h
      rw [← hF] at h
      omega
    have hFA : F ≤ Abar := sup_le (Subgroup.zpowers_le.mpr hbA) (Subgroup.zpowers_le.mpr ha₀A)
    have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
      3 Nat.prime_three F Ω (fun m => Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hA3 _ (hFA m.2))) hF9
      (by
        have h2Ω : IsPGroup 2 Ω := hW2.to_le hΩW
        obtain ⟨n, hn⟩ := h2Ω.exists_card_eq
        rw [hn]
        intro h3
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
          (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
        omega)
      (hFA.trans hAΩ)
    obtain ⟨f, hf1, hfΩ⟩ : ∃ f : ↥F, f ≠ 1 ∧ Ω ⊓ Subgroup.centralizer ({(f : M)} : Set M) ≠ ⊥ := by
      by_contra h
      push Not at h
      apply hΩ1
      rw [hgen]
      refine iSup_eq_bot.mpr fun f => iSup_eq_bot.mpr fun hf => ?_
      exact h f hf
    have hfC : ∀ x, x * (f : M) = (f : M) * x → x ∈ Ω → x ∈ W ⊓ Subgroup.centralizer {b} →
        x = 1 := fun x _ _ hx => by
      rw [hWb] at hx
      exact Subgroup.mem_bot.mp hx
    have hfb : (f : M) ∉ Subgroup.zpowers b := by
      intro hfb
      apply hfΩ
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxΩ, hxf⟩ := Subgroup.mem_inf.mp hx
      have hbz := hzb (f : M) hfb (fun h => hf1 (Subtype.ext h))
      have hxb : x ∈ Subgroup.centralizer ({b} : Set M) := by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hbz
        rw [Subgroup.mem_centralizer_singleton_iff] at hxf ⊢
        rw [← hk]
        exact (Commute.zpow_left hxf.symm k).eq.symm
      have : x ∈ W ⊓ Subgroup.centralizer ({b} : Set M) := ⟨hΩW hxΩ, hxb⟩
      rw [hWb] at this
      exact this
    have hfout : (f : M) ∉ Xbar ⊔ Subgroup.centralizer (Xbar : Set M) := by
      intro hfX
      have hmem : (f : M) ∈ ((Subgroup.zpowers b ⊔ Subgroup.zpowers a₀ : Subgroup M) : Set M) :=
        f.2
      rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm] at hmem
      obtain ⟨u, hu, v, hv, huv⟩ := hmem
      change u * v = (f : M) at huv
      have hv1 : v ≠ 1 := by
        rintro rfl
        rw [mul_one] at huv
        exact hfb (huv ▸ hu)
      have hvX : v ∈ Xbar ⊔ Subgroup.centralizer (Xbar : Set M) := by
        have : v = u⁻¹ * (f : M) := by rw [← huv]; group
        rw [this]
        exact mul_mem (inv_mem (hb₀X hu)) hfX
      have hva : Subgroup.zpowers v = Subgroup.zpowers a₀ := by
        have hle : Subgroup.zpowers v ≤ Subgroup.zpowers a₀ := Subgroup.zpowers_le.mpr hv
        have hvo : orderOf v = 3 := orderOf_eq_prime (by
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hA3 a₀ ha₀A,
            one_zpow]) hv1
        exact Subgroup.eq_of_le_of_card_ge hle (by
          rw [Nat.card_zpowers, Nat.card_zpowers, hvo, ha₀o])
      apply ha₀
      have : a₀ ∈ Subgroup.zpowers v := hva ▸ Subgroup.mem_zpowers a₀
      exact Subgroup.zpowers_le.mpr hvX this
    have hfA : (f : M) ∈ Abar := hFA f.2
    obtain ⟨⟨t₁, ht₁⟩, ht₁1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hfΩ
    obtain ⟨ht₁Ω, ht₁f⟩ := Subgroup.mem_inf.mp ht₁
    have ht₁f' : (f : M) * t₁ = t₁ * (f : M) :=
      (Subgroup.mem_centralizer_singleton_iff.mp ht₁f).symm
    set t₂ := b * t₁ * b⁻¹ with ht₂def
    have hconjΩ : ∀ x ∈ Ω, b * x * b⁻¹ ∈ Ω := fun x hx =>
      (Subgroup.mem_normalizer_iff.mp (hAΩ hbA) x).mp hx
    have ht₂Ω : t₂ ∈ Ω := hconjΩ _ ht₁Ω
    have ht₁ne : t₁ ≠ 1 := fun h => ht₁1 (Subtype.ext h)
    have h12 : t₁ ≠ t₂ := by
      intro h
      apply ht₁ne
      have hx : t₁ ∈ W ⊓ Subgroup.centralizer ({b} : Set M) := by
        refine ⟨hΩW ht₁Ω, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        calc t₁ * b = b * t₁ * b⁻¹ * b := by rw [← ht₂def, ← h]
          _ = b * t₁ := by group
      rw [hWb] at hx
      exact Subgroup.mem_bot.mp hx
    have ht₂1 : t₂ ≠ 1 := by
      intro h
      apply ht₁ne
      calc t₁ = b⁻¹ * t₂ * b := by rw [ht₂def]; group
        _ = 1 := by rw [h]; group
    have hc12 : t₁ * t₂ = t₂ * t₁ := hΩc _ ht₁Ω _ ht₂Ω
    set t₃ := b * t₂ * b⁻¹ with ht₃def
    have ht₃Ω : t₃ ∈ Ω := hconjΩ _ ht₂Ω
    have hb3 : b ^ 3 = 1 := hA3 b hbA
    have hprod : t₁ * t₂ * t₃ = 1 := by
      have hx : t₁ * t₂ * t₃ ∈ W ⊓ Subgroup.centralizer ({b} : Set M) := by
        refine ⟨hΩW (mul_mem (mul_mem ht₁Ω ht₂Ω) ht₃Ω),
          Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        have hbt₃ : b * t₃ * b⁻¹ = t₁ := by
          rw [ht₃def, ht₂def]
          rw [show b * (b * (b * t₁ * b⁻¹) * b⁻¹) * b⁻¹ = (b * b * b) * t₁ * (b * b * b)⁻¹ by
            group, show b * b * b = b ^ 3 by rw [pow_succ, sq], hb3]
          group
        have h1 : b * (t₁ * t₂ * t₃) * b⁻¹ = t₁ * t₂ * t₃ := by
          calc b * (t₁ * t₂ * t₃) * b⁻¹ =
              (b * t₁ * b⁻¹) * (b * t₂ * b⁻¹) * (b * t₃ * b⁻¹) := by group
            _ = t₂ * t₃ * t₁ := by rw [← ht₂def, ← ht₃def, hbt₃]
            _ = t₁ * (t₂ * t₃) := by rw [hΩc _ (mul_mem ht₂Ω ht₃Ω) _ ht₁Ω]
            _ = t₁ * t₂ * t₃ := by group
        calc t₁ * t₂ * t₃ * b = b * (t₁ * t₂ * t₃) * b⁻¹ * b := by rw [h1]
          _ = b * (t₁ * t₂ * t₃) := by group
      rw [hWb] at hx
      exact Subgroup.mem_bot.mp hx
    have ht₁2 : t₁ ^ 2 = 1 := ((hΩ _).mp ht₁Ω).2.2
    have ht₂2 : t₂ ^ 2 = 1 := ((hΩ _).mp ht₂Ω).2.2
    have hb₂ : b * t₂ * b⁻¹ = t₁ * t₂ := by
      have h1 : t₃ = (t₁ * t₂)⁻¹ := eq_inv_of_mul_eq_one_right hprod
      have hi1 : t₁⁻¹ = t₁ := inv_eq_of_mul_eq_one_right (by rw [← sq, ht₁2])
      have hi2 : t₂⁻¹ = t₂ := inv_eq_of_mul_eq_one_right (by rw [← sq, ht₂2])
      rw [← ht₃def, h1, mul_inv_rev, hi1, hi2]
      exact hc12.symm
    have hft₂ : (f : M) * t₂ = t₂ * (f : M) := by
      have hc1 : Commute (f : M) b := hAc _ hfA _ hbA
      have hc2 : Commute (f : M) t₁ := ht₁f'
      exact ((hc1.mul_right hc2).mul_right hc1.inv_right).eq
    obtain ⟨y, hy⟩ := hpgl _ hfA
    have hfCX : (f : M) ∉ Subgroup.centralizer (Xbar : Set M) := fun h =>
      hfout (Subgroup.mem_sup_right h)
    refine false_of_fix_four hK hq h2 e hy (hA3 _ hfA) hfCX ?_ (hWX (hΩW ht₁Ω)) (hWX (hΩW ht₂Ω))
      hbX ht₁2 ht₂2 ht₁ne ht₂1 h12 hc12 ht₁f' hft₂ (hAc _ hfA _ hbA) rfl hb₂
    rintro ⟨l, hl, hyl⟩
    obtain ⟨v, hv, -, hfv⟩ := exists_inner_mem_of_innerP hK hq hy hl hyl
    apply hfout
    have : (f : M) = (f : M) * v⁻¹ * v := by group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_right hfv) (Subgroup.mem_sup_left hv)
  have hP2 : ∀ R : Subgroup M, Maximal (Wales1411W.InvTwo Abar Ybar) R → R ≠ ⊥ →
      R ⊓ Subgroup.centralizer ({b} : Set M) ≠ ⊥ := by
    intro R hR hR1
    obtain ⟨-, hAR, hR2⟩ := hR.prop
    by_cases hRX : R ⊓ Xbar = ⊥
    · have hRb : R ≤ Subgroup.centralizer ({b} : Set M) := by
        intro r hr
        have hc : b * r * b⁻¹ * r⁻¹ ∈ R ⊓ Xbar := by
          refine Subgroup.mem_inf.mpr
            ⟨mul_mem ((Subgroup.mem_normalizer_iff.mp (hAR hbA) r).mp hr) (inv_mem hr), ?_⟩
          have : b * r * b⁻¹ * r⁻¹ = b * (r * b⁻¹ * r⁻¹) := by group
          rw [this]
          exact mul_mem hbX (hXn.conj_mem _ (inv_mem hbX) r)
        rw [hRX, Subgroup.mem_bot] at hc
        rw [Subgroup.mem_centralizer_singleton_iff]
        have : b * r * b⁻¹ = r := by
          calc b * r * b⁻¹ = b * r * b⁻¹ * r⁻¹ * r := by group
            _ = r := by rw [hc, one_mul]
        calc r * b = b * r * b⁻¹ * b := by rw [this]
          _ = b * r := by group
      rwa [inf_eq_left.mpr hRb]
    · have hW := hP1 (R ⊓ Xbar) inf_le_right (hR2.to_le inf_le_left)
        (fun ε hε => by
          refine Subgroup.mem_normalizer_fintype fun x hx => ?_
          exact ⟨(Subgroup.mem_normalizer_iff.mp (hAR hε) x).mp hx.1, hXn.conj_mem _ hx.2 ε⟩)
        hRX
      intro h
      apply hW
      rw [eq_bot_iff]
      intro x hx
      have : x ∈ R ⊓ Subgroup.centralizer ({b} : Set M) := ⟨hx.1.1, hx.2⟩
      rw [h] at this
      exact this
  have hY2 : ∀ R : Subgroup M, R = Ybar → ¬ IsPGroup 2 R := by
    intro R hR h2R
    have hbR : b ∈ R := hR ▸ hset.le_Y hbX
    obtain ⟨n, hn⟩ := h2R ⟨b, hbR⟩
    have h1 : orderOf b ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one (by
      have := congrArg Subtype.val hn
      simpa using this)
    rw [hbo] at h1
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1)
    omega
  have hS1 : S ≠ ⊥ := by
    intro h
    apply hY2 T (by rw [← hST, h, bot_sup_eq])
    exact hT.prop.2.2
  have hT1 : T ≠ ⊥ := by
    intro h
    apply hY2 S (by rw [← hST, h, sup_bot_eq])
    exact hS.prop.2.2
  have hbY : ¬ Ybar ≤ Subgroup.centralizer ({b} : Set M) := by
    intro h
    apply hb1
    have hbC : b ∈ Xbar ⊓ Subgroup.centralizer (Xbar : Set M) := by
      refine ⟨hbX, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mp (h (hset.le_Y hx))
    rw [hLC] at hbC
    exact Subgroup.mem_bot.mp hbC
  rcases hsupp b hbA hbY with h | h
  · exact hP2 S hS hS1 h
  · exact hP2 T hT hT1 h

end CFSG.RankThree.PartTwo.Sec14.Ronan1411L37
