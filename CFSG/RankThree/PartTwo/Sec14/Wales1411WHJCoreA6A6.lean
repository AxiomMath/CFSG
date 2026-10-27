module

public import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJCore
import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJInner
import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJFactor
public import CFSG.RankThree.PartTwo.Sec14.Item14Res9ProofPair
import CFSG.LargeExtraspecial.S8DimB
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo Equiv

namespace Wales1411W.HJA6A6

open Res9Pair Item148PtRes

variable {M : Type} [Group M] [Finite M] {Ybar Abar Xbar Rbar : Subgroup M} {abar : M}

theorem fixed_of_card_three {Γ : Type*} [Group Γ] {Z : Subgroup Γ} (hZ : Nat.card Z = 3)
    {σ : MulAut Γ} (hσ3 : σ ^ 3 = 1) (hσZ : ∀ z ∈ Z, σ z ∈ Z) {z : Γ} (hz : z ∈ Z) :
    σ z = z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite Z := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
  by_cases hz1 : z = 1
  · rw [hz1, map_one]
  have hzo : orderOf z = 3 := by
    have h := Subgroup.orderOf_dvd_natCard Z hz
    rw [hZ] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp h with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz1
    · exact h
  have hZz : Z = Subgroup.zpowers z :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz)
      (by rw [hZ, Nat.card_zpowers, hzo])).symm
  have hσz : σ z ∈ Subgroup.zpowers z := hZz ▸ hσZ z hz
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hσz
  have hz3 : z ^ 3 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one z
  have hkmod : z ^ k = z ^ (k % 3) := by
    rw [← zpow_mod_orderOf z k, hzo, Nat.cast_ofNat]
  have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  have hσ3z : σ (σ (σ z)) = z := by
    have h := congrArg (fun τ : MulAut Γ => τ z) hσ3
    simpa [pow_succ, MulAut.mul_apply] using h
  rcases hk3 with h | h | h
  · rw [hkmod, h, zpow_zero] at hk
    exact absurd ((map_eq_one_iff σ σ.injective).mp hk.symm) hz1
  · rw [hkmod, h, zpow_one] at hk
    exact hk.symm
  · rw [hkmod, h] at hk
    exfalso
    have h2 : σ z = z * z := by rw [← hk, zpow_two]
    have h4 : σ (σ z) = z := by
      rw [h2, map_mul, h2]
      calc z * z * (z * z) = z ^ 3 * z := by rw [pow_three]; simp only [mul_assoc]
        _ = z := by rw [hz3, one_mul]
    rw [h4, h2] at hσ3z
    apply hz1
    calc z = z * z * z⁻¹ := by group
      _ = z * z⁻¹ := by rw [hσ3z]
      _ = 1 := by group

theorem a6_noncomm : ∃ σ τ : alternatingGroup (Fin 6), σ ^ 3 = 1 ∧ σ * τ ≠ τ * σ := by
  have h1 : (swap (0 : Fin 6) 1 * swap 0 2) ∈ alternatingGroup (Fin 6) := by
    rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap (by decide),
      Perm.sign_swap (by decide)]
    decide
  have h2 : (swap (0 : Fin 6) 1 * swap 0 3) ∈ alternatingGroup (Fin 6) := by
    rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap (by decide),
      Perm.sign_swap (by decide)]
    decide
  refine ⟨⟨_, h1⟩, ⟨_, h2⟩, Subtype.ext ?_, fun h => ?_⟩
  · show (swap (0 : Fin 6) 1 * swap 0 2) ^ 3 = 1
    decide
  · have h' : (swap (0 : Fin 6) 1 * swap 0 2) * (swap 0 1 * swap 0 3) =
        (swap 0 1 * swap 0 3) * (swap 0 1 * swap 0 2) := congrArg Subtype.val h
    exact absurd h' (by decide)

theorem exists_plane (hset : HJCoreSetting Ybar Abar Xbar Rbar abar) :
    ∃ E : Subgroup M, E ≤ Abar ∧ Nat.card E = 9 ∧ E ⊓ Subgroup.zpowers abar = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : ∀ g ∈ Abar, g ^ 3 = 1 := hset.isElemAbelian.2
  have hAc : ∀ g ∈ Abar, ∀ h ∈ Abar, g * h = h * g := fun g hg h hh =>
    congrArg Subtype.val (hset.isElemAbelian.1.is_comm.comm ⟨g, hg⟩ ⟨h, hh⟩)
  have hord : ∀ g ∈ Abar, g ≠ 1 → Nat.card (Subgroup.zpowers g) = 3 := fun g hg h1 => by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hA3 g hg) h1
  have hcard : ∀ g ∈ Abar, ∀ h ∈ Abar, Nat.card (Subgroup.zpowers g) = 3 →
      Nat.card (Subgroup.zpowers h) = 3 → h ∉ Subgroup.zpowers g →
      Nat.card (Subgroup.zpowers g ⊔ Subgroup.zpowers h : Subgroup M) = 9 := by
    intro g hg h hh hg3 hh3 hgh
    have hN : Subgroup.zpowers h ≤ Subgroup.normalizer ((Subgroup.zpowers g : Subgroup M) :
        Set M) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.mem_normalizer_fintype fun z hz => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hc : Commute h (g ^ k) := (Commute.zpow_right (hAc h hh g hg) k)
      rw [hc.eq, mul_inv_cancel_right]
      exact Subgroup.zpow_mem_zpowers g k
    have hinf : Subgroup.zpowers g ⊓ Subgroup.zpowers h = ⊥ := by
      rcases (Nat.dvd_prime Nat.prime_three).mp
          (hh3 ▸ Subgroup.card_dvd_of_le (inf_le_right : Subgroup.zpowers g ⊓
            Subgroup.zpowers h ≤ _)) with h1 | h1
      · exact Subgroup.card_eq_one.mp h1
      · exfalso
        have heq : Subgroup.zpowers g ⊓ Subgroup.zpowers h = Subgroup.zpowers h :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h1, hh3])
        exact hgh (heq ▸ Subgroup.mem_inf.mp (heq.symm ▸ Subgroup.mem_zpowers h) |>.1)
    have hc := CFSG.LargeExtraspecial.S8.card_sup_mul_card_inf_of_le_normalizer' hN
    rw [hinf, Subgroup.card_bot, mul_one, hg3, hh3] at hc
    exact hc
  have ha3 := hord abar hset.mem_A hset.ne_one
  have hnle1 : ¬ Abar ≤ Subgroup.zpowers abar := fun hle => by
    have := Subgroup.card_le_of_le hle
    rw [hset.card_A, ha3] at this
    norm_num at this
  obtain ⟨e₁, he₁A, he₁⟩ := SetLike.not_le_iff_exists.mp hnle1
  have he₁1 : e₁ ≠ 1 := fun h => he₁ (h ▸ one_mem _)
  have he₁3 := hord e₁ he₁A he₁1
  set B₁ := Subgroup.zpowers abar ⊔ Subgroup.zpowers e₁ with hB₁
  have hB₁9 : Nat.card B₁ = 9 := hcard abar hset.mem_A e₁ he₁A ha3 he₁3 he₁
  have hB₁A : B₁ ≤ Abar :=
    sup_le (Subgroup.zpowers_le.mpr hset.mem_A) (Subgroup.zpowers_le.mpr he₁A)
  have hnle2 : ¬ Abar ≤ B₁ := fun hle => by
    have := Subgroup.card_le_of_le hle
    rw [hset.card_A, hB₁9] at this
    norm_num at this
  obtain ⟨e₂, he₂A, he₂⟩ := SetLike.not_le_iff_exists.mp hnle2
  have he₂1 : e₂ ≠ 1 := fun h => he₂ (h ▸ one_mem _)
  have he₂3 := hord e₂ he₂A he₂1
  have he₂₁ : e₂ ∉ Subgroup.zpowers e₁ := fun h => he₂ (Subgroup.mem_sup_right h)
  refine ⟨Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂,
    sup_le (Subgroup.zpowers_le.mpr he₁A) (Subgroup.zpowers_le.mpr he₂A),
    hcard e₁ he₁A e₂ he₂A he₁3 he₂3 he₂₁, ?_⟩
  set E := Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂ with hE
  have hE9 : Nat.card E = 9 := hcard e₁ he₁A e₂ he₂A he₁3 he₂3 he₂₁
  rcases (Nat.dvd_prime Nat.prime_three).mp
      (ha3 ▸ Subgroup.card_dvd_of_le (inf_le_right : E ⊓ Subgroup.zpowers abar ≤ _)) with h1 | h1
  · exact Subgroup.card_eq_one.mp h1
  · exfalso
    have heq : E ⊓ Subgroup.zpowers abar = Subgroup.zpowers abar :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h1, ha3])
    have haE : Subgroup.zpowers abar ≤ E := heq ▸ inf_le_left
    have hB₁E : B₁ ≤ E := sup_le haE le_sup_left
    have hB₁eq : B₁ = E := Subgroup.eq_of_le_of_card_ge hB₁E (by rw [hB₁9, hE9])
    exact he₂ (hB₁eq ▸ (Subgroup.mem_sup_right (Subgroup.mem_zpowers e₂) : e₂ ∈ E))

theorem false_of_trivOn (hset : HJCoreSetting Ybar Abar Xbar Rbar abar) [hXn : Xbar.Normal]
    [hXp : Group.IsPerfect ↥Xbar] {U V : Subgroup ↥Xbar} (hP : IsPair U V) {e : M}
    (heA : e ∈ Abar) (hea : e ∉ Subgroup.zpowers abar)
    (htriv : TrivOn (MulAut.conjNormal (H := Xbar) e) V) {S T : Subgroup M}
    (hS : InvTwo Abar Ybar S) (hT : InvTwo Abar Ybar T) (hST : S ⊔ T = Ybar)
    (hsupp : S ⊓ Subgroup.centralizer ({e} : Set M) = ⊥ ∨
      T ⊓ Subgroup.centralizer ({e} : Set M) = ⊥) : False := by
  haveI hUn := hP.normal_left
  haveI hVn := hP.normal_right
  have hA3 : ∀ g ∈ Abar, g ^ 3 = 1 := hset.isElemAbelian.2
  set σ := MulAut.conjNormal (H := Xbar) e with hσ
  have hσapp : ∀ g : ↥Xbar, ((σ g : ↥Xbar) : M) = e * g * e⁻¹ := fun g =>
    MulAut.conjNormal_apply e g
  have hσ3 : σ ^ 3 = 1 := by rw [hσ, ← map_pow, hA3 e heA, map_one]
  obtain ⟨hσU, hσV⟩ := map_eq_of_pow_three hP.sup_eq hP.comm_eq hP.card_inf hP.cover_left
    hP.cover_right hσ3
  have hfixVV : ∀ x ∈ ⁅V, V⁆, σ x = x := fun x hx =>
    fixed_of_mem_commutator hP.symm.centerIn_le_center htriv hx
  have hσZ : ∀ z ∈ U ⊓ V, σ z ∈ U ⊓ V := by
    intro z hz
    obtain ⟨hzU, hzV⟩ := Subgroup.mem_inf.mp hz
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [← hσU]
      exact ⟨z, hzU, rfl⟩
    · rw [← hσV]
      exact ⟨z, hzV, rfl⟩
  have hfixZ : ∀ z ∈ U ⊓ V, σ z = z := fun z hz =>
    fixed_of_card_three hP.card_inf hσ3 hσZ hz
  have hfixV : ∀ v ∈ V, σ v = v := by
    intro v hv
    have htop := top_eq_commutator_sup hP.sup_eq hP.comm_eq
    have hv' : v ∈ ((⁅U, U⁆ ⊔ ⁅V, V⁆ : Subgroup ↥Xbar) : Set ↥Xbar) := by
      rw [← htop]
      trivial
    rw [Subgroup.mul_normal] at hv'
    obtain ⟨a, ha, b, hb, hab⟩ := hv'
    change a * b = v at hab
    have hbV : b ∈ V := Subgroup.commutator_le_left V V hb
    have haU : a ∈ U := Subgroup.commutator_le_left U U ha
    have haV : a ∈ V := by
      have : a = v * b⁻¹ := by rw [← hab]; group
      rw [this]
      exact mul_mem hv (inv_mem hbV)
    rw [← hab, map_mul, hfixZ a (Subgroup.mem_inf.mpr ⟨haU, haV⟩), hfixVV b hb]
  set V' : Subgroup M := V.map Xbar.subtype with hV'
  have heV : V' ≤ Subgroup.centralizer ({e} : Set M) := by
    rintro _ ⟨v, hv, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := congrArg Subtype.val (hfixV v hv)
    rw [hσapp] at h
    calc (v : M) * e = e * v * e⁻¹ * e := by rw [h]
      _ = e * v := by group
  have hnot : ¬ ∀ g : ↥Xbar, σ g = g := by
    intro hall
    apply hea
    apply hset.mem_zpowers e heA
    apply HJInner.le_centralizer_Y_of_X hset heA
    intro x hx
    have h := congrArg Subtype.val (hall ⟨x, hx⟩)
    rw [hσapp] at h
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * e = e * x * e⁻¹ * e := by rw [h]
      _ = e * x := by group
  have hRN : Rbar ≤ Subgroup.normalizer (V' : Set M) := by
    intro r hr
    set τ := MulAut.conjNormal (H := Xbar) r with hτ
    have hτapp : ∀ g : ↥Xbar, ((τ g : ↥Xbar) : M) = r * g * r⁻¹ := fun g =>
      MulAut.conjNormal_apply r g
    have hτn : (V.map τ.toMonoidHom).Normal := hVn.map _ τ.surjective
    have hτc : Nat.card (V.map τ.toMonoidHom) = Nat.card U := by
      rw [Subgroup.card_map_of_injective (f := τ.toMonoidHom) (by exact τ.injective),
        card_eq_of_isTripleCover hP.cover_right,
        card_eq_of_isTripleCover hP.cover_left]
    have her : e * r = r * e := Subgroup.mem_centralizer_iff.mp (hset.le_centralizer_R hr) e heA
    rcases eq_or_eq_of_normal hP.sup_eq hP.comm_eq hP.card_inf hP.cover_left hP.cover_right hτn
      hτc with h | h
    · exfalso
      apply hnot
      have hfixU : ∀ u ∈ U, σ u = u := by
        intro u hu
        rw [← h] at hu
        obtain ⟨v, hv, rfl⟩ := hu
        apply Subtype.ext
        have hv' := congrArg Subtype.val (hfixV v hv)
        rw [hσapp] at hv'
        change ((σ (τ v) : ↥Xbar) : M) = ((τ v : ↥Xbar) : M)
        rw [hσapp, hτapp]
        calc e * (r * v * r⁻¹) * e⁻¹ = (e * r) * v * (e * r)⁻¹ := by group
          _ = (r * e) * v * (r * e)⁻¹ := by rw [her]
          _ = r * (e * v * e⁻¹) * r⁻¹ := by group
          _ = r * v * r⁻¹ := by rw [hv']
      intro g
      have hle : U ⊔ V ≤ MonoidHom.eqLocus σ.toMonoidHom (MonoidHom.id _) :=
        sup_le (fun u hu => hfixU u hu) (fun v hv => hfixV v hv)
      exact hle (hP.sup_eq ▸ Subgroup.mem_top g)
    · refine Subgroup.mem_normalizer_fintype fun n hn => ?_
      obtain ⟨v, hv, rfl⟩ := hn
      have hτv : τ v ∈ V := by
        rw [← h]
        exact ⟨v, hv, rfl⟩
      exact ⟨τ v, hτv, hτapp v⟩
  have hXN : Xbar ≤ Subgroup.normalizer (V' : Set M) := by
    intro x hx
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨v, hv, rfl⟩ := hn
    have hc : (⟨x, hx⟩ : ↥Xbar) * v * (⟨x, hx⟩ : ↥Xbar)⁻¹ ∈ V := hVn.conj_mem v hv _
    exact ⟨_, hc, by simp⟩
  have hYN : Ybar ≤ Subgroup.normalizer (V' : Set M) := by
    rw [hset.eq_sup]
    exact sup_le hXN hRN
  have hV'Y : V' ≤ Ybar := (Subgroup.map_subtype_le V).trans hset.le_Y
  obtain ⟨-, ⟨χ⟩⟩ := hP.cover_right
  obtain ⟨σ1, τ1, hσ1, hστ⟩ := a6_noncomm
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (χ.symm σ1)
  obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (χ.symm τ1)
  have hxV : (((u : ↥V) : ↥Xbar) : M) ∈ V' := ⟨u, u.2, rfl⟩
  have hu3 : u ^ 3 ∈ Subgroup.center ↥V := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hu, ← map_pow, hσ1, map_one]
  have hx3 : (((u : ↥V) : ↥Xbar) : M) ^ 3 ∈ Subgroup.centralizer (V' : Set M) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    have h := Subgroup.mem_center_iff.mp hu3 ⟨v, hv⟩
    have h' := congrArg (fun z : ↥V => ((z : ↥Xbar) : M)) h
    simpa using h'
  have hxc : ¬ V' ≤ Subgroup.centralizer ({(((u : ↥V) : ↥Xbar) : M)} : Set M) := by
    intro hle
    apply hστ
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hle ⟨w, w.2, rfl⟩)
    have huw : u * w = w * u := Subtype.ext (Subtype.ext h.symm)
    apply χ.symm.injective
    rw [map_mul, map_mul, ← hu, ← hw, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, huw]
  exact HJFactor.false_of_factor hV'Y hYN hxV hx3 hxc heA (hA3 e heA) heV hS hT hST hsupp

theorem le_centralizer_of_diag (hset : HJCoreSetting Ybar Abar Xbar Rbar abar)
    [hXn : Xbar.Normal] [hXp : Group.IsPerfect ↥Xbar] {U V : Subgroup ↥Xbar} (hP : IsPair U V)
    (hdiag : ∀ e ∈ Abar, e ∉ Subgroup.zpowers abar →
      ¬ TrivOn (MulAut.conjNormal (H := Xbar) e) U ∧ ¬ TrivOn (MulAut.conjNormal (H := Xbar) e) V)
    {S : Subgroup M} (hS : InvTwo Abar Ybar S) : S ≤ Subgroup.centralizer (Abar : Set M) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hSY, hAS, hS2⟩ := hS
  have hA3 : ∀ g ∈ Abar, g ^ 3 = 1 := hset.isElemAbelian.2
  obtain ⟨E, hEA, hE9, hEa⟩ := exists_plane hset
  set W : Subgroup M := S ⊓ Xbar with hW
  have hW2 : IsPGroup 2 W := hS2.to_le inf_le_left
  have hW3 : ¬ 3 ∣ Nat.card W := by
    obtain ⟨m, hm⟩ := hW2.exists_card_eq
    rw [hm]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    norm_num at this
  have hEW : E ≤ Subgroup.normalizer (W : Set M) :=
    Late.le_normalizer_inf (hEA.trans hAS)
      (by rw [Subgroup.normalizer_eq_top (H := Xbar)]; exact le_top)
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
    3 Nat.prime_three E W (fun g => Subtype.ext (by simpa using hA3 g (hEA g.2))) hE9 hW3 hEW
  have hWbot : W = ⊥ := by
    rw [hgen, eq_bot_iff]
    refine iSup₂_le fun g hg => ?_
    intro w hw
    obtain ⟨hwW, hwC⟩ := Subgroup.mem_inf.mp hw
    obtain ⟨hwS, hwX⟩ := Subgroup.mem_inf.mp hwW
    have hgA : (g : M) ∈ Abar := hEA g.2
    have hga : (g : M) ∉ Subgroup.zpowers abar := by
      intro h
      apply hg
      have hmem : (g : M) ∈ E ⊓ Subgroup.zpowers abar := Subgroup.mem_inf.mpr ⟨g.2, h⟩
      rw [hEa, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    obtain ⟨h1, h2⟩ := hdiag g hgA hga
    set σ := MulAut.conjNormal (H := Xbar) (g : M) with hσ
    have hσ3 : σ ^ 3 = 1 := by rw [hσ, ← map_pow, hA3 g hgA, map_one]
    have hfix : σ ⟨w, hwX⟩ = ⟨w, hwX⟩ := by
      apply Subtype.ext
      rw [hσ, MulAut.conjNormal_apply]
      have hc : w * g = g * w := Subgroup.mem_centralizer_singleton_iff.mp hwC
      show (g : M) * w * (g : M)⁻¹ = w
      rw [← hc, mul_inv_cancel_right]
    obtain ⟨m, hm⟩ := hW2 ⟨w, hwW⟩
    have hwk : (⟨w, hwX⟩ : ↥Xbar) ^ (2 ^ m) = 1 := by
      apply Subtype.ext
      simpa using congrArg Subtype.val hm
    have hw1 := hP.eq_one_of_fixed_both hσ3 hσ3 h1 h2 hfix hfix hwk
      (Nat.Coprime.pow_left m (by norm_num))
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hw1
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro ε hε
  have hsY := hSY hs
  rw [hset.eq_sup, ← SetLike.mem_coe, Subgroup.normal_mul Xbar Rbar] at hsY
  obtain ⟨x, hx, r, hr, hxr⟩ := hsY
  change x * r = s at hxr
  have her : r * ε = ε * r := (Subgroup.mem_centralizer_iff.mp (hset.le_centralizer_R hr) ε hε).symm
  have hεS : ε * s * ε⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp (hAS hε) s).mp hs
  have hmem : s⁻¹ * (ε * s * ε⁻¹) ∈ W := by
    refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hs) hεS, ?_⟩
    have h : s⁻¹ * (ε * s * ε⁻¹) = r⁻¹ * (x⁻¹ * (ε * x * ε⁻¹)) * r := by
      rw [← hxr]
      calc (x * r)⁻¹ * (ε * (x * r) * ε⁻¹) = r⁻¹ * (x⁻¹ * (ε * x * ε⁻¹)) * (ε * r * ε⁻¹) := by
            group
        _ = r⁻¹ * (x⁻¹ * (ε * x * ε⁻¹)) * r := by
            rw [← her, mul_inv_cancel_right]
    rw [h]
    have hεx : ε * x * ε⁻¹ ∈ Xbar := hXn.conj_mem x hx ε
    exact hXn.conj_mem _ (mul_mem (inv_mem hx) hεx) r⁻¹ |> fun h' => by simpa using h'
  rw [hWbot, Subgroup.mem_bot] at hmem
  have h : ε * s * ε⁻¹ = s := by
    calc ε * s * ε⁻¹ = s * (s⁻¹ * (ε * s * ε⁻¹)) := by group
      _ = s := by rw [hmem, mul_one]
  calc ε * s = ε * s * ε⁻¹ * ε := by group
    _ = s * ε := by rw [h]

end Wales1411W.HJA6A6

open Wales1411W Wales1411W.HJA6A6 Res9Pair in
theorem ks1411HJCoreA6A6 : KS1411HJCoreA6A6 := by
  intro M _ _ Ybar Abar Xbar Rbar abar hset hX S T hS hT hST hsupp
  exfalso
  haveI := HJInner.normal_X hset
  haveI := hset.perfect
  obtain ⟨U, V, hP⟩ := exists_isPair hX
  have hnot : ∀ e ∈ Abar, ¬ Ybar ≤ Subgroup.centralizer ({e} : Set M) ∨ e ∈ Subgroup.zpowers abar :=
    fun e heA => by
      by_cases h : Ybar ≤ Subgroup.centralizer ({e} : Set M)
      · exact Or.inr (hset.mem_zpowers e heA h)
      · exact Or.inl h
  by_cases hI : ∃ e ∈ Abar, e ∉ Subgroup.zpowers abar ∧
      (TrivOn (MulAut.conjNormal (H := Xbar) e) U ∨ TrivOn (MulAut.conjNormal (H := Xbar) e) V)
  · obtain ⟨e, heA, hea, hU | hV⟩ := hI
    · have heY : ¬ Ybar ≤ Subgroup.centralizer ({e} : Set M) := fun h =>
        hea (hset.mem_zpowers e heA h)
      exact false_of_trivOn hset hP.symm heA hea hU hS.prop hT.prop hST (hsupp e heA heY)
    · have heY : ¬ Ybar ≤ Subgroup.centralizer ({e} : Set M) := fun h =>
        hea (hset.mem_zpowers e heA h)
      exact false_of_trivOn hset hP heA hea hV hS.prop hT.prop hST (hsupp e heA heY)
  · push Not at hI
    have hdiag : ∀ e ∈ Abar, e ∉ Subgroup.zpowers abar →
        ¬ TrivOn (MulAut.conjNormal (H := Xbar) e) U ∧
          ¬ TrivOn (MulAut.conjNormal (H := Xbar) e) V := fun e heA hea => hI e heA hea
    have hSC := le_centralizer_of_diag hset hP hdiag hS.prop
    have hTC := le_centralizer_of_diag hset hP hdiag hT.prop
    have hYC : Ybar ≤ Subgroup.centralizer (Abar : Set M) := hST ▸ sup_le hSC hTC
    have hnle : ¬ Abar ≤ Subgroup.zpowers abar := fun hle => by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hc := Subgroup.card_le_of_le hle
      rw [hset.card_A, Nat.card_zpowers,
        orderOf_eq_prime (hset.isElemAbelian.2 abar hset.mem_A) hset.ne_one] at hc
      norm_num at hc
    obtain ⟨e, heA, hea⟩ := SetLike.not_le_iff_exists.mp hnle
    apply hea
    apply hset.mem_zpowers e heA
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hYC hy) e heA).symm

end CFSG.RankThree.PartTwo.Sec14
