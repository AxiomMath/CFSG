module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3TwoMod
import CFSG.RankThree.PartTwo.Late.Transitivity
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.PartTwo.Sec19.Step1919NarrowRank
import CFSG.LocalAnalysis.SignalizerFunctor.Maximality

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof17Res7

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projImage)

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

section Group

variable {M : Type*} [Group M]

theorem mem_centralizer_conj {R : Subgroup M} {g x : M} (hg : g ∈ Subgroup.normalizer (R : Set M))
    (hx : x ∈ Subgroup.centralizer (R : Set M)) :
    g * x * g⁻¹ ∈ Subgroup.centralizer (R : Set M) := by
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro r hr
  have hr' : g⁻¹ * r * g⁻¹⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) r).mp hr
  have h := hx _ hr'
  calc r * (g * x * g⁻¹) = g * ((g⁻¹ * r * g⁻¹⁻¹) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * r * g⁻¹⁻¹)) * g⁻¹ := by rw [h]
    _ = g * x * g⁻¹ * r := by group

theorem normalizer_le_normalizer_centralizer [Finite M] (R : Subgroup M) :
    Subgroup.normalizer (R : Set M) ≤
      Subgroup.normalizer ((Subgroup.centralizer (R : Set M) : Subgroup M) : Set M) := fun _ hg =>
  Subgroup.mem_normalizer_fintype fun _ hx => mem_centralizer_conj hg hx

end Group

variable {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)

include hτ1 in
theorem le_pCoreOf_centralizer_d (hK : PiField π p f K) (hp2 : p ≠ 2)
    {dM cM : projImage (slPi π 3 (p ^ f) K)}
    (hdM : (dM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagTau hτ))
    (hcM : (cM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (cycThree : GL (Fin 3) K))
    {R : Subgroup (projImage (slPi π 3 (p ^ f) K))} (hR2 : IsPGroup 2 R)
    (hcR : cM ∈ Subgroup.normalizer (R : Set (projImage (slPi π 3 (p ^ f) K))))
    {z : projImage (slPi π 3 (p ^ f) K)} (hzR : z ∈ R)
    (hzC : z ∈ Subgroup.centralizer (R : Set (projImage (slPi π 3 (p ^ f) K))))
    (hzd : z * dM = dM * z) (hz1 : z ≠ 1) :
    R ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer {dM}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  set t₁ := tM hK hp2 _ isTInv_tOne with ht₁
  set t₂ := tM hK hp2 _ isTInv_tTwo with ht₂
  set t₃ := tM hK hp2 _ isTInv_tThree with ht₃
  have h12 : t₁ * t₂ = t₃ := tM_one_mul_tM_two hK hp2
  obtain ⟨hc1, hc2, hc3⟩ := cM_conj_tM hK hp2 hcM
  set Zd := R ⊓ Subgroup.centralizer (R : Set (projImage (slPi π 3 (p ^ f) K))) ⊓
    Subgroup.centralizer {dM} with hZd
  have hzZ : z ∈ Zd := ⟨⟨hzR, hzC⟩, Subgroup.mem_centralizer_singleton_iff.mpr hzd⟩
  have hz2 : IsPGroup 2 (Subgroup.zpowers z) :=
    (hR2.to_le (Subgroup.zpowers_le.mpr hzR) : IsPGroup 2 (Subgroup.zpowers z))
  have h2z : 2 ∣ Nat.card (Subgroup.zpowers z) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hz2
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, Subgroup.card_eq_one, Subgroup.zpowers_eq_bot] at hk
      exact hz1 hk
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨⟨z₀, hz₀⟩, hz₀o⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers z) 2 h2z
  have hz₀o' : orderOf z₀ = 2 := (Subgroup.orderOf_mk z₀ hz₀).symm.trans hz₀o
  have hz₀Z : z₀ ∈ Zd := Subgroup.zpowers_le.mpr hzZ hz₀
  have hz₀2 : z₀ ^ 2 = 1 := by rw [← hz₀o', pow_orderOf_eq_one]
  have hz₀1 : z₀ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz₀o'
    omega
  have hz₀d : z₀ * dM = dM * z₀ := Subgroup.mem_centralizer_singleton_iff.mp hz₀Z.2
  obtain ⟨A₀, -, hA₀⟩ := exists_lift z₀
  have hz₀2' : z₀ ^ 2 ^ 1 = 1 := by rw [pow_one]; exact hz₀2
  have hoff₀ := offDiag_of_comm_d_of_pow hτ hτ1 hdM hz₀d hz₀2' hA₀
  have hz₀t : IsTM hK hp2 z₀ := isTM_of_offDiag hK hp2 hz₀2 hz₀1 hA₀ hoff₀
  have hcC : ∀ x ∈ Subgroup.centralizer (R : Set (projImage (slPi π 3 (p ^ f) K))),
      cM * x * cM⁻¹ ∈ Subgroup.centralizer (R : Set (projImage (slPi π 3 (p ^ f) K))) :=
    fun x hx => mem_centralizer_conj hcR hx
  have hz₀C : z₀ ∈ Subgroup.centralizer (R : Set (projImage (slPi π 3 (p ^ f) K))) := hz₀Z.1.2
  have ht12 : t₁ ∈ Subgroup.centralizer (R : Set (projImage (slPi π 3 (p ^ f) K))) ∧
      t₂ ∈ Subgroup.centralizer (R : Set (projImage (slPi π 3 (p ^ f) K))) := by
    rcases hz₀t with h | h | h
    · rw [h] at hz₀C
      have h2 := hcC _ hz₀C
      rw [hc1] at h2
      exact ⟨hz₀C, h2⟩
    · rw [h] at hz₀C
      have h3 := hcC _ hz₀C
      rw [hc2] at h3
      have h1 := hcC _ h3
      rw [hc3] at h1
      exact ⟨h1, hz₀C⟩
    · rw [h] at hz₀C
      have h1 := hcC _ hz₀C
      rw [hc3] at h1
      have h2 := hcC _ h1
      rw [hc1] at h2
      exact ⟨h1, h2⟩
  set D : Subgroup (projImage (slPi π 3 (p ^ f) K)) :=
    Subgroup.centralizer {t₁} ⊓ Subgroup.centralizer {t₂} with hD
  have hRD : R ≤ D := fun r hr =>
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp ht12.1 r hr),
     Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp ht12.2 r hr)⟩
  have hDoff : ∀ x ∈ D, ∀ A : GL (Fin 3) K,
      ProjGenLinGroup.mk A = (x : ProjGenLinGroup (Fin 3) K) →
        ∀ i j : Fin 3, i ≠ j → (A : Matrix (Fin 3) (Fin 3) K) i j = 0 := fun x hx A hA =>
    offDiag_of_comm_t hK hp2 (Subgroup.mem_centralizer_singleton_iff.mp hx.1)
      (Subgroup.mem_centralizer_singleton_iff.mp hx.2) hA
  have hDcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := by
    intro x hx y hy
    obtain ⟨A, -, hA⟩ := exists_lift x
    obtain ⟨B, -, hB⟩ := exists_lift y
    exact comm_of_offDiag_offDiag hA hB (hDoff x hx A hA) (hDoff y hy B hB)
  have hDd : D ≤ Subgroup.centralizer {dM} := by
    intro x hx
    obtain ⟨A, -, hA⟩ := exists_lift x
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact comm_of_offDiag hA (hDoff x hx A hA)
      (hdM.trans (by rw [diagTau_eq_diagUnits hτ (tau_ne_zero hτ)]))
  have hCD : Subgroup.centralizer {dM} ≤
      Subgroup.normalizer (D : Set (projImage (slPi π 3 (p ^ f) K))) := by
    intro g hg
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have hginv : g⁻¹ * dM = dM * g⁻¹ := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (inv_mem hg)
      exact this
    have hcommT : ∀ s, IsTM hK hp2 s → x * s = s * x := by
      intro s hs
      have e1 : x * t₁ = t₁ * x := Subgroup.mem_centralizer_singleton_iff.mp hx.1
      have e2 : x * t₂ = t₂ * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
      rcases hs with h | h | h
      · rw [h]; exact e1
      · rw [h]; exact e2
      · rw [h, ← ht₃, ← h12]
        calc x * (t₁ * t₂) = (x * t₁) * t₂ := by group
          _ = t₁ * (x * t₂) := by rw [e1]; group
          _ = t₁ * t₂ * x := by rw [e2]; group
    have key : ∀ t, IsTM hK hp2 t → (g * x * g⁻¹) * t = t * (g * x * g⁻¹) := by
      intro t ht
      have hs := isTM_conj_of_comm_d hτ hτ1 hK hp2 hdM hginv ht
      rw [inv_inv] at hs
      have h := hcommT _ hs
      calc g * x * g⁻¹ * t = g * (x * (g⁻¹ * t * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * t * g) * x) * g⁻¹ := by rw [h]
        _ = t * (g * x * g⁻¹) := by group
    exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr (key _ (Or.inl rfl)),
      Subgroup.mem_centralizer_singleton_iff.mpr (key _ (Or.inr (Or.inl rfl)))⟩
  have hRO : R ≤ CFSG.Open.pCoreOf 2 D := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hRD (fun x hx => ?_) hR2
    refine Subgroup.mem_normalizer_fintype fun r hr => ?_
    rw [hDcomm x hx r (hRD hr), mul_inv_cancel_right]
    exact hr
  have hOO : CFSG.Open.pCoreOf 2 D ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer {dM}) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 D).trans hDd)
      (hCD.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 D))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D)
  exact hRO.trans hOO

theorem map_pCoreOf_centralizer_le {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (Φ : G ≃* H) (x : G) :
    (CFSG.Open.pCoreOf 2 (Subgroup.centralizer {x})).map Φ.toMonoidHom ≤
      CFSG.Open.pCoreOf 2 (Subgroup.centralizer {Φ x}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).map _)
  · rintro _ ⟨y, hy, rfl⟩
    have hyC := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hyC ⊢
    change Φ y * Φ x = Φ x * Φ y
    rw [← map_mul, hyC, map_mul]
  · intro w hw
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    have hw' : Φ.symm w ∈ Subgroup.centralizer {x} := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hw ⊢
      apply Φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hw]
    have h1 := (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hw') y₀).mp hy₀
    refine ⟨Φ.symm w * y₀ * (Φ.symm w)⁻¹, h1, ?_⟩
    change Φ (Φ.symm w * y₀ * (Φ.symm w)⁻¹) = _
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    rfl

include hτ1 in
theorem exists_le_pCoreOf_model (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hp2 : p ≠ 2)
    {dM cM : projImage (slPi π 3 (p ^ f) K)}
    (hdM : (dM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagTau hτ))
    (hcM : (cM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (cycThree : GL (Fin 3) K))
    (hdc : dM * cM = cM * dM) (hdo : orderOf dM = 3) (hco : orderOf cM = 3)
    (hcd : cM ∉ Subgroup.zpowers dM) {R : Subgroup (projImage (slPi π 3 (p ^ f) K))}
    (hR2 : IsPGroup 2 R)
    (hER : Subgroup.zpowers dM ⊔ Subgroup.zpowers cM ≤
      Subgroup.normalizer (R : Set (projImage (slPi π 3 (p ^ f) K)))) :
    ∃ b ∈ Subgroup.zpowers dM ⊔ Subgroup.zpowers cM, b ≠ 1 ∧
      R ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer {b}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  set E := Subgroup.zpowers dM ⊔ Subgroup.zpowers cM with hE
  have hdE : dM ∈ E := Subgroup.mem_sup_left (Subgroup.mem_zpowers dM)
  have hcE : cM ∈ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers cM)
  have hd1 : dM ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hdo
    omega
  by_cases hR : R = ⊥
  · exact ⟨dM, hdE, hd1, by rw [hR]; exact bot_le⟩
  have hRnt : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).mpr hR
  have hZnt := hR2.center_nontrivial
  obtain ⟨⟨z₀, hz₀c⟩, hz₀1⟩ := exists_ne (1 : Subgroup.center R)
  set Z := R ⊓ Subgroup.centralizer (R : Set (projImage (slPi π 3 (p ^ f) K))) with hZ
  have hz₀Z : (z₀ : projImage (slPi π 3 (p ^ f) K)) ∈ Z := by
    refine ⟨z₀.2, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
    have := Subgroup.mem_center_iff.mp hz₀c ⟨r, hr⟩
    exact congrArg Subtype.val this
  have hZ1 : Z ≠ ⊥ := by
    intro hZ0
    rw [hZ0, Subgroup.mem_bot] at hz₀Z
    exact hz₀1 (Subtype.ext (Subtype.ext hz₀Z))
  have hEZ : E ≤ Subgroup.normalizer (Z : Set (projImage (slPi π 3 (p ^ f) K))) :=
    Late.le_normalizer_inf hER (hER.trans (normalizer_le_normalizer_centralizer R))
  have hE9 : Nat.card E = 9 := by
    rw [hE, Sec19.Step1919NarrowRank.card_sup_zpowers_of_orderOf _ hco hcd (by
      rintro _ ⟨k, rfl⟩
      exact ((Commute.zpow_left hdc k).eq)), Nat.card_zpowers, hdo]
  have hd3 : dM ^ 3 = 1 := by simpa [hdo] using pow_orderOf_eq_one dM
  have hc3 : cM ^ 3 = 1 := by simpa [hco] using pow_orderOf_eq_one cM
  have hEab : CFSG.Open.IsElemAbelian 3 E := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨i, j, hij⟩ := exists_zpow_mul_of_mem_sup hdc x.2
      obtain ⟨k, l, hkl⟩ := exists_zpow_mul_of_mem_sup hdc y.2
      change (x : projImage (slPi π 3 (p ^ f) K)) * y = y * x
      rw [hij, hkl]
      have hc := fun a b : ℤ => (Commute.zpow_zpow hdc a b).eq
      calc dM ^ i * cM ^ j * (dM ^ k * cM ^ l) = dM ^ i * (cM ^ j * dM ^ k) * cM ^ l := by group
        _ = dM ^ i * (dM ^ k * cM ^ j) * cM ^ l := by rw [← hc k j]
        _ = dM ^ k * dM ^ i * (cM ^ j * cM ^ l) := by group
        _ = dM ^ k * dM ^ i * (cM ^ l * cM ^ j) := by group
        _ = dM ^ k * (dM ^ i * cM ^ l) * cM ^ j := by group
        _ = dM ^ k * (cM ^ l * dM ^ i) * cM ^ j := by rw [hc i l]
        _ = dM ^ k * cM ^ l * (dM ^ i * cM ^ j) := by group
    · obtain ⟨i, j, rfl⟩ := exists_zpow_mul_of_mem_sup hdc hx
      rw [(Commute.zpow_zpow hdc i j).mul_pow, ← zpow_natCast, ← zpow_natCast,
        ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, mul_comm (j : ℤ),
        _root_.zpow_mul]
      simp [hd3, hc3]
  have hZ2 : IsPGroup 2 Z := hR2.to_le inf_le_left
  have hcop : Nat.Coprime 3 (Nat.card Z) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ2
    rw [hk]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 3 1
    Nat.prime_three E Z hEab (by rw [hE9]; norm_num) hEZ hcop
  obtain ⟨U, hU, hZU⟩ : ∃ U ∈ CFSG.Open.signalizerFunctorEk 3 1 E,
      Z ⊓ Subgroup.centralizer (U : Set (projImage (slPi π 3 (p ^ f) K))) ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    apply hZ1
    rw [← hgen]
    exact iSup₂_eq_bot.mpr hcon
  obtain ⟨hUE, hU3⟩ := hU
  have hUnt : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by rw [hU3]; norm_num)
  obtain ⟨⟨b, hbU⟩, hb1⟩ := exists_ne (1 : U)
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hUb : U = Subgroup.zpowers b := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbU) ?_).symm
    rw [hU3, pow_one, Nat.card_zpowers]
    have h1 : orderOf b ∣ 3 := by
      have := orderOf_dvd_natCard (⟨b, hbU⟩ : U)
      rwa [Subgroup.orderOf_mk, hU3, pow_one] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hb1'
    · rw [h]
  obtain ⟨⟨z, hzZ, hzU⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZU
  have hzb : (z : projImage (slPi π 3 (p ^ f) K)) * b = b * z :=
    (Subgroup.mem_centralizer_iff.mp hzU b hbU).symm
  have hz1' : (z : projImage (slPi π 3 (p ^ f) K)) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hbE : b ∈ E := hUE hbU
  set e : (⊤ : Subgroup (projImage (slPi π 3 (p ^ f) K))) ≃* projImage (slPi π 3 (p ^ f) K) :=
    Subgroup.topEquiv with he
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have htr := transitive_of_normal_form hK hq e hτ hτ1 (one_mem (glPi π 3 (p ^ f) K))
    (Subgroup.mem_top dM) (Subgroup.mem_top cM) (by rw [he, Subgroup.topEquiv_apply, hdM]; simp)
    (by rw [he, Subgroup.topEquiv_apply, hcM]; simp)
  obtain ⟨n, ⟨-, hnE⟩, hnb⟩ := htr b hbE hb1' dM hdE hd1
  set R' := R.map (MulAut.conj n).toMonoidHom with hR'
  have hR'2 : IsPGroup 2 R' := hR2.map _
  have hnE' : n⁻¹ ∈ Subgroup.normalizer (E : Set (projImage (slPi π 3 (p ^ f) K))) :=
    inv_mem hnE
  have hcR' : cM ∈ Subgroup.normalizer (R' : Set (projImage (slPi π 3 (p ^ f) K))) := by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨r, hr, rfl⟩ := hx
    have hc' : n⁻¹ * cM * n⁻¹⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hnE' cM).mp hcE
    have hr' := (Subgroup.mem_normalizer_iff.mp (hER hc') r).mp hr
    refine ⟨n⁻¹ * cM * n⁻¹⁻¹ * r * (n⁻¹ * cM * n⁻¹⁻¹)⁻¹, hr', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hz'R : n * z * n⁻¹ ∈ R' := ⟨z, hzZ.1, rfl⟩
  have hz'C : n * z * n⁻¹ ∈
      Subgroup.centralizer (R' : Set (projImage (slPi π 3 (p ^ f) K))) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨r, hr, rfl⟩
    have hzr := Subgroup.mem_centralizer_iff.mp hzZ.2 r hr
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc n * r * n⁻¹ * (n * z * n⁻¹) = n * (r * z) * n⁻¹ := by group
      _ = n * (z * r) * n⁻¹ := by rw [hzr]
      _ = n * z * n⁻¹ * (n * r * n⁻¹) := by group
  have hz'd : n * z * n⁻¹ * dM = dM * (n * z * n⁻¹) := by
    rw [← hnb]
    calc n * z * n⁻¹ * (n * b * n⁻¹) = n * (z * b) * n⁻¹ := by group
      _ = n * (b * z) * n⁻¹ := by rw [hzb]
      _ = n * b * n⁻¹ * (n * z * n⁻¹) := by group
  have hz'1 : n * z * n⁻¹ ≠ 1 := by
    intro h
    apply hz1'
    calc (z : projImage (slPi π 3 (p ^ f) K)) = n⁻¹ * (n * z * n⁻¹) * n := by group
      _ = 1 := by rw [h]; group
  have hR'O := le_pCoreOf_centralizer_d hτ hτ1 hK hp2 hdM hcM hR'2 hcR' hz'R hz'C hz'd hz'1
  refine ⟨b, hbE, hb1', fun r hr => ?_⟩
  have h1 : n * r * n⁻¹ ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer {dM}) := hR'O ⟨r, hr, rfl⟩
  have h2 := map_pCoreOf_centralizer_le (MulAut.conj n⁻¹) dM ⟨_, h1, rfl⟩
  have e1 : (MulAut.conj n⁻¹) dM = b := by
    rw [MulAut.conj_apply, ← hnb]
    group
  have e2 : (MulAut.conj n⁻¹).toMonoidHom (n * r * n⁻¹) = r := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [e1, e2] at h2
  exact h2

theorem fourGroup_model (hK : PiField π p f K) (hp2 : p ≠ 2)
    {dM cM : projImage (slPi π 3 (p ^ f) K)}
    (hdM : (dM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagTau hτ))
    (hcM : (cM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (cycThree : GL (Fin 3) K)) :
    ∃ R₀ : Subgroup (projImage (slPi π 3 (p ^ f) K)), IsPGroup 2 R₀ ∧
      Subgroup.zpowers dM ⊔ Subgroup.zpowers cM ≤
        Subgroup.normalizer (R₀ : Set (projImage (slPi π 3 (p ^ f) K))) ∧ R₀ ≠ ⊥ := by
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  set t₁ := tM hK hp2 _ isTInv_tOne with ht₁
  set t₂ := tM hK hp2 _ isTInv_tTwo with ht₂
  set t₃ := tM hK hp2 _ isTInv_tThree with ht₃
  have h12 : t₁ * t₂ = t₃ := tM_one_mul_tM_two hK hp2
  obtain ⟨hc1, hc2, hc3⟩ := cM_conj_tM hK hp2 hcM
  have hoff : ∀ t : GL (Fin 3) K, IsTInv t → ∀ i j : Fin 3, i ≠ j →
      (t : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
    intro t ht i j hij
    obtain ⟨a, b, c, rfl⟩ := isTInv_diagUnits ht
    rw [coe_diagUnits]
    exact diagonal_apply_ne _ hij
  have hdt : ∀ t (ht : IsTInv t), tM hK hp2 t ht * dM = dM * tM hK hp2 t ht := fun t ht =>
    comm_of_offDiag (coe_tM hK hp2 ht).symm (hoff t ht)
      (hdM.trans (by rw [diagTau_eq_diagUnits hτ (tau_ne_zero hτ)]))
  have ht12c : t₁ * t₂ = t₂ * t₁ := by
    obtain ⟨A, -, hA⟩ := exists_lift t₁
    exact comm_of_offDiag (coe_tM hK hp2 isTInv_tOne).symm (hoff _ isTInv_tOne)
      (coe_tM hK hp2 isTInv_tTwo)
  set R₀ := Subgroup.zpowers t₁ ⊔ Subgroup.zpowers t₂ with hR₀
  have h1sq : t₁ ^ 2 = 1 := tM_sq hK hp2 isTInv_tOne
  have h2sq : t₂ ^ 2 = 1 := tM_sq hK hp2 isTInv_tTwo
  refine ⟨R₀, fun x => ⟨1, Subtype.ext ?_⟩, ?_, ?_⟩
  · obtain ⟨i, j, hij⟩ := exists_zpow_mul_of_mem_sup ht12c x.2
    rw [Subgroup.coe_pow, hij, pow_one, (Commute.zpow_zpow ht12c i j).mul_pow, ← zpow_natCast,
      ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
      mul_comm (j : ℤ), _root_.zpow_mul]
    simp [h1sq, h2sq]
  · refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · refine Subgroup.mem_normalizer_fintype fun x hx => ?_
      obtain ⟨i, j, rfl⟩ := exists_zpow_mul_of_mem_sup ht12c hx
      have e1 : dM * t₁ * dM⁻¹ = t₁ := by rw [← hdt _ isTInv_tOne, mul_inv_cancel_right]
      have e2 : dM * t₂ * dM⁻¹ = t₂ := by rw [← hdt _ isTInv_tTwo, mul_inv_cancel_right]
      rw [show dM * (t₁ ^ i * t₂ ^ j) * dM⁻¹ = (dM * t₁ * dM⁻¹) ^ i * (dM * t₂ * dM⁻¹) ^ j by
        rw [conj_zpow, conj_zpow]; group, e1, e2]
      exact mul_mem (zpow_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers t₁)) i)
        (zpow_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers t₂)) j)
    · refine Subgroup.mem_normalizer_fintype fun x hx => ?_
      obtain ⟨i, j, rfl⟩ := exists_zpow_mul_of_mem_sup ht12c hx
      have hc2' : cM * t₂ * cM⁻¹ = t₁ * t₂ := hc2.trans h12.symm
      rw [show cM * (t₁ ^ i * t₂ ^ j) * cM⁻¹ = (cM * t₁ * cM⁻¹) ^ i * (cM * t₂ * cM⁻¹) ^ j by
        rw [conj_zpow, conj_zpow]; group, hc1, hc2']
      exact mul_mem (zpow_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers t₂)) i)
        (zpow_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers t₁))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers t₂))) j)
  · intro h
    have : t₁ ∈ R₀ := Subgroup.mem_sup_left (Subgroup.mem_zpowers t₁)
    rw [h, Subgroup.mem_bot] at this
    exact tM_ne_one hK hp2 isTInv_tOne this

end CFSG.RankThree.PartTwo.Sec17.Proof17Res7
