module

public import CFSG.Quasithin.Background.G8Basic
public import CFSG.Quasithin.Background.A1bPGroups
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

@[expose] def lambdaSubgroup {H : Type*} [Group H] (K : Subgroup H) : Subgroup H :=
  Subgroup.closure {x : H | x ∈ K ∧ (orderOf x).Prime}

@[expose] def IsTheta (H : Type*) [Group H] (θ : Subgroup H) : Prop :=
  ∃ θd : ℕ → Subgroup H,
    (∀ d ∈ (Nat.card (CFSG.fittingSubgroup H)).primeFactors,
        θd d ≤ CFSG.pCore d H ∧ IsSupercritical d ((θd d).subgroupOf (CFSG.pCore d H))) ∧
    θ = CFSG.layer H ⊔ ⨆ d ∈ (Nat.card (CFSG.fittingSubgroup H)).primeFactors, θd d

section Lambda

variable {H : Type*} [Group H]

theorem lambdaSubgroup_le (K : Subgroup H) : lambdaSubgroup K ≤ K :=
  (Subgroup.closure_le K).mpr fun _ hx => hx.1

theorem lambdaSubgroup_mono {K K' : Subgroup H} (h : K ≤ K') :
    lambdaSubgroup K ≤ lambdaSubgroup K' :=
  Subgroup.closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

theorem lambdaSubgroup_le_iff {K X : Subgroup H} :
    lambdaSubgroup K ≤ X ↔ ∀ x ∈ K, (orderOf x).Prime → x ∈ X :=
  ⟨fun h _ hx hp => h (Subgroup.subset_closure ⟨hx, hp⟩),
    fun h => (Subgroup.closure_le X).mpr fun _ hx => h _ hx.1 hx.2⟩

theorem mem_lambdaSubgroup {K : Subgroup H} {x : H} (hx : x ∈ K) (hp : (orderOf x).Prime) :
    x ∈ lambdaSubgroup K :=
  Subgroup.subset_closure ⟨hx, hp⟩

end Lambda

namespace G8

section Finite

variable {H : Type*} [Group H] [Finite H]

theorem le_pCore_of_le_fitting {p : ℕ} [Fact p.Prime] {T : Subgroup H}
    (hTF : T ≤ CFSG.fittingSubgroup H) (hT : IsPGroup p T) : T ≤ CFSG.pCore p H := by
  set F := CFSG.fittingSubgroup H with hF
  have hT' : IsPGroup p (T.subgroupOf F) := hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTF).symm
  obtain ⟨Q, hQ⟩ := hT'.exists_le_sylow
  have h1 : (Q : Subgroup F).map F.subtype ≤ CFSG.pCore p H :=
    Sylow.map_le_pCore inferInstance inferInstance p Q
  intro x hx
  exact h1 ⟨⟨x, hTF hx⟩, hQ hx, rfl⟩

theorem fitting_odd (h : CFSG.pCore 2 H = ⊥) : Odd (Nat.card (CFSG.fittingSubgroup H)) := by
  by_contra hodd
  have h2 : 2 ∣ Nat.card (CFSG.fittingSubgroup H) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := CFSG.fittingSubgroup H) 2 h2
  have hord : orderOf (x : H) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
  have hT : IsPGroup 2 (Subgroup.zpowers (x : H)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
  have hle : Subgroup.zpowers (x : H) ≤ CFSG.fittingSubgroup H :=
    Subgroup.zpowers_le.mpr x.2
  have := le_pCore_of_le_fitting hle hT (Subgroup.mem_zpowers (x : H))
  rw [h, Subgroup.mem_bot] at this
  rw [this, orderOf_one] at hord
  omega

theorem centralizes_of_centralizes_orderP {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Q : Subgroup H}
    (hQ : IsPGroup p Q) {g : H} (hg : g ∈ Subgroup.normalizer (Q : Set H))
    (hcop : (orderOf g).Coprime p) (hΩ : ∀ y ∈ Q, orderOf y = p → g * y = y * g) :
    ∀ y ∈ Q, g * y = y * g := by
  have hK : Subgroup.zpowers g ≤ Subgroup.normalizer (Q : Set H) := Subgroup.zpowers_le.mpr hg
  set α : MulAut Q := conjAut hK ⟨g, Subgroup.mem_zpowers g⟩ with hα
  obtain ⟨X, hXs, hXker⟩ := exists_isSupercritical_faithful (p := p) hp2 hQ
  have hαord : (orderOf α).Coprime p := by
    have h1 : orderOf α ∣ orderOf g := by
      have := orderOf_map_dvd (conjAut hK) (⟨g, Subgroup.mem_zpowers g⟩ : Subgroup.zpowers g)
      rwa [Subgroup.orderOf_mk] at this
    exact Nat.Coprime.coprime_dvd_left h1 hcop
  have hαfix : ∀ x : Q, x ∈ X → α x = x := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1, map_one]
    · have hxp : x ^ p = 1 := hXs.pow_eq_one x hx
      have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
      have hxo' : orderOf ((x : Q) : H) = p := by rw [Subgroup.orderOf_coe]; exact hxo
      have hcomm := hΩ _ x.2 hxo'
      apply Subtype.ext
      rw [hα, conjAut_apply_coe]
      calc g * ((x : Q) : H) * g⁻¹ = ((x : Q) : H) * g * g⁻¹ := by rw [hcomm]
        _ = ((x : Q) : H) := by simp
  have hα1 : α = 1 := hXker α hαord fun x hx => by
    rw [hαfix x hx]; simp
  intro y hy
  have := congrArg (fun β : MulAut Q => ((β ⟨y, hy⟩ : Q) : H)) hα1
  simp only [hα, conjAut_apply_coe] at this
  have h5 : g * y * g⁻¹ = y := this
  calc g * y = g * y * g⁻¹ * g := by group
    _ = y * g := by rw [h5]

theorem centralizes_of_centralizes_lambda {N C : Subgroup H} (hN : Group.IsNilpotent N)
    (hNodd : Odd (Nat.card N)) (hC : IsPGroup 2 C) (hCN : C ≤ Subgroup.normalizer (N : Set H))
    (hΛ : C ≤ Subgroup.centralizer (lambdaSubgroup N : Set H)) :
    C ≤ Subgroup.centralizer (N : Set H) := by
  intro c hc
  have htop : (⊤ : Subgroup N) = ⨆ d : (Nat.card N).primeFactors.attach, CFSG.pCore d.1.1 N := by
    rw [← CFSG.fitting_eq_top_of_nilpotent N]
    exact CFSG.fitting_eq_sup_pCore N
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hC ⟨c, hc⟩
  have hordc : orderOf c = 2 ^ k := by rw [← Subgroup.orderOf_mk c hc]; exact hk
  have hcN : c ∈ Subgroup.normalizer (N : Set H) := hCN hc
  have key : ∀ d ∈ (Nat.card N).primeFactors, ∀ z : N, z ∈ CFSG.pCore d N →
      c * (z : H) = (z : H) * c := by
    intro d hd z hz
    have hdp : d.Prime := Nat.prime_of_mem_primeFactors hd
    have : Fact d.Prime := ⟨hdp⟩
    have hd2 : d ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hd))
    have hQp : IsPGroup d (pCoreOf d N) := pCoreOf_isPGroup d N
    have hcQ : c ∈ Subgroup.normalizer (pCoreOf d N : Set H) :=
      normalizer_le_normalizer_pCoreOf d N hcN
    have hcop : (orderOf c).Coprime d := by
      rw [hordc]
      exact Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hdp).mpr (Ne.symm hd2))
    have hΩ : ∀ y ∈ pCoreOf d N, orderOf y = d → c * y = y * c := by
      intro y hy hyo
      have hyN : y ∈ N := pCoreOf_le d N hy
      have hyΛ : y ∈ lambdaSubgroup N := mem_lambdaSubgroup hyN (hyo ▸ hdp)
      exact (Subgroup.mem_centralizer_iff.mp (hΛ hc) y hyΛ).symm
    have hz' : ((z : N) : H) ∈ pCoreOf d N := by
      exact ⟨z, by exact hz, rfl⟩
    exact centralizes_of_centralizes_orderP hd2 hQp hcQ hcop hΩ _ hz'
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hmem : (⟨y, hy⟩ : N) ∈ (⊤ : Subgroup N) := Subgroup.mem_top _
  rw [htop] at hmem
  have hle : (⨆ d : (Nat.card N).primeFactors.attach, CFSG.pCore d.1.1 N) ≤
      (Subgroup.centralizer {c}).comap N.subtype :=
    iSup_le fun d z hz => by
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      exact (key d.1.1 d.1.2 z hz).symm
  have := hle hmem
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at this
  exact this

theorem centralizer_generalizedFitting_le_fitting (H : Type*) [Group H] [Finite H] :
    Subgroup.centralizer (CFSG.generalizedFitting H : Set H) ≤ CFSG.fittingSubgroup H := by
  have := CFSG.ComponentClassification.GeneralizedFitting.centralizer_le_fitting H
  rw [← CFSG.generalizedFitting_eq_componentClassification] at this
  exact this

theorem fitting_layer_commute (H : Type*) [Group H] [Finite H] :
    ∀ f ∈ CFSG.fittingSubgroup H, ∀ e ∈ CFSG.layer H, Commute f e := by
  have h := CFSG.ComponentClassification.GeneralizedFitting.fitting_layer_commute H
  rw [← CFSG.layer_eq_componentClassification] at h
  have h2 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  intro f hf e he
  exact (Subgroup.mem_centralizer_iff.mp (h2 hf) e he).symm

theorem g8_9_core (hO2 : CFSG.pCore 2 H = ⊥) {X U : Subgroup H}
    (hXF : X ≤ CFSG.generalizedFitting H) (hEX : CFSG.layer H ≤ X)
    (hΛ : lambdaSubgroup (CFSG.fittingSubgroup H ⊓ Subgroup.centralizer (X : Set H)) ≤ X)
    (hU : IsPGroup 2 U) (hUX : U ≤ Subgroup.normalizer (X : Set H)) :
    U ⊓ Subgroup.centralizer (X : Set H) = ⊥ := by
  set F := CFSG.fittingSubgroup H with hF
  set E := CFSG.layer H with hE
  have hFodd : Odd (Nat.card F) := fitting_odd hO2
  have hFn : Group.IsNilpotent F := inferInstance
  have hFnorm : F.Normal := inferInstance
  have hcomm : ∀ f ∈ F, ∀ e ∈ E, Commute f e := fitting_layer_commute H
  set Y := X ⊓ F with hY
  have hYX : Y ≤ X := inf_le_left
  have hYF : Y ≤ F := inf_le_right
  have hdec : ∀ x ∈ X, ∃ f ∈ Y, ∃ e ∈ E, x = f * e := by
    intro x hx
    have hx' : x ∈ (↑(F ⊔ E) : Set H) := hXF hx
    rw [Subgroup.normal_mul] at hx'
    obtain ⟨f, hf, e, he, rfl⟩ := Set.mem_mul.mp hx'
    refine ⟨f, ⟨?_, hf⟩, e, he, rfl⟩
    have := X.mul_mem hx (X.inv_mem (hEX he))
    simpa using this
  have hCFY : F ⊓ Subgroup.centralizer (Y : Set H) ≤ Subgroup.centralizer (X : Set H) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨f, hf, e, he, rfl⟩ := hdec x hx
    have h1 : f * z = z * f := Subgroup.mem_centralizer_iff.mp hz.2 f hf
    have h2 : e * z = z * e := (hcomm z hz.1 e he).eq.symm
    calc f * e * z = f * (e * z) := mul_assoc _ _ _
      _ = f * (z * e) := by rw [h2]
      _ = (f * z) * e := (mul_assoc _ _ _).symm
      _ = z * f * e := by rw [h1]
      _ = z * (f * e) := mul_assoc _ _ _
  set V := U ⊓ Subgroup.centralizer (E : Set H) with hV
  have hVF : V ⊓ Subgroup.centralizer (F : Set H) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have hv1 : v ∈ F := by
      apply centralizer_generalizedFitting_le_fitting H
      show v ∈ Subgroup.centralizer ((F ⊔ E : Subgroup H) : Set H)
      rw [centralizer_sup]
      exact ⟨hv.2, hv.1.2⟩
    exact Subgroup.mem_bot.mpr (eq_one_of_mem_of_odd hU hFodd hv.1.1 hv1)
  set C := V ⊓ Subgroup.centralizer (Y : Set H) with hC
  have hC2 : IsPGroup 2 C := hU.to_le (inf_le_left.trans inf_le_left)
  have hCF : C ≤ Subgroup.normalizer (F : Set H) := Subgroup.le_normalizer_of_normal
  have hCY : C ≤ Subgroup.centralizer (Y : Set H) := inf_le_right
  have hCfaith : C ⊓ Subgroup.centralizer (F : Set H) = ⊥ :=
    le_bot_iff.mp (hVF ▸ inf_le_inf_right _ inf_le_left)
  have h84 := g8_4_of hFn hFodd hC2 hCF hYF hCY hCfaith
  set N := F ⊓ Subgroup.centralizer (X : Set H) with hN
  have hNeq : N = F ⊓ Subgroup.centralizer (Y : Set H) :=
    le_antisymm (inf_le_inf_left _ (Subgroup.centralizer_le hYX)) (le_inf inf_le_left hCFY)
  have hNnil : Group.IsNilpotent N := by
    have := hFn
    exact (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : N ≤ F))).mp
      inferInstance
  have hNodd : Odd (Nat.card N) :=
    Odd.of_dvd_nat hFodd (Subgroup.card_dvd_of_le inf_le_left)
  have hNnorm : ∀ g ∈ Subgroup.normalizer (X : Set H), g ∈ Subgroup.normalizer (N : Set H) := by
    have key : ∀ g ∈ Subgroup.normalizer (X : Set H), ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
      intro g hg n hn
      exact ⟨hFnorm.conj_mem n hn.1 g,
        (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_centralizer X hg) n).mp hn.2⟩
    intro g hg
    exact mem_normalizer_of_conj_mem (key g hg) (fun n hn => by
      simpa using key g⁻¹ (Subgroup.inv_mem _ hg) n hn)
  have hCN : C ≤ Subgroup.normalizer (N : Set H) := fun c hc => hNnorm c (hUX hc.1.1)
  have hΛY : lambdaSubgroup N ≤ Y := le_inf hΛ ((lambdaSubgroup_le N).trans inf_le_left)
  have hCΛ : C ≤ Subgroup.centralizer (lambdaSubgroup N : Set H) :=
    hCY.trans (Subgroup.centralizer_le hΛY)
  have hCN' : C ≤ Subgroup.centralizer (N : Set H) :=
    centralizes_of_centralizes_lambda hNnil hNodd hC2 hCN hCΛ
  have hCbot : C = ⊥ := by
    rw [eq_bot_iff, ← h84]
    exact le_inf le_rfl (by rw [← hNeq]; exact hCN')
  rw [eq_bot_iff]
  intro u hu
  have : u ∈ C := ⟨⟨hu.1, Subgroup.centralizer_le hEX hu.2⟩, Subgroup.centralizer_le hYX hu.2⟩
  rw [hCbot] at this
  exact this

end Finite

end G8

section Theta

variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
theorem IsTheta.layer_le {θ : Subgroup H} (h : IsTheta H θ) : CFSG.layer H ≤ θ := by
  obtain ⟨θd, -, rfl⟩ := h
  exact le_sup_left

theorem IsTheta.le_generalizedFitting {θ : Subgroup H} (h : IsTheta H θ) :
    θ ≤ CFSG.generalizedFitting H := by
  obtain ⟨θd, hθd, rfl⟩ := h
  refine sup_le le_sup_right (iSup₂_le fun d hd => ?_)
  have hdp : d.Prime := Nat.prime_of_mem_primeFactors hd
  have : Fact d.Prime := ⟨hdp⟩
  exact (hθd d hd).1.trans ((CFSG.pCore_le_fitting H d).trans le_sup_left)

omit [Finite H] in
theorem IsTheta.normal {θ : Subgroup H} (h : IsTheta H θ) : θ.Normal := by
  obtain ⟨θd, hθd, rfl⟩ := h
  have hE : (CFSG.layer H).Normal := by
    rw [CFSG.layer_eq_componentClassification]
    exact CFSG.ComponentClassification.Layer.normal H
  have hd : ∀ d ∈ (Nat.card (CFSG.fittingSubgroup H)).primeFactors, (θd d).Normal := by
    intro d hd
    obtain ⟨hle, hsc⟩ := hθd d hd
    have hchar := hsc.characteristic
    have h1 := normalizer_le_normalizer_map_of_characteristic (H := CFSG.pCore d H)
      ((θd d).subgroupOf (CFSG.pCore d H))
    rw [Subgroup.map_subgroupOf_eq_of_le hle] at h1
    have h2 : Subgroup.normalizer ((CFSG.pCore d H : Subgroup H) : Set H) = ⊤ :=
      Subgroup.normalizer_eq_top (CFSG.pCore d H)
    rw [h2] at h1
    exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h1)
  have : (⨆ d ∈ (Nat.card (CFSG.fittingSubgroup H)).primeFactors, θd d).Normal :=
    Subgroup.biSup_normal _ _ hd
  exact Subgroup.sup_normal _ _

theorem IsTheta.lambda_le {θ : Subgroup H} (h : IsTheta H θ) :
    lambdaSubgroup (CFSG.fittingSubgroup H ⊓ Subgroup.centralizer (θ : Set H)) ≤ θ := by
  obtain ⟨θd, hθd, rfl⟩ := h
  rw [lambdaSubgroup_le_iff]
  rintro x ⟨hxF, hxC⟩ hxp
  set r := orderOf x with hr
  have : Fact r.Prime := ⟨hxp⟩
  have hrmem : r ∈ (Nat.card (CFSG.fittingSubgroup H)).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hxp, Subgroup.orderOf_dvd_natCard _ hxF, Nat.card_pos.ne'⟩
  have hxpc : x ∈ CFSG.pCore r H := by
    have hT : IsPGroup r (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ← hr, pow_one])
    exact G8.le_pCore_of_le_fitting (Subgroup.zpowers_le.mpr hxF) hT (Subgroup.mem_zpowers x)
  obtain ⟨hle, hsc⟩ := hθd r hrmem
  have hθr : θd r ≤ CFSG.layer H ⊔ ⨆ d ∈ (Nat.card (CFSG.fittingSubgroup H)).primeFactors, θd d :=
    le_sup_of_le_right (le_iSup₂ (f := fun d
      (_ : d ∈ (Nat.card (CFSG.fittingSubgroup H)).primeFactors) => θd d) r hrmem)
  set y : CFSG.pCore r H := ⟨x, hxpc⟩ with hy
  have hycent : y ∈ Subgroup.centralizer (((θd r).subgroupOf (CFSG.pCore r H) : Subgroup _) :
      Set (CFSG.pCore r H)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    apply Subtype.ext
    have hw' : (w : H) ∈ θd r := hw
    exact Subgroup.mem_centralizer_iff.mp hxC (w : H) (hθr hw')
  have hyord : orderOf y = r := by rw [← Subgroup.orderOf_coe]
  have := hsc.mem_of_orderOf_eq y hycent hyord
  exact hθr this

end Theta

end CFSG.Quasithin
