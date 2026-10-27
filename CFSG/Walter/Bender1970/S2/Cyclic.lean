module

public import CFSG.Walter.Bender1970.S2.OddFitting

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter
open scoped Pointwise commutatorElement MatrixGroups

theorem isCyclic_of_odd_card_dihedralGroup {n : ℕ} (R : Subgroup (DihedralGroup n))
    (hR : Odd (Nat.card R)) : IsCyclic R := by
  have hle : R ≤ Subgroup.zpowers (DihedralGroup.r 1) := by
    intro x hx
    rcases x with i | i
    · obtain ⟨k, rfl⟩ := ZMod.intCast_surjective i
      exact ⟨k, DihedralGroup.r_one_zpow k⟩
    · exfalso
      have h1 : orderOf (⟨DihedralGroup.sr i, hx⟩ : R) ∣ Nat.card R := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk, DihedralGroup.orderOf_sr] at h1
      exact (Nat.not_even_iff_odd.mpr hR) (even_iff_two_dvd.mpr h1)
  have : IsCyclic (R.subgroupOf (Subgroup.zpowers (DihedralGroup.r 1))) := Subgroup.isCyclic _
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom
    (MulEquiv.surjective _)

theorem odd_normal_subgroup_centralizer {L : Type} [Group L] [Finite L] [IsSimpleGroup L]
    (h2L : 2 ∣ Nat.card L) (hL : IsTypeL2 L ∨ IsTypeJR L) {ℓ : L} (hℓ : ℓ ^ 2 = 1)
    {R : Subgroup L} (hRodd : Odd (Nat.card R)) (hRC : R ≤ Subgroup.centralizer ({ℓ} : Set L))
    (hCR : Subgroup.centralizer ({ℓ} : Set L) ≤ Subgroup.normalizer (R : Set L)) :
    IsCyclic R ∧ (IsTypeL2Even L ∨ IsTypeJR L → R = ⊥) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd2 : ∀ P : Subgroup L, IsPGroup 2 P → R ≤ P → R = ⊥ := by
    intro P hP hRP
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨k, hk⟩ := hP ⟨x, hRP hx⟩
    have h1 : orderOf x ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    have h2 : orderOf x ∣ Nat.card R := by
      have := orderOf_dvd_natCard (⟨x, hx⟩ : R)
      rwa [Subgroup.orderOf_mk] at this
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left h2 (Nat.Coprime.pow_right k
        (Nat.coprime_two_right.mpr hRodd))) h1))
  have hbot : R = ⊥ → IsCyclic R ∧ (IsTypeL2Even L ∨ IsTypeJR L → R = ⊥) := by
    rintro rfl
    exact ⟨inferInstance, fun _ => rfl⟩
  by_cases hℓ1 : ℓ = 1
  · apply hbot
    have hRn : R.Normal := by
      rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
      intro x _
      apply hCR
      rw [hℓ1, Subgroup.mem_centralizer_singleton_iff, one_mul, mul_one]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal R with h | h
    · exact h
    · exfalso
      rw [← Subgroup.card_top (G := L), ← h] at h2L
      exact (Nat.not_even_iff_odd.mpr hRodd) (even_iff_two_dvd.mpr h2L)
  have hℓ2 : orderOf ℓ = 2 := orderOf_eq_prime hℓ hℓ1
  have heven : IsTypeL2Even L → R = ⊥ := by
    rintro ⟨f, hf, ⟨e⟩⟩
    have h1 := psl2_even_eq_bot_of_centralizer_le_normalizer hf (ℓ := e ℓ)
      (by rwa [MulEquiv.orderOf_eq]) (R := R.map e.toMonoidHom)
      (by rwa [Subgroup.card_map_of_injective e.injective])
      (by
        rw [← map_centralizer_singleton_mulEquiv, ← Subgroup.map_equiv_normalizer_eq]
        exact Subgroup.map_mono hCR)
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  have hJR : IsTypeJR L → R = ⊥ := by
    intro hJ
    obtain ⟨-, p, f, hp, M, hpodd, hf, h5, hMC, hMn, ⟨eM⟩, hCM⟩ := hJ.2.2 ℓ hℓ2
    have hcardF : 4 ≤ Nat.card (GaloisField p f) := by
      rw [GaloisField.card p f hf.ne']
      omega
    have : IsSimpleGroup PSL(2, GaloisField p f) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hcardF
    have : IsSimpleGroup M := eM.isSimpleGroup
    have hMnab : ∃ a b : M, a * b ≠ b * a := exists_mul_ne_mul_of_mulEquiv_psl2 hcardF eM
    have hMnormC : Subgroup.centralizer ({ℓ} : Set L) ≤ Subgroup.normalizer (M : Set L) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hMC).mp hMn
    have hRM : R ⊓ M = ⊥ := by
      have hn : ((R ⊓ M).subgroupOf M).Normal := by
        rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
        exact (le_inf (hMC.trans hCR) M.le_normalizer).trans
          Subgroup.inf_normalizer_le_normalizer_inf
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((R ⊓ M).subgroupOf M) with h | h
      · rw [eq_bot_iff]
        intro x hx
        have h1 : (⟨x, hx.2⟩ : M) ∈ (R ⊓ M).subgroupOf M := hx
        rw [h, Subgroup.mem_bot] at h1
        exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
      · exfalso
        have h1 : M ≤ R := by
          intro x hx
          have h2 : (⟨x, hx⟩ : M) ∈ (R ⊓ M).subgroupOf M := h ▸ Subgroup.mem_top _
          exact h2.1
        have h2M : 2 ∣ Nat.card M := (even_card_of_isSimpleGroup hMnab).two_dvd
        exact (Nat.not_even_iff_odd.mpr hRodd)
          (even_iff_two_dvd.mpr (h2M.trans (Subgroup.card_dvd_of_le h1)))
    have hcomm : ⁅R, M⁆ = ⊥ := by
      rw [← le_bot_iff, ← hRM, Subgroup.commutator_le]
      intro r hr m hm
      rw [commutatorElement_def]
      refine ⟨?_, ?_⟩
      · have h1 : r * m * r⁻¹ * m⁻¹ = r * (m * r⁻¹ * m⁻¹) := by group
        rw [h1]
        exact R.mul_mem hr
          ((Subgroup.mem_normalizer_iff.mp (hCR (hMC hm)) r⁻¹).mp (R.inv_mem hr))
      · exact M.mul_mem ((Subgroup.mem_normalizer_iff.mp (hMnormC (hRC hr)) m).mp hm)
          (M.inv_mem hm)
    have hRl : R ≤ Subgroup.zpowers ℓ := by
      rw [← hCM]
      exact le_inf hRC (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)
    exact hodd2 _ (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hℓ2, pow_one])) hRl
  refine ⟨?_, fun h => h.elim heven hJR⟩
  rcases hL with (hev | ⟨p, f, hp, hpodd, hf, h5, h8, ⟨e⟩⟩) | hJ
  · exact (hbot (heven hev)).1
  ·
    set C := Subgroup.centralizer ({ℓ} : Set L) with hC
    have hC' : C.map e.toMonoidHom =
        Subgroup.centralizer ({e ℓ} : Set PSL(2, GaloisField p f)) :=
      map_centralizer_singleton_mulEquiv e ℓ
    obtain ⟨n, ⟨d⟩⟩ : ∃ n : ℕ, Nonempty
        (Subgroup.centralizer ({e ℓ} : Set PSL(2, GaloisField p f)) ≃* DihedralGroup n) := by
      have h := psl2_odd_centralizer_involution hpodd hf (t := e ℓ)
        (by rwa [MulEquiv.orderOf_eq])
      have hq : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by
        have := Nat.odd_iff.mp (hpodd.pow (n := f))
        omega
      rcases hq with hq | hq
      · exact ⟨_, (h.1 hq).2⟩
      · exact ⟨_, (h.2 hq).2⟩
    let φ : C ≃* DihedralGroup n :=
      ((C.equivMapOfInjective e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr hC')).trans d
    set R' := (R.subgroupOf C).map φ.toMonoidHom with hR'
    have hR'odd : Odd (Nat.card R') := by
      rw [hR', Subgroup.card_map_of_injective φ.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRC).toEquiv]
      exact hRodd
    have := isCyclic_of_odd_card_dihedralGroup R' hR'odd
    let ψ : R' ≃* R := ((R.subgroupOf C).equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans
      (Subgroup.subgroupOfEquivOfLe hRC)
    exact isCyclic_of_surjective ψ.toMonoidHom ψ.surjective
  · exact (hbot (hJR hJ)).1

theorem normal_centralizer_subgroupOf {G : Type*} [Group G] {A B : Subgroup G}
    (h : A ≤ Subgroup.normalizer (B : Set G)) :
    ((Subgroup.centralizer (B : Set G)).subgroupOf A).Normal := by
  constructor
  intro x hx a
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  have hC : (a : G) ∈ Subgroup.normalizer (Subgroup.centralizer (B : Set G) : Set G) :=
    normalizer_le_normalizer_centralizer_subgroup B (h a.2)
  simpa using (Subgroup.mem_normalizer_iff.mp hC x).mp hx

theorem isCyclic_quotient_centralizer_of_le_fstar {Y : Type} [Group Y] [Finite Y]
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) (hZL : Subgroup.center L = ⊥)
    (hLt : IsTypeL2 L ∨ IsTypeJR L) {t : Y} (ht : t ^ 2 = 1)
    (htF : t ∈ generalizedFittingSubgroupOf (⊤ : Subgroup Y)) {Q : Subgroup Y}
    (hQodd : Odd (Nat.card Q)) (hQF : Q ≤ generalizedFittingSubgroupOf (⊤ : Subgroup Y))
    (hQt : Q ≤ Subgroup.centralizer ({t} : Set Y))
    (hCQ : Subgroup.centralizer ({t} : Set Y) ≤ Subgroup.normalizer (Q : Set Y)) :
    (∀ [((Subgroup.centralizer (L : Set Y)).subgroupOf Q).Normal],
      IsCyclic (Q ⧸ (Subgroup.centralizer (L : Set Y)).subgroupOf Q)) ∧
      (IsTypeL2Even L ∨ IsTypeJR L → Q ≤ Subgroup.centralizer (L : Set Y)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinnF := generalizedFittingSubgroupOf_le_actingAs hL
  set N := Subgroup.normalizer (L : Set Y) with hN
  have hQN : Q ≤ N := fun q hq => (hinnF (hQF hq)).1
  have htN : t ∈ N := (hinnF htF).1
  set ρ : N →* MulAut L := L.normalizerMonoidHom with hρ
  set θ : L →* MulAut L := MulAut.conj with hθ
  have hθinj : Function.Injective θ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZL]
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 := congrArg (fun α : MulAut L => α y) (MonoidHom.mem_ker.mp hx)
    simp only [hθ, MulAut.conj_apply, MulAut.one_apply] at h1
    calc y * x = x * y * x⁻¹ * x := by rw [h1]
      _ = x * y := by group
  have hρθ : ∀ (y : N) (k : L), (∀ x ∈ L, (y : Y) * x * (y : Y)⁻¹ = k * x * (k : Y)⁻¹) →
      ρ y = θ k := by
    intro y k h
    ext x
    rw [hρ, Subgroup.normalizerMonoidHom_apply_apply_coe, hθ, MulAut.conj_apply]
    simpa using h x x.2
  obtain ⟨-, ℓ, hℓL, hℓ⟩ := hinnF htF
  set t' : N := ⟨t, htN⟩ with ht'
  set ℓ' : L := ⟨ℓ, hℓL⟩ with hℓ'
  have hρt : ρ t' = θ ℓ' := hρθ t' ℓ' hℓ
  set Q' := Q.subgroupOf N with hQ'
  set ψ : Q →* MulAut L := ρ.comp (Subgroup.inclusion hQN) with hψ
  have hψapply : ∀ (x : Q) (y : L), ((ψ x y : L) : Y) = (x : Y) * y * (x : Y)⁻¹ := by
    intro x y
    rw [hψ, MonoidHom.comp_apply, hρ, Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  have hker : ψ.ker = (Subgroup.centralizer (L : Set Y)).subgroupOf Q := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro h y hy
      have h1 := hψapply x ⟨y, hy⟩
      rw [h, MulAut.one_apply] at h1
      calc y * x = ((x : Y) * y * (x : Y)⁻¹) * x := by rw [← h1]
        _ = x * y := by group
    · intro h
      ext y
      rw [hψapply, MulAut.one_apply, ← h y y.2, mul_inv_cancel_right]
  have hrangeEq : ψ.range = Q'.map ρ := by
    ext α
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hQN x, x.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have hrange : ψ.range ≤ θ.range := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨-, k, hk, hkx⟩ := hinnF (hQF x.2)
    exact ⟨⟨k, hk⟩, (hρθ (Subgroup.inclusion hQN x) ⟨k, hk⟩ hkx).symm⟩
  set R := ψ.range.comap θ with hR
  have hRmap : R.map θ = ψ.range := Subgroup.map_comap_eq_self hrange
  let eR : R ≃* ψ.range := (R.equivMapOfInjective θ hθinj).trans (MulEquiv.subgroupCongr hRmap)
  have hRodd : Odd (Nat.card R) := by
    rw [Nat.card_congr eR.toEquiv, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
    exact Odd.of_dvd_nat hQodd (Subgroup.card_quotient_dvd_card _)
  have hℓ2 : ℓ' ^ 2 = 1 := by
    apply hθinj
    rw [map_pow, ← hρt, ← map_pow, map_one]
    have : t' ^ 2 = 1 := Subtype.ext (by simpa using ht)
    rw [this, map_one]
  have hRC : R ≤ Subgroup.centralizer ({ℓ'} : Set L) := by
    intro r hr
    obtain ⟨x, hx⟩ := hr
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply hθinj
    rw [map_mul, map_mul, ← hx, ← hρt, hψ, MonoidHom.comp_apply, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (hQt x.2)
  have hCR : Subgroup.centralizer ({ℓ'} : Set L) ≤ Subgroup.normalizer (R : Set L) := by
    intro c hc
    have hct : (c : Y) ∈ Subgroup.centralizer ({t} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hℓ c c.2
      have h2 : (c : Y) * ℓ = ℓ * c := congrArg Subtype.val
        (Subgroup.mem_centralizer_singleton_iff.mp hc)
      have h3 : ℓ * (c : Y) * ℓ⁻¹ = c := by rw [← h2, mul_inv_cancel_right]
      calc (c : Y) * t = (t * c * t⁻¹) * t := by rw [h1, h3]
        _ = t * c := by group
    have hcN : (c : Y) ∈ N := Subgroup.le_normalizer c.2
    have hcQ' : (⟨c, hcN⟩ : N) ∈ Subgroup.normalizer (Q' : Set N) := by
      rw [hQ', ← Subgroup.subgroupOf_normalizer_eq hQN, Subgroup.mem_subgroupOf]
      exact hCQ hct
    have h1 : ρ ⟨c, hcN⟩ ∈ Subgroup.normalizer ((Q'.map ρ : Subgroup (MulAut L)) :
        Set (MulAut L)) :=
      Subgroup.le_normalizer_map ρ ⟨_, hcQ', rfl⟩
    have h2 : ρ ⟨c, hcN⟩ = θ c := hρθ ⟨c, hcN⟩ c (fun x _ => rfl)
    rw [h2, ← hrangeEq] at h1
    exact Subgroup.le_normalizer_comap θ h1
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.2.2.2.2
  have : IsSimpleGroup L :=
    ((QuotientGroup.quotientMulEquivOfEq hZL).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  obtain ⟨hcyc, hR1⟩ := odd_normal_subgroup_centralizer (IsQuasisimple.two_dvd_card hL.2.2) hLt
    hℓ2 hRodd hRC hCR
  refine ⟨?_, fun h => ?_⟩
  · intro _
    let eQ : Q ⧸ (Subgroup.centralizer (L : Set Y)).subgroupOf Q ≃* R :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        ((QuotientGroup.quotientKerEquivRange ψ).trans eR.symm)
    exact isCyclic_of_surjective eQ.symm.toMonoidHom eQ.symm.surjective
  have hrange1 : ψ.range = ⊥ := by rw [← hRmap, hR1 h, Subgroup.map_bot]
  intro x hx
  have h1 : ψ ⟨x, hx⟩ ∈ ψ.range := ⟨⟨x, hx⟩, rfl⟩
  rw [hrange1, Subgroup.mem_bot, ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf] at h1
  exact h1

section AStar

variable {X : Type} [Group X] [Finite X]

theorem IsAStar.mem_centralizer_iff_mk (hX : IsAStar X) {E : Subgroup X}
    (hE : IsComponentOf E ⊤) {x : X} (hx : x ∈ Subgroup.normalizer (E : Set X)) :
    x ∈ Subgroup.centralizer (E : Set X) ↔
      QuotientGroup.mk' (pPrimeCore 2 X) x ∈ Subgroup.centralizer
        ((E.map (QuotientGroup.mk' (pPrimeCore 2 X)) : Subgroup (X ⧸ pPrimeCore 2 X)) :
          Set (X ⧸ pPrimeCore 2 X)) := by
  set q := QuotientGroup.mk' (pPrimeCore 2 X) with hq
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp h y hy]
  · intro h
    have hcenter := (hX.component_image hE).2.1
    apply mem_centralizer_of_commutator_mem_center hE.2.2.2.1
    intro y hy
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ E :=
      E.mul_mem ((Subgroup.mem_normalizer_iff.mp hx y).mp hy) (E.inv_mem hy)
    have h2 : x * y * x⁻¹ * y⁻¹ ∈ pPrimeCore 2 X := by
      rw [← QuotientGroup.eq_one_iff]
      have h3 := Subgroup.mem_centralizer_iff.mp h (q y) ⟨y, hy, rfl⟩
      have h4 : q (x * y * x⁻¹ * y⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        rw [← h3]
        group
      exact h4
    refine ⟨⟨_, h1⟩, ?_, rfl⟩
    show (⟨_, h1⟩ : E) ∈ Subgroup.center E
    rw [hcenter, Subgroup.mem_subgroupOf]
    exact h2

theorem IsAStar.isCyclic_quotient_centralizer (hX : IsAStar X) {t : X} (ht : orderOf t = 2)
    {U : Subgroup X} (hUodd : Odd (Nat.card U)) (hUO : U ≤ oStar X)
    (hUt : U ≤ Subgroup.centralizer ({t} : Set X))
    (hCU : Subgroup.centralizer ({t} : Set X) ≤ Subgroup.normalizer (U : Set X))
    {E : Subgroup X} (hE : IsComponentOf E ⊤) :
    U ≤ Subgroup.normalizer (E : Set X) ∧
      ((Subgroup.centralizer (E : Set X)).subgroupOf U).Normal ∧
      (∀ [((Subgroup.centralizer (E : Set X)).subgroupOf U).Normal],
        IsCyclic (U ⧸ (Subgroup.centralizer (E : Set X)).subgroupOf U)) ∧
      (IsTypeL2Even (E ⧸ Subgroup.center E) ∨ IsTypeJR (E ⧸ Subgroup.center E) →
        U ≤ Subgroup.centralizer (E : Set X)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCore 2 X with hOdef
  set q : X →* X ⧸ O := QuotientGroup.mk' O with hq
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  obtain ⟨hEb, -, ⟨eE⟩⟩ := hX.component_image hE
  set Eb := E.map q with hEbdef
  obtain ⟨hZEb, hEbt⟩ := hX.2.2 Eb hEb
  have hUN : U ≤ Subgroup.normalizer (E : Set X) := hUO.trans (oStar_le_normalizer hX hE)
  have htp : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  have htF : q t ∈ generalizedFittingSubgroupOf (⊤ : Subgroup (X ⧸ O)) :=
    le_oStar_of_isPGroup hX htp (Subgroup.mem_zpowers t)
  have ht2 : (q t) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht] at h
    rw [← map_pow, h, map_one]
  set Ub := U.map q with hUbdef
  have hUbodd : Odd (Nat.card Ub) := Odd.of_dvd_nat hUodd (Subgroup.card_map_dvd U q)
  have hUbF : Ub ≤ generalizedFittingSubgroupOf (⊤ : Subgroup (X ⧸ O)) :=
    Subgroup.map_le_iff_le_comap.mpr hUO
  have hUbt : Ub ≤ Subgroup.centralizer ({q t} : Set (X ⧸ O)) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp (hUt hu)]
  have hCUb : Subgroup.centralizer ({q t} : Set (X ⧸ O)) ≤
      Subgroup.normalizer (Ub : Set (X ⧸ O)) := by
    have : Fact (IsPGroup 2 (Subgroup.zpowers t)) := ⟨htp⟩
    have hC := centralizer_map_quotient_eq_map_centralizer (p := 2) (Subgroup.zpowers t) O
      inferInstance (Nat.coprime_two_left.mpr hOodd)
    simp only at hC
    rw [MonoidHom.map_zpowers] at hC
    have hC1 : Subgroup.centralizer ({q t} : Set (X ⧸ O)) =
        (Subgroup.centralizer ({t} : Set X)).map q := by
      rw [← centralizer_zpowers_eq', ← centralizer_zpowers_eq']
      exact hC
    rw [hC1]
    exact (Subgroup.map_mono hCU).trans (Subgroup.le_normalizer_map q)
  obtain ⟨hcyc, hcent⟩ := isCyclic_quotient_centralizer_of_le_fstar hEb hZEb hEbt ht2 htF
    hUbodd hUbF hUbt hCUb
  have hkey : ∀ u ∈ U, (u ∈ Subgroup.centralizer (E : Set X) ↔
      q u ∈ Subgroup.centralizer (Eb : Set (X ⧸ O))) :=
    fun u hu => hX.mem_centralizer_iff_mk hE (hUN hu)
  have hUbN : Ub ≤ Subgroup.normalizer (Eb : Set (X ⧸ O)) :=
    (Subgroup.map_mono hUN).trans (Subgroup.le_normalizer_map q)
  have hUbn := normal_centralizer_subgroupOf hUbN
  refine ⟨hUN, normal_centralizer_subgroupOf hUN, ?_, fun h => ?_⟩
  · intro _
    set π : U →* Ub ⧸ (Subgroup.centralizer (Eb : Set (X ⧸ O))).subgroupOf Ub :=
      (QuotientGroup.mk' _).comp (q.subgroupMap U) with hπ
    have hπs : Function.Surjective π :=
      (QuotientGroup.mk'_surjective _).comp (q.subgroupMap_surjective U)
    have hπker : π.ker = (Subgroup.centralizer (E : Set X)).subgroupOf U := by
      ext u
      rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact (hkey u u.2).symm
    let e : U ⧸ (Subgroup.centralizer (E : Set X)).subgroupOf U ≃*
        Ub ⧸ (Subgroup.centralizer (Eb : Set (X ⧸ O))).subgroupOf Ub :=
      (QuotientGroup.quotientMulEquivOfEq hπker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective π hπs)
    have hcyc' : IsCyclic (Ub ⧸ (Subgroup.centralizer (Eb : Set (X ⧸ O))).subgroupOf Ub) := hcyc
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  · have h' : IsTypeL2Even Eb ∨ IsTypeJR Eb := by
      rcases h with ⟨f, hf, ⟨φ⟩⟩ | hJ
      · exact Or.inl ⟨f, hf, ⟨eE.symm.trans φ⟩⟩
      · exact Or.inr (hJ.of_mulEquiv eE)
    intro u hu
    exact (hkey u hu).mpr (hcent h' ⟨u, hu, rfl⟩)

theorem oddFitting_centralizer_properties (t : X) :
    Odd (Nat.card (oddCoreOf (CFSG.fittingSubgroupOf (Subgroup.centralizer ({t} : Set X))))) ∧
      oddCoreOf (CFSG.fittingSubgroupOf (Subgroup.centralizer ({t} : Set X))) ≤
        Subgroup.centralizer ({t} : Set X) ∧
      Subgroup.centralizer ({t} : Set X) ≤ Subgroup.normalizer
        ((oddCoreOf (CFSG.fittingSubgroupOf (Subgroup.centralizer ({t} : Set X))) :
          Subgroup X) : Set X) := by
  set C := Subgroup.centralizer ({t} : Set X) with hC
  set FC := CFSG.fittingSubgroupOf C with hFC
  refine ⟨odd_card_oddCoreOf FC, (Subgroup.map_subtype_le _).trans (Subgroup.map_subtype_le _),
    ?_⟩
  exact (le_normalizer_of_isNormalIn (fittingSubgroupOf_isNormalIn C)).trans
    (normalizer_le_normalizer_map_of_characteristic (pPrimeCore 2 FC))

theorem bender1970_2_5_of_inf_centralizer_le (hX : IsAStar X) {t : X} (ht : orderOf t = 2)
    (T : Sylow 2 X) (htT : t ∈ (T : Subgroup X)) {U : Subgroup X}
    (hU : U = oddCoreOf (CFSG.fittingSubgroupOf (Subgroup.centralizer ({t} : Set X))))
    (hCU : U ⊓ Subgroup.centralizer ((T : Subgroup X) : Set X) ≤ pPrimeCore 2 X) :
    U ≤ oStar X ∧ ∀ E : Subgroup X, IsComponentOf E ⊤ →
      U ≤ Subgroup.normalizer (E : Set X) ∧
        ((Subgroup.centralizer (E : Set X)).subgroupOf U).Normal ∧
        (∀ [((Subgroup.centralizer (E : Set X)).subgroupOf U).Normal],
          IsCyclic (U ⧸ (Subgroup.centralizer (E : Set X)).subgroupOf U)) ∧
        (IsTypeL2Even (E ⧸ Subgroup.center E) ∨ IsTypeJR (E ⧸ Subgroup.center E) →
          U ≤ Subgroup.centralizer (E : Set X)) := by
  subst hU
  have hUO := le_oStar_of_inf_centralizer_le hX T htT hCU
  obtain ⟨hodd, hUt, hCU'⟩ := oddFitting_centralizer_properties t
  exact ⟨hUO, fun E hE => hX.isCyclic_quotient_centralizer ht hodd hUO hUt hCU' hE⟩

end AStar

end CFSG.Walter
