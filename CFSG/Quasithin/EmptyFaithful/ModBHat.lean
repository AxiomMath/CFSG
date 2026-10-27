module

public import CFSG.Quasithin.EmptyFaithful.S153F21B
public import CFSG.Quasithin.EmptyFaithful.R3c2Hat
public import CFSG.Quasithin.EmptyFaithful.S153H30
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
public import CFSG.Quasithin.EmptyFaithful.ModBLin
public import CFSG.Quasithin.EmptyFaithful.ModBAlt6
public import CFSG.Quasithin.EmptyFaithful.ModBGrp
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin

namespace ModB

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

section Excl

variable {G : Type} [Group G] [Finite G]

private theorem hat_card_quot {K : Subgroup G} (hK : IsHatA6Block K) :
    Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 1080 :=
  R3c2.card_of_isHat_alt6 hK.2.1

private theorem hat_not_seven_dvd {K : Subgroup G} (hK : IsHatA6Block K) : ¬ 7 ∣ Nat.card ↥K := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K)
  rw [hat_card_quot hK] at h1
  have hpc : IsPGroup 2 ↥(CFSG.pCore 2 ↥K) := by
    exact CFSG.LieType.BorelTits.pCore_isPGroup 2
  obtain ⟨a, ha⟩ := hpc.exists_card_eq
  rw [ha] at h1
  intro h7
  rw [h1] at h7
  have hp : Nat.Prime 7 := by norm_num
  rcases (Nat.Prime.dvd_mul hp).mp h7 with h | h
  · omega
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
    omega

omit [Finite G] in
private theorem card_quot_of_surj_ker {K : Subgroup G} {H : Type} [Group H] {α : ↥K →* H}
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥K) :
    Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = Nat.card H :=
  Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα)).toEquiv

omit [Finite G] in
private theorem card_autOn_dvd_card (K V : Subgroup G) : Nat.card ↥(autOn K V) ∣ Nat.card ↥K := by
  refine (Subgroup.card_map_dvd (H := K.subgroupOf (Subgroup.normalizer (V : Set G)))
    (conjAct V)).trans ?_
  let f : ↥(K.subgroupOf (Subgroup.normalizer (V : Set G))) →* ↥K :=
    { toFun := fun x => ⟨(x : ↥(Subgroup.normalizer (V : Set G))).1, x.2⟩
      map_one' := rfl
      map_mul' := fun a b => rfl }
  exact Subgroup.card_dvd_of_injective f (fun a b hab => by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun y : ↥K => (y : G)) hab)

omit [Group G] [Finite G] in
private theorem card_alt_eq {n : ℕ} (hn : 2 ≤ n) :
    Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]

omit [Group G] [Finite G] in
private theorem card_alt_small {n : ℕ} (hn : n < 2) : Nat.card (alternatingGroup (Fin n)) = 1 := by
  have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr (by omega)
  have : Subsingleton (alternatingGroup (Fin n)) :=
    ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  exact Nat.card_of_subsingleton 1

omit [Group G] [Finite G] in
private theorem card_alt_ne_1080 {n : ℕ} (hn : 5 ≤ n) (hn8 : n ≤ 8) :
    Nat.card (alternatingGroup (Fin n)) ≠ 1080 := by
  rw [card_alt_eq (by omega)]
  interval_cases n <;> decide

private def HatCaseC (M K : Subgroup G) : Prop :=
  M.relIndex K = 15 ∧ ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 4 ∧
    ∃ (ρ : ↥K →* Matrix.GeneralLinearGroup (Fin 3) F)
      (e : ↥(blockU K) ≃* Multiplicative (Fin 3 → F)),
      (∀ (k : ↥K) (u v : ↥(blockU K)), (v : G) = k * u * k⁻¹ →
        Multiplicative.toAdd (e v) =
          ((ρ k : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
            (Multiplicative.toAdd (e u))) ∧
      ∃ W : Submodule F (Fin 3 → F), Module.finrank F W = 2 ∧
        ∀ k : ↥K, (k : G) ∈ M ↔ ∀ w ∈ W,
          ((ρ k : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ W

private theorem hat_caseC {H R M K V : Subgroup G} (hK : IsHatA6Block K) (hC : C27Concl H R M K V) :
    HatCaseC M K := by
  have h1080 := hat_card_quot hK
  have h7 := hat_not_seven_dvd hK
  rcases hC.2.2 with ha | hb | hc | hd | he | hf | hg | hh
  · exfalso
    obtain ⟨-, hL | ⟨m, hm, hA⟩⟩ := ha.1
    · obtain ⟨n, hn, F, _, _, hF, α, hα, hker, -⟩ := hL
      have hq := card_quot_of_surj_ker hα hker
      rw [h1080] at hq
      have hFc : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
      have hSL := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := F) (n := 2)
        (by norm_num)
      rw [← hq, hFc, show Finset.Icc 2 2 = {2} by decide, Finset.prod_singleton] at hSL
      norm_num at hSL
      have hdvd : 2 ^ n ∣ 1080 := ⟨(2 ^ n) ^ 2 - 1, hSL⟩
      have hn3 : n ≤ 3 := by
        by_contra hcon
        push Not at hcon
        have := pow_dvd_pow 2 hcon
        have h16 : (2 : ℕ) ^ 4 ∣ 1080 := this.trans hdvd
        omega
      interval_cases n <;> omega
    · obtain ⟨α, hα, hker, -⟩ := hA
      have hq := card_quot_of_surj_ker hα hker
      rw [h1080] at hq
      by_cases hm2 : 2 ≤ m
      · rw [card_alt_eq hm2] at hq
        by_cases hm7 : 7 ≤ m
        · have := Nat.factorial_le hm7
          have h5040 : (7 : ℕ).factorial = 5040 := by decide
          omega
        · push Not at hm7
          interval_cases m <;> revert hq <;> decide
      · push Not at hm2
        rw [card_alt_small hm2] at hq
        omega
  · exfalso
    obtain ⟨n, α, h5, h8, -, ⟨hα, hker, -⟩, -⟩ := hb.1
    have hq := card_quot_of_surj_ker hα hker
    rw [h1080] at hq
    exact card_alt_ne_1080 h5 h8 hq.symm
  · exact hc.2
  · exfalso
    obtain ⟨-, ⟨α, hα, hker⟩, -⟩ := hd.1
    have hq := card_quot_of_surj_ker hα hker
    rw [h1080, card_alt_eq (by norm_num)] at hq
    revert hq; decide
  · exfalso
    rcases he.1 with ⟨-, α, hα, hker, -⟩ | ⟨-, F, _, _, hF, α, hα, hker, -⟩
    · have hq := card_quot_of_surj_ker hα hker
      rw [h1080, card_alt_eq (by norm_num)] at hq
      revert hq; decide
    · have hq := card_quot_of_surj_ker hα hker
      rw [h1080, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp,
        Nat.card_eq_fintype_card (α := F), hF] at hq
      revert hq
      rw [show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
      norm_num
  · exfalso
    have h6048 := S153H.card_psu_three_three hf.1.2.1
    omega
  · exfalso
    obtain ⟨⟨n, F, _, _, hn, hF, ⟨e⟩⟩, -⟩ := hg
    have h1 : Nat.card ↥(autOn K V) = Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) := by
      rw [Nat.card_congr e.toEquiv,
        ← Nat.card_congr (specialLinearGroupEquivStatedSL 3 F).toEquiv]
    have hFc : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
    have h2 := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := F) (n := 3)
      (by norm_num)
    rw [hFc, show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)] at h2
    have h37 : 7 ∣ (2 ^ n) ^ 3 - 1 := by
      have := Nat.sub_dvd_pow_sub_pow 8 1 n
      rw [one_pow] at this
      have e8 : (2 ^ n) ^ 3 = 8 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [e8]
      exact this
    have h3 : 7 ∣ Nat.card ↥(autOn K V) := by
      rw [h1, h2]
      exact Dvd.dvd.mul_left (Dvd.dvd.mul_left h37 _) _
    exact h7 (h3.trans (card_autOn_dvd_card K V))
  · exfalso
    obtain ⟨hSL, -⟩ := hh
    have h7' : ∀ m : ℕ, Nat.card ↥(autOn K V) = m → 7 ∣ m → False := fun m hm h =>
      h7 ((hm ▸ h : 7 ∣ Nat.card ↥(autOn K V)).trans (card_autOn_dvd_card K V))
    rcases hSL with h4 | h5
    · obtain ⟨e⟩ := h4
      have h1 : Nat.card ↥(autOn K V) = Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) := by
        rw [Nat.card_congr e.toEquiv,
          ← Nat.card_congr (specialLinearGroupEquivStatedSL 4 (ZMod 2)).toEquiv]
      have h2 := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := ZMod 2) (n := 4)
        (by norm_num)
      rw [Nat.card_zmod] at h2
      exact h7' _ (h1.trans h2) (by decide)
    · obtain ⟨e⟩ := h5
      have h1 : Nat.card ↥(autOn K V) = Nat.card (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) := by
        rw [Nat.card_congr e.toEquiv,
          ← Nat.card_congr (specialLinearGroupEquivStatedSL 5 (ZMod 2)).toEquiv]
      have h2 := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := ZMod 2) (n := 5)
        (by norm_num)
      rw [Nat.card_zmod] at h2
      exact h7' _ (h1.trans h2) (by decide)

end Excl


section Rep

open Matrix

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {F : Type} [Field F] [Fintype F]

private def Compat (ρ : ↥K →* GL (Fin 3) F) (e : ↥(blockU K) ≃* Multiplicative (Fin 3 → F)) : Prop :=
  ∀ (k : ↥K) (u v : ↥(blockU K)), (v : G) = k * u * k⁻¹ →
    Multiplicative.toAdd (e v) =
      ((ρ k : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (Multiplicative.toAdd (e u))

private theorem conj_mem_blockU (k : ↥K) (u : ↥(blockU K)) :
    (k : G) * u * (k : G)⁻¹ ∈ blockU K :=
  (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU K k.2) u).mp u.2

omit [Fintype F] in
private theorem compat_apply {ρ : ↥K →* GL (Fin 3) F} {e : ↥(blockU K) ≃* Multiplicative (Fin 3 → F)}
    (hρ : Compat ρ e) (k : ↥K) (u : ↥(blockU K)) :
    ((ρ k : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (Multiplicative.toAdd (e u)) =
      Multiplicative.toAdd (e ⟨(k : G) * u * (k : G)⁻¹, conj_mem_blockU k u⟩) :=
  (hρ k u ⟨(k : G) * u * (k : G)⁻¹, conj_mem_blockU k u⟩ rfl).symm

omit [Finite G] in
private theorem mem_pCore_of_mem_pCoreOf {k : ↥K} (hk : (k : G) ∈ pCoreOf 2 K) :
    k ∈ CFSG.pCore 2 ↥K := (CFSG.mem_openPCoreOf_iff k).mp hk


variable {ρ : ↥K →* GL (Fin 3) F} {e : ↥(blockU K) ≃* Multiplicative (Fin 3 → F)}

omit [Finite G] [Fintype F] in
private theorem rho_eq_one_of_mem_pCore (hK : IsHatA6Block K) (hρ : Compat ρ e) {n : ↥K}
    (hn : n ∈ CFSG.pCore 2 ↥K) : ρ n = 1 := by
  have hnK : (n : G) ∈ K ⊓ Subgroup.centralizer (blockU K : Set G) := by
    rw [hK.2.2.2]
    exact Subgroup.mem_map.mpr ⟨n, hn, rfl⟩
  have hcent := Subgroup.mem_centralizer_iff.mp hnK.2
  apply Units.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  obtain ⟨u, hu⟩ := e.surjective (Multiplicative.ofAdd x)
  have hux : Multiplicative.toAdd (e u) = x := by rw [hu]; rfl
  have hc : (u : G) = (n : G) * u * (n : G)⁻¹ := by
    rw [← hcent (u : G) u.2, mul_inv_cancel_right]
  have h1 := hρ n u u hc
  simp only [Matrix.toLin'_apply, Units.val_one, Matrix.one_mulVec]
  rw [← hux]
  exact h1.symm

omit [Fintype F] in
private theorem mem_pCore_of_rho_eq_one (hK : IsHatA6Block K) (hρ : Compat ρ e) {k : ↥K}
    (hk : ρ k = 1) : k ∈ CFSG.pCore 2 ↥K := by
  have hcent : (k : G) ∈ Subgroup.centralizer (blockU K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h1 := hρ k ⟨u, hu⟩ ⟨(k : G) * u * (k : G)⁻¹, conj_mem_blockU k ⟨u, hu⟩⟩ rfl
    rw [hk] at h1
    simp only [Units.val_one, Matrix.one_mulVec] at h1
    have h2 : e ⟨(k : G) * u * (k : G)⁻¹, conj_mem_blockU k ⟨u, hu⟩⟩ = e ⟨u, hu⟩ :=
      Multiplicative.toAdd.injective h1
    have h3 := congrArg Subtype.val (e.injective h2)
    simp only at h3
    calc (u : G) * k = ((k : G) * u * (k : G)⁻¹) * k := by rw [h3]
      _ = (k : G) * u := by group
  have : (k : G) ∈ pCoreOf 2 K := by
    rw [← hK.2.2.2]
    exact ⟨k.2, hcent⟩
  exact mem_pCore_of_mem_pCoreOf this



private def lineSet (e : ↥(blockU K) ≃* Multiplicative (Fin 3 → F)) (V' : Subgroup G) :
    AddSubgroup (Fin 3 → F) where
  carrier := {x | ∃ u : ↥(blockU K), (u : G) ∈ V' ∧ Multiplicative.toAdd (e u) = x}
  zero_mem' := ⟨1, V'.one_mem, by simp⟩
  add_mem' := by
    rintro _ _ ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
    exact ⟨u * u', V'.mul_mem hu hu', by simp⟩
  neg_mem' := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u⁻¹, V'.inv_mem hu, by simp⟩

omit [Finite G] [Fintype F] in
private theorem card_lineSet {V' : Subgroup G} (hV : V' ≤ blockU K) :
    Nat.card (lineSet e V') = Nat.card V' := by
  symm
  refine Nat.card_eq_of_bijective
    (fun v : V' => (⟨Multiplicative.toAdd (e ⟨v, hV v.2⟩), ⟨v, hV v.2⟩, v.2, rfl⟩ : lineSet e V'))
    ⟨fun a b hab => ?_, fun ⟨x, u, hu, hx⟩ => ⟨⟨u, hu⟩, Subtype.ext hx⟩⟩
  have h1 := congrArg Subtype.val hab
  have h2 : e ⟨a, hV a.2⟩ = e ⟨b, hV b.2⟩ := Multiplicative.toAdd.injective h1
  have h3 := congrArg Subtype.val (e.injective h2)
  exact Subtype.ext h3

omit [Finite G] [Fintype F] in
private theorem lineSet_inf {V₁ V₂ : Subgroup G} (h : V₁ ⊓ V₂ = ⊥) {x : Fin 3 → F}
    (h1 : x ∈ lineSet e V₁) (h2 : x ∈ lineSet e V₂) : x = 0 := by
  obtain ⟨u, hu, rfl⟩ := h1
  obtain ⟨u', hu', hx⟩ := h2
  have huu : u = u' := e.injective (Multiplicative.toAdd.injective hx.symm)
  subst huu
  have hmem : (u : G) ∈ V₁ ⊓ V₂ := ⟨hu, hu'⟩
  rw [h, Subgroup.mem_bot] at hmem
  have : u = 1 := Subtype.ext hmem
  simp [this]

omit [Fintype F] in
private theorem rho_mem_lineSet (hρ : Compat ρ e) {V' : Subgroup G} {k : ↥K}
    (hk : (k : G) ∈ Subgroup.normalizer (V' : Set G)) {x : Fin 3 → F} (hx : x ∈ lineSet e V') :
    ((ρ k : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec x ∈ lineSet e V' := by
  obtain ⟨u, hu, rfl⟩ := hx
  refine ⟨⟨(k : G) * u * (k : G)⁻¹, conj_mem_blockU k u⟩, ?_, (compat_apply hρ k u).symm⟩
  exact (Subgroup.mem_normalizer_iff.mp hk u).mp hu

omit [Fintype F] in
private theorem exists_central_lift (hK : IsHatA6Block K) (hρ : Compat ρ e) :
    ∃ z : ↥K, ρ z ≠ 1 ∧ ρ z ^ 3 = 1 ∧ ∀ k : ↥K, ρ z * ρ k = ρ k * ρ z := by
  have hcen := hK.2.1.2.1
  have hnt : Nontrivial ↥(Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcen]; norm_num)
  obtain ⟨zb, hzb⟩ := exists_ne (1 : ↥(Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)))
  obtain ⟨z, hz⟩ := QuotientGroup.mk_surjective (zb : ↥K ⧸ CFSG.pCore 2 ↥K)
  have hzc : ∀ g : ↥K ⧸ CFSG.pCore 2 ↥K, g * (zb : ↥K ⧸ CFSG.pCore 2 ↥K) = zb * g :=
    Subgroup.mem_center_iff.mp zb.2
  refine ⟨z, ?_, ?_, ?_⟩
  · intro h1
    apply hzb
    apply Subtype.ext
    rw [← hz]
    exact (QuotientGroup.eq_one_iff z).2 (mem_pCore_of_rho_eq_one hK hρ h1)
  · have h3 : zb ^ 3 = 1 := by
      have := pow_card_eq_one' (G := ↥(Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K))) (x := zb)
      rwa [hcen] at this
    have h3' : ((z ^ 3 : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) = 1 := by
      rw [QuotientGroup.mk_pow, hz]
      exact congrArg Subtype.val h3
    rw [← map_pow]
    exact rho_eq_one_of_mem_pCore hK hρ ((QuotientGroup.eq_one_iff _).1 h3')
  · intro k
    rw [← map_mul, ← map_mul]
    have : ((z * k : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) = ((k * z : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hz]
      exact (hzc k).symm
    have hmem := (QuotientGroup.eq.mp this)
    have h1 := rho_eq_one_of_mem_pCore hK hρ hmem
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1


private theorem hat_main {M K V₁ V₂ S₀ Y : Subgroup G} (hK : IsHatA6Block K)
    (hF : Fintype.card F = 4) (ρ : ↥K →* GL (Fin 3) F)
    (e : ↥(blockU K) ≃* Multiplicative (Fin 3 → F)) (hρ : Compat ρ e)
    (W : Submodule F (Fin 3 → F))
    (hMW : ∀ k : ↥K, (k : G) ∈ M ↔ ∀ w ∈ W,
      ((ρ k : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ W)
    (hM15 : M.relIndex K = 15) (hS₀ : IsSylowTwoOf S₀ K) (hYMK : Y ≤ M ⊓ K)
    (h9 : 9 ∣ Nat.card ↥Y) (hV₁ : V₁ ≤ blockU K) (hV₂ : V₂ ≤ blockU K) (hinf : V₁ ⊓ V₂ = ⊥)
    (hc₁ : Nat.card ↥V₁ = 4) (hc₂ : Nat.card ↥V₂ = 4)
    (hYN₁ : Y ≤ Subgroup.normalizer (V₁ : Set G)) (hYN₂ : Y ≤ Subgroup.normalizer (V₂ : Set G))
    (hSN₁ : S₀ ≤ Subgroup.normalizer (V₁ : Set G))
    (hSN₂ : S₀ ≤ Subgroup.normalizer (V₂ : Set G)) : False := by
  classical
  have hperf : commutator (↥K ⧸ CFSG.pCore 2 ↥K) = ⊤ := Group.isPerfect_def.mp hK.2.1.1.1
  have hN2 : IsPGroup 2 ↥(CFSG.pCore 2 ↥K) := by
    exact CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hker : ρ.ker = CFSG.pCore 2 ↥K := by
    ext k
    exact ⟨mem_pCore_of_rho_eq_one hK hρ, rho_eq_one_of_mem_pCore hK hρ⟩
  have hNM : CFSG.pCore 2 ↥K ≤ M.subgroupOf K := by
    intro n hn
    show (n : G) ∈ M
    refine (hMW n).2 fun w hw => ?_
    rw [rho_eq_one_of_mem_pCore hK hρ hn]
    simpa using hw
  have hN1080 : (CFSG.pCore 2 ↥K).index = 1080 := by
    rw [Subgroup.index_eq_card]
    exact hat_card_quot hK
  have hYK : Y ≤ K := hYMK.trans inf_le_right
  have hYM : Y.subgroupOf K ≤ M.subgroupOf K := fun y hy => (hYMK hy).1
  have h9' : 9 ∣ Nat.card ↥(Y.subgroupOf K) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYK).toEquiv]
    exact h9
  obtain ⟨z, hz1, hz3, hzc⟩ := exists_central_lift hK hρ
  obtain ⟨c, hc0, hc1, hscal⟩ := scalar_of_central hF (CFSG.pCore 2 ↥K) hperf ρ
    (fun n hn => rho_eq_one_of_mem_pCore hK hρ hn) z hz1 hz3 hzc
  have hzM : z ∈ M.subgroupOf K := by
    show (z : G) ∈ M
    refine (hMW z).2 fun w hw => ?_
    rw [hscal]
    exact W.smul_mem c hw
  obtain ⟨y, hyY, hy⟩ := exists_mem_of_central_image ρ (CFSG.pCore 2 ↥K) (M.subgroupOf K)
    (Y.subgroupOf K) hN2 hker hNM hM15 hN1080 hYM h9' z hzM hz3 (fun k _ => hzc k)
  have hyY' : (y : G) ∈ Y := hyY
  have hcl : ∀ V' : Subgroup G, Y ≤ Subgroup.normalizer (V' : Set G) →
      ∀ x ∈ lineSet e V', c • x ∈ lineSet e V' := by
    intro V' hYN x hx
    have := rho_mem_lineSet hρ (hYN hyY') hx
    rw [hy, hscal] at this
    exact this
  have hA₁ : Nat.card (lineSet e V₁) = 4 := by rw [card_lineSet hV₁, hc₁]
  have hA₂ : Nat.card (lineSet e V₂) = 4 := by rw [card_lineSet hV₂, hc₂]
  obtain ⟨a₁, ha₁, ha₁0⟩ : ∃ a ∈ lineSet e V₁, a ≠ 0 := by
    have : Nontrivial ↥(lineSet e V₁) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hA₁]; norm_num)
    obtain ⟨a, ha⟩ := exists_ne (0 : ↥(lineSet e V₁))
    exact ⟨a, a.2, fun h => ha (Subtype.ext h)⟩
  obtain ⟨a₂, ha₂, ha₂0⟩ : ∃ a ∈ lineSet e V₂, a ≠ 0 := by
    have : Nontrivial ↥(lineSet e V₂) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hA₂]; norm_num)
    obtain ⟨a, ha⟩ := exists_ne (0 : ↥(lineSet e V₂))
    exact ⟨a, a.2, fun h => ha (Subtype.ext h)⟩
  have hl₁ := line_of_card_four hF (lineSet e V₁) hA₁ hc0 hc1 (hcl V₁ hYN₁) ha₁ ha₁0
  have hl₂ := line_of_card_four hF (lineSet e V₂) hA₂ hc0 hc1 (hcl V₂ hYN₂) ha₂ ha₂0
  have hli : LinearIndependent F ![a₁, a₂] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hs : s • a₁ ∈ lineSet e V₁ := (hl₁ _).2 ⟨s, rfl⟩
    have ht : -(t • a₂) ∈ lineSet e V₂ := (lineSet e V₂).neg_mem ((hl₂ _).2 ⟨t, rfl⟩)
    have heq : s • a₁ = -(t • a₂) := eq_neg_of_add_eq_zero_left hst
    have h0 : s • a₁ = 0 := lineSet_inf hinf hs (heq ▸ ht)
    have hs0 : s = 0 := (smul_eq_zero.mp h0).resolve_right ha₁0
    subst hs0
    have : t • a₂ = 0 := by simpa using hst
    exact ⟨rfl, (smul_eq_zero.mp this).resolve_right ha₂0⟩
  have hS₀p : IsPGroup 2 ↥(S₀.subgroupOf K) := by
    intro s
    obtain ⟨k, hk⟩ := hS₀.2.1 (Subgroup.subgroupOfEquivOfLe hS₀.1 s)
    refine ⟨k, ?_⟩
    apply (Subgroup.subgroupOfEquivOfLe hS₀.1).injective
    rw [map_pow, hk, map_one]
  have hfix : ∀ (V' : Subgroup G) (a : Fin 3 → F), S₀ ≤ Subgroup.normalizer (V' : Set G) →
      (∀ x : Fin 3 → F, x ∈ lineSet e V' ↔ ∃ t : F, x = t • a) → a ≠ 0 →
      ∀ s : ↥(S₀.subgroupOf K),
        ((ρ.comp (S₀.subgroupOf K).subtype s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ a = a := by
    intro V' a hSN hl ha0 s
    have ha : a ∈ lineSet e V' := (hl a).2 ⟨1, (one_smul F a).symm⟩
    have hmem := rho_mem_lineSet hρ (hSN s.2) ha
    obtain ⟨t, ht⟩ := (hl _).1 hmem
    have h1 := eigen_one_of_pgroup hF hS₀p (ρ.comp (S₀.subgroupOf K).subtype) ha0 s (l := t) ht
    rw [h1, one_smul] at ht
    exact ht
  have hcomm := commute_of_fixing hF hS₀p (ρ.comp (S₀.subgroupOf K).subtype) hli
    (hfix V₁ a₁ hSN₁ hl₁ ha₁0) (hfix V₂ a₂ hSN₂ hl₂ ha₂0)
  obtain ⟨eA⟩ := hK.2.1.2.2
  let π : ↥K →* alternatingGroup (Fin 6) :=
    eA.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K))).comp
      (QuotientGroup.mk' (CFSG.pCore 2 ↥K)))
  have hπ : Function.Surjective π :=
    eA.surjective.comp ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  have hπN : ∀ n ∈ CFSG.pCore 2 ↥K, π n = 1 := by
    intro n hn
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥K) n = 1 := (QuotientGroup.eq_one_iff n).2 hn
    show eA ((QuotientGroup.mk' (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)))
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥K)) n)) = 1
    rw [h1, map_one, map_one]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let SS : Sylow 2 ↥K := IsPGroup.toSylow hS₀p hS₀.2.2
  refine alt6_sylow_not_comm (Sylow.mapSurjective hπ SS) ?_
  intro a ha b hb
  rw [Sylow.coe_mapSurjective] at ha hb
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hb
  have hst := hcomm ⟨s, hs⟩ ⟨t, ht⟩
  have e1 : ρ (s * t) = ρ (t * s) := by simpa [map_mul] using hst
  have hmem : (t * s)⁻¹ * (s * t) ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, e1, inv_mul_cancel]
  rw [hker] at hmem
  have h2 := hπN _ hmem
  rw [map_mul, map_inv, inv_mul_eq_one] at h2
  rw [← map_mul, ← map_mul]
  exact h2.symm

end Rep

end ModB

theorem hatA6SwapLocal_holds : HatA6SwapLocal := by
  intro G _ _ H R M K V V₁ V₂ S₀ Y hK _ hC hS₀ _ hYMK h9 hVU _ hsup hinf hc₁ hc₂ hYN₁ hYN₂ hSN₁ hSN₂
  obtain ⟨hM15, F, _, _, hF, ρ, e, hρ, W, -, hMW⟩ := ModB.hat_caseC hK hC
  have hV₁ : V₁ ≤ QuasithinUnique.blockU K := le_sup_left.trans (hsup ▸ hVU)
  have hV₂ : V₂ ≤ QuasithinUnique.blockU K := le_sup_right.trans (hsup ▸ hVU)
  exact ModB.hat_main hK hF ρ e hρ W hMW hM15 hS₀ hYMK h9 hV₁ hV₂ hinf hc₁ hc₂ hYN₁ hYN₂ hSN₁ hSN₂

end CFSG.Quasithin
