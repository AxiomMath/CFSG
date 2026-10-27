module

public import CFSG.Quasithin.EmptyFaithful.S153F21B
public import CFSG.Quasithin.EmptyFaithful.R3c2Hat
public import CFSG.Quasithin.EmptyFaithful.S153H30
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
public import CFSG.Quasithin.EmptyFaithful.ModBLin
public import CFSG.Quasithin.EmptyFaithful.ModBGrp
public import CFSG.Quasithin.EmptyFaithful.SzN12Gen
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


end Rep

section NewHat

open Matrix

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

private theorem szN12_exists_scalar {M K Y : Subgroup G} (hK : IsHatA6Block K) (hF : Fintype.card F = 4)
    (ρ : ↥K →* GL (Fin 3) F) (e : ↥(blockU K) ≃* Multiplicative (Fin 3 → F)) (hρ : Compat ρ e)
    (W : Submodule F (Fin 3 → F))
    (hMW : ∀ k : ↥K, (k : G) ∈ M ↔ ∀ w ∈ W,
      ((ρ k : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ W)
    (hM15 : M.relIndex K = 15) (hYMK : Y ≤ M ⊓ K) (h9 : 9 ∣ Nat.card ↥Y) :
    ∃ y : ↥K, (y : G) ∈ Y ∧ (∀ k : ↥K, ρ y * ρ k = ρ k * ρ y) ∧
      ∃ c : F, c ≠ 0 ∧ c ≠ 1 ∧
        ∀ w, ((ρ y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w = c • w := by
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
  refine ⟨y, hyY, fun k => ?_, c, hc0, hc1, fun w => ?_⟩
  · rw [hy]
    exact hzc k
  · rw [hy]
    exact hscal w

omit [Fintype F] in
private theorem szN12_comm_eq_one {K : Subgroup G} (hK : IsHatA6Block K) {ρ : ↥K →* GL (Fin 3) F}
    {e : ↥(blockU K) ≃* Multiplicative (Fin 3 → F)} (hρ : Compat ρ e) {y : ↥K} {c : F}
    (hc1 : c ≠ 1) (hcomm : ∀ k : ↥K, ρ y * ρ k = ρ k * ρ y)
    (hscal : ∀ w, ((ρ y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w = c • w) {v : G}
    (hvQ : ∀ x ∈ pCoreOf 2 K, v * x = x * v) (hvU : ∀ l ∈ K, v * l * v⁻¹ * l⁻¹ ∈ blockU K)
    (hvy : v * (y : G) = (y : G) * v) : ∀ l ∈ K, v * l * v⁻¹ * l⁻¹ = 1 := by
  intro l hl
  have hq : (y : G) * l * (y : G)⁻¹ * l⁻¹ ∈ pCoreOf 2 K := by
    have h1 : ρ (y * ⟨l, hl⟩ * y⁻¹ * ⟨l, hl⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm ⟨l, hl⟩]
      group
    exact (szN4_mem_pCore_iff _).mp (mem_pCore_of_rho_eq_one hK hρ h1)
  set q : G := (y : G) * l * (y : G)⁻¹ * l⁻¹ with hqdef
  set d : G := v * l * v⁻¹ * l⁻¹ with hddef
  have hdU : d ∈ blockU K := hvU l hl
  have hqd : q * d = d * q := by
    have hd' : d ∈ Subgroup.centralizer (blockQ K : Set G) := (hK.1.2.2.1.1 hdU).2
    exact Subgroup.mem_centralizer_iff.mp hd' q hq
  have hvq : v * q = q * v := hvQ q hq
  have e1 : (y : G) * v * (y : G)⁻¹ = v := by rw [← hvy]; group
  have e2 : (y : G) * l * (y : G)⁻¹ = q * l := by rw [hqdef]; group
  have e4 : (y : G) * v⁻¹ * (y : G)⁻¹ = v⁻¹ := by
    have := congrArg (fun x : G => x⁻¹) e1
    simpa [mul_assoc] using this
  have e5 : (y : G) * l⁻¹ * (y : G)⁻¹ = (q * l)⁻¹ := by rw [← e2]; group
  have e3 : (y : G) * d * (y : G)⁻¹ = d := by
    have e6 : (y : G) * d * (y : G)⁻¹ = ((y : G) * v * (y : G)⁻¹) * ((y : G) * l * (y : G)⁻¹) *
        ((y : G) * v⁻¹ * (y : G)⁻¹) * ((y : G) * l⁻¹ * (y : G)⁻¹) := by
      rw [hddef]; group
    rw [e6, e1, e2, e4, e5]
    calc v * (q * l) * v⁻¹ * (q * l)⁻¹ = (v * q) * l * v⁻¹ * l⁻¹ * q⁻¹ := by group
      _ = (q * v) * l * v⁻¹ * l⁻¹ * q⁻¹ := by rw [hvq]
      _ = q * (v * l * v⁻¹ * l⁻¹) * q⁻¹ := by group
      _ = (d * q) * q⁻¹ := by rw [hddef, ← hddef, hqd]
      _ = d := by group
  let ud : ↥(blockU K) := ⟨d, hdU⟩
  have h1 := compat_apply hρ y ud
  have h2 : (⟨(y : G) * (ud : G) * (y : G)⁻¹, conj_mem_blockU y ud⟩ : ↥(blockU K)) = ud :=
    Subtype.ext e3
  rw [h2, hscal] at h1
  have h3 : (c - 1) • Multiplicative.toAdd (e ud) = 0 := by
    rw [sub_smul, one_smul, h1, sub_self]
  have h4 : Multiplicative.toAdd (e ud) = 0 :=
    (smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hc1)
  have h5 : e ud = 1 := Multiplicative.toAdd.injective (by simpa using h4)
  have h6 : ud = 1 := e.injective (by rw [h5, map_one])
  exact congrArg Subtype.val h6

end NewHat

end ModB

section Main

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem hatA6VleU_holds (h113 : StageLemma14113) : HatA6VleU := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hA hYL
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hI : IsHPlus Yp (Sgp153 T V₁) M I := c.ctx.inH
  have hF : Facts15311 T M V₁ Yp I := c.facts
  obtain ⟨hLc, hLn, -, -, -, -⟩ := c.conc
  have hLI : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ hLc
  have hLle : L ≤ I := le_of_mem_cComp hLI
  have hYI : Yp ≤ I := le_sup_left.trans hI.1.1
  have hYM : Yp ≤ M ⊓ I := hF.norm_eq ▸ le_inf hYI Subgroup.le_normalizer
  have hcommU : ∀ V' : Subgroup G, V' ≤ VZ T M → ⁅V', Yp⁆ ≤ blockU L := by
    intro V' hV'
    rw [Subgroup.commutator_le]
    intro v hv y hy
    exact (szN12_V_facts c (hV' hv)).2.2 y (hYL hy)
  suffices hV : V₁ ≤ blockU L ∧ V₂ ≤ blockU L by
    rw [← hh.decomp.sup]
    exact sup_le hV.1 hV.2
  have hV₂ : V₂ ≤ blockU L :=
    calc V₂ = ⁅V₂, Yp⁆ := (v2CommutatorYp_holds h113 G T Mc M V₁ V₂ Yp t hh).symm
      _ ≤ blockU L := hcommU V₂ hh.decomp.le₂
  refine ⟨?_, hV₂⟩
  rcases hh.cases with hY | ⟨hU, hYp⟩
  ·
    obtain ⟨hV, L₁, L₂, tb, hS, hV₁eq, -, -⟩ := hh.decomp.model
    have hle : V₁ ≤ ⁅V₁, Yp⁆ := by
      have := szN12_comm_le_aux h113 hh.hyp hS.symm (P := Yp)
        (fun g hg _ => ⟨0, by simpa [hY] using hg⟩)
      rw [hV₁eq]
      exact this
    exact hle.trans (hcommU V₁ hh.decomp.le₁)
  ·
    exfalso
    have hC := c.c16.desc
    obtain ⟨hM15, F, _, _, hF4, ρ, e, hρ, W, -, hMW⟩ := ModB.hat_caseC hA hC
    obtain ⟨y, hyY, hycomm, c0, -, hc1, hscal⟩ := ModB.szN12_exists_scalar hA hF4 ρ e hρ W hMW hM15
      (le_inf hYM hYL) (S153F.nine_dvd_card_Yp hF)
    have hYC : Yp ≤ Subgroup.centralizer (V₁ : Set G) := by
      rw [hYp]
      exact (oTwoUpper_le _).trans inf_le_right
    have hV₁C : V₁ ≤ Subgroup.centralizer (L : Set G) := by
      intro v hv
      obtain ⟨hvN, hvQ, hvU⟩ := szN12_V_facts c (hh.decomp.le₁ hv)
      have hvy : v * (y : G) = (y : G) * v := Subgroup.mem_centralizer_iff.mp (hYC hyY) v hv
      refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
      have h1 := ModB.szN12_comm_eq_one hA hρ hc1 hycomm hscal hvQ hvU hvy l hl
      have h2 : v * l = l * v := by
        calc v * l = (v * l * v⁻¹ * l⁻¹) * l * v := by group
          _ = l * v := by rw [h1]; group
      exact h2.symm
    have hLM : L ≤ M := by
      intro l hl
      refine (Hyp153.normalizer_V_le h113 hh.hyp hh.decomp hU).1 ?_
      refine Subgroup.centralizer_le_normalizer _ ?_
      refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
      exact (Subgroup.mem_centralizer_iff.mp (hV₁C hv) l hl).symm
    exact hLn (le_inf hLM hLle)

end Main

end CFSG.Quasithin
