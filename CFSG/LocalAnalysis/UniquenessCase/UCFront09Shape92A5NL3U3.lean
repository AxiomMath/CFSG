module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Bar2A5
import CFSG.GH74.GLS.C3.Layer1.Th2P72cR26
import CFSG.GH74.GLS.IVK.Proofs2.GU2Center
import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.AutTransfer
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpHSPerm5
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.L3OvContra
import CFSG.LocalAnalysis.UniquenessCase.UC22L3U3Torus
import CFSG.Quasithin.Vol2.KGFactInspModelU
import TauCeti.GroupTheory.QuotientGroup.MulAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.GH74.GLS.Th2.Obs (autPerm5 autPerm5_apply)
open CFSG.GH74.GLS.IVK.Proofs2 CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin.H13.KGInspOdd (InvCentModel invCentModel_psl invCentModel_psu)

variable {S : Type} [Group S] [Finite S]

theorem exists_le_centralizer_of_isAlt_five {P D C : Subgroup S} (hA5 : IsAlt (Bar2 P) 5)
    (hP : ⁅P, P⁆ = P) (hZ : ∀ a ∈ pCoreOf 2 P, ∀ k ∈ P, a * k = k * a) (hDP : D ≤ P)
    (hD : Nat.card D = 3) (hCP : C ≤ normalizer (P : Set S)) (hCD : C ≤ centralizer (D : Set S)) :
    ∃ C₀ : Subgroup S, C₀ ≤ C ∧ C₀ ≤ centralizer (P : Set S) ∧
      Nat.card C ∣ 6 * Nat.card C₀ := by
  obtain ⟨e⟩ := hA5
  have : Group.IsPerfect P := isPerfect_iff.mpr hP
  let γ : C →* MulAut P := (normalizerMonoidHom P).comp (inclusion hCP)
  have hγ : ∀ (c : C) (x : P), ((γ c x : P) : S) = c * x * (c : S)⁻¹ := fun c x =>
    normalizerMonoidHom_apply_apply_coe P (inclusion hCP c) x
  let Φ : C →* Equiv.Perm (Fin 5) :=
    (autPerm5 e).toMonoidHom.comp ((MulAut.mapQuotient (CFSG.pCore 2 P)).comp γ)
  refine ⟨Φ.ker.map C.subtype, map_subtype_le _, ?_, ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    have hq : MulAut.mapQuotient (CFSG.pCore 2 P) (γ c) = 1 :=
      (autPerm5 e).injective ((MonoidHom.mem_ker.mp hc).trans (map_one _).symm)
    have h1 : γ c = 1 := by
      refine CFSG.HardMathSupport.Timmesfeld.Balance.Alt.mulAut_eq_one_of_central _ fun x => ?_
      have hx : x⁻¹ * γ c x ∈ CFSG.pCore 2 P :=
        QuotientGroup.eq.mp ((MulAut.mem_ker_mapQuotient_iff _).mp hq x).symm
      exact mem_center_iff.mpr fun g => Subtype.ext (hZ _ (mem_map_of_mem _ hx) g g.2).symm
    refine mem_centralizer_iff.mpr fun x hx => ?_
    have hcx : (c : S) * x * (c : S)⁻¹ = x := by
      rw [← hγ c ⟨x, hx⟩, h1]
      rfl
    calc x * (c : S) = c * x * (c : S)⁻¹ * c := by rw [hcx]
      _ = c * x := by group
  ·
    obtain ⟨d, hd⟩ :=
      exists_prime_orderOf_dvd_card' (G := D) 3 (hp := ⟨Nat.prime_three⟩) (dvd_of_eq hD.symm)
    let x : P := ⟨d, hDP d.2⟩
    have hx : orderOf x = 3 :=
      (Subgroup.orderOf_coe x).symm.trans ((Subgroup.orderOf_coe d).trans hd)
    let σ : Equiv.Perm (Fin 5) := (e (x : Bar2 P) : Equiv.Perm (Fin 5))
    have hσ3 : σ ^ 3 = 1 := by
      have h : e (x : Bar2 P) ^ 3 = 1 := by
        rw [← map_pow, ← QuotientGroup.mk_pow, ← hx, pow_orderOf_eq_one, QuotientGroup.mk_one,
          map_one]
      exact congrArg Subtype.val h
    have hσ1 : σ ≠ 1 := by
      intro h1
      have hxO : x ∈ CFSG.pCore 2 P :=
        (QuotientGroup.eq_one_iff x).mp (e.map_eq_one_iff.mp (Subtype.ext h1))
      obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 2) (G := P) ⟨x, hxO⟩
      have h3 : 3 ∣ 2 ^ n := by
        rw [← hx]
        exact orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hn)
      exact absurd (Nat.le_of_dvd two_pos (Nat.prime_three.dvd_of_dvd_pow h3)) (by norm_num)
    have hrange : Φ.range ≤ centralizer ({σ} : Set (Equiv.Perm (Fin 5))) := by
      rintro _ ⟨c, rfl⟩
      have hcd : (d : S) * c = c * d := mem_centralizer_iff.mp (hCD c.2) d d.2
      have hfix : γ c x = x := Subtype.ext <| (hγ c x).trans <| by
        change (c : S) * d * (c : S)⁻¹ = d
        rw [← hcd, mul_inv_cancel_right]
      have h := autPerm5_apply e (MulAut.mapQuotient (CFSG.pCore 2 P) (γ c)) (x : Bar2 P)
      rw [MulAut.mapQuotient_mk, hfix] at h
      have h' : Φ c * σ * (Φ c)⁻¹ = σ := h.symm
      exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp h')
    have h6 : Nat.card Φ.range ∣ 6 :=
      CFSG.EvenSporadicStandard.HSStd.PumpHS.card_centralizer_perm5_three hσ3 hσ1 ▸
        card_dvd_of_le hrange
    rw [card_map_of_injective C.subtype_injective, ← card_ker_mul_card_range Φ, mul_comm 6]
    exact mul_dvd_mul_left _ h6

private theorem card_le_of_invCentModel {X : Type} [Group X] {F₀ : Type} [Field F₀]
    (e : S ≃* X) (hM : InvCentModel X F₀) {N : ℕ}
    (hN : ∀ w : X, orderOf w = 2 → Nat.card (center (centralizer ({w} : Set X))) ≤ N)
    {P C₀ : Subgroup S} (hP : ⁅P, P⁆ = P) (hA5 : IsAlt (Bar2 P) 5) (hC₀ : IsCyclic C₀)
    (h2 : 2 ∣ Nat.card C₀) (hC₀P : C₀ ≤ centralizer (P : Set S)) : Nat.card C₀ ≤ N := by
  have : Finite X := Finite.of_equiv S e.toEquiv
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := C₀) 2 h2
  have hw : orderOf (e z) = 2 := by rw [MulEquiv.orderOf_eq, orderOf_coe, hz]
  obtain ⟨ι, -, -, hCC, hschur⟩ := hM (e z) hw
  have hcomm : ∀ c ∈ C₀, ∀ x ∈ P, x * c = c * x := fun c hc => mem_centralizer_iff.mp (hC₀P hc)
  have hzP : ∀ x ∈ P, e x ∈ centralizer ({e z} : Set X) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (by rw [← map_mul, ← map_mul, hcomm z z.2 x hx])
  have hzC : ∀ c ∈ C₀, e c ∈ centralizer ({e z} : Set X) := fun c hc =>
    mem_centralizer_singleton_iff.mpr (by
      rw [← map_mul, ← map_mul, mem_centralizer_iff.mp (le_centralizer C₀ hc) z z.2])
  have hPι : P.map e.toMonoidHom ≤ ι.range := by
    have hPC : P.map e.toMonoidHom ≤ centralizer ({e z} : Set X) := by
      rintro _ ⟨x, hx, rfl⟩
      exact hzP x hx
    calc P.map e.toMonoidHom = ⁅P.map e.toMonoidHom, P.map e.toMonoidHom⁆ := by
          rw [← map_commutator, hP]
      _ ≤ ⁅centralizer ({e z} : Set X), centralizer ({e z} : Set X)⁆ := commutator_mono hPC hPC
      _ ≤ ι.range := hCC
  have hH : ∃ a ∈ (P.map e.toMonoidHom).comap ι, ∃ b ∈ (P.map e.toMonoidHom).comap ι,
      a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hPP : P ≤ centralizer (P : Set S) := fun x hx => mem_centralizer_iff.mpr fun y hy => by
      obtain ⟨a, ha⟩ := hPι (mem_map_of_mem e.toMonoidHom hy)
      obtain ⟨b, hb⟩ := hPι (mem_map_of_mem e.toMonoidHom hx)
      have hab := hcon a (by rw [mem_comap, ha]; exact mem_map_of_mem _ hy) b
        (by rw [mem_comap, hb]; exact mem_map_of_mem _ hx)
      apply e.injective
      have hab' := congrArg ι hab
      rw [map_mul, map_mul, ha, hb] at hab'
      simpa using hab'
    have h60 := sixty_dvd_card_of_isAlt_five hA5
    rw [hP.symm.trans (commutator_eq_bot_iff_le_centralizer.mpr hPP), card_bot] at h60
    norm_num at h60
  have hcen : ∀ c ∈ C₀, ∀ y ∈ centralizer ({e z} : Set X), e c * y = y * e c := by
    intro c hc
    refine hschur _ hH (e c) (hzC c hc) fun h hh => ?_
    obtain ⟨x, hx, hxh⟩ := mem_map.mp (mem_comap.mp hh)
    rw [← hxh]
    change e c * e x = e x * e c
    rw [← map_mul, ← map_mul, hcomm c hc x hx]
  let g : C₀ → center (centralizer ({e z} : Set X)) := fun c =>
    ⟨⟨e c, hzC c c.2⟩, mem_center_iff.mpr fun y => Subtype.ext (hcen c c.2 y y.2).symm⟩
  have hg : Function.Injective g := fun a b hab =>
    Subtype.ext (e.injective (congrArg Subtype.val (congrArg Subtype.val hab)))
  exact (Nat.card_le_card_of_injective g hg).trans (hN _ hw)

theorem card_le_sub_one_L3 {p f : ℕ} (hp : p ≠ 2) (hS : p ^ f % 3 = 2 ∧ LieModel S .PSL 3 p f)
    {P C₀ : Subgroup S} (hP : ⁅P, P⁆ = P) (hA5 : IsAlt (Bar2 P) 5) (hC₀ : IsCyclic C₀)
    (h2 : 2 ∣ Nat.card C₀) (hC₀P : C₀ ≤ centralizer (P : Set S)) : Nat.card C₀ ≤ p ^ f - 1 := by
  obtain ⟨⟨hpp, -, -⟩, F, _, _, hF, ⟨e⟩⟩ := hS.2.statedClassicalModel_of_ne_zero (by norm_num)
  have hodd : Odd (Nat.card F) := hF ▸ (hpp.odd_of_ne_two hp).pow
  have h3 : ¬ 3 ∣ Nat.card F - 1 := by
    rw [hF]
    omega
  refine card_le_of_invCentModel e
    (invCentModel_psl (CFSG.Wreathed.OddLinearThreeCentralizerCore.two_ne_zero F hodd))
    (fun w hw => ?_) hP hA5 hC₀ h2 hC₀P
  obtain ⟨φ⟩ := Lemma41aL3.nonempty_centralizer_equiv_GL_of_not_dvd hodd h3 hw
  rw [Nat.card_congr (centerCongr φ).toEquiv, Matrix.GeneralLinearGroup.center_eq_range_scalar,
    ← hF, ← Nat.card_units F]
  exact (Nat.card_range_of_injective fun a b hab =>
    CFSG.ClassicalInvolution.Q3.TA3.Q5GL2.scalar_injective hab).le

theorem card_le_add_one_U3 {p f : ℕ} (hp : p ≠ 2) (hS : p ^ f % 3 = 1 ∧ LieModel S .PSU 3 p f)
    {P C₀ : Subgroup S} (hP : ⁅P, P⁆ = P) (hA5 : IsAlt (Bar2 P) 5) (hC₀ : IsCyclic C₀)
    (h2 : 2 ∣ Nat.card C₀) (hC₀P : C₀ ≤ centralizer (P : Set S)) : Nat.card C₀ ≤ p ^ f + 1 := by
  obtain ⟨⟨hpp, hf, -⟩, F, _, _, hF, ⟨e⟩⟩ := hS.2.statedClassicalModel_of_ne_zero (by norm_num)
  have h : UnitaryFieldData p f F := ⟨hpp, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have : Fact p.Prime := ⟨hpp⟩
  have : CharP F p := h.charP
  have h3 : ¬ 3 ∣ p ^ f + 1 := by omega
  refine card_le_of_invCentModel e (invCentModel_psu h hp hF) (fun w hw => ?_) hP hA5 hC₀ h2
    hC₀P
  obtain ⟨φ⟩ := Lemma41aU3.nonempty_centralizer_equiv_GU2_of_not_dvd h hp h3 hw
  exact ((Nat.card_congr (centerCongr φ).toEquiv).trans (natCard_center_GU2Stated h)).le

omit [Finite S] in
private theorem natCard_of_lieModel_PSU_three {p f : ℕ} (hS : LieModel S .PSU 3 p f)
    (h3 : ¬ 3 ∣ p ^ f + 1) :
    Nat.card S = (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) := by
  obtain ⟨⟨hpp, hf, -⟩, F, _, _, hF, ⟨e⟩⟩ := hS.statedClassicalModel_of_ne_zero (by norm_num)
  have h : UnitaryFieldData p f F := ⟨hpp, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have : Fact p.Prime := ⟨hpp⟩
  have : CharP F p := h.charP
  rw [Nat.card_congr e.toEquiv, ← CFSG.SectionRank.OddCover.card_statedSU_three hF]
  exact (Nat.card_congr (Equiv.ofBijective _ ⟨Lemma41aU3.statedProjMk_injective_of_not_dvd h h3,
    CFSG.RankThree.CentralCover.statedProjMk_surjective _⟩)).symm

theorem a5Normalizer_L3U3_odd {p f : ℕ} (hp : p ≠ 2)
    (hS : (p ^ f % 3 = 2 ∧ LieModel S .PSL 3 p f) ∨ (p ^ f % 3 = 1 ∧ LieModel S .PSU 3 p f))
    {K D : Subgroup S} (hA5 : IsAlt (Bar2 K) 5) (hDK : D ≤ K) (hD : Nat.card D = 3)
    (hC : centralizer (D : Set S) ≤ normalizer (K : Set S)) : LieModel S .PSL 3 5 1 := by
  obtain ⟨P, -, hP, -, hKP, hA5P, hodd⟩ := exists_perfect_core_of_isAlt_five hA5
  have hDP : D ≤ P := hodd D hDK (by rw [hD]; decide)
  have hZ := PartOne.Theorem82.pCoreOf_two_commute_of_lieModel_odd hp
    (hS.imp And.right And.right) hP
  obtain ⟨C, hCD, hCcyc, hCcard⟩ := exists_cyclic_le_centralizer_of_card_three hS hD
  obtain ⟨C₀, hC₀C, hC₀P, hdvd⟩ :=
    exists_le_centralizer_of_isAlt_five hA5P hP hZ hDP hD (hCD.trans (hC.trans hKP)) hCD
  have hC₀cyc : IsCyclic C₀ := isCyclic_of_le hC₀C
  have hpf : p.Prime ∧ 1 ≤ f := hS.elim (fun h => ⟨h.2.admissible.1, h.2.admissible.2.1⟩)
    fun h => ⟨h.2.admissible.1, h.2.admissible.2.1⟩
  have hqodd : (p ^ f) % 2 = 1 := Nat.odd_iff.mp ((hpf.1.odd_of_ne_two hp).pow)
  have hq3 : 3 ≤ p ^ f := (show 3 ≤ p by have := hpf.1.two_le; omega).trans
    (Nat.le_self_pow (by have := hpf.2; omega) p)
  have h8 : 8 ∣ 6 * Nat.card C₀ :=
    (hCcard ▸ Nat.eight_dvd_sq_sub_one_of_odd (Nat.odd_iff.mpr hqodd)).trans hdvd
  have h2 : 2 ∣ Nat.card C₀ := by omega
  have hle : (p ^ f + 1) * (p ^ f - 1) ≤ 6 * Nat.card C₀ := by
    rw [← Nat.sq_sub_sq (p ^ f) 1, one_pow, ← hCcard]
    exact Nat.le_of_dvd (Nat.mul_pos (by norm_num) Nat.card_pos) hdvd
  rcases hS with ⟨hq, hL⟩ | ⟨hq, hU⟩
  ·
    have hc := card_le_sub_one_L3 hp ⟨hq, hL⟩ hP hA5P hC₀cyc h2 hC₀P
    have h6 : p ^ f + 1 ≤ 6 :=
      Nat.le_of_mul_le_mul_right (hle.trans (Nat.mul_le_mul_left 6 hc)) (by omega)
    obtain ⟨rfl, rfl⟩ := (Nat.prime_five.pow_eq_iff).mp (by omega : p ^ f = 5)
    exact hL
  ·
    have hc := card_le_add_one_U3 hp ⟨hq, hU⟩ hP hA5P hC₀cyc h2 hC₀P
    have h6 : p ^ f - 1 ≤ 6 := Nat.le_of_mul_le_mul_left
      (by rw [mul_comm 6] at hle; exact hle.trans (Nat.mul_le_mul_right 6 hc)) (by omega)
    have hq7 : p ^ f = 7 := by omega
    have h5 : 5 ∣ Nat.card S :=
      ((show 5 ∣ 60 by norm_num).trans (sixty_dvd_card_of_isAlt_five hA5)).trans
        (card_subgroup_dvd_card K)
    rw [natCard_of_lieModel_PSU_three hU (by omega), hq7] at h5
    norm_num at h5

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
