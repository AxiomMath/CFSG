module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2Tau
import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2Y
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Cent162
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1V
import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJSyl
import CFSG.GroupTheory.GroupAction.CoprimeFiniteSubgroups
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

section Abstract

variable {G : Type*} [Group G]

theorem res1L2_commutator_r_a_centralizes_ob {R A O : Subgroup G}
    (hOA : O ≤ Subgroup.centralizer (A : Set G)) (hRO : R ≤ Subgroup.normalizer (O : Set G)) :
    ⁅R, A⁆ ≤ Subgroup.centralizer (O : Set G) := by
  rw [Subgroup.commutator_le]
  intro r hr a ha
  rw [Subgroup.mem_centralizer_iff]
  intro o ho
  have h1 : a * o = o * a := Subgroup.mem_centralizer_iff.mp (hOA ho) a ha
  have ho₁ : r⁻¹ * o * r ∈ O := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem (hRO hr)) o).mp ho
    simpa using this
  have h2 : a * (r⁻¹ * o * r) = (r⁻¹ * o * r) * a :=
    Subgroup.mem_centralizer_iff.mp (hOA ho₁) a ha
  have h1' : o * a⁻¹ = a⁻¹ * o := by
    calc o * a⁻¹ = a⁻¹ * (a * o) * a⁻¹ := by group
      _ = a⁻¹ * (o * a) * a⁻¹ := by rw [h1]
      _ = a⁻¹ * o := by group
  rw [commutatorElement_def]
  calc o * (r * a * r⁻¹ * a⁻¹) = r * ((r⁻¹ * o * r) * a) * r⁻¹ * a⁻¹ := by group
    _ = r * (a * (r⁻¹ * o * r)) * r⁻¹ * a⁻¹ := by rw [← h2]
    _ = r * a * r⁻¹ * (o * a⁻¹) := by group
    _ = r * a * r⁻¹ * (a⁻¹ * o) := by rw [h1']
    _ = r * a * r⁻¹ * a⁻¹ * o := by group

private theorem res1L2L154_commutator_le_left {R A : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (R : Set G)) : ⁅R, A⁆ ≤ R := by
  rw [Subgroup.commutator_le]
  intro r hr a ha
  rw [show ⁅r, a⁆ = r * (a * r⁻¹ * a⁻¹) by rw [commutatorElement_def]; group]
  exact R.mul_mem hr ((Subgroup.mem_normalizer_iff.mp (hA ha) r⁻¹).mp (R.inv_mem hr))

private theorem res1L2L154_conj_mem_centralizer {O : Subgroup G} {x k : G}
    (hx : x ∈ Subgroup.normalizer (O : Set G)) (hk : k ∈ Subgroup.centralizer (O : Set G)) :
    x * k * x⁻¹ ∈ Subgroup.centralizer (O : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro o ho
  have ho' : x⁻¹ * o * x ∈ O := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hx) o).mp ho
    simpa using this
  have h := Subgroup.mem_centralizer_iff.mp hk _ ho'
  calc o * (x * k * x⁻¹) = x * ((x⁻¹ * o * x) * k) * x⁻¹ := by group
    _ = x * (k * (x⁻¹ * o * x)) * x⁻¹ := by rw [h]
    _ = (x * k * x⁻¹) * o := by group

private theorem res1L2L154_commutator_le_of_decomp {R A K : Subgroup G}
    (hdec : R ≤ ⁅R, A⁆ ⊔ R ⊓ Subgroup.centralizer (A : Set G))
    (hKR : K ≤ R) (hKn : ∀ x ∈ R, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hRA : ⁅R, A⁆ ≤ K)
    (hCC : ∀ s ∈ R ⊓ Subgroup.centralizer (A : Set G), ∀ t ∈ R ⊓ Subgroup.centralizer (A : Set G),
      ⁅s, t⁆ ∈ K) :
    ⁅R, R⁆ ≤ K := by
  let cen : Set G → Subgroup G := fun T =>
    { carrier := {y | y ∈ R ∧ ∀ t ∈ T, ⁅t, y⁆ ∈ K}
      mul_mem' := fun {y₁ y₂} h₁ h₂ => ⟨R.mul_mem h₁.1 h₂.1, fun t ht => by
        have e : ⁅t, y₁ * y₂⁆ = ⁅t, y₁⁆ * (y₁ * ⁅t, y₂⁆ * y₁⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact K.mul_mem (h₁.2 t ht) (hKn y₁ h₁.1 _ (h₂.2 t ht))⟩
      one_mem' := ⟨R.one_mem, fun t _ => by simp⟩
      inv_mem' := fun {y} h => ⟨R.inv_mem h.1, fun t ht => by
        have e : ⁅t, y⁻¹⁆ = y⁻¹ * ⁅t, y⁆⁻¹ * y⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact hKn y⁻¹ (R.inv_mem h.1) _ (K.inv_mem (h.2 t ht))⟩ }
  have hRAcen : ∀ T : Set G, T ⊆ R → ⁅R, A⁆ ≤ cen T := by
    intro T hT u hu
    refine ⟨hKR (hRA hu), fun t ht => ?_⟩
    rw [commutatorElement_def]
    exact K.mul_mem (hKn t (hT ht) u (hRA hu)) (K.inv_mem (hRA hu))
  have hstageA : ∀ s ∈ R ⊓ Subgroup.centralizer (A : Set G), ∀ y ∈ R, ⁅s, y⁆ ∈ K := by
    intro s hs y hy
    have hle : R ≤ cen {s} := hdec.trans (sup_le (hRAcen {s} (by
        rintro _ rfl; exact hs.1)) (fun u hu => ⟨hu.1, fun t ht => by
          rw [Set.mem_singleton_iff.mp ht]; exact hCC s hs u hu⟩))
    exact (hle hy).2 s rfl
  have hle : R ≤ cen (R : Set G) := hdec.trans (sup_le (hRAcen (R : Set G) le_rfl)
    (fun s hs => ⟨hs.1, fun t ht => by
      have h := K.inv_mem (hstageA s hs t ht)
      rwa [commutatorElement_inv] at h⟩))
  rw [Subgroup.commutator_le]
  intro x hx y hy
  exact (hle hy).2 x hx

private theorem res1L2L154_commutator_self_characteristic (R : Subgroup G) :
    ((⁅R, R⁆ : Subgroup G).subgroupOf R).Characteristic := by
  have hc : (⁅(⊤ : Subgroup R), (⊤ : Subgroup R)⁆).Characteristic := inferInstance
  have hmap : (⁅(⊤ : Subgroup R), (⊤ : Subgroup R)⁆).map R.subtype = ⁅R, R⁆ := by
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have : (⁅R, R⁆ : Subgroup G).subgroupOf R = ⁅(⊤ : Subgroup R), (⊤ : Subgroup R)⁆ := by
    rw [← hmap]
    exact Subgroup.comap_map_eq_self_of_injective R.subtype_injective _
  rw [this]
  exact hc

end Abstract

section L2

variable {P₀ : Type*} [Group P₀] {Y₀ : Type*} [Group Y₀]

private theorem res1L2L154_comm_conj_of_fixed {n : ℕ} (hn : 2 ≤ n)
    (e : Y₀ ≃* ↥(CFSG.PGLModel.projSL 2 (GaloisField 2 n))) {α β : MulAut Y₀} {x : Y₀}
    (hα : α x = x) (hβ : β x = x) :
    ∃ y ∈ Subgroup.centralizer ({x} : Set Y₀), α * β * α⁻¹ * β⁻¹ = MulAut.conj y := by
  obtain ⟨y, hy⟩ := l2_mulAut_commutator_inner hn e α β
  refine ⟨y, ?_, hy⟩
  have hα' : α⁻¹ x = x := by
    rw [MulAut.inv_def, MulEquiv.symm_apply_eq]
    exact hα.symm
  have hβ' : β⁻¹ x = x := by
    rw [MulAut.inv_def, MulEquiv.symm_apply_eq]
    exact hβ.symm
  have h1 : (α * β * α⁻¹ * β⁻¹) x = x := by
    simp [MulAut.mul_apply, hα, hβ, hα', hβ']
  rw [hy] at h1
  rw [Subgroup.mem_centralizer_singleton_iff]
  simp only [MulAut.conj_apply] at h1
  exact mul_inv_eq_iff_eq_mul.mp h1

private theorem res1L2L154_rho_commutator_eq_one {n : ℕ} (hn : 2 ≤ n)
    (e : Y₀ ≃* ↥(CFSG.PGLModel.projSL 2 (GaloisField 2 n))) (ρ : P₀ →* MulAut Y₀)
    {x : Y₀} (hx : orderOf x = 3) {g₁ g₂ : P₀} (h₁ : ρ g₁ x = x) (h₂ : ρ g₂ x = x) {k : ℕ}
    (hk : ⁅g₁, g₂⁆ ^ (2 ^ k) = 1) : ρ ⁅g₁, g₂⁆ = 1 := by
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    omega
  have hxodd : Odd (orderOf x) := by
    rw [hx]
    decide
  obtain ⟨-, hodd⟩ := l2_centralizer_cyclic_odd hn e x hx1 hxodd
  obtain ⟨y, hy, hyeq⟩ := res1L2L154_comm_conj_of_fixed hn e h₁ h₂
  have hyodd : Odd (orderOf y) := by
    have h := orderOf_dvd_natCard (⟨y, hy⟩ : Subgroup.centralizer ({x} : Set Y₀))
    rw [Subgroup.orderOf_mk] at h
    exact Odd.of_dvd_nat hodd h
  have hρ : ρ ⁅g₁, g₂⁆ = MulAut.conj y := by
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact hyeq
  have hd1 : orderOf (ρ ⁅g₁, g₂⁆) ∣ orderOf y := by
    rw [hρ]
    exact orderOf_map_dvd (MulAut.conj : Y₀ →* MulAut Y₀) y
  have hd2 : orderOf (ρ ⁅g₁, g₂⁆) ∣ 2 ^ k :=
    (orderOf_map_dvd ρ _).trans (orderOf_dvd_of_pow_eq_one hk)
  have hodd' : Odd (orderOf (ρ ⁅g₁, g₂⁆)) := Odd.of_dvd_nat hyodd hd1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd2
  rw [← orderOf_eq_one_iff]
  rw [hj] at hodd' ⊢
  rcases j with _ | j
  · rfl
  · exfalso
    exact (Nat.not_even_iff_odd.mpr hodd') ((Nat.even_pow' (by omega)).mpr even_two)

end L2

section Ker

variable {G : Type} [Group G]

theorem res1L2_ker_rho_centralizes_ob {A L : Subgroup G} {Yc : Subgroup (Res1Q A L)} [Yc.Normal]
    {Ob : Subgroup G} (hOC : Ob ≤ Res1C A L)
    (hinj : ∀ u : ↥(Res1C A L), (u : G) ∈ Ob → res1L2Rho A L Yc u = 1 → u = 1)
    {k : ↥(Res1C A L)} (hk : res1L2Rho A L Yc k = 1)
    (hkN : (k : G) ∈ Subgroup.normalizer (Ob : Set G)) :
    (k : G) ∈ Subgroup.centralizer (Ob : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro o ho
  let o' : ↥(Res1C A L) := ⟨o, hOC ho⟩
  have hu : ((k * o' * k⁻¹ * o'⁻¹ : ↥(Res1C A L)) : G) ∈ Ob := by
    have h1 : (k : G) * o * (k : G)⁻¹ ∈ Ob := (Subgroup.mem_normalizer_iff.mp hkN o).mp ho
    exact Ob.mul_mem h1 (Ob.inv_mem ho)
  have hρ : res1L2Rho A L Yc (k * o' * k⁻¹ * o'⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hk]
    simp
  have h : (k : G) * o * (k : G)⁻¹ * o⁻¹ = 1 := congrArg Subtype.val (hinj _ hu hρ)
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
  exact h.symm

end Ker

section Tau

variable {G : Type} [Group G] [Finite G] {Q : ∀ (X : Type) [Group X], Prop} {A : Subgroup G}
  {c : G} {L X K Y M T P' : Subgroup G} {Yc : Subgroup (Res1Q A L)} {z : G}

private theorem res1L2L154_exists_fixed_point [Yc.Normal]
    (τ : Sylow155R1.Res1Tau Q Res1OpenL2Type A c L X K Y M T P' Yc z) :
    ∃ x : ↥Yc, orderOf x = 3 ∧ ∀ u : ↥(Res1C A L), (u : G) ∈ Subgroup.centralizer (A : Set G) →
      res1L2Rho A L Yc u x = x := by
  have hcA : c ∈ A := (zpowers_mem_omegaA_iff.mp τ.std.zpowers_mem_omegaA).1
  obtain ⟨c', hc'Y, hc'⟩ := τ.at_of.2.2.2.1.2.1
  have hc'val : (c' : G) = c := hc'
  have hc'Y' : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c' ∈ Yc :=
    Subgroup.mem_comap.mp hc'Y
  refine ⟨⟨QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c', hc'Y'⟩, ?_, ?_⟩
  · rw [Subgroup.orderOf_mk]
    exact Gagen155R1HJ.res1_orderOf_pi_c'_eq_three τ.std hc'val
  · intro u hu
    apply Subtype.ext
    show QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) u *
        QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c' *
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) u)⁻¹ =
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c'
    rw [mul_inv_eq_iff_eq_mul, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show (u : G) * (c' : G) = (c' : G) * (u : G)
    rw [hc'val]
    exact (Subgroup.mem_centralizer_iff.mp hu c hcA).symm

private theorem res1L2L154_commutator_mem_centralizer [Yc.Normal]
    (τ : Sylow155R1.Res1Tau Q Res1OpenL2Type A c L X K Y M T P' Yc z)
    {r₁ r₂ : G} (h₁ : r₁ ∈ CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer (A : Set G))
    (h₂ : r₂ ∈ CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer (A : Set G)) :
    ⁅r₁, r₂⁆ ∈ Subgroup.centralizer (Sylow155R1.res1Ob A X Y M : Set G) := by
  obtain ⟨n, hn0, h4, ⟨e⟩⟩ := τ.p
  have hn2 : 2 ≤ n := by omega
  obtain ⟨x, hx, hfix⟩ := res1L2L154_exists_fixed_point τ
  have hOA : Sylow155R1.res1Ob A X Y M ≤ Subgroup.centralizer (A : Set G) := τ.e_eq ▸ τ.e_le
  have hOC : Sylow155R1.res1Ob A X Y M ≤ Res1C A L := hOA.trans (res1L2_centralizer_le_res1C A L)
  have hRO : CFSG.Open.pCoreOf 2 Y ≤ Subgroup.normalizer (Sylow155R1.res1Ob A X Y M : Set G) :=
    τ.r_le_host.trans τ.host_le_normalizer_ob
  let u₁ : ↥(Res1C A L) := ⟨r₁, res1L2_centralizer_le_res1C A L h₁.2⟩
  let u₂ : ↥(Res1C A L) := ⟨r₂, res1L2_centralizer_le_res1C A L h₂.2⟩
  have hcomm_mem : ⁅r₁, r₂⁆ ∈ CFSG.Open.pCoreOf 2 Y := by
    rw [commutatorElement_def]
    exact (CFSG.Open.pCoreOf 2 Y).mul_mem ((CFSG.Open.pCoreOf 2 Y).mul_mem
      ((CFSG.Open.pCoreOf 2 Y).mul_mem h₁.1 h₂.1) (inv_mem h₁.1)) (inv_mem h₂.1)
  have hR2 : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 Y) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  obtain ⟨k, hk⟩ := hR2 ⟨⁅r₁, r₂⁆, hcomm_mem⟩
  have hk' : ⁅u₁, u₂⁆ ^ (2 ^ k) = 1 := by
    have h1 := congrArg (fun w : ↥(CFSG.Open.pCoreOf 2 Y) => (w : G)) hk
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h1
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    exact h1
  have hρ := res1L2L154_rho_commutator_eq_one hn2 e (res1L2Rho A L Yc) hx (hfix u₁ h₁.2)
    (hfix u₂ h₂.2) hk'
  exact res1L2_ker_rho_centralizes_ob hOC
    (fun u hu h1 => τ.comm u hu ((res1L2_rho_eq_one_iff u).mp h1)) hρ (hRO hcomm_mem)

theorem res1L2_r_comm
    (τ : Sylow155R1.Res1Tau Q Res1OpenL2Type A c L X K Y M T P' Yc z) :
    ∀ a ∈ CFSG.Open.pCoreOf 2 Y, ∀ b ∈ CFSG.Open.pCoreOf 2 Y, a * b = b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Yc.Normal := Sylow155R1.res1_isComponent_normal τ.std τ.at_of.1 τ.at_of.2.2.2.1.1
  have hOA : Sylow155R1.res1Ob A X Y M ≤ Subgroup.centralizer (A : Set G) := τ.e_eq ▸ τ.e_le
  have hRO : CFSG.Open.pCoreOf 2 Y ≤ Subgroup.normalizer (Sylow155R1.res1Ob A X Y M : Set G) :=
    τ.r_le_host.trans τ.host_le_normalizer_ob
  set R := CFSG.Open.pCoreOf 2 Y with hRdef
  set Ob := Sylow155R1.res1Ob A X Y M with hObdef
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := fun a ha =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y (τ.ctx.isY.1.1.1.2 ha)
  have hR2 : IsPGroup 2 ↥R := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hA3 : IsPGroup 3 ↥A := CFSG.Open.IsElemAbelian.isPGroup τ.sec15.mem_partTwoF.1
  have hcop : Nat.Coprime (Nat.card A) (Nat.card R) := by
    obtain ⟨a, ha⟩ := hA3.exists_card_eq
    obtain ⟨b, hb⟩ := hR2.exists_card_eq
    rw [ha, hb]
    exact Nat.Coprime.pow _ _ (by norm_num)
  have hsolv : Group.IsSolvable ↥R := by
    have := hR2.isNilpotent
    infer_instance
  have hdec : R ≤ ⁅R, A⁆ ⊔ R ⊓ Subgroup.centralizer (A : Set G) :=
    CFSG.GroupTheory.le_commutator_sup_inf_centralizer_of_coprime_of_finite hAR hcop hsolv
  have hRcomm : ∀ s ∈ R, ∀ t ∈ R, ⁅s, t⁆ ∈ R := fun s hs t ht => by
    rw [commutatorElement_def]
    exact R.mul_mem (R.mul_mem (R.mul_mem hs ht) (R.inv_mem hs)) (R.inv_mem ht)
  have hKn : ∀ x ∈ R, ∀ k ∈ R ⊓ Subgroup.centralizer (Ob : Set G),
      x * k * x⁻¹ ∈ R ⊓ Subgroup.centralizer (Ob : Set G) := fun x hx k hk =>
    ⟨R.mul_mem (R.mul_mem hx hk.1) (R.inv_mem hx),
      res1L2L154_conj_mem_centralizer (hRO hx) hk.2⟩
  have hRA : ⁅R, A⁆ ≤ R ⊓ Subgroup.centralizer (Ob : Set G) :=
    le_inf (res1L2L154_commutator_le_left hAR) (res1L2_commutator_r_a_centralizes_ob hOA hRO)
  have hCC : ∀ s ∈ R ⊓ Subgroup.centralizer (A : Set G), ∀ t ∈ R ⊓ Subgroup.centralizer (A : Set G),
      ⁅s, t⁆ ∈ R ⊓ Subgroup.centralizer (Ob : Set G) := fun s hs t ht =>
    ⟨hRcomm s hs.1 t ht.1, res1L2L154_commutator_mem_centralizer τ hs ht⟩
  have hRR : ⁅R, R⁆ ≤ Subgroup.centralizer (Ob : Set G) :=
    (res1L2L154_commutator_le_of_decomp hdec inf_le_left hKn hRA hCC).trans inf_le_right
  have hbot : ⁅R, R⁆ = ⊥ := by
    by_contra hne
    apply τ.ob_not_le
    have hle : ⁅R, R⁆ ≤ R := res1L2L154_commutator_le_left Subgroup.le_normalizer
    have hclaim := τ.endN.claim ⁅R, R⁆ hne hle (res1L2L154_commutator_self_characteristic R)
    have hQ : Ob ∈ scriptQ A (lB A) :=
      Sylow155R1.pPrimeCoreOf_two_host_mem_scriptQ τ.std τ.i146 τ.ctx τ.endN τ.r_le
    have hON : Ob ≤ Subgroup.normalizer ((⁅R, R⁆ : Subgroup G) : Set G) :=
      (Subgroup.le_centralizer_iff.mp hRR).trans (Subgroup.centralizer_le_normalizer _)
    exact (le_delta hQ hON).trans hclaim
  intro a ha b hb
  have h := Subgroup.commutator_mem_commutator ha hb
  rw [hbot, Subgroup.mem_bot, commutatorElement_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
  exact h

end Tau

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2
