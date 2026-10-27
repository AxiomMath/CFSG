module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45K22pDefs
public import CFSG.GroupTheory.PCore.OpenTransport
public import Certificates.Data.A5

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open Subgroup
open scoped commutatorElement

lemma not_isSolvable_alternatingGroup_five : ¬ IsSolvable (alternatingGroup (Fin 5)) := by
  intro h
  have hcomm : ∀ a b : alternatingGroup (Fin 5), a * b = b * a :=
    (IsSimpleGroup.comm_iff_isSolvable).mpr h
  obtain ⟨a, b, hab⟩ : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a := by decide
  exact hab (hcomm a b)

lemma card_sup_dvd_mul_card {G : Type*} [Group G] (H K : Subgroup G) [H.Normal] :
    Nat.card ↥(H ⊔ K) ∣ Nat.card ↥H * Nat.card ↥K := by
  let M : Subgroup ↥(H ⊔ K) := H.subgroupOf (H ⊔ K)
  let φ : ↥K →* ↥(H ⊔ K) ⧸ M :=
    (QuotientGroup.mk' M).comp (Subgroup.inclusion (le_sup_right : K ≤ H ⊔ K))
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective M y
    obtain ⟨a, ha, b, hb, rfl⟩ := (Subgroup.mem_sup_of_normal_left (s := H) (t := K)).mp hx
    refine ⟨⟨b, hb⟩, ?_⟩
    simp only [φ, MonoidHom.comp_apply]
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simpa [mul_assoc] using (inferInstance : H.Normal).conj_mem' a ha b
  have hcard : Nat.card ↥(H.subgroupOf (H ⊔ K)) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : H ≤ H ⊔ K)).toEquiv
  have hq : Nat.card (↥(H ⊔ K) ⧸ M) ∣ Nat.card K :=
    Subgroup.card_dvd_of_surjective hφ
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup M, hcard]
  have h := mul_dvd_mul_right hq (Nat.card H)
  rw [mul_comm (Nat.card K) (Nat.card H)] at h
  exact h

lemma isSolvable_sup_of_isSolvable_of_normal {G : Type*} [Group G] {H K : Subgroup G}
    [H.Normal] (hH : Group.IsSolvable ↥H) (hK : Group.IsSolvable ↥K) :
    Group.IsSolvable ↥(H ⊔ K) := by
  haveI : Group.IsSolvable ↥H := hH
  let M : Subgroup ↥(H ⊔ K) := H.subgroupOf (H ⊔ K)
  have hM : M.Normal := Subgroup.normal_subgroupOf
  haveI : M.Normal := hM
  have hMsolv : Group.IsSolvable ↥M :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (le_sup_left : H ≤ H ⊔ K)).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe le_sup_left).injective
  let φ : ↥K →* ↥(H ⊔ K) ⧸ M :=
    (QuotientGroup.mk' M).comp (Subgroup.inclusion (le_sup_right : K ≤ H ⊔ K))
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective M y
    obtain ⟨a, ha, b, hb, rfl⟩ := (Subgroup.mem_sup_of_normal_left (s := H) (t := K)).mp hx
    refine ⟨⟨b, hb⟩, ?_⟩
    simp only [φ, MonoidHom.comp_apply]
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simpa [mul_assoc] using (inferInstance : H.Normal).conj_mem' a ha b
  haveI : Group.IsSolvable ↥K := hK
  haveI : Group.IsSolvable ↥M := hMsolv
  have hQsolv : Group.IsSolvable (↥(H ⊔ K) ⧸ M) := Group.isSolvable_of_surjective hφ
  haveI : Group.IsSolvable (↥(H ⊔ K) ⧸ M) := hQsolv
  exact Group.isSolvable_of_subgroup_quotient M

lemma map_conj_le_sup {Γ : Type*} [Group Γ] (K D : Subgroup Γ) [K.Normal] (k : Γ) (hk : k ∈ K) :
    D.map (MulAut.conj k).toMonoidHom ≤ K ⊔ D := by
  rintro _ ⟨y, hy, rfl⟩
  change MulAut.conj k y ∈ K ⊔ D
  rw [MulAut.conj_apply]
  have h1 : y * k⁻¹ * y⁻¹ ∈ K := (inferInstance : K.Normal).conj_mem k⁻¹ (K.inv_mem hk) y
  have h2 : k * (y * k⁻¹ * y⁻¹) ∈ K := K.mul_mem hk h1
  have heq : k * y * k⁻¹ = (k * (y * k⁻¹ * y⁻¹)) * y := by group
  rw [heq]
  exact Subgroup.mul_mem_sup h2 hy

lemma quotient_pCoreOf_isCyclic_card_three {Γ : Type} [Group Γ] (Y : Subgroup Γ)
    (N : Subgroup ↥Y) [N.Normal] (hN : N = (CFSG.Open.pCoreOf 2 Y).subgroupOf Y)
    (hYsolv : Group.IsSolvable ↥Y) (h9 : ¬ 9 ∣ Nat.card Y) (hshape : Z3E9A5Mod2 Y) :
    IsCyclic (↥Y ⧸ N) ∧ Nat.card (↥Y ⧸ N) = 3 := by
  rcases hshape N hN with ⟨hcyc, hcard⟩ | ⟨hcard9, -⟩ | hisAlt
  · exact ⟨hcyc, hcard⟩
  · exfalso
    haveI : Group.IsSolvable ↥Y := hYsolv
    exact h9 (hcard9 ▸ Subgroup.card_quotient_dvd_card N)
  · exfalso
    obtain ⟨e⟩ := hisAlt
    haveI : Group.IsSolvable ↥Y := hYsolv
    haveI : Group.IsSolvable (↥Y ⧸ N) := inferInstance
    exact not_isSolvable_alternatingGroup_five
      (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)

lemma pairSubgroup_shape {Γ : Type} [Group Γ] {Dbar Kbar : Subgroup Γ} [Kbar.Normal]
    (hD : Nat.card Dbar = 3) (hsolv : Group.IsSolvable ↥Kbar)
    (hcop : Nat.Coprime 3 (Nat.card Kbar)) {k : Γ} (hk : k ∈ Kbar) :
    (Dbar ⊔ Dbar.map (MulAut.conj k).toMonoidHom) ≤ Kbar ⊔ Dbar ∧
      Group.IsSolvable ↥(Dbar ⊔ Dbar.map (MulAut.conj k).toMonoidHom) ∧
      ¬ 9 ∣ Nat.card ↥(Dbar ⊔ Dbar.map (MulAut.conj k).toMonoidHom) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYle : Dbar ⊔ Dbar.map (MulAut.conj k).toMonoidHom ≤ Kbar ⊔ Dbar :=
    sup_le le_sup_right (map_conj_le_sup Kbar Dbar k hk)
  have hsupSolv : Group.IsSolvable ↥(Kbar ⊔ Dbar) := by
    haveI : IsCyclic ↥Dbar := isCyclic_of_prime_card hD
    have hDsolv : Group.IsSolvable ↥Dbar := inferInstance
    exact isSolvable_sup_of_isSolvable_of_normal hsolv hDsolv
  have hYsolv : Group.IsSolvable ↥(Dbar ⊔ Dbar.map (MulAut.conj k).toMonoidHom) := by
    haveI : Group.IsSolvable ↥(Kbar ⊔ Dbar) := hsupSolv
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hYle)
      (Subgroup.inclusion_injective hYle)
  refine ⟨hYle, hYsolv, ?_⟩
  intro h9dvd
  have hdvd : Nat.card ↥(Dbar ⊔ Dbar.map (MulAut.conj k).toMonoidHom) ∣ 3 * Nat.card Kbar := by
    refine (Subgroup.card_dvd_of_le hYle).trans ?_
    rw [← hD, mul_comm]
    exact card_sup_dvd_mul_card Kbar Dbar
  have h3 : 3 ∣ Nat.card Kbar := by
    have h : 3 * 3 ∣ 3 * Nat.card Kbar := by
      rw [show (9 : ℕ) = 3 * 3 from rfl] at h9dvd
      exact h9dvd.trans hdvd
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 3)).mp h
  exact (Nat.prime_three.coprime_iff_not_dvd).mp hcop h3

lemma mem_pCoreOf_of_isSolvable_of_shape {Γ : Type} [Group Γ] (Y K : Subgroup Γ)
    (hYsolv : Group.IsSolvable ↥Y) (h9 : ¬ 9 ∣ Nat.card Y) (hshape : Z3E9A5Mod2 Y)
    (hcop : Nat.Coprime 3 (Nat.card K)) {e : Γ} (heY : e ∈ Y) (heK : e ∈ K) :
    e ∈ CFSG.Open.pCoreOf 2 Y := by
  let N : Subgroup ↥Y := (CFSG.Open.pCoreOf 2 Y).subgroupOf Y
  have hNnormal : N.Normal := by
    rw [show N = (CFSG.Open.pCoreOf 2 Y).subgroupOf Y from rfl,
      CFSG.openPCoreOf_subgroupOf]
    exact CFSG.pCore_normal
  haveI : N.Normal := hNnormal
  haveI : Group.IsSolvable ↥Y := hYsolv
  obtain ⟨-, hcard⟩ :=
    quotient_pCoreOf_isCyclic_card_three Y N rfl hYsolv h9 hshape
  let q : ↥Y ⧸ N := QuotientGroup.mk' N ⟨e, heY⟩
  have hcardN : Nat.card (↥Y ⧸ N) = 3 := hcard
  have hdvd3 : orderOf q ∣ 3 := by
    have h := orderOf_dvd_natCard q
    rw [hcardN] at h
    exact h
  have hdvdE : orderOf q ∣ orderOf e := by
    have h := orderOf_map_dvd (QuotientGroup.mk' N) (⟨e, heY⟩ : ↥Y)
    rw [Subgroup.orderOf_mk] at h
    exact h
  have hdvdK : orderOf e ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K heK
  have hdvd1 : orderOf q ∣ 1 := by
    have hg : orderOf q ∣ Nat.gcd 3 (Nat.card K) := Nat.dvd_gcd hdvd3 (hdvdE.trans hdvdK)
    rw [Nat.coprime_iff_gcd_eq_one.mp hcop] at hg
    exact hg
  have hq1 : q = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)
  have hmemN : (⟨e, heY⟩ : ↥Y) ∈ N := by
    rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
    exact hq1
  rw [show N = (CFSG.Open.pCoreOf 2 Y).subgroupOf Y from rfl] at hmemN
  simpa using Subgroup.mem_subgroupOf.mp hmemN

lemma conj_mem_commSub {M : Type} [Group M] (σ : MulAut M) (m : M) {c : M}
    (hc : c ∈ K22p.commSub σ) : m * c * m⁻¹ ∈ K22p.commSub σ := by
  let C := K22p.commSub σ
  change c ∈ C at hc
  change m * c * m⁻¹ ∈ C
  induction hc using Subgroup.closure_induction with
  | mem z hz =>
      rcases hz with ⟨x, rfl⟩
      have hgen1 : (x * m⁻¹)⁻¹ * σ (x * m⁻¹) ∈ C :=
        Subgroup.subset_closure ⟨x * m⁻¹, rfl⟩
      have hgen2 : (m⁻¹⁻¹ * σ m⁻¹)⁻¹ ∈ C :=
        C.inv_mem (Subgroup.subset_closure ⟨m⁻¹, rfl⟩)
      have heq : m * (x⁻¹ * σ x) * m⁻¹ =
          ((x * m⁻¹)⁻¹ * σ (x * m⁻¹)) * (m⁻¹⁻¹ * σ m⁻¹)⁻¹ := by
        simp only [map_mul, map_inv]
        group
      rw [heq]
      exact C.mul_mem hgen1 hgen2
  | one => simpa using C.one_mem
  | mul x y _ _ ihx ihy =>
      have heq : m * (x * y) * m⁻¹ = m * x * m⁻¹ * (m * y * m⁻¹) := by group
      rw [heq]
      exact C.mul_mem ihx ihy
  | inv x _ ih =>
      have heq : m * x⁻¹ * m⁻¹ = (m * x * m⁻¹)⁻¹ := by group
      rw [heq]
      exact C.inv_mem ih

lemma inv_mul_conj_mem_sup_conj {Γ : Type} [Group Γ] {Dbar : Subgroup Γ} {k d : Γ}
    (hdmem : d ∈ Dbar) :
    d⁻¹ * (k * d * k⁻¹) ∈ Dbar ⊔ Dbar.map (MulAut.conj k).toMonoidHom := by
  have h1 : d⁻¹ ∈ Dbar ⊔ Dbar.map (MulAut.conj k).toMonoidHom :=
    Subgroup.mem_sup_left (Dbar.inv_mem hdmem)
  have h2 : k * d * k⁻¹ ∈ Dbar ⊔ Dbar.map (MulAut.conj k).toMonoidHom :=
    Subgroup.mem_sup_right (Subgroup.mem_map_of_mem (MulAut.conj k).toMonoidHom hdmem)
  exact (Dbar ⊔ Dbar.map (MulAut.conj k).toMonoidHom).mul_mem h1 h2

lemma inv_mul_conj_mem {Γ : Type} [Group Γ] {Kbar : Subgroup Γ} [Kbar.Normal] {k d : Γ}
    (hk : k ∈ Kbar) : d⁻¹ * (k * d * k⁻¹) ∈ Kbar := by
  have hcomm : ⁅k, d⁆ ∈ Kbar := by
    have hconj : d * k⁻¹ * d⁻¹ ∈ Kbar :=
      (inferInstance : Kbar.Normal).conj_mem k⁻¹ (Kbar.inv_mem hk) d
    have heq : ⁅k, d⁆ = k * (d * k⁻¹ * d⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [heq]
    exact Kbar.mul_mem hk hconj
  have heq : d⁻¹ * (k * d * k⁻¹) = d⁻¹ * ⁅k, d⁆ * d := by
    simp only [commutatorElement_def]
    group
  rw [heq]
  simpa using (inferInstance : Kbar.Normal).conj_mem ⁅k, d⁆ hcomm d⁻¹

lemma exists_orderOf_dvd_two_of_mem_pCoreOf {Γ : Type} [Group Γ] {Y : Subgroup Γ} {e : Γ}
    (heY : e ∈ Y) (he : e ∈ CFSG.Open.pCoreOf 2 Y) : ∃ m, orderOf e ∣ 2 ^ m := by
  have hmem : (⟨e, heY⟩ : ↥Y) ∈ CFSG.pCore 2 ↥Y :=
    (CFSG.mem_openPCoreOf_iff (p := 2) (H := Y) ⟨e, heY⟩).mp he
  obtain ⟨m, hm⟩ := IsPGroup.exists_orderOf_dvd_pow
    (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)) (⟨⟨e, heY⟩, hmem⟩ : ↥(CFSG.pCore 2 ↥Y))
  refine ⟨m, ?_⟩
  simp only [Subgroup.orderOf_mk] at hm
  exact hm

lemma orderOf_inv_mul_conjNormal_eq_orderOf {Γ : Type} [Group Γ] {Kbar : Subgroup Γ}
    [Kbar.Normal] (d : Γ) (x : ↥Kbar) :
    orderOf (x⁻¹ * MulAut.conjNormal d x) =
      orderOf (d⁻¹ * ((x : Γ)⁻¹ * d * ((x : Γ)⁻¹)⁻¹)) := by
  have hcoeeq : ((x⁻¹ * MulAut.conjNormal d x : ↥Kbar) : Γ) =
      d * (d⁻¹ * ((x : Γ)⁻¹ * d * ((x : Γ)⁻¹)⁻¹)) * d⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply]
    group
  have hsem : SemiconjBy d (d⁻¹ * ((x : Γ)⁻¹ * d * ((x : Γ)⁻¹)⁻¹))
      (d * (d⁻¹ * ((x : Γ)⁻¹ * d * ((x : Γ)⁻¹)⁻¹)) * d⁻¹) := by
    simp only [SemiconjBy]
    group
  rw [← Subgroup.orderOf_coe (x⁻¹ * MulAut.conjNormal d x), hcoeeq]
  exact (SemiconjBy.orderOf_eq d hsem).symm

lemma exists_orderOf_inv_mul_conjNormal_dvd_two {Γ : Type} [Group Γ] [Finite Γ]
    {Dbar Kbar : Subgroup Γ} [Kbar.Normal] (d : Γ) (hdmem : d ∈ Dbar)
    (hD : Nat.card Dbar = 3)
    (hpair : ∀ k ∈ Kbar, Z3E9A5Mod2 (Dbar ⊔ Dbar.map (MulAut.conj k).toMonoidHom))
    (hsolv : Group.IsSolvable ↥Kbar) (hcop : Nat.Coprime 3 (Nat.card Kbar)) (x : ↥Kbar) :
    ∃ m, orderOf (x⁻¹ * MulAut.conjNormal d x) ∣ 2 ^ m := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let k : Γ := (x : Γ)⁻¹
  have hk : k ∈ Kbar := by
    dsimp only [k]
    exact Kbar.inv_mem x.2
  obtain ⟨hYle, hYsolv, h9⟩ := pairSubgroup_shape hD hsolv hcop hk
  have hshape : Z3E9A5Mod2 (Dbar ⊔ Dbar.map (MulAut.conj k).toMonoidHom) := hpair k hk
  have heY : d⁻¹ * (k * d * k⁻¹) ∈ Dbar ⊔ Dbar.map (MulAut.conj k).toMonoidHom :=
    inv_mul_conj_mem_sup_conj hdmem
  have heK : d⁻¹ * (k * d * k⁻¹) ∈ Kbar := inv_mul_conj_mem hk
  have hepCore : d⁻¹ * (k * d * k⁻¹) ∈
      CFSG.Open.pCoreOf 2 (Dbar ⊔ Dbar.map (MulAut.conj k).toMonoidHom) :=
    mem_pCoreOf_of_isSolvable_of_shape _ Kbar hYsolv h9 hshape hcop heY heK
  obtain ⟨m, hm⟩ := exists_orderOf_dvd_two_of_mem_pCoreOf heY hepCore
  refine ⟨m, ?_⟩
  rw [orderOf_inv_mul_conjNormal_eq_orderOf]
  exact hm

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46
