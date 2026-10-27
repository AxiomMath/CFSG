module

public import CFSG.RankThree.PartTwo.Sec6.Item612Fitting
import CFSG.LocalAnalysis.RankThreeEvenClassification.HallContainment
public import CFSG.RankThree.GroupTheory.SteinbergBYAlphaTransport
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport

public section

namespace CFSG.RankThree.PartTwo.Sec6.Res611Res4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThreeEvenClassification.Helpers

section Hall

variable {X : Type*} [Group X] [Finite X]

theorem exists_invariant_threeLift {N P E S : Subgroup X}
    (hNsol : Group.IsSolvable N) (hNodd : Odd (Nat.card N)) (hN3 : ¬ 3 ∣ Nat.card N)
    (hNP : N ≤ P) (hPN : P ≤ Subgroup.normalizer (N : Set X))
    (hP3 : ∀ x ∈ P, ∃ k : ℕ, x ^ 3 ^ k ∈ N)
    (hE : IsPGroup 3 E) (hS : IsPGroup 2 S) (hES : E ≤ Subgroup.normalizer (S : Set X))
    (hESP : E ⊔ S ≤ Subgroup.normalizer (P : Set X))
    (hESN : E ⊔ S ≤ Subgroup.normalizer (N : Set X)) :
    ∃ R : Subgroup X, R ≤ P ∧ IsPGroup 3 R ∧ E ⊔ S ≤ Subgroup.normalizer (R : Set X) ∧
      ∀ x ∈ P, ∃ r ∈ R, r⁻¹ * x ∈ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hNPn : (N.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNP).mpr hPN
  have hPsol : Group.IsSolvable P := by
    have hq3 : IsPGroup 3 (P ⧸ N.subgroupOf P) := by
      intro z
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf P) z
      obtain ⟨k, hk⟩ := hP3 x x.2
      refine ⟨k, ?_⟩
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using hk
    have : Group.IsNilpotent (P ⧸ N.subgroupOf P) := hq3.isNilpotent
    have : Group.IsSolvable (N.subgroupOf P) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hNP).toMonoidHom) (MulEquiv.injective _)
    exact Group.isSolvable_of_ker_le_range (N.subgroupOf P).subtype
      (QuotientGroup.mk' (N.subgroupOf P))
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  set ES := E ⊔ S with hESdef
  have hESsol : Group.IsSolvable ES := by
    have : Group.IsNilpotent S := hS.isNilpotent
    have : Group.IsNilpotent E := hE.isNilpotent
    have h1 := isSolvable_sup_of_le_normalizer hES inferInstance inferInstance
    rwa [sup_comm] at h1
  set M := P ⊔ ES with hM
  have hMsol : Group.IsSolvable M := isSolvable_sup_of_le_normalizer hESP hPsol hESsol
  have hESM : ES ≤ M := le_sup_right
  have hPM : P ≤ M := le_sup_left
  have hNM : N ≤ M := hNP.trans hPM
  have hMN : M ≤ Subgroup.normalizer (N : Set X) := sup_le hPN hESN
  have hMP : M ≤ Subgroup.normalizer (P : Set X) := sup_le Subgroup.le_normalizer hESP
  set π : Set ℕ := {2, 3} with hπ
  have h2π : 2 ∈ π := by rw [hπ]; exact Set.mem_insert 2 _
  have h3π : 3 ∈ π := by rw [hπ]; simp
  have hESπ : PrimeSetOrder π (Nat.card (ES.subgroupOf M)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hESM).toEquiv, hESdef, sup_comm]
    exact normalized_sup_primeSetOrder π S E hES (primeSetOrder_of_isPGroup h2π hS)
      (primeSetOrder_of_isPGroup h3π hE)
  obtain ⟨Hl, hHl, hESHl⟩ := hall_containment_of_solvable π (ES.subgroupOf M) hESπ
  set θM := N.subgroupOf M with hθMdef
  have hθMn : θM.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mpr hMN
  have hθMcard : Nat.card θM = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
  have hθπ : PrimeSetOrder πᶜ (Nat.card θM) := by
    intro q hq hqd
    rw [hθMcard] at hqd
    simp only [hπ, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨fun h2 => ?_, fun h3 => ?_⟩
    swap
    · rw [h3] at hqd
      exact hN3 hqd
    rw [h2] at hqd
    exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr hqd)
  have hcardM : Nat.card M = Nat.card (M ⧸ θM) * Nat.card θM :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup θM
  set PM := P.subgroupOf M with hPMdef
  have hPMn : PM.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hPM).mpr hMP
  have hMπ : PrimeSetOrder π (Nat.card (M ⧸ θM)) := by
    set ρ := QuotientGroup.mk' θM with hρ
    have hρs : Function.Surjective ρ := QuotientGroup.mk'_surjective θM
    have htop : PM ⊔ ES.subgroupOf M = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hPM hESM, ← hM, Subgroup.subgroupOf_self]
    have heq : PM.map ρ ⊔ (ES.subgroupOf M).map ρ = ⊤ := by
      rw [← Subgroup.map_sup, htop, Subgroup.map_top_of_surjective _ hρs]
    have hPMρ : (PM.map ρ).Normal := hPMn.map ρ hρs
    have hPM3 : IsPGroup 3 (PM.map ρ) := by
      rintro ⟨_, x, hx, rfl⟩
      obtain ⟨k, hk⟩ := hP3 x (Subgroup.mem_subgroupOf.mp hx)
      refine ⟨k, Subtype.ext ?_⟩
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
      rw [← map_pow, hρ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf]
      simpa using hk
    rw [← Subgroup.card_top (G := M ⧸ θM), ← heq]
    exact normalized_sup_primeSetOrder π (PM.map ρ) ((ES.subgroupOf M).map ρ)
      (by rw [Subgroup.normalizer_eq_top (PM.map ρ)]; exact le_top)
      (primeSetOrder_of_isPGroup h3π hPM3)
      (PrimeSetOrder.of_dvd π _ _ hESπ (Subgroup.card_map_dvd _ ρ))
  have hindex : Hl.index = Nat.card θM := by
    have h1 : Nat.card Hl * Hl.index = Nat.card (M ⧸ θM) * Nat.card θM := by
      rw [Subgroup.card_mul_index, hcardM]
    have hc1 : (Nat.card Hl).Coprime (Nat.card θM) := PrimeSetOrder.coprime_compl π _ _ hHl.1 hθπ
    have hc2 : (Nat.card (M ⧸ θM)).Coprime Hl.index :=
      PrimeSetOrder.coprime_compl π _ _ hMπ hHl.2
    apply Nat.dvd_antisymm
    · exact (hc2.symm).dvd_of_dvd_mul_left (h1 ▸ Dvd.intro_left _ rfl)
    · exact (hc1.symm).dvd_of_dvd_mul_left (h1.symm ▸ Dvd.intro_left _ rfl)
  have hdisj : Disjoint Hl θM :=
    Subgroup.disjoint_of_coprime_natCard (PrimeSetOrder.coprime_compl π _ _ hHl.1 hθπ)
  have hsup : Hl ⊔ θM = ⊤ := (Subgroup.isComplement'_of_card_mul_and_disjoint
    (by rw [← hindex, Subgroup.card_mul_index]) hdisj).sup_eq_top
  set R := Hl ⊓ PM with hR
  have hθMPM : θM ≤ PM := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hNP (Subgroup.mem_subgroupOf.mp hx))
  refine ⟨R.map M.subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨r, hr, rfl⟩
    exact Subgroup.mem_subgroupOf.mp hr.2
  · rintro ⟨_, r, hr, rfl⟩
    obtain ⟨k, hk⟩ := hP3 r (Subgroup.mem_subgroupOf.mp hr.2)
    have hθk : r ^ (3 ^ k) ∈ θM := by
      rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
      exact hk
    have hHk : r ^ (3 ^ k) ∈ Hl := Hl.pow_mem hr.1 _
    have h1 : r ^ (3 ^ k) = 1 := Subgroup.disjoint_def.mp hdisj hHk hθk
    refine ⟨k, Subtype.ext ?_⟩
    simp only [SubmonoidClass.coe_pow, Subgroup.coe_subtype, OneMemClass.coe_one]
    rw [← Subgroup.coe_pow, h1, OneMemClass.coe_one]
  · intro g hg
    set g' : M := ⟨g, hESM hg⟩
    have hg'H : g' ∈ Hl := hESHl (Subgroup.mem_subgroupOf.mpr hg)
    have hg'R : g' ∈ Subgroup.normalizer (R : Set M) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg'H,
        by rw [Subgroup.normalizer_eq_top PM]; exact Subgroup.mem_top _⟩
    exact Subgroup.le_normalizer_map M.subtype ⟨g', hg'R, rfl⟩
  · intro x hx
    have hx' : (⟨x, hPM hx⟩ : M) ∈ Hl ⊔ θM := hsup ▸ Subgroup.mem_top _
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.mp hx'
    have hxPM : (⟨x, hPM hx⟩ : M) ∈ PM := Subgroup.mem_subgroupOf.mpr hx
    have hyP : y ∈ PM := by
      have h1 := PM.mul_mem hxPM (inv_mem (hθMPM hz))
      rwa [← hyz, mul_inv_cancel_right] at h1
    refine ⟨(y : X), ⟨y, ⟨hy, hyP⟩, rfl⟩, ?_⟩
    have h2 : (y : X)⁻¹ * x = (z : X) := by
      have h3 := congrArg Subtype.val hyz
      simp only [Subgroup.coe_mul] at h3
      rw [← h3]
      group
    rw [h2]
    exact Subgroup.mem_subgroupOf.mp hz

end Hall

section Fix

variable {X : Type*} [Group X]

theorem fix_of_fix_pCore (τ : MulAut X) (hτ : τ * τ = 1) {C : Subgroup X}
    (hC : ∀ x ∈ C, τ x ∈ C) (hP : ∀ x ∈ inSubgroup (CFSG.pCore 3) C, τ x = x)
    (hK : C ⊓ Subgroup.centralizer (inSubgroup (CFSG.pCore 3) C : Set X) ≤
      inSubgroup (CFSG.pCore 3) C) :
    ∀ x ∈ C, τ x = x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P := inSubgroup (CFSG.pCore 3) C with hPdef
  have hP3 : IsPGroup 3 P := CFSG.pCore_isPGroup.map _
  have hPn : ∀ x ∈ C, ∀ p ∈ P, x * p * x⁻¹ ∈ P := by
    rintro x hx _ ⟨p, hp, rfl⟩
    exact ⟨⟨x, hx⟩ * p * ⟨x, hx⟩⁻¹, CFSG.pCore_normal.conj_mem p hp _, rfl⟩
  intro x hx
  set y := x⁻¹ * τ x with hy
  have hyC : y ∈ C := C.mul_mem (C.inv_mem hx) (hC x hx)
  have hyc : y ∈ Subgroup.centralizer (P : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have h1 : τ (x * p * x⁻¹) = x * p * x⁻¹ := hP _ (hPn x hx p hp)
    rw [map_mul, map_mul, map_inv, hP p hp] at h1
    calc p * (x⁻¹ * τ x) = x⁻¹ * (x * p * x⁻¹) * τ x := by group
      _ = x⁻¹ * (τ x * p * (τ x)⁻¹) * τ x := by rw [h1]
      _ = x⁻¹ * τ x * p := by group
  have hyP : y ∈ P := hK ⟨hyC, hyc⟩
  have hτx : τ x = x * y := by rw [hy]; group
  have hy2 : y ^ 2 = 1 := by
    have h1 : τ (τ x) = x := by rw [← MulAut.mul_apply, hτ, MulAut.one_apply]
    rw [hτx, map_mul, hP y hyP, hτx, mul_assoc] at h1
    rw [pow_two]
    exact mul_eq_left.mp h1
  obtain ⟨k, hk⟩ := hP3 ⟨y, hyP⟩
  have hk' : y ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hord : orderOf y ∣ Nat.gcd (3 ^ k) 2 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one hy2)
  have hg : Nat.gcd (3 ^ k) 2 = 1 := Nat.Coprime.pow_left k (by norm_num)
  rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at hord
  rw [hτx, hord, mul_one]

end Fix

section Stab

variable {X : Type*} [Group X]

@[expose] def stabAut (H : Subgroup X) : Subgroup (MulAut X) where
  carrier := {α | ∀ x, α x ∈ H ↔ x ∈ H}
  mul_mem' {α β} hα hβ x := by
    rw [MulAut.mul_apply]
    exact (hα (β x)).trans (hβ x)
  one_mem' x := by rw [MulAut.one_apply]
  inv_mem' {α} hα x := by
    have h := hα (α⁻¹ x)
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply] at h
    exact h.symm

@[expose] def fixAut (H : Subgroup X) : Subgroup (MulAut X) where
  carrier := {α | ∀ x ∈ H, α x = x}
  mul_mem' {α β} hα hβ x hx := by rw [MulAut.mul_apply, hβ x hx, hα x hx]
  one_mem' x _ := by rw [MulAut.one_apply]
  inv_mem' {α} hα x hx := by
    have h := hα x hx
    calc α⁻¹ x = α⁻¹ (α x) := by rw [h]
      _ = x := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]

theorem fixAut_le_stabAut (H : Subgroup X) : fixAut H ≤ stabAut H := by
  intro α hα x
  constructor
  · intro hx
    have h := ((fixAut H).inv_mem hα) (α x) hx
    rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply] at h
    rw [h]
    exact hx
  · intro hx
    rw [hα x hx]
    exact hx

theorem fixAut_anti {H H' : Subgroup X} (h : H ≤ H') : fixAut H' ≤ fixAut H :=
  fun _ hα x hx => hα x (h hx)

theorem map_eq_of_mem_stabAut {H : Subgroup X} {α : MulAut X} (hα : α ∈ stabAut H) :
    H.map α.toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hα y).mpr hy
  · intro hx
    refine ⟨α⁻¹ x, ((stabAut H).inv_mem hα x).mpr hx, ?_⟩
    change α (α⁻¹ x) = x
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]

theorem stabAut_le_stabAut_centralizer (H : Subgroup X) :
    stabAut H ≤ stabAut (Subgroup.centralizer (H : Set X)) := by
  have key : ∀ α ∈ stabAut H, ∀ x ∈ Subgroup.centralizer (H : Set X),
      α x ∈ Subgroup.centralizer (H : Set X) := by
    intro α hα x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro h hh
    have h1 : α⁻¹ h ∈ H := ((stabAut H).inv_mem hα h).mpr hh
    have h2 := hx _ h1
    have h3 : α (α⁻¹ h) = h := by rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
    have h4 := congrArg α h2
    rwa [map_mul, map_mul, h3] at h4
  intro α hα x
  constructor
  · intro hx
    have h := key α⁻¹ ((stabAut H).inv_mem hα) _ hx
    rwa [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply] at h
  · exact key α hα x

theorem stabAut_le_stabAut_pCore (C : Subgroup X) :
    stabAut C ≤ stabAut (inSubgroup (CFSG.pCore 3) C) := by
  have key : ∀ α ∈ stabAut C, ∀ x ∈ inSubgroup (CFSG.pCore 3) C,
      α x ∈ inSubgroup (CFSG.pCore 3) C := by
    intro α hα x hx
    have h := CFSG.RankThree.GroupTheory.SteinbergBY.map_inSubgroup_pCore 3 α C
    rw [map_eq_of_mem_stabAut hα] at h
    rw [← h]
    exact ⟨x, hx, rfl⟩
  intro α hα x
  constructor
  · intro hx
    have h := key α⁻¹ ((stabAut C).inv_mem hα) _ hx
    rwa [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply] at h
  · exact key α hα x

theorem mem_stabAut_centralizer_of_commute {α : MulAut X} {u : X}
    (h : α * MulAut.conj u = MulAut.conj u * α) :
    α ∈ stabAut (Subgroup.centralizer ({u} : Set X)) := by
  intro y
  have key : u * α y * u⁻¹ = α (u * y * u⁻¹) := by
    have h1 := congrArg (fun β : MulAut X => β y) h
    simp only [MulAut.mul_apply, MulAut.conj_apply] at h1
    exact h1.symm
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hy
    have h2 : α (u * y * u⁻¹) = α y := by
      rw [← key, ← hy, mul_inv_cancel_right]
    have h3 := α.injective h2
    calc y * u = u * y * u⁻¹ * u := by rw [h3]
      _ = u * y := by group
  · intro hy
    have h2 : u * y * u⁻¹ = y := by rw [← hy, mul_inv_cancel_right]
    calc α y * u = α (u * y * u⁻¹) * u := by rw [h2]
      _ = u * α y * u⁻¹ * u := by rw [key]
      _ = u * α y := by group

end Stab

section Theta

variable {G : Type*} [Group G] [Finite G]

@[expose] noncomputable def thetaAct (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) →* MulAut (L ⧸ aschbacherSolvableCore 3 L) :=
  (thetaQuotMulAut L).comp L.normalizerMonoidHom

theorem thetaAct_mk (L : Subgroup G) (g : Subgroup.normalizer (L : Set G)) (y : L) :
    thetaAct L g (y : L ⧸ aschbacherSolvableCore 3 L) =
      ((L.normalizerMonoidHom g y : L) : L ⧸ aschbacherSolvableCore 3 L) :=
  rfl

@[expose] noncomputable def invG (L : Subgroup G)
    (H : Subgroup (L ⧸ aschbacherSolvableCore 3 L)) : Subgroup G :=
  ((stabAut H).comap (thetaAct L)).map (Subgroup.normalizer (L : Set G)).subtype

@[expose] noncomputable def fixG (L : Subgroup G)
    (H : Subgroup (L ⧸ aschbacherSolvableCore 3 L)) : Subgroup G :=
  ((fixAut H).comap (thetaAct L)).map (Subgroup.normalizer (L : Set G)).subtype

theorem mem_invG_iff {L : Subgroup G} {H : Subgroup (L ⧸ aschbacherSolvableCore 3 L)} {g : G} :
    g ∈ invG L H ↔ ∃ hg : g ∈ Subgroup.normalizer (L : Set G), thetaAct L ⟨g, hg⟩ ∈ stabAut H := by
  constructor
  · rintro ⟨⟨g, hg⟩, h, rfl⟩
    exact ⟨hg, h⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem mem_fixG_iff {L : Subgroup G} {H : Subgroup (L ⧸ aschbacherSolvableCore 3 L)} {g : G} :
    g ∈ fixG L H ↔ ∃ hg : g ∈ Subgroup.normalizer (L : Set G), thetaAct L ⟨g, hg⟩ ∈ fixAut H := by
  constructor
  · rintro ⟨⟨g, hg⟩, h, rfl⟩
    exact ⟨hg, h⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem fixG_le_invG (L : Subgroup G) (H : Subgroup (L ⧸ aschbacherSolvableCore 3 L)) :
    fixG L H ≤ invG L H :=
  Subgroup.map_mono (Subgroup.comap_mono (fixAut_le_stabAut H))

theorem invG_le_invG_centralizer (L : Subgroup G)
    (H : Subgroup (L ⧸ aschbacherSolvableCore 3 L)) :
    invG L H ≤ invG L (Subgroup.centralizer (H : Set (L ⧸ aschbacherSolvableCore 3 L))) :=
  Subgroup.map_mono (Subgroup.comap_mono (stabAut_le_stabAut_centralizer H))

theorem invG_le_invG_pCore (L : Subgroup G) (C : Subgroup (L ⧸ aschbacherSolvableCore 3 L)) :
    invG L C ≤ invG L (inSubgroup (CFSG.pCore 3) C) :=
  Subgroup.map_mono (Subgroup.comap_mono (stabAut_le_stabAut_pCore C))

theorem fixG_anti (L : Subgroup G) {H H' : Subgroup (L ⧸ aschbacherSolvableCore 3 L)}
    (h : H ≤ H') : fixG L H' ≤ fixG L H :=
  Subgroup.map_mono (Subgroup.comap_mono (fixAut_anti h))

theorem card_map_mk_of_isPGroup {L B : Subgroup G} (hB : IsPGroup 3 B) (hBL : B ≤ L) :
    Nat.card ((B.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L))) =
      Nat.card B := by
  have hB' : IsPGroup 3 (B.subgroupOf L) := hB.comap_of_injective _ L.subtype_injective
  have hinj := CFSG.RankThree.injOn_mk_of_isPGroup (G := L) Nat.prime_three hB'
  set f := (QuotientGroup.mk' (aschbacherSolvableCore 3 L)).comp (B.subgroupOf L).subtype
    with hfdef
  have hf : Function.Injective f := fun x y hxy => Subtype.ext (hinj x.2 y.2 hxy)
  have hrange : f.range =
      (B.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) := by
    rw [hfdef, MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv]

theorem le_invG_map (L Q : Subgroup G) :
    Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (Q : Set G) ≤
      invG L ((Q.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L))) := by
  set θL := aschbacherSolvableCore 3 L
  set Qb := (Q.subgroupOf L).map (QuotientGroup.mk' θL) with hQb
  have key : ∀ g (hgL : g ∈ Subgroup.normalizer (L : Set G)),
      g ∈ Subgroup.normalizer (Q : Set G) → ∀ x ∈ Qb, thetaAct L ⟨g, hgL⟩ x ∈ Qb := by
    rintro g hgL hgQ _ ⟨y, hy, rfl⟩
    refine ⟨L.normalizerMonoidHom ⟨g, hgL⟩ y, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy ⊢
    exact (Subgroup.mem_normalizer_iff.mp hgQ _).mp hy
  rintro g ⟨hgL, hgQ⟩
  refine mem_invG_iff.mpr ⟨hgL, fun x => ⟨fun hx => ?_, key g hgL hgQ x⟩⟩
  have h := key g⁻¹ (inv_mem hgL) (inv_mem hgQ) _ hx
  have h1 : thetaAct L ⟨g⁻¹, inv_mem hgL⟩ = (thetaAct L ⟨g, hgL⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  rwa [h1, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply] at h

theorem le_fixG_map (L B : Subgroup G) :
    Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (B : Set G) ≤
      fixG L ((B.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L))) := by
  rintro g ⟨hgL, hgB⟩
  refine mem_fixG_iff.mpr ⟨hgL, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [QuotientGroup.mk'_apply, thetaAct_mk]
  congr 1
  apply Subtype.ext
  rw [normalizerMonoidHom_apply_coe]
  have h := Subgroup.mem_centralizer_iff.mp hgB _ (Subgroup.mem_subgroupOf.mp hy)
  rw [← h, mul_inv_cancel_right]

theorem disjoint_of_isPGroup_three {R N : Subgroup G} (hR : IsPGroup 3 R)
    (hN : ¬ 3 ∣ Nat.card N) : Disjoint R N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hR.exists_card_eq
  apply Subgroup.disjoint_of_coprime_natCard
  rw [hk]
  exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hN)

theorem exists_lift_centralizer {L E T : Subgroup G}
    (hθodd : Odd (Nat.card (inSubgroup (aschbacherSolvableCore 3) L)))
    (hE : IsPGroup 3 E) (hT : IsPGroup 2 T) (hET : E ≤ Subgroup.normalizer (T : Set G))
    (hETL : E ⊔ T ≤ Subgroup.normalizer (L : Set G))
    (h642 : ∀ R : Subgroup G, IsPGroup 3 R → E ⊔ T ≤ Subgroup.normalizer (R : Set G) →
      R ≤ Subgroup.centralizer (T : Set G))
    {P : Subgroup (L ⧸ aschbacherSolvableCore 3 L)} (hP : IsPGroup 3 P)
    (hinv : E ⊔ T ≤ invG L P) :
    ∃ R : Subgroup G, R ≤ L ∧ IsPGroup 3 R ∧ R ≤ Subgroup.centralizer (T : Set G) ∧
      (∀ r : L, (r : G) ∈ R → (r : L ⧸ aschbacherSolvableCore 3 L) ∈ P) ∧
      ∀ x ∈ P, ∃ r : L, (r : G) ∈ R ∧ (r : L ⧸ aschbacherSolvableCore 3 L) = x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θL := aschbacherSolvableCore 3 L with hθL
  set N := inSubgroup (aschbacherSolvableCore 3) L with hNdef
  set Phat : Subgroup G := (P.comap (QuotientGroup.mk' θL)).map L.subtype with hPhat
  have hmemP : ∀ y : L, (y : G) ∈ Phat ↔ (y : L ⧸ θL) ∈ P := by
    intro y
    constructor
    · rintro ⟨y', hy', hyy'⟩
      rw [← Subtype.ext hyy']
      exact hy'
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hPhatL : Phat ≤ L := Subgroup.map_subtype_le _
  have hmemN : ∀ y : L, (y : G) ∈ N ↔ y ∈ θL := by
    intro y
    constructor
    · rintro ⟨y', hy', hyy'⟩
      rw [← Subtype.ext hyy']
      exact hy'
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hNP : N ≤ Phat := by
    rintro _ ⟨y, hy, rfl⟩
    change (y : G) ∈ Phat
    rw [hmemP, (QuotientGroup.eq_one_iff y).mpr hy]
    exact P.one_mem
  have hPN : Phat ≤ Subgroup.normalizer (N : Set G) := hPhatL.trans (le_normalizer_theta L)
  have hP3 : ∀ x ∈ Phat, ∃ k : ℕ, x ^ 3 ^ k ∈ N := by
    rintro _ ⟨y, hy, rfl⟩
    change ∃ k : ℕ, (y : G) ^ 3 ^ k ∈ N
    obtain ⟨k, hk⟩ := hP ⟨_, hy⟩
    refine ⟨k, ?_⟩
    have h1 : ((y ^ 3 ^ k : L) : L ⧸ θL) = 1 := by
      rw [QuotientGroup.mk_pow]
      simpa using congrArg Subtype.val hk
    have h2 := (hmemN (y ^ 3 ^ k)).mpr ((QuotientGroup.eq_one_iff _).mp h1)
    simpa using h2
  have hESP : E ⊔ T ≤ Subgroup.normalizer (Phat : Set G) := by
    intro g hg
    obtain ⟨hgL, hstab⟩ := mem_invG_iff.mp (hinv hg)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change g * (y : G) * g⁻¹ ∈ Phat
      have h1 : g * (y : G) * g⁻¹ = ((L.normalizerMonoidHom ⟨g, hgL⟩ y : L) : G) := rfl
      rw [h1, hmemP]
      exact (hstab (y : L ⧸ θL)).mpr hy
    · intro hx
      have hxL : x ∈ L := by
        have h1 := (Subgroup.mem_normalizer_iff.mp (inv_mem hgL) _).mp (hPhatL hx)
        simpa [mul_assoc] using h1
      have h2 : ((L.normalizerMonoidHom ⟨g, hgL⟩ ⟨x, hxL⟩ : L) : G) ∈ Phat := hx
      rw [hmemP] at h2
      exact (hmemP ⟨x, hxL⟩).mpr ((hstab _).mp h2)
  have hESN : E ⊔ T ≤ Subgroup.normalizer (N : Set G) :=
    hETL.trans (normalizer_le_normalizer_theta L)
  obtain ⟨hNsol, hN3⟩ := theta_solvable_and_not_dvd L
  obtain ⟨R, hRP, hR3, hRN, hcov⟩ :=
    exists_invariant_threeLift hNsol hθodd hN3 hNP hPN hP3 hE hT hET hESP hESN
  refine ⟨R, hRP.trans hPhatL, hR3, h642 R hR3 hRN, fun r hr => (hmemP r).mp (hRP hr), ?_⟩
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨r, hr, hrN⟩ := hcov y ((hmemP y).mpr hx)
  have hrL : r ∈ L := hPhatL (hRP hr)
  refine ⟨⟨r, hrL⟩, hr, ?_⟩
  rw [QuotientGroup.eq, ← hmemN]
  simpa using hrN

theorem le_fixG_of_invariant {L E T : Subgroup G}
    (hθodd : Odd (Nat.card (inSubgroup (aschbacherSolvableCore 3) L)))
    (hE : IsPGroup 3 E) (hT : IsPGroup 2 T) (hET : E ≤ Subgroup.normalizer (T : Set G))
    (hETL : E ⊔ T ≤ Subgroup.normalizer (L : Set G))
    (h642 : ∀ R : Subgroup G, IsPGroup 3 R → E ⊔ T ≤ Subgroup.normalizer (R : Set G) →
      R ≤ Subgroup.centralizer (T : Set G))
    {P : Subgroup (L ⧸ aschbacherSolvableCore 3 L)} (hP : IsPGroup 3 P)
    (hinv : E ⊔ T ≤ invG L P) : T ≤ fixG L P := by
  obtain ⟨R, -, -, hRT, -, hsurj⟩ := exists_lift_centralizer hθodd hE hT hET hETL h642 hP hinv
  intro t ht
  have htL : t ∈ Subgroup.normalizer (L : Set G) := hETL (Subgroup.mem_sup_right ht)
  refine mem_fixG_iff.mpr ⟨htL, fun x hx => ?_⟩
  obtain ⟨r, hr, rfl⟩ := hsurj x hx
  rw [thetaAct_mk]
  congr 1
  apply Subtype.ext
  rw [normalizerMonoidHom_apply_coe]
  have h := Subgroup.mem_centralizer_iff.mp (hRT hr) t ht
  rw [h, mul_inv_cancel_right]

theorem false_of_invariant_elemAbelian (he : CFSG.Assembly.evenRank G = 3) {L E T : Subgroup G}
    (hθodd : Odd (Nat.card (inSubgroup (aschbacherSolvableCore 3) L)))
    (hE : IsPGroup 3 E) (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hET : E ≤ Subgroup.normalizer (T : Set G))
    (hETL : E ⊔ T ≤ Subgroup.normalizer (L : Set G))
    (h642 : ∀ R : Subgroup G, IsPGroup 3 R → E ⊔ T ≤ Subgroup.normalizer (R : Set G) →
      R ≤ Subgroup.centralizer (T : Set G))
    {P : Subgroup (L ⧸ aschbacherSolvableCore 3 L)} (hPe : CFSG.Assembly.IsElemAbelian 3 P)
    (h81 : 81 ≤ Nat.card P) (hinv : E ⊔ T ≤ invG L P) : False := by
  have hP3 : IsPGroup 3 P := Sec5.isPGroup_of_isElemAbelian hPe
  obtain ⟨R, hRL, hR3, hRT, himg, hsurj⟩ :=
    exists_lift_centralizer hθodd hE hT hET hETL h642 hP3 hinv
  set θL := aschbacherSolvableCore 3 L with hθL
  have hdisj : Disjoint R (inSubgroup (aschbacherSolvableCore 3) L) :=
    disjoint_of_isPGroup_three hR3 (theta_solvable_and_not_dvd L).2
  have hone : ∀ r ∈ R, ∀ hr : r ∈ L, ((⟨r, hr⟩ : L) : L ⧸ θL) = 1 → r = 1 := by
    intro r hr hrL h1
    have hθ : r ∈ inSubgroup (aschbacherSolvableCore 3) L :=
      ⟨⟨r, hrL⟩, (QuotientGroup.eq_one_iff _).mp h1, rfl⟩
    exact Subgroup.disjoint_def.mp hdisj hr hθ
  have hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hPe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hRe : CFSG.Assembly.IsElemAbelian 3 R := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun r hr => ?_⟩
    · have ha := hRL a.2
      have hb := hRL b.2
      have hc : (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ = 1 := by
        refine hone _ (R.mul_mem (R.mul_mem (R.mul_mem a.2 b.2) (R.inv_mem a.2)) (R.inv_mem b.2))
          (L.mul_mem (L.mul_mem (L.mul_mem ha hb) (L.inv_mem ha)) (L.inv_mem hb)) ?_
        have h1 := hPc _ (himg ⟨a, ha⟩ a.2) _ (himg ⟨b, hb⟩ b.2)
        have h2 : ((⟨(a : G) * b * (a : G)⁻¹ * (b : G)⁻¹,
            L.mul_mem (L.mul_mem (L.mul_mem ha hb) (L.inv_mem ha)) (L.inv_mem hb)⟩ : L) :
              L ⧸ θL) =
            ((⟨a, ha⟩ : L) : L ⧸ θL) * ((⟨b, hb⟩ : L) : L ⧸ θL) *
              (((⟨a, ha⟩ : L) : L ⧸ θL))⁻¹ * (((⟨b, hb⟩ : L) : L ⧸ θL))⁻¹ := rfl
        rw [h2, h1, mul_inv_cancel_right, mul_inv_cancel]
      show (a : G) * b = b * a
      calc (a : G) * b = (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ * (b * a) := by group
        _ = b * a := by rw [hc, one_mul]
    · have hrL := hRL hr
      refine hone _ (R.pow_mem hr 3) (L.pow_mem hrL 3) ?_
      have h1 := hPe.2 _ (himg ⟨r, hrL⟩ hr)
      have h2 : ((⟨r ^ 3, L.pow_mem hrL 3⟩ : L) : L ⧸ θL) = ((⟨r, hrL⟩ : L) : L ⧸ θL) ^ 3 := rfl
      rw [h2, h1]
  have hcard : Nat.card P ≤ Nat.card R := by
    refine Nat.card_le_card_of_surjective
      (fun r : R => (⟨((⟨r, hRL r.2⟩ : L) : L ⧸ θL), himg _ r.2⟩ : P)) ?_
    rintro ⟨x, hx⟩
    obtain ⟨r, hr, rfl⟩ := hsurj x hx
    exact ⟨⟨r, hr⟩, rfl⟩
  have h27 := Sec5.card_le_of_le_normalizer he hT1 hT hRe
    (hRT.trans (Subgroup.centralizer_le_normalizer _))
  omega

end Theta

end CFSG.RankThree.PartTwo.Sec6.Res611Res4
