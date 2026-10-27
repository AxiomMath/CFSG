module

public import CFSG.LocalAnalysis.SectionRank.LocalDet
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Out2
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.Quasithin.B45Exc3A7

open Equiv Equiv.Perm CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family

@[expose] def tau1 : Perm (Fin 7) := swap 0 1

@[expose] def tau2 : Perm (Fin 7) := swap 0 3 * swap 1 4 * swap 2 5

theorem cycleType_taus : tau1.cycleType = {2} ∧ tau2.cycleType = {2, 2, 2} := by
  have hsw : ∀ a b : Fin 7, a ≠ b → (swap a b).cycleType = {2} := fun a b hab => by
    rw [(isCycle_swap hab).cycleType, card_support_swap hab]
  have hd1 : Disjoint (swap (0 : Fin 7) 3) (swap 1 4) := by
    intro x
    revert x
    decide
  have hd2 : Disjoint (swap (0 : Fin 7) 3 * swap 1 4) (swap 2 5) := by
    intro x
    revert x
    decide
  refine ⟨hsw 0 1 (by decide), ?_⟩
  unfold tau2
  rw [Equiv.Perm.Disjoint.cycleType_mul hd2, Equiv.Perm.Disjoint.cycleType_mul hd1,
    hsw 0 3 (by decide), hsw 1 4 (by decide), hsw 2 5 (by decide)]
  rfl

theorem tau_facts : tau1 * tau1 = 1 ∧ tau2 * tau2 = 1 ∧ sign tau1 = -1 ∧ sign tau2 = -1 := by
  decide

theorem odd_invol_conj (σ : Perm (Fin 7)) (h2 : σ * σ = 1) (hs : sign σ = -1) :
    ∃ ρ ∈ alternatingGroup (Fin 7), ∃ τ : Perm (Fin 7), (τ = tau1 ∨ τ = tau2) ∧
      ρ * τ * ρ⁻¹ = σ := by
  classical
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [Perm.sign_one] at hs
    exact absurd hs (by decide)
  have hord : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact h2) hσ1
  have hmem : ∀ n ∈ σ.cycleType, n = 2 := by
    intro n hn
    have h1 := dvd_of_mem_cycleType hn
    rw [hord] at h1
    have h2' := two_le_of_mem_cycleType hn
    have h3 : n ≤ 2 := Nat.le_of_dvd (by norm_num) h1
    omega
  set k := Multiset.card σ.cycleType with hk
  have hrep : σ.cycleType = Multiset.replicate k 2 := Multiset.eq_replicate.2 ⟨rfl, hmem⟩
  have hsum : σ.cycleType.sum = 2 * k := by
    rw [hrep, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have hk3 : k ≤ 3 := by
    have h1 := sum_cycleType σ
    have h2' : σ.support.card ≤ 7 := by
      have := Finset.card_le_univ σ.support
      simpa using this
    omega
  have hsign := sign_of_cycleType σ
  rw [hs, hsum, ← hk] at hsign
  have hconj : ∀ τ : Perm (Fin 7), σ.cycleType = τ.cycleType → sign τ = -1 → τ * τ = 1 →
      ∃ ρ ∈ alternatingGroup (Fin 7), ρ * τ * ρ⁻¹ = σ := by
    intro τ hτ hτs hτ2
    obtain ⟨c, hc⟩ := isConj_iff.1 ((isConj_iff_cycleType_eq).2 hτ.symm)
    by_cases hcs : sign c = 1
    · exact ⟨c, mem_alternatingGroup.2 hcs, hc⟩
    · have hcs' : sign c = -1 := (Int.units_eq_one_or _).resolve_left hcs
      refine ⟨c * τ, ?_, ?_⟩
      · rw [mem_alternatingGroup, Perm.sign_mul, hcs', hτs]
        decide
      · calc c * τ * τ * (c * τ)⁻¹ = c * τ * c⁻¹ := by group
          _ = σ := hc
  obtain ⟨h1, h2'', h3, h4⟩ := tau_facts
  obtain ⟨c1, c2⟩ := cycleType_taus
  interval_cases k
  · exfalso
    norm_num at hsign
  · obtain ⟨ρ, hρ, h⟩ := hconj tau1 (hrep.trans ((show Multiset.replicate 1 2 = {2} from rfl).trans
      c1.symm)) h3 h1
    exact ⟨ρ, hρ, tau1, Or.inl rfl, h⟩
  · exfalso
    norm_num at hsign
  · obtain ⟨ρ, hρ, h⟩ := hconj tau2 (hrep.trans
      ((show Multiset.replicate 3 2 = {2, 2, 2} from rfl).trans c2.symm)) h4 h2''
    exact ⟨ρ, hρ, tau2, Or.inr rfl, h⟩

@[expose] def x3 : alternatingGroup (Fin 7) :=
  ⟨swap 0 1 * swap 1 2, by rw [mem_alternatingGroup]; decide⟩

@[expose] def y3 : alternatingGroup (Fin 7) :=
  ⟨swap 3 4 * swap 4 5, by rw [mem_alternatingGroup]; decide⟩

theorem xy_facts :
    (x3 : Perm (Fin 7)) ^ 3 = 1 ∧ (y3 : Perm (Fin 7)) ^ 3 = 1 ∧
    (x3 : Perm (Fin 7)) * y3 = y3 * x3 ∧
    tau1 * x3 * tau1⁻¹ = (x3 : Perm (Fin 7)) ^ 2 * (y3 : Perm (Fin 7)) ^ 0 ∧
    tau1 * y3 * tau1⁻¹ = (x3 : Perm (Fin 7)) ^ 0 * (y3 : Perm (Fin 7)) ^ 1 ∧
    tau2 * x3 * tau2⁻¹ = (x3 : Perm (Fin 7)) ^ 0 * (y3 : Perm (Fin 7)) ^ 1 ∧
    tau2 * y3 * tau2⁻¹ = (x3 : Perm (Fin 7)) ^ 1 * (y3 : Perm (Fin 7)) ^ 0 := by
  decide

theorem xy_eval : ∀ i j : Fin 3,
    ((x3 : Perm (Fin 7)) ^ i.val * (y3 : Perm (Fin 7)) ^ j.val) 0 = ⟨i.val, by omega⟩ ∧
    ((x3 : Perm (Fin 7)) ^ i.val * (y3 : Perm (Fin 7)) ^ j.val) 3 = ⟨3 + j.val, by omega⟩ := by
  decide

theorem closure_pair_facts {G : Type*} [Group G] {a b : G} (hab : a * b = b * a) {n : ℕ}
    (ha : a ^ n = 1) (hb : b ^ n = 1) :
    (∀ x ∈ Subgroup.closure ({a, b} : Set G), ∀ y ∈ Subgroup.closure ({a, b} : Set G),
      x * y = y * x) ∧ ∀ x ∈ Subgroup.closure ({a, b} : Set G), x ^ n = 1 := by
  have hc : ∀ x ∈ ({a, b} : Set G), ∀ y ∈ ({a, b} : Set G), x * y = y * x := by
    rintro x (rfl | rfl) y (rfl | rfl)
    · rfl
    · exact hab
    · exact hab.symm
    · rfl
  have h1 : Subgroup.closure ({a, b} : Set G) ≤ Subgroup.centralizer ({a, b} : Set G) :=
    (Subgroup.closure_le _).mpr fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy =>
      hc y hy x hx
  have h2 : Subgroup.closure ({a, b} : Set G) ≤
      Subgroup.centralizer (Subgroup.closure ({a, b} : Set G) : Set G) :=
    (Subgroup.closure_le _).mpr fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (Subgroup.mem_centralizer_iff.mp (h1 hy) x hx).symm
  have hcomm : ∀ x ∈ Subgroup.closure ({a, b} : Set G), ∀ y ∈ Subgroup.closure ({a, b} : Set G),
      x * y = y * x :=
    fun x hx y hy => Subgroup.mem_centralizer_iff.mp (h2 hy) x hx
  refine ⟨hcomm, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · exact ha
    · exact hb
  | one => exact one_pow n
  | mul x y hx hy ihx ihy => rw [Commute.mul_pow (hcomm x hx y hy) n, ihx, ihy, one_mul]
  | inv x _ ih => rw [inv_pow, ih, inv_one]

theorem exists_sylowQ : ∃ Q : Sylow 3 (alternatingGroup (Fin 7)),
    (Q : Subgroup (alternatingGroup (Fin 7))) = Subgroup.closure {x3, y3} ∧
      CFSG.Open.IsElemAbelian 3 (Q : Subgroup (alternatingGroup (Fin 7))) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hx3, hy3, hxy, -⟩ := xy_facts
  have hx3' : x3 ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hx3)
  have hy3' : y3 ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hy3)
  have hxy' : x3 * y3 = y3 * x3 := Subtype.ext hxy
  obtain ⟨hcomm, hpow⟩ := closure_pair_facts hxy' hx3' hy3'
  set C := Subgroup.closure ({x3, y3} : Set (alternatingGroup (Fin 7))) with hC
  have hCp : IsPGroup 3 C := fun g => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow]
    exact hpow _ g.2)⟩
  obtain ⟨Q, hCQ⟩ := hCp.exists_le_sylow
  have hQ9 : Nat.card (Q : Subgroup (alternatingGroup (Fin 7))) = 9 := by
    rw [Sylow.card_eq_multiplicity, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin, show Nat.factorial 7 / 2 = 3 ^ 2 * 280 from rfl,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    norm_num
  have hxC : x3 ∈ C := Subgroup.subset_closure (by simp)
  have hyC : y3 ∈ C := Subgroup.subset_closure (by simp)
  let F : Fin 3 × Fin 3 → C := fun p => ⟨x3 ^ p.1.val * y3 ^ p.2.val,
    mul_mem (pow_mem hxC _) (pow_mem hyC _)⟩
  have hF : Function.Injective F := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have h1 : (x3 : Perm (Fin 7)) ^ i.val * (y3 : Perm (Fin 7)) ^ j.val =
        (x3 : Perm (Fin 7)) ^ i'.val * (y3 : Perm (Fin 7)) ^ j'.val := by
      have := congrArg (fun c : C => ((c : alternatingGroup (Fin 7)) : Perm (Fin 7))) h
      simpa [F] using this
    have h0 := congrArg (fun σ : Perm (Fin 7) => σ 0) h1
    have h3 := congrArg (fun σ : Perm (Fin 7) => σ 3) h1
    simp only [(xy_eval i j).1, (xy_eval i' j').1, (xy_eval i j).2, (xy_eval i' j').2] at h0 h3
    have hi : i = i' := Fin.ext (by simpa using congrArg Fin.val h0)
    have hj : j = j' := Fin.ext (by
      have := congrArg Fin.val h3
      simp at this
      omega)
    rw [hi, hj]
  have hC9 : 9 ≤ Nat.card C := by
    have := Nat.card_le_card_of_injective F hF
    simpa using this
  have hCQ' : C = Q := Subgroup.eq_of_le_of_card_ge hCQ (by rw [hQ9]; exact hC9)
  refine ⟨Q, hCQ'.symm, ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun g hg => ?_⟩⟩
  · have ha : (a : alternatingGroup (Fin 7)) ∈ C := by rw [hCQ']; exact a.2
    have hb : (b : alternatingGroup (Fin 7)) ∈ C := by rw [hCQ']; exact b.2
    exact hcomm _ ha _ hb
  · have hg' : g ∈ C := by rw [hCQ']; exact hg
    exact hpow g hg'

section Claim

variable {W : Type} [CommGroup W] [Finite W]

theorem mem_of_commute_center (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L) (hirr : IsIrrOn L)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEel : IsElemAbelian2 E)
    (e : CQ L ≃* alternatingGroup (Fin 7)) (hZ3 : Nat.card (Subgroup.center ↥L) = 3)
    {zL : ↥L} (hcen : Subgroup.center ↥L = Subgroup.zpowers zL) {b : MulAut W} (hbE : b ∈ E)
    (hbz : b * (zL : MulAut W) = (zL : MulAut W) * b) : b ∈ L := by
  classical
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by norm_num) (by norm_num)
  let cEquiv : Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) := MulEquiv.ofBijective _ hbij
  have hcf : ∀ s : alternatingGroup (Fin 7), cEquiv (s : Perm (Fin 7)) = MulAut.conj s :=
    fun s => MulAut.conjNormal_val
  have hcapp : ∀ (τ : Perm (Fin 7)) (s : alternatingGroup (Fin 7)),
      ((cEquiv τ s : alternatingGroup (Fin 7)) : Perm (Fin 7)) = τ * s * τ⁻¹ :=
    fun τ s => MulAut.conjNormal_apply τ s
  set bE : ↥(L ⊔ E) := ⟨b, Subgroup.mem_sup_right hbE⟩ with hbE'
  set σ := cEquiv.symm (actS hE e bE) with hσdef
  have hσ : cEquiv σ = actS hE e bE := cEquiv.apply_symm_apply _
  by_cases hσA : σ ∈ alternatingGroup (Fin 7)
  · refine mem_of_actS_inner hW hperf hirr hE hEel e hbE ⟨⟨σ, hσA⟩, ?_⟩
    rw [← hcf, hσ]
  · exfalso
    have hb2 : bE * bE = 1 := Subtype.ext (by
      show b * b = 1
      rw [← pow_two]
      exact hEel.2 b hbE)
    have hσ2 : σ * σ = 1 := cEquiv.injective (by rw [map_mul, hσ, ← map_mul, hb2, map_one,
      map_one])
    have hsign : sign σ = -1 :=
      (Int.units_eq_one_or _).resolve_left fun h => hσA (mem_alternatingGroup.2 h)
    obtain ⟨ρ, hρA, τ, hτ, hρτ⟩ := odd_invol_conj σ hσ2 hsign
    obtain ⟨l, hl⟩ := redHom_surjective L e ⟨ρ, hρA⟩
    set lE : ↥(L ⊔ E) := ⟨(l : MulAut W), Subgroup.mem_sup_left l.2⟩ with hlE
    set g : ↥(L ⊔ E) := lE⁻¹ * bE * lE with hg
    have hl' : actS hE e lE = cEquiv ρ := by
      rw [hlE, actS_of_mem hE e l, hl, ← hcf]
    have hgτ : actS hE e g = cEquiv τ := by
      rw [hg, map_mul, map_mul, map_inv, hl', ← hσ, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      rw [← hρτ]
      group
    have hzl : (l : MulAut W) * (zL : MulAut W) = (zL : MulAut W) * l := by
      have hzc : zL ∈ Subgroup.center ↥L := hcen ▸ Subgroup.mem_zpowers zL
      have := Subgroup.mem_center_iff.1 hzc l
      exact congrArg Subtype.val this
    have hgz : (g : MulAut W) * (zL : MulAut W) = (zL : MulAut W) * g := by
      show (l : MulAut W)⁻¹ * b * l * zL = zL * ((l : MulAut W)⁻¹ * b * l)
      have hzl' : (l : MulAut W)⁻¹ * (zL : MulAut W) = (zL : MulAut W) * (l : MulAut W)⁻¹ :=
        (Commute.inv_left (show Commute (l : MulAut W) (zL : MulAut W) from hzl)).eq
      calc (l : MulAut W)⁻¹ * b * l * zL = (l : MulAut W)⁻¹ * b * (zL * l) := by
            rw [mul_assoc, hzl]
        _ = (l : MulAut W)⁻¹ * (b * zL) * l := by group
        _ = (l : MulAut W)⁻¹ * (zL * b) * l := by rw [hbz]
        _ = ((l : MulAut W)⁻¹ * zL) * b * l := by group
        _ = (zL * (l : MulAut W)⁻¹) * b * l := by rw [hzl']
        _ = zL * ((l : MulAut W)⁻¹ * b * l) := by group
    let π : ↥L →* alternatingGroup (Fin 7) := redHom L e
    have hker : π.ker = Subgroup.center ↥L := by
      ext x
      exact redHom_eq_one_iff L e x
    have hn := normal_sup_of_le_normalizer hE
    let α : ↥L ≃* ↥L := conjAutL le_sup_left hn g
    have hαβ : ∀ x, π (α x) = actS hE e g (π x) := by
      intro x
      show e (QuotientGroup.mk (conjAutL le_sup_left hn g x)) =
        e (actionOnCQ le_sup_left hn g (e.symm (e (QuotientGroup.mk x))))
      rw [MulEquiv.symm_apply_apply, actionOnCQ_mk]
    have hαC : ∀ c ∈ π.ker, α c = c := by
      intro c hc
      rw [hker, hcen] at hc
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
      apply Subtype.ext
      rw [conjAutL_apply, Subgroup.coe_zpow]
      have hc' := (Commute.zpow_right hgz n).eq
      calc (g : MulAut W) * (zL : MulAut W) ^ n * (g : MulAut W)⁻¹ =
          (zL : MulAut W) ^ n * g * (g : MulAut W)⁻¹ := by rw [hc']
        _ = (zL : MulAut W) ^ n := by group
    obtain ⟨Q, hQ, hQe⟩ := exists_sylowQ
    obtain ⟨Cp⟩ : Nonempty (Sylow 3 π.ker) := inferInstance
    obtain ⟨-, -, -, h1x, h1y, h2x, h2y⟩ := xy_facts
    have hβ : ∀ s : alternatingGroup (Fin 7),
        ((actS hE e g s : alternatingGroup (Fin 7)) : Perm (Fin 7)) = τ * s * τ⁻¹ := by
      intro s
      rw [hgτ, hcapp]
    have hbot : (Cp : Subgroup π.ker) = ⊥ := by
      rcases hτ with rfl | rfl
      · refine SectionRank.sylow_kernel_eq_bot_of_det π (redHom_surjective L e) hker.le Q hQe α
          (actS hE e g) hαβ hαC hQ.symm (a := 2) (b := 0) (c := 0) (d := 1) ?_ ?_ (by decide) Cp
        · apply Subtype.ext
          rw [hβ, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow, h1x]
        · apply Subtype.ext
          rw [hβ, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow, h1y]
      · refine SectionRank.sylow_kernel_eq_bot_of_det π (redHom_surjective L e) hker.le Q hQe α
          (actS hE e g) hαβ hαC hQ.symm (a := 0) (b := 1) (c := 1) (d := 0) ?_ ?_ (by decide) Cp
        · apply Subtype.ext
          rw [hβ, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow, h2x]
        · apply Subtype.ext
          rw [hβ, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow, h2y]
    have hk3 : Nat.card π.ker = 3 := by rw [hker, hZ3]
    have hCp := Sylow.card_eq_multiplicity Cp
    rw [hk3, hbot, Subgroup.card_bot, Nat.Prime.factorization_self Nat.prime_three] at hCp
    norm_num at hCp

end Claim

end CFSG.Quasithin.B45Exc3A7
